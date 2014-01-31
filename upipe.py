#!/usr/bin/env python
try: 
    import asl
    ASL=True
except: 
    """This is just for flash, not essential"""
    ASL=False

import asyncore
import base64
import calendar
import inspect
import optparse
import os
import pprint
import Queue
import re
import socket
import struct
import sys
import threading
import time

HAS_GUI=True
try:
    import pygtk
    pygtk.require('2.0')
    import gtk
    import gobject
    gobject.threads_init()
except:
    HAS_GUI=False
    pass

"""
TCP Forwarding:

(NOTE: Most of fhe following has been done, but there are still 
       some bugs to work out.)

We need a way for a TCP connection status to be recognized
both on local and remote pipes. The best way to start is
to add support for local pipes to recognize TCP connections.
Connect, Accept, Write, Read, Close
Each operation must be handled by the MultiPipe class.
Once the MultiPipe knows how to handle these operations, we
must extend the INTERNAL TCP messages to include each of
these operations as well.

Currently we only have one command, 'FWD_DATA'

This must be expanded to handle any number of directives.
For TCP this should include:

'CONNECT' (Host -> Pipe: creates a new TCP Pipe)
'ACCEPT'  (Pipe -> Host: confirms a new TCP Pipe)
'CLOSE'   (either direction: deletes a TCP Pipe)



We may need to handle multiple simultaneous connections to
TCP hosts whether remote or not. This means generating a new
connection every time we receive a connect event from the
client side, and disposing of them correctly when either end
terminates the connection. Compare this with how we are doing
it now.
"""

# === Exceptions /*{{{*/
class UPipeException(Exception):
    pass

class CoreTypeException(UPipeException):
    pass
class ExServerDied(UPipeException):
    pass

class ClientException(UPipeException):
    pass

class ConfigException(UPipeException):
    pass
class ConfigNotAFileException(ConfigException):
    pass
class ConfigNotFoundException(ConfigException):
    pass
class ConfigReadError(ConfigException):
    pass
class InvalidConfigException(ConfigException):
    pass

class HostException(UPipeException):
    pass
class DuplicateHostException(HostException):
    pass
class HostBindException(HostException):
    pass
#/*}}}*/

# === Helper Functions /*{{{*/
def verify_port(port):
    try:
        port = int(port)
        if 0 > port > 65535:
            return None
    except:
        return None
    return port

def verify_host(host):
    if type(host) != str:
        return None
    try:
        host = socket.gethostbyname(host)
    except:
        return None
    return host

def verify_pipe(pipe_str):
    pipe = None
    parts = pipe_str.split(':')[::-1]
    if len(parts) < 3:
        return None
    if len(parts) > 5:
        return None
    bind_host = ''
    bind_port = 0
    pipe_type = parts[0]
    port = verify_port(parts[1])
    host = verify_host(parts[2])
    if len(parts) > 3:
        bind_port = verify_port(parts[3]) 
    if len(parts) > 4:
        bind_host = verify_host(parts[4]) 

    if pipe_type not in ("TCP", "UDP"): return None
    if host is None: return None
    if port is None: return None
    if bind_host is None: return None
    if bind_port is None: return None

    return (bind_host,bind_port,host,port,pipe_type)


def parse_config(config_file):
    config = {}
    pipes = []
    if not os.path.exists(config_file):
        raise ConfigNotFoundException("config path '%s' does not exist" % config_file)
    if not os.path.isfile(config_file):
        raise ConfigNotAFileException("config path '%s' is not a regular file" % config_file)
    try:
        lines = open(config_file, 'r').readlines()
        line_index = 0
        for line in map(lambda l: l.strip(), lines):
            line_index += 1
            if len(line) == 0:
                continue
            if line[0] == '#':
                continue
            parts = map(lambda p: p.strip(), line.split('='))
            if len(parts) != 2:
                raise InvalidConfigException("bad entry on line %d" % line_index)
            key,value = parts
            if key == 'pipe':
                pipes.append(value)
            else:
                if config.has_key(key):
                    raise InvalidConfigException("duplicate entry on line %d" % line_index)
                config[key] = value

        if len(pipes):
            config['pipes'] = pipes
    except:
        raise ConfigReadError("could not read config file '%s'" % config_file)

    return config
#/*}}}*/

# === Counter Class /*{{{*/
# A simple counter class that keeps track of state
# methods ending in _t are thread safe
def thread_safe(func):
    def lock_func(self, *args):
        self.lock.acquire()
        func(self, *args)
        self.lock.release()
    return lock_func

class Counter(object):
    def __init__(self, value=0, stride=1):
        self.stride = stride
        self.original = value
        self.lock = threading.Lock()
        self.reset()

    def reset(self):
        self.value = self.original

    @thread_safe
    def reset_t(self):
        self.reset()

    def set_value(self, value):
        self.value = value

    @thread_safe
    def set_value_t(self, value):
        self.set_value(value)

    def set_stride(self, stride):
        self.stride = stride

    @thread_safe
    def set_stride_t(self, stride):
        self.set_stride(stride)

    # Pre increment
    def inc(self):
        self.value += self.stride
        return self.value

    @thread_safe
    def inc_t(self):
        return self.inc()

    # Pre decrement
    def dec(self):
        self.value -= self.stride
        return self.value

    @thread_safe
    def dec_t(self):
        return self.dec()

    # Post increment
    def inc_p(self):
        temp = self.value
        self.value += self.stride
        return temp

    @thread_safe
    def inc_p_t(self):
        return self.inc_p()

    # Post decrement
    def dec_p(self):
        temp = self.value
        self.value -= self.stride
        return temp

    @thread_safe
    def dec_p_t(self):
        return self.dec_p()

#/*}}}*/

# === Pipe Classes /*{{{*/
# Base class for all network communications classes which are
# attached to asyncore
class PipeBase(asyncore.dispatcher):
    def __init__(self, master=None, id=None):
        self._master = master # MultiPipe class instance that "owns" this Pipe component
        self._id = id

        asyncore.dispatcher.__init__(self)
        self._hostname = None # Remote host name
        self._address = None # Remote host (IP,Port)
        self._socket_type = None # Connection type (UDP/TCP)

        self._buffers = [] # Queued write data for this PipeBase object
        self._write_buffer = '' # Write buffer which is currently being processed
        self._write_address = None # Address associated with the current write buffer

        self._rx_packets = 0 # Number of packets received
        self._rx_bytes = 0 # Number of bytes received
        self._tx_packets = 0 # Number of packets sent
        self._tx_bytes = 0 # Number of bytes sent

        # TCP Connections Only
        self._remote_key = None  # Key for the remote host format "xxx.xxx.xxx.xxx-ppppp-TCP"
        self._connecting = False # True when the connection is being initialized
        self._connected = False # True when the connection has been established
        self._disconnecting = False # True when a request has been made to close the connection

    def get_id(self):
        return self._id

    def log(self, string, verbosity=1):
        if self._master:
            self._master.log(string, verbosity)

    def set_address(self, address):
        if type(address) is not tuple:
            raise TypeError("address must be of type 'tuple'")
        if len(address) != 2:
            raise TypeError("address must be a tuple of length 2")
        ip, port = address
        if type(ip) is not str:
            raise TypeError("address' first item must be of type 'str'")
        if type(port) is not int:
            raise TypeError("address' second item must be of type 'int'")
        host, port = address
        try:
            ip = socket.gethostbyname(host)
        except socket.gaierror:
            raise ValueError("unknown host")
        self._hostname = host
        self._address = (ip, port)

    def set_socket_type(self, socket_type):
        if type(socket_type) not in (int, str):
            raise TypeError("socket_type must be of type 'str' or 'int'")
        if socket_type not in ('UDP', 'TCP', socket.SOCK_DGRAM, socket.SOCK_STREAM):
            raise ValueError("invalid value for socket_type")
        if type(socket_type) is int:
            self._socket_type = socket_type
        else:
            if socket_type == 'UDP':
                self._socket_type = socket.SOCK_DGRAM
            elif socket_type == 'TCP':
                self._socket_type = socket.SOCK_STREAM

    def get_socket_type(self):
        return self._socket_type

    def get_socket_type_str(self):
        type = self._socket_type
        if self._socket_type == socket.SOCK_DGRAM:
            return 'UDP'
        elif self._socket_type == socket.SOCK_STREAM:
            return 'TCP'
        return ''

    def get_address(self):
        return self._address

    def get_key(self):
        if self._address and self._socket_type:
            return "%s-%d-%s" % (self._address[0], self._address[1], self.get_socket_type_str())
        return ""

    def __str__(self):
        if self._address and self._socket_type:
            ip,port = self._address
            bind_ip,bind_port = self.getsockname()
            return "%s %s:%s:%s:%s" % (self.get_socket_type_str(),bind_ip,bind_port,ip,port)
        return ""

    # Add packet to buffer list for transmission
    def queue_packet(self, packet, address=None):
        self.log("Queueing Packet: %s %s" % (str(packet), str(address)), 4)
        if not packet:
            packet = ''
        self._buffers.append((packet, address))

    # Check that there is data queued for writing
    # (Overrides the method in asyncore.dispatcher)
    def writable(self):
        self.log("%s buffers %s" % (self.__class__.__name__, str(self._buffers)), 5)
        self.log("%s write_buffer %s" % (self.__class__.__name__, str(self._write_buffer)), 5)
        self.log("%s write_address %s" % (self.__class__.__name__, str(self._write_address)), 5)
        return (len(self._buffers) > 0) or (len(self._write_buffer) > 0)

    # Check that we are connected before reading
    # (Overrides the method in asyncore.dispatcher)
    def readable(self):
        if self._socket_type == socket.SOCK_STREAM:
            if self._connecting and not self._connected:
                return False
        return True
# Call the underlying write handler, track the byte and packet counts
    # (Overrides the method in asyncore.dispatcher)
    def handle_write(self):
        self.log("In write handler for %s %s" % (self.__class__.__name__, str(self.get_key())), 4)
        self.log("remote_key   : %s" % str(self._remote_key), 5)
        self.log("connecting   : %s" % str(self._connecting), 5)
        self.log("connected    : %s" % str(self._connected), 5)
        self.log("disconnecting: %s" % str(self._disconnecting), 5)
        if not self._ensure_connected():
            return
        bytes_written = self._handle_write()
        self._last_activity = calendar.timegm(time.gmtime())
        if bytes_written > 0:
            self._tx_bytes   += bytes_written
            self._tx_packets += 1

    def _handle_write(self):
        bytes_written = 0
        self.log("Entered %s::_handle_write" % self.__class__.__name__, 4)
        if (not len(self._write_buffer)) and len(self._buffers):
            self._write_buffer, self._write_address = self._buffers.pop(0)
        if len(self._write_buffer):
            self.log("writing to address %s" % str(self._write_address), 5)
            if self._socket_type == socket.SOCK_STREAM or self._write_address is None:
                bytes_written = self.send(self._write_buffer)
            else:
                bytes_written = self.sendto(self._write_buffer, self._write_address)
            self._write_buffer = self._write_buffer[bytes_written:]
        self.handle_disconnect()
        return bytes_written

    # Call the underlying read handler, track the byte and packet counts
    # (Overrides the method in asyncore.dispatcher)
    def handle_read(self):
        self.log("In read handler for %s %s" % (self.__class__.__name__, str(self.get_key())), 4)
        self.log("remote_key   : %s" % str(self._remote_key), 5)
        self.log("connecting   : %s" % str(self._connecting), 5)
        self.log("connected    : %s" % str(self._connected), 5)
        self.log("disconnecting: %s" % str(self._disconnecting), 5)
        if not self._ensure_connected():
            if not self._connecting:
                self.handle_connect()
        else:
            bytes_read = self._handle_read()
            self._last_activity = calendar.timegm(time.gmtime())
            if bytes_read > 0:
                self._tx_bytes   += bytes_read
                self._tx_packets += 1

    def _ensure_connected(self):
        self.log("%s::_ensure_connected()" % self.__class__.__name__, 4)
        self.log("  connecting = %s" % self._connecting, 5)
        self.log("  connected  = %s" % self._connected, 5)
        #pprint.pprint(inspect.stack())
        if self._socket_type == socket.SOCK_STREAM:
            if not self._connected:
                return False
        return True

    def begin_disconnect(self):
        self._connecting = False
        self._disconnecting = True
        self.handle_disconnect()

    def handle_disconnect(self):
        if self._socket_type == socket.SOCK_STREAM and self._disconnecting and not self.writable():
            self._handle_close()


# Hosts send/receive as if they were the actual host.
# They communicate directly with the initializing client.
class Host(PipeBase):
    def __init__(self, master, address, socket_type='UDP', bind_port=0, bind_host='', id=None, bind_to_any=False):
        PipeBase.__init__(self, master, id=id)
        self._original_socket = None # Socket on which the Host listens for TCP connections

        self.set_address(address)
        self.set_socket_type(socket_type)
        self._original_socket = socket.socket(socket.AF_INET, self.get_socket_type())
        self.set_socket(self._original_socket)
        self.set_reuse_addr()
        try:
            self.bind((bind_host, bind_port))
        except:
            if bind_to_any:
                self.bind(('', 0))
            else:
                c_address,c_port = address
                raise HostBindException("Failed to bind to %s:%s for host %s:%s" % (bind_host, str(bind_port), c_address, str(c_port)))
        if self._socket_type == socket.SOCK_STREAM:
            self._original_socket.listen(5)


    def _handle_read(self):
        self.log("Host::_handle_read()", 4)
        if not self._ensure_connected():
            self.log("Host::_handle_read() not connected", 2)
            return 0
        packet,address = self.recvfrom(4096)
        if address is None and self._socket_type == socket.SOCK_STREAM:
            client_key = self._remote_key
        else:
            ip,port = address
            client_key = "%s-%d-%s" % (ip, port, self.get_socket_type_str())
        if len(packet) > 0:
            self._master.client_to_host('FWD_DATA', client_key, self.get_key(), packet)
        elif self._socket_type == socket.SOCK_STREAM:
            self.handle_close()
        return len(packet)

    def handle_connect(self):
        self.log("Host::handle_connect()", 3)
        if self._socket_type == socket.SOCK_STREAM:
            if self._connected:
                self.log("Host::handle_connect() already connected", 2)
                return
            if self._connecting:
                self.log("Host::handle_connect() is in the process of connecting", 2)
                return
            new_sock,address = self._original_socket.accept()
            self.log("New connection from: %s" % str(address), 1)
            self.log("Old Socket: %s" % str(self._original_socket), 1)
            self.log("New Socket: %s" % str(new_sock), 1)
            ip,port = address
            client_key = "%s-%d-%s" % (ip, port, self.get_socket_type_str())
            self._remote_key = client_key
            self._connecting = True
            self.set_socket(new_sock)
            self._master.client_to_host('CONNECT', self._remote_key, self.get_key(), 'CONNECT')
            self._master.notify()

    # Each port can only handle a single open connection,
    # so we have to be certain of our state.
    def _handle_accept(self, client_key):
        if self._connected:
            return
        # If we are in the process of disconnection,
        # we are not yet ready for a new connection
        if self._disconnecting:
            return
        # If a connection has not been initialized,
        # we are not ready to accept
        if not self._connecting:
            return
        # If the remote key was not generated for some reason,
        # we cannot establish a connection
        if self._remote_key is None:
            return
        if client_key == self._remote_key:
            self._connected = True
            self._connecting = False

    def handle_close(self):
        self.log("Host::handle_close()", 3)
        #self._connected_to = None
        if self._socket_type == socket.SOCK_STREAM:
            if not self._connected:
                self.log("Host::handle_close() not connected", 2)
                return
            self._master.client_to_host('CLOSE', self._remote_key, self.get_key(), 'CLOSE')
            self._handle_close()
            # Wake up asyncore so it can update file descriptors
            self._master.notify()

    def _handle_close(self):
        self.close()
        self._remote_key = None
        self._connecting = False
        self._connected = False
        self._disconnecting = False
        self.set_socket(self._original_socket)
        self._original_socket.listen(5)


# Pipes send/receive as if they were the actual client.
# They communicate directly with the target host.
class Pipe(PipeBase):
    def __init__(self, master, address, host_key, socket_type='UDP', bind_port=0, bind_host='', id=None):
        PipeBase.__init__(self, master, id=id)
        self._last_activity = calendar.timegm(time.gmtime())
        self._original_socket = None # Just keeping with convention.

        self._remote_key = host_key # Unique identifier for this pipe's remote connection.
        self.set_address(address)
        self.set_socket_type(socket_type)
        self._original_socket = socket.socket(socket.AF_INET, self.get_socket_type())
        self.set_socket(self._original_socket)
        try:
            self.bind((bind_host, bind_port))
        except:
            self.bind(('', 0))

    def _handle_read(self):
        self.log("Pipe::_handle_read()", 4)
        self.log("self._connected = %s" % str(self._connected), 5)
        packet,address = self.recvfrom(4096)
        self.log("packet size: %d" % len(packet), 5)
        if len(packet) > 0:
            self._master.host_to_client('FWD_DATA', self._remote_key, self.get_key(), packet)
        elif self._socket_type == socket.SOCK_STREAM:
            self.handle_close() # If we received an empty string from at TCP connection, the client closed their socket
        return len(packet)

    def handle_connect(self):
        self.log("Pipe::handle_connect()", 3)
        if self._socket_type == socket.SOCK_STREAM:
            self._master.host_to_client('ACCEPT', self._remote_key, self.get_key(), 'ACCEPT')
            self._connected = True

    # The Client class always initiates connections with the real host
    # I think I just added this to see if this was being called...
    def handle_accept(self):
        self.log("Pipe::handle_accept()", 3)

    def handle_close(self):
        self.log("Pipe::handle_close()", 3)
        if self._socket_type == socket.SOCK_STREAM:
            self._master.host_to_client('CLOSE', self._remote_key, self.get_key(), 'CLOSE')
            self._handle_close()
            # Wake up asyncore so it can update file descriptors
            self._master.notify()

    def _handle_close(self):
        self.close()
        self._remote_key = None
        self._connecting = False
        self._connected = False
        self._disconnecting = False
        self._master.del_pipe(self.get_key())

# Writes to itself to force asyncore to re-evaluated file descriptors
# This is necessary both when adding and removing pipes
# - A new pipe needs to be added to asyncore's file descriptor list
# - An old pipe should not be left in the list, or we may receive a
#   response that we are unable to handle. This may actually be an
#   issue still, as we do not tend to destroy the Client/Host after the
#   notification is done...
class Notifier(PipeBase):
    def __init__(self, master, id=None):
        PipeBase.__init__(self, master, id=id)
        self.sock_in = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.sock_in.bind(('', 0))
        self.set_address(('127.0.0.1', self.sock_in.getsockname()[1]))
        self.sock_out = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.set_socket(self.sock_in)

    def notify(self):
        self.log("-=NOTIFIER=-", 2)
        self.sock_out.sendto('CHANGED', self.get_address())

    def _handle_read(self):
        msg = self.sock_in.recv(7)
        return len(msg)

    def writable(self):
        return False


# Base class for TCP communication between upipe instances
class Internal(PipeBase):
    def __init__(self, master, id=None):
        PipeBase.__init__(self, master, id=id)
        self.r_cmd  = "[A-Za-z0-9_]+" # Command character set regex
        self.r_ip   = "(?:\d{1,3})[.](?:\d{1,3})[.](?:\d{1,3})[.](?:\d{1,3})" # IP address regex
        self.r_key  = "%s[-]\d+[-][a-zA-Z]+" % self.r_ip # key regex
        self.r_data = "[0-9A-Za-z+-_/=]+" # Data character set regex (base-64 encoded)
        self.regex_message = re.compile("^<\[(%s)\]\((%s)\)\((%s)\)\{(%s)\}>$" % (self.r_cmd, self.r_key, self.r_key, self.r_data))

    def _handle_read(self):
        data = self.recv(4096)
        msgs = map(lambda s: '<'+s, filter(lambda s: s!='', data.split('<')))
        self.log("%s::_handle_read() %d messages received" % (self.__class__.__name__, len(msgs)), 2)
        for msg in msgs:
            self.log("%s::_handle_read()  msg: %s" % (self.__class__.__name__, msg), 5)
            pot = self.melt(msg)
            if pot is None:
                return len(msg)
            command, src_key, dst_key, packet = pot
            self._src_to_dst(command, src_key, dst_key, packet)
        return len(data)

    # Assemble a message from keys and data
    def freeze(self, src_key, dst_key, packet, command='FWD_DATA'):
        message = "<[%s](%s)(%s){%s}>" % (command, src_key, dst_key, base64.standard_b64encode(packet))
        self.log("Freezing: %s" % str(message), 1)
        match = self.regex_message.search(message)
        if match:
            self.log("Freeze Succeeded!", 3)
            return message
        self.log("Freeze Failed!", 3)
        return None

    # Break down a message into keys and data
    def melt(self, message):
        self.log("Melting: %s" % str(message), 1)
        match = self.regex_message.search(message)
        if match:
            groups = match.groups()
            command = groups[0]
            src_key = groups[1]
            dst_key = groups[2]
            packet  = base64.standard_b64decode(groups[3])
            self.log("Melt Succeeded!", 3)
            return (command, src_key, dst_key, packet)
        self.log("Melt Failed!", 3)
        return None


# Client host comm. handler
class InternalHosts(Internal):
    def __init__(self, master, address):
        Internal.__init__(self, master)

        #sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        #sock.bind(('', 0))
        #self.set_socket(sock)
        #sock.connect(address)
        #sock.send('Greetings Server')
        #self.log("Client is connected on ('%s', %d)" % sock.getsockname(), 3)

        self._socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self._socket.bind(('', 0))
        self._socket.connect(address)
        self.set_socket(self._socket)
        #self._socket.send('Greetings Server')
        self.log("Client is connected on ('%s', %d)" % self._socket.getsockname(), 3)

    def handle_connect(self):
        pass
        #self.set_socket(self._socket.accept()[0])

    def handle_close(self):
        raise ExServerDied("The Client Server Died")
        #self.set_socket(None)

    def _src_to_dst(self, command, host_key, client_key, packet):
        self.log("InternalHosts::_src_to_dst()", 4)
        self._master.host_to_client(command, host_key, client_key, packet)


# Server client comm. handler
class InternalClients(Internal):
    def __init__(self, master, address):
        Internal.__init__(self, master)
        self._socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        try:
            self._socket.bind(address)
        except:
            self._socket.bind(('', 0))
        self.log("Server is running at ('%s', %d)" % self._socket.getsockname(), 0)
        self.set_socket(self._socket)
        self._socket.listen(1)

    def handle_connect(self):
        self.set_socket(self._socket.accept()[0])
        self.log("Client connection accepted", 0)

    def handle_close(self):
        self._master._remove_all_pipes()
        self.handle_connect()

    def _src_to_dst(self, command, client_key, host_key, packet):
        self.log("InternalClients::_src_to_dst()", 4)
        self._master.client_to_host(command, client_key, host_key, packet)
#/*}}}*/

# === Core Classes /*{{{*/
# Base class for pipe management
class MultiPipe(threading.Thread):
    def __init__(self, log=False, verbosity=0):
        threading.Thread.__init__(self)
        self._sockets = {}
        self._sockets['NOTIFIER'] = Notifier(self)
        self._running = False
        self._pipe_timeout = 300 #seconds
        self._log = log == True
        self._verbosity = verbosity
        self._local = True
        self._id_counter = Counter()

    def set_verbosity(verbosity):
        self._verbosity = verbosity 
        
    def get_verbosity():
        return self._verbosity

    def enable_packet_logging(self):
        self._log = True

    def disable_packet_logging(self):
        self._log = False

    def log(self, string, verbosity=1):
        if verbosity <= self._verbosity:
            print string

    def run(self):
        self._running = True
        while self._running:
            self._clean()
            self.log("MAP:", 6)
            self.log(str(self._sockets), 6)
            self.log(str(self._get_map()), 6)
            asyncore.loop(30.0, False, self._get_map(), 1)

        self._remove_all_pipes()

        try: self._sockets['INTERNAL'].close() 
        except: pass
        try: del self._sockets['INTERNAL']
        except: pass

        try: self._sockets['NOTIFIER'].close()
        except: pass
        del self._sockets['NOTIFIER']

    def notify(self):
        self._sockets['NOTIFIER'].notify()

    def add_host(self, address, socket_type='UDP', bind_port=0, bind_host=''):
        host = Host(self, address, socket_type, bind_port, bind_host, id=self._id_counter.inc())
        if not self._sockets.has_key(host.get_key()):
            self._sockets[host.get_key()] = host
            self.log("New Host: %s" % str(host.socket.getsockname()), 0)
            self.notify()
        else:
            c_address,c_port = address
            raise DuplicateHostException("%s:%d:%s:%d" % (bind_host,bind_port,c_address,c_port))

    def get_hosts(self):
        hosts = []
        for k,v in self._sockets.items():
            if k not in ('NOTIFIER', 'INTERNAL'):
                hosts.append(v)
        return hosts

    def get_host_keys(self):
        keys = []
        for k,v in self._sockets.items():
            if k not in ('NOTIFIER', 'INTERNAL'):
                keys.append(k)
        return keys


    def del_host(self, key):
        if self._sockets.has_key(key): 
            if self._sockets[key].__class__.__name__ == 'Host':
                del self._sockets[key]
                self.notify()
    
    def del_pipe(self, key):
        if self._sockets.has_key(key):
            if self._sockets[key].__class__.__name__ == 'Pipe':
                del self._sockets[key]
                self.notify()

    def stop(self):
        self._running = False
        self.notify()

    def _get_map(self):
        map = {}
        for k,s in self._sockets.items():
            map[s.socket] = s
        self.log("%s::_get_map" % (self.__class__.__name__,), 7)
        self.log(str(map), 7)
        self.log(str(self._sockets), 7)
        return map

    def _clean(self):
        now = calendar.timegm(time.gmtime())
        for k,v in self._sockets.items():
            if v.__class__.__name__ == 'Pipe':
                if (not v._socket_type == socket.SOCK_STREAM) or (not v._connected):
                    if not self._sockets.has_key(v._remote_key):
                        self.log("retiring client '%s' with no associated host" % k, 1)
                        del self._sockets[k]
                    elif (now - v._last_activity) > self._pipe_timeout:
                        self.log("retiring old client '%s'" % k, 1)
                        del self._sockets[k]

    def _remove_all_pipes(self):
        for k,v in self._sockets.items():
            if k not in ('NOTIFIER', 'INTERNAL'):
                del self._sockets[k]

    def host_to_client(self, command, host_key, client_key, packet):
        self.log("%s::host_to_client():" % (self.__class__.__name__,), 1)
        self.log("    host   : %s" % str(host_key), 1)
        self.log("    client : %s" % str(client_key), 1)
        self.log("    command: %s" % str(command), 1)
        self.log("    # bytes: %d" % len(packet), 1)
        self.log("", 1)

        h_ip,h_port,h_type = host_key.split('-',2)
        c_ip,c_port,c_type = client_key.split('-',2)
        if h_type != c_type:
            self.log("%s::client_to_host(): mismatch between client '%s' and host '%s' connection type" % (self.__class__.__name__, client_key, host_key), 0)
            return
        h_address = (h_ip,int(h_port))
        c_address = (c_ip,int(c_port))
        socket_type = c_type

        if command == 'CLOSE':
            if not self._sockets.has_key(host_key):
                self.log("%s::host_to_client(): recieved 'CLOSE' command for invalid host key (%s)" % (self.__class__.__name__, host_key), 0)
                return
            host = self._sockets[host_key]
            host.begin_disconnect()
        elif command == 'ACCEPT':
            if not self._sockets.has_key(host_key):
                self.log("%s::host_to_client(): recieved 'ACCEPT' command for invalid host key (%s)" % (self.__class__.__name__, host_key), 0)
                return
            host = self._sockets[host_key]
            if host._connected:
                self.log("%s::host_to_client(): recieved 'ACCEPT' command for host key (%s), but we are already connected to host key (%s)" % (self.__class__.__name__, host_key, self._remote_key), 0)
                return
            self.log("host_to_client():", 2)
            self.log("Host: %s" % str(host), 2)
            self.log("remote key: %s" % str(host._remote_key), 2)
            self.log("connecting: %s" % str(host._connecting), 2)
            self.log("connected : %s" % str(host._connected), 2)
            host._handle_accept(client_key)
        elif command == 'FWD_DATA':
            if self._local and not self._sockets.has_key(client_key):
                self.log("%s::host_to_client(): recieved 'FWD_DATA' command with invalid client key (%s)" % (self.__class__.__name__, client_key), 0)
                return
            if not self._sockets.has_key(host_key):
                if socket_type == 'TCP':
                    self.log("%s::host_to_client(): recieved 'FWD_DATA' command with invalid host key (%s)" % (self.__class__.__name__, host_key), 0)
                    return
                host = Host(self, h_address, h_type, bind_port=h_address[1])
                self._sockets[host.get_key()] = host
            else:
                host = self._sockets[host_key]
            self.log("MultiPipe::host_to_client(): adding packet", 3)
            self.log("    host   : %s" % str(host_key), 3)
            self.log("    client : %s" % str(client_key), 3)
            self.log("", 3)
            self.log_packet(host_key, client_key, packet)
            host.queue_packet(packet, c_address)

    def client_to_host(self, command, client_key, host_key, packet):
        self.log("%s::client_to_host():" % self.__class__.__name__, 1)
        self.log("    client : %s" % str(client_key), 1)
        self.log("    host   : %s" % str(host_key), 1)
        self.log("    command: %s" % str(command), 1)
        self.log("    # bytes: %d" % len(packet), 1)
        self.log("", 1)

        if self._local: 
            if not self._sockets.has_key(host_key):
                return
        h_ip,h_port,h_type = host_key.split('-',2)
        c_ip,c_port,c_type = client_key.split('-',2)
        if h_type != c_type:
            self.log("%s::client_to_host(): mismatch between client '%s' and host '%s' connection type" % (self.__class__.__name__, client_key, host_key), 0)
            return
        h_address = (h_ip,int(h_port))
        c_address = (c_ip,int(c_port))
        socket_type = c_type

        if command == 'CLOSE':
            if not self._sockets.has_key(client_key):
                return
            client = self._sockets[client_key]
            client.begin_disconnect()
        elif command == 'CONNECT':
            if not self._sockets.has_key(client_key):
                client = Pipe(self, c_address, host_key, socket_type=socket_type, bind_port=c_address[1])
                self._sockets[client.get_key()] = client
                client.connect(h_address)
            else:
                self.log("Client Key '%s' already exists" % client_key, 0)
        elif command == 'FWD_DATA':
            if not self._sockets.has_key(client_key):
                if socket_type == 'TCP':
                    self.log("%s::client_to_host(): received command 'FWD_DATA' for invalid client key (%s)" % (self.__class__.__name__, client_key), 0)
                    return
                client = Pipe(self, c_address, host_key, socket_type=socket_type, bind_port=c_address[1])
                self._sockets[client.get_key()] = client
            else:
                client = self._sockets[client_key]
            self.log_packet(client_key, host_key, packet)
            client.queue_packet(packet, h_address)

    def log_packet(self, source_key, destination_key, packet):
        if self._log:
            print "TRAFFIC FROM[%s] TO[%s] BYTES[%s] TIME[%s]" % (source_key, destination_key, len(packet), time.strftime("%Y-%m-%d (%j) %H:%M:%S", time.gmtime()))

# Base class for multi-host pipe server/client
class MultiPipeTCP(MultiPipe):
    def __init__(self, log=False, verbosity=0):
        MultiPipe.__init__(self, log=log, verbosity=verbosity)
        self._local = False

    def src_to_dst(self, command, src_key, dst_key, packet):
        message = self._sockets['INTERNAL'].freeze(src_key, dst_key, packet, command)
        self.log_packet(src_key, dst_key, packet)
        self._sockets['INTERNAL'].queue_packet(message)

    def _clean(self):
        now = calendar.timegm(time.gmtime())
        for k,v in self._sockets.items():
            if v.__class__.__name__ == 'Pipe':
                if (not v._socket_type == socket.SOCK_STREAM) or (not v._connected):
                    if (now - v._last_activity) > self._pipe_timeout:
                        self.log("retiring old client '%s'" % k, 1)
                        del self._sockets[k]


# Client pipe manager
class MultiPipeHosts(MultiPipeTCP):
    def __init__(self, address, log=False, verbosity=0):
        MultiPipeTCP.__init__(self, log=log, verbosity=verbosity)
        self._sockets['INTERNAL'] = InternalHosts(self, address)

    # Override the client_to_host() method so that packets
    # are forwarded over the TCP link rather than attempting
    # to send directly to the host.
    def client_to_host(self, command, client_key, host_key, packet):
        self.src_to_dst(command, client_key, host_key, packet)


# Server pipe manager
class MultiPipeClients(MultiPipeTCP):
    def __init__(self, address, log=False, verbosity=0):
        MultiPipeTCP.__init__(self, log=log, verbosity=verbosity)
        self._sockets['INTERNAL'] = InternalClients(self, address)

    # Override the host_to_client() method so that packets
    # are forwarded over the TCP link rather than attempting
    # to send directly to the client.
    def host_to_client(self, command, host_key, client_key, packet):
        self.src_to_dst(command, host_key, client_key, packet)
#/*}}}*/

# === Graphical User Interface /*{{{*/
class PipeGUI:
    def __init__(self, local=True, log=False, verbosity=0):
        self.window = gtk.Window(gtk.WINDOW_TOPLEVEL)
        self.window.set_title("Multi-Pipe")
        if ASL:
            self.window.set_icon(asl.new_icon('upipe'))

# ===== Widget Creation ===========================================
        self.vbox_main = gtk.VBox()
        self.vbox_hosts = gtk.VBox()
        self.hbox_new = gtk.HBox()
        self.hbox_control = gtk.HBox()

        #self.table_hosts = gtk.Table()
        self.hosts = {}

      # User Interaction Widgets
        self.entry_bind_address = gtk.Entry()
        self.label_sep1 = gtk.Label(":")
        self.entry_bind_port = gtk.Entry()
        self.label_sep2 = gtk.Label(":")
        self.entry_address = gtk.Entry()
        self.label_sep3 = gtk.Label(":")
        self.entry_port = gtk.Entry()
        self.combobox_type = gtk.combo_box_new_text()
        self.button_add = gtk.Button(stock=gtk.STOCK_ADD)

        self.button_add = gtk.Button(stock=None)
        self.hbox_add = gtk.HBox()
        self.image_add = gtk.Image()
        self.image_add.set_from_stock(gtk.STOCK_ADD, gtk.ICON_SIZE_MENU)
        self.label_add = gtk.Label('Add')
        self.button_add.add(self.hbox_add)
        self.hbox_add.pack_start(self.image_add, padding=1)
        self.hbox_add.pack_start(self.label_add, padding=1)

        self.checkbutton_log_packets = gtk.CheckButton("Log Packets")

        self.button_quit = gtk.Button(stock=None)
        self.hbox_quit = gtk.HBox()
        self.image_quit = gtk.Image()
        self.image_quit.set_from_stock(gtk.STOCK_QUIT, gtk.ICON_SIZE_MENU)
        self.label_quit  = gtk.Label('Quit')
        self.button_quit.add(self.hbox_quit)
        self.hbox_quit.pack_start(self.image_quit, padding=1)
        self.hbox_quit.pack_start(self.label_quit, padding=1)


# ===== Layout Configuration ======================================
        self.window.add(self.vbox_main)
        #self.window.set_size_request(250,250)

        self.vbox_main.pack_start(self.hbox_new, False, True, 0)
        self.vbox_main.pack_start(self.vbox_hosts, False, True, 0)
        self.vbox_main.pack_start(self.hbox_control, True,  True, 0)

        self.hbox_new.pack_start(self.entry_bind_address, False, False, 0)
        self.hbox_new.pack_start(self.label_sep1, False, False, 0)
        self.hbox_new.pack_start(self.entry_bind_port, False, False, 0)
        self.hbox_new.pack_start(self.label_sep2, False, False, 0)
        self.hbox_new.pack_start(self.entry_address, False, False, 0)
        self.hbox_new.pack_start(self.label_sep3, False, False, 0)
        self.hbox_new.pack_start(self.entry_port, False, False, 0)
        self.hbox_new.pack_start(self.combobox_type, False, False, 0)
        self.hbox_new.pack_start(self.button_add, False, False, 0)

        self.hbox_control.pack_start(self.checkbutton_log_packets, False, False, 0)
        self.hbox_control.pack_end(self.button_quit, False, False, 0)


# ===== Widget Configurations =====================================
        self.entry_bind_address.set_text("")
        self.entry_bind_address.set_width_chars(20)
        self.entry_bind_port.set_text("0")
        self.entry_bind_port.set_width_chars(5)
        self.entry_address.set_text("")
        self.entry_address.set_width_chars(20)
        self.entry_port.set_text("")
        self.entry_port.set_width_chars(5)
        self.combobox_type.append_text('TCP')
        self.combobox_type.append_text('UDP')
        self.combobox_type.set_active(1)
        self.checkbutton_log_packets.set_active(0)
        if log:
            self.checkbutton_log_packets.set_active(1)

# ===== Event Bindings ============================================
        self.button_add.connect("clicked",  self.callback_add,  None)
        self.button_quit.connect("clicked", self.callback_quit, None)
        self.checkbutton_log_packets.connect("toggled", self.callback_toggle_log_packets, None)

# ===== Keyboard Shortcuts ========================================
        self.window.connect("key-press-event", self.callback_key_pressed)

        # Show widgets
        self.window.show_all()
        self.window.set_resizable(False)

        self.host_counter = Counter()

        if local:
            self.core = MultiPipe(log=log)
        else:
            self.dialog = gtk.Dialog(title="Select Tunneling Server", buttons=(gtk.STOCK_CANCEL, gtk.RESPONSE_REJECT, gtk.STOCK_OK, gtk.RESPONSE_ACCEPT))
            if ASL:
                self.dialog.set_icon(asl.new_icon('upipe'))
            dialog_hbox = gtk.HBox()
            dialog_label = gtk.Label('Host:Port')
            dialog_entry_host  = gtk.Entry()
            dialog_label_colon = gtk.Label(':')
            dialog_entry_port  = gtk.Entry()

            dialog_entry_host.set_width_chars(20)
            dialog_entry_port.set_width_chars(5)

            dialog_hbox.pack_start(dialog_label,       False, False, 0)
            dialog_hbox.pack_start(dialog_entry_host,  False, False, 0)
            dialog_hbox.pack_start(dialog_label_colon, False, False, 0)
            dialog_hbox.pack_start(dialog_entry_port,  False, False, 0)

            self.dialog.vbox.pack_end(dialog_hbox)
            dialog_hbox.show_all()

            self.dialog.connect("key-press-event", self.callback_dialog_escape)
            dialog_entry_host.connect("key-press-event", self.callback_dialog_enter)
            dialog_entry_port.connect("key-press-event", self.callback_dialog_enter)

            response = self.dialog.run()
            host = dialog_entry_host.get_text()
            port = dialog_entry_port.get_text()
            self.dialog.destroy()

            if response == gtk.RESPONSE_ACCEPT:
                try:
                    host = socket.gethostbyname(host)
                except:
                    dialog = gtk.MessageDialog(type=gtk.MESSAGE_WARNING, buttons=gtk.BUTTONS_OK, message_format="Invalid host")
                    dialog.run()
                    dialog.destroy()
                    sys.exit(1)

                try:
                    port = int(port)
                    assert port > 0
                    assert port < 65536
                except:
                    dialog = gtk.MessageDialog(type=gtk.MESSAGE_WARNING, buttons=gtk.BUTTONS_OK, message_format="Invalid port")
                    dialog.run()
                    dialog.destroy()
                    sys.exit(1)

                address = (host, port)
                self.core = MultiPipeHosts(address, log=log, verbosity=verbosity)
            else:
                self.core = MultiPipe(log=log, verbosity=verbosity)

        # Start the asyncore manager thread
        self.core.start()


# ===== Callbacks =================================================
    def callback_key_pressed(self, widget, event, data=None):
        if event.state == gtk.gdk.MOD1_MASK:
            if event.keyval == ord('q'):
                self.close_application()

    def callback_dialog_escape(self, widget, event, data=None):
        if event.keyval == gtk.keysyms.Escape:
            self.dialog.response(gtk.RESPONSE_REJECT)

    def callback_dialog_enter(self, widget, event, data=None):
        if event.keyval == gtk.keysyms.Return:
            self.dialog.response(gtk.RESPONSE_ACCEPT)

    def callback_quit(self, widget, event, data=None):
        self.close_application()

    def callback_toggle_log_packets(self, widget, event, data=None):
        self.toggle_log_packets()

    def callback_add(self, widget, event, data=None):
        try:
            bind_host = socket.gethostbyname(self.entry_bind_address.get_text())
        except:
            self.log("Invalid bind address")
            return

        try:
            bind_port = int(self.entry_bind_port.get_text())
        except:
            self.log("Invalid bind port")
            return

        try:
            address = socket.gethostbyname(self.entry_address.get_text())
        except:
            self.log("Invalid address")
            return

        try:
            port = int(self.entry_port.get_text())
        except:
            self.log("Invalid port")
            return

        try:
            socket_type = self.combobox_type.get_active_text()
            self._add_host(address, port, socket_type, bind_port, bind_host)
        except Exception, e:
            self.log("Failed to add host %s:%d:%s:%d > %s" % (bind_host,bind_port,address,port,str(e)))
            pass

    def callback_delete(self, widget, event, data=None):
        self._del_host(data)


# ===== Public Methods ============================================
    def close_application(self):
        self.core.stop()
        gtk.main_quit()
        return False

    def toggle_log_packets(self):
        if self.checkbutton_log_packets.get_active():
            self.core.enable_packet_logging()
        else:
            self.core.disable_packet_logging()

    def log(self, string, verbosity=1):
        self.core.log(string, verbosity)

# ===== Private Methods ===========================================
    def _add_host(self, host, port, socket_type='UDP', bind_port=0, bind_host=''):
        ip = socket.gethostbyname(host)
        key = "%s-%d-%s" % (ip, port, socket_type)
        if self.hosts.has_key(key):
            self.log('Host exists, cannot re-add...', 0)
            return
        try:
            self.core.add_host((ip, port), socket_type, bind_port, bind_host)
        except DuplicateHostException:
            self.log('Host exists, cannot re-add...', 0)
            return
        except HostBindException:
            self.log('Could not bind to requested address (%s:%d)' % (bind_host,bind_port), 0)
            return

        if not self.core._sockets.has_key(key):
            self.log('Failed to add new host...', 0)
            return
        host = {}
        host['vbox-host'] = gtk.VBox()
        host['hbox-host'] = gtk.HBox()
        host['vbox-clients'] = gtk.VBox()

        host['entry-bind-ip'] = gtk.Entry()
        host['label-sep1'] = gtk.Label(":")
        host['entry-bind-port'] = gtk.Entry()
        host['label-sep2'] = gtk.Label(":")
        host['entry-ip'] = gtk.Entry()
        host['label-sep3'] = gtk.Label(":")
        host['entry-port'] = gtk.Entry()
        host['entry-type'] = gtk.Entry()
        host['button-del'] = gtk.Button(stock=None)
        host['hbox-del'] = gtk.HBox()
        host['image-del'] = gtk.Image()
        host['image-del'].set_from_stock(gtk.STOCK_DELETE, gtk.ICON_SIZE_MENU)
        host['label-del'] = gtk.Label('Delete')
        host['button-del'].add(host['hbox-del'])
        host['hbox-del'].pack_start(host['image-del'], padding=1)
        host['hbox-del'].pack_start(host['label-del'], padding=1)

        self.vbox_hosts.pack_start(host['vbox-host'], False, True, 0)
        host['vbox-host'].pack_start(host['hbox-host'], False, True, 0)
        host['vbox-host'].pack_start(host['vbox-clients'], False, True, 0)

        host['hbox-host'].pack_start(host['entry-bind-ip'], False, False, 0)
        host['hbox-host'].pack_start(host['label-sep1'], False, False, 0)
        host['hbox-host'].pack_start(host['entry-bind-port'], False, False, 0)
        host['hbox-host'].pack_start(host['label-sep2'], False, False, 0)
        host['hbox-host'].pack_start(host['entry-ip'], False, False, 0)
        host['hbox-host'].pack_start(host['label-sep3'], False, False, 0)
        host['hbox-host'].pack_start(host['entry-port'], False, False, 0)
        host['hbox-host'].pack_start(host['entry-type'], False, False, 0)
        host['hbox-host'].pack_start(host['button-del'], False, False, 0)

        host['entry-bind-ip'].set_text(str(self.core._sockets[key].getsockname()[0]))
        host['entry-bind-ip'].set_editable(False)
        host['entry-bind-ip'].set_width_chars(20)
        host['entry-bind-port'].set_text(str(self.core._sockets[key].getsockname()[1]))
        host['entry-bind-port'].set_editable(False)
        host['entry-bind-port'].set_width_chars(5)
        host['entry-ip'].set_text(ip)
        host['entry-ip'].set_editable(False)
        host['entry-ip'].set_width_chars(20)
        host['entry-port'].set_text(str(port))
        host['entry-port'].set_editable(False)
        host['entry-port'].set_width_chars(5)
        host['entry-type'].set_text(str(socket_type))
        host['entry-type'].set_editable(False)
        host['entry-type'].set_width_chars(5)

        host['button-del'].connect("clicked", self.callback_delete, None, key)

        self.hosts[key] = host
        self.hosts[key]['vbox-host'].show_all()
        self.window.resize_children()

    def _del_host(self, key):
        if self.hosts.has_key(key):
            host = self.hosts[key]
            for k,_ in self.hosts[key].items():
                host[k].hide()
                del host[k]
            del self.hosts[key]
        self.core.del_host(key)
        self.window.resize_children()
        self.window.check_resize()

#/*}}}*/

# === Command Interface /*{{{*/
class PipeCI(threading.Thread):
    def __init__(self, core, log=False, verbosity=0, print_function=None, stop_queue=None):
        threading.Thread.__init__(self)
        self.core = core
        self.running = False
        self.stop_queue = stop_queue

        self.commands = {
            "add"    : (self.add_pipe,    "Add a new pipe", "[[bind_host:]bind_port:]address:port:TCP|UDP"),
            "help"   : (self.print_help,  "Show this list of commands", ""),
            "list"   : (self.list_pipes,  "List the existing pipes", ""),
            "quit"   : (self.quit,        "Close the program", ""),
            "remove" : (self.remove_pipe, "Remove an existing pipe", "pipe_id"),
        }

        self._print = self._to_stdout
        if print_function:
            self._print = print_function

        # Start the asyncore manager thread
        self.core.start()

    def _to_stdout(self, text):
        print text

    def run(self):

        self.running = True
        while self.running:
            try:
                cmd_string = raw_input("> ")
                self.process_command(cmd_string)
            except EOFError:
                print
                continue
            except KeyboardInterrupt:
                try:
                    print
                except EOFError:
                    pass
                continue
            except:
                self.stop_core()
                raise
        self.stop_core()
        self.stop_queue.put("DONE")

    def process_command(self, cmd_string):
        parts = map(lambda p: p.strip(), cmd_string.split(' ', 1))
        command = parts[0]
        if command == "":
            return
        arg_string = ""
        if len(parts) > 1:
            arg_string = parts[1]
        if not self.commands.has_key(command):
            self._print("Unrecognized command")
            return
        self.commands[command][0](arg_string)

    def print_help(self, arg_line=''):
        max_key_len = max(map(len, self.commands.keys()))
        for command in sorted(self.commands.keys()):
            _,description,arg_spec = self.commands[command]
            if len(arg_spec):
                print "%s : %s (%s %s)" % (command.rjust(max_key_len), description, command, arg_spec)
            else:
                print "%s : %s" % (command.rjust(max_key_len), description)

    def add_pipe(self, arg_line):
        parts = verify_pipe(arg_line)
        if parts is None:
            self._print("Invalid pipe definition")
            return
        bind_host,bind_port,address,port,pipe_type = parts
        self.core.add_host((address,port), pipe_type, bind_port, bind_host)

    def list_pipes(self, arg_line=''):
        hosts = self.core.get_hosts()
        ids = []
        pipes = []
        if len(hosts) < 1:
            self._print("No open pipes.")
            return

        for host in hosts:
            id = host.get_id()
            ids.append(id)
            pipes.append((id,host))
        pipes = sorted(pipes)

        max_id_len = max(map(len, map(str, ids)))
        self._print("Open Pipes:")
        for id,pipe in pipes:
            self._print("  %s > %s" % (str(id).rjust(max_id_len), pipe))

    def remove_pipe(self, arg_line):
        try:
            id = int(arg_line)
        except:
            self._print("Invalid host ID format")
            return

        key = None
        hosts = self.core.get_hosts()
        for host in hosts:
            if host.get_id() == id:
                key = host.get_key()

        if key is None:
            self._print("Could not find host with ID '%s'" % str(id))
            return
            
        self.core.del_host(key)
        self._print("Host deleted")

    def quit(self, arg_line=''):
        self.running = False
    
    def stop_core(self):
        self.core.stop()
        self.core.join()
#/*}}}*/

# === main /*{{{*/
def main():
    pipe = None
    gui = None
    ci = None
    try:
        use_message = """usage: %prog [options]

PIPE_SPEC: [[bind_host:]bind_port:]remote_host:remote_port:TCP|UDP"""
        option_list = []
        option_list.append(optparse.make_option("-c", "--config-file", dest="config_file", action="store", help="configuration file from which to read connection information"))
        option_list.append(optparse.make_option("-d", "--daemon", dest="daemon", action="store_true", help="run in daemon mode (disable program command line)"))
        option_list.append(optparse.make_option("-g", "--gui", dest="gui", action="store_true", help="launch in graphical mode"))
        option_list.append(optparse.make_option("-H", "--host", dest="host", action="store", help="The server or bind host for client or server respectively"))
        option_list.append(optparse.make_option("-l", "--log", dest="log", action="store_true", help="log traffic"))
        option_list.append(optparse.make_option("-p", "--port", dest="port", action="store", help="The server or bind port for client or server respectively"))
        option_list.append(optparse.make_option("-P", "--pipe", dest="pipes", action="append", metavar="PIPE_SPEC", help="start with one or more pipes open"))
        option_list.append(optparse.make_option("-q", "--quiet", dest="quiet", action="store_true", help="Only report errors, no traffic information"))
        option_list.append(optparse.make_option("-s", "--server", dest="server", action="store_true", help="start as server instead of client or unified mode"))
        option_list.append(optparse.make_option("-v", action="count", dest="verbosity", help="specify multiple time to increase verbosity"))
        parser = optparse.OptionParser(option_list=option_list, usage=use_message)
        options, args = parser.parse_args()

        if options.quiet:
            verbosity = 0
        else:
            if options.verbosity is None:
                verbosity = 1
            else:
                verbosity = options.verbosity + 1

        if options.gui:
            if not HAS_GUI:
                print "System does not support the GUI component."
                parser.print_help()
                sys.exit(1)
            gui = PipeGUI(local=False, log=options.log, verbosity=verbosity)
            gtk.main()
        else:
            ip   = None
            port = None
            core_type = None
            pipe_strings = []
            interactive = True

            # Read options from config file
            if options.config_file:
                # get type UNIFIED|SERVER|CLIENT
                config = parse_config(options.config_file)
                if config.has_key('type'):
                    core_type = config['type']
                    if core_type not in ('CLIENT', 'SERVER', 'UNIFIED'):
                        raise CoreTypeException("Invalid run type '%s'" % core_type)
                if config.has_key('ip'):
                    ip = config['ip']
                if config.has_key('port'):
                    port = int(config['port'])
                if config.has_key('pipes'):
                    pipe_strings.extend(config['pipes'])

            if options.host:
                ip = options.host
            if options.port:
                port = int(options.port)

            if options.server:
                core_type = 'SERVER'
            elif not core_type: 
                if ip or port:
                    core_type = 'CLIENT'
                else:
                    core_type = 'UNIFIED'

            if ip is None:
                ip = ''
            if port is None:
                port = 8000

            if options.daemon:
                interactive = False

            # Determine which mode to run
            if core_type == 'SERVER':
                pipe = MultiPipeClients((ip, port), log=options.log, verbosity=verbosity)
                interactive = False
            elif core_type == 'CLIENT':
                pipe = MultiPipeHosts((ip, port), log=options.log, verbosity=verbosity)
            elif core_type == 'UNIFIED':
                pipe = MultiPipe(log=options.log, verbosity=verbosity)
            else:
                raise Exception("Invalid type specification")

            
            if options.pipes:
                for pipe_def in options.pipes:
                    pipe_strings.append(pipe_def)

            for pipe_str in pipe_strings:
                pipe_vals = verify_pipe(pipe_str)
                if pipe_vals is None:
                    raise Exception("Invalid pipe specification: %s" % pipe_str)
                ba,bp,a,p,t = pipe_vals
                pipe.add_host((a,p),t,bp,ba)

            if interactive:
                stop_queue = Queue.Queue()
                ci = PipeCI(pipe, log=False, verbosity=options.verbosity, stop_queue=stop_queue)
                ci.start()
                stop_queue.get()
            else:
                pipe.run()
    except KeyboardInterrupt:
        print "Keyboard Interrupt [^C]"
        if gui:
            try: gui.close_application()
            except RuntimeError: pass
        elif ci:
            try: ci.quit()
            except RuntimeError: pass
        elif pipe:
            pipe.stop()
    except ExServerDied, e:
        print str(e)
    except UPipeException, e:
        print "%s: %s" % (e.__class__.__name__, str(e))
    except Exception, e:
        print e
        if type(e) != tuple:
            raise
        elif len(e) != 2:
            raise
        elif e[0] not in (9,):
            raise
        else:
            pass

    #except Exception, e:
    #    print "Caught an unanticipated exception:"
    #    print str(e)
#/*}}}*/

if __name__ == "__main__":
    try:
        import psyco
        #psyco.full()
        psyco.profile()
        print "Psyco JIT enabled."
    except ImportError:
        pass

    main()

