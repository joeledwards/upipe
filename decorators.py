#!/usr/bin/env python

def classDecorator(func):
    def decorator(self, *args):
        print "before: inner value", self.inner_value
        func(self, *args)
        print "after: inner value", self.inner_value
    return decorator

class Decorated:
    def __init__(self):
        self.inner_value = "original"

    @classDecorator
    def changeValue(self):
        self.inner_value = "panultimate"

    @classDecorator
    def changeAgain(self, value):
        self.inner_value = "ultimate"
        print "value =", value


def functionDecorator(func):
    def decorator():
        print "before"
        func()
        print "after"
    return decorator

@functionDecorator
def sampleFunction():
    print "during"


sampleFunction()

d = Decorated()
d.changeValue()
d.changeAgain("Joel")


