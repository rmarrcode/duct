from dependency_test.b import b
import json

def a():
    return "a" + b()

print(a())