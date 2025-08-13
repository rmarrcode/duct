from dependency_test.b import b
import os
from dependency_test.typeshit import Typeshit

def a():
    typeshit = Typeshit("typeshit")
    print(str(typeshit))
    typeshit.test()
    print(os.getcwd())
    return "a" + b()

print(a())