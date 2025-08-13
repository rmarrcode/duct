from dependency_test.b import b

def a():
    return "a" + b()

print(a())