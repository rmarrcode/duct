class Typeshit:
    def __init__(self, name: str):
        self.name = name

    def __str__(self):
        return self.name

    def __repr__(self):
        return self.name

    def test(self):
        return "test"

    def __eq__(self, other):
        return self.name == other.name