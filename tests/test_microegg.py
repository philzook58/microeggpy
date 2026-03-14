from microegg import EGraph, Term, Node
from dataclasses import dataclass


@dataclass
class FuncDeclRef:
    f: str
    E: EGraph

    def __call__(self, *args):
        id = self.E.add(self.f, args)
        return ExprRef(id, self.E)


@dataclass
class ExprRef:
    id: int
    E: EGraph

    def __add__(self, other):
        return FuncDeclRef("+", self.E)(self, other)


def test_add_node():
    g = EGraph()
    id1 = g.add("a", [])
    id2 = g.add("a", [])
    assert id1 == id2
    id3 = g.add("b", [])
    assert id3 != id1
    assert not g.is_eq(id1, id3)
    g.union(id1, id3)
    assert g.is_eq(id1, id3)


def test_pattern():
    p = Term.Var("x")
    assert repr(p) == "Var(x)"
    fx = Term.App("f", [p])
    assert repr(fx) == "App(f, [Var(x)])"
    fx2 = Term.App("f", [Term.Var("x")])
    assert fx == fx2
    assert hash(fx) == hash(fx2)
    E = EGraph()
    a = E.add("a", [])
    id1 = E.add("f", [E.add("a", [])])
    assert E.ematch(fx, id1) == [{"x": a}]
    b = E.add("b", [])
    E.union(a, b)
    E.rebuild()
    assert len(E.ematch(fx, id1)) == 2  # [{"x": a}, {"x": b}]

    match fx2:
        case Term.App("f", _):
            assert True
        case _:
            assert False

    """
    assert E.to_list() == [
        (("a", []), 2),
        (("f", [0]), 1),
        (("b", []), 2),
        (("f", [2]), 1),
    ]
    """


def test_apply_rules():
    E = EGraph()
    a = E.add("a", [])
    b = E.add("b", [])
    fa = E.add("f", [a])
    E.union(a, b)
    E.rebuild()
    p = Term.App("a", [])
    x = Term.Var("x")
    fx = Term.App("f", [x])
    # assert E.ematch(fx, fa) == None
    assert E.ematch(fx, a) == []
    E.add_rule(fx, p)
    E.apply_rules(fa)
    E.apply_rules(a)
    assert E.is_eq(a, b)
    assert E.is_eq(a, fa)


def test_ac():
    E = EGraph()
    a = E.add("a", [])
    acc = a
    for i in range(3):
        n = E.add(str(i), [])
        acc = E.add("+", [acc, n])
    x = Term.Var("x")
    y = Term.Var("y")
    z = Term.Var("z")
    plus = lambda x, y: Term.App("+", [x, y])

    E.add_rule(plus(x, plus(y, z)), plus(plus(x, y), z))
    E.add_rule(plus(plus(x, y), z), plus(x, plus(y, z)))
    E.add_rule(plus(x, y), plus(y, x))

    E.run(2)
    # assert E.size() == 16


def test_extract_skips_cycles():
    E = EGraph()
    a = E.add("a", [])
    fa = E.add("f", [a])
    E.union(a, fa)
    E.rebuild()

    cost, term = E.extract(fa)
    assert cost == 1
    assert term == Term.App("a", [])


def test_memo():
    E = EGraph()
    a = E.add("a", [])
    b = E.add("b", [])
    fa = E.add("f", [a])
    fb = E.add("f", [b])
    assert len(E.memo) == 4
    assert len(E.uf) == 4
    print(E.memo)
    Node("f", [a]) in E.memo.keys()
    E.memo[Node("f", [a])] == fa


def test_compact():
    E = EGraph()
    a = E.add("a", [])
    b = E.add("b", [])
    c = E.add("c", [])
    fa = E.add("f", [a])
    fb = E.add("f", [b])
    fc = E.add("f", [c])
    assert E.num_classes() == 6
    E.union(a, b)
    E.union(b, c)
    assert E.num_classes() == 4
    # compaction should actually do rebuilding also
    compacted = E.compact()
    assert len(compacted.nodes) == 4
    assert compacted.num_classes() == 2

    E.rebuild()
    compacted = E.compact()
    assert len(E.nodes) == 6
    assert E.num_classes() == 2

    assert len(compacted.nodes) == 4
    assert compacted.num_classes() == 2
