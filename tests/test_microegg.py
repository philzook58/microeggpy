import microeggpy
from microeggpy import EGraph, Term


def test_add_node():
    g = microeggpy.EGraph()
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
    assert repr(p) == """Var("x")"""
    fx = Term.App("f", [p])
    assert repr(fx) == """App("f", [Var("x")])"""
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
    assert E.ematch(fx, id1) == [{"x": a}, {"x": b}]

    match fx2:
        case Term.App("f", _):
            assert True
        case _:
            assert False
