import pytest
from microegg import EGraph, Node, Term


def test_congruence_and_native_types():
    g = EGraph()
    a, b = g.add("a", []), g.add("b", [])
    assert g.add_node(Node("a", [])) == a
    fa, fb = g.add("f", [a]), g.add("f", [b])
    assert not g.is_eq(fa, fb)
    assert g.union(a, b)
    assert not g.union(a, b)
    assert g.is_eq(fa, fb)
    assert Node("f", [a]) == Node("f", [a])
    assert hash(Term.App("f", [Term.Var("x")])) == hash(Term.App("f", [Term.Var("x")]))
    assert Node("f", [a]).args == [a]
    with pytest.raises(ValueError):
        g.add("f", [999])


def test_repeated_variable_and_operator_mismatch():
    g = EGraph()
    a, b = g.add("a", []), g.add("b", [])
    aa, bb, ab = [g.add("f", args) for args in ([a, a], [b, b], [a, b])]
    g.union(aa, bb)
    g.union(bb, ab)
    x, y = Term.Var("x"), Term.Var("y")
    assert len(g.ematch(Term.App("f", [x, x]), aa)) == 2
    assert len(g.ematch(Term.App("f", [x, y]), aa)) == 3
    assert g.ematch(Term.App("other", [x, y]), aa) == []
    assert g.ematch(Term.App("f", [x]), aa) == []


def test_rules_and_validation():
    g = EGraph()
    x = Term.Var("x")
    a = g.add("a", [])
    fa = g.add("f", [a])
    g.add_rule(Term.App("f", [x]), x)
    assert g.run(0) == 0
    assert g.run(5) <= 5
    assert g.is_eq(a, fa)
    assert g.extract(fa) == (1, Term.App("a", []))
    with pytest.raises(ValueError):
        g.add_term(x)
    with pytest.raises(ValueError):
        g.add_rule(x, Term.Var("unbound"))


def test_ac():
    g = EGraph()
    x, y, z = map(Term.Var, "xyz")
    plus = lambda a, b: Term.App("+", [a, b])
    a, b, c = [Term.App(s, []) for s in "abc"]
    start = g.add_term(plus(plus(a, b), c))
    goal = g.add_term(plus(c, plus(b, a)))
    g.add_rule(plus(x, y), plus(y, x))
    g.add_rule(plus(plus(x, y), z), plus(x, plus(y, z)))
    g.add_rule(plus(x, plus(y, z)), plus(plus(x, y), z))
    g.run(10)
    assert g.is_eq(start, goal)
    assert g.num_classes() == 7


def test_extraction_relaxes_mutually_recursive_alternatives():
    g = EGraph()
    a, b = g.add("a", []), g.add("b", [])
    fa, fb = g.add("f", [a]), g.add("f", [b])
    g.union(a, fb)
    g.union(b, fa)
    assert g.extract(a)[0] == 1
    assert g.extract(b)[0] == 1
