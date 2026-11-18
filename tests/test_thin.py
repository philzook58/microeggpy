import importlib
import random

import pytest
from microegg import thin

T = thin.Term
A, F, B, M = T.atom, T.fvar, T.bvar, T.meta
app, bind = T.app, T.binder


def apps(op, *args):
    term = A(op)
    for arg in args:
        term = app(term, arg)
    return term


def test_namespace_and_recursive_constructors():
    assert importlib.import_module("microegg.thin") is thin
    term = bind("lam", app(A("f"), B(0)))
    assert term == bind("lam", app(A("f"), B(0)))
    assert hash(term) == hash(bind("lam", app(A("f"), B(0))))
    assert "Binder" in repr(term)
    g = thin.EGraph()
    result = g.add(term)
    assert g.extract(result) == (4, term)
    assert not hasattr(g, "substitute")


def test_thinning_algebra_and_weakening():
    outer = thin.Thin([True, False, True])
    inner = thin.Thin([False, True])
    assert outer.compose(inner).bits == [False, False, True]
    assert outer.dom() == 2 and outer.cod() == 3
    assert outer.compose(thin.Thin.identity(2)) == outer
    with pytest.raises(ValueError):
        outer.compose(thin.Thin.identity(3))
    g = thin.EGraph()
    x = g.var(1, 0)
    lifted = x.weaken(outer.compose(thin.Thin([True, False])))
    assert lifted.ctx == 3 and lifted.raw == x.raw
    assert lifted.thinning.bits == [True, False, False]
    assert lifted.in_context(1) == x
    with pytest.raises(ValueError):
        lifted.in_context(0)
    with pytest.raises(ValueError):
        x.weaken(thin.Thin.identity(2))


def test_alpha_sharing_and_shadowing():
    g = thin.EGraph()
    term = bind("lam", bind("lam", B(0)))
    assert g.add(term) == g.add(bind("lam", bind("lam", B(0))))
    assert not g.is_eq(g.add(term), g.add(bind("lam", bind("lam", B(1)))))
    x, y = g.var(3, 0), g.var(3, 2)
    fx, fy = g.app(g.atom("f", 3), x), g.app(g.atom("f", 3), y)
    assert fx.raw == fy.raw
    assert fx.thinning.bits == [True, False, False]
    assert fy.thinning.bits == [False, False, True]
    assert not g.is_eq(fx, fy)
    assert g.add(bind("sum", F(0)), 1) != g.add(bind("sum", B(0)))
    assert g.extract(g.add(bind("lam", F(1)), 3))[1] == bind("lam", F(1))


def test_invalid_scope_and_concrete_metavariables():
    g = thin.EGraph()
    for term in (B(0), F(0), bind("lam", B(1)), M("x")):
        with pytest.raises(ValueError):
            g.add(term)
    with pytest.raises(ValueError):
        g.var(0, 0)
    with pytest.raises(ValueError):
        g.binder("lam", g.atom("a"))
    with pytest.raises(ValueError):
        g.union(g.atom("a"), g.atom("a", 1))
    with pytest.raises(ValueError):
        g.app(g.atom("a"), g.var(1, 0))


def test_equalizer_and_dependency_propagation():
    g = thin.EGraph()
    x, y = g.var(2, 0), g.var(2, 1)
    fx, fy = g.app(g.atom("f", 2), x), g.app(g.atom("f", 2), y)
    parent_x, parent_y = g.app(g.atom("g", 2), fx), g.app(g.atom("g", 2), fy)
    lam_x, lam_y = g.binder("sum", fx), g.binder("sum", fy)
    assert fx.raw == fy.raw
    assert g.union(fx, fy)
    assert g.rebuild()
    assert not g.rebuild()
    assert g.is_eq(parent_x, parent_y)
    assert g.is_eq(lam_x, lam_y)
    assert g.find(fx).thinning.bits == [False, False]
    closed = g.find(fx).in_context(0)
    with pytest.raises(ValueError, match="finite"):
        g.extract(closed)  # f needs a variable, and this context has none
    g.union(fx, g.atom("constant", 2))
    assert g.extract(closed) == (1, A("constant"))


def test_intersection_of_incomparable_dependencies():
    g = thin.EGraph()
    left = g.add(apps("pair", F(0), F(1)), 3)
    right = g.add(apps("other", F(1), F(2)), 3)
    assert g.union(left, right)
    g.rebuild()
    assert g.find(left).thinning.bits == [False, True, False]
    assert g.is_eq(left, right)


def test_count_neutral_rebuild_reports_dependency_change():
    g = thin.EGraph()
    x = g.var(1, 0)
    zero = g.atom("0", 1)
    fx = g.app(g.atom("f", 1), x)
    g.union(x, zero)
    before = g.num_classes()
    assert g.rebuild()
    assert g.num_classes() == before
    assert g.find(fx).thinning.bits == [False]
    assert g.extract(g.find(fx).in_context(0)) == (3, app(A("f"), A("0")))


def test_capture_permissions_and_sibling_binders():
    g = thin.EGraph()
    identity = g.add(bind("lam", B(0)))
    assert g.ematch(bind("lam", M("x")), identity) == []
    matches = g.ematch(bind("lam", M("body", [0])), identity)
    assert len(matches) == 1
    assert g.is_eq(matches[0]["body"], g.var(1, 0))
    constant = g.add(bind("lam", A("a")))
    assert len(g.ematch(bind("lam", M("x")), constant)) == 1
    pair = apps("pair", A("a"), bind("lam", A("a")))
    pattern = apps("pair", M("x"), bind("lam", M("x")))
    assert len(g.ematch(pattern, g.add(pair))) == 1
    assert g.ematch(pattern, g.add(apps("pair", A("a"), bind("lam", B(0))))) == []
    siblings = apps("pair", bind("lam", B(0)), bind("sum", B(0)))
    p = apps("pair", bind("lam", M("x", [0])), bind("sum", M("x", [0])))
    assert len(g.ematch(p, g.add(siblings))) == 1


def test_repeated_capture_moves_between_different_local_contexts():
    g = thin.EGraph()
    pattern = apps("pair", bind("lam", M("x", [0])), bind("lam", bind("sum", M("x", [1]))))
    good = apps("pair", bind("lam", B(0)), bind("lam", bind("sum", B(1))))
    bad = apps("pair", bind("lam", B(0)), bind("lam", bind("sum", B(0))))
    assert g.ematch(pattern, g.add(good))
    assert not g.ematch(pattern, g.add(bad))


def test_ordered_multivariable_capture_and_ambient_context():
    g = thin.EGraph()
    term = bind("lam", bind("sum", apps("pair", F(1), B(1), B(0))))
    pat = bind("lam", bind("sum", M("body", [1, 0])))
    target = g.add(term, 3)
    matches = g.ematch(pat, target)
    assert len(matches) == 1
    assert matches[0]["body"].ctx == 5
    expected = g.add(apps("pair", F(1), F(3), F(4)), 5)
    assert g.is_eq(matches[0]["body"], expected)


@pytest.mark.parametrize("lhs,rhs", [
    (bind("lam", M("x", [1])), A("a")),
    (bind("lam", M("x", [0, 0])), A("a")),
    (bind("lam", bind("lam", M("x", [0, 1]))), A("a")),
    (apps("pair", M("x"), bind("lam", M("x", [0]))), A("a")),
    (M("x"), M("unbound")),
    (M("x"), bind("lam", M("x", [0]))),
    (bind("lam", bind("lam", M("x", [1, 0]))), bind("lam", bind("lam", M("x", [0, 1])))),
    (M("x"), B(0)),
])
def test_rule_validation(lhs, rhs):
    with pytest.raises(ValueError):
        thin.EGraph().add_rule(lhs, rhs)


def test_arbitrary_miller_arguments_are_not_syntax():
    with pytest.raises(TypeError):
        M("x", [A("a")])


def test_independent_capture_can_move_under_a_binder():
    g = thin.EGraph()
    g.add_rule(apps("wrap", M("x")), bind("lam", M("x")))
    target = g.add(apps("wrap", A("a")))
    assert g.run(4) <= 4
    assert g.is_eq(target, g.add(bind("lam", A("a"))))


def test_generic_sum_factorization():
    g = thin.EGraph()
    lhs = bind("sum", apps("mul", M("a"), M("body", [0])))
    rhs = apps("mul", M("a"), bind("sum", M("body", [0])))
    g.add_rule(lhs, rhs)
    good = g.add(bind("sum", apps("mul", A("a"), apps("f", B(0)))))
    bad = g.add(bind("sum", apps("mul", B(0), A("a"))))
    assert g.ematch(lhs, good)
    assert not g.ematch(lhs, bad)
    g.run(5)
    expected = g.add(apps("mul", A("a"), bind("sum", apps("f", B(0)))))
    assert g.is_eq(good, expected)
    assert not g.is_eq(bad, expected)


def test_redundant_node_placements_are_all_matched():
    g = thin.EGraph()
    x, y = g.var(2, 0), g.var(2, 1)
    fx, fy = g.app(g.atom("f", 2), x), g.app(g.atom("f", 2), y)
    g.union(fx, fy)
    # Both concrete variable positions are valid representatives after pruning.
    assert g.ematch(apps("f", F(0)), fx)
    assert g.ematch(apps("f", F(1)), fx)


def test_extraction_cycles_and_new_scope_under_binders():
    g = thin.EGraph()
    a = g.atom("a")
    fa = g.app(g.atom("f"), a)
    g.union(a, fa)
    assert g.extract(a) == (1, A("a"))
    # Equate the variable class to a binder over itself. It has no variable
    # representative in the empty context, but lambda x.x is finite there.
    h = thin.EGraph()
    v = h.var(2, 0)
    vv = h.var(2, 1)
    h.union(v, vv)
    h.rebuild()
    closed = h.find(v).in_context(0)
    body = h.find(v).in_context(1)
    lam = h.binder("lam", body)
    h.union(closed, lam)
    cost, term = h.extract(closed)
    assert (cost, term) == (2, bind("lam", B(0)))
    assert h.is_eq(h.add(term), closed)


def test_contexts_larger_than_machine_word():
    g = thin.EGraph()
    target = g.add(bind("lam", apps("pair", F(80), B(0))), 100)
    assert target.ctx == 100
    assert g.extract(target)[1] == bind("lam", apps("pair", F(80), B(0)))
    assert g.find(target).thinning.dom() == 1


def test_generated_terms_extract_and_reinsert():
    rng = random.Random(127)

    def term(top, depth, budget):
        if budget == 0:
            options = [A("a"), A("b")]
            options += [F(i) for i in range(top)]
            options += [B(i) for i in range(depth)]
            return rng.choice(options)
        if rng.randrange(2):
            return bind(rng.choice(["sum", "lam"]), term(top, depth + 1, budget - 1))
        return app(term(top, depth, budget - 1), term(top, depth, budget - 1))

    g = thin.EGraph()
    ids = [g.add(term(3, 0, 3), 3) for _ in range(30)]
    for _ in range(8):
        a, b = rng.sample(ids, 2)
        g.union(a, b)
    for target in ids:
        cost, result = g.extract(target)
        assert cost > 0
        assert g.is_eq(target, g.add(result, 3))


def test_nested_extraction_requirements_can_exceed_any_single_enode():
    g = thin.EGraph()
    mask = lambda bits: thin.Thin([bool(x) for x in bits])
    b = g.add(apps("triple", F(0), F(1), F(2)), 3)
    # B ignores its middle argument, but every stored representative still
    # mentions that argument between its two surviving dependencies.
    g.union(b.weaken(mask([1, 1, 0, 1])), b.weaken(mask([1, 0, 1, 1])))
    g.rebuild()
    a = g.app(b.in_context(4), g.var(4, 3))
    g.union(a.weaken(mask([1, 1, 1, 1, 0, 0, 0, 0])),
            a.weaken(mask([0, 0, 0, 0, 1, 1, 1, 1])))
    g.rebuild()
    cost, term = g.extract(a)
    assert cost == 9
    assert g.is_eq(a, g.add(term, 4))
    closed = g.find(a).in_context(0)
    with pytest.raises(ValueError, match="finite"):
        g.extract(closed)
    # Recursive binders can supply the four required variables. A raw-ID cycle
    # check or a per-node context-size cutoff would incorrectly reject this.
    lam = g.binder("lam", closed.in_context(1))
    g.union(closed, lam)
    cost, term = g.extract(closed)
    assert cost == 13
    assert g.is_eq(closed, g.add(term))


def test_extraction_keeps_cost_and_scope_tradeoffs():
    g = thin.EGraph()
    fx = g.add(apps("f", F(0)), 1)
    g.union(fx.weaken(thin.Thin([True, False])),
            fx.weaken(thin.Thin([False, True])))
    expensive = apps("g", A("a"), A("b"))
    g.union(fx, g.add(expensive, 1))
    g.rebuild()
    assert g.extract(fx)[0] == 3
    closed = g.find(fx).in_context(0)
    assert g.extract(closed) == (5, expensive)
    # Both children can reuse the same extra variable, rather than requiring
    # two distinct slots just because they were originally constructed apart.
    pair = g.app(fx, fx)
    assert g.extract(pair)[0] == 7
    assert g.extract(g.find(pair).in_context(0))[0] == 11


def test_extraction_distinguishes_leading_and_trailing_slots():
    g = thin.EGraph()
    xy = g.add(app(F(0), F(1)), 2)
    g.union(xy.weaken(thin.Thin([True, True, False])),
            xy.weaken(thin.Thin([True, False, True])))
    g.rebuild()
    x_only = g.find(xy).in_context(1)
    with pytest.raises(ValueError, match="finite"):
        g.extract(x_only)
    assert g.extract(x_only.in_context(2)) == (3, app(F(0), F(1)))
    last = x_only.weaken(thin.Thin([False, True]))
    with pytest.raises(ValueError, match="finite"):
        g.extract(last)
    # A binder cannot provide a slot *after* its bound variable.
    lam = g.binder("lam", x_only)
    with pytest.raises(ValueError, match="finite"):
        g.extract(lam)


def test_construction_preserves_placements_through_dependent_merges():
    g = thin.EGraph()
    first = g.add(apps("f", F(0), F(1), F(2)), 3)
    middle = g.add(apps("g", F(1), F(2)), 3)
    last = g.add(apps("h", F(2)), 3)
    g.union(first, middle)
    g.union(middle, last)
    before = g.find(first)
    assert before.thinning.bits == [False, False, True]
    lifted = first.weaken(thin.Thin([False, True, False, True, True]))
    wrapped = g.app(g.atom("wrap", 5), lifted)
    assert g.find(first) == before
    expected = g.add(apps("wrap", apps("h", F(4))), 5)
    assert g.is_eq(wrapped, expected)
