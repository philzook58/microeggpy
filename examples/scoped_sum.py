"""Factor a constant out of a generic summation binder."""
from microegg import thin

T = thin.Term


def mul(a, b):
    return T.app(T.app(T.atom("mul"), a), b)


g = thin.EGraph()
a, body = T.meta("a"), T.meta("body", [0])
g.add_rule(T.binder("sum", mul(a, body)), mul(a, T.binder("sum", body)))
term = g.add(T.binder("sum", mul(T.atom("constant"), T.bvar(0))))
g.run(5)
goal = g.add(mul(T.atom("constant"), T.binder("sum", T.bvar(0))))
assert g.is_eq(term, goal)
print(g.extract(term))
