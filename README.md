# kdrag-egraph / microegg

Small e-graphs in the style of [Max Willsey’s microegg](https://github.com/mwillsey/microegg),
with Rust implementations exposed directly to Python through PyO3 and maturin.
`microegg.EGraph` handles ordinary terms; `microegg.thin.EGraph` adds scoped
rewriting with thinnings and ordered Miller captures.

```sh
pip install kdrag-egraph
```

```python
from microegg import EGraph, Term

g = EGraph()
a, x = Term.App("a", []), Term.Var("x")
start = g.add_term(Term.App("f", [a]))
g.add_rule(Term.App("f", [x]), x)
g.run(5)
assert g.extract(start) == (1, a)
```

See [notes](NOTES.md) for scoped usage, variable conventions, and historical comments.
