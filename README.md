# kdrag-egraph / microegg

Small e-graphs in the style of [Max Willsey's microegg](https://github.com/mwillsey/microegg).
Install the Python distribution `kdrag-egraph`; import it as `microegg`.
Python 3.8 through 3.14 are supported by the current PyO3 version.
PyO3 exposes the Rust implementations directly, and maturin builds the package.

There are two concrete implementations: ordinary `microegg.EGraph` and
`microegg.thin.EGraph` for scoped terms. They have separate representations;
there is no common extension framework. The scoped algorithms come from
[lambda-microegg](https://github.com/philzook58/lambda-microegg), with boolean-vector
thinnings and ordered Miller rewriting. Refinement relations, substitution,
parameter permutations, and a scoped text language are outside this version.

## Ordinary terms

```python
from microegg import EGraph, Term

g = EGraph()
a = Term.App("a", [])
x = Term.Var("x")                       # a pattern metavariable
start = g.add_term(Term.App("f", [a]))
g.add_rule(Term.App("f", [x]), x)
g.run(5)                                # at most five rounds
assert g.extract(start) == (1, a)
```

`add(name, child_ids)` and `add_node(Node(name, child_ids))` build nodes directly.
`find(id)` returns the current union-find representative. `union(a, b)` asserts
an equality. `rebuild()` closes congruence and returns whether it changed the
graph. `is_eq`, `ematch`, and `extract` rebuild before querying; `find` only follows
existing union-find links. `ematch(pattern, id)` returns dictionaries of captures.
`run(limit)` searches all rules before applying a round's matches and stops when
stable, returning the number of rounds performed. `extract(id)` returns
`(node_count, term)` for a smallest finite representative. Graph-local IDs must
only be used with the graph that created them.

## Scoped terms and patterns

```python
from microegg import thin

T = thin.Term
g = thin.EGraph()
identity = T.binder("lam", T.bvar(0))
term = g.add(identity)
assert g.extract(term) == (2, identity)
assert g.ematch(T.binder("lam", T.meta("body", [0])), term)
assert not g.ematch(T.binder("lam", T.meta("closed")), term)
```

The constructors are `atom(name)`, `fvar(level)`, `bvar(index)`,
`app(function, argument)`, `binder(operator, body)`, and
`meta(name, parameters=[])`. Application is binary and curried; for `f(a,b)` write
`T.app(T.app(T.atom("f"), a), b)`. Every binder introduces one variable;
`lam`, `sum`, and `forall` are ordinary operator names. Alpha equivalence is
structural because bound variables have indices rather than names.

- `fvar(i)` selects level `i` in the ambient context passed to `g.add(term, ctx)`.
  Levels count from zero, outermost first, and retain their meaning under binders.
- `bvar(0)` selects the nearest enclosing syntax binder, `bvar(1)` the next, etc.
- `meta("m")` may depend on the entire ambient context, but on none of the
  binders introduced inside its pattern.
- `meta("m", [1, 0])` additionally permits the next and nearest pattern binders.
  Parameters must be distinct bound-variable indices in decreasing order
  (outermost to innermost). Both sides of a rule use this restriction. A repeated
  metavariable must have the same arity, and each RHS metavariable must occur on
  the LHS. Arbitrary term arguments and permutations are rejected.

Metavariables belong to patterns only: `add` rejects them. `add_rule` validates
both sides before storing a rule; malformed patterns passed to `ematch` also
raise an error. Rules mentioning free-variable levels run only in contexts large
enough for both sides. A capture dictionary stores each metavariable in
`ambient context + its ordered formal parameters`.

### Sum factorization

```python
from microegg import thin
T = thin.Term

def mul(a, b):
    return T.app(T.app(T.atom("mul"), a), b)

g = thin.EGraph()
a, body = T.meta("a"), T.meta("body", [0])
g.add_rule(T.binder("sum", mul(a, body)),
           mul(a, T.binder("sum", body)))
start = g.add(T.binder("sum", mul(T.atom("constant"), T.bvar(0))))
g.run(5)
expected = g.add(mul(T.atom("constant"), T.binder("sum", T.bvar(0))))
assert g.is_eq(start, expected)
```

The first capture cannot depend on the summation variable. Consequently the
rule does not match `sum i. mul(i, constant)`.

### Thinnings and low-level construction

`Thin([True, False, True])` embeds two variables in a three-variable context.
`dom()` counts selected variables; `cod()` is the ambient context length.
`outer.compose(inner)` composes injections. `identity(n)`, `unused(n)`, and
`select(n, level)` construct common thinnings. There is no machine-word limit.

Scoped `Id` values are immutable and expose `raw`, `thinning`, and `ctx`.
`id.weaken(thin)` embeds an ID in a larger context without reinterning it.
`id.in_context(n)` adds unused trailing variables or removes unused trailing
ones. Low-level graph constructors are `var(ctx, level)`, `atom(name, ctx=0)`,
`app(function_id, argument_id)`, and `binder(operator, body_id)`; the bound
variable is the body's final context variable.

Equating different placements of one class can remove dependencies, rather
than equating the variables themselves. Rebuild after unions, then use
`g.find(id)` to obtain the smaller dependency mask before shrinking its context.
As with ordinary graphs, all IDs are local to their creating graph. `extract`
raises `ValueError` if no finite representative exists in the requested context.
Its node-count cost counts variables, atoms, application nodes, and binders.

## Development and migration

```sh
uv sync
uv run maturin develop
uv run pytest -q
cargo test
```

For wheel verification, use `uv run maturin build`, install the wheel in a fresh
environment, and run the Python tests there. Maturin enables the extension-module
linking feature for Python builds; ordinary Cargo tests link Python normally.

API changes in this revision:

- The ordinary Rust and Python APIs now use the same implementation.
- `add_term` replaces `add_term0`. Rules are registered with `add_rule(lhs, rhs)`
  and run with `run(limit)` in both APIs; register two rules for both directions.
- Recursive insertion-time rewriting, `apply_rules`, `compact`, storage-field
  access, and their compatibility aliases are removed. Use `num_classes()` and
  `node_count()` for counts. Class numbers and match multiplicities are not
  stable across rebuilding.
- The unfinished Rust thinning API is replaced by the scoped API above. The
  unrelated co-egraph, partial-thinning, Prolog, and s-expression experiments
  remain in their source files and are not exposed as Python APIs.
