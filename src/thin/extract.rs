//! Finite representatives with explicit scope requirements. A representative
//! may need extra variables after its class loses dependencies. Keep only
//! representatives undominated in both cost and required variables per gap.
use super::*;

#[derive(Clone)]
struct Witness {
    term: Term,
    placement: Thin,
    cost: usize,
}

fn gaps(t: &Thin) -> Vec<usize> {
    let mut out = vec![0];
    for &keep in &t.bits {
        if keep {
            out.push(0);
        } else {
            *out.last_mut().unwrap() += 1;
        }
    }
    out
}

fn dominates(a: &Witness, b: &Witness) -> bool {
    a.cost <= b.cost
        && gaps(&a.placement)
            .iter()
            .zip(gaps(&b.placement))
            .all(|(a, b)| *a <= b)
}

fn insert(table: &mut HashMap<usize, Vec<Witness>>, raw: usize, witness: Witness) -> bool {
    let old = table.entry(raw).or_default();
    if old.iter().any(|a| dominates(a, &witness)) {
        return false;
    }
    old.retain(|b| !dominates(&witness, b));
    old.push(witness);
    true
}

// Rename only ambient variables; indices belonging to syntax binders stay put.
fn rename(term: &Term, levels: &[usize]) -> Term {
    match &term.kind {
        Kind::FVar(i) => Term::fvar(levels[*i]),
        Kind::App(f, x) => Term::app(rename(f, levels), rename(x, levels)),
        Kind::Binder(op, body) => Term::binder(op.clone(), rename(body, levels)),
        _ => term.clone(),
    }
}

fn abstract_last(term: &Term, level: usize, depth: usize) -> Term {
    match &term.kind {
        Kind::FVar(i) if *i == level => Term::bvar(depth),
        Kind::App(f, x) => Term::app(
            abstract_last(f, level, depth),
            abstract_last(x, level, depth),
        ),
        Kind::Binder(op, body) => Term::binder(op.clone(), abstract_last(body, level, depth + 1)),
        _ => term.clone(),
    }
}

// Label the witness's semantic variables by their positions in the enode's
// context. Unlabelled positions are additional variables needed by its syntax.
fn labels(witness: &Thin, child: &Thin) -> Vec<Option<usize>> {
    let mut levels = child
        .bits
        .iter()
        .enumerate()
        .filter_map(|(i, &b)| b.then_some(i));
    witness
        .bits
        .iter()
        .map(|&keep| {
            if keep {
                Some(levels.next().unwrap())
            } else {
                None
            }
        })
        .collect()
}

struct Alignment {
    labels: Vec<Option<usize>>,
    left: Vec<usize>,
    right: Vec<usize>,
}

// All common ordered contexts for two representatives. Extra variables can
// coincide, including with a semantic variable belonging to the other child.
// For example, [Some(0), None] and [None, Some(1)] can share context
// [Some(0), Some(1)]: each child's extra variable uses the other's dependency.
// Keeping only the cheapest witness per class would lose these scope choices.
fn align(left: &[Option<usize>], right: &[Option<usize>]) -> Vec<Alignment> {
    fn visit(
        a: &[Option<usize>],
        b: &[Option<usize>],
        current: &mut Alignment,
        out: &mut Vec<Alignment>,
    ) {
        if a.is_empty() && b.is_empty() {
            out.push(Alignment {
                labels: current.labels.clone(),
                left: current.left.clone(),
                right: current.right.clone(),
            });
            return;
        }
        for (take_a, take_b) in [(true, false), (false, true), (true, true)] {
            if (take_a && a.is_empty()) || (take_b && b.is_empty()) {
                continue;
            }
            let x = if take_a { a[0] } else { None };
            let y = if take_b { b[0] } else { None };
            if x.is_some() && y.is_some() && x != y {
                continue;
            }
            let label = x.or(y);
            let rest_a = &a[usize::from(take_a)..];
            let rest_b = &b[usize::from(take_b)..];
            if let Some(i) = label {
                // Anchors must appear once, in their original global order.
                if rest_a.iter().chain(rest_b).flatten().any(|&j| j <= i) {
                    continue;
                }
            }
            let level = current.labels.len();
            current.labels.push(label);
            if take_a {
                current.left.push(level);
            }
            if take_b {
                current.right.push(level);
            }
            visit(rest_a, rest_b, current, out);
            current.labels.pop();
            if take_a {
                current.left.pop();
            }
            if take_b {
                current.right.pop();
            }
        }
    }
    let mut out = vec![];
    visit(
        left,
        right,
        &mut Alignment {
            labels: vec![],
            left: vec![],
            right: vec![],
        },
        &mut out,
    );
    out
}

pub(super) fn extract(g: &EGraph, target: &Id) -> PyResult<(usize, Term)> {
    let mut table: HashMap<usize, Vec<Witness>> = HashMap::new();
    loop {
        let mut changed = false;
        for (&raw, nodes) in &g.rev {
            for (node, edge) in nodes {
                let candidates = match node {
                    Node::Var => vec![Witness {
                        term: Term::fvar(0),
                        placement: edge.clone(),
                        cost: 1,
                    }],
                    Node::Atom(name) => vec![Witness {
                        term: Term::atom(name.clone()),
                        placement: edge.clone(),
                        cost: 1,
                    }],
                    Node::App(f, x) => {
                        let (f, x) = (g.root(f), g.root(x));
                        let mut out = vec![];
                        for a in table.get(&f.raw).into_iter().flatten() {
                            for b in table.get(&x.raw).into_iter().flatten() {
                                for context in align(
                                    &labels(&a.placement, &f.thinning),
                                    &labels(&b.placement, &x.thinning),
                                ) {
                                    out.push(Witness {
                                        placement: Thin::new(
                                            context
                                                .labels
                                                .iter()
                                                .map(|i| i.is_some_and(|i| edge.bits[i]))
                                                .collect(),
                                        ),
                                        term: Term::app(
                                            rename(&a.term, &context.left),
                                            rename(&b.term, &context.right),
                                        ),
                                        cost: 1usize.saturating_add(a.cost).saturating_add(b.cost),
                                    });
                                }
                            }
                        }
                        out
                    }
                    Node::Binder(op, body) => {
                        let body = g.root(body);
                        let bound = body.ctx() - 1;
                        let uses_bound = body.thinning.bits[bound];
                        let mut out = vec![];
                        for child in table.get(&body.raw).into_iter().flatten() {
                            let mut context = labels(&child.placement, &body.thinning);
                            // A used binder must be the final variable. If it is
                            // semantically unused, it can supply a trailing extra.
                            if uses_bound && context.last() != Some(&Some(bound)) {
                                continue;
                            }
                            let consumes_last = context.last() == Some(&None) || uses_bound;
                            let body_term = if consumes_last {
                                abstract_last(&child.term, context.len() - 1, 0)
                            } else {
                                child.term.clone()
                            };
                            if consumes_last {
                                context.pop();
                            }
                            out.push(Witness {
                                placement: Thin::new(
                                    context
                                        .iter()
                                        .map(|i| i.is_some_and(|i| edge.bits[i]))
                                        .collect(),
                                ),
                                term: Term::binder(op.clone(), body_term),
                                cost: child.cost.saturating_add(1),
                            });
                        }
                        out
                    }
                };
                for candidate in candidates {
                    changed |= insert(&mut table, raw, candidate);
                }
            }
        }
        // The nonnegative cost/requirement vectors form a well-quasi-order:
        // only finitely many undominated witnesses can be discovered.
        if !changed {
            break;
        }
    }
    let target = g.root(target);
    let available = gaps(&target.thinning);
    let best = table
        .get(&target.raw)
        .into_iter()
        .flatten()
        .filter(|w| {
            gaps(&w.placement)
                .iter()
                .zip(&available)
                .all(|(need, have)| need <= have)
        })
        .min_by_key(|w| w.cost)
        .ok_or_else(|| {
            PyValueError::new_err("class has no finite representative in this context")
        })?;
    let mut index = 0;
    let mut levels = vec![];
    for (level, &used) in target.thinning.bits.iter().enumerate() {
        if used || best.placement.bits.get(index) == Some(&false) {
            levels.push(level);
            index += 1;
        }
    }
    debug_assert_eq!(index, best.placement.cod());
    Ok((best.cost, rename(&best.term, &levels)))
}
