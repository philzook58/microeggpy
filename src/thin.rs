//! A lifting e-graph: IDs place a shared class into an ordered variable context.
//! Core algorithms adapted from philzook58/lambda-microegg, without substitution.
//!
//! See NOTES.md for the original lifting commentary and blog references.
mod extract;

use indexmap::IndexMap;
use pyo3::{exceptions::PyValueError, prelude::*};
use std::collections::{HashMap, HashSet};

/// An order-preserving injection. Bits run outermost to innermost; true selects a variable.
/// Equivalently, a bitvector selects a smaller context from a larger one:
/// `[x, y, z]` with `[true, false, true]` selects `[x, z]`.
/// As a lifting, the same bits embed a function of `[x, z]` into `[x, y, z]`,
/// leaving `y` unused. Here `dom()` counts selected variables and `cod()` is
/// the ambient context length: the injection direction used in lambda-microegg.
#[pyclass(frozen, eq, hash, get_all, module = "microegg.thin")]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Thin {
    pub bits: Vec<bool>,
}

#[pymethods]
impl Thin {
    #[new]
    pub fn new(bits: Vec<bool>) -> Self {
        Self { bits }
    }
    #[staticmethod]
    pub fn identity(ctx: usize) -> Self {
        Self::new(vec![true; ctx])
    }
    #[staticmethod]
    pub fn unused(ctx: usize) -> Self {
        Self::new(vec![false; ctx])
    }
    #[staticmethod]
    pub fn select(ctx: usize, level: usize) -> PyResult<Self> {
        if level >= ctx {
            return Err(PyValueError::new_err(
                "variable level is outside its context",
            ));
        }
        let mut bits = vec![false; ctx];
        bits[level] = true;
        Ok(Self::new(bits))
    }
    pub fn dom(&self) -> usize {
        self.bits.iter().filter(|&&b| b).count()
    }
    pub fn cod(&self) -> usize {
        self.bits.len()
    }
    /// `outer.compose(inner)` places the inner context through the outer injection.
    /// If `outer : A -> Γ` and `inner : B -> A`, the result is `B -> Γ`.
    /// The inner mask selects among the variables already selected by outer.
    pub fn compose(&self, inner: &Self) -> PyResult<Self> {
        if self.dom() != inner.cod() {
            return Err(PyValueError::new_err(
                "thinning composition context mismatch",
            ));
        }
        Ok(self.comp(inner))
    }
    fn __repr__(&self) -> String {
        format!("Thin({:?})", self.bits)
    }
}

impl Thin {
    fn comp(&self, inner: &Self) -> Self {
        debug_assert_eq!(self.dom(), inner.cod());
        let mut bits = inner.bits.iter();
        Self::new(
            self.bits
                .iter()
                .map(|&keep| keep && *bits.next().unwrap())
                .collect(),
        )
    }
    // Extend the ambient context by its newest variable. Under a binder,
    // append(true) carries that bound variable along with the outer context.
    fn append(&self, keep: bool) -> Self {
        let mut bits = self.bits.clone();
        bits.push(keep);
        Self::new(bits)
    }
    /// Factor `target` through this thinning. If `self : A -> Γ` and
    /// `target : B -> Γ`, return the unique ordered thinning `B -> A`.
    /// `self.comp(result) == target`; fail if target uses a variable absent in self.
    fn factor(&self, target: &Self) -> Option<Self> {
        if self.cod() != target.cod() {
            return None;
        }
        let mut bits = vec![];
        for (&a, &b) in self.bits.iter().zip(&target.bits) {
            if b && !a {
                return None;
            }
            if a {
                bits.push(b);
            }
        }
        Some(Self::new(bits))
    }
    /// Form the union of two subcontexts of one shared ambient context.
    /// This is their coproduct in the subcontext lattice. Application needs
    /// precisely this union of the function's and argument's dependencies.
    /// Factor each input through the result to place its child in that context.
    fn join(&self, other: &Self) -> Self {
        debug_assert_eq!(self.cod(), other.cod());
        Self::new(
            self.bits
                .iter()
                .zip(&other.bits)
                .map(|(a, b)| a | b)
                .collect(),
        )
    }
    /// Pull back two thinnings into a shared ambient context: intersect their
    /// dependency subcontexts, and return the maps from that intersection into
    /// each input context. For `(common, left, right)`:
    /// `self.comp(left) == common` and `other.comp(right) == common`.
    /// Equality can retain only dependencies available on both sides.
    fn meet(&self, other: &Self) -> (Self, Self, Self) {
        debug_assert_eq!(self.cod(), other.cod());
        let common = Self::new(
            self.bits
                .iter()
                .zip(&other.bits)
                .map(|(a, b)| a & b)
                .collect(),
        );
        let left = self.factor(&common).unwrap();
        let right = other.factor(&common).unwrap();
        (common, left, right)
    }
    /// Largest subcontext of their shared domain on which the two thinnings
    /// agree, context variable by context variable. Compare the selected
    /// positions in order, rather than intersecting their ambient bitmasks.
    fn equalizer(&self, other: &Self) -> Self {
        fn positions(t: &Thin) -> impl Iterator<Item = usize> + '_ {
            t.bits
                .iter()
                .enumerate()
                .filter_map(|(i, &keep)| keep.then_some(i))
        }
        Self::new(
            positions(self)
                .zip(positions(other))
                .map(|(a, b)| a == b)
                .collect(),
        )
    }
}

/// A graph-local raw class and its placement in an ambient context.
/// This fat ID allows lifting an object into a weaker context without having
/// to reintern it. Its thinning embeds the raw class's own context into `ctx`.
#[pyclass(frozen, eq, hash, get_all, module = "microegg.thin")]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Id {
    pub raw: usize,
    pub thinning: Thin,
}

#[pymethods]
impl Id {
    #[getter]
    pub fn ctx(&self) -> usize {
        self.thinning.cod()
    }
    /// Widen an ID into a larger context with unused variables. Only its
    /// placement changes; the interned raw class stays the same.
    pub fn weaken(&self, by: &Thin) -> PyResult<Self> {
        if by.dom() != self.ctx() {
            return Err(PyValueError::new_err("weakening context mismatch"));
        }
        Ok(self.lift(by))
    }
    /// Add unused trailing variables, or remove trailing variables not used by this ID.
    pub fn in_context(&self, ctx: usize) -> PyResult<Self> {
        if self.thinning.bits.iter().skip(ctx).any(|&b| b) {
            return Err(PyValueError::new_err(
                "cannot discard a used context variable; find the ID after rebuilding first",
            ));
        }
        let mut bits = self.thinning.bits.clone();
        bits.resize(ctx, false);
        Ok(Self {
            raw: self.raw,
            thinning: Thin::new(bits),
        })
    }
    fn __repr__(&self) -> String {
        format!("Id({}, {:?})", self.raw, self.thinning.bits)
    }
}
impl Id {
    fn new(raw: usize, thinning: Thin) -> Self {
        Self { raw, thinning }
    }
    fn lift(&self, by: &Thin) -> Self {
        Self::new(self.raw, by.comp(&self.thinning))
    }
}

// One syntax type serves concrete terms and patterns. Boxing stays inside Rust;
// only the small constructors below adapt recursive children for PyO3.
// A de Bruijn index counts outward from the nearest binder; a level names a
// variable coming down from the ambient context.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Kind {
    Atom(String),
    FVar(usize),
    BVar(usize),
    App(Box<Term>, Box<Term>),
    Binder(String, Box<Term>),
    Meta(String, Vec<usize>),
}

#[pyclass(frozen, eq, hash, module = "microegg.thin")]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Term {
    kind: Kind,
}

#[pymethods]
impl Term {
    #[staticmethod]
    pub fn atom(name: String) -> Self {
        Self {
            kind: Kind::Atom(name),
        }
    }
    #[staticmethod]
    pub fn fvar(level: usize) -> Self {
        Self {
            kind: Kind::FVar(level),
        }
    }
    #[staticmethod]
    pub fn bvar(index: usize) -> Self {
        Self {
            kind: Kind::BVar(index),
        }
    }
    #[staticmethod]
    pub fn app(function: Self, argument: Self) -> Self {
        Self {
            kind: Kind::App(Box::new(function), Box::new(argument)),
        }
    }
    #[staticmethod]
    pub fn binder(op: String, body: Self) -> Self {
        Self {
            kind: Kind::Binder(op, Box::new(body)),
        }
    }
    #[staticmethod]
    #[pyo3(signature = (name, parameters = vec![]))]
    pub fn meta(name: String, parameters: Vec<usize>) -> Self {
        Self {
            kind: Kind::Meta(name, parameters),
        }
    }
    fn __repr__(&self) -> String {
        format!("{:?}", self.kind)
    }
}

impl Term {
    fn validate(
        &self,
        depth: usize,
        vars: &mut HashMap<String, usize>,
        concrete: bool,
    ) -> PyResult<()> {
        match &self.kind {
            Kind::Meta(name, args) => {
                if concrete {
                    return Err(PyValueError::new_err(
                        "concrete terms cannot contain metavariables",
                    ));
                }
                if args.iter().any(|&i| i >= depth) {
                    return Err(PyValueError::new_err(
                        "Miller parameter is outside the pattern binders",
                    ));
                }
                if !args.windows(2).all(|w| w[0] > w[1]) {
                    return Err(PyValueError::new_err(
                        "Miller parameters must be distinct and ordered outermost to innermost (decreasing indices)",
                    ));
                }
                if vars
                    .insert(name.clone(), args.len())
                    .is_some_and(|n| n != args.len())
                {
                    return Err(PyValueError::new_err("metavariable has inconsistent arity"));
                }
            }
            Kind::BVar(i) if *i >= depth => {
                return Err(PyValueError::new_err(
                    "bound variable is outside its binders",
                ));
            }
            Kind::App(f, x) => {
                f.validate(depth, vars, concrete)?;
                x.validate(depth, vars, concrete)?;
            }
            Kind::Binder(_, body) => body.validate(depth + 1, vars, concrete)?,
            _ => {}
        }
        Ok(())
    }
    fn required_context(&self) -> usize {
        match &self.kind {
            Kind::FVar(i) => i.saturating_add(1),
            Kind::App(f, x) => f.required_context().max(x.required_context()),
            Kind::Binder(_, body) => body.required_context(),
            _ => 0,
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Node {
    Var,
    Atom(String),
    App(Id, Id),
    Binder(String, Id),
}
type Subst = HashMap<String, Id>;

/// Find every W for which W.compose(edge) == target. A redundant edge may
/// admit several W, corresponding to different variables in the target.
/// Unlike `factor`, which fixes the outer injection, this fixes the inner one:
/// edge=[true,false], target=[true,false,false] admits W=[true,true,false]
/// and W=[true,false,true]. Both compose with edge to give target.
/// E-matching needs all these placements when traversing redundant edges.
fn factors(target: &Thin, edge: &Thin) -> Vec<Thin> {
    fn visit(
        target: &Thin,
        edge: &Thin,
        index: usize,
        start: usize,
        bits: &mut Vec<bool>,
        out: &mut Vec<Thin>,
    ) {
        if index == edge.cod() {
            let by = Thin::new(bits.clone());
            if by.comp(edge) == *target {
                out.push(by);
            }
            return;
        }
        let remaining = edge.cod() - index - 1;
        for i in start..target.cod().saturating_sub(remaining) {
            if target.bits[i] == edge.bits[index] {
                bits[i] = true;
                visit(target, edge, index + 1, i + 1, bits, out);
                bits[i] = false;
            }
        }
    }
    if target.dom() != edge.dom() || target.cod() < edge.cod() {
        return vec![];
    }
    if edge.bits.iter().all(|&b| b) {
        return vec![target.clone()];
    }
    let mut out = vec![];
    visit(target, edge, 0, 0, &mut vec![false; target.cod()], &mut out);
    out
}

#[pyclass(module = "microegg.thin")]
#[derive(Default)]
pub struct EGraph {
    parent: Vec<Id>,
    memo: IndexMap<Node, usize>,
    // Rebuilt index: root class -> enodes and placements of that class in each enode.
    rev: IndexMap<usize, Vec<(Node, Thin)>>,
    rules: Vec<(Term, Term)>,
}

impl EGraph {
    fn check(&self, id: &Id) -> PyResult<()> {
        if self
            .parent
            .get(id.raw)
            .is_none_or(|origin| origin.ctx() != id.thinning.dom())
        {
            return Err(PyValueError::new_err("invalid graph-local scoped ID"));
        }
        Ok(())
    }
    fn make_set(&mut self, ctx: usize) -> Id {
        let id = Id::new(self.parent.len(), Thin::identity(ctx));
        self.parent.push(id.clone());
        id
    }
    fn origin(&self, raw: usize) -> Id {
        Id::new(raw, Thin::identity(self.parent[raw].ctx()))
    }
    fn root(&self, id: &Id) -> Id {
        let mut out = id.clone();
        while self.parent[out.raw].raw != out.raw {
            let edge = &self.parent[out.raw];
            out = edge.lift(&out.thinning);
        }
        out
    }
    // Shorten union-find paths while composing their context annotations.
    // Read-only matching uses root(); construction keeps its paths short here.
    fn root_mut(&mut self, id: &Id) -> Id {
        let mut raw = id.raw;
        loop {
            let parent = self.parent[raw].raw;
            if self.parent[parent].raw == parent {
                break;
            }
            let edge = self.parent[raw].clone();
            self.parent[raw] = self.parent[parent].lift(&edge.thinning);
            raw = parent;
        }
        self.root(id)
    }
    fn intern(&mut self, ctx: usize, node: Node) -> Id {
        if let Some(&raw) = self.memo.get(&node) {
            return self.root_mut(&self.origin(raw));
        }
        let id = self.make_set(ctx);
        self.memo.insert(node, id.raw);
        id
    }
    fn variable(&mut self, ctx: usize, level: usize) -> Id {
        self.intern(1, Node::Var)
            .lift(&Thin::select(ctx, level).unwrap())
    }
    fn literal(&mut self, name: &str, ctx: usize) -> Id {
        self.intern(0, Node::Atom(name.into()))
            .lift(&Thin::unused(ctx))
    }
    /// Return the pulled e-node and the thinning back to its original context.
    /// Intern only the dependencies used by its children; the returned
    /// placement restores unused variables in the caller's ambient context.
    fn canonicalize(&mut self, node: &Node) -> (Thin, Node) {
        match node {
            Node::Var => (Thin::identity(1), Node::Var),
            Node::Atom(name) => (Thin::identity(0), Node::Atom(name.clone())),
            Node::App(f, x) => {
                let (f, x) = (self.root_mut(f), self.root_mut(x));
                let common = f.thinning.join(&x.thinning);
                let f = Id::new(f.raw, common.factor(&f.thinning).unwrap());
                let x = Id::new(x.raw, common.factor(&x.thinning).unwrap());
                (common, Node::App(f, x))
            }
            Node::Binder(op, body) => {
                let body = self.root_mut(body);
                let outer = Thin::new(body.thinning.bits[..body.ctx() - 1].to_vec());
                let inner = Thin::identity(outer.dom()).append(*body.thinning.bits.last().unwrap());
                (outer, Node::Binder(op.clone(), Id::new(body.raw, inner)))
            }
        }
    }
    fn application(&mut self, f: Id, x: Id) -> Id {
        let (by, node) = self.canonicalize(&Node::App(f, x));
        self.intern(by.dom(), node).lift(&by)
    }
    fn binding(&mut self, op: &str, body: Id) -> Id {
        let (by, node) = self.canonicalize(&Node::Binder(op.into(), body));
        self.intern(by.dom(), node).lift(&by)
    }
    fn merge(&mut self, a: &Id, b: &Id) -> bool {
        debug_assert_eq!(a.ctx(), b.ctx());
        let (a, b) = (self.root_mut(a), self.root_mut(b));
        if a == b {
            return false;
        }
        if a.raw == b.raw {
            // Equating two placements of one class restricts that class to
            // the context variables on which the placements agree. For example,
            // f(x) = f(y) turns the result of f into a context-independent
            // value rather than treating x and y themselves as equal.
            let dependency = a.thinning.equalizer(&b.thinning);
            let root = self.make_set(dependency.dom());
            self.parent[a.raw] = Id::new(root.raw, dependency);
        } else {
            let (common, left, right) = a.thinning.meet(&b.thinning);
            if common == b.thinning {
                self.parent[a.raw] = Id::new(b.raw, left);
            } else if common == a.thinning {
                self.parent[b.raw] = Id::new(a.raw, right);
            } else {
                let root = self.make_set(common.dom());
                self.parent[a.raw] = Id::new(root.raw, left);
                self.parent[b.raw] = Id::new(root.raw, right);
            }
        }
        true
    }
    fn nodes_in_class(&self, target: &Id) -> Vec<(&Node, Thin)> {
        let target = self.root(target);
        self.rev
            .get(&target.raw)
            .into_iter()
            .flatten()
            .flat_map(|(node, edge)| {
                factors(&target.thinning, edge)
                    .into_iter()
                    .map(move |by| (node, by))
            })
            .collect()
    }
    // `ambient_ctx` counts variables outside the pattern; `current_ctx` also
    // includes its local binders. Captures retain the ambient context implicitly
    // and only the local binders selected by their Miller parameters.
    // https://www.philipzucker.com/ho_unify/
    fn occurrence(ambient_ctx: usize, current_ctx: usize, args: &[usize]) -> Thin {
        let mut bits = vec![false; current_ctx];
        bits[..ambient_ctx].fill(true);
        for &index in args {
            bits[current_ctx - 1 - index] = true;
        }
        Thin::new(bits)
    }
    fn matches(&self, pattern: &Term, target: &Id, subst: Subst, ambient_ctx: usize) -> Vec<Subst> {
        if let Kind::Meta(name, args) = &pattern.kind {
            let occurrence = Self::occurrence(ambient_ctx, target.ctx(), args);
            let target = self.root(target);
            let mut subst = subst;
            if let Some(old) = subst.get(name) {
                if self.root(&old.lift(&occurrence)) != target {
                    return vec![];
                }
            } else {
                let Some(by) = occurrence.factor(&target.thinning) else {
                    return vec![];
                };
                subst.insert(name.clone(), Id::new(target.raw, by));
            }
            return vec![subst];
        }
        let mut out = vec![];
        for (node, by) in self.nodes_in_class(target) {
            match (&pattern.kind, node) {
                (Kind::Atom(a), Node::Atom(b)) if a == b => out.push(subst.clone()),
                (Kind::FVar(i), Node::Var) if by == Thin::select(target.ctx(), *i).unwrap() => {
                    out.push(subst.clone())
                }
                (Kind::BVar(i), Node::Var)
                    if by == Thin::select(target.ctx(), target.ctx() - 1 - i).unwrap() =>
                {
                    out.push(subst.clone())
                }
                (Kind::App(pf, px), Node::App(f, x)) => {
                    for s in self.matches(pf, &f.lift(&by), subst.clone(), ambient_ctx) {
                        out.extend(self.matches(px, &x.lift(&by), s, ambient_ctx));
                    }
                }
                (Kind::Binder(a, p), Node::Binder(b, body)) if a == b => {
                    out.extend(self.matches(
                        p,
                        &body.lift(&by.append(true)),
                        subst.clone(),
                        ambient_ctx,
                    ));
                }
                _ => {}
            }
        }
        out
    }
    fn instantiate(
        &mut self,
        term: &Term,
        current_ctx: usize,
        ambient_ctx: usize,
        subst: &Subst,
    ) -> Id {
        match &term.kind {
            Kind::Meta(name, args) => {
                self.root(&subst[name].lift(&Self::occurrence(ambient_ctx, current_ctx, args)))
            }
            Kind::Atom(name) => self.literal(name, current_ctx),
            Kind::FVar(i) => self.variable(current_ctx, *i),
            Kind::BVar(i) => self.variable(current_ctx, current_ctx - 1 - i),
            Kind::App(f, x) => {
                let f = self.instantiate(f, current_ctx, ambient_ctx, subst);
                let x = self.instantiate(x, current_ctx, ambient_ctx, subst);
                self.application(f, x)
            }
            Kind::Binder(op, body) => {
                let body = self.instantiate(body, current_ctx + 1, ambient_ctx, subst);
                self.binding(op, body)
            }
        }
    }
}

#[pymethods]
impl EGraph {
    #[new]
    pub fn new() -> Self {
        Self::default()
    }
    pub fn var(&mut self, ctx: usize, level: usize) -> PyResult<Id> {
        Thin::select(ctx, level)?;
        Ok(self.variable(ctx, level))
    }
    #[pyo3(signature = (name, ctx = 0))]
    pub fn atom(&mut self, name: &str, ctx: usize) -> Id {
        self.literal(name, ctx)
    }
    pub fn app(&mut self, function: &Id, argument: &Id) -> PyResult<Id> {
        self.check(function)?;
        self.check(argument)?;
        if function.ctx() != argument.ctx() {
            return Err(PyValueError::new_err(
                "application requires a shared context",
            ));
        }
        Ok(self.application(function.clone(), argument.clone()))
    }
    pub fn binder(&mut self, op: &str, body: &Id) -> PyResult<Id> {
        self.check(body)?;
        if body.ctx() == 0 {
            return Err(PyValueError::new_err(
                "binder body needs at least one context variable",
            ));
        }
        Ok(self.binding(op, body.clone()))
    }
    #[pyo3(signature = (term, ctx = 0))]
    pub fn add(&mut self, term: &Term, ctx: usize) -> PyResult<Id> {
        term.validate(0, &mut HashMap::new(), true)?;
        if term.required_context() > ctx {
            return Err(PyValueError::new_err(
                "free variable is outside the ambient context",
            ));
        }
        Ok(self.instantiate(term, ctx, ctx, &Subst::new()))
    }
    pub fn find(&self, id: &Id) -> PyResult<Id> {
        self.check(id)?;
        Ok(self.root(id))
    }
    pub fn union(&mut self, a: &Id, b: &Id) -> PyResult<bool> {
        self.check(a)?;
        self.check(b)?;
        if a.ctx() != b.ctx() {
            return Err(PyValueError::new_err("equality requires a shared context"));
        }
        Ok(self.merge(a, b))
    }
    pub fn is_eq(&mut self, a: &Id, b: &Id) -> PyResult<bool> {
        self.check(a)?;
        self.check(b)?;
        self.rebuild();
        Ok(self.root(a) == self.root(b))
    }
    pub fn rebuild(&mut self) -> bool {
        let mut changed = false;
        loop {
            let mut merged = false;
            for (node, raw) in std::mem::take(&mut self.memo) {
                let old = self.origin(raw);
                let (by, canonical) = self.canonicalize(&node);
                changed |= by != Thin::identity(old.ctx()) || canonical != node;
                let base = if let Some(&existing) = self.memo.get(&canonical) {
                    self.root(&self.origin(existing))
                } else if by == Thin::identity(old.ctx()) {
                    self.memo.insert(canonical, raw);
                    old.clone()
                } else {
                    self.intern(by.dom(), canonical)
                };
                merged |= self.merge(&old, &base.lift(&by));
            }
            changed |= merged;
            if !merged {
                break;
            }
        }
        self.rev.clear();
        for (node, &raw) in &self.memo {
            let edge = self.root(&self.origin(raw));
            self.rev
                .entry(edge.raw)
                .or_default()
                .push((node.clone(), edge.thinning));
        }
        changed
    }
    pub fn ematch(&mut self, pattern: &Term, target: &Id) -> PyResult<Vec<Subst>> {
        self.check(target)?;
        pattern.validate(0, &mut HashMap::new(), false)?;
        if pattern.required_context() > target.ctx() {
            return Err(PyValueError::new_err(
                "free variable is outside the ambient context",
            ));
        }
        self.rebuild();
        Ok(self.matches(pattern, target, Subst::new(), target.ctx()))
    }
    pub fn add_rule(&mut self, lhs: Term, rhs: Term) -> PyResult<()> {
        let (mut left, mut right) = (HashMap::new(), HashMap::new());
        lhs.validate(0, &mut left, false)?;
        rhs.validate(0, &mut right, false)?;
        if right
            .iter()
            .any(|(name, arity)| left.get(name) != Some(arity))
        {
            return Err(PyValueError::new_err(
                "RHS metavariables must be bound on the LHS with the same arity",
            ));
        }
        self.rules.push((lhs, rhs));
        Ok(())
    }
    pub fn run(&mut self, limit: usize) -> usize {
        // Borrow each RHS from one rule snapshot instead of cloning it per match.
        let rules = self.rules.clone();
        self.rebuild();
        for round in 0..limit {
            let mut targets = HashSet::new();
            for &raw in self.memo.values() {
                targets.insert(self.root(&self.origin(raw)));
            }
            let mut targets: Vec<_> = targets.into_iter().collect();
            targets.sort_by(|a, b| (a.raw, &a.thinning.bits).cmp(&(b.raw, &b.thinning.bits)));
            let mut matches = vec![];
            for (lhs, rhs) in &rules {
                for target in &targets {
                    if lhs.required_context().max(rhs.required_context()) <= target.ctx() {
                        for subst in self.matches(lhs, target, Subst::new(), target.ctx()) {
                            matches.push((target.clone(), rhs, subst));
                        }
                    }
                }
            }
            let mut changed = false;
            for (target, rhs, subst) in matches {
                let replacement = self.instantiate(rhs, target.ctx(), target.ctx(), &subst);
                changed |= self.merge(&target, &replacement);
            }
            changed |= self.rebuild();
            if !changed {
                return round + 1;
            }
        }
        limit
    }
    /// Extract a least node-count finite term, preserving the requested scope.
    pub fn extract(&mut self, target: &Id) -> PyResult<(usize, Term)> {
        self.check(target)?;
        self.rebuild();
        extract::extract(self, target)
    }
    pub fn num_classes(&self) -> usize {
        self.parent
            .iter()
            .enumerate()
            .filter(|(i, p)| *i == p.raw)
            .count()
    }
    pub fn node_count(&self) -> usize {
        self.memo.len()
    }
}

#[pymodule(name = "thin", submodule)]
pub mod python {
    #[pymodule_export]
    use super::{EGraph, Id, Term, Thin};
}

#[cfg(test)]
mod tests {
    use super::*;

    fn thins(n: usize) -> Vec<Thin> {
        (0..1usize << n)
            .map(|mask| Thin::new((0..n).map(|i| mask & (1 << i) != 0).collect()))
            .collect()
    }

    #[test]
    fn exhaustive_small_thinning_laws() {
        for n in 0..=5 {
            for a in thins(n) {
                assert_eq!(Thin::identity(n).comp(&a), a);
                assert_eq!(a.comp(&Thin::identity(a.dom())), a);
                for b in thins(n) {
                    let (common, left, right) = a.meet(&b);
                    assert_eq!(a.comp(&left), common);
                    assert_eq!(b.comp(&right), common);
                    let joined = a.join(&b);
                    assert_eq!(joined.comp(&joined.factor(&a).unwrap()), a);
                    assert_eq!(joined.comp(&joined.factor(&b).unwrap()), b);
                    if a.dom() == b.dom() {
                        let equal = a.equalizer(&b);
                        assert_eq!(a.comp(&equal), b.comp(&equal));
                    }
                }
                for b in thins(a.dom()) {
                    for c in thins(b.dom()) {
                        assert_eq!(a.comp(&b).comp(&c), a.comp(&b.comp(&c)));
                    }
                }
            }
        }
    }

    #[test]
    fn factor_enumeration_is_complete() {
        for n in 0..=5 {
            for m in 0..=n {
                for target in thins(n) {
                    for edge in thins(m) {
                        let actual: HashSet<_> = factors(&target, &edge).into_iter().collect();
                        let expected: HashSet<_> = thins(n)
                            .into_iter()
                            .filter(|by| by.dom() == m && by.comp(&edge) == target)
                            .collect();
                        assert_eq!(actual, expected);
                    }
                }
            }
        }
    }

    #[test]
    fn construction_handles_long_union_paths_without_recursion() {
        let mut g = EGraph::new();
        let first = g.atom("first", 0);
        let mut last = first.clone();
        for i in 0..10_000 {
            let next = g.atom(&format!("a{i}"), 0);
            g.union(&last, &next).unwrap();
            last = next;
        }
        let f = g.atom("f", 0);
        let old = g.app(&f, &first).unwrap();
        let canonical = g.app(&f, &last).unwrap();
        assert_eq!(old, canonical);
    }

    #[test]
    fn union_shrinks_dependencies_and_rebuilds_binders() {
        let mut g = EGraph::new();
        let (x, y) = (g.var(2, 0).unwrap(), g.var(2, 1).unwrap());
        let f = g.atom("f", 2);
        let (fx, fy) = (g.app(&f, &x).unwrap(), g.app(&f, &y).unwrap());
        let (lx, ly) = (g.binder("sum", &fx).unwrap(), g.binder("sum", &fy).unwrap());
        assert_eq!(fx.raw, fy.raw);
        g.union(&fx, &fy).unwrap();
        assert!(g.rebuild());
        assert!(!g.rebuild());
        assert_eq!(g.find(&fx).unwrap().thinning, Thin::unused(2));
        assert!(g.is_eq(&lx, &ly).unwrap());
    }
}
