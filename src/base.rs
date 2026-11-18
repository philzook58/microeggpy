//! An ordinary microegg-style e-graph. Rust and Python use this same implementation.
use pyo3::{exceptions::PyValueError, prelude::*};
use std::collections::{HashMap, HashSet};

pub type Id = usize;
type Subst = HashMap<String, Id>;

#[pyclass(frozen, eq, hash, get_all, module = "microegg")]
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct Node {
    pub f: String,
    pub args: Vec<Id>,
}

#[pymethods]
impl Node {
    #[new]
    pub fn new(f: String, args: Vec<Id>) -> Self {
        Self { f, args }
    }
    fn __repr__(&self) -> String {
        format!("{self:?}")
    }
}

/// `Var` is a pattern metavariable; constants are nullary `App`s.
#[pyclass(frozen, eq, hash, module = "microegg")]
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum Term {
    Var(String),
    App(String, Vec<Term>),
}

#[pymethods]
impl Term {
    fn __repr__(&self) -> String {
        format!("{self:?}")
    }
}

impl Term {
    fn variables(&self, out: &mut HashSet<String>) {
        match self {
            Self::Var(name) => {
                out.insert(name.clone());
            }
            Self::App(_, args) => {
                for arg in args {
                    arg.variables(out);
                }
            }
        }
    }
}

#[pyclass(module = "microegg")]
#[derive(Default, Debug)]
pub struct EGraph {
    memo: HashMap<Node, Id>,
    nodes: Vec<Node>,
    parent: Vec<Id>,
    sibling: Vec<Id>,
    rules: Vec<(Term, Term)>,
}

impl EGraph {
    fn check(&self, id: Id) -> PyResult<()> {
        if id < self.parent.len() {
            Ok(())
        } else {
            Err(PyValueError::new_err("invalid e-class ID"))
        }
    }
    fn root(&self, mut id: Id) -> Id {
        while self.parent[id] != id {
            id = self.parent[id];
        }
        id
    }
    fn merge(&mut self, a: Id, b: Id) -> bool {
        let (a, b) = (self.root(a), self.root(b));
        if a == b {
            return false;
        }
        self.parent[a] = b;
        self.sibling.swap(a, b);
        true
    }
    fn intern(&mut self, node: Node) -> Id {
        let node = Node {
            f: node.f,
            args: node.args.into_iter().map(|id| self.root(id)).collect(),
        };
        if let Some(&id) = self.memo.get(&node) {
            return self.root(id);
        }
        let id = self.parent.len();
        self.parent.push(id);
        self.sibling.push(id);
        self.nodes.push(node.clone());
        self.memo.insert(node, id);
        id
    }
    fn nodes_in_class(&self, class: Id) -> impl Iterator<Item = &Node> {
        let mut id = class;
        let mut first = true;
        std::iter::from_fn(move || {
            if !first && id == class {
                return None;
            }
            first = false;
            let node = &self.nodes[id];
            id = self.sibling[id];
            Some(node)
        })
    }
    fn matches(&self, pat: &Term, class: Id, mut subst: Subst) -> Vec<Subst> {
        let class = self.root(class);
        match pat {
            Term::Var(name) => {
                if let Some(&old) = subst.get(name) {
                    if self.root(old) != class {
                        return vec![];
                    }
                } else {
                    subst.insert(name.clone(), class);
                }
                vec![subst]
            }
            Term::App(f, args) => self
                .nodes_in_class(class)
                .filter(|node| node.f == *f && node.args.len() == args.len())
                .flat_map(|node| {
                    args.iter()
                        .zip(&node.args)
                        .fold(vec![subst.clone()], |todo, (p, &a)| {
                            todo.into_iter()
                                .flat_map(|s| self.matches(p, a, s))
                                .collect()
                        })
                })
                .collect(),
        }
    }
    fn instantiate(&mut self, term: &Term, subst: &Subst) -> Id {
        match term {
            Term::Var(name) => self.root(subst[name]),
            Term::App(f, args) => {
                let args = args.iter().map(|a| self.instantiate(a, subst)).collect();
                self.intern(Node::new(f.clone(), args))
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

    pub fn add_node(&mut self, node: Node) -> PyResult<Id> {
        for &arg in &node.args {
            self.check(arg)?;
        }
        Ok(self.intern(node))
    }
    pub fn add(&mut self, f: &str, args: Vec<Id>) -> PyResult<Id> {
        self.add_node(Node::new(f.into(), args))
    }
    pub fn add_term(&mut self, term: &Term) -> PyResult<Id> {
        let mut vars = HashSet::new();
        term.variables(&mut vars);
        if !vars.is_empty() {
            return Err(PyValueError::new_err(
                "concrete terms cannot contain metavariables",
            ));
        }
        Ok(self.instantiate(term, &Subst::new()))
    }
    pub fn find(&self, id: Id) -> PyResult<Id> {
        self.check(id)?;
        Ok(self.root(id))
    }
    pub fn union(&mut self, a: Id, b: Id) -> PyResult<bool> {
        self.check(a)?;
        self.check(b)?;
        Ok(self.merge(a, b))
    }
    pub fn is_eq(&mut self, a: Id, b: Id) -> PyResult<bool> {
        self.check(a)?;
        self.check(b)?;
        self.rebuild();
        Ok(self.root(a) == self.root(b))
    }
    pub fn rebuild(&mut self) -> bool {
        let mut changed = false;
        loop {
            let mut merged = false;
            // Re-key existing classes instead of allocating new IDs. Allocating
            // here can chase fresh representatives forever on cyclic graphs.
            for (node, id) in std::mem::take(&mut self.memo) {
                let canonical = Node::new(
                    node.f.clone(),
                    node.args.iter().map(|&a| self.root(a)).collect(),
                );
                changed |= canonical != node;
                let id = self.root(id);
                if let Some(&other) = self.memo.get(&canonical) {
                    merged |= self.merge(id, other);
                } else {
                    self.memo.insert(canonical, id);
                }
            }
            changed |= merged;
            if !merged {
                return changed;
            }
        }
    }
    pub fn ematch(&mut self, pattern: &Term, class: Id) -> PyResult<Vec<Subst>> {
        self.check(class)?;
        self.rebuild();
        Ok(self.matches(pattern, class, Subst::new()))
    }
    pub fn add_rule(&mut self, lhs: Term, rhs: Term) -> PyResult<()> {
        let (mut left, mut right) = (HashSet::new(), HashSet::new());
        lhs.variables(&mut left);
        rhs.variables(&mut right);
        if !right.is_subset(&left) {
            return Err(PyValueError::new_err("RHS uses an unbound metavariable"));
        }
        self.rules.push((lhs, rhs));
        Ok(())
    }
    /// Run at most `limit` search-then-apply rounds, stopping at a fixed point.
    pub fn run(&mut self, limit: usize) -> usize {
        let rules = self.rules.clone();
        self.rebuild();
        for round in 0..limit {
            let mut matches = vec![];
            for (lhs, rhs) in &rules {
                for class in 0..self.parent.len() {
                    if self.root(class) == class {
                        for subst in self.matches(lhs, class, Subst::new()) {
                            matches.push((class, rhs, subst));
                        }
                    }
                }
            }
            let mut changed = false;
            for (class, rhs, subst) in matches {
                let replacement = self.instantiate(rhs, &subst);
                changed |= self.merge(class, replacement);
            }
            changed |= self.rebuild();
            if !changed {
                return round + 1;
            }
        }
        limit
    }
    pub fn num_classes(&self) -> usize {
        (0..self.parent.len())
            .filter(|&id| self.root(id) == id)
            .count()
    }
    pub fn node_count(&self) -> usize {
        self.memo.len()
    }

    /// Least node-count finite representative. Relaxation handles cyclic classes.
    pub fn extract(&mut self, class: Id) -> PyResult<(usize, Term)> {
        self.check(class)?;
        self.rebuild();
        let mut best: HashMap<Id, (usize, Term)> = HashMap::new();
        loop {
            let mut changed = false;
            for (id, node) in self.nodes.iter().enumerate() {
                let children: Option<Vec<_>> = node
                    .args
                    .iter()
                    .map(|&id| best.get(&self.root(id)).cloned())
                    .collect();
                let Some(children) = children else {
                    continue;
                };
                let cost = children
                    .iter()
                    .fold(1usize, |n, (c, _)| n.saturating_add(*c));
                let root = self.root(id);
                if best.get(&root).is_none_or(|(old, _)| cost < *old) {
                    best.insert(
                        root,
                        (
                            cost,
                            Term::App(
                                node.f.clone(),
                                children.into_iter().map(|(_, t)| t).collect(),
                            ),
                        ),
                    );
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        best.remove(&self.root(class))
            .ok_or_else(|| PyValueError::new_err("class has no finite representative"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{rw, rws, term};

    #[test]
    fn congruence_and_cycles() {
        let mut g = EGraph::new();
        let a = g.add("a", vec![]).unwrap();
        let b = g.add("b", vec![]).unwrap();
        let fa = g.add("f", vec![a]).unwrap();
        let fb = g.add("f", vec![b]).unwrap();
        g.union(a, b).unwrap();
        assert!(g.is_eq(fa, fb).unwrap());
        g.union(fa, a).unwrap();
        assert_eq!(g.extract(fa).unwrap().0, 1);
    }
    #[test]
    fn mutually_recursive_classes_do_not_allocate_during_rebuild() {
        let mut g = EGraph::new();
        let a = g.add("a", vec![]).unwrap();
        let b = g.add("b", vec![]).unwrap();
        let fa = g.add("f", vec![a]).unwrap();
        let fb = g.add("f", vec![b]).unwrap();
        g.union(a, fb).unwrap();
        g.union(b, fa).unwrap();
        let allocated = g.parent.len();
        g.rebuild();
        assert_eq!(g.parent.len(), allocated);
        assert!(!g.rebuild());
        assert_eq!(g.extract(a).unwrap().0, 1);
        assert_eq!(g.extract(b).unwrap().0, 1);
    }

    #[test]
    fn macros_and_rewriting() {
        assert_eq!(rw!(f(?x) => g(?x)), (term!(f(?x)), term!(g(?x))));
        let mut g = EGraph::new();
        let input = g.add_term(&term!(f(a))).unwrap();
        let rules = rws![f(?x) => g(?x)];
        for (lhs, rhs) in rules {
            g.add_rule(lhs, rhs).unwrap();
        }
        g.run(3);
        let goal = g.add_term(&term!(g(a))).unwrap();
        assert!(g.is_eq(input, goal).unwrap());
    }
}
