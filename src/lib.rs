use pyo3::prelude::*;
pub mod base;
mod coegraph;
pub mod thin;
pub mod uf;
#[pymodule]
mod microegg {
    use pyo3::prelude::*;
    use std::collections::HashMap;
    use std::fmt::Display;
    pub type Id = usize;
    /*
    #[pyclass(eq, frozen, hash)]
    #[derive(PartialEq, Eq, Hash, Clone, Debug)]
    pub enum Id {
        EId(usize), // Function?
        Constructor(usize),
        // Int(usize),
        // String(String),
        // OffSet(usize, usize)
        // Factor(usize, usize)
        // Thin(Thin, usize)

    }

    fn add_constructor()
    fn add_function()

    */
    type Name = String;
    #[pyclass(unsendable, get_all, frozen, eq, hash)]
    #[derive(PartialEq, Eq, Hash, Clone, Debug)]
    pub struct Node {
        pub f: Name,
        pub args: Vec<Id>,
    }
    #[pymethods]
    impl Node {
        #[new]
        pub fn new(f: String, args: Vec<Id>) -> Self {
            Self { f, args }
        }
        pub fn __repr__(&self) -> String {
            let args_str = self
                .args
                .iter()
                .map(|id| id.to_string())
                .collect::<Vec<_>>()
                .join(", ");
            format!("Node({}, [{}])", self.f, args_str)
        }
    }

    #[pyclass(unsendable, get_all)]
    #[derive(Default)]
    pub struct EGraph {
        pub memo: HashMap<Node, Id>,
        pub nodes: Vec<Node>, // todo Indexmap?
        pub uf: Vec<Id>,
        pub sibling: Vec<Id>,
        pub rules: Vec<(Term, Term)>,
    }

    #[pyclass(eq, frozen, hash, unsendable, str)]
    #[derive(PartialEq, Eq, Hash, Clone, Debug)]
    pub enum Term {
        Var(Name),
        App(Name, Vec<Term>),
    }
    impl Display for Term {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Term::Var(name) => write!(f, "{}", name),
                Term::App(name, args) => {
                    write!(f, "{}(", name)?;
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", arg)?;
                    }
                    write!(f, ")")
                }
            }
        }
    }
    #[pymethods]
    impl Term {
        fn __repr__(&self) -> String {
            match self {
                Term::Var(name) => format!("Var({})", name),
                Term::App(name, args) => {
                    let args_str = args
                        .iter()
                        .map(Term::__repr__)
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("App({}, [{}])", name, args_str)
                }
            }
        }
    }
    pub type Subst = HashMap<Name, Id>;

    impl EGraph {
        pub fn nodes_in_class(&self, class: Id) -> impl Iterator<Item = &Node> {
            let mut id = class;
            let mut first = true;
            std::iter::from_fn(move || {
                if !first && id == class {
                    return None;
                }
                first = false;
                id = self.sibling[id];
                Some(&self.nodes[id])
            })
        }
        pub fn add_term(&mut self, term: &Term, subst: &Subst, depth: usize) -> Id {
            match term {
                Term::Var(name) => subst[name],
                Term::App(f, args) => {
                    let arg_ids = args
                        .iter()
                        .map(|arg| self.add_term(arg, subst, depth))
                        .collect();
                    self.add_node_rewrite(
                        Node {
                            f: f.into(),
                            args: arg_ids,
                        },
                        depth,
                    )
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
        pub fn add_node(&mut self, node: Node) -> Id {
            let node = self.canonicalize_node(&node);
            if let Some(&id) = self.memo.get(&node) {
                id
            } else {
                let new_id = self.uf.len();
                self.uf.push(new_id);
                self.sibling.push(new_id);
                self.nodes.push(node.clone());
                self.memo.insert(node, new_id);
                new_id
            }
        }

        #[pyo3(signature = (node, depth=0))]
        pub fn add_node_rewrite(&mut self, node: Node, depth: usize) -> Id {
            if depth <= 0 {
                return self.add_node(node);
            } else {
                // If we opened up ematch to one that starts on a node, we could avoid this.
                let id = self.add_node(node.clone());
                self.apply_rules(id, depth - 1);
                self.add_node(node) // micro rebuild
            }
        }

        pub fn size(&self) -> (usize, usize) {
            (self.memo.len(), self.uf.len())
        }

        pub fn add(&mut self, f: &str, args: Vec<Id>) -> Id {
            let node = Node {
                f: f.into(),
                args: args.into(),
            };
            self.add_node(node)
        }

        pub fn union(&mut self, a: Id, b: Id) {
            let a = self.find(a);
            let b = self.find(b);
            if a != b {
                self.uf[a] = b;
                // Splice together the two loops of siblings
                let a_next = self.sibling[a];
                let b_next = self.sibling[b];
                self.sibling[a] = b_next;
                self.sibling[b] = a_next;
            }
        }

        pub fn find(&self, mut a: Id) -> Id {
            while self.uf[a] != a {
                a = self.uf[a];
            }
            a
        }

        pub fn is_eq(&self, a: Id, b: Id) -> bool {
            self.find(a) == self.find(b)
        }

        pub fn canonicalize_node(&self, node: &Node) -> Node {
            Node {
                f: node.f.clone(),
                args: node.args.iter().map(|id| self.find(*id)).collect(),
            }
        }

        pub fn num_classes(&self) -> usize {
            // Could track as field in EGraph.
            (0..self.uf.len()).filter(|&id| self.find(id) == id).count()
        }

        pub fn rebuild(&mut self) {
            // copy needed for borrowing
            let nodes_copy = self.memo.clone();

            let mut keep_going = true;
            while keep_going {
                keep_going = false;
                for (node, id) in &nodes_copy {
                    let new_id = self.add_node(node.clone());
                    if !self.is_eq(new_id, *id) {
                        self.union(new_id, *id);
                        keep_going = true;
                    }
                }
            }
        }

        fn compact(&self) -> Self {
            let mut egraph = EGraph::default();
            let mut root_map = HashMap::new();
            for (id, node) in self.nodes.iter().enumerate() {
                let new_node = Node {
                    f: node.f.clone(),
                    args: node
                        .args
                        .iter()
                        .map(|id| root_map[&self.find(*id)])
                        .collect(),
                };
                let id2 = egraph.add_node(new_node);
                let id = self.find(id);
                if let Some(&existing_id) = root_map.get(&id) {
                    egraph.union(existing_id, id2);
                } else {
                    root_map.insert(id, id2);
                }
            }
            egraph
        }

        /*
        let root_map = HashMap::new();
        fn transfer(root_map : &mut HashMap<Id, Id>, egraph: &mut EGraph, id: Id) -> Id {
            if let Some(&new_id) = root_map.get(&id) {
                new_id
            } else {
                egraph.
            }
        }
        for id, node in self.nodes.iter().enumerate() {
            root_map.
            let node = Node {
                f: node.f.clone(),
                args: node.args.iter().map(|id| self.find(*id)).collect(),
            };
        }
        */

        pub fn ematch(&self, pat: &Term, class: Id) -> Vec<Subst> {
            self.ematch_rec(0, pat, class, Default::default())
        }
        pub fn ematch_rec(
            &self,
            depth: usize,
            pat: &Term,
            class: Id,
            mut subst: Subst,
        ) -> Vec<Subst> {
            match pat {
                Term::Var(name) => {
                    if let Some(&id) = subst.get(name) {
                        if self.is_eq(id, class) {
                            return vec![subst];
                        } else {
                            return vec![];
                        }
                    } else {
                        subst.insert(name.clone(), class);
                        return vec![subst];
                    }
                }
                Term::App(f, args) => {
                    let mut results = vec![];
                    for node in self.nodes_in_class(class) {
                        if node.f == *f && node.args.len() == args.len() {
                            let mut todo = vec![subst.clone()];
                            for (pa, na) in args.iter().zip(node.args.iter()) {
                                todo = todo
                                    .into_iter()
                                    .flat_map(|subst| self.ematch_rec(depth + 1, pa, *na, subst))
                                    .collect();
                            }

                            results.extend(todo);
                        }
                    }
                    results
                }
            }
        }

        pub fn to_list(&self) -> Vec<((String, Vec<Id>), Id)> {
            self.memo
                .iter()
                .map(|(node, id)| ((node.f.to_string(), node.args.clone()), *id))
                .collect()
        }

        pub fn add_rule(&mut self, lhs: Term, rhs: Term) {
            self.rules.push((lhs, rhs));
        }

        pub fn add_birule(&mut self, lhs: Term, rhs: Term) {
            self.add_rule(lhs.clone(), rhs.clone());
            self.add_rule(rhs, lhs);
        }

        #[pyo3(signature = (eclass, depth=0))]
        pub fn apply_rules(&mut self, eclass: Id, depth: usize) {
            // Copy rules so we can mutate the e-graph while iterating matches.
            let rules = self.rules.clone();
            for (lhs, rhs) in &rules {
                let matches = self.ematch(lhs, eclass);
                for subst in matches {
                    let new_id = self.add_term(rhs, &subst, depth);
                    self.union(eclass, new_id);
                }
            }
        }

        pub fn run(&mut self, n: usize) {
            for _i in 0..n {
                for eclass in 0..self.uf.len() {
                    self.apply_rules(eclass, 0);
                }
                self.rebuild();
            }
        }
        pub fn extract(&self, class: Id) -> (usize, Term) {
            fn worker(
                egraph: &EGraph,
                cost: &mut HashMap<Id, Option<(usize, Term)>>,
                class: Id,
            ) -> Option<(usize, Term)> {
                let class = egraph.find(class);
                if let Some(best) = cost.get(&class) {
                    return best.clone();
                }

                cost.insert(class, None);

                let best = egraph
                    .nodes_in_class(class)
                    .filter_map(|node| {
                        let arg_costs: Option<Vec<_>> = node
                            .args
                            .iter()
                            .map(|&arg| worker(egraph, cost, arg))
                            .collect();
                        let arg_costs = arg_costs?;
                        let total_cost = 1 + arg_costs
                            .iter()
                            .map(|(node_cost, _)| *node_cost)
                            .sum::<usize>();
                        let args = arg_costs.into_iter().map(|(_, term)| term).collect();
                        Some((total_cost, Term::App(node.f.clone(), args)))
                    })
                    .min_by_key(|(node_cost, _)| *node_cost);

                cost.insert(class, best.clone());
                best
            }

            let mut cost: HashMap<Id, Option<(usize, Term)>> = HashMap::new();
            worker(self, &mut cost, class)
                .unwrap_or_else(|| panic!("could not extract an acyclic term from class {}", class))
        }
    }
}
/*
Multi patterns?
More interesting cost

generalized uf
constructors
factor out ematch_node(f, args)
AC nodes?
smallvec / smallstrings? intern strings?
proofs as just a trace.
analysis? Extensible?
App. LFHOL
context?
backtrackable?
backtrack(id) -> splice out of siblings, remove all nodes beyond...
trail = [id, id, id]

examples:
Relational algebra.
Polynomials
bitvector

benchmarks
reduce allocations

*/
