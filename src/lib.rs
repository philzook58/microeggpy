use pyo3::prelude::*;
#[pymodule]
mod microegg {
    use pyo3::prelude::*;
    use std::collections::HashMap;
    use std::fmt::Display;
    pub type Id = usize;
    type Name = String;
    #[pyclass(unsendable)]
    #[derive(PartialEq, Eq, Hash, Clone, Debug)]
    pub struct Node {
        f: Name,
        args: Vec<Id>,
    }

    #[pyclass(unsendable)]
    #[derive(Default)]
    pub struct EGraph {
        memo: HashMap<Node, Id>,
        uf: Vec<Id>,
        rules: Vec<(Term, Term)>,
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
            self.memo
                .iter()
                .filter(move |(_, id)| self.is_eq(**id, class))
                .map(|(node, _)| node)
        }
        pub fn add_term(&mut self, term: &Term, subst: &Subst) -> Id {
            match term {
                Term::Var(name) => subst[name],
                Term::App(f, args) => {
                    let arg_ids = args.iter().map(|arg| self.add_term(arg, subst)).collect();
                    self.add(f, arg_ids)
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
                self.memo.insert(node, new_id);
                new_id
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

        pub fn rebuild(&mut self) {
            // copy needed for borrowing
            let nodes_copy = self.memo.clone();

            let mut keep_going = true;
            while keep_going {
                keep_going = false;
                for (node, id) in &nodes_copy {
                    let new_node = self.canonicalize_node(node);
                    let new_id = self.add_node(new_node);
                    if !self.is_eq(new_id, *id) {
                        self.union(new_id, *id);
                        keep_going = true;
                    }
                }
            }
        }

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

        pub fn apply_rules(&mut self, eclass: Id) {
            // Copy rules so we can mutate the e-graph while iterating matches.
            let rules = self.rules.clone();
            for (lhs, rhs) in &rules {
                let matches = self.ematch(lhs, eclass);
                for subst in matches {
                    let new_id = self.add_term(rhs, &subst);
                    self.union(eclass, new_id);
                }
            }
        }

        pub fn run(&mut self, n: usize) {
            for i in 0..n {
                for eclass in 1..self.uf.len() {
                    self.apply_rules(eclass);
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
    #[pymethods]
    impl PyEGraph {
        #[new]
        pub fn new() -> Self {
            Self::default()
        }

        pub fn add(&mut self, f: String, args: Vec<Id>) -> Id {
            self.inner.add(f, args)
        }

        pub fn union(&mut self, a: Id, b: Id) {
            self.inner.union(a, b);
        }

        pub fn find(&self, a: Id) -> Id {
            self.inner.find(a)
        }

        pub fn is_eq(&self, a: Id, b: Id) -> bool {
            self.inner.is_eq(a, b)
        }

        pub fn rebuild(&mut self) {
            self.inner.rebuild();
        }

        pub fn __repr__(&self) -> String {
            format!("EGraph with {} nodes", self.inner.nodes.len())
        }

        pub fn ematch(&self, pat: PyTerm, class: Id) -> Vec<HashMap<String, Id>> {
            let pat: Pattern = pat.into();
            self.inner
                .ematch(&pat, class)
                .into_iter()
                .map(|subst| {
                    subst
                        .into_iter()
                        .map(|(name, id)| (name.to_string(), id))
                        .collect::<HashMap<String, Id>>()
                })
                .collect()
        }

        pub fn to_list(&self) -> Vec<((String, Vec<Id>), Id)> {
            self.inner
                .nodes
                .iter()
                .map(|(node, id)| ((node.f.to_string(), node.args.clone()), *id))
                .collect()
        }
    }
*/

/*
    Next steps:
    Maybe rebuild should just return a new egraph anyhow
    Aegraph?
    extraction
    iteration or dictionary serialization
    If I inlined there'd be less duplication


*/
