// Largely pulled from: https://github.com/mwillsey/microegg/blob/main/src/lib.rs
use std::collections::HashMap;
pub type Id = usize;

type Name = String;
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum Node {
    App { f: Name, args: Vec<Id> },
}

#[derive(Default, Debug)]
pub struct EGraph {
    pub memo: HashMap<Node, Id>,
    pub nodes: Vec<Node>, // todo Indexmap?
    pub uf: Vec<Id>,
    pub sibling: Vec<Id>,
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum Term {
    Var(Name),
    App(Name, Vec<Term>),
    // EId
}

type Subst = HashMap<Name, Id>;

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
    pub fn add_term(&mut self, term: &Term, subst: &Subst) -> Id {
        match term {
            Term::Var(name) => subst[name],
            Term::App(f, args) => {
                let args = args.iter().map(|arg| self.add_term(arg, subst)).collect();
                self.add_node(Node::App { f: f.into(), args })
            }
        }
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

    pub fn app(&mut self, f: &str, args: Vec<Id>) -> Id {
        let node = Node::App {
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
        match node {
            Node::App { f, args } => Node::App {
                f: f.clone(),
                args: args.iter().map(|id| self.find(*id)).collect(),
            },
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

    pub fn compact(&self) -> Self {
        let mut egraph = EGraph::default();
        let mut root_map = HashMap::new();
        for (id, node) in self.nodes.iter().enumerate() {
            let new_node = match node {
                Node::App { f, args } => Node::App {
                    f: f.clone(),
                    args: args.iter().map(|id| root_map[&self.find(*id)]).collect(),
                },
            };
            let id2 = egraph.add_node(new_node);
            let id = self.find(id);
            if let Some(&existing_id) = root_map.get(&id) {
                egraph.union(id2, existing_id); // order matters?
            } else {
                root_map.insert(id, id2);
            }
        }
        egraph
    }

    pub fn ematch(&self, pat: &Term, class: Id) -> Vec<Subst> {
        self.ematch_rec(pat, class, Default::default())
    }
    pub fn ematch_rec(&self, pat: &Term, class: Id, mut subst: Subst) -> Vec<Subst> {
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
            Term::App(pf, pargs) => {
                let mut results = vec![];
                for node in self.nodes_in_class(class) {
                    match node {
                        Node::App { f, args } => {
                            if f == pf && pargs.len() == args.len() {
                                let mut todo = vec![subst.clone()];
                                for (pa, na) in pargs.iter().zip(args.iter()) {
                                    todo = todo
                                        .into_iter()
                                        .flat_map(|subst| self.ematch_rec(pa, *na, subst))
                                        .collect();
                                }

                                results.extend(todo);
                            }
                        }
                    }
                }
                results
            }
        }
    }

    pub fn apply_rules(&mut self, eclass: Id, rules: &[(Term, Term)]) {
        // Copy rules so we can mutate the e-graph while iterating matches.
        for (lhs, rhs) in rules {
            let matches = self.ematch(lhs, eclass);
            for subst in matches {
                let new_id = self.add_term(rhs, &subst);
                self.union(eclass, new_id);
            }
        }
    }

    pub fn run(&mut self, rules: &[(Term, Term)], n: usize) {
        for _i in 0..n {
            for eclass in 0..self.uf.len() {
                self.apply_rules(eclass, rules);
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
                .filter_map(|node| match node {
                    Node::App { f, args } => {
                        let arg_costs: Option<Vec<_>> =
                            args.iter().map(|&arg| worker(egraph, cost, arg)).collect();
                        let arg_costs = arg_costs?;
                        let total_cost = 1 + arg_costs
                            .iter()
                            .map(|(node_cost, _)| *node_cost)
                            .sum::<usize>();
                        let args = arg_costs.into_iter().map(|(_, term)| term).collect();
                        Some((total_cost, Term::App(f.clone(), args)))
                    }
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

#[cfg(test)]
mod tests {
    use crate::{rw, rws, term};

    use super::*;
    #[test]
    fn test_base_egraph() {
        let mut g = EGraph::default();
        g.add_term(&Term::App("a".into(), vec![]), &HashMap::new());
        let a = g.app("a", vec![]);
        let b = g.app("b", vec![]);
        g.union(a, b);
        assert_eq!(g.find(a), g.find(b));
    }
    #[test]
    fn test_extract() {
        let mut g = EGraph::default();
        let a = g.app("a", vec![]);
        let fa = g.app("f", vec![a]);
        g.union(fa, a);
        assert_eq!(g.extract(fa), (1, Term::App("a".into(), vec![])));
    }

    #[test]
    fn test_term_macro_vars() {
        assert_eq!(
            term!(f(?x, a, g(?y))),
            Term::App(
                "f".into(),
                vec![
                    Term::Var("x".into()),
                    Term::App("a".into(), vec![]),
                    Term::App("g".into(), vec![Term::Var("y".into())]),
                ],
            )
        );
    }

    #[test]
    fn test_rw_macro() {
        assert_eq!(
            rw!(f(?x) => g(?x)),
            (
                Term::App("f".into(), vec![Term::Var("x".into())]),
                Term::App("g".into(), vec![Term::Var("x".into())]),
            )
        );
    }

    #[test]
    fn test_rws_macro() {
        assert_eq!(
            rws![f(?x) => g(?x), a => b],
            vec![
                (
                    Term::App("f".into(), vec![Term::Var("x".into())]),
                    Term::App("g".into(), vec![Term::Var("x".into())]),
                ),
                (Term::App("a".into(), vec![]), Term::App("b".into(), vec![]),),
            ]
        );
    }
}
