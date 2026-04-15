use std::collections::HashMap;
use std::fmt::Display;
pub type Id = usize;

type Name = String;
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct Node {
    pub f: Name,
    pub args: Vec<Id>,
} // | FixVar()

#[derive(Default)]
pub struct EGraph {
    pub memo: HashMap<Node, Id>,
    pub nodes: Vec<Node>, // todo Indexmap?
    pub uf: Vec<Id>,
    pub sibling: Vec<Id>,
    pub defns: HashMap<Id, Id>,
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum Term {
    Var(Name),
    App(Name, Vec<Term>),
    // EId
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
    pub fn add_term(&mut self, term: &Term, subst: &Subst) -> Id {
        match term {
            Term::Var(name) => subst[name],
            Term::App(f, args) => {
                let args = args.iter().map(|arg| self.add_term(arg, subst)).collect();
                self.add_node(Node { f: f.into(), args })
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

    // fn make_defn(&mut self, body) {} // ? fix? make_defn(&mut self, name, body)

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

    pub fn ematch(&self, pat: &Term, class: Id) -> Vec<Subst> {
        self.ematch_rec(0, pat, class, Default::default())
    }
    pub fn ematch_rec(&self, depth: usize, pat: &Term, class: Id, mut subst: Subst) -> Vec<Subst> {
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
            for eclass in 1..self.uf.len() {
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

#[cfg(test)]
mod tests {
    use super::*; // Import names from parent module
    #[test]
    fn test_coegraph() {
        let mut g = EGraph::default();
        g.add_term(&Term::App("a".into(), vec![]), &HashMap::new());
    }
}
