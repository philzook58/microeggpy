type Id = usize;
use indexmap::IndexSet;
use std::collections::HashMap;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum Node {
    App { f: Id, x: Id },
    Lit { name: String },
    Var { name: String },
    Impl { hyp: Id, conc: Id },
    And(Id, Id),
    Or(Id, Id),
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct Branch {
    subst: HashMap<String, Id>,
    goals: Vec<Id>,
    hyps: Vec<Node>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct State {
    tb: IndexSet<Node>,
    branches: Vec<Branch>,
}

impl State {
    pub fn app(&mut self, f: Id, x: Id) -> Id {
        self.tb.insert_full(Node::App { f, x }).0
    }
    pub fn lit(&mut self, name: impl AsRef<str>) -> Id {
        self.tb
            .insert_full(Node::Lit {
                name: name.as_ref().to_owned(),
            })
            .0
    }

    fn run(&mut self) {
        while let Some(mut branch) = self.branches.pop() {
            while let Some(goal) = branch.goals.pop() {
                match self.tb[goal] {
                    Node::And(a, b) => {
                        branch.goals.push(b);
                        branch.goals.push(a);
                    }
                    Node::Or(a, b) => {
                        let mut branch1 = branch.clone();
                        branch1.goals.push(b);
                        branch.goals.push(a);
                    }
                    _ => {}
                }
            }
        }
    }
}
