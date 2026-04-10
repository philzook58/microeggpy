//! A Thinning EGraph to support alpha invariance

use std::collections::HashMap;
use std::fmt::Debug;
use std::iter::zip;
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Thin(Vec<bool>); // TODO: swtich to bitvec. smallbitvec, or smallvec
// Is there a lighter weight thing if it doesn't need to be resiable? Neh.

impl Thin {
    //! Thinnings are mappings between contexts represented as bitvectors. true means keep, false means drop.
    //! https://www.philipzucker.com/thin1/
    pub fn id(n: usize) -> Self {
        Thin(vec![true; n])
    }

    pub fn is_id(&self) -> bool {
        self.0.iter().all(|b| *b)
    }

    /// Thinning go from big to small
    pub fn dom(&self) -> usize {
        self.0.len()
    }

    pub fn cod(&self) -> usize {
        self.0.iter().filter(|i| **i).count()
    }

    pub fn comp(&self, small: &Thin) -> Thin {
        //! compose self with small. self : A -> B, small : B -> C, output : A -> C
        assert_eq!(self.cod(), small.dom());
        let mut res = Vec::with_capacity(self.0.len());
        let mut j = 0;
        for b in self.0.iter() {
            if *b {
                res.push(small.0[j]);
                j += 1;
            } else {
                res.push(false);
            }
        }
        Thin(res)
    }

    pub fn lcm(&self, other: &Thin) -> Thin {
        //! Reconcile two thinnings with common domain. Basically bitwise and.
        assert_eq!(self.dom(), other.dom());
        Thin(
            zip(self.0.iter(), other.0.iter())
                .map(|(x, y)| *x && *y)
                .collect(),
        )
    }

    fn div(&self, small: &Thin) -> Thin {
        //! self.comp(output) = small  if small <= self
        assert_eq!(self.dom(), small.dom());
        Thin(
            zip(self.0.iter(), small.0.iter())
                .filter(|(_, b)| **b)
                .map(|(a, _)| *a)
                .collect(),
        )
    }
}

// Working with named contexts
pub fn is_subseq<T: Eq>(big: &[T], small: &[T]) -> Option<Thin> {
    //! Compute the thinning witness of extracting small from big if it exists.
    let mut res = Vec::with_capacity(big.len());
    let mut j = 0;
    for i in big.iter() {
        if j < small.len() && i == &small[j] {
            res.push(true);
            j += 1;
        } else {
            res.push(false);
        }
    }
    if j == small.len() {
        Some(Thin(res))
    } else {
        None
    }
}

fn common_minctx<T: Eq + Clone + Debug>(
    big: &[T],
    small1: &[T],
    small2: &[T],
) -> (Vec<T>, Thin, Thin) {
    //! From a maximal context and two needed contexts, find the smallest combo context and thinnning
    //! small1 = thin @ minctx
    //! small2 = thin @ minctx
    //! maxctx is needed to know how to interleave small1 and small2
    // assert!(is_subseq(big, small1).is_some() && is_subseq(big, small2).is_some()); // I guess the end check is also doing this
    let mut wide1 = vec![];
    let mut wide2 = vec![];
    let mut minctx: Vec<T> = vec![];
    let mut n1 = 0;
    let mut n2 = 0;
    // Reconcile the two minimal contexts. A sorted union
    dbg!("{} {} {}", big, small1, small2);
    for s in big.iter() {
        let take1 = n1 < small1.len() && small1[n1] == *s;
        let take2 = n2 < small2.len() && small2[n2] == *s;
        if take1 {
            n1 += 1;
        }
        if take2 {
            n2 += 1;
        }
        if take1 || take2 {
            minctx.push(s.clone());
            wide1.push(take1);
            wide2.push(take2);
        }
    }
    assert_eq!(n1, small1.len());
    assert_eq!(n2, small2.len());
    assert_eq!(minctx.len(), wide1.len());
    assert_eq!(minctx.len(), wide2.len());
    (minctx, Thin(wide1), Thin(wide2))
}
/// An Id is the combo of a raw usize identifier and a thinning. This allows lifting an object into a weaker context without having to reintern it.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Id(Thin, usize);
// Possibly Var could be factored to be a case in this enum. Eh. The convention that id = 0 is var seems fine.
// enum Id { EId(Thin, usize), Var} but Var might still need to be thinng. Id = (Thin, Option<usize) ?
impl Id {
    pub fn widen(&self, thin: &Thin) -> Id {
        //! The action of widening / weakening on an Id. Brings the id into a larger context with some unused stuff in the context.
        assert_eq!(thin.cod(), self.0.dom());
        Id(thin.comp(&self.0), self.1)
    }

    pub fn ctx(&self) -> usize {
        self.0.dom()
    }
    pub fn widen0(&self) -> Self {
        //! Widen to a context with one more variable that is not used. Useful for lambda abstraction when the body doesn't use the bound var.
        let mut thin = vec![false];
        thin.extend(self.0.0.iter());
        Id(Thin(thin), self.1)
    }
}
// TODO: I should possibly have

/// An ordinary syntax tree for user readability. Using the raw api is very painful and error prone.
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum Term {
    Var(String),
    App(Box<Term>, Box<Term>),
    Lam(String, Box<Term>),
    Lit(String),
    // PVar(String, Vec<String>) Miller pattern var
    // Id(Id) Embedded eid
    // Drop(String, Box<Term>) explicitly say a variable is dropped. For weakening to an Id? Or for weakening to pattern variable, which then always captures everything
    // Kind of the converse of Lam.
}
type Pattern = (usize, Term); // first n variables are pattern variables.

impl Term {
    pub fn var(v: &str) -> Self {
        Term::Var(v.to_string())
    }
    pub fn app(f: Term, x: Term) -> Self {
        Term::App(Box::new(f), Box::new(x))
    }
    pub fn app2(f: Term, x: Term, y: Term) -> Self {
        Term::App(Box::new(Term::App(Box::new(f), Box::new(x))), Box::new(y))
    }
    pub fn app3(f: Term, x: Term, y: Term, z: Term) -> Self {
        Term::App(
            Box::new(Term::App(
                Box::new(Term::App(Box::new(f), Box::new(x))),
                Box::new(y),
            )),
            Box::new(z),
        )
    }
    pub fn lam(v: &str, body: Term) -> Self {
        Term::Lam(v.to_string(), Box::new(body))
    }
    pub fn lit(s: &str) -> Self {
        Term::Lit(s.to_string())
    }
}

type TermInCtx = (Vec<String>, Term);

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Node {
    App(Id, Id),
    Lam(Id),
    Var,
    Lit(String), // Symbol? Constant
    // Value(Value)
    UNode(Id, Id),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EGraph {
    memo: HashMap<Node, Id>,
    nodes: Vec<Node>,
    uf: Vec<Id>,
}
pub fn varid() -> Id {
    Id(Thin::id(1), 0)
}

type UserId = (Vec<String>, Id);
/*
struct UserId { maxctx : Vec<String>, needed : thin, rawid : usize}
*/

impl EGraph {
    pub fn new() -> Self {
        let mut memo = HashMap::new();
        memo.insert(Node::Var, varid());
        EGraph {
            memo,
            nodes: vec![Node::Var],
            uf: vec![varid()],
        }
    }

    fn makeset(&mut self, ctx: usize) -> usize {
        let rawid = self.uf.len();
        self.uf.push(Id(Thin::id(ctx), rawid));
        rawid
    }

    fn add_node(&mut self, ctx: usize, n: Node) -> Id {
        if let Some(id) = self.memo.get(&n) {
            self.find(id)
        } else {
            let id = Id(Thin::id(ctx), self.uf.len());
            self.uf.push(id.clone());
            self.nodes.push(n.clone());
            self.memo.insert(n, id.clone());
            id
        }
    }

    pub fn app(&mut self, f: Id, x: Id) -> Id {
        assert!(f.ctx() == x.ctx());
        // scan f for lambda? smart constructor loop might terminate?
        // add app node version, only subst version, do both
        self.add_node(f.ctx(), Node::App(f, x))
    }
    /*
    pub fn app_beta(&mut self, f : Id, x : Id) -> Id
    {
        for id in self.enodes(f.rawid) {
            if let Node::Lam(body) = self.nodes[id] {
            return self.subst(&body, 0, &x);
            }
        }
        self.app(f,x);
    }
     */

    pub fn var(&self) -> Id {
        varid()
    }

    pub fn lit(&mut self, s: String) -> Id {
        self.add_node(0, Node::Lit(s))
    }

    pub fn lam(&mut self, body: Id) -> Id {
        assert!(body.ctx() != 0);
        self.add_node(body.ctx() - 1, Node::Lam(body))
    }

    pub fn find(&self, id: &Id) -> Id {
        let Id(mut thin, mut rawid) = id.clone();
        loop {
            let Id(thin1, rawid1) = self.uf[rawid].clone();
            if rawid1 == rawid {
                return Id(thin, rawid);
            } else {
                thin = thin1.comp(&thin);
                rawid = rawid1;
            }
        }
    }

    pub fn is_eq(&mut self, a: &Id, b: &Id) -> bool {
        self.find(a) == self.find(b)
    }
    pub fn union(&mut self, a: &Id, b: &Id) -> Option<Id> {
        assert_eq!(a.ctx(), b.ctx(), "Can only union ids in the same context");
        let a = self.find(a);
        let b = self.find(b);
        if a == b {
            None
        }
        /*
        // TODO: We can avoid making a new rawid in many cases (?)
        else if a.0 == b.0 && a.0.is_id() {
            self.uf[a.1] =
        }
        else if a.0 <= b.0{
        }
        else if
        }*/
        else {
            let thin = a.0.lcm(&b.0);
            let Id(_, rawz) = self.add_node(thin.cod(), Node::UNode(a.clone(), b.clone()));
            //let rawz = self.makeset(a.ctx()); // Hmm. Maybe this is wrong. I don't want nodes and uf out of sync. Maybe UNode is appropriate
            // Actually unodes are essential for enumeration, because the annotations are tree structured.
            // We actually need to insert carefully into unode tree? no, maybe not.
            // So the monus heap shows up as the enumerator?
            self.uf[a.1] = Id(thin.div(&a.0), rawz);
            self.uf[b.1] = Id(thin.div(&b.0), rawz);
            Some(Id(thin, rawz))
        }
    }

    pub fn nodes_in_class_no_find(&self, id: &Id) -> Vec<Id> {
        // Is it worth making this an Iterator instead of returning Vec?
        //let Id(thin, rawid) = self.find(id);
        let mut res = vec![];
        let mut todo = vec![id.clone()];
        while let Some(id) = todo.pop() {
            match &self.nodes[id.1] {
                Node::UNode(a, b) => {
                    let thin = id.0;
                    todo.push(a.widen(&thin));
                    todo.push(b.widen(&thin));
                }
                _ => res.push(id),
            }
        }
        res
    }

    pub fn nodes_in_class(&self, id: &Id) -> Vec<Id> {
        self.nodes_in_class_no_find(&self.find(id))
    }
    /*
    What I've done to ids is too funky. Now ids
     */
    // rebuild?
    //fn subst(&mut self, s : &Id, v : usize, t : &Id) {}
    // fn ematch
    // fn beta() // scan just for beta redexes and subst them

    // Hmm the isomorphism matching. That might be interesting.
    //fn ematch(&self, )

    pub fn add_term(&mut self, maxctx: &[String], t: Term) -> UserId {
        // Hmm. UserId could be a thinning from maxctx.
        match t {
            Term::Var(s) => (vec![s], self.var()),
            Term::Lit(s) => (vec![], self.lit(s)),
            Term::App(f, x) => {
                let (fctx, fid) = self.add_term(maxctx, *f);
                let (xctx, xid) = self.add_term(maxctx, *x);
                let (minctx, widef, widex) = common_minctx(maxctx, &fctx, &xctx);
                (minctx, self.app(fid.widen(&widef), xid.widen(&widex)))
            }
            Term::Lam(v, body) => {
                // Search for shadowed x and remove it
                let mut bodymaxctx = maxctx.to_vec();
                if let Some(pos) = maxctx.iter().position(|s| *s == v) {
                    bodymaxctx.remove(pos);
                }
                // v is now available in the body in position 0. Should I reverse the direction I do this?
                bodymaxctx.insert(0, v.clone());
                let (mut bodyminctx, mut bid) = self.add_term(&bodymaxctx, *body);
                if bodyminctx.len() == 0 || bodyminctx[0] != v {
                    // If the body doesn't use the variable, we need to pad with a false to kill the variable the lambda introduces.
                    bid = bid.widen0();
                } else {
                    // If the body does use the bound var, the lam_minctx doesn't have it
                    bodyminctx.remove(0);
                }
                (bodyminctx, self.lam(bid))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*; // Import names from parent module
    #[test]
    fn test_thin() {
        assert!(Thin::id(3).dom() == 3);
        assert!(Thin::id(3).cod() == 3);
        let t1 = Thin(vec![true, false, true]);
        assert!(&Thin::id(3).comp(&t1) == &t1);
        assert!(&t1.comp(&Thin::id(2)) == &t1);
    }
    #[test]
    fn test_egraph() {
        let mut g = EGraph::new();
        let x = g.var();
        let y = g.var();
        assert!(x.ctx() == 1);

        let x1 = g.add_term(&["x".to_string()], Term::Var("x".to_string()));
        assert!(x1.0 == vec!["x".to_string()]);
        assert!(x1.1 == x);

        let x1 = g.add_term(
            &["x".to_string(), "y".to_string()],
            Term::Var("x".to_string()),
        );
        assert!(x1.0 == vec!["x".to_string()]); // min context is just x, y is not used
        let id1 = g.app(x.clone(), y.clone());
        let id2 = g.app(x.clone(), y.clone());
        assert!(id1 == id2);
        assert!(id1.ctx() == 1);

        let a = g.lit("a".to_string());
        let b = g.lit("b".to_string());
        assert!(a != b);

        let a1 = g.add_term(&[], Term::Lit("a".to_string()));
        assert!(a1.1 == a);

        let ab = g.app(a.clone(), b.clone());
        assert!(ab.ctx() == 0);

        let (emp, id1) = g.add_term(
            &[],
            Term::Lam("x".to_string(), Box::new(Term::Var("x".to_string()))),
        );
        assert_eq!(emp.len(), 0);
        let (emp, id2) = g.add_term(
            &[],
            Term::Lam("y".to_string(), Box::new(Term::Var("y".to_string()))),
        );
        assert_eq!(emp.len(), 0);
        assert_eq!(id1, id2);

        let c1 = g.add_term(
            &["x".to_string()],
            Term::Lam("y".to_string(), Box::new(Term::Var("x".to_string()))),
        );
        assert_eq!(c1.0, vec!["x".to_string()]);
        assert_eq!(c1.1.ctx(), 1);
        //let c2 = g.add_term(&[], Term.Lam("x".to_string(), Box::new(c1.1)));

        let const1 = g.add_term(
            &[],
            Term::Lam(
                "x".to_string(),
                Box::new(Term::Lam(
                    "y".to_string(),
                    Box::new(Term::Var("x".to_string())),
                )),
            ),
        );
        let const2 = g.add_term(
            &[],
            Term::Lam(
                "a".to_string(),
                Box::new(Term::Lam(
                    "b".to_string(),
                    Box::new(Term::Var("a".to_string())),
                )),
            ),
        );
        assert_eq!(
            const1.1, const2.1,
            "alpha equivalent terms should map to same id"
        );

        let c1 = g.add_term(&[], Term::Lit("c".to_string()));
        let c2 = g.add_term(&[], Term::Lit("c1".to_string()));
        assert!(c1 != c2);
        assert!(!g.is_eq(&c1.1, &c2.1));
        assert_eq!(g.nodes_in_class(&c1.1).len(), 1);
        let c3 = g.union(&c1.1, &c2.1).unwrap();
        assert_eq!(g.nodes_in_class(&c3).len(), 2);
        assert!(g.is_eq(&c1.1, &c2.1));

        let plusab = g.add_term(
            &["a".to_string(), "b".to_string()],
            Term::App(
                Box::new(Term::App(
                    Box::new(Term::Lit("+".to_string())),
                    Box::new(Term::Var("a".to_string())),
                )),
                Box::new(Term::Var("b".to_string())),
            ),
        );
        let plusba = g.add_term(
            &["a".to_string(), "b".to_string()],
            Term::App(
                Box::new(Term::App(
                    Box::new(Term::Lit("+".to_string())),
                    Box::new(Term::Var("b".to_string())),
                )),
                Box::new(Term::Var("a".to_string())),
            ),
        );
        assert!(!g.is_eq(&plusab.1, &plusba.1));
        let newid = g.union(&plusab.1, &plusba.1).unwrap();
        assert!(g.is_eq(&plusab.1, &plusba.1));

        let n_nodes = g.nodes.len();
        // A construction macro would be killer.
        let plusxy = g.add_term(
            &["x".to_string(), "y".to_string()],
            Term::app2(Term::lit("+"), Term::var("x"), Term::var("y")),
        );
        assert_eq!(g.nodes.len(), n_nodes, "Should hit the memo");
        assert_eq!(plusxy.0, vec!["x".to_string(), "y".to_string()]);
        assert_eq!(plusxy.1, newid, "finds to newid");
        assert!(g.is_eq(&plusxy.1, &plusab.1), "Should be equal to plusab");

        assert_eq!(
            g.nodes_in_class(&plusab.1).len(),
            2,
            "Should have two nodes in class",
        );
    }
}
