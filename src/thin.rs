//! A Thinning EGraph to support alpha invariance

use std::collections::HashMap;
use std::fmt::Debug;
use std::iter::zip;
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Thin(Vec<bool>); // TODO: swtich to bitvec. smallbitvec, or smallvec, u32, box_leak;
// Is there a lighter weight thing if it doesn't need to be resizable? Neh.

impl Thin {
    //! Thinnings are mappings between contexts represented as bitvectors. true means keep, false means drop.
    //! They can also be thought of as liftings of functions by adding unused arguments
    //! [x,y,z].thin([true,false,true]) => [x,z]
    //! [x,z].widen([true,false,true]) => [x,_,z]
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

    fn dump0(&self) -> Self {
        //! Dump the first variable in the context. Useful for lambda abstraction where lambdas create a variable in scope
        let mut thin = self.0.clone();
        thin.remove(0);
        Thin(thin)
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

    //pub fn comp_mut(&mut self, other : &Thin){
    //}

    pub fn meet(&self, other: &Thin) -> (Thin, Thin, Thin) {
        //! widest_common_subthinning
        //! meet
        //! Compute the bitwise and widest common thinning and how to get there.
        //! self.comp(out.1) = other.comp(out.2)
        //! Pullback?
        debug_assert_eq!(self.dom(), other.dom());
        // Should I just do the dumb loop?
        let mut common = Vec::with_capacity(self.dom());
        let mut proj_self = vec![];
        let mut proj_other = vec![];
        for (&a, &b) in zip(self.0.iter(), other.0.iter()) {
            common.push(a && b);
            if a {
                proj_self.push(b);
            }
            if b {
                proj_other.push(a);
            }
        }
        (Thin(common), Thin(proj_self), Thin(proj_other))
    }

    pub fn join(&self, other: &Thin) -> (Thin, Thin, Thin) {
        //! thinnest_common_superthinning
        //! join
        //! union
        //! bitwise or
        // pushout?
        // common prefix
        debug_assert_eq!(self.dom(), other.dom());
        let mut prefix = Vec::with_capacity(self.dom());
        let mut proj_self = vec![];
        let mut proj_other = vec![];
        for (&a, &b) in zip(self.0.iter(), other.0.iter()) {
            prefix.push(a || b);
            if a || b {
                proj_self.push(a);
                proj_other.push(b);
            }
        }
        (Thin(prefix), Thin(proj_self), Thin(proj_other))
    }

    fn is_ge(&self, other: &Thin) -> bool {
        //! Is self a subthinning of other? I.e. is there a thinning from self to other?
        //! Proof relevant version would return the thinning that does it. Does there exists t, such that self . t = other
        debug_assert_eq!(self.dom(), other.dom());
        zip(self.0.iter(), other.0.iter()).all(|(a, b)| !*a || *b)
    }

    fn all_comm_triangles(&self, other: &Thin) -> Vec<Thin> {
        debug_assert_eq!(self.cod(), other.cod());
        if self.dom() <= other.dom() {
            if self == other {
                return vec![self.clone()];
            } else {
                return vec![];
            }
        }
        // tuple of how far along in other and current prefix
        let mut partials = vec![(0, Vec::with_capacity(self.dom()))];
        for &target in &self.0 {
            let mut next = Vec::new();
            for (j, bits) in partials {
                if !target {
                    let mut skip = bits.clone();
                    skip.push(false);
                    next.push((j, skip));
                }

                if j < other.dom() && other.0[j] == target {
                    let mut take = bits;
                    take.push(true);
                    next.push((j + 1, take));
                }
            }
            partials = next;
        }

        let res = partials
            .into_iter()
            .filter_map(|(j, bits)| (j == other.dom()).then_some(Thin(bits)))
            .collect::<Vec<_>>();
        debug_assert!(res.iter().all(|t| t.comp(other) == *self));
        res
    }
}

mod named {
    use super::Debug;
    use super::Thin;
    use super::zip;

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

    pub fn apply_thin<T: Clone>(thin: &Thin, big: &[T]) -> Vec<T> {
        //! Apply a thinning to a big context to get the small context.
        assert_eq!(thin.dom(), big.len());
        zip(thin.0.iter(), big.iter())
            .filter(|(b, _)| **b)
            .map(|(_, x)| x.clone())
            .collect()
    }

    // This is the named version of pullback?
    pub fn common_minctx<T: Eq + Clone + Debug>(
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
}
type RawId = usize;

/// An Id is the combo of a raw usize identifier and a thinning. This allows lifting an object into a weaker context without having to reintern it.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Id(Thin, RawId);
// Possibly Var could be factored to be a case in this enum. Eh. The convention that id = 0 is var seems fine.
// enum Id { EId(Thin, usize), Var} but Var might still need to be thinng. Id = (Thin, Option<usize) ?
impl Id {
    pub fn weaken(&self, thin: &Thin) -> Id {
        //! The action of widening / weakening on an Id. Brings the id into a larger context with some unused stuff in the context.
        assert_eq!(thin.cod(), self.0.dom());
        Id(thin.comp(&self.0), self.1)
    }

    pub fn ctx(&self) -> usize {
        //! The big context the Id has currently been lifted to
        self.0.dom()
    }
    pub fn minctx(&self) -> usize {
        //! The minimal context needed to make sense of the rawid.
        self.0.cod()
    }
    pub fn widen0(&self) -> Self {
        //! Widen to a context with one more variable that is not used. Useful for lambda abstraction when the body doesn't use the bound var.
        let mut thin = vec![false];
        thin.extend(self.0.0.iter());
        Id(Thin(thin), self.1)
    }
}

/// An ordinary syntax tree for user readability. Using the raw api is very painful and error prone.
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum Term {
    Var(String),
    App(Box<Term>, Box<Term>),
    //Lam(String, Box<Term>),
    Lit(String),
    EId(Id), // Do I want Vec<String> here? Or does the Id narrow from the full context. But I might not even know
             // PVar(String, Vec<String>) Miller pattern var
             // Drop(String, Box<Term>) explicitly say a variable is dropped. For weakening to an Id? Or for weakening to pattern variable, which then always captures everything
             // Kind of the converse of Lam.
}

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
    //pub fn lam(v: &str, body: Term) -> Self {
    //    Term::Lam(v.to_string(), Box::new(body))
    //}
    pub fn lit(s: &str) -> Self {
        Term::Lit(s.to_string())
    }
}

type TermInCtx = (Vec<String>, Term);

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Node {
    App(Id, Id),
    // Lam { var_used: bool, rawid: RawId },
    //Lam(Id), // Lam(var_used:bool, rawid : usize)
    Var,
    Lit(String), // Symbol? Constant.
    // Value(Value)
    UNode(Id, Id), // Maybe rawid because everything in eclass has same minimal context. No. rawid are terms which have a very concrete
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EGraph {
    memo: HashMap<Node, Id>,
    nodes: Vec<Node>,
    uf: Vec<Id>,
    minctx: Vec<usize>,
}
pub fn varid() -> Id {
    Id(Thin::id(1), 0)
}

type UserId = (Vec<String>, Id);

impl EGraph {
    pub fn new() -> Self {
        let mut memo = HashMap::new();
        memo.insert(Node::Var, varid());
        EGraph {
            memo,
            nodes: vec![Node::Var],
            uf: vec![varid()],
            minctx: vec![1],
        }
    }

    fn add_node(&mut self, ctx: usize, n: Node) -> Id {
        if let Some(id) = self.memo.get(&n) {
            self.find(id)
        } else {
            let id = Id(Thin::id(ctx), self.uf.len());
            self.uf.push(id.clone());
            self.nodes.push(n.clone());
            self.memo.insert(n, id.clone());
            self.minctx.push(ctx);
            id
        }
    }

    pub fn app(&mut self, f: Id, x: Id) -> Id {
        assert!(f.ctx() == x.ctx());
        let f = self.find(&f);
        let x = self.find(&x);
        // do find?
        // scan f for lambda? smart constructor loop might terminate?
        // add app node version, only subst version, do both

        // fthin :  [false, true, false]  : 3 -> 1
        // xthin :  [false, false, true] : 3 -> 1
        // common_thin : [false, true, true] : 3 -> 2
        // common_thin.conj().comp(common_thin) != id ...? Wha? Is this make any sense at all?
        // common_thin.conj().(fthin) = proj_fthin : [true, false] : 2 -> 1 // projected to common needed context
        // proj_xthin : [false, true] // projected common needed context
        // common_thin @ [true, true] |- App(proj_fthin, proj_xthin)
        // You want to intern in the smallest possible canonical context

        // Construct the app in the smallest common needed context
        let (common, f1thin, x1thin) = f.0.join(&x.0);
        let id = self.add_node(common.cod(), Node::App(Id(f1thin, f.1), Id(x1thin, x.1)));
        // Lift back into context actually requested
        id.weaken(&common)

        /*
        let thin_to_needed = f.0.bitor(&x.0); // bitwise or
        assert!(thin_to_needed.0.iter().all(|b| *b));
        // Wait... But shouldn't it e the case that thin_to_needed is all true?
        let f1 = Id(f.0.div(&thin_to_needed), f.1);
        let x1 = Id(x.0.div(&thin_to_needed), x.1);
        let id = self.add_node(thin_to_needed.cod(), Node::App(f1, x1));
        id.weaken(&thin_to_needed) // widen the id the common context;
        */
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

    /*
    fn lam(&mut self, body: Id) -> Id {
        assert!(
            body.ctx() != 0,
            "Body should have at least one variable in its context"
        );
        let body = self.find(&body);
        let thin = body.0.dump0(); // the scope of the lambda is the minctx of the "body.remove(0)", since it hsouldn't matter if body used var or not.
        // Also here. Everything in body should be true except _possibly_ the first value.
        // TODO: No. This is wrong. I need to dump, then work in the smallest. Id(Thin::id(thin.cod()), body.1)
        let id = self.add_node(
            thin.cod(),
            Node::Lam {
                var_used: body.0.0[0],
                rawid: body.1,
            },
        );
        id.weaken(&thin) // I'm just composing an identity with a thinning. seems wasteful
    }
    */

    pub fn find(&self, id: &Id) -> Id {
        let Id(mut thin, mut rawid) = id.clone();
        loop {
            let Id(thin1, rawid1) = self.uf[rawid].clone();
            if rawid1 == rawid {
                assert!(thin1.is_id());
                return Id(thin, rawid);
            } else {
                thin = thin.comp(&thin1);
                rawid = rawid1;
            }
        }
    }

    pub fn named_find(&self, nid: &UserId) -> UserId {
        let id = self.find(&nid.1);
        (named::apply_thin(&id.0, &nid.0), id)
    }
    pub fn is_eq(&mut self, a: &Id, b: &Id) -> bool {
        self.find(a) == self.find(b)
    }

    //pub fn user_union(ctx : &[String], a : UserId, b : UserId) {}
    fn union(&mut self, a: &Id, b: &Id) -> bool {
        assert_eq!(a.ctx(), b.ctx(), "Can only union ids in the same context");
        let a = self.find(a);
        let b = self.find(b);
        if a == b {
            false
        }
        /*
        // TODO: We can avoid making a new rawid in many cases (?) But unodes?
        else if a.0 == b.0 && a.0.is_id() {
            self.uf[a.1] =
        }
        else if a.0 <= b.0{
        }
        else if
        }*/
        else {
            let (common, proj_a, proj_b) = Thin::meet(&a.0, &b.0);
            let Id(_, rawz) = self.add_node(
                common.cod(),
                Node::UNode(Id(proj_a.clone(), a.1), Id(proj_b.clone(), b.1)),
            );
            self.uf[a.1] = Id(proj_a, rawz);
            self.uf[b.1] = Id(proj_b, rawz);
            true
        }
    }

    pub fn named_union(&mut self, ctx: &[String], a: UserId, b: UserId) -> bool {
        let (minctx, thina, thinb) = named::common_minctx(ctx, &a.0, &b.0);
        self.union(&a.1.weaken(&thina), &b.1.weaken(&thinb))
    }

    pub fn named_union0(&mut self, a: UserId, b: UserId) -> Option<bool> {
        // Result.
        if a.0 == b.0 {
            Some(self.union(&a.1, &b.1))
        } else {
            None
        }
    }

    pub fn rebuild(&mut self) {
        loop {
            let mut done = true;
            for i in 0..self.nodes.len() {
                let node = &self.nodes[i];
                let id = self.find(&self.uf[i]);
                match node {
                    Node::Lit(_) => {}
                    Node::Var => {}
                    Node::UNode(_, _) => {}
                    /*
                    Node::Lam { var_used, rawid } => {
                        panic!("unimplemented");
                        //let id1 = self.lam(Id(, rawid));
                        //done &= !self.union(&id, &id1);
                    } */
                    Node::App(f, x) => {
                        let id1 = self.app(f.clone(), x.clone());
                        done &= !self.union(&id, &id1);
                    }
                }
            }
            if done {
                return;
            }
        }
    }

    // I maybe suspect this should just be what happens when you hit a unode in ematching.

    fn all_liftable_node_ids(&self, id0: &Id) -> Vec<Id> {
        /*
        We find to rawid with smallest minctx and seek out all rawids that can be lifted into the requested context
        We then ave to reconcile all the ways there other thing may have to be fit into the larger context
        */
        let id0 = self.find(id0);
        let mut res = vec![];
        let ctx = id0.ctx();
        let thin0 = id0.0;
        let mut todo = vec![Id(Thin::id(thin0.cod()), id0.1)];
        while let Some(Id(thin, rawid)) = todo.pop() {
            match &self.nodes[rawid] {
                Node::UNode(a, b) => {
                    if a.ctx() <= ctx {
                        todo.push(Id(a.0.comp(&thin), a.1)); // This composition is in the opposite direction of weakening
                    }
                    if b.ctx() <= ctx {
                        todo.push(Id(b.0.comp(&thin), b.1));
                    }
                }
                _ => res.extend(
                    thin0
                        .all_comm_triangles(&thin)
                        .into_iter()
                        .map(|thin1| Id(thin1, rawid)),
                ),
            }
        }
        res
    }

    fn ematch(&self, pat: &Term, id: &Id) -> Vec<()> {
        let res = vec![];
        for id1 in self.all_liftable_node_ids(id) {
            let node = &self.nodes[id1.1];
            match (pat, node) {
                (Term::App(f, x), Node::App(f1, x1)) => {}
                //(Term::Lam(v, body), Node::Lam { var_used, rawid }) => {}
                (Term::Lit(l), Node::Lit(l1)) => {}
                (Term::Var(v), Node::Var) => {}
                (_, _) => {} // Term::EId(id1), _ =>
            }
        }
        res
    }

    /*
    In minimal version ignore lambda?
    */

    /*
    What I've done to ids is too funky. Now ids
     */
    // rebuild?
    //fn subst(&mut self, s : &Id, v : usize, t : &Id) {}
    // fn ematch
    // fn beta() // scan just for beta redexes and subst them

    // Hmm the isomorphism matching. That might be interesting.
    //fn ematch(&self, )

    // add_term is kind of named_add_node

    fn add_term_helper(&mut self, maxctx: &[String], t: Term) -> UserId {
        // Hmm. UserId could be a thinning from maxctx.
        match t {
            Term::Var(s) => (vec![s], self.var()), //  (maxctx.map(|name| name == s), self.var()
            Term::Lit(s) => (vec![], self.lit(s)),
            Term::App(f, x) => {
                let (fctx, fid) = self.add_term_helper(maxctx, *f);
                let (xctx, xid) = self.add_term_helper(maxctx, *x);
                let (minctx, widef, widex) = named::common_minctx(maxctx, &fctx, &xctx);
                // Hmm. What if add_node returns less than I thought? I should thin minctx
                (minctx, self.app(fid.weaken(&widef), xid.weaken(&widex)))
            }
            /*
            Term::Lam(v, body) => {
                // Search for shadowed x and remove it
                let mut bodymaxctx = maxctx.to_vec();
                if let Some(pos) = maxctx.iter().position(|s| *s == v) {
                    bodymaxctx.remove(pos);
                }
                // v is now available in the body in position 0. Should I reverse the direction I do this?
                bodymaxctx.insert(0, v.clone()); // [x,y,z] -> [v, x,y,z]
                let (mut bodyminctx, mut bid) = self.add_term_helper(&bodymaxctx, *body);
                if bodyminctx.len() == 0 || bodyminctx[0] != v {
                    // If the body doesn't use the variable, we need to pad with a false to kill the variable the lambda introduces.
                    bid = bid.widen0(); // [true, false] -> [false, true, false]
                } else {
                    // If the body does use the bound var, the lam_minctx doesn't have it
                    bodyminctx.remove(0); // [v, x] -> [x]
                }
                (bodyminctx, self.lam(bid))
            }
            */
            Term::EId(id) => {
                assert!(id.ctx() <= maxctx.len());
                //  = is_ssubseq(maxctx ,id.1).unwrap()
                (named::apply_thin(&id.0, maxctx), id)
            }
        }
    }

    pub fn add_term(&mut self, ctx: &[String], t: Term) -> UserId {
        // Make Result.
        let (minctx, id) = self.add_term_helper(ctx, t);
        let thin = named::is_subseq(ctx, &minctx).unwrap();
        (ctx.to_vec(), id.weaken(&thin))
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
    fn test_all_comm_triangles_no_extra_holes() {
        let self_ = Thin(vec![true, false, true]);
        let other = Thin(vec![true, true]);

        let triangles = self_.all_comm_triangles(&other);

        assert_eq!(triangles, vec![self_.clone()]);
        assert!(triangles.iter().all(|t| t.comp(&other) == self_));
    }

    #[test]
    fn test_all_comm_triangles_choose_one_extra_hole() {
        let self_ = Thin(vec![true, false, true, false]);
        let other = Thin(vec![true, false, true]);

        let mut triangles = self_.all_comm_triangles(&other);
        triangles.sort_by_key(|t| t.0.clone());

        assert_eq!(triangles, vec![Thin(vec![true, true, true, false])]);
        assert!(triangles.iter().all(|t| t.comp(&other) == self_));
    }

    #[test]
    fn test_all_comm_triangles_choose_two_extra_holes() {
        let self_ = Thin(vec![true, false, false, false, true]);
        let other = Thin(vec![true, false, false, true]);

        let triangles = self_.all_comm_triangles(&other);

        assert_eq!(triangles.len(), 3);
        assert!(triangles.iter().all(|t| t.dom() == self_.dom()));
        assert!(triangles.iter().all(|t| t.cod() == other.dom()));
        assert!(triangles.iter().all(|t| t.comp(&other) == self_));
        assert!(triangles.contains(&Thin(vec![true, true, false, true, true])));
        assert!(triangles.contains(&Thin(vec![true, true, true, false, true])));
        assert!(triangles.contains(&Thin(vec![true, false, true, true, true])));
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
        assert_eq!(x1.0, vec!["x".to_string(), "y".to_string()]);
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

        /*

        Add back when we return to lambda
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
        dbg!("{}", &c1);
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
        */

        let c1 = g.add_term(&[], Term::Lit("c".to_string()));
        let c2 = g.add_term(&[], Term::Lit("c1".to_string()));
        assert!(c1 != c2);
        assert!(!g.is_eq(&c1.1, &c2.1));
        assert_eq!(g.all_liftable_node_ids(&c1.1).len(), 1);
        assert!(g.union(&c1.1, &c2.1));
        assert_eq!(g.all_liftable_node_ids(&c1.1).len(), 2);
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
        assert!(g.union(&plusab.1, &plusba.1));
        let newid = g.find(&plusab.1);
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
            g.all_liftable_node_ids(&plusab.1).len(),
            2,
            "Should have two nodes in class",
        );

        let mut g = EGraph::new();
        let xzero = g.add_term(
            &["x".to_string()],
            Term::app2(Term::lit("+"), Term::var("x"), Term::lit("zero")),
        );
        assert_eq!(xzero.0.len(), 1);
        let zero = g.add_term(&["x".to_string()], Term::lit("zero"));
        assert_eq!(zero.0.len(), 1);
        // Hmm. unon a different contexts _could_ mean kill. But
        //g.union(&zero.1, &xzero.1);
        g.named_union(&["x".to_string()], zero.clone(), xzero.clone());
        let zero1 = g.named_find(&zero);
        assert_eq!(zero1.0.len(), 0);

        let zero2 = g.named_find(&xzero);
        assert_eq!(zero2.0.len(), 0);

        assert_eq!(zero1, zero2);

        //assert_eq!(g.nodes_in_class(&zero2.1).len(), 2);
        assert_eq!(g.all_liftable_node_ids(&Id(Thin::id(0), zero.1.1)).len(), 1);

        // Or is this just wrong. We should never be calling app on something that has
        // Widening should commute with app  app(f,x).wide() == app(f.wide(), x.wide())
        // It should also commute with lam.

        /*

        let a0 = g.add_term(&[], Term::lit("a"));
        let wa = a0.1.widen(&Thin(vec![false])); // widen to a context with one variable that is not used
        let fa0 = g.add_term(&[], Term::app(Term::lit("f"), Term::EId(a0.1)));
        let fa1 = g.add_term(&["x".to_string()], Term::app(Term::lit("f"), Term::EId(wa)));
        assert_eq!(fa0.1, fa1.1, "Widening should commute with app");
        assert_eq!(fa0.0.len(), 0, "fa0 should have empty minctx");
        assert_eq!(fa1.0.len(), 0, "fa1 should have empty minctx");

        */
    }
}

/*

/*
            for (thin, rawid) in ids {
            // Take those that can be raised into id0's context
            res.extend(
                id0.0
                    .all_comm_triangles(&thin)
                    .into_iter()
                    .map(|thin1| Id(thin1, rawid)),
            )
        }
     */

    pub fn nodes_in_class_no_find(&self, id: &Id) -> Vec<(Thin, usize)> {
        // Is it worth making this an Iterator instead of returning Vec?
        //let Id(thin, rawid) = self.find(id);
        let mut res = vec![];
        let ctx = id.ctx();
        let mut todo = vec![(Thin::id(id.minctx()), id.1)];
        //let orig_thin = id.0.clone();
        while let Some((thin, rawid)) = todo.pop() {
            match &self.nodes[rawid] {
                Node::UNode(a, b) => {
                    let thina = a.0.comp(&thin);
                    //if thina.dom() < ctx {
                        todo.push((thina, a.1)); // This composition is in the opposite direction of weakening
                    //}
                    todo.push((b.0.comp(&thin), b.1));
                }
                _ => res.push((thin, rawid)),
            }
        }
        res
    }

    pub fn nodes_in_class(&self, id: &Id) -> Vec<(Thin, usize)> {
        self.nodes_in_class_no_find(&self.find(id))
    }

// type Pattern = (usize, Term); // first n variables are pattern variables.

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
struct MinId {
    ctx: usize,
    rawid: usize,
} // An Id that has an implicit Id thinning of size ctx
// TODO: I should possibly have


    /*
    fn all_comm_squares(&self, other: &Thin) -> Vec<(Thin, Thin)> {
        // Its not _all_ of them but it is the non tivial ones that form a frontier.
        // Needed for bottom up ematching
        assert_eq!(self.cod(), other.cod());
        let self_ = &self.0;
        let other = &other.0;
        let mut todo = vec![(0, vec![], 0, vec![])];
        let mut res = vec![];
        while let Some((mut i, mut t1, mut j, mut t2)) = todo.pop() {
            while (i < self_.len() && self_[i]) || (j <= other.len() && other[j]) {
                if self_[i] && other[j] {
                    // Both take pinned value
                    t1.push(true);
                    t2.push(true);
                    i += 1;
                    j += 1;
                } else if self_[i] {
                    // have to take other to get back in sync to true true
                    // No we can still have true true true happen.
                    j += 1;
                    t1.push(false);
                    t2.push(true);
                    // No we can also take
                } else if other[j] {
                    // have to take self to get back in sync
                    i += 1;
                    t1.push(true);
                    t2.push(false);
                }
            }
            if i == self.0.len() && j == other.len() {
                let t1 = Thin(t1);
                let t2 = Thin(t2);
                assert_eq!(t1.dom(), t2.dom());
                assert_eq!(t1.cod(), self_.len());
                assert_eq!(t2.cod(), other.len());
                res.push((t1, t2))
            } else {
                // both false. Need to try both orderings
                assert!(!self_[i]);
                assert!(!other[j]);
                let mut t1a = t1.clone();
                let mut t2a = t2.clone();
                t1a.push(true);
                t2a.push(false);
                todo.push((i + 1, t1a, j, t2a));
                t1.push(false);
                t2.push(true);
                todo.push((i, t1, j + 1, t2));
            }
        }
        res
    }
    */

    /*
    fn all_comm_triangles(&self, other: &Thin) -> Vec<Thin> {
        /*

        */
        assert_eq!(self.cod(), other.cod());
        assert!(self.dom() >= other.dom());
        let N = self.dom() - self.cod();
        let k = other.dom() - other.cod();
        // all 1010101 strings with extras 1 digits. N choose k

        let res = vec![];
        let res = vec![(0, vec![])];
        for b in self.0 {}
    }
    */

    /*
    let obj = zip(self.0.iter(), other.0.iter())
        .filter(|(a, b)| **a && **b)
        .count();
    let proj_self = zip(self.0.iter(), other.0.iter())
        .filter_map(|(a, b)| if *a { Some(*b) } else { None })
        .collect();
    let proj_other = zip(self.0.iter(), other.0.iter())
        .filter_map(|(a, b)| if *b { Some(*a) } else { None })
        .collect();

    (obj, Thin(proj_self), Thin(proj_other))
    */

// UserId = (Vec<String>, usize)
/*
struct UserId { maxctx : Vec<String>, needed : thin, rawid : usize}
*/
            //let rawz = self.makeset(a.ctx()); // Hmm. Maybe this is wrong. I don't want nodes and uf out of sync. Maybe UNode is appropriate
            // Actually unodes are essential for enumeration, because the annotations are tree structured.
            // We actually need to insert carefully into unode tree? no, maybe not.
            // So the monus heap shows up as the enumerator?

    // TODO remove.
    pub fn bitor(&self, other: &Thin) -> Thin {
        //! bitwise or. Useful for computing the needed context of a node from its children.
        assert_eq!(self.dom(), other.dom());
        Thin(
            zip(self.0.iter(), other.0.iter())
                .map(|(x, y)| *x || *y)
                .collect(),
        )
    }

    fn div(&self, small: &Thin) -> Thin {
        //! self.comp(output) = small  if small <= self
        //! self :   ctxn -> ctxm
        //! small :  ctxn -> ctxk
        //! output : ctxm -> ctxk
        assert_eq!(self.dom(), small.dom());

        assert!(
            self.is_ge(small),
            "The small thinning should be a sub thinning of the bigger one (self)"
        ); // small <= self
        Thin(
            zip(self.0.iter(), small.0.iter())
                .filter(|(_, b)| **b)
                .map(|(a, _)| *a)
                .collect(),
        )
    }

        /*
        lam x, 5
        lam(wide([false], lit(5)))

        union(1 |- x * 0, 1 |- wide([false], 0))

        lam x, f(f(f(f(a))))
        lam(wide([false], f(f(f(f(a))))))
        lam(drop(x, f(f(f(f(a))))))
        */


    /*fn makeset(&mut self, ctx: usize) -> usize {
        let rawid = self.uf.len();
        self.uf.push(Id(Thin::id(ctx), rawid));
        rawid
    } */

    /*

    [false, true, true] . [true, false] = [false, true, false]


    [true, true, false] @ ([x,y] |- x + y) ===> [x, y, _] |- x + y
    [true, true, false] @ (2 |- v0 + v1)    ===> 3 |- v0 + v1
    [true, false , true] @ (2 |- v0 + v1)   ===> 3 |- v0 + v2

    (3 |- a + hole) @ [true, true, false] @ (2 |- v0 + v1)

    All of these are wrong though. They are in half de bruijn


    [true, false, true] |-  wide([false,true],v)  + wide([true, false], v) ======  v2 + v0 in the de bruijn sense.

     */

    pub fn lower(&self, thin: &Thin) -> Id {
        assert!(thin.is_ge(&self.0));
        Id(thin.div(&self.0), self.1)
    }


{x, y} |- x + y  slotted
[x, y] |- x + y  thinning

lam {x,y,z}, t(x,y,z)
lam [x,y,z], t(x,y,z)

sum {x,y,z}, t(x,y,z) slotted
sum [x,y,z], t(x,y,z)


union([x,y] |- f(x,y), [x,y] |- g(x,y))
union(2, f(v0, v1), g(v0, v1))
query:
 [x,y] | f(y,x) = [x,y] |- g(y,x) No

 [y,x] |- f(y,x) = [y,x] |- g(y,x) Yes
 [x,y] |- f(y,x) = g(y,x)
 2 |- f(v1, v0) = g(v1, v0)


 {x,y} |- f(x,y) -->   -keyword argument style -> sorting keyword argument <-> positional
 lam x y z,       positional argument style

global slot ordering but only mappings that monotonic or preserve that ordering --> thinnings

    /// global slot order?
    ///
    ///
    ///
    ///
    ///
    ///

    pub fn lcm(&self, other: &Thin) -> Thin {
        //! Reconcile two thinnings with common domain. Basically bitwise and.
        assert_eq!(self.dom(), other.dom());
        Thin(
            zip(self.0.iter(), other.0.iter())
                .map(|(x, y)| *x && *y)
                .collect(),
        )
    }


        /*
    fn divl(&self, other: &Thin) -> Self {
        //! self : ctxn ->
        //! small : ctxn ->
        //! output :
        other.div(self)
        /*
        Thin(
            zip(self.0.iter(), other.0.iter())
                .filter(|(a, b)| **a)
                .map(|(_, b)| *b)
                .collect(),
        )
        */
    }
    */
*/
