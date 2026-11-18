# Notes

Historical comments and TODOs are preserved verbatim below. They describe experiments
and earlier implementations, and are not a current roadmap.

Original blog posts: [thinnings](https://www.philipzucker.com/thin1/),
[Miller e-graphs](https://www.philipzucker.com/lambda_miller_egg/),
[higher-order unification](https://www.philipzucker.com/ho_unify/),
[ground lambda Prolog](https://www.philipzucker.com/ground_lambda_prolog/),
[Knuck Prolog](https://www.philipzucker.com/knuck_prolog/).

## Original `benches/my_benchmark.rs`

```rust
//let rules = vec![
//    (Term::App("+".into(), vec![Term::Var("x".into()), Term::Var("y".into())]), Term::App("+".into(), vec![Term::Var("x".into()), Term::Var("y".into())]))
//]
```

## Original `examples/profile_ac.rs`

```rust
//g.rebuild();
//println!("{:?}", g);
```

## Original `src/backtrack.rs`

```rust
/*
Backtracking / Proofs
Write only log? Similar to trail. Enough to undo is also enough to prove.

Wrap base or just copy over

*/
```

## Original `src/base.rs`

```rust
// Largely pulled from: https://github.com/mwillsey/microegg/blob/main/src/lib.rs
    pub nodes: Vec<Node>, // todo Indexmap?
// EId
// Splice together the two loops of siblings
// Could track as field in EGraph.
// copy needed for borrowing
                egraph.union(id2, existing_id); // order matters?
// Copy rules so we can mutate the e-graph while iterating matches.
```

## Original `src/coegraph.rs`

```rust
    App { f: Name, args: Vec<Id> }, // is_constr / is_guard / is_productive : bool
/*
Slotted and Thinning have their own Var constructor. Hmm.
FixVar is enough of a blocker that the new thing and it's body are not exactly automatically identified. Just Fix()?

App(), Lit(), FixVar(Id), Constr(f : String, args : Vec<Id>
*/
    pub nodes: Vec<Node>, // todo Indexmap?
//pub defns: HashMap<Id, Id>,
// fixes : HashSet<Id>
// EId
// fn make_defn(&mut self, body) {} // ? fix? make_defn(&mut self, name, body)
// Or is the flimflam too cute?
// Splice together the two loops of siblings
// Tie break to constructor?
// Could track as field in EGraph.
/*
    fn is_bisim_rec(&self, a: Id, b: Id, seen: &mut Vec<(bool, Id, Id)>) -> bool {
        if a == b {
            return true;
        } else if guarded && seen.contains(&(a, b)) {
          // Hmm. That's not right? We need to record guard points in the seen
          // and also if contains unguarded we need to fail to avoid 1*a = 1*b loop
        }

        else {
            seen.push((a, b));
            for nodea in seld.nodes_in_class(a) {
                for nodeb in self.nodes_in_class(b) {}
            }
            seen.pop();
        }
    }

    pub fn is_bisim(&self, a: Id, b: Id) -> bool {
        let a = self.find(a);
        let b = self.find(b);
        let mut stack = vec![];
        self.is_bisim_rec(a, b, false, &mut stack)
    }

    // Maybe I could do this bottom up. Do sort of a hypothetical query that tracks
    // n*2?
    */
// copy needed for borrowing
// TODO Bisimilar compaction
                ), // Make a dummy id, come back later and patch it up.
                            ); // Really we should check there are not transitive self loops, but this is cheap and easy
// Copy rules so we can mutate the e-graph while iterating matches.
// Extraction needs to output a full  definitional equational system. &[Term] where each Term can refer to Var(n) in a fixedpoint manner
// Actually this is kind of a nice way to put a name into the egraph that it won't show up in the extraction?
    use super::*; // Import names from parent module
```

## Original `src/extract.rs`

```rust
// Extraction gym could use some rationalization.
```

## Original `src/junk_drawer/glattice.rs`

```rust
// Look at Rudi's interfaces
```

## Original `src/junk_drawer/uf.rs`

```rust
    fn makeset(&mut self) -> Self::Id; // take in extra data?
/*

Slotted Uf
Thin UF
Monus UF
Group UF
Value UF
Constructor UF
All? Then we avoid
extensible annotations. Per sort?
struct Id = {annot : [], data: T}

Extensible Analysis data?

Egraph8/16/32/64  . Don't use a bigger id type than you need.
8 would be somewhat silly. 16 at least.
Unless you have a ton of copies

*/
```

## Original `src/lib.rs`

```rust
// pub mod uf;
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
        pub nodes: Vec<Node>, // todo Indexmap?
// If we opened up ematch to one that starts on a node, we could avoid this.
                self.add_node(node) // micro rebuild
// Splice together the two loops of siblings
// Could track as field in EGraph.
// copy needed for borrowing
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
// Copy rules so we can mutate the e-graph while iterating matches.
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
```

## Original `src/macros.rs`

```rust
// Pattern variables are written with a leading `?`, e.g. `term!(?x)`.
// Applications are written as `term!(f(...))`. The contents inside the
// parentheses are parsed by `__term_args!` as a comma-separated term list.
// A bare identifier is a nullary application, e.g. `term!(a)`.
// Empty argument list: `term!(f())`.
// Parse a variable argument at the front of the list, then recurse on the
// comma-separated tail if one exists.
// Parse an application or nullary application at the front of the list.
// `$head` is the function/name, and optional `(...)` captures nested args
// such as `g(?y)`.
```

## Original `src/prolog.rs`

```rust
// https://www.philipzucker.com/ground_lambda_prolog/
// https://www.philipzucker.com/knuck_prolog/
    hyps: Vec<Node>, // local_facts / hyps / ctx
// linear_facts
// uf
// constrs
    branches: Vec<Branch>, // maybe a tree
//global_rules :
                    _ => {} // todo
// Also that Horn sat stuff could be cool.
```

## Original `src/pthin.rs`

```rust
/*
lift :
dump :

PThin represents a normal form of lifting and dumping combinators on functional expressions
  lift(t,dump(d, f))
dump partially applies f to some junk constants.
I suppose dump could contain values? eids?
lift allows f to take more arguments by throwing them away.
*/
// Maybe mutate both? And output the common
// Update b with new projection
// Is 0 |- var == junk ?   ([],[false]) @ var ought to be junk. var = id.
// literals should come with a context too? Then remove var. What about multiaorted vars
        g.union(&av0, &av1); // We are determining a tosses it's arugment
//assert_eq!(g.find(&av0).pthin.wide.len(), 2);
```

## Original `src/sexp.rs`

```rust
// https://github.com/mwillsey/microegg/blob/main/src/sexp.rs
    *pos += 1; // consume '('
```

## Original `src/thin.rs`

```rust
//! A Thinning EGraph to support alpha invariance
pub struct Thin(Vec<bool>); // TODO: swtich to bitvec. smallbitvec, or smallvec, u32, box_leak;
// Is there a lighter weight thing if it doesn't need to be resizable? Neh.
//! Thinnings are mappings between contexts represented as bitvectors. true means keep, false means drop.
//! They can also be thought of as liftings of functions by adding unused arguments
//! [x,y,z].thin([true,false,true]) => [x,z]
//! [x,z].widen([true,false,true]) => [x,_,z]
//! https://www.philipzucker.com/thin1/
/// Thinning go from big to small
//! compose self with small. self : A -> B, small : B -> C, output : A -> C
//pub fn comp_mut(&mut self, other : &Thin){
//}
//! widest_common_subthinning
//! meet
//! Compute the bitwise and widest common thinning and how to get there.
//! self.comp(out.1) = other.comp(out.2)
//! Pullback?
// Should I just do the dumb loop?
//! thinnest_common_superthinning
//! join
//! union
//! bitwise or
// pushout?
// common prefix
//! Is self a subthinning of other? I.e. is there a thinning from self to other?
//! Proof relevant version would return the thinning that does it. Does there exists t, such that self . t = other
// tuple of how far along in other and current prefix
/// An Id is the combo of a raw usize identifier and a thinning. This allows lifting an object into a weaker context without having to reintern it.
// Possibly Var could be factored to be a case in this enum. Eh. The convention that id = 0 is var seems fine.
// enum Id { EId(Thin, usize), Var} but Var might still need to be thinng. Id = (Thin, Option<usize) ?
//! The action of widening / weakening on an Id. Brings the id into a larger context with some unused stuff in the context.
//! The big context the Id has currently been lifted to
//! The minimal context needed to make sense of the rawid.
/// An ordinary syntax tree for user readability. Using the raw api is very painful and error prone.
    EId(Id), // Do I want Vec<String> here? Or does the Id narrow from the full context. But I might not even know
// PVar(String, Vec<String>) Miller pattern var
// Drop(String, Box<Term>) explicitly say a variable is dropped. For weakening to an Id? Or for weakening to pattern variable, which then always captures everything
// Kind of the converse of Lam.
//
//Lam(String, Box<Term>),
    UNode(Id, Id), // Maybe rawid because everything in eclass has same minimal context. No. rawid are terms which have a very concrete
// Construct the app in the smallest common needed context
// Lift back into context actually requested
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
//pub fn user_union(ctx : &[String], a : UserId, b : UserId) {}
/*
        // TODO: We can avoid making a new rawid in many cases (?) But unodes?
        else if a.0 == b.0 && a.0.is_id() {
            self.uf[a.1] =
        }
        else if a.0 <= b.0{
        }
        else if
        }*/
/*
                    Node::Lam { var_used, rawid } => {
                        panic!("unimplemented");
                        //let id1 = self.lam(Id(, rawid));
                        //done &= !self.union(&id, &id1);
                    } */
// I maybe suspect this should just be what happens when you hit a unode in ematching.
/*
        We find to rawid with smallest minctx and seek out all rawids that can be lifted into the requested context
        We then ave to reconcile all the ways there other thing may have to be fit into the larger context
        */
                        todo.push(Id(a.0.comp(&thin), a.1)); // This composition is in the opposite direction of weakening
//(Term::Lam(v, body), Node::Lam { var_used, rawid }) => {}
                (_, _) => {} // Term::EId(id1), _ =>
    use super::*; // Import names from parent module
//let x1 = g.add_term(&["x".to_string()], Term::Var("x".to_string()));
//assert!(x1.0 == vec!["x".to_string()]);
//assert!(x1.1 == x);
//assert_eq!(x1.0, vec!["x".to_string(), "y".to_string()]);
//assert!(a1.1 == a);
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
// A construction macro would be killer.
// Hmm. unon a different contexts _could_ mean kill. But
//g.union(&zero.1, &xzero.1);
//assert_eq!(g.nodes_in_class(&zero2.1).len(), 2);
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
// Working with named contexts
//! Compute the thinning witness of extracting small from big if it exists.
//! Apply a thinning to a big context to get the small context.
// This is the named version of pullback?
//! From a maximal context and two needed contexts, find the smallest combo context and thinnning
//! small1 = thin @ minctx
//! small2 = thin @ minctx
//! maxctx is needed to know how to interleave small1 and small2
// assert!(is_subseq(big, small1).is_some() && is_subseq(big, small2).is_some()); // I guess the end check is also doing this
// Reconcile the two minimal contexts. A sorted union
/*
type UserId = (Vec<String>, Id);

    pub fn named_union0(&mut self, a: UserId, b: UserId) -> Option<bool> {
        // Result.
        if a.0 == b.0 {
            Some(self.union(&a.1, &b.1))
        } else {
            None
        }
    }
    pub fn named_union(&mut self, ctx: &[String], a: UserId, b: UserId) -> bool {
        let (minctx, thina, thinb) = named::common_minctx(ctx, &a.0, &b.0);
        self.union(&a.1.weaken(&thina), &b.1.weaken(&thinb))
    }
    pub fn named_find(&self, nid: &UserId) -> UserId {
        let id = self.find(&nid.1);
        (named::apply_thin(&id.0, &nid.0), id)
    }
type TermInCtx = (Vec<String>, Term);

    pub fn widen0(&self) -> Self {
        //! Widen to a context with one more variable that is not used. Useful for lambda abstraction when the body doesn't use the bound var.
        let mut thin = vec![false];
        thin.extend(self.0.0.iter());
        Id(Thin(thin), self.1)
    }
    fn dump0(&self) -> Self {
        //! Dump the first variable in the context. Useful for lambda abstraction where lambdas create a variable in scope
        let mut thin = self.0.clone();
        thin.remove(0);
        Thin(thin)
    }

    //pub fn lam(v: &str, body: Term) -> Self {
    //    Term::Lam(v.to_string(), Box::new(body))
    //}
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
// Lam { var_used: bool, rawid: RawId },
//Lam(Id), // Lam(var_used:bool, rawid : usize)
// Symbol? Constant.
// Value(Value)
// add_term is kind of named_add_node
// Hmm. UserId could be a thinning from maxctx.
            Term::Var(s) => (vec![s], self.var()), //  (maxctx.map(|name| name == s), self.var()
// Hmm. What if add_node returns less than I thought? I should thin minctx
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
//  = is_ssubseq(maxctx ,id.1).unwrap()
// Make Result.
/*
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
        let thin_to_needed = f.0.bitor(&x.0); // bitwise or
        assert!(thin_to_needed.0.iter().all(|b| *b));
        // Wait... But shouldn't it e the case that thin_to_needed is all true?
        let f1 = Id(f.0.div(&thin_to_needed), f.1);
        let x1 = Id(x.0.div(&thin_to_needed), x.1);
        let id = self.add_node(thin_to_needed.cod(), Node::App(f1, x1));
        id.weaken(&thin_to_needed) // widen the id the common context;
        */
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
// Is it worth making this an Iterator instead of returning Vec?
//let Id(thin, rawid) = self.find(id);
//let orig_thin = id.0.clone();
//if thina.dom() < ctx {
                        todo.push((thina, a.1)); // This composition is in the opposite direction of weakening
//}
// type Pattern = (usize, Term); // first n variables are pattern variables.
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
// all 1010101 strings with extras 1 digits. N choose k
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
//! bitwise or. Useful for computing the needed context of a node from its children.
//! self.comp(output) = small  if small <= self
//! self :   ctxn -> ctxm
//! small :  ctxn -> ctxk
//! output : ctxm -> ctxk
        ); // small <= self
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
/// global slot order?
///
///
///
///
///
///
//! Reconcile two thinnings with common domain. Basically bitwise and.
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
```

## Lifting commentary from lambda-microegg

```rust
//! Liftings are annotations on the edges of the union-find, akin to group
//! elements like offsets. Each ID represents a function taking ordered arguments;
//! lifting adds redundant arguments:
//!
//! ```text
//! fun x y => x + y  -----lift_101----->  fun x y z => x + z
//! ```
//!
//! These functions are NOT equal, but are clearly highly related. The lifting
//! e-graph deduplicates interning memory for different lifts of the same base
//! function. Liftings have identity and composition. They form a category
//! (uh oh! I said the C word!).
//!
//! Philip's original explanations:
//! - <https://www.philipzucker.com/thin1/>
//! - <https://www.philipzucker.com/lambda_miller_egg/>
//! - <https://github.com/philzook58/lambda-microegg>
```

Original syntax note:

> These are for conventional user syntax, beside the main point of thinning/lifting
> inside the e-graph. Working with raw thinnings is too mind boggling.

## API and migration reference

## Ordinary terms

```python
from microegg import EGraph, Term

g = EGraph()
a = Term.App("a", [])
x = Term.Var("x")                       # a pattern metavariable
start = g.add_term(Term.App("f", [a]))
g.add_rule(Term.App("f", [x]), x)
g.run(5)                                # at most five rounds
assert g.extract(start) == (1, a)
```

`add(name, child_ids)` and `add_node(Node(name, child_ids))` build nodes directly.
`find(id)` returns the current union-find representative. `union(a, b)` asserts
an equality. `rebuild()` closes congruence and returns whether it changed the
graph. `is_eq`, `ematch`, and `extract` rebuild before querying; `find` only follows
existing union-find links. `ematch(pattern, id)` returns dictionaries of captures.
`run(limit)` searches all rules before applying a round's matches and stops when
stable, returning the number of rounds performed. `extract(id)` returns
`(node_count, term)` for a smallest finite representative. Graph-local IDs must
only be used with the graph that created them.

## Scoped terms and patterns

```python
from microegg import thin

T = thin.Term
g = thin.EGraph()
identity = T.binder("lam", T.bvar(0))
term = g.add(identity)
assert g.extract(term) == (2, identity)
assert g.ematch(T.binder("lam", T.meta("body", [0])), term)
assert not g.ematch(T.binder("lam", T.meta("closed")), term)
```

The constructors are `atom(name)`, `fvar(level)`, `bvar(index)`,
`app(function, argument)`, `binder(operator, body)`, and
`meta(name, parameters=[])`. Application is binary and curried; for `f(a,b)` write
`T.app(T.app(T.atom("f"), a), b)`. Every binder introduces one variable;
`lam`, `sum`, and `forall` are ordinary operator names. Alpha equivalence is
structural because bound variables have indices rather than names.

- `fvar(i)` selects level `i` in the ambient context passed to `g.add(term, ctx)`.
  Levels count from zero, outermost first, and retain their meaning under binders.
- `bvar(0)` selects the nearest enclosing syntax binder, `bvar(1)` the next, etc.
- `meta("m")` may depend on the entire ambient context, but on none of the
  binders introduced inside its pattern.
- `meta("m", [1, 0])` additionally permits the next and nearest pattern binders.
  Parameters must be distinct bound-variable indices in decreasing order
  (outermost to innermost). Both sides of a rule use this restriction. A repeated
  metavariable must have the same arity, and each RHS metavariable must occur on
  the LHS. Arbitrary term arguments and permutations are rejected.

Metavariables belong to patterns only: `add` rejects them. `add_rule` validates
both sides before storing a rule; malformed patterns passed to `ematch` also
raise an error. Rules mentioning free-variable levels run only in contexts large
enough for both sides. A capture dictionary stores each metavariable in
`ambient context + its ordered formal parameters`.

### Sum factorization

```python
from microegg import thin
T = thin.Term

def mul(a, b):
    return T.app(T.app(T.atom("mul"), a), b)

g = thin.EGraph()
a, body = T.meta("a"), T.meta("body", [0])
g.add_rule(T.binder("sum", mul(a, body)),
           mul(a, T.binder("sum", body)))
start = g.add(T.binder("sum", mul(T.atom("constant"), T.bvar(0))))
g.run(5)
expected = g.add(mul(T.atom("constant"), T.binder("sum", T.bvar(0))))
assert g.is_eq(start, expected)
```

The first capture cannot depend on the summation variable. Consequently the
rule does not match `sum i. mul(i, constant)`.

### Thinnings and low-level construction

`Thin([True, False, True])` embeds two variables in a three-variable context.
`dom()` counts selected variables; `cod()` is the ambient context length.
`outer.compose(inner)` composes injections. `identity(n)`, `unused(n)`, and
`select(n, level)` construct common thinnings. There is no machine-word limit.

Scoped `Id` values are immutable and expose `raw`, `thinning`, and `ctx`.
`id.weaken(thin)` embeds an ID in a larger context without reinterning it.
`id.in_context(n)` adds unused trailing variables or removes unused trailing
ones. Low-level graph constructors are `var(ctx, level)`, `atom(name, ctx=0)`,
`app(function_id, argument_id)`, and `binder(operator, body_id)`; the bound
variable is the body's final context variable.

Equating different placements of one class can remove dependencies, rather
than equating the variables themselves. Rebuild after unions, then use
`g.find(id)` to obtain the smaller dependency mask before shrinking its context.
As with ordinary graphs, all IDs are local to their creating graph. `extract`
raises `ValueError` if no finite representative exists in the requested context.
Its node-count cost counts variables, atoms, application nodes, and binders.

## Development and migration

```sh
uv sync
uv run maturin develop
uv run pytest -q
cargo test
```

For wheel verification, use `uv run maturin build`, install the wheel in a fresh
environment, and run the Python tests there. Maturin enables the extension-module
linking feature for Python builds; ordinary Cargo tests link Python normally.

API changes in this revision:

- The ordinary Rust and Python APIs now use the same implementation.
- `add_term` replaces `add_term0`. Rules are registered with `add_rule(lhs, rhs)`
  and run with `run(limit)` in both APIs; register two rules for both directions.
- Recursive insertion-time rewriting, `apply_rules`, `compact`, storage-field
  access, and their compatibility aliases are removed. Use `num_classes()` and
  `node_count()` for counts. Class numbers and match multiplicities are not
  stable across rebuilding.
- The unfinished Rust thinning API is replaced by the scoped API above. The
  unrelated co-egraph, partial-thinning, Prolog, and s-expression experiments
  remain in their source files and are not exposed as Python APIs.
