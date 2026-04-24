use std::collections::HashMap;
use std::iter::zip;
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct PThin {
    thin: Vec<bool>,
    wide: Vec<bool>,
}

impl PThin {
    pub fn new(thin: Vec<bool>, wide: Vec<bool>) -> Self {
        let pthin = Self { thin, wide };
        assert!(pthin.valid(), "invalid partial thinning");
        pthin
    }

    pub fn id(n: usize) -> Self {
        Self {
            thin: vec![true; n],
            wide: vec![true; n],
        }
    }

    pub fn thin(thin: Vec<bool>) -> Self {
        let cod = thin.iter().filter(|&&b| b).count();
        Self {
            thin,
            wide: vec![true; cod],
        }
    }

    pub fn select(ctx: usize, n: usize) -> Self {
        assert!(ctx > n);
        let mut t = vec![false; ctx];
        t[n] = true;
        Self::thin(t)
    }

    pub fn empty(dom: usize, cod: usize) -> Self {
        PThin {
            thin: vec![false; dom],
            wide: vec![false; cod],
        }
    }

    pub fn wide(wide: Vec<bool>) -> Self {
        let dom = wide.iter().filter(|&&b| b).count();
        Self {
            thin: vec![true; dom],
            wide,
        }
    }

    pub fn proj(bits: Vec<bool>) -> Self {
        Self::new(bits.clone(), bits)
    }

    pub fn pinv(&self) -> Self {
        Self {
            thin: self.wide.clone(),
            wide: self.thin.clone(),
        }
    }

    pub fn dom(&self) -> usize {
        self.thin.len()
    }

    pub fn cod(&self) -> usize {
        self.wide.len()
    }

    pub fn is_id(&self) -> bool {
        assert!(self.valid());
        self.is_proj() && self.thin.iter().all(|b| *b)
    }
    pub fn is_proj(&self) -> bool {
        assert!(self.valid());
        self.cod() == self.dom()
    }

    pub fn valid(&self) -> bool {
        self.thin.iter().filter(|&&b| b).count() == self.wide.iter().filter(|&&b| b).count()
    }

    pub fn thin_bits(&self) -> &[bool] {
        &self.thin
    }

    pub fn wide_bits(&self) -> &[bool] {
        &self.wide
    }

    pub fn comp(&self, other: &Self) -> Self {
        assert!(self.valid(), "left operand is invalid");
        assert!(other.valid(), "right operand is invalid");
        assert_eq!(self.cod(), other.dom(), "partial thinning cod/dom mismatch");

        let self_wide_true_positions = self
            .wide
            .iter()
            .enumerate()
            .filter_map(|(i, &b)| b.then_some(i))
            .collect::<Vec<_>>();
        let other_wide_true_positions = other
            .wide
            .iter()
            .enumerate()
            .filter_map(|(i, &b)| b.then_some(i))
            .collect::<Vec<_>>();

        let mut other_thin_true_rank = vec![None; other.thin.len()];
        let mut rank = 0usize;
        for (i, &b) in other.thin.iter().enumerate() {
            if b {
                other_thin_true_rank[i] = Some(rank);
                rank += 1;
            }
        }

        let mut thin_out = vec![false; self.thin.len()];
        let mut wide_out = vec![false; other.wide.len()];
        let mut self_true_rank = 0usize;

        for (src_idx, &keep_src) in self.thin.iter().enumerate() {
            if !keep_src {
                continue;
            }

            let mid_idx = self_wide_true_positions[self_true_rank];
            if let Some(other_rank) = other_thin_true_rank[mid_idx] {
                thin_out[src_idx] = true;
                let dst_idx = other_wide_true_positions[other_rank];
                wide_out[dst_idx] = true;
            }
            self_true_rank += 1;
        }

        let out = Self {
            thin: thin_out,
            wide: wide_out,
        };
        assert!(out.valid(), "composition produced invalid partial thinning");
        out
    }
    pub fn join(&self, other: &PThin) -> (PThin, PThin, PThin) {
        // Maybe mutate both? And output the common
        debug_assert_eq!(self.dom(), other.dom());
        let mut prefix = Vec::with_capacity(self.dom());
        let mut proj_self = vec![];
        let mut proj_other = vec![];
        for (&a, &b) in zip(self.thin.iter(), other.thin.iter()) {
            prefix.push(a || b);
            if a || b {
                proj_self.push(a);
                proj_other.push(b);
            }
        }
        (
            PThin::thin(prefix),
            PThin {
                thin: proj_self,
                wide: self.wide.clone(),
            },
            PThin {
                thin: proj_other,
                wide: other.wide.clone(),
            },
        )
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Id {
    pthin: PThin,
    rawid: usize,
}

impl Id {
    pub fn ctx(&self) -> usize {
        self.pthin.dom()
    }
    pub fn weaken(&mut self, thin: &PThin) {
        self.pthin = thin.comp(&self.pthin);
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Node {
    App(Id, Id),
    Var,
    Lit(String),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EGraph {
    memo: HashMap<Node, Id>,
    nodes: Vec<Node>,
    uf: Vec<Id>,
}

pub fn var(ctx: usize, n: usize) -> Id {
    assert!(ctx > n, "variable id must be less than context size");
    Id {
        pthin: PThin::select(ctx, n),
        rawid: 0,
    }
}

impl EGraph {
    pub fn new() -> Self {
        let mut memo = HashMap::new();
        let id = var(1, 0);
        memo.insert(Node::Var, id.clone());
        EGraph {
            memo,
            nodes: vec![Node::Var],
            uf: vec![id],
        }
    }
    fn add_node(&mut self, ctx: usize, n: Node) -> Id {
        if let Some(id) = self.memo.get(&n) {
            self.find(id)
        } else {
            let id = Id {
                pthin: PThin::id(ctx),
                rawid: self.uf.len(),
            };
            self.uf.push(id.clone());
            self.nodes.push(n.clone());
            self.memo.insert(n, id.clone());
            id
        }
    }
    pub fn find(&self, id: &Id) -> Id {
        let Id {
            mut pthin,
            mut rawid,
        } = id.clone();
        loop {
            let Id {
                pthin: thin1,
                rawid: rawid1,
            } = self.uf[rawid].clone();
            pthin = pthin.comp(&thin1);
            if rawid1 == rawid {
                assert!(thin1.is_proj());
                return Id { pthin, rawid };
            } else {
                rawid = rawid1;
            }
        }
    }
    pub fn lit(&mut self, ctx: usize, s: impl AsRef<str>) -> Id {
        let mut id = self.add_node(0, Node::Lit(s.as_ref().to_owned()));
        id.weaken(&PThin::empty(ctx, 0));
        id
    }

    pub fn app(&mut self, f: &Id, x: &Id) -> Id {
        assert_eq!(f.ctx(), x.ctx());
        let f = self.find(f);
        let x = self.find(x);
        let (common, thinf, thinx) = PThin::join(&f.pthin, &x.pthin);
        let mut id = self.add_node(
            common.cod(),
            Node::App(
                Id {
                    pthin: thinf,
                    rawid: f.rawid,
                },
                Id {
                    pthin: thinx,
                    rawid: x.rawid,
                },
            ),
        );
        id.weaken(&common);
        id
    }

    fn union(&mut self, a: &Id, b: &Id) -> bool {
        assert_eq!(a.ctx(), b.ctx(), "Can only union ids in the same context");
        let a = self.find(a);
        let b = self.find(b);
        if a == b {
            false
        } else {
            // Update b with new projection
            let bproj = b
                .pthin
                .pinv()
                .comp(&a.pthin.comp(&a.pthin.pinv().comp(&b.pthin)));
            assert!(bproj.is_proj() && bproj.dom() == b.pthin.cod());
            self.uf[b.rawid] = Id {
                pthin: bproj,
                rawid: b.rawid,
            };
            self.uf[a.rawid] = Id {
                pthin: a.pthin.pinv().comp(&b.pthin),
                rawid: b.rawid,
            };
            true
        }
    }
}

#[cfg(test)]
mod tests {
    use super::PThin;
    use super::*;

    #[test]
    fn test_egraph() {
        let mut g = EGraph::new();
        let mut a = g.lit(0, "a");
        let a1 = g.lit(0, "a");
        assert_eq!(a, a1);
        let aa = g.app(&a, &a);
        assert_eq!(aa.ctx(), 0);

        a.weaken(&PThin::empty(1, 0));
        let v = var(1, 0);
        let av = g.app(&a, &v);

        let v1 = var(2, 0);
        let a = g.lit(2, "a");
        let av1 = g.app(&a, &v1);
        assert_eq!(
            av1.rawid, av.rawid,
            "in different context, still should refer to same interned rawid"
        );
    }
    #[test]
    fn union_test() {
        let mut g = EGraph::new();
        let v0 = var(2, 0);
        let v1 = var(2, 1);
        assert_eq!(v0, g.find(&v0));
        assert_eq!(v1, g.find(&v1));
        let a = g.lit(2, "a");

        let av0 = g.app(&a, &v0);
        let av1 = g.app(&a, &v1);
        assert_eq!(av0.rawid, av1.rawid);
        g.union(&av0, &av1); // We are determining a tosses it's arugment
        assert_eq!(g.find(&av0), g.find(&av1));
        assert_eq!(g.find(&av0).ctx(), 2);
        //assert_eq!(g.find(&av0).pthin.wide.len(), 2);
        assert_eq!(g.uf[av0.rawid].pthin, PThin::empty(1, 1));
    }

    #[test]
    fn python_reference_examples() {
        assert_eq!(PThin::select(2, 1).comp(&PThin::id(1)), PThin::select(2, 1));
        assert_eq!(PThin::id(2).comp(&PThin::id(2)), PThin::id(2));

        let thin = PThin::thin(vec![true, false]);
        assert_eq!(thin, PThin::new(vec![true, false], vec![true]));
        assert_eq!(PThin::id(2).comp(&thin), thin);
        assert_eq!(thin.comp(&PThin::id(1)), thin);

        let wide = PThin::wide(vec![true, false]);
        assert_eq!(wide.comp(&PThin::id(2)), wide);
        assert_eq!(PThin::id(1).comp(&wide), wide);
        assert_eq!(wide.comp(&wide.pinv()), PThin::id(1));

        assert_eq!(thin.pinv().comp(&thin), PThin::id(1));
        assert_eq!(thin.comp(&thin.pinv()), PThin::proj(vec![true, false]));

        assert_eq!(
            PThin::proj(vec![true, false]).comp(&PThin::proj(vec![false, true])),
            PThin::proj(vec![false, false])
        );
    }

    #[test]
    fn comp_keeps_late_selected_slot() {
        assert_eq!(PThin::select(2, 1).comp(&PThin::id(1)), PThin::select(2, 1));
    }
}
