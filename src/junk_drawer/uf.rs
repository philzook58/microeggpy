trait UF {
    type Id;
    fn makeset(&mut self) -> Self::Id;
    fn find(&self, id: Self::Id) -> Self::Id;
    fn union(&mut self, id1: Self::Id, id2: Self::Id);
}

trait Group {
    fn mul(&self, a: &Self) -> Self;
    fn inv(&self) -> Self;
    fn id() -> Self;
}

trait SemiLattice {}
