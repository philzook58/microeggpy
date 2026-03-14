trait UF {
    type Id;
    fn makeset(&mut self) -> Self::Id; // take in extra data?
    fn find(&self, id: Self::Id) -> Self::Id;
    fn union(&mut self, id1: Self::Id, id2: Self::Id);
}

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
