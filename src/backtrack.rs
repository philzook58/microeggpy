/*
Backtracking / Proofs
Write only log? Similar to trail. Enough to undo is also enough to prove.

Wrap base or just copy over

*/

enum Event {
    Union,
    Cong,
    Push,
}

struct EGraph {
    trail: Vec<Event>,
}
