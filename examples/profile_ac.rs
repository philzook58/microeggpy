use microegg::base::EGraph;
use microegg::rws;
use std::time::Instant;

fn main() {
    let n = 5;
    let start = Instant::now();
    let mut g = EGraph::new();
    let mut acc = g.add("0", vec![]).unwrap();
    for i in 1..n {
        let x = g.add(&i.to_string(), vec![]).unwrap();
        acc = g.add("add", vec![acc, x]).unwrap();
    }
    for (lhs, rhs) in rws![
        add(?x, ?y) => add(?y, ?x),
        add(add(?x, ?y), ?z) => add(?x, add(?y, ?z)),
        add(?x, add(?y, ?z)) => add(add(?x, ?y), ?z),
    ] {
        g.add_rule(lhs, rhs).unwrap();
    }
    g.run(10);
    assert_eq!(g.num_classes(), (1 << n) - 1);
    println!(
        "{:?}: {} classes, {} nodes",
        start.elapsed(),
        g.num_classes(),
        g.node_count()
    );
    println!("{:?}", g.extract(acc).unwrap());
}
