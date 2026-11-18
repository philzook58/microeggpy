use criterion::{Criterion, criterion_group, criterion_main};
use microegg::base::{EGraph, Term};
use microegg::rws;
use std::hint::black_box;

fn ac(n: usize) {
    let mut g = EGraph::default();
    let mut acc = g.add(&0.to_string(), vec![]).unwrap();
    for i in 1..n {
        let x = g.add(&i.to_string(), vec![]).unwrap();
        acc = g.add("add", vec![acc, x]).unwrap();
    }
    //let rules = vec![
    //    (Term::App("+".into(), vec![Term::Var("x".into()), Term::Var("y".into())]), Term::App("+".into(), vec![Term::Var("x".into()), Term::Var("y".into())]))
    //]
    let _rules: Vec<(Term, Term)> = rws![
        add(?x, ?y) => add(?y, ?x),
        add(add(?x, ?y),?z) => add(?x, add(?y, ?z)),
        add(?x, add(?y, ?z)) => add(add(?x, ?y),?z),
    ];
    for (lhs, rhs) in _rules {
        g.add_rule(lhs, rhs).unwrap();
    }
    g.run(n);
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function(" ac3", |b| b.iter(|| ac(black_box(4))));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
