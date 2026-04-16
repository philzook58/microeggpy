use criterion::{Criterion, criterion_group, criterion_main};
use microegg::base::{EGraph, Term};
use microegg::rws;
use std::hint::black_box;

fn ac(n: usize) {
    let mut g = EGraph::default();
    let mut acc = g.app(&0.to_string(), vec![]);
    for i in 1..n {
        let x = g.app(&i.to_string(), vec![]);
        acc = g.app("add", vec![acc, x]);
    }
    //let rules = vec![
    //    (Term::App("+".into(), vec![Term::Var("x".into()), Term::Var("y".into())]), Term::App("+".into(), vec![Term::Var("x".into()), Term::Var("y".into())]))
    //]
    let _rules: Vec<(Term, Term)> = rws![
        add(?x, ?y) => add(?y, ?x),
        add(add(?x, ?y),?z) => add(?x, add(?y, ?z)),
        add(?x, add(?y, ?z)) => add(add(?x, ?y),?z),
    ];
    g.run(&_rules, n);
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function(" ac3", |b| b.iter(|| ac(black_box(4))));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
