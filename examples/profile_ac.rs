use microegg::base::{EGraph, Term};
use microegg::rws;
use std::hint::black_box;
use std::time::Instant;

fn main() {
    let n = 5;
    let start = Instant::now();
    let mut g = EGraph::default();
    let mut acc = g.app(&0.to_string(), vec![]);
    for i in 1..n {
        let x = g.app(&i.to_string(), vec![]);
        acc = g.app("add", vec![acc, x]);
    }
    black_box(acc);
    println!(
        "graph construction: {:?}, nodes={}",
        start.elapsed(),
        g.nodes.len()
    );

    let start = Instant::now();
    let rules: Vec<(Term, Term)> = rws![
        add(?x, ?y) => add(?y, ?x),
        add(add(?x, ?y), ?z) => add(?x, add(?y, ?z)),
        add(?x, add(?y, ?z)) => add(add(?x, ?y), ?z),
    ];
    println!("rule construction: {:?}", start.elapsed());

    for i in 0..(n - 1) {
        let mut ematch_time = std::time::Duration::default();
        let mut add_union_time = std::time::Duration::default();
        let mut match_count = 0usize;
        let classes_before = g.uf.len();
        for eclass in 0..g.uf.len() {
            for (lhs, rhs) in &rules {
                let start = Instant::now();
                let matches = g.ematch(lhs, eclass);
                ematch_time += start.elapsed();
                match_count += matches.len();

                let start = Instant::now();
                for subst in matches {
                    let new_id = g.add_term(rhs, &subst);
                    g.union(eclass, new_id);
                }
                add_union_time += start.elapsed();
            }
        }
        println!(
            "iteration {i}: apply_rules {:?} (ematch {:?}, add+union {:?}, matches {}), nodes {} -> {}",
            ematch_time + add_union_time,
            ematch_time,
            add_union_time,
            match_count,
            classes_before,
            g.nodes.len()
        );

        let start = Instant::now();
        //g.rebuild();
        g = g.compact();
        println!(
            "iteration {i}: rebuild {:?}, nodes={}",
            start.elapsed(),
            g.nodes.len()
        );
    }
    println!("actual classes {}", g.num_classes());
    println!("expected eclasses {}", 2_i64.pow(n) - 1);
    let enodes: i64 = 3_i64.pow(n) + -(2_i64.pow(n + 1)) + 1 + (n as i64);
    println!("total expected enodes {}", enodes);
    //println!("{:?}", g);
    black_box(g);
}
