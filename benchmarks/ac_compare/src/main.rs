use lambda_microegg::{EGraph as Lambda, Pattern, Rewrite};
use microegg::thin::{EGraph, Id, Term};
use std::hint::black_box;
use std::time::Instant;

fn plus(a: Term, b: Term) -> Term {
    Term::app(Term::app(Term::atom("+".into()), a), b)
}
fn add(g: &mut EGraph, a: &Id, b: &Id) -> Id {
    let op = g.atom("+", a.ctx());
    let partial = g.app(&op, a).unwrap();
    g.app(&partial, b).unwrap()
}
fn thin_case(n: usize, variables: bool) -> (EGraph, Id, Id) {
    let mut g = EGraph::new();
    let leaves: Vec<_> = (0..n)
        .map(|i| {
            if variables {
                g.var(n, i).unwrap()
            } else {
                g.atom(&format!("x{i}"), 0)
            }
        })
        .collect();
    let mut input = leaves[0].clone();
    for x in &leaves[1..] {
        input = add(&mut g, &input, x);
    }
    let mut goal = leaves[n - 1].clone();
    for x in leaves[..n - 1].iter().rev() {
        goal = add(&mut g, &goal, x);
    }
    let var = |s: &str| Term::meta(s.into(), vec![]);
    g.add_rule(
        plus(plus(var("a"), var("b")), var("c")),
        plus(var("a"), plus(var("b"), var("c"))),
    )
    .unwrap();
    g.add_rule(plus(var("a"), var("b")), plus(var("b"), var("a")))
        .unwrap();
    (g, input, goal)
}
fn lambda_case(
    n: usize,
    variables: bool,
) -> (
    Lambda,
    lambda_microegg::Id,
    lambda_microegg::Id,
    Vec<Rewrite>,
) {
    let mut g = Lambda::new();
    let leaves: Vec<_> = (0..n)
        .map(|i| {
            if variables {
                g.var(n, i)
            } else {
                g.atom(&format!("x{i}"), 0)
            }
        })
        .collect();
    let mut input = leaves[0];
    for x in &leaves[1..] {
        input = g.apps("+", vec![input, *x]);
    }
    let mut goal = leaves[n - 1];
    for x in leaves[..n - 1].iter().rev() {
        goal = g.apps("+", vec![goal, *x]);
    }
    let var = Pattern::meta;
    let plus = |a, b| Pattern::apps("+", vec![a, b]);
    let rules = vec![
        Rewrite::new(
            plus(plus(var("a"), var("b")), var("c")),
            plus(var("a"), plus(var("b"), var("c"))),
        )
        .unwrap(),
        Rewrite::new(plus(var("a"), var("b")), plus(var("b"), var("a"))).unwrap(),
    ];
    (g, input, goal, rules)
}
fn main() {
    let args: Vec<_> = std::env::args().collect();
    let engine = &args[1];
    let variables = args[2] == "variables";
    let n: usize = args[3].parse().unwrap();
    let repeats: usize = args.get(4).map(|s| s.parse().unwrap()).unwrap_or(1);
    for _ in 0..repeats {
        let (seconds, classes, nodes) = match engine.as_str() {
            "thin" => {
                let (mut g, input, goal) = thin_case(n, variables);
                let start = Instant::now();
                let rounds = g.run(100);
                let seconds = start.elapsed().as_secs_f64();
                assert!(rounds < 100, "did not saturate");
                assert!(g.is_eq(&input, &goal).unwrap());
                (seconds, g.num_classes(), g.node_count())
            }
            "lambda" => {
                let (mut g, input, goal, rules) = lambda_case(n, variables);
                let start = Instant::now();
                let stats = g.run(&rules, 100);
                let seconds = start.elapsed().as_secs_f64();
                eprintln!(
                    "phase,lambda,{:.9},{:.9},{:.9},{}",
                    stats.match_time.as_secs_f64(),
                    stats.apply_time.as_secs_f64(),
                    stats.rebuild_time.as_secs_f64(),
                    stats.rounds + 1
                );
                assert!(stats.rounds < 100, "did not saturate");
                assert!(g.equivalent(&input, &goal));
                (seconds, g.class_count(), g.node_count())
            }
            _ => panic!("engine must be thin or lambda"),
        };
        let expected_classes = if variables { 2 * n } else { 2 * (1 << n) - 2 };
        let expected_nodes = if variables {
            (1 << (n + 1)) - n - 1
        } else {
            3usize.pow(n as u32) - (1 << n) + n
        };
        assert_eq!(classes, expected_classes);
        assert_eq!(nodes, expected_nodes);
        black_box((classes, nodes));
        println!("{engine},{},{n},{seconds:.9},{classes},{nodes}", args[2]);
    }
}
