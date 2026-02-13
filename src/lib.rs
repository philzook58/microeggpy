use pyo3::prelude::*;

#[pymodule]
mod microeggpy {
    use microegg::Pattern;
    use microegg::{EGraph, Id};
    use pyo3::prelude::*;
    use std::collections::HashMap;

    #[pyclass(name = "EGraph", unsendable)]
    #[derive(Default)]
    pub struct PyEGraph {
        inner: EGraph,
    }

    #[pyclass(name = "Term", eq, frozen, hash, unsendable)]
    #[derive(PartialEq, Eq, Hash, Clone, Debug)]
    pub enum PyTerm {
        Var(String),
        App(String, Vec<PyTerm>),
    }

    impl From<PyTerm> for Pattern {
        fn from(term: PyTerm) -> Self {
            match term {
                PyTerm::Var(name) => Pattern::Var(name.into()),
                PyTerm::App(f, args) => {
                    Pattern::App(f.into(), args.into_iter().map(Pattern::from).collect())
                }
            }
        }
    }

    impl From<Pattern> for PyTerm {
        fn from(pat: Pattern) -> Self {
            match pat {
                Pattern::Var(name) => PyTerm::Var(name.to_string()),
                Pattern::App(f, args) => {
                    PyTerm::App(f.to_string(), args.into_iter().map(Pattern::into).collect())
                }
            }
        }
    }

    #[pymethods]
    impl PyEGraph {
        #[new]
        pub fn new() -> Self {
            Self::default()
        }

        pub fn add(&mut self, f: String, args: Vec<Id>) -> Id {
            self.inner.add(f, args)
        }

        pub fn union(&mut self, a: Id, b: Id) {
            self.inner.union(a, b);
        }

        pub fn find(&self, a: Id) -> Id {
            self.inner.find(a)
        }

        pub fn is_eq(&self, a: Id, b: Id) -> bool {
            self.inner.is_eq(a, b)
        }

        pub fn rebuild(&mut self) {
            self.inner.rebuild();
        }

        pub fn __repr__(&self) -> String {
            format!("EGraph with {} nodes", self.inner.nodes.len())
        }

        pub fn ematch(&self, pat: PyTerm, class: Id) -> Vec<HashMap<String, Id>> {
            let pat: Pattern = pat.into();
            self.inner
                .ematch(&pat, class)
                .into_iter()
                .map(|subst| {
                    subst
                        .into_iter()
                        .map(|(name, id)| (name.to_string(), id))
                        .collect::<HashMap<String, Id>>()
                })
                .collect()
        }
    }

    #[pymethods]
    impl PyTerm {
        pub fn __repr__(&self) -> String {
            format!("{self:?}")
        }
    }

    /*
        Next steps:
        Maybe rebuild should just return a new egraph anyhow
        Aegraph?
        extraction
        iteration or dictionary serialization
        If I inlined there'd be less duplication


    */
}
