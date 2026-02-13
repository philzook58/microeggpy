use pyo3::prelude::*;

#[pymodule]
mod microeggpy {
    use microegg::Pattern;
    use microegg::{EGraph, Id};
    use pyo3::prelude::*;

    #[pyclass(name = "EGraph", unsendable)]
    #[derive(Default)]
    pub struct PyEGraph {
        inner: EGraph,
    }

    #[pyclass(name = "Pattern", eq, frozen, hash, unsendable)]
    #[derive(Debug, PartialEq, Eq, Hash, Clone)]
    pub struct PyPattern {
        inner: Pattern,
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
    }
}
