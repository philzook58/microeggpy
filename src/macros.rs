#[macro_export]
macro_rules! term {
    // Pattern variables are written with a leading `?`, e.g. `term!(?x)`.
    (? $name:ident) => {
        $crate::base::Term::Var(stringify!($name).to_string())
    };

    // Applications are written as `term!(f(...))`. The contents inside the
    // parentheses are parsed by `__term_args!` as a comma-separated term list.
    ($f:ident ( $($args:tt)* )) => {
        $crate::base::Term::App(
            stringify!($f).to_string(),
            $crate::__term_args!($($args)*),
        )
    };

    // A bare identifier is a nullary application, e.g. `term!(a)`.
    ($name:ident) => {
        $crate::base::Term::App(
            stringify!($name).to_string(),
            Vec::new(),
        )
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __term_args {
    // Empty argument list: `term!(f())`.
    () => {
        Vec::new()
    };

    // Parse a variable argument at the front of the list, then recurse on the
    // comma-separated tail if one exists.
    (? $head:ident $(, $($tail:tt)*)? ) => {{
        let mut args = Vec::new();
        args.push($crate::term!(? $head));

        $(
            args.extend($crate::__term_args!($($tail)*));
        )?

        args
    }};

    // Parse an application or nullary application at the front of the list.
    // `$head` is the function/name, and optional `(...)` captures nested args
    // such as `g(?y)`.
    ($head:ident $( ( $($inner:tt)* ) )? $(, $($tail:tt)*)? ) => {{
        let mut args = Vec::new();
        args.push($crate::term!($head $( ( $($inner)* ) )?));

        $(
            args.extend($crate::__term_args!($($tail)*));
        )?

        args
    }};
}

#[macro_export]
macro_rules! rw {
    ($lhs:ident $( ( $($lhs_args:tt)* ) )? => $rhs:ident $( ( $($rhs_args:tt)* ) )?) => {
        (
            $crate::term!($lhs $( ( $($lhs_args)* ) )?),
            $crate::term!($rhs $( ( $($rhs_args)* ) )?),
        )
    };
}

#[macro_export]
macro_rules! rws {
    ($($lhs:ident $( ( $($lhs_args:tt)* ) )? => $rhs:ident $( ( $($rhs_args:tt)* ) )?),* $(,)?) => {
        vec![
            $(
                $crate::rw!($lhs $( ( $($lhs_args)* ) )? => $rhs $( ( $($rhs_args)* ) )?)
            ),*
        ]
    };
}
