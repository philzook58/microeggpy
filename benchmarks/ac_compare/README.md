# AC comparison and loop profile

Measured 2026-11-18 on an AMD Ryzen 7 PRO 7840U, Rust 1.98.0, Linux,
CPU 2 pinned with `taskset`, existing powersave governor. Baseline microeggpy:
`0120430`; lambda-microegg: `48f4fcdf3b295cd7611ed22412be019cafb29989` (clean).
The final variant retains `Vec<bool>` and changes only union-find path shortening
and RHS reuse. No storage experiments or new runtime dependencies are included.

## End-to-end rewriting

Seven interleaved fresh-graph samples per case and engine, after one discarded
warmup each. Times cover bounded saturation (100-round safety limit), excluding
construction, rule registration, validation, extraction, and destruction.
Both engines use identical curried terms, a left-associated input, reversed goal,
and two rules: left-to-right associativity and commutativity. Both must reach the
same expected class and node counts. Atoms have empty thinnings; variable leaves
exercise nonempty dependency masks. No other build/profile ran during timing.

| Leaves | Case | Baseline | Fixed | Lambda | Fixed / lambda |
|---|---|---:|---:|---:|---:|
| Atoms | AC7 | 0.2127 s | 0.1151 s | 0.0280 s | 4.12x |
| Atoms | AC8 | 1.0328 s | 0.4773 s | 0.1018 s | 4.69x |
| Variables | AC9 | 1.3101 s | 0.2583 s | 0.0895 s | 2.89x |
| Variables | AC10 | 5.4277 s | 0.6666 s | 0.1689 s | 3.95x |

Raw samples are in `comparison.csv`. Local timings vary with power management
and system load; these establish the size of the difference, not a universal
performance guarantee. The library still uses the simple matcher and hashing.

## Phase timings

Separate instrumented runs, three samples each; medians below in seconds.
Matching includes target enumeration and retaining matches; application includes
instantiation, union, and match disposal. Rebuilding includes the initial rebuild
and each round's rebuild. These separate-run phase medians should not be added
to reconstruct the interleaved end-to-end medians above.

| Case | Engine | Matching | Applying | Rebuilding |
|---|---|---:|---:|---:|
| Atoms AC8 | Baseline | 0.2865 | 0.9217 | 0.3178 |
| Atoms AC8 | Fixed | 0.1826 | 0.4061 | 0.0939 |
| Atoms AC8 | Lambda | 0.0454 | 0.0627 | 0.0115 |
| Variables AC10 | Baseline | 0.3121 | 4.2905 | 0.3680 |
| Variables AC10 | Fixed | 0.2472 | 0.4319 | 0.0125 |
| Variables AC10 | Lambda | 0.0683 | 0.1233 | 0.0024 |

`phases.csv` also includes variable AC9. Before/after round counts and retained
matches agree: atoms AC8, 8 rounds / 150,248 matches; variables AC9, 7 / 67,705;
variables AC10, 7 / 183,253. The improvement does not skip rewriting work.

## Function profile

Hardware sampling was unavailable (`perf_event_paranoid=4`); Callgrind 3.26.0
provided instruction counts, not sampled wall time. Profiles include the whole
executable, including small setup/validation costs. `functions.txt` groups
exclusive costs across recursive/inlined contexts; percentages are of each
profile's instruction total. Inclusive costs overlap and are not additive.

For variable AC8, total instructions fall from 1,964 million to 482 million
(lambda: 172 million). Lookup (`root` + `root_mut`) falls from 212 to 32 million
self instructions; thinning composition from 795 to 33 million; libc allocation
from 546 to 129 million. The baseline's long union-find walks repeatedly composed
thinnings. Shortening those walks removes most of that work without changing
containers. Cloning the RHS per match was a second avoidable cost; now each
match borrows its RHS from one rule snapshot.

## Reproduce

This separate development crate expects lambda-microegg alongside microeggpy.
It does not add that dependency to the Python package.

```sh
CARGO_TARGET_DIR=/tmp/ac-target cargo build --release --manifest-path benchmarks/ac_compare/Cargo.toml
/tmp/ac-target/release/ac-compare thin atoms 8 7
/tmp/ac-target/release/ac-compare lambda atoms 8 7
/tmp/ac-target/release/ac-compare thin variables 10 7
```

For interleaving, preserve binaries from each checkout/build, then run:

```sh
python3 benchmarks/ac_compare/compare.py --binary baseline=/tmp/baseline-ac --binary fixed=/tmp/fixed-ac --binary lambda=/tmp/fixed-ac --output /tmp/ac.csv
```

Optional phase instrumentation stays out of the library's maintained API:

```sh
git apply --unidiff-zero benchmarks/ac_compare/phase-timing.patch
CARGO_TARGET_DIR=/tmp/ac-profile CARGO_PROFILE_RELEASE_DEBUG=1 cargo build --release --manifest-path benchmarks/ac_compare/Cargo.toml
/tmp/ac-profile/release/ac-compare thin variables 10 3
valgrind --tool=callgrind --callgrind-out-file=/tmp/ac.callgrind /tmp/ac-profile/release/ac-compare thin variables 8
callgrind_annotate --inclusive=no --threshold=100 /tmp/ac.callgrind
git apply --unidiff-zero -R benchmarks/ac_compare/phase-timing.patch
```
