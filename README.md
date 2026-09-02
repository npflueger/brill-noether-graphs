# Brill–Noether theory of graphs

This repository formalizes results about chip-firing divisors, Brill–Noether
theory, and divisorial gonality on finite multigraphs in Lean 4. The code herein
has been created primarily with generative AI, and is meant primarily for
experimental purposes, as well as preparation to be added to the [Palomar
registry](https://palomar-registry.org/). This work is ongoing, and new contributions are
welcome!

## Source papers

- [A tropical proof of the Brill--Noether Theorem](https://doi.org/10.1016/j.aim.2012.02.019),
  by F. Cools, J. Draisma, S. Payne, and E. Robeva (2012). The discrete form
  of Theorem 1.1 has been formalized.
- [A note on Brill--Noether existence for graphs of low genus](https://doi.org/10.1307/mmj/1519095622),
  by S. Atanasov and D. Ranganathan (2018). The main low-genus existence
  theorem, for all graphs of genus at most five, has been formalized.
- [Treewidth is a lower bound on graph gonality](https://doi.org/10.5802/alco.124),
  by J. van Dobben de Bruyn and D. Gijswijt (2020). The theorem that treewidth
  is a lower bound for the divisorial gonality of a finite connected graph has
  been formalized.
- [Discrete and metric divisorial gonality can be different](https://doi.org/10.1016/j.jcta.2022.105619),
  by J. van Dobben de Bruyn, H. Smit, and M. van der Wegen (2022). The
  tricycle counterexample has been formalized in its discrete,
  regular-subdivision form; the paper's identification with metric gonality
  has not been formalized.
- [Twice-marked banana graphs & Brill--Noether generality](https://doi.org/10.5802/alco.443),
  by N. Pflueger and N. Solomon (2025). The paper's principal results are
  formalized; formulation and scope differences are documented alongside the
  statements.

## Contents

- `Utilities/` develops reusable graph-divisor infrastructure: rank and
  gonality, graph isomorphisms and contractions, gluing, transmission
  permutations, subdivisions, harmonic maps, and topological types of graphs.
- `Bananas/` formalizes the theory of twice-marked banana and theta graphs,
  including Jacobians and torsion, transmission permutations, wedge and chain
  constructions, and applications to chains of loops and theta graphs.
- `LowGenus/` formalizes the Atanasov–Ranganathan theorem proving
  Brill–Noether existence for connected graphs through genus five.
- `TreewidthGonality/` formalizes Seymour–Thomas bramble/treewidth duality and
  the theorem that treewidth is at most divisorial gonality.
- `Tricycle/` formalizes the tricycle counterexample showing that divisorial
  gonality can drop under regular subdivision.
- `Highlights.lean` and `HighlightsStatements.lean` collect nine headline
  results in proved and Mathlib-only statement forms. `TwiceMarkedBananas.lean`
  and `TwiceMarkedBananasStatements.lean` provide a paper-order proved index
  and standalone statement audit for the paper of Pflueger and Solomon.

## Building

Install [Lean via `elan`](https://lean-lang.org/lean4/doc/setup.html), then run:

```bash
lake update
lake exe cache get
lake build
```

The default build checks the principal libraries and proved indexes. Individual
libraries can also be checked with, for example, `lake build LowGenus` or
`lake build TreewidthGonality`.

## Statement verification

On Linux, with Git, Go, Rust/Cargo, and Python 3 installed, run:

```bash
./scripts/verify-comparator.sh
```

This checks both statement/solution pairs with pinned versions of Comparator,
`lean4export`, Landrun, and NanoDa. GitHub Actions runs the same check on pushes
and pull requests to `main`.

## License

The repository is licensed under the [Apache License 2.0](LICENSE). Quoted and
adapted source material is identified in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md);
dependencies and cited mathematical sources retain their own licenses.
