# Brill–Noether theory of graphs

This repository formalizes results about combinatorial Brill–Noether theory and
gonality of finite multigraphs in Lean 4. The code herein has been created
primarily with generative AI. It is meant for experimental purposes, as well as
preparation to be added to the [Palomar
registry](https://palomar-registry.org/). This work is ongoing, and new
contributions are welcome!

## Dependencies

These formalizations build upon [Mathlib](github.com/leanprover-community/mathlib4) and the following two repositories.

* [Chip-firing with Lean4](github.com/DhyeyMavani2003), developed by Dhyey Mavani and Nathan Pflueger. This provides the basic notions of divisor theory on graphs, including the Riemann--Roch theorem.
* [Demazure products](github.com/npflueger/demazure), developed by Nathan Pflueger. This provides the theory of Demazure products on integer permutations, needed for vertex gluing arguments.


## Source papers

- [A tropical proof of the Brill--Noether Theorem](https://doi.org/10.1016/j.aim.2012.02.019),
  by F. Cools, J. Draisma, S. Payne, and E. Robeva (2012). The finite-graph case
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
- [Catalan-many tropical morphisms to trees; Part I: Constructions](https://arxiv.org/abs/1909.12924),
  by J. Draisma and A. Vargas (2019). The main theorem, that a graph of genus `g`
  has gonality at most `⌈g/2⌉ + 1`, has been formalized in its discrete,
  regular-subdivision form; its identification with metric gonality has not
  been formalized. In even genus the construction follows the route of Part II
  below.
- [Catalan-many tropical morphisms to trees; Part II: A space and a count](https://arxiv.org/abs/2609.09109),
  by A. Vargas (2026). Its walk through the space of metric graphs by Whitehead
  moves is used in the proof of Part I here, and its count of tropical
  morphisms to trees has been formalized modulo 2 in genus six, as far as needed
  for Brill–Noether existence in genus six.
- [Twice-marked banana graphs & Brill--Noether generality](https://doi.org/10.5802/alco.443),
  by N. Pflueger and N. Solomon (2025). The paper's principal results are
  formalized; formulation and scope differences are documented alongside the
  statements.

## Palomar entries

`Palomar/BNChains/` is a complete entry: a Mathlib-only challenge, its solution,
a comparator configuration and formalization metadata. `Palomar/GenusSix/`
(Brill–Noether existence through genus six, and once-marked existence through
genus five) has its challenge, its solution `Palomar/Solutions/GenusSix.lean` and
a comparator configuration; its formalization metadata is a draft.
`Palomar/SubdivisionGonality/` (the Draisma–Vargas bound on gonality up to
subdivision) is a draft: it states the theorems over a Mathlib-only vocabulary,
and its solution is still to be written.

## Contents

- `Utilities/` develops reusable graph-divisor infrastructure: rank and
  gonality, graph isomorphisms and contractions, gluing, transmission
  permutations, subdivisions, harmonic maps, and topological types of graphs.
  It also defines the discrete Brill–Noether rank `w^r_d` of Lim–Payne–Potashnik
  and Len (`Utilities/Foundations/BrillNoetherRank.lean`) and proves that it
  descends along odd regular subdivisions when two residual chips are involved
  (`Utilities/Subdivision/OddSubdivisionDescent.lean`): for every finite
  loopless multigraph `G`, if some odd regular subdivision of `G` has
  `w^1_4 ≥ 1`, then so does `G`.
- `Bananas/` formalizes the theory of twice-marked banana and theta graphs,
  including Jacobians and torsion, transmission permutations, wedge and chain
  constructions, and applications to chains of loops and theta graphs.
- `LowGenus/` formalizes the Atanasov–Ranganathan theorem proving
  Brill–Noether existence for connected graphs through genus five.
- `TreewidthGonality/` formalizes Seymour–Thomas bramble/treewidth duality and
  the theorem that treewidth is at most divisorial gonality.
- `Tricycle/` formalizes the tricycle counterexample showing that divisorial
  gonality can drop under regular subdivision.
- `GenusSixOddDescent/` formalizes odd-subdivision descent for genus-six
  graphs: a divisor of degree four and rank at least one on an odd regular
  subdivision of a bridgeless connected genus-six graph descends to the graph
  itself. It derives a conditional theorem: every connected genus-six graph
  satisfies Brill–Noether existence, provided each has such a divisor on some
  odd regular subdivision, a hypothesis supplied by the Draisma–Vargas count
  of `DraismaVargasCount`.
- `DraismaVargas/` formalizes the Draisma–Vargas bound in divisorial form: every
  connected finite graph of genus `g` has a regular subdivision carrying a
  divisor of degree `⌈g/2⌉ + 1` and rank at least one, and the same holds for
  graphs with positive integer edge lengths.
- `DraismaVargasCount/` proves that every connected graph of genus six has a
  regular subdivision of odd order carrying a divisor of degree four and rank
  at least one, by a mod-2 form of the Draisma–Vargas count of tropical
  morphisms to trees. Together with `GenusSixOddDescent` this gives
  Brill–Noether existence in genus six.
- `GenusSixExistence/` proves Brill–Noether existence for every connected graph
  of genus six, and hence through genus six, extending the Atanasov–Ranganathan
  theorem of `LowGenus`. It also deduces once-marked Brill–Noether existence at
  every vertex of every connected graph of genus at most five.
- `Highlights.lean` and `HighlightsStatements.lean` collect ten headline
  results in proved and Mathlib-only statement forms. `TwiceMarkedBananas.lean`
  and `TwiceMarkedBananasStatements.lean` provide a paper-order proved index
  and standalone statement audit for the paper of Pflueger and Solomon.

Genus-five rows 01, 02, 03, 04, 07, and 13 share the canonical two-pole construction in
[`LowGenus/GenusFiveTwoPole.lean`](LowGenus/GenusFiveTwoPole.lean).
It glues two genus-two canonical pencils by clamping firing scripts and
bending one connector potential when needed. Integer rounding then extends
the fixed core divisor over all permitted zero-length contraction faces in
[`GenusFiveTwoPoleClosed`](LowGenus/GenusFiveTwoPoleClosed.lean). See the
[proof and implementation note](Research/unmarked-genus-five-two-pole-proof.md).
The [proof comparison](Research/genus-five-proof-comparison.md) records the
source-size and compile-time measurements supporting replacement of the six
old proofs.

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

For work on the shared two-pole proof and its contraction closure, check their target with four
Lean threads:

```bash
LEAN_NUM_THREADS=4 lake build LowGenus.GenusFiveTwoPoleClosed
```

After changing its integration or the library roots, check both affected
libraries:

```bash
LEAN_NUM_THREADS=4 lake build Utilities LowGenus
```

## Statement verification

On Linux, with Git, Go, Rust/Cargo, and Python 3 installed, run:

```bash
./scripts/verify-comparator.sh
```

This checks all statement/solution pairs with pinned versions of Comparator,
`lean4export`, Landrun, and NanoDa. GitHub Actions runs the same check on pushes
and pull requests to `main`. Pass config paths to check only those pairs, for
example `./scripts/verify-comparator.sh Palomar/GenusSix/comparator.json`.

On macOS, where Landrun cannot run, set `PALOMAR_FAKE_LANDRUN=1` to replace it
with Comparator's development shim, which runs the build and export steps
without a sandbox; Go is then not needed:

```bash
PALOMAR_FAKE_LANDRUN=1 ./scripts/verify-comparator.sh Palomar/GenusSix/comparator.json
```

The statement, axiom and kernel checks are the same, so this is a useful check
before submission, but it is weaker evidence than the sandboxed run in CI.

## License

The repository is licensed under the [Apache License 2.0](LICENSE). Quoted and
adapted source material is identified in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md);
dependencies and cited mathematical sources retain their own licenses.
