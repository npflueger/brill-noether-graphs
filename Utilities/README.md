# Utilities

Shared Lean 4 infrastructure for divisor theory (chip-firing) on finite
multigraphs, with an emphasis on the two-marked *transmission* framework.
This library is self-contained over Mathlib plus two small pinned dependencies
([chip-firing-with-lean](https://github.com/DhyeyMavani2003/chip-firing-with-lean),
[demazure](https://github.com/npflueger/demazure)).

Build with `lake build Utilities`.

This is the bottom of the repository's stack: it imports nothing else from the
repository, and every other library sits on top of it. Reusable theory belongs
here; application-specific developments live in their respective top-level
libraries, such as `TreewidthGonality/` and `Tricycle/`.

## Layout

- **Foundations/** — `CFGraph` parameters and Brill–Noether vocabulary
  (`bnNumber`, `BNExists`), rank facts (`RankOne`, `RankInvariance`,
  `RankChipStep`), Riemann–Roch winnability, duality, effective differences,
  canonical slack-pair divisors, induced subgraphs, the `CFGraph → SimpleGraph`
  bridge, edge addition.
- **Iso/** — graph isomorphisms (`CFGraphIso`) and graph contractions with
  their Euler/topology/fibre-tree theory.
- **Gluing/** — bridge and vertex-wedge constructors, bridge divisors and
  rank-one gluing, the wedge rank formula, genus-three/cycle rank-one gluing,
  one-vertex cuts and their factor inheritance, cycle and
  two-edge-connected rigidity, iterated chain gluing.
- **Transmission/** — the transmission-locus framework for twice-marked
  graphs: the defining predicate, finite-corner reduction, shifts, duality,
  existence, Riemann–Roch and Brill–Noether interfaces, wedge gluing (with
  Demazure-product composition), marked rank profiles.
- **Grassmannian/** — the dictionary between Grassmannian ASP permutations /
  Young diagrams and once-marked Brill–Noether statements.
- **Harmonic/** — indexed harmonic-map certificates, fibre divisors, pullback
  of divisors and scripts, and rank/transmission inequalities under pullback.
- **Segments/** — firing-potential calculus on subdivided segments: seam
  displacement, segment reflection, the Atanasov–Ranganathan local
  configurations (the graph-independent pictures; the genus-five programme that
  consumes them lives in `LowGenus/`), two-chip reflection machinery.
- **Subdivision/** — the "positive subdivision of an ordered core" model:
  the `Spec` graph construction, separators, connectivity, cut counting,
  Laplacian equivalences, relabelings/reindexing, explicit-potential and
  affine-positioned moving-chip and multi-break rank-one certificates, compact
  affine wall-decision covers, checked core bridge and rigid-cycle cuts, linear spanning-tree
  connectivity witnesses, ordered path refinements (including deletion
  of zero source segments before canonical splitting), leaf reduction, and
  the endpoint pencil.
- **Gonality/** — the generic divisorial gonality API: the `Nat.sInf`
  definition and its attainment, legal firings and the nested legal chain to a
  `q`-reduced divisor, the maximal legal ("burned") set that replaces Dhar's
  algorithm, the linear non-existence certificate, transport of gonality along
  subdivision and relabelling, and the orientation model at degree `g-1`.
  The two applications built on it — `treewidth <= gonality` and the
  discrete/metric gap — live in `TreewidthGonality/` and `Tricycle/`.
- **Pseudocore/** — loop-aware pseudocores: the validity API, split-metadata
  compatibility, the genus-generic bivalent-path presentation engine, and
  marker cut/wedge packaging.

## Namespace

Most declarations live under `Utilities.*`. Some reusable APIs retain the
`Certificate.*` or `MarkedGraphs.*` namespaces for compatibility. Namespace
spelling does not indicate a dependency on code outside this repository; module
imports determine the dependency boundary. A few declarations in `LowGenus/`
likewise use the `Utilities` namespace.
