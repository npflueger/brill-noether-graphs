# Twice-marked banana graphs

This directory formalizes results from *Twice-marked banana graphs &
Brill--Noether generality*. The paper-order index is
`../TwiceMarkedBananas.lean`; `FORMALIZATION_NOTES.md` records formulation and
scope differences made explicit by the formalization.

The Lean sources are grouped by mathematical topic:

- `Basics/` defines banana graphs and their marked geometry.
- `Jacobian/` develops the Jacobian presentation and torsion slopes.
- `Transmission/` contains transmission permutations, rank witnesses, and
  chain arithmetic.
- `SameStrand/` and `CrossOneOff/` analyze the principal marking regimes.
- `Theta/` gives the exact genus-two theory.
- `Wedge/` treats vertex sums and transmission under gluing.
- `Classification/` contains the low-genus structural results.
- `Sections/` assembles the statements from Sections 5 and 6 of the paper.
- `Examples/` contains worked examples and API audits.
- `ChainOfLoops/` applies the Section 6 chain theorems to a named result in the
  tropical Brill--Noether literature: Cools--Draisma--Payne--Robeva
  nonexistence (arXiv:1001.2774, Theorem 1.1), in discrete form. Its
  kernel-checked restatement file is `ChainOfLoops/Highlights.lean`.

The library depends only on `Utilities` and the pinned external
dependencies.  Build the complete paper library with

```bash
lake build Bananas
```

Build the paper-order reference index with

```bash
lake build TwiceMarkedBananas
```
