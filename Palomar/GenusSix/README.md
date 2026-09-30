# Brill–Noether existence for graphs of genus six

`Challenge.lean` imports only Mathlib. It defines finite multigraphs, divisors,
chip-firing equivalence and the Baker–Norine rank test locally. It then states
three theorems whose bodies are deliberately `sorry`.

## The theorems

1. **`brill_noether_existence_genus_six`.** Let `G` be a connected graph of
   genus six. Let `r ≥ 0` and `d` be integers with
   `ρ(6, r, d) = 6 − (r + 1)(6 − d + r) ≥ 0`. Then `G` has a divisor of degree
   `d` and rank at least `r`. This is Baker's Brill–Noether existence
   conjecture for graphs (Conjecture 3.9(1) of [Baker]) in genus six. Only
   `(r, d) = (1, 4)` needs work: every connected genus-six graph has a divisor
   of degree four and rank at least one. The library proves this in two steps.
   Such a divisor on an odd regular subdivision of a genus-six graph descends to
   the graph itself (library `GenusSixOddDescent`), and every connected
   genus-six graph has such a subdivision, by a mod-2 form of the
   Draisma–Vargas count of tropical pencils ([DV1], [V2]).
   Library declaration: `GenusSixExistence.bnExists`.

2. **`brill_noether_existence_through_six`.** Every connected graph of genus
   `g ≤ 6` has, for all integers `r` and `d` with `(r + 1)(g − d + r) ≤ g`, a
   divisor of degree `d` and rank at least `r`. [AR] proved genus at most five,
   and theorem 1 supplies genus six. The statement is the repository's existing
   through-genus-five highlight with 5 replaced by 6.
   Library declaration: `GenusSixExistence.brillNoetherExistenceThroughSix`.

3. **`once_marked_brill_noether_existence_through_five`.** Let `G` be a
   connected graph of genus `g ≤ 5` with a marked vertex `u`. Let `μ` be a
   Young diagram with at most `g` boxes and row lengths
   `μ₀ ≥ μ₁ ≥ ⋯ > 0`. Then some divisor `D` of degree `g` satisfies
   `rank(D + (i − μᵢ)·u) ≥ i` for every row `i`. Equivalently, the Weierstrass
   partition of `D` at `u` (in the sense of [PS], Definition 1.6) contains
   `μ`. In genus five the statement is equivalent to its case `μ = (3, 2)`: a
   divisor of degree four and rank at least one that contains `2u`. That case
   follows from theorem 1 by attaching a cycle at `u` (a tropical elliptic
   tail). Genus at most four is handled separately, using [AR] in genus four.
   Library declaration: `GenusSixExistence.onceMarkedBNExistenceThroughFive`.

## Formulation choices

- **Graphs.** A graph is a finite, nonempty multigraph without loops, with
  its edges stored as a multiset of vertex pairs. Parallel edges are allowed.
  Connectivity means that every nontrivial vertex cut is crossed by an edge.
  The genus is the cyclomatic number `|E| − |V| + 1`, an integer.
- **Rank.** Rank is never defined as a number. `rank_geq G D k` says that
  `D − E` is equivalent to an effective divisor for every effective `E` of
  degree `k`, which is the Baker–Norine condition `r(D) ≥ k`. For `k < 0` it
  holds vacuously.
- **Exact degree and lower bound on rank.** Each conclusion gives a divisor of
  degree exactly `d` and rank at least `r`. Baker asks for rank exactly `r` and
  degree at most `d`. The two forms are equivalent, since adding a chip does not
  lower the rank and removing one lowers it by at most one.
- **ρ.** The condition `ρ ≥ 0` is written without division as
  `(r + 1)(6 − d + r) ≤ 6`, or `(r + 1)(g − d + r) ≤ g` with `genus G = g`.
  Theorem 1 assumes `0 ≤ r`, as the library does. Theorem 2 has no such
  hypothesis because the case `r < 0` is trivial, again as in the library.
- **Once-marked form.** Young diagrams are Mathlib's `YoungDiagram`, and `μᵢ`
  is `μ.rowLens[i]`. The witness is normalized to degree exactly `g`. Only rows
  `i` of `μ` are tested. For larger `i` the inequality
  `rank(D + i·u) ≥ i` follows from Riemann–Roch.
- **Universes.** Theorem 1 holds for graphs whose vertex type lies in any
  universe. Theorems 2 and 3 are stated for vertex types in `Type`, as is the
  Atanasov–Ranganathan theorem they extend.

## References

- [AR] S. Atanasov and D. Ranganathan, *A note on Brill–Noether existence for
  graphs of low genus*, Michigan Math. J. 67 (2018);
  [doi:10.1307/mmj/1519095622](https://doi.org/10.1307/mmj/1519095622),
  arXiv:1609.02091.
- [Baker] M. Baker, *Specialization of linear systems from curves to graphs*,
  Algebra & Number Theory 2 (2008).
- [DV1] J. Draisma and A. Vargas, *Catalan-many tropical morphisms to trees;
  Part I: Constructions*, arXiv:1909.12924.
- [V2] A. Vargas, *Catalan-many tropical morphisms to trees; Part II: A space
  and a count*, arXiv:2609.09109.
- [PS] N. Pflueger and N. Solomon, *Twice-marked banana graphs & Brill–Noether
  generality*, Algebraic Combinatorics 8 (2025);
  [doi:10.5802/alco.443](https://doi.org/10.5802/alco.443).
