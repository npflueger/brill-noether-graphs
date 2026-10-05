# Brill–Noether existence for graphs of genus six

`Challenge.lean` imports only Mathlib. It defines finite multigraphs, divisors,
chip-firing equivalence and the Baker–Norine rank test locally. It then states
four theorems whose bodies are deliberately `sorry`.

## The theorems

1. **`brill_noether_existence_through_six`.** Let `G` be a connected graph of
   genus `g ≤ 6`. Let `r` and `d` be integers with
   `ρ(g, r, d) = g − (r + 1)(g − d + r) ≥ 0`. Then `G` has a divisor of degree
   `d` and rank at least `r`. This is Baker's Brill–Noether existence
   conjecture for graphs (Conjecture 3.9(1) of [Baker]) through genus six.
   [AR] proved genus at most five, and the statement is the repository's
   existing through-genus-five highlight with 5 replaced by 6. The new case is
   genus six, where only `(r, d) = (1, 4)` needs work: every connected
   genus-six graph has a divisor of degree four and rank at least one. The
   other genus-six cases follow from it and Riemann–Roch. The library proves
   the case `(1, 4)` in two steps. Such a divisor on an odd regular subdivision
   of a genus-six graph descends to the graph itself (library
   `GenusSixOddDescent`), and every connected genus-six graph has such a
   subdivision, by a mod-2 form of the Draisma–Vargas count of tropical pencils
   ([DV1], [V2]).
   Library declarations: `GenusSixExistence.brillNoetherExistenceThroughSix`,
   and `GenusSixExistence.bnExists` for genus six alone.

2. **`brill_noether_rank_through_six`** and
   **`brill_noether_rank_ge_rho_through_six`.** The Brill–Noether rank
   `w^r_d(G)` of [LPP] and [Len] is the largest `k ≥ 0` such that every
   effective divisor of degree `r + k` is contained, up to linear equivalence,
   in a divisor of degree `d` and rank at least `r`. For a connected graph of
   genus `g ≤ 6` and `r ≥ 0`, `ρ(g, r, d) ≥ 0`, the first theorem gives
   `w^r_d(G) ≥ min(ρ, d − r)`, and the second gives `ρ ≤ w^r_d(G)` when
   `d ≤ g + r`, as for a general curve. The statements unfold the definition:
   every effective `E` of the given degree has a `D` of degree `d` with
   `rank_geq G D r` and `D − E` winnable. Beyond existence, the new cases are
   pairs in genus five (`w^1_4 ≥ 1`), proved by attaching a long path between
   the two vertices and applying genus-six existence, and triples in genus six
   (`w^1_5 ≥ 2`), proved by attaching a tripod at the three vertices and
   counting tropical morphisms on the genus-eight result mod 2. The proof is
   in `Research/genus-six-brill-noether-rank.md`.
   Library declarations: `GenusSixExistence.bnRankGe_through_six` and
   `GenusSixExistence.bnNumber_le_bnRank_through_six`.

3. **`once_marked_brill_noether_existence_through_five`.** Let `G` be a
   connected graph of genus `g ≤ 5` with a marked vertex `u`. Let `μ` be a
   Young diagram with at most `g` boxes and row lengths
   `μ₀ ≥ μ₁ ≥ ⋯ > 0`. Then some divisor `D` of degree `g` satisfies
   `rank(D + (i − μᵢ)·u) ≥ i` for every row `i`. Equivalently, the Weierstrass
   partition of `D` at `u` (in the sense of [PS], Definition 1.6) contains
   `μ`. The case of rectangular diagrams is precisely the theorem of [AR]. If
   `μ` has `r + 1` rows of length `g − d + r`, it has at most `g` boxes exactly
   when `ρ(g, r, d) ≥ 0`, and the conclusion says that `D − (g − d)·u` has
   degree `d` and rank at least `r`. In genus five the statement is equivalent
   to its case `μ = (3, 2)`: a divisor of degree four and rank at least one that
   contains `2u`. That case follows from the genus-six case of theorem 1 by
   attaching a cycle at `u` (a tropical elliptic tail). Genus at most four is
   handled separately, using [AR] in genus four.
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
  `(r + 1)(g − d + r) ≤ g`, with `genus G = g`. There is no hypothesis
  `0 ≤ r`, because the case `r < 0` is trivial, as in the library's
  through-genus-six theorem.
- **Once-marked form.** Young diagrams are Mathlib's `YoungDiagram`, and `μᵢ`
  is `μ.rowLens[i]`. The witness is normalized to degree exactly `g`. Only rows
  `i` of `μ` are tested. For larger `i` the inequality
  `rank(D + i·u) ≥ i` follows from Riemann–Roch.
- **Universes.** All four theorems are stated for vertex types in `Type`, as is the
  Atanasov–Ranganathan theorem they extend. The library's genus-six theorem
  `GenusSixExistence.bnExists` holds for vertex types in any universe, but that
  generality is not claimed here.

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
- [Len] Y. Len, *The Brill–Noether rank of a metric graph*, arXiv:1209.6309.
- [LPP] C. M. Lim, S. Payne and N. Potashnik, *A note on Brill–Noether theory and
  rank-determining sets for metric graphs*, Int. Math. Res. Not. IMRN (2012);
  arXiv:1106.5519.
- [PS] N. Pflueger and N. Solomon, *Twice-marked banana graphs & Brill–Noether
  generality*, Algebraic Combinatorics 8 (2025);
  [doi:10.5802/alco.443](https://doi.org/10.5802/alco.443).
