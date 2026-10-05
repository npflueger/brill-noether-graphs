import GenusSixExistence.BrillNoetherRank.Tripod.Realisation
import GenusSixExistence.BrillNoetherRank.GenusFivePairs

/-!
# The expected Brill--Noether rank through genus six

Every connected graph of genus at most six has the expected Brill--Noether rank: for all `r ≥ 0`
with `ρ = ρ(g, r, d) ≥ 0`, `w^r_d ≥ min(ρ, d - r)` (`bnRankGe_through_six`), and so
`ρ ≤ w^r_d` whenever `d ≤ g + r` (`bnNumber_le_bnRank_through_six`). Here `w^r_d(G) ≥ k` is
`Utilities.BNRankGe G r d k`: every effective divisor of degree `r + k` on the vertices of `G` is
contained in an effective divisor of degree `d` and rank at least `r`.

The proof is in prose in `Research/genus-six-brill-noether-rank.md`; section and statement
numbers below refer to that note. By `bnRankGe_through_six_of_triples`
(`GenusSixExistence/BrillNoetherRank/GenusFivePairs.lean`), the theorem reduces to the *triple
witness* `tripleWitness`, which is `w^1_5 ≥ 2` in genus six before descent (§1, §2). The triple
witness is proved by *tripod subtraction* (§3--§7):

1. contract every bridge (`Closure.oddCompletionWitness_of_bridgeless`, §6.1);
2. build a tripod model of `(G, E)`: a cubic core of genus eight carrying `G`, the three chips
   of `E` as marks, and a tripod of long legs attached at them (`Closure.exists_tripodModel`,
   §6.2);
3. at the actual request of the model, find a closed claw frame of odd multiplicity
   (`Closure.exists_closed_oddClaw`, Theorem 6.3). It comes from the parity (P5) of §6.3:
   the open odd count in degree five over the genus-eight core is even
   (`DraismaVargas.Count.EvenGenusParity.evenC34_three`), the one in degree four over the
   genus-six core is odd (`DraismaVargas.Count.Assembly.c34_genusSix`), and gluing matches the
   glued classes with the classes over the genus-six core;
4. realise that frame as a divisor `E + F` of rank at least one on an odd subdivision of `G`
   (`Realisation.witness_of_closed_oddClaw`, Theorem 7.5).

## Map of the modules

Under `GenusSixExistence/BrillNoetherRank/`:

| module | content | note |
|---|---|---|
| `Reduction` | the elementary cases; the reduction to existence, `w^1_4 ≥ 1` in genus five and `w^1_5 ≥ 2` in genus six; `OddCompletionWitness` and its descent by two-chip rounding | §1.3--§1.4, §2.1--§2.2 |
| `GenusFivePairs` | pairs in genus five from the long-handle lemma; the expected rank through genus five; the reduction through genus six to the triple witness | §1.5 |
| `Tripod/Gadget` | the gadget core: subdivision at the marks, the tripod, requests, long legs; genus eight, cubic, connected, loopless | §3.1, §6.2 |
| `Tripod/ClawDefs` | claw and glued frames, members and classes, and their invariance under isomorphism; admissible requests | §3.4, §6.3 |
| `Tripod/Dichotomy` | the lost-edge bound, the leg shape, long legs leave the image of `G`, the parameter count: glued or claw, not both | §4.3--§4.6, §4.8 |
| `Tripod/ClawShape` | the shape of a claw frame: its centre is trivalent with the lost edges at it, every leg edge has index one, `k₀ = 0` | §4.6, §4.7 |
| `Tripod/Gluing` | the Cools--Draisma gluing as a gluing datum; its dangling edges, stable paths and trivalence; the determinant and the denominators | §5.1--§5.4 |
| `Tripod/GluingRestrict`, `Tripod/GluingInjective`, `Tripod/GluingExtend` | restriction to the old sheets; injectivity on classes; transport along an isomorphism | §5.5 |
| `Tripod/GluingOntoIdent`, `Tripod/GluingOntoOpen`, `Tripod/GluingOntoTarget`, `Tripod/GluingOntoShape`, `Tripod/GluingOnto` | surjectivity: the shape of a glued member, and the member over `G` left after deleting the arms and the extra sheet | §5.5 |
| `Tripod/GluingLayout`, `Tripod/GluingLayoutStages`, `Tripod/GluingPieceIdent`, `Tripod/GluingPositivity`, `Tripod/GluingWellDefined` | the glued labels at the actual mark positions; positivity; well-definedness on classes | §5.2, §5.5 |
| `Tripod/GluingClasses` | the gluing bijection on classes, preserving multiplicity | Theorem 5.1 |
| `Tripod/Classification` | the dichotomy, the gluing bijection, and the parity (P5) of the claw classes | §3.4, §6.3 |
| `Tripod/BridgeLift` | reduction to bridgeless graphs | §6.1 |
| `Tripod/TripodModelDefs`, `Tripod/TripodMarkRefinement`, `Tripod/TripodModelProof` | the tripod model, and its existence for every bridgeless `G` and every `E` | §6.2 |
| `Tripod/ClosureFrame`, `Tripod/Closure` | the segment: a closed claw frame of odd multiplicity at the actual request | §6.4 |
| `Tripod/ChainSeparator` | rank one through the marker chains of a subdivision, by Luo's criterion | §7.4 |
| `Tripod/RealisationProof`, `Tripod/Realisation` | the witness divisor, odd denominators, slot moments, interior firing and rounding with `E` fixed | §7.3--§7.5 |

The namespace of `Tripod/X` is `GenusSixExistence.Tripod.X`, except that the definition modules
share the namespace of their main module (`ClawDefs` is in `Tripod.Classification`,
`TripodModelDefs` in `Tripod.Closure`, every `Gluing*` module in `Tripod.Gluing`,
`TripodMarkRefinement` in `Tripod.MarkRefinement`). Four generic pieces are in `Utilities`:
`Utilities.Subdivision.ScaleLift` (a Laplacian equivalence of subdivisions lifts to every scale),
`Utilities.Subdivision.BridgeLift` (contracting every bridge at every scale),
`Utilities.Subdivision.BivalentPaths` (bivalent paths and strong-separator cells) and
`Utilities.DeterminantExpansion` (determinants of matrices with sparse columns).
-/

namespace GenusSixExistence

open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph MarkedGraphs
open GenusSixExistence.Tripod.Closure GenusSixExistence.Tripod.Realisation

/-- **The genus-six triple witness** (`w^1_5 ≥ 2` in genus six, before descent). For every
connected genus-six graph `G` and every effective divisor `E` of degree three on its vertices,
there are an odd `N` and an effective `F` of degree two on the `N`-fold subdivision of `G` with
`rank (E + F) ≥ 1`. -/
theorem tripleWitness : ∀ G : CFGraph.{0}, graph_connected G → genus G = 6 →
    BrillNoetherRank.OddCompletionWitness G 1 2 := by
  intro G hG hg
  refine oddCompletionWitness_of_bridgeless ?_ G hG hg
  intro H hH hHg hHb E hE hdeg
  obtain ⟨M⟩ := exists_tripodModel H hH hHg hHb E hE (by rw [hdeg]; norm_num)
  obtain ⟨mem, hClosed, hOdd, hClaw⟩ :=
    exists_closed_oddClaw M.core M.cubic M.connected M.loopless (by norm_num) M.slots M.request
      M.request_nonneg M.longLegs
  exact witness_of_closed_oddClaw M mem hClosed hOdd hClaw

/-- **The expected Brill--Noether rank through genus six.** For every connected graph of genus
at most six and all `r ≥ 0`, `ρ ≥ 0`: `w^r_d ≥ min(ρ, d - r)`. -/
theorem bnRankGe_through_six (G : CFGraph.{0}) (hG : graph_connected G) (hg : genus G ≤ 6)
    {r d : ℤ} (hr : 0 ≤ r) (hρ : 0 ≤ bnNumber G r d) :
    BNRankGe G r d (min (bnNumber G r d) (d - r)) :=
  bnRankGe_through_six_of_triples tripleWitness G hG hg hr hρ

/-- **`ρ ≤ w^r_d` through genus six**, in the natural degree range `d ≤ g + r`. -/
theorem bnNumber_le_bnRank_through_six (G : CFGraph.{0}) (hG : graph_connected G)
    (hg : genus G ≤ 6) {r d : ℤ} (hr : 0 ≤ r) (hρ : 0 ≤ bnNumber G r d)
    (hd : d ≤ genus G + r) : bnNumber G r d ≤ bnRank G r d :=
  bnNumber_le_bnRank_through_six_of_triples tripleWitness G hG hg hr hρ hd

end GenusSixExistence
