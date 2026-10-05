module

public import GenusSixOddDescent.Main
public import DraismaVargasCount.Assembly
public import LowGenus.AtanasovRanganathanExistence

@[expose] public section

/-!
# Brill--Noether existence in genus six

Every connected finite graph of genus six satisfies Brill--Noether existence: for all integers
`r ≥ 0` and `d` with `ρ(6, r, d) ≥ 0` it carries a divisor of degree `d` and rank at least `r`.

The proof composes two libraries.

* `GenusSixOddDescent.bnExists_genus_six_of_oddWitness` proves existence in genus six from the
  hypothesis `GenusSixOddDescent.GenusSixOddSubdivisionWitness`: every connected genus-six graph
  has an odd regular subdivision carrying a degree-four divisor of rank at least one. Its proof
  descends such a pencil from the subdivision to the graph.
* `DraismaVargas.Count.genusSix_witness` proves that hypothesis with the mod-2 count of tropical
  pencils of Draisma--Vargas (Part I) and Vargas (Part II); `DraismaVargasCount.Assembly` lays out
  its five steps.

`brillNoetherExistenceThroughSix` then extends the Atanasov--Ranganathan theorem
(`AtanasovRanganathan.brillNoetherExistenceThroughFive`) from genus five to genus six, in the
same statement form.
-/

namespace GenusSixExistence

open Utilities Utilities.Gonality GenusSixOddDescent

universe u

/-- **The genus-six odd-subdivision witness.** Every connected genus-six graph has an odd regular
subdivision carrying a degree-four divisor of rank at least one. -/
theorem genusSixOddSubdivisionWitness : GenusSixOddSubdivisionWitness.{u} :=
  _root_.DraismaVargas.Count.genusSix_witness

/-- **Brill--Noether existence in genus six.** Every connected genus-six graph satisfies
Brill--Noether existence at every admissible `(r, d)`: `0 ≤ r` and `0 ≤ ρ(G, r, d)`. -/
theorem bnExists (G : CFGraph.{u}) (hConnected : graph_connected G) (hGenus : genus G = 6)
    {r d : ℤ} (hRank : 0 ≤ r) (hRho : 0 ≤ bnNumber G r d) : BNExists G r d :=
  bnExists_genus_six_of_oddWitness genusSixOddSubdivisionWitness G hConnected hGenus hRank hRho

/-- **The critical genus-six pencil.** Every connected genus-six graph carries a divisor of
degree four and rank at least one. -/
theorem criticalPencil (G : CFGraph.{u}) (hConnected : graph_connected G)
    (hGenus : genus G = 6) : BNExists G 1 4 := by
  apply bnExists G hConnected hGenus
  · norm_num
  · simp [bnNumber, rectangleWidth, hGenus]

/-- **Brill--Noether existence through genus six.** Every connected finite graph of genus at
most six satisfies Brill--Noether existence, stated exactly as
`Utilities.BrillNoetherExistenceThroughFive` (the library's degree-exact,
rank-lower-bound convention `brill_noether_conjecture`, for all `r d : ℤ`). Genus at most five
is `AtanasovRanganathan.brillNoetherExistenceThroughFive`; genus six is `bnExists`; a negative
`r` is trivial because every rank is at least `-1`. -/
theorem brillNoetherExistenceThroughSix :
    ∀ (G : CFGraph.{0}) (hG : graph_connected G), genus G ≤ 6 →
      ∀ r d : ℤ, brill_noether_conjecture hG r d := by
  intro G hG hGenus r d
  rcases lt_or_ge (genus G) 6 with h5 | h6
  · exact AtanasovRanganathan.brillNoetherExistenceThroughFive G hG (by omega) r d
  have hSix : genus G = 6 := by omega
  show 0 ≤ genus G - (r + 1) * (genus G - d + r) →
    ∃ D : CFDiv G, rank G D ≥ r ∧ deg D = d
  intro hRho
  by_cases hR : 0 ≤ r
  · obtain ⟨D, hDegree, hRank⟩ :=
      bnExists G hG hSix hR (by simpa [bnNumber, rectangleWidth] using hRho)
    exact ⟨D, hRank, hDegree⟩
  · let u : G.V := Classical.arbitrary G.V
    refine ⟨d • one_chip u, ?_, ?_⟩
    · have hLower := rank_geq_neg_one G (d • one_chip u)
      omega
    · rw [map_zsmul, deg_one_chip]
      ring

end GenusSixExistence
