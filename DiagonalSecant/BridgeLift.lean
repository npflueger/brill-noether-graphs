module

public import DiagonalSecant.Defs
public import Utilities.Subdivision.BridgeLift

@[expose] public section

/-!
# Reduction of the diagonal witness to bridgeless graphs

The bridge lift is Lemma 6.1 and Corollary 6.2 of `Research/genus-six-brill-noether-rank.md`
(§6.1). This module is the public
`GenusSixExistence.Tripod.BridgeLift.oddCompletionWitness_of_bridgeless`
(`GenusSixExistence/BrillNoetherRank/Tripod/BridgeLift.lean`) with `OddCompletionWitness H 1 2`
replaced by `DiagonalOddWitness H m (baseMap G u)`: apply the bridgeless case to the fossil
`Utilities.fossil G` (all bridges contracted; connected, of the same genus, with a bridgeless
core: `graph_connected_fossil`, `genus_fossil`, `twoEdgeCutCondition_fossil`,
`Gonality.core_bridgeless_of_twoEdgeCutCondition`, all genus-free), and lift the completion back
along the contraction of every bridge at the odd scale it uses
(`Utilities.Subdivision.BridgeLift.rank_geq_of_contraction`, `liftDiv`). The one new fact is that
the pushforward of `m • one_chip u` along the base contraction is `m • one_chip (baseMap G u)`
(`pushDivHom` is additive; a chip pushes to a chip).
-/

namespace DiagonalSecant

open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.UnitSubdivisionPresentation
open Utilities.Subdivision.BridgeLift

/-- **The bridge lift.** It suffices to prove the diagonal witness for graphs whose unit
presentation has a bridgeless core, in the same genus. -/
theorem diagonalOddWitness_of_bridgeless {g : ℕ}
    (h : ∀ (H : CFGraph.{0}) (v : (spec H).graph.V), graph_connected H → genus H = g →
      (spec H).core.Bridgeless → DiagonalOddWitness H (g - 3) v)
    (G : CFGraph.{0}) (u : (spec G).graph.V) (hG : graph_connected G) (hg : genus G = g) :
    DiagonalOddWitness G (g - 3) u := by
  have hH : graph_connected (fossil G) := graph_connected_fossil G hG
  have hgH : genus (fossil G) = g := (genus_fossil G hG).trans hg
  have hbH : (spec (fossil G)).core.Bridgeless :=
    Gonality.core_bridgeless_of_twoEdgeCutCondition (fossil G) hH (twoEdgeCutCondition_fossil G hG)
  let c₁ : GraphContractionCertificate (spec G).graph (spec (fossil G)).graph := ⟨baseMap G⟩
  have hpush : c₁.pushDiv ((g - 3) • one_chip u) = (g - 3) • one_chip (baseMap G u) := by
    rw [← pushDivHom_apply, map_nsmul, pushDivHom_apply, c₁.pushDiv_one_chip]
  obtain ⟨N, hN, hodd, F', hF', hF'deg, hrank⟩ := h (fossil G) (baseMap G u) hH hgH hbH
  let c : GraphContractionCertificate ((spec G).scale N hN).graph
      ((spec (fossil G)).scale N hN).graph := ⟨contractionMap G N hN⟩
  have hsurj : Function.Surjective c.vertexMap := contractionMap_surjective G N hN
  refine ⟨N, hN, hodd, liftDiv c hsurj F', effective_liftDiv c hsurj hF',
    by rw [deg_liftDiv]; exact hF'deg, ?_⟩
  apply (rank_geq_iff _ _ _).mp
  apply rank_geq_of_contraction c hsurj (fibresEquivalent G N hN hG) (contraction_valid G N hN)
  rw [c.pushDiv_add, pushDiv_embed, pushDiv_liftDiv]
  change rank_geq _ ((spec (fossil G)).embed N hN (c₁.pushDiv ((g - 3) • one_chip u)) + F') 1
  rw [hpush]
  exact (rank_geq_iff _ _ _).mpr hrank

end DiagonalSecant
