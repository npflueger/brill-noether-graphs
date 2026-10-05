import GenusSixExistence.BrillNoetherRank.Reduction
import Utilities.Subdivision.BridgeLift

/-!
# Reduction of the triple witness to bridgeless graphs

`oddCompletionWitness_of_bridgeless` reduces the genus-six triple witness
`BrillNoetherRank.OddCompletionWitness G 1 2` to graphs whose unit presentation has a bridgeless
core. Apply the bridgeless case to the fossil `Utilities.fossil G` (all bridges contracted), and
lift the completion back along the contraction of every bridge at the odd scale it uses, by
`Utilities.Subdivision.BridgeLift.rank_geq_of_contraction`. Prose proof:
`Research/genus-six-brill-noether-rank.md`, the reduction to bridgeless graphs.
-/

namespace GenusSixExistence.Tripod.BridgeLift

open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.UnitSubdivisionPresentation
open Utilities.Subdivision.BridgeLift

/-- **The bridge lift.** It suffices to prove the triple
witness for graphs whose unit presentation has a bridgeless core: apply it to the fossil of `G`,
and lift the completion along the contraction of every bridge. -/
theorem oddCompletionWitness_of_bridgeless
    (h : ∀ H : CFGraph.{0}, graph_connected H → genus H = 6 →
      (UnitSubdivisionPresentation.spec H).core.Bridgeless →
        BrillNoetherRank.OddCompletionWitness H 1 2)
    (G : CFGraph.{0}) (hG : graph_connected G) (hg : genus G = 6) :
    BrillNoetherRank.OddCompletionWitness G 1 2 := by
  intro E hE hdeg
  have hH : graph_connected (fossil G) := graph_connected_fossil G hG
  have hgH : genus (fossil G) = 6 := (genus_fossil G hG).trans hg
  have hbH : (spec (fossil G)).core.Bridgeless :=
    Gonality.core_bridgeless_of_twoEdgeCutCondition (fossil G) hH (twoEdgeCutCondition_fossil G hG)
  let c₁ : GraphContractionCertificate (spec G).graph (spec (fossil G)).graph := ⟨baseMap G⟩
  obtain ⟨N, hN, hodd, F', hF', hF'deg, hrank⟩ := h (fossil G) hH hgH hbH (c₁.pushDiv E)
    (c₁.effective_pushDiv hE) (by rw [c₁.deg_pushDiv]; exact hdeg)
  let c : GraphContractionCertificate ((spec G).scale N hN).graph
      ((spec (fossil G)).scale N hN).graph := ⟨contractionMap G N hN⟩
  have hsurj : Function.Surjective c.vertexMap := contractionMap_surjective G N hN
  refine ⟨N, hN, hodd, liftDiv c hsurj F', effective_liftDiv c hsurj hF',
    by rw [deg_liftDiv]; exact hF'deg, ?_⟩
  apply (rank_geq_iff _ _ _).mp
  apply rank_geq_of_contraction c hsurj (fibresEquivalent G N hN hG) (contraction_valid G N hN)
  rw [c.pushDiv_add, pushDiv_embed, pushDiv_liftDiv]
  exact (rank_geq_iff _ _ _).mpr hrank

end GenusSixExistence.Tripod.BridgeLift
