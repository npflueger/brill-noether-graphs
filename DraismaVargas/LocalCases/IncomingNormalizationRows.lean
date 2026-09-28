import DraismaVargas.LocalCases.TargetPartitionNormalization
import DraismaVargas.LocalCases.ResolutionAwayFromWall
import DraismaVargas.LocalCases.WallDegeneration

/-!
# Incoming normalization follows every retained wall row

The compatible-labelling rule of Draisma--Vargas Part I, Section 5
("Inherited properties": the edge labellings a limit inherits, labellings
compatible at `t_k`, and Lemma `lemma-limit-matrix-change`) follows a literal
surviving occurrence through contraction, target renaming and compatible
sheet normalization. This module proves that this is exactly the candidate's
retained occurrence. All old edge partitions were retained, so their
representatives are fixed by the normalization. No arbitrary stable-row
bijection is used.
-/

namespace DraismaVargas.LocalCases.IncomingNormalizationRows

open Utilities DraismaVargas.Infrastructure GraphContraction GluingContraction
open W4StableSource TargetExpansion

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  (incoming : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

/-- The inverse contraction occurrence map preserves the actual sheet
representative and unfolds its target occurrence. -/
theorem sourceEdgeEmbedding_val
    (edge : (contractDatum incoming hc hab hOne).SourceEdge) :
    (WallDegeneration.sourceEdgeEmbedding incoming hc hab hOne edge).1 =
      (unfoldEdge hc hab hOne edge.1.1, edge.1.2) := by
  let restored : {e : incoming.SourceEdge // e.1.1 ≠ contracted} :=
    ⟨⟨(unfoldEdge hc hab hOne edge.1.1, edge.1.2), edge.2⟩,
      unfoldEdge_ne_contracted hc hab hOne edge.1.1⟩
  have hRestore : (ContractionFibre.sourceEdgeEquiv incoming hc hab hOne).symm edge =
      restored := by
    apply (ContractionFibre.sourceEdgeEquiv incoming hc hab hOne).symm_apply_eq.mpr
    exact Subtype.ext (Prod.ext
      (foldEdge_unfoldEdge hc hab hOne edge.1.1 restored.2).symm rfl)
  exact congrArg (fun e => e.1.1) hRestore

variable (candidate : BalancedGlobal.Candidate (contract target hab hOne) degree
    (contractDatum incoming hc hab hOne) ⟨a, hab⟩)
  (φ : CFGraphIso target (TargetExpansion.graph (contract target hab hOne) ⟨a, hab⟩ candidate.right))
  (hVertices : ∀ vertex, ((GluingTransport.transport φ incoming).vertexPartition vertex).SameBlocks
    (candidate.datum.vertexPartition vertex))
  (hEdges : ∀ edge, ((GluingTransport.transport φ incoming).edgePartition edge).SameBlocks
    (candidate.datum.edgePartition edge))
  (hColumns : ∀ edge : (contract target hab hOne).edges,
    GluingTransport.edgeEquiv φ (unfoldEdge hc hab hOne edge) =
      occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ candidate.right (some edge))

include hColumns

/-- The actual composite normalization sends each incoming copy of a wall
survivor to that very survivor's retained copy in the candidate. -/
theorem nonDanglingEdgeEquiv_retained
    (hConnected : incoming.Connected)
    (hWallConnected : (contractDatum incoming hc hab hOne).Connected)
    (hPreserved : WallDegeneration.DanglingPreserved incoming hc hab hOne)
    (edge : NonDanglingEdge (contractDatum incoming hc hab hOne)) :
    TargetPartitionNormalization.nonDanglingEdgeEquiv φ incoming candidate.datum
      hVertices hEdges hConnected (WallDegeneration.nonDanglingEmbedding incoming hPreserved edge) =
        ResolutionAwayFromWall.retainedEdge candidate hWallConnected edge := by
  apply Subtype.ext
  apply Subtype.ext
  rw [TargetPartitionNormalization.nonDanglingEdgeEquiv_val]
  have hOld := sourceEdgeEmbedding_val incoming hc hab hOne edge.1
  have hTarget : (WallDegeneration.nonDanglingEmbedding incoming hPreserved edge).1.1.1 =
      unfoldEdge hc hab hOne edge.1.1.1 := congrArg Prod.fst hOld
  have hSheet : (WallDegeneration.nonDanglingEmbedding incoming hPreserved edge).1.1.2 =
      edge.1.1.2 := congrArg Prod.snd hOld
  rw [hTarget, hSheet, hColumns]
  apply Prod.ext
  · rfl
  · exact (candidate.oldSourceEdge edge.1).2

/-- The row map is compatible with the induced wall labelling on every
surviving occurrence, before any choice of coordinates. -/
theorem stablePathEquiv_retained
    (hConnected : incoming.Connected)
    (hWallConnected : (contractDatum incoming hc hab hOne).Connected)
    (hPreserved : WallDegeneration.DanglingPreserved incoming hc hab hOne)
    (edge : NonDanglingEdge (contractDatum incoming hc hab hOne)) :
    TargetPartitionNormalization.stablePathEquiv φ incoming candidate.datum
      hVertices hEdges hConnected
      (WallDegeneration.nonDanglingEmbedding incoming hPreserved edge).stablePath =
        (ResolutionAwayFromWall.retainedEdge candidate hWallConnected edge).stablePath := by
  rw [TargetPartitionNormalization.stablePathEquiv_mk,
    nonDanglingEdgeEquiv_retained incoming hc hab hOne candidate φ hVertices hEdges
      hColumns hConnected hWallConnected hPreserved]

end DraismaVargas.LocalCases.IncomingNormalizationRows
