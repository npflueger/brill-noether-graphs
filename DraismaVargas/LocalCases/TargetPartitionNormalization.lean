import DraismaVargas.LocalCases.PartitionStableNormalization

/-!
# Occurrence-induced transport through target and partition normalization

Compose the actual target renaming with the within-block representative
normalization. The final source occurrence is named by the mapped target
occurrence and the same original sheet. This supplies the literal comparison
needed for compatible wall rows; no row bijection is selected by cardinality.
-/

namespace DraismaVargas.LocalCases.TargetPartitionNormalization

open Utilities DraismaVargas.Infrastructure GluingTransport W4StableSource

variable {G H : CFGraph} {degree : ℕ} (φ : CFGraphIso G H)
  (data : GluingDatum G degree) (other : GluingDatum H degree)
  (hVertices : ∀ vertex, ((transport φ data).vertexPartition vertex).SameBlocks
    (other.vertexPartition vertex))
  (hEdges : ∀ edge, ((transport φ data).edgePartition edge).SameBlocks
    (other.edgePartition edge))

noncomputable def nonDanglingEdgeEquiv (hConnected : data.Connected) :
    NonDanglingEdge data ≃ NonDanglingEdge other :=
  (TargetRelabelStable.nonDanglingEdgeEquiv φ data hConnected).trans
    (PartitionStableNormalization.nonDanglingEdgeEquiv (transport φ data) other
      hVertices hEdges (connected_transport φ data hConnected))

noncomputable def stablePathEquiv (hConnected : data.Connected) :
    StablePath data ≃ StablePath other :=
  (TargetRelabelStable.stablePathEquiv φ data hConnected).trans
    (PartitionStableNormalization.stablePathEquiv (transport φ data) other
      hVertices hEdges (connected_transport φ data hConnected))

theorem stablePathEquiv_mk (hConnected : data.Connected) (edge : NonDanglingEdge data) :
    stablePathEquiv φ data other hVertices hEdges hConnected edge.stablePath =
      (nonDanglingEdgeEquiv φ data other hVertices hEdges hConnected edge).stablePath := by
  unfold stablePathEquiv nonDanglingEdgeEquiv
  rw [Equiv.trans_apply, TargetRelabelStable.stablePathEquiv_mk,
    PartitionStableNormalization.stablePathEquiv_mk]
  rfl

private theorem target_sourceEdge_val (hConnected : data.Connected)
    (edge : NonDanglingEdge data) :
    (TargetRelabelStable.nonDanglingEdgeEquiv φ data hConnected edge).1 =
      (transport φ data).sourceEdge (edgeEquiv φ edge.1.1.1) edge.1.1.2 := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change edge.1.1.2 = ((transport φ data).edgePartition
      (edgeEquiv φ edge.1.1.1)).repr edge.1.1.2
    rw [transport_edgePartition_apply]
    exact edge.1.2.symm

/-- Every original surviving occurrence follows its mapped target occurrence
and original sheet, with the final datum's canonical representative. -/
theorem nonDanglingEdgeEquiv_val (hConnected : data.Connected)
    (edge : NonDanglingEdge data) :
    (nonDanglingEdgeEquiv φ data other hVertices hEdges hConnected edge).1.1 =
      (edgeEquiv φ edge.1.1.1,
        (other.edgePartition (edgeEquiv φ edge.1.1.1)).repr edge.1.1.2) := by
  let moved := TargetRelabelStable.nonDanglingEdgeEquiv φ data hConnected edge
  have hValue : moved.1 = (transport φ data).sourceEdge
      (edgeEquiv φ edge.1.1.1) edge.1.1.2 := target_sourceEdge_val φ data hConnected edge
  have hSurvives : ¬ IsDangling (transport φ data)
      ((transport φ data).sourceEdge (edgeEquiv φ edge.1.1.1) edge.1.1.2) := by
    rw [← hValue]
    exact moved.2
  have hMoved : moved = ⟨_, hSurvives⟩ := Subtype.ext hValue
  change (PartitionStableNormalization.nonDanglingEdgeEquiv (transport φ data) other
    hVertices hEdges (connected_transport φ data hConnected) moved).1.1 = _
  rw [hMoved]
  exact PartitionStableNormalization.nonDanglingEdgeEquiv_sourceEdge_val
    (transport φ data) other hVertices hEdges (connected_transport φ data hConnected)
    (edgeEquiv φ edge.1.1.1) edge.1.1.2 hSurvives

theorem matrix_map (hConnected : data.Connected) (path : StablePath data) (edge : G.edges) :
    StableSourceMatrix.matrix other
        (stablePathEquiv φ data other hVertices hEdges hConnected path) (edgeEquiv φ edge) =
      StableSourceMatrix.matrix data path edge := by
  unfold stablePathEquiv
  rw [Equiv.trans_apply, PartitionStableNormalization.matrix_map,
    TargetRelabelStable.matrix_map]

noncomputable def graphEquivalence (hConnected : data.Connected) :
    StableGraphIncidence.Equivalence data other :=
  (TargetRelabelStable.graphEquivalence φ data hConnected).trans
    (PartitionStableNormalization.graphEquivalence (transport φ data) other
      hVertices hEdges (connected_transport φ data hConnected))

theorem graphEquivalence_row (hConnected : data.Connected) :
    (graphEquivalence φ data other hVertices hEdges hConnected).row =
      stablePathEquiv φ data other hVertices hEdges hConnected := by
  unfold graphEquivalence StableGraphIncidence.Equivalence.trans
  simp only [PartitionStableNormalization.graphEquivalence_row]
  rfl

section Presentation

open FullDimensionalSource

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- Full-dimensionality in exactly the original coordinates, transported
through the actual target map and within-block representative changes. -/
noncomputable def presentation (source : FullDimensionalSourcePresentation data coordinate) :
    FullDimensionalSourcePresentation other coordinate :=
  PartitionStableNormalization.presentation (transport φ data) other hVertices hEdges
    (RelabelFullDimensional.targetPresentation φ source)

theorem presentation_matrix_eq (source : FullDimensionalSourcePresentation data coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix
        (presentation φ data other hVertices hEdges source).labelling.presentation =
      GluingDatum.LengthMatrixPresentation.matrix source.labelling.presentation := by
  rw [presentation, PartitionStableNormalization.presentation_matrix_eq]
  exact RelabelFullDimensional.target_matrix_eq φ data source.valid.1 source.labelling

theorem presentation_targetEdge (source : FullDimensionalSourcePresentation data coordinate) :
    (presentation φ data other hVertices hEdges source).labelling.targetEdge =
      source.labelling.targetEdge.trans (edgeEquiv φ) := by
  rw [presentation, PartitionStableNormalization.presentation_targetEdge]
  rfl

end Presentation

end DraismaVargas.LocalCases.TargetPartitionNormalization
