import DraismaVargas.Infrastructure.PartitionNormalization
import DraismaVargas.LocalCases.RelabelFullDimensional

/-!
# Actual stable-source transport across equal partition relations

Use the proved within-block representative normalization, then transport
along its exact datum equality. The stable rows follow the literal source
occurrences, and their entire natural matrix is preserved. Equal block counts
alone are not an input: equality of every vertex/edge relation is required.
-/

namespace DraismaVargas.LocalCases.PartitionStableNormalization

open DraismaVargas.Infrastructure W4StableSource FullDimensionalSource
open StableSourceMatrix

variable {target : CFGraph} {degree : ℕ}

private theorem stablePath_cast {first second : GluingDatum target degree}
    (h : first = second) (edge : NonDanglingEdge first) :
    (Equiv.cast (congrArg NonDanglingEdge h) edge).stablePath =
      Equiv.cast (congrArg StablePath h) edge.stablePath := by
  cases h
  rfl

private theorem edge_val_cast {first second : GluingDatum target degree}
    (h : first = second) (edge : NonDanglingEdge first) :
    (Equiv.cast (congrArg NonDanglingEdge h) edge).1.1 = edge.1.1 := by
  cases h
  rfl

private theorem matrix_cast {first second : GluingDatum target degree}
    (h : first = second) (path : StablePath first) (edge : target.edges) :
    matrix second (Equiv.cast (congrArg StablePath h) path) edge = matrix first path edge := by
  cases h
  rfl

private theorem graph_cast_row {first second : GluingDatum target degree}
    (h : first = second) {initial : GluingDatum target degree}
    (certificate : StableGraphIncidence.Equivalence initial first) :
    (h ▸ certificate : StableGraphIncidence.Equivalence initial second).row =
      certificate.row.trans (Equiv.cast (congrArg StablePath h)) := by
  cases h
  rfl

variable (data other : GluingDatum target degree)
  (hVertices : ∀ vertex, (data.vertexPartition vertex).SameBlocks (other.vertexPartition vertex))
  (hEdges : ∀ edge, (data.edgePartition edge).SameBlocks (other.edgePartition edge))

/-- The surviving-edge equivalence induced by within-block normalization,
followed by exact equality of the normalized datum with `other`. -/
noncomputable def nonDanglingEdgeEquiv (hConnected : data.Connected) :
    NonDanglingEdge data ≃ NonDanglingEdge other :=
  (SheetRelabelStable.nonDanglingEdgeEquiv
    (PartitionNormalization.sheetRelabeling data other hVertices hEdges) hConnected).trans
    (Equiv.cast (congrArg NonDanglingEdge
      (PartitionNormalization.sheetRelabeling_apply data other hVertices hEdges)))

noncomputable def stablePathEquiv (hConnected : data.Connected) :
    StablePath data ≃ StablePath other :=
  (SheetRelabelStable.stablePathEquiv
    (PartitionNormalization.sheetRelabeling data other hVertices hEdges) hConnected).trans
    (Equiv.cast (congrArg StablePath
      (PartitionNormalization.sheetRelabeling_apply data other hVertices hEdges)))

/-- The row transport is the quotient of that actual surviving occurrence
map, not a finite row equivalence selected from cardinalities. -/
theorem stablePathEquiv_mk (hConnected : data.Connected) (edge : NonDanglingEdge data) :
    stablePathEquiv data other hVertices hEdges hConnected edge.stablePath =
      (nonDanglingEdgeEquiv data other hVertices hEdges hConnected edge).stablePath := by
  unfold stablePathEquiv nonDanglingEdgeEquiv
  rw [Equiv.trans_apply, Equiv.trans_apply,
    stablePath_cast (PartitionNormalization.sheetRelabeling_apply data other hVertices hEdges)]
  rfl

theorem nonDanglingEdgeEquiv_sourceEdge_val (hConnected : data.Connected)
    (edge : target.edges) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling data (data.sourceEdge edge sheet)) :
    (nonDanglingEdgeEquiv data other hVertices hEdges hConnected
      ⟨data.sourceEdge edge sheet, hSurvives⟩).1.1 =
        (edge, (other.edgePartition edge).repr sheet) := by
  exact (edge_val_cast
    (PartitionNormalization.sheetRelabeling_apply data other hVertices hEdges)
    ((SheetRelabelStable.nonDanglingEdgeEquiv
      (PartitionNormalization.sheetRelabeling data other hVertices hEdges) hConnected)
      ⟨data.sourceEdge edge sheet, hSurvives⟩)).trans
    (PartitionNormalization.sourceEdgeEquiv_sourceEdge_val data other hVertices hEdges edge sheet)

theorem matrix_map (hConnected : data.Connected) (path : StablePath data) (edge : target.edges) :
    matrix other (stablePathEquiv data other hVertices hEdges hConnected path) edge =
      matrix data path edge := by
  unfold stablePathEquiv
  rw [Equiv.trans_apply,
    matrix_cast (PartitionNormalization.sheetRelabeling_apply data other hVertices hEdges)]
  exact SheetRelabelStable.matrix_map _ hConnected path edge

/-- The same literal normalization supplies the stable incidence certificate. -/
noncomputable def graphEquivalence (hConnected : data.Connected) :
    StableGraphIncidence.Equivalence data other :=
  PartitionNormalization.sheetRelabeling_apply data other hVertices hEdges ▸
    StableGraphIncidence.sheetRelabel
      (PartitionNormalization.sheetRelabeling data other hVertices hEdges) hConnected

/-- The incidence certificate uses exactly the occurrence-induced row map. -/
theorem graphEquivalence_row (hConnected : data.Connected) :
    (graphEquivalence data other hVertices hEdges hConnected).row =
      stablePathEquiv data other hVertices hEdges hConnected := by
  unfold graphEquivalence
  rw [graph_cast_row]
  rfl

section Presentation

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

private theorem presentation_cast_matrix {first second : GluingDatum target degree}
    (h : first = second) (source : FullDimensionalSourcePresentation first coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix
        (h ▸ source : FullDimensionalSourcePresentation second coordinate).labelling.presentation =
      GluingDatum.LengthMatrixPresentation.matrix source.labelling.presentation := by
  cases h
  rfl

private theorem presentation_cast_targetEdge {first second : GluingDatum target degree}
    (h : first = second) (source : FullDimensionalSourcePresentation first coordinate) :
    (h ▸ source : FullDimensionalSourcePresentation second coordinate).labelling.targetEdge =
      source.labelling.targetEdge := by
  cases h
  rfl

/-- Full-dimensionality is transported by actual relabelling and equality;
the structural properties are not new hypotheses. -/
noncomputable def presentation (source : FullDimensionalSourcePresentation data coordinate) :
    FullDimensionalSourcePresentation other coordinate :=
  PartitionNormalization.sheetRelabeling_apply data other hVertices hEdges ▸
    RelabelFullDimensional.sheetPresentation
      (PartitionNormalization.sheetRelabeling data other hVertices hEdges) source

theorem presentation_matrix_eq (source : FullDimensionalSourcePresentation data coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix
        (presentation data other hVertices hEdges source).labelling.presentation =
      GluingDatum.LengthMatrixPresentation.matrix source.labelling.presentation := by
  unfold presentation
  rw [presentation_cast_matrix]
  exact RelabelFullDimensional.sheet_matrix_eq _ source.valid.1 source.labelling

theorem presentation_targetEdge (source : FullDimensionalSourcePresentation data coordinate) :
    (presentation data other hVertices hEdges source).labelling.targetEdge =
      source.labelling.targetEdge := by
  unfold presentation
  rw [presentation_cast_targetEdge]
  rfl

end Presentation

end DraismaVargas.LocalCases.PartitionStableNormalization
