import DraismaVargas.LocalCases.CycleRows
import DraismaVargas.LocalCases.MonovalentWall

/-!
# A non-collapsed stable metric forces forest contraction fibres

The source argument is simple: a cycle in the zero-length subgraph would
contain a whole stable edge, whose prescribed length is nonzero. `CycleRows`
already proves the incidence half. Here it is consumed directly on an actual
gluing datum and metric, without requiring a candidate resolution, requested
graph dictionary, or an assumed contraction forest. Dangling edges may have
positive length, and surviving segments may vanish.

This supplies the forest hypothesis for a wall reached from an honest stable
presentation whose stable lengths remain nonzero. It does not identify the
stable source after contraction or prove inherited rectangular rank.
-/

namespace DraismaVargas.LocalCases.SourceFibreForest

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum.NonnegativeIntegralRealization
open DraismaVargas.LocalCases.TraversalPresentation
open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- If each honest stable row retains one positive-length occurrence, no
cycle can lie entirely in the zero subgraph. -/
theorem isForest_of_nonzero_rows (strong : StrongPresentation data coordinate)
    (realization : data.NonnegativeIntegralRealization)
    (hRows : ∀ row, ∃ edge ∈ strong.toPresentation.path row,
      realization.sourceLength edge ≠ 0) :
    IsForest (UnitSubdivisionPresentation.core data.sourceGraph)
      realization.sourceZeroSet := by
  by_contra hNot
  obtain ⟨row, hRow⟩ := CycleRows.row_subset_of_not_isForest
    strong.decomposes strong.chain realization realization.sourceZeroSet hNot
  obtain ⟨edge, hMem, hLength⟩ := hRows row
  have hZero := (realization.mem_sourceZeroSet _).mp (hRow edge hMem)
  rw [← GluingDatum.NonnegativeIntegralRealization.sourceSlotEquiv_apply,
    Equiv.apply_symm_apply] at hZero
  exact hLength hZero

/-- The metric form of the source's forest argument. The row vector is the
actual stable-length matrix times the nonnegative target coordinates. -/
theorem isForest_of_nonnegative_metric
    (strong : StrongPresentation data coordinate) (coordinates : coordinate → ℚ)
    (hNonnegative : ∀ column, 0 ≤ coordinates column)
    (hRows : ∀ row,
      (GluingDatum.LengthMatrixPresentation.matrix strong.toPresentation).mulVec
        coordinates row ≠ 0) :
    IsForest (UnitSubdivisionPresentation.core data.sourceGraph)
      (GluingDatum.NonnegativeIntegralRealization.ofNonnegativeRational data
        (fun edge ↦ coordinates (strong.toPresentation.targetEdge.symm edge))
        (fun edge ↦ hNonnegative (strong.toPresentation.targetEdge.symm edge))).sourceZeroSet := by
  apply isForest_of_nonzero_rows strong
  intro row
  by_contra hNone
  push Not at hNone
  apply hRows row
  rw [GluingDatum.LengthMatrixPresentation.matrix_mulVec]
  unfold GluingDatum.sourcePathLength
  apply List.sum_eq_zero
  intro term hTerm
  obtain ⟨edge, hEdge, rfl⟩ := List.mem_map.mp hTerm
  have hZero := (ofNonnegativeRational_sourceLength_eq_zero_iff data
      (fun edge ↦ coordinates (strong.toPresentation.targetEdge.symm edge))
      (fun edge ↦ hNonnegative (strong.toPresentation.targetEdge.symm edge)) edge).mp
        (hNone edge hEdge)
  simp only [GluingDatum.sourceEdgeLength, hZero, zero_div]

/-- A vanishing target edge in a non-collapsed stable metric has a forest
source fibre. This derives the hypothesis used by the W2/W3/W4 bridges. -/
theorem contractionForest_of_nonnegative_metric
    (strong : StrongPresentation data coordinate) (coordinates : coordinate → ℚ)
    (hNonnegative : ∀ column, 0 ≤ coordinates column)
    (hRows : ∀ row,
      (GluingDatum.LengthMatrixPresentation.matrix strong.toPresentation).mulVec
        coordinates row ≠ 0)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b))
    (hZero : coordinates (strong.toPresentation.targetEdge.symm contracted) = 0) :
    ContractionRamification.ContractionForest data a b contracted := by
  apply ZeroForestBridge.contractionForest_of_isForest_of_targetLength_eq_zero data
    (GluingDatum.NonnegativeIntegralRealization.ofNonnegativeRational data
      (fun edge ↦ coordinates (strong.toPresentation.targetEdge.symm edge))
      (fun edge ↦ hNonnegative (strong.toPresentation.targetEdge.symm edge))) hc
  · exact (ofNonnegativeRational_targetLength_eq_zero_iff _ _ _ _).mpr hZero
  · exact isForest_of_nonnegative_metric strong coordinates hNonnegative hRows

/-- The full-dimensional package supplies the honest stable rows. No forest
receipt or graph-identification dictionary is added as a hypothesis. -/
theorem contractionForest_of_fullDimensional
    (fullDim : FullDimensionalSource.FullDimensionalSourcePresentation data coordinate)
    (coordinates : coordinate → ℚ) (hNonnegative : ∀ column, 0 ≤ coordinates column)
    (hRows : ∀ row,
      (GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation).mulVec
        coordinates row ≠ 0)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b))
    (hZero : coordinates (fullDim.labelling.targetEdge.symm contracted) = 0) :
    ContractionRamification.ContractionForest data a b contracted := by
  apply contractionForest_of_nonnegative_metric (ofFullDimensional fullDim)
    coordinates hNonnegative ?_ hc hZero
  simpa only [ofFullDimensional, matrix_ofLabelling] using hRows

/-- At an actual nonnegative wall metric with nonzero prescribed stable
lengths, W2/W3/W4 exhaust the target valencies without assuming `ContractionForest`. -/
theorem wall_valencies_of_nonnegative_metric
    (fullDim : FullDimensionalSource.FullDimensionalSourcePresentation data coordinate)
    (coordinates : coordinate → ℚ) (hNonnegative : ∀ column, 0 ≤ coordinates column)
    (hRows : ∀ row,
      (GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation).mulVec
        coordinates row ≠ 0)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (hZero : coordinates (fullDim.labelling.targetEdge.symm contracted) = 0) :
    (GluingDatum.incidentEdges
        (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card = 2 ∨
      (GluingDatum.incidentEdges
          (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card = 3 ∨
        (GluingDatum.incidentEdges
          (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card = 4 :=
  MonovalentWall.card_incidentEdges_merge_eq_two_three_or_four data hc hab hOne fullDim
    (contractionForest_of_fullDimensional fullDim coordinates hNonnegative hRows hc hZero)

end DraismaVargas.LocalCases.SourceFibreForest
