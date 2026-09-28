import DraismaVargasCount.OutgoingRowCalculus

/-!
# Sharp row denominators of full-dimensional covers

`EdgeDenominator` proves the sharp values of the row denominators given simple
columns; this module constructs those simple columns.
A leaf-avoiding stable row is a non-returning target walk, hence every target
column it meets contains exactly one occurrence. A ramified occurrence itself
certifies leaf avoidance. Consequently every displayed index divides the row
denominator, with index one handled trivially even on a folded leaf row.

Combining this lower bound with the denominator upper bounds of `EdgeDenominator`
gives the exact values `k` and `k(k+1)`. The ordered-row argument supplies
consecutive indices from full dimensionality, so the final sharp trichotomy
has no simple-column, index-pattern, target-simplicity, or tameness hypothesis.

Source: Vargas, Part II (arXiv:2609.09109), the lemma on edge denominators
(`lemma-edge-deno`). The global
walk and no-return inputs are `RowWalk` and `RowGeodesic`; nothing is assumed
about a codimension-one datum or a singular outgoing member.
-/

namespace DraismaVargas.Count.SharpRowDenominator

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.EdgeDenominator
open DraismaVargas.Count.LeafFibre
open DraismaVargas.Count.RowWalk

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

omit [Fintype coordinate] in
/-- An actual stable row contains an occurrence. -/
theorem rowEdges_nonempty (labelling : StableLengthMatrixLabelling data coordinate)
    (sourceRow : coordinate) : (rowEdges labelling sourceRow).Nonempty := by
  obtain ⟨edge, hEdge⟩ := Quot.exists_rep (labelling.row.symm sourceRow)
  refine ⟨edge.1, (mem_rowEdges_iff_onRow labelling sourceRow edge.1).mpr ?_⟩
  exact ⟨edge.2, hEdge⟩

/-- Leaf avoidance is all that the non-returning target-walk argument needs;
the other inputs are fields of the full-dimensional presentation. -/
theorem rowTargetInjective_of_not_passesAboveLeaf
    (fd : FullDimensionalSourcePresentation data coordinate) {sourceRow : coordinate}
    (hAvoid : ¬ PassesAboveLeaf fd.labelling sourceRow) :
    RowTargetInjective data (fd.labelling.row.symm sourceRow) :=
  RowGeodesic.rowTargetInjective_of_genusZero fd.targetConnected fd.targetGenus
    fd.danglingEdgeNoGlue fd.pathEnds
    (rowRamificationAtMostOne_of_rowAvoidsLeaves fd
      ((rowAvoidsLeaves_iff_not_passesAboveLeaf fd.labelling sourceRow).mpr hAvoid))

/-- Every column visited by a leaf-avoiding row is simple. This is the
geometric input the sharp denominator theorems of `EdgeDenominator` take as a hypothesis. -/
theorem rowFibre_eq_singleton_of_not_passesAboveLeaf
    (fd : FullDimensionalSourcePresentation data coordinate) {sourceRow : coordinate}
    (hAvoid : ¬ PassesAboveLeaf fd.labelling sourceRow)
    {edge : data.SourceEdge} (hEdge : edge ∈ rowEdges fd.labelling sourceRow) :
    rowFibre fd.labelling sourceRow edge.1.1 = {edge} := by
  classical
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
  · exact (mem_rowFibre_iff _ _ _ _).mpr ⟨hEdge, rfl⟩
  · intro other hOther
    obtain ⟨hOtherRow, hTarget⟩ := (mem_rowFibre_iff _ _ _ _).mp hOther
    exact rowTargetInjective_of_not_passesAboveLeaf fd hAvoid other edge
      ((mem_rowEdges_iff_onRow _ _ _).mp hOtherRow)
      ((mem_rowEdges_iff_onRow _ _ _).mp hEdge) hTarget

/-- Every displayed dilation index divides the row denominator. If the index
is not one, the occurrence forces leaf avoidance and its own simple column. -/
theorem index_dvd_rowDenominator
    (fd : FullDimensionalSourcePresentation data coordinate) {sourceRow : coordinate}
    {edge : data.SourceEdge} (hEdge : edge ∈ rowEdges fd.labelling sourceRow) :
    data.sourceEdgeIndex edge ∣ rowDenominator fd.labelling.presentation sourceRow := by
  by_cases hOne : data.sourceEdgeIndex edge = 1
  · rw [hOne]
    exact one_dvd _
  have hFibre := rowFibre_eq_singleton_of_not_passesAboveLeaf fd
    (not_passesAboveLeaf_of_index_ne_one fd hEdge hOne) hEdge
  exact dvd_rowDenominator_of_rowFibre_eq_singleton fd.labelling sourceRow
    (fd.labelling.targetEdge.symm edge.1.1) (by simpa only [Equiv.apply_symm_apply] using hFibre)

/-- Lemma `edge-deno` (b), with no simple-column hypothesis. This also covers
unit-index rows passing above a leaf. -/
theorem rowDenominator_eq_of_constant
    (fd : FullDimensionalSourcePresentation data coordinate) (sourceRow : coordinate)
    {index : ℕ} (hConstant : RowIndexConstant fd.labelling sourceRow index) :
    rowDenominator fd.labelling.presentation sourceRow = index := by
  apply Nat.dvd_antisymm (rowDenominator_dvd_of_rowIndexConstant fd.labelling sourceRow hConstant)
  obtain ⟨edge, hEdge⟩ := rowEdges_nonempty fd.labelling sourceRow
  rw [← hConstant edge hEdge]
  exact index_dvd_rowDenominator fd hEdge

/-- Lemma `edge-deno` (c), with both simple columns constructed from the
actual full-dimensional geometry. The two value witnesses are the case itself. -/
theorem rowDenominator_eq_of_two_values
    (fd : FullDimensionalSourcePresentation data coordinate) (sourceRow : coordinate)
    {index : ℕ} (hTwoValued : RowIndexTwoValued fd.labelling sourceRow index)
    (hLow : ∃ edge ∈ rowEdges fd.labelling sourceRow, data.sourceEdgeIndex edge = index)
    (hHigh : ∃ edge ∈ rowEdges fd.labelling sourceRow, data.sourceEdgeIndex edge = index + 1) :
    rowDenominator fd.labelling.presentation sourceRow = index * (index + 1) := by
  apply Nat.dvd_antisymm (rowDenominator_dvd_of_rowIndexTwoValued fd.labelling sourceRow hTwoValued)
  obtain ⟨edgeLow, hLowMem, hLowIndex⟩ := hLow
  obtain ⟨edgeHigh, hHighMem, hHighIndex⟩ := hHigh
  apply (coprime_succ index).mul_dvd_of_dvd_of_dvd
  · rw [← hLowIndex]
    exact index_dvd_rowDenominator fd hLowMem
  · rw [← hHighIndex]
    exact index_dvd_rowDenominator fd hHighMem

/-- The global consecutive-index pattern is supplied by the ordered
row and full-dimensional determinant argument. Target simplicity is derived. -/
theorem rowIndicesConsecutive
    (fd : FullDimensionalSourcePresentation data coordinate) (sourceRow : coordinate) :
    RowIndicesConsecutive fd.labelling sourceRow :=
  rowIndicesConsecutive_of_simpleTarget fd
    (OutgoingRowCalculus.simpleTarget_of_fullDim fd) sourceRow

/-- The full sharp denominator trichotomy on an actual full-dimensional
presentation, with no geometric hypothesis beyond full dimensionality. -/
theorem rowDenominator_trichotomy
    (fd : FullDimensionalSourcePresentation data coordinate) (sourceRow : coordinate) :
    (PassesAboveLeaf fd.labelling sourceRow ∧
        rowDenominator fd.labelling.presentation sourceRow = 1) ∨
      (¬ PassesAboveLeaf fd.labelling sourceRow ∧ ∃ index : ℕ, 0 < index ∧
        RowIndexConstant fd.labelling sourceRow index ∧
        rowDenominator fd.labelling.presentation sourceRow = index) ∨
      (¬ PassesAboveLeaf fd.labelling sourceRow ∧ ∃ index : ℕ, 0 < index ∧
        RowIndexTwoValued fd.labelling sourceRow index ∧
        (∃ edge ∈ rowEdges fd.labelling sourceRow, data.sourceEdgeIndex edge = index) ∧
        (∃ edge ∈ rowEdges fd.labelling sourceRow, data.sourceEdgeIndex edge = index + 1) ∧
        rowDenominator fd.labelling.presentation sourceRow = index * (index + 1)) := by
  rcases EdgeDenominator.rowDenominator_trichotomy fd sourceRow
      (rowIndicesConsecutive fd sourceRow) with hLeaf | hConstant | hTwo
  · exact Or.inl hLeaf
  · obtain ⟨hAvoid, index, hPos, hIndices, _⟩ := hConstant
    exact Or.inr (Or.inl ⟨hAvoid, index, hPos, hIndices,
      rowDenominator_eq_of_constant fd sourceRow hIndices⟩)
  · obtain ⟨hAvoid, index, hPos, hIndices, hLow, hHigh, _⟩ := hTwo
    exact Or.inr (Or.inr ⟨hAvoid, index, hPos, hIndices, hLow, hHigh,
      rowDenominator_eq_of_two_values fd sourceRow hIndices hLow hHigh⟩)

end DraismaVargas.Count.SharpRowDenominator

