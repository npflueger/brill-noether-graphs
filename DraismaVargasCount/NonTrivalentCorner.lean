module

public import DraismaVargasCount.NonTrivalentBalance
public import DraismaVargasCount.SharpRowDenominator

@[expose] public section

/-!
# Actual full-dimensional corner and leaf-column receipts

For a row supported on one target column, the corner is exactly 2 when that
column is leaf-incident, and otherwise is the reciprocal of the index of its
unique occurrence. In particular the leaf corner has numerator 2 and row
denominator 1, not a reciprocal of a positive natural number.

The leaf column is zero on every other row, so deleting that column preserves
every nonfacet row denominator. These feed the multiplicity balance at a type
change; the nonleaf nonfacet denominators are treated in
`NonTrivalentNonfacetDenominator`.
-/

namespace DraismaVargas.Count.NonTrivalentCorner

open DraismaVargas.Infrastructure
open GluingDatum.LengthMatrixPresentation
open DraismaVargas.LocalCases
open W4StableSource FullDimensionalSource
open LeafFibre EdgeDenominator

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

omit [Fintype coordinate] in
/-- A displayed surviving occurrence contributes a strictly positive entry. -/
theorem matrix_pos_of_mem_rowEdges
    (labelling : StableLengthMatrixLabelling data coordinate)
    {row : coordinate} {edge : data.SourceEdge} (hEdge : edge ∈ rowEdges labelling row) :
    0 < matrix labelling.presentation row (labelling.targetEdge.symm edge.1.1) := by
  rw [matrix_eq_sum_fibre]
  apply Finset.sum_pos'
  · intro item _
    exact le_of_lt (one_div_pos.mpr (by exact_mod_cast data.sourceEdgeIndex_pos item))
  · refine ⟨edge, (mem_rowFibre_iff _ _ _ _).mpr ⟨hEdge, rfl⟩, ?_⟩
    exact one_div_pos.mpr (by exact_mod_cast data.sourceEdgeIndex_pos edge)

omit [Fintype coordinate] in
/-- Every occurrence of a supported row lies above its supporting column. -/
theorem target_eq_of_supported
    (labelling : StableLengthMatrixLabelling data coordinate) {row col : coordinate}
    (hSupport : ∀ j, j ≠ col → matrix labelling.presentation row j = 0)
    {edge : data.SourceEdge} (hEdge : edge ∈ rowEdges labelling row) :
    edge.1.1 = labelling.targetEdge col := by
  have hPos := matrix_pos_of_mem_rowEdges labelling hEdge
  have hCol : labelling.targetEdge.symm edge.1.1 = col := by
    by_contra hNe
    rw [hSupport _ hNe] at hPos
    exact (lt_irrefl _ hPos)
  exact (Equiv.apply_symm_apply _ _).symm.trans (congrArg labelling.targetEdge hCol)

/-- A supported row in a nonsingular matrix has nonzero corner. -/
theorem corner_ne_zero (fd : FullDimensionalSourcePresentation data coordinate)
    {row col : coordinate}
    (hSupport : ∀ j, j ≠ col → matrix fd.labelling.presentation row j = 0) :
    matrix fd.labelling.presentation row col ≠ 0 := by
  intro hZero
  apply fd.det_ne_zero
  rw [NonTrivalentLinkMatrix.det_eq_corner_mul_cofactor hSupport, hZero, zero_mul]

/-- A nonleaf supporting column forces the entire supported row to avoid leaves. -/
theorem not_passesAboveLeaf_of_supported
    (fd : FullDimensionalSourcePresentation data coordinate) {row col : coordinate}
    (hSupport : ∀ j, j ≠ col → matrix fd.labelling.presentation row j = 0)
    (hNonleaf : col ∉ leafColumns fd.labelling.presentation) :
    ¬ PassesAboveLeaf fd.labelling row := by
  rintro ⟨edge, hEdge, vertex, hLeaf, hIncident⟩
  apply hNonleaf
  apply (mem_leafColumns _ _).mpr
  refine ⟨vertex, hLeaf, ?_⟩
  have hTarget := target_eq_of_supported fd.labelling hSupport hEdge
  rwa [hTarget] at hIncident

/-- The supported row at a leaf column is exactly that leaf's unique row. -/
theorem row_eq_leafRow_of_supported
    (fd : FullDimensionalSourcePresentation data coordinate) {row col : coordinate}
    (hSupport : ∀ j, j ≠ col → matrix fd.labelling.presentation row j = 0)
    {vertex : target.V} (hLeaf : IsLeafVertex target vertex)
    (hColumn : fd.labelling.targetEdge col ∈ GluingDatum.incidentEdges vertex) :
    row = leafRow fd hLeaf := by
  have hEdge := eq_leafEdge_of_mem hLeaf hColumn
  have hCol : col = fd.labelling.targetEdge.symm (leafEdge hLeaf) := by
    apply fd.labelling.targetEdge.injective
    simpa only [Equiv.apply_symm_apply] using hEdge
  have hValue := matrix_leafEdge_column fd hLeaf row
  rw [← hCol] at hValue
  by_contra hNe
  rw [ite_eq_right hNe] at hValue
  exact corner_ne_zero fd hSupport hValue

/-- The actual leaf corner is 2. No single-occurrence receipt is assumed. -/
theorem corner_eq_two_of_leaf
    (fd : FullDimensionalSourcePresentation data coordinate) {row col : coordinate}
    (hSupport : ∀ j, j ≠ col → matrix fd.labelling.presentation row j = 0)
    (hLeafColumn : col ∈ leafColumns fd.labelling.presentation) :
    matrix fd.labelling.presentation row col = 2 := by
  obtain ⟨vertex, hLeaf, hColumn⟩ := (mem_leafColumns _ _).mp hLeafColumn
  change fd.labelling.targetEdge col ∈ GluingDatum.incidentEdges vertex at hColumn
  have hRow := row_eq_leafRow_of_supported fd hSupport hLeaf hColumn
  have hEdge := eq_leafEdge_of_mem hLeaf hColumn
  have h := matrix_leafEdge_column fd hLeaf row
  rw [ite_eq_left hRow, ← hEdge, Equiv.symm_apply_apply] at h
  exact h

/-- A nonleaf supported row has one actual occurrence and a reciprocal corner. -/
theorem corner_eq_reciprocal_of_nonleaf
    (fd : FullDimensionalSourcePresentation data coordinate) {row col : coordinate}
    (hSupport : ∀ j, j ≠ col → matrix fd.labelling.presentation row j = 0)
    (hNonleaf : col ∉ leafColumns fd.labelling.presentation) :
    ∃ edge ∈ rowEdges fd.labelling row,
      rowFibre fd.labelling row (fd.labelling.targetEdge col) = {edge} ∧
      matrix fd.labelling.presentation row col = 1 / (data.sourceEdgeIndex edge : ℚ) := by
  classical
  obtain ⟨edge, hEdge⟩ := SharpRowDenominator.rowEdges_nonempty fd.labelling row
  have hTarget := target_eq_of_supported fd.labelling hSupport hEdge
  have hFibre := SharpRowDenominator.rowFibre_eq_singleton_of_not_passesAboveLeaf fd
    (not_passesAboveLeaf_of_supported fd hSupport hNonleaf) hEdge
  rw [hTarget] at hFibre
  refine ⟨edge, hEdge, hFibre, ?_⟩
  rw [matrix_eq_sum_rowFibre, hFibre, Finset.sum_singleton]

/-- The exact corner numerator: 2 on a leaf column, 1 otherwise. -/
theorem corner_num (fd : FullDimensionalSourcePresentation data coordinate)
    {row col : coordinate}
    (hSupport : ∀ j, j ≠ col → matrix fd.labelling.presentation row j = 0) :
    (matrix fd.labelling.presentation row col).num =
      if col ∈ leafColumns fd.labelling.presentation then 2 else 1 := by
  classical
  by_cases hLeaf : col ∈ leafColumns fd.labelling.presentation
  · rw [ite_eq_left hLeaf, corner_eq_two_of_leaf fd hSupport hLeaf]
    norm_num
  · rw [ite_eq_right hLeaf]
    obtain ⟨edge, _, _, hCorner⟩ := corner_eq_reciprocal_of_nonleaf fd hSupport hLeaf
    exact NonTrivalentBalance.num_eq_one_of_eq_one_div (data.sourceEdgeIndex_pos edge) hCorner

/-- A leaf-incident supported row has denominator one, despite its corner 2. -/
theorem rowDenominator_facet_leaf
    (fd : FullDimensionalSourcePresentation data coordinate) {row col : coordinate}
    (hSupport : ∀ j, j ≠ col → matrix fd.labelling.presentation row j = 0)
    (hLeafColumn : col ∈ leafColumns fd.labelling.presentation) :
    rowDenominator fd.labelling.presentation row = 1 := by
  rw [NonTrivalentBalance.rowDenominator_eq_den_corner _ hSupport,
    corner_eq_two_of_leaf fd hSupport hLeafColumn]
  norm_num

/-- Every other row is zero at a leaf supporting column. -/
theorem nonfacet_entry_eq_zero_of_leaf
    (fd : FullDimensionalSourcePresentation data coordinate) {facet col row : coordinate}
    (hSupport : ∀ j, j ≠ col → matrix fd.labelling.presentation facet j = 0)
    (hLeafColumn : col ∈ leafColumns fd.labelling.presentation) (hRow : row ≠ facet) :
    matrix fd.labelling.presentation row col = 0 := by
  obtain ⟨vertex, hLeaf, hColumn⟩ := (mem_leafColumns _ _).mp hLeafColumn
  change fd.labelling.targetEdge col ∈ GluingDatum.incidentEdges vertex at hColumn
  have hFacet := row_eq_leafRow_of_supported fd hSupport hLeaf hColumn
  have hEdge := eq_leafEdge_of_mem hLeaf hColumn
  have h := matrix_leafEdge_column fd hLeaf row
  rw [← hEdge, Equiv.symm_apply_apply, ite_eq_right (hRow.trans_eq hFacet)] at h
  exact h

/-- Deleting an actual zero entry does not change a row denominator. -/
theorem rowDenominator_eq_erase_of_entry_zero
    (presentation : data.LengthMatrixPresentation coordinate) {row col : coordinate}
    (hZero : matrix presentation row col = 0) :
    rowDenominator presentation row =
      commonDenominator (Finset.univ.erase col) (matrix presentation row) := by
  classical
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro j _
    by_cases hEq : j = col
    · subst j
      rw [hZero]
      simp
    · exact den_dvd_commonDenominator _ _ (Finset.mem_erase.mpr ⟨hEq, Finset.mem_univ _⟩)
  · apply Finset.lcm_dvd
    intro j _
    exact den_dvd_commonDenominator _ _ (Finset.mem_univ _)

/-- The leaf case of the nonfacet denominator erasure at a type change, on actual FD data. -/
theorem nonfacet_rowDenominator_eq_erase_of_leaf
    (fd : FullDimensionalSourcePresentation data coordinate) {facet col row : coordinate}
    (hSupport : ∀ j, j ≠ col → matrix fd.labelling.presentation facet j = 0)
    (hLeafColumn : col ∈ leafColumns fd.labelling.presentation) (hRow : row ≠ facet) :
    rowDenominator fd.labelling.presentation row =
      commonDenominator (Finset.univ.erase col) (matrix fd.labelling.presentation row) :=
  rowDenominator_eq_erase_of_entry_zero _
    (nonfacet_entry_eq_zero_of_leaf fd hSupport hLeafColumn hRow)


section Landed

open OuterWalk

variable {κ : Type} [Fintype κ] [DecidableEq κ]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {ambient : Infrastructure.CubicDarts.CubicDartGraph D V}
  {label : D → κ} {m : ambient.MoveData}
  {arrival : FacetArrival degree ambient label (label m.base)}
  {wd : WallData arrival} (link : TypeChangeLink m wd)

/-- The actual incoming corner numerator, including its leaf value 2. -/
theorem incoming_corner_num :
    (wd.incomingMatrix (label m.base) wd.column).num =
      if wd.column ∈ leafColumns wd.fullDim.labelling.presentation then 2 else 1 :=
  corner_num wd.fullDim wd.incomingMatrix_facet_eq_zero

/-- The actual outgoing corner numerator, including its leaf value 2. -/
theorem outgoing_corner_num :
    (link.outgoingMatrix (label m.base) wd.column).num =
      if wd.column ∈ leafColumns link.outgoingFD.labelling.presentation then 2 else 1 :=
  corner_num link.outgoingFD link.outgoingMatrix_facet_eq_zero

/-- The nonfacet row denominators at a type change agree whenever both contracted
columns are leaf-incident. No per-row denominator receipt is supplied. -/
theorem nonfacet_rowDenominator_eq_of_both_leaf
    (hIncoming : wd.column ∈ leafColumns wd.fullDim.labelling.presentation)
    (hOutgoing : wd.column ∈ leafColumns link.outgoingFD.labelling.presentation)
    {row : κ} (hRow : row ≠ label m.base) :
    rowDenominator link.outgoingFD.labelling.presentation row =
      rowDenominator wd.fullDim.labelling.presentation row := by
  rw [nonfacet_rowDenominator_eq_erase_of_leaf link.outgoingFD
      link.outgoingMatrix_facet_eq_zero hOutgoing hRow,
    nonfacet_rowDenominator_eq_erase_of_leaf wd.fullDim
      wd.incomingMatrix_facet_eq_zero hIncoming hRow]
  apply Finset.lcm_congr rfl
  intro j hj
  exact congrArg Rat.den (link.agree row j (Finset.mem_erase.mp hj).1).symm

/-- The complete nonfacet denominator-product identity at a type change, in the
leaf/leaf case. -/
theorem nonfacet_product_eq_of_both_leaf
    (hIncoming : wd.column ∈ leafColumns wd.fullDim.labelling.presentation)
    (hOutgoing : wd.column ∈ leafColumns link.outgoingFD.labelling.presentation) :
    ∏ row ∈ Finset.univ.erase (label m.base),
        rowDenominator link.outgoingFD.labelling.presentation row =
      ∏ row ∈ Finset.univ.erase (label m.base),
        rowDenominator wd.fullDim.labelling.presentation row := by
  apply Finset.prod_congr rfl
  intro row hRow
  exact nonfacet_rowDenominator_eq_of_both_leaf link hIncoming hOutgoing
    (Finset.mem_erase.mp hRow).1

end Landed

end DraismaVargas.Count.NonTrivalentCorner

