module

public import DraismaVargasCount.NonTrivalentCorner
public import DraismaVargasCount.Integrality

@[expose] public section

/-!
# Matrix-intrinsic leaf columns and the normalized non-trivalent corner

In a full-dimensional stable length matrix, the leaf columns are exactly the
columns equal to twice a basis vector. Thus agreement off the contracted column
preserves every other leaf-column flag. The exceptional corner numerator is
2 on a leaf column and 1 otherwise, so its change exactly cancels the change
in the target leaf count. Hence the comparison of signed multiplicities across a
non-trivalent limit (Vargas, Part II, `lm:change-comb-type`) needs no separate leaf or
numerator hypothesis, even across a mixed leaf/nonleaf transition: its only other input
is the invariance of the product of the nonfacet row denominators, proved in
`NonTrivalentNonfacetDenominator`.
-/

namespace DraismaVargas.Count.NonTrivalentLeafNormalization

open DraismaVargas.Infrastructure
open GluingDatum.LengthMatrixPresentation
open DraismaVargas.LocalCases
open W4StableSource FullDimensionalSource NonTrivalentLinkMatrix
open LeafFibre EdgeDenominator NonTrivalentCorner

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- Every entry of a leaf-avoiding full-dimensional row is at most one. -/
theorem matrix_le_one_of_not_passesAboveLeaf
    (fd : FullDimensionalSourcePresentation data coordinate) {row : coordinate}
    (hAvoid : ¬ PassesAboveLeaf fd.labelling row) (col : coordinate) :
    matrix fd.labelling.presentation row col ≤ 1 := by
  classical
  by_cases hEmpty : rowFibre fd.labelling row (fd.labelling.targetEdge col) = ∅
  · rw [matrix_eq_sum_rowFibre, hEmpty, Finset.sum_empty]
    norm_num
  · obtain ⟨edge, hEdge⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
    obtain ⟨hRow, hTarget⟩ := (mem_rowFibre_iff _ _ _ _).mp hEdge
    have hFibre := SharpRowDenominator.rowFibre_eq_singleton_of_not_passesAboveLeaf
      fd hAvoid hRow
    rw [hTarget] at hFibre
    rw [matrix_eq_sum_rowFibre, hFibre, Finset.sum_singleton]
    apply (div_le_iff₀ (by exact_mod_cast data.sourceEdgeIndex_pos edge)).mpr
    simpa only [one_mul] using
      (show (1 : ℚ) ≤ data.sourceEdgeIndex edge by exact_mod_cast data.sourceEdgeIndex_pos edge)

/-- Leaf incidence is determined by the honest matrix, not extra target data. -/
theorem mem_leafColumns_iff_basis_two
    (fd : FullDimensionalSourcePresentation data coordinate) (col : coordinate) :
    col ∈ leafColumns fd.labelling.presentation ↔
      ∃ row : coordinate, ∀ i : coordinate,
        matrix fd.labelling.presentation i col = if i = row then 2 else 0 := by
  classical
  constructor
  · intro hLeafColumn
    obtain ⟨vertex, hLeaf, hColumn⟩ := (mem_leafColumns _ _).mp hLeafColumn
    change fd.labelling.targetEdge col ∈ GluingDatum.incidentEdges vertex at hColumn
    have hEdge := eq_leafEdge_of_mem hLeaf hColumn
    refine ⟨leafRow fd hLeaf, fun i ↦ ?_⟩
    have h := matrix_leafEdge_column fd hLeaf i
    rwa [← hEdge, Equiv.symm_apply_apply] at h
  · rintro ⟨row, hColumn⟩
    have hPasses : PassesAboveLeaf fd.labelling row := by
      by_contra hAvoid
      have hLe := matrix_le_one_of_not_passesAboveLeaf fd hAvoid col
      rw [hColumn row, ite_eq_left rfl] at hLe
      norm_num at hLe
    obtain ⟨vertex, hLeaf, hRow⟩ := exists_eq_leafRow_of_passesAboveLeaf fd hPasses
    have hCol : col = fd.labelling.targetEdge.symm (leafEdge hLeaf) := by
      by_contra hNe
      apply fd.det_ne_zero
      apply Matrix.det_zero_of_column_eq hNe
      intro i
      rw [hColumn i, matrix_leafEdge_column fd hLeaf, hRow]
    apply (mem_leafColumns _ _).mpr
    refine ⟨vertex, hLeaf, ?_⟩
    change fd.labelling.targetEdge col ∈ GluingDatum.incidentEdges vertex
    rw [hCol, Equiv.apply_symm_apply]
    exact leafEdge_mem hLeaf

section Compare

variable {targetIn targetOut : CFGraph.{0}} {degIn degOut : ℕ}
  {dataIn : GluingDatum targetIn degIn} {dataOut : GluingDatum targetOut degOut}
  (fdIn : FullDimensionalSourcePresentation dataIn coordinate)
  (fdOut : FullDimensionalSourcePresentation dataOut coordinate)
  {col : coordinate}
  (hAgree : AgreeOffColumn (matrix fdIn.labelling.presentation)
    (matrix fdOut.labelling.presentation) col)

include hAgree

/-- Every retained column keeps its leaf flag across matrix agreement. -/
theorem leafColumn_iff_of_ne {j : coordinate} (hNe : j ≠ col) :
    j ∈ leafColumns fdOut.labelling.presentation ↔
      j ∈ leafColumns fdIn.labelling.presentation := by
  rw [mem_leafColumns_iff_basis_two, mem_leafColumns_iff_basis_two]
  constructor
  · rintro ⟨row, h⟩
    exact ⟨row, fun i ↦ (hAgree i j hNe).trans (h i)⟩
  · rintro ⟨row, h⟩
    exact ⟨row, fun i ↦ (hAgree i j hNe).symm.trans (h i)⟩

/-- The retained leaf-column sets are literally identical. -/
theorem erase_leafColumns_eq :
    (leafColumns fdOut.labelling.presentation).erase col =
      (leafColumns fdIn.labelling.presentation).erase col := by
  classical
  ext j
  simp only [Finset.mem_erase]
  constructor
  · rintro ⟨hNe, hMem⟩
    exact ⟨hNe, (leafColumn_iff_of_ne fdIn fdOut hAgree hNe).mp hMem⟩
  · rintro ⟨hNe, hMem⟩
    exact ⟨hNe, (leafColumn_iff_of_ne fdIn fdOut hAgree hNe).mpr hMem⟩

/-- Leaf counts may change, but only by the contracted column's leaf flag. -/
theorem leafCount_add_flag :
    leafCount targetOut + (if col ∈ leafColumns fdIn.labelling.presentation then 1 else 0) =
      leafCount targetIn + (if col ∈ leafColumns fdOut.labelling.presentation then 1 else 0) := by
  classical
  have hErase := congrArg Finset.card (erase_leafColumns_eq fdIn fdOut hAgree)
  rw [← leafColumns_card_eq_leafCount_of_fullDimensional fdIn,
    ← leafColumns_card_eq_leafCount_of_fullDimensional fdOut]
  by_cases hIn : col ∈ leafColumns fdIn.labelling.presentation <;>
    by_cases hOut : col ∈ leafColumns fdOut.labelling.presentation
  · rw [ite_eq_left hIn, ite_eq_left hOut]
    have hI := Finset.card_erase_add_one hIn
    have hO := Finset.card_erase_add_one hOut
    omega
  · rw [ite_eq_left hIn, ite_eq_right hOut]
    rw [Finset.erase_eq_of_notMem hOut] at hErase
    have hI := Finset.card_erase_add_one hIn
    omega
  · rw [ite_eq_right hIn, ite_eq_left hOut]
    rw [Finset.erase_eq_of_notMem hIn] at hErase
    have hO := Finset.card_erase_add_one hOut
    omega
  · rw [ite_eq_right hIn, ite_eq_right hOut]
    simpa only [Finset.erase_eq_of_notMem hIn, Finset.erase_eq_of_notMem hOut,
      Nat.add_zero] using hErase

/-- The corner numerator divided by the leaf factor is unchanged, even across
a mixed leaf/nonleaf transition. -/
theorem normalized_corner_num_eq {row : coordinate}
    (hIn : ∀ j, j ≠ col → matrix fdIn.labelling.presentation row j = 0)
    (hOut : ∀ j, j ≠ col → matrix fdOut.labelling.presentation row j = 0) :
    ((matrix fdOut.labelling.presentation row col).num : ℚ) / 2 ^ leafCount targetOut =
      ((matrix fdIn.labelling.presentation row col).num : ℚ) / 2 ^ leafCount targetIn := by
  classical
  have hCount := leafCount_add_flag fdIn fdOut hAgree
  have hNumIn : ((matrix fdIn.labelling.presentation row col).num : ℚ) =
      (2 : ℚ) ^ (if col ∈ leafColumns fdIn.labelling.presentation then 1 else 0 : ℕ) := by
    rw [corner_num fdIn hIn]
    split_ifs <;> norm_num
  have hNumOut : ((matrix fdOut.labelling.presentation row col).num : ℚ) =
      (2 : ℚ) ^ (if col ∈ leafColumns fdOut.labelling.presentation then 1 else 0 : ℕ) := by
    rw [corner_num fdOut hOut]
    split_ifs <;> norm_num
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  rw [hNumIn, hNumOut, ← pow_add, ← pow_add]
  congr 1
  omega

/-- The signed multiplicities agree as soon as the products of the nonfacet row denominators
agree; the leaf counts and corner numerators need no separate hypothesis. -/
theorem signedMult_eq_of_nonfacet_product {row : coordinate}
    (hIn : ∀ j, j ≠ col → matrix fdIn.labelling.presentation row j = 0)
    (hOut : ∀ j, j ≠ col → matrix fdOut.labelling.presentation row j = 0)
    (hOther : ∏ i ∈ Finset.univ.erase row, rowDenominator fdOut.labelling.presentation i =
      ∏ i ∈ Finset.univ.erase row, rowDenominator fdIn.labelling.presentation i) :
    fdSignedMult fdOut = fdSignedMult fdIn := by
  apply NonTrivalentBalance.signedMult_eq_of_weightedCorner _ _ hAgree hIn hOut
    (corner_ne_zero fdIn hIn)
  have hNormalized := normalized_corner_num_eq fdIn fdOut hAgree hIn hOut
  unfold NonTrivalentBalance.weight
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
    NonTrivalentBalance.denominatorProduct_mul_corner _ hOut,
    NonTrivalentBalance.denominatorProduct_mul_corner _ hIn, hOther,
    mul_div_assoc, mul_div_assoc, hNormalized]

end Compare

section Landed

open OuterWalk

variable {κ : Type} [Fintype κ] [DecidableEq κ]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {ambient : Infrastructure.CubicDarts.CubicDartGraph D V}
  {label : D → κ} {m : ambient.MoveData}
  {arrival : FacetArrival degree ambient label (label m.base)}
  {wd : WallData arrival} (link : TypeChangeLink m wd)

/-- Actual type-change links preserve the normalized corner numerator. -/
theorem normalized_corner_num_eq_of_typeChangeLink :
    ((link.outgoingMatrix (label m.base) wd.column).num : ℚ) /
        2 ^ leafCount (TargetExpansion.graph
          (GraphContraction.contract wd.coverTarget wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩ link.candidate.right) =
      ((wd.incomingMatrix (label m.base) wd.column).num : ℚ) /
        2 ^ leafCount wd.coverTarget :=
  normalized_corner_num_eq wd.fullDim link.outgoingFD link.agree
    wd.incomingMatrix_facet_eq_zero link.outgoingMatrix_facet_eq_zero

/-- For actual type-change links: equality of signed multiplicities, with the leaf and
corner-numerator hypotheses discharged. The only hypothesis left is the nonfacet denominator
product (`NonTrivalentNonfacetDenominator.nonfacet_product_eq_of_typeChangeLink`). -/
theorem signedMult_eq_of_typeChangeLink_of_nonfacet_product
    (hOther : ∏ row ∈ Finset.univ.erase (label m.base),
        rowDenominator link.outgoingFD.labelling.presentation row =
      ∏ row ∈ Finset.univ.erase (label m.base),
        rowDenominator wd.fullDim.labelling.presentation row) :
    fdSignedMult link.outgoingFD = fdSignedMult wd.fullDim :=
  signedMult_eq_of_nonfacet_product wd.fullDim link.outgoingFD link.agree
    wd.incomingMatrix_facet_eq_zero link.outgoingMatrix_facet_eq_zero hOther

/-- Equal signed multiplicity across an actual type-change link whose contracted column is a
leaf column on both sides, with no further hypothesis. -/
theorem signedMult_eq_of_typeChangeLink_of_both_leaf
    (hIncoming : wd.column ∈ leafColumns wd.fullDim.labelling.presentation)
    (hOutgoing : wd.column ∈ leafColumns link.outgoingFD.labelling.presentation) :
    fdSignedMult link.outgoingFD = fdSignedMult wd.fullDim :=
  signedMult_eq_of_typeChangeLink_of_nonfacet_product link
    (NonTrivalentCorner.nonfacet_product_eq_of_both_leaf link hIncoming hOutgoing)

end Landed

end DraismaVargas.Count.NonTrivalentLeafNormalization

