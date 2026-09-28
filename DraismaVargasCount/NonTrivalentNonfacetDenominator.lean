import DraismaVargasCount.NonTrivalentLeafNormalization
import DraismaVargasCount.UnitWeightBalance

/-!
# Nonfacet row denominators at a supported facet

A transition along a nonfacet row cannot touch the contracted column: its
column relation would annihilate the nonzero facet corner. Thus a ramified
occurrence over that column continues with the same index into a retained
column. Full dimensionality and the sharp simple-column theorem make that
retained reciprocal visible in the row denominator.
-/

namespace DraismaVargas.Count.NonTrivalentNonfacetDenominator

open DraismaVargas.Infrastructure
open GluingDatum GluingDatum.LengthMatrixPresentation
open DraismaVargas.LocalCases
open W4StableSource FullDimensionalSource StableLocalProperties
open LeafFibre EdgeDenominator NonTrivalentCorner IndexPattern

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- In a nonsingular matrix, another row cannot be supported on the same single
column as a facet row. -/
theorem exists_nonzero_off_support {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℚ) (hDet : A.det ≠ 0) {facet col row : κ}
    (hSupport : ∀ j, j ≠ col → A facet j = 0)
    (hRow : row ≠ facet) : ∃ j, j ≠ col ∧ A row j ≠ 0 := by
  classical
  have hCorner : A facet col ≠ 0 := by
    intro hZero
    apply hDet
    rw [NonTrivalentLinkMatrix.det_eq_corner_mul_cofactor hSupport, hZero, zero_mul]
  by_contra h
  have hZero : ∀ j, j ≠ col → A row j = 0 := by
    intro j hj
    by_contra hEntry
    exact h ⟨j, hj, hEntry⟩
  apply hRow
  apply (Matrix.linearIndependent_rows_of_det_ne_zero hDet).eq_of_smul_apply_eq_smul_apply
    (A facet col) (A row col) row facet hCorner
  ext j
  change A facet col * A row j = A row col * A facet j
  by_cases hj : j = col
  · subst j
    ring
  · rw [hZero j hj, hSupport j hj, mul_zero, mul_zero]

/-- The contracted occurrence cannot be a genuine index transition on a
nonfacet row: the transition's column identity would kill the facet corner. -/
theorem index_eq_of_consecutive_at_supported_column
    (fd : FullDimensionalSourcePresentation data coordinate)
    {facet col row : coordinate}
    (hSupport : ∀ j, j ≠ col → matrix fd.labelling.presentation facet j = 0)
    (hRow : row ≠ facet) {first second : NonDanglingEdge data}
    (hFirstRow : fd.labelling.row first.stablePath = row)
    (hColumn : first.1.1.1 = fd.labelling.targetEdge col)
    (hConsecutive : Consecutive data first second) :
    data.sourceEdgeIndex first.1 = data.sourceEdgeIndex second.1 := by
  classical
  obtain ⟨hNe, vertex, hFirstIncident, hSecondIncident, hValency⟩ := hConsecutive
  have hNeVal : first.1 ≠ second.1 := fun h ↦ hNe (Subtype.ext h)
  by_contra hIndexNe
  have hNotZero : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ ≠ 0 := by
    intro hZero
    exact hIndexNe (sourceEdgeIndex_eq_of_localRamification_eq_zero fd hValency hZero
      first.2 hFirstIncident second.2 hSecondIncident hNeVal)
  have hNonneg := data.localRamification_nonneg vertex.1.1 (fd.valid.2 vertex.1.1)
    ⟨vertex.1.2, vertex.2⟩
  have hPos : 1 ≤ data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ := by omega
  have hValCard := incidentEdges_card_le_two_of_localRamification_pos fd
    ⟨vertex.1.2, vertex.2⟩ hPos
  have hValPos := incidentEdges_card_pos_of_changeMinimalAt data vertex.1.1
    (fd.changeMinimal vertex.1.1)
  interval_cases hCard : (GluingDatum.incidentEdges vertex.1.1).card
  · apply hIndexNe
    rw [sourceEdgeIndex_eq_one_of_target_leaf data fd.valid fd.noDanglingTargetFibres
        vertex hCard (fd.changeMinimal _) ⟨first.1, hFirstIncident⟩,
      sourceEdgeIndex_eq_one_of_target_leaf data fd.valid fd.noDanglingTargetFibres
        vertex hCard (fd.changeMinimal _) ⟨second.1, hSecondIncident⟩]
  · have hRam : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 1 := by
      have hLe := localRamification_le_targetChange fd (wall := vertex.1.1)
        ⟨vertex.1.2, vertex.2⟩
      rw [targetChange_eq_three_sub_valency fd vertex.1.1, hCard] at hLe
      omega
    have hTargetNe := target_ne_of_transition fd hCard hRam hValency
      first.2 hFirstIncident second.2 hSecondIncident hNeVal
    have hColumnNe : fd.labelling.targetEdge.symm second.1.1.1 ≠ col := by
      intro h
      apply hTargetNe
      rw [hColumn, ← h, Equiv.apply_symm_apply]
    have hRelation := matrix_sub_eq_of_transition fd hCard hRam hValency
      first.2 hFirstIncident second.2 hSecondIncident hNeVal facet
    change matrix fd.labelling.presentation facet (fd.labelling.targetEdge.symm first.1.1.1) -
        matrix fd.labelling.presentation facet (fd.labelling.targetEdge.symm second.1.1.1) =
      (if facet = fd.labelling.row first.stablePath then
        (1 : ℚ) / data.sourceEdgeIndex first.1 - 1 / data.sourceEdgeIndex second.1 else 0)
      at hRelation
    rw [hFirstRow, if_neg hRow.symm, hColumn, Equiv.symm_apply_apply,
      hSupport _ hColumnNe, sub_zero] at hRelation
    exact corner_ne_zero fd hSupport hRelation

/-- A non-singleton stable class contains a neighbor of any given occurrence. -/
theorem exists_consecutive_of_same_row_ne {first other : NonDanglingEdge data}
    (hPath : first.stablePath = other.stablePath) (hNe : first ≠ other) :
    ∃ second : NonDanglingEdge data, Consecutive data first second := by
  by_contra hNone
  have hClosed : ∀ a b : NonDanglingEdge data, Consecutive data a b →
      a = first → b = first := by
    intro a b hConsecutive hEq
    subst a
    exact False.elim (hNone ⟨b, hConsecutive⟩)
  have h := (eqvGen_iff_of_closed hClosed ((stablePath_eq_iff first other).mp hPath)).mp rfl
  exact hNe h.symm

/-- A nonzero retained matrix entry supplies an occurrence distinct from any
occurrence over the contracted column, hence a consecutive neighbor. -/
theorem exists_consecutive_of_retained_entry
    (fd : FullDimensionalSourcePresentation data coordinate)
    {row col : coordinate} {first : NonDanglingEdge data}
    (hFirstRow : fd.labelling.row first.stablePath = row)
    (hColumn : first.1.1.1 = fd.labelling.targetEdge col)
    (hRetained : ∃ j, j ≠ col ∧ matrix fd.labelling.presentation row j ≠ 0) :
    ∃ second : NonDanglingEdge data, Consecutive data first second := by
  classical
  obtain ⟨j, hNe, hEntry⟩ := hRetained
  have hNonempty : (rowFibre fd.labelling row (fd.labelling.targetEdge j)).Nonempty := by
    by_contra hEmpty
    rw [matrix_eq_sum_rowFibre, Finset.not_nonempty_iff_eq_empty.mp hEmpty,
      Finset.sum_empty] at hEntry
    exact hEntry rfl
  obtain ⟨other, hOther⟩ := hNonempty
  obtain ⟨hOtherRow, hTarget⟩ := (mem_rowFibre_iff _ _ _ _).mp hOther
  obtain ⟨hSurvives, hRow⟩ := (mem_rowEdges _ _ _).mp hOtherRow
  let other' : NonDanglingEdge data := ⟨other, hSurvives⟩
  apply exists_consecutive_of_same_row_ne (other := other')
  · exact fd.labelling.row.injective (hFirstRow.trans hRow.symm)
  · intro hEq
    have h := congrArg (fun e : NonDanglingEdge data ↦ e.1.1.1) hEq
    change first.1.1.1 = other.1.1 at h
    rw [hColumn, hTarget] at h
    exact hNe (fd.labelling.targetEdge.injective h).symm

/-- The index of a contracted occurrence on a nonfacet row already occurs
as a simple retained-column denominator. Unit indices need no geometry. -/
theorem contracted_index_dvd_retained
    (fd : FullDimensionalSourcePresentation data coordinate)
    {facet col row : coordinate}
    (hSupport : ∀ j, j ≠ col → matrix fd.labelling.presentation facet j = 0)
    (hRow : row ≠ facet)
    (hRetained : ∃ j, j ≠ col ∧ matrix fd.labelling.presentation row j ≠ 0)
    {edge : data.SourceEdge} (hEdge : edge ∈ rowEdges fd.labelling row)
    (hColumn : edge.1.1 = fd.labelling.targetEdge col) :
    data.sourceEdgeIndex edge ∣
      commonDenominator (Finset.univ.erase col) (matrix fd.labelling.presentation row) := by
  classical
  by_cases hOne : data.sourceEdgeIndex edge = 1
  · rw [hOne]
    exact one_dvd _
  have hAvoid := not_passesAboveLeaf_of_index_ne_one fd hEdge hOne
  obtain ⟨hSurvives, hFirstRow⟩ := (mem_rowEdges _ _ _).mp hEdge
  let first : NonDanglingEdge data := ⟨edge, hSurvives⟩
  obtain ⟨second, hConsecutive⟩ := exists_consecutive_of_retained_entry fd
    (first := first) hFirstRow hColumn hRetained
  have hIndex := index_eq_of_consecutive_at_supported_column fd hSupport hRow
    hFirstRow hColumn hConsecutive
  have hSecondRow : fd.labelling.row second.stablePath = row := by
    rw [← stablePath_eq_of_consecutive hConsecutive]
    exact hFirstRow
  have hSecondMem : second.1 ∈ rowEdges fd.labelling row :=
    (mem_rowEdges _ _ _).mpr ⟨second.2, hSecondRow⟩
  have hTargetNe : second.1.1.1 ≠ fd.labelling.targetEdge col := by
    intro h
    have hEq : second.1 = edge :=
      SharpRowDenominator.rowTargetInjective_of_not_passesAboveLeaf fd hAvoid
        second.1 edge ((RowWalk.mem_rowEdges_iff_onRow _ _ _).mp hSecondMem)
        ((RowWalk.mem_rowEdges_iff_onRow _ _ _).mp hEdge) (h.trans hColumn.symm)
    exact hConsecutive.1 (Subtype.ext hEq.symm)
  have hColumnNe : fd.labelling.targetEdge.symm second.1.1.1 ≠ col := by
    intro h
    apply hTargetNe
    rw [← h, Equiv.apply_symm_apply]
  have hFibre := SharpRowDenominator.rowFibre_eq_singleton_of_not_passesAboveLeaf
    fd hAvoid hSecondMem
  have hDen := den_dvd_commonDenominator (Finset.univ.erase col)
    (matrix fd.labelling.presentation row)
    (Finset.mem_erase.mpr ⟨hColumnNe, Finset.mem_univ _⟩)
  rw [matrix_eq_sum_rowFibre, Equiv.apply_symm_apply, hFibre, Finset.sum_singleton] at hDen
  have hPos := data.sourceEdgeIndex_pos second.1
  have hReciprocal : ((1 : ℚ) / data.sourceEdgeIndex second.1).den =
      data.sourceEdgeIndex second.1 := by
    simp [Nat.ne_of_gt hPos]
  rw [hReciprocal] at hDen
  change data.sourceEdgeIndex edge = data.sourceEdgeIndex second.1 at hIndex
  rwa [hIndex]

/-- Deleting the supported facet's column does not change a different row's
denominator; the removed entry is already cleared by the retained columns. -/
theorem nonfacet_rowDenominator_eq_erase
    (fd : FullDimensionalSourcePresentation data coordinate)
    {facet col row : coordinate}
    (hSupport : ∀ j, j ≠ col → matrix fd.labelling.presentation facet j = 0)
    (hRow : row ≠ facet) :
    rowDenominator fd.labelling.presentation row =
      commonDenominator (Finset.univ.erase col) (matrix fd.labelling.presentation row) := by
  classical
  have hRetained := exists_nonzero_off_support _ fd.det_ne_zero hSupport hRow
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro j _
    by_cases hEq : j = col
    · subst j
      rw [matrix_eq_sum_rowFibre]
      apply UnitWeightBalance.den_sum_dvd
      intro edge hEdge
      obtain ⟨hEdgeRow, hTarget⟩ := (mem_rowFibre_iff _ _ _ _).mp hEdge
      exact (UnitWeightBalance.den_one_div_natCast _).trans
        (contracted_index_dvd_retained fd hSupport hRow hRetained hEdgeRow hTarget)
    · exact den_dvd_commonDenominator _ _ (Finset.mem_erase.mpr ⟨hEq, Finset.mem_univ _⟩)
  · apply Finset.lcm_dvd
    intro j _
    exact den_dvd_commonDenominator _ _ (Finset.mem_univ _)

section Compare

variable {targetIn targetOut : CFGraph.{0}} {degIn degOut : ℕ}
  {dataIn : GluingDatum targetIn degIn} {dataOut : GluingDatum targetOut degOut}
  (fdIn : FullDimensionalSourcePresentation dataIn coordinate)
  (fdOut : FullDimensionalSourcePresentation dataOut coordinate)
  {facet col : coordinate}
  (hAgree : AgreeOffColumn (matrix fdIn.labelling.presentation)
    (matrix fdOut.labelling.presentation) col)
  (hIn : ∀ j, j ≠ col → matrix fdIn.labelling.presentation facet j = 0)
  (hOut : ∀ j, j ≠ col → matrix fdOut.labelling.presentation facet j = 0)

include hAgree hIn hOut

/-- Actual full-dimensional nonfacet row denominators are unchanged across
agreement away from a supported facet column. -/
theorem nonfacet_rowDenominator_eq {row : coordinate} (hRow : row ≠ facet) :
    rowDenominator fdOut.labelling.presentation row =
      rowDenominator fdIn.labelling.presentation row := by
  rw [nonfacet_rowDenominator_eq_erase fdOut hOut hRow,
    nonfacet_rowDenominator_eq_erase fdIn hIn hRow]
  apply Finset.lcm_congr rfl
  intro j hj
  exact congrArg Rat.den (hAgree row j (Finset.mem_erase.mp hj).1).symm

/-- The products of the nonfacet row denominators agree, derived from the full-dimensional
presentations. -/
theorem nonfacet_product_eq :
    ∏ row ∈ Finset.univ.erase facet, rowDenominator fdOut.labelling.presentation row =
      ∏ row ∈ Finset.univ.erase facet, rowDenominator fdIn.labelling.presentation row := by
  apply Finset.prod_congr rfl
  intro row hRow
  exact nonfacet_rowDenominator_eq fdIn fdOut hAgree hIn hOut (Finset.mem_erase.mp hRow).1

/-- Non-trivalent supported-facet balance, with all denominator and leaf
normalization inputs derived from actual full-dimensional presentations. -/
theorem signedMult_eq : fdSignedMult fdOut = fdSignedMult fdIn :=
  NonTrivalentLeafNormalization.signedMult_eq_of_nonfacet_product fdIn fdOut
    hAgree hIn hOut (nonfacet_product_eq fdIn fdOut hAgree hIn hOut)

end Compare

section Landed

open OuterWalk

variable {κ : Type} [Fintype κ] [DecidableEq κ]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {ambient : Infrastructure.CubicDarts.CubicDartGraph D V}
  {label : D → κ} {m : ambient.MoveData}
  {arrival : FacetArrival degree ambient label (label m.base)}
  {wd : WallData arrival} (link : TypeChangeLink m wd)

/-- Actual type-change links preserve every nonfacet row denominator. -/
theorem nonfacet_rowDenominator_eq_of_typeChangeLink {row : κ}
    (hRow : row ≠ label m.base) :
    rowDenominator link.outgoingFD.labelling.presentation row =
      rowDenominator wd.fullDim.labelling.presentation row :=
  nonfacet_rowDenominator_eq wd.fullDim link.outgoingFD link.agree
    wd.incomingMatrix_facet_eq_zero link.outgoingMatrix_facet_eq_zero hRow

/-- For actual type-change links, the products of the row denominators off the facet row agree
on the two sides. -/
theorem nonfacet_product_eq_of_typeChangeLink :
    ∏ row ∈ Finset.univ.erase (label m.base),
        rowDenominator link.outgoingFD.labelling.presentation row =
      ∏ row ∈ Finset.univ.erase (label m.base),
        rowDenominator wd.fullDim.labelling.presentation row :=
  nonfacet_product_eq wd.fullDim link.outgoingFD link.agree
    wd.incomingMatrix_facet_eq_zero link.outgoingMatrix_facet_eq_zero

/-- Full non-trivalent multiplicity balance for the actual type-change link.
There are no additional denominator, leaf-count, or corner-numerator receipts. -/
theorem signedMult_eq_of_typeChangeLink :
    fdSignedMult link.outgoingFD = fdSignedMult wd.fullDim :=
  signedMult_eq wd.fullDim link.outgoingFD link.agree
    wd.incomingMatrix_facet_eq_zero link.outgoingMatrix_facet_eq_zero

end Landed

end DraismaVargas.Count.NonTrivalentNonfacetDenominator

