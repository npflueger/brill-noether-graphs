import DraismaVargas.LocalCases.W3ShiftGraphData

/-!
# `W3ShiftClosure.LimitRows` at an arbitrary stable labelling

Source: Draisma–Vargas Part I, arXiv:1909.12924, case `{w3-r1-nd3-t2-(a>k₄)}`, Figure 29 and
Equation (3).

## What this file settles

`W3ShiftClosure.LimitRows` for Equation (3)'s pair **at an arbitrary
`W4StableSource.StableLengthMatrixLabelling` of one member**, which is the
analogue of `W3Nd3CommonBalance.labelling` / `squareMatrix` / `columnEquiv` /
`wallColumn`.  `W3ShiftLimitRows.limitRows` is fixed at the limit's own stable
rows, with columns `Option target.edges` and wall column `none`, so an exit
built on it has to carry `hOrder` and `hHonest` as named hypotheses.
Here both disappear at the source: each member's presented matrix **is** the
honest stable-length matrix of its own labelling (`honestLabelling_matrix` is
`rfl`), and the wall column is whatever coordinate the supplied labelling puts
the regrown occurrence in.

## The route, and why it is short

`W3ShiftGraphData` supplies, for each member, the occurrence-induced row
equivalence and the retained columns.  What is added here is the **value of the
regrown column**, from `LimitChainCore.SelectedData.matrix_new_split`:

* `matrix_wall` -- a member's regrown column is `1/|e'|` in `e_α`'s own stable
  row and zero in every other, plus `LimitChainCore.backgroundColumn` on the
  moving direction.  The `1/|e'|` is `1/(k_α − 1)` for Position II.b and
  `1/(k_α + 1)` for Position II.a (`commonMatrix_wall_zero`, `_one`), read off
  `W3ShiftLimitRows.shrink_newIndex_cast` and `grow_newIndex_cast`.
* `matrix_moving_split` -- the limit's own `t_α` column is `1/k_α` in that same
  row, plus the **same** background sum.  Both members carry
  `branch := shrink.remainder` as their distinguished-block anchor, so the two
  background halves are literally one function and no congruence is needed.
* `column_identity` -- **Equation (3) at column level**:
  `(k_α − 1)·c⁽¹⁾ + (k_α + 1)·c⁽²⁾ = 2k_α · (limit's t_α column)`, row by row.
  Both weights are positive because the case *derives* `min(k₂,k₃,k₄) ≥ 2`
  (`W3ShiftClosure.one_lt_movingIndex`).

Weighting that identity by the pair's common cofactor row and using the
vanishing of the cofactor-weighted old column
(`Infrastructure.columnContribution_eq_zero`) gives Figure 29's two displayed
determinants and the limit's own wall relation, with `c(e_α)` the cofactor of
`e_α`'s row and `σ₀(J₀,α)` the cofactor-weighted background sum -- **not** free
constants: `wallContribution` and `wallSum` are both defined from the actual
cofactors, and `wallRelation` is a theorem, not a `ring` identity at a chosen
`wallSum`.

## What is proved

`sourceCoordinates`, `targetCoordinates`, `labelling`, `squareMatrix`,
`wallColumn`, `squareMatrix_retained`, `squareMatrix_wall`, `matrices_agree`;
`cofactor`, `wallContribution`, `wallSum`, `det_squareMatrix_zero` / `_one`,
`wallRelation`; **`limitRows`**, a `W3ShiftClosure.LimitRows` at the arbitrary
labelling, and `honestLabelling_matrix`.  Then, over it, `det_closed_zero` /
`_one`, `det_eq_zero_iff`, `det_mul_neg` and
`exists_positive_exit_other` -- the analogues of `W3ShiftLimitRows`' separation
and exit block, at arbitrary coordinates, with the gate `c(e_α) ≠ 0` a
condition on the limit alone.

## What is not proved here

No incoming-member identification (that is `W3ShiftIncomingMatching`), no
original-coordinate restatement (that is `W3ShiftStableIncidence`), and no
branch-swap transport: everything lives over one datum.
-/

namespace DraismaVargas.LocalCases.W3ShiftHonestBalance

open DraismaVargas.Infrastructure
open TargetExpansion
open BalancedGlobal
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open ResolutionCoarseFine
open ResolutionAwayFromWall StableSourceMatrix StablePathCount
open W3R1SourceProfile
open W3ShiftSourceCandidates
open W3FourStableGraph (newIndex)
open W3ShiftGraphData

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {input : W3SourceInput data star}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## The stable row of the moving survivor -/

/-- The limit's stable row displaying `e_α`. -/
noncomputable def movingRow (shift : ShiftProfile input) : StablePath data :=
  NonDanglingEdge.stablePath
    (⟨shift.moving.1, W3ShiftLimitRows.moving_survives shift⟩ : NonDanglingEdge data)

/-! ## The incoming `t_α` column, split at the distinguished block -/

/-- **Above `t_α` the distinguished block displays `e_α` alone.** -/
theorem occurrences_moving_filter (shift : ShiftProfile input) {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel shift.movingAnchor anchor)
    (path : StablePath data) :
    (occurrences data path shift.movingTarget).filter
        (fun edge ↦ (data.vertexPartition wall).Rel anchor edge.1.2) =
      if path = movingRow shift then {shift.moving.1} else ∅ := by
  classical
  ext edge
  constructor
  · intro hMem
    obtain ⟨hOcc, hRel⟩ := Finset.mem_filter.mp hMem
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hOcc
    have hEq : edge = shift.moving.1 :=
      W3ShiftLimitRows.moving_unique_of_wall_rel shift hSurvives hTarget.symm
        (hAnchor.trans hRel)
    subst hEq
    have hPath : path = movingRow shift := hRow.symm
    rw [if_pos hPath]
    exact Finset.mem_singleton_self _
  · intro hMem
    by_cases hPath : path = movingRow shift
    · rw [if_pos hPath, Finset.mem_singleton] at hMem
      subst hMem
      refine Finset.mem_filter.mpr ⟨(mem_occurrences _ _ _).mpr
        ⟨⟨W3ShiftLimitRows.moving_survives shift, hPath.symm⟩, rfl⟩, ?_⟩
      exact hAnchor.symm
    · rw [if_neg hPath] at hMem
      exact absurd hMem (Finset.notMem_empty _)

/-- **The incoming `t_α` column of a stable row**: `1/k_α` in `e_α`'s own row,
plus the limit's own background sum. -/
theorem matrix_moving_split (shift : ShiftProfile input) {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel shift.movingAnchor anchor)
    (path : StablePath data) :
    matrix data path shift.movingTarget =
      (if path = movingRow shift then
        (1 : ℚ) / data.sourceEdgeIndex shift.moving.1 else 0) +
        LimitChainCore.backgroundColumn data wall anchor path shift.movingTarget := by
  classical
  have hSplit := Finset.sum_filter_add_sum_filter_not
    (occurrences data path shift.movingTarget)
    (fun edge ↦ (data.vertexPartition wall).Rel anchor edge.1.2)
    (fun edge ↦ (1 : ℚ) / data.sourceEdgeIndex edge)
  rw [occurrences_moving_filter shift hAnchor path] at hSplit
  show (∑ edge ∈ occurrences data path shift.movingTarget,
    (1 : ℚ) / data.sourceEdgeIndex edge) = _
  rw [← hSplit]
  congr 1
  · split_ifs <;> simp


/-! ## The regrown column of a member, split at the distinguished block -/

section Regrown

variable {shift : ShiftProfile input} {m : MemberData shift} (c : SelectedCensus m)
  (hValid : data.Valid)

@[simp] theorem graphData_selected : (c.graphData hValid).selected = c.branch := rfl

@[simp] theorem graphData_retainedTarget :
    (c.graphData hValid).retainedTarget = shift.movingTarget := rfl

theorem selected_rel_main :
    (data.vertexPartition wall).Rel (c.graphData hValid).selected c.main :=
  c.branch_wall.symm.trans c.main_wall

/-- **The member's regrown occurrences above the distinguished block**: the one
surviving regrown class, in `e_α`'s own stable row, and nothing else. -/
theorem newOccurrences_filter (path : StablePath data) :
    ((c.graphData hValid).newOccurrences path).filter
        (fun edge ↦ (data.vertexPartition wall).Rel
          (c.graphData hValid).selected edge.1.2) =
      if path = movingRow shift then
        {(c.graphData hValid).candidate.newSourceEdge c.main} else ∅ := by
  classical
  ext edge
  constructor
  · intro hMem
    obtain ⟨hOcc, hRel⟩ := Finset.mem_filter.mp hMem
    obtain ⟨⟨hSurvives, _⟩, _⟩ := (mem_occurrences _ _ _).mp hOcc
    have hEdge : edge = (c.graphData hValid).candidate.newSourceEdge edge.1.2 :=
      (c.graphData hValid).eq_newSourceEdge_of_mem path edge hOcc
    have hWall : (data.vertexPartition wall).Rel shift.movingAnchor edge.1.2 :=
      c.branch_wall.trans hRel
    have hNewRel : m.selectedResolution.newEdge.Rel edge.1.2 c.main := by
      by_contra hSep
      refine hSurvives ?_
      rw [hEdge]
      exact c.new_dangles edge.1.2 hWall hSep
    have hMain : edge = (c.graphData hValid).candidate.newSourceEdge c.main :=
      hEdge.trans (m.newSourceEdge_eq_of_rel hWall hNewRel).symm
    have hPath : path = movingRow shift :=
      ((c.graphData hValid).new_mem_iff_of_survives c.main
        (selected_rel_main c hValid) c.new_main_survives path).mp
        (by rw [← hMain]; exact hOcc)
    rw [if_pos hPath]
    exact Finset.mem_singleton.mpr hMain
  · intro hMem
    by_cases hPath : path = movingRow shift
    · rw [if_pos hPath, Finset.mem_singleton] at hMem
      subst hMem
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact ((c.graphData hValid).new_mem_iff_of_survives c.main
          (selected_rel_main c hValid) c.new_main_survives path).mpr hPath
      · exact ((c.graphData hValid).newSourceEdge_sheet_rel_iff c.main).mpr
          (selected_rel_main c hValid)
    · rw [if_neg hPath] at hMem
      exact absurd hMem (Finset.notMem_empty _)

/-- **The member's regrown column of a stable row**: the reciprocal of its own
displayed new-edge index in `e_α`'s row, plus the limit's own background sum on
the moving direction. -/
theorem matrix_wall_aux (path : StablePath data) :
    matrix (c.graphData hValid).candidate.datum
        ((c.graphData hValid).stablePathEquiv path)
        (occurrenceEquiv target wall (c.graphData hValid).candidate.right none) =
      (if path = movingRow shift then
        (1 : ℚ) / newIndex (c.graphData hValid).candidate c.main else 0) +
        LimitChainCore.backgroundColumn data wall (c.graphData hValid).selected path
          (c.graphData hValid).retainedTarget := by
  classical
  rw [(c.graphData hValid).matrix_new_split path, newOccurrences_filter c hValid path]
  congr 1
  split_ifs with hPath
  · rw [Finset.sum_singleton]
    rfl
  · exact Finset.sum_empty

/-- The same, read on the member's own candidate. -/
theorem matrix_wall (path : StablePath data) :
    matrix m.candidate.datum ((c.graphData hValid).stablePathEquiv path)
        (occurrenceEquiv target wall m.candidate.right none) =
      (if path = movingRow shift then
        (1 : ℚ) / newIndex m.candidate c.main else 0) +
        LimitChainCore.backgroundColumn data wall c.branch path shift.movingTarget :=
  matrix_wall_aux c hValid path

end Regrown


/-! ## Equation (3) at column level -/

section Pair

variable {shift : ShiftProfile input} (shrink : ShrinkData shift) (hValid : data.Valid)

theorem movingIndex_eq :
    W3ShiftLimitRows.movingIndex shift =
      ((data.sourceEdgeIndex shift.moving.1 : ℕ) : ℚ) := rfl

/-- **Position II.b's regrown column**: `1/(k_α − 1)` in `e_α`'s row, plus the
limit's own background sum. -/
theorem commonMatrix_wall_zero (path : StablePath data) :
    commonMatrix shrink hValid 0 path none =
      (if path = movingRow shift then
        (1 : ℚ) / (W3ShiftLimitRows.movingIndex shift - 1) else 0) +
        LimitChainCore.backgroundColumn data wall shrink.remainder path
          shift.movingTarget := by
  have hCast : ((newIndex (shrinkMember shrink).candidate
      (Shrink.census shrink hValid).main : ℕ) : ℚ) =
      W3ShiftLimitRows.movingIndex shift - 1 :=
    W3ShiftLimitRows.shrink_newIndex_cast shrink
  have h := matrix_wall (Shrink.census shrink hValid) hValid path
  rw [hCast] at h
  exact h

/-- **Position II.a's regrown column**: `1/(k_α + 1)` in `e_α`'s row, plus the
same background sum. -/
theorem commonMatrix_wall_one (path : StablePath data) :
    commonMatrix shrink hValid 1 path none =
      (if path = movingRow shift then
        (1 : ℚ) / (W3ShiftLimitRows.movingIndex shift + 1) else 0) +
        LimitChainCore.backgroundColumn data wall shrink.remainder path
          shift.movingTarget := by
  have hCast : ((newIndex (growMember shift).candidate
      (Grow.census shift hValid (Shrink.wall_rel_remainder shrink)).main : ℕ) : ℚ) =
      W3ShiftLimitRows.movingIndex shift + 1 :=
    W3ShiftLimitRows.grow_newIndex_cast shift
  have h := matrix_wall (Grow.census shift hValid (Shrink.wall_rel_remainder shrink))
    hValid path
  rw [hCast] at h
  exact h

/-- **Equation (3) at column level.**  The two regrown columns, weighted by
`k_α − 1` and `k_α + 1`, reproduce `2k_α` times the limit's own `t_α` column.
Both weights are positive because the case derives `min(k₂,k₃,k₄) ≥ 2`. -/
theorem column_identity (path : StablePath data) :
    (W3ShiftLimitRows.movingIndex shift - 1) * commonMatrix shrink hValid 0 path none +
        (W3ShiftLimitRows.movingIndex shift + 1) *
          commonMatrix shrink hValid 1 path none =
      2 * W3ShiftLimitRows.movingIndex shift * matrix data path shift.movingTarget := by
  have hk : (1 : ℚ) < W3ShiftLimitRows.movingIndex shift :=
    W3ShiftClosure.one_lt_movingIndex shift
  have hk0 : W3ShiftLimitRows.movingIndex shift ≠ 0 := by linarith
  have hkm : W3ShiftLimitRows.movingIndex shift - 1 ≠ 0 := by
    intro h
    have : W3ShiftLimitRows.movingIndex shift = 1 := by linarith
    linarith
  have hkp : W3ShiftLimitRows.movingIndex shift + 1 ≠ 0 := by
    intro h
    have : W3ShiftLimitRows.movingIndex shift = -1 := by linarith
    linarith
  rw [commonMatrix_wall_zero shrink hValid path, commonMatrix_wall_one shrink hValid path,
    matrix_moving_split shift (Shrink.wall_rel_remainder shrink) path,
    show ((data.sourceEdgeIndex shift.moving.1 : ℕ) : ℚ) =
      W3ShiftLimitRows.movingIndex shift from rfl]
  split_ifs
  · field_simp
    ring
  · ring

end Pair


/-! ## Equation (3) at an arbitrary stable labelling of one member -/

section Square

variable {shift : ShiftProfile input} (shrink : ShrinkData shift) (hValid : data.Valid)
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (initial : StableLengthMatrixLabelling
    (W3ShiftLimitRows.shiftMembers shrink 0).datum coordinate)

/-- A single honest member labelling supplies only the finite coordinate order;
the other member is labelled through the geometric equivalences. -/
noncomputable def sourceCoordinates : StablePath data ≃ coordinate :=
  (rowEquiv shrink hValid 0).trans initial.row

noncomputable def targetCoordinates : coordinate ≃ Option target.edges :=
  initial.targetEdge.trans
    (occurrenceEquiv target wall (W3ShiftLimitRows.shiftMembers shrink 0).right).symm

/-- **The induced honest square labelling of both members of Figure 29's
pair.** -/
noncomputable def labelling (i : Fin 2) :
    StableLengthMatrixLabelling (W3ShiftLimitRows.shiftMembers shrink i).datum
      coordinate where
  row := (rowEquiv shrink hValid i).symm.trans (sourceCoordinates shrink hValid initial)
  targetEdge := (targetCoordinates shrink initial).trans
    (occurrenceEquiv target wall (W3ShiftLimitRows.shiftMembers shrink i).right)

/-- The honest square length matrix of one member. -/
noncomputable def squareMatrix (i : Fin 2) : Matrix coordinate coordinate ℚ :=
  GluingDatum.LengthMatrixPresentation.matrix
    (labelling shrink hValid initial i).presentation

/-- The coordinate naming the regrown wall column. -/
noncomputable def wallColumn : coordinate :=
  (targetCoordinates shrink initial).symm none

theorem squareMatrix_common (i : Fin 2) (row column : coordinate) :
    squareMatrix shrink hValid initial i row column =
      commonMatrix shrink hValid i
        ((sourceCoordinates shrink hValid initial).symm row)
        (targetCoordinates shrink initial column) :=
  labelling_matrix_eq (labelling shrink hValid initial i) row column

theorem squareMatrix_retained (i : Fin 2) (row : coordinate) (place : target.edges) :
    squareMatrix shrink hValid initial i row
        ((targetCoordinates shrink initial).symm (some place)) =
      matrix data ((sourceCoordinates shrink hValid initial).symm row) place := by
  rw [squareMatrix_common, Equiv.apply_symm_apply, commonMatrix_retained]

theorem squareMatrix_wall (i : Fin 2) (row : coordinate) :
    squareMatrix shrink hValid initial i row (wallColumn shrink initial) =
      commonMatrix shrink hValid i
        ((sourceCoordinates shrink hValid initial).symm row) none := by
  rw [squareMatrix_common, wallColumn, Equiv.apply_symm_apply]

/-- The two members agree away from the regrown wall column: this is the
retained-column theorem and nothing else. -/
theorem matrices_agree (first second : Fin 2) :
    AgreeOffColumn (squareMatrix shrink hValid initial first)
      (squareMatrix shrink hValid initial second)
      (wallColumn shrink initial) := by
  intro row column hColumn
  rw [squareMatrix_common, squareMatrix_common]
  cases hPlace : targetCoordinates shrink initial column with
  | none => exact (hColumn ((Equiv.eq_symm_apply _).mpr hPlace)).elim
  | some place => rw [commonMatrix_retained, commonMatrix_retained]

/-- The family's common cofactor row, read from Position II.b. -/
noncomputable def cofactor (row : coordinate) : ℚ :=
  (squareMatrix shrink hValid initial 0).adjugate
    (wallColumn shrink initial) row

theorem cofactor_def (row : coordinate) :
    (squareMatrix shrink hValid initial 0).adjugate (wallColumn shrink initial) row =
      cofactor shrink hValid initial row := rfl

/-- Figure 29's `c(e_α)`, in the chosen coordinate order. -/
noncomputable def wallContribution : ℚ :=
  cofactor shrink hValid initial
    (sourceCoordinates shrink hValid initial (movingRow shift))

/-- Figure 29's `σ₀(J₀,α)`, in the chosen coordinate order: the
cofactor-weighted background sum of the limit's own `t_α` column. -/
noncomputable def wallSum : ℚ :=
  ∑ row : coordinate,
    LimitChainCore.backgroundColumn data wall shrink.remainder
        ((sourceCoordinates shrink hValid initial).symm row) shift.movingTarget *
      cofactor shrink hValid initial row

omit [Fintype coordinate] in
theorem ite_source (value : ℚ) (row : coordinate) :
    (if (sourceCoordinates shrink hValid initial).symm row = movingRow shift then
      value else 0) =
      if row = sourceCoordinates shrink hValid initial (movingRow shift) then
        value else 0 := by
  by_cases hRow : row = sourceCoordinates shrink hValid initial (movingRow shift)
  · rw [if_pos hRow, if_pos (by rw [hRow]; exact Equiv.symm_apply_apply _ _)]
  · refine (if_neg fun hEq ↦ hRow ?_).trans (if_neg hRow).symm
    rw [← hEq, Equiv.apply_symm_apply]

theorem sum_ite_cofactor (value : ℚ) :
    ∑ row : coordinate,
        (if (sourceCoordinates shrink hValid initial).symm row = movingRow shift then
          value else 0) * cofactor shrink hValid initial row =
      value * wallContribution shrink hValid initial := by
  classical
  simp only [ite_source shrink hValid initial value]
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ
    (sourceCoordinates shrink hValid initial (movingRow shift))
    (fun row ↦ value * cofactor shrink hValid initial row)]
  simp [wallContribution]

theorem det_squareMatrix_zero :
    (squareMatrix shrink hValid initial 0).det =
      wallContribution shrink hValid initial /
          (W3ShiftLimitRows.movingIndex shift - 1) +
        wallSum shrink hValid initial := by
  classical
  rw [det_eq_sum_wallColumn_mul_commonCofactor
    (matrices_agree shrink hValid initial 0 0)]
  simp only [cofactor_def]
  have hEntry : ∀ row : coordinate,
      squareMatrix shrink hValid initial 0 row (wallColumn shrink initial) *
          cofactor shrink hValid initial row =
        (if (sourceCoordinates shrink hValid initial).symm row = movingRow shift then
            (1 : ℚ) / (W3ShiftLimitRows.movingIndex shift - 1) else 0) *
            cofactor shrink hValid initial row +
          LimitChainCore.backgroundColumn data wall shrink.remainder
              ((sourceCoordinates shrink hValid initial).symm row)
              shift.movingTarget *
            cofactor shrink hValid initial row := by
    intro row
    rw [squareMatrix_wall, commonMatrix_wall_zero]
    ring
  rw [Finset.sum_congr rfl (fun row (_ : row ∈ Finset.univ) ↦ hEntry row),
    Finset.sum_add_distrib, sum_ite_cofactor]
  rw [wallSum]
  ring

theorem det_squareMatrix_one :
    (squareMatrix shrink hValid initial 1).det =
      wallContribution shrink hValid initial /
          (W3ShiftLimitRows.movingIndex shift + 1) +
        wallSum shrink hValid initial := by
  classical
  rw [det_eq_sum_wallColumn_mul_commonCofactor
    (matrices_agree shrink hValid initial 1 0)]
  simp only [cofactor_def]
  have hEntry : ∀ row : coordinate,
      squareMatrix shrink hValid initial 1 row (wallColumn shrink initial) *
          cofactor shrink hValid initial row =
        (if (sourceCoordinates shrink hValid initial).symm row = movingRow shift then
            (1 : ℚ) / (W3ShiftLimitRows.movingIndex shift + 1) else 0) *
            cofactor shrink hValid initial row +
          LimitChainCore.backgroundColumn data wall shrink.remainder
              ((sourceCoordinates shrink hValid initial).symm row)
              shift.movingTarget *
            cofactor shrink hValid initial row := by
    intro row
    rw [squareMatrix_wall, commonMatrix_wall_one]
    ring
  rw [Finset.sum_congr rfl (fun row (_ : row ∈ Finset.univ) ↦ hEntry row),
    Finset.sum_add_distrib, sum_ite_cofactor]
  rw [wallSum]
  ring

/-- **The limit's own wall relation** `c(e_α)/k_α + σ₀(J₀,α) = 0`: the
cofactor-weighted `t_α` column of the limit vanishes, and the distinguished
block contributes exactly `c(e_α)/k_α` to it. -/
theorem wallRelation :
    wallContribution shrink hValid initial / W3ShiftLimitRows.movingIndex shift +
      wallSum shrink hValid initial = 0 := by
  classical
  have hZero := columnContribution_eq_zero (squareMatrix shrink hValid initial 0)
    (wallColumn := wallColumn shrink initial)
    (column := (targetCoordinates shrink initial).symm
      (some shift.movingTarget))
    (fun hEq ↦ by
      have hSome := (targetCoordinates shrink initial).symm.injective hEq
      exact Option.some_ne_none _ hSome)
  rw [columnContribution] at hZero
  simp only [cofactor_def] at hZero
  have hEntry : ∀ row : coordinate,
      squareMatrix shrink hValid initial 0 row
            ((targetCoordinates shrink initial).symm
              (some shift.movingTarget)) *
          cofactor shrink hValid initial row =
        (if (sourceCoordinates shrink hValid initial).symm row = movingRow shift then
            (1 : ℚ) / W3ShiftLimitRows.movingIndex shift else 0) *
            cofactor shrink hValid initial row +
          LimitChainCore.backgroundColumn data wall shrink.remainder
              ((sourceCoordinates shrink hValid initial).symm row)
              shift.movingTarget *
            cofactor shrink hValid initial row := by
    intro row
    rw [squareMatrix_retained,
      matrix_moving_split shift (Shrink.wall_rel_remainder shrink),
      show ((data.sourceEdgeIndex shift.moving.1 : ℕ) : ℚ) =
        W3ShiftLimitRows.movingIndex shift from rfl]
    ring
  rw [Finset.sum_congr rfl (fun row (_ : row ∈ Finset.univ) ↦ hEntry row),
    Finset.sum_add_distrib, sum_ite_cofactor] at hZero
  rw [wallSum]
  rw [← hZero]
  ring

/-- **`W3ShiftClosure.LimitRows` for Figure 29's pair, at an arbitrary stable
length-matrix labelling of one member.**  Every presented matrix is that
member's own honest stable-length matrix, and the two determinants are
Figure 29's displayed `c(e_α)/(k_α ∓ 1) + σ₀(J₀,α)`. -/
noncomputable def limitRows :
    W3ShiftClosure.LimitRows (W3ShiftLimitRows.shiftMembers shrink) coordinate where
  presentation := fun i ↦ (labelling shrink hValid initial i).presentation
  wallColumn := wallColumn shrink initial
  movingIndex := W3ShiftLimitRows.movingIndex shift
  wallContribution := wallContribution shrink hValid initial
  wallSum := wallSum shrink hValid initial
  one_lt_movingIndex' := W3ShiftClosure.one_lt_movingIndex shift
  wallRelation := wallRelation shrink hValid initial
  det := by
    intro i
    fin_cases i
    · exact det_squareMatrix_zero shrink hValid initial
    · exact det_squareMatrix_one shrink hValid initial
  agreeOffWall := matrices_agree shrink hValid initial

/-- **The honest labelling of each member**, and the identity that makes the
family's determinant gate a gate on the member's own matrix: the presented
matrix *is* the labelling's. -/
theorem honestLabelling_matrix (i : Fin 2) :
    GluingDatum.LengthMatrixPresentation.matrix
        (labelling shrink hValid initial i).presentation =
      GluingDatum.LengthMatrixPresentation.matrix
        ((limitRows shrink hValid initial).presentation i) := rfl

@[simp] theorem limitRows_wallColumn :
    (limitRows shrink hValid initial).wallColumn =
      wallColumn shrink initial := rfl

end Square


/-! ## The two determinants, and the exit over the honest matrices -/

section Exit

variable {shift : ShiftProfile input} (shrink : ShrinkData shift) (hValid : data.Valid)
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (initial : StableLengthMatrixLabelling
    (W3ShiftLimitRows.shiftMembers shrink 0).datum coordinate)

/-- **Position II.b's determinant in closed form**: `c(e_α)/(k_α(k_α − 1))`. -/
theorem det_closed_zero :
    (squareMatrix shrink hValid initial 0).det =
      wallContribution shrink hValid initial /
        (W3ShiftLimitRows.movingIndex shift *
          (W3ShiftLimitRows.movingIndex shift - 1)) := by
  have hOne : (1 : ℚ) < W3ShiftLimitRows.movingIndex shift :=
    W3ShiftClosure.one_lt_movingIndex shift
  have hk : W3ShiftLimitRows.movingIndex shift ≠ 0 := ne_of_gt (by linarith)
  have hk1 : W3ShiftLimitRows.movingIndex shift - 1 ≠ 0 := ne_of_gt (by linarith)
  refine (det_squareMatrix_zero shrink hValid initial).trans ?_
  have hRel := wallRelation shrink hValid initial
  have hSum : wallSum shrink hValid initial =
      -(wallContribution shrink hValid initial /
        W3ShiftLimitRows.movingIndex shift) := by linarith
  rw [hSum]
  field_simp
  ring

/-- **Position II.a's determinant in closed form**: `−c(e_α)/(k_α(k_α + 1))`. -/
theorem det_closed_one :
    (squareMatrix shrink hValid initial 1).det =
      -(wallContribution shrink hValid initial /
        (W3ShiftLimitRows.movingIndex shift *
          (W3ShiftLimitRows.movingIndex shift + 1))) := by
  have hOne : (1 : ℚ) < W3ShiftLimitRows.movingIndex shift :=
    W3ShiftClosure.one_lt_movingIndex shift
  have hk : W3ShiftLimitRows.movingIndex shift ≠ 0 := ne_of_gt (by linarith)
  have hk2 : W3ShiftLimitRows.movingIndex shift + 1 ≠ 0 := ne_of_gt (by linarith)
  refine (det_squareMatrix_one shrink hValid initial).trans ?_
  have hRel := wallRelation shrink hValid initial
  have hSum : wallSum shrink hValid initial =
      -(wallContribution shrink hValid initial /
        W3ShiftLimitRows.movingIndex shift) := by linarith
  rw [hSum]
  field_simp
  ring

theorem det_eq_zero_iff_zero :
    (squareMatrix shrink hValid initial 0).det = 0 ↔
      wallContribution shrink hValid initial = 0 := by
  have hOne : (1 : ℚ) < W3ShiftLimitRows.movingIndex shift :=
    W3ShiftClosure.one_lt_movingIndex shift
  have hk : W3ShiftLimitRows.movingIndex shift ≠ 0 := ne_of_gt (by linarith)
  have hk1 : W3ShiftLimitRows.movingIndex shift - 1 ≠ 0 := ne_of_gt (by linarith)
  rw [det_closed_zero shrink hValid initial, div_eq_zero_iff]
  exact or_iff_left (mul_ne_zero hk hk1)

theorem det_eq_zero_iff_one :
    (squareMatrix shrink hValid initial 1).det = 0 ↔
      wallContribution shrink hValid initial = 0 := by
  have hOne : (1 : ℚ) < W3ShiftLimitRows.movingIndex shift :=
    W3ShiftClosure.one_lt_movingIndex shift
  have hk : W3ShiftLimitRows.movingIndex shift ≠ 0 := ne_of_gt (by linarith)
  have hk2 : W3ShiftLimitRows.movingIndex shift + 1 ≠ 0 := ne_of_gt (by linarith)
  rw [det_closed_one shrink hValid initial, neg_eq_zero, div_eq_zero_iff]
  exact or_iff_left (mul_ne_zero hk hk2)

/-- **The exit's nonsingularity gate is a condition on the limit alone.** -/
theorem det_eq_zero_iff (i : Fin 2) :
    (squareMatrix shrink hValid initial i).det = 0 ↔
      wallContribution shrink hValid initial = 0 := by
  fin_cases i
  · exact det_eq_zero_iff_zero shrink hValid initial
  · exact det_eq_zero_iff_one shrink hValid initial

/-- **Equation (3)'s two members always have opposite determinant sign.** -/
theorem det_mul_neg (hContribution : wallContribution shrink hValid initial ≠ 0) :
    (squareMatrix shrink hValid initial 0).det *
      (squareMatrix shrink hValid initial 1).det < 0 := by
  have hOne : (1 : ℚ) < W3ShiftLimitRows.movingIndex shift :=
    W3ShiftClosure.one_lt_movingIndex shift
  have hk : (0 : ℚ) < W3ShiftLimitRows.movingIndex shift := by linarith
  have hk1 : (0 : ℚ) < W3ShiftLimitRows.movingIndex shift - 1 := by linarith
  have hk2 : (0 : ℚ) < W3ShiftLimitRows.movingIndex shift + 1 := by linarith
  have hSquare : 0 < wallContribution shrink hValid initial ^ 2 := by
    rcases lt_trichotomy (wallContribution shrink hValid initial) 0 with
      hNeg | hZero | hPos
    · nlinarith
    · exact absurd hZero hContribution
    · nlinarith
  have hProduct : (wallContribution shrink hValid initial /
        (W3ShiftLimitRows.movingIndex shift *
          (W3ShiftLimitRows.movingIndex shift - 1))) *
      -(wallContribution shrink hValid initial /
        (W3ShiftLimitRows.movingIndex shift *
          (W3ShiftLimitRows.movingIndex shift + 1))) =
      -(wallContribution shrink hValid initial ^ 2 /
        (W3ShiftLimitRows.movingIndex shift *
          (W3ShiftLimitRows.movingIndex shift - 1) *
          (W3ShiftLimitRows.movingIndex shift *
            (W3ShiftLimitRows.movingIndex shift + 1)))) := by
    field_simp
  rw [det_closed_zero shrink hValid initial, det_closed_one shrink hValid initial,
    hProduct]
  have hDenominator : (0 : ℚ) < W3ShiftLimitRows.movingIndex shift *
      (W3ShiftLimitRows.movingIndex shift - 1) *
      (W3ShiftLimitRows.movingIndex shift *
        (W3ShiftLimitRows.movingIndex shift + 1)) :=
    mul_pos (mul_pos hk hk1) (mul_pos hk hk2)
  have hPos := div_pos hSquare hDenominator
  linarith

theorem ne_of_det_mul_neg {i j : Fin 2}
    (hSign : (squareMatrix shrink hValid initial i).det *
      (squareMatrix shrink hValid initial j).det < 0) : j ≠ i := by
  intro hEq
  rw [hEq] at hSign
  nlinarith [mul_self_nonneg (squareMatrix shrink hValid initial i).det]

/-- **Equation (3)'s certified positive exit over the honest matrices at an
arbitrary labelling**, landing on the *other* member of the pair, with its gate
`c(e_α) ≠ 0` a condition on the limit alone. -/
theorem exists_positive_exit_other (hTargetConnected : graph_connected target)
    (hTargetGenus : genus target = 0) (root : target.V) (incoming : Fin 2)
    (hContribution : wallContribution shrink hValid initial ≠ 0)
    (z incomingVelocity : coordinate → ℚ)
    (outgoingVelocity : Fin 2 → coordinate → ℚ)
    (hz : z (wallColumn shrink initial) = 0)
    (hzpos : ∀ i, i ≠ wallColumn shrink initial → 0 < z i)
    (hSystems : ∀ outgoing,
      (squareMatrix shrink hValid initial outgoing).det ≠ 0 →
      (squareMatrix shrink hValid initial incoming).mulVec incomingVelocity =
        (squareMatrix shrink hValid initial outgoing).mulVec
          (outgoingVelocity outgoing))
    (hIncomingDirection : incomingVelocity (wallColumn shrink initial) < 0) :
    ∃ outgoing, outgoing ≠ incoming ∧
      (W3ShiftLimitRows.shiftMembers shrink outgoing).datum.Valid ∧
      (squareMatrix shrink hValid initial incoming).det *
        (squareMatrix shrink hValid initial outgoing).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        (squareMatrix shrink hValid initial outgoing).mulVec
            (z + t • outgoingVelocity outgoing) =
          (squareMatrix shrink hValid initial incoming).mulVec z +
            t • (squareMatrix shrink hValid initial incoming).mulVec
              incomingVelocity ∧
        Nonempty (Candidate.ClearedPencil
          (W3ShiftLimitRows.shiftMembers shrink outgoing)
          ((limitRows shrink hValid initial).presentation outgoing)
          (z + t • outgoingVelocity outgoing)) := by
  obtain ⟨outgoing, hValidOut, hSign, hRest⟩ :=
    W3ShiftClosure.exists_equationThree_positive_exit data (fun h ↦ h)
      (W3ShiftLimitRows.shiftMembers shrink) (limitRows shrink hValid initial)
      hValid hTargetConnected hTargetGenus root incoming
      (fun hDet ↦ hContribution
        ((det_eq_zero_iff shrink hValid initial incoming).mp hDet))
      z incomingVelocity outgoingVelocity hz hzpos hSystems hIncomingDirection
  exact ⟨outgoing, ne_of_det_mul_neg shrink hValid initial hSign, hValidOut, hSign,
    hRest⟩

end Exit

end DraismaVargas.LocalCases.W3ShiftHonestBalance
