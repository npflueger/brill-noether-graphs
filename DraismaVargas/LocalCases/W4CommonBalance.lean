module

public import DraismaVargas.LocalCases.W4OutgoingLimitMatrix
public import Utilities.IntegralGeometry.WallColumnDeterminant

@[expose] public section

/-!
# W4 common cofactors, the sigma sum, and Equation (1)

`W4OutgoingLimitMatrix` evaluates the regrown column (`matrix_new`),
identifies `AuxR0SourceInput.presentedFamily`'s presented matrices with the
natural stable-length matrices `StableSourceMatrix.matrix` of the three actual
outgoing candidates under the occurrence-induced row equivalence
`stablePathEquiv` (`presentedFamily_matrix_eq`), and proves Equation (1) **at
column level**: over the three candidates the regrown columns sum to the four
incoming wall columns at every stable row (`sum_matrix_new_eq_sum_wall`).  It
does not weight those columns by cofactors or turn the column identity into a
determinant identity.

This module does that, in the coordinates that `presentedFamily_matrix_eq`
supplies and following `M11CommonBalance` and `W3Nd2CommonBalance`.

* `commonMatrix` — the three candidates' natural stable-length matrices read
  in one common coordinate system: incoming stable rows through
  `stablePathEquiv`, `Option target.edges` columns through `occurrenceEquiv`,
  with `none` the regrown wall column.  `commonMatrix_retained` and
  `commonMatrix_new_sum` are `matrix_retained` and `sum_matrix_new_eq_sum_wall`
  in those coordinates.
* `common_cofactors` — **the cofactor weighting.**  The three candidates'
  square matrices agree away from the wall column (`matrices_agree`, from the
  retained columns alone), so the wall row of the adjugate — the source's
  `c₁, …, c_{3g-3}` — is literally common to the three of them.  No
  nonsingularity and no supplied cofactor correspondence enter.
* `det_eq_sigma_wall` — the source's `σ^{(q)}(1) = c^{(q)}`: each candidate's
  determinant is its own wall column weighted by those common cofactors.
* `sum_sigma_star_eq_zero` — **`∑_{j=2}^{5} σ(j) = 0`.**  Each of the four old
  star columns is a column other than the wall column, so its cofactor-weighted
  contribution is the corresponding off-diagonal entry of
  `adjugate A * A = det A • 1`, which vanishes.
* `sum_det_eq_sum_sigma_star` and `determinant_balance` — **Equation (1)**:
  the first is the source's middle equality, obtained by summing
  `commonMatrix_new_sum` against the common cofactors, and the second adds the
  sigma sum to conclude `∑_{q} det A^{(q)} = 0`.  `determinant_balance_three`
  is the displayed three-term form.
* `family` / `honestPresentedFamily` — the balanced family.  Both carry the
  three actual outgoing candidates and the **honest** matrices
  `GluingDatum.LengthMatrixPresentation.matrix (labelling …).presentation` of a
  `StableLengthMatrixLabelling` on the real outgoing data, with weights
  `(1,1,1)` and `positiveBalance` proved from `determinant_balance` — not from
  any list receipt.  No member is assumed nonsingular; `exists_valid_opposite`
  takes only the chosen member's determinant to be nonzero.

The canonical instance needs no supplied coordinate order: the source input's
own `input.labelling.row`, forced by the full-dimensional stable-path
cardinality, is used.  With that choice `canonicalMatrix_eq_presented` shows
the canonical square matrices **are** the presented matrices of
`AuxR0SourceInput.presentedFamily`; `canonical_wallColumn` and
`presentedFamily_wallColumn` show both expand the same wall column `none`, and
`canonicalPresentedFamily_candidate` that both carry the same three actual
candidates.  So `canonicalPresentedFamily` is that family again, with honest
stable-source path enumerations in place of the raw lists, and
`sum_presented_det_eq_zero` is a second, geometric proof of its balance: the
three determinants of the presented matrices sum to zero because the honest
regrown columns sum to the honest incoming wall columns.

**Not proved here.** Nothing about an incoming full-dimensional presentation or
original coordinates; the positive exit is `W4PositiveExit`, which supplies the
compatible velocity systems. No member of the family is claimed nonsingular, and
no prescribed-endpoint theorem is asserted.

**Which side of the wall bridge.**  Everything is stated for an
`AuxR0SourceInput`, exactly as every W4 outgoing module is, and no
`FullDimensionalSourcePresentation` appears; the two cannot share a datum
(`FullDimensionalSource.false_of_changeMinimal_auxR0SourceInput`).  The
hypotheses are the five fields of `AuxR0SourceInput` and
`[DecidableEq target.edges]`, plus, in the `Square` section only, one arbitrary
square labelling of the first member supplying the finite coordinate order.
Nothing is vacuous: `AuxR0SourceInput.ofChangeMinimalExpansion` produces the
input, and `canonicalInitialLabelling` produces the labelling from the input's
own `stablePath_card` field, so every canonical statement below applies to
those inputs.

Source: Draisma--Vargas Part I, §6.2 (the balancing condition: `σ_0(J, j)`,
`σ^{(q)}(J, j)` and `lemma-formula-for-cq`) and case `{w4}` (Equation (1) and
Figures 26--27).  Part I uses two finite steps of case `{w4}` without stating
them, and the two sides of Equation (w4-nd2) match only after a regrouping of
terms; both enter here only through `sum_matrix_new_eq_sum_wall`, where they
are proved.
-/

namespace DraismaVargas.LocalCases.W4CommonBalance

open DraismaVargas.Infrastructure TargetExpansion
open ResolutionM11 W4Assembly GlobalW4 W4StableSource W4StableGraph
open W4SourceClassification ResolutionAwayFromWall W4OutgoingSurvival
open StableGraphIncidence StablePathCount StableSourceMatrix
open W4OutgoingStableRows W4OutgoingLimitMatrix

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

section Candidate

variable {data : GluingDatum target degree}
  {star : W4TargetPairings.FourStar target wall}
  [DecidableEq target.edges]
  (input : AuxR0SourceInput data star)

/-- The three actual outgoing W4 candidates of the semantic family, with
their derived global validity. -/
noncomputable def candidates : Fin 3 → BalancedGlobal.CertifiedCandidate data :=
  fun pairing ↦ (member input pairing).certified

/-! ## The natural matrices in one common coordinate system

Rows are the incoming stable rows, transported by the occurrence-induced
equivalence `stablePathEquiv`; columns are `Option target.edges`, transported
by the canonical expansion labelling, with `none` the regrown wall column.
-/

/-- The natural stable-length matrix of one outgoing candidate, read in the
common incoming row and `Option` column coordinates. -/
noncomputable def commonMatrix (pairing : Fin 3) :
    Matrix (StablePath data) (Option target.edges) ℚ :=
  fun path place ↦ matrix (member input pairing).datum
    (stablePathEquiv input pairing path)
    (occurrenceEquiv target wall (member input pairing).right place)

/-- Every retained column is the incoming column: `matrix_retained`. -/
theorem commonMatrix_retained (pairing : Fin 3) (path : StablePath data)
    (place : target.edges) :
    commonMatrix input pairing path (some place) = matrix data path place :=
  matrix_retained input pairing path place

/-- **Equation (1) at column level**, in common coordinates: the three regrown
columns sum to the four incoming wall columns at every stable row.  This is
`sum_matrix_new_eq_sum_wall`, i.e. Equations (w4-nd2) and (w4-nd3) block by
block. -/
theorem commonMatrix_new_sum (path : StablePath data) :
    ∑ pairing : Fin 3, commonMatrix input pairing path none =
      ∑ label : Fin 4, matrix data path (star.edge label) :=
  sum_matrix_new_eq_sum_wall input path

section Square

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (initial : StableLengthMatrixLabelling (member input 0).datum coordinate)

/-- A single honest member labelling supplies only the finite coordinate
order; the inter-member row correspondences are the proved geometric ones. -/
noncomputable def sourceCoordinates : StablePath data ≃ coordinate :=
  (stablePathEquiv input 0).trans initial.row

noncomputable def targetCoordinates : coordinate ≃ Option target.edges :=
  initial.targetEdge.trans (occurrenceEquiv target wall (member input 0).right).symm

/-- The induced honest square labelling of every member. -/
noncomputable def labelling (pairing : Fin 3) :
    StableLengthMatrixLabelling (member input pairing).datum coordinate where
  row := (stablePathEquiv input pairing).symm.trans (sourceCoordinates input initial)
  targetEdge := (targetCoordinates input initial).trans
    (occurrenceEquiv target wall (member input pairing).right)

/-- The honest square length matrix of one member. -/
noncomputable def squareMatrix (pairing : Fin 3) : Matrix coordinate coordinate ℚ :=
  GluingDatum.LengthMatrixPresentation.matrix (labelling input initial pairing).presentation

/-- The coordinate naming the regrown wall column. -/
noncomputable def wallColumn : coordinate := (targetCoordinates input initial).symm none

theorem squareMatrix_common (pairing : Fin 3) (row column : coordinate) :
    squareMatrix input initial pairing row column =
      commonMatrix input pairing ((sourceCoordinates input initial).symm row)
        (targetCoordinates input initial column) :=
  labelling_matrix_eq (labelling input initial pairing) row column

theorem squareMatrix_retained (pairing : Fin 3) (row : coordinate) (place : target.edges) :
    squareMatrix input initial pairing row
        ((targetCoordinates input initial).symm (some place)) =
      matrix data ((sourceCoordinates input initial).symm row) place := by
  rw [squareMatrix_common, Equiv.apply_symm_apply, commonMatrix_retained]

theorem squareMatrix_new (pairing : Fin 3) (row : coordinate) :
    squareMatrix input initial pairing row (wallColumn input initial) =
      commonMatrix input pairing ((sourceCoordinates input initial).symm row) none := by
  rw [squareMatrix_common, wallColumn, Equiv.apply_symm_apply]

/-- The three members' matrices agree away from the regrown wall column.
This is the retained-column theorem and nothing else. -/
theorem matrices_agree (first second : Fin 3) :
    AgreeOffColumn (squareMatrix input initial first)
      (squareMatrix input initial second) (wallColumn input initial) := by
  intro row column hColumn
  rw [squareMatrix_common, squareMatrix_common]
  cases hPlace : targetCoordinates input initial column with
  | none => exact (hColumn ((Equiv.eq_symm_apply _).mpr hPlace)).elim
  | some place => rw [commonMatrix_retained, commonMatrix_retained]

/-! ## Cofactors, and the four old star columns `j = 2, …, 5` -/

/-- The coordinate naming one of the four old star columns. -/
noncomputable def starColumn (label : Fin 4) : coordinate :=
  (targetCoordinates input initial).symm (some (star.edge label))

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- An old column is never the regrown wall column: `j ≠ 1`. -/
theorem oldColumn_ne_wallColumn (place : target.edges) :
    (targetCoordinates input initial).symm (some place) ≠ wallColumn input initial := by
  intro hEq
  have hLabels := (targetCoordinates input initial).symm.injective hEq
  cases hLabels

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem starColumn_ne_wallColumn (label : Fin 4) :
    starColumn input initial label ≠ wallColumn input initial :=
  oldColumn_ne_wallColumn input initial (star.edge label)

/-- **The common cofactors.**  The wall row of the adjugate — the source's
`c₁, …, c_{3g-3}`, which depend only on the incoming datum — is the same for
all three candidates, because their matrices agree off the wall column.  No
member is assumed nonsingular. -/
theorem common_cofactors (pairing : Fin 3) (row : coordinate) :
    (squareMatrix input initial pairing).adjugate (wallColumn input initial) row =
      (squareMatrix input initial 0).adjugate (wallColumn input initial) row :=
  adjugate_wallRow_eq_of_agreeOffColumn (matrices_agree input initial pairing 0) row

/-- `σ^{(q)}(1) = c^{(q)}` of `lemma-formula-for-cq`: expanding down the wall
column with the common cofactors computes each candidate's determinant. -/
theorem det_eq_sigma_wall (pairing : Fin 3) :
    (squareMatrix input initial pairing).det =
      ∑ row, squareMatrix input initial pairing row (wallColumn input initial) *
        (squareMatrix input initial 0).adjugate (wallColumn input initial) row :=
  det_eq_sum_wallColumn_mul_commonCofactor (matrices_agree input initial pairing 0)

/-- `σ(j) = 0` for one old column: the other half of `lemma-formula-for-cq`. -/
theorem old_column_annihilation (place : target.edges) :
    columnContribution (squareMatrix input initial 0) (wallColumn input initial)
      ((targetCoordinates input initial).symm (some place)) = 0 :=
  columnContribution_eq_zero _ (oldColumn_ne_wallColumn input initial place)

/-- **`∑_{j=2}^{5} σ(j) = 0`**, the vanishing the source uses to annihilate
the four old star columns. -/
theorem sum_sigma_star_eq_zero :
    ∑ label : Fin 4, columnContribution (squareMatrix input initial 0)
      (wallColumn input initial) (starColumn input initial label) = 0 :=
  Finset.sum_eq_zero fun label _ ↦
    columnContribution_eq_zero _ (starColumn_ne_wallColumn input initial label)

/-! ## Equation (1) -/

/-- Equation (1) at one row, in square coordinates. -/
theorem sum_squareMatrix_wallColumn (row : coordinate) :
    ∑ pairing : Fin 3, squareMatrix input initial pairing row (wallColumn input initial) =
      ∑ label : Fin 4, squareMatrix input initial 0 row
        (starColumn input initial label) := by
  simp only [squareMatrix_new, starColumn, squareMatrix_retained]
  exact commonMatrix_new_sum input _

/-- **The middle equality of Equation (1).**  Weighting the column identity by
the common cofactors turns the three candidates' determinants into the four
old star columns' sigma contributions. -/
theorem sum_det_eq_sum_sigma_star :
    ∑ pairing : Fin 3, (squareMatrix input initial pairing).det =
      ∑ label : Fin 4, columnContribution (squareMatrix input initial 0)
        (wallColumn input initial) (starColumn input initial label) := by
  classical
  calc
    ∑ pairing : Fin 3, (squareMatrix input initial pairing).det
        = ∑ pairing : Fin 3, ∑ row,
            squareMatrix input initial pairing row (wallColumn input initial) *
              (squareMatrix input initial 0).adjugate (wallColumn input initial) row :=
          Finset.sum_congr rfl fun pairing _ ↦ det_eq_sigma_wall input initial pairing
    _ = ∑ row, (∑ pairing : Fin 3,
          squareMatrix input initial pairing row (wallColumn input initial)) *
            (squareMatrix input initial 0).adjugate (wallColumn input initial) row := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun row _ ↦ (Finset.sum_mul _ _ _).symm
    _ = _ := by
          simp only [columnContribution]
          simp_rw [sum_squareMatrix_wallColumn, Finset.sum_mul]
          exact Finset.sum_comm

/-- **Equation (1).**  The three actual outgoing W4 candidates' honest
determinants sum to zero.  No member is assumed nonsingular. -/
theorem determinant_balance :
    ∑ pairing : Fin 3, (squareMatrix input initial pairing).det = 0 :=
  (sum_det_eq_sum_sigma_star input initial).trans (sum_sigma_star_eq_zero input initial)

/-- Equation (1) in the source's displayed three-term form `c⁽¹⁾ + c⁽²⁾ +
c⁽³⁾ = 0`. -/
theorem determinant_balance_three :
    (squareMatrix input initial 0).det + (squareMatrix input initial 1).det +
      (squareMatrix input initial 2).det = 0 := by
  have h := determinant_balance input initial
  simpa [Fin.sum_univ_succ, add_assoc] using h

theorem positiveBalance : BalancingValencyTwo.PositiveBalance ![1, 1, 1]
    (fun pairing ↦ (squareMatrix input initial pairing).det) := by
  constructor
  · intro pairing
    fin_cases pairing <;> norm_num
  · have h := determinant_balance input initial
    simpa [Fin.sum_univ_succ, add_assoc] using h

/-! ## The balanced family -/

/-- The three actual outgoing W4 candidates with their honest stable-length
matrices and the proved Equation (1) balance.  A possibly singular member is
kept in the family. -/
noncomputable def family : BalancedGlobal.Family (coordinate := coordinate) 3 data where
  candidate := candidates input
  matrix := squareMatrix input initial
  wallColumn := wallColumn input initial
  weight := ![1, 1, 1]
  positiveBalance := positiveBalance input initial
  agreeOffWall := matrices_agree input initial

theorem family_matrix_is_honest (pairing : Fin 3) :
    (family input initial).matrix pairing =
      GluingDatum.LengthMatrixPresentation.matrix
        (labelling input initial pairing).presentation := rfl

/-- The same family before forgetting the actual candidates and their honest
presentations: the form a semantic positive exit consumes. -/
noncomputable def honestPresentedFamily :
    BalancedGlobal.PresentedFamily (coordinate := coordinate) 3 data wall where
  candidate := member input
  presentation := fun pairing ↦ (labelling input initial pairing).presentation
  wallColumn := wallColumn input initial
  weight := ![1, 1, 1]
  positiveBalance := positiveBalance input initial
  agreeOffWall := matrices_agree input initial

theorem honestPresentedFamily_toFamily :
    (honestPresentedFamily input initial).toFamily = family input initial := rfl

/-- Any nonsingular chosen member has an actual valid opposite-sign member;
no nonsingularity hypothesis is imposed on the other two. -/
theorem exists_valid_opposite (incoming : Fin 3)
    (hIncoming : (squareMatrix input initial incoming).det ≠ 0) :
    ∃ outgoing, (member input outgoing).datum.Valid ∧
      (squareMatrix input initial incoming).det *
        (squareMatrix input initial outgoing).det < 0 :=
  (family input initial).exists_valid_opposite input.valid incoming hIncoming

end Square

/-! ## The canonical square coordinates

The source input already carries the only coordinate choice there is: its
stable-path labelling `input.labelling`, forced by the full-dimensional
stable-path cardinality `input.stablePath_card`.  Using it identifies the
honest matrices below with the presented matrices of
`AuxR0SourceInput.presentedFamily` on the nose.
-/

/-- The first member's honest square labelling, from the source input alone. -/
noncomputable def canonicalInitialLabelling :
    StableLengthMatrixLabelling (member input 0).datum (Option target.edges) where
  row := (stablePathEquiv input 0).symm.trans input.labelling.row
  targetEdge := occurrenceEquiv target wall (member input 0).right

theorem canonical_sourceCoordinates :
    sourceCoordinates input (canonicalInitialLabelling input) = input.labelling.row := by
  ext path
  simp [sourceCoordinates, canonicalInitialLabelling]

theorem canonical_targetCoordinates (column : Option target.edges) :
    targetCoordinates input (canonicalInitialLabelling input) column = column := by
  simp [targetCoordinates, canonicalInitialLabelling]

/-- The canonical wall column is `none`, the column `AuxR0SourceInput.presentedFamily`
also uses. -/
theorem canonical_wallColumn :
    wallColumn input (canonicalInitialLabelling input) = none := by
  rw [← canonical_targetCoordinates input (wallColumn input (canonicalInitialLabelling input)),
    wallColumn, Equiv.apply_symm_apply]

noncomputable def canonicalMatrix (pairing : Fin 3) :
    Matrix (Option target.edges) (Option target.edges) ℚ :=
  squareMatrix input (canonicalInitialLabelling input) pairing

/-- **The canonical honest matrices are the presented ones.**  With the source
input's own row labelling, the honest stable-length matrix of each outgoing
candidate is literally the presented matrix of
`AuxR0SourceInput.presentedFamily`; this is `presentedFamily_matrix_eq` read in
square coordinates. -/
theorem canonicalMatrix_eq_presented (pairing : Fin 3) :
    canonicalMatrix input pairing =
      GluingDatum.LengthMatrixPresentation.matrix
        ((input.presentedFamily data star).presentation pairing) := by
  ext row column
  rw [canonicalMatrix, squareMatrix_common, presentedFamily_matrix_eq,
    canonical_sourceCoordinates, canonical_targetCoordinates]
  rfl

/-- **Equation (1) with no supplied square labelling.** -/
theorem canonical_determinant_balance :
    ∑ pairing : Fin 3, (canonicalMatrix input pairing).det = 0 :=
  determinant_balance input (canonicalInitialLabelling input)

/-- A geometric proof of `AuxR0SourceInput.presentedFamily`'s balance: its
three presented determinants sum to zero because the honest regrown columns
sum to the honest incoming wall columns. -/
theorem sum_presented_det_eq_zero :
    ∑ pairing : Fin 3, (GluingDatum.LengthMatrixPresentation.matrix
      ((input.presentedFamily data star).presentation pairing)).det = 0 := by
  calc
    ∑ pairing : Fin 3, (GluingDatum.LengthMatrixPresentation.matrix
          ((input.presentedFamily data star).presentation pairing)).det
        = ∑ pairing : Fin 3, (canonicalMatrix input pairing).det :=
          Finset.sum_congr rfl fun pairing _ ↦
            congrArg Matrix.det (canonicalMatrix_eq_presented input pairing).symm
    _ = 0 := canonical_determinant_balance input

/-- A source-certified balanced family needing no external coordinate
labelling; all inter-member row maps are the proved geometric ones. -/
noncomputable def canonicalFamily :
    BalancedGlobal.Family (coordinate := Option target.edges) 3 data :=
  family input (canonicalInitialLabelling input)

theorem canonicalFamily_matrix_is_honest (pairing : Fin 3) :
    (canonicalFamily input).matrix pairing =
      GluingDatum.LengthMatrixPresentation.matrix
        (labelling input (canonicalInitialLabelling input) pairing).presentation := rfl

/-- The canonical family in presented form, retaining the three actual
outgoing candidates. -/
noncomputable def canonicalPresentedFamily :
    BalancedGlobal.PresentedFamily (coordinate := Option target.edges) 3 data wall :=
  honestPresentedFamily input (canonicalInitialLabelling input)

/-- `AuxR0SourceInput.presentedFamily` expands the same wall column, so
`canonical_wallColumn` really does match it. -/
theorem presentedFamily_wallColumn :
    (input.presentedFamily data star).wallColumn = none := rfl

/-- Both families carry the same three actual outgoing candidates. -/
theorem canonicalPresentedFamily_candidate (pairing : Fin 3) :
    (canonicalPresentedFamily input).candidate pairing =
      (input.presentedFamily data star).candidate pairing := rfl

/-- The canonical presented family differs from `AuxR0SourceInput.presentedFamily`
only in carrying honest stable-source path enumerations: its matrices are the
same. -/
theorem canonicalPresentedFamily_matrix (pairing : Fin 3) :
    GluingDatum.LengthMatrixPresentation.matrix
        ((canonicalPresentedFamily input).presentation pairing) =
      GluingDatum.LengthMatrixPresentation.matrix
        ((input.presentedFamily data star).presentation pairing) :=
  canonicalMatrix_eq_presented input pairing

end Candidate

end DraismaVargas.LocalCases.W4CommonBalance
