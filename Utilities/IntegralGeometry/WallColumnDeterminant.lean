module

public import Utilities.IntegralGeometry.ConeWall
public import Mathlib.LinearAlgebra.Matrix.Adjugate

@[expose] public section

/-!
# Determinant contributions of a changing wall column

At a codimension-one wall of the Draisma--Vargas deformation argument
(Draisma--Vargas Part I, arXiv:1909.12924), candidate edge-length matrices
agree away from the column of the regrown target edge.  Consequently the
corresponding row of the adjugate is common to every candidate.  Expanding the
determinant down that column gives a sum of wall-column entries times these
common cofactors.

The row-grouping theorem is convenient when each row belongs to one block.
The more general entry-summand theorem first decomposes each changing-column
entry by a finite block label; this permits one stable-path row to pass through
several source wall blocks, which is the form a local wall analysis needs.
-/

namespace DraismaVargas.Infrastructure

open Matrix

variable {row : Type*} [Fintype row] [DecidableEq row]

/-- Matrices agreeing away from column `wallColumn` have the same cofactors
for expansion down that column. -/
theorem adjugate_wallRow_eq_of_agreeOffColumn
    {A B : Matrix row row ℚ} {wallColumn : row}
    (hAgree : AgreeOffColumn A B wallColumn) (sourceRow : row) :
    A.adjugate wallColumn sourceRow =
      B.adjugate wallColumn sourceRow := by
  have hCramer := cramer_eq_of_agreeOffColumn hAgree
    (Pi.single sourceRow 1)
  rw [Matrix.cramer_eq_adjugate_mulVec,
    Matrix.cramer_eq_adjugate_mulVec] at hCramer
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, eq_comm] using hCramer

/-- Expand `A.det` down its wall column, using the common cofactors from any
matrix `B` with the same off-wall columns. -/
theorem det_eq_sum_wallColumn_mul_commonCofactor
    {A B : Matrix row row ℚ} {wallColumn : row}
    (hAgree : AgreeOffColumn A B wallColumn) :
    A.det = ∑ sourceRow,
      A sourceRow wallColumn * B.adjugate wallColumn sourceRow := by
  rw [Matrix.det_eq_sum_mul_adjugate_col A wallColumn]
  apply Finset.sum_congr rfl
  intro sourceRow _
  rw [adjugate_wallRow_eq_of_agreeOffColumn hAgree sourceRow]

/-- The determinant contribution from the rows assigned to one source wall
block.  Cofactors are read from `reference`; wall-column entries are read from
the current candidate. -/
noncomputable def wallBlockContribution
    {block : Type*} [Fintype block]
    (reference current : Matrix row row ℚ) (wallColumn : row)
    (rowBlock : row → block) (sourceBlock : block) : ℚ := by
  classical
  exact ∑ sourceRow ∈ Finset.univ with rowBlock sourceRow = sourceBlock,
    current sourceRow wallColumn *
      reference.adjugate wallColumn sourceRow

/-- Cofactor expansion followed by finite fiberwise summation decomposes the
determinant over any total labelling of rows by source wall blocks. -/
theorem det_eq_sum_wallBlockContribution
    {block : Type*} [Fintype block]
    {reference current : Matrix row row ℚ} {wallColumn : row}
    (rowBlock : row → block)
    (hAgree : AgreeOffColumn current reference wallColumn) :
    current.det = ∑ sourceBlock,
      wallBlockContribution reference current wallColumn rowBlock
        sourceBlock := by
  classical
  rw [det_eq_sum_wallColumn_mul_commonCofactor hAgree]
  symm
  simpa [wallBlockContribution] using
    (Finset.sum_fiberwise (M := ℚ) Finset.univ rowBlock
      (fun sourceRow ↦ current sourceRow wallColumn *
        reference.adjugate wallColumn sourceRow))

/-- Contribution of one source wall block after every changing-column entry
has been decomposed into block-indexed summands. -/
noncomputable def wallEntrySummandContribution
    {block : Type*} [Fintype block]
    (reference : Matrix row row ℚ) (wallColumn : row)
    (entrySummand : block → row → ℚ) (sourceBlock : block) : ℚ :=
  ∑ sourceRow, entrySummand sourceBlock sourceRow *
    reference.adjugate wallColumn sourceRow

/-- General wall-column determinant decomposition.  A row may contribute to
several source blocks: only its changing-column entry must be a sum of the
displayed block summands. -/
theorem det_eq_sum_wallEntrySummandContribution
    {block : Type*} [Fintype block]
    {reference current : Matrix row row ℚ} {wallColumn : row}
    (entrySummand : block → row → ℚ)
    (hEntry : ∀ sourceRow,
      current sourceRow wallColumn =
        ∑ sourceBlock, entrySummand sourceBlock sourceRow)
    (hAgree : AgreeOffColumn current reference wallColumn) :
    current.det = ∑ sourceBlock,
      wallEntrySummandContribution reference wallColumn entrySummand
        sourceBlock := by
  classical
  calc
    current.det = ∑ sourceRow,
        current sourceRow wallColumn *
          reference.adjugate wallColumn sourceRow :=
      det_eq_sum_wallColumn_mul_commonCofactor hAgree
    _ = ∑ sourceRow, ∑ sourceBlock,
        entrySummand sourceBlock sourceRow *
          reference.adjugate wallColumn sourceRow := by
            apply Finset.sum_congr rfl
            intro sourceRow _
            rw [hEntry sourceRow, Finset.sum_mul]
    _ = ∑ sourceBlock, ∑ sourceRow,
        entrySummand sourceBlock sourceRow *
          reference.adjugate wallColumn sourceRow := by
            exact Finset.sum_comm
    _ = ∑ sourceBlock,
        wallEntrySummandContribution reference wallColumn entrySummand
          sourceBlock := rfl

/-- Cofactor-weighted contribution of one matrix column. -/
noncomputable def columnContribution (matrix : Matrix row row ℚ)
    (wallColumn column : row) : ℚ :=
  ∑ sourceRow, matrix sourceRow column *
    matrix.adjugate wallColumn sourceRow

/-- Every column other than the expansion column has zero contribution.  This
is the off-diagonal entry of `adjugate matrix * matrix = det matrix • 1`. -/
theorem columnContribution_eq_zero (matrix : Matrix row row ℚ)
    {wallColumn column : row} (hne : column ≠ wallColumn) :
    columnContribution matrix wallColumn column = 0 := by
  have hAdjugate := congrFun
    (congrFun (Matrix.adjugate_mul matrix) wallColumn) column
  simpa [columnContribution, Matrix.mul_apply, Matrix.one_apply, hne,
    Ne.symm hne, mul_comm] using hAdjugate

/-- Contribution of the displayed old target columns coming from the rows in
one source wall block. -/
noncomputable def oldBlockContribution
    {block : Type*} [Fintype block]
    (matrix : Matrix row row ℚ) (wallColumn : row)
    (rowBlock : row → block) (oldColumns : Finset row)
    (sourceBlock : block) : ℚ := by
  classical
  exact ∑ column ∈ oldColumns,
    ∑ sourceRow ∈ Finset.univ with rowBlock sourceRow = sourceBlock,
      matrix sourceRow column * matrix.adjugate wallColumn sourceRow

/-- If every displayed old column differs from the wall column, its
cofactor-weighted contributions sum to zero even after grouping rows by source
wall block.  This is the generic old wall-column relation. -/
theorem sum_oldBlockContribution_eq_zero
    {block : Type*} [Fintype block]
    (matrix : Matrix row row ℚ) (wallColumn : row)
    (rowBlock : row → block) (oldColumns : Finset row)
    (hOld : ∀ column ∈ oldColumns, column ≠ wallColumn) :
    ∑ sourceBlock,
      oldBlockContribution matrix wallColumn rowBlock oldColumns
        sourceBlock = 0 := by
  classical
  calc
    ∑ sourceBlock,
        oldBlockContribution matrix wallColumn rowBlock oldColumns
          sourceBlock =
        ∑ column ∈ oldColumns,
          ∑ sourceBlock,
            ∑ sourceRow ∈ Finset.univ with
              rowBlock sourceRow = sourceBlock,
              matrix sourceRow column *
                matrix.adjugate wallColumn sourceRow := by
          simp only [oldBlockContribution]
          rw [Finset.sum_comm]
    _ = ∑ column ∈ oldColumns,
        columnContribution matrix wallColumn column := by
          apply Finset.sum_congr rfl
          intro column _
          rw [columnContribution]
          simpa using
            (Finset.sum_fiberwise (M := ℚ) Finset.univ rowBlock
              (fun sourceRow ↦ matrix sourceRow column *
                matrix.adjugate wallColumn sourceRow))
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro column hColumn
      exact columnContribution_eq_zero matrix (hOld column hColumn)

/-- Contribution from one source wall block to a finite family of old target
columns, when each matrix entry has been split into block summands. -/
noncomputable def oldEntrySummandContribution
    {block : Type*} [Fintype block]
    (matrix : Matrix row row ℚ) (wallColumn : row)
    (oldColumns : Finset row)
    (entrySummand : block → row → row → ℚ) (sourceBlock : block) : ℚ :=
  ∑ column ∈ oldColumns, ∑ sourceRow,
    entrySummand sourceBlock column sourceRow *
      matrix.adjugate wallColumn sourceRow

/-- General old-column relation with entry-level block decomposition.  It
allows one stable-path row to contain source edges from several wall blocks. -/
theorem sum_oldEntrySummandContribution_eq_zero
    {block : Type*} [Fintype block]
    (matrix : Matrix row row ℚ) (wallColumn : row)
    (oldColumns : Finset row)
    (entrySummand : block → row → row → ℚ)
    (hEntry : ∀ column ∈ oldColumns, ∀ sourceRow,
      matrix sourceRow column =
        ∑ sourceBlock, entrySummand sourceBlock column sourceRow)
    (hOld : ∀ column ∈ oldColumns, column ≠ wallColumn) :
    ∑ sourceBlock,
      oldEntrySummandContribution matrix wallColumn oldColumns entrySummand
        sourceBlock = 0 := by
  classical
  calc
    ∑ sourceBlock,
        oldEntrySummandContribution matrix wallColumn oldColumns entrySummand
          sourceBlock =
        ∑ column ∈ oldColumns, ∑ sourceRow,
          matrix sourceRow column *
            matrix.adjugate wallColumn sourceRow := by
              simp only [oldEntrySummandContribution]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro column hColumn
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro sourceRow _
              rw [hEntry column hColumn sourceRow, Finset.sum_mul]
    _ = ∑ column ∈ oldColumns,
        columnContribution matrix wallColumn column := by
          apply Finset.sum_congr rfl
          intro column _
          rfl
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro column hColumn
      exact columnContribution_eq_zero matrix (hOld column hColumn)

end DraismaVargas.Infrastructure
