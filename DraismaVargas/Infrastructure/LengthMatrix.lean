module

public import DraismaVargas.Infrastructure.GluingRealization
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

/-!
# Length matrices from occurrence-labelled source paths

For a source edge block above a target occurrence `t`, harmonicity forces its
length to be the target length divided by the block's dilation index. A stable
source edge is a path of such blocks, so its length is the sum of those
fractions. This is the entry formula

`a_(h,t) = ∑_{e in h, φ(e)=t} 1 / m(e)`

used for the Draisma--Vargas edge-length matrix.

This module states the formula directly on `GluingDatum.SourceEdge`, retaining
target-edge occurrence identity. The presentation deliberately supplies the
stable paths: proving that a particular path family is the essential source
type is separate finite combinatorics, while the rational matrix and its
metric semantics are uniform.
-/

namespace DraismaVargas.Infrastructure

open Matrix

namespace GluingDatum

variable {target : CFGraph} {degree : ℕ}

/-- Every source-edge dilation index is positive. -/
theorem sourceEdgeIndex_pos (data : GluingDatum target degree)
    (edge : data.SourceEdge) : 0 < data.sourceEdgeIndex edge :=
  (data.edgePartition edge.1.1).blockCard_pos edge.1.2

/-- Rational length of one source edge block under a target length vector. -/
def sourceEdgeLength (data : GluingDatum target degree)
    (targetLength : target.edges → ℚ) (edge : data.SourceEdge) : ℚ :=
  targetLength edge.1.1 / data.sourceEdgeIndex edge

/-- Length of an occurrence-labelled source path. -/
def sourcePathLength (data : GluingDatum target degree)
    (targetLength : target.edges → ℚ) (path : List data.SourceEdge) : ℚ :=
  (path.map (data.sourceEdgeLength targetLength)).sum

/-- A square coordinate presentation of the target occurrences and stable
source paths. In the full-dimensional Draisma--Vargas application the common
coordinate type labels both sets, but the paths themselves retain exact
source-edge occurrences. -/
structure LengthMatrixPresentation (data : GluingDatum target degree)
    (coordinate : Type*) where
  targetEdge : coordinate ≃ target.edges
  path : coordinate → List data.SourceEdge

namespace LengthMatrixPresentation

variable {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (presentation : data.LengthMatrixPresentation coordinate)

/-- Contribution of one source edge block to one target column. -/
noncomputable def coefficient (edge : data.SourceEdge)
    (column : coordinate) : ℚ := by
  classical
  exact if column = presentation.targetEdge.symm edge.1.1 then
      1 / data.sourceEdgeIndex edge
    else 0

omit [Fintype coordinate] in
/-- On the target column containing a source edge, its cofactor-weighted
matrix contribution is the paper's literal term `c(h(e)) / m(e)`. -/
theorem coefficient_mul_eq_cofactor_div (edge : data.SourceEdge)
    (column : coordinate) (cofactor : ℚ)
    (hTarget : presentation.targetEdge column = edge.1.1) :
    coefficient presentation edge column * cofactor =
      cofactor / data.sourceEdgeIndex edge := by
  have hColumn : column = presentation.targetEdge.symm edge.1.1 := by
    apply presentation.targetEdge.injective
    simpa using hTarget
  simp [coefficient, hColumn, div_eq_mul_inv, mul_comm]

omit [Fintype coordinate] in
/-- A source edge contributes zero to every other target column. -/
theorem coefficient_eq_zero_of_target_ne (edge : data.SourceEdge)
    (column : coordinate)
    (hTarget : presentation.targetEdge column ≠ edge.1.1) :
    coefficient presentation edge column = 0 := by
  have hColumn : column ≠ presentation.targetEdge.symm edge.1.1 := by
    intro h
    apply hTarget
    simp [h]
  simp [coefficient, hColumn]

/-- One row of the rational length matrix. -/
noncomputable def row (path : List data.SourceEdge) : coordinate → ℚ :=
  fun column ↦
    (path.map (fun edge ↦ coefficient presentation edge column)).sum

omit [Fintype coordinate] in
/-- **Splitting a displayed path in two splits its row additively.**  The row
is a list sum over the path, so concatenating paths adds rows columnwise; this
is what lets an extension step be computed block by block. -/
theorem row_append (first second : List data.SourceEdge) (column : coordinate) :
    row presentation (first ++ second) column =
      row presentation first column + row presentation second column := by
  simp [row, List.map_append, List.sum_append]

/-- Contribution to one matrix entry from path edges carrying a fixed finite
block label.  This retains multiplicity because it sums over the path list,
not a finset of source edges. -/
noncomputable def pathBlockCoefficient
    {block : Type*} [Fintype block]
    (edgeBlock : data.SourceEdge → block) (sourceBlock : block)
    (path : List data.SourceEdge) (column : coordinate) : ℚ := by
  classical
  exact (path.map fun edge ↦
    if edgeBlock edge = sourceBlock then
      coefficient presentation edge column
    else 0).sum

/-- Cofactor-weighted version of one path's block contribution, expanded as
the literal sum over its source-edge occurrences. -/
noncomputable def pathBlockCofactorContribution
    {block : Type*} [Fintype block]
    (edgeBlock : data.SourceEdge → block) (sourceBlock : block)
    (path : List data.SourceEdge) (column : coordinate) (cofactor : ℚ) : ℚ := by
  classical
  exact (path.map fun edge ↦
    if edgeBlock edge = sourceBlock then
      coefficient presentation edge column * cofactor
    else 0).sum

/-- The paper's literal path contribution: each matching source edge
contributes the stable-row cofactor divided by its dilation index. -/
noncomputable def pathBlockQuotientContribution
    {block : Type*} [Fintype block]
    (edgeBlock : data.SourceEdge → block) (sourceBlock : block)
    (path : List data.SourceEdge) (column : coordinate) (cofactor : ℚ) : ℚ := by
  classical
  exact (path.map fun edge ↦
    if edgeBlock edge = sourceBlock then
      if presentation.targetEdge column = edge.1.1 then
        cofactor / data.sourceEdgeIndex edge
      else 0
    else 0).sum

omit [Fintype coordinate] in
/-- Expanding the matrix coefficient turns the cofactor sum into the literal
`c(h(e)) / m(e)` sum over the path's matching source edges. -/
theorem pathBlockCofactorContribution_eq_quotient
    {block : Type*} [Fintype block]
    (edgeBlock : data.SourceEdge → block) (sourceBlock : block)
    (path : List data.SourceEdge) (column : coordinate) (cofactor : ℚ) :
    pathBlockCofactorContribution presentation edgeBlock sourceBlock path
        column cofactor =
      pathBlockQuotientContribution presentation edgeBlock sourceBlock path
        column cofactor := by
  classical
  induction path with
  | nil => simp [pathBlockCofactorContribution,
      pathBlockQuotientContribution]
  | cons edge rest ih =>
      simp only [pathBlockCofactorContribution,
        pathBlockQuotientContribution] at ih
      simp only [pathBlockCofactorContribution,
        pathBlockQuotientContribution, List.map_cons, List.sum_cons]
      by_cases hBlock : edgeBlock edge = sourceBlock
      · rw [ite_eq_left hBlock, ite_eq_left hBlock]
        by_cases hTarget : presentation.targetEdge column = edge.1.1
        · rw [ite_eq_left hTarget,
            coefficient_mul_eq_cofactor_div presentation edge column
              cofactor hTarget, ih]
        · rw [ite_eq_right hTarget,
            coefficient_eq_zero_of_target_ne presentation edge column hTarget,
            zero_mul, ih]
      · rw [ite_eq_right hBlock, ite_eq_right hBlock, ih]

omit [Fintype coordinate] in
/-- Multiplying a path's grouped coefficient by a cofactor distributes to
the literal edge-occurrence sum. -/
theorem pathBlockCoefficient_mul
    {block : Type*} [Fintype block]
    (edgeBlock : data.SourceEdge → block) (sourceBlock : block)
    (path : List data.SourceEdge) (column : coordinate) (cofactor : ℚ) :
    pathBlockCoefficient presentation edgeBlock sourceBlock path column *
        cofactor =
      pathBlockCofactorContribution presentation edgeBlock sourceBlock path
        column cofactor := by
  classical
  induction path with
  | nil => simp [pathBlockCoefficient, pathBlockCofactorContribution]
  | cons edge rest ih =>
      simp only [pathBlockCoefficient, pathBlockCofactorContribution] at ih
      simp only [pathBlockCoefficient, pathBlockCofactorContribution,
        List.map_cons, List.sum_cons]
      rw [add_mul, ih]
      by_cases hBlock : edgeBlock edge = sourceBlock <;> simp [hBlock]

omit [Fintype coordinate] in
/-- Every path-row entry is the sum of its edge-level block contributions. -/
theorem row_eq_sum_pathBlockCoefficient
    {block : Type*} [Fintype block]
    (edgeBlock : data.SourceEdge → block)
    (path : List data.SourceEdge) (column : coordinate) :
    row presentation path column = ∑ sourceBlock,
      pathBlockCoefficient presentation edgeBlock sourceBlock path column := by
  classical
  induction path with
  | nil => simp [row, pathBlockCoefficient]
  | cons edge rest ih =>
      simp only [row, pathBlockCoefficient] at ih
      simp only [row, pathBlockCoefficient, List.map_cons, List.sum_cons]
      rw [ih]
      rw [Finset.sum_add_distrib]
      simp

/-- The Draisma--Vargas edge-length matrix attached to the displayed stable paths. -/
noncomputable def matrix : Matrix coordinate coordinate ℚ :=
  fun sourceRow column ↦
    row presentation (presentation.path sourceRow) column

/-- Contribution of one source-edge block label to one presented matrix
entry. -/
noncomputable def blockCoefficient
    {block : Type*} [Fintype block]
    (edgeBlock : data.SourceEdge → block) (sourceBlock : block)
    (sourceRow column : coordinate) : ℚ :=
  pathBlockCoefficient presentation edgeBlock sourceBlock
    (presentation.path sourceRow) column

/-- Cofactor-weighted source-edge contribution of one block to one target
column, summed over all displayed stable-path rows. -/
noncomputable def blockCofactorContribution
    {block : Type*} [Fintype block]
    (edgeBlock : data.SourceEdge → block) (sourceBlock : block)
    (column : coordinate) (cofactor : coordinate → ℚ) : ℚ :=
  ∑ sourceRow,
    pathBlockCofactorContribution presentation edgeBlock sourceBlock
      (presentation.path sourceRow) column (cofactor sourceRow)

/-- The paper's literal `c(h(e)) / m(e)` contribution of one source block and
one target column, summed over all stable paths. -/
noncomputable def blockQuotientContribution
    {block : Type*} [Fintype block]
    (edgeBlock : data.SourceEdge → block) (sourceBlock : block)
    (column : coordinate) (cofactor : coordinate → ℚ) : ℚ :=
  ∑ sourceRow,
    pathBlockQuotientContribution presentation edgeBlock sourceBlock
      (presentation.path sourceRow) column (cofactor sourceRow)

/-- Retain one source-edge quotient term exactly when it belongs to the
chosen source block and target occurrence. -/
noncomputable def matchingQuotientTerm
    {block : Type*}
    (edgeBlock : data.SourceEdge → block) (sourceBlock : block)
    (column : coordinate) (cofactor : ℚ)
    (edge : data.SourceEdge) : Option ℚ := by
  classical
  exact if edgeBlock edge = sourceBlock ∧
      presentation.targetEdge column = edge.1.1 then
    some (cofactor / data.sourceEdgeIndex edge)
  else none

/-- Retain the actual stable-row/source-edge pair exactly when it belongs to
the chosen source block and target occurrence. -/
noncomputable def matchingOccurrence
    {block : Type*}
    (edgeBlock : data.SourceEdge → block) (sourceBlock : block)
    (column sourceRow : coordinate) (edge : data.SourceEdge) :
    Option (coordinate × data.SourceEdge) := by
  classical
  exact if edgeBlock edge = sourceBlock ∧
      presentation.targetEdge column = edge.1.1 then
    some (sourceRow, edge)
  else none

/-- Multiplicity-preserving multiset of actual `(stable row, source edge)`
occurrences contributing to one block and target column. -/
noncomputable def blockColumnOccurrences
    {block : Type*} [Fintype block]
    (edgeBlock : data.SourceEdge → block) (sourceBlock : block)
    (column : coordinate) : Multiset (coordinate × data.SourceEdge) := by
  classical
  exact ∑ sourceRow,
    Multiset.ofList
      ((presentation.path sourceRow).filterMap
        (matchingOccurrence presentation edgeBlock sourceBlock column
          sourceRow))

/-- The multiplicity-preserving multiset of literal quotient terms belonging
to one source block and target column.  Unlike the numerical sum, this is a
direct finite classification target: a local case can prove that it is empty,
a singleton, or a prescribed collection of old branch terms. -/
noncomputable def blockColumnTerms
    {block : Type*} [Fintype block]
    (edgeBlock : data.SourceEdge → block) (sourceBlock : block)
    (column : coordinate) (cofactor : coordinate → ℚ) : Multiset ℚ := by
  classical
  exact ∑ sourceRow,
    Multiset.ofList
      ((presentation.path sourceRow).filterMap
        (matchingQuotientTerm presentation edgeBlock sourceBlock column
          (cofactor sourceRow)))

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- Weighting the exact occurrence list of one stable path gives precisely
its filtered quotient-term list. -/
theorem map_matchingOccurrences_eq_matchingTerms
    {block : Type*} [Fintype block]
    (edgeBlock : data.SourceEdge → block) (sourceBlock : block)
    (path : List data.SourceEdge) (column sourceRow : coordinate)
    (cofactor : coordinate → ℚ) :
    (Multiset.ofList
      (path.filterMap
        (matchingOccurrence presentation edgeBlock sourceBlock column
          sourceRow))).map
        (fun occurrence ↦
          cofactor occurrence.1 / data.sourceEdgeIndex occurrence.2) =
      Multiset.ofList
        (path.filterMap
          (matchingQuotientTerm presentation edgeBlock sourceBlock column
            (cofactor sourceRow))) := by
  classical
  induction path with
  | nil => simp
  | cons edge rest ih =>
      rw [List.filterMap_cons, List.filterMap_cons]
      by_cases hBlock : edgeBlock edge = sourceBlock
      · by_cases hTarget : presentation.targetEdge column = edge.1.1
        · rw [show matchingOccurrence presentation edgeBlock sourceBlock
              column sourceRow edge = some (sourceRow, edge) by
                simp [matchingOccurrence, hBlock, hTarget]]
          rw [show matchingQuotientTerm presentation edgeBlock sourceBlock
              column (cofactor sourceRow) edge =
                some (cofactor sourceRow / data.sourceEdgeIndex edge) by
                simp [matchingQuotientTerm, hBlock, hTarget]]
          simpa using congrArg (fun terms =>
            (cofactor sourceRow / data.sourceEdgeIndex edge) ::ₘ terms) ih
        · rw [show matchingOccurrence presentation edgeBlock sourceBlock
              column sourceRow edge = none by
                simp [matchingOccurrence, hBlock, hTarget]]
          rw [show matchingQuotientTerm presentation edgeBlock sourceBlock
              column (cofactor sourceRow) edge = none by
                simp [matchingQuotientTerm, hBlock, hTarget]]
          exact ih
      · rw [show matchingOccurrence presentation edgeBlock sourceBlock
            column sourceRow edge = none by
              simp [matchingOccurrence, hBlock]]
        rw [show matchingQuotientTerm presentation edgeBlock sourceBlock
            column (cofactor sourceRow) edge = none by
              simp [matchingQuotientTerm, hBlock]]
        exact ih

omit [DecidableEq coordinate] in
/-- The rational term multiset is obtained by weighting the independently
classified `(stable row, source edge)` occurrence multiset. -/
theorem blockColumnTerms_eq_occurrences_map
    {block : Type*} [Fintype block]
    (edgeBlock : data.SourceEdge → block) (sourceBlock : block)
    (column : coordinate) (cofactor : coordinate → ℚ) :
    blockColumnTerms presentation edgeBlock sourceBlock column cofactor =
      (blockColumnOccurrences presentation edgeBlock sourceBlock column).map
        (fun occurrence ↦
          cofactor occurrence.1 / data.sourceEdgeIndex occurrence.2) := by
  classical
  unfold blockColumnTerms blockColumnOccurrences
  calc
    (∑ sourceRow,
      Multiset.ofList
        ((presentation.path sourceRow).filterMap
          (matchingQuotientTerm presentation edgeBlock sourceBlock column
            (cofactor sourceRow)))) =
        ∑ sourceRow,
          (Multiset.ofList
            ((presentation.path sourceRow).filterMap
              (matchingOccurrence presentation edgeBlock sourceBlock column
                sourceRow))).map
            (fun occurrence ↦
              cofactor occurrence.1 / data.sourceEdgeIndex occurrence.2) := by
      apply Finset.sum_congr rfl
      intro sourceRow _
      exact (map_matchingOccurrences_eq_matchingTerms presentation edgeBlock
        sourceBlock (presentation.path sourceRow) column sourceRow
          cofactor).symm
    _ = (∑ sourceRow,
          Multiset.ofList
            ((presentation.path sourceRow).filterMap
              (matchingOccurrence presentation edgeBlock sourceBlock column
                sourceRow))).map
          (fun occurrence ↦
            cofactor occurrence.1 / data.sourceEdgeIndex occurrence.2) := by
      symm
      exact map_sum (Multiset.mapAddMonoidHom fun occurrence =>
        cofactor occurrence.1 / data.sourceEdgeIndex occurrence.2)
        (fun sourceRow ↦
          Multiset.ofList
            ((presentation.path sourceRow).filterMap
              (matchingOccurrence presentation edgeBlock sourceBlock column
                sourceRow))) Finset.univ

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- Filtering a single path for its matching block and target occurrence
removes exactly the zero branches in the quotient-sum definition. -/
theorem pathBlockQuotientContribution_eq_filtered_sum
    {block : Type*} [Fintype block]
    (edgeBlock : data.SourceEdge → block) (sourceBlock : block)
    (path : List data.SourceEdge) (column : coordinate) (cofactor : ℚ) :
    pathBlockQuotientContribution presentation edgeBlock sourceBlock path
        column cofactor =
      (path.filterMap
        (matchingQuotientTerm presentation edgeBlock sourceBlock column
          cofactor)).sum := by
  classical
  induction path with
  | nil => simp [pathBlockQuotientContribution]
  | cons edge rest ih =>
      change
        (if edgeBlock edge = sourceBlock then
          if presentation.targetEdge column = edge.1.1 then
            cofactor / data.sourceEdgeIndex edge
          else 0
        else 0) +
          pathBlockQuotientContribution presentation edgeBlock sourceBlock
            rest column cofactor =
        (List.filterMap
          (matchingQuotientTerm presentation edgeBlock sourceBlock column
            cofactor) (edge :: rest)).sum
      by_cases hBlock : edgeBlock edge = sourceBlock
      · by_cases hTarget : presentation.targetEdge column = edge.1.1
        · rw [ite_eq_left hBlock, ite_eq_left hTarget]
          rw [List.filterMap_cons]
          rw [show matchingQuotientTerm presentation edgeBlock sourceBlock
            column cofactor edge =
              some (cofactor / data.sourceEdgeIndex edge) by
                simp [matchingQuotientTerm, hBlock, hTarget]]
          simp only [List.sum_cons]
          rw [ih]
        · rw [ite_eq_left hBlock, ite_eq_right hTarget, zero_add]
          rw [List.filterMap_cons]
          rw [show matchingQuotientTerm presentation edgeBlock sourceBlock
            column cofactor edge = none by
                simp [matchingQuotientTerm, hBlock, hTarget]]
          exact ih
      · rw [ite_eq_right hBlock, zero_add]
        rw [List.filterMap_cons]
        rw [show matchingQuotientTerm presentation edgeBlock sourceBlock
          column cofactor edge = none by
              simp [matchingQuotientTerm, hBlock]]
        exact ih

omit [DecidableEq coordinate] in
/-- The numerical block quotient is the sum of its occurrence-level term
multiset.  This is the bridge from finite stable-path classification to the
numeric receipt consumed by the determinant identity. -/
theorem blockQuotientContribution_eq_terms_sum
    {block : Type*} [Fintype block]
    (edgeBlock : data.SourceEdge → block) (sourceBlock : block)
    (column : coordinate) (cofactor : coordinate → ℚ) :
    blockQuotientContribution presentation edgeBlock sourceBlock column
        cofactor =
      (blockColumnTerms presentation edgeBlock sourceBlock column cofactor).sum := by
  classical
  calc
    blockQuotientContribution presentation edgeBlock sourceBlock column
        cofactor =
        ∑ sourceRow,
          (Multiset.ofList
            ((presentation.path sourceRow).filterMap
              (matchingQuotientTerm presentation edgeBlock sourceBlock column
                (cofactor sourceRow)))).sum := by
      unfold blockQuotientContribution
      apply Finset.sum_congr rfl
      intro sourceRow _
      simpa using pathBlockQuotientContribution_eq_filtered_sum presentation
        edgeBlock sourceBlock (presentation.path sourceRow) column
          (cofactor sourceRow)
    _ = (blockColumnTerms presentation edgeBlock sourceBlock column
          cofactor).sum := by
      unfold blockColumnTerms
      symm
      exact map_sum (Multiset.sumAddMonoidHom : Multiset ℚ →+ ℚ)
        (fun sourceRow ↦
          Multiset.ofList
            ((presentation.path sourceRow).filterMap
              (matchingQuotientTerm presentation edgeBlock sourceBlock column
                (cofactor sourceRow)))) Finset.univ

/-- Occurrence-level terms contributed by a finite family of target columns. -/
noncomputable def blockColumnsTerms
    {block : Type*} [Fintype block]
    (edgeBlock : data.SourceEdge → block) (sourceBlock : block)
    (columns : Finset coordinate) (cofactor : coordinate → ℚ) : Multiset ℚ :=
  ∑ column ∈ columns,
    blockColumnTerms presentation edgeBlock sourceBlock column cofactor

/-- Actual stable-row/source-edge occurrences contributed by a finite family
of target columns, before any cofactor or dilation-index weights are applied. -/
noncomputable def blockColumnsOccurrences
    {block : Type*} [Fintype block]
    (edgeBlock : data.SourceEdge → block) (sourceBlock : block)
    (columns : Finset coordinate) : Multiset (coordinate × data.SourceEdge) :=
  ∑ column ∈ columns,
    blockColumnOccurrences presentation edgeBlock sourceBlock column

omit [DecidableEq coordinate] in
/-- Weighting the occurrence classification for a family of columns gives
exactly its combined rational term multiset. -/
theorem blockColumnsTerms_eq_occurrences_map
    {block : Type*} [Fintype block]
    (edgeBlock : data.SourceEdge → block) (sourceBlock : block)
    (columns : Finset coordinate) (cofactor : coordinate → ℚ) :
    blockColumnsTerms presentation edgeBlock sourceBlock columns cofactor =
      (blockColumnsOccurrences presentation edgeBlock sourceBlock columns).map
        (fun occurrence ↦
          cofactor occurrence.1 / data.sourceEdgeIndex occurrence.2) := by
  classical
  unfold blockColumnsTerms blockColumnsOccurrences
  simp_rw [blockColumnTerms_eq_occurrences_map]
  symm
  exact map_sum (Multiset.mapAddMonoidHom fun occurrence =>
    cofactor occurrence.1 / data.sourceEdgeIndex occurrence.2)
    (fun column ↦
      blockColumnOccurrences presentation edgeBlock sourceBlock column)
    columns

omit [DecidableEq coordinate] in
/-- Summing the numerical quotients over old columns is the sum of their
combined occurrence multiset. -/
theorem sum_blockQuotientContribution_eq_terms_sum
    {block : Type*} [Fintype block]
    (edgeBlock : data.SourceEdge → block) (sourceBlock : block)
    (columns : Finset coordinate) (cofactor : coordinate → ℚ) :
    (∑ column ∈ columns,
      blockQuotientContribution presentation edgeBlock sourceBlock column
        cofactor) =
      (blockColumnsTerms presentation edgeBlock sourceBlock columns
        cofactor).sum := by
  classical
  simp only [blockColumnsTerms,
    blockQuotientContribution_eq_terms_sum]
  symm
  exact map_sum (Multiset.sumAddMonoidHom : Multiset ℚ →+ ℚ)
    (fun column ↦
      blockColumnTerms presentation edgeBlock sourceBlock column cofactor)
    columns

/-- The cofactor-weighted matrix contribution is exactly the paper's nested
quotient sum. -/
theorem blockCofactorContribution_eq_quotient
    {block : Type*} [Fintype block]
    (edgeBlock : data.SourceEdge → block) (sourceBlock : block)
    (column : coordinate) (cofactor : coordinate → ℚ) :
    blockCofactorContribution presentation edgeBlock sourceBlock column
        cofactor =
      blockQuotientContribution presentation edgeBlock sourceBlock column
        cofactor := by
  classical
  unfold blockCofactorContribution blockQuotientContribution
  apply Finset.sum_congr rfl
  intro sourceRow _
  exact pathBlockCofactorContribution_eq_quotient presentation edgeBlock
    sourceBlock (presentation.path sourceRow) column (cofactor sourceRow)

/-- A cofactor-weighted sum of grouped matrix-entry coefficients is exactly
the nested sum over the source-edge occurrences in the stable paths. -/
theorem sum_blockCoefficient_mul_eq_blockCofactorContribution
    {block : Type*} [Fintype block]
    (edgeBlock : data.SourceEdge → block) (sourceBlock : block)
    (column : coordinate) (cofactor : coordinate → ℚ) :
    (∑ sourceRow,
      blockCoefficient presentation edgeBlock sourceBlock sourceRow column *
        cofactor sourceRow) =
      blockCofactorContribution presentation edgeBlock sourceBlock column
        cofactor := by
  classical
  unfold blockCofactorContribution blockCoefficient
  apply Finset.sum_congr rfl
  intro sourceRow _
  exact pathBlockCoefficient_mul presentation edgeBlock sourceBlock
    (presentation.path sourceRow) column (cofactor sourceRow)

omit [Fintype coordinate] in
/-- Each length-matrix entry decomposes automatically as a finite sum over
the block labels of its constituent source path edges. -/
theorem matrix_apply_eq_sum_blockCoefficient
    {block : Type*} [Fintype block]
    (edgeBlock : data.SourceEdge → block)
    (sourceRow column : coordinate) :
    matrix presentation sourceRow column = ∑ sourceBlock,
      blockCoefficient presentation edgeBlock sourceBlock sourceRow column :=
  row_eq_sum_pathBlockCoefficient presentation edgeBlock
    (presentation.path sourceRow) column

private theorem sum_coefficient_mul (edge : data.SourceEdge)
    (targetLength : coordinate → ℚ) :
    ∑ column, coefficient presentation edge column * targetLength column =
      targetLength (presentation.targetEdge.symm edge.1.1) /
        data.sourceEdgeIndex edge := by
  simp [coefficient, div_eq_mul_inv, mul_comm]

private theorem sum_row_mul (path : List data.SourceEdge)
    (targetLength : coordinate → ℚ) :
    ∑ column, row presentation path column * targetLength column =
      data.sourcePathLength
        (fun edge ↦ targetLength (presentation.targetEdge.symm edge)) path := by
  induction path with
  | nil => simp [row, GluingDatum.sourcePathLength]
  | cons edge rest ih =>
      change
        (∑ column,
          (coefficient presentation edge column +
              row presentation rest column) * targetLength column) =
        data.sourceEdgeLength
            (fun targetEdge ↦
              targetLength (presentation.targetEdge.symm targetEdge)) edge +
          data.sourcePathLength
            (fun targetEdge ↦
              targetLength (presentation.targetEdge.symm targetEdge)) rest
      simp only [add_mul, Finset.sum_add_distrib]
      rw [sum_coefficient_mul presentation edge targetLength, ih]
      rfl

/-- Matrix multiplication is exactly the vector of stable source-path
lengths obtained from the target coordinate vector. -/
theorem matrix_mulVec (targetLength : coordinate → ℚ)
    (sourceRow : coordinate) :
    (matrix presentation).mulVec targetLength sourceRow =
      data.sourcePathLength
        (fun edge ↦ targetLength (presentation.targetEdge.symm edge))
        (presentation.path sourceRow) := by
  exact sum_row_mul presentation (presentation.path sourceRow) targetLength

end LengthMatrixPresentation

namespace IntegralRealization

variable {data : GluingDatum target degree}

/-- The integral realization equation identifies its stored source length
with target length divided by the source-edge index. -/
theorem sourceEdgeLength_eq (realization : data.IntegralRealization)
    (edge : data.SourceEdge) :
    data.sourceEdgeLength (fun targetEdge ↦ realization.targetLength targetEdge) edge =
      realization.sourceLength edge := by
  have hIndex : (data.sourceEdgeIndex edge : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (data.sourceEdgeIndex_pos edge))
  have hDilation :
      (data.sourceEdgeIndex edge : ℚ) *
          (realization.sourceLength edge : ℚ) =
        (realization.targetLength edge.1.1 : ℚ) := by
    exact_mod_cast realization.dilation_length edge
  unfold GluingDatum.sourceEdgeLength
  apply (div_eq_iff hIndex).2
  simpa [mul_comm] using hDilation.symm

/-- Hence the rational path formula recovers the literal sum of stored
integral source-edge lengths. -/
theorem sourcePathLength_eq (realization : data.IntegralRealization)
    (path : List data.SourceEdge) :
    data.sourcePathLength
        (fun targetEdge ↦ realization.targetLength targetEdge) path =
      (path.map (fun edge ↦ (realization.sourceLength edge : ℚ))).sum := by
  induction path with
  | nil => simp [GluingDatum.sourcePathLength]
  | cons edge rest ih =>
      change
        data.sourceEdgeLength
            (fun targetEdge ↦ realization.targetLength targetEdge) edge +
          data.sourcePathLength
            (fun targetEdge ↦ realization.targetLength targetEdge) rest =
        (realization.sourceLength edge : ℚ) +
          (rest.map
            (fun sourceEdge ↦
              (realization.sourceLength sourceEdge : ℚ))).sum
      rw [realization.sourceEdgeLength_eq, ih]

end IntegralRealization

/-- Evaluating a presented length matrix on the target lengths of an integral
realization gives the actual sum of source lengths along every displayed
stable path. -/
theorem LengthMatrixPresentation.matrix_mulVec_realization
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    {data : GluingDatum target degree}
    (presentation : data.LengthMatrixPresentation coordinate)
    (realization : data.IntegralRealization) (sourceRow : coordinate) :
    (LengthMatrixPresentation.matrix presentation).mulVec
        (fun column ↦
          (realization.targetLength (presentation.targetEdge column) : ℚ))
        sourceRow =
      ((presentation.path sourceRow).map
        (fun edge ↦ (realization.sourceLength edge : ℚ))).sum := by
  rw [LengthMatrixPresentation.matrix_mulVec presentation]
  simpa using realization.sourcePathLength_eq (presentation.path sourceRow)

end GluingDatum

end DraismaVargas.Infrastructure
