module

public import DraismaVargasCount.IndexPattern

@[expose] public section

/-!
# The row denominators `d_i` of a full-dimensional morphism

**Source.**  Vargas, Part II (arXiv:2609.09109), the lemma on edge denominators
(`lemma-edge-deno`): for `φ ∈ FD_g` with edge-length matrix `A_φ` and `h_i` a
stable row, exactly one of

* (a) `h_i` passes above a leaf and `d_i = 1`;
* (b) `h_i` avoids leaves, its edge indices are constantly `k`, and `d_i = k`;
* (c) `h_i` avoids leaves, its edge indices take the two values `k` and `k+1`,
  and `d_i = k(k+1)`.

The local inputs are proved elsewhere: `IndexPattern`'s
`sourceEdgeIndex_eq_one_of_row_eq_leafRow` is the whole of case (a) (Part II
argues it by a kernel perturbation; `IndexPattern` uses a full-rank column
argument instead, which gives the same conclusion), and `LeafFibre`'s
`leafRow`/`row_eq_leafRow` identify the
leaf-passing rows.  What is added here is the arithmetic: the entries of row
`i` are the fibre sums `∑ 1/m(e)` of `Count.LeafFibre.matrix_eq_sum_fibre`, so
the least common denominator of the row is controlled by the indices occurring
on it.

## What is proved

* `rowEdges` -- the surviving source occurrences displayed on one stable row,
  with `rowEdges_eq_toFinset_path` and `mem_rowFibre_iff` relating it to
  `StableLengthMatrixLabelling.path` and to `Count.LeafFibre.rowFibre`.
* `rowDenominator_dvd_of_forall_index_dvd` -- **the upper bound**, and the
  engine of the whole file: if every index occurring on row `i` divides `N`
  then `d_i ∣ N`.  No hypothesis on the presentation at all.
* `dvd_rowDenominator_of_rowFibre_eq_singleton` -- **the lower bound**: if some
  column's fibre on row `i` is a single occurrence `e`, then `m(e) ∣ d_i`.
  This is where the sharp values of (b) and (c) come from.
* `PassesAboveLeaf`, `exists_eq_leafRow_of_passesAboveLeaf`,
  `passesAboveLeaf_leafRow` -- "row `i` passes above a leaf" in the intrinsic
  form (some displayed occurrence of the row lies above a leaf-incident target
  occurrence), proved equivalent to `i = leafRow fd hLeaf`.
* **(a)** `rowDenominator_eq_one_of_passesAboveLeaf` and
  `rowDenominator_eq_one_of_leafRow`: `d_i = 1` on a leaf-passing row, with
  **no hypothesis**.
* **(b)** `rowDenominator_dvd_of_rowIndexConstant` (`d_i ∣ k`) and
  `rowDenominator_eq_of_rowIndexConstant` (`d_i = k`, given one simple column).
* **(c)** `rowDenominator_dvd_of_rowIndexTwoValued` (`d_i ∣ k(k+1)`) and
  `rowDenominator_eq_of_rowIndexTwoValued` (`d_i = k(k+1)`, given a simple
  column of index `k` and one of index `k+1`); `lcm k (k+1) = k(k+1)` is the
  coprimality of consecutive integers.
* `rowDenominator_trichotomy` -- the three cases as one disjunction, under the
  single hypothesis `RowIndicesConsecutive` (see below), together with the
  exclusivity lemmas `not_rowIndexConstant_of_two_values` and
  `not_passesAboveLeaf_of_index_ne_one`.

## What is NOT proved

* **`RowIndicesConsecutive`, the hypothesis of the trichotomy.**  It says the
  indices on the row lie in `{k, k+1}` for some `k ≥ 1`.  That is the *global*
  reading of the index pattern.  The pointwise content is in `IndexPattern`
  (`sourceEdgeIndex_eq_of_localRamification_eq_zero`,
  `sourceEdgeIndex_sub_eq_one_of_transition`,
  `not_two_transitions_on_one_row`, the last with its own separation hypothesis
  `hPairs`), and turning it into "the row is `k^μ (k+1)^{ν-μ}`" needs the
  ordered walk of a stable row (`RowWalk`); `SharpRowDenominator.rowIndicesConsecutive`
  supplies it at every full-dimensional presentation.  Case **(a)** is free of
  all of this and is proved outright; cases (b) and (c) are proved *from* the
  index pattern.
* **The sharp values `d_i = k` and `d_i = k(k+1)` without a simple column.**
  The paper's "every entry in row `i` is an integer multiple of `1/k`, so
  `d_i = k`" reads the reverse divisibility off the *geodesic* form of the row:
  a row traversing some target edge exactly once has an entry exactly `1/k`
  there.  Without the ordered walk a row could in principle traverse every
  target edge an even number of times and have a strictly smaller `d_i`, so the
  hypothesis is carried explicitly as `rowFibre … = {e}` (`SharpRowDenominator`
  constructs the simple columns).  The divisibility halves `d_i ∣ k` and
  `d_i ∣ k(k+1)` are unconditional, and they are what `Integrality` uses.
* Nothing here is conditional on integrality, on the genus, or on the degree.

## Consumers

`Integrality` uses `rowDenominator_eq_one_of_leafRow`; the multiplicity balances
at trivalent walls and at type changes use the sharp `d_1 = k_1` at a corner.
-/

namespace DraismaVargas.Count.EdgeDenominator

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.GluingDatum.LengthMatrixPresentation
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.LeafFibre
open DraismaVargas.Count.IndexPattern

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-! ## 1.  The surviving occurrences displayed on one stable row -/

/-- The surviving source occurrences displayed on the stable row `sourceRow`.
`Count.LeafFibre.rowFibre` is its part lying above one target occurrence. -/
noncomputable def rowEdges (labelling : StableLengthMatrixLabelling data coordinate)
    (sourceRow : coordinate) : Finset data.SourceEdge := by
  classical
  exact (Finset.univ : Finset data.SourceEdge).filter
    fun edge ↦ ∃ hSurvives : ¬ IsDangling data edge,
      labelling.row (NonDanglingEdge.stablePath
        (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = sourceRow

omit [Fintype coordinate] in
theorem mem_rowEdges (labelling : StableLengthMatrixLabelling data coordinate)
    (sourceRow : coordinate) (edge : data.SourceEdge) :
    edge ∈ rowEdges labelling sourceRow ↔
      ∃ hSurvives : ¬ IsDangling data edge,
        labelling.row (NonDanglingEdge.stablePath
          (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = sourceRow := by
  classical
  simp [rowEdges]

omit [Fintype coordinate] in
/-- The displayed occurrences of a row are exactly the entries of the row's
enumeration list. -/
theorem rowEdges_eq_toFinset_path
    (labelling : StableLengthMatrixLabelling data coordinate)
    (sourceRow : coordinate) :
    rowEdges labelling sourceRow = (labelling.path sourceRow).toFinset := by
  classical
  ext edge
  rw [mem_rowEdges, List.mem_toFinset, StableLengthMatrixLabelling.mem_path_iff]

omit [Fintype coordinate] in
theorem mem_rowFibre_iff (labelling : StableLengthMatrixLabelling data coordinate)
    (sourceRow : coordinate) (item : target.edges) (edge : data.SourceEdge) :
    edge ∈ rowFibre labelling sourceRow item ↔
      edge ∈ rowEdges labelling sourceRow ∧ edge.1.1 = item := by
  classical
  rw [mem_rowFibre, mem_rowEdges]

omit [Fintype coordinate] in
theorem rowFibre_subset_rowEdges
    (labelling : StableLengthMatrixLabelling data coordinate)
    (sourceRow : coordinate) (item : target.edges) :
    rowFibre labelling sourceRow item ⊆ rowEdges labelling sourceRow := fun _ hEdge ↦
  ((mem_rowFibre_iff labelling sourceRow item _).mp hEdge).1

omit [Fintype coordinate] in
/-- One entry of the honest stable length matrix, read at a *column* rather
than at a target occurrence. -/
theorem matrix_eq_sum_rowFibre
    (labelling : StableLengthMatrixLabelling data coordinate)
    (sourceRow column : coordinate) :
    matrix labelling.presentation sourceRow column =
      ∑ edge ∈ rowFibre labelling sourceRow (labelling.targetEdge column),
        (1 : ℚ) / data.sourceEdgeIndex edge := by
  have h := matrix_eq_sum_fibre labelling sourceRow (labelling.targetEdge column)
  rwa [Equiv.symm_apply_apply] at h

/-! ## 2.  The two divisibility bounds -/

/-- **The upper bound on `d_i`.**  Every entry of row `i` is a sum of
reciprocals of indices occurring on the row, so any common multiple of those
indices clears the whole row. -/
theorem rowDenominator_dvd_of_forall_index_dvd
    (labelling : StableLengthMatrixLabelling data coordinate)
    (sourceRow : coordinate) {N : ℕ}
    (hIndex : ∀ edge ∈ rowEdges labelling sourceRow, data.sourceEdgeIndex edge ∣ N) :
    rowDenominator labelling.presentation sourceRow ∣ N := by
  classical
  refine commonDenominator_dvd_of_integral _ _ ?_
  intro column _
  rw [show matrix labelling.presentation sourceRow column = _ from
    matrix_eq_sum_rowFibre labelling sourceRow column, Finset.mul_sum]
  refine integral_sum _ _ ?_
  intro edge hEdge
  obtain ⟨factor, hFactor⟩ :=
    hIndex edge (rowFibre_subset_rowEdges labelling sourceRow _ hEdge)
  refine ⟨factor, ?_⟩
  have hPos : (data.sourceEdgeIndex edge : ℚ) ≠ 0 := by
    exact_mod_cast (GluingDatum.sourceEdgeIndex_pos data edge).ne'
  rw [hFactor]
  push_cast
  field_simp

/-- **The lower bound on `d_i`.**  A column whose fibre on the row is a single
occurrence `e` has entry exactly `1/m(e)`, so `m(e)` divides the row
denominator. -/
theorem dvd_rowDenominator_of_rowFibre_eq_singleton
    (labelling : StableLengthMatrixLabelling data coordinate)
    (sourceRow column : coordinate) {edge : data.SourceEdge}
    (hFibre : rowFibre labelling sourceRow (labelling.targetEdge column) = {edge}) :
    data.sourceEdgeIndex edge ∣ rowDenominator labelling.presentation sourceRow := by
  classical
  have hInt : Integral ((rowDenominator labelling.presentation sourceRow : ℚ) *
      matrix labelling.presentation sourceRow column) :=
    integral_commonDenominator_mul _ _ (Finset.mem_univ column)
  rw [matrix_eq_sum_rowFibre, hFibre, Finset.sum_singleton] at hInt
  obtain ⟨value, hValue⟩ := hInt
  have hPos : (data.sourceEdgeIndex edge : ℚ) ≠ 0 := by
    exact_mod_cast (GluingDatum.sourceEdgeIndex_pos data edge).ne'
  have hRat : ((rowDenominator labelling.presentation sourceRow : ℕ) : ℚ) =
      (data.sourceEdgeIndex edge : ℚ) * (value : ℚ) := by
    field_simp at hValue
    linarith
  have hInt' : ((rowDenominator labelling.presentation sourceRow : ℕ) : ℤ) =
      ((data.sourceEdgeIndex edge : ℕ) : ℤ) * value := by exact_mod_cast hRat
  exact Int.natCast_dvd_natCast.mp ⟨value, hInt'⟩

/-! ## 3.  Case (a): a row passing above a leaf -/

/-- **Row `i` passes above a leaf**: one of its displayed occurrences lies
above a target occurrence incident to a leaf. -/
def PassesAboveLeaf (labelling : StableLengthMatrixLabelling data coordinate)
    (sourceRow : coordinate) : Prop :=
  ∃ edge ∈ rowEdges labelling sourceRow, ∃ vertex : target.V,
    IsLeafVertex target vertex ∧ edge.1.1 ∈ GluingDatum.incidentEdges vertex

/-- A leaf-passing row is one of `Count.LeafFibre`'s rows `h(v)`. -/
theorem exists_eq_leafRow_of_passesAboveLeaf
    (fd : FullDimensionalSourcePresentation data coordinate) {sourceRow : coordinate}
    (hPasses : PassesAboveLeaf fd.labelling sourceRow) :
    ∃ (vertex : target.V) (hLeaf : IsLeafVertex target vertex),
      sourceRow = leafRow fd hLeaf := by
  obtain ⟨edge, hEdge, vertex, hLeaf, hMem⟩ := hPasses
  obtain ⟨hSurvives, hRow⟩ := (mem_rowEdges fd.labelling sourceRow edge).mp hEdge
  have hTarget : edge.1.1 = leafEdge hLeaf := eq_leafEdge_of_mem hLeaf hMem
  refine ⟨vertex, hLeaf, ?_⟩
  rw [← hRow, row_eq_leafRow fd hLeaf ((mem_leafSurvivors hLeaf).mpr ⟨hSurvives, hTarget⟩)
    hSurvives]

/-- Conversely, `h(v)` passes above the leaf `v`. -/
theorem passesAboveLeaf_leafRow
    (fd : FullDimensionalSourcePresentation data coordinate) {vertex : target.V}
    (hLeaf : IsLeafVertex target vertex) :
    PassesAboveLeaf fd.labelling (leafRow fd hLeaf) := by
  refine ⟨leafSurvivor fd hLeaf, (mem_rowEdges _ _ _).mpr
    ⟨(leafSurvivor_spec fd hLeaf).2, rfl⟩, vertex, hLeaf, ?_⟩
  rw [(leafSurvivor_spec fd hLeaf).1]
  exact leafEdge_mem hLeaf

/-- Every occurrence displayed on a leaf-passing row is unramified. -/
theorem sourceEdgeIndex_eq_one_of_passesAboveLeaf
    (fd : FullDimensionalSourcePresentation data coordinate) {sourceRow : coordinate}
    (hPasses : PassesAboveLeaf fd.labelling sourceRow)
    {edge : data.SourceEdge} (hEdge : edge ∈ rowEdges fd.labelling sourceRow) :
    data.sourceEdgeIndex edge = 1 := by
  obtain ⟨vertex, hLeaf, hRowEq⟩ := exists_eq_leafRow_of_passesAboveLeaf fd hPasses
  obtain ⟨hSurvives, hRow⟩ := (mem_rowEdges fd.labelling sourceRow edge).mp hEdge
  exact sourceEdgeIndex_eq_one_of_row_eq_leafRow fd hLeaf hSurvives (by rw [hRow, hRowEq])

/-- **`lemma-edge-deno` (a): a leaf-passing row has `d_i = 1`.**  No
hypothesis. -/
theorem rowDenominator_eq_one_of_passesAboveLeaf
    (fd : FullDimensionalSourcePresentation data coordinate) {sourceRow : coordinate}
    (hPasses : PassesAboveLeaf fd.labelling sourceRow) :
    rowDenominator fd.labelling.presentation sourceRow = 1 :=
  Nat.dvd_one.mp (rowDenominator_dvd_of_forall_index_dvd fd.labelling sourceRow
    fun edge hEdge ↦ by
      rw [sourceEdgeIndex_eq_one_of_passesAboveLeaf fd hPasses hEdge])

/-- **`d_{h(v)} = 1`**: the row through the core vertex above a leaf has unit
denominator.  This is the form `Count.Integrality` consumes. -/
theorem rowDenominator_eq_one_of_leafRow
    (fd : FullDimensionalSourcePresentation data coordinate) {vertex : target.V}
    (hLeaf : IsLeafVertex target vertex) :
    rowDenominator fd.labelling.presentation (leafRow fd hLeaf) = 1 :=
  rowDenominator_eq_one_of_passesAboveLeaf fd (passesAboveLeaf_leafRow fd hLeaf)

/-! ## 4.  Cases (b) and (c): the index pattern of a leaf-avoiding row -/

/-- The indices displayed on row `i` are constantly `k`. -/
def RowIndexConstant (labelling : StableLengthMatrixLabelling data coordinate)
    (sourceRow : coordinate) (index : ℕ) : Prop :=
  ∀ edge ∈ rowEdges labelling sourceRow, data.sourceEdgeIndex edge = index

/-- The indices displayed on row `i` lie in `{k, k+1}`. -/
def RowIndexTwoValued (labelling : StableLengthMatrixLabelling data coordinate)
    (sourceRow : coordinate) (index : ℕ) : Prop :=
  ∀ edge ∈ rowEdges labelling sourceRow,
    data.sourceEdgeIndex edge = index ∨ data.sourceEdgeIndex edge = index + 1

/-- **The hypothesis the trichotomy needs, which the pointwise index pattern does
not supply by itself**: the indices along row `i` take at most two values, and
consecutive ones.  See the module docstring. -/
def RowIndicesConsecutive (labelling : StableLengthMatrixLabelling data coordinate)
    (sourceRow : coordinate) : Prop :=
  ∃ index : ℕ, 0 < index ∧ RowIndexTwoValued labelling sourceRow index

omit [Fintype coordinate] in
theorem RowIndexConstant.rowIndexTwoValued
    {labelling : StableLengthMatrixLabelling data coordinate}
    {sourceRow : coordinate} {index : ℕ}
    (hConstant : RowIndexConstant labelling sourceRow index) :
    RowIndexTwoValued labelling sourceRow index :=
  fun edge hEdge ↦ Or.inl (hConstant edge hEdge)

/-- A leaf-passing row satisfies the hypothesis outright, with `k = 1`. -/
theorem rowIndicesConsecutive_of_passesAboveLeaf
    (fd : FullDimensionalSourcePresentation data coordinate) {sourceRow : coordinate}
    (hPasses : PassesAboveLeaf fd.labelling sourceRow) :
    RowIndicesConsecutive fd.labelling sourceRow :=
  ⟨1, Nat.one_pos, fun _ hEdge ↦
    Or.inl (sourceEdgeIndex_eq_one_of_passesAboveLeaf fd hPasses hEdge)⟩

/-- **`lemma-edge-deno` (b), divisibility half**: a row of constant index `k`
has `d_i ∣ k`. -/
theorem rowDenominator_dvd_of_rowIndexConstant
    (labelling : StableLengthMatrixLabelling data coordinate)
    (sourceRow : coordinate) {index : ℕ}
    (hConstant : RowIndexConstant labelling sourceRow index) :
    rowDenominator labelling.presentation sourceRow ∣ index :=
  rowDenominator_dvd_of_forall_index_dvd labelling sourceRow fun edge hEdge ↦ by
    rw [hConstant edge hEdge]

/-- **`lemma-edge-deno` (b)**: `d_i = k` as soon as some column of the row
carries a single occurrence, which then necessarily has index `k`. -/
theorem rowDenominator_eq_of_rowIndexConstant
    (labelling : StableLengthMatrixLabelling data coordinate)
    (sourceRow column : coordinate) {index : ℕ} {edge : data.SourceEdge}
    (hConstant : RowIndexConstant labelling sourceRow index)
    (hFibre : rowFibre labelling sourceRow (labelling.targetEdge column) = {edge}) :
    rowDenominator labelling.presentation sourceRow = index := by
  refine Nat.dvd_antisymm (rowDenominator_dvd_of_rowIndexConstant labelling sourceRow
    hConstant) ?_
  have hMem : edge ∈ rowEdges labelling sourceRow :=
    rowFibre_subset_rowEdges labelling sourceRow _
      (by rw [hFibre]; exact Finset.mem_singleton_self _)
  rw [← hConstant edge hMem]
  exact dvd_rowDenominator_of_rowFibre_eq_singleton labelling sourceRow column hFibre

/-- Consecutive integers are coprime, so their lcm is their product. -/
theorem coprime_succ (index : ℕ) : Nat.Coprime index (index + 1) := by
  simp

/-- **`lemma-edge-deno` (c), divisibility half**: a row whose indices lie in
`{k, k+1}` has `d_i ∣ k(k+1)`. -/
theorem rowDenominator_dvd_of_rowIndexTwoValued
    (labelling : StableLengthMatrixLabelling data coordinate)
    (sourceRow : coordinate) {index : ℕ}
    (hTwoValued : RowIndexTwoValued labelling sourceRow index) :
    rowDenominator labelling.presentation sourceRow ∣ index * (index + 1) :=
  rowDenominator_dvd_of_forall_index_dvd labelling sourceRow fun edge hEdge ↦ by
    rcases hTwoValued edge hEdge with hCase | hCase
    · rw [hCase]
      exact dvd_mul_right index (index + 1)
    · rw [hCase]
      exact dvd_mul_left (index + 1) index

/-- **`lemma-edge-deno` (c)**: `d_i = k(k+1)` as soon as the row has a simple
column of index `k` and a simple column of index `k+1`. -/
theorem rowDenominator_eq_of_rowIndexTwoValued
    (labelling : StableLengthMatrixLabelling data coordinate)
    (sourceRow columnLow columnHigh : coordinate) {index : ℕ}
    {edgeLow edgeHigh : data.SourceEdge}
    (hTwoValued : RowIndexTwoValued labelling sourceRow index)
    (hLow : rowFibre labelling sourceRow (labelling.targetEdge columnLow) = {edgeLow})
    (hLowIndex : data.sourceEdgeIndex edgeLow = index)
    (hHigh : rowFibre labelling sourceRow (labelling.targetEdge columnHigh) = {edgeHigh})
    (hHighIndex : data.sourceEdgeIndex edgeHigh = index + 1) :
    rowDenominator labelling.presentation sourceRow = index * (index + 1) := by
  refine Nat.dvd_antisymm (rowDenominator_dvd_of_rowIndexTwoValued labelling sourceRow
    hTwoValued) ?_
  refine (coprime_succ index).mul_dvd_of_dvd_of_dvd ?_ ?_
  · rw [← hLowIndex]
    exact dvd_rowDenominator_of_rowFibre_eq_singleton labelling sourceRow columnLow hLow
  · rw [← hHighIndex]
    exact dvd_rowDenominator_of_rowFibre_eq_singleton labelling sourceRow columnHigh hHigh

/-! ## 5.  The trichotomy -/

omit [Fintype coordinate] in
/-- Cases (b) and (c) are exclusive: a row on which two distinct indices occur
is not of constant index. -/
theorem not_rowIndexConstant_of_two_values
    {labelling : StableLengthMatrixLabelling data coordinate}
    {sourceRow : coordinate} {index candidate : ℕ}
    (hLow : ∃ edge ∈ rowEdges labelling sourceRow, data.sourceEdgeIndex edge = index)
    (hHigh : ∃ edge ∈ rowEdges labelling sourceRow,
      data.sourceEdgeIndex edge = index + 1) :
    ¬ RowIndexConstant labelling sourceRow candidate := by
  rintro hConstant
  obtain ⟨edgeLow, hLowMem, hLowIndex⟩ := hLow
  obtain ⟨edgeHigh, hHighMem, hHighIndex⟩ := hHigh
  have h1 : candidate = index := (hConstant edgeLow hLowMem).symm.trans hLowIndex
  have h2 : candidate = index + 1 := (hConstant edgeHigh hHighMem).symm.trans hHighIndex
  omega

/-- Case (a) is exclusive of (b) and (c) at any index `≥ 2`: a leaf-passing row
has every index one. -/
theorem not_passesAboveLeaf_of_index_ne_one
    (fd : FullDimensionalSourcePresentation data coordinate) {sourceRow : coordinate}
    {edge : data.SourceEdge} (hEdge : edge ∈ rowEdges fd.labelling sourceRow)
    (hIndex : data.sourceEdgeIndex edge ≠ 1) :
    ¬ PassesAboveLeaf fd.labelling sourceRow :=
  fun hPasses ↦ hIndex (sourceEdgeIndex_eq_one_of_passesAboveLeaf fd hPasses hEdge)

/-- **`lemma-edge-deno`: the row-denominator trichotomy.**  Under the single
hypothesis `RowIndicesConsecutive` -- the indices on the row take at most two,
consecutive, values -- every row of a full-dimensional presentation falls into
exactly one of the paper's three cases, with the stated denominator.  Case (a)
is exact and unconditional; in cases (b) and (c) the divisibility is
unconditional and the sharp value needs a simple column
(`rowDenominator_eq_of_rowIndexConstant`,
`rowDenominator_eq_of_rowIndexTwoValued`). -/
theorem rowDenominator_trichotomy
    (fd : FullDimensionalSourcePresentation data coordinate) (sourceRow : coordinate)
    (hPattern : RowIndicesConsecutive fd.labelling sourceRow) :
    (PassesAboveLeaf fd.labelling sourceRow ∧
        rowDenominator fd.labelling.presentation sourceRow = 1) ∨
      (¬ PassesAboveLeaf fd.labelling sourceRow ∧ ∃ index : ℕ, 0 < index ∧
        RowIndexConstant fd.labelling sourceRow index ∧
        rowDenominator fd.labelling.presentation sourceRow ∣ index) ∨
      (¬ PassesAboveLeaf fd.labelling sourceRow ∧ ∃ index : ℕ, 0 < index ∧
        RowIndexTwoValued fd.labelling sourceRow index ∧
        (∃ edge ∈ rowEdges fd.labelling sourceRow,
          data.sourceEdgeIndex edge = index) ∧
        (∃ edge ∈ rowEdges fd.labelling sourceRow,
          data.sourceEdgeIndex edge = index + 1) ∧
        rowDenominator fd.labelling.presentation sourceRow ∣ index * (index + 1)) := by
  classical
  by_cases hPasses : PassesAboveLeaf fd.labelling sourceRow
  · exact Or.inl ⟨hPasses, rowDenominator_eq_one_of_passesAboveLeaf fd hPasses⟩
  obtain ⟨index, hIndexPos, hTwoValued⟩ := hPattern
  by_cases hHigh : ∃ edge ∈ rowEdges fd.labelling sourceRow,
      data.sourceEdgeIndex edge = index + 1
  · by_cases hLow : ∃ edge ∈ rowEdges fd.labelling sourceRow,
        data.sourceEdgeIndex edge = index
    · exact Or.inr (Or.inr ⟨hPasses, index, hIndexPos, hTwoValued, hLow, hHigh,
        rowDenominator_dvd_of_rowIndexTwoValued fd.labelling sourceRow hTwoValued⟩)
    · have hConstant : RowIndexConstant fd.labelling sourceRow (index + 1) := by
        intro edge hEdge
        rcases hTwoValued edge hEdge with hCase | hCase
        · exact absurd ⟨edge, hEdge, hCase⟩ hLow
        · exact hCase
      exact Or.inr (Or.inl ⟨hPasses, index + 1, Nat.succ_pos index, hConstant,
        rowDenominator_dvd_of_rowIndexConstant fd.labelling sourceRow hConstant⟩)
  · have hConstant : RowIndexConstant fd.labelling sourceRow index := by
      intro edge hEdge
      rcases hTwoValued edge hEdge with hCase | hCase
      · exact hCase
      · exact absurd ⟨edge, hEdge, hCase⟩ hHigh
    exact Or.inr (Or.inl ⟨hPasses, index, hIndexPos, hConstant,
      rowDenominator_dvd_of_rowIndexConstant fd.labelling sourceRow hConstant⟩)

/-! ## 6.  Non-vacuity: the caterpillar of loops

`Count.Caterpillar.matrix_diag_cat` computes the whole diagonal of
`A_φ` for the caterpillar of loops, and `den_matrix_diag_cat` reads its
denominators: `2` on a pair edge, `1` elsewhere.  Every case of the trichotomy
is inhabited there, and the values agree. -/

section Witness

open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CaterpillarDatum
open DraismaVargas.LocalCases.CaterpillarPruning
open DraismaVargas.Count.Caterpillar

/-- The main occurrence of a caterpillar row is displayed on that row. -/
theorem main_mem_rowEdges (m : ℕ) (i : Fin (6 * m + 3)) :
    (caterpillarDatum m).sourceEdge (occ m i) 0 ∈
      rowEdges (CaterpillarRows.labelling m) i := by
  rw [rowEdges_eq_toFinset_path, List.mem_toFinset]
  exact (mem_path_iff_cat m i _).mpr ⟨CaterpillarRows.main_survives m i, rfl⟩

/-- **Case (a) is inhabited**: above a leaf edge of `T^CL_g` the row passes
above the lollipop tip. -/
theorem passesAboveLeaf_cat (m : ℕ) {i : Fin (6 * m + 3)} (hLeaf : IsLeafEdge m i) :
    PassesAboveLeaf (CaterpillarRows.labelling m) i := by
  refine ⟨(caterpillarDatum m).sourceEdge (occ m i) 0, main_mem_rowEdges m i,
    i.succ, ?_, (GluingContraction.mem_incidentEdges_iff _ _).mpr (Or.inr rfl)⟩
  refine (isLeafVertex_catTree_iff m i.succ).mpr ?_
  have hlt := i.isLt
  have hval : (i.succ : Fin (6 * m + 4)).val = i.val + 1 := rfl
  rcases hLeaf with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- **`d_i = 1` on every leaf-edge row of the caterpillar**, by case (a). -/
theorem rowDenominator_cat_leafEdge (m : ℕ) {i : Fin (6 * m + 3)}
    (hLeaf : IsLeafEdge m i) :
    rowDenominator (CaterpillarRows.labelling m).presentation i = 1 :=
  rowDenominator_eq_one_of_passesAboveLeaf (CaterpillarRows.fullDim m)
    (passesAboveLeaf_cat m hLeaf)

/-- Off the leaf edges the caterpillar row displays a single occurrence. -/
theorem rowEdges_cat_notLeafEdge (m : ℕ) {i : Fin (6 * m + 3)}
    (hNotLeaf : ¬ IsLeafEdge m i) :
    rowEdges (CaterpillarRows.labelling m) i =
      {(caterpillarDatum m).sourceEdge (occ m i) 0} := by
  rw [rowEdges_eq_toFinset_path]
  exact toFinset_path_notLeaf m hNotLeaf

theorem rowFibre_cat_notLeafEdge (m : ℕ) {i : Fin (6 * m + 3)}
    (hNotLeaf : ¬ IsLeafEdge m i) :
    rowFibre (CaterpillarRows.labelling m) i
        ((CaterpillarRows.labelling m).targetEdge i) =
      {(caterpillarDatum m).sourceEdge (occ m i) 0} := by
  classical
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
  · refine (mem_rowFibre_iff _ _ _ _).mpr ⟨main_mem_rowEdges m i, rfl⟩
  · intro edge hEdge
    have hMem := ((mem_rowFibre_iff _ _ _ _).mp hEdge).1
    rw [rowEdges_cat_notLeafEdge m hNotLeaf, Finset.mem_singleton] at hMem
    exact hMem

/-- **Case (b) is inhabited with `k = 2`**: a pair edge of `T^CL_g` -- a stem or
a slope-two spine edge -- carries a row of constant index `2`, whose denominator
is `2`.  This agrees with `Count.Caterpillar.den_matrix_diag_cat`. -/
theorem rowDenominator_cat_pairEdge (m : ℕ) {i : Fin (6 * m + 3)}
    (hPair : IsPairEdge m i.val) :
    rowDenominator (CaterpillarRows.labelling m).presentation i = 2 := by
  have hNotLeaf : ¬ IsLeafEdge m i := fun hLeaf ↦ not_pair_of_leaf hLeaf hPair
  have hConstant : RowIndexConstant (CaterpillarRows.labelling m) i 2 := by
    intro edge hEdge
    rw [rowEdges_cat_notLeafEdge m hNotLeaf, Finset.mem_singleton] at hEdge
    rw [hEdge, CaterpillarStable.sourceEdgeIndex_caterpillar,
      ite_eq_left ⟨hPair, Or.inl rfl⟩]
  exact rowDenominator_eq_of_rowIndexConstant _ i i hConstant
    (rowFibre_cat_notLeafEdge m hNotLeaf)

/-- **Case (b) is inhabited with `k = 1`** as well: a slope-one spine edge. -/
theorem rowDenominator_cat_spineEdge (m : ℕ) {i : Fin (6 * m + 3)}
    (hNotLeaf : ¬ IsLeafEdge m i) (hNotPair : ¬ IsPairEdge m i.val) :
    rowDenominator (CaterpillarRows.labelling m).presentation i = 1 := by
  have hConstant : RowIndexConstant (CaterpillarRows.labelling m) i 1 := by
    intro edge hEdge
    rw [rowEdges_cat_notLeafEdge m hNotLeaf, Finset.mem_singleton] at hEdge
    rw [hEdge, CaterpillarStable.sourceEdgeIndex_caterpillar,
      ite_eq_right (fun hCase ↦ hNotPair hCase.1)]
  exact rowDenominator_eq_of_rowIndexConstant _ i i hConstant
    (rowFibre_cat_notLeafEdge m hNotLeaf)

/-- **The hypothesis of the trichotomy is inhabited**: every row of the
caterpillar of loops has consecutive indices (indeed constant ones). -/
theorem rowIndicesConsecutive_cat (m : ℕ) (i : Fin (6 * m + 3)) :
    RowIndicesConsecutive (CaterpillarRows.labelling m) i := by
  by_cases hLeaf : IsLeafEdge m i
  · exact rowIndicesConsecutive_of_passesAboveLeaf (CaterpillarRows.fullDim m)
      (passesAboveLeaf_cat m hLeaf)
  refine ⟨1, Nat.one_pos, ?_⟩
  intro edge hEdge
  rw [rowEdges_cat_notLeafEdge m hLeaf, Finset.mem_singleton] at hEdge
  rw [hEdge, CaterpillarStable.sourceEdgeIndex_caterpillar]
  by_cases hPair : IsPairEdge m i.val
  · exact Or.inr (by rw [ite_eq_left ⟨hPair, Or.inl rfl⟩])
  · exact Or.inl (by rw [ite_eq_right (fun hCase ↦ hPair hCase.1)])

/-- **The trichotomy, inhabited**: every row of the caterpillar of loops meets
one of the three cases. -/
example (m : ℕ) (i : Fin (6 * m + 3)) :
    (PassesAboveLeaf (CaterpillarRows.labelling m) i ∧
        rowDenominator (CaterpillarRows.labelling m).presentation i = 1) ∨
      (¬ PassesAboveLeaf (CaterpillarRows.labelling m) i ∧ ∃ index : ℕ, 0 < index ∧
        RowIndexConstant (CaterpillarRows.labelling m) i index ∧
        rowDenominator (CaterpillarRows.labelling m).presentation i ∣ index) ∨
      (¬ PassesAboveLeaf (CaterpillarRows.labelling m) i ∧ ∃ index : ℕ, 0 < index ∧
        RowIndexTwoValued (CaterpillarRows.labelling m) i index ∧
        (∃ edge ∈ rowEdges (CaterpillarRows.labelling m) i,
          (caterpillarDatum m).sourceEdgeIndex edge = index) ∧
        (∃ edge ∈ rowEdges (CaterpillarRows.labelling m) i,
          (caterpillarDatum m).sourceEdgeIndex edge = index + 1) ∧
        rowDenominator (CaterpillarRows.labelling m).presentation i ∣
          index * (index + 1)) :=
  rowDenominator_trichotomy (CaterpillarRows.fullDim m) i (rowIndicesConsecutive_cat m i)

/-- `g = 6`: the first stem of `T^CL_6` is a pair edge, so its row denominator
is `2`. -/
example : rowDenominator (CaterpillarRows.labelling 2).presentation
    ⟨1, by omega⟩ = 2 :=
  rowDenominator_cat_pairEdge 2 (Or.inl rfl)

/-- `g = 6`: the first lollipop loop of `T^CL_6` is a leaf edge, so its row
denominator is `1`. -/
example : rowDenominator (CaterpillarRows.labelling 2).presentation
    ⟨0, by omega⟩ = 1 :=
  rowDenominator_cat_leafEdge 2 (Or.inl rfl)

end Witness

end DraismaVargas.Count.EdgeDenominator
