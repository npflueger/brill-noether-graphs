import DraismaVargas.LocalCases.CaterpillarRows
import Utilities.IntegralGeometry.Denominator

/-!
# Part II's determinantal multiplicity, and its API

**Source.**  Vargas, Part II (arXiv:2609.09109), the definition of the multiplicity
(`def-multiplicity`): for a full-dimensional degree-`d` morphism `φ` with edge-length matrix
`A_φ` (rows the displayed stable paths, columns the target edge occurrences), `d_i` the
least common denominator of row `i`, `D_φ = ∏ᵢ dᵢ` and `l(T)` the number of leaves of the
target tree,

    Mult φ = (D_φ / 2^{l(T)}) · det A_φ,        absMult φ = |Mult φ|.

The cleared matrix `B'` and the leaf-column convention below make integrality visible
(`Count.Integrality`).  The caterpillar computation of §6 is the step of Part II's proof of
the main theorem (`thm`) that computes the multiplicity of a caterpillar member.

## What is proved

* `leafCount` -- the number of leaves of the target, defined through the
  library's leaf idiom `(GluingDatum.incidentEdges v).card = 1`.
* `rowDenominator` (`= commonDenominator` of a row, so literally the paper's
  `d_i`), `denominatorProduct`, `signedMult`, `absMult`, all over an arbitrary
  `GluingDatum.LengthMatrixPresentation`; no full-dimensionality hypothesis is
  required to *state* them.
* `clearedMatrix` -- `B' = diag(dᵢ) · A_φ · diag(½ on leaf columns, 1
  elsewhere)` -- and `det_clearedMatrix`, its determinant, **unconditionally**:
  `det B' = D_φ · det A_φ · (1/2)^{#leaf columns}`.  Nothing about
  integrality of `B'` enters, and nothing about the target beyond counting its
  leaf columns.
* `absMult_eq_abs_det_clearedMatrix` -- the workhorse identity
  `absMult φ = |det B'|`, whose only input is that the leaf columns are in
  bijection with the leaves.  `leafColumns_card_eq_leafCount` supplies that
  from the purely combinatorial `NoLeafToLeafEdge` (no target edge joins two
  leaves), which `Caterpillar.noLeafToLeafEdge_catTree` discharges for the
  caterpillar target, giving `abs_det_clearedMatrix_caterpillar` with no
  hypothesis at all.
* Invariance: `signedMult_reindex` (relabelling rows *and* columns along one
  equivalence of the coordinate type leaves `Mult` unchanged, no hypothesis --
  the leaf columns are permuted among themselves because the target dictionary
  is composed with the same equivalence) and `signedMult_reindexRows`
  (permuting only the displayed rows multiplies `Mult` by the sign of the
  permutation), hence `absMult_reindex` and `absMult_reindexRows`.
* `signedMult_of_diagonalPattern` -- for a `SeedDeterminant.DiagonalPattern`,
  `Mult φ = (∏ᵢ num(A_φ(i,i))) / 2^{l(T)}`.
* `fdSignedMult`, `fdAbsMult`, `fdClearedMatrix`, `fdDenominatorProduct` --
  the same objects read off a `FullDimensionalSourcePresentation`, with
  `fdSignedMult_ne_zero`.
* The caterpillar of loops, uniformly in `g = 2m + 2`
  (`Caterpillar` section): `matrix_diag_cat` computes every diagonal entry of
  `A_φ` (`2` on a leaf edge, `1/2` on a pair edge, `1` on a slope-one spine
  edge), `leafCount_catTree` gives `l(T) = 2m + 2`, and
  `absMult_caterpillar` gives **`absMult = 1`**, which is the normalisation
  the whole Part II count rests on.

## Comparison with Part II

This differs from the corresponding step of Part II's proof of the main theorem as
follows.  That step computes the multiplicity of a caterpillar member from the two
intermediate values `det A_φ = 1` and `D_φ = 2^{l(T)}`.  In the encoding of `T^CL_g` used
here those two values are `denominatorProduct_caterpillar : D_φ = 2^{3m+1}` and
`det_caterpillar : det A_φ = 2^{2m+2} / 2^{3m+1}`, which coincide with Part II's only at
`m = 1` (`g = 4`).  Their *product* is what the count needs, and it is `1` for every `m`;
the definition of the multiplicity is the one of Part II.

## What is not proved here

* **Integrality of `Mult`** (and of `B'`) is stated here as the named `Prop`
  `IsIntegralMultiplicity`, with no theorem in this file using it; the only inhabitant
  supplied here is the caterpillar (`isIntegralMultiplicity_caterpillar`).  It is proved in
  `Count/Integrality.lean` (`Count.isIntegralMultiplicity`), with no hypothesis beyond a
  `FullDimensionalSourcePresentation`, from `Count.LeafFibre.matrix_leafEdge_column` and
  `Count.EdgeDenominator.rowDenominator_eq_one_of_leafRow`.
* Part II's `lemma-edge-deno`, the case analysis of the `d_i`; it is
  `Count.EdgeDenominator` and `Count.SharpRowDenominator`.
* The toric interpretation `lemma-toric-multiplicity`, and any wall-crossing
  balancing identity.
* `absMult_eq_abs_det_clearedMatrix` carries the hypothesis
  `(leafColumns p).card = leafCount target`; the hypothesis-free version needs
  `NoLeafToLeafEdge target`.  It is derived, unconditionally on a
  `FullDimensionalSourcePresentation`, by `Count.noLeafToLeafEdge_of_fullDimensional`
  (not from connectivity alone).

## Consumers

`DraismaVargasCount.Integrality` (integrality, `absMultNat`, oddness) proves
`IsIntegralMultiplicity`; `DraismaVargasCount.TransportMultiplicity` proves the invariance
of `absMult` under isomorphism of gluing data; `DraismaVargasCount.BallotMultiplicity`
extends §6 from the zig-zag sequence to every ballot sequence; the balancing identities at
walls consume `signedMult`.
-/

namespace DraismaVargas.Count

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.GluingDatum.LengthMatrixPresentation

variable {target : CFGraph}

/-! ## 1.  Leaves of the target -/

/-- A target vertex is a leaf when exactly one edge occurrence meets it. -/
def IsLeafVertex (target : CFGraph) (vertex : target.V) : Prop :=
  (GluingDatum.incidentEdges vertex).card = 1

instance (target : CFGraph) (vertex : target.V) :
    Decidable (IsLeafVertex target vertex) := by
  unfold IsLeafVertex; infer_instance

/-- The leaves of the target. -/
def leafVertices (target : CFGraph) : Finset target.V :=
  Finset.univ.filter fun vertex ↦ IsLeafVertex target vertex

@[simp] theorem mem_leafVertices (vertex : target.V) :
    vertex ∈ leafVertices target ↔ IsLeafVertex target vertex := by
  simp [leafVertices]

/-- `l(T)`, the number of leaves of the target tree. -/
def leafCount (target : CFGraph) : ℕ := (leafVertices target).card

/-- No edge occurrence of the target joins two leaves. -/
def NoLeafToLeafEdge (target : CFGraph) : Prop :=
  ∀ edge : target.edges, IsLeafVertex target (edge : target.V × target.V).1 →
    ¬ IsLeafVertex target (edge : target.V × target.V).2

/-! ## 2.  Row denominators, the multiplicity, the cleared matrix -/

variable {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- `d_i`: the least common denominator of row `i` of the edge-length matrix. -/
noncomputable def rowDenominator
    (presentation : data.LengthMatrixPresentation coordinate)
    (sourceRow : coordinate) : ℕ :=
  commonDenominator Finset.univ (matrix presentation sourceRow)

/-- `D_φ = ∏ᵢ dᵢ`. -/
noncomputable def denominatorProduct
    (presentation : data.LengthMatrixPresentation coordinate) : ℕ :=
  ∏ sourceRow, rowDenominator presentation sourceRow

theorem rowDenominator_pos
    (presentation : data.LengthMatrixPresentation coordinate)
    (sourceRow : coordinate) : 0 < rowDenominator presentation sourceRow :=
  commonDenominator_pos _ _

theorem denominatorProduct_pos
    (presentation : data.LengthMatrixPresentation coordinate) :
    0 < denominatorProduct presentation :=
  Finset.prod_pos fun sourceRow _ ↦ rowDenominator_pos presentation sourceRow

/-- The columns of the presentation carrying a target edge incident to a
leaf. -/
noncomputable def leafColumns
    (presentation : data.LengthMatrixPresentation coordinate) :
    Finset coordinate := by
  classical
  exact Finset.univ.filter fun column ↦ ∃ vertex : target.V,
    IsLeafVertex target vertex ∧
      presentation.targetEdge column ∈ GluingDatum.incidentEdges vertex

omit [DecidableEq coordinate] in
theorem mem_leafColumns
    (presentation : data.LengthMatrixPresentation coordinate)
    (column : coordinate) :
    column ∈ leafColumns presentation ↔ ∃ vertex : target.V,
      IsLeafVertex target vertex ∧
        presentation.targetEdge column ∈ GluingDatum.incidentEdges vertex := by
  classical
  simp [leafColumns]

/-- The signed multiplicity `Mult φ = (D_φ / 2^{l(T)}) · det A_φ`. -/
noncomputable def signedMult
    (presentation : data.LengthMatrixPresentation coordinate) : ℚ :=
  (denominatorProduct presentation : ℚ) / 2 ^ leafCount target *
    (matrix presentation).det

/-- The multiplicity `absMult φ = |Mult φ|`. -/
noncomputable def absMult
    (presentation : data.LengthMatrixPresentation coordinate) : ℚ :=
  |signedMult presentation|

/-- `½` on the leaf columns, `1` elsewhere. -/
noncomputable def columnScale
    (presentation : data.LengthMatrixPresentation coordinate)
    (column : coordinate) : ℚ :=
  if column ∈ leafColumns presentation then 1 / 2 else 1

/-- `B' = diag(dᵢ) · A_φ · diag(½ on leaf columns, 1 elsewhere)`. -/
noncomputable def clearedMatrix
    (presentation : data.LengthMatrixPresentation coordinate) :
    Matrix coordinate coordinate ℚ :=
  Matrix.diagonal (fun sourceRow ↦ (rowDenominator presentation sourceRow : ℚ)) *
      matrix presentation * Matrix.diagonal (columnScale presentation)

@[simp] theorem clearedMatrix_apply
    (presentation : data.LengthMatrixPresentation coordinate)
    (sourceRow column : coordinate) :
    clearedMatrix presentation sourceRow column =
      (rowDenominator presentation sourceRow : ℚ) *
        matrix presentation sourceRow column * columnScale presentation column := by
  simp [clearedMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem prod_columnScale
    (presentation : data.LengthMatrixPresentation coordinate) :
    ∏ column, columnScale presentation column =
      (1 / 2 : ℚ) ^ (leafColumns presentation).card := by
  rw [show (fun column ↦ columnScale presentation column) =
      fun column ↦ if column ∈ leafColumns presentation then (1 / 2 : ℚ) else 1 from rfl,
    Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-- **The determinant of the cleared matrix**, unconditionally: no integrality
of `B'` and no property of the target beyond the leaf-column count enters. -/
theorem det_clearedMatrix
    (presentation : data.LengthMatrixPresentation coordinate) :
    (clearedMatrix presentation).det =
      (denominatorProduct presentation : ℚ) * (matrix presentation).det *
        (1 / 2 : ℚ) ^ (leafColumns presentation).card := by
  rw [clearedMatrix, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_diagonal, prod_columnScale, denominatorProduct, Nat.cast_prod]

/-! ## 3.  The workhorse identity -/

section LeafEdge

variable {vertex : target.V}

/-- The unique edge occurrence at a leaf. -/
noncomputable def leafEdge (hLeaf : IsLeafVertex target vertex) : target.edges :=
  (Finset.card_eq_one.mp hLeaf).choose

theorem incidentEdges_eq_leafEdge (hLeaf : IsLeafVertex target vertex) :
    GluingDatum.incidentEdges vertex = {leafEdge hLeaf} :=
  (Finset.card_eq_one.mp hLeaf).choose_spec

theorem leafEdge_mem (hLeaf : IsLeafVertex target vertex) :
    leafEdge hLeaf ∈ GluingDatum.incidentEdges vertex :=
  (incidentEdges_eq_leafEdge hLeaf).ge (Finset.mem_singleton_self _)

theorem eq_leafEdge_of_mem (hLeaf : IsLeafVertex target vertex)
    {edge : target.edges} (hEdge : edge ∈ GluingDatum.incidentEdges vertex) :
    edge = leafEdge hLeaf := by
  rw [incidentEdges_eq_leafEdge hLeaf, Finset.mem_singleton] at hEdge
  exact hEdge

theorem fst_eq_or_snd_eq_of_mem_incidentEdges {edge : target.edges}
    (hEdge : edge ∈ GluingDatum.incidentEdges vertex) :
    (edge : target.V × target.V).1 = vertex ∨
      (edge : target.V × target.V).2 = vertex := by
  rw [GluingDatum.incidentEdges, Finset.mem_filter] at hEdge
  exact hEdge.2

end LeafEdge

omit [DecidableEq coordinate] in
theorem leafColumns_card_eq_leafCount
    (presentation : data.LengthMatrixPresentation coordinate)
    (hTarget : NoLeafToLeafEdge target) :
    (leafColumns presentation).card = leafCount target := by
  classical
  symm
  refine Finset.card_bij
    (fun vertex hv ↦ presentation.targetEdge.symm
      (leafEdge ((mem_leafVertices vertex).mp hv))) ?_ ?_ ?_
  · intro vertex hv
    refine (mem_leafColumns presentation _).mpr
      ⟨vertex, (mem_leafVertices vertex).mp hv, ?_⟩
    rw [Equiv.apply_symm_apply]
    exact leafEdge_mem _
  · intro first hfirst second hsecond hEq
    have hLeafFirst : IsLeafVertex target first := (mem_leafVertices first).mp hfirst
    have hLeafSecond : IsLeafVertex target second := (mem_leafVertices second).mp hsecond
    have hEdge : leafEdge hLeafFirst = leafEdge hLeafSecond :=
      presentation.targetEdge.symm.injective hEq
    by_contra hne
    have h1 := fst_eq_or_snd_eq_of_mem_incidentEdges (leafEdge_mem hLeafFirst)
    have h2 := fst_eq_or_snd_eq_of_mem_incidentEdges (leafEdge_mem hLeafSecond)
    rw [← hEdge] at h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact hne (h1.symm.trans h2)
    · exact hTarget _ (by rw [h1]; exact hLeafFirst) (by rw [h2]; exact hLeafSecond)
    · exact hTarget _ (by rw [h2]; exact hLeafSecond) (by rw [h1]; exact hLeafFirst)
    · exact hne (h1.symm.trans h2)
  · intro column hcolumn
    obtain ⟨vertex, hLeaf, hMem⟩ := (mem_leafColumns presentation column).mp hcolumn
    refine ⟨vertex, (mem_leafVertices vertex).mpr hLeaf, ?_⟩
    have hEq : presentation.targetEdge column = leafEdge hLeaf :=
      eq_leafEdge_of_mem hLeaf hMem
    rw [show leafEdge ((mem_leafVertices vertex).mp
      ((mem_leafVertices vertex).mpr hLeaf)) = leafEdge hLeaf from rfl, ← hEq,
      Equiv.symm_apply_apply]

/-- **`absMult φ = |det B'|`.**  The only input is that the leaf columns are
in bijection with the leaves; integrality of `B'` is never used. -/
theorem absMult_eq_abs_det_clearedMatrix
    (presentation : data.LengthMatrixPresentation coordinate)
    (hLeaf : (leafColumns presentation).card = leafCount target) :
    absMult presentation = |(clearedMatrix presentation).det| := by
  rw [det_clearedMatrix, hLeaf, absMult, signedMult]
  congr 1
  rw [one_div, inv_pow, div_eq_mul_inv]
  ring

theorem absMult_eq_abs_det_clearedMatrix_of_noLeafToLeafEdge
    (presentation : data.LengthMatrixPresentation coordinate)
    (hTarget : NoLeafToLeafEdge target) :
    absMult presentation = |(clearedMatrix presentation).det| :=
  absMult_eq_abs_det_clearedMatrix presentation
    (leafColumns_card_eq_leafCount presentation hTarget)

/-- Part II's assertion that the signed multiplicity is an integer.  **Owed**;
nothing in this module uses it. -/
def IsIntegralMultiplicity
    (presentation : data.LengthMatrixPresentation coordinate) : Prop :=
  Integral (signedMult presentation)

/-! ## 4.  Invariance under relabelling -/

/-- Relabelling both the rows and the columns of a presentation along an
equivalence of the coordinate type. -/
def reindex (presentation : data.LengthMatrixPresentation coordinate)
    {coordinate' : Type*} (relabel : coordinate' ≃ coordinate) :
    data.LengthMatrixPresentation coordinate' where
  targetEdge := relabel.trans presentation.targetEdge
  path := fun sourceRow ↦ presentation.path (relabel sourceRow)

/-- Relabelling only the rows: the displayed stable path of a coordinate is
the one the permutation names, with the target dictionary untouched. -/
def reindexRows (presentation : data.LengthMatrixPresentation coordinate)
    (relabel : Equiv.Perm coordinate) :
    data.LengthMatrixPresentation coordinate where
  targetEdge := presentation.targetEdge
  path := fun sourceRow ↦ presentation.path (relabel sourceRow)

variable {coordinate' : Type*} [Fintype coordinate'] [DecidableEq coordinate']

omit [Fintype coordinate] [Fintype coordinate'] in
theorem coefficient_reindex (presentation : data.LengthMatrixPresentation coordinate)
    (relabel : coordinate' ≃ coordinate) (edge : data.SourceEdge)
    (column : coordinate') :
    coefficient (reindex presentation relabel) edge column =
      coefficient presentation edge (relabel column) := by
  classical
  unfold coefficient reindex
  congr 1
  simp [Equiv.eq_symm_apply]

omit [Fintype coordinate] [Fintype coordinate'] in
theorem row_reindex (presentation : data.LengthMatrixPresentation coordinate)
    (relabel : coordinate' ≃ coordinate) (path : List data.SourceEdge)
    (column : coordinate') :
    row (reindex presentation relabel) path column =
      row presentation path (relabel column) := by
  unfold row
  congr 1
  exact List.map_congr_left fun edge _ ↦
    coefficient_reindex presentation relabel edge column

omit [Fintype coordinate] [Fintype coordinate'] in
theorem matrix_reindex (presentation : data.LengthMatrixPresentation coordinate)
    (relabel : coordinate' ≃ coordinate) :
    matrix (reindex presentation relabel) =
      (matrix presentation).submatrix relabel relabel := by
  funext sourceRow column
  exact row_reindex presentation relabel _ column

theorem rowDenominator_reindex
    (presentation : data.LengthMatrixPresentation coordinate)
    (relabel : coordinate' ≃ coordinate) (sourceRow : coordinate') :
    rowDenominator (reindex presentation relabel) sourceRow =
      rowDenominator presentation (relabel sourceRow) := by
  classical
  unfold rowDenominator commonDenominator
  rw [matrix_reindex]
  rw [show (Finset.univ : Finset coordinate) = Finset.univ.image relabel from by
    simp [Finset.image_univ_equiv]]
  rw [Finset.lcm_image]
  rfl

theorem denominatorProduct_reindex
    (presentation : data.LengthMatrixPresentation coordinate)
    (relabel : coordinate' ≃ coordinate) :
    denominatorProduct (reindex presentation relabel) =
      denominatorProduct presentation := by
  unfold denominatorProduct
  rw [show (fun sourceRow ↦ rowDenominator (reindex presentation relabel) sourceRow) =
      fun sourceRow ↦ rowDenominator presentation (relabel sourceRow) from
    funext fun sourceRow ↦ rowDenominator_reindex presentation relabel sourceRow]
  exact Fintype.prod_equiv relabel _ _ fun _ ↦ rfl

/-- **Relabelling rows and columns together leaves the signed multiplicity
unchanged.**  No hypothesis: the leaf columns are permuted among themselves
because the target dictionary is composed with the same equivalence. -/
theorem signedMult_reindex (presentation : data.LengthMatrixPresentation coordinate)
    (relabel : coordinate' ≃ coordinate) :
    signedMult (reindex presentation relabel) = signedMult presentation := by
  unfold signedMult
  rw [denominatorProduct_reindex, matrix_reindex, Matrix.det_submatrix_equiv_self]

theorem absMult_reindex (presentation : data.LengthMatrixPresentation coordinate)
    (relabel : coordinate' ≃ coordinate) :
    absMult (reindex presentation relabel) = absMult presentation := by
  unfold absMult
  rw [signedMult_reindex]

omit [Fintype coordinate] in
theorem matrix_reindexRows (presentation : data.LengthMatrixPresentation coordinate)
    (relabel : Equiv.Perm coordinate) (sourceRow column : coordinate) :
    matrix (reindexRows presentation relabel) sourceRow column =
      matrix presentation (relabel sourceRow) column := rfl

theorem rowDenominator_reindexRows
    (presentation : data.LengthMatrixPresentation coordinate)
    (relabel : Equiv.Perm coordinate) (sourceRow : coordinate) :
    rowDenominator (reindexRows presentation relabel) sourceRow =
      rowDenominator presentation (relabel sourceRow) := rfl

theorem denominatorProduct_reindexRows
    (presentation : data.LengthMatrixPresentation coordinate)
    (relabel : Equiv.Perm coordinate) :
    denominatorProduct (reindexRows presentation relabel) =
      denominatorProduct presentation :=
  Fintype.prod_equiv relabel _ _ fun _ ↦ rfl

omit [DecidableEq coordinate] in
theorem leafColumns_reindexRows
    (presentation : data.LengthMatrixPresentation coordinate)
    (relabel : Equiv.Perm coordinate) :
    leafColumns (reindexRows presentation relabel) = leafColumns presentation := rfl

/-- **Permuting the displayed rows changes `Mult` by the sign of the
permutation only**, so `absMult` is unchanged. -/
theorem signedMult_reindexRows
    (presentation : data.LengthMatrixPresentation coordinate)
    (relabel : Equiv.Perm coordinate) :
    signedMult (reindexRows presentation relabel) =
      (Equiv.Perm.sign relabel : ℚ) * signedMult presentation := by
  unfold signedMult
  rw [denominatorProduct_reindexRows,
    show matrix (reindexRows presentation relabel) =
      (matrix presentation).submatrix relabel id from rfl,
    Matrix.det_permute]
  ring

theorem absMult_reindexRows
    (presentation : data.LengthMatrixPresentation coordinate)
    (relabel : Equiv.Perm coordinate) :
    absMult (reindexRows presentation relabel) = absMult presentation := by
  unfold absMult
  rw [signedMult_reindexRows, abs_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign relabel) with h | h <;> rw [h] <;> norm_num

/-! ## 5.  Diagonal index patterns -/

open DraismaVargas.LocalCases.SeedDeterminant in
/-- On a diagonal index pattern the row denominator is the denominator of the
diagonal entry. -/
theorem rowDenominator_of_diagonalPattern
    {presentation : data.LengthMatrixPresentation coordinate}
    (pattern : DiagonalPattern presentation) (sourceRow : coordinate) :
    rowDenominator presentation sourceRow =
      (matrix presentation sourceRow sourceRow).den := by
  refine Nat.dvd_antisymm ?_ ?_
  · refine (commonDenominator_dvd_iff _ _ _).mpr fun column _ ↦ ?_
    by_cases hcolumn : column = sourceRow
    · rw [hcolumn]
    · rw [pattern.matrix_apply_eq_zero hcolumn]
      simp
  · exact den_dvd_commonDenominator _ _ (Finset.mem_univ sourceRow)

open DraismaVargas.LocalCases.SeedDeterminant in
/-- **The multiplicity of a diagonal index pattern**: the numerators of the
diagonal entries, divided by `2^{l(T)}`. -/
theorem signedMult_of_diagonalPattern
    {presentation : data.LengthMatrixPresentation coordinate}
    (pattern : DiagonalPattern presentation) :
    signedMult presentation =
      (∏ sourceRow, ((matrix presentation sourceRow sourceRow).num : ℚ)) /
        2 ^ leafCount target := by
  have hDet : (matrix presentation).det =
      ∏ sourceRow, matrix presentation sourceRow sourceRow := by
    conv_lhs => rw [pattern.matrix_eq_diagonal]
    rw [Matrix.det_diagonal]
  have hDen : ((denominatorProduct presentation : ℚ)) =
      ∏ sourceRow, ((matrix presentation sourceRow sourceRow).den : ℚ) := by
    rw [denominatorProduct, Nat.cast_prod]
    exact Finset.prod_congr rfl fun sourceRow _ ↦ by
      rw [rowDenominator_of_diagonalPattern pattern sourceRow]
  rw [signedMult, hDet, hDen, div_mul_eq_mul_div, ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl fun sourceRow _ ↦ Rat.den_mul_eq_num _

/-! ## 7.  The same multiplicity, read off a full-dimensional presentation

The fibre uses the multiplicity *on a* `FullDimensionalSourcePresentation`.  Everything
above is stated on the bare `LengthMatrixPresentation` it carries, which is strictly more
general; these abbreviations are the full-dimensional form, and are definitionally the same
objects.
-/

section FullDimensional

open DraismaVargas.LocalCases.FullDimensionalSource

variable {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- `D_φ` of a full-dimensional presentation. -/
noncomputable def fdDenominatorProduct
    (fd : FullDimensionalSourcePresentation data coordinate) : ℕ :=
  denominatorProduct fd.labelling.presentation

/-- `Mult φ` of a full-dimensional presentation. -/
noncomputable def fdSignedMult
    (fd : FullDimensionalSourcePresentation data coordinate) : ℚ :=
  signedMult fd.labelling.presentation

/-- `absMult φ` of a full-dimensional presentation. -/
noncomputable def fdAbsMult
    (fd : FullDimensionalSourcePresentation data coordinate) : ℚ :=
  absMult fd.labelling.presentation

/-- `B'` of a full-dimensional presentation. -/
noncomputable def fdClearedMatrix
    (fd : FullDimensionalSourcePresentation data coordinate) :
    Matrix coordinate coordinate ℚ :=
  clearedMatrix fd.labelling.presentation

theorem fdAbsMult_eq_abs_det_clearedMatrix
    (fd : FullDimensionalSourcePresentation data coordinate)
    (hTarget : NoLeafToLeafEdge target) :
    fdAbsMult fd = |(fdClearedMatrix fd).det| :=
  absMult_eq_abs_det_clearedMatrix_of_noLeafToLeafEdge _ hTarget

/-- `Mult φ ≠ 0`: a full-dimensional presentation is nonsingular by
construction. -/
theorem fdSignedMult_ne_zero
    (fd : FullDimensionalSourcePresentation data coordinate) :
    fdSignedMult fd ≠ 0 := by
  have hDen : ((denominatorProduct fd.labelling.presentation : ℚ)) ≠ 0 := by
    exact_mod_cast (denominatorProduct_pos fd.labelling.presentation).ne'
  refine mul_ne_zero (div_ne_zero hDen (by positivity)) fd.det_ne_zero

end FullDimensional


/-! ## 6.  The caterpillar of loops -/

namespace Caterpillar

open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases.CaterpillarDatum
open DraismaVargas.LocalCases.CaterpillarPruning
open DraismaVargas.LocalCases.CaterpillarSpine
open DraismaVargas.LocalCases.CaterpillarStable
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases

/-- **The leaves of `T^CL_g`** are the lollipop tips `v_i`. -/
theorem isLeafVertex_catTree_iff (m : ℕ) (vertex : (catTree m).V) :
    IsLeafVertex (catTree m) vertex ↔
      (vertex.val % 3 = 1 ∨ vertex.val = 6 * m + 3) := by
  have hlt := vertex.isLt
  unfold IsLeafVertex
  constructor
  · intro hCard
    by_contra hClass
    rw [not_or] at hClass
    rcases vertexClass m vertex with h | h | h | h | h | h
    · rw [card_incidentEdges_two m vertex
        (show (⟨0, by omega⟩ : Fin (6 * m + 3)) ≠ ⟨1, by omega⟩ from by
          simp only [ne_eq, Fin.ext_iff]; omega)
        (incidentIndices_root m vertex h)] at hCard
      omega
    · exact hClass.1 h
    · rw [card_incidentEdges_two m vertex
        (show (⟨vertex.val - 1, by omega⟩ : Fin (6 * m + 3)) ≠
            ⟨vertex.val, by omega⟩ from by simp only [ne_eq, Fin.ext_iff]; omega)
        (incidentIndices_stem m vertex h.1 h.2.1 h.2.2)] at hCard
      omega
    · exact hClass.2 h
    · rw [card_incidentEdges_three m vertex
        (show (⟨vertex.val - 1, by omega⟩ : Fin (6 * m + 3)) ≠
            ⟨vertex.val, by omega⟩ from by simp only [ne_eq, Fin.ext_iff]; omega)
        (show (⟨vertex.val - 1, by omega⟩ : Fin (6 * m + 3)) ≠
            ⟨vertex.val + 2, by omega⟩ from by simp only [ne_eq, Fin.ext_iff]; omega)
        (show (⟨vertex.val, by omega⟩ : Fin (6 * m + 3)) ≠
            ⟨vertex.val + 2, by omega⟩ from by simp only [ne_eq, Fin.ext_iff]; omega)
        (incidentIndices_junction m vertex h.1 h.2)] at hCard
      omega
    · rw [card_incidentEdges_two m vertex
        (show (⟨6 * m + 1, by omega⟩ : Fin (6 * m + 3)) ≠
            ⟨6 * m + 2, by omega⟩ from by simp only [ne_eq, Fin.ext_iff]; omega)
        (incidentIndices_lastStem m vertex h)] at hCard
      omega
  · rintro (h | h)
    · exact card_incidentEdges_one m vertex (incidentIndices_leaf m vertex h)
    · exact card_incidentEdges_one m vertex (incidentIndices_lastLeaf m vertex h)

/-- The parent endpoint of a caterpillar edge is never a leaf. -/
theorem parent_not_isLeafVertex (m : ℕ) (i : Fin (6 * m + 3)) :
    ¬ IsLeafVertex (catTree m) (catParent m i) := by
  intro hLeaf
  have h := (isLeafVertex_catTree_iff m _).mp hLeaf
  have hlt := i.isLt
  have hp := (parentIndex_eq_iff (i.val + 1) (parentIndex (i.val + 1))).mp rfl
  simp only [catParent_val] at h
  omega

/-- **No edge of `T^CL_g` joins two leaves.** -/
theorem noLeafToLeafEdge_catTree (m : ℕ) : NoLeafToLeafEdge (catTree m) := by
  intro edge hFirst _
  obtain ⟨i, rfl⟩ := (occ_bijective m).2 edge
  rw [occ_fst] at hFirst
  exact parent_not_isLeafVertex m i hFirst

/-- The leaf `v_i` of `T^CL_g` numbered by its lollipop. -/
def leafIdx (m : ℕ) (vertex : (catTree m).V) : Fin (2 * m + 2) :=
  ⟨if vertex.val ≤ 6 * m + 1 then vertex.val / 3 else 2 * m + 1, by
    split <;> omega⟩

/-- **`l(T^CL_g) = g = 2m + 2`.** -/
theorem leafCount_catTree (m : ℕ) : leafCount (catTree m) = 2 * m + 2 := by
  classical
  unfold leafCount
  rw [← Fintype.card_fin (2 * m + 2), ← Finset.card_univ]
  refine Finset.card_bij (fun vertex _ ↦ leafIdx m vertex)
    (fun _ _ ↦ Finset.mem_univ _) ?_ ?_
  · intro first hfirst second hsecond hEq
    have h1 := (isLeafVertex_catTree_iff m first).mp ((mem_leafVertices first).mp hfirst)
    have h2 := (isLeafVertex_catTree_iff m second).mp ((mem_leafVertices second).mp hsecond)
    have hv1 := first.isLt
    have hv2 := second.isLt
    have hval := congrArg Fin.val hEq
    simp only [leafIdx] at hval
    apply Fin.ext
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      [ (rw [if_pos (by omega), if_pos (by omega)] at hval);
        (rw [if_pos (by omega), if_neg (by omega)] at hval);
        (rw [if_neg (by omega), if_pos (by omega)] at hval);
        (rw [if_neg (by omega), if_neg (by omega)] at hval) ] <;> omega
  · intro index _
    have hlt := index.isLt
    by_cases hk : index.val ≤ 2 * m
    · refine ⟨⟨3 * index.val + 1, by omega⟩, ?_, ?_⟩
      · exact (mem_leafVertices _).mpr ((isLeafVertex_catTree_iff m _).mpr (Or.inl (by
          show (3 * index.val + 1) % 3 = 1
          omega)))
      · apply Fin.ext
        simp only [leafIdx]
        rw [if_pos (by show 3 * index.val + 1 ≤ 6 * m + 1; omega)]
        show (3 * index.val + 1) / 3 = index.val
        omega
    · refine ⟨⟨6 * m + 3, by omega⟩, ?_, ?_⟩
      · exact (mem_leafVertices _).mpr ((isLeafVertex_catTree_iff m _).mpr (Or.inr rfl))
      · apply Fin.ext
        simp only [leafIdx]
        rw [if_neg (by show ¬ (6 * m + 3 ≤ 6 * m + 1); omega)]
        omega

/-! ### The diagonal entries of the caterpillar length matrix -/

theorem path_nodup (m : ℕ) (i : Fin (6 * m + 3)) :
    ((CaterpillarRows.labelling m).path i).Nodup := by
  classical
  unfold StableLengthMatrixLabelling.path
  exact List.Nodup.filter _ (Finset.nodup_toList _)

theorem mem_path_iff_cat (m : ℕ) (i : Fin (6 * m + 3))
    (edge : (caterpillarDatum m).SourceEdge) :
    edge ∈ (CaterpillarRows.labelling m).path i ↔
      ¬ IsDangling (caterpillarDatum m) edge ∧ edge.1.1 = occ m i := by
  rw [StableLengthMatrixLabelling.mem_path_iff]
  constructor
  · rintro ⟨hSurvives, hRow⟩
    refine ⟨hSurvives, ?_⟩
    have hsymm : (catEdgeEquiv m).symm edge.1.1 = i := hRow
    rw [← hsymm]
    exact ((catEdgeEquiv m).apply_symm_apply _).symm
  · rintro ⟨hSurvives, hTarget⟩
    refine ⟨hSurvives, ?_⟩
    show (catEdgeEquiv m).symm edge.1.1 = i
    rw [hTarget]
    exact (catEdgeEquiv m).symm_apply_apply i

theorem coefficient_cat (m : ℕ) (i : Fin (6 * m + 3))
    (edge : (caterpillarDatum m).SourceEdge) (hTarget : edge.1.1 = occ m i) :
    coefficient (CaterpillarRows.labelling m).presentation edge i =
      1 / ((caterpillarDatum m).sourceEdgeIndex edge : ℚ) := by
  classical
  unfold coefficient
  rw [if_pos]
  show i = (catEdgeEquiv m).symm edge.1.1
  rw [hTarget]
  exact ((catEdgeEquiv m).symm_apply_apply i).symm

/-- The diagonal entry is the sum of the reciprocal indices of the surviving
occurrences above that target edge. -/
theorem matrix_diag_eq_sum (m : ℕ) (i : Fin (6 * m + 3)) :
    matrix (CaterpillarRows.labelling m).presentation i i =
      ∑ edge ∈ ((CaterpillarRows.labelling m).path i).toFinset,
        1 / ((caterpillarDatum m).sourceEdgeIndex edge : ℚ) := by
  classical
  have hsum := List.sum_toFinset
    (fun edge ↦ (1 : ℚ) / ((caterpillarDatum m).sourceEdgeIndex edge : ℚ))
    (path_nodup m i)
  rw [hsum]
  show ((CaterpillarRows.labelling m).path i |>.map
    (fun edge ↦ coefficient (CaterpillarRows.labelling m).presentation edge i)).sum = _
  congr 1
  refine List.map_congr_left fun edge hEdge ↦ ?_
  exact coefficient_cat m i edge ((mem_path_iff_cat m i edge).mp hEdge).2

/-- Above a leaf edge exactly the two loop flags survive. -/
theorem toFinset_path_leaf (m : ℕ) {i : Fin (6 * m + 3)} (hLeaf : IsLeafEdge m i) :
    ((CaterpillarRows.labelling m).path i).toFinset =
      ({loopFirst m i, loopSecond m i} : Finset (caterpillarDatum m).SourceEdge) := by
  classical
  ext edge
  rw [List.mem_toFinset, mem_path_iff_cat, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hSurvives, hTarget⟩
    have hself : (caterpillarDatum m).sourceEdge (occ m i) edge.1.2 = edge := by
      have hs := GluingDatum.sourceEdge_self (caterpillarDatum m) edge
      rw [hTarget] at hs
      exact hs
    have hDang : ¬ (edge.1.2.val ≠ 0 ∧ edge.1.2.val ≠ (partnerSheet m i).val) := by
      intro hcon
      exact hSurvives (hself ▸ (leafOccurrence_isDangling_iff hLeaf edge.1.2).mpr hcon)
    rw [not_and_or, not_not, not_not] at hDang
    rcases hDang with h | h
    · exact Or.inl (by rw [← hself, show edge.1.2 = 0 from Fin.ext h]; rfl)
    · exact Or.inr (by
        rw [← hself, show edge.1.2 = partnerSheet m i from Fin.ext h]; rfl)
  · rintro (rfl | rfl)
    · exact ⟨fun hDang ↦ (leafOccurrence_isDangling_iff hLeaf 0).mp hDang |>.1 rfl, rfl⟩
    · exact ⟨fun hDang ↦ (leafOccurrence_isDangling_iff hLeaf (partnerSheet m i)).mp
        hDang |>.2 rfl, rfl⟩

/-- Off the leaf edges only the spine-sheet block survives. -/
theorem sourceEdge_eq_spineSheet (m : ℕ) {i : Fin (6 * m + 3)}
    (hNotLeaf : ¬ IsLeafEdge m i) (s : Fin (m + 2))
    (hSurvives : ¬ IsDangling (caterpillarDatum m)
      ((caterpillarDatum m).sourceEdge (occ m i) s)) :
    (caterpillarDatum m).sourceEdge (occ m i) s =
      (caterpillarDatum m).sourceEdge (occ m i) 0 := by
  by_cases hs0 : s.val = 0
  · rw [show s = 0 from Fin.ext hs0]
  have hPairRel : ∀ hPair : IsPairEdge m i.val, s.val = pairIndex (i.val + 1) →
      (caterpillarDatum m).sourceEdge (occ m i) s =
        (caterpillarDatum m).sourceEdge (occ m i) 0 := by
    intro hPair hs
    apply Subtype.ext
    apply Prod.ext
    · rfl
    change ((caterpillarDatum m).edgePartition (occ m i)).Rel s 0
    rw [caterpillarDatum_edgePartition, catEdgePart_of_pair m i hPair]
    exact pairPart_rel_zero m _ s hs
  rcases CaterpillarRows.leaf_or_stem_or_spine m i with hLeaf | hStem | hSpine
  · exact absurd hLeaf hNotLeaf
  · have hDang := (stemOccurrence_isDangling_iff hStem s)
    have hsp : s.val = (partnerSheet m i).val := by
      by_contra hne
      exact hSurvives (hDang.mpr ⟨hs0, hne⟩)
    exact hPairRel (pair_of_stem hStem) hsp
  · have hDang := (spineOccurrence_isDangling_iff hSpine s)
    have hi : i.val = 6 * (s.val - 1) + 1 := by
      by_contra hne
      exact hSurvives (hDang.mpr ⟨hs0, hne⟩)
    have hsPos : 1 ≤ s.val := Nat.one_le_iff_ne_zero.mpr hs0
    refine hPairRel (Or.inl (by omega)) ?_
    unfold pairIndex lolli
    omega

theorem toFinset_path_notLeaf (m : ℕ) {i : Fin (6 * m + 3)}
    (hNotLeaf : ¬ IsLeafEdge m i) :
    ((CaterpillarRows.labelling m).path i).toFinset =
      ({(caterpillarDatum m).sourceEdge (occ m i) 0} :
        Finset (caterpillarDatum m).SourceEdge) := by
  classical
  ext edge
  rw [List.mem_toFinset, mem_path_iff_cat, Finset.mem_singleton]
  constructor
  · rintro ⟨hSurvives, hTarget⟩
    have hself : (caterpillarDatum m).sourceEdge (occ m i) edge.1.2 = edge := by
      have hs := GluingDatum.sourceEdge_self (caterpillarDatum m) edge
      rw [hTarget] at hs
      exact hs
    rw [← hself]
    exact sourceEdge_eq_spineSheet m hNotLeaf edge.1.2
      (by rw [hself]; exact hSurvives)
  · rintro rfl
    exact ⟨CaterpillarRows.main_survives m i, rfl⟩

/-- **The caterpillar length matrix, entry by entry.** -/
theorem matrix_diag_cat (m : ℕ) (i : Fin (6 * m + 3)) :
    matrix (CaterpillarRows.labelling m).presentation i i =
      if IsLeafEdge m i then 2 else if IsPairEdge m i.val then 1 / 2 else 1 := by
  classical
  rw [matrix_diag_eq_sum]
  by_cases hLeaf : IsLeafEdge m i
  · rw [if_pos hLeaf, toFinset_path_leaf m hLeaf,
      Finset.sum_pair (loopFirst_ne_loopSecond hLeaf)]
    unfold loopFirst loopSecond
    rw [sourceEdgeIndex_caterpillar, sourceEdgeIndex_caterpillar,
      if_neg (fun h ↦ not_pair_of_leaf hLeaf h.1),
      if_neg (fun h ↦ not_pair_of_leaf hLeaf h.1)]
    norm_num
  · rw [if_neg hLeaf, toFinset_path_notLeaf m hLeaf, Finset.sum_singleton,
      sourceEdgeIndex_caterpillar]
    by_cases hPair : IsPairEdge m i.val
    · rw [if_pos hPair, if_pos ⟨hPair, Or.inl rfl⟩]
      norm_num
    · rw [if_neg hPair, if_neg (fun h ↦ hPair h.1)]
      norm_num

/-! ### The caterpillar has multiplicity one -/

/-- The leaf edges of `T^CL_g` numbered by their lollipop. -/
def leafEdgeIdx (m : ℕ) (i : Fin (6 * m + 3)) : Fin (2 * m + 2) :=
  ⟨if i.val ≤ 6 * m then i.val / 3 else 2 * m + 1, by split <;> omega⟩

/-- **`T^CL_g` has `g = 2m + 2` leaf edges**, one per lollipop. -/
theorem card_leafEdges (m : ℕ) :
    ((Finset.univ : Finset (Fin (6 * m + 3))).filter fun i ↦ IsLeafEdge m i).card
      = 2 * m + 2 := by
  classical
  rw [← Fintype.card_fin (2 * m + 2), ← Finset.card_univ]
  refine Finset.card_bij (fun i _ ↦ leafEdgeIdx m i) (fun _ _ ↦ Finset.mem_univ _) ?_ ?_
  · intro first hfirst second hsecond hEq
    have h1 : IsLeafEdge m first := (Finset.mem_filter.mp hfirst).2
    have h2 : IsLeafEdge m second := (Finset.mem_filter.mp hsecond).2
    have hv1 := first.isLt
    have hv2 := second.isLt
    have hval := congrArg Fin.val hEq
    simp only [leafEdgeIdx] at hval
    unfold IsLeafEdge at h1 h2
    apply Fin.ext
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      [ (rw [if_pos (by omega), if_pos (by omega)] at hval);
        (rw [if_pos (by omega), if_neg (by omega)] at hval);
        (rw [if_neg (by omega), if_pos (by omega)] at hval);
        (rw [if_neg (by omega), if_neg (by omega)] at hval) ] <;> omega
  · intro index _
    have hlt := index.isLt
    by_cases hk : index.val ≤ 2 * m
    · refine ⟨⟨3 * index.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Or.inl (by show (3 * index.val) % 3 = 0; omega)⟩, ?_⟩
      apply Fin.ext
      simp only [leafEdgeIdx]
      rw [if_pos (by show 3 * index.val ≤ 6 * m; omega)]
      show (3 * index.val) / 3 = index.val
      omega
    · refine ⟨⟨6 * m + 2, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Or.inr rfl⟩, ?_⟩
      apply Fin.ext
      simp only [leafEdgeIdx]
      rw [if_neg (by show ¬ (6 * m + 2 ≤ 6 * m); omega)]
      omega

theorem num_matrix_diag_cat (m : ℕ) (i : Fin (6 * m + 3)) :
    ((matrix (CaterpillarRows.labelling m).presentation i i).num : ℚ) =
      if IsLeafEdge m i then 2 else 1 := by
  rw [matrix_diag_cat]
  by_cases hLeaf : IsLeafEdge m i
  · rw [if_pos hLeaf, if_pos hLeaf]
    norm_num
  · rw [if_neg hLeaf, if_neg hLeaf]
    by_cases hPair : IsPairEdge m i.val
    · rw [if_pos hPair]; norm_num
    · rw [if_neg hPair]; norm_num

/-- The numerators of the caterpillar's diagonal multiply to `2^{l(T)}`. -/
theorem prod_num_matrix_diag_cat (m : ℕ) :
    ∏ i, ((matrix (CaterpillarRows.labelling m).presentation i i).num : ℚ) =
      2 ^ (2 * m + 2) := by
  classical
  rw [Finset.prod_congr rfl fun i _ ↦ num_matrix_diag_cat m i,
    ← Finset.prod_filter, Finset.prod_const, card_leafEdges]

/-! ### The paper's intermediate values, and where they differ -/

/-- The pair edges of `T^CL_g` -- the slope-two spine edges and the stems --
numbered consecutively. -/
def pairEdgeIdx (m : ℕ) (i : Fin (6 * m + 3)) : Fin (3 * m + 1) :=
  ⟨min (3 * (i.val / 6) +
      (if i.val % 6 = 1 then 0 else if i.val % 6 = 2 then 1 else 2)) (3 * m), by omega⟩

theorem card_pairEdges (m : ℕ) :
    ((Finset.univ : Finset (Fin (6 * m + 3))).filter fun i ↦ IsPairEdge m i.val).card
      = 3 * m + 1 := by
  classical
  rw [← Fintype.card_fin (3 * m + 1), ← Finset.card_univ]
  refine Finset.card_bij (fun i _ ↦ pairEdgeIdx m i) (fun _ _ ↦ Finset.mem_univ _) ?_ ?_
  · intro first hfirst second hsecond hEq
    have h1 : IsPairEdge m first.val := (Finset.mem_filter.mp hfirst).2
    have h2 : IsPairEdge m second.val := (Finset.mem_filter.mp hsecond).2
    have hv1 := first.isLt
    have hv2 := second.isLt
    have hval := congrArg Fin.val hEq
    simp only [pairEdgeIdx] at hval
    unfold IsPairEdge at h1 h2
    apply Fin.ext
    split_ifs at hval <;> omega
  · intro index _
    have hlt := index.isLt
    have hmod : index.val % 3 = 0 ∨ index.val % 3 = 1 ∨ index.val % 3 = 2 := by omega
    rcases hmod with h | h | h
    · have hlt' : 6 * (index.val / 3) + 1 < 6 * m + 3 := by omega
      have hmod6 : (6 * (index.val / 3) + 1) % 6 = 1 := by omega
      refine ⟨⟨6 * (index.val / 3) + 1, hlt'⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Or.inl hmod6⟩, ?_⟩
      apply Fin.ext
      simp only [pairEdgeIdx]
      rw [if_pos (show (6 * (index.val / 3) + 1) % 6 = 1 from hmod6)]
      show min (3 * ((6 * (index.val / 3) + 1) / 6) + 0) (3 * m) = index.val
      omega
    · have hlt' : 6 * (index.val / 3) + 2 < 6 * m + 3 := by omega
      have hmod6 : (6 * (index.val / 3) + 2) % 6 = 2 := by omega
      have hmod3 : (6 * (index.val / 3) + 2) % 3 = 2 := by omega
      have hne : 6 * (index.val / 3) + 2 ≠ 6 * m + 2 := by omega
      refine ⟨⟨6 * (index.val / 3) + 2, hlt'⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Or.inr ⟨hmod3, hne⟩⟩, ?_⟩
      apply Fin.ext
      simp only [pairEdgeIdx]
      rw [if_neg (show ¬ ((6 * (index.val / 3) + 2) % 6 = 1) by omega), if_pos hmod6]
      show min (3 * ((6 * (index.val / 3) + 2) / 6) + 1) (3 * m) = index.val
      omega
    · have hlt' : 6 * (index.val / 3) + 5 < 6 * m + 3 := by omega
      have hmod3 : (6 * (index.val / 3) + 5) % 3 = 2 := by omega
      have hne : 6 * (index.val / 3) + 5 ≠ 6 * m + 2 := by omega
      refine ⟨⟨6 * (index.val / 3) + 5, hlt'⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Or.inr ⟨hmod3, hne⟩⟩, ?_⟩
      apply Fin.ext
      simp only [pairEdgeIdx]
      rw [if_neg (show ¬ ((6 * (index.val / 3) + 5) % 6 = 1) by omega),
        if_neg (show ¬ ((6 * (index.val / 3) + 5) % 6 = 2) by omega)]
      show min (3 * ((6 * (index.val / 3) + 5) / 6) + 2) (3 * m) = index.val
      omega


theorem den_matrix_diag_cat (m : ℕ) (i : Fin (6 * m + 3)) :
    ((matrix (CaterpillarRows.labelling m).presentation i i).den : ℚ) =
      if IsPairEdge m i.val then 2 else 1 := by
  rw [matrix_diag_cat]
  by_cases hLeaf : IsLeafEdge m i
  · rw [if_pos hLeaf, if_neg (not_pair_of_leaf hLeaf)]
    norm_num
  · rw [if_neg hLeaf]
    by_cases hPair : IsPairEdge m i.val
    · rw [if_pos hPair, if_pos hPair]; norm_num
    · rw [if_neg hPair, if_neg hPair]; norm_num

theorem prod_den_matrix_diag_cat (m : ℕ) :
    ∏ i, ((matrix (CaterpillarRows.labelling m).presentation i i).den : ℚ) =
      2 ^ (3 * m + 1) := by
  classical
  rw [Finset.prod_congr rfl fun i _ ↦ den_matrix_diag_cat m i,
    ← Finset.prod_filter, Finset.prod_const, card_pairEdges]

/-- **`D_φ = 2^{3m+1}` for the caterpillar** -- not `2^{l(T)} = 2^{2m+2}`. -/
theorem denominatorProduct_caterpillar (m : ℕ) :
    denominatorProduct (CaterpillarRows.labelling m).presentation = 2 ^ (3 * m + 1) := by
  classical
  have hcast : ((denominatorProduct (CaterpillarRows.labelling m).presentation : ℕ) : ℚ) =
      ((2 ^ (3 * m + 1) : ℕ) : ℚ) := by
    rw [denominatorProduct, Nat.cast_prod, Nat.cast_pow]
    rw [Finset.prod_congr rfl fun i _ ↦ congrArg (fun n : ℕ ↦ (n : ℚ))
      (rowDenominator_of_diagonalPattern (CaterpillarRows.diagonalPattern m) i)]
    rw [prod_den_matrix_diag_cat]
    norm_num
  exact_mod_cast hcast

/-- **`det A_φ = 2^{2m+2} / 2^{3m+1}`** for the caterpillar -- not `1`. -/
theorem det_caterpillar (m : ℕ) :
    (matrix (CaterpillarRows.labelling m).presentation).det =
      2 ^ (2 * m + 2) / 2 ^ (3 * m + 1) := by
  classical
  have hdet : (matrix (CaterpillarRows.labelling m).presentation).det =
      ∏ i, matrix (CaterpillarRows.labelling m).presentation i i := by
    conv_lhs => rw [(CaterpillarRows.diagonalPattern m).matrix_eq_diagonal]
    rw [Matrix.det_diagonal]
  rw [hdet, Finset.prod_congr rfl fun i _ ↦ (Rat.num_div_den _).symm,
    Finset.prod_div_distrib, prod_num_matrix_diag_cat, prod_den_matrix_diag_cat]


/-- **The caterpillar seed has multiplicity one**, uniformly in the genus. -/
theorem signedMult_caterpillar (m : ℕ) :
    signedMult (CaterpillarRows.labelling m).presentation = 1 := by
  rw [signedMult_of_diagonalPattern (CaterpillarRows.diagonalPattern m),
    prod_num_matrix_diag_cat, leafCount_catTree]
  exact div_self (by positivity)

theorem absMult_caterpillar (m : ℕ) :
    absMult (CaterpillarRows.labelling m).presentation = 1 := by
  rw [absMult, signedMult_caterpillar, abs_one]

/-- The workhorse identity, on the caterpillar, with nothing left to
discharge: `|det B'| = 1`. -/
theorem abs_det_clearedMatrix_caterpillar (m : ℕ) :
    |(clearedMatrix (CaterpillarRows.labelling m).presentation).det| = 1 := by
  rw [← absMult_eq_abs_det_clearedMatrix_of_noLeafToLeafEdge _
    (noLeafToLeafEdge_catTree m), absMult_caterpillar]

/-- **Non-vacuity of `IsIntegralMultiplicity`**: the caterpillar seed has
integral (indeed unit) signed multiplicity, with no hypothesis. -/
theorem isIntegralMultiplicity_caterpillar (m : ℕ) :
    IsIntegralMultiplicity (CaterpillarRows.labelling m).presentation :=
  ⟨1, by rw [signedMult_caterpillar]; norm_num⟩

/-! ### Concrete values -/

/-- `g = 2`: three target edges, two of them leaf edges. -/
example : leafCount (catTree 0) = 2 := leafCount_catTree 0

/-- `g = 4`: the one genus where the paper's `D_φ = 2^{l(T)}` and
`det A_φ = 1` hold on the nose in this encoding. -/
example : denominatorProduct (CaterpillarRows.labelling 1).presentation = 2 ^ 4 :=
  denominatorProduct_caterpillar 1

example : (matrix (CaterpillarRows.labelling 1).presentation).det = 1 := by
  rw [det_caterpillar]; norm_num

/-- `g = 6`: `D_φ = 2^7 ≠ 2^6 = 2^{l(T)}` and `det A_φ = 1/2 ≠ 1`, yet the
multiplicity is still one. -/
example : denominatorProduct (CaterpillarRows.labelling 2).presentation = 2 ^ 7 :=
  denominatorProduct_caterpillar 2

example : leafCount (catTree 2) = 6 := leafCount_catTree 2

example : (matrix (CaterpillarRows.labelling 2).presentation).det = 1 / 2 := by
  rw [det_caterpillar]; norm_num

example : absMult (CaterpillarRows.labelling 2).presentation = 1 := absMult_caterpillar 2

/-- Non-vacuity of the relabelling invariance: reindexing the caterpillar's
`3g-3` coordinates by any equivalence keeps its multiplicity one. -/
theorem absMult_reindex_caterpillar (m : ℕ) {coordinate : Type}
    [Fintype coordinate] [DecidableEq coordinate]
    (relabel : coordinate ≃ Fin (6 * m + 3)) :
    absMult (reindex (CaterpillarRows.labelling m).presentation relabel) = 1 := by
  rw [absMult_reindex, absMult_caterpillar]

/-- The full-dimensional form, on Part I's caterpillar seed. -/
theorem fdAbsMult_caterpillar (m : ℕ) :
    fdAbsMult (CaterpillarRows.fullDim m) = 1 := absMult_caterpillar m

end Caterpillar

end DraismaVargas.Count
