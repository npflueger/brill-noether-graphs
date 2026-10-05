module

public import DraismaVargas.LocalCases.AtlasGenericStart
public import Utilities.IntegralGeometry.PositiveOrthantExit

@[expose] public section

/-!
# Facet genericity for the finite matrix atlas

The route of Vargas, Part II crosses a
codimension-one wall of `M_g^trop` at a *boundary terminal state* of one march:
the endpoint `baseFinish` of the march is chosen on the facet

```text
F = {y : y facet = 0}
```

of the current type's cone, and the state's chart coordinates there are the
lengths of the target tree's edges.  The setup at the wall needs the
chart coordinate vector at such an endpoint to have **exactly one** zero.

This file proves the genericity half of that, in the finish-side analogue of
`AtlasGenericStart.exists_atlasGeneric_preserving_positive`.

## The statement

`FacetGeneric degree y` says: for every chart of the universal
`MatrixAtlas.chart`, at most one chart coordinate of `y` vanishes.
`exists_facetGeneric` produces a rational point of the open facet
(`y facet = 0`, `0 < y t` elsewhere) which is facet-generic.

## The proof

For a chart matrix `M` and a chart coordinate `t`, the vanishing of
`chartCoordinates M y t = (M⁻¹ *ᵥ y) t` is an affine equation in `y`.  On the
facet `{y facet = 0}` its equation is the row `t` of `M⁻¹` with the column
`facet` deleted, so it is a *proper* equation unless that row is supported on
the single column `facet`.  `facetRowWall` is that equation, replaced by the
never-vanishing constant equation `1` in the degenerate case, which makes the
whole family proper and lets the existing finite rational avoidance
(`RationalAffineWall.exists_avoids_preserving_positive`) run over the finite
index `chart × coordinate`.

Two distinct rows of the nonsingular matrix `M⁻¹` cannot both be supported on
the column `facet` (`eq_of_rows_supported_on_single`), so at most one chart
coordinate of an avoiding point vanishes.  Every wall equation has coefficient
`0` at `facet`, so the produced point may be corrected to `y facet = 0` by
`Function.update` without disturbing either the avoidance or the positivity of
the other coordinates (`eval_update_of_coefficient_eq_zero`).

## What is exported

* `eq_of_rows_supported_on_single` — the linear-algebra core;
* `FacetGeneric`, `facetRowWall`, `facetRowWall_proper`, `eval_facetRowWall`;
* `exists_facetGeneric` — **the facet genericity lemma**;
* `exists_zero_of_nonneg_chart` — the "at least one" half, from entrywise
  nonnegativity of an honest length matrix;
* `existsUnique_zero_of_facetGeneric` — exactly one vanishing chart
  coordinate at a nonnegative solution, as the setup at the wall needs;
* `not_facetGeneric_zero` — a two-element non-vacuity check showing
  `FacetGeneric` is not vacuously true.

Nothing here identifies the vanishing coordinate with a contracted target
occurrence, and nothing here is about the source: the march's own endpoint
selection is not performed.
-/

namespace DraismaVargas.LocalCases.FacetGenericity

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.RationalAffineWall
open DraismaVargas.LocalCases.FiniteAtlasMarch

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]

/-! ## 1.  Two rows supported on one column force a singular matrix -/

/-- A nonsingular square matrix has at most one row supported on a single
prescribed column.  This is the codimension count behind facet genericity: the facet
`{y facet = 0}` is a hyperplane, and a chart coordinate vanishes identically on
it exactly when its row of `M⁻¹` is supported on `facet`. -/
theorem eq_of_rows_supported_on_single
    (matrix : Matrix coordinate coordinate ℚ) (hdet : matrix.det ≠ 0)
    (column first second : coordinate)
    (hfirst : ∀ k, k ≠ column → matrix first k = 0)
    (hsecond : ∀ k, k ≠ column → matrix second k = 0) :
    first = second := by
  classical
  by_contra hne
  apply hdet
  by_cases hzero : matrix second column = 0
  · refine Matrix.det_eq_zero_of_row_eq_zero second ?_
    intro k
    by_cases hk : k = column
    · rw [hk]; exact hzero
    · exact hsecond k hk
  · have hrow : matrix first =
        (matrix first column / matrix second column) • matrix second := by
      funext k
      by_cases hk : k = column
      · subst hk
        simp only [Pi.smul_apply, smul_eq_mul]
        field_simp
      · rw [hfirst k hk]
        simp [hsecond k hk]
    have hupdate : matrix.updateRow first (matrix second) first =
        matrix.updateRow first (matrix second) second := by
      rw [Matrix.updateRow_self, Matrix.updateRow_ne (Ne.symm hne)]
    have hzeroDet : (matrix.updateRow first (matrix second)).det = 0 :=
      Matrix.det_zero_of_row_eq hne hupdate
    calc matrix.det
        = (matrix.updateRow first (matrix first)).det := by
          rw [Matrix.updateRow_eq_self]
      _ = (matrix.updateRow first
            ((matrix first column / matrix second column) • matrix second)).det := by
          rw [← hrow]
      _ = (matrix first column / matrix second column) *
            (matrix.updateRow first (matrix second)).det :=
          Matrix.det_updateRow_smul _ _ _ _
      _ = 0 := by rw [hzeroDet, mul_zero]

/-! ## 2.  The facet wall of one chart coordinate -/

/-- One chart coordinate is *facet-degenerate* at `facet` when its row of the
inverse chart matrix is supported on the single column `facet`; then the
coordinate vanishes identically on the facet and cuts out no wall there. -/
def FacetDegenerate (matrix : Matrix coordinate coordinate ℚ)
    (facet row : coordinate) : Prop :=
  ∀ k, k ≠ facet → matrix⁻¹ row k = 0

noncomputable instance instDecidableFacetDegenerate
    (matrix : Matrix coordinate coordinate ℚ) (facet row : coordinate) :
    Decidable (FacetDegenerate matrix facet row) :=
  Classical.dec _

/-- The affine equation, in the base metric, cutting out the vanishing of the
chart coordinate `row` **along the facet** `{y facet = 0}`.

In the degenerate case the coordinate vanishes on the whole facet, so no
equation can be imposed; the constant equation `1` is used instead, which is
proper and is satisfied by every point. -/
noncomputable def facetRowWall (matrix : Matrix coordinate coordinate ℚ)
    (facet row : coordinate) : RationalAffineWall coordinate :=
  if FacetDegenerate matrix facet row then
    { coefficient := fun _ => 0, constant := 1 }
  else
    { coefficient := fun k => if k = facet then 0 else matrix⁻¹ row k,
      constant := 0 }

/-- Every facet wall has vanishing coefficient at the facet column, in both
branches.  This is what lets the avoiding point be corrected onto the facet. -/
theorem facetRowWall_coefficient_facet (matrix : Matrix coordinate coordinate ℚ)
    (facet row : coordinate) :
    (facetRowWall matrix facet row).coefficient facet = 0 := by
  unfold facetRowWall
  split <;> simp

/-- Every facet wall is a proper affine equation. -/
theorem facetRowWall_proper (matrix : Matrix coordinate coordinate ℚ)
    (facet row : coordinate) : (facetRowWall matrix facet row).Proper := by
  classical
  unfold facetRowWall
  split
  · exact proper_of_constant_ne_zero _ (by norm_num)
  · rename_i hdegenerate
    unfold FacetDegenerate at hdegenerate
    push Not at hdegenerate
    obtain ⟨k, hk, hvalue⟩ := hdegenerate
    exact proper_of_coefficient_ne_zero _ (i := k) (by simpa [hk] using hvalue)

/-- On the facet, a non-degenerate facet wall evaluates to the chart
coordinate it governs. -/
theorem eval_facetRowWall (matrix : Matrix coordinate coordinate ℚ)
    (facet row : coordinate) (y : coordinate → ℚ) (hy : y facet = 0)
    (hdegenerate : ¬ FacetDegenerate matrix facet row) :
    (facetRowWall matrix facet row).eval y = chartCoordinates matrix y row := by
  classical
  unfold facetRowWall
  rw [ite_eq_right hdegenerate]
  show (∑ k, (if k = facet then 0 else matrix⁻¹ row k) * y k) + 0 =
    chartCoordinates matrix y row
  rw [add_zero]
  unfold chartCoordinates Matrix.mulVec dotProduct
  refine Finset.sum_congr rfl ?_
  intro k _
  by_cases hk : k = facet
  · subst hk; simp [hy]
  · simp [hk]

/-- An affine equation whose coefficient at `facet` vanishes does not see a
change of the `facet` entry of its argument. -/
theorem eval_update_of_coefficient_eq_zero (wall : RationalAffineWall coordinate)
    (facet : coordinate) (hcoefficient : wall.coefficient facet = 0)
    (y : coordinate → ℚ) (value : ℚ) :
    wall.eval (Function.update y facet value) = wall.eval y := by
  classical
  unfold RationalAffineWall.eval
  congr 1
  refine Finset.sum_congr rfl ?_
  intro k _
  by_cases hk : k = facet
  · subst hk; rw [hcoefficient]; ring
  · rw [Function.update_of_ne hk]

/-! ## 3.  The facet genericity lemma -/

/-- **Facet genericity.**  At most one chart coordinate of the base metric `y`
vanishes, in every chart of the universal matrix atlas.

This is the finish-side analogue of `AtlasGenericStart.AtlasGeneric`: that
condition makes the *crossing times* of a segment pairwise distinct, this one
makes the *vanishing coordinates* of a fixed endpoint unique. -/
def FacetGeneric (degree : ℕ) (y : coordinate → ℚ) : Prop :=
  ∀ (label : MatrixAtlas.chart coordinate degree) (first second : coordinate),
    chartCoordinates (MatrixAtlas.atlasMatrix label) y first = 0 →
    chartCoordinates (MatrixAtlas.atlasMatrix label) y second = 0 →
    first = second

/-- A point avoiding every facet wall is facet-generic. -/
theorem facetGeneric_of_avoids (degree : ℕ) (facet : coordinate)
    (y : coordinate → ℚ) (hy : y facet = 0)
    (havoid : ∀ event : MatrixAtlas.chart coordinate degree × coordinate,
      (facetRowWall (MatrixAtlas.atlasMatrix event.1) facet event.2).eval y ≠ 0) :
    FacetGeneric degree y := by
  classical
  intro label first second hfirst hsecond
  have hdet : ((MatrixAtlas.atlasMatrix label)⁻¹).det ≠ 0 := by
    have hunit : IsUnit (MatrixAtlas.atlasMatrix label).det :=
      isUnit_iff_ne_zero.mpr (MatrixAtlas.atlasMatrix_det_ne_zero label)
    exact isUnit_iff_ne_zero.mp (Matrix.isUnit_nonsing_inv_det _ hunit)
  have hdegenerate : ∀ row : coordinate,
      chartCoordinates (MatrixAtlas.atlasMatrix label) y row = 0 →
      FacetDegenerate (MatrixAtlas.atlasMatrix label) facet row := by
    intro row hrow
    by_contra hcontra
    exact havoid (label, row)
      (by rw [eval_facetRowWall _ facet row y hy hcontra]; exact hrow)
  exact eq_of_rows_supported_on_single _ hdet facet first second
    (hdegenerate first hfirst) (hdegenerate second hsecond)

/-- **The facet genericity lemma.**  Every facet of the positive orthant of
base metrics contains a rational point in its relative interior at which, in
every chart of the universal matrix atlas, at most one chart coordinate
vanishes.

The produced point is the `finish` of one march of the Part II route: it lies
on the facet `{facet = 0}` of the current type's cone, is positive in every
other base coordinate, and is facet-generic. -/
theorem exists_facetGeneric (degree : ℕ) (facet : coordinate) :
    ∃ y : coordinate → ℚ,
      y facet = 0 ∧ (∀ t, t ≠ facet → 0 < y t) ∧ FacetGeneric degree y := by
  classical
  obtain ⟨base, hpositive, havoid⟩ :=
    exists_avoids_preserving_positive
      (ι := coordinate)
      (κ := MatrixAtlas.chart coordinate degree × coordinate)
      (η := {t : coordinate // t ≠ facet})
      (fun event => facetRowWall (MatrixAtlas.atlasMatrix event.1) facet event.2)
      (fun t => coordinateWall t.1) (fun _ => 1)
      (fun event => facetRowWall_proper _ facet event.2)
      (fun t => by simp [eval_coordinateWall])
  refine ⟨Function.update base facet 0, Function.update_self _ _ _, ?_, ?_⟩
  · intro t ht
    rw [Function.update_of_ne ht]
    simpa [eval_coordinateWall] using hpositive ⟨t, ht⟩
  · refine facetGeneric_of_avoids degree facet _ (Function.update_self _ _ _) ?_
    intro event
    rw [eval_update_of_coefficient_eq_zero _ facet
      (facetRowWall_coefficient_facet _ facet event.2)]
    exact havoid event

/-! ## 4.  Exactly one vanishing chart coordinate -/

/-- **At least one chart coordinate vanishes.**  An honest stable length matrix
has nonnegative entries, so a nonnegative solution of `A ⬝ z = y` with a zero
base coordinate `facet` has a zero chart coordinate: the `facet` row of `A` is
not identically zero, and a sum of nonnegative terms vanishes termwise. -/
theorem exists_zero_of_nonneg_chart
    (matrix : Matrix coordinate coordinate ℚ) (hdet : matrix.det ≠ 0)
    (hentries : ∀ i j, 0 ≤ matrix i j) (facet : coordinate)
    (y z : coordinate → ℚ) (hmap : matrix.mulVec z = y) (hy : y facet = 0)
    (hz : ∀ t, 0 ≤ z t) :
    ∃ t, z t = 0 := by
  classical
  have hrow : ∃ t, matrix facet t ≠ 0 := by
    by_contra hcontra
    push Not at hcontra
    exact hdet (Matrix.det_eq_zero_of_row_eq_zero facet hcontra)
  obtain ⟨t, ht⟩ := hrow
  refine ⟨t, ?_⟩
  have hsum : ∑ k, matrix facet k * z k = 0 := by
    have := congrArg (fun v => v facet) hmap
    simpa [Matrix.mulVec, dotProduct, hy] using this
  have hterms : ∀ k ∈ (Finset.univ : Finset coordinate), 0 ≤ matrix facet k * z k :=
    fun k _ => mul_nonneg (hentries facet k) (hz k)
  have hzero : matrix facet t * z t = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hsum t (Finset.mem_univ t)
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd h ht
  · exact h

/-- Every atlas matrix entry is `k / degree !` with `k : ℕ`, hence
nonnegative.  The honest stable length matrices the march registers are
entrywise nonnegative (`SeedDeterminant.row_nonneg`); the crude universal atlas
inherits that for free from its own entry bound. -/
theorem atlasMatrix_nonneg {degree : ℕ}
    (label : MatrixAtlas.chart coordinate degree) (i j : coordinate) :
    0 ≤ MatrixAtlas.atlasMatrix label i j := by
  obtain ⟨k, -, hk⟩ := MatrixAtlas.atlasMatrix_isAtlasMatrix label i j
  rw [hk]
  positivity

/-- **Exactly one vanishing chart coordinate.**  At a facet-generic endpoint, a nonnegative
chart-coordinate solution in a chart of the atlas with nonnegative entries has
*exactly one* vanishing coordinate.

This is the setup needed at a wall: the terminal state's target metric has one
contracted occurrence and is positive at every other occurrence. -/
theorem existsUnique_zero_of_facetGeneric (degree : ℕ)
    (label : MatrixAtlas.chart coordinate degree)
    (hentries : ∀ i j, 0 ≤ MatrixAtlas.atlasMatrix label i j)
    (facet : coordinate) (y z : coordinate → ℚ)
    (hgeneric : FacetGeneric degree y)
    (hmap : (MatrixAtlas.atlasMatrix label).mulVec z = y) (hy : y facet = 0)
    (hz : ∀ t, 0 ≤ z t) :
    ∃! t, z t = 0 := by
  classical
  obtain ⟨t, ht⟩ := exists_zero_of_nonneg_chart _
    (MatrixAtlas.atlasMatrix_det_ne_zero label) hentries facet y z hmap hy hz
  have hchart : chartCoordinates (MatrixAtlas.atlasMatrix label) y = z :=
    chartCoordinates_eq_of_mulVec_eq _
      (MatrixAtlas.atlasMatrix_det_ne_zero label) hmap
  refine ⟨t, ht, ?_⟩
  intro s hs
  exact hgeneric label s t (by rw [hchart]; exact hs) (by rw [hchart]; exact ht)

/-- The same statement with the chart's nonnegativity discharged from the
atlas entry bound: this is the form the march consumes at a terminal state,
where `z` is the state's `currentFinish` and `y` is the march's `baseFinish`. -/
theorem existsUnique_zero_of_facetGeneric_atlas (degree : ℕ)
    (label : MatrixAtlas.chart coordinate degree) (facet : coordinate)
    (y z : coordinate → ℚ) (hgeneric : FacetGeneric degree y)
    (hmap : (MatrixAtlas.atlasMatrix label).mulVec z = y) (hy : y facet = 0)
    (hz : ∀ t, 0 ≤ z t) :
    ∃! t, z t = 0 :=
  existsUnique_zero_of_facetGeneric degree label (atlasMatrix_nonneg label) facet
    y z hgeneric hmap hy hz

/-! ## 5.  Non-vacuity -/

section NonVacuity

/-- The identity matrix is an atlas matrix at every positive degree. -/
theorem isAtlasMatrix_one {degree : ℕ} (hdegree : 0 < degree)
    (hcard : 0 < Fintype.card coordinate) :
    MatrixAtlas.IsAtlasMatrix (coordinate := coordinate) degree 1 := by
  classical
  intro i j
  by_cases hij : i = j
  · refine ⟨MatrixAtlas.denominator degree, ?_, ?_⟩
    · have : 1 ≤ Fintype.card coordinate * degree := Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero hcard.ne' hdegree.ne')
      calc MatrixAtlas.denominator degree
          = MatrixAtlas.denominator degree * 1 := by ring
        _ ≤ MatrixAtlas.denominator degree * (Fintype.card coordinate * degree) :=
            Nat.mul_le_mul_left _ this
    · rw [div_self (MatrixAtlas.denominator_ne_zero degree)]
      simp [Matrix.one_apply, hij]
  · exact ⟨0, Nat.zero_le _, by simp [hij]⟩

/-- **`FacetGeneric` is not vacuously true.**  The zero base metric fails it in
the identity chart as soon as the coordinate type has two elements: every chart
coordinate of `0` vanishes. -/
theorem not_facetGeneric_zero {degree : ℕ} (hdegree : 0 < degree)
    (first second : coordinate) (hne : first ≠ second) :
    ¬ FacetGeneric (coordinate := coordinate) degree (fun _ => 0) := by
  classical
  have hcard : 0 < Fintype.card coordinate :=
    Fintype.card_pos_iff.mpr ⟨first⟩
  intro hgeneric
  have hzero : ∀ t : coordinate,
      chartCoordinates (MatrixAtlas.atlasMatrix
        (MatrixAtlas.encode (1 : Matrix coordinate coordinate ℚ)
          (isAtlasMatrix_one hdegree hcard) (by simp))) (fun _ => 0) t = 0 := by
    intro t
    simp [chartCoordinates, Matrix.mulVec, dotProduct]
  exact hne (hgeneric _ first second (hzero first) (hzero second))

/-- A two-element instance of the facet genericity lemma, to exhibit the hypotheses as jointly
satisfiable at an actual finite coordinate type. -/
theorem exists_facetGeneric_fin_two :
    ∃ y : Fin 2 → ℚ, y 0 = 0 ∧ (∀ t, t ≠ 0 → 0 < y t) ∧ FacetGeneric 1 y :=
  exists_facetGeneric 1 0

end NonVacuity

end DraismaVargas.LocalCases.FacetGenericity
