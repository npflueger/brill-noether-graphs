import DraismaVargasCount.StarPilot

/-!
# Walls inside the positive orthant: the exact criterion

The count of the genus-six assembly is transported along segments of strictly positive
requests, so the walls that matter are those inside the positive orthant.  If no frame had a
coordinate vanishing inside the positive orthant, constancy of the count
(`SegmentWalls.Frame.openAt_segment_iff_of_no_wall`) would carry it across every positive segment
with no wall to cross.  This file gives the exact criterion for a frame coordinate to vanish
somewhere in the strictly positive orthant, and shows that a frame with no such zero is a
rare degeneracy: its length matrix is monomial, as the caterpillar frame's is.

## What is proved

* `coordsAt_smul`, `coordsAt_comb` -- a frame coordinate is a linear functional
  of the request.  (`SegmentWalls.Frame.coordsAt_segment` is the affine-in-`t`
  consequence; this is the underlying linearity in the request itself.)
* `exists_matrix_ne_zero` -- a nonsingular length matrix has no zero row.
* `coordsAt_pos_of_isolatedRow` -- **the no-wall criterion.**  If some row `r`
  of the length matrix is supported in the single column `col`, then
  `0 < k.coordsAt y col` at **every** strictly positive request `y`.  The proof
  is the realization equation plus `StarPilot.matrix_nonneg`: the row reads
  `y (k.slot r) = k.matrix r col * k.coordsAt y col` with a nonnegative
  coefficient.
* `exists_positive_zero_iff` -- **the criterion is exact**: a column carries a
  positive-orthant zero iff `StarPilot.RetainedRowSupport k col`, i.e. iff *no*
  row is supported in that column alone.  The `←` direction is
  `StarPilot.positiveWall_iff`; the `→` direction weakens
  `Frame.DegenerateAt` to the bare vanishing of the one coordinate.
* `isolatedRow_column_unique`, `exists_unique_isolatedRow_of_no_positive_wall` -- **the
  structural answer to "is the caterpillar special?".**  A frame with no positive-orthant
  zero in *any* column has a **monomial** length matrix: every row is supported in
  exactly one column and the column it is supported in determines it.  The
  caterpillar frame is the diagonal case.  So "no positive-orthant wall" is not
  a theorem about frames; it is a rare degeneracy of the length matrix.
* `exists_scale` -- a small positive multiple of a positive request that stays slotwise
  below another, the first step in promoting a positive request with a vanishing
  coordinate to an isolated wall of a segment of positive requests.

## What is not proved here

* **`exists_unique_isolatedRow_of_no_positive_wall` is a statement about the
  length matrix of one frame**, not about the fibre.  A fibre could in principle
  have every frame monomial; no theorem here rules that out for an arbitrary
  core.
* Nothing here is about parity, `switchingCount`, `openOddCount` or `CountLink`.
-/

namespace DraismaVargas.Count.PositiveOrthantWall

open DraismaVargas.Infrastructure
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)

variable {n p degree : ℕ} {core : Core n p}

/-! ## 1.  A frame coordinate is linear in the request -/

/-- Scaling the request scales every frame coordinate. -/
theorem coordsAt_smul (k : Frame core degree) (a : ℚ) (u : Fin p → ℚ) (col : Fin p) :
    k.coordsAt (fun s ↦ a * u s) col = a * k.coordsAt u col := by
  simp only [Frame.coordsAt_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun row _ ↦ by ring

/-- A frame coordinate is a linear functional of the request. -/
theorem coordsAt_comb (k : Frame core degree) (a b : ℚ) (u v : Fin p → ℚ)
    (col : Fin p) :
    k.coordsAt (fun s ↦ a * u s + b * v s) col =
      a * k.coordsAt u col + b * k.coordsAt v col := by
  simp only [Frame.coordsAt_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun row _ ↦ by ring

/-! ## 2.  The exact criterion for a column to have no positive-orthant zero -/

/-- A nonsingular length matrix has no zero row. -/
theorem exists_matrix_ne_zero (k : Frame core degree) (r : Fin p) :
    ∃ c, k.matrix r c ≠ 0 := by
  by_contra h
  push Not at h
  exact k.det_ne_zero (Matrix.det_eq_zero_of_row_eq_zero r h)

/-- **The no-wall criterion.**  If some stable row of the length matrix is
supported in the single column `col`, then that coordinate is strictly positive
at every strictly positive request -- so the column contributes no wall inside
the positive orthant.  This is the abstract form of "the caterpillar frame's
matrix is diagonal". -/
theorem coordsAt_pos_of_isolatedRow (k : Frame core degree) {col r : Fin p}
    (hrow : ∀ c, c ≠ col → k.matrix r c = 0)
    {y : Fin p → ℚ} (hy : ∀ s, 0 < y s) : 0 < k.coordsAt y col := by
  have hsum : k.matrix.mulVec (k.coordsAt y) r =
      k.matrix r col * k.coordsAt y col := by
    change (∑ c, k.matrix r c * k.coordsAt y c) = _
    refine Finset.sum_eq_single col (fun c _ hc ↦ ?_) (fun h ↦ absurd (Finset.mem_univ col) h)
    rw [hrow c hc, zero_mul]
  have hpos : 0 < k.matrix r col * k.coordsAt y col := by
    rw [← hsum, k.mulVec_coordsAt y]
    exact hy (k.slot r)
  rcases mul_pos_iff.mp hpos with ⟨_, h⟩ | ⟨h, _⟩
  · exact h
  · exact absurd h (not_lt.mpr (StarPilot.matrix_nonneg k r col))

/-- **The criterion is exact.**  A column of a frame vanishes somewhere in the
strictly positive orthant precisely when no row of the length matrix is
supported in that column alone.  The `←` direction is
`StarPilot.positiveWall_iff`; the `→` direction needs only the vanishing of the
one coordinate, not `Frame.DegenerateAt`. -/
theorem exists_positive_zero_iff (k : Frame core degree) (col : Fin p) :
    (∃ y : Fin p → ℚ, (∀ s, 0 < y s) ∧ k.coordsAt y col = 0) ↔
      StarPilot.RetainedRowSupport k col := by
  constructor
  · rintro ⟨y, hy, hzero⟩ r
    by_contra hcon
    push Not at hcon
    have hrow : ∀ c, c ≠ col → k.matrix r c = 0 := fun c hc ↦
      le_antisymm (hcon c hc) (StarPilot.matrix_nonneg k r c)
    exact absurd hzero (ne_of_gt (coordsAt_pos_of_isolatedRow k hrow hy))
  · intro hs
    exact ⟨StarPilot.unitWallRequest k col,
      StarPilot.nondegenerate_unitWallRequest k col hs,
      (StarPilot.degenerateAt_unitWallRequest k col).1⟩

/-! ## 3.  No positive-orthant zero anywhere means a monomial length matrix -/

/-- A row supported in one column is supported in only one column. -/
theorem isolatedRow_column_unique (k : Frame core degree) {r col col' : Fin p}
    (h : ∀ c, c ≠ col → k.matrix r c = 0)
    (h' : ∀ c, c ≠ col' → k.matrix r c = 0) : col = col' := by
  by_contra hne
  obtain ⟨c, hc⟩ := exists_matrix_ne_zero k r
  by_cases hcol : c = col
  · exact hc (h' c (by rw [hcol]; exact hne))
  · exact hc (h c hcol)

/-- **Is the caterpillar's no-wall property special, or a theorem?  Special.**
A frame whose coordinates never vanish anywhere in the strictly positive orthant
has a *monomial* length matrix: every row is supported in exactly one column.
The caterpillar frame is the diagonal case of this.  Since a general
full-dimensional presentation is nothing like monomial, no-wall-in-the-positive-orthant
is a degeneracy of the frame, not a property of the fibre. -/
theorem exists_unique_isolatedRow_of_no_positive_wall (k : Frame core degree)
    (h : ∀ (col : Fin p) (y : Fin p → ℚ), (∀ s, 0 < y s) → k.coordsAt y col ≠ 0)
    (r : Fin p) : ∃! col : Fin p, ∀ c, c ≠ col → k.matrix r c = 0 := by
  classical
  have hcol : ∀ col : Fin p, ∃ row : Fin p, ∀ c, c ≠ col → k.matrix row c = 0 := by
    intro col
    have hnot : ¬ StarPilot.RetainedRowSupport k col := by
      rw [← exists_positive_zero_iff]
      rintro ⟨y, hy, hzero⟩
      exact h col y hy hzero
    rw [StarPilot.RetainedRowSupport] at hnot
    push Not at hnot
    obtain ⟨row, hrow⟩ := hnot
    exact ⟨row, fun c hc ↦ le_antisymm (hrow c hc) (StarPilot.matrix_nonneg k row c)⟩
  choose f hf using hcol
  have hinj : Function.Injective f := by
    intro a b hab
    have h2 : ∀ c, c ≠ b → k.matrix (f a) c = 0 := by rw [hab]; exact hf b
    exact isolatedRow_column_unique k (hf a) h2
  obtain ⟨col, hcoleq⟩ := Finite.injective_iff_surjective.mp hinj r
  have hmain : ∀ c, c ≠ col → k.matrix r c = 0 := by rw [← hcoleq]; exact hf col
  exact ⟨col, hmain, fun col' hcol' ↦ (isolatedRow_column_unique k hmain hcol').symm⟩

/-! ## 4.  Towards an isolated segment wall at a positive degenerate request -/

/-- A positive multiple of `z` that stays slotwise below `y`. -/
theorem exists_scale (y z : Fin p → ℚ) (hy : ∀ s, 0 < y s) (hz : ∀ s, 0 < z s)
    (col : Fin p) : ∃ lam : ℚ, 0 < lam ∧ ∀ s, lam * z s < y s := by
  classical
  have hne : (Finset.univ : Finset (Fin p)).Nonempty := ⟨col, Finset.mem_univ col⟩
  refine ⟨Finset.univ.inf' hne (fun s ↦ y s / z s) / 2, ?_, ?_⟩
  · have hpos : 0 < Finset.univ.inf' hne (fun s ↦ y s / z s) := by
      rw [Finset.lt_inf'_iff]
      exact fun s _ ↦ div_pos (hy s) (hz s)
    linarith
  · intro s
    have hle : Finset.univ.inf' hne (fun s ↦ y s / z s) ≤ y s / z s :=
      Finset.inf'_le _ (Finset.mem_univ s)
    rw [le_div_iff₀ (hz s)] at hle
    have hrw : Finset.univ.inf' hne (fun s ↦ y s / z s) / 2 * z s =
        Finset.univ.inf' hne (fun s ↦ y s / z s) * z s / 2 := by ring
    rw [hrw]
    linarith [hy s]

end DraismaVargas.Count.PositiveOrthantWall
