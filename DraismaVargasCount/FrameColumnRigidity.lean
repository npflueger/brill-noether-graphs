import DraismaVargasCount.ConeSide
import DraismaVargasCount.GeometricSegmentWalls
import DraismaVargasCount.InheritedLimitRows

/-!
# Request-free column rigidity for frame isomorphisms

## The question this file settles

`SegmentWalls.Frame.coordsAt_column` and its geometric twin
`GeometricSegmentWalls.FrameIso.coordsAt_column` export the relation between
two frames of the same core as a *pointwise-in-the-request* identity: for every
`y` and every column `col`, `l.coordsAt y (fi.column col) = k.coordsAt y col`.
The proof of `Frame.coordsAt_column` in the module `SegmentWalls`
does establish the corresponding **matrix** identity
(`l.matrix = k.matrix.submatrix ρ γ`) internally, but discards it; and a
column-rigidity argument that uses the pointwise identity at a *single*
request needs, in addition, a per-frame coordinate-distinctness hypothesis
(injectivity of the target coordinates at that request).

`inv_apply_of_coordsAt_perm` below shows that nothing is lost: the family of
pointwise identities, taken over **all** requests `y`, is *equivalent* to a
matrix identity, recovered by the same indicator-vector trick that
`SegmentWalls.Frame.col_eq_of_coordsAt_eq` already uses.  So the column
permutation can be pinned down by matrix data alone, with no request and no
coordinate-distinctness hypothesis.

## What is proved

* `perm_eq_of_inverse_rows_agree` -- a Mathlib-only statement.  If `M` and `N`
  are invertible, `N⁻¹` composed with `π` on rows equals `M⁻¹` composed with
  `σ` on columns, and `N` agrees with `M` (rows aligned by `σ`, columns aligned
  by `φ`) *off one column*, then `π = φ`.  The invertibility used is that of
  `M` and `N` themselves; nothing about a request enters.
* `Frame.inv_apply_of_coordsAt_perm` -- the matrix form of a `coordsAt`
  intertwiner: a permutation `π` with `l.coordsAt y (π c) = k.coordsAt y c` for
  *all* `y` satisfies `l.matrix⁻¹ (π c) r = k.matrix⁻¹ c (k.slot.symm (l.slot r))`.
* `Frame.perm_eq_of_coordsAt_perm_of_agree` -- the two combined.
* `FrameIso.column_eq_of_retainedColumns` -- the same conclusion from the
  hypothesis shape `StarMetricCompatibility.RetainedColumnsAgree` already uses.
* `FrameIso.column_eq_of_agree` and `FrameIso.column_eq_id_of_agreeOffColumn`
  for the geometric `GeometricSegmentWalls.FrameIso`, and
  `SegmentWalls.FrameIso.column_eq_id_of_agreeOffColumn` for the strict one:
  a frame isomorphism between two frames whose length matrices agree off one
  column (rows aligned through the core slot map) induces the **identity**
  permutation of columns.
* `FrameIso.targetEdge_map_of_agreeOffColumn` -- hence the datum isomorphism
  carries each column label of the source frame to the same column label of the
  target frame.  This is the generic form of the input that
  `Count.W4PairingRigidity`'s `hlabel` hypothesis asks for.
* `FrameIso.column_eq_allColumns` -- the general statement.  For two
  `WallStar.Regrowth`s at a nondegenerate request carrying a geometric limit
  isomorphism that preserves the inherited row labels, *every* frame
  isomorphism between their frames induces exactly the column dictionary
  `InheritedLimitRows.allColumns` of that limit isomorphism.  No coordinate
  distinctness and no choice of request are involved.

## What is NOT proved (every hypothesis, explicitly)

* **`AgreeOffColumn` is a hypothesis here, not a construction.**  Nothing in
  this file proves that two frames of one star have length matrices agreeing
  off the wall column; the module `Star` does not prove it either.
  `column_eq_allColumns` replaces it with the
  hypotheses of `InheritedLimitRows.matrix_retained_iso`, namely a geometric
  limit isomorphism `limIso` **and** its preservation of the inherited row
  labels (`hLabel`); neither is constructed here.
* **`Nondegenerate y` is assumed** in `column_eq_allColumns`, because
  `InheritedLimitRows` assumes it.  It is not assumed anywhere else.
* **The row alignment is a hypothesis in the raw form.**  The agreement
  hypotheses are stated with rows read through each frame's own
  `Frame.slot`; nothing here proves two given frames have a common slot map.
* **No star, count, multiplicity or parity statement is made.**  Nothing here
  evaluates a star, exhibits a star member, or discharges
  `W4PairingRigidity.hlabel` for any concrete wall.
* **No claim that `allColumns` is the identity.**  `column_eq_allColumns`
  identifies the frame-iso column permutation with the limit isomorphism's
  dictionary; whether that dictionary is the identity at a given wall is a
  separate question this file does not touch.
-/

namespace DraismaVargas.Count.FrameColumnRigidity

open DraismaVargas.Infrastructure
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)

/-! ## 1.  The Mathlib-only core -/

/-- **Invertibility pins a permutation down from agreement off one column.**

Read `π` as the column permutation induced by a frame isomorphism, `σ` as the
row alignment between the two frames, `φ` as the dictionary of retained
columns, and `col` as the wall column.  `hinv` is the matrix form of the
`coordsAt` intertwining relation; `hagree` is the retained-column identity.
The conclusion is that the two dictionaries coincide.

The only input beyond bookkeeping is `IsUnit M.det` and `IsUnit N.det`, which
for a frame is `Frame.isUnit_det`, i.e. full-dimensionality.  No request enters,
so there is no circularity with the coordinate calculus. -/
theorem perm_eq_of_inverse_rows_agree {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M N : Matrix ι ι ℚ} (hM : IsUnit M.det) (hN : IsUnit N.det)
    {π φ σ : Equiv.Perm ι} {col : ι}
    (hinv : ∀ c r : ι, N⁻¹ (π c) r = M⁻¹ c (σ r))
    (hagree : ∀ r j : ι, j ≠ col → N r (φ j) = M (σ r) j) :
    π = φ := by
  classical
  have key : ∀ c j : ι, j ≠ col →
      (1 : Matrix ι ι ℚ) (π c) (φ j) = (1 : Matrix ι ι ℚ) c j := by
    intro c j hj
    have h1 : (N⁻¹ * N) (π c) (φ j) = (M⁻¹ * M) c j := by
      rw [Matrix.mul_apply, Matrix.mul_apply,
        ← Equiv.sum_comp σ fun t ↦ M⁻¹ c t * M t j]
      exact Finset.sum_congr rfl fun r _ ↦ by rw [hinv c r, hagree r j hj]
    rwa [Matrix.nonsing_inv_mul _ hN, Matrix.nonsing_inv_mul _ hM] at h1
  refine Equiv.ext fun c ↦ ?_
  by_cases hc : c = col
  · subst hc
    by_contra hne
    have hd : φ.symm (π c) ≠ c := by
      intro h
      exact hne ((Equiv.apply_symm_apply φ (π c)).symm.trans (congrArg φ h))
    have h := key c (φ.symm (π c)) hd
    rw [Equiv.apply_symm_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (Ne.symm hd)] at h
    exact one_ne_zero h
  · have h := key c c hc
    rw [Matrix.one_apply_eq] at h
    by_contra hne
    rw [Matrix.one_apply_ne hne] at h
    exact zero_ne_one h

/-! ## 2.  The pointwise family of coordinate identities is matrix data -/

variable {n p degree : ℕ} {core : Core n p}

/-- **The matrix form of a `coordsAt` intertwiner.**  Knowing
`l.coordsAt y (π c) = k.coordsAt y c` for *every* request `y` is exactly
knowing the corresponding rows of the two inverse length matrices agree, after
the row relabelling that matches the two frames' core slot maps.  The proof is
the indicator-vector trick of `SegmentWalls.Frame.col_eq_of_coordsAt_eq`. -/
theorem inv_apply_of_coordsAt_perm (k l : Frame core degree) {π : Equiv.Perm (Fin p)}
    (hcol : ∀ (y : Fin p → ℚ) (c : Fin p), l.coordsAt y (π c) = k.coordsAt y c)
    (c r : Fin p) :
    l.matrix⁻¹ (π c) r = k.matrix⁻¹ c (k.slot.symm (l.slot r)) := by
  classical
  have hy := hcol (fun s ↦ if s = l.slot r then (1 : ℚ) else 0) c
  rw [Frame.coordsAt_apply, Frame.coordsAt_apply] at hy
  have hL : (∑ row, l.matrix⁻¹ (π c) row * (if l.slot row = l.slot r then (1 : ℚ) else 0)) =
      l.matrix⁻¹ (π c) r := by
    rw [Finset.sum_eq_single r]
    · simp
    · intro b _ hb
      have hne : l.slot b ≠ l.slot r := fun hcon ↦ hb (l.slot.injective hcon)
      simp [hne]
    · intro hcon
      exact absurd (Finset.mem_univ r) hcon
  have hR : (∑ row, k.matrix⁻¹ c row * (if k.slot row = l.slot r then (1 : ℚ) else 0)) =
      k.matrix⁻¹ c (k.slot.symm (l.slot r)) := by
    rw [Finset.sum_eq_single (k.slot.symm (l.slot r))]
    · simp
    · intro b _ hb
      have hne : k.slot b ≠ l.slot r := by
        intro hcon
        exact hb (by rw [← hcon, Equiv.symm_apply_apply])
      simp [hne]
    · intro hcon
      exact absurd (Finset.mem_univ (k.slot.symm (l.slot r))) hcon
  rw [hL, hR] at hy
  exact hy

/-- **The request-free rigidity, in raw form.**  A coordinate intertwiner `π`
between two frames whose length matrices agree off one column, with rows read
through each frame's own core slot map and columns through `φ`, *is* `φ`. -/
theorem perm_eq_of_coordsAt_perm_of_agree (k l : Frame core degree)
    {π φ : Equiv.Perm (Fin p)} {col : Fin p}
    (hcol : ∀ (y : Fin p → ℚ) (c : Fin p), l.coordsAt y (π c) = k.coordsAt y c)
    (hagree : ∀ s j : Fin p, j ≠ col →
      l.matrix (l.slot.symm s) (φ j) = k.matrix (k.slot.symm s) j) :
    π = φ := by
  refine perm_eq_of_inverse_rows_agree k.isUnit_det l.isUnit_det
    (σ := l.slot.trans k.slot.symm) (col := col) (fun c r ↦ ?_) (fun r j hj ↦ ?_)
  · exact inv_apply_of_coordsAt_perm k l hcol c r
  · have h := hagree (l.slot r) j hj
    rwa [Equiv.symm_apply_apply] at h

/-! ## 3.  Slot-aligned agreement off a column -/

/-- **The retained-matrix hypothesis, slot-aligned.**  Two frames' length
matrices agree off `col`, with rows read through each frame's own core-slot
permutation.  This is a statement about matrices; no request occurs in it. -/
def AgreeOffColumnSlot (k l : Frame core degree) (col : Fin p) : Prop :=
  ∀ s j : Fin p, j ≠ col → l.matrix (l.slot.symm s) j = k.matrix (k.slot.symm s) j

/-- Raw `Infrastructure.AgreeOffColumn` plus a common slot map gives the
slot-aligned form. -/
theorem agreeOffColumnSlot_of_agreeOffColumn {k l : Frame core degree} {col : Fin p}
    (hslot : k.slot = l.slot) (h : AgreeOffColumn k.matrix l.matrix col) :
    AgreeOffColumnSlot k l col := by
  intro s j hj
  rw [hslot]
  exact (h _ j hj).symm

end DraismaVargas.Count.FrameColumnRigidity

/-! ## 4.  The geometric frame isomorphism -/

namespace DraismaVargas.Count.GeometricSegmentWalls.FrameIso

open DraismaVargas.Infrastructure
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.FrameColumnRigidity

variable {n p degree : ℕ} {core : Core n p} {k l : Frame core degree}

/-- **Request-free column rigidity, general form.**  If the two length
matrices agree off `col` through the column dictionary `φ`, then *every*
geometric frame isomorphism induces exactly `φ` on columns. -/
theorem column_eq_of_agree (fi : FrameIso k l) {φ : Equiv.Perm (Fin p)} {col : Fin p}
    (hagree : ∀ s j : Fin p, j ≠ col →
      l.matrix (l.slot.symm s) (φ j) = k.matrix (k.slot.symm s) j) :
    fi.column = φ :=
  perm_eq_of_coordsAt_perm_of_agree k l (fun y c ↦ fi.coordsAt_column y c) hagree


/-- **The `StarMetricCompatibility` hypothesis shape.**  This is
`RetainedColumnsAgree`'s and `coords_eq_of_retained_columns`' own form of the
retained-matrix identity (`StarMetricCompatibility.coords_eq_of_retained_columns`,
`StarMetricCompatibility.RetainedColumnsAgree`),
which is already a matrix identity; the frame isomorphism's column permutation
is exactly its column dictionary. -/
theorem column_eq_of_retainedColumns (fi : FrameIso k l) {columns : Equiv.Perm (Fin p)}
    {col : Fin p}
    (hretained : ∀ r c : Fin p, c ≠ col →
      l.matrix (l.slot.symm (k.slot r)) (columns c) = k.matrix r c) :
    fi.column = columns := by
  refine column_eq_of_agree fi (col := col) (fun s j hj ↦ ?_)
  have h := hretained (k.slot.symm s) j hj
  rwa [Equiv.apply_symm_apply] at h

/-- **Request-free column rigidity, `AgreeOffColumn` form.**  From the
retained-column identity as a *matrix*
identity, invertibility of the incoming length matrix forces the induced
column permutation to be the identity.  No request, and no coordinate
distinctness, is used. -/
theorem column_eq_id_of_agreeOffColumn (fi : FrameIso k l) {col : Fin p}
    (hagree : AgreeOffColumnSlot k l col) : fi.column = Equiv.refl (Fin p) :=
  column_eq_of_agree fi (φ := Equiv.refl (Fin p)) (col := col) hagree

theorem column_self_of_agreeOffColumn (fi : FrameIso k l) {col : Fin p}
    (hagree : AgreeOffColumnSlot k l col) (c : Fin p) : fi.column c = c := by
  rw [column_eq_id_of_agreeOffColumn fi hagree]
  rfl

/-- **The generic form of `W4PairingRigidity`'s `hlabel` input.**  The datum
isomorphism carries the column label `c` of the source frame to the column
label `c` of the target frame. -/
theorem targetEdge_map_of_agreeOffColumn (fi : FrameIso k l) {col : Fin p}
    (hagree : AgreeOffColumnSlot k l col) (c : Fin p) :
    fi.datum.targetEdge (k.fullDim.labelling.targetEdge c) =
      l.fullDim.labelling.targetEdge c := by
  have h := column_self_of_agreeOffColumn fi hagree c
  rw [FrameIso.column, Equiv.trans_apply, Equiv.trans_apply] at h
  exact (Equiv.symm_apply_eq _).mp h

end DraismaVargas.Count.GeometricSegmentWalls.FrameIso

/-! ## 5.  The strict frame isomorphism -/

namespace DraismaVargas.Count.SegmentWalls.FrameIso

open DraismaVargas.Infrastructure
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.FrameColumnRigidity

variable {n p degree : ℕ} {core : Core n p} {k l : Frame core degree}

theorem column_eq_of_agree (fi : FrameIso k l) {φ : Equiv.Perm (Fin p)} {col : Fin p}
    (hagree : ∀ s j : Fin p, j ≠ col →
      l.matrix (l.slot.symm s) (φ j) = k.matrix (k.slot.symm s) j) :
    fi.column = φ :=
  perm_eq_of_coordsAt_perm_of_agree k l (fun y c ↦ fi.coordsAt_column y c) hagree

theorem column_eq_id_of_agreeOffColumn (fi : FrameIso k l) {col : Fin p}
    (hagree : AgreeOffColumnSlot k l col) : fi.column = Equiv.refl (Fin p) :=
  column_eq_of_agree fi (φ := Equiv.refl (Fin p)) (col := col) hagree

theorem column_eq_of_retainedColumns (fi : FrameIso k l) {columns : Equiv.Perm (Fin p)}
    {col : Fin p}
    (hretained : ∀ r c : Fin p, c ≠ col →
      l.matrix (l.slot.symm (k.slot r)) (columns c) = k.matrix r c) :
    fi.column = columns := by
  refine column_eq_of_agree fi (col := col) (fun s j hj ↦ ?_)
  have h := hretained (k.slot.symm s) j hj
  rwa [Equiv.apply_symm_apply] at h

end DraismaVargas.Count.SegmentWalls.FrameIso

/-! ## 6.  The limit isomorphism's dictionary is the only freedom -/

namespace DraismaVargas.Count.FrameColumnRigidity

open DraismaVargas.Infrastructure
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.WallStar (Regrowth Nondegenerate)
open DraismaVargas.LocalCases.W4StableSource (StablePath)

variable {n p degree : ℕ} {core : Core n p}

/-- **The general statement.**  Let `w` and `w'` be regrowths at a
nondegenerate request, and let `limIso` be a geometric isomorphism of their
limits preserving the inherited row labels -- the hypotheses of
`InheritedLimitRows.matrix_retained_iso`.  Then *every* geometric frame
isomorphism between the two frames induces exactly the retained-column
dictionary `InheritedLimitRows.allColumns` of `limIso`.

Nothing here is request-specific and no coordinate-distinctness receipt is
used: the retained-column identity enters as the matrix identity it is. -/
theorem column_eq_allColumns {y : Fin p → ℚ} (w w' : Regrowth core y degree)
    (hy : Nondegenerate y)
    (limIso : GeometricDatumIso w.limit w'.limit)
    (hLabel : ∀ row : StablePath w.limit,
      InheritedLimitRows.rowLabel w' hy
          (limIso.stablePathEquiv (InheritedLimitRows.limit_connected w) row) =
        InheritedLimitRows.rowLabel w hy row)
    (fi : GeometricSegmentWalls.FrameIso w.frame w'.frame) :
    fi.column = InheritedLimitRows.allColumns w w' limIso := by
  refine GeometricSegmentWalls.FrameIso.column_eq_of_agree fi (col := w.column)
    (fun s j hj ↦ ?_)
  rw [InheritedLimitRows.allColumns_retained w w' limIso ⟨j, hj⟩]
  exact InheritedLimitRows.matrix_retained_iso w hy w' limIso hLabel s ⟨j, hj⟩

end DraismaVargas.Count.FrameColumnRigidity

/-! ## 7.  The wall-crossing bundle carries the hypothesis -/

namespace DraismaVargas.Count.ConeSide.WallCrossing

open DraismaVargas.Infrastructure
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.FrameColumnRigidity

variable {n p degree : ℕ} {core : Core n p}

/-- `ConeSide.WallCrossing` bundles exactly `slot_eq` and `AgreeOffColumn`, so
its two frames admit no column-moving isomorphism.  No request and no
coordinate-distinctness receipt is used. -/
theorem frameIso_column_eq_id (w : WallCrossing core degree)
    (fi : GeometricSegmentWalls.FrameIso w.first w.second) :
    fi.column = Equiv.refl (Fin p) :=
  GeometricSegmentWalls.FrameIso.column_eq_id_of_agreeOffColumn fi
    (col := w.column) (agreeOffColumnSlot_of_agreeOffColumn w.slot_eq w.agree)

/-- The strict frame isomorphism, same statement. -/
theorem strictFrameIso_column_eq_id (w : WallCrossing core degree)
    (fi : DraismaVargas.Count.SegmentWalls.FrameIso w.first w.second) :
    fi.column = Equiv.refl (Fin p) :=
  DraismaVargas.Count.SegmentWalls.FrameIso.column_eq_id_of_agreeOffColumn fi
    (col := w.column) (agreeOffColumnSlot_of_agreeOffColumn w.slot_eq w.agree)

end DraismaVargas.Count.ConeSide.WallCrossing
