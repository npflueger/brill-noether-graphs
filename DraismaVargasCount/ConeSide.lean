import DraismaVargasCount.SegmentWalls

/-!
# Side = sign: the wall coordinate of a member is a common numerator over its determinant

**Source.**  Vargas, Part II (arXiv:2609.09109), the count of the section
*Invariance of the count via continuous deformation* (the balancing condition
`prop-signed-mult` and wall crossing, `proposition-walking-through-II`) and
`lm:change-comb-type`.  The statement used there, and proved here: *for members
whose matrices satisfy `AgreeOffColumn` at the wall column,
`(A_q⁻¹ y)_{wall} = C(y) / det A_q` with `C(y)` common; hence the side on which
`q` sits along a segment through the wall is `sign(det A_q) · sign(C)`.*

The algebra is `DraismaVargas.Infrastructure.ConeWall`
(`cramer_eq_of_agreeOffColumn`, `determinant_coordinate_eq`); the segment
geometry is `DraismaVargas.Count.SegmentWalls` (`Frame`, `Frame.memberEquiv`,
`Frame.coordsAt_segment`, `Frame.IsWallParam`) and, through it,
`DraismaVargas.Infrastructure.RationalAffineWall`.  Nothing here re-derives
either.

## What is proved

* `wallNumerator`, `wallNumerator_eq_cramer` -- the numerator `C(y)` as an
  **explicit function of the request**: `det A_φ · (A_φ⁻¹ y)_col` is the Cramer
  determinant `det (A_φ with column `col` replaced by `y ∘ slot`)`.  No
  invertibility is used in that identification.
* `coordsAt_eq_wallNumerator_div` -- the division form `(A_φ⁻¹ y)_col = C(y) / det A_φ`.
* `wallNumerator_eq_of_agree` -- **the numerator is common**: two frames over the
  same core whose slot permutations agree and whose matrices agree off `col` have
  the same `C(y)`, for every request `y`.  This is
  `ConeWall.determinant_coordinate_eq` at the `Count` layer; it needs neither
  frame to be nonsingular, though frames always are.
* `sign_coordsAt_mul_sign_det_eq` -- **side = sign**, in the crisp form: the
  product `sign (A_φ⁻¹ y)_col · sign (det A_φ)` is the *same* for both members,
  namely `sign C(y)`.  Its positivity readings are
  `coordsAt_pos_iff_of_det_mul_pos` / `coordsAt_pos_iff_of_det_mul_neg`
  (members with determinants of equal sign sit on the same side of the wall,
  members with opposite determinant signs on opposite sides) and
  `coordsAt_eq_zero_iff_of_agree` / `isWallParam_iff_of_agree` (they cross the
  wall at exactly the same parameter).
* `sign_fdSignedMult_eq_sign_det` -- `sign (Mult φ) = sign (det A_φ)`, so the
  displayed law may be read with the **signed multiplicity** in place of the
  determinant.  This is the form the parity at a trivalent wall uses next to
  `Σ_q Mult φ_q = 0`.
* `coordsAt_segment_of_isWallParam` -- **the segment form**: if `s₀` is a wall
  parameter of `(k, col)` on `y(s) = y₀ + s (y₁ − y₀)` then
  `(A_k⁻¹ y(s))_col = (s − s₀) · Δ_k` with `Δ_k = (A_k⁻¹y₁)_col − (A_k⁻¹y₀)_col`
  constant along the segment; hence `coordsAt_pos_iff_of_lt` /
  `coordsAt_pos_iff_of_gt`: the sign of the wall coordinate is constant on each
  side of `s₀` and flips across it.  `wallNumerator_segment` is the same for the
  common numerator, and `sign_coordsAt_segment_after` /
  `sign_coordsAt_segment_before` combine the two into the per-member sign law on
  each side of a **named** wall parameter.
* `WallCrossing` -- the bundle the parity at a trivalent wall asks for: two frames over one
  core, the wall column, the agreement, the segment and the wall parameter named.
  Its fields are restated as `WallCrossing.sign_side`,
  `WallCrossing.sides_agree`, `WallCrossing.sides_opposite`,
  `WallCrossing.isWallParam_second`.
  **Non-vacuity:** `catCrossing`, on the caterpillar frame of every even genus
  `g = 2m + 2`, with the all-ones request, one slot driven through zero, and the
  wall parameter `1/2` (`SegmentWalls.catFrame_wallParam`);
  `catCrossing_sides_agree` exercises the law on it.
* `FibreMember` restatements: `member_det_mul_coords_eq`,
  `member_coords_pos_iff_of_det_mul_pos`, `member_coords_pos_iff_of_det_mul_neg`
  -- the same statements on `Count.Fibre.FibreMember`s over one request, through
  `Frame.memberEquiv`.

## What is NOT proved (every remaining hypothesis, explicitly)

* **The agreement is a hypothesis, not a construction.**  `AgreeOffColumn` at the
  wall column and the equality of the two frames' slot permutations are assumed
  throughout; producing them at an actual wall is the business of the
  `LocalCases` row dictionaries, not of this file.  Nothing
  here builds a member, a limit or a star.
* **No wall is named combinatorially.**  As in `SegmentWalls`, a wall
  parameter is only "a coordinate vanishes"; which degeneration of the source it
  is, is decided elsewhere, wall type by wall type.
* **Nothing is claimed about `Σ_q Mult φ_q`.**  The balancing identity over the
  star is not used or reproved here; the parity at a trivalent wall combines it
  with `sign_fdSignedMult_eq_sign_det` and the side law below.
* **Nothing about integrality, oddness, the genus or the degree** is assumed or
  proved.
* The two-member statements carry `first.slot = second.slot`.  That is not
  cosmetic: `Frame.coordsAt` reads the request through `Frame.slot`, so without
  it the two members solve *different* linear systems and no common numerator
  exists.

## Consumers

The parity at a trivalent wall (step 2 of `Assembly`), which needs exactly
`sign_coordsAt_mul_sign_det_eq` / `sides_agree` / `sides_opposite` per member on
a segment with the wall parameter named, together with `Σ_q Mult φ_q = 0` over
the star and the unchanged members off the wall; and the parity at a type change
(step 3) for the same reason.
-/

namespace DraismaVargas.Count.ConeSide

open DraismaVargas.Infrastructure
open DraismaVargas.Count.SegmentWalls
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p : ℕ} {core : Core n p} {degree : ℕ}

/-! ## 1.  The numerator of a wall coordinate -/

/-- **The numerator of the column `col` of the frame `k` at the request `y`**:
`det A_k · (A_k⁻¹ y)_col`.  `wallNumerator_eq_cramer` identifies it with the
Cramer determinant, and `wallNumerator_eq_of_agree` shows it is common to two
frames agreeing off `col`. -/
noncomputable def wallNumerator (k : Frame core degree) (col : Fin p)
    (y : Fin p → ℚ) : ℚ :=
  k.matrix.det * k.coordsAt y col

/-- **The numerator is the Cramer determinant of the request.**  The proof uses
`adjugate A * A = det A • 1` and no invertibility. -/
theorem wallNumerator_eq_cramer (k : Frame core degree) (col : Fin p)
    (y : Fin p → ℚ) :
    wallNumerator k col y =
      Matrix.cramer k.matrix (fun row ↦ y (k.slot row)) col := by
  have hmul : Matrix.cramer k.matrix (fun row ↦ y (k.slot row)) =
      k.matrix.adjugate.mulVec (k.matrix.mulVec (k.coordsAt y)) := by
    rw [Matrix.cramer_eq_adjugate_mulVec, k.mulVec_coordsAt]
  rw [hmul, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec]
  rfl

/-- **The division form**: `(A_k⁻¹ y)_col = C(y) / det A_k`. -/
theorem coordsAt_eq_wallNumerator_div (k : Frame core degree) (col : Fin p)
    (y : Fin p → ℚ) :
    k.coordsAt y col = wallNumerator k col y / k.matrix.det := by
  rw [wallNumerator, mul_comm, mul_div_assoc, div_self k.det_ne_zero, mul_one]

/-- **The numerator is common to two frames agreeing off the wall column.**
This is `ConeWall.determinant_coordinate_eq` read on the two solutions
`Frame.coordsAt`, so it needs no inverse and no nonsingularity. -/
theorem wallNumerator_eq_of_agree {k l : Frame core degree} {col : Fin p}
    (hslot : k.slot = l.slot)
    (hagree : AgreeOffColumn k.matrix l.matrix col) (y : Fin p → ℚ) :
    wallNumerator k col y = wallNumerator l col y := by
  refine determinant_coordinate_eq hagree ?_
  rw [k.mulVec_coordsAt, l.mulVec_coordsAt, hslot]

/-! ## 2.  Side = sign -/

/-- **Side = sign.**  The product of the sign of the wall coordinate with the
sign of the determinant is the sign of the common numerator, hence the *same*
for both members. -/
theorem sign_coordsAt_mul_sign_det (k : Frame core degree) (col : Fin p)
    (y : Fin p → ℚ) :
    SignType.sign (k.coordsAt y col) * SignType.sign k.matrix.det =
      SignType.sign (wallNumerator k col y) := by
  rw [wallNumerator, sign_mul, mul_comm]

/-- **Side = sign, across the wall.** -/
theorem sign_coordsAt_mul_sign_det_eq {k l : Frame core degree} {col : Fin p}
    (hslot : k.slot = l.slot)
    (hagree : AgreeOffColumn k.matrix l.matrix col) (y : Fin p → ℚ) :
    SignType.sign (k.coordsAt y col) * SignType.sign k.matrix.det =
      SignType.sign (l.coordsAt y col) * SignType.sign l.matrix.det := by
  rw [sign_coordsAt_mul_sign_det, sign_coordsAt_mul_sign_det,
    wallNumerator_eq_of_agree hslot hagree]

/-- The two members' wall coordinates vanish together: they cross the wall at
exactly the same requests. -/
theorem coordsAt_eq_zero_iff_of_agree {k l : Frame core degree} {col : Fin p}
    (hslot : k.slot = l.slot)
    (hagree : AgreeOffColumn k.matrix l.matrix col) (y : Fin p → ℚ) :
    k.coordsAt y col = 0 ↔ l.coordsAt y col = 0 := by
  have hcommon := wallNumerator_eq_of_agree hslot hagree y
  rw [wallNumerator, wallNumerator] at hcommon
  constructor
  · intro h
    rw [h, mul_zero] at hcommon
    exact (mul_eq_zero.mp hcommon.symm).resolve_left l.det_ne_zero
  · intro h
    rw [h, mul_zero] at hcommon
    exact (mul_eq_zero.mp hcommon).resolve_left k.det_ne_zero

/-- Two members agreeing off the wall column have the **same** wall parameters
along a segment. -/
theorem isWallParam_iff_of_agree {k l : Frame core degree} {col : Fin p}
    (hslot : k.slot = l.slot)
    (hagree : AgreeOffColumn k.matrix l.matrix col)
    (y₀ y₁ : Fin p → ℚ) (s : ℚ) :
    k.IsWallParam y₀ y₁ col s ↔ l.IsWallParam y₀ y₁ col s :=
  coordsAt_eq_zero_iff_of_agree hslot hagree _

/-- **Equal determinant signs, same side.** -/
theorem coordsAt_pos_iff_of_det_mul_pos {k l : Frame core degree} {col : Fin p}
    (hslot : k.slot = l.slot)
    (hagree : AgreeOffColumn k.matrix l.matrix col)
    (hdet : 0 < k.matrix.det * l.matrix.det) (y : Fin p → ℚ) :
    0 < k.coordsAt y col ↔ 0 < l.coordsAt y col := by
  have hcommon := wallNumerator_eq_of_agree hslot hagree y
  rw [wallNumerator, wallNumerator] at hcommon
  constructor
  · intro h
    by_contra hcon
    have hle : l.coordsAt y col ≤ 0 := le_of_not_gt hcon
    rcases mul_pos_iff.mp hdet with ⟨hk, hl⟩ | ⟨hk, hl⟩
    · nlinarith
    · nlinarith
  · intro h
    by_contra hcon
    have hle : k.coordsAt y col ≤ 0 := le_of_not_gt hcon
    rcases mul_pos_iff.mp hdet with ⟨hk, hl⟩ | ⟨hk, hl⟩
    · nlinarith
    · nlinarith

/-- **Opposite determinant signs, opposite sides.** -/
theorem coordsAt_pos_iff_of_det_mul_neg {k l : Frame core degree} {col : Fin p}
    (hslot : k.slot = l.slot)
    (hagree : AgreeOffColumn k.matrix l.matrix col)
    (hdet : k.matrix.det * l.matrix.det < 0) (y : Fin p → ℚ) :
    0 < k.coordsAt y col ↔ l.coordsAt y col < 0 := by
  have hcommon := wallNumerator_eq_of_agree hslot hagree y
  rw [wallNumerator, wallNumerator] at hcommon
  constructor
  · intro h
    by_contra hcon
    have hle : 0 ≤ l.coordsAt y col := le_of_not_gt hcon
    rcases mul_neg_iff.mp hdet with ⟨hk, hl⟩ | ⟨hk, hl⟩
    · nlinarith
    · nlinarith
  · intro h
    by_contra hcon
    have hle : k.coordsAt y col ≤ 0 := le_of_not_gt hcon
    rcases mul_neg_iff.mp hdet with ⟨hk, hl⟩ | ⟨hk, hl⟩
    · nlinarith
    · nlinarith

/-! ## 3.  The determinant sign is the signed multiplicity's sign -/

/-- **`sign (Mult φ) = sign (det A_φ)`.**  The weight `D_φ / 2^{l(T)}` is
positive, so the side law may be read with the signed multiplicity in place of
the determinant -- which is how the parity at a trivalent wall uses it, beside
`Σ_q Mult φ_q = 0`. -/
theorem sign_fdSignedMult_eq_sign_det (k : Frame core degree) :
    SignType.sign (fdSignedMult k.fullDim) = SignType.sign k.matrix.det := by
  have hweight : (0 : ℚ) <
      (denominatorProduct k.fullDim.labelling.presentation : ℚ) /
        2 ^ leafCount k.target := by
    have hnum : (0 : ℚ) < (denominatorProduct k.fullDim.labelling.presentation : ℚ) := by
      exact_mod_cast denominatorProduct_pos k.fullDim.labelling.presentation
    positivity
  have hval : fdSignedMult k.fullDim =
      ((denominatorProduct k.fullDim.labelling.presentation : ℚ) /
        2 ^ leafCount k.target) * k.matrix.det := rfl
  rw [hval, sign_mul, sign_pos hweight, one_mul]

/-- **Side = sign, with the signed multiplicity.** -/
theorem sign_coordsAt_mul_sign_signedMult_eq {k l : Frame core degree} {col : Fin p}
    (hslot : k.slot = l.slot)
    (hagree : AgreeOffColumn k.matrix l.matrix col) (y : Fin p → ℚ) :
    SignType.sign (k.coordsAt y col) * SignType.sign (fdSignedMult k.fullDim) =
      SignType.sign (l.coordsAt y col) * SignType.sign (fdSignedMult l.fullDim) := by
  rw [sign_fdSignedMult_eq_sign_det, sign_fdSignedMult_eq_sign_det]
  exact sign_coordsAt_mul_sign_det_eq hslot hagree y

/-! ## 4.  The segment form, with the wall parameter named -/

/-- **The wall coordinate along a segment through a named wall parameter.**
It is `(s − s₀)` times the constant `Δ_k`. -/
theorem coordsAt_segment_of_isWallParam (k : Frame core degree) (y₀ y₁ : Fin p → ℚ)
    (col : Fin p) {s₀ : ℚ} (hwall : k.IsWallParam y₀ y₁ col s₀) (s : ℚ) :
    k.coordsAt (RationalAffineWall.segment y₀ y₁ s) col =
      (s - s₀) * (k.coordsAt y₁ col - k.coordsAt y₀ col) := by
  have hz := (k.isWallParam_iff y₀ y₁ col s₀).mp hwall
  rw [k.coordsAt_segment y₀ y₁ s col]
  linear_combination hz

/-- The same for the common numerator. -/
theorem wallNumerator_segment (k : Frame core degree) (y₀ y₁ : Fin p → ℚ)
    (col : Fin p) {s₀ : ℚ} (hwall : k.IsWallParam y₀ y₁ col s₀) (s : ℚ) :
    wallNumerator k col (RationalAffineWall.segment y₀ y₁ s) =
      (s - s₀) * (wallNumerator k col y₁ - wallNumerator k col y₀) := by
  rw [wallNumerator, wallNumerator, wallNumerator,
    coordsAt_segment_of_isWallParam k y₀ y₁ col hwall s]
  ring

/-- **After the wall**: the sign of the wall coordinate is the sign of `Δ_k`,
constant on `s₀ < s`. -/
theorem coordsAt_pos_iff_of_lt (k : Frame core degree) (y₀ y₁ : Fin p → ℚ)
    (col : Fin p) {s₀ s : ℚ} (hwall : k.IsWallParam y₀ y₁ col s₀) (hs : s₀ < s) :
    0 < k.coordsAt (RationalAffineWall.segment y₀ y₁ s) col ↔
      0 < k.coordsAt y₁ col - k.coordsAt y₀ col := by
  rw [coordsAt_segment_of_isWallParam k y₀ y₁ col hwall s]
  exact mul_pos_iff_of_pos_left (sub_pos.mpr hs)

/-- **Before the wall**: the opposite sign, constant on `s < s₀`. -/
theorem coordsAt_pos_iff_of_gt (k : Frame core degree) (y₀ y₁ : Fin p → ℚ)
    (col : Fin p) {s₀ s : ℚ} (hwall : k.IsWallParam y₀ y₁ col s₀) (hs : s < s₀) :
    0 < k.coordsAt (RationalAffineWall.segment y₀ y₁ s) col ↔
      k.coordsAt y₁ col - k.coordsAt y₀ col < 0 := by
  rw [coordsAt_segment_of_isWallParam k y₀ y₁ col hwall s]
  constructor
  · intro h
    nlinarith [sub_neg.mpr hs]
  · intro h
    nlinarith [sub_neg.mpr hs]

/-- **The per-member sign law after a named wall parameter.** -/
theorem sign_coordsAt_segment_after (k : Frame core degree) (y₀ y₁ : Fin p → ℚ)
    (col : Fin p) {s₀ s : ℚ} (hwall : k.IsWallParam y₀ y₁ col s₀) (hs : s₀ < s) :
    SignType.sign (k.coordsAt (RationalAffineWall.segment y₀ y₁ s) col) *
        SignType.sign k.matrix.det =
      SignType.sign (wallNumerator k col y₁ - wallNumerator k col y₀) := by
  rw [sign_coordsAt_mul_sign_det, wallNumerator_segment k y₀ y₁ col hwall s, sign_mul,
    sign_pos (sub_pos.mpr hs), one_mul]

/-- **The per-member sign law before a named wall parameter**: the mirror
image. -/
theorem sign_coordsAt_segment_before (k : Frame core degree) (y₀ y₁ : Fin p → ℚ)
    (col : Fin p) {s₀ s : ℚ} (hwall : k.IsWallParam y₀ y₁ col s₀) (hs : s < s₀) :
    SignType.sign (k.coordsAt (RationalAffineWall.segment y₀ y₁ s) col) *
        SignType.sign k.matrix.det =
      - SignType.sign (wallNumerator k col y₁ - wallNumerator k col y₀) := by
  rw [sign_coordsAt_mul_sign_det, wallNumerator_segment k y₀ y₁ col hwall s, sign_mul,
    sign_neg (sub_neg.mpr hs)]
  simp

/-! ## 5.  The wall-crossing bundle -/

/-- **A wall crossing**: two frames over one core, the wall column, the
agreement off it, the segment of requests and the wall parameter, all named.
This is the shape the parity at a trivalent wall asks for -- per member, on a
segment, with the wall parameter named. -/
structure WallCrossing (core : Core n p) (degree : ℕ) where
  /-- The first member's frame. -/
  first : Frame core degree
  /-- The second member's frame. -/
  second : Frame core degree
  /-- The wall column. -/
  column : Fin p
  /-- Both frames read the request through the same slot permutation. -/
  slot_eq : first.slot = second.slot
  /-- The matrices agree off the wall column. -/
  agree : AgreeOffColumn first.matrix second.matrix column
  /-- The start of the segment of requests. -/
  startRequest : Fin p → ℚ
  /-- Its end. -/
  endRequest : Fin p → ℚ
  /-- The wall parameter. -/
  param : ℚ
  /-- ... at which the first frame's wall coordinate vanishes. -/
  isWall : first.IsWallParam startRequest endRequest column param

namespace WallCrossing

variable (w : WallCrossing core degree)

/-- The second frame crosses at the same parameter. -/
theorem isWallParam_second :
    w.second.IsWallParam w.startRequest w.endRequest w.column w.param :=
  (isWallParam_iff_of_agree w.slot_eq w.agree _ _ _).mp w.isWall

/-- **Side = sign** on a wall crossing. -/
theorem sign_side (y : Fin p → ℚ) :
    SignType.sign (w.first.coordsAt y w.column) * SignType.sign w.first.matrix.det =
      SignType.sign (w.second.coordsAt y w.column) *
        SignType.sign w.second.matrix.det :=
  sign_coordsAt_mul_sign_det_eq w.slot_eq w.agree y

/-- **Side = sign** with the signed multiplicities. -/
theorem sign_side_signedMult (y : Fin p → ℚ) :
    SignType.sign (w.first.coordsAt y w.column) *
        SignType.sign (fdSignedMult w.first.fullDim) =
      SignType.sign (w.second.coordsAt y w.column) *
        SignType.sign (fdSignedMult w.second.fullDim) :=
  sign_coordsAt_mul_sign_signedMult_eq w.slot_eq w.agree y

/-- Equal determinant signs: the two members sit on the same side. -/
theorem sides_agree (hdet : 0 < w.first.matrix.det * w.second.matrix.det)
    (y : Fin p → ℚ) :
    0 < w.first.coordsAt y w.column ↔ 0 < w.second.coordsAt y w.column :=
  coordsAt_pos_iff_of_det_mul_pos w.slot_eq w.agree hdet y

/-- Opposite determinant signs: the two members sit on opposite sides. -/
theorem sides_opposite (hdet : w.first.matrix.det * w.second.matrix.det < 0)
    (y : Fin p → ℚ) :
    0 < w.first.coordsAt y w.column ↔ w.second.coordsAt y w.column < 0 :=
  coordsAt_pos_iff_of_det_mul_neg w.slot_eq w.agree hdet y

/-- The wall coordinate of the first member along the segment. -/
theorem coordsAt_first_segment (s : ℚ) :
    w.first.coordsAt (RationalAffineWall.segment w.startRequest w.endRequest s)
        w.column =
      (s - w.param) *
        (w.first.coordsAt w.endRequest w.column -
          w.first.coordsAt w.startRequest w.column) :=
  coordsAt_segment_of_isWallParam _ _ _ _ w.isWall s

/-- The wall coordinate of the second member along the segment. -/
theorem coordsAt_second_segment (s : ℚ) :
    w.second.coordsAt (RationalAffineWall.segment w.startRequest w.endRequest s)
        w.column =
      (s - w.param) *
        (w.second.coordsAt w.endRequest w.column -
          w.second.coordsAt w.startRequest w.column) :=
  coordsAt_segment_of_isWallParam _ _ _ _ w.isWallParam_second s

end WallCrossing

/-! ## 6.  Non-vacuity -/

/-- **A wall crossing exists for every even genus `g = 2m + 2`**: the caterpillar
frame against itself, on the segment from the all-ones request to the request
with the slot `j` driven through zero, with wall parameter `1/2`. -/
noncomputable def catCrossing (m : ℕ) (j : Fin (6 * m + 3)) :
    WallCrossing (FibreCaterpillar.catCore m) (m + 2) where
  first := catFrame m
  second := catFrame m
  column := j
  slot_eq := rfl
  agree := fun _ _ _ ↦ rfl
  startRequest := catStart m
  endRequest := catFinish m j
  param := 1 / 2
  isWall := catFrame_wallParam m j

@[simp] theorem catCrossing_param (m : ℕ) (j : Fin (6 * m + 3)) :
    (catCrossing m j).param = 1 / 2 := rfl

/-- The law is not vacuous on it: the determinant product is positive, so the
two readings of the caterpillar frame sit on the same side at every request. -/
theorem catCrossing_sides_agree (m : ℕ) (j : Fin (6 * m + 3))
    (y : Fin (6 * m + 3) → ℚ) :
    0 < (catCrossing m j).first.coordsAt y j ↔
      0 < (catCrossing m j).second.coordsAt y j := by
  refine (catCrossing m j).sides_agree ?_ y
  exact mul_self_pos.mpr (catFrame m).det_ne_zero

/-! ## 7.  The same statements on members of the fibre -/

/-- **Side = sign on members.**  Through `Frame.memberEquiv` every statement
above is a statement about `Count.Fibre.FibreMember`s over one request. -/
theorem member_det_mul_coords_eq {y : Fin p → ℚ}
    (mem₁ mem₂ : FibreMember core y degree) {col : Fin p}
    (hslot : (Frame.of mem₁).slot = (Frame.of mem₂).slot)
    (hagree : AgreeOffColumn mem₁.matrix mem₂.matrix col) :
    mem₁.matrix.det * mem₁.coords col = mem₂.matrix.det * mem₂.coords col := by
  have h := wallNumerator_eq_of_agree (k := Frame.of mem₁) (l := Frame.of mem₂)
    hslot hagree y
  rw [wallNumerator, wallNumerator, Frame.coordsAt_of, Frame.coordsAt_of] at h
  exact h

/-- Members whose determinants have the same sign sit on the same side. -/
theorem member_coords_pos_iff_of_det_mul_pos {y : Fin p → ℚ}
    (mem₁ mem₂ : FibreMember core y degree) {col : Fin p}
    (hslot : (Frame.of mem₁).slot = (Frame.of mem₂).slot)
    (hagree : AgreeOffColumn mem₁.matrix mem₂.matrix col)
    (hdet : 0 < mem₁.matrix.det * mem₂.matrix.det) :
    0 < mem₁.coords col ↔ 0 < mem₂.coords col := by
  have h := coordsAt_pos_iff_of_det_mul_pos (k := Frame.of mem₁) (l := Frame.of mem₂)
    hslot hagree hdet y
  rwa [Frame.coordsAt_of, Frame.coordsAt_of] at h

/-- Members whose determinants have opposite signs sit on opposite sides. -/
theorem member_coords_pos_iff_of_det_mul_neg {y : Fin p → ℚ}
    (mem₁ mem₂ : FibreMember core y degree) {col : Fin p}
    (hslot : (Frame.of mem₁).slot = (Frame.of mem₂).slot)
    (hagree : AgreeOffColumn mem₁.matrix mem₂.matrix col)
    (hdet : mem₁.matrix.det * mem₂.matrix.det < 0) :
    0 < mem₁.coords col ↔ mem₂.coords col < 0 := by
  have h := coordsAt_pos_iff_of_det_mul_neg (k := Frame.of mem₁) (l := Frame.of mem₂)
    hslot hagree hdet y
  rwa [Frame.coordsAt_of, Frame.coordsAt_of] at h

end DraismaVargas.Count.ConeSide
