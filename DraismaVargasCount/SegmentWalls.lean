import DraismaVargasCount.FibreNormalForm
import Utilities.IntegralGeometry.RationalGenericStart

/-!
# Wall parameters of a segment of requests, and constancy between them

**Strict and geometric fibres.** Frames and their coordinate-wall and genericity
infrastructure serve both fibres. The quotient and count theorems in this file are
about the strict, orientation-preserving fibre `Fibre`; the request-independence of
the fibre and the constancy of the open odd count that the genus-six count uses are
proved for `GeometricFibre` in `GeometricSegmentWalls`.

**Source.**  Vargas, Part II: the space `TM_{g,d}` (`definition-TMSpace`), the
finiteness of the fibre (the remark following `lemma-count-realizations`), and the
count along general paths (`proposition-generic-path`) and across walls
(`proposition-walking-through-II`).  This file proves that a segment of requests has
finitely many wall parameters and admits generic starts, that the fibre is constant
between consecutive wall parameters, and that general requests (avoiding every wall)
exist.  It is built on the fibre and its finiteness (`DraismaVargasCount.Fibre`,
`Count.FibreNormalForm.instFiniteFibre`) and uses the library's genericity idiom,
`Infrastructure.RationalAffineWall` (`Utilities.IntegralGeometry.RationalWallOrder`,
`Utilities.IntegralGeometry.RationalGenericStart`) -- the same notion
`LocalCases.AtlasGenericStart` and
`LocalCases.CaterpillarGenericSeed.exists_genericInitialState` use: a finite
family of *proper* affine equations, avoided at a rational point of a nonempty
region cut out by strict affine inequalities, with `SimpleAlong` for "distinct
walls cross at distinct times".

## The organising observation

A `Count.FibreMember core y degree` splits into a part that does not move
with the request -- target, gluing datum, full-dimensionality receipt, core
identification -- and the coordinate vector, which the realization equation
determines.  That part is `Frame core degree`, and `Frame.memberEquiv` is an
explicit bijection `Frame core degree ≃ FibreMember core y degree` for **every**
`y`.  Each coordinate of a frame is then a linear functional of the request
(`Frame.coordWall`), so along a segment of requests it is an affine function of
the parameter, and finiteness of wall parameters, constancy between them and the
existence of general requests all come down to the affine-wall calculus of
`RationalAffineWall`.

Note the shape: the fibre is **labelled** and indexed by a `Core n p` together
with a rational length vector `y : Fin p → ℚ`, never by a
`SubdivisionGraph.Spec`.  Everything below is stated that way.

## What is proved

* `Frame`, `Frame.member`, `Frame.of`, `Frame.memberEquiv` -- the frame of a
  member and the bijection above; `Frame.coordsAt` is `A_φ⁻¹ (y ∘ ident)`, and
  `Frame.absMult` shows the multiplicity is a function of the frame alone.
* `Frame.coordWall`, `Frame.eval_coordWall`, `Frame.coordWall_proper` --
  the coordinate walls, **proper with no hypothesis**: a nonsingular length
  matrix has no zero row in its inverse.
* `Frame.isWallParam_subsingleton`, `finite_wallTriples`, `finite_wallParams`,
  `exists_least_wallParam_after` -- **finiteness of wall parameters.**  Over a
  finite family of frames the set of `(member, column, parameter)` triples at
  which a coordinate of `A_φ⁻¹ y(s)` vanishes is finite, and consecutive wall
  parameters exist.  `finite_wallTriples_nf`, `mem_wallParams_nf` and `finite_allWallParams` carry
  this to the whole fibre: every wall parameter of *every* frame is one of the
  finitely many of the normal-form family, and `no_wall_of_no_wall_nf`
  discharges the hypothesis of the constancy theorems against that finite set.
* `Frame.collisionWall_proper`, `exists_generic_start` -- **generic segment starts.**
  From a general endpoint `y₁` and any positive base point, a general positive
  start `y₀` whose segment is nondegenerate on every coordinate wall and along
  which, *for each frame separately*, distinct columns vanish at distinct
  parameters (`RationalAffineWall.SimpleAlong`).  `col_eq_of_isWallParam` is the
  codimension-one consequence: at a wall parameter one column of a frame
  vanishes.  `crossingTime_eq_of_frameIso` and `not_simpleAlong_of_frames_eq`
  are the proof that this is the strongest true form.
* `Frame.pos_of_pos_of_no_wall`, `Frame.openAt_segment_iff_of_no_wall`,
  `openFrames_eq_of_no_wall` -- **constancy between wall parameters, for
  frames.**  Convexity is used in the only form the count needs: each coordinate
  is affine in the segment parameter (`Frame.coordsAt_segment`), so on an
  interval free of its wall parameters its sign does not change.
* `Frame.coordsAt_column`, `FrameIso`, `fibreEquiv`,
  `open_fibreEquiv_iff_of_no_wall` -- **constancy on the quotient.**  An isomorphism
  of gluing data over the core matches coordinate vectors along the induced
  permutation of the columns *at every request*, so the quotient
  `Count.Fibre core y degree` is canonically the same type for every `y`
  (`fibreEquiv`) and, between wall parameters, that bijection matches open
  classes with open classes.  `Frame.coordsAt_column`'s proof uses
  `Count.matrix_labelling_submatrix` (`DraismaVargasCount.TransportMultiplicity`;
  it is a fact about two labellings of one datum, not about segments).
* `exists_general_positive`, `exists_general_positive_fibre` -- **general
  requests.**  Every positive orthant contains a request avoiding every coordinate
  wall of every frame: generality over the finite normal-form family transfers to
  every frame through the coordinate field of `Count.MemberIso`.
* `openOddCount_eq_of_no_wall` -- the constancy between wall parameters of
  `Count.openOddCount`, the count over the fibre *proper* (defined in
  `DraismaVargasCount.Fibre`, next to `oddCount`).
* `catFrame`, `catFrame_wallParam`, `catFrame_wallParam_eq`,
  `catFrame_not_wallParam_of_ne`, `catFrame_openAt_quarter` -- non-vacuity, for
  every even genus `g = 2m + 2`: the caterpillar frame, the all-ones request,
  and the same request with one slot driven through zero.  The segment has
  exactly one wall parameter, at `1/2`, in exactly one column, and the frame is
  still open a quarter of the way *by* the constancy theorem.

## Scope and hypotheses

* **Finiteness is conditional on the segment, not unconditional.**
  `finite_wallTriples` assumes that no coordinate wall contains *both* endpoints
  (`coordsAt y₀ col ≠ 0 ∨ coordsAt y₁ col ≠ 0`).  That is sharp: a frame-column
  whose wall contains the whole segment vanishes at every parameter.  The
  hypothesis is discharged at a general endpoint by `exists_general_positive`.
* **Genericity is per frame, not across frames.**  `exists_generic_start`
  delivers `SimpleAlong` for `(frames i).coordWall` for each `i` separately, and
  this is the strongest true form: isomorphic frames carry *equal* coordinate
  walls (`crossingTime_eq_of_frameIso`), so their crossing times coincide and a
  family-wide `SimpleAlong` over `ι × Fin p` is false whenever the family
  repeats a frame (`not_simpleAlong_of_frames_eq`).  "Distinct limits
  have distinct parameters" is therefore read as "distinct columns of one
  frame", which is what a codimension-one star needs.
* **Density is existence in a region**, the library's idiom: `exists_general_positive`
  produces a general point of any nonempty rational region cut out by strict
  affine inequalities (here the positive orthant), not a topological statement.
* **No wall is named combinatorially.**  A wall parameter here is only "a
  coordinate vanishes"; which degeneration of the source that is -- the star of
  the limit, the type on each side -- is the subject of the wall arguments
  (stars of limits, balancing, sides of a wall) and is not touched here.
* **Nothing about integrality or descent** is assumed or proved here.  `HasOddMult`
  is used in the existential form `DraismaVargasCount.Fibre` gives it; the
  integral form of the multiplicity (`DraismaVargasCount.Integrality`) and its
  bridge `Count.hasOddMult_iff_odd_oddMult` are not needed here.  The descent of
  the multiplicity to the quotient is taken from `Count.isOddClass_cls_iff'`
  (`DraismaVargasCount.TransportMultiplicity`), which has no hypothesis.
* `openOddCount` and `matrix_labelling_submatrix` are not defined here: they are
  defined in `DraismaVargasCount.Fibre` (next to `oddCount`) and
  `DraismaVargasCount.TransportMultiplicity`.  Both are re-exported into this
  namespace right after the `open` lines below, so the names
  `SegmentWalls.openOddCount` and `SegmentWalls.matrix_labelling_submatrix`
  resolve to the same declarations.

## A remark on `Count.oddCount`

`oddCount_eq_oddCount` proves that `Count.oddCount core y degree` is the
**same number for every `y`**.  That is not a defect of this file: `oddCount`
counts every class of odd multiplicity with no positivity condition, and both
the set of classes and their multiplicities are determined by the frames.  The
count that matters is the open odd count, over the classes that are open:
`Count.openOddCount`, whose constancy between walls is proved here, and its
geometric counterpart `GeometricFibre.openOddCount` (`GeometricSegmentWalls`).

## Consumers

The stars of codimension-one limits (`Star`, `ConeSide`) use `Frame` and
`IsWallParam`, and `WallSwitchingBridge` uses `col_eq_of_isWallParam`; the
schedule of segments between requests (`CountSchedule`, behind step 4 of
`Assembly`) uses `exists_generic_start`, `exists_least_wallParam_after`,
`exists_general_positive_fibre` and `openOddCount_eq_of_no_wall`.
-/

namespace DraismaVargas.Count.SegmentWalls

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open Utilities.Certificate.ExplicitPotential (Core)

/-! **Re-exported, not redefined.**  `openOddCount` and `matrix_labelling_submatrix`
are defined in `DraismaVargasCount.Fibre` and `DraismaVargasCount.TransportMultiplicity`
respectively; they are re-exported here so that the names `SegmentWalls.openOddCount`
and `SegmentWalls.matrix_labelling_submatrix` resolve to the same declarations. -/
export DraismaVargas.Count (openOddCount matrix_labelling_submatrix)

variable {n p : ℕ}

/-! ## 1.  Frames: the part of a member that does not move with the request -/

/-- **A frame**: everything a `Count.FibreMember` carries except its coordinate
vector. -/
structure Frame (core : Core n p) (degree : ℕ) where
  /-- The target tree. -/
  target : CFGraph.{0}
  /-- The gluing datum over it. -/
  data : GluingDatum target degree
  /-- Its full-dimensionality receipt, on the request's slot type. -/
  fullDim : FullDimensionalSource.FullDimensionalSourcePresentation data (Fin p)
  /-- The identification of the stable graph with the requested core. -/
  ident : CoreIdentification core data

namespace Frame

variable {core : Core n p} {degree : ℕ} {y : Fin p → ℚ}

/-- The length matrix of a frame. -/
noncomputable def matrix (k : Frame core degree) : Matrix (Fin p) (Fin p) ℚ :=
  GluingDatum.LengthMatrixPresentation.matrix k.fullDim.labelling.presentation

theorem det_ne_zero (k : Frame core degree) : k.matrix.det ≠ 0 := k.fullDim.det_ne_zero

theorem isUnit_det (k : Frame core degree) : IsUnit k.matrix.det :=
  isUnit_iff_ne_zero.mpr k.det_ne_zero

/-- The permutation reading a matrix row as a core slot. -/
def slot (k : Frame core degree) : Fin p ≃ Fin p :=
  k.fullDim.labelling.row.symm.trans k.ident.row

/-- **The coordinate vector a frame gets over the request `y`.** -/
noncomputable def coordsAt (k : Frame core degree) (y : Fin p → ℚ) : Fin p → ℚ :=
  k.matrix⁻¹.mulVec fun row ↦ y (k.slot row)

theorem mulVec_coordsAt (k : Frame core degree) (y : Fin p → ℚ) :
    k.matrix.mulVec (k.coordsAt y) = fun row ↦ y (k.slot row) := by
  rw [coordsAt, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ k.isUnit_det,
    Matrix.one_mulVec]

/-- **The member a frame gives over the request `y`.** -/
noncomputable def member (k : Frame core degree) (y : Fin p → ℚ) :
    FibreMember core y degree where
  target := k.target
  data := k.data
  fullDim := k.fullDim
  ident := k.ident
  coords := k.coordsAt y
  realizes := k.mulVec_coordsAt y

@[simp] theorem coords_member (k : Frame core degree) (y : Fin p → ℚ) :
    (k.member y).coords = k.coordsAt y := rfl

/-- The frame underlying a member. -/
def of (mem : FibreMember core y degree) : Frame core degree :=
  ⟨mem.target, mem.data, mem.fullDim, mem.ident⟩

@[simp] theorem of_member (k : Frame core degree) (y : Fin p → ℚ) :
    Frame.of (k.member y) = k := rfl

/-- The coordinate vector of a member is the one its frame computes. -/
@[simp] theorem coordsAt_of (mem : FibreMember core y degree) :
    (Frame.of mem).coordsAt y = mem.coords :=
  mem.coords_unique _ ((Frame.of mem).mulVec_coordsAt y)

theorem member_of (mem : FibreMember core y degree) : (Frame.of mem).member y = mem := by
  have hc : (Frame.of mem).coordsAt y = mem.coords := coordsAt_of mem
  obtain ⟨target, data, fullDim, ident, coords, realizes⟩ := mem
  simp only [Frame.of] at hc
  simp only [member, Frame.of, hc]

/-- **The members over `y` are the frames, for every `y`.** -/
noncomputable def memberEquiv (core : Core n p) (degree : ℕ) (y : Fin p → ℚ) :
    Frame core degree ≃ FibreMember core y degree where
  toFun k := k.member y
  invFun := Frame.of
  left_inv k := of_member k y
  right_inv mem := member_of mem

end Frame

/-! ## 2.  What a frame decides, and what the request decides -/

namespace Frame

variable {core : Core n p} {degree : ℕ}

/-- **The multiplicity belongs to the frame, not to the request.** -/
noncomputable def absMult (k : Frame core degree) : ℚ := fdAbsMult k.fullDim

@[simp] theorem absMult_member (k : Frame core degree) (y : Fin p → ℚ) :
    (k.member y).absMult = k.absMult := rfl

/-- A frame is open over `y` when all its coordinates there are positive. -/
def OpenAt (k : Frame core degree) (y : Fin p → ℚ) : Prop := ∀ col, 0 < k.coordsAt y col

theorem openAt_iff_open (k : Frame core degree) (y : Fin p → ℚ) :
    k.OpenAt y ↔ (k.member y).Open := Iff.rfl

/-! ### The coordinate walls -/

/-- **The wall functional of one coordinate of one frame**: the linear form on
requests whose value is that coordinate. -/
noncomputable def coordWall (k : Frame core degree) (col : Fin p) :
    RationalAffineWall (Fin p) where
  coefficient s := k.matrix⁻¹ col (k.slot.symm s)
  constant := 0

theorem coordsAt_apply (k : Frame core degree) (y : Fin p → ℚ) (col : Fin p) :
    k.coordsAt y col = ∑ row, k.matrix⁻¹ col row * y (k.slot row) := rfl

@[simp] theorem eval_coordWall (k : Frame core degree) (col : Fin p) (y : Fin p → ℚ) :
    (k.coordWall col).eval y = k.coordsAt y col := by
  rw [coordsAt_apply]
  simp only [RationalAffineWall.eval, coordWall, add_zero]
  exact (Fintype.sum_equiv k.slot _ _ (fun row ↦ by simp)).symm

/-- **Every coordinate wall is proper**: the length matrix is nonsingular, so no
row of its inverse vanishes. -/
theorem coordWall_coefficient_ne_zero (k : Frame core degree) (col : Fin p) :
    ∃ s : Fin p, (k.coordWall col).coefficient s ≠ 0 := by
  by_contra hzero
  have hrow : ∀ row : Fin p, k.matrix⁻¹ col row = 0 := by
    intro row
    by_contra hne
    exact hzero ⟨k.slot row, by simpa [coordWall] using hne⟩
  have hone : (1 : Matrix (Fin p) (Fin p) ℚ) col col = 0 := by
    rw [← Matrix.nonsing_inv_mul _ k.isUnit_det, Matrix.mul_apply]
    simp [hrow]
  simp at hone

theorem coordWall_proper (k : Frame core degree) (col : Fin p) :
    (k.coordWall col).Proper := by
  obtain ⟨s, hs⟩ := k.coordWall_coefficient_ne_zero col
  exact RationalAffineWall.proper_of_coefficient_ne_zero _ hs

/-- **Each coordinate is affine in the segment parameter.**  This is the
convexity input of the constancy between wall parameters, in the only form the
count uses. -/
theorem coordsAt_segment (k : Frame core degree) (y₀ y₁ : Fin p → ℚ) (t : ℚ)
    (col : Fin p) :
    k.coordsAt (RationalAffineWall.segment y₀ y₁ t) col =
      k.coordsAt y₀ col + t * (k.coordsAt y₁ col - k.coordsAt y₀ col) := by
  rw [← eval_coordWall, ← eval_coordWall k col y₀, ← eval_coordWall k col y₁,
    RationalAffineWall.eval_segment]

end Frame

/-! ## 3.  Wall parameters of a segment -/

namespace Frame

variable {core : Core n p} {degree : ℕ}

/-- **A wall parameter**: a parameter of the segment `y₀ → y₁` at which the
column `col` of the frame `k` vanishes. -/
def IsWallParam (k : Frame core degree) (y₀ y₁ : Fin p → ℚ) (col : Fin p) (t : ℚ) :
    Prop :=
  k.coordsAt (RationalAffineWall.segment y₀ y₁ t) col = 0

theorem isWallParam_iff (k : Frame core degree) (y₀ y₁ : Fin p → ℚ) (col : Fin p)
    (t : ℚ) :
    k.IsWallParam y₀ y₁ col t ↔
      k.coordsAt y₀ col + t * (k.coordsAt y₁ col - k.coordsAt y₀ col) = 0 := by
  rw [IsWallParam, coordsAt_segment]

/-- **One column of one frame contributes at most one wall parameter**, unless
both endpoints lie on its wall. -/
theorem isWallParam_subsingleton (k : Frame core degree) (y₀ y₁ : Fin p → ℚ)
    (col : Fin p) (h : k.coordsAt y₀ col ≠ 0 ∨ k.coordsAt y₁ col ≠ 0) :
    Set.Subsingleton {t : ℚ | k.IsWallParam y₀ y₁ col t} := by
  intro t htmem u humem
  have ht := (k.isWallParam_iff y₀ y₁ col t).mp htmem
  have hu := (k.isWallParam_iff y₀ y₁ col u).mp humem
  have hsub : (t - u) * (k.coordsAt y₁ col - k.coordsAt y₀ col) = 0 := by
    linear_combination ht - hu
  rcases mul_eq_zero.mp hsub with hzero | hzero
  · exact sub_eq_zero.mp hzero
  · exfalso
    have hA : k.coordsAt y₀ col = 0 := by
      rw [hzero, mul_zero, add_zero] at ht
      exact ht
    have hB : k.coordsAt y₁ col = 0 := by
      have := sub_eq_zero.mp hzero
      rw [this, hA]
    rcases h with h | h
    · exact h hA
    · exact h hB

end Frame

/-! ### Finiteness over a finite family of frames -/

variable {core : Core n p} {degree : ℕ}

/-- **The wall triples of a family of frames along a segment**: a member of the
family, a column, and a parameter at which that column vanishes. -/
def wallTriples {ι : Type} (frames : ι → Frame core degree) (y₀ y₁ : Fin p → ℚ) :
    Set (ι × Fin p × ℚ) :=
  {x | (frames x.1).IsWallParam y₀ y₁ x.2.1 x.2.2}

/-- **Finiteness of wall parameters.**  Along a segment none of whose
coordinate walls contains both endpoints, the set of `(member, column,
parameter)` triples at which a coordinate of `A_φ⁻¹ y(s)` vanishes is finite.
No decidable counting is used: the proof is the injection to `(member, column)`
supplied by `isWallParam_subsingleton`. -/
theorem finite_wallTriples {ι : Type} [Finite ι] (frames : ι → Frame core degree)
    (y₀ y₁ : Fin p → ℚ)
    (h : ∀ i col, (frames i).coordsAt y₀ col ≠ 0 ∨ (frames i).coordsAt y₁ col ≠ 0) :
    (wallTriples frames y₀ y₁).Finite := by
  rw [← Set.finite_coe_iff]
  have hinj : Function.Injective
      (fun x : wallTriples frames y₀ y₁ ↦ (x.1.1, x.1.2.1)) := by
    rintro ⟨⟨i, col, t⟩, ht⟩ ⟨⟨j, col', u⟩, hu⟩ heq
    have hi : i = j := congrArg Prod.fst heq
    have hcol : col = col' := congrArg Prod.snd heq
    subst hi
    subst hcol
    have htu : t = u :=
      (frames i).isWallParam_subsingleton y₀ y₁ col (h i col) ht hu
    subst htu
    rfl
  exact Finite.of_injective _ hinj

/-- The parameters themselves. -/
def wallParams {ι : Type} (frames : ι → Frame core degree) (y₀ y₁ : Fin p → ℚ) :
    Set ℚ :=
  {t | ∃ i col, (frames i).IsWallParam y₀ y₁ col t}

theorem finite_wallParams {ι : Type} [Finite ι] (frames : ι → Frame core degree)
    (y₀ y₁ : Fin p → ℚ)
    (h : ∀ i col, (frames i).coordsAt y₀ col ≠ 0 ∨ (frames i).coordsAt y₁ col ≠ 0) :
    (wallParams frames y₀ y₁).Finite := by
  refine ((finite_wallTriples frames y₀ y₁ h).image fun x ↦ x.2.2).subset ?_
  rintro t ⟨i, col, ht⟩
  exact ⟨(i, col, t), ht, rfl⟩

/-- **Consecutive wall parameters exist**: after any parameter at which a future
wall remains there is a least next one. -/
theorem exists_least_wallParam_after {ι : Type} [Finite ι]
    (frames : ι → Frame core degree) (y₀ y₁ : Fin p → ℚ)
    (h : ∀ i col, (frames i).coordsAt y₀ col ≠ 0 ∨ (frames i).coordsAt y₁ col ≠ 0)
    (current : ℚ) (hfuture : ∃ t ∈ wallParams frames y₀ y₁, current < t) :
    ∃ t ∈ wallParams frames y₀ y₁, current < t ∧
      ∀ u ∈ wallParams frames y₀ y₁, current < u → t ≤ u := by
  classical
  have hfin : (wallParams frames y₀ y₁ ∩ {t : ℚ | current < t}).Finite :=
    (finite_wallParams frames y₀ y₁ h).inter_of_left _
  obtain ⟨t₀, ht₀, hlt₀⟩ := hfuture
  have hne : hfin.toFinset.Nonempty := ⟨t₀, by simpa using ⟨ht₀, hlt₀⟩⟩
  obtain ⟨t, htmem, htmin⟩ := hfin.toFinset.exists_min_image id hne
  rw [Set.Finite.mem_toFinset] at htmem
  refine ⟨t, htmem.1, htmem.2, ?_⟩
  intro u hu hcurrent
  exact htmin u (by simp [Set.Finite.mem_toFinset, hu, hcurrent])

/-! ## 4.  Constancy between wall parameters -/

theorem segment_segment (y₀ y₁ : Fin p → ℚ) (u v r : ℚ) :
    RationalAffineWall.segment (RationalAffineWall.segment y₀ y₁ u)
        (RationalAffineWall.segment y₀ y₁ v) r =
      RationalAffineWall.segment y₀ y₁ (u + r * (v - u)) := by
  funext i
  simp only [RationalAffineWall.segment]
  ring

theorem mem_interval {u v r : ℚ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    min u v ≤ u + r * (v - u) ∧ u + r * (v - u) ≤ max u v := by
  rcases le_total u v with h | h
  · rw [min_eq_left h, max_eq_right h]
    constructor <;> nlinarith
  · rw [min_eq_right h, max_eq_left h]
    constructor <;> nlinarith

namespace Frame

variable {core : Core n p} {degree : ℕ}

/-- **A coordinate cannot change sign without a wall parameter in between.**
This is the convexity input of the constancy between wall parameters: each
coordinate is affine in the segment parameter, so on an interval free of its
wall parameters its sign is constant. -/
theorem pos_of_pos_of_no_wall (k : Frame core degree) (y₀ y₁ : Fin p → ℚ)
    (col : Fin p) (u v : ℚ)
    (hu : 0 < k.coordsAt (RationalAffineWall.segment y₀ y₁ u) col)
    (hno : ∀ t, min u v ≤ t → t ≤ max u v → ¬ k.IsWallParam y₀ y₁ col t) :
    0 < k.coordsAt (RationalAffineWall.segment y₀ y₁ v) col := by
  rcases lt_trichotomy (k.coordsAt (RationalAffineWall.segment y₀ y₁ v) col) 0
    with hv | hv | hv
  · exfalso
    set wall := k.coordWall col with hwall
    set x := RationalAffineWall.segment y₀ y₁ u with hx
    set z := RationalAffineWall.segment y₀ y₁ v with hz
    have hxpos : 0 < wall.eval x := by rw [hwall, eval_coordWall]; exact hu
    have hzneg : wall.eval z < 0 := by rw [hwall, eval_coordWall]; exact hv
    have hdiff : wall.eval x ≠ wall.eval z := by
      intro hEq
      rw [hEq] at hxpos
      exact absurd hzneg (not_lt.mpr hxpos.le)
    have hr0 : 0 < wall.crossingTime x z :=
      RationalAffineWall.crossingTime_pos wall x z hxpos hzneg
    have hr1 : wall.crossingTime x z < 1 :=
      RationalAffineWall.crossingTime_lt_one wall x z hxpos hzneg
    have hroot : wall.eval
        (RationalAffineWall.segment x z (wall.crossingTime x z)) = 0 :=
      RationalAffineWall.eval_segment_crossingTime_eq_zero wall x z hdiff
    rw [hx, hz, segment_segment] at hroot
    have hmem := mem_interval (u := u) (v := v) hr0.le hr1.le
    exact hno _ hmem.1 hmem.2 (by rw [hwall, eval_coordWall] at hroot; exact hroot)
  · exact absurd hv (hno v (min_le_right u v) (le_max_right u v))
  · exact hv

/-- **Constancy between wall parameters, for one frame.**  Between two parameters
with no wall parameter of `k` in between, `k` is open at one exactly when it is
open at the other. -/
theorem openAt_segment_iff_of_no_wall (k : Frame core degree) (y₀ y₁ : Fin p → ℚ)
    (u v : ℚ)
    (hno : ∀ col t, min u v ≤ t → t ≤ max u v → ¬ k.IsWallParam y₀ y₁ col t) :
    k.OpenAt (RationalAffineWall.segment y₀ y₁ u) ↔
      k.OpenAt (RationalAffineWall.segment y₀ y₁ v) := by
  constructor
  · intro hOpen col
    exact k.pos_of_pos_of_no_wall y₀ y₁ col u v (hOpen col) (hno col)
  · intro hOpen col
    refine k.pos_of_pos_of_no_wall y₀ y₁ col v u (hOpen col) ?_
    intro t hmin hmax
    exact hno col t (by rwa [min_comm]) (by rwa [max_comm])

end Frame

/-- **Constancy between wall parameters, for a family.**  Between consecutive wall
parameters the labelled fibre is constant: the set of frames of the family that
are open is the same at any two parameters with no wall parameter of the family
in between. -/
theorem openFrames_eq_of_no_wall {ι : Type} (frames : ι → Frame core degree)
    (y₀ y₁ : Fin p → ℚ) (u v : ℚ)
    (hno : ∀ t ∈ wallParams frames y₀ y₁, ¬ (min u v ≤ t ∧ t ≤ max u v)) :
    {i | (frames i).OpenAt (RationalAffineWall.segment y₀ y₁ u)} =
      {i | (frames i).OpenAt (RationalAffineWall.segment y₀ y₁ v)} := by
  ext i
  refine (frames i).openAt_segment_iff_of_no_wall y₀ y₁ u v ?_
  intro col t hmin hmax hwall
  exact hno t ⟨i, col, hwall⟩ ⟨hmin, hmax⟩

/-- **The multiplicity does not move at all.**  `absMult` is a function of the
frame, so it is constant along the whole segment, walls included; only which
frames are *open* can change. -/
theorem absMult_member_eq (k : Frame core degree) (y y' : Fin p → ℚ) :
    (k.member y).absMult = (k.member y').absMult := rfl

/-! ## 5.  Generic requests and generic segment starts -/

/-- The coordinate functional of the orthant, as an affine wall. -/
def coordinateWall (i : Fin p) : RationalAffineWall (Fin p) where
  coefficient j := if j = i then 1 else 0
  constant := 0

@[simp] theorem eval_coordinateWall (i : Fin p) (y : Fin p → ℚ) :
    (coordinateWall i).eval y = y i := by
  simp [coordinateWall, RationalAffineWall.eval, Finset.sum_ite_eq']

namespace Frame

variable {core : Core n p} {degree : ℕ}

/-- **The collision equation of two distinct columns of one frame is proper**,
as soon as the endpoint is off the first of the two walls.  The rows of the
inverse of a nonsingular matrix are linearly independent, so a vanishing
collision coefficient vector forces both endpoint values to vanish. -/
theorem collisionWall_proper (k : Frame core degree) (y₁ : Fin p → ℚ)
    {col col' : Fin p} (hne : col ≠ col') (hA : k.coordsAt y₁ col ≠ 0) :
    (RationalAffineWall.collisionWall (k.coordWall col) (k.coordWall col') y₁).Proper := by
  by_contra hnot
  have hall : ∀ s : Fin p,
      (k.coordWall col').eval y₁ * (k.coordWall col).coefficient s -
        (k.coordWall col).eval y₁ * (k.coordWall col').coefficient s = 0 := by
    intro s
    by_contra hs
    exact hnot (RationalAffineWall.collisionWall_proper_of_coefficient_ne_zero _ _ _ hs)
  have hrow : ∀ r : Fin p,
      k.coordsAt y₁ col' * k.matrix⁻¹ col r -
        k.coordsAt y₁ col * k.matrix⁻¹ col' r = 0 := by
    intro r
    have h := hall (k.slot r)
    rw [eval_coordWall, eval_coordWall] at h
    simpa [coordWall] using h
  have hsum : ∑ r, (k.coordsAt y₁ col' * k.matrix⁻¹ col r -
      k.coordsAt y₁ col * k.matrix⁻¹ col' r) * k.matrix r col' = 0 := by
    refine Finset.sum_eq_zero ?_
    intro r _
    rw [hrow r, zero_mul]
  have hexpand : ∑ r, (k.coordsAt y₁ col' * k.matrix⁻¹ col r -
        k.coordsAt y₁ col * k.matrix⁻¹ col' r) * k.matrix r col' =
      k.coordsAt y₁ col' * (k.matrix⁻¹ * k.matrix) col col' -
        k.coordsAt y₁ col * (k.matrix⁻¹ * k.matrix) col' col' := by
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro r _
    ring
  rw [hexpand, Matrix.nonsing_inv_mul _ k.isUnit_det, Matrix.one_apply_ne hne,
    Matrix.one_apply_eq] at hsum
  simp only [mul_zero, mul_one, zero_sub, neg_eq_zero] at hsum
  exact hA hsum

end Frame

/-- **A general request exists in every positive orthant.**
"General" means avoiding every coordinate wall of every frame of the family --
every wall hyperplane of every type carried by the family. -/
theorem exists_general_positive {ι : Type} [Fintype ι] (frames : ι → Frame core degree)
    (base : Fin p → ℚ) (hbase : ∀ i, 0 < base i) :
    ∃ y : Fin p → ℚ, (∀ i, 0 < y i) ∧ ∀ i col, (frames i).coordsAt y col ≠ 0 := by
  obtain ⟨y, hpos, havoid⟩ :=
    RationalAffineWall.exists_avoids_preserving_positive
      (fun x : ι × Fin p ↦ (frames x.1).coordWall x.2) coordinateWall base
      (fun x ↦ (frames x.1).coordWall_proper x.2)
      (by intro l; rw [eval_coordinateWall]; exact hbase l)
  refine ⟨y, fun l ↦ by simpa using hpos l, ?_⟩
  intro i col
  have h := havoid (i, col)
  rwa [Frame.eval_coordWall] at h

/-- The exceptional equations a generic segment start must avoid: every
coordinate wall, every denominator equation, and -- **for one frame at a time**
-- every collision equation of an ordered pair of distinct columns. -/
abbrev SegmentException (ι : Type) (p : ℕ) : Type :=
  (ι × Fin p) ⊕ (ι × Fin p) ⊕ (ι × {q : Fin p × Fin p // q.1 ≠ q.2})

/-- The equation named by an index. -/
noncomputable def segmentException {ι : Type} (frames : ι → Frame core degree)
    (y₁ : Fin p → ℚ) : SegmentException ι p → RationalAffineWall (Fin p)
  | Sum.inl x => (frames x.1).coordWall x.2
  | Sum.inr (Sum.inl x) => ((frames x.1).coordWall x.2).endpointDifference y₁
  | Sum.inr (Sum.inr x) => RationalAffineWall.collisionWall
      ((frames x.1).coordWall x.2.1.1) ((frames x.1).coordWall x.2.1.2) y₁

theorem segmentException_proper {ι : Type} (frames : ι → Frame core degree)
    (y₁ : Fin p → ℚ) (hy₁ : ∀ i col, (frames i).coordsAt y₁ col ≠ 0)
    (e : SegmentException ι p) : (segmentException frames y₁ e).Proper := by
  rcases e with x | x | x
  · exact (frames x.1).coordWall_proper x.2
  · obtain ⟨s, hs⟩ := (frames x.1).coordWall_coefficient_ne_zero x.2
    exact RationalAffineWall.endpointDifference_proper_of_coefficient_ne_zero _ _ hs
  · exact (frames x.1).collisionWall_proper y₁ x.2.2 (hy₁ x.1 x.2.1.1)

/-- **Generic segment starts.**  Given a general endpoint `y₁`, every positive
orthant contains a general start `y₀` whose segment to `y₁` is nondegenerate on
every coordinate wall and along which, *for each frame separately*, distinct
columns vanish at distinct parameters. -/
theorem exists_generic_start {ι : Type} [Fintype ι] (frames : ι → Frame core degree)
    (y₁ : Fin p → ℚ) (hy₁ : ∀ i col, (frames i).coordsAt y₁ col ≠ 0)
    (base : Fin p → ℚ) (hbase : ∀ i, 0 < base i) :
    ∃ y₀ : Fin p → ℚ, (∀ i, 0 < y₀ i) ∧
      (∀ i col, (frames i).coordsAt y₀ col ≠ 0) ∧
      (∀ i col, (frames i).coordsAt y₀ col ≠ (frames i).coordsAt y₁ col) ∧
      ∀ i, RationalAffineWall.SimpleAlong ((frames i).coordWall) y₀ y₁ := by
  obtain ⟨y₀, hpos, havoid⟩ :=
    RationalAffineWall.exists_avoids_preserving_positive (segmentException frames y₁)
      coordinateWall base (segmentException_proper frames y₁ hy₁)
      (by intro l; rw [eval_coordinateWall]; exact hbase l)
  have hgeneral : ∀ i col, (frames i).coordsAt y₀ col ≠ 0 := by
    intro i col
    have h := havoid (Sum.inl (i, col))
    rwa [show segmentException frames y₁ (Sum.inl (i, col)) =
      (frames i).coordWall col from rfl, Frame.eval_coordWall] at h
  have hdiff : ∀ i col,
      ((frames i).coordWall col).eval y₀ ≠ ((frames i).coordWall col).eval y₁ := by
    intro i col hEq
    refine havoid (Sum.inr (Sum.inl (i, col))) ?_
    show (((frames i).coordWall col).endpointDifference y₁).eval y₀ = 0
    rw [RationalAffineWall.eval_endpointDifference, hEq, sub_self]
  refine ⟨y₀, fun l ↦ by simpa using hpos l, hgeneral, ?_, ?_⟩
  · intro i col hEq
    exact hdiff i col (by rw [Frame.eval_coordWall, Frame.eval_coordWall, hEq])
  · intro i first second heq
    by_contra hne
    refine havoid (Sum.inr (Sum.inr (i, ⟨(first, second), hne⟩))) ?_
    show (RationalAffineWall.collisionWall ((frames i).coordWall first)
      ((frames i).coordWall second) y₁).eval y₀ = 0
    exact RationalAffineWall.eval_collisionWall_eq_zero_of_crossingTime_eq
      ((frames i).coordWall first) ((frames i).coordWall second) y₁ y₀
      (hdiff i first) (hdiff i second) heq

/-- **At a wall parameter of a generic segment, one column of a frame vanishes.**
This is the codimension-one statement the star of a limit needs. -/
theorem col_eq_of_isWallParam {ι : Type} (frames : ι → Frame core degree)
    (y₀ y₁ : Fin p → ℚ) (i : ι)
    (hdiff : ∀ col, ((frames i).coordWall col).eval y₀ ≠
      ((frames i).coordWall col).eval y₁)
    (hsimple : RationalAffineWall.SimpleAlong ((frames i).coordWall) y₀ y₁)
    {col col' : Fin p} {t : ℚ}
    (h : (frames i).IsWallParam y₀ y₁ col t)
    (h' : (frames i).IsWallParam y₀ y₁ col' t) : col = col' :=
  RationalAffineWall.wall_eq_of_both_eval_segment_eq_zero ((frames i).coordWall)
    y₀ y₁ hdiff hsimple (by rwa [Frame.eval_coordWall]) (by rwa [Frame.eval_coordWall])

/-! ## 6.  A finite family that covers the whole fibre -/

instance instFiniteFullDim {target : CFGraph.{0}} {degree : ℕ}
    (data : GluingDatum target degree) :
    Finite (FullDimensionalSource.FullDimensionalSourcePresentation data (Fin p)) := by
  refine Finite.of_injective
    (fun fd : FullDimensionalSource.FullDimensionalSourcePresentation data (Fin p) ↦
      fd.labelling) ?_
  intro a b h
  cases a
  cases b
  subst h
  rfl

/-- **The finite index of normal-form frames.**  `Count.FibreNormalForm.Raw`
with the full-dimensionality receipt in place of the bare labelling; the
receipt's other seven fields are propositions, so this is still finite. -/
def NFFrame (core : Core n p) (degree : ℕ) : Type :=
  Σ t : FibreNormalForm.TargetIndex p,
    Σ data : GluingDatum (FibreNormalForm.indexTarget t) degree,
      FullDimensionalSource.FullDimensionalSourcePresentation data (Fin p) ×
        CoreIdentification core data

instance instFiniteNFFrame (core : Core n p) (degree : ℕ) :
    Finite (NFFrame core degree) := by
  unfold NFFrame
  infer_instance

/-- The frame named by a normal-form index. -/
def NFFrame.toFrame {core : Core n p} {degree : ℕ} (r : NFFrame core degree) :
    Frame core degree :=
  ⟨FibreNormalForm.indexTarget r.1, r.2.1, r.2.2.1, r.2.2.2⟩

/-- **Every member is in the class of a normal-form frame's member**, at every
request.  Same proof as `Count.FibreNormalForm.exists_matching_normalForm`, read
through frames. -/
theorem exists_nfFrame {core : Core n p} {y : Fin p → ℚ} {degree : ℕ}
    (mem : FibreMember core y degree) :
    ∃ r : NFFrame core degree, ((NFFrame.toFrame r).member y).cls = mem.cls := by
  have hcard : Multiset.card mem.target.edges = p := by
    have hc := Fintype.card_congr mem.fullDim.labelling.targetEdge
    rw [Fintype.card_fin, Multiset.card_coe] at hc
    exact hc.symm
  obtain ⟨nf⟩ := TargetNormalForm.exists_normalForm mem.target
    mem.fullDim.targetConnected mem.fullDim.targetGenus p hcard
  refine ⟨⟨(⟨nf.parent, nf.parent_le⟩, nf.flip),
      (mem.transport (nf.datumIso mem.data)).data,
      ((mem.transport (nf.datumIso mem.data)).fullDim,
        (mem.transport (nf.datumIso mem.data)).ident)⟩, ?_⟩
  rw [show (NFFrame.toFrame (core := core) ⟨(⟨nf.parent, nf.parent_le⟩, nf.flip),
      (mem.transport (nf.datumIso mem.data)).data,
      ((mem.transport (nf.datumIso mem.data)).fullDim,
        (mem.transport (nf.datumIso mem.data)).ident)⟩).member y =
      mem.transport (nf.datumIso mem.data) from
    Frame.member_of (mem.transport (nf.datumIso mem.data))]
  exact cls_transport mem (nf.datumIso mem.data)

/-- **Generality over the finite normal-form family is generality over every
frame.**  The transfer is the coordinate field of `Count.MemberIso`: an
isomorphism over the core matches the coordinate vectors along a permutation of
the columns. -/
theorem exists_nf_coordsAt_eq {core : Core n p} {degree : ℕ} (y : Fin p → ℚ)
    (k : Frame core degree) (col : Fin p) :
    ∃ (r : NFFrame core degree) (col' : Fin p),
      (NFFrame.toFrame r).coordsAt y col' = k.coordsAt y col := by
  obtain ⟨r, hcls⟩ := exists_nfFrame (k.member y)
  obtain ⟨iso⟩ := FibreMember.cls_eq_cls_iff.mp hcls
  refine ⟨r, iso.column.symm col, ?_⟩
  have hco := iso.coords_column (iso.column.symm col)
  rw [Equiv.apply_symm_apply, Frame.coords_member, Frame.coords_member] at hco
  exact hco.symm

theorem coordsAt_ne_zero_of_nf {core : Core n p} {degree : ℕ} (y : Fin p → ℚ)
    (h : ∀ (r : NFFrame core degree) (col : Fin p),
      (NFFrame.toFrame r).coordsAt y col ≠ 0)
    (k : Frame core degree) (col : Fin p) : k.coordsAt y col ≠ 0 := by
  obtain ⟨r, col', hEq⟩ := exists_nf_coordsAt_eq y k col
  rw [← hEq]
  exact h r col'

/-- **Every wall parameter of every frame is one of the normal-form family's.**
The transfer is again the coordinate field of `Count.MemberIso`, applied
at the request reached at that parameter. -/
theorem mem_wallParams_nf {core : Core n p} {degree : ℕ} (y₀ y₁ : Fin p → ℚ)
    {k : Frame core degree} {col : Fin p} {t : ℚ} (h : k.IsWallParam y₀ y₁ col t) :
    t ∈ wallParams (fun r : NFFrame core degree ↦ NFFrame.toFrame r) y₀ y₁ := by
  obtain ⟨r, col', hEq⟩ :=
    exists_nf_coordsAt_eq (RationalAffineWall.segment y₀ y₁ t) k col
  exact ⟨r, col', hEq.trans h⟩

/-- **Finiteness of wall parameters over the whole fibre, as a set of
parameters.**  From a start general for the normal-form family, the set of
parameters at which *any* frame whatever loses a coordinate is finite. -/
theorem finite_allWallParams (core : Core n p) (degree : ℕ) (y₀ y₁ : Fin p → ℚ)
    (h : ∀ (r : NFFrame core degree) (col : Fin p),
      (NFFrame.toFrame r).coordsAt y₀ col ≠ 0) :
    {t : ℚ | ∃ (k : Frame core degree) (col : Fin p), k.IsWallParam y₀ y₁ col t}.Finite := by
  refine (finite_wallParams (fun r : NFFrame core degree ↦ NFFrame.toFrame r) y₀ y₁
    fun r col ↦ Or.inl (h r col)).subset ?_
  rintro t ⟨k, col, hk⟩
  exact mem_wallParams_nf y₀ y₁ hk

/-- **The hypothesis of the constancy theorems, discharged against a finite
set.**  "No wall parameter of the normal-form family between `u` and `v`" gives
"no wall parameter of any frame between `u` and `v`". -/
theorem no_wall_of_no_wall_nf (core : Core n p) (degree : ℕ) (y₀ y₁ : Fin p → ℚ)
    (u v : ℚ)
    (hno : ∀ t ∈ wallParams (fun r : NFFrame core degree ↦ NFFrame.toFrame r) y₀ y₁,
      ¬ (min u v ≤ t ∧ t ≤ max u v))
    (k : Frame core degree) (col : Fin p) (t : ℚ) (h1 : min u v ≤ t) (h2 : t ≤ max u v) :
    ¬ k.IsWallParam y₀ y₁ col t :=
  fun hw ↦ hno t (mem_wallParams_nf y₀ y₁ hw) ⟨h1, h2⟩

/-- **General requests for the whole fibre.**  Every positive orthant contains a
request avoiding every coordinate wall of every frame -- the wall hyperplanes of
every combinatorial type at once. -/
theorem exists_general_positive_fibre (core : Core n p) (degree : ℕ)
    (base : Fin p → ℚ) (hbase : ∀ i, 0 < base i) :
    ∃ y : Fin p → ℚ, (∀ i, 0 < y i) ∧
      ∀ (k : Frame core degree) (col : Fin p), k.coordsAt y col ≠ 0 := by
  classical
  let _ : Fintype (NFFrame core degree) := Fintype.ofFinite _
  obtain ⟨y, hpos, havoid⟩ :=
    exists_general_positive (fun r : NFFrame core degree ↦ NFFrame.toFrame r) base hbase
  exact ⟨y, hpos, coordsAt_ne_zero_of_nf y havoid⟩

/-- **Finiteness of wall triples over the whole fibre.**  Between two general
requests, the normal-form family has finitely many wall triples. -/
theorem finite_wallTriples_nf (core : Core n p) (degree : ℕ) (y₀ y₁ : Fin p → ℚ)
    (h : ∀ (k : Frame core degree) (col : Fin p), k.coordsAt y₀ col ≠ 0) :
    (wallTriples (fun r : NFFrame core degree ↦ NFFrame.toFrame r) y₀ y₁).Finite :=
  finite_wallTriples _ y₀ y₁ fun _r col ↦ Or.inl (h _ col)

/-! ## 7.  Non-vacuity: a caterpillar segment with one explicit wall parameter -/

theorem segment_zero (y₀ y₁ : Fin p → ℚ) :
    RationalAffineWall.segment y₀ y₁ 0 = y₀ := by
  funext i
  simp [RationalAffineWall.segment]

/-- **The caterpillar frame**, for every even genus `g = 2m + 2`.  It is the
frame of `Count.FibreCaterpillar.caterpillarMember`, which does not depend on
the request. -/
noncomputable def catFrame (m : ℕ) : Frame (FibreCaterpillar.catCore m) (m + 2) :=
  Frame.of (FibreCaterpillar.caterpillarMember m fun _ ↦ 1)

theorem coordsAt_catFrame (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    (catFrame m).coordsAt request = FibreCaterpillar.catCoords m request :=
  Frame.coordsAt_of (FibreCaterpillar.caterpillarMember m request)

theorem coordsAt_catFrame_apply (m : ℕ) (request : Fin (6 * m + 3) → ℚ)
    (slot : Fin (6 * m + 3)) :
    (catFrame m).coordsAt request slot =
      request slot / FibreCaterpillar.catDiag m slot := by
  rw [coordsAt_catFrame]
  rfl

/-- The all-ones request on the caterpillar core. -/
def catStart (m : ℕ) : Fin (6 * m + 3) → ℚ := fun _ ↦ 1

/-- The same request with the slot `j` driven through zero. -/
def catFinish (m : ℕ) (j : Fin (6 * m + 3)) : Fin (6 * m + 3) → ℚ :=
  Function.update (catStart m) j (-1)

theorem coordsAt_catStart (m : ℕ) (col : Fin (6 * m + 3)) :
    (catFrame m).coordsAt (catStart m) col = 1 / FibreCaterpillar.catDiag m col := by
  rw [coordsAt_catFrame_apply]
  rfl

theorem coordsAt_catFinish_self (m : ℕ) (j : Fin (6 * m + 3)) :
    (catFrame m).coordsAt (catFinish m j) j = -(1 / FibreCaterpillar.catDiag m j) := by
  rw [coordsAt_catFrame_apply, catFinish, Function.update_self]
  ring

theorem coordsAt_catFinish_ne (m : ℕ) {j col : Fin (6 * m + 3)} (h : col ≠ j) :
    (catFrame m).coordsAt (catFinish m j) col = 1 / FibreCaterpillar.catDiag m col := by
  rw [coordsAt_catFrame_apply, catFinish, Function.update_of_ne h]
  rfl

/-- **The explicit wall parameter.**  Driving the slot `j` of the all-ones
request through zero makes the `j`-th coordinate of the caterpillar member
vanish at the midpoint of the segment. -/
theorem catFrame_wallParam (m : ℕ) (j : Fin (6 * m + 3)) :
    (catFrame m).IsWallParam (catStart m) (catFinish m j) j (1 / 2) := by
  rw [Frame.isWallParam_iff, coordsAt_catStart, coordsAt_catFinish_self]
  ring

/-- It is the only parameter at which that coordinate vanishes. -/
theorem catFrame_wallParam_eq (m : ℕ) (j : Fin (6 * m + 3)) {t : ℚ}
    (h : (catFrame m).IsWallParam (catStart m) (catFinish m j) j t) : t = 1 / 2 := by
  rw [Frame.isWallParam_iff, coordsAt_catStart, coordsAt_catFinish_self] at h
  have hd := FibreCaterpillar.catDiag_ne_zero m j
  field_simp at h
  linarith

/-- No other column of the caterpillar frame meets a wall on this segment. -/
theorem catFrame_not_wallParam_of_ne (m : ℕ) {j col : Fin (6 * m + 3)} (h : col ≠ j)
    (t : ℚ) : ¬ (catFrame m).IsWallParam (catStart m) (catFinish m j) col t := by
  rw [Frame.isWallParam_iff, coordsAt_catStart, coordsAt_catFinish_ne m h, sub_self,
    mul_zero, add_zero]
  exact one_div_ne_zero (FibreCaterpillar.catDiag_ne_zero m col)

theorem catFrame_openAt_start (m : ℕ) : (catFrame m).OpenAt (catStart m) := by
  intro col
  rw [coordsAt_catStart]
  exact one_div_pos.mpr (FibreCaterpillar.catDiag_pos m col)

/-- **Constancy, exercised on the caterpillar.**  A quarter of the way along
the segment the frame is still open -- not by recomputing the coordinates, but
because `openAt_segment_iff_of_no_wall` applies: the only wall parameter is at
`1/2`. -/
theorem catFrame_openAt_quarter (m : ℕ) (j : Fin (6 * m + 3)) :
    (catFrame m).OpenAt
      (RationalAffineWall.segment (catStart m) (catFinish m j) (1 / 4)) := by
  refine ((catFrame m).openAt_segment_iff_of_no_wall (catStart m) (catFinish m j)
    0 (1 / 4) ?_).mp ?_
  · intro col t _ hmax hwall
    rw [max_eq_right (by norm_num : (0 : ℚ) ≤ 1 / 4)] at hmax
    by_cases hcol : col = j
    · subst hcol
      rw [catFrame_wallParam_eq m col hwall] at hmax
      norm_num at hmax
    · exact catFrame_not_wallParam_of_ne m hcol t hwall
  · rw [segment_zero]
    exact catFrame_openAt_start m

/-- Non-vacuity of the finite normal-form index. -/
theorem nonempty_nfFrame (m : ℕ) :
    Nonempty (NFFrame (FibreCaterpillar.catCore m) (m + 2)) :=
  ⟨(exists_nfFrame (FibreCaterpillar.caterpillarMember m (catStart m))).choose⟩

/-! ## 8.  The labelled fibre itself does not move with the request -/

open DraismaVargas.Count.Transport (DatumIso)

/-- Multiplying by a row- and column-permuted matrix. -/
theorem mulVec_submatrix {A B : Matrix (Fin p) (Fin p) ℚ} (ρ γ : Equiv.Perm (Fin p))
    (h : A = B.submatrix ρ γ) (w : Fin p → ℚ) (r : Fin p) :
    A.mulVec w r = B.mulVec (fun c ↦ w (γ.symm c)) (ρ r) := by
  rw [h]
  show ∑ c, B (ρ r) (γ c) * w c = ∑ c, B (ρ r) c * w (γ.symm c)
  exact Fintype.sum_equiv γ _ _ fun c ↦ by simp

namespace Frame

variable {core : Core n p} {degree : ℕ}

/-- **The coordinate vectors of two frames with isomorphic data correspond, at
every request.**  This is what makes the constancy between wall parameters a
statement about which members are *open*: the members themselves, and their
identifications, do not depend on the request at all. -/
theorem coordsAt_column (k l : Frame core degree) (iso : DatumIso k.data l.data)
    (hRow : ∀ path : StablePath k.data,
      l.ident.row (iso.stablePathEquiv k.fullDim.valid.1 path) = k.ident.row path)
    (y : Fin p → ℚ) (col : Fin p) :
    l.coordsAt y (l.fullDim.labelling.targetEdge.symm
        (iso.targetEdge (k.fullDim.labelling.targetEdge col))) = k.coordsAt y col := by
  classical
  set transported := transportLabelling iso k.fullDim.valid.1 k.fullDim.labelling with htrans
  set ρ : Equiv.Perm (Fin p) := l.fullDim.labelling.row.symm.trans transported.row with hρ
  set γ : Equiv.Perm (Fin p) :=
    l.fullDim.labelling.targetEdge.trans transported.targetEdge.symm with hγ
  have hsub : l.matrix = k.matrix.submatrix ρ γ := by
    rw [matrix, matrix_labelling_submatrix l.fullDim.labelling transported, hρ, hγ,
      matrix_transportLabelling iso k.fullDim.valid.1 k.fullDim.labelling]
    rfl
  have hslot : ∀ r : Fin p, l.slot r = k.slot (ρ r) := by
    intro r
    have h := hRow ((iso.stablePathEquiv k.fullDim.valid.1).symm
      (l.fullDim.labelling.row.symm r))
    rw [Equiv.apply_symm_apply] at h
    have hrowsym : k.fullDim.labelling.row.symm (ρ r) =
        (iso.stablePathEquiv k.fullDim.valid.1).symm (l.fullDim.labelling.row.symm r) := by
      rw [hρ, htrans]
      simp [transportLabelling]
    rw [slot, slot]
    show l.ident.row (l.fullDim.labelling.row.symm r) =
      k.ident.row (k.fullDim.labelling.row.symm (ρ r))
    rw [hrowsym]
    exact h
  have hsolve : l.matrix.mulVec (fun c ↦ k.coordsAt y (γ c)) = fun r ↦ y (l.slot r) := by
    funext r
    rw [mulVec_submatrix ρ γ hsub]
    have hcomp : (fun c ↦ k.coordsAt y (γ (γ.symm c))) = k.coordsAt y := by
      funext c
      rw [Equiv.apply_symm_apply]
    rw [hcomp, mulVec_coordsAt, hslot r]
  have huniq : (fun c ↦ k.coordsAt y (γ c)) = l.coordsAt y := by
    have hUnit : IsUnit l.matrix.det := l.isUnit_det
    have hInv : IsUnit l.matrix := (Matrix.isUnit_iff_isUnit_det _).mpr hUnit
    obtain ⟨inverse, hinv⟩ := hInv.exists_left_inv
    have hStep := congrArg (fun vector ↦ inverse.mulVec vector)
      (hsolve.trans (l.mulVec_coordsAt y).symm)
    simpa only [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] using hStep
  have hgamma : γ (l.fullDim.labelling.targetEdge.symm
      (iso.targetEdge (k.fullDim.labelling.targetEdge col))) = col := by
    rw [hγ, htrans]
    simp [transportLabelling]
  rw [← huniq]
  show k.coordsAt y (γ (l.fullDim.labelling.targetEdge.symm
    (iso.targetEdge (k.fullDim.labelling.targetEdge col)))) = k.coordsAt y col
  rw [hgamma]

end Frame

/-! ## 9.  Isomorphism of frames, and the request-independence of the quotient -/

/-- **An isomorphism of frames over the identity of the core**: exactly the data
of a `Count.MemberIso` with its coordinate field deleted.  No request
occurs in this definition. -/
structure FrameIso (k l : Frame core degree) where
  /-- The isomorphism of the two gluing data. -/
  datum : DatumIso k.data l.data
  /-- Over the identity of the core, on vertices. -/
  overCore_vertex : ∀ branch : BranchVertex k.data,
    l.ident.vertex (datum.branchVertexEquiv k.fullDim.valid.1 branch) =
      k.ident.vertex branch
  /-- Over the identity of the core, on slots. -/
  overCore_row : ∀ path : StablePath k.data,
    l.ident.row (datum.stablePathEquiv k.fullDim.valid.1 path) = k.ident.row path

/-- **The coordinate field is free.**  A frame isomorphism gives a member
isomorphism over *every* request. -/
noncomputable def FrameIso.toMemberIso {k l : Frame core degree} (fi : FrameIso k l)
    (y : Fin p → ℚ) : MemberIso (k.member y) (l.member y) :=
  MemberIso.ofDatumIso fi.datum fi.overCore_vertex fi.overCore_row
    fun col ↦ Frame.coordsAt_column k l fi.datum fi.overCore_row y col

/-- And conversely, a member isomorphism forgets to a frame isomorphism. -/
def FrameIso.ofMemberIso {k l : Frame core degree} {y : Fin p → ℚ}
    (iso : MemberIso (k.member y) (l.member y)) : FrameIso k l where
  datum := iso.datum
  overCore_vertex := iso.overCore_vertex
  overCore_row := iso.overCore_row

theorem isoOverCore_member_iff (k l : Frame core degree) (y : Fin p → ℚ) :
    IsoOverCore (k.member y) (l.member y) ↔ Nonempty (FrameIso k l) := by
  constructor
  · rintro ⟨iso⟩
    exact ⟨FrameIso.ofMemberIso iso⟩
  · rintro ⟨fi⟩
    exact ⟨fi.toMemberIso y⟩

/-- **The labelled fibre is the same type for every request.**  Its members are
the frames and its equivalence relation is `FrameIso`; only which classes are
*open* depends on the request. -/
noncomputable def fibreEquiv (core : Core n p) (degree : ℕ) (y y' : Fin p → ℚ) :
    Fibre core y degree ≃ Fibre core y' degree :=
  Quotient.congr
    ((Frame.memberEquiv core degree y).symm.trans (Frame.memberEquiv core degree y'))
    (by
      intro a b
      have ha := Frame.member_of a
      have hb := Frame.member_of b
      show IsoOverCore a b ↔ IsoOverCore ((Frame.of a).member y') ((Frame.of b).member y')
      rw [isoOverCore_member_iff, ← ha, ← hb, isoOverCore_member_iff, Frame.of_member,
        Frame.of_member])

@[simp] theorem fibreEquiv_cls (core : Core n p) (degree : ℕ) (y y' : Fin p → ℚ)
    (mem : FibreMember core y degree) :
    fibreEquiv core degree y y' mem.cls = ((Frame.of mem).member y').cls := rfl

/-- **Constancy between wall parameters, on the quotient.**  Between two
parameters with no wall parameter of any frame in between, the canonical
bijection of labelled fibres matches open classes with open classes: the
labelled fibre is constant there. -/
theorem open_fibreEquiv_iff_of_no_wall (core : Core n p) (degree : ℕ)
    (y₀ y₁ : Fin p → ℚ) (u v : ℚ)
    (hno : ∀ (k : Frame core degree) (col : Fin p) (t : ℚ), min u v ≤ t → t ≤ max u v →
      ¬ k.IsWallParam y₀ y₁ col t)
    (cls : Fibre core (RationalAffineWall.segment y₀ y₁ u) degree) :
    (fibreEquiv core degree (RationalAffineWall.segment y₀ y₁ u)
        (RationalAffineWall.segment y₀ y₁ v) cls).Open ↔ cls.Open := by
  obtain ⟨mem, rfl⟩ := FibreMember.cls_surjective cls
  rw [fibreEquiv_cls, Fibre.open_cls, Fibre.open_cls]
  have h := (Frame.of mem).openAt_segment_iff_of_no_wall y₀ y₁ u v
    fun col t ↦ hno (Frame.of mem) col t
  constructor
  · intro hv
    have h2 : ((Frame.of mem).member (RationalAffineWall.segment y₀ y₁ u)).Open := h.mpr hv
    rwa [Frame.member_of] at h2
  · intro hu
    refine h.mp ?_
    show ((Frame.of mem).member (RationalAffineWall.segment y₀ y₁ u)).Open
    rw [Frame.member_of]
    exact hu

/-! ## 10.  What the count sees -/

/-- **Odd multiplicity is a property of the frame**, so the canonical bijection
of labelled fibres preserves it. -/
theorem isOddClass_fibreEquiv (core : Core n p) (degree : ℕ) (y y' : Fin p → ℚ)
    (cls : Fibre core y degree) :
    IsOddClass (fibreEquiv core degree y y' cls) ↔ IsOddClass cls := by
  obtain ⟨mem, rfl⟩ := FibreMember.cls_surjective cls
  rw [fibreEquiv_cls, isOddClass_cls_iff', isOddClass_cls_iff']
  exact Iff.rfl

/-- **`Count.oddCount` does not depend on the request at all.**  It counts
*every* class of odd multiplicity, with no positivity condition, and both the
classes and their multiplicities are determined by the frames.  So the count
that matters is the one below, over the *open* classes. -/
theorem oddCount_eq_oddCount (core : Core n p) (degree : ℕ) (y y' : Fin p → ℚ) :
    oddCount core y degree = oddCount core y' degree :=
  Nat.card_congr (Equiv.subtypeEquiv (fibreEquiv core degree y y')
    fun cls ↦ (isOddClass_fibreEquiv core degree y y' cls).symm)

/-- **Constancy between wall parameters, in the form the count uses.**  Between
consecutive wall parameters the number of open classes of odd multiplicity is
constant. -/
theorem openOddCount_eq_of_no_wall (core : Core n p) (degree : ℕ)
    (y₀ y₁ : Fin p → ℚ) (u v : ℚ)
    (hno : ∀ (k : Frame core degree) (col : Fin p) (t : ℚ), min u v ≤ t → t ≤ max u v →
      ¬ k.IsWallParam y₀ y₁ col t) :
    openOddCount core (RationalAffineWall.segment y₀ y₁ u) degree =
      openOddCount core (RationalAffineWall.segment y₀ y₁ v) degree :=
  Nat.card_congr (Equiv.subtypeEquiv
    (fibreEquiv core degree (RationalAffineWall.segment y₀ y₁ u)
      (RationalAffineWall.segment y₀ y₁ v))
    fun cls ↦ and_congr
      (open_fibreEquiv_iff_of_no_wall core degree y₀ y₁ u v hno cls).symm
      (isOddClass_fibreEquiv core degree _ _ cls).symm)

/-! ## 11.  Why genericity is per frame and not across frames -/

/-- **Isomorphic frames have the same wall parameters.**  Their coordinate walls
agree along the induced permutation of the columns at every request, so their
crossing times agree; no choice of endpoints separates them. -/
theorem crossingTime_eq_of_frameIso {k l : Frame core degree} (fi : FrameIso k l)
    (y₀ y₁ : Fin p → ℚ) (col : Fin p) :
    (l.coordWall (l.fullDim.labelling.targetEdge.symm
        (fi.datum.targetEdge (k.fullDim.labelling.targetEdge col)))).crossingTime y₀ y₁ =
      (k.coordWall col).crossingTime y₀ y₁ := by
  simp only [RationalAffineWall.crossingTime, Frame.eval_coordWall,
    Frame.coordsAt_column k l fi.datum fi.overCore_row]

/-- **So a family-wide `SimpleAlong` is unavailable.**  Already a family that
repeats a frame has two distinct indices with equal coordinate walls, whatever
the endpoints are.  This is why `exists_generic_start` states simplicity one
frame at a time. -/
theorem not_simpleAlong_of_frames_eq {ι : Type} [Fintype ι]
    (frames : ι → Frame core degree) (y₀ y₁ : Fin p → ℚ) {i j : ι} (hne : i ≠ j)
    (heq : frames i = frames j) (hp : 0 < p) :
    ¬ RationalAffineWall.SimpleAlong
        (fun x : ι × Fin p ↦ (frames x.1).coordWall x.2) y₀ y₁ := by
  intro hsimple
  have hEval : ((frames i).coordWall ⟨0, hp⟩).crossingTime y₀ y₁ =
      ((frames j).coordWall ⟨0, hp⟩).crossingTime y₀ y₁ := by rw [heq]
  have hpair : (i, (⟨0, hp⟩ : Fin p)) = (j, (⟨0, hp⟩ : Fin p)) := hsimple hEval
  exact hne (congrArg Prod.fst hpair)

end DraismaVargas.Count.SegmentWalls









