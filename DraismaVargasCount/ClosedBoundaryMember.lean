import DraismaVargasCount.StepSupplyReduction
import DraismaVargasCount.GeometricCount

/-!
# An odd closed member at every non-negative request

`CountSchedule.C34 m` says: over every connected cubic core of genus `2m + 2`, at every
*general positive* request, the number of open classes of odd multiplicity is odd.  The
endgame needs a consequence of it at requests that need not be general and need not be
strictly positive: a member of the fibre whose coordinate vector `z` is **non-negative**
(`FibreMember.Closed`) and whose multiplicity is odd.

This file proves that consequence from `CountSchedule.C34 m`, in both halves, uniformly in
`m`.  At genus six the hypothesis is `Assembly.c34_genusSix` (step 4 of the assembly), and the
conclusion is the entry point of the endgame (step 5).

## The two halves

* `exists_open_hasOddMult_of_general` / `exists_closed_hasOddMult_of_general` --
  the statement at a **general positive** request.  This is the easy half: the conclusion
  of `CountSchedule.C34` is `Odd (openOddCount …)`, an odd natural number is positive, and
  `GeometricCount.exists_open_hasOddMult_of_openOddCount_pos` turns positivity
  of the count into an actual member.  `FibreMember.Closed.of_open` then weakens
  `Open` (`0 < z`) to `Closed` (`0 ≤ z`).
* `exists_closed_hasOddMult_of_nonneg` -- the statement at **every** request with
  `0 ≤ y`, general or not, boundary or not.  One might expect this half to need a limit
  argument: general requests `y_n → y`, finiteness of types, continuity of `A_φ⁻¹`.

## The boundary argument is finite, not analytic

The second half needs no limit argument, because two facts make the whole thing a
one-point argument on a single rational segment:

* `SegmentWalls.Frame.coordsAt_segment` -- each coordinate of each frame is an
  **affine** function of the segment parameter.  Not merely continuous: affine,
  with rational coefficients.
* `SegmentWalls.finite_allWallParams` -- along a segment whose *start* is
  general, the set of parameters at which **any** frame whatever loses a
  coordinate is finite.  (Its proof is the normal-form reduction: the finite
  index `SegmentWalls.NFFrame` meets every coordinate of every frame.)

So: let `w` be a general positive request (`exists_general_positive_fibre`), let `y ≥ 0` be
arbitrary, and run the segment `w → y`.  Only
finitely many parameters are walls, so there is a single `t₀ < 1` lying above
every wall parameter below `1`; the request at `t₀` is strictly positive
(a positive convex combination of `w > 0` and `y ≥ 0`) and general, so
`CountSchedule.C34` applies there and hands back an open member of odd multiplicity.  Its
frame `k` -- replaced by a normal-form frame only for tidiness, not for finiteness -- is
then open at `t₀`, and `Frame.pos_of_pos_of_no_wall` carries that positivity all
the way to the endpoint `t = 1`, i.e. to `y` itself, **unless** a wall sits at
`t = 1`.  A wall at `t = 1` is exactly `k.coordsAt y col = 0`, which is not a
counterexample to `0 ≤ k.coordsAt y col` but an instance of it.  That is the
whole argument, and it is why `Closed` and not `Open` is what survives.

No sequence, no completion of `ℚ`, no compactness, and no pigeonhole over the
frames is used.

## What is not proved here

* **`CountSchedule.C34 m` is a hypothesis of every theorem in this file.**  It fails at
  `m = 1` (see the warning on the definition); at genus six (`m = 2`) it is
  `Assembly.c34_genusSix`.
* Nothing here produces a member over a `Spec` at the `Spec`'s own integral
  request.
* Nothing here says the closed member's coordinates are integral, or that its
  frame is any particular combinatorial type.
* `absMult` is a function of the frame alone
  (`SegmentWalls.Frame.absMult_member`), so the multiplicity transported to the
  endpoint is literally the same number; the invariance of `absMult` under isomorphism of
  members is not used.
-/

namespace DraismaVargas.Count.ClosedBoundaryMember

open DraismaVargas.Infrastructure
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame NFFrame)

variable {m : ℕ}

/-! ## 1.  The cell at a general positive request -/

/-- **The easy half, before weakening to the closed cone.**  The odd count of
`CountSchedule.C34` is in particular a positive count, and a positive geometric open odd
count is an actual open member of odd multiplicity. -/
theorem exists_open_hasOddMult_of_general (hC34 : CountSchedule.C34 m)
    {n p : ℕ} (core : Core n p) (hcubic : core.Cubic) (hconn : core.Connected)
    (hgenus : p + 1 - n = 2 * m + 2) (y : Fin p → ℚ) (hypos : ∀ i, 0 < y i)
    (hgen : ∀ (k : Frame core (m + 2)) (col : Fin p), k.coordsAt y col ≠ 0) :
    ∃ member : FibreMember core y (m + 2), member.Open ∧ member.HasOddMult := by
  have hodd := hC34 core hcubic hconn hgenus y hypos hgen
  refine GeometricFibre.exists_open_hasOddMult_of_openOddCount_pos ?_
  rcases Nat.eq_zero_or_pos (GeometricFibre.openOddCount core y (m + 2)) with hzero | hpos
  · rw [hzero] at hodd
    exact absurd hodd (by simp)
  · exact hpos

/-- **An odd closed member at a general positive request.** -/
theorem exists_closed_hasOddMult_of_general (hC34 : CountSchedule.C34 m)
    {n p : ℕ} (core : Core n p) (hcubic : core.Cubic) (hconn : core.Connected)
    (hgenus : p + 1 - n = 2 * m + 2) (y : Fin p → ℚ) (hypos : ∀ i, 0 < y i)
    (hgen : ∀ (k : Frame core (m + 2)) (col : Fin p), k.coordsAt y col ≠ 0) :
    ∃ member : FibreMember core y (m + 2), member.Closed ∧ member.HasOddMult := by
  obtain ⟨member, hOpen, hOdd⟩ :=
    exists_open_hasOddMult_of_general hC34 core hcubic hconn hgenus y hypos hgen
  exact ⟨member, FibreMember.Closed.of_open hOpen, hOdd⟩

/-! ## 2.  The cell at the boundary of the cone -/

/-- **An odd closed member at every non-negative request**, from `CountSchedule.C34`.  No
positivity of the request, no generality of the request.  The coordinate vector of the
member produced is non-negative, and its multiplicity is odd. -/
theorem exists_closed_hasOddMult_of_nonneg (hC34 : CountSchedule.C34 m)
    {n p : ℕ} (core : Core n p) (hcubic : core.Cubic) (hconn : core.Connected)
    (hgenus : p + 1 - n = 2 * m + 2) (y : Fin p → ℚ) (hy : ∀ i, 0 ≤ y i) :
    ∃ member : FibreMember core y (m + 2), member.Closed ∧ member.HasOddMult := by
  classical
  obtain ⟨w, hwpos, hwgen⟩ :=
    SegmentWalls.exists_general_positive_fibre core (m + 2) (fun _ ↦ 1) fun _ ↦ one_pos
  -- The finitely many parameters at which some frame loses a coordinate.
  have hBfin : {t : ℚ | ∃ (k : Frame core (m + 2)) (col : Fin p),
      k.IsWallParam w y col t}.Finite :=
    SegmentWalls.finite_allWallParams core (m + 2) w y fun r col ↦ hwgen (NFFrame.toFrame r) col
  have hBltfin : ({t : ℚ | ∃ (k : Frame core (m + 2)) (col : Fin p),
      k.IsWallParam w y col t} ∩ Set.Iio (1 : ℚ)).Finite := hBfin.inter_of_left _
  -- A parameter `t₀ < 1` above every wall parameter below `1`.
  set T : Finset ℚ := insert (0 : ℚ) hBltfin.toFinset with hT
  have hTne : T.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  have hM0 : (0 : ℚ) ≤ T.max' hTne := Finset.le_max' T 0 (Finset.mem_insert_self _ _)
  have hM1 : T.max' hTne < 1 := by
    rw [Finset.max'_lt_iff]
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha'
    · norm_num
    · exact ((Set.Finite.mem_toFinset _).mp ha').2
  set t₀ : ℚ := (T.max' hTne + 1) / 2 with ht₀
  have ht₀M : T.max' hTne < t₀ := by rw [ht₀]; linarith
  have ht₀one : t₀ < 1 := by rw [ht₀]; linarith
  have ht₀pos : 0 < t₀ := by rw [ht₀]; linarith
  have hle : ∀ (k : Frame core (m + 2)) (col : Fin p) (t : ℚ),
      k.IsWallParam w y col t → t < 1 → t ≤ T.max' hTne := fun k col t hw ht ↦
    Finset.le_max' T t
      (Finset.mem_insert_of_mem ((Set.Finite.mem_toFinset _).mpr ⟨⟨k, col, hw⟩, ht⟩))
  -- At `t₀` the request is strictly positive and general, so `hC34` applies.
  have hreqpos : ∀ i, 0 < RationalAffineWall.segment w y t₀ i := by
    intro i
    have hrw : RationalAffineWall.segment w y t₀ i = (1 - t₀) * w i + t₀ * y i := by
      simp only [RationalAffineWall.segment]; ring
    rw [hrw]
    have h1 : 0 < (1 - t₀) * w i := mul_pos (by linarith) (hwpos i)
    have h2 : 0 ≤ t₀ * y i := mul_nonneg ht₀pos.le (hy i)
    linarith
  have hreqgen : ∀ (k : Frame core (m + 2)) (col : Fin p),
      k.coordsAt (RationalAffineWall.segment w y t₀) col ≠ 0 := by
    intro k col hzero
    exact absurd (hle k col t₀ hzero ht₀one) (not_le.mpr ht₀M)
  obtain ⟨mem, hmemOpen, hmemOdd⟩ := exists_open_hasOddMult_of_general hC34 core hcubic hconn
    hgenus (RationalAffineWall.segment w y t₀) hreqpos hreqgen
  -- Read that member through a normal-form frame, then evaluate the frame at `y`.
  obtain ⟨r, hr⟩ := SegmentWalls.exists_nfFrame mem
  set k : Frame core (m + 2) := NFFrame.toFrame r with hk
  have hkOpen : ∀ col, 0 < k.coordsAt (RationalAffineWall.segment w y t₀) col := by
    have : (k.member (RationalAffineWall.segment w y t₀)).Open := by
      rw [← Fibre.open_cls, hr, Fibre.open_cls]; exact hmemOpen
    exact this
  have hkAbs : (k.member (RationalAffineWall.segment w y t₀)).absMult = mem.absMult := by
    rw [← GeometricFibre.absMult_cls, ← GeometricFibre.absMult_cls,
      ← GeometricFibre.ofStrict_cls, ← GeometricFibre.ofStrict_cls, hr]
  refine ⟨k.member y, ?_, ?_⟩
  · -- every coordinate at `y` is non-negative
    intro col
    by_contra hneg
    rw [not_le] at hneg
    have hcoord : k.coordsAt y col < 0 := hneg
    have hno : ∀ t, min t₀ 1 ≤ t → t ≤ max t₀ 1 → ¬ k.IsWallParam w y col t := by
      intro t hmin hmax hwall
      rw [min_eq_left ht₀one.le] at hmin
      rw [max_eq_right ht₀one.le] at hmax
      rcases lt_or_eq_of_le hmax with hlt | heq
      · exact absurd (hle k col t hwall hlt) (not_le.mpr (lt_of_lt_of_le ht₀M hmin))
      · rw [SegmentWalls.Frame.IsWallParam, heq, StepSupplyReduction.segment_one] at hwall
        exact absurd hwall (ne_of_lt hcoord)
    have hcarry := k.pos_of_pos_of_no_wall w y col t₀ 1 (hkOpen col) hno
    rw [StepSupplyReduction.segment_one] at hcarry
    exact absurd hcarry (not_lt.mpr hcoord.le)
  · -- the multiplicity is a function of the frame, so it does not move
    obtain ⟨j, hjodd, hjeq⟩ := hmemOdd
    exact ⟨j, hjodd, by rw [show (k.member y).absMult
      = (k.member (RationalAffineWall.segment w y t₀)).absMult from rfl, hkAbs, hjeq]⟩

/-- **An odd closed member at every non-negative request, at genus six.**
`CountSchedule.C34 2` is `Assembly.c34_genusSix` (step 4 of the assembly), so this is the
endgame's entry point: the request is an arbitrary non-negative rational length
vector on the slots, degenerate slots included.  `CorePencilCoverProducer` (step 5) consumes
it at the degenerate request of every graph's cubic model. -/
theorem genusSix_exists_closed_hasOddMult_of_nonneg (hC34 : CountSchedule.C34 2)
    {n p : ℕ} (core : Core n p) (hcubic : core.Cubic) (hconn : core.Connected)
    (hgenus : p + 1 - n = 6) (y : Fin p → ℚ) (hy : ∀ i, 0 ≤ y i) :
    ∃ member : FibreMember core y 4, member.Closed ∧ member.HasOddMult :=
  exists_closed_hasOddMult_of_nonneg hC34 core hcubic hconn (by omega) y hy

end DraismaVargas.Count.ClosedBoundaryMember
