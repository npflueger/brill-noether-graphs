module

public import DiagonalSecant.CountAtActual
public import DraismaVargasCount.ClosedBoundaryMember
public import GenusSixExistence.BrillNoetherRank.Tripod.ClosureFrame

@[expose] public section

/-!
# The closure on the tailed core: a closed full-type member of odd multiplicity

The segment argument is that of `Research/genus-six-brill-noether-rank.md` §6.4.

The closure is run **on the tailed core `H`**, not on the typed frames: the public segment-wall
machinery (`DraismaVargasCount/SegmentWalls.lean`, `ClosedBoundaryMember.lean`) is stated for
unmarked frames of a core, and `H` is a core. The typed statement is recovered afterwards by
restriction (`Restrict.lean`). This is the tripod's `ClosureFrame.exists_closed_oddClaw_of_package`
(`GenusSixExistence/BrillNoetherRank/Tripod/ClosureFrame.lean`) with

* the claw predicate replaced by `IsFullType` (a frame predicate, as `MemberIsClaw` is);
* the walls of the gadget replaced by the walls of `H` in degree `d`
  (`SegmentWalls.finite_allWallParams`);
* the base-request walls of `G̃` in degree four replaced by the walls of `Γ` in degree
  `d − a/2` at the merged request, pulled back along the linear map
  `yH ↦ mergeRequest s (core part of yH)` (`ClosureFrame.pullWall`, with a section as
  `ClosureFrame.liftRequest`), which is the drop clause `OnceDropGeneral`;
* no functionals `B` and no long legs;
* the parity input `ParityPackage` replaced by `CountAtActual.exists_open_oddFullType`.

The endpoint is `(tailed core s a).request y`: core part `y ≥ 0`, tails `1`. Along the segment
from a positive general start the tails stay positive, so `exists_open_oddFullType` applies at
the interior point, and the frame carried to `t = 1` is closed there.
-/

namespace DiagonalSecant

open DraismaVargas.Count DraismaVargas.Count.MarkedCount DraismaVargas.Count.MarkedCountGeneral
open DraismaVargas.Count.SegmentWalls (Frame NFFrame)
open DraismaVargas.Infrastructure
open Utilities.Certificate.ExplicitPotential (Core)
open GenusSixExistence.Tripod.Gadget (subdivide)

variable {n p : ℕ}

/-- The core part of a request on `H`. -/
noncomputable def corePart {core : Core n p} {s : Fin p} {a : ℕ} (yH : Fin (tailed core s a).P → ℚ) :
    Fin (p + 1) → ℚ :=
  fun i ↦ yH ((tailed core s a).coreSlot i)

/-- The linear map `yH ↦ mergeRequest s (corePart yH)` along which the drop walls are pulled
back. -/
noncomputable def dropMap (core : Core n p) (s : Fin p) (a : ℕ) :
    (Fin (tailed core s a).P → ℚ) →ₗ[ℚ] (Fin p → ℚ) where
  toFun yH := mergeRequest s (corePart yH)
  map_add' x z := by
    funext i
    simp only [mergeRequest, corePart, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    funext i
    simp only [mergeRequest, corePart, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

@[simp] theorem dropMap_apply (core : Core n p) (s : Fin p) (a : ℕ)
    (yH : Fin (tailed core s a).P → ℚ) : dropMap core s a yH = mergeRequest s (corePart yH) :=
  rfl

/-- **The merged segment is a segment**: `dropMap` is linear. -/
theorem dropMap_segment (core : Core n p) (s : Fin p) (a : ℕ)
    (x z : Fin (tailed core s a).P → ℚ) (t : ℚ) :
    dropMap core s a (RationalAffineWall.segment x z t) =
      RationalAffineWall.segment (dropMap core s a x) (dropMap core s a z) t := by
  rw [GenusSixExistence.Tripod.ClosureFrame.segment_eq,
    GenusSixExistence.Tripod.ClosureFrame.segment_eq, map_add, map_smul, map_sub]

/-- A section of `dropMap`: `z` on the old core slots, `0` on the new piece and the tails. -/
noncomputable def liftDrop (core : Core n p) (s : Fin p) (a : ℕ) (z : Fin p → ℚ) :
    Fin (tailed core s a).P → ℚ :=
  fun e ↦ Sum.elim (Fin.snoc z 0 : Fin (p + 1) → ℚ) (fun _ ↦ 0)
    ((tailed core s a).slotEquiv.symm e)

theorem dropMap_liftDrop (core : Core n p) (s : Fin p) (a : ℕ) (z : Fin p → ℚ) :
    dropMap core s a (liftDrop core s a z) = z := by
  have h : corePart (liftDrop core s a z) = (Fin.snoc z 0 : Fin (p + 1) → ℚ) := by
    funext i
    simp [corePart, liftDrop, Tailed.coreSlot]
  rw [dropMap_apply, h]
  funext i
  simp [mergeRequest]

/-- The walls the start must avoid: the coordinates of the normal-form frames of `H` in degree
`d`, and those of `Γ` in degree `d₀` pulled back along `dropMap`. -/
noncomputable def startWall (core : Core n p) (s : Fin p) (a d d₀ : ℕ) :
    (NFFrame (tailed core s a).H d × Fin (tailed core s a).P) ⊕ (NFFrame core d₀ × Fin p) →
      RationalAffineWall (Fin (tailed core s a).P)
  | Sum.inl x => (NFFrame.toFrame x.1).coordWall x.2
  | Sum.inr x => GenusSixExistence.Tripod.ClosureFrame.pullWall (dropMap core s a)
      ((NFFrame.toFrame x.1).coordWall x.2)

theorem startWall_proper (core : Core n p) (s : Fin p) (a d d₀ : ℕ) (x) :
    (startWall core s a d d₀ x).Proper := by
  rcases x with x | x
  · exact (NFFrame.toFrame x.1).coordWall_proper x.2
  · obtain ⟨z, hz⟩ := (NFFrame.toFrame x.1).coordWall_proper x.2
    refine ⟨liftDrop core s a z, ?_⟩
    show (GenusSixExistence.Tripod.ClosureFrame.pullWall (dropMap core s a)
      ((NFFrame.toFrame x.1).coordWall x.2)).eval (liftDrop core s a z) ≠ 0
    rw [GenusSixExistence.Tripod.ClosureFrame.eval_pullWall, dropMap_liftDrop]
    exact hz

/-- **The start of the segment**: a positive request on `H` general for `H` in degree `d` and
general for `Γ` in degree `d₀` at the merged request. -/
theorem exists_start (core : Core n p) (s : Fin p) (a d d₀ : ℕ) :
    ∃ w : Fin (tailed core s a).P → ℚ, (∀ i, 0 < w i) ∧
      (∀ (r : NFFrame (tailed core s a).H d) (col : Fin (tailed core s a).P),
        (NFFrame.toFrame r).coordsAt w col ≠ 0) ∧
      (∀ (r : NFFrame core d₀) (col : Fin p),
        (NFFrame.toFrame r).coordsAt (dropMap core s a w) col ≠ 0) := by
  classical
  let _ : Fintype (NFFrame (tailed core s a).H d) := Fintype.ofFinite _
  let _ : Fintype (NFFrame core d₀) := Fintype.ofFinite _
  obtain ⟨w, hpos, havoid⟩ :=
    RationalAffineWall.exists_avoids_preserving_positive (startWall core s a d d₀)
      SegmentWalls.coordinateWall (fun _ ↦ 1) (startWall_proper core s a d d₀)
      (by intro l; rw [SegmentWalls.eval_coordinateWall]; exact one_pos)
  refine ⟨w, fun i ↦ by simpa using hpos i, fun r col ↦ ?_, fun r col ↦ ?_⟩
  · have h := havoid (Sum.inl (r, col))
    rwa [show startWall core s a d d₀ (Sum.inl (r, col)) =
      (NFFrame.toFrame r).coordWall col from rfl, Frame.eval_coordWall] at h
  · have h := havoid (Sum.inr (r, col))
    rwa [show startWall core s a d d₀ (Sum.inr (r, col)) =
      GenusSixExistence.Tripod.ClosureFrame.pullWall (dropMap core s a)
        ((NFFrame.toFrame r).coordWall col) from rfl,
      GenusSixExistence.Tripod.ClosureFrame.eval_pullWall, Frame.eval_coordWall] at h

/-- **The closure on `H`** (the tripod's Theorem 6.3, one mark, no legs): at every request on
`H` whose core part is non-negative and whose tails are `1`, some member of `H` in degree `d` is
closed, has odd multiplicity, and is of full type. -/
theorem exists_closed_oddFullType_of_nonneg {core : Core n p} (hCubic : core.Cubic)
    (hConnected : core.Connected) {g : ℕ} (hg : p + 1 - n = g) (hg5 : 5 ≤ g) (s : Fin p)
    {a d : ℕ} (ha : 1 ≤ a) (hd : g + a + 2 = 2 * d) (hL : d ≤ g)
    (hOdd : Odd (markedFormula g d a)) (y : Fin (p + 1) → ℚ) (hy : ∀ i, 0 ≤ y i) :
    ∃ mem : FibreMember (tailed core s a).H ((tailed core s a).request y) d,
      mem.Closed ∧ mem.HasOddMult ∧
        IsFullType (tailed core s a) (tailed_markedCubic hCubic s) (Frame.of mem) := by
  classical
  have hc := tailed_markedCubic hCubic s
  set Y := (tailed core s a).request y with hY
  have hYnn : ∀ e, 0 ≤ Y e := by
    intro e
    rcases (tailed core s a).slot_cases e with ⟨i, rfl⟩ | ⟨j, t, rfl⟩
    · rw [hY, Tailed.request_coreSlot]; exact hy i
    · rw [hY, Tailed.request_tailSlot]; exact zero_le_one
  -- Step 1: the start.
  obtain ⟨w, hwpos, hwH, hwG⟩ := exists_start core s a d (d - a / 2)
  -- Step 2: finitely many walls on the segment.
  have hHfin : {t : ℚ | ∃ (k : Frame (tailed core s a).H d) (col : Fin (tailed core s a).P),
      k.IsWallParam w Y col t}.Finite :=
    SegmentWalls.finite_allWallParams _ _ w Y hwH
  have hGfin : {t : ℚ | ∃ (k : Frame core (d - a / 2)) (col : Fin p),
      k.IsWallParam (dropMap core s a w) (dropMap core s a Y) col t}.Finite :=
    SegmentWalls.finite_allWallParams _ _ _ _ hwG
  set Bad : Set ℚ := {t : ℚ | ∃ (k : Frame (tailed core s a).H d)
      (col : Fin (tailed core s a).P), k.IsWallParam w Y col t} ∪
    {t : ℚ | ∃ (k : Frame core (d - a / 2)) (col : Fin p),
      k.IsWallParam (dropMap core s a w) (dropMap core s a Y) col t} with hBad
  have hBadlt : (Bad ∩ Set.Iio (1 : ℚ)).Finite := (hHfin.union hGfin).inter_of_left _
  -- Step 3: the interior point `t₀ < 1`, above every wall below `1`.
  set T : Finset ℚ := insert (0 : ℚ) hBadlt.toFinset with hT
  have hTne : T.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  have hM1 : T.max' hTne < 1 := by
    rw [Finset.max'_lt_iff]
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb'
    · norm_num
    · exact ((Set.Finite.mem_toFinset _).mp hb').2
  have hM0 : (0 : ℚ) ≤ T.max' hTne := Finset.le_max' T 0 (Finset.mem_insert_self _ _)
  set t₀ : ℚ := (T.max' hTne + 1) / 2 with ht₀
  have ht₀M : T.max' hTne < t₀ := by rw [ht₀]; linarith
  have ht₀one : t₀ < 1 := by rw [ht₀]; linarith
  have ht₀pos : 0 < t₀ := by rw [ht₀]; linarith
  have hle : ∀ t, t ∈ Bad → t < 1 → t ≤ T.max' hTne := fun t hbad ht ↦
    Finset.le_max' T t (Finset.mem_insert_of_mem ((Set.Finite.mem_toFinset _).mpr ⟨hbad, ht⟩))
  have hnotBad : t₀ ∉ Bad := fun hbad ↦ absurd (hle t₀ hbad ht₀one) (not_le.mpr ht₀M)
  set y₀ := RationalAffineWall.segment w Y t₀ with hy₀
  have hreqpos : ∀ e, 0 < y₀ e := by
    intro e
    have hrw : y₀ e = (1 - t₀) * w e + t₀ * Y e := by
      simp only [hy₀, RationalAffineWall.segment]; ring
    rw [hrw]
    have h1 : 0 < (1 - t₀) * w e := mul_pos (by linarith) (hwpos e)
    have h2 : 0 ≤ t₀ * Y e := mul_nonneg ht₀pos.le (hYnn e)
    linarith
  -- Step 4: an open full-type member of odd multiplicity at `t₀`.
  have hHgen : ∀ (f : Frame (tailed core s a).H d) (col : Fin (tailed core s a).P),
      f.coordsAt y₀ col ≠ 0 := fun f col hzero ↦ hnotBad (Or.inl ⟨f, col, hzero⟩)
  have hDrop : OnceDropGeneral core s (d - a / 2) (corePart y₀) := by
    intro f col hzero
    have h : f.coordsAt (dropMap core s a y₀) col = 0 := hzero
    rw [hy₀, dropMap_segment] at h
    exact hnotBad (Or.inr ⟨f, col, h⟩)
  obtain ⟨mem, hmemOpen, hmemOdd, hFull⟩ := exists_open_oddFullType hCubic hConnected hg hg5 s
    ha hd hL hOdd (y := corePart y₀) (fun i ↦ hreqpos _) (yH := y₀) (fun _ ↦ rfl)
    (fun _ _ ↦ hreqpos _) hHgen hDrop
  -- Step 5: read it through its frame, and carry the frame to `t = 1`.
  set κ : Frame (tailed core s a).H d := Frame.of mem with hκ
  have hκOpen : ∀ col, 0 < κ.coordsAt y₀ col := by
    intro col
    rw [hκ, Frame.coordsAt_of]
    exact hmemOpen col
  refine ⟨κ.member Y, ?_,
    (GenusSixExistence.Tripod.ClosureFrame.hasOddMult_frame_member mem Y).mpr hmemOdd, hFull⟩
  intro col
  by_contra hneg
  rw [not_le] at hneg
  have hcoord : κ.coordsAt Y col < 0 := hneg
  have hno : ∀ t, min t₀ 1 ≤ t → t ≤ max t₀ 1 → ¬ κ.IsWallParam w Y col t := by
    intro t hmin hmax hwall
    rw [min_eq_left ht₀one.le] at hmin
    rw [max_eq_right ht₀one.le] at hmax
    rcases lt_or_eq_of_le hmax with hlt | heq
    · exact absurd (hle t (Or.inl ⟨κ, col, hwall⟩) hlt)
        (not_le.mpr (lt_of_lt_of_le ht₀M hmin))
    · rw [SegmentWalls.Frame.IsWallParam, heq, StepSupplyReduction.segment_one] at hwall
      exact absurd hwall (ne_of_lt hcoord)
  have hcarry := κ.pos_of_pos_of_no_wall w Y col t₀ 1 (hκOpen col) hno
  rw [StepSupplyReduction.segment_one] at hcarry
  exact absurd hcarry (not_lt.mpr hcoord.le)

end DiagonalSecant
