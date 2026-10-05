module

public import GenusSixExistence.BrillNoetherRank.Tripod.Classification
public import DraismaVargasCount.SegmentWalls
public import DraismaVargasCount.StepSupplyReduction

@[expose] public section

/-!
# The closure, by one segment

Prose proof: `Research/genus-six-brill-noether-rank.md`, §6.4 (The segment), Theorem 6.3 and its
steps 1–7, with the admissible requests of §6.3; section and statement numbers in this file
refer to that note. From the generic-point package
`Classification.ParityPackage core s`, at **every** non-negative request with long legs there is
a member over the gadget `Γ̃ = tripodCore core s` that is closed, of odd multiplicity, and a claw
member: `exists_closed_oddClaw_of_package`.

The proof is `ClosedBoundaryMember.exists_closed_hasOddMult_of_nonneg`
(`DraismaVargasCount/ClosedBoundaryMember.lean`) with three more families of walls on the
segment `y(t) = (1 - t) w + t y`:

* the coordinates of the frames of `G̃ = core` in degree four along the merged segment
  `baseRequest s (y t)` (`baseRequest` is linear, `baseRequest_segment`, so this is the segment
  from `baseRequest s w` to `baseRequest s y`, and `SegmentWalls.finite_allWallParams` applies
  to it once `baseRequest s w` is general);
* the functionals of the family `B` of the package, each affine in `t` and nonzero at `t = 0`,
  hence with at most one zero (`affine_zero_subsingleton`);
* the long-leg conditions, each affine in `t` and positive at `t = 1`, hence positive on some
  `(t_L, 1]` (`exists_threshold`).

The start `w` (`exists_start`) avoids the walls of `Γ̃`, the pulled-back walls of `G̃`
(`pullWall`, proper because `baseRequest` has a section, `baseRequest_liftRequest`) and the
functionals of `B`, by `RationalAffineWall.exists_avoids_preserving_positive`.

## The two frame facts

* **`IsClaw` is a frame predicate.** `MemberIsClaw mem` is by definition
  `TripodFrame.IsClaw (Frame.of mem)`, and `Frame.of (k.member y) = k` is `rfl`, so a member read
  through its frame at another request is a claw member exactly when the original one is
  (`memberIsClaw_frame_member`, `Iff.rfl`).
* **`absMult` is a frame function.** `FibreMember.absMult` is `fdAbsMult` of the
  full-dimensionality receipt, which the frame carries (`hasOddMult_frame_member`, `Iff.rfl`).
-/

namespace GenusSixExistence.Tripod.ClosureFrame

open DraismaVargas.Count
open DraismaVargas.Infrastructure
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame NFFrame)
open Gadget Classification

variable {n p : ℕ}

/-! ## 1.  The two frame facts -/

/-- **`IsClaw` is a frame predicate**: a member read through its frame at another request is a
claw member exactly when the original one is. -/
theorem memberIsClaw_frame_member {core : Core n p} {s : MarkSlots p} {degree : ℕ}
    {y : Fin (p + 1 + 1 + 1 + 3) → ℚ} (mem : FibreMember (tripodCore core s) y degree)
    (y' : Fin (p + 1 + 1 + 1 + 3) → ℚ) :
    MemberIsClaw ((Frame.of mem).member y') ↔ MemberIsClaw mem :=
  Iff.rfl

/-- **`absMult` is a frame function**: a member read through its frame at another request has
odd multiplicity exactly when the original one does. -/
theorem hasOddMult_frame_member {m q degree : ℕ} {core : Core m q} {y : Fin q → ℚ}
    (mem : FibreMember core y degree) (y' : Fin q → ℚ) :
    ((Frame.of mem).member y').HasOddMult ↔ mem.HasOddMult :=
  Iff.rfl

/-! ## 2.  The base request is linear, and has a section -/

theorem mergeRequest_add (e : Fin p) (x z : Fin (p + 1) → ℚ) :
    mergeRequest e (x + z) = mergeRequest e x + mergeRequest e z := by
  funext i
  simp only [mergeRequest, Pi.add_apply]
  split_ifs <;> ring

theorem mergeRequest_smul (e : Fin p) (c : ℚ) (x : Fin (p + 1) → ℚ) :
    mergeRequest e (c • x) = c • mergeRequest e x := by
  funext i
  simp only [mergeRequest, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- `baseRequest s` as a linear map. -/
def baseRequestLinear (s : MarkSlots p) : (Fin (p + 1 + 1 + 1 + 3) → ℚ) →ₗ[ℚ] (Fin p → ℚ) where
  toFun := baseRequest s
  map_add' x z := by
    unfold baseRequest
    rw [show gPart (x + z) = gPart x + gPart z from rfl, mergeRequest_add, mergeRequest_add,
      mergeRequest_add]
  map_smul' c x := by
    unfold baseRequest
    rw [show gPart (c • x) = c • gPart x from rfl, RingHom.id_apply, mergeRequest_smul,
      mergeRequest_smul, mergeRequest_smul]

@[simp] theorem baseRequestLinear_apply (s : MarkSlots p) (x : Fin (p + 1 + 1 + 1 + 3) → ℚ) :
    baseRequestLinear s x = baseRequest s x := rfl

theorem segment_eq {m : ℕ} (x z : Fin m → ℚ) (t : ℚ) :
    RationalAffineWall.segment x z t = x + t • (z - x) := by
  funext i
  simp [RationalAffineWall.segment]

/-- **The merged segment is a segment**: merging the split slots commutes with the segment. -/
theorem baseRequest_segment (s : MarkSlots p) (x z : Fin (p + 1 + 1 + 1 + 3) → ℚ) (t : ℚ) :
    baseRequest s (RationalAffineWall.segment x z t) =
      RationalAffineWall.segment (baseRequest s x) (baseRequest s z) t := by
  rw [segment_eq, segment_eq, ← baseRequestLinear_apply, map_add, map_smul, map_sub]
  rfl

theorem mergeRequest_snoc_zero (e : Fin p) (z : Fin p → ℚ) :
    mergeRequest e (Fin.snoc z 0 : Fin (p + 1) → ℚ) = z := by
  funext i
  simp [mergeRequest]

/-- A section of `baseRequest s`: put `z` on the old slots and `0` on the new pieces and legs. -/
def liftRequest (z : Fin p → ℚ) : Fin (p + 1 + 1 + 1 + 3) → ℚ :=
  Fin.addCases (Fin.snoc (Fin.snoc (Fin.snoc z 0 : Fin (p + 1) → ℚ) 0 : Fin (p + 1 + 1) → ℚ) 0 :
    Fin (p + 1 + 1 + 1) → ℚ) fun _ ↦ 0

theorem baseRequest_liftRequest (s : MarkSlots p) (z : Fin p → ℚ) :
    baseRequest s (liftRequest z) = z := by
  have hg : gPart (liftRequest z) = (Fin.snoc (Fin.snoc (Fin.snoc z 0 : Fin (p + 1) → ℚ) 0 :
      Fin (p + 1 + 1) → ℚ) 0 : Fin (p + 1 + 1 + 1) → ℚ) := by
    funext i
    simp [gPart, liftRequest]
  rw [baseRequest, hg, mergeRequest_snoc_zero, mergeRequest_snoc_zero, mergeRequest_snoc_zero]

/-! ## 3.  Walls pulled back along a linear map -/

/-- The wall `x ↦ wall (L x)`. -/
noncomputable def pullWall {m q : ℕ} (L : (Fin m → ℚ) →ₗ[ℚ] (Fin q → ℚ))
    (wall : RationalAffineWall (Fin q)) : RationalAffineWall (Fin m) where
  coefficient := Matrix.vecMul wall.coefficient (LinearMap.toMatrix' L)
  constant := wall.constant

theorem eval_pullWall {m q : ℕ} (L : (Fin m → ℚ) →ₗ[ℚ] (Fin q → ℚ))
    (wall : RationalAffineWall (Fin q)) (x : Fin m → ℚ) :
    (pullWall L wall).eval x = wall.eval (L x) := by
  have h := Matrix.dotProduct_mulVec wall.coefficient (LinearMap.toMatrix' L) x
  rw [LinearMap.toMatrix'_mulVec] at h
  simp only [RationalAffineWall.eval, pullWall]
  exact congrArg (· + wall.constant) h.symm

/-- The wall of a functional `b`, `x ↦ ∑ i, b i * x i`. -/
def functionalWall {m : ℕ} (b : Fin m → ℚ) : RationalAffineWall (Fin m) where
  coefficient := b
  constant := 0

@[simp] theorem eval_functionalWall {m : ℕ} (b x : Fin m → ℚ) :
    (functionalWall b).eval x = ∑ i, b i * x i := by
  simp [functionalWall, RationalAffineWall.eval]

/-! ## 4.  Affine functions of the segment parameter -/

theorem sum_mul_segment {m : ℕ} (b x z : Fin m → ℚ) (t : ℚ) :
    ∑ i, b i * RationalAffineWall.segment x z t i =
      ∑ i, b i * x i + t * (∑ i, b i * z i - ∑ i, b i * x i) := by
  have h := RationalAffineWall.eval_segment (functionalWall b) x z t
  simpa using h

theorem sum_segment {m : ℕ} (x z : Fin m → ℚ) (t : ℚ) :
    ∑ i, RationalAffineWall.segment x z t i = ∑ i, x i + t * (∑ i, z i - ∑ i, x i) := by
  simpa using sum_mul_segment (fun _ ↦ 1) x z t

/-- An affine function of `t`, nonzero at `t = 0`, has at most one zero. -/
theorem affine_zero_subsingleton {a b : ℚ} (ha : a ≠ 0) :
    {t : ℚ | a + t * (b - a) = 0}.Subsingleton := by
  intro t ht u hu
  simp only [Set.mem_ofPred_eq] at ht hu
  have hsub : (t - u) * (b - a) = 0 := by linear_combination ht - hu
  rcases mul_eq_zero.mp hsub with h | h
  · linarith
  · exfalso
    rw [h, mul_zero, add_zero] at ht
    exact ha ht

/-- An affine function of `t`, positive at `t = 1`, is positive on some `(t_L, 1]`. -/
theorem exists_threshold {a b : ℚ} (hb : 0 < b) :
    ∃ tL : ℚ, tL < 1 ∧ ∀ t, tL < t → t ≤ 1 → 0 < a + t * (b - a) := by
  by_cases ha : 0 ≤ a
  · refine ⟨0, by norm_num, fun t ht0 ht1 ↦ ?_⟩
    have h1 : 0 ≤ (1 - t) * a := mul_nonneg (by linarith) ha
    have h2 : 0 < t * b := mul_pos ht0 hb
    linarith
  · push Not at ha
    have hba : 0 < b - a := by linarith
    refine ⟨-a / (b - a), ?_, fun t ht _ ↦ ?_⟩
    · rw [div_lt_one hba]
      linarith
    · rw [div_lt_iff₀ hba] at ht
      linarith

/-- The long-leg slack of leg `k`, `ℓ_k - 4 L(y_G)`, along the segment. -/
theorem legSlack_segment (s : MarkSlots p) (x z : Fin (p + 1 + 1 + 1 + 3) → ℚ) (t : ℚ)
    (k : Fin 3) :
    legLength (RationalAffineWall.segment x z t) k -
        4 * ∑ i, baseRequest s (RationalAffineWall.segment x z t) i =
      (legLength x k - 4 * ∑ i, baseRequest s x i) +
        t * ((legLength z k - 4 * ∑ i, baseRequest s z i) -
          (legLength x k - 4 * ∑ i, baseRequest s x i)) := by
  rw [baseRequest_segment, sum_segment]
  simp only [legLength, RationalAffineWall.segment]
  ring

/-! ## 5.  The start of the segment -/

/-- The walls the start must avoid: the coordinates of the normal-form frames of `Γ̃`, those of
`G̃` pulled back along `baseRequest s`, and the functionals of `B`. -/
noncomputable def startWall (core : Core n p) (s : MarkSlots p)
    (B : Finset (Fin (p + 1 + 1 + 1 + 3) → ℚ)) :
    (NFFrame (tripodCore core s) (3 + 2) × Fin (p + 1 + 1 + 1 + 3)) ⊕
        (NFFrame core (2 + 2) × Fin p) ⊕ B → RationalAffineWall (Fin (p + 1 + 1 + 1 + 3))
  | Sum.inl x => (NFFrame.toFrame x.1).coordWall x.2
  | Sum.inr (Sum.inl x) => pullWall (baseRequestLinear s) ((NFFrame.toFrame x.1).coordWall x.2)
  | Sum.inr (Sum.inr b) => functionalWall b.1

theorem startWall_proper (core : Core n p) (s : MarkSlots p)
    (B : Finset (Fin (p + 1 + 1 + 1 + 3) → ℚ)) (hB : ∀ b ∈ B, b ≠ 0) (x) :
    (startWall core s B x).Proper := by
  rcases x with x | x | b
  · exact (NFFrame.toFrame x.1).coordWall_proper x.2
  · obtain ⟨z, hz⟩ := (NFFrame.toFrame x.1).coordWall_proper x.2
    refine ⟨liftRequest z, ?_⟩
    show (pullWall (baseRequestLinear s) ((NFFrame.toFrame x.1).coordWall x.2)).eval
      (liftRequest z) ≠ 0
    rw [eval_pullWall, baseRequestLinear_apply, baseRequest_liftRequest]
    exact hz
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp (hB b.1 b.2)
    exact RationalAffineWall.proper_of_coefficient_ne_zero (functionalWall b.1) (i := i) hi

/-- **The start** (Theorem 6.3, step 1): a positive request general for `Γ̃` in degree five,
whose base request is general for `G̃` in degree four, off every functional of `B`. -/
theorem exists_start (core : Core n p) (s : MarkSlots p)
    (B : Finset (Fin (p + 1 + 1 + 1 + 3) → ℚ)) (hB : ∀ b ∈ B, b ≠ 0) :
    ∃ w : Fin (p + 1 + 1 + 1 + 3) → ℚ, (∀ i, 0 < w i) ∧
      (∀ (r : NFFrame (tripodCore core s) (3 + 2)) (col : Fin (p + 1 + 1 + 1 + 3)),
        (NFFrame.toFrame r).coordsAt w col ≠ 0) ∧
      (∀ (r : NFFrame core (2 + 2)) (col : Fin p),
        (NFFrame.toFrame r).coordsAt (baseRequest s w) col ≠ 0) ∧
      (∀ b ∈ B, ∑ i, b i * w i ≠ 0) := by
  classical
  let _ : Fintype (NFFrame (tripodCore core s) (3 + 2)) := Fintype.ofFinite _
  let _ : Fintype (NFFrame core (2 + 2)) := Fintype.ofFinite _
  obtain ⟨w, hpos, havoid⟩ :=
    RationalAffineWall.exists_avoids_preserving_positive (startWall core s B)
      SegmentWalls.coordinateWall (fun _ ↦ 1) (startWall_proper core s B hB)
      (by intro l; rw [SegmentWalls.eval_coordinateWall]; exact one_pos)
  refine ⟨w, fun i ↦ by simpa using hpos i, fun r col ↦ ?_, fun r col ↦ ?_, fun b hb ↦ ?_⟩
  · have h := havoid (Sum.inl (r, col))
    rwa [show startWall core s B (Sum.inl (r, col)) = (NFFrame.toFrame r).coordWall col from rfl,
      Frame.eval_coordWall] at h
  · have h := havoid (Sum.inr (Sum.inl (r, col)))
    rwa [show startWall core s B (Sum.inr (Sum.inl (r, col))) =
      pullWall (baseRequestLinear s) ((NFFrame.toFrame r).coordWall col) from rfl,
      eval_pullWall, baseRequestLinear_apply, Frame.eval_coordWall] at h
  · have h := havoid (Sum.inr (Sum.inr ⟨b, hb⟩))
    rwa [show startWall core s B (Sum.inr (Sum.inr ⟨b, hb⟩)) = functionalWall b from rfl,
      eval_functionalWall] at h

/-! ## 6.  The closure -/

/-- **The closure** (Theorem 6.3). From the generic-point package, at every non-negative
request on the gadget with long legs there is a member that is closed (`z ≥ 0`), has odd
multiplicity, and is a claw member. -/
theorem exists_closed_oddClaw_of_package {n p : ℕ} (core : Core n p) (s : MarkSlots p)
    (hP : ParityPackage core s) (y : Fin (p + 1 + 1 + 1 + 3) → ℚ) (hy : ∀ i, 0 ≤ y i)
    (hlong : LongLegs s y) :
    ∃ mem : FibreMember (tripodCore core s) y (3 + 2),
      mem.Closed ∧ mem.HasOddMult ∧ MemberIsClaw mem := by
  classical
  obtain ⟨B, hB, hpack⟩ := hP
  -- Step 1: the start.
  obtain ⟨w, hwpos, hwΓ, hwG, hwB⟩ := exists_start core s B hB
  -- Step 2: finitely many walls on the segment.
  have hΓfin : {t : ℚ | ∃ (k : Frame (tripodCore core s) (3 + 2))
      (col : Fin (p + 1 + 1 + 1 + 3)), k.IsWallParam w y col t}.Finite :=
    SegmentWalls.finite_allWallParams _ _ w y hwΓ
  have hGfin : {t : ℚ | ∃ (k : Frame core (2 + 2)) (col : Fin p),
      k.IsWallParam (baseRequest s w) (baseRequest s y) col t}.Finite :=
    SegmentWalls.finite_allWallParams _ _ _ _ hwG
  have hBfin : {t : ℚ | ∃ b ∈ B, ∑ i, b i * RationalAffineWall.segment w y t i = 0}.Finite := by
    refine (B.finite_toSet.biUnion fun b hb ↦
      (affine_zero_subsingleton (b := ∑ i, b i * y i) (hwB b hb)).finite).subset ?_
    rintro t ⟨b, hb, ht⟩
    refine Set.mem_biUnion hb ?_
    show _ = 0
    rw [← sum_mul_segment]
    exact ht
  set Bad : Set ℚ := {t : ℚ | ∃ (k : Frame (tripodCore core s) (3 + 2))
      (col : Fin (p + 1 + 1 + 1 + 3)), k.IsWallParam w y col t} ∪
    {t : ℚ | ∃ (k : Frame core (2 + 2)) (col : Fin p),
      k.IsWallParam (baseRequest s w) (baseRequest s y) col t} ∪
    {t : ℚ | ∃ b ∈ B, ∑ i, b i * RationalAffineWall.segment w y t i = 0} with hBad
  have hBadlt : (Bad ∩ Set.Iio (1 : ℚ)).Finite :=
    ((hΓfin.union hGfin).union hBfin).inter_of_left _
  -- Step 3: long legs near `t = 1`.
  have hleg : ∀ k : Fin 3, ∃ tL : ℚ, tL < 1 ∧ ∀ t, tL < t → t ≤ 1 →
      4 * ∑ i, baseRequest s (RationalAffineWall.segment w y t) i <
        legLength (RationalAffineWall.segment w y t) k := by
    intro k
    obtain ⟨tL, htL, hpos⟩ := exists_threshold
      (a := legLength w k - 4 * ∑ i, baseRequest s w i)
      (b := legLength y k - 4 * ∑ i, baseRequest s y i) (by linarith [hlong k])
    refine ⟨tL, htL, fun t ht ht1 ↦ ?_⟩
    have h := hpos t ht ht1
    rw [← legSlack_segment] at h
    linarith
  choose tL htL1 htL using hleg
  -- Step 4: the interior point `t₀ < 1`, above every wall below `1` and every leg threshold.
  set T : Finset ℚ := insert (0 : ℚ) (hBadlt.toFinset ∪ Finset.univ.image tL) with hT
  have hTne : T.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  have hM1 : T.max' hTne < 1 := by
    rw [Finset.max'_lt_iff]
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha'
    · norm_num
    rcases Finset.mem_union.mp ha' with ha' | ha'
    · exact ((Set.Finite.mem_toFinset _).mp ha').2
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ha'
      exact htL1 k
  have hM0 : (0 : ℚ) ≤ T.max' hTne := Finset.le_max' T 0 (Finset.mem_insert_self _ _)
  set t₀ : ℚ := (T.max' hTne + 1) / 2 with ht₀
  have ht₀M : T.max' hTne < t₀ := by rw [ht₀]; linarith
  have ht₀one : t₀ < 1 := by rw [ht₀]; linarith
  have ht₀pos : 0 < t₀ := by rw [ht₀]; linarith
  have hle : ∀ t, t ∈ Bad → t < 1 → t ≤ T.max' hTne := fun t hbad ht ↦
    Finset.le_max' T t (Finset.mem_insert_of_mem (Finset.mem_union_left _
      ((Set.Finite.mem_toFinset _).mpr ⟨hbad, ht⟩)))
  have hnotBad : t₀ ∉ Bad := fun hbad ↦ absurd (hle t₀ hbad ht₀one) (not_le.mpr ht₀M)
  have hlegt₀ : ∀ k, tL k < t₀ := fun k ↦ lt_of_le_of_lt
    (Finset.le_max' T (tL k) (Finset.mem_insert_of_mem (Finset.mem_union_right _
      (Finset.mem_image_of_mem tL (Finset.mem_univ k))))) ht₀M
  -- `y t₀` is admissible.
  set y₀ := RationalAffineWall.segment w y t₀ with hy₀
  have hreqpos : ∀ i, 0 < y₀ i := by
    intro i
    have hrw : y₀ i = (1 - t₀) * w i + t₀ * y i := by
      simp only [hy₀, RationalAffineWall.segment]; ring
    rw [hrw]
    have h1 : 0 < (1 - t₀) * w i := mul_pos (by linarith) (hwpos i)
    have h2 : 0 ≤ t₀ * y i := mul_nonneg ht₀pos.le (hy i)
    linarith
  have hadm : Admissible core s B y₀ := by
    refine ⟨hreqpos, ?_, ?_, ?_, ?_⟩
    · intro k col hzero
      exact hnotBad (Or.inl (Or.inl ⟨k, col, hzero⟩))
    · intro k col hzero
      rw [hy₀, baseRequest_segment] at hzero
      exact hnotBad (Or.inl (Or.inr ⟨k, col, hzero⟩))
    · intro b hb hzero
      exact hnotBad (Or.inr ⟨b, hb, hzero⟩)
    · intro k
      exact htL k t₀ (hlegt₀ k) ht₀one.le
  -- Step 5: an open odd claw member at `t₀`.
  have hodd := hpack y₀ hadm
  have hne : openOddClawCount core s y₀ ≠ 0 := by
    intro h
    rw [h] at hodd
    exact absurd hodd (by simp)
  obtain ⟨⟨c, hcOpen, hcOdd, mem, rfl, hClaw⟩⟩ := (Nat.card_ne_zero.mp hne).1
  have hmemOpen : mem.Open := (GeometricFibre.open_cls mem).mp hcOpen
  have hmemOdd : mem.HasOddMult := (GeometricFibre.isOdd_cls_iff mem).mp hcOdd
  -- Step 6: read it through its frame, and carry the frame to `t = 1`.
  set κ : Frame (tripodCore core s) (3 + 2) := Frame.of mem with hκ
  have hκOpen : ∀ col, 0 < κ.coordsAt y₀ col := by
    intro col
    rw [hκ, Frame.coordsAt_of]
    exact hmemOpen col
  refine ⟨κ.member y, ?_, (hasOddMult_frame_member mem y).mpr hmemOdd,
    (memberIsClaw_frame_member mem y).mpr hClaw⟩
  intro col
  by_contra hneg
  rw [not_le] at hneg
  have hcoord : κ.coordsAt y col < 0 := hneg
  have hno : ∀ t, min t₀ 1 ≤ t → t ≤ max t₀ 1 → ¬ κ.IsWallParam w y col t := by
    intro t hmin hmax hwall
    rw [min_eq_left ht₀one.le] at hmin
    rw [max_eq_right ht₀one.le] at hmax
    rcases lt_or_eq_of_le hmax with hlt | heq
    · exact absurd (hle t (Or.inl (Or.inl ⟨κ, col, hwall⟩)) hlt)
        (not_le.mpr (lt_of_lt_of_le ht₀M hmin))
    · rw [SegmentWalls.Frame.IsWallParam, heq, StepSupplyReduction.segment_one] at hwall
      exact absurd hwall (ne_of_lt hcoord)
  have hcarry := κ.pos_of_pos_of_no_wall w y col t₀ 1 (hκOpen col) hno
  rw [StepSupplyReduction.segment_one] at hcarry
  exact absurd hcarry (not_lt.mpr hcoord.le)

end GenusSixExistence.Tripod.ClosureFrame
