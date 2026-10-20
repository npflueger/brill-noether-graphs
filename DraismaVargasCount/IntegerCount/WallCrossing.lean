module

public import DraismaVargasCount.IntegerCount.StarBalance

@[expose] public section

/-!
# The integer crossing of a trivalent wall

The integer twin of `WallSwitchingBridge.countLink_of_even_stars` and of
`SimpleWallSupply.inConeSupplySimple_of_even_stars`: across an isolated
codimension-one wall of a segment of positive requests, the weighted count is unchanged as soon
as every star at the wall request is balanced by sides (`StarBalanceAt`).

## The argument

Read both counts inside the fibre at the wall request `yt = segment y₀ y₁ t` through
`GeometricSegmentWalls.fibreEquiv` (`multNat` does not move, `multNat_fibreEquiv`).  A class
that is not a wall class has the same openness at `a` and at `b`
(`WallSwitchingBridge.changes_iff_isWallClass`), so it contributes equally.  A wall class is
open at `b` exactly when it opens toward `y₁ - y₀`, and at `a` exactly when it opens toward
`y₀ - y₁` (`openAt_after_iff`, `openAt_before_iff`, from the side law of `ConeSide` on one
coordinate).  The wall classes are the disjoint union of the stars
(`WallSwitchingBridge.SameStar`, `sameStar_of_isStarClass`, `isWallClass_iff_exists_star`), so
the difference of the two counts is a sum over stars of
`starSideSum hy w (y₀ - y₁) - starSideSum hy w (y₁ - y₀)`, which `StarBalanceAt` makes zero.

## Contents

* `coordsAt_sub`, `openAt_after_iff`, `openAt_before_iff` (proved).
* `finsum_subtype_eq_sum_filter`, `sum_filter_eq_of_blocks`, `openMultCount_eq_sum_at`,
  `open_fibreEquiv_cls_iff` (proved): the counting facts, with no wall in them.
* `intLink_of_balanced_stars` (proved): one wall.
* `inConeSupplySum_of_starBalance` (proved from it): the supply.
-/

namespace DraismaVargas.Count.IntegerCount

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open DraismaVargas.Count.WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)

variable {n p degree : ℕ} {core : Core n p}

/-! ## 1.  The side of a wall class, on a segment -/

theorem coordsAt_sub (k : Frame core degree) (y y' : Fin p → ℚ) (col : Fin p) :
    k.coordsAt (y - y') col = k.coordsAt y col - k.coordsAt y' col := by
  simp only [Frame.coordsAt_apply, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun r _ ↦ by ring

/-- **After an isolated simple wall, a degenerate frame is open exactly when it opens toward
`y₁ - y₀`.** -/
theorem openAt_after_iff {y₀ y₁ : Fin p → ℚ} {a t b : ℚ} (hat : a < t) (htb : t < b)
    (hsimple : WallSwitchingBridge.SimpleAt core degree y₀ y₁ t)
    (hiso : WallSwitchingBridge.Isolated core degree y₀ y₁ a t b)
    (k : Frame core degree) {col : Fin p}
    (hdeg : k.DegenerateAt (RationalAffineWall.segment y₀ y₁ t) col) :
    k.OpenAt (RationalAffineWall.segment y₀ y₁ b) ↔
      OpensToward (GeometricFibre.cls (k.member (RationalAffineWall.segment y₀ y₁ t)))
        (y₁ - y₀) := by
  rw [opensToward_cls_iff hdeg, coordsAt_sub]
  have hwall : k.IsWallParam y₀ y₁ col t := hdeg.1
  constructor
  · intro hb
    exact (ConeSide.coordsAt_pos_iff_of_lt k y₀ y₁ col hwall htb).mp (hb col)
  · intro hΔ c
    by_cases hc : c = col
    · subst hc
      exact (ConeSide.coordsAt_pos_iff_of_lt k y₀ y₁ c hwall htb).mpr hΔ
    · have hnow : ¬ k.IsWallParam y₀ y₁ c t := fun h ↦ hc (hsimple k c col h hwall)
      exact WallSwitchingBridge.pos_of_pos_of_isolated hiso k c hnow hat.le htb.le
        (hat.trans htb).le le_rfl (hdeg.2 c hc)

/-- **Before an isolated simple wall, a degenerate frame is open exactly when it opens toward
`y₀ - y₁`.** -/
theorem openAt_before_iff {y₀ y₁ : Fin p → ℚ} {a t b : ℚ} (hat : a < t) (htb : t < b)
    (hsimple : WallSwitchingBridge.SimpleAt core degree y₀ y₁ t)
    (hiso : WallSwitchingBridge.Isolated core degree y₀ y₁ a t b)
    (k : Frame core degree) {col : Fin p}
    (hdeg : k.DegenerateAt (RationalAffineWall.segment y₀ y₁ t) col) :
    k.OpenAt (RationalAffineWall.segment y₀ y₁ a) ↔
      OpensToward (GeometricFibre.cls (k.member (RationalAffineWall.segment y₀ y₁ t)))
        (y₀ - y₁) := by
  rw [opensToward_cls_iff hdeg, coordsAt_sub, sub_pos]
  have hwall : k.IsWallParam y₀ y₁ col t := hdeg.1
  constructor
  · intro ha
    have h := (ConeSide.coordsAt_pos_iff_of_gt k y₀ y₁ col hwall hat).mp (ha col)
    linarith
  · intro hΔ c
    by_cases hc : c = col
    · subst hc
      exact (ConeSide.coordsAt_pos_iff_of_gt k y₀ y₁ c hwall hat).mpr (by linarith)
    · have hnow : ¬ k.IsWallParam y₀ y₁ c t := fun h ↦ hc (hsimple k c col h hwall)
      exact WallSwitchingBridge.pos_of_pos_of_isolated hiso k c hnow hat.le htb.le
        le_rfl (hat.trans htb).le (hdeg.2 c hc)

/-! ## 2.  Two counting facts

The integer twin of `WallSwitchingBridge.even_card_of_even_blocks`, and the weighted count read
inside a fixed fibre.  Nothing about walls or stars enters. -/

/-- A `finsum` over a subtype of a finite type is the `Finset` sum over the filter. -/
theorem finsum_subtype_eq_sum_filter {T : Type*} [Fintype T] (P : T → Prop) [DecidablePred P]
    (f : T → ℕ) : ∑ᶠ c : {c // P c}, f c.1 = ∑ c ∈ Finset.univ.filter P, f c := by
  rw [finsum_eq_sum_of_fintype,
    Finset.sum_subtype (p := P) (Finset.univ.filter P) (fun c ↦ by simp)]

/-- **Sums agreeing on every block of a partition agree.**  Over a finite type carrying an
equivalence relation, if on every block the elements satisfying `P` and those satisfying `Q`
carry the same total weight, then so do all of them. -/
theorem sum_filter_eq_of_blocks {T : Type*} [Fintype T] (s : Setoid T) [DecidableRel s.r]
    (P Q : T → Prop) [DecidablePred P] [DecidablePred Q] (f : T → ℕ)
    (h : ∀ x : T, ∑ y ∈ Finset.univ.filter (fun y ↦ s.r y x ∧ P y), f y =
      ∑ y ∈ Finset.univ.filter (fun y ↦ s.r y x ∧ Q y), f y) :
    ∑ y ∈ Finset.univ.filter P, f y = ∑ y ∈ Finset.univ.filter Q, f y := by
  classical
  have _ : Finite (Quotient s) := Finite.of_surjective (Quotient.mk s) Quotient.mk_surjective
  have _ : Fintype (Quotient s) := Fintype.ofFinite _
  have hset : ∀ (R : T → Prop) [DecidablePred R] (x : T),
      {a ∈ Finset.univ.filter R | Quotient.mk s a = Quotient.mk s x} =
        Finset.univ.filter (fun y ↦ s.r y x ∧ R y) := by
    intro R _ x
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Quotient.eq]
    exact ⟨fun hh ↦ ⟨hh.2, hh.1⟩, fun hh ↦ ⟨hh.2, hh.1⟩⟩
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter P) (t := Finset.univ)
      (g := Quotient.mk s) (fun _ _ ↦ Finset.mem_univ _),
    ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter Q) (t := Finset.univ)
      (g := Quotient.mk s) (fun _ _ ↦ Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  obtain ⟨x, rfl⟩ := Quotient.exists_rep b
  rw [hset P x, hset Q x]
  exact h x

/-- **The weighted count at `y'`, read in the fibre at `yt`** through the request-fibre
identification, which keeps `multNat`. -/
theorem openMultCount_eq_sum_at (yt y' : Fin p → ℚ)
    [Fintype (GeometricFibre core yt degree)]
    [DecidablePred fun c : GeometricFibre core yt degree ↦
      (GeometricSegmentWalls.fibreEquiv core degree yt y' c).Open] :
    openMultCount core y' degree =
      ∑ c ∈ Finset.univ.filter (fun c : GeometricFibre core yt degree ↦
        (GeometricSegmentWalls.fibreEquiv core degree yt y' c).Open), c.multNat := by
  let e : {c : GeometricFibre core yt degree //
      (GeometricSegmentWalls.fibreEquiv core degree yt y' c).Open} ≃
      {c : GeometricFibre core y' degree // c.Open} :=
    (GeometricSegmentWalls.fibreEquiv core degree yt y').subtypeEquiv fun _ ↦ Iff.rfl
  unfold openMultCount
  rw [← finsum_comp_equiv e, ← finsum_subtype_eq_sum_filter]
  exact finsum_congr fun c ↦ multNat_fibreEquiv core degree yt y' c.1

/-- Openness of a class at another request, read on a representative frame. -/
theorem open_fibreEquiv_cls_iff (yt y' : Fin p → ℚ) (k : Frame core degree) :
    (GeometricSegmentWalls.fibreEquiv core degree yt y'
      (GeometricFibre.cls (k.member yt))).Open ↔ k.OpenAt y' := by
  rw [GeometricSegmentWalls.fibreEquiv_cls, Frame.of_member, GeometricFibre.open_cls]
  exact Iff.rfl

/-! ## 3.  One wall -/

/-- **The integer crossing of one wall.**  At an isolated codimension-one wall of a segment,
with the wall request nondegenerate, balanced stars give equal weighted counts on the two
sides.  The integer twin of `WallSwitchingBridge.countLink_of_even_stars`.

The proof follows the module docstring, in four steps.
1. Both counts are read in the fibre at `yt = segment y₀ y₁ t` (`openMultCount_eq_sum_at`).
2. Off the wall classes the two openness conditions agree
   (`WallSwitchingBridge.openAt_ne_iff_exists_degenerateAt` on a representative frame).
3. On a wall class they are the two sides (`openAt_before_iff`, `openAt_after_iff`).
4. The wall part is summed over the blocks of `WallSwitchingBridge.SameStar hy`
   (`sum_filter_eq_of_blocks`, the integer twin of `even_card_of_even_blocks`).  The block of a
   wall class of the star of `w` is that star, so its two parts are `starSideSum hy w (y₀ - y₁)`
   and `starSideSum hy w (y₁ - y₀)`, equal by `hstar w`. -/
theorem intLink_of_balanced_stars {y₀ y₁ : Fin p → ℚ} {a t b : ℚ}
    (hat : a < t) (htb : t < b)
    (hsimple : WallSwitchingBridge.SimpleAt core degree y₀ y₁ t)
    (hiso : WallSwitchingBridge.Isolated core degree y₀ y₁ a t b)
    (hy : Nondegenerate (RationalAffineWall.segment y₀ y₁ t))
    (hstar : ∀ w : Regrowth core (RationalAffineWall.segment y₀ y₁ t) degree,
      StarBalanceAt hy w) :
    IntLink degree core (RationalAffineWall.segment y₀ y₁ a) core
      (RationalAffineWall.segment y₀ y₁ b) := by
  classical
  have _ : Fintype (GeometricFibre core (RationalAffineWall.segment y₀ y₁ t) degree) :=
    Fintype.ofFinite _
  set yt := RationalAffineWall.segment y₀ y₁ t with hyt
  set Pa := fun c : GeometricFibre core yt degree ↦
    (GeometricSegmentWalls.fibreEquiv core degree yt (RationalAffineWall.segment y₀ y₁ a) c).Open
  set Pb := fun c : GeometricFibre core yt degree ↦
    (GeometricSegmentWalls.fibreEquiv core degree yt (RationalAffineWall.segment y₀ y₁ b) c).Open
  set W := fun c : GeometricFibre core yt degree ↦ WallSwitchingBridge.IsWallClass core degree yt c
  -- the class-level crossing: off the wall classes nothing changes; on them, the sides
  have hoff : ∀ c, ¬ W c → (Pa c ↔ Pb c) := by
    intro c hc
    obtain ⟨k, rfl⟩ := WallSwitchingBridge.cls_frame_surjective yt c
    simp only [Pa, Pb, open_fibreEquiv_cls_iff]
    by_contra hne
    exact hc ((WallSwitchingBridge.isWallClass_cls_iff yt k).mpr
      ((WallSwitchingBridge.openAt_ne_iff_exists_degenerateAt hat htb k (hsimple k) hiso).mp
        hne))
  have hon : ∀ c, W c → (Pa c ↔ OpensToward c (y₀ - y₁)) ∧ (Pb c ↔ OpensToward c (y₁ - y₀)) := by
    intro c hc
    obtain ⟨k, rfl⟩ := WallSwitchingBridge.cls_frame_surjective yt c
    obtain ⟨col, hdeg⟩ := (WallSwitchingBridge.isWallClass_cls_iff yt k).mp hc
    simp only [Pa, Pb, open_fibreEquiv_cls_iff]
    exact ⟨openAt_before_iff hat htb hsimple hiso k hdeg,
      openAt_after_iff hat htb hsimple hiso k hdeg⟩
  -- split both counts into wall and non-wall classes
  have hsplit : ∀ P : GeometricFibre core yt degree → Prop, ∀ _ : DecidablePred P,
      ∑ c ∈ Finset.univ.filter P, c.multNat =
        ∑ c ∈ Finset.univ.filter (fun c ↦ W c ∧ P c), c.multNat +
          ∑ c ∈ Finset.univ.filter (fun c ↦ ¬ W c ∧ P c), c.multNat := by
    intro P _
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter P) W, Finset.filter_filter,
      Finset.filter_filter]
    congr 1 <;> exact Finset.sum_congr (Finset.filter_congr fun c _ ↦ and_comm) fun _ _ ↦ rfl
  unfold IntLink
  rw [openMultCount_eq_sum_at yt, openMultCount_eq_sum_at yt]
  change ∑ c ∈ Finset.univ.filter Pa, c.multNat = ∑ c ∈ Finset.univ.filter Pb, c.multNat
  rw [hsplit Pa inferInstance, hsplit Pb inferInstance]
  congr 1
  · -- the wall classes: sum over the stars
    rw [Finset.filter_congr fun c _ ↦ and_congr_right fun hc ↦ (hon c hc).1,
      Finset.filter_congr fun c _ ↦ and_congr_right fun hc ↦ (hon c hc).2]
    refine sum_filter_eq_of_blocks (WallSwitchingBridge.SameStar hy) _ _ _ fun x ↦ ?_
    by_cases hx : W x
    · obtain ⟨w, hw⟩ := (WallSwitchingBridge.isWallClass_iff_exists_star hy x).mp hx
      have hblock : ∀ d : Fin p → ℚ,
          Finset.univ.filter (fun c ↦ (WallSwitchingBridge.SameStar hy).r c x ∧
              (W c ∧ OpensToward c d)) =
            Finset.univ.filter (fun c ↦ GeometricStar.IsStarClass hy w c ∧ OpensToward c d) := by
        intro d
        refine Finset.filter_congr fun c _ ↦ ?_
        constructor
        · rintro ⟨hrel, -, ho⟩
          exact ⟨(hrel w).mpr hw, ho⟩
        · rintro ⟨hc, ho⟩
          exact ⟨WallSwitchingBridge.sameStar_of_isStarClass hy hc hw,
            (WallSwitchingBridge.isWallClass_iff_exists_star hy c).mpr ⟨w, hc⟩, ho⟩
      rw [hblock, hblock, ← finsum_subtype_eq_sum_filter, ← finsum_subtype_eq_sum_filter]
      have h := hstar w (y₀ - y₁)
      rw [neg_sub] at h
      exact h
    · have hempty : ∀ d : Fin p → ℚ,
          Finset.univ.filter (fun c ↦ (WallSwitchingBridge.SameStar hy).r c x ∧
            (W c ∧ OpensToward c d)) = ∅ := by
        intro d
        refine Finset.filter_eq_empty_iff.mpr fun c _ ⟨hrel, hc, _⟩ ↦ hx ?_
        obtain ⟨w, hw⟩ := (WallSwitchingBridge.isWallClass_iff_exists_star hy c).mp hc
        exact (WallSwitchingBridge.isWallClass_iff_exists_star hy x).mpr ⟨w, (hrel w).mp hw⟩
      rw [hempty, hempty]
  · -- the other classes do not move
    exact Finset.sum_congr (Finset.filter_congr fun c _ ↦ and_congr_right fun hc ↦ hoff c hc)
      fun _ _ ↦ rfl

/-! ## 4.  The supply -/

/-- **The trivalent walls, integer form, from the balance of every star.**  The twin of
`SimpleWallSupply.inConeSupplySimple_of_even_stars`: positivity of the endpoints makes the wall
request nondegenerate (`WallSwitchingBridge.nondegenerate_segment`). -/
theorem inConeSupplySum_of_starBalance
    (hstars : ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y)
      (w : Regrowth core y degree), StarBalanceAt hy w) :
    InConeSupplySum degree n p := by
  intro core S a t b hsrc htgt hlo hat htb hb1 _ hiso hsimple
  exact intLink_of_balanced_stars hat htb hsimple hiso
    (WallSwitchingBridge.nondegenerate_segment hsrc htgt (le_trans hlo hat.le)
      (le_trans htb.le hb1))
    fun w ↦ hstars core _ _ w

/-- **The trivalent walls, integer form, from the ten families.**  The twin of
`RegrowthWallInput.inConeSupplySimple_of_familyStarParity`. -/
theorem inConeSupplySum_of_familyStarBalance
    (h : ∀ tag, FamilyStarBalance degree n p tag) : InConeSupplySum degree n p :=
  inConeSupplySum_of_starBalance fun _ _ hy w ↦ starBalanceAt_of_family h hy w

end DraismaVargas.Count.IntegerCount
