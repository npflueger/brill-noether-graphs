module

public import DraismaVargasCount.CountSchedule
public import DraismaVargasCount.SwitchingParity
public import DraismaVargasCount.GeometricStar
public import DraismaVargasCount.ConeSide

@[expose] public section

/-!
# The bridge from the switching classes to the star of a wall

**Source.**  Vargas, Part II (arXiv:2609.09109), `sec-deformation-invariance`, in particular
the wall crossing of `subsec-walking-through-walls`.

## Why this file exists

`CountTransportLink.countLink_iff_even_switchingCount` reduces a
`CountLink` across an in-cone wall to `Even (switchingCount core degree y y')`.
But `switchingCount` is a statement about a **pair of requests**, while
`GeometricStar.Star hy wall` -- the object the star censuses build, count and
classify -- is indexed by **one** nondegenerate request and **one** limit.
Nothing elsewhere connects the two: the only `DegenerateAt` result in
`GeometricSegmentWalls` is `degenerateAt_map`, plain transport along a `FrameIso`, and
`SwitchingParity` names both `switchingCount` and `Star` without relating them.  Without
this bridge, `Covers` at every wall of all ten families would not produce
`Even (switchingCount …)`.

This file builds that bridge.

## What is proved here

* `exists_degenerateAt_of_openAt_ne`, `openAt_ne_of_degenerateAt`,
  `openAt_ne_iff_exists_degenerateAt` -- **the frame-level bridge, as an
  equivalence.**  Across an interval `[a, b]` containing exactly one wall
  parameter `t` of the whole fibre, a frame's openness differs at the two ends
  **iff** the frame is `SegmentWalls.Frame.DegenerateAt` at the wall request.
  Both directions are proved; the converse is the sharper half, and it is what
  says the star is not merely an upper bound for the changing classes.  The
  converse uses the sign law of `ConeSide` directly (the side of a wall is the sign of
  the vanishing coordinate): `ConeSide.coordsAt_segment_of_isWallParam` and
  `ConeSide.coordsAt_pos_iff_of_lt` / `_of_gt` are exactly what it needs.  The
  parity step below does not need them.
* `changes_iff_isWallClass` -- **the same on classes.**  A class of the geometric
  fibre changes its openness between the two sides exactly when its image at the
  wall request is a **wall class**, i.e. carries a `WallStar.Regrowth`.
* `switchingCount_eq_card_oddWallClasses` -- the switching count *is* the number
  of odd wall classes at the wall request.  This is the identification the parity
  across a trivalent wall needs.
* `isWallClass_iff_exists_star`, `sameLimit_of_isStarClass`, `isStarClass_congr`,
  `sameStar_of_isStarClass` -- **the decomposition into stars, and its
  disjointness.**  Every wall class lies in a star; two stars sharing a class
  have isomorphic limits, hence are the same set of classes.  So the stars at one
  wall parameter partition the wall classes, and are indexed by `SameLimit`
  classes of regrowths rather than by regrowths.  This settles the first
  obstacle: **the sum over the several stars at one wall parameter is taken over
  the blocks of `SameStar`.**
* `even_card_of_even_blocks` -- how that sum is taken, over any finite type with
  any equivalence relation: if every block carries an even number of elements
  satisfying `P`, so does the whole type.  No fibre, no wall, no star.
* `even_switchingCount_of_even_stars`, `countLink_of_even_stars`,
  `schedule_countLink_of_even_stars`, `schedule_countLink_of_even_star_card` --
  **the bridge, assembled**: per-star parity at the wall gives
  `Even (switchingCount …)`, hence the `CountLink` in the shape
  `CountSchedule.Schedule.transport`'s `link` binder asks for.
* `simpleAtFrame_of_nf`, `simpleAt_of_genericStart`,
  `exists_simple_generic_start` -- the codimension-one hypothesis `SimpleAt` is
  exactly `SegmentWalls.exists_generic_start`'s output read over the whole fibre
  through the normal-form family, so it is achievable **provided the finish is
  general and the start is chosen after it**.
* `nondegenerate_segment` -- the wall request is nondegenerate when both
  endpoints are positive and `0 ≤ t ≤ 1`.
* `not_nondegenerate_of_catFrame_isWallParam`,
  `catFrame_not_isWallParam_of_nondegenerate` -- **the second obstacle: the
  caterpillar frame's walls are degenerate requests.**  The caterpillar frame's
  coordinate in a column is the requested slot length over a positive diagonal
  entry, so it vanishes exactly when the slot length does.  Hence a wall of the
  caterpillar frame sits at a request with a zero slot, where
  `GeometricStar.Star` is **not defined**; and the caterpillar frame contributes
  no wall at all inside the positive orthant.
* `transport_of_finite_walls_bounded`, `schedule_transport_bounded` -- the
  bounded restatement of the schedule.  The induction never leaves `[0, 1]`, so
  the link binder may be restricted to `0 ≤ a` and `b ≤ 1` at no cost to
  `transport_source_target`.
* `countLink_source_target_of_even_stars` -- **the in-cone parity at one
  schedule, end to end**: positive endpoints, a general finish and a
  codimension-one segment reduce the whole segment's link to per-star parity at
  the interior wall requests, and to nothing else.

## What is NOT proved here -- every surviving hypothesis

* **No star parity is proved.**  `hstar` -- "every star at the wall request
  carries an even number of odd classes" -- is a hypothesis of every theorem in
  §6, §7 and §10.  The star parity is proved family by family in the star
  exhaustion modules and collected in `StarSupplyAssembly`; none of it is
  discharged here.  Nothing here counts a star, classifies its members, or
  evaluates a multiplicity.
* **`SimpleAt` is a genuine extra hypothesis, and `CountSchedule.Schedule` does
  not carry it.**  `Schedule` stores only `general` at the `source`; its `target`
  is unconstrained and its `source` is chosen without reference to the target,
  whereas `SegmentWalls.exists_generic_start` chooses the start *after* the
  finish.  Without `SimpleAt` the forward bridge fails at a codimension-two
  crossing -- two columns of one frame vanishing at the same parameter -- where
  the frame's openness can change without the frame being `DegenerateAt`
  anywhere.  `exists_simple_generic_start` shows the hypothesis is achievable,
  not that any given schedule satisfies it.
* **`Nondegenerate` at the wall request is a genuine extra hypothesis.**  It fails
  at every wall of the caterpillar frame (`not_nondegenerate_of_catFrame_isWallParam`).
  A link asked for at all `a t b : ℚ` with `Schedule.target` unconstrained would
  reach walls at which no star exists.  Restricting to `0 ≤ a ∧ b ≤ 1` with
  **positive** endpoints is what `nondegenerate_segment` and
  `schedule_transport_bounded` make available, and it is the form
  `SimpleWallSupply.InConeSupplySimple` takes.  Carrying positivity along the chain
  of cores is not done here: `StepSupplyReduction.GeneralRequest` does not include
  positivity, and `SimpleWallSupply.TypeChangeSupplyPositive` asks for it separately.
* **Nothing here exhibits a wall inside the positive orthant.**  The caterpillar
  frame contributes none (`catFrame_not_isWallParam_of_nondegenerate`), but that
  immunity is special: a frame column carries a positive-orthant zero unless some
  row of the length matrix is supported in that column alone
  (`PositiveOrthantWall.exists_positive_zero_iff`), and a frame with no
  positive-orthant zero in any column has a monomial length matrix
  (`PositiveOrthantWall.exists_unique_isolatedRow_of_no_positive_wall`).  So the
  absence of positive-orthant walls is a rare degeneracy of the length matrix, not a
  general property of frames.
* **The partition is by `SameStar`, an indistinguishability relation, not by a
  chosen index of stars.**  `even_card_of_even_blocks` needs no index type, and
  none is built: `Regrowth core y degree` is not finite, and no finite indexing
  of the stars at a wall parameter is constructed here.
* **`switchingCount` here is `CountTransportLink.switchingCount` and `IsOdd` is
  `GeometricFibre.IsOdd`**, the unsigned `multNat` parity.  No signed
  multiplicity is used anywhere; `Count.ConeSide` enters only through its sign
  law on one coordinate, never through a multiplicity.
* Nothing here is about a type-change wall (step 3 of the genus-six assembly).

Consumers: `SimpleWallSupply` (`InConeSupplySimple`, `inConeSupplySimple_of_even_stars`) and
`StarParityFromBalance`, and through them the trivalent walls of step 2 of
`DraismaVargasCount/Assembly.lean`.
-/

namespace DraismaVargas.Count.WallSwitchingBridge

open DraismaVargas.Infrastructure
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.WallStar (Regrowth Nondegenerate)

variable {n p degree : ℕ} {core : Core n p}

/-! ## 1.  The two hypotheses the bridge needs -/

/-- **Codimension one at `t`, for one frame.** -/
def SimpleAtFrame (k : Frame core degree) (y₀ y₁ : Fin p → ℚ) (t : ℚ) : Prop :=
  ∀ col col' : Fin p, k.IsWallParam y₀ y₁ col t → k.IsWallParam y₀ y₁ col' t → col = col'

/-- **Codimension one at `t`, over the whole fibre.** -/
def SimpleAt (core : Core n p) (degree : ℕ) (y₀ y₁ : Fin p → ℚ) (t : ℚ) : Prop :=
  ∀ k : Frame core degree, SimpleAtFrame k y₀ y₁ t

/-- **Isolation of the wall parameter**: `t` is the only wall parameter in `[a, b]`.  This is
the isolation hypothesis `SimpleWallSupply.InConeSupplySimple` carries. -/
def Isolated (core : Core n p) (degree : ℕ) (y₀ y₁ : Fin p → ℚ) (a t b : ℚ) : Prop :=
  ∀ u, CountSchedule.IsWall core degree y₀ y₁ u → a ≤ u → u ≤ b → u = t

theorem isWallParam_eq_of_isolated {y₀ y₁ : Fin p → ℚ} {a t b u : ℚ}
    (hiso : Isolated core degree y₀ y₁ a t b) (k : Frame core degree) (col : Fin p)
    (hu : k.IsWallParam y₀ y₁ col u) (h1 : a ≤ u) (h2 : u ≤ b) : u = t :=
  hiso u ⟨k, col, hu⟩ h1 h2

/-- **A column with no wall at `t` keeps its sign across the whole interval.** -/
theorem pos_of_pos_of_isolated {y₀ y₁ : Fin p → ℚ} {a t b : ℚ}
    (hiso : Isolated core degree y₀ y₁ a t b) (k : Frame core degree) (col : Fin p)
    (hcol : ¬ k.IsWallParam y₀ y₁ col t) {u v : ℚ}
    (hu : a ≤ u) (hu' : u ≤ b) (hv : a ≤ v) (hv' : v ≤ b)
    (hpos : 0 < k.coordsAt (RationalAffineWall.segment y₀ y₁ u) col) :
    0 < k.coordsAt (RationalAffineWall.segment y₀ y₁ v) col := by
  refine k.pos_of_pos_of_no_wall y₀ y₁ col u v hpos ?_
  intro s hs1 hs2 hw
  have hsa : a ≤ s := le_trans (le_min hu hv) hs1
  have hsb : s ≤ b := le_trans hs2 (max_le hu' hv')
  have hst : s = t := isWallParam_eq_of_isolated hiso k col hw hsa hsb
  exact hcol (hst ▸ hw)

/-! ## 2.  The frame-level bridge -/

/-- **A frame whose openness changes across an isolated wall is degenerate at it.** -/
theorem exists_degenerateAt_of_openAt_ne {y₀ y₁ : Fin p → ℚ} {a t b : ℚ}
    (hat : a < t) (htb : t < b) (k : Frame core degree)
    (hk : SimpleAtFrame k y₀ y₁ t) (hiso : Isolated core degree y₀ y₁ a t b)
    (hne : ¬ (k.OpenAt (RationalAffineWall.segment y₀ y₁ a) ↔
      k.OpenAt (RationalAffineWall.segment y₀ y₁ b))) :
    ∃ col, k.DegenerateAt (RationalAffineWall.segment y₀ y₁ t) col := by
  classical
  have hab : a ≤ b := (hat.trans htb).le
  have hta : a ≤ t := hat.le
  have htb' : t ≤ b := htb.le
  by_cases hA : k.OpenAt (RationalAffineWall.segment y₀ y₁ a)
  · have hB : ¬ k.OpenAt (RationalAffineWall.segment y₀ y₁ b) := fun h ↦
      hne ⟨fun _ ↦ h, fun _ ↦ hA⟩
    obtain ⟨c₀, hc₀⟩ := not_forall.mp hB
    have hwall : k.IsWallParam y₀ y₁ c₀ t := by
      by_contra hno
      exact hc₀ (pos_of_pos_of_isolated hiso k c₀ hno le_rfl hab hab le_rfl (hA c₀))
    refine ⟨c₀, hwall, ?_⟩
    intro c hc
    refine pos_of_pos_of_isolated hiso k c ?_ le_rfl hab hta htb' (hA c)
    intro hcw
    exact hc (hk c c₀ hcw hwall)
  · have hB : k.OpenAt (RationalAffineWall.segment y₀ y₁ b) := by
      by_contra hB
      exact hne ⟨fun h ↦ absurd h hA, fun h ↦ absurd h hB⟩
    obtain ⟨c₀, hc₀⟩ := not_forall.mp hA
    have hwall : k.IsWallParam y₀ y₁ c₀ t := by
      by_contra hno
      exact hc₀ (pos_of_pos_of_isolated hiso k c₀ hno hab le_rfl le_rfl hab (hB c₀))
    refine ⟨c₀, hwall, ?_⟩
    intro c hc
    refine pos_of_pos_of_isolated hiso k c ?_ hab le_rfl hta htb' (hB c)
    intro hcw
    exact hc (hk c c₀ hcw hwall)

/-- **Conversely, a frame degenerate at an isolated wall changes openness across it.** -/
theorem openAt_ne_of_degenerateAt {y₀ y₁ : Fin p → ℚ} {a t b : ℚ}
    (hat : a < t) (htb : t < b) (k : Frame core degree)
    (hk : SimpleAtFrame k y₀ y₁ t) (hiso : Isolated core degree y₀ y₁ a t b)
    {col : Fin p} (hdeg : k.DegenerateAt (RationalAffineWall.segment y₀ y₁ t) col) :
    ¬ (k.OpenAt (RationalAffineWall.segment y₀ y₁ a) ↔
      k.OpenAt (RationalAffineWall.segment y₀ y₁ b)) := by
  have hab : a ≤ b := (hat.trans htb).le
  have hta : a ≤ t := hat.le
  have htb' : t ≤ b := htb.le
  have hcolwall : k.IsWallParam y₀ y₁ col t := hdeg.1
  have hother : ∀ c, c ≠ col →
      0 < k.coordsAt (RationalAffineWall.segment y₀ y₁ a) c ∧
        0 < k.coordsAt (RationalAffineWall.segment y₀ y₁ b) c := by
    intro c hc
    have hnow : ¬ k.IsWallParam y₀ y₁ c t := fun h ↦ hc (hk c col h hcolwall)
    exact ⟨pos_of_pos_of_isolated hiso k c hnow hta htb' le_rfl hab (hdeg.2 c hc),
      pos_of_pos_of_isolated hiso k c hnow hta htb' hab le_rfl (hdeg.2 c hc)⟩
  have hBA : k.coordsAt y₁ col - k.coordsAt y₀ col ≠ 0 := by
    intro h
    have hwa : k.IsWallParam y₀ y₁ col a := by
      show k.coordsAt (RationalAffineWall.segment y₀ y₁ a) col = 0
      rw [ConeSide.coordsAt_segment_of_isWallParam k y₀ y₁ col hcolwall a, h, mul_zero]
    exact absurd (isWallParam_eq_of_isolated hiso k col hwa le_rfl hab) (ne_of_lt hat)
  intro hiff
  rcases lt_or_gt_of_ne hBA with hlt | hgt
  · have hApos : 0 < k.coordsAt (RationalAffineWall.segment y₀ y₁ a) col :=
      (ConeSide.coordsAt_pos_iff_of_gt k y₀ y₁ col hcolwall hat).mpr hlt
    have hBnotpos : ¬ (0 < k.coordsAt (RationalAffineWall.segment y₀ y₁ b) col) := by
      rw [ConeSide.coordsAt_pos_iff_of_lt k y₀ y₁ col hcolwall htb]
      exact not_lt.mpr hlt.le
    refine hBnotpos (hiff.mp (fun c ↦ ?_) col)
    by_cases hc : c = col
    · subst hc; exact hApos
    · exact (hother c hc).1
  · have hBpos : 0 < k.coordsAt (RationalAffineWall.segment y₀ y₁ b) col :=
      (ConeSide.coordsAt_pos_iff_of_lt k y₀ y₁ col hcolwall htb).mpr hgt
    have hAnotpos : ¬ (0 < k.coordsAt (RationalAffineWall.segment y₀ y₁ a) col) := by
      rw [ConeSide.coordsAt_pos_iff_of_gt k y₀ y₁ col hcolwall hat]
      exact not_lt.mpr hgt.le
    refine hAnotpos (hiff.mpr (fun c ↦ ?_) col)
    by_cases hc : c = col
    · subst hc; exact hBpos
    · exact (hother c hc).2

/-- **The frame-level bridge, as an equivalence.** -/
theorem openAt_ne_iff_exists_degenerateAt {y₀ y₁ : Fin p → ℚ} {a t b : ℚ}
    (hat : a < t) (htb : t < b) (k : Frame core degree)
    (hk : SimpleAtFrame k y₀ y₁ t) (hiso : Isolated core degree y₀ y₁ a t b) :
    (¬ (k.OpenAt (RationalAffineWall.segment y₀ y₁ a) ↔
      k.OpenAt (RationalAffineWall.segment y₀ y₁ b))) ↔
      ∃ col, k.DegenerateAt (RationalAffineWall.segment y₀ y₁ t) col :=
  ⟨exists_degenerateAt_of_openAt_ne hat htb k hk hiso,
    fun ⟨_, hdeg⟩ ↦ openAt_ne_of_degenerateAt hat htb k hk hiso hdeg⟩

/-! ## 3.  From frames to classes of the geometric fibre -/

/-- Every class of the geometric fibre is the class of a frame's member. -/
theorem cls_frame_surjective (y : Fin p → ℚ) (c : GeometricFibre core y degree) :
    ∃ k : Frame core degree, GeometricFibre.cls (k.member y) = c := by
  obtain ⟨member, rfl⟩ := GeometricFibre.cls_surjective c
  exact ⟨Frame.of member, by rw [Frame.member_of]⟩

/-- **A wall class**: a class of the geometric fibre at the wall request that
some frame degenerates at.  This is `WallStar.Regrowth`, read on classes. -/
def IsWallClass (core : Core n p) (degree : ℕ) (yt : Fin p → ℚ)
    (c : GeometricFibre core yt degree) : Prop :=
  ∃ w : Regrowth core yt degree, GeometricFibre.cls (w.frame.member yt) = c

/-- Being a wall class can be tested on any representative frame. -/
theorem isWallClass_cls_iff (yt : Fin p → ℚ) (k : Frame core degree) :
    IsWallClass core degree yt (GeometricFibre.cls (k.member yt)) ↔
      ∃ col, k.DegenerateAt yt col := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨iso⟩ := GeometricFibre.cls_eq_cls_iff.mp hw
    exact ⟨_, (GeometricSegmentWalls.FrameIso.ofMemberIso iso).degenerateAt_map w.degenerate⟩
  · rintro ⟨col, hcol⟩
    exact ⟨⟨k, col, hcol⟩, rfl⟩

/-- `SwitchingParity.Changes`, read on a frame. -/
theorem changes_cls_iff (y₀ y₁ : Fin p → ℚ) (a b : ℚ) (k : Frame core degree) :
    SwitchingParity.Changes core degree (RationalAffineWall.segment y₀ y₁ a)
        (RationalAffineWall.segment y₀ y₁ b)
        (GeometricFibre.cls (k.member (RationalAffineWall.segment y₀ y₁ a))) ↔
      ¬ (k.OpenAt (RationalAffineWall.segment y₀ y₁ a) ↔
        k.OpenAt (RationalAffineWall.segment y₀ y₁ b)) := by
  unfold SwitchingParity.Changes
  rw [GeometricSegmentWalls.fibreEquiv_cls, Frame.of_member]
  exact Iff.rfl

/-- **The bridge, on classes.**  Across an isolated codimension-one wall a class
changes its openness exactly when it is a wall class at the wall request. -/
theorem changes_iff_isWallClass {y₀ y₁ : Fin p → ℚ} {a t b : ℚ}
    (hat : a < t) (htb : t < b)
    (hsimple : SimpleAt core degree y₀ y₁ t) (hiso : Isolated core degree y₀ y₁ a t b)
    (c : GeometricFibre core (RationalAffineWall.segment y₀ y₁ a) degree) :
    SwitchingParity.Changes core degree (RationalAffineWall.segment y₀ y₁ a)
        (RationalAffineWall.segment y₀ y₁ b) c ↔
      IsWallClass core degree (RationalAffineWall.segment y₀ y₁ t)
        (GeometricSegmentWalls.fibreEquiv core degree (RationalAffineWall.segment y₀ y₁ a)
          (RationalAffineWall.segment y₀ y₁ t) c) := by
  obtain ⟨k, rfl⟩ := cls_frame_surjective (RationalAffineWall.segment y₀ y₁ a) c
  rw [changes_cls_iff, GeometricSegmentWalls.fibreEquiv_cls, Frame.of_member,
    isWallClass_cls_iff]
  exact openAt_ne_iff_exists_degenerateAt hat htb k (hsimple k) hiso

/-- **The switching count, read at the wall request.**  The odd classes whose
openness changes between the two sides are exactly the odd wall classes. -/
theorem switchingCount_eq_card_oddWallClasses {y₀ y₁ : Fin p → ℚ} {a t b : ℚ}
    (hat : a < t) (htb : t < b)
    (hsimple : SimpleAt core degree y₀ y₁ t) (hiso : Isolated core degree y₀ y₁ a t b) :
    CountTransportLink.switchingCount core degree (RationalAffineWall.segment y₀ y₁ a)
        (RationalAffineWall.segment y₀ y₁ b) =
      Nat.card {c : GeometricFibre core (RationalAffineWall.segment y₀ y₁ t) degree //
        c.IsOdd ∧ IsWallClass core degree (RationalAffineWall.segment y₀ y₁ t) c} := by
  rw [SwitchingParity.switchingCount_eq_card]
  refine Nat.card_congr (Equiv.subtypeEquiv
    (GeometricSegmentWalls.fibreEquiv core degree (RationalAffineWall.segment y₀ y₁ a)
      (RationalAffineWall.segment y₀ y₁ t)) fun c ↦ ?_)
  exact and_congr
    (GeometricSegmentWalls.isOdd_fibreEquiv core degree _ _ c).symm
    (changes_iff_isWallClass hat htb hsimple hiso c)

/-! ## 4.  The wall classes are the disjoint union of the stars -/

section Stars

variable {yt : Fin p → ℚ}

/-- **Every wall class lies in a star, and every star class is a wall class.** -/
theorem isWallClass_iff_exists_star (hy : Nondegenerate yt)
    (c : GeometricFibre core yt degree) :
    IsWallClass core degree yt c ↔
      ∃ w : Regrowth core yt degree, GeometricStar.IsStarClass hy w c := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, GeometricStar.Star.self hy w, hw⟩
  · rintro ⟨w, m, hm⟩
    exact ⟨m.member, hm⟩

/-- **Two stars that share a class have the same limit.** -/
theorem sameLimit_of_isStarClass (hy : Nondegenerate yt) {w w' : Regrowth core yt degree}
    {c : GeometricFibre core yt degree}
    (h : GeometricStar.IsStarClass hy w c) (h' : GeometricStar.IsStarClass hy w' c) :
    GeometricStar.SameLimit hy w w' := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨m', hm'⟩ := h'
  have hcls : GeometricFibre.cls (m.member.frame.member yt) =
      GeometricFibre.cls (m'.member.frame.member yt) := by rw [hm, hm']
  obtain ⟨iso⟩ := GeometricFibre.cls_eq_cls_iff.mp hcls
  have hmm' : GeometricStar.SameLimit hy m.member m'.member :=
    ⟨GeometricStar.LimitIso.ofFrameIso hy (GeometricSegmentWalls.FrameIso.ofMemberIso iso)⟩
  have heq := GeometricStar.sameLimit_equivalence (core := core) (degree := degree) hy
  exact heq.trans (heq.symm m.specializes) (heq.trans hmm' m'.specializes)

/-- **A star depends only on the limit**, so the stars of the wall request are
indexed by `SameLimit` classes of regrowths, not by regrowths. -/
theorem isStarClass_congr (hy : Nondegenerate yt) {w w' : Regrowth core yt degree}
    (h : GeometricStar.SameLimit hy w w') (c : GeometricFibre core yt degree) :
    GeometricStar.IsStarClass hy w c ↔ GeometricStar.IsStarClass hy w' c := by
  have heq := GeometricStar.sameLimit_equivalence (core := core) (degree := degree) hy
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨⟨m.member, heq.trans m.specializes h⟩, hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨⟨m.member, heq.trans m.specializes (heq.symm h)⟩, hm⟩

/-- **The partition relation.**  Two classes are in the same block when they
belong to exactly the same stars.  Every class of the fibre has a block; the
blocks meeting the wall classes are precisely the stars, and the one block of
non-wall classes carries no wall class at all. -/
def SameStar (hy : Nondegenerate yt) : Setoid (GeometricFibre core yt degree) where
  r c c' := ∀ w : Regrowth core yt degree,
    GeometricStar.IsStarClass hy w c ↔ GeometricStar.IsStarClass hy w c'
  iseqv := ⟨fun _ _ ↦ Iff.rfl, fun h w ↦ (h w).symm, fun h h' w ↦ (h w).trans (h' w)⟩

/-- **Two classes of one star are in one block.** -/
theorem sameStar_of_isStarClass (hy : Nondegenerate yt) {w : Regrowth core yt degree}
    {c c' : GeometricFibre core yt degree}
    (h : GeometricStar.IsStarClass hy w c) (h' : GeometricStar.IsStarClass hy w c') :
    (SameStar hy).r c c' := by
  intro w'
  constructor
  · intro hc
    exact (isStarClass_congr hy (sameLimit_of_isStarClass hy hc h) c').mpr h'
  · intro hc'
    exact (isStarClass_congr hy (sameLimit_of_isStarClass hy hc' h') c).mpr h

end Stars

/-! ## 5.  Summing a parity over the blocks of a partition -/

/-- **How a parity is summed over a partition.**  Over a finite type carrying an
equivalence relation, if every block contains an even number of elements
satisfying `P`, then the whole type does.  Nothing about walls, stars or fibres
enters; this is the only counting fact the star decomposition uses. -/
theorem even_card_of_even_blocks {T : Type*} [Finite T] (s : Setoid T) (P : T → Prop)
    (h : ∀ x : T, Even (Nat.card {y : T // s.r y x ∧ P y})) :
    Even (Nat.card {y : T // P y}) := by
  classical
  have _ : Fintype T := Fintype.ofFinite T
  have _ : Finite (Quotient s) := Finite.of_surjective (Quotient.mk s) Quotient.mk_surjective
  have _ : Fintype (Quotient s) := Fintype.ofFinite _
  have hcard : Nat.card {y : T // P y} = (Finset.univ.filter P).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard, Finset.card_eq_sum_card_fiberwise
    (f := fun x : T ↦ Quotient.mk s x) (s := Finset.univ.filter P) (t := Finset.univ)
    (fun x _ ↦ Finset.mem_univ _)]
  refine Finset.even_sum _ ?_
  intro b _
  obtain ⟨x, rfl⟩ := Quotient.exists_rep b
  have hset : {a ∈ Finset.univ.filter P | Quotient.mk s a = Quotient.mk s x} =
      Finset.univ.filter (fun y ↦ s.r y x ∧ P y) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Quotient.eq]
    exact ⟨fun hh ↦ ⟨hh.2, hh.1⟩, fun hh ↦ ⟨hh.2, hh.1⟩⟩
  rw [hset]
  have hx := h x
  rwa [Nat.card_eq_fintype_card, Fintype.card_subtype] at hx

/-! ## 6.  The parity of the switching count, from the parities of the stars -/

section Parity

variable {yt : Fin p → ℚ}

/-- The odd classes of a star, counted in the fibre rather than in the star. -/
theorem card_star_isOdd_eq (hy : Nondegenerate yt) (w : Regrowth core yt degree) :
    Nat.card {s : GeometricStar.Star hy w // (GeometricStar.Star.toFibre s).IsOdd} =
      Nat.card {c : GeometricFibre core yt degree //
        GeometricStar.IsStarClass hy w c ∧ c.IsOdd} :=
  Nat.card_congr
    ((Equiv.subtypeEquiv (GeometricStar.Star.equivSubtype hy w) fun _ ↦ Iff.rfl).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _))

/-- **The star decomposition of the odd wall classes, in parity.**  If every
star at the wall request carries an even number of odd classes, so does the set
of all odd wall classes.  The sum over the stars is taken by
`even_card_of_even_blocks`: the blocks of `SameStar` that meet the wall classes
are exactly the stars (`sameStar_of_isStarClass`, `sameLimit_of_isStarClass`),
and the remaining block contains no wall class. -/
theorem even_card_oddWallClasses_of_even_stars (hy : Nondegenerate yt)
    (hstar : ∀ w : Regrowth core yt degree,
      Even (Nat.card {c : GeometricFibre core yt degree //
        GeometricStar.IsStarClass hy w c ∧ c.IsOdd})) :
    Even (Nat.card {c : GeometricFibre core yt degree //
      c.IsOdd ∧ IsWallClass core degree yt c}) := by
  refine even_card_of_even_blocks (SameStar hy) _ ?_
  intro x
  by_cases hx : IsWallClass core degree yt x
  · obtain ⟨w, hw⟩ := (isWallClass_iff_exists_star hy x).mp hx
    have hEq : Nat.card {c : GeometricFibre core yt degree //
          (SameStar hy).r c x ∧ (c.IsOdd ∧ IsWallClass core degree yt c)} =
        Nat.card {c : GeometricFibre core yt degree //
          GeometricStar.IsStarClass hy w c ∧ c.IsOdd} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun c ↦ ?_)
      constructor
      · rintro ⟨hrel, hodd, -⟩
        exact ⟨(hrel w).mpr hw, hodd⟩
      · rintro ⟨hc, hodd⟩
        exact ⟨sameStar_of_isStarClass hy hc hw, hodd,
          (isWallClass_iff_exists_star hy c).mpr ⟨w, hc⟩⟩
    rw [hEq]
    exact hstar w
  · have hempty : IsEmpty {c : GeometricFibre core yt degree //
        (SameStar hy).r c x ∧ (c.IsOdd ∧ IsWallClass core degree yt c)} := by
      constructor
      rintro ⟨c, hrel, -, hwc⟩
      obtain ⟨w, hw⟩ := (isWallClass_iff_exists_star hy c).mp hwc
      exact hx ((isWallClass_iff_exists_star hy x).mpr ⟨w, (hrel w).mp hw⟩)
    rw [Nat.card_of_isEmpty]
    exact ⟨0, rfl⟩

end Parity

/-! ## 7.  The bridge, assembled -/

/-- **The bridge at one wall.**  At an isolated codimension-one wall
of a segment, if every star of the wall request carries an even number of odd
classes then the switching count across the wall is even. -/
theorem even_switchingCount_of_even_stars {y₀ y₁ : Fin p → ℚ} {a t b : ℚ}
    (hat : a < t) (htb : t < b)
    (hsimple : SimpleAt core degree y₀ y₁ t) (hiso : Isolated core degree y₀ y₁ a t b)
    (hy : Nondegenerate (RationalAffineWall.segment y₀ y₁ t))
    (hstar : ∀ w : Regrowth core (RationalAffineWall.segment y₀ y₁ t) degree,
      Even (Nat.card {c : GeometricFibre core (RationalAffineWall.segment y₀ y₁ t) degree //
        GeometricStar.IsStarClass hy w c ∧ c.IsOdd})) :
    Even (CountTransportLink.switchingCount core degree
      (RationalAffineWall.segment y₀ y₁ a) (RationalAffineWall.segment y₀ y₁ b)) := by
  rw [switchingCount_eq_card_oddWallClasses hat htb hsimple hiso]
  exact even_card_oddWallClasses_of_even_stars hy hstar

/-- **The same, as the `CountLink` the schedule consumes.** -/
theorem countLink_of_even_stars {y₀ y₁ : Fin p → ℚ} {a t b : ℚ}
    (hat : a < t) (htb : t < b)
    (hsimple : SimpleAt core degree y₀ y₁ t) (hiso : Isolated core degree y₀ y₁ a t b)
    (hy : Nondegenerate (RationalAffineWall.segment y₀ y₁ t))
    (hstar : ∀ w : Regrowth core (RationalAffineWall.segment y₀ y₁ t) degree,
      Even (Nat.card {c : GeometricFibre core (RationalAffineWall.segment y₀ y₁ t) degree //
        GeometricStar.IsStarClass hy w c ∧ c.IsOdd})) :
    CountTransportLink.CountLink degree core (RationalAffineWall.segment y₀ y₁ a) core
      (RationalAffineWall.segment y₀ y₁ b) :=
  (CountTransportLink.countLink_iff_even_switchingCount core degree _ _).mpr
    (even_switchingCount_of_even_stars hat htb hsimple hiso hy hstar)

/-- **The bridge in the shape `CountSchedule.Schedule.transport`'s `link` binder
asks for**, with the two hypotheses the
schedule does not itself carry named explicitly: codimension one at the wall,
and nondegeneracy of the wall request. -/
theorem schedule_countLink_of_even_stars (S : CountSchedule.Schedule core degree) {a t b : ℚ}
    (hat : a < t) (htb : t < b)
    (hsimple : SimpleAt core degree S.source S.target t)
    (hiso : ∀ u, CountSchedule.IsWall core degree S.source S.target u → a ≤ u → u ≤ b → u = t)
    (hy : Nondegenerate (S.request t))
    (hstar : ∀ w : Regrowth core (S.request t) degree,
      Even (Nat.card {c : GeometricFibre core (S.request t) degree //
        GeometricStar.IsStarClass hy w c ∧ c.IsOdd})) :
    CountTransportLink.CountLink degree core (S.request a) core (S.request b) :=
  countLink_of_even_stars hat htb hsimple hiso hy hstar

/-- **The same, with the star parity stated on `GeometricStar.Star` itself.** -/
theorem schedule_countLink_of_even_star_card (S : CountSchedule.Schedule core degree) {a t b : ℚ}
    (hat : a < t) (htb : t < b)
    (hsimple : SimpleAt core degree S.source S.target t)
    (hiso : ∀ u, CountSchedule.IsWall core degree S.source S.target u → a ≤ u → u ≤ b → u = t)
    (hy : Nondegenerate (S.request t))
    (hstar : ∀ w : Regrowth core (S.request t) degree,
      Even (Nat.card {s : GeometricStar.Star hy w // (GeometricStar.Star.toFibre s).IsOdd})) :
    CountTransportLink.CountLink degree core (S.request a) core (S.request b) :=
  schedule_countLink_of_even_stars S hat htb hsimple hiso hy
    fun w ↦ (card_star_isOdd_eq hy w) ▸ hstar w

/-! ## 8.  The codimension-one hypothesis is achievable, and where it comes from -/

/-- **Codimension one transfers from the normal-form family to every frame.**
A frame isomorphism over the core carries coordinates along a permutation of the
columns at *every* request, so a wall of a frame at `t` is a wall of its
normal form at `t`. -/
theorem simpleAtFrame_of_nf {y₀ y₁ : Fin p → ℚ} (t : ℚ)
    (hnf : ∀ (r : SegmentWalls.NFFrame core degree) (col col' : Fin p),
      r.toFrame.IsWallParam y₀ y₁ col t → r.toFrame.IsWallParam y₀ y₁ col' t → col = col')
    (k : Frame core degree) : SimpleAtFrame k y₀ y₁ t := by
  intro col col' hcol hcol'
  obtain ⟨r, hr⟩ := SegmentWalls.exists_nfFrame (k.member y₀)
  obtain ⟨fi⟩ := (SegmentWalls.isoOverCore_member_iff r.toFrame k y₀).mp
    (FibreMember.cls_eq_cls_iff.mp hr)
  have h1 : r.toFrame.IsWallParam y₀ y₁ (fi.symm.column col) t := by
    show r.toFrame.coordsAt (RationalAffineWall.segment y₀ y₁ t) (fi.symm.column col) = 0
    rw [fi.symm.coordsAt_column]
    exact hcol
  have h2 : r.toFrame.IsWallParam y₀ y₁ (fi.symm.column col') t := by
    show r.toFrame.coordsAt (RationalAffineWall.segment y₀ y₁ t) (fi.symm.column col') = 0
    rw [fi.symm.coordsAt_column]
    exact hcol'
  exact fi.symm.column.injective (hnf r _ _ h1 h2)

/-- **`SimpleAt` is exactly `SegmentWalls.exists_generic_start`'s output**, read
over the whole fibre through the normal-form family. -/
theorem simpleAt_of_genericStart {y₀ y₁ : Fin p → ℚ}
    (hdiff : ∀ (r : SegmentWalls.NFFrame core degree) (col : Fin p),
      r.toFrame.coordsAt y₀ col ≠ r.toFrame.coordsAt y₁ col)
    (hsimp : ∀ r : SegmentWalls.NFFrame core degree,
      RationalAffineWall.SimpleAlong r.toFrame.coordWall y₀ y₁)
    (t : ℚ) : SimpleAt core degree y₀ y₁ t := fun k ↦
  simpleAtFrame_of_nf t
    (fun r col col' h h' ↦
      SegmentWalls.col_eq_of_isWallParam
        (fun r : SegmentWalls.NFFrame core degree ↦ r.toFrame) y₀ y₁ r
        (fun c ↦ by
          rw [Frame.eval_coordWall, Frame.eval_coordWall]
          exact hdiff r c)
        (hsimp r) h h')
    k

/-- **A segment that is codimension one at every parameter exists**, provided
the *finish* is general: choose the start after the finish is known.  This is
the precise sense in which `SimpleAt` costs nothing -- and the precise sense in
which `CountSchedule.Schedule`, whose `target` is unconstrained and whose
`source` is chosen without reference to it, does not supply it. -/
theorem exists_simple_generic_start (core : Core n p) (degree : ℕ) (y₁ : Fin p → ℚ)
    (hy₁ : ∀ (k : Frame core degree) (col : Fin p), k.coordsAt y₁ col ≠ 0)
    (base : Fin p → ℚ) (hbase : ∀ i, 0 < base i) :
    ∃ y₀ : Fin p → ℚ, (∀ i, 0 < y₀ i) ∧
      (∀ (k : Frame core degree) (col : Fin p), k.coordsAt y₀ col ≠ 0) ∧
      ∀ t : ℚ, SimpleAt core degree y₀ y₁ t := by
  classical
  let _ : Fintype (SegmentWalls.NFFrame core degree) := Fintype.ofFinite _
  obtain ⟨y₀, hpos, hgen, hdiff, hsimp⟩ :=
    SegmentWalls.exists_generic_start
      (fun r : SegmentWalls.NFFrame core degree ↦ r.toFrame) y₁
      (fun r col ↦ hy₁ _ col) base hbase
  exact ⟨y₀, hpos, SegmentWalls.coordsAt_ne_zero_of_nf y₀ hgen,
    fun t ↦ simpleAt_of_genericStart hdiff hsimp t⟩

/-! ## 9.  The nondegeneracy hypothesis: where it holds and where it fails -/

/-- **The wall request is nondegenerate when both endpoints are positive and the
parameter lies in `[0, 1]`.** -/
theorem nondegenerate_segment {y₀ y₁ : Fin p → ℚ} (h₀ : ∀ i, 0 < y₀ i) (h₁ : ∀ i, 0 < y₁ i)
    {t : ℚ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Nondegenerate (RationalAffineWall.segment y₀ y₁ t) := by
  intro s
  have hA := h₀ s
  have hB := h₁ s
  show 0 < y₀ s + t * (y₁ s - y₀ s)
  rcases eq_or_lt_of_le ht1 with h | h
  · rw [h]; linarith
  · linarith [mul_nonneg ht0 hB.le, mul_pos (sub_pos.mpr h) hA]

/-- **Every wall of the caterpillar frame is a degeneration of the request
itself.**  The caterpillar frame's coordinate in a column is the requested slot
length divided by a positive diagonal entry, so it vanishes exactly when the
slot length does.  At such a parameter `GeometricStar.Star` is not defined. -/
theorem not_nondegenerate_of_catFrame_isWallParam (m : ℕ) (col : Fin (6 * m + 3))
    (y₀ y₁ : Fin (6 * m + 3) → ℚ) (t : ℚ)
    (h : (SegmentWalls.catFrame m).IsWallParam y₀ y₁ col t) :
    ¬ Nondegenerate (RationalAffineWall.segment y₀ y₁ t) := by
  intro hy
  have h' : RationalAffineWall.segment y₀ y₁ t col / FibreCaterpillar.catDiag m col = 0 := by
    rw [← SegmentWalls.coordsAt_catFrame_apply]
    exact h
  have hpos := hy col
  have hd := FibreCaterpillar.catDiag_pos m col
  rcases div_eq_zero_iff.mp h' with h'' | h''
  · exact absurd h'' (ne_of_gt hpos)
  · exact absurd h'' (ne_of_gt hd)

/-- **The caterpillar frame contributes no wall at a nondegenerate request.**
The contrapositive of the previous lemma: inside the positive orthant the
caterpillar frame's coordinates are all positive multiples of slot lengths. -/
theorem catFrame_not_isWallParam_of_nondegenerate (m : ℕ) (col : Fin (6 * m + 3))
    (y₀ y₁ : Fin (6 * m + 3) → ℚ) (t : ℚ)
    (hy : Nondegenerate (RationalAffineWall.segment y₀ y₁ t)) :
    ¬ (SegmentWalls.catFrame m).IsWallParam y₀ y₁ col t :=
  fun h ↦ not_nondegenerate_of_catFrame_isWallParam m col y₀ y₁ t h hy

/-! ## 10.  The bounded schedule: the link binder may be restricted to `[0, 1]` -/

/-- **`CountSchedule.transport_of_finite_walls`, with the crossing hypothesis
bounded.**  The schedule never leaves `[lo, s]`, so the wall-crossing input may
be assumed only there.  This is the restatement a link binder needs before it can
be restricted to `0 ≤ a` and `b ≤ 1`; the proof is
the original induction with the bound threaded through it, so nothing about the
schedule changes. -/
theorem transport_of_finite_walls_bounded (W : Finset ℚ) (P : ℚ → Prop) (lo s : ℚ)
    (hconst : ∀ a b : ℚ, a ≤ b → (∀ t ∈ W, ¬ (a ≤ t ∧ t ≤ b)) → (P a ↔ P b))
    (hcross : ∀ a t b : ℚ, lo ≤ a → a < t → t < b → b ≤ s → t ∈ W →
      (∀ u ∈ W, a ≤ u → u ≤ b → u = t) → (P a ↔ P b))
    (hs : s ∉ W) :
    ∀ k : ℕ, ∀ a : ℚ, lo ≤ a → a ∉ W → a ≤ s →
      (W.filter (fun t ↦ a < t ∧ t ≤ s)).card ≤ k → (P a ↔ P s) := by
  classical
  intro k
  induction k with
  | zero =>
    intro a _ ha hle hcard
    refine hconst a s hle ?_
    intro t ht ⟨h1, h2⟩
    have hmem : t ∈ W.filter (fun t ↦ a < t ∧ t ≤ s) := by
      refine Finset.mem_filter.mpr ⟨ht, ?_, h2⟩
      rcases lt_or_eq_of_le h1 with h | h
      · exact h
      · exact absurd (h ▸ ht) ha
    have := Finset.card_pos.mpr ⟨t, hmem⟩
    omega
  | succ k ih =>
    intro a hlo ha hle hcard
    set F := W.filter (fun t ↦ a < t ∧ t ≤ s) with hF
    by_cases hEmpty : F = ∅
    · refine hconst a s hle ?_
      intro t ht ⟨h1, h2⟩
      have hmem : t ∈ F := by
        refine Finset.mem_filter.mpr ⟨ht, ?_, h2⟩
        rcases lt_or_eq_of_le h1 with h | h
        · exact h
        · exact absurd (h ▸ ht) ha
      rw [hEmpty] at hmem
      exact absurd hmem (Finset.notMem_empty t)
    · have hne : F.Nonempty := Finset.nonempty_of_ne_empty hEmpty
      set t₀ := F.min' hne with ht₀
      have ht₀F : t₀ ∈ F := F.min'_mem hne
      have ht₀W : t₀ ∈ W := (Finset.mem_filter.mp ht₀F).1
      have ht₀a : a < t₀ := (Finset.mem_filter.mp ht₀F).2.1
      have ht₀s : t₀ ≤ s := (Finset.mem_filter.mp ht₀F).2.2
      have ht₀lt : t₀ < s := lt_of_le_of_ne ht₀s (fun h ↦ hs (h ▸ ht₀W))
      set G := W.filter (fun t ↦ t₀ < t ∧ t ≤ s) with hG
      set b : ℚ := if hG' : G.Nonempty then (t₀ + G.min' hG') / 2 else s with hb
      have hbt₀ : t₀ < b := by
        rw [hb]
        split
        · next hG' =>
          have h := (Finset.mem_filter.mp (G.min'_mem hG')).2.1
          linarith
        · exact ht₀lt
      have hbs : b ≤ s := by
        rw [hb]
        split
        · next hG' =>
          have hm := G.min'_mem hG'
          have h1 := (Finset.mem_filter.mp hm).2.1
          have h2 := (Finset.mem_filter.mp hm).2.2
          linarith
        · exact le_refl s
      have hbW : b ∉ W := by
        rw [hb]
        split
        · next hG' =>
          intro hmem
          have hm := G.min'_mem hG'
          have h1 := (Finset.mem_filter.mp hm).2.1
          have h2 := (Finset.mem_filter.mp hm).2.2
          have hin : (t₀ + G.min' hG') / 2 ∈ G :=
            Finset.mem_filter.mpr ⟨hmem, by linarith, by linarith⟩
          have := G.min'_le _ hin
          linarith
        · exact hs
      have hOnly : ∀ u ∈ W, a ≤ u → u ≤ b → u = t₀ := by
        intro u hu hau hub
        have hua : a < u := by
          rcases lt_or_eq_of_le hau with h | h
          · exact h
          · exact absurd (h ▸ hu) ha
        have huF : u ∈ F := Finset.mem_filter.mpr ⟨hu, hua, le_trans hub hbs⟩
        rcases lt_or_eq_of_le (F.min'_le _ huF) with h | h
        · exfalso
          have huG : u ∈ G := Finset.mem_filter.mpr ⟨hu, h, le_trans hub hbs⟩
          rw [hb] at hub
          split at hub
          · next hG' =>
            have hle' := G.min'_le _ huG
            have h1 := (Finset.mem_filter.mp (G.min'_mem hG')).2.1
            linarith
          · next hG' => exact hG' ⟨u, huG⟩
        · exact h.symm
      refine (hcross a t₀ b hlo ht₀a hbt₀ hbs ht₀W hOnly).trans
        (ih b (by linarith) hbW hbs ?_)
      have hsub : W.filter (fun t ↦ b < t ∧ t ≤ s) ⊆ F := by
        intro u hu
        rw [Finset.mem_filter] at hu ⊢
        exact ⟨hu.1, by linarith [hu.2.1], hu.2.2⟩
      have hnotin : t₀ ∉ W.filter (fun t ↦ b < t ∧ t ≤ s) := by
        intro hmem
        have := (Finset.mem_filter.mp hmem).2.1
        linarith
      have hlt : (W.filter (fun t ↦ b < t ∧ t ≤ s)).card < F.card :=
        Finset.card_lt_card ⟨hsub, fun hcon ↦ hnotin (hcon ht₀F)⟩
      omega

/-- **The schedule transport, with the link binder bounded.**  The
schedule's own induction never leaves `[0, 1]`, so a link supplied only for
`0 ≤ a` and `b ≤ 1` carries the count from the schedule's start to its finish.
This is what lets the star hypothesis be asked for only at requests that are
actual convex combinations of the two endpoints. -/
theorem schedule_transport_bounded (S : CountSchedule.Schedule core degree)
    (link : ∀ a t b : ℚ, 0 ≤ a → a < t → t < b → b ≤ 1 →
      CountSchedule.IsWall core degree S.source S.target t →
      (∀ u, CountSchedule.IsWall core degree S.source S.target u → a ≤ u → u ≤ b → u = t) →
      CountTransportLink.CountLink degree core (S.request a) core (S.request b))
    (hgen : ∀ (k : Frame core degree) (col : Fin p), k.coordsAt S.target col ≠ 0) :
    CountTransportLink.CountLink degree core S.source core S.target := by
  classical
  have h := transport_of_finite_walls_bounded S.walls
    (fun t ↦ Odd (GeometricFibre.openOddCount core (S.request t) degree)) 0 1
    (by
      intro u v huv hno
      have hmin : min u v = u := min_eq_left huv
      have hmax : max u v = v := max_eq_right huv
      rw [S.openOddCount_eq_of_no_wall_between (a := u) (b := v)
        (by rw [hmin, hmax]; exact hno)])
    (by
      intro u t v hlo hut htv hv1 htW hOnly
      exact link u t v hlo hut htv hv1 (S.mem_walls.mp htW)
        fun w hw h1 h2 ↦ hOnly w (S.mem_walls.mpr hw) h1 h2)
    (fun h ↦ (S.one_notMem_walls hgen) h)
    _ 0 le_rfl S.zero_notMem_walls zero_le_one (le_refl _)
  rwa [S.request_zero, S.request_one] at h

/-- **The in-cone parity, assembled.**  Over a schedule whose
two endpoints are positive, whose finish is general, and whose segment is
codimension one at every parameter, the parity of the count carries from start
to finish as soon as every star at every interior wall request carries an even
number of odd classes.

This is the in-cone parity at one schedule, with
exactly one obligation left -- the per-star parity, proved in the star
exhaustion modules -- and with the two structural hypotheses the schedule does
not itself carry named: `hsimple` (codimension one, available from
`exists_simple_generic_start` when the start is chosen after the finish) and
positivity of both endpoints (which is what makes the star defined at all). -/
theorem countLink_source_target_of_even_stars (S : CountSchedule.Schedule core degree)
    (hsrc : ∀ i, 0 < S.source i) (htgt : ∀ i, 0 < S.target i)
    (hgen : ∀ (k : Frame core degree) (col : Fin p), k.coordsAt S.target col ≠ 0)
    (hsimple : ∀ t : ℚ, SimpleAt core degree S.source S.target t)
    (hstar : ∀ (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (w : Regrowth core (S.request t) degree),
      Even (Nat.card {c : GeometricFibre core (S.request t) degree //
        GeometricStar.IsStarClass (nondegenerate_segment hsrc htgt ht0 ht1) w c ∧ c.IsOdd})) :
    CountTransportLink.CountLink degree core S.source core S.target := by
  refine schedule_transport_bounded S (fun a t b hlo hat htb hb1 _ hiso ↦ ?_) hgen
  exact countLink_of_even_stars hat htb (hsimple t) hiso
    (nondegenerate_segment hsrc htgt (le_trans hlo hat.le) (le_trans htb.le hb1))
    (hstar t (le_trans hlo hat.le) (le_trans htb.le hb1))

end DraismaVargas.Count.WallSwitchingBridge
