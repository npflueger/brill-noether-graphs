import DraismaVargasCount.StepSupplyGenusSix
import DraismaVargasCount.WallSwitchingBridge

/-!
# The propagation: simple positive walls, positive type changes, and the chain

**Source.**  Vargas, Part II (arXiv:2609.09109), the proof of the main theorem
(`sec-proof-main-theorems`): a general path from the caterpillar base to any general metric
graph crosses the walls of the fibre one at a time (`proposition-generic-path`), and the
count is invariant across each crossing (`proposition-walking-through-II`).

This file states the two hypotheses of the propagation (step 4 of the genus-six assembly)
and derives from them the parity of the open odd count over every connected cubic core:

* `InConeSupplySimple` -- crossing a wall of codimension one on a segment of strictly
  positive requests over one core preserves the parity of the open odd count.  At genus six
  this is step 2 of the assembly (`Assembly.trivalentWalls_genusSix`).
* `TypeChangeSupplyPositive` -- across every Whitehead move between cores there are
  positive general requests on the two sides whose open odd counts have the same parity.
  At genus six this is step 3 (`Assembly.typeChanges_genusSix`).

`c34_of_base_positive` combines them with a base count, and is what `Assembly.c34_genusSix`
applies.

## Why the hypotheses have this shape

`InConeSupplySimple` carries exactly what the star argument of
`WallSwitchingBridge.countLink_source_target_of_even_stars` needs:

* `SimpleAt` at the wall parameter -- codimension one.  An isolated wall parameter need not
  be simple: two columns of one frame can vanish together at a nondegenerate wall request
  between strictly positive endpoints, so this is a genuine restriction;
* both endpoints strictly positive -- which is what makes
  `WallStar.Nondegenerate` hold at the wall request, hence what makes
  `GeometricStar.Star` defined there at all.  Positivity cannot be dropped anyway: the count
  vanishes off the positive orthant (`OpenAtPositivity.openOddCount_eq_zero_of_nonpos`);
* `0 ≤ a` and `b ≤ 1` -- the bounded binder of
  `WallSwitchingBridge.schedule_transport_bounded`, which is free.

The price is paid on the type-change half.  `countLink_of_positiveGeneral`
routes two general requests through a **hub** rather than along the segment
between them, because the segment between two *given* general requests need not be
codimension one and `exists_simple_hub` chooses the hub after both finishes are
known.  The hub is positive, so for the two links to be available the two
finishes must be positive too, and positivity therefore has to be carried along
the Whitehead chain.  That is why `TypeChangeSupplyPositive` asks for its two chosen
requests to be **positive** general rather than merely general.  `CountSchedule.C34`
carries positivity of the request in its own binder, which is why `c34_genusSix_simple`
below is `CountSchedule.C34 2` verbatim.

## What is proved here

* `generic_of_avoid`, `exists_generic_start_two` -- `SegmentWalls.exists_generic_start`
  for **two** finishes at once: one start, generic and simple along the segment
  to each of them.  The proof is the original one with the exceptional family
  doubled; the index type is still finite, so `exists_avoids_preserving_positive`
  applies unchanged.  `exists_generic_start` chooses the start after **one** finish.
* `exists_simple_hub` -- the same over the whole fibre, in the form
  `WallSwitchingBridge.SimpleAt` wants.
* `PositiveGeneral`, `exists_positiveGeneral`, `InConeSupplySimple`,
  `inConeSupplySimple_of_even_stars`, `TypeChangeSupplyPositive` -- the two hypotheses, and
  the record that the star parity at every wall discharges the in-cone one through
  `WallSwitchingBridge.countLink_of_even_stars`.
* `negCoordWall`, `exists_general_positive_neg_coord`, `exists_simple_start_pos_coord`,
  `opposite_signs_of_mid_zero` -- tools for producing simple walls between positive
  requests: a general positive request keeping one coordinate negative, a simple start
  keeping it positive, and the opposite signs forced at the two ends of a segment whose
  midpoint zeroes a coordinate.
* `countLink_of_positiveGeneral`, `odd_indep_of_positiveGeneral` -- the in-cone
  half, through the hub.
* `step_positiveGeneral`, `exists_siteChain_positive`,
  `odd_of_positiveGeneral`, `odd_of_base_positive`, `c34_of_base_positive` --
  the chain of `StepSupplyReduction`, with positivity carried.
* `c34_genusSix_simple` -- **`CountSchedule.C34 2` itself**, from
  `InConeSupplySimple`, `TypeChangeSupplyPositive`, the genus bound and one
  ballot classification at one positive general request over the caterpillar.

## What is not proved here

* **`InConeSupplySimple` is not proved here.**  At genus six it is
  `StarSupplyAssembly.inConeSupplySimple_genusSix`, from the star parity at each of the ten
  wall types (step 2 of the assembly).
* **`TypeChangeSupplyPositive` is not proved here**; it asks the prover of a type change to
  choose its two requests strictly positive.  `FacetMachine.positiveGeneral_facetRequest`
  shows that the facet requests `facetRequest e₀ y₀ ε` are positive and general at every
  core where they are stable, and at genus six the hypothesis is
  `FacetCensus.typeChangeSupplyPositive_of_metricCensus` with `CensusAssembly` (step 3 of
  the assembly).
* **The genus bound `2 ≤ p + 1 - n`** and **the ballot classification** are hypotheses of
  `c34_genusSix_simple`, exactly as in `Count/StepSupplyGenusSix.lean`.  The genus-six
  assembly does not go through `c34_genusSix_simple`: it applies `c34_of_base_positive`
  with the base count of `CaterpillarAllMembers`.
* The base request is required positive, which `exists_positiveGeneral` supplies with no
  hypothesis.
* Nothing here is about the unrestricted `CoreChainSites.StepSupply`.

## Consumers

The genus-six assembly applies `c34_of_base_positive` (`Assembly.c34_genusSix`).
`c34_genusSix_simple` is the entry point of the facet-parity routes (`FacetMachine`,
`FacetParityPilot`).
-/

namespace DraismaVargas.Count.SimpleWallSupply

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore Step CoreIso)
open DraismaVargas.Count.CoreRelabel (Relabel)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.StepSupplyReduction (GeneralRequest)

variable {n p degree : ℕ} {core : Core n p}

/-! ## 1.  A start that is generic and simple towards two finishes at once -/

/-- The extraction half of `SegmentWalls.exists_generic_start`, separated from
the choice of the start so that it can be applied to each of several finishes
against **one** avoidance condition. -/
theorem generic_of_avoid {ι : Type} (frames : ι → Frame core degree) (y₁ y₀ : Fin p → ℚ)
    (havoid : ∀ e : SegmentWalls.SegmentException ι p,
      (SegmentWalls.segmentException frames y₁ e).eval y₀ ≠ 0) :
    (∀ i col, (frames i).coordsAt y₀ col ≠ 0) ∧
      (∀ i col, (frames i).coordsAt y₀ col ≠ (frames i).coordsAt y₁ col) ∧
      (∀ i, RationalAffineWall.SimpleAlong ((frames i).coordWall) y₀ y₁) := by
  have hgeneral : ∀ i col, (frames i).coordsAt y₀ col ≠ 0 := by
    intro i col
    have h := havoid (Sum.inl (i, col))
    rwa [show SegmentWalls.segmentException frames y₁ (Sum.inl (i, col)) =
      (frames i).coordWall col from rfl, Frame.eval_coordWall] at h
  have hdiff : ∀ i col,
      ((frames i).coordWall col).eval y₀ ≠ ((frames i).coordWall col).eval y₁ := by
    intro i col hEq
    refine havoid (Sum.inr (Sum.inl (i, col))) ?_
    show (((frames i).coordWall col).endpointDifference y₁).eval y₀ = 0
    rw [RationalAffineWall.eval_endpointDifference, hEq, sub_self]
  refine ⟨hgeneral, ?_, ?_⟩
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

/-- **`SegmentWalls.exists_generic_start` for two finishes at once.**  Given two
general endpoints, every positive orthant contains a single general start whose
segment to **each** of them is nondegenerate on every coordinate wall and, for
each frame separately, simple.  The exceptional family is the disjoint union of
the two single-finish families, which is still finite, so nothing about the
avoidance argument changes. -/
theorem exists_generic_start_two {ι : Type} [Fintype ι] (frames : ι → Frame core degree)
    (y₁ y₂ : Fin p → ℚ)
    (hy₁ : ∀ i col, (frames i).coordsAt y₁ col ≠ 0)
    (hy₂ : ∀ i col, (frames i).coordsAt y₂ col ≠ 0)
    (base : Fin p → ℚ) (hbase : ∀ i, 0 < base i) :
    ∃ y₀ : Fin p → ℚ, (∀ i, 0 < y₀ i) ∧
      (∀ i col, (frames i).coordsAt y₀ col ≠ 0) ∧
      (∀ i col, (frames i).coordsAt y₀ col ≠ (frames i).coordsAt y₁ col) ∧
      (∀ i, RationalAffineWall.SimpleAlong ((frames i).coordWall) y₀ y₁) ∧
      (∀ i col, (frames i).coordsAt y₀ col ≠ (frames i).coordsAt y₂ col) ∧
      (∀ i, RationalAffineWall.SimpleAlong ((frames i).coordWall) y₀ y₂) := by
  classical
  obtain ⟨y₀, hpos, havoid⟩ :=
    RationalAffineWall.exists_avoids_preserving_positive
      (Sum.elim (SegmentWalls.segmentException frames y₁)
        (SegmentWalls.segmentException frames y₂))
      SegmentWalls.coordinateWall base
      (by
        rintro (e | e)
        · exact SegmentWalls.segmentException_proper frames y₁ hy₁ e
        · exact SegmentWalls.segmentException_proper frames y₂ hy₂ e)
      (by intro l; rw [SegmentWalls.eval_coordinateWall]; exact hbase l)
  obtain ⟨hgen, hdiff₁, hsimp₁⟩ := generic_of_avoid frames y₁ y₀ fun e ↦ havoid (Sum.inl e)
  obtain ⟨-, hdiff₂, hsimp₂⟩ := generic_of_avoid frames y₂ y₀ fun e ↦ havoid (Sum.inr e)
  refine ⟨y₀, fun l ↦ ?_, hgen, hdiff₁, hsimp₁, hdiff₂, hsimp₂⟩
  have h := hpos l
  rwa [SegmentWalls.eval_coordinateWall] at h

/-- **The hub.**  Two general requests over one core have a common start that is
strictly positive, general for the whole fibre, and codimension one along the
segment to each of them.  This is what `Count/WallSwitchingBridge.lean`'s
`exists_simple_generic_start` cannot give: it chooses the start after a single
finish, so it links a *chosen* pair, not a given one. -/
theorem exists_simple_hub (core : Core n p) (degree : ℕ) (y₁ y₂ : Fin p → ℚ)
    (hy₁ : ∀ (k : Frame core degree) (col : Fin p), k.coordsAt y₁ col ≠ 0)
    (hy₂ : ∀ (k : Frame core degree) (col : Fin p), k.coordsAt y₂ col ≠ 0)
    (base : Fin p → ℚ) (hbase : ∀ i, 0 < base i) :
    ∃ z : Fin p → ℚ, (∀ i, 0 < z i) ∧
      (∀ (k : Frame core degree) (col : Fin p), k.coordsAt z col ≠ 0) ∧
      (∀ t : ℚ, WallSwitchingBridge.SimpleAt core degree z y₁ t) ∧
      (∀ t : ℚ, WallSwitchingBridge.SimpleAt core degree z y₂ t) := by
  classical
  let _ : Fintype (SegmentWalls.NFFrame core degree) := Fintype.ofFinite _
  obtain ⟨z, hpos, hgen, hdiff₁, hsimp₁, hdiff₂, hsimp₂⟩ :=
    exists_generic_start_two (fun r : SegmentWalls.NFFrame core degree ↦ r.toFrame)
      y₁ y₂ (fun _ col ↦ hy₁ _ col) (fun _ col ↦ hy₂ _ col) base hbase
  exact ⟨z, hpos, SegmentWalls.coordsAt_ne_zero_of_nf z hgen,
    fun t ↦ WallSwitchingBridge.simpleAt_of_genericStart hdiff₁ hsimp₁ t,
    fun t ↦ WallSwitchingBridge.simpleAt_of_genericStart hdiff₂ hsimp₂ t⟩

/-! ## 2.  The two hypotheses -/

/-- A request that is both strictly positive and general for the whole fibre. -/
def PositiveGeneral (core : Core n p) (degree : ℕ) (y : Fin p → ℚ) : Prop :=
  (∀ i, 0 < y i) ∧ GeneralRequest core degree y

theorem exists_positiveGeneral (core : Core n p) (degree : ℕ) :
    ∃ y : Fin p → ℚ, PositiveGeneral core degree y := by
  obtain ⟨y, hpos, hgen⟩ := StepSupplyReduction.exists_generalRequest core degree
  exact ⟨y, hpos, hgen⟩

/-- **The parity of the count across a simple positive wall.**  Over every core, on
every schedule whose two endpoints are strictly positive, crossing a wall parameter `t`
that is the only one in `[a, b] ⊆ [0, 1]` and is codimension one
(`WallSwitchingBridge.SimpleAt`) preserves the parity of the open odd count.  These are
exactly the conditions the star route can supply. -/
def InConeSupplySimple (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (S : CountSchedule.Schedule core degree) (a t b : ℚ),
    (∀ i, 0 < S.source i) → (∀ i, 0 < S.target i) →
    0 ≤ a → a < t → t < b → b ≤ 1 →
    CountSchedule.IsWall core degree S.source S.target t →
    (∀ u, CountSchedule.IsWall core degree S.source S.target u → a ≤ u → u ≤ b → u = t) →
    WallSwitchingBridge.SimpleAt core degree S.source S.target t →
      CountTransportLink.CountLink degree core (S.request a) core (S.request b)

/-- **The star route's output, in the shape `InConeSupplySimple` asks for.**
`WallSwitchingBridge.countLink_of_even_stars` discharges one wall of
`InConeSupplySimple` outright from the per-star parity at the wall; positivity of the
endpoints is what supplies its `Nondegenerate` hypothesis, and `SimpleAt` is available
because the definition carries it. -/
theorem inConeSupplySimple_of_even_stars
    (hstars : ∀ (core : Core n p) (S : CountSchedule.Schedule core degree) (t : ℚ)
      (hy : WallStar.Nondegenerate (S.request t))
      (w : WallStar.Regrowth core (S.request t) degree),
        Even (Nat.card {c : GeometricFibre core (S.request t) degree //
          GeometricStar.IsStarClass hy w c ∧ c.IsOdd})) :
    InConeSupplySimple degree n p := by
  intro core S a t b hsrc htgt hlo hat htb hb1 _ hiso hsimple
  exact WallSwitchingBridge.countLink_of_even_stars hat htb hsimple hiso
    (WallSwitchingBridge.nondegenerate_segment hsrc htgt (le_trans hlo hat.le)
      (le_trans htb.le hb1))
    (hstars core S t _)

/-- **The parity of the count across a type change, at positive general requests.**
Across every Whitehead step there are two positive general requests, one over each core,
whose open odd counts have the same parity.  This is what the hub route below has to be
handed. -/
def TypeChangeSupplyPositive (degree n p : ℕ) : Prop :=
  ∀ c c' : CubicCore n p, Step c c' →
    ∃ y y' : Fin p → ℚ, PositiveGeneral c.core degree y ∧ PositiveGeneral c'.core degree y' ∧
      CountTransportLink.CountLink degree c.core y c'.core y'

/-! ## 2b.  Tools for simple walls between positive requests -/

/-- One coordinate wall of a frame, negated, so that `0 < eval` says the
coordinate is strictly **negative**.  Used only as a *constraint* of
`RationalAffineWall.exists_avoids_preserving_positive`, never as an exceptional,
so no properness is needed. -/
noncomputable def negCoordWall (k : Frame core degree) (col : Fin p) :
    RationalAffineWall (Fin p) where
  coefficient s := -((k.coordWall col).coefficient s)
  constant := 0

theorem eval_negCoordWall (k : Frame core degree) (col : Fin p) (y : Fin p → ℚ) :
    (negCoordWall k col).eval y = -(k.coordsAt y col) := by
  rw [← Frame.eval_coordWall k col y]
  simp only [RationalAffineWall.eval, negCoordWall, Frame.coordWall, neg_mul, add_zero,
    Finset.sum_neg_distrib]

/-- **A general positive request keeping one coordinate negative.** -/
theorem exists_general_positive_neg_coord (k : Frame core degree) (col : Fin p)
    (base : Fin p → ℚ) (hbase : ∀ s, 0 < base s) (hneg : k.coordsAt base col < 0) :
    ∃ y : Fin p → ℚ, (∀ s, 0 < y s) ∧ k.coordsAt y col < 0 ∧
      ∀ (k' : Frame core degree) (c : Fin p), k'.coordsAt y c ≠ 0 := by
  classical
  let _ : Fintype (SegmentWalls.NFFrame core degree) := Fintype.ofFinite _
  obtain ⟨y, hcon, havoid⟩ :=
    RationalAffineWall.exists_avoids_preserving_positive
      (fun x : SegmentWalls.NFFrame core degree × Fin p ↦ x.1.toFrame.coordWall x.2)
      (Sum.elim SegmentWalls.coordinateWall (fun _ : Unit ↦ negCoordWall k col))
      base
      (fun x ↦ x.1.toFrame.coordWall_proper x.2)
      (by
        rintro (l | -)
        · rw [Sum.elim_inl, SegmentWalls.eval_coordinateWall]
          exact hbase l
        · rw [Sum.elim_inr, eval_negCoordWall]
          linarith)
  refine ⟨y, fun s ↦ ?_, ?_, ?_⟩
  · have h := hcon (Sum.inl s)
    rwa [Sum.elim_inl, SegmentWalls.eval_coordinateWall] at h
  · have h := hcon (Sum.inr ())
    rw [Sum.elim_inr, eval_negCoordWall] at h
    linarith
  · refine SegmentWalls.coordsAt_ne_zero_of_nf y ?_
    intro r c
    have h := havoid (r, c)
    rwa [Frame.eval_coordWall] at h

/-- **A start that is generic and simple towards a given finish and keeps one
coordinate positive.**  This is `SegmentWalls.exists_generic_start` with the one
extra strict inequality `0 < k.coordsAt · col` carried along. -/
theorem exists_simple_start_pos_coord (k : Frame core degree) (col : Fin p)
    (y₁ : Fin p → ℚ)
    (hy₁ : ∀ (k' : Frame core degree) (c : Fin p), k'.coordsAt y₁ c ≠ 0)
    (base : Fin p → ℚ) (hbase : ∀ s, 0 < base s) (hpos : 0 < k.coordsAt base col) :
    ∃ y₀ : Fin p → ℚ, (∀ s, 0 < y₀ s) ∧
      (∀ (k' : Frame core degree) (c : Fin p), k'.coordsAt y₀ c ≠ 0) ∧
      0 < k.coordsAt y₀ col ∧
      ∀ t : ℚ, WallSwitchingBridge.SimpleAt core degree y₀ y₁ t := by
  classical
  let _ : Fintype (SegmentWalls.NFFrame core degree) := Fintype.ofFinite _
  obtain ⟨y₀, hcon, havoid⟩ :=
    RationalAffineWall.exists_avoids_preserving_positive
      (SegmentWalls.segmentException
        (fun r : SegmentWalls.NFFrame core degree ↦ r.toFrame) y₁)
      (Sum.elim SegmentWalls.coordinateWall (fun _ : Unit ↦ k.coordWall col))
      base
      (SegmentWalls.segmentException_proper _ y₁ fun _ c ↦ hy₁ _ c)
      (by
        rintro (l | -)
        · rw [Sum.elim_inl, SegmentWalls.eval_coordinateWall]
          exact hbase l
        · rw [Sum.elim_inr, Frame.eval_coordWall]
          exact hpos)
  obtain ⟨hgen, hdiff, hsimp⟩ :=
    generic_of_avoid (fun r : SegmentWalls.NFFrame core degree ↦ r.toFrame) y₁ y₀ havoid
  refine ⟨y₀, fun s ↦ ?_, SegmentWalls.coordsAt_ne_zero_of_nf y₀ hgen, ?_,
    fun t ↦ WallSwitchingBridge.simpleAt_of_genericStart hdiff hsimp t⟩
  · have h := hcon (Sum.inl s)
    rwa [Sum.elim_inl, SegmentWalls.eval_coordinateWall] at h
  · have h := hcon (Sum.inr ())
    rwa [Sum.elim_inr, Frame.eval_coordWall] at h

/-- **A wall parameter whose midpoint vanishes forces opposite signs at the two
endpoints.** -/
theorem opposite_signs_of_mid_zero (k : Frame core degree) (col : Fin p)
    (y₀ y₁ : Fin p → ℚ)
    (hmid : k.coordsAt (RationalAffineWall.segment y₀ y₁ (1 / 2)) col = 0)
    (hne : k.coordsAt y₀ col ≠ 0) :
    (0 < k.coordsAt y₀ col ∧ k.coordsAt y₁ col < 0) ∨
      (0 < k.coordsAt y₁ col ∧ k.coordsAt y₀ col < 0) := by
  rw [Frame.coordsAt_segment] at hmid
  rcases lt_or_gt_of_ne hne with h | h
  · right; constructor <;> linarith
  · left; constructor <;> linarith

/-! ## 3.  The in-cone half, through the hub -/

/-- **The in-cone half, from the restated hypothesis.**  Two positive general
requests over one core are linked -- not along the segment between them, which
need not be codimension one, but through a hub chosen after both are known. -/
theorem countLink_of_positiveGeneral (h : InConeSupplySimple degree n p) (core : Core n p)
    {y₀ y₁ : Fin p → ℚ} (h₀ : PositiveGeneral core degree y₀)
    (h₁ : PositiveGeneral core degree y₁) :
    CountTransportLink.CountLink degree core y₀ core y₁ := by
  obtain ⟨z, hzpos, hzgen, hs₀, hs₁⟩ :=
    exists_simple_hub core degree y₀ y₁ h₀.2 h₁.2 (fun _ ↦ 1) fun _ ↦ one_pos
  have link₀ : CountTransportLink.CountLink degree core z core y₀ :=
    WallSwitchingBridge.schedule_transport_bounded ⟨z, y₀, hzgen⟩
      (fun a t b hlo hat htb hb1 hw hiso ↦
        h core ⟨z, y₀, hzgen⟩ a t b hzpos h₀.1 hlo hat htb hb1 hw hiso (hs₀ t)) h₀.2
  have link₁ : CountTransportLink.CountLink degree core z core y₁ :=
    WallSwitchingBridge.schedule_transport_bounded ⟨z, y₁, hzgen⟩
      (fun a t b hlo hat htb hb1 hw hiso ↦
        h core ⟨z, y₁, hzgen⟩ a t b hzpos h₁.1 hlo hat htb hb1 hw hiso (hs₁ t)) h₁.2
  exact CountTransportLink.countLink_trans (CountTransportLink.countLink_symm link₀) link₁

/-- **The parity of the count over a fixed core does not depend on which positive
general request is asked for.** -/
theorem odd_indep_of_positiveGeneral (h : InConeSupplySimple degree n p) (core : Core n p)
    {y₀ y₁ : Fin p → ℚ} (h₀ : PositiveGeneral core degree y₀)
    (h₁ : PositiveGeneral core degree y₁)
    (hodd : Odd (GeometricFibre.openOddCount core y₀ degree)) :
    Odd (GeometricFibre.openOddCount core y₁ degree) :=
  (countLink_of_positiveGeneral h core h₀ h₁).mp hodd

/-! ## 4.  The chain, carrying positivity -/

theorem step_positiveGeneral (hcone : InConeSupplySimple degree n p)
    (htype : TypeChangeSupplyPositive degree n p) {c c' : CubicCore n p} (hstep : Step c c')
    {y : Fin p → ℚ} (hy : PositiveGeneral c.core degree y) :
    ∃ y' : Fin p → ℚ, PositiveGeneral c'.core degree y' ∧
      CountTransportLink.CountLink degree c.core y c'.core y' := by
  obtain ⟨z, y', hz, hy', hlink⟩ := htype c c' hstep
  exact ⟨y', hy', CountTransportLink.countLink_trans
    (countLink_of_positiveGeneral hcone c.core hy hz) hlink⟩

theorem exists_siteChain_positive (hcone : InConeSupplySimple degree n p)
    (htype : TypeChangeSupplyPositive degree n p) {c c' : CubicCore n p}
    (h : Relation.ReflTransGen Step c c') {y : Fin p → ℚ}
    (hy : PositiveGeneral c.core degree y) :
    ∃ y' : Fin p → ℚ, PositiveGeneral c'.core degree y' ∧
      Relation.ReflTransGen (CountSchedule.Site.Link (degree := degree))
        (CoreChainSites.siteOf degree c y) (CoreChainSites.siteOf degree c' y') := by
  induction h with
  | refl => exact ⟨y, hy, Relation.ReflTransGen.refl⟩
  | tail _ hstep ih =>
      obtain ⟨u, hu, hchain⟩ := ih
      obtain ⟨v, hv, hlink⟩ := step_positiveGeneral hcone htype hstep hu
      exact ⟨v, hv, hchain.tail hlink⟩

/-! ## 5.  The headline -/

/-- **Oddness at every positive general request over every core of a chain**, from the two
hypotheses. -/
theorem odd_of_positiveGeneral (hcone : InConeSupplySimple degree n p)
    (htype : TypeChangeSupplyPositive degree n p) (hGenus : 2 ≤ p + 1 - n)
    (c c' : CubicCore n p) (y y' : Fin p → ℚ)
    (hy : PositiveGeneral c.core degree y) (hy' : PositiveGeneral c'.core degree y')
    (hodd : Odd (GeometricFibre.openOddCount c.core y degree)) :
    Odd (GeometricFibre.openOddCount c'.core y' degree) := by
  obtain ⟨c'', hchain, ⟨i⟩⟩ := CoreOfDarts.exists_chain c c' hGenus
  obtain ⟨z, hz, hsite⟩ := exists_siteChain_positive hcone htype hchain hy
  have hoddz : Odd (GeometricFibre.openOddCount c''.core z degree) :=
    CountSchedule.Site.odd_of_reflTransGen hsite hodd
  obtain ⟨d, -⟩ : ∃ d : Relabel c''.core c'.core, d = CoreRelabel.Relabel.ofCoreIso i :=
    ⟨_, rfl⟩
  obtain ⟨w, hwdef⟩ : ∃ w : Fin p → ℚ, w = fun e ↦ z (d.slot.symm e) := ⟨_, rfl⟩
  have hzw : ∀ e, w (d.slot e) = z e := by
    intro e
    rw [hwdef]
    exact congrArg z (d.slot.symm_apply_apply e)
  have hoddw : Odd (GeometricFibre.openOddCount c'.core w degree) :=
    CoreRelabel.openOddCount_relabel d hzw degree ▸ hoddz
  have hwpos : ∀ e, 0 < w e := by
    intro e
    rw [hwdef]
    exact hz.1 _
  exact odd_indep_of_positiveGeneral hcone c'.core
    ⟨hwpos, StepSupplyReduction.generalRequest_relabel d hzw hz.2⟩ hy' hoddw

/-- **The same, from a single base case.** -/
theorem odd_of_base_positive (hcone : InConeSupplySimple degree n p)
    (htype : TypeChangeSupplyPositive degree n p) (hGenus : 2 ≤ p + 1 - n)
    (base : CubicCore n p) (y₀ : Fin p → ℚ) (hy₀ : PositiveGeneral base.core degree y₀)
    (hodd : Odd (GeometricFibre.openOddCount base.core y₀ degree))
    (c : CubicCore n p) (y : Fin p → ℚ) (hy : PositiveGeneral c.core degree y) :
    Odd (GeometricFibre.openOddCount c.core y degree) :=
  odd_of_positiveGeneral hcone htype hGenus base c y₀ y hy₀ hy hodd

/-- **The conclusion of `CountSchedule.C34` at fixed `n`, `p` and `degree`**, from the two
hypotheses and a base count.  It uses the positivity of the request that
`CountSchedule.C34` carries. -/
theorem c34_of_base_positive (hcone : InConeSupplySimple degree n p)
    (htype : TypeChangeSupplyPositive degree n p) (hGenus : 2 ≤ p + 1 - n)
    (base : CubicCore n p) (y₀ : Fin p → ℚ) (hy₀ : ∀ i, 0 < y₀ i)
    (hgen₀ : ∀ (k : Frame base.core degree) (col : Fin p), k.coordsAt y₀ col ≠ 0)
    (hodd : Odd (GeometricFibre.openOddCount base.core y₀ degree))
    (core : Core n p) (hcubic : core.Cubic) (hconn : core.Connected) (y : Fin p → ℚ)
    (hpos : ∀ i, 0 < y i)
    (hy : ∀ (k : Frame core degree) (col : Fin p), k.coordsAt y col ≠ 0) :
    Odd (GeometricFibre.openOddCount core y degree) :=
  odd_of_base_positive hcone htype hGenus base y₀ ⟨hy₀, hgen₀⟩ hodd
    ⟨core, hcubic, hconn⟩ y ⟨hpos, hy⟩

/-! ## 6.  Genus six -/

/-- **`CountSchedule.C34 2` from the two hypotheses**, together with a ballot
classification at one positive general request over the caterpillar, which gives the base
count `5`. -/
theorem c34_genusSix_simple
    (hcone : InConeSupplySimple (2 + 2) (4 * 2 + 2) (6 * 2 + 3))
    (htype : TypeChangeSupplyPositive (2 + 2) (4 * 2 + 2) (6 * 2 + 3))
    (request : Fin (6 * 2 + 3) → ℚ) (hreqpos : ∀ i, 0 < request i)
    (hbase : GeneralRequest (FibreCaterpillar.catCore 2) (2 + 2) request)
    (classification : CaterpillarBallot.BallotClassification 2 request) :
    CountSchedule.C34 2 := by
  intro n p core hcubic hconn hg y hypos hy
  obtain ⟨hn, hp⟩ := StepSupplyGenusSix.index_of_genusSix hcubic hg
  subst hn
  subst hp
  refine c34_of_base_positive hcone htype (by norm_num) StepSupplyGenusSix.catCubicCore
    request hreqpos hbase ?_ core hcubic hconn y hypos hy
  have hfive : GeometricFibre.openOddCount StepSupplyGenusSix.catCubicCore.core request
      (2 + 2) = 5 :=
    CaterpillarBallot.openOddCount_genusSix_eq_five classification
  rw [hfive]
  decide

end DraismaVargas.Count.SimpleWallSupply
