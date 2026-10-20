module

public import DraismaVargasCount.IntegerCount.WeightedCount
public import DraismaVargasCount.SimpleWallSupply

@[expose] public section

/-!
# The integer walk

The integer twin of the walk of `DraismaVargasCount.SimpleWallSupply` (and of the transport
step of `DraismaVargasCount.EvenGenusParity`): one generic segment per cone, routed through a
hub, and one link per Whitehead move.  Every statement here is the parity statement with
`CountTransportLink.CountLink` replaced by `IntLink`, and every proof is the parity proof with
`Odd (openOddCount …)` replaced by `openMultCount … = N`; nothing here needs a new idea.

## The two hypotheses

* `InConeSupplySum degree n p`: crossing a simple isolated wall on a segment of strictly
  positive requests over one core preserves the weighted count.  It is the integer twin of
  `SimpleWallSupply.InConeSupplySimple`, with the same binders.  It is produced from the
  per-star balance in `DraismaVargasCount.IntegerCount.WallCrossing`.
* `TypeChangeSupplySum degree n p`: across every Whitehead move there are positive general
  requests on the two sides with equal weighted counts.  It is the integer twin of
  `SimpleWallSupply.TypeChangeSupplyPositive`, produced in
  `DraismaVargasCount.IntegerCount.TypeChange`.

## What is proved here

* `schedule_transport_bounded_int` — the bounded schedule transport, from
  `WallSwitchingBridge.transport_of_finite_walls_bounded` with the predicate
  `openMultCount (S.request t) = openMultCount S.source`.
* `intLink_of_positiveGeneral` — the in-cone half through the hub
  (`SimpleWallSupply.exists_simple_hub`).
* `step_positiveGeneral_int`, `exists_chain_positive_int`, `eq_of_positiveGeneral` — the chain
  of Whitehead moves (`CoreOfDarts.exists_chain`) with positivity carried, and the terminal
  relabelling removed by `openMultCount_relabel`.  The last is the integer twin of
  `SimpleWallSupply.odd_of_positiveGeneral` and of `EvenGenusParity.mod_two_eq_of_positiveGeneral`;
  since it is an equality, no contraposition (`even_of_base_positive`) is needed.
-/

namespace DraismaVargas.Count.IntegerCount

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore Step)
open DraismaVargas.Count.CoreRelabel (Relabel)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.SimpleWallSupply (PositiveGeneral)

variable {n p degree : ℕ}

/-! ## 1.  The schedule -/

/-- The weighted count is constant between the wall parameters of a schedule. -/
theorem Schedule.openMultCount_eq_of_no_wall_between {core : Core n p}
    (S : CountSchedule.Schedule core degree) {a b : ℚ}
    (hno : ∀ t ∈ S.walls, ¬ (min a b ≤ t ∧ t ≤ max a b)) :
    openMultCount core (S.request a) degree = openMultCount core (S.request b) degree :=
  openMultCount_eq_of_no_wall core degree S.source S.target a b
    fun k col t h1 h2 hw ↦ hno t (S.mem_walls.mpr ⟨k, col, hw⟩) ⟨h1, h2⟩

/-- **The bounded schedule transport, integer form**: an integer link at every isolated wall
of `[0, 1]` carries the weighted count from the start of a schedule to a general finish.  The
integer twin of `WallSwitchingBridge.schedule_transport_bounded`. -/
theorem schedule_transport_bounded_int {core : Core n p} (S : CountSchedule.Schedule core degree)
    (link : ∀ a t b : ℚ, 0 ≤ a → a < t → t < b → b ≤ 1 →
      CountSchedule.IsWall core degree S.source S.target t →
      (∀ u, CountSchedule.IsWall core degree S.source S.target u → a ≤ u → u ≤ b → u = t) →
      IntLink degree core (S.request a) core (S.request b))
    (hgen : ∀ (k : Frame core degree) (col : Fin p), k.coordsAt S.target col ≠ 0) :
    IntLink degree core S.source core S.target := by
  classical
  have h := WallSwitchingBridge.transport_of_finite_walls_bounded S.walls
    (fun t ↦ openMultCount core (S.request t) degree = openMultCount core S.source degree) 0 1
    (by
      intro u v huv hno
      have hmin : min u v = u := min_eq_left huv
      have hmax : max u v = v := max_eq_right huv
      rw [Schedule.openMultCount_eq_of_no_wall_between S (a := u) (b := v)
        (by rw [hmin, hmax]; exact hno)])
    (by
      intro u t v hlo hut htv hv1 htW hOnly
      rw [link u t v hlo hut htv hv1 (S.mem_walls.mp htW)
        fun w hw h1 h2 ↦ hOnly w (S.mem_walls.mpr hw) h1 h2])
    (fun h ↦ (S.one_notMem_walls hgen) h)
    _ 0 le_rfl S.zero_notMem_walls zero_le_one (le_refl _)
  have h0 : openMultCount core (S.request 0) degree = openMultCount core S.source degree := by
    rw [S.request_zero]
  have h1 := h.mp h0
  rw [S.request_one] at h1
  exact h1.symm

/-! ## 2.  The two hypotheses -/

/-- **The weighted count across a simple positive wall.**  The integer twin of
`SimpleWallSupply.InConeSupplySimple`, with the same binders: over every core, on every
schedule with strictly positive endpoints, crossing a wall parameter `t` that is the only one
in `[a, b] ⊆ [0, 1]` and is codimension one preserves the weighted count. -/
def InConeSupplySum (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (S : CountSchedule.Schedule core degree) (a t b : ℚ),
    (∀ i, 0 < S.source i) → (∀ i, 0 < S.target i) →
    0 ≤ a → a < t → t < b → b ≤ 1 →
    CountSchedule.IsWall core degree S.source S.target t →
    (∀ u, CountSchedule.IsWall core degree S.source S.target u → a ≤ u → u ≤ b → u = t) →
    WallSwitchingBridge.SimpleAt core degree S.source S.target t →
      IntLink degree core (S.request a) core (S.request b)

/-- **The weighted count across a type change, at positive general requests.**  The integer
twin of `SimpleWallSupply.TypeChangeSupplyPositive`. -/
def TypeChangeSupplySum (degree n p : ℕ) : Prop :=
  ∀ c c' : CubicCore n p, Step c c' →
    ∃ y y' : Fin p → ℚ, PositiveGeneral c.core degree y ∧ PositiveGeneral c'.core degree y' ∧
      IntLink degree c.core y c'.core y'

/-! ## 3.  The in-cone half, through the hub -/

/-- **Two positive general requests over one core have equal weighted counts**, given the
in-cone supply.  The integer twin of `SimpleWallSupply.countLink_of_positiveGeneral`; the hub
is the one of `SimpleWallSupply.exists_simple_hub`. -/
theorem intLink_of_positiveGeneral (h : InConeSupplySum degree n p) (core : Core n p)
    {y₀ y₁ : Fin p → ℚ} (h₀ : PositiveGeneral core degree y₀)
    (h₁ : PositiveGeneral core degree y₁) :
    IntLink degree core y₀ core y₁ := by
  obtain ⟨z, hzpos, hzgen, hs₀, hs₁⟩ :=
    SimpleWallSupply.exists_simple_hub core degree y₀ y₁ h₀.2 h₁.2 (fun _ ↦ 1) fun _ ↦ one_pos
  have link₀ : IntLink degree core z core y₀ :=
    schedule_transport_bounded_int ⟨z, y₀, hzgen⟩
      (fun a t b hlo hat htb hb1 hw hiso ↦
        h core ⟨z, y₀, hzgen⟩ a t b hzpos h₀.1 hlo hat htb hb1 hw hiso (hs₀ t)) h₀.2
  have link₁ : IntLink degree core z core y₁ :=
    schedule_transport_bounded_int ⟨z, y₁, hzgen⟩
      (fun a t b hlo hat htb hb1 hw hiso ↦
        h core ⟨z, y₁, hzgen⟩ a t b hzpos h₁.1 hlo hat htb hb1 hw hiso (hs₁ t)) h₁.2
  exact intLink_trans (intLink_symm link₀) link₁

/-! ## 4.  The chain, carrying positivity -/

theorem step_positiveGeneral_int (hcone : InConeSupplySum degree n p)
    (htype : TypeChangeSupplySum degree n p) {c c' : CubicCore n p} (hstep : Step c c')
    {y : Fin p → ℚ} (hy : PositiveGeneral c.core degree y) :
    ∃ y' : Fin p → ℚ, PositiveGeneral c'.core degree y' ∧
      IntLink degree c.core y c'.core y' := by
  obtain ⟨z, y', hz, hy', hlink⟩ := htype c c' hstep
  exact ⟨y', hy', intLink_trans (intLink_of_positiveGeneral hcone c.core hy hz) hlink⟩

theorem exists_chain_positive_int (hcone : InConeSupplySum degree n p)
    (htype : TypeChangeSupplySum degree n p) {c c' : CubicCore n p}
    (h : Relation.ReflTransGen Step c c') {y : Fin p → ℚ}
    (hy : PositiveGeneral c.core degree y) :
    ∃ y' : Fin p → ℚ, PositiveGeneral c'.core degree y' ∧
      IntLink degree c.core y c'.core y' := by
  induction h with
  | refl => exact ⟨y, hy, intLink_refl _ _ _⟩
  | tail _ hstep ih =>
      obtain ⟨u, hu, hchain⟩ := ih
      obtain ⟨v, hv, hlink⟩ := step_positiveGeneral_int hcone htype hstep hu
      exact ⟨v, hv, intLink_trans hchain hlink⟩

/-- **The weighted count is the same at every positive general site** of cubic cores with the
same indices, given the two supplies and the genus bound.  The integer twin of
`SimpleWallSupply.odd_of_positiveGeneral`; the terminal core isomorphism of
`CoreOfDarts.exists_chain` is removed by `openMultCount_relabel`. -/
theorem eq_of_positiveGeneral (hcone : InConeSupplySum degree n p)
    (htype : TypeChangeSupplySum degree n p) (hGenus : 2 ≤ p + 1 - n)
    (c c' : CubicCore n p) (y y' : Fin p → ℚ)
    (hy : PositiveGeneral c.core degree y) (hy' : PositiveGeneral c'.core degree y') :
    openMultCount c'.core y' degree = openMultCount c.core y degree := by
  obtain ⟨c'', hchain, ⟨i⟩⟩ := CoreOfDarts.exists_chain c c' hGenus
  obtain ⟨z, hz, hlink⟩ := exists_chain_positive_int hcone htype hchain hy
  let d : Relabel c''.core c'.core := CoreRelabel.Relabel.ofCoreIso i
  let w : Fin p → ℚ := fun e ↦ z (d.slot.symm e)
  have hzw : ∀ e, w (d.slot e) = z e := fun e ↦ congrArg z (d.slot.symm_apply_apply e)
  have hw : openMultCount c''.core z degree = openMultCount c'.core w degree :=
    openMultCount_relabel d hzw degree
  have hwpos : ∀ e, 0 < w e := fun e ↦ hz.1 _
  have hlast : IntLink degree c'.core w c'.core y' :=
    intLink_of_positiveGeneral hcone c'.core
      ⟨hwpos, StepSupplyReduction.generalRequest_relabel d hzw hz.2⟩ hy'
  exact (hlink.trans (hw.trans hlast)).symm

end DraismaVargas.Count.IntegerCount
