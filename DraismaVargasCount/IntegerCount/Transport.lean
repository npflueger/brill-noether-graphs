module

public import DraismaVargasCount.IntegerCount.WeightedCount
public import DraismaVargasCount.SimpleWallSupply

@[expose] public section

/-!
# The integer walk

The walk of `DraismaVargasCount.SimpleWallSupply` with the integer link: one generic segment
per cone, routed through a hub, and one link per Whitehead move.  The walk is proved there
once for any link of sites (`SimpleWallSupply.IsSiteLink`); this file shows that `IntLink` is
one (`isSiteLink_intLink`) and reads off the two hypotheses and the transport.

## The two hypotheses

* `InConeSupplySum degree n p`: crossing a simple isolated wall on a segment of strictly
  positive requests over one core preserves the weighted count.  It is
  `SimpleWallSupply.InConeSupply` for `IntLink`, the integer form of
  `SimpleWallSupply.InConeSupplySimple`.  It is produced from the per-star balance in
  `DraismaVargasCount.IntegerCount.WallCrossing`.
* `TypeChangeSupplySum degree n p`: across every Whitehead move there are positive general
  requests on the two sides with equal weighted counts.  It is
  `SimpleWallSupply.TypeChangeSupply` for `IntLink`, the integer form of
  `SimpleWallSupply.TypeChangeSupplyPositive`, produced in
  `DraismaVargasCount.IntegerCount.TypeChange`.

## What is proved here

* `Schedule.openMultCount_eq_of_no_wall_between`, `isSiteLink_intLink` — `IntLink` is a link
  of sites.
* `intLink_of_positiveGeneral` — the in-cone half through the hub.
* `eq_of_positiveGeneral` — **the weighted count is the same at every positive general site**
  of cubic cores, from `SimpleWallSupply.IsSiteLink.link_of_cubic`.  It is the integer form of
  `SimpleWallSupply.odd_of_positiveGeneral`; since it is an equality, no contraposition
  (`EvenGenusParity.even_of_base_positive`) is needed.
-/

namespace DraismaVargas.Count.IntegerCount

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore Step)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SimpleWallSupply (PositiveGeneral)

variable {n p degree : ℕ}

/-! ## 1.  The integer link is a link of sites -/

/-- The weighted count is constant between the wall parameters of a schedule. -/
theorem Schedule.openMultCount_eq_of_no_wall_between {core : Core n p}
    (S : CountSchedule.Schedule core degree) {a b : ℚ}
    (hno : ∀ t ∈ S.walls, ¬ (min a b ≤ t ∧ t ≤ max a b)) :
    openMultCount core (S.request a) degree = openMultCount core (S.request b) degree :=
  openMultCount_eq_of_no_wall core degree S.source S.target a b
    fun k col t h1 h2 hw ↦ hno t (S.mem_walls.mpr ⟨k, col, hw⟩) ⟨h1, h2⟩

/-- **The integer link is a link of sites.** -/
theorem isSiteLink_intLink :
    SimpleWallSupply.IsSiteLink degree (IntLink degree (n := n) (p := p) (n' := n) (p' := p))
    where
  refl := intLink_refl degree
  symm := intLink_symm
  trans := intLink_trans
  of_no_wall S _ _ h := Schedule.openMultCount_eq_of_no_wall_between S h
  relabel d _ _ hy := openMultCount_relabel d hy degree

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

/-! ## 3.  The transport -/

/-- **Two positive general requests over one core have equal weighted counts**, given the
in-cone supply: `SimpleWallSupply.IsSiteLink.link_of_positiveGeneral`, through the hub. -/
theorem intLink_of_positiveGeneral (h : InConeSupplySum degree n p) (core : Core n p)
    {y₀ y₁ : Fin p → ℚ} (h₀ : PositiveGeneral core degree y₀)
    (h₁ : PositiveGeneral core degree y₁) :
    IntLink degree core y₀ core y₁ :=
  isSiteLink_intLink.link_of_positiveGeneral h core h₀ h₁

/-- **The weighted count is the same at every positive general site** of cubic cores with the
same indices, given the two supplies and the genus bound.  The integer twin of
`SimpleWallSupply.odd_of_positiveGeneral`. -/
theorem eq_of_positiveGeneral (hcone : InConeSupplySum degree n p)
    (htype : TypeChangeSupplySum degree n p) (hGenus : 2 ≤ p + 1 - n)
    (c c' : CubicCore n p) (y y' : Fin p → ℚ)
    (hy : PositiveGeneral c.core degree y) (hy' : PositiveGeneral c'.core degree y') :
    openMultCount c'.core y' degree = openMultCount c.core y degree :=
  (isSiteLink_intLink.link_of_cubic hcone htype hGenus c c' y y' hy hy').symm

end DraismaVargas.Count.IntegerCount
