import DraismaVargasCount.CountTransportLink

/-!
# The schedule for whole-fibre count transport

**Source.**  Vargas, Part II (arXiv:2609.09109), the section on invariance of the count
under continuous deformation (`sec-deformation-invariance`) and the proof of the main
theorem: from the caterpillar base to any general `y` over any connected cubic genus-six
core, a chain of cubic types, one general segment per cone, one link per type change.  This
module supplies the in-cone half of that propagation (step 4 of the genus-six assembly) and
states its conclusion, `C34`.

## The architecture this reuses, and the one place it cannot

Part I already walks the same path.  `LocalCases.OuterWalk.coneEntry_of_reaches`
is an induction along the Whitehead chain `CubicDartGraph.Reaches` in which each step is
one cone march to a facet plus a `TypeChangeLink` into the next cone, and
`OuterWalk.exists_terminal_of_chain` runs it from the caterpillar seed to the requested
core.  Two of its three layers are reused verbatim by the count and one is not:

* the **chain** is reused: it is the same finite Whitehead chain, produced by
  `StableSourceWhiteheadChain.exists_chain_of_fullDimensional`, and a finite
  chain of links composes here exactly as `Reaches` composes there
  (`Site.odd_of_reflTransGen`);
* the **type-change link** is reused: `OuterWalk.TypeChangeLink` is already the object on
  which the equality of signed multiplicities across a non-trivalent limit is stated
  (`NonTrivalentNonfacetDenominator.signedMult_eq_of_typeChangeLink`), and the
  adapter into the count lives in `Count.CountTransportLink`;
* the **in-cone march** is *not* reused, and must not be.
  `OuterWalk`'s per-cone step is `TrackedProgress` on a `TrackedState`, which
  follows **one** member of the fibre through the atlas; a count is not a
  property of one member, so that march cannot carry it.  The in-cone half of
  the count schedule is instead the affine-wall calculus of `Count.SegmentWalls`
  (finiteness of the wall parameters, constancy between them, general requests), which
  supplies `exists_generic_start`, `exists_least_wallParam_after` and
  `exists_general_positive_fibre`.

`OuterWalk`'s transported predicate `ConeEntry` is also not reusable:
it is the existence of a generic start and a time-zero tracked state in one
cone, a property of a graph with no request and no count in it.  What this file
transports is `Odd (openOddCount core y degree)`, a function of the *pair*
(core, request).

## What is proved here

* `transport_of_finite_walls` -- **the schedule and its well-foundedness**, in
  the only form it needs: over a finite set `W ⊆ ℚ` of wall parameters, a
  predicate that is constant on wall-free closed intervals and survives the
  crossing of a single isolated wall survives the whole segment.  The induction
  is on the number of walls still ahead, which strictly decreases at every
  step; the next parameter after a wall is chosen strictly below the following
  wall, so each step really does isolate exactly one.  Nothing about counts
  enters.
* `IsWall`, `Schedule`, `Schedule.walls` -- the schedule object for one cone: a
  segment of requests over a fixed core whose start is general (no frame loses a
  coordinate there), together with the finite set of its wall parameters
  (`SegmentWalls.finite_allWallParams`, which is over **every** frame, not just
  the normal-form family).  `Schedule.zero_notMem_walls` and
  `Schedule.one_notMem_walls` are the two endpoints' genericity.
* `Schedule.transport` -- **the in-cone half**: from a link at every
  isolated wall of the segment, the parity of `openOddCount` at the start
  carries to every non-wall parameter.  The constancy hypothesis is *discharged
  here*, not assumed: it is `GeometricSegmentWalls.openOddCount_eq_of_no_wall`.
* `Schedule.transport_source_target` -- the same, start to finish.
* `Site`, `Site.Link`, `Site.odd_of_reflTransGen` -- **the chain half**: a site
  is a labelled core with a request, a link between sites is
  `CountTransportLink.CountLink`, and a finite chain of links carries oddness.
  This composition is deliberately trivial: the design decision recorded in
  `CountTransportLink` is that the neutral link object *is* the parity
  conclusion, because the trivalent and non-trivalent walls have no common
  evidence shape.  All of the content sits in the two producers there.
* `Schedule.siteLink` -- the bridge: an in-cone transport is a `Site.Link`, so
  segments and type changes enter one and the same chain.
* `C34` -- the statement the propagation proves: over every connected cubic core of genus
  `2m + 2`, at every general positive request, the number of open classes of odd
  multiplicity is odd.  At genus six it is `Assembly.c34_genusSix`.

## What is not proved here

* **`Schedule.transport` assumes a link at every isolated wall of the segment**
  (`link`, quantified over all triples `a < t < b` isolating a wall `t`).  That
  hypothesis is the parity of the count across a trivalent wall, step 2 of the assembly.
  By `CountTransportLink.countLink_iff_even_switchingCount` it is exactly the
  evenness of the number of odd classes whose openness changes at `t`.
* **Nothing here produces the chain of cores.**  `Site.odd_of_reflTransGen`
  takes the chain as a `Relation.ReflTransGen` of links.  Part I's chain lives in
  `CubicDartGraph D V` while the count's index is `Core n p`; the coring adapter
  `LocalCases.CoreOfDarts.coreOf` bridges the two with no choice of orderings, because
  both orderings are already part of the types `Fin p × Bool` and `Fin n`, and
  `LocalCases.CoreOfDarts.exists_chain` is the resulting chain of cores.  It is spent on
  sites in `CoreChainSites`.
* **Nothing here produces a link at a type change**; that is step 3 of the assembly.
  `Site.Link` accepts one when it exists.
* `Schedule.general` is generality in the form `coordsAt … ≠ 0` for every
  frame and every column, supplied by
  `SegmentWalls.exists_general_positive_fibre`; the endpoint `Schedule.target`
  is **not** assumed general, so `Schedule.transport` carries its own
  `¬ IsWall` hypothesis at the parameter it lands on.
* `C34` is a `Prop`-valued definition: it names the statement of the propagation, which is
  proved at genus six by `Assembly.c34_genusSix`.
* `openOddCount` throughout is `Count.GeometricFibre.openOddCount`.
-/

namespace DraismaVargas.Count.CountSchedule

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open Utilities.Certificate.ExplicitPotential (Core)
open SegmentWalls (Frame)
open Finset

variable {n p degree : ℕ}

/-! ## 1.  The schedule, as pure order theory on a finite wall set -/

/-- **The schedule and its well-foundedness.**  `W` is the finite set of wall
parameters of a segment.  `hconst` is what holds on a wall-free closed interval
and `hcross` is what one isolated wall costs; `P` then survives the whole
segment from any non-wall parameter to any later non-wall parameter.

The induction is on `k`, a bound for the number of walls in `(a, s]`, and each
step consumes at least one: after crossing the least remaining wall `t₀` the
schedule stops at a parameter strictly below the *next* wall (or at `s` if there
is none), so the crossing hypothesis really is applied to an interval containing
exactly one wall, and the remaining count has dropped. -/
theorem transport_of_finite_walls (W : Finset ℚ) (P : ℚ → Prop)
    (hconst : ∀ a b : ℚ, a ≤ b → (∀ t ∈ W, ¬ (a ≤ t ∧ t ≤ b)) → (P a ↔ P b))
    (hcross : ∀ a t b : ℚ, a < t → t < b → t ∈ W →
      (∀ u ∈ W, a ≤ u → u ≤ b → u = t) → (P a ↔ P b))
    (s : ℚ) (hs : s ∉ W) :
    ∀ k : ℕ, ∀ a : ℚ, a ∉ W → a ≤ s →
      (W.filter (fun t ↦ a < t ∧ t ≤ s)).card ≤ k → (P a ↔ P s) := by
  classical
  intro k
  induction k with
  | zero =>
    intro a ha hle hcard
    refine hconst a s hle ?_
    intro t ht ⟨h1, h2⟩
    have hmem : t ∈ W.filter (fun t ↦ a < t ∧ t ≤ s) := by
      refine mem_filter.mpr ⟨ht, ?_, h2⟩
      rcases lt_or_eq_of_le h1 with h | h
      · exact h
      · exact absurd (h ▸ ht) ha
    have := Finset.card_pos.mpr ⟨t, hmem⟩
    omega
  | succ k ih =>
    intro a ha hle hcard
    set F := W.filter (fun t ↦ a < t ∧ t ≤ s) with hF
    by_cases hEmpty : F = ∅
    · refine hconst a s hle ?_
      intro t ht ⟨h1, h2⟩
      have hmem : t ∈ F := by
        refine mem_filter.mpr ⟨ht, ?_, h2⟩
        rcases lt_or_eq_of_le h1 with h | h
        · exact h
        · exact absurd (h ▸ ht) ha
      rw [hEmpty] at hmem
      exact absurd hmem (notMem_empty t)
    · have hne : F.Nonempty := Finset.nonempty_of_ne_empty hEmpty
      set t₀ := F.min' hne with ht₀
      have ht₀F : t₀ ∈ F := F.min'_mem hne
      have ht₀W : t₀ ∈ W := (mem_filter.mp ht₀F).1
      have ht₀a : a < t₀ := (mem_filter.mp ht₀F).2.1
      have ht₀s : t₀ ≤ s := (mem_filter.mp ht₀F).2.2
      have ht₀lt : t₀ < s := lt_of_le_of_ne ht₀s (fun h ↦ hs (h ▸ ht₀W))
      set G := W.filter (fun t ↦ t₀ < t ∧ t ≤ s) with hG
      set b : ℚ := if hG' : G.Nonempty then (t₀ + G.min' hG') / 2 else s with hb
      have hbt₀ : t₀ < b := by
        rw [hb]
        split
        · next hG' =>
          have h := (mem_filter.mp (G.min'_mem hG')).2.1
          linarith
        · exact ht₀lt
      have hbs : b ≤ s := by
        rw [hb]
        split
        · next hG' =>
          have hm := G.min'_mem hG'
          have h1 := (mem_filter.mp hm).2.1
          have h2 := (mem_filter.mp hm).2.2
          linarith
        · exact le_refl s
      have hbW : b ∉ W := by
        rw [hb]
        split
        · next hG' =>
          intro hmem
          have hm := G.min'_mem hG'
          have h1 := (mem_filter.mp hm).2.1
          have h2 := (mem_filter.mp hm).2.2
          have hin : (t₀ + G.min' hG') / 2 ∈ G :=
            mem_filter.mpr ⟨hmem, by linarith, by linarith⟩
          have := G.min'_le _ hin
          linarith
        · exact hs
      have hOnly : ∀ u ∈ W, a ≤ u → u ≤ b → u = t₀ := by
        intro u hu hau hub
        have hua : a < u := by
          rcases lt_or_eq_of_le hau with h | h
          · exact h
          · exact absurd (h ▸ hu) ha
        have huF : u ∈ F := mem_filter.mpr ⟨hu, hua, le_trans hub hbs⟩
        rcases lt_or_eq_of_le (F.min'_le _ huF) with h | h
        · exfalso
          have huG : u ∈ G := mem_filter.mpr ⟨hu, h, le_trans hub hbs⟩
          rw [hb] at hub
          split at hub
          · next hG' =>
            have hle' := G.min'_le _ huG
            have h1 := (mem_filter.mp (G.min'_mem hG')).2.1
            linarith
          · next hG' => exact hG' ⟨u, huG⟩
        · exact h.symm
      refine (hcross a t₀ b ht₀a hbt₀ ht₀W hOnly).trans (ih b hbW hbs ?_)
      have hsub : W.filter (fun t ↦ b < t ∧ t ≤ s) ⊆ F := by
        intro u hu
        rw [mem_filter] at hu ⊢
        exact ⟨hu.1, by linarith [hu.2.1], hu.2.2⟩
      have hnotin : t₀ ∉ W.filter (fun t ↦ b < t ∧ t ≤ s) := by
        intro hmem
        have := (mem_filter.mp hmem).2.1
        linarith
      have hlt : (W.filter (fun t ↦ b < t ∧ t ≤ s)).card < F.card :=
        Finset.card_lt_card ⟨hsub, fun hcon ↦ hnotin (hcon ht₀F)⟩
      omega

/-! ## 2.  The wall parameters of a segment of requests over one core -/

/-- **A wall parameter of the segment**: at `t` some frame over the core loses a
coordinate.  This is `SegmentWalls.Frame.IsWallParam` with the frame and the
column existentially quantified -- the whole fibre's walls, not one family's. -/
def IsWall (core : Core n p) (degree : ℕ) (y₀ y₁ : Fin p → ℚ) (t : ℚ) : Prop :=
  ∃ (k : Frame core degree) (col : Fin p), k.IsWallParam y₀ y₁ col t

/-- **The schedule object for one cone.**  A segment of requests over a fixed
core whose start is general: no frame loses a coordinate there.  The finish is
unconstrained; `transport` carries its own non-wall hypothesis at whatever
parameter it lands on. -/
structure Schedule (core : Core n p) (degree : ℕ) where
  /-- The start of the segment, a general request. -/
  source : Fin p → ℚ
  /-- The end of the segment. -/
  target : Fin p → ℚ
  /-- Generality at the start, over **every** frame. -/
  general : ∀ (k : Frame core degree) (col : Fin p), k.coordsAt source col ≠ 0

/-- **Non-vacuity, with no hypothesis**: every positive request is the finish of
a schedule whose start is a general positive request of the same orthant.  This
is `SegmentWalls.exists_general_positive_fibre`. -/
theorem exists_schedule (core : Core n p) (degree : ℕ) (base finish : Fin p → ℚ)
    (hbase : ∀ i, 0 < base i) :
    ∃ S : Schedule core degree, (∀ i, 0 < S.source i) ∧ S.target = finish := by
  obtain ⟨y, hpos, havoid⟩ :=
    SegmentWalls.exists_general_positive_fibre core degree base hbase
  exact ⟨⟨y, finish, havoid⟩, hpos, rfl⟩

namespace Schedule

variable {core : Core n p} (S : Schedule core degree)

/-- The request at segment parameter `t`. -/
noncomputable def request (t : ℚ) : Fin p → ℚ :=
  RationalAffineWall.segment S.source S.target t

@[simp] theorem request_zero : S.request 0 = S.source := by
  rw [request, SegmentWalls.segment_zero]

@[simp] theorem request_one : S.request 1 = S.target := by
  funext i
  simp [request, RationalAffineWall.segment]

/-- **Finiteness over the whole fibre**: the wall parameters of the segment
are finite.  This is `SegmentWalls.finite_allWallParams`, whose hypothesis the
schedule's generality discharges. -/
theorem finite_isWall : {t : ℚ | IsWall core degree S.source S.target t}.Finite :=
  SegmentWalls.finite_allWallParams core degree S.source S.target
    fun r col ↦ S.general (SegmentWalls.NFFrame.toFrame r) col

/-- The finite set of wall parameters of the segment. -/
noncomputable def walls : Finset ℚ := S.finite_isWall.toFinset

@[simp] theorem mem_walls {t : ℚ} : t ∈ S.walls ↔ IsWall core degree S.source S.target t :=
  Set.Finite.mem_toFinset _

/-- The start of a schedule is never a wall parameter. -/
theorem zero_notMem_walls : (0 : ℚ) ∉ S.walls := by
  rw [mem_walls]
  rintro ⟨k, col, hk⟩
  have hk' : k.coordsAt (RationalAffineWall.segment S.source S.target 0) col = 0 := hk
  rw [SegmentWalls.segment_zero] at hk'
  exact S.general k col hk'

/-- If the finish is general too, it is not a wall parameter either. -/
theorem one_notMem_walls
    (hgen : ∀ (k : Frame core degree) (col : Fin p), k.coordsAt S.target col ≠ 0) :
    (1 : ℚ) ∉ S.walls := by
  rw [mem_walls]
  rintro ⟨k, col, hk⟩
  refine hgen k col ?_
  have hone : RationalAffineWall.segment S.source S.target 1 = S.target := by
    funext i
    simp [RationalAffineWall.segment]
  have hk' : k.coordsAt (RationalAffineWall.segment S.source S.target 1) col = 0 := hk
  rwa [hone] at hk'

/-! ## 3.  The in-cone half of the schedule -/

/-- **The count is constant between wall parameters.**
`GeometricSegmentWalls.openOddCount_eq_of_no_wall` read against the schedule's
own wall set, which is where the constancy hypothesis of `transport` comes from
-- it is discharged, never assumed. -/
theorem openOddCount_eq_of_no_wall_between {a b : ℚ}
    (hno : ∀ t ∈ S.walls, ¬ (min a b ≤ t ∧ t ≤ max a b)) :
    GeometricFibre.openOddCount core (S.request a) degree =
      GeometricFibre.openOddCount core (S.request b) degree :=
  GeometricSegmentWalls.openOddCount_eq_of_no_wall core degree S.source S.target a b
    fun k col t h1 h2 hw ↦ hno t (S.mem_walls.mpr ⟨k, col, hw⟩) ⟨h1, h2⟩

/-- **The in-cone half of the schedule.**  Given a link at every isolated
wall of the segment, the parity of `openOddCount` carries from any non-wall
parameter to any later non-wall parameter.

The `link` hypothesis, the parity of the count across a trivalent wall, is the only
thing assumed: by `CountTransportLink.countLink_iff_even_switchingCount` it is exactly
the statement that an even number of odd classes change openness across the wall
`t`.  Constancy away from walls is proved, not assumed. -/
theorem transport
    (link : ∀ a t b : ℚ, a < t → t < b → IsWall core degree S.source S.target t →
      (∀ u, IsWall core degree S.source S.target u → a ≤ u → u ≤ b → u = t) →
      CountTransportLink.CountLink degree core (S.request a) core (S.request b))
    {a s : ℚ} (ha : ¬ IsWall core degree S.source S.target a)
    (hs : ¬ IsWall core degree S.source S.target s) (hle : a ≤ s) :
    CountTransportLink.CountLink degree core (S.request a) core (S.request s) := by
  classical
  refine transport_of_finite_walls S.walls
    (fun t ↦ Odd (GeometricFibre.openOddCount core (S.request t) degree)) ?_ ?_ s
    (fun h ↦ hs (S.mem_walls.mp h)) _ a (fun h ↦ ha (S.mem_walls.mp h)) hle (le_refl _)
  · intro u v huv hno
    have hmin : min u v = u := min_eq_left huv
    have hmax : max u v = v := max_eq_right huv
    rw [S.openOddCount_eq_of_no_wall_between (a := u) (b := v) (by rw [hmin, hmax]; exact hno)]
  · intro u t v hut htv htW hOnly
    exact link u t v hut htv (S.mem_walls.mp htW)
      fun w hw h1 h2 ↦ hOnly w (S.mem_walls.mpr hw) h1 h2

/-- The same, from the schedule's start to its finish, when the finish is
general too. -/
theorem transport_source_target
    (link : ∀ a t b : ℚ, a < t → t < b → IsWall core degree S.source S.target t →
      (∀ u, IsWall core degree S.source S.target u → a ≤ u → u ≤ b → u = t) →
      CountTransportLink.CountLink degree core (S.request a) core (S.request b))
    (hgen : ∀ (k : Frame core degree) (col : Fin p), k.coordsAt S.target col ≠ 0) :
    CountTransportLink.CountLink degree core S.source core S.target := by
  have h := S.transport link
    (a := 0) (s := 1)
    (fun h ↦ S.zero_notMem_walls (S.mem_walls.mpr h))
    (fun h ↦ (S.one_notMem_walls hgen) (S.mem_walls.mpr h)) zero_le_one
  rwa [S.request_zero, S.request_one] at h

end Schedule

/-! ## 4.  The chain half: sites and their links -/

/-- **A site of the count**: a labelled core together with a rational request.
The chain of cubic types of the propagation is a chain of these. -/
structure Site (degree : ℕ) where
  /-- The number of core vertices. -/
  vertices : ℕ
  /-- The number of core slots. -/
  slots : ℕ
  /-- The labelled core. -/
  core : Core vertices slots
  /-- The requested slot lengths. -/
  request : Fin slots → ℚ

namespace Site

variable {degree : ℕ}

/-- The count at a site. -/
noncomputable def openOddCount (site : Site degree) : ℕ :=
  GeometricFibre.openOddCount site.core site.request degree

/-- **One step of the walk.**  It is `CountTransportLink.CountLink`, which is
neutral between an in-cone wall and a type change by design; see that file for
why no finer common object exists. -/
def Link (first second : Site degree) : Prop :=
  CountTransportLink.CountLink degree first.core first.request second.core second.request

theorem link_refl (site : Site degree) : Link site site := Iff.rfl

theorem link_symm {first second : Site degree} (h : Link first second) : Link second first :=
  h.symm

theorem link_trans {first second third : Site degree}
    (h : Link first second) (h' : Link second third) : Link first third := h.trans h'

/-- **The chain composes.**  A finite chain of links carries oddness of the
count from one end to the other.  This is deliberately trivial: all of the
content of a link sits in its producers, in `Count.CountTransportLink`. -/
theorem odd_of_reflTransGen {first second : Site degree}
    (h : Relation.ReflTransGen Link first second) (hodd : Odd first.openOddCount) :
    Odd second.openOddCount := by
  induction h with
  | refl => exact hodd
  | tail _ hstep ih => exact hstep.mp ih

end Site

/-- **The bridge**: an in-cone transport over one core is a link of sites, so
segments and type changes enter one and the same chain. -/
theorem Schedule.siteLink {core : Core n p} (S : Schedule core degree)
    (link : ∀ a t b : ℚ, a < t → t < b → IsWall core degree S.source S.target t →
      (∀ u, IsWall core degree S.source S.target u → a ≤ u → u ≤ b → u = t) →
      CountTransportLink.CountLink degree core (S.request a) core (S.request b))
    {a s : ℚ} (ha : ¬ IsWall core degree S.source S.target a)
    (hs : ¬ IsWall core degree S.source S.target s) (hle : a ≤ s) :
    Site.Link (degree := degree) ⟨n, p, core, S.request a⟩ ⟨n, p, core, S.request s⟩ :=
  S.transport link ha hs hle

/-! ## 5.  The statement of the propagation -/

/-- **The statement of the propagation.**  For genus `2m + 2` and degree `m + 2`: over
every connected cubic core of that genus and every general positive request, the number of
open classes of odd multiplicity is odd.

"General" is the form `SegmentWalls.exists_general_positive_fibre` produces: no frame loses
a coordinate at the request.  The route is the induction of this file --
`Schedule.transport` inside each cone, `Site.odd_of_reflTransGen` along the
chain of cubic types -- started at the base count over the caterpillar and fed by the
parity across trivalent walls inside each cone and across the type changes.  At genus six
(`m = 2`) it is `Assembly.c34_genusSix`, step 4 of the assembly.

**Warning: `C34 m` fails at `m = 1`, and this definition is stated for a general `m`.**
The open multiplicities over a genus-`2m+2` cubic core sum to `catalan (m+1)` -- the
Castelnuovo number `1, 2, 5` at genus `2, 4, 6` -- which is odd exactly when `m + 2` is a
power of two.  So `C34 m` can hold only at `m = 0, 2, 6, 14, …`.  In Lean,
`Count.BaseCountParity.not_odd_openOddCount_genusFour_of_ballotClassification` derives
`¬ Odd (openOddCount (catCore 1) request 3)` from a `BallotClassification 1 request`,
because `catalan 2 = 2`.

Every use of `C34` in this library instantiates it at `m = 2`, the genus-six case, where
`catalan 3 = 5` is odd.  The reduction machinery of `StepSupplyReduction` is generic in
`m` and so invites a uniform-in-`m` attempt, but `C34` cannot be proved for general `m`. -/
def C34 (m : ℕ) : Prop :=
  ∀ {n p : ℕ} (core : Core n p), core.Cubic → core.Connected → p + 1 - n = 2 * m + 2 →
    ∀ y : Fin p → ℚ, (∀ i, 0 < y i) →
      (∀ (k : Frame core (m + 2)) (col : Fin p), k.coordsAt y col ≠ 0) →
        Odd (GeometricFibre.openOddCount core y (m + 2))

end DraismaVargas.Count.CountSchedule
