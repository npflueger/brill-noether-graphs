module

public import DraismaVargasCount.TransportedChipEndgame
public import Utilities.Subdivision.CoreExpansion
public import Utilities.Subdivision.SlotMoment

@[expose] public section

/-!
# The series moment of an expanded slot

This file supplies the arithmetic of one step of the endgame (step 5 of
`Assembly`).  From a `Closed` odd-multiplicity member over `D.bigCore` at the
degenerate request one wants a degree-four pencil **of `spec₀`** at scale
`memberScale member`, with the slot moments computed on `spec₀`'s slots.  A
double retained slot carries two `spec₀` slots in series through a marker, so one
model moment splits into two.  This file is that splitting, and nothing else.

## The picture

`Utilities.Subdivision.CoreExpansion` presents the contraction
`(D.bigSpec spec₀ hN hL).graph → spec₀.graph` slot by slot: a big slot `e` of
role `D.kind e` is laid along `spec₀` by `kindVertex`, which sends path position
`q` of `e` to

* `spec₀.coreVertex fallback` when `e` is contracted (the whole slot collapses);
* position `q` of the small slot `j` when `D.kind e = .single j`;
* position `q` of `j₁` while `q ≤ length j₁`, and position `q - length j₁` of
  `j₂` afterwards, when `D.kind e = .double j₁ j₂`.

So the chips a transported divisor puts on the *series path* of one big slot are
read, on the small side, as chips on **two** consecutive small slots separated by
the marker `coreVertex (core.head j₁)`.  `seriesMoment` is the offset-weighted
sum of those chips **with the big slot's own offsets**; `InteriorFiring.slotMoment`
is the same sum with the small slot's offsets.  The two disagree, and §2 says by
exactly how much.

## What is proved

* `kindVertex_double_first`, `kindVertex_double_marker`, `kindVertex_double_second`
  — where one series position of a `double` slot sits on the small side: an
  interior vertex of `j₁`, the marker `coreVertex (core.head j₁)` at position
  exactly `T.length j₁`, or an interior vertex of `j₂` at the offset measured
  **from the marker**.
* `seriesMoment_single` — on a retained `single` slot the two moments agree on
  the nose.
* `seriesMoment_double` — **the identity this file is about.**  With
  `L₁ = T.length j₁`,
  `seriesMoment = slotMoment j₁ + slotMoment j₂ + L₁ * (Dv marker + slotCount j₂)`,
  where `marker = T.coreVertex (T.core.head j₁)`.  No hypothesis at all: not
  `D.Conditions`, not `core.head j₁ = core.tail j₂`, not connectivity.
* `dvd_seriesMoment_double_iff` — once `m ∣ L₁`, `m ∣ seriesMoment` says exactly
  `m ∣ slotMoment j₁ + slotMoment j₂`, and no more.
* `dvd_slotMoment_double_of_terms` / `dvd_slotMoment_double_of_ratTerms` — the
  consumable form.  A **per-position** `2`-adic hypothesis along the series path
  splits into the two small slots, provided `2 ^ a ∣ L₁` (respectively
  `k ∣ L₁`), which at `T = spec₀.scale k hk` is free.  `..._single_...` are the
  same for a retained `single`.
* `ratTerms_of_reversed`, `kindLength_scale_dvd` — the split does not depend on
  which way round the row runs along the big slot, exactly as
  `RowRealizedPosition.orientedInteriorRowPushforward_slotMoment` does on the
  small side.
* `dvd_slotMoment_of_expansion` (and `..._reversed`) — the same conclusion for
  *every* small slot at once, routed through `ExpansionData.exists_carrier`,
  i.e. through the datum's own `owner`/`side` bookkeeping.
* `bnExists_of_expansion` — that fed to
  `TransportedChipEndgame.bnExists_of_pencil_slotMoment`: a degree-four divisor
  on `(spec₀.scale (2 ^ a * u) hk).graph` whose chips satisfy the per-position
  condition along the big slots gives `BNExists (spec₀.scale u hu).graph 1 4` at
  the odd part `u` of the scale.
* `pushDivisor`, `pushDivisor_interior`, `effective_pushDivisor`,
  `deg_pushDivisor`, `ratTerms_of_pushDivisor` — **the divisor need not be given
  on the small side.**  The naive pushforward along the contraction
  `ExpansionData.vertexMap` keeps the coefficient at every interior image (by
  `ExpansionData.interior_fibre`, whose fibres there are singletons), keeps
  effectivity and keeps total degree, so the per-position receipts may be stated
  where a member over `D.bigCore` actually lives.
* `dvd_slotMoment_of_bigDivisor`, `bnExists_of_bigDivisor` — the whole chain from
  the expanded side: a divisor on `(D.bigSpec (spec₀.scale (2 ^ a * u) hk) hN hL).graph`,
  effective of degree four, with per-position receipts, whose pushforward has
  rank at least one, gives `BNExists (spec₀.scale u hu).graph 1 4`.
* `SplitWitness.aggregate_does_not_split` — a named `Spec` and a named divisor
  at which the seam is even and the series moment is even while the first small
  moment is odd.  This is the witness that `dvd_seriesMoment_double_iff` cannot
  be strengthened.
* `exists_odd_subdivisionPencil` — the four-line odd corollary of
  `LocalCases.RetainedIndexProducer.exists_expansionModel_retainedIndex`, whose
  `pencil.scale = k` is strictly stronger than `Odd pencil.scale`.

## Why the aggregate identity is *not* enough, and what replaces it

`seriesMoment_double` alone does **not** split divisibility:
`2 ^ a ∣ seriesMoment` gives only `2 ^ a ∣ slotMoment j₁ + slotMoment j₂` once
`2 ^ a ∣ L₁` kills the correction term (`dvd_seriesMoment_double_iff`), and
§6 exhibits a divisor with `slotMoment j₁ = 1` and `slotMoment j₂ = -1` where
that is all one gets.  The split is recovered from the *per-chip* hypothesis
instead, which is exactly the shape the member route delivers
(`RowRealizedPosition.member_collisionCoefficient_mem` is stated chip by chip,
and `SlotMoment.slotMoment_dvd_two_pow_of_terms` consumes it chip by chip).
The arithmetic of the split is one subtraction: a chip at series position
`L₁ + o + 1` has small offset `o + 1`, and `L₁` is a multiple of the scale.

## What is NOT proved

* **No divisor is produced here.**  Everything below takes the divisor as given,
  on the small side (`Dv`) or on the expanded side (`Bv`).  Producing `Bv` from a
  `Closed` odd-multiplicity member over `D.bigCore` — a pushforward of the
  member's pullback divisor at the **degenerate** request, where
  `Spec.length_pos` fails on the forest rows — is the *geometric* half of this
  step and is not done here.  In particular no `FibreMember` appears anywhere in
  this file, and `memberScale` is not mentioned: `k` is a bare natural number.
* **`D.bigSpec (spec₀.scale k hk) hN hL` is not the degenerate request.**  It
  gives a forest slot length `1`, not `0`, because `Spec` carries `length_pos`.
  That is harmless for everything proved here (the forest slots are contracted
  and carry no interior position that any statement below reads), but a producer
  must still say which object its member is over; this file does not choose for
  it.  This is the same `length_pos` obstruction that the member's forest rows
  meet at the degenerate request, seen from the other end.
* **`hRank` is untouched.**  `bnExists_of_expansion` and `bnExists_of_bigDivisor`
  both ask for `rank ... ≥ 1` on the small-side divisor as a hypothesis, exactly
  as `TransportedChipEndgame` does.  `effective` and `deg` are carried
  across the contraction (`effective_pushDivisor`, `deg_pushDivisor`) but are
  still hypotheses on the big side.  Nothing here says rank survives the
  contraction; that is an upper-semicontinuity statement, and it is the real
  content of the passage from the expanded core to the requested one.
* **`D.Conditions` is used only in `dvd_slotMoment_of_expansion`**, and there
  only through `ExpansionData.exists_carrier`; no clause about markers, fibres,
  looplessness or connectivity enters the arithmetic.  Nothing here shows the
  seam vertex of a `double` slot is a genuine bivalent marker — that is
  `MarkerIsolated`, and it is not needed for the moment bookkeeping.
* **Nothing here says the small side is `spec₀` rather than an arbitrary
  `Spec`.**  The theorems are stated for any `small : Spec n p` carrying an
  `ExpansionData`, which is more general but also means the file cannot by
  itself know that `small` is the reduced request.
* The `fallback : Fin n` argument of `kindVertex` is carried but never used: the
  contracted branch is the only one that reads it, and every statement below is
  vacuous on contracted slots because `kindLength T .contracted = 1`.
* No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`,
  no `#eval`.  §6's concrete witness uses `decide` on three closed goals over
  `Fin 2`/`Fin 3` and nothing parametric.
-/

namespace DraismaVargas.Count.ExpansionSeriesMoment

open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Subdivision.CoreExpansion
open DraismaVargas.Count.SlotMoment
open Finset

variable {n p : ℕ}

/-! ## 0.  Where one series position sits on the small side -/

/-- An interior position of a retained `single` slot is that slot's own interior
vertex at the same offset. -/
theorem kindVertex_single_interior (T : Spec n p) (fallback : Fin n) (j : Fin p)
    {x : ℕ} (hx : x + 1 < T.length j) :
    kindVertex T fallback (SlotKind.single j) (x + 1) =
      T.interiorVertex j ⟨x, by omega⟩ := by
  show T.pathVertex j ⟨min (x + 1) (T.length j), by omega⟩ = _
  rw [PathHelpers.pathVertex_of_interior T j _ (by simp only []; omega)
    (by simp only []; omega)]
  congr 1
  exact Fin.ext (by simp only []; omega)

/-- A position in the first half of a `double` slot is an interior vertex of its
first small slot, at the same offset. -/
theorem kindVertex_double_first (T : Spec n p) (fallback : Fin n) (j₁ j₂ : Fin p)
    {x : ℕ} (hx : x + 1 < T.length j₁) :
    kindVertex T fallback (SlotKind.double j₁ j₂) (x + 1) =
      T.interiorVertex j₁ ⟨x, by omega⟩ := by
  rw [kindVertex_double_le j₁ j₂ fallback (q := x + 1) (by omega)]
  rw [PathHelpers.pathVertex_of_interior T j₁ _ (by simp only []; omega)
    (by simp only []; omega)]
  congr 1
  exact Fin.ext (by simp only []; omega)

/-- The seam of a `double` slot is the marker: the head of its first small
slot. -/
theorem kindVertex_double_marker (T : Spec n p) (fallback : Fin n) (j₁ j₂ : Fin p) :
    kindVertex T fallback (SlotKind.double j₁ j₂) (T.length j₁) =
      T.coreVertex (T.core.head j₁) := by
  rw [kindVertex_double_le j₁ j₂ fallback (q := T.length j₁) le_rfl]
  exact PathHelpers.pathVertex_of_last T j₁ _
    (by simp only []; have := T.length_pos j₁; omega)
    (by simp only []; omega)

/-- A position past the seam is an interior vertex of the second small slot, at
the offset **measured from the marker**. -/
theorem kindVertex_double_second (T : Spec n p) (fallback : Fin n) (j₁ j₂ : Fin p)
    {x : ℕ} (hx : x + 1 < T.length j₂) :
    kindVertex T fallback (SlotKind.double j₁ j₂) (T.length j₁ + x + 1) =
      T.interiorVertex j₂ ⟨x, by omega⟩ := by
  rw [kindVertex_double_gt j₁ j₂ fallback (q := T.length j₁ + x + 1) (by omega)]
  rw [PathHelpers.pathVertex_of_interior T j₂ _ (by simp only []; omega)
    (by simp only []; omega)]
  congr 1
  exact Fin.ext (by simp only []; omega)

/-! ## 1.  The series moment -/

/-- The offset-weighted sum of the chips a divisor on the small subdivision puts
on the series path of one big slot, **with the big slot's own offsets**.  This
is `InteriorFiring.slotMoment` read along `kindVertex` instead of along a single
small slot. -/
def seriesMoment (T : Spec n p) (fallback : Fin n) (kind : SlotKind p)
    (Dv : CFDiv T.graph) : ℤ :=
  ∑ q : Fin (kindLength T kind - 1),
    Dv (kindVertex T fallback kind (q.val + 1)) * ((q.val + 1 : ℕ) : ℤ)

/-- `slotMoment` as a `range` sum along `kindVertex`. -/
theorem slotMoment_eq_range (T : Spec n p) (fallback : Fin n) (j : Fin p)
    (Dv : CFDiv T.graph) :
    InteriorFiring.slotMoment T Dv j =
      ∑ x ∈ range (T.length j - 1),
        Dv (kindVertex T fallback (SlotKind.single j) (x + 1)) * ((x + 1 : ℕ) : ℤ) := by
  rw [← Fin.sum_univ_eq_sum_range
    (fun x ↦ Dv (kindVertex T fallback (SlotKind.single j) (x + 1)) * ((x + 1 : ℕ) : ℤ))]
  refine Finset.sum_congr rfl ?_
  intro o _
  rw [kindVertex_single_interior T fallback j (by have := o.isLt; omega)]

/-- `slotCount` as a `range` sum along `kindVertex`. -/
theorem slotCount_eq_range (T : Spec n p) (fallback : Fin n) (j : Fin p)
    (Dv : CFDiv T.graph) :
    InteriorFiring.slotCount T Dv j =
      ∑ x ∈ range (T.length j - 1),
        Dv (kindVertex T fallback (SlotKind.single j) (x + 1)) := by
  rw [← Fin.sum_univ_eq_sum_range
    (fun x ↦ Dv (kindVertex T fallback (SlotKind.single j) (x + 1)))]
  refine Finset.sum_congr rfl ?_
  intro o _
  rw [kindVertex_single_interior T fallback j (by have := o.isLt; omega)]

/-- **A retained `single` slot changes nothing.** -/
theorem seriesMoment_single (T : Spec n p) (fallback : Fin n) (j : Fin p)
    (Dv : CFDiv T.graph) :
    seriesMoment T fallback (SlotKind.single j) Dv =
      InteriorFiring.slotMoment T Dv j := by
  rw [slotMoment_eq_range T fallback j Dv]
  exact Fin.sum_univ_eq_sum_range
    (fun x ↦ Dv (kindVertex T fallback (SlotKind.single j) (x + 1)) * ((x + 1 : ℕ) : ℤ)) _

/-- **The identity this file is about: one model moment splits into two.**

A `double` big slot carries the small slots `j₁` and `j₂` in series through the
marker `T.coreVertex (T.core.head j₁)`.  Reading the big slot's own offsets, the
moment is the sum of the two small moments plus a correction supported entirely
at and beyond the marker: the marker's own chip, and the whole interior chip
count of `j₂`, each weighted by the marker's position `T.length j₁`.

No hypothesis is needed — in particular the identity does not ask that `j₁` and
`j₂` actually meet, because `kindVertex` puts the seam at `T.length j₁` by
construction. -/
theorem seriesMoment_double (T : Spec n p) (fallback : Fin n) (j₁ j₂ : Fin p)
    (Dv : CFDiv T.graph) :
    seriesMoment T fallback (SlotKind.double j₁ j₂) Dv =
      InteriorFiring.slotMoment T Dv j₁ + InteriorFiring.slotMoment T Dv j₂ +
        (T.length j₁ : ℤ) *
          (Dv (T.coreVertex (T.core.head j₁)) + InteriorFiring.slotCount T Dv j₂) := by
  classical
  have hL₁ := T.length_pos j₁
  have hL₂ := T.length_pos j₂
  set f : ℕ → ℤ := fun x ↦
    Dv (kindVertex T fallback (SlotKind.double j₁ j₂) (x + 1)) * ((x + 1 : ℕ) : ℤ) with hf
  have hlen : kindLength T (SlotKind.double j₁ j₂) - 1
      = (T.length j₁ - 1) + (1 + (T.length j₂ - 1)) := by
    show T.length j₁ + T.length j₂ - 1 = _
    omega
  have hseries : seriesMoment T fallback (SlotKind.double j₁ j₂) Dv
      = ∑ x ∈ range (kindLength T (SlotKind.double j₁ j₂) - 1), f x :=
    Fin.sum_univ_eq_sum_range f _
  rw [hseries, hlen, Finset.sum_range_add, Finset.sum_range_add]
  have hfirst : ∑ x ∈ range (T.length j₁ - 1), f x = InteriorFiring.slotMoment T Dv j₁ := by
    rw [slotMoment_eq_range T fallback j₁ Dv]
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hx' : x + 1 < T.length j₁ := by
      have := Finset.mem_range.mp hx; omega
    simp only [hf]
    rw [kindVertex_double_first T fallback j₁ j₂ hx',
      kindVertex_single_interior T fallback j₁ hx']
  have hmarker : ∑ x ∈ range 1, f (T.length j₁ - 1 + x)
      = (T.length j₁ : ℤ) * Dv (T.coreVertex (T.core.head j₁)) := by
    rw [Finset.sum_range_one]
    simp only [hf, Nat.add_zero]
    have hval : T.length j₁ - 1 + 1 = T.length j₁ := by omega
    rw [hval, kindVertex_double_marker T fallback j₁ j₂]
    ring
  have hsecond : ∑ x ∈ range (T.length j₂ - 1), f (T.length j₁ - 1 + (1 + x))
      = InteriorFiring.slotMoment T Dv j₂ +
        (T.length j₁ : ℤ) * InteriorFiring.slotCount T Dv j₂ := by
    rw [slotMoment_eq_range T fallback j₂ Dv, slotCount_eq_range T fallback j₂ Dv,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hx' : x + 1 < T.length j₂ := by
      have := Finset.mem_range.mp hx; omega
    have hval : T.length j₁ - 1 + (1 + x) = T.length j₁ + x := by omega
    simp only [hf, hval]
    rw [show T.length j₁ + x + 1 = T.length j₁ + x + 1 from rfl,
      kindVertex_double_second T fallback j₁ j₂ hx',
      kindVertex_single_interior T fallback j₂ hx']
    push_cast
    ring
  rw [hfirst, hmarker, hsecond]
  ring

/-! ## 2.  The aggregate is exactly the sum, and that is strictly too weak -/

/-- **The correction term is the only thing the seam contributes.**  Once the
seam position `T.length j₁` is a multiple of `m`, divisibility of the series
moment says precisely that `m` divides the **sum** of the two small moments.

This is the precise sense in which an aggregate hypothesis cannot suffice: it
is blind to how the mass is distributed between `j₁` and `j₂`, and
`bnExists_of_pencil_slotMoment` needs the two separately.  §3 recovers the split
from a per-position hypothesis instead. -/
theorem dvd_seriesMoment_double_iff (T : Spec n p) (fallback : Fin n)
    (j₁ j₂ : Fin p) (Dv : CFDiv T.graph) (m : ℤ)
    (hseam : m ∣ (T.length j₁ : ℤ)) :
    m ∣ seriesMoment T fallback (SlotKind.double j₁ j₂) Dv ↔
      m ∣ (InteriorFiring.slotMoment T Dv j₁ + InteriorFiring.slotMoment T Dv j₂) := by
  rw [seriesMoment_double]
  exact dvd_add_left (Dvd.dvd.mul_right hseam _)

/-! ## 3.  The split of the divisibility, chip by chip

The hypotheses below are indexed by the **series position** `q + 1` along the big
slot, not by a `Fin` of the small slot: that is the form in which a divisor
transported across the contraction knows where its chips are. -/

/-- **Integer form, `single`.**  Along a retained `single` slot there is nothing
to transport. -/
theorem dvd_slotMoment_single_of_terms (T : Spec n p) (fallback : Fin n) (j : Fin p)
    (Dv : CFDiv T.graph) (a : ℕ)
    (hTerms : ∀ q : ℕ, q + 1 < kindLength T (SlotKind.single j) →
      ((2 ^ a : ℕ) : ℤ) ∣
        Dv (kindVertex T fallback (SlotKind.single j) (q + 1)) * ((q + 1 : ℕ) : ℤ)) :
    ((2 ^ a : ℕ) : ℤ) ∣ InteriorFiring.slotMoment T Dv j := by
  rw [InteriorFiring.slotMoment]
  refine Finset.dvd_sum ?_
  intro o _
  have ho := o.isLt
  have hlt : o.val + 1 < T.length j := by omega
  have h := hTerms o.val (by simpa only [kindLength] using hlt)
  rwa [kindVertex_single_interior T fallback j hlt] at h

/-- **Integer form, `double`.**  A per-position `2 ^ a`-divisibility along the
series path splits into the two small slots as soon as the seam position
`T.length j₁` is itself a multiple of `2 ^ a`.

The arithmetic is exactly one subtraction: a chip at series position
`T.length j₁ + o + 1` has small offset `o + 1`, and the difference of the two
weights is the seam position. -/
theorem dvd_slotMoment_double_of_terms (T : Spec n p) (fallback : Fin n)
    (j₁ j₂ : Fin p) (Dv : CFDiv T.graph) (a : ℕ)
    (hseam : ((2 ^ a : ℕ) : ℤ) ∣ (T.length j₁ : ℤ))
    (hTerms : ∀ q : ℕ, q + 1 < kindLength T (SlotKind.double j₁ j₂) →
      ((2 ^ a : ℕ) : ℤ) ∣
        Dv (kindVertex T fallback (SlotKind.double j₁ j₂) (q + 1)) * ((q + 1 : ℕ) : ℤ)) :
    ((2 ^ a : ℕ) : ℤ) ∣ InteriorFiring.slotMoment T Dv j₁ ∧
      ((2 ^ a : ℕ) : ℤ) ∣ InteriorFiring.slotMoment T Dv j₂ := by
  have hL₁ := T.length_pos j₁
  have hL₂ := T.length_pos j₂
  constructor
  · rw [InteriorFiring.slotMoment]
    refine Finset.dvd_sum ?_
    intro o _
    have ho := o.isLt
    have hlt : o.val + 1 < T.length j₁ := by omega
    have h := hTerms o.val (by simp only [kindLength]; omega)
    rwa [kindVertex_double_first T fallback j₁ j₂ hlt] at h
  · rw [InteriorFiring.slotMoment]
    refine Finset.dvd_sum ?_
    intro o _
    have ho := o.isLt
    have hlt : o.val + 1 < T.length j₂ := by omega
    have h := hTerms (T.length j₁ + o.val) (by simp only [kindLength]; omega)
    rw [kindVertex_double_second T fallback j₁ j₂ hlt] at h
    have hsub : ((2 ^ a : ℕ) : ℤ) ∣
        Dv (T.interiorVertex j₂ ⟨o.val, by omega⟩) * (T.length j₁ : ℤ) :=
      Dvd.dvd.mul_left hseam _
    have hdiff := dvd_sub h hsub
    rw [← mul_sub, show (((T.length j₁ + o.val + 1 : ℕ)) : ℤ) - (T.length j₁ : ℤ)
      = ((o.val + 1 : ℕ) : ℤ) by push_cast; ring] at hdiff
    exact hdiff

/-- **Rational form, `single`**: the odd-denominator hypothesis that the
member route actually produces
(`RowRealizedPosition.member_collisionCoefficient_mem`), consumed through
`SlotMoment.slotMoment_dvd_two_pow_of_terms`. -/
theorem dvd_slotMoment_single_of_ratTerms (T : Spec n p) (fallback : Fin n) (j : Fin p)
    (Dv : CFDiv T.graph) (k a : ℕ) (hk : 0 < k) (hka : 2 ^ a ∣ k)
    (hTerms : ∀ q : ℕ, q + 1 < kindLength T (SlotKind.single j) →
      (Dv (kindVertex T fallback (SlotKind.single j) (q + 1)) : ℚ) *
        (((q + 1 : ℕ) : ℚ) / k) ∈ oddDenominatorSubring) :
    ((2 ^ a : ℕ) : ℤ) ∣ InteriorFiring.slotMoment T Dv j := by
  refine slotMoment_dvd_two_pow_of_terms T Dv k a hk hka j ?_
  intro o
  have ho := o.isLt
  have hlt : o.val + 1 < T.length j := by omega
  have h := hTerms o.val (by simpa only [kindLength] using hlt)
  rwa [kindVertex_single_interior T fallback j hlt] at h

/-- **Rational form, `double`**: the same split, with the odd-denominator
hypothesis.  The seam hypothesis is `k ∣ T.length j₁`, which at
`T = spec₀.scale k hk` holds for free. -/
theorem dvd_slotMoment_double_of_ratTerms (T : Spec n p) (fallback : Fin n)
    (j₁ j₂ : Fin p) (Dv : CFDiv T.graph) (k a : ℕ) (hk : 0 < k) (hka : 2 ^ a ∣ k)
    (hseam : k ∣ T.length j₁)
    (hTerms : ∀ q : ℕ, q + 1 < kindLength T (SlotKind.double j₁ j₂) →
      (Dv (kindVertex T fallback (SlotKind.double j₁ j₂) (q + 1)) : ℚ) *
        (((q + 1 : ℕ) : ℚ) / k) ∈ oddDenominatorSubring) :
    ((2 ^ a : ℕ) : ℤ) ∣ InteriorFiring.slotMoment T Dv j₁ ∧
      ((2 ^ a : ℕ) : ℤ) ∣ InteriorFiring.slotMoment T Dv j₂ := by
  have hL₁ := T.length_pos j₁
  have hL₂ := T.length_pos j₂
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  obtain ⟨c, hc⟩ := hseam
  constructor
  · refine slotMoment_dvd_two_pow_of_terms T Dv k a hk hka j₁ ?_
    intro o
    have ho := o.isLt
    have hlt : o.val + 1 < T.length j₁ := by omega
    have h := hTerms o.val (by simp only [kindLength]; omega)
    rwa [kindVertex_double_first T fallback j₁ j₂ hlt] at h
  · refine slotMoment_dvd_two_pow_of_terms T Dv k a hk hka j₂ ?_
    intro o
    have ho := o.isLt
    have hlt : o.val + 1 < T.length j₂ := by omega
    have h := hTerms (T.length j₁ + o.val) (by simp only [kindLength]; omega)
    rw [kindVertex_double_second T fallback j₁ j₂ hlt] at h
    set chip : ℤ := Dv (T.interiorVertex j₂ ⟨o.val, by omega⟩) with hchip
    have hseamMem : (chip : ℚ) * ((T.length j₁ : ℚ) / k) ∈ oddDenominatorSubring := by
      have hquot : (T.length j₁ : ℚ) / k = (c : ℚ) := by
        rw [hc]; push_cast; field_simp
      rw [hquot]
      exact oddDenominatorSubring.mul_mem (intCast_mem _ chip) (natCast_mem _ c)
    have hdiff := oddDenominatorSubring.sub_mem h hseamMem
    have hcast : (chip : ℚ) * (((T.length j₁ + o.val + 1 : ℕ) : ℚ) / k) -
        (chip : ℚ) * ((T.length j₁ : ℚ) / k) =
        (chip : ℚ) * (((o.val + 1 : ℕ) : ℚ) / k) := by
      push_cast
      field_simp
      ring
    rwa [hcast] at hdiff

/-! ## 3a.  Independence of the row's direction

A member does not know which way round its row runs along the big slot, so the
odd-denominator receipt it carries may be about the distance from the *other*
end.  Exactly as `RowRealizedPosition.orientedInteriorRowPushforward_slotMoment`
does on the small side, the reversed receipt implies the forward one, because
the two weights differ by the whole slot length and that is a multiple of the
scale. -/

/-- The scaled length of a **retained** big slot is a multiple of the scale.
(It is not for a contracted slot: `kindLength T .contracted = 1` at every
scale, which is why that case is excluded.) -/
theorem kindLength_scale_dvd (small : Spec n p) (k : ℕ) (hk : 0 < k)
    {kind : SlotKind p} (hne : kind ≠ SlotKind.contracted) :
    k ∣ kindLength (small.scale k hk) kind := by
  cases kind with
  | contracted => exact absurd rfl hne
  | single j => exact ⟨small.length j, rfl⟩
  | double j₁ j₂ => exact ⟨small.length j₁ + small.length j₂, by
      simp only [kindLength, Spec.scale_length, Nat.mul_add]⟩

/-- **The reversed receipt implies the forward one.**  If the odd-denominator
condition holds for the distance measured from the far end of the big slot, it
holds for the distance measured from the near end. -/
theorem ratTerms_of_reversed (T : Spec n p) (fallback : Fin n) (kind : SlotKind p)
    (Dv : CFDiv T.graph) (k : ℕ) (hk : 0 < k) (hlen : k ∣ kindLength T kind)
    (hTerms : ∀ q : ℕ, q + 1 < kindLength T kind →
      (Dv (kindVertex T fallback kind (q + 1)) : ℚ) *
        (((kindLength T kind - (q + 1) : ℕ) : ℚ) / k) ∈ oddDenominatorSubring)
    (q : ℕ) (hq : q + 1 < kindLength T kind) :
    (Dv (kindVertex T fallback kind (q + 1)) : ℚ) * (((q + 1 : ℕ) : ℚ) / k)
      ∈ oddDenominatorSubring := by
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  obtain ⟨m, hm⟩ := hlen
  set chip : ℤ := Dv (kindVertex T fallback kind (q + 1)) with hchip
  have hfull : (chip : ℚ) * ((kindLength T kind : ℚ) / k) ∈ oddDenominatorSubring := by
    have hquot : (kindLength T kind : ℚ) / k = (m : ℚ) := by
      rw [hm]; push_cast; field_simp
    rw [hquot]
    exact oddDenominatorSubring.mul_mem (intCast_mem _ chip) (natCast_mem _ m)
  have hdiff := oddDenominatorSubring.sub_mem hfull (hTerms q hq)
  have hcast : (chip : ℚ) * ((kindLength T kind : ℚ) / k) -
      (chip : ℚ) * (((kindLength T kind - (q + 1) : ℕ) : ℚ) / k) =
      (chip : ℚ) * (((q + 1 : ℕ) : ℚ) / k) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    field_simp
    ring
  rwa [hcast] at hdiff

/-! ## 4.  Every small slot at once, through the datum's own bookkeeping -/

variable {N Q : ℕ}

/-- **The transport, for every requested slot at once.**  A divisor on the
scaled *small* subdivision whose chips satisfy the per-position odd-denominator
condition **along the big slots** — i.e. read with the offsets of
`D.bigCore`, which is the only place a member over `D.bigCore` at the degenerate
request knows its positions — has `2 ^ a`-divisible moments on every slot of the
small request.

The routing is `ExpansionData.exists_carrier`: a requested slot is either the
whole of a retained `single`, or the first or the second half of a retained
`double`, and `side` says which.  No other clause of `D.Conditions` is used. -/
theorem dvd_slotMoment_of_expansion (small : Spec n p) {D : ExpansionData n p N Q}
    (hCond : D.Conditions small.core) (k a : ℕ) (hk : 0 < k) (hka : 2 ^ a ∣ k)
    (Dv : CFDiv (small.scale k hk).graph) (fallback : Fin n)
    (hTerms : ∀ (e : Fin Q) (q : ℕ),
        q + 1 < kindLength (small.scale k hk) (D.kind e) →
      (Dv (kindVertex (small.scale k hk) fallback (D.kind e) (q + 1)) : ℚ) *
        (((q + 1 : ℕ) : ℚ) / k) ∈ oddDenominatorSubring)
    (j : Fin p) :
    ((2 ^ a : ℕ) : ℤ) ∣
      InteriorFiring.slotMoment (small.scale k hk) Dv j := by
  have hseam : ∀ i : Fin p, k ∣ (small.scale k hk).length i :=
    fun i ↦ ⟨small.length i, rfl⟩
  have hE := hTerms (D.owner j)
  rcases ExpansionData.exists_carrier hCond j with
    ⟨hkind, -⟩ | ⟨j₂, hkind, -⟩ | ⟨j₁, hkind, -⟩
  · rw [hkind] at hE
    exact dvd_slotMoment_single_of_ratTerms _ fallback j Dv k a hk hka hE
  · rw [hkind] at hE
    exact (dvd_slotMoment_double_of_ratTerms _ fallback j j₂ Dv k a hk hka
      (hseam j) hE).1
  · rw [hkind] at hE
    exact (dvd_slotMoment_double_of_ratTerms _ fallback j₁ j Dv k a hk hka
      (hseam j₁) hE).2

/-- **The same, with the row read from the far end of each big slot.**  The
direction convention is not an extra arithmetic assumption: the reversed
receipt is converted to the forward one slot by slot by `ratTerms_of_reversed`,
using only that a retained big slot's scaled length is a multiple of the
scale. -/
theorem dvd_slotMoment_of_expansion_reversed (small : Spec n p)
    {D : ExpansionData n p N Q} (hCond : D.Conditions small.core)
    (k a : ℕ) (hk : 0 < k) (hka : 2 ^ a ∣ k)
    (Dv : CFDiv (small.scale k hk).graph) (fallback : Fin n)
    (hTerms : ∀ (e : Fin Q) (q : ℕ),
        q + 1 < kindLength (small.scale k hk) (D.kind e) →
      (Dv (kindVertex (small.scale k hk) fallback (D.kind e) (q + 1)) : ℚ) *
        (((kindLength (small.scale k hk) (D.kind e) - (q + 1) : ℕ) : ℚ) / k)
          ∈ oddDenominatorSubring)
    (j : Fin p) :
    ((2 ^ a : ℕ) : ℤ) ∣
      InteriorFiring.slotMoment (small.scale k hk) Dv j := by
  refine dvd_slotMoment_of_expansion small hCond k a hk hka Dv fallback ?_ j
  intro e q hq
  have hne : D.kind e ≠ SlotKind.contracted := by
    intro hcontr
    rw [hcontr] at hq
    simp only [kindLength] at hq
    omega
  exact ratTerms_of_reversed _ fallback (D.kind e) Dv k hk
    (kindLength_scale_dvd small k hk hne) (hTerms e) q hq

/-! ## 4a.  From a divisor on the big spec, by the contraction

The member lives over `D.bigCore`, so its transported divisor lives on
the **big** subdivision.  `ExpansionData.vertexMap` is the contraction
onto the small one, and `ExpansionData.interior_fibre` says its fibres over
interior images are singletons.  So the naive pushforward has the *same*
coefficient at `kindVertex` positions as the big divisor has at the
corresponding big interior vertex, and the per-position receipts carry over with
nothing to prove about multiplicities. -/

/-- `kindVertex` reads its `fallback` only on a contracted slot. -/
theorem kindVertex_fallback_irrel (T : Spec n p) (fb fb' : Fin n) {kind : SlotKind p}
    (hne : kind ≠ SlotKind.contracted) (q : ℕ) :
    kindVertex T fb kind q = kindVertex T fb' kind q := by
  cases kind with
  | contracted => exact absurd rfl hne
  | single j => rfl
  | double j₁ j₂ => rfl

variable (D : ExpansionData n p N Q) (small : Spec n p) (hN : 0 < N)
  (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)

/-- The naive finite pushforward of a divisor on the expanded subdivision along
the contraction `ExpansionData.vertexMap`. -/
noncomputable def pushDivisor (Bv : CFDiv (D.bigSpec small hN hL).graph) :
    CFDiv small.graph := by
  classical
  exact fun w ↦ ∑ v : (D.bigSpec small hN hL).Vertex,
    if ExpansionData.vertexMap D small hN hL v = w then Bv v else 0

/-- The expanded specification's slot lengths are the kind lengths. -/
theorem bigSpec_length (e : Fin Q) :
    (D.bigSpec small hN hL).length e = kindLength small (D.kind e) := rfl

variable {D small hN hL}

/-- **The pushforward keeps the coefficient at every interior image.**  Only
`ExpansionData.interior_fibre` is used: the fibre over such an image is the
singleton `{interiorVertex e o}`. -/
theorem pushDivisor_interior (hCond : D.Conditions small.core)
    (Bv : CFDiv (D.bigSpec small hN hL).graph) (e : Fin Q)
    (o : Fin ((D.bigSpec small hN hL).length e - 1)) :
    pushDivisor D small hN hL Bv
        (kindVertex small (D.fib (D.bigCore.tail e)) (D.kind e) (o.val + 1)) =
      Bv ((D.bigSpec small hN hL).interiorVertex e o) := by
  classical
  have himage : ExpansionData.vertexMap D small hN hL
      ((D.bigSpec small hN hL).interiorVertex e o) =
      kindVertex small (D.fib (D.bigCore.tail e)) (D.kind e) (o.val + 1) := rfl
  show (∑ v : (D.bigSpec small hN hL).Vertex,
      if ExpansionData.vertexMap D small hN hL v =
        kindVertex small (D.fib (D.bigCore.tail e)) (D.kind e) (o.val + 1) then Bv v
      else 0) = _
  rw [Finset.sum_eq_single ((D.bigSpec small hN hL).interiorVertex e o)]
  · rw [ite_eq_left himage]
  · intro v _ hne
    refine ite_eq_right ?_
    intro hv
    exact hne (ExpansionData.interior_fibre hCond e o v (hv.trans himage.symm))
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- The pushforward of an effective divisor is effective. -/
theorem effective_pushDivisor (Bv : CFDiv (D.bigSpec small hN hL).graph)
    (hEff : effective Bv) : effective (pushDivisor D small hN hL Bv) := by
  classical
  intro w
  show 0 ≤ ∑ v : (D.bigSpec small hN hL).Vertex,
    if ExpansionData.vertexMap D small hN hL v = w then Bv v else 0
  refine Finset.sum_nonneg ?_
  intro v _
  split_ifs with h
  · exact hEff v
  · exact le_rfl

/-- The pushforward has the same total degree. -/
theorem deg_pushDivisor (Bv : CFDiv (D.bigSpec small hN hL).graph) :
    deg (pushDivisor D small hN hL Bv) = deg Bv := by
  classical
  show (∑ w : small.Vertex, ∑ v : (D.bigSpec small hN hL).Vertex,
      if ExpansionData.vertexMap D small hN hL v = w then Bv v else 0)
    = ∑ v : (D.bigSpec small hN hL).Vertex, Bv v
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [Finset.sum_ite_eq Finset.univ (ExpansionData.vertexMap D small hN hL v)
    (fun _ ↦ Bv v), ite_eq_left (Finset.mem_univ _)]

/-- **The per-position receipts transfer from the big side.**  This is the
hypothesis `dvd_slotMoment_of_expansion` consumes, produced from the same
condition stated on the expanded subdivision, where a member over `D.bigCore`
actually knows where its chips are. -/
theorem ratTerms_of_pushDivisor (hCond : D.Conditions small.core)
    (Bv : CFDiv (D.bigSpec small hN hL).graph) (k : ℕ) (fallback : Fin n)
    (hBig : ∀ (e : Fin Q) (o : Fin ((D.bigSpec small hN hL).length e - 1)),
      (Bv ((D.bigSpec small hN hL).interiorVertex e o) : ℚ) *
        (((o.val + 1 : ℕ) : ℚ) / k) ∈ oddDenominatorSubring)
    (e : Fin Q) (q : ℕ) (hq : q + 1 < kindLength small (D.kind e)) :
    (pushDivisor D small hN hL Bv (kindVertex small fallback (D.kind e) (q + 1)) : ℚ) *
      (((q + 1 : ℕ) : ℚ) / k) ∈ oddDenominatorSubring := by
  have hne : D.kind e ≠ SlotKind.contracted := by
    intro hcontr
    rw [hcontr] at hq
    simp only [kindLength] at hq
    omega
  have hlen : (D.bigSpec small hN hL).length e = kindLength small (D.kind e) := rfl
  rw [kindVertex_fallback_irrel small fallback (D.fib (D.bigCore.tail e)) hne (q + 1),
    pushDivisor_interior hCond Bv e ⟨q, by omega⟩]
  exact hBig e ⟨q, by omega⟩

/-- **The transport, from a divisor on the expanded subdivision.**  A divisor on
`(D.bigSpec (small.scale k hk) hN hL).graph` — the expanded model with every
retained slot already at its scaled length and every forest slot at length one —
whose interior chips carry the per-position odd-denominator receipt pushes
forward to a divisor on `(small.scale k hk).graph` with `2 ^ a`-divisible
moments on **every** requested slot.

This is the endgame step with the geometry stripped away: what remains to be
produced is the big-side divisor and its receipts. -/
theorem dvd_slotMoment_of_bigDivisor (small : Spec n p) {D : ExpansionData n p N Q}
    {hN : 0 < N} {hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e}
    (hCond : D.Conditions small.core) (k a : ℕ) (hk : 0 < k) (hka : 2 ^ a ∣ k)
    (Bv : CFDiv (D.bigSpec (small.scale k hk) hN hL).graph)
    (hBig : ∀ (e : Fin Q)
        (o : Fin ((D.bigSpec (small.scale k hk) hN hL).length e - 1)),
      (Bv ((D.bigSpec (small.scale k hk) hN hL).interiorVertex e o) : ℚ) *
        (((o.val + 1 : ℕ) : ℚ) / k) ∈ oddDenominatorSubring)
    (j : Fin p) :
    ((2 ^ a : ℕ) : ℤ) ∣ InteriorFiring.slotMoment (small.scale k hk)
      (pushDivisor D (small.scale k hk) hN hL Bv) j :=
  dvd_slotMoment_of_expansion small hCond k a hk hka
    (pushDivisor D (small.scale k hk) hN hL Bv) ⟨0, small.core_nonempty⟩
    (ratTerms_of_pushDivisor (small := small.scale k hk) (hN := hN) (hL := hL)
      hCond Bv k ⟨0, small.core_nonempty⟩ hBig) j

/-! ## 5.  Fed to the endgame -/

/-- **The arithmetic half, wired to `TransportedChipEndgame`.**

Given a degree-four effective rank-one divisor on `(small.scale (2 ^ a * u)).graph`
whose chips carry the per-position odd-denominator condition along the big slots
of an expansion datum over `small`, Brill--Noether existence holds on the
subdivision at the **odd part** `u` of the scale.

Everything here except the hypotheses is proved: the descent to the odd part is
`TransportedChipEndgame.bnExists_of_pencil_slotMoment`, which needs no member, no
cubicity and no genericity. -/
theorem bnExists_of_expansion (small : Spec n p) {D : ExpansionData n p N Q}
    (hCond : D.Conditions small.core) (u a : ℕ) (hu : 0 < u)
    (hk : 0 < 2 ^ a * u) (Dv : CFDiv (small.scale (2 ^ a * u) hk).graph)
    (fallback : Fin n) (hEff : effective Dv)
    (hDeg : deg Dv = ((4 : ℕ) : ℤ))
    (hRank : rank (small.scale (2 ^ a * u) hk).graph Dv ≥ 1)
    (hTerms : ∀ (e : Fin Q) (q : ℕ),
        q + 1 < kindLength (small.scale (2 ^ a * u) hk) (D.kind e) →
      (Dv (kindVertex (small.scale (2 ^ a * u) hk) fallback (D.kind e) (q + 1)) : ℚ) *
        (((q + 1 : ℕ) : ℚ) / ((2 ^ a * u : ℕ) : ℚ)) ∈ oddDenominatorSubring) :
    BNExists (small.scale u hu).graph 1 4 :=
  TransportedChipEndgame.bnExists_of_pencil_slotMoment small u a hu
    ⟨2 ^ a * u, hk, Dv, hEff, hDeg, hRank⟩ rfl
    (fun e ↦ dvd_slotMoment_of_expansion small hCond (2 ^ a * u) a hk ⟨u, rfl⟩ Dv
      fallback hTerms e)

/-- **The same, starting from the expanded model.**  A divisor on the expanded
subdivision whose interior chips carry the per-position odd-denominator receipt,
and whose pushforward is effective of degree four and rank at least one, gives
Brill--Noether existence on the requested subdivision at the odd part of the
scale.

This is the statement a producer of the pencil should aim at: only the three
hypotheses are left: effectivity and degree four **on the big side** (carried
across by `effective_pushDivisor` and `deg_pushDivisor`), the per-position
receipts on the big side, and rank at least one on the pushforward — the last
being the only genuinely geometric one, and the same `hRank` that
`TransportedChipEndgame` asks for. -/
theorem bnExists_of_bigDivisor (small : Spec n p) {D : ExpansionData n p N Q}
    {hN : 0 < N} {hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e}
    (hCond : D.Conditions small.core) (u a : ℕ) (hu : 0 < u) (hk : 0 < 2 ^ a * u)
    (Bv : CFDiv (D.bigSpec (small.scale (2 ^ a * u) hk) hN hL).graph)
    (hEff : effective Bv) (hDeg : deg Bv = ((4 : ℕ) : ℤ))
    (hRank : rank (small.scale (2 ^ a * u) hk).graph
      (pushDivisor D (small.scale (2 ^ a * u) hk) hN hL Bv) ≥ 1)
    (hBig : ∀ (e : Fin Q)
        (o : Fin ((D.bigSpec (small.scale (2 ^ a * u) hk) hN hL).length e - 1)),
      (Bv ((D.bigSpec (small.scale (2 ^ a * u) hk) hN hL).interiorVertex e o) : ℚ) *
        (((o.val + 1 : ℕ) : ℚ) / ((2 ^ a * u : ℕ) : ℚ)) ∈ oddDenominatorSubring) :
    BNExists (small.scale u hu).graph 1 4 :=
  TransportedChipEndgame.bnExists_of_pencil_slotMoment small u a hu
    ⟨2 ^ a * u, hk, pushDivisor D (small.scale (2 ^ a * u) hk) hN hL Bv,
      effective_pushDivisor Bv hEff, (deg_pushDivisor Bv).trans hDeg, hRank⟩
    rfl
    (fun e ↦ dvd_slotMoment_of_bigDivisor small hCond (2 ^ a * u) a hk ⟨u, rfl⟩ Bv hBig e)

/-! ## 6.  The aggregate hypothesis is strictly weaker — a bounded witness

`dvd_seriesMoment_double_iff` says the series moment only sees the *sum*.  This
section exhibits an actual `Spec` and an actual divisor at which the seam
hypothesis holds, the series moment is even, and the first small moment is odd,
so that no strengthening of `dvd_seriesMoment_double_iff` can recover §3's
conclusion from an aggregate hypothesis. -/

namespace SplitWitness

/-- The path `0 — 1 — 2` on two slots. -/
def core : ExplicitPotential.Core 3 2 where
  tail := ![0, 1]
  head := ![1, 2]

/-- Both slots of length two, so the seam sits at position `2`. -/
def spec : Spec 3 2 :=
  Spec.ofCore core (by norm_num) (by decide) ![2, 2] (by decide)

theorem spec_length (e : Fin 2) : spec.length e = 2 := by
  fin_cases e <;> rfl

/-- One chip on the interior of slot `0`, one anti-chip on the interior of slot
`1`, nothing at the marker. -/
def divisor : CFDiv spec.graph
  | Sum.inl _ => 0
  | Sum.inr point => if point.1 = 0 then 1 else -1

theorem slotMoment_zero : InteriorFiring.slotMoment spec divisor 0 = 1 := by
  have h : InteriorFiring.slotMoment spec divisor 0
      = ∑ o : Fin 1, divisor (spec.interiorVertex 0 o) * ((o.val + 1 : ℕ) : ℤ) := rfl
  rw [h, Fin.sum_univ_one]
  decide

theorem slotMoment_one : InteriorFiring.slotMoment spec divisor 1 = -1 := by
  have h : InteriorFiring.slotMoment spec divisor 1
      = ∑ o : Fin 1, divisor (spec.interiorVertex 1 o) * ((o.val + 1 : ℕ) : ℤ) := rfl
  rw [h, Fin.sum_univ_one]
  decide

theorem slotCount_one : InteriorFiring.slotCount spec divisor 1 = -1 := by
  have h : InteriorFiring.slotCount spec divisor 1
      = ∑ o : Fin 1, divisor (spec.interiorVertex 1 o) := rfl
  rw [h, Fin.sum_univ_one]
  decide

theorem marker_eq_zero : divisor (spec.coreVertex (spec.core.head 0)) = 0 := rfl

theorem seriesMoment_eq : seriesMoment spec 0 (SlotKind.double 0 1) divisor = -2 := by
  rw [seriesMoment_double, slotMoment_zero, slotMoment_one, slotCount_one,
    marker_eq_zero, spec_length]
  norm_num

/-- **The bounded negative.**  At this `Spec` and this divisor the seam position
is even and the series moment is even, yet the first slot's own moment is odd.
So `2 ∣ seriesMoment` does **not** imply `2 ∣ slotMoment j₁`, and §3's
per-position hypothesis is not a convenience. -/
theorem aggregate_does_not_split :
    (2 : ℤ) ∣ ((spec.length 0 : ℕ) : ℤ) ∧
      (2 : ℤ) ∣ seriesMoment spec 0 (SlotKind.double 0 1) divisor ∧
      ¬ (2 : ℤ) ∣ InteriorFiring.slotMoment spec divisor 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [spec_length]; norm_num
  · rw [seriesMoment_eq]; norm_num
  · rw [slotMoment_zero]; norm_num

end SplitWitness

/-! ## 7.  The odd-scale corollary

`RetainedIndexProducer.exists_expansionModel_retainedIndex` delivers
`pencil.scale = k`, which is strictly stronger than `Odd pencil.scale`.  Its odd
corollary is the following four lines, stated against that last clause verbatim
so that it is applied by `obtain` and nothing is restated. -/

/-- **`Odd pencil.scale` from the scale-exact transport.**  `htransport`
is the final clause of
`LocalCases.RetainedIndexProducer.exists_expansionModel_retainedIndex`, copied
without change. -/
theorem exists_odd_subdivisionPencil {n₁ p₁ n₀ p₀ : ℕ} {spec : Spec n₁ p₁}
    {spec₀ : Spec n₀ p₀}
    (htransport : ∀ (d k : ℕ) (hk : 0 < k), BNExists (spec₀.scale k hk).graph 1 (d : ℤ) →
      ∃ pencil : DraismaVargas.SubdivisionPencil spec d, pencil.scale = k)
    (d k : ℕ) (hk : 0 < k) (hOdd : Odd k)
    (hBN : BNExists (spec₀.scale k hk).graph 1 (d : ℤ)) :
    ∃ pencil : DraismaVargas.SubdivisionPencil spec d, Odd pencil.scale := by
  obtain ⟨pencil, hscale⟩ := htransport d k hk hBN
  exact ⟨pencil, hscale ▸ hOdd⟩

end DraismaVargas.Count.ExpansionSeriesMoment
