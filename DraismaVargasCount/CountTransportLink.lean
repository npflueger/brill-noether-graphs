import DraismaVargasCount.GeometricSegmentWalls
import DraismaVargasCount.NonTrivalentNonfacetDenominator

/-!
# The per-wall link of the count transport

**Source.**  Vargas, Part II (arXiv:2609.09109): the count of the section
*Invariance of the count via continuous deformation* (general paths,
`proposition-generic-path`; the balancing condition, `prop-signed-mult`; wall
crossing, `proposition-walking-through-II`) and the lemma on determinants and
multiplicities across non-trivalent limits (`lm:change-comb-type`).  The count is
transported along one generic segment per cone and one link per type change.

## What a link is here, and why it is stated this way

The walk from the caterpillar base to a requested pair (core, request) crosses
two kinds of wall, and the transport must accept both **without privileging
either**:

* an **in-cone** wall -- the core is unchanged and a *cover* coordinate of some
  frame vanishes (`SegmentWalls.Frame.IsWallParam`).  This is a trivalent wall
  (step 2 of `Assembly`): the star's `Σ_q signedMult φ_q = 0` together with
  side = sign (`ConeSide`) is what handles it;
* a **type-change** wall -- the core itself degenerates and a Whitehead move
  produces the next cubic type.  This is a non-trivalent wall (step 3 of
  `Assembly`), whose multiplicity input is
  `NonTrivalentNonfacetDenominator.signedMult_eq_of_typeChangeLink`, stated on
  `LocalCases.OuterWalk.TypeChangeLink`.

There is no single *evidence* shape common to the two: a trivalent wall
creates and destroys open odd classes in pairs (no bijection), a type change
matches them (a bijection but across two different cores).  The neutral object
is therefore the **conclusion** -- "the two sides' `openOddCount` have the same
parity" -- with a separate *producer* for each kind.  `CountLink` is that
object, and the schedule (`CountSchedule`) consumes only it, never asking
which producer built it.

Nothing here is a weight or a multiplicity factor.  `openOddCount` counts
distinct labelled geometric classes, each once, and the star carries no weight
field.  The link is a statement about *how many* classes change status, never
about what they are worth.

## What is proved here

* `odd_iff_odd_iff_even_symmDiff` -- the arithmetic core, over an arbitrary
  finite type: two finite counts have the same parity **iff** the elements on
  which the two defining predicates disagree are even in number.  No fibre,
  no request, no multiplicity.
* `fibreEquiv_self` -- the canonical request-fibre identification at a single
  request is the identity, so a count read "through the identification" at the
  same request is the count itself.
* `openOddCount_eq_card_transported` -- `openOddCount` at `y'`, read inside the
  fibre at `y` through `GeometricSegmentWalls.fibreEquiv`.  This is the form in
  which the two sides of an in-cone wall are literally subsets of one finite
  type: under the canonical identification of the fibres over different requests
  (`GeometricSegmentWalls.fibreEquiv`, `SegmentWalls.absMult_member_eq`) only
  *openness* moves with the request, never the classes or their multiplicities.
* `CountLink` -- the link object, and `countLink_refl/symm/trans`: it is an
  equivalence relation on sites, which is what makes a chain of links compose.
* `countLink_of_openOddCount_eq` -- the degenerate producer (equal counts).
* `switchingCount` and `countLink_iff_even_switchingCount` -- **the in-cone
  producer, as an iff**: a link across an in-cone wall is *exactly* the
  evenness of the number of odd classes whose openness changes across it.  It
  is neither stronger nor weaker than the parity step, so a computation showing
  that "the star contributes an even number of status changes" gives the link,
  and nothing more is owed (see `SwitchingParity`).
* `countLink_of_oddOpenEquiv` -- **the type-change producer**: an equivalence
  of the two fibres matching `Open` with `Open` and `IsOdd` with `IsOdd` is a
  link.  The two cores are independent here, which is why this producer, and
  not the previous one, is the one a non-trivalent wall uses.
* `fdAbsMultNat_eq_of_typeChangeLink`,
  `odd_fdAbsMultNat_iff_of_typeChangeLink` -- **the adapter from Part I's
  wall-crossing architecture**: across an actual
  `OuterWalk.TypeChangeLink` the natural-number multiplicity is *equal*, hence
  odd on one side iff odd on the other.  This is
  `NonTrivalentNonfacetDenominator.signedMult_eq_of_typeChangeLink` read at the
  level the count uses (`fdAbsMultNat`, i.e. `FibreMember.oddMult`), and it is
  the member-level ingredient of the `countLink_of_oddOpenEquiv` hypothesis at a
  type change.

## What is NOT proved here -- every hypothesis

This file proves no link.  It states the link and proves the *criteria* under
which one exists.  Explicitly:

* **Nothing produces `Even (switchingCount …)` at an actual in-cone wall.**
  That is the parity at a trivalent wall (step 2 of `Assembly`).
  `countLink_iff_even_switchingCount` is an equivalence, not a producer.
* **Nothing produces the fibre equivalence of `countLink_of_oddOpenEquiv` at an
  actual type change.**  That is the parity at a type change (step 3 of
  `Assembly`).  The adapter proved here supplies only the *multiplicity* half of
  that equivalence (equal `fdAbsMultNat`), at a single matched pair of
  full-dimensional presentations; the matching itself -- a bijection of the two
  chambers' fibres -- is not made here.
* The adapter's hypothesis is an actual `OuterWalk.TypeChangeLink`; the
  identification of the two *fibres* it sits between is not made here.
* `openOddCount` is `GeometricFibre.openOddCount` -- the orientation-independent
  labelled count.  Nothing here compares it with the strict
  `Count.openOddCount`.

Consumers: `CountSchedule`, and through it `CountSchedule.C34`, the statement
proved in step 4 of `Assembly`.
-/

namespace DraismaVargas.Count.CountTransportLink

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open Utilities.Certificate.ExplicitPotential (Core)
open Finset

variable {n p degree : ℕ}

/-! ## 1.  Two finite counts have equal parity iff their disagreement set is even -/

/-- **The arithmetic core of a link.**  Over a finite type, the counts of two
predicates have the same parity exactly when the set on which the predicates
disagree has even cardinality.  Everything about walls, fibres and
multiplicities is stripped away; this is the only counting fact the link uses,
and in particular no element is ever weighted. -/
theorem odd_iff_odd_iff_even_symmDiff {T : Type*} [Finite T] (P Q : T → Prop) :
    (Odd (Nat.card {x // P x}) ↔ Odd (Nat.card {x // Q x})) ↔
      Even (Nat.card {x : T // ¬ (P x ↔ Q x)}) := by
  classical
  have _ : Fintype T := Fintype.ofFinite T
  have hA : Nat.card {x // P x} = (univ.filter P).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hB : Nat.card {x // Q x} = (univ.filter Q).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hS : Nat.card {x : T // ¬ (P x ↔ Q x)} =
      (univ.filter fun x ↦ ¬ (P x ↔ Q x)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  set A := univ.filter P with hAdef
  set B := univ.filter Q with hBdef
  have hUnion : (univ.filter fun x ↦ ¬ (P x ↔ Q x)) = (A \ B) ∪ (B \ A) := by
    ext x
    simp only [hAdef, hBdef, mem_filter, mem_union, mem_sdiff, mem_univ, true_and]
    tauto
  have hDisj : Disjoint (A \ B) (B \ A) :=
    Finset.disjoint_left.mpr fun x hx hx' ↦ (mem_sdiff.mp hx').2 (mem_sdiff.mp hx).1
  have hcard : A.card + B.card = (A \ B).card + (B \ A).card + 2 * (A ∩ B).card := by
    have h1 := Finset.card_sdiff_add_card_inter A B
    have h2 := Finset.card_sdiff_add_card_inter B A
    have h3 : (B ∩ A).card = (A ∩ B).card := congrArg Finset.card (Finset.inter_comm B A)
    omega
  rw [hA, hB, hS, hUnion, Finset.card_union_of_disjoint hDisj]
  rw [Nat.odd_iff, Nat.odd_iff, Nat.even_iff]
  omega

/-! ## 2.  The two sides of an in-cone wall inside one finite type -/

/-- **The canonical request-fibre identification at a single request is the
identity.**  `GeometricSegmentWalls.fibreEquiv` sends the class of a member to
the class of the same frame's member over the new request; at the same
request that is the member itself. -/
@[simp] theorem fibreEquiv_self (core : Core n p) (degree : ℕ) (y : Fin p → ℚ)
    (c : GeometricFibre core y degree) :
    GeometricSegmentWalls.fibreEquiv core degree y y c = c := by
  obtain ⟨member, rfl⟩ := GeometricFibre.cls_surjective c
  rw [GeometricSegmentWalls.fibreEquiv_cls, SegmentWalls.Frame.member_of]

/-- **`openOddCount` at `y'`, read inside the fibre at `y`.**  Through
`GeometricSegmentWalls.fibreEquiv` the labelled geometric fibre is canonically
the same finite type at every request
and the multiplicities do not move at all, so the only thing that moves is
which classes are open.  Both sides of an in-cone wall are therefore subsets of
one finite type, which is what lets `odd_iff_odd_iff_even_symmDiff` apply. -/
theorem openOddCount_eq_card_transported (core : Core n p) (degree : ℕ)
    (y y' : Fin p → ℚ) :
    GeometricFibre.openOddCount core y' degree =
      Nat.card {c : GeometricFibre core y degree //
        (GeometricSegmentWalls.fibreEquiv core degree y y' c).Open ∧ c.IsOdd} := by
  refine (Nat.card_congr (Equiv.subtypeEquiv
    (GeometricSegmentWalls.fibreEquiv core degree y y') fun c ↦ ?_)).symm
  exact and_congr Iff.rfl
    (GeometricSegmentWalls.isOdd_fibreEquiv core degree y y' c).symm

/-! ## 3.  The link -/

/-- **The link: what one wall of the count schedule has to carry.**  The two
sides may sit over *different* cores -- at a type-change wall they do -- so the
two cores and the two requests are independent.  Nothing is asserted about the
classes themselves, only about the parity of how many open ones have odd
multiplicity. -/
def CountLink (degree : ℕ) {n p n' p' : ℕ} (core : Core n p) (y : Fin p → ℚ)
    (core' : Core n' p') (y' : Fin p' → ℚ) : Prop :=
  Odd (GeometricFibre.openOddCount core y degree) ↔
    Odd (GeometricFibre.openOddCount core' y' degree)

theorem countLink_refl (degree : ℕ) (core : Core n p) (y : Fin p → ℚ) :
    CountLink degree core y core y := Iff.rfl

theorem countLink_symm {n' p' : ℕ} {core : Core n p} {core' : Core n' p'}
    {y : Fin p → ℚ} {y' : Fin p' → ℚ} (h : CountLink degree core y core' y') :
    CountLink degree core' y' core y := h.symm

theorem countLink_trans {n' p' n'' p'' : ℕ} {core : Core n p} {core' : Core n' p'}
    {core'' : Core n'' p''} {y : Fin p → ℚ} {y' : Fin p' → ℚ} {y'' : Fin p'' → ℚ}
    (h : CountLink degree core y core' y') (h' : CountLink degree core' y' core'' y'') :
    CountLink degree core y core'' y'' := h.trans h'

/-- The degenerate producer: equal counts are a link.  This is how the
constancy of the count along a segment that crosses no wall
(`GeometricSegmentWalls.openOddCount_eq_of_no_wall`) enters. -/
theorem countLink_of_openOddCount_eq {n' p' : ℕ} {core : Core n p} {core' : Core n' p'}
    {y : Fin p → ℚ} {y' : Fin p' → ℚ}
    (h : GeometricFibre.openOddCount core y degree =
      GeometricFibre.openOddCount core' y' degree) :
    CountLink degree core y core' y' := by
  rw [CountLink, h]

/-! ## 4.  The in-cone producer: the switching classes -/

/-- **The odd classes whose openness changes between two requests over one
core.**  Read inside the fibre at `y` through the canonical identification
`GeometricSegmentWalls.fibreEquiv`.
Each class is counted once; there is no weight. -/
noncomputable def switchingCount (core : Core n p) (degree : ℕ) (y y' : Fin p → ℚ) : ℕ :=
  Nat.card {c : GeometricFibre core y degree //
    c.IsOdd ∧ ¬ (c.Open ↔ (GeometricSegmentWalls.fibreEquiv core degree y y' c).Open)}

/-- **Nothing switches between a request and itself.**  A sanity check on the
definition: `switchingCount` measures a *change*, so it vanishes when there is
none. -/
@[simp] theorem switchingCount_self (core : Core n p) (degree : ℕ) (y : Fin p → ℚ) :
    switchingCount core degree y y = 0 := by
  have hempty : IsEmpty {c : GeometricFibre core y degree //
      c.IsOdd ∧ ¬ (c.Open ↔ (GeometricSegmentWalls.fibreEquiv core degree y y c).Open)} := by
    constructor
    rintro ⟨c, -, h⟩
    exact h (by rw [fibreEquiv_self])
  rw [switchingCount]
  exact Nat.card_of_isEmpty

/-- **The in-cone criterion, as an equivalence.**  Over one core, a link between
two requests holds **exactly** when an even number of odd classes change their
openness between them.  This is the shape the parity at a trivalent wall has to
produce, and the equivalence says it needs neither more nor less. -/
theorem countLink_iff_even_switchingCount (core : Core n p) (degree : ℕ)
    (y y' : Fin p → ℚ) :
    CountLink degree core y core y' ↔ Even (switchingCount core degree y y') := by
  have hY : GeometricFibre.openOddCount core y degree =
      Nat.card {c : GeometricFibre core y degree // c.Open ∧ c.IsOdd} := rfl
  have hY' := openOddCount_eq_card_transported core degree y y'
  have hswitch : switchingCount core degree y y' =
      Nat.card {c : GeometricFibre core y degree //
        ¬ ((c.Open ∧ c.IsOdd) ↔
          ((GeometricSegmentWalls.fibreEquiv core degree y y' c).Open ∧ c.IsOdd))} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun c ↦ ?_)
    by_cases hodd : c.IsOdd
    · simp only [hodd, and_true, true_and]
    · simp only [hodd, and_false, false_and, iff_self, not_true]
  rw [CountLink, hY, hY', hswitch]
  exact odd_iff_odd_iff_even_symmDiff _ _

/-! ## 5.  The type-change producer -/

/-- **The type-change producer.**  An equivalence of the two fibres that matches
open classes with open classes and odd classes with odd classes is a link.  The
two cores are unrelated here, which is why this, and not the switching
criterion, is the producer a non-trivalent wall uses: across a type change the
requests live over different cores and there is no single fibre to take a
symmetric difference in. -/
theorem countLink_of_oddOpenEquiv {n' p' : ℕ} {core : Core n p} {core' : Core n' p'}
    {y : Fin p → ℚ} {y' : Fin p' → ℚ}
    (e : GeometricFibre core y degree ≃ GeometricFibre core' y' degree)
    (hopen : ∀ c, (e c).Open ↔ c.Open) (hodd : ∀ c, (e c).IsOdd ↔ c.IsOdd) :
    CountLink degree core y core' y' :=
  countLink_of_openOddCount_eq
    (Nat.card_congr (Equiv.subtypeEquiv e fun c ↦ ⟨fun h ↦ ⟨(hopen c).mpr h.1,
      (hodd c).mpr h.2⟩, fun h ↦ ⟨(hopen c).mp h.1, (hodd c).mp h.2⟩⟩))

/-! ## 6.  The adapter from Part I's type-change architecture -/

section Adapter

open OuterWalk
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource

variable {κ : Type} [Fintype κ] [DecidableEq κ]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {ambient : Infrastructure.CubicDarts.CubicDartGraph D V}
  {label : D → κ} {mv : ambient.MoveData}
  {arrival : FacetArrival degree ambient label (label mv.base)}
  {wd : WallData arrival} (link : TypeChangeLink mv wd)

/-- **Equal multiplicity across a type change, at the level the count uses.**
Across an actual type-change link the
natural-number multiplicity -- `FibreMember.oddMult`, i.e. `|Mult φ|` as a
natural number -- is *equal* on the two sides.  This is
`NonTrivalentNonfacetDenominator.signedMult_eq_of_typeChangeLink` read through
`absMultNat = (signedMult).num.natAbs`. -/
theorem fdAbsMultNat_eq_of_typeChangeLink :
    fdAbsMultNat link.outgoingFD = fdAbsMultNat wd.fullDim :=
  congrArg (fun q : ℚ ↦ q.num.natAbs)
    (NonTrivalentNonfacetDenominator.signedMult_eq_of_typeChangeLink link)

/-- **The oddness half of a non-trivalent link, from Part I's wall crossing.**
Odd multiplicity is preserved across an actual type change, with no hypothesis
beyond the link itself.  This is the ingredient the fibre equivalence of
`countLink_of_oddOpenEquiv` needs on multiplicities; the equivalence of the two
chambers' fibres is not proved here. -/
theorem odd_fdAbsMultNat_iff_of_typeChangeLink :
    Odd (fdAbsMultNat link.outgoingFD) ↔ Odd (fdAbsMultNat wd.fullDim) := by
  rw [fdAbsMultNat_eq_of_typeChangeLink link]

end Adapter

end DraismaVargas.Count.CountTransportLink
