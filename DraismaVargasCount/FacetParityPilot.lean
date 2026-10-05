module

public import DraismaVargasCount.FacetMachine

@[expose] public section

/-!
# `FacetParity`: the weaker consumer and the per-limit shapes

This module builds on the facet machine (`Count/FacetMachine.lean`), whose one open input is
`FacetMachine.FacetParity`, and provides the forms in which `FacetParity` is discharged: a
consumer that needs it at one facet datum per step, and the per-limit shapes that imply it.
The type changes of the genus-six assembly (step 3 of `Assembly`) go through
`typeChangeSupplyPositive_of_exists_facetParity`, called by
`FacetCensus.typeChangeSupplyPositive_of_metricCensus`.

## Two observations

Computer enumeration (not part of this library) supports `FacetParity` at the genus-six
Whitehead steps out of the caterpillar of loops -- at the six stem slots every facet limit
is `1 + 1` at a **valency-three** anchor, and at the three spine slots the limits are
`1 + 1, 2 + 2, 2 + 2` at a **valency-four** anchor, the `K`-family with two members on each
side -- and at every genus-four Whitehead step.  Two features of that data shape what is
proved below.

* **Coarse uniqueness fails at valency four.**  `FacetLimit` is unlabelled, and
  at a valency-four anchor one coarse limit carries two odd classes on each
  side.  So "at most one class per facet limit" does not hold in general; the
  valency-two/three shape `facetParity_of_unique` is only for those anchors,
  and the general shape is `facetParity_of_injective_index` (index `K`).
* **The unlabelled limit does not pin the frame class.**  At the limit of
  `cat_facetParity_domain` the far-side datum carries two ident orbits over
  `catLoopCore` (the digon swap of slots `0`, `1`); exactly one of them is
  degenerate at the facet point, the other has a negative coordinate.  So a
  uniqueness proof on the far side must use the slot label `e₀`
  (`FacetMachine.bridgeRow_of_degenerateAt`) and the metric of `y₀`, not only the
  combinatorial limit.

## What is proved here

* `exists_facetParity_of_forall` and `typeChangeSupplyPositive_step_of_exists_facetParity`,
  `typeChangeSupplyPositive_of_exists_facetParity`,
  `c34_genusSix_of_exists_facetParity` -- **the weaker consumer**: the
  type-change obligation needs `FacetParity` at **one** facet datum per step,
  not at every one.  The facet machine's consumer quantifies over all facet data; this
  one lets the prover *choose* the facet point (e.g. one that is also Part I's
  `FacetGenericity.FacetGeneric`), and it is implied by the machine's form
  (`exists_facetParity_of_forall`).
* `facetParity_of_injective_index` -- **the general per-limit shape**: two
  injective labellings of the two odd fibres by a common index set, with equal
  ranges.  It covers the valency-four `K`-family (index: the pairing's `K`)
  and the valency-two/three cases (index: `Unit`).
* `facetParity_of_equiv_isOdd` -- a bijection of the *whole* specialising
  fibres preserving oddness (what a matching of candidates delivers).
* `facetParity_of_unique` -- **the valency-two/three shape**: at most one odd class on each
  side per limit, and an odd class on one side exists iff one exists on the other.  Its two
  halves are *uniqueness* (the members of each type at valency three and two) and
  *existence with equal parity* (Part I's `TypeChangeLink` producers and
  `NonTrivalentNonfacetDenominator.signedMult_eq_of_typeChangeLink`, given an adapter from
  a facet regrowth to Part I's `WallData`).
* `cat_obligation_of_facetParity_at` -- the weaker consumer at the genus-six
  caterpillar step, whose antecedent's datum half is inhabited
  (`FacetMachine.exists_facetDatum`).

No new `Prop` is introduced: every statement takes explicit hypotheses, and `FacetParity`
remains the facet machine's predicate.

## What is not proved here

* **`FacetParity` is not proved here**, at any step.  The enumeration above is evidence,
  not a proof.  At genus six it holds at the facet data the assembly uses, through the
  census route (`FacetCensus`, `CensusAssembly`).
* The hypotheses of `facetParity_of_unique` (uniqueness of the odd class per
  facet limit on each side; existence of a far-side odd class) are not
  discharged here.  Existence needs an adapter from a `FacetMachine.FacetDatum`
  plus a `WallStar.Regrowth` to `OuterWalk.FacetArrival` / `WallData`, which is
  not built here.  `cat_step`'s limits are all at a **valency-three** anchor.  The
  uniqueness hypothesis fails at valency-four anchors (see above), so this lemma does not
  apply there; the genus-six proof does not use it.
* The hypotheses of `facetParity_of_injective_index` at valency four (the
  `K`-family) are not discharged here: injectivity of the index is proved in
  `Count/ValencyFourRigidity.lean` (`kIndexL_injective_of_v4`, `kIndexR_injective_of_v4`),
  and equal ranges (per-`K` realisation on both sides) in
  `Count/ValencyFourRealisation.lean` (`hex_of_resolved`).
* The `∃`-consumer still needs `FacetParity` for **every** facet limit at the
  chosen point, and `hcone`, `hbase`, `classification` of the count's positive
  assembly are carried exactly as `SimpleWallSupply.c34_genusSix_simple`
  carries them.
-/

namespace DraismaVargas.Count.FacetParityPilot

open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore Step)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)
open DraismaVargas.Count.SimpleWallSupply (PositiveGeneral TypeChangeSupplyPositive)
open DraismaVargas.Count.FacetMachine

variable {n p degree : ℕ}

/-! ## 1.  The weaker consumer: `FacetParity` at one facet datum per step -/

/-- **The every-datum hypothesis implies the one-datum hypothesis**: a facet datum always
exists (`FacetMachine.exists_facetDatum`), so `FacetParity` at every facet datum
gives it at one. -/
theorem exists_facetParity_of_forall {c c' : CubicCore n p} (hstep : Step c c')
    (hpar : ∀ (e₀ : Fin p) (y₀ : Fin p → ℚ) (ε : ℚ),
      FacetDatum c.core c'.core degree e₀ y₀ ε → FacetParity c.core c'.core degree y₀) :
    ∃ (e₀ : Fin p) (y₀ : Fin p → ℚ) (ε : ℚ),
      FacetDatum c.core c'.core degree e₀ y₀ ε ∧ FacetParity c.core c'.core degree y₀ := by
  obtain ⟨e₀, y₀, ε, hd⟩ := exists_facetDatum hstep degree
  exact ⟨e₀, y₀, ε, hd, hpar e₀ y₀ ε hd⟩

/-- **The per-step obligation from `FacetParity` at one facet datum.**  No step
hypothesis is needed once the datum is given: a facet datum already carries the
shared contraction slot. -/
theorem typeChangeSupplyPositive_step_of_exists_facetParity {c c' : Core n p}
    (hpar : ∃ (e₀ : Fin p) (y₀ : Fin p → ℚ) (ε : ℚ),
      FacetDatum c c' degree e₀ y₀ ε ∧ FacetParity c c' degree y₀) :
    ∃ y y' : Fin p → ℚ, PositiveGeneral c degree y ∧ PositiveGeneral c' degree y' ∧
      CountTransportLink.CountLink degree c y c' y' := by
  obtain ⟨e₀, y₀, ε, hd, hp⟩ := hpar
  exact ⟨_, _, hd.positiveGeneral_left, hd.positiveGeneral_right,
    countLink_of_facetParity hd hp⟩

/-- **`SimpleWallSupply.TypeChangeSupplyPositive` from `FacetParity` at one facet
datum of each step** -- the weaker consumer. -/
theorem typeChangeSupplyPositive_of_exists_facetParity
    (h : ∀ c c' : CubicCore n p, Step c c' →
      ∃ (e₀ : Fin p) (y₀ : Fin p → ℚ) (ε : ℚ),
        FacetDatum c.core c'.core degree e₀ y₀ ε ∧ FacetParity c.core c'.core degree y₀) :
    TypeChangeSupplyPositive degree n p :=
  fun c c' hstep ↦ typeChangeSupplyPositive_step_of_exists_facetParity (h c c' hstep)

/-- The facet machine's global consumer factors through the weaker one. -/
theorem typeChangeSupplyPositive_of_forall_facetParity
    (h : ∀ c c' : CubicCore n p, Step c c' →
      ∀ (e₀ : Fin p) (y₀ : Fin p → ℚ) (ε : ℚ),
        FacetDatum c.core c'.core degree e₀ y₀ ε → FacetParity c.core c'.core degree y₀) :
    TypeChangeSupplyPositive degree n p :=
  typeChangeSupplyPositive_of_exists_facetParity fun c c' hstep ↦
    exists_facetParity_of_forall hstep (h c c' hstep)

/-- **`CountSchedule.C34 2` with the type-change half replaced by `FacetParity` at
one facet datum of each genus-six step.** -/
theorem c34_genusSix_of_exists_facetParity
    (hcone : SimpleWallSupply.InConeSupplySimple (2 + 2) (4 * 2 + 2) (6 * 2 + 3))
    (hfacet : ∀ c c' : CubicCore (4 * 2 + 2) (6 * 2 + 3), Step c c' →
      ∃ (e₀ : Fin (6 * 2 + 3)) (y₀ : Fin (6 * 2 + 3) → ℚ) (ε : ℚ),
        FacetDatum c.core c'.core (2 + 2) e₀ y₀ ε ∧ FacetParity c.core c'.core (2 + 2) y₀)
    (request : Fin (6 * 2 + 3) → ℚ) (hreqpos : ∀ i, 0 < request i)
    (hbase : StepSupplyReduction.GeneralRequest (FibreCaterpillar.catCore 2) (2 + 2) request)
    (classification : CaterpillarBallot.BallotClassification 2 request) :
    CountSchedule.C34 2 :=
  SimpleWallSupply.c34_genusSix_simple hcone (typeChangeSupplyPositive_of_exists_facetParity hfacet)
    request hreqpos hbase classification

/-! ## 2.  The per-limit shapes -/

section Shapes

variable {c c' : Core n p} {y₀ : Fin p → ℚ}

/-- **The general per-limit shape**: the odd classes specialising to `l` on the
two sides are labelled injectively by one index type, with the same labels
used.  At valency four the index is the `K` of the `K`-family; at
valency two and three it is `Unit` (`facetParity_of_unique`). -/
theorem facetParity_of_injective_index {ι : Type*}
    (τL : ∀ l : FacetLimit c c' y₀ degree,
      {x : FrameClass c degree // x.IsOdd ∧ SpecializesLeft x l} → ι)
    (τR : ∀ l : FacetLimit c c' y₀ degree,
      {x : FrameClass c' degree // x.IsOdd ∧ SpecializesRight x l} → ι)
    (hL : ∀ l, Function.Injective (τL l)) (hR : ∀ l, Function.Injective (τR l))
    (hrange : ∀ l, Set.range (τL l) = Set.range (τR l)) :
    FacetParity c c' degree y₀ :=
  facetParity_of_card_eq fun l ↦ by
    rw [← Nat.card_range_of_injective (hL l), ← Nat.card_range_of_injective (hR l), hrange l]

/-- **A bijection of the whole specialising fibres that preserves oddness** --
the form a matching of star members with far-side candidates delivers. -/
theorem facetParity_of_equiv_isOdd
    (e : ∀ l : FacetLimit c c' y₀ degree,
      {x : FrameClass c degree // SpecializesLeft x l} ≃
        {x : FrameClass c' degree // SpecializesRight x l})
    (hodd : ∀ l x, (e l x).1.IsOdd ↔ x.1.IsOdd) :
    FacetParity c c' degree y₀ :=
  facetParity_of_card_eq fun l ↦ by
    let eL : {x : FrameClass c degree // x.IsOdd ∧ SpecializesLeft x l} ≃
        {x : {x : FrameClass c degree // SpecializesLeft x l} // x.1.IsOdd} :=
      { toFun := fun x ↦ ⟨⟨x.1, x.2.2⟩, x.2.1⟩
        invFun := fun x ↦ ⟨x.1.1, x.2, x.1.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    let eR : {x : FrameClass c' degree // x.IsOdd ∧ SpecializesRight x l} ≃
        {x : {x : FrameClass c' degree // SpecializesRight x l} // x.1.IsOdd} :=
      { toFun := fun x ↦ ⟨⟨x.1, x.2.2⟩, x.2.1⟩
        invFun := fun x ↦ ⟨x.1.1, x.2, x.1.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    exact Nat.card_congr
      (eL.trans ((Equiv.subtypeEquiv (e l) fun x ↦ (hodd l x).symm).trans eR.symm))

/-- **The valency-two/three shape** (Part II, `subsec-case-v3` and `subsec-case-v2`:
exactly one member of each type), in the mod-two form: per facet limit, at most one odd
class on each side, and an odd class on one side exists exactly when one exists on the
other.  The two halves are uniqueness and existence with equal parity (a `TypeChangeLink`
plus
`NonTrivalentNonfacetDenominator.signedMult_eq_of_typeChangeLink`). -/
theorem facetParity_of_unique
    (huniqL : ∀ (l : FacetLimit c c' y₀ degree) (x x' : FrameClass c degree),
      x.IsOdd → SpecializesLeft x l → x'.IsOdd → SpecializesLeft x' l → x = x')
    (huniqR : ∀ (l : FacetLimit c c' y₀ degree) (x x' : FrameClass c' degree),
      x.IsOdd → SpecializesRight x l → x'.IsOdd → SpecializesRight x' l → x = x')
    (hLR : ∀ (l : FacetLimit c c' y₀ degree) (x : FrameClass c degree),
      x.IsOdd → SpecializesLeft x l → ∃ x' : FrameClass c' degree, x'.IsOdd ∧ SpecializesRight x' l)
    (hRL : ∀ (l : FacetLimit c c' y₀ degree) (x' : FrameClass c' degree),
      x'.IsOdd → SpecializesRight x' l → ∃ x : FrameClass c degree, x.IsOdd ∧ SpecializesLeft x l) :
    FacetParity c c' degree y₀ :=
  facetParity_of_injective_index (ι := Unit) (fun _ _ ↦ ()) (fun _ _ ↦ ())
    (fun l a b _ ↦ Subtype.ext (huniqL l a.1 b.1 a.2.1 a.2.2 b.2.1 b.2.2))
    (fun l a b _ ↦ Subtype.ext (huniqR l a.1 b.1 a.2.1 a.2.2 b.2.1 b.2.2))
    fun l ↦ by
      ext u
      constructor
      · rintro ⟨a, -⟩
        obtain ⟨x', hx', hs⟩ := hLR l a.1 a.2.1 a.2.2
        exact ⟨⟨x', hx', hs⟩, Subsingleton.elim _ _⟩
      · rintro ⟨b, -⟩
        obtain ⟨x, hx, hs⟩ := hRL l b.1 b.2.1 b.2.2
        exact ⟨⟨x, hx, hs⟩, Subsingleton.elim _ _⟩

end Shapes

/-! ## 3.  At the genus-six caterpillar step -/

section GenusSix

open DraismaVargas.Count.StepSupplyGenusSix (catCubicCore)

/-- **The weaker consumer at the caterpillar step**: `FacetParity` at the one
facet datum the machine picks gives the per-step obligation of
`TypeChangeSupplyPositive 4 10 15` there. -/
theorem cat_obligation_of_facetParity_at {e₀ : Fin (6 * 2 + 3)} {y₀ : Fin (6 * 2 + 3) → ℚ}
    {ε : ℚ} (hd : FacetDatum catCubicCore.core catLoopCore.core (2 + 2) e₀ y₀ ε)
    (hpar : FacetParity catCubicCore.core catLoopCore.core (2 + 2) y₀) :
    ∃ y y' : Fin (6 * 2 + 3) → ℚ, PositiveGeneral catCubicCore.core (2 + 2) y ∧
      PositiveGeneral catLoopCore.core (2 + 2) y' ∧
        CountTransportLink.CountLink (2 + 2) catCubicCore.core y catLoopCore.core y' :=
  typeChangeSupplyPositive_step_of_exists_facetParity ⟨e₀, y₀, ε, hd, hpar⟩

/-- The datum half of the weaker consumer's antecedent is inhabited at the
caterpillar step. -/
example : ∃ (e₀ : Fin (6 * 2 + 3)) (y₀ : Fin (6 * 2 + 3) → ℚ) (ε : ℚ),
    FacetDatum catCubicCore.core catLoopCore.core (2 + 2) e₀ y₀ ε :=
  exists_facetDatum cat_step (2 + 2)

end GenusSix

end DraismaVargas.Count.FacetParityPilot
