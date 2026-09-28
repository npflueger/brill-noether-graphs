import DraismaVargasCount.OpenOddRung
import DraismaVargasCount.SwitchingParity

/-!
# A parity form of the count link across a type change

A count link (`CountTransportLink.CountLink degree c y c' y'`) asks only that the open odd counts
on the two sides have the same parity (`OpenOddRung.countLink_iff_parity`), and
`OpenOddRung.card_openOdd` reads each count as `Nat.card` of a finite type.  So a link is exactly
the evenness of `Nat.card (OpenOdd c degree y ⊕ OpenOdd c' degree y')`, and it can be produced by
a fixed-point-free involution on that disjoint union, which may pair classes of the *same* side
with each other.  The other cross-core producers of a `CountLink` --
`CrossCoreTransport.countLink_of_openOddTransport`,
`CountTransportLink.countLink_of_oddOpenEquiv`,
`CountTransportLink.countLink_of_openOddCount_eq` -- factor through an **equality** of the two
open odd counts, or through a bijection delivering one.  The parity machinery of
`Count.SwitchingParity` works over **one** core, because it needs the identification of the
fibres between consecutive wall parameters there.

This is a reformulation, not a weakening: `countLink_iff_evenSum` and
`countLink_iff_exists_freeInvolution` are equivalences, so "exhibit a fixed-point-free involution
on the disjoint union" is neither more nor less than the parity it replaces.  Only a *canonical*
involution, built from the geometry of the Whitehead move, buys anything.  No fibre equivalence,
no multiplicity and no genericity of the request enters §§1--3.

## Main results

* `countLink_iff_evenSum`, `countLink_of_evenSum` -- a `CountLink` across a type change is
  exactly evenness of `Nat.card (OpenOdd c degree y ⊕ OpenOdd c' degree y')`.
* `sumSwap`, `sumSwap_involutive`, `sumSwap_ne`, `even_card_sum_of_equiv`,
  `even_card_sum_of_openOddTransport`, `countLink_of_openOddTransport_via_parity` -- an
  equivalence of the two sides is the special case of the involution in which every pair
  straddles the two cores, so `CrossCoreTransport.countLink_of_openOddTransport` is reproved
  from §1.
* `countLink_of_freeInvolution`, `countLink_iff_exists_freeInvolution` -- the involution form of
  the producer, and the equivalence that prices it.
* `even_card_of_fibrewise_even` -- **the localisation lemma**, over an arbitrary finite type and
  an arbitrary index type `L` with **no** finiteness assumption on `L`: if every fibre of an
  invariant is even, the total is even.  The proof assembles the fibres' involutions rather than
  summing cardinalities, which is what removes the hypothesis on `L`.
* `sumFibreEquiv`, `even_card_sum_of_fibrewiseEven`, `even_card_sum_of_fibrewiseParity`,
  `countLink_of_fibrewiseEven`, `countLink_of_fibrewiseParity` -- **the local form.**  The
  wall-crossing statement of Part II is local: it is about the full-dimensional morphisms
  specialising to **one** codimension-one limit, partitioned among the resolutions of the merged
  vertex.  `even_card_sum_of_fibrewiseParity` accepts exactly that: two invariants `μ`, `μ'` on
  the two sides' open odd classes with values in a common `L`, and, over each value, a *parity*
  of the two fibre cardinalities.  Nothing asks the two fibres to be equinumerous, which is what
  `CrossCoreTransport.Transport.ofFibrewise` and `OpenOddRung.openOddTransportOfFibrewise` both
  do ask, and nothing constrains `L`.
* `even_card_sum_slotRelabel` -- non-vacuity of the criterion: the disjoint union has even
  cardinality at two genuinely different cores, at every degree and every request, with no
  hypothesis.  Its two cores are related by a slot relabelling, not by a Whitehead move
  (`CoreOfDarts.Step`).

None of these theorems constructs an invariant or an involution at an actual Whitehead move;
each takes it as a hypothesis.  The type-change step of the count (step 3 of
`DraismaVargasCount.Assembly`) uses `countLink_of_fibrewiseParity`: `FacetMachine` supplies the
invariant (the facet limit a class specialises to) and the per-value parities.

The results of §§2--3 other than those about `OpenOdd` (`sumSwap`, `sumFibreEquiv`,
`even_card_of_fibrewise_even`, ...) are generic finite combinatorics.

The source is A. Vargas, *Catalan-many tropical morphisms to trees; Part II: A space and a
count*, arXiv:2609.09109, section "Constructions: changing combinatorial type"
(`sec-constructions`).
-/

namespace DraismaVargas.Count.CrossCoreParity

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore Step)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.StepSupplyReduction (GeneralRequest)
open DraismaVargas.Count.CrossCoreTransport (OpenOddTransport slotRelabel)
open DraismaVargas.Count.OpenOddRung (OpenOdd card_openOdd countLink_iff_parity
  openOddTransportSlotRelabel)
open DraismaVargas.Count.SwitchingParity (even_card_of_freeInvolution
  exists_freeInvolution_of_even_card)

variable {n p degree : ℕ} {c c' : Core n p} {y y' : Fin p → ℚ}

/-! ## 1.  The parity criterion -/

/-- **A `CountLink` is the evenness of one cardinality.**  The two sides' open
odd classes are two finite types (`OpenOddRung.instFiniteOpenOdd`), and the link
asks precisely that their disjoint union be even.  No equality of counts, no
bijection and no multiplicity occurs in the statement, which is what
distinguishes this criterion from every other cross-core producer in the
library. -/
theorem countLink_iff_evenSum (c c' : Core n p) (degree : ℕ) (y y' : Fin p → ℚ) :
    CountTransportLink.CountLink degree c y c' y' ↔
      Even (Nat.card (OpenOdd c degree y ⊕ OpenOdd c' degree y')) := by
  rw [Nat.card_sum, card_openOdd, card_openOdd, Nat.even_iff, countLink_iff_parity,
    Nat.odd_iff, Nat.odd_iff]
  omega

/-- **The producer.**  Evenness of the disjoint union of the two sides' open odd
classes is a link. -/
theorem countLink_of_evenSum
    (h : Even (Nat.card (OpenOdd c degree y ⊕ OpenOdd c' degree y'))) :
    CountTransportLink.CountLink degree c y c' y' :=
  (countLink_iff_evenSum c c' degree y y').mpr h

/-! ## 2.  The involution form, and why the existing rung sits above it -/

/-- **The swap involution of an equivalence.**  On `A ⊕ B` it sends each `a` to
its partner in `B` and back.  Every pair it forms straddles the two summands;
the point of §2 is that an involution is *not* obliged to do that. -/
def sumSwap {A B : Type*} (e : A ≃ B) : A ⊕ B → A ⊕ B :=
  Sum.elim (fun a ↦ Sum.inr (e a)) (fun b ↦ Sum.inl (e.symm b))

theorem sumSwap_involutive {A B : Type*} (e : A ≃ B) : Function.Involutive (sumSwap e) := by
  rintro (a | b) <;> simp [sumSwap]

theorem sumSwap_ne {A B : Type*} (e : A ≃ B) : ∀ x : A ⊕ B, sumSwap e x ≠ x := by
  rintro (a | b) <;> simp [sumSwap]

/-- An equivalence of two finite types makes their disjoint union even. -/
theorem even_card_sum_of_equiv {A B : Type*} [Finite A] [Finite B] (e : A ≃ B) :
    Even (Nat.card (A ⊕ B)) :=
  even_card_of_freeInvolution (sumSwap e) (sumSwap_involutive e) (sumSwap_ne e)

/-- **The involution producer.**  A fixed-point-free involution on the disjoint
union of the two sides' open odd classes is a link.  Unlike an
`CrossCoreTransport.OpenOddTransport`, it may pair two classes of the *same*
core with each other, and it never has to say how many classes there are on
either side. -/
theorem countLink_of_freeInvolution
    (g : OpenOdd c degree y ⊕ OpenOdd c' degree y' →
      OpenOdd c degree y ⊕ OpenOdd c' degree y')
    (hinv : Function.Involutive g) (hfree : ∀ x, g x ≠ x) :
    CountTransportLink.CountLink degree c y c' y' :=
  countLink_of_evenSum (even_card_of_freeInvolution g hinv hfree)

/-- **What the involution form is worth, exactly.**  It is an equivalence, so on
its own it re-prices nothing -- as `Count.SwitchingParity` records for the
in-cone side.  Only an involution produced *by the geometry of the Whitehead
move* adds anything. -/
theorem countLink_iff_exists_freeInvolution (c c' : Core n p) (degree : ℕ)
    (y y' : Fin p → ℚ) :
    CountTransportLink.CountLink degree c y c' y' ↔
      ∃ g : OpenOdd c degree y ⊕ OpenOdd c' degree y' →
            OpenOdd c degree y ⊕ OpenOdd c' degree y',
        Function.Involutive g ∧ ∀ x, g x ≠ x :=
  (countLink_iff_evenSum c c' degree y y').trans
    ⟨exists_freeInvolution_of_even_card,
      fun ⟨g, hinv, hfree⟩ ↦ even_card_of_freeInvolution g hinv hfree⟩

/-- **The existing rung, recovered through the new one.**  An
`CrossCoreTransport.OpenOddTransport` is the special case of
`countLink_of_freeInvolution` in which every pair straddles the two cores; this
reproves `CrossCoreTransport.countLink_of_openOddTransport` from §1, and shows
that the parity interface sits below the equivalence interface. -/
theorem even_card_sum_of_openOddTransport (e : OpenOddTransport c c' degree y y') :
    Even (Nat.card (OpenOdd c degree y ⊕ OpenOdd c' degree y')) :=
  even_card_sum_of_equiv (A := OpenOdd c degree y) (B := OpenOdd c' degree y') e

theorem countLink_of_openOddTransport_via_parity (e : OpenOddTransport c c' degree y y') :
    CountTransportLink.CountLink degree c y c' y' :=
  countLink_of_evenSum (even_card_sum_of_openOddTransport e)

/-! ## 3.  The local form: one wall-limit at a time -/

/-- **The localisation lemma.**  If a finite type carries an invariant whose
every fibre is even, the type is even.  The index type `L` carries **no**
finiteness assumption, and no cardinality is summed: the proof chooses a
fixed-point-free involution on each fibre and assembles them over the fibration.
Summing the fibres with `Nat.card_sigma` instead would force `L` to be finite;
this does not. -/
theorem even_card_of_fibrewise_even {T L : Type*} [Finite T] (κ : T → L)
    (h : ∀ l : L, Even (Nat.card {x : T // κ x = l})) : Even (Nat.card T) := by
  classical
  choose g hinv hfree using fun l : L ↦ exists_freeInvolution_of_even_card (h l)
  have hfin : Finite (Σ l : L, {x : T // κ x = l}) :=
    Finite.of_equiv T (Equiv.sigmaFiberEquiv κ).symm
  have heven : Even (Nat.card (Σ l : L, {x : T // κ x = l})) := by
    refine even_card_of_freeInvolution (fun z ↦ ⟨z.1, g z.1 z.2⟩) (fun z ↦ ?_) fun z hz ↦ ?_
    · simp only [hinv z.1 z.2]
    · exact hfree z.1 z.2 (eq_of_heq (Sigma.mk.inj_iff.mp hz).2)
  rwa [Nat.card_congr (Equiv.sigmaFiberEquiv κ)] at heven

/-- The fibre of `Sum.elim μ μ'` over a value is the disjoint union of the two
sides' fibres. -/
def sumFibreEquiv {A B L : Type*} (μ : A → L) (μ' : B → L) (l : L) :
    {x : A ⊕ B // Sum.elim μ μ' x = l} ≃ {a : A // μ a = l} ⊕ {b : B // μ' b = l} where
  toFun x :=
    match x with
    | ⟨Sum.inl a, h⟩ => Sum.inl ⟨a, h⟩
    | ⟨Sum.inr b, h⟩ => Sum.inr ⟨b, h⟩
  invFun := Sum.elim (fun a ↦ ⟨Sum.inl a.1, a.2⟩) fun b ↦ ⟨Sum.inr b.1, b.2⟩
  left_inv := by rintro ⟨a | b, h⟩ <;> rfl
  right_inv := by rintro (⟨a, h⟩ | ⟨b, h⟩) <;> rfl

/-- **The local producer, one invariant on the union.**  Stated in the `Even`
form; the `countLink_*` corollaries are the same statement read through §1. -/
theorem even_card_sum_of_fibrewiseEven {L : Type*}
    (κ : OpenOdd c degree y ⊕ OpenOdd c' degree y' → L)
    (h : ∀ l : L,
      Even (Nat.card {x : OpenOdd c degree y ⊕ OpenOdd c' degree y' // κ x = l})) :
    Even (Nat.card (OpenOdd c degree y ⊕ OpenOdd c' degree y')) :=
  even_card_of_fibrewise_even κ h

/-- **The local producer in the shape of the argument of Part II.**  Two
invariants with a common value type -- in that argument, the codimension-one limit
a full-dimensional morphism specialises to at the shared wall -- and, over each
value, a *parity* of the two fibre cardinalities.  Contrast
`OpenOddRung.openOddTransportOfFibrewise`, which asks for a bijection of the two
fibres over each value; that is strictly more, and it is more than the source
statement supplies: Part II's section `sec-constructions` partitions the
morphisms over one limit among the resolutions of the merged vertex, it does not
match two whole fibres.

`L` is unconstrained -- no finiteness, no universe -- so a producer indexing by
`Fin 3`, by a `Type 1` quotient of frames, or by anything else feeds this
directly. -/
theorem even_card_sum_of_fibrewiseParity {L : Type*} (μ : OpenOdd c degree y → L)
    (μ' : OpenOdd c' degree y' → L)
    (h : ∀ l : L, Even (Nat.card {a : OpenOdd c degree y // μ a = l} +
      Nat.card {b : OpenOdd c' degree y' // μ' b = l})) :
    Even (Nat.card (OpenOdd c degree y ⊕ OpenOdd c' degree y')) := by
  refine even_card_sum_of_fibrewiseEven (Sum.elim μ μ') fun l ↦ ?_
  rw [Nat.card_congr (sumFibreEquiv μ μ' l), Nat.card_sum]
  exact h l

/-- The link from one invariant on the union. -/
theorem countLink_of_fibrewiseEven {L : Type*}
    (κ : OpenOdd c degree y ⊕ OpenOdd c' degree y' → L)
    (h : ∀ l : L,
      Even (Nat.card {x : OpenOdd c degree y ⊕ OpenOdd c' degree y' // κ x = l})) :
    CountTransportLink.CountLink degree c y c' y' :=
  countLink_of_evenSum (even_card_sum_of_fibrewiseEven κ h)

/-- The link from a pair of invariants and their per-value parities. -/
theorem countLink_of_fibrewiseParity {L : Type*} (μ : OpenOdd c degree y → L)
    (μ' : OpenOdd c' degree y' → L)
    (h : ∀ l : L, Even (Nat.card {a : OpenOdd c degree y // μ a = l} +
      Nat.card {b : OpenOdd c' degree y' // μ' b = l})) :
    CountTransportLink.CountLink degree c y c' y' :=
  countLink_of_evenSum (even_card_sum_of_fibrewiseParity μ μ' h)

/-! ## 4.  Non-vacuity at two different cores -/

/-- **Non-vacuity of the object**, at two genuinely different cores, at every
degree and every request, with no hypothesis.  The two cores are related by a
slot relabelling and **not** by `CoreOfDarts.Step`
(`CrossCoreTransport.slotRelabel_ne_self` says they can differ), so this
exercises the criterion, not a type change. -/
theorem even_card_sum_slotRelabel (core : Core n p) (σ : Equiv.Perm (Fin p)) (degree : ℕ)
    (y : Fin p → ℚ) :
    Even (Nat.card (OpenOdd core degree y ⊕
      OpenOdd (slotRelabel core σ) degree fun e ↦ y (σ.symm e))) :=
  even_card_sum_of_equiv (A := OpenOdd core degree y)
    (B := OpenOdd (slotRelabel core σ) degree fun e ↦ y (σ.symm e))
    (openOddTransportSlotRelabel core σ degree y)

end DraismaVargas.Count.CrossCoreParity
