import DraismaVargasCount.CrossCoreTransport
import DraismaVargasCount.StepSupplyGenusSix

/-!
# A count link is a parity; the open odd subfibre

A count link `CountTransportLink.CountLink degree core y core' y'` is *by definition* the
statement `Odd (openOddCount core y degree) ↔ Odd (openOddCount core' y' degree)`: a parity of
two natural numbers, with no bijection, no cardinality and no fibre in it.  This module pins that
down and names the open odd part of the fibre, in terms of which the type-change step of the
count (step 3 of `DraismaVargasCount.Assembly`) is phrased.

* `countLink_iff_parity`, `countLink_iff_modEq` -- a count link is a parity, by `Iff.rfl`, and
  equivalently a congruence mod two.
* `OpenOdd`, `card_openOdd` -- the open classes of odd multiplicity of the request-free fibre
  `CrossCoreTransport.FrameClass` at one request, and the open odd count read as their number.
* `openOddTransportSlotRelabel` -- an `CrossCoreTransport.OpenOddTransport` between two
  genuinely different cores, at every degree and request, with no hypothesis, obtained from
  `CrossCoreTransport.transportSlotRelabel`.  The two cores are related by a relabelling of the
  slots and **not** by a Whitehead move (`CoreOfDarts.Step`), so this shows that the type is
  inhabited, not that a type change preserves the count.
* `openOddTransportOfFibrewise` -- what a local construction must supply.  If the open odd
  classes of both sides carry a common invariant -- in the argument of Part II, the
  codimension-one limit a frame specialises to at the shared wall -- and the two sides match
  over each value of it, they match globally.  This is `CrossCoreTransport.Transport.ofFibrewise`
  restricted to the open odd classes: it asks nothing of the closed classes, the classes of even
  multiplicity, or the multiplicities themselves.  `CrossCoreParity` weakens the matching over
  each value to a parity.

Throughout, `openOddCount` is `Count.GeometricFibre.openOddCount`.  The source is A. Vargas,
*Catalan-many tropical morphisms to trees; Part II: A space and a count*, arXiv:2609.09109.
-/

namespace DraismaVargas.Count.OpenOddRung

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore Step CoreIso)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.CoreRelabel (Relabel)
open DraismaVargas.Count.StepSupplyReduction (GeneralRequest exists_generalRequest
  generalRequest_relabel)
open DraismaVargas.Count.CrossCoreTransport (FrameClass OpenOddTransport openOddCount_eq_card
  openOddCount_eq_of_openOddTransport slotRelabel transportSlotRelabel fibreEquiv
  open_fibreEquiv isOdd_fibreEquiv)

variable {n p degree : ℕ}

/-! ## 1.  A count link is a parity -/

/-- **A `CountLink` is a parity of two natural numbers and nothing else.**
`Iff.rfl`: this *is* the definition of `CountTransportLink.CountLink`.  No
fibre, no equivalence, no cardinality. -/
theorem countLink_iff_parity {n' p' : ℕ} (degree : ℕ) (core : Core n p) (y : Fin p → ℚ)
    (core' : Core n' p') (y' : Fin p' → ℚ) :
    CountTransportLink.CountLink degree core y core' y' ↔
      (Odd (GeometricFibre.openOddCount core y degree) ↔
        Odd (GeometricFibre.openOddCount core' y' degree)) :=
  Iff.rfl

/-- The same, as a congruence mod two. -/
theorem countLink_iff_modEq {n' p' : ℕ} (degree : ℕ) (core : Core n p) (y : Fin p → ℚ)
    (core' : Core n' p') (y' : Fin p' → ℚ) :
    CountTransportLink.CountLink degree core y core' y' ↔
      GeometricFibre.openOddCount core y degree ≡
        GeometricFibre.openOddCount core' y' degree [MOD 2] := by
  simp only [CountTransportLink.CountLink, Nat.odd_iff, Nat.ModEq]
  omega

/-! ## 2.  The open odd subfibre: an inhabitant, and what a local construction owes -/

/-- The open odd part of the request-free fibre, at one request.  This is the
domain and codomain of `CrossCoreTransport.OpenOddTransport`, named. -/
def OpenOdd (c : Core n p) (degree : ℕ) (y : Fin p → ℚ) : Type 1 :=
  {x : FrameClass c degree // x.OpenAt y ∧ x.IsOdd}

instance instFiniteOpenOdd (c : Core n p) (degree : ℕ) (y : Fin p → ℚ) :
    Finite (OpenOdd c degree y) := by
  unfold OpenOdd
  infer_instance

/-- The open odd count, read on the open odd subfibre. -/
theorem card_openOdd (c : Core n p) (y : Fin p → ℚ) (degree : ℕ) :
    Nat.card (OpenOdd c degree y) = GeometricFibre.openOddCount c y degree :=
  (openOddCount_eq_card c y degree).symm

variable {c c' : Core n p} {y y' : Fin p → ℚ}

/-- **A concrete `OpenOddTransport` at two genuinely different cores**, at every
degree and every request, with no hypothesis.  It is
`CrossCoreTransport.transportSlotRelabel` restricted to the open odd classes.

The two cores here are related by a slot relabelling, **not** by
`CoreOfDarts.Step`, so this shows that the type is inhabited, not that a
Whitehead move preserves the count.  That the two cores can genuinely differ is
`CrossCoreTransport.slotRelabel_ne_self`.  The force of this declaration is
that `OpenOddTransport` at two distinct cores is not an empty type. -/
noncomputable def openOddTransportSlotRelabel (core : Core n p) (σ : Equiv.Perm (Fin p))
    (degree : ℕ) (y : Fin p → ℚ) :
    OpenOddTransport core (slotRelabel core σ) degree y (fun e ↦ y (σ.symm e)) :=
  (transportSlotRelabel core σ degree y).toOpenOdd

/-- **What a local construction must supply, on the open odd classes.**  If the open odd
classes of both sides carry a common invariant -- in the argument of Part II,
the codimension-one limit a frame specialises to at the shared wall -- and the
two sides match over each value of it, they match globally.

This is `CrossCoreTransport.Transport.ofFibrewise` with everything it does not
need removed: no closed class, no even-multiplicity class and no multiplicity
appears, so a construction that can only control the open odd classes over one
limit at a time still produces an `OpenOddTransport`. -/
def openOddTransportOfFibrewise {L : Type*} (μ : OpenOdd c degree y → L)
    (μ' : OpenOdd c' degree y' → L)
    (e : ∀ l : L, {x : OpenOdd c degree y // μ x = l} ≃
      {x : OpenOdd c' degree y' // μ' x = l}) :
    OpenOddTransport c c' degree y y' :=
  ((Equiv.sigmaFiberEquiv μ).symm.trans (Equiv.sigmaCongrRight e)).trans
    (Equiv.sigmaFiberEquiv μ')

end DraismaVargas.Count.OpenOddRung
