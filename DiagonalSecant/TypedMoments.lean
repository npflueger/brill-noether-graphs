module

public import DiagonalSecant.TypedImage
public import DiagonalSecant.Defs
public import DiagonalSecant.CMDictionary
public import DiagonalSecant.Restrict
public import DraismaVargasMarkedCount.MarkedCountGeneral.Correspondence
public import DraismaVargasCount.RowHairpinPosition
public import DraismaVargasCount.OddDenominator

@[expose] public section

/-!
# The slot moments of the typed pushed fibre

Three layers, from the inside out:

1. **The hairpin receipt on marked rows** (`HairpinReceipt`): every interior chip term along a
   marked row, coefficient times rational position, has odd denominator. This is the conclusion
   of `RowHairpinPosition.weighted_prefix_mem`, read on a typed presentation, and it is carried
   through the chain below **as a hypothesis**. A generic typed twin of the public lemma
   (stated for every `MarkedFullDim … excess`, with the leaf-adjusted denominators odd and an
   `AdmissibleRoot`) is not available from the typed fields, because the public proof rests on
   dangling-no-glue and the leaf dichotomy, which the public side derives from
   change-minimality, and a typed frame is not change-minimal at the images of its marks (the
   type excess sits there). For the typed frames the theorem uses, those that regrow (lower
   index `0`, marked-cubic core, tailed core at the headline degree), the receipt is proved by
   transporting the public lemma from the regrown frame (`CM.weighted_prefix_mem_of_regrow`,
   `CMHairpin.lean`), and its model instance
   `CM.weighted_prefix_mem_of_model` supplies the hypothesis in
   `TypedRealisation.exists_placedFibre`. Likewise "the mark's image is an admissible root" is
   proved in the regrown form `CM.admissibleRoot_mark_of_tailed` (`CMRoot.lean`); the chain does
   not need the root condition, the receipt subsuming it.
2. **The interior receipt of the big divisor** (`collisionCoefficient_mem`,
   `divisor_interior_mem`): `DegeneratePlacement.divisor_interior_mem` through
   `TypedPlacement.divisor_interior`.
3. **The moments** (`dvd_slotMoment_pushed`): the public, datum-free
   `ExpansionSeriesMoment.dvd_slotMoment_of_bigDivisor`, fed by layer 2.

The odd denominators of the typed member's leaf-adjusted coordinates at the actual request
(`odd_leafAdjustedCoords_den_of_model`, proved here although the chain does not use it) come
from the same route: it comes from the **regrown** frame of `H` through
`OddDenominator.odd_leafAdjustedCoords_den` (which uses no positivity), read on the core columns
by `coordsAt_restrictTailed`, with `|Mult f| = |Mult κ|` odd (`typedAbsMult_restrictTailed`,
`mult_tailedClassEquiv`). The fold leaf `x_u` of κ's target is not a leaf of `f`'s target, so its
coordinate has odd denominator without halving, and doubling keeps it odd.
-/

namespace DiagonalSecant.TypedMoments

open DraismaVargas.Infrastructure DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count DraismaVargas.Count.MarkedCount DraismaVargas.Count.MarkedCountGeneral
open DraismaVargas.Count.PendantRetraction DraismaVargas.Count.SlotMoment
open DraismaVargas.Count.DegenerateBigDivisor (degenerateLength)
open DiagonalSecant.TypedRows DiagonalSecant.TypedPlacement DiagonalSecant.TypedImage
open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.ExplicitPotential (Core)
open Utilities.Subdivision.CoreExpansion

/-! ## 1.  Hairpin positions on marked rows -/

section Hairpin

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {marks : Finset data.SourceVertex} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate] {excess : ℤ} (fd : MarkedFullDim data marks coordinate excess)

/-- **An admissible root**: an internal target vertex, or a leaf of the target over which every
surviving source vertex is a mark. The public hairpin lemma takes an internal root; the fibre
over the image of a mark is what the diagonal secant theorem pushes, and that image may be a leaf
(a *fold* at the mark). -/
def AdmissibleRoot (data : GluingDatum target degree) (marks : Finset data.SourceVertex)
    (root : target.V) : Prop :=
  ¬ IsLeafVertex target root ∨
    ∀ v : data.SourceVertex, v.1.1 = root → 0 < nonDanglingValency data v → v ∈ marks

/-- **The hairpin receipt** at a root: every interior chip term along every marked row,
coefficient times rational position, has odd denominator (the conclusion of
`RowHairpinPosition.weighted_prefix_mem`, on a typed presentation). -/
def HairpinReceipt (z : coordinate → ℚ) (root : target.V) : Prop :=
  ∀ (path : MarkedStablePath data marks) (i : ℕ), i + 1 < (orderedRow fd.pathEnds path).length →
    (retractedFibre root (retractVertex (rowVertex fd.pathEnds path (i + 1))) : ℚ) *
      prefixPosition fd z path (i + 1) ∈ oddDenominatorSubring

end Hairpin

/-! ## 2.  The interior receipt of the big divisor -/

section Receipt

variable {N Q m degree : ℕ} {mark : Fin m → Fin N} {types : Fin m → ℕ}
  (B : Spec N Q) (y : Fin Q → ℕ) (κ : TypedFrame B.core mark types degree)
  (hClosed : Closed y κ) (hFit : ∀ e : Fin Q, scale y κ * y e ≤ B.length e)

/-- The collision coefficient at an integral offset, times the offset over the scale, has odd
denominator (`RowRealizedPosition.member_collisionCoefficient_mem`). -/
theorem collisionCoefficient_mem {root : κ.target.V}
    (hReceipt : HairpinReceipt κ.fullDim (coords y κ) root) (e : Fin Q) (offset : ℕ) :
    (collisionCoefficient κ.fullDim (realization y κ hClosed) root (rowOf κ e) offset : ℚ) *
      ((offset : ℚ) / scale y κ) ∈ oddDenominatorSubring := by
  classical
  simp only [collisionCoefficient, Int.cast_sum, Finset.sum_mul]
  apply oddDenominatorSubring.sum_mem
  intro i _
  by_cases hOffset : integralPrefix κ.fullDim (realization y κ hClosed) (rowOf κ e) (i.val + 1) =
      offset
  · simp only [ite_eq_left hOffset]
    have hScale : (scale y κ : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (scale_pos y κ))
    have hPosition := TypedPlacement.integralPrefix_cast y κ hClosed e (i.val + 1)
    rw [hOffset] at hPosition
    have hDivide : (offset : ℚ) / scale y κ =
        prefixPosition κ.fullDim (coords y κ) (rowOf κ e) (i.val + 1) := by
      rw [hPosition, mul_div_cancel_left₀ _ hScale]
    rw [hDivide]
    exact hReceipt (rowOf κ e) i.val (by have hi := i.isLt; omega)
  · simp only [ite_eq_right hOffset, Int.cast_zero, zero_mul]
    exact oddDenominatorSubring.zero_mem

/-- **The interior coefficients of the big divisor carry the odd-denominator receipt** at their
own positions (`DegeneratePlacement.divisor_interior_mem`). Exactness is asked only where a slot
has an interior vertex. -/
theorem divisor_interior_mem
    (hExact : ∀ e : Fin Q, 1 < B.length e → scale y κ * y e = B.length e)
    {root : κ.target.V} (hReceipt : HairpinReceipt κ.fullDim (coords y κ) root)
    (e : Fin Q) (o : Fin (B.length e - 1)) :
    ((divisor B y κ hClosed hFit root (B.interiorVertex e o) : ℤ) : ℚ) *
        (((o.val + 1 : ℕ) : ℚ) / (scale y κ : ℚ)) ∈ oddDenominatorSubring := by
  classical
  rw [divisor_interior]
  by_cases hRev : reverse κ e = true
  · have hInner := o.isLt
    have hLength : scale y κ * y e = B.length e := hExact e (by omega)
    have hOff : B.length e - (o.val + 1) = scale y κ * y e - (o.val + 1) := by rw [hLength]
    simp only [hRev, ite_true, hOff]
    have hBound : o.val + 1 ≤ scale y κ * y e := by omega
    have hScaleQ : (scale y κ : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (scale_pos y κ))
    set c := collisionCoefficient κ.fullDim (realization y κ hClosed) root (rowOf κ e)
      (scale y κ * y e - (o.val + 1)) with hc
    have hTerm := collisionCoefficient_mem B y κ hClosed hReceipt e
      (scale y κ * y e - (o.val + 1))
    have hTotal : ((c : ℤ) : ℚ) * ((y e : ℕ) : ℚ) ∈ oddDenominatorSubring :=
      oddDenominatorSubring.mul_mem (intCast_mem _ c) (natCast_mem _ (y e))
    have hDifference := oddDenominatorSubring.sub_mem hTotal hTerm
    simp only [Nat.cast_sub hBound, Nat.cast_mul] at hDifference
    convert hDifference using 1
    field_simp
    ring
  · simp only [hRev, Bool.false_eq_true, ite_false]
    exact collisionCoefficient_mem B y κ hClosed hReceipt e (o.val + 1)

end Receipt

/-! ## 3.  The moments of the pushed fibre -/

section Moments

variable {n p N Q m degree : ℕ} {mark : Fin m → Fin N} {types : Fin m → ℕ}
  (D : ExpansionData n p N Q) (small : Spec n p) (hN : 0 < N)
  (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e) (k : ℕ) (hk : 0 < k)
  (κ : TypedFrame D.bigCore mark types degree)
  (hClosed : Closed (degenerateLength D small) κ)
  (hScale : scale (degenerateLength D small) κ = k)

/-- **Every slot moment of the pushed fibre is divisible by every power of two dividing the
scale** (`ExpansionSeriesMoment.dvd_slotMoment_of_bigDivisor`, fed by `divisor_interior_mem`). -/
theorem dvd_slotMoment_pushed (hCond : D.Conditions small.core) {root : κ.target.V}
    (hReceipt : HairpinReceipt κ.fullDim (coords (degenerateLength D small) κ) root)
    (a : ℕ) (hka : 2 ^ a ∣ k) (j : Fin p) :
    ((2 ^ a : ℕ) : ℤ) ∣ InteriorFiring.slotMoment (small.scale k hk)
      (pushed D small hN hL k hk κ hClosed hScale root) j := by
  refine ExpansionSeriesMoment.dvd_slotMoment_of_bigDivisor small hCond k a hk hka
    (bigDivisor D small hN hL k hk κ hClosed hScale root) (fun e o ↦ ?_) j
  have h := divisor_interior_mem (D.bigSpec (small.scale k hk) hN hL) (degenerateLength D small)
    κ hClosed (fit D small hN hL k hk κ hScale)
    (fun e' h' ↦ exact D small hN hL k hk κ hScale e' h') hReceipt e o
  have hcast : (k : ℚ) = (scale (degenerateLength D small) κ : ℚ) := by rw [hScale]
  rw [hcast]
  exact h

end Moments

/-! ## 4.  The inputs for the diagonal secant theorem -/

section Model

open DiagonalSecant
open GenusSixExistence.Tripod.Gadget (subdivide)

variable {g : ℕ} {G : CFGraph.{0}} {u : (UnitSubdivisionPresentation.spec G).graph.V}

/-- **The odd denominators of the typed member's leaf-adjusted coordinates** at the actual
request. -/
theorem odd_leafAdjustedCoords_den_of_model (M : OnceMarkedModel g G u) (hg5 : 5 ≤ g)
    (κ : TypedFrame M.markedCore (onceMark M.N) ![g - 4] (g - 1))
    (hOdd : ∃ m : ℕ, Odd m ∧ κ.typedAbsMult = m) (column : Fin (M.Q + 1)) :
    Odd (OddDenominator.leafAdjustedCoords κ.fullDim.labelling.presentation
      (κ.coordsAt M.request) column).den := by
  -- Through the regrowth, as in the module docstring: the regrown frame
  -- `f := regrowTailed T hc hd 0 κ' s` of the tailed core `T = tailed M.core M.slot (g − 4)` is
  -- a public frame of `T.H`, with `|Mult f| = |Mult(κ; marks)|` odd and `κ`'s coordinates on
  -- its core columns; `CM.odd_leafAdjustedCoords_den_of_regrow` reads
  -- `OddDenominator.odd_leafAdjustedCoords_den` on `f` back on `κ`, after casting `κ` to the
  -- lower type `lowerType (tailType (g − 4)) 0 = ![g − 4]` in degree `(g − 1) − shed 0 = g − 1`.
  have ha : 1 ≤ g - 4 := by omega
  have hd : IsTailDegree (M.N + 1) (M.Q + 1) (tailType (g - 4)) (g - 1) :=
    tailed_isTailDegree M.genus_eq ha (by omega)
  have hShed : (g - 1) - shed (c := tailType (g - 4)) (fun _ ↦ 0) = g - 1 := by
    rw [show shed (c := tailType (g - 4)) (fun _ ↦ 0) = 0 from Finset.sum_eq_zero fun _ _ ↦ rfl,
      Nat.sub_zero]
  have h := CM.odd_leafAdjustedCoords_den_of_regrow (tailed M.core M.slot (g - 4))
    (tailed_markedCubic M.cubic M.slot) hd (fun _ ↦ 0)
    (TypedFrame.cast (lowerType_tailType_zero ha).symm hShed.symm κ)
    (fun _ ↦ CM.zeroSlope _ rfl) M.request
    (fun e ↦ (degenerateLength M.expansion M.small e : ℤ))
    (fun e ↦ by simp [OnceMarkedModel.request]) (by rw [TypedFrame.typedAbsMult_cast]; exact hOdd)
    column
  rw [TypedFrame.coordsAt_cast] at h
  exact (CM.odd_leafAdjusted_cast_iff _ _ κ _ _).mp h

end Model

end DiagonalSecant.TypedMoments
