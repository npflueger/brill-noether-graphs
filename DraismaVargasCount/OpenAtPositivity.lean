import DraismaVargasCount.OpenOddRung
import DraismaVargasCount.PositiveOrthantWall
import DraismaVargasCount.BallotCoreIdentification
import DraismaVargasCount.SimpleWallSupply

/-!
# Openness forces a positive request

**Source.**  Vargas, Part II (arXiv:2609.09109): the metric graphs of the count have
positive edge lengths.

## The one lemma

`SegmentWalls.Frame.OpenAt k y` says every *coordinate* of the frame `k` is
strictly positive at the request `y`.  `pos_of_openAt` says that this forces
every *slot* of the request itself to be strictly positive.  The proof is three
lines of linear algebra:
`y (k.slot r) = ∑ c, k.matrix r c * k.coordsAt y c` (`Frame.mulVec_coordsAt`),
every entry of the length matrix is non-negative (`StarPilot.matrix_nonneg`),
and no row of a nonsingular matrix is zero
(`PositiveOrthantWall.exists_matrix_ne_zero`).  So the sum is a non-negative
combination with at least one strictly positive term.

The consequence is structural, not incidental: **the open odd count vanishes
identically off the strictly positive orthant** (`openOddCount_eq_zero_of_nonpos`).
The count the propagation transports is supported on positive requests only.

## Why positivity must be in the hypotheses

`StepSupplyReduction.GeneralRequest` carries **no positivity** -- it says only
that no frame loses a coordinate.  Negating a general request therefore leaves it
general (`generalRequest_neg`, from `PositiveOrthantWall.coordsAt_smul` at
`-1`), while sending its count to zero (`openOddCount_neg_eq_zero`).  Any statement
that moves a *parity* or a *count* freely between two general requests over one core
therefore fails as soon as the count is odd -- or nonzero -- anywhere; at genus six the
count at a positive general request over the caterpillar is at least five
(`BallotCoreIdentification.five_le_openOddCount_genusSix`).  This is why the statements
the genus-six assembly uses carry positivity: `SimpleWallSupply.InConeSupplySimple`
requires both ends of its segments positive, `SimpleWallSupply.countLink_of_positiveGeneral`
requires `PositiveGeneral` at both ends, `CountSchedule.C34` carries `(∀ i, 0 < y i)` in
its binder, and `SimpleWallSupply.TypeChangeSupplyPositive` chooses positive requests.

## What is proved here

* `pos_of_openAt`, `nondegenerate_of_openAt`, `not_openAt_of_nonpos`,
  `pos_of_frameClass_openAt`, `pos_of_open`, `pos_of_geometricFibre_open` --
  **the lemma**, on a frame, as `WallStar.Nondegenerate`, contrapositively, on a
  `FrameClass`, on a `FibreMember` and on a `GeometricFibre` class.  The member form is
  also proved low in the stack as `FibreMember.pos_of_open` (`Count/CoreSlotCoords.lean`),
  so that the rigidity layer does not have to import this module; `pos_of_open` here is
  the frame-route copy, and is what `pos_of_frameClass_openAt` and
  `pos_of_geometricFibre_open` are read from.
* `openOddCount_eq_zero_of_nonpos` -- **the count is zero at any request with a
  non-positive slot.**  No genericity, no cubicity, no genus bound.
* `generalRequest_neg`, `openOddCount_neg_eq_zero` -- the negated request stays
  general and reads zero.
* `PositiveCountInvariance`, `countLink_of_positiveCountInvariance` -- equality of the
  count at any two positive general requests over one core, stated with
  `SimpleWallSupply.PositiveGeneral` so that a negated request is never in its binder, and
  the link it would deliver.

## What is not proved here

* **Nothing here shows `PositiveCountInvariance` is true.**  It is not asserted anywhere,
  and the genus-six assembly does not use it: across a wall only the parity of the count
  is carried.
* **Nothing here computes any `Nat.card (FrameClass …)`.**
-/

namespace DraismaVargas.Count.OpenAtPositivity

open DraismaVargas.Infrastructure
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.CrossCoreTransport (FrameClass fibreEquiv open_fibreEquiv
  openOddCount_eq_card)
open DraismaVargas.Count.StepSupplyReduction (GeneralRequest exists_generalRequest)

variable {n p degree : ℕ}

/-! ## 1.  Openness of a frame forces positivity of the request -/

/-- **An open frame only sits over a strictly positive request.**  The requested
length of the slot `s` is the `k.slot.symm s` row of `k.matrix` applied to the
frame's coordinate vector; the entries of the length matrix are non-negative
genuine path sums, the coordinates are strictly positive by `OpenAt`, and the
row is not identically zero because the matrix is nonsingular.  So the sum is
strictly positive. -/
theorem pos_of_openAt {core : Core n p} (k : Frame core degree) {y : Fin p → ℚ}
    (h : k.OpenAt y) (s : Fin p) : 0 < y s := by
  obtain ⟨c, hc⟩ := PositiveOrthantWall.exists_matrix_ne_zero k (k.slot.symm s)
  have hy : k.matrix.mulVec (k.coordsAt y) (k.slot.symm s) = y s := by
    rw [k.mulVec_coordsAt y]
    simp
  rw [← hy]
  show 0 < ∑ j, k.matrix (k.slot.symm s) j * k.coordsAt y j
  exact Finset.sum_pos' (fun j _ ↦ mul_nonneg (StarPilot.matrix_nonneg k _ j) (h j).le)
    ⟨c, Finset.mem_univ c,
      mul_pos ((StarPilot.matrix_nonneg k _ c).lt_of_ne (Ne.symm hc)) (h c)⟩

/-- The same, as `WallStar.Nondegenerate`: an open frame witnesses that its
request is a genuine metric graph. -/
theorem nondegenerate_of_openAt {core : Core n p} (k : Frame core degree) {y : Fin p → ℚ}
    (h : k.OpenAt y) : WallStar.Nondegenerate y := fun s ↦ pos_of_openAt k h s

/-- The contrapositive: no frame at all is open over a request with a
non-positive slot. -/
theorem not_openAt_of_nonpos {core : Core n p} (k : Frame core degree) {y : Fin p → ℚ}
    {s : Fin p} (hs : y s ≤ 0) : ¬ k.OpenAt y :=
  fun h ↦ absurd (pos_of_openAt k h s) (not_lt.mpr hs)

/-- The lemma on the request-free model. -/
theorem pos_of_frameClass_openAt {core : Core n p} (x : FrameClass core degree)
    {y : Fin p → ℚ} (s : Fin p) (h : x.OpenAt y) : 0 < y s := by
  revert h
  induction x using Quotient.inductionOn with
  | h k => exact fun hk ↦ pos_of_openAt k hk s

/-- **The member form.**  An open `Count.FibreMember` forces its own request
strictly positive.  The same statement is proved low in the stack as
`FibreMember.pos_of_open` (`Count/CoreSlotCoords.lean`), which is the copy the
rigidity layer consumes.  This
copy takes the frame route, and is kept because the `FrameClass` and
`GeometricFibre` corollaries below are read from `pos_of_openAt`. -/
theorem pos_of_open {core : Core n p} {y : Fin p → ℚ} {mem : FibreMember core y degree}
    (h : mem.Open) (s : Fin p) : 0 < y s := by
  refine pos_of_openAt (Frame.of mem) ?_ s
  rw [Frame.openAt_iff_open, Frame.member_of]
  exact h

/-- The same on `Count.GeometricFibre`, the quotient the count is read on. -/
theorem pos_of_geometricFibre_open {core : Core n p} {y : Fin p → ℚ}
    (z : GeometricFibre core y degree) (s : Fin p) (h : z.Open) : 0 < y s := by
  have hx := open_fibreEquiv core degree y ((fibreEquiv core degree y).symm z)
  rw [Equiv.apply_symm_apply] at hx
  exact pos_of_frameClass_openAt _ s (hx.mp h)

/-! ## 2.  The count is supported on the strictly positive orthant -/

/-- **The open odd count vanishes off the positive orthant.**  One non-positive
slot empties the open part of the fibre outright, so the open odd count is
zero there.  No genericity, cubicity or genus hypothesis. -/
theorem openOddCount_eq_zero_of_nonpos (core : Core n p) (degree : ℕ) {y : Fin p → ℚ}
    {s : Fin p} (hs : y s ≤ 0) : GeometricFibre.openOddCount core y degree = 0 := by
  rw [openOddCount_eq_card core y degree]
  have : IsEmpty {x : FrameClass core degree // x.OpenAt y ∧ x.IsOdd} :=
    ⟨fun x ↦ absurd (pos_of_frameClass_openAt x.1 s x.2.1) (not_lt.mpr hs)⟩
  exact Nat.card_of_isEmpty

/-- **Negating a general request leaves it general.**  `GeneralRequest` asks only
that no frame coordinate vanishes, and every frame coordinate is linear in the
request (`PositiveOrthantWall.coordsAt_smul`). -/
theorem generalRequest_neg {core : Core n p} {y : Fin p → ℚ}
    (hy : GeneralRequest core degree y) :
    GeneralRequest core degree (fun s ↦ (-1 : ℚ) * y s) := by
  intro k col
  rw [PositiveOrthantWall.coordsAt_smul k (-1) y col]
  exact mul_ne_zero (by norm_num) (hy k col)

/-- The negated request reads zero. -/
theorem openOddCount_neg_eq_zero (core : Core n p) (degree : ℕ) {y : Fin p → ℚ} {s : Fin p}
    (hs : 0 < y s) :
    GeometricFibre.openOddCount core (fun t ↦ (-1 : ℚ) * y t) degree = 0 :=
  openOddCount_eq_zero_of_nonpos core degree (s := s)
    (show (-1 : ℚ) * y s ≤ 0 by linarith)

/-! ## 3.  Count invariance between positive general requests -/

/-- **Equality of the count at any two positive general requests over one core.**
`SimpleWallSupply.PositiveGeneral` is `GeneralRequest` together with strict positivity of
every slot, so a negated request is never in the binder and the negation argument of §2
does not apply.  It is not asserted anywhere. -/
def PositiveCountInvariance (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (y y' : Fin p → ℚ), SimpleWallSupply.PositiveGeneral core degree y →
    SimpleWallSupply.PositiveGeneral core degree y' →
      GeometricFibre.openOddCount core y degree =
        GeometricFibre.openOddCount core y' degree

/-- It would deliver the link `CountTransportLink.CountLink` at positive general
requests -- which is where `SimpleWallSupply.countLink_of_positiveGeneral` reads them. -/
theorem countLink_of_positiveCountInvariance (h : PositiveCountInvariance degree n p)
    (core : Core n p) {y y' : Fin p → ℚ} (hy : SimpleWallSupply.PositiveGeneral core degree y)
    (hy' : SimpleWallSupply.PositiveGeneral core degree y') :
    CountTransportLink.CountLink degree core y core y' :=
  CountTransportLink.countLink_of_openOddCount_eq (h core y y' hy hy')

end DraismaVargas.Count.OpenAtPositivity
