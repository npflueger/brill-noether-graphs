import DraismaVargasCount.CoreRelabelInvariance

/-!
# General requests

The count is compared only at *general* requests: requests at which no coordinate of any
full-dimensional frame vanishes, that is, requests on no wall of any frame. This module isolates
that notion and the facts about it that the propagation step (step 4 of
`DraismaVargasCount.Assembly`) uses.

* `GeneralRequest` is exactly the `general` field of `CountSchedule.Schedule` and the last
  hypothesis of `CountSchedule.C34`, pulled out so that it can be quantified over.
  `exists_generalRequest` produces a positive general request over every core and in every
  degree, with no hypothesis.
* `isWall_one_iff`: a request is general exactly when it is not a wall parameter of a segment
  ending at it. Since `CountSchedule.Schedule.transport` never stops at a wall parameter, the
  general requests are exactly the endpoints the segment calculus reaches.
* `not_open_of_coordsAt_eq_zero`: a frame on one of its own walls is closed there. The count at a
  non-general request therefore omits every frame whose wall it lies on, and there is no reason
  for its parity to agree with the parity at nearby general requests.
* `typeChangeObligation_of_core_eq`: across a step that does not move the core, general requests
  on the two sides are trivially linked. A Whitehead move always moves the core (it swaps two
  darts whose vertices are the distinct ends of the base edge), so this lemma applies to no
  actual move; it only records the shape of the obligation that step 3 of `Assembly` discharges.
* `relabelFrame`, `coordsAt_relabelFrame`, `generalRequest_relabel`: genericity transports along
  a relabelling of the core (`CoreRelabel.Relabel`). A relabelled frame keeps its target, datum,
  full-dimensionality receipt and length matrix, so its coordinate vector is literally the old
  one. This is what lets the terminal `CoreIso` of `CoreOfDarts.exists_chain` be removed without
  losing genericity.
-/

namespace DraismaVargas.Count.StepSupplyReduction

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore Step CoreIso)
open DraismaVargas.Count.CoreRelabel (Relabel)
open Utilities.Certificate.ExplicitPotential (Core)
open SegmentWalls (Frame)

variable {n p degree : ℕ}

/-! ## 1.  General requests -/

/-- **General requests.**  A request is general over a core when no coordinate of
any full-dimensional frame vanishes at it.  This is exactly the `general` field of
`CountSchedule.Schedule` and exactly the last hypothesis of `CountSchedule.C34`,
pulled out so it can be quantified over. -/
def GeneralRequest (core : Core n p) (degree : ℕ) (y : Fin p → ℚ) : Prop :=
  ∀ (k : Frame core degree) (col : Fin p), k.coordsAt y col ≠ 0

/-- **General requests exist, positively, over every core**, with no hypothesis.
This is `SegmentWalls.exists_general_positive_fibre` at the all-ones base, and
it is what makes every restriction below non-vacuous. -/
theorem exists_generalRequest (core : Core n p) (degree : ℕ) :
    ∃ y : Fin p → ℚ, (∀ i, 0 < y i) ∧ GeneralRequest core degree y :=
  SegmentWalls.exists_general_positive_fibre core degree (fun _ ↦ 1) fun _ ↦ one_pos

theorem segment_one (y₀ y₁ : Fin p → ℚ) :
    RationalAffineWall.segment y₀ y₁ 1 = y₁ := by
  funext i
  simp [RationalAffineWall.segment]

/-- **General requests are exactly the endpoints the segment calculus reaches.**
A request is general precisely when the segment parameter that lands on it is not
a wall parameter -- and `CountSchedule.Schedule.transport` refuses to land on a
wall parameter.  So restricting to general requests loses nothing that the
segment calculus could reach. -/
theorem isWall_one_iff (core : Core n p) (degree : ℕ) (y₀ y₁ : Fin p → ℚ) :
    CountSchedule.IsWall core degree y₀ y₁ 1 ↔ ¬ GeneralRequest core degree y₁ := by
  constructor
  · rintro ⟨k, col, hk⟩ hgen
    refine hgen k col ?_
    have hk' : k.coordsAt (RationalAffineWall.segment y₀ y₁ 1) col = 0 := hk
    rwa [segment_one] at hk'
  · intro h
    by_contra hw
    refine h fun k col hk ↦ hw ⟨k, col, ?_⟩
    show k.coordsAt (RationalAffineWall.segment y₀ y₁ 1) col = 0
    rwa [segment_one]

/-- **Why a non-general request is the wrong place to read the count.**
`Open` is a *strict* positivity condition on a frame's coordinates, so a frame
sitting on one of its own walls is closed there.  The count at a non-general
request therefore omits every frame whose wall it lies on; there is no reason to
expect its parity to agree with that of a nearby general request, which is why
the count is only ever compared at general requests. -/
theorem not_open_of_coordsAt_eq_zero (core : Core n p) (degree : ℕ) (k : Frame core degree)
    (y : Fin p → ℚ) (col : Fin p) (h : k.coordsAt y col = 0) : ¬ (k.member y).Open := by
  intro hopen
  have h0 : 0 < k.coordsAt y col := (Frame.openAt_iff_open k y).mpr hopen col
  rw [h] at h0
  exact lt_irrefl 0 h0

/-! ## 2.  A step that fixes the core -/

/-- **The per-step obligation's shape, discharged under `c.core = c'.core`.**
Whenever a step does not move the core, a count link between general requests on
its two sides follows outright from `exists_generalRequest` and reflexivity.

**This lemma applies to no actual Whitehead move.**  A move swaps two darts whose
vertices are the distinct ends of the base edge, so `vert` genuinely changes and
the hypothesis `c.core = c'.core` fails whenever there is a `Step` to discharge.
The lemma only records the shape of the obligation; the type changes of an actual
move are handled by step 3 of `DraismaVargasCount.Assembly`. -/
theorem typeChangeObligation_of_core_eq (degree : ℕ) (c c' : CubicCore n p)
    (h : c.core = c'.core) :
    ∃ y y' : Fin p → ℚ, GeneralRequest c.core degree y ∧ GeneralRequest c'.core degree y' ∧
      CountTransportLink.CountLink degree c.core y c'.core y' := by
  obtain ⟨y, -, hy⟩ := exists_generalRequest c.core degree
  refine ⟨y, y, hy, ?_, ?_⟩
  · rw [← h]
    exact hy
  · rw [← h]
    exact CountTransportLink.countLink_refl degree c.core y

/-! ## 3.  Genericity transports along a relabelling -/

variable {c c' : Core n p}

/-- **A frame, relabelled.**  Target, datum and full-dimensionality receipt are
untouched; only the identification with the core is re-read, exactly as
`CoreRelabel.relabelMember` re-reads a member. -/
def relabelFrame (d : Relabel c c') (k : Frame c degree) : Frame c' degree where
  target := k.target
  data := k.data
  fullDim := k.fullDim
  ident := CoreRelabel.relabelIdent d k.ident

/-- **A relabelled frame has literally the old coordinate vector.**  Its length
matrix is the old one -- the matrix reads only the full-dimensionality receipt --
and its slot map is the old one composed with the relabelling, which the matched
requests cancel. -/
theorem coordsAt_relabelFrame (d : Relabel c c') (k : Frame c degree)
    {y y' : Fin p → ℚ} (hy : ∀ e, y' (d.slot e) = y e) :
    (relabelFrame d k).coordsAt y' = k.coordsAt y := by
  funext col
  rw [Frame.coordsAt_apply, Frame.coordsAt_apply]
  refine Finset.sum_congr rfl fun row _ ↦ ?_
  show k.matrix⁻¹ col row * y' (d.slot (k.slot row)) = k.matrix⁻¹ col row * y (k.slot row)
  rw [hy]

/-- **Genericity is a relabelling invariant.**  Together with
`CoreRelabel.openOddCount_relabel` this is what lets the terminal `CoreIso` of
`CoreOfDarts.exists_chain` be removed without losing the genericity the next
link needs. -/
theorem generalRequest_relabel (d : Relabel c c') {y y' : Fin p → ℚ}
    (hy : ∀ e, y' (d.slot e) = y e) (hgen : GeneralRequest c degree y) :
    GeneralRequest c' degree y' := by
  intro k' col
  have hy' : ∀ e, y (d.symm.slot e) = y' e := by
    intro e
    have h := hy (d.slot.symm e)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  have h := coordsAt_relabelFrame d.symm k' hy'
  rw [← h]
  exact hgen _ col

end DraismaVargas.Count.StepSupplyReduction
