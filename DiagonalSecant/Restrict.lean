module

public import DiagonalSecant.Defs

@[expose] public section

/-!
# From a closed full-type member of `H` to a closed typed member of `(Γ, u)`

The type of a member is a property of its frame, so it passes from `H` down to `(Γ, u)`.

A full-type frame `f` of `H` restricts (the restriction of the two-point ramified count,
`restrictTailed`) to a typed frame of type `lowerType (tailType a) 0 = ![a]` in degree
`d − 0 = d`. Its coordinates at the core
part of the request are coordinates of `f` (`coordsAt_restrictTailed`), so closedness passes
down, and its typed multiplicity is `|Mult f|` (`typedAbsMult_restrictTailed`), so odd
multiplicity passes down. The two casts (`![a]` for `lowerType (tailType a) (fun _ ↦ 0)`, `d`
for `d − shed 0`) are definitional up to `Nat` arithmetic and are made by `TypedFrame.cast`
(`Defs.lean`).
-/

namespace DiagonalSecant

open DraismaVargas.Count DraismaVargas.Count.MarkedCount DraismaVargas.Count.MarkedCountGeneral
open DraismaVargas.Count.SegmentWalls (Frame)
open Utilities.Certificate.ExplicitPotential (Core)
open GenusSixExistence.Tripod.Gadget (subdivide)

variable {n p : ℕ}

/-! ## The restriction of a full-type member -/

/-- **A closed full-type member of odd multiplicity restricts to a closed typed member of type
`a` and odd typed multiplicity** at the core part of the request. -/
theorem exists_typed_of_fullType {core : Core n p} (hCubic : core.Cubic) (s : Fin p)
    {a d : ℕ} (ha : 1 ≤ a) {y : Fin (p + 1) → ℚ}
    (mem : FibreMember (tailed core s a).H ((tailed core s a).request y) d)
    (hClosed : mem.Closed) (hOdd : mem.HasOddMult)
    (hFull : IsFullType (tailed core s a) (tailed_markedCubic hCubic s) (Frame.of mem)) :
    ∃ κ : TypedFrame (subdivide core s) (onceMark n) ![a] d,
      (∀ col, 0 ≤ κ.coordsAt y col) ∧ ∃ m : ℕ, Odd m ∧ κ.typedAbsMult = m := by
  have hc := tailed_markedCubic hCubic s
  set f := Frame.of mem with hf
  -- the restriction, read at the zero index
  have key : ∀ z : LowerFrame (subdivide core s) (onceMark n) (tailType a) d,
      z.1 = (fun _ ↦ 0) →
      ∃ κ : TypedFrame (subdivide core s) (onceMark n)
          (lowerType (tailType a) (fun _ ↦ 0)) (d - shed (c := tailType a) (fun _ ↦ 0)),
        (∀ y', κ.coordsAt y' = z.2.1.coordsAt y') ∧ κ.typedAbsMult = z.2.1.typedAbsMult := by
    rintro ⟨J, κ, sl⟩ hJ
    dsimp only at hJ
    subst hJ
    exact ⟨κ, fun _ ↦ rfl, rfl⟩
  obtain ⟨κ₀, hκ₀c, hκ₀m⟩ := key (restrictTailed (tailed core s a) hc f) hFull.lowerIndex_eq
  have hShed : d - shed (c := tailType a) (fun _ ↦ 0) = d := by
    rw [show shed (c := tailType a) (fun _ ↦ 0) = 0 from Finset.sum_eq_zero fun _ _ ↦ rfl,
      Nat.sub_zero]
  refine ⟨TypedFrame.cast (lowerType_tailType_zero ha) hShed κ₀, fun col ↦ ?_, ?_⟩
  · obtain ⟨cols, slotOf, weight, -, hCoords⟩ := coordsAt_restrictTailed (tailed core s a) hc f
    have h := (hCoords y ((tailed core s a).request y)
      (fun i ↦ (tailed core s a).request_coreSlot y i)).1 col
    rw [TypedFrame.coordsAt_cast, hκ₀c, ← h, hf, Frame.coordsAt_of]
    exact hClosed _
  · obtain ⟨m, hm, hmem⟩ := hOdd
    refine ⟨m, hm, ?_⟩
    rw [TypedFrame.typedAbsMult_cast, hκ₀m, typedAbsMult_restrictTailed]
    exact hmem

end DiagonalSecant
