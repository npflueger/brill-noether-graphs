module

public import DiagonalSecant.CountAtActual
public import DraismaVargasCount.ClosedBoundaryMember
public import GenusSixExistence.BrillNoetherRank.Tripod.ClosureFrame

@[expose] public section

/-!
# The closure on the tailed core: a closed full-type member of odd multiplicity

The segment argument is that of `Research/genus-six-brill-noether-rank.md` §6.4.

The closure is run **on the tailed core `H`**, not on the typed frames: the public segment-wall
machinery (`DraismaVargasCount/SegmentWalls.lean`, `ClosedBoundaryMember.lean`) is stated for
unmarked frames of a core, and `H` is a core. The typed statement is recovered afterwards by
restriction (`Restrict.lean`). The closure is the instance of the segment argument
`ClosureFrame.exists_closed_of_segment` with

* the frame predicate `IsFullType`;
* the walls of `H` in degree `d`;
* the walls of `Γ` in degree `d − a/2` at the merged request, pulled back along the linear map
  `dropMap : yH ↦ mergeRequest s (core part of yH)` (with the section `liftDrop`), which is the
  drop clause `OnceDropGeneral`;
* no functionals and no conditions near the end of the segment;
* the open members supplied by `CountAtActual.exists_open_oddFullType`.

The endpoint is `(tailed core s a).request y`: core part `y ≥ 0`, tails `1`. Along the segment
from a positive general start the tails stay positive, so `exists_open_oddFullType` applies at
the interior point, and the frame carried to `t = 1` is closed there.
-/

namespace DiagonalSecant

open DraismaVargas.Count DraismaVargas.Count.MarkedCount DraismaVargas.Count.MarkedCountGeneral
open DraismaVargas.Count.SegmentWalls (Frame NFFrame)
open DraismaVargas.Infrastructure
open Utilities.Certificate.ExplicitPotential (Core)
open GenusSixExistence.Tripod.Gadget (subdivide)

variable {n p : ℕ}

/-- The core part of a request on `H`. -/
noncomputable def corePart {core : Core n p} {s : Fin p} {a : ℕ} (yH : Fin (tailed core s a).P → ℚ) :
    Fin (p + 1) → ℚ :=
  fun i ↦ yH ((tailed core s a).coreSlot i)

/-- The linear map `yH ↦ mergeRequest s (corePart yH)` along which the drop walls are pulled
back. -/
noncomputable def dropMap (core : Core n p) (s : Fin p) (a : ℕ) :
    (Fin (tailed core s a).P → ℚ) →ₗ[ℚ] (Fin p → ℚ) where
  toFun yH := mergeRequest s (corePart yH)
  map_add' x z := by
    funext i
    simp only [mergeRequest, corePart, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    funext i
    simp only [mergeRequest, corePart, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

@[simp] theorem dropMap_apply (core : Core n p) (s : Fin p) (a : ℕ)
    (yH : Fin (tailed core s a).P → ℚ) : dropMap core s a yH = mergeRequest s (corePart yH) :=
  rfl

/-- A section of `dropMap`: `z` on the old core slots, `0` on the new piece and the tails. -/
noncomputable def liftDrop (core : Core n p) (s : Fin p) (a : ℕ) (z : Fin p → ℚ) :
    Fin (tailed core s a).P → ℚ :=
  fun e ↦ Sum.elim (Fin.snoc z 0 : Fin (p + 1) → ℚ) (fun _ ↦ 0)
    ((tailed core s a).slotEquiv.symm e)

theorem dropMap_liftDrop (core : Core n p) (s : Fin p) (a : ℕ) (z : Fin p → ℚ) :
    dropMap core s a (liftDrop core s a z) = z := by
  have h : corePart (liftDrop core s a z) = (Fin.snoc z 0 : Fin (p + 1) → ℚ) := by
    funext i
    simp [corePart, liftDrop, Tailed.coreSlot]
  rw [dropMap_apply, h]
  funext i
  simp [mergeRequest]

/-- **The closure on `H`** (the tripod's Theorem 6.3, one mark, no legs): at every request on
`H` whose core part is non-negative and whose tails are `1`, some member of `H` in degree `d` is
closed, has odd multiplicity, and is of full type. -/
theorem exists_closed_oddFullType_of_nonneg {core : Core n p} (hCubic : core.Cubic)
    (hConnected : core.Connected) {g : ℕ} (hg : p + 1 - n = g) (hg5 : 5 ≤ g) (s : Fin p)
    {a d : ℕ} (ha : 1 ≤ a) (hd : g + a + 2 = 2 * d) (hL : d ≤ g)
    (hOdd : Odd (markedFormula g d a)) (y : Fin (p + 1) → ℚ) (hy : ∀ i, 0 ≤ y i) :
    ∃ mem : FibreMember (tailed core s a).H ((tailed core s a).request y) d,
      mem.Closed ∧ mem.HasOddMult ∧
        IsFullType (tailed core s a) (tailed_markedCubic hCubic s) (Frame.of mem) := by
  have hYnn : ∀ e, 0 ≤ (tailed core s a).request y e := by
    intro e
    rcases (tailed core s a).slot_cases e with ⟨i, rfl⟩ | ⟨j, t, rfl⟩
    · rw [Tailed.request_coreSlot]; exact hy i
    · rw [Tailed.request_tailSlot]; exact zero_le_one
  exact GenusSixExistence.Tripod.ClosureFrame.exists_closed_of_segment (tailed core s a).H d
    core (d - a / 2) (dropMap core s a)
    (fun z ↦ ⟨liftDrop core s a z, dropMap_liftDrop core s a z⟩)
    ∅ (by simp) (fun (k : Empty) _ ↦ k.elim) _ _ hYnn (fun _ k ↦ k.elim)
    fun y₀ hpos hH hDrop _ _ ↦ exists_open_oddFullType hCubic hConnected hg hg5 s ha hd hL hOdd
      (y := corePart y₀) (fun _ ↦ hpos _) (yH := y₀) (fun _ ↦ rfl) (fun _ _ ↦ hpos _) hH hDrop

end DiagonalSecant
