import Utilities.Subdivision.ZeroBudgetRounding
import Utilities.Gonality.SubdivisionPencil

/-!
# A subdivision pencil with divisible slot moments descends to the odd part of its scale

The rounding entry point of the endgame.  `bnExists_of_pencil_slotMoment` feeds a packaged
`SubdivisionPencil` to `ZeroBudgetRounding.bnExists_of_slotMoment`: a degree-four pencil of
rank at least one on a subdivision at scale `2 ^ a * u`, whose interior chips on every slot
have offset sum (slot moment) divisible by `2 ^ a`, yields
`BNExists (spec.scale u hu).graph 1 4` outright.  The endgame
(`ExpansionSeriesMoment.bnExists_of_bigDivisor`, used through
`DegenerateBigDivisor.bnExists_of_degenerateMember` in step 5 of `Assembly`) reaches it with
`u` the odd part of the member's own realization scale.

The scale's factorization `2 ^ a * u` is a hypothesis about the pencil's scale; the
statement that `u` is odd is not needed for the conclusion and is therefore not assumed.
-/

namespace DraismaVargas.Count.TransportedChipEndgame

open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph

/-! ## Feeding the packaged pencil to the rounding entry point -/

/-- A degree-four subdivision pencil whose scale factors as `2 ^ a * u`, and
whose per-slot interior moments are divisible by `2 ^ a`, descends to the
requested odd-part scale.  This is `ZeroBudgetRounding.bnExists_of_slotMoment`
read on a `SubdivisionPencil` record. -/
theorem bnExists_of_pencil_slotMoment {n p : ℕ} (spec : Spec n p) (u a : ℕ) (hu : 0 < u)
    (w : DraismaVargas.SubdivisionPencil spec 4) (hw : w.scale = 2 ^ a * u)
    (hmom : ∀ e : Fin p, ((2 ^ a : ℕ) : ℤ) ∣
      InteriorFiring.slotMoment (spec.scale w.scale w.scale_pos) w.divisor e) :
    BNExists (spec.scale u hu).graph 1 4 := by
  obtain ⟨scale, scale_pos, divisor, hEff, hDeg, hRank⟩ := w
  dsimp only at hw hmom
  subst hw
  exact ZeroBudgetRounding.bnExists_of_slotMoment spec u a hu divisor hEff
    (by exact_mod_cast hDeg) hmom hRank

end DraismaVargas.Count.TransportedChipEndgame
