module

public import DraismaVargasCount.IntegerCount.StarBalance
public import DraismaVargasCount.W4NonDiscreteStarExhaustionProof

@[expose] public section

/-!
# The balance by sides at the four-valent walls

The integer twin of `W4NonDiscreteStarExhaustionProof.familyStarParity_w4_all`.  The parity
proof splits the four-valent walls into discrete ones (`W4StarParity.starParityAt_of_discrete`,
over `W4StarParity.partialStarEquiv`, `W4StarParity.candidate`, `W4StarParity.lab`) and
non-discrete ones (`W4NonDiscreteStarExhaustionProof.w4NonDiscreteStarExhaustion`, through
`W4NonDiscreteStarCensus.census_of_exhausts`); in both the star is the set of nonsingular
pairings of Equation (1) of Draisma--Vargas Part I, and the balance is
`RegrowthWallInput.w4_sum_signedMult_eq_zero`.

The integer proof needs no split.  `W4NonDiscreteStarExhaustionProof.exhausts` exhausts the
star by the nonsingular positions at every four-valent wall, discrete or not, and the positions
(`W4NonDiscreteStarCensus.rep`) are `StarCensusEngine` frames.  Their engine labelling is the
balance's labelling `W4StarParity.lab` (`engineLabelling_eq_lab`), so the side law is the generic
`opensToward_engineFrame_iff`, with no sign comparison: W4 is like `w3Shift`.

## Contents

* `engineLabelling_eq_lab` (proved): the engine labelling of a position is the balance's.
* `w4SignedCensus` (defined): the signed census of a four-valent star.
* `familyStarBalance_w4` (proved).
-/

namespace DraismaVargas.Count.IntegerCount

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open DraismaVargas.Count.WallStar (Regrowth Nondegenerate)
open W4TargetPairings (FourStar)
open DraismaVargas.Count.W4WallExhaustion (mergeVertex)
open DraismaVargas.Count.W4NonDiscreteStarCensus (Nonsingular)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- **The engine labelling of a position of Equation (1) is the balance's labelling.**  Both
read the rows through the family's stable-path dictionary and the wall's inherited row labels,
and the columns through the wall's own coordinates (`W4StarParity.lab_row`,
`W4StarParity.lab_targetEdge`). -/
theorem engineLabelling_eq_lab (w : Regrowth core y degree) (hy : Nondegenerate y)
    (star : FourStar (w.frame.limitTarget w.column) (mergeVertex w)) (q : Fin 3) :
    StarCensusEngine.labelling w hy (W4StarParity.datum w hy star q)
        (W4NonDiscreteStarCensus.equiv w hy star q) = W4StarParity.lab w hy star q := by
  have hext : ∀ {target : CFGraph} {data : GluingDatum target degree}
      (L L' : W4StableSource.StableLengthMatrixLabelling data (Fin p)),
      L.row = L'.row → L.targetEdge = L'.targetEdge → L = L' := by
    rintro _ _ ⟨_, _⟩ ⟨_, _⟩ rfl rfl
    rfl
  refine hext _ _ ?_ ?_
  · rw [W4StarParity.lab_row]
    rfl
  · rw [W4StarParity.lab_targetEdge]
    rfl

/-- **The signed census of a four-valent star.**  Positions: the three pairings of
Equation (1); terms: the balance's signed multiplicities; census map: the classes of the
nonsingular positions, `W4NonDiscreteStarCensus.repCls`, bijective by exhaustion at every
four-valent wall (`W4NonDiscreteStarExhaustionProof.exhausts`); side law: the engine side law
(`opensToward_engineFrame_iff`), since the engine labelling of every position is the
balance's (`engineLabelling_eq_lab`). -/
noncomputable def w4SignedCensus (w : Regrowth core y degree) (hy : Nondegenerate y)
    (hFour : (GluingDatum.incidentEdges (mergeVertex w)).card = 4) :
    SignedStarCensus hy w :=
  let star : FourStar (w.frame.limitTarget w.column) (mergeVertex w) := FourStar.of_card hFour
  have hExh := W4NonDiscreteStarExhaustionProof.exhausts w hy star hFour
  { ι := Fin 3
    term := fun q ↦ signedMult (W4StarParity.lab w hy star q).presentation
    integral := fun q ↦ by
      by_cases hq : Nonsingular w hy star q
      · exact isIntegralMultiplicity (W4StarParity.fullDim w hy star q hq)
      · exact ⟨0, by
          rw [W4NonDiscreteStarCensus.signedMult_eq_zero_of_not_nonsingular w hy star q hq]
          simp⟩
    balance := RegrowthWallInput.w4_sum_signedMult_eq_zero w hy star
      (W4StarParity.initial w hy star)
    nonsingular := Nonsingular w hy star
    zero_of_singular := W4NonDiscreteStarCensus.signedMult_eq_zero_of_not_nonsingular w hy star
    equiv := Equiv.ofBijective _ ⟨W4NonDiscreteStarCensus.repCls_injective w hy star,
      W4NonDiscreteStarCensus.repCls_surjective w hy star hExh⟩
    multNat_equiv := fun q ↦ W4NonDiscreteStarCensus.multNat_rep w hy star q.1 q.2
    numerator := wallNumeratorAt w
    numerator_neg := wallNumeratorAt_neg w
    side := fun q d ↦ by
      have h := opensToward_engineFrame_iff w hy (W4StarParity.fullDim w hy star q.1 q.2)
        (W4NonDiscreteStarCensus.matrix_retained w hy star q.1) d
      rw [engineLabelling_eq_lab] at h
      exact h }

/-- **The four-valent walls are balanced by sides.**  Proved, at every four-valent wall,
discrete or not, by `w4SignedCensus` and `starBalanceAt_of_signedCensus`.  This is Part II's
balancing condition `prop-signed-mult` at a four-valent limit, with the side law of
`ConeSide`.  The two facts that make it short: the exhaustion of the star by the nonsingular
positions of Equation (1) holds at every four-valent wall
(`W4NonDiscreteStarExhaustionProof.exhausts`), and the positions are engine frames whose engine
labelling *is* the balance's labelling (`engineLabelling_eq_lab`), so no sign comparison is
needed. -/
theorem familyStarBalance_w4 (degree n p : ℕ) : FamilyStarBalance degree n p .w4 := by
  intro core y hy w cls htag
  exact starBalanceAt_of_signedCensus
    (w4SignedCensus w hy ((RegrowthWallInput.sourceCase_eq_w4_iff cls).mp htag))

end DraismaVargas.Count.IntegerCount
