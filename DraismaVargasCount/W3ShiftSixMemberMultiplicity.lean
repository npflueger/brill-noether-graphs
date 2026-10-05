module

public import DraismaVargasCount.W3ShiftSixMemberMatrices

@[expose] public section

/-!
# Equation (3): the six-member signed-multiplicity balance

This file proves the balancing identity of Draisma–Vargas Part I, Equation (3) (Case
`{w3-r1-nd3-t2-(a>k4)}`, Figure 29) on its six members, three shrink/grow pairs.
One selected member's full-dimensional presentation supplies the structural
data for every nonsingular member via the proved common stable-incidence maps.
Each pair either has both determinants zero, hence contributes zero, or its
shrink member is nonsingular and supplies the sharp denominator needed by the
pair balance. No full-dimensionality is assumed for singular members.

The final constructed-family theorem uses the three direction packages built by
`exists_sixPackages`, not three independently supplied full-dimensional charts or
denominator hypotheses.  The star of the wall, with the nonsingular members of
Equation (3) as its classes, is treated separately
(`DraismaVargasCount.W3ShiftStarCensusProof`, `DraismaVargasCount.W3ShiftStarExhaustionProof`).
-/

namespace DraismaVargas.Count.W3ShiftSixMemberMultiplicity

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open W4Assembly W4StableSource ThirdEquation FullDimensionalSource
open W3ShiftSourceCandidates W3ShiftSixMemberBalance W3ShiftSixMemberMatrices

variable {target : CFGraph.{0}} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {input : W3SourceInput data star}
  {shifts : Fin 3 → ShiftProfile input}
  (pairs : ∀ direction, PairPackage (shifts direction))

/-- Stable incidence between any two of the six members, including across gauges. -/
noncomputable def between (first second : MemberIndex) :
    StableGraphIncidence.Equivalence (member pairs first).datum (member pairs second).datum :=
  (memberIncidence pairs first).symm.trans (memberIncidence pairs second)

/-- Each member has the original wall datum's source genus. -/
theorem member_sourceGenus (i : MemberIndex) :
    genus (member pairs i).datum.sourceGraph = genus data.sourceGraph :=
  (W3ShiftStableIncidence.candidate_sourceGenus (pairs i.1).shrink i.2).trans
    (pairs i.1).copy.sourceGenus

section Presentation

variable (hConnected : graph_connected target) (hGenus : genus target = 0)
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (selected : MemberIndex)
  (incomingFD : FullDimensionalSourcePresentation (member pairs selected).datum coordinate)

/-- Only the destination's common-coordinate matrix needs to be nonsingular;
all other full-dimensionality data are transported from the one selected member. -/
noncomputable def memberPresentation (i : MemberIndex)
    (hDet : (squareMatrix pairs selected incomingFD.labelling i).det ≠ 0) :
    FullDimensionalSourcePresentation (member pairs i).datum coordinate :=
  StableGraphFullDimensional.presentationOfEquivalence incomingFD (between pairs selected i)
    ((member pairs i).datum_valid (pairs i.1).gaugeInput.valid)
    (W3ShiftStableIncidence.candidate_targetConnected (pairs i.1).shrink hConnected i.2)
    (W3ShiftStableIncidence.candidate_targetGenus (pairs i.1).shrink hGenus i.2)
    ((W3ShiftStableIncidence.candidate_targetEdgeCard (pairs i.1).shrink i.2).trans
      (W3ShiftStableIncidence.candidate_targetEdgeCard (pairs selected.1).shrink selected.2).symm)
    ((member_sourceGenus pairs i).trans (member_sourceGenus pairs selected).symm)
    (labelling pairs selected incomingFD.labelling i) hDet

@[simp] theorem memberPresentation_labelling (i : MemberIndex)
    (hDet : (squareMatrix pairs selected incomingFD.labelling i).det ≠ 0) :
    (memberPresentation pairs hConnected hGenus selected incomingFD i hDet).labelling =
      labelling pairs selected incomingFD.labelling i := rfl

/-- A zero determinant makes the literal signed multiplicity zero. -/
theorem signedMult_eq_zero_of_det (i : MemberIndex)
    (hDet : (squareMatrix pairs selected incomingFD.labelling i).det = 0) :
    signedMult (labelling pairs selected incomingFD.labelling i).presentation = 0 := by
  change _ * (squareMatrix pairs selected incomingFD.labelling i).det = 0
  rw [hDet, mul_zero]

include hConnected hGenus in
/-- Each direction pair balances in the same six-member coordinates,
even when this pair is singular and the selected member is in another direction. -/
theorem pair_sum_signedMult_eq_zero (direction : Fin 3) :
    ∑ position : Fin 2,
      signedMult (labelling pairs selected incomingFD.labelling (direction, position)).presentation = 0 := by
  let p := pairs direction
  let initial := labelling pairs selected incomingFD.labelling (direction, 0)
  by_cases hDet : (squareMatrix pairs selected incomingFD.labelling (direction, 0)).det = 0
  · have hContribution : W3ShiftHonestBalance.wallContribution p.shrink
        p.gaugeInput.valid initial = 0 := by
      apply (W3ShiftHonestBalance.det_eq_zero_iff_zero p.shrink p.gaugeInput.valid initial).mp
      simpa only [initial, p, pair_squareMatrix_eq] using hDet
    apply Finset.sum_eq_zero
    intro position _
    apply signedMult_eq_zero_of_det pairs selected incomingFD
    have hZero := (W3ShiftHonestBalance.det_eq_zero_iff
      p.shrink p.gaugeInput.valid initial position).mpr hContribution
    simpa only [initial, p, pair_squareMatrix_eq] using hZero
  · let fd := memberPresentation pairs hConnected hGenus selected incomingFD (direction, 0) hDet
    have hSharp := W3ShiftIncomingDenominator.incomingRowDenominator_of_shrink p.shrink fd
    have hSum := W3ShiftMultiplicityBalance.sum_signedMult_eq_zero_of_sharp
      p.shrink p.gaugeInput.valid initial hSharp
    simpa only [initial, p, pair_labelling_eq, member] using hSum

include hConnected hGenus in
/-- **Equation (3): the sum of all six signed multiplicities is zero.**
Only one selected member's full-dimensional chart is required. -/
theorem sum_signedMult_eq_zero :
    ∑ i : MemberIndex,
      signedMult (labelling pairs selected incomingFD.labelling i).presentation = 0 := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_eq_zero fun direction _ ↦
    pair_sum_signedMult_eq_zero pairs hConnected hGenus selected incomingFD direction

end Presentation

section Constructed

open W3R1SourceProfile

variable (profile : Nd3Profile data input.distinguishedBlock)
  (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
  (largest_lt : data.sourceEdgeIndex profile.largest.1 <
    (data.vertexPartition wall).blockCard input.distinguishedBlock.1)
  (hConnected : graph_connected target) (hGenus : genus target = 0)

/-- The constructor `exists_sixPackages` chooses all three direction packages. -/
noncomputable def constructedPackages : ∀ direction : Fin 3,
    PairPackage (orientation profile directions largest_lt direction) :=
  Classical.choice (exists_sixPackages profile directions largest_lt hConnected hGenus)

/-- Equation (3) on the constructed six-member family.  Beyond one full-dimensional
presentation of the selected member, no shrink data, matrix compatibility, sharp
denominators or per-pair full-dimensional presentations are assumed. -/
theorem sum_signedMult_constructed_eq_zero
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (selected : MemberIndex)
    (incomingFD : FullDimensionalSourcePresentation
      (member (constructedPackages profile directions largest_lt hConnected hGenus) selected).datum
        coordinate) :
    ∑ i : MemberIndex, signedMult
      (labelling (constructedPackages profile directions largest_lt hConnected hGenus)
        selected incomingFD.labelling i).presentation = 0 :=
  sum_signedMult_eq_zero _ hConnected hGenus selected incomingFD

end Constructed

end DraismaVargas.Count.W3ShiftSixMemberMultiplicity
