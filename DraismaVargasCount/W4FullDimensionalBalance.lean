module

public import DraismaVargasCount.W4IncomingIndex
public import DraismaVargasCount.OutgoingRowCalculus

@[expose] public section

/-!
# W4 balance from the actual incoming full-dimensional member

Source: Draisma--Vargas Part I (arXiv:1909.12924), case `{w4}`, Figures 26--27 and
Equation (1).

`W4IncomingIndex` discharges the wall-column census assuming tameness of the
incoming rows. That assumption is unnecessary on the actual family.
Retain any incoming occurrence in the given full-dimensional member. If its
index is ramified, the member row avoids leaves and is target-injective.
The occurrence-induced W4 row lift pulls injectivity back to the incoming row,
so that index divides the incoming denominator. Unit indices divide trivially.

One actual full-dimensional member therefore supplies all incoming index
divisibilities, for all three pairings at once. Feeding `W4UnitBalance` closes
Equation (1) without a tameness, simple-column, or member-presentation receipt.
The only extra datum is the incoming full-dimensional chart.
`RegrowthWallInput.w4_sum_signedMult_eq_zero` supplies exactly that datum at every
regrowth's own wall, so `sum_signedMult_eq_zero` below is discharged there with no
remaining hypothesis; this is part of the multiplicity input of the star parity in step 2
(trivalent walls) of `DraismaVargasCount/Assembly.lean`.
-/

namespace DraismaVargas.Count.W4FullDimensionalBalance

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open W4Assembly W4StableSource W4OutgoingStableRows W4OutgoingLimitMatrix W4CommonBalance
open FullDimensionalSource StableSourceMatrix
open RowWalk TrivalentWeight

variable {target : CFGraph.{0}} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : W4TargetPairings.FourStar target wall}
  [DecidableEq target.edges]

/-- The actual W4 row lift sends each incoming occurrence to its retained copy. -/
theorem onRow_retained (input : AuxR0SourceInput data star) (pairing : Fin 3)
    {path : StablePath data} {edge : data.SourceEdge} (hEdge : OnRow data path edge) :
    OnRow (member input pairing).datum (stablePathLift input pairing path)
      ((member input pairing).oldSourceEdge edge) := by
  refine ⟨ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 edge hEdge.1, ?_⟩
  exact (stablePathLift_mk input pairing ⟨edge, hEdge.1⟩).symm.trans
    (congrArg (stablePathLift input pairing) hEdge.2)

/-- Retained target-column injectivity pulls back to the original row. -/
theorem rowTargetInjective_of_member (input : AuxR0SourceInput data star) (pairing : Fin 3)
    {path : StablePath data}
    (hMember : RowTargetInjective (member input pairing).datum
      (stablePathLift input pairing path)) : RowTargetInjective data path := by
  intro first second hFirst hSecond hTarget
  apply ResolutionCut.oldSourceEdge_injective (member input pairing)
  apply hMember _ _ (onRow_retained input pairing hFirst) (onRow_retained input pairing hSecond)
  exact congrArg (fun place ↦ occurrenceEquiv target wall (member input pairing).right (some place))
    hTarget

/-- Every index on every incoming row divides that row's denominator, as soon
as any one actual W4 member is full dimensional. -/
theorem index_dvd_incomingRowDenominator (input : AuxR0SourceInput data star) (incoming : Fin 3)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incomingFD : FullDimensionalSourcePresentation (member input incoming).datum coordinate)
    {path : StablePath data} {edge : data.SourceEdge} (hEdge : OnRow data path edge) :
    data.sourceEdgeIndex edge ∣ incomingRowDenominator data path := by
  by_cases hOne : data.sourceEdgeIndex edge = 1
  · rw [hOne]
    exact one_dvd _
  have hMember := onRow_retained input incoming hEdge
  have hTame := OutgoingRowCalculus.rowRamificationAtMostOne_of_index_ne_one incomingFD hMember
    (by rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge]; exact hOne)
  have hInjective := rowTargetInjective_of_member input incoming
    (RowGeodesic.rowTargetInjective_of_genusZero incomingFD.targetConnected incomingFD.targetGenus
      incomingFD.danglingEdgeNoGlue incomingFD.pathEnds hTame)
  exact dvd_incomingRowDenominator_of_rowTargetInjective hInjective hEdge

/-- The exact W4 wall-index receipt is produced for every pairing, with no
incoming row tameness assumption. -/
theorem hIndex (input : AuxR0SourceInput data star) (incoming : Fin 3)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incomingFD : FullDimensionalSourcePresentation (member input incoming).datum coordinate)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) (path : StablePath data)
    (hRow : blockRegrownRow input pairing sourceBlock = some path) :
    data.sourceEdgeIndex (blockOldSourceEdge input pairing sourceBlock) ∣
      incomingRowDenominator data path :=
  index_dvd_incomingRowDenominator input incoming incomingFD
    (W4IncomingIndex.onRow_blockOldSourceEdge input pairing sourceBlock path hRow)

section Balance

/-- All three W4 denominator products equal the incoming product. -/
theorem denominatorProduct_eq_incoming (input : AuxR0SourceInput data star) (incoming : Fin 3)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (initial : StableLengthMatrixLabelling (member input 0).datum coordinate)
    (incomingFD : FullDimensionalSourcePresentation (member input incoming).datum coordinate)
    (pairing : Fin 3) :
    denominatorProduct (labelling input initial pairing).presentation = incomingDenominatorProduct data :=
  W4UnitBalance.denominatorProduct_eq_incoming input (hIndex input incoming incomingFD) initial pairing

/-- Full Equation (1) on the actual family, with the incoming chart as the
only full-dimensional input and no row-calculus receipt. -/
theorem sum_signedMult_eq_zero (input : AuxR0SourceInput data star) (incoming : Fin 3)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (initial : StableLengthMatrixLabelling (member input 0).datum coordinate)
    (incomingFD : FullDimensionalSourcePresentation (member input incoming).datum coordinate) :
    ∑ pairing : Fin 3, signedMult (labelling input initial pairing).presentation = 0 :=
  W4UnitBalance.sum_signedMult_eq_zero input (hIndex input incoming incomingFD) initial

noncomputable local instance : DecidableEq (Option target.edges) := Classical.decEq _

/-- Canonical-coordinate Equation (1), with the same actual incoming chart. -/
theorem sum_signedMult_canonical_eq_zero (input : AuxR0SourceInput data star) (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation (member input incoming).datum
      (Option target.edges)) :
    ∑ pairing : Fin 3,
      signedMult (labelling input (canonicalInitialLabelling input) pairing).presentation = 0 :=
  sum_signedMult_eq_zero input incoming (canonicalInitialLabelling input) incomingFD

end Balance

end DraismaVargas.Count.W4FullDimensionalBalance

