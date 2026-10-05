module

public import DraismaVargasCount.W2MkkIncomingDenominator
public import DraismaVargas.LocalCases.W3ShiftHonestBalance

@[expose] public section

/-!
# Sharp incoming denominators from Figure 29's members

This file concerns the grow and shrink members of Draisma–Vargas Part I, Figure 29
(Case `{w3-r1-nd3-t2-(a>k4)}`, Equation (3)).
Full dimensionality of either the grow or shrink member forces the incoming
moving-row denominator to equal its retained index k. The case itself gives
k ≥ 2; the new occurrence has index k+1 or k-1 and ends at a trivalent vertex.
The proofs use the members' own occurrence lift and endpoint census, without
assuming row tameness, injective target columns, or a transition hypothesis.

This is the sharp-row input to the balance of Equation (3), obtained from the index
pattern along rows (the row calculus, the transport of incoming rows into the member,
and the siting of the regrown transition).  The multiplicity and leaf factors of that
balance are assembled in `DraismaVargasCount.W3ShiftMultiplicityBalance`.
-/

namespace DraismaVargas.Count.W3ShiftIncomingDenominator

open DraismaVargas.Infrastructure
open GluingDatum TargetExpansion
open DraismaVargas.LocalCases
open W4Assembly W4StableSource StableLocalProperties FullDimensionalSource
open ThirdEquation W3ShiftSourceCandidates W3ShiftGraphData LimitChainCore
open RowWalk TrivalentWeight

variable {target : CFGraph.{0}} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {input : W3SourceInput data star} {shift : ShiftProfile input}

/-- Pull an index divisor back through a member's retained-row map. -/
theorem index_dvd_of_census {member : MemberData shift} (census : SelectedCensus member)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation member.candidate.datum coordinate)
    {path : StablePath data} {edge : data.SourceEdge} (hEdge : OnRow data path edge) :
    data.sourceEdgeIndex edge ∣ incomingRowDenominator data path := by
  by_cases hOne : data.sourceEdgeIndex edge = 1
  · rw [hOne]
    exact one_dvd _
  exact W2MkkIncomingDenominator.index_dvd_incomingRowDenominator_of_retained
    (census.graphData input.valid).toLiftData fd hEdge hOne

/-- The common terminal-transition argument, with its two local conditions
discharged below by the grow and shrink constructions. -/
theorem incomingRowDenominator_eq_of_census {member : MemberData shift}
    (census : SelectedCensus member) (hBranch : census.main = census.branch)
    (hIndex : member.candidate.datum.sourceEdgeIndex
      (member.candidate.newSourceEdge census.main) ≠ data.sourceEdgeIndex shift.moving.1)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation member.candidate.datum coordinate) :
    incomingRowDenominator data (W3ShiftHonestBalance.movingRow shift) =
      data.sourceEdgeIndex shift.moving.1 := by
  have hOld := member.moving_survives_out input.valid
  have hOldRow : OnRow member.candidate.datum
      (NonDanglingEdge.stablePath ⟨member.candidate.oldSourceEdge shift.moving.1, hOld⟩)
      (member.candidate.oldSourceEdge shift.moving.1) := ⟨hOld, rfl⟩
  have hOldIndex : member.candidate.datum.sourceEdgeIndex
      (member.candidate.oldSourceEdge shift.moving.1) =
        data.sourceEdgeIndex shift.moving.1 :=
    BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge _ _
  have hCalculus := OutgoingRowCalculus.rowCalculus_of_index_ne_one fd hOldRow
    (by rw [hOldIndex]; have := shift.two_le_moving; omega)
  have hNewRow : OnRow member.candidate.datum
      (NonDanglingEdge.stablePath ⟨member.candidate.oldSourceEdge shift.moving.1, hOld⟩)
      (member.candidate.newSourceEdge census.main) :=
    ⟨census.new_main_survives, census.new_main_stablePath input.valid⟩
  have hTransition := W2M1kTransitionSiting.transition_of_unequal_indices fd hCalculus.1
    census.old_main_valency hNewRow (member.new_incident_old census.main)
    hOld census.moving_incident_main (member.new_ne_old _ _)
    (by rw [hOldIndex]; exact hIndex)
  have hTerminal := W2M1kTransitionSiting.terminal_of_opposite_branch member.candidate
    census.main false true (by decide)
    (by rw [hBranch]; exact census.fresh_branch_valency)
  have hUpper := RowRegrowth.incomingRowDenominator_dvd_of_transport
    fd.danglingEdgeNoGlue fd.pathEnds hCalculus.1 hCalculus.2 hTransition
    census.new_main_survives (member.new_incident_old census.main)
    hOld census.moving_incident_main (Ne.symm (member.new_ne_old _ _))
    hTerminal hOldIndex
    (W2M1kRowTransport.transport (census.graphData input.valid).toLiftData
      (W3ShiftHonestBalance.movingRow shift) census.main)
  apply Nat.dvd_antisymm hUpper
  exact index_dvd_of_census census fd ⟨W3ShiftLimitRows.moving_survives shift, rfl⟩

/-- Every incoming index divides its row denominator when the grow
member is full-dimensional. -/
theorem index_dvd_of_grow
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation shift.growCandidate.datum coordinate)
    {path : StablePath data} {edge : data.SourceEdge} (hEdge : OnRow data path edge) :
    data.sourceEdgeIndex edge ∣ incomingRowDenominator data path :=
  index_dvd_of_census (Grow.census shift input.valid (branch := shift.movingAnchor) rfl)
    fd hEdge

/-- Figure 29's grow member supplies the exact incoming denominator k. -/
theorem incomingRowDenominator_of_grow
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation shift.growCandidate.datum coordinate) :
    incomingRowDenominator data (W3ShiftHonestBalance.movingRow shift) =
      data.sourceEdgeIndex shift.moving.1 := by
  apply incomingRowDenominator_eq_of_census
    (Grow.census shift input.valid (branch := shift.movingAnchor) rfl) rfl _ fd
  change W3FourStableGraph.newIndex shift.growCandidate shift.movingAnchor ≠ _
  rw [W3ShiftLimitRows.growCandidate_newIndex_moving]
  omega

/-- Every incoming index divides its row denominator when the shrink
member is full-dimensional. -/
theorem index_dvd_of_shrink (shrink : ShrinkData shift)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation shrink.shrinkCandidate.datum coordinate)
    {path : StablePath data} {edge : data.SourceEdge} (hEdge : OnRow data path edge) :
    data.sourceEdgeIndex edge ∣ incomingRowDenominator data path :=
  index_dvd_of_census (Shrink.census shrink input.valid) fd hEdge

/-- Figure 29's shrink member supplies the same exact incoming denominator k. -/
theorem incomingRowDenominator_of_shrink (shrink : ShrinkData shift)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation shrink.shrinkCandidate.datum coordinate) :
    incomingRowDenominator data (W3ShiftHonestBalance.movingRow shift) =
      data.sourceEdgeIndex shift.moving.1 := by
  apply incomingRowDenominator_eq_of_census (Shrink.census shrink input.valid) rfl _ fd
  change W3FourStableGraph.newIndex shrink.shrinkCandidate shrink.remainder ≠ _
  have := W3ShiftLimitRows.shrinkCandidate_newIndex_remainder shrink
  omega

end DraismaVargas.Count.W3ShiftIncomingDenominator

