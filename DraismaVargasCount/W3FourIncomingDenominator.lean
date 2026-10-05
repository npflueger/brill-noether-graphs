module

public import DraismaVargasCount.W2MkkIncomingDenominator
public import DraismaVargas.LocalCases.W3FourRowDescent

@[expose] public section

/-!
# Sharp incoming denominators from Figure 28's grow members

For either actual grow member M3/M4 of Equation (2), full dimensionality
forces the incoming grow row to have denominator exactly its retained index.
The new occurrence has index k+1 and joins the old k occurrence at a divalent
endpoint; its other endpoint is trivalent. Thus the new occurrence supplies
the row calculus even when k=1, and the terminal-transition theorem supplies
the upper bound. The retained-row injection supplies the lower bound.

These are sharp incoming-row denominators for an actual case (Draisma--Vargas Part I,
arXiv:1909.12924, Figure 28 and Equation (2)).  Their consumer is the Equation (2) balance
`W3FourCountBalance.exists_sum_signedMult_eq_zero`, which combines these grow
receipts with the reversed-member receipts and the four-member weight/leaf
assembly.
-/

namespace DraismaVargas.Count.W3FourIncomingDenominator

open DraismaVargas.Infrastructure
open GluingDatum TargetExpansion
open DraismaVargas.LocalCases
open W4Assembly W4StableSource StableLocalProperties FullDimensionalSource
open ThirdEquation W3FourSourceCandidates W3FourSurvival LimitChainCore
open RowWalk TrivalentWeight

variable {target : CFGraph.{0}} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {input : W3SourceInput data star}

/-- The retained grow occurrence as a genuine surviving incoming edge. -/
noncomputable def growEdge (grown : GrowProfile input) : NonDanglingEdge data :=
  ⟨data.sourceEdge grown.growTarget grown.growAnchor,
    (SelectedSurvival.ofGrowProfile grown).grow_survives⟩

/-- The quotient representative has the profile's own dilation index. -/
theorem growEdge_index (grown : GrowProfile input) :
    data.sourceEdgeIndex (growEdge grown).1 = data.sourceEdgeIndex grown.grow.1 := by
  change data.sourceEdgeIndex (data.sourceEdge grown.growTarget grown.growAnchor) = _
  rw [GluingDatum.sourceEdge_self]

/-- The new selected occurrence has index k+1. -/
theorem new_grow_index (grown : GrowProfile input) :
    grown.growCandidate.datum.sourceEdgeIndex
      (grown.growCandidate.newSourceEdge grown.growAnchor) =
        data.sourceEdgeIndex grown.grow.1 + 1 := by
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge]
  change (GrowMember.pasted grown).newEdge.blockCard grown.growAnchor = _
  unfold SheetPartition.blockCard
  rw [GrowMember.pasted_newEdge_block grown rfl]
  exact grown.growPartition_blockCard_growAnchor

/-- A nonsingular grow member gives every incoming index its lower divisor
bound, on arbitrary rows of the incoming datum. -/
theorem index_dvd_incomingRowDenominator (grown : GrowProfile input)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation grown.growCandidate.datum coordinate)
    {path : StablePath data} {edge : data.SourceEdge} (hEdge : OnRow data path edge) :
    data.sourceEdgeIndex edge ∣ incomingRowDenominator data path := by
  by_cases hOne : data.sourceEdgeIndex edge = 1
  · rw [hOne]
    exact one_dvd _
  exact W2MkkIncomingDenominator.index_dvd_incomingRowDenominator_of_retained
    (W3FourRowDescent.GrowMember.rowData grown (SelectedSurvival.ofGrowProfile grown)
      input.valid).toLiftData fd hEdge hOne

/-- The exact incoming grow-row denominator, with all transport, transition
and terminal-site receipts proved for the actual Figure 28 candidate. -/
theorem incomingRowDenominator_grow_eq (grown : GrowProfile input)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation grown.growCandidate.datum coordinate) :
    incomingRowDenominator data (growEdge grown).stablePath = data.sourceEdgeIndex grown.grow.1 := by
  let survival := SelectedSurvival.ofGrowProfile grown
  have hNew := GrowMember.new_grow_survives grown survival input.valid
  have hPartner := GrowMember.grow_survives_out grown survival input.valid
  have hNewRow : OnRow grown.growCandidate.datum
      (NonDanglingEdge.stablePath ⟨grown.growCandidate.oldSourceEdge (growEdge grown).1, hPartner⟩)
      (grown.growCandidate.newSourceEdge grown.growAnchor) :=
    ⟨hNew, GrowMember.new_grow_stablePath grown survival input.valid⟩
  have hPartnerIndex : grown.growCandidate.datum.sourceEdgeIndex
      (grown.growCandidate.oldSourceEdge (growEdge grown).1) = data.sourceEdgeIndex grown.grow.1 := by
    rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge, growEdge_index]
  have hCalculus := OutgoingRowCalculus.rowCalculus_of_index_ne_one fd hNewRow
    (by rw [new_grow_index]; have := data.sourceEdgeIndex_pos grown.grow.1; omega)
  have hPartnerIncident := GrowMember.grow_incident_old grown grown.growAnchor
  have hNewIncident := GrowMember.new_incident_old grown grown.growAnchor
  have hNe := oldSourceEdge_ne_newSourceEdge
    (candidate := grown.growCandidate) (growEdge grown).1 grown.growAnchor
  have hTransition := W2M1kTransitionSiting.transition_of_unequal_indices fd hCalculus.1
    (GrowMember.old_grow_nonDanglingValency_eq_two grown survival input.valid)
    hNewRow hNewIncident hPartner hPartnerIncident (Ne.symm hNe)
    (by
      change grown.growCandidate.datum.sourceEdgeIndex
          (grown.growCandidate.newSourceEdge grown.growAnchor) ≠
        grown.growCandidate.datum.sourceEdgeIndex
          (grown.growCandidate.oldSourceEdge (growEdge grown).1)
      rw [new_grow_index, hPartnerIndex]
      omega)
  have hUpper := RowRegrowth.incomingRowDenominator_dvd_of_transport
    fd.danglingEdgeNoGlue fd.pathEnds hCalculus.1 hCalculus.2 hTransition
    hNew hNewIncident hPartner hPartnerIncident hNe
    (W2M1kTransitionSiting.terminal_of_opposite_branch grown.growCandidate
      grown.growAnchor false true (by decide)
      (GrowMember.fresh_nonDanglingValency_eq_three grown survival input.valid))
    hPartnerIndex
    (W2M1kRowTransport.transport
      (W3FourRowDescent.GrowMember.rowData grown survival input.valid).toLiftData
      (growEdge grown).stablePath grown.growAnchor)
  apply Nat.dvd_antisymm hUpper
  rw [← growEdge_index grown]
  exact index_dvd_incomingRowDenominator grown fd ⟨(growEdge grown).2, rfl⟩

/-- The sharp receipt for Figure 28's actual third member. -/
theorem incomingRowDenominator_thirdMember
    (profile : W3R1SourceProfile.Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : data.sourceEdgeIndex profile.largest.1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation
      (thirdCandidate profile directions largest_index).datum coordinate) :
    incomingRowDenominator data
      (growEdge (growProfileFirst profile directions largest_index)).stablePath =
        data.sourceEdgeIndex profile.first.1 :=
  incomingRowDenominator_grow_eq (growProfileFirst profile directions largest_index) fd

/-- The sharp receipt for Figure 28's actual fourth member. -/
theorem incomingRowDenominator_fourthMember
    (profile : W3R1SourceProfile.Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : data.sourceEdgeIndex profile.largest.1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation
      (fourthCandidate profile directions largest_index).datum coordinate) :
    incomingRowDenominator data
      (growEdge (growProfileSecond profile directions largest_index)).stablePath =
        data.sourceEdgeIndex profile.second.1 :=
  incomingRowDenominator_grow_eq (growProfileSecond profile directions largest_index) fd

end DraismaVargas.Count.W3FourIncomingDenominator
