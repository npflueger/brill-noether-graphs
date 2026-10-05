module

public import DraismaVargasCount.W2MkkIncomingDenominator
public import DraismaVargas.LocalCases.W2PGraphData

@[expose] public section

/-!
# Sharp incoming denominators from Figure 35's actual members

Figure 35 of Draisma--Vargas Part I (arXiv:1909.12924) shows the three members of case
`{w2-r2-nd3-P}`, and Equation (9) there is their balance.
Actual full dimensionality supplies all retained-row lower divisors and the
sharp incoming denominator of the row changed by each member. The first two
members have new index k+1; the third member has new index k₃-1.
The terminal-transition geometry is read from the constructed surviving stars.
These are the row-denominator inputs of Equation (9). The multiplicity balance
itself is proved in `W2PMultiplicityBalance`, which uses these receipts.
-/

namespace DraismaVargas.Count.W2PIncomingDenominator

open DraismaVargas.Infrastructure
open GluingDatum TargetExpansion
open DraismaVargas.LocalCases
open W4Assembly W4StableSource StableLocalProperties FullDimensionalSource
open SecondEquation W2R1Target W2PSourceCandidates W2PSurvival W2PGraphData LimitChainCore
open RowWalk TrivalentWeight

variable {target : CFGraph.{0}} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- Any actual Figure 35 member supplies the lower index divisor on every
incoming stable row. -/
theorem index_dvd_incomingRowDenominator (input : W2SourceInput data star)
    (member : MemberShape profile)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation member.candidate.datum coordinate)
    {path : StablePath data} {edge : data.SourceEdge} (hEdge : OnRow data path edge) :
    data.sourceEdgeIndex edge ∣ incomingRowDenominator data path := by
  by_cases hOne : data.sourceEdgeIndex edge = 1
  · rw [hOne]
    exact one_dvd _
  exact W2MkkIncomingDenominator.index_dvd_incomingRowDenominator_of_retained
    (W2PStableLift.liftData input member) fd hEdge hOne

/-- The merged block's new index really is its retained index plus one. -/
theorem merge_new_index (shape : Shape profile) (m : MergeInput profile) :
    m.member.candidate.datum.sourceEdgeIndex
      (m.member.candidate.newSourceEdge m.own.1.1.2) =
        data.sourceEdgeIndex m.own.1 + 1 := by
  rw [m.member.newSourceEdge_index_of_rel _ m.own_rel]
  change ((endpointPartition profile).mergeBlocks m.own.1.1.2
    (extraSheet profile) m.own_extra).blockCard m.own.1.1.2 = _
  rw [SheetPartition.mergeBlocks_blockCard_first_of_singleton _ _ _ _
    (extraSheet_block shape)]
  congr 1
  change (data.edgePartition (star.edge profile.doubleLabel)).blockCard m.own.1.1.2 = _
  rw [← m.own_target]
  rfl

/-- The sharp receipt for either merging member, with its own retained row. -/
theorem incomingRowDenominator_merge (input : W2SourceInput data star)
    (shape : Shape profile) (m : MergeInput profile)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation m.member.candidate.datum coordinate) :
    incomingRowDenominator data
      (NonDanglingEdge.stablePath ⟨m.own.1, m.own_survives⟩) =
        data.sourceEdgeIndex m.own.1 := by
  classical
  have hOld := m.member.retained_survives input ⟨m.own.1, m.own_survives⟩
  have hNew := m.new_own_survives shape input
  have hNewRow : OnRow m.member.candidate.datum
      (NonDanglingEdge.stablePath ⟨m.member.candidate.oldSourceEdge m.own.1, hOld⟩)
      (m.member.candidate.newSourceEdge m.own.1.1.2) :=
    ⟨hNew, m.new_own_row shape input⟩
  have hOldIndex : m.member.candidate.datum.sourceEdgeIndex
      (m.member.candidate.oldSourceEdge m.own.1) = data.sourceEdgeIndex m.own.1 :=
    BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge _ _
  have hCalculus := OutgoingRowCalculus.rowCalculus_of_index_ne_one fd hNewRow
    (by rw [merge_new_index shape]; have := data.sourceEdgeIndex_pos m.own.1; omega)
  have hValency : nonDanglingValency m.member.candidate.datum
      (m.member.candidate.datum.sourceEndpoint (oldVertex target wall) m.own.1.1.2) = 2 := by
    rw [← card_nonDanglingIncident, m.old_own_star shape input]
    exact Finset.card_pair (Ne.symm (oldSourceEdge_ne_newSourceEdge _ _))
  have hNewIncident := newSourceEdge_incident_old
    (candidate := m.member.candidate) m.own.1.1.2
  have hNe := oldSourceEdge_ne_newSourceEdge
    (candidate := m.member.candidate) m.own.1 m.own.1.1.2
  have hTransition := W2M1kTransitionSiting.transition_of_unequal_indices fd hCalculus.1
    hValency hNewRow hNewIncident hOld m.own_incident (Ne.symm hNe)
    (by rw [merge_new_index shape, hOldIndex]; omega)
  have hFresh : nonDanglingValency m.member.candidate.datum
      (m.member.candidate.datum.sourceEndpoint (freshVertex target) m.own.1.1.2) = 3 := by
    rw [← m.member.sourceEndpoint_fresh_eq_of_rel block.1 m.own.1.1.2 m.own_rel]
    exact m.fresh_valency shape input
  have hUpper := RowRegrowth.incomingRowDenominator_dvd_of_transport
    fd.danglingEdgeNoGlue fd.pathEnds hCalculus.1 hCalculus.2 hTransition
    hNew hNewIncident hOld m.own_incident hNe
    (W2M1kTransitionSiting.terminal_of_opposite_branch m.member.candidate
      m.own.1.1.2 false true (by decide) hFresh)
    hOldIndex
    (W2M1kRowTransport.transport (W2PStableLift.liftData input m.member)
      (NonDanglingEdge.stablePath ⟨m.own.1, m.own_survives⟩) m.own.1.1.2)
  exact Nat.dvd_antisymm hUpper
    (index_dvd_incomingRowDenominator input m.member fd ⟨m.own_survives, rfl⟩)

/-- The actual first member gives d(e₁'s incoming row)=k₁. -/
theorem incomingRowDenominator_first (input : W2SourceInput data star)
    (shape : Shape profile)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation (firstMember shape).datum coordinate) :
    incomingRowDenominator data
      (NonDanglingEdge.stablePath ⟨profile.first.1, profile.first_survives⟩) =
        data.sourceEdgeIndex profile.first.1 :=
  incomingRowDenominator_merge input shape (firstMergeInput shape) fd

/-- The actual second member gives d(e₂'s incoming row)=k₂. -/
theorem incomingRowDenominator_second (input : W2SourceInput data star)
    (shape : Shape profile)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation (secondMember shape).datum coordinate) :
    incomingRowDenominator data
      (NonDanglingEdge.stablePath ⟨profile.second.1, profile.second_survives⟩) =
        data.sourceEdgeIndex profile.second.1 :=
  incomingRowDenominator_merge input shape (secondMergeInput shape) fd

/-- The third member's surviving new index is k₃-1. -/
theorem third_new_index (shape : Shape profile) :
    (thirdMember shape).datum.sourceEdgeIndex
      ((thirdMember shape).newSourceEdge (firstSheet profile)) + 1 =
        data.sourceEdgeIndex profile.third.1 := by
  have hNew := (thirdShape shape).newSourceEdge_index_of_rel
    (firstSheet profile) (firstSheet_rel profile)
  have hCard := (thirdMember_indices shape).1
  change (thirdShape shape).fine.blockCard (firstSheet profile) =
    data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 at hCard
  change (thirdShape shape).candidate.datum.sourceEdgeIndex
    ((thirdShape shape).candidate.newSourceEdge (firstSheet profile)) + 1 = _
  rw [hNew, hCard, shape.third_index]

/-- The actual third member gives d(e₃'s incoming row)=k₃. -/
theorem incomingRowDenominator_third (input : W2SourceInput data star)
    (shape : Shape profile)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation (thirdMember shape).datum coordinate) :
    incomingRowDenominator data
      (NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩) =
        data.sourceEdgeIndex profile.third.1 := by
  classical
  let member := thirdShape shape
  change FullDimensionalSourcePresentation member.candidate.datum coordinate at fd
  have hOld := member.retained_survives input ⟨profile.third.1, profile.third_survives⟩
  have hNew := thirdShape_new_first_survives shape input
  have hOldRow : OnRow member.candidate.datum
      (NonDanglingEdge.stablePath ⟨member.candidate.oldSourceEdge profile.third.1, hOld⟩)
      (member.candidate.oldSourceEdge profile.third.1) := ⟨hOld, rfl⟩
  have hOldIndex : member.candidate.datum.sourceEdgeIndex
      (member.candidate.oldSourceEdge profile.third.1) = data.sourceEdgeIndex profile.third.1 :=
    BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge _ _
  have hCalculus := OutgoingRowCalculus.rowCalculus_of_index_ne_one fd hOldRow
    (by
      rw [hOldIndex, shape.third_index]
      have := data.sourceEdgeIndex_pos profile.first.1
      have := data.sourceEdgeIndex_pos profile.second.1
      omega)
  have hNewRow : OnRow member.candidate.datum
      (NonDanglingEdge.stablePath ⟨member.candidate.oldSourceEdge profile.third.1, hOld⟩)
      (member.candidate.newSourceEdge (firstSheet profile)) :=
    ⟨hNew, Third.new_first_row shape input⟩
  have hValency : nonDanglingValency member.candidate.datum
      (member.candidate.datum.sourceEndpoint (freshVertex target) (firstSheet profile)) = 2 := by
    rw [← card_nonDanglingIncident, Third.fresh_star shape input _ (firstSheet_rel profile)]
    exact Finset.card_pair (Ne.symm (oldSourceEdge_ne_newSourceEdge _ _))
  have hNewIncident := newSourceEdge_incident_fresh
    (candidate := member.candidate) (firstSheet profile)
  have hOldIncident := Third.third_incident shape (firstSheet profile) (firstSheet_rel profile)
  have hNe := oldSourceEdge_ne_newSourceEdge
    (candidate := member.candidate) profile.third.1 (firstSheet profile)
  have hTransition := W2M1kTransitionSiting.transition_of_unequal_indices fd hCalculus.1
    hValency hNewRow hNewIncident hOld hOldIncident (Ne.symm hNe)
    (by
      rw [hOldIndex]
      have := third_new_index shape
      change (thirdMember shape).datum.sourceEdgeIndex
        ((thirdMember shape).newSourceEdge (firstSheet profile)) ≠ _
      omega)
  have hUpper := RowRegrowth.incomingRowDenominator_dvd_of_transport
    fd.danglingEdgeNoGlue fd.pathEnds hCalculus.1 hCalculus.2 hTransition
    hNew hNewIncident hOld hOldIncident hNe
    (W2M1kTransitionSiting.terminal_of_opposite_branch member.candidate
      (firstSheet profile) true false (by decide) (Third.old_valency shape input))
    hOldIndex
    (W2M1kRowTransport.transport (W2PStableLift.liftData input member)
      (NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩)
      (firstSheet profile))
  exact Nat.dvd_antisymm hUpper
    (index_dvd_incomingRowDenominator input member fd ⟨profile.third_survives, rfl⟩)

end DraismaVargas.Count.W2PIncomingDenominator
