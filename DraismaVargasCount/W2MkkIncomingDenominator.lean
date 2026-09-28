import DraismaVargasCount.W2M1kTransitionSiting
import DraismaVargas.LocalCases.W2MkkStableIncidence
import DraismaVargasCount.W2MkkClosure
import DraismaVargasCount.W2MkkMultiplicityBalance

/-!
# Sharp incoming row denominators from the M-kk members

Source: Draisma--Vargas Part I (arXiv:1909.12924), case `{w2-r2-nd3-M-kk}`, Figure 34 and
Equation (8).  The lower denominator bound is pulled back from the nonsingular member's
simple target columns through its retained-occurrence injection.  This needs
no incoming-row tameness or pairwise distinctness assumption.
-/

namespace DraismaVargas.Count.W2MkkIncomingDenominator

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open W4Assembly W4StableSource W2R1Target SecondEquation StableSourceMatrix
open StableLocalProperties FullDimensionalSource LimitChainCore
open W2MkkSourceCandidates W2MkkStableGraph W2MkkStableLift
open TrivalentWeight RowWalk

variable {target : CFGraph.{0}} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}

/-- A retained row inherits target injectivity from its member row. -/
theorem rowTargetInjective_of_retained (lift : LiftData data wall)
    {path : StablePath data}
    (hMember : RowTargetInjective lift.candidate.datum (lift.stablePathLift path)) :
    RowTargetInjective data path := by
  intro first second hFirst hSecond hTarget
  apply ResolutionCut.oldSourceEdge_injective lift.candidate
  apply hMember _ _ (W2M1kRowTransport.onRow_oldSourceEdge lift hFirst)
    (W2M1kRowTransport.onRow_oldSourceEdge lift hSecond)
  exact congrArg (fun place ↦ occurrenceEquiv target wall lift.candidate.right (some place)) hTarget

/-- A ramified incoming occurrence supplies the member row calculus and hence
the simple-column lower denominator bound on its own incoming row. -/
theorem index_dvd_incomingRowDenominator_of_retained (lift : LiftData data wall)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation lift.candidate.datum coordinate)
    {path : StablePath data} {edge : data.SourceEdge}
    (hEdge : OnRow data path edge) (hIndex : data.sourceEdgeIndex edge ≠ 1) :
    data.sourceEdgeIndex edge ∣ incomingRowDenominator data path := by
  have hImage := W2M1kRowTransport.onRow_oldSourceEdge lift hEdge
  have hTame := OutgoingRowCalculus.rowRamificationAtMostOne_of_index_ne_one fd hImage
    (by rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge]; exact hIndex)
  have hInjective := rowTargetInjective_of_retained lift
    (RowGeodesic.rowTargetInjective_of_genusZero fd.targetConnected fd.targetGenus
      fd.danglingEdgeNoGlue fd.pathEnds hTame)
  exact dvd_incomingRowDenominator_of_occurrences_eq_singleton path edge.1.1
    (occurrences_eq_singleton_of_rowTargetInjective hInjective hEdge rfl)

variable {star : TwoStar target wall} {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- The incoming occurrence whose block is shortened by a detachment. -/
noncomputable def detachIncomingEdge (shape : Shape profile) (detach : DetachData profile) :
    NonDanglingEdge data :=
  ⟨data.sourceEdge (star.edge profile.doubleLabel) detach.remainder,
    double_sourceEdge_survives_shape shape detach.remainder
      ((pinSheet_rel profile).trans detach.wallTogether)⟩

/-- Its incoming index is the cardinality of the pinned endpoint block. -/
theorem detachIncomingEdge_index (shape : Shape profile) (detach : DetachData profile) :
    data.sourceEdgeIndex (detachIncomingEdge shape detach).1 =
      (endpointPartition profile).blockCard (pinSheet profile) := by
  change data.sourceEdgeIndex (data.sourceEdge (star.edge profile.doubleLabel) detach.remainder) = _
  rw [GluingDatum.sourceEdgeIndex_sourceEdge]
  exact (SheetPartition.blockCard_congr _ detach.together).symm

/-- The detaching member gives the sharp incoming denominator on the row it
perturbs, independently of which labelled survivor carries the pinned sheet. -/
theorem incomingRowDenominator_detach_eq (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation (detach.candidate shape).datum coordinate) :
    incomingRowDenominator data (detachIncomingEdge shape detach).stablePath =
      (endpointPartition profile).blockCard (pinSheet profile) := by
  let old := detachIncomingEdge shape detach
  have hNePin : detach.remainder ≠ pinSheet profile := Ne.symm detach.ne_remainder
  have hPartner : ¬ IsDangling (detach.candidate shape).datum
      ((detach.candidate shape).oldSourceEdge old.1) :=
    ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ old.2
  have hPartnerIncident := detach_double_incident shape detach detach.remainder
  have hNewIncident := newSourceEdge_incident_old (candidate := detach.candidate shape)
    detach.remainder
  have hNew := detach_new_survives input shape detach detach.remainder detach.wallTogether hNePin
  have hNe := oldSourceEdge_ne_newSourceEdge
    (candidate := detach.candidate shape) old.1 detach.remainder
  have hPartnerRow : OnRow (detach.candidate shape).datum
      (NonDanglingEdge.stablePath ⟨(detach.candidate shape).oldSourceEdge old.1, hPartner⟩)
      ((detach.candidate shape).oldSourceEdge old.1) := ⟨hPartner, rfl⟩
  have hIndex : (detach.candidate shape).datum.sourceEdgeIndex
      ((detach.candidate shape).oldSourceEdge old.1) =
        (endpointPartition profile).blockCard (pinSheet profile) := by
    rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge]
    exact detachIncomingEdge_index shape detach
  have hIndexNe : (endpointPartition profile).blockCard (pinSheet profile) ≠ 1 :=
    ne_of_gt (one_lt_pinSheet_endpoint_blockCard shape)
  have hCalculus := OutgoingRowCalculus.rowCalculus_of_index_ne_one fd hPartnerRow
    (by rw [hIndex]; exact hIndexNe)
  have hTransition := W2M1kTransitionSiting.transition_of_unequal_indices fd hCalculus.1
    (detach_nonDanglingValency_old input shape detach detach.remainder detach.wallTogether hNePin)
    hPartnerRow hPartnerIncident hNew hNewIncident hNe (by
      rw [hIndex, W2MkkLimitMatrix.detach_newSourceEdge_index shape detach
        detach.remainder detach.wallTogether]
      have := W2MkkCommonBalance.detach_weight_eq profile shape detach
      omega)
  have hUpper := RowRegrowth.incomingRowDenominator_dvd_of_transport
    fd.danglingEdgeNoGlue fd.pathEnds hCalculus.1 hCalculus.2 hTransition
    hNew hNewIncident hPartner hPartnerIncident hNe
    (W2M1kTransitionSiting.terminal_of_opposite_branch (detach.candidate shape)
      detach.remainder false true (by decide)
      (detach_nonDanglingValency_fresh input shape detach detach.remainder detach.wallTogether hNePin))
    hIndex (W2M1kRowTransport.transport (detachLiftData input shape detach) old.stablePath
      detach.remainder)
  apply Nat.dvd_antisymm hUpper
  rw [← detachIncomingEdge_index shape detach]
  exact index_dvd_incomingRowDenominator_of_retained (detachLiftData input shape detach)
    fd ⟨old.2, rfl⟩ (by rw [detachIncomingEdge_index shape detach]; exact hIndexNe)

/-- The joined member forces the incoming third row's exact denominator. -/
theorem incomingRowDenominator_third_eq (input : W2SourceInput data star)
    (shape : Shape profile) (distinguished : Fin degree)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation (joinedCandidate profile distinguished).datum coordinate) :
    incomingRowDenominator data
      (NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩) =
        data.sourceEdgeIndex profile.third.1 := by
  have hRel : (data.vertexPartition wall).Rel block.1 block.1 := rfl
  have hThirdRel : (data.vertexPartition wall).Rel (thirdSheet profile) block.1 :=
    (thirdSheet_rel profile).symm
  have hPartnerIncident := joined_fresh_vertex_eq profile distinguished
    (thirdSheet profile) block.1 hThirdRel ▸
      joined_single_incident profile distinguished profile.third.1 profile.third_target
  have hNewIncident := newSourceEdge_incident_fresh
    (candidate := joinedCandidate profile distinguished) block.1
  have hPartner := ResolutionSurvival.not_isDangling_oldSourceEdge
    (joinedCandidate profile distinguished) input.valid.1 _ profile.third_survives
  have hNew := joined_new_survives input shape distinguished block.1 hRel
  have hNe := oldSourceEdge_ne_newSourceEdge
    (candidate := joinedCandidate profile distinguished) profile.third.1 block.1
  have hPartnerRow : OnRow (joinedCandidate profile distinguished).datum
      (NonDanglingEdge.stablePath
        ⟨(joinedCandidate profile distinguished).oldSourceEdge profile.third.1, hPartner⟩)
      ((joinedCandidate profile distinguished).oldSourceEdge profile.third.1) := ⟨hPartner, rfl⟩
  have hThirdNeOne : data.sourceEdgeIndex profile.third.1 ≠ 1 := by
    have := shape.third_index
    have := shape.one_lt_first
    have := shape.one_lt_second
    omega
  have hCalculus := OutgoingRowCalculus.rowCalculus_of_index_ne_one fd hPartnerRow
    (by rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge]; exact hThirdNeOne)
  have hTransition := W2M1kTransitionSiting.transition_of_unequal_indices fd hCalculus.1
    (joined_nonDanglingValency_fresh input shape distinguished block.1 hRel)
    hPartnerRow hPartnerIncident hNew hNewIncident hNe (by
      rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge,
        W2MkkLimitMatrix.joined_newSourceEdge_index profile distinguished block.1]
      rw [blockCard_of_rel shape block.1 hRel]
      have := shape.third_index
      omega)
  have hUpper := RowRegrowth.incomingRowDenominator_dvd_of_transport
    fd.danglingEdgeNoGlue fd.pathEnds hCalculus.1 hCalculus.2 hTransition
    hNew hNewIncident hPartner hPartnerIncident hNe
    (W2M1kTransitionSiting.terminal_of_opposite_branch
      (joinedCandidate profile distinguished) block.1 true false (by decide)
      (joined_nonDanglingValency_old input shape distinguished block.1 hRel))
    (BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge _ profile.third.1)
    (W2M1kRowTransport.transport (joinedLiftData input profile distinguished)
      (NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩) block.1)
  exact Nat.dvd_antisymm hUpper
    (index_dvd_incomingRowDenominator_of_retained (joinedLiftData input profile distinguished)
      fd ⟨profile.third_survives, rfl⟩ hThirdNeOne)

open W2MkkCommonBalance W2MkkLimitColumns W2MkkTransport

/-- Local first detachment sharpens the first incoming row. -/
theorem incomingRowDenominator_first_eq (input : W2SourceInput data star)
    (shape : Shape profile) (member : FirstMember profile)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation (member.toDetachData.candidate shape).datum coordinate) :
    incomingRowDenominator data (firstRow profile) = data.sourceEdgeIndex profile.first.1 := by
  have hEdge : detachIncomingEdge shape member.toDetachData =
      (⟨profile.first.1, profile.first_survives⟩ : NonDanglingEdge data) := by
    apply Subtype.ext
    exact (W2MkkLimitMatrix.sourceEdge_double_congr profile
      (member.pin_first.trans member.together).symm).trans
      (W2MkkLimitMatrix.sourceEdge_double_first profile)
  have h := incomingRowDenominator_detach_eq input shape member.toDetachData fd
  rw [hEdge, ← SheetPartition.blockCard_congr _ member.pin_first,
    endpointPartition_blockCard_first] at h
  exact h

/-- Local second detachment sharpens the second incoming row. -/
theorem incomingRowDenominator_second_eq (input : W2SourceInput data star)
    (shape : Shape profile) (member : SecondMember profile)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation (member.toDetachData.candidate shape).datum coordinate) :
    incomingRowDenominator data (secondRow profile) = data.sourceEdgeIndex profile.second.1 := by
  have hEdge : detachIncomingEdge shape member.toDetachData =
      (⟨profile.second.1, profile.second_survives⟩ : NonDanglingEdge data) := by
    apply Subtype.ext
    exact (W2MkkLimitMatrix.sourceEdge_double_congr profile
      (member.pin_second.trans member.together).symm).trans
      (W2MkkLimitMatrix.sourceEdge_double_second profile)
  have h := incomingRowDenominator_detach_eq input shape member.toDetachData fd
  rw [hEdge, ← SheetPartition.blockCard_congr _ member.pin_second,
    endpointPartition_blockCard_second] at h
  exact h

/-- Sheet relabelling leaves the complete incoming row denominator unchanged. -/
theorem incomingRowDenominator_gauge {base : GluingDatum target degree}
    (gauge : Gauge data base wall) (path : StablePath data) :
    incomingRowDenominator base (gauge.row path) = incomingRowDenominator data path := by
  unfold incomingRowDenominator
  congr 1
  exact funext (gauge.matrix_gauge path)

/-- The first remote detachment sharpens the original first row. -/
theorem incomingRowDenominator_remoteFirst_eq (input : W2SourceInput data star)
    (shape : Shape profile) (hConnected : graph_connected target) (hGenus : genus target = 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation (remoteFirstMember input shape).datum coordinate) :
    incomingRowDenominator data (firstRow profile) = data.sourceEdgeIndex profile.first.1 := by
  have h := incomingRowDenominator_first_eq
    (swapInput input (firstSheet profile) (firstSheet_together profile))
    (swapShape shape input.valid.1 (firstSheet profile) (firstSheet_together profile))
    ⟨remoteDetach input shape (firstSheet profile) (firstSheet_together profile),
      swapProfile_pin_first shape hConnected hGenus input.valid.1⟩ fd
  change incomingRowDenominator _ (W2MkkLimitMatrix.firstRow _) = _ at h
  rw [swapProfile_firstRow, incomingRowDenominator_gauge, swapProfile_first_index] at h
  exact h

/-- The second remote detachment sharpens the original second row. -/
theorem incomingRowDenominator_remoteSecond_eq (input : W2SourceInput data star)
    (shape : Shape profile) (hConnected : graph_connected target) (hGenus : genus target = 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation (remoteSecondMember input shape).datum coordinate) :
    incomingRowDenominator data (secondRow profile) = data.sourceEdgeIndex profile.second.1 := by
  have h := incomingRowDenominator_second_eq
    (swapInput input (secondSheet profile) (secondSheet_together profile))
    (swapShape shape input.valid.1 (secondSheet profile) (secondSheet_together profile))
    ⟨remoteDetach input shape (secondSheet profile) (secondSheet_together profile),
      swapProfile_pin_second shape hConnected hGenus input.valid.1⟩ fd
  change incomingRowDenominator _ (W2MkkLimitMatrix.secondRow _) = _ at h
  rw [swapProfile_secondRow, incomingRowDenominator_gauge, swapProfile_second_index] at h
  exact h

/-- Each actual family member has the incoming stable graph, including the
remotely relabelled detachment. -/
noncomputable def limitDictionary (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (distinguished : Fin degree)
    (hConnected : graph_connected target) (hGenus : genus target = 0) (position : Fin 3) :
    StableGraphIncidence.Equivalence data
      ((limitColumns input shape detach distinguished hConnected hGenus).member position).datum := by
  classical
  by_cases hPin : (endpointPartition profile).Rel (firstSheet profile) (pinSheet profile)
  · exact cast (congrArg (fun limit : LimitColumns profile shape ↦
      StableGraphIncidence.Equivalence data (limit.member position).datum)
      (limitColumns_eq_firstOrientation input shape detach distinguished hConnected hGenus hPin)).symm
      (W2MkkArbitraryExit.firstOrientationDictionary input shape distinguished hConnected hGenus
        ⟨detach, hPin⟩ (W2MkkClosure.remoteEquivalence profile input.valid.1
          (secondSheet profile) (secondSheet_together profile)) position)
  · exact cast (congrArg (fun limit : LimitColumns profile shape ↦
      StableGraphIncidence.Equivalence data (limit.member position).datum)
      (limitColumns_eq_secondOrientation input shape detach distinguished hConnected hGenus hPin
        ((pinSheet_mem shape).resolve_left hPin))).symm
      (W2MkkArbitraryExit.secondOrientationDictionary input shape distinguished hConnected hGenus
        ⟨detach, (pinSheet_mem shape).resolve_left hPin⟩
        (W2MkkClosure.remoteEquivalence profile input.valid.1
          (firstSheet profile) (firstSheet_together profile)) position)

/-- Source genus is unchanged at every actual family position. -/
theorem limitMemberGenus (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (distinguished : Fin degree)
    (hConnected : graph_connected target) (hGenus : genus target = 0) (position : Fin 3) :
    genus ((limitColumns input shape detach distinguished hConnected hGenus).member position).datum.sourceGraph =
      genus data.sourceGraph := by
  classical
  by_cases hPin : (endpointPartition profile).Rel (firstSheet profile) (pinSheet profile)
  · rw [limitColumns_eq_firstOrientation input shape detach distinguished hConnected hGenus hPin]
    exact W2MkkArbitraryExit.firstOrientationSourceGenus input shape distinguished hConnected hGenus
      ⟨detach, hPin⟩ (W2MkkClosure.remote_sourceGenus profile
        (secondSheet profile) (secondSheet_together profile)) position
  · rw [limitColumns_eq_secondOrientation input shape detach distinguished hConnected hGenus hPin
      ((pinSheet_mem shape).resolve_left hPin)]
    exact W2MkkArbitraryExit.secondOrientationSourceGenus input shape distinguished hConnected hGenus
      ⟨detach, (pinSheet_mem shape).resolve_left hPin⟩ (W2MkkClosure.remote_sourceGenus profile
        (firstSheet profile) (firstSheet_together profile)) position

/-- A nonzero determinant supplies the actual member's full-dimensional
presentation from the incoming chart, in arbitrary coordinates. -/
noncomputable def memberPresentation (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (distinguished : Fin degree)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming outgoing : Fin 3)
    (initial : StableLengthMatrixLabelling
      ((limitColumns input shape detach distinguished hConnected hGenus).member 0).datum coordinate)
    (incomingFD : FullDimensionalSourcePresentation
      ((limitColumns input shape detach distinguished hConnected hGenus).member incoming).datum coordinate)
    (hDet : ((limitColumns input shape detach distinguished hConnected hGenus).squareMatrix
      initial outgoing).det ≠ 0) :
    FullDimensionalSourcePresentation
      ((limitColumns input shape detach distinguished hConnected hGenus).member outgoing).datum coordinate :=
  W2MkkStableIncidence.presentationAt _ incoming outgoing
    ((limitDictionary input shape detach distinguished hConnected hGenus incoming).symm.trans
      (limitDictionary input shape detach distinguished hConnected hGenus outgoing))
    input.valid hConnected hGenus
    (limitMemberGenus input shape detach distinguished hConnected hGenus incoming)
    (limitMemberGenus input shape detach distinguished hConnected hGenus outgoing)
    initial incomingFD hDet

/-- Every full-dimensional member forces precisely the sharp denominator
needed by its own multiplicity term. No relation between the three rows is assumed. -/
theorem incomingRowDenominator_member_eq (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile) (distinguished : Fin degree)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (position : Fin 3)
    (fd : FullDimensionalSourcePresentation
      ((limitColumns input shape detach distinguished hConnected hGenus).member position).datum coordinate) :
    incomingRowDenominator data (W2MkkMultiplicityBalance.affectedRow profile position) =
      W2MkkMultiplicityBalance.incomingIndex profile position := by
  classical
  by_cases hPin : (endpointPartition profile).Rel (firstSheet profile) (pinSheet profile)
  · rw [limitColumns_eq_firstOrientation input shape detach distinguished hConnected hGenus hPin] at fd
    fin_cases position
    · exact incomingRowDenominator_first_eq input shape ⟨detach, hPin⟩ fd
    · exact incomingRowDenominator_remoteSecond_eq input shape hConnected hGenus fd
    · exact incomingRowDenominator_third_eq input shape distinguished fd
  · rw [limitColumns_eq_secondOrientation input shape detach distinguished hConnected hGenus hPin
      ((pinSheet_mem shape).resolve_left hPin)] at fd
    fin_cases position
    · exact incomingRowDenominator_remoteFirst_eq input shape hConnected hGenus fd
    · exact incomingRowDenominator_second_eq input shape
        ⟨detach, (pinSheet_mem shape).resolve_left hPin⟩ fd
    · exact incomingRowDenominator_third_eq input shape distinguished fd

/-- Equation (8), including the paper's denominator and target-leaf weights,
from the actual incoming full-dimensional chart in arbitrary coordinates. -/
theorem sum_signedMult_eq_zero (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (distinguished : Fin degree)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : Fin 3)
    (initial : StableLengthMatrixLabelling
      ((limitColumns input shape detach distinguished hConnected hGenus).member 0).datum coordinate)
    (incomingFD : FullDimensionalSourcePresentation
      ((limitColumns input shape detach distinguished hConnected hGenus).member incoming).datum coordinate) :
    ∑ position : Fin 3, signedMult
      ((limitColumns input shape detach distinguished hConnected hGenus).labelling
        initial position).presentation = 0 := by
  apply W2MkkMultiplicityBalance.sum_signedMult_eq_zero_of_conditional_sharp input shape detach
    distinguished hConnected hGenus initial
  intro position hDet
  exact incomingRowDenominator_member_eq input shape detach distinguished hConnected hGenus position
    (memberPresentation input shape detach distinguished hConnected hGenus incoming position
      initial incomingFD hDet)

noncomputable local instance : DecidableEq (Option target.edges) := Classical.decEq _

/-- The same full Equation (8) balance in the canonical source-derived chart. -/
theorem sum_signedMult_canonical_eq_zero (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (distinguished : Fin degree)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation
      ((limitColumns input shape detach distinguished hConnected hGenus).member incoming).datum
        (Option target.edges)) :
    ∑ position : Fin 3, signedMult
      ((limitColumns input shape detach distinguished hConnected hGenus).labelling
        ((limitColumns input shape detach distinguished hConnected hGenus).canonicalInitialLabelling input)
          position).presentation = 0 :=
  sum_signedMult_eq_zero input shape detach distinguished hConnected hGenus incoming
    ((limitColumns input shape detach distinguished hConnected hGenus).canonicalInitialLabelling input)
    incomingFD

end DraismaVargas.Count.W2MkkIncomingDenominator

