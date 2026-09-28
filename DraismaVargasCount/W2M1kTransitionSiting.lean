import DraismaVargasCount.W2M1kMemberBalance
import DraismaVargasCount.W2M1kRowTransport

/-!
# The actual regrown transitions of Figure 33

This file sites the regrown transition on each perturbed member of case
`{w2-r2-nd3-M-1k}` (Draisma--Vargas Part I, arXiv:1909.12924, Figure 33).  The two unequal
adjacent indices force positive ramification; the member row calculus of
`W2M1kMemberBalance` bounds it by one.  The other endpoint has surviving valency three, so
the regrown occurrence is terminal on its stable row.

`forall_index_dvd_secondRow` and `forall_index_dvd_thirdRow` combine the siting
with the literal retained-occurrence injection of `W2M1kRowTransport` and consume
`RowRegrowth`.
No siting or transport hypotheses remain in those statements.  The sharp
denominator corollaries retain only the existing incoming-row distinctness
hypothesis; deriving it needs the incoming row's ramification bound.

The constructions below use the actual divided and joined candidates.  They
assume the member's full-dimensional presentation.  On the constructed family,
`W2M1kMemberBalance.memberPresentation` supplies it from an incoming chart,
target connectivity and genus zero, and the member's nonzero determinant.
-/

namespace DraismaVargas.Count.W2M1kTransitionSiting

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open W4Assembly W4StableSource StableLocalProperties FullDimensionalSource
open W2R1Target SecondEquation W2M1kSourceCandidates W2M1kStableGraph
open W2M1kLimitMatrix LimitChainCore
open RowWalk

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}

/-- All the geometric slots of `RowRegrowth`, with a specified partner index. -/
structure Siting (path : StablePath data) (regrown partner : data.SourceEdge)
    (vertex : data.SourceVertex) (index : ℕ) : Prop where
  transition : IsRowTransition data path vertex
  regrown_survives : ¬ IsDangling data regrown
  regrown_incident : Incident data regrown vertex
  partner_survives : ¬ IsDangling data partner
  partner_incident : Incident data partner vertex
  partner_ne : partner ≠ regrown
  terminal : ∀ u, Incident data regrown u → nonDanglingValency data u = 2 → u = vertex
  partner_index : data.sourceEdgeIndex partner = index

/-- Unequal indices exclude the unramified alternative of `RowRamificationAtMostOne`. -/
theorem transition_of_unequal_indices
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {first second : data.SourceEdge} {vertex : data.SourceVertex}
    (hTame : RowRamificationAtMostOne data path)
    (hValency : nonDanglingValency data vertex = 2)
    (hFirst : OnRow data path first) (hFirstIncident : Incident data first vertex)
    (hSecond : ¬ IsDangling data second) (hSecondIncident : Incident data second vertex)
    (hNe : first ≠ second) (hIndex : data.sourceEdgeIndex first ≠ data.sourceEdgeIndex second) :
    IsRowTransition data path vertex := by
  refine ⟨hValency, ?_, first, hFirst, hFirstIncident⟩
  rcases hTame vertex first hFirst hFirstIncident hValency with hZero | hOne
  · exact False.elim (hIndex (IndexPattern.sourceEdgeIndex_eq_of_localRamification_eq_zero
      fd hValency hZero hFirst.1 hFirstIncident hSecond hSecondIncident hNe))
  · exact hOne

variable {wall : target.V} {star : TwoStar target wall}
  {block : WallBlock data wall} {profile : W2R2SourceProfile.SourceProfile data star block}

/-- An occurrence added by expansion has just its two displayed endpoints. -/
theorem incident_newSourceEdge_endpoints
    (candidate : BalancedGlobal.Candidate target degree data wall) (sheet : Fin degree)
    {vertex : candidate.datum.SourceVertex}
    (hIncident : Incident candidate.datum (candidate.newSourceEdge sheet) vertex) :
    vertex = candidate.datum.sourceEndpoint (wallSide target wall false) sheet ∨
      vertex = candidate.datum.sourceEndpoint (wallSide target wall true) sheet := by
  change (candidate.datum.sourceEnds (candidate.newSourceEdge sheet)).1 = vertex ∨
    (candidate.datum.sourceEnds (candidate.newSourceEdge sheet)).2 = vertex at hIncident
  have hEnds : candidate.datum.sourceEnds (candidate.newSourceEdge sheet) =
      (candidate.datum.sourceEndpoint (wallSide target wall false) sheet,
        candidate.datum.sourceEndpoint (wallSide target wall true) sheet) :=
    GlobalResolution.sourceEnds_newSourceEdge data wall candidate.right (pasted candidate)
      (GlobalAssembly.blockwiseCompatible _ _ _ _ _ candidate.exterior) sheet
  rw [hEnds] at hIncident
  exact hIncident.elim (fun h ↦ Or.inl h.symm) (fun h ↦ Or.inr h.symm)

/-- If the opposite endpoint branches, only the selected endpoint can be interior. -/
theorem terminal_of_opposite_branch
    (candidate : BalancedGlobal.Candidate target degree data wall) (sheet : Fin degree)
    (selected other : Bool) (hNe : selected ≠ other)
    (hBranch : nonDanglingValency candidate.datum
      (candidate.datum.sourceEndpoint (wallSide target wall other) sheet) = 3) :
    ∀ u, Incident candidate.datum (candidate.newSourceEdge sheet) u →
      nonDanglingValency candidate.datum u = 2 →
      u = candidate.datum.sourceEndpoint (wallSide target wall selected) sheet := by
  intro u hIncident hValency
  rcases incident_newSourceEdge_endpoints candidate sheet hIncident with hLeft | hRight
  · cases selected <;> cases other <;> simp_all
  · cases selected <;> cases other <;> simp_all

/-- The siting of the regrown transition on the divided member, with every slot
constructed. -/
theorem divided_siting (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation (DividedData.candidate shape divided).datum coordinate) :
    Siting
      (NonDanglingEdge.stablePath
        ⟨(DividedData.candidate shape divided).oldSourceEdge profile.second.1,
          ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
            profile.second_survives⟩)
      ((DividedData.candidate shape divided).newSourceEdge divided.third)
      ((DividedData.candidate shape divided).oldSourceEdge profile.second.1)
      ((DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall (sideOf profile.doubleLabel)) divided.third) shape.k := by
  have hPartner := divided_pair_incident shape divided divided.third divided.rel_third
    (divided_third_ne_pin divided _)
  have hRegrown := newSourceEdge_incident_side (DividedData.candidate shape divided)
    (sideOf profile.doubleLabel) divided.third
  have hSurvives := ResolutionSurvival.not_isDangling_oldSourceEdge
    (DividedData.candidate shape divided) input.valid.1 _ profile.second_survives
  have hNew := divided_new_third_survives input shape divided
  have hNe := oldSourceEdge_ne_newSourceEdge
    (candidate := DividedData.candidate shape divided) profile.second.1 divided.third
  refine ⟨?_, hNew, hRegrown, hSurvives, hPartner, hNe, ?_, ?_⟩
  · apply transition_of_unequal_indices fd
      (W2M1kMemberBalance.rowCalculus_dividedCandidate_secondRow input shape divided fd).1
      (divided_nonDanglingValency_pair input shape divided divided.third divided.rel_third
        (divided_third_ne_pin divided _)) ⟨hSurvives, rfl⟩ hPartner hNew hRegrown hNe
    rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge, shape.second_index,
      divided_newSourceEdge_index shape divided divided.third divided.rel_third,
      dividedNewEdge_blockCard_third shape divided]
    have := shape.one_lt_k
    omega
  · exact terminal_of_opposite_branch _ divided.third _ _
      (sideOf_ne profile.labels_ne)
      (divided_nonDanglingValency_branch input shape divided divided.third divided.rel_third
        (divided_third_ne_pin divided _))
  · rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge, shape.second_index]

/-- The siting on the joined member, based at the canonical sheet of the selected block. -/
theorem joined_siting (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation (joinedCandidate star geometry).datum coordinate) :
    Siting
      (NonDanglingEdge.stablePath
        ⟨(joinedCandidate star geometry).oldSourceEdge profile.third.1,
          ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
            profile.third_survives⟩)
      ((joinedCandidate star geometry).newSourceEdge block.1)
      ((joinedCandidate star geometry).oldSourceEdge profile.third.1)
      ((joinedCandidate star geometry).datum.sourceEndpoint
        (wallSide target wall (sideOf profile.singleLabel)) block.1) shape.k := by
  have hRel : (data.vertexPartition wall).Rel block.1 block.1 := rfl
  have hPartner := joined_old_incident geometry (sideOf profile.singleLabel)
    profile.third (by rw [sideLabel_sideOf]; exact profile.third_target) block.1 hRel
  have hRegrown := newSourceEdge_incident_side (joinedCandidate star geometry)
    (sideOf profile.singleLabel) block.1
  have hSurvives := ResolutionSurvival.not_isDangling_oldSourceEdge
    (joinedCandidate star geometry) input.valid.1 _ profile.third_survives
  have hNew := joined_new_survives input shape geometry block.1 hRel
  have hNe := oldSourceEdge_ne_newSourceEdge
    (candidate := joinedCandidate star geometry) profile.third.1 block.1
  refine ⟨?_, hNew, hRegrown, hSurvives, hPartner, hNe, ?_, ?_⟩
  · apply transition_of_unequal_indices fd
      (W2M1kMemberBalance.rowCalculus_joinedCandidate_thirdRow input shape geometry fd).1
      (joined_nonDanglingValency_single input shape geometry block.1 hRel)
      ⟨hSurvives, rfl⟩ hPartner hNew hRegrown hNe
    rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge, shape.third_index,
      joined_newSourceEdge_index geometry block.1, wall_blockCard_of_rel shape hRel]
    omega
  · exact terminal_of_opposite_branch _ block.1 _ _
      (sideOf_ne profile.labels_ne.symm)
      (joined_nonDanglingValency_double input shape geometry block.1 hRel)
  · rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge, shape.third_index]

/-- The member row calculus, the occurrence transport and the siting composed on the actual
divided member: every incoming second-row index divides `k`.  No siting or
occurrence-transport receipt is assumed. -/
theorem forall_index_dvd_secondRow (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation (DividedData.candidate shape divided).datum coordinate) :
    ∀ edge ∈ TrivalentWeight.incomingRowEdges data (W2M1kCommonBalance.secondRow profile),
      data.sourceEdgeIndex edge ∣ shape.k := by
  have site := divided_siting input shape divided fd
  exact W2M1kMemberBalance.forall_index_dvd_secondRow_of_regrowth_of_fullDim shape fd
    site.transition site.regrown_survives site.regrown_incident
    site.partner_survives site.partner_incident site.partner_ne site.terminal site.partner_index
    (W2M1kRowTransport.transport_divided_secondRow input shape divided)

/-- The same complete regrowth argument on the actual joined member. -/
theorem forall_index_dvd_thirdRow (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation (joinedCandidate star geometry).datum coordinate) :
    ∀ edge ∈ TrivalentWeight.incomingRowEdges data (W2M1kCommonBalance.thirdRow profile),
      data.sourceEdgeIndex edge ∣ shape.k := by
  have site := joined_siting input shape geometry fd
  exact W2M1kMemberBalance.forall_index_dvd_thirdRow_of_regrowth_of_fullDim shape fd
    site.transition site.regrown_survives site.regrown_incident
    site.partner_survives site.partner_incident site.partner_ne site.terminal site.partner_index
    (W2M1kRowTransport.transport_joined_thirdRow input profile geometry)

open W2M1kTransport

/-- The aligned orientation's divided member lives over a branch-swapped datum.
Its siting and the gauge transport of `W2M1kRowTransport` still control the original
incoming row. -/
theorem forall_index_dvd_secondRow_remote (input : W2SourceInput data star)
    (shape : Shape profile) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other)
    (divided : DividedData (swapProfile profile input.valid.1 other hOther))
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation
      (DividedData.candidate (swapShape shape input.valid.1 other hOther) divided).datum
      coordinate) :
    ∀ edge ∈ TrivalentWeight.incomingRowEdges data (W2M1kCommonBalance.secondRow profile),
      data.sourceEdgeIndex edge ∣ shape.k := by
  have site := divided_siting (swapInput input other hOther)
    (swapShape shape input.valid.1 other hOther) divided fd
  exact W2M1kMemberBalance.forall_index_dvd_secondRow_of_regrowth_of_fullDim shape fd
    site.transition site.regrown_survives site.regrown_incident
    site.partner_survives site.partner_incident site.partner_ne site.terminal site.partner_index
    (W2M1kRowTransport.transport_remote_divided_secondRow input shape other hOther divided)

/-- Sharp incoming second-row denominator, with all member-side geometry discharged. -/
theorem incomingRowDenominator_secondRow_eq (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation (DividedData.candidate shape divided).datum coordinate)
    (hRows : W2M1kCommonBalance.secondRow profile ≠ W2M1kCommonBalance.thirdRow profile) :
    TrivalentWeight.incomingRowDenominator data (W2M1kCommonBalance.secondRow profile) =
      shape.k :=
  IncomingSimpleColumn.incomingRowDenominator_secondRow_eq_of_index profile input shape hRows
    (forall_index_dvd_secondRow input shape divided fd)

/-- Sharp incoming third-row denominator, with all member-side geometry discharged. -/
theorem incomingRowDenominator_thirdRow_eq (input : W2SourceInput data star)
    (shape : Shape profile) (geometry : GlobalM1k.Geometry data wall)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation (joinedCandidate star geometry).datum coordinate)
    (hRows : W2M1kCommonBalance.secondRow profile ≠ W2M1kCommonBalance.thirdRow profile) :
    TrivalentWeight.incomingRowDenominator data (W2M1kCommonBalance.thirdRow profile) =
      shape.k :=
  IncomingSimpleColumn.incomingRowDenominator_thirdRow_eq_of_index profile input shape hRows
    (forall_index_dvd_thirdRow input shape geometry fd)

end DraismaVargas.Count.W2M1kTransitionSiting
