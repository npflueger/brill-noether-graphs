module

public import DraismaVargas.LocalCases.W2PSourceCandidates
public import DraismaVargas.LocalCases.W2MkkStableGraph
public import DraismaVargas.LocalCases.LimitChainCore
public import DraismaVargas.LocalCases.M11JoinedDescentGeometry
public import DraismaVargas.LocalCases.ResolutionAwayFromWall

@[expose] public section

/-!
# Figure 35's survival census

The three members of Figure 35 of Draisma--Vargas Part I (arXiv:1909.12924,
Section 6, Case `{w2-r2-nd3-P}`) share one shape: the `t₂` endpoint partition
is also the new-edge partition, a coarsening of the `t₂` occurrence partition,
and the `t₃` endpoint keeps the whole wall block.  This module computes the
endpoint incidences of that shape and which occurrences survive pruning.
-/

namespace DraismaVargas.LocalCases.W2PSurvival

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open ResolutionM11 GlobalM11Arbitrary
open ResolutionAwayFromWall
open W2PSourceCandidates

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}

/-- The common Figure 35 member shape. -/
structure MemberShape (profile : W2R2SourceProfile.SourceProfile data star block) where
  /-- The `t₂` endpoint partition, which is also the new-edge partition. -/
  fine : SheetPartition degree
  /-- It refines the wall block structure. -/
  refines : fine.Refines (data.vertexPartition wall)
  /-- The `t₂` occurrence partition refines it. -/
  covers : (endpointPartition profile).Refines fine

namespace MemberShape

variable {profile : W2R2SourceProfile.SourceProfile data star block}

/-- The member as an actual outgoing candidate. -/
noncomputable def candidate (member : MemberShape profile) :
    BalancedGlobal.Candidate target degree data wall :=
  (pattern profile (firstSheet profile) member.fine member.refines member.covers).candidate
    (leftSplitResolution_contracts _ _ _)

/-- The selected local resolution of the member. -/
abbrev selected (member : MemberShape profile) : LocalResolution degree :=
  leftSplitResolution (data.vertexPartition wall) member.fine member.refines

theorem resolution_eq (member : MemberShape profile) (anchor : Fin degree) :
    member.candidate.resolution anchor =
      LocalResolution.onBlock (data.vertexPartition wall) (firstSheet profile)
        member.selected (fun _ ↦ joinedResolutionAt (data.vertexPartition wall)) anchor := rfl

theorem right_eq (member : MemberShape profile) (edge : target.edges) :
    member.candidate.right edge = (orientedStar profile).right edge := rfl

end MemberShape

/-- The shape that merges the dangling sheet into one of the two surviving
`t₂` occurrences: Base II.2.1.P and Base II.2.2.P in one definition. -/
noncomputable def mergeShape (profile : W2R2SourceProfile.SourceProfile data star block)
    (own : IncidentSourceEdge data (WallBlock.sourceVertex data wall block))
    (hOwnExtra : ¬ (endpointPartition profile).Rel own.1.1.2 (extraSheet profile)) :
    MemberShape profile where
  fine := (endpointPartition profile).mergeBlocks own.1.1.2 (extraSheet profile) hOwnExtra
  refines := (endpointPartition profile).mergeBlocks_refines_coarse (data.vertexPartition wall)
    own.1.1.2 (extraSheet profile) hOwnExtra (endpointPartition_refines profile)
    ((sheet_rel_of_incident own).symm.trans (extraSheet_rel profile))
  covers := SheetPartition.refines_mergeBlocks _ _ _ _

/-- Figure 35's `M⁽¹⁾` shape. -/
noncomputable def firstShape {profile : W2R2SourceProfile.SourceProfile data star block}
    (shape : Shape profile) : MemberShape profile :=
  mergeShape profile profile.first (first_extra_separate shape)

/-- Figure 35's `M⁽²⁾` shape. -/
noncomputable def secondShape {profile : W2R2SourceProfile.SourceProfile data star block}
    (shape : Shape profile) : MemberShape profile :=
  mergeShape profile profile.second (second_extra_separate shape)

/-- Figure 35's `M⁽³⁾` shape. -/
noncomputable def thirdShape {profile : W2R2SourceProfile.SourceProfile data star block}
    (shape : Shape profile) : MemberShape profile where
  fine := thirdFine shape
  refines := thirdFine_refines shape
  covers := SheetPartition.refines_detachSheet_of_block_singleton _ (data.vertexPartition wall)
    (extraSheet profile) (firstSheet profile) (extra_ne_first shape)
    (wall_extra_first profile) (endpointPartition_refines profile)
    (extraSheet_block shape)

theorem firstShape_candidate {profile : W2R2SourceProfile.SourceProfile data star block}
    (shape : Shape profile) : (firstShape shape).candidate = firstMember shape := rfl

theorem secondShape_candidate {profile : W2R2SourceProfile.SourceProfile data star block}
    (shape : Shape profile) : (secondShape shape).candidate = secondMember shape := rfl

theorem thirdShape_candidate {profile : W2R2SourceProfile.SourceProfile data star block}
    (shape : Shape profile) : (thirdShape shape).candidate = thirdMember shape := rfl


/-! ## The pasted geometry of one member -/

namespace MemberShape

variable {profile : W2R2SourceProfile.SourceProfile data star block}

theorem rel_firstSheet_iff (sheet : Fin degree) :
    (data.vertexPartition wall).Rel (firstSheet profile) sheet ↔
      (data.vertexPartition wall).Rel block.1 sheet :=
  ⟨fun h ↦ (firstSheet_rel profile).trans h, fun h ↦ (firstSheet_rel profile).symm.trans h⟩

theorem resolution_of_rel (member : MemberShape profile) (anchor : Fin degree)
    (hRel : (data.vertexPartition wall).Rel block.1 anchor) :
    member.candidate.resolution anchor = member.selected := by
  rw [member.resolution_eq anchor,
    LocalResolution.onBlock_of_rel _ _ _ _ _ ((rel_firstSheet_iff anchor).mpr hRel)]

theorem resolution_of_not_rel (member : MemberShape profile) (anchor : Fin degree)
    (hRel : ¬ (data.vertexPartition wall).Rel block.1 anchor) :
    member.candidate.resolution anchor = joinedResolutionAt (data.vertexPartition wall) := by
  rw [member.resolution_eq anchor,
    LocalResolution.onBlock_of_not_rel _ _ _ _ _
      (fun h ↦ hRel ((rel_firstSheet_iff anchor).mp h))]

theorem resolution_repr_of_rel (member : MemberShape profile) (sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    member.candidate.resolution ((data.vertexPartition wall).repr sheet) = member.selected :=
  member.resolution_of_rel _ (hRel.trans ((data.vertexPartition wall).rel_repr_right sheet))

theorem resolution_repr_of_not_rel (member : MemberShape profile) (sheet : Fin degree)
    (hRel : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    member.candidate.resolution ((data.vertexPartition wall).repr sheet) =
      joinedResolutionAt (data.vertexPartition wall) :=
  member.resolution_of_not_rel _
    (fun h ↦ hRel (h.trans ((data.vertexPartition wall).rel_repr_left sheet)))

/-- The pasted new-edge partition, inside `A₀`. -/
theorem pasted_newEdge_rel_iff_of_rel (member : MemberShape profile) (first second : Fin degree)
    (hRel : (data.vertexPartition wall).Rel block.1 first) :
    (LimitChainCore.pasted member.candidate).newEdge.Rel first second ↔
      member.fine.Rel first second := by
  rw [← SheetPartition.mem_block_iff, ← SheetPartition.mem_block_iff,
    LocalResolution.pasteNewEdge_block, member.resolution_repr_of_rel first hRel]
  rfl

theorem pasted_newEdge_rel_iff_of_not_rel (member : MemberShape profile)
    (first second : Fin degree) (hRel : ¬ (data.vertexPartition wall).Rel block.1 first) :
    (LimitChainCore.pasted member.candidate).newEdge.Rel first second ↔
      (data.vertexPartition wall).Rel first second := by
  rw [← SheetPartition.mem_block_iff, ← SheetPartition.mem_block_iff,
    LocalResolution.pasteNewEdge_block, member.resolution_repr_of_not_rel first hRel]
  rfl

/-- Two regrown occurrences inside `A₀` agree exactly on the fine blocks. -/
theorem newSourceEdge_eq_iff_fine (member : MemberShape profile) (first second : Fin degree)
    (hRel : (data.vertexPartition wall).Rel block.1 first) :
    member.candidate.newSourceEdge first = member.candidate.newSourceEdge second ↔
      member.fine.Rel first second :=
  (LimitChainCore.newSourceEdge_eq_iff_rel first second).trans
    (member.pasted_newEdge_rel_iff_of_rel first second hRel)

theorem newSourceEdge_eq_iff_wall (member : MemberShape profile) (first second : Fin degree)
    (hRel : ¬ (data.vertexPartition wall).Rel block.1 first) :
    member.candidate.newSourceEdge first = member.candidate.newSourceEdge second ↔
      (data.vertexPartition wall).Rel first second :=
  (LimitChainCore.newSourceEdge_eq_iff_rel first second).trans
    (member.pasted_newEdge_rel_iff_of_not_rel first second hRel)

/-- The regrown index inside `A₀` is the fine block's cardinality. -/
theorem newSourceEdge_index_of_rel (member : MemberShape profile) (sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    member.candidate.datum.sourceEdgeIndex (member.candidate.newSourceEdge sheet) =
      member.fine.blockCard sheet := by
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge,
    LocalResolution.paste_newEdge_blockCard, member.resolution_repr_of_rel sheet hRel]
  rfl

/-- Outside `A₀` the regrown index is the old wall block's cardinality. -/
theorem newSourceEdge_index_of_not_rel (member : MemberShape profile) (sheet : Fin degree)
    (hRel : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    member.candidate.datum.sourceEdgeIndex (member.candidate.newSourceEdge sheet) =
      (data.vertexPartition wall).blockCard sheet := by
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge,
    LocalResolution.paste_newEdge_blockCard, member.resolution_repr_of_not_rel sheet hRel]
  rfl

/-- Every member preserves the source genus: on `A₀` the `t₃` endpoint is the
whole wall block and the new edge agrees with the `t₂` endpoint; elsewhere the
background is the joined star. -/
theorem sourceGenus (member : MemberShape profile) :
    genus member.candidate.datum.sourceGraph = genus data.sourceGraph := by
  apply M11SourceGenus.candidate_sourceGenus_of_stars
  intro anchor
  by_cases hRel : (data.vertexPartition wall).Rel block.1 anchor
  · rw [member.resolution_of_rel anchor hRel]
    exact Or.inr ⟨rfl, rfl⟩
  · rw [member.resolution_of_not_rel anchor hRel]
    exact Or.inl ⟨rfl, rfl⟩

end MemberShape


/-! ## The endpoint incidence census -/

namespace MemberShape

variable {profile : W2R2SourceProfile.SourceProfile data star block}

theorem target_valencies (member : MemberShape profile) :
    (GluingDatum.incidentEdges (target := graph target wall member.candidate.right)
        (oldVertex target wall)).card = 2 ∧
      (GluingDatum.incidentEdges (target := graph target wall member.candidate.right)
        (freshVertex target)).card = 2 :=
  M11SourceCandidates.candidate_target_valencies member.candidate

theorem pasted_newEdge_blockCountWithin_left (member : MemberShape profile)
    (sheet : Fin degree) :
    (LimitChainCore.pasted member.candidate).newEdge.blockCountWithin
      (LimitChainCore.pasted member.candidate).left sheet = 1 := by
  rw [LocalResolution.paste_newEdge_blockCountWithin_left]
  by_cases hRel : (data.vertexPartition wall).Rel block.1 sheet
  · rw [member.resolution_repr_of_rel sheet hRel]
    exact SheetPartition.blockCountWithin_self _ _
  · rw [member.resolution_repr_of_not_rel sheet hRel]
    exact SheetPartition.blockCountWithin_self _ _

theorem pasted_newEdge_blockCountWithin_right_of_rel (member : MemberShape profile)
    (sheet : Fin degree) (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    (LimitChainCore.pasted member.candidate).newEdge.blockCountWithin
        (LimitChainCore.pasted member.candidate).right sheet =
      member.fine.blockCountWithin (data.vertexPartition wall) sheet := by
  rw [LocalResolution.paste_newEdge_blockCountWithin_right,
    member.resolution_repr_of_rel sheet hRel]
  rfl

theorem pasted_newEdge_blockCountWithin_right_of_not_rel (member : MemberShape profile)
    (sheet : Fin degree) (hRel : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    (LimitChainCore.pasted member.candidate).newEdge.blockCountWithin
      (LimitChainCore.pasted member.candidate).right sheet = 1 := by
  rw [LocalResolution.paste_newEdge_blockCountWithin_right,
    member.resolution_repr_of_not_rel sheet hRel]
  exact SheetPartition.blockCountWithin_self _ _

theorem edgePartition_blockCountWithin_pasted_left_of_rel (member : MemberShape profile)
    (sheet : Fin degree) (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    (data.edgePartition (star.edge profile.doubleLabel)).blockCountWithin
        (LimitChainCore.pasted member.candidate).left sheet =
      (endpointPartition profile).blockCountWithin member.fine sheet := by
  rw [LocalResolution.blockCountWithin_paste_left, member.resolution_repr_of_rel sheet hRel]
  rfl

theorem edgePartition_blockCountWithin_pasted_left_of_not_rel (member : MemberShape profile)
    (sheet : Fin degree) (hRel : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    (data.edgePartition (star.edge profile.doubleLabel)).blockCountWithin
        (LimitChainCore.pasted member.candidate).left sheet =
      (endpointPartition profile).blockCountWithin (data.vertexPartition wall) sheet := by
  rw [LocalResolution.blockCountWithin_paste_left, member.resolution_repr_of_not_rel sheet hRel]
  rfl

theorem edgePartition_blockCountWithin_pasted_right (member : MemberShape profile)
    (label : Fin 2) (sheet : Fin degree) :
    (data.edgePartition (star.edge label)).blockCountWithin
        (LimitChainCore.pasted member.candidate).right sheet =
      (data.edgePartition (star.edge label)).blockCountWithin
        (data.vertexPartition wall) sheet := by
  rw [LocalResolution.blockCountWithin_paste_right]
  by_cases hRel : (data.vertexPartition wall).Rel block.1 sheet
  · rw [member.resolution_repr_of_rel sheet hRel]; rfl
  · rw [member.resolution_repr_of_not_rel sheet hRel]; rfl

/-- **The `t₂` endpoint census.**  One regrown occurrence, plus the `t₂`
occurrences inside the fine block. -/
theorem card_incident_old (member : MemberShape profile) (sheet : Fin degree) :
    Fintype.card (IncidentSourceEdge member.candidate.datum
        (member.candidate.datum.sourceEndpoint (oldVertex target wall) sheet)) =
      1 + (data.edgePartition (star.edge profile.doubleLabel)).blockCountWithin
        (LimitChainCore.pasted member.candidate).left sheet := by
  rw [LimitChainCore.card_incident_oldEndpoint (twoStar := orientedStar profile)
    (fun edge ↦ member.right_eq edge) sheet,
    member.pasted_newEdge_blockCountWithin_left sheet, orientedStar_edge_zero]

/-- **The `t₃` endpoint census.**  The regrown occurrences inside the old wall
block, plus the `t₃` occurrences inside it. -/
theorem card_incident_fresh (member : MemberShape profile) (sheet : Fin degree) :
    Fintype.card (IncidentSourceEdge member.candidate.datum
        (member.candidate.datum.sourceEndpoint (freshVertex target) sheet)) =
      (LimitChainCore.pasted member.candidate).newEdge.blockCountWithin
          (LimitChainCore.pasted member.candidate).right sheet +
        (data.edgePartition (star.edge profile.singleLabel)).blockCountWithin
          (data.vertexPartition wall) sheet := by
  rw [LimitChainCore.card_incident_freshEndpoint (twoStar := orientedStar profile)
    (fun edge ↦ member.right_eq edge) sheet, orientedStar_edge_one,
    member.edgePartition_blockCountWithin_pasted_right profile.singleLabel sheet]

end MemberShape


/-! ## Two general partition lemmas -/

theorem blockCountWithin_eq_one_of_block_eq {d : ℕ} (fine coarse : SheetPartition d)
    (i : Fin d) (hBlock : fine.block i = coarse.block i) :
    fine.blockCountWithin coarse i = 1 := by
  have h := fine.blockCountWithin_self i
  unfold SheetPartition.blockCountWithin at h ⊢
  rw [hBlock] at h
  exact h

theorem block_eq_of_refines_of_blockCard_le {d : ℕ} (fine coarse : SheetPartition d)
    (hRefines : fine.Refines coarse) (i : Fin d)
    (hCard : coarse.blockCard i ≤ fine.blockCard i) : fine.block i = coarse.block i := by
  apply Finset.eq_of_subset_of_card_le
  · intro sheet hSheet
    exact (coarse.mem_block_iff i sheet).mpr (hRefines.rel ((fine.mem_block_iff i sheet).mp hSheet))
  · exact hCard

/-! ## The `t₃` direction displays exactly `e₃` on `A₀` -/

/-- **Cardinality P's one-occurrence `t₃` fibre.**  `k₃ = |A₀|` forces `e₃`'s
block to be the whole wall block, so the `t₃` direction induces a single block
there. -/
theorem single_blockCountWithin {profile : W2R2SourceProfile.SourceProfile data star block}
    (shape : Shape profile) (sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    (data.edgePartition (star.edge profile.singleLabel)).blockCountWithin
      (data.vertexPartition wall) sheet = 1 := by
  have hThirdRel : (data.vertexPartition wall).Rel block.1 profile.third.1.1.2 :=
    sheet_rel_of_incident profile.third
  have hIndex : (data.edgePartition (star.edge profile.singleLabel)).blockCard
      profile.third.1.1.2 = data.sourceEdgeIndex profile.third.1 := by
    show (data.edgePartition (star.edge profile.singleLabel)).blockCard profile.third.1.1.2 =
      (data.edgePartition profile.third.1.1.1).blockCard profile.third.1.1.2
    rw [profile.third_target]
  have hWall : (data.vertexPartition wall).blockCard profile.third.1.1.2 =
      data.sourceEdgeIndex profile.third.1 := by
    rw [← SheetPartition.blockCard_congr (data.vertexPartition wall) hThirdRel]
    exact shape.cardinality.2.symm
  have hBlock := block_eq_of_refines_of_blockCard_le
    (data.edgePartition (star.edge profile.singleLabel)) (data.vertexPartition wall)
    (star.edgePartition_refines_wall data profile.singleLabel) profile.third.1.1.2
    (le_of_eq (hWall.trans hIndex.symm))
  rw [← SheetPartition.blockCountWithin_congr _ (data.vertexPartition wall)
    (hThirdRel.symm.trans hRel)]
  exact blockCountWithin_eq_one_of_block_eq _ _ _ hBlock

/-! ## The four endpoint counts -/

namespace MemberShape

variable {profile : W2R2SourceProfile.SourceProfile data star block}

/-- Outside `A₀` the `t₂` endpoint is divalent. -/
theorem card_incident_old_background (input : W2SourceInput data star)
    (member : MemberShape profile) (sheet : Fin degree)
    (hBackground : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    Fintype.card (IncidentSourceEdge member.candidate.datum
      (member.candidate.datum.sourceEndpoint (oldVertex target wall) sheet)) = 2 := by
  rw [member.card_incident_old sheet,
    member.edgePartition_blockCountWithin_pasted_left_of_not_rel sheet hBackground]
  rw [show (endpointPartition profile) =
      data.edgePartition (star.edge profile.doubleLabel) from rfl,
    M11JoinedBackground.background_blockCount input profile profile.doubleLabel sheet hBackground]

/-- Outside `A₀` the `t₃` endpoint is divalent. -/
theorem card_incident_fresh_background (input : W2SourceInput data star)
    (member : MemberShape profile) (sheet : Fin degree)
    (hBackground : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    Fintype.card (IncidentSourceEdge member.candidate.datum
      (member.candidate.datum.sourceEndpoint (freshVertex target) sheet)) = 2 := by
  rw [member.card_incident_fresh sheet,
    member.pasted_newEdge_blockCountWithin_right_of_not_rel sheet hBackground,
    M11JoinedBackground.background_blockCount input profile profile.singleLabel sheet hBackground]

/-- Inside `A₀` the `t₂` endpoint carries the regrown occurrence and the `t₂`
occurrences of its own fine block. -/
theorem card_incident_old_selected (member : MemberShape profile) (sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    Fintype.card (IncidentSourceEdge member.candidate.datum
        (member.candidate.datum.sourceEndpoint (oldVertex target wall) sheet)) =
      1 + (endpointPartition profile).blockCountWithin member.fine sheet := by
  rw [member.card_incident_old sheet,
    member.edgePartition_blockCountWithin_pasted_left_of_rel sheet hRel]

/-- Inside `A₀` the `t₃` endpoint carries the regrown occurrences of the whole
wall block and the single `t₃` occurrence `e₃`. -/
theorem card_incident_fresh_selected (shape : Shape profile) (member : MemberShape profile)
    (sheet : Fin degree) (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    Fintype.card (IncidentSourceEdge member.candidate.datum
        (member.candidate.datum.sourceEndpoint (freshVertex target) sheet)) =
      member.fine.blockCountWithin (data.vertexPartition wall) sheet + 1 := by
  rw [member.card_incident_fresh sheet,
    member.pasted_newEdge_blockCountWithin_right_of_rel sheet hRel,
    single_blockCountWithin shape sheet hRel]

end MemberShape


/-! ## Which occurrences meet which endpoint -/

namespace MemberShape

variable {profile : W2R2SourceProfile.SourceProfile data star block}

theorem right_double (member : MemberShape profile) :
    member.candidate.right (star.edge profile.doubleLabel) = false := by
  rw [member.right_eq, ← orientedStar_edge_zero profile]
  exact TwoStar.right_edge_zero _

theorem right_single (member : MemberShape profile) :
    member.candidate.right (star.edge profile.singleLabel) = true := by
  rw [member.right_eq, ← orientedStar_edge_one profile]
  exact TwoStar.right_edge_one _

/-- The `t₃` endpoint keeps the whole old wall partition. -/
theorem pasted_right_eq (member : MemberShape profile) :
    (LimitChainCore.pasted member.candidate).right = data.vertexPartition wall := by
  apply SheetPartition.ext_repr
  funext sheet
  change (member.candidate.resolution ((data.vertexPartition wall).repr sheet)).right.repr sheet = _
  by_cases hRel : (data.vertexPartition wall).Rel block.1 sheet
  · rw [member.resolution_repr_of_rel sheet hRel]; rfl
  · rw [member.resolution_repr_of_not_rel sheet hRel]; rfl

theorem vertexPartition_old (member : MemberShape profile) :
    member.candidate.datum.vertexPartition (oldVertex target wall) =
      (LimitChainCore.pasted member.candidate).left :=
  GlobalResolution.expandedVertexPartition_old_wall data wall _

theorem vertexPartition_fresh (member : MemberShape profile) :
    member.candidate.datum.vertexPartition (freshVertex target) = data.vertexPartition wall :=
  (GlobalResolution.expandedVertexPartition_fresh data wall _).trans member.pasted_right_eq

theorem sourceEndpoint_fresh_eq_of_rel (member : MemberShape profile) (first second : Fin degree)
    (hRel : (data.vertexPartition wall).Rel first second) :
    member.candidate.datum.sourceEndpoint (freshVertex target) first =
      member.candidate.datum.sourceEndpoint (freshVertex target) second := by
  refine (member.candidate.datum.sourceEndpoint_eq_iff (freshVertex target) first _).mpr
    ⟨rfl, ?_⟩
  change (member.candidate.datum.vertexPartition (freshVertex target)).Rel first
    ((member.candidate.datum.vertexPartition (freshVertex target)).repr second)
  rw [member.vertexPartition_fresh]
  exact hRel.trans ((data.vertexPartition wall).rel_repr_right second)

/-- The retained `t₂` occurrence through a sheet meets the `t₂` endpoint over
that sheet. -/
theorem double_incident_canonical (member : MemberShape profile) (sheet : Fin degree) :
    Incident member.candidate.datum
      (member.candidate.oldSourceEdge (data.sourceEdge (star.edge profile.doubleLabel) sheet))
      (member.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) :=
  LimitChainCore.oldSourceEdge_incident_old member.candidate _
    (star.edge_mem_incidentEdges profile.doubleLabel) member.right_double sheet

/-- The retained `t₃` occurrence through a sheet meets the `t₃` endpoint over
that sheet. -/
theorem single_incident_canonical (member : MemberShape profile) (sheet : Fin degree) :
    Incident member.candidate.datum
      (member.candidate.oldSourceEdge (data.sourceEdge (star.edge profile.singleLabel) sheet))
      (member.candidate.datum.sourceEndpoint (freshVertex target) sheet) :=
  M11SplitSurvival.oldSourceEdge_incident_fresh member.candidate _
    (star.edge_mem_incidentEdges profile.singleLabel) member.right_single sheet

/-- An actual retained `t₂` occurrence meets the `t₂` endpoint over any sheet
of its own fine block. -/
theorem double_incident (member : MemberShape profile) (edge : data.SourceEdge)
    (hTarget : edge.1.1 = star.edge profile.doubleLabel) (anchor : Fin degree)
    (hRel : (LimitChainCore.pasted member.candidate).left.Rel anchor edge.1.2) :
    Incident member.candidate.datum (member.candidate.oldSourceEdge edge)
      (member.candidate.datum.sourceEndpoint (oldVertex target wall) anchor) := by
  have h := member.double_incident_canonical edge.1.2
  rw [show data.sourceEdge (star.edge profile.doubleLabel) edge.1.2 = edge from by
    rw [← hTarget]; exact GluingDatum.sourceEdge_self data edge] at h
  exact LimitChainCore.sourceEndpoint_old_eq_of_rel edge.1.2 anchor hRel.symm ▸ h

/-- An actual retained `t₃` occurrence meets the `t₃` endpoint over any sheet
of its own old wall block. -/
theorem single_incident (member : MemberShape profile) (edge : data.SourceEdge)
    (hTarget : edge.1.1 = star.edge profile.singleLabel) (anchor : Fin degree)
    (hRel : (data.vertexPartition wall).Rel anchor edge.1.2) :
    Incident member.candidate.datum (member.candidate.oldSourceEdge edge)
      (member.candidate.datum.sourceEndpoint (freshVertex target) anchor) := by
  have h := member.single_incident_canonical edge.1.2
  rw [show data.sourceEdge (star.edge profile.singleLabel) edge.1.2 = edge from by
    rw [← hTarget]; exact GluingDatum.sourceEdge_self data edge] at h
  exact member.sourceEndpoint_fresh_eq_of_rel edge.1.2 anchor hRel.symm ▸ h

/-- What a retained occurrence at the `t₂` endpoint must be. -/
theorem retained_incident_old_data (member : MemberShape profile) (sheet : Fin degree)
    (edge : data.SourceEdge)
    (hIncident : Incident member.candidate.datum (member.candidate.oldSourceEdge edge)
      (member.candidate.datum.sourceEndpoint (oldVertex target wall) sheet)) :
    edge.1.1 = star.edge profile.doubleLabel ∧
      (LimitChainCore.pasted member.candidate).left.Rel sheet edge.1.2 := by
  classical
  have h := (incident_iff_target_mem_and_rel _ _ _).mp hIncident
  have hTarget := h.1
  change occurrenceEquiv target wall member.candidate.right (some edge.1.1) ∈
    GluingDatum.incidentEdges (oldVertex target wall) at hTarget
  rw [LimitChainCore.target_incident_pair_old (twoStar := orientedStar profile)
    (fun e ↦ member.right_eq e)] at hTarget
  rcases Finset.mem_insert.mp hTarget with hNew | hOld
  · have hLabels := (occurrenceEquiv target wall member.candidate.right).injective hNew
    cases hLabels
  · have hLabels := (occurrenceEquiv target wall member.candidate.right).injective
      (Finset.mem_singleton.mp hOld)
    refine ⟨(Option.some.inj hLabels).trans (orientedStar_edge_zero profile), ?_⟩
    have hRel := h.2
    change (member.candidate.datum.vertexPartition (oldVertex target wall)).Rel
      ((member.candidate.datum.vertexPartition (oldVertex target wall)).repr sheet) edge.1.2 at hRel
    rw [member.vertexPartition_old] at hRel
    simpa only [SheetPartition.Rel, SheetPartition.repr_idem] using hRel

/-- What a retained occurrence at the `t₃` endpoint must be. -/
theorem retained_incident_fresh_data (member : MemberShape profile) (sheet : Fin degree)
    (edge : data.SourceEdge)
    (hIncident : Incident member.candidate.datum (member.candidate.oldSourceEdge edge)
      (member.candidate.datum.sourceEndpoint (freshVertex target) sheet)) :
    edge.1.1 = star.edge profile.singleLabel ∧
      (data.vertexPartition wall).Rel sheet edge.1.2 := by
  classical
  have h := (incident_iff_target_mem_and_rel _ _ _).mp hIncident
  have hTarget := h.1
  change occurrenceEquiv target wall member.candidate.right (some edge.1.1) ∈
    GluingDatum.incidentEdges (freshVertex target) at hTarget
  rw [LimitChainCore.target_incident_pair_fresh (twoStar := orientedStar profile)
    (fun e ↦ member.right_eq e)] at hTarget
  rcases Finset.mem_insert.mp hTarget with hNew | hOld
  · have hLabels := (occurrenceEquiv target wall member.candidate.right).injective hNew
    cases hLabels
  · have hLabels := (occurrenceEquiv target wall member.candidate.right).injective
      (Finset.mem_singleton.mp hOld)
    refine ⟨(Option.some.inj hLabels).trans (orientedStar_edge_one profile), ?_⟩
    have hRel := h.2
    change (member.candidate.datum.vertexPartition (freshVertex target)).Rel
      ((member.candidate.datum.vertexPartition (freshVertex target)).repr sheet) edge.1.2 at hRel
    rw [member.vertexPartition_fresh] at hRel
    simpa only [SheetPartition.Rel, SheetPartition.repr_idem] using hRel

/-- A regrown occurrence at the `t₂` endpoint lies in its own fine block. -/
theorem new_incident_old_rel (member : MemberShape profile) (anchor sheet : Fin degree)
    (hIncident : Incident member.candidate.datum (member.candidate.newSourceEdge sheet)
      (member.candidate.datum.sourceEndpoint (oldVertex target wall) anchor)) :
    (LimitChainCore.pasted member.candidate).left.Rel anchor sheet := by
  have hRel := ((incident_iff_target_mem_and_rel _ _ _).mp hIncident).2
  change (member.candidate.datum.vertexPartition (oldVertex target wall)).Rel
    ((member.candidate.datum.vertexPartition (oldVertex target wall)).repr anchor)
    (member.candidate.newSourceEdge sheet).1.2 at hRel
  rw [member.vertexPartition_old, BalancedGlobal.Candidate.newSourceEdge_sheet] at hRel
  have hAnchor : (LimitChainCore.pasted member.candidate).left.Rel anchor
      ((LimitChainCore.pasted member.candidate).newEdge.repr sheet) := by
    simpa only [SheetPartition.Rel, SheetPartition.repr_idem] using hRel
  exact hAnchor.trans (((LimitChainCore.pasted member.candidate).edge_refines_left.rel
    ((LimitChainCore.pasted member.candidate).newEdge.rel_repr_left sheet)))

/-- A regrown occurrence at the `t₃` endpoint lies in its own old wall block. -/
theorem new_incident_fresh_rel (member : MemberShape profile) (anchor sheet : Fin degree)
    (hIncident : Incident member.candidate.datum (member.candidate.newSourceEdge sheet)
      (member.candidate.datum.sourceEndpoint (freshVertex target) anchor)) :
    (data.vertexPartition wall).Rel anchor sheet := by
  have hRel := ((incident_iff_target_mem_and_rel _ _ _).mp hIncident).2
  change (member.candidate.datum.vertexPartition (freshVertex target)).Rel
    ((member.candidate.datum.vertexPartition (freshVertex target)).repr anchor)
    (member.candidate.newSourceEdge sheet).1.2 at hRel
  rw [member.vertexPartition_fresh, BalancedGlobal.Candidate.newSourceEdge_sheet] at hRel
  have hAnchor : (data.vertexPartition wall).Rel anchor
      ((LimitChainCore.pasted member.candidate).newEdge.repr sheet) := by
    simpa only [SheetPartition.Rel, SheetPartition.repr_idem] using hRel
  refine hAnchor.trans ?_
  rw [← member.pasted_right_eq]
  exact ((LimitChainCore.pasted member.candidate).edge_refines_right.rel
    ((LimitChainCore.pasted member.candidate).newEdge.rel_repr_left sheet))

end MemberShape


/-! ## Divalent new endpoints: the regrown occurrence copies its neighbour -/

namespace MemberShape

variable {profile : W2R2SourceProfile.SourceProfile data star block}

/-- At a divalent `t₂` endpoint the regrown occurrence and the retained `t₂`
occurrence are pruned together. -/
theorem new_isDangling_iff_double (input : W2SourceInput data star)
    (member : MemberShape profile) (sheet : Fin degree)
    (hCard : Fintype.card (IncidentSourceEdge member.candidate.datum
      (member.candidate.datum.sourceEndpoint (oldVertex target wall) sheet)) = 2) :
    IsDangling member.candidate.datum (member.candidate.newSourceEdge sheet) ↔
      IsDangling data (data.sourceEdge (star.edge profile.doubleLabel) sheet) := by
  have hNew := LimitChainCore.newSourceEdge_incident_old (candidate := member.candidate) sheet
  have hOld := member.double_incident_canonical sheet
  have hDegree : vertex_degree member.candidate.datum.sourceGraph
      (member.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) = 2 := by
    rw [vertex_degree_sourceGraph_eq_card_incidentSourceEdge, hCard]
    norm_num
  have hNe : member.candidate.newSourceEdge sheet ≠
      member.candidate.oldSourceEdge (data.sourceEdge (star.edge profile.doubleLabel) sheet) :=
    (LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _).symm
  have hPruning := ResolutionPruning.isDangling_oldSourceEdge_iff member.candidate input.valid
    member.sourceGenus (data.sourceEdge (star.edge profile.doubleLabel) sheet)
  exact ⟨fun h ↦ hPruning.mp (isDangling_of_incident_of_vertex_degree_eq_two
      member.candidate.datum hNe hNew hOld hDegree h),
    fun h ↦ isDangling_of_incident_of_vertex_degree_eq_two member.candidate.datum hNe.symm
      hOld hNew hDegree (hPruning.mpr h)⟩

/-- At a divalent `t₃` endpoint the regrown occurrence and the retained `t₃`
occurrence are pruned together. -/
theorem new_isDangling_iff_single (input : W2SourceInput data star)
    (member : MemberShape profile) (sheet : Fin degree)
    (hCard : Fintype.card (IncidentSourceEdge member.candidate.datum
      (member.candidate.datum.sourceEndpoint (freshVertex target) sheet)) = 2) :
    IsDangling member.candidate.datum (member.candidate.newSourceEdge sheet) ↔
      IsDangling data (data.sourceEdge (star.edge profile.singleLabel) sheet) := by
  have hNew := LimitChainCore.newSourceEdge_incident_fresh (candidate := member.candidate) sheet
  have hOld := member.single_incident_canonical sheet
  have hDegree : vertex_degree member.candidate.datum.sourceGraph
      (member.candidate.datum.sourceEndpoint (freshVertex target) sheet) = 2 := by
    rw [vertex_degree_sourceGraph_eq_card_incidentSourceEdge, hCard]
    norm_num
  have hNe : member.candidate.newSourceEdge sheet ≠
      member.candidate.oldSourceEdge (data.sourceEdge (star.edge profile.singleLabel) sheet) :=
    (LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _).symm
  have hPruning := ResolutionPruning.isDangling_oldSourceEdge_iff member.candidate input.valid
    member.sourceGenus (data.sourceEdge (star.edge profile.singleLabel) sheet)
  exact ⟨fun h ↦ hPruning.mp (isDangling_of_incident_of_vertex_degree_eq_two
      member.candidate.datum hNe hNew hOld hDegree h),
    fun h ↦ isDangling_of_incident_of_vertex_degree_eq_two member.candidate.datum hNe.symm
      hOld hNew hDegree (hPruning.mpr h)⟩

theorem new_survives_of_double (input : W2SourceInput data star) (member : MemberShape profile)
    (sheet : Fin degree)
    (hCard : Fintype.card (IncidentSourceEdge member.candidate.datum
      (member.candidate.datum.sourceEndpoint (oldVertex target wall) sheet)) = 2)
    (hSurvives : ¬ IsDangling data (data.sourceEdge (star.edge profile.doubleLabel) sheet)) :
    ¬ IsDangling member.candidate.datum (member.candidate.newSourceEdge sheet) :=
  fun h ↦ hSurvives ((new_isDangling_iff_double input member sheet hCard).mp h)

theorem new_survives_of_single (input : W2SourceInput data star) (member : MemberShape profile)
    (sheet : Fin degree)
    (hCard : Fintype.card (IncidentSourceEdge member.candidate.datum
      (member.candidate.datum.sourceEndpoint (freshVertex target) sheet)) = 2)
    (hSurvives : ¬ IsDangling data (data.sourceEdge (star.edge profile.singleLabel) sheet)) :
    ¬ IsDangling member.candidate.datum (member.candidate.newSourceEdge sheet) :=
  fun h ↦ hSurvives ((new_isDangling_iff_single input member sheet hCard).mp h)

theorem new_stablePath_eq_double (input : W2SourceInput data star) (member : MemberShape profile)
    (sheet : Fin degree)
    (hCard : Fintype.card (IncidentSourceEdge member.candidate.datum
      (member.candidate.datum.sourceEndpoint (oldVertex target wall) sheet)) = 2)
    (hSurvives : ¬ IsDangling data (data.sourceEdge (star.edge profile.doubleLabel) sheet)) :
    NonDanglingEdge.stablePath
        ⟨member.candidate.newSourceEdge sheet,
          new_survives_of_double input member sheet hCard hSurvives⟩ =
      (retainedEdge member.candidate input.valid.1
        ⟨data.sourceEdge (star.edge profile.doubleLabel) sheet, hSurvives⟩).stablePath :=
  M11SplitRows.stablePath_eq_of_incident_card_two _
    (member.candidate.datum_valid input.valid).1 _ _
    (member.candidate.datum.sourceEndpoint (oldVertex target wall) sheet)
    (LimitChainCore.newSourceEdge_incident_old (candidate := member.candidate) sheet)
    (member.double_incident_canonical sheet) hCard

theorem new_stablePath_eq_single (input : W2SourceInput data star) (member : MemberShape profile)
    (sheet : Fin degree)
    (hCard : Fintype.card (IncidentSourceEdge member.candidate.datum
      (member.candidate.datum.sourceEndpoint (freshVertex target) sheet)) = 2)
    (hSurvives : ¬ IsDangling data (data.sourceEdge (star.edge profile.singleLabel) sheet)) :
    NonDanglingEdge.stablePath
        ⟨member.candidate.newSourceEdge sheet,
          new_survives_of_single input member sheet hCard hSurvives⟩ =
      (retainedEdge member.candidate input.valid.1
        ⟨data.sourceEdge (star.edge profile.singleLabel) sheet, hSurvives⟩).stablePath :=
  M11SplitRows.stablePath_eq_of_incident_card_two _
    (member.candidate.datum_valid input.valid).1 _ _
    (member.candidate.datum.sourceEndpoint (freshVertex target) sheet)
    (LimitChainCore.newSourceEdge_incident_fresh (candidate := member.candidate) sheet)
    (member.single_incident_canonical sheet) hCard

/-! ### The background, where every member looks the same -/

theorem background_isDangling_iff (input : W2SourceInput data star) (member : MemberShape profile)
    (sheet : Fin degree) (hBackground : ¬ (data.vertexPartition wall).Rel block.1 sheet)
    (label : Fin 2) :
    IsDangling member.candidate.datum (member.candidate.newSourceEdge sheet) ↔
      IsDangling data (data.sourceEdge (star.edge label) sheet) := by
  rcases (show label = profile.doubleLabel ∨ label = profile.singleLabel by
      have := profile.labels_ne; omega) with rfl | rfl
  · exact new_isDangling_iff_double input member sheet
      (member.card_incident_old_background input sheet hBackground)
  · exact new_isDangling_iff_single input member sheet
      (member.card_incident_fresh_background input sheet hBackground)

theorem background_survives (input : W2SourceInput data star) (member : MemberShape profile)
    (sheet : Fin degree) (hBackground : ¬ (data.vertexPartition wall).Rel block.1 sheet)
    (label : Fin 2)
    (hSurvives : ¬ IsDangling data (data.sourceEdge (star.edge label) sheet)) :
    ¬ IsDangling member.candidate.datum (member.candidate.newSourceEdge sheet) :=
  fun h ↦ hSurvives ((background_isDangling_iff input member sheet hBackground label).mp h)

theorem background_stablePath_eq (input : W2SourceInput data star) (member : MemberShape profile)
    (sheet : Fin degree) (hBackground : ¬ (data.vertexPartition wall).Rel block.1 sheet)
    (label : Fin 2)
    (hSurvives : ¬ IsDangling data (data.sourceEdge (star.edge label) sheet)) :
    NonDanglingEdge.stablePath
        ⟨member.candidate.newSourceEdge sheet,
          background_survives input member sheet hBackground label hSurvives⟩ =
      (retainedEdge member.candidate input.valid.1
        ⟨data.sourceEdge (star.edge label) sheet, hSurvives⟩).stablePath := by
  rcases (show label = profile.doubleLabel ∨ label = profile.singleLabel by
      have := profile.labels_ne; omega) with rfl | rfl
  · exact new_stablePath_eq_double input member sheet
      (member.card_incident_old_background input sheet hBackground) hSurvives
  · exact new_stablePath_eq_single input member sheet
      (member.card_incident_fresh_background input sheet hBackground) hSurvives

/-- The background regrown occurrence keeps the old wall block's index. -/
theorem background_index_eq (input : W2SourceInput data star) (member : MemberShape profile)
    (sheet : Fin degree) (hBackground : ¬ (data.vertexPartition wall).Rel block.1 sheet)
    (label : Fin 2) :
    member.candidate.datum.sourceEdgeIndex (member.candidate.newSourceEdge sheet) =
      data.sourceEdgeIndex (data.sourceEdge (star.edge label) sheet) := by
  rw [member.newSourceEdge_index_of_not_rel sheet hBackground,
    GluingDatum.sourceEdgeIndex_sourceEdge]
  exact (SheetPartition.blockCard_eq_of_refines_of_blockCountWithin_eq_one _ _
    (star.edgePartition_refines_wall data label) sheet
    (M11JoinedBackground.background_blockCount input profile label sheet hBackground)).symm

end MemberShape


/-! ## The `t₂` endpoint blocks inside `A₀` -/

namespace MemberShape

variable {profile : W2R2SourceProfile.SourceProfile data star block}

theorem pasted_left_rel_iff_of_rel (member : MemberShape profile) (first second : Fin degree)
    (hRel : (data.vertexPartition wall).Rel block.1 first) :
    (LimitChainCore.pasted member.candidate).left.Rel first second ↔
      member.fine.Rel first second := by
  rw [← SheetPartition.mem_block_iff, ← SheetPartition.mem_block_iff,
    LocalResolution.pasteLeft_block, member.resolution_repr_of_rel first hRel]
  rfl

theorem pasted_left_rel_iff_of_not_rel (member : MemberShape profile) (first second : Fin degree)
    (hRel : ¬ (data.vertexPartition wall).Rel block.1 first) :
    (LimitChainCore.pasted member.candidate).left.Rel first second ↔
      (data.vertexPartition wall).Rel first second := by
  rw [← SheetPartition.mem_block_iff, ← SheetPartition.mem_block_iff,
    LocalResolution.pasteLeft_block, member.resolution_repr_of_not_rel first hRel]
  rfl

/-- Two sheets of one fine block inside `A₀` name one `t₂` endpoint. -/
theorem sourceEndpoint_old_eq_of_fine (member : MemberShape profile) (first second : Fin degree)
    (hRel : (data.vertexPartition wall).Rel block.1 first)
    (hFine : member.fine.Rel first second) :
    member.candidate.datum.sourceEndpoint (oldVertex target wall) first =
      member.candidate.datum.sourceEndpoint (oldVertex target wall) second :=
  LimitChainCore.sourceEndpoint_old_eq_of_rel first second
    ((member.pasted_left_rel_iff_of_rel first second hRel).mpr hFine)

/-- The retained `t₂` occurrence through a sheet of `A₀` meets the `t₂` endpoint
over any sheet of its own fine block. -/
theorem double_incident_fine (member : MemberShape profile) (edge : data.SourceEdge)
    (hTarget : edge.1.1 = star.edge profile.doubleLabel) (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor)
    (hFine : member.fine.Rel anchor edge.1.2) :
    Incident member.candidate.datum (member.candidate.oldSourceEdge edge)
      (member.candidate.datum.sourceEndpoint (oldVertex target wall) anchor) :=
  member.double_incident edge hTarget anchor
    ((member.pasted_left_rel_iff_of_rel anchor edge.1.2 hAnchor).mpr hFine)

/-- What a retained occurrence at a `t₂` endpoint inside `A₀` must be. -/
theorem retained_incident_old_fine (member : MemberShape profile) (sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel block.1 sheet) (edge : data.SourceEdge)
    (hIncident : Incident member.candidate.datum (member.candidate.oldSourceEdge edge)
      (member.candidate.datum.sourceEndpoint (oldVertex target wall) sheet)) :
    edge.1.1 = star.edge profile.doubleLabel ∧ member.fine.Rel sheet edge.1.2 :=
  ⟨(member.retained_incident_old_data sheet edge hIncident).1,
    (member.pasted_left_rel_iff_of_rel sheet edge.1.2 hRel).mp
      (member.retained_incident_old_data sheet edge hIncident).2⟩

/-- A regrown occurrence at a `t₂` endpoint inside `A₀` lies in the same fine
block. -/
theorem new_incident_old_fine (member : MemberShape profile) (anchor sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel block.1 anchor)
    (hIncident : Incident member.candidate.datum (member.candidate.newSourceEdge sheet)
      (member.candidate.datum.sourceEndpoint (oldVertex target wall) anchor)) :
    member.fine.Rel anchor sheet :=
  (member.pasted_left_rel_iff_of_rel anchor sheet hRel).mp
    (member.new_incident_old_rel anchor sheet hIncident)

/-- The canonical `t₂` occurrence through the sheet of an actual `t₂`
occurrence is that occurrence. -/
theorem double_canonical (edge : data.SourceEdge)
    (hTarget : edge.1.1 = star.edge profile.doubleLabel) :
    data.sourceEdge (star.edge profile.doubleLabel) edge.1.2 = edge := by
  rw [← hTarget]; exact GluingDatum.sourceEdge_self data edge

theorem single_canonical (edge : data.SourceEdge)
    (hTarget : edge.1.1 = star.edge profile.singleLabel) :
    data.sourceEdge (star.edge profile.singleLabel) edge.1.2 = edge := by
  rw [← hTarget]; exact GluingDatum.sourceEdge_self data edge

end MemberShape


/-! ## Reading a surviving star -/

namespace MemberShape

variable {profile : W2R2SourceProfile.SourceProfile data star block}

theorem retained_survives (input : W2SourceInput data star) (member : MemberShape profile)
    (edge : NonDanglingEdge data) :
    ¬ IsDangling member.candidate.datum (member.candidate.oldSourceEdge edge.1) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge member.candidate input.valid.1 edge.1 edge.2

/-- Genus-preserving pruning keeps the dangling `e₄` dangling. -/
theorem deleted_dangles (input : W2SourceInput data star) (member : MemberShape profile) :
    IsDangling member.candidate.datum
      (member.candidate.oldSourceEdge profile.deleted.edge.1) :=
  (ResolutionPruning.isDangling_oldSourceEdge_iff member.candidate input.valid
    member.sourceGenus _).mpr profile.deleted.dangling

theorem trivalent_survives (input : W2SourceInput data star) (member : MemberShape profile)
    {vertex : member.candidate.datum.SourceVertex}
    (survivor deleted other : member.candidate.datum.SourceEdge)
    (hSurvivor : Incident member.candidate.datum survivor vertex)
    (hDeleted : Incident member.candidate.datum deleted vertex)
    (hOther : Incident member.candidate.datum other vertex)
    (hSurvivorSurvives : ¬ IsDangling member.candidate.datum survivor)
    (hDeletedDangles : IsDangling member.candidate.datum deleted)
    (hNe : deleted ≠ other)
    (hCard : Fintype.card (IncidentSourceEdge member.candidate.datum vertex) = 3) :
    ¬ IsDangling member.candidate.datum other :=
  M11SplitSurvival.survives_of_trivalent_of_deleted member.candidate.datum
    (member.candidate.datum_valid input.valid).1 vertex ⟨survivor, hSurvivor⟩
    ⟨deleted, hDeleted⟩ ⟨other, hOther⟩ hSurvivorSurvives hDeletedDangles
    (fun h ↦ hNe (congrArg Subtype.val h)) hCard

theorem trivalent_stablePath (input : W2SourceInput data star) (member : MemberShape profile)
    {vertex : member.candidate.datum.SourceVertex}
    (first second : NonDanglingEdge member.candidate.datum)
    (hFirst : Incident member.candidate.datum first.1 vertex)
    (hSecond : Incident member.candidate.datum second.1 vertex)
    (deleted : member.candidate.datum.SourceEdge)
    (hDeleted : Incident member.candidate.datum deleted vertex)
    (hDeletedDangles : IsDangling member.candidate.datum deleted)
    (hCard : Fintype.card (IncidentSourceEdge member.candidate.datum vertex) = 3) :
    first.stablePath = second.stablePath :=
  M11SplitSurvival.stablePath_eq_of_trivalent_deleted member.candidate.datum
    (member.candidate.datum_valid input.valid).1 first second vertex hFirst hSecond
    ⟨deleted, hDeleted⟩ hDeletedDangles hCard

end MemberShape

/-! ## The `A₀` half of the census -/

/-- What a member owes the row descent above the distinguished block `A₀`:
the old occurrence whose stable row each surviving regrown occurrence joins,
and the complete surviving star at every joining endpoint above `A₀`. -/
structure Census {profile : W2R2SourceProfile.SourceProfile data star block}
    (input : W2SourceInput data star) (member : MemberShape profile) where
  /-- The old occurrence represented by a regrown occurrence above `A₀`. -/
  rep : Fin degree → NonDanglingEdge data
  /-- Sheets carrying one regrown occurrence carry one representative. -/
  rep_congr : ∀ first second : Fin degree, (data.vertexPartition wall).Rel block.1 first →
    member.fine.Rel first second → rep first = rep second
  /-- A surviving regrown occurrence above `A₀` lies in its representative's row. -/
  rep_row : ∀ (sheet : Fin degree) (old : NonDanglingEdge data),
    (data.vertexPartition wall).Rel block.1 sheet → old = rep sheet →
    ∀ hSurvives : ¬ IsDangling member.candidate.datum (member.candidate.newSourceEdge sheet),
      NonDanglingEdge.stablePath
          (⟨member.candidate.newSourceEdge sheet, hSurvives⟩ :
            NonDanglingEdge member.candidate.datum) =
        (retainedEdge member.candidate input.valid.1 old).stablePath
  /-- A `t₂` endpoint above `A₀` of surviving valency two carries exactly one
  regrown occurrence and its representative. -/
  old_pair : ∀ sheet : Fin degree, (data.vertexPartition wall).Rel block.1 sheet →
    nonDanglingValency member.candidate.datum
        (member.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) = 2 →
    ∃ (other : Fin degree) (old : NonDanglingEdge data),
      (data.vertexPartition wall).Rel block.1 other ∧ old = rep other ∧
      nonDanglingIncident member.candidate.datum
          (member.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) =
        {member.candidate.newSourceEdge other, member.candidate.oldSourceEdge old.1}
  /-- The same at the `t₃` endpoint above `A₀`. -/
  fresh_pair : ∀ sheet : Fin degree, (data.vertexPartition wall).Rel block.1 sheet →
    nonDanglingValency member.candidate.datum
        (member.candidate.datum.sourceEndpoint (freshVertex target) sheet) = 2 →
    ∃ (other : Fin degree) (old : NonDanglingEdge data),
      (data.vertexPartition wall).Rel block.1 other ∧ old = rep other ∧
      nonDanglingIncident member.candidate.datum
          (member.candidate.datum.sourceEndpoint (freshVertex target) sheet) =
        {member.candidate.newSourceEdge other, member.candidate.oldSourceEdge old.1}


/-! ## The census of the two merging members -/

/-- **Base II.2.1.P and II.2.2.P, in one proof.**  Above `A₀` the member has two
`t₂` endpoints: the merged one, trivalent with the dangling `e₄`, and the other
one, divalent.  The `t₃` endpoint is a branch vertex. -/
noncomputable def mergeCensus {profile : W2R2SourceProfile.SourceProfile data star block}
    (shape : Shape profile) (input : W2SourceInput data star)
    (own other : IncidentSourceEdge data (WallBlock.sourceVertex data wall block))
    (hOwnTarget : own.1.1.1 = star.edge profile.doubleLabel)
    (hOtherTarget : other.1.1.1 = star.edge profile.doubleLabel)
    (hOwnSurvives : ¬ IsDangling data own.1) (hOtherSurvives : ¬ IsDangling data other.1)
    (hOwnExtra : ¬ (endpointPartition profile).Rel own.1.1.2 (extraSheet profile))
    (hOtherExtra : ¬ (endpointPartition profile).Rel other.1.1.2 (extraSheet profile))
    (hSeparate : ¬ (endpointPartition profile).Rel own.1.1.2 other.1.1.2)
    (hCovers : ∀ sheet : Fin degree, (data.vertexPartition wall).Rel block.1 sheet →
      (endpointPartition profile).Rel own.1.1.2 sheet ∨
        (endpointPartition profile).Rel other.1.1.2 sheet ∨
          (endpointPartition profile).Rel (extraSheet profile) sheet) :
    Census input (mergeShape profile own hOwnExtra) := by
  have hOwnRel : (data.vertexPartition wall).Rel block.1 own.1.1.2 := sheet_rel_of_incident own
  have hOtherRel : (data.vertexPartition wall).Rel block.1 other.1.1.2 :=
    sheet_rel_of_incident other
  have hThirdRel : (data.vertexPartition wall).Rel block.1 profile.third.1.1.2 :=
    sheet_rel_of_incident profile.third
  have hFineOwnExtra : (mergeShape profile own hOwnExtra).fine.Rel own.1.1.2
      (extraSheet profile) :=
    ((endpointPartition profile).mergeBlocks_rel_first_iff _ _ _ hOwnExtra).mpr (Or.inr rfl)
  have hFineNotOther : ¬ (mergeShape profile own hOwnExtra).fine.Rel own.1.1.2 other.1.1.2 := by
    intro h
    rcases ((endpointPartition profile).mergeBlocks_rel_first_iff _ _ _ hOwnExtra).mp h with h' | h'
    · exact hSeparate h'
    · exact hOtherExtra h'.symm
  have hCoverFine : ∀ sheet : Fin degree, (data.vertexPartition wall).Rel block.1 sheet →
      (mergeShape profile own hOwnExtra).fine.Rel own.1.1.2 sheet ∨
        (mergeShape profile own hOwnExtra).fine.Rel other.1.1.2 sheet := by
    intro sheet hSheet
    rcases hCovers sheet hSheet with h | h | h
    · exact Or.inl (((endpointPartition profile).mergeBlocks_rel_first_iff _ _ _ hOwnExtra).mpr
        (Or.inl h))
    · exact Or.inr ((SheetPartition.refines_mergeBlocks _ _ _ hOwnExtra).rel h)
    · exact Or.inl (((endpointPartition profile).mergeBlocks_rel_first_iff _ _ _ hOwnExtra).mpr
        (Or.inr h))
  have hCountOwn : (endpointPartition profile).blockCountWithin
      (mergeShape profile own hOwnExtra).fine own.1.1.2 = 2 := by
    show (endpointPartition profile).blockCountWithin
      ((endpointPartition profile).mergeBlocks own.1.1.2 (extraSheet profile) hOwnExtra)
        own.1.1.2 = 2
    rw [SheetPartition.mergeBlocks_blockCountWithin_first _ _
      (SheetPartition.Refines.refl _) _ _ hOwnExtra, SheetPartition.blockCountWithin_self,
      SheetPartition.blockCountWithin_self]
  have hCountOther : (endpointPartition profile).blockCountWithin
      (mergeShape profile own hOwnExtra).fine other.1.1.2 = 1 := by
    show (endpointPartition profile).blockCountWithin
      ((endpointPartition profile).mergeBlocks own.1.1.2 (extraSheet profile) hOwnExtra)
        other.1.1.2 = 1
    rw [SheetPartition.mergeBlocks_blockCountWithin_of_separate _ _ _ _ _ hOwnExtra
      (fun h ↦ hSeparate h.symm) hOtherExtra, SheetPartition.blockCountWithin_self]
  have hCardOwn : Fintype.card (IncidentSourceEdge
      (mergeShape profile own hOwnExtra).candidate.datum
      ((mergeShape profile own hOwnExtra).candidate.datum.sourceEndpoint
        (oldVertex target wall) own.1.1.2)) = 3 := by
    rw [(mergeShape profile own hOwnExtra).card_incident_old_selected own.1.1.2 hOwnRel, hCountOwn]
  have hCardOther : Fintype.card (IncidentSourceEdge
      (mergeShape profile own hOwnExtra).candidate.datum
      ((mergeShape profile own hOwnExtra).candidate.datum.sourceEndpoint
        (oldVertex target wall) other.1.1.2)) = 2 := by
    rw [(mergeShape profile own hOwnExtra).card_incident_old_selected other.1.1.2 hOtherRel,
      hCountOther]
  have hOwnIncident := (mergeShape profile own hOwnExtra).double_incident_fine own.1 hOwnTarget
    own.1.1.2 hOwnRel rfl
  have hOtherIncident := (mergeShape profile own hOwnExtra).double_incident_fine other.1
    hOtherTarget other.1.1.2 hOtherRel rfl
  have hDeletedIncident := (mergeShape profile own hOwnExtra).double_incident_fine
    profile.deleted.edge.1 shape.deleted_double own.1.1.2 hOwnRel hFineOwnExtra
  have hNewOwnIncident := LimitChainCore.newSourceEdge_incident_old
    (candidate := (mergeShape profile own hOwnExtra).candidate) own.1.1.2
  have hNewOtherIncident := LimitChainCore.newSourceEdge_incident_old
    (candidate := (mergeShape profile own hOwnExtra).candidate) other.1.1.2
  have hOwnNeDeleted : (mergeShape profile own hOwnExtra).candidate.oldSourceEdge own.1 ≠
      (mergeShape profile own hOwnExtra).candidate.oldSourceEdge profile.deleted.edge.1 := by
    intro h
    refine hOwnSurvives ?_
    rw [ResolutionCut.oldSourceEdge_injective _ h]
    exact profile.deleted.dangling
  have hNewOwnSurvives : ¬ IsDangling (mergeShape profile own hOwnExtra).candidate.datum
      ((mergeShape profile own hOwnExtra).candidate.newSourceEdge own.1.1.2) :=
    (mergeShape profile own hOwnExtra).trivalent_survives input _ _ _ hOwnIncident hDeletedIncident
      hNewOwnIncident
      ((mergeShape profile own hOwnExtra).retained_survives input ⟨own.1, hOwnSurvives⟩)
      ((mergeShape profile own hOwnExtra).deleted_dangles input)
      (LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _) hCardOwn
  have hNewOwnRow : NonDanglingEdge.stablePath
      (⟨(mergeShape profile own hOwnExtra).candidate.newSourceEdge own.1.1.2, hNewOwnSurvives⟩ :
        NonDanglingEdge (mergeShape profile own hOwnExtra).candidate.datum) =
      (retainedEdge (mergeShape profile own hOwnExtra).candidate input.valid.1
        ⟨own.1, hOwnSurvives⟩).stablePath :=
    (mergeShape profile own hOwnExtra).trivalent_stablePath input _ _ hNewOwnIncident hOwnIncident
      _ hDeletedIncident ((mergeShape profile own hOwnExtra).deleted_dangles input) hCardOwn
  have hStarOwn : nonDanglingIncident (mergeShape profile own hOwnExtra).candidate.datum
      ((mergeShape profile own hOwnExtra).candidate.datum.sourceEndpoint
        (oldVertex target wall) own.1.1.2) =
      {(mergeShape profile own hOwnExtra).candidate.newSourceEdge own.1.1.2,
        (mergeShape profile own hOwnExtra).candidate.oldSourceEdge own.1} :=
    LimitChainCore.nonDanglingIncident_pair_of_card_three _ hNewOwnIncident hOwnIncident
      hDeletedIncident (Ne.symm (LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _))
      (Ne.symm (LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _)) hOwnNeDeleted
      hNewOwnSurvives
      ((mergeShape profile own hOwnExtra).retained_survives input ⟨own.1, hOwnSurvives⟩)
      ((mergeShape profile own hOwnExtra).deleted_dangles input) hCardOwn
  have hOtherCanonical : data.sourceEdge (star.edge profile.doubleLabel) other.1.1.2 = other.1 :=
    MemberShape.double_canonical other.1 hOtherTarget
  have hOtherSurvivesCanonical :
      ¬ IsDangling data (data.sourceEdge (star.edge profile.doubleLabel) other.1.1.2) := by
    rw [hOtherCanonical]; exact hOtherSurvives
  have hNewOtherSurvives := (mergeShape profile own hOwnExtra).new_survives_of_double input
    other.1.1.2 hCardOther hOtherSurvivesCanonical
  have hRetEq : retainedEdge (mergeShape profile own hOwnExtra).candidate input.valid.1
        ⟨data.sourceEdge (star.edge profile.doubleLabel) other.1.1.2, hOtherSurvivesCanonical⟩ =
      retainedEdge (mergeShape profile own hOwnExtra).candidate input.valid.1
        ⟨other.1, hOtherSurvives⟩ :=
    congrArg (retainedEdge (mergeShape profile own hOwnExtra).candidate input.valid.1)
      (Subtype.ext hOtherCanonical)
  have hNewOtherRow : NonDanglingEdge.stablePath
      (⟨(mergeShape profile own hOwnExtra).candidate.newSourceEdge other.1.1.2,
        hNewOtherSurvives⟩ : NonDanglingEdge (mergeShape profile own hOwnExtra).candidate.datum) =
      (retainedEdge (mergeShape profile own hOwnExtra).candidate input.valid.1
        ⟨other.1, hOtherSurvives⟩).stablePath := by
    rw [← hRetEq]
    exact (mergeShape profile own hOwnExtra).new_stablePath_eq_double input other.1.1.2 hCardOther
      hOtherSurvivesCanonical
  have hStarOther : nonDanglingIncident (mergeShape profile own hOwnExtra).candidate.datum
      ((mergeShape profile own hOwnExtra).candidate.datum.sourceEndpoint
        (oldVertex target wall) other.1.1.2) =
      {(mergeShape profile own hOwnExtra).candidate.newSourceEdge other.1.1.2,
        (mergeShape profile own hOwnExtra).candidate.oldSourceEdge other.1} :=
    LimitChainCore.nonDanglingIncident_pair_of_card_two _ hNewOtherIncident hOtherIncident
      (Ne.symm (LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _)) hNewOtherSurvives
      ((mergeShape profile own hOwnExtra).retained_survives input ⟨other.1, hOtherSurvives⟩)
      hCardOther
  have hNewNe : (mergeShape profile own hOwnExtra).candidate.newSourceEdge own.1.1.2 ≠
      (mergeShape profile own hOwnExtra).candidate.newSourceEdge other.1.1.2 := by
    intro h
    exact hFineNotOther
      (((mergeShape profile own hOwnExtra).newSourceEdge_eq_iff_fine own.1.1.2 other.1.1.2
        hOwnRel).mp h)
  refine {
    rep := fun sheet ↦ if (mergeShape profile own hOwnExtra).fine.Rel own.1.1.2 sheet then
      (⟨own.1, hOwnSurvives⟩ : NonDanglingEdge data) else ⟨other.1, hOtherSurvives⟩
    rep_congr := ?_
    rep_row := ?_
    old_pair := ?_
    fresh_pair := ?_ }
  · intro first second _ hFine
    by_cases h : (mergeShape profile own hOwnExtra).fine.Rel own.1.1.2 first
    · exact (ite_eq_left h).trans (ite_eq_left (show (mergeShape profile own hOwnExtra).fine.Rel own.1.1.2
        second from h.trans hFine)).symm
    · exact (ite_eq_right h).trans (ite_eq_right (show ¬ (mergeShape profile own hOwnExtra).fine.Rel own.1.1.2
        second from fun h' ↦ h (h'.trans hFine.symm))).symm
  · intro sheet old hRel hOld hSurvives
    by_cases h : (mergeShape profile own hOwnExtra).fine.Rel own.1.1.2 sheet
    · have hOldEq : old = (⟨own.1, hOwnSurvives⟩ : NonDanglingEdge data) :=
        hOld.trans (ite_eq_left h)
      have hEq : (mergeShape profile own hOwnExtra).candidate.newSourceEdge sheet =
          (mergeShape profile own hOwnExtra).candidate.newSourceEdge own.1.1.2 :=
        ((mergeShape profile own hOwnExtra).newSourceEdge_eq_iff_fine sheet own.1.1.2 hRel).mpr
          h.symm
      rw [hOldEq]
      exact Eq.trans (congrArg NonDanglingEdge.stablePath (Subtype.ext hEq)) hNewOwnRow
    · have hOldEq : old = (⟨other.1, hOtherSurvives⟩ : NonDanglingEdge data) :=
        hOld.trans (ite_eq_right h)
      rcases hCoverFine sheet hRel with h' | h'
      · exact absurd h' h
      have hEq : (mergeShape profile own hOwnExtra).candidate.newSourceEdge sheet =
          (mergeShape profile own hOwnExtra).candidate.newSourceEdge other.1.1.2 :=
        ((mergeShape profile own hOwnExtra).newSourceEdge_eq_iff_fine sheet other.1.1.2 hRel).mpr
          h'.symm
      rw [hOldEq]
      exact Eq.trans (congrArg NonDanglingEdge.stablePath (Subtype.ext hEq)) hNewOtherRow
  · intro sheet hRel _
    rcases hCoverFine sheet hRel with h | h
    · refine ⟨own.1.1.2, ⟨own.1, hOwnSurvives⟩, hOwnRel,
        (ite_eq_left (show (mergeShape profile own hOwnExtra).fine.Rel own.1.1.2 own.1.1.2
          from rfl)).symm, ?_⟩
      rw [(mergeShape profile own hOwnExtra).sourceEndpoint_old_eq_of_fine own.1.1.2 sheet hOwnRel
        h] at hStarOwn
      exact hStarOwn
    · refine ⟨other.1.1.2, ⟨other.1, hOtherSurvives⟩, hOtherRel,
        (ite_eq_right hFineNotOther).symm, ?_⟩
      rw [(mergeShape profile own hOwnExtra).sourceEndpoint_old_eq_of_fine other.1.1.2 sheet
        hOtherRel h] at hStarOther
      exact hStarOther
  · intro sheet hRel hValency
    exfalso
    have hVertexEq := (mergeShape profile own hOwnExtra).sourceEndpoint_fresh_eq_of_rel
      own.1.1.2 sheet (hOwnRel.symm.trans hRel)
    have hThirdIncident := (mergeShape profile own hOwnExtra).single_incident profile.third.1
      profile.third_target own.1.1.2 (hOwnRel.symm.trans hThirdRel)
    have hNewOwnFresh := LimitChainCore.newSourceEdge_incident_fresh
      (candidate := (mergeShape profile own hOwnExtra).candidate) own.1.1.2
    have hNewOtherFresh := LimitChainCore.newSourceEdge_incident_fresh
      (candidate := (mergeShape profile own hOwnExtra).candidate) other.1.1.2
    rw [(mergeShape profile own hOwnExtra).sourceEndpoint_fresh_eq_of_rel other.1.1.2 own.1.1.2
      (hOtherRel.symm.trans hOwnRel)] at hNewOtherFresh
    have hSubset : ({(mergeShape profile own hOwnExtra).candidate.newSourceEdge own.1.1.2,
        (mergeShape profile own hOwnExtra).candidate.newSourceEdge other.1.1.2,
        (mergeShape profile own hOwnExtra).candidate.oldSourceEdge profile.third.1} :
          Finset (mergeShape profile own hOwnExtra).candidate.datum.SourceEdge) ⊆
        nonDanglingIncident (mergeShape profile own hOwnExtra).candidate.datum
          ((mergeShape profile own hOwnExtra).candidate.datum.sourceEndpoint
            (freshVertex target) own.1.1.2) := by
      intro edge hEdge
      simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
      rcases hEdge with rfl | rfl | rfl
      · exact (mem_nonDanglingIncident _ _ _).mpr ⟨hNewOwnSurvives, hNewOwnFresh⟩
      · exact (mem_nonDanglingIncident _ _ _).mpr ⟨hNewOtherSurvives, hNewOtherFresh⟩
      · exact (mem_nonDanglingIncident _ _ _).mpr
          ⟨(mergeShape profile own hOwnExtra).retained_survives input
            ⟨profile.third.1, profile.third_survives⟩, hThirdIncident⟩
    have hCount := Finset.card_le_card hSubset
    rw [← hVertexEq] at hValency
    have hNeAC : (mergeShape profile own hOwnExtra).candidate.newSourceEdge own.1.1.2 ≠
        (mergeShape profile own hOwnExtra).candidate.oldSourceEdge profile.third.1 :=
      Ne.symm (LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _)
    have hNeBC : (mergeShape profile own hOwnExtra).candidate.newSourceEdge other.1.1.2 ≠
        (mergeShape profile own hOwnExtra).candidate.oldSourceEdge profile.third.1 :=
      Ne.symm (LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _)
    rw [Finset.card_insert_of_notMem (by simp [hNewNe, hNeAC]), Finset.card_pair hNeBC,
      card_nonDanglingIncident, hValency] at hCount
    omega


/-! ## The census of the third member -/

/-- The `t₂` endpoint blocks of `M⁽³⁾` inside `A₀`: everything but the dangling
sheet lies in one block, and the dangling sheet is alone. -/
theorem thirdFine_rel_iff {profile : W2R2SourceProfile.SourceProfile data star block}
    (shape : Shape profile) (sheet : Fin degree) :
    (thirdFine shape).Rel (firstSheet profile) sheet ↔
      (data.vertexPartition wall).Rel block.1 sheet ∧ sheet ≠ extraSheet profile := by
  rw [← SheetPartition.mem_block_iff, (data.vertexPartition wall).detachSheet_block_remainder
    (extraSheet profile) (firstSheet profile) (extra_ne_first shape) (wall_extra_first profile),
    Finset.mem_erase, SheetPartition.mem_block_iff]
  exact ⟨fun h ↦ ⟨(extraSheet_rel profile).trans h.2, h.1⟩,
    fun h ↦ ⟨h.2, (extraSheet_rel profile).symm.trans h.1⟩⟩

/-- **Base II.1.P.**  Above `A₀` the `t₂` endpoint splits into the trivalent
vertex carrying `e₁`, `e₂` and the new occurrence, and the entirely pruned
vertex over the dangling singleton; the `t₃` endpoint is divalent and joins the
surviving new occurrence to `e₃`. -/
noncomputable def thirdCensus {profile : W2R2SourceProfile.SourceProfile data star block}
    (shape : Shape profile) (input : W2SourceInput data star) :
    Census input (thirdShape shape) := by
  have hFirstRel : (data.vertexPartition wall).Rel block.1 (firstSheet profile) :=
    firstSheet_rel profile
  have hSecondRel : (data.vertexPartition wall).Rel block.1 (secondSheet profile) :=
    secondSheet_rel profile
  have hExtraRel : (data.vertexPartition wall).Rel block.1 (extraSheet profile) :=
    extraSheet_rel profile
  have hThirdRel : (data.vertexPartition wall).Rel block.1 profile.third.1.1.2 :=
    sheet_rel_of_incident profile.third
  have hFineSecond : (thirdShape shape).fine.Rel (firstSheet profile) (secondSheet profile) :=
    (thirdFine_rel_iff shape (secondSheet profile)).mpr
      ⟨hSecondRel, fun h ↦ extra_ne_second shape h.symm⟩
  have hExtraBlock : (thirdShape shape).fine.block (extraSheet profile) = {extraSheet profile} :=
    (data.vertexPartition wall).detachSheet_block_single (extraSheet profile) (firstSheet profile)
      (extra_ne_first shape) (wall_extra_first profile)
  have hCountExtra : (endpointPartition profile).blockCountWithin (thirdShape shape).fine
      (extraSheet profile) = 1 :=
    SheetPartition.blockCountWithin_eq_one_of_block_eq_singleton _ _ _ hExtraBlock
  have hCountFirst : (endpointPartition profile).blockCountWithin (thirdShape shape).fine
      (firstSheet profile) = 2 := by
    refine blockCountWithin_eq_two _ _ (firstSheet profile) (secondSheet profile)
      (firstSheet profile) rfl hFineSecond ?_ (first_second_separate profile)
    intro sheet hSheet
    have hData := (thirdFine_rel_iff shape sheet).mp hSheet
    rcases endpointPartition_covers shape sheet hData.1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (Finset.mem_singleton.mp (by
        rw [← extraSheet_block shape]
        exact (SheetPartition.mem_block_iff _ _ _).mpr h)) hData.2
  have hCardExtra : Fintype.card (IncidentSourceEdge (thirdShape shape).candidate.datum
      ((thirdShape shape).candidate.datum.sourceEndpoint (oldVertex target wall)
        (extraSheet profile))) = 2 := by
    rw [(thirdShape shape).card_incident_old_selected (extraSheet profile) hExtraRel, hCountExtra]
  have hCardFirstOld : Fintype.card (IncidentSourceEdge (thirdShape shape).candidate.datum
      ((thirdShape shape).candidate.datum.sourceEndpoint (oldVertex target wall)
        (firstSheet profile))) = 3 := by
    rw [(thirdShape shape).card_incident_old_selected (firstSheet profile) hFirstRel, hCountFirst]
  have hCardFresh : Fintype.card (IncidentSourceEdge (thirdShape shape).candidate.datum
      ((thirdShape shape).candidate.datum.sourceEndpoint (freshVertex target)
        (firstSheet profile))) = 3 := by
    rw [(thirdShape shape).card_incident_fresh_selected shape (firstSheet profile) hFirstRel]
    exact congrArg (· + 1)
      (thirdMember_blockCountWithin shape (firstSheet profile) hFirstRel).2.1
  have hDeletedCanonical : data.sourceEdge (star.edge profile.doubleLabel) (extraSheet profile) =
      profile.deleted.edge.1 := MemberShape.double_canonical _ shape.deleted_double
  have hNewExtraDangles : IsDangling (thirdShape shape).candidate.datum
      ((thirdShape shape).candidate.newSourceEdge (extraSheet profile)) := by
    refine ((thirdShape shape).new_isDangling_iff_double input (extraSheet profile)
      hCardExtra).mpr ?_
    rw [hDeletedCanonical]
    exact profile.deleted.dangling
  have hNewExtraNeFirst : (thirdShape shape).candidate.newSourceEdge (extraSheet profile) ≠
      (thirdShape shape).candidate.newSourceEdge (firstSheet profile) := by
    intro h
    have hRel := ((thirdShape shape).newSourceEdge_eq_iff_fine (extraSheet profile)
      (firstSheet profile) hExtraRel).mp h
    exact (extra_ne_first shape)
      ((SheetPartition.detachSheet_rel_single_iff (data.vertexPartition wall) (extraSheet profile)
        (firstSheet profile) (firstSheet profile) (extra_ne_first shape)
        (wall_extra_first profile)).mp hRel)
  have hThirdIncident := (thirdShape shape).single_incident profile.third.1 profile.third_target
    (firstSheet profile) (hFirstRel.symm.trans hThirdRel)
  have hNewFirstFresh := LimitChainCore.newSourceEdge_incident_fresh
    (candidate := (thirdShape shape).candidate) (firstSheet profile)
  have hNewExtraFresh := LimitChainCore.newSourceEdge_incident_fresh
    (candidate := (thirdShape shape).candidate) (extraSheet profile)
  rw [(thirdShape shape).sourceEndpoint_fresh_eq_of_rel (extraSheet profile) (firstSheet profile)
    (hExtraRel.symm.trans hFirstRel)] at hNewExtraFresh
  have hNewFirstSurvives : ¬ IsDangling (thirdShape shape).candidate.datum
      ((thirdShape shape).candidate.newSourceEdge (firstSheet profile)) :=
    (thirdShape shape).trivalent_survives input _ _ _ hThirdIncident hNewExtraFresh hNewFirstFresh
      ((thirdShape shape).retained_survives input ⟨profile.third.1, profile.third_survives⟩)
      hNewExtraDangles hNewExtraNeFirst hCardFresh
  have hNewFirstRow : NonDanglingEdge.stablePath
      (⟨(thirdShape shape).candidate.newSourceEdge (firstSheet profile), hNewFirstSurvives⟩ :
        NonDanglingEdge (thirdShape shape).candidate.datum) =
      (retainedEdge (thirdShape shape).candidate input.valid.1
        ⟨profile.third.1, profile.third_survives⟩).stablePath :=
    (thirdShape shape).trivalent_stablePath input _ _ hNewFirstFresh hThirdIncident _
      hNewExtraFresh hNewExtraDangles hCardFresh
  have hStarFresh : nonDanglingIncident (thirdShape shape).candidate.datum
      ((thirdShape shape).candidate.datum.sourceEndpoint (freshVertex target)
        (firstSheet profile)) =
      {(thirdShape shape).candidate.newSourceEdge (firstSheet profile),
        (thirdShape shape).candidate.oldSourceEdge profile.third.1} :=
    LimitChainCore.nonDanglingIncident_pair_of_card_three _ hNewFirstFresh hThirdIncident
      hNewExtraFresh (LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _).symm
      (Ne.symm hNewExtraNeFirst) (LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _)
      hNewFirstSurvives
      ((thirdShape shape).retained_survives input ⟨profile.third.1, profile.third_survives⟩)
      hNewExtraDangles hCardFresh
  refine {
    rep := fun _ ↦ ⟨profile.third.1, profile.third_survives⟩
    rep_congr := fun _ _ _ _ ↦ rfl
    rep_row := ?_
    old_pair := ?_
    fresh_pair := ?_ }
  · intro sheet old hRel hOld hSurvives
    have hNe : sheet ≠ extraSheet profile := by
      intro hEq
      refine hSurvives ?_
      rw [hEq]
      exact hNewExtraDangles
    have hFine : (thirdShape shape).fine.Rel (firstSheet profile) sheet :=
      (thirdFine_rel_iff shape sheet).mpr ⟨hRel, hNe⟩
    have hEq : (thirdShape shape).candidate.newSourceEdge sheet =
        (thirdShape shape).candidate.newSourceEdge (firstSheet profile) :=
      ((thirdShape shape).newSourceEdge_eq_iff_fine sheet (firstSheet profile) hRel).mpr hFine.symm
    rw [hOld]
    exact Eq.trans (congrArg NonDanglingEdge.stablePath (Subtype.ext hEq)) hNewFirstRow
  · intro sheet hRel hValency
    exfalso
    by_cases hNe : sheet = extraSheet profile
    · subst hNe
      have hDeletedIncident := (thirdShape shape).double_incident_fine profile.deleted.edge.1
        shape.deleted_double (extraSheet profile) hExtraRel rfl
      have hNewIncident := LimitChainCore.newSourceEdge_incident_old
        (candidate := (thirdShape shape).candidate) (extraSheet profile)
      have hEmpty := LimitChainCore.nonDanglingIncident_empty_of_card_two
        (thirdShape shape).candidate.datum hDeletedIncident hNewIncident
        (LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _)
        ((thirdShape shape).deleted_dangles input) hNewExtraDangles hCardExtra
      rw [← card_nonDanglingIncident, hEmpty] at hValency
      simp at hValency
    · have hFine : (thirdShape shape).fine.Rel (firstSheet profile) sheet :=
        (thirdFine_rel_iff shape sheet).mpr ⟨hRel, hNe⟩
      rw [← (thirdShape shape).sourceEndpoint_old_eq_of_fine (firstSheet profile) sheet hFirstRel
        hFine] at hValency
      have hFirstIncident := (thirdShape shape).double_incident_fine profile.first.1
        profile.first_target (firstSheet profile) hFirstRel rfl
      have hSecondIncident := (thirdShape shape).double_incident_fine profile.second.1
        profile.second_target (firstSheet profile) hFirstRel hFineSecond
      have hNewIncident := LimitChainCore.newSourceEdge_incident_old
        (candidate := (thirdShape shape).candidate) (firstSheet profile)
      have hNewFirstOldSurvives : ¬ IsDangling (thirdShape shape).candidate.datum
          ((thirdShape shape).candidate.newSourceEdge (firstSheet profile)) := hNewFirstSurvives
      have hSubset : ({(thirdShape shape).candidate.oldSourceEdge profile.first.1,
          (thirdShape shape).candidate.oldSourceEdge profile.second.1,
          (thirdShape shape).candidate.newSourceEdge (firstSheet profile)} :
            Finset (thirdShape shape).candidate.datum.SourceEdge) ⊆
          nonDanglingIncident (thirdShape shape).candidate.datum
            ((thirdShape shape).candidate.datum.sourceEndpoint (oldVertex target wall)
              (firstSheet profile)) := by
        intro edge hEdge
        simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
        rcases hEdge with rfl | rfl | rfl
        · exact (mem_nonDanglingIncident _ _ _).mpr
            ⟨(thirdShape shape).retained_survives input
              ⟨profile.first.1, profile.first_survives⟩, hFirstIncident⟩
        · exact (mem_nonDanglingIncident _ _ _).mpr
            ⟨(thirdShape shape).retained_survives input
              ⟨profile.second.1, profile.second_survives⟩, hSecondIncident⟩
        · exact (mem_nonDanglingIncident _ _ _).mpr ⟨hNewFirstOldSurvives, hNewIncident⟩
      have hCount := Finset.card_le_card hSubset
      have hNeAB : (thirdShape shape).candidate.oldSourceEdge profile.first.1 ≠
          (thirdShape shape).candidate.oldSourceEdge profile.second.1 := by
        intro h
        exact profile.first_ne_second
          (Subtype.ext (ResolutionCut.oldSourceEdge_injective _ h))
      have hNeAC : (thirdShape shape).candidate.oldSourceEdge profile.first.1 ≠
          (thirdShape shape).candidate.newSourceEdge (firstSheet profile) :=
        LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _
      have hNeBC : (thirdShape shape).candidate.oldSourceEdge profile.second.1 ≠
          (thirdShape shape).candidate.newSourceEdge (firstSheet profile) :=
        LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _
      rw [Finset.card_insert_of_notMem (by simp [hNeAB, hNeAC]), Finset.card_pair hNeBC,
        card_nonDanglingIncident, hValency] at hCount
      omega
  · intro sheet hRel _
    refine ⟨firstSheet profile, ⟨profile.third.1, profile.third_survives⟩, hFirstRel, rfl,
      ?_⟩
    rw [← (thirdShape shape).sourceEndpoint_fresh_eq_of_rel (firstSheet profile) sheet
      (hFirstRel.symm.trans hRel)]
    exact hStarFresh


/-! ## Figure 35's three censuses -/

/-- `M⁽¹⁾`'s census: the dangling sheet joins `e₁`. -/
noncomputable def firstCensus {profile : W2R2SourceProfile.SourceProfile data star block}
    (shape : Shape profile) (input : W2SourceInput data star) :
    Census input (firstShape shape) :=
  mergeCensus shape input profile.first profile.second profile.first_target profile.second_target
    profile.first_survives profile.second_survives (first_extra_separate shape)
    (second_extra_separate shape) (first_second_separate profile)
    (endpointPartition_covers shape)

/-- `M⁽²⁾`'s census: the dangling sheet joins `e₂`. -/
noncomputable def secondCensus {profile : W2R2SourceProfile.SourceProfile data star block}
    (shape : Shape profile) (input : W2SourceInput data star) :
    Census input (secondShape shape) :=
  mergeCensus shape input profile.second profile.first profile.second_target profile.first_target
    profile.second_survives profile.first_survives (second_extra_separate shape)
    (first_extra_separate shape) (fun h ↦ first_second_separate profile h.symm)
    (fun sheet hSheet ↦ by
      rcases endpointPartition_covers shape sheet hSheet with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h))


/-! ## The two fine blocks above `A₀`, named

The regrown column of a member is a sum over the blocks of its new-edge
partition.  Above `A₀` there are exactly two, and these are their anchors,
their survival status and their representatives. -/

section Anchors

variable {profile : W2R2SourceProfile.SourceProfile data star block}

theorem mergeShape_fine_rel_extra
    (own : IncidentSourceEdge data (WallBlock.sourceVertex data wall block))
    (hOwnExtra : ¬ (endpointPartition profile).Rel own.1.1.2 (extraSheet profile)) :
    (mergeShape profile own hOwnExtra).fine.Rel own.1.1.2 (extraSheet profile) :=
  ((endpointPartition profile).mergeBlocks_rel_first_iff _ _ _ hOwnExtra).mpr (Or.inr rfl)

theorem mergeShape_fine_not_rel
    (own other : IncidentSourceEdge data (WallBlock.sourceVertex data wall block))
    (hOwnExtra : ¬ (endpointPartition profile).Rel own.1.1.2 (extraSheet profile))
    (hOtherExtra : ¬ (endpointPartition profile).Rel other.1.1.2 (extraSheet profile))
    (hSeparate : ¬ (endpointPartition profile).Rel own.1.1.2 other.1.1.2) :
    ¬ (mergeShape profile own hOwnExtra).fine.Rel own.1.1.2 other.1.1.2 := by
  intro h
  rcases ((endpointPartition profile).mergeBlocks_rel_first_iff _ _ _ hOwnExtra).mp h with h' | h'
  · exact hSeparate h'
  · exact hOtherExtra h'.symm

theorem mergeShape_fine_cover
    (own other : IncidentSourceEdge data (WallBlock.sourceVertex data wall block))
    (hOwnExtra : ¬ (endpointPartition profile).Rel own.1.1.2 (extraSheet profile))
    (hCovers : ∀ sheet : Fin degree, (data.vertexPartition wall).Rel block.1 sheet →
      (endpointPartition profile).Rel own.1.1.2 sheet ∨
        (endpointPartition profile).Rel other.1.1.2 sheet ∨
          (endpointPartition profile).Rel (extraSheet profile) sheet)
    (sheet : Fin degree) (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    (mergeShape profile own hOwnExtra).fine.Rel own.1.1.2 sheet ∨
      (mergeShape profile own hOwnExtra).fine.Rel other.1.1.2 sheet := by
  rcases hCovers sheet hSheet with h | h | h
  · exact Or.inl (((endpointPartition profile).mergeBlocks_rel_first_iff _ _ _ hOwnExtra).mpr
      (Or.inl h))
  · exact Or.inr ((SheetPartition.refines_mergeBlocks _ _ _ hOwnExtra).rel h)
  · exact Or.inl (((endpointPartition profile).mergeBlocks_rel_first_iff _ _ _ hOwnExtra).mpr
      (Or.inr h))

theorem mergeShape_cardOwn
    (own : IncidentSourceEdge data (WallBlock.sourceVertex data wall block))
    (hOwnExtra : ¬ (endpointPartition profile).Rel own.1.1.2 (extraSheet profile)) :
    Fintype.card (IncidentSourceEdge (mergeShape profile own hOwnExtra).candidate.datum
      ((mergeShape profile own hOwnExtra).candidate.datum.sourceEndpoint
        (oldVertex target wall) own.1.1.2)) = 3 := by
  rw [(mergeShape profile own hOwnExtra).card_incident_old_selected own.1.1.2
    (sheet_rel_of_incident own)]
  show 1 + (endpointPartition profile).blockCountWithin
    ((endpointPartition profile).mergeBlocks own.1.1.2 (extraSheet profile) hOwnExtra)
      own.1.1.2 = 3
  rw [SheetPartition.mergeBlocks_blockCountWithin_first _ _ (SheetPartition.Refines.refl _) _ _
    hOwnExtra, SheetPartition.blockCountWithin_self, SheetPartition.blockCountWithin_self]

theorem mergeShape_cardOther
    (own other : IncidentSourceEdge data (WallBlock.sourceVertex data wall block))
    (hOwnExtra : ¬ (endpointPartition profile).Rel own.1.1.2 (extraSheet profile))
    (hOtherExtra : ¬ (endpointPartition profile).Rel other.1.1.2 (extraSheet profile))
    (hSeparate : ¬ (endpointPartition profile).Rel own.1.1.2 other.1.1.2) :
    Fintype.card (IncidentSourceEdge (mergeShape profile own hOwnExtra).candidate.datum
      ((mergeShape profile own hOwnExtra).candidate.datum.sourceEndpoint
        (oldVertex target wall) other.1.1.2)) = 2 := by
  rw [(mergeShape profile own hOwnExtra).card_incident_old_selected other.1.1.2
    (sheet_rel_of_incident other)]
  show 1 + (endpointPartition profile).blockCountWithin
    ((endpointPartition profile).mergeBlocks own.1.1.2 (extraSheet profile) hOwnExtra)
      other.1.1.2 = 2
  rw [SheetPartition.mergeBlocks_blockCountWithin_of_separate _ _ _ _ _ hOwnExtra
    (fun h ↦ hSeparate h.symm) hOtherExtra, SheetPartition.blockCountWithin_self]

/-- The merged block's regrown occurrence survives: its `t₂` endpoint is
trivalent with the dangling `e₄`. -/
theorem mergeShape_new_own_survives (shape : Shape profile) (input : W2SourceInput data star)
    (own : IncidentSourceEdge data (WallBlock.sourceVertex data wall block))
    (hOwnTarget : own.1.1.1 = star.edge profile.doubleLabel)
    (hOwnSurvives : ¬ IsDangling data own.1)
    (hOwnExtra : ¬ (endpointPartition profile).Rel own.1.1.2 (extraSheet profile)) :
    ¬ IsDangling (mergeShape profile own hOwnExtra).candidate.datum
      ((mergeShape profile own hOwnExtra).candidate.newSourceEdge own.1.1.2) :=
  (mergeShape profile own hOwnExtra).trivalent_survives input _ _ _
    ((mergeShape profile own hOwnExtra).double_incident_fine own.1 hOwnTarget own.1.1.2
      (sheet_rel_of_incident own) rfl)
    ((mergeShape profile own hOwnExtra).double_incident_fine profile.deleted.edge.1
      shape.deleted_double own.1.1.2 (sheet_rel_of_incident own)
      (mergeShape_fine_rel_extra own hOwnExtra))
    (LimitChainCore.newSourceEdge_incident_old
      (candidate := (mergeShape profile own hOwnExtra).candidate) own.1.1.2)
    ((mergeShape profile own hOwnExtra).retained_survives input ⟨own.1, hOwnSurvives⟩)
    ((mergeShape profile own hOwnExtra).deleted_dangles input)
    (LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _)
    (mergeShape_cardOwn own hOwnExtra)

/-- The untouched block's regrown occurrence survives: its `t₂` endpoint is
divalent and its retained neighbour survives. -/
theorem mergeShape_new_other_survives (input : W2SourceInput data star)
    (own other : IncidentSourceEdge data (WallBlock.sourceVertex data wall block))
    (hOtherTarget : other.1.1.1 = star.edge profile.doubleLabel)
    (hOtherSurvives : ¬ IsDangling data other.1)
    (hOwnExtra : ¬ (endpointPartition profile).Rel own.1.1.2 (extraSheet profile))
    (hOtherExtra : ¬ (endpointPartition profile).Rel other.1.1.2 (extraSheet profile))
    (hSeparate : ¬ (endpointPartition profile).Rel own.1.1.2 other.1.1.2) :
    ¬ IsDangling (mergeShape profile own hOwnExtra).candidate.datum
      ((mergeShape profile own hOwnExtra).candidate.newSourceEdge other.1.1.2) := by
  refine (mergeShape profile own hOwnExtra).new_survives_of_double input other.1.1.2
    (mergeShape_cardOther own other hOwnExtra hOtherExtra hSeparate) ?_
  rw [MemberShape.double_canonical other.1 hOtherTarget]
  exact hOtherSurvives

/-- `M⁽³⁾`'s dangling singleton: the regrown occurrence through the dangling
sheet is itself pruned. -/
theorem thirdShape_new_extra_dangles (shape : Shape profile) (input : W2SourceInput data star) :
    IsDangling (thirdShape shape).candidate.datum
      ((thirdShape shape).candidate.newSourceEdge (extraSheet profile)) := by
  have hCardExtra : Fintype.card (IncidentSourceEdge (thirdShape shape).candidate.datum
      ((thirdShape shape).candidate.datum.sourceEndpoint (oldVertex target wall)
        (extraSheet profile))) = 2 := by
    rw [(thirdShape shape).card_incident_old_selected (extraSheet profile)
      (extraSheet_rel profile)]
    exact congrArg (1 + ·) (SheetPartition.blockCountWithin_eq_one_of_block_eq_singleton _ _ _
      ((data.vertexPartition wall).detachSheet_block_single (extraSheet profile)
        (firstSheet profile) (extra_ne_first shape) (wall_extra_first profile)))
  have hCanonical : data.sourceEdge (star.edge profile.doubleLabel) (extraSheet profile) =
      profile.deleted.edge.1 :=
    MemberShape.double_canonical profile.deleted.edge.1 shape.deleted_double
  refine ((thirdShape shape).new_isDangling_iff_double input (extraSheet profile) hCardExtra).mpr ?_
  rw [hCanonical]
  exact profile.deleted.dangling

/-- `M⁽³⁾`'s surviving regrown occurrence, on the block `A₀ ∖ {x}`. -/
theorem thirdShape_new_first_survives (shape : Shape profile)
    (input : W2SourceInput data star) :
    ¬ IsDangling (thirdShape shape).candidate.datum
      ((thirdShape shape).candidate.newSourceEdge (firstSheet profile)) := by
  have hCardFresh : Fintype.card (IncidentSourceEdge (thirdShape shape).candidate.datum
      ((thirdShape shape).candidate.datum.sourceEndpoint (freshVertex target)
        (firstSheet profile))) = 3 := by
    rw [(thirdShape shape).card_incident_fresh_selected shape (firstSheet profile)
      (firstSheet_rel profile)]
    exact congrArg (· + 1)
      (thirdMember_blockCountWithin shape (firstSheet profile) (firstSheet_rel profile)).2.1
  have hNewExtraFresh := LimitChainCore.newSourceEdge_incident_fresh
    (candidate := (thirdShape shape).candidate) (extraSheet profile)
  rw [(thirdShape shape).sourceEndpoint_fresh_eq_of_rel (extraSheet profile) (firstSheet profile)
    ((extraSheet_rel profile).symm.trans (firstSheet_rel profile))] at hNewExtraFresh
  refine (thirdShape shape).trivalent_survives input _ _ _
    ((thirdShape shape).single_incident profile.third.1 profile.third_target (firstSheet profile)
      ((firstSheet_rel profile).symm.trans (sheet_rel_of_incident profile.third)))
    hNewExtraFresh
    (LimitChainCore.newSourceEdge_incident_fresh
      (candidate := (thirdShape shape).candidate) (firstSheet profile))
    ((thirdShape shape).retained_survives input ⟨profile.third.1, profile.third_survives⟩)
    (thirdShape_new_extra_dangles shape input) ?_ hCardFresh
  intro h
  exact (extra_ne_first shape) ((SheetPartition.detachSheet_rel_single_iff
    (data.vertexPartition wall) (extraSheet profile) (firstSheet profile) (firstSheet profile)
    (extra_ne_first shape) (wall_extra_first profile)).mp
      (((thirdShape shape).newSourceEdge_eq_iff_fine (extraSheet profile) (firstSheet profile)
        (extraSheet_rel profile)).mp h))

theorem thirdShape_fine_not_rel (shape : Shape profile) :
    ¬ (thirdShape shape).fine.Rel (firstSheet profile) (extraSheet profile) :=
  fun h ↦ ((thirdFine_rel_iff shape (extraSheet profile)).mp h).2 rfl

theorem thirdShape_fine_cover (shape : Shape profile) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    (thirdShape shape).fine.Rel (firstSheet profile) sheet ∨
      (thirdShape shape).fine.Rel (extraSheet profile) sheet := by
  by_cases hNe : sheet = extraSheet profile
  · refine Or.inr ?_
    subst hNe
    exact rfl
  · exact Or.inl ((thirdFine_rel_iff shape sheet).mpr ⟨hSheet, hNe⟩)

/-! ### The three representatives, evaluated -/

theorem firstCensus_rep_first (shape : Shape profile) (input : W2SourceInput data star) :
    (firstCensus shape input).rep (firstSheet profile) =
      ⟨profile.first.1, profile.first_survives⟩ :=
  ite_eq_left rfl

theorem firstCensus_rep_second (shape : Shape profile) (input : W2SourceInput data star) :
    (firstCensus shape input).rep (secondSheet profile) =
      ⟨profile.second.1, profile.second_survives⟩ :=
  ite_eq_right (mergeShape_fine_not_rel profile.first profile.second (first_extra_separate shape)
    (second_extra_separate shape) (first_second_separate profile))

theorem secondCensus_rep_second (shape : Shape profile) (input : W2SourceInput data star) :
    (secondCensus shape input).rep (secondSheet profile) =
      ⟨profile.second.1, profile.second_survives⟩ :=
  ite_eq_left rfl

theorem secondCensus_rep_first (shape : Shape profile) (input : W2SourceInput data star) :
    (secondCensus shape input).rep (firstSheet profile) =
      ⟨profile.first.1, profile.first_survives⟩ :=
  ite_eq_right (mergeShape_fine_not_rel profile.second profile.first (second_extra_separate shape)
    (first_extra_separate shape) (fun h ↦ first_second_separate profile h.symm))

theorem thirdCensus_rep (shape : Shape profile) (input : W2SourceInput data star)
    (sheet : Fin degree) :
    (thirdCensus shape input).rep sheet = ⟨profile.third.1, profile.third_survives⟩ := rfl

end Anchors

end DraismaVargas.LocalCases.W2PSurvival
