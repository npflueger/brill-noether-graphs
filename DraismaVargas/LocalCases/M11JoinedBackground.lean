import DraismaVargas.LocalCases.M11JoinedSurvival

/-!
# The joined M11 background is a subdivision, not a family of leaves

M11 is Case {w2-r2-nd3-M-11} of Draisma--Vargas Part I (Figure 32).
Every wall block other than the distinguished one is unramified and has one old occurrence in each
target direction. Its joined endpoints are divalent. The new occurrence
therefore has exactly the same pruning status as either retained direction;
when surviving, they share a stable class and have equal dilation index.
These are the actual background contributions denoted by `s` in Figure 32 of
Part I.
-/

namespace DraismaVargas.LocalCases.M11JoinedBackground

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource W2R1Target SecondEquation StableLocalProperties
open M11SourceCandidates M11JoinedGeometry

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

theorem background_ramification_zero (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (sheet : Fin degree) (hBackground : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    data.localRamification wall ((data.vertexPartition wall).toBlock sheet) = 0 := by
  apply W2RankObstructions.other_localRamification_eq_zero input block profile.ramification
  intro hEqual
  apply hBackground
  exact block.2.trans (congrArg Subtype.val hEqual).symm

theorem background_blockCount (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (label : Fin 2) (sheet : Fin degree)
    (hBackground : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    (data.edgePartition (star.edge label)).blockCountWithin (data.vertexPartition wall) sheet = 1 :=
  blockCountWithin_eq_one_of_divalent_localRamification_zero data wall star.card_incidentEdges sheet
    (background_ramification_zero input profile sheet hBackground) _ (star.edge_mem_incidentEdges label)

theorem card_incident_background_endpoint (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) (label : Fin 2) (sheet : Fin degree)
    (hBackground : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    Fintype.card (IncidentSourceEdge (joinedPattern data star block hCard).candidate.datum
      ((joinedPattern data star block hCard).candidate.datum.sourceEndpoint (endpoint target wall label) sheet)) = 2 := by
  rw [card_incident_endpoint, background_blockCount input profile label sheet hBackground]

/-- A joined background occurrence is dangling iff the original occurrence
in either chosen target direction is dangling. No compatibility is assumed. -/
theorem background_isDangling_iff (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) (label : Fin 2) (sheet : Fin degree)
    (hBackground : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    IsDangling (joinedPattern data star block hCard).candidate.datum
        ((joinedPattern data star block hCard).candidate.newSourceEdge sheet) ↔
      IsDangling data (data.sourceEdge (star.edge label) sheet) := by
  let candidate := (joinedPattern data star block hCard).candidate
  have hNew := newSourceEdge_incident_endpoint data star block hCard label sheet
  have hOld := oldSourceEdge_incident_endpoint data star block hCard label sheet
  have hDegree : vertex_degree candidate.datum.sourceGraph
      (candidate.datum.sourceEndpoint (endpoint target wall label) sheet) = 2 := by
    rw [vertex_degree_sourceGraph_eq_card_incidentSourceEdge,
      card_incident_background_endpoint input profile hCard label sheet hBackground]
    norm_num
  have hNe : candidate.newSourceEdge sheet ≠ candidate.oldSourceEdge (data.sourceEdge (star.edge label) sheet) := by
    intro hEqual
    have hTargets := congrArg (fun edge : candidate.datum.SourceEdge ↦ edge.1.1) hEqual
    have hLabels := (occurrenceEquiv target wall candidate.right).injective hTargets
    cases hLabels
  have hPruning := ResolutionPruning.isDangling_oldSourceEdge_iff candidate input.valid
    (M11SourceGenus.joined_sourceGenus data star block hCard) (data.sourceEdge (star.edge label) sheet)
  constructor
  · intro hDangling
    exact hPruning.mp (isDangling_of_incident_of_vertex_degree_eq_two candidate.datum hNe hNew hOld hDegree hDangling)
  · intro hDangling
    exact isDangling_of_incident_of_vertex_degree_eq_two candidate.datum hNe.symm hOld hNew hDegree
      (hPruning.mpr hDangling)

theorem background_survives (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) (label : Fin 2) (sheet : Fin degree)
    (hBackground : ¬ (data.vertexPartition wall).Rel block.1 sheet)
    (hSurvives : ¬ IsDangling data (data.sourceEdge (star.edge label) sheet)) :
    ¬ IsDangling (joinedPattern data star block hCard).candidate.datum
      ((joinedPattern data star block hCard).candidate.newSourceEdge sheet) :=
  fun h ↦ hSurvives ((background_isDangling_iff input profile hCard label sheet hBackground).mp h)

/-- The background new edge shares the actual retained row in either
direction, with both survival proofs constructed from the original datum. -/
theorem background_stablePath_eq_retained (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) (label : Fin 2) (sheet : Fin degree)
    (hBackground : ¬ (data.vertexPartition wall).Rel block.1 sheet)
    (hSurvives : ¬ IsDangling data (data.sourceEdge (star.edge label) sheet)) :
    NonDanglingEdge.stablePath
        ⟨(joinedPattern data star block hCard).candidate.newSourceEdge sheet,
          background_survives input profile hCard label sheet hBackground hSurvives⟩ =
      NonDanglingEdge.stablePath
        ⟨(joinedPattern data star block hCard).candidate.oldSourceEdge (data.sourceEdge (star.edge label) sheet),
          ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ hSurvives⟩ :=
  M11SplitRows.stablePath_eq_of_incident_card_two _ (joined_valid input block hCard).1 _ _
    ((joinedPattern data star block hCard).candidate.datum.sourceEndpoint (endpoint target wall label) sheet)
    (newSourceEdge_incident_endpoint data star block hCard label sheet)
    (oldSourceEdge_incident_endpoint data star block hCard label sheet)
    (card_incident_background_endpoint input profile hCard label sheet hBackground)

/-- The same wall-block size is the dilation index on the new and old
background occurrences. Their reciprocal-index contributions agree. -/
theorem background_index_eq (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) (label : Fin 2) (sheet : Fin degree)
    (hBackground : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    (joinedPattern data star block hCard).candidate.datum.sourceEdgeIndex
        ((joinedPattern data star block hCard).candidate.newSourceEdge sheet) =
      data.sourceEdgeIndex (data.sourceEdge (star.edge label) sheet) := by
  rw [joined_newSourceEdge_index, GluingDatum.sourceEdgeIndex_sourceEdge]
  exact (SheetPartition.blockCard_eq_of_refines_of_blockCountWithin_eq_one _ _
    (star.edgePartition_refines_wall data label) sheet
    (background_blockCount input profile label sheet hBackground)).symm

end DraismaVargas.LocalCases.M11JoinedBackground
