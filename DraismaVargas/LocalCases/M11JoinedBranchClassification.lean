import DraismaVargas.LocalCases.M11JoinedBranch

/-!
# Branch-vertex classification over the joined M11 wall

The selected single-direction endpoint is divalent after pruning, and every
endpoint belonging to a background wall block has surviving valency at most
two.  Consequently the selected double-direction block is the unique branch
vertex over the two expanded endpoints.  Statements about arbitrary sheets
are converted to equalities of quotient-source vertices before identifying
the branch vertex.
-/

namespace DraismaVargas.LocalCases.M11JoinedBranchClassification

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource W2R1Target SecondEquation
open StableLocalProperties
open M11SourceCandidates M11JoinedGeometry M11JoinedBackground M11JoinedSurvival
open M11JoinedBranch

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

/-- The selected endpoint in the single old target direction. -/
noncomputable def singleVertex {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    (joinedPattern data star block hCard).candidate.datum.SourceVertex :=
  (joinedPattern data star block hCard).candidate.datum.sourceEndpoint
    (endpoint target wall profile.singleLabel) block.1

/-- The selected single-direction endpoint has precisely the retained third
occurrence and the joined occurrence surviving. -/
theorem singleVertex_valency (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    nonDanglingValency (joinedPattern data star block hCard).candidate.datum
      (singleVertex profile hCard) = 2 := by
  classical
  let candidate := (joinedPattern data star block hCard).candidate
  let vertex := singleVertex profile hCard
  change nonDanglingValency candidate.datum vertex = 2
  have hDangling : IsDangling candidate.datum
      (candidate.oldSourceEdge profile.deleted.edge.1) :=
    joined_deleted_dangling input profile hCard
  have hDeletedIncident : Incident candidate.datum
      (candidate.oldSourceEdge profile.deleted.edge.1) vertex :=
    joined_deleted_incident profile hCard
  have hDanglingPositive : 0 <
      ((Finset.univ : Finset (IncidentSourceEdge candidate.datum vertex)).filter
        fun edge ↦ IsDangling candidate.datum edge.1).card :=
    Finset.card_pos.mpr
      ⟨⟨candidate.oldSourceEdge profile.deleted.edge.1, hDeletedIncident⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDangling⟩⟩
  have hTotal := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (IncidentSourceEdge candidate.datum vertex)))
    (p := fun edge ↦ IsDangling candidate.datum edge.1)
  change ((Finset.univ : Finset (IncidentSourceEdge candidate.datum
      (candidate.datum.sourceEndpoint (endpoint target wall profile.singleLabel) block.1))).filter
      fun edge ↦ IsDangling candidate.datum edge.1).card +
    ((Finset.univ : Finset (IncidentSourceEdge candidate.datum
      (candidate.datum.sourceEndpoint (endpoint target wall profile.singleLabel) block.1))).filter
      fun edge ↦ ¬ IsDangling candidate.datum edge.1).card =
    (Finset.univ : Finset (IncidentSourceEdge candidate.datum
      (candidate.datum.sourceEndpoint (endpoint target wall profile.singleLabel) block.1))).card at hTotal
  rw [card_filter_not_isDangling_eq_nonDanglingValency, Finset.card_univ,
    card_incident_distinguished_endpoint profile hCard profile.singleLabel] at hTotal
  change ((Finset.univ : Finset (IncidentSourceEdge candidate.datum vertex)).filter
      fun edge ↦ IsDangling candidate.datum edge.1).card +
    nonDanglingValency candidate.datum vertex = 3 at hTotal
  have hUpper : nonDanglingValency candidate.datum vertex ≤ 2 := by
    omega
  have hNew : (thirdEnd input profile hCard).1 ∈ nonDanglingIncident candidate.datum vertex :=
    (mem_nonDanglingIncident _ _ _).mpr
      ⟨(thirdEnd input profile hCard).2,
        newSourceEdge_incident_endpoint data star block hCard _ _⟩
  have hPositive : 0 < nonDanglingValency candidate.datum vertex := by
    rw [← card_nonDanglingIncident]
    exact Finset.card_pos.mpr ⟨_, hNew⟩
  have hNeOne := NonDanglingValency.nonDanglingValency_ne_one candidate.datum
    (joined_valid input block hCard).1 vertex
  omega

/-- Any endpoint over a nonselected old wall block has surviving valency at
most two, for either target label. -/
theorem background_endpoint_valency_le_two (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (label : Fin 2) (sheet : Fin degree)
    (hBackground : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    nonDanglingValency (joinedPattern data star block hCard).candidate.datum
      ((joinedPattern data star block hCard).candidate.datum.sourceEndpoint
        (endpoint target wall label) sheet) ≤ 2 := by
  exact (NonDanglingValency.nonDanglingValency_le_card_incidentSourceEdge _ _).trans
    (card_incident_background_endpoint input profile hCard label sheet hBackground).le

/-- Every source vertex in the selected single-direction endpoint block has
surviving valency two. -/
theorem selected_single_endpoint_valency (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (sheet : Fin degree) (hSelected : (data.vertexPartition wall).Rel block.1 sheet) :
    nonDanglingValency (joinedPattern data star block hCard).candidate.datum
      ((joinedPattern data star block hCard).candidate.datum.sourceEndpoint
        (endpoint target wall profile.singleLabel) sheet) = 2 := by
  rw [endpoint_eq_of_rel data star block hCard profile.singleLabel sheet block.1 hSelected.symm]
  exact singleVertex_valency input profile hCard

/-- Numerical classification of branch vertices over either expanded wall
endpoint.  The sheet condition names a wall block, not a distinct vertex. -/
theorem endpoint_branch_iff (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (label : Fin 2) (sheet : Fin degree) :
    3 ≤ nonDanglingValency (joinedPattern data star block hCard).candidate.datum
        ((joinedPattern data star block hCard).candidate.datum.sourceEndpoint
          (endpoint target wall label) sheet) ↔
      label = profile.doubleLabel ∧
        (data.vertexPartition wall).Rel block.1 sheet := by
  constructor
  · intro hBranch
    by_cases hSelected : (data.vertexPartition wall).Rel block.1 sheet
    · refine ⟨?_, hSelected⟩
      by_contra hDouble
      have hSingle : label = profile.singleLabel := by
        have hLabels := profile.labels_ne
        omega
      rw [hSingle, selected_single_endpoint_valency input profile hCard sheet hSelected] at hBranch
      omega
    · have hLe := background_endpoint_valency_le_two input profile hCard label sheet hSelected
      omega
  · rintro ⟨rfl, hSelected⟩
    rw [endpoint_eq_of_rel data star block hCard profile.doubleLabel sheet block.1
      hSelected.symm]
    change 3 ≤ nonDanglingValency (joinedPattern data star block hCard).candidate.datum
      (branchVertex profile hCard)
    rw [branchVertex_valency input profile hCard]

/-- The selected double block is the unique actual branch vertex above the
two expanded endpoints. -/
theorem eq_branchVertex_of_endpoint_of_branch (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (vertex : (joinedPattern data star block hCard).candidate.datum.SourceVertex)
    (label : Fin 2) (hTarget : vertex.1.1 = endpoint target wall label)
    (hBranch : 3 ≤ nonDanglingValency
      (joinedPattern data star block hCard).candidate.datum vertex) :
    vertex = branchVertex profile hCard := by
  let candidate := (joinedPattern data star block hCard).candidate
  have hVertex := candidate.datum.sourceEndpoint_self vertex
  rw [hTarget] at hVertex
  have hCanonical : 3 ≤ nonDanglingValency candidate.datum
      (candidate.datum.sourceEndpoint (endpoint target wall label) vertex.1.2) := by
    rw [hVertex]
    exact hBranch
  obtain ⟨hLabel, hSelected⟩ :=
    (endpoint_branch_iff input profile hCard label vertex.1.2).mp hCanonical
  rw [← hVertex, hLabel]
  exact endpoint_eq_of_rel data star block hCard profile.doubleLabel vertex.1.2 block.1
    hSelected.symm

end DraismaVargas.LocalCases.M11JoinedBranchClassification
