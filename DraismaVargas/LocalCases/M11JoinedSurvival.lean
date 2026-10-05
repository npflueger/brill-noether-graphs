module

public import DraismaVargas.LocalCases.M11JoinedGeometry

@[expose] public section

/-!
# The joined M11 edge survives on the retained single-direction row

At the endpoint carrying the old single target direction, the three actual
incidences are the surviving third occurrence, the deleted occurrence, and
the new edge. Genus-preserving pruning keeps the old statuses unchanged.
Non-dangling valency cannot be one, so the new edge survives; it is consecutive
with the third occurrence. This is the `e3` row of Figure 32 of Draisma--Vargas
Part I (Case `{w2-r2-nd3-M-11}`), in either orientation of the joined target
assignment.
-/

namespace DraismaVargas.LocalCases.M11JoinedSurvival

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource W2R1Target SecondEquation
open M11SourceCandidates M11SplitSurvival M11JoinedGeometry

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

theorem joined_deleted_incident {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    Incident (joinedPattern data star block hCard).candidate.datum
      ((joinedPattern data star block hCard).candidate.oldSourceEdge profile.deleted.edge.1)
      ((joinedPattern data star block hCard).candidate.datum.sourceEndpoint
        (endpoint target wall profile.singleLabel) block.1) :=
  oldSourceEdge_incident_of_target_rel data star block hCard _ _
    (deleted_target_eq_single profile hCard) _ (sheet_rel_of_incident_block profile.deleted.edge)

theorem joined_third_incident {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    Incident (joinedPattern data star block hCard).candidate.datum
      ((joinedPattern data star block hCard).candidate.oldSourceEdge profile.third.1)
      ((joinedPattern data star block hCard).candidate.datum.sourceEndpoint
        (endpoint target wall profile.singleLabel) block.1) :=
  oldSourceEdge_incident_of_target_rel data star block hCard _ _
    profile.third_target _ (sheet_rel_of_incident_block profile.third)

theorem joined_deleted_dangling (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    IsDangling (joinedPattern data star block hCard).candidate.datum
      ((joinedPattern data star block hCard).candidate.oldSourceEdge profile.deleted.edge.1) :=
  (ResolutionPruning.isDangling_oldSourceEdge_iff _ input.valid
    (M11SourceGenus.joined_sourceGenus data star block hCard) _).mpr profile.deleted.dangling

/-- The distinguished joined occurrence really survives. It is one
index-two occurrence, not two unit-index split arms. -/
theorem joined_distinguished_survives (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    ¬ IsDangling (joinedPattern data star block hCard).candidate.datum
      ((joinedPattern data star block hCard).candidate.newSourceEdge block.1) := by
  let candidate := (joinedPattern data star block hCard).candidate
  let vertex := candidate.datum.sourceEndpoint (endpoint target wall profile.singleLabel) block.1
  have hThird := ResolutionSurvival.not_isDangling_oldSourceEdge candidate input.valid.1 _ profile.third_survives
  apply survives_of_trivalent_of_deleted candidate.datum (joined_valid input block hCard).1 vertex
    ⟨candidate.oldSourceEdge profile.third.1, joined_third_incident profile hCard⟩
    ⟨candidate.oldSourceEdge profile.deleted.edge.1, joined_deleted_incident profile hCard⟩
    ⟨candidate.newSourceEdge block.1, newSourceEdge_incident_endpoint data star block hCard _ _⟩
    hThird (joined_deleted_dangling input profile hCard)
  · intro hEqual
    have hTargets := congrArg (fun item : IncidentSourceEdge candidate.datum vertex ↦ item.1.1.1) hEqual
    have hLabels := (occurrenceEquiv target wall candidate.right).injective hTargets
    cases hLabels
  · exact card_incident_distinguished_endpoint profile hCard profile.singleLabel

theorem joined_new_survives (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (sheet : Fin degree) (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    ¬ IsDangling (joinedPattern data star block hCard).candidate.datum
      ((joinedPattern data star block hCard).candidate.newSourceEdge sheet) :=
  newSourceEdge_eq_of_rel data star block hCard block.1 sheet hRel ▸
    joined_distinguished_survives input profile hCard

/-- Figure 32's actual retained third occurrence (`e3`). -/
noncomputable def joined_retainedSingle (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    NonDanglingEdge (joinedPattern data star block hCard).candidate.datum :=
  ⟨(joinedPattern data star block hCard).candidate.oldSourceEdge profile.third.1,
    ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ profile.third_survives⟩

/-- The new joined edge and the retained third edge share their actual
stable class: they are consecutive after pruning the third incidence. -/
theorem joined_distinguished_stablePath_eq (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    NonDanglingEdge.stablePath
        ⟨(joinedPattern data star block hCard).candidate.newSourceEdge block.1,
          joined_distinguished_survives input profile hCard⟩ =
      (joined_retainedSingle input profile hCard).stablePath :=
  stablePath_eq_of_trivalent_deleted _ (joined_valid input block hCard).1 _ _
    ((joinedPattern data star block hCard).candidate.datum.sourceEndpoint
      (endpoint target wall profile.singleLabel) block.1)
    (newSourceEdge_incident_endpoint data star block hCard _ _)
    (joined_third_incident profile hCard)
    ⟨(joinedPattern data star block hCard).candidate.oldSourceEdge profile.deleted.edge.1,
      joined_deleted_incident profile hCard⟩
    (joined_deleted_dangling input profile hCard)
    (card_incident_distinguished_endpoint profile hCard profile.singleLabel)

theorem joined_new_stablePath_eq_retained (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (sheet : Fin degree) (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    NonDanglingEdge.stablePath
        ⟨(joinedPattern data star block hCard).candidate.newSourceEdge sheet,
          joined_new_survives input profile hCard sheet hRel⟩ =
      (joined_retainedSingle input profile hCard).stablePath := by
  have hEqual : (⟨(joinedPattern data star block hCard).candidate.newSourceEdge sheet,
      joined_new_survives input profile hCard sheet hRel⟩ : NonDanglingEdge _) =
      ⟨(joinedPattern data star block hCard).candidate.newSourceEdge block.1,
        joined_distinguished_survives input profile hCard⟩ :=
    Subtype.ext (newSourceEdge_eq_of_rel data star block hCard sheet block.1 hRel.symm)
  exact (congrArg NonDanglingEdge.stablePath hEqual).trans (joined_distinguished_stablePath_eq input profile hCard)

end DraismaVargas.LocalCases.M11JoinedSurvival
