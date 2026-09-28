import DraismaVargas.LocalCases.M11SplitSurvival
import DraismaVargas.LocalCases.SheetRelabelPruning

/-!
# Actual surviving and deleted occurrences after the M11 remote swap

Transport the deleted occurrence through the literal branch relabelling.
To certify a surviving occurrence in the double direction, pull it back
through the edge equivalence and use the original two-survivor profile.
The wall vertex is fixed. No second W2 input or stable-path census is assumed.
-/

namespace DraismaVargas.LocalCases.M11RemotePruning

open DraismaVargas.Infrastructure
open W4Assembly W4StableSource W2R1Target SecondEquation
open ResolutionM11 M11RemoteCandidates M11SplitSurvival

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

noncomputable def branchRelabeling {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) : data.SheetRelabeling :=
  wallBranchSwap data wall (branchRoot star profile.doubleLabel) (branchRoot_ne star profile.doubleLabel)
    block.1 (otherSheet block hCard) (otherSheet_spec block hCard).1

theorem branchRelabeling_vertex_wall {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    (branchRelabeling profile hCard).vertexPermutation wall = Equiv.refl _ := by
  change GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.vertexMoved wall (branchRoot star profile.doubleLabel)
      (branchRoot_ne star profile.doubleLabel) wall) (Equiv.swap block.1 (otherSheet block hCard)) = _
  rw [TargetBranchRegion.vertexMoved_wall]
  rfl

theorem wall_endpoint_map {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) (sheet : Fin degree) :
    (branchRelabeling profile hCard).sourceVertexEquiv (data.sourceEndpoint wall sheet) =
      (swappedDatum profile hCard).sourceEndpoint wall sheet := by
  have h := SheetRelabelPruning.sourceVertexEquiv_sourceEndpoint (branchRelabeling profile hCard) wall sheet
  rw [branchRelabeling_vertex_wall] at h
  exact h

theorem incident_preimage_wall {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (edge : (swappedDatum profile hCard).SourceEdge) (sheet : Fin degree)
    (hIncident : Incident (swappedDatum profile hCard) edge ((swappedDatum profile hCard).sourceEndpoint wall sheet)) :
    Incident data ((branchRelabeling profile hCard).sourceEdgeEquiv.symm edge) (data.sourceEndpoint wall sheet) := by
  apply (SheetRelabelPruning.incident_sourceEdgeEquiv_iff (branchRelabeling profile hCard)
    ((branchRelabeling profile hCard).sourceEdgeEquiv.symm edge) (data.sourceEndpoint wall sheet)).mp
  exact (congrArg₂ (Incident (swappedDatum profile hCard))
    ((branchRelabeling profile hCard).sourceEdgeEquiv.apply_symm_apply edge)
    (wall_endpoint_map profile hCard sheet)).mpr hIncident

/-- The literal image of the original uniquely deleted wall occurrence. -/
noncomputable def swappedDeleted {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) : (swappedDatum profile hCard).SourceEdge :=
  (branchRelabeling profile hCard).sourceEdgeEquiv profile.deleted.edge.1

theorem swappedDeleted_dangling (hConnected : data.Connected) {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    IsDangling (swappedDatum profile hCard) (swappedDeleted profile hCard) :=
  (SheetRelabelPruning.isDangling_sourceEdgeEquiv_iff (branchRelabeling profile hCard)
    hConnected profile.deleted.edge.1).mpr profile.deleted.dangling

theorem swappedDeleted_target {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    (swappedDeleted profile hCard).1.1 = star.edge profile.singleLabel :=
  deleted_target_eq_single profile hCard

theorem swappedDeleted_incident {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    Incident (swappedDatum profile hCard) (swappedDeleted profile hCard)
      ((swappedDatum profile hCard).sourceEndpoint wall block.1) := by
  have h := (SheetRelabelPruning.incident_sourceEdgeEquiv_iff (branchRelabeling profile hCard)
    profile.deleted.edge.1 (WallBlock.sourceVertex data wall block)).mpr profile.deleted.edge.2
  change Incident (swappedDatum profile hCard) (swappedDeleted profile hCard)
    ((branchRelabeling profile hCard).sourceVertexEquiv (data.sourceEndpoint wall block.1)) at h
  rwa [wall_endpoint_map] at h

theorem swappedDeleted_sheet_rel {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    (data.vertexPartition wall).Rel block.1 (swappedDeleted profile hCard).1.2 := by
  have h := ((incident_iff_target_mem_and_rel (swappedDatum profile hCard) _ _).mp
    (swappedDeleted_incident profile hCard)).2
  change ((swappedDatum profile hCard).vertexPartition wall).Rel
    (((swappedDatum profile hCard).vertexPartition wall).repr block.1) (swappedDeleted profile hCard).1.2 at h
  rw [swappedDatum_vertexPartition] at h
  exact ((data.vertexPartition wall).rel_repr_right block.1).trans h

/-- Every distinguished double-direction occurrence still survives after
the actual remote swap, by pulling it back to the original profile. -/
theorem swapped_double_sourceEdge_survives (hConnected : data.Connected) {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (sheet : Fin degree) (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    ¬ IsDangling (swappedDatum profile hCard) ((swappedDatum profile hCard).sourceEdge (star.edge profile.doubleLabel) sheet) := by
  let relabeling := branchRelabeling profile hCard
  let edge := (swappedDatum profile hCard).sourceEdge (star.edge profile.doubleLabel) sheet
  let old := relabeling.sourceEdgeEquiv.symm edge
  have hAt := star.edge_mem_incidentEdges profile.doubleLabel
  have hIncident : Incident data old (data.sourceEndpoint wall sheet) :=
    incident_preimage_wall profile hCard edge sheet
      (incident_sourceEdge_sourceEndpoint (swappedDatum profile hCard) wall _ hAt sheet)
  have hOldRel := ((incident_iff_target_mem_and_rel data old (data.sourceEndpoint wall sheet)).mp hIncident).2
  have hSelected : (data.vertexPartition wall).Rel block.1 old.1.2 :=
    (hRel.trans ((data.vertexPartition wall).rel_repr_right sheet)).trans hOldRel
  have hOldEqual : data.sourceEdge (star.edge profile.doubleLabel) old.1.2 = old :=
    GluingDatum.sourceEdge_self data old
  have hOldSurvives : ¬ IsDangling data old := hOldEqual ▸ double_sourceEdge_survives profile hCard old.1.2 hSelected
  intro hDangling
  apply hOldSurvives
  apply (SheetRelabelPruning.isDangling_sourceEdgeEquiv_iff relabeling hConnected old).mp
  exact (congrArg (IsDangling (swappedDatum profile hCard))
    (relabeling.sourceEdgeEquiv.apply_symm_apply edge)).mpr hDangling

end DraismaVargas.LocalCases.M11RemotePruning
