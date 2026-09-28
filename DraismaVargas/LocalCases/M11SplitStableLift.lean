import DraismaVargas.LocalCases.M11JoinedStableLift

/-!
# The actual induced stable-row map for the first M11 split

The induced-labelling paragraph after the non-dangling union lemma of
Draisma--Vargas Part I (`lemma-class-union`) retains an actual old surviving
occurrence. At a background wall block, the first split keeps the old block at
the fresh endpoint and adds only dangling leaf arms. Its surviving incidence set
is therefore exactly the retained old set. This proves compatibility with the
defining consecutive relation, not just an equality of row counts. The
distinguished block has old surviving valency three and cannot support an old
consecutive pair.
-/

namespace DraismaVargas.LocalCases.M11SplitStableLift

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource W2R1Target SecondEquation ResolutionM11
open M11SourceCandidates M11SplitSurvival ResolutionAwayFromWall

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

/-- On a background block the actual fresh partition retains the complete
old wall relation, even when that block has many sheets. -/
theorem background_fresh_rel (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (sheet other : Fin degree) (hBackground : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    ((firstSplitPattern input profile hCard).candidate.datum.vertexPartition
      (freshVertex target)).Rel sheet other ↔ (data.vertexPartition wall).Rel sheet other := by
  let candidate := (firstSplitPattern input profile hCard).candidate
  change ((data.vertexPartition wall).paste (fun anchor ↦ (candidate.resolution anchor).right)
    (fun anchor ↦ (candidate.contracts anchor).right_refines)).Rel sheet other ↔ _
  rw [SheetPartition.paste_rel_iff]
  change (LocalResolution.onBlock (data.vertexPartition wall) block.1
    (splitResolutionAt (data.vertexPartition wall) block.1)
    (backgroundResolution (data.vertexPartition wall))
    ((data.vertexPartition wall).repr sheet)).right.Rel sheet other ↔ _
  rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _
    (fun h ↦ hBackground (h.trans ((data.vertexPartition wall).rel_repr_left sheet)))]
  rfl

/-- The retained occurrences at the fresh background vertex are exactly the
old occurrences at the original wall vertex. -/
theorem background_old_incident_iff (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (sheet : Fin degree) (hBackground : ¬ (data.vertexPartition wall).Rel block.1 sheet)
    (edge : data.SourceEdge) :
    Incident (firstSplitPattern input profile hCard).candidate.datum
      ((firstSplitPattern input profile hCard).candidate.oldSourceEdge edge)
      ((firstSplitPattern input profile hCard).candidate.datum.sourceEndpoint (freshVertex target) sheet) ↔
      Incident data edge (data.sourceEndpoint wall sheet) := by
  let candidate := (firstSplitPattern input profile hCard).candidate
  have hTarget : occurrenceEquiv target wall candidate.right (some edge.1.1) ∈
      GluingDatum.incidentEdges (target := graph target wall candidate.right) (freshVertex target) ↔
      edge.1.1 ∈ GluingDatum.incidentEdges wall := by
    simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [occurrenceEquiv_some]
    exact (oldEnds_incident_freshVertex_iff target wall candidate.right edge.1.1).trans
      (and_iff_left rfl)
  rw [incident_iff_target_mem_and_rel, incident_iff_target_mem_and_rel]
  change (_ ∧ (candidate.datum.vertexPartition (freshVertex target)).Rel
      ((candidate.datum.vertexPartition (freshVertex target)).repr sheet) edge.1.2) ↔
      (_ ∧ (data.vertexPartition wall).Rel ((data.vertexPartition wall).repr sheet) edge.1.2)
  simp only [SheetPartition.Rel, SheetPartition.repr_idem]
  change (_ ∧ (candidate.datum.vertexPartition (freshVertex target)).Rel sheet edge.1.2) ↔
      (_ ∧ (data.vertexPartition wall).Rel sheet edge.1.2)
  rw [background_fresh_rel input profile hCard sheet edge.1.2 hBackground]
  exact and_congr_left fun _ ↦ hTarget

/-- A new occurrence incident to a background vertex lies in that same old
wall block. It is consequently one of the proved dangling background arms. -/
theorem background_new_incident_rel (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (anchor sheet : Fin degree) (hBackground : ¬ (data.vertexPartition wall).Rel block.1 anchor)
    (hIncident : Incident (firstSplitPattern input profile hCard).candidate.datum
      ((firstSplitPattern input profile hCard).candidate.newSourceEdge sheet)
      ((firstSplitPattern input profile hCard).candidate.datum.sourceEndpoint (freshVertex target) anchor)) :
    (data.vertexPartition wall).Rel anchor sheet := by
  let candidate := (firstSplitPattern input profile hCard).candidate
  let pasted := LocalResolution.paste (data.vertexPartition wall) candidate.resolution candidate.contracts
  have hRel := (incident_iff_target_mem_and_rel _ _ _).mp hIncident |>.2
  change (candidate.datum.vertexPartition (freshVertex target)).Rel
    ((candidate.datum.vertexPartition (freshVertex target)).repr anchor)
    (candidate.newSourceEdge sheet).1.2 at hRel
  have hRel' : (candidate.datum.vertexPartition (freshVertex target)).Rel
      anchor (candidate.newSourceEdge sheet).1.2 := by
    simpa only [SheetPartition.Rel, SheetPartition.repr_idem] using hRel
  have hWall := (background_fresh_rel input profile hCard anchor _ hBackground).mp hRel'
  have hRefines : pasted.newEdge.Refines (data.vertexPartition wall) :=
    pasted.edge_refines_right.trans
      (LocalResolution.pasteRight_refines _ candidate.resolution candidate.contracts)
  exact hWall.trans (hRefines.rel (pasted.newEdge.rel_repr_left sheet))

/-- All fresh background leaf arms disappear under pruning. The remaining
incidence set is the literal injective image of the old one. -/
theorem nonDanglingIncident_background (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (sheet : Fin degree) (hBackground : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    nonDanglingIncident (firstSplitPattern input profile hCard).candidate.datum
        ((firstSplitPattern input profile hCard).candidate.datum.sourceEndpoint (freshVertex target) sheet) =
      (nonDanglingIncident data (data.sourceEndpoint wall sheet)).image
        (firstSplitPattern input profile hCard).candidate.oldSourceEdge := by
  classical
  let candidate := (firstSplitPattern input profile hCard).candidate
  ext edge
  constructor
  · intro hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases ResolutionPruning.sourceEdge_cases candidate edge with ⟨old, rfl⟩ | ⟨other, rfl⟩
    · refine Finset.mem_image.mpr ⟨old, (mem_nonDanglingIncident _ _ _).mpr ⟨?_, ?_⟩, rfl⟩
      · exact fun h ↦ hSurvives ((ResolutionPruning.isDangling_oldSourceEdge_iff candidate input.valid
          (M11SourceGenus.firstSplit_sourceGenus input profile hCard) old).mpr h)
      · exact (background_old_incident_iff input profile hCard sheet hBackground old).mp hIncident
    · have hRel := background_new_incident_rel input profile hCard sheet other hBackground hIncident
      exact (hSurvives (M11SplitLeaves.firstSplit_background_isDangling input profile hCard other
        (fun h ↦ hBackground (h.trans hRel.symm)))).elim
  · intro hMem
    obtain ⟨old, hOld, rfl⟩ := Finset.mem_image.mp hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hOld
    exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨ResolutionSurvival.not_isDangling_oldSourceEdge candidate input.valid.1 old hSurvives,
        (background_old_incident_iff input profile hCard sheet hBackground old).mpr hIncident⟩

theorem nonDanglingValency_background (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (sheet : Fin degree) (hBackground : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    nonDanglingValency (firstSplitPattern input profile hCard).candidate.datum
        ((firstSplitPattern input profile hCard).candidate.datum.sourceEndpoint (freshVertex target) sheet) =
      nonDanglingValency data (data.sourceEndpoint wall sheet) := by
  classical
  rw [← card_nonDanglingIncident, nonDanglingIncident_background input profile hCard sheet hBackground,
    Finset.card_image_of_injective _ (ResolutionCut.oldSourceEdge_injective _), card_nonDanglingIncident]

/-- Every old consecutive pair stays consecutive. At the wall it is in a
background block, whose added arms have just been proved irrelevant. -/
theorem consecutive_retained (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (first second : NonDanglingEdge data) (hConsecutive : Consecutive data first second) :
    Consecutive (firstSplitPattern input profile hCard).candidate.datum
      (retainedEdge (firstSplitPattern input profile hCard).candidate input.valid.1 first)
      (retainedEdge (firstSplitPattern input profile hCard).candidate input.valid.1 second) := by
  obtain ⟨hNe, vertex, hFirst, hSecond, hValency⟩ := hConsecutive
  let candidate := (firstSplitPattern input profile hCard).candidate
  by_cases hAt : vertex.1.1 = wall
  · have hBackground := M11JoinedStableLift.background_of_wall_valency_two profile vertex hAt hValency
    have hVertex : data.sourceEndpoint wall vertex.1.2 = vertex :=
      (data.sourceEndpoint_eq_iff wall vertex.1.2 vertex).mpr ⟨hAt.symm, rfl⟩
    refine ⟨fun h ↦ hNe (retainedEdge_injective candidate input.valid.1 h),
      candidate.datum.sourceEndpoint (freshVertex target) vertex.1.2, ?_, ?_, ?_⟩
    · exact (background_old_incident_iff input profile hCard vertex.1.2 hBackground first.1).mpr
        (hVertex.symm ▸ hFirst)
    · exact (background_old_incident_iff input profile hCard vertex.1.2 hBackground second.1).mpr
        (hVertex.symm ▸ hSecond)
    · rw [nonDanglingValency_background input profile hCard vertex.1.2 hBackground, hVertex]
      exact hValency
  · exact consecutive_retained_of_away candidate input.valid
      (M11SourceGenus.firstSplit_sourceGenus input profile hCard) first second hNe vertex hAt hFirst hSecond hValency

/-- The first split's row map is induced by retaining an actual old survivor,
with independence of the representative proved above. -/
noncomputable def stablePathLift (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    StablePath data → StablePath (firstSplitPattern input profile hCard).candidate.datum :=
  Quot.lift (fun edge ↦ (retainedEdge (firstSplitPattern input profile hCard).candidate input.valid.1 edge).stablePath)
    (fun _ _ h ↦ stablePath_eq_of_consecutive (consecutive_retained input profile hCard _ _ h))

@[simp] theorem stablePathLift_mk (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) (edge : NonDanglingEdge data) :
    stablePathLift input profile hCard edge.stablePath =
      (retainedEdge (firstSplitPattern input profile hCard).candidate input.valid.1 edge).stablePath := rfl

/-- Every new survivor joins the retained double-direction occurrence on
the deleted sheet. No stable row is supported only by new occurrences. -/
theorem exists_retained_row (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (edge : NonDanglingEdge (firstSplitPattern input profile hCard).candidate.datum) :
    ∃ old : NonDanglingEdge data,
      (retainedEdge (firstSplitPattern input profile hCard).candidate input.valid.1 old).stablePath = edge.stablePath := by
  let candidate := (firstSplitPattern input profile hCard).candidate
  rcases nonDanglingEdge_cases candidate input.valid
      (M11SourceGenus.firstSplit_sourceGenus input profile hCard) edge with
    ⟨old, rfl⟩ | ⟨sheet, hSurvives, rfl⟩
  · exact ⟨old, rfl⟩
  · have hRel := (firstSplit_new_survives_iff input profile hCard sheet).mp hSurvives
    refine ⟨⟨data.sourceEdge (star.edge profile.doubleLabel) profile.deleted.edge.1.1.2,
      double_sourceEdge_survives profile hCard _ (sheet_rel_of_incident_block profile.deleted.edge)⟩, ?_⟩
    exact (firstSplit_new_stablePath_eq_retained input profile hCard sheet hRel).symm

/-- Surjectivity consumes the induced map on all old rows. Its converse is
proved in `M11SplitRowDescent`; `M11SplitLimitMatrix` compares the columns. -/
theorem stablePathLift_surjective (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    Function.Surjective (stablePathLift input profile hCard) := by
  intro path
  induction path using Quot.inductionOn with
  | h edge =>
      obtain ⟨old, hPath⟩ := exists_retained_row input profile hCard edge
      exact ⟨old.stablePath, hPath⟩

end DraismaVargas.LocalCases.M11SplitStableLift
