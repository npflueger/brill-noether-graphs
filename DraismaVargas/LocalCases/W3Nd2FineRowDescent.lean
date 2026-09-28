import DraismaVargas.LocalCases.W3Nd2StableLift

/-!
# Reverse row transport for the true Figure 31 fine resolution

The fine background replaces each old large-direction occurrence by the
corresponding new occurrence and retains every other old occurrence.  The
first step below proves this is a literal bijection on surviving incidence
sets at every unramified wall block, without assuming that the old block is
divalent. The quotient descent and its literal left inverse prove the fine
stable-row equivalence. The coarse companion is in `W3Nd2RowDescent`; the
branch-incidence and matrix comparisons are in other modules.
-/

namespace DraismaVargas.LocalCases.W3Nd2FineRowDescent

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open W3R1SourceProfile W3Nd2SourceCandidates W3Nd2FineRefinement
open W3Nd2FineCandidates W3Nd2Survival W3Nd2EndRows W3Nd2Background
open W3Nd2StableLift ResolutionM11 ResolutionPruning ResolutionSurvival
open ResolutionAwayFromWall

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (datum : GluingDatum target degree)
    (vertex : datum.SourceVertex) : DecidableEq (IncidentSourceEdge datum vertex) :=
  Classical.decEq _

/-- The actual occurrence replacement on a fine background star: the old
large direction becomes the new arm and every other direction is retained. -/
noncomputable def fineBackgroundReplace
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (old : data.SourceEdge) : (fineCandidate input profile).datum.SourceEdge :=
  if old.1.1 = largeTarget input profile then
    (fineCandidate input profile).newSourceEdge old.1.2
  else (fineCandidate input profile).oldSourceEdge old

theorem fineBackgroundReplace_of_large
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (old : data.SourceEdge) (hTarget : old.1.1 = largeTarget input profile) :
    fineBackgroundReplace input profile old =
      (fineCandidate input profile).newSourceEdge old.1.2 := by
  rw [fineBackgroundReplace, if_pos hTarget]

theorem fineBackgroundReplace_of_ne_large
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (old : data.SourceEdge) (hTarget : old.1.1 ≠ largeTarget input profile) :
    fineBackgroundReplace input profile old =
      (fineCandidate input profile).oldSourceEdge old := by
  rw [fineBackgroundReplace, if_neg hTarget]

/-- Replacement preserves and reflects survival and incidence at an
unramified background source vertex. -/
theorem fineBackgroundReplace_mem_iff
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (old : data.SourceEdge) :
    fineBackgroundReplace input profile old ∈
        nonDanglingIncident (fineCandidate input profile).datum
          ((fineCandidate input profile).datum.sourceEndpoint
            (freshVertex target) sheet) ↔
      old ∈ nonDanglingIncident data (data.sourceEndpoint wall sheet) := by
  classical
  by_cases hTarget : old.1.1 = largeTarget input profile
  · rw [fineBackgroundReplace_of_large input profile old hTarget]
    constructor
    · intro hMem
      obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
      have hWall := fine_background_new_incident_right_rel
        input profile sheet old.1.2 hSheet hIncident
      have hOldSheet : ¬(data.vertexPartition wall).Rel
          input.distinguishedBlock.1 old.1.2 := by
        intro hDist
        exact hSheet (hDist.trans hWall.symm)
      have hOldSurvives : ¬ IsDangling data old := by
        have hCanonical : data.sourceEdge (largeTarget input profile) old.1.2 = old := by
          rw [← hTarget]
          exact GluingDatum.sourceEdge_self data old
        have := (fine_background_new_survives_iff_oldLarge
          input profile old.1.2 hOldSheet).mp hSurvives
        simpa [hCanonical] using this
      have hOldIncident : Incident data old (data.sourceEndpoint wall sheet) := by
        apply (incident_iff_target_mem_and_rel data old _).mpr
        refine ⟨hTarget ▸ largeTarget_mem input profile, ?_⟩
        change (data.vertexPartition wall).Rel
          ((data.vertexPartition wall).repr sheet) old.1.2
        exact (data.vertexPartition wall).rel_repr_left sheet |>.trans hWall
      exact (mem_nonDanglingIncident _ _ _).mpr ⟨hOldSurvives, hOldIncident⟩
    · intro hMem
      obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
      have hWall : (data.vertexPartition wall).Rel sheet old.1.2 := by
        have hRel := (incident_iff_target_mem_and_rel data old _).mp hIncident |>.2
        change (data.vertexPartition wall).Rel
          ((data.vertexPartition wall).repr sheet) old.1.2 at hRel
        exact (data.vertexPartition wall).rel_repr_right sheet |>.trans hRel
      have hOldSheet : ¬(data.vertexPartition wall).Rel
          input.distinguishedBlock.1 old.1.2 := by
        intro hDist
        exact hSheet (hDist.trans hWall.symm)
      have hCanonical : data.sourceEdge (largeTarget input profile) old.1.2 = old := by
        rw [← hTarget]
        exact GluingDatum.sourceEdge_self data old
      apply (mem_nonDanglingIncident _ _ _).mpr
      refine ⟨(fine_background_new_survives_iff_oldLarge input profile
        old.1.2 hOldSheet).mpr (by simpa [hCanonical] using hSurvives), ?_⟩
      exact fine_background_new_incident_right input profile sheet old.1.2 hSheet hWall
  · rw [fineBackgroundReplace_of_ne_large input profile old hTarget]
    rw [mem_nonDanglingIncident, mem_nonDanglingIncident]
    rw [fine_old_isDangling_iff input profile old,
      fine_background_old_incident_right_iff input profile sheet hSheet old]
    tauto

/-- Every surviving incidence at a fine fresh background endpoint is the
replacement of an actual old surviving incidence. -/
theorem fineBackgroundReplace_surjective_on_incidence
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (edge : (fineCandidate input profile).datum.SourceEdge)
    (hEdge : edge ∈ nonDanglingIncident (fineCandidate input profile).datum
      ((fineCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet)) :
    ∃ old : data.SourceEdge,
      old ∈ nonDanglingIncident data (data.sourceEndpoint wall sheet) ∧
        fineBackgroundReplace input profile old = edge := by
  classical
  let candidate := fineCandidate input profile
  obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hEdge
  rcases sourceEdge_cases candidate edge with ⟨old, rfl⟩ | ⟨other, rfl⟩
  · have hOldTarget :=
      (fine_background_old_incident_right_iff input profile sheet hSheet old).mp
        hIncident |>.2
    have hReplace := fineBackgroundReplace_of_ne_large input profile old hOldTarget
    refine ⟨old, (fineBackgroundReplace_mem_iff input profile sheet hSheet old).mp ?_, hReplace⟩
    rw [hReplace]
    exact hEdge
  · have hWall := fine_background_new_incident_right_rel
      input profile sheet other hSheet hIncident
    let old := data.sourceEdge (largeTarget input profile) other
    have hOldSheet : ¬(data.vertexPartition wall).Rel
        input.distinguishedBlock.1 old.1.2 := by
      intro hDist
      apply hSheet
      have hFineWall := (large_refines_wall input profile).rel
        ((largePartition input profile).rel_repr_left other)
      exact hDist.trans (hFineWall.trans hWall.symm)
    have hOldTarget : old.1.1 = largeTarget input profile := rfl
    refine ⟨old, (fineBackgroundReplace_mem_iff input profile sheet hSheet old).mp ?_, ?_⟩
    · rw [fineBackgroundReplace_of_large input profile old hOldTarget]
      have hEq : candidate.newSourceEdge old.1.2 = candidate.newSourceEdge other := by
        apply fine_background_new_eq_of_large_source_eq input profile other old.1.2
        · intro hDist
          exact hSheet (hDist.trans hWall.symm)
        · exact GluingDatum.sourceEdge_self data old
      rw [hEq]
      exact hEdge
    · rw [fineBackgroundReplace_of_large input profile old hOldTarget]
      apply fine_background_new_eq_of_large_source_eq input profile other old.1.2
      · intro hDist
        exact hSheet (hDist.trans hWall.symm)
      · exact GluingDatum.sourceEdge_self data old

/-- Distinct old surviving incidences have distinct replacements.  In the
large/large case this is exactly the equality of the old large partition and
the new-edge partition on a background block. -/
theorem fineBackgroundReplace_injective_on_incidence
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (first second : data.SourceEdge)
    (hFirst : first ∈ nonDanglingIncident data (data.sourceEndpoint wall sheet))
    (_hSecond : second ∈ nonDanglingIncident data (data.sourceEndpoint wall sheet))
    (hEqual : fineBackgroundReplace input profile first =
      fineBackgroundReplace input profile second) : first = second := by
  classical
  let candidate := fineCandidate input profile
  by_cases hFirstTarget : first.1.1 = largeTarget input profile
  · by_cases hSecondTarget : second.1.1 = largeTarget input profile
    · rw [fineBackgroundReplace_of_large input profile first hFirstTarget,
        fineBackgroundReplace_of_large input profile second hSecondTarget] at hEqual
      have hNewRepr := congrArg
        (fun edge : candidate.datum.SourceEdge ↦ edge.1.2) hEqual
      have hFirstIncident := (mem_nonDanglingIncident _ _ _).mp hFirst |>.2
      have hFirstWall : (data.vertexPartition wall).Rel sheet first.1.2 := by
        have hRel := (incident_iff_target_mem_and_rel data first _).mp hFirstIncident |>.2
        change (data.vertexPartition wall).Rel
          ((data.vertexPartition wall).repr sheet) first.1.2 at hRel
        exact (data.vertexPartition wall).rel_repr_right sheet |>.trans hRel
      have hFirstSheet : ¬(data.vertexPartition wall).Rel
          input.distinguishedBlock.1 first.1.2 := by
        intro hDist
        exact hSheet (hDist.trans hFirstWall.symm)
      have hNewRel : (finePastedResolution input profile).newEdge.Rel
          first.1.2 second.1.2 := hNewRepr
      have hFineRel : (largePartition input profile).Rel first.1.2 second.1.2 := by
        apply (largePartition input profile).mem_block_iff _ _ |>.mp
        rw [← fine_background_newEdge_block input profile first.1.2 hFirstSheet,
          (finePastedResolution input profile).newEdge.mem_block_iff]
        exact hNewRel
      apply Subtype.ext
      apply Prod.ext
      · exact hFirstTarget.trans hSecondTarget.symm
      · have hFirstRepr : (largePartition input profile).repr first.1.2 = first.1.2 := by
          change (data.edgePartition (largeTarget input profile)).repr first.1.2 = first.1.2
          rw [← hFirstTarget]
          exact first.2
        have hSecondRepr : (largePartition input profile).repr second.1.2 = second.1.2 := by
          change (data.edgePartition (largeTarget input profile)).repr second.1.2 = second.1.2
          rw [← hSecondTarget]
          exact second.2
        exact hFirstRepr.symm.trans (hFineRel.trans hSecondRepr)
    · rw [fineBackgroundReplace_of_large input profile first hFirstTarget,
        fineBackgroundReplace_of_ne_large input profile second hSecondTarget] at hEqual
      have hLabels := (occurrenceEquiv target wall candidate.right).injective
        (congrArg (fun edge : candidate.datum.SourceEdge ↦ edge.1.1) hEqual)
      cases hLabels
  · by_cases hSecondTarget : second.1.1 = largeTarget input profile
    · rw [fineBackgroundReplace_of_ne_large input profile first hFirstTarget,
        fineBackgroundReplace_of_large input profile second hSecondTarget] at hEqual
      have hLabels := (occurrenceEquiv target wall candidate.right).injective
        (congrArg (fun edge : candidate.datum.SourceEdge ↦ edge.1.1) hEqual)
      cases hLabels
    · rw [fineBackgroundReplace_of_ne_large input profile first hFirstTarget,
        fineBackgroundReplace_of_ne_large input profile second hSecondTarget] at hEqual
      exact ResolutionCut.oldSourceEdge_injective candidate hEqual

/-- The complete surviving incidence set is the image of the old one under
the literal large-to-new replacement. -/
theorem fine_nonDanglingIncident_background_image
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    nonDanglingIncident (fineCandidate input profile).datum
        ((fineCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet) =
      (nonDanglingIncident data (data.sourceEndpoint wall sheet)).image
        (fineBackgroundReplace input profile) := by
  classical
  ext edge
  constructor
  · intro hEdge
    obtain ⟨old, hOld, hReplace⟩ :=
      fineBackgroundReplace_surjective_on_incidence input profile sheet hSheet edge hEdge
    exact Finset.mem_image.mpr ⟨old, hOld, hReplace⟩
  · intro hEdge
    obtain ⟨old, hOld, rfl⟩ := Finset.mem_image.mp hEdge
    exact (fineBackgroundReplace_mem_iff input profile sheet hSheet old).mpr hOld

/-- Hence pruning valency is preserved at every fine background fresh
vertex, including old nd3 blocks. -/
theorem fine_nonDanglingValency_background
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    nonDanglingValency (fineCandidate input profile).datum
        ((fineCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet) =
      nonDanglingValency data (data.sourceEndpoint wall sheet) := by
  classical
  rw [← card_nonDanglingIncident,
    fine_nonDanglingIncident_background_image input profile sheet hSheet,
    Finset.card_image_iff.mpr]
  · rw [card_nonDanglingIncident]
  · intro first hFirst second hSecond hEqual
    exact fineBackgroundReplace_injective_on_incidence input profile sheet hSheet
      first second hFirst hSecond hEqual

/-- Decode an occurrence of the fine resolved source back to an actual old
surviving occurrence.  Retained occurrences use their literal preimage; a new
occurrence uses the old large-direction occurrence on its canonical sheet,
except that all selected sheets use the profile's fixed large survivor. -/
noncomputable def fineOldEdgeOf
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (edge : NonDanglingEdge (fineCandidate input profile).datum) :
    NonDanglingEdge data := by
  let candidate := fineCandidate input profile
  cases hDecode : (occurrenceEquiv target wall candidate.right).symm edge.1.1.1 with
  | none =>
      have hTarget : edge.1.1.1 = occurrenceEquiv target wall candidate.right none := by
        have hApply := congrArg (occurrenceEquiv target wall candidate.right) hDecode
        simpa using hApply
      have hEdge : candidate.newSourceEdge edge.1.1.2 = edge.1 := by
        apply Subtype.ext
        apply Prod.ext
        · exact hTarget.symm
        · have hCanonical := edge.1.2
          change (candidate.datum.edgePartition edge.1.1.1).repr edge.1.1.2 =
            edge.1.1.2 at hCanonical
          have hPartition : candidate.datum.edgePartition
              (occurrenceEquiv target wall candidate.right none) =
              (finePastedResolution input profile).newEdge :=
            GlobalResolution.expandedEdgePartition_new data wall _ _
          rw [hTarget, hPartition] at hCanonical
          change (finePastedResolution input profile).newEdge.repr edge.1.1.2 =
            edge.1.1.2
          exact hCanonical
      by_cases hSelected : (data.vertexPartition wall).Rel
          input.distinguishedBlock.1 edge.1.1.2
      · exact ⟨profile.large.1, profile.large_survives⟩
      · have hNewSurvives : ¬ IsDangling candidate.datum
            (candidate.newSourceEdge edge.1.1.2) := by
          rw [hEdge]
          exact edge.2
        exact ⟨data.sourceEdge (largeTarget input profile) edge.1.1.2,
          (fine_background_new_survives_iff_oldLarge input profile
            edge.1.1.2 hSelected).mp hNewSurvives⟩
  | some oldTarget =>
      have hTarget : edge.1.1.1 =
          occurrenceEquiv target wall candidate.right (some oldTarget) := by
        have hApply := congrArg (occurrenceEquiv target wall candidate.right) hDecode
        simpa using hApply
      let old := data.sourceEdge oldTarget edge.1.1.2
      have hOldSheet : old.1.2 = edge.1.1.2 := by
        have hCanonical := edge.1.2
        change (candidate.datum.edgePartition edge.1.1.1).repr edge.1.1.2 =
          edge.1.1.2 at hCanonical
        have hPartition : candidate.datum.edgePartition
            (occurrenceEquiv target wall candidate.right (some oldTarget)) =
            data.edgePartition oldTarget :=
          GlobalResolution.expandedEdgePartition_old data wall _ _ _
        rw [hTarget, hPartition] at hCanonical
        change (data.edgePartition oldTarget).repr edge.1.1.2 = edge.1.1.2
        exact hCanonical
      have hEdge : candidate.oldSourceEdge old = edge.1 := by
        apply Subtype.ext
        apply Prod.ext
        · exact hTarget.symm
        · exact hOldSheet
      have hOldSurvives : ¬ IsDangling data old := by
        intro hDangling
        have hCandidateDangling :=
          (fine_old_isDangling_iff input profile old).mpr hDangling
        rw [hEdge] at hCandidateDangling
        exact edge.2 hCandidateDangling
      exact ⟨old, hOldSurvives⟩

/-- The old source occurrence represented by a new fine occurrence. -/
noncomputable def fineNewOldSourceEdge
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree) : data.SourceEdge :=
  if (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet then
    profile.large.1
  else data.sourceEdge (largeTarget input profile) sheet

theorem fineNewOldSourceEdge_survives
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (fineCandidate input profile).datum
      ((fineCandidate input profile).newSourceEdge sheet)) :
    ¬ IsDangling data (fineNewOldSourceEdge input profile sheet) := by
  classical
  by_cases hSelected : (data.vertexPartition wall).Rel
      input.distinguishedBlock.1 sheet
  · rw [fineNewOldSourceEdge, if_pos hSelected]
    exact profile.large_survives
  · rw [fineNewOldSourceEdge, if_neg hSelected]
    exact (fine_background_new_survives_iff_oldLarge input profile sheet hSelected).mp
      hSurvives

noncomputable def fineNewOldEdge
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (fineCandidate input profile).datum
      ((fineCandidate input profile).newSourceEdge sheet)) : NonDanglingEdge data :=
  ⟨fineNewOldSourceEdge input profile sheet,
    fineNewOldSourceEdge_survives input profile sheet hSurvives⟩

theorem fine_new_representation
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (edge : NonDanglingEdge (fineCandidate input profile).datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge (fineCandidate input profile) input.valid.1 old = edge) :
    ∃ sheet : Fin degree, ∃ hSurvives : ¬ IsDangling
        (fineCandidate input profile).datum
        ((fineCandidate input profile).newSourceEdge sheet),
      edge = ⟨(fineCandidate input profile).newSourceEdge sheet, hSurvives⟩ := by
  let candidate := fineCandidate input profile
  rcases nonDanglingEdge_cases candidate input.valid
      (fineCandidate_sourceGenus input profile) edge with ⟨old, hOld⟩ | ⟨sheet, hSurvives, hNew⟩
  · exact (hNotOld ⟨old, hOld.symm⟩).elim
  · exact ⟨sheet, hSurvives, hNew⟩

noncomputable def fineNewSheet
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (edge : NonDanglingEdge (fineCandidate input profile).datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge (fineCandidate input profile) input.valid.1 old = edge) : Fin degree :=
  (fine_new_representation input profile edge hNotOld).choose

theorem fineNewSheet_survives
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (edge : NonDanglingEdge (fineCandidate input profile).datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge (fineCandidate input profile) input.valid.1 old = edge) :
    ¬ IsDangling (fineCandidate input profile).datum
      ((fineCandidate input profile).newSourceEdge
        (fineNewSheet input profile edge hNotOld)) :=
  (fine_new_representation input profile edge hNotOld).choose_spec.choose

theorem fineNewSheet_spec
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (edge : NonDanglingEdge (fineCandidate input profile).datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge (fineCandidate input profile) input.valid.1 old = edge) :
    edge = ⟨(fineCandidate input profile).newSourceEdge
        (fineNewSheet input profile edge hNotOld),
      fineNewSheet_survives input profile edge hNotOld⟩ :=
  (fine_new_representation input profile edge hNotOld).choose_spec.choose_spec

/-- Retained occurrences return to their literal preimage; otherwise use the
actual old large occurrence represented by the decoded new occurrence. -/
noncomputable def fineRowOfEdge
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (edge : NonDanglingEdge (fineCandidate input profile).datum) : StablePath data := by
  classical
  exact if hOld : ∃ old : NonDanglingEdge data,
      retainedEdge (fineCandidate input profile) input.valid.1 old = edge then
    (Classical.choose hOld).stablePath
  else
    (fineNewOldEdge input profile (fineNewSheet input profile edge hOld)
      (fineNewSheet_survives input profile edge hOld)).stablePath

@[simp] theorem fineRowOfEdge_retained
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (old : NonDanglingEdge data) :
    fineRowOfEdge input profile
      (retainedEdge (fineCandidate input profile) input.valid.1 old) =
        old.stablePath := by
  classical
  have hOld : ∃ other : NonDanglingEdge data,
      retainedEdge (fineCandidate input profile) input.valid.1 other =
        retainedEdge (fineCandidate input profile) input.valid.1 old := ⟨old, rfl⟩
  rw [fineRowOfEdge, dif_pos hOld]
  exact congrArg NonDanglingEdge.stablePath
    (retainedEdge_injective _ input.valid.1 (Classical.choose_spec hOld))

theorem fineRowOfEdge_not_retained
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (edge : NonDanglingEdge (fineCandidate input profile).datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge (fineCandidate input profile) input.valid.1 old = edge) :
    fineRowOfEdge input profile edge =
      (fineNewOldEdge input profile (fineNewSheet input profile edge hNotOld)
        (fineNewSheet_survives input profile edge hNotOld)).stablePath := by
  classical
  exact dif_neg hNotOld

theorem fineNewOldEdge_of_selected
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (fineCandidate input profile).datum
      ((fineCandidate input profile).newSourceEdge sheet))
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    fineNewOldEdge input profile sheet hSurvives =
      ⟨profile.large.1, profile.large_survives⟩ := by
  apply Subtype.ext
  change fineNewOldSourceEdge input profile sheet = profile.large.1
  rw [fineNewOldSourceEdge, if_pos hSelected]

theorem fineNewOldEdge_of_background
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (fineCandidate input profile).datum
      ((fineCandidate input profile).newSourceEdge sheet))
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (fineNewOldEdge input profile sheet hSurvives).1 =
      data.sourceEdge (largeTarget input profile) sheet := by
  change fineNewOldSourceEdge input profile sheet =
    data.sourceEdge (largeTarget input profile) sheet
  rw [fineNewOldSourceEdge, if_neg hBackground]

/-- At a background fresh endpoint, every assigned reverse row has an actual
old surviving occurrence incident at the original wall vertex, and that old
occurrence replaces back to the given resolved occurrence. -/
theorem fineRowOfEdge_incident_background
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (edge : NonDanglingEdge (fineCandidate input profile).datum)
    (hIncident : Incident (fineCandidate input profile).datum edge.1
      ((fineCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet)) :
    ∃ old : NonDanglingEdge data,
      Incident data old.1 (data.sourceEndpoint wall sheet) ∧
        fineBackgroundReplace input profile old.1 = edge.1 ∧
          fineRowOfEdge input profile edge = old.stablePath := by
  classical
  let candidate := fineCandidate input profile
  by_cases hOld : ∃ old : NonDanglingEdge data,
      retainedEdge candidate input.valid.1 old = edge
  · let old := Classical.choose hOld
    have hEq := Classical.choose_spec hOld
    have hCandidateIncident : Incident candidate.datum (candidate.oldSourceEdge old.1)
        (candidate.datum.sourceEndpoint (freshVertex target) sheet) := by
      rw [show candidate.oldSourceEdge old.1 = edge.1 from congrArg Subtype.val hEq]
      exact hIncident
    obtain ⟨hOldIncident, hTarget⟩ :=
      (fine_background_old_incident_right_iff input profile sheet hBackground old.1).mp
        hCandidateIncident
    refine ⟨old, hOldIncident, ?_, ?_⟩
    · rw [fineBackgroundReplace_of_ne_large input profile old.1 hTarget]
      exact congrArg Subtype.val hEq
    · rw [fineRowOfEdge, dif_pos hOld]
  · let newSheet := fineNewSheet input profile edge hOld
    let hNewSurvives := fineNewSheet_survives input profile edge hOld
    have hEdge := fineNewSheet_spec input profile edge hOld
    have hNewIncident : Incident candidate.datum (candidate.newSourceEdge newSheet)
        (candidate.datum.sourceEndpoint (freshVertex target) sheet) := by
      rw [← show edge.1 = candidate.newSourceEdge newSheet from congrArg Subtype.val hEdge]
      exact hIncident
    have hWall := fine_background_new_incident_right_rel input profile
      sheet newSheet hBackground hNewIncident
    have hNewBackground : ¬(data.vertexPartition wall).Rel
        input.distinguishedBlock.1 newSheet := by
      intro hSelected
      exact hBackground (hSelected.trans hWall.symm)
    let old := fineNewOldEdge input profile newSheet hNewSurvives
    have hOldValue : old.1 = data.sourceEdge (largeTarget input profile) newSheet :=
      fineNewOldEdge_of_background input profile newSheet hNewSurvives hNewBackground
    have hOldIncident : Incident data old.1 (data.sourceEndpoint wall sheet) := by
      rw [hOldValue]
      have hBase := incident_sourceEdge_sourceEndpoint data wall
        (largeTarget input profile) (largeTarget_mem input profile) newSheet
      have hEndpoint : data.sourceEndpoint wall sheet = data.sourceEndpoint wall newSheet := by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact hWall
      rw [hEndpoint]
      exact hBase
    refine ⟨old, hOldIncident, ?_, ?_⟩
    · rw [fineBackgroundReplace_of_large input profile old.1 (by
        rw [hOldValue]
        rfl)]
      rw [hOldValue]
      have hReplace : candidate.newSourceEdge
          (data.sourceEdge (largeTarget input profile) newSheet).1.2 =
          candidate.newSourceEdge newSheet := by
        apply fine_background_new_eq_of_large_source_eq input profile
          newSheet (data.sourceEdge (largeTarget input profile) newSheet).1.2
        · exact hNewBackground
        · exact GluingDatum.sourceEdge_self data
            (data.sourceEdge (largeTarget input profile) newSheet)
      exact hReplace.trans (congrArg Subtype.val hEdge).symm
    · exact (fineRowOfEdge_not_retained input profile edge hOld).trans
        (congrArg NonDanglingEdge.stablePath rfl)

theorem fineRowOfEdge_eq_background
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (first second : NonDanglingEdge (fineCandidate input profile).datum)
    (hNe : first ≠ second)
    (hFirst : Incident (fineCandidate input profile).datum first.1
      ((fineCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet))
    (hSecond : Incident (fineCandidate input profile).datum second.1
      ((fineCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet))
    (hValency : nonDanglingValency (fineCandidate input profile).datum
      ((fineCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet) = 2) :
    fineRowOfEdge input profile first = fineRowOfEdge input profile second := by
  obtain ⟨oldFirst, hOldFirst, hReplaceFirst, hFirstRow⟩ :=
    fineRowOfEdge_incident_background input profile sheet hBackground first hFirst
  obtain ⟨oldSecond, hOldSecond, hReplaceSecond, hSecondRow⟩ :=
    fineRowOfEdge_incident_background input profile sheet hBackground second hSecond
  have hOldValency : nonDanglingValency data (data.sourceEndpoint wall sheet) = 2 :=
    (fine_nonDanglingValency_background input profile sheet hBackground).symm.trans hValency
  have hOldNe : oldFirst ≠ oldSecond := by
    intro hEqual
    apply hNe
    apply Subtype.ext
    rw [← hReplaceFirst, ← hReplaceSecond, hEqual]
  exact hFirstRow.trans ((stablePath_eq_of_consecutive
    ⟨hOldNe, data.sourceEndpoint wall sheet, hOldFirst, hOldSecond,
      hOldValency⟩).trans hSecondRow.symm)

theorem fineRowOfEdge_new_selected
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hSurvives : ¬ IsDangling (fineCandidate input profile).datum
      ((fineCandidate input profile).newSourceEdge sheet)) :
    fineRowOfEdge input profile
        ⟨(fineCandidate input profile).newSourceEdge sheet, hSurvives⟩ =
      NonDanglingEdge.stablePath ⟨profile.large.1, profile.large_survives⟩ := by
  classical
  let candidate := fineCandidate input profile
  let edge : NonDanglingEdge candidate.datum := ⟨candidate.newSourceEdge sheet, hSurvives⟩
  have hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge candidate input.valid.1 old = edge := by
    rintro ⟨old, hEqual⟩
    have hLabels := (occurrenceEquiv target wall candidate.right).injective
      (congrArg (fun occurrence : NonDanglingEdge candidate.datum ↦ occurrence.1.1.1)
        hEqual)
    cases hLabels
  let chosen := fineNewSheet input profile edge hNotOld
  let hChosenSurvives := fineNewSheet_survives input profile edge hNotOld
  have hSpec := fineNewSheet_spec input profile edge hNotOld
  have hNewEqual : candidate.newSourceEdge sheet = candidate.newSourceEdge chosen :=
    congrArg Subtype.val hSpec
  have hNewRel : (finePastedResolution input profile).newEdge.Rel sheet chosen :=
    congrArg (fun item : candidate.datum.SourceEdge ↦ item.1.2) hNewEqual
  have hWallRel : (data.vertexPartition wall).Rel sheet chosen :=
    (finePastedResolution input profile).edge_refines_left.trans
      (LocalResolution.pasteLeft_refines (data.vertexPartition wall)
        candidate.resolution candidate.contracts) |>.rel hNewRel
  have hChosenSelected : (data.vertexPartition wall).Rel
      input.distinguishedBlock.1 chosen := hSelected.trans hWallRel
  calc
    fineRowOfEdge input profile edge =
        (fineNewOldEdge input profile chosen hChosenSurvives).stablePath :=
      fineRowOfEdge_not_retained input profile edge hNotOld
    _ = NonDanglingEdge.stablePath ⟨profile.large.1, profile.large_survives⟩ :=
      congrArg NonDanglingEdge.stablePath
        (fineNewOldEdge_of_selected input profile chosen hChosenSurvives hChosenSelected)

theorem fineRowOfEdge_new_background
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hSurvives : ¬ IsDangling (fineCandidate input profile).datum
      ((fineCandidate input profile).newSourceEdge sheet)) :
    fineRowOfEdge input profile
        ⟨(fineCandidate input profile).newSourceEdge sheet, hSurvives⟩ =
      NonDanglingEdge.stablePath
        ⟨data.sourceEdge (largeTarget input profile) sheet,
          (fine_background_new_survives_iff_oldLarge input profile sheet hBackground).mp
            hSurvives⟩ := by
  classical
  let candidate := fineCandidate input profile
  let edge : NonDanglingEdge candidate.datum := ⟨candidate.newSourceEdge sheet, hSurvives⟩
  have hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge candidate input.valid.1 old = edge := by
    rintro ⟨old, hEqual⟩
    have hLabels := (occurrenceEquiv target wall candidate.right).injective
      (congrArg (fun occurrence : NonDanglingEdge candidate.datum ↦ occurrence.1.1.1)
        hEqual)
    cases hLabels
  let chosen := fineNewSheet input profile edge hNotOld
  let hChosenSurvives := fineNewSheet_survives input profile edge hNotOld
  have hSpec := fineNewSheet_spec input profile edge hNotOld
  have hNewEqual : candidate.newSourceEdge sheet = candidate.newSourceEdge chosen :=
    congrArg Subtype.val hSpec
  have hNewRel : (finePastedResolution input profile).newEdge.Rel sheet chosen :=
    congrArg (fun item : candidate.datum.SourceEdge ↦ item.1.2) hNewEqual
  have hWallRel : (data.vertexPartition wall).Rel sheet chosen :=
    (finePastedResolution input profile).edge_refines_left.trans
      (LocalResolution.pasteLeft_refines (data.vertexPartition wall)
        candidate.resolution candidate.contracts) |>.rel hNewRel
  have hChosenBackground : ¬(data.vertexPartition wall).Rel
      input.distinguishedBlock.1 chosen := by
    intro hSelected
    exact hBackground (hSelected.trans hWallRel.symm)
  have hOldEqual : data.sourceEdge (largeTarget input profile) chosen =
      data.sourceEdge (largeTarget input profile) sheet := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hFineRel : (largePartition input profile).Rel sheet chosen := by
          apply (largePartition input profile).mem_block_iff _ _ |>.mp
          rw [← fine_background_newEdge_block input profile sheet hBackground,
            (finePastedResolution input profile).newEdge.mem_block_iff]
          exact hNewRel
      calc
        (data.sourceEdge (largeTarget input profile) chosen).1.2 =
            (largePartition input profile).repr chosen := rfl
        _ = (largePartition input profile).repr sheet := hFineRel.symm
        _ = (data.sourceEdge (largeTarget input profile) sheet).1.2 := rfl
  have hChosenOld := fineNewOldEdge_of_background input profile chosen
    hChosenSurvives hChosenBackground
  calc
    fineRowOfEdge input profile edge =
        (fineNewOldEdge input profile chosen hChosenSurvives).stablePath :=
      fineRowOfEdge_not_retained input profile edge hNotOld
    _ = NonDanglingEdge.stablePath
        ⟨data.sourceEdge (largeTarget input profile) sheet,
          (fine_background_new_survives_iff_oldLarge input profile sheet hBackground).mp
            hSurvives⟩ := by
      apply congrArg NonDanglingEdge.stablePath
      apply Subtype.ext
      exact hChosenOld.trans hOldEqual

/-- Every surviving row assigned at a selected fresh endpoint is the common
old small/large row.  This proof does not identify the endpoint by wall-block
membership alone: the residual singleton is a distinct fresh endpoint and
its three occurrences dangle. -/
theorem fineRowOfEdge_incident_fresh_selected
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (edge : NonDanglingEdge (fineCandidate input profile).datum)
    (hIncident : Incident (fineCandidate input profile).datum edge.1
      ((fineCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet)) :
    fineRowOfEdge input profile edge =
      NonDanglingEdge.stablePath ⟨profile.large.1, profile.large_survives⟩ := by
  classical
  let candidate := fineCandidate input profile
  rcases nonDanglingEdge_cases candidate input.valid
      (fineCandidate_sourceGenus input profile) edge with ⟨old, rfl⟩ | ⟨other, hSurvives, rfl⟩
  · rw [fineRowOfEdge_retained]
    have hInfo := old_incident_fresh_selected_info candidate input.distinguishedBlock
      sheet hSelected old.1 hIncident
    rcases selected_survivor_eq_small_or_large input profile old hInfo.1 with
      hSmall | hLarge
    · have hOld : old =
          (⟨profile.small.1, profile.small_survives⟩ : NonDanglingEdge data) :=
        Subtype.ext hSmall
      have hPath := congrArg NonDanglingEdge.stablePath hOld
      exact hPath.trans profile.stablePath_eq
    · have hTargetLarge := congrArg (fun source : data.SourceEdge ↦ source.1.1) hLarge
      have hWrong : candidate.right (largeTarget input profile) = true :=
        (congrArg candidate.right hTargetLarge.symm).trans hInfo.2
      change rightOf (largeTarget input profile) (largeTarget input profile) = true at hWrong
      simp [rightOf] at hWrong
  · have hData := (incident_iff_target_mem_and_rel candidate.datum
      (candidate.newSourceEdge other)
      (candidate.datum.sourceEndpoint (freshVertex target) sheet)).mp hIncident
    simp only [GluingDatum.sourceEndpoint, candidate.newSourceEdge_target,
      candidate.newSourceEdge_sheet] at hData
    have hVertex : candidate.datum.vertexPartition (freshVertex target) =
        (finePastedResolution input profile).right :=
      GlobalResolution.expandedVertexPartition_fresh data wall _
    rw [hVertex] at hData
    have hRel := hData.2
    have hRightRel : (finePastedResolution input profile).right.Rel sheet
        ((finePastedResolution input profile).newEdge.repr other) := by
      change (finePastedResolution input profile).right.Rel
        ((finePastedResolution input profile).right.repr sheet)
        ((finePastedResolution input profile).newEdge.repr other) at hRel
      exact (finePastedResolution input profile).right.rel_repr_right sheet |>.trans hRel
    have hWallRepr : (data.vertexPartition wall).Rel sheet
        ((finePastedResolution input profile).newEdge.repr other) :=
      (LocalResolution.pasteRight_refines (data.vertexPartition wall)
        candidate.resolution candidate.contracts).rel hRightRel
    have hWallOther : (data.vertexPartition wall).Rel sheet other :=
      hWallRepr.trans ((finePastedResolution input profile).edge_refines_right.trans
        (LocalResolution.pasteRight_refines (data.vertexPartition wall)
          candidate.resolution candidate.contracts) |>.rel
            ((finePastedResolution input profile).newEdge.rel_repr_left other))
    exact fineRowOfEdge_new_selected input profile other
      (hSelected.trans hWallOther) hSurvives

/-- Every surviving row assigned at the selected old (divalent-side)
endpoint is the common old small/large row. -/
theorem fineRowOfEdge_incident_left_selected
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (edge : NonDanglingEdge (fineCandidate input profile).datum)
    (hIncident : Incident (fineCandidate input profile).datum edge.1
      ((fineCandidate input profile).datum.sourceEndpoint (oldVertex target wall) sheet)) :
    fineRowOfEdge input profile edge =
      NonDanglingEdge.stablePath ⟨profile.large.1, profile.large_survives⟩ := by
  classical
  let candidate := fineCandidate input profile
  rcases nonDanglingEdge_cases candidate input.valid
      (fineCandidate_sourceGenus input profile) edge with ⟨old, rfl⟩ | ⟨other, hSurvives, rfl⟩
  · rw [fineRowOfEdge_retained]
    have hData := (incident_iff_target_mem_and_rel candidate.datum
      (candidate.oldSourceEdge old.1)
      (candidate.datum.sourceEndpoint (oldVertex target wall) sheet)).mp hIncident
    simp only [GluingDatum.sourceEndpoint, candidate.oldSourceEdge_target,
      candidate.oldSourceEdge_sheet] at hData
    have hVertex : candidate.datum.vertexPartition (oldVertex target wall) =
        (finePastedResolution input profile).left :=
      GlobalResolution.expandedVertexPartition_old_wall data wall _
    rw [hVertex] at hData
    have hTarget := hData.1
    rw [fine_left_target_incident_pair input profile] at hTarget
    rcases Finset.mem_insert.mp hTarget with hNew | hLargeTarget
    · have hLabels := (occurrenceEquiv target wall candidate.right).injective hNew
      cases hLabels
    · have hOldTarget : old.1.1.1 = largeTarget input profile :=
        Option.some.inj ((occurrenceEquiv target wall candidate.right).injective
          (Finset.mem_singleton.mp hLargeTarget))
      have hLeftRel : (finePastedResolution input profile).left.Rel sheet old.1.1.2 := by
        have hRel := hData.2
        change (finePastedResolution input profile).left.Rel
          ((finePastedResolution input profile).left.repr sheet) old.1.1.2 at hRel
        exact (finePastedResolution input profile).left.rel_repr_right sheet |>.trans hRel
      have hWallRel : (data.vertexPartition wall).Rel sheet old.1.1.2 :=
        (LocalResolution.pasteLeft_refines (data.vertexPartition wall)
          candidate.resolution candidate.contracts).rel hLeftRel
      have hOldIncident : Incident data old.1
          (WallBlock.sourceVertex data wall input.distinguishedBlock) := by
        apply (incident_wallBlock_sourceVertex_iff data input.distinguishedBlock old.1).mpr
        refine ⟨hOldTarget ▸ largeTarget_mem input profile, ?_⟩
        apply Subtype.ext
        exact (hSelected.trans hWallRel).symm.trans input.distinguishedBlock.2
      rcases selected_survivor_eq_small_or_large input profile old hOldIncident with
        hOldSmall | hOldLarge
      · have hSmallTarget := congrArg (fun source : data.SourceEdge ↦ source.1.1)
          hOldSmall
        exact (profile.target_ne (hSmallTarget.symm.trans hOldTarget)).elim
      · exact congrArg NonDanglingEdge.stablePath (Subtype.ext hOldLarge)
  · have hData := (incident_iff_target_mem_and_rel candidate.datum
      (candidate.newSourceEdge other)
      (candidate.datum.sourceEndpoint (oldVertex target wall) sheet)).mp hIncident
    simp only [GluingDatum.sourceEndpoint, candidate.newSourceEdge_target,
      candidate.newSourceEdge_sheet] at hData
    have hVertex : candidate.datum.vertexPartition (oldVertex target wall) =
        (finePastedResolution input profile).left :=
      GlobalResolution.expandedVertexPartition_old_wall data wall _
    rw [hVertex] at hData
    have hRel := hData.2
    have hLeftRel : (finePastedResolution input profile).left.Rel sheet
        ((finePastedResolution input profile).newEdge.repr other) := by
      change (finePastedResolution input profile).left.Rel
        ((finePastedResolution input profile).left.repr sheet)
        ((finePastedResolution input profile).newEdge.repr other) at hRel
      exact (finePastedResolution input profile).left.rel_repr_right sheet |>.trans hRel
    have hLeftOther : (finePastedResolution input profile).left.Rel sheet other :=
      hLeftRel.trans ((finePastedResolution input profile).edge_refines_left.rel
        ((finePastedResolution input profile).newEdge.rel_repr_left other))
    have hWallOther : (data.vertexPartition wall).Rel sheet other :=
      (LocalResolution.pasteLeft_refines (data.vertexPartition wall)
        candidate.resolution candidate.contracts).rel hLeftOther
    exact fineRowOfEdge_new_selected input profile other
      (hSelected.trans hWallOther) hSurvives

theorem fineRowOfEdge_incident_left_background
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (edge : NonDanglingEdge (fineCandidate input profile).datum)
    (hIncident : Incident (fineCandidate input profile).datum edge.1
      ((fineCandidate input profile).datum.sourceEndpoint (oldVertex target wall) sheet)) :
    ∃ hOld : ¬ IsDangling data (data.sourceEdge (largeTarget input profile) sheet),
      fineRowOfEdge input profile edge = NonDanglingEdge.stablePath
        ⟨data.sourceEdge (largeTarget input profile) sheet, hOld⟩ := by
  classical
  let candidate := fineCandidate input profile
  rcases nonDanglingEdge_cases candidate input.valid
      (fineCandidate_sourceGenus input profile) edge with ⟨old, rfl⟩ | ⟨other, hSurvives, rfl⟩
  · have hData := (incident_iff_target_mem_and_rel candidate.datum
      (candidate.oldSourceEdge old.1)
      (candidate.datum.sourceEndpoint (oldVertex target wall) sheet)).mp hIncident
    simp only [GluingDatum.sourceEndpoint, candidate.oldSourceEdge_target,
      candidate.oldSourceEdge_sheet] at hData
    have hVertex : candidate.datum.vertexPartition (oldVertex target wall) =
        (finePastedResolution input profile).left :=
      GlobalResolution.expandedVertexPartition_old_wall data wall _
    rw [hVertex] at hData
    have hTarget := hData.1
    rw [fine_left_target_incident_pair input profile] at hTarget
    rcases Finset.mem_insert.mp hTarget with hNew | hLarge
    · have hLabels := (occurrenceEquiv target wall candidate.right).injective hNew
      cases hLabels
    · have hOldTarget : old.1.1.1 = largeTarget input profile :=
        Option.some.inj ((occurrenceEquiv target wall candidate.right).injective
          (Finset.mem_singleton.mp hLarge))
      have hRel := hData.2
      have hLeftRel : (finePastedResolution input profile).left.Rel
          sheet old.1.1.2 := by
        change (finePastedResolution input profile).left.Rel
          ((finePastedResolution input profile).left.repr sheet) old.1.1.2 at hRel
        exact (finePastedResolution input profile).left.rel_repr_right sheet |>.trans hRel
      have hFineRel : (largePartition input profile).Rel sheet old.1.1.2 := by
        apply (largePartition input profile).mem_block_iff _ _ |>.mp
        rw [← fine_background_left_block input profile sheet hBackground,
          (finePastedResolution input profile).left.mem_block_iff]
        exact hLeftRel
      have hOldEq : old.1 = data.sourceEdge (largeTarget input profile) sheet := by
        apply Subtype.ext
        apply Prod.ext
        · exact hOldTarget
        · calc
            old.1.1.2 = (largePartition input profile).repr old.1.1.2 := by
              have hCanonical := old.1.2
              change (data.edgePartition old.1.1.1).repr old.1.1.2 = old.1.1.2 at hCanonical
              rw [hOldTarget] at hCanonical
              exact hCanonical.symm
            _ = (largePartition input profile).repr sheet := hFineRel.symm
            _ = (data.sourceEdge (largeTarget input profile) sheet).1.2 := rfl
      refine ⟨hOldEq ▸ old.2, ?_⟩
      rw [fineRowOfEdge_retained]
      exact congrArg NonDanglingEdge.stablePath (Subtype.ext hOldEq)
  · have hData := (incident_iff_target_mem_and_rel candidate.datum
      (candidate.newSourceEdge other)
      (candidate.datum.sourceEndpoint (oldVertex target wall) sheet)).mp hIncident
    simp only [GluingDatum.sourceEndpoint, candidate.newSourceEdge_target,
      candidate.newSourceEdge_sheet] at hData
    have hVertex : candidate.datum.vertexPartition (oldVertex target wall) =
        (finePastedResolution input profile).left :=
      GlobalResolution.expandedVertexPartition_old_wall data wall _
    rw [hVertex] at hData
    have hRel := hData.2
    have hLeftRel : (finePastedResolution input profile).left.Rel sheet
        ((finePastedResolution input profile).newEdge.repr other) := by
      change (finePastedResolution input profile).left.Rel
        ((finePastedResolution input profile).left.repr sheet)
        ((finePastedResolution input profile).newEdge.repr other) at hRel
      exact (finePastedResolution input profile).left.rel_repr_right sheet |>.trans hRel
    have hLeftRelOther : (finePastedResolution input profile).left.Rel sheet other :=
      hLeftRel.trans ((finePastedResolution input profile).edge_refines_left.rel
        ((finePastedResolution input profile).newEdge.rel_repr_left other))
    have hWallOther : (data.vertexPartition wall).Rel sheet other :=
      (LocalResolution.pasteLeft_refines (data.vertexPartition wall)
        candidate.resolution candidate.contracts).rel hLeftRelOther
    have hOtherBackground : ¬(data.vertexPartition wall).Rel
        input.distinguishedBlock.1 other := by
      intro hSelected
      exact hBackground (hSelected.trans hWallOther.symm)
    have hNewRel : (finePastedResolution input profile).newEdge.Rel sheet other := by
      apply (finePastedResolution input profile).newEdge.mem_block_iff _ _ |>.mp
      rw [fine_background_newEdge_block input profile sheet hBackground]
      apply (largePartition input profile).mem_block_iff _ _ |>.mpr
      apply (largePartition input profile).mem_block_iff _ _ |>.mp
      rw [← fine_background_left_block input profile sheet hBackground,
        (finePastedResolution input profile).left.mem_block_iff]
      exact hLeftRelOther
    have hFineRel : (largePartition input profile).Rel sheet other := by
      apply (largePartition input profile).mem_block_iff _ _ |>.mp
      rw [← fine_background_newEdge_block input profile sheet hBackground,
        (finePastedResolution input profile).newEdge.mem_block_iff]
      exact hNewRel
    have hOldEq : data.sourceEdge (largeTarget input profile) other =
        data.sourceEdge (largeTarget input profile) sheet := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact hFineRel.symm
    have hOldOther := (fine_background_new_survives_iff_oldLarge input profile
      other hOtherBackground).mp hSurvives
    have hOldSheet : ¬ IsDangling data (data.sourceEdge
        (largeTarget input profile) sheet) := hOldEq.symm ▸ hOldOther
    refine ⟨hOldSheet, ?_⟩
    exact (fineRowOfEdge_new_background input profile other hOtherBackground
      hSurvives).trans (congrArg NonDanglingEdge.stablePath (Subtype.ext hOldEq))

/-- Away from the expanded wall, both consecutive survivors are retained and
their assigned rows are the corresponding old consecutive rows. -/
theorem fineRowOfEdge_eq_away
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (vertex : data.SourceVertex) (hAway : vertex.1.1 ≠ wall)
    (first second : NonDanglingEdge (fineCandidate input profile).datum)
    (hFirst : Incident (fineCandidate input profile).datum first.1
      (retainedVertex (fineCandidate input profile) vertex))
    (hSecond : Incident (fineCandidate input profile).datum second.1
      (retainedVertex (fineCandidate input profile) vertex))
    (hValency : nonDanglingValency (fineCandidate input profile).datum
      (retainedVertex (fineCandidate input profile) vertex) = 2) :
    fineRowOfEdge input profile first = fineRowOfEdge input profile second := by
  classical
  let candidate := fineCandidate input profile
  have hGenus := fineCandidate_sourceGenus input profile
  rcases nonDanglingEdge_cases candidate input.valid hGenus first with
      ⟨oldFirst, rfl⟩ | ⟨sheet, hSurvives, rfl⟩
  · rcases nonDanglingEdge_cases candidate input.valid hGenus second with
        ⟨oldSecond, rfl⟩ | ⟨sheet, hSurvives, rfl⟩
    · rw [fineRowOfEdge_retained, fineRowOfEdge_retained]
      by_cases hEqual : oldFirst = oldSecond
      · exact congrArg NonDanglingEdge.stablePath hEqual
      · exact stablePath_eq_of_consecutive ⟨hEqual, vertex,
          (incident_oldSourceEdge_iff candidate vertex hAway oldFirst.1).mp hFirst,
          (incident_oldSourceEdge_iff candidate vertex hAway oldSecond.1).mp hSecond,
          (nonDanglingValency_retainedVertex candidate input.valid hGenus vertex hAway).symm.trans
            hValency⟩
    · exact (not_incident_newSourceEdge candidate vertex hAway sheet hSecond).elim
  · exact (not_incident_newSourceEdge candidate vertex hAway sheet hFirst).elim

/-- The fine reverse assignment is constant on every actual consecutive
pair, with selected and background wall blocks treated by their literal local
censuses. -/
theorem fineRowOfEdge_eq_of_consecutive
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (first second : NonDanglingEdge (fineCandidate input profile).datum)
    (hConsecutive : Consecutive (fineCandidate input profile).datum first second) :
    fineRowOfEdge input profile first = fineRowOfEdge input profile second := by
  classical
  let candidate := fineCandidate input profile
  obtain ⟨hNe, vertex, hFirst, hSecond, hValency⟩ := hConsecutive
  have hSelf : candidate.datum.sourceEndpoint vertex.1.1 vertex.1.2 = vertex :=
    (candidate.datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨rfl, rfl⟩
  cases hTarget : vertex.1.1 with
  | inl place =>
      by_cases hAt : place = wall
      · subst place
        have hEndpoint : candidate.datum.sourceEndpoint (oldVertex target wall)
            vertex.1.2 = vertex := by
          exact (congrArg (fun place ↦ candidate.datum.sourceEndpoint place vertex.1.2)
            hTarget.symm).trans hSelf
        rw [← hEndpoint] at hFirst hSecond
        by_cases hSelected : (data.vertexPartition wall).Rel
            input.distinguishedBlock.1 vertex.1.2
        · exact (fineRowOfEdge_incident_left_selected input profile _ hSelected first
            hFirst).trans (fineRowOfEdge_incident_left_selected input profile _ hSelected
              second hSecond).symm
        · obtain ⟨hOldFirst, hFirstRow⟩ :=
            fineRowOfEdge_incident_left_background input profile _ hSelected first hFirst
          obtain ⟨hOldSecond, hSecondRow⟩ :=
            fineRowOfEdge_incident_left_background input profile _ hSelected second hSecond
          exact hFirstRow.trans hSecondRow.symm
      · obtain ⟨old, hOld, hVertex⟩ :=
          exists_retainedVertex_of_target candidate vertex place hAt hTarget
        rw [← hVertex] at hFirst hSecond hValency
        exact fineRowOfEdge_eq_away input profile old (hOld ▸ hAt) first second
          hFirst hSecond hValency
  | inr point =>
      cases point
      have hEndpoint : candidate.datum.sourceEndpoint (freshVertex target) vertex.1.2 =
          vertex := by
        exact (congrArg (fun place ↦ candidate.datum.sourceEndpoint place vertex.1.2)
          hTarget.symm).trans hSelf
      rw [← hEndpoint] at hFirst hSecond hValency
      by_cases hSelected : (data.vertexPartition wall).Rel
          input.distinguishedBlock.1 vertex.1.2
      · exact (fineRowOfEdge_incident_fresh_selected input profile _ hSelected first
          hFirst).trans (fineRowOfEdge_incident_fresh_selected input profile _ hSelected
            second hSecond).symm
      · exact fineRowOfEdge_eq_background input profile _ hSelected first second hNe
          hFirst hSecond hValency

/-- The explicit reverse row assignment descends through the stable-path
quotient. -/
noncomputable def fineStablePathDescend
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    StablePath (fineCandidate input profile).datum → StablePath data :=
  Quot.lift (fineRowOfEdge input profile)
    (fineRowOfEdge_eq_of_consecutive input profile)

@[simp] theorem fineStablePathDescend_mk
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (edge : NonDanglingEdge (fineCandidate input profile).datum) :
    fineStablePathDescend input profile edge.stablePath =
      fineRowOfEdge input profile edge := rfl

/-- Descent is a literal left inverse on every old retained row. -/
theorem fineStablePathDescend_lift
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (path : StablePath data) :
    fineStablePathDescend input profile (fineStablePathLift input profile path) = path := by
  induction path using Quot.inductionOn with
  | h edge => exact fineRowOfEdge_retained input profile edge

theorem fineStablePathLift_injective
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    Function.Injective (fineStablePathLift input profile) :=
  Function.LeftInverse.injective (fineStablePathDescend_lift input profile)

/-- The true Figure 31 fine member's stable rows are equivalent via the
actual retained-occurrence map. -/
noncomputable def fineStablePathEquiv
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    StablePath data ≃ StablePath (fineCandidate input profile).datum :=
  Equiv.ofBijective (fineStablePathLift input profile)
    ⟨fineStablePathLift_injective input profile,
      fineStablePathLift_surjective input profile⟩

@[simp] theorem fineStablePathEquiv_mk
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (edge : NonDanglingEdge data) :
    fineStablePathEquiv input profile edge.stablePath =
      (retainedEdge (fineCandidate input profile) input.valid.1 edge).stablePath := rfl

end DraismaVargas.LocalCases.W3Nd2FineRowDescent
