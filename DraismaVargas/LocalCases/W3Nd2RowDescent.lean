module

public import DraismaVargas.LocalCases.W3Nd2StableLift

@[expose] public section

/-!
# Reverse row transport for the true Figure 31 coarse resolution

The coarse background replaces each old small-direction occurrence by the
corresponding new occurrence and retains every other old occurrence.  The
first step below proves this is a literal bijection on surviving incidence
sets at every unramified wall block, without assuming that the old block is
divalent. The quotient descent and its literal left inverse prove the coarse
stable-row equivalence. The complementary fine reverse map is treated
separately.
-/

namespace DraismaVargas.LocalCases.W3Nd2RowDescent

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

/-- The actual occurrence replacement on a coarse background star: the old
small direction becomes the new arm and every other direction is retained. -/
noncomputable def coarseBackgroundReplace
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (old : data.SourceEdge) : (coarseCandidate input profile).datum.SourceEdge :=
  if old.1.1 = smallTarget input profile then
    (coarseCandidate input profile).newSourceEdge old.1.2
  else (coarseCandidate input profile).oldSourceEdge old

theorem coarseBackgroundReplace_of_small
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (old : data.SourceEdge) (hTarget : old.1.1 = smallTarget input profile) :
    coarseBackgroundReplace input profile old =
      (coarseCandidate input profile).newSourceEdge old.1.2 := by
  rw [coarseBackgroundReplace, ite_eq_left hTarget]

theorem coarseBackgroundReplace_of_ne_small
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (old : data.SourceEdge) (hTarget : old.1.1 ≠ smallTarget input profile) :
    coarseBackgroundReplace input profile old =
      (coarseCandidate input profile).oldSourceEdge old := by
  rw [coarseBackgroundReplace, ite_eq_right hTarget]

/-- Replacement preserves and reflects survival and incidence at an
unramified background source vertex. -/
theorem coarseBackgroundReplace_mem_iff
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (old : data.SourceEdge) :
    coarseBackgroundReplace input profile old ∈
        nonDanglingIncident (coarseCandidate input profile).datum
          ((coarseCandidate input profile).datum.sourceEndpoint
            (freshVertex target) sheet) ↔
      old ∈ nonDanglingIncident data (data.sourceEndpoint wall sheet) := by
  classical
  by_cases hTarget : old.1.1 = smallTarget input profile
  · rw [coarseBackgroundReplace_of_small input profile old hTarget]
    constructor
    · intro hMem
      obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
      have hWall := coarse_background_new_incident_right_rel
        input profile sheet old.1.2 hSheet hIncident
      have hOldSheet : ¬(data.vertexPartition wall).Rel
          input.distinguishedBlock.1 old.1.2 := by
        intro hDist
        exact hSheet (hDist.trans hWall.symm)
      have hOldSurvives : ¬ IsDangling data old := by
        have hCanonical : data.sourceEdge (smallTarget input profile) old.1.2 = old := by
          rw [← hTarget]
          exact GluingDatum.sourceEdge_self data old
        have := (coarse_background_new_survives_iff_oldSmall
          input profile old.1.2 hOldSheet).mp hSurvives
        simpa [hCanonical] using this
      have hOldIncident : Incident data old (data.sourceEndpoint wall sheet) := by
        apply (incident_iff_target_mem_and_rel data old _).mpr
        refine ⟨hTarget ▸ smallTarget_mem input profile, ?_⟩
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
      have hCanonical : data.sourceEdge (smallTarget input profile) old.1.2 = old := by
        rw [← hTarget]
        exact GluingDatum.sourceEdge_self data old
      apply (mem_nonDanglingIncident _ _ _).mpr
      refine ⟨(coarse_background_new_survives_iff_oldSmall input profile
        old.1.2 hOldSheet).mpr (by simpa [hCanonical] using hSurvives), ?_⟩
      exact coarse_background_new_incident_right input profile sheet old.1.2 hSheet hWall
  · rw [coarseBackgroundReplace_of_ne_small input profile old hTarget]
    rw [mem_nonDanglingIncident, mem_nonDanglingIncident]
    rw [coarse_old_isDangling_iff input profile old,
      coarse_background_old_incident_right_iff input profile sheet hSheet old]
    tauto

/-- Every surviving incidence at a coarse fresh background endpoint is the
replacement of an actual old surviving incidence. -/
theorem coarseBackgroundReplace_surjective_on_incidence
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (edge : (coarseCandidate input profile).datum.SourceEdge)
    (hEdge : edge ∈ nonDanglingIncident (coarseCandidate input profile).datum
      ((coarseCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet)) :
    ∃ old : data.SourceEdge,
      old ∈ nonDanglingIncident data (data.sourceEndpoint wall sheet) ∧
        coarseBackgroundReplace input profile old = edge := by
  classical
  let candidate := coarseCandidate input profile
  obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hEdge
  rcases sourceEdge_cases candidate edge with ⟨old, rfl⟩ | ⟨other, rfl⟩
  · have hOldTarget :=
      (coarse_background_old_incident_right_iff input profile sheet hSheet old).mp
        hIncident |>.2
    have hReplace := coarseBackgroundReplace_of_ne_small input profile old hOldTarget
    refine ⟨old, (coarseBackgroundReplace_mem_iff input profile sheet hSheet old).mp ?_, hReplace⟩
    rw [hReplace]
    exact hEdge
  · have hWall := coarse_background_new_incident_right_rel
      input profile sheet other hSheet hIncident
    let old := data.sourceEdge (smallTarget input profile) other
    have hOldSheet : ¬(data.vertexPartition wall).Rel
        input.distinguishedBlock.1 old.1.2 := by
      intro hDist
      apply hSheet
      have hFineWall := (fine_refines_wall input profile).rel
        ((finePartition input profile).rel_repr_left other)
      exact hDist.trans (hFineWall.trans hWall.symm)
    have hOldTarget : old.1.1 = smallTarget input profile := rfl
    refine ⟨old, (coarseBackgroundReplace_mem_iff input profile sheet hSheet old).mp ?_, ?_⟩
    · rw [coarseBackgroundReplace_of_small input profile old hOldTarget]
      have hEq : candidate.newSourceEdge old.1.2 = candidate.newSourceEdge other := by
        apply coarse_background_new_eq_of_small_source_eq input profile other old.1.2
        · intro hDist
          exact hSheet (hDist.trans hWall.symm)
        · exact GluingDatum.sourceEdge_self data old
      rw [hEq]
      exact hEdge
    · rw [coarseBackgroundReplace_of_small input profile old hOldTarget]
      apply coarse_background_new_eq_of_small_source_eq input profile other old.1.2
      · intro hDist
        exact hSheet (hDist.trans hWall.symm)
      · exact GluingDatum.sourceEdge_self data old

/-- Distinct old surviving incidences have distinct replacements.  In the
small/small case this is exactly the equality of the old small partition and
the new-edge partition on a background block. -/
theorem coarseBackgroundReplace_injective_on_incidence
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (first second : data.SourceEdge)
    (hFirst : first ∈ nonDanglingIncident data (data.sourceEndpoint wall sheet))
    (_hSecond : second ∈ nonDanglingIncident data (data.sourceEndpoint wall sheet))
    (hEqual : coarseBackgroundReplace input profile first =
      coarseBackgroundReplace input profile second) : first = second := by
  classical
  let candidate := coarseCandidate input profile
  by_cases hFirstTarget : first.1.1 = smallTarget input profile
  · by_cases hSecondTarget : second.1.1 = smallTarget input profile
    · rw [coarseBackgroundReplace_of_small input profile first hFirstTarget,
        coarseBackgroundReplace_of_small input profile second hSecondTarget] at hEqual
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
      have hNewRel : (coarsePastedResolution input profile).newEdge.Rel
          first.1.2 second.1.2 := hNewRepr
      have hFineRel : (finePartition input profile).Rel first.1.2 second.1.2 := by
        apply (finePartition input profile).mem_block_iff _ _ |>.mp
        rw [← coarse_background_newEdge_block input profile first.1.2 hFirstSheet,
          (coarsePastedResolution input profile).newEdge.mem_block_iff]
        exact hNewRel
      apply Subtype.ext
      apply Prod.ext
      · exact hFirstTarget.trans hSecondTarget.symm
      · have hFirstRepr : (finePartition input profile).repr first.1.2 = first.1.2 := by
          change (data.edgePartition (smallTarget input profile)).repr first.1.2 = first.1.2
          rw [← hFirstTarget]
          exact first.2
        have hSecondRepr : (finePartition input profile).repr second.1.2 = second.1.2 := by
          change (data.edgePartition (smallTarget input profile)).repr second.1.2 = second.1.2
          rw [← hSecondTarget]
          exact second.2
        exact hFirstRepr.symm.trans (hFineRel.trans hSecondRepr)
    · rw [coarseBackgroundReplace_of_small input profile first hFirstTarget,
        coarseBackgroundReplace_of_ne_small input profile second hSecondTarget] at hEqual
      have hLabels := (occurrenceEquiv target wall candidate.right).injective
        (congrArg (fun edge : candidate.datum.SourceEdge ↦ edge.1.1) hEqual)
      cases hLabels
  · by_cases hSecondTarget : second.1.1 = smallTarget input profile
    · rw [coarseBackgroundReplace_of_ne_small input profile first hFirstTarget,
        coarseBackgroundReplace_of_small input profile second hSecondTarget] at hEqual
      have hLabels := (occurrenceEquiv target wall candidate.right).injective
        (congrArg (fun edge : candidate.datum.SourceEdge ↦ edge.1.1) hEqual)
      cases hLabels
    · rw [coarseBackgroundReplace_of_ne_small input profile first hFirstTarget,
        coarseBackgroundReplace_of_ne_small input profile second hSecondTarget] at hEqual
      exact ResolutionCut.oldSourceEdge_injective candidate hEqual

/-- The complete surviving incidence set is the image of the old one under
the literal small-to-new replacement. -/
theorem coarse_nonDanglingIncident_background_image
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    nonDanglingIncident (coarseCandidate input profile).datum
        ((coarseCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet) =
      (nonDanglingIncident data (data.sourceEndpoint wall sheet)).image
        (coarseBackgroundReplace input profile) := by
  classical
  ext edge
  constructor
  · intro hEdge
    obtain ⟨old, hOld, hReplace⟩ :=
      coarseBackgroundReplace_surjective_on_incidence input profile sheet hSheet edge hEdge
    exact Finset.mem_image.mpr ⟨old, hOld, hReplace⟩
  · intro hEdge
    obtain ⟨old, hOld, rfl⟩ := Finset.mem_image.mp hEdge
    exact (coarseBackgroundReplace_mem_iff input profile sheet hSheet old).mpr hOld

/-- Hence pruning valency is preserved at every coarse background fresh
vertex, including old nd3 blocks. -/
theorem coarse_nonDanglingValency_background
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    nonDanglingValency (coarseCandidate input profile).datum
        ((coarseCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet) =
      nonDanglingValency data (data.sourceEndpoint wall sheet) := by
  classical
  rw [← card_nonDanglingIncident,
    coarse_nonDanglingIncident_background_image input profile sheet hSheet,
    Finset.card_image_iff.mpr]
  · rw [card_nonDanglingIncident]
  · intro first hFirst second hSecond hEqual
    exact coarseBackgroundReplace_injective_on_incidence input profile sheet hSheet
      first second hFirst hSecond hEqual

/-- Decode an occurrence of the coarse resolved source back to an actual old
surviving occurrence.  Retained occurrences use their literal preimage; a new
occurrence uses the old small-direction occurrence on its canonical sheet,
except that all selected sheets use the profile's fixed small survivor. -/
noncomputable def coarseOldEdgeOf
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (edge : NonDanglingEdge (coarseCandidate input profile).datum) :
    NonDanglingEdge data := by
  let candidate := coarseCandidate input profile
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
              (coarsePastedResolution input profile).newEdge :=
            GlobalResolution.expandedEdgePartition_new data wall _ _
          rw [hTarget, hPartition] at hCanonical
          change (coarsePastedResolution input profile).newEdge.repr edge.1.1.2 =
            edge.1.1.2
          exact hCanonical
      by_cases hSelected : (data.vertexPartition wall).Rel
          input.distinguishedBlock.1 edge.1.1.2
      · exact ⟨profile.small.1, profile.small_survives⟩
      · have hNewSurvives : ¬ IsDangling candidate.datum
            (candidate.newSourceEdge edge.1.1.2) := by
          rw [hEdge]
          exact edge.2
        exact ⟨data.sourceEdge (smallTarget input profile) edge.1.1.2,
          (coarse_background_new_survives_iff_oldSmall input profile
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
          (coarse_old_isDangling_iff input profile old).mpr hDangling
        rw [hEdge] at hCandidateDangling
        exact edge.2 hCandidateDangling
      exact ⟨old, hOldSurvives⟩

/-- The old source occurrence represented by a new coarse occurrence. -/
noncomputable def coarseNewOldSourceEdge
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree) : data.SourceEdge :=
  if (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet then
    profile.small.1
  else data.sourceEdge (smallTarget input profile) sheet

theorem coarseNewOldSourceEdge_survives
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (coarseCandidate input profile).datum
      ((coarseCandidate input profile).newSourceEdge sheet)) :
    ¬ IsDangling data (coarseNewOldSourceEdge input profile sheet) := by
  classical
  by_cases hSelected : (data.vertexPartition wall).Rel
      input.distinguishedBlock.1 sheet
  · rw [coarseNewOldSourceEdge, ite_eq_left hSelected]
    exact profile.small_survives
  · rw [coarseNewOldSourceEdge, ite_eq_right hSelected]
    exact (coarse_background_new_survives_iff_oldSmall input profile sheet hSelected).mp
      hSurvives

noncomputable def coarseNewOldEdge
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (coarseCandidate input profile).datum
      ((coarseCandidate input profile).newSourceEdge sheet)) : NonDanglingEdge data :=
  ⟨coarseNewOldSourceEdge input profile sheet,
    coarseNewOldSourceEdge_survives input profile sheet hSurvives⟩

theorem coarse_new_representation
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (edge : NonDanglingEdge (coarseCandidate input profile).datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge (coarseCandidate input profile) input.valid.1 old = edge) :
    ∃ sheet : Fin degree, ∃ hSurvives : ¬ IsDangling
        (coarseCandidate input profile).datum
        ((coarseCandidate input profile).newSourceEdge sheet),
      edge = ⟨(coarseCandidate input profile).newSourceEdge sheet, hSurvives⟩ := by
  let candidate := coarseCandidate input profile
  rcases nonDanglingEdge_cases candidate input.valid
      (coarseCandidate_sourceGenus input profile) edge with ⟨old, hOld⟩ | ⟨sheet, hSurvives, hNew⟩
  · exact (hNotOld ⟨old, hOld.symm⟩).elim
  · exact ⟨sheet, hSurvives, hNew⟩

noncomputable def coarseNewSheet
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (edge : NonDanglingEdge (coarseCandidate input profile).datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge (coarseCandidate input profile) input.valid.1 old = edge) : Fin degree :=
  (coarse_new_representation input profile edge hNotOld).choose

theorem coarseNewSheet_survives
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (edge : NonDanglingEdge (coarseCandidate input profile).datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge (coarseCandidate input profile) input.valid.1 old = edge) :
    ¬ IsDangling (coarseCandidate input profile).datum
      ((coarseCandidate input profile).newSourceEdge
        (coarseNewSheet input profile edge hNotOld)) :=
  (coarse_new_representation input profile edge hNotOld).choose_spec.choose

theorem coarseNewSheet_spec
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (edge : NonDanglingEdge (coarseCandidate input profile).datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge (coarseCandidate input profile) input.valid.1 old = edge) :
    edge = ⟨(coarseCandidate input profile).newSourceEdge
        (coarseNewSheet input profile edge hNotOld),
      coarseNewSheet_survives input profile edge hNotOld⟩ :=
  (coarse_new_representation input profile edge hNotOld).choose_spec.choose_spec

/-- Retained occurrences return to their literal preimage; otherwise use the
actual old small occurrence represented by the decoded new occurrence. -/
noncomputable def coarseRowOfEdge
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (edge : NonDanglingEdge (coarseCandidate input profile).datum) : StablePath data := by
  classical
  exact if hOld : ∃ old : NonDanglingEdge data,
      retainedEdge (coarseCandidate input profile) input.valid.1 old = edge then
    (Classical.choose hOld).stablePath
  else
    (coarseNewOldEdge input profile (coarseNewSheet input profile edge hOld)
      (coarseNewSheet_survives input profile edge hOld)).stablePath

@[simp] theorem coarseRowOfEdge_retained
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (old : NonDanglingEdge data) :
    coarseRowOfEdge input profile
      (retainedEdge (coarseCandidate input profile) input.valid.1 old) =
        old.stablePath := by
  classical
  have hOld : ∃ other : NonDanglingEdge data,
      retainedEdge (coarseCandidate input profile) input.valid.1 other =
        retainedEdge (coarseCandidate input profile) input.valid.1 old := ⟨old, rfl⟩
  rw [coarseRowOfEdge, dite_eq_left hOld]
  exact congrArg NonDanglingEdge.stablePath
    (retainedEdge_injective _ input.valid.1 (Classical.choose_spec hOld))

theorem coarseRowOfEdge_not_retained
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (edge : NonDanglingEdge (coarseCandidate input profile).datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge (coarseCandidate input profile) input.valid.1 old = edge) :
    coarseRowOfEdge input profile edge =
      (coarseNewOldEdge input profile (coarseNewSheet input profile edge hNotOld)
        (coarseNewSheet_survives input profile edge hNotOld)).stablePath := by
  classical
  exact dite_eq_right hNotOld

theorem coarseNewOldEdge_of_selected
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (coarseCandidate input profile).datum
      ((coarseCandidate input profile).newSourceEdge sheet))
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    coarseNewOldEdge input profile sheet hSurvives =
      ⟨profile.small.1, profile.small_survives⟩ := by
  apply Subtype.ext
  change coarseNewOldSourceEdge input profile sheet = profile.small.1
  rw [coarseNewOldSourceEdge, ite_eq_left hSelected]

theorem coarseNewOldEdge_of_background
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (coarseCandidate input profile).datum
      ((coarseCandidate input profile).newSourceEdge sheet))
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (coarseNewOldEdge input profile sheet hSurvives).1 =
      data.sourceEdge (smallTarget input profile) sheet := by
  change coarseNewOldSourceEdge input profile sheet =
    data.sourceEdge (smallTarget input profile) sheet
  rw [coarseNewOldSourceEdge, ite_eq_right hBackground]

/-- At a background fresh endpoint, every assigned reverse row has an actual
old surviving occurrence incident at the original wall vertex, and that old
occurrence replaces back to the given resolved occurrence. -/
theorem coarseRowOfEdge_incident_background
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (edge : NonDanglingEdge (coarseCandidate input profile).datum)
    (hIncident : Incident (coarseCandidate input profile).datum edge.1
      ((coarseCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet)) :
    ∃ old : NonDanglingEdge data,
      Incident data old.1 (data.sourceEndpoint wall sheet) ∧
        coarseBackgroundReplace input profile old.1 = edge.1 ∧
          coarseRowOfEdge input profile edge = old.stablePath := by
  classical
  let candidate := coarseCandidate input profile
  by_cases hOld : ∃ old : NonDanglingEdge data,
      retainedEdge candidate input.valid.1 old = edge
  · let old := Classical.choose hOld
    have hEq := Classical.choose_spec hOld
    have hCandidateIncident : Incident candidate.datum (candidate.oldSourceEdge old.1)
        (candidate.datum.sourceEndpoint (freshVertex target) sheet) := by
      rw [show candidate.oldSourceEdge old.1 = edge.1 from congrArg Subtype.val hEq]
      exact hIncident
    obtain ⟨hOldIncident, hTarget⟩ :=
      (coarse_background_old_incident_right_iff input profile sheet hBackground old.1).mp
        hCandidateIncident
    refine ⟨old, hOldIncident, ?_, ?_⟩
    · rw [coarseBackgroundReplace_of_ne_small input profile old.1 hTarget]
      exact congrArg Subtype.val hEq
    · rw [coarseRowOfEdge, dite_eq_left hOld]
  · let newSheet := coarseNewSheet input profile edge hOld
    let hNewSurvives := coarseNewSheet_survives input profile edge hOld
    have hEdge := coarseNewSheet_spec input profile edge hOld
    have hNewIncident : Incident candidate.datum (candidate.newSourceEdge newSheet)
        (candidate.datum.sourceEndpoint (freshVertex target) sheet) := by
      rw [← show edge.1 = candidate.newSourceEdge newSheet from congrArg Subtype.val hEdge]
      exact hIncident
    have hWall := coarse_background_new_incident_right_rel input profile
      sheet newSheet hBackground hNewIncident
    have hNewBackground : ¬(data.vertexPartition wall).Rel
        input.distinguishedBlock.1 newSheet := by
      intro hSelected
      exact hBackground (hSelected.trans hWall.symm)
    let old := coarseNewOldEdge input profile newSheet hNewSurvives
    have hOldValue : old.1 = data.sourceEdge (smallTarget input profile) newSheet :=
      coarseNewOldEdge_of_background input profile newSheet hNewSurvives hNewBackground
    have hOldIncident : Incident data old.1 (data.sourceEndpoint wall sheet) := by
      rw [hOldValue]
      have hBase := incident_sourceEdge_sourceEndpoint data wall
        (smallTarget input profile) (smallTarget_mem input profile) newSheet
      have hEndpoint : data.sourceEndpoint wall sheet = data.sourceEndpoint wall newSheet := by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact hWall
      rw [hEndpoint]
      exact hBase
    refine ⟨old, hOldIncident, ?_, ?_⟩
    · rw [coarseBackgroundReplace_of_small input profile old.1 (by
        rw [hOldValue]
        rfl)]
      rw [hOldValue]
      have hReplace : candidate.newSourceEdge
          (data.sourceEdge (smallTarget input profile) newSheet).1.2 =
          candidate.newSourceEdge newSheet := by
        apply coarse_background_new_eq_of_small_source_eq input profile
          newSheet (data.sourceEdge (smallTarget input profile) newSheet).1.2
        · exact hNewBackground
        · exact GluingDatum.sourceEdge_self data
            (data.sourceEdge (smallTarget input profile) newSheet)
      exact hReplace.trans (congrArg Subtype.val hEdge).symm
    · exact (coarseRowOfEdge_not_retained input profile edge hOld).trans
        (congrArg NonDanglingEdge.stablePath rfl)

theorem coarseRowOfEdge_eq_background
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (first second : NonDanglingEdge (coarseCandidate input profile).datum)
    (hNe : first ≠ second)
    (hFirst : Incident (coarseCandidate input profile).datum first.1
      ((coarseCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet))
    (hSecond : Incident (coarseCandidate input profile).datum second.1
      ((coarseCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet))
    (hValency : nonDanglingValency (coarseCandidate input profile).datum
      ((coarseCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet) = 2) :
    coarseRowOfEdge input profile first = coarseRowOfEdge input profile second := by
  obtain ⟨oldFirst, hOldFirst, hReplaceFirst, hFirstRow⟩ :=
    coarseRowOfEdge_incident_background input profile sheet hBackground first hFirst
  obtain ⟨oldSecond, hOldSecond, hReplaceSecond, hSecondRow⟩ :=
    coarseRowOfEdge_incident_background input profile sheet hBackground second hSecond
  have hOldValency : nonDanglingValency data (data.sourceEndpoint wall sheet) = 2 :=
    (coarse_nonDanglingValency_background input profile sheet hBackground).symm.trans hValency
  have hOldNe : oldFirst ≠ oldSecond := by
    intro hEqual
    apply hNe
    apply Subtype.ext
    rw [← hReplaceFirst, ← hReplaceSecond, hEqual]
  exact hFirstRow.trans ((stablePath_eq_of_consecutive
    ⟨hOldNe, data.sourceEndpoint wall sheet, hOldFirst, hOldSecond,
      hOldValency⟩).trans hSecondRow.symm)

theorem coarseRowOfEdge_new_selected
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hSurvives : ¬ IsDangling (coarseCandidate input profile).datum
      ((coarseCandidate input profile).newSourceEdge sheet)) :
    coarseRowOfEdge input profile
        ⟨(coarseCandidate input profile).newSourceEdge sheet, hSurvives⟩ =
      NonDanglingEdge.stablePath ⟨profile.small.1, profile.small_survives⟩ := by
  classical
  let candidate := coarseCandidate input profile
  let edge : NonDanglingEdge candidate.datum := ⟨candidate.newSourceEdge sheet, hSurvives⟩
  have hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge candidate input.valid.1 old = edge := by
    rintro ⟨old, hEqual⟩
    have hLabels := (occurrenceEquiv target wall candidate.right).injective
      (congrArg (fun occurrence : NonDanglingEdge candidate.datum ↦ occurrence.1.1.1)
        hEqual)
    cases hLabels
  let chosen := coarseNewSheet input profile edge hNotOld
  let hChosenSurvives := coarseNewSheet_survives input profile edge hNotOld
  have hSpec := coarseNewSheet_spec input profile edge hNotOld
  have hNewEqual : candidate.newSourceEdge sheet = candidate.newSourceEdge chosen :=
    congrArg Subtype.val hSpec
  have hNewRel : (coarsePastedResolution input profile).newEdge.Rel sheet chosen :=
    congrArg (fun item : candidate.datum.SourceEdge ↦ item.1.2) hNewEqual
  have hWallRel : (data.vertexPartition wall).Rel sheet chosen :=
    (coarsePastedResolution input profile).edge_refines_left.trans
      (LocalResolution.pasteLeft_refines (data.vertexPartition wall)
        candidate.resolution candidate.contracts) |>.rel hNewRel
  have hChosenSelected : (data.vertexPartition wall).Rel
      input.distinguishedBlock.1 chosen := hSelected.trans hWallRel
  calc
    coarseRowOfEdge input profile edge =
        (coarseNewOldEdge input profile chosen hChosenSurvives).stablePath :=
      coarseRowOfEdge_not_retained input profile edge hNotOld
    _ = NonDanglingEdge.stablePath ⟨profile.small.1, profile.small_survives⟩ :=
      congrArg NonDanglingEdge.stablePath
        (coarseNewOldEdge_of_selected input profile chosen hChosenSurvives hChosenSelected)

theorem coarseRowOfEdge_new_background
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hSurvives : ¬ IsDangling (coarseCandidate input profile).datum
      ((coarseCandidate input profile).newSourceEdge sheet)) :
    coarseRowOfEdge input profile
        ⟨(coarseCandidate input profile).newSourceEdge sheet, hSurvives⟩ =
      NonDanglingEdge.stablePath
        ⟨data.sourceEdge (smallTarget input profile) sheet,
          (coarse_background_new_survives_iff_oldSmall input profile sheet hBackground).mp
            hSurvives⟩ := by
  classical
  let candidate := coarseCandidate input profile
  let edge : NonDanglingEdge candidate.datum := ⟨candidate.newSourceEdge sheet, hSurvives⟩
  have hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge candidate input.valid.1 old = edge := by
    rintro ⟨old, hEqual⟩
    have hLabels := (occurrenceEquiv target wall candidate.right).injective
      (congrArg (fun occurrence : NonDanglingEdge candidate.datum ↦ occurrence.1.1.1)
        hEqual)
    cases hLabels
  let chosen := coarseNewSheet input profile edge hNotOld
  let hChosenSurvives := coarseNewSheet_survives input profile edge hNotOld
  have hSpec := coarseNewSheet_spec input profile edge hNotOld
  have hNewEqual : candidate.newSourceEdge sheet = candidate.newSourceEdge chosen :=
    congrArg Subtype.val hSpec
  have hNewRel : (coarsePastedResolution input profile).newEdge.Rel sheet chosen :=
    congrArg (fun item : candidate.datum.SourceEdge ↦ item.1.2) hNewEqual
  have hWallRel : (data.vertexPartition wall).Rel sheet chosen :=
    (coarsePastedResolution input profile).edge_refines_left.trans
      (LocalResolution.pasteLeft_refines (data.vertexPartition wall)
        candidate.resolution candidate.contracts) |>.rel hNewRel
  have hChosenBackground : ¬(data.vertexPartition wall).Rel
      input.distinguishedBlock.1 chosen := by
    intro hSelected
    exact hBackground (hSelected.trans hWallRel.symm)
  have hOldEqual : data.sourceEdge (smallTarget input profile) chosen =
      data.sourceEdge (smallTarget input profile) sheet := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hFineRel : (finePartition input profile).Rel sheet chosen := by
          apply (finePartition input profile).mem_block_iff _ _ |>.mp
          rw [← coarse_background_newEdge_block input profile sheet hBackground,
            (coarsePastedResolution input profile).newEdge.mem_block_iff]
          exact hNewRel
      calc
        (data.sourceEdge (smallTarget input profile) chosen).1.2 =
            (finePartition input profile).repr chosen := rfl
        _ = (finePartition input profile).repr sheet := hFineRel.symm
        _ = (data.sourceEdge (smallTarget input profile) sheet).1.2 := rfl
  have hChosenOld := coarseNewOldEdge_of_background input profile chosen
    hChosenSurvives hChosenBackground
  calc
    coarseRowOfEdge input profile edge =
        (coarseNewOldEdge input profile chosen hChosenSurvives).stablePath :=
      coarseRowOfEdge_not_retained input profile edge hNotOld
    _ = NonDanglingEdge.stablePath
        ⟨data.sourceEdge (smallTarget input profile) sheet,
          (coarse_background_new_survives_iff_oldSmall input profile sheet hBackground).mp
            hSurvives⟩ := by
      apply congrArg NonDanglingEdge.stablePath
      apply Subtype.ext
      exact hChosenOld.trans hOldEqual

/-- Every row assigned at the selected fresh endpoint is the old selected
small/large row. -/
theorem coarseRowOfEdge_incident_fresh_selected
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (edge : NonDanglingEdge (coarseCandidate input profile).datum)
    (hIncident : Incident (coarseCandidate input profile).datum edge.1
      ((coarseCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet)) :
    coarseRowOfEdge input profile edge =
      NonDanglingEdge.stablePath ⟨profile.small.1, profile.small_survives⟩ := by
  classical
  let candidate := coarseCandidate input profile
  have hEndpoint : candidate.datum.sourceEndpoint (freshVertex target) sheet =
      candidate.datum.sourceEndpoint (freshVertex target) (anchor input profile) := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (coarsePastedResolution input profile).right.repr sheet =
          (coarsePastedResolution input profile).right.repr (anchor input profile)
      apply (coarsePastedResolution input profile).right.mem_block_iff _ _ |>.mp
      rw [coarse_pasted_right_block_selected input profile sheet hSelected]
      exact (data.vertexPartition wall).mem_block_iff _ _ |>.mpr
        (hSelected.symm.trans (anchor_wall_rel input profile))
  have hAtAnchor : edge.1 ∈ nonDanglingIncident candidate.datum
      (candidate.datum.sourceEndpoint (freshVertex target) (anchor input profile)) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hEndpoint.symm ▸ hIncident⟩
  rw [coarse_nonDanglingIncident_right input profile] at hAtAnchor
  rcases Finset.mem_insert.mp hAtAnchor with hNew | hLarge
  · have hEdge : edge = coarseAnchorNew input profile := Subtype.ext hNew
    rw [hEdge]
    exact coarseRowOfEdge_new_selected input profile (anchor input profile)
      (anchor_wall_rel input profile) (coarse_anchor_new_survives input profile)
  · have hOld := Finset.mem_singleton.mp hLarge
    let retainedLarge : NonDanglingEdge candidate.datum :=
      retainedEdge candidate input.valid.1 ⟨profile.large.1, profile.large_survives⟩
    have hEdge : edge = retainedLarge := Subtype.ext hOld
    rw [hEdge]
    have hRow : coarseRowOfEdge input profile retainedLarge =
        NonDanglingEdge.stablePath
          (⟨profile.large.1, profile.large_survives⟩ : NonDanglingEdge data) := by
      simpa only [candidate, retainedLarge] using
        (coarseRowOfEdge_retained input profile
          (⟨profile.large.1, profile.large_survives⟩ : NonDanglingEdge data))
    exact hRow.trans profile.stablePath_eq.symm

theorem coarseRowOfEdge_incident_left_selected
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (edge : NonDanglingEdge (coarseCandidate input profile).datum)
    (hIncident : Incident (coarseCandidate input profile).datum edge.1
      ((coarseCandidate input profile).datum.sourceEndpoint (oldVertex target wall) sheet)) :
    coarseRowOfEdge input profile edge =
      NonDanglingEdge.stablePath ⟨profile.small.1, profile.small_survives⟩ := by
  classical
  let candidate := coarseCandidate input profile
  rcases nonDanglingEdge_cases candidate input.valid
      (coarseCandidate_sourceGenus input profile) edge with ⟨old, rfl⟩ | ⟨other, hSurvives, rfl⟩
  · rw [coarseRowOfEdge_retained]
    have hData := (incident_iff_target_mem_and_rel candidate.datum
      (candidate.oldSourceEdge old.1)
      (candidate.datum.sourceEndpoint (oldVertex target wall) sheet)).mp hIncident
    simp only [GluingDatum.sourceEndpoint, candidate.oldSourceEdge_target,
      candidate.oldSourceEdge_sheet] at hData
    have hVertex : candidate.datum.vertexPartition (oldVertex target wall) =
        (coarsePastedResolution input profile).left :=
      GlobalResolution.expandedVertexPartition_old_wall data wall _
    rw [hVertex] at hData
    have hTarget := hData.1
    rw [coarse_left_target_incident_pair input profile] at hTarget
    rcases Finset.mem_insert.mp hTarget with hNew | hSmall
    · have hLabels := (occurrenceEquiv target wall candidate.right).injective hNew
      cases hLabels
    · have hOldTarget : old.1.1.1 = smallTarget input profile :=
        Option.some.inj ((occurrenceEquiv target wall candidate.right).injective
          (Finset.mem_singleton.mp hSmall))
      have hLeftRel : (coarsePastedResolution input profile).left.Rel sheet old.1.1.2 := by
        have hRel := hData.2
        change (coarsePastedResolution input profile).left.Rel
          ((coarsePastedResolution input profile).left.repr sheet) old.1.1.2 at hRel
        exact (coarsePastedResolution input profile).left.rel_repr_right sheet |>.trans hRel
      have hWallRel : (data.vertexPartition wall).Rel sheet old.1.1.2 :=
        (LocalResolution.pasteLeft_refines (data.vertexPartition wall)
          candidate.resolution candidate.contracts).rel hLeftRel
      have hOldIncident : Incident data old.1
          (WallBlock.sourceVertex data wall input.distinguishedBlock) := by
        apply (incident_wallBlock_sourceVertex_iff data input.distinguishedBlock old.1).mpr
        refine ⟨hOldTarget ▸ smallTarget_mem input profile, ?_⟩
        apply Subtype.ext
        exact (hSelected.trans hWallRel).symm.trans input.distinguishedBlock.2
      rcases selected_survivor_eq_small_or_large input profile old hOldIncident with
        hOldSmall | hOldLarge
      · exact congrArg NonDanglingEdge.stablePath (Subtype.ext hOldSmall)
      · have hLargeTarget := congrArg (fun source : data.SourceEdge ↦ source.1.1)
          hOldLarge
        exact (profile.target_ne (hOldTarget.symm.trans hLargeTarget)).elim
  · have hData := (incident_iff_target_mem_and_rel candidate.datum
      (candidate.newSourceEdge other)
      (candidate.datum.sourceEndpoint (oldVertex target wall) sheet)).mp hIncident
    simp only [GluingDatum.sourceEndpoint, candidate.newSourceEdge_target,
      candidate.newSourceEdge_sheet] at hData
    have hVertex : candidate.datum.vertexPartition (oldVertex target wall) =
        (coarsePastedResolution input profile).left :=
      GlobalResolution.expandedVertexPartition_old_wall data wall _
    rw [hVertex] at hData
    have hRel := hData.2
    have hLeftRel : (coarsePastedResolution input profile).left.Rel sheet
        ((coarsePastedResolution input profile).newEdge.repr other) := by
      change (coarsePastedResolution input profile).left.Rel
        ((coarsePastedResolution input profile).left.repr sheet)
        ((coarsePastedResolution input profile).newEdge.repr other) at hRel
      exact (coarsePastedResolution input profile).left.rel_repr_right sheet |>.trans hRel
    have hLeftOther : (coarsePastedResolution input profile).left.Rel sheet other :=
      hLeftRel.trans ((coarsePastedResolution input profile).edge_refines_left.rel
        ((coarsePastedResolution input profile).newEdge.rel_repr_left other))
    have hWallOther : (data.vertexPartition wall).Rel sheet other :=
      (LocalResolution.pasteLeft_refines (data.vertexPartition wall)
        candidate.resolution candidate.contracts).rel hLeftOther
    exact coarseRowOfEdge_new_selected input profile other
      (hSelected.trans hWallOther) hSurvives

theorem coarseRowOfEdge_incident_left_background
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (edge : NonDanglingEdge (coarseCandidate input profile).datum)
    (hIncident : Incident (coarseCandidate input profile).datum edge.1
      ((coarseCandidate input profile).datum.sourceEndpoint (oldVertex target wall) sheet)) :
    ∃ hOld : ¬ IsDangling data (data.sourceEdge (smallTarget input profile) sheet),
      coarseRowOfEdge input profile edge = NonDanglingEdge.stablePath
        ⟨data.sourceEdge (smallTarget input profile) sheet, hOld⟩ := by
  classical
  let candidate := coarseCandidate input profile
  rcases nonDanglingEdge_cases candidate input.valid
      (coarseCandidate_sourceGenus input profile) edge with ⟨old, rfl⟩ | ⟨other, hSurvives, rfl⟩
  · have hData := (incident_iff_target_mem_and_rel candidate.datum
      (candidate.oldSourceEdge old.1)
      (candidate.datum.sourceEndpoint (oldVertex target wall) sheet)).mp hIncident
    simp only [GluingDatum.sourceEndpoint, candidate.oldSourceEdge_target,
      candidate.oldSourceEdge_sheet] at hData
    have hVertex : candidate.datum.vertexPartition (oldVertex target wall) =
        (coarsePastedResolution input profile).left :=
      GlobalResolution.expandedVertexPartition_old_wall data wall _
    rw [hVertex] at hData
    have hTarget := hData.1
    rw [coarse_left_target_incident_pair input profile] at hTarget
    rcases Finset.mem_insert.mp hTarget with hNew | hSmall
    · have hLabels := (occurrenceEquiv target wall candidate.right).injective hNew
      cases hLabels
    · have hOldTarget : old.1.1.1 = smallTarget input profile :=
        Option.some.inj ((occurrenceEquiv target wall candidate.right).injective
          (Finset.mem_singleton.mp hSmall))
      have hRel := hData.2
      have hLeftRel : (coarsePastedResolution input profile).left.Rel
          sheet old.1.1.2 := by
        change (coarsePastedResolution input profile).left.Rel
          ((coarsePastedResolution input profile).left.repr sheet) old.1.1.2 at hRel
        exact (coarsePastedResolution input profile).left.rel_repr_right sheet |>.trans hRel
      have hFineRel : (finePartition input profile).Rel sheet old.1.1.2 := by
        apply (finePartition input profile).mem_block_iff _ _ |>.mp
        rw [← coarse_background_left_block input profile sheet hBackground,
          (coarsePastedResolution input profile).left.mem_block_iff]
        exact hLeftRel
      have hOldEq : old.1 = data.sourceEdge (smallTarget input profile) sheet := by
        apply Subtype.ext
        apply Prod.ext
        · exact hOldTarget
        · calc
            old.1.1.2 = (finePartition input profile).repr old.1.1.2 := by
              have hCanonical := old.1.2
              change (data.edgePartition old.1.1.1).repr old.1.1.2 = old.1.1.2 at hCanonical
              rw [hOldTarget] at hCanonical
              exact hCanonical.symm
            _ = (finePartition input profile).repr sheet := hFineRel.symm
            _ = (data.sourceEdge (smallTarget input profile) sheet).1.2 := rfl
      refine ⟨hOldEq ▸ old.2, ?_⟩
      rw [coarseRowOfEdge_retained]
      exact congrArg NonDanglingEdge.stablePath (Subtype.ext hOldEq)
  · have hData := (incident_iff_target_mem_and_rel candidate.datum
      (candidate.newSourceEdge other)
      (candidate.datum.sourceEndpoint (oldVertex target wall) sheet)).mp hIncident
    simp only [GluingDatum.sourceEndpoint, candidate.newSourceEdge_target,
      candidate.newSourceEdge_sheet] at hData
    have hVertex : candidate.datum.vertexPartition (oldVertex target wall) =
        (coarsePastedResolution input profile).left :=
      GlobalResolution.expandedVertexPartition_old_wall data wall _
    rw [hVertex] at hData
    have hRel := hData.2
    have hLeftRel : (coarsePastedResolution input profile).left.Rel sheet
        ((coarsePastedResolution input profile).newEdge.repr other) := by
      change (coarsePastedResolution input profile).left.Rel
        ((coarsePastedResolution input profile).left.repr sheet)
        ((coarsePastedResolution input profile).newEdge.repr other) at hRel
      exact (coarsePastedResolution input profile).left.rel_repr_right sheet |>.trans hRel
    have hLeftRelOther : (coarsePastedResolution input profile).left.Rel sheet other :=
      hLeftRel.trans ((coarsePastedResolution input profile).edge_refines_left.rel
        ((coarsePastedResolution input profile).newEdge.rel_repr_left other))
    have hWallOther : (data.vertexPartition wall).Rel sheet other :=
      (LocalResolution.pasteLeft_refines (data.vertexPartition wall)
        candidate.resolution candidate.contracts).rel hLeftRelOther
    have hOtherBackground : ¬(data.vertexPartition wall).Rel
        input.distinguishedBlock.1 other := by
      intro hSelected
      exact hBackground (hSelected.trans hWallOther.symm)
    have hNewRel : (coarsePastedResolution input profile).newEdge.Rel sheet other := by
      apply (coarsePastedResolution input profile).newEdge.mem_block_iff _ _ |>.mp
      rw [coarse_background_newEdge_block input profile sheet hBackground]
      apply (finePartition input profile).mem_block_iff _ _ |>.mpr
      apply (finePartition input profile).mem_block_iff _ _ |>.mp
      rw [← coarse_background_left_block input profile sheet hBackground,
        (coarsePastedResolution input profile).left.mem_block_iff]
      exact hLeftRelOther
    have hFineRel : (finePartition input profile).Rel sheet other := by
      apply (finePartition input profile).mem_block_iff _ _ |>.mp
      rw [← coarse_background_newEdge_block input profile sheet hBackground,
        (coarsePastedResolution input profile).newEdge.mem_block_iff]
      exact hNewRel
    have hOldEq : data.sourceEdge (smallTarget input profile) other =
        data.sourceEdge (smallTarget input profile) sheet := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact hFineRel.symm
    have hOldOther := (coarse_background_new_survives_iff_oldSmall input profile
      other hOtherBackground).mp hSurvives
    have hOldSheet : ¬ IsDangling data (data.sourceEdge
        (smallTarget input profile) sheet) := hOldEq.symm ▸ hOldOther
    refine ⟨hOldSheet, ?_⟩
    exact (coarseRowOfEdge_new_background input profile other hOtherBackground
      hSurvives).trans (congrArg NonDanglingEdge.stablePath (Subtype.ext hOldEq))

/-- Away from the expanded wall, both consecutive survivors are retained and
their assigned rows are the corresponding old consecutive rows. -/
theorem coarseRowOfEdge_eq_away
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (vertex : data.SourceVertex) (hAway : vertex.1.1 ≠ wall)
    (first second : NonDanglingEdge (coarseCandidate input profile).datum)
    (hFirst : Incident (coarseCandidate input profile).datum first.1
      (retainedVertex (coarseCandidate input profile) vertex))
    (hSecond : Incident (coarseCandidate input profile).datum second.1
      (retainedVertex (coarseCandidate input profile) vertex))
    (hValency : nonDanglingValency (coarseCandidate input profile).datum
      (retainedVertex (coarseCandidate input profile) vertex) = 2) :
    coarseRowOfEdge input profile first = coarseRowOfEdge input profile second := by
  classical
  let candidate := coarseCandidate input profile
  have hGenus := coarseCandidate_sourceGenus input profile
  rcases nonDanglingEdge_cases candidate input.valid hGenus first with
      ⟨oldFirst, rfl⟩ | ⟨sheet, hSurvives, rfl⟩
  · rcases nonDanglingEdge_cases candidate input.valid hGenus second with
        ⟨oldSecond, rfl⟩ | ⟨sheet, hSurvives, rfl⟩
    · rw [coarseRowOfEdge_retained, coarseRowOfEdge_retained]
      by_cases hEqual : oldFirst = oldSecond
      · exact congrArg NonDanglingEdge.stablePath hEqual
      · exact stablePath_eq_of_consecutive ⟨hEqual, vertex,
          (incident_oldSourceEdge_iff candidate vertex hAway oldFirst.1).mp hFirst,
          (incident_oldSourceEdge_iff candidate vertex hAway oldSecond.1).mp hSecond,
          (nonDanglingValency_retainedVertex candidate input.valid hGenus vertex hAway).symm.trans
            hValency⟩
    · exact (not_incident_newSourceEdge candidate vertex hAway sheet hSecond).elim
  · exact (not_incident_newSourceEdge candidate vertex hAway sheet hFirst).elim

/-- The coarse reverse assignment is constant on every actual consecutive
pair, with selected and background wall blocks treated by their literal local
censuses. -/
theorem coarseRowOfEdge_eq_of_consecutive
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (first second : NonDanglingEdge (coarseCandidate input profile).datum)
    (hConsecutive : Consecutive (coarseCandidate input profile).datum first second) :
    coarseRowOfEdge input profile first = coarseRowOfEdge input profile second := by
  classical
  let candidate := coarseCandidate input profile
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
        · exact (coarseRowOfEdge_incident_left_selected input profile _ hSelected first
            hFirst).trans (coarseRowOfEdge_incident_left_selected input profile _ hSelected
              second hSecond).symm
        · obtain ⟨hOldFirst, hFirstRow⟩ :=
            coarseRowOfEdge_incident_left_background input profile _ hSelected first hFirst
          obtain ⟨hOldSecond, hSecondRow⟩ :=
            coarseRowOfEdge_incident_left_background input profile _ hSelected second hSecond
          exact hFirstRow.trans hSecondRow.symm
      · obtain ⟨old, hOld, hVertex⟩ :=
          exists_retainedVertex_of_target candidate vertex place hAt hTarget
        rw [← hVertex] at hFirst hSecond hValency
        exact coarseRowOfEdge_eq_away input profile old (hOld ▸ hAt) first second
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
      · exact (coarseRowOfEdge_incident_fresh_selected input profile _ hSelected first
          hFirst).trans (coarseRowOfEdge_incident_fresh_selected input profile _ hSelected
            second hSecond).symm
      · exact coarseRowOfEdge_eq_background input profile _ hSelected first second hNe
          hFirst hSecond hValency

/-- The explicit reverse row assignment descends through the stable-path
quotient. -/
noncomputable def coarseStablePathDescend
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    StablePath (coarseCandidate input profile).datum → StablePath data :=
  Quot.lift (coarseRowOfEdge input profile)
    (coarseRowOfEdge_eq_of_consecutive input profile)

@[simp] theorem coarseStablePathDescend_mk
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (edge : NonDanglingEdge (coarseCandidate input profile).datum) :
    coarseStablePathDescend input profile edge.stablePath =
      coarseRowOfEdge input profile edge := rfl

/-- Descent is a literal left inverse on every old retained row. -/
theorem coarseStablePathDescend_lift
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (path : StablePath data) :
    coarseStablePathDescend input profile (coarseStablePathLift input profile path) = path := by
  induction path using Quot.inductionOn with
  | h edge => exact coarseRowOfEdge_retained input profile edge

theorem coarseStablePathLift_injective
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    Function.Injective (coarseStablePathLift input profile) :=
  Function.LeftInverse.injective (coarseStablePathDescend_lift input profile)

/-- The true Figure 31 coarse member's stable rows are equivalent via the
actual retained-occurrence map. -/
noncomputable def coarseStablePathEquiv
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    StablePath data ≃ StablePath (coarseCandidate input profile).datum :=
  Equiv.ofBijective (coarseStablePathLift input profile)
    ⟨coarseStablePathLift_injective input profile,
      coarseStablePathLift_surjective input profile⟩

@[simp] theorem coarseStablePathEquiv_mk
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (edge : NonDanglingEdge data) :
    coarseStablePathEquiv input profile edge.stablePath =
      (retainedEdge (coarseCandidate input profile) input.valid.1 edge).stablePath := rfl

end DraismaVargas.LocalCases.W3Nd2RowDescent
