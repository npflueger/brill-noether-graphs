import DraismaVargas.LocalCases.W3Nd2FineRowDescent
import DraismaVargas.LocalCases.StableSourceMatrix

/-!
# Honest common-wall matrix formulas for the Figure 31 fine member

Retained target occurrences reproduce the original natural source matrix
under the geometric fine stable-row equivalence.  On the new occurrence the
only selected survivor is the anchor occurrence; the residual selected
singleton is excluded by its proved danglingness.  All remaining terms are
transported from actual old large-direction background occurrences with their
literal indices.
-/

namespace DraismaVargas.LocalCases.W3Nd2FineLimitMatrix

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource ThirdEquation StableSourceMatrix
open W3R1SourceProfile W3Nd2SourceCandidates W3Nd2FineRefinement
open W3Nd2FineCandidates W3Nd2Survival W3Nd2Background
open W3Nd2StableLift W3Nd2FineRowDescent
open ResolutionM11 ResolutionPruning ResolutionSurvival ResolutionAwayFromWall
open M11SplitRows

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  (input : W3SourceInput data star)
  (profile : Nd2Profile data input.distinguishedBlock)

/-- Exact retained-column occurrence dictionary under the actual fine row
equivalence and canonical occurrence labelling. -/
theorem occurrences_retained (path : StablePath data) (place : target.edges) :
    occurrences (fineCandidate input profile).datum
        (fineStablePathEquiv input profile path)
        (occurrenceEquiv target wall (fineCandidate input profile).right (some place)) =
      (occurrences data path place).image
        (fineCandidate input profile).oldSourceEdge := by
  classical
  let candidate := fineCandidate input profile
  ext edge
  constructor
  · intro hMem
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hMem
    rcases sourceEdge_cases candidate edge with ⟨old, rfl⟩ | ⟨sheet, rfl⟩
    · have hOld : ¬ IsDangling data old := fun h ↦ hSurvives
        ((isDangling_oldSourceEdge_iff candidate input.valid
          (fineCandidate_sourceGenus input profile) old).mpr h)
      refine Finset.mem_image.mpr
        ⟨old, (mem_occurrences _ _ _).mpr ⟨⟨hOld, ?_⟩, ?_⟩, rfl⟩
      · apply (fineStablePathEquiv input profile).injective
        exact (fineStablePathEquiv_mk input profile ⟨old, hOld⟩).trans hRow
      · exact Option.some.inj
          ((occurrenceEquiv target wall candidate.right).injective hTarget)
    · have hLabels := (occurrenceEquiv target wall candidate.right).injective hTarget
      cases hLabels
  · intro hMem
    obtain ⟨old, hOld, rfl⟩ := Finset.mem_image.mp hMem
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hOld
    refine (mem_occurrences _ _ _).mpr
      ⟨⟨not_isDangling_oldSourceEdge candidate input.valid.1 old hSurvives, ?_⟩, ?_⟩
    · exact (fineStablePathEquiv_mk input profile ⟨old, hSurvives⟩).symm.trans
        (congrArg (fineStablePathEquiv input profile) hRow)
    · exact congrArg
        (fun label ↦ occurrenceEquiv target wall candidate.right (some label)) hTarget

/-- Every retained natural-matrix entry is literally its original wall
entry. -/
theorem matrix_retained (path : StablePath data) (place : target.edges) :
    matrix (fineCandidate input profile).datum
        (fineStablePathEquiv input profile path)
        (occurrenceEquiv target wall (fineCandidate input profile).right (some place)) =
      matrix data path place := by
  classical
  unfold matrix
  rw [occurrences_retained, Finset.sum_image]
  · exact Finset.sum_congr rfl fun edge _ ↦ by
      rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge]
  · intro first _ second _ hEqual
    exact ResolutionCut.oldSourceEdge_injective _ hEqual

/-- The row-filtered fine new fibre with its sole surviving selected-block
occurrence removed. -/
noncomputable def backgroundOccurrences
    (path : StablePath (fineCandidate input profile).datum) :
    Finset (fineCandidate input profile).datum.SourceEdge := by
  classical
  exact (occurrences (fineCandidate input profile).datum path
    (occurrenceEquiv target wall (fineCandidate input profile).right none)).erase
      ((fineCandidate input profile).newSourceEdge (anchor input profile))

theorem mem_backgroundOccurrences
    (path : StablePath (fineCandidate input profile).datum)
    (edge : (fineCandidate input profile).datum.SourceEdge) :
    edge ∈ backgroundOccurrences input profile path ↔
      edge ∈ occurrences (fineCandidate input profile).datum path
          (occurrenceEquiv target wall (fineCandidate input profile).right none) ∧
        ¬ (data.vertexPartition wall).Rel input.distinguishedBlock.1 edge.1.2 := by
  classical
  let candidate := fineCandidate input profile
  rw [backgroundOccurrences, Finset.mem_erase]
  constructor
  · rintro ⟨hNe, hMem⟩
    refine ⟨hMem, ?_⟩
    intro hSelected
    have hNew := eq_newSourceEdge_of_target candidate edge
      ((mem_occurrences _ _ _).mp hMem).2
    have hNewSurvives : ¬ IsDangling candidate.datum
        (candidate.newSourceEdge edge.1.2) := by
      rw [← hNew]
      exact ((mem_occurrences _ _ _).mp hMem).1.1
    exact hNe (hNew.trans
      (fine_selected_new_eq_anchor_of_survives input profile edge.1.2
        hSelected hNewSurvives))
  · rintro ⟨hMem, hBackground⟩
    refine ⟨?_, hMem⟩
    intro hEqual
    apply hBackground
    rw [hEqual]
    let candidate := fineCandidate input profile
    let pasted := finePastedResolution input profile
    have hRefines : pasted.newEdge.Refines (data.vertexPartition wall) :=
      pasted.edge_refines_left.trans
        (SheetPartition.IsJoin.left_refines (LocalResolution.paste_contracts
          (data.vertexPartition wall) candidate.resolution candidate.contracts))
    change (data.vertexPartition wall).Rel input.distinguishedBlock.1
      (pasted.newEdge.repr (anchor input profile))
    exact (anchor_wall_rel input profile).trans
      (hRefines.rel (pasted.newEdge.rel_repr_right (anchor input profile)))

/-- The selected anchor occurrence is present exactly on its proved surviving
stable row; the residual selected singleton contributes nothing. -/
theorem selected_mem_occurrences_iff
    (path : StablePath (fineCandidate input profile).datum) :
    (fineCandidate input profile).newSourceEdge (anchor input profile) ∈
        occurrences (fineCandidate input profile).datum path
          (occurrenceEquiv target wall (fineCandidate input profile).right none) ↔
      path = (fineAnchorNew input profile).stablePath := by
  rw [mem_occurrences]
  constructor
  · rintro ⟨⟨_, hRow⟩, _⟩
    exact hRow.symm
  · intro hRow
    exact ⟨⟨fine_anchor_new_survives input profile, hRow.symm⟩, rfl⟩

noncomputable def backgroundColumn
    (path : StablePath (fineCandidate input profile).datum) : ℚ :=
  ∑ edge ∈ backgroundOccurrences input profile path,
    (1 : ℚ) / (fineCandidate input profile).datum.sourceEdgeIndex edge

/-- The unique selected new survivor has the actual small-source index,
derived from the literal selected fine partition. -/
theorem selected_newSourceEdge_index :
    (fineCandidate input profile).datum.sourceEdgeIndex
        ((fineCandidate input profile).newSourceEdge (anchor input profile)) =
      data.sourceEdgeIndex profile.small.1 := by
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge]
  change (finePastedResolution input profile).newEdge.blockCard
      (anchor input profile) =
    (data.edgePartition profile.small.1.1.1).blockCard profile.small.1.1.2
  unfold SheetPartition.blockCard
  rw [pasted_newEdge_block_selected input profile (anchor input profile)
    (anchor_wall_rel input profile)]

/-- Exact fine new-column decomposition into the one surviving selected
anchor contribution and every actual background contribution. -/
theorem matrix_new
    (path : StablePath (fineCandidate input profile).datum) :
    matrix (fineCandidate input profile).datum path
        (occurrenceEquiv target wall (fineCandidate input profile).right none) =
      (if path = (fineAnchorNew input profile).stablePath then
          (1 : ℚ) /
            (fineCandidate input profile).datum.sourceEdgeIndex
              ((fineCandidate input profile).newSourceEdge (anchor input profile))
        else 0) + backgroundColumn input profile path := by
  classical
  let candidate := fineCandidate input profile
  let selected := candidate.newSourceEdge (anchor input profile)
  let fibre := occurrences candidate.datum path
    (occurrenceEquiv target wall candidate.right none)
  by_cases hRow : path = (fineAnchorNew input profile).stablePath
  · have hMem : selected ∈ fibre :=
      (selected_mem_occurrences_iff input profile path).mpr hRow
    have hSum := Finset.sum_erase_add fibre
      (fun edge ↦ (1 : ℚ) / candidate.datum.sourceEdgeIndex edge) hMem
    change backgroundColumn input profile path +
      (1 : ℚ) / candidate.datum.sourceEdgeIndex selected =
        matrix candidate.datum path
          (occurrenceEquiv target wall candidate.right none) at hSum
    rw [if_pos hRow]
    exact hSum.symm.trans (add_comm _ _)
  · have hNot : selected ∉ fibre :=
      fun h ↦ hRow ((selected_mem_occurrences_iff input profile path).mp h)
    have hErase := Finset.erase_eq_of_notMem hNot
    rw [if_neg hRow, zero_add]
    change (∑ edge ∈ fibre, (1 : ℚ) / candidate.datum.sourceEdgeIndex edge) =
      ∑ edge ∈ fibre.erase selected,
        (1 : ℚ) / candidate.datum.sourceEdgeIndex edge
    rw [hErase]

noncomputable def oldBackgroundOccurrences (path : StablePath data) :
    Finset data.SourceEdge := by
  classical
  exact (occurrences data path (largeTarget input profile)).filter
    (fun edge ↦ ¬ (data.vertexPartition wall).Rel
      input.distinguishedBlock.1 edge.1.2)

theorem mem_oldBackgroundOccurrences (path : StablePath data)
    (edge : data.SourceEdge) :
    edge ∈ oldBackgroundOccurrences input profile path ↔
      edge ∈ occurrences data path (largeTarget input profile) ∧
        ¬ (data.vertexPartition wall).Rel input.distinguishedBlock.1 edge.1.2 := by
  classical
  exact Finset.mem_filter

/-- The actual old-large to fine-new map preserves survival and its geometric
stable row on every background block. -/
theorem new_mem_of_old_mem (path : StablePath data) (edge : data.SourceEdge)
    (hMem : edge ∈ oldBackgroundOccurrences input profile path) :
    (fineCandidate input profile).newSourceEdge edge.1.2 ∈
      backgroundOccurrences input profile (fineStablePathEquiv input profile path) := by
  let candidate := fineCandidate input profile
  have hOld := (mem_oldBackgroundOccurrences input profile path edge).mp hMem
  obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hOld.1
  have hCanonical : data.sourceEdge (largeTarget input profile) edge.1.2 = edge := by
    rw [← hTarget]
    exact GluingDatum.sourceEdge_self data edge
  have hCanonicalSurvives :
      ¬ IsDangling data (data.sourceEdge (largeTarget input profile) edge.1.2) := by
    rw [hCanonical]
    exact hSurvives
  have hNew := (fine_background_new_survives_iff_oldLarge input profile
    edge.1.2 hOld.2).mpr hCanonicalSurvives
  refine (mem_backgroundOccurrences input profile _ _).mpr
    ⟨(mem_occurrences _ _ _).mpr ⟨⟨hNew, ?_⟩, rfl⟩, ?_⟩
  · exact (fine_background_new_stablePath_eq_oldLarge input profile
      edge.1.2 hOld.2 hCanonicalSurvives).trans
      ((fineStablePathEquiv_mk input profile
        ⟨data.sourceEdge (largeTarget input profile) edge.1.2,
          hCanonicalSurvives⟩).symm.trans
        (congrArg (fineStablePathEquiv input profile)
          ((congrArg NonDanglingEdge.stablePath
            (show (⟨data.sourceEdge (largeTarget input profile) edge.1.2,
              hCanonicalSurvives⟩ : NonDanglingEdge data) = ⟨edge, hSurvives⟩ from
                Subtype.ext hCanonical)).trans hRow)))
  · let pasted := finePastedResolution input profile
    have hRefines : pasted.newEdge.Refines (data.vertexPartition wall) :=
      pasted.edge_refines_left.trans
        (SheetPartition.IsJoin.left_refines (LocalResolution.paste_contracts
          (data.vertexPartition wall) candidate.resolution candidate.contracts))
    intro hSelected
    apply hOld.2
    exact hSelected.trans
      (hRefines.rel (pasted.newEdge.rel_repr_left edge.1.2))

theorem old_mem_of_new_mem (path : StablePath data)
    (edge : (fineCandidate input profile).datum.SourceEdge)
    (hMem : edge ∈ backgroundOccurrences input profile
      (fineStablePathEquiv input profile path)) :
    data.sourceEdge (largeTarget input profile) edge.1.2 ∈
      oldBackgroundOccurrences input profile path := by
  let candidate := fineCandidate input profile
  have hData := (mem_backgroundOccurrences input profile _ _).mp hMem
  obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hData.1
  have hEdge := eq_newSourceEdge_of_target candidate edge hTarget
  have hNew : ¬ IsDangling candidate.datum (candidate.newSourceEdge edge.1.2) := by
    rw [← hEdge]
    exact hSurvives
  have hOld : ¬ IsDangling data
      (data.sourceEdge (largeTarget input profile) edge.1.2) :=
    (fine_background_new_survives_iff_oldLarge input profile edge.1.2 hData.2).mp hNew
  have hNewRow : NonDanglingEdge.stablePath
      ⟨candidate.newSourceEdge edge.1.2, hNew⟩ =
        fineStablePathEquiv input profile path :=
    (congrArg NonDanglingEdge.stablePath
      (show (⟨candidate.newSourceEdge edge.1.2, hNew⟩ : NonDanglingEdge candidate.datum) =
        ⟨edge, hSurvives⟩ from Subtype.ext hEdge.symm)).trans hRow
  refine (mem_oldBackgroundOccurrences input profile path _).mpr
    ⟨(mem_occurrences _ _ _).mpr ⟨⟨hOld, ?_⟩, rfl⟩, ?_⟩
  · apply (fineStablePathEquiv input profile).injective
    exact (fineStablePathEquiv_mk input profile
      ⟨data.sourceEdge (largeTarget input profile) edge.1.2, hOld⟩).trans
      ((fine_background_new_stablePath_eq_oldLarge input profile
        edge.1.2 hData.2 hOld).symm.trans hNewRow)
  · intro hSelected
    apply hData.2
    exact hSelected.trans
      ((StableLocalProperties.refines_of_mem_incidentEdges data
        (largeTarget_mem input profile)).rel
          ((data.edgePartition (largeTarget input profile)).rel_repr_left edge.1.2))

theorem new_old_roundtrip (path : StablePath data)
    (edge : (fineCandidate input profile).datum.SourceEdge)
    (hMem : edge ∈ backgroundOccurrences input profile
      (fineStablePathEquiv input profile path)) :
    (fineCandidate input profile).newSourceEdge
        (data.sourceEdge (largeTarget input profile) edge.1.2).1.2 = edge := by
  let candidate := fineCandidate input profile
  have hData := (mem_backgroundOccurrences input profile _ _).mp hMem
  have hTarget := ((mem_occurrences _ _ _).mp hData.1).2
  have hEdge := eq_newSourceEdge_of_target candidate edge hTarget
  exact (fine_background_new_eq_of_large_source_eq input profile edge.1.2
    (data.sourceEdge (largeTarget input profile) edge.1.2).1.2 hData.2
      (GluingDatum.sourceEdge_self data
        (data.sourceEdge (largeTarget input profile) edge.1.2))).trans hEdge.symm

theorem new_of_old_injective (path : StablePath data)
    (first second : data.SourceEdge)
    (hFirst : first ∈ oldBackgroundOccurrences input profile path)
    (hSecond : second ∈ oldBackgroundOccurrences input profile path)
    (hEqual : (fineCandidate input profile).newSourceEdge first.1.2 =
      (fineCandidate input profile).newSourceEdge second.1.2) : first = second := by
  have hFirstData := (mem_oldBackgroundOccurrences input profile path first).mp hFirst
  have hSecondData := (mem_oldBackgroundOccurrences input profile path second).mp hSecond
  have hFirstTarget := ((mem_occurrences _ _ _).mp hFirstData.1).2
  have hSecondTarget := ((mem_occurrences _ _ _).mp hSecondData.1).2
  have hNewRepr := congrArg
    (fun edge : (fineCandidate input profile).datum.SourceEdge ↦ edge.1.2) hEqual
  have hLargeRel : (largePartition input profile).Rel first.1.2 second.1.2 := by
    apply (largePartition input profile).mem_block_iff _ _ |>.mp
    rw [← fine_background_newEdge_block input profile first.1.2 hFirstData.2,
      (finePastedResolution input profile).newEdge.mem_block_iff]
    exact hNewRepr
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
    exact hFirstRepr.symm.trans (hLargeRel.trans hSecondRepr)

theorem background_index_eq (path : StablePath data) (edge : data.SourceEdge)
    (hMem : edge ∈ oldBackgroundOccurrences input profile path) :
    (fineCandidate input profile).datum.sourceEdgeIndex
        ((fineCandidate input profile).newSourceEdge edge.1.2) =
      data.sourceEdgeIndex edge := by
  have hData := (mem_oldBackgroundOccurrences input profile path edge).mp hMem
  have hTarget := ((mem_occurrences _ _ _).mp hData.1).2
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge]
  change (finePastedResolution input profile).newEdge.blockCard edge.1.2 =
    (data.edgePartition edge.1.1).blockCard edge.1.2
  unfold SheetPartition.blockCard
  rw [fine_background_newEdge_block input profile edge.1.2 hData.2]
  change ((data.edgePartition (largeTarget input profile)).block edge.1.2).card =
    ((data.edgePartition edge.1.1).block edge.1.2).card
  rw [hTarget]

/-- The fine background column is an exact termwise reindexing of the old
large-direction background fibre, preserving every actual source index. -/
theorem backgroundColumn_eq_sum_old (path : StablePath data) :
    backgroundColumn input profile (fineStablePathEquiv input profile path) =
      ∑ edge ∈ oldBackgroundOccurrences input profile path,
        (1 : ℚ) / data.sourceEdgeIndex edge := by
  classical
  symm
  unfold backgroundColumn
  refine Finset.sum_bij
    (fun edge _ ↦ (fineCandidate input profile).newSourceEdge edge.1.2)
    ?_ ?_ ?_ ?_
  · exact fun edge hEdge ↦ new_mem_of_old_mem input profile path edge hEdge
  · exact fun first hFirst second hSecond hEqual ↦
      new_of_old_injective input profile path first second hFirst hSecond hEqual
  · intro edge hEdge
    exact ⟨_, old_mem_of_new_mem input profile path edge hEdge,
      new_old_roundtrip input profile path edge hEdge⟩
  · intro edge hEdge
    rw [background_index_eq input profile path edge hEdge]

/-- The complete fine new column on the original stable-row type.  The one
selected survivor lies in the old large-survivor row, but its reciprocal
index is the actual old small-survivor index; every other term is an old
large-direction background occurrence. -/
theorem matrix_new_on_old_row (path : StablePath data) :
    matrix (fineCandidate input profile).datum
        (fineStablePathEquiv input profile path)
        (occurrenceEquiv target wall (fineCandidate input profile).right none) =
      (if path = NonDanglingEdge.stablePath
          ⟨profile.large.1, profile.large_survives⟩ then
        (1 : ℚ) / data.sourceEdgeIndex profile.small.1
       else 0) +
        ∑ edge ∈ oldBackgroundOccurrences input profile path,
          (1 : ℚ) / data.sourceEdgeIndex edge := by
  classical
  rw [matrix_new input profile, backgroundColumn_eq_sum_old input profile]
  have hSelected : fineStablePathEquiv input profile
      (NonDanglingEdge.stablePath ⟨profile.large.1, profile.large_survives⟩) =
        (fineAnchorNew input profile).stablePath := by
    exact (fineStablePathEquiv_mk input profile
      ⟨profile.large.1, profile.large_survives⟩).trans
        (fine_anchor_new_stablePath_eq_large input profile).symm
  have hIff : fineStablePathEquiv input profile path =
      (fineAnchorNew input profile).stablePath ↔
        path = NonDanglingEdge.stablePath
          ⟨profile.large.1, profile.large_survives⟩ := by
    rw [← hSelected, Equiv.apply_eq_iff_eq]
  simp only [hIff, selected_newSourceEdge_index input profile]

end DraismaVargas.LocalCases.W3Nd2FineLimitMatrix
