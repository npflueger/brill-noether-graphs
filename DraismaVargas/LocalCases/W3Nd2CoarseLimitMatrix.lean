import DraismaVargas.LocalCases.W3Nd2RowDescent
import DraismaVargas.LocalCases.StableSourceMatrix

/-!
# Honest common-wall matrix formulas for the Figure 31 coarse member

Figure 31 is Case {w3-r1-nd2} of Draisma--Vargas Part I.
Retained target occurrences reproduce the original natural source matrix
under the geometric coarse stable-row equivalence.  On the new target
occurrence, the actual selected source occurrence is separated from every
background occurrence without replacing its dilation index by an inferred
small/large cardinality.
-/

namespace DraismaVargas.LocalCases.W3Nd2CoarseLimitMatrix

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource ThirdEquation StableSourceMatrix
open W3R1SourceProfile W3Nd2SourceCandidates W3Nd2FineRefinement
open W3Nd2FineCandidates W3Nd2Survival W3Nd2Background
open W3Nd2StableLift W3Nd2RowDescent
open ResolutionM11 ResolutionPruning ResolutionSurvival ResolutionAwayFromWall
open M11SplitRows

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  (input : W3SourceInput data star)
  (profile : Nd2Profile data input.distinguishedBlock)

/-- Exact retained-column occurrence dictionary under the actual coarse row
equivalence and canonical occurrence labelling. -/
theorem occurrences_retained (path : StablePath data) (place : target.edges) :
    occurrences (coarseCandidate input profile).datum
        (coarseStablePathEquiv input profile path)
        (occurrenceEquiv target wall (coarseCandidate input profile).right (some place)) =
      (occurrences data path place).image
        (coarseCandidate input profile).oldSourceEdge := by
  classical
  let candidate := coarseCandidate input profile
  ext edge
  constructor
  · intro hMem
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hMem
    rcases sourceEdge_cases candidate edge with ⟨old, rfl⟩ | ⟨sheet, rfl⟩
    · have hOld : ¬ IsDangling data old := fun h ↦ hSurvives
        ((isDangling_oldSourceEdge_iff candidate input.valid
          (coarseCandidate_sourceGenus input profile) old).mpr h)
      refine Finset.mem_image.mpr
        ⟨old, (mem_occurrences _ _ _).mpr ⟨⟨hOld, ?_⟩, ?_⟩, rfl⟩
      · apply (coarseStablePathEquiv input profile).injective
        exact (coarseStablePathEquiv_mk input profile ⟨old, hOld⟩).trans hRow
      · exact Option.some.inj
          ((occurrenceEquiv target wall candidate.right).injective hTarget)
    · have hLabels := (occurrenceEquiv target wall candidate.right).injective hTarget
      cases hLabels
  · intro hMem
    obtain ⟨old, hOld, rfl⟩ := Finset.mem_image.mp hMem
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hOld
    refine (mem_occurrences _ _ _).mpr
      ⟨⟨not_isDangling_oldSourceEdge candidate input.valid.1 old hSurvives, ?_⟩, ?_⟩
    · exact (coarseStablePathEquiv_mk input profile ⟨old, hSurvives⟩).symm.trans
        (congrArg (coarseStablePathEquiv input profile) hRow)
    · exact congrArg
        (fun label ↦ occurrenceEquiv target wall candidate.right (some label)) hTarget

/-- Every retained natural-matrix entry is literally its original wall
entry; no displayed matrix is supplied. -/
theorem matrix_retained (path : StablePath data) (place : target.edges) :
    matrix (coarseCandidate input profile).datum
        (coarseStablePathEquiv input profile path)
        (occurrenceEquiv target wall (coarseCandidate input profile).right (some place)) =
      matrix data path place := by
  classical
  unfold matrix
  rw [occurrences_retained, Finset.sum_image]
  · exact Finset.sum_congr rfl fun edge _ ↦ by
      rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge]
  · intro first _ second _ hEqual
    exact ResolutionCut.oldSourceEdge_injective _ hEqual

/-- The row-filtered new fibre with its unique selected-block occurrence
removed. -/
noncomputable def backgroundOccurrences
    (path : StablePath (coarseCandidate input profile).datum) :
    Finset (coarseCandidate input profile).datum.SourceEdge := by
  classical
  exact (occurrences (coarseCandidate input profile).datum path
    (occurrenceEquiv target wall (coarseCandidate input profile).right none)).erase
      ((coarseCandidate input profile).newSourceEdge (anchor input profile))

theorem mem_backgroundOccurrences
    (path : StablePath (coarseCandidate input profile).datum)
    (edge : (coarseCandidate input profile).datum.SourceEdge) :
    edge ∈ backgroundOccurrences input profile path ↔
      edge ∈ occurrences (coarseCandidate input profile).datum path
          (occurrenceEquiv target wall (coarseCandidate input profile).right none) ∧
        ¬ (data.vertexPartition wall).Rel input.distinguishedBlock.1 edge.1.2 := by
  classical
  let candidate := coarseCandidate input profile
  rw [backgroundOccurrences, Finset.mem_erase]
  constructor
  · rintro ⟨hNe, hMem⟩
    refine ⟨hMem, ?_⟩
    intro hSelected
    have hNew := eq_newSourceEdge_of_target candidate edge
      ((mem_occurrences _ _ _).mp hMem).2
    exact hNe (hNew.trans
      (coarse_newSourceEdge_eq_of_selected input profile edge.1.2 hSelected))
  · rintro ⟨hMem, hBackground⟩
    refine ⟨?_, hMem⟩
    intro hEqual
    apply hBackground
    rw [hEqual]
    let pasted := coarsePastedResolution input profile
    have hRefines : pasted.newEdge.Refines (data.vertexPartition wall) :=
      pasted.edge_refines_left.trans
        (SheetPartition.IsJoin.left_refines (LocalResolution.paste_contracts
          (data.vertexPartition wall) candidate.resolution candidate.contracts))
    change (data.vertexPartition wall).Rel input.distinguishedBlock.1
      (pasted.newEdge.repr (anchor input profile))
    exact (anchor_wall_rel input profile).trans
      (hRefines.rel (pasted.newEdge.rel_repr_right (anchor input profile)))

/-- The actual selected new occurrence lies in exactly its geometric coarse
stable row. -/
theorem selected_mem_occurrences_iff
    (path : StablePath (coarseCandidate input profile).datum) :
    (coarseCandidate input profile).newSourceEdge (anchor input profile) ∈
        occurrences (coarseCandidate input profile).datum path
          (occurrenceEquiv target wall (coarseCandidate input profile).right none) ↔
      path = (coarseAnchorNew input profile).stablePath := by
  rw [mem_occurrences]
  constructor
  · rintro ⟨⟨_, hRow⟩, _⟩
    exact hRow.symm
  · intro hRow
    exact ⟨⟨coarse_anchor_new_survives input profile, hRow.symm⟩, rfl⟩

/-- Every new-fibre contribution away from the distinguished wall block,
with its actual quotient-source index. -/
noncomputable def backgroundColumn
    (path : StablePath (coarseCandidate input profile).datum) : ℚ :=
  ∑ edge ∈ backgroundOccurrences input profile path,
    (1 : ℚ) / (coarseCandidate input profile).datum.sourceEdgeIndex edge

/-- The selected coarse new occurrence has the whole selected wall-block
index.  This is derived from the literal pasted partition, not from the
small/large numerical profile. -/
theorem selected_newSourceEdge_index :
    (coarseCandidate input profile).datum.sourceEdgeIndex
        ((coarseCandidate input profile).newSourceEdge (anchor input profile)) =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1 := by
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge]
  unfold SheetPartition.blockCard
  rw [coarse_pasted_newEdge_block_selected input profile (anchor input profile)
    (anchor_wall_rel input profile)]
  exact congrArg Finset.card
    ((data.vertexPartition wall).block_eq_of_rel (anchor_wall_rel input profile).symm)

/-- Exact coarse new-column decomposition: one actual selected occurrence
plus every actual background occurrence, all with their genuine indices. -/
theorem matrix_new
    (path : StablePath (coarseCandidate input profile).datum) :
    matrix (coarseCandidate input profile).datum path
        (occurrenceEquiv target wall (coarseCandidate input profile).right none) =
      (if path = (coarseAnchorNew input profile).stablePath then
          (1 : ℚ) /
            (coarseCandidate input profile).datum.sourceEdgeIndex
              ((coarseCandidate input profile).newSourceEdge (anchor input profile))
        else 0) + backgroundColumn input profile path := by
  classical
  let candidate := coarseCandidate input profile
  let selected := candidate.newSourceEdge (anchor input profile)
  let fibre := occurrences candidate.datum path
    (occurrenceEquiv target wall candidate.right none)
  by_cases hRow : path = (coarseAnchorNew input profile).stablePath
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

/-- Original small-direction occurrences in a fixed old row and outside the
distinguished wall block. -/
noncomputable def oldBackgroundOccurrences (path : StablePath data) :
    Finset data.SourceEdge := by
  classical
  exact (occurrences data path (smallTarget input profile)).filter
    (fun edge ↦ ¬ (data.vertexPartition wall).Rel
      input.distinguishedBlock.1 edge.1.2)

theorem mem_oldBackgroundOccurrences (path : StablePath data)
    (edge : data.SourceEdge) :
    edge ∈ oldBackgroundOccurrences input profile path ↔
      edge ∈ occurrences data path (smallTarget input profile) ∧
        ¬ (data.vertexPartition wall).Rel input.distinguishedBlock.1 edge.1.2 := by
  classical
  exact Finset.mem_filter

/-- Map an actual old background small-direction occurrence to its actual
coarse new occurrence, preserving survival and the geometrically identified
stable row. -/
theorem new_mem_of_old_mem (path : StablePath data) (edge : data.SourceEdge)
    (hMem : edge ∈ oldBackgroundOccurrences input profile path) :
    (coarseCandidate input profile).newSourceEdge edge.1.2 ∈
      backgroundOccurrences input profile (coarseStablePathEquiv input profile path) := by
  let candidate := coarseCandidate input profile
  have hOld := (mem_oldBackgroundOccurrences input profile path edge).mp hMem
  obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hOld.1
  have hCanonical : data.sourceEdge (smallTarget input profile) edge.1.2 = edge := by
    rw [← hTarget]
    exact GluingDatum.sourceEdge_self data edge
  have hCanonicalSurvives :
      ¬ IsDangling data (data.sourceEdge (smallTarget input profile) edge.1.2) := by
    rw [hCanonical]
    exact hSurvives
  have hNew := (coarse_background_new_survives_iff_oldSmall input profile
    edge.1.2 hOld.2).mpr hCanonicalSurvives
  refine (mem_backgroundOccurrences input profile _ _).mpr
    ⟨(mem_occurrences _ _ _).mpr ⟨⟨hNew, ?_⟩, rfl⟩, ?_⟩
  · exact (coarse_background_new_stablePath_eq_oldSmall input profile
      edge.1.2 hOld.2 hCanonicalSurvives).trans
      ((coarseStablePathEquiv_mk input profile
        ⟨data.sourceEdge (smallTarget input profile) edge.1.2,
          hCanonicalSurvives⟩).symm.trans
        (congrArg (coarseStablePathEquiv input profile)
          ((congrArg NonDanglingEdge.stablePath
            (show (⟨data.sourceEdge (smallTarget input profile) edge.1.2,
              hCanonicalSurvives⟩ : NonDanglingEdge data) = ⟨edge, hSurvives⟩ from
                Subtype.ext hCanonical)).trans hRow)))
  · let pasted := coarsePastedResolution input profile
    have hRefines : pasted.newEdge.Refines (data.vertexPartition wall) :=
      pasted.edge_refines_left.trans
        (SheetPartition.IsJoin.left_refines (LocalResolution.paste_contracts
          (data.vertexPartition wall) candidate.resolution candidate.contracts))
    intro hSelected
    apply hOld.2
    exact hSelected.trans
      (hRefines.rel (pasted.newEdge.rel_repr_left edge.1.2))

/-- Decode every actual coarse background new occurrence to the canonical old
small-direction occurrence in the same old stable row. -/
theorem old_mem_of_new_mem (path : StablePath data)
    (edge : (coarseCandidate input profile).datum.SourceEdge)
    (hMem : edge ∈ backgroundOccurrences input profile
      (coarseStablePathEquiv input profile path)) :
    data.sourceEdge (smallTarget input profile) edge.1.2 ∈
      oldBackgroundOccurrences input profile path := by
  let candidate := coarseCandidate input profile
  have hData := (mem_backgroundOccurrences input profile _ _).mp hMem
  obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hData.1
  have hEdge := eq_newSourceEdge_of_target candidate edge hTarget
  have hNew : ¬ IsDangling candidate.datum (candidate.newSourceEdge edge.1.2) := by
    rw [← hEdge]
    exact hSurvives
  have hOld : ¬ IsDangling data
      (data.sourceEdge (smallTarget input profile) edge.1.2) :=
    (coarse_background_new_survives_iff_oldSmall input profile edge.1.2 hData.2).mp hNew
  have hNewRow : NonDanglingEdge.stablePath
      ⟨candidate.newSourceEdge edge.1.2, hNew⟩ =
        coarseStablePathEquiv input profile path :=
    (congrArg NonDanglingEdge.stablePath
      (show (⟨candidate.newSourceEdge edge.1.2, hNew⟩ : NonDanglingEdge candidate.datum) =
        ⟨edge, hSurvives⟩ from Subtype.ext hEdge.symm)).trans hRow
  refine (mem_oldBackgroundOccurrences input profile path _).mpr
    ⟨(mem_occurrences _ _ _).mpr ⟨⟨hOld, ?_⟩, rfl⟩, ?_⟩
  · apply (coarseStablePathEquiv input profile).injective
    exact (coarseStablePathEquiv_mk input profile
      ⟨data.sourceEdge (smallTarget input profile) edge.1.2, hOld⟩).trans
      ((coarse_background_new_stablePath_eq_oldSmall input profile
        edge.1.2 hData.2 hOld).symm.trans hNewRow)
  · intro hSelected
    apply hData.2
    exact hSelected.trans
      ((StableLocalProperties.refines_of_mem_incidentEdges data
        (smallTarget_mem input profile)).rel
          ((data.edgePartition (smallTarget input profile)).rel_repr_left edge.1.2))

theorem new_old_roundtrip (path : StablePath data)
    (edge : (coarseCandidate input profile).datum.SourceEdge)
    (hMem : edge ∈ backgroundOccurrences input profile
      (coarseStablePathEquiv input profile path)) :
    (coarseCandidate input profile).newSourceEdge
        (data.sourceEdge (smallTarget input profile) edge.1.2).1.2 = edge := by
  let candidate := coarseCandidate input profile
  have hData := (mem_backgroundOccurrences input profile _ _).mp hMem
  have hTarget := ((mem_occurrences _ _ _).mp hData.1).2
  have hEdge := eq_newSourceEdge_of_target candidate edge hTarget
  exact (coarse_background_new_eq_of_small_source_eq input profile edge.1.2
    (data.sourceEdge (smallTarget input profile) edge.1.2).1.2 hData.2
      (GluingDatum.sourceEdge_self data
        (data.sourceEdge (smallTarget input profile) edge.1.2))).trans hEdge.symm

theorem new_of_old_injective (path : StablePath data)
    (first second : data.SourceEdge)
    (hFirst : first ∈ oldBackgroundOccurrences input profile path)
    (hSecond : second ∈ oldBackgroundOccurrences input profile path)
    (hEqual : (coarseCandidate input profile).newSourceEdge first.1.2 =
      (coarseCandidate input profile).newSourceEdge second.1.2) : first = second := by
  have hFirstData := (mem_oldBackgroundOccurrences input profile path first).mp hFirst
  have hSecondData := (mem_oldBackgroundOccurrences input profile path second).mp hSecond
  have hFirstTarget := ((mem_occurrences _ _ _).mp hFirstData.1).2
  have hSecondTarget := ((mem_occurrences _ _ _).mp hSecondData.1).2
  have hNewRepr := congrArg
    (fun edge : (coarseCandidate input profile).datum.SourceEdge ↦ edge.1.2) hEqual
  have hNewRel : (coarsePastedResolution input profile).newEdge.Rel
      first.1.2 second.1.2 := hNewRepr
  have hFineRel : (finePartition input profile).Rel first.1.2 second.1.2 := by
    apply (finePartition input profile).mem_block_iff _ _ |>.mp
    rw [← coarse_background_newEdge_block input profile first.1.2 hFirstData.2,
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

/-- The background occurrence bijection preserves the genuine source-edge
index, by equality of the pasted new block with the actual small-direction
block. -/
theorem background_index_eq (path : StablePath data) (edge : data.SourceEdge)
    (hMem : edge ∈ oldBackgroundOccurrences input profile path) :
    (coarseCandidate input profile).datum.sourceEdgeIndex
        ((coarseCandidate input profile).newSourceEdge edge.1.2) =
      data.sourceEdgeIndex edge := by
  have hData := (mem_oldBackgroundOccurrences input profile path edge).mp hMem
  have hTarget := ((mem_occurrences _ _ _).mp hData.1).2
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge]
  change (coarsePastedResolution input profile).newEdge.blockCard edge.1.2 =
    (data.edgePartition edge.1.1).blockCard edge.1.2
  unfold SheetPartition.blockCard
  rw [coarse_background_newEdge_block input profile edge.1.2 hData.2]
  change ((data.edgePartition (smallTarget input profile)).block edge.1.2).card =
    ((data.edgePartition edge.1.1).block edge.1.2).card
  rw [hTarget]

/-- The complete background part of the coarse new column is an actual
term-by-term reindexing of the original small-direction background fibre. -/
theorem backgroundColumn_eq_sum_old (path : StablePath data) :
    backgroundColumn input profile (coarseStablePathEquiv input profile path) =
      ∑ edge ∈ oldBackgroundOccurrences input profile path,
        (1 : ℚ) / data.sourceEdgeIndex edge := by
  classical
  symm
  unfold backgroundColumn
  refine Finset.sum_bij
    (fun edge _ ↦ (coarseCandidate input profile).newSourceEdge edge.1.2)
    ?_ ?_ ?_ ?_
  · exact fun edge hEdge ↦ new_mem_of_old_mem input profile path edge hEdge
  · exact fun first hFirst second hSecond hEqual ↦
      new_of_old_injective input profile path first second hFirst hSecond hEqual
  · intro edge hEdge
    exact ⟨_, old_mem_of_new_mem input profile path edge hEdge,
      new_old_roundtrip input profile path edge hEdge⟩
  · intro edge hEdge
    rw [background_index_eq input profile path edge hEdge]

/-- The complete coarse new column on the original stable-row type.  Its
selected coefficient is the reciprocal of the actual selected wall-block
cardinality, and the residual term is the exact old small-direction
background sum. -/
theorem matrix_new_on_old_row (path : StablePath data) :
    matrix (coarseCandidate input profile).datum
        (coarseStablePathEquiv input profile path)
        (occurrenceEquiv target wall (coarseCandidate input profile).right none) =
      (if path = NonDanglingEdge.stablePath
          ⟨profile.small.1, profile.small_survives⟩ then
        (1 : ℚ) /
          (data.vertexPartition wall).blockCard input.distinguishedBlock.1
       else 0) +
        ∑ edge ∈ oldBackgroundOccurrences input profile path,
          (1 : ℚ) / data.sourceEdgeIndex edge := by
  classical
  rw [matrix_new input profile, backgroundColumn_eq_sum_old input profile]
  have hSelected : coarseStablePathEquiv input profile
      (NonDanglingEdge.stablePath ⟨profile.small.1, profile.small_survives⟩) =
        (coarseAnchorNew input profile).stablePath := by
    exact (coarseStablePathEquiv_mk input profile
      ⟨profile.small.1, profile.small_survives⟩).trans
        (coarse_anchor_new_stablePath_eq_small input profile).symm
  have hIff : coarseStablePathEquiv input profile path =
      (coarseAnchorNew input profile).stablePath ↔
        path = NonDanglingEdge.stablePath
          ⟨profile.small.1, profile.small_survives⟩ := by
    rw [← hSelected, Equiv.apply_eq_iff_eq]
  simp only [hIff, selected_newSourceEdge_index input profile]

end DraismaVargas.LocalCases.W3Nd2CoarseLimitMatrix
