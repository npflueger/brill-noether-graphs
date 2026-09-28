import DraismaVargas.LocalCases.M11SplitBranch
import DraismaVargas.LocalCases.M11BranchSeparation
import DraismaVargas.LocalCases.StablePathCount
import DraismaVargas.LocalCases.M11JoinedIncidence

/-!
# Literal branch flags for the first M11 split

The old deleted-sheet double flag is replaced by the new arm at the unique
fresh branch. The other double flag and the third survivor are retained.
These are three distinct occurrences, not necessarily three distinct rows.
-/

namespace DraismaVargas.LocalCases.M11SplitBranchFlags

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource W2R1Target SecondEquation
open M11SourceCandidates M11SplitSurvival M11SplitBranch
open M11SplitRowDescent ResolutionAwayFromWall

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  (input : W2SourceInput data star) {block : WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)
  (hCard : (data.vertexPartition wall).blockCard block.1 = 2)

noncomputable def oldFirst : NonDanglingEdge data := newOldEdge profile hCard
noncomputable def oldSecond : NonDanglingEdge data := branchDouble profile hCard
noncomputable def oldThird : NonDanglingEdge data := ⟨profile.third.1, profile.third_survives⟩

noncomputable def firstEnd : NonDanglingEdge (firstSplitPattern input profile hCard).candidate.datum :=
  ⟨(firstSplitPattern input profile hCard).candidate.newSourceEdge profile.third.1.1.2,
    firstSplit_new_survives input profile hCard _ (sheet_rel_of_incident_block profile.third)⟩

noncomputable def secondEnd : NonDanglingEdge (firstSplitPattern input profile hCard).candidate.datum :=
  retainedEdge (firstSplitPattern input profile hCard).candidate input.valid.1 (oldSecond profile hCard)

noncomputable def thirdEnd : NonDanglingEdge (firstSplitPattern input profile hCard).candidate.datum :=
  retainedEdge (firstSplitPattern input profile hCard).candidate input.valid.1 (oldThird profile)

include hCard in
theorem old_double_incident (sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    Incident data (data.sourceEdge (star.edge profile.doubleLabel) sheet)
      (WallBlock.sourceVertex data wall block) := by
  apply (incident_iff_target_mem_and_rel _ _ _).mpr
  refine ⟨star.edge_mem_incidentEdges profile.doubleLabel, ?_⟩
  change (data.vertexPartition wall).Rel ((data.vertexPartition wall).repr block.1)
    (data.sourceEdge (star.edge profile.doubleLabel) sheet).1.2
  rw [M11BranchSeparation.double_sourceEdge_sheet profile hCard sheet hRel]
  exact ((data.vertexPartition wall).rel_repr_left block.1).trans hRel

theorem oldFirst_ne_oldSecond : oldFirst profile hCard ≠ oldSecond profile hCard := by
  intro h
  have hSheets := congrArg (fun edge : NonDanglingEdge data ↦ edge.1.1.2) h
  change (data.sourceEdge (star.edge profile.doubleLabel) profile.deleted.edge.1.1.2).1.2 =
    (data.sourceEdge (star.edge profile.doubleLabel) profile.third.1.1.2).1.2 at hSheets
  rw [M11BranchSeparation.double_sourceEdge_sheet profile hCard _
      (sheet_rel_of_incident_block profile.deleted.edge),
    M11BranchSeparation.double_sourceEdge_sheet profile hCard _
      (sheet_rel_of_incident_block profile.third)] at hSheets
  exact third_sheet_ne_deleted profile hCard hSheets.symm

theorem oldFirst_ne_oldThird : oldFirst profile hCard ≠ oldThird profile := by
  intro h
  have hTargets := congrArg (fun edge : NonDanglingEdge data ↦ edge.1.1.1) h
  exact profile.labels_ne (star.edge_injective (hTargets.trans profile.third_target))

theorem oldSecond_ne_oldThird : oldSecond profile hCard ≠ oldThird profile := by
  intro h
  have hTargets := congrArg (fun edge : NonDanglingEdge data ↦ edge.1.1.1) h
  exact profile.labels_ne (star.edge_injective (hTargets.trans profile.third_target))

/-- Exact old branch occurrences, with the two double directions named by
their physical sheets instead of a possibly unrelated profile ordering. -/
theorem old_incidentEdges : StablePathCount.incidentEdges data (WallBlock.sourceVertex data wall block) =
    {oldFirst profile hCard, oldSecond profile hCard, oldThird profile} := by
  classical
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro edge hEdge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
    rcases hEdge with rfl | rfl | rfl
    · exact (StablePathCount.mem_incidentEdges _ _ _).mpr
        (old_double_incident profile hCard _ (sheet_rel_of_incident_block profile.deleted.edge))
    · exact (StablePathCount.mem_incidentEdges _ _ _).mpr
        (old_double_incident profile hCard _ (sheet_rel_of_incident_block profile.third))
    · exact (StablePathCount.mem_incidentEdges _ _ _).mpr profile.third.2
  · rw [StablePathCount.card_incidentEdges, profile.valency]
    simp [oldFirst_ne_oldSecond profile hCard, oldFirst_ne_oldThird profile hCard,
      oldSecond_ne_oldThird profile hCard]

theorem firstEnd_ne_secondEnd : firstEnd input profile hCard ≠ secondEnd input profile hCard := by
  intro h
  have hLabels := (occurrenceEquiv target wall (firstSplitPattern input profile hCard).candidate.right).injective
    (congrArg (fun edge : NonDanglingEdge (firstSplitPattern input profile hCard).candidate.datum ↦
      edge.1.1.1) h)
  cases hLabels

theorem firstEnd_ne_thirdEnd : firstEnd input profile hCard ≠ thirdEnd input profile hCard := by
  intro h
  have hLabels := (occurrenceEquiv target wall (firstSplitPattern input profile hCard).candidate.right).injective
    (congrArg (fun edge : NonDanglingEdge (firstSplitPattern input profile hCard).candidate.datum ↦
      edge.1.1.1) h)
  cases hLabels

theorem secondEnd_ne_thirdEnd : secondEnd input profile hCard ≠ thirdEnd input profile hCard := by
  intro h
  exact oldSecond_ne_oldThird profile hCard (retainedEdge_injective _ input.valid.1 h)

/-- Exact surviving branch flags as a finset of surviving occurrences. -/
theorem incidentEdges_branchVertex : StablePathCount.incidentEdges
    (firstSplitPattern input profile hCard).candidate.datum (branchVertex input profile hCard) =
    {firstEnd input profile hCard, secondEnd input profile hCard, thirdEnd input profile hCard} := by
  classical
  ext edge
  rw [StablePathCount.mem_incidentEdges]
  have hCensus := congrArg (fun edges ↦ edge.1 ∈ edges)
    (nonDanglingIncident_branchVertex input profile hCard)
  simp only [mem_nonDanglingIncident, edge.2, not_false_eq_true, true_and, branchEdges,
    Finset.mem_insert, Finset.mem_singleton] at hCensus
  rw [hCensus]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inr (Subtype.ext h))
    · exact Or.inr (Or.inl (Subtype.ext h))
  · rintro (rfl | rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)

theorem firstEnd_stablePath : (firstEnd input profile hCard).stablePath =
    stablePathEquiv input profile hCard (oldFirst profile hCard).stablePath := by
  have h := firstSplit_new_stablePath_eq_retained input profile hCard _
    (sheet_rel_of_incident_block profile.third)
  exact h.trans (stablePathEquiv_mk input profile hCard (oldFirst profile hCard)).symm

theorem secondEnd_stablePath : (secondEnd input profile hCard).stablePath =
    stablePathEquiv input profile hCard (oldSecond profile hCard).stablePath :=
  (stablePathEquiv_mk input profile hCard (oldSecond profile hCard)).symm

theorem thirdEnd_stablePath : (thirdEnd input profile hCard).stablePath =
    stablePathEquiv input profile hCard (oldThird profile).stablePath :=
  (stablePathEquiv_mk input profile hCard (oldThird profile)).symm

/-- All row-incidence multiplicities at the unique branch are preserved.
In particular two flags of a loop remain counted separately. -/
theorem incidenceCount_branchVertex (path : StablePath data) :
    StablePathCount.incidenceCount data (WallBlock.sourceVertex data wall block) path =
      StablePathCount.incidenceCount (firstSplitPattern input profile hCard).candidate.datum
        (branchVertex input profile hCard) (stablePathEquiv input profile hCard path) := by
  classical
  rw [M11JoinedIncidence.incidenceCount_of_incidentEdges_three _
    (oldFirst profile hCard) (oldSecond profile hCard) (oldThird profile)
    (oldFirst_ne_oldSecond profile hCard) (oldFirst_ne_oldThird profile hCard)
    (oldSecond_ne_oldThird profile hCard) (old_incidentEdges profile hCard)]
  rw [M11JoinedIncidence.incidenceCount_of_incidentEdges_three _
    (firstEnd input profile hCard) (secondEnd input profile hCard) (thirdEnd input profile hCard)
    (firstEnd_ne_secondEnd input profile hCard) (firstEnd_ne_thirdEnd input profile hCard)
    (secondEnd_ne_thirdEnd input profile hCard) (incidentEdges_branchVertex input profile hCard)]
  rw [firstEnd_stablePath, secondEnd_stablePath, thirdEnd_stablePath]
  simp only [Equiv.apply_eq_iff_eq]

end DraismaVargas.LocalCases.M11SplitBranchFlags
