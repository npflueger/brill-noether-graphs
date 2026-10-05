module

public import DraismaVargas.LocalCases.M11JoinedRowDescent
public import DraismaVargas.LocalCases.M11JoinedColumn

@[expose] public section

/-!
# The joined M11 matrix has the literal common-wall retained columns

Source: Draisma–Vargas Part I, arXiv:1909.12924, the limit-matrix lemma
(`lemma-limit-matrix-change`). The row equivalence
is the proved geometric one; retaining an old target occurrence identifies
the full row-filtered surviving occurrence set and preserves every index.
Thus deleting the joined new column gives the original wall matrix.
-/

namespace DraismaVargas.LocalCases.M11JoinedLimitMatrix

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource W2R1Target SecondEquation StableSourceMatrix
open M11SourceCandidates M11JoinedStableLift M11JoinedRowDescent ResolutionAwayFromWall

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  (input : W2SourceInput data star) {block : WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)
  (hCard : (data.vertexPartition wall).blockCard block.1 = 2)

/-- Exact retained-column occurrence dictionary, including the actual old
stable class. Injectivity of the geometric row map is essential here. -/
theorem occurrences_retained (path : StablePath data) (place : target.edges) :
    occurrences (joinedPattern data star block hCard).candidate.datum
        (stablePathEquiv input profile hCard path)
        (occurrenceEquiv target wall (joinedPattern data star block hCard).candidate.right (some place)) =
      (occurrences data path place).image (joinedPattern data star block hCard).candidate.oldSourceEdge := by
  classical
  let candidate := (joinedPattern data star block hCard).candidate
  ext edge
  constructor
  · intro hMem
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hMem
    rcases ResolutionPruning.sourceEdge_cases candidate edge with ⟨old, rfl⟩ | ⟨sheet, rfl⟩
    · have hOld : ¬ IsDangling data old := fun h ↦ hSurvives
        ((ResolutionPruning.isDangling_oldSourceEdge_iff candidate input.valid
          (M11SourceGenus.joined_sourceGenus data star block hCard) old).mpr h)
      refine Finset.mem_image.mpr ⟨old, (mem_occurrences _ _ _).mpr ⟨⟨hOld, ?_⟩, ?_⟩, rfl⟩
      · apply (stablePathEquiv input profile hCard).injective
        exact (stablePathEquiv_mk input profile hCard ⟨old, hOld⟩).trans hRow
      · exact Option.some.inj ((occurrenceEquiv target wall candidate.right).injective hTarget)
    · have hLabels := (occurrenceEquiv target wall candidate.right).injective hTarget
      cases hLabels
  · intro hMem
    obtain ⟨old, hOld, rfl⟩ := Finset.mem_image.mp hMem
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hOld
    refine (mem_occurrences _ _ _).mpr ⟨⟨ResolutionSurvival.not_isDangling_oldSourceEdge candidate input.valid.1 old hSurvives, ?_⟩, ?_⟩
    · exact (stablePathEquiv_mk input profile hCard ⟨old, hSurvives⟩).symm.trans
        (congrArg (stablePathEquiv input profile hCard) hRow)
    · exact congrArg (fun label ↦ occurrenceEquiv target wall candidate.right (some label)) hTarget

/-- Every retained matrix entry is the original wall entry under the actual
row equivalence and occurrence labelling. No displayed matrix is supplied. -/
theorem matrix_retained (path : StablePath data) (place : target.edges) :
    matrix (joinedPattern data star block hCard).candidate.datum
        (stablePathEquiv input profile hCard path)
        (occurrenceEquiv target wall (joinedPattern data star block hCard).candidate.right (some place)) =
      matrix data path place := by
  classical
  unfold matrix
  rw [occurrences_retained, Finset.sum_image]
  · exact Finset.sum_congr rfl fun edge _ ↦ by rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge]
  · intro first _ second _ hEqual
    exact ResolutionCut.oldSourceEdge_injective _ hEqual

/-- The distinguished term uses the original third stable row and the
background remains its explicit finite occurrence sum. Its comparison with
the old background is proved in `M11JoinedBackgroundMatrix`. -/
theorem matrix_new (path : StablePath data) :
    matrix (joinedPattern data star block hCard).candidate.datum
        (stablePathEquiv input profile hCard path)
        (occurrenceEquiv target wall (joinedPattern data star block hCard).candidate.right none) =
      (if path = NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩ then (1 / 2 : ℚ) else 0) +
        M11JoinedColumn.backgroundColumn data star block hCard (stablePathEquiv input profile hCard path) := by
  classical
  rw [M11JoinedColumn.joined_matrix_new_column input profile hCard]
  have hThird : stablePathEquiv input profile hCard
      (NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩) =
      (M11JoinedSurvival.joined_retainedSingle input profile hCard).stablePath := rfl
  have hIff : stablePathEquiv input profile hCard path =
      (M11JoinedSurvival.joined_retainedSingle input profile hCard).stablePath ↔
      path = NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩ := by
    rw [← hThird, Equiv.apply_eq_iff_eq]
  simp only [hIff]

end DraismaVargas.LocalCases.M11JoinedLimitMatrix
