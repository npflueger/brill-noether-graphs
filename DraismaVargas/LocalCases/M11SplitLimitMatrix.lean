import DraismaVargas.LocalCases.M11SplitRowDescent

/-!
# The first-split M11 matrix has the literal common-wall retained columns

Source: the limit-matrix lemma of Draisma--Vargas Part I
(`lemma-limit-matrix-change`, in the subsection on inherited properties of
limits). The row equivalence
is the proved geometric one; retaining an old target occurrence identifies
the full row-filtered surviving occurrence set and preserves every index.
Thus deleting the first-split new column gives the original wall matrix.
-/

namespace DraismaVargas.LocalCases.M11SplitLimitMatrix

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource W2R1Target SecondEquation StableSourceMatrix
open M11SourceCandidates M11SplitStableLift M11SplitRowDescent ResolutionAwayFromWall

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  (input : W2SourceInput data star) {block : WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)
  (hCard : (data.vertexPartition wall).blockCard block.1 = 2)

/-- Exact retained-column occurrence dictionary, including the actual old
stable class. Injectivity of the geometric row map is essential here. -/
theorem occurrences_retained (path : StablePath data) (place : target.edges) :
    occurrences (firstSplitPattern input profile hCard).candidate.datum
        (stablePathEquiv input profile hCard path)
        (occurrenceEquiv target wall (firstSplitPattern input profile hCard).candidate.right (some place)) =
      (occurrences data path place).image (firstSplitPattern input profile hCard).candidate.oldSourceEdge := by
  classical
  let candidate := (firstSplitPattern input profile hCard).candidate
  ext edge
  constructor
  · intro hMem
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hMem
    rcases ResolutionPruning.sourceEdge_cases candidate edge with ⟨old, rfl⟩ | ⟨sheet, rfl⟩
    · have hOld : ¬ IsDangling data old := fun h ↦ hSurvives
        ((ResolutionPruning.isDangling_oldSourceEdge_iff candidate input.valid
          (M11SourceGenus.firstSplit_sourceGenus input profile hCard) old).mpr h)
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
    matrix (firstSplitPattern input profile hCard).candidate.datum
        (stablePathEquiv input profile hCard path)
        (occurrenceEquiv target wall (firstSplitPattern input profile hCard).candidate.right (some place)) =
      matrix data path place := by
  classical
  unfold matrix
  rw [occurrences_retained, Finset.sum_image]
  · exact Finset.sum_congr rfl fun edge _ ↦ by rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge]
  · intro first _ second _ hEqual
    exact ResolutionCut.oldSourceEdge_injective _ hEqual

/-- The new column is twice the indicator of the actual old deleted-sheet
double row. Together with `matrix_retained` this identifies every column. -/
theorem matrix_new (path : StablePath data) :
    matrix (firstSplitPattern input profile hCard).candidate.datum
        (stablePathEquiv input profile hCard path)
        (occurrenceEquiv target wall (firstSplitPattern input profile hCard).candidate.right none) =
      if path = (newOldEdge profile hCard).stablePath then 2 else 0 := by
  classical
  rw [M11SplitColumn.firstSplit_matrix_new_column input profile hCard]
  have hDouble : stablePathEquiv input profile hCard (newOldEdge profile hCard).stablePath =
      (M11SplitSurvival.firstSplit_retainedDouble input profile hCard).stablePath := rfl
  rw [← hDouble]
  simp only [Equiv.apply_eq_iff_eq]

end DraismaVargas.LocalCases.M11SplitLimitMatrix
