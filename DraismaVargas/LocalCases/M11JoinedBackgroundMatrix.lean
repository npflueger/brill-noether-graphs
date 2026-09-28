import DraismaVargas.LocalCases.M11JoinedLimitMatrix

/-!
# Identifying Figure 32's joined background sum on the original wall

The old single-direction fibre has exactly one distinguished survivor, the
third occurrence. After removing it, same-sheet transport is a bijection
onto the joined background fibre, preserving survival, actual stable row,
and index. This identifies the source's `s` without assuming a cofactor sum.
-/

namespace DraismaVargas.LocalCases.M11JoinedBackgroundMatrix

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource W2R1Target SecondEquation StableSourceMatrix
open M11SourceCandidates M11JoinedGeometry M11JoinedBackground M11JoinedColumn
open M11JoinedStableLift M11JoinedRowDescent M11JoinedDescentGeometry

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  (input : W2SourceInput data star) {block : WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)
  (hCard : (data.vertexPartition wall).blockCard block.1 = 2)

/-- The actual old single-direction fibre, with its third occurrence removed. -/
noncomputable def oldBackgroundOccurrences (path : StablePath data) : Finset data.SourceEdge := by
  classical
  exact (occurrences data path (star.edge profile.singleLabel)).erase profile.third.1

theorem mem_oldBackgroundOccurrences (path : StablePath data) (edge : data.SourceEdge) :
    edge ∈ oldBackgroundOccurrences profile path ↔
      edge ∈ occurrences data path (star.edge profile.singleLabel) ∧
        ¬ (data.vertexPartition wall).Rel block.1 edge.1.2 := by
  classical
  rw [oldBackgroundOccurrences, Finset.mem_erase]
  constructor
  · rintro ⟨hNe, hMem⟩
    refine ⟨hMem, ?_⟩
    intro hRel
    obtain ⟨⟨hSurvives, _⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hMem
    exact hNe (single_retained_survivor_eq_third profile ⟨edge, hSurvives⟩ hTarget hRel)
  · rintro ⟨hMem, hBackground⟩
    refine ⟨?_, hMem⟩
    intro hEqual
    apply hBackground
    rw [hEqual]
    exact M11SplitSurvival.sheet_rel_of_incident_block profile.third

theorem new_mem_of_old_mem (path : StablePath data) (edge : data.SourceEdge)
    (hMem : edge ∈ oldBackgroundOccurrences profile path) :
    (joinedPattern data star block hCard).candidate.newSourceEdge edge.1.2 ∈
      backgroundOccurrences data star block hCard (stablePathEquiv input profile hCard path) := by
  have hOld := (mem_oldBackgroundOccurrences profile path edge).mp hMem
  obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hOld.1
  have hCanonical := background_sourceEdge_eq input profile profile.singleLabel edge.1.2 hOld.2 edge hTarget rfl
  have hCanonicalSurvives : ¬ IsDangling data (data.sourceEdge (star.edge profile.singleLabel) edge.1.2) := by
    rw [hCanonical]
    exact hSurvives
  have hCanonicalRow : NonDanglingEdge.stablePath
      ⟨data.sourceEdge (star.edge profile.singleLabel) edge.1.2, hCanonicalSurvives⟩ = path :=
    (congrArg NonDanglingEdge.stablePath (show
      (⟨data.sourceEdge (star.edge profile.singleLabel) edge.1.2, hCanonicalSurvives⟩ : NonDanglingEdge data) =
        ⟨edge, hSurvives⟩ from Subtype.ext hCanonical)).trans hRow
  have hNew := background_survives input profile hCard profile.singleLabel edge.1.2 hOld.2 hCanonicalSurvives
  refine (mem_backgroundOccurrences data star block hCard _ _).mpr ⟨(mem_occurrences _ _ _).mpr ⟨⟨hNew, ?_⟩, rfl⟩, ?_⟩
  · exact (background_stablePath_eq_retained input profile hCard profile.singleLabel edge.1.2 hOld.2 hCanonicalSurvives).trans
      ((stablePathEquiv_mk input profile hCard ⟨_, hCanonicalSurvives⟩).symm.trans
        (congrArg (stablePathEquiv input profile hCard) hCanonicalRow))
  · rw [newSourceEdge_sheet]
    exact fun h ↦ hOld.2 (h.trans ((data.vertexPartition wall).rel_repr_left edge.1.2))

/-- An actual joined background occurrence has a surviving old preimage in
the original single direction, in the same geometrically identified row. -/
theorem old_mem_of_new_mem (path : StablePath data)
    (edge : (joinedPattern data star block hCard).candidate.datum.SourceEdge)
    (hMem : edge ∈ backgroundOccurrences data star block hCard (stablePathEquiv input profile hCard path)) :
    data.sourceEdge (star.edge profile.singleLabel) edge.1.2 ∈ oldBackgroundOccurrences profile path := by
  let candidate := (joinedPattern data star block hCard).candidate
  have hData := (mem_backgroundOccurrences data star block hCard _ _).mp hMem
  obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hData.1
  have hEdge := M11SplitRows.eq_newSourceEdge_of_target candidate edge hTarget
  have hNew : ¬ IsDangling candidate.datum (candidate.newSourceEdge edge.1.2) := by
    rw [← hEdge]
    exact hSurvives
  have hNewRow : NonDanglingEdge.stablePath ⟨candidate.newSourceEdge edge.1.2, hNew⟩ =
      stablePathEquiv input profile hCard path :=
    (congrArg NonDanglingEdge.stablePath (show
      (⟨candidate.newSourceEdge edge.1.2, hNew⟩ : NonDanglingEdge candidate.datum) = ⟨edge, hSurvives⟩
      from Subtype.ext hEdge.symm)).trans hRow
  have hOld : ¬ IsDangling data (data.sourceEdge (star.edge profile.singleLabel) edge.1.2) :=
    fun h ↦ hNew ((background_isDangling_iff input profile hCard profile.singleLabel edge.1.2 hData.2).mpr h)
  refine (mem_oldBackgroundOccurrences profile path _).mpr ⟨(mem_occurrences _ _ _).mpr ⟨⟨hOld, ?_⟩, rfl⟩, ?_⟩
  · apply (stablePathEquiv input profile hCard).injective
    exact (stablePathEquiv_mk input profile hCard ⟨_, hOld⟩).trans
      ((background_stablePath_eq_retained input profile hCard profile.singleLabel edge.1.2 hData.2 hOld).symm.trans hNewRow)
  · exact fun h ↦ hData.2 (h.trans ((star.edgePartition_refines_wall data profile.singleLabel).rel
      ((data.edgePartition (star.edge profile.singleLabel)).rel_repr_left edge.1.2)))

theorem new_old_roundtrip (path : StablePath data)
    (edge : (joinedPattern data star block hCard).candidate.datum.SourceEdge)
    (hMem : edge ∈ backgroundOccurrences data star block hCard (stablePathEquiv input profile hCard path)) :
    (joinedPattern data star block hCard).candidate.newSourceEdge
      (data.sourceEdge (star.edge profile.singleLabel) edge.1.2).1.2 = edge := by
  have hData := (mem_backgroundOccurrences data star block hCard _ _).mp hMem
  have hTarget := ((mem_occurrences _ _ _).mp hData.1).2
  exact (newSourceEdge_eq_of_rel data star block hCard _ _
    ((star.edgePartition_refines_wall data profile.singleLabel).rel
      ((data.edgePartition (star.edge profile.singleLabel)).rel_repr_left edge.1.2))).trans
    (M11SplitRows.eq_newSourceEdge_of_target _ edge hTarget).symm

include input in
theorem new_of_old_injective (path : StablePath data) (first second : data.SourceEdge)
    (hFirst : first ∈ oldBackgroundOccurrences profile path)
    (hSecond : second ∈ oldBackgroundOccurrences profile path)
    (hEqual : (joinedPattern data star block hCard).candidate.newSourceEdge first.1.2 =
      (joinedPattern data star block hCard).candidate.newSourceEdge second.1.2) : first = second := by
  have hFirstData := (mem_oldBackgroundOccurrences profile path first).mp hFirst
  have hSecondData := (mem_oldBackgroundOccurrences profile path second).mp hSecond
  have hRel := (newSourceEdge_eq_iff_rel data star block hCard _ _).mp hEqual
  have hFirstCanonical := background_sourceEdge_eq input profile profile.singleLabel first.1.2 hFirstData.2 first
    ((mem_occurrences _ _ _).mp hFirstData.1).2 rfl
  have hSecondCanonical := background_sourceEdge_eq input profile profile.singleLabel first.1.2 hFirstData.2 second
    ((mem_occurrences _ _ _).mp hSecondData.1).2 hRel
  exact hFirstCanonical.symm.trans hSecondCanonical

/-- The exact background sum, transported term by term to the original wall. -/
theorem backgroundColumn_eq_sum_old (path : StablePath data) :
    backgroundColumn data star block hCard (stablePathEquiv input profile hCard path) =
      ∑ edge ∈ oldBackgroundOccurrences profile path, (1 : ℚ) / data.sourceEdgeIndex edge := by
  classical
  symm
  unfold backgroundColumn
  refine Finset.sum_bij (fun edge _ ↦ (joinedPattern data star block hCard).candidate.newSourceEdge edge.1.2) ?_ ?_ ?_ ?_
  · exact fun edge hEdge ↦ new_mem_of_old_mem input profile hCard path edge hEdge
  · exact fun first hFirst second hSecond hEqual ↦ new_of_old_injective input profile hCard path first second hFirst hSecond hEqual
  · intro edge hEdge
    exact ⟨_, old_mem_of_new_mem input profile hCard path edge hEdge, new_old_roundtrip input profile hCard path edge hEdge⟩
  · intro edge hEdge
    have hData := (mem_oldBackgroundOccurrences profile path edge).mp hEdge
    have hCanonical := background_sourceEdge_eq input profile profile.singleLabel edge.1.2 hData.2 edge
      ((mem_occurrences _ _ _).mp hData.1).2 rfl
    rw [background_index_eq input profile hCard profile.singleLabel edge.1.2 hData.2, hCanonical]

theorem third_mem_occurrences_iff (path : StablePath data) :
    profile.third.1 ∈ occurrences data path (star.edge profile.singleLabel) ↔
      path = NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩ := by
  rw [mem_occurrences]
  constructor
  · rintro ⟨⟨_, hRow⟩, _⟩
    exact hRow.symm
  · intro hRow
    exact ⟨⟨profile.third_survives, hRow.symm⟩, profile.third_target⟩

include hCard in
/-- Put back exactly the old third term, whose dilation index is one. -/
theorem sum_old_add_third (path : StablePath data) :
    (∑ edge ∈ oldBackgroundOccurrences profile path, (1 : ℚ) / data.sourceEdgeIndex edge) +
        (if path = NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩ then (1 : ℚ) else 0) =
      matrix data path (star.edge profile.singleLabel) := by
  classical
  have hIndex := index_eq_one_of_blockCard_eq_two profile hCard profile.third
  by_cases hRow : path = NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩
  · have hMem := (third_mem_occurrences_iff profile path).mpr hRow
    have hSum := Finset.sum_erase_add (occurrences data path (star.edge profile.singleLabel))
      (fun edge ↦ (1 : ℚ) / data.sourceEdgeIndex edge) hMem
    change (∑ edge ∈ oldBackgroundOccurrences profile path, (1 : ℚ) / data.sourceEdgeIndex edge) +
      (1 : ℚ) / data.sourceEdgeIndex profile.third.1 = matrix data path (star.edge profile.singleLabel) at hSum
    simpa only [if_pos hRow, hIndex, Nat.cast_one, div_one] using hSum
  · have hNot : profile.third.1 ∉ occurrences data path (star.edge profile.singleLabel) :=
      fun h ↦ hRow ((third_mem_occurrences_iff profile path).mp h)
    simp only [oldBackgroundOccurrences, Finset.erase_eq_of_notMem hNot, if_neg hRow, add_zero, matrix]

/-- The source's joined background `s` is the old single column with the
one third-row contribution removed. -/
theorem backgroundColumn_add_third (path : StablePath data) :
    backgroundColumn data star block hCard (stablePathEquiv input profile hCard path) +
        (if path = NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩ then (1 : ℚ) else 0) =
      matrix data path (star.edge profile.singleLabel) := by
  rw [backgroundColumn_eq_sum_old]
  exact sum_old_add_third profile hCard path

/-- The full joined new column on the original row type. Together with
`M11JoinedLimitMatrix.matrix_retained`, this describes every actual column. -/
theorem matrix_new_eq_old_sub_half (path : StablePath data) :
    matrix (joinedPattern data star block hCard).candidate.datum
        (stablePathEquiv input profile hCard path)
        (occurrenceEquiv target wall (joinedPattern data star block hCard).candidate.right none) =
      matrix data path (star.edge profile.singleLabel) -
        (if path = NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩ then (1 / 2 : ℚ) else 0) := by
  classical
  rw [M11JoinedLimitMatrix.matrix_new input profile hCard]
  have hBackground := backgroundColumn_add_third input profile hCard path
  by_cases hRow : path = NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩
  · simp only [if_pos hRow] at hBackground ⊢
    linarith
  · simp only [if_neg hRow] at hBackground ⊢
    linarith

/-- The joined contribution for any weights on the original stable rows.
In a determinant application these weights will be the common cofactors. -/
theorem sum_weighted_new_column (weight : StablePath data → ℚ) :
    (∑ path, weight path * matrix (joinedPattern data star block hCard).candidate.datum
        (stablePathEquiv input profile hCard path)
        (occurrenceEquiv target wall (joinedPattern data star block hCard).candidate.right none)) =
      (∑ path, weight path * matrix data path (star.edge profile.singleLabel)) -
        weight (NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩) / 2 := by
  classical
  simp_rw [matrix_new_eq_old_sub_half input profile hCard, mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- When the row weights annihilate the old single column, the joined
contribution is minus half the third weight. The annihilation premise is
explicit; the natural matrix and geometric row map are the proved ones. -/
theorem sum_weighted_new_column_of_annihilator (weight : StablePath data → ℚ)
    (hAnnihilates : (∑ path, weight path * matrix data path (star.edge profile.singleLabel)) = 0) :
    (∑ path, weight path * matrix (joinedPattern data star block hCard).candidate.datum
        (stablePathEquiv input profile hCard path)
        (occurrenceEquiv target wall (joinedPattern data star block hCard).candidate.right none)) =
      -weight (NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩) / 2 := by
  rw [sum_weighted_new_column input profile hCard weight, hAnnihilates]
  ring

end DraismaVargas.LocalCases.M11JoinedBackgroundMatrix
