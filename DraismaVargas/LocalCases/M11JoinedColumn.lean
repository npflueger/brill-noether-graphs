module

public import DraismaVargas.LocalCases.M11JoinedBackground
public import DraismaVargas.LocalCases.StableSourceMatrix

@[expose] public section

/-!
# The joined M11 new column: the third row divided by two plus background

Separate the single distinguished index-two occurrence from the literal
row-filtered new fibre. Everything remaining belongs to a different old wall
block; no background contribution is dropped. `M11JoinedBackground` proves
that those occurrences have the same pruning status, surviving stable row,
and index as the corresponding retained old occurrences.

This is the natural-source-matrix decomposition behind Figure 32's
`c(e3)/2 + s`. A common-row labelling and cofactor balance are not assumed.
-/

namespace DraismaVargas.LocalCases.M11JoinedColumn

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource W2R1Target SecondEquation
open M11SourceCandidates M11SplitRows M11JoinedGeometry M11JoinedSurvival

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

/-- The actual new-fibre occurrences outside the distinguished old block.
The membership theorem below proves that this erasure has exactly that meaning. -/
noncomputable def backgroundOccurrences (data : GluingDatum target degree) (star : TwoStar target wall)
    (block : WallBlock data wall) (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (path : StablePath (joinedPattern data star block hCard).candidate.datum) :
    Finset (joinedPattern data star block hCard).candidate.datum.SourceEdge := by
  classical
  exact (StableSourceMatrix.occurrences (joinedPattern data star block hCard).candidate.datum path
    (occurrenceEquiv target wall (joinedPattern data star block hCard).candidate.right none)).erase
      ((joinedPattern data star block hCard).candidate.newSourceEdge block.1)

theorem mem_backgroundOccurrences (data : GluingDatum target degree) (star : TwoStar target wall)
    (block : WallBlock data wall) (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (path : StablePath (joinedPattern data star block hCard).candidate.datum)
    (edge : (joinedPattern data star block hCard).candidate.datum.SourceEdge) :
    edge ∈ backgroundOccurrences data star block hCard path ↔
      edge ∈ StableSourceMatrix.occurrences (joinedPattern data star block hCard).candidate.datum path
          (occurrenceEquiv target wall (joinedPattern data star block hCard).candidate.right none) ∧
        ¬ (data.vertexPartition wall).Rel block.1 edge.1.2 := by
  classical
  rw [backgroundOccurrences, Finset.mem_erase]
  constructor
  · rintro ⟨hNe, hMem⟩
    refine ⟨hMem, ?_⟩
    intro hRel
    have hEqual := eq_newSourceEdge_of_target (joinedPattern data star block hCard).candidate edge
      ((StableSourceMatrix.mem_occurrences _ _ _).mp hMem).2
    exact hNe (hEqual.trans (newSourceEdge_eq_of_rel data star block hCard _ _ hRel.symm))
  · rintro ⟨hMem, hBackground⟩
    refine ⟨?_, hMem⟩
    intro hEqual
    have hNew := eq_newSourceEdge_of_target (joinedPattern data star block hCard).candidate edge
      ((StableSourceMatrix.mem_occurrences _ _ _).mp hMem).2
    exact hBackground ((newSourceEdge_eq_iff_rel data star block hCard _ _).mp (hEqual.symm.trans hNew))

/-- The source's residual term, before transporting all candidates to a
common row type: sum exactly the surviving new background occurrences. -/
noncomputable def backgroundColumn (data : GluingDatum target degree) (star : TwoStar target wall)
    (block : WallBlock data wall) (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (path : StablePath (joinedPattern data star block hCard).candidate.datum) : ℚ :=
  ∑ edge ∈ backgroundOccurrences data star block hCard path,
    (1 : ℚ) / (joinedPattern data star block hCard).candidate.datum.sourceEdgeIndex edge

theorem distinguished_mem_occurrences_iff (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (path : StablePath (joinedPattern data star block hCard).candidate.datum) :
    (joinedPattern data star block hCard).candidate.newSourceEdge block.1 ∈
        StableSourceMatrix.occurrences (joinedPattern data star block hCard).candidate.datum path
          (occurrenceEquiv target wall (joinedPattern data star block hCard).candidate.right none) ↔
      path = (joined_retainedSingle input profile hCard).stablePath := by
  rw [StableSourceMatrix.mem_occurrences]
  constructor
  · rintro ⟨⟨hSurvives, hRow⟩, _⟩
    exact hRow.symm.trans (joined_distinguished_stablePath_eq input profile hCard)
  · intro hRow
    exact ⟨⟨joined_distinguished_survives input profile hCard,
      (joined_distinguished_stablePath_eq input profile hCard).trans hRow.symm⟩, rfl⟩

/-- The joined candidate's literal new column, retaining every background
contribution and counting the distinguished index-two occurrence only once. -/
theorem joined_matrix_new_column (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (path : StablePath (joinedPattern data star block hCard).candidate.datum) :
    StableSourceMatrix.matrix (joinedPattern data star block hCard).candidate.datum path
        (occurrenceEquiv target wall (joinedPattern data star block hCard).candidate.right none) =
      (if path = (joined_retainedSingle input profile hCard).stablePath then (1 / 2 : ℚ) else 0) +
        backgroundColumn data star block hCard path := by
  classical
  let candidate := (joinedPattern data star block hCard).candidate
  let occurrences := StableSourceMatrix.occurrences candidate.datum path
    (occurrenceEquiv target wall candidate.right none)
  have hIndex : candidate.datum.sourceEdgeIndex (candidate.newSourceEdge block.1) = 2 :=
    (joined_newSourceEdge_index data star block hCard block.1).trans hCard
  by_cases hRow : path = (joined_retainedSingle input profile hCard).stablePath
  · have hMem : candidate.newSourceEdge block.1 ∈ occurrences :=
      (distinguished_mem_occurrences_iff input profile hCard path).mpr hRow
    have hSum := Finset.sum_erase_add occurrences
      (fun edge ↦ (1 : ℚ) / candidate.datum.sourceEdgeIndex edge) hMem
    change backgroundColumn data star block hCard path +
      (1 : ℚ) / candidate.datum.sourceEdgeIndex (candidate.newSourceEdge block.1) =
      StableSourceMatrix.matrix candidate.datum path (occurrenceEquiv target wall candidate.right none) at hSum
    rw [hIndex] at hSum
    rw [ite_eq_left hRow]
    exact hSum.symm.trans (add_comm _ _)
  · have hNot : candidate.newSourceEdge block.1 ∉ occurrences :=
      fun h ↦ hRow ((distinguished_mem_occurrences_iff input profile hCard path).mp h)
    have hErase := Finset.erase_eq_of_notMem hNot
    rw [ite_eq_right hRow, zero_add]
    change (∑ edge ∈ occurrences, (1 : ℚ) / candidate.datum.sourceEdgeIndex edge) =
      ∑ edge ∈ occurrences.erase (candidate.newSourceEdge block.1), (1 : ℚ) / candidate.datum.sourceEdgeIndex edge
    rw [hErase]

end DraismaVargas.LocalCases.M11JoinedColumn
