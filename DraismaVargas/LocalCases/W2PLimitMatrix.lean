module

public import DraismaVargas.LocalCases.W2PRowDescent
public import DraismaVargas.LocalCases.W2PCommonBalance

@[expose] public section

/-!
# Figure 35's limit matrices, and an inhabitant of `LimitColumns`

Source: Draisma--Vargas Part I, case `{w2-r2-nd3-P}`, Figure 35 and
Equation (9).

This module supplies an inhabitant of `W2PCommonBalance.LimitColumns`, on
every datum of the case: the row field is
`W2PRowDescent.stablePathEquiv`, the retained field is `matrix_retained`, and
the regrown field is the three evaluations `firstMember_regrown`,
`secondMember_regrown`, `thirdMember_regrown` of Figure 35's boxes.

The retained columns, the split of the regrown column into its selected half
and Figure 35's `s`, and the selected half's two readers are the core's
(`LimitChainCore.SelectedData.matrix_retained`, `matrix_new_split`,
`selected_set`, `selected_set_of_dangling`), read on `W2PStableLift.selectedData`;
`W2PCommonBalance.backgroundColumn` is the core's `backgroundColumn` by
definition.
-/

namespace DraismaVargas.LocalCases.W2PLimitMatrix

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open StableSourceMatrix
open ResolutionM11 GlobalM11Arbitrary
open ResolutionAwayFromWall
open W2PSourceCandidates
open W2PSurvival W2PStableLift W2PRowDescent

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-! ## The retained columns -/

/-- Exact retained-column occurrence dictionary, including the actual old
stable class.  Injectivity of the geometric row map is essential here. -/
theorem occurrences_retained (input : W2SourceInput data star) {member : MemberShape profile}
    (census : Census input member) (path : StablePath data) (place : target.edges) :
    occurrences member.candidate.datum (stablePathEquiv input census path)
        (occurrenceEquiv target wall member.candidate.right (some place)) =
      (occurrences data path place).image member.candidate.oldSourceEdge :=
  (selectedData input census).occurrences_retained path place

/-- **Every retained column is literally the incoming wall column**, read
through the proved geometric row bijection. -/
theorem matrix_retained (input : W2SourceInput data star) {member : MemberShape profile}
    (census : Census input member) (path : StablePath data) (place : target.edges) :
    matrix member.candidate.datum (stablePathEquiv input census path)
        (occurrenceEquiv target wall member.candidate.right (some place)) =
      matrix data path place :=
  (selectedData input census).matrix_retained path place


/-! ## The regrown column -/

/-- The regrown column's occurrence set of one member, read in the incoming
row. -/
noncomputable def newOccurrences (input : W2SourceInput data star) {member : MemberShape profile}
    (census : Census input member) (path : StablePath data) :
    Finset member.candidate.datum.SourceEdge :=
  (selectedData input census).newOccurrences path

theorem new_mem_iff_of_survives (input : W2SourceInput data star) {member : MemberShape profile}
    (census : Census input member) (sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel block.1 sheet)
    (hSurvives : ¬ IsDangling member.candidate.datum (member.candidate.newSourceEdge sheet))
    (path : StablePath data) :
    member.candidate.newSourceEdge sheet ∈ newOccurrences input census path ↔
      path = (census.rep sheet).stablePath :=
  (selectedData input census).new_mem_iff_of_survives sheet hRel hSurvives path

theorem new_not_mem_of_dangling (input : W2SourceInput data star) {member : MemberShape profile}
    (census : Census input member) (sheet : Fin degree)
    (hDangling : IsDangling member.candidate.datum (member.candidate.newSourceEdge sheet))
    (path : StablePath data) :
    member.candidate.newSourceEdge sheet ∉ newOccurrences input census path :=
  (selectedData input census).new_not_mem_of_dangling sheet hDangling path

/-- Figure 35's `s` is the core's background column of the `t₂` direction. -/
theorem backgroundColumn_eq (path : StablePath data) (label : Fin 2) :
    LimitChainCore.backgroundColumn data wall block.1 path (star.edge label) =
      W2PCommonBalance.backgroundColumn star block path label := rfl

/-- **The background half of the regrown column is Figure 35's `s`.**  Every
old `t₂` occurrence outside `A₀` is matched with the regrown occurrence of its
own wall block, in the same row and with the same index. -/
theorem background_sum (input : W2SourceInput data star) {member : MemberShape profile}
    (census : Census input member) (path : StablePath data) :
    ∑ edge ∈ (newOccurrences input census path).filter
        (fun edge ↦ ¬ (data.vertexPartition wall).Rel block.1 edge.1.2),
      (1 : ℚ) / member.candidate.datum.sourceEdgeIndex edge =
    W2PCommonBalance.backgroundColumn star block path profile.doubleLabel :=
  ((selectedData input census).background_sum path).trans
    (backgroundColumn_eq path profile.doubleLabel)

/-- The two regrown occurrences above `A₀`, named by their anchors. -/
theorem selected_set (input : W2SourceInput data star) {member : MemberShape profile}
    (census : Census input member) (first second : Fin degree)
    (hFirst : (data.vertexPartition wall).Rel block.1 first)
    (hSecond : (data.vertexPartition wall).Rel block.1 second)
    (hCover : ∀ sheet : Fin degree, (data.vertexPartition wall).Rel block.1 sheet →
      member.fine.Rel first sheet ∨ member.fine.Rel second sheet)
    (path : StablePath data) :
    (newOccurrences input census path).filter
        (fun edge ↦ (data.vertexPartition wall).Rel block.1 edge.1.2) =
      ({member.candidate.newSourceEdge first, member.candidate.newSourceEdge second} :
        Finset member.candidate.datum.SourceEdge).filter
        (fun edge ↦ edge ∈ newOccurrences input census path) :=
  (selectedData input census).selected_set first second hFirst hSecond
    (fun sheet hRel ↦ by
      rcases hCover sheet hRel with h | h
      · exact Or.inl ((member.newSourceEdge_eq_iff_fine sheet first hRel).mpr h.symm)
      · exact Or.inr ((member.newSourceEdge_eq_iff_fine sheet second hRel).mpr h.symm))
    path

/-- **The regrown column, split into Figure 35's two halves.** -/
theorem matrix_new_split (input : W2SourceInput data star) {member : MemberShape profile}
    (census : Census input member) (path : StablePath data) :
    matrix member.candidate.datum (stablePathEquiv input census path)
        (occurrenceEquiv target wall member.candidate.right none) =
      (∑ edge ∈ (newOccurrences input census path).filter
          (fun edge ↦ (data.vertexPartition wall).Rel block.1 edge.1.2),
        (1 : ℚ) / member.candidate.datum.sourceEdgeIndex edge) +
        W2PCommonBalance.backgroundColumn star block path profile.doubleLabel :=
  (selectedData input census).matrix_new_split path

/-- The regrown occurrences above `A₀` when one of the two is pruned. -/
theorem selected_set_of_dangling (input : W2SourceInput data star) {member : MemberShape profile}
    (census : Census input member) (first second : Fin degree)
    (hFirst : (data.vertexPartition wall).Rel block.1 first)
    (hCover : ∀ sheet : Fin degree, (data.vertexPartition wall).Rel block.1 sheet →
      member.fine.Rel first sheet ∨ member.fine.Rel second sheet)
    (hDangling : IsDangling member.candidate.datum (member.candidate.newSourceEdge second))
    (path : StablePath data) :
    (newOccurrences input census path).filter
        (fun edge ↦ (data.vertexPartition wall).Rel block.1 edge.1.2) =
      ({member.candidate.newSourceEdge first} :
        Finset member.candidate.datum.SourceEdge).filter
        (fun edge ↦ edge ∈ newOccurrences input census path) :=
  (selectedData input census).selected_set_of_dangling first second hFirst
    (fun sheet hRel ↦ by
      rcases hCover sheet hRel with h | h
      · exact Or.inl ((member.newSourceEdge_eq_iff_fine sheet first hRel).mpr h.symm)
      · exact Or.inr ((member.newSourceEdge_eq_iff_fine sheet second hRel).mpr h.symm))
    hDangling path

theorem firstMember_regrown (shape : Shape profile) (input : W2SourceInput data star)
    (path : StablePath data) :
    matrix (firstShape shape).candidate.datum
        (stablePathEquiv input (firstCensus shape input) path)
        (occurrenceEquiv target wall (firstShape shape).candidate.right none) =
      W2PCommonBalance.firstNewColumn profile path := by
  classical
  have hFirstRel := firstSheet_rel profile
  have hSecondRel := secondSheet_rel profile
  have hSurvFirst : ¬ IsDangling (firstShape shape).candidate.datum
      ((firstShape shape).candidate.newSourceEdge (firstSheet profile)) :=
    mergeShape_new_own_survives shape input profile.first profile.first_target
      profile.first_survives (first_extra_separate shape)
  have hSurvSecond : ¬ IsDangling (firstShape shape).candidate.datum
      ((firstShape shape).candidate.newSourceEdge (secondSheet profile)) :=
    mergeShape_new_other_survives input profile.first profile.second profile.second_target
      profile.second_survives (first_extra_separate shape) (second_extra_separate shape)
      (first_second_separate profile)
  have hNe : (firstShape shape).candidate.newSourceEdge (firstSheet profile) ≠
      (firstShape shape).candidate.newSourceEdge (secondSheet profile) := fun h ↦
    mergeShape_fine_not_rel profile.first profile.second (first_extra_separate shape)
      (second_extra_separate shape) (first_second_separate profile)
      (((firstShape shape).newSourceEdge_eq_iff_fine (firstSheet profile) (secondSheet profile)
        hFirstRel).mp h)
  have hIdxFirst : (firstShape shape).fine.blockCard (firstSheet profile) =
      data.sourceEdgeIndex profile.first.1 + 1 := (firstMember_indices shape).1
  have hIdxSecond : (firstShape shape).fine.blockCard (secondSheet profile) =
      data.sourceEdgeIndex profile.second.1 := (firstMember_indices shape).2
  have hMemFirst : ((firstShape shape).candidate.newSourceEdge (firstSheet profile) ∈
      newOccurrences input (firstCensus shape input) path) ↔
        path = W2PCommonBalance.firstRow profile := by
    rw [new_mem_iff_of_survives input (firstCensus shape input) (firstSheet profile) hFirstRel
      hSurvFirst path, firstCensus_rep_first shape input]
    rfl
  have hMemSecond : ((firstShape shape).candidate.newSourceEdge (secondSheet profile) ∈
      newOccurrences input (firstCensus shape input) path) ↔
        path = W2PCommonBalance.secondRow profile := by
    rw [new_mem_iff_of_survives input (firstCensus shape input) (secondSheet profile) hSecondRel
      hSurvSecond path, firstCensus_rep_second shape input]
    rfl
  rw [matrix_new_split input (firstCensus shape input) path,
    selected_set input (firstCensus shape input) (firstSheet profile) (secondSheet profile)
      hFirstRel hSecondRel (mergeShape_fine_cover profile.first profile.second
        (first_extra_separate shape) (endpointPartition_covers shape)) path,
    Finset.sum_filter, Finset.sum_pair hNe,
    (firstShape shape).newSourceEdge_index_of_rel (firstSheet profile) hFirstRel,
    (firstShape shape).newSourceEdge_index_of_rel (secondSheet profile) hSecondRel,
    hIdxFirst, hIdxSecond]
  simp only [hMemFirst, hMemSecond, W2PCommonBalance.firstNewColumn]
  split_ifs <;> push_cast <;> ring

/-- **`c⁽²⁾ = c(e₁)/k₁ + c(e₂)/(k₂+1) + s`.** -/
theorem secondMember_regrown (shape : Shape profile) (input : W2SourceInput data star)
    (path : StablePath data) :
    matrix (secondShape shape).candidate.datum
        (stablePathEquiv input (secondCensus shape input) path)
        (occurrenceEquiv target wall (secondShape shape).candidate.right none) =
      W2PCommonBalance.secondNewColumn profile path := by
  classical
  have hFirstRel := firstSheet_rel profile
  have hSecondRel := secondSheet_rel profile
  have hSurvSecond : ¬ IsDangling (secondShape shape).candidate.datum
      ((secondShape shape).candidate.newSourceEdge (secondSheet profile)) :=
    mergeShape_new_own_survives shape input profile.second profile.second_target
      profile.second_survives (second_extra_separate shape)
  have hSurvFirst : ¬ IsDangling (secondShape shape).candidate.datum
      ((secondShape shape).candidate.newSourceEdge (firstSheet profile)) :=
    mergeShape_new_other_survives input profile.second profile.first profile.first_target
      profile.first_survives (second_extra_separate shape) (first_extra_separate shape)
      (fun h ↦ first_second_separate profile h.symm)
  have hNe : (secondShape shape).candidate.newSourceEdge (secondSheet profile) ≠
      (secondShape shape).candidate.newSourceEdge (firstSheet profile) := fun h ↦
    mergeShape_fine_not_rel profile.second profile.first (second_extra_separate shape)
      (first_extra_separate shape) (fun h' ↦ first_second_separate profile h'.symm)
      (((secondShape shape).newSourceEdge_eq_iff_fine (secondSheet profile) (firstSheet profile)
        hSecondRel).mp h)
  have hIdxSecond : (secondShape shape).fine.blockCard (secondSheet profile) =
      data.sourceEdgeIndex profile.second.1 + 1 := (secondMember_indices shape).1
  have hIdxFirst : (secondShape shape).fine.blockCard (firstSheet profile) =
      data.sourceEdgeIndex profile.first.1 := (secondMember_indices shape).2
  have hMemSecond : ((secondShape shape).candidate.newSourceEdge (secondSheet profile) ∈
      newOccurrences input (secondCensus shape input) path) ↔
        path = W2PCommonBalance.secondRow profile := by
    rw [new_mem_iff_of_survives input (secondCensus shape input) (secondSheet profile) hSecondRel
      hSurvSecond path, secondCensus_rep_second shape input]
    rfl
  have hMemFirst : ((secondShape shape).candidate.newSourceEdge (firstSheet profile) ∈
      newOccurrences input (secondCensus shape input) path) ↔
        path = W2PCommonBalance.firstRow profile := by
    rw [new_mem_iff_of_survives input (secondCensus shape input) (firstSheet profile) hFirstRel
      hSurvFirst path, secondCensus_rep_first shape input]
    rfl
  rw [matrix_new_split input (secondCensus shape input) path,
    selected_set input (secondCensus shape input) (secondSheet profile) (firstSheet profile)
      hSecondRel hFirstRel (mergeShape_fine_cover profile.second profile.first
        (second_extra_separate shape) (fun sheet hSheet ↦ by
          rcases endpointPartition_covers shape sheet hSheet with h | h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h))) path,
    Finset.sum_filter, Finset.sum_pair hNe,
    (secondShape shape).newSourceEdge_index_of_rel (secondSheet profile) hSecondRel,
    (secondShape shape).newSourceEdge_index_of_rel (firstSheet profile) hFirstRel,
    hIdxSecond, hIdxFirst]
  simp only [hMemFirst, hMemSecond, W2PCommonBalance.secondNewColumn]
  split_ifs <;> push_cast <;> ring

/-- **`c⁽³⁾ = c(e₃)/(k₁+k₂) + s`**: the dangling singleton contributes nothing. -/
theorem thirdMember_regrown (shape : Shape profile) (input : W2SourceInput data star)
    (path : StablePath data) :
    matrix (thirdShape shape).candidate.datum
        (stablePathEquiv input (thirdCensus shape input) path)
        (occurrenceEquiv target wall (thirdShape shape).candidate.right none) =
      W2PCommonBalance.thirdNewColumn profile path := by
  classical
  have hFirstRel := firstSheet_rel profile
  have hSurvFirst := thirdShape_new_first_survives shape input
  have hIdxFirst : (thirdShape shape).fine.blockCard (firstSheet profile) =
      data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 :=
    (thirdMember_indices shape).1
  have hMemFirst : ((thirdShape shape).candidate.newSourceEdge (firstSheet profile) ∈
      newOccurrences input (thirdCensus shape input) path) ↔
        path = W2PCommonBalance.thirdRow profile := by
    rw [new_mem_iff_of_survives input (thirdCensus shape input) (firstSheet profile) hFirstRel
      hSurvFirst path, thirdCensus_rep shape input]
    rfl
  rw [matrix_new_split input (thirdCensus shape input) path,
    selected_set_of_dangling input (thirdCensus shape input) (firstSheet profile)
      (extraSheet profile) hFirstRel (thirdShape_fine_cover shape)
      (thirdShape_new_extra_dangles shape input) path,
    Finset.sum_filter, Finset.sum_singleton,
    (thirdShape shape).newSourceEdge_index_of_rel (firstSheet profile) hFirstRel, hIdxFirst]
  simp only [hMemFirst, W2PCommonBalance.thirdNewColumn]
  split_ifs <;> push_cast <;> ring

/-! ## The inhabitant -/

/-- The three members' geometric stable-row bijections, indexed.  The member
implicits are pinned: without them the elaborator solves `?member.candidate`
against `members profile shape 0` by unfolding both candidates. -/
noncomputable def rowEquiv (input : W2SourceInput data star) (shape : Shape profile) :
    ∀ position : Fin 3,
      StablePath data ≃ StablePath (W2PCommonBalance.members profile shape position).datum :=
  Fin.cases (n := 2) (motive := fun position ↦ StablePath data ≃
      StablePath (W2PCommonBalance.members profile shape position).datum)
    (stablePathEquiv (member := firstShape shape) input (firstCensus shape input))
    (Fin.cases (n := 1) (motive := fun i : Fin 2 ↦ StablePath data ≃
        StablePath (W2PCommonBalance.members profile shape i.succ).datum)
      (stablePathEquiv (member := secondShape shape) input (secondCensus shape input))
      (Fin.cases (n := 0) (motive := fun j : Fin 1 ↦ StablePath data ≃
          StablePath (W2PCommonBalance.members profile shape j.succ.succ).datum)
        (stablePathEquiv (member := thirdShape shape) input (thirdCensus shape input))
        (fun k ↦ k.elim0)))

@[simp] theorem rowEquiv_zero (input : W2SourceInput data star) (shape : Shape profile) :
    rowEquiv input shape 0 = stablePathEquiv input (firstCensus shape input) := rfl

@[simp] theorem rowEquiv_one (input : W2SourceInput data star) (shape : Shape profile) :
    rowEquiv input shape 1 = stablePathEquiv input (secondCensus shape input) := rfl

@[simp] theorem rowEquiv_two (input : W2SourceInput data star) (shape : Shape profile) :
    rowEquiv input shape 2 = stablePathEquiv input (thirdCensus shape input) := rfl

/-- **`W2PCommonBalance.LimitColumns` is inhabited.**  The row field is the
proved geometric bijection, the retained field is `matrix_retained`, and the
regrown field is Figure 35's three boxes. -/
noncomputable def limitColumns (input : W2SourceInput data star) (shape : Shape profile) :
    W2PCommonBalance.LimitColumns profile shape where
  row := rowEquiv input shape
  retained := by
    intro position path place
    fin_cases position
    · exact matrix_retained (member := firstShape shape) input (firstCensus shape input) path place
    · exact matrix_retained (member := secondShape shape) input (secondCensus shape input) path
        place
    · exact matrix_retained (member := thirdShape shape) input (thirdCensus shape input) path place
  regrown := by
    intro position path
    fin_cases position
    · exact firstMember_regrown shape input path
    · exact secondMember_regrown shape input path
    · exact thirdMember_regrown shape input path

/-- **Non-vacuity.**  Every actual case-P datum carrying a `Shape` inhabits
`W2PCommonBalance.LimitColumns`, so nothing downstream of it is vacuous. -/
theorem nonempty_limitColumns (input : W2SourceInput data star) (shape : Shape profile) :
    Nonempty (W2PCommonBalance.LimitColumns profile shape) :=
  ⟨limitColumns input shape⟩


/-! ## Consequences -/

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

noncomputable local instance : DecidableEq (Option target.edges) := Classical.decEq _

/-- **Equation (9) for Figure 35's three actual members, unconditionally.**
`W2PCommonBalance.LimitColumns.canonical_determinant_balance` is stated there
for an arbitrary inhabitant; here the inhabitant is supplied. -/
theorem canonical_determinant_balance (input : W2SourceInput data star)
    (shape : Shape profile) :
    ((data.sourceEdgeIndex profile.first.1 : ℚ) + 1) *
          ((limitColumns input shape).canonicalMatrix input 0).det +
        ((data.sourceEdgeIndex profile.second.1 : ℚ) + 1) *
          ((limitColumns input shape).canonicalMatrix input 1).det +
        ((data.sourceEdgeIndex profile.first.1 : ℚ) +
            (data.sourceEdgeIndex profile.second.1 : ℚ)) *
          ((limitColumns input shape).canonicalMatrix input 2).det = 0 :=
  (limitColumns input shape).canonical_determinant_balance input

/-- The honest presented family of Figure 35's three members, unconditionally. -/
noncomputable def canonicalPresentedFamily (input : W2SourceInput data star)
    (shape : Shape profile) :
    BalancedGlobal.PresentedFamily (coordinate := Option target.edges) 3 data wall :=
  (limitColumns input shape).canonicalPresentedFamily input

theorem canonicalPresentedFamily_candidate (input : W2SourceInput data star)
    (shape : Shape profile) (position : Fin 3) :
    (canonicalPresentedFamily input shape).candidate position =
      W2PCommonBalance.members profile shape position := rfl

end DraismaVargas.LocalCases.W2PLimitMatrix
