import DraismaVargas.LocalCases.W2MkkRowDescent

/-!
# Figure 34's limit matrices

Source: Draisma--Vargas Part I, Case {w2-r2-nd3-M-kk} (abbreviated M-kk),
Figure 34 and Equation (8).

The retained columns, the split of the regrown column into its selected half
and Figure 34's `s`, and the readers of the selected half are the core's
(`LimitChainCore.SelectedData.matrix_retained`, `matrix_new_split`,
`new_mem_iff_of_survives`, `new_not_mem_of_dangling`), read on
`W2MkkStableLift`'s `detachSelectedData` and `joinedSelectedData`.  On top of
them this module evaluates **Figure 34's three boxes**:

* `firstMember_regrown` — `c⁽¹⁾ = c(e₁)/(k₁-1) + c(e₂)/k₂ + s`;
* `secondMember_regrown` — `c⁽²⁾ = c(e₁)/k₁ + c(e₂)/(k₂-1) + s`;
* `thirdMember_regrown` — `c⁽³⁾ = c(e₃)/(k₁+k₂) + s`,

with the indices `W2MkkSourceCandidates.detach_indices_first`,
`detach_indices_second` and `joined_newEdge_blockCard` display.  `s` is the
core's own `LimitChainCore.backgroundColumn data wall block.1 path
(star.edge profile.doubleLabel)`; `W2MkkCommonBalance` meets it by `rfl`,
exactly as `W2PLimitMatrix.backgroundColumn_eq` does for Figure 35.

## One extension of the core's selected-set readers

`LimitChainCore.SelectedData.selected_set` covers two regrown classes above
the distinguished block and `selected_set_of_dangling` covers two of which the
second is pruned.  A **detaching** M-kk member has **three** classes above `A₀`
— `A_p ∖ {x}`, `A_q` and the singleton `{x}` — of which exactly the singleton
is pruned (`W2MkkStableGraph.detach_new_pin_dangling`).  So one more reader is
needed, `selected_set_of_dangling_third`, proved below from the core's own
`eq_newSourceEdge_of_mem`, `newSourceEdge_sheet_rel_iff` and
`new_not_mem_of_dangling` and stated for an arbitrary `SelectedData`.  Like
`selected_set_single`, which `M⁽³⁾` needs (one class above `A₀`), it is a
generic fact about `SelectedData`, of the same kind as
`LimitChainCore.SelectedData.selected_set_of_dangling`.

## The three members

`M⁽¹⁾` and `M⁽²⁾` are the *same* uniform object, `DetachData.candidate`, and
`detach_regrown` is proved once for it, with the two surviving regrown classes
named by `detach.remainder` (the pinned endpoint block minus `x`) and
`W2MkkStableGraph.otherSheet` (the other endpoint block).  Which of the two
figures a datum displays is decided by where the pinned sheet sits, and that is
all `firstMember_regrown` and `secondMember_regrown` add:
`W2MkkSourceCandidates.detach_indices_first` and its mirror turn the two class
sizes into `k₁-1, k₂` or `k₁, k₂-1`, and
`W2MkkSourceCandidates.endpointPartition_covers` turns the two representatives
into `e₁` and `e₂`.  Member 2 over the branch-swapped datum is obtained by
instantiating the *same* theorems there; nothing is transported.

## What is not here

The `LimitColumns`-style receipt of Equation (8) and the common balance
(Equation (8) itself) belong to `W2MkkCommonBalance`, which this
module deliberately does not import.
-/

namespace DraismaVargas.LocalCases.W2MkkLimitMatrix

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open StableSourceMatrix
open ResolutionM11 GlobalM11Arbitrary
open ResolutionAwayFromWall
open W2MkkSourceCandidates
open W2MkkStableGraph
open W2MkkStableLift W2MkkRowDescent

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-! ## Two more readers of the selected half of a regrown column

Both belong in `LimitChainCore` beside `selected_set_of_dangling`; they are
stated here for an arbitrary `SelectedData` and use only its public API. -/

/-- **Three regrown classes above the distinguished block, the third pruned.**
This is what a detaching M-kk member needs: `A_p ∖ {x}`, `A_q`, and the
singleton `{x}` whose regrown occurrence dies with `e₄`. -/
theorem selected_set_of_dangling_third (rd : LimitChainCore.SelectedData data wall)
    (first second third : Fin degree)
    (hFirst : (data.vertexPartition wall).Rel rd.selected first)
    (hSecond : (data.vertexPartition wall).Rel rd.selected second)
    (hCover : ∀ sheet : Fin degree, (data.vertexPartition wall).Rel rd.selected sheet →
      rd.candidate.newSourceEdge sheet = rd.candidate.newSourceEdge first ∨
        rd.candidate.newSourceEdge sheet = rd.candidate.newSourceEdge second ∨
          rd.candidate.newSourceEdge sheet = rd.candidate.newSourceEdge third)
    (hDangling : IsDangling rd.candidate.datum (rd.candidate.newSourceEdge third))
    (path : StablePath data) :
    (rd.newOccurrences path).filter
        (fun edge ↦ (data.vertexPartition wall).Rel rd.selected edge.1.2) =
      ({rd.candidate.newSourceEdge first, rd.candidate.newSourceEdge second} :
        Finset rd.candidate.datum.SourceEdge).filter
        (fun edge ↦ edge ∈ rd.newOccurrences path) := by
  classical
  ext edge
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hMem, hRel⟩
    refine ⟨?_, hMem⟩
    have hEdgeNew := rd.eq_newSourceEdge_of_mem path edge hMem
    rcases hCover edge.1.2 hRel with h | h | h
    · exact Or.inl (hEdgeNew.trans h)
    · exact Or.inr (hEdgeNew.trans h)
    · exact absurd (rd.new_not_mem_of_dangling third hDangling path)
        (fun hNot ↦ hNot (by rwa [← h, ← hEdgeNew]))
  · rintro ⟨hEq, hMem⟩
    refine ⟨hMem, ?_⟩
    rcases hEq with rfl | rfl
    · exact (rd.newSourceEdge_sheet_rel_iff first).mpr hFirst
    · exact (rd.newSourceEdge_sheet_rel_iff second).mpr hSecond

/-- **One regrown class above the distinguished block.**  This is what `M⁽³⁾`
needs: it keeps the whole wall block along the new edge. -/
theorem selected_set_single (rd : LimitChainCore.SelectedData data wall) (first : Fin degree)
    (hFirst : (data.vertexPartition wall).Rel rd.selected first)
    (hCover : ∀ sheet : Fin degree, (data.vertexPartition wall).Rel rd.selected sheet →
      rd.candidate.newSourceEdge sheet = rd.candidate.newSourceEdge first)
    (path : StablePath data) :
    (rd.newOccurrences path).filter
        (fun edge ↦ (data.vertexPartition wall).Rel rd.selected edge.1.2) =
      ({rd.candidate.newSourceEdge first} :
        Finset rd.candidate.datum.SourceEdge).filter
        (fun edge ↦ edge ∈ rd.newOccurrences path) := by
  classical
  ext edge
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hMem, hRel⟩
    exact ⟨(rd.eq_newSourceEdge_of_mem path edge hMem).trans (hCover edge.1.2 hRel), hMem⟩
  · rintro ⟨rfl, hMem⟩
    exact ⟨hMem, (rd.newSourceEdge_sheet_rel_iff first).mpr hFirst⟩

/-! ## The three incoming stable rows Figure 34 names -/

/-- The stable row of `e₁`. -/
noncomputable def firstRow (profile : W2R2SourceProfile.SourceProfile data star block) :
    StablePath data :=
  NonDanglingEdge.stablePath ⟨profile.first.1, profile.first_survives⟩

/-- The stable row of `e₂`. -/
noncomputable def secondRow (profile : W2R2SourceProfile.SourceProfile data star block) :
    StablePath data :=
  NonDanglingEdge.stablePath ⟨profile.second.1, profile.second_survives⟩

/-- The stable row of `e₃`. -/
noncomputable def thirdRow (profile : W2R2SourceProfile.SourceProfile data star block) :
    StablePath data :=
  NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩

/-! ## The `t₂` occurrences above `A₀`, named by their sheets -/

/-- `e₁` is the `t₂` occurrence through its own sheet. -/
theorem sourceEdge_double_first (profile : W2R2SourceProfile.SourceProfile data star block) :
    data.sourceEdge (star.edge profile.doubleLabel) (firstSheet profile) = profile.first.1 := by
  have h := GluingDatum.sourceEdge_self data profile.first.1
  rw [profile.first_target] at h
  exact h

/-- `e₂` is the `t₂` occurrence through its own sheet. -/
theorem sourceEdge_double_second (profile : W2R2SourceProfile.SourceProfile data star block) :
    data.sourceEdge (star.edge profile.doubleLabel) (secondSheet profile) = profile.second.1 := by
  have h := GluingDatum.sourceEdge_self data profile.second.1
  rw [profile.second_target] at h
  exact h

/-- Sheets of one `t₂` occurrence name that occurrence. -/
theorem sourceEdge_double_congr (profile : W2R2SourceProfile.SourceProfile data star block)
    {first second : Fin degree} (hRel : (endpointPartition profile).Rel first second) :
    data.sourceEdge (star.edge profile.doubleLabel) first =
      data.sourceEdge (star.edge profile.doubleLabel) second :=
  (LimitChainCore.sourceEdge_eq_iff_rel data _ first second).mpr hRel

/-- **The endpoint block that does not carry the pinned sheet tiles what is
left of `A₀`.**  `e₁`, `e₂` tile `A₀` and the pinned sheet lies in exactly one
of them, so every sheet outside the pinned block lies in `otherSheet`'s. -/
theorem otherSheet_covers (shape : Shape profile) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet)
    (hNot : ¬ (endpointPartition profile).Rel (pinSheet profile) sheet) :
    (endpointPartition profile).Rel (otherSheet profile) sheet := by
  classical
  by_cases hFirst : (endpointPartition profile).Rel (firstSheet profile) (pinSheet profile)
  · have hOther : otherSheet profile = secondSheet profile := by
      simp only [otherSheet, hFirst, ↓reduceIte]
    rw [hOther]
    rcases endpointPartition_covers shape sheet hSheet with h | h
    · exact absurd (hFirst.symm.trans h) hNot
    · exact h
  · have hOther : otherSheet profile = firstSheet profile := by
      simp only [otherSheet, hFirst, ↓reduceIte]
    rw [hOther]
    rcases endpointPartition_covers shape sheet hSheet with h | h
    · exact h
    · rcases pinSheet_mem shape with hPin | hPin
      · exact absurd hPin hFirst
      · exact absurd (hPin.symm.trans h) hNot

/-! ## The retained columns -/

/-- Exact retained-column occurrence dictionary of a detaching member,
including the actual old stable class. -/
theorem detach_occurrences_retained (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (path : StablePath data) (place : target.edges) :
    occurrences (detach.candidate shape).datum (detachStablePathEquiv input shape detach path)
        (occurrenceEquiv target wall (detach.candidate shape).right (some place)) =
      (occurrences data path place).image (detach.candidate shape).oldSourceEdge :=
  (detachSelectedData input shape detach).occurrences_retained path place

/-- **Every retained column of a detaching member is literally the incoming
wall column**, read through the proved geometric row bijection. -/
theorem detach_matrix_retained (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (path : StablePath data) (place : target.edges) :
    matrix (detach.candidate shape).datum (detachStablePathEquiv input shape detach path)
        (occurrenceEquiv target wall (detach.candidate shape).right (some place)) =
      matrix data path place :=
  (detachSelectedData input shape detach).matrix_retained path place

theorem joined_occurrences_retained (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) (path : StablePath data) (place : target.edges) :
    occurrences (joinedCandidate profile distinguished).datum
        (joinedStablePathEquiv input shape distinguished path)
        (occurrenceEquiv target wall (joinedCandidate profile distinguished).right (some place)) =
      (occurrences data path place).image
        (joinedCandidate profile distinguished).oldSourceEdge :=
  (joinedSelectedData input shape distinguished).occurrences_retained path place

/-- **Every retained column of `M⁽³⁾` is literally the incoming wall
column.** -/
theorem joined_matrix_retained (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) (path : StablePath data) (place : target.edges) :
    matrix (joinedCandidate profile distinguished).datum
        (joinedStablePathEquiv input shape distinguished path)
        (occurrenceEquiv target wall (joinedCandidate profile distinguished).right (some place)) =
      matrix data path place :=
  (joinedSelectedData input shape distinguished).matrix_retained path place

/-! ## The regrown column of a detaching member -/

/-- The regrown column's occurrence set of a detaching member, read in the
incoming row. -/
noncomputable def detachNewOccurrences (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (path : StablePath data) :
    Finset (detach.candidate shape).datum.SourceEdge :=
  (detachSelectedData input shape detach).newOccurrences path

theorem detach_new_mem_iff_of_survives (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel block.1 sheet)
    (hSurvives : ¬ IsDangling (detach.candidate shape).datum
      ((detach.candidate shape).newSourceEdge sheet))
    (path : StablePath data) :
    (detach.candidate shape).newSourceEdge sheet ∈
        detachNewOccurrences input shape detach path ↔
      path = NonDanglingEdge.stablePath
        (⟨data.sourceEdge (star.edge profile.doubleLabel) sheet,
          double_sourceEdge_survives_shape shape sheet hRel⟩ : NonDanglingEdge data) :=
  (detachSelectedData input shape detach).new_mem_iff_of_survives sheet hRel hSurvives path

theorem detach_new_not_mem_of_dangling (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (sheet : Fin degree)
    (hDangling : IsDangling (detach.candidate shape).datum
      ((detach.candidate shape).newSourceEdge sheet))
    (path : StablePath data) :
    (detach.candidate shape).newSourceEdge sheet ∉
      detachNewOccurrences input shape detach path :=
  (detachSelectedData input shape detach).new_not_mem_of_dangling sheet hDangling path

/-- **The regrown column of a detaching member, split into its two halves**: the
occurrences above `A₀`, and Figure 34's `s`. -/
theorem detach_matrix_new_split (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (path : StablePath data) :
    matrix (detach.candidate shape).datum (detachStablePathEquiv input shape detach path)
        (occurrenceEquiv target wall (detach.candidate shape).right none) =
      (∑ edge ∈ (detachNewOccurrences input shape detach path).filter
          (fun edge ↦ (data.vertexPartition wall).Rel block.1 edge.1.2),
        (1 : ℚ) / (detach.candidate shape).datum.sourceEdgeIndex edge) +
        LimitChainCore.backgroundColumn data wall block.1 path
          (star.edge profile.doubleLabel) :=
  (detachSelectedData input shape detach).matrix_new_split path

/-- The regrown index of a detaching member above `A₀` is its own detached
class size. -/
theorem detach_newSourceEdge_index (shape : Shape profile) (detach : DetachData profile)
    (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile) sheet) :
    (detach.candidate shape).datum.sourceEdgeIndex
        ((detach.candidate shape).newSourceEdge sheet) =
      detach.selected.newEdge.blockCard sheet := by
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge,
    LocalResolution.paste_newEdge_blockCard, detach_resolution shape detach _
      (hWall.trans ((data.vertexPartition wall).rel_repr_right sheet))]

/-- **The three regrown classes of a detaching member above `A₀`**: the pinned
singleton `{x}`, what is left of its endpoint block, and the other endpoint
block. -/
theorem detach_newSourceEdge_cover (shape : Shape profile) (detach : DetachData profile)
    (sheet : Fin degree) (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    (detach.candidate shape).newSourceEdge sheet =
          (detach.candidate shape).newSourceEdge detach.remainder ∨
        (detach.candidate shape).newSourceEdge sheet =
          (detach.candidate shape).newSourceEdge (otherSheet profile) ∨
      (detach.candidate shape).newSourceEdge sheet =
        (detach.candidate shape).newSourceEdge (pinSheet profile) := by
  classical
  have hWall : (data.vertexPartition wall).Rel (pinSheet profile) sheet :=
    (pinSheet_rel profile).symm.trans hSheet
  by_cases hPin : sheet = pinSheet profile
  · exact Or.inr (Or.inr (by rw [hPin]))
  by_cases hSame : (endpointPartition profile).Rel (pinSheet profile) sheet
  · refine Or.inl ((LimitChainCore.newSourceEdge_eq_iff_rel sheet detach.remainder).mpr ?_)
    refine (detach_pasted_newEdge_rel_iff shape detach sheet detach.remainder hWall).mpr ?_
    exact W3ShiftSourceCandidates.detachSheet_rel_remainder (endpointPartition profile)
      (pinSheet profile) detach.remainder sheet detach.ne_remainder detach.together hSame hPin
  · refine Or.inr (Or.inl
      ((LimitChainCore.newSourceEdge_eq_iff_rel sheet (otherSheet profile)).mpr ?_))
    refine (detach_pasted_newEdge_rel_iff shape detach sheet (otherSheet profile) hWall).mpr ?_
    rw [SheetPartition.rel_iff,
      SheetPartition.detachSheet_repr_of_not_rel (endpointPartition profile) (pinSheet profile)
        detach.remainder sheet detach.ne_remainder detach.together hSame,
      SheetPartition.detachSheet_repr_of_not_rel (endpointPartition profile) (pinSheet profile)
        detach.remainder (otherSheet profile) detach.ne_remainder detach.together
        (otherSheet_not_rel profile)]
    exact ((endpointPartition profile).rel_iff _ _).mp
      (otherSheet_covers shape sheet hSheet hSame).symm

/-- The two surviving regrown occurrences of a detaching member above `A₀`,
named by their anchors. -/
theorem detach_selected_set (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (path : StablePath data) :
    (detachNewOccurrences input shape detach path).filter
        (fun edge ↦ (data.vertexPartition wall).Rel block.1 edge.1.2) =
      ({(detach.candidate shape).newSourceEdge detach.remainder,
        (detach.candidate shape).newSourceEdge (otherSheet profile)} :
        Finset (detach.candidate shape).datum.SourceEdge).filter
        (fun edge ↦ edge ∈ detachNewOccurrences input shape detach path) :=
  selected_set_of_dangling_third (detachSelectedData input shape detach) detach.remainder
    (otherSheet profile) (pinSheet profile)
    ((pinSheet_rel profile).trans detach.wallTogether)
    ((pinSheet_rel profile).trans (otherSheet_wall_rel profile))
    (fun sheet hSheet ↦ detach_newSourceEdge_cover shape detach sheet hSheet)
    (detach_new_pin_dangling input shape detach) path

/-- **The regrown column of a detaching member, evaluated.**  Its two surviving
classes are what is left of the pinned endpoint block and the other endpoint
block; the pinned singleton contributes nothing, because its regrown occurrence
dies with `e₄`. -/
theorem detach_regrown (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (rowP rowQ : StablePath data) (indexP indexQ : ℚ)
    (hRowP : ∀ hSurvives : ¬ IsDangling data
        (data.sourceEdge (star.edge profile.doubleLabel) detach.remainder),
      NonDanglingEdge.stablePath
        (⟨data.sourceEdge (star.edge profile.doubleLabel) detach.remainder, hSurvives⟩ :
          NonDanglingEdge data) = rowP)
    (hRowQ : ∀ hSurvives : ¬ IsDangling data
        (data.sourceEdge (star.edge profile.doubleLabel) (otherSheet profile)),
      NonDanglingEdge.stablePath
        (⟨data.sourceEdge (star.edge profile.doubleLabel) (otherSheet profile), hSurvives⟩ :
          NonDanglingEdge data) = rowQ)
    (hIndexP : (detach.selected.newEdge.blockCard detach.remainder : ℚ) = indexP)
    (hIndexQ : (detach.selected.newEdge.blockCard (otherSheet profile) : ℚ) = indexQ)
    (path : StablePath data) :
    matrix (detach.candidate shape).datum (detachStablePathEquiv input shape detach path)
        (occurrenceEquiv target wall (detach.candidate shape).right none) =
      (if path = rowP then (1 : ℚ) else 0) / indexP +
        (if path = rowQ then (1 : ℚ) else 0) / indexQ +
        LimitChainCore.backgroundColumn data wall block.1 path
          (star.edge profile.doubleLabel) := by
  classical
  have hRemWall : (data.vertexPartition wall).Rel block.1 detach.remainder :=
    (pinSheet_rel profile).trans detach.wallTogether
  have hOtherWall : (data.vertexPartition wall).Rel block.1 (otherSheet profile) :=
    (pinSheet_rel profile).trans (otherSheet_wall_rel profile)
  have hRemSurvives := detach_new_survives input shape detach detach.remainder
    detach.wallTogether (Ne.symm detach.ne_remainder)
  have hOtherSurvives := detach_new_survives input shape detach (otherSheet profile)
    (otherSheet_wall_rel profile) (otherSheet_ne_pinSheet profile)
  have hNe := detach_newSourceEdge_ne shape detach detach.remainder (otherSheet profile)
    detach.wallTogether detach.together (otherSheet_not_rel profile)
  have hMemP : ((detach.candidate shape).newSourceEdge detach.remainder ∈
      detachNewOccurrences input shape detach path) ↔ path = rowP :=
    (detach_new_mem_iff_of_survives input shape detach detach.remainder hRemWall
      hRemSurvives path).trans
      ⟨fun h ↦ h.trans (hRowP _), fun h ↦ h.trans (hRowP _).symm⟩
  have hMemQ : ((detach.candidate shape).newSourceEdge (otherSheet profile) ∈
      detachNewOccurrences input shape detach path) ↔ path = rowQ :=
    (detach_new_mem_iff_of_survives input shape detach (otherSheet profile) hOtherWall
      hOtherSurvives path).trans
      ⟨fun h ↦ h.trans (hRowQ _), fun h ↦ h.trans (hRowQ _).symm⟩
  rw [detach_matrix_new_split input shape detach path,
    detach_selected_set input shape detach path, Finset.sum_filter, Finset.sum_pair hNe,
    detach_newSourceEdge_index shape detach detach.remainder detach.wallTogether,
    detach_newSourceEdge_index shape detach (otherSheet profile) (otherSheet_wall_rel profile),
    hIndexP, hIndexQ]
  simp only [hMemP, hMemQ]
  split_ifs <;> ring

/-! ### Figure 34's `M⁽¹⁾` and `M⁽²⁾` -/

/-- **`c⁽¹⁾ = c(e₁)/(k₁-1) + c(e₂)/k₂ + s`** (Figure 34).  Base II.2.1.M: the
datum's pinned sheet lies in `e₁`, so the detachment shrinks the `k₁` class and
leaves `e₂`'s alone. -/
theorem firstMember_regrown (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile)
    (hPin : (endpointPartition profile).Rel (firstSheet profile) (pinSheet profile))
    (path : StablePath data) :
    matrix (detach.candidate shape).datum (detachStablePathEquiv input shape detach path)
        (occurrenceEquiv target wall (detach.candidate shape).right none) =
      (if path = firstRow profile then (1 : ℚ) else 0) /
          ((data.sourceEdgeIndex profile.first.1 : ℚ) - 1) +
        (if path = secondRow profile then (1 : ℚ) else 0) /
          (data.sourceEdgeIndex profile.second.1 : ℚ) +
        LimitChainCore.backgroundColumn data wall block.1 path
          (star.edge profile.doubleLabel) := by
  classical
  have hOther : otherSheet profile = secondSheet profile := by
    simp only [otherSheet, hPin, ↓reduceIte]
  have hIndices := detach_indices_first shape detach hPin
  have hRemEq : data.sourceEdge (star.edge profile.doubleLabel) detach.remainder =
      profile.first.1 :=
    (sourceEdge_double_congr profile (hPin.trans detach.together).symm).trans
      (sourceEdge_double_first profile)
  have hOtherEq : data.sourceEdge (star.edge profile.doubleLabel) (otherSheet profile) =
      profile.second.1 := by
    rw [hOther]
    exact sourceEdge_double_second profile
  have hIndexP : (detach.selected.newEdge.blockCard detach.remainder : ℚ) =
      (data.sourceEdgeIndex profile.first.1 : ℚ) - 1 := by
    have hCast : ((detach.selected.newEdge.blockCard detach.remainder : ℕ) : ℚ) + 1 =
        (data.sourceEdgeIndex profile.first.1 : ℚ) := by exact_mod_cast hIndices.2.1
    rw [← hCast]
    ring
  have hIndexQ : (detach.selected.newEdge.blockCard (otherSheet profile) : ℚ) =
      (data.sourceEdgeIndex profile.second.1 : ℚ) := by
    rw [hOther]
    exact_mod_cast hIndices.2.2.1
  exact detach_regrown input shape detach (firstRow profile) (secondRow profile) _ _
    (fun hSurvives ↦ congrArg NonDanglingEdge.stablePath (Subtype.ext hRemEq))
    (fun hSurvives ↦ congrArg NonDanglingEdge.stablePath (Subtype.ext hOtherEq))
    hIndexP hIndexQ path

/-- **`c⁽²⁾ = c(e₁)/k₁ + c(e₂)/(k₂-1) + s`**.  Base II.2.2.M: the mirror
statement, when the datum's pinned sheet lies in `e₂`. -/
theorem secondMember_regrown (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile)
    (hPin : (endpointPartition profile).Rel (secondSheet profile) (pinSheet profile))
    (path : StablePath data) :
    matrix (detach.candidate shape).datum (detachStablePathEquiv input shape detach path)
        (occurrenceEquiv target wall (detach.candidate shape).right none) =
      (if path = firstRow profile then (1 : ℚ) else 0) /
          (data.sourceEdgeIndex profile.first.1 : ℚ) +
        (if path = secondRow profile then (1 : ℚ) else 0) /
          ((data.sourceEdgeIndex profile.second.1 : ℚ) - 1) +
        LimitChainCore.backgroundColumn data wall block.1 path
          (star.edge profile.doubleLabel) := by
  classical
  have hNotFirst : ¬ (endpointPartition profile).Rel (firstSheet profile)
      (pinSheet profile) := fun h ↦ not_first_and_second h hPin
  have hOther : otherSheet profile = firstSheet profile := by
    simp only [otherSheet, hNotFirst, ↓reduceIte]
  have hIndices := detach_indices_second shape detach hPin
  have hRemEq : data.sourceEdge (star.edge profile.doubleLabel) detach.remainder =
      profile.second.1 :=
    (sourceEdge_double_congr profile (hPin.trans detach.together).symm).trans
      (sourceEdge_double_second profile)
  have hOtherEq : data.sourceEdge (star.edge profile.doubleLabel) (otherSheet profile) =
      profile.first.1 := by
    rw [hOther]
    exact sourceEdge_double_first profile
  have hIndexP : (detach.selected.newEdge.blockCard detach.remainder : ℚ) =
      (data.sourceEdgeIndex profile.second.1 : ℚ) - 1 := by
    have hCast : ((detach.selected.newEdge.blockCard detach.remainder : ℕ) : ℚ) + 1 =
        (data.sourceEdgeIndex profile.second.1 : ℚ) := by exact_mod_cast hIndices.2.1
    rw [← hCast]
    ring
  have hIndexQ : (detach.selected.newEdge.blockCard (otherSheet profile) : ℚ) =
      (data.sourceEdgeIndex profile.first.1 : ℚ) := by
    rw [hOther]
    exact_mod_cast hIndices.2.2.1
  rw [detach_regrown input shape detach (secondRow profile) (firstRow profile) _ _
    (fun hSurvives ↦ congrArg NonDanglingEdge.stablePath (Subtype.ext hRemEq))
    (fun hSurvives ↦ congrArg NonDanglingEdge.stablePath (Subtype.ext hOtherEq))
    hIndexP hIndexQ path]
  ring

/-- `M⁽¹⁾`, read off the structure `W2MkkSourceCandidates` displays. -/
theorem firstMember_regrown_of (input : W2SourceInput data star) (shape : Shape profile)
    (member : FirstMember profile) (path : StablePath data) :
    matrix (member.toDetachData.candidate shape).datum
        (detachStablePathEquiv input shape member.toDetachData path)
        (occurrenceEquiv target wall (member.toDetachData.candidate shape).right none) =
      (if path = firstRow profile then (1 : ℚ) else 0) /
          ((data.sourceEdgeIndex profile.first.1 : ℚ) - 1) +
        (if path = secondRow profile then (1 : ℚ) else 0) /
          (data.sourceEdgeIndex profile.second.1 : ℚ) +
        LimitChainCore.backgroundColumn data wall block.1 path
          (star.edge profile.doubleLabel) :=
  firstMember_regrown input shape member.toDetachData member.pin_first path

/-- `M⁽²⁾`, read off the structure `W2MkkSourceCandidates` displays. -/
theorem secondMember_regrown_of (input : W2SourceInput data star) (shape : Shape profile)
    (member : SecondMember profile) (path : StablePath data) :
    matrix (member.toDetachData.candidate shape).datum
        (detachStablePathEquiv input shape member.toDetachData path)
        (occurrenceEquiv target wall (member.toDetachData.candidate shape).right none) =
      (if path = firstRow profile then (1 : ℚ) else 0) /
          (data.sourceEdgeIndex profile.first.1 : ℚ) +
        (if path = secondRow profile then (1 : ℚ) else 0) /
          ((data.sourceEdgeIndex profile.second.1 : ℚ) - 1) +
        LimitChainCore.backgroundColumn data wall block.1 path
          (star.edge profile.doubleLabel) :=
  secondMember_regrown input shape member.toDetachData member.pin_second path

/-! ## The regrown column of `M⁽³⁾` -/

noncomputable def joinedNewOccurrences (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) (path : StablePath data) :
    Finset (joinedCandidate profile distinguished).datum.SourceEdge :=
  (joinedSelectedData input shape distinguished).newOccurrences path

theorem joined_new_mem_iff_of_survives (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel block.1 sheet)
    (hSurvives : ¬ IsDangling (joinedCandidate profile distinguished).datum
      ((joinedCandidate profile distinguished).newSourceEdge sheet))
    (path : StablePath data) :
    (joinedCandidate profile distinguished).newSourceEdge sheet ∈
        joinedNewOccurrences input shape distinguished path ↔
      path = thirdRow profile :=
  (joinedSelectedData input shape distinguished).new_mem_iff_of_survives sheet hRel hSurvives path

/-- **The regrown column of `M⁽³⁾`, split into its two halves.** -/
theorem joined_matrix_new_split (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) (path : StablePath data) :
    matrix (joinedCandidate profile distinguished).datum
        (joinedStablePathEquiv input shape distinguished path)
        (occurrenceEquiv target wall (joinedCandidate profile distinguished).right none) =
      (∑ edge ∈ (joinedNewOccurrences input shape distinguished path).filter
          (fun edge ↦ (data.vertexPartition wall).Rel block.1 edge.1.2),
        (1 : ℚ) / (joinedCandidate profile distinguished).datum.sourceEdgeIndex edge) +
        LimitChainCore.backgroundColumn data wall block.1 path
          (star.edge profile.doubleLabel) :=
  (joinedSelectedData input shape distinguished).matrix_new_split path

/-- `M⁽³⁾` keeps the whole wall block along the new edge, so its regrown index
is the block's own size. -/
theorem joined_newSourceEdge_index
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished sheet : Fin degree) :
    (joinedCandidate profile distinguished).datum.sourceEdgeIndex
        ((joinedCandidate profile distinguished).newSourceEdge sheet) =
      (data.vertexPartition wall).blockCard sheet := by
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge]
  exact congrArg (fun partition : SheetPartition degree ↦ partition.blockCard sheet)
    (joined_pasted_newEdge profile distinguished)

/-- **`M⁽³⁾` has one regrown class above `A₀`.** -/
theorem joined_newSourceEdge_cover
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    (joinedCandidate profile distinguished).newSourceEdge sheet =
      (joinedCandidate profile distinguished).newSourceEdge block.1 := by
  refine (LimitChainCore.newSourceEdge_eq_iff_rel sheet block.1).mpr ?_
  rw [joined_pasted_newEdge profile distinguished]
  exact hSheet.symm

theorem joined_selected_set (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) (path : StablePath data) :
    (joinedNewOccurrences input shape distinguished path).filter
        (fun edge ↦ (data.vertexPartition wall).Rel block.1 edge.1.2) =
      ({(joinedCandidate profile distinguished).newSourceEdge block.1} :
        Finset (joinedCandidate profile distinguished).datum.SourceEdge).filter
        (fun edge ↦ edge ∈ joinedNewOccurrences input shape distinguished path) :=
  selected_set_single (joinedSelectedData input shape distinguished) block.1 rfl
    (fun sheet hSheet ↦ joined_newSourceEdge_cover profile distinguished sheet hSheet) path

/-- **`c⁽³⁾ = c(e₃)/(k₁+k₂) + s`**.  Base II.1.M: the whole block is retained
along the new edge, and the one regrown occurrence lies in `e₃`'s row. -/
theorem thirdMember_regrown (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) (path : StablePath data) :
    matrix (joinedCandidate profile distinguished).datum
        (joinedStablePathEquiv input shape distinguished path)
        (occurrenceEquiv target wall (joinedCandidate profile distinguished).right none) =
      (if path = thirdRow profile then (1 : ℚ) else 0) /
          ((data.sourceEdgeIndex profile.first.1 : ℚ) +
            (data.sourceEdgeIndex profile.second.1 : ℚ)) +
        LimitChainCore.backgroundColumn data wall block.1 path
          (star.edge profile.doubleLabel) := by
  classical
  have hAnchor : (data.vertexPartition wall).Rel block.1 block.1 := rfl
  have hSurvives := joined_new_survives input shape distinguished block.1 hAnchor
  have hMem := joined_new_mem_iff_of_survives input shape distinguished block.1 hAnchor
    hSurvives path
  rw [joined_matrix_new_split input shape distinguished path,
    joined_selected_set input shape distinguished path, Finset.sum_filter, Finset.sum_singleton,
    joined_newSourceEdge_index profile distinguished block.1,
    blockCard_of_rel shape block.1 hAnchor]
  simp only [hMem]
  split_ifs <;> push_cast <;> ring

end DraismaVargas.LocalCases.W2MkkLimitMatrix
