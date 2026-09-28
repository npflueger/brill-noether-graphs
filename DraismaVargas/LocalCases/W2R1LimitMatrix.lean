import DraismaVargas.LocalCases.W2R1CommonBalance

/-!
# Figures 37 and 38's limit matrices, and an inhabitant of `LimitColumns`

Source: Draisma--Vargas Part I (arXiv:1909.12924), Section 6, Case `{w2-r1}`,
Figures 37 and 38 and Equation (10).

`W2R1RowDescent` proves the two-block row equivalence, the retained columns and
`matrix_new_split_pair` -- Equation (10)'s shape
`c⁽ⁱ⁾ = σ⁽ⁱ⁾(J_{A₀},1) + σ⁽ⁱ⁾(J_{B₀},1) + s` with the two selected sums left
unevaluated.  This module evaluates them, at **both** blocks and for **both**
members, and inhabits `W2R1CommonBalance.LimitColumns`.

## The four regrown evaluations

At one ramification-one block a member is retained (`position = double`) or
resolved (`position ≠ double`), and the block is `nd3` or `nd2`:

| member | sub-case | regrown occurrences above the block | evaluation |
|---|---|---|---|
| retained (gluing I) | nd3 | one, `\|e'\| = k₃ = k₁+k₂` | `c(e₃)/(k₁+k₂)` |
| retained (gluing I) | nd2 | one, `\|e'\| = k₃ = k₂+1` | `c_h/(k₂+1)` |
| resolved (gluing II) | nd3 | two, `\|e'\| = k₁`, `\|e''\| = k₂` | `c(e₁)/k₁ + c(e₂)/k₂` |
| resolved (gluing II) | nd2 | one surviving, `\|e''\| = k₂` (`e'` pruned with `e₁`) | `c_h/k₂` |

These are `first_regrown_retained`, `first_regrown_resolved_nd3`,
`first_regrown_resolved_nd2` at `A₀` and their `B₀` twins.  Read with
`W2R1SourceCandidates.nd2_displayed_indices` (`k₁ = 1`, `k₃ = k₂ + 1`) the two
`nd2` rows are exactly Figure 38's two gluing boxes, and the two `nd3` rows
are Figure 37's.

## The three sum shapes, proved once for an arbitrary anchor set

`selected_sum_single`, `selected_sum_pair` and `selected_sum_pair_of_dangling`
are stated for an arbitrary `LimitChainTwoBlock.SelectedData` over an
arbitrary finite anchor set, so nothing in them is specific to this case.  They
are the summed forms of `LimitChainTwoBlock.SelectedData.selected_set` and
`LimitChainTwoBlock.SelectedData.selected_set_of_dangling`, which identify the
regrown occurrences above one block as a set.
-/

namespace DraismaVargas.LocalCases.W2R1LimitMatrix

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open ResolutionM11
open ResolutionAwayFromWall StableSourceMatrix
open W2R1SourceCandidates
open W2R1StableGraph
open W2R1StableLift
open W2R1RowDescent
open W2R1CommonBalance
open LimitChainTwoBlock (IsSelected SelectedData isSelected_of_rel)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## §1  The three regrown sum shapes, at an arbitrary anchor set -/

section Sums

variable {anchors : Finset (Fin degree)} (rd : SelectedData data wall anchors)

/-- **One regrown occurrence above the block.**  This is Figure 37/38's
gluing I, and Figure 38's gluing II once `e'` is pruned. -/
theorem selected_sum_single {anchor witness : Fin degree} (hAnchor : anchor ∈ anchors)
    (hWitness : (data.vertexPartition wall).Rel anchor witness)
    (hCover : ∀ sheet : Fin degree, (data.vertexPartition wall).Rel anchor sheet →
      rd.candidate.newSourceEdge sheet = rd.candidate.newSourceEdge witness)
    (hSurvives : ¬ IsDangling rd.candidate.datum (rd.candidate.newSourceEdge witness))
    (old : NonDanglingEdge data) (hRep : rd.selectedRep witness = old.1)
    (path : StablePath data) :
    (∑ edge ∈ (rd.newOccurrences path).filter
        (fun edge ↦ (data.vertexPartition wall).Rel anchor edge.1.2),
      (1 : ℚ) / rd.candidate.datum.sourceEdgeIndex edge) =
      (if path = old.stablePath then (1 : ℚ) else 0) /
        (rd.candidate.datum.sourceEdgeIndex (rd.candidate.newSourceEdge witness) : ℚ) := by
  classical
  have hSet : (rd.newOccurrences path).filter
        (fun edge ↦ (data.vertexPartition wall).Rel anchor edge.1.2) =
      ({rd.candidate.newSourceEdge witness} : Finset rd.candidate.datum.SourceEdge).filter
        (fun edge ↦ edge ∈ rd.newOccurrences path) := by
    ext edge
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hMem, hRel⟩
      exact ⟨(rd.eq_newSourceEdge_of_mem path edge hMem).trans (hCover edge.1.2 hRel), hMem⟩
    · rintro ⟨rfl, hMem⟩
      exact ⟨hMem, (rd.newSourceEdge_sheet_rel_iff anchor witness).mpr hWitness⟩
  have hMem : rd.candidate.newSourceEdge witness ∈ rd.newOccurrences path ↔
      path = old.stablePath := by
    rw [rd.new_mem_iff_of_survives witness (isSelected_of_rel hAnchor hWitness) hSurvives path]
    exact Iff.of_eq (congrArg (fun item ↦ path = item)
      (congrArg NonDanglingEdge.stablePath (Subtype.ext hRep)))
  rw [hSet, Finset.sum_filter, Finset.sum_singleton]
  simp only [hMem]
  split_ifs <;> ring

/-- **Two surviving regrown occurrences above the block**: Figure 37's
gluing II. -/
theorem selected_sum_pair {anchor first second : Fin degree} (hAnchor : anchor ∈ anchors)
    (hFirst : (data.vertexPartition wall).Rel anchor first)
    (hSecond : (data.vertexPartition wall).Rel anchor second)
    (hCover : ∀ sheet : Fin degree, (data.vertexPartition wall).Rel anchor sheet →
      rd.candidate.newSourceEdge sheet = rd.candidate.newSourceEdge first ∨
        rd.candidate.newSourceEdge sheet = rd.candidate.newSourceEdge second)
    (hNe : rd.candidate.newSourceEdge first ≠ rd.candidate.newSourceEdge second)
    (hSurvivesFirst : ¬ IsDangling rd.candidate.datum (rd.candidate.newSourceEdge first))
    (hSurvivesSecond : ¬ IsDangling rd.candidate.datum (rd.candidate.newSourceEdge second))
    (oldFirst oldSecond : NonDanglingEdge data)
    (hRepFirst : rd.selectedRep first = oldFirst.1)
    (hRepSecond : rd.selectedRep second = oldSecond.1)
    (path : StablePath data) :
    (∑ edge ∈ (rd.newOccurrences path).filter
        (fun edge ↦ (data.vertexPartition wall).Rel anchor edge.1.2),
      (1 : ℚ) / rd.candidate.datum.sourceEdgeIndex edge) =
      (if path = oldFirst.stablePath then (1 : ℚ) else 0) /
          (rd.candidate.datum.sourceEdgeIndex (rd.candidate.newSourceEdge first) : ℚ) +
        (if path = oldSecond.stablePath then (1 : ℚ) else 0) /
          (rd.candidate.datum.sourceEdgeIndex (rd.candidate.newSourceEdge second) : ℚ) := by
  classical
  have hMemFirst : rd.candidate.newSourceEdge first ∈ rd.newOccurrences path ↔
      path = oldFirst.stablePath := by
    rw [rd.new_mem_iff_of_survives first (isSelected_of_rel hAnchor hFirst) hSurvivesFirst path]
    exact Iff.of_eq (congrArg (fun item ↦ path = item)
      (congrArg NonDanglingEdge.stablePath (Subtype.ext hRepFirst)))
  have hMemSecond : rd.candidate.newSourceEdge second ∈ rd.newOccurrences path ↔
      path = oldSecond.stablePath := by
    rw [rd.new_mem_iff_of_survives second (isSelected_of_rel hAnchor hSecond) hSurvivesSecond path]
    exact Iff.of_eq (congrArg (fun item ↦ path = item)
      (congrArg NonDanglingEdge.stablePath (Subtype.ext hRepSecond)))
  rw [rd.selected_set anchor first second hFirst hSecond hCover path,
    Finset.sum_filter, Finset.sum_pair hNe]
  simp only [hMemFirst, hMemSecond]
  split_ifs <;> ring

/-- **Two regrown classes, one of them pruned**: Figure 38's gluing II, where
the whole `e₁` endpoint is deleted with `e₁`. -/
theorem selected_sum_pair_of_dangling {anchor first second : Fin degree}
    (hAnchor : anchor ∈ anchors)
    (hFirst : (data.vertexPartition wall).Rel anchor first)
    (hCover : ∀ sheet : Fin degree, (data.vertexPartition wall).Rel anchor sheet →
      rd.candidate.newSourceEdge sheet = rd.candidate.newSourceEdge first ∨
        rd.candidate.newSourceEdge sheet = rd.candidate.newSourceEdge second)
    (hDangling : IsDangling rd.candidate.datum (rd.candidate.newSourceEdge second))
    (hSurvives : ¬ IsDangling rd.candidate.datum (rd.candidate.newSourceEdge first))
    (old : NonDanglingEdge data) (hRep : rd.selectedRep first = old.1)
    (path : StablePath data) :
    (∑ edge ∈ (rd.newOccurrences path).filter
        (fun edge ↦ (data.vertexPartition wall).Rel anchor edge.1.2),
      (1 : ℚ) / rd.candidate.datum.sourceEdgeIndex edge) =
      (if path = old.stablePath then (1 : ℚ) else 0) /
        (rd.candidate.datum.sourceEdgeIndex (rd.candidate.newSourceEdge first) : ℚ) := by
  classical
  have hMem : rd.candidate.newSourceEdge first ∈ rd.newOccurrences path ↔
      path = old.stablePath := by
    rw [rd.new_mem_iff_of_survives first (isSelected_of_rel hAnchor hFirst) hSurvives path]
    exact Iff.of_eq (congrArg (fun item ↦ path = item)
      (congrArg NonDanglingEdge.stablePath (Subtype.ext hRep)))
  rw [rd.selected_set_of_dangling anchor first second hFirst hCover hDangling path,
    Finset.sum_filter, Finset.sum_singleton]
  simp only [hMem]
  split_ifs <;> ring

end Sums

/-! ## §2  The regrown indices of one member above one block

Figure 37's `|e'| = k₃` (gluing I) and `|e'| = k₁`, `|e''| = k₂` (gluing II),
read on the member's actual quotient-source occurrence. -/

section Indices

variable {block : WallBlock data wall} (member : BlockMember data star block)

private theorem newEdge_blockCard {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    member.candidate.datum.sourceEdgeIndex (member.candidate.newSourceEdge sheet) =
      (memberLocal data star member.profile.doubleLabel member.position).newEdge.blockCard
        sheet := by
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge,
    LocalResolution.paste_newEdge_blockCard,
    member.local_eq ((data.vertexPartition wall).repr sheet)
      (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]

/-- **Gluing I: `|e'| = k₃`.** -/
theorem retained_new_index (hPosition : member.position = member.double)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    member.candidate.datum.sourceEdgeIndex (member.candidate.newSourceEdge sheet) =
      data.sourceEdgeIndex member.profile.third.1 := by
  rw [newEdge_blockCard member hSheet]
  exact memberLocal_newEdge_blockCard_retained member.profile.toOccurrenceProfile
    hPosition sheet hSheet

/-- **Gluing II: `|e'| = k₁`.** -/
theorem resolved_new_index_first (hPosition : member.position ≠ member.double) :
    member.candidate.datum.sourceEdgeIndex (member.candidate.newSourceEdge
        (firstSheet member.profile.toOccurrenceProfile)) =
      data.sourceEdgeIndex member.profile.first.1 := by
  rw [newEdge_blockCard member (firstSheet_rel member.profile.toOccurrenceProfile)]
  exact (memberLocal_newEdge_blockCard_resolved member.profile.toOccurrenceProfile hPosition).1

/-- **Gluing II: `|e''| = k₂`.** -/
theorem resolved_new_index_second (hPosition : member.position ≠ member.double) :
    member.candidate.datum.sourceEdgeIndex (member.candidate.newSourceEdge
        (secondSheet member.profile.toOccurrenceProfile)) =
      data.sourceEdgeIndex member.profile.second.1 := by
  rw [newEdge_blockCard member (secondSheet_rel member.profile.toOccurrenceProfile)]
  exact (memberLocal_newEdge_blockCard_resolved member.profile.toOccurrenceProfile hPosition).2.1

/-- The doubled direction's two classes cover the block, in the shape the sum
lemmas want. -/
theorem resolved_new_cover (hPosition : member.position ≠ member.double)
    (sheet : Fin degree) (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    member.candidate.newSourceEdge sheet =
        member.candidate.newSourceEdge (firstSheet member.profile.toOccurrenceProfile) ∨
      member.candidate.newSourceEdge sheet =
        member.candidate.newSourceEdge (secondSheet member.profile.toOccurrenceProfile) := by
  rcases doublePartition_covers member.profile.toOccurrenceProfile sheet hSheet with hRel | hRel
  · exact Or.inl ((member.resolved_new_eq_iff hPosition hSheet _).mpr hRel.symm)
  · exact Or.inr ((member.resolved_new_eq_iff hPosition hSheet _).mpr hRel.symm)

/-- `e'` dies with `e₁` in `nd2`. -/
theorem resolved_new_first_dangles (hPosition : member.position ≠ member.double)
    (hNd2 : IsDangling data member.profile.first.1) :
    IsDangling member.candidate.datum (member.candidate.newSourceEdge
      (firstSheet member.profile.toOccurrenceProfile)) := by
  by_contra hSurvives
  exact ((member.resolved_new_first_survives_iff hPosition).mp hSurvives) hNd2

end Indices


/-! ## §3  The four regrown evaluations

`firstHalf` and `secondHalf` are literally the two selected sums that
`W2R1RowDescent.matrix_new_split_pair` leaves standing.  Each is evaluated in
three theorems -- gluing I, gluing II in `nd3`, gluing II in `nd2` -- and the
three evaluations are exactly the figures' boxes. -/

section Evaluations

variable (pair : Pair data star) (hValid : data.Valid)

/-- **`σ⁽ᵠ⁾(J_{A₀},1)`**, the member's regrown half above `A₀`. -/
noncomputable def firstHalf (position : Fin 2) (path : StablePath data) : ℚ :=
  ∑ edge ∈ ((selectedData pair hValid position).newOccurrences path).filter
      (fun edge ↦ (data.vertexPartition wall).Rel pair.first.1 edge.1.2),
    (1 : ℚ) / (selectedData pair hValid position).candidate.datum.sourceEdgeIndex edge

/-- **`σ⁽ᵠ⁾(J_{B₀},1)`**, the member's regrown half above `B₀`. -/
noncomputable def secondHalf (position : Fin 2) (path : StablePath data) : ℚ :=
  ∑ edge ∈ ((selectedData pair hValid position).newOccurrences path).filter
      (fun edge ↦ (data.vertexPartition wall).Rel pair.second.1 edge.1.2),
    (1 : ℚ) / (selectedData pair hValid position).candidate.datum.sourceEdgeIndex edge

/-- **Figure 37/38 gluing I at `A₀`: `σ⁽¹⁾(J_{A₀},1) = c(e₃)/k₃`.**  In `nd2`,
`k₃ = k₂ + 1` and `e₃`'s row is Figure 38's `h`, so this is `c_h/(k₂+1)`. -/
theorem first_regrown_retained {position : Fin 2}
    (hPosition : position = pair.firstProfile.doubleLabel) (path : StablePath data) :
    firstHalf pair hValid position path =
      (if path = thirdRow pair.firstProfile then (1 : ℚ) else 0) /
        (data.sourceEdgeIndex pair.firstProfile.third.1 : ℚ) := by
  have hRefl : (data.vertexPartition wall).Rel pair.first.1 pair.first.1 := rfl
  have hCover : ∀ sheet : Fin degree, (data.vertexPartition wall).Rel pair.first.1 sheet →
      (selectedData pair hValid position).candidate.newSourceEdge sheet =
        (selectedData pair hValid position).candidate.newSourceEdge pair.first.1 :=
    fun sheet hSheet ↦ (firstMember pair hValid position).retained_new_eq hPosition hSheet hRefl
  have hSurvives : ¬ IsDangling (selectedData pair hValid position).candidate.datum
      ((selectedData pair hValid position).candidate.newSourceEdge pair.first.1) :=
    (firstMember pair hValid position).retained_new_survives hPosition hRefl
  have hRep : (selectedData pair hValid position).selectedRep pair.first.1 =
      pair.firstProfile.third.1 :=
    (selectedRep_first pair hValid position hRefl).trans
      (rep_retained (firstMember pair hValid position) hPosition pair.first.1)
  have hIndex : (selectedData pair hValid position).candidate.datum.sourceEdgeIndex
      ((selectedData pair hValid position).candidate.newSourceEdge pair.first.1) =
      data.sourceEdgeIndex pair.firstProfile.third.1 :=
    retained_new_index (firstMember pair hValid position) hPosition hRefl
  rw [firstHalf, selected_sum_single (selectedData pair hValid position)
    (first_mem_anchors pair) hRefl hCover hSurvives
    ⟨pair.firstProfile.third.1, pair.firstProfile.third_survives⟩ hRep path, hIndex]
  rfl

/-- **Figure 37 gluing II at `A₀` (`nd3`): `σ⁽²⁾(J_{A₀},1) = c(e₁)/k₁ +
c(e₂)/k₂`.** -/
theorem first_regrown_resolved_nd3 {position : Fin 2}
    (hPosition : position ≠ pair.firstProfile.doubleLabel)
    (hNd3 : ¬ IsDangling data pair.firstProfile.first.1) (path : StablePath data) :
    firstHalf pair hValid position path =
      (if path = firstRow pair.firstProfile hNd3 then (1 : ℚ) else 0) /
          (data.sourceEdgeIndex pair.firstProfile.first.1 : ℚ) +
        (if path = secondRow pair.firstProfile then (1 : ℚ) else 0) /
          (data.sourceEdgeIndex pair.firstProfile.second.1 : ℚ) := by
  have hFirstRel := firstSheet_rel pair.firstProfile.toOccurrenceProfile
  have hSecondRel := secondSheet_rel pair.firstProfile.toOccurrenceProfile
  have hCover := resolved_new_cover (firstMember pair hValid position) hPosition
  have hNe : (selectedData pair hValid position).candidate.newSourceEdge
        (firstSheet pair.firstProfile.toOccurrenceProfile) ≠
      (selectedData pair hValid position).candidate.newSourceEdge
        (secondSheet pair.firstProfile.toOccurrenceProfile) :=
    (firstMember pair hValid position).resolved_new_first_ne_second hPosition
  have hSurvivesFirst : ¬ IsDangling (selectedData pair hValid position).candidate.datum
      ((selectedData pair hValid position).candidate.newSourceEdge
        (firstSheet pair.firstProfile.toOccurrenceProfile)) :=
    ((firstMember pair hValid position).resolved_new_first_survives_iff hPosition).mpr hNd3
  have hSurvivesSecond : ¬ IsDangling (selectedData pair hValid position).candidate.datum
      ((selectedData pair hValid position).candidate.newSourceEdge
        (secondSheet pair.firstProfile.toOccurrenceProfile)) :=
    (firstMember pair hValid position).resolved_new_second_survives hPosition
  have hRepFirst : (selectedData pair hValid position).selectedRep
      (firstSheet pair.firstProfile.toOccurrenceProfile) = pair.firstProfile.first.1 :=
    (selectedRep_first pair hValid position hFirstRel).trans
      (rep_resolved_first_nd3 (firstMember pair hValid position) hPosition
        (fun h ↦ doublePartition_separate pair.firstProfile.toOccurrenceProfile h.symm) hNd3)
  have hRepSecond : (selectedData pair hValid position).selectedRep
      (secondSheet pair.firstProfile.toOccurrenceProfile) = pair.firstProfile.second.1 :=
    (selectedRep_first pair hValid position hSecondRel).trans
      (rep_resolved_second (firstMember pair hValid position) hPosition
        (((doublePartition pair.firstProfile.toOccurrenceProfile).rel_iff _ _).mpr rfl))
  have hIndexFirst : (selectedData pair hValid position).candidate.datum.sourceEdgeIndex
      ((selectedData pair hValid position).candidate.newSourceEdge
        (firstSheet pair.firstProfile.toOccurrenceProfile)) =
      data.sourceEdgeIndex pair.firstProfile.first.1 :=
    resolved_new_index_first (firstMember pair hValid position) hPosition
  have hIndexSecond : (selectedData pair hValid position).candidate.datum.sourceEdgeIndex
      ((selectedData pair hValid position).candidate.newSourceEdge
        (secondSheet pair.firstProfile.toOccurrenceProfile)) =
      data.sourceEdgeIndex pair.firstProfile.second.1 :=
    resolved_new_index_second (firstMember pair hValid position) hPosition
  rw [firstHalf, selected_sum_pair (selectedData pair hValid position)
    (first_mem_anchors pair) hFirstRel hSecondRel hCover hNe hSurvivesFirst hSurvivesSecond
    ⟨pair.firstProfile.first.1, hNd3⟩
    ⟨pair.firstProfile.second.1, pair.firstProfile.second_survives⟩ hRepFirst hRepSecond path,
    hIndexFirst, hIndexSecond]
  rfl

/-- **Figure 38 gluing II at `A₀` (`nd2`): `σ⁽²⁾(J_{A₀},1) = c_h/k₂`.**  The
`e₁` class is a single sheet and its whole endpoint is pruned, which is why
Figure 38 draws one new occurrence where Figure 37 draws two. -/
theorem first_regrown_resolved_nd2 {position : Fin 2}
    (hPosition : position ≠ pair.firstProfile.doubleLabel)
    (hNd2 : IsDangling data pair.firstProfile.first.1) (path : StablePath data) :
    firstHalf pair hValid position path =
      (if path = secondRow pair.firstProfile then (1 : ℚ) else 0) /
        (data.sourceEdgeIndex pair.firstProfile.second.1 : ℚ) := by
  have hSecondRel := secondSheet_rel pair.firstProfile.toOccurrenceProfile
  have hCover : ∀ sheet : Fin degree, (data.vertexPartition wall).Rel pair.first.1 sheet →
      (selectedData pair hValid position).candidate.newSourceEdge sheet =
          (selectedData pair hValid position).candidate.newSourceEdge
            (secondSheet pair.firstProfile.toOccurrenceProfile) ∨
        (selectedData pair hValid position).candidate.newSourceEdge sheet =
          (selectedData pair hValid position).candidate.newSourceEdge
            (firstSheet pair.firstProfile.toOccurrenceProfile) := by
    intro sheet hSheet
    rcases resolved_new_cover (firstMember pair hValid position) hPosition sheet hSheet with
      hEq | hEq
    · exact Or.inr hEq
    · exact Or.inl hEq
  have hDangling : IsDangling (selectedData pair hValid position).candidate.datum
      ((selectedData pair hValid position).candidate.newSourceEdge
        (firstSheet pair.firstProfile.toOccurrenceProfile)) :=
    resolved_new_first_dangles (firstMember pair hValid position) hPosition hNd2
  have hSurvives : ¬ IsDangling (selectedData pair hValid position).candidate.datum
      ((selectedData pair hValid position).candidate.newSourceEdge
        (secondSheet pair.firstProfile.toOccurrenceProfile)) :=
    (firstMember pair hValid position).resolved_new_second_survives hPosition
  have hRep : (selectedData pair hValid position).selectedRep
      (secondSheet pair.firstProfile.toOccurrenceProfile) = pair.firstProfile.second.1 :=
    (selectedRep_first pair hValid position hSecondRel).trans
      (rep_resolved_second (firstMember pair hValid position) hPosition
        (((doublePartition pair.firstProfile.toOccurrenceProfile).rel_iff _ _).mpr rfl))
  have hIndex : (selectedData pair hValid position).candidate.datum.sourceEdgeIndex
      ((selectedData pair hValid position).candidate.newSourceEdge
        (secondSheet pair.firstProfile.toOccurrenceProfile)) =
      data.sourceEdgeIndex pair.firstProfile.second.1 :=
    resolved_new_index_second (firstMember pair hValid position) hPosition
  rw [firstHalf, selected_sum_pair_of_dangling (selectedData pair hValid position)
    (first_mem_anchors pair) hSecondRel hCover hDangling hSurvives
    ⟨pair.firstProfile.second.1, pair.firstProfile.second_survives⟩ hRep path, hIndex]
  rfl


/-- **Gluing I at `B₀`: `σ⁽¹⁾(J_{B₀},1) = c(e₃)/k₃`** -- "the previous analysis
holds for `B₀`, with notation entirely analogous" (Part I, proof of (⋆) for
Case `{w2-r1}`), at the **opposite** position. -/
theorem second_regrown_retained {position : Fin 2}
    (hPosition : other position = pair.secondProfile.doubleLabel) (path : StablePath data) :
    secondHalf pair hValid position path =
      (if path = thirdRow pair.secondProfile then (1 : ℚ) else 0) /
        (data.sourceEdgeIndex pair.secondProfile.third.1 : ℚ) := by
  have hRefl : (data.vertexPartition wall).Rel pair.second.1 pair.second.1 := rfl
  have hCover : ∀ sheet : Fin degree, (data.vertexPartition wall).Rel pair.second.1 sheet →
      (selectedData pair hValid position).candidate.newSourceEdge sheet =
        (selectedData pair hValid position).candidate.newSourceEdge pair.second.1 :=
    fun sheet hSheet ↦ (secondMember pair hValid position).retained_new_eq hPosition hSheet hRefl
  have hSurvives : ¬ IsDangling (selectedData pair hValid position).candidate.datum
      ((selectedData pair hValid position).candidate.newSourceEdge pair.second.1) :=
    (secondMember pair hValid position).retained_new_survives hPosition hRefl
  have hRep : (selectedData pair hValid position).selectedRep pair.second.1 =
      pair.secondProfile.third.1 :=
    (selectedRep_second pair hValid position (pair.not_rel_first_of_rel_second hRefl)).trans
      (rep_retained (secondMember pair hValid position) hPosition pair.second.1)
  have hIndex : (selectedData pair hValid position).candidate.datum.sourceEdgeIndex
      ((selectedData pair hValid position).candidate.newSourceEdge pair.second.1) =
      data.sourceEdgeIndex pair.secondProfile.third.1 :=
    retained_new_index (secondMember pair hValid position) hPosition hRefl
  rw [secondHalf, selected_sum_single (selectedData pair hValid position)
    (second_mem_anchors pair) hRefl hCover hSurvives
    ⟨pair.secondProfile.third.1, pair.secondProfile.third_survives⟩ hRep path, hIndex]
  rfl

/-- **Gluing II at `B₀` (`nd3`): `σ⁽²⁾(J_{B₀},1) = c(e₁)/k₁ + c(e₂)/k₂`.** -/
theorem second_regrown_resolved_nd3 {position : Fin 2}
    (hPosition : other position ≠ pair.secondProfile.doubleLabel)
    (hNd3 : ¬ IsDangling data pair.secondProfile.first.1) (path : StablePath data) :
    secondHalf pair hValid position path =
      (if path = firstRow pair.secondProfile hNd3 then (1 : ℚ) else 0) /
          (data.sourceEdgeIndex pair.secondProfile.first.1 : ℚ) +
        (if path = secondRow pair.secondProfile then (1 : ℚ) else 0) /
          (data.sourceEdgeIndex pair.secondProfile.second.1 : ℚ) := by
  have hFirstRel := firstSheet_rel pair.secondProfile.toOccurrenceProfile
  have hSecondRel := secondSheet_rel pair.secondProfile.toOccurrenceProfile
  have hCover := resolved_new_cover (secondMember pair hValid position) hPosition
  have hNe : (selectedData pair hValid position).candidate.newSourceEdge
        (firstSheet pair.secondProfile.toOccurrenceProfile) ≠
      (selectedData pair hValid position).candidate.newSourceEdge
        (secondSheet pair.secondProfile.toOccurrenceProfile) :=
    (secondMember pair hValid position).resolved_new_first_ne_second hPosition
  have hSurvivesFirst : ¬ IsDangling (selectedData pair hValid position).candidate.datum
      ((selectedData pair hValid position).candidate.newSourceEdge
        (firstSheet pair.secondProfile.toOccurrenceProfile)) :=
    ((secondMember pair hValid position).resolved_new_first_survives_iff hPosition).mpr hNd3
  have hSurvivesSecond : ¬ IsDangling (selectedData pair hValid position).candidate.datum
      ((selectedData pair hValid position).candidate.newSourceEdge
        (secondSheet pair.secondProfile.toOccurrenceProfile)) :=
    (secondMember pair hValid position).resolved_new_second_survives hPosition
  have hRepFirst : (selectedData pair hValid position).selectedRep
      (firstSheet pair.secondProfile.toOccurrenceProfile) = pair.secondProfile.first.1 :=
    (selectedRep_second pair hValid position
        (pair.not_rel_first_of_rel_second hFirstRel)).trans
      (rep_resolved_first_nd3 (secondMember pair hValid position) hPosition
        (fun h ↦ doublePartition_separate pair.secondProfile.toOccurrenceProfile h.symm) hNd3)
  have hRepSecond : (selectedData pair hValid position).selectedRep
      (secondSheet pair.secondProfile.toOccurrenceProfile) = pair.secondProfile.second.1 :=
    (selectedRep_second pair hValid position
        (pair.not_rel_first_of_rel_second hSecondRel)).trans
      (rep_resolved_second (secondMember pair hValid position) hPosition
        (((doublePartition pair.secondProfile.toOccurrenceProfile).rel_iff _ _).mpr rfl))
  have hIndexFirst : (selectedData pair hValid position).candidate.datum.sourceEdgeIndex
      ((selectedData pair hValid position).candidate.newSourceEdge
        (firstSheet pair.secondProfile.toOccurrenceProfile)) =
      data.sourceEdgeIndex pair.secondProfile.first.1 :=
    resolved_new_index_first (secondMember pair hValid position) hPosition
  have hIndexSecond : (selectedData pair hValid position).candidate.datum.sourceEdgeIndex
      ((selectedData pair hValid position).candidate.newSourceEdge
        (secondSheet pair.secondProfile.toOccurrenceProfile)) =
      data.sourceEdgeIndex pair.secondProfile.second.1 :=
    resolved_new_index_second (secondMember pair hValid position) hPosition
  rw [secondHalf, selected_sum_pair (selectedData pair hValid position)
    (second_mem_anchors pair) hFirstRel hSecondRel hCover hNe hSurvivesFirst hSurvivesSecond
    ⟨pair.secondProfile.first.1, hNd3⟩
    ⟨pair.secondProfile.second.1, pair.secondProfile.second_survives⟩ hRepFirst hRepSecond path,
    hIndexFirst, hIndexSecond]
  rfl

/-- **Gluing II at `B₀` (`nd2`): `σ⁽²⁾(J_{B₀},1) = c_h/k₂`.** -/
theorem second_regrown_resolved_nd2 {position : Fin 2}
    (hPosition : other position ≠ pair.secondProfile.doubleLabel)
    (hNd2 : IsDangling data pair.secondProfile.first.1) (path : StablePath data) :
    secondHalf pair hValid position path =
      (if path = secondRow pair.secondProfile then (1 : ℚ) else 0) /
        (data.sourceEdgeIndex pair.secondProfile.second.1 : ℚ) := by
  have hSecondRel := secondSheet_rel pair.secondProfile.toOccurrenceProfile
  have hCover : ∀ sheet : Fin degree, (data.vertexPartition wall).Rel pair.second.1 sheet →
      (selectedData pair hValid position).candidate.newSourceEdge sheet =
          (selectedData pair hValid position).candidate.newSourceEdge
            (secondSheet pair.secondProfile.toOccurrenceProfile) ∨
        (selectedData pair hValid position).candidate.newSourceEdge sheet =
          (selectedData pair hValid position).candidate.newSourceEdge
            (firstSheet pair.secondProfile.toOccurrenceProfile) := by
    intro sheet hSheet
    rcases resolved_new_cover (secondMember pair hValid position) hPosition sheet hSheet with
      hEq | hEq
    · exact Or.inr hEq
    · exact Or.inl hEq
  have hDangling : IsDangling (selectedData pair hValid position).candidate.datum
      ((selectedData pair hValid position).candidate.newSourceEdge
        (firstSheet pair.secondProfile.toOccurrenceProfile)) :=
    resolved_new_first_dangles (secondMember pair hValid position) hPosition hNd2
  have hSurvives : ¬ IsDangling (selectedData pair hValid position).candidate.datum
      ((selectedData pair hValid position).candidate.newSourceEdge
        (secondSheet pair.secondProfile.toOccurrenceProfile)) :=
    (secondMember pair hValid position).resolved_new_second_survives hPosition
  have hRep : (selectedData pair hValid position).selectedRep
      (secondSheet pair.secondProfile.toOccurrenceProfile) = pair.secondProfile.second.1 :=
    (selectedRep_second pair hValid position
        (pair.not_rel_first_of_rel_second hSecondRel)).trans
      (rep_resolved_second (secondMember pair hValid position) hPosition
        (((doublePartition pair.secondProfile.toOccurrenceProfile).rel_iff _ _).mpr rfl))
  have hIndex : (selectedData pair hValid position).candidate.datum.sourceEdgeIndex
      ((selectedData pair hValid position).candidate.newSourceEdge
        (secondSheet pair.secondProfile.toOccurrenceProfile)) =
      data.sourceEdgeIndex pair.secondProfile.second.1 :=
    resolved_new_index_second (secondMember pair hValid position) hPosition
  rw [secondHalf, selected_sum_pair_of_dangling (selectedData pair hValid position)
    (second_mem_anchors pair) hSecondRel hCover hDangling hSurvives
    ⟨pair.secondProfile.second.1, pair.secondProfile.second_survives⟩ hRep path, hIndex]
  rfl

/-! ### The boxes in the figures' own symbols

Figure 37 prints gluing I as `c(e₃)/(k₁+k₂)` and Figure 38 prints it as
`c_h/(k₂+1)`; both are `first_regrown_retained` with the block's own index
identity substituted.  Gluing II is already printed in the profile's own
symbols by `first_regrown_resolved_nd3` and `first_regrown_resolved_nd2`. -/

/-- **Figure 37, gluing I at `A₀`: `σ⁽¹⁾(J_{A₀},1) = c(e₃)/(k₁+k₂)`.** -/
theorem first_regrown_retained_nd3 {position : Fin 2}
    (hPosition : position = pair.firstProfile.doubleLabel) (path : StablePath data) :
    firstHalf pair hValid position path =
      (if path = thirdRow pair.firstProfile then (1 : ℚ) else 0) /
        ((data.sourceEdgeIndex pair.firstProfile.first.1 : ℚ) +
          (data.sourceEdgeIndex pair.firstProfile.second.1 : ℚ)) := by
  have hIndex : (data.sourceEdgeIndex pair.firstProfile.first.1 : ℚ) +
      (data.sourceEdgeIndex pair.firstProfile.second.1 : ℚ) =
      (data.sourceEdgeIndex pair.firstProfile.third.1 : ℚ) := by
    exact_mod_cast congrArg (Nat.cast (R := ℚ))
      (pair.firstProfile.pair_index.trans pair.firstProfile.single_index.symm)
  rw [first_regrown_retained pair hValid hPosition path, hIndex]

/-- **Figure 38, gluing I at `A₀`: `σ⁽¹⁾(J_{A₀},1) = c_h/(k₂+1)`** -- the row
is Figure 38's `h = h(e₂) = h(e₃)` and the index is `k₃ = k₂ + 1`. -/
theorem first_regrown_retained_nd2 {position : Fin 2}
    (hPosition : position = pair.firstProfile.doubleLabel)
    (hNd2 : IsDangling data pair.firstProfile.first.1) (path : StablePath data) :
    firstHalf pair hValid position path =
      (if path = secondRow pair.firstProfile then (1 : ℚ) else 0) /
        ((data.sourceEdgeIndex pair.firstProfile.second.1 : ℚ) + 1) := by
  have hIndex : (data.sourceEdgeIndex pair.firstProfile.third.1 : ℚ) =
      (data.sourceEdgeIndex pair.firstProfile.second.1 : ℚ) + 1 := by
    exact_mod_cast congrArg (Nat.cast (R := ℚ))
      (nd2_displayed_indices pair.firstProfile hNd2).2.2
  rw [first_regrown_retained pair hValid hPosition path, hIndex,
    nd2_thirdRow_eq_secondRow pair.firstProfile hNd2]

/-- The `B₀` twin of `first_regrown_retained_nd3`. -/
theorem second_regrown_retained_nd3 {position : Fin 2}
    (hPosition : other position = pair.secondProfile.doubleLabel) (path : StablePath data) :
    secondHalf pair hValid position path =
      (if path = thirdRow pair.secondProfile then (1 : ℚ) else 0) /
        ((data.sourceEdgeIndex pair.secondProfile.first.1 : ℚ) +
          (data.sourceEdgeIndex pair.secondProfile.second.1 : ℚ)) := by
  have hIndex : (data.sourceEdgeIndex pair.secondProfile.first.1 : ℚ) +
      (data.sourceEdgeIndex pair.secondProfile.second.1 : ℚ) =
      (data.sourceEdgeIndex pair.secondProfile.third.1 : ℚ) := by
    exact_mod_cast congrArg (Nat.cast (R := ℚ))
      (pair.secondProfile.pair_index.trans pair.secondProfile.single_index.symm)
  rw [second_regrown_retained pair hValid hPosition path, hIndex]

/-- The `B₀` twin of `first_regrown_retained_nd2`. -/
theorem second_regrown_retained_nd2 {position : Fin 2}
    (hPosition : other position = pair.secondProfile.doubleLabel)
    (hNd2 : IsDangling data pair.secondProfile.first.1) (path : StablePath data) :
    secondHalf pair hValid position path =
      (if path = secondRow pair.secondProfile then (1 : ℚ) else 0) /
        ((data.sourceEdgeIndex pair.secondProfile.second.1 : ℚ) + 1) := by
  have hIndex : (data.sourceEdgeIndex pair.secondProfile.third.1 : ℚ) =
      (data.sourceEdgeIndex pair.secondProfile.second.1 : ℚ) + 1 := by
    exact_mod_cast congrArg (Nat.cast (R := ℚ))
      (nd2_displayed_indices pair.secondProfile hNd2).2.2
  rw [second_regrown_retained pair hValid hPosition path, hIndex,
    nd2_thirdRow_eq_secondRow pair.secondProfile hNd2]

end Evaluations


/-! ## §4  The full regrown column, Equation (10), and the receipt -/

section Columns

variable (pair : Pair data star) (hValid : data.Valid)

/-- **Equation (10)'s shape on the two halves**: `W2R1RowDescent`'s split, with
the two selected sums named. -/
theorem matrix_new_split (position : Fin 2) (path : StablePath data) :
    matrix (pair.candidate position).datum (stablePathEquiv pair hValid position path)
        (occurrenceEquiv target wall (pair.candidate position).right none) =
      firstHalf pair hValid position path + secondHalf pair hValid position path +
        LimitChainTwoBlock.backgroundColumn data wall (anchors pair) path (star.edge 0) :=
  matrix_new_split_pair pair hValid position path

/-- **`σ⁽ᵠ⁾(J_{A₀},1)` is `A₀`'s own box**, in all four of gluing I/II and
`nd2`/`nd3`. -/
theorem firstHalf_eq (position : Fin 2) (path : StablePath data) :
    firstHalf pair hValid position path = firstBox pair position path := by
  by_cases hPosition : position = pair.firstProfile.doubleLabel
  · rw [first_regrown_retained pair hValid hPosition path,
      firstBox_retained pair hPosition path]
  · by_cases hNd2 : IsDangling data pair.firstProfile.first.1
    · rw [first_regrown_resolved_nd2 pair hValid hPosition hNd2 path,
        firstBox_resolved_nd2 pair hPosition hNd2 path]
    · rw [first_regrown_resolved_nd3 pair hValid hPosition hNd2 path,
        firstBox_resolved_nd3 pair hPosition hNd2 path]

/-- **`σ⁽ᵠ⁾(J_{B₀},1)` is `B₀`'s own box.** -/
theorem secondHalf_eq (position : Fin 2) (path : StablePath data) :
    secondHalf pair hValid position path = secondBox pair position path := by
  by_cases hPosition : other position = pair.secondProfile.doubleLabel
  · rw [second_regrown_retained pair hValid hPosition path,
      secondBox_retained pair hPosition path]
  · by_cases hNd2 : IsDangling data pair.secondProfile.first.1
    · rw [second_regrown_resolved_nd2 pair hValid hPosition hNd2 path,
        secondBox_resolved_nd2 pair hPosition hNd2 path]
    · rw [second_regrown_resolved_nd3 pair hValid hPosition hNd2 path,
        secondBox_resolved_nd3 pair hPosition hNd2 path]

/-- **`c⁽ᵠ⁾ = σ⁽ᵠ⁾(J_{A₀},1) + σ⁽ᵠ⁾(J_{B₀},1) + s`** on the member's honest
natural stable-length matrix, with both selected halves evaluated. -/
theorem matrix_new (position : Fin 2) (path : StablePath data) :
    matrix (pair.candidate position).datum (stablePathEquiv pair hValid position path)
        (occurrenceEquiv target wall (pair.candidate position).right none) =
      newColumn pair position path := by
  rw [matrix_new_split pair hValid position path, firstHalf_eq, secondHalf_eq]
  rfl

/-- **Equation (10) of Part I on the two actual members' honest matrices**:
`c⁽¹⁾ + c⁽²⁾ = σ₀(2) + σ₀(3)`, on every incoming stable row, with unit
weights. -/
theorem equation_ten (path : StablePath data) :
    matrix (pair.candidate 0).datum (stablePathEquiv pair hValid 0 path)
          (occurrenceEquiv target wall (pair.candidate 0).right none) +
        matrix (pair.candidate 1).datum (stablePathEquiv pair hValid 1 path)
          (occurrenceEquiv target wall (pair.candidate 1).right none) =
      matrix data path (star.edge 0) + matrix data path (star.edge 1) := by
  rw [matrix_new pair hValid 0 path, matrix_new pair hValid 1 path]
  exact newColumn_sum pair hValid path

/-! ### The inhabitant -/

/-- **`W2R1CommonBalance.LimitColumns` is inhabited.**  The row field is the
proved geometric bijection `W2R1RowDescent.stablePathEquiv`, the retained
field is `matrix_retained`, and the regrown field is Figures 37 and 38's four
boxes plus `s`. -/
noncomputable def limitColumns : W2R1CommonBalance.LimitColumns pair where
  row := fun position ↦ stablePathEquiv pair hValid position
  retained := fun position path place ↦ matrix_retained pair hValid position path place
  regrown := fun position path ↦ matrix_new pair hValid position path

include hValid in
/-- **Non-vacuity.**  Every actual `{w2-r1}` datum inhabits the receipt, so
nothing downstream of it is vacuous. -/
theorem nonempty_limitColumns : Nonempty (W2R1CommonBalance.LimitColumns pair) :=
  ⟨limitColumns pair hValid⟩

@[simp] theorem limitColumns_row (position : Fin 2) :
    (limitColumns pair hValid).row position = stablePathEquiv pair hValid position := rfl

end Columns

/-! ## §5  The unconditional statements -/

noncomputable local instance : DecidableEq (Option target.edges) := Classical.decEq _

section Closure

variable (pair : Pair data star) (input : W2SourceInput data star)

/-- **Equation (10) for the two actual members, unconditionally**: the sum of
the two honest square determinants vanishes.  Neither member is assumed
nonsingular and the unit weights are derived. -/
theorem canonical_determinant_balance :
    (1 : ℚ) * ((limitColumns pair input.valid).canonicalMatrix input 0).det +
        (1 : ℚ) * ((limitColumns pair input.valid).canonicalMatrix input 1).det = 0 :=
  (limitColumns pair input.valid).canonical_determinant_balance input

/-- **Equation (10) as a positive balance**, unconditionally. -/
theorem canonical_positiveBalance :
    BalancingValencyTwo.PositiveBalance ![(1 : ℚ), (1 : ℚ)]
      (fun position ↦ ((limitColumns pair input.valid).canonicalMatrix input position).det) :=
  (limitColumns pair input.valid).positiveBalance input.valid
    ((limitColumns pair input.valid).canonicalInitialLabelling input)

/-- **The honest presented family of Equation (10)'s two members**,
unconditionally: its matrices are the honest
`GluingDatum.LengthMatrixPresentation.matrix` of a `StableLengthMatrixLabelling`
on the members' real data, not of a presentation built from supplied path
lists. -/
noncomputable def canonicalPresentedFamily :
    BalancedGlobal.PresentedFamily (coordinate := Option target.edges) 2 data wall :=
  (limitColumns pair input.valid).canonicalPresentedFamily input

theorem canonicalPresentedFamily_candidate (position : Fin 2) :
    (canonicalPresentedFamily pair input).candidate position = pair.candidate position := rfl

theorem canonicalPresentedFamily_matrix_is_honest (position : Fin 2) :
    GluingDatum.LengthMatrixPresentation.matrix
        ((canonicalPresentedFamily pair input).presentation position) =
      (limitColumns pair input.valid).canonicalMatrix input position := rfl

/-- Any nonsingular chosen member of the pair has an actual valid
opposite-sign partner. -/
theorem exists_valid_opposite (incoming : Fin 2)
    (hIncoming : ((limitColumns pair input.valid).canonicalMatrix input incoming).det ≠ 0) :
    ∃ outgoing, (pair.candidate outgoing).datum.Valid ∧
      ((limitColumns pair input.valid).canonicalMatrix input incoming).det *
        ((limitColumns pair input.valid).canonicalMatrix input outgoing).det < 0 :=
  (limitColumns pair input.valid).exists_valid_opposite input.valid
    ((limitColumns pair input.valid).canonicalInitialLabelling input) incoming hIncoming

end Closure

end DraismaVargas.LocalCases.W2R1LimitMatrix
