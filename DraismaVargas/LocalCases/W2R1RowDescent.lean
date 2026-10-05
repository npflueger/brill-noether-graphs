module

public import DraismaVargas.LocalCases.W2R1StableLift

@[expose] public section

/-!
# Figures 37 and 38's row descent, at **both** blocks

Source: Draisma--Vargas Part I (arXiv:1909.12924), Section 6, Case `{w2-r1}`,
Figures 37 and 38, and Equation (10).

`W2R1StableLift` reads Equation (10)'s member as `LimitChainTwoBlock.LiftData`
over the anchor set `{A₀, B₀}` and produces the induced stable-row map.  This
module completes the two-block `SelectedData`: the representative of each
regrown occurrence above each of the two blocks, and the complete surviving
star at every divalent expanded endpoint there.  With it come the reverse row
assignment, the row **equivalence** `stablePathEquiv`, the retained columns
`matrix_retained` and Equation (10)'s split of the regrown column,
`matrix_new_split_pair`.

## The representative, and why the core's shape is relaxed

Above a ramification-one block a member is *retained* (`position = double`,
Figure 37 gluing I) or *resolved* (`position ≠ double`, gluing II).

* retained: one regrown occurrence `e'` over the whole block, joining `e₃`'s
  row, so the representative is `e₃` throughout the block;
* resolved: two regrown occurrences, `e''` over `e₂`'s class joining `e₂`'s
  row and `e'` over `e₁`'s class joining `e₁`'s row in `nd3`; in `nd2` that
  `e'` is pruned with `e₁`, so the representative there is any survivor and
  `e₃` is taken.

`LimitChainCore.SelectedData` asks a divalent selected endpoint to carry a
regrown occurrence **and its own representative**.  The retained member in
`nd2` violates that: its two divalent endpoints above one block carry the
*same* regrown occurrence with *different* old partners, `e₃` on the single
side and `e₂` on the doubled one.  `LimitChainTwoBlock.SelectedData` therefore
asks only that the old partner lie in the representative's **incoming** row,
and `W2R1SourceProfile.SourceProfile.nd2_stablePath_eq` -- `e₂` and `e₃` share
an incoming row in `nd2` -- is exactly the receipt.

## What is **not** done here

The limit matrices' *evaluation*: the regrown entries `σ⁽¹⁾(J_{A₀},1) =
c_h/(k₂+1)`, `σ⁽²⁾(J_{A₀},1) = c_h/k₂` and their `B₀` twins, and Equation (10)
itself, are in `W2R1LimitMatrix`, which evaluates each of the two selected sums
of `matrix_new_split_pair` with `SelectedData.selected_set` and the profile's
indices.  `matrix_new_split_pair` below is the display's shape.

Also not done here: the stable incidence graph.  `LimitChainTwoBlock.GraphData`
is the structure, and `branch_ne_of_side_ne` discharges its one genuinely new
field from `W2R1StableGraph.branch_side_ne`; the per-anchor `selectedFlag` at
each of the member's two branch vertices and the `selected_not_branch` bound at
the other endpoints above each block are supplied in `W2R1GraphData`.
-/

namespace DraismaVargas.LocalCases.W2R1RowDescent

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open ResolutionM11
open ResolutionAwayFromWall StableSourceMatrix
open W2R1SourceCandidates
open W2R1StableGraph
open W2R1StableLift
open LimitChainTwoBlock (IsSelected SelectedData isSelected_of_rel)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## §1  The nd-trichotomy, read off the surviving valency -/

section Block

variable {block : WallBlock data wall} (member : BlockMember data star block)

theorem nd2_of_valency_eq_two
    (hValency : nonDanglingValency data (WallBlock.sourceVertex data wall block) = 2) :
    IsDangling data member.profile.first.1 := by
  rcases member.nd_cases with ⟨hThree, _⟩ | ⟨_, hNd2, _, _⟩
  · rw [hThree] at hValency; exact absurd hValency (by omega)
  · exact hNd2

theorem nd3_of_valency_ne_two
    (hValency : nonDanglingValency data (WallBlock.sourceVertex data wall block) ≠ 2) :
    ¬ IsDangling data member.profile.first.1 := by
  rcases member.nd_cases with ⟨_, hNd3⟩ | ⟨hTwo, _, _, _⟩
  · exact hNd3
  · exact absurd hTwo hValency

theorem valency_eq_two_of_nd2 (hNd2 : IsDangling data member.profile.first.1) :
    nonDanglingValency data (WallBlock.sourceVertex data wall block) = 2 := by
  rcases member.nd_cases with ⟨_, hNd3⟩ | ⟨hTwo, _, _, _⟩
  · exact absurd hNd2 hNd3
  · exact hTwo

theorem valency_ne_two_of_nd3 (hNd3 : ¬ IsDangling data member.profile.first.1) :
    nonDanglingValency data (WallBlock.sourceVertex data wall block) ≠ 2 := by
  rcases member.nd_cases with ⟨hThree, _⟩ | ⟨_, hNd2, _, _⟩
  · rw [hThree]; omega
  · exact absurd hNd2 hNd3

/-! ## §2  The representative of a regrown occurrence above one block

Every branch of the definition names a **surviving** incoming occurrence, and
the discriminators are decidable: which member the block sees, which of `e₁`'s
and `e₂`'s classes a sheet lies in, and the block's own surviving valency. -/

/-- The incoming occurrence a member's regrown occurrence above the block
represents. -/
noncomputable def rep (sheet : Fin degree) : data.SourceEdge :=
  if member.position = member.double then member.profile.third.1
  else if (doublePartition member.profile.toOccurrenceProfile).Rel
      (secondSheet member.profile.toOccurrenceProfile) sheet then member.profile.second.1
  else if nonDanglingValency data (WallBlock.sourceVertex data wall block) = 2 then
    member.profile.third.1
  else member.profile.first.1

theorem rep_retained (hPosition : member.position = member.double) (sheet : Fin degree) :
    rep member sheet = member.profile.third.1 := ite_eq_left hPosition

theorem rep_resolved_second (hPosition : member.position ≠ member.double) {sheet : Fin degree}
    (hRel : (doublePartition member.profile.toOccurrenceProfile).Rel
      (secondSheet member.profile.toOccurrenceProfile) sheet) :
    rep member sheet = member.profile.second.1 := by
  unfold rep
  rw [ite_eq_right hPosition, ite_eq_left hRel]

theorem rep_resolved_first_nd2 (hPosition : member.position ≠ member.double)
    {sheet : Fin degree}
    (hRel : ¬ (doublePartition member.profile.toOccurrenceProfile).Rel
      (secondSheet member.profile.toOccurrenceProfile) sheet)
    (hNd2 : IsDangling data member.profile.first.1) :
    rep member sheet = member.profile.third.1 := by
  unfold rep
  rw [ite_eq_right hPosition, ite_eq_right hRel, ite_eq_left (valency_eq_two_of_nd2 member hNd2)]

theorem rep_resolved_first_nd3 (hPosition : member.position ≠ member.double)
    {sheet : Fin degree}
    (hRel : ¬ (doublePartition member.profile.toOccurrenceProfile).Rel
      (secondSheet member.profile.toOccurrenceProfile) sheet)
    (hNd3 : ¬ IsDangling data member.profile.first.1) :
    rep member sheet = member.profile.first.1 := by
  unfold rep
  rw [ite_eq_right hPosition, ite_eq_right hRel, ite_eq_right (valency_ne_two_of_nd3 member hNd3)]

/-- **Every branch of the representative survives.** -/
theorem rep_survives (sheet : Fin degree) : ¬ IsDangling data (rep member sheet) := by
  by_cases hPosition : member.position = member.double
  · rw [rep_retained member hPosition]
    exact member.profile.third_survives
  · by_cases hRel : (doublePartition member.profile.toOccurrenceProfile).Rel
      (secondSheet member.profile.toOccurrenceProfile) sheet
    · rw [rep_resolved_second member hPosition hRel]
      exact member.profile.second_survives
    · by_cases hNd2 : IsDangling data member.profile.first.1
      · rw [rep_resolved_first_nd2 member hPosition hRel hNd2]
        exact member.profile.third_survives
      · rw [rep_resolved_first_nd3 member hPosition hRel hNd2]
        exact hNd2

/-- Sheets of the block carrying one regrown occurrence carry one
representative. -/
theorem rep_congr {first second : Fin degree}
    (hFirst : (data.vertexPartition wall).Rel block.1 first)
    (hEq : member.candidate.newSourceEdge first = member.candidate.newSourceEdge second) :
    rep member first = rep member second := by
  by_cases hPosition : member.position = member.double
  · rw [rep_retained member hPosition, rep_retained member hPosition]
  · have hDouble := (member.resolved_new_eq_iff hPosition hFirst second).mp hEq
    by_cases hRel : (doublePartition member.profile.toOccurrenceProfile).Rel
        (secondSheet member.profile.toOccurrenceProfile) first
    · rw [rep_resolved_second member hPosition hRel,
        rep_resolved_second member hPosition (hRel.trans hDouble)]
    · have hRel' : ¬ (doublePartition member.profile.toOccurrenceProfile).Rel
          (secondSheet member.profile.toOccurrenceProfile) second :=
        fun h ↦ hRel (h.trans hDouble.symm)
      by_cases hNd2 : IsDangling data member.profile.first.1
      · rw [rep_resolved_first_nd2 member hPosition hRel hNd2,
          rep_resolved_first_nd2 member hPosition hRel' hNd2]
      · rw [rep_resolved_first_nd3 member hPosition hRel hNd2,
          rep_resolved_first_nd3 member hPosition hRel' hNd2]

/-! ## §3  Every surviving regrown occurrence above the block lies in its
representative's row -/

theorem new_stablePath_eq_rep {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet)
    (hSurvives : ¬ IsDangling member.candidate.datum
      (member.candidate.newSourceEdge sheet))
    (hRep : ¬ IsDangling member.candidate.datum
      (member.candidate.oldSourceEdge (rep member sheet))) :
    NonDanglingEdge.stablePath
        (⟨member.candidate.newSourceEdge sheet, hSurvives⟩ :
          NonDanglingEdge member.candidate.datum) =
      NonDanglingEdge.stablePath
        (⟨member.candidate.oldSourceEdge (rep member sheet), hRep⟩ :
          NonDanglingEdge member.candidate.datum) := by
  by_cases hPosition : member.position = member.double
  · refine Eq.trans (member.retained_new_stablePath_eq hPosition hSheet) ?_
    exact congrArg NonDanglingEdge.stablePath (Subtype.ext
      (congrArg member.candidate.oldSourceEdge (rep_retained member hPosition sheet).symm))
  · by_cases hRel : (doublePartition member.profile.toOccurrenceProfile).Rel
        (secondSheet member.profile.toOccurrenceProfile) sheet
    · have hNew : member.candidate.newSourceEdge sheet =
          member.candidate.newSourceEdge (secondSheet member.profile.toOccurrenceProfile) :=
        (member.resolved_new_eq_iff hPosition hSheet _).mpr hRel.symm
      refine Eq.trans (congrArg NonDanglingEdge.stablePath
        (Subtype.ext hNew : (⟨member.candidate.newSourceEdge sheet, hSurvives⟩ :
          NonDanglingEdge member.candidate.datum) =
          ⟨member.candidate.newSourceEdge (secondSheet member.profile.toOccurrenceProfile),
            member.resolved_new_second_survives hPosition⟩)) ?_
      refine Eq.trans (member.resolved_new_second_stablePath_eq hPosition) ?_
      exact congrArg NonDanglingEdge.stablePath (Subtype.ext
        (congrArg member.candidate.oldSourceEdge
          (rep_resolved_second member hPosition hRel).symm))
    · have hFirstRel : (doublePartition member.profile.toOccurrenceProfile).Rel
          (firstSheet member.profile.toOccurrenceProfile) sheet := by
        rcases doublePartition_covers member.profile.toOccurrenceProfile sheet hSheet with h | h
        · exact h
        · exact absurd h hRel
      have hNew : member.candidate.newSourceEdge sheet =
          member.candidate.newSourceEdge (firstSheet member.profile.toOccurrenceProfile) :=
        (member.resolved_new_eq_iff hPosition hSheet _).mpr hFirstRel.symm
      by_cases hNd2 : IsDangling data member.profile.first.1
      · exfalso
        refine hSurvives ?_
        rw [hNew]
        by_contra hAlive
        exact ((member.resolved_new_first_survives_iff hPosition).mp hAlive) hNd2
      · refine Eq.trans (congrArg NonDanglingEdge.stablePath
          (Subtype.ext hNew : (⟨member.candidate.newSourceEdge sheet, hSurvives⟩ :
            NonDanglingEdge member.candidate.datum) =
            ⟨member.candidate.newSourceEdge (firstSheet member.profile.toOccurrenceProfile),
              (member.resolved_new_first_survives_iff hPosition).mpr hNd2⟩)) ?_
        refine Eq.trans (member.resolved_new_first_stablePath_eq hPosition hNd2) ?_
        exact congrArg NonDanglingEdge.stablePath (Subtype.ext
          (congrArg member.candidate.oldSourceEdge
            (rep_resolved_first_nd3 member hPosition hRel hNd2).symm))

/-! ## §4  The complete surviving star at a divalent endpoint above the block -/

/-- **The variant's selected-pair clause, at one block and one side.**  The old
partner is `e₃` or `e₂`, and in `nd2` those share an incoming row. -/
theorem selected_pair (label : Fin 2) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet)
    (hValency : nonDanglingValency member.candidate.datum
      (member.vertex label sheet) = 2) :
    ∃ (other : Fin degree) (old : data.SourceEdge) (hOld : ¬ IsDangling data old),
      (data.vertexPartition wall).Rel block.1 other ∧
      nonDanglingIncident member.candidate.datum (member.vertex label sheet) =
        {member.candidate.newSourceEdge other, member.candidate.oldSourceEdge old} ∧
      NonDanglingEdge.stablePath (⟨old, hOld⟩ : NonDanglingEdge data) =
        NonDanglingEdge.stablePath
          (⟨rep member other, rep_survives member other⟩ : NonDanglingEdge data) := by
  have hLabel : label = member.double ∨ label = member.single := by
    have := member.double_ne_single
    omega
  by_cases hPosition : member.position = member.double
  · rcases hLabel with rfl | rfl
    · by_cases hNd2 : IsDangling data member.profile.first.1
      · refine ⟨sheet, member.profile.second.1, member.profile.second_survives, hSheet,
          ?_, ?_⟩
        · rw [member.retained_nonDanglingIncident_double_nd2 hPosition hNd2 hSheet]
          exact Finset.pair_comm _ _
        · exact Eq.trans (member.profile.nd2_stablePath_eq (valency_eq_two_of_nd2 member hNd2))
            (congrArg NonDanglingEdge.stablePath
              (Subtype.ext (rep_retained member hPosition sheet).symm))
      · rw [member.retained_nonDanglingValency_double_nd3 hPosition hNd2 hSheet] at hValency
        exact absurd hValency (by omega)
    · refine ⟨sheet, member.profile.third.1, member.profile.third_survives, hSheet, ?_, ?_⟩
      · exact member.retained_nonDanglingIncident_single hPosition hSheet
      · exact congrArg NonDanglingEdge.stablePath
          (Subtype.ext (rep_retained member hPosition sheet).symm)
  · rcases hLabel with rfl | rfl
    · rcases doublePartition_covers member.profile.toOccurrenceProfile sheet hSheet with
        hRel | hRel
      · by_cases hNd2 : IsDangling data member.profile.first.1
        · exfalso
          rw [← member.resolved_double_vertex_eq' hPosition
            (firstSheet_rel member.profile.toOccurrenceProfile) hRel,
            ← card_nonDanglingIncident,
            member.resolved_nonDanglingIncident_first_nd2 hPosition hNd2] at hValency
          exact absurd hValency (by simp)
        · refine ⟨firstSheet member.profile.toOccurrenceProfile, member.profile.first.1,
            hNd2, firstSheet_rel member.profile.toOccurrenceProfile, ?_, ?_⟩
          · rw [← member.resolved_double_vertex_eq' hPosition
              (firstSheet_rel member.profile.toOccurrenceProfile) hRel]
            exact member.resolved_nonDanglingIncident_first_nd3 hPosition hNd2
          · exact congrArg NonDanglingEdge.stablePath (Subtype.ext
              (rep_resolved_first_nd3 member hPosition
                (fun h ↦ doublePartition_separate member.profile.toOccurrenceProfile h.symm)
                hNd2).symm)
      · refine ⟨secondSheet member.profile.toOccurrenceProfile, member.profile.second.1,
          member.profile.second_survives,
          secondSheet_rel member.profile.toOccurrenceProfile, ?_, ?_⟩
        · rw [← member.resolved_double_vertex_eq' hPosition
            (secondSheet_rel member.profile.toOccurrenceProfile) hRel]
          exact member.resolved_nonDanglingIncident_second hPosition
        · exact congrArg NonDanglingEdge.stablePath (Subtype.ext
            (rep_resolved_second member hPosition
              (((doublePartition member.profile.toOccurrenceProfile).rel_iff _ _).mpr rfl)).symm)
    · by_cases hNd2 : IsDangling data member.profile.first.1
      · refine ⟨secondSheet member.profile.toOccurrenceProfile, member.profile.third.1,
          member.profile.third_survives,
          secondSheet_rel member.profile.toOccurrenceProfile, ?_, ?_⟩
        · rw [member.resolved_nonDanglingIncident_single_nd2 hPosition hNd2 hSheet]
          exact Finset.pair_comm _ _
        · exact Eq.trans
            (member.profile.nd2_stablePath_eq (valency_eq_two_of_nd2 member hNd2)).symm
            (congrArg NonDanglingEdge.stablePath (Subtype.ext
              (rep_resolved_second member hPosition
                (((doublePartition member.profile.toOccurrenceProfile).rel_iff _ _).mpr
                  rfl)).symm))
      · rw [member.resolved_nonDanglingValency_single_nd3 hPosition hNd2 hSheet] at hValency
        exact absurd hValency (by omega)

end Block

/-! ## §5  The two blocks together: the member's two-block selected data -/

/-- The canonical sheet of a regrown occurrence lies in the wall block of the
sheet naming it, so a regrown occurrence never spans `A₀` and `B₀`. -/
theorem newSourceEdge_sheet_rel_iff (C : BalancedGlobal.Candidate target degree data wall)
    (anchor sheet : Fin degree) :
    (data.vertexPartition wall).Rel anchor (C.newSourceEdge sheet).1.2 ↔
      (data.vertexPartition wall).Rel anchor sheet := by
  rw [BalancedGlobal.Candidate.newSourceEdge_sheet]
  have hRefines : (LimitChainCore.pasted C).right.Refines (data.vertexPartition wall) :=
    SheetPartition.IsJoin.right_refines (LocalResolution.paste_contracts
      (data.vertexPartition wall) C.resolution C.contracts)
  have hRel : (data.vertexPartition wall).Rel sheet
      ((LimitChainCore.pasted C).newEdge.repr sheet) :=
    hRefines.rel ((LimitChainCore.pasted C).edge_refines_right.rel
      ((LimitChainCore.pasted C).newEdge.rel_repr_right sheet))
  exact ⟨fun h ↦ h.trans hRel.symm, fun h ↦ h.trans hRel⟩

theorem rel_iff_of_newSourceEdge_eq (C : BalancedGlobal.Candidate target degree data wall)
    (anchor : Fin degree) {first second : Fin degree}
    (hEq : C.newSourceEdge first = C.newSourceEdge second) :
    (data.vertexPartition wall).Rel anchor first ↔
      (data.vertexPartition wall).Rel anchor second := by
  rw [← newSourceEdge_sheet_rel_iff C anchor first,
    ← newSourceEdge_sheet_rel_iff C anchor second, hEq]

variable (pair : Pair data star) (hValid : data.Valid)

/-- The representative of a regrown occurrence above either block. -/
noncomputable def selectedRep (position : Fin 2) (sheet : Fin degree) : data.SourceEdge :=
  if (data.vertexPartition wall).Rel pair.first.1 sheet then
    rep (firstMember pair hValid position) sheet
  else rep (secondMember pair hValid position) sheet

theorem selectedRep_first (position : Fin 2) {sheet : Fin degree}
    (hRel : (data.vertexPartition wall).Rel pair.first.1 sheet) :
    selectedRep pair hValid position sheet = rep (firstMember pair hValid position) sheet :=
  ite_eq_left hRel

theorem selectedRep_second (position : Fin 2) {sheet : Fin degree}
    (hRel : ¬ (data.vertexPartition wall).Rel pair.first.1 sheet) :
    selectedRep pair hValid position sheet = rep (secondMember pair hValid position) sheet :=
  ite_eq_right hRel

theorem selectedRep_survives (position : Fin 2) (sheet : Fin degree) :
    ¬ IsDangling data (selectedRep pair hValid position sheet) := by
  by_cases hRel : (data.vertexPartition wall).Rel pair.first.1 sheet
  · rw [selectedRep_first pair hValid position hRel]
    exact rep_survives _ sheet
  · rw [selectedRep_second pair hValid position hRel]
    exact rep_survives _ sheet

theorem selectedRep_congr (position : Fin 2) (first second : Fin degree)
    (hFirst : IsSelected data wall (anchors pair) first)
    (hEq : (pair.candidate position).newSourceEdge first =
      (pair.candidate position).newSourceEdge second) :
    selectedRep pair hValid position first = selectedRep pair hValid position second := by
  by_cases hRel : (data.vertexPartition wall).Rel pair.first.1 first
  · rw [selectedRep_first pair hValid position hRel,
      selectedRep_first pair hValid position
        ((rel_iff_of_newSourceEdge_eq (pair.candidate position) pair.first.1 hEq).mp hRel)]
    exact rep_congr (firstMember pair hValid position) hRel hEq
  · have hSecond : (data.vertexPartition wall).Rel pair.second.1 first := by
      rcases (isSelected_iff pair first).mp hFirst with h | h
      · exact absurd h hRel
      · exact h
    rw [selectedRep_second pair hValid position hRel,
      selectedRep_second pair hValid position
        (fun h ↦ hRel
          ((rel_iff_of_newSourceEdge_eq (pair.candidate position) pair.first.1 hEq).mpr h))]
    exact rep_congr (secondMember pair hValid position) hSecond hEq

theorem selected_new_stablePath (position : Fin 2) (sheet : Fin degree)
    (hSel : IsSelected data wall (anchors pair) sheet)
    (hSurvives : ¬ IsDangling (pair.candidate position).datum
      ((pair.candidate position).newSourceEdge sheet))
    (hRep : ¬ IsDangling (pair.candidate position).datum
      ((pair.candidate position).oldSourceEdge (selectedRep pair hValid position sheet))) :
    NonDanglingEdge.stablePath
        (⟨(pair.candidate position).newSourceEdge sheet, hSurvives⟩ :
          NonDanglingEdge (pair.candidate position).datum) =
      NonDanglingEdge.stablePath
        (⟨(pair.candidate position).oldSourceEdge (selectedRep pair hValid position sheet),
          hRep⟩ : NonDanglingEdge (pair.candidate position).datum) := by
  by_cases hRel : (data.vertexPartition wall).Rel pair.first.1 sheet
  · refine Eq.trans (new_stablePath_eq_rep (firstMember pair hValid position) hRel hSurvives
      (ResolutionSurvival.not_isDangling_oldSourceEdge _ hValid.1 _
        (rep_survives (firstMember pair hValid position) sheet))) ?_
    exact congrArg NonDanglingEdge.stablePath (Subtype.ext
      (congrArg (pair.candidate position).oldSourceEdge
        (selectedRep_first pair hValid position hRel).symm))
  · have hSecond : (data.vertexPartition wall).Rel pair.second.1 sheet := by
      rcases (isSelected_iff pair sheet).mp hSel with h | h
      · exact absurd h hRel
      · exact h
    refine Eq.trans (new_stablePath_eq_rep (secondMember pair hValid position) hSecond hSurvives
      (ResolutionSurvival.not_isDangling_oldSourceEdge _ hValid.1 _
        (rep_survives (secondMember pair hValid position) sheet))) ?_
    exact congrArg NonDanglingEdge.stablePath (Subtype.ext
      (congrArg (pair.candidate position).oldSourceEdge
        (selectedRep_second pair hValid position hRel).symm))

/-- The variant's selected-pair clause, at either block and either side. -/
theorem selected_pair_side (position : Fin 2) (label : Fin 2) (sheet : Fin degree)
    (hSel : IsSelected data wall (anchors pair) sheet)
    (hValency : nonDanglingValency (pair.candidate position).datum
      ((pair.candidate position).datum.sourceEndpoint
        (LimitChainCore.wallSide target wall (side label)) sheet) = 2) :
    ∃ (other : Fin degree) (old : data.SourceEdge) (hOld : ¬ IsDangling data old),
      IsSelected data wall (anchors pair) other ∧
      nonDanglingIncident (pair.candidate position).datum
          ((pair.candidate position).datum.sourceEndpoint
            (LimitChainCore.wallSide target wall (side label)) sheet) =
        {(pair.candidate position).newSourceEdge other,
          (pair.candidate position).oldSourceEdge old} ∧
      NonDanglingEdge.stablePath (⟨old, hOld⟩ : NonDanglingEdge data) =
        NonDanglingEdge.stablePath
          (⟨selectedRep pair hValid position other,
            selectedRep_survives pair hValid position other⟩ : NonDanglingEdge data) := by
  by_cases hRel : (data.vertexPartition wall).Rel pair.first.1 sheet
  · obtain ⟨other, old, hOld, hOtherRel, hStar, hRow⟩ :=
      selected_pair (firstMember pair hValid position) label hRel hValency
    refine ⟨other, old, hOld, isSelected_of_rel (first_mem_anchors pair) hOtherRel, hStar, ?_⟩
    exact hRow.trans (congrArg NonDanglingEdge.stablePath
      (Subtype.ext (selectedRep_first pair hValid position hOtherRel).symm))
  · have hSecond : (data.vertexPartition wall).Rel pair.second.1 sheet := by
      rcases (isSelected_iff pair sheet).mp hSel with h | h
      · exact absurd h hRel
      · exact h
    obtain ⟨other, old, hOld, hOtherRel, hStar, hRow⟩ :=
      selected_pair (secondMember pair hValid position) label hSecond hValency
    refine ⟨other, old, hOld, isSelected_of_rel (second_mem_anchors pair) hOtherRel, hStar, ?_⟩
    refine hRow.trans (congrArg NonDanglingEdge.stablePath
      (Subtype.ext (selectedRep_second pair hValid position ?_).symm))
    exact pair.not_rel_first_of_rel_second hOtherRel

/-- **Equation (10)'s member, read as two-block selected data.** -/
noncomputable def selectedData (position : Fin 2) :
    SelectedData data wall (anchors pair) where
  toLiftData := liftData pair hValid position
  selectedRep := selectedRep pair hValid position
  selectedRep_survives := fun sheet _ ↦ selectedRep_survives pair hValid position sheet
  selectedRep_congr := fun first second hFirst _ hEq ↦
    selectedRep_congr pair hValid position first second hFirst hEq
  selected_new_stablePath := fun sheet hSel hSurvives hRep ↦
    selected_new_stablePath pair hValid position sheet hSel hSurvives hRep
  selected_left_pair := by
    intro sheet hSel hValency
    obtain ⟨other, old, hOld, hOther, hStar, hRow⟩ :=
      selected_pair_side pair hValid position 0 sheet hSel hValency
    exact ⟨other, old, hOther, hOld, hStar, hRow⟩
  selected_right_pair := by
    intro sheet hSel hValency
    obtain ⟨other, old, hOld, hOther, hStar, hRow⟩ :=
      selected_pair_side pair hValid position 1 sheet hSel hValency
    exact ⟨other, old, hOther, hOld, hStar, hRow⟩

@[simp] theorem selectedData_candidate (position : Fin 2) :
    (selectedData pair hValid position).candidate = pair.candidate position := rfl

/-! ## §6  The row descent, the row equivalence and the retained columns -/

/-- **Equation (10)'s stable-row equivalence**: the induced row map of the
member is a bijection, with the explicit geometric inverse
`SelectedData.stablePathDescend`. -/
noncomputable def stablePathEquiv (position : Fin 2) :
    StablePath data ≃ StablePath (pair.candidate position).datum :=
  (selectedData pair hValid position).stablePathEquiv

theorem stablePathLift_surjective (position : Fin 2) :
    Function.Surjective (stablePathLift pair hValid position) :=
  (selectedData pair hValid position).stablePathLift_surjective

theorem stablePathLift_injective (position : Fin 2) :
    Function.Injective (stablePathLift pair hValid position) :=
  (selectedData pair hValid position).stablePathLift_injective

@[simp] theorem stablePathEquiv_mk (position : Fin 2) (edge : NonDanglingEdge data) :
    stablePathEquiv pair hValid position edge.stablePath =
      (retainedEdge (pair.candidate position) hValid.1 edge).stablePath := rfl

/-- **Every retained column of the member is the incoming wall column.** -/
theorem matrix_retained (position : Fin 2) (path : StablePath data) (place : target.edges) :
    matrix (pair.candidate position).datum (stablePathEquiv pair hValid position path)
        (occurrenceEquiv target wall (pair.candidate position).right (some place)) =
      matrix data path place :=
  (selectedData pair hValid position).matrix_retained path place

/-- **Equation (10)'s shape**: the regrown column of the member splits into a
regrown half above `A₀`, a regrown half above `B₀` and one background `s`.
This is `c⁽ⁱ⁾ = σ⁽ⁱ⁾(J_{A₀},1) + σ⁽ⁱ⁾(J_{B₀},1) + s` of Part I, in the proof of
(⋆) for Case `{w2-r1}`, before the
two selected halves are evaluated. -/
theorem matrix_new_split_pair (position : Fin 2) (path : StablePath data) :
    matrix (pair.candidate position).datum (stablePathEquiv pair hValid position path)
        (occurrenceEquiv target wall (pair.candidate position).right none) =
      (∑ edge ∈ ((selectedData pair hValid position).newOccurrences path).filter
          (fun edge ↦ (data.vertexPartition wall).Rel pair.first.1 edge.1.2),
        (1 : ℚ) / (pair.candidate position).datum.sourceEdgeIndex edge) +
      (∑ edge ∈ ((selectedData pair hValid position).newOccurrences path).filter
          (fun edge ↦ (data.vertexPartition wall).Rel pair.second.1 edge.1.2),
        (1 : ℚ) / (pair.candidate position).datum.sourceEdgeIndex edge) +
      LimitChainTwoBlock.backgroundColumn data wall (anchors pair) path (star.edge 0) :=
  (selectedData pair hValid position).matrix_new_split_pair pair.first.1 pair.second.1 rfl
    pair.separate path

end DraismaVargas.LocalCases.W2R1RowDescent
