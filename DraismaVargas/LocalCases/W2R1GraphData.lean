import DraismaVargas.LocalCases.W2R1LimitMatrix
import DraismaVargas.LocalCases.StableGraphFullDimensional

/-!
# Figures 37 and 38's stable incidence dictionaries, at **both** blocks

Source: Draisma--Vargas Part I, case `{w2-r1}`, Figures 37 and 38 and
Equation (10).

`W2R1StableGraph` proves the census; `W2R1RowDescent` the two-block
`SelectedData`; `W2R1LimitMatrix` the limit matrices.  This module supplies
the remaining half of `LimitChainTwoBlock.GraphData` -- one `selectedSide` and
one `selectedFlag` **per anchor**, plus `selected_not_branch` at every other
expanded endpoint above each block -- and with it
`LimitChainTwoBlock.GraphData.equivalence`, the stable incidence graph
equivalence of each member, and `outgoingPresentation`.

## The branch side is the member's own position, in **all four** sub-cases

`W2R1StableGraph.card_incident_side` says the expanded endpoint named by the
direction `position` carries three incidences above a ramification-one block,
and the other carries two.  So `selectedSide` is `side position` at `A₀` and
`side (other position)` at `B₀`, uniformly; `branch_ne` is then free from
`W2R1StableGraph.branch_side_ne` through
`LimitChainTwoBlock.branch_ne_of_side_ne`.

**The `nd2` sub-case is not an obstruction, and `GraphData` *is* instantiated
there.**  What is true in `nd2` is that *no expanded endpoint above the block
is trivalent*: the endpoint named by `position` has three incidences but one
of them is dangling, so its surviving valency is two
(`BlockMember.retained_nonDanglingValency_double_nd2`,
`resolved_nonDanglingValency_single_nd2`).  `GraphData` never asks the branch
vertex to be trivalent.  It asks two things, and both hold:

* `selectedFlag_star`, that the surviving star at `branchVertex anchor` is the
  **image** of the incoming surviving star at the wall vertex.  In `nd2` the
  incoming star is `{e₂, e₃}` -- `e₁` dangles -- and the branch star is a pair
  as well, so the correspondence is a bijection between two two-element stars;
* `selected_not_branch`, that every *other* endpoint above the block has
  surviving valency at most two.  In `nd2` every endpoint above the block is
  divalent or entirely pruned, so this is immediate.

That is why the whole of §6 below is uniform in the sub-case: the `nd3`/`nd2`
split appears only in *which* star equality of the census is quoted, never in
the shape of the argument.  Both members and both sub-cases have the exit.

## What the flag is

At the branch vertex the occurrences of the **other** direction are retained
and the occurrences of the branch vertex's own direction are replaced by
regrown ones:

* retained member (`position = double`, gluing I): the branch vertex is the
  doubled direction's endpoint, `e₁` and `e₂` stay, and `e₃` is replaced by the
  single regrown occurrence `e'` above the whole block;
* resolved member (`position ≠ double`, gluing II): the branch vertex is the
  single direction's endpoint, `e₃` stays, and `e₁`, `e₂` are replaced by the
  regrown occurrences `e'`, `e''` of their own classes.

`W2PGraphData.singleFlag` and `doubleFlag` are the one-block analogues and are
keyed the same way, by the occurrence's own target direction.
-/

namespace DraismaVargas.LocalCases.W2R1GraphData

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open FullDimensionalSource
open ResolutionM11
open ResolutionAwayFromWall StableSourceMatrix
open W2R1SourceCandidates
open W2R1StableGraph
open W2R1StableLift
open W2R1RowDescent
open LimitChainCore (wallSide)
open LimitChainTwoBlock (IsSelected SelectedData GraphData isSelected_of_rel)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## §1  The incoming surviving star above one ramification-one block -/

section Star

variable {block : WallBlock data wall}
  (profile : W2R1SourceProfile.SourceProfile data star block)

/-- **nd3: the wall vertex carries exactly `e₁`, `e₂`, `e₃`.** -/
theorem incoming_star_nd3 (hNd3 : ¬ IsDangling data profile.first.1) :
    nonDanglingIncident data (data.sourceEndpoint wall block.1) =
      {profile.first.1, profile.second.1, profile.third.1} := by
  classical
  ext edge
  simp only [mem_nonDanglingIncident, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨_, hIncident⟩
    rcases profile.exhaustive ⟨edge, hIncident⟩ with h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (congrArg Subtype.val h))
  · rintro (rfl | rfl | rfl)
    · exact ⟨hNd3, profile.first.2⟩
    · exact ⟨profile.second_survives, profile.second.2⟩
    · exact ⟨profile.third_survives, profile.third.2⟩

/-- **nd2: `e₁` dangles and the wall vertex carries exactly `e₂`, `e₃`.** -/
theorem incoming_star_nd2 (hNd2 : IsDangling data profile.first.1) :
    nonDanglingIncident data (data.sourceEndpoint wall block.1) =
      {profile.second.1, profile.third.1} := by
  classical
  ext edge
  simp only [mem_nonDanglingIncident, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hSurvives, hIncident⟩
    rcases profile.exhaustive ⟨edge, hIncident⟩ with h | h | h
    · refine absurd ?_ hSurvives
      rw [show edge = profile.first.1 from congrArg Subtype.val h]
      exact hNd2
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · rintro (rfl | rfl)
    · exact ⟨profile.second_survives, profile.second.2⟩
    · exact ⟨profile.third_survives, profile.third.2⟩

/-- The star is read at any sheet of the block. -/
theorem sourceEndpoint_eq {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    data.sourceEndpoint wall anchor = data.sourceEndpoint wall block.1 :=
  (LimitChainCore.sourceEndpoint_eq_of_rel data wall hAnchor).symm

end Star


/-! ## §2  The branch flag of a member at one block -/

section Flag

variable {block : WallBlock data wall} (member : BlockMember data star block)

/-- **The retained member's branch flag** (gluing I).  At the doubled
direction's endpoint `e₁` and `e₂` are retained and `e₃` is replaced by the
single regrown occurrence above the block. -/
noncomputable def retainedFlag (anchor : Fin degree) (edge : data.SourceEdge) :
    member.candidate.datum.SourceEdge :=
  if edge.1.1 = star.edge member.profile.singleLabel then
    member.candidate.newSourceEdge anchor
  else member.candidate.oldSourceEdge edge

/-- **The resolved member's branch flag** (gluing II).  At the single
direction's endpoint `e₃` is retained and `e₁`, `e₂` are replaced by the
regrown occurrences of their own classes. -/
noncomputable def resolvedFlag (edge : data.SourceEdge) :
    member.candidate.datum.SourceEdge :=
  if edge.1.1 = star.edge member.profile.doubleLabel then
    member.candidate.newSourceEdge edge.1.2
  else member.candidate.oldSourceEdge edge

/-- **The member's branch flag**, uniform in the position. -/
noncomputable def flag (anchor : Fin degree) (edge : data.SourceEdge) :
    member.candidate.datum.SourceEdge :=
  if member.position = member.double then retainedFlag member anchor edge
  else resolvedFlag member edge

theorem flag_retained (hPosition : member.position = member.double) (anchor : Fin degree)
    (edge : data.SourceEdge) : flag member anchor edge = retainedFlag member anchor edge :=
  if_pos hPosition

theorem flag_resolved (hPosition : member.position ≠ member.double) (anchor : Fin degree)
    (edge : data.SourceEdge) : flag member anchor edge = resolvedFlag member edge :=
  if_neg hPosition

theorem retainedFlag_single (anchor : Fin degree) {edge : data.SourceEdge}
    (hTarget : edge.1.1 = star.edge member.profile.singleLabel) :
    retainedFlag member anchor edge = member.candidate.newSourceEdge anchor := if_pos hTarget

theorem retainedFlag_double (anchor : Fin degree) {edge : data.SourceEdge}
    (hTarget : edge.1.1 = star.edge member.profile.doubleLabel) :
    retainedFlag member anchor edge = member.candidate.oldSourceEdge edge :=
  if_neg (fun h ↦ member.profile.labels_ne (star.edge_injective (hTarget.symm.trans h)))

theorem resolvedFlag_double {edge : data.SourceEdge}
    (hTarget : edge.1.1 = star.edge member.profile.doubleLabel) :
    resolvedFlag member edge = member.candidate.newSourceEdge edge.1.2 := if_pos hTarget

theorem resolvedFlag_single {edge : data.SourceEdge}
    (hTarget : edge.1.1 = star.edge member.profile.singleLabel) :
    resolvedFlag member edge = member.candidate.oldSourceEdge edge :=
  if_neg (fun h ↦ member.profile.labels_ne (star.edge_injective (hTarget.symm.trans h)).symm)

/-- The member's branch vertex above the block, at any of its sheets. -/
theorem branch_vertex_retained (hPosition : member.position = member.double)
    (anchor : Fin degree) :
    member.vertex member.position anchor = member.vertex member.double anchor :=
  congrArg (fun label ↦ member.vertex label anchor) hPosition

theorem branch_vertex_resolved (hPosition : member.position ≠ member.double)
    (anchor : Fin degree) :
    member.vertex member.position anchor = member.vertex member.single anchor :=
  congrArg (fun label ↦ member.vertex label anchor) (member.position_eq_single hPosition)

/-! ### The star at the branch vertex is the image of the incoming star -/

/-- **Gluing I, `nd3`.** -/
theorem flag_star_retained_nd3 (hPosition : member.position = member.double)
    (hNd3 : ¬ IsDangling data member.profile.first.1) {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    nonDanglingIncident member.candidate.datum (member.vertex member.position anchor) =
      (nonDanglingIncident data (data.sourceEndpoint wall anchor)).image
        (flag member anchor) := by
  classical
  rw [branch_vertex_retained member hPosition anchor,
    member.retained_nonDanglingIncident_double_nd3 hPosition hNd3 hAnchor,
    sourceEndpoint_eq hAnchor, incoming_star_nd3 member.profile hNd3]
  simp only [Finset.image_insert, Finset.image_singleton,
    flag_retained member hPosition,
    retainedFlag_double member anchor member.profile.first_target,
    retainedFlag_double member anchor member.profile.second_target,
    retainedFlag_single member anchor member.profile.third_target]

/-- **Gluing I, `nd2`.**  The incoming star is the pair `{e₂, e₃}` and the
branch star is the pair `{old e₂, e'}`. -/
theorem flag_star_retained_nd2 (hPosition : member.position = member.double)
    (hNd2 : IsDangling data member.profile.first.1) {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    nonDanglingIncident member.candidate.datum (member.vertex member.position anchor) =
      (nonDanglingIncident data (data.sourceEndpoint wall anchor)).image
        (flag member anchor) := by
  classical
  rw [branch_vertex_retained member hPosition anchor,
    member.retained_nonDanglingIncident_double_nd2 hPosition hNd2 hAnchor,
    sourceEndpoint_eq hAnchor, incoming_star_nd2 member.profile hNd2]
  simp only [Finset.image_insert, Finset.image_singleton,
    flag_retained member hPosition,
    retainedFlag_double member anchor member.profile.second_target,
    retainedFlag_single member anchor member.profile.third_target]

/-- **Gluing II, `nd3`.** -/
theorem flag_star_resolved_nd3 (hPosition : member.position ≠ member.double)
    (hNd3 : ¬ IsDangling data member.profile.first.1) {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    nonDanglingIncident member.candidate.datum (member.vertex member.position anchor) =
      (nonDanglingIncident data (data.sourceEndpoint wall anchor)).image
        (flag member anchor) := by
  classical
  rw [branch_vertex_resolved member hPosition anchor,
    member.resolved_nonDanglingIncident_single_nd3 hPosition hNd3 hAnchor,
    sourceEndpoint_eq hAnchor, incoming_star_nd3 member.profile hNd3]
  simp only [Finset.image_insert, Finset.image_singleton,
    flag_resolved member hPosition,
    resolvedFlag_double member member.profile.first_target,
    resolvedFlag_double member member.profile.second_target,
    resolvedFlag_single member member.profile.third_target]
  rw [Finset.insert_comm, Finset.pair_comm]
  rfl

/-- **Gluing II, `nd2`.**  `e'` is pruned with `e₁`, and both stars are
pairs. -/
theorem flag_star_resolved_nd2 (hPosition : member.position ≠ member.double)
    (hNd2 : IsDangling data member.profile.first.1) {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    nonDanglingIncident member.candidate.datum (member.vertex member.position anchor) =
      (nonDanglingIncident data (data.sourceEndpoint wall anchor)).image
        (flag member anchor) := by
  classical
  rw [branch_vertex_resolved member hPosition anchor,
    member.resolved_nonDanglingIncident_single_nd2 hPosition hNd2 hAnchor,
    sourceEndpoint_eq hAnchor, incoming_star_nd2 member.profile hNd2]
  simp only [Finset.image_insert, Finset.image_singleton,
    flag_resolved member hPosition,
    resolvedFlag_double member member.profile.second_target,
    resolvedFlag_single member member.profile.third_target]
  rw [Finset.pair_comm]
  rfl

/-- **The star correspondence, in all four sub-cases.** -/
theorem flag_star {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    nonDanglingIncident member.candidate.datum (member.vertex member.position anchor) =
      (nonDanglingIncident data (data.sourceEndpoint wall anchor)).image
        (flag member anchor) := by
  by_cases hPosition : member.position = member.double
  · by_cases hNd2 : IsDangling data member.profile.first.1
    · exact flag_star_retained_nd2 member hPosition hNd2 hAnchor
    · exact flag_star_retained_nd3 member hPosition hNd2 hAnchor
  · by_cases hNd2 : IsDangling data member.profile.first.1
    · exact flag_star_resolved_nd2 member hPosition hNd2 hAnchor
    · exact flag_star_resolved_nd3 member hPosition hNd2 hAnchor

end Flag


/-! ## §3  The flag is injective on the incoming star -/

section FlagInjective

variable {block : WallBlock data wall} (member : BlockMember data star block)

/-- Every surviving occurrence at the block's wall vertex is one of `e₁`,
`e₂`, `e₃`. -/
theorem mem_star_cases {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) {edge : data.SourceEdge}
    (hMem : edge ∈ nonDanglingIncident data (data.sourceEndpoint wall anchor)) :
    edge = member.profile.first.1 ∨ edge = member.profile.second.1 ∨
      edge = member.profile.third.1 := by
  obtain ⟨_, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
  rw [sourceEndpoint_eq hAnchor] at hIncident
  rcases member.profile.exhaustive ⟨edge, hIncident⟩ with h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (congrArg Subtype.val h))

/-- **The flag is injective on the incoming star**, in all four sub-cases. -/
theorem flag_injOn {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    Set.InjOn (flag member anchor)
      ↑(nonDanglingIncident data (data.sourceEndpoint wall anchor)) := by
  classical
  intro x hx y hy hEq
  have hxCases := mem_star_cases member hAnchor (Finset.mem_coe.mp hx)
  have hyCases := mem_star_cases member hAnchor (Finset.mem_coe.mp hy)
  by_cases hPosition : member.position = member.double
  · rw [flag_retained member hPosition, flag_retained member hPosition] at hEq
    rcases hxCases with rfl | rfl | rfl <;> rcases hyCases with rfl | rfl | rfl
    · rfl
    · rw [retainedFlag_double member anchor member.profile.first_target,
        retainedFlag_double member anchor member.profile.second_target] at hEq
      exact absurd hEq member.old_first_ne_second
    · rw [retainedFlag_double member anchor member.profile.first_target,
        retainedFlag_single member anchor member.profile.third_target] at hEq
      exact absurd hEq (member.old_ne_new _ _)
    · rw [retainedFlag_double member anchor member.profile.second_target,
        retainedFlag_double member anchor member.profile.first_target] at hEq
      exact absurd hEq.symm member.old_first_ne_second
    · rfl
    · rw [retainedFlag_double member anchor member.profile.second_target,
        retainedFlag_single member anchor member.profile.third_target] at hEq
      exact absurd hEq (member.old_ne_new _ _)
    · rw [retainedFlag_single member anchor member.profile.third_target,
        retainedFlag_double member anchor member.profile.first_target] at hEq
      exact absurd hEq.symm (member.old_ne_new _ _)
    · rw [retainedFlag_single member anchor member.profile.third_target,
        retainedFlag_double member anchor member.profile.second_target] at hEq
      exact absurd hEq.symm (member.old_ne_new _ _)
    · rfl
  · rw [flag_resolved member hPosition, flag_resolved member hPosition] at hEq
    rcases hxCases with rfl | rfl | rfl <;> rcases hyCases with rfl | rfl | rfl
    · rfl
    · rw [resolvedFlag_double member member.profile.first_target,
        resolvedFlag_double member member.profile.second_target] at hEq
      exact absurd hEq (member.resolved_new_first_ne_second hPosition)
    · rw [resolvedFlag_double member member.profile.first_target,
        resolvedFlag_single member member.profile.third_target] at hEq
      exact absurd hEq.symm (member.old_ne_new _ _)
    · rw [resolvedFlag_double member member.profile.second_target,
        resolvedFlag_double member member.profile.first_target] at hEq
      exact absurd hEq.symm (member.resolved_new_first_ne_second hPosition)
    · rfl
    · rw [resolvedFlag_double member member.profile.second_target,
        resolvedFlag_single member member.profile.third_target] at hEq
      exact absurd hEq.symm (member.old_ne_new _ _)
    · rw [resolvedFlag_single member member.profile.third_target,
        resolvedFlag_double member member.profile.first_target] at hEq
      exact absurd hEq (member.old_ne_new _ _)
    · rw [resolvedFlag_single member member.profile.third_target,
        resolvedFlag_double member member.profile.second_target] at hEq
      exact absurd hEq (member.old_ne_new _ _)
    · rfl

/-! ## §4  The flag preserves the stable row -/

/-- **The branch flag lands in the incoming occurrence's own outgoing row.**
The retained occurrences keep their row by construction; the regrown ones join
the row of the occurrence they replace, which is §6, §7 and §12 of the
census. -/
theorem flag_row {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor)
    (edge : data.SourceEdge) (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge (data.sourceEndpoint wall anchor))
    (hFlag : ¬ IsDangling member.candidate.datum (flag member anchor edge)) :
    NonDanglingEdge.stablePath
        (⟨flag member anchor edge, hFlag⟩ : NonDanglingEdge member.candidate.datum) =
      (retainedEdge member.candidate member.valid.1
        (⟨edge, hSurvives⟩ : NonDanglingEdge data)).stablePath := by
  have hCases := mem_star_cases member hAnchor
    ((mem_nonDanglingIncident _ _ _).mpr ⟨hSurvives, hIncident⟩)
  by_cases hPosition : member.position = member.double
  · rcases hCases with rfl | rfl | rfl
    · exact congrArg NonDanglingEdge.stablePath (Subtype.ext
        ((flag_retained member hPosition anchor _).trans
          (retainedFlag_double member anchor member.profile.first_target)))
    · exact congrArg NonDanglingEdge.stablePath (Subtype.ext
        ((flag_retained member hPosition anchor _).trans
          (retainedFlag_double member anchor member.profile.second_target)))
    · refine Eq.trans (congrArg NonDanglingEdge.stablePath (Subtype.ext
        ((flag_retained member hPosition anchor _).trans
          (retainedFlag_single member anchor member.profile.third_target)) :
          (⟨flag member anchor member.profile.third.1, hFlag⟩ :
            NonDanglingEdge member.candidate.datum) =
            ⟨member.candidate.newSourceEdge anchor,
              member.retained_new_survives hPosition hAnchor⟩)) ?_
      exact member.retained_new_stablePath_eq hPosition hAnchor
  · rcases hCases with rfl | rfl | rfl
    · refine Eq.trans (congrArg NonDanglingEdge.stablePath (Subtype.ext
        ((flag_resolved member hPosition anchor _).trans
          (resolvedFlag_double member member.profile.first_target)) :
          (⟨flag member anchor member.profile.first.1, hFlag⟩ :
            NonDanglingEdge member.candidate.datum) =
            ⟨member.candidate.newSourceEdge
                (firstSheet member.profile.toOccurrenceProfile),
              (member.resolved_new_first_survives_iff hPosition).mpr hSurvives⟩)) ?_
      exact member.resolved_new_first_stablePath_eq hPosition hSurvives
    · refine Eq.trans (congrArg NonDanglingEdge.stablePath (Subtype.ext
        ((flag_resolved member hPosition anchor _).trans
          (resolvedFlag_double member member.profile.second_target)) :
          (⟨flag member anchor member.profile.second.1, hFlag⟩ :
            NonDanglingEdge member.candidate.datum) =
            ⟨member.candidate.newSourceEdge
                (secondSheet member.profile.toOccurrenceProfile),
              member.resolved_new_second_survives hPosition⟩)) ?_
      exact member.resolved_new_second_stablePath_eq hPosition
    · exact congrArg NonDanglingEdge.stablePath (Subtype.ext
        ((flag_resolved member hPosition anchor _).trans
          (resolvedFlag_single member member.profile.third_target)))

end FlagInjective


/-! ## §5  Every other endpoint above the block has surviving valency ≤ 2

This is the field `LimitChainTwoBlock.GraphData.selected_not_branch`, and it
is where `nd2` would have to fail if `GraphData` required a trivalent branch
vertex.  It does not: it only bounds the *other* endpoints, and above a
ramification-one block those are divalent in `nd3` and divalent or entirely
pruned in `nd2`. -/

section NotBranch

variable {block : WallBlock data wall} (member : BlockMember data star block)

/-- The `e₁`-class endpoint of a resolved member: divalent in `nd3`, empty in
`nd2`. -/
theorem resolved_first_valency_le (hPosition : member.position ≠ member.double) :
    nonDanglingValency member.candidate.datum
      (member.vertex member.double (firstSheet member.profile.toOccurrenceProfile)) ≤ 2 := by
  classical
  rw [← card_nonDanglingIncident]
  by_cases hNd2 : IsDangling data member.profile.first.1
  · rw [member.resolved_nonDanglingIncident_first_nd2 hPosition hNd2]
    simp
  · rw [member.resolved_nonDanglingIncident_first_nd3 hPosition hNd2,
      Finset.card_pair (Ne.symm (member.old_ne_new _ _))]

/-- **`selected_not_branch` at one block, read on a wall direction.** -/
theorem not_branch_at_label {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor)
    (label : Fin 2) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet)
    (hNe : member.vertex label sheet ≠ member.vertex member.position anchor) :
    nonDanglingValency member.candidate.datum (member.vertex label sheet) ≤ 2 := by
  by_cases hPosition : member.position = member.double
  · by_cases hLabel : label = member.position
    · subst hLabel
      exact absurd (member.retained_vertex_eq' hPosition member.position hSheet hAnchor) hNe
    · have hSingle : label = member.single :=
        eq_singleLabel_of_ne_doubleLabel member.profile.toOccurrenceProfile
          (fun h ↦ hLabel (h.trans hPosition.symm))
      subst hSingle
      exact le_of_eq (member.retained_nonDanglingValency_single hPosition hSheet)
  · have hPos := member.position_eq_single hPosition
    by_cases hLabel : label = member.position
    · refine absurd ?_ hNe
      subst hLabel
      rw [hPos]
      exact member.resolved_vertex_eq' hPosition hSheet hAnchor
    · have hDouble : label = member.double := by
        have hSingleNe : label ≠ member.single := fun h ↦ hLabel (h.trans hPos.symm)
        have hBoth := member.double_ne_single
        omega
      subst hDouble
      rcases doublePartition_covers member.profile.toOccurrenceProfile sheet hSheet with
        hRel | hRel
      · rw [member.resolved_double_vertex_eq' hPosition hSheet hRel.symm]
        exact resolved_first_valency_le member hPosition
      · rw [member.resolved_double_vertex_eq' hPosition hSheet hRel.symm]
        exact le_of_eq (member.resolved_nonDanglingValency_second hPosition)

end NotBranch


/-! ## §6  The two-block graph data of Equation (10)'s member

One `selectedSide` and one `selectedFlag` per anchor, and `branch_ne` free
from `W2R1StableGraph.branch_side_ne`: the member's two branch vertices lie on
opposite sides of the new edge. -/

section Pair

variable (pair : Pair data star) (hValid : data.Valid)

theorem anchor_cases {anchor : Fin degree} (hAnchor : anchor ∈ anchors pair) :
    anchor = pair.first.1 ∨ anchor = pair.second.1 := by
  rcases Finset.mem_insert.mp hAnchor with h | h
  · exact Or.inl h
  · exact Or.inr (Finset.mem_singleton.mp h)

/-- **The side of the member's branch vertex above each block**: `A₀`'s is the
member's own position, `B₀`'s the opposite one. -/
noncomputable def selectedSide (position : Fin 2) (anchor : Fin degree) : Bool :=
  if (data.vertexPartition wall).Rel pair.first.1 anchor then side position
  else side (other position)

@[simp] theorem selectedSide_first (position : Fin 2) :
    selectedSide pair position pair.first.1 = side position := if_pos rfl

@[simp] theorem selectedSide_second (position : Fin 2) :
    selectedSide pair position pair.second.1 = side (other position) := if_neg pair.separate

/-- **The flag dictionary at each of the two branch vertices.** -/
noncomputable def selectedFlag (position : Fin 2) (anchor : Fin degree)
    (edge : data.SourceEdge) : (pair.candidate position).datum.SourceEdge :=
  if (data.vertexPartition wall).Rel pair.first.1 anchor then
    flag (firstMember pair hValid position) anchor edge
  else flag (secondMember pair hValid position) anchor edge

@[simp] theorem selectedFlag_first (position : Fin 2) (edge : data.SourceEdge) :
    selectedFlag pair hValid position pair.first.1 edge =
      flag (firstMember pair hValid position) pair.first.1 edge :=
  if_pos rfl

@[simp] theorem selectedFlag_second (position : Fin 2) (edge : data.SourceEdge) :
    selectedFlag pair hValid position pair.second.1 edge =
      flag (secondMember pair hValid position) pair.second.1 edge :=
  if_neg pair.separate

/-- The anchors name distinct wall blocks. -/
theorem anchors_sep : ∀ first ∈ anchors pair, ∀ second ∈ anchors pair,
    (data.vertexPartition wall).Rel first second → first = second := by
  intro first hFirst second hSecond hRel
  rcases anchor_cases pair hFirst with rfl | rfl <;>
    rcases anchor_cases pair hSecond with rfl | rfl
  · rfl
  · exact absurd hRel pair.separate
  · exact absurd hRel.symm pair.separate
  · rfl

/-- **The two branch vertices lie on opposite sides**, so `branch_ne` is
free. -/
theorem selectedSide_ne (position : Fin 2) : ∀ first ∈ anchors pair,
    ∀ second ∈ anchors pair, first ≠ second →
      selectedSide pair position first ≠ selectedSide pair position second := by
  intro first hFirst second hSecond hNe
  rcases anchor_cases pair hFirst with rfl | rfl <;>
    rcases anchor_cases pair hSecond with rfl | rfl
  · exact absurd rfl hNe
  · simp only [selectedSide_first, selectedSide_second, branch_side_ne position]
    simp
  · simp only [selectedSide_first, selectedSide_second, branch_side_ne position]
    simp
  · exact absurd rfl hNe

/-- **Equation (10)'s member, read as two-block graph data.** -/
noncomputable def graphData (position : Fin 2) : GraphData data wall (anchors pair) where
  toSelectedData := selectedData pair hValid position
  anchors_sep := anchors_sep pair
  selectedSide := selectedSide pair position
  selectedFlag := selectedFlag pair hValid position
  selectedFlag_star := by
    intro anchor hAnchor
    rcases anchor_cases pair hAnchor with rfl | rfl
    · rw [selectedSide_first]
      exact Eq.trans (flag_star (firstMember pair hValid position) rfl)
        (Finset.image_congr (fun edge _ ↦
          (selectedFlag_first pair hValid position edge).symm))
    · rw [selectedSide_second]
      exact Eq.trans (flag_star (secondMember pair hValid position) rfl)
        (Finset.image_congr (fun edge _ ↦
          (selectedFlag_second pair hValid position edge).symm))
  selectedFlag_injOn := by
    intro anchor hAnchor
    rcases anchor_cases pair hAnchor with rfl | rfl
    · intro x hx y hy hEq
      refine flag_injOn (firstMember pair hValid position) rfl hx hy ?_
      rwa [selectedFlag_first, selectedFlag_first] at hEq
    · intro x hx y hy hEq
      refine flag_injOn (secondMember pair hValid position) rfl hx hy ?_
      rwa [selectedFlag_second, selectedFlag_second] at hEq
  selected_not_branch := by
    intro anchor hAnchor b sheet hSheet hNe
    rcases anchor_cases pair hAnchor with rfl | rfl
    · rw [selectedSide_first] at hNe
      cases b
      · exact not_branch_at_label (firstMember pair hValid position) rfl 0 hSheet hNe
      · exact not_branch_at_label (firstMember pair hValid position) rfl 1 hSheet hNe
    · rw [selectedSide_second] at hNe
      cases b
      · exact not_branch_at_label (secondMember pair hValid position) rfl 0 hSheet hNe
      · exact not_branch_at_label (secondMember pair hValid position) rfl 1 hSheet hNe
  selectedFlag_row := by
    intro anchor hAnchor edge hSurvives hIncident hFlag
    rcases anchor_cases pair hAnchor with rfl | rfl
    · have hFlag' : ¬ IsDangling (pair.candidate position).datum
          (flag (firstMember pair hValid position) pair.first.1 edge) := by
        rwa [selectedFlag_first] at hFlag
      refine Eq.trans (congrArg NonDanglingEdge.stablePath (Subtype.ext
        (selectedFlag_first pair hValid position edge) :
          (⟨selectedFlag pair hValid position pair.first.1 edge, hFlag⟩ :
            NonDanglingEdge (pair.candidate position).datum) =
            ⟨flag (firstMember pair hValid position) pair.first.1 edge, hFlag'⟩)) ?_
      exact flag_row (firstMember pair hValid position) rfl edge hSurvives hIncident hFlag'
    · have hFlag' : ¬ IsDangling (pair.candidate position).datum
          (flag (secondMember pair hValid position) pair.second.1 edge) := by
        rwa [selectedFlag_second] at hFlag
      refine Eq.trans (congrArg NonDanglingEdge.stablePath (Subtype.ext
        (selectedFlag_second pair hValid position edge) :
          (⟨selectedFlag pair hValid position pair.second.1 edge, hFlag⟩ :
            NonDanglingEdge (pair.candidate position).datum) =
            ⟨flag (secondMember pair hValid position) pair.second.1 edge, hFlag'⟩)) ?_
      exact flag_row (secondMember pair hValid position) rfl edge hSurvives hIncident hFlag'
  branch_ne := LimitChainTwoBlock.branch_ne_of_side_ne (pair.candidate position)
    (anchors pair) (selectedSide pair position) (selectedSide_ne pair position)

@[simp] theorem graphData_candidate (position : Fin 2) :
    (graphData pair hValid position).candidate = pair.candidate position := rfl

@[simp] theorem graphData_toSelectedData (position : Fin 2) :
    (graphData pair hValid position).toSelectedData = selectedData pair hValid position := rfl

/-- **Each member's stable incidence graph is the incoming one**, with exactly
the row map the limit matrices use. -/
noncomputable def equivalence (position : Fin 2) :
    StableGraphIncidence.Equivalence data (pair.candidate position).datum :=
  (graphData pair hValid position).equivalence

@[simp] theorem equivalence_row (position : Fin 2) :
    (equivalence pair hValid position).row = stablePathEquiv pair hValid position := rfl

include hValid in
/-- **Non-vacuity.** -/
theorem nonempty_equivalence (position : Fin 2) :
    Nonempty (StableGraphIncidence.Equivalence data (pair.candidate position).datum) :=
  ⟨equivalence pair hValid position⟩

end Pair


/-! ## §7  The certified exit: the outgoing full-dimensional presentation

The chain closes the way `W2PArbitraryExit` closes case P: one identified
member's full-dimensional presentation fixes the common square coordinate
order, and `StableGraphFullDimensional.presentationOfEquivalence` transports
it to any member whose own honest matrix is nonsingular.  The `certificate`
input is `between`, built from §6's two `GraphData.equivalence`s; every other
input is a receipt `W2R1SourceCandidates` already carries.

**Both members and both sub-cases have the exit**, because §6's `graphData` is
uniform in `position` and in `nd2`/`nd3`. -/

section Exit

variable (pair : Pair data star) (hValid : data.Valid)

/-- Compare the two members through the incoming stable graph. -/
noncomputable def between (first second : Fin 2) :
    StableGraphIncidence.Equivalence (pair.candidate first).datum
      (pair.candidate second).datum :=
  (equivalence pair hValid first).symm.trans (equivalence pair hValid second)

include hValid in
theorem member_valid (position : Fin 2) : (pair.candidate position).datum.Valid :=
  (pair.candidate position).datum_valid hValid

theorem member_targetConnected (hConnected : graph_connected target) (position : Fin 2) :
    graph_connected (TargetExpansion.graph target wall (pair.candidate position).right) :=
  TargetExpansion.graph_connected target wall _ hConnected

theorem member_targetGenus (hGenus : genus target = 0) (position : Fin 2) :
    genus (TargetExpansion.graph target wall (pair.candidate position).right) = 0 := by
  simpa using hGenus

theorem member_targetEdgeCard (position : Fin 2) :
    (TargetExpansion.graph target wall (pair.candidate position).right).edges.card =
      target.edges.card + 1 := by
  simp

theorem member_sourceGenus (position : Fin 2) :
    genus (pair.candidate position).datum.sourceGraph = genus data.sourceGraph :=
  pair.candidate_sourceGenus position

section Transport

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- One identified member's honest labelling, read back on member `0`: the
only source of the common square coordinate order. -/
noncomputable def initialLabelling (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (pair.candidate incoming).datum coordinate) :
    StableLengthMatrixLabelling (pair.candidate 0).datum coordinate where
  row := (between pair hValid 0 incoming).row.trans incomingFD.labelling.row
  targetEdge := incomingFD.labelling.targetEdge.trans
    ((W2R1CommonBalance.columnEquiv pair incoming).symm.trans
      (W2R1CommonBalance.columnEquiv pair 0))

/-- The induced honest square labelling of each of the two members. -/
noncomputable def outgoingLabelling (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (pair.candidate incoming).datum coordinate) (outgoing : Fin 2) :
    StableLengthMatrixLabelling (pair.candidate outgoing).datum coordinate :=
  (W2R1LimitMatrix.limitColumns pair hValid).labelling
    (initialLabelling pair hValid incoming incomingFD) outgoing

/-- **Transport a full-dimensional presentation to a chosen `{w2-r1}`
member.**  Only that member's own compatible matrix must be nonsingular; the
rest is what the two-block stable-incidence dictionary carries. -/
noncomputable def outgoingPresentation (hConnected : graph_connected target)
    (hGenus : genus target = 0) (incoming outgoing : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (pair.candidate incoming).datum coordinate)
    (outgoingDet : (GluingDatum.LengthMatrixPresentation.matrix
      (outgoingLabelling pair hValid incoming incomingFD outgoing).presentation).det ≠ 0) :
    FullDimensionalSourcePresentation (pair.candidate outgoing).datum coordinate :=
  StableGraphFullDimensional.presentationOfEquivalence incomingFD
    (between pair hValid incoming outgoing)
    (member_valid pair hValid outgoing)
    (member_targetConnected pair hConnected outgoing)
    (member_targetGenus pair hGenus outgoing)
    ((member_targetEdgeCard pair outgoing).trans (member_targetEdgeCard pair incoming).symm)
    ((member_sourceGenus pair outgoing).trans (member_sourceGenus pair incoming).symm)
    (outgoingLabelling pair hValid incoming incomingFD outgoing)
    outgoingDet

@[simp] theorem outgoingPresentation_labelling (hConnected : graph_connected target)
    (hGenus : genus target = 0) (incoming outgoing : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (pair.candidate incoming).datum coordinate)
    (outgoingDet : (GluingDatum.LengthMatrixPresentation.matrix
      (outgoingLabelling pair hValid incoming incomingFD outgoing).presentation).det ≠ 0) :
    (outgoingPresentation pair hValid hConnected hGenus incoming outgoing incomingFD
        outgoingDet).labelling =
      outgoingLabelling pair hValid incoming incomingFD outgoing := rfl

/-- The honest presented family of Equation (10)'s two members, in the square
coordinates one identified member induces. -/
noncomputable def family (input : W2SourceInput data star) (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (pair.candidate incoming).datum coordinate) :
    BalancedGlobal.PresentedFamily (coordinate := coordinate) 2 data wall :=
  (W2R1LimitMatrix.limitColumns pair input.valid).honestPresentedFamily input.valid
    (initialLabelling pair input.valid incoming incomingFD)

@[simp] theorem family_candidate (input : W2SourceInput data star) (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (pair.candidate incoming).datum coordinate) (outgoing : Fin 2) :
    (family pair input incoming incomingFD).candidate outgoing =
      pair.candidate outgoing := rfl

@[simp] theorem family_presentation (input : W2SourceInput data star) (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (pair.candidate incoming).datum coordinate) (outgoing : Fin 2) :
    (family pair input incoming incomingFD).presentation outgoing =
      (outgoingLabelling pair input.valid incoming incomingFD outgoing).presentation := rfl

/-- **The full-dimensional supply for `{w2-r1}`, first field**: an outgoing full-dimensional
presentation at every nonsingular member of Equation (10)'s honest family. -/
noncomputable def familyFullDim (input : W2SourceInput data star)
    (hConnected : graph_connected target) (hGenus : genus target = 0) (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (pair.candidate incoming).datum coordinate) :
    ∀ outgoing : Fin 2,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((family pair input incoming incomingFD).presentation outgoing)).det ≠ 0 →
      FullDimensionalSourcePresentation
        ((family pair input incoming incomingFD).candidate outgoing).datum coordinate :=
  fun outgoing hdet ↦ outgoingPresentation pair input.valid hConnected hGenus incoming
    outgoing incomingFD hdet

/-- **The full-dimensional supply for `{w2-r1}`, second field**: it is a presentation *of that
member*, because the family carries the honest presentations the transport
installs. -/
theorem familyFullDim_presentation (input : W2SourceInput data star)
    (hConnected : graph_connected target) (hGenus : genus target = 0) (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (pair.candidate incoming).datum coordinate) :
    ∀ (outgoing : Fin 2)
      (hdet : (GluingDatum.LengthMatrixPresentation.matrix
        ((family pair input incoming incomingFD).presentation outgoing)).det ≠ 0),
      (familyFullDim pair input hConnected hGenus incoming incomingFD outgoing
          hdet).labelling.presentation =
        (family pair input incoming incomingFD).presentation outgoing :=
  fun _ _ ↦ rfl

/-! ### Transport to the chosen member and back is the identity -/

/-- **Transport to the common member `0` and back cancels both the actual row
equivalence and the target-occurrence equivalence**, so the identified
incoming member's honest square matrix is its own. -/
theorem outgoingLabelling_self (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (pair.candidate incoming).datum coordinate) :
    outgoingLabelling pair hValid incoming incomingFD incoming = incomingFD.labelling := by
  cases incomingFD with
  | mk valid targetConnected targetGenus saturated labelling det_ne_zero trivalent pathEnds =>
    cases labelling with
    | mk targetEdge row =>
      simp only [outgoingLabelling, initialLabelling,
        W2R1CommonBalance.LimitColumns.labelling,
        W2R1CommonBalance.LimitColumns.sourceCoordinates,
        W2R1CommonBalance.LimitColumns.targetCoordinates]
      congr 1
      · ext column
        simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
      · ext path
        have hBetween : (between pair hValid 0 incoming).row =
            ((W2R1LimitMatrix.limitColumns pair hValid).row 0).symm.trans
              ((W2R1LimitMatrix.limitColumns pair hValid).row incoming) := by
          change (equivalence pair hValid 0).row.symm.trans
            (equivalence pair hValid incoming).row = _
          rw [equivalence_row pair hValid 0, equivalence_row pair hValid incoming]
          rfl
        rw [hBetween]
        simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- The identified incoming member's own honest square matrix is
nonsingular. -/
theorem incomingDet_ne_zero (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (pair.candidate incoming).datum coordinate) :
    ((W2R1LimitMatrix.limitColumns pair hValid).squareMatrix
      (initialLabelling pair hValid incoming incomingFD) incoming).det ≠ 0 := by
  change (GluingDatum.LengthMatrixPresentation.matrix
    (outgoingLabelling pair hValid incoming incomingFD incoming).presentation).det ≠ 0
  rw [outgoingLabelling_self pair hValid incoming incomingFD]
  exact incomingFD.det_ne_zero

end Transport

end Exit

end DraismaVargas.LocalCases.W2R1GraphData
