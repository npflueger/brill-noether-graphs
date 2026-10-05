module

public import DraismaVargas.LocalCases.W2PSurvival

@[expose] public section

/-!
# Figure 35's induced stable-row map

Source: Draisma--Vargas Part I (arXiv:1909.12924), Section 6, Case
`{w2-r2-nd3-P}` and its Figure 35; and, in Section 5, the induced-labelling
paragraph following the non-dangling-union lemma (`lemma-class-union`).

The stable lift is the generic one, `LimitChainCore.LiftData.stablePathLift`:
retain any surviving occurrence of an old stable path.  What this module
supplies is the reading of a Figure 35 member as the core's data:

* `wallCandidate` — a member retains `t₂` and sends `t₃` to the fresh
  endpoint;
* `backgroundShape` — off `A₀` a member installs
  `ResolutionM11.joinedResolutionAt`, which agrees with `t₂`'s own star block
  by block because every background wall block has local ramification zero
  (`M11JoinedBackground.background_blockCount`);
* `liftData` — `A₀` has surviving valency three
  (`M11JoinedStableLift.background_of_wall_valency_two`), so no consecutive
  pair of the incoming stable quotient meets it;
* `selectedData` — the `A₀` half of the census (`W2PSurvival.Census`) is the
  core's `SelectedData`, which gives surjectivity here and the reverse map,
  hence injectivity, in `W2PRowDescent`.
-/

namespace DraismaVargas.LocalCases.W2PStableLift

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open ResolutionM11 GlobalM11Arbitrary
open ResolutionAwayFromWall
open W2PSourceCandidates
open W2PSurvival
open LimitChainCore (WallCandidate BackgroundShape LiftData SelectedData)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- A Figure 35 member retains `t₂` and nothing else at the retained
endpoint. -/
noncomputable def wallCandidate (member : MemberShape profile) : WallCandidate data wall where
  candidate := member.candidate
  retainedTarget := star.edge profile.doubleLabel
  target_mem := star.edge_mem_incidentEdges _
  left := member.right_double
  unique := by
    intro edge hMem hFalse
    obtain ⟨label, hLabel⟩ := star.label.surjective ⟨edge, hMem⟩
    have hEdge : edge = star.edge label := (congrArg Subtype.val hLabel).symm
    rcases (show label = profile.doubleLabel ∨ label = profile.singleLabel by
        have := profile.labels_ne; omega) with rfl | rfl
    · exact hEdge
    · rw [hEdge, member.right_single] at hFalse
      exact Bool.noConfusion hFalse

/-- Off `A₀` a member installs `t₂`'s own star, block by block: the joined
background retains the whole wall block, and `t₂` induces exactly one class
there. -/
noncomputable def backgroundShape (input : W2SourceInput data star)
    (member : MemberShape profile) : BackgroundShape data wall where
  toWallCandidate := wallCandidate member
  selected := block.1
  left_block := by
    intro sheet hSheet
    change (LimitChainCore.pasted member.candidate).left.block sheet =
      (data.edgePartition (star.edge profile.doubleLabel)).block sheet
    have hWall : (LimitChainCore.pasted member.candidate).left.block sheet =
        (data.vertexPartition wall).block sheet := by
      ext other
      rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
      exact member.pasted_left_rel_iff_of_not_rel sheet other hSheet
    rw [hWall]
    exact (SheetPartition.block_eq_of_refines_of_blockCountWithin_eq_one _ _
      (star.edgePartition_refines_wall data _) sheet
      (M11JoinedBackground.background_blockCount input profile profile.doubleLabel sheet
        hSheet)).symm
  right_block := by
    intro sheet _
    change (LimitChainCore.pasted member.candidate).right.block sheet = _
    rw [member.pasted_right_eq]
  newEdge_block := by
    intro sheet hSheet
    change (LimitChainCore.pasted member.candidate).newEdge.block sheet =
      (data.edgePartition (star.edge profile.doubleLabel)).block sheet
    have hWall : (LimitChainCore.pasted member.candidate).newEdge.block sheet =
        (data.vertexPartition wall).block sheet := by
      ext other
      rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
      exact member.pasted_newEdge_rel_iff_of_not_rel sheet other hSheet
    rw [hWall]
    exact (SheetPartition.block_eq_of_refines_of_blockCountWithin_eq_one _ _
      (star.edgePartition_refines_wall data _) sheet
      (M11JoinedBackground.background_blockCount input profile profile.doubleLabel sheet
        hSheet)).symm
  genus_eq := member.sourceGenus

/-- `A₀` has surviving valency three, so retention respects the incoming
stable quotient. -/
noncomputable def liftData (input : W2SourceInput data star) (member : MemberShape profile) :
    LiftData data wall where
  toBackgroundShape := backgroundShape input member
  valid := input.valid
  selected_valency_ne_two := fun hValency ↦
    M11JoinedStableLift.background_of_wall_valency_two profile _ rfl hValency
      ((data.vertexPartition wall).rel_repr_right block.1)

/-- Retaining a different occurrence of one old stable row gives the same
row upstairs. -/
theorem stablePath_retained_eq_of_consecutive (input : W2SourceInput data star)
    (member : MemberShape profile) (first second : NonDanglingEdge data)
    (hConsecutive : Consecutive data first second) :
    (retainedEdge member.candidate input.valid.1 first).stablePath =
      (retainedEdge member.candidate input.valid.1 second).stablePath :=
  (liftData input member).retained_stablePath_eq_of_consecutive first second hConsecutive

/-- **Figure 35's induced stable-row map**, evaluated by retaining any actual
surviving occurrence of the old row. -/
noncomputable def stablePathLift (input : W2SourceInput data star)
    (member : MemberShape profile) :
    StablePath data → StablePath member.candidate.datum :=
  (liftData input member).stablePathLift

@[simp] theorem stablePathLift_mk (input : W2SourceInput data star)
    (member : MemberShape profile) (edge : NonDanglingEdge data) :
    stablePathLift input member edge.stablePath =
      (retainedEdge member.candidate input.valid.1 edge).stablePath := rfl

/-- The `A₀` half of the census, read as the core's selected data. -/
noncomputable def selectedData (input : W2SourceInput data star) {member : MemberShape profile}
    (census : Census input member) : SelectedData data wall where
  toLiftData := liftData input member
  selectedRep := fun sheet ↦ (census.rep sheet).1
  selectedRep_survives := fun sheet _ ↦ (census.rep sheet).2
  selectedRep_congr := fun first second hFirst _ hEq ↦
    congrArg Subtype.val (census.rep_congr first second hFirst
      ((member.newSourceEdge_eq_iff_fine first second hFirst).mp hEq))
  selected_new_stablePath := fun sheet hRel hSurvives _ ↦
    census.rep_row sheet (census.rep sheet) hRel rfl hSurvives
  selected_left_pair := by
    intro sheet hRel hValency
    obtain ⟨other, old, hOther, rfl, hStar⟩ := census.old_pair sheet hRel hValency
    exact ⟨other, hOther, hStar⟩
  selected_right_pair := by
    intro sheet hRel hValency
    obtain ⟨other, old, hOther, rfl, hStar⟩ := census.fresh_pair sheet hRel hValency
    exact ⟨other, hOther, hStar⟩

@[simp] theorem selectedData_candidate (input : W2SourceInput data star)
    {member : MemberShape profile} (census : Census input member) :
    (selectedData input census).candidate = member.candidate := rfl

/-- No stable row of a member lies entirely in the new fibre. -/
theorem exists_retained_row (input : W2SourceInput data star) {member : MemberShape profile}
    (census : Census input member) (edge : NonDanglingEdge member.candidate.datum) :
    ∃ old : NonDanglingEdge data,
      (retainedEdge member.candidate input.valid.1 old).stablePath = edge.stablePath :=
  (selectedData input census).exists_retained_row edge

theorem stablePathLift_surjective (input : W2SourceInput data star)
    {member : MemberShape profile} (census : Census input member) :
    Function.Surjective (stablePathLift input member) :=
  (selectedData input census).stablePathLift_surjective

end DraismaVargas.LocalCases.W2PStableLift
