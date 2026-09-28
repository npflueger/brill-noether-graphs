import DraismaVargas.LocalCases.W2M1kLeafLimitMatrix
import DraismaVargas.LocalCases.W2M1kStableIncidence
import DraismaVargas.LocalCases.ResolutionStableIncidence
import DraismaVargas.LocalCases.M11JoinedIncidence

/-!
# Figure 33's leaf member: its branch dictionary and its certified exit

Source: Draisma--Vargas Part I (arXiv:1909.12924), Section 6, Case
`{w2-r2-nd3-M-1k}`, its Figure 33 and Equation (7); the Base I/II vocabulary is
that of Case `{w2-r2}` there.

`W2M1kGraphData` gives Figure 33's two **divalent** members their branch half as
instances of `LimitChainCore.GraphData`, and `W2M1kStableIncidence` §6 records
exactly what the third member needs.  This module supplies it.  `M⁽¹⁾` has no
`LimitChainCore.WallCandidate` -- `W2M1kStableLift.leaf_not_wallCandidate` is a
theorem, Base I.a's retained endpoint being a target leaf with no wall
direction -- so there is no `SelectedData` and no `GraphData` to take
`GraphData.equivalence` of.  What is built below is the object that
construction *produces*, by hand, on the pattern of the only other member in
this library with a target leaf: the M11 chain's split member
(`M11SplitVertices`, `M11SplitBranchFlags`, `M11SplitStableGraph`).

## The dictionary, as `W2M1kStableIncidence` §6 specifies it

`leafEquivalence` is a `StableGraphIncidence.Equivalence data
(W2M1kSourceCandidates.LeafPair.candidate input shape pair).datum` whose

* `row` field **is** `W2M1kLeafRowDescent.leafStablePathEquiv`
  (`leafEquivalence_row`, by `rfl`), the same bijection
  `W2M1kLeafLimitMatrix.leaf_matrix_retained` and `leafMember_regrown` are
  stated against, so the retained columns and this dictionary read the same
  rows; and whose
* `vertex` field is `leafBranchVertexEquiv`, sending the case's own
  `w2-r2-nd3` branch vertex above `A₀` to `leafBranchVertex` -- the **fresh
  trivalent** endpoint over `A₀ ∖ {x}`, anchored at `pair.second`, of surviving
  valency three (`W2M1kStableGraph.leaf_nonDanglingValency_fresh_branch`) --
  every background wall vertex to the fresh endpoint over its own sheet, and
  every off-wall vertex to its literal retained copy.

The flag at the branch vertex is read off
`W2M1kStableGraph.leaf_nonDanglingIncident_fresh_branch`, never off a
cardinality: the surviving star there is `{e₂, e₃, new(pair.second)}`, so the
flag **retains `e₂` and `e₃` and sends `e₁` to `new(pair.second)`**, and the one
row identity it needs is `W2M1kStableGraph.leaf_new_second_stablePath_eq` (that
regrown occurrence lies in `e₁`'s row, which is also where
`leaf_new_pin_stablePath_eq` puts the other survivor -- Figure 33's
`c⁽¹⁾ = 2c(e₁)`).  Nothing here asserts two stable rows distinct, so a stable
loop through the branch is still counted twice on both sides.

## Why the vertex map is a bijection

Every other expanded endpoint of `M⁽¹⁾` above `A₀` is divalent or entirely
pruned, and that is the whole content of the leaf census:

| endpoint | surviving valency | reader |
|---|---|---|
| leaf over `{x, pair.second}` | `2` | `leaf_nonDanglingValency_left_pair` |
| leaf over `{s}`, `s ∈ A₀ ∖ {x, pair.second}` | `0` | `leaf_nonDanglingIncident_left_singleton` |
| leaf over a background sheet | `0` | `leaf_nonDanglingIncident_left_background` |
| fresh over `{x}` | `2` | `leaf_nonDanglingValency_fresh_pin` |
| fresh over `A₀ ∖ {x}` | `3` | `leaf_nonDanglingValency_fresh_branch` |
| fresh over a background sheet | incoming | `W2M1kLeafStableLift.leaf_nonDanglingValency_background` |

so `leaf_left_valency_le_two` rules the whole target leaf out of the branch
subtype, and surjectivity needs no count.  The census of `W2M1kStableGraph`
supplies every fact this module needs.

## What the background half costs here, and what it does not

Off `A₀` the leaf member's surviving star is the **literal**
`oldSourceEdge`-image of the incoming one -- every background regrown
occurrence is pruned (`W2M1kLeaves.leaf_new_background_dangling`) -- so
`leaf_incidenceCount_background` is proved directly, on the model of
`ResolutionStableIncidence.incidenceCount_retainedVertex`, with no
`LimitChainCore.Background.replace` matching in it.  That is the same place
where the leaf member departs from the core in `W2M1kLeafStableLift`.

## The two member-to-member certificates

`leafToJoined` / `joinedToLeaf` are composites through the incoming stable
graph, exactly as `W2M1kStableIncidence.dividedToJoined` is.  `leafToDivided` /
`dividedToLeaf` are stated in the same shape, but over one datum they are
**vacuous**: `W2M1kSourceCandidates.not_leafPair_and_dividedData` is a theorem
(`LeafPair.aligned` and `DividedData.pins_ne` contradict), so the leaf pair and
the divided data never coexist over one datum.  The honest route to Figure 33's
member 2 is the remote copy over
`W2M1kSwapped.swappedData`, as `W2M1kStableIncidence` §6 records; nothing below
claims otherwise.

## What is not here

No `W2M1kCommonBalance.LimitColumns` is built: the three-member family,
remote position included, is assembled elsewhere.  §6 states the leaf
exit at position `0` of an **arbitrary** `LimitColumns`, gated only on that
position being the leaf member, through `W2M1kStableIncidence.presentationAt`
and its `positionCertificate`.
-/

namespace DraismaVargas.LocalCases.W2M1kLeafStableGraph

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open StablePathCount
open StableSourceMatrix
open ResolutionM11 ResolutionM1k GlobalM11Arbitrary
open ResolutionAwayFromWall
open FullDimensionalSource
open W2M1kSourceCandidates W2M1kLeaves
open W2M1kStableGraph
open W2M1kLeafStableLift W2M1kLeafRowDescent W2M1kLeafLimitMatrix
open LimitChainCore (pasted newSourceEdge_incident_old newSourceEdge_incident_fresh
  oldSourceEdge_ne_newSourceEdge sourceEndpoint_eq_of_rel sourceEndpoint_fresh_eq_of_rel)
open StableGraphIncidence (BranchVertex)
open W2M1kCommonBalance (LimitMember LimitColumns)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## §1  `M⁽¹⁾`'s branch vertex

Base I.a's fresh endpoint over `A₀ ∖ {x}`, of surviving valency three.  Any
sheet of that set names it; `pair.second` is the one the census already used,
so no re-anchoring is needed anywhere below. -/

/-- **The branch vertex of `M⁽¹⁾`**: the fresh trivalent endpoint over
`A₀ ∖ {x}`, anchored at `pair.second`. -/
noncomputable def leafBranchVertex (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) : (LeafPair.candidate input shape pair).datum.SourceVertex :=
  (LeafPair.candidate input shape pair).datum.sourceEndpoint (freshVertex target) pair.second

/-- Every sheet of `A₀ ∖ {x}` names it. -/
theorem leaf_fresh_endpoint_eq_branchVertex (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (hNe : sheet ≠ pinSheet profile 0) :
    (LeafPair.candidate input shape pair).datum.sourceEndpoint (freshVertex target) sheet =
      leafBranchVertex input shape pair :=
  leaf_fresh_vertex_eq input shape pair sheet pair.second hWall hNe pair.rel_second
    (Ne.symm pair.ne_second)

/-- **It has surviving valency three.** -/
theorem leaf_nonDanglingValency_branchVertex (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile) :
    nonDanglingValency (LeafPair.candidate input shape pair).datum
      (leafBranchVertex input shape pair) = 3 :=
  leaf_nonDanglingValency_fresh_branch input shape pair pair.second pair.rel_second
    (Ne.symm pair.ne_second)

/-- **Its surviving star**: `e₂`, `e₃` and the regrown occurrence through
`pair.second`.  The other `k - 1` regrown arms above `A₀` were pruned at the
target leaf. -/
theorem leaf_branchVertex_star (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    nonDanglingIncident (LeafPair.candidate input shape pair).datum
        (leafBranchVertex input shape pair) =
      {(LeafPair.candidate input shape pair).oldSourceEdge profile.second.1,
        (LeafPair.candidate input shape pair).oldSourceEdge profile.third.1,
        (LeafPair.candidate input shape pair).newSourceEdge pair.second} :=
  leaf_nonDanglingIncident_fresh_branch input shape pair pair.second pair.rel_second
    (Ne.symm pair.ne_second)

/-- **The whole target leaf is outside the branch subtype.**  Its source
vertices carry two regrown arms over the retained pair and nothing at all
anywhere else. -/
theorem leaf_left_valency_le_two (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (sheet : Fin degree) :
    nonDanglingValency (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).datum.sourceEndpoint
        (oldVertex target wall) sheet) ≤ 2 := by
  classical
  by_cases hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet
  · by_cases hPin : sheet = pinSheet profile 0
    · subst hPin
      exact le_of_eq (leaf_nonDanglingValency_left_pair input shape pair)
    · by_cases hSecond : sheet = pair.second
      · subst hSecond
        rw [← leaf_left_vertex_eq input shape pair]
        exact le_of_eq (leaf_nonDanglingValency_left_pair input shape pair)
      · rw [← card_nonDanglingIncident,
          leaf_nonDanglingIncident_left_singleton input shape pair sheet hWall hPin hSecond]
        simp
  · rw [← card_nonDanglingIncident,
      leaf_nonDanglingIncident_left_background input shape pair sheet hWall]
    simp

/-! ## §2  The vertex map

The shape is the core's `LimitChainCore.GraphData.branchImage`: the
distinguished block to the member's own branch vertex, a background wall block
to the fresh endpoint over its own sheet, everything off the wall to its
retained copy.  Only the proofs are bespoke. -/

/-- The member vertex an incoming source vertex becomes. -/
noncomputable def leafBranchImage (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (vertex : data.SourceVertex) :
    (LeafPair.candidate input shape pair).datum.SourceVertex := by
  classical
  exact if vertex.1.1 = wall then
      (if (data.vertexPartition wall).Rel (pinSheet profile 0) vertex.1.2 then
        leafBranchVertex input shape pair
      else (LeafPair.candidate input shape pair).datum.sourceEndpoint
        (freshVertex target) vertex.1.2)
    else retainedVertex (LeafPair.candidate input shape pair) vertex

theorem leafBranchImage_away (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) {vertex : data.SourceVertex} (hAway : vertex.1.1 ≠ wall) :
    leafBranchImage input shape pair vertex =
      retainedVertex (LeafPair.candidate input shape pair) vertex := by
  classical
  exact if_neg hAway

theorem leafBranchImage_selected (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) {vertex : data.SourceVertex} (hAt : vertex.1.1 = wall)
    (hSelected : (data.vertexPartition wall).Rel (pinSheet profile 0) vertex.1.2) :
    leafBranchImage input shape pair vertex = leafBranchVertex input shape pair := by
  classical
  exact (if_pos hAt).trans (if_pos hSelected)

theorem leafBranchImage_background (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) {vertex : data.SourceVertex} (hAt : vertex.1.1 = wall)
    (hBackground : ¬ (data.vertexPartition wall).Rel (pinSheet profile 0) vertex.1.2) :
    leafBranchImage input shape pair vertex =
      (LeafPair.candidate input shape pair).datum.sourceEndpoint
        (freshVertex target) vertex.1.2 := by
  classical
  exact (if_pos hAt).trans (if_neg hBackground)

/-- Off `A₀` the fresh endpoints of two sheets of one incoming wall block
agree: there the member installs `M11SourceCandidates.backgroundResolution`,
which retains the whole block. -/
theorem leaf_background_fresh_endpoint_eq (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile) {first second : Fin degree}
    (hBackground : ¬ (data.vertexPartition wall).Rel (pinSheet profile 0) first)
    (hRel : (data.vertexPartition wall).Rel first second) :
    (LeafPair.candidate input shape pair).datum.sourceEndpoint (freshVertex target) first =
      (LeafPair.candidate input shape pair).datum.sourceEndpoint (freshVertex target) second :=
  sourceEndpoint_fresh_eq_of_rel _ _
    ((leaf_pasted_right_rel_background input shape pair first second hBackground).mpr hRel)

/-- A background fresh endpoint is never the branch vertex: the two sheets
would then lie in one incoming wall block. -/
theorem leaf_branchVertex_ne_background (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile) {sheet : Fin degree}
    (hBackground : ¬ (data.vertexPartition wall).Rel (pinSheet profile 0) sheet) :
    (LeafPair.candidate input shape pair).datum.sourceEndpoint (freshVertex target) sheet ≠
      leafBranchVertex input shape pair := by
  intro hEqual
  have hRel :
      ((LeafPair.candidate input shape pair).datum.vertexPartition (freshVertex target)).Rel
        sheet pair.second :=
    (((LeafPair.candidate input shape pair).datum.sourceEndpoint_eq_iff
      (freshVertex target) sheet _).mp hEqual).2.trans
      (((LeafPair.candidate input shape pair).datum.vertexPartition
        (freshVertex target)).rel_repr_left pair.second)
  exact hBackground
    (pair.rel_second.trans
      ((leaf_background_fresh_rel input shape pair sheet pair.second hBackground).mp hRel).symm)

/-- A retained vertex is never a fresh one: the target places differ. -/
theorem leaf_retained_ne_fresh (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) {vertex : data.SourceVertex} (sheet : Fin degree) :
    retainedVertex (LeafPair.candidate input shape pair) vertex ≠
      (LeafPair.candidate input shape pair).datum.sourceEndpoint (freshVertex target) sheet := by
  intro hEqual
  have hTarget : oldVertex target vertex.1.1 = freshVertex target :=
    congrArg (fun item : (LeafPair.candidate input shape pair).datum.SourceVertex ↦ item.1.1)
      hEqual
  simp only [oldVertex, freshVertex] at hTarget
  exact absurd hTarget (by simp)

/-- **The vertex map is injective.** -/
theorem leafBranchImage_injective (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    Function.Injective (leafBranchImage input shape pair) := by
  classical
  intro first second hEqual
  by_cases hFirstAt : first.1.1 = wall
  · by_cases hSecondAt : second.1.1 = wall
    · have hFirstRepr : (data.vertexPartition wall).repr first.1.2 = first.1.2 := by
        have := first.2
        rw [hFirstAt] at this
        exact this
      have hSecondRepr : (data.vertexPartition wall).repr second.1.2 = second.1.2 := by
        have := second.2
        rw [hSecondAt] at this
        exact this
      by_cases hFirstSel : (data.vertexPartition wall).Rel (pinSheet profile 0) first.1.2
      · by_cases hSecondSel : (data.vertexPartition wall).Rel (pinSheet profile 0) second.1.2
        · refine Subtype.ext (Prod.ext (hFirstAt.trans hSecondAt.symm) ?_)
          exact hFirstRepr.symm.trans
            ((hFirstSel.symm.trans hSecondSel).trans hSecondRepr)
        · exact absurd
            ((leafBranchImage_background input shape pair hSecondAt hSecondSel).symm.trans
              (hEqual.symm.trans (leafBranchImage_selected input shape pair hFirstAt hFirstSel)))
            (leaf_branchVertex_ne_background input shape pair hSecondSel)
      · by_cases hSecondSel : (data.vertexPartition wall).Rel (pinSheet profile 0) second.1.2
        · exact absurd
            ((leafBranchImage_background input shape pair hFirstAt hFirstSel).symm.trans
              (hEqual.trans (leafBranchImage_selected input shape pair hSecondAt hSecondSel)))
            (leaf_branchVertex_ne_background input shape pair hFirstSel)
        · have hFresh :=
            (leafBranchImage_background input shape pair hFirstAt hFirstSel).symm.trans
              (hEqual.trans (leafBranchImage_background input shape pair hSecondAt hSecondSel))
          have hRel :
              ((LeafPair.candidate input shape pair).datum.vertexPartition
                (freshVertex target)).Rel first.1.2 second.1.2 :=
            (((LeafPair.candidate input shape pair).datum.sourceEndpoint_eq_iff
              (freshVertex target) first.1.2 _).mp hFresh).2.trans
              (((LeafPair.candidate input shape pair).datum.vertexPartition
                (freshVertex target)).rel_repr_left second.1.2)
          have hWall := (leaf_background_fresh_rel input shape pair first.1.2 second.1.2
            hFirstSel).mp hRel
          refine Subtype.ext (Prod.ext (hFirstAt.trans hSecondAt.symm) ?_)
          exact hFirstRepr.symm.trans (hWall.trans hSecondRepr)
    · by_cases hFirstSel : (data.vertexPartition wall).Rel (pinSheet profile 0) first.1.2
      · exact absurd ((leafBranchImage_away input shape pair hSecondAt).symm.trans
          (hEqual.symm.trans (leafBranchImage_selected input shape pair hFirstAt hFirstSel)))
          (leaf_retained_ne_fresh input shape pair pair.second)
      · exact absurd ((leafBranchImage_away input shape pair hSecondAt).symm.trans
          (hEqual.symm.trans (leafBranchImage_background input shape pair hFirstAt hFirstSel)))
          (leaf_retained_ne_fresh input shape pair first.1.2)
  · by_cases hSecondAt : second.1.1 = wall
    · by_cases hSecondSel : (data.vertexPartition wall).Rel (pinSheet profile 0) second.1.2
      · exact absurd ((leafBranchImage_away input shape pair hFirstAt).symm.trans
          (hEqual.trans (leafBranchImage_selected input shape pair hSecondAt hSecondSel)))
          (leaf_retained_ne_fresh input shape pair pair.second)
      · exact absurd ((leafBranchImage_away input shape pair hFirstAt).symm.trans
          (hEqual.trans (leafBranchImage_background input shape pair hSecondAt hSecondSel)))
          (leaf_retained_ne_fresh input shape pair second.1.2)
    · exact ResolutionStableIncidence.retainedVertex_injective_away
        (LeafPair.candidate input shape pair) first second
        hFirstAt hSecondAt
        ((leafBranchImage_away input shape pair hFirstAt).symm.trans
          (hEqual.trans (leafBranchImage_away input shape pair hSecondAt)))

/-! ### Surviving valency is preserved -/

/-- The incoming distinguished source vertex, read at any sheet of `A₀`. -/
theorem leaf_incoming_selected_valency (profile : W2R2SourceProfile.SourceProfile data star block)
    {sheet : Fin degree} (hSelected : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet) :
    nonDanglingValency data (data.sourceEndpoint wall sheet) = 3 := by
  rw [← sourceEndpoint_eq_of_rel data wall ((pinSheet_rel 0).trans hSelected)]
  exact profile.valency

/-- **Every surviving valency is preserved.** -/
theorem leaf_nonDanglingValency_branchImage (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile) (vertex : data.SourceVertex) :
    nonDanglingValency (LeafPair.candidate input shape pair).datum
        (leafBranchImage input shape pair vertex) =
      nonDanglingValency data vertex := by
  classical
  by_cases hAt : vertex.1.1 = wall
  · have hVertex : data.sourceEndpoint wall vertex.1.2 = vertex :=
      (data.sourceEndpoint_eq_iff wall vertex.1.2 vertex).mpr ⟨hAt.symm, rfl⟩
    by_cases hSelected : (data.vertexPartition wall).Rel (pinSheet profile 0) vertex.1.2
    · rw [leafBranchImage_selected input shape pair hAt hSelected,
        leaf_nonDanglingValency_branchVertex input shape pair, ← hVertex]
      exact (leaf_incoming_selected_valency profile hSelected).symm
    · rw [leafBranchImage_background input shape pair hAt hSelected,
        leaf_nonDanglingValency_background input shape pair vertex.1.2 hSelected, hVertex]
  · rw [leafBranchImage_away input shape pair hAt]
    exact nonDanglingValency_retainedVertex _ input.valid
      (leaf_sourceGenus input shape pair) vertex hAt

/-- **Every surviving branch vertex of `M⁽¹⁾` is hit.**  The target leaf has
none, the fresh endpoint over `{x}` is divalent, every fresh endpoint over
`A₀ ∖ {x}` *is* the branch vertex, and off `A₀` the fresh endpoints are the
incoming wall vertices. -/
theorem leaf_exists_branchImage (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (w : (LeafPair.candidate input shape pair).datum.SourceVertex)
    (hBranch : 3 ≤ nonDanglingValency (LeafPair.candidate input shape pair).datum w) :
    ∃ vertex : data.SourceVertex, leafBranchImage input shape pair vertex = w := by
  classical
  have hSelf : (LeafPair.candidate input shape pair).datum.sourceEndpoint w.1.1 w.1.2 = w :=
    ((LeafPair.candidate input shape pair).datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨rfl, rfl⟩
  cases hTarget : w.1.1 with
  | inl place =>
      by_cases hAt : place = wall
      · subst place
        exfalso
        have hEndpoint : (LeafPair.candidate input shape pair).datum.sourceEndpoint
            (oldVertex target wall) w.1.2 = w :=
          (congrArg (fun item ↦ (LeafPair.candidate input shape pair).datum.sourceEndpoint
            item w.1.2) hTarget.symm).trans hSelf
        have hLe := leaf_left_valency_le_two input shape pair w.1.2
        rw [hEndpoint] at hLe
        omega
      · obtain ⟨old, hOld, hVertex⟩ := exists_retainedVertex_of_target
          (LeafPair.candidate input shape pair) w place hAt hTarget
        exact ⟨old, (leafBranchImage_away input shape pair (hOld ▸ hAt)).trans hVertex⟩
  | inr point =>
      cases point
      have hEndpoint : (LeafPair.candidate input shape pair).datum.sourceEndpoint
          (freshVertex target) w.1.2 = w :=
        (congrArg (fun item ↦ (LeafPair.candidate input shape pair).datum.sourceEndpoint
          item w.1.2) hTarget.symm).trans hSelf
      by_cases hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) w.1.2
      · by_cases hPin : w.1.2 = pinSheet profile 0
        · exfalso
          have hValency := leaf_nonDanglingValency_fresh_pin input shape pair
          rw [← hPin, hEndpoint] at hValency
          omega
        · refine ⟨data.sourceEndpoint wall (pinSheet profile 0), ?_⟩
          refine (leafBranchImage_selected input shape pair rfl
            ((data.vertexPartition wall).rel_repr_right _)).trans ?_
          exact (leaf_fresh_endpoint_eq_branchVertex input shape pair w.1.2 hWall
            hPin).symm.trans hEndpoint
      · refine ⟨data.sourceEndpoint wall w.1.2, ?_⟩
        have hBackground : ¬ (data.vertexPartition wall).Rel (pinSheet profile 0)
            ((data.vertexPartition wall).repr w.1.2) := fun hRel ↦
          hWall (hRel.trans ((data.vertexPartition wall).rel_repr_left w.1.2))
        refine (leafBranchImage_background input shape pair rfl hBackground).trans ?_
        exact (leaf_background_fresh_endpoint_eq input shape pair hBackground
          ((data.vertexPartition wall).rel_repr_left w.1.2)).trans hEndpoint

/-- **The bijection of surviving branch vertices.** -/
noncomputable def leafBranchVertexEquiv (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    BranchVertex data ≃ BranchVertex (LeafPair.candidate input shape pair).datum :=
  Equiv.ofBijective
    (fun vertex ↦ (⟨leafBranchImage input shape pair vertex.1, by
      rw [leaf_nonDanglingValency_branchImage input shape pair]
      exact vertex.2⟩ : BranchVertex (LeafPair.candidate input shape pair).datum))
    ⟨by
      intro first second hEqual
      exact Subtype.ext (leafBranchImage_injective input shape pair
        (congrArg Subtype.val hEqual)),
      by
      intro w
      obtain ⟨vertex, hVertex⟩ := leaf_exists_branchImage input shape pair w.1 w.2
      refine ⟨⟨vertex, ?_⟩, Subtype.ext hVertex⟩
      rw [← leaf_nonDanglingValency_branchImage input shape pair vertex, hVertex]
      exact w.2⟩

@[simp] theorem leafBranchVertexEquiv_apply (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile) (vertex : BranchVertex data) :
    (leafBranchVertexEquiv input shape pair vertex).1 =
      leafBranchImage input shape pair vertex.1 := rfl

/-! ## §3  The three incidence identities

Off the wall and off `A₀` the flag is retention itself; above `A₀` it is the
three-occurrence dictionary the census fixes. -/

/-- **Off `A₀` the surviving star is the literal `oldSourceEdge`-image.**  Every
background regrown occurrence of `M⁽¹⁾` is pruned, so no replacement bijection
enters; this is `ResolutionStableIncidence.incidenceCount_retainedVertex`'s
argument at the member's background fresh vertices. -/
theorem leaf_incidenceCount_background (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (sheet : Fin degree)
    (hBackground : ¬ (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (path : StablePath data) :
    incidenceCount data (data.sourceEndpoint wall sheet) path =
      incidenceCount (LeafPair.candidate input shape pair).datum
        ((LeafPair.candidate input shape pair).datum.sourceEndpoint (freshVertex target) sheet)
        (leafStablePathEquiv input shape pair path) := by
  classical
  unfold incidenceCount
  apply Finset.card_bij
    (fun edge _ ↦ retainedEdge (LeafPair.candidate input shape pair) input.valid.1 edge)
  · intro edge hEdge
    simp only [Finset.mem_filter, mem_incidentEdges] at hEdge ⊢
    refine ⟨(leaf_background_old_incident_iff input shape pair sheet hBackground edge.1).mpr
      hEdge.1, ?_⟩
    rw [← leafStablePathEquiv_mk input shape pair edge, hEdge.2]
  · intro first _ second _ hEq
    exact retainedEdge_injective _ input.valid.1 hEq
  · intro edge hEdge
    simp only [Finset.mem_filter, mem_incidentEdges] at hEdge
    have hMem : edge.1 ∈ nonDanglingIncident (LeafPair.candidate input shape pair).datum
        ((LeafPair.candidate input shape pair).datum.sourceEndpoint
          (freshVertex target) sheet) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hEdge.1⟩
    rw [leaf_nonDanglingIncident_background input shape pair sheet hBackground] at hMem
    obtain ⟨old, hOld, hEqual⟩ := Finset.mem_image.mp hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hOld
    let oldEdge : NonDanglingEdge data := ⟨old, hSurvives⟩
    have hRetained : retainedEdge (LeafPair.candidate input shape pair) input.valid.1 oldEdge =
        edge := Subtype.ext hEqual
    refine ⟨oldEdge, ?_, hRetained⟩
    simp only [Finset.mem_filter, mem_incidentEdges]
    refine ⟨hIncident, (leafStablePathEquiv input shape pair).injective ?_⟩
    rw [leafStablePathEquiv_mk, hRetained]
    exact hEdge.2

/-! ### The branch flag

Three distinct occurrences, not three distinct rows: `e₂` and `e₃` retained,
`e₁` sent to the regrown occurrence through `pair.second`. -/

/-- The retained `e₂`, one of the two flags `M⁽¹⁾` keeps at its branch. -/
noncomputable def leafSecondEnd (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) : NonDanglingEdge (LeafPair.candidate input shape pair).datum :=
  retainedEdge (LeafPair.candidate input shape pair) input.valid.1
    ⟨profile.second.1, profile.second_survives⟩

/-- The retained `e₃`. -/
noncomputable def leafThirdEnd (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) : NonDanglingEdge (LeafPair.candidate input shape pair).datum :=
  retainedEdge (LeafPair.candidate input shape pair) input.valid.1
    ⟨profile.third.1, profile.third_survives⟩

/-- The regrown occurrence through `pair.second`, the flag `e₁` is sent to. -/
noncomputable def leafNewEnd (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) : NonDanglingEdge (LeafPair.candidate input shape pair).datum :=
  ⟨(LeafPair.candidate input shape pair).newSourceEdge pair.second,
    leaf_new_second_survives input shape pair⟩

theorem leafSecondEnd_ne_leafThirdEnd (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    leafSecondEnd input shape pair ≠ leafThirdEnd input shape pair := fun hEqual ↦
  leaf_second_ne_third input shape pair (congrArg Subtype.val hEqual)

theorem leafSecondEnd_ne_leafNewEnd (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    leafSecondEnd input shape pair ≠ leafNewEnd input shape pair := fun hEqual ↦
  oldSourceEdge_ne_newSourceEdge _ _ (congrArg Subtype.val hEqual)

theorem leafThirdEnd_ne_leafNewEnd (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    leafThirdEnd input shape pair ≠ leafNewEnd input shape pair := fun hEqual ↦
  oldSourceEdge_ne_newSourceEdge _ _ (congrArg Subtype.val hEqual)

/-- `e₁` and `e₂` are distinct incoming occurrences. -/
theorem leaf_incoming_first_ne_second (profile : W2R2SourceProfile.SourceProfile data star block) :
    (⟨profile.first.1, profile.first_survives⟩ : NonDanglingEdge data) ≠
      ⟨profile.second.1, profile.second_survives⟩ := fun hEqual ↦
  W2M1kGraphData.first_ne_second_edge profile
    (congrArg (fun edge : NonDanglingEdge data ↦ edge.1) hEqual)

/-- `e₁` is above `t₂` and `e₃` above `t₃`. -/
theorem leaf_incoming_first_ne_third (profile : W2R2SourceProfile.SourceProfile data star block) :
    (⟨profile.first.1, profile.first_survives⟩ : NonDanglingEdge data) ≠
      ⟨profile.third.1, profile.third_survives⟩ := fun hEqual ↦
  W2M1kGraphData.first_target_ne profile
    ((congrArg (fun edge : NonDanglingEdge data ↦ edge.1.1.1) hEqual).trans profile.third_target)

/-- and so is `e₂`. -/
theorem leaf_incoming_second_ne_third (profile : W2R2SourceProfile.SourceProfile data star block) :
    (⟨profile.second.1, profile.second_survives⟩ : NonDanglingEdge data) ≠
      ⟨profile.third.1, profile.third_survives⟩ := fun hEqual ↦
  W2M1kGraphData.second_target_ne profile
    ((congrArg (fun edge : NonDanglingEdge data ↦ edge.1.1.1) hEqual).trans profile.third_target)

theorem leafSecondEnd_stablePath (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    (leafSecondEnd input shape pair).stablePath =
      leafStablePathEquiv input shape pair
        (NonDanglingEdge.stablePath ⟨profile.second.1, profile.second_survives⟩) :=
  (leafStablePathEquiv_mk input shape pair ⟨profile.second.1, profile.second_survives⟩).symm

theorem leafThirdEnd_stablePath (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    (leafThirdEnd input shape pair).stablePath =
      leafStablePathEquiv input shape pair
        (NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩) :=
  (leafStablePathEquiv_mk input shape pair ⟨profile.third.1, profile.third_survives⟩).symm

/-- **The one row identity the flag needs.**  The regrown occurrence through
`pair.second` lies in `e₁`'s row -- Figure 33's `c⁽¹⁾ = 2c(e₁)` at the
occurrence level. -/
theorem leafNewEnd_stablePath (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    (leafNewEnd input shape pair).stablePath =
      leafStablePathEquiv input shape pair
        (NonDanglingEdge.stablePath ⟨profile.first.1, profile.first_survives⟩) :=
  (leaf_new_second_stablePath_eq input shape pair).trans
    (leafStablePathEquiv_mk input shape pair ⟨profile.first.1, profile.first_survives⟩).symm

/-- **The branch flag preserves every incidence multiplicity.**  Both stars are
read off the census by the three-occurrence indicator formula, so two flags of
one stable loop stay counted separately. -/
theorem leaf_incidenceCount_selected (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (path : StablePath data) :
    incidenceCount data (data.sourceEndpoint wall block.1) path =
      incidenceCount (LeafPair.candidate input shape pair).datum
        (leafBranchVertex input shape pair) (leafStablePathEquiv input shape pair path) := by
  classical
  rw [M11JoinedIncidence.incidenceCount_of_three (data.sourceEndpoint wall block.1)
      ⟨profile.first.1, profile.first_survives⟩ ⟨profile.second.1, profile.second_survives⟩
      ⟨profile.third.1, profile.third_survives⟩
      (leaf_incoming_first_ne_second profile) (leaf_incoming_first_ne_third profile)
      (leaf_incoming_second_ne_third profile)
      (M11JoinedIncidence.nonDanglingIncident_wallBlock profile) path,
    M11JoinedIncidence.incidenceCount_of_three (leafBranchVertex input shape pair)
      (leafSecondEnd input shape pair) (leafThirdEnd input shape pair)
      (leafNewEnd input shape pair)
      (leafSecondEnd_ne_leafThirdEnd input shape pair)
      (leafSecondEnd_ne_leafNewEnd input shape pair)
      (leafThirdEnd_ne_leafNewEnd input shape pair)
      (leaf_branchVertex_star input shape pair) (leafStablePathEquiv input shape pair path),
    leafSecondEnd_stablePath, leafThirdEnd_stablePath, leafNewEnd_stablePath]
  simp only [Equiv.apply_eq_iff_eq]
  split_ifs <;> omega

/-- **Every incidence count is preserved.** -/
theorem leaf_incidenceCount_branchImage (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (vertex : data.SourceVertex) (path : StablePath data) :
    incidenceCount data vertex path =
      incidenceCount (LeafPair.candidate input shape pair).datum
        (leafBranchImage input shape pair vertex) (leafStablePathEquiv input shape pair path) := by
  classical
  by_cases hAt : vertex.1.1 = wall
  · have hVertex : data.sourceEndpoint wall vertex.1.2 = vertex :=
      (data.sourceEndpoint_eq_iff wall vertex.1.2 vertex).mpr ⟨hAt.symm, rfl⟩
    by_cases hSelected : (data.vertexPartition wall).Rel (pinSheet profile 0) vertex.1.2
    · have hAnchor : data.sourceEndpoint wall block.1 = vertex :=
        (sourceEndpoint_eq_of_rel data wall ((pinSheet_rel 0).trans hSelected)).trans hVertex
      rw [leafBranchImage_selected input shape pair hAt hSelected, ← hAnchor]
      exact leaf_incidenceCount_selected input shape pair path
    · refine Eq.trans ?_ (congrArg (fun item ↦
        incidenceCount (LeafPair.candidate input shape pair).datum item
          (leafStablePathEquiv input shape pair path))
        (leafBranchImage_background input shape pair hAt hSelected)).symm
      exact (congrArg (fun item ↦ incidenceCount data item path) hVertex).symm.trans
        (leaf_incidenceCount_background input shape pair vertex.1.2 hSelected path)
  · rw [leafBranchImage_away input shape pair hAt]
    exact ResolutionStableIncidence.incidenceCount_retainedVertex
      (LeafPair.candidate input shape pair) input.valid (leaf_sourceGenus input shape pair)
      (leafStablePathEquiv input shape pair) (leafStablePathEquiv_mk input shape pair)
      vertex hAt path

/-! ## §4  The branch dictionary

The first object `W2M1kStableIncidence` §6 specifies: a
branch-vertex bijection plus a row bijection preserving `incidenceCount`, with
the row field the leaf member's own geometric bijection. -/

/-- **`M⁽¹⁾`'s stable incidence graph is the incoming one.** -/
noncomputable def leafEquivalence (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    StableGraphIncidence.Equivalence data (LeafPair.candidate input shape pair).datum where
  vertex := leafBranchVertexEquiv input shape pair
  row := leafStablePathEquiv input shape pair
  incidence := fun vertex path ↦
    leaf_incidenceCount_branchImage input shape pair vertex.1 path

/-- **Its row map is literally `W2M1kLeafRowDescent`'s bijection**, so the
retained columns of `W2M1kLeafLimitMatrix` and this dictionary read the same
rows. -/
theorem leafEquivalence_row (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    (leafEquivalence input shape pair).row = leafStablePathEquiv input shape pair := rfl

@[simp] theorem leafEquivalence_row_apply (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile) (path : StablePath data) :
    (leafEquivalence input shape pair).row path =
      leafStablePathEquiv input shape pair path := rfl

@[simp] theorem leafEquivalence_vertex (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (vertex : BranchVertex data) :
    ((leafEquivalence input shape pair).vertex vertex).1 =
      leafBranchImage input shape pair vertex.1 := rfl

/-- The branch vertex above `A₀` is the fresh trivalent endpoint, as
`W2M1kStableIncidence` §6 specifies. -/
@[simp] theorem leafEquivalence_selected (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile)
    (vertex : BranchVertex data) (hAt : vertex.1.1.1 = wall)
    (hSelected : (data.vertexPartition wall).Rel (pinSheet profile 0) vertex.1.1.2) :
    ((leafEquivalence input shape pair).vertex vertex).1 = leafBranchVertex input shape pair :=
  leafBranchImage_selected input shape pair hAt hSelected

/-- **Path ends transport to `M⁽¹⁾`.**  The incoming source is connected, so
every incoming path end is a branch and positive incidence at its image
produces a new one. -/
theorem leaf_hasPathEnds (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (hEnds : HasPathEnds data) :
    HasPathEnds (LeafPair.candidate input shape pair).datum :=
  (leafEquivalence input shape pair).hasPathEnds input.valid.1 hEnds

/-! ## §5  The member-to-member certificates, and the leaf's own exit

Each is a composite through the **incoming** stable graph, exactly as
`W2M1kStableIncidence.dividedToJoined` is: that is what lets a presentation
cross from one Figure 33 member to another with no statement about the two
members' own geometries. -/

/-- From `M⁽¹⁾` to `M⁽³⁾`, through the incoming stable graph. -/
noncomputable def leafToJoined (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (geometry : GlobalM1k.Geometry data wall) :
    StableGraphIncidence.Equivalence (LeafPair.candidate input shape pair).datum
      (joinedCandidate star geometry).datum :=
  (leafEquivalence input shape pair).symm.trans
    (W2M1kGraphData.joinedEquivalence input shape geometry)

/-- From `M⁽³⁾` to `M⁽¹⁾`. -/
noncomputable def joinedToLeaf (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (geometry : GlobalM1k.Geometry data wall) :
    StableGraphIncidence.Equivalence (joinedCandidate star geometry).datum
      (LeafPair.candidate input shape pair).datum :=
  (W2M1kGraphData.joinedEquivalence input shape geometry).symm.trans
    (leafEquivalence input shape pair)

/-- From `M⁽¹⁾` to `M⁽²⁾`, in the same shape.  **Vacuous over one datum**:
`W2M1kSourceCandidates.not_leafPair_and_dividedData` is a theorem, and
Figure 33's member 2 is served by the remote copy over
`W2M1kSwapped.swappedData` instead. -/
noncomputable def leafToDivided (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (divided : DividedData profile) :
    StableGraphIncidence.Equivalence (LeafPair.candidate input shape pair).datum
      (DividedData.candidate shape divided).datum :=
  (leafEquivalence input shape pair).symm.trans
    (W2M1kGraphData.dividedEquivalence input shape divided)

/-- From `M⁽²⁾` to `M⁽¹⁾`, equally vacuous over one datum. -/
noncomputable def dividedToLeaf (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (divided : DividedData profile) :
    StableGraphIncidence.Equivalence (DividedData.candidate shape divided).datum
      (LeafPair.candidate input shape pair).datum :=
  (W2M1kGraphData.dividedEquivalence input shape divided).symm.trans
    (leafEquivalence input shape pair)

/-- The two hypotheses of the previous two definitions are jointly
unsatisfiable: the leaf pair and the divided data never coexist over one
datum. -/
theorem leaf_divided_vacuous (pair : LeafPair profile) (divided : DividedData profile) : False :=
  not_leafPair_and_dividedData pair divided

/-- **`M⁽¹⁾`'s outgoing presentation**, from `M⁽³⁾`'s, gated on `M⁽¹⁾`'s own
nonsingularity.  Both genus receipts are discharged:
`W2M1kSourceCandidates.joined_sourceGenus` and `leaf_sourceGenus`.  That the
leaf member's outgoing target is `T_∅` and not `T₂` is not an obstruction --
`W2M1kStableIncidence.expanded_targetEdgeCard` compares two wall-side
assignments of one `target`. -/
noncomputable def leafOutgoingPresentation (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile)
    (geometry : GlobalM1k.Geometry data wall)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (joinedFD : FullDimensionalSourcePresentation
      (joinedCandidate star geometry).datum coordinate)
    (labelling : StableLengthMatrixLabelling
      (LeafPair.candidate input shape pair).datum coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    FullDimensionalSourcePresentation (LeafPair.candidate input shape pair).datum coordinate :=
  W2M1kStableIncidence.outgoingPresentation (data := data)
    (joinedToLeaf input shape pair geometry) (leaf_valid input shape pair) hConnected hGenus
    (joined_sourceGenus geometry) (leaf_sourceGenus input shape pair) joinedFD labelling hDet

/-- It presents `M⁽¹⁾`'s own labelling. -/
theorem leafOutgoingPresentation_presentation_eq (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile)
    (geometry : GlobalM1k.Geometry data wall)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (joinedFD : FullDimensionalSourcePresentation
      (joinedCandidate star geometry).datum coordinate)
    (labelling : StableLengthMatrixLabelling
      (LeafPair.candidate input shape pair).datum coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    (leafOutgoingPresentation input shape pair geometry hConnected hGenus joinedFD labelling
      hDet).labelling.presentation = labelling.presentation := rfl

/-! ## §6  Position `0` of a limit-column receipt

`W2M1kStableIncidence` §5 assembles a member-to-member certificate from two
dictionaries against the incoming stable graph, and §4 states the exit at a
position gated on `W2M1kCommonBalance.LimitColumns.squareMatrix`.  This section
supplies the leaf half of that at position `0`.

No `LimitColumns` is built here.  The single hypothesis is that position `0` is
the leaf member -- `leafLimitMember`, whose `row` and `retained` fields are
`W2M1kLeafRowDescent.leafStablePathEquiv` and
`W2M1kLeafLimitMatrix.leaf_matrix_retained` -- and it is exactly what an
assembly of the three-member family discharges by `rfl`. -/

/-- **`M⁽¹⁾` as a `W2M1kCommonBalance.LimitMember`.**  Its `row` field is the
dictionary's own row map, so the regrown evaluation
`W2M1kLeafLimitMatrix.leafMember_regrown` -- `c⁽¹⁾ = 2c(e₁)`, no background
term -- is stated against the same rows. -/
noncomputable def leafLimitMember (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) : LimitMember data wall where
  right := (LeafPair.candidate input shape pair).right
  datum := (LeafPair.candidate input shape pair).datum
  valid_of_old := (LeafPair.candidate input shape pair).datum_valid
  row := leafStablePathEquiv input shape pair
  retained := leaf_matrix_retained input shape pair

@[simp] theorem leafLimitMember_datum (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    (leafLimitMember input shape pair).datum = (LeafPair.candidate input shape pair).datum := rfl

@[simp] theorem leafLimitMember_row (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    (leafLimitMember input shape pair).row = leafStablePathEquiv input shape pair := rfl

section Position

variable {shape : Shape profile}

/-- The leaf dictionary, read at position `0` of a limit-column receipt. -/
noncomputable def leafPositionDictionary (input : W2SourceInput data star)
    (pair : LeafPair profile) (limit : LimitColumns profile shape)
    (hMember : limit.member 0 = leafLimitMember input shape pair) :
    StableGraphIncidence.Equivalence data (limit.member 0).datum :=
  cast (congrArg (fun member : LimitMember data wall ↦
    StableGraphIncidence.Equivalence data member.datum) hMember).symm
    (leafEquivalence input shape pair)

/-- Position `0`'s genus receipt, `W2M1kSourceCandidates.leaf_sourceGenus`. -/
theorem leafPositionGenus (input : W2SourceInput data star) (pair : LeafPair profile)
    (limit : LimitColumns profile shape)
    (hMember : limit.member 0 = leafLimitMember input shape pair) :
    genus (limit.member 0).datum.sourceGraph = genus data.sourceGraph := by
  rw [hMember]
  exact leaf_sourceGenus input shape pair

/-- **Figure 33's certified exit at position `0`.**  The certificate is
`W2M1kStableIncidence.positionCertificate` of the incoming position's
dictionary and the leaf one; the presentation is the family's own honest
`LimitColumns.labelling`, gated on its `squareMatrix`. -/
noncomputable def leafPresentationAt (input : W2SourceInput data star)
    (pair : LeafPair profile) (limit : LimitColumns profile shape) (incoming : Fin 3)
    (hMember : limit.member 0 = leafLimitMember input shape pair)
    (incomingDictionary : StableGraphIncidence.Equivalence data (limit.member incoming).datum)
    (hValid : data.Valid) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hIncomingGenus : genus (limit.member incoming).datum.sourceGraph = genus data.sourceGraph)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (incomingFD : FullDimensionalSourcePresentation (limit.member incoming).datum coordinate)
    (hDet : (limit.squareMatrix initial 0).det ≠ 0) :
    FullDimensionalSourcePresentation (limit.member 0).datum coordinate :=
  W2M1kStableIncidence.presentationAtOfDictionaries limit incoming 0 incomingDictionary
    (leafPositionDictionary input pair limit hMember) hValid hConnected hGenus hIncomingGenus
    (leafPositionGenus input pair limit hMember) initial incomingFD hDet

/-- **It presents the family's own honest labelling at position `0`.** -/
theorem leafPresentationAt_presentation_eq (input : W2SourceInput data star)
    (pair : LeafPair profile) (limit : LimitColumns profile shape) (incoming : Fin 3)
    (hMember : limit.member 0 = leafLimitMember input shape pair)
    (incomingDictionary : StableGraphIncidence.Equivalence data (limit.member incoming).datum)
    (hValid : data.Valid) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hIncomingGenus : genus (limit.member incoming).datum.sourceGraph = genus data.sourceGraph)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (incomingFD : FullDimensionalSourcePresentation (limit.member incoming).datum coordinate)
    (hDet : (limit.squareMatrix initial 0).det ≠ 0) :
    (leafPresentationAt input pair limit incoming hMember incomingDictionary hValid hConnected
        hGenus hIncomingGenus initial incomingFD hDet).labelling.presentation =
      (limit.labelling initial 0).presentation := rfl

end Position

end DraismaVargas.LocalCases.W2M1kLeafStableGraph
