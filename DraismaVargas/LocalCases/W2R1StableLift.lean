import DraismaVargas.LocalCases.W2R1StableGraph
import DraismaVargas.LocalCases.LimitChainTwoBlock

/-!
# Figures 37 and 38's induced stable-row map, at **both** blocks

Source: Draisma–Vargas Part I, arXiv:1909.12924, case `{w2-r1}`, sub-cases `{w2-r1-nd3}`
(Figure 37) and `{w2-r1-nd2}` (Figure 38), and the proof of Equation (*) for the
case, whose display is Equation (10).

`W2R1StableGraph` proves the census -- which occurrences survive, the complete
surviving star at each new endpoint and which stable row each surviving new
occurrence joins -- at `A₀`, at `B₀` and over the background, and proves that
`LimitChainCore`'s **one-block** `BackgroundShape` cannot serve a `{w2-r1}`
member (`not_backgroundClauses_both`, `backgroundClauses_not_uniform`).
`LimitChainTwoBlock` is the anchor-set variant that serves it.  This module
reads Equation (10)'s member `q` as that variant's data:

* `anchors` -- the two ramification-one blocks `{A₀, B₀}`, separated by
  `Pair.separate`;
* `backgroundShape` -- off **both** blocks a member installs
  `ResolutionM11.joinedResolutionAt` (`Pair.resolution_of_background`), which
  agrees with `t₀`'s own star block by block because every background wall
  block has local ramification zero (`W2R1StableGraph.background_blockCount`);
* `liftData` -- the clause `LimitChainCore.LiftData.selected_valency_ne_two`
  **fails** here in `{w2-r1-nd2}`
  (`W2R1StableGraph.BlockMember.nd2_selected_valency_eq_two`), so the variant's
  weaker `selected_consecutive` is what has to be supplied, and §2 below
  supplies it from the nd2 row identities of `W2R1StableGraph` §12:
  `e₂` and `e₃` are the block's only incoming survivors there
  (`OccurrenceProfile.exhaustive`), and both members put them in one outgoing
  row;
* `stablePathLift` -- Equation (10)'s induced stable-row map, evaluated by
  retaining any actual surviving occurrence of the old row.

## What is **not** done here

The row descent is `W2R1RowDescent` (this case's `selectedRep` and the two
`selected_*_pair` fields, hence `stablePathEquiv` and `matrix_retained`).  The
regrown evaluations `σ⁽¹⁾(J_{A₀},1) = c_h/(k₂+1)`, `σ⁽²⁾(J_{A₀},1) = c_h/k₂` and
their `B₀` twins, Equation (10) itself, the stable incidence graph
(`LimitChainTwoBlock.GraphData` for this case), the incoming member, the
certified positive exit and an honest presented family are in the modules built
on this one (`W2R1LimitMatrix`, `W2R1CommonBalance`, `W2R1GraphData`,
`W2R1IncomingMatching`, `W2R1ArbitraryIncomingExit`).
-/

namespace DraismaVargas.LocalCases.W2R1StableLift

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open ResolutionM11
open ResolutionAwayFromWall
open W2R1SourceCandidates
open W2R1StableGraph
open LimitChainTwoBlock (IsSelected BackgroundShape LiftData isSelected_of_rel)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## §1  The two anchors

`A₀` and `B₀` are the distinguished blocks; `Pair.separate` says they are
different wall blocks, which is exactly `GraphData.anchors_sep` and the
hypothesis `matrix_new_split_pair` needs. -/

/-- The two ramification-one blocks, as a set of anchors. -/
noncomputable def anchors (pair : Pair data star) : Finset (Fin degree) :=
  {pair.first.1, pair.second.1}

theorem first_mem_anchors (pair : Pair data star) : pair.first.1 ∈ anchors pair :=
  Finset.mem_insert_self _ _

theorem second_mem_anchors (pair : Pair data star) : pair.second.1 ∈ anchors pair :=
  Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

theorem isSelected_iff (pair : Pair data star) (sheet : Fin degree) :
    IsSelected data wall (anchors pair) sheet ↔
      (data.vertexPartition wall).Rel pair.first.1 sheet ∨
        (data.vertexPartition wall).Rel pair.second.1 sheet := by
  constructor
  · rintro ⟨anchor, hAnchor, hRel⟩
    rcases Finset.mem_insert.mp hAnchor with hEq | hEq
    · exact Or.inl (hEq ▸ hRel)
    · exact Or.inr ((Finset.mem_singleton.mp hEq) ▸ hRel)
  · rintro (hRel | hRel)
    · exact isSelected_of_rel (first_mem_anchors pair) hRel
    · exact isSelected_of_rel (second_mem_anchors pair) hRel

theorem not_rel_first_of_not_isSelected {pair : Pair data star} {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall (anchors pair) sheet) :
    ¬ (data.vertexPartition wall).Rel pair.first.1 sheet :=
  fun hRel ↦ hSheet ((isSelected_iff pair sheet).mpr (Or.inl hRel))

theorem not_rel_second_of_not_isSelected {pair : Pair data star} {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall (anchors pair) sheet) :
    ¬ (data.vertexPartition wall).Rel pair.second.1 sheet :=
  fun hRel ↦ hSheet ((isSelected_iff pair sheet).mpr (Or.inr hRel))

/-! ## §2  The background shape at `{A₀, B₀}`

Off both blocks the member installs `joinedResolutionAt`, so its three pasted
partitions all carry the whole wall block there; and `t₀` induces exactly one
class on a background block, so that is also `t₀`'s own star. -/

theorem pasted_left_block (pair : Pair data star) (position : Fin 2)
    {sheet : Fin degree} (hSheet : ¬ IsSelected data wall (anchors pair) sheet) :
    (LimitChainCore.pasted (pair.candidate position)).left.block sheet =
      (data.vertexPartition wall).block sheet := by
  show (LocalResolution.pasteLeft (data.vertexPartition wall)
    (pair.candidate position).resolution (pair.candidate position).contracts).block sheet = _
  unfold LocalResolution.pasteLeft
  rw [SheetPartition.paste_block, background_resolution_at_repr pair position
    (not_rel_first_of_not_isSelected hSheet) (not_rel_second_of_not_isSelected hSheet)]
  rfl

theorem pasted_right_block (pair : Pair data star) (position : Fin 2)
    {sheet : Fin degree} (hSheet : ¬ IsSelected data wall (anchors pair) sheet) :
    (LimitChainCore.pasted (pair.candidate position)).right.block sheet =
      (data.vertexPartition wall).block sheet := by
  show (LocalResolution.pasteRight (data.vertexPartition wall)
    (pair.candidate position).resolution (pair.candidate position).contracts).block sheet = _
  unfold LocalResolution.pasteRight
  rw [SheetPartition.paste_block, background_resolution_at_repr pair position
    (not_rel_first_of_not_isSelected hSheet) (not_rel_second_of_not_isSelected hSheet)]
  rfl

theorem pasted_newEdge_block (pair : Pair data star) (position : Fin 2)
    {sheet : Fin degree} (hSheet : ¬ IsSelected data wall (anchors pair) sheet) :
    (LimitChainCore.pasted (pair.candidate position)).newEdge.block sheet =
      (data.vertexPartition wall).block sheet := by
  show (LocalResolution.pasteNewEdge (data.vertexPartition wall)
    (pair.candidate position).resolution (pair.candidate position).contracts).block sheet = _
  unfold LocalResolution.pasteNewEdge
  rw [SheetPartition.paste_block, background_resolution_at_repr pair position
    (not_rel_first_of_not_isSelected hSheet) (not_rel_second_of_not_isSelected hSheet)]
  rfl

/-- On a background block the retained direction `t₀` induces exactly one
class, so the whole wall block **is** `t₀`'s own star block. -/
theorem wall_block_eq_retained_block (pair : Pair data star)
    {sheet : Fin degree} (hSheet : ¬ IsSelected data wall (anchors pair) sheet) :
    (data.vertexPartition wall).block sheet =
      (data.edgePartition (star.edge 0)).block sheet :=
  (SheetPartition.block_eq_of_refines_of_blockCountWithin_eq_one _ _
    (star.edgePartition_refines_wall data _) sheet
    (background_blockCount pair 0 (not_rel_first_of_not_isSelected hSheet)
      (not_rel_second_of_not_isSelected hSheet))).symm

/-- **Equation (10)'s member, read as a two-block background shape.** -/
noncomputable def backgroundShape (pair : Pair data star) (position : Fin 2) :
    BackgroundShape data wall (anchors pair) where
  toWallCandidate := wallCandidate pair position
  left_block := fun {_} hSheet ↦
    (pasted_left_block pair position hSheet).trans (wall_block_eq_retained_block pair hSheet)
  right_block := fun {_} hSheet ↦ pasted_right_block pair position hSheet
  newEdge_block := fun {_} hSheet ↦
    (pasted_newEdge_block pair position hSheet).trans (wall_block_eq_retained_block pair hSheet)
  genus_eq := pair.candidate_sourceGenus position

@[simp] theorem backgroundShape_candidate (pair : Pair data star) (position : Fin 2) :
    (backgroundShape pair position).candidate = pair.candidate position := rfl

@[simp] theorem backgroundShape_retainedTarget (pair : Pair data star) (position : Fin 2) :
    (backgroundShape pair position).retainedTarget = star.edge 0 := rfl

/-! ## §3  What `nd2` supplies in place of `selected_valency_ne_two`

`LimitChainCore.LiftData.selected_valency_ne_two` fails at a
ramification-one block in `{w2-r1-nd2}`
(`W2R1StableGraph.BlockMember.nd2_selected_valency_eq_two`): the distinguished
incoming vertex is itself divalent there.  What the variant asks for instead
is that the two survivors at such a vertex still land on one outgoing row,
and that is exactly what §12 of the census buys. -/

/-- In `nd2` every incoming survivor at the block's wall vertex is `e₂` or
`e₃`: the profile's incidence list is exhaustive and `e₁` dangles. -/
theorem nd2_survivor_cases {block : WallBlock data wall}
    (profile : W2R1SourceProfile.SourceProfile data star block)
    (hNd2 : IsDangling data profile.first.1)
    {edge : data.SourceEdge} (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge (WallBlock.sourceVertex data wall block)) :
    edge = profile.second.1 ∨ edge = profile.third.1 := by
  rcases profile.exhaustive ⟨edge, hIncident⟩ with hEq | hEq | hEq
  · exfalso
    have hValue : edge = profile.first.1 := congrArg Subtype.val hEq
    rw [hValue] at hSurvives
    exact hSurvives hNd2
  · exact Or.inl (congrArg Subtype.val hEq)
  · exact Or.inr (congrArg Subtype.val hEq)

/-- **In `nd2` the block's two incoming survivors keep one outgoing row**, in
both members.  Retained member: `e'` joins `e₃`'s row (§6) and `e₂`'s row
(§12).  Resolved member: `e''` joins `e₂`'s row (§7) and `e₃`'s row (§12). -/
theorem nd2_old_stablePath_eq {block : WallBlock data wall}
    (member : BlockMember data star block)
    (hNd2 : IsDangling data member.profile.first.1) :
    NonDanglingEdge.stablePath
        (⟨member.candidate.oldSourceEdge member.profile.second.1, member.second_survives⟩ :
          NonDanglingEdge member.candidate.datum) =
      NonDanglingEdge.stablePath
        (⟨member.candidate.oldSourceEdge member.profile.third.1, member.third_survives⟩ :
          NonDanglingEdge member.candidate.datum) := by
  have hRefl : (data.vertexPartition wall).Rel block.1 block.1 := rfl
  by_cases hPosition : member.position = member.double
  · exact (member.retained_new_stablePath_eq_second_nd2 hPosition hNd2 hRefl).symm.trans
      (member.retained_new_stablePath_eq hPosition hRefl)
  · exact (member.resolved_new_second_stablePath_eq hPosition).symm.trans
      (member.resolved_new_second_stablePath_eq_third_nd2 hPosition hNd2 hRefl)

/-- **The variant's selected clause, at one block.**  A consecutive pair of the
incoming stable quotient at a ramification-one block's wall vertex lands on one
outgoing row: in `nd3` the vertex is trivalent and there is no such pair, in
`nd2` the pair is `e₂, e₃` and `nd2_old_stablePath_eq` is the identity.  No
distinctness of the pair is needed: in `nd2` *every* survivor there returns to
the one row carrying `e₂` and `e₃`. -/
theorem selected_consecutive_at_block {block : WallBlock data wall}
    (member : BlockMember data star block) (hValid : data.Valid)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet)
    (first second : NonDanglingEdge data)
    (hFirst : Incident data first.1 (data.sourceEndpoint wall sheet))
    (hSecond : Incident data second.1 (data.sourceEndpoint wall sheet))
    (hValency : nonDanglingValency data (data.sourceEndpoint wall sheet) = 2) :
    (retainedEdge member.candidate hValid.1 first).stablePath =
      (retainedEdge member.candidate hValid.1 second).stablePath := by
  have hVertex : data.sourceEndpoint wall sheet =
      WallBlock.sourceVertex data wall block :=
    (LimitChainCore.sourceEndpoint_eq_of_rel data wall hSheet).symm
  rw [hVertex] at hFirst hSecond hValency
  rcases member.nd_cases with ⟨hThree, _⟩ | ⟨_, hNd2, _, _⟩
  · rw [hThree] at hValency
    exact absurd hValency (by omega)
  · have key : ∀ edge : NonDanglingEdge data,
        Incident data edge.1 (WallBlock.sourceVertex data wall block) →
        (retainedEdge member.candidate hValid.1 edge).stablePath =
          NonDanglingEdge.stablePath
            (⟨member.candidate.oldSourceEdge member.profile.third.1,
              member.third_survives⟩ : NonDanglingEdge member.candidate.datum) ∨
          edge.1 = member.profile.second.1 := by
      intro edge hIncident
      rcases nd2_survivor_cases member.profile hNd2 edge.2 hIncident with hEq | hEq
      · exact Or.inr hEq
      · refine Or.inl ?_
        exact congrArg NonDanglingEdge.stablePath
          (Subtype.ext (congrArg member.candidate.oldSourceEdge hEq))
    have secondRow : ∀ edge : NonDanglingEdge data, edge.1 = member.profile.second.1 →
        (retainedEdge member.candidate hValid.1 edge).stablePath =
          NonDanglingEdge.stablePath
            (⟨member.candidate.oldSourceEdge member.profile.third.1,
              member.third_survives⟩ : NonDanglingEdge member.candidate.datum) := by
      intro edge hEq
      refine Eq.trans ?_ (nd2_old_stablePath_eq member hNd2)
      exact congrArg NonDanglingEdge.stablePath
        (Subtype.ext (congrArg member.candidate.oldSourceEdge hEq))
    have hRowFirst : (retainedEdge member.candidate hValid.1 first).stablePath = _ :=
      (key first hFirst).elim id (secondRow first)
    have hRowSecond : (retainedEdge member.candidate hValid.1 second).stablePath = _ :=
      (key second hSecond).elim id (secondRow second)
    exact hRowFirst.trans hRowSecond.symm

/-! ## §4  The two-block lift data, and Equation (10)'s stable-row map -/

/-- **Equation (10)'s member, read as two-block lift data.**  The selected
clause runs at `A₀` through `firstMember` and at `B₀` through `secondMember`;
neither uses a valency receipt at the distinguished vertex. -/
noncomputable def liftData (pair : Pair data star) (hValid : data.Valid)
    (position : Fin 2) : LiftData data wall (anchors pair) where
  toBackgroundShape := backgroundShape pair position
  valid := hValid
  selected_consecutive := by
    intro sheet hSel first second _hNe hFirst hSecond hValency
    rcases (isSelected_iff pair sheet).mp hSel with hRel | hRel
    · exact selected_consecutive_at_block (firstMember pair hValid position) hValid hRel
        first second hFirst hSecond hValency
    · exact selected_consecutive_at_block (secondMember pair hValid position) hValid hRel
        first second hFirst hSecond hValency

@[simp] theorem liftData_candidate (pair : Pair data star) (hValid : data.Valid)
    (position : Fin 2) :
    (liftData pair hValid position).candidate = pair.candidate position := rfl

/-- Retaining a different occurrence of one old stable row gives the same row
upstairs -- at `A₀`, at `B₀` and over the background. -/
theorem stablePath_retained_eq_of_consecutive (pair : Pair data star) (hValid : data.Valid)
    (position : Fin 2) (first second : NonDanglingEdge data)
    (hConsecutive : Consecutive data first second) :
    (retainedEdge (pair.candidate position) hValid.1 first).stablePath =
      (retainedEdge (pair.candidate position) hValid.1 second).stablePath :=
  (liftData pair hValid position).retained_stablePath_eq_of_consecutive first second hConsecutive

/-- **Equation (10)'s induced stable-row map**, evaluated by retaining any
actual surviving occurrence of the old row. -/
noncomputable def stablePathLift (pair : Pair data star) (hValid : data.Valid)
    (position : Fin 2) :
    StablePath data → StablePath (pair.candidate position).datum :=
  (liftData pair hValid position).stablePathLift

@[simp] theorem stablePathLift_mk (pair : Pair data star) (hValid : data.Valid)
    (position : Fin 2) (edge : NonDanglingEdge data) :
    stablePathLift pair hValid position edge.stablePath =
      (retainedEdge (pair.candidate position) hValid.1 edge).stablePath := rfl

/-- The background replacement bijection of the member, at every wall block
that is neither `A₀` nor `B₀`. -/
theorem nonDanglingValency_fresh_eq (pair : Pair data star) (hValid : data.Valid)
    (position : Fin 2) {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall (anchors pair) sheet) :
    nonDanglingValency (pair.candidate position).datum
        ((pair.candidate position).datum.sourceEndpoint (freshVertex target) sheet) =
      nonDanglingValency data (data.sourceEndpoint wall sheet) :=
  LimitChainTwoBlock.Background.nonDanglingValency_fresh_eq
    (backgroundShape pair position) hValid hSheet

end DraismaVargas.LocalCases.W2R1StableLift
