module

public import DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitGauge
public import DraismaVargas.LocalCases.NonTrivalentValencyTwoRows
public import DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneRows

@[expose] public section

/-!
# Stable rows of the Base II **split** candidate above a two-valent wall

Source: Vargas, Part II (arXiv:2609.09109), Section 5.4 (Case `{v2-nd4}`,
Configuration A, base tree `T_2` = Base II, and the diagrams of its subcases),
read through the labelling convention (1) of Section 5.1.

This module computes the stable rows of the split family: it is the valency-two
analogue of `NonTrivalentValencyTwoRows` (the merge member) over
`NonTrivalentValencyTwoSplitCandidate.validCandidate`, whose receipt
`SplitSetup` is produced by `NonTrivalentValencyTwoSplitGauge`.

## The picture, and why the census has four vertices

Above the anchor `A` the two `t_thick`-classes are `e_alpha` (the class that
splits) and `e_beta`, the two `t_thin`-classes are `e_delta` (the piece, with
`e_delta ⊆ e_alpha`) and `e_epsilon`, and the new edge carries the common
refinement `{e_delta, e_alpha ∖ e_delta, e_beta}`.  So, unlike at the merge,
**both** sides of the new target edge are split in two:

* over `u` (carrying `t_thick`): `S = e_alpha`, seeing its own old occurrence,
  the piece and the bridge -- `nd(S) = 3`; and `P_u = e_beta`, seeing its own
  old occurrence and the pass-through only -- `nd(P_u) = 2`;
* over `v` (carrying `t_thin`): `A_v = e_epsilon`, seeing its own old
  occurrence, the bridge and the pass-through -- `nd(A_v) = 3`; and
  `P_v = e_delta`, seeing its own old occurrence and the piece only --
  `nd(P_v) = 2`.

The two divalent vertices are exactly the paper's pass-through points, so the
*piece* lies on `e_delta`'s retained stable row (through `P_v`) and the
*pass-through* occurrence lies on `e_beta`'s retained row (through `P_u`):
`pieceEdge_stablePath_eq_retained` and `passEdge_stablePath_eq_retained`, the
two-vertex version of
`NonTrivalentValencyThreeSimpleRows.newSourceEdge_stablePath_eq_retained`.  Only
the **bridge** joins two trivalent vertices, so it alone is a new stable row
(`bridgeEdge_isolated`); the stable pairing it realizes is `{h_alpha, h_delta}`
at `S` and `{h_beta, h_epsilon}` at `A_v`, which with the paper's labels is
`H_{2,3}` (Type I) when `e_3` splits and `H_{2,4}` (Type II) when `e_4` does.
These are the type labels of Part II, Subcase `{v2-nd4-t3-k2=k3}`; in Subcase
`{v2-nd4-t3-k2<k3}` Part II attaches the labels Type I and Type II to the two
split members the other way round.  The statements here depend only on which
class splits, not on the names of the types.

## What is proved

* `SplitAnchor`: Configuration A at the wall block with the four named
  survivors of the paper's picture and the split receipt; `splitAnchor_gauged`
  inhabits it at the gauged datum of `NonTrivalentValencyTwoSplitGauge` from
  `k_delta < k_alpha` alone.
* `thin_rel_alpha_epsilon`, `thick_rel_alpha_delta`, `thin_rel_alpha_beta`: the
  four classes really are distributed as the figures show.
* `meet_blockCountWithin_eq_three` and `selectedResolution_euler`: the anchor
  block carries exactly three new-edge classes against two on each side, so
  `candidate_sourceGenus` -- the split candidate preserves the source genus,
  with no receipt beyond the `SplitAnchor`.
* `endpointVertex`, `newEdgeAt`, `bridgeEdge`, `pieceEdge`, `passEdge` and
  their incidences, with the exact outgoing endpoint sizes
  (`endpointVertex_blockCard`, and `endpointVertex_blockCard_index` in the
  paper's indices: `|S| = k_alpha`, `|P_u| = k_beta`, `|A_v| = k_epsilon`,
  `|P_v| = k_delta`).
* The exact surviving stars
  (`nonDanglingIncident_endpointVertex_alpha`, `..._beta`, `..._epsilon`,
  `..._delta`) and hence the census
  `nonDanglingValency_endpointVertex_alpha = 3`,
  `..._epsilon = 3`, `..._beta = 2`, `..._delta = 2`.
* `bridgeEdge_isolated`; `pieceEdge_stablePath_eq_retained` and
  `passEdge_stablePath_eq_retained`.
* `nonDanglingValency_anchor = 4`, the named `OrdinaryBlockDescent`, the
  retained-row map `retainedRow` modulo it, and -- discharging it -- the
  ordinary-block census (`ordinaryStar`, `card_ordinaryStar_add`,
  `mem_nonDanglingIncident_endpointVertex_ordinary`,
  `newEdgeAt_survives_iff_ordinary`), `ordinaryBlockDescent` and the
  **unconditional** `retainedRowFree` (the argument of
  `NonTrivalentValencyTwoDescent`, which applies because off the anchor the
  split candidate installs the same neutral joined resolution).
* `census_of_splitAnchor`: the whole package in one statement.

## Hypotheses left explicit here

1. `SplitAnchor` itself (its `setup` field is the receipt of
   `NonTrivalentValencyTwoSplitGauge`, its `source` field is the classifier of
   `NonTrivalentAnchorValency`, its `split` field is Configuration A).
   `nd(A) = 4` is *derived* here (`nonDanglingValency_anchor`), not assumed.
2. Nothing about the *ordinary* blocks beyond `data.Valid`: the ordinary-block
   bound `nd(B) <= 3` is **not** used and not assumed (as for the merge member,
   it is an input of the row equivalence, not of the descent).
3. No row equivalence `StablePath cand ≃ Option (StablePath data)`, no chart
   re-indexing, no common minor, no exit, no tracking: those are
   `NonTrivalentValencyTwoSplitRowEquiv`, `NonTrivalentValencyTwoSplitRowDictionary`,
   `NonTrivalentValencyTwoSplitExit`, `NonTrivalentValencyTwoSplitTracks` and
   `NonTrivalentValencyTwoSplitStarCount`.
4. The orientation is that of `NonTrivalentValencyTwoCandidate`
   (`rightAssignment`: `t_thick` at `u`); the mirror members are obtained in
   `NonTrivalentValencyTwoSplitExit` by relabelling the wall star.

## Consumers

`NonTrivalentValencyTwoSplitRowEquiv` (the row equivalence and the honest
labelling), the rest of the split family (common minor, exit) and the
valency-two move dispatcher.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitRows

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionCoarseFine
open DraismaVargas.LocalCases.ResolutionM1k
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.W3R1SourceProfile (survivors mem_survivors card_survivors)
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate.Prescribed
  (thickEdge thinEdge thickEdge_eq thinEdge_eq rightAssignment rightAssignment_thick
    rightAssignment_of_ne rightAssignment_eq_false_iff incidentEdges_eq_pair)
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOne (refineOnBlock
  refineOnBlock_rel_iff refineOnBlock_block_of_rel refineOnBlock_blockCard_of_rel
  refineOnBlock_refines refineOnBlock_repr_of_rel refineOnBlock_repr_of_not_rel)
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitGauge (thickEdge_eq_zero
  thinEdge_eq_one)
open DraismaVargas.LocalCases.NonTrivalentValencyTwoGauge (pair_cover)
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneRows
  (refineOnBlock_blockCountWithin blockCountWithin_congr)
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRows (sourceEdge_occurrenceSheet
  survivor_not_isDangling exists_directionSurvivor_eq)
open DraismaVargas.LocalCases.NonTrivalentValencyFourRows (IsStar euler_of_isStar
  isStar_joinedResolutionAt)

/-! ## 0.  Three classes over the new edge -/

section Meet

variable {d : ℕ}

/-- **The anchor carries exactly three new-edge classes.**  With `e_delta`
inside `e_alpha` the common refinement of the two direction partitions on the
anchor block is `{e_delta, e_alpha ∖ e_delta, e_beta}`: the piece, the bridge
and the pass-through.  Without the sub-alignment there would be four, and both
`v`-vertices would be trivalent -- which is the reason for the gauge. -/
theorem meet_blockCountWithin_eq_three (wall thick thin : SheetPartition d)
    (anchor alpha beta delta : Fin d)
    (hAlpha : wall.Rel anchor alpha) (hBeta : wall.Rel anchor beta)
    (hDelta : wall.Rel anchor delta)
    (hSub : thin.block delta ⊆ thick.block alpha)
    (hNotThin : ¬thin.Rel alpha delta) (hNotThick : ¬thick.Rel alpha beta)
    (hThinCover : ∀ i, wall.Rel anchor i → thin.Rel delta i ∨ thin.Rel alpha i)
    (hThickCover : ∀ i, wall.Rel anchor i → thick.Rel alpha i ∨ thick.Rel beta i) :
    (meet thick thin).blockCountWithin wall anchor = 3 := by
  classical
  have hThickDelta : thick.Rel alpha delta :=
    (thick.mem_block_iff _ _).mp (hSub (thin.self_mem_block delta))
  have hThinBeta : thin.Rel alpha beta := by
    rcases hThinCover beta hBeta with hCase | hCase
    · exact absurd ((thick.mem_block_iff _ _).mp
        (hSub ((thin.mem_block_iff _ _).mpr hCase))) hNotThick
    · exact hCase
  have hImage : (wall.block anchor).image (meet thick thin).repr =
      {(meet thick thin).repr delta, (meet thick thin).repr alpha,
        (meet thick thin).repr beta} := by
    ext representative
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨sheet, hSheet, rfl⟩
      have hWall : wall.Rel anchor sheet := (wall.mem_block_iff _ _).mp hSheet
      rcases hThinCover sheet hWall with hCase | hCase
      · left
        have hThickSheet : thick.Rel delta sheet :=
          hThickDelta.symm.trans ((thick.mem_block_iff _ _).mp
            (hSub ((thin.mem_block_iff _ _).mpr hCase)))
        exact ((meet_rel_iff thick thin delta sheet).mpr ⟨hThickSheet, hCase⟩).symm
      · rcases hThickCover sheet hWall with hThickCase | hThickCase
        · right; left
          exact ((meet_rel_iff thick thin alpha sheet).mpr ⟨hThickCase, hCase⟩).symm
        · right; right
          exact ((meet_rel_iff thick thin beta sheet).mpr
            ⟨hThickCase, hThinBeta.symm.trans hCase⟩).symm
    · rintro (rfl | rfl | rfl)
      · exact ⟨delta, (wall.mem_block_iff _ _).mpr hDelta, rfl⟩
      · exact ⟨alpha, (wall.mem_block_iff _ _).mpr hAlpha, rfl⟩
      · exact ⟨beta, (wall.mem_block_iff _ _).mpr hBeta, rfl⟩
  show ((wall.block anchor).image (meet thick thin).repr).card = 3
  rw [hImage]
  have hDeltaAlpha : (meet thick thin).repr delta ≠ (meet thick thin).repr alpha := by
    intro hEq
    exact hNotThin (((meet_rel_iff thick thin delta alpha).mp hEq).2).symm
  have hAlphaBeta : (meet thick thin).repr alpha ≠ (meet thick thin).repr beta := by
    intro hEq
    exact hNotThick ((meet_rel_iff thick thin alpha beta).mp hEq).1
  have hDeltaBeta : (meet thick thin).repr delta ≠ (meet thick thin).repr beta := by
    intro hEq
    exact hNotThick (hThickDelta.trans ((meet_rel_iff thick thin delta beta).mp hEq).1)
  rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact fun hCase ↦ hCase.elim hDeltaAlpha hDeltaBeta),
    Finset.card_insert_of_notMem (by simpa using hAlphaBeta), Finset.card_singleton]

end Meet

/-! ## 1.  The split anchor -/

section Anchor

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (data : GluingDatum target degree)
    (vertex : data.SourceVertex) : DecidableEq (IncidentSourceEdge data vertex) :=
  Classical.decEq _

/-- **The split anchor.**  Configuration A at the wall block, the four named
survivors of the paper's picture (`e_alpha` splits above `u`, `e_beta` passes
through `u`, `e_delta` is the piece and passes through `v`, `e_epsilon` sits at
`A_v`), and the split receipt of
`NonTrivalentValencyTwoSplitCandidate` at the two named sheets. -/
structure SplitAnchor (data : GluingDatum target degree) (star : TwoStar target wall)
    (anchor : WallBlock data wall) where
  /-- the valency-two classifier at the anchor -/
  source : TwoBranchAnchor data star anchor
  /-- Configuration A: both directions carry two survivors -/
  split : ∀ label : Fin 2, (directionSurvivors data star anchor label).card = 2
  /-- the `t_thick`-survivor whose class splits above `u` -/
  alphaEdge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)
  /-- the other `t_thick`-survivor, which passes through `u` -/
  betaEdge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)
  /-- the `t_thin`-survivor forming the piece, which passes through `v` -/
  deltaEdge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)
  /-- the other `t_thin`-survivor, which sits at `A_v` -/
  epsilonEdge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)
  /-- `e_alpha` lies above `star.edge 0` -/
  alpha_mem : alphaEdge ∈ directionSurvivors data star anchor 0
  /-- `e_beta` lies above `star.edge 0` -/
  beta_mem : betaEdge ∈ directionSurvivors data star anchor 0
  /-- `e_delta` lies above `star.edge 1` -/
  delta_mem : deltaEdge ∈ directionSurvivors data star anchor 1
  /-- `e_epsilon` lies above `star.edge 1` -/
  epsilon_mem : epsilonEdge ∈ directionSurvivors data star anchor 1
  /-- the two `t_thick`-survivors are distinct -/
  alpha_ne_beta : alphaEdge ≠ betaEdge
  /-- the two `t_thin`-survivors are distinct -/
  delta_ne_epsilon : deltaEdge ≠ epsilonEdge
  /-- the split receipt at the two named sheets -/
  setup : SplitSetup data star anchor (occurrenceSheet alphaEdge) (occurrenceSheet deltaEdge)

namespace SplitAnchor

variable {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall} (ra : SplitAnchor data star anchor)

include ra in
theorem thick_eq : thickEdge data star anchor = star.edge 0 :=
  thickEdge_eq_zero (ra.split 0)

include ra in
theorem thin_eq : thinEdge data star anchor = star.edge 1 :=
  thinEdge_eq_one (ra.split 0)

/-- `e_alpha` really contains `e_delta`, so `alpha` and `delta` share a
`t_thick`-class. -/
theorem thick_rel_alpha_delta :
    (data.edgePartition (thickEdge data star anchor)).Rel (occurrenceSheet ra.alphaEdge)
      (occurrenceSheet ra.deltaEdge) :=
  ra.setup.same_thick

/-- The two `t_thick`-classes are distinct. -/
theorem not_thick_rel_alpha_beta :
    ¬(data.edgePartition (thickEdge data star anchor)).Rel (occurrenceSheet ra.alphaEdge)
      (occurrenceSheet ra.betaEdge) := by
  rw [ra.thick_eq]
  exact not_rel_occurrenceSheet ra.alpha_mem ra.beta_mem ra.alpha_ne_beta

/-- The two `t_thin`-classes are distinct. -/
theorem not_thin_rel_delta_epsilon :
    ¬(data.edgePartition (thinEdge data star anchor)).Rel (occurrenceSheet ra.deltaEdge)
      (occurrenceSheet ra.epsilonEdge) := by
  rw [ra.thin_eq]
  exact not_rel_occurrenceSheet ra.delta_mem ra.epsilon_mem ra.delta_ne_epsilon

/-- **`e_epsilon` is the `t_thin`-class of `alpha`**: the receipt says `alpha`
is not in `e_delta`, and Configuration A leaves only the other class. -/
theorem thin_rel_alpha_epsilon :
    (data.edgePartition (thinEdge data star anchor)).Rel (occurrenceSheet ra.alphaEdge)
      (occurrenceSheet ra.epsilonEdge) := by
  rcases ra.setup.cover (occurrenceSheet ra.epsilonEdge)
    (occurrenceSheet_wall_rel ra.epsilonEdge) with hCase | hCase
  · exact absurd hCase ra.not_thin_rel_delta_epsilon
  · exact hCase

/-- **`e_beta` lies inside `e_epsilon`**: it misses `e_delta`, which sits
inside `e_alpha`. -/
theorem thin_rel_alpha_beta :
    (data.edgePartition (thinEdge data star anchor)).Rel (occurrenceSheet ra.alphaEdge)
      (occurrenceSheet ra.betaEdge) := by
  rcases ra.setup.cover (occurrenceSheet ra.betaEdge)
    (occurrenceSheet_wall_rel ra.betaEdge) with hCase | hCase
  · refine absurd (((data.edgePartition (thickEdge data star anchor)).mem_block_iff _ _).mp
      (ra.setup.sub (((data.edgePartition (thinEdge data star anchor)).mem_block_iff _ _).mpr
        hCase))) ra.not_thick_rel_alpha_beta
  · exact hCase

/-- The two `t_thick`-classes cover the anchor block. -/
theorem thick_cover {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel anchor.1 sheet) :
    (data.edgePartition (thickEdge data star anchor)).Rel (occurrenceSheet ra.alphaEdge)
        sheet ∨
      (data.edgePartition (thickEdge data star anchor)).Rel (occurrenceSheet ra.betaEdge)
        sheet := by
  rw [ra.thick_eq]
  exact pair_cover ra.source (ra.split 0) ra.alpha_mem ra.beta_mem ra.alpha_ne_beta hSheet

end SplitAnchor

/-! ## 2.  The candidate's resolution at every wall block, and the source genus -/

section Candidate

variable {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall} (ra : SplitAnchor data star anchor)

local notation "cand" => (validCandidate ra.setup)

/-- At the anchor block the candidate uses the split resolution. -/
theorem candidate_resolution_of_wall_rel (block : Fin degree)
    (hBlock : (data.vertexPartition wall).Rel anchor.1 block) :
    (cand).resolution block = selectedResolution data star anchor :=
  NonTrivalentValencyTwoSplitCandidate.candidate_resolution_of_wall_rel ra.setup _ block hBlock

/-- Off the anchor block the split candidate really uses the neutral joined
resolution of `NonTrivalentValencyTwoCandidate`'s `subdivisionBackground` --
exactly as the merge candidate does, which is why the ordinary-block census of
`NonTrivalentValencyTwoDescent` ports verbatim. -/
theorem candidate_resolution_of_not_wall_rel (block : Fin degree)
    (hBlock : ¬ (data.vertexPartition wall).Rel anchor.1 block) :
    (cand).resolution block = joinedResolutionAt (data.vertexPartition wall) := by
  unfold NonTrivalentValencyTwoSplitCandidate.validCandidate
    NonTrivalentValencyTwoSplitCandidate.candidate
    NonTrivalentValencyTwoCandidate.Prescribed.SubdivisionBackground.background
    GlobalM11Arbitrary.Background.install
  exact LocalResolution.onBlock_of_not_rel _ _ _ _ _ hBlock

theorem selectedResolution_left :
    (selectedResolution data star anchor).left =
      refineOnBlock (data.vertexPartition wall)
        (data.edgePartition (thickEdge data star anchor)) anchor.1
        (thickEdge_refines_wall data star anchor) := rfl

theorem selectedResolution_right :
    (selectedResolution data star anchor).right =
      refineOnBlock (data.vertexPartition wall)
        (data.edgePartition (thinEdge data star anchor)) anchor.1
        (thinEdge_refines_wall data star anchor) := rfl

theorem selectedResolution_newEdge :
    (selectedResolution data star anchor).newEdge =
      refineOnBlock (data.vertexPartition wall)
        (meet (data.edgePartition (thickEdge data star anchor))
          (data.edgePartition (thinEdge data star anchor))) anchor.1
        ((meet_refines_left _ _).trans (thickEdge_refines_wall data star anchor)) := rfl

include ra in
/-- Over `u` the anchor block carries the two `t_thick`-classes. -/
theorem left_blockCountWithin (block : Fin degree)
    (hBlock : (data.vertexPartition wall).Rel anchor.1 block) :
    (selectedResolution data star anchor).left.blockCountWithin
      (data.vertexPartition wall) block = 2 := by
  rw [selectedResolution_left (data := data) (star := star) (anchor := anchor),
    refineOnBlock_blockCountWithin (data.vertexPartition wall)
      (data.edgePartition (thickEdge data star anchor)) anchor.1 block
      (thickEdge_refines_wall data star anchor) hBlock,
    ← blockCountWithin_congr (data.edgePartition (thickEdge data star anchor))
      (data.vertexPartition wall) hBlock, ra.thick_eq,
    blockCountWithin_eq_card_directionSurvivors ra.source 0, ra.split 0]

include ra in
/-- Over `v` the anchor block carries the two `t_thin`-classes. -/
theorem right_blockCountWithin (block : Fin degree)
    (hBlock : (data.vertexPartition wall).Rel anchor.1 block) :
    (selectedResolution data star anchor).right.blockCountWithin
      (data.vertexPartition wall) block = 2 := by
  rw [selectedResolution_right (data := data) (star := star) (anchor := anchor),
    refineOnBlock_blockCountWithin (data.vertexPartition wall)
      (data.edgePartition (thinEdge data star anchor)) anchor.1 block
      (thinEdge_refines_wall data star anchor) hBlock,
    ← blockCountWithin_congr (data.edgePartition (thinEdge data star anchor))
      (data.vertexPartition wall) hBlock, ra.thin_eq,
    blockCountWithin_eq_card_directionSurvivors ra.source 1, ra.split 1]

include ra in
/-- **Three occurrences over the new edge**: the piece, the bridge and the
pass-through. -/
theorem newEdge_blockCountWithin (block : Fin degree)
    (hBlock : (data.vertexPartition wall).Rel anchor.1 block) :
    (selectedResolution data star anchor).newEdge.blockCountWithin
      (data.vertexPartition wall) block = 3 := by
  rw [selectedResolution_newEdge (data := data) (star := star) (anchor := anchor),
    refineOnBlock_blockCountWithin (data.vertexPartition wall)
      (meet (data.edgePartition (thickEdge data star anchor))
        (data.edgePartition (thinEdge data star anchor))) anchor.1 block
      ((meet_refines_left _ _).trans (thickEdge_refines_wall data star anchor)) hBlock,
    ← blockCountWithin_congr
      (meet (data.edgePartition (thickEdge data star anchor))
        (data.edgePartition (thinEdge data star anchor)))
      (data.vertexPartition wall) hBlock]
  exact meet_blockCountWithin_eq_three (data.vertexPartition wall)
    (data.edgePartition (thickEdge data star anchor))
    (data.edgePartition (thinEdge data star anchor)) anchor.1
    (occurrenceSheet ra.alphaEdge) (occurrenceSheet ra.betaEdge)
    (occurrenceSheet ra.deltaEdge) (occurrenceSheet_wall_rel _)
    (occurrenceSheet_wall_rel _) (occurrenceSheet_wall_rel _) ra.setup.sub
    ra.setup.not_thin ra.not_thick_rel_alpha_beta ra.setup.cover
    (fun _ hi ↦ ra.thick_cover hi)

include ra in
/-- **The blockwise Euler identity at the anchor**: `3 + 1 = 2 + 2`. -/
theorem selectedResolution_euler (block : Fin degree)
    (hBlock : (data.vertexPartition wall).Rel anchor.1 block) :
    (selectedResolution data star anchor).newEdge.blockCountWithin
        (data.vertexPartition wall) block + 1 =
      (selectedResolution data star anchor).left.blockCountWithin
          (data.vertexPartition wall) block +
        (selectedResolution data star anchor).right.blockCountWithin
          (data.vertexPartition wall) block := by
  rw [newEdge_blockCountWithin ra block hBlock, left_blockCountWithin ra block hBlock,
    right_blockCountWithin ra block hBlock]

/-- **The split candidate does not change the source genus.**  No receipt
beyond the `SplitAnchor`: the anchor block satisfies the Euler identity
`3 + 1 = 2 + 2` and every other wall block carries the neutral joined star. -/
theorem candidate_sourceGenus :
    genus (cand).datum.sourceGraph = genus data.sourceGraph := by
  apply M11SourceGenus.candidate_sourceGenus_of_blockwise_euler
  intro block _
  by_cases hBlock : (data.vertexPartition wall).Rel anchor.1 block
  · rw [candidate_resolution_of_wall_rel ra block hBlock]
    exact selectedResolution_euler ra block hBlock
  · rw [candidate_resolution_of_not_wall_rel ra block hBlock]
    exact euler_of_isStar (isStar_joinedResolutionAt _) block

end Candidate

/-! ## 3.  The four endpoint vertices and the three new occurrences -/

section Census

variable {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall} (ra : SplitAnchor data star anchor)

local notation "cand" => (validCandidate ra.setup)

/-- The direction partition carried by one side of the new target edge: the
`t_thick` classes over `u`, the `t_thin` classes over `v`. -/
noncomputable def sidePartition (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall) (sideValue : Bool) :
    SheetPartition degree :=
  data.edgePartition (if sideValue then thinEdge data star anchor
    else thickEdge data star anchor)

@[simp] theorem sidePartition_false :
    sidePartition data star anchor false =
      data.edgePartition (thickEdge data star anchor) := rfl

@[simp] theorem sidePartition_true :
    sidePartition data star anchor true =
      data.edgePartition (thinEdge data star anchor) := rfl

theorem sidePartition_refines (sideValue : Bool) :
    (sidePartition data star anchor sideValue).Refines (data.vertexPartition wall) := by
  cases sideValue
  · exact thickEdge_refines_wall data star anchor
  · exact thinEdge_refines_wall data star anchor

/-- Inside the anchor block the candidate's endpoint partition on a side is
literally that side's direction partition. -/
theorem candidate_vertexPartition_rel_iff (sideValue : Bool) {a b : Fin degree}
    (hA : (data.vertexPartition wall).Rel anchor.1 a) :
    ((cand).datum.vertexPartition
        (if sideValue then freshVertex target else oldVertex target wall)).Rel a b ↔
      (sidePartition data star anchor sideValue).Rel a b := by
  have hReprRel : (data.vertexPartition wall).Rel anchor.1
      ((data.vertexPartition wall).repr a) :=
    hA.trans ((data.vertexPartition wall).rel_repr_right a)
  have hSelected := candidate_resolution_of_wall_rel ra _ hReprRel
  cases sideValue
  · show ((cand).datum.vertexPartition (oldVertex target wall)).Rel a b ↔ _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_old_wall]
    refine Iff.trans (SheetPartition.paste_rel_iff (data.vertexPartition wall)
      (fun blk ↦ ((cand).resolution blk).left)
      (fun blk ↦ ((cand).contracts blk).left_refines) a b) ?_
    rw [hSelected, selectedResolution_left]
    exact refineOnBlock_rel_iff (data.vertexPartition wall)
      (data.edgePartition (thickEdge data star anchor)) anchor.1 a b
      (thickEdge_refines_wall data star anchor) hA
  · show ((cand).datum.vertexPartition (freshVertex target)).Rel a b ↔ _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_fresh]
    refine Iff.trans (SheetPartition.paste_rel_iff (data.vertexPartition wall)
      (fun blk ↦ ((cand).resolution blk).right)
      (fun blk ↦ ((cand).contracts blk).right_refines) a b) ?_
    rw [hSelected, selectedResolution_right]
    exact refineOnBlock_rel_iff (data.vertexPartition wall)
      (data.edgePartition (thinEdge data star anchor)) anchor.1 a b
      (thinEdge_refines_wall data star anchor) hA

/-- Inside the anchor block the candidate's new-edge partition is literally the
common refinement of the two direction partitions. -/
theorem newEdge_rel_iff {a b : Fin degree}
    (hA : (data.vertexPartition wall).Rel anchor.1 a) :
    (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
        (cand).contracts).newEdge.Rel a b ↔
      (meet (data.edgePartition (thickEdge data star anchor))
        (data.edgePartition (thinEdge data star anchor))).Rel a b := by
  have hReprRel : (data.vertexPartition wall).Rel anchor.1
      ((data.vertexPartition wall).repr a) :=
    hA.trans ((data.vertexPartition wall).rel_repr_right a)
  have hSelected := candidate_resolution_of_wall_rel ra _ hReprRel
  refine Iff.trans (SheetPartition.paste_rel_iff (data.vertexPartition wall)
    (fun blk ↦ ((cand).resolution blk).newEdge)
    (fun blk ↦ ((cand).resolution blk).edge_refines_left.trans
      ((cand).contracts blk).left_refines) a b) ?_
  rw [hSelected, selectedResolution_newEdge]
  exact refineOnBlock_rel_iff (data.vertexPartition wall)
    (meet (data.edgePartition (thickEdge data star anchor))
      (data.edgePartition (thinEdge data star anchor))) anchor.1 a b
    ((meet_refines_left _ _).trans (thickEdge_refines_wall data star anchor)) hA

/-- The actual outgoing source vertex on one side of the new target edge. -/
noncomputable def endpointVertex (sideValue : Bool) (sheet : Fin degree) :
    (cand).datum.SourceVertex :=
  (cand).datum.sourceEndpoint
    (if sideValue then freshVertex target else oldVertex target wall) sheet

/-- The new occurrence of a sheet over the new target edge. -/
noncomputable def newEdgeAt (sheet : Fin degree) : (cand).datum.SourceEdge :=
  (cand).newSourceEdge sheet

/-- **The bridge** `e_1 = e_alpha ∖ e_delta`, joining `S` to `A_v`. -/
noncomputable def bridgeEdge : (cand).datum.SourceEdge :=
  newEdgeAt ra (occurrenceSheet ra.alphaEdge)

/-- **The piece** `e_delta`, joining `S` to the divalent `P_v`. -/
noncomputable def pieceEdge : (cand).datum.SourceEdge :=
  newEdgeAt ra (occurrenceSheet ra.deltaEdge)

/-- **The pass-through** `e_beta`, joining the divalent `P_u` to `A_v`. -/
noncomputable def passEdge : (cand).datum.SourceEdge :=
  newEdgeAt ra (occurrenceSheet ra.betaEdge)

theorem sourceEnds_newEdgeAt (sheet : Fin degree) :
    (cand).datum.sourceEnds (newEdgeAt ra sheet) =
      (endpointVertex ra false sheet, endpointVertex ra true sheet) :=
  GlobalResolution.sourceEnds_newSourceEdge _ _ _ _ _ sheet

theorem newEdgeAt_incident (sideValue : Bool) (sheet : Fin degree) :
    Incident (cand).datum (newEdgeAt ra sheet) (endpointVertex ra sideValue sheet) := by
  cases sideValue
  · exact Or.inl (congrArg Prod.fst
      (GlobalResolution.sourceEnds_newSourceEdge _ _ _ _ _ sheet))
  · exact Or.inr (congrArg Prod.snd
      (GlobalResolution.sourceEnds_newSourceEdge _ _ _ _ _ sheet))

theorem endpointVertex_eq (sideValue : Bool) {a b : Fin degree}
    (hA : (data.vertexPartition wall).Rel anchor.1 a)
    (hRel : (sidePartition data star anchor sideValue).Rel a b) :
    endpointVertex ra sideValue a = endpointVertex ra sideValue b := by
  apply (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr
  refine ⟨rfl, ?_⟩
  refine Eq.trans ?_ (((cand).datum.vertexPartition
    (if sideValue then freshVertex target else oldVertex target wall)).rel_repr_right b)
  exact (candidate_vertexPartition_rel_iff ra sideValue hA).mpr hRel

theorem newEdgeAt_eq_of_rel {a b : Fin degree}
    (h : (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
      (cand).contracts).newEdge.Rel a b) :
    newEdgeAt ra a = newEdgeAt ra b := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact h

/-- A new occurrence whose block meets the meet-class of a sheet of the anchor
is the new occurrence of that sheet. -/
theorem newEdgeAt_eq_of_meet_rel {t s : Fin degree}
    (hT : (data.vertexPartition wall).Rel anchor.1 t)
    (hRel : (meet (data.edgePartition (thickEdge data star anchor))
        (data.edgePartition (thinEdge data star anchor))).Rel t
      ((LocalResolution.paste (data.vertexPartition wall) (cand).resolution
        (cand).contracts).newEdge.repr s)) :
    newEdgeAt ra s = newEdgeAt ra t := by
  have hEqU : newEdgeAt ra s =
      newEdgeAt ra ((LocalResolution.paste (data.vertexPartition wall)
        (cand).resolution (cand).contracts).newEdge.repr s) := by
    apply newEdgeAt_eq_of_rel
    show (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
      (cand).contracts).newEdge.repr s =
        (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
          (cand).contracts).newEdge.repr
            ((LocalResolution.paste (data.vertexPartition wall) (cand).resolution
              (cand).contracts).newEdge.repr s)
    rw [(LocalResolution.paste (data.vertexPartition wall) (cand).resolution
      (cand).contracts).newEdge.repr_idem]
  rw [hEqU]
  exact (newEdgeAt_eq_of_rel ra ((newEdge_rel_iff ra hT).mpr hRel)).symm

theorem newEdgeAt_ne_oldSourceEdge (s : Fin degree) (old : data.SourceEdge) :
    newEdgeAt ra s ≠ (cand).oldSourceEdge old := by
  intro hEq
  have h := congrArg (fun edge : (cand).datum.SourceEdge ↦ edge.1.1) hEq
  have hNone := (occurrenceEquiv target wall (cand).right).injective h
  cases hNone

/-! ### The two sides of the base tree -/

include ra in
theorem rightAssignment_zero :
    rightAssignment data star anchor (star.edge 0) = false := by
  rw [← ra.thick_eq]
  exact rightAssignment_thick data star anchor

include ra in
theorem rightAssignment_one :
    rightAssignment data star anchor (star.edge 1) = true := by
  rw [← ra.thin_eq]
  exact rightAssignment_of_ne data star anchor
    (NonTrivalentValencyTwoCandidate.Prescribed.thinEdge_ne_thickEdge data star anchor)

/-- A retained old occurrence at the wall meets the endpoint vertex on the side
the base tree assigns to its target occurrence. -/
theorem retainedEdge_incident (edge : target.edges)
    (hAt : edge ∈ GluingDatum.incidentEdges wall) (sideValue : Bool)
    (hSide : rightAssignment data star anchor edge = sideValue) (sheet : Fin degree) :
    Incident (cand).datum ((cand).oldSourceEdge (data.sourceEdge edge sheet))
      (endpointVertex ra sideValue sheet) := by
  cases sideValue
  · exact LimitChainCore.oldSourceEdge_incident_old _ edge hAt hSide sheet
  · exact M11SplitSurvival.oldSourceEdge_incident_fresh _ edge hAt hSide sheet

theorem retained_survivor_survives (hValid : data.Valid) {label : Fin 2}
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor label) :
    ¬ IsDangling (cand).datum ((cand).oldSourceEdge edge.1) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge _ hValid.1 _
    (survivor_not_isDangling hEdge)

theorem retained_survivor_incident (sideValue : Bool) {label : Fin 2}
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor label)
    (hSide : rightAssignment data star anchor (star.edge label) = sideValue)
    {sheet : Fin degree}
    (hWall : (data.vertexPartition wall).Rel anchor.1 sheet)
    (hRel : (sidePartition data star anchor sideValue).Rel sheet (occurrenceSheet edge)) :
    Incident (cand).datum ((cand).oldSourceEdge edge.1)
      (endpointVertex ra sideValue sheet) := by
  rw [← sourceEdge_occurrenceSheet hEdge, endpointVertex_eq ra sideValue hWall hRel]
  exact retainedEdge_incident ra (star.edge label) (star.edge_mem_incidentEdges label)
    sideValue hSide (occurrenceSheet edge)

include ra in
theorem nonDanglingValency_ne_zero_false (hValid : data.Valid)
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor 0) :
    nonDanglingValency (cand).datum
      (endpointVertex ra false (occurrenceSheet edge)) ≠ 0 :=
  ClassInjectivity.nonDanglingValency_ne_zero_of_incident _
    (retained_survivor_survives ra hValid hEdge)
    (retained_survivor_incident ra false hEdge (rightAssignment_zero ra)
      (occurrenceSheet_wall_rel edge) rfl)

include ra in
theorem nonDanglingValency_ne_zero_true (hValid : data.Valid)
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor 1) :
    nonDanglingValency (cand).datum
      (endpointVertex ra true (occurrenceSheet edge)) ≠ 0 :=
  ClassInjectivity.nonDanglingValency_ne_zero_of_incident _
    (retained_survivor_survives ra hValid hEdge)
    (retained_survivor_incident ra true hEdge (rightAssignment_one ra)
      (occurrenceSheet_wall_rel edge) rfl)

/-- A new occurrence both of whose endpoint vertices already carry a retained
survivor is not dangling. -/
theorem newEdgeAt_survives {sheet : Fin degree}
    (hFalse : nonDanglingValency (cand).datum (endpointVertex ra false sheet) ≠ 0)
    (hTrue : nonDanglingValency (cand).datum (endpointVertex ra true sheet) ≠ 0) :
    ¬ IsDangling (cand).datum (newEdgeAt ra sheet) := by
  have hEnds := sourceEnds_newEdgeAt ra sheet
  intro hDangling
  rcases hDangling with hSide | hSide
  · obtain ⟨cut⟩ := hSide
    apply hFalse
    have hFst := congrArg Prod.fst hEnds
    have hZero := DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side
      _ cut cut.left_mem
    rwa [hFst] at hZero
  · obtain ⟨cut⟩ := hSide
    apply hTrue
    have hSnd := congrArg Prod.snd hEnds
    have hZero := DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side
      _ cut cut.left_mem
    rwa [hSnd] at hZero

/-! ### Exhaustion: what can meet an endpoint vertex -/

theorem sidePartition_rel_of_incident (sideValue : Bool) {t : Fin degree}
    (hT : (data.vertexPartition wall).Rel anchor.1 t)
    {e : (cand).datum.SourceEdge}
    (hIncident : Incident (cand).datum e (endpointVertex ra sideValue t)) :
    (sidePartition data star anchor sideValue).Rel t e.1.2 := by
  rw [incident_iff_target_mem_and_rel] at hIncident
  refine (candidate_vertexPartition_rel_iff ra sideValue hT).mp ?_
  exact Eq.trans
    (((cand).datum.vertexPartition
      (if sideValue then freshVertex target else oldVertex target wall)).rel_repr_right t)
    hIncident.2

theorem mem_incidentEdges_endpoint_old (sideValue : Bool) (edge : target.edges) :
    occurrenceEquiv target wall (cand).right (some edge) ∈
        GluingDatum.incidentEdges
          (if sideValue then freshVertex target else oldVertex target wall) ↔
      (edge ∈ GluingDatum.incidentEdges wall ∧
        rightAssignment data star anchor edge = sideValue) := by
  rw [GluingContraction.mem_incidentEdges_iff, occurrenceEquiv_some,
    GluingContraction.mem_incidentEdges_iff]
  cases sideValue
  · exact oldEnds_incident_oldVertex_iff target wall (cand).right edge
  · exact oldEnds_incident_freshVertex_iff target wall (cand).right edge

theorem right_eq_of_incident_old (sideValue : Bool) {t : Fin degree}
    {old : data.SourceEdge}
    (hIncident : Incident (cand).datum ((cand).oldSourceEdge old)
      (endpointVertex ra sideValue t)) :
    old.1.1 ∈ GluingDatum.incidentEdges wall ∧
      rightAssignment data star anchor old.1.1 = sideValue := by
  rw [incident_iff_target_mem_and_rel] at hIncident
  have hTargetMem := hIncident.1
  rw [BalancedGlobal.Candidate.oldSourceEdge_target] at hTargetMem
  exact (mem_incidentEdges_endpoint_old ra sideValue old.1.1).mp hTargetMem

/-- A surviving retained occurrence meeting a `u`-side endpoint vertex is a
`t_thick`-survivor lying in that vertex's class. -/
theorem exists_thickSurvivor_of_incident_false (hValid : data.Valid) {t : Fin degree}
    (hT : (data.vertexPartition wall).Rel anchor.1 t) {old : data.SourceEdge}
    (hSurvives : ¬ IsDangling (cand).datum ((cand).oldSourceEdge old))
    (hIncident : Incident (cand).datum ((cand).oldSourceEdge old)
      (endpointVertex ra false t)) :
    ∃ edge ∈ directionSurvivors data star anchor 0, edge.1 = old ∧
      (data.edgePartition (thickEdge data star anchor)).Rel t (occurrenceSheet edge) := by
  obtain ⟨_, hSide⟩ := right_eq_of_incident_old ra false hIncident
  have hTarget : old.1.1 = star.edge 0 := by
    rw [← ra.thick_eq]
    exact (rightAssignment_eq_false_iff data star anchor old.1.1).mp hSide
  have hRel : (data.edgePartition (thickEdge data star anchor)).Rel t old.1.2 :=
    sidePartition_rel_of_incident ra false hT hIncident
  have hWallRel : (data.vertexPartition wall).Rel anchor.1 old.1.2 :=
    hT.trans ((thickEdge_refines_wall data star anchor).rel hRel)
  have hOldSurv : ¬ IsDangling data old := fun h ↦ hSurvives
    ((ResolutionPruning.isDangling_oldSourceEdge_iff (cand) hValid
      (candidate_sourceGenus ra) old).mpr h)
  obtain ⟨edge, hEdge, hVal⟩ := exists_directionSurvivor_eq 0 old hTarget hWallRel hOldSurv
  refine ⟨edge, hEdge, hVal, ?_⟩
  show (data.edgePartition (thickEdge data star anchor)).Rel t edge.1.1.2
  rw [hVal]
  exact hRel

/-- A surviving retained occurrence meeting a `v`-side endpoint vertex is a
`t_thin`-survivor lying in that vertex's class. -/
theorem exists_thinSurvivor_of_incident_true (hValid : data.Valid) {t : Fin degree}
    (hT : (data.vertexPartition wall).Rel anchor.1 t) {old : data.SourceEdge}
    (hSurvives : ¬ IsDangling (cand).datum ((cand).oldSourceEdge old))
    (hIncident : Incident (cand).datum ((cand).oldSourceEdge old)
      (endpointVertex ra true t)) :
    ∃ edge ∈ directionSurvivors data star anchor 1, edge.1 = old ∧
      (data.edgePartition (thinEdge data star anchor)).Rel t (occurrenceSheet edge) := by
  obtain ⟨hAt, hSide⟩ := right_eq_of_incident_old ra true hIncident
  have hTarget : old.1.1 = star.edge 1 := by
    rw [← ra.thin_eq]
    classical
    rw [incidentEdges_eq_pair data star anchor, Finset.mem_insert,
      Finset.mem_singleton] at hAt
    rcases hAt with hThick | hThin
    · rw [hThick, rightAssignment_thick data star anchor] at hSide
      exact absurd hSide (by simp)
    · exact hThin
  have hRel : (data.edgePartition (thinEdge data star anchor)).Rel t old.1.2 :=
    sidePartition_rel_of_incident ra true hT hIncident
  have hWallRel : (data.vertexPartition wall).Rel anchor.1 old.1.2 :=
    hT.trans ((thinEdge_refines_wall data star anchor).rel hRel)
  have hOldSurv : ¬ IsDangling data old := fun h ↦ hSurvives
    ((ResolutionPruning.isDangling_oldSourceEdge_iff (cand) hValid
      (candidate_sourceGenus ra) old).mpr h)
  obtain ⟨edge, hEdge, hVal⟩ := exists_directionSurvivor_eq 1 old hTarget hWallRel hOldSurv
  refine ⟨edge, hEdge, hVal, ?_⟩
  show (data.edgePartition (thinEdge data star anchor)).Rel t edge.1.1.2
  rw [hVal]
  exact hRel

include ra in
/-- Configuration A: the two `t_thick`-survivors are `e_alpha` and `e_beta`. -/
theorem thick_survivor_cases
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor 0) :
    edge = ra.alphaEdge ∨ edge = ra.betaEdge := by
  classical
  rw [NonTrivalentValencyTwoGauge.directionSurvivors_eq_pair (ra.split 0) ra.alpha_mem
    ra.beta_mem ra.alpha_ne_beta, Finset.mem_insert, Finset.mem_singleton] at hEdge
  exact hEdge

include ra in
/-- Configuration A: the two `t_thin`-survivors are `e_delta` and `e_epsilon`. -/
theorem thin_survivor_cases
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor 1) :
    edge = ra.deltaEdge ∨ edge = ra.epsilonEdge := by
  classical
  rw [NonTrivalentValencyTwoGauge.directionSurvivors_eq_pair (ra.split 1) ra.delta_mem
    ra.epsilon_mem ra.delta_ne_epsilon, Finset.mem_insert, Finset.mem_singleton] at hEdge
  exact hEdge

theorem newEdgeAt_ne_of_not_meet {a b : Fin degree}
    (hA : (data.vertexPartition wall).Rel anchor.1 a)
    (hNot : ¬(meet (data.edgePartition (thickEdge data star anchor))
      (data.edgePartition (thinEdge data star anchor))).Rel a b) :
    newEdgeAt ra a ≠ newEdgeAt ra b := by
  intro hEq
  exact hNot ((newEdge_rel_iff ra hA).mp
    (congrArg (fun e : (cand).datum.SourceEdge ↦ e.1.2) hEq))

/-! ### Survival of the three new occurrences -/

include ra in
theorem endpointVertex_true_alpha :
    endpointVertex ra true (occurrenceSheet ra.alphaEdge) =
      endpointVertex ra true (occurrenceSheet ra.epsilonEdge) :=
  endpointVertex_eq ra true (occurrenceSheet_wall_rel ra.alphaEdge) ra.thin_rel_alpha_epsilon

include ra in
theorem endpointVertex_true_beta :
    endpointVertex ra true (occurrenceSheet ra.betaEdge) =
      endpointVertex ra true (occurrenceSheet ra.epsilonEdge) := by
  refine endpointVertex_eq ra true (occurrenceSheet_wall_rel ra.betaEdge) ?_
  exact ra.thin_rel_alpha_beta.symm.trans ra.thin_rel_alpha_epsilon

include ra in
theorem endpointVertex_false_delta :
    endpointVertex ra false (occurrenceSheet ra.deltaEdge) =
      endpointVertex ra false (occurrenceSheet ra.alphaEdge) := by
  refine endpointVertex_eq ra false (occurrenceSheet_wall_rel ra.deltaEdge) ?_
  exact ra.thick_rel_alpha_delta.symm

include ra in
theorem bridgeEdge_survives (hValid : data.Valid) :
    ¬ IsDangling (cand).datum (bridgeEdge ra) := by
  refine newEdgeAt_survives ra (nonDanglingValency_ne_zero_false ra hValid ra.alpha_mem) ?_
  rw [endpointVertex_true_alpha ra]
  exact nonDanglingValency_ne_zero_true ra hValid ra.epsilon_mem

include ra in
theorem pieceEdge_survives (hValid : data.Valid) :
    ¬ IsDangling (cand).datum (pieceEdge ra) := by
  refine newEdgeAt_survives ra ?_ (nonDanglingValency_ne_zero_true ra hValid ra.delta_mem)
  rw [endpointVertex_false_delta ra]
  exact nonDanglingValency_ne_zero_false ra hValid ra.alpha_mem

include ra in
theorem passEdge_survives (hValid : data.Valid) :
    ¬ IsDangling (cand).datum (passEdge ra) := by
  refine newEdgeAt_survives ra (nonDanglingValency_ne_zero_false ra hValid ra.beta_mem) ?_
  rw [endpointVertex_true_beta ra]
  exact nonDanglingValency_ne_zero_true ra hValid ra.epsilon_mem

/-! ## 4.  The four surviving stars, and the census `3, 2, 3, 2` -/

include ra in
/-- **The star at `S = e_alpha` over `u`**: its own old occurrence, the piece
and the bridge. -/
theorem nonDanglingIncident_endpointVertex_alpha (hValid : data.Valid) :
    nonDanglingIncident (cand).datum
        (endpointVertex ra false (occurrenceSheet ra.alphaEdge)) =
      {bridgeEdge ra, pieceEdge ra, (cand).oldSourceEdge ra.alphaEdge.1} := by
  classical
  refine Finset.Subset.antisymm ?_ ?_
  · intro e he
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp he
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases ResolutionPruning.sourceEdge_cases (cand) e with ⟨old, rfl⟩ | ⟨s, rfl⟩
    · obtain ⟨edge, hEdge, hVal, hRel⟩ := exists_thickSurvivor_of_incident_false ra
        hValid (occurrenceSheet_wall_rel ra.alphaEdge) hSurvives hIncident
      rcases thick_survivor_cases ra hEdge with rfl | rfl
      · exact Or.inr (Or.inr (by rw [← hVal]))
      · exact absurd hRel ra.not_thick_rel_alpha_beta
    · have hRel : (data.edgePartition (thickEdge data star anchor)).Rel
          (occurrenceSheet ra.alphaEdge)
          ((LocalResolution.paste (data.vertexPartition wall) (cand).resolution
            (cand).contracts).newEdge.repr s) :=
        sidePartition_rel_of_incident ra false
          (occurrenceSheet_wall_rel ra.alphaEdge) hIncident
      have hWallR : (data.vertexPartition wall).Rel anchor.1
          ((LocalResolution.paste (data.vertexPartition wall) (cand).resolution
            (cand).contracts).newEdge.repr s) :=
        (occurrenceSheet_wall_rel ra.alphaEdge).trans
          ((thickEdge_refines_wall data star anchor).rel hRel)
      rcases ra.setup.cover _ hWallR with hCase | hCase
      · exact Or.inr (Or.inl (newEdgeAt_eq_of_meet_rel ra
          (occurrenceSheet_wall_rel ra.deltaEdge)
          ((meet_rel_iff _ _ _ _).mpr ⟨ra.thick_rel_alpha_delta.symm.trans hRel, hCase⟩)))
      · exact Or.inl (newEdgeAt_eq_of_meet_rel ra (occurrenceSheet_wall_rel ra.alphaEdge)
          ((meet_rel_iff _ _ _ _).mpr ⟨hRel, hCase⟩))
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨bridgeEdge_survives ra hValid, newEdgeAt_incident ra false _⟩
    · refine (mem_nonDanglingIncident _ _ _).mpr ⟨pieceEdge_survives ra hValid, ?_⟩
      rw [← endpointVertex_false_delta ra]
      exact newEdgeAt_incident ra false _
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨retained_survivor_survives ra hValid ra.alpha_mem,
          retained_survivor_incident ra false ra.alpha_mem (rightAssignment_zero ra)
            (occurrenceSheet_wall_rel ra.alphaEdge) rfl⟩

include ra in
/-- **`S` is trivalent.** -/
theorem nonDanglingValency_endpointVertex_alpha (hValid : data.Valid) :
    nonDanglingValency (cand).datum
      (endpointVertex ra false (occurrenceSheet ra.alphaEdge)) = 3 := by
  classical
  rw [← card_nonDanglingIncident, nonDanglingIncident_endpointVertex_alpha ra hValid]
  refine Finset.card_eq_three.mpr ⟨_, _, _, ?_, ?_, ?_, rfl⟩
  · exact newEdgeAt_ne_of_not_meet ra (occurrenceSheet_wall_rel ra.alphaEdge)
      (fun h ↦ ra.setup.not_thin ((meet_rel_iff _ _ _ _).mp h).2)
  · exact newEdgeAt_ne_oldSourceEdge ra _ _
  · exact newEdgeAt_ne_oldSourceEdge ra _ _

include ra in
/-- **The star at the pass-through `P_u = e_beta` over `u`**: its own old
occurrence and the pass-through new occurrence, nothing else. -/
theorem nonDanglingIncident_endpointVertex_beta (hValid : data.Valid) :
    nonDanglingIncident (cand).datum
        (endpointVertex ra false (occurrenceSheet ra.betaEdge)) =
      {passEdge ra, (cand).oldSourceEdge ra.betaEdge.1} := by
  classical
  refine Finset.Subset.antisymm ?_ ?_
  · intro e he
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp he
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases ResolutionPruning.sourceEdge_cases (cand) e with ⟨old, rfl⟩ | ⟨s, rfl⟩
    · obtain ⟨edge, hEdge, hVal, hRel⟩ := exists_thickSurvivor_of_incident_false ra
        hValid (occurrenceSheet_wall_rel ra.betaEdge) hSurvives hIncident
      rcases thick_survivor_cases ra hEdge with rfl | rfl
      · exact absurd hRel.symm ra.not_thick_rel_alpha_beta
      · exact Or.inr (by rw [← hVal])
    · have hRel : (data.edgePartition (thickEdge data star anchor)).Rel
          (occurrenceSheet ra.betaEdge)
          ((LocalResolution.paste (data.vertexPartition wall) (cand).resolution
            (cand).contracts).newEdge.repr s) :=
        sidePartition_rel_of_incident ra false
          (occurrenceSheet_wall_rel ra.betaEdge) hIncident
      have hWallR : (data.vertexPartition wall).Rel anchor.1
          ((LocalResolution.paste (data.vertexPartition wall) (cand).resolution
            (cand).contracts).newEdge.repr s) :=
        (occurrenceSheet_wall_rel ra.betaEdge).trans
          ((thickEdge_refines_wall data star anchor).rel hRel)
      rcases ra.setup.cover _ hWallR with hCase | hCase
      · exfalso
        refine ra.not_thick_rel_alpha_beta ?_
        have hInside : (data.edgePartition (thickEdge data star anchor)).Rel
            (occurrenceSheet ra.alphaEdge) _ :=
          ((data.edgePartition (thickEdge data star anchor)).mem_block_iff _ _).mp
            (ra.setup.sub
              (((data.edgePartition (thinEdge data star anchor)).mem_block_iff _ _).mpr hCase))
        exact hInside.trans hRel.symm
      · exact Or.inl (newEdgeAt_eq_of_meet_rel ra (occurrenceSheet_wall_rel ra.betaEdge)
          ((meet_rel_iff _ _ _ _).mpr ⟨hRel, ra.thin_rel_alpha_beta.symm.trans hCase⟩))
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨passEdge_survives ra hValid, newEdgeAt_incident ra false _⟩
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨retained_survivor_survives ra hValid ra.beta_mem,
          retained_survivor_incident ra false ra.beta_mem (rightAssignment_zero ra)
            (occurrenceSheet_wall_rel ra.betaEdge) rfl⟩

include ra in
/-- **`P_u` is divalent** -- the paper's pass-through point above `u`. -/
theorem nonDanglingValency_endpointVertex_beta (hValid : data.Valid) :
    nonDanglingValency (cand).datum
      (endpointVertex ra false (occurrenceSheet ra.betaEdge)) = 2 := by
  classical
  rw [← card_nonDanglingIncident, nonDanglingIncident_endpointVertex_beta ra hValid,
    Finset.card_insert_of_notMem (by
      simp only [Finset.mem_singleton]
      exact newEdgeAt_ne_oldSourceEdge ra _ _), Finset.card_singleton]

include ra in
/-- **The star at `A_v = e_epsilon` over `v`**: its own old occurrence, the
bridge and the pass-through. -/
theorem nonDanglingIncident_endpointVertex_epsilon (hValid : data.Valid) :
    nonDanglingIncident (cand).datum
        (endpointVertex ra true (occurrenceSheet ra.epsilonEdge)) =
      {bridgeEdge ra, passEdge ra, (cand).oldSourceEdge ra.epsilonEdge.1} := by
  classical
  refine Finset.Subset.antisymm ?_ ?_
  · intro e he
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp he
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases ResolutionPruning.sourceEdge_cases (cand) e with ⟨old, rfl⟩ | ⟨s, rfl⟩
    · obtain ⟨edge, hEdge, hVal, hRel⟩ := exists_thinSurvivor_of_incident_true ra
        hValid (occurrenceSheet_wall_rel ra.epsilonEdge) hSurvives hIncident
      rcases thin_survivor_cases ra hEdge with rfl | rfl
      · exact absurd hRel.symm ra.not_thin_rel_delta_epsilon
      · exact Or.inr (Or.inr (by rw [← hVal]))
    · have hRel : (data.edgePartition (thinEdge data star anchor)).Rel
          (occurrenceSheet ra.epsilonEdge)
          ((LocalResolution.paste (data.vertexPartition wall) (cand).resolution
            (cand).contracts).newEdge.repr s) :=
        sidePartition_rel_of_incident ra true
          (occurrenceSheet_wall_rel ra.epsilonEdge) hIncident
      have hWallR : (data.vertexPartition wall).Rel anchor.1
          ((LocalResolution.paste (data.vertexPartition wall) (cand).resolution
            (cand).contracts).newEdge.repr s) :=
        (occurrenceSheet_wall_rel ra.epsilonEdge).trans
          ((thinEdge_refines_wall data star anchor).rel hRel)
      have hThinAlpha := ra.thin_rel_alpha_epsilon.trans hRel
      rcases ra.thick_cover hWallR with hCase | hCase
      · exact Or.inl (newEdgeAt_eq_of_meet_rel ra (occurrenceSheet_wall_rel ra.alphaEdge)
          ((meet_rel_iff _ _ _ _).mpr ⟨hCase, hThinAlpha⟩))
      · exact Or.inr (Or.inl (newEdgeAt_eq_of_meet_rel ra
          (occurrenceSheet_wall_rel ra.betaEdge)
          ((meet_rel_iff _ _ _ _).mpr
            ⟨hCase, ra.thin_rel_alpha_beta.symm.trans hThinAlpha⟩)))
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · refine (mem_nonDanglingIncident _ _ _).mpr ⟨bridgeEdge_survives ra hValid, ?_⟩
      rw [← endpointVertex_true_alpha ra]
      exact newEdgeAt_incident ra true _
    · refine (mem_nonDanglingIncident _ _ _).mpr ⟨passEdge_survives ra hValid, ?_⟩
      rw [← endpointVertex_true_beta ra]
      exact newEdgeAt_incident ra true _
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨retained_survivor_survives ra hValid ra.epsilon_mem,
          retained_survivor_incident ra true ra.epsilon_mem (rightAssignment_one ra)
            (occurrenceSheet_wall_rel ra.epsilonEdge) rfl⟩

include ra in
/-- **`A_v` is trivalent.** -/
theorem nonDanglingValency_endpointVertex_epsilon (hValid : data.Valid) :
    nonDanglingValency (cand).datum
      (endpointVertex ra true (occurrenceSheet ra.epsilonEdge)) = 3 := by
  classical
  rw [← card_nonDanglingIncident, nonDanglingIncident_endpointVertex_epsilon ra hValid]
  refine Finset.card_eq_three.mpr ⟨_, _, _, ?_, ?_, ?_, rfl⟩
  · exact newEdgeAt_ne_of_not_meet ra (occurrenceSheet_wall_rel ra.alphaEdge)
      (fun h ↦ ra.not_thick_rel_alpha_beta ((meet_rel_iff _ _ _ _).mp h).1)
  · exact newEdgeAt_ne_oldSourceEdge ra _ _
  · exact newEdgeAt_ne_oldSourceEdge ra _ _

include ra in
/-- **The star at the pass-through `P_v = e_delta` over `v`**: its own old
occurrence and the piece, nothing else. -/
theorem nonDanglingIncident_endpointVertex_delta (hValid : data.Valid) :
    nonDanglingIncident (cand).datum
        (endpointVertex ra true (occurrenceSheet ra.deltaEdge)) =
      {pieceEdge ra, (cand).oldSourceEdge ra.deltaEdge.1} := by
  classical
  refine Finset.Subset.antisymm ?_ ?_
  · intro e he
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp he
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases ResolutionPruning.sourceEdge_cases (cand) e with ⟨old, rfl⟩ | ⟨s, rfl⟩
    · obtain ⟨edge, hEdge, hVal, hRel⟩ := exists_thinSurvivor_of_incident_true ra
        hValid (occurrenceSheet_wall_rel ra.deltaEdge) hSurvives hIncident
      rcases thin_survivor_cases ra hEdge with rfl | rfl
      · exact Or.inr (by rw [← hVal])
      · exact absurd hRel ra.not_thin_rel_delta_epsilon
    · have hRel : (data.edgePartition (thinEdge data star anchor)).Rel
          (occurrenceSheet ra.deltaEdge)
          ((LocalResolution.paste (data.vertexPartition wall) (cand).resolution
            (cand).contracts).newEdge.repr s) :=
        sidePartition_rel_of_incident ra true
          (occurrenceSheet_wall_rel ra.deltaEdge) hIncident
      refine Or.inl (newEdgeAt_eq_of_meet_rel ra (occurrenceSheet_wall_rel ra.deltaEdge)
        ((meet_rel_iff _ _ _ _).mpr ⟨?_, hRel⟩))
      have hInside : (data.edgePartition (thickEdge data star anchor)).Rel
          (occurrenceSheet ra.alphaEdge) _ :=
        ((data.edgePartition (thickEdge data star anchor)).mem_block_iff _ _).mp
          (ra.setup.sub
            (((data.edgePartition (thinEdge data star anchor)).mem_block_iff _ _).mpr hRel))
      exact ra.thick_rel_alpha_delta.symm.trans hInside
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨pieceEdge_survives ra hValid, newEdgeAt_incident ra true _⟩
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨retained_survivor_survives ra hValid ra.delta_mem,
          retained_survivor_incident ra true ra.delta_mem (rightAssignment_one ra)
            (occurrenceSheet_wall_rel ra.deltaEdge) rfl⟩

include ra in
/-- **`P_v` is divalent** -- the paper's pass-through point above `v`. -/
theorem nonDanglingValency_endpointVertex_delta (hValid : data.Valid) :
    nonDanglingValency (cand).datum
      (endpointVertex ra true (occurrenceSheet ra.deltaEdge)) = 2 := by
  classical
  rw [← card_nonDanglingIncident, nonDanglingIncident_endpointVertex_delta ra hValid,
    Finset.card_insert_of_notMem (by
      simp only [Finset.mem_singleton]
      exact newEdgeAt_ne_oldSourceEdge ra _ _), Finset.card_singleton]

/-! ## 5.  Exact endpoint sizes -/

include ra in
/-- **The exact outgoing endpoint sizes**: over `u` the two vertices are the
`t_thick`-classes (`|S| = k_alpha`, `|P_u| = k_beta`), over `v` the two vertices
are the `t_thin`-classes (`|A_v| = k_epsilon`, `|P_v| = k_delta`). -/
theorem endpointVertex_blockCard (sideValue : Bool) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel anchor.1 sheet) :
    ((cand).datum.vertexPartition
        (if sideValue then freshVertex target else oldVertex target wall)).blockCard sheet =
      (sidePartition data star anchor sideValue).blockCard sheet := by
  unfold SheetPartition.blockCard
  congr 1
  ext j
  rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
  exact candidate_vertexPartition_rel_iff ra sideValue hSheet

include ra in
/-- The four endpoint sizes in the paper's indices. -/
theorem endpointVertex_blockCard_index (hSplitZero :
      (directionSurvivors data star anchor 0).card = 2) :
    ((cand).datum.vertexPartition (oldVertex target wall)).blockCard
          (occurrenceSheet ra.alphaEdge) = data.sourceEdgeIndex ra.alphaEdge.1 ∧
      ((cand).datum.vertexPartition (oldVertex target wall)).blockCard
          (occurrenceSheet ra.betaEdge) = data.sourceEdgeIndex ra.betaEdge.1 ∧
        ((cand).datum.vertexPartition (freshVertex target)).blockCard
            (occurrenceSheet ra.deltaEdge) = data.sourceEdgeIndex ra.deltaEdge.1 ∧
          ((cand).datum.vertexPartition (freshVertex target)).blockCard
              (occurrenceSheet ra.epsilonEdge) = data.sourceEdgeIndex ra.epsilonEdge.1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show ((cand).datum.vertexPartition (oldVertex target wall)) =
      ((cand).datum.vertexPartition
        (if false then freshVertex target else oldVertex target wall)) from rfl,
      endpointVertex_blockCard ra false (occurrenceSheet_wall_rel ra.alphaEdge),
      sidePartition_false, sourceEdgeIndex_eq_blockCard ra.alpha_mem,
      thickEdge_eq_zero hSplitZero]
  · rw [show ((cand).datum.vertexPartition (oldVertex target wall)) =
      ((cand).datum.vertexPartition
        (if false then freshVertex target else oldVertex target wall)) from rfl,
      endpointVertex_blockCard ra false (occurrenceSheet_wall_rel ra.betaEdge),
      sidePartition_false, sourceEdgeIndex_eq_blockCard ra.beta_mem,
      thickEdge_eq_zero hSplitZero]
  · rw [show ((cand).datum.vertexPartition (freshVertex target)) =
      ((cand).datum.vertexPartition
        (if true then freshVertex target else oldVertex target wall)) from rfl,
      endpointVertex_blockCard ra true (occurrenceSheet_wall_rel ra.deltaEdge),
      sidePartition_true, sourceEdgeIndex_eq_blockCard ra.delta_mem,
      thinEdge_eq_one hSplitZero]
  · rw [show ((cand).datum.vertexPartition (freshVertex target)) =
      ((cand).datum.vertexPartition
        (if true then freshVertex target else oldVertex target wall)) from rfl,
      endpointVertex_blockCard ra true (occurrenceSheet_wall_rel ra.epsilonEdge),
      sidePartition_true, sourceEdgeIndex_eq_blockCard ra.epsilon_mem,
      thinEdge_eq_one hSplitZero]

/-! ## 6.  One new row: the bridge; the piece and the pass-through descend -/

include ra in
/-- **The bridge is alone in its stable class**: both of its ends are
trivalent, and a stable path continues only through a divalent surviving
vertex.  So the split really adds exactly one new stable row, realizing the
cross pairing `{h_alpha, h_delta}` at `S` and `{h_beta, h_epsilon}` at
`A_v`. -/
theorem bridgeEdge_isolated (hValid : data.Valid)
    (other : NonDanglingEdge (cand).datum)
    (hPath : other.stablePath =
      NonDanglingEdge.stablePath ⟨bridgeEdge ra, bridgeEdge_survives ra hValid⟩) :
    other.1 = bridgeEdge ra := by
  have hEnds : (cand).datum.sourceEnds (bridgeEdge ra) =
      (endpointVertex ra false (occurrenceSheet ra.alphaEdge),
        endpointVertex ra true (occurrenceSheet ra.alphaEdge)) :=
    sourceEnds_newEdgeAt ra (occurrenceSheet ra.alphaEdge)
  refine congrArg Subtype.val
    (NonTrivalentUniqueFourValent.eq_of_stablePath_eq_of_ends_ne_two _ ?_ ?_ other hPath)
  · show nonDanglingValency (cand).datum ((cand).datum.sourceEnds (bridgeEdge ra)).1 ≠ 2
    rw [congrArg Prod.fst hEnds, nonDanglingValency_endpointVertex_alpha ra hValid]
    omega
  · show nonDanglingValency (cand).datum ((cand).datum.sourceEnds (bridgeEdge ra)).2 ≠ 2
    rw [congrArg Prod.snd hEnds, endpointVertex_true_alpha ra,
      nonDanglingValency_endpointVertex_epsilon ra hValid]
    omega

include ra in
/-- **The piece carries no new row**: it is consecutive with `e_delta`'s
retained occurrence at the divalent `P_v`, so it lies on `e_delta`'s retained
stable row.  This is
`NonTrivalentValencyThreeSimpleRows.newSourceEdge_stablePath_eq_retained` at the
first of the split's two divalent new vertices. -/
theorem pieceEdge_stablePath_eq_retained (hValid : data.Valid) :
    NonDanglingEdge.stablePath
        (⟨pieceEdge ra, pieceEdge_survives ra hValid⟩ :
          NonDanglingEdge (cand).datum) =
      NonDanglingEdge.stablePath
        (⟨(cand).oldSourceEdge ra.deltaEdge.1,
          retained_survivor_survives ra hValid ra.delta_mem⟩ :
          NonDanglingEdge (cand).datum) := by
  refine stablePath_eq_of_consecutive
    ⟨?_, endpointVertex ra true (occurrenceSheet ra.deltaEdge), ?_, ?_, ?_⟩
  · intro hEq
    exact newEdgeAt_ne_oldSourceEdge ra (occurrenceSheet ra.deltaEdge) ra.deltaEdge.1
      (congrArg Subtype.val hEq)
  · exact newEdgeAt_incident ra true _
  · exact retained_survivor_incident ra true ra.delta_mem (rightAssignment_one ra)
      (occurrenceSheet_wall_rel ra.deltaEdge) rfl
  · exact nonDanglingValency_endpointVertex_delta ra hValid

include ra in
/-- **The pass-through carries no new row** either: it is consecutive with
`e_beta`'s retained occurrence at the divalent `P_u`.  This is the second of the
split's two divalent new vertices. -/
theorem passEdge_stablePath_eq_retained (hValid : data.Valid) :
    NonDanglingEdge.stablePath
        (⟨passEdge ra, passEdge_survives ra hValid⟩ :
          NonDanglingEdge (cand).datum) =
      NonDanglingEdge.stablePath
        (⟨(cand).oldSourceEdge ra.betaEdge.1,
          retained_survivor_survives ra hValid ra.beta_mem⟩ :
          NonDanglingEdge (cand).datum) := by
  refine stablePath_eq_of_consecutive
    ⟨?_, endpointVertex ra false (occurrenceSheet ra.betaEdge), ?_, ?_, ?_⟩
  · intro hEq
    exact newEdgeAt_ne_oldSourceEdge ra (occurrenceSheet ra.betaEdge) ra.betaEdge.1
      (congrArg Subtype.val hEq)
  · exact newEdgeAt_incident ra false _
  · exact retained_survivor_incident ra false ra.beta_mem (rightAssignment_zero ra)
      (occurrenceSheet_wall_rel ra.betaEdge) rfl
  · exact nonDanglingValency_endpointVertex_beta ra hValid

/-! ## 7.  The retained-row descent -/

include ra in
/-- The anchor really has surviving valency four: `2 + 2` over the two
directions. -/
theorem nonDanglingValency_anchor :
    nonDanglingValency data (WallBlock.sourceVertex data wall anchor) = 4 := by
  classical
  have hSum := sum_card_directionSurvivors data star anchor
  rw [card_survivors, Fin.sum_univ_two, ra.split 0, ra.split 1] at hSum
  omega

/-- The remaining geometric input for the retained-row descent: at every wall
block *other than the anchor*, two surviving occurrences meeting at a divalent
quotient-source vertex still lie on one stable path of the candidate.  This is
`NonTrivalentValencyTwoRows.OrdinaryBlockDescent` verbatim; off the anchor the
split candidate installs the same neutral joined resolution, so its proof
`NonTrivalentValencyTwoDescent.ordinaryBlockDescent` ports unchanged. -/
def OrdinaryBlockDescent (hValid : data.Valid) : Prop :=
  ∀ (first second : NonDanglingEdge data) (vertex : data.SourceVertex),
    vertex.1.1 = wall →
    ¬ (data.vertexPartition wall).Rel anchor.1 vertex.1.2 →
    first ≠ second →
    Incident data first.1 vertex → Incident data second.1 vertex →
    nonDanglingValency data vertex = 2 →
    (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 first).stablePath =
      (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 second).stablePath

include ra in
theorem stablePath_retained_eq_of_consecutive (hValid : data.Valid)
    (hDescent : OrdinaryBlockDescent ra hValid)
    {first second : NonDanglingEdge data}
    (h : Consecutive data first second) :
    (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 first).stablePath =
      (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 second).stablePath := by
  obtain ⟨hNe, vertex, hFirst, hSecond, hValency⟩ := h
  by_cases hAt : vertex.1.1 = wall
  · by_cases hAnchorRel : (data.vertexPartition wall).Rel anchor.1 vertex.1.2
    · exfalso
      have hVertex : WallBlock.sourceVertex data wall anchor = vertex :=
        (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hAt.symm, hAnchorRel⟩
      rw [← hVertex, nonDanglingValency_anchor ra] at hValency
      omega
    · exact hDescent first second vertex hAt hAnchorRel hNe hFirst hSecond hValency
  · exact stablePath_eq_of_consecutive
      (ResolutionAwayFromWall.consecutive_retained_of_away (cand) hValid
        (candidate_sourceGenus ra) first second hNe vertex hAt hFirst hSecond hValency)

/-- **The retained-row map.**  Every stable row of the incoming wall datum
descends to a stable row of the outgoing split candidate along the literal
retained occurrences. -/
noncomputable def retainedRow (hValid : data.Valid)
    (hDescent : OrdinaryBlockDescent ra hValid) :
    StablePath data → StablePath (cand).datum :=
  Quot.lift
    (fun e ↦ (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 e).stablePath)
    (fun _ _ h ↦ stablePath_retained_eq_of_consecutive ra hValid hDescent h)

@[simp] theorem retainedRow_mk (hValid : data.Valid)
    (hDescent : OrdinaryBlockDescent ra hValid) (e : NonDanglingEdge data) :
    retainedRow ra hValid hDescent e.stablePath =
      (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 e).stablePath := rfl

/-! ## 8.  The packaged census -/

include ra in
/-- **The split candidate's row package.**  The source genus is preserved, the
anchor really has surviving valency four, the two non-pass-through endpoint
classes `S` and `A_v` are trivalent, the two pass-through classes `P_u` and
`P_v` are divalent, and the bridge is alone in its stable class. -/
theorem census_of_splitAnchor (hValid : data.Valid) :
    genus (cand).datum.sourceGraph = genus data.sourceGraph ∧
      nonDanglingValency data (WallBlock.sourceVertex data wall anchor) = 4 ∧
        nonDanglingValency (cand).datum
            (endpointVertex ra false (occurrenceSheet ra.alphaEdge)) = 3 ∧
          nonDanglingValency (cand).datum
              (endpointVertex ra true (occurrenceSheet ra.epsilonEdge)) = 3 ∧
            nonDanglingValency (cand).datum
                (endpointVertex ra false (occurrenceSheet ra.betaEdge)) = 2 ∧
              nonDanglingValency (cand).datum
                  (endpointVertex ra true (occurrenceSheet ra.deltaEdge)) = 2 ∧
                ∀ other : NonDanglingEdge (cand).datum,
                  other.stablePath =
                      NonDanglingEdge.stablePath
                        ⟨bridgeEdge ra, bridgeEdge_survives ra hValid⟩ →
                    other.1 = bridgeEdge ra :=
  ⟨candidate_sourceGenus ra, nonDanglingValency_anchor ra,
    nonDanglingValency_endpointVertex_alpha ra hValid,
    nonDanglingValency_endpointVertex_epsilon ra hValid,
    nonDanglingValency_endpointVertex_beta ra hValid,
    nonDanglingValency_endpointVertex_delta ra hValid,
    bridgeEdge_isolated ra hValid⟩

end Census

/-! ## 9.  The ordinary-block census and the unconditional retained row

Off the anchor the split candidate installs the *neutral* joined resolution of
`NonTrivalentValencyTwoCandidate`, exactly as the merge candidate does, so the
ordinary-block argument of `NonTrivalentValencyTwoDescent` applies verbatim: an
ordinary wall block `B` is not split, its vertices over `u` and `v` are both
the whole of `B`, joined by one new occurrence, and two survivors at a divalent
`B` either
sit on one side (and the new occurrence is dangling, so they are consecutive
there) or one on each side (and the new occurrence survives and carries the row
across). -/

section Descent

variable {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall} (ra : SplitAnchor data star anchor)

local notation "cand" => (validCandidate ra.setup)

theorem not_rel_repr {a : Fin degree}
    (hA : ¬ (data.vertexPartition wall).Rel anchor.1 a) :
    ¬ (data.vertexPartition wall).Rel anchor.1 ((data.vertexPartition wall).repr a) :=
  fun h ↦ hA (h.trans ((data.vertexPartition wall).rel_repr_right a).symm)

/-- Over an ordinary wall block the candidate's endpoint partitions are the
*unchanged* wall partition, on both sides of the new target edge. -/
theorem candidate_vertexPartition_rel_ordinary (sideValue : Bool) {a b : Fin degree}
    (hA : ¬ (data.vertexPartition wall).Rel anchor.1 a) :
    ((cand).datum.vertexPartition
        (if sideValue then freshVertex target else oldVertex target wall)).Rel a b ↔
      (data.vertexPartition wall).Rel a b := by
  have hJoined := candidate_resolution_of_not_wall_rel ra
    ((data.vertexPartition wall).repr a) (not_rel_repr hA)
  cases sideValue
  · show ((cand).datum.vertexPartition (oldVertex target wall)).Rel a b ↔ _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_old_wall]
    refine Iff.trans (SheetPartition.paste_rel_iff (data.vertexPartition wall)
      (fun blk ↦ ((cand).resolution blk).left)
      (fun blk ↦ ((cand).contracts blk).left_refines) a b) ?_
    rw [hJoined]
    rfl
  · show ((cand).datum.vertexPartition (freshVertex target)).Rel a b ↔ _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_fresh]
    refine Iff.trans (SheetPartition.paste_rel_iff (data.vertexPartition wall)
      (fun blk ↦ ((cand).resolution blk).right)
      (fun blk ↦ ((cand).contracts blk).right_refines) a b) ?_
    rw [hJoined]
    rfl

/-- The same for the new-edge partition: an ordinary block is not split. -/
theorem newEdge_rel_ordinary {a b : Fin degree}
    (hA : ¬ (data.vertexPartition wall).Rel anchor.1 a) :
    (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
        (cand).contracts).newEdge.Rel a b ↔
      (data.vertexPartition wall).Rel a b := by
  have hJoined := candidate_resolution_of_not_wall_rel ra
    ((data.vertexPartition wall).repr a) (not_rel_repr hA)
  refine Iff.trans (SheetPartition.paste_rel_iff (data.vertexPartition wall)
    (fun blk ↦ ((cand).resolution blk).newEdge)
    (fun blk ↦ ((cand).resolution blk).edge_refines_left.trans
      ((cand).contracts blk).left_refines) a b) ?_
  rw [hJoined]
  rfl

theorem incident_sourceEndpoint_wall_iff (x : Fin degree) (old : data.SourceEdge) :
    Incident data old (data.sourceEndpoint wall x) ↔
      (old.1.1 ∈ GluingDatum.incidentEdges wall ∧
        (data.vertexPartition wall).Rel x old.1.2) := by
  constructor
  · intro hIncident
    obtain ⟨hMem, hRel⟩ := (incident_iff_target_mem_and_rel _ _ _).mp hIncident
    exact ⟨hMem, Eq.trans ((data.vertexPartition wall).rel_repr_right x) hRel⟩
  · rintro ⟨hMem, hRel⟩
    exact (incident_iff_target_mem_and_rel _ _ _).mpr
      ⟨hMem, Eq.trans ((data.vertexPartition wall).rel_repr_right x).symm hRel⟩

theorem incident_endpointVertex_iff (sideValue : Bool) (x : Fin degree)
    (e : (cand).datum.SourceEdge) :
    Incident (cand).datum e (endpointVertex ra sideValue x) ↔
      (e.1.1 ∈ GluingDatum.incidentEdges
          (if sideValue then freshVertex target else oldVertex target wall) ∧
        ((cand).datum.vertexPartition
          (if sideValue then freshVertex target else oldVertex target wall)).Rel x e.1.2) := by
  constructor
  · intro hIncident
    obtain ⟨hMem, hRel⟩ := (incident_iff_target_mem_and_rel _ _ _).mp hIncident
    exact ⟨hMem, Eq.trans (((cand).datum.vertexPartition
      (if sideValue then freshVertex target else oldVertex target wall)).rel_repr_right x) hRel⟩
  · rintro ⟨hMem, hRel⟩
    refine (incident_iff_target_mem_and_rel _ _ _).mpr ⟨hMem, ?_⟩
    exact Eq.trans (((cand).datum.vertexPartition
      (if sideValue then freshVertex target else oldVertex target wall)).rel_repr_right x).symm
      hRel

/-- **Retained occurrences at an ordinary block.** -/
theorem incident_oldSourceEdge_endpointVertex_iff (sideValue : Bool) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) (old : data.SourceEdge) :
    Incident (cand).datum ((cand).oldSourceEdge old) (endpointVertex ra sideValue x) ↔
      (Incident data old (data.sourceEndpoint wall x) ∧
        rightAssignment data star anchor old.1.1 = sideValue) := by
  rw [incident_endpointVertex_iff, BalancedGlobal.Candidate.oldSourceEdge_target,
    mem_incidentEdges_endpoint_old, BalancedGlobal.Candidate.oldSourceEdge_sheet,
    candidate_vertexPartition_rel_ordinary ra sideValue hX,
    incident_sourceEndpoint_wall_iff]
  tauto

theorem newEdge_refines_wall :
    (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
      (cand).contracts).newEdge.Refines (data.vertexPartition wall) :=
  (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
    (cand).contracts).edge_refines_left.trans
      (LocalResolution.pasteLeft_refines (data.vertexPartition wall) (cand).resolution
        (cand).contracts)

/-- **New occurrences at an ordinary block.**  The block is not split, so the
only new occurrence meeting either endpoint vertex over it is its own. -/
theorem newEdgeAt_eq_of_incident_ordinary (sideValue : Bool) {x y : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hIncident : Incident (cand).datum (newEdgeAt ra y) (endpointVertex ra sideValue x)) :
    newEdgeAt ra y = newEdgeAt ra x := by
  have hRel := ((incident_endpointVertex_iff ra sideValue x _).mp hIncident).2
  rw [candidate_vertexPartition_rel_ordinary ra sideValue hX] at hRel
  have hSheet : (newEdgeAt ra y).1.2 =
      (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
        (cand).contracts).newEdge.repr y := rfl
  rw [hSheet] at hRel
  have hBack : (data.vertexPartition wall).Rel
      ((LocalResolution.paste (data.vertexPartition wall) (cand).resolution
        (cand).contracts).newEdge.repr y) y :=
    (newEdge_refines_wall ra).rel
      ((LocalResolution.paste (data.vertexPartition wall) (cand).resolution
        (cand).contracts).newEdge.rel_repr_left y)
  exact (newEdgeAt_eq_of_rel ra ((newEdge_rel_ordinary ra hX).mpr (hRel.trans hBack))).symm

/-- The wall datum's surviving occurrences at one ordinary block, on one side
of the outgoing base tree. -/
noncomputable def ordinaryStar (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (x : Fin degree) (sideValue : Bool) : Finset data.SourceEdge := by
  classical
  exact (nonDanglingIncident data (data.sourceEndpoint wall x)).filter
    (fun old ↦ rightAssignment data star anchor old.1.1 = sideValue)

theorem mem_ordinaryStar {x : Fin degree} {sideValue : Bool} (old : data.SourceEdge) :
    old ∈ ordinaryStar data star anchor x sideValue ↔
      ((¬ IsDangling data old ∧ Incident data old (data.sourceEndpoint wall x)) ∧
        rightAssignment data star anchor old.1.1 = sideValue) := by
  classical
  rw [ordinaryStar, Finset.mem_filter, mem_nonDanglingIncident]

theorem ordinaryStar_disjoint (x : Fin degree) :
    Disjoint (ordinaryStar data star anchor x false)
      (ordinaryStar data star anchor x true) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro old hFalse hTrue
  rw [mem_ordinaryStar] at hFalse hTrue
  rw [hFalse.2] at hTrue
  exact Bool.false_ne_true hTrue.2

theorem ordinaryStar_union (x : Fin degree) :
    ordinaryStar data star anchor x false ∪ ordinaryStar data star anchor x true =
      nonDanglingIncident data (data.sourceEndpoint wall x) := by
  classical
  ext old
  rw [Finset.mem_union, mem_ordinaryStar, mem_ordinaryStar, mem_nonDanglingIncident]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h
    cases rightAssignment data star anchor old.1.1
    · exact Or.inl ⟨h, rfl⟩
    · exact Or.inr ⟨h, rfl⟩

/-- **The two sides partition the block's surviving star.** -/
theorem card_ordinaryStar_add (x : Fin degree) :
    (ordinaryStar data star anchor x false).card +
        (ordinaryStar data star anchor x true).card =
      nonDanglingValency data (data.sourceEndpoint wall x) := by
  classical
  rw [← Finset.card_union_of_disjoint
      (ordinaryStar_disjoint (star := star) (anchor := anchor) x),
    ordinaryStar_union, card_nonDanglingIncident]

/-- **The ordinary-block census.** -/
theorem mem_nonDanglingIncident_endpointVertex_ordinary (hValid : data.Valid)
    (sideValue : Bool) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (e : (cand).datum.SourceEdge) :
    e ∈ nonDanglingIncident (cand).datum (endpointVertex ra sideValue x) ↔
      ((∃ old ∈ ordinaryStar data star anchor x sideValue, e = (cand).oldSourceEdge old) ∨
        (e = newEdgeAt ra x ∧ ¬ IsDangling (cand).datum (newEdgeAt ra x))) := by
  classical
  constructor
  · intro hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases ResolutionPruning.sourceEdge_cases (cand) e with ⟨old, rfl⟩ | ⟨y, rfl⟩
    · refine Or.inl ⟨old, ?_, rfl⟩
      rw [mem_ordinaryStar]
      refine ⟨⟨fun h ↦ hSurvives ((ResolutionPruning.isDangling_oldSourceEdge_iff (cand)
        hValid (candidate_sourceGenus ra) old).mpr h), ?_⟩, ?_⟩
      · exact ((incident_oldSourceEdge_endpointVertex_iff ra sideValue hX old).mp
          hIncident).1
      · exact ((incident_oldSourceEdge_endpointVertex_iff ra sideValue hX old).mp
          hIncident).2
    · have hEq := newEdgeAt_eq_of_incident_ordinary ra sideValue hX hIncident
      exact Or.inr ⟨hEq, hEq ▸ hSurvives⟩
  · rintro (⟨old, hOld, rfl⟩ | ⟨rfl, hSurvives⟩)
    · rw [mem_ordinaryStar] at hOld
      refine (mem_nonDanglingIncident _ _ _).mpr
        ⟨ResolutionSurvival.not_isDangling_oldSourceEdge (cand) hValid.1 old hOld.1.1, ?_⟩
      exact (incident_oldSourceEdge_endpointVertex_iff ra sideValue hX old).mpr
        ⟨hOld.1.2, hOld.2⟩
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨hSurvives, newEdgeAt_incident ra sideValue x⟩

theorem nonDanglingIncident_endpointVertex_of_new_dangling (hValid : data.Valid)
    (sideValue : Bool) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hDangling : IsDangling (cand).datum (newEdgeAt ra x)) :
    nonDanglingIncident (cand).datum (endpointVertex ra sideValue x) =
      (ordinaryStar data star anchor x sideValue).image (cand).oldSourceEdge := by
  classical
  ext e
  rw [mem_nonDanglingIncident_endpointVertex_ordinary ra hValid sideValue hX,
    Finset.mem_image]
  constructor
  · rintro (⟨old, hOld, rfl⟩ | ⟨-, hSurvives⟩)
    · exact ⟨old, hOld, rfl⟩
    · exact absurd hDangling hSurvives
  · rintro ⟨old, hOld, rfl⟩
    exact Or.inl ⟨old, hOld, rfl⟩

theorem nonDanglingIncident_endpointVertex_of_new_survives (hValid : data.Valid)
    (sideValue : Bool) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hSurvives : ¬ IsDangling (cand).datum (newEdgeAt ra x)) :
    nonDanglingIncident (cand).datum (endpointVertex ra sideValue x) =
      insert (newEdgeAt ra x)
        ((ordinaryStar data star anchor x sideValue).image (cand).oldSourceEdge) := by
  classical
  ext e
  rw [mem_nonDanglingIncident_endpointVertex_ordinary ra hValid sideValue hX,
    Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (⟨old, hOld, rfl⟩ | ⟨rfl, -⟩)
    · exact Or.inr ⟨old, hOld, rfl⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨old, hOld, rfl⟩)
    · exact Or.inr ⟨rfl, hSurvives⟩
    · exact Or.inl ⟨old, hOld, rfl⟩

theorem newEdgeAt_notMem_image (sideValue : Bool) (x : Fin degree) :
    newEdgeAt ra x ∉
      (ordinaryStar data star anchor x sideValue).image (cand).oldSourceEdge := by
  classical
  intro hMem
  obtain ⟨old, -, hEq⟩ := Finset.mem_image.mp hMem
  exact newEdgeAt_ne_oldSourceEdge ra x old hEq.symm

/-- `nd(B_s) = |star_s(B)|` when the block's new occurrence is dangling. -/
theorem nonDanglingValency_endpointVertex_of_new_dangling (hValid : data.Valid)
    (sideValue : Bool) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hDangling : IsDangling (cand).datum (newEdgeAt ra x)) :
    nonDanglingValency (cand).datum (endpointVertex ra sideValue x) =
      (ordinaryStar data star anchor x sideValue).card := by
  classical
  rw [← card_nonDanglingIncident,
    nonDanglingIncident_endpointVertex_of_new_dangling ra hValid sideValue hX hDangling,
    Finset.card_image_of_injective _ (ResolutionCut.oldSourceEdge_injective (cand))]

/-- `nd(B_s) = |star_s(B)| + 1` when the block's new occurrence survives. -/
theorem nonDanglingValency_endpointVertex_of_new_survives (hValid : data.Valid)
    (sideValue : Bool) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hSurvives : ¬ IsDangling (cand).datum (newEdgeAt ra x)) :
    nonDanglingValency (cand).datum (endpointVertex ra sideValue x) =
      (ordinaryStar data star anchor x sideValue).card + 1 := by
  classical
  rw [← card_nonDanglingIncident,
    nonDanglingIncident_endpointVertex_of_new_survives ra hValid sideValue hX hSurvives,
    Finset.card_insert_of_notMem (newEdgeAt_notMem_image ra sideValue x),
    Finset.card_image_of_injective _ (ResolutionCut.oldSourceEdge_injective (cand))]

theorem nonDanglingValency_candidate_ne_one (hValid : data.Valid)
    (vertex : (cand).datum.SourceVertex) :
    nonDanglingValency (cand).datum vertex ≠ 1 :=
  NonDanglingValency.nonDanglingValency_ne_one (cand).datum
    (validCandidate_datum_valid ra.setup hValid).1 vertex

/-- **A block whose star is empty on one side has a dangling new
occurrence.** -/
theorem newEdgeAt_isDangling_of_ordinaryStar_empty (hValid : data.Valid)
    (sideValue : Bool) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hEmpty : (ordinaryStar data star anchor x sideValue).card = 0) :
    IsDangling (cand).datum (newEdgeAt ra x) := by
  classical
  by_contra hSurvives
  refine nonDanglingValency_candidate_ne_one ra hValid (endpointVertex ra sideValue x) ?_
  rw [nonDanglingValency_endpointVertex_of_new_survives ra hValid sideValue hX hSurvives,
    hEmpty]

/-- **A surviving new occurrence forces a survivor on each side.** -/
theorem ordinaryStar_card_ne_zero_of_new_survives (hValid : data.Valid)
    (sideValue : Bool) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hSurvives : ¬ IsDangling (cand).datum (newEdgeAt ra x)) :
    (ordinaryStar data star anchor x sideValue).card ≠ 0 := by
  intro hEmpty
  exact hSurvives
    (newEdgeAt_isDangling_of_ordinaryStar_empty ra hValid sideValue hX hEmpty)

/-- **The new occurrence of an ordinary block survives exactly when both sides
carry a surviving retained occurrence.** -/
theorem newEdgeAt_survives_iff_ordinary (hValid : data.Valid) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) :
    ¬ IsDangling (cand).datum (newEdgeAt ra x) ↔
      ((ordinaryStar data star anchor x false).card ≠ 0 ∧
        (ordinaryStar data star anchor x true).card ≠ 0) := by
  classical
  constructor
  · intro hSurvives
    exact ⟨ordinaryStar_card_ne_zero_of_new_survives ra hValid false hX hSurvives,
      ordinaryStar_card_ne_zero_of_new_survives ra hValid true hX hSurvives⟩
  · rintro ⟨hFalse, hTrue⟩
    intro hDangling
    have hEnds := sourceEnds_newEdgeAt ra x
    have hNonZero : ∀ sideValue : Bool,
        nonDanglingValency (cand).datum (endpointVertex ra sideValue x) ≠ 0 := by
      intro sideValue
      rw [nonDanglingValency_endpointVertex_of_new_dangling ra hValid sideValue hX
        hDangling]
      cases sideValue
      · exact hFalse
      · exact hTrue
    rcases hDangling with hSide | hSide
    · obtain ⟨cut⟩ := hSide
      refine hNonZero false ?_
      have hFst := congrArg Prod.fst hEnds
      have hZero := DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side
        _ cut cut.left_mem
      rwa [hFst] at hZero
    · obtain ⟨cut⟩ := hSide
      refine hNonZero true ?_
      have hSnd := congrArg Prod.snd hEnds
      have hZero := DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side
        _ cut cut.left_mem
      rwa [hSnd] at hZero

theorem incident_retainedEdge_endpointVertex (hValid : data.Valid) (sideValue : Bool)
    {x : Fin degree} (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    {old : NonDanglingEdge data}
    (hOld : old.1 ∈ ordinaryStar data star anchor x sideValue) :
    Incident (cand).datum (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old).1
      (endpointVertex ra sideValue x) := by
  rw [mem_ordinaryStar] at hOld
  exact (incident_oldSourceEdge_endpointVertex_iff ra sideValue hX old.1).mpr
    ⟨hOld.1.2, hOld.2⟩

theorem stablePath_retainedEdge_eq_newEdgeAt (hValid : data.Valid) (sideValue : Bool)
    {x : Fin degree} (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    {old : NonDanglingEdge data}
    (hOld : old.1 ∈ ordinaryStar data star anchor x sideValue)
    (hCard : (ordinaryStar data star anchor x sideValue).card = 1)
    (hSurvives : ¬ IsDangling (cand).datum (newEdgeAt ra x)) :
    (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old).stablePath =
      NonDanglingEdge.stablePath
        (⟨newEdgeAt ra x, hSurvives⟩ : NonDanglingEdge (cand).datum) := by
  refine stablePath_eq_of_consecutive ⟨?_, endpointVertex ra sideValue x, ?_, ?_, ?_⟩
  · intro hEq
    exact newEdgeAt_ne_oldSourceEdge ra x old.1 (congrArg Subtype.val hEq).symm
  · exact incident_retainedEdge_endpointVertex ra hValid sideValue hX hOld
  · exact newEdgeAt_incident ra sideValue x
  · rw [nonDanglingValency_endpointVertex_of_new_survives ra hValid sideValue hX
      hSurvives, hCard]

theorem stablePath_retainedEdge_eq_of_same_side (hValid : data.Valid) (sideValue : Bool)
    {x : Fin degree} (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    {first second : NonDanglingEdge data} (hNe : first ≠ second)
    (hFirst : first.1 ∈ ordinaryStar data star anchor x sideValue)
    (hSecond : second.1 ∈ ordinaryStar data star anchor x sideValue)
    (hCard : (ordinaryStar data star anchor x sideValue).card = 2)
    (hDangling : IsDangling (cand).datum (newEdgeAt ra x)) :
    (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 first).stablePath =
      (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 second).stablePath := by
  refine stablePath_eq_of_consecutive ⟨?_, endpointVertex ra sideValue x, ?_, ?_, ?_⟩
  · exact fun hEq ↦ hNe (ResolutionAwayFromWall.retainedEdge_injective (cand) hValid.1 hEq)
  · exact incident_retainedEdge_endpointVertex ra hValid sideValue hX hFirst
  · exact incident_retainedEdge_endpointVertex ra hValid sideValue hX hSecond
  · rw [nonDanglingValency_endpointVertex_of_new_dangling ra hValid sideValue hX
      hDangling, hCard]

/-- **The ordinary-block descent, discharged.**  `OrdinaryBlockDescent` holds
for every wall datum and every split anchor; no ordinary-block valency bound
and no further receipt is needed. -/
theorem ordinaryBlockDescent (hValid : data.Valid) : OrdinaryBlockDescent ra hValid := by
  classical
  intro first second vertex hAt hX hNe hFirst hSecond hValency
  set x := vertex.1.2 with hx
  have hVertex : data.sourceEndpoint wall x = vertex :=
    (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hAt.symm, rfl⟩
  have hFirst' : Incident data first.1 (data.sourceEndpoint wall x) := by
    rw [hVertex]; exact hFirst
  have hSecond' : Incident data second.1 (data.sourceEndpoint wall x) := by
    rw [hVertex]; exact hSecond
  have hValNew : nonDanglingValency data (data.sourceEndpoint wall x) = 2 := by
    rw [hVertex]; exact hValency
  have hNeVal : first.1 ≠ second.1 := fun h ↦ hNe (Subtype.ext h)
  have hPairCard : ({first.1, second.1} : Finset data.SourceEdge).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hNeVal), Finset.card_singleton]
  have hSum := card_ordinaryStar_add (data := data) (star := star) (anchor := anchor) x
  rw [hValNew] at hSum
  have hMemFirst : ∀ sideValue : Bool,
      rightAssignment data star anchor first.1.1.1 = sideValue →
        first.1 ∈ ordinaryStar data star anchor x sideValue := by
    intro sideValue hSide
    exact (mem_ordinaryStar first.1).mpr ⟨⟨first.2, hFirst'⟩, hSide⟩
  have hMemSecond : ∀ sideValue : Bool,
      rightAssignment data star anchor second.1.1.1 = sideValue →
        second.1 ∈ ordinaryStar data star anchor x sideValue := by
    intro sideValue hSide
    exact (mem_ordinaryStar second.1).mpr ⟨⟨second.2, hSecond'⟩, hSide⟩
  by_cases hSame : rightAssignment data star anchor first.1.1.1 =
      rightAssignment data star anchor second.1.1.1
  · have hTwo : ∀ sideValue : Bool,
        first.1 ∈ ordinaryStar data star anchor x sideValue →
        second.1 ∈ ordinaryStar data star anchor x sideValue →
        (ordinaryStar data star anchor x sideValue).card = 2 ∧
          (ordinaryStar data star anchor x (!sideValue)).card = 0 := by
      intro sideValue hF hS
      have hSub : ({first.1, second.1} : Finset data.SourceEdge) ⊆
          ordinaryStar data star anchor x sideValue := by
        intro e he
        rw [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl
        · exact hF
        · exact hS
      have hGe : 2 ≤ (ordinaryStar data star anchor x sideValue).card := by
        rw [← hPairCard]
        exact Finset.card_le_card hSub
      cases sideValue
      · simp only [Bool.not_false]
        omega
      · simp only [Bool.not_true]
        omega
    have hF := hMemFirst _ rfl
    have hS := hMemSecond _ hSame.symm
    obtain ⟨hCardTwo, hCardZero⟩ := hTwo _ hF hS
    exact stablePath_retainedEdge_eq_of_same_side ra hValid _ hX hNe hF hS hCardTwo
      (newEdgeAt_isDangling_of_ordinaryStar_empty ra hValid _ hX hCardZero)
  · have hBoolEq : ∀ a b c : Bool, ¬ (a = b) → ¬ (c = a) → c = b := by decide
    have hNonempty : ∀ sideValue : Bool,
        (ordinaryStar data star anchor x sideValue).Nonempty := by
      intro sideValue
      by_cases hCase : sideValue = rightAssignment data star anchor first.1.1.1
      · rw [hCase]
        exact ⟨first.1, hMemFirst _ rfl⟩
      · rw [hBoolEq _ _ sideValue hSame hCase]
        exact ⟨second.1, hMemSecond _ rfl⟩
    have hCardAll : ∀ sideValue : Bool,
        (ordinaryStar data star anchor x sideValue).card = 1 := by
      have h1 := (hNonempty false).card_pos
      have h2 := (hNonempty true).card_pos
      intro sideValue
      cases sideValue
      · omega
      · omega
    have hSurvives : ¬ IsDangling (cand).datum (newEdgeAt ra x) :=
      (newEdgeAt_survives_iff_ordinary ra hValid hX).mpr
        ⟨by rw [hCardAll false]; omega, by rw [hCardAll true]; omega⟩
    have hFirstRow := stablePath_retainedEdge_eq_newEdgeAt ra hValid _ hX
      (hMemFirst _ rfl) (hCardAll _) hSurvives
    have hSecondRow := stablePath_retainedEdge_eq_newEdgeAt ra hValid _ hX
      (hMemSecond _ rfl) (hCardAll _) hSurvives
    exact hFirstRow.trans hSecondRow.symm

/-- **`retainedRow`, unconditionally.**  Every stable row of the incoming wall
datum descends to a stable row of the outgoing split candidate, with no
remaining geometric receipt beyond the `SplitAnchor` and `data.Valid`. -/
noncomputable def retainedRowFree (hValid : data.Valid) :
    StablePath data → StablePath (cand).datum :=
  retainedRow ra hValid (ordinaryBlockDescent ra hValid)

@[simp] theorem retainedRowFree_mk (hValid : data.Valid) (e : NonDanglingEdge data) :
    retainedRowFree ra hValid e.stablePath =
      (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 e).stablePath := rfl

end Descent

/-! ## 10.  Non-vacuity: the split anchor at the gauged datum -/

section Producer

variable {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall}

open NonTrivalentValencyTwoSplitGauge

/-- **The split anchor, produced.**  Configuration A with four named survivors
and the paper's strict inequality `k_delta < k_alpha` give a `SplitAnchor` at
the gauged wall datum of `NonTrivalentValencyTwoSplitGauge` -- so every
statement of this module is inhabited, and the whole row census lives over the
gauged datum, which is where
`TypeChangeLink.base` sits. -/
noncomputable def splitAnchor_gauged
    (source : TwoBranchAnchor data star anchor)
    (hSplit : ∀ label : Fin 2, (directionSurvivors data star anchor label).card = 2)
    {alphaEdge betaEdge deltaEdge epsilonEdge :
      IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hSourceConnected : data.Connected)
    (hAlpha : alphaEdge ∈ directionSurvivors data star anchor 0)
    (hBeta : betaEdge ∈ directionSurvivors data star anchor 0)
    (hDelta : deltaEdge ∈ directionSurvivors data star anchor 1)
    (hEpsilon : epsilonEdge ∈ directionSurvivors data star anchor 1)
    (hAlphaNe : alphaEdge ≠ betaEdge) (hDeltaNe : deltaEdge ≠ epsilonEdge)
    (hIndex : data.sourceEdgeIndex deltaEdge.1 < data.sourceEdgeIndex alphaEdge.1) :
    SplitAnchor (splitGaugedData data star anchor (occurrenceSheet alphaEdge)
        (occurrenceSheet deltaEdge)) star
      (splitGaugedAnchor data star anchor (occurrenceSheet alphaEdge)
        (occurrenceSheet deltaEdge)) where
  source := splitGaugedSource data star anchor (occurrenceSheet alphaEdge)
    (occurrenceSheet deltaEdge) hSourceConnected source
  split := fun label ↦ split_splitGauged data star anchor (occurrenceSheet alphaEdge)
    (occurrenceSheet deltaEdge) hSourceConnected hSplit label
  alphaEdge := splitSurvivorEquiv data star anchor (occurrenceSheet alphaEdge)
    (occurrenceSheet deltaEdge) alphaEdge
  betaEdge := splitSurvivorEquiv data star anchor (occurrenceSheet alphaEdge)
    (occurrenceSheet deltaEdge) betaEdge
  deltaEdge := splitSurvivorEquiv data star anchor (occurrenceSheet alphaEdge)
    (occurrenceSheet deltaEdge) deltaEdge
  epsilonEdge := splitSurvivorEquiv data star anchor (occurrenceSheet alphaEdge)
    (occurrenceSheet deltaEdge) epsilonEdge
  alpha_mem := mem_directionSurvivors_splitGauged data star anchor _ _ hSourceConnected 0 hAlpha
  beta_mem := mem_directionSurvivors_splitGauged data star anchor _ _ hSourceConnected 0 hBeta
  delta_mem := mem_directionSurvivors_splitGauged data star anchor _ _ hSourceConnected 1 hDelta
  epsilon_mem :=
    mem_directionSurvivors_splitGauged data star anchor _ _ hSourceConnected 1 hEpsilon
  alpha_ne_beta := (splitSurvivorEquiv data star anchor (occurrenceSheet alphaEdge)
    (occurrenceSheet deltaEdge)).injective.ne hAlphaNe
  delta_ne_epsilon := (splitSurvivorEquiv data star anchor (occurrenceSheet alphaEdge)
    (occurrenceSheet deltaEdge)).injective.ne hDeltaNe
  setup := by
    rw [occurrenceSheet_splitSurvivorEquiv_zero data star anchor (occurrenceSheet alphaEdge)
        (occurrenceSheet deltaEdge) hConnected hGenus hAlpha,
      occurrenceSheet_splitSurvivorEquiv_one data star anchor (occurrenceSheet alphaEdge)
        (occurrenceSheet deltaEdge) hDelta]
    exact splitSetup_gauged source hSplit hConnected hGenus hSourceConnected hAlpha hDelta
      hEpsilon hDeltaNe hIndex

end Producer

end Anchor

end DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitRows
