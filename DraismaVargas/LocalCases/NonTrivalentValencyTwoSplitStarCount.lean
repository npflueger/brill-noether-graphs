import DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitTracks
import DraismaVargas.LocalCases.NonTrivalentValencyTwoStarCountAll

/-!
# The valency-two Base II **split** star count, and the split link at an actual wall

Source: Vargas, Part II (arXiv:2609.09109), §5.1 (a combinatorial type change
is a Whitehead move on the *ambient* tracked graph; labelling convention (1))
and §5.4 (case `{v2-nd4-t3}`, Configuration A, base tree `T_2` = Base II, the
**split** members of subcases `{v2-nd4-t3-k2=k3}` and `{v2-nd4-t3-k2<k3}` and
their diagrams), together with Draisma--Vargas Part I, Case `{w2}`, for the
base tree and `lemma-ndval-of-GqA0`.

`NonTrivalentValencyTwoSplitTracks` reduces `OuterWalk.TypeChangeLink` at a
valency-two Base II **split** wall to a **single star count**, `hIncidence`,
against the branch-vertex bijection `vertexEquiv` and the outgoing presentation
`wallOutgoingFD` of `NonTrivalentValencyTwoSplitExit`.  **This module
discharges that star count**, so the split link follows from (H-split)
`PrescribedSplitMove`, the wall data and the incoming two-valent star alone.
It is the split analogue of `NonTrivalentValencyTwoBaseOneStarCount` (Base I)
and of `NonTrivalentValencyTwoStarCount` and
`NonTrivalentValencyTwoStarCountAll` (the merge member); everywhere
`NonTrivalentValencyTwoStarCount` carries
`StablePathFacetContraction.NoContractedReturn`, the input is taken from the
no-return-free `NonTrivalentValencyTwoStarCountAll.injective_incomingRow`
instead, so **no no-return receipt of any kind appears**.

## What is different from Base I and from the merge member

The split anchor has **four** outgoing vertices, `S = e_alpha` and the
pass-through `P_u = e_beta` over `u`, `A_v = e_epsilon` and the pass-through
`P_v = e_delta` over `v`, of which only `S` and `A_v` are branch vertices.  The
pair the split realizes at `S` is `{h_alpha, h_delta}`, and `e_delta`'s row is
**not** carried at `S` by a retained occurrence: it is carried by the *piece*,
through the divalent `P_v`
(`NonTrivalentValencyTwoSplitTracks.stablePath_pieceEdge_eq_retainedRow`).  So the
anchor match here is between the star `{bridge, piece, e_alpha}` and the moved
star `{m.base, first, second}`, with the piece -- a new occurrence -- playing the
role the second retained cross member plays at Base I.  This is exactly why
(H-split) is stated at row level.

## What is proved

### 1.  (T1) at an ordinary wall block, and at every non-anchor vertex

At a two-valent wall the outgoing base tree subdivides the wall vertex, so an
ordinary wall block `B` is split into two endpoint vertices.
`NonTrivalentValencyTwoSplitTracks` does the valency bookkeeping (`!ordSide`
keeps the whole surviving valency, `ordSide` is at most divalent); here
`card_ordinaryStar_ordSide_le`, `card_ordinaryStar_ordSide_le_one`,
`newEdgeAt_survives_of_mem_ordSide`, `branchEndEdge`, `branchEnd`,
`stablePath_branchEnd`, `incident_branchEnd` and
`incidenceCount_endpointVertex_branchSide_ordinary` transport the
*row-filtered* star, and `incidenceCount_candVertex` combines that with the
off-wall transport.

### 2.  The exact stars at `S` and `A_v`, as surviving occurrences

`anchorND`, `bridgeND`, `directRetained`, `throughND`,
`stablePath_throughND` (the split's characteristic fact: the pass-through member's
row is carried by the piece resp. by the pass-through occurrence),
`incidentEdges_anchorBranchVertex`, `incidentEdges_anchorBranchVertex_ordered`,
`directRetained_ne_throughND`, and
`incidenceCount_bridgeRow_inl_eq_zero` (the bridge is alone in its class and its
two ends are `S` and `A_v`, so the bridge row misses every other branch vertex).

### 3.  (T2), the chart rows, and the two matching tests

`incidenceCount_gauged_eq_incoming` is the gauge leg of
`NonTrivalentValencyTwoSplitTracks` composed with
`NonTrivalentValencyTwoStarCountAll.incidenceCount_wall_eq_incoming`;
`outFD_row_retained` / `outFD_row_bridge` / `outFD_row_split` are the chart rows
of `NonTrivalentValencyTwoSplitExit.wallOutgoingFD`;
`vanishingEnds_of_orientation` and `incidenceCount_facetRow_eq_zero` build
`NonTrivalentValencyTwoStarCountAll.VanishingEnds` from (H-split)'s orientation
clause; `splitGaugeRowEquiv_splitWallEdge`, `stablePath_anchorOcc_iff`,
`label_dart_split_iff` and `label_dart_split_ne_base` are the candidate-side
and dart-side matching tests.

### 4.  The star count

`incidence_inl_retained`, `incidence_inl_bridge` away from the anchor;
`incidence_inr_false_retained`, `incidence_inr_false_bridge` at `S`, matched
against the moved star (H-split) prescribes; `incidence_inr_true` at `A_v` from
the leftover equation (a stable row meets its branch vertices twice in all, a
chart row carries two darts of the moved graph, and the count agrees everywhere
else -- the two divalent pass-through vertices never enter either sum);
`incidence_of_prescribedSplitMove`; and the links
`typeChangeLink_of_prescribedSplitMove` and `typeChangeLink_of_rows`.

### 5.  The headline

`exists_typeChangeLink_of_prescribedSplitMove_of_wallData` and
`exists_typeChangeLink_of_prescribedSplitMove_splitMirror_of_wallData`: from the
wall data and the incoming two-valent star alone, the anchor block with
`nd(A) = 4`, the two anchor ends, and -- for Configuration A, the four named
survivors and the strict index inequality `k_delta < k_alpha` -- the split
candidate's outgoing presentation, the common minor `AgreeOffColumn`, and the
link as soon as (H-split) is supplied.  (H-split) itself is supplied
unconditionally by `NonTrivalentValencyTwoBaseOneLink.splitCrossLink`.  The
mirror is the same theorem at `NonTrivalentValencyTwoSplitExit.relabelStar
wallStar`.

## What is not proved -- the explicit hypotheses

1. `PrescribedSplitMove m wd (occurrenceSheet alphaEdge) (occurrenceSheet
   deltaEdge) ra p q`, i.e. (H-split): the Whitehead move is oriented along the
   vanishing row and the two darts it places with `m.base` carry the *rows* of
   `e_alpha` and `e_delta`.  `NonTrivalentValencyTwoSplitTracks` supplies its
   relative witness `prescribedSplitMove_prescribedMove`, the orientation
   producers `orientation_of_hBase_two` / `orientation_of_hBase_leaf`, and the
   row-level constructor `prescribedSplitMove_of_rows` (which
   `typeChangeLink_of_rows` consumes).  Choosing the move that realizes a
   *prescribed* outgoing type is the move-to-type dispatcher's job, not this
   module's.
2. The dispatch data of the headline: the incoming `W2R1Target.TwoStar`,
   Configuration A, the four named survivors with their memberships and
   distinctness, and the strict index inequality `k_delta < k_alpha` (Part II,
   subcase `{v2-nd4-t3-k2<k3}`: exactly the case in which the Base I member does
   not exist).  Which class splits is what chooses between Types I and II, so
   it cannot be discharged here.
3. Nothing else.  No no-return receipt, no ordinary-block valency bound beyond
   what the wall metric gives (`ordinaryTrivalent_of_wall_metric`), and no
   structure is introduced by this module.

## Consumers

`OuterWalk.TypeChangeLink` at Part II case `{v2-nd4}`, Configuration A, the two
Base II split outgoing types; and the valency-two move-to-type dispatcher,
which feeds `NonTrivalentValencyTwoBaseOneLink.link_all` with no hypothesis.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitStarCount

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.StablePathCount
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate.Prescribed (rightAssignment)
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitGauge
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitRows
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitRowEquiv (ordSide ordSide_eq_true
  ordSide_eq_false bridgeRow rowMap rowEquiv rowEquiv_retainedRow rowEquiv_bridgeRow)
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitRowDictionary (retainedRowFree_injective
  splitGaugeRowEquiv splitRelabelLabelling splitRelabelLabelling_row)
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitTracks
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRowEquiv (OrdinaryTrivalent)
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRows (survivor_not_isDangling)
open DraismaVargas.LocalCases.NonTrivalentValencyTwoTracksLeaf (AnchorEnds leftBranch
  rightBranch)

noncomputable section

/-! ## 1.  (T1) at an ordinary wall block -/

section Ordinary

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

variable {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall} (ra : SplitAnchor data star anchor)
  (hValid : data.Valid) (hOrd : OrdinaryTrivalent data wall anchor)

local notation "cand" => (validCandidate ra.setup)

include hOrd in
/-- A retained row is never the bridge row. -/
theorem retainedRowFree_ne_bridgeRow (r : StablePath data) :
    retainedRowFree ra hValid r ≠ bridgeRow ra hValid := by
  intro hBad
  have h := congrArg (rowEquiv ra hValid hOrd) hBad
  rw [rowEquiv_retainedRow ra hValid hOrd r, rowEquiv_bridgeRow ra hValid hOrd] at h
  exact Option.some_ne_none r h

/-- `ordSide` names the side carrying no more survivors than the other. -/
theorem card_ordinaryStar_ordSide_le (x : Fin degree) :
    (ordinaryStar data star anchor x (ordSide data star anchor x)).card ≤
      (ordinaryStar data star anchor x (!ordSide data star anchor x)).card := by
  classical
  by_cases hLt : (ordinaryStar data star anchor x true).card <
      (ordinaryStar data star anchor x false).card
  · rw [ordSide_eq_true hLt]
    simp only [Bool.not_true]
    omega
  · rw [ordSide_eq_false hLt]
    simp only [Bool.not_false]
    omega

/-- **The `ordSide` side of a trivalent ordinary wall block carries at most one
survivor**: the two sides partition a star of size at most three. -/
theorem card_ordinaryStar_ordSide_le_one {x : Fin degree}
    (hLe : nonDanglingValency data (data.sourceEndpoint wall x) ≤ 3) :
    (ordinaryStar data star anchor x (ordSide data star anchor x)).card ≤ 1 := by
  classical
  have hSum := card_ordinaryStar_add (data := data) (star := star) (anchor := anchor) x
  have hLeSide := card_ordinaryStar_ordSide_le (data := data) (star := star) (anchor := anchor) x
  cases hCase : ordSide data star anchor x with
  | false =>
    rw [hCase] at hLeSide
    simp only [Bool.not_false] at hLeSide
    omega
  | true =>
    rw [hCase] at hLeSide
    simp only [Bool.not_true] at hLeSide
    omega

include hValid in
/-- A survivor on the `ordSide` side forces the block's new occurrence to
survive: the other side then carries one too. -/
theorem newEdgeAt_survives_of_mem_ordSide {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) {old : data.SourceEdge}
    (hOld : old ∈ ordinaryStar data star anchor x (ordSide data star anchor x)) :
    ¬ IsDangling (cand).datum (newEdgeAt ra x) := by
  classical
  have hPos : 0 < (ordinaryStar data star anchor x (ordSide data star anchor x)).card :=
    Finset.card_pos.mpr ⟨old, hOld⟩
  have hLeSide := card_ordinaryStar_ordSide_le (data := data) (star := star) (anchor := anchor) x
  refine (newEdgeAt_survives_iff_ordinary ra hValid hX).mpr ?_
  cases hCase : ordSide data star anchor x with
  | false =>
    rw [hCase] at hPos hLeSide
    simp only [Bool.not_false] at hLeSide
    omega
  | true =>
    rw [hCase] at hPos hLeSide
    simp only [Bool.not_true] at hLeSide
    omega

/-! ### The branch-side representative of a survivor -/

/-- The representative, at the `!ordSide` endpoint of an ordinary wall block, of
a surviving occurrence of that block: the retained copy of the occurrence itself
when the base tree assigns its target to that side, and the block's own new
occurrence when it assigns it to the other one. -/
def branchEndEdge (x : Fin degree) (e : NonDanglingEdge data) : (cand).datum.SourceEdge :=
  if rightAssignment data star anchor e.1.1.1 = !ordSide data star anchor x then
    (cand).oldSourceEdge e.1
  else newEdgeAt ra x

include hValid in
theorem branchEndEdge_survives {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) (e : NonDanglingEdge data)
    (hInc : Incident data e.1 (data.sourceEndpoint wall x)) :
    ¬ IsDangling (cand).datum (branchEndEdge ra x e) := by
  classical
  unfold branchEndEdge
  by_cases hs : rightAssignment data star anchor e.1.1.1 = !ordSide data star anchor x
  · rw [if_pos hs]
    exact ResolutionSurvival.not_isDangling_oldSourceEdge (cand) hValid.1 e.1 e.2
  · rw [if_neg hs]
    have hs' : rightAssignment data star anchor e.1.1.1 = ordSide data star anchor x := by
      revert hs
      cases ordSide data star anchor x <;>
        cases rightAssignment data star anchor e.1.1.1 <;> simp
    exact newEdgeAt_survives_of_mem_ordSide ra hValid hX
      ((mem_ordinaryStar e.1).mpr ⟨⟨e.2, hInc⟩, hs'⟩)

include hValid in
/-- The same representative, as a surviving occurrence of the candidate. -/
def branchEnd {x : Fin degree} (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (e : NonDanglingEdge data) (hInc : Incident data e.1 (data.sourceEndpoint wall x)) :
    NonDanglingEdge (cand).datum :=
  ⟨branchEndEdge ra x e, branchEndEdge_survives ra hValid hX e hInc⟩

theorem stablePath_branchEnd {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hLe : nonDanglingValency data (data.sourceEndpoint wall x) ≤ 3)
    (e : NonDanglingEdge data) (hInc : Incident data e.1 (data.sourceEndpoint wall x)) :
    (branchEnd ra hValid hX e hInc).stablePath = retainedRowFree ra hValid e.stablePath := by
  classical
  rw [retainedRowFree_mk ra hValid e]
  by_cases hs : rightAssignment data star anchor e.1.1.1 = !ordSide data star anchor x
  · refine congrArg NonDanglingEdge.stablePath (Subtype.ext ?_)
    show branchEndEdge ra x e = (cand).oldSourceEdge e.1
    unfold branchEndEdge
    rw [if_pos hs]
  · have hs' : rightAssignment data star anchor e.1.1.1 = ordSide data star anchor x := by
      revert hs
      cases ordSide data star anchor x <;>
        cases rightAssignment data star anchor e.1.1.1 <;> simp
    have hOld : e.1 ∈ ordinaryStar data star anchor x (ordSide data star anchor x) :=
      (mem_ordinaryStar e.1).mpr ⟨⟨e.2, hInc⟩, hs'⟩
    have hSurv := newEdgeAt_survives_of_mem_ordSide ra hValid hX hOld
    have hCard : (ordinaryStar data star anchor x (ordSide data star anchor x)).card = 1 := by
      have hPos : 0 < (ordinaryStar data star anchor x (ordSide data star anchor x)).card :=
        Finset.card_pos.mpr ⟨e.1, hOld⟩
      have hLeOne := card_ordinaryStar_ordSide_le_one (data := data) (star := star)
        (anchor := anchor) (x := x) hLe
      omega
    rw [stablePath_retainedEdge_eq_newEdgeAt ra hValid _ hX hOld hCard hSurv]
    refine congrArg NonDanglingEdge.stablePath (Subtype.ext ?_)
    show branchEndEdge ra x e = newEdgeAt ra x
    unfold branchEndEdge
    rw [if_neg hs]

theorem incident_branchEnd {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) (e : NonDanglingEdge data)
    (hInc : Incident data e.1 (data.sourceEndpoint wall x)) :
    Incident (cand).datum (branchEnd ra hValid hX e hInc).1
      (endpointVertex ra (!ordSide data star anchor x) x) := by
  classical
  by_cases hs : rightAssignment data star anchor e.1.1.1 = !ordSide data star anchor x
  · have hVal : (branchEnd ra hValid hX e hInc).1 = (cand).oldSourceEdge e.1 := by
      show branchEndEdge ra x e = _
      unfold branchEndEdge
      rw [if_pos hs]
    rw [hVal]
    exact (incident_oldSourceEdge_endpointVertex_iff ra _ hX e.1).mpr ⟨hInc, hs⟩
  · have hVal : (branchEnd ra hValid hX e hInc).1 = newEdgeAt ra x := by
      show branchEndEdge ra x e = _
      unfold branchEndEdge
      rw [if_neg hs]
    rw [hVal]
    exact newEdgeAt_incident ra _ x

include hOrd in
/-- **(T1) at an ordinary wall block.**  At a two-valent wall the outgoing base
tree subdivides the wall vertex, so an ordinary wall block `B` is split in two;
the `!ordSide` endpoint keeps the block's whole row-filtered star.  The bijection
sends a survivor whose target lies on that side to its retained copy, and the at
most one survivor on the other side to `B`'s new occurrence, which sits on that
survivor's own retained row. -/
theorem incidenceCount_endpointVertex_branchSide_ordinary {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hLe : nonDanglingValency data (data.sourceEndpoint wall x) ≤ 3)
    (row : StablePath data) :
    incidenceCount data (data.sourceEndpoint wall x) row =
      incidenceCount (cand).datum (endpointVertex ra (!ordSide data star anchor x) x)
        (retainedRowFree ra hValid row) := by
  classical
  unfold incidenceCount
  refine Finset.card_bij (fun e he ↦ branchEnd ra hValid hX e
    ((mem_incidentEdges _ _ _).mp (Finset.mem_filter.mp he).1)) ?_ ?_ ?_
  · intro e he
    obtain ⟨hMem, hRow⟩ := Finset.mem_filter.mp he
    refine Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr
      (incident_branchEnd ra hValid hX e _), ?_⟩
    rw [stablePath_branchEnd ra hValid hX hLe e _, hRow]
  · intro e₁ he₁ e₂ he₂ hEq
    have hInc₁ := (mem_incidentEdges _ _ _).mp (Finset.mem_filter.mp he₁).1
    have hInc₂ := (mem_incidentEdges _ _ _).mp (Finset.mem_filter.mp he₂).1
    have hVal : branchEndEdge ra x e₁ = branchEndEdge ra x e₂ := congrArg Subtype.val hEq
    unfold branchEndEdge at hVal
    by_cases hs₁ : rightAssignment data star anchor e₁.1.1.1 = !ordSide data star anchor x <;>
      by_cases hs₂ : rightAssignment data star anchor e₂.1.1.1 = !ordSide data star anchor x
    · rw [if_pos hs₁, if_pos hs₂] at hVal
      exact Subtype.ext (ResolutionCut.oldSourceEdge_injective (cand) hVal)
    · rw [if_pos hs₁, if_neg hs₂] at hVal
      exact absurd hVal.symm (newEdgeAt_ne_oldSourceEdge ra x e₁.1)
    · rw [if_neg hs₁, if_pos hs₂] at hVal
      exact absurd hVal (newEdgeAt_ne_oldSourceEdge ra x e₂.1)
    · have hs₁' : rightAssignment data star anchor e₁.1.1.1 = ordSide data star anchor x := by
        revert hs₁
        cases ordSide data star anchor x <;>
          cases rightAssignment data star anchor e₁.1.1.1 <;> simp
      have hs₂' : rightAssignment data star anchor e₂.1.1.1 = ordSide data star anchor x := by
        revert hs₂
        cases ordSide data star anchor x <;>
          cases rightAssignment data star anchor e₂.1.1.1 <;> simp
      have hOld₁ : e₁.1 ∈ ordinaryStar data star anchor x (ordSide data star anchor x) :=
        (mem_ordinaryStar e₁.1).mpr ⟨⟨e₁.2, hInc₁⟩, hs₁'⟩
      have hOld₂ : e₂.1 ∈ ordinaryStar data star anchor x (ordSide data star anchor x) :=
        (mem_ordinaryStar e₂.1).mpr ⟨⟨e₂.2, hInc₂⟩, hs₂'⟩
      exact Subtype.ext (Finset.card_le_one.mp
        (card_ordinaryStar_ordSide_le_one (data := data) (star := star) (anchor := anchor)
          (x := x) hLe) e₁.1 hOld₁ e₂.1 hOld₂)
  · intro f hf
    obtain ⟨hMem, hRow⟩ := Finset.mem_filter.mp hf
    have hStar : f.1 ∈ nonDanglingIncident (cand).datum
        (endpointVertex ra (!ordSide data star anchor x) x) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨f.2, (mem_incidentEdges _ _ _).mp hMem⟩
    rcases (mem_nonDanglingIncident_endpointVertex_ordinary ra hValid _ hX f.1).mp hStar with
      ⟨old, hOld, hEq⟩ | ⟨hEq, hSurv⟩
    · obtain ⟨⟨hSurvOld, hIncOld⟩, hSide⟩ := (mem_ordinaryStar old).mp hOld
      have hValEq : branchEndEdge ra x ⟨old, hSurvOld⟩ = f.1 := by
        unfold branchEndEdge
        rw [if_pos hSide]
        exact hEq.symm
      refine ⟨⟨old, hSurvOld⟩, ?_, Subtype.ext hValEq⟩
      refine Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr hIncOld, ?_⟩
      refine retainedRowFree_injective ra hValid hOrd ?_
      rw [← stablePath_branchEnd ra hValid hX hLe ⟨old, hSurvOld⟩ hIncOld]
      exact Eq.trans (congrArg NonDanglingEdge.stablePath (Subtype.ext hValEq)) hRow
    · obtain ⟨hFalse, hTrue⟩ := (newEdgeAt_survives_iff_ordinary ra hValid hX).mp hSurv
      have hNonempty :
          (ordinaryStar data star anchor x (ordSide data star anchor x)).Nonempty := by
        cases hCase : ordSide data star anchor x with
        | false => exact Finset.card_pos.mp (by omega)
        | true => exact Finset.card_pos.mp (by omega)
      obtain ⟨old, hOld⟩ := hNonempty
      obtain ⟨⟨hSurvOld, hIncOld⟩, hSide⟩ := (mem_ordinaryStar old).mp hOld
      have hSideNe : ¬ (rightAssignment data star anchor old.1.1 =
          !ordSide data star anchor x) := by
        rw [hSide]
        cases ordSide data star anchor x <;> simp
      have hValEq : branchEndEdge ra x ⟨old, hSurvOld⟩ = f.1 := by
        unfold branchEndEdge
        rw [if_neg hSideNe]
        exact hEq.symm
      refine ⟨⟨old, hSurvOld⟩, ?_, Subtype.ext hValEq⟩
      refine Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr hIncOld, ?_⟩
      refine retainedRowFree_injective ra hValid hOrd ?_
      rw [← stablePath_branchEnd ra hValid hX hLe ⟨old, hSurvOld⟩ hIncOld]
      exact Eq.trans (congrArg NonDanglingEdge.stablePath (Subtype.ext hValEq)) hRow

include hOrd in
/-- **(T1) at every vertex of the datum other than the anchor.** -/
theorem incidenceCount_candVertex (w : data.SourceVertex)
    (hne : w ≠ WallBlock.sourceVertex data wall anchor) (row : StablePath data) :
    incidenceCount data w row =
      incidenceCount (cand).datum (candVertex ra w) (retainedRowFree ra hValid row) := by
  classical
  by_cases hw : w.1.1 = wall
  · rw [candVertex_wall ra w hw]
    conv_lhs => rw [← sourceEndpoint_self w hw]
    exact incidenceCount_endpointVertex_branchSide_ordinary ra hValid hOrd
      (not_rel_anchor_of_ne w hw hne) (hOrd _ (not_rel_anchor_of_ne w hw hne)) row
  · rw [candVertex_away ra w hw]
    exact incidenceCount_retainedVertex_retainedRow ra hValid hOrd w hw row

end Ordinary

/-! ## 2.  The exact stars at `S` and `A_v`, as surviving occurrences -/

section AnchorStar

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

variable {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall} (ra : SplitAnchor data star anchor)
  (hValid : data.Valid) (hOrd : OrdinaryTrivalent data wall anchor)

local notation "cand" => (validCandidate ra.setup)

/-- The four named survivors of the split anchor, as surviving occurrences of the
datum the candidate is built over.  `which = false` is the `u`-side member of the
pair the split realizes (`e_alpha` at `S`, `e_beta` at `A_v`), `which = true` the
`v`-side one (`e_delta` at `S`, `e_epsilon` at `A_v`). -/
def anchorND (side which : Bool) : NonDanglingEdge data :=
  match side, which with
  | false, false => ⟨ra.alphaEdge.1, survivor_not_isDangling ra.alpha_mem⟩
  | false, true => ⟨ra.deltaEdge.1, survivor_not_isDangling ra.delta_mem⟩
  | true, false => ⟨ra.betaEdge.1, survivor_not_isDangling ra.beta_mem⟩
  | true, true => ⟨ra.epsilonEdge.1, survivor_not_isDangling ra.epsilon_mem⟩

/-- The **bridge** as a surviving occurrence. -/
def bridgeND : NonDanglingEdge (cand).datum :=
  ⟨bridgeEdge ra, bridgeEdge_survives ra hValid⟩

@[simp] theorem stablePath_bridgeND :
    (bridgeND ra hValid).stablePath = bridgeRow ra hValid := rfl

/-- The **direct** member of the pair realized at `S` resp. at `A_v`, retained:
`e_alpha` at `S` (side `false`), `e_epsilon` at `A_v` (side `true`). -/
def directRetained (side : Bool) : NonDanglingEdge (cand).datum :=
  ResolutionAwayFromWall.retainedEdge (cand) hValid.1
    (anchorND ra side (decide (side = true)))

theorem directRetained_false :
    directRetained ra hValid false =
      ResolutionAwayFromWall.retainedEdge (cand) hValid.1 (anchorND ra false false) := rfl

theorem directRetained_true :
    directRetained ra hValid true =
      ResolutionAwayFromWall.retainedEdge (cand) hValid.1 (anchorND ra true true) := rfl

/-- The **pass-through** member of the pair realized at `S` resp. at `A_v`, read
through the new occurrence that carries it: the piece at `S` (whose row is
`e_delta`'s) and the pass-through occurrence at `A_v` (whose row is
`e_beta`'s). -/
def throughND (side : Bool) : NonDanglingEdge (cand).datum :=
  match side with
  | false => ⟨pieceEdge ra, pieceEdge_survives ra hValid⟩
  | true => ⟨passEdge ra, passEdge_survives ra hValid⟩

/-- **The row a pass-through member carries is the retained row of its own
survivor** -- the split's characteristic fact. -/
theorem stablePath_throughND (side : Bool) :
    (throughND ra hValid side).stablePath =
      retainedRowFree ra hValid (anchorND ra side (!(decide (side = true)))).stablePath := by
  cases side
  · exact stablePath_pieceEdge_eq_retainedRow ra hValid
  · exact stablePath_passEdge_eq_retainedRow ra hValid

theorem stablePath_directRetained (side : Bool) :
    (directRetained ra hValid side).stablePath =
      retainedRowFree ra hValid (anchorND ra side (decide (side = true))).stablePath :=
  (retainedRowFree_mk ra hValid _).symm

/-- **The exact star at `S` and at `A_v`, read on surviving occurrences**: the
bridge, the pass-through member's new occurrence, and the direct member's
retained occurrence. -/
theorem incidentEdges_anchorBranchVertex (side : Bool) :
    incidentEdges (cand).datum (anchorBranchVertex ra side) =
      {bridgeND ra hValid, throughND ra hValid side, directRetained ra hValid side} := by
  classical
  have hStar : nonDanglingIncident (cand).datum (anchorBranchVertex ra side) =
      {(bridgeND ra hValid).1, (throughND ra hValid side).1,
        (directRetained ra hValid side).1} := by
    cases side
    · exact nonDanglingIncident_anchorBranchVertex_false ra hValid
    · exact nonDanglingIncident_anchorBranchVertex_true ra hValid
  ext e
  rw [mem_incidentEdges]
  constructor
  · intro hInc
    have h : e.1 ∈ nonDanglingIncident (cand).datum (anchorBranchVertex ra side) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨e.2, hInc⟩
    rw [hStar] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
    rcases h with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  · intro h
    have h2 : e.1 ∈ nonDanglingIncident (cand).datum (anchorBranchVertex ra side) := by
      rw [hStar]
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    exact ((mem_nonDanglingIncident _ _ _).mp h2).2

/-- The star at `S` / `A_v` with the *direct* member listed before the
pass-through one, the order (H-split) names the two darts in. -/
theorem incidentEdges_anchorBranchVertex_ordered (side : Bool) :
    incidentEdges (cand).datum (anchorBranchVertex ra side) =
      {bridgeND ra hValid, directRetained ra hValid side, throughND ra hValid side} := by
  classical
  rw [incidentEdges_anchorBranchVertex ra hValid side, Finset.pair_comm]

/-- The direct member's retained occurrence and the pass-through member's new
occurrence are different occurrences. -/
theorem directRetained_ne_throughND (side : Bool) :
    directRetained ra hValid side ≠ throughND ra hValid side := by
  intro hBad
  have hVal : (directRetained ra hValid side).1 = (throughND ra hValid side).1 :=
    congrArg Subtype.val hBad
  cases side
  · exact newEdgeAt_ne_oldSourceEdge ra (occurrenceSheet ra.deltaEdge)
      (anchorND ra false false).1 hVal.symm
  · exact newEdgeAt_ne_oldSourceEdge ra (occurrenceSheet ra.betaEdge)
      (anchorND ra true true).1 hVal.symm

/-! ### The bridge row misses every branch vertex away from the anchor -/

include hOrd in
/-- A branch vertex of the candidate away from the anchor is neither `S` nor
`A_v`. -/
theorem anchorBranchVertex_ne_candBranchMap_inl (side : Bool)
    (w : {w : BranchVertex data // w.1 ≠ WallBlock.sourceVertex data wall anchor}) :
    anchorBranchVertex ra side ≠ (candBranchMap ra hValid hOrd (Sum.inl w)).1 := by
  intro hBad
  exact Sum.inr_ne_inl (candBranchMap_injective ra hValid hOrd
    (Subtype.ext hBad : candBranchMap ra hValid hOrd (Sum.inr side) =
      candBranchMap ra hValid hOrd (Sum.inl w)))

include hOrd in
/-- **The bridge row does not reach a branch vertex of the candidate away from
the anchor**: the bridge is alone in its stable class (`bridgeEdge_isolated`) and
its two ends are `S` and `A_v`. -/
theorem incidenceCount_bridgeRow_inl_eq_zero
    (w : {w : BranchVertex data // w.1 ≠ WallBlock.sourceVertex data wall anchor}) :
    incidenceCount (cand).datum (candBranchMap ra hValid hOrd (Sum.inl w)).1
      (bridgeRow ra hValid) = 0 := by
  classical
  unfold incidenceCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hRow
  have hInc := (mem_incidentEdges _ _ _).mp he
  have hVal : e.1 = bridgeEdge ra := bridgeEdge_isolated ra hValid e hRow
  have hEnds : (cand).datum.sourceEnds e.1 =
      (endpointVertex ra false (occurrenceSheet ra.alphaEdge),
        endpointVertex ra true (occurrenceSheet ra.alphaEdge)) := by
    rw [hVal]
    exact sourceEnds_newEdgeAt ra (occurrenceSheet ra.alphaEdge)
  rcases hInc with h | h
  · rw [hEnds] at h
    exact anchorBranchVertex_ne_candBranchMap_inl ra hValid hOrd false w h
  · rw [hEnds] at h
    refine anchorBranchVertex_ne_candBranchMap_inl ra hValid hOrd true w ?_
    show endpointVertex ra true (occurrenceSheet ra.epsilonEdge) = _
    rw [← endpointVertex_true_alpha ra]
    exact h

end AnchorStar

/-! ## 3.  The two transports and the chart rows at a wall of the outer walk -/

section Wall

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {deg : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival deg graph label (label m.base)}
  (wd : WallData arrival)
  {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (thickSheet thinSheet : Fin deg)

variable (ra : SplitAnchor
    (splitGaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      thickSheet thinSheet) wallStar
    (splitGaugedAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      thickSheet thinSheet))
  (hGauged : (splitGaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
    anchorBlk thickSheet thinSheet).Valid)
  (hOrdGauged : OrdinaryTrivalent (splitGaugedData (contractDatum wd.cover wd.hc wd.hab
    wd.hOne) wallStar anchorBlk thickSheet thinSheet) ⟨wd.a, wd.hab⟩
    (splitGaugedAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      thickSheet thinSheet))
  (hOrd : OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
    anchorBlk)
  (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)

include src hOrd in
/-- **(T2)**: the gauge leg composed with the wall contraction. -/
theorem incidenceCount_gauged_eq_incoming
    (w₀ : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hne : w₀ ≠ NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk)
    (u : wd.cover.SourceVertex)
    (hMapU : sourceVertexMap wd.cover wd.hc wd.hab wd.hOne u = w₀)
    (hThreeU : 3 ≤ nonDanglingValency wd.cover u)
    (r₀ : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (splitGaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
        anchorBlk thickSheet thinSheet)
        (NonTrivalentValencyTwoSplitExit.splitGaugeVertexEquiv
          (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet
          thinSheet w₀)
        (splitGaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
          thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 r₀) =
      incidenceCount wd.cover u (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
        (wd.hCompat m) (wd.hForest m) r₀) := by
  rw [← incidenceCount_gauge (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
    thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 w₀ r₀]
  exact NonTrivalentValencyTwoStarCountAll.incidenceCount_wall_eq_incoming m wd src hOrd w₀ hne
    u hMapU hThreeU r₀

variable (labelling₀ : StableLengthMatrixLabelling
    (contractDatum wd.cover wd.hc wd.hab wd.hOne)
    {column : coordinate // column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted})
  (hRowVal : ∀ pth : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne),
    (labelling₀.row pth).1 =
      Equiv.swap (label m.base) (wd.fullDim.labelling.targetEdge.symm wd.contracted)
        (wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (WallAdmissibility.danglingCompatible_of_contractionForest wd.cover wd.hc wd.hab
            wd.hOne (wd.hForest m)) (wd.hForest m) pth)))
  (hMatrixWall : ∀ (pth : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (column : {column : coordinate //
      column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted}),
    GluingDatum.LengthMatrixPresentation.matrix labelling₀.presentation
        (labelling₀.row pth) column =
      GluingDatum.LengthMatrixPresentation.matrix wd.fullDim.labelling.presentation
        (wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (WallAdmissibility.danglingCompatible_of_contractionForest wd.cover wd.hc wd.hab
            wd.hOne (wd.hForest m)) (wd.hForest m) pth)) column.1)

/-- A retained row of the outgoing split presentation keeps the chart coordinate
of its own incoming row. -/
theorem outFD_row_retained
    (r₀ : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    (NonTrivalentValencyTwoSplitExit.wallOutgoingFD m wd wallStar anchorBlk thickSheet
        thinSheet labelling₀ ra hGauged hOrdGauged hRowVal hMatrixWall).labelling.row
      (retainedRowFree ra hGauged
        (splitGaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
          thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 r₀)) =
      wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
        (wd.hCompat m) (wd.hForest m) r₀) := by
  show (NonTrivalentValencyTwoExit.rowChart wd.cover wd.fullDim (label m.base)
      (contracted := wd.contracted))
      ((NonTrivalentValencyTwoSplitRowEquiv.labelling ra hGauged hOrdGauged
        (splitRelabelLabelling (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
          anchorBlk thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1
          labelling₀)).row
        (retainedRowFree ra hGauged
          (splitGaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
            thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 r₀))) = _
  have hRelab : (splitRelabelLabelling (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
      anchorBlk thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1
      labelling₀).row
        (splitGaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
          thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 r₀) =
      labelling₀.row r₀ :=
    splitRelabelLabelling_row
      (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet thinSheet
      (NonTrivalentValencyTwoTracks.wallValid m wd).1 labelling₀ r₀
  rw [NonTrivalentValencyTwoSplitRowEquiv.labelling_row_retained ra hGauged hOrdGauged _ _,
    NonTrivalentValencyTwoExit.rowChart_some, hRelab, hRowVal r₀,
    Equiv.swap_comm (label m.base) (wd.fullDim.labelling.targetEdge.symm wd.contracted)]
  exact Equiv.swap_apply_self _ _ _

/-- The bridge row of the outgoing split presentation occupies the vanishing
chart row. -/
theorem outFD_row_bridge :
    (NonTrivalentValencyTwoSplitExit.wallOutgoingFD m wd wallStar anchorBlk thickSheet
        thinSheet labelling₀ ra hGauged hOrdGauged hRowVal hMatrixWall).labelling.row
      (bridgeRow ra hGauged) = label m.base := by
  show (NonTrivalentValencyTwoExit.rowChart wd.cover wd.fullDim (label m.base)
      (contracted := wd.contracted))
      ((NonTrivalentValencyTwoSplitRowEquiv.labelling ra hGauged hOrdGauged
        (splitRelabelLabelling (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
          anchorBlk thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1
          labelling₀)).row (bridgeRow ra hGauged)) = label m.base
  rw [NonTrivalentValencyTwoSplitRowEquiv.labelling_row_bridge ra hGauged hOrdGauged _]
  rfl

/-! ### The pair of vanishing ends, from (H-split)'s orientation -/

variable {p q : wd.cover.SourceVertex}

/-- `NonTrivalentValencyTwoStarCountAll.VanishingEnds` from
`NonTrivalentValencyTwoTracksLeaf.AnchorEnds` together with (H-split)'s
orientation clause. -/
def vanishingEnds_of_orientation (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hRight : (IncomingPairing.opBaseDart m wd).1.1 = q) :
    NonTrivalentValencyTwoStarCountAll.VanishingEnds m wd anchorBlk where
  left := p
  right := q
  ends := hEnds
  leftMeets := by
    refine (incidenceCount_pos_iff wd.cover _ _).mpr
      ⟨(IncomingPairing.baseDart m wd).2.1, ?_, stablePath_baseDart m wd⟩
    rw [← hLeft]
    exact (IncomingPairing.baseDart m wd).2.2
  rightMeets := by
    refine (incidenceCount_pos_iff wd.cover _ _).mpr
      ⟨(IncomingPairing.opBaseDart m wd).2.1, ?_, stablePath_opBaseDart m wd⟩
    rw [← hRight]
    exact (IncomingPairing.opBaseDart m wd).2.2

/-- **The vanishing row meets no branch vertex of the incoming cover other than
the two anchor ends.** -/
theorem incidenceCount_facetRow_eq_zero (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hRight : (IncomingPairing.opBaseDart m wd).1.1 = q)
    (u : BranchVertex wd.cover) (hl : u.1 ≠ p) (hr : u.1 ≠ q) :
    incidenceCount wd.cover u.1 (NonTrivalentValencyTwoTracks.facetRow m wd) = 0 :=
  NonTrivalentValencyTwoStarCountAll.incidenceCount_facetRow_eq_zero m wd
    (vanishingEnds_of_orientation m wd hEnds hLeft hRight) u hl hr

/-! ### The pair realized at `S`, across the gauge -/

/-- **The gauge carries the row of a paired survivor to its own row.** -/
theorem splitGaugeRowEquiv_splitWallEdge (which : Bool) :
    splitGaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1
        (splitWallEdge m wd thickSheet thinSheet ra which).stablePath =
      (anchorND ra false which).stablePath := by
  have hval : (anchorND ra false which).1 =
      (splitSurvivor m wd thickSheet thinSheet ra which).1 := by
    cases which <;> rfl
  show SheetRelabelStable.stablePathEquiv
      (splitRelabeling (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        thickSheet thinSheet) (NonTrivalentValencyTwoTracks.wallValid m wd).1
      (splitWallEdge m wd thickSheet thinSheet ra which).stablePath = _
  rw [SheetRelabelStable.stablePathEquiv_mk]
  refine congrArg NonDanglingEdge.stablePath (Subtype.ext ?_)
  show (splitRelabeling (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      thickSheet thinSheet).sourceEdgeEquiv
      (ungaugeSurvivor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        thickSheet thinSheet (splitSurvivor m wd thickSheet thinSheet ra which)).1 =
    (anchorND ra false which).1
  rw [hval]
  exact congrArg (fun z : IncidentSourceEdge
      (splitGaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        thickSheet thinSheet)
      (WallBlock.sourceVertex
        (splitGaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
          thickSheet thinSheet) ⟨wd.a, wd.hab⟩
        (splitGaugedAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
          thickSheet thinSheet)) ↦ z.1)
    (Equiv.apply_symm_apply
      (splitSurvivorEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        thickSheet thinSheet) (splitSurvivor m wd thickSheet thinSheet ra which))

/-- **The chart row of a paired survivor** is the chart row of its lift to the
incoming cover. -/
theorem outFD_row_split (which : Bool) :
    (NonTrivalentValencyTwoSplitExit.wallOutgoingFD m wd wallStar anchorBlk thickSheet
        thinSheet labelling₀ ra hGauged hOrdGauged hRowVal hMatrixWall).labelling.row
      (retainedRowFree ra hGauged (anchorND ra false which).stablePath) =
      wd.fullDim.labelling.row
        (splitLift m wd thickSheet thinSheet ra which).stablePath := by
  rw [← splitGaugeRowEquiv_splitWallEdge m wd thickSheet thinSheet ra which,
    outFD_row_retained m wd thickSheet thinSheet ra hGauged hOrdGauged labelling₀ hRowVal
      hMatrixWall (splitWallEdge m wd thickSheet thinSheet ra which).stablePath,
    splitLift_stablePath m wd thickSheet thinSheet ra which]

include hOrdGauged in
/-- The candidate-side test at `S`: the occurrence carrying a paired survivor's
row carries a given retained row exactly when the survivor's own row is that
row.  For `which = true` the carrier is the **piece**, not a retained
occurrence. -/
theorem stablePath_anchorOcc_iff (which : Bool)
    (r₀ : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    (retainedRowFree ra hGauged (anchorND ra false which).stablePath =
        retainedRowFree ra hGauged
          (splitGaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
            thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 r₀)) ↔
      (splitWallEdge m wd thickSheet thinSheet ra which).stablePath = r₀ := by
  rw [← splitGaugeRowEquiv_splitWallEdge m wd thickSheet thinSheet ra which]
  constructor
  · intro h
    exact (splitGaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1).injective
      (retainedRowFree_injective ra hGauged hOrdGauged h)
  · intro h
    exact congrArg _ (congrArg _ h)

/-- The dart-side test, the mirror of `stablePath_anchorOcc_iff`. -/
theorem label_dart_split_iff (which : Bool) (d : StableSourceDarts.Dart wd.cover)
    (hd : label (wd.tracks.iso.dart d) = wd.fullDim.labelling.row
      (splitLift m wd thickSheet thinSheet ra which).stablePath)
    (r₀ : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    (label (wd.tracks.iso.dart d) = wd.fullDim.labelling.row
        (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m)
          r₀)) ↔
      (splitWallEdge m wd thickSheet thinSheet ra which).stablePath = r₀ := by
  rw [hd, splitLift_stablePath m wd thickSheet thinSheet ra which]
  constructor
  · intro h
    exact NonTrivalentValencyTwoStarCountAll.injective_incomingRow m wd wallStar
      (wd.fullDim.labelling.row.injective h)
  · intro h
    exact congrArg _ (congrArg _ h)

/-- No member of the pair carries the vanishing chart row. -/
theorem label_dart_split_ne_base (which : Bool) (d : StableSourceDarts.Dart wd.cover)
    (hd : label (wd.tracks.iso.dart d) = wd.fullDim.labelling.row
      (splitLift m wd thickSheet thinSheet ra which).stablePath) :
    label (wd.tracks.iso.dart d) ≠ label m.base := by
  rw [hd, splitLift_stablePath m wd thickSheet thinSheet ra which]
  exact NonTrivalentValencyThreeStarCount.labelling_row_incomingRow_ne_base m wd _

/-! ## 4.  The star count -/

include src hOrd in
/-- **The star count at a branch vertex away from the anchor, on a retained
row**: (T1), then the gauge leg and (T2), then the incoming tracking. -/
theorem incidence_inl_retained (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hRight : (IncomingPairing.opBaseDart m wd).1.1 = q)
    (w : {w : BranchVertex (splitGaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        wallStar anchorBlk thickSheet thinSheet) //
      w.1 ≠ gaugedAnchorVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
        anchorBlk thickSheet thinSheet})
    (r₀ : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (validCandidate ra.setup).datum
        (candBranchMap ra hGauged hOrdGauged (Sum.inl w)).1
        (retainedRowFree ra hGauged
          (splitGaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
            thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 r₀)) =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquiv m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd hEnds
            (candBranchMap ra hGauged hOrdGauged (Sum.inl w)) ∧
        label d = (NonTrivalentValencyTwoSplitExit.wallOutgoingFD m wd wallStar anchorBlk
            thickSheet thinSheet labelling₀ ra hGauged hOrdGauged hRowVal
            hMatrixWall).labelling.row
          (retainedRowFree ra hGauged
            (splitGaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
              anchorBlk thickSheet thinSheet
              (NonTrivalentValencyTwoTracks.wallValid m wd).1 r₀))} := by
  classical
  set w₀ := (gaugeBranchEquivAnchorComplement (contractDatum wd.cover wd.hc wd.hab wd.hOne)
    wallStar anchorBlk thickSheet thinSheet
    (NonTrivalentValencyTwoTracks.wallValid m wd).1).symm w with hw₀
  set j := (branchEquivGaugedAnchorComplement m wd thickSheet thinSheet hOrd hEnds).symm w
    with hj
  have hgw : gaugeBranchEquivAnchorComplement (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      wallStar anchorBlk thickSheet thinSheet
      (NonTrivalentValencyTwoTracks.wallValid m wd).1 w₀ = w := Equiv.apply_symm_apply _ _
  have hGV : NonTrivalentValencyTwoSplitExit.splitGaugeVertexEquiv
      (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet thinSheet
      w₀.1.1 = w.1.1 :=
    (gaugeBranchEquivAnchorComplement_apply (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      wallStar anchorBlk thickSheet thinSheet
      (NonTrivalentValencyTwoTracks.wallValid m wd).1 w₀).symm.trans
      (congrArg (fun z : {z : BranchVertex (splitGaugedData
          (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet
          thinSheet) // z.1 ≠ gaugedAnchorVertex
          (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet
          thinSheet} ↦ z.1.1) hgw)
  have hjw : NonTrivalentValencyTwoTracksLeaf.branchEquivAnchorComplement m wd hOrd hEnds j =
      w₀ := Equiv.apply_symm_apply _ _
  have hMapU : sourceVertexMap wd.cover wd.hc wd.hab wd.hOne j.1.1 = w₀.1.1 :=
    (NonTrivalentValencyTwoTracksLeaf.branchEquivAnchorComplement_apply m wd hOrd hEnds
      j).symm.trans
      (congrArg (fun z : {z : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
        z.1 ≠ NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk} ↦ z.1.1) hjw)
  rw [vertexEquiv_inl m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd hEnds w,
    outFD_row_retained m wd thickSheet thinSheet ra hGauged hOrdGauged labelling₀ hRowVal
      hMatrixWall r₀,
    ← card_star_move_eq_incidenceCount m wd hEnds hLeft hRight j.1 j.2.1 j.2.2
      (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m) r₀)]
  refine Eq.trans ?_ (incidenceCount_gauged_eq_incoming m wd thickSheet thinSheet hOrd src
    w₀.1.1 w₀.2 j.1.1 hMapU j.1.2 r₀)
  rw [hGV]
  exact (incidenceCount_candVertex ra hGauged hOrdGauged w.1.1 w.2
    (splitGaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 r₀)).symm

include hOrd in
/-- **The star count at a branch vertex away from the anchor, on the bridge
row.**  Both sides vanish: downstairs the bridge joins `S` to `A_v` and is alone
in its class, upstairs the vanishing chart row reaches only the two anchor
ends. -/
theorem incidence_inl_bridge (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hRight : (IncomingPairing.opBaseDart m wd).1.1 = q)
    (w : {w : BranchVertex (splitGaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        wallStar anchorBlk thickSheet thinSheet) //
      w.1 ≠ gaugedAnchorVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
        anchorBlk thickSheet thinSheet}) :
    incidenceCount (validCandidate ra.setup).datum
        (candBranchMap ra hGauged hOrdGauged (Sum.inl w)).1 (bridgeRow ra hGauged) =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquiv m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd hEnds
            (candBranchMap ra hGauged hOrdGauged (Sum.inl w)) ∧
        label d = (NonTrivalentValencyTwoSplitExit.wallOutgoingFD m wd wallStar anchorBlk
            thickSheet thinSheet labelling₀ ra hGauged hOrdGauged hRowVal
            hMatrixWall).labelling.row (bridgeRow ra hGauged)} := by
  classical
  set j := (branchEquivGaugedAnchorComplement m wd thickSheet thinSheet hOrd hEnds).symm w
    with hj
  rw [incidenceCount_bridgeRow_inl_eq_zero ra hGauged hOrdGauged w]
  symm
  rw [vertexEquiv_inl m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd hEnds w,
    outFD_row_bridge m wd thickSheet thinSheet ra hGauged hOrdGauged labelling₀ hRowVal
      hMatrixWall]
  have h := card_star_move_eq_incidenceCount m wd hEnds hLeft hRight j.1 j.2.1 j.2.2
    (NonTrivalentValencyTwoTracks.facetRow m wd)
  rw [show wd.fullDim.labelling.row (NonTrivalentValencyTwoTracks.facetRow m wd) = label m.base
    from Equiv.apply_symm_apply _ _] at h
  rw [← h]
  exact incidenceCount_facetRow_eq_zero m wd hEnds hLeft hRight j.1 j.2.1 j.2.2

include hOrd in
/-- **The star count at `S`, on a retained row.**  The exact star
`{bridge, piece, e_alpha}` of `NonTrivalentValencyTwoSplitRows` is matched
occurrence by dart with the moved star (H-split) prescribes: `m.base` carries
the vanishing chart row, the two remaining darts carry the incoming rows of
`e_alpha` and `e_delta`, and `e_delta`'s row is carried at `S` by the
**piece**. -/
theorem incidence_inr_false_retained (hEnds : AnchorEnds m wd anchorBlk p q)
    (hPres : PrescribedSplitMove m wd thickSheet thinSheet ra p q)
    (r₀ : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (validCandidate ra.setup).datum
        (candBranchMap ra hGauged hOrdGauged (Sum.inr false)).1
        (retainedRowFree ra hGauged
          (splitGaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
            thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 r₀)) =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquiv m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd hEnds
            (candBranchMap ra hGauged hOrdGauged (Sum.inr false)) ∧
        label d = (NonTrivalentValencyTwoSplitExit.wallOutgoingFD m wd wallStar anchorBlk
            thickSheet thinSheet labelling₀ ra hGauged hOrdGauged hRowVal
            hMatrixWall).labelling.row
          (retainedRowFree ra hGauged
            (splitGaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
              anchorBlk thickSheet thinSheet
              (NonTrivalentValencyTwoTracks.wallValid m wd).1 r₀))} := by
  classical
  obtain ⟨first, second, -, hFirstLab, hSecondLab, hStar⟩ :=
    prescribedSplitMove_spec m wd thickSheet thinSheet ra p q hPres
  rw [vertexEquiv_anchor_false m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd hEnds
      hPres.1.1,
    outFD_row_retained m wd thickSheet thinSheet ra hGauged hOrdGauged labelling₀ hRowVal
      hMatrixWall r₀]
  have hRHS : Nat.card {d : D // graph.vert (m.perm d) = graph.vert m.base ∧
      label d = wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
        (wd.hCompat m) (wd.hForest m) r₀)} =
      ((Finset.univ.filter fun d : D ↦ graph.vert (m.perm d) = graph.vert m.base).filter
        fun d ↦ label d = wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc
          wd.hab wd.hOne (wd.hCompat m) (wd.hForest m) r₀)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter]
  have hBridgeRow : ¬ ((bridgeND ra hGauged).stablePath =
      retainedRowFree ra hGauged
        (splitGaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
          thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 r₀)) := by
    rw [stablePath_bridgeND ra hGauged]
    exact fun h ↦ retainedRowFree_ne_bridgeRow ra hGauged hOrdGauged _ h.symm
  rw [hRHS, NonTrivalentValencyThreeStarCount.filter_moved_base m wd first second hStar,
    Finset.filter_insert,
    if_neg (Ne.symm
      (NonTrivalentValencyThreeStarCount.labelling_row_incomingRow_ne_base m wd r₀)),
    NonTrivalentValencyThreeStarCount.card_filter_pair _ _
      (NonTrivalentValencyThreeStarCount.dart_ne m wd first second hStar)]
  show incidenceCount (validCandidate ra.setup).datum (anchorBranchVertex ra false)
    (retainedRowFree ra hGauged
      (splitGaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 r₀)) = _
  unfold incidenceCount
  rw [incidentEdges_anchorBranchVertex_ordered ra hGauged false, Finset.filter_insert,
    if_neg hBridgeRow,
    NonTrivalentValencyThreeStarCount.card_filter_pair _ _
      (directRetained_ne_throughND ra hGauged false),
    show (directRetained ra hGauged false).stablePath =
        retainedRowFree ra hGauged (anchorND ra false false).stablePath from
      stablePath_directRetained ra hGauged false,
    show (throughND ra hGauged false).stablePath =
        retainedRowFree ra hGauged (anchorND ra false true).stablePath from
      stablePath_throughND ra hGauged false,
    if_congr (stablePath_anchorOcc_iff m wd thickSheet thinSheet ra hGauged hOrdGauged false
      r₀) rfl rfl,
    if_congr (stablePath_anchorOcc_iff m wd thickSheet thinSheet ra hGauged hOrdGauged true
      r₀) rfl rfl,
    if_congr (label_dart_split_iff m wd thickSheet thinSheet ra false first hFirstLab r₀)
      rfl rfl,
    if_congr (label_dart_split_iff m wd thickSheet thinSheet ra true second hSecondLab r₀)
      rfl rfl]

include hOrd in
/-- **The star count at `S`, on the bridge row.**  Both sides are one: the bridge
occurrence downstairs, the contracted dart `m.base` upstairs. -/
theorem incidence_inr_false_bridge (hEnds : AnchorEnds m wd anchorBlk p q)
    (hPres : PrescribedSplitMove m wd thickSheet thinSheet ra p q) :
    incidenceCount (validCandidate ra.setup).datum
        (candBranchMap ra hGauged hOrdGauged (Sum.inr false)).1 (bridgeRow ra hGauged) =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquiv m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd hEnds
            (candBranchMap ra hGauged hOrdGauged (Sum.inr false)) ∧
        label d = (NonTrivalentValencyTwoSplitExit.wallOutgoingFD m wd wallStar anchorBlk
            thickSheet thinSheet labelling₀ ra hGauged hOrdGauged hRowVal
            hMatrixWall).labelling.row (bridgeRow ra hGauged)} := by
  classical
  obtain ⟨first, second, -, hFirstLab, hSecondLab, hStar⟩ :=
    prescribedSplitMove_spec m wd thickSheet thinSheet ra p q hPres
  rw [vertexEquiv_anchor_false m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd hEnds
      hPres.1.1,
    outFD_row_bridge m wd thickSheet thinSheet ra hGauged hOrdGauged labelling₀ hRowVal
      hMatrixWall]
  have hRHS : Nat.card {d : D // graph.vert (m.perm d) = graph.vert m.base ∧
      label d = label m.base} =
      ((Finset.univ.filter fun d : D ↦ graph.vert (m.perm d) = graph.vert m.base).filter
        fun d ↦ label d = label m.base).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter]
  have hEmptyD : (({wd.tracks.iso.dart first, wd.tracks.iso.dart second} : Finset D).filter
      fun d ↦ label d = label m.base) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact label_dart_split_ne_base m wd thickSheet thinSheet ra false first hFirstLab
    · exact label_dart_split_ne_base m wd thickSheet thinSheet ra true second hSecondLab
  have hR : ((Finset.univ.filter fun d : D ↦ graph.vert (m.perm d) = graph.vert m.base).filter
      fun d ↦ label d = label m.base).card = 1 := by
    rw [NonTrivalentValencyThreeStarCount.filter_moved_base m wd first second hStar,
      Finset.filter_insert, if_pos rfl, hEmptyD]
    simp
  rw [hRHS, hR]
  show incidenceCount (validCandidate ra.setup).datum (anchorBranchVertex ra false)
    (bridgeRow ra hGauged) = 1
  have hEmptyC : (({directRetained ra hGauged false, throughND ra hGauged false} :
        Finset (NonDanglingEdge (validCandidate ra.setup).datum)).filter
      fun e ↦ e.stablePath = bridgeRow ra hGauged) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · rw [stablePath_directRetained ra hGauged false]
      exact retainedRowFree_ne_bridgeRow ra hGauged hOrdGauged _
    · rw [stablePath_throughND ra hGauged false]
      exact retainedRowFree_ne_bridgeRow ra hGauged hOrdGauged _
  unfold incidenceCount
  rw [incidentEdges_anchorBranchVertex_ordered ra hGauged false, Finset.filter_insert,
    if_pos (stablePath_bridgeND ra hGauged), hEmptyC]
  simp

include hOrd src in
/-- **The star count at every branch vertex except `A_v`.** -/
theorem incidence_of_ne_rightAnchor (hEnds : AnchorEnds m wd anchorBlk p q)
    (hPres : PrescribedSplitMove m wd thickSheet thinSheet ra p q)
    (v : BranchVertex (validCandidate ra.setup).datum)
    (hv : v ≠ candBranchMap ra hGauged hOrdGauged (Sum.inr true))
    (r : StablePath (validCandidate ra.setup).datum) :
    incidenceCount (validCandidate ra.setup).datum v.1 r =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquiv m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd hEnds v ∧
        label d = (NonTrivalentValencyTwoSplitExit.wallOutgoingFD m wd wallStar anchorBlk
            thickSheet thinSheet labelling₀ ra hGauged hOrdGauged hRowVal
            hMatrixWall).labelling.row r} := by
  classical
  obtain ⟨x, rfl⟩ : ∃ x, candBranchMap ra hGauged hOrdGauged x = v :=
    ⟨(candBranchEquiv ra hGauged hOrdGauged).symm v,
      (candBranchEquiv ra hGauged hOrdGauged).apply_symm_apply v⟩
  obtain ⟨r', rfl⟩ : ∃ r', rowMap ra hGauged r' = r :=
    ⟨rowEquiv ra hGauged hOrdGauged r, (rowEquiv ra hGauged hOrdGauged).left_inv r⟩
  cases x with
  | inl w =>
    cases r' with
    | none =>
      exact incidence_inl_bridge m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd
        labelling₀ hRowVal hMatrixWall hEnds hPres.1.1 hPres.1.2 w
    | some r₀ =>
      have h := incidence_inl_retained m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd
        src labelling₀ hRowVal hMatrixWall hEnds hPres.1.1 hPres.1.2 w
        ((splitGaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
          thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1).symm r₀)
      rwa [Equiv.apply_symm_apply] at h
  | inr side =>
    cases side with
    | true => exact absurd rfl hv
    | false =>
      cases r' with
      | none =>
        exact incidence_inr_false_bridge m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd
          labelling₀ hRowVal hMatrixWall hEnds hPres
      | some r₀ =>
        have h := incidence_inr_false_retained m wd thickSheet thinSheet ra hGauged hOrdGauged
          hOrd labelling₀ hRowVal hMatrixWall hEnds hPres
          ((splitGaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
            thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1).symm r₀)
        rwa [Equiv.apply_symm_apply] at h

include hOrd src in
/-- **The star count at `A_v`, from the leftover equation.**  A stable row of the
candidate meets its branch vertices twice in all, a chart row carries two darts
of the moved graph, `vertexEquiv` is a bijection, and the count agrees at every
other branch vertex; so it agrees at `A_v` too.  This is where the split's two
divalent pass-through vertices cost nothing: they are not branch vertices, so
they never enter either sum. -/
theorem incidence_inr_true (hEnds : AnchorEnds m wd anchorBlk p q)
    (hPres : PrescribedSplitMove m wd thickSheet thinSheet ra p q)
    (r : StablePath (validCandidate ra.setup).datum) :
    incidenceCount (validCandidate ra.setup).datum
        (candBranchMap ra hGauged hOrdGauged (Sum.inr true)).1 r =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquiv m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd hEnds
            (candBranchMap ra hGauged hOrdGauged (Sum.inr true)) ∧
        label d = (NonTrivalentValencyTwoSplitExit.wallOutgoingFD m wd wallStar anchorBlk
            thickSheet thinSheet labelling₀ ra hGauged hOrdGauged hRowVal
            hMatrixWall).labelling.row r} := by
  classical
  set outFD := NonTrivalentValencyTwoSplitExit.wallOutgoingFD m wd wallStar anchorBlk
    thickSheet thinSheet labelling₀ ra hGauged hOrdGauged hRowVal hMatrixWall with houtFD
  set v₀ := candBranchMap ra hGauged hOrdGauged (Sum.inr true) with hv₀
  set f : BranchVertex (validCandidate ra.setup).datum → ℕ :=
    fun v ↦ incidenceCount (validCandidate ra.setup).datum v.1 r with hf
  set g : BranchVertex (validCandidate ra.setup).datum → ℕ :=
    fun v ↦ Nat.card {d : D // graph.vert (m.perm d) =
        vertexEquiv m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd hEnds v ∧
      label d = outFD.labelling.row r} with hg
  have hSumF : ∑ v, f v = 2 :=
    NonTrivalentValencyThreeStarCount.sum_incidenceCount_branchVertex
      (validCandidate ra.setup).datum outFD.connected outFD.pathEnds r
  have hSumG : ∑ v, g v = 2 := by
    rw [Fintype.sum_equiv
      (vertexEquiv m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd hEnds)
      g (fun x : V ↦ Nat.card {d : D // graph.vert (m.perm d) = x ∧
        label d = outFD.labelling.row r}) (fun v ↦ rfl)]
    exact NonTrivalentValencyThreeStarCount.sum_natCard_moved m wd (outFD.labelling.row r)
  have hAway : ∀ v ∈ Finset.univ.erase v₀, f v = g v := by
    intro v hv
    exact incidence_of_ne_rightAnchor m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd
      src labelling₀ hRowVal hMatrixWall hEnds hPres v (Finset.mem_erase.mp hv).1 r
  have hfsum := Finset.add_sum_erase Finset.univ f (Finset.mem_univ v₀)
  have hgsum := Finset.add_sum_erase Finset.univ g (Finset.mem_univ v₀)
  have hEq : ∑ x ∈ Finset.univ.erase v₀, f x = ∑ x ∈ Finset.univ.erase v₀, g x :=
    Finset.sum_congr rfl hAway
  show f v₀ = g v₀
  omega

include hOrd src in
/-- **The star count, at every branch vertex and every row, at a valency-two
Base II split wall.**  This is the one geometric input
`NonTrivalentValencyTwoSplitTracks` takes, here under (H-split) alone. -/
theorem incidence_of_prescribedSplitMove (hEnds : AnchorEnds m wd anchorBlk p q)
    (hPres : PrescribedSplitMove m wd thickSheet thinSheet ra p q)
    (v : BranchVertex (validCandidate ra.setup).datum)
    (r : StablePath (validCandidate ra.setup).datum) :
    incidenceCount (validCandidate ra.setup).datum v.1 r =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquiv m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd hEnds v ∧
        label d = (NonTrivalentValencyTwoSplitExit.wallOutgoingFD m wd wallStar anchorBlk
            thickSheet thinSheet labelling₀ ra hGauged hOrdGauged hRowVal
            hMatrixWall).labelling.row r} := by
  classical
  by_cases hv : v = candBranchMap ra hGauged hOrdGauged (Sum.inr true)
  · subst hv
    exact incidence_inr_true m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd src
      labelling₀ hRowVal hMatrixWall hEnds hPres r
  · exact incidence_of_ne_rightAnchor m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd
      src labelling₀ hRowVal hMatrixWall hEnds hPres v hv r

include hOrd src in
/-- **`OuterWalk.TypeChangeLink` at a valency-two Base II split wall under
(H-split).** -/
def typeChangeLink_of_prescribedSplitMove (hEnds : AnchorEnds m wd anchorBlk p q)
    (hPres : PrescribedSplitMove m wd thickSheet thinSheet ra p q) :
    TypeChangeLink m wd :=
  typeChangeLink_of_incidence m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd
    labelling₀ hRowVal hMatrixWall hEnds
    (incidence_of_prescribedSplitMove m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd
      src labelling₀ hRowVal hMatrixWall hEnds hPres)

include hOrd src in
/-- **The link from the row condition alone** -- the shape the move-to-type
dispatcher discharges. Under the orientation clause the move always places one
dart at each anchor end, so all that has to be checked is that those two darts
carry the *stable rows* of `e_alpha` and `e_delta`. -/
def typeChangeLink_of_rows (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hRight : (IncomingPairing.opBaseDart m wd).1.1 = q)
    (hRows : ∀ x y : StableSourceDarts.Dart wd.cover, x.1.1 = p → y.1.1 = q →
      (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
          {wd.tracks.iso.dart x, wd.tracks.iso.dart y} →
      x.2.1.stablePath = (splitLift m wd thickSheet thinSheet ra false).stablePath ∧
        y.2.1.stablePath = (splitLift m wd thickSheet thinSheet ra true).stablePath) :
    TypeChangeLink m wd :=
  typeChangeLink_of_prescribedSplitMove m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd
    src labelling₀ hRowVal hMatrixWall hEnds
    (prescribedSplitMove_of_rows m wd thickSheet thinSheet ra hLeft hRight hRows)

end Wall

/-! ## 5.  The receipt-free headline at an actual wall -/

section Headline

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {deg : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival deg graph label (label m.base)}
  (wd : WallData arrival)

/-- **The Base II split type-changing exit at a two-valent wall of the outer
walk, with the star count discharged.**
`NonTrivalentValencyTwoSplitExit.exists_typeChangeLink_split_of_wallData` with
its `Tracks` input replaced by (H-split): from the wall data and the incoming
two-valent star alone this produces the anchor block, `nd(A) = 4`, the two
anchor ends `p`, `q` of the vanishing row (the incoming `2 + 2` / `1 + 3` /
`3 + 1` trichotomy is discharged internally by
`NonTrivalentValencyTwoTracksLeaf.exists_anchorEnds`), the ordinary-block
trivalence and the wall labelling
`NonTrivalentValencyTwoBaseOneRowDictionary.exists_wallLabelling_two`; and then
-- for Configuration A, the four named survivors of the paper's picture and the
strict index inequality `k_delta < k_alpha` -- the gauged split anchor
`NonTrivalentValencyTwoSplitRows.splitAnchor_gauged`, the outgoing
`FullDimensionalSourcePresentation` on the incoming chart, the common minor
`AgreeOffColumn` that `OuterWalk.TypeChangeLink.agree` asks for, and the link
itself as soon as (H-split) is supplied. -/
theorem exists_typeChangeLink_of_prescribedSplitMove_of_wallData
    (wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    ∃ (anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
      (p q : wd.cover.SourceVertex),
      nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            ⟨wd.a, wd.hab⟩ anchorBlock) = 4 ∧
      ∀ (_ : ∀ direction : Fin 2,
          (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
            anchorBlock direction).card = 2)
        (alphaEdge betaEdge deltaEdge epsilonEdge :
          IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
              ⟨wd.a, wd.hab⟩ anchorBlock)),
        alphaEdge ∈ directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            wallStar anchorBlock 0 →
        betaEdge ∈ directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            wallStar anchorBlock 0 →
        deltaEdge ∈ directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            wallStar anchorBlock 1 →
        epsilonEdge ∈ directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            wallStar anchorBlock 1 →
        alphaEdge ≠ betaEdge → deltaEdge ≠ epsilonEdge →
        (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex deltaEdge.1 <
            (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex alphaEdge.1 →
        ∃ (ra : SplitAnchor
            (splitGaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
              anchorBlock (occurrenceSheet alphaEdge) (occurrenceSheet deltaEdge)) wallStar
            (splitGaugedAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
              anchorBlock (occurrenceSheet alphaEdge) (occurrenceSheet deltaEdge)))
          (out : FullDimensionalSourcePresentation (validCandidate ra.setup).datum
            coordinate),
          AgreeOffColumn wd.incomingMatrix
              (GluingDatum.LengthMatrixPresentation.matrix out.labelling.presentation)
              wd.column ∧
            (PrescribedSplitMove m wd (occurrenceSheet alphaEdge)
                (occurrenceSheet deltaEdge) ra p q → Nonempty (TypeChangeLink m wd)) := by
  classical
  have hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid :=
    NonTrivalentValencyTwoRows.wall_valid wd.cover wd.fullDim wd.hc wd.hab wd.hOne
      (wd.hForest m)
  obtain ⟨anchorBlock, hNd, src⟩ :=
    NonTrivalentAnchorValency.twoBranchAnchor_of_single_row wd.cover wd.fullDim wd.hc wd.hab
      wd.hOne (wd.hForest m) wd.coordinates (label m.base) wd.hRows wd.hZeroCoord
      wd.hPosCoord wd.hFacetZero wallStar
  have hOrd := NonTrivalentValencyTwoRowEquiv.ordinaryTrivalent_of_wall_metric wd.cover
    wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m) wallStar wd.coordinates (label m.base)
    wd.hRows wd.hZeroCoord anchorBlock hNd
  obtain ⟨labelling₀, hRowVal, hMatrixWall⟩ :=
    NonTrivalentValencyTwoBaseOneRowDictionary.exists_wallLabelling_two wd.cover wd.fullDim
      wd.hc wd.hab wd.hOne (wd.hForest m) (label m.base) wallStar wd.coordinates wd.hRows
      wd.hZeroCoord wd.hPosCoord wd.hFacetZero
  obtain ⟨p, q, hEnds⟩ := NonTrivalentValencyTwoTracksLeaf.exists_anchorEnds m wd src hOrd
  refine ⟨anchorBlock, p, q, hNd, ?_⟩
  intro hSplit alphaEdge betaEdge deltaEdge epsilonEdge hAlpha hBeta hDelta hEpsilon
    hAlphaNe hDeltaNe hIndex
  have ra := splitAnchor_gauged src hSplit
    (NonTrivalentUniqueFourValent.wall_target_connected wd.cover wd.fullDim wd.hab wd.hOne)
    (NonTrivalentUniqueFourValent.wall_target_genus wd.cover wd.fullDim wd.hab wd.hOne)
    hValid.1 hAlpha hBeta hDelta hEpsilon hAlphaNe hDeltaNe hIndex
  have hGauged := splitGaugedData_valid (contractDatum wd.cover wd.hc wd.hab wd.hOne)
    wallStar anchorBlock (occurrenceSheet alphaEdge) (occurrenceSheet deltaEdge) hValid
  have hOrdGauged := NonTrivalentValencyTwoSplitExit.ordinaryTrivalent_splitGauged
    (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlock
    (occurrenceSheet alphaEdge) (occurrenceSheet deltaEdge) hValid.1 hOrd
  refine ⟨ra, NonTrivalentValencyTwoSplitExit.wallOutgoingFD m wd wallStar anchorBlock
    (occurrenceSheet alphaEdge) (occurrenceSheet deltaEdge) labelling₀ ra hGauged hOrdGauged
    hRowVal hMatrixWall, ?_, ?_⟩
  · have h := NonTrivalentValencyTwoSplitRowDictionary.agreeOffColumn_chartLabelling wd.cover
      wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m) (label m.base) wallStar anchorBlock
      (occurrenceSheet alphaEdge) (occurrenceSheet deltaEdge) labelling₀ ra hGauged
      hOrdGauged wd.coordinates wd.hZeroCoord wd.hPosCoord wd.hFacetZero hRowVal hMatrixWall
    rw [wd.targetEdge_symm_contracted] at h
    exact h
  · intro hPres
    exact ⟨typeChangeLink_of_prescribedSplitMove m wd (occurrenceSheet alphaEdge)
      (occurrenceSheet deltaEdge) ra hGauged hOrdGauged hOrd src labelling₀ hRowVal
      hMatrixWall hEnds hPres⟩

/-- **The mirror split member, with the star count discharged.**
`NonTrivalentValencyTwoSplitExit.relabelStar` exchanges the two labels of the
wall star, and in Configuration A that exchanges thick and thin, so the member
in which a class over `wallStar.edge 1` splits above the divalent endpoint is
`exists_typeChangeLink_of_prescribedSplitMove_of_wallData` read at the
relabelled star; only the incoming classifier and Configuration A have to be
transported. -/
theorem exists_typeChangeLink_of_prescribedSplitMove_splitMirror_of_wallData
    (wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    ∃ (anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
      (p q : wd.cover.SourceVertex),
      nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            ⟨wd.a, wd.hab⟩ anchorBlock) = 4 ∧
      ∀ (_ : ∀ direction : Fin 2,
          (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
            anchorBlock direction).card = 2)
        (alphaEdge betaEdge deltaEdge epsilonEdge :
          IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
              ⟨wd.a, wd.hab⟩ anchorBlock)),
        alphaEdge ∈ directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            wallStar anchorBlock 1 →
        betaEdge ∈ directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            wallStar anchorBlock 1 →
        deltaEdge ∈ directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            wallStar anchorBlock 0 →
        epsilonEdge ∈ directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            wallStar anchorBlock 0 →
        alphaEdge ≠ betaEdge → deltaEdge ≠ epsilonEdge →
        (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex deltaEdge.1 <
            (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex alphaEdge.1 →
        ∃ (ra : SplitAnchor
            (splitGaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne)
              (NonTrivalentValencyTwoSplitExit.relabelStar wallStar) anchorBlock
              (occurrenceSheet alphaEdge) (occurrenceSheet deltaEdge))
            (NonTrivalentValencyTwoSplitExit.relabelStar wallStar)
            (splitGaugedAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne)
              (NonTrivalentValencyTwoSplitExit.relabelStar wallStar) anchorBlock
              (occurrenceSheet alphaEdge) (occurrenceSheet deltaEdge)))
          (out : FullDimensionalSourcePresentation (validCandidate ra.setup).datum
            coordinate),
          AgreeOffColumn wd.incomingMatrix
              (GluingDatum.LengthMatrixPresentation.matrix out.labelling.presentation)
              wd.column ∧
            (PrescribedSplitMove m wd (occurrenceSheet alphaEdge)
                (occurrenceSheet deltaEdge) ra p q → Nonempty (TypeChangeLink m wd)) := by
  classical
  obtain ⟨anchorBlock, p, q, hNd, hRest⟩ :=
    exists_typeChangeLink_of_prescribedSplitMove_of_wallData m wd
      (NonTrivalentValencyTwoSplitExit.relabelStar wallStar)
  refine ⟨anchorBlock, p, q, hNd, ?_⟩
  intro hSplit alphaEdge betaEdge deltaEdge epsilonEdge hAlpha hBeta hDelta hEpsilon
    hAlphaNe hDeltaNe hIndex
  have hZero : directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (NonTrivalentValencyTwoSplitExit.relabelStar wallStar) anchorBlock 0 =
        directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
          anchorBlock 1 :=
    NonTrivalentValencyTwoSplitExit.directionSurvivors_relabelStar_zero wallStar
  have hOne' : directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (NonTrivalentValencyTwoSplitExit.relabelStar wallStar) anchorBlock 1 =
        directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
          anchorBlock 0 :=
    NonTrivalentValencyTwoSplitExit.directionSurvivors_relabelStar_one wallStar
  refine hRest (fun direction ↦ ?_) alphaEdge betaEdge deltaEdge epsilonEdge
    (hZero ▸ hAlpha) (hZero ▸ hBeta) (hOne' ▸ hDelta) (hOne' ▸ hEpsilon)
    hAlphaNe hDeltaNe hIndex
  have hDir : directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (NonTrivalentValencyTwoSplitExit.relabelStar wallStar) anchorBlock direction =
        directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
          anchorBlock (Equiv.swap 0 1 direction) :=
    NonTrivalentValencyTwoSplitExit.directionSurvivors_relabelStar wallStar direction
  rw [hDir]
  exact hSplit _

end Headline

end

end DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitStarCount
