module

public import DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleRowDictionary
public import DraismaVargas.LocalCases.NonTrivalentValencyThreePathEnds

@[expose] public section

/-!
# The valency-three Type I / Type II exit: outgoing presentation and link

Source: Vargas, Part II, Section 5.1 (the labelling convention at a
non-trivalent wall, and Lemma `lm:change-comb-type`: the wall matrix is the
common minor `A_{\varphi_0}` of the two incoming matrices) together with
Section 5.3, case `{v3-nd4}` (base trees `T_alpha` with `alpha` simple, the
Type I and Type II members, and the two subcases `{v3-nd4-1}`, `{v3-nd4-2}`
whose realized pairs are `(3,2)` resp. `(4,5)`), and the conclusion of the proof
of Proposition `prop-signed-mult`(2), which asks for a full-dimensional morphism
of each of the three types -- so that the walk can realize a prescribed
Whitehead move.  The interface this module serves is
`OuterWalk.TypeChangeLink`.

This is the Type I / Type II sibling of `NonTrivalentValencyThreeExit` (Type III)
and `NonTrivalentValencyThreePathEnds`.  The candidates over the two-fold branch
gauge are built in `NonTrivalentValencyThreeSimpleCandidate`; their rows,
descent, row equivalence, chart labelling and entrywise common minor at an
actual wall are in `NonTrivalentValencyThreeSimpleRows`,
`NonTrivalentValencyThreeSimpleRowEquiv` and
`NonTrivalentValencyThreeSimpleRowDictionary`.  This module builds the object
`OuterWalk.TypeChangeLink` asks for: a `FullDimensionalSourcePresentation` of
the outgoing candidate **on the incoming chart index type**, with the
`AgreeOffColumn` statement against the incoming honest matrix.

## The one structural difference from Type III

The candidate's base datum is `SimpleBase.gaugedData`, not the wall datum, so
`TypeChangeLink.base` is the gauged datum and `baseValid` is
`SimpleBase.gaugedData_valid` -- exactly as valency four's
`PrescribedPairing.gaugedData` (see the docstring of `OuterWalk.TypeChangeLink`).
The gauge is crossed by `NonTrivalentValencyThreeSimpleRowDictionary`'s
`gaugedLabelling_matrix` / `gaugedLabelling_row` on the matrix side, and here by
`exists_ungauged_vertex` / `hasPathEnds_gaugedData` on the geometric side.

The second difference is the anchor picture: above the anchor the Type I /
Type II resolution has **three** new vertices `A_u`, `A'`, `A_v` with exact
stars `3, 2, 3`, and `A'` is *divalent*.  A wall path end landing on `A'` is
therefore not a path end of the candidate; its row continues through the second
occurrence `e'` above `t_1` (`newSourceEdge_stablePath_eq_retained`)
and stops at the trivalent `A_u`.  Type III has no such vertex, which is why
the transport in `NonTrivalentValencyThreePathEnds` is shorter than
`exists_isPathEnd_anchor` below.

## What is reused by import, and what is new

The generic infrastructure is `NonTrivalentValencyTwoExit`'s and is used
verbatim, not copied: `ofTypeChange`, `genus_sourceGraph_contractDatum`,
`reindexLabelling₂` / `matrix_reindexLabelling₂` (two **independent** charts --
the new target occurrence goes into the vanishing column `t_1`, the bridge row
into the vanishing row `h_1 = label m.base`; a single chart cannot satisfy
`TypeChangeLink.agree`), `rowChart` / `colChart`, `wallLab`,
`incoming_facet_eq_zero` and `wallDatum_trivalent_away`.
`NonTrivalentValencyThreeExit`'s `ordinaryBlock_trivalent` and
`noContractedReturn_of_valency_three` are reused as they stand (they mention only
the wall datum and the `ThreeBranchAnchor`, which `SimpleBase.source`
supplies); `WallDatumPathEnds.hasPathEnds_contractDatum` is the wall datum's own
`HasPathEnds`.

What is new here is everything that mentions the Type I / Type II candidate.

## What is proved

* `exists_ungauged_vertex`, `hasPathEnds_gaugedData`: the two branch gauges move
  no surviving valency and no path end
  (`StableGraphIncidence.hasPathEnds_sheetRelabel` twice).
* `exists_isPathEnd_anchor`, `exists_isPathEnd_ordinary`,
  `exists_isPathEnd_of_wall_end`: a path end of the gauged wall datum transports
  to a path end of the outgoing candidate on the retained row of the same
  occurrence.  At the anchor the four survivors are separated by their target
  occurrence and their gauged class: `e_alpha` ends at `A_u`, `e_beta` and
  `e_gamma` at `A_v`, and `e_delta` -- whose own end `A'` is divalent -- is
  moved to `e'` at `A_u`.
* `hasPathEnds_of_retainedRowEnds`, `hasPathEnds_candidate`: **`HasPathEnds` of
  the outgoing candidate**, from `HasPathEnds` of the gauged wall datum alone;
  the bridge row `h_1` is a path end outright because both `A_u` and `A_v` are
  trivalent.
* `candidate_trivalent`: **the outgoing candidate is trivalent**, from the
  gauged datum's trivalence away from the wall and at every ordinary block.  At
  the anchor the stars are `3, 2, 3` and a fine class of `A` outside `A_u`
  carries at most one survivor; at an ordinary block the census gives
  `nd(B_u) <= 2` and `nd(B_v) = nd(B)`.
* `outLabelling`, `matrix_outLabelling_eq_incoming`: the outgoing honest
  labelling in the incoming chart, and the entrywise common minor, obtained by
  composing `NonTrivalentValencyThreeSimpleRowDictionary.matrix_candidateLabelling`
  with `gaugedLabelling_matrix` and
  `StablePathFacetContraction.matrix_wallLabelling`.
* `outLabelling_row_bridge`, `outLabelling_row_retained`: the **row half of the
  `InteriorGraphTracking.Tracks.row_map` obligation**.  The bridge row occupies
  the vanishing row `facet` (= `label m.base` along the walk) and every retained
  row keeps the incoming chart coordinate of its own incoming row -- the two
  gauges do not move a stable row.
* `matrix_outLabelling_facet_eq_zero`, `matrix_outLabelling_corner_pos`: the
  bridge row vanishes off the contracted column and its corner entry is
  `1 / index(h_1) > 0`; `bridgeEdge_isolated` says `e_1` is alone in its stable
  class because **both** its ends `A_u`, `A_v` are trivalent.
* `agreeOffColumn_outLabelling`, `det_outLabelling_ne_zero`: the `AgreeOffColumn`
  shape `TypeChangeLink.agree` asks for, and the outgoing nonsingularity by
  `NonTrivalentLinkMatrix.det_ne_zero`.
* `outgoing_targetConnected`, `outgoing_targetGenus`, `outgoing_targetEdgeCard`:
  the expanded wall target is connected of genus zero with as many edges as the
  incoming target.
* `gaugedData_trivalent_away`, `gaugedData_ordinary_trivalent`,
  `candidate_trivalent_wall`, `hasPathEnds_wall`: the two geometric hypotheses
  discharged at an actual three-valent wall.
* `outgoingFD`: the outgoing `FullDimensionalSourcePresentation` on
  `coordinate`.  Its hypotheses are the incoming full-dimensional cover, its
  contraction forest, `NoContractedReturn`, the wall metric of a Part II open
  facet with a single vanishing stable row, the `SimpleBase` and the wall
  datum's validity; **no** receipt about the candidate remains -- validity,
  saturation, target connectedness/genus/edge count, source genus,
  nonsingularity, trivalence and path ends are all derived.  `wallOutgoingFD`
  is the same at an `OuterWalk.WallData`, where `NoContractedReturn` is
  discharged from `wallStar` and every metric hypothesis is the wall data's
  own, so only `simpleBase` and `hValid` are passed in.
* `typeChangeLink_of_receipts`: an inhabitant of `OuterWalk.TypeChangeLink` at a
  three-valent wall over the gauged wall datum, from `simpleBase`, `hValid` and
  `tracks`.

## The hypotheses that remain explicit here

1. `tracks : InteriorGraphTracking.Tracks (wallOutgoingFD ...) (graph.move m)
   label`: the dart-level dictionary between the candidate's stable graph and
   the Whitehead move of the tracked ambient graph.  Its `row_map` half is
   `outLabelling_row_bridge` / `outLabelling_row_retained` above; its `iso` half
   is the branch-vertex bijection `NonTrivalentValencyThreeSimpleTracks.vertexEquiv`
   together with the star count of `NonTrivalentValencyThreeSimpleStarCount`,
   which supplies `typeChangeLink_of_prescribedSimpleMove` under (H-I/II) alone,
   exactly as `NonTrivalentValencyThreeTracks` and
   `NonTrivalentValencyThreeStarCount` do for the Type III exit.
2. `wallStar : ThirdEquation.ThreeStar (contract wd.coverTarget wd.hab wd.hOne)
   ⟨wd.a, wd.hab⟩`.  At an actual three-valent wall of the outer walk this
   witness comes from `OuterWalk.WallData.valency` and
   `ThirdEquation.ThreeStar.of_card`; the valency dispatcher
   `NonTrivalentValencyThreeDispatcher` produces it, not this module
   (`NonTrivalentValencyThreeExit` and `NonTrivalentValencyThreePathEnds` carry
   the same hypothesis).
3. Nothing here chooses *which* of Types I, II, III the move `m` prescribes:
   `simpleBase` is a parameter carrying the order condition, and
   `NonTrivalentValencyThreeDispatcher.classify` picks the type from the
   Whitehead move to be realized.

No new structure is introduced: every declaration here is a composition of
existing ones applied to `NonTrivalentValencyThreeSimpleCandidate.validCandidate`,
so there is nothing beyond the definitions themselves to witness for
non-vacuity, and each definition is applied
(`outLabelling` in `outgoingFD`, `outgoingFD` in `wallOutgoingFD`,
`wallOutgoingFD` in `typeChangeLink_of_receipts`).  Nothing here identifies a
graph by a matrix.

## Used by

`OuterWalk.TypeChangeLink` (hence `OuterWalk.coneEntry_of_reaches` and its
`link` hypothesis) at Part II case `{v3-nd4}`, Types I and II.
-/


namespace DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleExit

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionCoarseFine
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.ThirdEquation
open DraismaVargas.LocalCases.W3R1SourceProfile
open DraismaVargas.LocalCases.NonTrivalentValencyThreeAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyThreeCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleRows
open DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleRowEquiv

section Transport

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {anchor : WallBlock data wall} (base : SimpleBase data star anchor)

noncomputable section

/-! ### The two branch gauges are invisible to surviving valency -/

private theorem nonDanglingValency_step {datum : GluingDatum target degree}
    (relabeling : datum.SheetRelabeling) (hConnected : datum.Connected)
    (place : target.V) (sheet : Fin degree) :
    nonDanglingValency relabeling.apply
        (relabeling.apply.sourceEndpoint place
          (relabeling.vertexPermutation place sheet)) =
      nonDanglingValency datum (datum.sourceEndpoint place sheet) := by
  have h := SheetRelabelStable.nonDanglingValency_map relabeling hConnected
    (datum.sourceEndpoint place sheet)
  rwa [SheetRelabelPruning.sourceVertexEquiv_sourceEndpoint] at h

private theorem exists_step_vertex {datum : GluingDatum target degree}
    (relabeling : datum.SheetRelabeling) (hConnected : datum.Connected)
    (v : relabeling.apply.SourceVertex) :
    ∃ u : datum.SourceVertex, u.1.1 = v.1.1 ∧
      nonDanglingValency relabeling.apply v = nonDanglingValency datum u := by
  refine ⟨datum.sourceEndpoint v.1.1
    ((relabeling.vertexPermutation v.1.1).symm v.1.2), rfl, ?_⟩
  have h := nonDanglingValency_step relabeling hConnected v.1.1
    ((relabeling.vertexPermutation v.1.1).symm v.1.2)
  rw [Equiv.apply_symm_apply] at h
  have hv : relabeling.apply.sourceEndpoint v.1.1 v.1.2 = v :=
    (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨rfl, rfl⟩
  rw [hv] at h
  exact h

/-- **Every gauged source vertex has an ungauged partner over the same target
vertex with the same surviving valency.** -/
theorem exists_ungauged_vertex (hValid : data.Valid)
    (v : base.gaugedData.SourceVertex) :
    ∃ u : data.SourceVertex, u.1.1 = v.1.1 ∧
      nonDanglingValency base.gaugedData v = nonDanglingValency data u := by
  obtain ⟨w, hw, hwv⟩ := exists_step_vertex base.secondRelabeling
    (middleData_connected base hValid) v
  obtain ⟨u, hu, huw⟩ := exists_step_vertex base.firstRelabeling hValid.1 w
  exact ⟨u, hu.trans hw, hwv.trans huw⟩

/-- **`HasPathEnds` survives the two branch gauges.** -/
theorem hasPathEnds_gaugedData (hValid : data.Valid) (hEnds : HasPathEnds data) :
    HasPathEnds base.gaugedData :=
  StableGraphIncidence.hasPathEnds_sheetRelabel base.secondRelabeling
    (middleData_connected base hValid)
    (StableGraphIncidence.hasPathEnds_sheetRelabel base.firstRelabeling hValid.1 hEnds)


/-! ### A path end of the gauged datum transports to the candidate -/

variable (hValid : data.Valid)

/-- **The anchor half.**  A surviving occurrence of the gauged datum at the
anchor block is `e_alpha`, `e_beta`, `e_gamma` or `e_delta`.  The first three
already end at a trivalent new vertex (`A_u` for `e_alpha`, `A_v` for `e_beta`
and `e_gamma`); `e_delta` ends at the **divalent** `A'`, where its row
continues into the second occurrence `e'` above `t_1`
(`newSourceEdge_stablePath_eq_retained`) and stops at the trivalent `A_u`.
This is the one structural difference from the Type III anchor of
`NonTrivalentValencyThreeExit`, where both new anchor vertices are
trivalent. -/
theorem exists_isPathEnd_anchor {h : NonDanglingEdge base.gaugedData}
    (hInc : Incident base.gaugedData h.1
      (base.gaugedData.sourceEndpoint wall anchor.1)) :
    ∃ (first : NonDanglingEdge (validCandidate base hValid).datum)
      (vertex : (validCandidate base hValid).datum.SourceVertex),
      first.stablePath = (ResolutionAwayFromWall.retainedEdge
          (validCandidate base hValid) (base.gaugedData_valid hValid).1 h).stablePath ∧
        IsPathEnd (validCandidate base hValid).datum first.1 vertex := by
  classical
  obtain ⟨hMem, hRel⟩ := (incident_sourceEndpoint_wall_iff base anchor.1 h.1).mp hInc
  have hWall : (data.vertexPartition wall).Rel anchor.1 h.1.1.2 :=
    (gauged_rel_iff base).mp hRel
  cases hSide : base.rightAssignment h.1.1.1 with
  | false =>
    have hTarget : h.1.1.1 = directionEdge star base.alphaLabel :=
      (base.rightAssignment_eq_false_iff h.1.1.1).mp hSide
    have hEq : h.1 = base.gaugedData.sourceEdge
        (directionEdge star base.alphaLabel) h.1.1.2 :=
      oldSourceEdge_eq base (sheet := h.1.1.2) hTarget rfl
    have hAlphaMem : h.1.1.2 ∈ base.alphaBlock := by
      by_contra hNot
      refine h.2 ?_
      rw [hEq]
      exact gauged_alpha_isDangling_of_not_mem base hValid hWall hNot
    refine ⟨ResolutionAwayFromWall.retainedEdge (validCandidate base hValid)
        (base.gaugedData_valid hValid).1 h,
      endpointVertex base hValid false h.1.1.2, rfl, ?_, ?_⟩
    · show Incident (validCandidate base hValid).datum
        ((validCandidate base hValid).oldSourceEdge h.1) _
      nth_rewrite 1 [hEq]
      exact retainedEdge_incident base hValid _
        (directionEdge_mem_incidentEdges star base.alphaLabel) false
        base.rightAssignment_alpha h.1.1.2
    · rw [← endpointVertex_eq base hValid false base.hubSheet_wall
        ((left_rel_hub_iff base).mpr hAlphaMem),
        nonDanglingValency_hubLeft base hValid]
      omega
  | true =>
    rcases target_cases_of_rightAssignment_true base hMem hSide with hTarget | hTarget
    · -- the doubled direction: `e_delta` or `e_gamma`
      have hEqDelta : ∀ sheet : Fin degree,
          (base.gaugedData.edgePartition
            (Prescribed.doubledEdge base.source)).Rel sheet h.1.1.2 →
          h.1 = base.gaugedData.sourceEdge
            (Prescribed.doubledEdge base.source) sheet :=
        fun sheet hs ↦ oldSourceEdge_eq base (sheet := sheet) hTarget hs
      by_cases hDelta : h.1.1.2 ∈ base.newDeltaBlock
      · -- `e_delta`: the end at `A'` is divalent, so use `e'` at `A_u`
        have hIsDelta : h.1 = deltaOccurrence base :=
          hEqDelta base.deltaRepr
            (doubled_rel_of_mem_newDelta base base.deltaRepr_mem hDelta)
        refine ⟨⟨bridgeEdge base hValid base.deltaRepr,
            bridgeEdge_delta_survives base hValid⟩,
          endpointVertex base hValid false base.deltaRepr, ?_, ?_, ?_⟩
        · refine Eq.trans (newSourceEdge_stablePath_eq_retained base hValid) ?_
          exact congrArg (fun e : NonDanglingEdge base.gaugedData ↦
            (ResolutionAwayFromWall.retainedEdge (validCandidate base hValid)
              (base.gaugedData_valid hValid).1 e).stablePath)
            (Subtype.ext hIsDelta.symm)
        · exact bridgeEdge_incident base hValid false base.deltaRepr
        · rw [← endpointVertex_false_hub_eq_deltaRepr base hValid,
            nonDanglingValency_hubLeft base hValid]
          omega
      · -- `e_gamma`: the end at `A_v` is trivalent
        have hGamma : h.1.1.2 ∈ base.newGammaBlock := by
          by_contra hNot
          refine h.2 ?_
          rw [hEqDelta h.1.1.2 rfl]
          exact gauged_doubled_isDangling_of_not_mem base hValid hWall hDelta hNot
        refine ⟨ResolutionAwayFromWall.retainedEdge (validCandidate base hValid)
            (base.gaugedData_valid hValid).1 h,
          endpointVertex base hValid true h.1.1.2, rfl, ?_, ?_⟩
        · show Incident (validCandidate base hValid).datum
            ((validCandidate base hValid).oldSourceEdge h.1) _
          nth_rewrite 1 [hEqDelta h.1.1.2 rfl]
          refine retainedEdge_incident base hValid _
            (Prescribed.doubledEdge_mem_incidentEdges base.source) true ?_ h.1.1.2
          rw [← hTarget]
          exact hSide
        · rw [← endpointVertex_eq base hValid true base.hubSheet_wall
            (base.right_rel_hub_of_mem (Finset.mem_sdiff.mpr
              ⟨base.newGammaBlock_subset_whole hGamma,
                base.newGammaBlock_not_mem_delta hGamma⟩)),
            nonDanglingValency_hubRight base hValid]
          omega
    · -- `e_beta`: the end at `A_v` is trivalent
      have hEq : h.1 = base.gaugedData.sourceEdge
          (directionEdge star base.betaLabel) h.1.1.2 :=
        oldSourceEdge_eq base (sheet := h.1.1.2) hTarget rfl
      have hBeta : h.1.1.2 ∈ base.newBetaBlock := by
        by_contra hNot
        refine h.2 ?_
        rw [hEq]
        exact gauged_beta_isDangling_of_not_mem base hValid hWall hNot
      refine ⟨ResolutionAwayFromWall.retainedEdge (validCandidate base hValid)
          (base.gaugedData_valid hValid).1 h,
        endpointVertex base hValid true h.1.1.2, rfl, ?_, ?_⟩
      · show Incident (validCandidate base hValid).datum
          ((validCandidate base hValid).oldSourceEdge h.1) _
        nth_rewrite 1 [hEq]
        refine retainedEdge_incident base hValid _
          (directionEdge_mem_incidentEdges star base.betaLabel) true ?_ h.1.1.2
        rw [← hTarget]
        exact hSide
      · rw [← endpointVertex_eq base hValid true base.hubSheet_wall
          (base.right_rel_hub_of_mem (base.newBetaBlock_subset_sdiff hBeta)),
          nonDanglingValency_hubRight base hValid]
        omega


/-- **The ordinary-block half.**  Every survivor of a wall block other than the
anchor reaches the trivalent end `B_v` along its own row
(`NonTrivalentValencyThreeSimpleRows.exists_trivalentEndEdge`), and `B_v`
carries exactly the block's own surviving valency. -/
theorem exists_isPathEnd_ordinary {h : NonDanglingEdge base.gaugedData}
    {x : Fin degree} (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hInc : Incident base.gaugedData h.1 (base.gaugedData.sourceEndpoint wall x))
    (hNd : nonDanglingValency base.gaugedData
      (base.gaugedData.sourceEndpoint wall x) ≠ 2) :
    ∃ (first : NonDanglingEdge (validCandidate base hValid).datum)
      (vertex : (validCandidate base hValid).datum.SourceVertex),
      first.stablePath = (ResolutionAwayFromWall.retainedEdge
          (validCandidate base hValid) (base.gaugedData_valid hValid).1 h).stablePath ∧
        IsPathEnd (validCandidate base hValid).datum first.1 vertex := by
  classical
  have hOld : h.1 ∈ ordinaryStar base x (base.rightAssignment h.1.1.1) :=
    (mem_ordinaryStar base h.1).mpr ⟨⟨h.2, hInc⟩, rfl⟩
  obtain ⟨e, hIncE, hRowE, -⟩ := exists_trivalentEndEdge base hValid hX hOld
  refine ⟨e, endpointVertex base hValid true x, hRowE, hIncE, ?_⟩
  rw [nonDanglingValency_endpointVertex_true_ordinary base hValid hX]
  exact hNd

/-- **A path end of the gauged datum transports to a path end of the outgoing
Type I / Type II candidate**, on the retained row of the same occurrence. -/
theorem exists_isPathEnd_of_wall_end {h : NonDanglingEdge base.gaugedData}
    {w : base.gaugedData.SourceVertex} (hInc : Incident base.gaugedData h.1 w)
    (hNd : nonDanglingValency base.gaugedData w ≠ 2) :
    ∃ (first : NonDanglingEdge (validCandidate base hValid).datum)
      (vertex : (validCandidate base hValid).datum.SourceVertex),
      first.stablePath = (ResolutionAwayFromWall.retainedEdge
          (validCandidate base hValid) (base.gaugedData_valid hValid).1 h).stablePath ∧
        IsPathEnd (validCandidate base hValid).datum first.1 vertex := by
  classical
  by_cases hAt : w.1.1 = wall
  · have hVertex : base.gaugedData.sourceEndpoint wall w.1.2 = w :=
      (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hAt.symm, rfl⟩
    by_cases hAnchor : (data.vertexPartition wall).Rel anchor.1 w.1.2
    · have hwEq : base.gaugedData.sourceEndpoint wall anchor.1 = w :=
        (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr
          ⟨hAt.symm, (gauged_rel_iff base).mpr hAnchor⟩
      refine exists_isPathEnd_anchor base hValid ?_
      rw [hwEq]
      exact hInc
    · refine exists_isPathEnd_ordinary base hValid hAnchor ?_ ?_
      · rw [hVertex]; exact hInc
      · rw [hVertex]; exact hNd
  · refine ⟨ResolutionAwayFromWall.retainedEdge (validCandidate base hValid)
        (base.gaugedData_valid hValid).1 h,
      ResolutionAwayFromWall.retainedVertex (validCandidate base hValid) w, rfl, ?_, ?_⟩
    · exact (ResolutionAwayFromWall.incident_oldSourceEdge_iff
        (validCandidate base hValid) w hAt h.1).mpr hInc
    · rw [ResolutionAwayFromWall.nonDanglingValency_retainedVertex
        (validCandidate base hValid) (base.gaugedData_valid hValid)
        (candidate_sourceGenus base hValid) w hAt]
      exact hNd

/-! ### `HasPathEnds` of the outgoing candidate -/

/-- **`HasPathEnds` of the outgoing candidate reduces to the retained rows.**
Through `NonTrivalentValencyThreeSimpleRowEquiv.rowEquiv` every stable row of
the candidate is either the bridge row `h_1` -- whose occurrence has both ends
at the trivalent `A_u` and `A_v`, so it is a path end outright -- or the
retained row of a stable row of the gauged wall datum. -/
theorem hasPathEnds_of_retainedRowEnds
    (hRetained : ∀ r : StablePath base.gaugedData,
      ∃ (first : NonDanglingEdge (validCandidate base hValid).datum)
        (vertex : (validCandidate base hValid).datum.SourceVertex),
        first.stablePath = retainedRow base hValid r ∧
          IsPathEnd (validCandidate base hValid).datum first.1 vertex) :
    HasPathEnds (validCandidate base hValid).datum := by
  classical
  intro e
  have hBack := (rowEquiv base hValid).symm_apply_apply e.stablePath
  cases hCase : rowEquiv base hValid e.stablePath with
  | none =>
    rw [hCase] at hBack
    have hRow : e.stablePath = bridgeRow base hValid := hBack.symm
    refine ⟨⟨bridgeEdge base hValid base.hubSheet,
        bridgeEdge_hub_survives base hValid⟩,
      endpointVertex base hValid false base.hubSheet, hRow.symm, ?_, ?_⟩
    · exact bridgeEdge_incident base hValid false base.hubSheet
    · rw [nonDanglingValency_hubLeft base hValid]
      omega
  | some r =>
    rw [hCase] at hBack
    have hRow : e.stablePath = retainedRow base hValid r := hBack.symm
    obtain ⟨first, vertex, hFirst, hEnd⟩ := hRetained r
    exact ⟨first, vertex, hFirst.trans hRow.symm, hEnd⟩

/-- **`HasPathEnds` of the outgoing Type I / Type II candidate**, from
`HasPathEnds` of the gauged wall datum alone. -/
theorem hasPathEnds_candidate (hEnds : HasPathEnds base.gaugedData) :
    HasPathEnds (validCandidate base hValid).datum := by
  classical
  refine hasPathEnds_of_retainedRowEnds base hValid ?_
  intro r
  obtain ⟨g, hg⟩ := Quot.exists_rep r
  have hgr : NonDanglingEdge.stablePath g = r := hg
  obtain ⟨wallEdge, w, hRow, hInc, hNd⟩ := hEnds g
  obtain ⟨first, vertex, hFirst, hEnd⟩ :=
    exists_isPathEnd_of_wall_end base hValid hInc hNd
  refine ⟨first, vertex, ?_, hEnd⟩
  rw [hFirst, ← retainedRow_mk base hValid wallEdge, hRow, hgr]


/-! ### Trivalence of the outgoing candidate -/

/-- Every source vertex of the candidate over one side of the new target edge
is the endpoint vertex of its own sheet. -/
theorem eq_endpointVertex (sideValue : Bool)
    (v : (validCandidate base hValid).datum.SourceVertex)
    (hv : v.1.1 = (if sideValue then freshVertex target else oldVertex target wall)) :
    endpointVertex base hValid sideValue v.1.2 = v :=
  ((validCandidate base hValid).datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨hv.symm, rfl⟩

/-- **The outgoing Type I / Type II candidate is trivalent.**  Off the wall the
gauged datum's trivalence descends through `ResolutionAwayFromWall`; at the
anchor the exact stars of `NonTrivalentValencyThreeSimpleRows` give
`nd(A_u) = 3`, `nd(A') = 2`, `nd(A_v) = 3` and a fine class of `A` outside
`A_u` carries at most one survivor; at an ordinary block the census gives
`nd(B_u) <= 2` on the divalent side and `nd(B_v) = nd(B)` on the trivalent
side. -/
theorem candidate_trivalent
    (hAway : ∀ u : base.gaugedData.SourceVertex, u.1.1 ≠ wall →
      nonDanglingValency base.gaugedData u ≤ 3)
    (hOrdinary : ∀ y : Fin degree, ¬ (data.vertexPartition wall).Rel anchor.1 y →
      nonDanglingValency base.gaugedData
        (base.gaugedData.sourceEndpoint wall y) ≤ 3)
    (v : (validCandidate base hValid).datum.SourceVertex) :
    nonDanglingValency (validCandidate base hValid).datum v ≤ 3 := by
  classical
  have hWall : ∀ sideValue : Bool,
      v.1.1 = (if sideValue then freshVertex target else oldVertex target wall) →
      nonDanglingValency (validCandidate base hValid).datum v ≤ 3 := by
    intro sideValue hv
    rw [← eq_endpointVertex base hValid sideValue v hv]
    by_cases hAnchor : (data.vertexPartition wall).Rel anchor.1 v.1.2
    · cases sideValue with
      | true =>
        by_cases hDelta : v.1.2 ∈ base.newDeltaBlock
        · rw [← endpointVertex_eq base hValid true base.deltaRepr_wall
              (base.right_rel_delta_of_mem hDelta),
            nonDanglingValency_deltaRight base hValid]
          omega
        · rw [← endpointVertex_eq base hValid true base.hubSheet_wall
              (base.right_rel_hub_of_mem (Finset.mem_sdiff.mpr
                ⟨mem_wholeBlock_of_wall_rel base hAnchor, hDelta⟩)),
            nonDanglingValency_hubRight base hValid]
      | false =>
        by_cases hAlpha : v.1.2 ∈ base.alphaBlock
        · rw [← endpointVertex_eq base hValid false base.hubSheet_wall
              ((left_rel_hub_iff base).mpr hAlpha),
            nonDanglingValency_hubLeft base hValid]
        · have hCard := Finset.card_le_card
            (nonDanglingIncident_left_singleton_subset base hValid hAnchor hAlpha)
          rw [card_nonDanglingIncident, Finset.card_singleton] at hCard
          omega
    · cases sideValue with
      | false =>
        have hSub : nonDanglingIncident (validCandidate base hValid).datum
            (endpointVertex base hValid false v.1.2) ⊆
              {(validCandidate base hValid).oldSourceEdge
                  (alphaOccurrenceAt base v.1.2),
                (validCandidate base hValid).newSourceEdge v.1.2} := by
          intro e he
          rcases (mem_nonDanglingIncident_endpointVertex_false_ordinary base hValid
            hAnchor e).mp he with ⟨rfl, -⟩ | ⟨rfl, -⟩
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        have hCard := Finset.card_le_card hSub
        rw [card_nonDanglingIncident] at hCard
        have hPair := Finset.card_insert_le
          ((validCandidate base hValid).oldSourceEdge (alphaOccurrenceAt base v.1.2))
          ({(validCandidate base hValid).newSourceEdge v.1.2} :
            Finset (validCandidate base hValid).datum.SourceEdge)
        rw [Finset.card_singleton] at hPair
        omega
      | true =>
        rw [nonDanglingValency_endpointVertex_true_ordinary base hValid hAnchor]
        exact hOrdinary v.1.2 hAnchor
  rcases hcase : (v.1.1 : TargetExpansion.Vertex target) with place | u
  · by_cases hIsWall : place = wall
    · exact hWall false (by rw [hcase, hIsWall]; rfl)
    · obtain ⟨old, hOld, hRet⟩ := ResolutionAwayFromWall.exists_retainedVertex_of_target
        (validCandidate base hValid) v place hIsWall hcase
      rw [← hRet, ResolutionAwayFromWall.nonDanglingValency_retainedVertex
        (validCandidate base hValid) (base.gaugedData_valid hValid)
        (candidate_sourceGenus base hValid) old (by rw [hOld]; exact hIsWall)]
      exact hAway old (by rw [hOld]; exact hIsWall)
  · exact hWall true (by rw [hcase]; cases u; rfl)

end

end Transport

section Exit

open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleRowDictionary
  (matrix_candidateLabelling gaugeStablePath gaugedLabelling_row MinorIdentity)

noncomputable section

variable {targetIn : CFGraph} {deg : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (cover : GluingDatum targetIn deg)
  (fd : FullDimensionalSourcePresentation cover coordinate)
  {a b : targetIn.V} {contracted : targetIn.edges}
  (hc : (contracted : targetIn.V × targetIn.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges targetIn a b = 1)
  (hForest : ContractionForest cover a b contracted)
  (hNoReturn : NoContractedReturn cover contracted)
  (coordinates : coordinate → ℚ) (facet : coordinate)
  (hRows : ∀ row, row ≠ facet →
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates row ≠ 0)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
  (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
    0 < coordinates column)
  (hFacetZero :
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates facet = 0)
  {wallStar : ThreeStar (contract targetIn hab hOne) ⟨a, hab⟩}
  {anchorBlk : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩}
  (simpleBase : SimpleBase (contractDatum cover hc hab hOne) wallStar anchorBlk)
  (hValid : (contractDatum cover hc hab hOne).Valid)

/-! ### The outgoing honest labelling on the incoming chart -/

/-- **The outgoing honest labelling.**  The two independent charts of
`NonTrivalentValencyTwoExit` applied to the Type I / Type II candidate labelling
over the **gauged** wall datum's
square labelling: the bridge row `h_1` goes into the vanishing row `facet`, the
new target occurrence `t_1` into the vanishing column. -/
def outLabelling :
    StableLengthMatrixLabelling (validCandidate simpleBase hValid).datum coordinate :=
  NonTrivalentValencyTwoExit.reindexLabelling₂
    (NonTrivalentValencyTwoExit.rowChart cover fd facet (contracted := contracted))
    (NonTrivalentValencyTwoExit.colChart cover fd (contracted := contracted))
    (labelling simpleBase hValid
      (gaugedLabelling simpleBase hValid
        (NonTrivalentValencyTwoExit.wallLab cover fd hc hab hOne hForest hNoReturn
          coordinates facet hRows hZeroCoord hPosCoord hFacetZero)))

/-- **The common minor, entry by entry.**  In a retained row and a retained
column the outgoing matrix is the incoming matrix's own entry.  The gauge is
crossed by `gaugedLabelling_matrix` / `gaugedLabelling_row`. -/
theorem matrix_outLabelling_eq_incoming (i j : coordinate) (hi : i ≠ facet)
    (hj : j ≠ fd.labelling.targetEdge.symm contracted) :
    GluingDatum.LengthMatrixPresentation.matrix
        (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
          hZeroCoord hPosCoord hFacetZero simpleBase hValid).presentation i j =
      GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation i j := by
  classical
  have hd : Equiv.swap (fd.labelling.targetEdge.symm contracted) facet i ≠
      fd.labelling.targetEdge.symm contracted := by
    intro h
    apply hi
    have h2 := congrArg (Equiv.swap (fd.labelling.targetEdge.symm contracted) facet) h
    rwa [Equiv.swap_apply_self, Equiv.swap_apply_left] at h2
  set d : {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted} :=
    ⟨Equiv.swap (fd.labelling.targetEdge.symm contracted) facet i, hd⟩ with hdDef
  set p := (NonTrivalentValencyTwoExit.wallLab cover fd hc hab hOne hForest hNoReturn
    coordinates facet hRows hZeroCoord hPosCoord hFacetZero).row.symm d with hpDef
  have hrow : (NonTrivalentValencyTwoExit.wallLab cover fd hc hab hOne hForest hNoReturn
      coordinates facet hRows hZeroCoord hPosCoord hFacetZero).row p = d :=
    Equiv.apply_symm_apply _ _
  have hi' : NonTrivalentValencyTwoExit.rowChart cover fd facet (contracted := contracted)
      (some d) = i := by
    rw [NonTrivalentValencyTwoExit.rowChart_some]
    exact Equiv.swap_apply_self _ _ i
  have hMid := NonTrivalentValencyTwoExit.matrix_reindexLabelling₂
    (NonTrivalentValencyTwoExit.rowChart cover fd facet (contracted := contracted))
    (NonTrivalentValencyTwoExit.colChart cover fd (contracted := contracted))
    (labelling simpleBase hValid
      (gaugedLabelling simpleBase hValid
        (NonTrivalentValencyTwoExit.wallLab cover fd hc hab hOne hForest hNoReturn
          coordinates facet hRows hZeroCoord hPosCoord hFacetZero))) (some d) (some ⟨j, hj⟩)
  rw [hi'] at hMid
  have hPath : fd.labelling.row (incomingRow cover fd hc hab hOne
      (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne hForest)
      hForest p) = i := by
    have hval := NonTrivalentValencyTwoExit.wallLab_row_val cover fd hc hab hOne hForest
      hNoReturn coordinates facet hRows hZeroCoord hPosCoord hFacetZero p
    rw [hrow] at hval
    refine (Equiv.swap facet (fd.labelling.targetEdge.symm contracted)).injective ?_
    rw [← hval, Equiv.swap_comm]
  refine Eq.trans hMid ?_
  rw [← hrow]
  have hCand := matrix_candidateLabelling simpleBase hValid
    (gaugedLabelling simpleBase hValid
      (NonTrivalentValencyTwoExit.wallLab cover fd hc hab hOne hForest hNoReturn
        coordinates facet hRows hZeroCoord hPosCoord hFacetZero))
    (gaugeStablePath simpleBase hValid p) ⟨j, hj⟩
  rw [gaugedLabelling_row simpleBase hValid
    (NonTrivalentValencyTwoExit.wallLab cover fd hc hab hOne hForest hNoReturn
      coordinates facet hRows hZeroCoord hPosCoord hFacetZero) p] at hCand
  refine Eq.trans hCand ?_
  rw [gaugedLabelling_matrix simpleBase hValid]
  refine Eq.trans (matrix_wallLabelling cover fd hc hab hOne
    (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne hForest)
    hForest hNoReturn coordinates facet hRows hZeroCoord hPosCoord hFacetZero p ⟨j, hj⟩) ?_
  rw [hPath]

/-! ### The bridge row of the outgoing matrix -/

/-- **The bridge row of the candidate occupies the vanishing row of the
incoming chart.** -/
theorem outLabelling_row_bridge :
    (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
        hZeroCoord hPosCoord hFacetZero simpleBase hValid).row
      (bridgeRow simpleBase hValid) = facet := by
  show (NonTrivalentValencyTwoExit.rowChart cover fd facet (contracted := contracted))
      ((labelling simpleBase hValid
        (gaugedLabelling simpleBase hValid
          (NonTrivalentValencyTwoExit.wallLab cover fd hc hab hOne hForest hNoReturn
            coordinates facet hRows hZeroCoord hPosCoord hFacetZero))).row
        (bridgeRow simpleBase hValid)) = facet
  rw [labelling_row_bridge simpleBase hValid]
  rfl

theorem outLabelling_row_symm_facet :
    (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
        hZeroCoord hPosCoord hFacetZero simpleBase hValid).row.symm facet =
      bridgeRow simpleBase hValid :=
  (Equiv.symm_apply_eq _).mpr
    (outLabelling_row_bridge cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
      hZeroCoord hPosCoord hFacetZero simpleBase hValid).symm

/-- **A retained row keeps the incoming chart coordinate of its own incoming
row.**  This is the row half of the `InteriorGraphTracking.Tracks.row_map`
obligation at a Type I / Type II change: the two branch gauges do not move a
stable row (`gaugedLabelling_row`), and the row chart's transposition cancels
exactly the one `StablePathFacetContraction.wallRowIndex` builds in. -/
theorem outLabelling_row_retained (p : StablePath (contractDatum cover hc hab hOne)) :
    (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
        hZeroCoord hPosCoord hFacetZero simpleBase hValid).row
      (retainedRow simpleBase hValid (gaugeStablePath simpleBase hValid p)) =
      fd.labelling.row (incomingRow cover fd hc hab hOne
        (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne hForest)
        hForest p) := by
  show (NonTrivalentValencyTwoExit.rowChart cover fd facet (contracted := contracted))
      ((labelling simpleBase hValid
        (gaugedLabelling simpleBase hValid
          (NonTrivalentValencyTwoExit.wallLab cover fd hc hab hOne hForest hNoReturn
            coordinates facet hRows hZeroCoord hPosCoord hFacetZero))).row
        (retainedRow simpleBase hValid (gaugeStablePath simpleBase hValid p))) = _
  rw [labelling_row_retained simpleBase hValid _ (gaugeStablePath simpleBase hValid p),
    gaugedLabelling_row simpleBase hValid
      (NonTrivalentValencyTwoExit.wallLab cover fd hc hab hOne hForest hNoReturn
        coordinates facet hRows hZeroCoord hPosCoord hFacetZero) p,
    NonTrivalentValencyTwoExit.rowChart_some,
    NonTrivalentValencyTwoExit.wallLab_row_val cover fd hc hab hOne hForest hNoReturn
      coordinates facet hRows hZeroCoord hPosCoord hFacetZero p,
    Equiv.swap_comm facet (fd.labelling.targetEdge.symm contracted)]
  exact Equiv.swap_apply_self _ _ _

/-- The only surviving occurrence of the bridge row lies over the new target
occurrence: `e_1` is alone in its stable class because **both** of its ends
`A_u`, `A_v` are trivalent. -/
theorem occurrences_bridgeRow_of_ne (t : (TargetExpansion.graph (contract targetIn hab hOne)
      ⟨a, hab⟩ (validCandidate simpleBase hValid).right).edges)
    (ht : t ≠ TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
      (validCandidate simpleBase hValid).right none) :
    StableSourceMatrix.occurrences (validCandidate simpleBase hValid).datum
      (bridgeRow simpleBase hValid) t = ∅ := by
  classical
  refine Finset.eq_empty_iff_forall_notMem.mpr ?_
  intro e he
  obtain ⟨⟨hSurv, hRow⟩, hTarget⟩ := (StableSourceMatrix.mem_occurrences _ t e).mp he
  have hEq := bridgeEdge_isolated simpleBase hValid ⟨e, hSurv⟩ hRow
  have hEq' : e = bridgeEdge simpleBase hValid simpleBase.hubSheet := hEq
  apply ht
  rw [← hTarget, hEq']
  exact BalancedGlobal.Candidate.newSourceEdge_target _ _

theorem occurrences_bridgeRow_new :
    StableSourceMatrix.occurrences (validCandidate simpleBase hValid).datum
        (bridgeRow simpleBase hValid)
        (TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
          (validCandidate simpleBase hValid).right none) =
      {bridgeEdge simpleBase hValid simpleBase.hubSheet} := by
  classical
  refine Finset.Subset.antisymm ?_ ?_
  · intro e he
    obtain ⟨⟨hSurv, hRow⟩, -⟩ := (StableSourceMatrix.mem_occurrences _ _ e).mp he
    exact Finset.mem_singleton.mpr (bridgeEdge_isolated simpleBase hValid ⟨e, hSurv⟩ hRow)
  · intro e he
    rw [Finset.mem_singleton] at he
    subst he
    refine (StableSourceMatrix.mem_occurrences _ _ _).mpr ⟨⟨?_, rfl⟩, ?_⟩
    · exact bridgeEdge_hub_survives simpleBase hValid
    · exact BalancedGlobal.Candidate.newSourceEdge_target _ _

theorem matrix_outLabelling_facet_eq_zero (j : coordinate)
    (hj : j ≠ fd.labelling.targetEdge.symm contracted) :
    GluingDatum.LengthMatrixPresentation.matrix
        (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
          hZeroCoord hPosCoord hFacetZero simpleBase hValid).presentation facet j = 0 := by
  classical
  rw [StableSourceMatrix.labelling_matrix_eq, outLabelling_row_symm_facet]
  have hTarget : (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
        hZeroCoord hPosCoord hFacetZero simpleBase hValid).targetEdge j ≠
      TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
        (validCandidate simpleBase hValid).right none := by
    have hSymm : (NonTrivalentValencyTwoExit.colChart cover fd (contracted := contracted)).symm
        j = some ⟨j, hj⟩ := Equiv.optionSubtypeNe_symm_of_ne hj
    show TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
        (validCandidate simpleBase hValid).right
        (Option.map _ ((NonTrivalentValencyTwoExit.colChart cover fd
          (contracted := contracted)).symm j)) ≠ _
    intro hBad
    have hNone := (TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
      (validCandidate simpleBase hValid).right).injective hBad
    rw [hSymm] at hNone
    simp at hNone
  unfold StableSourceMatrix.matrix
  rw [occurrences_bridgeRow_of_ne cover hc hab hOne simpleBase hValid _ hTarget,
    Finset.sum_empty]

theorem matrix_outLabelling_corner_pos :
    0 < GluingDatum.LengthMatrixPresentation.matrix
        (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
          hZeroCoord hPosCoord hFacetZero simpleBase hValid).presentation facet
        (fd.labelling.targetEdge.symm contracted) := by
  classical
  rw [StableSourceMatrix.labelling_matrix_eq, outLabelling_row_symm_facet]
  have hSymm : (NonTrivalentValencyTwoExit.colChart cover fd (contracted := contracted)).symm
      (fd.labelling.targetEdge.symm contracted) = none :=
    Equiv.optionSubtypeNe_symm_self _
  have hTarget : (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
        hZeroCoord hPosCoord hFacetZero simpleBase hValid).targetEdge
        (fd.labelling.targetEdge.symm contracted) =
      TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
        (validCandidate simpleBase hValid).right none := by
    show TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
        (validCandidate simpleBase hValid).right
        (Option.map _ ((NonTrivalentValencyTwoExit.colChart cover fd
          (contracted := contracted)).symm (fd.labelling.targetEdge.symm contracted))) = _
    rw [hSymm]
    rfl
  rw [hTarget]
  unfold StableSourceMatrix.matrix
  rw [occurrences_bridgeRow_new cover hc hab hOne simpleBase hValid, Finset.sum_singleton]
  exact div_pos one_pos
    (by exact_mod_cast (validCandidate simpleBase hValid).datum.sourceEdgeIndex_pos _)

/-! ### The common minor and nonsingularity -/

/-- **The common minor.**  The outgoing honest matrix agrees with the incoming
one in every row off the contracted column. -/
theorem agreeOffColumn_outLabelling :
    AgreeOffColumn (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation)
      (GluingDatum.LengthMatrixPresentation.matrix
        (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
          hZeroCoord hPosCoord hFacetZero simpleBase hValid).presentation)
      (fd.labelling.targetEdge.symm contracted) := by
  intro i j hj
  by_cases hi : i = facet
  · rw [hi]
    rw [matrix_outLabelling_facet_eq_zero cover fd hc hab hOne hForest hNoReturn coordinates
      facet hRows hZeroCoord hPosCoord hFacetZero simpleBase hValid j hj]
    exact NonTrivalentValencyTwoExit.incoming_facet_eq_zero cover fd coordinates facet
      hZeroCoord hPosCoord hFacetZero j hj
  · exact (matrix_outLabelling_eq_incoming cover fd hc hab hOne hForest hNoReturn coordinates
      facet hRows hZeroCoord hPosCoord hFacetZero simpleBase hValid i j hi hj).symm

/-- **Nonsingularity of the outgoing matrix**, by the common-minor expansion
along the bridge row (`NonTrivalentLinkMatrix.det_ne_zero`). -/
theorem det_outLabelling_ne_zero :
    (GluingDatum.LengthMatrixPresentation.matrix
      (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
        hZeroCoord hPosCoord hFacetZero simpleBase hValid).presentation).det ≠ 0 :=
  NonTrivalentLinkMatrix.det_ne_zero
    (agreeOffColumn_outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet
      hRows hZeroCoord hPosCoord hFacetZero simpleBase hValid)
    (fun j hj ↦ NonTrivalentValencyTwoExit.incoming_facet_eq_zero cover fd coordinates facet
      hZeroCoord hPosCoord hFacetZero j hj)
    (fun j hj ↦ matrix_outLabelling_facet_eq_zero cover fd hc hab hOne hForest hNoReturn
      coordinates facet hRows hZeroCoord hPosCoord hFacetZero simpleBase hValid j hj)
    fd.det_ne_zero
    (matrix_outLabelling_corner_pos cover fd hc hab hOne hForest hNoReturn coordinates facet
      hRows hZeroCoord hPosCoord hFacetZero simpleBase hValid).ne'


/-! ### The outgoing target: connected, genus zero, and the same edge count -/

include fd in
theorem outgoing_targetConnected :
    graph_connected (TargetExpansion.graph (contract targetIn hab hOne) ⟨a, hab⟩
      (validCandidate simpleBase hValid).right) :=
  TargetExpansion.graph_connected (contract targetIn hab hOne) ⟨a, hab⟩ _
    (NonTrivalentUniqueFourValent.wall_target_connected cover fd hab hOne)

include fd in
theorem outgoing_targetGenus :
    genus (TargetExpansion.graph (contract targetIn hab hOne) ⟨a, hab⟩
      (validCandidate simpleBase hValid).right) = 0 :=
  (TargetExpansion.graph_genus (contract targetIn hab hOne) ⟨a, hab⟩ _).trans
    (NonTrivalentUniqueFourValent.wall_target_genus cover fd hab hOne)

/-- **The outgoing target has as many edges as the incoming one**: one target
occurrence contracts and one is regrown. -/
theorem outgoing_targetEdgeCard :
    (TargetExpansion.graph (contract targetIn hab hOne) ⟨a, hab⟩
      (validCandidate simpleBase hValid).right).edges.card =
      targetIn.edges.card :=
  (TargetExpansion.graph_edge_card (contract targetIn hab hOne) ⟨a, hab⟩ _).trans
    (WallDegeneration.edge_card_contract hab hOne).symm

/-! ### Trivalence and path ends of the outgoing candidate at the wall -/

include fd hForest hValid in
/-- **The gauged wall datum is trivalent away from the merged vertex.**  The
two branch gauges move no surviving valency (`exists_ungauged_vertex`), and the
wall datum itself is trivalent there
(`NonTrivalentValencyTwoExit.wallDatum_trivalent_away`). -/
theorem gaugedData_trivalent_away (v : simpleBase.gaugedData.SourceVertex)
    (hv : v.1.1 ≠ (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)) :
    nonDanglingValency simpleBase.gaugedData v ≤ 3 := by
  obtain ⟨u, hu, hval⟩ := exists_ungauged_vertex simpleBase hValid v
  rw [hval]
  exact NonTrivalentValencyTwoExit.wallDatum_trivalent_away cover fd hc hab hOne hForest u
    (by rw [hu]; exact hv)

include fd hForest hValid in
/-- **The gauged wall datum is trivalent at every ordinary block.**  The gauge
does not change the surviving valency over the wall
(`gauged_nonDanglingValency_wall`), and the non-anchor bound at a three-valent
wall is `NonTrivalentValencyThreeExit.ordinaryBlock_trivalent`. -/
theorem gaugedData_ordinary_trivalent (y : Fin deg)
    (hy : ¬ ((contractDatum cover hc hab hOne).vertexPartition
      (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).Rel anchorBlk.1 y) :
    nonDanglingValency simpleBase.gaugedData
      (simpleBase.gaugedData.sourceEndpoint ⟨a, hab⟩ y) ≤ 3 := by
  rw [gauged_nonDanglingValency_wall simpleBase hValid y]
  exact NonTrivalentValencyThreeExit.ordinaryBlock_trivalent cover fd hc hab hOne hForest
    simpleBase.source y hy

include fd hForest in
/-- **The outgoing Type I / Type II candidate is trivalent at an actual
three-valent wall.** -/
theorem candidate_trivalent_wall
    (v : (validCandidate simpleBase hValid).datum.SourceVertex) :
    nonDanglingValency (validCandidate simpleBase hValid).datum v ≤ 3 :=
  candidate_trivalent simpleBase hValid
    (gaugedData_trivalent_away cover fd hc hab hOne hForest simpleBase hValid)
    (gaugedData_ordinary_trivalent cover fd hc hab hOne hForest simpleBase hValid) v

include fd hForest hNoReturn hZeroCoord hPosCoord hFacetZero in
/-- **`HasPathEnds` of the outgoing Type I / Type II candidate.**  The
`HasPathEnds` of the wall datum (`WallDatumPathEnds.hasPathEnds_contractDatum`),
carried across the two branch gauges
(`hasPathEnds_gaugedData`) and transported to the candidate
(`hasPathEnds_candidate`). -/
theorem hasPathEnds_wall : HasPathEnds (validCandidate simpleBase hValid).datum :=
  hasPathEnds_candidate simpleBase hValid
    (hasPathEnds_gaugedData simpleBase hValid
      (WallDatumPathEnds.hasPathEnds_contractDatum cover fd hc hab hOne hForest coordinates
        facet
        (LeafFacetNoReturn.noContractedReturnOffRow_of_noContractedReturn cover contracted
          (fd.labelling.row.symm facet) hNoReturn)
        hZeroCoord hPosCoord hFacetZero))

/-! ### The outgoing full-dimensional presentation -/

/-- **The outgoing full-dimensional source presentation at a three-valent wall,
Type I / Type II.**  Every field is derived; no receipt about the candidate
is assumed. -/
def outgoingFD :
    FullDimensionalSourcePresentation (validCandidate simpleBase hValid).datum coordinate :=
  NonTrivalentValencyTwoExit.ofTypeChange fd
    (validCandidate_datum_valid simpleBase hValid)
    (outgoing_targetConnected cover fd hc hab hOne simpleBase hValid)
    (outgoing_targetGenus cover fd hc hab hOne simpleBase hValid)
    (outgoing_targetEdgeCard cover hc hab hOne simpleBase hValid)
    ((candidate_sourceGenus_incoming simpleBase hValid).trans
      (NonTrivalentValencyTwoExit.genus_sourceGraph_contractDatum cover hc hab hOne hForest))
    (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows hZeroCoord
      hPosCoord hFacetZero simpleBase hValid)
    (det_outLabelling_ne_zero cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
      hZeroCoord hPosCoord hFacetZero simpleBase hValid)
    (candidate_trivalent_wall cover fd hc hab hOne hForest simpleBase hValid)
    (hasPathEnds_wall cover fd hc hab hOne hForest hNoReturn coordinates facet hZeroCoord
      hPosCoord hFacetZero simpleBase hValid)

@[simp] theorem outgoingFD_labelling :
    (outgoingFD cover fd hc hab hOne hForest hNoReturn coordinates facet hRows hZeroCoord
        hPosCoord hFacetZero simpleBase hValid).labelling =
      outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
        hZeroCoord hPosCoord hFacetZero simpleBase hValid := rfl


end

end Exit

/-! ## The link at a three-valent wall of the outer walk -/

section Link

open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk

noncomputable section

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)

variable {wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (simpleBase : SimpleBase (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)

/-- The outgoing presentation at the wall data of the outer walk.  No
`NoContractedReturn` and no `HasPathEnds` hypothesis: both are discharged, the
first from `wallStar`
(`NonTrivalentValencyThreeRowDictionary.noContractedReturn_of_threeStar`) and
the second by `hasPathEnds_wall`. -/
def wallOutgoingFD :
    FullDimensionalSourcePresentation (validCandidate simpleBase hValid).datum coordinate :=
  outgoingFD wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m)
    (NonTrivalentValencyThreeExit.noContractedReturn_of_valency_three m wd wallStar)
    wd.coordinates (label m.base) wd.hRows wd.hZeroCoord wd.hPosCoord wd.hFacetZero
    simpleBase hValid

/-- **The type-change link at a three-valent wall, Type I / Type II.**  Unlike
Type III, the candidate lives over the **two-fold branch gauge** of the wall
datum, so `base` is `simpleBase.gaugedData` and `baseValid` is
`SimpleBase.gaugedData_valid` -- exactly as valency four's
`PrescribedPairing.gaugedData`.  The presentation is `wallOutgoingFD` and the
common minor is `agreeOffColumn_outLabelling`.  Exactly one receipt is a
hypothesis: `tracks`, the dart dictionary of the move. -/
def typeChangeLink_of_receipts
    (tracks : Tracks (wallOutgoingFD m wd simpleBase hValid) (graph.move m) label) :
    TypeChangeLink m wd where
  base := simpleBase.gaugedData
  baseValid := simpleBase.gaugedData_valid hValid
  candidate := validCandidate simpleBase hValid
  outgoingFD := wallOutgoingFD m wd simpleBase hValid
  tracks := tracks
  agree := by
    have h := agreeOffColumn_outLabelling wd.cover wd.fullDim wd.hc wd.hab wd.hOne
      (wd.hForest m)
      (NonTrivalentValencyThreeExit.noContractedReturn_of_valency_three m wd wallStar)
      wd.coordinates (label m.base) wd.hRows wd.hZeroCoord wd.hPosCoord wd.hFacetZero
      simpleBase hValid
    rw [wd.targetEdge_symm_contracted] at h
    exact h

end

end Link


end DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleExit
