import DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitRowDictionary

/-!
# The valency-two Base II **split** exit: the outgoing presentation and the link

Source: Vargas, Part II (arXiv:2609.09109), Section 5.1 (the labelling
convention at a non-trivalent wall, and Lemma `lm:change-comb-type`: the wall
matrix is the common minor `A_{\varphi_0}`) together with Section 5.4 (Case
`{v2-nd4}`, Configuration A, base tree `T_2` = Base II, the *split* members of
Subcases `{v2-nd4-t3-k2=k3}` and `{v2-nd4-t3-k2<k3}` and their diagrams), and
Draisma--Vargas Part I (arXiv:1909.12924), Case `{w2}` of Section 6, for the
base tree.  The consumer interface is `OuterWalk.TypeChangeLink`.

This is `NonTrivalentValencyTwoBaseOneExit` ported from the Base I members to
the Base II **split** members (`NonTrivalentValencyTwoSplitCandidate`,
`NonTrivalentValencyTwoSplitGauge`), using the common minor of
`NonTrivalentValencyTwoSplitRowDictionary` and the no-return-free ingredients
`NonTrivalentValencyTwoBaseOneRowDictionary.exists_wallLabelling_two` and
`NonTrivalentValencyTwoBaseOneExit.noContractedReturnOffRow_two`, which do not
mention the outgoing candidate at all and so are reused verbatim.

## What is different from Base I and from the merge member

* The candidate lives over `NonTrivalentValencyTwoSplitGauge.splitGaugedData`,
  the **inclusion** alignment gauge `e_delta ⊆ e_alpha`, so
  `TypeChangeLink.base` is the gauged wall datum, as at Base I and at valency
  four.  `OrdinaryTrivalent`, trivalence away from the wall and `HasPathEnds` are
  transported across that gauge here.
* The anchor census is `3, 2, 3, 2`, not `3, 3` or `3, 2`: the split has **two**
  divalent pass-through vertices, `P_u = e_beta` over `u` and `P_v = e_delta`
  over `v`.  So a retained survivor of `e_beta` or of `e_delta` is *not* itself a
  path end of the outgoing candidate; the end has to be moved along the
  pass-through occurrence (to the trivalent `A_v`) resp. along the piece (to the
  trivalent `S`), which is what
  `NonTrivalentValencyTwoSplitRows.passEdge_stablePath_eq_retained` and
  `pieceEdge_stablePath_eq_retained` make possible.  This is the one place where
  the split's path-end argument is genuinely new; the ordinary blocks are the
  argument of `WallDatumPathEnds` over
  `NonTrivalentValencyTwoSplitRows.ordinaryStar`.
* The bridge row has a single occurrence (`bridgeEdge_isolated`), both of whose
  ends are trivalent, so it is a path end outright and its outgoing row vanishes
  off the contracted column.

## What is proved

* `splitGaugeVertexEquiv`, `splitGaugeEdgeEquiv`, `genus_splitGaugedData`,
  `nonDanglingValency_splitGauge`, `splitGauge_sourceEndpoint`,
  `ordinaryTrivalent_splitGauged`, `trivalent_splitGauged_away`,
  `splitGaugeNDEquiv`, `hasPathEnds_splitGauged`: the gauge transport.
* `eq_endpointVertex`, `candidate_trivalent`: **the split candidate is
  trivalent**, from the census of `NonTrivalentValencyTwoSplitRows`
  (`nd(S) = nd(A_v) = 3`,
  `nd(P_u) = nd(P_v) = 2`, `nd(B_s) = |star_s(B)| + [new survives]` at an
  ordinary block) plus `OrdinaryTrivalent` and trivalence away from the wall.
* `exists_isPathEnd_anchor`, `exists_isPathEnd_ordinary`,
  `exists_isPathEnd_of_wall_end`, `hasPathEnds_candidate`: **`HasPathEnds` of the
  split candidate** from `HasPathEnds` of the datum it lives over.
* `outgoing_targetConnected`, `outgoing_targetGenus`, `outgoing_targetEdgeCard`,
  `outgoing_sourceGenus`, `outgoing_trivalent`, `outgoing_pathEnds`,
  `det_chartLabelling_ne_zero`, `outgoingFD`: the outgoing
  `FullDimensionalSourcePresentation` on the incoming chart, every field
  produced.
* `wallOutgoingFD`, `typeChangeLink_of_receipts_split`: the same at an
  `OuterWalk.WallData`, and the split inhabitant of
  `OuterWalk.TypeChangeLink` with `tracks` the only hypothesis.
* `exists_typeChangeLink_split_of_wallData`: the actual-wall headline.
* `relabelStar` and its transport lemmas (`relabelStar_edge`,
  `relabelStar_edge_zero`, `relabelStar_edge_one`, `relabelStar_relabelStar`,
  `relabelStar_ne`, `directionSurvivors_relabelStar`,
  `directionSurvivors_relabelStar_zero`, `directionSurvivors_relabelStar_one`,
  `twoBranchDistribution_relabelStar`, `twoBranchAnchor_relabelStar`,
  `split_relabelStar`, `thickEdge_relabelStar_eq_thinEdge`,
  `thinEdge_relabelStar_eq_thickEdge`): **the mirror member is the
  same construction over the relabelled star.**  Complementary, and a warning:
  `thickEdge_of_two_le`, `thickEdge_of_le_one` and
  `thickEdge_relabelStar_eq_self_of_tripled` show that outside Configuration A
  (i.e. in Configuration B, the `3 + 1` distribution) `thickDirection` picks the
  *tripled* direction, which is intrinsic, so there `relabelStar` fixes
  `thickEdge` and the mirror trick is unavailable.  In Configuration A
  `NonTrivalentValencyTwoCandidate.Prescribed.thickDirection` is the label `0` of
  whatever `TwoStar` labelling is used
  (`NonTrivalentValencyTwoSplitGauge.thickDirection_eq_zero`), so swapping the
  two labels exchanges thick and thin, and
  `exists_typeChangeLink_splitMirror_of_wallData` is the headline over
  `relabelStar wallStar`: the member in which a class over `star.edge 1` splits.

## Hypotheses left explicit here

1. `tracks : InteriorGraphTracking.Tracks (wallOutgoingFD …) (graph.move m) label`:
   the dart-level dictionary between the candidate's stable graph and the
   Whitehead move.  Carried as a hypothesis exactly as in
   `NonTrivalentValencyTwoExit`, `NonTrivalentValencyTwoExitFree` and
   `NonTrivalentValencyTwoBaseOneExit`, so the rest of the link is proved here.
   The row-level hypothesis (H-split) and the star count are in
   `NonTrivalentValencyTwoSplitTracks` and `NonTrivalentValencyTwoSplitStarCount`.
2. The headline's remaining binders, all of them *dispatch data* about the
   incoming cover and none of them a receipt about the candidate: the incoming
   `wallStar : TwoStar …`; Configuration A
   (`hSplit : ∀ label, (directionSurvivors …).card = 2`); the four named
   survivors `alphaEdge, betaEdge` (over `wallStar.edge 0`) and
   `deltaEdge, epsilonEdge` (over `wallStar.edge 1`) with their memberships and
   the two distinctness clauses; and the paper's strict index inequality
   `k_delta < k_alpha`.  The naming is what chooses *which* class splits, i.e.
   which of Types I and II is produced, so it cannot be discharged; the strict
   inequality is exactly the case in which the Base I member does not exist
   (Part II, Subcase `{v2-nd4-t3-k2<k3}`).
3. The Part II wall metric (`wd.hRows`, `wd.hZeroCoord`, `wd.hPosCoord`,
   `wd.hFacetZero`) and the contraction data are `OuterWalk.WallData`'s own
   fields; nothing further about the incoming cover is assumed.
4. This module introduces **no new structure**; `relabelStar` is the only new
   definition and it is a relabelling of an existing one, non-vacuous by
   `relabelStar_ne` (it is never the identity) and involutive by
   `relabelStar_relabelStar`.  Inhabitation of everything consumed here is
   `NonTrivalentValencyTwoSplitCandidate.SplitSetup` with
   `NonTrivalentValencyTwoSplitGauge.splitSetup_gauged` /
   `exists_splitCandidate_of_indices` and the literal five-sheet model
   `splitModel_not_sub` / `splitModel_gauge_exists` / `splitModel_cards`; the
   headlines themselves *produce* a `SplitAnchor` from the wall data and the
   dispatch data, so no statement below is vacuous.

## Consumers

`OuterWalk.TypeChangeLink` (hence the `link` hypothesis of
`OuterWalk.coneEntry_of_reaches`) at Part II Case `{v2-nd4}`, Configuration A,
outgoing split Types I and II, and the valency-two move dispatcher, which takes
the split link as a named hypothesis.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitExit

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionCoarseFine
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.W3R1SourceProfile (survivors mem_survivors)
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitGauge
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitRows
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitRowEquiv
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitRowDictionary
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRowEquiv (OrdinaryTrivalent)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## 1.  The inclusion alignment gauge carries the local census -/

section Gauge

variable (base : GluingDatum target degree) (star : TwoStar target wall)
  (anchor : WallBlock base wall) (thickSheet thinSheet : Fin degree)

/-- The gauge on source vertices, at the gauged datum's type. -/
noncomputable def splitGaugeVertexEquiv :
    base.SourceVertex ≃
      (splitGaugedData base star anchor thickSheet thinSheet).SourceVertex :=
  (splitRelabeling base star anchor thickSheet thinSheet).sourceVertexEquiv

/-- The gauge on source occurrences, at the gauged datum's type. -/
noncomputable def splitGaugeEdgeEquiv :
    base.SourceEdge ≃ (splitGaugedData base star anchor thickSheet thinSheet).SourceEdge :=
  (splitRelabeling base star anchor thickSheet thinSheet).sourceEdgeEquiv

@[simp] theorem splitGaugeVertexEquiv_target (v : base.SourceVertex) :
    (splitGaugeVertexEquiv base star anchor thickSheet thinSheet v).1.1 = v.1.1 := rfl

@[simp] theorem splitGaugeVertexEquiv_symm_target
    (v : (splitGaugedData base star anchor thickSheet thinSheet).SourceVertex) :
    ((splitGaugeVertexEquiv base star anchor thickSheet thinSheet).symm v).1.1 = v.1.1 := rfl

/-- The gauge preserves the source genus: it is a relabelling, so both source
vertex sets and both source occurrence sets are equinumerous. -/
theorem genus_splitGaugedData :
    genus (splitGaugedData base star anchor thickSheet thinSheet).sourceGraph =
      genus base.sourceGraph := by
  classical
  have hV : Fintype.card (splitGaugedData base star anchor thickSheet thinSheet).SourceVertex =
      Fintype.card base.SourceVertex :=
    (Fintype.card_congr (splitGaugeVertexEquiv base star anchor thickSheet thinSheet)).symm
  have hE : Fintype.card (splitGaugedData base star anchor thickSheet thinSheet).SourceEdge =
      Fintype.card base.SourceEdge :=
    (Fintype.card_congr (splitGaugeEdgeEquiv base star anchor thickSheet thinSheet)).symm
  have hEdgeUp : Multiset.card base.sourceGraph.edges = Fintype.card base.SourceEdge := by
    simp [GluingDatum.sourceGraph]
  have hEdgeDown :
      Multiset.card (splitGaugedData base star anchor thickSheet thinSheet).sourceGraph.edges =
        Fintype.card (splitGaugedData base star anchor thickSheet thinSheet).SourceEdge := by
    simp [GluingDatum.sourceGraph]
  have hVertUp : Fintype.card base.sourceGraph.V = Fintype.card base.SourceVertex := rfl
  have hVertDown :
      Fintype.card (splitGaugedData base star anchor thickSheet thinSheet).sourceGraph.V =
        Fintype.card (splitGaugedData base star anchor thickSheet thinSheet).SourceVertex := rfl
  unfold genus
  rw [hEdgeUp, hEdgeDown, hVertUp, hVertDown, hV, hE]

variable (hConn : base.Connected)

include hConn in
theorem nonDanglingValency_splitGauge (v : base.SourceVertex) :
    nonDanglingValency (splitGaugedData base star anchor thickSheet thinSheet)
        (splitGaugeVertexEquiv base star anchor thickSheet thinSheet v) =
      nonDanglingValency base v :=
  SheetRelabelStable.nonDanglingValency_map
    (splitRelabeling base star anchor thickSheet thinSheet) hConn v

/-- The gauge fixes the wall's own vertex partition, so the endpoint above a
sheet is carried to the endpoint above that same sheet. -/
theorem splitGauge_sourceEndpoint (y : Fin degree) :
    splitGaugeVertexEquiv base star anchor thickSheet thinSheet (base.sourceEndpoint wall y) =
      (splitGaugedData base star anchor thickSheet thinSheet).sourceEndpoint wall y := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · show (splitRelabeling base star anchor thickSheet thinSheet).vertexPermutation wall
        ((base.vertexPartition wall).repr y) =
      ((splitGaugedData base star anchor thickSheet thinSheet).vertexPartition wall).repr y
    rw [splitGauge_vertexPermutation_wall base star anchor thickSheet thinSheet,
      splitGaugedData_vertexPartition_wall base star anchor thickSheet thinSheet]
    rfl

include hConn in
/-- **`OrdinaryTrivalent` transports across the gauge.** -/
theorem ordinaryTrivalent_splitGauged
    (hOrd : OrdinaryTrivalent base wall anchor) :
    OrdinaryTrivalent (splitGaugedData base star anchor thickSheet thinSheet) wall
      (splitGaugedAnchor base star anchor thickSheet thinSheet) := by
  intro y hY
  rw [splitGaugedAnchor_val,
    splitGaugedData_vertexPartition_wall base star anchor thickSheet thinSheet] at hY
  rw [← splitGauge_sourceEndpoint base star anchor thickSheet thinSheet y,
    nonDanglingValency_splitGauge base star anchor thickSheet thinSheet hConn]
  exact hOrd y hY

include hConn in
/-- **Trivalence away from the wall transports across the gauge.** -/
theorem trivalent_splitGauged_away
    (hAway : ∀ v : base.SourceVertex, v.1.1 ≠ wall → nonDanglingValency base v ≤ 3)
    (v : (splitGaugedData base star anchor thickSheet thinSheet).SourceVertex)
    (hv : v.1.1 ≠ wall) :
    nonDanglingValency (splitGaugedData base star anchor thickSheet thinSheet) v ≤ 3 := by
  have hEq := (splitGaugeVertexEquiv base star anchor thickSheet thinSheet).apply_symm_apply v
  rw [← hEq, nonDanglingValency_splitGauge base star anchor thickSheet thinSheet hConn]
  exact hAway _ (by rw [splitGaugeVertexEquiv_symm_target]; exact hv)

/-- The gauge on surviving occurrences, at the gauged datum's type. -/
noncomputable def splitGaugeNDEquiv :
    NonDanglingEdge base ≃
      NonDanglingEdge (splitGaugedData base star anchor thickSheet thinSheet) :=
  SheetRelabelStable.nonDanglingEdgeEquiv
    (splitRelabeling base star anchor thickSheet thinSheet) hConn

theorem splitGaugeNDEquiv_stablePath (g : NonDanglingEdge base) :
    (splitGaugeNDEquiv base star anchor thickSheet thinSheet hConn g).stablePath =
      splitGaugeRowEquiv base star anchor thickSheet thinSheet hConn g.stablePath := rfl

include hConn in
/-- **`HasPathEnds` transports across the gauge.** -/
theorem hasPathEnds_splitGauged (hEnds : HasPathEnds base) :
    HasPathEnds (splitGaugedData base star anchor thickSheet thinSheet) := by
  classical
  intro e
  obtain ⟨f, V, hRow, hInc, hNd⟩ := hEnds
    ((splitGaugeNDEquiv base star anchor thickSheet thinSheet hConn).symm e)
  refine ⟨splitGaugeNDEquiv base star anchor thickSheet thinSheet hConn f,
    splitGaugeVertexEquiv base star anchor thickSheet thinSheet V, ?_, ?_, ?_⟩
  · rw [splitGaugeNDEquiv_stablePath, hRow, ← splitGaugeNDEquiv_stablePath,
      Equiv.apply_symm_apply]
  · exact (SheetRelabelPruning.incident_sourceEdgeEquiv_iff
      (splitRelabeling base star anchor thickSheet thinSheet) f.1 V).mpr hInc
  · rw [nonDanglingValency_splitGauge base star anchor thickSheet thinSheet hConn]
    exact hNd

end Gauge

/-! ## 2.  Trivalence and path ends of the split candidate -/

section Candidate

variable {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall} (ra : SplitAnchor data star anchor)

local notation "cand" => (validCandidate ra.setup)

/-- Every source vertex over one side of the new target edge is the endpoint
vertex of its own sheet. -/
theorem eq_endpointVertex (sideValue : Bool) (v : (cand).datum.SourceVertex)
    (hv : v.1.1 = (if sideValue then freshVertex target else oldVertex target wall)) :
    endpointVertex ra sideValue v.1.2 = v :=
  (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hv.symm, rfl⟩

/-- **The split candidate is trivalent.**  Over `u` the anchor's two vertices are
`S` (`nd = 3`) and the pass-through `P_u` (`nd = 2`); over `v` they are `A_v`
(`nd = 3`) and the pass-through `P_v` (`nd = 2`); an ordinary block carries
`|star_s(B)| + [new survives] ≤ nd(B) ≤ 3`; away from the wall the datum's own
trivalence descends. -/
theorem candidate_trivalent (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor)
    (hAway : ∀ v : data.SourceVertex, v.1.1 ≠ wall → nonDanglingValency data v ≤ 3)
    (v : (cand).datum.SourceVertex) :
    nonDanglingValency (cand).datum v ≤ 3 := by
  classical
  have hWall : ∀ sideValue : Bool,
      v.1.1 = (if sideValue then freshVertex target else oldVertex target wall) →
      nonDanglingValency (cand).datum v ≤ 3 := by
    intro sideValue hv
    rw [← eq_endpointVertex ra sideValue v hv]
    by_cases hAnchor : (data.vertexPartition wall).Rel anchor.1 v.1.2
    · cases sideValue with
      | false =>
        rcases ra.thick_cover hAnchor with hT | hT
        · rw [endpointVertex_eq ra false hAnchor hT.symm,
            nonDanglingValency_endpointVertex_alpha ra hValid]
        · rw [endpointVertex_eq ra false hAnchor hT.symm,
            nonDanglingValency_endpointVertex_beta ra hValid]
          omega
      | true =>
        rcases ra.setup.cover v.1.2 hAnchor with hT | hT
        · rw [endpointVertex_eq ra true hAnchor hT.symm,
            nonDanglingValency_endpointVertex_delta ra hValid]
          omega
        · rw [endpointVertex_eq ra true hAnchor
              (hT.symm.trans ra.thin_rel_alpha_epsilon),
            nonDanglingValency_endpointVertex_epsilon ra hValid]
    · have hCard := card_ordinaryStar_add (data := data) (star := star) (anchor := anchor)
        v.1.2
      have hBound := hOrd v.1.2 hAnchor
      by_cases hDang : IsDangling (cand).datum (newEdgeAt ra v.1.2)
      · rw [nonDanglingValency_endpointVertex_of_new_dangling ra hValid sideValue hAnchor
          hDang]
        cases sideValue <;> omega
      · have hNe := ordinaryStar_card_ne_zero_of_new_survives ra hValid (!sideValue) hAnchor
          hDang
        rw [nonDanglingValency_endpointVertex_of_new_survives ra hValid sideValue hAnchor
          hDang]
        cases sideValue <;> simp only [Bool.not_false, Bool.not_true] at hNe <;> omega
  rcases hcase : (v.1.1 : TargetExpansion.Vertex target) with place | u
  · by_cases hIsWall : place = wall
    · exact hWall false (by rw [hcase, hIsWall]; rfl)
    · obtain ⟨old, hOld, hRet⟩ :=
        ResolutionAwayFromWall.exists_retainedVertex_of_target (cand) v place hIsWall hcase
      rw [← hRet, ResolutionAwayFromWall.nonDanglingValency_retainedVertex (cand) hValid
        (candidate_sourceGenus ra) old (by rw [hOld]; exact hIsWall)]
      exact hAway old (by rw [hOld]; exact hIsWall)
  · exact hWall true (by rw [hcase]; cases u; rfl)

/-- **The anchor half of the path-end transport.**  `e_alpha`'s retained
occurrence already meets the trivalent `S` and `e_epsilon`'s the trivalent
`A_v`; `e_beta`'s meets the divalent pass-through `P_u`, so the end moves along
the pass-through occurrence to `A_v`, and `e_delta`'s meets the divalent `P_v`,
so it moves along the piece to `S`.  These are the two places where the split's
census differs from the merge member's. -/
theorem exists_isPathEnd_anchor (hValid : data.Valid)
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hSurv : ¬ IsDangling data edge.1) :
    ∃ (first : NonDanglingEdge (cand).datum) (vertex : (cand).datum.SourceVertex),
      first.stablePath =
          (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 ⟨edge.1, hSurv⟩).stablePath ∧
        IsPathEnd (cand).datum first.1 vertex := by
  classical
  have hLabel : edge ∈ directionSurvivors data star anchor
      (survivorLabel data star anchor edge) :=
    (mem_directionSurvivors data star anchor _ edge).mpr
      ⟨(mem_survivors data anchor edge).mpr hSurv,
        (edge_survivorLabel data star anchor edge).symm⟩
  rcases NonTrivalentValencyTwoAnchor.eq_zero_or_one
    (survivorLabel data star anchor edge) with hDir | hDir
  · rw [hDir] at hLabel
    rcases thick_survivor_cases ra hLabel with rfl | rfl
    · refine ⟨ResolutionAwayFromWall.retainedEdge (cand) hValid.1 ⟨ra.alphaEdge.1, hSurv⟩,
        endpointVertex ra false (occurrenceSheet ra.alphaEdge), rfl, ?_, ?_⟩
      · exact retained_survivor_incident ra false hLabel (rightAssignment_zero ra)
          (occurrenceSheet_wall_rel ra.alphaEdge) rfl
      · rw [nonDanglingValency_endpointVertex_alpha ra hValid]
        omega
    · refine ⟨⟨passEdge ra, passEdge_survives ra hValid⟩,
        endpointVertex ra true (occurrenceSheet ra.epsilonEdge), ?_, ?_, ?_⟩
      · exact passEdge_stablePath_eq_retained ra hValid
      · rw [← endpointVertex_true_beta ra]
        exact newEdgeAt_incident ra true _
      · rw [nonDanglingValency_endpointVertex_epsilon ra hValid]
        omega
  · rw [hDir] at hLabel
    rcases thin_survivor_cases ra hLabel with rfl | rfl
    · refine ⟨⟨pieceEdge ra, pieceEdge_survives ra hValid⟩,
        endpointVertex ra false (occurrenceSheet ra.alphaEdge), ?_, ?_, ?_⟩
      · exact pieceEdge_stablePath_eq_retained ra hValid
      · rw [← endpointVertex_false_delta ra]
        exact newEdgeAt_incident ra false _
      · rw [nonDanglingValency_endpointVertex_alpha ra hValid]
        omega
    · refine ⟨ResolutionAwayFromWall.retainedEdge (cand) hValid.1 ⟨ra.epsilonEdge.1, hSurv⟩,
        endpointVertex ra true (occurrenceSheet ra.epsilonEdge), rfl, ?_, ?_⟩
      · exact retained_survivor_incident ra true hLabel (rightAssignment_one ra)
          (occurrenceSheet_wall_rel ra.epsilonEdge) rfl
      · rw [nonDanglingValency_endpointVertex_epsilon ra hValid]
        omega

/-- **The ordinary-block half of the path-end transport**, the argument of
`WallDatumPathEnds` over `NonTrivalentValencyTwoSplitRows.ordinaryStar`: off the
anchor the split candidate installs the same neutral joined resolution as the
merge member. -/
theorem exists_isPathEnd_ordinary (hValid : data.Valid)
    {h : NonDanglingEdge data} {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hInc : Incident data h.1 (data.sourceEndpoint wall x))
    (hNd : nonDanglingValency data (data.sourceEndpoint wall x) ≠ 2) :
    ∃ (first : NonDanglingEdge (cand).datum) (vertex : (cand).datum.SourceVertex),
      first.stablePath =
          (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 h).stablePath ∧
        IsPathEnd (cand).datum first.1 vertex := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : Bool,
      Prescribed.rightAssignment data star anchor h.1.1.1 = s := ⟨_, rfl⟩
  have hOld : h.1 ∈ ordinaryStar data star anchor x s := by
    rw [mem_ordinaryStar]
    exact ⟨⟨h.2, hInc⟩, hs⟩
  have hSum := card_ordinaryStar_add (data := data) (star := star) (anchor := anchor) x
  have hFlip : (ordinaryStar data star anchor x s).card +
      (ordinaryStar data star anchor x (!s)).card =
        nonDanglingValency data (data.sourceEndpoint wall x) := by
    cases s
    · exact hSum
    · rw [Nat.add_comm]; exact hSum
  have hPos : (ordinaryStar data star anchor x s).card ≠ 0 :=
    Finset.card_ne_zero_of_mem hOld
  by_cases hDang : IsDangling (cand).datum (newEdgeAt ra x)
  · have hOther : (ordinaryStar data star anchor x (!s)).card = 0 := by
      by_contra hBad
      refine ((newEdgeAt_survives_iff_ordinary ra hValid hX).mpr ?_) hDang
      cases s
      · exact ⟨hPos, hBad⟩
      · exact ⟨hBad, hPos⟩
    refine ⟨ResolutionAwayFromWall.retainedEdge (cand) hValid.1 h,
      endpointVertex ra s x, rfl, ?_, ?_⟩
    · exact incident_retainedEdge_endpointVertex ra hValid s hX hOld
    · rw [nonDanglingValency_endpointVertex_of_new_dangling ra hValid s hX hDang]
      omega
  · by_cases hCard : (ordinaryStar data star anchor x s).card = 1
    · refine ⟨⟨newEdgeAt ra x, hDang⟩, endpointVertex ra (!s) x, ?_, ?_, ?_⟩
      · exact (stablePath_retainedEdge_eq_newEdgeAt ra hValid s hX hOld hCard hDang).symm
      · exact newEdgeAt_incident ra (!s) x
      · rw [nonDanglingValency_endpointVertex_of_new_survives ra hValid (!s) hX hDang]
        omega
    · refine ⟨ResolutionAwayFromWall.retainedEdge (cand) hValid.1 h,
        endpointVertex ra s x, rfl, ?_, ?_⟩
      · exact incident_retainedEdge_endpointVertex ra hValid s hX hOld
      · rw [nonDanglingValency_endpointVertex_of_new_survives ra hValid s hX hDang]
        omega

/-- **A path end of the datum transports to a path end of the split candidate**,
on the retained row of the same occurrence. -/
theorem exists_isPathEnd_of_wall_end (hValid : data.Valid)
    {h : NonDanglingEdge data} {w : data.SourceVertex}
    (hInc : Incident data h.1 w) (hNd : nonDanglingValency data w ≠ 2) :
    ∃ (first : NonDanglingEdge (cand).datum) (vertex : (cand).datum.SourceVertex),
      first.stablePath =
          (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 h).stablePath ∧
        IsPathEnd (cand).datum first.1 vertex := by
  classical
  by_cases hAt : w.1.1 = wall
  · have hVertex : data.sourceEndpoint wall w.1.2 = w :=
      (GluingDatum.sourceEndpoint_eq_iff data wall w.1.2 w).mpr ⟨hAt.symm, rfl⟩
    by_cases hAnchor : (data.vertexPartition wall).Rel anchor.1 w.1.2
    · have hwEq : WallBlock.sourceVertex data wall anchor = w :=
        (GluingDatum.sourceEndpoint_eq_iff data wall anchor.1 w).mpr ⟨hAt.symm, hAnchor⟩
      have hIncAnchor : Incident data h.1 (WallBlock.sourceVertex data wall anchor) := by
        rw [hwEq]; exact hInc
      exact exists_isPathEnd_anchor ra hValid (edge := ⟨h.1, hIncAnchor⟩) h.2
    · refine exists_isPathEnd_ordinary ra hValid hAnchor ?_ ?_
      · rw [hVertex]; exact hInc
      · rw [hVertex]; exact hNd
  · refine ⟨ResolutionAwayFromWall.retainedEdge (cand) hValid.1 h,
      ResolutionAwayFromWall.retainedVertex (cand) w, rfl, ?_, ?_⟩
    · exact (ResolutionAwayFromWall.incident_oldSourceEdge_iff (cand) w hAt h.1).mpr hInc
    · rw [ResolutionAwayFromWall.nonDanglingValency_retainedVertex (cand) hValid
        (candidate_sourceGenus ra) w hAt]
      exact hNd

/-- **`HasPathEnds` of the split candidate.**  Through
`NonTrivalentValencyTwoSplitRowEquiv.rowEquiv` every stable row is the bridge
row -- whose single occurrence ends at the trivalent `S`, so it is a path end
outright -- or the retained row of a stable row of the datum. -/
theorem hasPathEnds_candidate (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor) (hEnds : HasPathEnds data) :
    HasPathEnds (cand).datum := by
  classical
  intro e
  have hBack := (rowEquiv ra hValid hOrd).symm_apply_apply e.stablePath
  cases hCase : rowEquiv ra hValid hOrd e.stablePath with
  | none =>
    rw [hCase] at hBack
    have hRow : bridgeRow ra hValid = e.stablePath := hBack
    refine ⟨⟨bridgeEdge ra, bridgeEdge_survives ra hValid⟩,
      endpointVertex ra false (occurrenceSheet ra.alphaEdge), hRow, ?_, ?_⟩
    · exact newEdgeAt_incident ra false _
    · rw [nonDanglingValency_endpointVertex_alpha ra hValid]
      omega
  | some r =>
    rw [hCase] at hBack
    have hRow : retainedRowFree ra hValid r = e.stablePath := hBack
    obtain ⟨g, hg⟩ := Quot.exists_rep r
    have hgr : NonDanglingEdge.stablePath g = r := hg
    obtain ⟨wallEdge, w, hRowW, hInc, hNd⟩ := hEnds g
    obtain ⟨first, vertex, hFirst, hEnd⟩ := exists_isPathEnd_of_wall_end ra hValid hInc hNd
    refine ⟨first, vertex, ?_, hEnd⟩
    rw [hFirst, ← retainedRowFree_mk ra hValid wallEdge, hRowW, hgr, hRow]

end Candidate

/-! ## 3.  The outgoing full-dimensional presentation at an actual two-valent wall -/

section Wall

open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.WallDegeneration

noncomputable section

variable {targetIn : CFGraph} {deg : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (cover : GluingDatum targetIn deg)
  (fd : FullDimensionalSourcePresentation cover coordinate)
  {a b : targetIn.V} {contracted : targetIn.edges}
  (hc : (contracted : targetIn.V × targetIn.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges targetIn a b = 1)
  (hForest : ContractionForest cover a b contracted)
  (coordinates : coordinate → ℚ) (facet : coordinate)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
  (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
    0 < coordinates column)
  (hFacetZero :
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates facet = 0)
  (wallStar : TwoStar (contract targetIn hab hOne) ⟨a, hab⟩)
  (anchorBlk : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩)
  (thickSheet thinSheet : Fin deg)
  (labelling₀ : StableLengthMatrixLabelling (contractDatum cover hc hab hOne)
    {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted})
  (ra : SplitAnchor
    (splitGaugedData (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet
      thinSheet) wallStar
    (splitGaugedAnchor (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet
      thinSheet))
  (hGauged : (splitGaugedData (contractDatum cover hc hab hOne) wallStar anchorBlk
    thickSheet thinSheet).Valid)
  (hOrdGauged : OrdinaryTrivalent (splitGaugedData (contractDatum cover hc hab hOne) wallStar
    anchorBlk thickSheet thinSheet) ⟨a, hab⟩
    (splitGaugedAnchor (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet
      thinSheet))

/-! ### The outgoing target -/

include fd in
theorem outgoing_targetConnected :
    graph_connected (TargetExpansion.graph (contract targetIn hab hOne) ⟨a, hab⟩
      (validCandidate ra.setup).right) :=
  TargetExpansion.graph_connected (contract targetIn hab hOne) ⟨a, hab⟩ _
    (NonTrivalentUniqueFourValent.wall_target_connected cover fd hab hOne)

include fd in
theorem outgoing_targetGenus :
    genus (TargetExpansion.graph (contract targetIn hab hOne) ⟨a, hab⟩
      (validCandidate ra.setup).right) = 0 :=
  (TargetExpansion.graph_genus (contract targetIn hab hOne) ⟨a, hab⟩ _).trans
    (NonTrivalentUniqueFourValent.wall_target_genus cover fd hab hOne)

theorem outgoing_targetEdgeCard :
    (TargetExpansion.graph (contract targetIn hab hOne) ⟨a, hab⟩
      (validCandidate ra.setup).right).edges.card = targetIn.edges.card :=
  (TargetExpansion.graph_edge_card (contract targetIn hab hOne) ⟨a, hab⟩ _).trans
    (WallDegeneration.edge_card_contract hab hOne).symm

include hForest in
/-- **The split candidate preserves the incoming source genus.**  The candidate
preserves the gauged datum's genus, the gauge is a relabelling, and the wall
contraction loses one source vertex and one source occurrence in every fibre. -/
theorem outgoing_sourceGenus :
    genus (validCandidate ra.setup).datum.sourceGraph = genus cover.sourceGraph :=
  (candidate_sourceGenus ra).trans
    ((genus_splitGaugedData (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet
      thinSheet).trans
      (NonTrivalentValencyTwoExit.genus_sourceGraph_contractDatum cover hc hab hOne hForest))

/-! ### Trivalence, path ends and nonsingularity -/

include fd hForest hGauged hOrdGauged in
/-- **The outgoing candidate is trivalent**, from the census of
`NonTrivalentValencyTwoSplitRows` transported across the inclusion gauge: `nd(S) = nd(A_v) = 3`, `nd(P_u) = nd(P_v) = 2` at the
anchor, `nd(B_s) = |star_s(B)| + [new survives]` at an ordinary block, and the
wall datum's own trivalence away from the anchor. -/
theorem outgoing_trivalent (v : (validCandidate ra.setup).datum.SourceVertex) :
    nonDanglingValency (validCandidate ra.setup).datum v ≤ 3 :=
  candidate_trivalent ra hGauged hOrdGauged
    (trivalent_splitGauged_away (contractDatum cover hc hab hOne) wallStar anchorBlk
      thickSheet thinSheet
      (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest).1
      (fun w hw ↦ NonTrivalentValencyTwoExit.wallDatum_trivalent_away cover fd hc hab hOne
        hForest w hw))
    v

include hForest hZeroCoord hPosCoord hFacetZero hGauged hOrdGauged in
/-- **`HasPathEnds` of the outgoing candidate**, from the wall-datum path ends
of `WallDatumPathEnds` transported across the inclusion gauge and then through
the split row
dictionary.  The two divalent pass-through vertices are handled by moving the end
along the pass-through occurrence resp. the piece. -/
theorem outgoing_pathEnds
    (hNoReturn : LeafFacetNoReturn.NoContractedReturnOffRow cover contracted
      (fd.labelling.row.symm facet)) :
    HasPathEnds (validCandidate ra.setup).datum :=
  hasPathEnds_candidate ra hGauged hOrdGauged
    (hasPathEnds_splitGauged (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet
      thinSheet (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest).1
      (WallDatumPathEnds.hasPathEnds_contractDatum cover fd hc hab hOne hForest coordinates
        facet hNoReturn hZeroCoord hPosCoord hFacetZero))

include coordinates hZeroCoord hPosCoord hFacetZero in
/-- **Nonsingularity of the outgoing matrix**, by the common-minor expansion
along the bridge row (`NonTrivalentLinkMatrix.det_ne_zero`). -/
theorem det_chartLabelling_ne_zero
    (hRowVal : ∀ p : StablePath (contractDatum cover hc hab hOne),
      (labelling₀.row p).1 =
        Equiv.swap facet (fd.labelling.targetEdge.symm contracted)
          (fd.labelling.row (incomingRow cover fd hc hab hOne
            (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
              hForest) hForest p)))
    (hMatrixWall : ∀ (p : StablePath (contractDatum cover hc hab hOne))
      (column : {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted}),
      GluingDatum.LengthMatrixPresentation.matrix labelling₀.presentation
          (labelling₀.row p) column =
        GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
          (fd.labelling.row (incomingRow cover fd hc hab hOne
            (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
              hForest) hForest p)) column.1) :
    (GluingDatum.LengthMatrixPresentation.matrix
      (chartLabelling cover fd hc hab hOne hForest facet wallStar anchorBlk thickSheet
        thinSheet labelling₀ ra hGauged hOrdGauged).presentation).det ≠ 0 :=
  NonTrivalentLinkMatrix.det_ne_zero
    (agreeOffColumn_chartLabelling cover fd hc hab hOne hForest facet wallStar anchorBlk
      thickSheet thinSheet labelling₀ ra hGauged hOrdGauged coordinates hZeroCoord hPosCoord
      hFacetZero hRowVal hMatrixWall)
    (fun j hj ↦ NonTrivalentValencyTwoExit.incoming_facet_eq_zero cover fd coordinates facet
      hZeroCoord hPosCoord hFacetZero j hj)
    (fun j hj ↦ matrix_chartLabelling_facet_eq_zero cover fd hc hab hOne hForest facet
      wallStar anchorBlk thickSheet thinSheet labelling₀ ra hGauged hOrdGauged j hj)
    fd.det_ne_zero
    (matrix_chartLabelling_corner_pos cover fd hc hab hOne hForest facet wallStar anchorBlk
      thickSheet thinSheet labelling₀ ra hGauged hOrdGauged).ne'

/-- **The outgoing full-dimensional source presentation of a Base II split
candidate at an actual two-valent wall.**  Every field is produced: validity, the
outgoing target's connectivity, genus and edge count, source-genus preservation,
saturation, the honest labelling on the incoming chart, nonsingularity,
trivalence and path ends. -/
def outgoingFD
    (hNoReturn : LeafFacetNoReturn.NoContractedReturnOffRow cover contracted
      (fd.labelling.row.symm facet))
    (hRowVal : ∀ p : StablePath (contractDatum cover hc hab hOne),
      (labelling₀.row p).1 =
        Equiv.swap facet (fd.labelling.targetEdge.symm contracted)
          (fd.labelling.row (incomingRow cover fd hc hab hOne
            (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
              hForest) hForest p)))
    (hMatrixWall : ∀ (p : StablePath (contractDatum cover hc hab hOne))
      (column : {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted}),
      GluingDatum.LengthMatrixPresentation.matrix labelling₀.presentation
          (labelling₀.row p) column =
        GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
          (fd.labelling.row (incomingRow cover fd hc hab hOne
            (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
              hForest) hForest p)) column.1) :
    FullDimensionalSourcePresentation (validCandidate ra.setup).datum coordinate :=
  NonTrivalentValencyTwoExit.ofTypeChange fd
    (validCandidate_datum_valid ra.setup hGauged)
    (outgoing_targetConnected cover fd hc hab hOne wallStar anchorBlk thickSheet thinSheet ra)
    (outgoing_targetGenus cover fd hc hab hOne wallStar anchorBlk thickSheet thinSheet ra)
    (outgoing_targetEdgeCard cover hc hab hOne wallStar anchorBlk thickSheet thinSheet ra)
    (outgoing_sourceGenus cover hc hab hOne hForest wallStar anchorBlk thickSheet thinSheet ra)
    (chartLabelling cover fd hc hab hOne hForest facet wallStar anchorBlk thickSheet
      thinSheet labelling₀ ra hGauged hOrdGauged)
    (det_chartLabelling_ne_zero cover fd hc hab hOne hForest coordinates facet hZeroCoord
      hPosCoord hFacetZero wallStar anchorBlk thickSheet thinSheet labelling₀ ra hGauged
      hOrdGauged hRowVal hMatrixWall)
    (outgoing_trivalent cover fd hc hab hOne hForest wallStar anchorBlk thickSheet thinSheet
      ra hGauged hOrdGauged)
    (outgoing_pathEnds cover fd hc hab hOne hForest coordinates facet hZeroCoord hPosCoord
      hFacetZero wallStar anchorBlk thickSheet thinSheet ra hGauged hOrdGauged hNoReturn)

end

end Wall

/-! ## 4.  The link at a wall of the outer walk -/

section Link

open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk

noncomputable section

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {deg : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival deg graph label (label m.base)}
  (wd : WallData arrival)
  (wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
  (anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
  (thickSheet thinSheet : Fin deg)
  (labelling₀ : StableLengthMatrixLabelling (contractDatum wd.cover wd.hc wd.hab wd.hOne)
    {column : coordinate //
      column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted})
  (ra : SplitAnchor
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
  (hRowVal : ∀ p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne),
    (labelling₀.row p).1 =
      Equiv.swap (label m.base) (wd.fullDim.labelling.targetEdge.symm wd.contracted)
        (wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (WallAdmissibility.danglingCompatible_of_contractionForest wd.cover wd.hc wd.hab
            wd.hOne (wd.hForest m)) (wd.hForest m) p)))
  (hMatrixWall : ∀ (p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (column : {column : coordinate //
      column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted}),
    GluingDatum.LengthMatrixPresentation.matrix labelling₀.presentation
        (labelling₀.row p) column =
      GluingDatum.LengthMatrixPresentation.matrix wd.fullDim.labelling.presentation
        (wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (WallAdmissibility.danglingCompatible_of_contractionForest wd.cover wd.hc wd.hab
            wd.hOne (wd.hForest m)) (wd.hForest m) p)) column.1)

/-- The outgoing split presentation at the wall data of the outer walk.  The
weak no-return condition is discharged internally at **every** two-valent wall by
`NonTrivalentValencyTwoBaseOneExit.noContractedReturnOffRow_two`, so no no-return
receipt of any kind reaches this interface. -/
def wallOutgoingFD :
    FullDimensionalSourcePresentation (validCandidate ra.setup).datum coordinate :=
  outgoingFD wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m) wd.coordinates
    (label m.base) wd.hZeroCoord wd.hPosCoord wd.hFacetZero wallStar anchorBlk thickSheet
    thinSheet labelling₀ ra hGauged hOrdGauged
    (NonTrivalentValencyTwoBaseOneExit.noContractedReturnOffRow_two wd.cover wd.fullDim
      wd.hc wd.hab wd.hOne wd.coordinates (label m.base) wd.hZeroCoord wd.hPosCoord
      wd.hFacetZero wallStar)
    hRowVal hMatrixWall

/-- **The Base II split inhabitant of `OuterWalk.TypeChangeLink` at a two-valent
wall.**  The base of the outgoing payload is the *gauged* wall datum of
`NonTrivalentValencyTwoSplitGauge` (the split needs the inclusion alignment
gauge, so `TypeChangeLink.base` is not the wall datum itself), the candidate is
the split member of `NonTrivalentValencyTwoSplitCandidate`, the presentation is
`wallOutgoingFD` and the common minor is
`NonTrivalentValencyTwoSplitRowDictionary.agreeOffColumn_chartLabelling`.
`tracks` is the only remaining hypothesis. -/
def typeChangeLink_of_receipts_split
    (tracks : Tracks (wallOutgoingFD m wd wallStar anchorBlk thickSheet thinSheet labelling₀
      ra hGauged hOrdGauged hRowVal hMatrixWall) (graph.move m) label) :
    TypeChangeLink m wd where
  base := splitGaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
    thickSheet thinSheet
  baseValid := hGauged
  candidate := validCandidate ra.setup
  outgoingFD := wallOutgoingFD m wd wallStar anchorBlk thickSheet thinSheet labelling₀ ra
    hGauged hOrdGauged hRowVal hMatrixWall
  tracks := tracks
  agree := by
    have h := agreeOffColumn_chartLabelling wd.cover wd.fullDim wd.hc wd.hab wd.hOne
      (wd.hForest m) (label m.base) wallStar anchorBlk thickSheet thinSheet labelling₀ ra
      hGauged hOrdGauged wd.coordinates wd.hZeroCoord wd.hPosCoord wd.hFacetZero hRowVal
      hMatrixWall
    rw [wd.targetEdge_symm_contracted] at h
    exact h

end

end Link

/-! ## 5.  The actual-wall headline -/

section Headline

open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk

noncomputable section

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {deg : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival deg graph label (label m.base)}
  (wd : WallData arrival)

/-- **The Base II split type-changing exit at a two-valent wall of the outer
walk, with no receipt about the candidate and no no-return hypothesis of any
kind.**  From the wall data alone (and the incoming two-valent star) this
produces the anchor block and `nd(A) = 4`; then, given the caller's dispatch data
-- Configuration A, the four named survivors of the paper's picture and the
strict index inequality `k_delta < k_alpha`, which is the condition of Part II,
Subcase `{v2-nd4-t3-k2<k3}`, for the Base I member *not* to exist and the split
member to be the one realizing the prescribed cross pairing -- it produces the
inclusion gauge of `NonTrivalentValencyTwoSplitGauge`,
the split candidate over it, the outgoing `FullDimensionalSourcePresentation` on
the incoming chart, the common minor `AgreeOffColumn` that
`OuterWalk.TypeChangeLink.agree` asks for, and the link itself as soon as
`InteriorGraphTracking.Tracks` is supplied. -/
theorem exists_typeChangeLink_split_of_wallData
    (wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    ∃ anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩,
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
            ∀ _tracks : Tracks out (graph.move m) label, Nonempty (TypeChangeLink m wd) := by
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
  refine ⟨anchorBlock, hNd, ?_⟩
  intro hSplit alphaEdge betaEdge deltaEdge epsilonEdge hAlpha hBeta hDelta hEpsilon
    hAlphaNe hDeltaNe hIndex
  have ra := splitAnchor_gauged src hSplit
    (NonTrivalentUniqueFourValent.wall_target_connected wd.cover wd.fullDim wd.hab wd.hOne)
    (NonTrivalentUniqueFourValent.wall_target_genus wd.cover wd.fullDim wd.hab wd.hOne)
    hValid.1 hAlpha hBeta hDelta hEpsilon hAlphaNe hDeltaNe hIndex
  have hGauged := splitGaugedData_valid (contractDatum wd.cover wd.hc wd.hab wd.hOne)
    wallStar anchorBlock (occurrenceSheet alphaEdge) (occurrenceSheet deltaEdge) hValid
  have hOrdGauged := ordinaryTrivalent_splitGauged
    (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlock
    (occurrenceSheet alphaEdge) (occurrenceSheet deltaEdge) hValid.1 hOrd
  refine ⟨ra,
    wallOutgoingFD m wd wallStar anchorBlock (occurrenceSheet alphaEdge)
      (occurrenceSheet deltaEdge) labelling₀ ra hGauged hOrdGauged hRowVal hMatrixWall,
    ?_, ?_⟩
  · have h := agreeOffColumn_chartLabelling wd.cover wd.fullDim wd.hc wd.hab wd.hOne
      (wd.hForest m) (label m.base) wallStar anchorBlock (occurrenceSheet alphaEdge)
      (occurrenceSheet deltaEdge) labelling₀ ra hGauged hOrdGauged wd.coordinates
      wd.hZeroCoord wd.hPosCoord wd.hFacetZero hRowVal hMatrixWall
    rw [wd.targetEdge_symm_contracted] at h
    exact h
  · exact fun tracks ↦ ⟨typeChangeLink_of_receipts_split m wd wallStar anchorBlock
      (occurrenceSheet alphaEdge) (occurrenceSheet deltaEdge) labelling₀ ra hGauged
      hOrdGauged hRowVal hMatrixWall tracks⟩

end

end Headline

/-! ## 6.  The mirror member, by relabelling the wall star

`NonTrivalentValencyTwoCandidate.Prescribed.thickDirection` is

```text
if 2 ≤ (directionSurvivors data star anchor 0).card then 0 else 1
```

so in Configuration A -- where both direction fibres have two survivors -- it is
the label `0` of *whatever* `TwoStar` labelling is used
(`NonTrivalentValencyTwoSplitGauge.thickDirection_eq_zero`), and the outgoing
base tree puts the direction labelled `0` at the divalent endpoint `u`.
Exchanging the two labels of the wall star therefore exchanges thick and thin,
and the split member "in which a class over `star.edge 1` splits above `u`" is
the *same* construction over the relabelled star.  No reversed subdivision
background is needed.
-/

section Mirror

variable {data : GluingDatum target degree} {anchor : WallBlock data wall}

/-- **The relabelled two-star**: the same two incident target occurrences of the
wall, with the two labels exchanged. -/
def relabelStar (star : TwoStar target wall) : TwoStar target wall :=
  ⟨(Equiv.swap 0 1).trans star.label⟩

@[simp] theorem relabelStar_edge (star : TwoStar target wall) (lbl : Fin 2) :
    (relabelStar star).edge lbl = star.edge (Equiv.swap 0 1 lbl) := rfl

@[simp] theorem relabelStar_edge_zero (star : TwoStar target wall) :
    (relabelStar star).edge 0 = star.edge 1 := by
  rw [relabelStar_edge, Equiv.swap_apply_left]

@[simp] theorem relabelStar_edge_one (star : TwoStar target wall) :
    (relabelStar star).edge 1 = star.edge 0 := by
  rw [relabelStar_edge, Equiv.swap_apply_right]

/-- The relabelling is an involution. -/
theorem relabelStar_relabelStar (star : TwoStar target wall) :
    relabelStar (relabelStar star) = star := by
  cases star with
  | mk lab =>
    exact congrArg TwoStar.mk
      (Equiv.ext fun lbl ↦ congrArg lab (Equiv.swap_apply_self (0 : Fin 2) 1 lbl))

/-- **Non-vacuity of the relabelling**: it really is a different labelling of the
same wall, so the two headlines below are two genuinely different members. -/
theorem relabelStar_ne (star : TwoStar target wall) : relabelStar star ≠ star := by
  intro hEq
  have h : star.label (Equiv.swap (0 : Fin 2) 1 0) = star.label 0 :=
    congrArg (fun s : TwoStar target wall ↦ s.label 0) hEq
  rw [Equiv.swap_apply_left] at h
  exact absurd (star.label.injective h) (by decide)

/-- The direction fibres are exchanged. -/
theorem directionSurvivors_relabelStar (star : TwoStar target wall) (lbl : Fin 2) :
    directionSurvivors data (relabelStar star) anchor lbl =
      directionSurvivors data star anchor (Equiv.swap 0 1 lbl) := by
  classical
  ext edge
  rw [mem_directionSurvivors, mem_directionSurvivors, relabelStar_edge]

@[simp] theorem directionSurvivors_relabelStar_zero (star : TwoStar target wall) :
    directionSurvivors data (relabelStar star) anchor 0 =
      directionSurvivors data star anchor 1 := by
  rw [directionSurvivors_relabelStar, Equiv.swap_apply_left]

@[simp] theorem directionSurvivors_relabelStar_one (star : TwoStar target wall) :
    directionSurvivors data (relabelStar star) anchor 1 =
      directionSurvivors data star anchor 0 := by
  rw [directionSurvivors_relabelStar, Equiv.swap_apply_right]

/-- The survivor distribution transports along the relabelling. -/
theorem twoBranchDistribution_relabelStar {star : TwoStar target wall}
    (h : TwoBranchDistribution data star anchor) :
    TwoBranchDistribution data (relabelStar star) anchor := by
  rcases h with hEven | ⟨tripled, hThree, hOne⟩
  · exact Or.inl fun lbl ↦ by
      rw [directionSurvivors_relabelStar]; exact hEven _
  · refine Or.inr ⟨Equiv.swap 0 1 tripled, ?_, ?_⟩
    · rw [directionSurvivors_relabelStar, Equiv.swap_apply_self]
      exact hThree
    · intro lbl hNe
      rw [directionSurvivors_relabelStar]
      refine hOne _ ?_
      intro hBad
      exact hNe (by rw [← hBad, Equiv.swap_apply_self])

/-- **The classifier transports along the relabelling.**  `activeTargets` and the
total survivor-index sum do not mention the star at all, and the two direction
sums are exchanged. -/
theorem twoBranchAnchor_relabelStar {star : TwoStar target wall}
    (src : TwoBranchAnchor data star anchor) :
    TwoBranchAnchor data (relabelStar star) anchor where
  active_all := src.active_all
  distribution := twoBranchDistribution_relabelStar src.distribution
  direction_index_sum := fun lbl ↦ by
    rw [directionSurvivors_relabelStar]
    exact src.direction_index_sum _
  survivor_index_sum := src.survivor_index_sum

/-- Configuration A transports along the relabelling. -/
theorem split_relabelStar {star : TwoStar target wall}
    (hSplit : ∀ lbl : Fin 2, (directionSurvivors data star anchor lbl).card = 2)
    (lbl : Fin 2) :
    (directionSurvivors data (relabelStar star) anchor lbl).card = 2 := by
  rw [directionSurvivors_relabelStar]
  exact hSplit _

/-- **Relabelling exchanges thick and thin.**  In Configuration A the thick
direction is the label `0` of whichever labelling is used, so the relabelled
star's thick occurrence is the original star's thin one. -/
theorem thickEdge_relabelStar_eq_thinEdge {star : TwoStar target wall}
    (hSplit : ∀ lbl : Fin 2, (directionSurvivors data star anchor lbl).card = 2) :
    Prescribed.thickEdge data (relabelStar star) anchor =
      Prescribed.thinEdge data star anchor := by
  rw [thickEdge_eq_zero (split_relabelStar hSplit 0), thinEdge_eq_one (hSplit 0),
    relabelStar_edge_zero]

/-- The mirror of `thickEdge_relabelStar_eq_thinEdge`. -/
theorem thinEdge_relabelStar_eq_thickEdge {star : TwoStar target wall}
    (hSplit : ∀ lbl : Fin 2, (directionSurvivors data star anchor lbl).card = 2) :
    Prescribed.thinEdge data (relabelStar star) anchor =
      Prescribed.thickEdge data star anchor := by
  rw [thinEdge_eq_one (split_relabelStar hSplit 0), thickEdge_eq_zero (hSplit 0),
    relabelStar_edge_one]

/-! ### Outside Configuration A the relabelling does *not* exchange thick and thin

`thickDirection` is label-based only where both direction fibres carry at least
two survivors.  In Configuration B (`3 + 1`, Part II, Case `{v2-nd4-t2}`) it
picks the **tripled** direction, which is intrinsic to the datum, so `thickEdge`
is *invariant* under `relabelStar` and the mirror trick is unavailable there.
The split family lives only in Configuration A, so nothing above is affected;
this is recorded because a Configuration B member cannot be mirrored by
relabelling the star. -/

/-- `thickEdge` is the label-`0` occurrence as soon as that direction carries two
survivors. -/
theorem thickEdge_of_two_le {star : TwoStar target wall}
    (h : 2 ≤ (directionSurvivors data star anchor 0).card) :
    Prescribed.thickEdge data star anchor = star.edge 0 := by
  rw [Prescribed.thickEdge_eq]
  congr 1
  unfold Prescribed.thickDirection
  rw [if_pos h]

/-- `thickEdge` is the label-`1` occurrence when the label-`0` direction carries
at most one survivor. -/
theorem thickEdge_of_le_one {star : TwoStar target wall}
    (h : (directionSurvivors data star anchor 0).card ≤ 1) :
    Prescribed.thickEdge data star anchor = star.edge 1 := by
  rw [Prescribed.thickEdge_eq]
  congr 1
  unfold Prescribed.thickDirection
  rw [if_neg (by omega)]

/-- **In Configuration B the relabelling fixes the thick occurrence.**  So the
mirror trick of this section is specific to Configuration A, where both direction
fibres have two survivors and `thickDirection` really is the label `0`. -/
theorem thickEdge_relabelStar_eq_self_of_tripled {star : TwoStar target wall}
    (tripled : Fin 2)
    (hThree : 2 ≤ (directionSurvivors data star anchor tripled).card)
    (hOne : ∀ lbl : Fin 2, lbl ≠ tripled →
      (directionSurvivors data star anchor lbl).card ≤ 1) :
    Prescribed.thickEdge data (relabelStar star) anchor =
      Prescribed.thickEdge data star anchor := by
  rcases NonTrivalentValencyTwoAnchor.eq_zero_or_one tripled with rfl | rfl
  · rw [thickEdge_of_two_le hThree,
      thickEdge_of_le_one (star := relabelStar star)
        (by rw [directionSurvivors_relabelStar_zero]; exact hOne 1 (by decide)),
      relabelStar_edge_one]
  · rw [thickEdge_of_le_one (hOne 0 (by decide)),
      thickEdge_of_two_le (star := relabelStar star)
        (by rw [directionSurvivors_relabelStar_zero]; exact hThree),
      relabelStar_edge_zero]

end Mirror

/-! ## 7.  The mirror headline -/

section MirrorHeadline

open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk

noncomputable section

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {deg : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival deg graph label (label m.base)}
  (wd : WallData arrival)

/-- **The mirror split exit**: the Base II split member in which a class over
`wallStar.edge 1` splits above the divalent endpoint.  It is
`exists_typeChangeLink_split_of_wallData` over the relabelled star, with the two
directions exchanged: `alphaEdge` (the class that splits) and `betaEdge` now run
over `wallStar.edge 1` and `deltaEdge` (the piece), `epsilonEdge` over
`wallStar.edge 0`, while the strict index inequality is unchanged.  Together with
the unrelabelled headline this gives the dispatcher both members at a
Configuration A wall: it compares `k_alpha` and `k_delta` on each side and picks
the star labelling accordingly, exactly as `NonTrivalentValencyFourDispatcher`
does at valency four. -/
theorem exists_typeChangeLink_splitMirror_of_wallData
    (wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    ∃ anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩,
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
              (relabelStar wallStar) anchorBlock (occurrenceSheet alphaEdge)
              (occurrenceSheet deltaEdge)) (relabelStar wallStar)
            (splitGaugedAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne)
              (relabelStar wallStar) anchorBlock (occurrenceSheet alphaEdge)
              (occurrenceSheet deltaEdge)))
          (out : FullDimensionalSourcePresentation (validCandidate ra.setup).datum
            coordinate),
          AgreeOffColumn wd.incomingMatrix
              (GluingDatum.LengthMatrixPresentation.matrix out.labelling.presentation)
              wd.column ∧
            ∀ _tracks : Tracks out (graph.move m) label, Nonempty (TypeChangeLink m wd) := by
  classical
  obtain ⟨anchorBlock, hNd, hRest⟩ :=
    exists_typeChangeLink_split_of_wallData m wd (relabelStar wallStar)
  refine ⟨anchorBlock, hNd, ?_⟩
  intro hSplit alphaEdge betaEdge deltaEdge epsilonEdge hAlpha hBeta hDelta hEpsilon
    hAlphaNe hDeltaNe hIndex
  have hZero : directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (relabelStar wallStar) anchorBlock 0 =
        directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
          anchorBlock 1 :=
    directionSurvivors_relabelStar_zero wallStar
  have hOne' : directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (relabelStar wallStar) anchorBlock 1 =
        directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
          anchorBlock 0 :=
    directionSurvivors_relabelStar_one wallStar
  refine hRest (fun direction ↦ ?_) alphaEdge betaEdge deltaEdge epsilonEdge
    (hZero ▸ hAlpha) (hZero ▸ hBeta) (hOne' ▸ hDelta) (hOne' ▸ hEpsilon)
    hAlphaNe hDeltaNe hIndex
  have hDir : directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (relabelStar wallStar) anchorBlock direction =
        directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
          anchorBlock (Equiv.swap 0 1 direction) :=
    directionSurvivors_relabelStar wallStar direction
  rw [hDir]
  exact hSplit _

end

end MirrorHeadline

end DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitExit
