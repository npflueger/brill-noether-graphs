module

public import DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneRowDictionary
public import DraismaVargas.LocalCases.WallDatumPathEnds

@[expose] public section

/-!
# The valency-two **Base I** exit: the outgoing full-dimensional presentation

Source: Vargas, Part II, arXiv:2609.09109, Section 5.1 (the labelling convention at a
non-trivalent wall, and `lm:change-comb-type`: the wall matrix is the common
minor `A_{\varphi_0}`) together with Section 5.4 (case `{v2-nd4-t3}`,
Configuration A, base tree `T_∅` = Base I), and Draisma–Vargas Part I, arXiv:1909.12924, Case
`{w2-r2}`, Base I.  The consumer interface is `OuterWalk.TypeChangeLink`.

This is `NonTrivalentValencyTwoExit`, ported from the Base II merge member to
the **Base I** candidates of `NonTrivalentValencyTwoBaseOne`, over the
`t_3`-branch alignment gauge of `NonTrivalentValencyTwoGauge`, with the census
of `NonTrivalentValencyTwoBaseOneRows` and the Base I row dictionary of
`NonTrivalentValencyTwoBaseOneRowDictionary`.

## What is different from Base II

* The candidate lives over `NonTrivalentValencyTwoGauge.gaugedData`, so
  `TypeChangeLink.base` is the **gauged** wall datum, not the wall datum itself
  (the same shape the valency-four exit needs).  Everything the
  Base II exit read off the wall datum -- `OrdinaryTrivalent`, trivalence away
  from the anchor, `HasPathEnds` -- is transported across the gauge here
  (`ordinaryTrivalent_gauged`, `trivalent_gauged_away`, `hasPathEnds_gauged`);
  the gauge is a `SheetRelabeling`, so nothing is lost and the source genus is
  unchanged (`genus_gaugedData`).
* **Path ends are easier at Base I.**  Base II needs an ordinary-block
  adjustment (`WallDatumPathEnds.Two.exists_isPathEnd_ordinary`, moving the end
  to the other side when one side has a single survivor and the new occurrence
  survives).  At Base I the base tree `T_∅` sends *every* old occurrence at the
  wall to the new trivalent point `v` (`incident_branchVertex_self`); the only
  surviving new occurrences are the two fold ones, so an ordinary block keeps
  exactly its old star (`nd(B_v) = nd(B)`) and both anchor branch vertices are
  trivalent.  No adjustment, no witness bookkeeping.  The bridge row `h_1` is a
  path end outright: it ends at the trivalent `A_1`.
* `NoContractedReturnOffRow` is discharged here in **all three** incoming
  sub-cases (`noContractedReturnOffRow_two`), so no no-return hypothesis reaches
  the link.  `NonTrivalentValencyTwoExit.typeChangeLink_of_receipts` carries the
  strong `NoContractedReturn`; its Base I analogue here does not.

## What is proved

* `gaugeVertexEquiv`, `gaugeEdgeEquiv`, `gaugeNDEquiv`, `genus_gaugedData`,
  `nonDanglingValency_gauge`, `gauge_sourceEndpoint`, `ordinaryTrivalent_gauged`,
  `trivalent_gauged_away`, `hasPathEnds_gauged`: the gauge transport.
* `candidate_trivalent`: **the Base I candidate is trivalent**, from the census
  of `NonTrivalentValencyTwoBaseOneRows` (`nd(F) = 2` at the fold, `nd = 0` at
  every other leaf sheet, `nd(A_i) = 3` at the anchor's branch vertices,
  `nd(B_v) = nd(B)` at an ordinary block) plus trivalence of the datum away from
  the wall.
* `incident_branchVertex_self`, `exists_isPathEnd_of_wall_end`,
  `hasPathEnds_candidate`: **`HasPathEnds` of the Base I candidate** from
  `HasPathEnds` of the datum it lives over.
* `outgoing_targetConnected`, `outgoing_targetGenus`, `outgoing_targetEdgeCard`,
  `outgoing_sourceGenus`: the outgoing target is connected of genus zero with as
  many edges as the incoming target, and the source genus is preserved through
  candidate, gauge and wall contraction.
* `noContractedReturnOffRow_two`: the weakened no-return condition of
  `LeafFacetNoReturn` at **every** two-valent wall (`2 + 2` through
  `StablePathFacetContraction.noContractedReturn_of_nonleaf`, `1 + 3` and
  `3 + 1` through the two leaf witnesses
  `NonTrivalentValencyTwoLeafDictionary.noContractedReturnOffRow_of_leaf` and
  `..._of_leaf_right`).
* `outgoing_trivalent`, `outgoing_pathEnds`, `det_chartLabelling_ne_zero`,
  `outgoingFD`: the outgoing `FullDimensionalSourcePresentation` on the incoming
  chart index type, every field produced.
* `wallOutgoingFD`, `typeChangeLink_of_receipts_baseOne`: the same at an
  `OuterWalk.WallData`, and the Base I inhabitant of `OuterWalk.TypeChangeLink`
  with `tracks` the only hypothesis.
* `exists_typeChangeLink_baseOne_of_wallData`: the headline, with no hypothesis
  about the candidate.  From the wall data and the incoming `TwoStar` alone it
  produces the anchor block and `nd(A) = 4`; given the caller's Configuration A
  dispatch data it produces the gauged datum, the Base I candidate, the outgoing
  presentation, the common minor in `OuterWalk.TypeChangeLink.agree`'s own
  shape, and the link itself as soon as `Tracks` is supplied.

## The hypotheses that remain explicit

1. `tracks : InteriorGraphTracking.Tracks (wallOutgoingFD …) (graph.move m) label`:
   the dart-level dictionary between the candidate's stable graph and the
   Whitehead move of the tracked ambient graph.  As in
   `NonTrivalentValencyTwoExit`, it is carried as a hypothesis here.
   `NonTrivalentValencyTwoBaseOneTracks.typeChangeLink_of_incidence` reduces it
   to the star count `hIncidence`, and `NonTrivalentValencyTwoBaseOneStarCount`
   discharges that count, so `tracks` needs no further input beyond (H-BaseI)
   and the wall data.  The *prescribed cross pairing* (`thickFirst`/`thinFirst`
   meeting at `A_1`) is a parameter of the headline, so a consumer matching the
   darts of `m` may choose it.
2. Configuration A (the `2 + 2` survivor split) and the two index equalities
   `|e_α| = |e_β|`, `|e_γ| = |e_δ|` stay the caller's **dispatch data**: Part II,
   Section 5.4, shows there is no Base I morphism at all when they fail
   (subcase `{v2-nd4-t3-k2<k3}` and the whole of Configuration B), so they are
   not hypotheses that could be discharged.  The Base II modules
   (`NonTrivalentValencyTwoExit`, `WallDatumPathEnds`) cover those cases.
3. The incoming `TwoStar` at the contracted wall, as in
   `NonTrivalentValencyTwoExit` and `WallDatumPathEnds`.
4. This module introduces **no new structure**; `TypeChangeLink` is inhabited by
   `typeChangeLink_of_receipts_baseOne` and `exists_typeChangeLink_baseOne_of_wallData`
   as soon as `tracks` is supplied, exactly as at Base II.

## Consumers

`OuterWalk.TypeChangeLink` (hence the `link` hypothesis of
`OuterWalk.coneEntry_of_reaches`) at Part II case `{v2-nd4}`, Configuration A,
outgoing Types I and II.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneExit

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionCoarseFine
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOne
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneRows
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneRowEquiv
open DraismaVargas.LocalCases.NonTrivalentValencyTwoGauge

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## 1.  The `t₃`-branch gauge carries the local census -/

section Gauge

variable (base : GluingDatum target degree) (star : TwoStar target wall)
  (anchor : WallBlock base wall) (thickSheet thinSheet : Fin degree)

/-- The gauge on source vertices, at the gauged datum's type. -/
noncomputable def gaugeVertexEquiv :
    base.SourceVertex ≃ (gaugedData base star anchor thickSheet thinSheet).SourceVertex :=
  (relabeling base star anchor thickSheet thinSheet).sourceVertexEquiv

/-- The gauge on source occurrences, at the gauged datum's type. -/
noncomputable def gaugeEdgeEquiv :
    base.SourceEdge ≃ (gaugedData base star anchor thickSheet thinSheet).SourceEdge :=
  (relabeling base star anchor thickSheet thinSheet).sourceEdgeEquiv

@[simp] theorem gaugeVertexEquiv_target (v : base.SourceVertex) :
    (gaugeVertexEquiv base star anchor thickSheet thinSheet v).1.1 = v.1.1 := rfl

@[simp] theorem gaugeVertexEquiv_symm_target
    (v : (gaugedData base star anchor thickSheet thinSheet).SourceVertex) :
    ((gaugeVertexEquiv base star anchor thickSheet thinSheet).symm v).1.1 = v.1.1 := rfl

/-- The gauge preserves the source genus: it is a relabelling, so both source
vertex sets and both source occurrence sets are equinumerous. -/
theorem genus_gaugedData :
    genus (gaugedData base star anchor thickSheet thinSheet).sourceGraph =
      genus base.sourceGraph := by
  classical
  have hV : Fintype.card (gaugedData base star anchor thickSheet thinSheet).SourceVertex =
      Fintype.card base.SourceVertex :=
    (Fintype.card_congr (gaugeVertexEquiv base star anchor thickSheet thinSheet)).symm
  have hE : Fintype.card (gaugedData base star anchor thickSheet thinSheet).SourceEdge =
      Fintype.card base.SourceEdge :=
    (Fintype.card_congr (gaugeEdgeEquiv base star anchor thickSheet thinSheet)).symm
  have hEdgeUp : Multiset.card base.sourceGraph.edges = Fintype.card base.SourceEdge := by
    simp [GluingDatum.sourceGraph]
  have hEdgeDown :
      Multiset.card (gaugedData base star anchor thickSheet thinSheet).sourceGraph.edges =
        Fintype.card (gaugedData base star anchor thickSheet thinSheet).SourceEdge := by
    simp [GluingDatum.sourceGraph]
  have hVertUp : Fintype.card base.sourceGraph.V = Fintype.card base.SourceVertex := rfl
  have hVertDown :
      Fintype.card (gaugedData base star anchor thickSheet thinSheet).sourceGraph.V =
        Fintype.card (gaugedData base star anchor thickSheet thinSheet).SourceVertex := rfl
  unfold genus
  rw [hEdgeUp, hEdgeDown, hVertUp, hVertDown, hV, hE]

variable (hConn : base.Connected)

include hConn in
theorem nonDanglingValency_gauge (v : base.SourceVertex) :
    nonDanglingValency (gaugedData base star anchor thickSheet thinSheet)
        (gaugeVertexEquiv base star anchor thickSheet thinSheet v) =
      nonDanglingValency base v :=
  SheetRelabelStable.nonDanglingValency_map (relabeling base star anchor thickSheet thinSheet)
    hConn v

/-- The gauge fixes the wall's own vertex partition, so the endpoint above a
sheet is carried to the endpoint above that same sheet. -/
theorem gauge_sourceEndpoint (y : Fin degree) :
    gaugeVertexEquiv base star anchor thickSheet thinSheet (base.sourceEndpoint wall y) =
      (gaugedData base star anchor thickSheet thinSheet).sourceEndpoint wall y := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · show (relabeling base star anchor thickSheet thinSheet).vertexPermutation wall
        ((base.vertexPartition wall).repr y) =
      ((gaugedData base star anchor thickSheet thinSheet).vertexPartition wall).repr y
    rw [gauge_vertexPermutation_wall base star anchor thickSheet thinSheet,
      gaugedData_vertexPartition_wall base star anchor thickSheet thinSheet]
    rfl

include hConn in
/-- **`OrdinaryTrivalent` transports across the gauge.**  The wall partition and
the anchor block are untouched, and the surviving valency at each sheet's
endpoint is unchanged. -/
theorem ordinaryTrivalent_gauged
    (hOrd : NonTrivalentValencyTwoRowEquiv.OrdinaryTrivalent base wall anchor) :
    NonTrivalentValencyTwoRowEquiv.OrdinaryTrivalent
      (gaugedData base star anchor thickSheet thinSheet) wall
      (gaugedAnchor base star anchor thickSheet thinSheet) := by
  intro y hY
  rw [gaugedAnchor_val, gaugedData_vertexPartition_wall base star anchor thickSheet thinSheet]
    at hY
  rw [← gauge_sourceEndpoint base star anchor thickSheet thinSheet y,
    nonDanglingValency_gauge base star anchor thickSheet thinSheet hConn]
  exact hOrd y hY

include hConn in
/-- **Trivalence away from the wall transports across the gauge.** -/
theorem trivalent_gauged_away
    (hAway : ∀ v : base.SourceVertex, v.1.1 ≠ wall → nonDanglingValency base v ≤ 3)
    (v : (gaugedData base star anchor thickSheet thinSheet).SourceVertex)
    (hv : v.1.1 ≠ wall) :
    nonDanglingValency (gaugedData base star anchor thickSheet thinSheet) v ≤ 3 := by
  have hEq := (gaugeVertexEquiv base star anchor thickSheet thinSheet).apply_symm_apply v
  rw [← hEq, nonDanglingValency_gauge base star anchor thickSheet thinSheet hConn]
  exact hAway _ (by rw [gaugeVertexEquiv_symm_target]; exact hv)

/-- The gauge on surviving occurrences, at the gauged datum's type. -/
noncomputable def gaugeNDEquiv :
    NonDanglingEdge base ≃ NonDanglingEdge (gaugedData base star anchor thickSheet thinSheet) :=
  SheetRelabelStable.nonDanglingEdgeEquiv (relabeling base star anchor thickSheet thinSheet)
    hConn

theorem gaugeNDEquiv_stablePath (g : NonDanglingEdge base) :
    (gaugeNDEquiv base star anchor thickSheet thinSheet hConn g).stablePath =
      NonTrivalentValencyTwoBaseOneRowDictionary.gaugeRowEquiv base star anchor thickSheet
        thinSheet hConn g.stablePath := rfl

include hConn in
/-- **`HasPathEnds` transports across the gauge.** -/
theorem hasPathEnds_gauged (hEnds : HasPathEnds base) :
    HasPathEnds (gaugedData base star anchor thickSheet thinSheet) := by
  classical
  intro e
  obtain ⟨f, V, hRow, hInc, hNd⟩ := hEnds
    ((gaugeNDEquiv base star anchor thickSheet thinSheet hConn).symm e)
  refine ⟨gaugeNDEquiv base star anchor thickSheet thinSheet hConn f,
    gaugeVertexEquiv base star anchor thickSheet thinSheet V, ?_, ?_, ?_⟩
  · rw [gaugeNDEquiv_stablePath, hRow, ← gaugeNDEquiv_stablePath, Equiv.apply_symm_apply]
  · exact (SheetRelabelPruning.incident_sourceEdgeEquiv_iff
      (relabeling base star anchor thickSheet thinSheet) f.1 V).mpr hInc
  · rw [nonDanglingValency_gauge base star anchor thickSheet thinSheet hConn]
    exact hNd

end Gauge

/-! ## 2.  Trivalence and path ends of the Base I candidate -/

section Candidate

variable {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall} (setup : BaseOneSetup data star anchor)

local notation "cand" => (validCandidate setup)

/-- Every source vertex over the old wall vertex is the leaf-layer vertex of its
own sheet. -/
theorem eq_leafVertex (v : (cand).datum.SourceVertex)
    (hv : v.1.1 = oldVertex target wall) : leafVertex setup v.1.2 = v :=
  (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hv.symm, rfl⟩

/-- Every source vertex over the new branch point is the branch-layer vertex of
its own sheet. -/
theorem eq_branchVertex (v : (cand).datum.SourceVertex)
    (hv : v.1.1 = freshVertex target) : branchVertex setup v.1.2 = v :=
  (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hv.symm, rfl⟩

/-- **The Base I candidate is trivalent.**  Above the new leaf `u` the only
non-empty star is the fold's, with `nd(F) = 2`; above the new branch point `v`
the anchor's sheets have `nd(A_i) = 3` and an ordinary block keeps its own
`nd(B)`; away from the wall the datum's trivalence descends. -/
theorem candidate_trivalent (hValid : data.Valid)
    (hOrd : NonTrivalentValencyTwoRowEquiv.OrdinaryTrivalent data wall anchor)
    (hAway : ∀ v : data.SourceVertex, v.1.1 ≠ wall → nonDanglingValency data v ≤ 3)
    (v : (cand).datum.SourceVertex) :
    nonDanglingValency (cand).datum v ≤ 3 := by
  classical
  rcases hcase : (v.1.1 : TargetExpansion.Vertex target) with place | u
  · by_cases hIsWall : place = wall
    · rw [← eq_leafVertex setup v (by rw [hcase, hIsWall]; rfl)]
      by_cases h1 : v.1.2 = setup.foldFirst
      · rw [h1, nonDanglingValency_leafVertex_fold setup hValid]
        omega
      · by_cases h2 : v.1.2 = setup.foldSecond
        · rw [h2, leafVertex_fold_eq setup, nonDanglingValency_leafVertex_fold setup hValid]
          omega
        · rw [nonDanglingValency_leafVertex_singleton setup hValid h1 h2]
          omega
    · obtain ⟨old, hOld, hRet⟩ :=
        ResolutionAwayFromWall.exists_retainedVertex_of_target (cand) v place hIsWall hcase
      rw [← hRet, ResolutionAwayFromWall.nonDanglingValency_retainedVertex (cand) hValid
        (candidate_sourceGenus setup) old (by rw [hOld]; exact hIsWall)]
      exact hAway old (by rw [hOld]; exact hIsWall)
  · cases u
    rw [← eq_branchVertex setup v (by rw [hcase]; rfl)]
    by_cases hAnchor : (data.vertexPartition wall).Rel anchor.1 v.1.2
    · rw [nonDanglingValency_branchVertex_anchor_sheet setup hValid hAnchor]
    · rw [nonDanglingValency_branchVertex_ordinary setup hValid hAnchor]
      exact hOrd v.1.2 hAnchor

/-- An old occurrence at the wall reaches the branch layer at its own sheet.  At
Base I this is where *every* old occurrence at the wall goes: the base tree
`T_∅` sends both old occurrences to the trivalent point `v`, so nothing at all
meets the new leaf `u` except the two fold occurrences. -/
theorem incident_branchVertex_self {old : data.SourceEdge}
    (hAt : old.1.1 ∈ GluingDatum.incidentEdges wall) :
    Incident (cand).datum ((cand).oldSourceEdge old) (branchVertex setup old.1.2) := by
  rw [incident_branchVertex_iff, BalancedGlobal.Candidate.oldSourceEdge_target,
    mem_incidentEdges_branch_old, BalancedGlobal.Candidate.oldSourceEdge_sheet]
  exact ⟨⟨hAt, candidate_right_apply setup old.1.1⟩, rfl⟩

/-- **A path end of the datum transports to a path end of the Base I candidate**,
on the retained row of the same occurrence.  Away from the wall the retained
vertex keeps its surviving valency; at the wall the retained occurrence lands on
the branch layer, where the anchor's sheets are trivalent and an ordinary block
keeps `nd(B)`. -/
theorem exists_isPathEnd_of_wall_end (hValid : data.Valid)
    {h : NonDanglingEdge data} {w : data.SourceVertex}
    (hInc : Incident data h.1 w) (hNd : nonDanglingValency data w ≠ 2) :
    ∃ (first : NonDanglingEdge (cand).datum) (vertex : (cand).datum.SourceVertex),
      first.stablePath =
          (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 h).stablePath ∧
        IsPathEnd (cand).datum first.1 vertex := by
  classical
  obtain ⟨hMem, hRel⟩ := (incident_iff_target_mem_and_rel data h.1 w).mp hInc
  by_cases hAt : w.1.1 = wall
  · rw [hAt] at hMem hRel
    have hVertex : data.sourceEndpoint wall h.1.1.2 = w :=
      (GluingDatum.sourceEndpoint_eq_iff data wall h.1.1.2 w).mpr ⟨hAt.symm, hRel.symm⟩
    refine ⟨ResolutionAwayFromWall.retainedEdge (cand) hValid.1 h,
      branchVertex setup h.1.1.2, rfl, incident_branchVertex_self setup hMem, ?_⟩
    by_cases hAnchor : (data.vertexPartition wall).Rel anchor.1 h.1.1.2
    · rw [nonDanglingValency_branchVertex_anchor_sheet setup hValid hAnchor]
      omega
    · rw [nonDanglingValency_branchVertex_ordinary setup hValid hAnchor, hVertex]
      exact hNd
  · refine ⟨ResolutionAwayFromWall.retainedEdge (cand) hValid.1 h,
      ResolutionAwayFromWall.retainedVertex (cand) w, rfl, ?_, ?_⟩
    · exact (ResolutionAwayFromWall.incident_oldSourceEdge_iff (cand) w hAt h.1).mpr hInc
    · rw [ResolutionAwayFromWall.nonDanglingValency_retainedVertex (cand) hValid
        (candidate_sourceGenus setup) w hAt]
      exact hNd

/-- **`HasPathEnds` of the Base I candidate.**  Through
`NonTrivalentValencyTwoBaseOneRowEquiv.rowEquiv` every stable row is the bridge
row -- whose occurrence `h_1` ends at the trivalent `A_1`, so it is a path end
outright -- or the retained row of a stable row of the datum. -/
theorem hasPathEnds_candidate (hValid : data.Valid) (hEnds : HasPathEnds data) :
    HasPathEnds (cand).datum := by
  classical
  intro e
  have hBack := (rowEquiv setup hValid).symm_apply_apply e.stablePath
  cases hCase : rowEquiv setup hValid e.stablePath with
  | none =>
    rw [hCase] at hBack
    have hRow : bridgeRow setup hValid = e.stablePath := hBack
    refine ⟨⟨(cand).newSourceEdge setup.foldFirst,
        newSourceEdge_foldFirst_survives setup hValid⟩,
      branchVertex setup setup.foldFirst, hRow, ?_, ?_⟩
    · exact bridgeEdge_incident_branch setup setup.foldFirst
    · rw [nonDanglingValency_branchVertex_anchor_sheet setup hValid setup.foldFirst_wall]
      omega
  | some r =>
    rw [hCase] at hBack
    have hRow : retainedRow setup hValid r = e.stablePath := hBack
    obtain ⟨g, hg⟩ := Quot.exists_rep r
    have hgr : NonDanglingEdge.stablePath g = r := hg
    obtain ⟨wallEdge, w, hRowW, hInc, hNd⟩ := hEnds g
    obtain ⟨first, vertex, hFirst, hEnd⟩ :=
      exists_isPathEnd_of_wall_end setup hValid hInc hNd
    refine ⟨first, vertex, ?_, hEnd⟩
    rw [hFirst, ← retainedRow_mk setup hValid wallEdge, hRowW, hgr, hRow]

end Candidate

/-! ## 3.  The outgoing full-dimensional presentation at an actual two-valent wall -/

section Wall

open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneRowDictionary

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
  (setup : BaseOneSetup
    (gaugedData (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet thinSheet)
    wallStar
    (gaugedAnchor (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet thinSheet))
  (hGauged : (gaugedData (contractDatum cover hc hab hOne) wallStar anchorBlk
    thickSheet thinSheet).Valid)

/-! ### The outgoing target -/

include fd in
theorem outgoing_targetConnected :
    graph_connected (TargetExpansion.graph (contract targetIn hab hOne) ⟨a, hab⟩
      (validCandidate setup).right) :=
  TargetExpansion.graph_connected (contract targetIn hab hOne) ⟨a, hab⟩ _
    (NonTrivalentUniqueFourValent.wall_target_connected cover fd hab hOne)

include fd in
theorem outgoing_targetGenus :
    genus (TargetExpansion.graph (contract targetIn hab hOne) ⟨a, hab⟩
      (validCandidate setup).right) = 0 :=
  (TargetExpansion.graph_genus (contract targetIn hab hOne) ⟨a, hab⟩ _).trans
    (NonTrivalentUniqueFourValent.wall_target_genus cover fd hab hOne)

theorem outgoing_targetEdgeCard :
    (TargetExpansion.graph (contract targetIn hab hOne) ⟨a, hab⟩
      (validCandidate setup).right).edges.card = targetIn.edges.card :=
  (TargetExpansion.graph_edge_card (contract targetIn hab hOne) ⟨a, hab⟩ _).trans
    (WallDegeneration.edge_card_contract hab hOne).symm

include hForest in
/-- **The Base I candidate preserves the incoming source genus.**  The candidate
preserves the gauged datum's genus, the gauge is a relabelling, and the wall
contraction loses one source vertex and one source occurrence in every fibre. -/
theorem outgoing_sourceGenus :
    genus (validCandidate setup).datum.sourceGraph = genus cover.sourceGraph :=
  (candidate_sourceGenus setup).trans
    ((genus_gaugedData (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet
      thinSheet).trans
      (NonTrivalentValencyTwoExit.genus_sourceGraph_contractDatum cover hc hab hOne hForest))

/-! ### The weakened no-return condition at every two-valent wall -/

include hc hab hOne wallStar coordinates hZeroCoord hPosCoord hFacetZero in
/-- **`NoContractedReturnOffRow` holds at every two-valent wall**, with no
sub-case hypothesis.  `val(w_0) = val(u) + val(v) - 2 = 2` splits into `2 + 2`
(neither endpoint a leaf, where even the strong `NoContractedReturn` holds by
`StablePathFacetContraction.noContractedReturn_of_nonleaf`), `1 + 3` and `3 + 1`
(the leaf-fold argument of `LeafFacetNoReturn`, and its mirror image in
`NonTrivalentValencyTwoLeafDictionary`). -/
theorem noContractedReturnOffRow_two :
    LeafFacetNoReturn.NoContractedReturnOffRow cover contracted
      (fd.labelling.row.symm facet) := by
  classical
  by_cases hA : (GluingDatum.incidentEdges a).card = 1
  · exact NonTrivalentValencyTwoLeafDictionary.noContractedReturnOffRow_of_leaf cover fd hc
      hab hOne wallStar coordinates facet hZeroCoord hPosCoord hFacetZero hA
  · by_cases hB : (GluingDatum.incidentEdges b).card = 1
    · exact NonTrivalentValencyTwoLeafDictionary.noContractedReturnOffRow_of_leaf_right cover
        fd hc hab hOne wallStar coordinates facet hZeroCoord hPosCoord hFacetZero hB
    · have hLeftMem := (WallProgress.endpoints_of_contraction cover hc hab hOne fd.valid
        fd.changeMinimal).2.1
      have hRightMem := (WallProgress.endpoints_of_contraction cover hc hab hOne fd.valid
        fd.changeMinimal).2.2.2.1
      have hLeft : 2 ≤ (GluingDatum.incidentEdges a).card := by omega
      have hRight : 2 ≤ (GluingDatum.incidentEdges b).card := by omega
      exact LeafFacetNoReturn.noContractedReturnOffRow_of_noContractedReturn cover contracted
        (fd.labelling.row.symm facet)
        (noContractedReturn_of_nonleaf cover fd hc hLeft hRight)

/-! ### Trivalence, path ends and nonsingularity -/

include fd hForest hGauged in
/-- **The outgoing candidate is trivalent**, from the census of
`NonTrivalentValencyTwoBaseOneRows` transported across the gauge: `nd(F) = 2` at
the fold, `nd = 0` at every other leaf sheet,
`nd(A_i) = 3` at the anchor's branch vertices, `nd(B_v) = nd(B)` at an ordinary
block, and the wall datum's own trivalence away from the anchor. -/
theorem outgoing_trivalent
    (hOrd : NonTrivalentValencyTwoRowEquiv.OrdinaryTrivalent
      (contractDatum cover hc hab hOne) ⟨a, hab⟩ anchorBlk)
    (v : (validCandidate setup).datum.SourceVertex) :
    nonDanglingValency (validCandidate setup).datum v ≤ 3 :=
  candidate_trivalent setup hGauged
    (ordinaryTrivalent_gauged (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet
      thinSheet (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest).1 hOrd)
    (trivalent_gauged_away (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet
      thinSheet (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest).1
      (fun w hw ↦ NonTrivalentValencyTwoExit.wallDatum_trivalent_away cover fd hc hab hOne
        hForest w hw))
    v

include hForest hZeroCoord hPosCoord hFacetZero hGauged in
/-- **`HasPathEnds` of the outgoing candidate**, from the wall-datum path ends of
`WallDatumPathEnds` transported across the gauge and then through the Base I row
dictionary.  Base I needs no ordinary-block adjustment: every old occurrence at
the wall reaches the branch layer, and both anchor branch vertices are
trivalent. -/
theorem outgoing_pathEnds
    (hNoReturn : LeafFacetNoReturn.NoContractedReturnOffRow cover contracted
      (fd.labelling.row.symm facet)) :
    HasPathEnds (validCandidate setup).datum :=
  hasPathEnds_candidate setup hGauged
    (hasPathEnds_gauged (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet
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
        thinSheet labelling₀ setup hGauged).presentation).det ≠ 0 :=
  NonTrivalentLinkMatrix.det_ne_zero
    (agreeOffColumn_chartLabelling cover fd hc hab hOne hForest facet wallStar anchorBlk
      thickSheet thinSheet labelling₀ setup hGauged coordinates hZeroCoord hPosCoord
      hFacetZero hRowVal hMatrixWall)
    (fun j hj ↦ NonTrivalentValencyTwoExit.incoming_facet_eq_zero cover fd coordinates facet
      hZeroCoord hPosCoord hFacetZero j hj)
    (fun j hj ↦ matrix_chartLabelling_facet_eq_zero cover fd hc hab hOne hForest facet
      wallStar anchorBlk thickSheet thinSheet labelling₀ setup hGauged j hj)
    fd.det_ne_zero
    (matrix_chartLabelling_corner_pos cover fd hc hab hOne hForest facet wallStar anchorBlk
      thickSheet thinSheet labelling₀ setup hGauged).ne'

/-- **The outgoing full-dimensional source presentation of a Base I candidate at
an actual two-valent wall.**  Every field is produced: validity, the outgoing
target's connectivity, genus and edge count, source-genus preservation,
saturation (from the incoming presentation, through
`NonTrivalentValencyTwoExit.ofTypeChange`), the honest labelling on the incoming
chart, nonsingularity, trivalence and path ends. -/
def outgoingFD
    (hOrd : NonTrivalentValencyTwoRowEquiv.OrdinaryTrivalent
      (contractDatum cover hc hab hOne) ⟨a, hab⟩ anchorBlk)
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
    FullDimensionalSourcePresentation (validCandidate setup).datum coordinate :=
  NonTrivalentValencyTwoExit.ofTypeChange fd
    (validCandidate_datum_valid setup hGauged)
    (outgoing_targetConnected cover fd hc hab hOne wallStar anchorBlk thickSheet thinSheet
      setup)
    (outgoing_targetGenus cover fd hc hab hOne wallStar anchorBlk thickSheet thinSheet setup)
    (outgoing_targetEdgeCard cover hc hab hOne wallStar anchorBlk thickSheet thinSheet setup)
    (outgoing_sourceGenus cover hc hab hOne hForest wallStar anchorBlk thickSheet thinSheet
      setup)
    (chartLabelling cover fd hc hab hOne hForest facet wallStar anchorBlk thickSheet
      thinSheet labelling₀ setup hGauged)
    (det_chartLabelling_ne_zero cover fd hc hab hOne hForest coordinates facet hZeroCoord
      hPosCoord hFacetZero wallStar anchorBlk thickSheet thinSheet labelling₀ setup hGauged
      hRowVal hMatrixWall)
    (outgoing_trivalent cover fd hc hab hOne hForest wallStar anchorBlk thickSheet thinSheet
      setup hGauged hOrd)
    (outgoing_pathEnds cover fd hc hab hOne hForest coordinates facet hZeroCoord hPosCoord
      hFacetZero wallStar anchorBlk thickSheet thinSheet setup hGauged hNoReturn)

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
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneRowDictionary

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
  (setup : BaseOneSetup
    (gaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      thickSheet thinSheet) wallStar
    (gaugedAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      thickSheet thinSheet))
  (hGauged : (gaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
    thickSheet thinSheet).Valid)
  (hOrd : NonTrivalentValencyTwoRowEquiv.OrdinaryTrivalent
    (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk)
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

/-- The outgoing Base I presentation at the wall data of the outer walk. -/
def wallOutgoingFD :
    FullDimensionalSourcePresentation (validCandidate setup).datum coordinate :=
  outgoingFD wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m) wd.coordinates
    (label m.base) wd.hZeroCoord wd.hPosCoord wd.hFacetZero wallStar anchorBlk thickSheet
    thinSheet labelling₀ setup hGauged hOrd
    (noContractedReturnOffRow_two wd.cover wd.fullDim wd.hc wd.hab wd.hOne wd.coordinates
      (label m.base) wd.hZeroCoord wd.hPosCoord wd.hFacetZero wallStar)
    hRowVal hMatrixWall

/-- **The Base I inhabitant of `OuterWalk.TypeChangeLink` at a two-valent wall.**
The base of the outgoing payload is the gauged wall datum of
`NonTrivalentValencyTwoGauge` (Base I needs the `t_3`-branch alignment gauge, so
`TypeChangeLink.base` is *not* the wall datum itself), the candidate is the
Base I member of `NonTrivalentValencyTwoBaseOne`, the presentation is
`wallOutgoingFD` and the common minor is
`NonTrivalentValencyTwoBaseOneRowDictionary.agreeOffColumn_chartLabelling`.
`tracks` is the only hypothesis left. -/
def typeChangeLink_of_receipts_baseOne
    (tracks : Tracks (wallOutgoingFD m wd wallStar anchorBlk thickSheet thinSheet labelling₀
      setup hGauged hOrd hRowVal hMatrixWall) (graph.move m) label) :
    TypeChangeLink m wd where
  base := gaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
    thickSheet thinSheet
  baseValid := hGauged
  candidate := validCandidate setup
  outgoingFD := wallOutgoingFD m wd wallStar anchorBlk thickSheet thinSheet labelling₀ setup
    hGauged hOrd hRowVal hMatrixWall
  tracks := tracks
  agree := by
    have h := agreeOffColumn_chartLabelling wd.cover wd.fullDim wd.hc wd.hab wd.hOne
      (wd.hForest m) (label m.base) wallStar anchorBlk thickSheet thinSheet labelling₀ setup
      hGauged wd.coordinates wd.hZeroCoord wd.hPosCoord wd.hFacetZero hRowVal hMatrixWall
    rw [wd.targetEdge_symm_contracted] at h
    exact h

end

end Link

/-! ## 5.  The headline at the wall data, with no hypothesis about the candidate -/

section Headline

open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneRowDictionary

noncomputable section

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {deg : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival deg graph label (label m.base)}
  (wd : WallData arrival)

/-- **The Base I type-changing exit at a two-valent wall of the outer walk, with
no hypothesis about the candidate.**  From the wall data alone (and the incoming
two-valent star) this produces the anchor block and `nd(A) = 4`; then, given the
caller's Configuration A dispatch data -- the `2 + 2` survivor split and the
prescribed cross pairing with its two index equalities `|e_α| = |e_β|`,
`|e_γ| = |e_δ|`, which is exactly Part II's condition (Section 5.4) for a Base I
morphism to exist -- it produces the gauged datum of `NonTrivalentValencyTwoGauge`,
the Base I candidate of `NonTrivalentValencyTwoBaseOne` over it, the outgoing
`FullDimensionalSourcePresentation` on the
incoming chart, the common minor `AgreeOffColumn` that
`OuterWalk.TypeChangeLink.agree` asks for, and the link itself as soon as
`InteriorGraphTracking.Tracks` is supplied. -/
theorem exists_typeChangeLink_baseOne_of_wallData
    (wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    ∃ anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩,
      nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            ⟨wd.a, wd.hab⟩ anchorBlock) = 4 ∧
      ∀ (_ : ∀ direction : Fin 2,
          (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
            anchorBlock direction).card = 2)
        (thickFirst thickSecond thinFirst thinSecond :
          IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
              ⟨wd.a, wd.hab⟩ anchorBlock)),
        thickFirst ∈ directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            wallStar anchorBlock 0 →
        thickSecond ∈ directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            wallStar anchorBlock 0 →
        thinFirst ∈ directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            wallStar anchorBlock 1 →
        thinSecond ∈ directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            wallStar anchorBlock 1 →
        thickFirst ≠ thickSecond → thinFirst ≠ thinSecond →
        (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex thickFirst.1 =
            (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex thinFirst.1 →
        (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex thickSecond.1 =
            (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex thinSecond.1 →
        ∃ (gauged : BaseOneSetup
            (gaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlock
              (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)) wallStar
            (gaugedAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlock
              (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)))
          (out : FullDimensionalSourcePresentation (validCandidate gauged).datum coordinate),
          AgreeOffColumn wd.incomingMatrix
              (GluingDatum.LengthMatrixPresentation.matrix out.labelling.presentation)
              wd.column ∧
            ∀ _tracks : Tracks out (graph.move m) label, Nonempty (TypeChangeLink m wd) := by
  classical
  obtain ⟨anchorBlock, hNd, hRest⟩ :=
    NonTrivalentValencyTwoBaseOneRowEquiv.exists_rowEquiv_of_wall_metric wd.cover wd.fullDim
      wd.hc wd.hab wd.hOne (wd.hForest m) (wd.hCompat m) wallStar wd.coordinates
      (label m.base) wd.hRows wd.hZeroCoord wd.hPosCoord wd.hFacetZero
  have hOrd := NonTrivalentValencyTwoRowEquiv.ordinaryTrivalent_of_wall_metric wd.cover
    wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m) wallStar wd.coordinates (label m.base)
    wd.hRows wd.hZeroCoord anchorBlock hNd
  obtain ⟨labelling₀, hRowVal, hMatrixWall⟩ :=
    exists_wallLabelling_two wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m)
      (label m.base) wallStar wd.coordinates wd.hRows wd.hZeroCoord wd.hPosCoord
      wd.hFacetZero
  refine ⟨anchorBlock, hNd, ?_⟩
  intro hSplit thickFirst thickSecond thinFirst thinSecond hTF hTS hNF hNS hTNe hNNe
    hIndexFirst hIndexSecond
  obtain ⟨gauged, hGauged, -⟩ :=
    hRest hSplit thickFirst thickSecond thinFirst thinSecond hTF hTS hNF hNS hTNe hNNe
      hIndexFirst hIndexSecond
  refine ⟨gauged,
    wallOutgoingFD m wd wallStar anchorBlock (occurrenceSheet thickFirst)
      (occurrenceSheet thinFirst) labelling₀ gauged hGauged hOrd hRowVal hMatrixWall,
    ?_, ?_⟩
  · have h := agreeOffColumn_chartLabelling wd.cover wd.fullDim wd.hc wd.hab wd.hOne
      (wd.hForest m) (label m.base) wallStar anchorBlock (occurrenceSheet thickFirst)
      (occurrenceSheet thinFirst) labelling₀ gauged hGauged wd.coordinates wd.hZeroCoord
      wd.hPosCoord wd.hFacetZero hRowVal hMatrixWall
    rw [wd.targetEdge_symm_contracted] at h
    exact h
  · exact fun tracks ↦ ⟨typeChangeLink_of_receipts_baseOne m wd wallStar anchorBlock
      (occurrenceSheet thickFirst) (occurrenceSheet thinFirst) labelling₀ gauged hGauged
      hOrd hRowVal hMatrixWall tracks⟩

end

end Headline

end DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneExit
