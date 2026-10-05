module

public import DraismaVargas.LocalCases.WallDatumPathEnds
public import DraismaVargas.LocalCases.MovedIncidenceIso
public import DraismaVargas.LocalCases.WallSplitIncidence

@[expose] public section

/-!
# The vertex dictionary of the valency-two Base II type change, and (H-II)

Source: Vargas, Part II, Section 5.1 (a combinatorial type change is recorded
as a Whitehead move on the *ambient* tracked graph; the labelling convention
(1)) and Section 5.4, case `{v2-nd4}` (Base II = the base tree `T_2` of Part I,
Case `{w2-r2}`, both new target endpoints divalent; Configuration A `2 + 2` with
its three subcases, and Configuration B `3 + 1`), together with Draisma--Vargas
Part I's stable graph `H(M)` with its row labels (the definition of
non-dangling valency and the subsection on inherited properties of limits) and
its `lemma-ndval-of-GqA0`.

This module supplies the vertex half of the `tracks` field of the valency-two
Base II link: it ports `NonTrivalentValencyThreeTracks` from a three-valent to a
two-valent wall.  `NonTrivalentValencyTwoExit` provides the outgoing
presentation and `typeChangeLink_of_receipts`, with the merged pair as the
explicit parameter `sel`; `WallDatumPathEnds.typeChangeLink_of_receipts'`
removes its `hPathEnds` receipt; and `WallSplitIncidence` and
`MovedIncidenceIso` provide the two valency-agnostic halves of `tracks`.  What
`MovedIncidenceIso.tracksOfMovedIncidence` still needs is a branch-vertex
bijection `vertexEquiv : BranchVertex cand.datum ≃ V` and the star count
`hIncidence` against the *permuted* vertex map of `graph.move m`.  This module
delivers the bijection, the hypothesis (H-II) that pins the anchor half of the
star count, and the wall-side geometry both rest on.

## What is proved

### 0.  Which side of an ordinary wall block keeps its star

At a two-valent wall the outgoing base tree *subdivides* the wall vertex, so --
unlike at a three-valent wall -- every ordinary wall block `B` is split into two
endpoint vertices, one per side of the new target edge.

* `ordinaryStar_congr`, `ordSide_congr`, `endpointVertex_eq_ordinary`: the side
  chooser and the endpoint vertices only see the wall block of a sheet.
* `nonDanglingValency_endpointVertex_branchSide`: the side
  `!NonTrivalentValencyTwoRowEquiv.ordSide` keeps the *whole* surviving valency
  of `B`, and `nonDanglingValency_endpointVertex_ordSide_le`: the other side is
  at most divalent.  (`ordSide` is the smaller side -- the one along which `B`'s
  new occurrence continues -- so with `|star_u| + |star_v| = nd(B) <= 3` the
  split is `3+0` or `2+1` and the larger side, plus the new occurrence when it
  survives, always totals `nd(B)`.)  Hence a trivalent ordinary block
  contributes **exactly one** branch vertex to the candidate.

### 1.  The vanishing occurrence

* `facetRow`, `facetEdge`: the vanishing row of the incoming cover is the chart
  row of the move's contracted dart, and it has a surviving occurrence.
* `nonDanglingValency_ne_two_of_incident_facetRow`,
  `three_le_nonDanglingValency_end`: **its ends are branch vertices.**  A
  divalent end would carry a second surviving occurrence on the same row, hence
  a second surviving occurrence over the contracted target occurrence, which
  `NoContractedReturn` forbids.  At valency three
  `NonTrivalentValencyThreeRowDictionary.noContractedReturn_of_threeStar`
  discharges that predicate outright; at a two-valent wall it is **carried as
  the hypothesis `hNoReturn`, which is already a binder of
  `NonTrivalentValencyTwoExit.wallOutgoingFD`**, so no new receipt appears (see
  "What is not proved here", item 3).
* `eq_facetEdge`: consequently the vanishing row is that single occurrence
  `h_1`; `leftEnd`, `rightEnd` are its two ends (`A_u`, `A_v` upstairs).

### 2.  The anchor

* `four_le_nonDanglingValency_map_leftEnd` and
  `sourceVertexMap_leftEnd_eq_anchorVertex`: **the vanishing occurrence lies
  over the anchor.**  `lemma-ndval-of-GqA0`
  (`WallSplitIncidence.nonDanglingValency_eq_sum_activeFibre`) gives
  `nd(W) >= 4` at the image of `leftEnd`, while every other wall block is
  trivalent -- `NonTrivalentValencyTwoRowEquiv.OrdinaryTrivalent`, which
  `NonTrivalentValencyTwoExit.exists_anchor_of_wallData` produces at an actual
  wall with no receipt.
* `eq_leftEnd_or_eq_rightEnd_of_mem_activeFibre`: **the anchor fibre carries
  exactly `leftEnd` and `rightEnd` as branch vertices**, because
  `nd(A) = 4 = 2 + sum (nd(V) - 2)`
  (`NonTrivalentValencyTwoRows.nonDanglingValency_anchor`) and each summand is
  `0` or `1`.
* `wallDatum_trivalent_away_anchor`: the wall datum is trivalent away from the
  anchor, off the merged vertex by
  `NonTrivalentValencyTwoExit.wallDatum_trivalent_away` and at an ordinary
  block by `OrdinaryTrivalent`.
* `branchEquivAnchorComplement`: the branch-vertex dictionary of
  `WallSplitIncidence`
  `{v : BranchVertex M // v <> leftEnd, rightEnd} ~ {w : BranchVertex M_0 // w <> A}`
  **with the `hFibre` hypothesis removed**: the proof only needs the branch pair
  above, not the full fibre `activeFibreVertices A = {leftEnd, rightEnd}`, which
  is *not* available at a two-valent wall either (see "What is not proved
  here").

### 3.  The branch vertices of the candidate

* `branchSide`, `candVertex`: the outgoing vertex over a wall-datum vertex other
  than the anchor -- `endpointVertex (branchSide x) x` over the merged target
  vertex, `ResolutionAwayFromWall.retainedVertex` away from it -- and
  `nonDanglingValency_candVertex`: its surviving valency is unchanged.
* `candBranchMap`, `candBranchEquiv`: **the branch vertices of the Base II
  candidate are the branch vertices of the wall datum other than the anchor,
  plus `A_u` and `A_v`.**  Surjectivity reads the case analysis of
  `NonTrivalentValencyTwoExit.candidate_trivalent` as a classification: over an
  ordinary block only the
  `branchSide` vertex can be a branch vertex, at the anchor the `u`-side classes
  other than the selected one are the divalent Configuration B subdivision
  vertices (`NonTrivalentValencyTwoRows.nonDanglingValency_extraEndpointVertex`)
  and both `A_u` and `A_v` are trivalent
  (`nonDanglingValency_endpointVertex`).

### 4.  `vertexEquiv`

* `coverBranchEquiv`, `vertexEquiv`: the composite
  `BranchVertex cand.datum ~ BranchVertex M_0-minus-A + Bool ~
   BranchVertex M-minus-ends + Bool ~ BranchVertex M ~ V`,
  the last step being the incoming tracking `wd.tracks.iso.vtx`.
* `vertexEquiv_anchor_false`, `vertexEquiv_anchor_true`: under (H-II)'s
  orientation, `A_u` goes to `graph.vert m.base` and `A_v` to
  `graph.vert (graph.op m.base)`; `vertexEquiv_inl` reads the rest as
  `sourceVertexMap` followed by the incoming tracking.

### 5.  (H-II)

* `PrescribedMergedMove m wd hNoReturn sel`: the two darts the Whitehead move
  places together with `m.base` -- the moved star of `graph.vert m.base` with
  `m.base` removed -- are, under `wd.tracks.iso.dart`, darts carrying the stable
  **rows** of the two thick-direction survivors that `sel` merges, in the
  orientation that puts `A_u` at `graph.vert m.base` (first conjunct: `m.base`
  is the dart of `h_1` at the `A_u` end).  The clause is at row level
  (`d.2.1.stablePath = ...`): a merged survivor may reach its end of `h_1`
  through a pass-through occurrence over the contracted target edge, and it is
  the row, not the occurrence, that the star count consumes
  (`IncomingPairing.label_dart_of_row`).  The other orientation is
  normalised by the caller with `CubicDartGraph.MoveData.swap`, which leaves
  `graph.move m` unchanged.
* `prescribedMergedMove_of_occurrence`: the old occurrence-level clause
  (`first.2.1 = selectedLift ...`) implies (H-II).
* `prescribedMergedMove_of_rows`: (H-II) from the orientation clause together
  with two moved darts carrying the two merged rows -- the shape
  `IncomingPairing.exists_movedStar_darts` produces, and the one the valency
  dispatcher consumes.  At row level separation is automatic
  (`IncomingPairing.vertex_of_movedStar_eq_pair`), so `MergedSeparated` is not a
  hypothesis of it.  **One
  clause covers both configurations**: the star of `A_u` is
  `{h_1, e_first, e_second}` in Configuration A (where the thick direction has
  exactly two survivors, so the pair is forced) and in Configuration B (where it
  has three and `sel` names the merged pair, the third reaching `A_v` through a
  divalent subdivision point).
* `MergedSeparated`: the geometric content of a *type change* -- the two merged
  survivors lift to occurrences at the two **different** ends of `h_1`.  Without
  it `A_u` sees exactly the star of `leftEnd` and no Whitehead move takes place.
* `prescribedMove` and `prescribedMergedMove_prescribedMove`: **non-vacuity of
  (H-II), in relative form.**  Given the orientation and `MergedSeparated`, the
  move that contracts the *same* edge as `m` and exchanges the merged survivor at
  the `A_v` end with the remaining dart at the `A_u` end satisfies (H-II).  (An
  absolute `exists m, PrescribedMergedMove m wd ...` does not typecheck:
  `wd : WallData arrival` with
  `arrival : FacetArrival degree graph label (label m.base)` fixes `m.base`, so
  the witness has to be produced with that same `base` field, which is what
  `prescribedMove` does.)

### 6.  Three pieces of the star count

* `move_vert_eq_iff_of_ne`: away from the two ends of the vanishing occurrence
  the Whitehead move does not change the star.
* `card_star_eq_incidenceCount`: the star of a branch vertex of the *incoming*
  cover, counted in the tracked ambient graph.
* `injective_retainedRow` and `incidenceCount_retainedVertex_retainedRow`:
  **away from the merged target vertex the candidate does not change the star.**

### 7.  The link, reduced to the star count

* `typeChangeLink_of_incidence`: **`OuterWalk.TypeChangeLink` at a two-valent
  wall from the star count alone.**  Feeding `vertexEquiv` to
  `MovedIncidenceIso.tracksOfMovedIncidence` and the result to
  `WallDatumPathEnds.typeChangeLink_of_receipts'` leaves exactly one geometric
  obligation, `hIncidence` (`hOp` is free from the incoming tracking through
  `MovedIncidenceIso.label_op_of_tracks`).

## What is not proved here: the receipts that remain

1. `hIncidence` and hence `tracks`: the star count
   `incidenceCount cand.datum v r =
    Nat.card {d // (graph.move m).vert d = vertexEquiv v and label d = row r}`.
   This composite is not proved in this file;
   `NonTrivalentValencyTwoStarCount` proves it, as the composite of two
   transports:
   * (T1) `incidenceCount M_0 w r =
     incidenceCount cand.datum (candVertex w) (retainedRow r)`.  Off the merged
     target vertex this is `incidenceCount_retainedVertex_retainedRow` above;
     **at an ordinary wall block** it is
     `NonTrivalentValencyTwoStarCount.incidenceCount_endpointVertex_branchSide_ordinary`,
     from the census of `NonTrivalentValencyTwoDescent`
     (`NonTrivalentValencyTwoDescent.nonDanglingIncident_endpointVertex_of_new_dangling`
     / `..._of_new_survives`, which list the star of the `branchSide` vertex as
     the retained copies of that side's `ordinaryStar` together with the block's
     one new occurrence when it survives, plus
     `stablePath_retainedEdge_eq_newSourceEdge`, which puts that new occurrence
     on the retained row of the survivor on the *other* side).
   * (T2) `incidenceCount M_0 w r =
     incidenceCount M (branchEquivAnchorComplement.symm w) (incomingRow r)`.
     Off the merged target vertex this is
     `WallSplitIncidence.incidenceCount_sourceVertexMap`; **at an ordinary wall
     block** it is the valency-agnostic
     `WallSplitIncidenceOrdinary.incidenceCount_unramified` (as at valency
     three, and again *not* a special case of
     `WallSplitIncidence.incidenceCount_anchor`, whose `hFacetOver` hypothesis
     fails there).
   At the anchor the count is the one (H-II) prescribes, together with the
   exact stars `NonTrivalentValencyTwoRows.nonDanglingIncident_endpointVertex_false`
   / `..._true` and `move_vert_eq_iff_of_ne` / `card_star_eq_incidenceCount` on
   the dart side; `NonTrivalentValencyTwoStarCount.typeChangeLink_of_prescribedMergedMove`
   packages the result as `OuterWalk.TypeChangeLink` at a two-valent `2 + 2`
   wall from (H-II) and `wallStar` alone.
2. `MergedSeparated`, and (H-II) itself.  (H-II) is the per-vertex match at the
   anchor; `MergedSeparated` is what makes the wall crossing an actual type
   change.  Neither is derived here.  With (H-II) stated at row level,
   `MergedSeparated` is a hypothesis of the relative witness only; the valency
   dispatcher discharges (H-II) through `prescribedMergedMove_of_rows`.
3. `hNoReturn : StablePathFacetContraction.NoContractedReturn wd.cover wd.contracted`,
   `wallStar : W2R1Target.TwoStar (contract wd.coverTarget wd.hab wd.hOne)
   <wd.a, wd.hab>`, `src`, `sel` and `hOrd` -- **exactly the binders of
   `NonTrivalentValencyTwoExit.wallOutgoingFD` and
   `WallDatumPathEnds.typeChangeLink_of_receipts'`**; nothing is added.
   `hNoReturn` is `NonTrivalentValencyTwoExit.noContractedReturn_of_two_two` in
   the `2 + 2` sub-case (neither end of the contracted target occurrence is a
   leaf of the incoming target tree), and it is genuinely *false* in the `1 + 3`
   leaf sub-case, where the weaker `LeafFacetNoReturn.NoContractedReturnOffRow`
   replaces it and the vanishing row is a path of two occurrences through a
   divalent vertex above the leaf.  `NonTrivalentValencyTwoTracksLeaf` restates
   §§1 and 5 above for that sub-case (the vanishing row's two outer ends replace
   its single occurrence's two ends) and hands the result to the no-return-free
   exit `NonTrivalentValencyTwoExitFree.typeChangeLink_of_receipts_free`.
4. `Function.Injective retainedRow` is proved here only through
   `NonTrivalentValencyTwoRowEquiv.rowEquiv`, i.e. under `hOrd`; no separate
   injectivity producer is added.

No structure is introduced.  The two `Prop` definitions ship as follows:
`PrescribedMergedMove` has the relative witness
`prescribedMergedMove_prescribedMove`; `MergedSeparated` is a named hypothesis
of that witness, in the same style as
`StablePathFacetContraction.NoContractedReturn`, and is not inhabited here.

## Used by

`NonTrivalentValencyTwoStarCount` proves (T1) and (T2) above at the
`2 + 2` wall and delivers `typeChangeLink_of_prescribedMergedMove`:
`OuterWalk.TypeChangeLink` from (H-II) and `wallStar` alone, via
`MovedIncidenceIso.tracksOfMovedIncidence` and hence the `tracks` field of
`WallDatumPathEnds.typeChangeLink_of_receipts'` and
`NonTrivalentValencyTwoExit.typeChangeLink_of_receipts`.
`NonTrivalentValencyTwoTracksLeaf` is the `1 + 3` / `3 + 1` sibling
that restates §§1 and 5 above instead of reusing them.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoTracks

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathCount
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.PrunedFibreValency
open DraismaVargas.LocalCases.PrunedFibreTree
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.ClassInjectivity
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk

noncomputable section

/-! ## 0.  Which side of an ordinary wall block keeps its star

At a two-valent wall the outgoing base tree subdivides the wall vertex, so a
wall block `B` other than the anchor is split into two endpoint vertices, one
per side of the new target edge.  The census of `NonTrivalentValencyTwoDescent`
(`NonTrivalentValencyTwoDescent.card_ordinaryStar_add`) says the two sides
partition `star(B)`, and `NonTrivalentValencyTwoRowEquiv.ordSide` names the
*smaller* side -- the one along which the block's new occurrence continues.
Below, the complementary side `!ordSide` is the one that keeps the whole
surviving valency, and the `ordSide` side is at most divalent.  Consequently a
trivalent ordinary block contributes exactly one branch vertex to the
candidate, which is what `candBranchEquiv` needs. -/

section OrdinarySide

open DraismaVargas.LocalCases.NonTrivalentValencyTwoRows
open DraismaVargas.LocalCases.NonTrivalentValencyTwoDescent
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRowEquiv

variable {target : CFGraph} {deg : ℕ} {wall : target.V}
  {data : GluingDatum target deg} {star : TwoStar target wall}
  {anchor : WallBlock data wall}
  (sel : Prescribed.Selection data star anchor)

/-- Both `ordinaryStar` and `ordSide` only see the wall block of a sheet. -/
theorem ordinaryStar_congr {x y : Fin deg}
    (hRel : (data.vertexPartition wall).Rel x y) (side : Bool) :
    ordinaryStar data star anchor x side = ordinaryStar data star anchor y side := by
  classical
  ext old
  rw [mem_ordinaryStar, mem_ordinaryStar, sourceEndpoint_eq_of_rel hRel]

theorem ordSide_congr {x y : Fin deg} (hRel : (data.vertexPartition wall).Rel x y) :
    ordSide data star anchor x = ordSide data star anchor y := by
  classical
  by_cases h : (ordinaryStar data star anchor y true).card <
      (ordinaryStar data star anchor y false).card
  · rw [ordSide_eq_true h, ordSide_eq_true (by
      rw [ordinaryStar_congr hRel true, ordinaryStar_congr hRel false]; exact h)]
  · rw [ordSide_eq_false h, ordSide_eq_false (by
      rw [ordinaryStar_congr hRel true, ordinaryStar_congr hRel false]; exact h)]

/-- Over an ordinary wall block the two endpoint vertices of the candidate are
compared through the *unchanged* wall partition. -/
theorem endpointVertex_eq_ordinary (side : Bool) {x y : Fin deg}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hRel : (data.vertexPartition wall).Rel x y) :
    endpointVertex sel side x = endpointVertex sel side y := by
  refine (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨rfl, ?_⟩
  refine Eq.trans ?_ (((Prescribed.validCandidate sel).datum.vertexPartition
    (if side then TargetExpansion.freshVertex target else
      TargetExpansion.oldVertex target wall)).rel_repr_right y)
  exact (candidate_vertexPartition_rel_ordinary sel side hX).mpr hRel

/-- **The side `!ordSide` keeps the whole surviving star of a trivalent
ordinary block.** -/
theorem nonDanglingValency_endpointVertex_branchSide (hValid : data.Valid) {x : Fin deg}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hLe : nonDanglingValency data (data.sourceEndpoint wall x) ≤ 3) :
    nonDanglingValency (Prescribed.validCandidate sel).datum
        (endpointVertex sel (!ordSide data star anchor x) x) =
      nonDanglingValency data (data.sourceEndpoint wall x) := by
  classical
  have hSum := card_ordinaryStar_add (data := data) (star := star) (anchor := anchor) x
  by_cases hDang : IsDangling (Prescribed.validCandidate sel).datum
      ((Prescribed.validCandidate sel).newSourceEdge x)
  · have hSplit : (ordinaryStar data star anchor x false).card = 0 ∨
        (ordinaryStar data star anchor x true).card = 0 := by
      by_contra hBad
      obtain ⟨hF, hT⟩ := not_or.mp hBad
      exact ((newSourceEdge_survives_iff_ordinary sel hValid hX).mpr ⟨hF, hT⟩) hDang
    by_cases hLt : (ordinaryStar data star anchor x true).card <
        (ordinaryStar data star anchor x false).card
    · rw [show (!ordSide data star anchor x) = false by rw [ordSide_eq_true hLt]; rfl,
        nonDanglingValency_endpointVertex_of_new_dangling sel hValid false hX hDang]
      omega
    · rw [show (!ordSide data star anchor x) = true by rw [ordSide_eq_false hLt]; rfl,
        nonDanglingValency_endpointVertex_of_new_dangling sel hValid true hX hDang]
      omega
  · obtain ⟨hF, hT⟩ := (newSourceEdge_survives_iff_ordinary sel hValid hX).mp hDang
    by_cases hLt : (ordinaryStar data star anchor x true).card <
        (ordinaryStar data star anchor x false).card
    · rw [show (!ordSide data star anchor x) = false by rw [ordSide_eq_true hLt]; rfl,
        nonDanglingValency_endpointVertex_of_new_survives sel hValid false hX hDang]
      omega
    · rw [show (!ordSide data star anchor x) = true by rw [ordSide_eq_false hLt]; rfl,
        nonDanglingValency_endpointVertex_of_new_survives sel hValid true hX hDang]
      omega

/-- **The side `ordSide` of a trivalent ordinary block is at most divalent**, so
it is never a branch vertex of the candidate. -/
theorem nonDanglingValency_endpointVertex_ordSide_le (hValid : data.Valid) {x : Fin deg}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hLe : nonDanglingValency data (data.sourceEndpoint wall x) ≤ 3) :
    nonDanglingValency (Prescribed.validCandidate sel).datum
      (endpointVertex sel (ordSide data star anchor x) x) ≤ 2 := by
  classical
  have hSum := card_ordinaryStar_add (data := data) (star := star) (anchor := anchor) x
  by_cases hDang : IsDangling (Prescribed.validCandidate sel).datum
      ((Prescribed.validCandidate sel).newSourceEdge x)
  · have hSplit : (ordinaryStar data star anchor x false).card = 0 ∨
        (ordinaryStar data star anchor x true).card = 0 := by
      by_contra hBad
      obtain ⟨hF, hT⟩ := not_or.mp hBad
      exact ((newSourceEdge_survives_iff_ordinary sel hValid hX).mpr ⟨hF, hT⟩) hDang
    by_cases hLt : (ordinaryStar data star anchor x true).card <
        (ordinaryStar data star anchor x false).card
    · rw [ordSide_eq_true hLt,
        nonDanglingValency_endpointVertex_of_new_dangling sel hValid true hX hDang]
      omega
    · rw [ordSide_eq_false hLt,
        nonDanglingValency_endpointVertex_of_new_dangling sel hValid false hX hDang]
      omega
  · obtain ⟨hF, hT⟩ := (newSourceEdge_survives_iff_ordinary sel hValid hX).mp hDang
    by_cases hLt : (ordinaryStar data star anchor x true).card <
        (ordinaryStar data star anchor x false).card
    · rw [ordSide_eq_true hLt,
        nonDanglingValency_endpointVertex_of_new_survives sel hValid true hX hDang]
      omega
    · rw [ordSide_eq_false hLt,
        nonDanglingValency_endpointVertex_of_new_survives sel hValid false hX hDang]
      omega

end OrdinarySide


variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)

/-! ## 1.  The vanishing row is a single occurrence between two branch vertices -/

/-- The vanishing stable row of the incoming cover. -/
def facetRow : StablePath wd.cover := wd.fullDim.labelling.row.symm (label m.base)

theorem over_contracted_of_facetRow (e : NonDanglingEdge wd.cover)
    (he : e.stablePath = facetRow m wd) : e.1.1.1 = wd.contracted :=
  LeafFacetNoReturn.facetRow_over_contracted wd.cover wd.fullDim wd.coordinates (label m.base)
    wd.hZeroCoord wd.hPosCoord wd.hFacetZero e he

theorem nonDanglingValency_ne_two_of_incident_facetRow
    (hNoReturn : NoContractedReturn wd.cover wd.contracted)
    (e : NonDanglingEdge wd.cover) (he : e.stablePath = facetRow m wd)
    (v : wd.cover.SourceVertex) (hv : Incident wd.cover e.1 v) :
    nonDanglingValency wd.cover v ≠ 2 := by
  classical
  intro hTwo
  obtain ⟨other, hNe, hPair⟩ := nonDanglingIncident_eq_pair wd.cover hTwo e.2 hv
  have hOtherMem : other ∈ nonDanglingIncident wd.cover v := by
    rw [hPair]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  obtain ⟨hOtherSurv, hOtherInc⟩ := (mem_nonDanglingIncident _ _ _).mp hOtherMem
  have hRow : NonDanglingEdge.stablePath
      (⟨other, hOtherSurv⟩ : NonDanglingEdge wd.cover) = e.stablePath :=
    PrunedFibreStablePath.stablePath_eq_of_incident_divalent wd.cover ⟨other, hOtherSurv⟩ e v
      hOtherInc hv hTwo
  have hOtherOver : other.1.1 = wd.contracted :=
    over_contracted_of_facetRow m wd (⟨other, hOtherSurv⟩ : NonDanglingEdge wd.cover)
      (hRow.trans he)
  exact hNe (hNoReturn v hTwo other e.1 hOtherOver (over_contracted_of_facetRow m wd e he)
    hOtherSurv e.2 hOtherInc hv)

theorem exists_facetEdge : ∃ e : NonDanglingEdge wd.cover, e.stablePath = facetRow m wd :=
  Quot.exists_rep _

/-- **The vanishing occurrence `h₁`.** -/
def facetEdge : NonDanglingEdge wd.cover := Classical.choose (exists_facetEdge m wd)

theorem facetEdge_stablePath : (facetEdge m wd).stablePath = facetRow m wd :=
  Classical.choose_spec (exists_facetEdge m wd)

theorem facetEdge_over_contracted : (facetEdge m wd).1.1.1 = wd.contracted :=
  over_contracted_of_facetRow m wd _ (facetEdge_stablePath m wd)

/-- The `A_u` end of the vanishing occurrence. -/
def leftEnd : wd.cover.SourceVertex := (wd.cover.sourceEnds (facetEdge m wd).1).1

/-- The `A_v` end of the vanishing occurrence. -/
def rightEnd : wd.cover.SourceVertex := (wd.cover.sourceEnds (facetEdge m wd).1).2

theorem incident_facetEdge_leftEnd : Incident wd.cover (facetEdge m wd).1 (leftEnd m wd) :=
  Or.inl rfl

theorem incident_facetEdge_rightEnd : Incident wd.cover (facetEdge m wd).1 (rightEnd m wd) :=
  Or.inr rfl

theorem leftEnd_ne_rightEnd : leftEnd m wd ≠ rightEnd m wd :=
  wd.cover.sourceEnds_ne (facetEdge m wd).1

/-- Both ends of the vanishing occurrence are branch vertices. -/
theorem three_le_nonDanglingValency_end
    (hNoReturn : NoContractedReturn wd.cover wd.contracted)
    (v : wd.cover.SourceVertex) (hv : Incident wd.cover (facetEdge m wd).1 v) :
    3 ≤ nonDanglingValency wd.cover v := by
  have hTwo := nonDanglingValency_ne_two_of_incident_facetRow m wd hNoReturn _
    (facetEdge_stablePath m wd) v hv
  have hOne := NonDanglingValency.nonDanglingValency_ne_one wd.cover wd.fullDim.connected v
  have hZero := nonDanglingValency_ne_zero_of_incident wd.cover (facetEdge m wd).2 hv
  omega

theorem nonDanglingValency_leftEnd_ne_two
    (hNoReturn : NoContractedReturn wd.cover wd.contracted) :
    nonDanglingValency wd.cover (wd.cover.sourceEnds (facetEdge m wd).1).1 ≠ 2 := by
  show nonDanglingValency wd.cover (leftEnd m wd) ≠ 2
  have := three_le_nonDanglingValency_end m wd hNoReturn (leftEnd m wd)
    (incident_facetEdge_leftEnd m wd)
  omega

theorem nonDanglingValency_rightEnd_ne_two
    (hNoReturn : NoContractedReturn wd.cover wd.contracted) :
    nonDanglingValency wd.cover (wd.cover.sourceEnds (facetEdge m wd).1).2 ≠ 2 := by
  show nonDanglingValency wd.cover (rightEnd m wd) ≠ 2
  have := three_le_nonDanglingValency_end m wd hNoReturn (rightEnd m wd)
    (incident_facetEdge_rightEnd m wd)
  omega

/-- **Uniqueness of the vanishing occurrence.** -/
theorem eq_facetEdge (hNoReturn : NoContractedReturn wd.cover wd.contracted)
    (e : NonDanglingEdge wd.cover) (he : e.stablePath = facetRow m wd) :
    e = facetEdge m wd :=
  NonTrivalentUniqueFourValent.eq_of_stablePath_eq_of_ends_ne_two (facetEdge m wd)
    (nonDanglingValency_leftEnd_ne_two m wd hNoReturn)
    (nonDanglingValency_rightEnd_ne_two m wd hNoReturn) e
    (he.trans (facetEdge_stablePath m wd).symm)

/-! ## 2.  The vanishing occurrence sits inside the anchor fibre -/

section Anchor

variable {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}

/-- The anchor of the wall datum: the four-valent merged source vertex. -/
def anchorVertex
    (anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex :=
  WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk

theorem nonDanglingValency_anchorVertex
    (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk) :
    nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (anchorVertex m wd anchorBlk) = 4 :=
  NonTrivalentValencyTwoRows.nonDanglingValency_anchor src

theorem leftEnd_target : (leftEnd m wd).1.1 = wd.a := by
  have h : (wd.cover.sourceEnds (facetEdge m wd).1).1.1.1 =
      ((facetEdge m wd).1.1.1 : wd.coverTarget.V × wd.coverTarget.V).1 :=
    sourceEnds_fst_fst wd.cover (facetEdge m wd).1
  show (wd.cover.sourceEnds (facetEdge m wd).1).1.1.1 = wd.a
  rw [h, facetEdge_over_contracted m wd]

theorem rightEnd_target : (rightEnd m wd).1.1 = wd.b := by
  have h : (wd.cover.sourceEnds (facetEdge m wd).1).2.1.1 =
      ((facetEdge m wd).1.1.1 : wd.coverTarget.V × wd.coverTarget.V).2 :=
    sourceEnds_snd_fst wd.cover (facetEdge m wd).1
  show (wd.cover.sourceEnds (facetEdge m wd).1).2.1.1 = wd.b
  rw [h, facetEdge_over_contracted m wd]

/-- Both ends of the vanishing occurrence lie in one fibre. -/
theorem sourceVertexMap_leftEnd_eq_rightEnd :
    sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (leftEnd m wd) =
      sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (rightEnd m wd) :=
  sourceVertexMap_sourceEnds_eq_of_contracted wd.cover wd.hc wd.hab wd.hOne
    (facetEdge m wd).1 (facetEdge_over_contracted m wd)

theorem leftEnd_mem_activeFibre :
    leftEnd m wd ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
      (sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (leftEnd m wd)) :=
  (mem_activeFibreVertices wd.cover wd.hc wd.hab wd.hOne _ _).mpr
    ⟨rfl, nonDanglingValency_ne_zero_of_incident wd.cover (facetEdge m wd).2
      (incident_facetEdge_leftEnd m wd)⟩

theorem rightEnd_mem_activeFibre :
    rightEnd m wd ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
      (sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (leftEnd m wd)) :=
  (mem_activeFibreVertices wd.cover wd.hc wd.hab wd.hOne _ _).mpr
    ⟨(sourceVertexMap_leftEnd_eq_rightEnd m wd).symm,
      nonDanglingValency_ne_zero_of_incident wd.cover (facetEdge m wd).2
        (incident_facetEdge_rightEnd m wd)⟩

/-- **The fibre of the vanishing occurrence is four-valent downstairs.** -/
theorem four_le_nonDanglingValency_map_leftEnd
    (hNoReturn : NoContractedReturn wd.cover wd.contracted) :
    4 ≤ nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (leftEnd m wd)) := by
  classical
  have hSum := WallSplitIncidence.nonDanglingValency_eq_sum_activeFibre wd.cover wd.hc wd.hab
    wd.hOne (wd.hCompat m) (wd.hForest m)
    (sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (leftEnd m wd))
    ⟨leftEnd m wd, leftEnd_mem_activeFibre m wd⟩
  set fibre := activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
    (sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (leftEnd m wd)) with hfibre
  have hNonneg : ∀ u ∈ fibre, (0 : ℤ) ≤ (nonDanglingValency wd.cover u : ℤ) - 2 := by
    intro u hu
    have := WallSplitIncidence.two_le_nonDanglingValency_of_mem_activeFibre wd.cover wd.hc wd.hab
      wd.hOne wd.fullDim.connected _ u hu
    omega
  have hPair : ({leftEnd m wd, rightEnd m wd} : Finset wd.cover.SourceVertex) ⊆ fibre := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact leftEnd_mem_activeFibre m wd
    · exact rightEnd_mem_activeFibre m wd
  have hLe := Finset.sum_le_sum_of_subset_of_nonneg hPair (fun u hu _ ↦ hNonneg u hu)
  rw [Finset.sum_pair (leftEnd_ne_rightEnd m wd)] at hLe
  have hL := three_le_nonDanglingValency_end m wd hNoReturn _ (incident_facetEdge_leftEnd m wd)
  have hR := three_le_nonDanglingValency_end m wd hNoReturn _ (incident_facetEdge_rightEnd m wd)
  omega

/-- **The vanishing occurrence lies over the anchor.** -/
theorem sourceVertexMap_leftEnd_eq_anchorVertex
    (hNoReturn : NoContractedReturn wd.cover wd.contracted)
    (hOrd : NonTrivalentValencyTwoRowEquiv.OrdinaryTrivalent
      (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk) :
    sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (leftEnd m wd) =
      anchorVertex m wd anchorBlk := by
  classical
  have hMap : sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (leftEnd m wd) =
      (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEndpoint
        (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) (leftEnd m wd).1.2 := by
    show (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEndpoint
        (GraphContraction.fold wd.coverTarget wd.hab (leftEnd m wd).1.1) (leftEnd m wd).1.2 = _
    rw [leftEnd_target m wd, GraphContraction.fold_a]
  have hFour := four_le_nonDanglingValency_map_leftEnd m wd hNoReturn
  rw [hMap] at hFour
  by_cases hRel : ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
      (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)).Rel anchorBlk.1
        (leftEnd m wd).1.2
  · rw [hMap]
    exact (NonTrivalentValencyTwoRowEquiv.sourceEndpoint_eq_of_rel hRel).symm
  · exact absurd (hOrd (leftEnd m wd).1.2 hRel) (by omega)

/-- **The anchor fibre carries exactly the two ends of the vanishing
occurrence as branch vertices.** -/
theorem eq_leftEnd_or_eq_rightEnd_of_mem_activeFibre
    (hNoReturn : NoContractedReturn wd.cover wd.contracted)
    (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hOrd : NonTrivalentValencyTwoRowEquiv.OrdinaryTrivalent
      (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk)
    (u : wd.cover.SourceVertex)
    (hu : u ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne (anchorVertex m wd anchorBlk))
    (hThree : 3 ≤ nonDanglingValency wd.cover u) :
    u = leftEnd m wd ∨ u = rightEnd m wd := by
  classical
  by_contra hBad
  obtain ⟨hBadL, hBadR⟩ := not_or.mp hBad
  have hSum := WallSplitIncidence.nonDanglingValency_eq_sum_activeFibre wd.cover wd.hc wd.hab
    wd.hOne (wd.hCompat m) (wd.hForest m) (anchorVertex m wd anchorBlk) ⟨u, hu⟩
  rw [nonDanglingValency_anchorVertex m wd src] at hSum
  have hL : leftEnd m wd ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
      (anchorVertex m wd anchorBlk) := by
    rw [← sourceVertexMap_leftEnd_eq_anchorVertex m wd hNoReturn hOrd]
    exact leftEnd_mem_activeFibre m wd
  have hR : rightEnd m wd ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
      (anchorVertex m wd anchorBlk) := by
    rw [← sourceVertexMap_leftEnd_eq_anchorVertex m wd hNoReturn hOrd]
    exact rightEnd_mem_activeFibre m wd
  have hNonneg : ∀ w ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
      (anchorVertex m wd anchorBlk), (0 : ℤ) ≤ (nonDanglingValency wd.cover w : ℤ) - 2 := by
    intro w hw
    have := WallSplitIncidence.two_le_nonDanglingValency_of_mem_activeFibre wd.cover wd.hc wd.hab
      wd.hOne wd.fullDim.connected _ w hw
    omega
  have hTriple : ({leftEnd m wd, rightEnd m wd, u} : Finset wd.cover.SourceVertex) ⊆
      activeFibreVertices wd.cover wd.hc wd.hab wd.hOne (anchorVertex m wd anchorBlk) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hL
    · exact hR
    · exact hu
  have hLe := Finset.sum_le_sum_of_subset_of_nonneg hTriple (fun w hw _ ↦ hNonneg w hw)
  rw [show ({leftEnd m wd, rightEnd m wd, u} : Finset wd.cover.SourceVertex) =
      insert (leftEnd m wd) {rightEnd m wd, u} from rfl,
    Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact not_or.mpr ⟨leftEnd_ne_rightEnd m wd, fun h ↦ hBadL h.symm⟩),
    Finset.sum_pair (fun h ↦ hBadR h.symm)] at hLe
  have hLv := three_le_nonDanglingValency_end m wd hNoReturn _ (incident_facetEdge_leftEnd m wd)
  have hRv := three_le_nonDanglingValency_end m wd hNoReturn _ (incident_facetEdge_rightEnd m wd)
  omega

/-- **The wall datum is trivalent away from the anchor.** -/
theorem wallDatum_trivalent_away_anchor
    (hOrd : NonTrivalentValencyTwoRowEquiv.OrdinaryTrivalent
      (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk)
    (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hw : w ≠ anchorVertex m wd anchorBlk) :
    nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne) w ≤ 3 := by
  classical
  by_cases hTarget : w.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)
  · have hSelf : (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEndpoint
        (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) w.1.2 = w :=
      (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hTarget.symm, rfl⟩
    have hRel : ¬ ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
        (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)).Rel anchorBlk.1 w.1.2 := by
      intro hBad
      exact hw ((NonTrivalentValencyTwoRowEquiv.sourceEndpoint_eq_of_rel hBad).trans hSelf).symm
    rw [← hSelf]
    exact hOrd w.1.2 hRel
  · exact NonTrivalentValencyTwoExit.wallDatum_trivalent_away wd.cover wd.fullDim wd.hc wd.hab
      wd.hOne (wd.hForest m) w hTarget

/-- **The branch-vertex dictionary across the wall contraction.** -/
def branchEquivAnchorComplement
    (hNoReturn : NoContractedReturn wd.cover wd.contracted)
    (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hOrd : NonTrivalentValencyTwoRowEquiv.OrdinaryTrivalent
      (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk) :
    {v : BranchVertex wd.cover // v.1 ≠ leftEnd m wd ∧ v.1 ≠ rightEnd m wd} ≃
      {w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
        w.1 ≠ anchorVertex m wd anchorBlk} := by
  classical
  have hNeAnchor : ∀ v : wd.cover.SourceVertex, 3 ≤ nonDanglingValency wd.cover v →
      v ≠ leftEnd m wd → v ≠ rightEnd m wd →
      sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v ≠ anchorVertex m wd anchorBlk := by
    intro v hv hvl hvr hBad
    have hMem : v ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
        (anchorVertex m wd anchorBlk) :=
      (mem_activeFibreVertices wd.cover wd.hc wd.hab wd.hOne _ v).mpr ⟨hBad, by omega⟩
    rcases eq_leftEnd_or_eq_rightEnd_of_mem_activeFibre m wd hNoReturn src hOrd v hMem hv with h | h
    · exact hvl h
    · exact hvr h
  refine Equiv.ofBijective
    (fun v ↦ ⟨⟨sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v.1.1,
      WallSplitIncidence.three_le_nonDanglingValency_sourceVertexMap wd.cover wd.hc wd.hab wd.hOne
        (wd.hCompat m) (wd.hForest m) wd.fullDim.connected v.1.1 v.1.2⟩,
      hNeAnchor v.1.1 v.1.2 v.2.1 v.2.2⟩) ⟨?_, ?_⟩
  · intro v v' hEq
    have hMap : sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v.1.1 =
        sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v'.1.1 :=
      congrArg (fun w : {w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
        w.1 ≠ anchorVertex m wd anchorBlk} ↦ w.1.1) hEq
    have hLe := wallDatum_trivalent_away_anchor m wd hOrd
      (sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v.1.1)
      (hNeAnchor v.1.1 v.1.2 v.2.1 v.2.2)
    have hMemV : v.1.1 ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
        (sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v.1.1) :=
      (mem_activeFibreVertices wd.cover wd.hc wd.hab wd.hOne _ v.1.1).mpr
        ⟨rfl, by have := v.1.2; omega⟩
    have hMemV' : v'.1.1 ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
        (sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v.1.1) :=
      (mem_activeFibreVertices wd.cover wd.hc wd.hab wd.hOne _ v'.1.1).mpr
        ⟨hMap.symm, by have := v'.1.2; omega⟩
    exact Subtype.ext (Subtype.ext (WallSplitIncidence.eq_of_mem_activeFibre_of_three_le wd.cover
      wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m) wd.fullDim.connected _ hLe v.1.1 v'.1.1
      hMemV hMemV' v.1.2 v'.1.2))
  · intro w
    obtain ⟨u, hu, hThree⟩ := WallSplitIncidence.exists_three_le_mem_activeFibre wd.cover wd.hc
      wd.hab wd.hOne (wd.hCompat m) (wd.hForest m) w.1.1 w.1.2
    obtain ⟨hMapU, -⟩ := (mem_activeFibreVertices wd.cover wd.hc wd.hab wd.hOne w.1.1 u).mp hu
    have hul : u ≠ leftEnd m wd := by
      intro hBad
      refine w.2 ?_
      rw [← hMapU, hBad, sourceVertexMap_leftEnd_eq_anchorVertex m wd hNoReturn hOrd]
    have hur : u ≠ rightEnd m wd := by
      intro hBad
      refine w.2 ?_
      rw [← hMapU, hBad, ← sourceVertexMap_leftEnd_eq_rightEnd m wd,
        sourceVertexMap_leftEnd_eq_anchorVertex m wd hNoReturn hOrd]
    exact ⟨⟨⟨u, hThree⟩, hul, hur⟩, Subtype.ext (Subtype.ext hMapU)⟩

@[simp] theorem branchEquivAnchorComplement_apply
    (hNoReturn : NoContractedReturn wd.cover wd.contracted)
    (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hOrd : NonTrivalentValencyTwoRowEquiv.OrdinaryTrivalent
      (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk)
    (v : {v : BranchVertex wd.cover // v.1 ≠ leftEnd m wd ∧ v.1 ≠ rightEnd m wd}) :
    (branchEquivAnchorComplement m wd hNoReturn src hOrd v).1.1 =
      sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v.1.1 := rfl

/-! ## 3.  The branch vertices of the outgoing candidate -/

/-- The wall datum's own validity, at the wall data of the outer walk. -/
theorem wallValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid :=
  NonTrivalentValencyTwoRows.wall_valid wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m)

/-- A wall-datum vertex over the merged target vertex is the source endpoint of
its own sheet. -/
theorem sourceEndpoint_self (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hw : w.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)) :
    (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEndpoint
      (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) w.1.2 = w :=
  (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hw.symm, rfl⟩

/-- A wall vertex other than the anchor is an ordinary block. -/
theorem not_rel_anchor_of_ne
    {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
    (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hw : w.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b))
    (hne : w ≠ anchorVertex m wd anchorBlk) :
    ¬ ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
      (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)).Rel anchorBlk.1 w.1.2 := by
  intro hBad
  exact hne (((NonTrivalentValencyTwoRowEquiv.sourceEndpoint_eq_of_rel hBad).trans
    (sourceEndpoint_self m wd w hw)).symm)

section Candidate

variable (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hOrd : NonTrivalentValencyTwoRowEquiv.OrdinaryTrivalent
    (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk)

/-- The side of the new target edge on which an ordinary wall block keeps its
whole surviving star. -/
def branchSide (x : Fin degree) : Bool :=
  !NonTrivalentValencyTwoRowEquiv.ordSide (contractDatum wd.cover wd.hc wd.hab wd.hOne)
    wallStar anchorBlk x

open scoped Classical in
/-- **The outgoing vertex over a wall-datum vertex other than the anchor.**
Over the merged target vertex the candidate splits the block in two; the vertex
that keeps the whole surviving star is the one on the side `branchSide`.  Away
from the merged target vertex the vertex is simply retained. -/
def candVertex (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex) :
    (Prescribed.validCandidate sel).datum.SourceVertex :=
  if w.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) then
    NonTrivalentValencyTwoRows.endpointVertex sel (branchSide m wd (anchorBlk := anchorBlk)
      (wallStar := wallStar) w.1.2) w.1.2
  else ResolutionAwayFromWall.retainedVertex (Prescribed.validCandidate sel) w

theorem candVertex_wall (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hw : w.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)) :
    candVertex m wd sel w =
      NonTrivalentValencyTwoRows.endpointVertex sel (branchSide m wd (anchorBlk := anchorBlk)
        (wallStar := wallStar) w.1.2) w.1.2 := by
  unfold candVertex
  rw [ite_eq_left hw]

theorem candVertex_away (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hw : w.1.1 ≠ (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)) :
    candVertex m wd sel w =
      ResolutionAwayFromWall.retainedVertex (Prescribed.validCandidate sel) w := by
  unfold candVertex
  rw [ite_eq_right hw]

theorem endpointVertex_target (side : Bool) (y : Fin degree) :
    (NonTrivalentValencyTwoRows.endpointVertex sel side y).1.1 =
      (if side then TargetExpansion.freshVertex (contract wd.coverTarget wd.hab wd.hOne)
        else TargetExpansion.oldVertex (contract wd.coverTarget wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩) :=
  ((GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mp rfl).1.symm

/-- Two vertices of the candidate on one side of the new target edge coincide
exactly when their sheets are related there. -/
theorem endpointVertex_rel {side : Bool} {y y' : Fin degree}
    (hEq : NonTrivalentValencyTwoRows.endpointVertex sel side y =
      NonTrivalentValencyTwoRows.endpointVertex sel side y') :
    ((Prescribed.validCandidate sel).datum.vertexPartition
      (if side then TargetExpansion.freshVertex (contract wd.coverTarget wd.hab wd.hOne)
        else TargetExpansion.oldVertex (contract wd.coverTarget wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩)).Rel y y' :=
  congrArg (fun z : (Prescribed.validCandidate sel).datum.SourceVertex ↦ z.1.2) hEq

/-- Two endpoint vertices on different sides of the new target edge differ. -/
theorem endpointVertex_side_eq {side side' : Bool} {y y' : Fin degree}
    (hEq : NonTrivalentValencyTwoRows.endpointVertex sel side y =
      NonTrivalentValencyTwoRows.endpointVertex sel side' y') : side = side' := by
  have hTarget := congrArg (fun z :
    (Prescribed.validCandidate sel).datum.SourceVertex ↦ z.1.1) hEq
  rw [endpointVertex_target m wd sel side y, endpointVertex_target m wd sel side' y'] at hTarget
  cases side <;> cases side' <;>
    first
      | rfl
      | exact absurd hTarget Sum.inl_ne_inr
      | exact absurd hTarget Sum.inr_ne_inl

theorem candVertex_wall_target (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hw : w.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)) :
    (candVertex m wd sel w).1.1 =
      (if branchSide m wd (anchorBlk := anchorBlk) (wallStar := wallStar) w.1.2 then
        TargetExpansion.freshVertex (contract wd.coverTarget wd.hab wd.hOne)
      else TargetExpansion.oldVertex (contract wd.coverTarget wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩) := by
  rw [candVertex_wall m wd sel w hw]
  exact endpointVertex_target m wd sel _ _

theorem candVertex_away_target (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hw : w.1.1 ≠ (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)) :
    (candVertex m wd sel w).1.1 =
      TargetExpansion.oldVertex (contract wd.coverTarget wd.hab wd.hOne) w.1.1 := by
  rw [candVertex_away m wd sel w hw]
  exact ((GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mp rfl).1.symm

theorem anchorVertex_target
    (anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    (anchorVertex m wd anchorBlk).1.1 =
      (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) :=
  ((GluingDatum.sourceEndpoint_eq_iff (contractDatum wd.cover wd.hc wd.hab wd.hOne) _ _ _).mp
    rfl).1.symm

include hOrd in
/-- **The surviving valency is unchanged.**  Over the merged target vertex this
is the `branchSide` census; away from it, the retained vertex. -/
theorem nonDanglingValency_candVertex
    (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hne : w ≠ anchorVertex m wd anchorBlk) :
    nonDanglingValency (Prescribed.validCandidate sel).datum (candVertex m wd sel w) =
      nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne) w := by
  classical
  by_cases hw : w.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)
  · have hRel := not_rel_anchor_of_ne m wd w hw hne
    rw [candVertex_wall m wd sel w hw, branchSide,
      nonDanglingValency_endpointVertex_branchSide sel (wallValid m wd) hRel
        (hOrd w.1.2 hRel), sourceEndpoint_self m wd w hw]
  · rw [candVertex_away m wd sel w hw,
      ResolutionAwayFromWall.nonDanglingValency_retainedVertex
        (Prescribed.validCandidate sel) (wallValid m wd)
        (NonTrivalentValencyTwoRows.candidate_sourceGenus sel) w hw]

include src hOrd in
/-- **The branch vertices of the Base II candidate.**  Every branch vertex of
the candidate is either the outgoing copy of a branch vertex of the wall datum
other than the anchor, or one of the two anchor ends `A_u`, `A_v`. -/
def candBranchMap :
    ({w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
        w.1 ≠ anchorVertex m wd anchorBlk} ⊕ Bool) →
      BranchVertex (Prescribed.validCandidate sel).datum
  | Sum.inl w => ⟨candVertex m wd sel w.1.1, by
      rw [nonDanglingValency_candVertex m wd sel hOrd w.1.1 w.2]
      exact w.1.2⟩
  | Sum.inr side => ⟨NonTrivalentValencyTwoRows.endpointVertex sel side
      (Prescribed.selectedRepresentative sel),
      (NonTrivalentValencyTwoRows.nonDanglingValency_endpointVertex src sel
        (wallValid m wd) side).ge⟩

/-- The outgoing vertex over the source endpoint of an ordinary sheet. -/
theorem candVertex_sourceEndpoint {x : Fin degree}
    (hX : ¬ ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
      (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)).Rel anchorBlk.1 x) :
    candVertex m wd sel ((contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEndpoint
        (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) x) =
      NonTrivalentValencyTwoRows.endpointVertex sel
        (branchSide m wd (anchorBlk := anchorBlk) (wallStar := wallStar) x) x := by
  classical
  have hRepr : ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
      (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)).Rel
        (((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
          (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)).repr x) x :=
    ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
      (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)).rel_repr_left x
  rw [candVertex_wall m wd sel _ rfl]
  simp only [branchSide]
  rw [show ((contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEndpoint
        (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) x).1.2 =
      ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
        (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)).repr x from rfl,
    ordSide_congr hRepr,
    endpointVertex_eq_ordinary sel _ (NonTrivalentValencyTwoDescent.not_rel_repr hX) hRepr]

include src hOrd in
theorem candBranchMap_injective :
    Function.Injective (candBranchMap m wd src sel hOrd) := by
  classical
  have hWallTarget : ∀ w : {w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
      w.1 ≠ anchorVertex m wd anchorBlk},
      w.1.1.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) →
      ¬ ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
        (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)).Rel anchorBlk.1
          w.1.1.1.2 :=
    fun w hw ↦ not_rel_anchor_of_ne m wd w.1.1 hw w.2
  rintro (w | side) (w' | side') hEq <;>
    have hv : (candBranchMap m wd src sel hOrd _).1 =
        (candBranchMap m wd src sel hOrd _).1 := congrArg Subtype.val hEq
  · by_cases hw : w.1.1.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) <;>
      by_cases hw' : w'.1.1.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)
    · have hv2 : NonTrivalentValencyTwoRows.endpointVertex sel
            (branchSide m wd (anchorBlk := anchorBlk) (wallStar := wallStar) w.1.1.1.2)
              w.1.1.1.2 =
          NonTrivalentValencyTwoRows.endpointVertex sel
            (branchSide m wd (anchorBlk := anchorBlk) (wallStar := wallStar) w'.1.1.1.2)
              w'.1.1.1.2 := by
        rw [← candVertex_wall m wd sel w.1.1 hw, ← candVertex_wall m wd sel w'.1.1 hw']
        exact hv
      rw [endpointVertex_side_eq m wd sel hv2] at hv2
      have hRel := (NonTrivalentValencyTwoDescent.candidate_vertexPartition_rel_ordinary sel _
        (hWallTarget w hw)).mp (endpointVertex_rel m wd sel hv2)
      have hSheet : w.1.1.1.2 = w'.1.1.1.2 := by
        have h1 : ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
            w.1.1.1.1).repr w.1.1.1.2 = w.1.1.1.2 := w.1.1.2
        have h2 : ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
            w'.1.1.1.1).repr w'.1.1.1.2 = w'.1.1.1.2 := w'.1.1.2
        rw [hw] at h1
        rw [hw'] at h2
        rw [← h1, ← h2]
        exact hRel
      exact congrArg Sum.inl (Subtype.ext (Subtype.ext (Subtype.ext
        (Prod.ext (hw.trans hw'.symm) hSheet))))
    · exfalso
      have hTarget := (candVertex_wall_target m wd sel w.1.1 hw).symm.trans
        ((congrArg (fun z : (Prescribed.validCandidate sel).datum.SourceVertex ↦ z.1.1) hv).trans
          (candVertex_away_target m wd sel w'.1.1 hw'))
      cases hSide : branchSide m wd (anchorBlk := anchorBlk) (wallStar := wallStar) w.1.1.1.2 with
      | false => rw [hSide] at hTarget; exact hw' (Sum.inl_injective hTarget).symm
      | true => rw [hSide] at hTarget; exact Sum.inr_ne_inl hTarget
    · exfalso
      have hTarget := (candVertex_away_target m wd sel w.1.1 hw).symm.trans
        ((congrArg (fun z : (Prescribed.validCandidate sel).datum.SourceVertex ↦ z.1.1) hv).trans
          (candVertex_wall_target m wd sel w'.1.1 hw'))
      cases hSide : branchSide m wd (anchorBlk := anchorBlk) (wallStar := wallStar) w'.1.1.1.2 with
      | false => rw [hSide] at hTarget; exact hw (Sum.inl_injective hTarget)
      | true => rw [hSide] at hTarget; exact Sum.inl_ne_inr hTarget
    · have hRet : ResolutionAwayFromWall.retainedVertex
          (Prescribed.validCandidate sel) w.1.1 =
          ResolutionAwayFromWall.retainedVertex (Prescribed.validCandidate sel) w'.1.1 := by
        rw [← candVertex_away m wd sel w.1.1 hw, ← candVertex_away m wd sel w'.1.1 hw']
        exact hv
      exact congrArg Sum.inl (Subtype.ext (Subtype.ext
        (ResolutionStableIncidence.retainedVertex_injective_away
          (Prescribed.validCandidate sel) w.1.1 w'.1.1 hw hw' hRet)))
  · exfalso
    have hv' : candVertex m wd sel w.1.1 =
        NonTrivalentValencyTwoRows.endpointVertex sel side'
          (Prescribed.selectedRepresentative sel) := hv
    by_cases hw : w.1.1.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)
    · have hv2 : NonTrivalentValencyTwoRows.endpointVertex sel
            (branchSide m wd (anchorBlk := anchorBlk) (wallStar := wallStar) w.1.1.1.2)
              w.1.1.1.2 =
          NonTrivalentValencyTwoRows.endpointVertex sel side'
            (Prescribed.selectedRepresentative sel) := by
        rw [← candVertex_wall m wd sel w.1.1 hw]
        exact hv'
      rw [endpointVertex_side_eq m wd sel hv2] at hv2
      have hRel := (NonTrivalentValencyTwoDescent.candidate_vertexPartition_rel_ordinary sel _
        (hWallTarget w hw)).mp (endpointVertex_rel m wd sel hv2)
      exact hWallTarget w hw ((NonTrivalentValencyTwoRows.rep_wall_rel sel).trans hRel.symm)
    · have hTarget := congrArg
        (fun z : (Prescribed.validCandidate sel).datum.SourceVertex ↦ z.1.1) hv'
      rw [candVertex_away_target m wd sel w.1.1 hw,
        endpointVertex_target m wd sel side' (Prescribed.selectedRepresentative sel)] at hTarget
      cases side' with
      | false => exact hw (Sum.inl_injective hTarget)
      | true => exact Sum.inl_ne_inr hTarget
  · exfalso
    have hv' : NonTrivalentValencyTwoRows.endpointVertex sel side
          (Prescribed.selectedRepresentative sel) =
        candVertex m wd sel w'.1.1 := hv
    by_cases hw : w'.1.1.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)
    · have hv2 : NonTrivalentValencyTwoRows.endpointVertex sel
            (branchSide m wd (anchorBlk := anchorBlk) (wallStar := wallStar) w'.1.1.1.2)
              w'.1.1.1.2 =
          NonTrivalentValencyTwoRows.endpointVertex sel side
            (Prescribed.selectedRepresentative sel) := by
        rw [← candVertex_wall m wd sel w'.1.1 hw]
        exact hv'.symm
      rw [endpointVertex_side_eq m wd sel hv2] at hv2
      have hRel := (NonTrivalentValencyTwoDescent.candidate_vertexPartition_rel_ordinary sel _
        (hWallTarget w' hw)).mp (endpointVertex_rel m wd sel hv2)
      exact hWallTarget w' hw ((NonTrivalentValencyTwoRows.rep_wall_rel sel).trans hRel.symm)
    · have hTarget := congrArg
        (fun z : (Prescribed.validCandidate sel).datum.SourceVertex ↦ z.1.1) hv'
      rw [candVertex_away_target m wd sel w'.1.1 hw,
        endpointVertex_target m wd sel side (Prescribed.selectedRepresentative sel)] at hTarget
      cases side with
      | false => exact hw (Sum.inl_injective hTarget.symm)
      | true => exact Sum.inr_ne_inl hTarget
  · exact congrArg Sum.inr (endpointVertex_side_eq m wd sel
      (show NonTrivalentValencyTwoRows.endpointVertex sel side
          (Prescribed.selectedRepresentative sel) =
        NonTrivalentValencyTwoRows.endpointVertex sel side'
          (Prescribed.selectedRepresentative sel) from hv))

include src hOrd in
theorem candBranchMap_surjective :
    Function.Surjective (candBranchMap m wd src sel hOrd) := by
  classical
  intro v
  have hAnchorNe : ∀ x : Fin degree,
      ¬ ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
        (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)).Rel anchorBlk.1 x →
      (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEndpoint
          (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) x ≠
        anchorVertex m wd anchorBlk := by
    intro x hX hBad
    refine hX ?_
    have h := ((GluingDatum.sourceEndpoint_eq_iff
      (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) x
      (anchorVertex m wd anchorBlk)).mp hBad).2
    set part := (contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
      (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) with hpart
    have hx : part.repr (anchorVertex m wd anchorBlk).1.2 = part.repr anchorBlk.1 :=
      part.repr_idem anchorBlk.1
    show part.repr anchorBlk.1 = part.repr x
    rw [← hx]
    exact h.symm
  have hOrdinary : ∀ side : Bool,
      NonTrivalentValencyTwoRows.endpointVertex sel side v.1.1.2 = v.1 →
      ¬ ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
        (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)).Rel anchorBlk.1 v.1.1.2 →
      ∃ w, candBranchMap m wd src sel hOrd w = v := by
    intro side hV hRel
    have hSide : branchSide m wd (anchorBlk := anchorBlk) (wallStar := wallStar) v.1.1.2 =
        side := by
      have hOther := nonDanglingValency_endpointVertex_ordSide_le sel (wallValid m wd) hRel
        (hOrd v.1.1.2 hRel)
      rw [branchSide]
      cases hCase : NonTrivalentValencyTwoRowEquiv.ordSide
          (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk v.1.1.2 with
      | false =>
        rw [hCase] at hOther
        cases side with
        | false => exact absurd (by rw [hV] at hOther; have := v.2; omega : False) (by simp)
        | true => rfl
      | true =>
        rw [hCase] at hOther
        cases side with
        | false => rfl
        | true => exact absurd (by rw [hV] at hOther; have := v.2; omega : False) (by simp)
    have hNd := nonDanglingValency_endpointVertex_branchSide sel (wallValid m wd) hRel
      (hOrd v.1.1.2 hRel)
    rw [show (!NonTrivalentValencyTwoRowEquiv.ordSide
      (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk v.1.1.2) = side from hSide,
      hV] at hNd
    refine ⟨Sum.inl ⟨⟨(contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEndpoint
      (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) v.1.1.2,
      by rw [← hNd]; exact v.2⟩, hAnchorNe v.1.1.2 hRel⟩, Subtype.ext ?_⟩
    show candVertex m wd sel ((contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEndpoint
      (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) v.1.1.2) = v.1
    rw [candVertex_sourceEndpoint m wd sel hRel, hSide]
    exact hV
  by_cases hFresh : v.1.1.1 =
      TargetExpansion.freshVertex (contract wd.coverTarget wd.hab wd.hOne)
  · have hV : NonTrivalentValencyTwoRows.endpointVertex sel true v.1.1.2 = v.1 :=
      NonTrivalentValencyTwoExit.eq_endpointVertex wd.cover wd.hc wd.hab wd.hOne sel true v.1
        (by rw [hFresh]; rfl)
    by_cases hRel : ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
        (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)).Rel anchorBlk.1 v.1.1.2
    · refine ⟨Sum.inr true, Subtype.ext ?_⟩
      show NonTrivalentValencyTwoRows.endpointVertex sel true
        (Prescribed.selectedRepresentative sel) = v.1
      rw [NonTrivalentValencyTwoRows.endpointVertex_eq sel true
        (NonTrivalentValencyTwoRows.rep_wall_rel sel)
        ((NonTrivalentValencyTwoRows.rep_wall_rel sel).symm.trans hRel)]
      exact hV
    · exact hOrdinary true hV hRel
  · obtain ⟨place, hplace⟩ : ∃ place,
        v.1.1.1 = TargetExpansion.oldVertex (contract wd.coverTarget wd.hab wd.hOne) place := by
      cases h : v.1.1.1 with
      | inl p => exact ⟨p, rfl⟩
      | inr u => exact absurd h hFresh
    by_cases hwall : place = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)
    · have hV : NonTrivalentValencyTwoRows.endpointVertex sel false v.1.1.2 = v.1 :=
        NonTrivalentValencyTwoExit.eq_endpointVertex wd.cover wd.hc wd.hab wd.hOne sel false v.1
          (by rw [hplace, hwall]; rfl)
      by_cases hAnchor : ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
          (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)).Rel anchorBlk.1 v.1.1.2
      · obtain ⟨edge, hEdge, hFine⟩ :=
          NonTrivalentValencyTwoRows.exists_retained_rel src sel hAnchor
        have hEq := NonTrivalentValencyTwoRows.endpointVertex_eq sel false
          (occurrenceSheet_wall_rel edge) hFine
        by_cases hFirst : edge = Prescribed.firstSelected sel
        · refine ⟨Sum.inr false, Subtype.ext ?_⟩
          show NonTrivalentValencyTwoRows.endpointVertex sel false
            (Prescribed.selectedRepresentative sel) = v.1
          rw [show Prescribed.selectedRepresentative sel = occurrenceSheet edge from by
            rw [hFirst]; rfl, hEq]
          exact hV
        · exfalso
          have h2 := NonTrivalentValencyTwoRows.nonDanglingValency_extraEndpointVertex src sel
            (wallValid m wd) hEdge hFirst
          rw [hEq, hV] at h2
          have := v.2
          omega
      · exact hOrdinary false hV hAnchor
    · obtain ⟨old, hOld, hRet⟩ := ResolutionAwayFromWall.exists_retainedVertex_of_target
        (Prescribed.validCandidate sel) v.1 place hwall hplace
      have hAway : old.1.1 ≠ (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) := by
        rw [hOld]
        exact hwall
      have hNd : nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne) old =
          nonDanglingValency (Prescribed.validCandidate sel).datum v.1 := by
        rw [← hRet, ResolutionAwayFromWall.nonDanglingValency_retainedVertex
          (Prescribed.validCandidate sel) (wallValid m wd)
          (NonTrivalentValencyTwoRows.candidate_sourceGenus sel) old hAway]
      have hne : old ≠ anchorVertex m wd anchorBlk := by
        intro hBad
        exact hAway (by rw [hBad]; exact anchorVertex_target m wd anchorBlk)
      refine ⟨Sum.inl ⟨⟨old, by rw [hNd]; exact v.2⟩, hne⟩, Subtype.ext ?_⟩
      show candVertex m wd sel old = v.1
      rw [candVertex_away m wd sel old hAway]
      exact hRet

include src hOrd in
/-- **The branch vertices of the Base II candidate.** -/
def candBranchEquiv :
    ({w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
        w.1 ≠ anchorVertex m wd anchorBlk} ⊕ Bool) ≃
      BranchVertex (Prescribed.validCandidate sel).datum :=
  Equiv.ofBijective (candBranchMap m wd src sel hOrd)
    ⟨candBranchMap_injective m wd src sel hOrd, candBranchMap_surjective m wd src sel hOrd⟩

end Candidate

/-! ## 4.  The vertex dictionary of the type change -/

section Vertex

variable (hNoReturn : NoContractedReturn wd.cover wd.contracted)

/-- The `A_u` end of the vanishing occurrence, as a branch vertex. -/
def leftBranch : BranchVertex wd.cover :=
  ⟨leftEnd m wd,
    three_le_nonDanglingValency_end m wd hNoReturn _ (incident_facetEdge_leftEnd m wd)⟩

/-- The `A_v` end of the vanishing occurrence, as a branch vertex. -/
def rightBranch : BranchVertex wd.cover :=
  ⟨rightEnd m wd,
    three_le_nonDanglingValency_end m wd hNoReturn _ (incident_facetEdge_rightEnd m wd)⟩

/-- The two ends of the vanishing occurrence complete the branch vertices of
the incoming cover. -/
def coverBranchMap :
    ({v : BranchVertex wd.cover // v.1 ≠ leftEnd m wd ∧ v.1 ≠ rightEnd m wd} ⊕ Bool) →
      BranchVertex wd.cover
  | Sum.inl v => v.1
  | Sum.inr side => if side then rightBranch m wd hNoReturn else leftBranch m wd hNoReturn

/-- The two ends of the vanishing occurrence complete the branch vertices of
the incoming cover. -/
def coverBranchEquiv :
    ({v : BranchVertex wd.cover // v.1 ≠ leftEnd m wd ∧ v.1 ≠ rightEnd m wd} ⊕ Bool) ≃
      BranchVertex wd.cover := by
  classical
  refine Equiv.ofBijective (coverBranchMap m wd hNoReturn) ⟨?_, ?_⟩
  · rintro (v | side) (v' | side') hEq
    · exact congrArg Sum.inl (Subtype.ext hEq)
    · exfalso
      cases side' with
      | false => exact v.2.1 (congrArg Subtype.val hEq)
      | true => exact v.2.2 (congrArg Subtype.val hEq)
    · exfalso
      cases side with
      | false => exact v'.2.1 (congrArg Subtype.val hEq).symm
      | true => exact v'.2.2 (congrArg Subtype.val hEq).symm
    · cases side <;> cases side' <;> first
        | rfl
        | exact absurd (congrArg Subtype.val hEq) (leftEnd_ne_rightEnd m wd)
        | exact absurd (congrArg Subtype.val hEq) (leftEnd_ne_rightEnd m wd).symm
  · intro u
    by_cases hl : u.1 = leftEnd m wd
    · exact ⟨Sum.inr false, Subtype.ext hl.symm⟩
    · by_cases hr : u.1 = rightEnd m wd
      · exact ⟨Sum.inr true, Subtype.ext hr.symm⟩
      · exact ⟨Sum.inl ⟨u, hl, hr⟩, rfl⟩

section VertexEquiv

variable {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hOrd : NonTrivalentValencyTwoRowEquiv.OrdinaryTrivalent
    (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk)

/-- **The vertex dictionary of the valency-two Base II type change.**  Away
from the anchor it is the outgoing (retained, or `branchSide` endpoint) vertex
of the wall datum, read back to the incoming cover by the branch dictionary of
the wall contraction and then through the incoming tracking; the two anchor
ends `A_u` and `A_v` go to the two ends of the vanishing occurrence. -/
def vertexEquiv : BranchVertex (Prescribed.validCandidate sel).datum ≃ V :=
  ((candBranchEquiv m wd src sel hOrd).symm.trans
    (Equiv.sumCongr (branchEquivAnchorComplement m wd hNoReturn src hOrd).symm
      (Equiv.refl Bool))).trans
    ((coverBranchEquiv m wd hNoReturn).trans wd.tracks.iso.vtx)

@[simp] theorem vertexEquiv_inl
    (w : {w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
      w.1 ≠ anchorVertex m wd anchorBlk}) :
    vertexEquiv m wd hNoReturn src sel hOrd
        (candBranchMap m wd src sel hOrd (Sum.inl w)) =
      wd.tracks.iso.vtx ((branchEquivAnchorComplement m wd hNoReturn src hOrd).symm w).1 := by
  have h : (candBranchEquiv m wd src sel hOrd).symm
      (candBranchMap m wd src sel hOrd (Sum.inl w)) = Sum.inl w :=
    (candBranchEquiv m wd src sel hOrd).symm_apply_apply (Sum.inl w)
  show wd.tracks.iso.vtx (coverBranchMap m wd hNoReturn
    (Equiv.sumCongr (branchEquivAnchorComplement m wd hNoReturn src hOrd).symm (Equiv.refl Bool)
      ((candBranchEquiv m wd src sel hOrd).symm
        (candBranchMap m wd src sel hOrd (Sum.inl w))))) = _
  rw [h]
  rfl

@[simp] theorem vertexEquiv_anchor (side : Bool) :
    vertexEquiv m wd hNoReturn src sel hOrd
        (candBranchMap m wd src sel hOrd (Sum.inr side)) =
      wd.tracks.iso.vtx (if side then rightBranch m wd hNoReturn
        else leftBranch m wd hNoReturn) := by
  have h : (candBranchEquiv m wd src sel hOrd).symm
      (candBranchMap m wd src sel hOrd (Sum.inr side)) = Sum.inr side :=
    (candBranchEquiv m wd src sel hOrd).symm_apply_apply (Sum.inr side)
  show wd.tracks.iso.vtx (coverBranchMap m wd hNoReturn
    (Equiv.sumCongr (branchEquivAnchorComplement m wd hNoReturn src hOrd).symm (Equiv.refl Bool)
      ((candBranchEquiv m wd src sel hOrd).symm
        (candBranchMap m wd src sel hOrd (Sum.inr side))))) = _
  rw [h]
  rfl

end VertexEquiv

end Vertex

/-! ## 5.  (H-II): the prescribed merged-pair move -/

section Prescribed

variable (hNoReturn : NoContractedReturn wd.cover wd.contracted)

/-- The dart of the vanishing occurrence at the `A_u` end. -/
def facetDartLeft : StableSourceDarts.Dart wd.cover :=
  ⟨leftBranch m wd hNoReturn, ⟨facetEdge m wd, incident_facetEdge_leftEnd m wd⟩⟩

/-- The dart of the vanishing occurrence at the `A_v` end. -/
def facetDartRight : StableSourceDarts.Dart wd.cover :=
  ⟨rightBranch m wd hNoReturn, ⟨facetEdge m wd, incident_facetEdge_rightEnd m wd⟩⟩

/-- A surviving occurrence of the wall datum, read as a surviving occurrence of
the incoming cover. -/
def liftEdge (g : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    NonDanglingEdge wd.cover :=
  WallDegeneration.nonDanglingEmbedding wd.cover (wd.hCompat m).1 g

theorem stablePath_liftEdge (g : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    (liftEdge m wd g).stablePath =
      incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m)
        g.stablePath := rfl

section Merged

variable {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)

theorem firstSelected_survives :
    ¬ IsDangling (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (Prescribed.firstSelected sel).1 :=
  NonTrivalentValencyTwoRows.survivor_not_isDangling (Prescribed.firstSelected_mem sel)

theorem secondSelected_survives :
    ¬ IsDangling (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (Prescribed.secondSelected sel).1 :=
  NonTrivalentValencyTwoRows.survivor_not_isDangling (Prescribed.secondSelected_mem sel)

/-- The two survivors of the thick direction that `sel` merges (the paper's
`e_first`, `e_second`), as surviving occurrences of the incoming cover. -/
def selectedLift (side : Bool) : NonDanglingEdge wd.cover :=
  liftEdge m wd (if side then
      ⟨(Prescribed.secondSelected sel).1, secondSelected_survives m wd sel⟩
    else ⟨(Prescribed.firstSelected sel).1, firstSelected_survives m wd sel⟩)

/-- **(H-II), the per-vertex match at the anchor of a two-valent wall.**  The
two darts that the Whitehead move `m` places together with `m.base` -- that is,
the moved star of `graph.vert m.base` with `m.base` removed -- carry the two
stable **rows** of the survivors of the thick direction that `sel` merges, in
the orientation that puts `A_u` at `graph.vert m.base`: the first conjunct says
that `m.base` is the dart of the vanishing occurrence at the `A_u` end.

The survivor clause is at the level of rows, `d.2.1.stablePath = ...`, not of
occurrences.  That is what the star count consumes
(`NonTrivalentValencyTwoStarCount.label_dart_merged`, through
`IncomingPairing.label_dart_of_row`), and it is the only form satisfiable at an
incoming shape with a *pass-through* survivor -- one whose row reaches its end
of the vanishing occurrence through an occurrence over the contracted target
edge, which happens at every Configuration B incoming and at the split incomings
of Configuration A.

In Configuration A (`2 + 2`) the thick direction carries exactly two survivors,
so the pair is forced and both directions are doubled; in Configuration B
(`3 + 1`) the thick direction carries three and the merged pair is exactly
`sel`'s choice -- which is why `sel` is a parameter of the exit
`NonTrivalentValencyTwoExit`.  A single clause therefore covers both sub-cases.

The other orientation is normalised away by the caller with
`CubicDartGraph.MoveData.swap`, which leaves `graph.move m` unchanged
(`CubicDartGraph.move_swap`) and exchanges `m.base` with `graph.op m.base`. -/
def PrescribedMergedMove : Prop :=
  wd.tracks.iso.dart (facetDartLeft m wd hNoReturn) = m.base ∧
    ∃ first second : StableSourceDarts.Dart wd.cover,
      first.2.1.stablePath = (selectedLift m wd sel false).stablePath ∧
        second.2.1.stablePath = (selectedLift m wd sel true).stablePath ∧
        (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
          {wd.tracks.iso.dart first, wd.tracks.iso.dart second}

/-- **The occurrence-level clause implies (H-II).**  If the two darts the move
places with `m.base` *are* the occurrences of the two merged survivors -- the
occurrence-level form of the condition -- then they carry their rows, so (H-II)
holds.  The converse fails at every incoming shape with a pass-through survivor
(Configuration B, and the split incomings of Configuration A): there no dart at
the relevant end of the vanishing occurrence is the merged survivor's own
occurrence. -/
theorem prescribedMergedMove_of_occurrence
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd hNoReturn) = m.base)
    (first second : StableSourceDarts.Dart wd.cover)
    (hFirst : first.2.1 = selectedLift m wd sel false)
    (hSecond : second.2.1 = selectedLift m wd sel true)
    (hStar : (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
      {wd.tracks.iso.dart first, wd.tracks.iso.dart second}) :
    PrescribedMergedMove m wd hNoReturn sel :=
  ⟨hBase, first, second, by rw [hFirst], by rw [hSecond], hStar⟩

/-- **(H-II) from the orientation clause and two moved darts carrying the two
merged rows.**  This is the shape the valency dispatcher consumes: it obtains
the two darts from `IncomingPairing.exists_movedStar_darts` (which also says
that one sits at each end of the vanishing occurrence, so no separation
hypothesis is needed here), checks that their rows are the merged pair, and
applies this lemma.  For the other order of the pair, apply it to `y`, `x` after
`Finset.pair_comm`. -/
theorem prescribedMergedMove_of_rows
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd hNoReturn) = m.base)
    (x y : StableSourceDarts.Dart wd.cover)
    (hx : x.2.1.stablePath = (selectedLift m wd sel false).stablePath)
    (hy : y.2.1.stablePath = (selectedLift m wd sel true).stablePath)
    (hStar : (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
      {wd.tracks.iso.dart x, wd.tracks.iso.dart y}) :
    PrescribedMergedMove m wd hNoReturn sel :=
  ⟨hBase, x, y, hx, hy, hStar⟩

/-- **The geometric content of a type change at a valency-two wall**: the two
merged survivors lift to occurrences at the *two different* ends of the
vanishing occurrence.  Without it `A_u` sees exactly the star of `leftEnd` and
no Whitehead move takes place. -/
def MergedSeparated : Prop :=
  Incident wd.cover (selectedLift m wd sel false).1 (leftEnd m wd) ∧
    Incident wd.cover (selectedLift m wd sel true).1 (rightEnd m wd)

theorem facetEdge_ne_selectedLift (side : Bool) :
    (facetEdge m wd).1 ≠ (selectedLift m wd sel side).1 := by
  intro hBad
  refine incomingRow_ne_facet wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m)
    (wd.hForest m) wd.coordinates (label m.base) wd.hZeroCoord wd.hPosCoord wd.hFacetZero
    (NonDanglingEdge.stablePath (if side then
      (⟨(Prescribed.secondSelected sel).1, secondSelected_survives m wd sel⟩ :
        NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
      else ⟨(Prescribed.firstSelected sel).1, firstSelected_survives m wd sel⟩)) ?_
  rw [← stablePath_liftEdge m wd]
  show NonDanglingEdge.stablePath (selectedLift m wd sel side) = facetRow m wd
  rw [show selectedLift m wd sel side = facetEdge m wd from Subtype.ext hBad.symm]
  exact facetEdge_stablePath m wd

end Merged

/-! ### The orientation prescribed by (H-II) -/

theorem facetDartLeft_ne_facetDartRight :
    facetDartRight m wd hNoReturn ≠ facetDartLeft m wd hNoReturn := by
  intro hBad
  exact (leftEnd_ne_rightEnd m wd)
    (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.1.1) hBad).symm

/-- The two darts of the vanishing occurrence are opposite. -/
theorem opposite_facetDartLeft :
    StableSourceDarts.opposite wd.cover wd.fullDim.connected wd.fullDim.pathEnds
        (facetDartLeft m wd hNoReturn) = facetDartRight m wd hNoReturn :=
  (StableSourceDarts.opposite_eq_of_row_eq wd.cover wd.fullDim.connected wd.fullDim.pathEnds
    (d := facetDartLeft m wd hNoReturn) (e := facetDartRight m wd hNoReturn) rfl
    (facetDartLeft_ne_facetDartRight m wd hNoReturn)).symm

/-- **Under (H-II) the `A_u` end of the vanishing occurrence sits at
`graph.vert m.base`.** -/
theorem vert_base_eq
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd hNoReturn) = m.base) :
    graph.vert m.base = wd.tracks.iso.vtx (leftBranch m wd hNoReturn) := by
  have h := wd.tracks.iso.vert_map (facetDartLeft m wd hNoReturn)
  rw [hBase] at h
  exact h

theorem op_base_eq
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd hNoReturn) = m.base) :
    graph.op m.base = wd.tracks.iso.dart (facetDartRight m wd hNoReturn) := by
  have h2 := wd.tracks.iso.op_map (facetDartLeft m wd hNoReturn)
  have h3 : (StableSourceDarts.ofDatum wd.cover wd.fullDim.connected wd.fullDim.trivalent
      wd.fullDim.pathEnds).op (facetDartLeft m wd hNoReturn) =
      facetDartRight m wd hNoReturn := opposite_facetDartLeft m wd hNoReturn
  rw [hBase, h3] at h2
  exact h2

/-- **Under (H-II) the `A_v` end sits at `graph.vert (graph.op m.base)`.** -/
theorem vert_opBase_eq
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd hNoReturn) = m.base) :
    graph.op m.base = wd.tracks.iso.dart (facetDartRight m wd hNoReturn) ∧
      graph.vert (graph.op m.base) = wd.tracks.iso.vtx (rightBranch m wd hNoReturn) := by
  refine ⟨op_base_eq m wd hNoReturn hBase, ?_⟩
  rw [op_base_eq m wd hNoReturn hBase]
  exact wd.tracks.iso.vert_map (facetDartRight m wd hNoReturn)

section Orientation

variable {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hOrd : NonTrivalentValencyTwoRowEquiv.OrdinaryTrivalent
    (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk)

/-- **`A_u` goes to `graph.vert m.base`.** -/
theorem vertexEquiv_anchor_false
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd hNoReturn) = m.base) :
    vertexEquiv m wd hNoReturn src sel hOrd
        (candBranchMap m wd src sel hOrd (Sum.inr false)) = graph.vert m.base := by
  rw [vertexEquiv_anchor m wd hNoReturn src sel hOrd false, vert_base_eq m wd hNoReturn hBase]
  rfl

/-- **`A_v` goes to `graph.vert (graph.op m.base)`.** -/
theorem vertexEquiv_anchor_true
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd hNoReturn) = m.base) :
    vertexEquiv m wd hNoReturn src sel hOrd
        (candBranchMap m wd src sel hOrd (Sum.inr true)) =
      graph.vert (graph.op m.base) := by
  rw [vertexEquiv_anchor m wd hNoReturn src sel hOrd true,
    (vert_opBase_eq m wd hNoReturn hBase).2]
  rfl

end Orientation

/-! ### Non-vacuity of (H-II) -/

section NonVacuity

variable {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)

include hNoReturn in
/-- A third surviving occurrence at the `A_u` end, distinct from the vanishing
occurrence and from the merged survivor there. -/
theorem exists_thirdEdge (hSep : MergedSeparated m wd sel) :
    ∃ e : NonDanglingEdge wd.cover, Incident wd.cover e.1 (leftEnd m wd) ∧
      e ≠ facetEdge m wd ∧ e ≠ selectedLift m wd sel false := by
  classical
  have hNd : nonDanglingValency wd.cover (leftEnd m wd) = 3 := by
    have h1 := three_le_nonDanglingValency_end m wd hNoReturn _ (incident_facetEdge_leftEnd m wd)
    have h2 : nonDanglingValency wd.cover (leftEnd m wd) ≤ 3 :=
      wd.fullDim.trivalent (leftEnd m wd)
    omega
  have hNe := facetEdge_ne_selectedLift m wd sel false
  set pair : Finset wd.cover.SourceEdge :=
    {(facetEdge m wd).1, (selectedLift m wd sel false).1} with hpair
  have hsub : pair ⊆ nonDanglingIncident wd.cover (leftEnd m wd) := by
    intro e he
    rw [hpair] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨(facetEdge m wd).2, incident_facetEdge_leftEnd m wd⟩
    · exact (mem_nonDanglingIncident _ _ _).mpr ⟨(selectedLift m wd sel false).2, hSep.1⟩
  have hcard : (nonDanglingIncident wd.cover (leftEnd m wd) \ pair).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, card_nonDanglingIncident, hNd, hpair,
      Finset.card_pair hNe]
  obtain ⟨e, he⟩ := Finset.card_pos.mp
    (by omega : 0 < (nonDanglingIncident wd.cover (leftEnd m wd) \ pair).card)
  rw [Finset.mem_sdiff, hpair] at he
  obtain ⟨hMem, hNotMem⟩ := he
  obtain ⟨hSurv, hInc⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hNotMem
  exact ⟨⟨e, hSurv⟩, hInc, fun h ↦ hNotMem (Or.inl (congrArg Subtype.val h)),
    fun h ↦ hNotMem (Or.inr (congrArg Subtype.val h))⟩

/-- The third dart at the `A_u` end. -/
def thirdEdge (hSep : MergedSeparated m wd sel) : NonDanglingEdge wd.cover :=
  Classical.choose (exists_thirdEdge m wd hNoReturn sel hSep)

theorem thirdEdge_spec (hSep : MergedSeparated m wd sel) :
    Incident wd.cover (thirdEdge m wd hNoReturn sel hSep).1 (leftEnd m wd) ∧
      thirdEdge m wd hNoReturn sel hSep ≠ facetEdge m wd ∧
      thirdEdge m wd hNoReturn sel hSep ≠ selectedLift m wd sel false :=
  Classical.choose_spec (exists_thirdEdge m wd hNoReturn sel hSep)

/-- The dart of the merged survivor at the `A_u` end. -/
def selectedDartLeft (hSep : MergedSeparated m wd sel) : StableSourceDarts.Dart wd.cover :=
  ⟨leftBranch m wd hNoReturn, ⟨selectedLift m wd sel false, hSep.1⟩⟩

/-- The dart of the merged survivor at the `A_v` end. -/
def selectedDartRight (hSep : MergedSeparated m wd sel) : StableSourceDarts.Dart wd.cover :=
  ⟨rightBranch m wd hNoReturn, ⟨selectedLift m wd sel true, hSep.2⟩⟩

/-- The remaining dart at the `A_u` end. -/
def thirdDart (hSep : MergedSeparated m wd sel) : StableSourceDarts.Dart wd.cover :=
  ⟨leftBranch m wd hNoReturn, ⟨thirdEdge m wd hNoReturn sel hSep,
    (thirdEdge_spec m wd hNoReturn sel hSep).1⟩⟩

/-- **The Whitehead move prescribed by the merged pair.**  It contracts the edge
of `m.base` and exchanges the merged survivor at the `A_v` end with the
remaining dart at the `A_u` end. -/
def prescribedMove (hSep : MergedSeparated m wd sel)
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd hNoReturn) = m.base) : graph.MoveData where
  base := m.base
  left := wd.tracks.iso.dart (thirdDart m wd hNoReturn sel hSep)
  right := wd.tracks.iso.dart (selectedDartRight m wd hNoReturn sel hSep)
  nonloop := m.nonloop
  left_vert := (wd.tracks.iso.vert_map (thirdDart m wd hNoReturn sel hSep)).trans
    (vert_base_eq m wd hNoReturn hBase).symm
  left_ne := by
    intro hBad
    exact (thirdEdge_spec m wd hNoReturn sel hSep).2.1
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1)
        (wd.tracks.iso.dart.injective (hBad.trans hBase.symm)))
  right_vert := (wd.tracks.iso.vert_map (selectedDartRight m wd hNoReturn sel hSep)).trans
    (vert_opBase_eq m wd hNoReturn hBase).2.symm
  right_ne := by
    intro hBad
    exact (facetEdge_ne_selectedLift m wd sel true)
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1.1)
        (wd.tracks.iso.dart.injective
          (hBad.trans (op_base_eq m wd hNoReturn hBase)))).symm

/-- **Non-vacuity of (H-II), in relative form.**  At a wall of the outer walk
whose vanishing occurrence is oriented with its `A_u` end at `graph.vert m.base`
and whose two merged survivors sit at the two different ends, the Whitehead move
`prescribedMove` -- which contracts the *same* edge as `m` -- satisfies (H-II).
This is the precise sense in which (H-II) only normalises the choice of `left`
and `right` in the move: it is the separation `MergedSeparated` that is
geometric. -/
theorem prescribedMergedMove_prescribedMove (hSep : MergedSeparated m wd sel)
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd hNoReturn) = m.base) :
    PrescribedMergedMove (prescribedMove m wd hNoReturn sel hSep hBase) wd hNoReturn sel := by
  classical
  set m' := prescribedMove m wd hNoReturn sel hSep hBase with hm'
  set dLeft := selectedDartLeft m wd hNoReturn sel hSep with hdLeft
  set dRight := selectedDartRight m wd hNoReturn sel hSep with hdRight
  have hLeftNeRight : dLeft ≠ dRight := by
    intro hBad
    exact (leftEnd_ne_rightEnd m wd)
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.1.1) hBad)
  have hLeftNeThird : dLeft ≠ thirdDart m wd hNoReturn sel hSep := by
    intro hBad
    exact (thirdEdge_spec m wd hNoReturn sel hSep).2.2
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1) hBad).symm
  have hBaseNeLeft : m.base ≠ wd.tracks.iso.dart dLeft := by
    intro hBad
    exact (facetEdge_ne_selectedLift m wd sel false)
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1.1)
        (wd.tracks.iso.dart.injective (hBase.trans hBad)))
  have hBaseNeRight : m.base ≠ wd.tracks.iso.dart dRight := by
    intro hBad
    exact (facetEdge_ne_selectedLift m wd sel true)
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1.1)
        (wd.tracks.iso.dart.injective (hBase.trans hBad)))
  refine ⟨hBase, dLeft, dRight, rfl, rfl, ?_⟩
  have hStar : (Finset.univ.filter fun d ↦ (graph.move m').vert d = graph.vert m.base) =
      {m.base, wd.tracks.iso.dart dRight, wd.tracks.iso.dart dLeft} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rcases hd with rfl | rfl | rfl
      · exact congrArg graph.vert m'.perm_base
      · exact (congrArg graph.vert m'.perm_right).trans m'.left_vert
      · have h1 : wd.tracks.iso.dart dLeft ≠ m'.left :=
          fun hBad ↦ hLeftNeThird (wd.tracks.iso.dart.injective hBad)
        have h2 : wd.tracks.iso.dart dLeft ≠ m'.right :=
          fun hBad ↦ hLeftNeRight (wd.tracks.iso.dart.injective hBad)
        show graph.vert (m'.perm (wd.tracks.iso.dart dLeft)) = graph.vert m.base
        rw [m'.perm_of_ne h1 h2, wd.tracks.iso.vert_map dLeft,
          vert_base_eq m wd hNoReturn hBase]
        rfl
    · rw [(graph.move m').card_fibre (graph.vert m.base)]
      exact le_of_eq (Finset.card_eq_three.mpr ⟨_, _, _, hBaseNeRight, hBaseNeLeft,
        fun hBad ↦ hLeftNeRight (wd.tracks.iso.dart.injective hBad).symm, rfl⟩).symm
  show (Finset.univ.filter fun d ↦ (graph.move m').vert d = graph.vert m.base).erase m.base =
    {wd.tracks.iso.dart dLeft, wd.tracks.iso.dart dRight}
  rw [hStar, Finset.erase_insert (by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact not_or.mpr ⟨hBaseNeRight, hBaseNeLeft⟩), Finset.pair_comm]

end NonVacuity

end Prescribed

/-! ## 6.  Three pieces of the star count -/

/-- **Away from the two ends of the vanishing occurrence the Whitehead move
does not change the star.**  The permutation `m.perm` is the transposition of
`m.left` and `m.right`, whose vertices are the two ends themselves. -/
theorem move_vert_eq_iff_of_ne {x : V} (hBase : x ≠ graph.vert m.base)
    (hOpBase : x ≠ graph.vert (graph.op m.base)) (d : D) :
    (graph.move m).vert d = x ↔ graph.vert d = x := by
  classical
  by_cases hl : d = m.left
  · subst hl
    constructor
    · intro hBad
      exact absurd ((congrArg graph.vert m.perm_left).symm.trans hBad).symm
        (fun h ↦ hOpBase (h.trans m.right_vert))
    · intro hBad
      exact absurd hBad.symm (fun h ↦ hBase (h.trans m.left_vert))
  · by_cases hr : d = m.right
    · subst hr
      constructor
      · intro hBad
        exact absurd ((congrArg graph.vert m.perm_right).symm.trans hBad).symm
          (fun h ↦ hBase (h.trans m.left_vert))
      · intro hBad
        exact absurd hBad.symm (fun h ↦ hOpBase (h.trans m.right_vert))
    · show graph.vert (m.perm d) = x ↔ _
      rw [m.perm_of_ne hl hr]

/-- **The star of a branch vertex of the incoming cover, counted in the tracked
ambient graph.** -/
theorem card_star_eq_incidenceCount (u : BranchVertex wd.cover) (row : StablePath wd.cover) :
    incidenceCount wd.cover u.1 row =
      Nat.card {d : D // graph.vert d = wd.tracks.iso.vtx u ∧
        label d = wd.fullDim.labelling.row row} := by
  classical
  have hDict := (MovedIncidenceIso.DatumGraphIncidence.ofIso wd.cover wd.fullDim.connected
    wd.fullDim.trivalent wd.fullDim.pathEnds wd.tracks.iso).incidence u row
  refine hDict.trans (Nat.card_congr (Equiv.subtypeEquivRight fun d ↦ ?_))
  have hLabel : label d = wd.fullDim.labelling.row
      (StableSourceDarts.row wd.cover (wd.tracks.iso.dart.symm d)) := by
    have h := wd.tracks.row_map (wd.tracks.iso.dart.symm d)
    rwa [Equiv.apply_symm_apply] at h
  constructor
  · rintro ⟨hv, hr⟩
    refine ⟨hv, ?_⟩
    rw [hLabel]
    exact congrArg wd.fullDim.labelling.row hr
  · rintro ⟨hv, hr⟩
    refine ⟨hv, ?_⟩
    show StableSourceDarts.row wd.cover (wd.tracks.iso.dart.symm d) = row
    refine wd.fullDim.labelling.row.injective ?_
    rw [← hLabel, hr]

section Retained

variable {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hOrd : NonTrivalentValencyTwoRowEquiv.OrdinaryTrivalent
    (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk)

include hOrd in
/-- **The retained-row map is injective**, from the row equivalence of
`NonTrivalentValencyTwoRowEquiv`. -/
theorem injective_retainedRow :
    Function.Injective (NonTrivalentValencyTwoDescent.retainedRow src sel (wallValid m wd)) := by
  intro r r' h
  have h2 := congrArg
    (NonTrivalentValencyTwoRowEquiv.rowEquiv src sel (wallValid m wd) hOrd) h
  rw [NonTrivalentValencyTwoRowEquiv.rowEquiv_retainedRow src sel (wallValid m wd) hOrd r,
    NonTrivalentValencyTwoRowEquiv.rowEquiv_retainedRow src sel (wallValid m wd) hOrd r'] at h2
  exact Option.some_injective _ h2

include hOrd in
/-- **Away from the merged target vertex the candidate does not change the
star.**  This is `ResolutionStableIncidence.incidenceCount_retainedVertex` with
its row *equivalence* hypothesis weakened to injectivity of the retained-row
map `NonTrivalentValencyTwoDescent.retainedRow`, which `injective_retainedRow`
supplies (the one row outside its image is the bridge row).  The proof uses the
equivalence only through `row.injective`. -/
theorem incidenceCount_retainedVertex_retainedRow
    (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hAway : w.1.1 ≠ (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b))
    (row : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (contractDatum wd.cover wd.hc wd.hab wd.hOne) w row =
      incidenceCount (Prescribed.validCandidate sel).datum
        (ResolutionAwayFromWall.retainedVertex (Prescribed.validCandidate sel) w)
        (NonTrivalentValencyTwoDescent.retainedRow src sel (wallValid m wd) row) := by
  classical
  unfold incidenceCount
  apply Finset.card_bij (fun edge _ ↦ ResolutionAwayFromWall.retainedEdge
    (Prescribed.validCandidate sel) (wallValid m wd).1 edge)
  · intro edge hEdge
    simp only [Finset.mem_filter, mem_incidentEdges] at hEdge ⊢
    refine ⟨(ResolutionAwayFromWall.incident_oldSourceEdge_iff
      (Prescribed.validCandidate sel) w hAway edge.1).mpr hEdge.1, ?_⟩
    rw [← NonTrivalentValencyTwoDescent.retainedRow_mk src sel (wallValid m wd) edge, hEdge.2]
  · intro first _ second _ hEq
    exact ResolutionAwayFromWall.retainedEdge_injective
      (Prescribed.validCandidate sel) (wallValid m wd).1 hEq
  · intro edge hEdge
    simp only [Finset.mem_filter, mem_incidentEdges] at hEdge
    have hMem : edge.1 ∈ nonDanglingIncident (Prescribed.validCandidate sel).datum
        (ResolutionAwayFromWall.retainedVertex (Prescribed.validCandidate sel) w) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hEdge.1⟩
    rw [ResolutionAwayFromWall.nonDanglingIncident_retainedVertex
      (Prescribed.validCandidate sel) (wallValid m wd)
      (NonTrivalentValencyTwoRows.candidate_sourceGenus sel) w hAway] at hMem
    obtain ⟨old, hOld, hEqual⟩ := Finset.mem_image.mp hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hOld
    refine ⟨⟨old, hSurvives⟩, ?_, Subtype.ext hEqual⟩
    refine Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr hIncident,
      injective_retainedRow m wd src sel hOrd ?_⟩
    rw [NonTrivalentValencyTwoDescent.retainedRow_mk src sel (wallValid m wd)
      (⟨old, hSurvives⟩ : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)),
      show ResolutionAwayFromWall.retainedEdge (Prescribed.validCandidate sel)
        (wallValid m wd).1 ⟨old, hSurvives⟩ = edge from Subtype.ext hEqual]
    exact hEdge.2

end Retained

/-! ## 7.  The link, reduced to the star count -/

section Link

variable (hNoReturn : NoContractedReturn wd.cover wd.contracted)
  {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hOrd : NonTrivalentValencyTwoRowEquiv.OrdinaryTrivalent
    (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk)

/-- **`OuterWalk.TypeChangeLink` at a two-valent wall, from the star count
alone.**  `NonTrivalentValencyTwoExit.typeChangeLink_of_receipts` takes two
receipts, `hPathEnds` and `tracks`;
`WallDatumPathEnds.typeChangeLink_of_receipts'` discharges the first, and
`MovedIncidenceIso.tracksOfMovedIncidence` reduces `tracks` to a branch-vertex
bijection and a star count against the *permuted* vertex map.
With `vertexEquiv` supplying the bijection, exactly one geometric obligation is
left: the star count `hIncidence`.  At a branch vertex away from the anchor it
is the composite of the two transports (T1) and (T2) of the module docstring,
and at `A_u`/`A_v` it is what (H-II) prescribes together with the exact anchor
stars of `NonTrivalentValencyTwoRows`. -/
def typeChangeLink_of_incidence
    (hIncidence : ∀ (v : BranchVertex (Prescribed.validCandidate sel).datum)
        (r : StablePath (Prescribed.validCandidate sel).datum),
      incidenceCount (Prescribed.validCandidate sel).datum v.1 r =
        Nat.card {d : D // graph.vert (m.perm d) =
            vertexEquiv m wd hNoReturn src sel hOrd v ∧
          label d = (NonTrivalentValencyTwoExit.wallOutgoingFD m wd hNoReturn src sel hOrd
            (WallDatumPathEnds.hasPathEnds_wallData m wd hNoReturn src sel
              hOrd)).labelling.row r}) :
    TypeChangeLink m wd :=
  WallDatumPathEnds.typeChangeLink_of_receipts' m wd hNoReturn src sel hOrd
    (MovedIncidenceIso.tracksOfMovedIncidence _ _ graph m label
      (vertexEquiv m wd hNoReturn src sel hOrd)
      (MovedIncidenceIso.label_op_of_tracks _ wd.fullDim wd.tracks) hIncidence)

end Link

end Anchor

end

end DraismaVargas.LocalCases.NonTrivalentValencyTwoTracks
