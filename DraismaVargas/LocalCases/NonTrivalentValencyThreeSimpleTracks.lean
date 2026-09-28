import DraismaVargas.LocalCases.NonTrivalentValencyThreeTracks
import DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleExit

/-!
# The vertex dictionary of the valency-three Type I / Type II type change, and (H-I/II)

Source: Vargas, Part II, Section 5.1 (a combinatorial type change is recorded
as a Whitehead move on the *ambient* tracked graph; the labelling convention
(1)) and Section 5.3, case `{v3-nd4}` (base trees `T_alpha` with `alpha`
simple: the anchor `A` resolves into `A_u`, the **divalent** `A'` and `A_v`,
and the resulting combinatorial type has `{h_alpha, h_delta}` meeting at `A_u`
and `{h_beta, h_gamma}` meeting at `A_v`), together with Draisma--Vargas
Part I's stable graph `H(M)` with its row labels (the definition of
non-dangling valency and the subsection on inherited properties of limits) and
its `lemma-ndval-of-GqA0`.

This module supplies the vertex half of the `tracks` field of the valency-three
Type I / Type II link; it is the Types I/II sibling of
`NonTrivalentValencyThreeTracks` (Type III), over the exit
`NonTrivalentValencyThreeSimpleExit`.  The Types I/II candidates over the
two-fold branch gauge `SimpleBase.gaugedData` are built in
`NonTrivalentValencyThreeSimpleCandidate`, their rows, descent, row
equivalence and common minor in `NonTrivalentValencyThreeSimpleRows`,
`NonTrivalentValencyThreeSimpleRowEquiv` and
`NonTrivalentValencyThreeSimpleRowDictionary`, and the outgoing presentation
`wallOutgoingFD` and `typeChangeLink_of_receipts`, whose only receipt is
`tracks`, in `NonTrivalentValencyThreeSimpleExit`.
`MovedIncidenceIso.tracksOfMovedIncidence` reduces `tracks` to a branch-vertex
bijection
`vertexEquiv : BranchVertex cand.datum ≃ V` and a star count `hIncidence`
against the *permuted* vertex map of `graph.move m`.  This module delivers the
bijection, the hypothesis (H-I/II) that pins the anchor half of the star
count, and the two off-wall pieces of that count.

## What is reused from `NonTrivalentValencyThreeTracks`, not restated

The whole of Section 1 and Section 2 of `NonTrivalentValencyThreeTracks` is
about the *incoming* cover and the *wall datum*, not about the candidate, and
`ThreeBranchAnchor` is exactly what `SimpleBase.source` carries.  So

* `facetRow`, `facetEdge`, `facetEdge_stablePath`, `leftEnd`, `rightEnd` (the
  vanishing occurrence `h_1` and its two ends `A_u`, `A_v` upstairs),
* `three_le_nonDanglingValency_end` (both ends are branch vertices, because
  `NoContractedReturn` is receipt-free at a three-valent wall by
  `NonTrivalentValencyThreeRowDictionary.noContractedReturn_of_threeStar`),
  `eq_facetEdge` (the vanishing row *is* that single occurrence),
* `anchorVertex`, `sourceVertexMap_leftEnd_eq_anchorVertex` (the vanishing
  occurrence lies over the anchor), `eq_leftEnd_or_eq_rightEnd_of_mem_activeFibre`
  (the anchor fibre's branch vertices are exactly the two ends),
  `wallDatum_trivalent_away_anchor`,
* `branchEquivAnchorComplement` in its `hFibre`-free branch-pair form,
* `leftBranch`, `rightBranch`, `facetDartLeft`, `facetDartRight`, `liftEdge`,
  `coverBranchEquiv`, `vert_base_eq`, `vert_opBase_eq`, `op_base_eq`,
* and the two valency-agnostic pieces of the star count
  `move_vert_eq_iff_of_ne`, `card_star_eq_incidenceCount`

are imported and applied with `src := base.source`; nothing of them is copied.

## What is proved here

### 1.  The gauge leg

The Types I/II candidate lives over `SimpleBase.gaugedData`, the two-fold
branch gauge of the wall datum, not over the wall datum itself, so every
dictionary of `NonTrivalentValencyThreeTracks` has to cross two sheet
relabellings.

* `gaugeVertexEquiv`, `nonDanglingValency_gaugeVertexEquiv`,
  `gaugeVertexEquiv_sourceEndpoint_wall`, `gaugeVertexEquiv_anchor`: the gauge
  is a bijection on source vertices that moves no surviving valency and fixes
  every wall vertex (both branch gauges act trivially at the wall, by
  `first_vertexPermutation_wall` / `second_vertexPermutation_wall`), so it
  carries the anchor to `gaugedAnchorVertex`.
* `gaugeBranchEquiv`, `gaugeBranchEquivAnchorComplement`: the same on branch
  vertices, and on branch vertices away from the anchor -- the valency-three
  analogue of the `gaugeBranchEquivAnchorComplement` of the other gauged type
  changes (for instance `NonTrivalentValencyFourTracks`).
* `branchEquivGaugedAnchorComplement`: the composite of the contraction
  dictionary of `NonTrivalentValencyThreeTracks` with the gauge,
  `{v : BranchVertex M // v ≠ A_u, A_v} ≃ {w : BranchVertex gaugedData // w ≠ A}`.
* `incidenceCount_sheetRelabel_gauge`: **the gauge leg of the star-count
  transport (T2)**, `incidenceCount data v r =
  incidenceCount gaugedData (gaugeVertexEquiv v) (gaugeStablePath r)`, twice
  `StableGraphIncidence.incidenceCount_sheetRelabel` along
  `NonTrivalentValencyThreeSimpleRowDictionary.gaugeStablePath`.

### 2.  The branch vertices of the candidate

* `candVertex`, `nonDanglingValency_candVertex`: the outgoing vertex over a
  gauged wall-datum vertex other than the anchor -- `endpointVertex true` over
  the wall, `ResolutionAwayFromWall.retainedVertex` away from it -- with
  unchanged surviving valency.
* `candBranchMap`, `candBranchEquiv`: **the branch vertices of the Types I/II
  candidate are the branch vertices of the gauged datum other than the anchor,
  plus `A_u` and `A_v`.**  `A'` is divalent
  (`nonDanglingValency_deltaRight`) and is therefore **not** a branch vertex:
  this is the one structural difference from Type III, and it is what makes
  surjectivity a four-way case analysis (fresh/old target vertex, anchor/
  ordinary block, delta/hub class) rather than the three-way one of
  `NonTrivalentValencyThreeTracks`.  The case analysis is
  `NonTrivalentValencyThreeSimpleExit.candidate_trivalent` read as a
  classification.

### 3.  Two pieces of the star count, off the wall

* `injective_retainedRow`: from
  `NonTrivalentValencyThreeSimpleRowEquiv.rowEquiv_retainedRow` (the
  complement of the retained image is the bridge row).
* `incidenceCount_retainedVertex_retainedRow`: **away from the wall the
  candidate does not change the star**;
  `ResolutionStableIncidence.incidenceCount_retainedVertex` with its row
  *equivalence* hypothesis weakened to that injectivity, which is all the
  proof uses.
* `move_vert_eq_iff_of_ne`, `card_star_eq_incidenceCount`: the two
  valency-agnostic pieces of `NonTrivalentValencyThreeTracks`, re-exported by
  application.

### 4.  The vertex dictionary

* `vertexEquiv`: the composite
  `BranchVertex cand.datum ≃ BranchVertex gaugedData-minus-A + Bool ≃
   BranchVertex M-minus-ends + Bool ≃ BranchVertex M ≃ V`,
  the middle step being `branchEquivGaugedAnchorComplement` and the last the
  incoming tracking `wd.tracks.iso.vtx`.
* `vertexEquiv_inl`, `vertexEquiv_anchor`, and under (H-I/II)'s orientation
  `vertexEquiv_anchor_false` (`A_u ↦ graph.vert m.base`),
  `vertexEquiv_anchor_true` (`A_v ↦ graph.vert (graph.op m.base)`).

### 5.  (H-I/II)

* `PrescribedSimpleMove m wd base`: the two darts the Whitehead move places
  together with `m.base` -- the moved star of `graph.vert m.base` with
  `m.base` removed -- are, under `wd.tracks.iso.dart`, darts carrying the stable
  **rows** of the two survivors that the Types I/II resolution brings together
  at `A_u`, namely `e_alpha` and `e_delta`, in the orientation that puts `A_u`
  at `graph.vert m.base`.  The clause is at row level
  (`d.2.1.stablePath = ...`): `e_delta` may reach `A_u` through a pass-through
  occurrence over the contracted target edge, and it is the row, not the
  occurrence, that the star count consumes
  (`IncomingPairing.label_dart_of_row`).  **One clause covers both Type I and
  Type II**: Part II says the resulting type has `{h_alpha, h_delta}` at `A_u`
  and `{h_beta, h_gamma}` at `A_v` for every realized pair
  `(alpha, delta) ∈ {3,4} × {2,5}`, and Types I and II differ only in *which*
  pair is realized (the order condition carried by `SimpleBase`), not in which
  survivors the resolution pairs.  The exact star at `A_u` is
  `{e_1, e', e_alpha}`
  (`NonTrivalentValencyThreeSimpleRows.nonDanglingIncident_hubLeft`), where
  `e_1` is the
  bridge, alone on the new row (`bridgeEdge_isolated`), and `e'` carries the
  retained row of `e_delta` (`newSourceEdge_stablePath_eq_retained`), so the
  three *stable rows* at `A_u` are `h_1`, `h_alpha`, `h_delta`, exactly as the
  clause names.  The other orientation is normalised by the caller with
  `CubicDarts.MoveData.swap`, which leaves `graph.move m` unchanged.
* `prescribedSimpleMove_of_occurrence`: the old occurrence-level clause
  (`first.2.1 = alphaLift ...`) implies (H-I/II).
* `prescribedSimpleMove_of_rows`: (H-I/II) from the orientation clause together
  with two moved darts carrying the rows of `e_alpha` and `e_delta` -- the shape
  `IncomingPairing.exists_movedStar_darts` produces, and the one the valency
  dispatcher consumes.  At row level separation is automatic
  (`IncomingPairing.vertex_of_movedStar_eq_pair`), so `SimpleSeparated` is not a
  hypothesis of it.
* `SimpleSeparated`: the geometric content of a *type change* -- `e_alpha` and
  `e_delta` lift to occurrences at the two **different** ends of `h_1`.
  Without it `A_u` sees exactly the star of `leftEnd` and no Whitehead move
  takes place.  With (H-I/II) stated at row level it is the geometric input of
  the relative witness only.
* `prescribedMove`, `prescribedSimpleMove_prescribedMove`: **non-vacuity of
  (H-I/II), in relative form**, exactly as
  `NonTrivalentValencyThreeTracks.prescribedDoubledMove_prescribedMove`.  An
  absolute
  `∃ m, PrescribedSimpleMove m wd base` does not typecheck, because
  `wd : WallData arrival` with
  `arrival : FacetArrival degree graph label (label m.base)` fixes `m.base`;
  the witness is produced with that same `base` field.

### 6.  The link

* `typeChangeLink_of_incidence`: **`OuterWalk.TypeChangeLink` at a
  three-valent wall, Types I/II, from the star count alone** -- `vertexEquiv`
  into `MovedIncidenceIso.tracksOfMovedIncidence` and the result into
  `NonTrivalentValencyThreeSimpleExit.typeChangeLink_of_receipts`.  `hOp` is
  free from the incoming tracking through
  `MovedIncidenceIso.label_op_of_tracks`.


## The hypotheses that remain explicit here

1. `hIncidence`, hence `tracks`: the star count
   `incidenceCount cand.datum v r =
    Nat.card {d // (graph.move m).vert d = vertexEquiv v and label d = row r}`.
   This composite is not proved in this file;
   `NonTrivalentValencyThreeSimpleStarCount` proves it, as the composite of
   three transports:
   * (T1) `incidenceCount gaugedData w r =
     incidenceCount cand.datum (candVertex w) (retainedRow r)`.  Away from the
     wall this is `incidenceCount_retainedVertex_retainedRow` above; **at an
     ordinary wall block** it is
     `NonTrivalentValencyThreeSimpleStarCount.incidenceCount_endpointVertex_true_ordinary`,
     from the census of `NonTrivalentValencyThreeSimpleRows`
     (`nonDanglingIncident_endpointVertex_true_ordinary`, which lists the star
     of `B_v` as the retained copies of the beta/gamma-side star together with
     one new occurrence per member of the alpha-side star, plus
     `newSourceEdge_stablePath_eq_retained`, which puts that new occurrence on
     the retained row of the survivor it replaces).
   * (T2) the gauge leg `incidenceCount_sheetRelabel_gauge`, **proved here**,
     composed with `incidenceCount M_0 w r =
     incidenceCount M (branchEquivAnchorComplement.symm w) (incomingRow r)`.
     The latter is `WallSplitIncidence.incidenceCount_sourceVertexMap` away
     from the merged target vertex; **at an ordinary wall block** it is the
     valency-agnostic `WallSplitIncidenceOrdinary.incidenceCount_unramified`
     (applied in `NonTrivalentValencyThreeSimpleStarCount`; it is not a special
     case of `WallSplitIncidence.incidenceCount_anchor`, whose `hFacetOver`
     hypothesis fails there).
   * At the anchor the count is the one (H-I/II) prescribes, together with
     the exact stars `nonDanglingIncident_hubLeft` /
     `nonDanglingIncident_hubRight` and `move_vert_eq_iff_of_ne` /
     `card_star_eq_incidenceCount` on the dart side.  The divalent `A'` costs
     nothing here -- it is not a branch vertex, so no count is asked of it --
     but it *does* mean the row `h_delta` at `A_u` is carried by `e'`, not by a
     retained copy of `e_delta`, so the anchor count must read the row through
     `newSourceEdge_stablePath_eq_retained`.
     `NonTrivalentValencyThreeSimpleStarCount` packages the result as
     `typeChangeLink_of_prescribedSimpleMove`: `OuterWalk.TypeChangeLink` at a
     three-valent wall from (H-I/II) and `wallStar` alone.
2. `SimpleSeparated`, and (H-I/II) itself.  (H-I/II) is the per-vertex match at
   the anchor; `SimpleSeparated` is what makes the wall crossing an actual type
   change.  Neither is derived here.  With (H-I/II) stated at row level,
   `SimpleSeparated` is a hypothesis of the relative witness only; the valency
   dispatcher `NonTrivalentValencyThreeDispatcher` discharges (H-I/II) through
   `prescribedSimpleMove_of_rows`.
3. `wallStar : ThirdEquation.ThreeStar (contract wd.coverTarget wd.hab wd.hOne)
   ⟨wd.a, wd.hab⟩`, exactly as in `NonTrivalentValencyThreeExit`,
   `NonTrivalentValencyThreePathEnds`, `NonTrivalentValencyThreeTracks` and
   `NonTrivalentValencyThreeSimpleExit`: the valency dispatcher
   `NonTrivalentValencyThreeDispatcher` produces it from
   `OuterWalk.WallData.valency`, not this module.
4. Nothing here chooses between Types I, II and III; the type is fixed by the
   `SimpleBase` the caller supplies, and
   `NonTrivalentValencyThreeDispatcher.classify` chooses it from the move.

No structure is introduced.  The two `Prop` definitions ship as follows:
`PrescribedSimpleMove` has the relative witness
`prescribedSimpleMove_prescribedMove`; `SimpleSeparated` is a named hypothesis
of that witness, in the same style as
`StablePathFacetContraction.NoContractedReturn` and
`NonTrivalentValencyThreeTracks.DoubledSeparated`, and is not inhabited here.

## Used by

`NonTrivalentValencyThreeSimpleStarCount` proves (T1), (T2) and the
anchor count above and delivers `typeChangeLink_of_prescribedSimpleMove`:
`OuterWalk.TypeChangeLink` at a three-valent wall, Types I and II, from
(H-I/II) and `wallStar` alone, via `MovedIncidenceIso.tracksOfMovedIncidence`
and hence the `tracks` field of
`NonTrivalentValencyThreeSimpleExit.typeChangeLink_of_receipts`.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleTracks

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.ThirdEquation
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.ClassInjectivity
open DraismaVargas.LocalCases.NonTrivalentValencyThreeAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyThreeCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleRows
open DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleRowEquiv

noncomputable section

/-! ## 1.  The gauge leg: the candidate lives over `SimpleBase.gaugedData` -/

section Gauge

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {anchor : WallBlock data wall} (base : SimpleBase data star anchor)

/-- The first branch gauge on source vertices. -/
def firstVertexEquiv : data.SourceVertex ≃ base.middleData.SourceVertex :=
  base.firstRelabeling.sourceVertexEquiv

/-- **The two branch gauges as one bijection on source vertices.** -/
def gaugeVertexEquiv : data.SourceVertex ≃ base.gaugedData.SourceVertex :=
  (firstVertexEquiv base).trans base.secondRelabeling.sourceVertexEquiv

@[simp] theorem gaugeVertexEquiv_target (v : data.SourceVertex) :
    (gaugeVertexEquiv base v).1.1 = v.1.1 := rfl

/-- **The gauge moves no surviving valency.** -/
theorem nonDanglingValency_gaugeVertexEquiv (hValid : data.Valid) (v : data.SourceVertex) :
    nonDanglingValency base.gaugedData (gaugeVertexEquiv base v) =
      nonDanglingValency data v :=
  (SheetRelabelStable.nonDanglingValency_map base.secondRelabeling
    (middleData_connected base hValid) (firstVertexEquiv base v)).trans
    (SheetRelabelStable.nonDanglingValency_map base.firstRelabeling hValid.1 v)

theorem firstVertexEquiv_sourceEndpoint_wall (sheet : Fin degree) :
    firstVertexEquiv base (data.sourceEndpoint wall sheet) =
      base.middleData.sourceEndpoint wall sheet := by
  show base.firstRelabeling.sourceVertexEquiv (data.sourceEndpoint wall sheet) =
    base.firstRelabeling.apply.sourceEndpoint wall sheet
  rw [SheetRelabelPruning.sourceVertexEquiv_sourceEndpoint base.firstRelabeling wall sheet,
    first_vertexPermutation_wall base]
  rfl

theorem secondVertexEquiv_sourceEndpoint_wall (sheet : Fin degree) :
    base.secondRelabeling.sourceVertexEquiv (base.middleData.sourceEndpoint wall sheet) =
      base.gaugedData.sourceEndpoint wall sheet := by
  show base.secondRelabeling.sourceVertexEquiv (base.middleData.sourceEndpoint wall sheet) =
    base.secondRelabeling.apply.sourceEndpoint wall sheet
  rw [SheetRelabelPruning.sourceVertexEquiv_sourceEndpoint base.secondRelabeling wall sheet,
    second_vertexPermutation_wall base]
  rfl

/-- **The gauge fixes every wall vertex**: both branch gauges act trivially at
the wall (`first_vertexPermutation_wall`, `second_vertexPermutation_wall`). -/
theorem gaugeVertexEquiv_sourceEndpoint_wall (sheet : Fin degree) :
    gaugeVertexEquiv base (data.sourceEndpoint wall sheet) =
      base.gaugedData.sourceEndpoint wall sheet := by
  show base.secondRelabeling.sourceVertexEquiv
    (firstVertexEquiv base (data.sourceEndpoint wall sheet)) = _
  rw [firstVertexEquiv_sourceEndpoint_wall base sheet,
    secondVertexEquiv_sourceEndpoint_wall base sheet]

/-- The anchor of the gauged wall datum. -/
def gaugedAnchorVertex : base.gaugedData.SourceVertex :=
  base.gaugedData.sourceEndpoint wall anchor.1

theorem gaugeVertexEquiv_anchor :
    gaugeVertexEquiv base (WallBlock.sourceVertex data wall anchor) =
      gaugedAnchorVertex base :=
  gaugeVertexEquiv_sourceEndpoint_wall base anchor.1

/-- **The branch vertices across the gauge.** -/
def gaugeBranchEquiv (hValid : data.Valid) :
    BranchVertex data ≃ BranchVertex base.gaugedData :=
  (gaugeVertexEquiv base).subtypeEquiv fun v ↦ by
    rw [nonDanglingValency_gaugeVertexEquiv base hValid v]

@[simp] theorem gaugeBranchEquiv_val (hValid : data.Valid) (v : BranchVertex data) :
    (gaugeBranchEquiv base hValid v).1 = gaugeVertexEquiv base v.1 := rfl

/-- **The branch vertices away from the anchor, across the gauge.** -/
def gaugeBranchEquivAnchorComplement (hValid : data.Valid) :
    {w : BranchVertex data // w.1 ≠ WallBlock.sourceVertex data wall anchor} ≃
      {w : BranchVertex base.gaugedData // w.1 ≠ gaugedAnchorVertex base} :=
  (gaugeBranchEquiv base hValid).subtypeEquiv fun w ↦ by
    show w.1 ≠ WallBlock.sourceVertex data wall anchor ↔
      gaugeVertexEquiv base w.1 ≠ gaugedAnchorVertex base
    constructor
    · intro hw hBad
      exact hw ((gaugeVertexEquiv base).injective
        (hBad.trans (gaugeVertexEquiv_anchor base).symm))
    · intro hw hBad
      exact hw (by rw [hBad, gaugeVertexEquiv_anchor base])

@[simp] theorem gaugeBranchEquivAnchorComplement_apply (hValid : data.Valid)
    (w : {w : BranchVertex data // w.1 ≠ WallBlock.sourceVertex data wall anchor}) :
    (gaugeBranchEquivAnchorComplement base hValid w).1.1 = gaugeVertexEquiv base w.1.1 := rfl

section GaugeIncidence

open DraismaVargas.LocalCases.StablePathCount

/-- **The gauge leg of the star-count transport (T2).**  Each of the two branch
gauges is a sheet relabelling, so it carries every row-filtered star to the
corresponding one (`StableGraphIncidence.incidenceCount_sheetRelabel`); the
composite row map is `NonTrivalentValencyThreeSimpleRowDictionary.gaugeStablePath`,
the same one `gaugedLabelling_row` uses on the matrix side. -/
theorem incidenceCount_sheetRelabel_gauge (hValid : data.Valid) (v : data.SourceVertex)
    (r : StablePath data) :
    incidenceCount data v r =
      incidenceCount base.gaugedData (gaugeVertexEquiv base v)
        (NonTrivalentValencyThreeSimpleRowDictionary.gaugeStablePath base hValid r) :=
  (StableGraphIncidence.incidenceCount_sheetRelabel base.firstRelabeling hValid.1 v r).trans
    (StableGraphIncidence.incidenceCount_sheetRelabel base.secondRelabeling
      (middleData_connected base hValid) _ _)

end GaugeIncidence


end Gauge

/-! ## 2.  The branch vertices of the Type I / Type II candidate -/

section Candidate

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {anchor : WallBlock data wall} (base : SimpleBase data star anchor)
  (hValid : data.Valid)

theorem sourceEndpoint_self (w : base.gaugedData.SourceVertex) (hw : w.1.1 = wall) :
    base.gaugedData.sourceEndpoint wall w.1.2 = w :=
  (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hw.symm, rfl⟩

/-- A gauged wall vertex other than the anchor is an ordinary block. -/
theorem not_rel_anchor_of_ne (w : base.gaugedData.SourceVertex) (hw : w.1.1 = wall)
    (hne : w ≠ gaugedAnchorVertex base) :
    ¬ (data.vertexPartition wall).Rel anchor.1 w.1.2 := by
  intro hBad
  exact hne ((sourceEndpoint_self base w hw).symm.trans
    (sourceEndpoint_eq_of_rel base ((gauged_rel_iff base).mpr hBad)).symm)

open scoped Classical in
/-- **The outgoing vertex over a gauged wall-datum vertex other than the
anchor.**  Over the wall the candidate keeps the whole block on the trivalent
side `v`; away from it the vertex is simply retained. -/
def candVertex (w : base.gaugedData.SourceVertex) :
    (validCandidate base hValid).datum.SourceVertex :=
  if w.1.1 = wall then endpointVertex base hValid true w.1.2
  else ResolutionAwayFromWall.retainedVertex (validCandidate base hValid) w

theorem candVertex_wall (w : base.gaugedData.SourceVertex) (hw : w.1.1 = wall) :
    candVertex base hValid w = endpointVertex base hValid true w.1.2 := by
  unfold candVertex
  rw [if_pos hw]

theorem candVertex_away (w : base.gaugedData.SourceVertex) (hw : w.1.1 ≠ wall) :
    candVertex base hValid w =
      ResolutionAwayFromWall.retainedVertex (validCandidate base hValid) w := by
  unfold candVertex
  rw [if_neg hw]

/-- **The surviving valency is unchanged.** -/
theorem nonDanglingValency_candVertex (w : base.gaugedData.SourceVertex)
    (hne : w ≠ gaugedAnchorVertex base) :
    nonDanglingValency (validCandidate base hValid).datum (candVertex base hValid w) =
      nonDanglingValency base.gaugedData w := by
  classical
  by_cases hw : w.1.1 = wall
  · rw [candVertex_wall base hValid w hw,
      nonDanglingValency_endpointVertex_true_ordinary base hValid
        (not_rel_anchor_of_ne base w hw hne),
      sourceEndpoint_self base w hw]
  · rw [candVertex_away base hValid w hw,
      ResolutionAwayFromWall.nonDanglingValency_retainedVertex (validCandidate base hValid)
        (base.gaugedData_valid hValid) (candidate_sourceGenus base hValid) w hw]

theorem endpointVertex_target (side : Bool) (y : Fin degree) :
    (endpointVertex base hValid side y).1.1 =
      (if side then freshVertex target else oldVertex target wall) :=
  ((GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mp rfl).1.symm

theorem candVertex_wall_target (w : base.gaugedData.SourceVertex) (hw : w.1.1 = wall) :
    (candVertex base hValid w).1.1 = freshVertex target := by
  rw [candVertex_wall base hValid w hw]
  exact endpointVertex_target base hValid true w.1.2

theorem candVertex_away_target (w : base.gaugedData.SourceVertex) (hw : w.1.1 ≠ wall) :
    (candVertex base hValid w).1.1 = oldVertex target w.1.1 := by
  rw [candVertex_away base hValid w hw]
  exact ((GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mp rfl).1.symm

/-- Two vertices of the candidate over the fresh target vertex coincide exactly
when their sheets are related there. -/
theorem endpointVertex_true_inj {y y' : Fin degree}
    (hEq : endpointVertex base hValid true y = endpointVertex base hValid true y') :
    ((validCandidate base hValid).datum.vertexPartition (freshVertex target)).Rel y y' := by
  have h := (GluingDatum.sourceEndpoint_eq_iff (validCandidate base hValid).datum
      (freshVertex target) y (endpointVertex base hValid true y')).mp hEq
  set part := (validCandidate base hValid).datum.vertexPartition (freshVertex target) with hpart
  have h2 : part.repr y = part.repr (endpointVertex base hValid true y').1.2 := h.2
  have hs : (endpointVertex base hValid true y').1.2 = part.repr y' := rfl
  show part.repr y = part.repr y'
  rw [h2, hs, part.repr_idem]


/-- **The branch vertices of the outgoing candidate.**  Every branch vertex of
the Type I / Type II candidate is either the outgoing copy of a branch vertex of
the gauged wall datum other than the anchor, or one of `A_u`, `A_v`.  The third
new anchor vertex `A'` is **divalent**, so it is not a branch vertex. -/
def candBranchMap :
    ({w : BranchVertex base.gaugedData // w.1 ≠ gaugedAnchorVertex base} ⊕ Bool) →
      BranchVertex (validCandidate base hValid).datum
  | Sum.inl w => ⟨candVertex base hValid w.1.1, by
      rw [nonDanglingValency_candVertex base hValid w.1.1 w.2]
      exact w.1.2⟩
  | Sum.inr side => ⟨endpointVertex base hValid side base.hubSheet, by
      cases side with
      | false => exact (nonDanglingValency_hubLeft base hValid).ge
      | true => exact (nonDanglingValency_hubRight base hValid).ge⟩

theorem candBranchMap_injective : Function.Injective (candBranchMap base hValid) := by
  classical
  have hWallTarget : ∀ w : {w : BranchVertex base.gaugedData // w.1 ≠ gaugedAnchorVertex base},
      w.1.1.1.1 = wall → ¬ (data.vertexPartition wall).Rel anchor.1 w.1.1.1.2 :=
    fun w hw ↦ not_rel_anchor_of_ne base w.1.1 hw w.2
  rintro (w | side) (w' | side') hEq <;>
    have hv : (candBranchMap base hValid _).1 = (candBranchMap base hValid _).1 :=
      congrArg Subtype.val hEq
  · by_cases hw : w.1.1.1.1 = wall <;> by_cases hw' : w'.1.1.1.1 = wall
    · have hEq2 : endpointVertex base hValid true w.1.1.1.2 =
          endpointVertex base hValid true w'.1.1.1.2 := by
        rw [← candVertex_wall base hValid w.1.1 hw, ← candVertex_wall base hValid w'.1.1 hw']
        exact hv
      have hRel := (candidate_vertexPartition_rel_ordinary base hValid true
        (hWallTarget w hw)).mp (endpointVertex_true_inj base hValid hEq2)
      have hSheet : w.1.1.1.2 = w'.1.1.1.2 := by
        have h1 : (base.gaugedData.vertexPartition w.1.1.1.1).repr w.1.1.1.2 = w.1.1.1.2 :=
          w.1.1.2
        have h2 : (base.gaugedData.vertexPartition w'.1.1.1.1).repr w'.1.1.1.2 = w'.1.1.1.2 :=
          w'.1.1.2
        rw [hw] at h1
        rw [hw'] at h2
        rw [← h1, ← h2]
        exact hRel
      exact congrArg Sum.inl (Subtype.ext (Subtype.ext (Subtype.ext
        (Prod.ext (hw.trans hw'.symm) hSheet))))
    · exact absurd ((candVertex_wall_target base hValid w.1.1 hw).symm.trans
        ((congrArg (fun z : (validCandidate base hValid).datum.SourceVertex ↦ z.1.1) hv).trans
          (candVertex_away_target base hValid w'.1.1 hw'))) Sum.inr_ne_inl
    · exact absurd ((candVertex_away_target base hValid w.1.1 hw).symm.trans
        ((congrArg (fun z : (validCandidate base hValid).datum.SourceVertex ↦ z.1.1) hv).trans
          (candVertex_wall_target base hValid w'.1.1 hw'))) Sum.inl_ne_inr
    · have hRet : ResolutionAwayFromWall.retainedVertex (validCandidate base hValid) w.1.1 =
          ResolutionAwayFromWall.retainedVertex (validCandidate base hValid) w'.1.1 := by
        rw [← candVertex_away base hValid w.1.1 hw, ← candVertex_away base hValid w'.1.1 hw']
        exact hv
      exact congrArg Sum.inl (Subtype.ext (Subtype.ext
        (ResolutionStableIncidence.retainedVertex_injective_away (validCandidate base hValid)
          w.1.1 w'.1.1 hw hw' hRet)))
  · exfalso
    have hv' : candVertex base hValid w.1.1 =
        endpointVertex base hValid side' base.hubSheet := hv
    have hTarget := congrArg
      (fun z : (validCandidate base hValid).datum.SourceVertex ↦ z.1.1) hv'
    rw [endpointVertex_target base hValid side' base.hubSheet] at hTarget
    by_cases hw : w.1.1.1.1 = wall
    · rw [candVertex_wall_target base hValid w.1.1 hw] at hTarget
      cases side' with
      | false => exact Sum.inr_ne_inl hTarget
      | true =>
        have hEq2 : endpointVertex base hValid true w.1.1.1.2 =
            endpointVertex base hValid true base.hubSheet := by
          rw [← candVertex_wall base hValid w.1.1 hw]
          exact hv'
        have hRel := (candidate_vertexPartition_rel_ordinary base hValid true
          (hWallTarget w hw)).mp (endpointVertex_true_inj base hValid hEq2)
        exact hWallTarget w hw
          (base.hubSheet_wall.trans ((gauged_rel_iff base).mp hRel).symm)
    · rw [candVertex_away_target base hValid w.1.1 hw] at hTarget
      cases side' with
      | false => exact hw (Sum.inl_injective hTarget)
      | true => exact Sum.inl_ne_inr hTarget
  · exfalso
    have hv' : endpointVertex base hValid side base.hubSheet =
        candVertex base hValid w'.1.1 := hv
    have hTarget := congrArg
      (fun z : (validCandidate base hValid).datum.SourceVertex ↦ z.1.1) hv'
    rw [endpointVertex_target base hValid side base.hubSheet] at hTarget
    by_cases hw : w'.1.1.1.1 = wall
    · rw [candVertex_wall_target base hValid w'.1.1 hw] at hTarget
      cases side with
      | false => exact Sum.inl_ne_inr hTarget
      | true =>
        have hEq2 : endpointVertex base hValid true base.hubSheet =
            endpointVertex base hValid true w'.1.1.1.2 := by
          rw [← candVertex_wall base hValid w'.1.1 hw]
          exact hv'
        have hRel := (candidate_vertexPartition_rel_ordinary base hValid true
          (hWallTarget w' hw)).mp (endpointVertex_true_inj base hValid hEq2.symm)
        exact hWallTarget w' hw
          (base.hubSheet_wall.trans ((gauged_rel_iff base).mp hRel).symm)
    · rw [candVertex_away_target base hValid w'.1.1 hw] at hTarget
      cases side with
      | false => exact hw (Sum.inl_injective hTarget.symm)
      | true => exact Sum.inr_ne_inl hTarget
  · have hv' : endpointVertex base hValid side base.hubSheet =
        endpointVertex base hValid side' base.hubSheet := hv
    have hTarget := congrArg
      (fun z : (validCandidate base hValid).datum.SourceVertex ↦ z.1.1) hv'
    rw [endpointVertex_target base hValid side base.hubSheet,
      endpointVertex_target base hValid side' base.hubSheet] at hTarget
    cases side <;> cases side' <;>
      first
        | rfl
        | exact absurd hTarget Sum.inl_ne_inr
        | exact absurd hTarget Sum.inr_ne_inl

theorem candBranchMap_surjective : Function.Surjective (candBranchMap base hValid) := by
  classical
  intro v
  by_cases hFresh : v.1.1.1 = freshVertex target
  · have hV : endpointVertex base hValid true v.1.1.2 = v.1 :=
      NonTrivalentValencyThreeSimpleExit.eq_endpointVertex base hValid true v.1
        (by rw [hFresh]; rfl)
    by_cases hAnchor : (data.vertexPartition wall).Rel anchor.1 v.1.1.2
    · by_cases hDelta : v.1.1.2 ∈ base.newDeltaBlock
      · exfalso
        have hNd : nonDanglingValency (validCandidate base hValid).datum v.1 = 2 := by
          rw [← hV, ← endpointVertex_eq base hValid true base.deltaRepr_wall
            (base.right_rel_delta_of_mem hDelta)]
          exact nonDanglingValency_deltaRight base hValid
        have := v.2
        omega
      · refine ⟨Sum.inr true, Subtype.ext ?_⟩
        show endpointVertex base hValid true base.hubSheet = v.1
        rw [endpointVertex_eq base hValid true base.hubSheet_wall
          (base.right_rel_hub_of_mem (Finset.mem_sdiff.mpr
            ⟨mem_wholeBlock_of_wall_rel base hAnchor, hDelta⟩))]
        exact hV
    · have hNd : nonDanglingValency base.gaugedData
          (base.gaugedData.sourceEndpoint wall v.1.1.2) =
          nonDanglingValency (validCandidate base hValid).datum v.1 := by
        rw [← nonDanglingValency_endpointVertex_true_ordinary base hValid hAnchor, hV]
      have hwne : base.gaugedData.sourceEndpoint wall v.1.1.2 ≠ gaugedAnchorVertex base := by
        intro hBad
        refine hAnchor ((gauged_rel_iff base).mp ?_)
        have h := ((GluingDatum.sourceEndpoint_eq_iff base.gaugedData wall v.1.1.2
          (gaugedAnchorVertex base)).mp hBad).2
        set part := base.gaugedData.vertexPartition wall with hpart
        have hx : part.repr (gaugedAnchorVertex base).1.2 = part.repr anchor.1 :=
          part.repr_idem anchor.1
        show part.repr anchor.1 = part.repr v.1.1.2
        rw [← hx]
        exact h.symm
      have hNotRepr : ¬ (data.vertexPartition wall).Rel anchor.1
          ((base.gaugedData.vertexPartition wall).repr v.1.1.2) := by
        rw [base.gaugedData_vertexPartition_wall]
        exact fun h ↦ hAnchor (h.trans ((data.vertexPartition wall).rel_repr_right v.1.1.2).symm)
      refine ⟨Sum.inl ⟨⟨base.gaugedData.sourceEndpoint wall v.1.1.2, by rw [hNd]; exact v.2⟩,
        hwne⟩, Subtype.ext ?_⟩
      show candVertex base hValid (base.gaugedData.sourceEndpoint wall v.1.1.2) = v.1
      rw [candVertex_wall base hValid _ rfl]
      show endpointVertex base hValid true
        ((base.gaugedData.vertexPartition wall).repr v.1.1.2) = v.1
      rw [endpointVertex_eq_ordinary base hValid true hNotRepr
        ((base.gaugedData.vertexPartition wall).rel_repr_left v.1.1.2)]
      exact hV
  · obtain ⟨place, hplace⟩ : ∃ place, v.1.1.1 = oldVertex target place := by
      cases h : v.1.1.1 with
      | inl p => exact ⟨p, rfl⟩
      | inr u => exact absurd h hFresh
    by_cases hwall : place = wall
    · have hV : endpointVertex base hValid false v.1.1.2 = v.1 :=
        NonTrivalentValencyThreeSimpleExit.eq_endpointVertex base hValid false v.1
          (by rw [hplace, hwall]; rfl)
      by_cases hAnchor : (data.vertexPartition wall).Rel anchor.1 v.1.1.2
      · by_cases hAlpha : v.1.1.2 ∈ base.alphaBlock
        · refine ⟨Sum.inr false, Subtype.ext ?_⟩
          show endpointVertex base hValid false base.hubSheet = v.1
          rw [endpointVertex_eq base hValid false base.hubSheet_wall
            ((left_rel_hub_iff base).mpr hAlpha)]
          exact hV
        · exfalso
          have hCard := Finset.card_le_card
            (nonDanglingIncident_left_singleton_subset base hValid hAnchor hAlpha)
          rw [card_nonDanglingIncident, Finset.card_singleton, hV] at hCard
          have := v.2
          omega
      · exfalso
        have hSub : nonDanglingIncident (validCandidate base hValid).datum
            (endpointVertex base hValid false v.1.1.2) ⊆
              {(validCandidate base hValid).oldSourceEdge (alphaOccurrenceAt base v.1.1.2),
                (validCandidate base hValid).newSourceEdge v.1.1.2} := by
          intro e he
          rcases (mem_nonDanglingIncident_endpointVertex_false_ordinary base hValid
            hAnchor e).mp he with ⟨rfl, -⟩ | ⟨rfl, -⟩
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        have hCard := Finset.card_le_card hSub
        rw [card_nonDanglingIncident, hV] at hCard
        have hPair := Finset.card_insert_le
          ((validCandidate base hValid).oldSourceEdge (alphaOccurrenceAt base v.1.1.2))
          ({(validCandidate base hValid).newSourceEdge v.1.1.2} :
            Finset (validCandidate base hValid).datum.SourceEdge)
        rw [Finset.card_singleton] at hPair
        have := v.2
        omega
    · obtain ⟨old, hOld, hRet⟩ := ResolutionAwayFromWall.exists_retainedVertex_of_target
        (validCandidate base hValid) v.1 place hwall hplace
      have hAway : old.1.1 ≠ wall := by rw [hOld]; exact hwall
      have hNd : nonDanglingValency base.gaugedData old =
          nonDanglingValency (validCandidate base hValid).datum v.1 := by
        rw [← hRet, ResolutionAwayFromWall.nonDanglingValency_retainedVertex
          (validCandidate base hValid) (base.gaugedData_valid hValid)
          (candidate_sourceGenus base hValid) old hAway]
      have hne : old ≠ gaugedAnchorVertex base := by
        intro hBad
        refine hAway ?_
        rw [hBad]
        rfl
      refine ⟨Sum.inl ⟨⟨old, by rw [hNd]; exact v.2⟩, hne⟩, Subtype.ext ?_⟩
      show candVertex base hValid old = v.1
      rw [candVertex_away base hValid old hAway]
      exact hRet

theorem alphaSurvivor_survives : ¬ IsDangling data base.alphaSurvivor.1 :=
  (W3R1SourceProfile.mem_survivors _ _ _).mp
    ((mem_directionSurvivors _ _ _ _ _).mp base.alphaSurvivor_mem).1

theorem deltaSurvivor_survives : ¬ IsDangling data base.deltaSurvivor.1 :=
  (W3R1SourceProfile.mem_survivors _ _ _).mp
    ((mem_directionSurvivors _ _ _ _ _).mp base.deltaSurvivor_mem).1

/-- **The branch vertices of the Type I / Type II candidate.** -/
def candBranchEquiv :
    ({w : BranchVertex base.gaugedData // w.1 ≠ gaugedAnchorVertex base} ⊕ Bool) ≃
      BranchVertex (validCandidate base hValid).datum :=
  Equiv.ofBijective (candBranchMap base hValid)
    ⟨candBranchMap_injective base hValid, candBranchMap_surjective base hValid⟩

end Candidate

/-! ## 3.  Two pieces of the star count, off the wall -/

section Incidence

open DraismaVargas.LocalCases.StablePathCount

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {anchor : WallBlock data wall} (base : SimpleBase data star anchor)
  (hValid : data.Valid)

/-- **The retained-row map is injective**, from the row equivalence of
`NonTrivalentValencyThreeSimpleRowEquiv` (`rowEquiv_retainedRow`; the
complement of its image is the bridge row). -/
theorem injective_retainedRow : Function.Injective (retainedRow base hValid) := by
  intro r r' h
  have h2 := congrArg (rowEquiv base hValid) h
  rw [rowEquiv_retainedRow base hValid r, rowEquiv_retainedRow base hValid r'] at h2
  exact Option.some_injective _ h2

/-- **Away from the wall the candidate does not change the star.**  This is
`ResolutionStableIncidence.incidenceCount_retainedVertex` with its row
*equivalence* hypothesis weakened to injectivity of the retained-row map, which
is what the proof actually uses. -/
theorem incidenceCount_retainedVertex_retainedRow (w : base.gaugedData.SourceVertex)
    (hAway : w.1.1 ≠ wall) (row : StablePath base.gaugedData) :
    incidenceCount base.gaugedData w row =
      incidenceCount (validCandidate base hValid).datum
        (ResolutionAwayFromWall.retainedVertex (validCandidate base hValid) w)
        (retainedRow base hValid row) := by
  classical
  unfold incidenceCount
  apply Finset.card_bij (fun edge _ ↦ ResolutionAwayFromWall.retainedEdge
    (validCandidate base hValid) (base.gaugedData_valid hValid).1 edge)
  · intro edge hEdge
    simp only [Finset.mem_filter, mem_incidentEdges] at hEdge ⊢
    refine ⟨(ResolutionAwayFromWall.incident_oldSourceEdge_iff (validCandidate base hValid) w
      hAway edge.1).mpr hEdge.1, ?_⟩
    rw [← retainedRow_mk base hValid edge, hEdge.2]
  · intro first _ second _ hEq
    exact ResolutionAwayFromWall.retainedEdge_injective (validCandidate base hValid)
      (base.gaugedData_valid hValid).1 hEq
  · intro edge hEdge
    simp only [Finset.mem_filter, mem_incidentEdges] at hEdge
    have hMem : edge.1 ∈ nonDanglingIncident (validCandidate base hValid).datum
        (ResolutionAwayFromWall.retainedVertex (validCandidate base hValid) w) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hEdge.1⟩
    rw [ResolutionAwayFromWall.nonDanglingIncident_retainedVertex (validCandidate base hValid)
      (base.gaugedData_valid hValid) (candidate_sourceGenus base hValid) w hAway] at hMem
    obtain ⟨old, hOld, hEqual⟩ := Finset.mem_image.mp hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hOld
    refine ⟨⟨old, hSurvives⟩, ?_, Subtype.ext hEqual⟩
    refine Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr hIncident,
      injective_retainedRow base hValid ?_⟩
    rw [retainedRow_mk base hValid
      (⟨old, hSurvives⟩ : NonDanglingEdge base.gaugedData),
      show ResolutionAwayFromWall.retainedEdge (validCandidate base hValid)
        (base.gaugedData_valid hValid).1 ⟨old, hSurvives⟩ = edge from Subtype.ext hEqual]
    exact hEdge.2

end Incidence

/-! ## 4.  The vertex dictionary of the type change -/

section Wall

open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathCount
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk
open DraismaVargas.LocalCases.NonTrivalentValencyThreeTracks
  (facetRow facetEdge facetEdge_stablePath leftEnd rightEnd incident_facetEdge_leftEnd
    incident_facetEdge_rightEnd leftEnd_ne_rightEnd three_le_nonDanglingValency_end
    anchorVertex branchEquivAnchorComplement leftBranch rightBranch facetDartLeft
    facetDartRight liftEdge stablePath_liftEdge coverBranchEquiv coverBranchMap
    vert_base_eq vert_opBase_eq op_base_eq)

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)

variable {wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (base : SimpleBase (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)

/-- **The branch-vertex dictionary across the wall contraction *and* the
two-fold branch gauge.**  `NonTrivalentValencyThreeTracks.branchEquivAnchorComplement` in its
`hFibre`-free branch-pair form, composed with the gauge leg: away from the
anchor the branch vertices of the incoming cover other than the two ends of the
vanishing occurrence correspond to the branch vertices of the *gauged* wall
datum other than the gauged anchor. -/
def branchEquivGaugedAnchorComplement :
    {v : BranchVertex wd.cover // v.1 ≠ leftEnd m wd ∧ v.1 ≠ rightEnd m wd} ≃
      {w : BranchVertex base.gaugedData // w.1 ≠ gaugedAnchorVertex base} :=
  (branchEquivAnchorComplement m wd wallStar base.source).trans
    (gaugeBranchEquivAnchorComplement base hValid)

@[simp] theorem branchEquivGaugedAnchorComplement_apply
    (v : {v : BranchVertex wd.cover // v.1 ≠ leftEnd m wd ∧ v.1 ≠ rightEnd m wd}) :
    (branchEquivGaugedAnchorComplement m wd base hValid v).1.1 =
      gaugeVertexEquiv base
        (sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v.1.1) := rfl

/-- **The vertex dictionary of the valency-three Type I / Type II type
change.**  Away from the anchor it is the retained (or ordinary-block) vertex of
the gauged wall datum, read back across the two branch gauges, then to the
incoming cover by the branch dictionary of the wall contraction and finally
through the incoming tracking; `A_u` and `A_v` go to the two ends of the
vanishing occurrence. -/
def vertexEquiv : BranchVertex (validCandidate base hValid).datum ≃ V :=
  ((candBranchEquiv base hValid).symm.trans
    (Equiv.sumCongr (branchEquivGaugedAnchorComplement m wd base hValid).symm
      (Equiv.refl Bool))).trans
    ((coverBranchEquiv m wd wallStar).trans wd.tracks.iso.vtx)

@[simp] theorem vertexEquiv_inl
    (w : {w : BranchVertex base.gaugedData // w.1 ≠ gaugedAnchorVertex base}) :
    vertexEquiv m wd base hValid (candBranchMap base hValid (Sum.inl w)) =
      wd.tracks.iso.vtx ((branchEquivGaugedAnchorComplement m wd base hValid).symm w).1 := by
  have h : (candBranchEquiv base hValid).symm
      (candBranchMap base hValid (Sum.inl w)) = Sum.inl w :=
    (candBranchEquiv base hValid).symm_apply_apply (Sum.inl w)
  show wd.tracks.iso.vtx (coverBranchMap m wd wallStar
    (Equiv.sumCongr (branchEquivGaugedAnchorComplement m wd base hValid).symm (Equiv.refl Bool)
      ((candBranchEquiv base hValid).symm
        (candBranchMap base hValid (Sum.inl w))))) = _
  rw [h]
  rfl

@[simp] theorem vertexEquiv_anchor (side : Bool) :
    vertexEquiv m wd base hValid (candBranchMap base hValid (Sum.inr side)) =
      wd.tracks.iso.vtx
        (if side then rightBranch m wd wallStar else leftBranch m wd wallStar) := by
  have h : (candBranchEquiv base hValid).symm
      (candBranchMap base hValid (Sum.inr side)) = Sum.inr side :=
    (candBranchEquiv base hValid).symm_apply_apply (Sum.inr side)
  show wd.tracks.iso.vtx (coverBranchMap m wd wallStar
    (Equiv.sumCongr (branchEquivGaugedAnchorComplement m wd base hValid).symm (Equiv.refl Bool)
      ((candBranchEquiv base hValid).symm
        (candBranchMap base hValid (Sum.inr side))))) = _
  rw [h]
  rfl

/-- **`A_u` goes to `graph.vert m.base`.** -/
theorem vertexEquiv_anchor_false
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base) :
    vertexEquiv m wd base hValid (candBranchMap base hValid (Sum.inr false)) =
      graph.vert m.base := by
  rw [vertexEquiv_anchor m wd base hValid false, vert_base_eq m wd wallStar hBase]
  rfl

/-- **`A_v` goes to `graph.vert (graph.op m.base)`.** -/
theorem vertexEquiv_anchor_true
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base) :
    vertexEquiv m wd base hValid (candBranchMap base hValid (Sum.inr true)) =
      graph.vert (graph.op m.base) := by
  rw [vertexEquiv_anchor m wd base hValid true, vert_opBase_eq m wd wallStar hBase]
  rfl


/-! ## 5.  (H-I/II): the prescribed simple move -/

/-- `e_alpha` as a surviving occurrence of the incoming cover. -/
def alphaLift : NonDanglingEdge wd.cover :=
  liftEdge m wd ⟨base.alphaSurvivor.1, alphaSurvivor_survives base⟩

/-- `e_delta` as a surviving occurrence of the incoming cover. -/
def deltaLift : NonDanglingEdge wd.cover :=
  liftEdge m wd ⟨base.deltaSurvivor.1, deltaSurvivor_survives base⟩

/-- No lift of a wall-datum survivor is the vanishing occurrence: the vanishing
row is not an incoming row. -/
theorem facetEdge_ne_liftEdge
    (g : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    (facetEdge m wd).1 ≠ (liftEdge m wd g).1 := by
  intro hBad
  refine incomingRow_ne_facet wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m)
    (wd.hForest m) wd.coordinates (label m.base) wd.hZeroCoord wd.hPosCoord wd.hFacetZero
    (NonDanglingEdge.stablePath g) ?_
  rw [← stablePath_liftEdge m wd]
  show NonDanglingEdge.stablePath (liftEdge m wd g) = facetRow m wd
  rw [show liftEdge m wd g = facetEdge m wd from Subtype.ext hBad.symm]
  exact facetEdge_stablePath m wd

theorem facetEdge_ne_alphaLift : (facetEdge m wd).1 ≠ (alphaLift m wd base).1 :=
  facetEdge_ne_liftEdge m wd _

theorem facetEdge_ne_deltaLift : (facetEdge m wd).1 ≠ (deltaLift m wd base).1 :=
  facetEdge_ne_liftEdge m wd _

/-- **(H-I/II), the per-vertex match at the anchor.**  The two darts that the
Whitehead move `m` places together with `m.base` -- the moved star of
`graph.vert m.base` with `m.base` removed -- are the darts of the two *retained*
survivors that the Type I / Type II resolution pairs at `A_u`, namely `e_alpha`
and `e_delta`, in the orientation that puts `A_u` at `graph.vert m.base` (first
conjunct: `m.base` is the dart of the vanishing occurrence at the `A_u` end).

The survivor clause is at the level of stable **rows**,
`d.2.1.stablePath = ...`, not of occurrences: that is what the star count
consumes (`NonTrivalentValencyThreeSimpleStarCount.label_dart_lift`, through
`IncomingPairing.label_dart_of_row`), and it is the only form satisfiable at a
Type I/II incoming, where `e_delta` reaches `A_u` through a *pass-through*
occurrence over the contracted target edge.

The candidate's exact star at `A_u` is `{e_alpha, e_1, e'}`
(`NonTrivalentValencyThreeSimpleRows.nonDanglingIncident_hubLeft`); `e_1` is the
bridge, alone on the new row, and `e'` continues through the divalent `A'` onto
the retained row of `e_delta`
(`newSourceEdge_stablePath_eq_retained`), so in the *stable* graph the three
edges at `A_u` are `h_alpha`, `h_1` and `h_delta`.  One clause therefore covers
both Type I and Type II: they differ only in the order condition on the four
indices, not in which pair the resolution brings together.

The other orientation is normalised away by the caller with
`CubicDarts.MoveData.swap`, which leaves `graph.move m` unchanged. -/
def PrescribedSimpleMove : Prop :=
  wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base ∧
    ∃ first second : StableSourceDarts.Dart wd.cover,
      first.2.1.stablePath = (alphaLift m wd base).stablePath ∧
        second.2.1.stablePath = (deltaLift m wd base).stablePath ∧
        (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
          {wd.tracks.iso.dart first, wd.tracks.iso.dart second}

/-- **The occurrence-level clause implies (H-I/II).**  If the two darts the move
places with `m.base` *are* the occurrences of `e_alpha` and `e_delta` -- the
occurrence-level form of the condition -- then they carry their rows, so
(H-I/II) holds.  The converse fails at a Type I/II incoming, where `e_delta`
reaches `A_u` through a pass-through occurrence over the contracted target
edge. -/
theorem prescribedSimpleMove_of_occurrence
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base)
    (first second : StableSourceDarts.Dart wd.cover)
    (hFirst : first.2.1 = alphaLift m wd base)
    (hSecond : second.2.1 = deltaLift m wd base)
    (hStar : (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
      {wd.tracks.iso.dart first, wd.tracks.iso.dart second}) :
    PrescribedSimpleMove m wd base :=
  ⟨hBase, first, second, by rw [hFirst], by rw [hSecond], hStar⟩

/-- **(H-I/II) from the orientation clause and two moved darts carrying the rows
of `e_alpha` and `e_delta`.**  This is the shape the valency dispatcher
consumes: it obtains the two darts from
`IncomingPairing.exists_movedStar_darts` (which also says that one sits at each
end of the vanishing occurrence, so no separation hypothesis is needed here),
checks that their rows are `{h_alpha, h_delta}`, and applies this lemma.  For
the other order of the pair, apply it to `y`, `x` after `Finset.pair_comm`. -/
theorem prescribedSimpleMove_of_rows
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base)
    (x y : StableSourceDarts.Dart wd.cover)
    (hx : x.2.1.stablePath = (alphaLift m wd base).stablePath)
    (hy : y.2.1.stablePath = (deltaLift m wd base).stablePath)
    (hStar : (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
      {wd.tracks.iso.dart x, wd.tracks.iso.dart y}) :
    PrescribedSimpleMove m wd base :=
  ⟨hBase, x, y, hx, hy, hStar⟩

/-- **The geometric content of a type change at a valency-three wall, Types I
and II**: the two survivors the outgoing resolution pairs at `A_u` -- `e_alpha`
and `e_delta` -- lift to occurrences at the two **different** ends of the
vanishing occurrence.  Without it `A_u` sees exactly the star of `leftEnd` and no
Whitehead move takes place. -/
def SimpleSeparated : Prop :=
  Incident wd.cover (alphaLift m wd base).1 (leftEnd m wd) ∧
    Incident wd.cover (deltaLift m wd base).1 (rightEnd m wd)

/-- A third surviving occurrence at the `A_u` end, distinct from the vanishing
occurrence and from `e_alpha` there. -/
theorem exists_thirdEdge (hSep : SimpleSeparated m wd base) :
    ∃ e : NonDanglingEdge wd.cover, Incident wd.cover e.1 (leftEnd m wd) ∧
      e ≠ facetEdge m wd ∧ e ≠ alphaLift m wd base := by
  classical
  have hNd : nonDanglingValency wd.cover (leftEnd m wd) = 3 := by
    have h1 := three_le_nonDanglingValency_end m wd wallStar _ (incident_facetEdge_leftEnd m wd)
    have h2 : nonDanglingValency wd.cover (leftEnd m wd) ≤ 3 :=
      wd.fullDim.trivalent (leftEnd m wd)
    omega
  have hNe := facetEdge_ne_alphaLift m wd base
  set pair : Finset wd.cover.SourceEdge :=
    {(facetEdge m wd).1, (alphaLift m wd base).1} with hpair
  have hsub : pair ⊆ nonDanglingIncident wd.cover (leftEnd m wd) := by
    intro e he
    rw [hpair] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨(facetEdge m wd).2, incident_facetEdge_leftEnd m wd⟩
    · exact (mem_nonDanglingIncident _ _ _).mpr ⟨(alphaLift m wd base).2, hSep.1⟩
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

/-- The third occurrence at the `A_u` end. -/
def thirdEdge (hSep : SimpleSeparated m wd base) : NonDanglingEdge wd.cover :=
  Classical.choose (exists_thirdEdge m wd base hSep)

theorem thirdEdge_spec (hSep : SimpleSeparated m wd base) :
    Incident wd.cover (thirdEdge m wd base hSep).1 (leftEnd m wd) ∧
      thirdEdge m wd base hSep ≠ facetEdge m wd ∧
      thirdEdge m wd base hSep ≠ alphaLift m wd base :=
  Classical.choose_spec (exists_thirdEdge m wd base hSep)

/-- The dart of `e_alpha` at the `A_u` end. -/
def alphaDartLeft (hSep : SimpleSeparated m wd base) : StableSourceDarts.Dart wd.cover :=
  ⟨leftBranch m wd wallStar, ⟨alphaLift m wd base, hSep.1⟩⟩

/-- The dart of `e_delta` at the `A_v` end. -/
def deltaDartRight (hSep : SimpleSeparated m wd base) : StableSourceDarts.Dart wd.cover :=
  ⟨rightBranch m wd wallStar, ⟨deltaLift m wd base, hSep.2⟩⟩

/-- The remaining dart at the `A_u` end. -/
def thirdDart (hSep : SimpleSeparated m wd base) : StableSourceDarts.Dart wd.cover :=
  ⟨leftBranch m wd wallStar, ⟨thirdEdge m wd base hSep, (thirdEdge_spec m wd base hSep).1⟩⟩

/-- **The Whitehead move prescribed by `e_alpha` and `e_delta`.**  It contracts
the edge of `m.base` and exchanges `e_delta` at the `A_v` end with the remaining
dart at the `A_u` end. -/
def prescribedMove (hSep : SimpleSeparated m wd base)
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base) : graph.MoveData where
  base := m.base
  left := wd.tracks.iso.dart (thirdDart m wd base hSep)
  right := wd.tracks.iso.dart (deltaDartRight m wd base hSep)
  nonloop := m.nonloop
  left_vert := (wd.tracks.iso.vert_map (thirdDart m wd base hSep)).trans
    (vert_base_eq m wd wallStar hBase).symm
  left_ne := by
    intro hBad
    exact (thirdEdge_spec m wd base hSep).2.1
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1)
        (wd.tracks.iso.dart.injective (hBad.trans hBase.symm)))
  right_vert := (wd.tracks.iso.vert_map (deltaDartRight m wd base hSep)).trans
    (vert_opBase_eq m wd wallStar hBase).symm
  right_ne := by
    intro hBad
    exact (facetEdge_ne_deltaLift m wd base)
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1.1)
        (wd.tracks.iso.dart.injective
          (hBad.trans (op_base_eq m wd wallStar hBase)))).symm

/-- **Non-vacuity of (H-I/II), in relative form.**  At a wall of the outer walk
whose vanishing occurrence is oriented with its `A_u` end at `graph.vert m.base`
and whose two paired survivors `e_alpha`, `e_delta` sit at the two different
ends, the Whitehead move `prescribedMove` -- which contracts the *same* edge as
`m` -- satisfies (H-I/II).  As at Type III, an absolute
`exists m, PrescribedSimpleMove m wd base` does not typecheck: `wd : WallData
arrival` with `arrival : FacetArrival degree graph label (label m.base)` fixes
`m.base`, so the witness has to be produced with that same `base` field. -/
theorem prescribedSimpleMove_prescribedMove (hSep : SimpleSeparated m wd base)
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base) :
    PrescribedSimpleMove (prescribedMove m wd base hSep hBase) wd base := by
  classical
  set m' := prescribedMove m wd base hSep hBase with hm'
  set dLeft := alphaDartLeft m wd base hSep with hdLeft
  set dRight := deltaDartRight m wd base hSep with hdRight
  have hLeftNeRight : dLeft ≠ dRight := by
    intro hBad
    exact (leftEnd_ne_rightEnd m wd)
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.1.1) hBad)
  have hLeftNeThird : dLeft ≠ thirdDart m wd base hSep := by
    intro hBad
    exact (thirdEdge_spec m wd base hSep).2.2
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1) hBad).symm
  have hBaseNeLeft : m.base ≠ wd.tracks.iso.dart dLeft := by
    intro hBad
    exact (facetEdge_ne_alphaLift m wd base)
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1.1)
        (wd.tracks.iso.dart.injective (hBase.trans hBad)))
  have hBaseNeRight : m.base ≠ wd.tracks.iso.dart dRight := by
    intro hBad
    exact (facetEdge_ne_deltaLift m wd base)
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
        rw [m'.perm_of_ne h1 h2, wd.tracks.iso.vert_map dLeft, vert_base_eq m wd wallStar hBase]
        rfl
    · rw [(graph.move m').card_fibre (graph.vert m.base)]
      exact le_of_eq (Finset.card_eq_three.mpr ⟨_, _, _, hBaseNeRight, hBaseNeLeft,
        fun hBad ↦ hLeftNeRight (wd.tracks.iso.dart.injective hBad).symm, rfl⟩).symm
  show (Finset.univ.filter fun d ↦ (graph.move m').vert d = graph.vert m.base).erase m.base =
    {wd.tracks.iso.dart dLeft, wd.tracks.iso.dart dRight}
  rw [hStar, Finset.erase_insert (by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact not_or.mpr ⟨hBaseNeRight, hBaseNeLeft⟩), Finset.pair_comm]

/-! ### The two valency-agnostic pieces of the star count, re-exported

Both come from `NonTrivalentValencyThreeTracks`, proved there for the incoming
cover and the ambient tracked graph alone; they mention neither the anchor nor
the candidate, so they apply verbatim at Types I and II.  They are re-exported
(by application, not by copy) so that the five pieces of the star count named
here live in one namespace. -/

/-- **Away from the two ends of the vanishing occurrence the Whitehead move does
not change the star.**  `m.perm` is the transposition of `m.left` and `m.right`,
whose vertices are the two ends themselves. -/
theorem move_vert_eq_iff_of_ne {x : V} (hBase : x ≠ graph.vert m.base)
    (hOpBase : x ≠ graph.vert (graph.op m.base)) (d : D) :
    (graph.move m).vert d = x ↔ graph.vert d = x :=
  DraismaVargas.LocalCases.NonTrivalentValencyThreeTracks.move_vert_eq_iff_of_ne m hBase
    hOpBase d

/-- **The star of a branch vertex of the incoming cover, counted in the tracked
ambient graph**: `MovedIncidenceIso.DatumGraphIncidence.ofIso` at the incoming
tracking, with the row label read through the chart. -/
theorem card_star_eq_incidenceCount (u : BranchVertex wd.cover)
    (row : StablePath wd.cover) :
    incidenceCount wd.cover u.1 row =
      Nat.card {d : D // graph.vert d = wd.tracks.iso.vtx u ∧
        label d = wd.fullDim.labelling.row row} :=
  DraismaVargas.LocalCases.NonTrivalentValencyThreeTracks.card_star_eq_incidenceCount m wd u row


/-! ## 6.  The link, reduced to the star count -/

/-- **`OuterWalk.TypeChangeLink` at a three-valent wall, Types I and II, from
the star count alone.**  `NonTrivalentValencyThreeSimpleExit.typeChangeLink_of_receipts`
takes one receipt, `tracks`; `MovedIncidenceIso.tracksOfMovedIncidence` reduces
it to a branch-vertex bijection and a star count against the permuted vertex
map.  With `vertexEquiv` supplying the bijection,
exactly one geometric obligation is left: the star count `hIncidence`.  At a
branch vertex away from the anchor it is the composite of the transports (T1)
and (T2) of the module docstring -- whose gauge leg is
`incidenceCount_sheetRelabel_gauge` and whose off-wall (T1) is
`incidenceCount_retainedVertex_retainedRow` -- and at `A_u` / `A_v` it is what
(H-I/II) prescribes together with the exact anchor stars of
`NonTrivalentValencyThreeSimpleRows`. -/
def typeChangeLink_of_incidence
    (hIncidence : ∀ (v : BranchVertex (validCandidate base hValid).datum)
        (r : StablePath (validCandidate base hValid).datum),
      incidenceCount (validCandidate base hValid).datum v.1 r =
        Nat.card {d : D // graph.vert (m.perm d) = vertexEquiv m wd base hValid v ∧
          label d = (NonTrivalentValencyThreeSimpleExit.wallOutgoingFD m wd base
            hValid).labelling.row r}) :
    TypeChangeLink m wd :=
  NonTrivalentValencyThreeSimpleExit.typeChangeLink_of_receipts m wd base hValid
    (MovedIncidenceIso.tracksOfMovedIncidence _ _ graph m label
      (vertexEquiv m wd base hValid)
      (MovedIncidenceIso.label_op_of_tracks _ wd.fullDim wd.tracks) hIncidence)


end Wall

end

end DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleTracks
