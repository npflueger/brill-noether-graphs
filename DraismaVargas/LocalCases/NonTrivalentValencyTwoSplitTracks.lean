import DraismaVargas.LocalCases.IncomingPairing
import DraismaVargas.LocalCases.NonTrivalentValencyTwoTracksLeaf
import DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitExit

/-!
# The vertex dictionary of the valency-two Base II **split** type change, and (H-split)

Source: Vargas, Part II (arXiv:2609.09109), Section 5.1 (a combinatorial type
change is recorded as a Whitehead move on the *ambient* tracked graph; the
labelling convention (1)) and Section 5.4 (Case `{v2-nd4-t3}`, Configuration A,
base tree `T_2` = Base II, the **split** members of Subcases
`{v2-nd4-t3-k2=k3}` and `{v2-nd4-t3-k2<k3}` and their diagrams), together with
Draisma--Vargas Part I (arXiv:1909.12924), Case `{w2}` of Section 6, for the
base tree.

`NonTrivalentValencyTwoSplitExit.typeChangeLink_of_receipts_split` has `tracks`
as its only hypothesis; it lives over the gauged wall datum
(`NonTrivalentValencyTwoSplitGauge.splitGaugedData`), the split candidate of
`NonTrivalentValencyTwoSplitCandidate`, and the census and row dictionary of
`NonTrivalentValencyTwoSplitRows` and `NonTrivalentValencyTwoSplitRowEquiv`.
`MovedIncidenceIso.tracksOfMovedIncidence` reduces `tracks` to a branch-vertex
bijection `vertexEquiv : BranchVertex cand.datum ≃ V` and a star count
`hIncidence` against the *permuted* vertex map of `graph.move m`.  This module
delivers the bijection, the hypothesis (H-split) that pins the anchor half of
that star count -- **stated at row level from the start** -- and the off-wall
pieces of the count.

## Why (H-split) is stated at row level, and why it must be

A prescribed-move condition stated at the *occurrence* level
(`first.2.1 = selectedLift …`) is satisfiable only when the named survivor is
directly incident to an end of the vanishing row `h₁`.  At the split that is not merely a convenience: the second member of the
pair the split realizes at `S` is `e_δ`, which is a **pass-through** in the
*outgoing* cover as well -- its row reaches `S` through the piece and the
divalent `P_v` (`NonTrivalentValencyTwoSplitRows.pieceEdge_stablePath_eq_retained`).
So the anchor count has to read `e_δ` through the piece, exactly as the
occurrence `e'` of the valency-three Types I/II candidate is absorbed into
`e_δ`'s row (`NonTrivalentValencyThreeSimpleTracks`).  `PrescribedSplitMove` is
therefore stated at the level of stable rows from the start; no occurrence-level
variant is introduced.

## What is proved

### 0.  Which side of an ordinary wall block keeps its star

At a two-valent wall the outgoing base tree subdivides the wall vertex, so every
ordinary wall block `B` is split into two endpoint vertices, one per side of the
new target edge.  Off the anchor the split candidate installs the *neutral*
joined resolution of `NonTrivalentValencyTwoCandidate`, exactly as the merge
member does, so the bookkeeping of section 0 of `NonTrivalentValencyTwoTracks`
ports verbatim over `NonTrivalentValencyTwoSplitRows.ordinaryStar` and
`NonTrivalentValencyTwoSplitRowEquiv.ordSide`:
`ordinaryStar_congr`, `ordSide_congr`, `endpointVertex_eq_ordinary`,
`nonDanglingValency_endpointVertex_branchSide` (the side `!ordSide` keeps the
whole surviving valency) and `nonDanglingValency_endpointVertex_ordSide_le` (the
other side is at most divalent).  So a trivalent ordinary block contributes
exactly one branch vertex.

### 1.  The branch vertices of the split candidate

* `candVertex`, `nonDanglingValency_candVertex`: the outgoing vertex over a
  wall-datum vertex other than the anchor -- the `!ordSide` endpoint vertex over
  the wall, `ResolutionAwayFromWall.retainedVertex` away from it -- with
  unchanged surviving valency.
* `anchorBranchSheet`, `anchorBranchVertex`,
  `nonDanglingValency_anchorBranchVertex`,
  `nonDanglingIncident_anchorBranchVertex_false` / `..._true`: `S = e_α` (side
  `false`, over `u`) and `A_v = e_ε` (side `true`, over `v`), the two trivalent
  vertices above the anchor, with the exact stars computed there in
  `NonTrivalentValencyTwoSplitRows` --
  `{bridge, piece, e_α}` and `{bridge, pass-through, e_ε}`.
* `stablePath_pieceEdge_eq_retainedRow`, `stablePath_passEdge_eq_retainedRow`:
  the piece carries `e_δ`'s outgoing row and the pass-through carries `e_β`'s.
* `candBranchMap`, `candBranchEquiv`: **the branch vertices of the split
  candidate are the branch vertices of the wall datum other than the anchor,
  plus `S` and `A_v`.**  Surjectivity reads the four-vertex anchor census of
  `NonTrivalentValencyTwoSplitRows` as a classification: above `u` the anchor contributes `S` (`nd = 3`) and the
  pass-through `P_u = e_β` (`nd = 2`), above `v` it contributes `A_v` (`nd = 3`)
  and the pass-through `P_v = e_δ` (`nd = 2`), so the two divalent pass-through
  classes are excluded exactly as `NonTrivalentValencyThreeSimpleTracks`
  excludes the divalent `A'`.
* `incidenceCount_retainedVertex_retainedRow`: the off-wall half of the star
  count, transport (T1) away from the wall, with
  `NonTrivalentValencyTwoSplitRowDictionary.retainedRowFree_injective` in place
  of a row equivalence.

### 2.  The gauge leg

The split candidate lives over `NonTrivalentValencyTwoSplitGauge.splitGaugedData`,
the inclusion alignment gauge `e_δ ⊆ e_α`, so every dictionary crosses one sheet
relabelling: `gaugedAnchorVertex`, `gaugeVertexEquiv_anchor`, `gaugeBranchEquiv`,
`gaugeBranchEquivAnchorComplement`, `incidenceCount_gauge` (**the gauge leg of
the star-count transport (T2)**, one `incidenceCount_sheetRelabel` along
`NonTrivalentValencyTwoSplitRowDictionary.splitGaugeRowEquiv`, the row map the
matrix side already uses), and
`ungaugeSurvivor` / `ungaugeSurvivor_not_isDangling`.

### 3.  The vertex dictionary

`branchEquivGaugedAnchorComplement` is
`NonTrivalentValencyTwoTracksLeaf.branchEquivAnchorComplement` (the wall
contraction, over the abstract pair `AnchorEnds`) composed with the
gauge leg, and `vertexEquiv` is the composite
`BranchVertex cand.datum ≃ BranchVertex gauged-minus-A ⊕ Bool ≃
 BranchVertex M-minus-{p,q} ⊕ Bool ≃ BranchVertex M ≃ V`,
with `vertexEquiv_inl`, `vertexEquiv_anchor`, and under (H-split)'s orientation
`vertexEquiv_anchor_false` (`S ↦ graph.vert m.base`) and
`vertexEquiv_anchor_true` (`A_v ↦ graph.vert (graph.op m.base)`).
`ordinaryTrivalent_gauged_of_ordinaryTrivalent` records that the gauged form of
`OrdinaryTrivalent` is not an extra input.

### 4.  (H-split), at row level (module sections 4 and 7)

* `splitSurvivor`, `splitWallEdge`, `splitLift`,
  `splitLift_stablePath_ne_facetRow`: `e_α` and `e_δ`, the pair the split brings
  together at `S`, as surviving occurrences of the incoming cover -- read back
  across the gauge and then across the wall contraction; neither lies on the
  vanishing row.
* `PrescribedSplitMove m wd … p q`: the orientation clause, in the
  hypothesis-free `IncomingPairing.baseDart` / `opBaseDart` form so that it is
  the same clause in all three incoming sub-cases, together with the row-level
  survivor clause.
* `prescribedSplitMove_spec`: under it the two named darts still sit one at each
  anchor end and their labels are the chart rows of `e_α` and `e_δ` -- the two
  facts the count at `S` uses.
* `exists_movedStar_darts_at_ends`, `prescribedSplitMove_of_rows`: the move
  always names one dart at each anchor end, so the condition is a statement about
  rows only and the dispatcher discharges it by matching rows.
* `SplitSeparated`, `prescribedMove`, `prescribedSplitMove_prescribedMove`:
  **non-vacuity of (H-split), in relative form** (an absolute `∃ m, …` does not
  typecheck, because `wd : WallData arrival` fixes `m.base`).
* `orientation_of_hBase_two`, `orientation_of_hBase_leaf`: the orientation clause
  holds in **all three** incoming sub-cases, from the (H-II) orientation of
  `NonTrivalentValencyTwoTracks` and `NonTrivalentValencyTwoTracksLeaf`.

### 5.  The off-wall dart half

`card_star_move_eq_incidenceCount`: away from the two anchor ends the Whitehead
move does not change the star.  `incidenceCount_candVertex_away`: (T1) and (T2)
composed, so away from the wall the incoming wall datum's star is the
candidate's star at the retained copy, on the retained row.

### 6.  The link

* `tracksOfIncidence`: `Tracks out (graph.move m) label` for an **arbitrary**
  outgoing presentation `out` of the split candidate, from the star count alone
  (`hOp` is free from the incoming tracking).
* `typeChangeLink_of_incidence`, `exists_typeChangeLink_of_incidence_split`:
  **`OuterWalk.TypeChangeLink` at a valency-two Base II split wall from the star
  count alone**, through `NonTrivalentValencyTwoSplitExit.wallOutgoingFD` and
  `typeChangeLink_of_receipts_split`; the second discharges the incoming
  trichotomy internally by `NonTrivalentValencyTwoTracksLeaf.exists_anchorEnds`
  and hands back the
  branch-vertex bijection the caller must count against.

### 8.  The mirror member (module section 8)

`exists_typeChangeLink_of_incidence_splitMirror`: every declaration above is
stated over an *arbitrary* wall star, so the mirror member (a class over
`wallStar.edge 1` splits) is the same theorem at
`NonTrivalentValencyTwoSplitExit.relabelStar wallStar`, with only the incoming
classifier transported.

## Hypotheses left explicit here

1. `hIncidence`, hence `tracks`: the star count
   `incidenceCount cand.datum v r =
    Nat.card {d // graph.vert (m.perm d) = vertexEquiv v and label d = row r}`.
   It is proved in `NonTrivalentValencyTwoSplitStarCount`.  Away from the anchor
   it is the composite of
   * (T1) `incidenceCount gauged w r =
     incidenceCount cand.datum (candVertex w) (retainedRowFree r)`.  Away from
     the wall this is `incidenceCount_retainedVertex_retainedRow` above, and
     with (T2) it is `incidenceCount_candVertex_away`; at an ordinary wall block
     it comes from the ordinary-block census of `NonTrivalentValencyTwoSplitRows`
     (`nonDanglingIncident_endpointVertex_of_new_dangling` / `..._of_new_survives`,
     `stablePath_retainedEdge_eq_newEdgeAt`) together with the retained-row map.
   * (T2) the gauge leg `incidenceCount_gauge`, **proved here**, composed with
     `incidenceCount M_0 w r =
     incidenceCount M (branchEquivAnchorComplement.symm w) (incomingRow r)`.  The
     latter is `WallSplitIncidence.incidenceCount_sourceVertexMap` away from the
     merged target vertex; at an ordinary wall block it needs the unramified
     count of `WallSplitIncidenceOrdinary`, as for the other valency-two and
     valency-three types.
   * At the anchor the count is the one (H-split) prescribes together with the
     exact stars `nonDanglingIncident_anchorBranchVertex_false` / `..._true` and
     the dart side `card_star_move_eq_incidenceCount`; the two pass-through
     vertices cost nothing, being divalent and so not branch vertices, but they
     do mean `e_δ`'s row is read at `S` through the piece and `e_β`'s at `A_v`
     through the pass-through (`stablePath_pieceEdge_eq_retainedRow`,
     `stablePath_passEdge_eq_retainedRow`).
   The star count itself is not proved here: `NonTrivalentValencyTwoSplitStarCount`
   supplies `hIncidence` from the wall data and the incoming star alone.
2. `SplitSeparated`, and (H-split) itself.  (H-split) is the per-vertex match at
   the anchor; `SplitSeparated` is what makes the wall crossing an actual type
   change.  Neither is derived here; (H-split) has the relative witness
   `prescribedSplitMove_prescribedMove` and the orientation clause has the two
   producers of §4.  `NonTrivalentValencyTwoBaseOneLink.splitCrossLink`
   discharges (H-split) unconditionally.
3. `AnchorEnds m wd anchorBlk p q` -- the abstraction of
   `NonTrivalentValencyTwoTracksLeaf`, supplied
   unconditionally at every two-valent wall by
   `NonTrivalentValencyTwoTracksLeaf.exists_anchorEnds`, which
   `exists_typeChangeLink_of_incidence_split` calls internally.
4. `wallStar`, `anchorBlk`, `thickSheet`, `thinSheet`, `ra`, `hGauged`,
   `hOrdGauged`, `labelling₀`, `hRowVal`, `hMatrixWall` -- **exactly the binders
   of `NonTrivalentValencyTwoSplitExit.wallOutgoingFD` and
   `typeChangeLink_of_receipts_split`** -- plus the incoming `hOrd`, which the
   branch dictionary of `NonTrivalentValencyTwoTracksLeaf` needs and from which
   `hOrdGauged` follows (`ordinaryTrivalent_gauged_of_ordinaryTrivalent`).
   Configuration A, the four named survivors and the paper's strict index
   inequality `k_δ < k_α` stay the caller's dispatch data, as in
   `NonTrivalentValencyTwoSplitExit`.
5. No structure is introduced.  The two `Prop` definitions ship as follows:
   `PrescribedSplitMove` has the relative witness
   `prescribedSplitMove_prescribedMove` together with the orientation producers
   `orientation_of_hBase_two` / `orientation_of_hBase_leaf`; `SplitSeparated` is
   a named hypothesis of that witness, in the same style as
   `StablePathFacetContraction.NoContractedReturn`.

## Consumers

`MovedIncidenceIso.tracksOfMovedIncidence` -- hence the `tracks` field of
`NonTrivalentValencyTwoSplitExit.typeChangeLink_of_receipts_split` and
`OuterWalk.TypeChangeLink` at Part II Case `{v2-nd4}`, Configuration A, the two
Base II split outgoing types -- with the star count supplied by
`NonTrivalentValencyTwoSplitStarCount`; and the move-to-type dispatcher, through
`prescribedSplitMove_of_rows`, which `NonTrivalentValencyTwoBaseOneLink.link_all`
discharges with no hypothesis.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitTracks

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionCoarseFine
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.StablePathCount
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate.Prescribed
  (thickEdge thinEdge rightAssignment)
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitRows
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitRowEquiv (ordSide ordSide_eq_true
  ordSide_eq_false)
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRowEquiv (OrdinaryTrivalent
  sourceEndpoint_eq_of_rel)
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRows (survivor_not_isDangling)

noncomputable section

/-! ## 0.  Which side of an ordinary wall block keeps its star -/

section OrdinarySide

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall} (ra : SplitAnchor data star anchor)

local notation "cand" => (validCandidate ra.setup)

/-- Both `ordinaryStar` and `ordSide` only see the wall block of a sheet. -/
theorem ordinaryStar_congr {x y : Fin degree}
    (hRel : (data.vertexPartition wall).Rel x y) (side : Bool) :
    ordinaryStar data star anchor x side = ordinaryStar data star anchor y side := by
  classical
  ext old
  rw [mem_ordinaryStar, mem_ordinaryStar, sourceEndpoint_eq_of_rel hRel]

theorem ordSide_congr {x y : Fin degree} (hRel : (data.vertexPartition wall).Rel x y) :
    ordSide data star anchor x = ordSide data star anchor y := by
  classical
  by_cases h : (ordinaryStar data star anchor y true).card <
      (ordinaryStar data star anchor y false).card
  · rw [ordSide_eq_true h, ordSide_eq_true (by
      rw [ordinaryStar_congr hRel true, ordinaryStar_congr hRel false]; exact h)]
  · rw [ordSide_eq_false h, ordSide_eq_false (by
      rw [ordinaryStar_congr hRel true, ordinaryStar_congr hRel false]; exact h)]

/-- Over an ordinary wall block the two endpoint vertices of the split
candidate are compared through the *unchanged* wall partition. -/
theorem endpointVertex_eq_ordinary (side : Bool) {x y : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hRel : (data.vertexPartition wall).Rel x y) :
    endpointVertex ra side x = endpointVertex ra side y := by
  refine (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨rfl, ?_⟩
  refine Eq.trans ?_ (((cand).datum.vertexPartition
    (if side then freshVertex target else oldVertex target wall)).rel_repr_right y)
  exact (candidate_vertexPartition_rel_ordinary ra side hX).mpr hRel

/-- **The side `!ordSide` keeps the whole surviving star of a trivalent
ordinary block.** -/
theorem nonDanglingValency_endpointVertex_branchSide (hValid : data.Valid) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hLe : nonDanglingValency data (data.sourceEndpoint wall x) ≤ 3) :
    nonDanglingValency (cand).datum
        (endpointVertex ra (!ordSide data star anchor x) x) =
      nonDanglingValency data (data.sourceEndpoint wall x) := by
  classical
  have hSum := card_ordinaryStar_add (data := data) (star := star) (anchor := anchor) x
  by_cases hDang : IsDangling (cand).datum (newEdgeAt ra x)
  · have hSplit : (ordinaryStar data star anchor x false).card = 0 ∨
        (ordinaryStar data star anchor x true).card = 0 := by
      by_contra hBad
      obtain ⟨hF, hT⟩ := not_or.mp hBad
      exact ((newEdgeAt_survives_iff_ordinary ra hValid hX).mpr ⟨hF, hT⟩) hDang
    by_cases hLt : (ordinaryStar data star anchor x true).card <
        (ordinaryStar data star anchor x false).card
    · rw [show (!ordSide data star anchor x) = false by rw [ordSide_eq_true hLt]; rfl,
        nonDanglingValency_endpointVertex_of_new_dangling ra hValid false hX hDang]
      omega
    · rw [show (!ordSide data star anchor x) = true by rw [ordSide_eq_false hLt]; rfl,
        nonDanglingValency_endpointVertex_of_new_dangling ra hValid true hX hDang]
      omega
  · obtain ⟨hF, hT⟩ := (newEdgeAt_survives_iff_ordinary ra hValid hX).mp hDang
    by_cases hLt : (ordinaryStar data star anchor x true).card <
        (ordinaryStar data star anchor x false).card
    · rw [show (!ordSide data star anchor x) = false by rw [ordSide_eq_true hLt]; rfl,
        nonDanglingValency_endpointVertex_of_new_survives ra hValid false hX hDang]
      omega
    · rw [show (!ordSide data star anchor x) = true by rw [ordSide_eq_false hLt]; rfl,
        nonDanglingValency_endpointVertex_of_new_survives ra hValid true hX hDang]
      omega

/-- **The side `ordSide` of a trivalent ordinary block is at most divalent**, so
it is never a branch vertex of the split candidate. -/
theorem nonDanglingValency_endpointVertex_ordSide_le (hValid : data.Valid) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hLe : nonDanglingValency data (data.sourceEndpoint wall x) ≤ 3) :
    nonDanglingValency (cand).datum (endpointVertex ra (ordSide data star anchor x) x) ≤ 2 := by
  classical
  have hSum := card_ordinaryStar_add (data := data) (star := star) (anchor := anchor) x
  by_cases hDang : IsDangling (cand).datum (newEdgeAt ra x)
  · have hSplit : (ordinaryStar data star anchor x false).card = 0 ∨
        (ordinaryStar data star anchor x true).card = 0 := by
      by_contra hBad
      obtain ⟨hF, hT⟩ := not_or.mp hBad
      exact ((newEdgeAt_survives_iff_ordinary ra hValid hX).mpr ⟨hF, hT⟩) hDang
    by_cases hLt : (ordinaryStar data star anchor x true).card <
        (ordinaryStar data star anchor x false).card
    · rw [ordSide_eq_true hLt,
        nonDanglingValency_endpointVertex_of_new_dangling ra hValid true hX hDang]
      omega
    · rw [ordSide_eq_false hLt,
        nonDanglingValency_endpointVertex_of_new_dangling ra hValid false hX hDang]
      omega
  · obtain ⟨hF, hT⟩ := (newEdgeAt_survives_iff_ordinary ra hValid hX).mp hDang
    by_cases hLt : (ordinaryStar data star anchor x true).card <
        (ordinaryStar data star anchor x false).card
    · rw [ordSide_eq_true hLt,
        nonDanglingValency_endpointVertex_of_new_survives ra hValid true hX hDang]
      omega
    · rw [ordSide_eq_false hLt,
        nonDanglingValency_endpointVertex_of_new_survives ra hValid false hX hDang]
      omega

end OrdinarySide

/-! ## 1.  The branch vertices of the split candidate -/

section Candidate

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall} (ra : SplitAnchor data star anchor)

local notation "cand" => (validCandidate ra.setup)

/-- A wall vertex of the datum is the source endpoint of its own sheet. -/
theorem sourceEndpoint_self (w : data.SourceVertex) (hw : w.1.1 = wall) :
    data.sourceEndpoint wall w.1.2 = w :=
  (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hw.symm, rfl⟩

/-- A wall vertex other than the anchor is an ordinary block. -/
theorem not_rel_anchor_of_ne (w : data.SourceVertex) (hw : w.1.1 = wall)
    (hne : w ≠ WallBlock.sourceVertex data wall anchor) :
    ¬ (data.vertexPartition wall).Rel anchor.1 w.1.2 := by
  intro hBad
  exact hne ((sourceEndpoint_eq_of_rel hBad).trans (sourceEndpoint_self w hw)).symm

/-- The endpoint above an ordinary block is not the anchor. -/
theorem sourceEndpoint_ne_anchor {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) :
    data.sourceEndpoint wall x ≠ WallBlock.sourceVertex data wall anchor := by
  intro hBad
  exact hX (congrArg (fun z : data.SourceVertex ↦ z.1.2) hBad).symm

open scoped Classical in
/-- **The outgoing vertex over a wall-datum vertex other than the anchor.**  Over
the wall the split candidate splits each ordinary block in two; the vertex that
keeps the whole surviving star is the one on the side `!ordSide`.  Away from the
wall the vertex is simply retained. -/
def candVertex (w : data.SourceVertex) : (cand).datum.SourceVertex :=
  if w.1.1 = wall then endpointVertex ra (!ordSide data star anchor w.1.2) w.1.2
  else ResolutionAwayFromWall.retainedVertex (cand) w

theorem candVertex_wall (w : data.SourceVertex) (hw : w.1.1 = wall) :
    candVertex ra w = endpointVertex ra (!ordSide data star anchor w.1.2) w.1.2 := by
  unfold candVertex
  rw [if_pos hw]

theorem candVertex_away (w : data.SourceVertex) (hw : w.1.1 ≠ wall) :
    candVertex ra w = ResolutionAwayFromWall.retainedVertex (cand) w := by
  unfold candVertex
  rw [if_neg hw]

theorem endpointVertex_target (side : Bool) (y : Fin degree) :
    (endpointVertex ra side y).1.1 =
      (if side then freshVertex target else oldVertex target wall) :=
  ((GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mp rfl).1.symm

/-- Two vertices of the candidate on one side of the new target edge coincide
exactly when their sheets are related there. -/
theorem endpointVertex_rel {side : Bool} {y y' : Fin degree}
    (hEq : endpointVertex ra side y = endpointVertex ra side y') :
    ((cand).datum.vertexPartition
      (if side then freshVertex target else oldVertex target wall)).Rel y y' :=
  congrArg (fun z : (cand).datum.SourceVertex ↦ z.1.2) hEq

/-- Two endpoint vertices on different sides of the new target edge differ. -/
theorem endpointVertex_side_eq {side side' : Bool} {y y' : Fin degree}
    (hEq : endpointVertex ra side y = endpointVertex ra side' y') : side = side' := by
  have hTarget := congrArg (fun z : (cand).datum.SourceVertex ↦ z.1.1) hEq
  rw [endpointVertex_target ra side y, endpointVertex_target ra side' y'] at hTarget
  cases side <;> cases side' <;>
    first
      | rfl
      | exact absurd hTarget Sum.inl_ne_inr
      | exact absurd hTarget Sum.inr_ne_inl

theorem candVertex_wall_target (w : data.SourceVertex) (hw : w.1.1 = wall) :
    (candVertex ra w).1.1 =
      (if (!ordSide data star anchor w.1.2) then freshVertex target
        else oldVertex target wall) := by
  rw [candVertex_wall ra w hw]
  exact endpointVertex_target ra _ _

theorem candVertex_away_target (w : data.SourceVertex) (hw : w.1.1 ≠ wall) :
    (candVertex ra w).1.1 = oldVertex target w.1.1 := by
  rw [candVertex_away ra w hw]
  exact ((GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mp rfl).1.symm

/-- **The surviving valency is unchanged.**  Over the wall this is the
`!ordSide` census of §0; away from it, the retained vertex. -/
theorem nonDanglingValency_candVertex (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor) (w : data.SourceVertex)
    (hne : w ≠ WallBlock.sourceVertex data wall anchor) :
    nonDanglingValency (cand).datum (candVertex ra w) = nonDanglingValency data w := by
  classical
  by_cases hw : w.1.1 = wall
  · have hRel := not_rel_anchor_of_ne w hw hne
    rw [candVertex_wall ra w hw,
      nonDanglingValency_endpointVertex_branchSide ra hValid hRel (hOrd _ hRel),
      sourceEndpoint_self w hw]
  · rw [candVertex_away ra w hw,
      ResolutionAwayFromWall.nonDanglingValency_retainedVertex (cand) hValid
        (candidate_sourceGenus ra) w hw]

/-- The outgoing vertex over the source endpoint of an ordinary sheet. -/
theorem candVertex_sourceEndpoint {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) :
    candVertex ra (data.sourceEndpoint wall x) =
      endpointVertex ra (!ordSide data star anchor x) x := by
  have hRepr := (data.vertexPartition wall).rel_repr_left x
  rw [candVertex_wall ra _ rfl]
  rw [show (data.sourceEndpoint wall x).1.2 = (data.vertexPartition wall).repr x from rfl,
    ordSide_congr hRepr, endpointVertex_eq_ordinary ra _ (not_rel_repr hX) hRepr]

/-! ### The two branch vertices above the anchor -/

/-- The sheet naming `S = e_alpha` (side `false`, over `u`) and
`A_v = e_epsilon` (side `true`, over `v`). -/
def anchorBranchSheet (side : Bool) : Fin degree :=
  if side then occurrenceSheet ra.epsilonEdge else occurrenceSheet ra.alphaEdge

theorem anchorBranchSheet_wall (side : Bool) :
    (data.vertexPartition wall).Rel anchor.1 (anchorBranchSheet ra side) := by
  cases side
  · exact occurrenceSheet_wall_rel ra.alphaEdge
  · exact occurrenceSheet_wall_rel ra.epsilonEdge

/-- **`S` (side `false`) and `A_v` (side `true`)**, the two trivalent vertices
above the anchor block; the pass-through classes `P_u` and `P_v` are divalent
and do not appear. -/
def anchorBranchVertex (side : Bool) : (cand).datum.SourceVertex :=
  endpointVertex ra side (anchorBranchSheet ra side)

theorem anchorBranchVertex_false :
    anchorBranchVertex ra false = endpointVertex ra false (occurrenceSheet ra.alphaEdge) := rfl

theorem anchorBranchVertex_true :
    anchorBranchVertex ra true = endpointVertex ra true (occurrenceSheet ra.epsilonEdge) := rfl

theorem anchorBranchVertex_target (side : Bool) :
    (anchorBranchVertex ra side).1.1 =
      (if side then freshVertex target else oldVertex target wall) :=
  endpointVertex_target ra side (anchorBranchSheet ra side)

theorem nonDanglingValency_anchorBranchVertex (hValid : data.Valid) (side : Bool) :
    nonDanglingValency (cand).datum (anchorBranchVertex ra side) = 3 := by
  cases side
  · exact nonDanglingValency_endpointVertex_alpha ra hValid
  · exact nonDanglingValency_endpointVertex_epsilon ra hValid

theorem anchorBranchVertex_ne :
    anchorBranchVertex ra false ≠ anchorBranchVertex ra true := by
  intro hBad
  exact Bool.false_ne_true (endpointVertex_side_eq ra hBad)

/-- **The exact surviving star of `S`**: the bridge, the piece and `e_alpha`'s
own retained occurrence. -/
theorem nonDanglingIncident_anchorBranchVertex_false (hValid : data.Valid) :
    nonDanglingIncident (cand).datum (anchorBranchVertex ra false) =
      {bridgeEdge ra, pieceEdge ra, (cand).oldSourceEdge ra.alphaEdge.1} :=
  nonDanglingIncident_endpointVertex_alpha ra hValid

/-- **The exact surviving star of `A_v`**: the bridge, the pass-through and
`e_epsilon`'s own retained occurrence. -/
theorem nonDanglingIncident_anchorBranchVertex_true (hValid : data.Valid) :
    nonDanglingIncident (cand).datum (anchorBranchVertex ra true) =
      {bridgeEdge ra, passEdge ra, (cand).oldSourceEdge ra.epsilonEdge.1} :=
  nonDanglingIncident_endpointVertex_epsilon ra hValid

/-- **The piece carries `e_delta`'s outgoing row.**  `e_delta` is a
pass-through in the *outgoing* cover as well: its retained occurrence meets the
divalent `P_v`, and the piece continues that row to the trivalent `S`.  So the
anchor half of the star count must read `e_delta` at `S` through the piece --
the split's analogue of the occurrence `e'` of
`NonTrivalentValencyThreeSimpleTracks`. -/
theorem stablePath_pieceEdge_eq_retainedRow (hValid : data.Valid) :
    NonDanglingEdge.stablePath
        (⟨pieceEdge ra, pieceEdge_survives ra hValid⟩ : NonDanglingEdge (cand).datum) =
      retainedRowFree ra hValid
        (NonDanglingEdge.stablePath
          (⟨ra.deltaEdge.1, survivor_not_isDangling ra.delta_mem⟩ : NonDanglingEdge data)) :=
  pieceEdge_stablePath_eq_retained ra hValid

/-- **The pass-through carries `e_beta`'s outgoing row**, the mirror statement at
the second divalent vertex `P_u`. -/
theorem stablePath_passEdge_eq_retainedRow (hValid : data.Valid) :
    NonDanglingEdge.stablePath
        (⟨passEdge ra, passEdge_survives ra hValid⟩ : NonDanglingEdge (cand).datum) =
      retainedRowFree ra hValid
        (NonDanglingEdge.stablePath
          (⟨ra.betaEdge.1, survivor_not_isDangling ra.beta_mem⟩ : NonDanglingEdge data)) :=
  passEdge_stablePath_eq_retained ra hValid

/-! ### The branch-vertex dictionary -/

/-- **The branch vertices of the split candidate.**  Every branch vertex is
either the outgoing copy of a branch vertex of the wall datum other than the
anchor, or one of `S`, `A_v`. -/
def candBranchMap (hValid : data.Valid) (hOrd : OrdinaryTrivalent data wall anchor) :
    ({w : BranchVertex data // w.1 ≠ WallBlock.sourceVertex data wall anchor} ⊕ Bool) →
      BranchVertex (cand).datum
  | Sum.inl w => ⟨candVertex ra w.1.1, by
      rw [nonDanglingValency_candVertex ra hValid hOrd w.1.1 w.2]
      exact w.1.2⟩
  | Sum.inr side => ⟨anchorBranchVertex ra side,
      (nonDanglingValency_anchorBranchVertex ra hValid side).ge⟩

theorem candBranchMap_injective (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor) :
    Function.Injective (candBranchMap ra hValid hOrd) := by
  classical
  have hWallTarget : ∀ w : {w : BranchVertex data //
      w.1 ≠ WallBlock.sourceVertex data wall anchor},
      w.1.1.1.1 = wall → ¬ (data.vertexPartition wall).Rel anchor.1 w.1.1.1.2 :=
    fun w hw ↦ not_rel_anchor_of_ne w.1.1 hw w.2
  rintro (w | side) (w' | side') hEq <;>
    have hv : (candBranchMap ra hValid hOrd _).1 = (candBranchMap ra hValid hOrd _).1 :=
      congrArg Subtype.val hEq
  · by_cases hw : w.1.1.1.1 = wall <;> by_cases hw' : w'.1.1.1.1 = wall
    · have hv2 : endpointVertex ra (!ordSide data star anchor w.1.1.1.2) w.1.1.1.2 =
          endpointVertex ra (!ordSide data star anchor w'.1.1.1.2) w'.1.1.1.2 := by
        rw [← candVertex_wall ra w.1.1 hw, ← candVertex_wall ra w'.1.1 hw']
        exact hv
      rw [endpointVertex_side_eq ra hv2] at hv2
      have hRel := (candidate_vertexPartition_rel_ordinary ra _ (hWallTarget w hw)).mp
        (endpointVertex_rel ra hv2)
      have hSheet : w.1.1.1.2 = w'.1.1.1.2 := by
        have h1 : (data.vertexPartition w.1.1.1.1).repr w.1.1.1.2 = w.1.1.1.2 := w.1.1.2
        have h2 : (data.vertexPartition w'.1.1.1.1).repr w'.1.1.1.2 = w'.1.1.1.2 := w'.1.1.2
        rw [hw] at h1
        rw [hw'] at h2
        rw [← h1, ← h2]
        exact hRel
      exact congrArg Sum.inl (Subtype.ext (Subtype.ext (Subtype.ext
        (Prod.ext (hw.trans hw'.symm) hSheet))))
    · exfalso
      have hTarget := (candVertex_wall_target ra w.1.1 hw).symm.trans
        ((congrArg (fun z : (cand).datum.SourceVertex ↦ z.1.1) hv).trans
          (candVertex_away_target ra w'.1.1 hw'))
      cases hSide : (!ordSide data star anchor w.1.1.1.2) with
      | false => rw [hSide] at hTarget; exact hw' (Sum.inl_injective hTarget).symm
      | true => rw [hSide] at hTarget; exact Sum.inr_ne_inl hTarget
    · exfalso
      have hTarget := (candVertex_away_target ra w.1.1 hw).symm.trans
        ((congrArg (fun z : (cand).datum.SourceVertex ↦ z.1.1) hv).trans
          (candVertex_wall_target ra w'.1.1 hw'))
      cases hSide : (!ordSide data star anchor w'.1.1.1.2) with
      | false => rw [hSide] at hTarget; exact hw (Sum.inl_injective hTarget)
      | true => rw [hSide] at hTarget; exact Sum.inl_ne_inr hTarget
    · have hRet : ResolutionAwayFromWall.retainedVertex (cand) w.1.1 =
          ResolutionAwayFromWall.retainedVertex (cand) w'.1.1 := by
        rw [← candVertex_away ra w.1.1 hw, ← candVertex_away ra w'.1.1 hw']
        exact hv
      exact congrArg Sum.inl (Subtype.ext (Subtype.ext
        (ResolutionStableIncidence.retainedVertex_injective_away (cand) w.1.1 w'.1.1
          hw hw' hRet)))
  · exfalso
    have hv' : candVertex ra w.1.1 = anchorBranchVertex ra side' := hv
    by_cases hw : w.1.1.1.1 = wall
    · have hv2 : endpointVertex ra (!ordSide data star anchor w.1.1.1.2) w.1.1.1.2 =
          endpointVertex ra side' (anchorBranchSheet ra side') := by
        rw [← candVertex_wall ra w.1.1 hw]
        exact hv'
      rw [endpointVertex_side_eq ra hv2] at hv2
      have hRel := (candidate_vertexPartition_rel_ordinary ra _ (hWallTarget w hw)).mp
        (endpointVertex_rel ra hv2)
      exact hWallTarget w hw ((anchorBranchSheet_wall ra side').trans hRel.symm)
    · have hTarget := congrArg (fun z : (cand).datum.SourceVertex ↦ z.1.1) hv'
      rw [candVertex_away_target ra w.1.1 hw, anchorBranchVertex_target ra side'] at hTarget
      cases side' with
      | false => exact hw (Sum.inl_injective hTarget)
      | true => exact Sum.inl_ne_inr hTarget
  · exfalso
    have hv' : anchorBranchVertex ra side = candVertex ra w'.1.1 := hv
    by_cases hw : w'.1.1.1.1 = wall
    · have hv2 : endpointVertex ra (!ordSide data star anchor w'.1.1.1.2) w'.1.1.1.2 =
          endpointVertex ra side (anchorBranchSheet ra side) := by
        rw [← candVertex_wall ra w'.1.1 hw]
        exact hv'.symm
      rw [endpointVertex_side_eq ra hv2] at hv2
      have hRel := (candidate_vertexPartition_rel_ordinary ra _ (hWallTarget w' hw)).mp
        (endpointVertex_rel ra hv2)
      exact hWallTarget w' hw ((anchorBranchSheet_wall ra side).trans hRel.symm)
    · have hTarget := congrArg (fun z : (cand).datum.SourceVertex ↦ z.1.1) hv'
      rw [candVertex_away_target ra w'.1.1 hw, anchorBranchVertex_target ra side] at hTarget
      cases side with
      | false => exact hw (Sum.inl_injective hTarget).symm
      | true => exact Sum.inr_ne_inl hTarget
  · cases side <;> cases side' <;>
      first
        | rfl
        | exact absurd hv (anchorBranchVertex_ne ra)
        | exact absurd hv.symm (anchorBranchVertex_ne ra)

theorem candBranchMap_surjective (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor) :
    Function.Surjective (candBranchMap ra hValid hOrd) := by
  classical
  intro v
  have hOrdinary : ∀ side : Bool, endpointVertex ra side v.1.1.2 = v.1 →
      ¬ (data.vertexPartition wall).Rel anchor.1 v.1.1.2 →
      ∃ w, candBranchMap ra hValid hOrd w = v := by
    intro side hV hRel
    have hNdV := v.2
    have hSide : (!ordSide data star anchor v.1.1.2) = side := by
      have hOther := nonDanglingValency_endpointVertex_ordSide_le ra hValid hRel (hOrd _ hRel)
      cases hCase : ordSide data star anchor v.1.1.2 <;> cases side <;>
        rw [hCase] at hOther <;>
          first
            | rfl
            | (exfalso; rw [hV] at hOther; omega)
    have hNd := nonDanglingValency_endpointVertex_branchSide ra hValid hRel (hOrd _ hRel)
    rw [hSide, hV] at hNd
    exact ⟨Sum.inl ⟨⟨data.sourceEndpoint wall v.1.1.2, by rw [← hNd]; exact v.2⟩,
      sourceEndpoint_ne_anchor hRel⟩, Subtype.ext (by
        show candVertex ra (data.sourceEndpoint wall v.1.1.2) = v.1
        rw [candVertex_sourceEndpoint ra hRel, hSide]
        exact hV)⟩
  rcases hcase : (v.1.1.1 : TargetExpansion.Vertex target) with place | u
  · by_cases hIsWall : place = wall
    · have hV : endpointVertex ra false v.1.1.2 = v.1 :=
        NonTrivalentValencyTwoSplitExit.eq_endpointVertex ra false v.1
          (by rw [hcase, hIsWall]; rfl)
      by_cases hAnchor : (data.vertexPartition wall).Rel anchor.1 v.1.1.2
      · rcases ra.thick_cover hAnchor with hT | hT
        · refine ⟨Sum.inr false, Subtype.ext ?_⟩
          show anchorBranchVertex ra false = v.1
          rw [anchorBranchVertex_false ra, ← endpointVertex_eq ra false hAnchor hT.symm]
          exact hV
        · exfalso
          have hNd := nonDanglingValency_endpointVertex_beta ra hValid
          rw [← endpointVertex_eq ra false hAnchor hT.symm, hV] at hNd
          have := v.2
          omega
      · exact hOrdinary false hV hAnchor
    · obtain ⟨old, hOld, hRet⟩ :=
        ResolutionAwayFromWall.exists_retainedVertex_of_target (cand) v.1 place hIsWall hcase
      have hAway : old.1.1 ≠ wall := by rw [hOld]; exact hIsWall
      have hNd : nonDanglingValency data old = nonDanglingValency (cand).datum v.1 := by
        rw [← hRet, ResolutionAwayFromWall.nonDanglingValency_retainedVertex (cand) hValid
          (candidate_sourceGenus ra) old hAway]
      have hne : old ≠ WallBlock.sourceVertex data wall anchor := by
        intro hBad
        exact hAway (by rw [hBad]; rfl)
      refine ⟨Sum.inl ⟨⟨old, by rw [hNd]; exact v.2⟩, hne⟩, Subtype.ext ?_⟩
      show candVertex ra old = v.1
      rw [candVertex_away ra old hAway]
      exact hRet
  · have hV : endpointVertex ra true v.1.1.2 = v.1 :=
      NonTrivalentValencyTwoSplitExit.eq_endpointVertex ra true v.1
        (by rw [hcase]; cases u; rfl)
    by_cases hAnchor : (data.vertexPartition wall).Rel anchor.1 v.1.1.2
    · rcases ra.setup.cover v.1.1.2 hAnchor with hT | hT
      · exfalso
        have hNd := nonDanglingValency_endpointVertex_delta ra hValid
        rw [← endpointVertex_eq ra true hAnchor hT.symm, hV] at hNd
        have := v.2
        omega
      · refine ⟨Sum.inr true, Subtype.ext ?_⟩
        show anchorBranchVertex ra true = v.1
        rw [anchorBranchVertex_true ra,
          ← endpointVertex_eq ra true hAnchor (hT.symm.trans ra.thin_rel_alpha_epsilon)]
        exact hV
    · exact hOrdinary true hV hAnchor

/-- **The branch-vertex dictionary of the split candidate.** -/
def candBranchEquiv (hValid : data.Valid) (hOrd : OrdinaryTrivalent data wall anchor) :
    ({w : BranchVertex data // w.1 ≠ WallBlock.sourceVertex data wall anchor} ⊕ Bool) ≃
      BranchVertex (cand).datum :=
  Equiv.ofBijective (candBranchMap ra hValid hOrd)
    ⟨candBranchMap_injective ra hValid hOrd, candBranchMap_surjective ra hValid hOrd⟩

/-! ### The off-wall half of the star count -/

/-- **Away from the wall the split candidate does not change the star.** -/
theorem incidenceCount_retainedVertex_retainedRow (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor)
    (w : data.SourceVertex) (hAway : w.1.1 ≠ wall) (row : StablePath data) :
    incidenceCount data w row =
      incidenceCount (cand).datum (ResolutionAwayFromWall.retainedVertex (cand) w)
        (retainedRowFree ra hValid row) := by
  classical
  unfold incidenceCount
  apply Finset.card_bij (fun edge _ ↦ ResolutionAwayFromWall.retainedEdge (cand) hValid.1 edge)
  · intro edge hEdge
    simp only [Finset.mem_filter, mem_incidentEdges] at hEdge ⊢
    refine ⟨(ResolutionAwayFromWall.incident_oldSourceEdge_iff (cand) w hAway edge.1).mpr
      hEdge.1, ?_⟩
    rw [← retainedRowFree_mk ra hValid edge, hEdge.2]
  · intro first _ second _ hEq
    exact ResolutionAwayFromWall.retainedEdge_injective (cand) hValid.1 hEq
  · intro edge hEdge
    simp only [Finset.mem_filter, mem_incidentEdges] at hEdge
    have hMem : edge.1 ∈ nonDanglingIncident (cand).datum
        (ResolutionAwayFromWall.retainedVertex (cand) w) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hEdge.1⟩
    rw [ResolutionAwayFromWall.nonDanglingIncident_retainedVertex (cand) hValid
      (candidate_sourceGenus ra) w hAway] at hMem
    obtain ⟨old, hOld, hEqual⟩ := Finset.mem_image.mp hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hOld
    refine ⟨⟨old, hSurvives⟩, ?_, Subtype.ext hEqual⟩
    refine Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr hIncident,
      NonTrivalentValencyTwoSplitRowDictionary.retainedRowFree_injective ra hValid hOrd ?_⟩
    rw [retainedRowFree_mk ra hValid (⟨old, hSurvives⟩ : NonDanglingEdge data),
      show ResolutionAwayFromWall.retainedEdge (cand) hValid.1 ⟨old, hSurvives⟩ = edge from
        Subtype.ext hEqual]
    exact hEdge.2

end Candidate

/-! ## 2.  The gauge leg -/

section Gauge

open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitGauge
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitExit (splitGaugeVertexEquiv
  nonDanglingValency_splitGauge)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  (base : GluingDatum target degree) (star : TwoStar target wall)
  (anchor : WallBlock base wall) (thickSheet thinSheet : Fin degree)
  (hConn : base.Connected)

/-- The anchor of the gauged wall datum. -/
def gaugedAnchorVertex :
    (splitGaugedData base star anchor thickSheet thinSheet).SourceVertex :=
  WallBlock.sourceVertex (splitGaugedData base star anchor thickSheet thinSheet) wall
    (splitGaugedAnchor base star anchor thickSheet thinSheet)

/-- **The gauge carries the anchor to the gauged anchor.** -/
theorem gaugeVertexEquiv_anchor :
    splitGaugeVertexEquiv base star anchor thickSheet thinSheet
        (WallBlock.sourceVertex base wall anchor) =
      gaugedAnchorVertex base star anchor thickSheet thinSheet :=
  splitGauged_sourceVertex_eq base star anchor thickSheet thinSheet

/-- **The branch vertices across the gauge.** -/
def gaugeBranchEquiv :
    BranchVertex base ≃ BranchVertex (splitGaugedData base star anchor thickSheet thinSheet) :=
  (splitGaugeVertexEquiv base star anchor thickSheet thinSheet).subtypeEquiv fun v ↦ by
    rw [nonDanglingValency_splitGauge base star anchor thickSheet thinSheet hConn v]

@[simp] theorem gaugeBranchEquiv_val (v : BranchVertex base) :
    (gaugeBranchEquiv base star anchor thickSheet thinSheet hConn v).1 =
      splitGaugeVertexEquiv base star anchor thickSheet thinSheet v.1 := rfl

/-- **The branch vertices away from the anchor, across the gauge.** -/
def gaugeBranchEquivAnchorComplement :
    {w : BranchVertex base // w.1 ≠ WallBlock.sourceVertex base wall anchor} ≃
      {w : BranchVertex (splitGaugedData base star anchor thickSheet thinSheet) //
        w.1 ≠ gaugedAnchorVertex base star anchor thickSheet thinSheet} :=
  (gaugeBranchEquiv base star anchor thickSheet thinSheet hConn).subtypeEquiv fun w ↦ by
    show w.1 ≠ WallBlock.sourceVertex base wall anchor ↔
      splitGaugeVertexEquiv base star anchor thickSheet thinSheet w.1 ≠
        gaugedAnchorVertex base star anchor thickSheet thinSheet
    constructor
    · intro hw hBad
      exact hw ((splitGaugeVertexEquiv base star anchor thickSheet thinSheet).injective
        (hBad.trans (gaugeVertexEquiv_anchor base star anchor thickSheet thinSheet).symm))
    · intro hw hBad
      exact hw (by rw [hBad, gaugeVertexEquiv_anchor base star anchor thickSheet thinSheet])

@[simp] theorem gaugeBranchEquivAnchorComplement_apply
    (w : {w : BranchVertex base // w.1 ≠ WallBlock.sourceVertex base wall anchor}) :
    (gaugeBranchEquivAnchorComplement base star anchor thickSheet thinSheet hConn w).1.1 =
      splitGaugeVertexEquiv base star anchor thickSheet thinSheet w.1.1 := rfl

/-- **The gauge leg of the star-count transport (T2).**  The inclusion alignment
gauge is a sheet relabelling, so it carries every row-filtered star to the
corresponding one; the row map is
`NonTrivalentValencyTwoSplitRowDictionary.splitGaugeRowEquiv`, the one the matrix
side already uses. -/
theorem incidenceCount_gauge (v : base.SourceVertex) (r : StablePath base) :
    incidenceCount base v r =
      incidenceCount (splitGaugedData base star anchor thickSheet thinSheet)
        (splitGaugeVertexEquiv base star anchor thickSheet thinSheet v)
        (NonTrivalentValencyTwoSplitRowDictionary.splitGaugeRowEquiv base star anchor
          thickSheet thinSheet hConn r) :=
  StableGraphIncidence.incidenceCount_sheetRelabel
    (splitRelabeling base star anchor thickSheet thinSheet) hConn v r

/-- A survivor at the gauged anchor, read back to the datum the gauge acts on. -/
def ungaugeSurvivor
    (e : IncidentSourceEdge (splitGaugedData base star anchor thickSheet thinSheet)
      (WallBlock.sourceVertex (splitGaugedData base star anchor thickSheet thinSheet) wall
        (splitGaugedAnchor base star anchor thickSheet thinSheet))) :
    IncidentSourceEdge base (WallBlock.sourceVertex base wall anchor) :=
  (splitSurvivorEquiv base star anchor thickSheet thinSheet).symm e

include hConn in
/-- The gauge is a sheet relabelling, so it carries survivors to survivors. -/
theorem ungaugeSurvivor_not_isDangling
    (e : IncidentSourceEdge (splitGaugedData base star anchor thickSheet thinSheet)
      (WallBlock.sourceVertex (splitGaugedData base star anchor thickSheet thinSheet) wall
        (splitGaugedAnchor base star anchor thickSheet thinSheet)))
    (hSurv : ¬ IsDangling (splitGaugedData base star anchor thickSheet thinSheet) e.1) :
    ¬ IsDangling base (ungaugeSurvivor base star anchor thickSheet thinSheet e).1 := by
  intro hBad
  refine hSurv ?_
  have h := (splitGauged_isDangling_iff base star anchor thickSheet thinSheet hConn
    (ungaugeSurvivor base star anchor thickSheet thinSheet e)).mpr hBad
  rwa [show splitSurvivorEquiv base star anchor thickSheet thinSheet
    (ungaugeSurvivor base star anchor thickSheet thinSheet e) = e from
    Equiv.apply_symm_apply _ _] at h

end Gauge

/-! ## 3.  The vertex dictionary at a wall of the outer walk -/

section Wall

open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitGauge
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitExit (splitGaugeVertexEquiv
  ordinaryTrivalent_splitGauged wallOutgoingFD typeChangeLink_of_receipts_split)
open DraismaVargas.LocalCases.NonTrivalentValencyTwoTracksLeaf (AnchorEnds coverBranchEquiv
  coverBranchMap leftBranch rightBranch branchEquivAnchorComplement)

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
  {p q : wd.cover.SourceVertex}

include m hOrd in
/-- The gauged form of `OrdinaryTrivalent` is not an extra input: it is the
transport of the incoming one across the inclusion alignment gauge
(`NonTrivalentValencyTwoSplitExit`). -/
theorem ordinaryTrivalent_gauged_of_ordinaryTrivalent :
    OrdinaryTrivalent (splitGaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
      anchorBlk thickSheet thinSheet) ⟨wd.a, wd.hab⟩
      (splitGaugedAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        thickSheet thinSheet) :=
  ordinaryTrivalent_splitGauged (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
    anchorBlk thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 hOrd

/-- **The branch-vertex dictionary across the wall contraction *and* the
inclusion alignment gauge**:
`NonTrivalentValencyTwoTracksLeaf.branchEquivAnchorComplement` composed with the
gauge leg. -/
def branchEquivGaugedAnchorComplement (hEnds : AnchorEnds m wd anchorBlk p q) :
    {v : BranchVertex wd.cover // v.1 ≠ p ∧ v.1 ≠ q} ≃
      {w : BranchVertex (splitGaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          wallStar anchorBlk thickSheet thinSheet) //
        w.1 ≠ gaugedAnchorVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
          anchorBlk thickSheet thinSheet} :=
  (branchEquivAnchorComplement m wd hOrd hEnds).trans
    (gaugeBranchEquivAnchorComplement (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
      anchorBlk thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1)

/-- **The vertex dictionary of the valency-two Base II split type change.**  Away
from the anchor it is the outgoing vertex of the gauged wall datum, read back
across the gauge, then to the incoming cover by the branch dictionary of the wall
contraction, and finally through the incoming tracking; `S` and `A_v` go to the
two anchor ends of the vanishing row. -/
def vertexEquiv (hEnds : AnchorEnds m wd anchorBlk p q) :
    BranchVertex (validCandidate ra.setup).datum ≃ V :=
  ((candBranchEquiv ra hGauged hOrdGauged).symm.trans
    (Equiv.sumCongr
      (branchEquivGaugedAnchorComplement m wd thickSheet thinSheet hOrd hEnds).symm
      (Equiv.refl Bool))).trans
    ((coverBranchEquiv m wd hEnds).trans wd.tracks.iso.vtx)

@[simp] theorem vertexEquiv_inl (hEnds : AnchorEnds m wd anchorBlk p q)
    (w : {w : BranchVertex (splitGaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        wallStar anchorBlk thickSheet thinSheet) //
      w.1 ≠ gaugedAnchorVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
        anchorBlk thickSheet thinSheet}) :
    vertexEquiv m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd hEnds
        (candBranchMap ra hGauged hOrdGauged (Sum.inl w)) =
      wd.tracks.iso.vtx
        ((branchEquivGaugedAnchorComplement m wd thickSheet thinSheet hOrd hEnds).symm w).1 := by
  have h : (candBranchEquiv ra hGauged hOrdGauged).symm
      (candBranchMap ra hGauged hOrdGauged (Sum.inl w)) = Sum.inl w :=
    (candBranchEquiv ra hGauged hOrdGauged).symm_apply_apply (Sum.inl w)
  show wd.tracks.iso.vtx (coverBranchMap m wd hEnds
    (Equiv.sumCongr
      (branchEquivGaugedAnchorComplement m wd thickSheet thinSheet hOrd hEnds).symm
      (Equiv.refl Bool)
      ((candBranchEquiv ra hGauged hOrdGauged).symm
        (candBranchMap ra hGauged hOrdGauged (Sum.inl w))))) = _
  rw [h]
  rfl

@[simp] theorem vertexEquiv_anchor (hEnds : AnchorEnds m wd anchorBlk p q) (side : Bool) :
    vertexEquiv m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd hEnds
        (candBranchMap ra hGauged hOrdGauged (Sum.inr side)) =
      wd.tracks.iso.vtx (if side then rightBranch m wd hEnds else leftBranch m wd hEnds) := by
  have h : (candBranchEquiv ra hGauged hOrdGauged).symm
      (candBranchMap ra hGauged hOrdGauged (Sum.inr side)) = Sum.inr side :=
    (candBranchEquiv ra hGauged hOrdGauged).symm_apply_apply (Sum.inr side)
  show wd.tracks.iso.vtx (coverBranchMap m wd hEnds
    (Equiv.sumCongr
      (branchEquivGaugedAnchorComplement m wd thickSheet thinSheet hOrd hEnds).symm
      (Equiv.refl Bool)
      ((candBranchEquiv ra hGauged hOrdGauged).symm
        (candBranchMap ra hGauged hOrdGauged (Sum.inr side))))) = _
  rw [h]
  rfl


/-! ## 4.  (H-split), stated at row level -/

/-- The two survivors the split brings together at `S`: `e_alpha` (`which =
false`) and `e_delta` (`which = true`).  `e_alpha` is the class that splits above
`u`, `e_delta` the piece; together they are the paper's pairing `{h_alpha,
h_delta}` at `S`, and `{h_beta, h_epsilon}` at `A_v` is the complementary pair. -/
def splitSurvivor (which : Bool) :
    IncidentSourceEdge
      (splitGaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        thickSheet thinSheet)
      (WallBlock.sourceVertex
        (splitGaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
          thickSheet thinSheet) ⟨wd.a, wd.hab⟩
        (splitGaugedAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
          thickSheet thinSheet)) :=
  if which then ra.deltaEdge else ra.alphaEdge

theorem splitSurvivor_not_isDangling (which : Bool) :
    ¬ IsDangling (splitGaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
      anchorBlk thickSheet thinSheet) (splitSurvivor m wd thickSheet thinSheet ra which).1 := by
  cases which
  · exact survivor_not_isDangling ra.alpha_mem
  · exact survivor_not_isDangling ra.delta_mem

/-- **One member of the pair the split realizes at `S`, as a surviving
occurrence of the wall datum**, read back across the inclusion alignment
gauge. -/
def splitWallEdge (which : Bool) :
    NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne) :=
  ⟨(ungaugeSurvivor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      thickSheet thinSheet (splitSurvivor m wd thickSheet thinSheet ra which)).1,
    ungaugeSurvivor_not_isDangling (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
      anchorBlk thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1
      (splitSurvivor m wd thickSheet thinSheet ra which)
      (splitSurvivor_not_isDangling m wd thickSheet thinSheet ra which)⟩

/-- The same, read as a surviving occurrence of the incoming cover. -/
def splitLift (which : Bool) : NonDanglingEdge wd.cover :=
  NonTrivalentValencyTwoTracks.liftEdge m wd
    (splitWallEdge m wd thickSheet thinSheet ra which)

theorem splitLift_stablePath (which : Bool) :
    (splitLift m wd thickSheet thinSheet ra which).stablePath =
      incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m)
        (splitWallEdge m wd thickSheet thinSheet ra which).stablePath := rfl

/-- **Neither member of the pair lies on the vanishing row.** -/
theorem splitLift_stablePath_ne_facetRow (which : Bool) :
    (splitLift m wd thickSheet thinSheet ra which).stablePath ≠
      NonTrivalentValencyTwoTracks.facetRow m wd := by
  rw [splitLift_stablePath m wd thickSheet thinSheet ra which]
  exact incomingRow_ne_facet wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m)
    (wd.hForest m) wd.coordinates (label m.base) wd.hZeroCoord wd.hPosCoord wd.hFacetZero _

/-- **(H-split), the per-vertex match at the anchor of a valency-two Base II
split wall, stated at row level.**  The two darts the Whitehead move `m` places
together with `m.base` -- the moved star of `graph.vert m.base` with `m.base`
removed -- carry the **stable rows** of `e_alpha` and `e_delta`, the two
survivors the split brings together at `S`, in the orientation that puts the `S`
end of the vanishing row at `graph.vert m.base`.

The first conjunct is the orientation: the end of the vanishing row at
`graph.vert m.base` is the anchor end `p`, and the other end is `q`.  It is
stated with the hypothesis-free `IncomingPairing.baseDart` / `opBaseDart`, so it
is literally the same clause in all three incoming sub-cases (`2 + 2`, `1 + 3`,
`3 + 1`); the other orientation is normalised away by the caller with
`CubicDartGraph.MoveData.swap`, which leaves `graph.move m` unchanged.

The survivor clause is at the level of **rows**, never of occurrences.  At the
split that is forced twice over: `e_delta` reaches its end of the vanishing row
through a pass-through occurrence in the *incoming* cover whenever the incoming
configuration is itself a split, and -- unlike at every other family -- it is
a pass-through in the *outgoing* cover as well, its row reaching the trivalent
`S` only through the piece (`stablePath_pieceEdge_eq_retainedRow`).  The
row-level clause is what the star count consumes
(`IncomingPairing.label_dart_of_row`) and what the dispatcher can always
discharge (`IncomingPairing.exists_movedStar_darts`). -/
def PrescribedSplitMove (p q : wd.cover.SourceVertex) : Prop :=
  ((IncomingPairing.baseDart m wd).1.1 = p ∧ (IncomingPairing.opBaseDart m wd).1.1 = q) ∧
    ∃ first second : StableSourceDarts.Dart wd.cover,
      first.2.1.stablePath = (splitLift m wd thickSheet thinSheet ra false).stablePath ∧
        second.2.1.stablePath = (splitLift m wd thickSheet thinSheet ra true).stablePath ∧
          (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
            {wd.tracks.iso.dart first, wd.tracks.iso.dart second}

/-- **Under (H-split) the two named darts sit one at each anchor end, and their
labels are the chart rows of `e_alpha` and `e_delta`** -- the two facts the star
count at `S` uses. -/
theorem prescribedSplitMove_spec (p q : wd.cover.SourceVertex)
    (hPres : PrescribedSplitMove m wd thickSheet thinSheet ra p q) :
    ∃ first second : StableSourceDarts.Dart wd.cover,
      ((first.1.1 = p ∧ second.1.1 = q) ∨ (first.1.1 = q ∧ second.1.1 = p)) ∧
      label (wd.tracks.iso.dart first) = wd.fullDim.labelling.row
          (splitLift m wd thickSheet thinSheet ra false).stablePath ∧
      label (wd.tracks.iso.dart second) = wd.fullDim.labelling.row
          (splitLift m wd thickSheet thinSheet ra true).stablePath ∧
      (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
        {wd.tracks.iso.dart first, wd.tracks.iso.dart second} := by
  obtain ⟨⟨hLeft, hRight⟩, first, second, hFirst, hSecond, hStar⟩ := hPres
  refine ⟨first, second, ?_, IncomingPairing.label_dart_of_row m wd first _ hFirst,
    IncomingPairing.label_dart_of_row m wd second _ hSecond, hStar⟩
  rcases IncomingPairing.vertex_of_movedStar_eq_pair m wd first second hStar with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by rw [h1, hLeft], by rw [h2, hRight]⟩
  · exact Or.inr ⟨by rw [h1, hRight], by rw [h2, hLeft]⟩

/-- **Under (H-split)'s orientation `S` sits at `graph.vert m.base`.** -/
theorem vtx_leftBranch (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p) :
    wd.tracks.iso.vtx (leftBranch m wd hEnds) = graph.vert m.base := by
  have h : (IncomingPairing.baseDart m wd).1 = leftBranch m wd hEnds := Subtype.ext hLeft
  rw [← h]
  exact IncomingPairing.vtx_baseDart m wd

/-- **Under (H-split)'s orientation `A_v` sits at `graph.vert (graph.op m.base)`.** -/
theorem vtx_rightBranch (hEnds : AnchorEnds m wd anchorBlk p q)
    (hRight : (IncomingPairing.opBaseDart m wd).1.1 = q) :
    wd.tracks.iso.vtx (rightBranch m wd hEnds) = graph.vert (graph.op m.base) := by
  have h : (IncomingPairing.opBaseDart m wd).1 = rightBranch m wd hEnds := Subtype.ext hRight
  rw [← h]
  exact IncomingPairing.vtx_opBaseDart m wd

/-- **`S` goes to `graph.vert m.base`.** -/
theorem vertexEquiv_anchor_false (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p) :
    vertexEquiv m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd hEnds
        (candBranchMap ra hGauged hOrdGauged (Sum.inr false)) = graph.vert m.base := by
  rw [vertexEquiv_anchor m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd hEnds false]
  exact vtx_leftBranch m wd hEnds hLeft

/-- **`A_v` goes to `graph.vert (graph.op m.base)`.** -/
theorem vertexEquiv_anchor_true (hEnds : AnchorEnds m wd anchorBlk p q)
    (hRight : (IncomingPairing.opBaseDart m wd).1.1 = q) :
    vertexEquiv m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd hEnds
        (candBranchMap ra hGauged hOrdGauged (Sum.inr true)) =
      graph.vert (graph.op m.base) := by
  rw [vertexEquiv_anchor m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd hEnds true]
  exact vtx_rightBranch m wd hEnds hRight

/-! ## 5.  The off-wall dart half -/

/-- **Away from the two anchor ends the Whitehead move does not change the
star.**  The two valency-agnostic pieces of `NonTrivalentValencyTwoTracks`,
combined under (H-split)'s orientation clause. -/
theorem card_star_move_eq_incidenceCount (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hRight : (IncomingPairing.opBaseDart m wd).1.1 = q)
    (u : BranchVertex wd.cover) (hu : u.1 ≠ p) (hu' : u.1 ≠ q) (row : StablePath wd.cover) :
    incidenceCount wd.cover u.1 row =
      Nat.card {d : D // graph.vert (m.perm d) = wd.tracks.iso.vtx u ∧
        label d = wd.fullDim.labelling.row row} := by
  have hNeBase : wd.tracks.iso.vtx u ≠ graph.vert m.base := by
    rw [← vtx_leftBranch m wd hEnds hLeft]
    intro hBad
    exact hu (congrArg Subtype.val (wd.tracks.iso.vtx.injective hBad))
  have hNeOp : wd.tracks.iso.vtx u ≠ graph.vert (graph.op m.base) := by
    rw [← vtx_rightBranch m wd hEnds hRight]
    intro hBad
    exact hu' (congrArg Subtype.val (wd.tracks.iso.vtx.injective hBad))
  refine (NonTrivalentValencyTwoTracks.card_star_eq_incidenceCount m wd u row).trans
    (Nat.card_congr (Equiv.subtypeEquivRight fun d ↦ ?_))
  constructor
  · rintro ⟨hv, hr⟩
    exact ⟨(NonTrivalentValencyTwoTracks.move_vert_eq_iff_of_ne m hNeBase hNeOp d).mpr hv, hr⟩
  · rintro ⟨hv, hr⟩
    exact ⟨(NonTrivalentValencyTwoTracks.move_vert_eq_iff_of_ne m hNeBase hNeOp d).mp hv, hr⟩

include hOrdGauged in
/-- **The off-wall half of the star count, as one transport.**  Away from the
wall the gauge leg (T2) and the retained-vertex transport (T1) compose: the
incoming wall datum's star at a vertex over a target place other than the wall
is the split candidate's star at the retained copy, on the retained row.  The
rest of the star count -- the same composite *at an ordinary wall block*, and
the anchor match (H-split) prescribes -- is in
`NonTrivalentValencyTwoSplitStarCount`. -/
theorem incidenceCount_candVertex_away
    (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hAway : w.1.1 ≠ (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b))
    (r : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (contractDatum wd.cover wd.hc wd.hab wd.hOne) w r =
      incidenceCount (validCandidate ra.setup).datum
        (candVertex ra (splitGaugeVertexEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          wallStar anchorBlk thickSheet thinSheet w))
        (retainedRowFree ra hGauged
          (NonTrivalentValencyTwoSplitRowDictionary.splitGaugeRowEquiv
            (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet
            thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 r)) := by
  have hAway' : (splitGaugeVertexEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      wallStar anchorBlk thickSheet thinSheet w).1.1 ≠
      (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) := hAway
  rw [incidenceCount_gauge (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 w r,
    incidenceCount_retainedVertex_retainedRow ra hGauged hOrdGauged _ hAway' _,
    candVertex_away ra _ hAway']

/-! ## 6.  The link, reduced to the star count -/

section Link

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

/-- **`Tracks` of the moved graph from the star count alone**, against an
arbitrary outgoing presentation `out` of the split candidate.  `hOp` is free
from the incoming tracking through `MovedIncidenceIso.label_op_of_tracks`; the
branch-vertex bijection is `vertexEquiv`. -/
def tracksOfIncidence
    (out : FullDimensionalSourcePresentation (validCandidate ra.setup).datum coordinate)
    (hEnds : AnchorEnds m wd anchorBlk p q)
    (hIncidence : ∀ (v : BranchVertex (validCandidate ra.setup).datum)
        (r : StablePath (validCandidate ra.setup).datum),
      incidenceCount (validCandidate ra.setup).datum v.1 r =
        Nat.card {d : D // graph.vert (m.perm d) =
            vertexEquiv m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd hEnds v ∧
          label d = out.labelling.row r}) :
    Tracks out (graph.move m) label :=
  MovedIncidenceIso.tracksOfMovedIncidence _ _ graph m label
    (vertexEquiv m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd hEnds)
    (MovedIncidenceIso.label_op_of_tracks _ wd.fullDim wd.tracks) hIncidence

/-- **`OuterWalk.TypeChangeLink` at a valency-two Base II split wall from the
star count alone.**  `NonTrivalentValencyTwoSplitExit.typeChangeLink_of_receipts_split`
has one receipt left, `tracks`; `MovedIncidenceIso.tracksOfMovedIncidence`
reduces it to a branch-vertex bijection and a star count against the *permuted*
vertex map.  With `vertexEquiv` supplying the bijection, exactly one geometric
obligation is left, `hIncidence`. -/
def typeChangeLink_of_incidence (hEnds : AnchorEnds m wd anchorBlk p q)
    (hIncidence : ∀ (v : BranchVertex (validCandidate ra.setup).datum)
        (r : StablePath (validCandidate ra.setup).datum),
      incidenceCount (validCandidate ra.setup).datum v.1 r =
        Nat.card {d : D // graph.vert (m.perm d) =
            vertexEquiv m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd hEnds v ∧
          label d = (wallOutgoingFD m wd wallStar anchorBlk thickSheet thinSheet labelling₀
            ra hGauged hOrdGauged hRowVal hMatrixWall).labelling.row r}) :
    TypeChangeLink m wd :=
  typeChangeLink_of_receipts_split m wd wallStar anchorBlk thickSheet thinSheet labelling₀ ra
    hGauged hOrdGauged hRowVal hMatrixWall
    (tracksOfIncidence m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd _ hEnds hIncidence)

include hOrd in
/-- **`OuterWalk.TypeChangeLink` at a valency-two Base II split wall, from one
star count.**  The incoming `2 + 2` / `1 + 3` / `3 + 1` trichotomy is discharged
internally by `NonTrivalentValencyTwoTracksLeaf.exists_anchorEnds`; what the
caller supplies is the star count against the branch-vertex bijection this
theorem hands back, and against the outgoing split presentation
`NonTrivalentValencyTwoSplitExit.wallOutgoingFD`. -/
theorem exists_typeChangeLink_of_incidence_split
    (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk) :
    ∃ ve : BranchVertex (validCandidate ra.setup).datum ≃ V,
      (∀ (v : BranchVertex (validCandidate ra.setup).datum)
          (r : StablePath (validCandidate ra.setup).datum),
        incidenceCount (validCandidate ra.setup).datum v.1 r =
          Nat.card {d : D // graph.vert (m.perm d) = ve v ∧
            label d = (wallOutgoingFD m wd wallStar anchorBlk thickSheet thinSheet labelling₀
              ra hGauged hOrdGauged hRowVal hMatrixWall).labelling.row r}) →
        Nonempty (TypeChangeLink m wd) := by
  obtain ⟨p, q, hEnds⟩ := NonTrivalentValencyTwoTracksLeaf.exists_anchorEnds m wd src hOrd
  exact ⟨vertexEquiv m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd hEnds, fun hInc ↦
    ⟨typeChangeLink_of_incidence m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd
      labelling₀ hRowVal hMatrixWall hEnds hInc⟩⟩

end Link

/-! ## 7.  Non-vacuity: the orientation clause, and (H-split) in relative form -/

section NonVacuity

/-- The dart of the vanishing row at `graph.vert m.base` carries the vanishing
row. -/
theorem stablePath_baseDart :
    (IncomingPairing.baseDart m wd).2.1.stablePath =
      NonTrivalentValencyTwoTracks.facetRow m wd :=
  (Equiv.eq_symm_apply _).mpr (IncomingPairing.row_baseDart m wd)

/-- The dart of the vanishing row at `graph.vert (graph.op m.base)` carries the
vanishing row. -/
theorem stablePath_opBaseDart :
    (IncomingPairing.opBaseDart m wd).2.1.stablePath =
      NonTrivalentValencyTwoTracks.facetRow m wd := by
  have h := IncomingPairing.row_opBaseDart m wd
  rw [MovedIncidenceIso.label_op_of_tracks _ wd.fullDim wd.tracks m.base] at h
  exact (Equiv.eq_symm_apply _).mpr h

theorem baseDart_edge_ne_splitLift (which : Bool) :
    (IncomingPairing.baseDart m wd).2.1 ≠ splitLift m wd thickSheet thinSheet ra which := by
  intro hBad
  refine splitLift_stablePath_ne_facetRow m wd thickSheet thinSheet ra which ?_
  rw [← hBad]
  exact stablePath_baseDart m wd

theorem opBaseDart_edge_ne_splitLift (which : Bool) :
    (IncomingPairing.opBaseDart m wd).2.1 ≠ splitLift m wd thickSheet thinSheet ra which := by
  intro hBad
  refine splitLift_stablePath_ne_facetRow m wd thickSheet thinSheet ra which ?_
  rw [← hBad]
  exact stablePath_opBaseDart m wd

/-- **The geometric content of a type change at a split wall**: the two survivors
the split brings together at `S` lift to occurrences at the two **different**
anchor ends of the vanishing row.  Without it the `S` end sees exactly the star
it already had and no Whitehead move takes place.  It is a named hypothesis, in
the style of `StablePathFacetContraction.NoContractedReturn`. -/
def SplitSeparated (p q : wd.cover.SourceVertex) : Prop :=
  Incident wd.cover (splitLift m wd thickSheet thinSheet ra false).1 p ∧
    Incident wd.cover (splitLift m wd thickSheet thinSheet ra true).1 q

/-- A third surviving occurrence at the `S` end, distinct from the vanishing
row's occurrence there and from `e_alpha`'s lift. -/
theorem exists_thirdEdge (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hSep : SplitSeparated m wd thickSheet thinSheet ra p q) :
    ∃ e : NonDanglingEdge wd.cover, Incident wd.cover e.1 p ∧
      e ≠ (IncomingPairing.baseDart m wd).2.1 ∧
      e ≠ splitLift m wd thickSheet thinSheet ra false := by
  classical
  have hNd : nonDanglingValency wd.cover p = 3 := by
    have h1 := hEnds.2.1
    have h2 : nonDanglingValency wd.cover p ≤ 3 := wd.fullDim.trivalent p
    omega
  have hIncBase : Incident wd.cover (IncomingPairing.baseDart m wd).2.1.1 p := by
    rw [← hLeft]
    exact (IncomingPairing.baseDart m wd).2.2
  have hNe : (IncomingPairing.baseDart m wd).2.1.1 ≠
      (splitLift m wd thickSheet thinSheet ra false).1 := by
    intro hBad
    exact baseDart_edge_ne_splitLift m wd thickSheet thinSheet ra false (Subtype.ext hBad)
  set pair : Finset wd.cover.SourceEdge :=
    {(IncomingPairing.baseDart m wd).2.1.1,
      (splitLift m wd thickSheet thinSheet ra false).1} with hpair
  have hsub : pair ⊆ nonDanglingIncident wd.cover p := by
    intro e he
    rw [hpair] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨(IncomingPairing.baseDart m wd).2.1.2, hIncBase⟩
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨(splitLift m wd thickSheet thinSheet ra false).2, hSep.1⟩
  have hcard : (nonDanglingIncident wd.cover p \ pair).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, card_nonDanglingIncident, hNd, hpair,
      Finset.card_pair hNe]
  obtain ⟨e, he⟩ := Finset.card_pos.mp
    (by omega : 0 < (nonDanglingIncident wd.cover p \ pair).card)
  rw [Finset.mem_sdiff, hpair] at he
  obtain ⟨hMem, hNotMem⟩ := he
  obtain ⟨hSurv, hInc⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hNotMem
  exact ⟨⟨e, hSurv⟩, hInc, fun h ↦ hNotMem (Or.inl (congrArg Subtype.val h)),
    fun h ↦ hNotMem (Or.inr (congrArg Subtype.val h))⟩

/-- The third occurrence at the `S` end. -/
def thirdEdge (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hSep : SplitSeparated m wd thickSheet thinSheet ra p q) : NonDanglingEdge wd.cover :=
  Classical.choose (exists_thirdEdge m wd thickSheet thinSheet ra hEnds hLeft hSep)

theorem thirdEdge_spec (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hSep : SplitSeparated m wd thickSheet thinSheet ra p q) :
    Incident wd.cover (thirdEdge m wd thickSheet thinSheet ra hEnds hLeft hSep).1 p ∧
      thirdEdge m wd thickSheet thinSheet ra hEnds hLeft hSep ≠
        (IncomingPairing.baseDart m wd).2.1 ∧
      thirdEdge m wd thickSheet thinSheet ra hEnds hLeft hSep ≠
        splitLift m wd thickSheet thinSheet ra false :=
  Classical.choose_spec (exists_thirdEdge m wd thickSheet thinSheet ra hEnds hLeft hSep)

/-- The dart of `e_alpha`'s lift at the `S` end. -/
def selectedDartLeft (hEnds : AnchorEnds m wd anchorBlk p q)
    (hSep : SplitSeparated m wd thickSheet thinSheet ra p q) :
    StableSourceDarts.Dart wd.cover :=
  ⟨leftBranch m wd hEnds, ⟨splitLift m wd thickSheet thinSheet ra false, hSep.1⟩⟩

/-- The dart of `e_delta`'s lift at the `A_v` end. -/
def selectedDartRight (hEnds : AnchorEnds m wd anchorBlk p q)
    (hSep : SplitSeparated m wd thickSheet thinSheet ra p q) :
    StableSourceDarts.Dart wd.cover :=
  ⟨rightBranch m wd hEnds, ⟨splitLift m wd thickSheet thinSheet ra true, hSep.2⟩⟩

/-- The remaining dart at the `S` end. -/
def thirdDart (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hSep : SplitSeparated m wd thickSheet thinSheet ra p q) :
    StableSourceDarts.Dart wd.cover :=
  ⟨leftBranch m wd hEnds, ⟨thirdEdge m wd thickSheet thinSheet ra hEnds hLeft hSep,
    (thirdEdge_spec m wd thickSheet thinSheet ra hEnds hLeft hSep).1⟩⟩

/-- **The Whitehead move prescribed by the split's pair at `S`.**  It contracts
the *same* edge as `m` and exchanges `e_delta`'s lift at the `A_v` end with the
remaining dart at the `S` end. -/
def prescribedMove (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hRight : (IncomingPairing.opBaseDart m wd).1.1 = q)
    (hSep : SplitSeparated m wd thickSheet thinSheet ra p q) : graph.MoveData where
  base := m.base
  left := wd.tracks.iso.dart (thirdDart m wd thickSheet thinSheet ra hEnds hLeft hSep)
  right := wd.tracks.iso.dart (selectedDartRight m wd thickSheet thinSheet ra hEnds hSep)
  nonloop := m.nonloop
  left_vert :=
    (wd.tracks.iso.vert_map (thirdDart m wd thickSheet thinSheet ra hEnds hLeft hSep)).trans
      (vtx_leftBranch m wd hEnds hLeft)
  left_ne := by
    intro hBad
    exact (thirdEdge_spec m wd thickSheet thinSheet ra hEnds hLeft hSep).2.1
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1)
        (wd.tracks.iso.dart.injective
          (hBad.trans (IncomingPairing.dart_baseDart m wd).symm)))
  right_vert :=
    (wd.tracks.iso.vert_map
      (selectedDartRight m wd thickSheet thinSheet ra hEnds hSep)).trans
      (vtx_rightBranch m wd hEnds hRight)
  right_ne := by
    intro hBad
    exact (opBaseDart_edge_ne_splitLift m wd thickSheet thinSheet ra true)
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1)
        (wd.tracks.iso.dart.injective
          (hBad.trans (IncomingPairing.dart_opBaseDart m wd).symm))).symm

/-- **Non-vacuity of (H-split), in relative form.**  At a wall whose vanishing
row is oriented with its `S` end at `graph.vert m.base` and whose two paired
survivors sit at the two different anchor ends, the Whitehead move
`prescribedMove` -- which contracts the *same* edge as `m` -- satisfies
(H-split).  An absolute `∃ m, PrescribedSplitMove m wd …` does not typecheck:
`wd : WallData arrival` with
`arrival : FacetArrival deg graph label (label m.base)` fixes `m.base`, so the
witness has to be produced with that same `base` field. -/
theorem prescribedSplitMove_prescribedMove (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hRight : (IncomingPairing.opBaseDart m wd).1.1 = q)
    (hSep : SplitSeparated m wd thickSheet thinSheet ra p q) :
    PrescribedSplitMove
      (prescribedMove m wd thickSheet thinSheet ra hEnds hLeft hRight hSep) wd
      thickSheet thinSheet ra p q := by
  classical
  set m' := prescribedMove m wd thickSheet thinSheet ra hEnds hLeft hRight hSep with hm'
  set dLeft := selectedDartLeft m wd thickSheet thinSheet ra hEnds hSep with hdLeft
  set dRight := selectedDartRight m wd thickSheet thinSheet ra hEnds hSep with hdRight
  have hLeftNeRight : dLeft ≠ dRight := by
    intro hBad
    exact hEnds.1 (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.1.1) hBad)
  have hLeftNeThird :
      dLeft ≠ thirdDart m wd thickSheet thinSheet ra hEnds hLeft hSep := by
    intro hBad
    exact (thirdEdge_spec m wd thickSheet thinSheet ra hEnds hLeft hSep).2.2
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1) hBad).symm
  have hBaseNeLeft : m.base ≠ wd.tracks.iso.dart dLeft := by
    intro hBad
    exact (baseDart_edge_ne_splitLift m wd thickSheet thinSheet ra false)
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1)
        (wd.tracks.iso.dart.injective ((IncomingPairing.dart_baseDart m wd).trans hBad)))
  have hBaseNeRight : m.base ≠ wd.tracks.iso.dart dRight := by
    intro hBad
    have h := wd.tracks.iso.dart.injective ((IncomingPairing.dart_baseDart m wd).trans hBad)
    exact hEnds.1
      (hLeft.symm.trans (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.1.1) h))
  refine ⟨⟨hLeft, hRight⟩, dLeft, dRight, rfl, rfl, ?_⟩
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
        rw [m'.perm_of_ne h1 h2, wd.tracks.iso.vert_map dLeft]
        exact vtx_leftBranch m wd hEnds hLeft
    · rw [(graph.move m').card_fibre (graph.vert m.base)]
      exact le_of_eq (Finset.card_eq_three.mpr ⟨_, _, _, hBaseNeRight, hBaseNeLeft,
        fun hBad ↦ hLeftNeRight (wd.tracks.iso.dart.injective hBad).symm, rfl⟩).symm
  show (Finset.univ.filter fun d ↦ (graph.move m').vert d = graph.vert m.base).erase m.base =
    {wd.tracks.iso.dart dLeft, wd.tracks.iso.dart dRight}
  rw [hStar, Finset.erase_insert (by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact not_or.mpr ⟨hBaseNeRight, hBaseNeLeft⟩), Finset.pair_comm]

/-! ### The orientation clause in the three incoming sub-cases -/

/-- At a `2 + 2` wall the (H-II) orientation of `NonTrivalentValencyTwoTracks`
gives the orientation clause of (H-split), with `p`, `q` the two ends of the
single vanishing occurrence. -/
theorem orientation_of_hBase_two (hNoReturn : NoContractedReturn wd.cover wd.contracted)
    (hBase : wd.tracks.iso.dart (NonTrivalentValencyTwoTracks.facetDartLeft m wd hNoReturn) =
      m.base) :
    (IncomingPairing.baseDart m wd).1.1 = NonTrivalentValencyTwoTracks.leftEnd m wd ∧
      (IncomingPairing.opBaseDart m wd).1.1 = NonTrivalentValencyTwoTracks.rightEnd m wd := by
  refine ⟨?_, ?_⟩
  · rw [IncomingPairing.baseDart_eq_facetDartLeft_two m wd hNoReturn hBase]
    rfl
  · rw [IncomingPairing.opBaseDart_eq_facetDartRight_two m wd hNoReturn hBase]
    rfl

theorem baseDart_eq_facetDartLeft_leaf (F : NonTrivalentValencyTwoTracksLeaf.LeafFold wd)
    (hBase : wd.tracks.iso.dart
      (NonTrivalentValencyTwoTracksLeaf.facetDartLeft m wd F) = m.base) :
    IncomingPairing.baseDart m wd = NonTrivalentValencyTwoTracksLeaf.facetDartLeft m wd F :=
  (Equiv.symm_apply_eq _).mpr hBase.symm

theorem opBaseDart_eq_facetDartRight_leaf (F : NonTrivalentValencyTwoTracksLeaf.LeafFold wd)
    (hBase : wd.tracks.iso.dart
      (NonTrivalentValencyTwoTracksLeaf.facetDartLeft m wd F) = m.base) :
    IncomingPairing.opBaseDart m wd = NonTrivalentValencyTwoTracksLeaf.facetDartRight m wd F :=
  (Equiv.symm_apply_eq _).mpr (NonTrivalentValencyTwoTracksLeaf.op_base_eq m wd F hBase)

/-- At a `1 + 3` or `3 + 1` wall the (H-II) orientation of
`NonTrivalentValencyTwoTracksLeaf` gives the orientation clause of (H-split),
with `p`, `q` the two *outer* ends of the
two-occurrence vanishing path through the leaf fold. -/
theorem orientation_of_hBase_leaf (F : NonTrivalentValencyTwoTracksLeaf.LeafFold wd)
    (hBase : wd.tracks.iso.dart
      (NonTrivalentValencyTwoTracksLeaf.facetDartLeft m wd F) = m.base) :
    (IncomingPairing.baseDart m wd).1.1 = NonTrivalentValencyTwoTracksLeaf.leftEnd m wd F ∧
      (IncomingPairing.opBaseDart m wd).1.1 =
        NonTrivalentValencyTwoTracksLeaf.rightEnd m wd F := by
  refine ⟨?_, ?_⟩
  · rw [baseDart_eq_facetDartLeft_leaf m wd F hBase]
    rfl
  · rw [opBaseDart_eq_facetDartRight_leaf m wd F hBase]
    rfl

/-! ### (H-split) is a condition on rows only -/

/-- **The move always places with `m.base` one dart at each anchor end**:
`IncomingPairing.exists_movedStar_darts` read under the orientation clause of
(H-split). -/
theorem exists_movedStar_darts_at_ends
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hRight : (IncomingPairing.opBaseDart m wd).1.1 = q) :
    ∃ x y : StableSourceDarts.Dart wd.cover,
      x.1.1 = p ∧ y.1.1 = q ∧ x ≠ IncomingPairing.baseDart m wd ∧
        y ≠ IncomingPairing.opBaseDart m wd ∧
        (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
          {wd.tracks.iso.dart x, wd.tracks.iso.dart y} := by
  obtain ⟨x, y, hx, hy, hxne, hyne, hStar⟩ := IncomingPairing.exists_movedStar_darts m wd
  exact ⟨x, y, (congrArg Subtype.val hx).trans hLeft, (congrArg Subtype.val hy).trans hRight,
    hxne, hyne, hStar⟩

/-- **The dispatcher can always discharge (H-split).**  Because the pair a move
names straddles the two anchor ends, the only thing left to check is that the
two darts it names carry the *rows* of `e_alpha` and `e_delta`: that is the whole
content of the row-level condition, and it is exactly what the move-to-type
dispatcher checks. -/
theorem prescribedSplitMove_of_rows
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hRight : (IncomingPairing.opBaseDart m wd).1.1 = q)
    (hRows : ∀ x y : StableSourceDarts.Dart wd.cover, x.1.1 = p → y.1.1 = q →
      (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
          {wd.tracks.iso.dart x, wd.tracks.iso.dart y} →
      x.2.1.stablePath = (splitLift m wd thickSheet thinSheet ra false).stablePath ∧
        y.2.1.stablePath = (splitLift m wd thickSheet thinSheet ra true).stablePath) :
    PrescribedSplitMove m wd thickSheet thinSheet ra p q := by
  obtain ⟨x, y, hx, hy, -, -, hStar⟩ := exists_movedStar_darts_at_ends m wd hLeft hRight
  obtain ⟨hFirst, hSecond⟩ := hRows x y hx hy hStar
  exact ⟨⟨hLeft, hRight⟩, x, y, hFirst, hSecond, hStar⟩

end NonVacuity

end Wall

/-! ## 8.  The mirror member -/

section Mirror

open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitGauge
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitExit (relabelStar
  twoBranchAnchor_relabelStar wallOutgoingFD)

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {deg : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival deg graph label (label m.base)}
  (wd : WallData arrival)
  (wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (thickSheet thinSheet : Fin deg)

variable (ra : SplitAnchor
    (splitGaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) (relabelStar wallStar)
      anchorBlk thickSheet thinSheet) (relabelStar wallStar)
    (splitGaugedAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) (relabelStar wallStar)
      anchorBlk thickSheet thinSheet))
  (hGauged : (splitGaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne)
    (relabelStar wallStar) anchorBlk thickSheet thinSheet).Valid)
  (hOrdGauged : OrdinaryTrivalent (splitGaugedData (contractDatum wd.cover wd.hc wd.hab
    wd.hOne) (relabelStar wallStar) anchorBlk thickSheet thinSheet) ⟨wd.a, wd.hab⟩
    (splitGaugedAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) (relabelStar wallStar)
      anchorBlk thickSheet thinSheet))
  (hOrd : OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
    anchorBlk)
  (labelling₀ : StableLengthMatrixLabelling
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

include hOrd in
/-- **The mirror member costs nothing.**  Every declaration of §§1--7 is stated
over an *arbitrary* wall star, so the Base II split member in which a class over
`wallStar.edge 1` splits above the divalent endpoint is the same theorem read at
`NonTrivalentValencyTwoSplitExit.relabelStar wallStar`; the only thing to
transport is the incoming classifier, by
`NonTrivalentValencyTwoSplitExit.twoBranchAnchor_relabelStar`.  Together with
`exists_typeChangeLink_of_incidence_split` this hands the dispatcher both
Configuration A split members from one star count each. -/
theorem exists_typeChangeLink_of_incidence_splitMirror
    (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk) :
    ∃ ve : BranchVertex (validCandidate ra.setup).datum ≃ V,
      (∀ (v : BranchVertex (validCandidate ra.setup).datum)
          (r : StablePath (validCandidate ra.setup).datum),
        incidenceCount (validCandidate ra.setup).datum v.1 r =
          Nat.card {d : D // graph.vert (m.perm d) = ve v ∧
            label d = (wallOutgoingFD m wd (relabelStar wallStar) anchorBlk thickSheet
              thinSheet labelling₀ ra hGauged hOrdGauged hRowVal hMatrixWall).labelling.row
              r}) → Nonempty (TypeChangeLink m wd) :=
  exists_typeChangeLink_of_incidence_split m wd thickSheet thinSheet ra hGauged hOrdGauged
    hOrd labelling₀ hRowVal hMatrixWall (twoBranchAnchor_relabelStar src)

end Mirror

end

end DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitTracks
