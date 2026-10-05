module

public import DraismaVargas.LocalCases.IncomingPairing
public import DraismaVargas.LocalCases.NonTrivalentValencyTwoTracksLeaf
public import DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneExit

@[expose] public section

/-!
# The vertex dictionary of the valency-two **Base I** type change, and (H-BaseI)

Source: Vargas, Part II (arXiv:2609.09109), Section 5.1 (a combinatorial type
change is recorded as a Whitehead move on the *ambient* tracked graph; the
labelling convention (1)) and Section 5.4 (Case {v2-nd4-t3}, Configuration A,
base tree `T_∅` = Base I, with the numerical condition `|e_α| = |e_β|`,
`|e_γ| = |e_δ|`), together with Draisma--Vargas Part I (arXiv:1909.12924), Case
{w2-r2}, Base I (the fibre above the new leaf: one fold `F` with `|F| = 2` and
two unramified vertices `A₁`, `A₂` above the new trivalent point).

`NonTrivalentValencyTwoBaseOneExit.typeChangeLink_of_receipts_baseOne` has
`tracks` as its only hypothesis; it works over the gauged wall datum
`NonTrivalentValencyTwoGauge.gaugedData`, the Base I candidate of
`NonTrivalentValencyTwoBaseOne`, and the census and row dictionary of
`NonTrivalentValencyTwoBaseOneRows` and `NonTrivalentValencyTwoBaseOneRowEquiv`.
`MovedIncidenceIso.tracksOfMovedIncidence` reduces `tracks` to a branch-vertex
bijection `vertexEquiv : BranchVertex cand.datum ≃ V` and a star count
`hIncidence` against the *permuted* vertex map of `graph.move m`.  This module
delivers the bijection, the hypothesis (H-BaseI) that pins the anchor half of
the star count -- **stated at row level** -- and the off-wall pieces of that
count.

## Why (H-BaseI) is stated at row level

A prescribed-move condition stated at the *occurrence* level
(`first.2.1 = selectedLift …`) is satisfiable only when the named survivor is
directly incident to an end of the vanishing row `h₁`; at a pass-through
survivor -- one whose row reaches its end of `h₁` through an occurrence over the
contracted target occurrence -- it is unsatisfiable, so outside valency four
such a condition would serve no actual Whitehead move.  The right form is the
**row level**: the two darts `m` places with `m.base` carry the *stable rows*
of the two survivors the candidate brings together.  That is what the star
count consumes (`IncomingPairing.label_dart_of_row`), it is always
dischargeable by the dispatcher (`IncomingPairing.exists_movedStar_darts`, here
`exists_movedStar_darts_at_ends` and `prescribedBaseOneMove_of_rows`), and
separation is then free (`IncomingPairing.vertex_of_movedStar_eq_pair`, here
`prescribedBaseOneMove_spec`).  `PrescribedBaseOneMove` is stated that way; no
occurrence-level variant is introduced.

## What is proved

### 1.  The branch vertices of the Base I candidate

* `candVertex`, `nonDanglingValency_candVertex`: the outgoing vertex over a
  wall-datum vertex other than the anchor -- `branchVertex` (the new trivalent
  point) over the wall, `ResolutionAwayFromWall.retainedVertex` away from it --
  with unchanged surviving valency, by the ordinary-block census
  `nd(B_v) = nd(B)` of `NonTrivalentValencyTwoBaseOneRows`.
* `candBranchMap`, `candBranchEquiv`: **the branch vertices of the Base I
  candidate are the branch vertices of the wall datum other than the anchor,
  plus `A₁` and `A₂`.**  Surjectivity reads the case analysis of
  `NonTrivalentValencyTwoBaseOneExit.candidate_trivalent` as a classification:
  above the new leaf the fold `F` is divalent (`nd(F) = 2`) and every other
  sheet is inactive (`nd = 0`), so nothing there is a branch vertex; above the
  new trivalent point the anchor contributes exactly the two classes `A₁`, `A₂`
  with `nd(A_i) = 3`, and an ordinary block keeps `nd(B)`.
* `crossThick`, `crossThin`, `crossSurvivor`,
  `nonDanglingIncident_anchorBranchVertex`: the prescribed cross pair at `A₁`
  (side `false`) and at `A₂` (side `true`), and the exact star
  `{h₁, thick, thin}` that `NonTrivalentValencyTwoBaseOneRows` computes there.
* `injective_retainedRow`, `incidenceCount_retainedVertex_retainedRow`: the
  off-wall half of the star count, transport (T1) away from the wall.

### 2.  The gauge leg

The Base I candidate lives over `NonTrivalentValencyTwoGauge.gaugedData`, not
over the wall datum, so every dictionary has to cross one sheet relabelling.

* `gaugedAnchorVertex`, `gaugeVertexEquiv_anchor`, `gaugeBranchEquiv`,
  `gaugeBranchEquivAnchorComplement`: the gauge on branch vertices, and on
  branch vertices away from the anchor -- the valency-two Base I analogue of
  `gaugeBranchEquivAnchorComplement` in `NonTrivalentValencyFourTracks` and
  `NonTrivalentValencyThreeSimpleTracks`.
* `incidenceCount_gauge`: **the gauge leg of the star-count transport (T2)**,
  one `StableGraphIncidence.incidenceCount_sheetRelabel` along
  `NonTrivalentValencyTwoBaseOneRowDictionary.gaugeRowEquiv`, the row map the
  matrix side already uses.
* `ungaugeSurvivor`, `ungaugeSurvivor_not_isDangling`: a survivor at the gauged
  anchor, read back to the wall datum.

### 3.  The vertex dictionary

* `branchEquivGaugedAnchorComplement`: the `branchEquivAnchorComplement` of
  `NonTrivalentValencyTwoTracks` (the wall contraction, over the abstract pair
  `AnchorEnds` of `NonTrivalentValencyTwoTracksLeaf`) composed with the gauge
  leg.
* `vertexEquiv`: the composite
  `BranchVertex cand.datum ≃ BranchVertex gaugedData-minus-A ⊕ Bool ≃
   BranchVertex M-minus-{p,q} ⊕ Bool ≃ BranchVertex M ≃ V`,
  with `vertexEquiv_inl`, `vertexEquiv_anchor`, and under (H-BaseI)'s
  orientation `vertexEquiv_anchor_false` (`A₁ ↦ graph.vert m.base`) and
  `vertexEquiv_anchor_true` (`A₂ ↦ graph.vert (graph.op m.base)`).

### 4.  (H-BaseI), at row level

* `crossWallEdge`, `crossLift`, `crossLift_stablePath_ne_facetRow`: the two
  cross-paired survivors as surviving occurrences of the incoming cover, read
  back across the gauge and then across the wall contraction; neither lies on
  the vanishing row.
* `PrescribedBaseOneMove m wd … p q`: the orientation clause -- the end of the
  vanishing row at `graph.vert m.base` is the anchor end `p` and the other end is
  `q`, stated with the hypothesis-free `IncomingPairing.baseDart` /
  `opBaseDart` so that it is the same clause in all three incoming sub-cases --
  together with the row-level survivor clause.
* `prescribedBaseOneMove_spec`: under it the two named darts still sit one at
  each anchor end and their labels are the chart rows of the two cross-paired
  survivors -- the two facts the count at `A₁` uses.
* `exists_movedStar_darts_at_ends`, `prescribedBaseOneMove_of_rows`: the move
  always names one dart at each anchor end, so the condition is a statement
  about rows only, and the dispatcher discharges it by matching rows.
* `BaseOneSeparated`, `prescribedMove`,
  `prescribedBaseOneMove_prescribedMove`: **non-vacuity of (H-BaseI), in
  relative form** (an absolute `∃ m, …` does not typecheck, because
  `wd : WallData arrival` fixes `m.base`).
* `orientation_of_hBase_two`, `orientation_of_hBase_leaf`: the orientation
  clause holds in **all three** incoming sub-cases, from the (H-II) orientation
  of `NonTrivalentValencyTwoTracks` and `NonTrivalentValencyTwoTracksLeaf` --
  so the clause is not vacuous at a `2 + 2`, a `1 + 3` or a `3 + 1` wall.

### 5.  The link

* `card_star_move_eq_incidenceCount`: away from the two anchor ends the
  Whitehead move does not change the star (the two valency-agnostic pieces of
  `NonTrivalentValencyTwoTracks`, combined under the orientation clause).
* `typeChangeLink_of_incidence`: **`OuterWalk.TypeChangeLink` at a valency-two
  Base I wall from the star count alone**, through
  `MovedIncidenceIso.tracksOfMovedIncidence` and
  `NonTrivalentValencyTwoBaseOneExit.typeChangeLink_of_receipts_baseOne`; `hOp`
  is free from the incoming tracking.
* `exists_typeChangeLink_of_incidence_baseOne`: the same with the incoming
  trichotomy discharged inside by
  `NonTrivalentValencyTwoTracksLeaf.exists_anchorEnds`, returning the
  branch-vertex bijection the caller must count against.

## What is NOT proved -- the hypotheses that remain explicit

1. `hIncidence`, hence `tracks`: the star count
   `incidenceCount cand.datum v r =
    Nat.card {d // graph.vert (m.perm d) = vertexEquiv v and label d = row r}`.
   This composite is not proved in this file;
   `NonTrivalentValencyTwoBaseOneStarCount` proves it, as the composite of
   * (T1) `incidenceCount gaugedData w r =
     incidenceCount cand.datum (candVertex w) (retainedRow r)`.  Away from the
     wall this is `incidenceCount_retainedVertex_retainedRow` above; **at an
     ordinary wall block** it is
     `NonTrivalentValencyTwoBaseOneStarCount.incidenceCount_branchVertex_ordinary`,
     from `NonTrivalentValencyTwoBaseOneRows.nonDanglingIncident_branchVertex_ordinary`
     (the block keeps exactly its old star, nothing being split or joined at
     Base I) together with the retained row map.
   * (T2) the gauge leg `incidenceCount_gauge`, **proved here**, composed with
     `incidenceCount M_0 w r =
     incidenceCount M (branchEquivAnchorComplement.symm w) (incomingRow r)`.  The
     latter is `WallSplitIncidence.incidenceCount_sourceVertexMap` away
     from the merged target vertex; **at an ordinary wall block** it is the
     valency-agnostic `WallSplitIncidenceOrdinary.incidenceCount_unramified`
     with `internalEdges_subsingleton_of_ne_anchor`, as at valencies
     three, two Base II and four.
   * At the anchor the count is the one (H-BaseI) prescribes together with the
     exact star `nonDanglingIncident_anchorBranchVertex` and the dart-side
     `card_star_move_eq_incidenceCount`; the fold `F` costs nothing, being
     divalent and so not a branch vertex, but it does mean the bridge row `h₁`
     at `A₁` is carried by `A₁`'s own new occurrence and continues through `F`.
   `NonTrivalentValencyTwoBaseOneStarCount.typeChangeLink_of_prescribedBaseOneMove`
   and `exists_typeChangeLink_of_prescribedBaseOneMove_of_wallData` package the
   result as `OuterWalk.TypeChangeLink` from (H-BaseI), `wd` and the incoming
   two-valent star alone.
2. `BaseOneSeparated`, and (H-BaseI) itself.  (H-BaseI) is the per-vertex match
   at the anchor; `BaseOneSeparated` is what makes the wall crossing an actual
   type change.  Neither is derived here; (H-BaseI) has the relative witness
   `prescribedBaseOneMove_prescribedMove` and the orientation clause has the two
   producers of §4.
3. `AnchorEnds m wd anchorBlk p q` -- the abstraction of
   `NonTrivalentValencyTwoTracksLeaf`, supplied unconditionally at every
   two-valent Base II or Base I wall by
   `NonTrivalentValencyTwoTracksLeaf.exists_anchorEnds`, which
   `exists_typeChangeLink_of_incidence_baseOne` calls internally.
4. `wallStar`, `anchorBlk`, `thickSheet`, `thinSheet`, `setup`, `hGauged`,
   `hOrd`, `labelling₀`, `hRowVal`, `hMatrixWall` -- **exactly the binders of
   `wallOutgoingFD` and `typeChangeLink_of_receipts_baseOne` in
   `NonTrivalentValencyTwoBaseOneExit`**; nothing is added.  Configuration A and
   the two index equalities stay the caller's dispatch data, as recorded there
   (Part II, Section 5.4: there is no Base I morphism at all when they fail).
5. No structure is introduced.  The two `Prop` definitions are used as follows:
   `PrescribedBaseOneMove` has the relative witness
   `prescribedBaseOneMove_prescribedMove` together with the orientation
   producers `orientation_of_hBase_two` / `orientation_of_hBase_leaf`;
   `BaseOneSeparated` is a named hypothesis of that witness, in the same style
   as `StablePathFacetContraction.NoContractedReturn`.

## Consumers

`NonTrivalentValencyTwoBaseOneStarCount` proves (T1) and (T2) above
and delivers `typeChangeLink_of_prescribedBaseOneMove`: `OuterWalk.TypeChangeLink`
at Part II, Case {v2-nd4}, Configuration A, the two Base I outgoing types, from
(H-BaseI) and the wall data alone, via `MovedIncidenceIso.tracksOfMovedIncidence`
and hence the `tracks` field of
`NonTrivalentValencyTwoBaseOneExit.typeChangeLink_of_receipts_baseOne`; and the
move-to-type dispatcher of `NonTrivalentValencyTwoDispatcher`, through
`prescribedBaseOneMove_of_rows`.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneTracks

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
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOne
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneRows

noncomputable section

/-! ## 1.  The branch vertices of the Base I candidate -/

section Candidate

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall} (setup : BaseOneSetup data star anchor)

local notation "cand" => (validCandidate setup)

/-- A wall vertex of the datum is the source endpoint of its own sheet. -/
theorem sourceEndpoint_self (w : data.SourceVertex) (hw : w.1.1 = wall) :
    data.sourceEndpoint wall w.1.2 = w :=
  (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hw.symm, rfl⟩

/-- A wall vertex other than the anchor is an ordinary block. -/
theorem not_rel_anchor_of_ne (w : data.SourceVertex) (hw : w.1.1 = wall)
    (hne : w ≠ WallBlock.sourceVertex data wall anchor) :
    ¬ (data.vertexPartition wall).Rel anchor.1 w.1.2 := by
  intro hBad
  exact hne
    ((NonTrivalentValencyThreeExit.sourceEndpoint_eq_of_rel hBad).trans
      (sourceEndpoint_self w hw)).symm

open scoped Classical in
/-- **The outgoing vertex over a wall-datum vertex other than the anchor.**
Over the wall the Base I candidate sends the whole ordinary block to the new
trivalent point `v`; away from the wall the vertex is simply retained. -/
def candVertex (w : data.SourceVertex) : (cand).datum.SourceVertex :=
  if w.1.1 = wall then branchVertex setup w.1.2
  else ResolutionAwayFromWall.retainedVertex (cand) w

theorem candVertex_wall (w : data.SourceVertex) (hw : w.1.1 = wall) :
    candVertex setup w = branchVertex setup w.1.2 := by
  unfold candVertex
  rw [ite_eq_left hw]

theorem candVertex_away (w : data.SourceVertex) (hw : w.1.1 ≠ wall) :
    candVertex setup w = ResolutionAwayFromWall.retainedVertex (cand) w := by
  unfold candVertex
  rw [ite_eq_right hw]

theorem branchVertex_target (y : Fin degree) :
    (branchVertex setup y).1.1 = freshVertex target :=
  ((GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mp rfl).1.symm

theorem candVertex_wall_target (w : data.SourceVertex) (hw : w.1.1 = wall) :
    (candVertex setup w).1.1 = freshVertex target := by
  rw [candVertex_wall setup w hw]
  exact branchVertex_target setup w.1.2

theorem candVertex_away_target (w : data.SourceVertex) (hw : w.1.1 ≠ wall) :
    (candVertex setup w).1.1 = oldVertex target w.1.1 := by
  rw [candVertex_away setup w hw]
  exact ((GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mp rfl).1.symm

/-- **The surviving valency is unchanged.**  Over the wall this is the
ordinary-block census `nd(B_v) = nd(B)` of `NonTrivalentValencyTwoBaseOneRows`;
away from it, the retained vertex. -/
theorem nonDanglingValency_candVertex (hValid : data.Valid) (w : data.SourceVertex)
    (hne : w ≠ WallBlock.sourceVertex data wall anchor) :
    nonDanglingValency (cand).datum (candVertex setup w) = nonDanglingValency data w := by
  classical
  by_cases hw : w.1.1 = wall
  · rw [candVertex_wall setup w hw,
      nonDanglingValency_branchVertex_ordinary setup hValid (not_rel_anchor_of_ne w hw hne),
      sourceEndpoint_self w hw]
  · rw [candVertex_away setup w hw,
      ResolutionAwayFromWall.nonDanglingValency_retainedVertex (cand) hValid
        (candidate_sourceGenus setup) w hw]

/-! ### The branch vertices of the Base I candidate -/

/-- The sheet naming `A₁` (side `false`) and `A₂` (side `true`). -/
def anchorBranchSheet (side : Bool) : Fin degree :=
  if side then setup.foldSecond else setup.foldFirst

theorem anchorBranchSheet_wall (side : Bool) :
    (data.vertexPartition wall).Rel anchor.1 (anchorBranchSheet setup side) := by
  cases side with
  | false => exact setup.foldFirst_wall
  | true => exact setup.foldSecond_wall

theorem anchorBranchVertex_ne :
    branchVertex setup (anchorBranchSheet setup false) ≠
      branchVertex setup (anchorBranchSheet setup true) :=
  branchVertex_fold_ne setup

/-- **The branch vertices of the Base I candidate.**  Every branch vertex is
either the outgoing copy of a branch vertex of the wall datum other than the
anchor, or one of the two vertices `A₁`, `A₂` above the new trivalent point.
The fold `F` is divalent and every other sheet above the new leaf is inactive,
so nothing above the leaf is a branch vertex. -/
def candBranchMap (hValid : data.Valid) :
    ({w : BranchVertex data // w.1 ≠ WallBlock.sourceVertex data wall anchor} ⊕ Bool) →
      BranchVertex (cand).datum
  | Sum.inl w => ⟨candVertex setup w.1.1, by
      rw [nonDanglingValency_candVertex setup hValid w.1.1 w.2]
      exact w.1.2⟩
  | Sum.inr side => ⟨branchVertex setup (anchorBranchSheet setup side),
      (NonTrivalentValencyTwoBaseOneRowEquiv.nonDanglingValency_branchVertex_anchor_sheet
        setup hValid (anchorBranchSheet_wall setup side)).ge⟩

theorem candBranchMap_injective (hValid : data.Valid) :
    Function.Injective (candBranchMap setup hValid) := by
  classical
  have hAnchorRel : ∀ side : Bool,
      (data.vertexPartition wall).Rel anchor.1 (anchorBranchSheet setup side) :=
    anchorBranchSheet_wall setup
  rintro (w | side) (w' | side') hEq <;>
    have hv : (candBranchMap setup hValid _).1 = (candBranchMap setup hValid _).1 :=
      congrArg Subtype.val hEq
  · by_cases hw : w.1.1.1.1 = wall <;> by_cases hw' : w'.1.1.1.1 = wall
    · have hEq2 : branchVertex setup w.1.1.1.2 = branchVertex setup w'.1.1.1.2 := by
        rw [← candVertex_wall setup w.1.1 hw, ← candVertex_wall setup w'.1.1 hw']
        exact hv
      have hX : ¬ (data.vertexPartition wall).Rel anchor.1 w.1.1.1.2 :=
        not_rel_anchor_of_ne w.1.1 hw w.2
      have hRel := (branchPartition_rel_ordinary setup hX).mp
        (branchPartition_rel_of_branchVertex_eq setup hEq2)
      have h1 : (data.vertexPartition wall).repr w.1.1.1.2 = w.1.1.1.2 := by
        have h := w.1.1.2
        rw [hw] at h
        exact h
      have h2 : (data.vertexPartition wall).repr w'.1.1.1.2 = w'.1.1.1.2 := by
        have h := w'.1.1.2
        rw [hw'] at h
        exact h
      have hSheet : w.1.1.1.2 = w'.1.1.1.2 := by
        rw [← h1, ← h2]
        exact hRel
      exact congrArg Sum.inl (Subtype.ext (Subtype.ext (Subtype.ext
        (Prod.ext (hw.trans hw'.symm) hSheet))))
    · exact absurd ((candVertex_wall_target setup w.1.1 hw).symm.trans
        ((congrArg (fun z : (cand).datum.SourceVertex ↦ z.1.1) hv).trans
          (candVertex_away_target setup w'.1.1 hw'))) Sum.inr_ne_inl
    · exact absurd ((candVertex_away_target setup w.1.1 hw).symm.trans
        ((congrArg (fun z : (cand).datum.SourceVertex ↦ z.1.1) hv).trans
          (candVertex_wall_target setup w'.1.1 hw'))) Sum.inl_ne_inr
    · have hRet : ResolutionAwayFromWall.retainedVertex (cand) w.1.1 =
          ResolutionAwayFromWall.retainedVertex (cand) w'.1.1 := by
        rw [← candVertex_away setup w.1.1 hw, ← candVertex_away setup w'.1.1 hw']
        exact hv
      exact congrArg Sum.inl (Subtype.ext (Subtype.ext
        (ResolutionStableIncidence.retainedVertex_injective_away (cand) w.1.1 w'.1.1
          hw hw' hRet)))
  · exfalso
    by_cases hw : w.1.1.1.1 = wall
    · have hEq2 : branchVertex setup w.1.1.1.2 =
          branchVertex setup (anchorBranchSheet setup side') := by
        rw [← candVertex_wall setup w.1.1 hw]
        exact hv
      have hX : ¬ (data.vertexPartition wall).Rel anchor.1 w.1.1.1.2 :=
        not_rel_anchor_of_ne w.1.1 hw w.2
      have hRel := (branchPartition_rel_ordinary setup hX).mp
        (branchPartition_rel_of_branchVertex_eq setup hEq2)
      exact hX ((hAnchorRel side').trans hRel.symm)
    · exact Sum.inl_ne_inr ((candVertex_away_target setup w.1.1 hw).symm.trans
        ((congrArg (fun z : (cand).datum.SourceVertex ↦ z.1.1) hv).trans
          (branchVertex_target setup (anchorBranchSheet setup side'))))
  · exfalso
    by_cases hw : w'.1.1.1.1 = wall
    · have hEq2 : branchVertex setup w'.1.1.1.2 =
          branchVertex setup (anchorBranchSheet setup side) := by
        rw [← candVertex_wall setup w'.1.1 hw]
        exact hv.symm
      have hX : ¬ (data.vertexPartition wall).Rel anchor.1 w'.1.1.1.2 :=
        not_rel_anchor_of_ne w'.1.1 hw w'.2
      have hRel := (branchPartition_rel_ordinary setup hX).mp
        (branchPartition_rel_of_branchVertex_eq setup hEq2)
      exact hX ((hAnchorRel side).trans hRel.symm)
    · exact Sum.inl_ne_inr ((candVertex_away_target setup w'.1.1 hw).symm.trans
        ((congrArg (fun z : (cand).datum.SourceVertex ↦ z.1.1) hv).symm.trans
          (branchVertex_target setup (anchorBranchSheet setup side))))
  · cases side <;> cases side' <;>
      first
        | rfl
        | exact absurd hv (anchorBranchVertex_ne setup)
        | exact absurd hv.symm (anchorBranchVertex_ne setup)

theorem candBranchMap_surjective (hValid : data.Valid) :
    Function.Surjective (candBranchMap setup hValid) := by
  classical
  intro v
  rcases hcase : (v.1.1.1 : TargetExpansion.Vertex target) with place | u
  · by_cases hIsWall : place = wall
    · exfalso
      have hLeaf : leafVertex setup v.1.1.2 = v.1 :=
        NonTrivalentValencyTwoBaseOneExit.eq_leafVertex setup v.1 (by rw [hcase, hIsWall]; rfl)
      have hNd := v.2
      rw [← hLeaf] at hNd
      by_cases h1 : v.1.1.2 = setup.foldFirst
      · rw [h1, nonDanglingValency_leafVertex_fold setup hValid] at hNd
        omega
      · by_cases h2 : v.1.1.2 = setup.foldSecond
        · rw [h2, leafVertex_fold_eq setup, nonDanglingValency_leafVertex_fold setup hValid] at hNd
          omega
        · rw [nonDanglingValency_leafVertex_singleton setup hValid h1 h2] at hNd
          omega
    · obtain ⟨old, hOld, hRet⟩ :=
        ResolutionAwayFromWall.exists_retainedVertex_of_target (cand) v.1 place hIsWall hcase
      have hAway : old.1.1 ≠ wall := by rw [hOld]; exact hIsWall
      have hNd : 3 ≤ nonDanglingValency data old := by
        have h := v.2
        rw [← hRet, ResolutionAwayFromWall.nonDanglingValency_retainedVertex (cand) hValid
          (candidate_sourceGenus setup) old hAway] at h
        exact h
      have hNeAnchor : old ≠ WallBlock.sourceVertex data wall anchor := by
        intro hBad
        exact hAway (by rw [hBad]; rfl)
      refine ⟨Sum.inl ⟨⟨old, hNd⟩, hNeAnchor⟩, Subtype.ext ?_⟩
      show candVertex setup old = v.1
      rw [candVertex_away setup old hAway]
      exact hRet
  · cases u
    have hBranch : branchVertex setup v.1.1.2 = v.1 :=
      NonTrivalentValencyTwoBaseOneExit.eq_branchVertex setup v.1 (by rw [hcase]; rfl)
    by_cases hAnchor : (data.vertexPartition wall).Rel anchor.1 v.1.1.2
    · have hSide : ∀ side : Bool,
          (data.edgePartition (star.edge 0)).Rel (anchorBranchSheet setup side) v.1.1.2 →
            candBranchMap setup hValid (Sum.inr side) = v := by
        intro side hRel
        refine Subtype.ext ?_
        show branchVertex setup (anchorBranchSheet setup side) = v.1
        rw [← hBranch]
        exact branchVertex_eq setup ((branchPartition_rel_anchor setup
          (anchorBranchSheet_wall setup side)).mpr
          ((refineOnBlock_rel_iff (data.vertexPartition wall)
            (data.edgePartition (star.edge 0)) anchor.1 (anchorBranchSheet setup side)
            v.1.1.2 (star.edgePartition_refines_wall data 0)
            (anchorBranchSheet_wall setup side)).mpr hRel))
      rcases setup.cover hAnchor with h | h
      · exact ⟨Sum.inr false, hSide false h⟩
      · exact ⟨Sum.inr true, hSide true h⟩
    · have hRepr : branchVertex setup ((data.vertexPartition wall).repr v.1.1.2) =
          branchVertex setup v.1.1.2 :=
        branchVertex_eq setup ((branchPartition_rel_ordinary setup
          (not_rel_repr hAnchor)).mpr
          ((data.vertexPartition wall).rel_repr_left v.1.1.2))
      have hCand : candVertex setup (data.sourceEndpoint wall v.1.1.2) =
          branchVertex setup v.1.1.2 := by
        rw [candVertex_wall setup _ rfl]
        exact hRepr
      have hNd : 3 ≤ nonDanglingValency data (data.sourceEndpoint wall v.1.1.2) := by
        have h := v.2
        rw [← hBranch, nonDanglingValency_branchVertex_ordinary setup hValid hAnchor] at h
        exact h
      have hNeAnchor : data.sourceEndpoint wall v.1.1.2 ≠
          WallBlock.sourceVertex data wall anchor := by
        intro hBad
        have h : (data.vertexPartition wall).repr v.1.1.2 =
            (data.vertexPartition wall).repr anchor.1 :=
          congrArg (fun z : data.SourceVertex ↦ z.1.2) hBad
        exact hAnchor h.symm
      refine ⟨Sum.inl ⟨⟨data.sourceEndpoint wall v.1.1.2, hNd⟩, hNeAnchor⟩, Subtype.ext ?_⟩
      show candVertex setup (data.sourceEndpoint wall v.1.1.2) = v.1
      rw [hCand]
      exact hBranch

/-- **The branch-vertex dictionary of the Base I candidate.** -/
def candBranchEquiv (hValid : data.Valid) :
    ({w : BranchVertex data // w.1 ≠ WallBlock.sourceVertex data wall anchor} ⊕ Bool) ≃
      BranchVertex (cand).datum :=
  Equiv.ofBijective (candBranchMap setup hValid)
    ⟨candBranchMap_injective setup hValid, candBranchMap_surjective setup hValid⟩

/-! ### The prescribed cross pair at the two anchor branch vertices -/

/-- The `t₂`-survivor the cross pairing brings to `A₁` (side `false`) and to
`A₂` (side `true`). -/
def crossThick (side : Bool) :
    IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor) :=
  if side then setup.secondOf 0 else setup.firstOf 0

theorem crossThick_mem (side : Bool) :
    crossThick setup side ∈ directionSurvivors data star anchor 0 := by
  cases side with
  | false => exact setup.firstOf_mem 0
  | true => exact setup.secondOf_mem 0

theorem occurrenceSheet_crossThick (side : Bool) :
    occurrenceSheet (crossThick setup side) = anchorBranchSheet setup side := by
  cases side <;> rfl

/-- The `t₃`-survivor the cross pairing brings to the same vertex, through the
Base I alignment `Aligned`. -/
def crossThin (side : Bool) :
    IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor) :=
  Classical.choose (exists_thinPartner setup (anchorBranchSheet_wall setup side))

theorem crossThin_mem (side : Bool) :
    crossThin setup side ∈ directionSurvivors data star anchor 1 :=
  (Classical.choose_spec (exists_thinPartner setup (anchorBranchSheet_wall setup side))).1

theorem crossThin_meet (side : Bool) :
    (data.edgePartition (star.edge 0)).Rel (occurrenceSheet (crossThin setup side))
      (anchorBranchSheet setup side) :=
  (Classical.choose_spec (exists_thinPartner setup (anchorBranchSheet_wall setup side))).2

/-- One member of the cross pair, selected by direction. -/
def crossSurvivor (side dir : Bool) :
    IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor) :=
  if dir then crossThin setup side else crossThick setup side

theorem crossSurvivor_not_isDangling (side dir : Bool) :
    ¬ IsDangling data (crossSurvivor setup side dir).1 := by
  cases dir with
  | false => exact survivor_not_isDangling (crossThick_mem setup side)
  | true => exact survivor_not_isDangling (crossThin_mem setup side)

/-- **The exact surviving star of `A₁` / `A₂`**: the bridge occurrence of its own
fold sheet together with the two members of its cross pair
(`NonTrivalentValencyTwoBaseOneRows.nonDanglingIncident_branchVertex_anchor`,
read at the named pair). -/
theorem nonDanglingIncident_anchorBranchVertex (hValid : data.Valid) (side : Bool) :
    nonDanglingIncident (cand).datum (branchVertex setup (anchorBranchSheet setup side)) =
      {(cand).newSourceEdge (anchorBranchSheet setup side),
        (cand).oldSourceEdge (crossThick setup side).1,
        (cand).oldSourceEdge (crossThin setup side).1} := by
  have hMeet : (data.edgePartition (star.edge 0)).Rel
      (occurrenceSheet (crossThick setup side)) (occurrenceSheet (crossThin setup side)) := by
    rw [occurrenceSheet_crossThick setup side]
    exact (crossThin_meet setup side).symm
  have h := nonDanglingIncident_branchVertex_anchor setup hValid (crossThick_mem setup side)
    (crossThin_mem setup side) hMeet
  rwa [occurrenceSheet_crossThick setup side] at h

/-! ### The off-wall half of the star count -/

/-- **The retained-row map is injective**, from the row dictionary of
`NonTrivalentValencyTwoBaseOneRowEquiv` (the complement of the retained image is
the bridge row). -/
theorem injective_retainedRow (hValid : data.Valid) :
    Function.Injective (NonTrivalentValencyTwoBaseOneRowEquiv.retainedRow setup hValid) := by
  intro r r' h
  have h2 := congrArg (NonTrivalentValencyTwoBaseOneRowEquiv.rowEquiv setup hValid) h
  rw [NonTrivalentValencyTwoBaseOneRowEquiv.rowEquiv_retainedRow setup hValid r,
    NonTrivalentValencyTwoBaseOneRowEquiv.rowEquiv_retainedRow setup hValid r'] at h2
  exact Option.some_injective _ h2

/-- **Away from the wall the Base I candidate does not change the star.**  This
is `ResolutionStableIncidence.incidenceCount_retainedVertex` with its row
*equivalence* hypothesis weakened to injectivity of the retained-row map, which
is all the proof uses. -/
theorem incidenceCount_retainedVertex_retainedRow (hValid : data.Valid)
    (w : data.SourceVertex) (hAway : w.1.1 ≠ wall) (row : StablePath data) :
    incidenceCount data w row =
      incidenceCount (cand).datum (ResolutionAwayFromWall.retainedVertex (cand) w)
        (NonTrivalentValencyTwoBaseOneRowEquiv.retainedRow setup hValid row) := by
  classical
  unfold incidenceCount
  apply Finset.card_bij (fun edge _ ↦ ResolutionAwayFromWall.retainedEdge (cand) hValid.1 edge)
  · intro edge hEdge
    simp only [Finset.mem_filter, mem_incidentEdges] at hEdge ⊢
    refine ⟨(ResolutionAwayFromWall.incident_oldSourceEdge_iff (cand) w hAway edge.1).mpr
      hEdge.1, ?_⟩
    rw [← NonTrivalentValencyTwoBaseOneRowEquiv.retainedRow_mk setup hValid edge, hEdge.2]
  · intro first _ second _ hEq
    exact ResolutionAwayFromWall.retainedEdge_injective (cand) hValid.1 hEq
  · intro edge hEdge
    simp only [Finset.mem_filter, mem_incidentEdges] at hEdge
    have hMem : edge.1 ∈ nonDanglingIncident (cand).datum
        (ResolutionAwayFromWall.retainedVertex (cand) w) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hEdge.1⟩
    rw [ResolutionAwayFromWall.nonDanglingIncident_retainedVertex (cand) hValid
      (candidate_sourceGenus setup) w hAway] at hMem
    obtain ⟨old, hOld, hEqual⟩ := Finset.mem_image.mp hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hOld
    refine ⟨⟨old, hSurvives⟩, ?_, Subtype.ext hEqual⟩
    refine Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr hIncident,
      injective_retainedRow setup hValid ?_⟩
    rw [NonTrivalentValencyTwoBaseOneRowEquiv.retainedRow_mk setup hValid
      (⟨old, hSurvives⟩ : NonDanglingEdge data),
      show ResolutionAwayFromWall.retainedEdge (cand) hValid.1 ⟨old, hSurvives⟩ = edge from
        Subtype.ext hEqual]
    exact hEdge.2

end Candidate

/-! ## 2.  The gauge leg -/

section Gauge

open DraismaVargas.LocalCases.NonTrivalentValencyTwoGauge
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneExit (gaugeVertexEquiv
  nonDanglingValency_gauge)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  (base : GluingDatum target degree) (star : TwoStar target wall)
  (anchor : WallBlock base wall) (thickSheet thinSheet : Fin degree)
  (hConn : base.Connected)

/-- The anchor of the gauged wall datum. -/
def gaugedAnchorVertex : (gaugedData base star anchor thickSheet thinSheet).SourceVertex :=
  WallBlock.sourceVertex (gaugedData base star anchor thickSheet thinSheet) wall
    (gaugedAnchor base star anchor thickSheet thinSheet)

/-- **The gauge carries the anchor to the gauged anchor.** -/
theorem gaugeVertexEquiv_anchor :
    gaugeVertexEquiv base star anchor thickSheet thinSheet
        (WallBlock.sourceVertex base wall anchor) =
      gaugedAnchorVertex base star anchor thickSheet thinSheet :=
  gauged_sourceVertex_eq base star anchor thickSheet thinSheet

/-- **The branch vertices across the gauge.** -/
def gaugeBranchEquiv :
    BranchVertex base ≃ BranchVertex (gaugedData base star anchor thickSheet thinSheet) :=
  (gaugeVertexEquiv base star anchor thickSheet thinSheet).subtypeEquiv fun v ↦ by
    rw [nonDanglingValency_gauge base star anchor thickSheet thinSheet hConn v]

@[simp] theorem gaugeBranchEquiv_val (v : BranchVertex base) :
    (gaugeBranchEquiv base star anchor thickSheet thinSheet hConn v).1 =
      gaugeVertexEquiv base star anchor thickSheet thinSheet v.1 := rfl

/-- **The branch vertices away from the anchor, across the gauge.** -/
def gaugeBranchEquivAnchorComplement :
    {w : BranchVertex base // w.1 ≠ WallBlock.sourceVertex base wall anchor} ≃
      {w : BranchVertex (gaugedData base star anchor thickSheet thinSheet) //
        w.1 ≠ gaugedAnchorVertex base star anchor thickSheet thinSheet} :=
  (gaugeBranchEquiv base star anchor thickSheet thinSheet hConn).subtypeEquiv fun w ↦ by
    show w.1 ≠ WallBlock.sourceVertex base wall anchor ↔
      gaugeVertexEquiv base star anchor thickSheet thinSheet w.1 ≠
        gaugedAnchorVertex base star anchor thickSheet thinSheet
    constructor
    · intro hw hBad
      exact hw ((gaugeVertexEquiv base star anchor thickSheet thinSheet).injective
        (hBad.trans (gaugeVertexEquiv_anchor base star anchor thickSheet thinSheet).symm))
    · intro hw hBad
      exact hw (by rw [hBad, gaugeVertexEquiv_anchor base star anchor thickSheet thinSheet])

@[simp] theorem gaugeBranchEquivAnchorComplement_apply
    (w : {w : BranchVertex base // w.1 ≠ WallBlock.sourceVertex base wall anchor}) :
    (gaugeBranchEquivAnchorComplement base star anchor thickSheet thinSheet hConn w).1.1 =
      gaugeVertexEquiv base star anchor thickSheet thinSheet w.1.1 := rfl

/-- **The gauge leg of the star-count transport (T2).**  The gauge is a sheet
relabelling, so it carries every row-filtered star to the corresponding one;
the row map is `NonTrivalentValencyTwoBaseOneRowDictionary.gaugeRowEquiv`, the
one the matrix side uses. -/
theorem incidenceCount_gauge (v : base.SourceVertex) (r : StablePath base) :
    incidenceCount base v r =
      incidenceCount (gaugedData base star anchor thickSheet thinSheet)
        (gaugeVertexEquiv base star anchor thickSheet thinSheet v)
        (NonTrivalentValencyTwoBaseOneRowDictionary.gaugeRowEquiv base star anchor thickSheet
          thinSheet hConn r) :=
  StableGraphIncidence.incidenceCount_sheetRelabel
    (relabeling base star anchor thickSheet thinSheet) hConn v r

/-- A survivor at the gauged anchor, read back to the datum the gauge acts on. -/
def ungaugeSurvivor
    (e : IncidentSourceEdge (gaugedData base star anchor thickSheet thinSheet)
      (WallBlock.sourceVertex (gaugedData base star anchor thickSheet thinSheet) wall
        (gaugedAnchor base star anchor thickSheet thinSheet))) :
    IncidentSourceEdge base (WallBlock.sourceVertex base wall anchor) :=
  (survivorEquiv base star anchor thickSheet thinSheet).symm e

include hConn in
/-- The gauge is a sheet relabelling, so it carries survivors to survivors. -/
theorem ungaugeSurvivor_not_isDangling
    (e : IncidentSourceEdge (gaugedData base star anchor thickSheet thinSheet)
      (WallBlock.sourceVertex (gaugedData base star anchor thickSheet thinSheet) wall
        (gaugedAnchor base star anchor thickSheet thinSheet)))
    (hSurv : ¬ IsDangling (gaugedData base star anchor thickSheet thinSheet) e.1) :
    ¬ IsDangling base (ungaugeSurvivor base star anchor thickSheet thinSheet e).1 := by
  intro hBad
  refine hSurv ?_
  have h := (gauged_isDangling_iff base star anchor thickSheet thinSheet hConn
    (ungaugeSurvivor base star anchor thickSheet thinSheet e)).mpr hBad
  rwa [show survivorEquiv base star anchor thickSheet thinSheet
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
open DraismaVargas.LocalCases.NonTrivalentValencyTwoGauge
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

variable (setup : BaseOneSetup
    (gaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      thickSheet thinSheet) wallStar
    (gaugedAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      thickSheet thinSheet))
  (hGauged : (gaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
    thickSheet thinSheet).Valid)
  (hOrd : NonTrivalentValencyTwoRowEquiv.OrdinaryTrivalent
    (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk)
  {p q : wd.cover.SourceVertex}

/-- **The branch-vertex dictionary across the wall contraction *and* the
`t₃`-branch alignment gauge of `NonTrivalentValencyTwoGauge`**: the
`branchEquivAnchorComplement` of the valency-two tracks, over `AnchorEnds`,
composed with the gauge leg. -/
def branchEquivGaugedAnchorComplement (hEnds : AnchorEnds m wd anchorBlk p q) :
    {v : BranchVertex wd.cover // v.1 ≠ p ∧ v.1 ≠ q} ≃
      {w : BranchVertex (gaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
          anchorBlk thickSheet thinSheet) //
        w.1 ≠ gaugedAnchorVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
          anchorBlk thickSheet thinSheet} :=
  (branchEquivAnchorComplement m wd hOrd hEnds).trans
    (gaugeBranchEquivAnchorComplement (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
      anchorBlk thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1)

/-- **The vertex dictionary of the valency-two Base I type change.**  Away from
the anchor it is the outgoing vertex of the gauged wall datum, read back across
the gauge, then to the incoming cover by the branch dictionary of the wall
contraction, and finally through the incoming tracking; `A₁` and `A₂` go to the
two anchor ends of the vanishing row. -/
def vertexEquiv (hEnds : AnchorEnds m wd anchorBlk p q) :
    BranchVertex (validCandidate setup).datum ≃ V :=
  ((candBranchEquiv setup hGauged).symm.trans
    (Equiv.sumCongr
      (branchEquivGaugedAnchorComplement m wd thickSheet thinSheet hOrd hEnds).symm
      (Equiv.refl Bool))).trans
    ((coverBranchEquiv m wd hEnds).trans wd.tracks.iso.vtx)

@[simp] theorem vertexEquiv_inl (hEnds : AnchorEnds m wd anchorBlk p q)
    (w : {w : BranchVertex (gaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
        anchorBlk thickSheet thinSheet) //
      w.1 ≠ gaugedAnchorVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
        anchorBlk thickSheet thinSheet}) :
    vertexEquiv m wd thickSheet thinSheet setup hGauged hOrd hEnds
        (candBranchMap setup hGauged (Sum.inl w)) =
      wd.tracks.iso.vtx
        ((branchEquivGaugedAnchorComplement m wd thickSheet thinSheet hOrd hEnds).symm w).1 := by
  have h : (candBranchEquiv setup hGauged).symm
      (candBranchMap setup hGauged (Sum.inl w)) = Sum.inl w :=
    (candBranchEquiv setup hGauged).symm_apply_apply (Sum.inl w)
  show wd.tracks.iso.vtx (coverBranchMap m wd hEnds
    (Equiv.sumCongr
      (branchEquivGaugedAnchorComplement m wd thickSheet thinSheet hOrd hEnds).symm
      (Equiv.refl Bool)
      ((candBranchEquiv setup hGauged).symm
        (candBranchMap setup hGauged (Sum.inl w))))) = _
  rw [h]
  rfl

@[simp] theorem vertexEquiv_anchor (hEnds : AnchorEnds m wd anchorBlk p q) (side : Bool) :
    vertexEquiv m wd thickSheet thinSheet setup hGauged hOrd hEnds
        (candBranchMap setup hGauged (Sum.inr side)) =
      wd.tracks.iso.vtx (if side then rightBranch m wd hEnds else leftBranch m wd hEnds) := by
  have h : (candBranchEquiv setup hGauged).symm
      (candBranchMap setup hGauged (Sum.inr side)) = Sum.inr side :=
    (candBranchEquiv setup hGauged).symm_apply_apply (Sum.inr side)
  show wd.tracks.iso.vtx (coverBranchMap m wd hEnds
    (Equiv.sumCongr
      (branchEquivGaugedAnchorComplement m wd thickSheet thinSheet hOrd hEnds).symm
      (Equiv.refl Bool)
      ((candBranchEquiv setup hGauged).symm
        (candBranchMap setup hGauged (Sum.inr side))))) = _
  rw [h]
  rfl

/-! ## 4.  (H-BaseI), stated at row level -/

/-- **One member of the prescribed cross pair, as a surviving occurrence of the
incoming cover.**  `side = false` is the pair that meets at `A₁`, `side = true`
the pair that meets at `A₂`; `dir = false` is the `t₂`-member, `dir = true` the
`t₃`-member.  The occurrence is read back across the gauge of
`NonTrivalentValencyTwoGauge` and then across the wall contraction. -/
def crossWallEdge (side dir : Bool) :
    NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne) :=
  ⟨(ungaugeSurvivor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      thickSheet thinSheet (crossSurvivor setup side dir)).1,
    ungaugeSurvivor_not_isDangling (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
      anchorBlk thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1
      (crossSurvivor setup side dir) (crossSurvivor_not_isDangling setup side dir)⟩

/-- The same, read as a surviving occurrence of the incoming cover. -/
def crossLift (side dir : Bool) : NonDanglingEdge wd.cover :=
  NonTrivalentValencyTwoTracks.liftEdge m wd
    (crossWallEdge m wd thickSheet thinSheet setup side dir)

theorem crossLift_stablePath (side dir : Bool) :
    (crossLift m wd thickSheet thinSheet setup side dir).stablePath =
      incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m)
        (crossWallEdge m wd thickSheet thinSheet setup side dir).stablePath := rfl

/-- **No member of the cross pair lies on the vanishing row.** -/
theorem crossLift_stablePath_ne_facetRow (side dir : Bool) :
    (crossLift m wd thickSheet thinSheet setup side dir).stablePath ≠
      NonTrivalentValencyTwoTracks.facetRow m wd := by
  rw [crossLift_stablePath m wd thickSheet thinSheet setup side dir]
  exact incomingRow_ne_facet wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m)
    (wd.hForest m) wd.coordinates (label m.base) wd.hZeroCoord wd.hPosCoord wd.hFacetZero _

/-- **(H-BaseI), the per-vertex match at the anchor of a valency-two Base I
wall, stated at row level.**  The two darts the Whitehead move `m` places
together with `m.base` -- the moved star of `graph.vert m.base` with `m.base`
removed -- carry the **stable rows** of the two survivors that the prescribed
cross pairing brings together at `A₁`, in the orientation that puts the `A₁` end
of the vanishing row at `graph.vert m.base`.

The first conjunct is the orientation: the end of the vanishing row at
`graph.vert m.base` is the anchor end `p`, and the other end is `q`.  The other
orientation is normalised away by the caller with `CubicDartGraph.MoveData.swap`,
which leaves `graph.move m` unchanged.

The survivor clause is stated at the level of **rows**, not of occurrences: a
merged survivor may reach its end of the vanishing row through a pass-through
occurrence over the contracted target occurrence, in which case an
occurrence-level clause would be unsatisfiable.  The row-level clause is what
the star count consumes (`IncomingPairing.label_dart_of_row`) and what the
dispatcher can always discharge (`IncomingPairing.exists_movedStar_darts`). -/
def PrescribedBaseOneMove (p q : wd.cover.SourceVertex) : Prop :=
  ((IncomingPairing.baseDart m wd).1.1 = p ∧ (IncomingPairing.opBaseDart m wd).1.1 = q) ∧
    ∃ first second : StableSourceDarts.Dart wd.cover,
      first.2.1.stablePath =
          (crossLift m wd thickSheet thinSheet setup false false).stablePath ∧
        second.2.1.stablePath =
            (crossLift m wd thickSheet thinSheet setup false true).stablePath ∧
          (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
            {wd.tracks.iso.dart first, wd.tracks.iso.dart second}

/-- **Under (H-BaseI) the two named darts sit one at each anchor end, and their
labels are the chart rows of the two cross-paired survivors** -- the two facts
the star count at `A₁` uses. -/
theorem prescribedBaseOneMove_spec (p q : wd.cover.SourceVertex)
    (hPres : PrescribedBaseOneMove m wd thickSheet thinSheet setup p q) :
    ∃ first second : StableSourceDarts.Dart wd.cover,
      ((first.1.1 = p ∧ second.1.1 = q) ∨ (first.1.1 = q ∧ second.1.1 = p)) ∧
      label (wd.tracks.iso.dart first) = wd.fullDim.labelling.row
          (crossLift m wd thickSheet thinSheet setup false false).stablePath ∧
      label (wd.tracks.iso.dart second) = wd.fullDim.labelling.row
          (crossLift m wd thickSheet thinSheet setup false true).stablePath ∧
      (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
        {wd.tracks.iso.dart first, wd.tracks.iso.dart second} := by
  obtain ⟨⟨hLeft, hRight⟩, first, second, hFirst, hSecond, hStar⟩ := hPres
  refine ⟨first, second, ?_, IncomingPairing.label_dart_of_row m wd first _ hFirst,
    IncomingPairing.label_dart_of_row m wd second _ hSecond, hStar⟩
  rcases IncomingPairing.vertex_of_movedStar_eq_pair m wd first second hStar with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by rw [h1, hLeft], by rw [h2, hRight]⟩
  · exact Or.inr ⟨by rw [h1, hRight], by rw [h2, hLeft]⟩

/-- **Under (H-BaseI)'s orientation `A₁` sits at `graph.vert m.base`.** -/
theorem vtx_leftBranch (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p) :
    wd.tracks.iso.vtx (leftBranch m wd hEnds) = graph.vert m.base := by
  have h : (IncomingPairing.baseDart m wd).1 = leftBranch m wd hEnds := Subtype.ext hLeft
  rw [← h]
  exact IncomingPairing.vtx_baseDart m wd

/-- **Under (H-BaseI)'s orientation `A₂` sits at `graph.vert (graph.op m.base)`.** -/
theorem vtx_rightBranch (hEnds : AnchorEnds m wd anchorBlk p q)
    (hRight : (IncomingPairing.opBaseDart m wd).1.1 = q) :
    wd.tracks.iso.vtx (rightBranch m wd hEnds) = graph.vert (graph.op m.base) := by
  have h : (IncomingPairing.opBaseDart m wd).1 = rightBranch m wd hEnds := Subtype.ext hRight
  rw [← h]
  exact IncomingPairing.vtx_opBaseDart m wd

/-- **`A₁` goes to `graph.vert m.base`.** -/
theorem vertexEquiv_anchor_false (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p) :
    vertexEquiv m wd thickSheet thinSheet setup hGauged hOrd hEnds
        (candBranchMap setup hGauged (Sum.inr false)) = graph.vert m.base := by
  rw [vertexEquiv_anchor m wd thickSheet thinSheet setup hGauged hOrd hEnds false]
  exact vtx_leftBranch m wd hEnds hLeft

/-- **`A₂` goes to `graph.vert (graph.op m.base)`.** -/
theorem vertexEquiv_anchor_true (hEnds : AnchorEnds m wd anchorBlk p q)
    (hRight : (IncomingPairing.opBaseDart m wd).1.1 = q) :
    vertexEquiv m wd thickSheet thinSheet setup hGauged hOrd hEnds
        (candBranchMap setup hGauged (Sum.inr true)) = graph.vert (graph.op m.base) := by
  rw [vertexEquiv_anchor m wd thickSheet thinSheet setup hGauged hOrd hEnds true]
  exact vtx_rightBranch m wd hEnds hRight

/-! ## 5.  The off-wall dart half, and the link -/

/-- **Away from the two anchor ends the Whitehead move does not change the
star.**  `NonTrivalentValencyTwoTracks.move_vert_eq_iff_of_ne` and
`card_star_eq_incidenceCount`, combined under (H-BaseI)'s orientation. -/
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

/-- **`OuterWalk.TypeChangeLink` at a valency-two Base I wall from the star count
alone.**  `NonTrivalentValencyTwoBaseOneExit.typeChangeLink_of_receipts_baseOne`
has one hypothesis, `tracks`; `MovedIncidenceIso` reduces it to a branch-vertex
bijection and a star count against the *permuted* vertex map.  With
`vertexEquiv` supplying the bijection, exactly one geometric hypothesis is
left, `hIncidence`; `hOp` is free from the
incoming tracking through `MovedIncidenceIso.label_op_of_tracks`. -/
def typeChangeLink_of_incidence (hEnds : AnchorEnds m wd anchorBlk p q)
    (hIncidence : ∀ (v : BranchVertex (validCandidate setup).datum)
        (r : StablePath (validCandidate setup).datum),
      incidenceCount (validCandidate setup).datum v.1 r =
        Nat.card {d : D // graph.vert (m.perm d) =
            vertexEquiv m wd thickSheet thinSheet setup hGauged hOrd hEnds v ∧
          label d = (NonTrivalentValencyTwoBaseOneExit.wallOutgoingFD m wd wallStar anchorBlk
            thickSheet thinSheet labelling₀ setup hGauged hOrd hRowVal
            hMatrixWall).labelling.row r}) :
    TypeChangeLink m wd :=
  NonTrivalentValencyTwoBaseOneExit.typeChangeLink_of_receipts_baseOne m wd wallStar anchorBlk
    thickSheet thinSheet labelling₀ setup hGauged hOrd hRowVal hMatrixWall
    (MovedIncidenceIso.tracksOfMovedIncidence _ _ graph m label
      (vertexEquiv m wd thickSheet thinSheet setup hGauged hOrd hEnds)
      (MovedIncidenceIso.label_op_of_tracks _ wd.fullDim wd.tracks) hIncidence)

/-- **`OuterWalk.TypeChangeLink` at a valency-two Base I wall, from one star
count.**  The incoming `2 + 2` / `1 + 3` / `3 + 1` trichotomy is discharged
internally by `NonTrivalentValencyTwoTracksLeaf.exists_anchorEnds`; what the
caller supplies is the star count against the branch-vertex bijection this
theorem hands back, and against the outgoing Base I presentation
`NonTrivalentValencyTwoBaseOneExit.wallOutgoingFD`. -/
theorem exists_typeChangeLink_of_incidence_baseOne
    (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk) :
    ∃ ve : BranchVertex (validCandidate setup).datum ≃ V,
      (∀ (v : BranchVertex (validCandidate setup).datum)
          (r : StablePath (validCandidate setup).datum),
        incidenceCount (validCandidate setup).datum v.1 r =
          Nat.card {d : D // graph.vert (m.perm d) = ve v ∧
            label d = (NonTrivalentValencyTwoBaseOneExit.wallOutgoingFD m wd wallStar anchorBlk
              thickSheet thinSheet labelling₀ setup hGauged hOrd hRowVal
              hMatrixWall).labelling.row r}) → Nonempty (TypeChangeLink m wd) := by
  obtain ⟨p, q, hEnds⟩ := NonTrivalentValencyTwoTracksLeaf.exists_anchorEnds m wd src hOrd
  exact ⟨vertexEquiv m wd thickSheet thinSheet setup hGauged hOrd hEnds, fun hInc ↦
    ⟨typeChangeLink_of_incidence m wd thickSheet thinSheet setup hGauged hOrd labelling₀
      hRowVal hMatrixWall hEnds hInc⟩⟩

end Link

/-! ## 6.  Non-vacuity: the orientation clause, and (H-BaseI) in relative form -/

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

theorem baseDart_edge_ne_crossLift (side dir : Bool) :
    (IncomingPairing.baseDart m wd).2.1 ≠
      crossLift m wd thickSheet thinSheet setup side dir := by
  intro hBad
  refine crossLift_stablePath_ne_facetRow m wd thickSheet thinSheet setup side dir ?_
  rw [← hBad]
  exact stablePath_baseDart m wd

theorem opBaseDart_edge_ne_crossLift (side dir : Bool) :
    (IncomingPairing.opBaseDart m wd).2.1 ≠
      crossLift m wd thickSheet thinSheet setup side dir := by
  intro hBad
  refine crossLift_stablePath_ne_facetRow m wd thickSheet thinSheet setup side dir ?_
  rw [← hBad]
  exact stablePath_opBaseDart m wd

/-- **The geometric content of a type change at a Base I wall**: the two
survivors the prescribed cross pairing brings together at `A₁` lift to
occurrences at the two **different** anchor ends of the vanishing row.  Without
it the `A₁` end sees exactly the star it already had and no Whitehead move takes
place.  It is a named hypothesis, in the style of
`StablePathFacetContraction.NoContractedReturn`. -/
def BaseOneSeparated (p q : wd.cover.SourceVertex) : Prop :=
  Incident wd.cover (crossLift m wd thickSheet thinSheet setup false false).1 p ∧
    Incident wd.cover (crossLift m wd thickSheet thinSheet setup false true).1 q

/-- A third surviving occurrence at the `A₁` end, distinct from the vanishing
row's occurrence there and from the cross-paired survivor. -/
theorem exists_thirdEdge (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hSep : BaseOneSeparated m wd thickSheet thinSheet setup p q) :
    ∃ e : NonDanglingEdge wd.cover, Incident wd.cover e.1 p ∧
      e ≠ (IncomingPairing.baseDart m wd).2.1 ∧
      e ≠ crossLift m wd thickSheet thinSheet setup false false := by
  classical
  have hNd : nonDanglingValency wd.cover p = 3 := by
    have h1 := hEnds.2.1
    have h2 : nonDanglingValency wd.cover p ≤ 3 := wd.fullDim.trivalent p
    omega
  have hIncBase : Incident wd.cover (IncomingPairing.baseDart m wd).2.1.1 p := by
    rw [← hLeft]
    exact (IncomingPairing.baseDart m wd).2.2
  have hNe : (IncomingPairing.baseDart m wd).2.1.1 ≠
      (crossLift m wd thickSheet thinSheet setup false false).1 := by
    intro hBad
    exact baseDart_edge_ne_crossLift m wd thickSheet thinSheet setup false false
      (Subtype.ext hBad)
  set pair : Finset wd.cover.SourceEdge :=
    {(IncomingPairing.baseDart m wd).2.1.1,
      (crossLift m wd thickSheet thinSheet setup false false).1} with hpair
  have hsub : pair ⊆ nonDanglingIncident wd.cover p := by
    intro e he
    rw [hpair] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨(IncomingPairing.baseDart m wd).2.1.2, hIncBase⟩
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨(crossLift m wd thickSheet thinSheet setup false false).2, hSep.1⟩
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

/-- The third occurrence at the `A₁` end. -/
def thirdEdge (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hSep : BaseOneSeparated m wd thickSheet thinSheet setup p q) : NonDanglingEdge wd.cover :=
  Classical.choose (exists_thirdEdge m wd thickSheet thinSheet setup hEnds hLeft hSep)

theorem thirdEdge_spec (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hSep : BaseOneSeparated m wd thickSheet thinSheet setup p q) :
    Incident wd.cover (thirdEdge m wd thickSheet thinSheet setup hEnds hLeft hSep).1 p ∧
      thirdEdge m wd thickSheet thinSheet setup hEnds hLeft hSep ≠
        (IncomingPairing.baseDart m wd).2.1 ∧
      thirdEdge m wd thickSheet thinSheet setup hEnds hLeft hSep ≠
        crossLift m wd thickSheet thinSheet setup false false :=
  Classical.choose_spec (exists_thirdEdge m wd thickSheet thinSheet setup hEnds hLeft hSep)

/-- The dart of the cross-paired `t₂`-survivor at the `A₁` end. -/
def selectedDartLeft (hEnds : AnchorEnds m wd anchorBlk p q)
    (hSep : BaseOneSeparated m wd thickSheet thinSheet setup p q) :
    StableSourceDarts.Dart wd.cover :=
  ⟨leftBranch m wd hEnds, ⟨crossLift m wd thickSheet thinSheet setup false false, hSep.1⟩⟩

/-- The dart of the cross-paired `t₃`-survivor at the `A₂` end. -/
def selectedDartRight (hEnds : AnchorEnds m wd anchorBlk p q)
    (hSep : BaseOneSeparated m wd thickSheet thinSheet setup p q) :
    StableSourceDarts.Dart wd.cover :=
  ⟨rightBranch m wd hEnds, ⟨crossLift m wd thickSheet thinSheet setup false true, hSep.2⟩⟩

/-- The remaining dart at the `A₁` end. -/
def thirdDart (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hSep : BaseOneSeparated m wd thickSheet thinSheet setup p q) :
    StableSourceDarts.Dart wd.cover :=
  ⟨leftBranch m wd hEnds, ⟨thirdEdge m wd thickSheet thinSheet setup hEnds hLeft hSep,
    (thirdEdge_spec m wd thickSheet thinSheet setup hEnds hLeft hSep).1⟩⟩

/-- **The Whitehead move prescribed by the cross pair at `A₁`.**  It contracts
the *same* edge as `m` and exchanges the cross-paired survivor at the `A₂` end
with the remaining dart at the `A₁` end. -/
def prescribedMove (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hRight : (IncomingPairing.opBaseDart m wd).1.1 = q)
    (hSep : BaseOneSeparated m wd thickSheet thinSheet setup p q) : graph.MoveData where
  base := m.base
  left := wd.tracks.iso.dart (thirdDart m wd thickSheet thinSheet setup hEnds hLeft hSep)
  right := wd.tracks.iso.dart (selectedDartRight m wd thickSheet thinSheet setup hEnds hSep)
  nonloop := m.nonloop
  left_vert :=
    (wd.tracks.iso.vert_map (thirdDart m wd thickSheet thinSheet setup hEnds hLeft hSep)).trans
      (vtx_leftBranch m wd hEnds hLeft)
  left_ne := by
    intro hBad
    exact (thirdEdge_spec m wd thickSheet thinSheet setup hEnds hLeft hSep).2.1
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1)
        (wd.tracks.iso.dart.injective
          (hBad.trans (IncomingPairing.dart_baseDart m wd).symm)))
  right_vert :=
    (wd.tracks.iso.vert_map (selectedDartRight m wd thickSheet thinSheet setup hEnds hSep)).trans
      (vtx_rightBranch m wd hEnds hRight)
  right_ne := by
    intro hBad
    exact (opBaseDart_edge_ne_crossLift m wd thickSheet thinSheet setup false true)
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1)
        (wd.tracks.iso.dart.injective
          (hBad.trans (IncomingPairing.dart_opBaseDart m wd).symm))).symm

/-- **Non-vacuity of (H-BaseI), in relative form.**  At a wall whose vanishing
row is oriented with its `A₁` end at `graph.vert m.base` and whose two
cross-paired survivors sit at the two different anchor ends, the Whitehead move
`prescribedMove` -- which contracts the *same* edge as `m` -- satisfies
(H-BaseI).  An absolute `∃ m, PrescribedBaseOneMove m wd …` does not typecheck:
`wd : WallData arrival` with
`arrival : FacetArrival deg graph label (label m.base)` fixes `m.base`, so the
witness has to be produced with that same `base` field. -/
theorem prescribedBaseOneMove_prescribedMove (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hRight : (IncomingPairing.opBaseDart m wd).1.1 = q)
    (hSep : BaseOneSeparated m wd thickSheet thinSheet setup p q) :
    PrescribedBaseOneMove
      (prescribedMove m wd thickSheet thinSheet setup hEnds hLeft hRight hSep) wd
      thickSheet thinSheet setup p q := by
  classical
  set m' := prescribedMove m wd thickSheet thinSheet setup hEnds hLeft hRight hSep with hm'
  set dLeft := selectedDartLeft m wd thickSheet thinSheet setup hEnds hSep with hdLeft
  set dRight := selectedDartRight m wd thickSheet thinSheet setup hEnds hSep with hdRight
  have hLeftNeRight : dLeft ≠ dRight := by
    intro hBad
    exact hEnds.1 (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.1.1) hBad)
  have hLeftNeThird :
      dLeft ≠ thirdDart m wd thickSheet thinSheet setup hEnds hLeft hSep := by
    intro hBad
    exact (thirdEdge_spec m wd thickSheet thinSheet setup hEnds hLeft hSep).2.2
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1) hBad).symm
  have hBaseNeLeft : m.base ≠ wd.tracks.iso.dart dLeft := by
    intro hBad
    exact (baseDart_edge_ne_crossLift m wd thickSheet thinSheet setup false false)
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
gives the orientation clause
of (H-BaseI), with `p`, `q` the two ends of the single vanishing occurrence. -/
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
`NonTrivalentValencyTwoTracksLeaf` gives the
orientation clause of (H-BaseI), with `p`, `q` the two *outer* ends of the
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

/-! ### (H-BaseI) is a condition on rows only -/

/-- **The move always places with `m.base` one dart at each anchor end**, other
than the two darts of the vanishing row: `IncomingPairing.exists_movedStar_darts`
read under the orientation clause of (H-BaseI). -/
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

/-- **The dispatcher can always discharge (H-BaseI).**  Because the pair a move
names straddles the two anchor ends, the only thing left to check is that the
two darts it names carry the *rows* of the cross pair: that is the whole content
of the row-level condition, and it is exactly what the move-to-type dispatcher
needs. -/
theorem prescribedBaseOneMove_of_rows
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hRight : (IncomingPairing.opBaseDart m wd).1.1 = q)
    (hRows : ∀ x y : StableSourceDarts.Dart wd.cover, x.1.1 = p → y.1.1 = q →
      (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
          {wd.tracks.iso.dart x, wd.tracks.iso.dart y} →
      x.2.1.stablePath = (crossLift m wd thickSheet thinSheet setup false false).stablePath ∧
        y.2.1.stablePath =
          (crossLift m wd thickSheet thinSheet setup false true).stablePath) :
    PrescribedBaseOneMove m wd thickSheet thinSheet setup p q := by
  obtain ⟨x, y, hx, hy, -, -, hStar⟩ :=
    exists_movedStar_darts_at_ends m wd hLeft hRight
  obtain ⟨hFirst, hSecond⟩ := hRows x y hx hy hStar
  exact ⟨⟨hLeft, hRight⟩, x, y, hFirst, hSecond, hStar⟩

end NonVacuity

end Wall

end

end DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneTracks
