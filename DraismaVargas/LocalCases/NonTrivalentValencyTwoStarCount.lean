module

public import DraismaVargas.LocalCases.NonTrivalentValencyTwoTracks
public import DraismaVargas.LocalCases.WallSplitIncidenceOrdinary
public import DraismaVargas.LocalCases.NonTrivalentValencyThreeStarCount

@[expose] public section

/-!
# The valency-two Base II star count, and the link under (H-II)

Source: Vargas, Part II, arXiv:2609.09109, Section 5.1 (a combinatorial type change is a Whitehead
move on the *ambient* tracked graph, with the labelling convention (1): the
contracting occurrence `h_1` has two trivalent ends) and Section 5.4 (case
`{v2-nd4}`, Base II = base tree `T_2`; the Configuration A `2 + 2` subcases and
the Configuration B `3 + 1` subcases), together with Draisma–Vargas Part I, arXiv:1909.12924 (the
stable graph `H(M)` and its row labels) and the non-dangling valency formula
`lemma-ndval-of-GqA0`.

This is the valency-two analogue of `NonTrivalentValencyThreeStarCount`.
`NonTrivalentValencyTwoTracks` reduces `OuterWalk.TypeChangeLink` at a
two-valent Base II wall to **one** geometric input, the star count `hIncidence`
of `typeChangeLink_of_incidence`.  This module proves that count under
(H-II) = `NonTrivalentValencyTwoTracks.PrescribedMergedMove`, and hence
delivers the link.

## What is proved

### 1.  (T1) at an ordinary wall block -- different from valency three

At a two-valent wall the outgoing base tree *subdivides* the wall vertex, so an
ordinary wall block `B` is split into two endpoint vertices, one per side of the
new target occurrence.  Section 0 of `NonTrivalentValencyTwoTracks` does the
valency bookkeeping: the side `!NonTrivalentValencyTwoRowEquiv.ordSide` keeps
the whole surviving valency of `B` and the other side is at most divalent.  The
identity is therefore stated at the `branchSide` vertex, not at a single
retained one.

* `card_ordinaryStar_ordSide_le`, `card_ordinaryStar_ordSide_le_one`: the
  `ordSide` side of a trivalent ordinary block carries at most one survivor.
* `branchEndEdge`, `branchEnd`, `stablePath_branchEnd`, `incident_branchEnd`:
  the representative at the `branchSide` vertex of a survivor of `B` -- the
  retained copy when the base tree assigns its target to that side, and `B`'s own
  new occurrence when it assigns it to the other one, which by
  `stablePath_retainedEdge_eq_newSourceEdge` sits on the retained row of that
  lone survivor.
* `incidenceCount_endpointVertex_branchSide_ordinary`: **the `branchSide` vertex
  keeps the block's whole row-filtered star**, with the two-sided census of
  `NonTrivalentValencyTwoDescent`
  (`nonDanglingIncident_endpointVertex_of_new_dangling` / `..._of_new_survives`,
  packaged as `mem_nonDanglingIncident_endpointVertex_ordinary`) for
  surjectivity and `injective_retainedRow` for the row filter.
* `incidenceCount_candVertex`: (T1) at every wall-datum vertex other than the
  anchor -- the ordinary-block case above, and
  `NonTrivalentValencyTwoTracks.incidenceCount_retainedVertex_retainedRow` off
  the merged target vertex.

### 2.  (T2) at an ordinary wall block

* `internalEdges_subsingleton_of_ne_anchor`: **an ordinary wall block is
  unramified**, hence its pruned fibre carries at most one internal occurrence.
  Part II `lemma-above-w0` at valency two
  (`NonTrivalentValencyTwoRigidity.localRamification_eq_zero_of_ne_anchor`, whose
  input is `NonTrivalentValencyTwoRows.nonDanglingValency_anchor`), then the
  valency-agnostic `NonTrivalentValencyThreeRigidity.localRamification_eq_zero_in_fibre`
  and `...internalEdges_subsingleton`.
* `incidenceCount_wall_eq_incoming`: (T2) at every wall-datum vertex other than
  the anchor, from `WallSplitIncidenceOrdinary.incidenceCount_unramified`.

### 3.  The chart rows of the outgoing presentation

`outFD_row_retained` and `outFD_row_bridge`: a retained row of
`NonTrivalentValencyTwoExit.wallOutgoingFD` keeps the chart coordinate of its own
incoming row, and the bridge row occupies the vanishing coordinate `label m.base`.
(The valency-three exit exports these two; the valency-two exit exports only
`outLabelling_row_symm_facet`, so they are derived here from `rowChart_some`,
`wallLab_row_val` and `NonTrivalentValencyTwoRowEquiv.labelling_row_*`.)

### 4.  The star count

* `incidence_inl_retained`, `incidence_inl_bridge`: away from the anchor.  On a
  retained row the count is (T1) then (T2) then
  `NonTrivalentValencyTwoTracks.card_star_eq_incidenceCount`, with
  `move_vert_eq_iff_of_ne` erasing the move; on the bridge row both sides
  vanish -- downstairs `h_1` joins `A_u` to `A_v` (`bridgeEdge_isolated`,
  `sourceEnds_bridgeEdge`), upstairs the vanishing chart row is the single
  occurrence `h_1` (`eq_facetEdge`).
* `incidence_inr_false_retained`, `incidence_inr_false_bridge`: **at `A_u`.**
  The exact star `{h_1, e_first, e_second}`
  (`NonTrivalentValencyTwoRows.nonDanglingIncident_endpointVertex_false`, read on
  surviving occurrences as `incidentEdges_endpointVertex_false`) is matched dart
  by dart with the moved star that (H-II) prescribes (`filter_moved_base`,
  `dart_ne`).  `outFD_row_bridge` puts the bridge row on `label m.base`,
  `incomingRow_ne_facet` keeps every retained row off it, and
  `label_dart_merged_iff` identifies the two remaining darts -- from the **row**
  equality of (H-II) alone (`IncomingPairing.label_dart_of_row`), which is all
  the count needs and all a pass-through survivor can give.
* `incidence_inr_true`: **at `A_v`, from the leftover equation.**  A stable row
  of the candidate meets its branch vertices twice in all
  (`sum_incidenceCount_branchVertex`, from `StableSourceDarts.card_row`), a chart
  row carries exactly two darts of the tracked graph (`card_filter_label`,
  `sum_natCard_moved`), and `vertexEquiv` is a bijection; the count agrees at
  every other branch vertex, so it agrees at `A_v`.
* `incidence_of_prescribedMergedMove`: the star count at every branch vertex and
  every row, and `typeChangeLink_of_prescribedMergedMove`:
  **`OuterWalk.TypeChangeLink` at a two-valent Base II wall from (H-II) alone.**

## The hypotheses that remain explicit

1. `hPres : NonTrivalentValencyTwoTracks.PrescribedMergedMove m wd hNoReturn sel`,
   i.e. (H-II), at row level: the two darts the move places with `m.base`
   carry the rows of the two merged survivors.  `NonTrivalentValencyTwoTracks`
   supplies its relative non-vacuity witness
   `prescribedMergedMove_prescribedMove` from `MergedSeparated` and the
   orientation clause, and the dispatcher's producer
   `prescribedMergedMove_of_rows`; neither is derived here.
2. `hNoReturn : StablePathFacetContraction.NoContractedReturn wd.cover wd.contracted`,
   `wallStar : W2R1Target.TwoStar (contract wd.coverTarget wd.hab wd.hOne)
   <wd.a, wd.hab>`, `src`, `sel` and `hOrd` -- exactly the five carried by
   `NonTrivalentValencyTwoTracks.typeChangeLink_of_incidence`,
   `NonTrivalentValencyTwoExit.wallOutgoingFD` and
   `WallDatumPathEnds.typeChangeLink_of_receipts'`.  `hNoReturn` is
   `NonTrivalentValencyTwoExit.noContractedReturn_of_two_two` in the `2 + 2`
   sub-case and is genuinely false at a `1 + 3` leaf wall, which is why the
   headline is stated with that binder (`NonTrivalentValencyTwoStarCountAll`
   removes it); `src`, `hOrd` and the candidate's validity come with no further
   hypothesis from `NonTrivalentValencyTwoExit.exists_anchor_of_wallData`.  The
   valency dispatcher of `OuterWalk.WallData.valency` is not built here.
3. Nothing else: `hPathEnds` is supplied by `WallDatumPathEnds`, and the
   branch-vertex bijection and the vertex dictionary are
   `NonTrivalentValencyTwoTracks.candBranchEquiv` / `vertexEquiv`.

No structure is introduced.  Every definition (`branchEndEdge`, `branchEnd`,
`mergedWall`, `mergedRetained`, `bridgeND`) is a named occurrence of an object
already built, and each is applied in the theorems above.  The ordinary-block
section is generic in the wall block and free of `hNoReturn`, `m` and `wd`, so
`NonTrivalentValencyTwoTracksLeaf` reuses it verbatim at the `1 + 3` leaf walls.

## Consumers

`OuterWalk.TypeChangeLink` at Part II case `{v2-nd4}`, Base II, hence the `link`
hypothesis of `OuterWalk.coneEntry_of_reaches`, once the valency dispatcher
supplies `wallStar` and the walk supplies (H-II).
`NonTrivalentValencyTwoTracksLeaf` ports the ordinary-block and dart-side lemmas
to the `1 + 3` leaf walls.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoStarCount

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.StablePathCount
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRows
open DraismaVargas.LocalCases.NonTrivalentValencyTwoDescent
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRowEquiv

noncomputable section

/-! ## 1.  (T1) at an ordinary wall block -/

section Ordinary

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

variable {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall}
  (source : TwoBranchAnchor data star anchor)
  (sel : Prescribed.Selection data star anchor)
  (hValid : data.Valid)
  (hOrd : OrdinaryTrivalent data wall anchor)

local notation "cand" => (Prescribed.validCandidate sel)

include hOrd in
/-- **The retained-row map is injective**, from the row dictionary
`NonTrivalentValencyTwoRowEquiv.rowEquiv`. -/
theorem injective_retainedRow :
    Function.Injective (NonTrivalentValencyTwoDescent.retainedRow source sel hValid) := by
  intro r r' h
  have h2 := congrArg (rowEquiv source sel hValid hOrd) h
  rw [rowEquiv_retainedRow source sel hValid hOrd r,
    rowEquiv_retainedRow source sel hValid hOrd r'] at h2
  exact Option.some_injective _ h2

include hOrd in
/-- A retained row is never the bridge row. -/
theorem retainedRow_ne_bridgeRow (r : StablePath data) :
    NonTrivalentValencyTwoDescent.retainedRow source sel hValid r ≠
      bridgeRow source sel hValid := by
  intro hBad
  have h := congrArg (rowEquiv source sel hValid hOrd) hBad
  rw [rowEquiv_retainedRow source sel hValid hOrd r,
    rowEquiv_bridgeRow source sel hValid hOrd] at h
  exact Option.some_ne_none r h

/-! ### The two sides of an ordinary wall block -/

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
theorem newSourceEdge_survives_of_mem_ordSide {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) {old : data.SourceEdge}
    (hOld : old ∈ ordinaryStar data star anchor x (ordSide data star anchor x)) :
    ¬ IsDangling (cand).datum ((cand).newSourceEdge x) := by
  classical
  have hPos : 0 < (ordinaryStar data star anchor x (ordSide data star anchor x)).card :=
    Finset.card_pos.mpr ⟨old, hOld⟩
  have hLeSide := card_ordinaryStar_ordSide_le (data := data) (star := star) (anchor := anchor) x
  refine (newSourceEdge_survives_iff_ordinary sel hValid hX).mpr ?_
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

/-- The representative, at the `branchSide` endpoint `!ordSide` of an ordinary
wall block, of a surviving occurrence of that block: the retained copy of the
occurrence itself when the base tree assigns its target to that side, and the
block's own new occurrence when it assigns it to the other one. -/
def branchEndEdge (x : Fin degree) (e : NonDanglingEdge data) : (cand).datum.SourceEdge :=
  if Prescribed.rightAssignment data star anchor e.1.1.1 = !ordSide data star anchor x then
    (cand).oldSourceEdge e.1
  else (cand).newSourceEdge x

include hValid in
theorem branchEndEdge_survives {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) (e : NonDanglingEdge data)
    (hInc : Incident data e.1 (data.sourceEndpoint wall x)) :
    ¬ IsDangling (cand).datum (branchEndEdge sel x e) := by
  classical
  unfold branchEndEdge
  by_cases hs : Prescribed.rightAssignment data star anchor e.1.1.1 =
      !ordSide data star anchor x
  · rw [ite_eq_left hs]
    exact ResolutionSurvival.not_isDangling_oldSourceEdge (cand) hValid.1 e.1 e.2
  · rw [ite_eq_right hs]
    have hs' : Prescribed.rightAssignment data star anchor e.1.1.1 =
        ordSide data star anchor x := by
      revert hs
      cases ordSide data star anchor x <;>
        cases Prescribed.rightAssignment data star anchor e.1.1.1 <;> simp
    exact newSourceEdge_survives_of_mem_ordSide sel hValid hX
      ((mem_ordinaryStar e.1).mpr ⟨⟨e.2, hInc⟩, hs'⟩)

include hValid in
/-- The same representative, as a surviving occurrence of the candidate. -/
def branchEnd {x : Fin degree} (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (e : NonDanglingEdge data) (hInc : Incident data e.1 (data.sourceEndpoint wall x)) :
    NonDanglingEdge (cand).datum :=
  ⟨branchEndEdge sel x e, branchEndEdge_survives sel hValid hX e hInc⟩

theorem stablePath_branchEnd {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hLe : nonDanglingValency data (data.sourceEndpoint wall x) ≤ 3)
    (e : NonDanglingEdge data) (hInc : Incident data e.1 (data.sourceEndpoint wall x)) :
    (branchEnd sel hValid hX e hInc).stablePath =
      NonTrivalentValencyTwoDescent.retainedRow source sel hValid e.stablePath := by
  classical
  rw [NonTrivalentValencyTwoDescent.retainedRow_mk source sel hValid e]
  by_cases hs : Prescribed.rightAssignment data star anchor e.1.1.1 =
      !ordSide data star anchor x
  · refine congrArg NonDanglingEdge.stablePath (Subtype.ext ?_)
    show branchEndEdge sel x e = (cand).oldSourceEdge e.1
    unfold branchEndEdge
    rw [ite_eq_left hs]
  · have hs' : Prescribed.rightAssignment data star anchor e.1.1.1 =
        ordSide data star anchor x := by
      revert hs
      cases ordSide data star anchor x <;>
        cases Prescribed.rightAssignment data star anchor e.1.1.1 <;> simp
    have hOld : e.1 ∈ ordinaryStar data star anchor x (ordSide data star anchor x) :=
      (mem_ordinaryStar e.1).mpr ⟨⟨e.2, hInc⟩, hs'⟩
    have hSurv := newSourceEdge_survives_of_mem_ordSide sel hValid hX hOld
    have hCard : (ordinaryStar data star anchor x (ordSide data star anchor x)).card = 1 := by
      have hPos : 0 < (ordinaryStar data star anchor x (ordSide data star anchor x)).card :=
        Finset.card_pos.mpr ⟨e.1, hOld⟩
      have hLeOne := card_ordinaryStar_ordSide_le_one (data := data) (star := star)
        (anchor := anchor) (x := x) hLe
      omega
    rw [stablePath_retainedEdge_eq_newSourceEdge sel hValid _ hX hOld hCard hSurv]
    refine congrArg NonDanglingEdge.stablePath (Subtype.ext ?_)
    show branchEndEdge sel x e = (cand).newSourceEdge x
    unfold branchEndEdge
    rw [ite_eq_right hs]

theorem incident_branchEnd {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) (e : NonDanglingEdge data)
    (hInc : Incident data e.1 (data.sourceEndpoint wall x)) :
    Incident (cand).datum (branchEnd sel hValid hX e hInc).1
      (endpointVertex sel (!ordSide data star anchor x) x) := by
  classical
  by_cases hs : Prescribed.rightAssignment data star anchor e.1.1.1 =
      !ordSide data star anchor x
  · have hVal : (branchEnd sel hValid hX e hInc).1 = (cand).oldSourceEdge e.1 := by
      show branchEndEdge sel x e = _
      unfold branchEndEdge
      rw [ite_eq_left hs]
    rw [hVal]
    exact (incident_oldSourceEdge_endpointVertex_iff sel _ hX e.1).mpr ⟨hInc, hs⟩
  · have hVal : (branchEnd sel hValid hX e hInc).1 = (cand).newSourceEdge x := by
      show branchEndEdge sel x e = _
      unfold branchEndEdge
      rw [ite_eq_right hs]
    rw [hVal]
    exact newSourceEdge_incident_endpointVertex sel _ x

include hOrd in
/-- **(T1) at an ordinary wall block.**  At a two-valent wall the outgoing base
tree subdivides the wall vertex, so an ordinary wall block `B` is split in two;
the `branchSide` endpoint `!ordSide` keeps the block's whole row-filtered star.
The bijection sends a survivor whose target lies on that side to its retained
copy, and the at most one survivor on the other side to `B`'s new occurrence,
which sits on that survivor's own retained row. -/
theorem incidenceCount_endpointVertex_branchSide_ordinary {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hLe : nonDanglingValency data (data.sourceEndpoint wall x) ≤ 3)
    (row : StablePath data) :
    incidenceCount data (data.sourceEndpoint wall x) row =
      incidenceCount (cand).datum
        (endpointVertex sel (!ordSide data star anchor x) x)
        (NonTrivalentValencyTwoDescent.retainedRow source sel hValid row) := by
  classical
  unfold incidenceCount
  refine Finset.card_bij (fun e he ↦ branchEnd sel hValid hX e
    ((mem_incidentEdges _ _ _).mp (Finset.mem_filter.mp he).1)) ?_ ?_ ?_
  · intro e he
    obtain ⟨hMem, hRow⟩ := Finset.mem_filter.mp he
    refine Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr
      (incident_branchEnd sel hValid hX e _), ?_⟩
    rw [stablePath_branchEnd source sel hValid hX hLe e _, hRow]
  · intro e₁ he₁ e₂ he₂ hEq
    have hInc₁ := (mem_incidentEdges _ _ _).mp (Finset.mem_filter.mp he₁).1
    have hInc₂ := (mem_incidentEdges _ _ _).mp (Finset.mem_filter.mp he₂).1
    have hVal : branchEndEdge sel x e₁ = branchEndEdge sel x e₂ := congrArg Subtype.val hEq
    unfold branchEndEdge at hVal
    by_cases hs₁ : Prescribed.rightAssignment data star anchor e₁.1.1.1 =
        !ordSide data star anchor x <;>
      by_cases hs₂ : Prescribed.rightAssignment data star anchor e₂.1.1.1 =
        !ordSide data star anchor x
    · rw [ite_eq_left hs₁, ite_eq_left hs₂] at hVal
      exact Subtype.ext (ResolutionCut.oldSourceEdge_injective (cand) hVal)
    · rw [ite_eq_left hs₁, ite_eq_right hs₂] at hVal
      exact absurd hVal.symm (newSourceEdge_ne_oldSourceEdge sel x e₁.1)
    · rw [ite_eq_right hs₁, ite_eq_left hs₂] at hVal
      exact absurd hVal (newSourceEdge_ne_oldSourceEdge sel x e₂.1)
    · have hs₁' : Prescribed.rightAssignment data star anchor e₁.1.1.1 =
          ordSide data star anchor x := by
        revert hs₁
        cases ordSide data star anchor x <;>
          cases Prescribed.rightAssignment data star anchor e₁.1.1.1 <;> simp
      have hs₂' : Prescribed.rightAssignment data star anchor e₂.1.1.1 =
          ordSide data star anchor x := by
        revert hs₂
        cases ordSide data star anchor x <;>
          cases Prescribed.rightAssignment data star anchor e₂.1.1.1 <;> simp
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
        (endpointVertex sel (!ordSide data star anchor x) x) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨f.2, (mem_incidentEdges _ _ _).mp hMem⟩
    rcases (mem_nonDanglingIncident_endpointVertex_ordinary sel hValid _ hX f.1).mp hStar with
      ⟨old, hOld, hEq⟩ | ⟨hEq, hSurv⟩
    · obtain ⟨⟨hSurvOld, hIncOld⟩, hSide⟩ := (mem_ordinaryStar old).mp hOld
      have hValEq : branchEndEdge sel x ⟨old, hSurvOld⟩ = f.1 := by
        unfold branchEndEdge
        rw [ite_eq_left hSide]
        exact hEq.symm
      refine ⟨⟨old, hSurvOld⟩, ?_, Subtype.ext hValEq⟩
      refine Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr hIncOld, ?_⟩
      refine injective_retainedRow source sel hValid hOrd ?_
      rw [← stablePath_branchEnd source sel hValid hX hLe ⟨old, hSurvOld⟩ hIncOld]
      exact Eq.trans (congrArg NonDanglingEdge.stablePath (Subtype.ext hValEq)) hRow
    · obtain ⟨hFalse, hTrue⟩ := (newSourceEdge_survives_iff_ordinary sel hValid hX).mp hSurv
      have hNonempty : (ordinaryStar data star anchor x (ordSide data star anchor x)).Nonempty := by
        cases hCase : ordSide data star anchor x with
        | false => exact Finset.card_pos.mp (by omega)
        | true => exact Finset.card_pos.mp (by omega)
      obtain ⟨old, hOld⟩ := hNonempty
      obtain ⟨⟨hSurvOld, hIncOld⟩, hSide⟩ := (mem_ordinaryStar old).mp hOld
      have hSideNe : ¬ (Prescribed.rightAssignment data star anchor old.1.1 =
          !ordSide data star anchor x) := by
        rw [hSide]
        cases ordSide data star anchor x <;> simp
      have hValEq : branchEndEdge sel x ⟨old, hSurvOld⟩ = f.1 := by
        unfold branchEndEdge
        rw [ite_eq_right hSideNe]
        exact hEq.symm
      refine ⟨⟨old, hSurvOld⟩, ?_, Subtype.ext hValEq⟩
      refine Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr hIncOld, ?_⟩
      refine injective_retainedRow source sel hValid hOrd ?_
      rw [← stablePath_branchEnd source sel hValid hX hLe ⟨old, hSurvOld⟩ hIncOld]
      exact Eq.trans (congrArg NonDanglingEdge.stablePath (Subtype.ext hValEq)) hRow


end Ordinary

/-! ## 2.  The two transports at a wall of the outer walk -/

section Wall

open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.PrunedFibreValency
open DraismaVargas.LocalCases.PrunedFibreTree
open DraismaVargas.LocalCases.FullContractionFibre
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.ClassInjectivity
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk
open DraismaVargas.LocalCases.NonTrivalentValencyTwoTracks

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)
  {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hOrd : OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk)

include hOrd in
/-- **(T1), at every wall-datum vertex other than the anchor.**  Off the merged
target vertex this is `NonTrivalentValencyTwoTracks.incidenceCount_retainedVertex_retainedRow`; at
an ordinary wall block it is the `branchSide` census above. -/
theorem incidenceCount_candVertex
    (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hne : w ≠ anchorVertex m wd anchorBlk)
    (row : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (contractDatum wd.cover wd.hc wd.hab wd.hOne) w row =
      incidenceCount (Prescribed.validCandidate sel).datum
        (candVertex m wd sel w)
        (NonTrivalentValencyTwoDescent.retainedRow src sel (wallValid m wd) row) := by
  classical
  by_cases hw : w.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)
  · have hRel := not_rel_anchor_of_ne m wd w hw hne
    rw [candVertex_wall m wd sel w hw]
    simp only [branchSide]
    conv_lhs => rw [← sourceEndpoint_self m wd w hw]
    exact incidenceCount_endpointVertex_branchSide_ordinary src sel (wallValid m wd) hOrd
      hRel (hOrd w.1.2 hRel) row
  · rw [candVertex_away m wd sel w hw]
    exact incidenceCount_retainedVertex_retainedRow m wd src sel hOrd w hw row

/-- The injectivity of the incoming-row map, from the `2 + 2` wall's
`NoContractedReturn`. -/
theorem injective_incomingRow
    (hNoReturn : NoContractedReturn wd.cover wd.contracted) :
    Function.Injective (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
      (wd.hCompat m) (wd.hForest m)) :=
  WallSplitIncidence.injective_incomingRow_of_noContractedReturn wd.cover wd.fullDim wd.hc
    wd.hab wd.hOne (wd.hCompat m) (wd.hForest m) hNoReturn

include src in
/-- **An ordinary wall block is unramified**, so its pruned fibre carries at
most one internal occurrence: Part II `lemma-above-w0` at valency two
(`NonTrivalentValencyTwoRigidity.localRamification_eq_zero_of_ne_anchor`) says
the four-valent anchor consumes both units of available ramification. -/
theorem internalEdges_subsingleton_of_ne_anchor
    (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hne : w ≠ anchorVertex m wd anchorBlk) :
    ∀ e ∈ internalEdges wd.cover wd.hc wd.hab wd.hOne w,
      ∀ f ∈ internalEdges wd.cover wd.hc wd.hab wd.hOne w, e = f := by
  classical
  by_cases hw : w.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)
  · have hFixed : ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
        (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)).repr w.1.2 = w.1.2 := by
      have h := w.2
      rw [hw] at h
      exact h
    set blk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) := ⟨w.1.2, hFixed⟩ with hblk
    have hBlkVertex : WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) blk = w :=
      sourceEndpoint_self m wd w hw
    have hBlkNe : blk ≠ anchorBlk := by
      intro hBad
      exact hne (hBlkVertex.symm.trans (congrArg
        (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)) hBad))
    have hRamZero := NonTrivalentValencyTwoRigidity.localRamification_eq_zero_of_ne_anchor
      wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m) (wd.hCompat m) wallStar anchorBlk
      (NonTrivalentValencyTwoRows.nonDanglingValency_anchor src) blk hBlkNe
    set merged : (mergedPartition wd.cover wd.a wd.b).Blocks := ⟨w.1.2, by
      rw [← contractDatum_vertexPartition_merge wd.cover wd.hc wd.hab wd.hOne]
      exact hFixed⟩ with hmerged
    have hMergedVertex : mergedVertex wd.cover wd.hc wd.hab wd.hOne merged = w :=
      Subtype.ext (Prod.ext hw.symm rfl)
    refine NonTrivalentValencyThreeRigidity.internalEdges_subsingleton wd.cover wd.fullDim
      wd.hc wd.hab wd.hOne w ?_
    intro point hPoint
    exact NonTrivalentValencyThreeRigidity.localRamification_eq_zero_in_fibre wd.cover
      wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m) merged hRamZero point
      (hPoint.trans hMergedVertex.symm)
  · intro e he
    rw [NonTrivalentValencyThreeStarCount.internalEdges_eq_empty_of_away m wd w hw] at he
    exact absurd he (Finset.notMem_empty e)

include src hOrd in
/-- **(T2), at every wall-datum vertex other than the anchor.**  At an ordinary
wall block it is `WallSplitIncidenceOrdinary.incidenceCount_unramified`, whose
input is the vanishing ramification above. -/
theorem incidenceCount_wall_eq_incoming
    (hNoReturn : NoContractedReturn wd.cover wd.contracted)
    (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hne : w ≠ anchorVertex m wd anchorBlk)
    (u : wd.cover.SourceVertex)
    (hMapU : sourceVertexMap wd.cover wd.hc wd.hab wd.hOne u = w)
    (hThreeU : 3 ≤ nonDanglingValency wd.cover u)
    (row : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (contractDatum wd.cover wd.hc wd.hab wd.hOne) w row =
      incidenceCount wd.cover u (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
        (wd.hCompat m) (wd.hForest m) row) :=
  WallSplitIncidenceOrdinary.incidenceCount_unramified wd.cover wd.fullDim wd.hc wd.hab wd.hOne
    (wd.hCompat m) (wd.hForest m) (injective_incomingRow m wd hNoReturn) wd.fullDim.connected
    w u hMapU hThreeU (wallDatum_trivalent_away_anchor m wd hOrd w hne) wd.fullDim.trivalent
    (internalEdges_subsingleton_of_ne_anchor m wd src w hne) row

/-! ## 3.  The chart rows of the outgoing presentation -/

/-- A retained row of the outgoing presentation keeps the chart coordinate of
its own incoming row. -/
theorem outFD_row_retained
    (hNoReturn : NoContractedReturn wd.cover wd.contracted)
    (p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    (NonTrivalentValencyTwoExit.wallOutgoingFD m wd hNoReturn src sel hOrd
        (WallDatumPathEnds.hasPathEnds_wallData m wd hNoReturn src sel hOrd)).labelling.row
      (NonTrivalentValencyTwoDescent.retainedRow src sel (wallValid m wd) p) =
      wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
        (wd.hCompat m) (wd.hForest m) p) := by
  show (NonTrivalentValencyTwoExit.rowChart wd.cover wd.fullDim (label m.base)
      (contracted := wd.contracted))
      ((NonTrivalentValencyTwoRowEquiv.labelling src sel (wallValid m wd) hOrd
        (NonTrivalentValencyTwoExit.wallLab wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (wd.hForest m) hNoReturn wd.coordinates (label m.base) wd.hRows wd.hZeroCoord
          wd.hPosCoord wd.hFacetZero)).row
        (NonTrivalentValencyTwoDescent.retainedRow src sel (wallValid m wd) p)) = _
  rw [NonTrivalentValencyTwoRowEquiv.labelling_row_retained src sel (wallValid m wd) hOrd _ p,
    NonTrivalentValencyTwoExit.rowChart_some,
    NonTrivalentValencyTwoExit.wallLab_row_val wd.cover wd.fullDim wd.hc wd.hab wd.hOne
      (wd.hForest m) hNoReturn wd.coordinates (label m.base) wd.hRows wd.hZeroCoord
      wd.hPosCoord wd.hFacetZero p,
    Equiv.swap_comm (label m.base) (wd.fullDim.labelling.targetEdge.symm wd.contracted)]
  exact Equiv.swap_apply_self _ _ _

/-- The bridge row of the outgoing presentation occupies the vanishing chart
row `label m.base`. -/
theorem outFD_row_bridge
    (hNoReturn : NoContractedReturn wd.cover wd.contracted) :
    (NonTrivalentValencyTwoExit.wallOutgoingFD m wd hNoReturn src sel hOrd
        (WallDatumPathEnds.hasPathEnds_wallData m wd hNoReturn src sel hOrd)).labelling.row
      (NonTrivalentValencyTwoRowEquiv.bridgeRow src sel (wallValid m wd)) = label m.base := by
  show (NonTrivalentValencyTwoExit.rowChart wd.cover wd.fullDim (label m.base)
      (contracted := wd.contracted))
      ((NonTrivalentValencyTwoRowEquiv.labelling src sel (wallValid m wd) hOrd
        (NonTrivalentValencyTwoExit.wallLab wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (wd.hForest m) hNoReturn wd.coordinates (label m.base) wd.hRows wd.hZeroCoord
          wd.hPosCoord wd.hFacetZero)).row
        (NonTrivalentValencyTwoRowEquiv.bridgeRow src sel (wallValid m wd))) = label m.base
  rw [NonTrivalentValencyTwoRowEquiv.labelling_row_bridge src sel (wallValid m wd) hOrd _]
  rfl

/-! ## 4.  Away from the anchor -/

/-- Away from the two ends of the vanishing occurrence the moved star of a
chart row is the star of the incoming cover. -/
theorem natCard_moved_of_ne (hNoReturn : NoContractedReturn wd.cover wd.contracted)
    (u : BranchVertex wd.cover)
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd hNoReturn) = m.base)
    (hul : u.1 ≠ leftEnd m wd) (hur : u.1 ≠ rightEnd m wd)
    (row : StablePath wd.cover) :
    Nat.card {d : D // graph.vert (m.perm d) = wd.tracks.iso.vtx u ∧
        label d = wd.fullDim.labelling.row row} =
      incidenceCount wd.cover u.1 row := by
  have hNeBase : wd.tracks.iso.vtx u ≠ graph.vert m.base := by
    rw [vert_base_eq m wd hNoReturn hBase]
    intro hBad
    exact hul (congrArg Subtype.val (wd.tracks.iso.vtx.injective hBad))
  have hNeOp : wd.tracks.iso.vtx u ≠ graph.vert (graph.op m.base) := by
    rw [(vert_opBase_eq m wd hNoReturn hBase).2]
    intro hBad
    exact hur (congrArg Subtype.val (wd.tracks.iso.vtx.injective hBad))
  rw [card_star_eq_incidenceCount m wd u row]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun d ↦ and_congr_left'
    (move_vert_eq_iff_of_ne m hNeBase hNeOp d))

include hOrd in
/-- **The star count at a branch vertex away from the anchor, on a retained
row.**  It is (T1) followed by (T2) followed by the incoming tracking. -/
theorem incidence_inl_retained (hNoReturn : NoContractedReturn wd.cover wd.contracted)
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd hNoReturn) = m.base)
    (w : {w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
      w.1 ≠ anchorVertex m wd anchorBlk})
    (r₀ : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (Prescribed.validCandidate sel).datum
        (candBranchMap m wd src sel hOrd (Sum.inl w)).1
        (NonTrivalentValencyTwoDescent.retainedRow src sel (wallValid m wd) r₀) =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquiv m wd hNoReturn src sel hOrd
            (candBranchMap m wd src sel hOrd (Sum.inl w)) ∧
        label d = (NonTrivalentValencyTwoExit.wallOutgoingFD m wd hNoReturn src sel hOrd
          (WallDatumPathEnds.hasPathEnds_wallData m wd hNoReturn src sel
            hOrd)).labelling.row
          (NonTrivalentValencyTwoDescent.retainedRow src sel (wallValid m wd) r₀)} := by
  classical
  have hMapU : sourceVertexMap wd.cover wd.hc wd.hab wd.hOne
      ((branchEquivAnchorComplement m wd hNoReturn src hOrd).symm w).1.1 = w.1.1 := by
    have h := branchEquivAnchorComplement_apply m wd hNoReturn src hOrd
      ((branchEquivAnchorComplement m wd hNoReturn src hOrd).symm w)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  rw [vertexEquiv_inl m wd hNoReturn src sel hOrd w,
    outFD_row_retained m wd src sel hOrd hNoReturn r₀,
    natCard_moved_of_ne m wd hNoReturn
      ((branchEquivAnchorComplement m wd hNoReturn src hOrd).symm w).1 hBase
      ((branchEquivAnchorComplement m wd hNoReturn src hOrd).symm w).2.1
      ((branchEquivAnchorComplement m wd hNoReturn src hOrd).symm w).2.2]
  refine Eq.trans ?_ (incidenceCount_wall_eq_incoming m wd src hOrd hNoReturn w.1.1 w.2
    ((branchEquivAnchorComplement m wd hNoReturn src hOrd).symm w).1.1 hMapU
    ((branchEquivAnchorComplement m wd hNoReturn src hOrd).symm w).1.2 r₀)
  exact (incidenceCount_candVertex m wd src sel hOrd w.1.1 w.2 r₀).symm

/-- The vanishing row of the incoming cover meets only the two ends of its
single occurrence. -/
theorem incidenceCount_facetRow_eq_zero
    (hNoReturn : NoContractedReturn wd.cover wd.contracted)
    (v : wd.cover.SourceVertex) (hl : v ≠ leftEnd m wd) (hr : v ≠ rightEnd m wd) :
    incidenceCount wd.cover v (facetRow m wd) = 0 := by
  classical
  unfold incidenceCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hRow
  have hEq := eq_facetEdge m wd hNoReturn e hRow
  have hInc := (mem_incidentEdges _ _ _).mp he
  rw [hEq] at hInc
  rcases hInc with h | h
  · exact hl h.symm
  · exact hr h.symm

include hOrd in
/-- A branch vertex of the candidate away from the anchor is neither `A_u` nor
`A_v`. -/
theorem endpointVertex_ne_candBranchMap_inl (side : Bool)
    (w : {w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
      w.1 ≠ anchorVertex m wd anchorBlk}) :
    NonTrivalentValencyTwoRows.endpointVertex sel side
        (Prescribed.selectedRepresentative sel) ≠
      (candBranchMap m wd src sel hOrd (Sum.inl w)).1 := by
  intro hBad
  exact Sum.inr_ne_inl (candBranchMap_injective m wd src sel hOrd (Subtype.ext hBad))

include hOrd in
/-- The bridge row does not reach a branch vertex of the candidate away from
the anchor: its only occurrence joins `A_u` to `A_v`. -/
theorem incidenceCount_bridgeRow_inl_eq_zero
    (w : {w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
      w.1 ≠ anchorVertex m wd anchorBlk}) :
    incidenceCount (Prescribed.validCandidate sel).datum
      (candBranchMap m wd src sel hOrd (Sum.inl w)).1
      (NonTrivalentValencyTwoRowEquiv.bridgeRow src sel (wallValid m wd)) = 0 := by
  classical
  unfold incidenceCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hRow
  have hVal := NonTrivalentValencyTwoRows.bridgeEdge_isolated src sel (wallValid m wd) e hRow
  have hInc := (mem_incidentEdges _ _ _).mp he
  rw [hVal] at hInc
  have hInc' : ((Prescribed.validCandidate sel).datum.sourceEnds
        (NonTrivalentValencyTwoRows.bridgeEdge sel
          (Prescribed.selectedRepresentative sel))).1 =
      (candBranchMap m wd src sel hOrd (Sum.inl w)).1 ∨
      ((Prescribed.validCandidate sel).datum.sourceEnds
        (NonTrivalentValencyTwoRows.bridgeEdge sel
          (Prescribed.selectedRepresentative sel))).2 =
      (candBranchMap m wd src sel hOrd (Sum.inl w)).1 := hInc
  rw [NonTrivalentValencyTwoRows.sourceEnds_bridgeEdge sel _] at hInc'
  rcases hInc' with h | h
  · exact endpointVertex_ne_candBranchMap_inl m wd src sel hOrd false w h
  · exact endpointVertex_ne_candBranchMap_inl m wd src sel hOrd true w h

include hOrd in
/-- **The star count at a branch vertex away from the anchor, on the bridge
row.**  Both sides vanish: downstairs the bridge joins `A_u` to `A_v`, upstairs
the vanishing chart row is the single occurrence `h_1`. -/
theorem incidence_inl_bridge (hNoReturn : NoContractedReturn wd.cover wd.contracted)
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd hNoReturn) = m.base)
    (w : {w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
      w.1 ≠ anchorVertex m wd anchorBlk}) :
    incidenceCount (Prescribed.validCandidate sel).datum
        (candBranchMap m wd src sel hOrd (Sum.inl w)).1
        (NonTrivalentValencyTwoRowEquiv.bridgeRow src sel (wallValid m wd)) =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquiv m wd hNoReturn src sel hOrd
            (candBranchMap m wd src sel hOrd (Sum.inl w)) ∧
        label d = (NonTrivalentValencyTwoExit.wallOutgoingFD m wd hNoReturn src sel hOrd
          (WallDatumPathEnds.hasPathEnds_wallData m wd hNoReturn src sel
            hOrd)).labelling.row
          (NonTrivalentValencyTwoRowEquiv.bridgeRow src sel (wallValid m wd))} := by
  classical
  rw [incidenceCount_bridgeRow_inl_eq_zero m wd src sel hOrd w]
  symm
  rw [vertexEquiv_inl m wd hNoReturn src sel hOrd w,
    outFD_row_bridge m wd src sel hOrd hNoReturn]
  have h := natCard_moved_of_ne m wd hNoReturn
    ((branchEquivAnchorComplement m wd hNoReturn src hOrd).symm w).1 hBase
    ((branchEquivAnchorComplement m wd hNoReturn src hOrd).symm w).2.1
    ((branchEquivAnchorComplement m wd hNoReturn src hOrd).symm w).2.2
    (facetRow m wd)
  rw [show wd.fullDim.labelling.row (facetRow m wd) = label m.base
    from Equiv.apply_symm_apply _ _] at h
  refine h.trans (incidenceCount_facetRow_eq_zero m wd hNoReturn _ ?_ ?_)
  · exact ((branchEquivAnchorComplement m wd hNoReturn src hOrd).symm w).2.1
  · exact ((branchEquivAnchorComplement m wd hNoReturn src hOrd).symm w).2.2

/-! ## 5.  At `A_u` -/

/-- The two survivors of the thick direction that `sel` merges (the paper's
`e_first`, `e_second`), as surviving occurrences of the wall datum. -/
def mergedWall (side : Bool) :
    NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne) :=
  if side then
      ⟨(Prescribed.secondSelected sel).1, secondSelected_survives m wd sel⟩
    else ⟨(Prescribed.firstSelected sel).1, firstSelected_survives m wd sel⟩

theorem selectedLift_eq (side : Bool) :
    selectedLift m wd sel side = liftEdge m wd (mergedWall m wd sel side) := by
  cases side <;> rfl

theorem stablePath_selectedLift (side : Bool) :
    (selectedLift m wd sel side).stablePath =
      incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m)
        (mergedWall m wd sel side).stablePath := by
  rw [selectedLift_eq m wd sel side]
  exact stablePath_liftEdge m wd _

/-- The retained merged survivor at `A_u`. -/
def mergedRetained (side : Bool) :
    NonDanglingEdge (Prescribed.validCandidate sel).datum :=
  ResolutionAwayFromWall.retainedEdge (Prescribed.validCandidate sel) (wallValid m wd).1
    (mergedWall m wd sel side)

theorem stablePath_mergedRetained (side : Bool) :
    (mergedRetained m wd sel side).stablePath =
      NonTrivalentValencyTwoDescent.retainedRow src sel (wallValid m wd)
        (mergedWall m wd sel side).stablePath :=
  (NonTrivalentValencyTwoDescent.retainedRow_mk src sel (wallValid m wd) _).symm

/-- The bridge occurrence, as a surviving occurrence of the candidate. -/
def bridgeND : NonDanglingEdge (Prescribed.validCandidate sel).datum :=
  ⟨NonTrivalentValencyTwoRows.bridgeEdge sel (Prescribed.selectedRepresentative sel),
    NonTrivalentValencyTwoRows.bridgeEdge_survives src sel (wallValid m wd)⟩

theorem stablePath_bridgeND :
    (bridgeND m wd src sel).stablePath =
      NonTrivalentValencyTwoRowEquiv.bridgeRow src sel (wallValid m wd) := rfl

theorem mergedRetained_ne :
    mergedRetained m wd sel false ≠ mergedRetained m wd sel true := by
  intro hBad
  exact NonTrivalentValencyTwoRows.firstSelected_val_ne sel
    (ResolutionCut.oldSourceEdge_injective (Prescribed.validCandidate sel)
      (congrArg Subtype.val hBad))

/-- **The exact star at `A_u` of `NonTrivalentValencyTwoRows`**, read on
surviving occurrences: the bridge and the two retained merged survivors. -/
theorem incidentEdges_endpointVertex_false :
    incidentEdges (Prescribed.validCandidate sel).datum
        (NonTrivalentValencyTwoRows.endpointVertex sel false
          (Prescribed.selectedRepresentative sel)) =
      {bridgeND m wd src sel, mergedRetained m wd sel false, mergedRetained m wd sel true} := by
  classical
  ext e
  rw [mem_incidentEdges]
  constructor
  · intro hInc
    have h : e.1 ∈ nonDanglingIncident (Prescribed.validCandidate sel).datum
        (NonTrivalentValencyTwoRows.endpointVertex sel false
          (Prescribed.selectedRepresentative sel)) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨e.2, hInc⟩
    rw [NonTrivalentValencyTwoRows.nonDanglingIncident_endpointVertex_false src sel
      (wallValid m wd)] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
    rcases h with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  · intro h
    have h2 : e.1 ∈ nonDanglingIncident (Prescribed.validCandidate sel).datum
        (NonTrivalentValencyTwoRows.endpointVertex sel false
          (Prescribed.selectedRepresentative sel)) := by
      rw [NonTrivalentValencyTwoRows.nonDanglingIncident_endpointVertex_false src sel
        (wallValid m wd)]
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    exact ((mem_nonDanglingIncident _ _ _).mp h2).2

/-- The chart label of the dart of an occurrence **on the row of** a merged
survivor.  Only the row equality is needed -- this is
`IncomingPairing.label_dart_of_row` composed with `stablePath_selectedLift` --
which is why (H-II) is stated at row level. -/
theorem label_dart_merged (d : StableSourceDarts.Dart wd.cover) (side : Bool)
    (hd : d.2.1.stablePath = (selectedLift m wd sel side).stablePath) :
    label (wd.tracks.iso.dart d) = wd.fullDim.labelling.row
      (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m)
        (mergedWall m wd sel side).stablePath) := by
  rw [wd.tracks.row_map d]
  refine congrArg wd.fullDim.labelling.row ?_
  show NonDanglingEdge.stablePath d.2.1 = _
  rw [hd]
  exact stablePath_selectedLift m wd sel side

theorem label_dart_merged_iff (hNoReturn : NoContractedReturn wd.cover wd.contracted)
    (d : StableSourceDarts.Dart wd.cover) (side : Bool)
    (hd : d.2.1.stablePath = (selectedLift m wd sel side).stablePath)
    (r₀ : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    (label (wd.tracks.iso.dart d) = wd.fullDim.labelling.row
        (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m)
          (wd.hForest m) r₀)) ↔
      (mergedWall m wd sel side).stablePath = r₀ := by
  rw [label_dart_merged m wd sel d side hd]
  constructor
  · intro h
    exact injective_incomingRow m wd hNoReturn (wd.fullDim.labelling.row.injective h)
  · intro h
    exact congrArg _ (congrArg _ h)

theorem label_dart_merged_ne_base (d : StableSourceDarts.Dart wd.cover) (side : Bool)
    (hd : d.2.1.stablePath = (selectedLift m wd sel side).stablePath) :
    label (wd.tracks.iso.dart d) ≠ label m.base := by
  rw [label_dart_merged m wd sel d side hd]
  exact NonTrivalentValencyThreeStarCount.labelling_row_incomingRow_ne_base m wd _

include hOrd in
/-- **The star count at `A_u`, on a retained row.**  The exact star
`{h_1, e_first, e_second}` is matched dart by dart with the star (H-II)
prescribes: `m.base` carries the vanishing chart row, and the two remaining
darts carry the incoming rows of the two merged survivors. -/
theorem incidence_inr_false_retained
    (hNoReturn : NoContractedReturn wd.cover wd.contracted)
    (hPres : PrescribedMergedMove m wd hNoReturn sel)
    (r₀ : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (Prescribed.validCandidate sel).datum
        (candBranchMap m wd src sel hOrd (Sum.inr false)).1
        (NonTrivalentValencyTwoDescent.retainedRow src sel (wallValid m wd) r₀) =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquiv m wd hNoReturn src sel hOrd
            (candBranchMap m wd src sel hOrd (Sum.inr false)) ∧
        label d = (NonTrivalentValencyTwoExit.wallOutgoingFD m wd hNoReturn src sel hOrd
          (WallDatumPathEnds.hasPathEnds_wallData m wd hNoReturn src sel
            hOrd)).labelling.row
          (NonTrivalentValencyTwoDescent.retainedRow src sel (wallValid m wd) r₀)} := by
  classical
  obtain ⟨hBase, first, second, hFirst, hSecond, hStar⟩ := hPres
  rw [vertexEquiv_anchor_false m wd hNoReturn src sel hOrd hBase,
    outFD_row_retained m wd src sel hOrd hNoReturn r₀]
  have hRHS : Nat.card {d : D // graph.vert (m.perm d) = graph.vert m.base ∧
      label d = wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
        (wd.hCompat m) (wd.hForest m) r₀)} =
      ((Finset.univ.filter fun d : D ↦ graph.vert (m.perm d) = graph.vert m.base).filter
        fun d ↦ label d = wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab
          wd.hOne (wd.hCompat m) (wd.hForest m) r₀)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter]
  have hBridgeRow : ¬ ((bridgeND m wd src sel).stablePath =
      NonTrivalentValencyTwoDescent.retainedRow src sel (wallValid m wd) r₀) := by
    rw [stablePath_bridgeND m wd src sel]
    exact fun h ↦ retainedRow_ne_bridgeRow src sel (wallValid m wd) hOrd r₀ h.symm
  rw [hRHS, NonTrivalentValencyThreeStarCount.filter_moved_base m wd first second hStar,
    Finset.filter_insert,
    ite_eq_right (Ne.symm (NonTrivalentValencyThreeStarCount.labelling_row_incomingRow_ne_base m wd r₀)),
    NonTrivalentValencyThreeStarCount.card_filter_pair _ _
      (NonTrivalentValencyThreeStarCount.dart_ne m wd first second hStar)]
  show incidenceCount (Prescribed.validCandidate sel).datum
    (NonTrivalentValencyTwoRows.endpointVertex sel false
      (Prescribed.selectedRepresentative sel))
    (NonTrivalentValencyTwoDescent.retainedRow src sel (wallValid m wd) r₀) = _
  unfold incidenceCount
  rw [incidentEdges_endpointVertex_false m wd src sel, Finset.filter_insert,
    ite_eq_right hBridgeRow,
    NonTrivalentValencyThreeStarCount.card_filter_pair _ _ (mergedRetained_ne m wd sel)]
  have hcond : ∀ side : Bool, ((mergedRetained m wd sel side).stablePath =
      NonTrivalentValencyTwoDescent.retainedRow src sel (wallValid m wd) r₀) ↔
      (mergedWall m wd sel side).stablePath = r₀ := by
    intro side
    rw [stablePath_mergedRetained m wd src sel side]
    exact ⟨fun h ↦ NonTrivalentValencyTwoStarCount.injective_retainedRow src sel
      (wallValid m wd) hOrd h, fun h ↦ congrArg _ h⟩
  rw [if_congr (hcond false) rfl rfl, if_congr (hcond true) rfl rfl,
    if_congr (label_dart_merged_iff m wd sel hNoReturn first false hFirst r₀) rfl rfl,
    if_congr (label_dart_merged_iff m wd sel hNoReturn second true hSecond r₀) rfl rfl]

include hOrd in
/-- **The star count at `A_u`, on the bridge row.**  Both sides are one: the
bridge occurrence `h_1` downstairs, the contracted dart `m.base` upstairs. -/
theorem incidence_inr_false_bridge
    (hNoReturn : NoContractedReturn wd.cover wd.contracted)
    (hPres : PrescribedMergedMove m wd hNoReturn sel) :
    incidenceCount (Prescribed.validCandidate sel).datum
        (candBranchMap m wd src sel hOrd (Sum.inr false)).1
        (NonTrivalentValencyTwoRowEquiv.bridgeRow src sel (wallValid m wd)) =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquiv m wd hNoReturn src sel hOrd
            (candBranchMap m wd src sel hOrd (Sum.inr false)) ∧
        label d = (NonTrivalentValencyTwoExit.wallOutgoingFD m wd hNoReturn src sel hOrd
          (WallDatumPathEnds.hasPathEnds_wallData m wd hNoReturn src sel
            hOrd)).labelling.row
          (NonTrivalentValencyTwoRowEquiv.bridgeRow src sel (wallValid m wd))} := by
  classical
  obtain ⟨hBase, first, second, hFirst, hSecond, hStar⟩ := hPres
  rw [vertexEquiv_anchor_false m wd hNoReturn src sel hOrd hBase,
    outFD_row_bridge m wd src sel hOrd hNoReturn]
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
    · exact label_dart_merged_ne_base m wd sel first false hFirst
    · exact label_dart_merged_ne_base m wd sel second true hSecond
  have hR : ((Finset.univ.filter fun d : D ↦ graph.vert (m.perm d) = graph.vert m.base).filter
      fun d ↦ label d = label m.base).card = 1 := by
    rw [NonTrivalentValencyThreeStarCount.filter_moved_base m wd first second hStar,
      Finset.filter_insert, ite_eq_left rfl, hEmptyD]
    simp
  rw [hRHS, hR]
  show incidenceCount (Prescribed.validCandidate sel).datum
    (NonTrivalentValencyTwoRows.endpointVertex sel false
      (Prescribed.selectedRepresentative sel))
    (NonTrivalentValencyTwoRowEquiv.bridgeRow src sel (wallValid m wd)) = 1
  have hEmptyC : (({mergedRetained m wd sel false, mergedRetained m wd sel true} :
        Finset (NonDanglingEdge (Prescribed.validCandidate sel).datum)).filter
      fun e ↦ e.stablePath =
        NonTrivalentValencyTwoRowEquiv.bridgeRow src sel (wallValid m wd)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · rw [stablePath_mergedRetained m wd src sel false]
      exact retainedRow_ne_bridgeRow src sel (wallValid m wd) hOrd _
    · rw [stablePath_mergedRetained m wd src sel true]
      exact retainedRow_ne_bridgeRow src sel (wallValid m wd) hOrd _
  unfold incidenceCount
  rw [incidentEdges_endpointVertex_false m wd src sel, Finset.filter_insert,
    ite_eq_left (stablePath_bridgeND m wd src sel), hEmptyC]
  simp

/-! ## 6.  The leftover equation at `A_v`, and the link -/

include hOrd in
/-- **The star count at every branch vertex except `A_v`.** -/
theorem incidence_of_ne_rightAnchor
    (hNoReturn : NoContractedReturn wd.cover wd.contracted)
    (hPres : PrescribedMergedMove m wd hNoReturn sel)
    (v : BranchVertex (Prescribed.validCandidate sel).datum)
    (hv : v ≠ candBranchMap m wd src sel hOrd (Sum.inr true))
    (r : StablePath (Prescribed.validCandidate sel).datum) :
    incidenceCount (Prescribed.validCandidate sel).datum v.1 r =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquiv m wd hNoReturn src sel hOrd v ∧
        label d = (NonTrivalentValencyTwoExit.wallOutgoingFD m wd hNoReturn src sel hOrd
          (WallDatumPathEnds.hasPathEnds_wallData m wd hNoReturn src sel
            hOrd)).labelling.row r} := by
  classical
  obtain ⟨x, rfl⟩ : ∃ x, candBranchMap m wd src sel hOrd x = v :=
    ⟨(candBranchEquiv m wd src sel hOrd).symm v,
      (candBranchEquiv m wd src sel hOrd).apply_symm_apply v⟩
  obtain ⟨r', rfl⟩ : ∃ r', NonTrivalentValencyTwoRowEquiv.rowMap src sel (wallValid m wd) r' = r :=
    ⟨NonTrivalentValencyTwoRowEquiv.rowEquiv src sel (wallValid m wd) hOrd r,
      (NonTrivalentValencyTwoRowEquiv.rowEquiv src sel (wallValid m wd) hOrd).left_inv r⟩
  cases x with
  | inl w =>
    cases r' with
    | none => exact incidence_inl_bridge m wd src sel hOrd hNoReturn hPres.1 w
    | some r₀ => exact incidence_inl_retained m wd src sel hOrd hNoReturn hPres.1 w r₀
  | inr side =>
    cases side with
    | true => exact absurd rfl hv
    | false =>
      cases r' with
      | none => exact incidence_inr_false_bridge m wd src sel hOrd hNoReturn hPres
      | some r₀ => exact incidence_inr_false_retained m wd src sel hOrd hNoReturn hPres r₀

include hOrd in
/-- **The star count at `A_v`, from the leftover equation.**  A stable row of
the candidate meets its branch vertices twice in all, a chart row carries two
darts of the moved graph, `vertexEquiv` is a bijection, and the count agrees at
every other branch vertex; so it agrees at `A_v` too. -/
theorem incidence_inr_true
    (hNoReturn : NoContractedReturn wd.cover wd.contracted)
    (hPres : PrescribedMergedMove m wd hNoReturn sel)
    (r : StablePath (Prescribed.validCandidate sel).datum) :
    incidenceCount (Prescribed.validCandidate sel).datum
        (candBranchMap m wd src sel hOrd (Sum.inr true)).1 r =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquiv m wd hNoReturn src sel hOrd
            (candBranchMap m wd src sel hOrd (Sum.inr true)) ∧
        label d = (NonTrivalentValencyTwoExit.wallOutgoingFD m wd hNoReturn src sel hOrd
          (WallDatumPathEnds.hasPathEnds_wallData m wd hNoReturn src sel
            hOrd)).labelling.row r} := by
  classical
  set outFD := NonTrivalentValencyTwoExit.wallOutgoingFD m wd hNoReturn src sel hOrd
    (WallDatumPathEnds.hasPathEnds_wallData m wd hNoReturn src sel hOrd) with houtFD
  set v₀ := candBranchMap m wd src sel hOrd (Sum.inr true) with hv₀
  set f : BranchVertex (Prescribed.validCandidate sel).datum → ℕ :=
    fun v ↦ incidenceCount (Prescribed.validCandidate sel).datum v.1 r with hf
  set g : BranchVertex (Prescribed.validCandidate sel).datum → ℕ :=
    fun v ↦ Nat.card {d : D // graph.vert (m.perm d) =
        vertexEquiv m wd hNoReturn src sel hOrd v ∧
      label d = outFD.labelling.row r} with hg
  have hSumF : ∑ v, f v = 2 :=
    NonTrivalentValencyThreeStarCount.sum_incidenceCount_branchVertex
      (Prescribed.validCandidate sel).datum outFD.connected outFD.pathEnds r
  have hSumG : ∑ v, g v = 2 := by
    rw [Fintype.sum_equiv (vertexEquiv m wd hNoReturn src sel hOrd) g
      (fun x : V ↦ Nat.card {d : D // graph.vert (m.perm d) = x ∧
        label d = outFD.labelling.row r}) (fun v ↦ rfl)]
    exact NonTrivalentValencyThreeStarCount.sum_natCard_moved m wd (outFD.labelling.row r)
  have hAway : ∀ v ∈ Finset.univ.erase v₀, f v = g v := by
    intro v hv
    exact incidence_of_ne_rightAnchor m wd src sel hOrd hNoReturn hPres v
      (Finset.mem_erase.mp hv).1 r
  have hfsum := Finset.add_sum_erase Finset.univ f (Finset.mem_univ v₀)
  have hgsum := Finset.add_sum_erase Finset.univ g (Finset.mem_univ v₀)
  have hEq : ∑ x ∈ Finset.univ.erase v₀, f x = ∑ x ∈ Finset.univ.erase v₀, g x :=
    Finset.sum_congr rfl hAway
  show f v₀ = g v₀
  omega

include hOrd in
/-- **The star count, at every branch vertex and every row.**  This is the one
geometric input `NonTrivalentValencyTwoTracks.typeChangeLink_of_incidence` needs,
under (H-II). -/
theorem incidence_of_prescribedMergedMove
    (hNoReturn : NoContractedReturn wd.cover wd.contracted)
    (hPres : PrescribedMergedMove m wd hNoReturn sel)
    (v : BranchVertex (Prescribed.validCandidate sel).datum)
    (r : StablePath (Prescribed.validCandidate sel).datum) :
    incidenceCount (Prescribed.validCandidate sel).datum v.1 r =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquiv m wd hNoReturn src sel hOrd v ∧
        label d = (NonTrivalentValencyTwoExit.wallOutgoingFD m wd hNoReturn src sel hOrd
          (WallDatumPathEnds.hasPathEnds_wallData m wd hNoReturn src sel
            hOrd)).labelling.row r} := by
  classical
  by_cases hv : v = candBranchMap m wd src sel hOrd (Sum.inr true)
  · subst hv
    exact incidence_inr_true m wd src sel hOrd hNoReturn hPres r
  · exact incidence_of_ne_rightAnchor m wd src sel hOrd hNoReturn hPres v hv r

include hOrd in
/-- **`OuterWalk.TypeChangeLink` at a two-valent Base II wall under (H-II).**
`NonTrivalentValencyTwoTracks.typeChangeLink_of_incidence` reduces the link to the
star count; this discharges it. -/
def typeChangeLink_of_prescribedMergedMove
    (hNoReturn : NoContractedReturn wd.cover wd.contracted)
    (hPres : PrescribedMergedMove m wd hNoReturn sel) :
    TypeChangeLink m wd :=
  typeChangeLink_of_incidence m wd hNoReturn src sel hOrd
    (incidence_of_prescribedMergedMove m wd src sel hOrd hNoReturn hPres)

end Wall

end

end DraismaVargas.LocalCases.NonTrivalentValencyTwoStarCount
