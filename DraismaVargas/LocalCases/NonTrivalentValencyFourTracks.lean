module

public import DraismaVargas.LocalCases.NonTrivalentValencyFourExitLink
public import DraismaVargas.LocalCases.MovedIncidenceIso
public import DraismaVargas.LocalCases.WallSplitIncidence

@[expose] public section

/-!
# The vertex dictionary of the valency-four `K = 0` type change, and (H-IV)

Source: Vargas, Part II (arXiv:2609.09109), §5.1 (a combinatorial type change
is recorded as a Whitehead move on the *ambient* tracked graph; labelling
convention (1)) and §5.2 (case `{v4-nd4}`: the unique four-valent vertex `A`
resolves into the two trivalent endpoints `A_1^{(q)}`, `A_2^{(q)}` joined by the
new occurrence `h_1^{(q)}`, the two survivors of each side of the prescribed
`2+2` pairing staying with their endpoint), together with Draisma--Vargas
Part I: the stable graph `H(M)` of a gluing datum, the induced row labels of a
limit (§5.2, inherited properties), and `lemma-ndval-of-GqA0`.

This module is the vertex half of the `tracks` field of the valency-four
`K = 0` link.  The valency-four exit (`NonTrivalentValencyFourExit`,
`NonTrivalentValencyFourExitLink`) reduces the link: at an
`OuterWalk.WallData` with `card (incidentEdges <wd.a, wd.hab>) = 4`,
`nonempty_typeChangeLink_of_tracks` needs only the prescribed `pairing : Fin 3`
and a `Tracks` of the move, whose `row_map` half is proved there
(`outLabelling_row_bridge`, `outLabelling_row_retained`).  `WallSplitIncidence`
and `MovedIncidenceIso` supply the two valency-agnostic halves of the `iso`
field: what `MovedIncidenceIso.tracksOfMovedIncidence` takes as input is a
branch-vertex bijection `vertexEquiv : BranchVertex cand.datum ~ V` and the
star count `hIncidence` against the *permuted* vertex map of `graph.move m`.
This module delivers the bijection, the hypothesis (H-IV) that pins the anchor
half of the star count, and the wall-side geometry both rest on.
`NonTrivalentValencyThreeTracks` does the same at valency three; the two
structural differences are that `NoContractedReturn` is free at a four-valent
wall (`StablePathFacetContraction.noContractedReturn_of_fourStar`), and that the
`K = 0` candidate lives over the block-preserving branch gauge
`PrescribedPairing.gaugedData` of the wall datum, so the branch-vertex
dictionary has an extra sheet-relabelling leg.

## What is proved

### 1.  The vanishing occurrence

* `facetRow`, `facetEdge`: the vanishing row of the incoming cover is the chart
  row of the move's contracted dart, and `facetEdge` is a surviving occurrence
  of it; `facetEdge_over_contracted` puts it over the contracted target
  occurrence (`NonTrivalentUniqueFourValent.target_eq_contracted_of_row_eq_facet`).
* `three_le_nonDanglingValency_end`, `nonDanglingValency_end_eq_three`: **its
  ends are branch vertices**, in fact trivalent.  A divalent end would carry a
  second surviving occurrence on the same row, hence a second surviving
  occurrence over the contracted target occurrence, which no-return at a
  four-valent wall forbids
  (`NonTrivalentUniqueFourValent.nonDanglingValency_ne_two_of_incident_row_facet`).
* `eq_facetEdge`: consequently the vanishing row is that single occurrence
  `h_1`; `leftEnd`, `rightEnd` are its two ends (`A_1`, `A_2` upstairs).

### 2.  The anchor

* `four_le_nonDanglingValency_map_leftEnd` and
  `sourceVertexMap_leftEnd_eq_anchorVertex`: **the vanishing occurrence lies
  over the anchor.**  `lemma-ndval-of-GqA0`
  (`WallSplitIncidence.nonDanglingValency_eq_sum_activeFibre`) gives `nd >= 4` at
  the image of `leftEnd`, and at a four-valent wall the merged vertex of
  surviving valency four is unique
  (`NonTrivalentUniqueFourValent.eq_of_nonDanglingValency_four`).
* `eq_leftEnd_or_eq_rightEnd_of_mem_activeFibre`: **the anchor fibre carries
  exactly `leftEnd` and `rightEnd` as branch vertices**, because
  `nd(A) = 4 = 2 + sum (nd(V) - 2)` and each summand is `0` or `1`.
* `wallDatum_trivalent_away_anchor`: the wall datum is trivalent away from the
  anchor (`NonTrivalentUniqueFourValent.nonDanglingValency_le_three_of_ne`; in
  Part II, §5.1, `H_0` has a unique four-valent vertex and is trivalent
  elsewhere), at every vertex and not only at a wall block.
* `branchEquivAnchorComplement`: the branch-vertex dictionary of
  `WallSplitIncidence`,
  `{v : BranchVertex M // v <> leftEnd, rightEnd} ~ {w : BranchVertex M_0 // w <> A}`,
  **without its `hFibre` hypothesis**, exactly as at valency three: the proof
  only needs the branch pair above, not the full fibre.
* `gaugeBranchEquivAnchorComplement`: the extra leg `M_0 -> gaugedData`, a sheet
  relabelling, which preserves branch vertices
  (`StableGraphIncidence.sheetRelabelVertex`) and carries the anchor to the
  anchor (`NonTrivalentValencyFourRows.gauged_sourceVertex_eq`).

### 3.  The block classification: branch vertices over a non-anchor block

This replaces the much shorter valency-three argument of
`NonTrivalentValencyThreeTracks`, where the ordinary blocks kept one endpoint
whole. At valency four a non-anchor block `B` of the gauged wall datum is split
by the canonical W4 pattern into a retaining endpoint (the whole block) and one
fine endpoint per new-edge class, and *which* of them is trivalent depends on
how the prescribed pairing distributes the survivors of `B`.

* `card_ret_add_card_fine`, `card_fine_le_two`: the pairing splits the star of
  `B` into the retaining side and the fine side, with at most two on each
  (`NonTrivalentValencyFourExit.card_side_le_two`).
* `nonDanglingIncident_ret_subset`, `nonDanglingValency_ret_le_block`: the
  retaining endpoint is at most as valent as `B`
  (`NonTrivalentValencyFourRowEquiv.nonDanglingIncident_ret_dichotomy`, read as
  a bound by `B` itself rather than by three).
* `nonDanglingIncident_fine_subset`, `nonDanglingValency_fine_le_class`: a fine
  endpoint is bounded by its own new-edge class together with its new occurrence
  (`NonTrivalentValencyFourDescent.nonDanglingIncident_fine_cases`).
* `nonDanglingValency_endpoint_le_two`: **a block of surviving valency at most
  two carries no branch vertex.**  The one delicate case is two fine-side
  survivors in one class: then `B` has no retaining-side survivor, so a
  surviving new occurrence would leave the retaining endpoint of surviving
  valency one.
* `exists_branch_endpoint`: **a block of surviving valency three carries exactly
  one branch vertex.** Either every fine-side survivor is alone in its class --
  then the retaining endpoint is trivalent
  (`NonTrivalentValencyFourExit.nonDanglingValency_ret_eq_three_of_unique`) and
  every fine endpoint divalent -- or two fine-side survivors share a class, and
  then `B` has exactly one retaining-side survivor, the retaining endpoint is
  divalent, and their common fine endpoint is trivalent.
* `candVertex`, `candBranchMap`, `candBranchEquiv`: **the branch vertices of the
  `K = 0` candidate are the gauged datum's branch vertices other than the anchor
  plus the two `K = 0` endpoint vertices**, both trivalent by
  `NonTrivalentValencyFourDictionary.nonDanglingValency_endpointVertex`.
  Surjectivity over the anchor is the anchor case of
  `NonTrivalentValencyFourExit.candidate_trivalent` read as a classification:
  over the anchor only the selected fine class and the whole non-smaller block
  survive.

### 4.  (H-IV)

* `PrescribedPairingMove m wd wallStar anchorBlock hAnchor pairing`: the two
  darts the Whitehead move `m` places together with `m.base` -- the moved star of
  `graph.vert m.base` with `m.base` removed -- are, under `wd.tracks.iso.dart`,
  the darts of the two survivors of the anchor that `pairing` assigns to the side
  `false`, in the orientation that puts `A_1` at `graph.vert m.base` (first
  conjunct: `m.base` is the dart of `h_1` at the `A_1` end).  Side `false` is the
  side whose `K = 0` endpoint vertex `vertexEquiv` sends to `graph.vert m.base`
  (`vertexEquiv_anchor_false`).  The other orientation is normalised by the
  caller with `CubicDartGraph.MoveData.swap`, which leaves `graph.move m` unchanged.
* `SelectedSeparated`: the geometric content of a *type change* -- the two
  survivors of the side the move collects lift to occurrences at the two
  **different** ends of `h_1`.  Without it `A_1` sees exactly the star of
  `leftEnd` and no Whitehead move takes place.
* `prescribedMove` and `prescribedPairingMove_prescribedMove`: **non-vacuity of
  (H-IV), in relative form.**  Given the orientation and `SelectedSeparated`, the
  move that contracts the *same* edge as `m` and exchanges the side-`false`
  survivor at the `A_2` end with the remaining dart at the `A_1` end satisfies
  (H-IV).  (An absolute `exists m, PrescribedPairingMove m wd ...` does not
  typecheck: `wd : WallData arrival` with
  `arrival : FacetArrival degree graph label (label m.base)` fixes `m.base`, so
  the witness has to be produced with that same `base` field, which is what
  `prescribedMove` does.)

### 5.  `vertexEquiv`

* `coverBranchEquiv`, `vertexEquiv`: the composite
  `BranchVertex cand.datum ~ BranchVertex gauged-minus-A + Bool ~
   BranchVertex M_0-minus-A + Bool ~ BranchVertex M-minus-ends + Bool ~
   BranchVertex M ~ V`, the last step being the incoming tracking
  `wd.tracks.iso.vtx`.
* `vertexEquiv_anchor_false`, `vertexEquiv_anchor_true`: under (H-IV)'s
  orientation, `A_1` goes to `graph.vert m.base` and `A_2` to
  `graph.vert (graph.op m.base)`; `vertexEquiv_inl` reads the rest as the gauge
  followed by `sourceVertexMap` followed by the incoming tracking.

### 6.  Three pieces of the star count

* `move_vert_eq_iff_of_ne`: away from the two ends of the vanishing occurrence
  the Whitehead move does not change the star -- `m.perm` is the transposition of
  `m.left` and `m.right`, which sit at those two ends.
* `card_star_eq_incidenceCount`: the star of a branch vertex of the *incoming*
  cover, counted in the tracked ambient graph
  (`MovedIncidenceIso.DatumGraphIncidence.ofIso` at the incoming tracking, with
  the row label read through the chart).
* `injective_retainedRow`
  (`NonTrivalentValencyFourRetainedInjective.retainedRow_injective_of_single_row`) and
  `incidenceCount_retainedVertex_retainedRow`: **away from the wall the candidate
  does not change the star.**  This is transport (T1) below off the wall; it is
  `ResolutionStableIncidence.incidenceCount_retainedVertex` with its row
  *equivalence* hypothesis weakened to injectivity of `retainedRow`, which is
  what that proof actually uses.

### 7.  The link, reduced to the star count

* `typeChangeLink_of_incidence`: **`OuterWalk.TypeChangeLink` at a four-valent
  wall from the star count alone.**  Feeding `vertexEquiv` to
  `MovedIncidenceIso.tracksOfMovedIncidence` and the result to
  `NonTrivalentValencyFourExit.typeChangeLink_of_receipts` leaves exactly one
  geometric input, `hIncidence` (`hOp` is free from the incoming tracking
  through `MovedIncidenceIso.label_op_of_tracks`).

## What is not proved here

1. `hIncidence`, and hence `tracks`: the star count
   `incidenceCount cand.datum v r =
    Nat.card {d // (graph.move m).vert d = vertexEquiv v and label d = row r}`.
   This composite is not proved in this file;
   `NonTrivalentValencyFourStarCount` proves it, as the composite of three
   transports:
   * (T1) `incidenceCount gauged w r =
     incidenceCount cand.datum (candVertex w) (retainedRow r)`.  Off the wall
     this is `incidenceCount_retainedVertex_retainedRow` above; **at a
     non-anchor wall block** it is
     `NonTrivalentValencyFourStarCount.incidenceCount_block_candVertex`, the
     block census of Section 3 read occurrence by occurrence in its two cases
     (`incidenceCount_block_unique`, `block_pair_transport`), via
     `NonTrivalentValencyFourRowEquiv.stablePath_newSourceEdge_eq`.
   * (T2) `incidenceCount M_0 w r = incidenceCount gauged (gauge w) (gaugeRow r)`.
     This one is **available**: the gauge is a sheet relabelling, so
     `StableGraphIncidence.incidenceCount_sheetRelabel` transports the count with
     no geometric input; the caller has to compose the row legs
     (`SheetRelabelStable.stablePathEquiv`) with
     `NonTrivalentValencyFourExit.outLabelling_row_retained`, which is stated
     against exactly that equivalence.
   * (T3) `incidenceCount M_0 w r =
     incidenceCount M (branchEquivAnchorComplement.symm w) (incomingRow r)`.  Off
     the merged target vertex this is
     `WallSplitIncidence.incidenceCount_sourceVertexMap`; **at a wall block** it
     is the valency-agnostic `WallSplitIncidenceOrdinary.incidenceCount_unramified`
     (`NonTrivalentValencyFourStarCount.incidenceCount_wall_eq_incoming`), not a
     special case of `WallSplitIncidence.incidenceCount_anchor`, whose
     `hFacetOver` hypothesis fails there.  As at valency three, an ordinary wall block is
     unramified; at valency four this is free, since `W4IncomingPrunedFibre`
     shows the pruned fibre of every merged vertex is a point or a single
     internal occurrence with two distinct ends, with no ramification
     bookkeeping.
   At the anchor the count is the one (H-IV) prescribes, together with the
   exact stars `NonTrivalentValencyFourDictionary.nonDanglingIncident_endpointVertex`
   and `move_vert_eq_iff_of_ne` / `card_star_eq_incidenceCount` on the dart side.
2. `SelectedSeparated`, and (H-IV) itself.  (H-IV) is the per-vertex match at the
   anchor; `SelectedSeparated` is what makes the wall crossing an actual type
   change.  Neither is derived here.
3. `wallStar`, `anchorBlock` and `hAnchor`, exactly as in
   `typeChangeLink_of_receipts`: `NonTrivalentValencyFourExit`'s
   `exists_anchor_of_wallData` and `nonempty_typeChangeLink_of_tracks` produce
   them from the valency hypothesis `h4` alone, so they are a packaging choice
   and not a geometric receipt.

No structure is introduced.  Of the two `Prop` definitions,
`PrescribedPairingMove` has the relative witness
`prescribedPairingMove_prescribedMove`; `SelectedSeparated` is a named hypothesis
of that witness, in the same style as
`StablePathFacetContraction.NoContractedReturn`, and is not inhabited here.

## Consumers

`NonTrivalentValencyFourStarCount` proves (T1) and (T3) above and
delivers `typeChangeLink_of_prescribedPairingMove`: `OuterWalk.TypeChangeLink`
at a four-valent wall from (H-IV) and `wallStar` alone, via
`MovedIncidenceIso.tracksOfMovedIncidence` and hence the `tracks` field of
`NonTrivalentValencyFourExit.typeChangeLink_of_receipts`.
`NonTrivalentValencyFourDispatcher` then closes the whole valency-four
branch of `OuterWalk.TypeChangeLink` unconditionally, from the wall valency
alone: it derives (H-IV), `wallStar`, `anchorBlock` and `hAnchor` from the move
itself and consumes the `Wall`-section form of
`NonTrivalentValencyFourStarCount.typeChangeLink_of_prescribedPairingMove` (the
`Nonempty`-quantified corollary there is not usable by a dispatcher; see its
docstring).
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyFourTracks

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.StablePathCount
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.PrunedFibreValency
open DraismaVargas.LocalCases.PrunedFibreTree
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.ClassInjectivity
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero.PrescribedPairing
open DraismaVargas.LocalCases.NonTrivalentValencyFourRows
open DraismaVargas.LocalCases.NonTrivalentValencyFourDictionary
open DraismaVargas.LocalCases.NonTrivalentValencyFourExit
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk

noncomputable section

/-! ## 3.  The block classification, and the branch vertices of the candidate

This section needs no move and no tracking, so it is stated at the generality of
the `Presentation` section of `NonTrivalentValencyFourExit`: an incoming cover
`cover` with a full-dimensional presentation `fd`, a four-valent wall, an anchor
block of surviving valency four, and a prescribed pairing. -/

section Presentation

variable {targetIn : CFGraph} {deg : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (cover : GluingDatum targetIn deg)
  (fd : FullDimensionalSourcePresentation cover coordinate)
  {a b : targetIn.V} {contracted : targetIn.edges}
  (hc : (contracted : targetIn.V × targetIn.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges targetIn a b = 1)
  (wallStar : W4TargetPairings.FourStar (contract targetIn hab hOne) ⟨a, hab⟩)
  (hForest : ContractionForest cover a b contracted)
  (coordinates : coordinate → ℚ) (facet : coordinate)
  (hRows : ∀ row, row ≠ facet →
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates row ≠ 0)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
  (anchorBlock : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩)
  (hAnchor : nonDanglingValency (contractDatum cover hc hab hOne)
    (WallBlock.sourceVertex (contractDatum cover hc hab hOne) ⟨a, hab⟩ anchorBlock) = 4)
  (pairing : Fin 3)

local notation "wSrc" =>
  (NonTrivalentUniqueFourValent.wallFourBranchAnchor cover fd hc hab hOne
    wallStar hForest anchorBlock hAnchor)
local notation "wNG" =>
  (NonTrivalentUniqueFourValent.wall_noGlue cover fd hc hab hOne hForest)
local notation "wRam" =>
  (NonTrivalentUniqueFourValent.wall_ramification cover fd hc hab hOne wallStar
    hForest anchorBlock)
local notation "wProf" =>
  (NonTrivalentUniqueFourValent.ordinaryBlockProfile_of_single_row cover fd hc
    hab hOne wallStar hForest coordinates facet hRows hZeroCoord anchorBlock
    hAnchor)
local notation "wConn" =>
  (NonTrivalentUniqueFourValent.wall_target_connected cover fd hab hOne)
local notation "wGen" =>
  (NonTrivalentUniqueFourValent.wall_target_genus cover fd hab hOne)
local notation "wVal" =>
  (NonTrivalentUniqueFourValent.wall_valid cover fd hc hab hOne hForest)
local notation "wGauged" =>
  (NonTrivalentValencyFourKZero.PrescribedPairing.gaugedData wSrc pairing wNG wRam)
local notation "wCand" =>
  (NonTrivalentValencyFourBackground.candidate wSrc pairing wNG wRam wProf wConn wGen wVal)
local notation "wEpv" =>
  (NonTrivalentValencyFourRows.endpointVertex wSrc pairing wNG wRam wProf wConn wGen wVal)
local notation "wRetSide" =>
  (NonTrivalentValencyFourRowEquiv.retSide wSrc pairing wNG wRam wProf)

set_option quotPrecheck false in
local notation "wW" => (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)
set_option quotPrecheck false in
local notation "wPart" => ((wGauged).vertexPartition wW)
set_option quotPrecheck false in
local notation "wBRes" =>
  (W4Assembly.blockwiseResolution (wGauged) wallStar (wProf).pattern pairing)

/-! ### The two sides of a non-anchor wall block -/

/-- The prescribed pairing splits the surviving star of a wall block in two. -/
theorem card_ret_add_card_fine (x : Fin deg) :
    ((nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x)).filter
        (fun z ↦ wallStar.right pairing z.1.1 = wRetSide ((wPart).repr x))).card +
      ((nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x)).filter
        (fun z ↦ wallStar.right pairing z.1.1 = !wRetSide ((wPart).repr x))).card =
      nonDanglingValency (wGauged) ((wGauged).sourceEndpoint wW x) := by
  classical
  set star := nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x) with hStar
  set T := wRetSide ((wPart).repr x) with hT
  have hDisj : Disjoint (star.filter (fun z ↦ wallStar.right pairing z.1.1 = T))
      (star.filter (fun z ↦ wallStar.right pairing z.1.1 = !T)) := by
    refine Finset.disjoint_left.mpr ?_
    intro z hz hz'
    exact Bool.not_ne_self T (((Finset.mem_filter.mp hz').2).symm.trans
      ((Finset.mem_filter.mp hz).2))
  have hUnion : star.filter (fun z ↦ wallStar.right pairing z.1.1 = T) ∪
      star.filter (fun z ↦ wallStar.right pairing z.1.1 = !T) = star := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact (Finset.mem_filter.mp hz).1
      · exact (Finset.mem_filter.mp hz).1
    · intro z hz
      by_cases hSide : wallStar.right pairing z.1.1 = T
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz, hSide⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz,
          NonTrivalentValencyFourRowDictionary.bool_eq_not_of_ne hSide⟩)
  rw [← Finset.card_union_of_disjoint hDisj, hUnion, hStar, card_nonDanglingIncident]

/-- At most two survivors of a wall block sit on one side of the pairing. -/
theorem card_fine_le_two (x : Fin deg) :
    ((nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x)).filter
      (fun z ↦ wallStar.right pairing z.1.1 = !wRetSide ((wPart).repr x))).card ≤ 2 := by
  classical
  rw [← blockVertex_eq cover fd hc hab hOne wallStar hForest anchorBlock hAnchor pairing x]
  exact card_side_le_two cover fd hc hab hOne wallStar hForest anchorBlock hAnchor pairing x
    (!wRetSide ((wPart).repr x))

/-- **The retaining endpoint's star is the image of the block's star.** -/
theorem nonDanglingIncident_ret_subset (x : Fin deg)
    (hb : ¬ (wPart).Rel anchorBlock.1 x) :
    nonDanglingIncident (wCand).datum (wEpv (wRetSide ((wPart).repr x)) x) ⊆
      (nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x)).image
        (fun z ↦ if wallStar.right pairing z.1.1 = wRetSide ((wPart).repr x) then
          (wCand).oldSourceEdge z else (wCand).newSourceEdge z.1.2) := by
  classical
  intro f hf
  obtain ⟨hSurv, hInc⟩ := (mem_nonDanglingIncident _ _ _).mp hf
  rcases NonTrivalentValencyFourRowEquiv.nonDanglingIncident_ret_dichotomy wSrc pairing wNG
    wRam wProf wConn wGen wVal hb hSurv hInc with
    ⟨old, hOldSurv, hAt, hSide, hRel, rfl⟩ | ⟨old, hOldSurv, hAt, hSide, hRel, rfl⟩
  · exact Finset.mem_image.mpr ⟨old,
      mem_block_star cover fd hc hab hOne wallStar hForest anchorBlock hAnchor pairing
        hOldSurv hAt hRel, by rw [ite_eq_left hSide]⟩
  · exact Finset.mem_image.mpr ⟨old,
      mem_block_star cover fd hc hab hOne wallStar hForest anchorBlock hAnchor pairing
        hOldSurv hAt hRel, by rw [ite_eq_right (by rw [hSide]; exact Bool.not_ne_self _)]⟩

/-- **The retaining endpoint is at most as valent as its block.** -/
theorem nonDanglingValency_ret_le_block (x : Fin deg)
    (hb : ¬ (wPart).Rel anchorBlock.1 x) :
    nonDanglingValency (wCand).datum (wEpv (wRetSide ((wPart).repr x)) x) ≤
      nonDanglingValency (wGauged) ((wGauged).sourceEndpoint wW x) := by
  classical
  rw [← card_nonDanglingIncident, ← card_nonDanglingIncident]
  exact le_trans (Finset.card_le_card (nonDanglingIncident_ret_subset cover fd hc hab hOne
    wallStar hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing x hb))
    Finset.card_image_le

/-- **The fine endpoint's star**: its own new occurrence together with the retained
fine-side survivors of the block that share its new-edge class. -/
theorem nonDanglingIncident_fine_subset (x s : Fin deg)
    (hb : ¬ (wPart).Rel anchorBlock.1 x) (hs : (wPart).Rel x s) :
    nonDanglingIncident (wCand).datum (wEpv (!wRetSide ((wPart).repr x)) s) ⊆
      insert ((wCand).newSourceEdge s)
        (((nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x)).filter
          (fun z ↦ wallStar.right pairing z.1.1 = !wRetSide ((wPart).repr x) ∧
            (wCand).newSourceEdge z.1.2 = (wCand).newSourceEdge s)).image
          (wCand).oldSourceEdge) := by
  classical
  have hbs : ¬ (wPart).Rel anchorBlock.1 s := fun hBad ↦ hb (hBad.trans hs.symm)
  have hRepr : (wPart).repr s = (wPart).repr x := hs.symm
  intro f hf
  obtain ⟨hSurv, hInc⟩ := (mem_nonDanglingIncident _ _ _).mp hf
  have hInc' : Incident (wCand).datum f (wEpv (!wRetSide ((wPart).repr s)) s) := by
    rw [hRepr]; exact hInc
  rcases NonTrivalentValencyFourDescent.nonDanglingIncident_fine_cases wSrc pairing wNG wRam
    wProf wConn wGen wVal hbs hSurv hInc' with
    hNew | ⟨old, hOldSurv, hAt, hSide, hRel, rfl⟩
  · rw [hNew]
    exact Finset.mem_insert_self _ _
  · rw [hRepr] at hRel hSide
    refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨old, Finset.mem_filter.mpr
      ⟨mem_block_star cover fd hc hab hOne wallStar hForest anchorBlock hAnchor pairing
        hOldSurv hAt (hs.trans ((NonTrivalentValencyFourDescent.blockRes_newEdge_refines wSrc
          pairing wNG wRam wProf _).rel hRel)), hSide, ?_⟩, rfl⟩)
    refine (NonTrivalentValencyFourDictionary.newSourceEdge_eq_of_rel wSrc pairing wNG wRam
      wProf wConn wGen wVal ?_).symm
    exact (NonTrivalentValencyFourRowEquiv.candidate_newEdge_rel_block wSrc pairing wNG wRam
      wProf wConn wGen wVal hbs _).mpr (by rw [hRepr]; exact hRel)

/-- Two sheets of a non-anchor block carrying the same new occurrence are in one
new-edge class. -/
theorem newEdge_rel_of_newSourceEdge_eq (x s : Fin deg)
    (hb : ¬ (wPart).Rel anchorBlock.1 x) (hs : (wPart).Rel x s) (y : Fin deg)
    (hy : (wCand).newSourceEdge y = (wCand).newSourceEdge s) :
    (wBRes ((wPart).repr x)).newEdge.Rel s y := by
  have hbs : ¬ (wPart).Rel anchorBlock.1 s := fun hBad ↦ hb (hBad.trans hs.symm)
  have hRepr : (wPart).repr s = (wPart).repr x := hs.symm
  have hPaste := NonTrivalentValencyFourRowDictionary.newSourceEdge_rel_of_eq wSrc pairing
    wNG wRam wProf wConn wGen wVal hy
  have h := (NonTrivalentValencyFourRowEquiv.candidate_newEdge_rel_block wSrc pairing wNG
    wRam wProf wConn wGen wVal hbs y).mp hPaste.symm
  rwa [hRepr] at h

/-- **A block of surviving valency at most two carries no branch vertex of the
candidate.**  The retaining endpoint is bounded by the block itself; a fine
endpoint is bounded by its own new-edge class together with its new occurrence,
and when that class carries both fine-side survivors the block has no
retaining-side survivor at all, so the new occurrence would leave the retaining
endpoint of surviving valency one. -/
theorem nonDanglingValency_endpoint_le_two (x s : Fin deg) (side : Bool)
    (hb : ¬ (wPart).Rel anchorBlock.1 x) (hs : (wPart).Rel x s)
    (hB : nonDanglingValency (wGauged) ((wGauged).sourceEndpoint wW x) ≤ 2) :
    nonDanglingValency (wCand).datum (wEpv side s) ≤ 2 := by
  classical
  by_cases hSide : side = wRetSide ((wPart).repr x)
  · rw [hSide, NonTrivalentValencyFourDescent.endpointVertex_ret_eq wSrc pairing wNG wRam
      wProf wConn wGen wVal hb hs]
    exact le_trans (nonDanglingValency_ret_le_block cover fd hc hab hOne wallStar hForest
      coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing x hb) hB
  · rw [NonTrivalentValencyFourRowDictionary.bool_eq_not_of_ne hSide]
    have hsub := nonDanglingIncident_fine_subset cover fd hc hab hOne wallStar hForest
      coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing x s hb hs
    have hSum := card_ret_add_card_fine cover fd hc hab hOne wallStar hForest coordinates
      facet hRows hZeroCoord anchorBlock hAnchor pairing x
    have hFineLe := card_fine_le_two cover fd hc hab hOne wallStar hForest coordinates facet
      hRows hZeroCoord anchorBlock hAnchor pairing x
    set star := nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x) with hStar
    set T := wRetSide ((wPart).repr x) with hT
    set filt := star.filter (fun z ↦ wallStar.right pairing z.1.1 = !T ∧
      (wCand).newSourceEdge z.1.2 = (wCand).newSourceEdge s) with hFilt
    have hImageLe := Finset.card_image_le (s := filt) (f := (wCand).oldSourceEdge)
    have hcard : nonDanglingValency (wCand).datum (wEpv (!T) s) ≤ 1 + filt.card := by
      rw [← card_nonDanglingIncident]
      refine le_trans (Finset.card_le_card hsub) ?_
      refine le_trans (Finset.card_insert_le _ _) ?_
      omega
    by_cases hk : filt.card ≤ 1
    · omega
    · have hk2 : 2 ≤ filt.card := by omega
      have hFiltSubFine : filt ⊆ star.filter (fun z ↦ wallStar.right pairing z.1.1 = !T) := by
        intro z hz
        rw [hFilt, Finset.mem_filter] at hz
        exact Finset.mem_filter.mpr ⟨hz.1, hz.2.1⟩
      have hFineGe := Finset.card_le_card hFiltSubFine
      have hRetZero : (star.filter (fun z ↦ wallStar.right pairing z.1.1 = T)).card = 0 := by
        omega
      have hFiltEqFine : filt = star.filter (fun z ↦ wallStar.right pairing z.1.1 = !T) :=
        Finset.eq_of_subset_of_card_le hFiltSubFine (by omega)
      have hDang : IsDangling (wCand).datum ((wCand).newSourceEdge s) := by
        by_contra hSurv
        have hIncRet : Incident (wCand).datum ((wCand).newSourceEdge s) (wEpv T x) :=
          NonTrivalentValencyFourRowDictionary.newSourceEdge_incident_ret wSrc pairing wNG
            wRam wProf wConn wGen wVal hb hs
        have hImg : nonDanglingIncident (wCand).datum (wEpv T x) ⊆
            {(wCand).newSourceEdge s} := by
          refine (nonDanglingIncident_ret_subset cover fd hc hab hOne wallStar hForest
            coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing x hb).trans ?_
          intro y hy
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
          have hzSide : wallStar.right pairing z.1.1 ≠ T := by
            intro hBad
            have hzT : z ∈ star.filter (fun w ↦ wallStar.right pairing w.1.1 = T) :=
              Finset.mem_filter.mpr ⟨hz, hBad⟩
            rw [Finset.card_eq_zero.mp hRetZero] at hzT
            exact absurd hzT (Finset.notMem_empty z)
          have hzFine : z ∈ filt := by
            rw [hFiltEqFine]
            exact Finset.mem_filter.mpr ⟨hz,
              NonTrivalentValencyFourRowDictionary.bool_eq_not_of_ne hzSide⟩
          rw [hFilt, Finset.mem_filter] at hzFine
          rw [ite_eq_right hzSide]
          exact Finset.mem_singleton.mpr hzFine.2.2
        have hLe := Finset.card_le_card hImg
        rw [card_nonDanglingIncident, Finset.card_singleton] at hLe
        have hne0 := ClassInjectivity.nonDanglingValency_ne_zero_of_incident (wCand).datum
          hSurv hIncRet
        have hne1 := NonDanglingValency.nonDanglingValency_ne_one (wCand).datum
          ((wCand).datum_valid (gaugedData_valid wSrc pairing wNG wRam wVal)).1 (wEpv T x)
        omega
      have hsub2 : nonDanglingIncident (wCand).datum (wEpv (!T) s) ⊆
          filt.image (wCand).oldSourceEdge := by
        intro y hy
        rcases Finset.mem_insert.mp (hsub hy) with rfl | h
        · exact absurd hDang ((mem_nonDanglingIncident _ _ _).mp hy).1
        · exact h
      have hFin := Finset.card_le_card hsub2
      rw [card_nonDanglingIncident] at hFin
      omega

/-- The fine endpoint at `s` is bounded by its own new-edge class. -/
theorem nonDanglingValency_fine_le_class (x s : Fin deg)
    (hb : ¬ (wPart).Rel anchorBlock.1 x) (hs : (wPart).Rel x s) :
    nonDanglingValency (wCand).datum (wEpv (!wRetSide ((wPart).repr x)) s) ≤
      1 + ((nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x)).filter
        (fun z ↦ wallStar.right pairing z.1.1 = !wRetSide ((wPart).repr x) ∧
          (wCand).newSourceEdge z.1.2 = (wCand).newSourceEdge s)).card := by
  classical
  have hsub := nonDanglingIncident_fine_subset cover fd hc hab hOne wallStar hForest
    coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing x s hb hs
  have hImageLe := Finset.card_image_le
    (s := (nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x)).filter
      (fun z ↦ wallStar.right pairing z.1.1 = !wRetSide ((wPart).repr x) ∧
        (wCand).newSourceEdge z.1.2 = (wCand).newSourceEdge s))
    (f := (wCand).oldSourceEdge)
  rw [← card_nonDanglingIncident]
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  omega

/-- **Exactly one branch vertex of the candidate over a non-anchor block of
surviving valency three.**  Either every fine-side survivor is alone in its
new-edge class, and then the retaining endpoint is the branch vertex while every
fine endpoint is divalent; or two fine-side survivors share a class, and then the
block has one retaining-side survivor, the retaining endpoint is divalent, and
their common fine endpoint is the branch vertex. -/
theorem exists_branch_endpoint (x : Fin deg)
    (hb : ¬ (wPart).Rel anchorBlock.1 x)
    (hB : nonDanglingValency (wGauged) ((wGauged).sourceEndpoint wW x) = 3) :
    ∃ (side : Bool) (s : Fin deg), (wPart).Rel x s ∧
      nonDanglingValency (wCand).datum (wEpv side s) = 3 ∧
      ∀ (side' : Bool) (s' : Fin deg), (wPart).Rel x s' →
        nonDanglingValency (wCand).datum (wEpv side' s') = 3 →
        wEpv side' s' = wEpv side s := by
  classical
  by_cases hU : ∀ z z' : (wGauged).SourceEdge,
      z ∈ nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x) →
      z' ∈ nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x) →
      wallStar.right pairing z.1.1 = !wRetSide ((wPart).repr x) →
      wallStar.right pairing z'.1.1 = !wRetSide ((wPart).repr x) →
      (wBRes ((wPart).repr x)).newEdge.Rel z.1.2 z'.1.2 → z = z'
  · refine ⟨wRetSide ((wPart).repr x), x, rfl,
      nonDanglingValency_ret_eq_three_of_unique cover fd hc hab hOne wallStar hForest
        coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing x hb hB hU, ?_⟩
    intro side' s' hs' h3'
    by_cases hSide' : side' = wRetSide ((wPart).repr x)
    · rw [hSide']
      exact NonTrivalentValencyFourDescent.endpointVertex_ret_eq wSrc pairing wNG wRam wProf
        wConn wGen wVal hb hs'
    · exfalso
      rw [NonTrivalentValencyFourRowDictionary.bool_eq_not_of_ne hSide'] at h3'
      have hLe := nonDanglingValency_fine_le_class cover fd hc hab hOne wallStar hForest
        coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing x s' hb hs'
      have hOne' : ((nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x)).filter
          (fun z ↦ wallStar.right pairing z.1.1 = !wRetSide ((wPart).repr x) ∧
            (wCand).newSourceEdge z.1.2 = (wCand).newSourceEdge s')).card ≤ 1 := by
        refine Finset.card_le_one.mpr ?_
        intro z hz z' hz'
        rw [Finset.mem_filter] at hz hz'
        refine hU z z' hz.1 hz'.1 hz.2.1 hz'.2.1 ?_
        have hzr := newEdge_rel_of_newSourceEdge_eq cover fd hc hab hOne wallStar hForest
          coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing x s' hb hs' z.1.2
          hz.2.2
        have hzr' := newEdge_rel_of_newSourceEdge_eq cover fd hc hab hOne wallStar hForest
          coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing x s' hb hs' z'.1.2
          hz'.2.2
        exact hzr.symm.trans hzr'
      omega
  · push Not at hU
    obtain ⟨f₁, f₂, hf₁, hf₂, hs₁, hs₂, hcls, hfNe⟩ := hU
    obtain ⟨h₁S, h₁A, h₁R⟩ := block_star_mem cover fd hc hab hOne wallStar hForest
      anchorBlock hAnchor pairing hf₁
    obtain ⟨h₂S, h₂A, h₂R⟩ := block_star_mem cover fd hc hab hOne wallStar hForest
      anchorBlock hAnchor pairing hf₂
    have hbf₁ : ¬ (wPart).Rel anchorBlock.1 f₁.1.2 := fun hBad ↦ hb (hBad.trans h₁R.symm)
    have hRepr₁ : (wPart).repr f₁.1.2 = (wPart).repr x := h₁R.symm
    have hSum := card_ret_add_card_fine cover fd hc hab hOne wallStar hForest coordinates
      facet hRows hZeroCoord anchorBlock hAnchor pairing x
    have hFineLe := card_fine_le_two cover fd hc hab hOne wallStar hForest coordinates facet
      hRows hZeroCoord anchorBlock hAnchor pairing x
    have hFineGe : 2 ≤ ((nonDanglingIncident (wGauged)
        ((wGauged).sourceEndpoint wW x)).filter
        (fun z ↦ wallStar.right pairing z.1.1 = !wRetSide ((wPart).repr x))).card := by
      have hsub : ({f₁, f₂} : Finset (wGauged).SourceEdge) ⊆
          (nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x)).filter
            (fun z ↦ wallStar.right pairing z.1.1 = !wRetSide ((wPart).repr x)) := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hf₁, hs₁⟩
        · exact Finset.mem_filter.mpr ⟨hf₂, hs₂⟩
      have hcard := Finset.card_le_card hsub
      rwa [Finset.card_insert_of_notMem (by simpa using hfNe), Finset.card_singleton] at hcard
    have hRetOne : ((nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x)).filter
        (fun z ↦ wallStar.right pairing z.1.1 = wRetSide ((wPart).repr x))).card = 1 := by
      omega
    have hFinePair : (nonDanglingIncident (wGauged)
        ((wGauged).sourceEndpoint wW x)).filter
        (fun z ↦ wallStar.right pairing z.1.1 = !wRetSide ((wPart).repr x)) = {f₁, f₂} := by
      refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
      · intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hf₁, hs₁⟩
        · exact Finset.mem_filter.mpr ⟨hf₂, hs₂⟩
      · rw [Finset.card_insert_of_notMem (by simpa using hfNe), Finset.card_singleton]
        omega
    have hNewPair : (wCand).newSourceEdge f₂.1.2 = (wCand).newSourceEdge f₁.1.2 :=
      (NonTrivalentValencyFourDictionary.newSourceEdge_eq_of_rel wSrc pairing wNG wRam wProf
        wConn wGen wVal
        ((NonTrivalentValencyFourRowEquiv.candidate_newEdge_rel_block wSrc pairing wNG wRam
          wProf wConn wGen wVal hbf₁ f₂.1.2).mpr (by rw [hRepr₁]; exact hcls))).symm
    obtain ⟨z, hzEq⟩ := Finset.card_eq_one.mp hRetOne
    have hzMem : z ∈ nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x) ∧
        wallStar.right pairing z.1.1 = wRetSide ((wPart).repr x) := by
      have hz : z ∈ (nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x)).filter
          (fun w ↦ wallStar.right pairing w.1.1 = wRetSide ((wPart).repr x)) := by
        rw [hzEq]; exact Finset.mem_singleton_self z
      exact Finset.mem_filter.mp hz
    obtain ⟨hzS, hzA, hzR⟩ := block_star_mem cover fd hc hab hOne wallStar hForest
      anchorBlock hAnchor pairing hzMem.1
    have hRetSubset : nonDanglingIncident (wCand).datum
        (wEpv (wRetSide ((wPart).repr x)) x) ⊆
        {(wCand).oldSourceEdge z, (wCand).newSourceEdge f₁.1.2} := by
      refine (nonDanglingIncident_ret_subset cover fd hc hab hOne wallStar hForest
        coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing x hb).trans ?_
      intro y hy
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
      by_cases hwS : wallStar.right pairing w.1.1 = wRetSide ((wPart).repr x)
      · rw [ite_eq_left hwS]
        have hwT : w ∈ (nonDanglingIncident (wGauged)
            ((wGauged).sourceEndpoint wW x)).filter
            (fun v ↦ wallStar.right pairing v.1.1 = wRetSide ((wPart).repr x)) :=
          Finset.mem_filter.mpr ⟨hw, hwS⟩
        rw [hzEq, Finset.mem_singleton] at hwT
        rw [hwT]
        exact Finset.mem_insert_self _ _
      · rw [ite_eq_right hwS]
        have hwF : w ∈ (nonDanglingIncident (wGauged)
            ((wGauged).sourceEndpoint wW x)).filter
            (fun v ↦ wallStar.right pairing v.1.1 = !wRetSide ((wPart).repr x)) :=
          Finset.mem_filter.mpr ⟨hw,
            NonTrivalentValencyFourRowDictionary.bool_eq_not_of_ne hwS⟩
        rw [hFinePair, Finset.mem_insert, Finset.mem_singleton] at hwF
        refine Finset.mem_insert_of_mem (Finset.mem_singleton.mpr ?_)
        rcases hwF with rfl | rfl
        · rfl
        · exact hNewPair
    have hOldZIncident : Incident (wCand).datum ((wCand).oldSourceEdge z)
        (wEpv (wRetSide ((wPart).repr x)) x) :=
      NonTrivalentValencyFourRowDictionary.oldSourceEdge_incident_ret wSrc pairing wNG wRam
        wProf wConn wGen wVal hb hzA hzR hzMem.2
    have hOldZSurv : ¬ IsDangling (wCand).datum ((wCand).oldSourceEdge z) :=
      ResolutionSurvival.not_isDangling_oldSourceEdge (wCand)
        (gaugedData_valid wSrc pairing wNG wRam wVal).1 _ hzS
    have hOldZMem : (wCand).oldSourceEdge z ∈ nonDanglingIncident (wCand).datum
        (wEpv (wRetSide ((wPart).repr x)) x) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨hOldZSurv, hOldZIncident⟩
    have hRetTwo : nonDanglingValency (wCand).datum
        (wEpv (wRetSide ((wPart).repr x)) x) = 2 := by
      have hLe : nonDanglingValency (wCand).datum
          (wEpv (wRetSide ((wPart).repr x)) x) ≤ 2 := by
        rw [← card_nonDanglingIncident]
        refine le_trans (Finset.card_le_card hRetSubset) ?_
        exact le_trans (Finset.card_insert_le _ _) (by simp)
      have hNe0 : nonDanglingValency (wCand).datum
          (wEpv (wRetSide ((wPart).repr x)) x) ≠ 0 :=
        ClassInjectivity.nonDanglingValency_ne_zero_of_incident (wCand).datum hOldZSurv
          hOldZIncident
      have hNe1 := NonDanglingValency.nonDanglingValency_ne_one (wCand).datum
        ((wCand).datum_valid (gaugedData_valid wSrc pairing wNG wRam wVal)).1
        (wEpv (wRetSide ((wPart).repr x)) x)
      omega
    have hCard2 : 1 < (nonDanglingIncident (wCand).datum
        (wEpv (wRetSide ((wPart).repr x)) x)).card := by
      rw [card_nonDanglingIncident, hRetTwo]
      omega
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hCard2
    obtain ⟨y, hyMem, hyNe⟩ : ∃ y ∈ nonDanglingIncident (wCand).datum
        (wEpv (wRetSide ((wPart).repr x)) x), y ≠ (wCand).oldSourceEdge z := by
      by_cases hU' : u = (wCand).oldSourceEdge z
      · exact ⟨v, hv, fun hBad ↦ huv (hU'.trans hBad.symm)⟩
      · exact ⟨u, hu, hU'⟩
    have hNewSurv : ¬ IsDangling (wCand).datum ((wCand).newSourceEdge f₁.1.2) := by
      have hyEq : y = (wCand).newSourceEdge f₁.1.2 := by
        have hmem := hRetSubset hyMem
        rw [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h | h
        · exact absurd h hyNe
        · exact h
      rw [← hyEq]
      exact ((mem_nonDanglingIncident _ _ _).mp hyMem).1
    have hFineThree : nonDanglingValency (wCand).datum
        (wEpv (!wRetSide ((wPart).repr x)) f₁.1.2) = 3 := by
      have hLe : nonDanglingValency (wCand).datum
          (wEpv (!wRetSide ((wPart).repr x)) f₁.1.2) ≤ 3 := by
        have hfine := nonDanglingValency_fine_le cover fd hc hab hOne wallStar hForest
          coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing f₁.1.2 hbf₁
        rwa [hRepr₁] at hfine
      have hInc₁ : Incident (wCand).datum ((wCand).oldSourceEdge f₁)
          (wEpv (!wRetSide ((wPart).repr x)) f₁.1.2) := by
        have hI := NonTrivalentValencyFourRows.retainedEdge_incident wSrc pairing wNG wRam
          wProf wConn wGen wVal f₁.1.1 h₁A (!wRetSide ((wPart).repr x)) hs₁ f₁.1.2
        rwa [GluingDatum.sourceEdge_self] at hI
      have hMove : wEpv (!wRetSide ((wPart).repr x)) f₂.1.2 =
          wEpv (!wRetSide ((wPart).repr x)) f₁.1.2 := by
        have h := NonTrivalentValencyFourRowEquiv.endpointVertex_fine_eq wSrc pairing wNG
          wRam wProf wConn wGen wVal hbf₁ (y := f₂.1.2) (by rw [hRepr₁]; exact hcls)
        rwa [hRepr₁] at h
      have hInc₂ : Incident (wCand).datum ((wCand).oldSourceEdge f₂)
          (wEpv (!wRetSide ((wPart).repr x)) f₁.1.2) := by
        have hI := NonTrivalentValencyFourRows.retainedEdge_incident wSrc pairing wNG wRam
          wProf wConn wGen wVal f₂.1.1 h₂A (!wRetSide ((wPart).repr x)) hs₂ f₂.1.2
        rw [GluingDatum.sourceEdge_self] at hI
        rwa [hMove] at hI
      have hInc₃ : Incident (wCand).datum ((wCand).newSourceEdge f₁.1.2)
          (wEpv (!wRetSide ((wPart).repr x)) f₁.1.2) :=
        NonTrivalentValencyFourRows.bridgeEdge_incident wSrc pairing wNG wRam wProf wConn
          wGen wVal (!wRetSide ((wPart).repr x)) f₁.1.2
      have hSub : ({(wCand).oldSourceEdge f₁, (wCand).oldSourceEdge f₂,
          (wCand).newSourceEdge f₁.1.2} : Finset (wCand).datum.SourceEdge) ⊆
            nonDanglingIncident (wCand).datum
              (wEpv (!wRetSide ((wPart).repr x)) f₁.1.2) := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · exact (mem_nonDanglingIncident _ _ _).mpr
            ⟨ResolutionSurvival.not_isDangling_oldSourceEdge (wCand)
              (gaugedData_valid wSrc pairing wNG wRam wVal).1 _ h₁S, hInc₁⟩
        · exact (mem_nonDanglingIncident _ _ _).mpr
            ⟨ResolutionSurvival.not_isDangling_oldSourceEdge (wCand)
              (gaugedData_valid wSrc pairing wNG wRam wVal).1 _ h₂S, hInc₂⟩
        · exact (mem_nonDanglingIncident _ _ _).mpr ⟨hNewSurv, hInc₃⟩
      have hCard := Finset.card_le_card hSub
      rw [card_nonDanglingIncident,
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          push Not
          exact ⟨fun hBad ↦ hfNe (ResolutionCut.oldSourceEdge_injective (wCand) hBad),
            NonTrivalentValencyFourRowDictionary.new_ne_old wSrc pairing wNG wRam wProf
              wConn wGen wVal f₁.1.2 f₁⟩),
        Finset.card_insert_of_notMem (by
          simpa using NonTrivalentValencyFourRowDictionary.new_ne_old wSrc pairing wNG wRam
            wProf wConn wGen wVal f₁.1.2 f₂),
        Finset.card_singleton] at hCard
      omega
    refine ⟨!wRetSide ((wPart).repr x), f₁.1.2, h₁R, hFineThree, ?_⟩
    intro side' s' hs' h3'
    by_cases hSide' : side' = wRetSide ((wPart).repr x)
    · exfalso
      rw [hSide', NonTrivalentValencyFourDescent.endpointVertex_ret_eq wSrc pairing wNG wRam
        wProf wConn wGen wVal hb hs', hRetTwo] at h3'
      exact absurd h3' (by decide)
    · rw [NonTrivalentValencyFourRowDictionary.bool_eq_not_of_ne hSide'] at h3' ⊢
      have hLe := nonDanglingValency_fine_le_class cover fd hc hab hOne wallStar hForest
        coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing x s' hb hs'
      have hClassGe : 2 ≤ ((nonDanglingIncident (wGauged)
          ((wGauged).sourceEndpoint wW x)).filter
          (fun z ↦ wallStar.right pairing z.1.1 = !wRetSide ((wPart).repr x) ∧
            (wCand).newSourceEdge z.1.2 = (wCand).newSourceEdge s')).card := by omega
      have hClassSub : ((nonDanglingIncident (wGauged)
          ((wGauged).sourceEndpoint wW x)).filter
          (fun z ↦ wallStar.right pairing z.1.1 = !wRetSide ((wPart).repr x) ∧
            (wCand).newSourceEdge z.1.2 = (wCand).newSourceEdge s')) ⊆ {f₁, f₂} := by
        rw [← hFinePair]
        intro w hw
        rw [Finset.mem_filter] at hw
        exact Finset.mem_filter.mpr ⟨hw.1, hw.2.1⟩
      have hClassEq : ((nonDanglingIncident (wGauged)
          ((wGauged).sourceEndpoint wW x)).filter
          (fun z ↦ wallStar.right pairing z.1.1 = !wRetSide ((wPart).repr x) ∧
            (wCand).newSourceEdge z.1.2 = (wCand).newSourceEdge s')) = {f₁, f₂} := by
        refine Finset.eq_of_subset_of_card_le hClassSub ?_
        rw [Finset.card_insert_of_notMem (by simpa using hfNe), Finset.card_singleton]
        omega
      have hf₁Mem : f₁ ∈ ((nonDanglingIncident (wGauged)
          ((wGauged).sourceEndpoint wW x)).filter
          (fun z ↦ wallStar.right pairing z.1.1 = !wRetSide ((wPart).repr x) ∧
            (wCand).newSourceEdge z.1.2 = (wCand).newSourceEdge s')) := by
        rw [hClassEq]; exact Finset.mem_insert_self _ _
      have hEqNew : (wCand).newSourceEdge f₁.1.2 = (wCand).newSourceEdge s' :=
        (Finset.mem_filter.mp hf₁Mem).2.2
      have hbs' : ¬ (wPart).Rel anchorBlock.1 s' := fun hBad ↦ hb (hBad.trans hs'.symm)
      have hRepr' : (wPart).repr s' = (wPart).repr x := hs'.symm
      have hRel := newEdge_rel_of_newSourceEdge_eq cover fd hc hab hOne wallStar hForest
        coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing x s' hb hs' f₁.1.2
        hEqNew
      have hMove := NonTrivalentValencyFourRowEquiv.endpointVertex_fine_eq wSrc pairing wNG
        wRam wProf wConn wGen wVal hbs' (y := f₁.1.2) (by rw [hRepr']; exact hRel)
      rw [hRepr'] at hMove
      exact hMove.symm

/-! ### The branch vertices of the outgoing candidate -/

/-- The anchor of the gauged wall datum. -/
def gaugedAnchorVertex : (wGauged).SourceVertex :=
  (wGauged).sourceEndpoint wW anchorBlock.1

theorem sourceEndpoint_self_gauged (w : (wGauged).SourceVertex) (hw : w.1.1 = wW) :
    (wGauged).sourceEndpoint wW w.1.2 = w :=
  (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hw.symm, rfl⟩

theorem gaugedAnchorVertex_target :
    (gaugedAnchorVertex cover fd hc hab hOne wallStar hForest anchorBlock hAnchor
      pairing).1.1 = wW :=
  ((GluingDatum.sourceEndpoint_eq_iff (wGauged) _ _ _).mp rfl).1.symm

/-- A gauged wall vertex other than the anchor sits on a non-anchor block. -/
theorem not_rel_anchor_of_ne (w : (wGauged).SourceVertex) (hw : w.1.1 = wW)
    (hne : w ≠ gaugedAnchorVertex cover fd hc hab hOne wallStar hForest anchorBlock hAnchor
      pairing) :
    ¬ (wPart).Rel anchorBlock.1 w.1.2 := by
  intro hRel
  exact hne ((NonTrivalentValencyFourExit.sourceEndpoint_eq_of_rel hRel).trans
    (sourceEndpoint_self_gauged cover fd hc hab hOne wallStar hForest anchorBlock hAnchor
      pairing w hw)).symm

include hRows hZeroCoord in
/-- A branch vertex of the gauged wall datum over a non-anchor block has
surviving valency exactly three. -/
theorem nonDanglingValency_gaugedBlock_eq_three (w : BranchVertex (wGauged))
    (hw : w.1.1.1 = wW)
    (hne : w.1 ≠ gaugedAnchorVertex cover fd hc hab hOne wallStar hForest anchorBlock
      hAnchor pairing) :
    nonDanglingValency (wGauged) ((wGauged).sourceEndpoint wW w.1.1.2) = 3 := by
  have hb := not_rel_anchor_of_ne cover fd hc hab hOne wallStar hForest anchorBlock hAnchor
    pairing w.1 hw hne
  have hLe : nonDanglingValency (wGauged) ((wGauged).sourceEndpoint wW w.1.1.2) ≤ 3 := by
    rw [← blockVertex_eq cover fd hc hab hOne wallStar hForest anchorBlock hAnchor pairing
      w.1.1.2]
    exact NonTrivalentValencyFourRowEquivFinal.gauged_valency_of_single_row cover fd hc hab
      hOne wallStar hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing
      w.1.1.2 hb
  have hGe : 3 ≤ nonDanglingValency (wGauged) ((wGauged).sourceEndpoint wW w.1.1.2) := by
    rw [sourceEndpoint_self_gauged cover fd hc hab hOne wallStar hForest anchorBlock hAnchor
      pairing w.1 hw]
    exact w.2
  omega

/-- The branch vertex of the candidate over a non-anchor block, in the packaged
form `candVertex` consumes. -/
theorem exists_branch_vertex (x : Fin deg)
    (hb : ¬ (wPart).Rel anchorBlock.1 x)
    (hB : nonDanglingValency (wGauged) ((wGauged).sourceEndpoint wW x) = 3) :
    ∃ v : (wCand).datum.SourceVertex,
      nonDanglingValency (wCand).datum v = 3 ∧
      (∃ side : Bool, ∃ s : Fin deg, (wPart).Rel x s ∧ v = wEpv side s) ∧
      ∀ (side' : Bool) (s' : Fin deg), (wPart).Rel x s' →
        nonDanglingValency (wCand).datum (wEpv side' s') = 3 → wEpv side' s' = v := by
  obtain ⟨side, s, hs, h3, hUniq⟩ := exists_branch_endpoint cover fd hc hab hOne wallStar
    hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing x hb hB
  exact ⟨wEpv side s, h3, ⟨side, s, hs, rfl⟩, hUniq⟩

open scoped Classical in
/-- **The outgoing vertex over a branch vertex of the gauged wall datum other
than the anchor.**  Away from the wall it is the retained vertex; over a
non-anchor wall block it is the unique trivalent endpoint of that block. -/
def candVertex
    (w : {w : BranchVertex (wGauged) //
      w.1 ≠ gaugedAnchorVertex cover fd hc hab hOne wallStar hForest anchorBlock hAnchor
        pairing}) : (wCand).datum.SourceVertex :=
  if hw : w.1.1.1.1 = wW then
    Classical.choose (exists_branch_vertex cover fd hc hab hOne wallStar hForest coordinates
      facet hRows hZeroCoord anchorBlock hAnchor pairing w.1.1.1.2
      (not_rel_anchor_of_ne cover fd hc hab hOne wallStar hForest anchorBlock hAnchor pairing
        w.1.1 hw w.2)
      (nonDanglingValency_gaugedBlock_eq_three cover fd hc hab hOne wallStar hForest
        coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing w.1 hw w.2))
  else ResolutionAwayFromWall.retainedVertex (wCand) w.1.1

theorem candVertex_wall
    (w : {w : BranchVertex (wGauged) //
      w.1 ≠ gaugedAnchorVertex cover fd hc hab hOne wallStar hForest anchorBlock hAnchor
        pairing}) (hw : w.1.1.1.1 = wW) :
    candVertex cover fd hc hab hOne wallStar hForest coordinates facet hRows hZeroCoord
        anchorBlock hAnchor pairing w =
      Classical.choose (exists_branch_vertex cover fd hc hab hOne wallStar hForest
        coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing w.1.1.1.2
        (not_rel_anchor_of_ne cover fd hc hab hOne wallStar hForest anchorBlock hAnchor
          pairing w.1.1 hw w.2)
        (nonDanglingValency_gaugedBlock_eq_three cover fd hc hab hOne wallStar hForest
          coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing w.1 hw w.2)) := by
  classical
  unfold candVertex
  rw [dite_eq_left hw]

theorem candVertex_away
    (w : {w : BranchVertex (wGauged) //
      w.1 ≠ gaugedAnchorVertex cover fd hc hab hOne wallStar hForest anchorBlock hAnchor
        pairing}) (hw : w.1.1.1.1 ≠ wW) :
    candVertex cover fd hc hab hOne wallStar hForest coordinates facet hRows hZeroCoord
        anchorBlock hAnchor pairing w =
      ResolutionAwayFromWall.retainedVertex (wCand) w.1.1 := by
  classical
  unfold candVertex
  rw [dite_eq_right hw]

theorem nonDanglingValency_candVertex
    (w : {w : BranchVertex (wGauged) //
      w.1 ≠ gaugedAnchorVertex cover fd hc hab hOne wallStar hForest anchorBlock hAnchor
        pairing}) :
    3 ≤ nonDanglingValency (wCand).datum
      (candVertex cover fd hc hab hOne wallStar hForest coordinates facet hRows hZeroCoord
        anchorBlock hAnchor pairing w) := by
  by_cases hw : w.1.1.1.1 = wW
  · have h := (Classical.choose_spec (exists_branch_vertex cover fd hc hab hOne wallStar
      hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing w.1.1.1.2
      (not_rel_anchor_of_ne cover fd hc hab hOne wallStar hForest anchorBlock hAnchor pairing
        w.1.1 hw w.2)
      (nonDanglingValency_gaugedBlock_eq_three cover fd hc hab hOne wallStar hForest
        coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing w.1 hw w.2))).1
    rw [candVertex_wall cover fd hc hab hOne wallStar hForest coordinates facet hRows
      hZeroCoord anchorBlock hAnchor pairing w hw]
    omega
  · rw [candVertex_away cover fd hc hab hOne wallStar hForest coordinates facet hRows
      hZeroCoord anchorBlock hAnchor pairing w hw,
      ResolutionAwayFromWall.nonDanglingValency_retainedVertex (wCand)
        (gaugedData_valid wSrc pairing wNG wRam wVal)
        (NonTrivalentValencyFourRows.candidate_sourceGenus wSrc pairing wNG wRam wProf wConn
          wGen wVal) w.1.1 hw]
    exact w.1.2

/-- The sheet of an endpoint vertex lies in the wall block of the sheet it is
built from. -/
theorem rel_endpointVertex_sheet (side : Bool) (s : Fin deg) :
    (wPart).Rel s (wEpv side s).1.2 :=
  (NonTrivalentValencyFourDictionary.candidate_endpointPartition_refines wSrc pairing wNG
    wRam wProf wConn wGen wVal side).rel
      (((wCand).datum.vertexPartition
        (if side then TargetExpansion.freshVertex (contract targetIn hab hOne)
          else TargetExpansion.oldVertex (contract targetIn hab hOne) wW)).rel_repr_right s)

theorem endpointVertex_target (side : Bool) (s : Fin deg) :
    (wEpv side s).1.1 =
      (if side then TargetExpansion.freshVertex (contract targetIn hab hOne)
        else TargetExpansion.oldVertex (contract targetIn hab hOne) wW) :=
  ((GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mp rfl).1.symm

theorem candVertex_spec_wall
    (w : {w : BranchVertex (wGauged) //
      w.1 ≠ gaugedAnchorVertex cover fd hc hab hOne wallStar hForest anchorBlock hAnchor
        pairing}) (hw : w.1.1.1.1 = wW) :
    (∃ side : Bool, ∃ s : Fin deg, (wPart).Rel w.1.1.1.2 s ∧
        candVertex cover fd hc hab hOne wallStar hForest coordinates facet hRows hZeroCoord
          anchorBlock hAnchor pairing w = wEpv side s) ∧
      ∀ (side' : Bool) (s' : Fin deg), (wPart).Rel w.1.1.1.2 s' →
        nonDanglingValency (wCand).datum (wEpv side' s') = 3 →
        wEpv side' s' = candVertex cover fd hc hab hOne wallStar hForest coordinates facet
          hRows hZeroCoord anchorBlock hAnchor pairing w := by
  have h := Classical.choose_spec (exists_branch_vertex cover fd hc hab hOne wallStar
    hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing w.1.1.1.2
    (not_rel_anchor_of_ne cover fd hc hab hOne wallStar hForest anchorBlock hAnchor pairing
      w.1.1 hw w.2)
    (nonDanglingValency_gaugedBlock_eq_three cover fd hc hab hOne wallStar hForest
      coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing w.1 hw w.2))
  rw [candVertex_wall cover fd hc hab hOne wallStar hForest coordinates facet hRows
    hZeroCoord anchorBlock hAnchor pairing w hw]
  exact ⟨h.2.1, h.2.2⟩

/-- The sheet of the branch vertex over a wall block lies in that block. -/
theorem rel_candVertex_sheet
    (w : {w : BranchVertex (wGauged) //
      w.1 ≠ gaugedAnchorVertex cover fd hc hab hOne wallStar hForest anchorBlock hAnchor
        pairing}) (hw : w.1.1.1.1 = wW) :
    (wPart).Rel w.1.1.1.2
      (candVertex cover fd hc hab hOne wallStar hForest coordinates facet hRows hZeroCoord
        anchorBlock hAnchor pairing w).1.2 := by
  obtain ⟨⟨side, s, hs, hEq⟩, -⟩ := candVertex_spec_wall cover fd hc hab hOne wallStar
    hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing w hw
  rw [hEq]
  exact hs.trans (rel_endpointVertex_sheet cover fd hc hab hOne wallStar hForest coordinates
    facet hRows hZeroCoord anchorBlock hAnchor pairing side s)

/-- Over a wall block the branch vertex sits over the expanded wall. -/
theorem candVertex_target_wall
    (w : {w : BranchVertex (wGauged) //
      w.1 ≠ gaugedAnchorVertex cover fd hc hab hOne wallStar hForest anchorBlock hAnchor
        pairing}) (hw : w.1.1.1.1 = wW) :
    ∃ side : Bool, (candVertex cover fd hc hab hOne wallStar hForest coordinates facet hRows
        hZeroCoord anchorBlock hAnchor pairing w).1.1 =
      (if side then TargetExpansion.freshVertex (contract targetIn hab hOne)
        else TargetExpansion.oldVertex (contract targetIn hab hOne) wW) := by
  obtain ⟨⟨side, s, -, hEq⟩, -⟩ := candVertex_spec_wall cover fd hc hab hOne wallStar
    hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing w hw
  refine ⟨side, ?_⟩
  rw [hEq]
  exact endpointVertex_target cover fd hc hab hOne wallStar hForest coordinates facet hRows
    hZeroCoord anchorBlock hAnchor pairing side s

theorem candVertex_target_away
    (w : {w : BranchVertex (wGauged) //
      w.1 ≠ gaugedAnchorVertex cover fd hc hab hOne wallStar hForest anchorBlock hAnchor
        pairing}) (hw : w.1.1.1.1 ≠ wW) :
    (candVertex cover fd hc hab hOne wallStar hForest coordinates facet hRows hZeroCoord
        anchorBlock hAnchor pairing w).1.1 =
      TargetExpansion.oldVertex (contract targetIn hab hOne) w.1.1.1.1 := by
  rw [candVertex_away cover fd hc hab hOne wallStar hForest coordinates facet hRows
    hZeroCoord anchorBlock hAnchor pairing w hw]
  exact ((GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mp rfl).1.symm

/-- **The branch vertices of the `K = 0` candidate.** -/
def candBranchMap :
    ({w : BranchVertex (wGauged) //
        w.1 ≠ gaugedAnchorVertex cover fd hc hab hOne wallStar hForest anchorBlock hAnchor
          pairing} ⊕ Bool) → BranchVertex (wCand).datum
  | Sum.inl w => ⟨candVertex cover fd hc hab hOne wallStar hForest coordinates facet hRows
      hZeroCoord anchorBlock hAnchor pairing w,
      nonDanglingValency_candVertex cover fd hc hab hOne wallStar hForest coordinates facet
        hRows hZeroCoord anchorBlock hAnchor pairing w⟩
  | Sum.inr side => ⟨wEpv side (selectedRepresentative wSrc pairing),
      (NonTrivalentValencyFourDictionary.nonDanglingValency_endpointVertex wSrc pairing wNG
        wRam wProf wConn wGen wVal side).ge⟩

theorem rep_wall_rel : (wPart).Rel anchorBlock.1 (selectedRepresentative wSrc pairing) :=
  (NonTrivalentValencyFourRows.gauged_rel_iff wSrc pairing wNG wRam _ _).mpr
    ((NonTrivalentUniqueFourValent.wallFourBranchAnchor cover fd hc hab hOne wallStar hForest
      anchorBlock hAnchor).sheet_wall_rel _)

theorem candBranchMap_injective :
    Function.Injective (candBranchMap cover fd hc hab hOne wallStar hForest coordinates facet
      hRows hZeroCoord anchorBlock hAnchor pairing) := by
  classical
  have hRep := rep_wall_rel cover fd hc hab hOne wallStar hForest anchorBlock hAnchor
    pairing
  rintro (w | side) (w' | side') hEq <;>
    have hv : (candBranchMap cover fd hc hab hOne wallStar hForest coordinates facet hRows
        hZeroCoord anchorBlock hAnchor pairing _).1 =
      (candBranchMap cover fd hc hab hOne wallStar hForest coordinates facet hRows
        hZeroCoord anchorBlock hAnchor pairing _).1 := congrArg Subtype.val hEq
  · by_cases hw : w.1.1.1.1 = wW <;> by_cases hw' : w'.1.1.1.1 = wW
    · have hSheet : w.1.1.1.2 = w'.1.1.1.2 := by
        have h1 := rel_candVertex_sheet cover fd hc hab hOne wallStar hForest coordinates
          facet hRows hZeroCoord anchorBlock hAnchor pairing w hw
        have h2 := rel_candVertex_sheet cover fd hc hab hOne wallStar hForest coordinates
          facet hRows hZeroCoord anchorBlock hAnchor pairing w' hw'
        have hcv : candVertex cover fd hc hab hOne wallStar hForest coordinates facet hRows
            hZeroCoord anchorBlock hAnchor pairing w =
            candVertex cover fd hc hab hOne wallStar hForest coordinates facet hRows
              hZeroCoord anchorBlock hAnchor pairing w' := hv
        have hRel : (wPart).Rel w.1.1.1.2 w'.1.1.1.2 := by
          show (wPart).repr w.1.1.1.2 = (wPart).repr w'.1.1.1.2
          rw [h1, hcv, ← h2]
        have hc1 : (wPart).repr w.1.1.1.2 = w.1.1.1.2 := by
          have := w.1.1.2
          rwa [hw] at this
        have hc2 : (wPart).repr w'.1.1.1.2 = w'.1.1.1.2 := by
          have := w'.1.1.2
          rwa [hw'] at this
        rw [← hc1, ← hc2]
        exact hRel
      exact congrArg Sum.inl (Subtype.ext (Subtype.ext (Subtype.ext
        (Prod.ext (hw.trans hw'.symm) hSheet))))
    · exfalso
      obtain ⟨side, hside⟩ := candVertex_target_wall cover fd hc hab hOne wallStar hForest
        coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing w hw
      have hAway := candVertex_target_away cover fd hc hab hOne wallStar hForest coordinates
        facet hRows hZeroCoord anchorBlock hAnchor pairing w' hw'
      have hTarget : (if side then TargetExpansion.freshVertex (contract targetIn hab hOne)
          else TargetExpansion.oldVertex (contract targetIn hab hOne) wW) =
          TargetExpansion.oldVertex (contract targetIn hab hOne) w'.1.1.1.1 := by
        rw [← hside, ← hAway]
        exact congrArg (fun z : (wCand).datum.SourceVertex ↦ z.1.1) hv
      cases side with
      | false => exact hw' (Sum.inl_injective hTarget).symm
      | true => exact Sum.inr_ne_inl hTarget
    · exfalso
      obtain ⟨side, hside⟩ := candVertex_target_wall cover fd hc hab hOne wallStar hForest
        coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing w' hw'
      have hAway := candVertex_target_away cover fd hc hab hOne wallStar hForest coordinates
        facet hRows hZeroCoord anchorBlock hAnchor pairing w hw
      have hTarget : TargetExpansion.oldVertex (contract targetIn hab hOne) w.1.1.1.1 =
          (if side then TargetExpansion.freshVertex (contract targetIn hab hOne)
            else TargetExpansion.oldVertex (contract targetIn hab hOne) wW) := by
        rw [← hside, ← hAway]
        exact congrArg (fun z : (wCand).datum.SourceVertex ↦ z.1.1) hv
      cases side with
      | false => exact hw (Sum.inl_injective hTarget)
      | true => exact Sum.inl_ne_inr hTarget
    · have hRet : ResolutionAwayFromWall.retainedVertex (wCand) w.1.1 =
          ResolutionAwayFromWall.retainedVertex (wCand) w'.1.1 := by
        rw [← candVertex_away cover fd hc hab hOne wallStar hForest coordinates facet hRows
          hZeroCoord anchorBlock hAnchor pairing w hw,
          ← candVertex_away cover fd hc hab hOne wallStar hForest coordinates facet hRows
          hZeroCoord anchorBlock hAnchor pairing w' hw']
        exact hv
      exact congrArg Sum.inl (Subtype.ext (Subtype.ext
        (ResolutionStableIncidence.retainedVertex_injective_away (wCand) w.1.1 w'.1.1 hw hw'
          hRet)))
  · exfalso
    by_cases hw : w.1.1.1.1 = wW
    · have hRelW := rel_candVertex_sheet cover fd hc hab hOne wallStar hForest coordinates
        facet hRows hZeroCoord anchorBlock hAnchor pairing w hw
      have hRelRep := rel_endpointVertex_sheet cover fd hc hab hOne wallStar hForest
        coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing side'
        (selectedRepresentative wSrc pairing)
      have hcv : candVertex cover fd hc hab hOne wallStar hForest coordinates facet hRows
          hZeroCoord anchorBlock hAnchor pairing w =
          wEpv side' (selectedRepresentative wSrc pairing) := hv
      have hSheet : (wPart).Rel w.1.1.1.2 (selectedRepresentative wSrc pairing) := by
        show (wPart).repr w.1.1.1.2 = (wPart).repr (selectedRepresentative wSrc pairing)
        rw [hRelW, hcv, ← hRelRep]
      exact not_rel_anchor_of_ne cover fd hc hab hOne wallStar hForest anchorBlock hAnchor
        pairing w.1.1 hw w.2 (hRep.trans hSheet.symm)
    · have hAway := candVertex_target_away cover fd hc hab hOne wallStar hForest coordinates
        facet hRows hZeroCoord anchorBlock hAnchor pairing w hw
      have hTarget : TargetExpansion.oldVertex (contract targetIn hab hOne) w.1.1.1.1 =
          (if side' then TargetExpansion.freshVertex (contract targetIn hab hOne)
            else TargetExpansion.oldVertex (contract targetIn hab hOne) wW) := by
        rw [← hAway, ← endpointVertex_target cover fd hc hab hOne wallStar hForest
          coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing side'
          (selectedRepresentative wSrc pairing)]
        exact congrArg (fun z : (wCand).datum.SourceVertex ↦ z.1.1) hv
      cases side' with
      | false => exact hw (Sum.inl_injective hTarget)
      | true => exact Sum.inl_ne_inr hTarget
  · exfalso
    by_cases hw : w'.1.1.1.1 = wW
    · have hRelW := rel_candVertex_sheet cover fd hc hab hOne wallStar hForest coordinates
        facet hRows hZeroCoord anchorBlock hAnchor pairing w' hw
      have hRelRep := rel_endpointVertex_sheet cover fd hc hab hOne wallStar hForest
        coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing side
        (selectedRepresentative wSrc pairing)
      have hcv : wEpv side (selectedRepresentative wSrc pairing) =
          candVertex cover fd hc hab hOne wallStar hForest coordinates facet hRows
            hZeroCoord anchorBlock hAnchor pairing w' := hv
      have hSheet : (wPart).Rel w'.1.1.1.2 (selectedRepresentative wSrc pairing) := by
        show (wPart).repr w'.1.1.1.2 = (wPart).repr (selectedRepresentative wSrc pairing)
        rw [hRelW, ← hcv, ← hRelRep]
      exact not_rel_anchor_of_ne cover fd hc hab hOne wallStar hForest anchorBlock hAnchor
        pairing w'.1.1 hw w'.2 (hRep.trans hSheet.symm)
    · have hAway := candVertex_target_away cover fd hc hab hOne wallStar hForest coordinates
        facet hRows hZeroCoord anchorBlock hAnchor pairing w' hw
      have hTarget : TargetExpansion.oldVertex (contract targetIn hab hOne) w'.1.1.1.1 =
          (if side then TargetExpansion.freshVertex (contract targetIn hab hOne)
            else TargetExpansion.oldVertex (contract targetIn hab hOne) wW) := by
        rw [← hAway, ← endpointVertex_target cover fd hc hab hOne wallStar hForest
          coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing side
          (selectedRepresentative wSrc pairing)]
        exact (congrArg (fun z : (wCand).datum.SourceVertex ↦ z.1.1) hv).symm
      cases side with
      | false => exact hw (Sum.inl_injective hTarget)
      | true => exact Sum.inl_ne_inr hTarget
  · have hTarget : (if side then TargetExpansion.freshVertex (contract targetIn hab hOne)
        else TargetExpansion.oldVertex (contract targetIn hab hOne) wW) =
        (if side' then TargetExpansion.freshVertex (contract targetIn hab hOne)
          else TargetExpansion.oldVertex (contract targetIn hab hOne) wW) := by
      rw [← endpointVertex_target cover fd hc hab hOne wallStar hForest coordinates facet
        hRows hZeroCoord anchorBlock hAnchor pairing side (selectedRepresentative wSrc
          pairing),
        ← endpointVertex_target cover fd hc hab hOne wallStar hForest coordinates facet
        hRows hZeroCoord anchorBlock hAnchor pairing side' (selectedRepresentative wSrc
          pairing)]
      exact congrArg (fun z : (wCand).datum.SourceVertex ↦ z.1.1) hv
    cases side <;> cases side' <;>
      first
        | rfl
        | exact absurd hTarget Sum.inl_ne_inr
        | exact absurd hTarget Sum.inr_ne_inl

theorem candBranchMap_surjective :
    Function.Surjective (candBranchMap cover fd hc hab hOne wallStar hForest coordinates facet
      hRows hZeroCoord anchorBlock hAnchor pairing) := by
  classical
  intro v
  have hRep := rep_wall_rel cover fd hc hab hOne wallStar hForest anchorBlock hAnchor pairing
  have hWall : ∀ side : Bool, v.1.1.1 =
      (if side then TargetExpansion.freshVertex (contract targetIn hab hOne)
        else TargetExpansion.oldVertex (contract targetIn hab hOne) wW) →
      ∃ z, candBranchMap cover fd hc hab hOne wallStar hForest coordinates facet hRows
        hZeroCoord anchorBlock hAnchor pairing z = v := by
    intro side hv
    have hEq : wEpv side v.1.1.2 = v.1 :=
      NonTrivalentValencyFourExit.eq_endpointVertex cover fd hc hab hOne wallStar hForest
        coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing side v.1 hv
    have hNd3 : nonDanglingValency (wCand).datum (wEpv side v.1.1.2) = 3 := by
      rw [hEq]
      have hLe := NonTrivalentValencyFourExit.candidate_trivalent cover fd hc hab hOne
        wallStar hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing v.1
      have hGe := v.2
      omega
    by_cases hAnchorRel : (wPart).Rel anchorBlock.1 v.1.1.2
    · refine ⟨Sum.inr side, Subtype.ext ?_⟩
      show wEpv side (selectedRepresentative wSrc pairing) = v.1
      by_cases hSide : side = smallerSide wSrc pairing
      · by_cases hFine : (finePartition wSrc pairing wNG wRam).Rel
            (selectedRepresentative wSrc pairing) v.1.1.2
        · rw [NonTrivalentValencyFourRows.endpointVertex_eq wSrc pairing wNG wRam wProf
            wConn wGen wVal side hRep
            (by rw [hSide, NonTrivalentValencyFourDictionary.endpointForSide_smaller wSrc
              pairing wNG wRam]; exact hFine)]
          exact hEq
        · exfalso
          have hSingle : (finePartition wSrc pairing wNG wRam).block v.1.1.2 = {v.1.1.2} := by
            rcases finePartition_rel_or_singleton wSrc pairing wNG wRam v.1.1.2
              ((NonTrivalentValencyFourRows.gauged_rel_iff wSrc pairing wNG wRam _ _).mp
                hAnchorRel) with hR | hS
            · exact absurd hR hFine
            · exact hS
          have hCard := Finset.card_le_card
            (NonTrivalentValencyFourDictionary.nonDanglingIncident_singleton_subset wSrc
              pairing wNG wRam wProf wConn wGen wVal hAnchorRel hSingle hFine)
          rw [card_nonDanglingIncident, Finset.card_singleton] at hCard
          rw [hSide] at hNd3
          omega
      · rw [NonTrivalentValencyFourRows.endpointVertex_eq wSrc pairing wNG wRam wProf wConn
          wGen wVal side hRep
          (by rw [NonTrivalentValencyFourRowDictionary.bool_eq_not_of_ne hSide,
            NonTrivalentValencyFourRowDictionary.endpointForSide_not_smaller wSrc pairing
              wNG wRam]; exact hRep.symm.trans hAnchorRel)]
        exact hEq
    · have hBlockNd : nonDanglingValency (wGauged)
          ((wGauged).sourceEndpoint wW v.1.1.2) = 3 := by
        have hLe : nonDanglingValency (wGauged) ((wGauged).sourceEndpoint wW v.1.1.2) ≤ 3 := by
          rw [← blockVertex_eq cover fd hc hab hOne wallStar hForest anchorBlock hAnchor
            pairing v.1.1.2]
          exact NonTrivalentValencyFourRowEquivFinal.gauged_valency_of_single_row cover fd hc
            hab hOne wallStar hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor
            pairing v.1.1.2 hAnchorRel
        by_contra hBad
        have h2 : nonDanglingValency (wGauged) ((wGauged).sourceEndpoint wW v.1.1.2) ≤ 2 := by
          omega
        have hLe2 := nonDanglingValency_endpoint_le_two cover fd hc hab hOne wallStar hForest
          coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing v.1.1.2 v.1.1.2 side
          hAnchorRel rfl h2
        omega
      have hne : (wGauged).sourceEndpoint wW v.1.1.2 ≠
          gaugedAnchorVertex cover fd hc hab hOne wallStar hForest anchorBlock hAnchor
            pairing := by
        intro hBad
        refine hAnchorRel ?_
        have h := ((GluingDatum.sourceEndpoint_eq_iff (wGauged) wW v.1.1.2
          (gaugedAnchorVertex cover fd hc hab hOne wallStar hForest anchorBlock hAnchor
            pairing)).mp hBad).2
        have hx : (wPart).repr (gaugedAnchorVertex cover fd hc hab hOne wallStar hForest
            anchorBlock hAnchor pairing).1.2 = (wPart).repr anchorBlock.1 :=
          (wPart).repr_idem anchorBlock.1
        show (wPart).repr anchorBlock.1 = (wPart).repr v.1.1.2
        rw [← hx]
        exact h.symm
      have hw : ((wGauged).sourceEndpoint wW v.1.1.2).1.1 = wW :=
        ((GluingDatum.sourceEndpoint_eq_iff (wGauged) _ _ _).mp rfl).1.symm
      refine ⟨Sum.inl ⟨⟨(wGauged).sourceEndpoint wW v.1.1.2, hBlockNd.ge⟩, hne⟩,
        Subtype.ext ?_⟩
      show candVertex cover fd hc hab hOne wallStar hForest coordinates facet hRows
        hZeroCoord anchorBlock hAnchor pairing
          ⟨⟨(wGauged).sourceEndpoint wW v.1.1.2, hBlockNd.ge⟩, hne⟩ = v.1
      obtain ⟨-, hUniq⟩ := candVertex_spec_wall cover fd hc hab hOne wallStar hForest
        coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing
        ⟨⟨(wGauged).sourceEndpoint wW v.1.1.2, hBlockNd.ge⟩, hne⟩ hw
      have hres := hUniq side v.1.1.2 ((wPart).rel_repr_left v.1.1.2) hNd3
      rw [← hres, hEq]
  rcases hcase : (v.1.1.1 : TargetExpansion.Vertex (contract targetIn hab hOne)) with
    place | u
  · by_cases hIsWall : place = wW
    · exact hWall false (by rw [hcase, hIsWall]; rfl)
    · obtain ⟨old, hOld, hRet⟩ := ResolutionAwayFromWall.exists_retainedVertex_of_target
        (wCand) v.1 place hIsWall hcase
      have hAway : old.1.1 ≠ wW := by rw [hOld]; exact hIsWall
      have hNd : nonDanglingValency (wGauged) old =
          nonDanglingValency (wCand).datum v.1 := by
        rw [← hRet, ResolutionAwayFromWall.nonDanglingValency_retainedVertex (wCand)
          (gaugedData_valid wSrc pairing wNG wRam wVal)
          (NonTrivalentValencyFourRows.candidate_sourceGenus wSrc pairing wNG wRam wProf
            wConn wGen wVal) old hAway]
      have hne : old ≠ gaugedAnchorVertex cover fd hc hab hOne wallStar hForest anchorBlock
          hAnchor pairing := by
        intro hBad
        refine hAway ?_
        rw [hBad]
        exact gaugedAnchorVertex_target cover fd hc hab hOne wallStar hForest anchorBlock
          hAnchor pairing
      refine ⟨Sum.inl ⟨⟨old, by rw [hNd]; exact v.2⟩, hne⟩, Subtype.ext ?_⟩
      show candVertex cover fd hc hab hOne wallStar hForest coordinates facet hRows
        hZeroCoord anchorBlock hAnchor pairing ⟨⟨old, by rw [hNd]; exact v.2⟩, hne⟩ = v.1
      rw [candVertex_away cover fd hc hab hOne wallStar hForest coordinates facet hRows
        hZeroCoord anchorBlock hAnchor pairing ⟨⟨old, by rw [hNd]; exact v.2⟩, hne⟩ hAway]
      exact hRet
  · exact hWall true (by rw [hcase]; cases u; rfl)

/-- **The branch vertices of the `K = 0` candidate are the gauged wall datum's
branch vertices other than the anchor, plus the two `K = 0` endpoint
vertices.** -/
def candBranchEquiv :
    ({w : BranchVertex (wGauged) //
        w.1 ≠ gaugedAnchorVertex cover fd hc hab hOne wallStar hForest anchorBlock hAnchor
          pairing} ⊕ Bool) ≃ BranchVertex (wCand).datum :=
  Equiv.ofBijective (candBranchMap cover fd hc hab hOne wallStar hForest coordinates facet
    hRows hZeroCoord anchorBlock hAnchor pairing)
    ⟨candBranchMap_injective cover fd hc hab hOne wallStar hForest coordinates facet hRows
      hZeroCoord anchorBlock hAnchor pairing,
      candBranchMap_surjective cover fd hc hab hOne wallStar hForest coordinates facet hRows
        hZeroCoord anchorBlock hAnchor pairing⟩

/-! ### The gauge leg of the branch dictionary, and the off-wall star -/

/-- **The branch-vertex dictionary across the block-preserving branch gauge.**
The gauge is a sheet relabelling, so it preserves surviving valency and carries
the anchor to the anchor. -/
def gaugeBranchEquivAnchorComplement :
    {w : BranchVertex (contractDatum cover hc hab hOne) //
        w.1 ≠ WallBlock.sourceVertex (contractDatum cover hc hab hOne) wW anchorBlock} ≃
      {w : BranchVertex (wGauged) //
        w.1 ≠ gaugedAnchorVertex cover fd hc hab hOne wallStar hForest anchorBlock hAnchor
          pairing} :=
  (StableGraphIncidence.sheetRelabelVertex
      (NonTrivalentValencyFourKZero.PrescribedPairing.relabeling wSrc pairing wNG wRam)
      (wVal).1).subtypeEquiv (fun w ↦ by
    rw [not_iff_not]
    constructor
    · intro hEq
      show (NonTrivalentValencyFourKZero.PrescribedPairing.relabeling wSrc pairing wNG
        wRam).sourceVertexEquiv w.1 = _
      rw [hEq]
      exact NonTrivalentValencyFourRows.gauged_sourceVertex_eq wSrc pairing wNG wRam
    · intro hEq
      refine (NonTrivalentValencyFourKZero.PrescribedPairing.relabeling wSrc pairing wNG
        wRam).sourceVertexEquiv.injective ?_
      exact hEq.trans
        (NonTrivalentValencyFourRows.gauged_sourceVertex_eq wSrc pairing wNG wRam).symm)

@[simp] theorem gaugeBranchEquivAnchorComplement_apply
    (w : {w : BranchVertex (contractDatum cover hc hab hOne) //
      w.1 ≠ WallBlock.sourceVertex (contractDatum cover hc hab hOne) wW anchorBlock}) :
    (gaugeBranchEquivAnchorComplement cover fd hc hab hOne wallStar hForest anchorBlock
        hAnchor pairing w).1.1 =
      (NonTrivalentValencyFourKZero.PrescribedPairing.relabeling wSrc pairing wNG
        wRam).sourceVertexEquiv w.1.1 := rfl

/-- **The retained-row map is injective**
(`NonTrivalentValencyFourRetainedInjective`), named here as the hypothesis
`ResolutionStableIncidence.incidenceCount_retainedVertex` actually uses. -/
theorem injective_retainedRow :
    Function.Injective (NonTrivalentValencyFourRowDictionary.retainedRow wSrc pairing wNG
      wRam wProf wConn wGen wVal) :=
  NonTrivalentValencyFourRetainedInjective.retainedRow_injective_of_single_row cover fd hc
    hab hOne wallStar hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing

/-- **Away from the wall the candidate does not change the star.**  This is
`ResolutionStableIncidence.incidenceCount_retainedVertex` with the row
*equivalence* hypothesis weakened to injectivity of `retainedRow` (whose
complement is the bridge row), which is all the proof uses. -/
theorem incidenceCount_retainedVertex_retainedRow (w : (wGauged).SourceVertex)
    (hAway : w.1.1 ≠ wW) (row : StablePath (wGauged)) :
    incidenceCount (wGauged) w row =
      incidenceCount (wCand).datum
        (ResolutionAwayFromWall.retainedVertex (wCand) w)
        (NonTrivalentValencyFourRowDictionary.retainedRow wSrc pairing wNG wRam wProf wConn
          wGen wVal row) := by
  classical
  unfold incidenceCount
  apply Finset.card_bij (fun edge _ ↦ ResolutionAwayFromWall.retainedEdge (wCand)
    (gaugedData_valid wSrc pairing wNG wRam wVal).1 edge)
  · intro edge hEdge
    simp only [Finset.mem_filter, mem_incidentEdges] at hEdge ⊢
    refine ⟨(ResolutionAwayFromWall.incident_oldSourceEdge_iff (wCand) w hAway edge.1).mpr
      hEdge.1, ?_⟩
    rw [← NonTrivalentValencyFourRowDictionary.retainedRow_mk wSrc pairing wNG wRam wProf
      wConn wGen wVal edge, hEdge.2]
  · intro first _ second _ hEq
    exact ResolutionAwayFromWall.retainedEdge_injective (wCand)
      (gaugedData_valid wSrc pairing wNG wRam wVal).1 hEq
  · intro edge hEdge
    simp only [Finset.mem_filter, mem_incidentEdges] at hEdge
    have hMem : edge.1 ∈ nonDanglingIncident (wCand).datum
        (ResolutionAwayFromWall.retainedVertex (wCand) w) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hEdge.1⟩
    rw [ResolutionAwayFromWall.nonDanglingIncident_retainedVertex (wCand)
      (gaugedData_valid wSrc pairing wNG wRam wVal)
      (NonTrivalentValencyFourRows.candidate_sourceGenus wSrc pairing wNG wRam wProf wConn
        wGen wVal) w hAway] at hMem
    obtain ⟨old, hOld, hEqual⟩ := Finset.mem_image.mp hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hOld
    refine ⟨⟨old, hSurvives⟩, ?_, Subtype.ext hEqual⟩
    refine Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr hIncident,
      NonTrivalentValencyFourRetainedInjective.retainedRow_injective_of_single_row cover fd
        hc hab hOne wallStar hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor
        pairing ?_⟩
    rw [NonTrivalentValencyFourRowDictionary.retainedRow_mk wSrc pairing wNG wRam wProf
      wConn wGen wVal (⟨old, hSurvives⟩ : NonDanglingEdge (wGauged)),
      show ResolutionAwayFromWall.retainedEdge (wCand)
        (gaugedData_valid wSrc pairing wNG wRam wVal).1 ⟨old, hSurvives⟩ = edge from
        Subtype.ext hEqual]
    exact hEdge.2

end Presentation

section Walk

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)

/-! ## 1.  The vanishing row is a single occurrence between two branch vertices -/

/-- The vanishing stable row of the incoming cover. -/
def facetRow : StablePath wd.cover := wd.fullDim.labelling.row.symm (label m.base)

theorem exists_facetEdge : ∃ e : NonDanglingEdge wd.cover, e.stablePath = facetRow m wd :=
  Quot.exists_rep _

/-- **The vanishing occurrence `h₁`.** -/
def facetEdge : NonDanglingEdge wd.cover := Classical.choose (exists_facetEdge m wd)

theorem facetEdge_stablePath : (facetEdge m wd).stablePath = facetRow m wd :=
  Classical.choose_spec (exists_facetEdge m wd)

theorem facetEdge_row :
    wd.fullDim.labelling.row (facetEdge m wd).stablePath = label m.base := by
  rw [facetEdge_stablePath, facetRow, Equiv.apply_symm_apply]

theorem facetEdge_over_contracted : (facetEdge m wd).1.1.1 = wd.contracted :=
  NonTrivalentUniqueFourValent.target_eq_contracted_of_row_eq_facet wd.cover wd.fullDim
    wd.coordinates (label m.base) wd.hZeroCoord wd.hPosCoord wd.hFacetZero _
    (facetEdge_row m wd)

/-- **The ends of the vanishing row are not divalent.** -/
theorem nonDanglingValency_ne_two_of_incident_facetEdge
    (wallStar : W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩)
    (v : wd.cover.SourceVertex) (hv : Incident wd.cover (facetEdge m wd).1 v) :
    nonDanglingValency wd.cover v ≠ 2 :=
  NonTrivalentUniqueFourValent.nonDanglingValency_ne_two_of_incident_row_facet wd.cover
    wd.fullDim wd.hc wd.hab wd.hOne wallStar wd.coordinates (label m.base) wd.hZeroCoord
    wd.hPosCoord wd.hFacetZero _ (facetEdge_row m wd) v hv

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
    (wallStar : W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩)
    (v : wd.cover.SourceVertex) (hv : Incident wd.cover (facetEdge m wd).1 v) :
    3 ≤ nonDanglingValency wd.cover v := by
  have hTwo := nonDanglingValency_ne_two_of_incident_facetEdge m wd wallStar v hv
  have hOne := NonDanglingValency.nonDanglingValency_ne_one wd.cover wd.fullDim.connected v
  have hZero := nonDanglingValency_ne_zero_of_incident wd.cover (facetEdge m wd).2 hv
  omega

theorem nonDanglingValency_end_eq_three
    (wallStar : W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩)
    (v : wd.cover.SourceVertex) (hv : Incident wd.cover (facetEdge m wd).1 v) :
    nonDanglingValency wd.cover v = 3 := by
  have h1 := three_le_nonDanglingValency_end m wd wallStar v hv
  have h2 : nonDanglingValency wd.cover v ≤ 3 := wd.fullDim.trivalent v
  omega

/-- **Uniqueness of the vanishing occurrence.** -/
theorem eq_facetEdge
    (wallStar : W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩)
    (e : NonDanglingEdge wd.cover) (he : e.stablePath = facetRow m wd) :
    e = facetEdge m wd :=
  NonTrivalentUniqueFourValent.eq_of_stablePath_eq_of_ends_ne_two (facetEdge m wd)
    (by
      have := three_le_nonDanglingValency_end m wd wallStar _ (incident_facetEdge_leftEnd m wd)
      show nonDanglingValency wd.cover (leftEnd m wd) ≠ 2
      omega)
    (by
      have := three_le_nonDanglingValency_end m wd wallStar _ (incident_facetEdge_rightEnd m wd)
      show nonDanglingValency wd.cover (rightEnd m wd) ≠ 2
      omega)
    e (he.trans (facetEdge_stablePath m wd).symm)

/-! ## 2.  The vanishing occurrence sits inside the anchor fibre -/

section Anchor

variable {wallStar : W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne)
    ⟨wd.a, wd.hab⟩}
  {anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}

/-- The anchor of the wall datum: the four-valent merged source vertex. -/
def anchorVertex
    (anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex :=
  WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
    anchorBlock

theorem anchorVertex_target
    (anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    (anchorVertex m wd anchorBlock).1.1 =
      (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) :=
  ((GluingDatum.sourceEndpoint_eq_iff (contractDatum wd.cover wd.hc wd.hab wd.hOne) _ _ _).mp
    rfl).1.symm

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
    (wallStar : W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩) :
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
  have hL := three_le_nonDanglingValency_end m wd wallStar _ (incident_facetEdge_leftEnd m wd)
  have hR := three_le_nonDanglingValency_end m wd wallStar _ (incident_facetEdge_rightEnd m wd)
  omega

/-- **The vanishing occurrence lies over the anchor**: at a four-valent wall the
merged vertex of surviving valency four is unique. -/
theorem sourceVertexMap_leftEnd_eq_anchorVertex
    (wallStar : W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩)
    (anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (hAnchor : nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
        anchorBlock) = 4) :
    sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (leftEnd m wd) =
      anchorVertex m wd anchorBlock := by
  have hFour := four_le_nonDanglingValency_map_leftEnd m wd wallStar
  have hLe := NonTrivalentUniqueFourValent.nonDanglingValency_le_four wd.cover wd.fullDim
    wd.hc wd.hab wd.hOne wallStar (wd.hCompat m)
    (sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (leftEnd m wd))
  exact NonTrivalentUniqueFourValent.eq_of_nonDanglingValency_four wd.cover wd.fullDim wd.hc
    wd.hab wd.hOne wallStar (wd.hCompat m) wd.coordinates (label m.base) wd.hRows
    wd.hZeroCoord _ _ (by omega) hAnchor

theorem nonDanglingValency_anchorVertex
    (anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (hAnchor : nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
        anchorBlock) = 4) :
    nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (anchorVertex m wd anchorBlock) = 4 := hAnchor

/-- **The anchor fibre carries exactly the two ends of the vanishing
occurrence as branch vertices.** -/
theorem eq_leftEnd_or_eq_rightEnd_of_mem_activeFibre
    (wallStar : W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩)
    (anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (hAnchor : nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
        anchorBlock) = 4)
    (u : wd.cover.SourceVertex)
    (hu : u ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
      (anchorVertex m wd anchorBlock))
    (hThree : 3 ≤ nonDanglingValency wd.cover u) :
    u = leftEnd m wd ∨ u = rightEnd m wd := by
  classical
  by_contra hBad
  obtain ⟨hBadL, hBadR⟩ := not_or.mp hBad
  have hSum := WallSplitIncidence.nonDanglingValency_eq_sum_activeFibre wd.cover wd.hc wd.hab
    wd.hOne (wd.hCompat m) (wd.hForest m) (anchorVertex m wd anchorBlock) ⟨u, hu⟩
  rw [nonDanglingValency_anchorVertex m wd anchorBlock hAnchor] at hSum
  have hL : leftEnd m wd ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
      (anchorVertex m wd anchorBlock) := by
    rw [← sourceVertexMap_leftEnd_eq_anchorVertex m wd wallStar anchorBlock hAnchor]
    exact leftEnd_mem_activeFibre m wd
  have hR : rightEnd m wd ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
      (anchorVertex m wd anchorBlock) := by
    rw [← sourceVertexMap_leftEnd_eq_anchorVertex m wd wallStar anchorBlock hAnchor]
    exact rightEnd_mem_activeFibre m wd
  have hNonneg : ∀ w ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
      (anchorVertex m wd anchorBlock), (0 : ℤ) ≤ (nonDanglingValency wd.cover w : ℤ) - 2 := by
    intro w hw
    have := WallSplitIncidence.two_le_nonDanglingValency_of_mem_activeFibre wd.cover wd.hc wd.hab
      wd.hOne wd.fullDim.connected _ w hw
    omega
  have hTriple : ({leftEnd m wd, rightEnd m wd, u} : Finset wd.cover.SourceVertex) ⊆
      activeFibreVertices wd.cover wd.hc wd.hab wd.hOne (anchorVertex m wd anchorBlock) := by
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
  have hLv := three_le_nonDanglingValency_end m wd wallStar _ (incident_facetEdge_leftEnd m wd)
  have hRv := three_le_nonDanglingValency_end m wd wallStar _ (incident_facetEdge_rightEnd m wd)
  omega

/-- **The wall datum is trivalent away from the anchor.** -/
theorem wallDatum_trivalent_away_anchor
    (wallStar : W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩)
    (anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (hAnchor : nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
        anchorBlock) = 4)
    (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hw : w ≠ anchorVertex m wd anchorBlock) :
    nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne) w ≤ 3 :=
  NonTrivalentUniqueFourValent.nonDanglingValency_le_three_of_ne wd.cover wd.fullDim wd.hc
    wd.hab wd.hOne wallStar (wd.hCompat m) wd.coordinates (label m.base) wd.hRows
    wd.hZeroCoord _ hAnchor w hw

/-- **The branch-vertex dictionary across the wall contraction.** -/
def branchEquivAnchorComplement
    (wallStar : W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩)
    (anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (hAnchor : nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
        anchorBlock) = 4) :
    {v : BranchVertex wd.cover // v.1 ≠ leftEnd m wd ∧ v.1 ≠ rightEnd m wd} ≃
      {w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
        w.1 ≠ anchorVertex m wd anchorBlock} := by
  classical
  have hNeAnchor : ∀ v : wd.cover.SourceVertex, 3 ≤ nonDanglingValency wd.cover v →
      v ≠ leftEnd m wd → v ≠ rightEnd m wd →
      sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v ≠ anchorVertex m wd anchorBlock := by
    intro v hv hvl hvr hBad
    have hMem : v ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
        (anchorVertex m wd anchorBlock) :=
      (mem_activeFibreVertices wd.cover wd.hc wd.hab wd.hOne _ v).mpr ⟨hBad, by omega⟩
    rcases eq_leftEnd_or_eq_rightEnd_of_mem_activeFibre m wd wallStar anchorBlock hAnchor v
      hMem hv with h | h
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
        w.1 ≠ anchorVertex m wd anchorBlock} ↦ w.1.1) hEq
    have hLe := wallDatum_trivalent_away_anchor m wd wallStar anchorBlock hAnchor
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
      rw [← hMapU, hBad, sourceVertexMap_leftEnd_eq_anchorVertex m wd wallStar anchorBlock
        hAnchor]
    have hur : u ≠ rightEnd m wd := by
      intro hBad
      refine w.2 ?_
      rw [← hMapU, hBad, ← sourceVertexMap_leftEnd_eq_rightEnd m wd,
        sourceVertexMap_leftEnd_eq_anchorVertex m wd wallStar anchorBlock hAnchor]
    exact ⟨⟨⟨u, hThree⟩, hul, hur⟩, Subtype.ext (Subtype.ext hMapU)⟩

@[simp] theorem branchEquivAnchorComplement_apply
    (wallStar : W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩)
    (anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (hAnchor : nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
        anchorBlock) = 4)
    (v : {v : BranchVertex wd.cover // v.1 ≠ leftEnd m wd ∧ v.1 ≠ rightEnd m wd}) :
    (branchEquivAnchorComplement m wd wallStar anchorBlock hAnchor v).1.1 =
      sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v.1.1 := rfl

end Anchor

/-! ## 4.  (H-IV): the prescribed pairing move -/

section Move

variable (wallStar : W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne)
    ⟨wd.a, wd.hab⟩)
  (anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
  (hAnchor : nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
    (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
      anchorBlock) = 4)
  (pairing : Fin 3)

local notation "vSrc" =>
  (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc wd.hab wd.hOne
    wallStar (wd.hForest m) anchorBlock hAnchor)
local notation "vNG" =>
  (NonTrivalentUniqueFourValent.wall_noGlue wd.cover wd.fullDim wd.hc wd.hab wd.hOne
    (wd.hForest m))
local notation "vRam" =>
  (NonTrivalentUniqueFourValent.wall_ramification wd.cover wd.fullDim wd.hc wd.hab wd.hOne
    wallStar (wd.hForest m) anchorBlock)
local notation "vProf" =>
  (NonTrivalentUniqueFourValent.ordinaryBlockProfile_of_single_row wd.cover wd.fullDim wd.hc
    wd.hab wd.hOne wallStar (wd.hForest m) wd.coordinates (label m.base) wd.hRows
    wd.hZeroCoord anchorBlock hAnchor)
local notation "vConn" =>
  (NonTrivalentUniqueFourValent.wall_target_connected wd.cover wd.fullDim wd.hab wd.hOne)
local notation "vGen" =>
  (NonTrivalentUniqueFourValent.wall_target_genus wd.cover wd.fullDim wd.hab wd.hOne)
local notation "vVal" =>
  (NonTrivalentUniqueFourValent.wall_valid wd.cover wd.fullDim wd.hc wd.hab wd.hOne
    (wd.hForest m))
local notation "vGauged" =>
  (NonTrivalentValencyFourKZero.PrescribedPairing.gaugedData vSrc pairing vNG vRam)
local notation "vCand" =>
  (NonTrivalentValencyFourBackground.candidate vSrc pairing vNG vRam vProf vConn vGen vVal)
local notation "vEpv" =>
  (NonTrivalentValencyFourRows.endpointVertex vSrc pairing vNG vRam vProf vConn vGen vVal)

/-- The `A_1` end of the vanishing occurrence, as a branch vertex. -/
def leftBranch : BranchVertex wd.cover :=
  ⟨leftEnd m wd,
    three_le_nonDanglingValency_end m wd wallStar _ (incident_facetEdge_leftEnd m wd)⟩

/-- The `A_2` end of the vanishing occurrence, as a branch vertex. -/
def rightBranch : BranchVertex wd.cover :=
  ⟨rightEnd m wd,
    three_le_nonDanglingValency_end m wd wallStar _ (incident_facetEdge_rightEnd m wd)⟩

/-- The dart of the vanishing occurrence at the `A_1` end. -/
def facetDartLeft : StableSourceDarts.Dart wd.cover :=
  ⟨leftBranch m wd wallStar, ⟨facetEdge m wd, incident_facetEdge_leftEnd m wd⟩⟩

/-- The dart of the vanishing occurrence at the `A_2` end. -/
def facetDartRight : StableSourceDarts.Dart wd.cover :=
  ⟨rightBranch m wd wallStar, ⟨facetEdge m wd, incident_facetEdge_rightEnd m wd⟩⟩

/-- A surviving occurrence of the wall datum, read as a surviving occurrence of
the incoming cover. -/
def liftEdge (g : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    NonDanglingEdge wd.cover :=
  WallDegeneration.nonDanglingEmbedding wd.cover (wd.hCompat m).1 g

theorem stablePath_liftEdge (g : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    (liftEdge m wd g).stablePath =
      incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m)
        g.stablePath := rfl

/-- The label of one of the two target directions the prescribed pairing assigns
to a side. -/
def selectedLabel (side which : Bool) : Fin 4 :=
  if which then PrescribedPairing.secondLabel pairing side
  else PrescribedPairing.firstLabel pairing side

/-- One of the two survivors of the anchor on one side of the prescribed pairing,
read as a surviving occurrence of the incoming cover. -/
def selectedLift (side which : Bool) : NonDanglingEdge wd.cover :=
  liftEdge m wd ⟨(vSrc).sourceEdge (selectedLabel pairing side which),
    (vSrc).sourceEdge_survives _⟩

/-- **(H-IV), the per-vertex match at the anchor.**  The two darts that the
Whitehead move `m` places together with `m.base` -- that is, the moved star of
`graph.vert m.base` with `m.base` removed -- are the darts of the two survivors
of the anchor that `pairing` assigns to the side `false`, in the orientation that
puts `A_1` at `graph.vert m.base`: the first conjunct says that `m.base` is the
dart of the vanishing occurrence at the `A_1` end.

Side `false` is the side whose `K = 0` endpoint vertex is `vertexEquiv`'s image of
`graph.vert m.base` (`vertexEquiv_anchor_false`).  The other orientation is
normalised away by the caller with `CubicDartGraph.MoveData.swap`, which leaves
`graph.move m` unchanged (`CubicDartGraph.move_swap`) and exchanges `m.base` with
`graph.op m.base`. -/
def PrescribedPairingMove : Prop :=
  wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base ∧
    ∃ first second : StableSourceDarts.Dart wd.cover,
      first.2.1 = selectedLift m wd wallStar anchorBlock hAnchor pairing false false ∧
        second.2.1 = selectedLift m wd wallStar anchorBlock hAnchor pairing false true ∧
        (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
          {wd.tracks.iso.dart first, wd.tracks.iso.dart second}

/-- **The geometric content of a type change at a four-valent wall**: the two
survivors of the side the move collects lift to occurrences at the *two
different* ends of the vanishing occurrence.  Without it `A_1` sees exactly the
star of `leftEnd` and no Whitehead move takes place. -/
def SelectedSeparated : Prop :=
  Incident wd.cover (selectedLift m wd wallStar anchorBlock hAnchor pairing false false).1
      (leftEnd m wd) ∧
    Incident wd.cover (selectedLift m wd wallStar anchorBlock hAnchor pairing false true).1
      (rightEnd m wd)

theorem facetEdge_ne_selectedLift (side which : Bool) :
    (facetEdge m wd).1 ≠
      (selectedLift m wd wallStar anchorBlock hAnchor pairing side which).1 := by
  intro hBad
  refine incomingRow_ne_facet wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m)
    (wd.hForest m) wd.coordinates (label m.base) wd.hZeroCoord wd.hPosCoord wd.hFacetZero
    (NonDanglingEdge.stablePath
      (⟨(vSrc).sourceEdge (selectedLabel pairing side which), (vSrc).sourceEdge_survives _⟩ :
        NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))) ?_
  show NonDanglingEdge.stablePath
    (selectedLift m wd wallStar anchorBlock hAnchor pairing side which) = facetRow m wd
  rw [show selectedLift m wd wallStar anchorBlock hAnchor pairing side which =
    facetEdge m wd from Subtype.ext hBad.symm]
  exact facetEdge_stablePath m wd

/-- A third surviving occurrence at the `A_1` end, distinct from the vanishing
occurrence and from the side-`false` survivor there. -/
theorem exists_thirdEdge
    (hSep : SelectedSeparated m wd wallStar anchorBlock hAnchor pairing) :
    ∃ e : NonDanglingEdge wd.cover, Incident wd.cover e.1 (leftEnd m wd) ∧
      e ≠ facetEdge m wd ∧
      e ≠ selectedLift m wd wallStar anchorBlock hAnchor pairing false false := by
  classical
  have hNd : nonDanglingValency wd.cover (leftEnd m wd) = 3 :=
    nonDanglingValency_end_eq_three m wd wallStar _ (incident_facetEdge_leftEnd m wd)
  have hNe := facetEdge_ne_selectedLift m wd wallStar anchorBlock hAnchor pairing false false
  set pair : Finset wd.cover.SourceEdge :=
    {(facetEdge m wd).1,
      (selectedLift m wd wallStar anchorBlock hAnchor pairing false false).1} with hpair
  have hsub : pair ⊆ nonDanglingIncident wd.cover (leftEnd m wd) := by
    intro e he
    rw [hpair] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨(facetEdge m wd).2, incident_facetEdge_leftEnd m wd⟩
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨(selectedLift m wd wallStar anchorBlock hAnchor pairing false false).2, hSep.1⟩
  have hcard : (nonDanglingIncident wd.cover (leftEnd m wd) \ pair).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, card_nonDanglingIncident, hNd,
      hpair, Finset.card_pair hNe]
  obtain ⟨e, he⟩ := Finset.card_pos.mp
    (by omega : 0 < (nonDanglingIncident wd.cover (leftEnd m wd) \ pair).card)
  rw [Finset.mem_sdiff, hpair] at he
  obtain ⟨hMem, hNotMem⟩ := he
  obtain ⟨hSurv, hInc⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hNotMem
  exact ⟨⟨e, hSurv⟩, hInc, fun h ↦ hNotMem (Or.inl (congrArg Subtype.val h)),
    fun h ↦ hNotMem (Or.inr (congrArg Subtype.val h))⟩

/-- The third occurrence at the `A_1` end. -/
def thirdEdge (hSep : SelectedSeparated m wd wallStar anchorBlock hAnchor pairing) :
    NonDanglingEdge wd.cover :=
  Classical.choose (exists_thirdEdge m wd wallStar anchorBlock hAnchor pairing hSep)

theorem thirdEdge_spec
    (hSep : SelectedSeparated m wd wallStar anchorBlock hAnchor pairing) :
    Incident wd.cover (thirdEdge m wd wallStar anchorBlock hAnchor pairing hSep).1
        (leftEnd m wd) ∧
      thirdEdge m wd wallStar anchorBlock hAnchor pairing hSep ≠ facetEdge m wd ∧
      thirdEdge m wd wallStar anchorBlock hAnchor pairing hSep ≠
        selectedLift m wd wallStar anchorBlock hAnchor pairing false false :=
  Classical.choose_spec (exists_thirdEdge m wd wallStar anchorBlock hAnchor pairing hSep)

/-- The dart of the side-`false` survivor at the `A_1` end. -/
def selectedDartLeft (hSep : SelectedSeparated m wd wallStar anchorBlock hAnchor pairing) :
    StableSourceDarts.Dart wd.cover :=
  ⟨leftBranch m wd wallStar,
    ⟨selectedLift m wd wallStar anchorBlock hAnchor pairing false false, hSep.1⟩⟩

/-- The dart of the side-`false` survivor at the `A_2` end. -/
def selectedDartRight (hSep : SelectedSeparated m wd wallStar anchorBlock hAnchor pairing) :
    StableSourceDarts.Dart wd.cover :=
  ⟨rightBranch m wd wallStar,
    ⟨selectedLift m wd wallStar anchorBlock hAnchor pairing false true, hSep.2⟩⟩

/-- The remaining dart at the `A_1` end. -/
def thirdDart (hSep : SelectedSeparated m wd wallStar anchorBlock hAnchor pairing) :
    StableSourceDarts.Dart wd.cover :=
  ⟨leftBranch m wd wallStar, ⟨thirdEdge m wd wallStar anchorBlock hAnchor pairing hSep,
    (thirdEdge_spec m wd wallStar anchorBlock hAnchor pairing hSep).1⟩⟩

theorem facetDartLeft_ne_facetDartRight :
    facetDartRight m wd wallStar ≠ facetDartLeft m wd wallStar := by
  intro hBad
  exact (leftEnd_ne_rightEnd m wd)
    (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.1.1) hBad).symm

/-- The two darts of the vanishing occurrence are opposite. -/
theorem opposite_facetDartLeft :
    StableSourceDarts.opposite wd.cover wd.fullDim.connected wd.fullDim.pathEnds
        (facetDartLeft m wd wallStar) = facetDartRight m wd wallStar :=
  (StableSourceDarts.opposite_eq_of_row_eq wd.cover wd.fullDim.connected wd.fullDim.pathEnds
    (d := facetDartLeft m wd wallStar) (e := facetDartRight m wd wallStar) rfl
    (facetDartLeft_ne_facetDartRight m wd wallStar)).symm

/-- **Under (H-IV) the `A_1` end of the vanishing occurrence sits at
`graph.vert m.base`.** -/
theorem vert_base_eq
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base) :
    graph.vert m.base = wd.tracks.iso.vtx (leftBranch m wd wallStar) := by
  have h := wd.tracks.iso.vert_map (facetDartLeft m wd wallStar)
  rw [hBase] at h
  exact h

theorem op_base_eq
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base) :
    graph.op m.base = wd.tracks.iso.dart (facetDartRight m wd wallStar) := by
  have h2 := wd.tracks.iso.op_map (facetDartLeft m wd wallStar)
  have h3 : (StableSourceDarts.ofDatum wd.cover wd.fullDim.connected wd.fullDim.trivalent
      wd.fullDim.pathEnds).op (facetDartLeft m wd wallStar) =
      facetDartRight m wd wallStar := opposite_facetDartLeft m wd wallStar
  rw [hBase, h3] at h2
  exact h2

/-- **Under (H-IV) the `A_2` end sits at `graph.vert (graph.op m.base)`.** -/
theorem vert_opBase_eq
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base) :
    graph.vert (graph.op m.base) = wd.tracks.iso.vtx (rightBranch m wd wallStar) := by
  rw [op_base_eq m wd wallStar hBase]
  exact wd.tracks.iso.vert_map (facetDartRight m wd wallStar)

/-- **The Whitehead move prescribed by the two side-`false` survivors.**  It
contracts the edge of `m.base` and exchanges the survivor at the `A_2` end with
the remaining dart at the `A_1` end. -/
def prescribedMove (hSep : SelectedSeparated m wd wallStar anchorBlock hAnchor pairing)
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base) : graph.MoveData where
  base := m.base
  left := wd.tracks.iso.dart (thirdDart m wd wallStar anchorBlock hAnchor pairing hSep)
  right :=
    wd.tracks.iso.dart (selectedDartRight m wd wallStar anchorBlock hAnchor pairing hSep)
  nonloop := m.nonloop
  left_vert :=
    (wd.tracks.iso.vert_map (thirdDart m wd wallStar anchorBlock hAnchor pairing hSep)).trans
      (vert_base_eq m wd wallStar hBase).symm
  left_ne := by
    intro hBad
    exact (thirdEdge_spec m wd wallStar anchorBlock hAnchor pairing hSep).2.1
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1)
        (wd.tracks.iso.dart.injective (hBad.trans hBase.symm)))
  right_vert :=
    (wd.tracks.iso.vert_map
      (selectedDartRight m wd wallStar anchorBlock hAnchor pairing hSep)).trans
      (vert_opBase_eq m wd wallStar hBase).symm
  right_ne := by
    intro hBad
    exact (facetEdge_ne_selectedLift m wd wallStar anchorBlock hAnchor pairing false true)
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1.1)
        (wd.tracks.iso.dart.injective
          (hBad.trans (op_base_eq m wd wallStar hBase)))).symm

/-- **Non-vacuity of (H-IV), in relative form.**  At a wall of the outer walk
whose vanishing occurrence is oriented with its `A_1` end at `graph.vert m.base`
and whose two side-`false` survivors sit at the two different ends, the Whitehead
move `prescribedMove` -- which contracts the *same* edge as `m` -- satisfies
(H-IV).  This is the precise sense in which (H-IV) only normalises the choice of
`left` and `right` in the move: it is the separation `SelectedSeparated` that is
geometric. -/
theorem prescribedPairingMove_prescribedMove
    (hSep : SelectedSeparated m wd wallStar anchorBlock hAnchor pairing)
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base) :
    PrescribedPairingMove (prescribedMove m wd wallStar anchorBlock hAnchor pairing hSep
      hBase) wd wallStar anchorBlock hAnchor pairing := by
  classical
  set m' := prescribedMove m wd wallStar anchorBlock hAnchor pairing hSep hBase with hm'
  set dLeft := selectedDartLeft m wd wallStar anchorBlock hAnchor pairing hSep with hdLeft
  set dRight := selectedDartRight m wd wallStar anchorBlock hAnchor pairing hSep with hdRight
  have hLeftNeRight : dLeft ≠ dRight := by
    intro hBad
    exact (leftEnd_ne_rightEnd m wd)
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.1.1) hBad)
  have hLeftNeThird : dLeft ≠ thirdDart m wd wallStar anchorBlock hAnchor pairing hSep := by
    intro hBad
    exact (thirdEdge_spec m wd wallStar anchorBlock hAnchor pairing hSep).2.2
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1) hBad).symm
  have hBaseNeLeft : m.base ≠ wd.tracks.iso.dart dLeft := by
    intro hBad
    exact (facetEdge_ne_selectedLift m wd wallStar anchorBlock hAnchor pairing false false)
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1.1)
        (wd.tracks.iso.dart.injective (hBase.trans hBad)))
  have hBaseNeRight : m.base ≠ wd.tracks.iso.dart dRight := by
    intro hBad
    exact (facetEdge_ne_selectedLift m wd wallStar anchorBlock hAnchor pairing false true)
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


/-! ## 5.  The vertex dictionary of the type change -/

/-- The two ends of the vanishing occurrence complete the branch vertices of
the incoming cover. -/
def coverBranchMap :
    ({v : BranchVertex wd.cover // v.1 ≠ leftEnd m wd ∧ v.1 ≠ rightEnd m wd} ⊕ Bool) →
      BranchVertex wd.cover
  | Sum.inl v => v.1
  | Sum.inr side => if side then rightBranch m wd wallStar else leftBranch m wd wallStar

/-- The two ends of the vanishing occurrence complete the branch vertices of
the incoming cover. -/
def coverBranchEquiv :
    ({v : BranchVertex wd.cover // v.1 ≠ leftEnd m wd ∧ v.1 ≠ rightEnd m wd} ⊕ Bool) ≃
      BranchVertex wd.cover := by
  classical
  refine Equiv.ofBijective (coverBranchMap m wd wallStar) ⟨?_, ?_⟩
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

/-- **The vertex dictionary of the valency-four `K = 0` type change.**  Away from
the anchor it is the branch vertex of the gauged wall datum, read back through
the block-preserving branch gauge, then through the branch dictionary of the wall
contraction, then through the incoming tracking; the two `K = 0` endpoint
vertices `A_1` and `A_2` go to the two ends of the vanishing occurrence. -/
def vertexEquiv : BranchVertex (vCand).datum ≃ V :=
  ((candBranchEquiv wd.cover wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hForest m)
      wd.coordinates (label m.base) wd.hRows wd.hZeroCoord anchorBlock hAnchor
      pairing).symm.trans
    (Equiv.sumCongr
      ((gaugeBranchEquivAnchorComplement wd.cover wd.fullDim wd.hc wd.hab wd.hOne wallStar
          (wd.hForest m) anchorBlock hAnchor pairing).symm.trans
        (branchEquivAnchorComplement m wd wallStar anchorBlock hAnchor).symm)
      (Equiv.refl Bool))).trans
    ((coverBranchEquiv m wd wallStar).trans wd.tracks.iso.vtx)

@[simp] theorem vertexEquiv_inl
    (w : {w : BranchVertex (vGauged) //
      w.1 ≠ gaugedAnchorVertex wd.cover wd.fullDim wd.hc wd.hab wd.hOne wallStar
        (wd.hForest m) anchorBlock hAnchor pairing}) :
    vertexEquiv m wd wallStar anchorBlock hAnchor pairing
        (candBranchMap wd.cover wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hForest m)
          wd.coordinates (label m.base) wd.hRows wd.hZeroCoord anchorBlock hAnchor pairing
          (Sum.inl w)) =
      wd.tracks.iso.vtx ((branchEquivAnchorComplement m wd wallStar anchorBlock hAnchor).symm
        ((gaugeBranchEquivAnchorComplement wd.cover wd.fullDim wd.hc wd.hab wd.hOne wallStar
          (wd.hForest m) anchorBlock hAnchor pairing).symm w)).1 := by
  have h : (candBranchEquiv wd.cover wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hForest m)
      wd.coordinates (label m.base) wd.hRows wd.hZeroCoord anchorBlock hAnchor pairing).symm
      (candBranchMap wd.cover wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hForest m)
        wd.coordinates (label m.base) wd.hRows wd.hZeroCoord anchorBlock hAnchor pairing
        (Sum.inl w)) = Sum.inl w :=
    (candBranchEquiv wd.cover wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hForest m)
      wd.coordinates (label m.base) wd.hRows wd.hZeroCoord anchorBlock hAnchor
      pairing).symm_apply_apply (Sum.inl w)
  show wd.tracks.iso.vtx (coverBranchMap m wd wallStar
    (Equiv.sumCongr
      ((gaugeBranchEquivAnchorComplement wd.cover wd.fullDim wd.hc wd.hab wd.hOne wallStar
          (wd.hForest m) anchorBlock hAnchor pairing).symm.trans
        (branchEquivAnchorComplement m wd wallStar anchorBlock hAnchor).symm)
      (Equiv.refl Bool)
      ((candBranchEquiv wd.cover wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hForest m)
        wd.coordinates (label m.base) wd.hRows wd.hZeroCoord anchorBlock hAnchor
        pairing).symm
        (candBranchMap wd.cover wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hForest m)
          wd.coordinates (label m.base) wd.hRows wd.hZeroCoord anchorBlock hAnchor pairing
          (Sum.inl w))))) = _
  rw [h]
  rfl

@[simp] theorem vertexEquiv_anchor (side : Bool) :
    vertexEquiv m wd wallStar anchorBlock hAnchor pairing
        (candBranchMap wd.cover wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hForest m)
          wd.coordinates (label m.base) wd.hRows wd.hZeroCoord anchorBlock hAnchor pairing
          (Sum.inr side)) =
      wd.tracks.iso.vtx (if side then rightBranch m wd wallStar else leftBranch m wd wallStar) := by
  have h : (candBranchEquiv wd.cover wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hForest m)
      wd.coordinates (label m.base) wd.hRows wd.hZeroCoord anchorBlock hAnchor pairing).symm
      (candBranchMap wd.cover wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hForest m)
        wd.coordinates (label m.base) wd.hRows wd.hZeroCoord anchorBlock hAnchor pairing
        (Sum.inr side)) = Sum.inr side :=
    (candBranchEquiv wd.cover wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hForest m)
      wd.coordinates (label m.base) wd.hRows wd.hZeroCoord anchorBlock hAnchor
      pairing).symm_apply_apply (Sum.inr side)
  show wd.tracks.iso.vtx (coverBranchMap m wd wallStar
    (Equiv.sumCongr
      ((gaugeBranchEquivAnchorComplement wd.cover wd.fullDim wd.hc wd.hab wd.hOne wallStar
          (wd.hForest m) anchorBlock hAnchor pairing).symm.trans
        (branchEquivAnchorComplement m wd wallStar anchorBlock hAnchor).symm)
      (Equiv.refl Bool)
      ((candBranchEquiv wd.cover wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hForest m)
        wd.coordinates (label m.base) wd.hRows wd.hZeroCoord anchorBlock hAnchor
        pairing).symm
        (candBranchMap wd.cover wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hForest m)
          wd.coordinates (label m.base) wd.hRows wd.hZeroCoord anchorBlock hAnchor pairing
          (Sum.inr side))))) = _
  rw [h]
  rfl

/-- **`A_1` goes to `graph.vert m.base`.**  This is the anchor half of the vertex
dictionary, in the orientation (H-IV) prescribes. -/
theorem vertexEquiv_anchor_false
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base) :
    vertexEquiv m wd wallStar anchorBlock hAnchor pairing
        (candBranchMap wd.cover wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hForest m)
          wd.coordinates (label m.base) wd.hRows wd.hZeroCoord anchorBlock hAnchor pairing
          (Sum.inr false)) = graph.vert m.base := by
  rw [vertexEquiv_anchor m wd wallStar anchorBlock hAnchor pairing false,
    vert_base_eq m wd wallStar hBase]
  rfl

/-- **`A_2` goes to `graph.vert (graph.op m.base)`.** -/
theorem vertexEquiv_anchor_true
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base) :
    vertexEquiv m wd wallStar anchorBlock hAnchor pairing
        (candBranchMap wd.cover wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hForest m)
          wd.coordinates (label m.base) wd.hRows wd.hZeroCoord anchorBlock hAnchor pairing
          (Sum.inr true)) = graph.vert (graph.op m.base) := by
  rw [vertexEquiv_anchor m wd wallStar anchorBlock hAnchor pairing true,
    vert_opBase_eq m wd wallStar hBase]
  rfl


/-! ## 7.  The link, reduced to the star count -/

/-- **`OuterWalk.TypeChangeLink` at a four-valent wall, from the star count
alone.** `typeChangeLink_of_receipts` has one receipt, `tracks`, and
`MovedIncidenceIso.tracksOfMovedIncidence` reduces it to a branch-vertex
bijection and a star count against the permuted vertex map. With `vertexEquiv`
supplying the bijection, exactly one geometric input is left: the star count
`hIncidence`. At a branch vertex away from the anchor it is the composite of the
three transports (T1), (T2) and (T3) of the module docstring, and at `A_1`/`A_2`
it is what (H-IV) prescribes together with the exact anchor stars of
`NonTrivalentValencyFourDictionary`. -/
def typeChangeLink_of_incidence
    (hIncidence : ∀ (v : BranchVertex (vCand).datum) (r : StablePath (vCand).datum),
      incidenceCount (vCand).datum v.1 r =
        Nat.card {d : D // graph.vert (m.perm d) =
            vertexEquiv m wd wallStar anchorBlock hAnchor pairing v ∧
          label d = (NonTrivalentValencyFourExit.wallOutgoingFD m wd wallStar anchorBlock
            hAnchor pairing).labelling.row r}) :
    TypeChangeLink m wd :=
  NonTrivalentValencyFourExit.typeChangeLink_of_receipts m wd wallStar anchorBlock hAnchor
    pairing
    (MovedIncidenceIso.tracksOfMovedIncidence _ _ graph m label
      (vertexEquiv m wd wallStar anchorBlock hAnchor pairing)
      (MovedIncidenceIso.label_op_of_tracks _ wd.fullDim wd.tracks) hIncidence)

end Move

/-! ## 6.  Two further pieces of the star count

These two need no anchor data, so they are stated outside `section Move`, after
Section 7. -/

/-- **Away from the two ends of the vanishing occurrence the Whitehead move does
not change the star.**  The permutation `m.perm` is the transposition of `m.left`
and `m.right`, whose vertices are the two ends themselves. -/
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
ambient graph.**  This is `MovedIncidenceIso.DatumGraphIncidence.ofIso` applied
to the incoming tracking, with the row label read through the chart. -/
theorem card_star_eq_incidenceCount (u : BranchVertex wd.cover)
    (row : StablePath wd.cover) :
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

end Walk

end

end DraismaVargas.LocalCases.NonTrivalentValencyFourTracks
