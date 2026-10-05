module

public import DraismaVargas.LocalCases.NonTrivalentValencyFourExit

@[expose] public section

/-!
# The valency-four `K = 0` exit: path ends, and the type-change link

Source: Vargas, Part II (arXiv:2609.09109), Section 5.1 and Section 5.2
(Case `{v4-nd4}`), together with Draisma--Vargas Part I (arXiv:1909.12924),
the construction of the stable graph `H(M)` in Section 3.

This is the second half of the valency-four exit.  `NonTrivalentValencyFourExit`
builds the outgoing honest labelling on the incoming chart, the common minor, the
nonsingularity, the outgoing target facts and the trivalence of the `K = 0`
candidate, and reduces `W4StableSource.HasPathEnds` of the candidate to its
retained rows.  This file discharges that reduction and assembles
`OuterWalk.TypeChangeLink`.

## What is proved here

* **`HasPathEnds` of the gauged wall datum** (`hasPathEnds_gauged`).
  `WallDatumPathEnds.hasPathEnds_contractDatum_of_noContractedReturn` -- whose
  `NoContractedReturn` input is free at a four-valent wall
  (`StablePathFacetContraction.noContractedReturn_of_fourStar`) -- transported
  along the block-preserving branch gauge by
  `StableGraphIncidence.hasPathEnds_sheetRelabel`.

* **The transport of a path end to the candidate**, in three halves.  Away from
  the wall `ResolutionAwayFromWall` keeps the surviving valency
  (`hasPathEnds_candidate_of_ordinary`'s last branch).  At the anchor
  (`exists_isPathEnd_anchor`) the retained copy of a survivor meets the endpoint
  vertex on the side the prescribed pairing assigns to its branch, and that
  vertex is trivalent: on the non-smaller side the endpoint partition is the
  whole old wall block, and on the smaller side a sheet outside the selected
  fine class carries no retained survivor at all
  (`NonTrivalentValencyFourDictionary.nonDanglingIncident_singleton_subset`).

* **The non-anchor block half** (`exists_isPathEnd_ordinary`), the mathematical
  content of this file.  A block met by a path end of the gauged datum has
  exactly three survivors (`block_valency_eq_three`: zero and two are excluded
  by hypothesis, one by `NonDanglingValency.nonDanglingValency_ne_one`, four by
  the census `gauged_valency_of_single_row`), and a `2 + 2` pairing puts at most
  two of them on a side (`eq_of_three_on_side`).  Two cases:
  - **every fine-side survivor is alone in its new-edge class**
    (`nonDanglingValency_ret_eq_three_of_unique`,
    `exists_isPathEnd_ordinary_unique`): then each fine class with a survivor
    has a surviving new occurrence
    (`newSourceEdge_survives_of_unique_fine_survivor`), the three survivors name
    three distinct objects at the retaining endpoint, so it is trivalent; a
    retaining-side survivor ends there directly and a fine-side survivor
    reaches it along its own new occurrence, which lies on its row
    (`stablePath_newSourceEdge_eq`);
  - **two distinct fine-side survivors share a new-edge class**
    (`exists_isPathEnd_ordinary_pair`): then the block has exactly one
    retaining-side survivor, the retaining endpoint is divalent, its second
    object is the single surviving new occurrence of that class -- surviving
    because a retaining endpoint cannot have surviving valency one -- and the
    common fine endpoint carries the two fine survivors together with that new
    occurrence, so it is trivalent.  A fine-side survivor ends there directly;
    the retaining-side survivor crosses the divalent retaining endpoint along
    the new occurrence, which is therefore on its row.

* `hasPathEnds_candidate`: **`HasPathEnds` of the `K = 0` candidate at an actual
  four-valent wall, with no receipt.**

* `outgoingFD`: the outgoing `FullDimensionalSourcePresentation` on the incoming
  `coordinate`, with **no** remaining geometric receipt.

* `exists_anchor_of_wallData`: the four-valent target star, the anchor block
  with surviving valency four and the validity of the `K = 0` candidate over the
  branch gauge, at an actual four-valent wall of the outer walk, with no
  receipt.

* `wallOutgoingFD` and `typeChangeLink_of_receipts`: an inhabitant of
  `OuterWalk.TypeChangeLink` at a four-valent wall.  Its `base` is **not** the
  wall datum but the block-preserving branch gauge
  `NonTrivalentValencyFourKZero.PrescribedPairing.gaugedData`, and
  `baseValid` is that gauge's validity.

* `nonempty_typeChangeLink_of_tracks`: the same statement with the star, the
  anchor block and its valency four produced from the valency hypothesis
  `h4` alone, so that the **only** remaining inputs at a four-valent wall are
  the prescribed `pairing` and the dart-level `tracks`.

## Hypotheses left explicit here

1. `pairing : Fin 3`.  By design: the exit takes the `2 + 2` resolution
   prescribed by the move as an input.  Everything else about the wall is
   derived from the wall data.
2. `tracks : InteriorGraphTracking.Tracks (wallOutgoingFD ...) (graph.move m) label`.
   The dart-level dictionary between the candidate's stable graph and the
   Whitehead move of the tracked ambient graph.  Its `row_map` half is
   `NonTrivalentValencyFourExit.outLabelling_row_bridge` /
   `outLabelling_row_retained`; the dart/vertex half uses the generic
   wall-crossing tracking infrastructure (`WallSplitIncidence`) and is supplied
   by `NonTrivalentValencyFourTracks.vertexEquiv` under **(H-IV)**: *the two darts
   that `m.perm` places with `m.base` are, under the incoming tracking, the
   darts of the two survivors of the anchor block that `pairing` assigns to
   the side whose `K = 0` endpoint vertex is mapped to `vert m.base`* -- the
   valency-four analogue of the hypothesis (H-III) of
   `NonTrivalentValencyThreeTracks`, with
   `NonTrivalentValencyFourKZero.PrescribedPairing.firstSelectedLabel` and
   `secondSelectedLabel` naming the two survivors on the smaller side and
   `W4TargetPairings.Pairing.labelsOnSide` naming them on the other.  (H-IV)'s
   star count is `NonTrivalentValencyFourStarCount`, and
   `NonTrivalentValencyFourDispatcher` derives (H-IV) and `pairing` from the
   move itself, so a caller going through that dispatcher supplies neither of
   this file's two inputs, `pairing` and `tracks`.

Nothing else is needed: `hPathEnds` is discharged here, `NoContractedReturn` is
free at valency four, and the anchor, the census, the background and the row
equivalence are all receipt-free at an actual wall.

Nothing here identifies a graph by a matrix, and no new structure is
introduced, so there is nothing to witness for non-vacuity beyond the
definitions themselves, each of which is applied.

## Consumers

`OuterWalk.TypeChangeLink` (hence the `link` hypothesis of
`OuterWalk.coneEntry_of_reaches`) at Part II Case `{v4-nd4}`.
`NonTrivalentValencyFourDispatcher.typeChangeLink_four` composes this file's
`nonempty_typeChangeLink_of_tracks` with the `tracks` of
`NonTrivalentValencyFourTracks` and the star count of
`NonTrivalentValencyFourStarCount` to discharge the whole `{v4-nd4}` branch
unconditionally, from the wall valency alone.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyFourExit

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero.PrescribedPairing
open DraismaVargas.LocalCases.NonTrivalentValencyFourRows
open DraismaVargas.LocalCases.NonTrivalentValencyFourDictionary

noncomputable section

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
  (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
    0 < coordinates column)
  (hFacetZero :
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates facet = 0)

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
local notation "wCompat" =>
  (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne hForest)
local notation "wNoRet" =>
  (StablePathFacetContraction.noContractedReturn_of_fourStar cover fd hc hab hOne wallStar)
local notation "wGauged" =>
  (NonTrivalentValencyFourKZero.PrescribedPairing.gaugedData wSrc pairing wNG wRam)
local notation "wCand" =>
  (NonTrivalentValencyFourBackground.candidate wSrc pairing wNG wRam wProf wConn wGen wVal)
local notation "wRowEq" =>
  (NonTrivalentValencyFourRetainedInjective.rowEquiv_of_single_row cover fd hc hab hOne
    wallStar hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing)
local notation "wEpv" =>
  (NonTrivalentValencyFourRows.endpointVertex wSrc pairing wNG wRam wProf wConn wGen wVal)
local notation "wRetSide" =>
  (NonTrivalentValencyFourRowEquiv.retSide wSrc pairing wNG wRam wProf)
local notation "wWallLab" =>
  (NonTrivalentValencyTwoExit.wallLab cover fd hc hab hOne hForest wNoRet coordinates facet
    hRows hZeroCoord hPosCoord hFacetZero)

/-! ### The non-anchor block half of the path-end transport -/

/-- The block vertex of a sheet, read as the sheet's own wall endpoint. -/
theorem blockVertex_eq (x : Fin deg) :
    WallBlock.sourceVertex (wGauged) (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)
        (WallBlock.ofSheet (wGauged) (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x) =
      (wGauged).sourceEndpoint (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x :=
  sourceEndpoint_eq_of_rel
    ((((wGauged).vertexPartition
      (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).rel_repr_left x))

/-- Membership in the surviving star of a wall block, in occurrence form. -/
theorem mem_block_star {x : Fin deg} {z : (wGauged).SourceEdge}
    (hz : ¬ IsDangling (wGauged) z)
    (hAt : z.1.1 ∈ GluingDatum.incidentEdges
      (⟨a, hab⟩ : GraphContraction.Vertex targetIn b))
    (hRel : ((wGauged).vertexPartition
      (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).Rel x z.1.2) :
    z ∈ nonDanglingIncident (wGauged)
      ((wGauged).sourceEndpoint (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x) :=
  (mem_nonDanglingIncident _ _ _).mpr ⟨hz,
    (incident_iff_target_mem_and_rel (wGauged) z _).mpr ⟨hAt,
      ((((wGauged).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).rel_repr_left x).trans hRel)⟩⟩

theorem block_star_mem {x : Fin deg} {z : (wGauged).SourceEdge}
    (hz : z ∈ nonDanglingIncident (wGauged)
      ((wGauged).sourceEndpoint (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x)) :
    ¬ IsDangling (wGauged) z ∧
      z.1.1 ∈ GluingDatum.incidentEdges
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) ∧
      ((wGauged).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).Rel x z.1.2 := by
  obtain ⟨hSurv, hInc⟩ := (mem_nonDanglingIncident _ _ _).mp hz
  obtain ⟨hAt, hRel⟩ := (incident_iff_target_mem_and_rel (wGauged) z _).mp hInc
  exact ⟨hSurv, hAt,
    ((((wGauged).vertexPartition
      (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).rel_repr_right x).trans hRel)⟩

include hRows hZeroCoord in
/-- **A non-anchor wall block met by a path end of the gauged datum has exactly
three survivors.**  Zero and two are excluded by hypothesis, one by
`NonDanglingValency.nonDanglingValency_ne_one`, and four by the census. -/
theorem block_valency_eq_three (x : Fin deg) (h : NonDanglingEdge (wGauged))
    (hb : ¬ ((wGauged).vertexPartition
      (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).Rel anchorBlock.1 x)
    (hInc : Incident (wGauged) h.1
      ((wGauged).sourceEndpoint (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x))
    (hNd : nonDanglingValency (wGauged)
      ((wGauged).sourceEndpoint (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x) ≠ 2) :
    nonDanglingValency (wGauged)
      ((wGauged).sourceEndpoint (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x) = 3 := by
  have hLe : nonDanglingValency (wGauged)
      ((wGauged).sourceEndpoint (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x) ≤ 3 := by
    rw [← blockVertex_eq cover fd hc hab hOne wallStar hForest anchorBlock hAnchor pairing x]
    exact NonTrivalentValencyFourRowEquivFinal.gauged_valency_of_single_row cover fd hc hab
      hOne wallStar hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing
      x hb
  have hNe0 : nonDanglingValency (wGauged)
      ((wGauged).sourceEndpoint (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x) ≠ 0 :=
    ClassInjectivity.nonDanglingValency_ne_zero_of_incident (wGauged) h.2 hInc
  have hNe1 := NonDanglingValency.nonDanglingValency_ne_one (wGauged)
    (gaugedData_valid wSrc pairing wNG wRam wVal).1
    ((wGauged).sourceEndpoint (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x)
  omega

theorem bool_ne_iff_eq_not {x y : Bool} : x ≠ y ↔ x = !y :=
  ⟨NonTrivalentValencyFourRowDictionary.bool_eq_not_of_ne,
    by rintro rfl; exact Bool.not_ne_self y⟩

include hRows hZeroCoord in
/-- **The retaining endpoint of a non-anchor block is trivalent when every
fine-side survivor of the block is alone in its new-edge class.**  The block's
three survivors then name three distinct objects there: the retained copies of
the retaining-side survivors and the surviving new occurrence of each fine
class. -/
theorem nonDanglingValency_ret_eq_three_of_unique (x : Fin deg)
    (hb : ¬ ((wGauged).vertexPartition
      (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).Rel anchorBlock.1 x)
    (hThree : nonDanglingValency (wGauged)
      ((wGauged).sourceEndpoint (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x) = 3)
    (hUniq : ∀ z z' : (wGauged).SourceEdge,
      z ∈ nonDanglingIncident (wGauged)
        ((wGauged).sourceEndpoint (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x) →
      z' ∈ nonDanglingIncident (wGauged)
        ((wGauged).sourceEndpoint (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x) →
      wallStar.right pairing z.1.1 = !wRetSide (((wGauged).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x) →
      wallStar.right pairing z'.1.1 = !wRetSide (((wGauged).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x) →
      (W4Assembly.blockwiseResolution (wGauged) wallStar (wProf).pattern pairing
        (((wGauged).vertexPartition
          (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x)).newEdge.Rel z.1.2 z'.1.2 →
      z = z') :
    nonDanglingValency (wCand).datum
      (wEpv (wRetSide (((wGauged).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x)) x) = 3 := by
  classical
  refine le_antisymm (nonDanglingValency_ret_le cover fd hc hab hOne wallStar hForest
    coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing x hb) ?_
  rw [← card_nonDanglingIncident, ← hThree, ← card_nonDanglingIncident]
  refine Finset.card_le_card_of_injOn (fun z : (wGauged).SourceEdge ↦
    if wallStar.right pairing z.1.1 = wRetSide (((wGauged).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x) then
      (wCand).oldSourceEdge z else (wCand).newSourceEdge z.1.2) ?_ ?_
  · intro z hz
    obtain ⟨hzS, hzA, hzR⟩ := block_star_mem cover fd hc hab hOne wallStar hForest
      anchorBlock hAnchor pairing hz
    have hbz : ¬ ((wGauged).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).Rel anchorBlock.1 z.1.2 :=
      fun hBad ↦ hb (hBad.trans hzR.symm)
    have hReprZ : ((wGauged).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr z.1.2 =
        ((wGauged).vertexPartition
          (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x := hzR.symm
    by_cases hSide : wallStar.right pairing z.1.1 = wRetSide (((wGauged).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x)
    · simp only [ite_eq_left hSide]
      exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨ResolutionSurvival.not_isDangling_oldSourceEdge (wCand)
          (gaugedData_valid wSrc pairing wNG wRam wVal).1 _ hzS,
        NonTrivalentValencyFourRowDictionary.oldSourceEdge_incident_ret wSrc pairing wNG wRam
          wProf wConn wGen wVal hb hzA hzR hSide⟩
    · simp only [ite_eq_right hSide]
      have hSurv :=
        (NonTrivalentValencyFourRowEquiv.newSourceEdge_survives_of_unique_fine_survivor
          wSrc pairing wNG wRam wProf wConn wGen wVal hbz hzS hzA
          (by rw [hReprZ]; exact bool_ne_iff_eq_not.mp hSide) rfl
          (by
            intro other hOtherS hOtherA hOtherSide hOtherRel
            rw [hReprZ] at hOtherSide hOtherRel
            refine hUniq other z ?_ hz hOtherSide (bool_ne_iff_eq_not.mp hSide)
              hOtherRel.symm
            exact mem_block_star cover fd hc hab hOne wallStar hForest anchorBlock hAnchor
              pairing hOtherS hOtherA
              (hzR.trans ((NonTrivalentValencyFourDescent.blockRes_newEdge_refines wSrc
                pairing wNG wRam wProf _).rel hOtherRel)))).1
      exact (mem_nonDanglingIncident _ _ _).mpr ⟨hSurv,
        NonTrivalentValencyFourRowDictionary.newSourceEdge_incident_ret wSrc pairing wNG wRam
          wProf wConn wGen wVal hb hzR⟩
  · intro z hz z' hz' hEq
    simp only at hEq
    obtain ⟨hzS, hzA, hzR⟩ := block_star_mem cover fd hc hab hOne wallStar hForest
      anchorBlock hAnchor pairing hz
    obtain ⟨hzS', hzA', hzR'⟩ := block_star_mem cover fd hc hab hOne wallStar hForest
      anchorBlock hAnchor pairing hz'
    by_cases hSide : wallStar.right pairing z.1.1 = wRetSide (((wGauged).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x)
    · by_cases hSide' : wallStar.right pairing z'.1.1 = wRetSide (((wGauged).vertexPartition
          (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x)
      · rw [ite_eq_left hSide, ite_eq_left hSide'] at hEq
        exact ResolutionCut.oldSourceEdge_injective (wCand) hEq
      · rw [ite_eq_left hSide, ite_eq_right hSide'] at hEq
        exact absurd hEq (NonTrivalentValencyFourRowDictionary.new_ne_old wSrc pairing
          wNG wRam wProf wConn wGen wVal z'.1.2 z)
    · by_cases hSide' : wallStar.right pairing z'.1.1 = wRetSide (((wGauged).vertexPartition
          (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x)
      · rw [ite_eq_right hSide, ite_eq_left hSide'] at hEq
        exact absurd hEq (NonTrivalentValencyFourRowDictionary.new_ne_old wSrc pairing
          wNG wRam wProf wConn wGen wVal z.1.2 z').symm
      · rw [ite_eq_right hSide, ite_eq_right hSide'] at hEq
        have hbz : ¬ ((wGauged).vertexPartition
            (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).Rel anchorBlock.1 z.1.2 :=
          fun hBad ↦ hb (hBad.trans hzR.symm)
        have hReprZ : ((wGauged).vertexPartition
            (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr z.1.2 =
            ((wGauged).vertexPartition
              (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x := hzR.symm
        have hRel := (NonTrivalentValencyFourRowEquiv.candidate_newEdge_rel_block wSrc pairing
          wNG wRam wProf wConn wGen wVal hbz z'.1.2).mp
          (NonTrivalentValencyFourRowDictionary.newSourceEdge_rel_of_eq wSrc pairing wNG wRam
            wProf wConn wGen wVal hEq)
        rw [hReprZ] at hRel
        exact hUniq z z' hz hz' (bool_ne_iff_eq_not.mp hSide) (bool_ne_iff_eq_not.mp hSide')
          hRel

include hRows hZeroCoord in
/-- **Case I of the non-anchor transport**: when every fine-side survivor of the
block is alone in its new-edge class, the retaining endpoint is trivalent, and a
survivor reaches it either directly (retaining side) or through its own new
occurrence (fine side). -/
theorem exists_isPathEnd_ordinary_unique (x : Fin deg) (h : NonDanglingEdge (wGauged))
    (hb : ¬ ((wGauged).vertexPartition
      (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).Rel anchorBlock.1 x)
    (hMem : h.1 ∈ nonDanglingIncident (wGauged)
      ((wGauged).sourceEndpoint (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x))
    (hThree : nonDanglingValency (wGauged)
      ((wGauged).sourceEndpoint (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x) = 3)
    (hUniq : ∀ z z' : (wGauged).SourceEdge,
      z ∈ nonDanglingIncident (wGauged)
        ((wGauged).sourceEndpoint (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x) →
      z' ∈ nonDanglingIncident (wGauged)
        ((wGauged).sourceEndpoint (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x) →
      wallStar.right pairing z.1.1 = !wRetSide (((wGauged).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x) →
      wallStar.right pairing z'.1.1 = !wRetSide (((wGauged).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x) →
      (W4Assembly.blockwiseResolution (wGauged) wallStar (wProf).pattern pairing
        (((wGauged).vertexPartition
          (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x)).newEdge.Rel z.1.2 z'.1.2 →
      z = z') :
    ∃ (first : NonDanglingEdge (wCand).datum) (vertex : (wCand).datum.SourceVertex),
      first.stablePath = (ResolutionAwayFromWall.retainedEdge (wCand)
          (gaugedData_valid wSrc pairing wNG wRam wVal).1 h).stablePath ∧
        IsPathEnd (wCand).datum first.1 vertex := by
  classical
  obtain ⟨hS, hA, hR⟩ := block_star_mem cover fd hc hab hOne wallStar hForest anchorBlock
    hAnchor pairing hMem
  have hRet3 := nonDanglingValency_ret_eq_three_of_unique cover fd hc hab hOne wallStar
    hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing x hb hThree hUniq
  by_cases hSide : wallStar.right pairing h.1.1.1 = wRetSide (((wGauged).vertexPartition
      (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x)
  · refine ⟨ResolutionAwayFromWall.retainedEdge (wCand) _ h,
      wEpv (wRetSide (((wGauged).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x)) x, rfl,
      NonTrivalentValencyFourRowDictionary.oldSourceEdge_incident_ret wSrc pairing wNG wRam
        wProf wConn wGen wVal hb hA hR hSide, ?_⟩
    rw [hRet3]
    omega
  · have hbz : ¬ ((wGauged).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).Rel anchorBlock.1 h.1.1.2 :=
      fun hBad ↦ hb (hBad.trans hR.symm)
    have hReprZ : ((wGauged).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr h.1.1.2 =
        ((wGauged).vertexPartition
          (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x := hR.symm
    have hSideFine : wallStar.right pairing h.1.1.1 = !wRetSide (((wGauged).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr h.1.1.2) := by
      rw [hReprZ]
      exact bool_ne_iff_eq_not.mp hSide
    have hUniqLocal : ∀ other : (wGauged).SourceEdge, ¬ IsDangling (wGauged) other →
        other.1.1 ∈ GluingDatum.incidentEdges
          (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) →
        wallStar.right pairing other.1.1 = !wRetSide (((wGauged).vertexPartition
          (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr h.1.1.2) →
        (W4Assembly.blockwiseResolution (wGauged) wallStar (wProf).pattern pairing
          (((wGauged).vertexPartition
            (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr h.1.1.2)).newEdge.Rel
          h.1.1.2 other.1.2 → other = h.1 := by
      intro other hOtherS hOtherA hOtherSide hOtherRel
      rw [hReprZ] at hOtherSide hOtherRel
      refine hUniq other h.1 ?_ hMem hOtherSide (bool_ne_iff_eq_not.mp hSide) hOtherRel.symm
      exact mem_block_star cover fd hc hab hOne wallStar hForest anchorBlock hAnchor pairing
        hOtherS hOtherA
        (hR.trans ((NonTrivalentValencyFourDescent.blockRes_newEdge_refines wSrc pairing wNG
          wRam wProf _).rel hOtherRel))
    have hSurv := (NonTrivalentValencyFourRowEquiv.newSourceEdge_survives_of_unique_fine_survivor
      wSrc pairing wNG wRam wProf wConn wGen wVal hbz h.2 hA hSideFine rfl hUniqLocal).1
    refine ⟨⟨(wCand).newSourceEdge h.1.1.2, hSurv⟩,
      wEpv (wRetSide (((wGauged).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x)) x, ?_,
      NonTrivalentValencyFourRowDictionary.newSourceEdge_incident_ret wSrc pairing wNG wRam
        wProf wConn wGen wVal hb hR, ?_⟩
    · exact NonTrivalentValencyFourRowEquiv.stablePath_newSourceEdge_eq wSrc pairing wNG wRam
        wProf wConn wGen wVal hbz h.2 hA hSideFine rfl hUniqLocal
    · rw [hRet3]
      omega

include hRows hZeroCoord in
/-- **Case II of the non-anchor transport**: two distinct fine-side survivors of
the block in one new-edge class.  Then the block has exactly one retaining-side
survivor, the retaining endpoint is divalent, the common fine endpoint is
trivalent, and the single surviving new occurrence joins them. -/
theorem exists_isPathEnd_ordinary_pair (x : Fin deg) (h : NonDanglingEdge (wGauged))
    (hb : ¬ ((wGauged).vertexPartition
      (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).Rel anchorBlock.1 x)
    (hMem : h.1 ∈ nonDanglingIncident (wGauged)
      ((wGauged).sourceEndpoint (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x))
    (hThree : nonDanglingValency (wGauged)
      ((wGauged).sourceEndpoint (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x) = 3)
    (f₁ f₂ : (wGauged).SourceEdge)
    (hf₁ : f₁ ∈ nonDanglingIncident (wGauged)
      ((wGauged).sourceEndpoint (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x))
    (hf₂ : f₂ ∈ nonDanglingIncident (wGauged)
      ((wGauged).sourceEndpoint (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x))
    (hfNe : f₁ ≠ f₂)
    (hs₁ : wallStar.right pairing f₁.1.1 = !wRetSide (((wGauged).vertexPartition
      (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x))
    (hs₂ : wallStar.right pairing f₂.1.1 = !wRetSide (((wGauged).vertexPartition
      (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x))
    (hcls : (W4Assembly.blockwiseResolution (wGauged) wallStar (wProf).pattern pairing
      (((wGauged).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x)).newEdge.Rel f₁.1.2 f₂.1.2) :
    ∃ (first : NonDanglingEdge (wCand).datum) (vertex : (wCand).datum.SourceVertex),
      first.stablePath = (ResolutionAwayFromWall.retainedEdge (wCand)
          (gaugedData_valid wSrc pairing wNG wRam wVal).1 h).stablePath ∧
        IsPathEnd (wCand).datum first.1 vertex := by
  classical
  obtain ⟨hS, hA, hR⟩ := block_star_mem cover fd hc hab hOne wallStar hForest anchorBlock
    hAnchor pairing hMem
  obtain ⟨h₁S, h₁A, h₁R⟩ := block_star_mem cover fd hc hab hOne wallStar hForest anchorBlock
    hAnchor pairing hf₁
  obtain ⟨h₂S, h₂A, h₂R⟩ := block_star_mem cover fd hc hab hOne wallStar hForest anchorBlock
    hAnchor pairing hf₂
  have hbf₁ : ¬ ((wGauged).vertexPartition
      (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).Rel anchorBlock.1 f₁.1.2 :=
    fun hBad ↦ hb (hBad.trans h₁R.symm)
  have hRepr₁ : ((wGauged).vertexPartition
      (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr f₁.1.2 =
      ((wGauged).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x := h₁R.symm
  -- the two sides of the block, as finsets of survivors
  set star := nonDanglingIncident (wGauged)
    ((wGauged).sourceEndpoint (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x) with hStar
  set T := wRetSide (((wGauged).vertexPartition
    (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x) with hT
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
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hz, bool_ne_iff_eq_not.mp hSide⟩)
  have hDisj : Disjoint (star.filter (fun z ↦ wallStar.right pairing z.1.1 = T))
      (star.filter (fun z ↦ wallStar.right pairing z.1.1 = !T)) := by
    refine Finset.disjoint_left.mpr ?_
    intro z hz hz'
    have h1 := (Finset.mem_filter.mp hz).2
    have h2 := (Finset.mem_filter.mp hz').2
    exact Bool.not_ne_self T (h2.symm.trans h1)
  have hSum : (star.filter (fun z ↦ wallStar.right pairing z.1.1 = T)).card +
      (star.filter (fun z ↦ wallStar.right pairing z.1.1 = !T)).card = 3 := by
    rw [← Finset.card_union_of_disjoint hDisj, hUnion, hStar, card_nonDanglingIncident]
    exact hThree
  have hFineGe : 2 ≤ (star.filter (fun z ↦ wallStar.right pairing z.1.1 = !T)).card := by
    have hsub : ({f₁, f₂} : Finset (wGauged).SourceEdge) ⊆
        star.filter (fun z ↦ wallStar.right pairing z.1.1 = !T) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hf₁, hs₁⟩
      · exact Finset.mem_filter.mpr ⟨hf₂, hs₂⟩
    have := Finset.card_le_card hsub
    rwa [Finset.card_insert_of_notMem (by simpa using hfNe), Finset.card_singleton] at this
  have hFineLe : (star.filter (fun z ↦ wallStar.right pairing z.1.1 = !T)).card ≤ 2 := by
    rw [hStar, ← blockVertex_eq cover fd hc hab hOne wallStar hForest anchorBlock hAnchor
      pairing x]
    exact card_side_le_two cover fd hc hab hOne wallStar hForest anchorBlock hAnchor pairing
      x (!T)
  have hRetOne : (star.filter (fun z ↦ wallStar.right pairing z.1.1 = T)).card = 1 := by
    omega
  obtain ⟨z, hzEq⟩ := Finset.card_eq_one.mp hRetOne
  have hzMem : z ∈ star ∧ wallStar.right pairing z.1.1 = T := by
    have : z ∈ star.filter (fun w ↦ wallStar.right pairing w.1.1 = T) := by
      rw [hzEq]; exact Finset.mem_singleton_self z
    exact Finset.mem_filter.mp this
  obtain ⟨hzS, hzA, hzR⟩ := block_star_mem cover fd hc hab hOne wallStar hForest anchorBlock
    hAnchor pairing hzMem.1
  -- the retaining endpoint has exactly the retained `z` and one new occurrence
  have hRetSubset : nonDanglingIncident (wCand).datum (wEpv T x) ⊆
      {(wCand).oldSourceEdge z, (wCand).newSourceEdge f₁.1.2} := by
    intro w hw
    obtain ⟨hwS, hwI⟩ := (mem_nonDanglingIncident _ _ _).mp hw
    rcases NonTrivalentValencyFourRowEquiv.nonDanglingIncident_ret_dichotomy wSrc pairing wNG
      wRam wProf wConn wGen wVal hb hwS hwI with
      ⟨old, hOldS, hOldA, hOldSide, hOldR, rfl⟩ | ⟨old, hOldS, hOldA, hOldSide, hOldR, rfl⟩
    · have hOldMem : old ∈ star.filter (fun w ↦ wallStar.right pairing w.1.1 = T) :=
        Finset.mem_filter.mpr ⟨mem_block_star cover fd hc hab hOne wallStar hForest
          anchorBlock hAnchor pairing hOldS hOldA hOldR, hOldSide⟩
      rw [hzEq, Finset.mem_singleton] at hOldMem
      rw [hOldMem]
      exact Finset.mem_insert_self _ _
    · have hOldMem : old ∈ star.filter (fun w ↦ wallStar.right pairing w.1.1 = !T) :=
        Finset.mem_filter.mpr ⟨mem_block_star cover fd hc hab hOne wallStar hForest
          anchorBlock hAnchor pairing hOldS hOldA hOldR, hOldSide⟩
      have hPair : star.filter (fun w ↦ wallStar.right pairing w.1.1 = !T) = {f₁, f₂} := by
        refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
        · intro w hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨hf₁, hs₁⟩
          · exact Finset.mem_filter.mpr ⟨hf₂, hs₂⟩
        · rw [Finset.card_insert_of_notMem (by simpa using hfNe), Finset.card_singleton]
          omega
      rw [hPair, Finset.mem_insert, Finset.mem_singleton] at hOldMem
      refine Finset.mem_insert_of_mem (Finset.mem_singleton.mpr ?_)
      rcases hOldMem with rfl | rfl
      · rfl
      · refine (NonTrivalentValencyFourDictionary.newSourceEdge_eq_of_rel wSrc pairing wNG
          wRam wProf wConn wGen wVal ?_).symm
        exact (NonTrivalentValencyFourRowEquiv.candidate_newEdge_rel_block wSrc pairing wNG
          wRam wProf wConn wGen wVal hbf₁ old.1.2).mpr (by rw [hRepr₁]; exact hcls)
  have hOldZIncident : Incident (wCand).datum ((wCand).oldSourceEdge z) (wEpv T x) :=
    NonTrivalentValencyFourRowDictionary.oldSourceEdge_incident_ret wSrc pairing wNG wRam
      wProf wConn wGen wVal hb hzA hzR hzMem.2
  have hOldZMem : (wCand).oldSourceEdge z ∈ nonDanglingIncident (wCand).datum (wEpv T x) :=
    (mem_nonDanglingIncident _ _ _).mpr
      ⟨ResolutionSurvival.not_isDangling_oldSourceEdge (wCand)
        (gaugedData_valid wSrc pairing wNG wRam wVal).1 _ hzS, hOldZIncident⟩
  have hRetTwo : nonDanglingValency (wCand).datum (wEpv T x) = 2 := by
    have hLe : nonDanglingValency (wCand).datum (wEpv T x) ≤ 2 := by
      rw [← card_nonDanglingIncident]
      refine le_trans (Finset.card_le_card hRetSubset) ?_
      exact le_trans (Finset.card_insert_le _ _) (by simp)
    have hNe0 : nonDanglingValency (wCand).datum (wEpv T x) ≠ 0 :=
      ClassInjectivity.nonDanglingValency_ne_zero_of_incident (wCand).datum
        ((mem_nonDanglingIncident _ _ _).mp hOldZMem).1 hOldZIncident
    have hNe1 := NonDanglingValency.nonDanglingValency_ne_one (wCand).datum
      ((wCand).datum_valid (gaugedData_valid wSrc pairing wNG wRam wVal)).1 (wEpv T x)
    omega
  have hCard2 : 1 < (nonDanglingIncident (wCand).datum (wEpv T x)).card := by
    rw [card_nonDanglingIncident, hRetTwo]
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hCard2
  obtain ⟨y, hyMem, hyNe⟩ : ∃ y ∈ nonDanglingIncident (wCand).datum (wEpv T x),
      y ≠ (wCand).oldSourceEdge z := by
    by_cases hU : u = (wCand).oldSourceEdge z
    · exact ⟨v, hv, fun hBad ↦ huv (hU.trans hBad.symm)⟩
    · exact ⟨u, hu, hU⟩
  have hyEq : y = (wCand).newSourceEdge f₁.1.2 := by
    have := hRetSubset hyMem
    rw [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h
    · exact absurd h hyNe
    · exact h
  have hNewSurv : ¬ IsDangling (wCand).datum ((wCand).newSourceEdge f₁.1.2) := by
    rw [← hyEq]
    exact ((mem_nonDanglingIncident _ _ _).mp hyMem).1
  -- the common fine endpoint is trivalent
  have hFineThree : nonDanglingValency (wCand).datum (wEpv (!T) f₁.1.2) = 3 := by
    have hLe : nonDanglingValency (wCand).datum (wEpv (!T) f₁.1.2) ≤ 3 := by
      have := nonDanglingValency_fine_le cover fd hc hab hOne wallStar hForest coordinates
        facet hRows hZeroCoord anchorBlock hAnchor pairing f₁.1.2 hbf₁
      rwa [hRepr₁] at this
    have hInc₁ : Incident (wCand).datum ((wCand).oldSourceEdge f₁) (wEpv (!T) f₁.1.2) := by
      have hI := NonTrivalentValencyFourRows.retainedEdge_incident wSrc pairing wNG wRam wProf
        wConn wGen wVal f₁.1.1 h₁A (!T) hs₁ f₁.1.2
      rwa [GluingDatum.sourceEdge_self] at hI
    have hInc₂ : Incident (wCand).datum ((wCand).oldSourceEdge f₂) (wEpv (!T) f₁.1.2) := by
      have hI := NonTrivalentValencyFourRows.retainedEdge_incident wSrc pairing wNG wRam wProf
        wConn wGen wVal f₂.1.1 h₂A (!T) hs₂ f₂.1.2
      rw [GluingDatum.sourceEdge_self] at hI
      have hMove := NonTrivalentValencyFourRowEquiv.endpointVertex_fine_eq wSrc pairing wNG
        wRam wProf wConn wGen wVal hbf₁ (by rw [hRepr₁]; exact hcls)
      rw [hRepr₁] at hMove
      rwa [hMove] at hI
    have hInc₃ : Incident (wCand).datum ((wCand).newSourceEdge f₁.1.2)
        (wEpv (!T) f₁.1.2) :=
      NonTrivalentValencyFourRows.bridgeEdge_incident wSrc pairing wNG wRam wProf wConn wGen
        wVal (!T) f₁.1.2
    have hSub : ({(wCand).oldSourceEdge f₁, (wCand).oldSourceEdge f₂,
        (wCand).newSourceEdge f₁.1.2} : Finset (wCand).datum.SourceEdge) ⊆
          nonDanglingIncident (wCand).datum (wEpv (!T) f₁.1.2) := by
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
          NonTrivalentValencyFourRowDictionary.new_ne_old wSrc pairing wNG wRam wProf wConn
            wGen wVal f₁.1.2 f₁⟩),
      Finset.card_insert_of_notMem (by
        simpa using NonTrivalentValencyFourRowDictionary.new_ne_old wSrc pairing wNG wRam
          wProf wConn wGen wVal f₁.1.2 f₂),
      Finset.card_singleton] at hCard
    omega
  by_cases hSideH : wallStar.right pairing h.1.1.1 = T
  · -- the unique retaining survivor: cross the divalent retaining endpoint
    have hHz : h.1 = z := by
      have hMemT : h.1 ∈ star.filter (fun w ↦ wallStar.right pairing w.1.1 = T) :=
        Finset.mem_filter.mpr ⟨hMem, hSideH⟩
      rw [hzEq, Finset.mem_singleton] at hMemT
      exact hMemT
    refine ⟨⟨(wCand).newSourceEdge f₁.1.2, hNewSurv⟩, wEpv (!T) f₁.1.2, ?_,
      NonTrivalentValencyFourRows.bridgeEdge_incident wSrc pairing wNG wRam wProf wConn wGen
        wVal (!T) f₁.1.2, ?_⟩
    · refine stablePath_eq_of_consecutive ⟨?_, wEpv T x,
        NonTrivalentValencyFourRowDictionary.newSourceEdge_incident_ret wSrc pairing wNG wRam
          wProf wConn wGen wVal hb h₁R, ?_, hRetTwo⟩
      · intro hBad
        apply hyNe
        rw [hyEq, ← hHz]
        exact congrArg Subtype.val hBad
      · show Incident (wCand).datum ((wCand).oldSourceEdge h.1) (wEpv T x)
        rw [hHz]
        exact hOldZIncident
    · rw [hFineThree]
      omega
  · -- a fine-side survivor: it already meets the trivalent fine endpoint
    have hSideFine : wallStar.right pairing h.1.1.1 = !T := bool_ne_iff_eq_not.mp hSideH
    have hMemF : h.1 ∈ star.filter (fun w ↦ wallStar.right pairing w.1.1 = !T) :=
      Finset.mem_filter.mpr ⟨hMem, hSideFine⟩
    have hPair : star.filter (fun w ↦ wallStar.right pairing w.1.1 = !T) = {f₁, f₂} := by
      refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
      · intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hf₁, hs₁⟩
        · exact Finset.mem_filter.mpr ⟨hf₂, hs₂⟩
      · rw [Finset.card_insert_of_notMem (by simpa using hfNe), Finset.card_singleton]
        omega
    rw [hPair, Finset.mem_insert, Finset.mem_singleton] at hMemF
    refine ⟨ResolutionAwayFromWall.retainedEdge (wCand) _ h, wEpv (!T) f₁.1.2, rfl, ?_, ?_⟩
    · show Incident (wCand).datum ((wCand).oldSourceEdge h.1) (wEpv (!T) f₁.1.2)
      have hI := NonTrivalentValencyFourRows.retainedEdge_incident wSrc pairing wNG wRam wProf
        wConn wGen wVal h.1.1.1 hA (!T) hSideFine h.1.1.2
      rw [GluingDatum.sourceEdge_self] at hI
      rcases hMemF with hEq | hEq
      · rw [hEq] at hI ⊢
        exact hI
      · rw [hEq] at hI ⊢
        have hMove := NonTrivalentValencyFourRowEquiv.endpointVertex_fine_eq wSrc pairing wNG
          wRam wProf wConn wGen wVal hbf₁ (by rw [hRepr₁]; exact hcls)
        rw [hRepr₁] at hMove
        rwa [hMove] at hI
    · rw [hFineThree]
      omega

include hRows hZeroCoord in
/-- **The non-anchor block half of the path-end transport.**  A survivor of a
non-anchor wall block that is a path end of the gauged wall datum keeps a path
end on its own retained row of the candidate. -/
theorem exists_isPathEnd_ordinary (x : Fin deg) (h : NonDanglingEdge (wGauged))
    (hb : ¬ ((wGauged).vertexPartition
      (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).Rel anchorBlock.1 x)
    (hInc : Incident (wGauged) h.1
      ((wGauged).sourceEndpoint (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x))
    (hNd : nonDanglingValency (wGauged)
      ((wGauged).sourceEndpoint (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x) ≠ 2) :
    ∃ (first : NonDanglingEdge (wCand).datum) (vertex : (wCand).datum.SourceVertex),
      first.stablePath = (ResolutionAwayFromWall.retainedEdge (wCand)
          (gaugedData_valid wSrc pairing wNG wRam wVal).1 h).stablePath ∧
        IsPathEnd (wCand).datum first.1 vertex := by
  classical
  have hMem : h.1 ∈ nonDanglingIncident (wGauged)
      ((wGauged).sourceEndpoint (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨h.2, hInc⟩
  have hThree := block_valency_eq_three cover fd hc hab hOne wallStar hForest coordinates
    facet hRows hZeroCoord anchorBlock hAnchor pairing x h hb hInc hNd
  by_cases hU : ∀ z z' : (wGauged).SourceEdge,
      z ∈ nonDanglingIncident (wGauged)
        ((wGauged).sourceEndpoint (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x) →
      z' ∈ nonDanglingIncident (wGauged)
        ((wGauged).sourceEndpoint (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x) →
      wallStar.right pairing z.1.1 = !wRetSide (((wGauged).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x) →
      wallStar.right pairing z'.1.1 = !wRetSide (((wGauged).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x) →
      (W4Assembly.blockwiseResolution (wGauged) wallStar (wProf).pattern pairing
        (((wGauged).vertexPartition
          (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x)).newEdge.Rel z.1.2 z'.1.2 →
      z = z'
  · exact exists_isPathEnd_ordinary_unique cover fd hc hab hOne wallStar hForest coordinates
      facet hRows hZeroCoord anchorBlock hAnchor pairing x h hb hMem hThree hU
  · push Not at hU
    obtain ⟨f₁, f₂, hf₁, hf₂, hs₁, hs₂, hcls, hfNe⟩ := hU
    exact exists_isPathEnd_ordinary_pair cover fd hc hab hOne wallStar hForest coordinates
      facet hRows hZeroCoord anchorBlock hAnchor pairing x h hb hMem hThree f₁ f₂ hf₁ hf₂
      hfNe hs₁ hs₂ hcls

/-! ### Path ends of the gauged wall datum, and their transport -/

include hZeroCoord hPosCoord hFacetZero in
/-- **`HasPathEnds` of the gauged wall datum.**  The `HasPathEnds` of the wall
datum from `WallDatumPathEnds` (`NoContractedReturn` is free at a four-valent
wall) transported along
the block-preserving branch gauge, which is a sheet relabelling and therefore a
stable-graph incidence equivalence. -/
theorem hasPathEnds_gauged : HasPathEnds (wGauged) :=
  StableGraphIncidence.hasPathEnds_sheetRelabel
    (NonTrivalentValencyFourKZero.PrescribedPairing.relabeling wSrc pairing wNG wRam)
    (wVal).1
    (WallDatumPathEnds.hasPathEnds_contractDatum_of_noContractedReturn cover fd hc hab hOne
      hForest coordinates facet hZeroCoord hPosCoord hFacetZero wNoRet)

/-- **A survivor of the anchor block keeps a path end on its own retained row.**
Its retained copy meets the endpoint vertex on the side the prescribed pairing
assigns to its target branch, and that vertex is one of the two trivalent `K = 0`
endpoints: on the non-smaller side the endpoint partition is the whole old wall
block, and on the smaller side a sheet outside the selected fine class carries
no surviving retained occurrence at all. -/
theorem exists_isPathEnd_anchor (h : NonDanglingEdge (wGauged))
    (hAt : h.1.1.1 ∈ GluingDatum.incidentEdges
      (⟨a, hab⟩ : GraphContraction.Vertex targetIn b))
    (hRel : ((wGauged).vertexPartition
      (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).Rel anchorBlock.1 h.1.1.2) :
    ∃ (first : NonDanglingEdge (wCand).datum) (vertex : (wCand).datum.SourceVertex),
      first.stablePath = (ResolutionAwayFromWall.retainedEdge (wCand)
          (gaugedData_valid wSrc pairing wNG wRam wVal).1 h).stablePath ∧
        IsPathEnd (wCand).datum first.1 vertex := by
  classical
  have hInc : Incident (wCand).datum ((wCand).oldSourceEdge h.1)
      (wEpv (wallStar.right pairing h.1.1.1) h.1.1.2) := by
    have hI := NonTrivalentValencyFourRows.retainedEdge_incident wSrc pairing wNG wRam wProf
      wConn wGen wVal h.1.1.1 hAt (wallStar.right pairing h.1.1.1) rfl h.1.1.2
    rwa [GluingDatum.sourceEdge_self] at hI
  have hRepRel : ((wGauged).vertexPartition
      (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).Rel anchorBlock.1
        (selectedRepresentative wSrc pairing) :=
    (NonTrivalentValencyFourRows.gauged_rel_iff wSrc pairing wNG wRam _ _).mpr
      ((wSrc).sheet_wall_rel _)
  by_cases hSide : wallStar.right pairing h.1.1.1 = smallerSide wSrc pairing
  · by_cases hFine : (finePartition wSrc pairing wNG wRam).Rel
        (selectedRepresentative wSrc pairing) h.1.1.2
    · refine ⟨ResolutionAwayFromWall.retainedEdge (wCand) _ h,
        wEpv (wallStar.right pairing h.1.1.1) h.1.1.2, rfl, hInc, ?_⟩
      rw [← NonTrivalentValencyFourRows.endpointVertex_eq wSrc pairing wNG wRam wProf wConn
          wGen wVal (wallStar.right pairing h.1.1.1) hRepRel
          (by rw [hSide, NonTrivalentValencyFourDictionary.endpointForSide_smaller wSrc
            pairing wNG wRam]; exact hFine),
        NonTrivalentValencyFourDictionary.nonDanglingValency_endpointVertex wSrc pairing wNG
          wRam wProf wConn wGen wVal (wallStar.right pairing h.1.1.1)]
      omega
    · exfalso
      have hSingle : (finePartition wSrc pairing wNG wRam).block h.1.1.2 = {h.1.1.2} := by
        rcases finePartition_rel_or_singleton wSrc pairing wNG wRam h.1.1.2
          ((NonTrivalentValencyFourRows.gauged_rel_iff wSrc pairing wNG wRam _ _).mp hRel)
          with hR | hS
        · exact absurd hR hFine
        · exact hS
      have hMem : (wCand).oldSourceEdge h.1 ∈ nonDanglingIncident (wCand).datum
          (wEpv (smallerSide wSrc pairing) h.1.1.2) := by
        refine (mem_nonDanglingIncident _ _ _).mpr
          ⟨ResolutionSurvival.not_isDangling_oldSourceEdge (wCand)
            (gaugedData_valid wSrc pairing wNG wRam wVal).1 _ h.2, ?_⟩
        rw [← hSide]
        exact hInc
      have hEq := NonTrivalentValencyFourDictionary.nonDanglingIncident_singleton_subset wSrc
        pairing wNG wRam wProf wConn wGen wVal hRel hSingle hFine hMem
      rw [Finset.mem_singleton] at hEq
      exact NonTrivalentValencyFourRowDictionary.new_ne_old wSrc pairing wNG wRam wProf wConn
        wGen wVal h.1.1.2 h.1 hEq
  · refine ⟨ResolutionAwayFromWall.retainedEdge (wCand) _ h,
      wEpv (wallStar.right pairing h.1.1.1) h.1.1.2, rfl, hInc, ?_⟩
    rw [← NonTrivalentValencyFourRows.endpointVertex_eq wSrc pairing wNG wRam wProf wConn
        wGen wVal (wallStar.right pairing h.1.1.1) hRepRel
        (by rw [NonTrivalentValencyFourRowDictionary.bool_eq_not_of_ne hSide,
          NonTrivalentValencyFourRowDictionary.endpointForSide_not_smaller wSrc pairing wNG
            wRam]; exact hRepRel.symm.trans hRel),
      NonTrivalentValencyFourDictionary.nonDanglingValency_endpointVertex wSrc pairing wNG
        wRam wProf wConn wGen wVal (wallStar.right pairing h.1.1.1)]
    omega

include hPosCoord hFacetZero in
/-- **`HasPathEnds` of the `K = 0` candidate, modulo the non-anchor block
half of the transport.**  The bridge row is a path end outright; a retained row
is handled away from the wall by `ResolutionAwayFromWall` and at the anchor by
`exists_isPathEnd_anchor`; `hOrdinary` is exactly the remaining case. -/
theorem hasPathEnds_candidate_of_ordinary
    (hOrdinary : ∀ (x : Fin deg) (h : NonDanglingEdge (wGauged)),
      ¬ ((wGauged).vertexPartition
          (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).Rel anchorBlock.1 x →
      Incident (wGauged) h.1 ((wGauged).sourceEndpoint
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x) →
      nonDanglingValency (wGauged) ((wGauged).sourceEndpoint
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x) ≠ 2 →
      ∃ (first : NonDanglingEdge (wCand).datum) (vertex : (wCand).datum.SourceVertex),
        first.stablePath = (ResolutionAwayFromWall.retainedEdge (wCand)
            (gaugedData_valid wSrc pairing wNG wRam wVal).1 h).stablePath ∧
          IsPathEnd (wCand).datum first.1 vertex) :
    HasPathEnds (wCand).datum := by
  classical
  refine hasPathEnds_of_retainedRowEnds cover fd hc hab hOne wallStar hForest coordinates
    facet hRows hZeroCoord anchorBlock hAnchor pairing ?_
  intro r
  obtain ⟨e, rfl⟩ := Quot.exists_rep r
  obtain ⟨h, w, hRow, hIncW, hNdW⟩ := hasPathEnds_gauged cover fd hc hab hOne wallStar
    hForest coordinates facet hZeroCoord anchorBlock hAnchor pairing hPosCoord hFacetZero e
  have hRowEq : NonTrivalentValencyFourRowDictionary.retainedRow wSrc pairing wNG wRam wProf
      wConn wGen wVal e.stablePath =
      (ResolutionAwayFromWall.retainedEdge (wCand)
        (gaugedData_valid wSrc pairing wNG wRam wVal).1 h).stablePath :=
    (congrArg (NonTrivalentValencyFourRowDictionary.retainedRow wSrc pairing wNG wRam wProf
        wConn wGen wVal) hRow.symm).trans
      (NonTrivalentValencyFourRowDictionary.retainedRow_mk wSrc pairing wNG wRam wProf wConn
        wGen wVal h)
  by_cases hAtW : w.1.1 = (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)
  · have hVertex : (wGauged).sourceEndpoint
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) w.1.2 = w :=
      (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hAtW.symm, rfl⟩
    by_cases hAnchorRel : ((wGauged).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).Rel anchorBlock.1 w.1.2
    · obtain ⟨hAt, hRelW⟩ := (incident_iff_target_mem_and_rel (wGauged) h.1
        ((wGauged).sourceEndpoint (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)
          w.1.2)).mp (by rw [hVertex]; exact hIncW)
      obtain ⟨first, vertex, hF, hE⟩ := exists_isPathEnd_anchor cover fd hc hab hOne wallStar
        hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing h hAt
        ((hAnchorRel.trans (((wGauged).vertexPartition
          (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).rel_repr_right w.1.2)).trans hRelW)
      exact ⟨first, vertex, hF.trans hRowEq.symm, hE⟩
    · obtain ⟨first, vertex, hF, hE⟩ := hOrdinary w.1.2 h hAnchorRel
        (by rw [hVertex]; exact hIncW) (by rw [hVertex]; exact hNdW)
      exact ⟨first, vertex, hF.trans hRowEq.symm, hE⟩
  · refine ⟨ResolutionAwayFromWall.retainedEdge (wCand)
      (gaugedData_valid wSrc pairing wNG wRam wVal).1 h,
      ResolutionAwayFromWall.retainedVertex (wCand) w, hRowEq.symm, ?_, ?_⟩
    · exact (ResolutionAwayFromWall.incident_oldSourceEdge_iff (wCand) w hAtW h.1).mpr hIncW
    · rw [ResolutionAwayFromWall.nonDanglingValency_retainedVertex (wCand)
        (gaugedData_valid wSrc pairing wNG wRam wVal)
        (NonTrivalentValencyFourRows.candidate_sourceGenus wSrc pairing wNG wRam wProf wConn
          wGen wVal) w hAtW]
      exact hNdW

/-! ### The outgoing full-dimensional presentation -/

include hPosCoord hFacetZero in
/-- **`HasPathEnds` of the `K = 0` candidate at an actual four-valent wall**, with
no receipt: the bridge row, the rows away from the wall, the rows through the
anchor and the rows through a non-anchor block are all covered. -/
theorem hasPathEnds_candidate : HasPathEnds (wCand).datum :=
  hasPathEnds_candidate_of_ordinary cover fd hc hab hOne wallStar hForest coordinates facet
    hRows hZeroCoord anchorBlock hAnchor pairing hPosCoord hFacetZero
    (fun x h hb hInc hNd ↦ exists_isPathEnd_ordinary cover fd hc hab hOne wallStar hForest
      coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing x h hb hInc hNd)

/-- **The outgoing full-dimensional source presentation at a four-valent wall.**
No receipt remains: `HasPathEnds` is `hasPathEnds_candidate`. -/
def outgoingFD :
    FullDimensionalSourcePresentation (wCand).datum coordinate :=
  NonTrivalentValencyTwoExit.ofTypeChange fd
    (NonTrivalentValencyFourBackground.candidate_datum_valid' wSrc pairing wNG wRam wProf
      wConn wGen wVal)
    (outgoing_targetConnected cover fd hc hab hOne wallStar hForest coordinates facet hRows
      hZeroCoord anchorBlock hAnchor pairing)
    (outgoing_targetGenus cover fd hc hab hOne wallStar hForest coordinates facet hRows
      hZeroCoord anchorBlock hAnchor pairing)
    (outgoing_targetEdgeCard cover fd hc hab hOne wallStar hForest coordinates facet hRows
      hZeroCoord anchorBlock hAnchor pairing)
    (((NonTrivalentValencyFourRows.candidate_sourceGenus wSrc pairing wNG wRam wProf wConn
        wGen wVal).trans
      (SheetRelabelIncidence.sourceGenus_eq
        (NonTrivalentValencyFourKZero.PrescribedPairing.relabeling wSrc pairing wNG
          wRam))).trans
      (NonTrivalentValencyTwoExit.genus_sourceGraph_contractDatum cover hc hab hOne hForest))
    (outLabelling cover fd hc hab hOne wallStar hForest coordinates facet hRows hZeroCoord
      anchorBlock hAnchor pairing hPosCoord hFacetZero)
    (det_outLabelling_ne_zero cover fd hc hab hOne wallStar hForest coordinates facet hRows
      hZeroCoord anchorBlock hAnchor pairing hPosCoord hFacetZero)
    (candidate_trivalent cover fd hc hab hOne wallStar hForest coordinates facet hRows
      hZeroCoord anchorBlock hAnchor pairing)
    (hasPathEnds_candidate cover fd hc hab hOne wallStar hForest coordinates facet hRows
      hZeroCoord anchorBlock hAnchor pairing hPosCoord hFacetZero)

@[simp] theorem outgoingFD_labelling :
    (outgoingFD cover fd hc hab hOne wallStar hForest coordinates facet hRows hZeroCoord
        anchorBlock hAnchor pairing hPosCoord hFacetZero).labelling =
      outLabelling cover fd hc hab hOne wallStar hForest coordinates facet hRows hZeroCoord
        anchorBlock hAnchor pairing hPosCoord hFacetZero := rfl

end Presentation

end

/-! ## The link at a four-valent wall of the outer walk -/

section Link

open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk

noncomputable section

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)

/-- **The anchor of a four-valent wall, with no receipt.**  The results of
`NonTrivalentUniqueFourValent` and `NonTrivalentValencyFourBackground`, read at
the wall data of the outer walk: the four-valent target star, the anchor
block with its surviving valency four, and -- for the pairing prescribed by the
move -- the validity of the `K = 0` candidate over the block-preserving branch
gauge of the wall datum. -/
theorem exists_anchor_of_wallData
    (h4 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 4) (pairing : Fin 3) :
    ∃ (wallStar : W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩)
      (anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
      (hAnchor : nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩ anchorBlock) = 4),
      (NonTrivalentValencyFourBackground.candidate
        (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc wd.hab
          wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor)
        pairing
        (NonTrivalentUniqueFourValent.wall_noGlue wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (wd.hForest m))
        (NonTrivalentUniqueFourValent.wall_ramification wd.cover wd.fullDim wd.hc wd.hab
          wd.hOne wallStar (wd.hForest m) anchorBlock)
        (NonTrivalentUniqueFourValent.ordinaryBlockProfile_of_single_row wd.cover wd.fullDim
          wd.hc wd.hab wd.hOne wallStar (wd.hForest m) wd.coordinates (label m.base) wd.hRows
          wd.hZeroCoord anchorBlock hAnchor)
        (NonTrivalentUniqueFourValent.wall_target_connected wd.cover wd.fullDim wd.hab
          wd.hOne)
        (NonTrivalentUniqueFourValent.wall_target_genus wd.cover wd.fullDim wd.hab wd.hOne)
        (NonTrivalentUniqueFourValent.wall_valid wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (wd.hForest m))).datum.Valid := by
  obtain ⟨wallStar⟩ : Nonempty (W4TargetPairings.FourStar
      (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :=
    ⟨W4TargetPairings.FourStar.of_card h4⟩
  obtain ⟨anchorBlock, hAnchor⟩ :=
    NonTrivalentUniqueFourValent.exists_wallBlock_nonDanglingValency_eq_four wd.cover
      wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hCompat m) wd.coordinates (label m.base)
      wd.hZeroCoord wd.hPosCoord wd.hFacetZero
  exact ⟨wallStar, anchorBlock, hAnchor,
    NonTrivalentValencyFourBackground.candidate_datum_valid' _ pairing _ _ _ _ _ _⟩

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
local notation "vCand" =>
  (NonTrivalentValencyFourBackground.candidate vSrc pairing vNG vRam vProf vConn vGen vVal)

/-- The outgoing presentation at the wall data of the outer walk.  No
`NoContractedReturn` hypothesis: it is free at a four-valent wall
(`StablePathFacetContraction.noContractedReturn_of_fourStar`). -/
def wallOutgoingFD :
    FullDimensionalSourcePresentation (vCand).datum coordinate :=
  outgoingFD wd.cover wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hForest m) wd.coordinates
    (label m.base) wd.hRows wd.hZeroCoord anchorBlock hAnchor pairing wd.hPosCoord
    wd.hFacetZero

/-- **The type-change link at a four-valent wall.**  The `K = 0` candidate lives
over the block-preserving branch gauge `PrescribedPairing.gaugedData` of the wall
datum, which is therefore the link's `base`; `baseValid` is that gauge's
validity.  The presentation is `wallOutgoingFD` and the common minor is
`agreeOffColumn_outLabelling`. -/
def typeChangeLink_of_receipts
    (tracks : Tracks (wallOutgoingFD m wd wallStar anchorBlock hAnchor pairing)
      (graph.move m) label) :
    TypeChangeLink m wd where
  base := NonTrivalentValencyFourKZero.PrescribedPairing.gaugedData vSrc pairing vNG vRam
  baseValid := NonTrivalentValencyFourKZero.PrescribedPairing.gaugedData_valid vSrc pairing
    vNG vRam vVal
  candidate := NonTrivalentValencyFourBackground.candidate vSrc pairing vNG vRam vProf vConn
    vGen vVal
  outgoingFD := wallOutgoingFD m wd wallStar anchorBlock hAnchor pairing
  tracks := tracks
  agree := by
    have h := agreeOffColumn_outLabelling wd.cover wd.fullDim wd.hc wd.hab wd.hOne wallStar
      (wd.hForest m) wd.coordinates (label m.base) wd.hRows wd.hZeroCoord anchorBlock hAnchor
      pairing wd.hPosCoord wd.hFacetZero
    rw [wd.targetEdge_symm_contracted] at h
    exact h

/-- **At a four-valent wall the only inputs the exit still needs are the
prescribed pairing and the dart-level tracking.**  The four-valent target star,
the anchor block and its surviving valency four are produced from the valency
hypothesis alone, so a `tracks` receipt for every choice of them yields the
type-change link. -/
theorem nonempty_typeChangeLink_of_tracks
    (h4 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 4) (pairing : Fin 3)
    (tracks : ∀ (wallStar : W4TargetPairings.FourStar
        (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
      (anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
      (hAnchor : nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
          anchorBlock) = 4),
      Tracks (wallOutgoingFD m wd wallStar anchorBlock hAnchor pairing) (graph.move m) label) :
    Nonempty (TypeChangeLink m wd) := by
  obtain ⟨wallStar⟩ : Nonempty (W4TargetPairings.FourStar
      (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :=
    ⟨W4TargetPairings.FourStar.of_card h4⟩
  obtain ⟨anchorBlock, hAnchor⟩ :=
    NonTrivalentUniqueFourValent.exists_wallBlock_nonDanglingValency_eq_four wd.cover
      wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hCompat m) wd.coordinates (label m.base)
      wd.hZeroCoord wd.hPosCoord wd.hFacetZero
  exact ⟨typeChangeLink_of_receipts m wd wallStar anchorBlock hAnchor pairing
    (tracks wallStar anchorBlock hAnchor)⟩

end

end Link

end DraismaVargas.LocalCases.NonTrivalentValencyFourExit
