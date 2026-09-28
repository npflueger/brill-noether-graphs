import DraismaVargas.LocalCases.NonTrivalentValencyFourTracks
import DraismaVargas.LocalCases.NonTrivalentValencyThreeStarCount
import DraismaVargas.LocalCases.W4IncomingPrunedFibre

/-!
# The valency-four `K = 0` star count, and the link under (H-IV)

Source: Vargas, Part II (arXiv:2609.09109), Section 5.1 (a combinatorial type
change is a Whitehead move on the *ambient* tracked graph, with the labelling
convention (1)) and Section 5.2 (Case {v4-nd4}: the unique four-valent vertex
`A` resolves into the two trivalent endpoints `A_1^{(q)}`, `A_2^{(q)}` joined by
the new occurrence `h_1^{(q)}`, the two survivors of each side of the
prescribed `2+2` pairing staying with their endpoint), together with
Draisma--Vargas Part I (arXiv:1909.12924): the stable graph `H(M)` of a gluing
datum and its row labels, and `lemma-ndval-of-GqA0`.

`NonTrivalentValencyFourTracks` reduces `OuterWalk.TypeChangeLink` at a
four-valent wall to **one** hypothesis, the star count `hIncidence` of
`typeChangeLink_of_incidence`.  This module proves that count under (H-IV) =
`NonTrivalentValencyFourTracks.PrescribedPairingMove`, and hence delivers the
link.  It follows the valency-three star count
(`NonTrivalentValencyThreeStarCount`), adapted to the `2+2` pairing; the six
valency-agnostic helpers of that file (`card_filter_pair`, `filter_moved_base`,
`dart_ne`, `card_filter_label`, `sum_natCard_moved`,
`sum_incidenceCount_branchVertex`) are *reused by import* rather than restated,
which is why this module imports the valency-three star count.

## What is proved

### 0.  A star map transports every row-filtered count

* `incidenceCount_of_star_map`, `nonDanglingValency_le_of_star_map`: if an
  injective map carries the surviving star of `v₁` into the surviving star of
  `v₂` and each occurrence onto the `rowMap`-image of its row, then it is a
  bijection as soon as `nd(v₂) ≤ nd(v₁)`, so *every* row-filtered count agrees.
  This replaces a hand-written `Finset.card_bij` at each block.

### 1.  (T1): the gauged wall datum's star descends to the candidate

At valency four the branch vertex over a non-anchor wall block is not always the
same endpoint, so the transport is the block classification of
`NonTrivalentValencyFourTracks` read occurrence by occurrence, in its two cases.

* `incidenceCount_block_unique`: **every fine-side survivor alone in its
  new-edge class.**  The star map is a retained survivor of the retaining side
  kept as itself, and a fine-side survivor replaced by the surviving new
  occurrence of its own class, which sits on that survivor's row
  (`NonTrivalentValencyFourRowEquiv.stablePath_newSourceEdge_eq`); the target is
  the retaining endpoint, trivalent by
  `nonDanglingValency_ret_eq_three_of_unique` (in
  `NonTrivalentValencyFourExitLink`).
* `block_pair_transport`: **two fine-side survivors in one class.**  Then
  the block has exactly one retaining-side survivor, the retaining endpoint is
  divalent, and the star map sends the two fine-side survivors to their retained
  copies and the retaining-side survivor to the block's single surviving new
  occurrence, which crosses the divalent retaining endpoint and is therefore on
  its row.  The target is their common fine endpoint.
* `exists_block_transport`, `incidenceCount_block_candVertex`,
  `incidenceCount_candVertex`: (T1) at every branch vertex of the gauged wall
  datum other than the anchor -- the two block cases above, identified with
  `NonTrivalentValencyFourTracks.candVertex` through `candVertex_spec_wall`,
  and `NonTrivalentValencyFourTracks.incidenceCount_retainedVertex_retainedRow`
  off the wall.

### 2.  (T2) and (T3): the gauge and the wall contraction

* `incidenceCount_gauge`: (T2) is free.  The block-preserving branch gauge is a
  sheet relabelling, so `StableGraphIncidence.incidenceCount_sheetRelabel`
  transports the count, with the row leg `SheetRelabelStable.stablePathEquiv`
  against which `NonTrivalentValencyFourExit.outLabelling_row_retained` is
  stated.
* `incidenceCount_wall_eq_incoming`: (T3), from the valency-agnostic
  `WallSplitIncidenceOrdinary.incidenceCount_unramified`.  Its `hSubsingleton`
  input is free at a four-valent wall: `W4IncomingPrunedFibre` shows the pruned
  fibre of *every* merged vertex is a point or a single internal occurrence with
  two distinct ends, with no ramification bookkeeping.

### 3.  The star count

* `incidence_inl_retained`, `incidence_inl_bridge`: away from the anchor.  On a
  retained row the count is (T1) then (T2) then (T3) then the incoming tracking
  (`card_star_eq_incidenceCount`, with `move_vert_eq_iff_of_ne` erasing the
  move); on the bridge row both sides vanish -- downstairs `h_1` joins `A_1` to
  `A_2`, upstairs the vanishing chart row is the single occurrence `h_1`.
* `incidence_inr_false_retained`, `incidence_inr_false_bridge`: **at `A_1`.**
  The exact star
  `NonTrivalentValencyFourDictionary.nonDanglingIncident_endpointVertex` (the
  bridge and the two survivors of that side) is matched dart by dart with the
  moved star that (H-IV) prescribes.
* `incidence_inr_true`: **at `A_2`, from the leftover equation**, exactly as at
  valency three.
* `incidence_of_prescribedPairingMove`: the star count at every branch vertex
  and every row, and `typeChangeLink_of_prescribedPairingMove`:
  **`OuterWalk.TypeChangeLink` at a four-valent wall from (H-IV) alone.**
* `nonempty_typeChangeLink_of_prescribedPairingMove`: the same at an actual wall
  from the valency hypothesis `h4`, the prescribed `pairing` and (H-IV), with
  `wallStar`, `anchorBlock` and `hAnchor` produced by
  `exists_anchor_of_wallData` (in `NonTrivalentValencyFourExitLink`).

## What is not proved here: the hypotheses that remain explicit

1. `hPres : NonTrivalentValencyFourTracks.PrescribedPairingMove m wd wallStar
   anchorBlock hAnchor pairing`, i.e. (H-IV).  `NonTrivalentValencyFourTracks`
   supplies its relative non-vacuity witness
   `prescribedPairingMove_prescribedMove` from `SelectedSeparated` and the
   orientation clause; neither is derived here.
2. `pairing : Fin 3`, and -- in the non-corollary form -- `wallStar`,
   `anchorBlock`, `hAnchor`: exactly the packaging inputs of
   `NonTrivalentValencyFourTracks.typeChangeLink_of_incidence`.
   `nonempty_typeChangeLink_of_prescribedPairingMove` removes all three, at the
   price of quantifying (H-IV) over them -- but that quantified form is **not
   usable by a dispatcher**: a fixed star relabelling makes
   `W4TargetPairings.Pairing.labelsOnSide p false` miss label `0`, so a fixed
   `wallStar` realizes only three of the four cross pairs, and swapping the
   move's orientation cannot recover the fourth.  A dispatcher must instead
   relabel the star by the move and consume the `Wall`-section
   `typeChangeLink_of_prescribedPairingMove` (this is a matter of packaging,
   not of soundness).
3. The valency dispatcher of `OuterWalk.WallData` -- which wall of the outer walk
   is four-valent -- is not built here; it is
   `NonTrivalentValencyFourDispatcher`, consuming the `Wall`-section theorem as
   above and establishing `OuterWalk.TypeChangeLink` at every four-valent wall
   of every Whitehead move unconditionally, from `card (incidentEdges ...) = 4`
   alone.
4. Nothing else: `hPathEnds`, `NoContractedReturn`, the census, the row
   equivalence and the branch-vertex bijection are all discharged upstream.

No structure and no `Prop` is introduced.  Every definition (`blockEdgeMap`,
`blockEdgePairMap`, `gaugedRow`, `selectedWallEdge`, `selectedCandEdge`,
`bridgeND`) is a named occurrence, row or vertex of an object already built, or a
map between two such families, and each is applied in the theorems above.

## Consumers

`NonTrivalentValencyFourDispatcher.typeChangeLink_four` consumes the
`Wall`-section `typeChangeLink_of_prescribedPairingMove` (not the `Corollary`
section) to establish `OuterWalk.TypeChangeLink` at Part II, Case {v4-nd4}
unconditionally, hence `OuterWalk.coneEntry_of_reaches` and the type-change
link of the outer walk at every four-valent wall -- with no (H-IV) supplied by
the walk.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyFourStarCount

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

/-! ## 0.  A star map transports every row-filtered count -/

section StarMap

variable {target₁ target₂ : CFGraph} {degree₁ degree₂ : ℕ}
  {data₁ : GluingDatum target₁ degree₁} {data₂ : GluingDatum target₂ degree₂}

/-- An injective map of surviving stars does not decrease the surviving
valency. -/
theorem nonDanglingValency_le_of_star_map (v₁ : data₁.SourceVertex)
    (v₂ : data₂.SourceVertex)
    (Φ : ∀ e ∈ incidentEdges data₁ v₁, NonDanglingEdge data₂)
    (hMem : ∀ e he, Φ e he ∈ incidentEdges data₂ v₂)
    (hInj : ∀ e₁ e₂ he₁ he₂, Φ e₁ he₁ = Φ e₂ he₂ → e₁ = e₂) :
    nonDanglingValency data₁ v₁ ≤ nonDanglingValency data₂ v₂ := by
  classical
  rw [← card_incidentEdges, ← card_incidentEdges, ← Finset.card_attach
    (s := incidentEdges data₁ v₁)]
  refine Finset.card_le_card_of_injOn (fun e ↦ Φ e.1 e.2) (fun e _ ↦ hMem e.1 e.2) ?_
  intro e₁ _ e₂ _ hEq
  exact Subtype.ext (hInj e₁.1 e₂.1 e₁.2 e₂.2 hEq)

/-- **An injective row-preserving star map transports every row-filtered
count.**  It is automatically surjective once the target star is no larger, so
the count agrees row by row. -/
theorem incidenceCount_of_star_map (v₁ : data₁.SourceVertex)
    (v₂ : data₂.SourceVertex)
    (rowMap : StablePath data₁ → StablePath data₂) (hRowInj : Function.Injective rowMap)
    (Φ : ∀ e ∈ incidentEdges data₁ v₁, NonDanglingEdge data₂)
    (hMem : ∀ e he, Φ e he ∈ incidentEdges data₂ v₂)
    (hRow : ∀ e he, (Φ e he).stablePath = rowMap e.stablePath)
    (hInj : ∀ e₁ e₂ he₁ he₂, Φ e₁ he₁ = Φ e₂ he₂ → e₁ = e₂)
    (hCard : nonDanglingValency data₂ v₂ ≤ nonDanglingValency data₁ v₁)
    (row : StablePath data₁) :
    incidenceCount data₁ v₁ row = incidenceCount data₂ v₂ (rowMap row) := by
  classical
  have hSurj := Finset.surj_on_of_inj_on_of_card_le Φ hMem hInj
    (by rw [card_incidentEdges, card_incidentEdges]; exact hCard)
  unfold incidenceCount
  refine Finset.card_bij (fun e he ↦ Φ e (Finset.mem_filter.mp he).1) ?_ ?_ ?_
  · intro e he
    refine Finset.mem_filter.mpr ⟨hMem _ _, ?_⟩
    rw [hRow, (Finset.mem_filter.mp he).2]
  · intro e₁ h₁ e₂ h₂ hEq
    exact hInj _ _ _ _ hEq
  · intro g hg
    obtain ⟨hMemG, hRowG⟩ := Finset.mem_filter.mp hg
    obtain ⟨e, he, rfl⟩ := hSurj g hMemG
    refine ⟨e, Finset.mem_filter.mpr ⟨he, hRowInj ?_⟩, rfl⟩
    rw [← hRow e he]
    exact hRowG

end StarMap

/-! ## 1.  (T1) at a non-anchor wall block -/

section Ordinary

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
local notation "wRetRow" =>
  (NonTrivalentValencyFourRowDictionary.retainedRow wSrc pairing wNG wRam wProf wConn
    wGen wVal)

set_option quotPrecheck false in
local notation "wW" => (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)
set_option quotPrecheck false in
local notation "wPart" => ((wGauged).vertexPartition wW)
set_option quotPrecheck false in
local notation "wBRes" =>
  (W4Assembly.blockwiseResolution (wGauged) wallStar (wProf).pattern pairing)

/-- A surviving occurrence at a wall block, read in the block's star. -/
theorem mem_block_star_of_incidentEdges (x : Fin deg) (e : NonDanglingEdge (wGauged))
    (he : e ∈ incidentEdges (wGauged) ((wGauged).sourceEndpoint wW x)) :
    e.1 ∈ nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x) :=
  (mem_nonDanglingIncident _ _ _).mpr ⟨e.2, (mem_incidentEdges _ _ _).mp he⟩

/-- **Case `U`: every fine-side survivor of the block is alone in its new-edge
class**, read at one such survivor in the form
`NonTrivalentValencyFourRowEquiv.newSourceEdge_survives_of_unique_fine_survivor`
consumes. -/
theorem fine_unique_of_block (x : Fin deg)
    (hU : ∀ z z' : (wGauged).SourceEdge,
      z ∈ nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x) →
      z' ∈ nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x) →
      wallStar.right pairing z.1.1 = !wRetSide ((wPart).repr x) →
      wallStar.right pairing z'.1.1 = !wRetSide ((wPart).repr x) →
      (wBRes ((wPart).repr x)).newEdge.Rel z.1.2 z'.1.2 → z = z')
    {z : (wGauged).SourceEdge}
    (hzMem : z ∈ nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x))
    (hzSide : wallStar.right pairing z.1.1 = !wRetSide ((wPart).repr x)) :
    ∀ other : (wGauged).SourceEdge, ¬ IsDangling (wGauged) other →
      other.1.1 ∈ GluingDatum.incidentEdges wW →
      wallStar.right pairing other.1.1 = !wRetSide ((wPart).repr z.1.2) →
      (wBRes ((wPart).repr z.1.2)).newEdge.Rel z.1.2 other.1.2 → other = z := by
  intro other hOtherS hOtherA hOtherSide hOtherRel
  obtain ⟨hzS, hzA, hzR⟩ := block_star_mem cover fd hc hab hOne wallStar hForest
    anchorBlock hAnchor pairing hzMem
  have hRepr : (wPart).repr z.1.2 = (wPart).repr x := hzR.symm
  rw [hRepr] at hOtherSide hOtherRel
  refine hU other z ?_ hzMem hOtherSide hzSide hOtherRel.symm
  exact mem_block_star cover fd hc hab hOne wallStar hForest anchorBlock hAnchor pairing
    hOtherS hOtherA
    (hzR.trans ((NonTrivalentValencyFourDescent.blockRes_newEdge_refines wSrc pairing wNG
      wRam wProf _).rel hOtherRel))

/-- **The star map of case `U`**: a retaining-side survivor of a non-anchor
block stays itself, a fine-side survivor is replaced by the new occurrence of
its own fine class. -/
def blockEdgeMap (x : Fin deg) (e : (wGauged).SourceEdge) : (wCand).datum.SourceEdge :=
  if wallStar.right pairing e.1.1 = wRetSide ((wPart).repr x) then
    (wCand).oldSourceEdge e
  else (wCand).newSourceEdge e.1.2

theorem blockEdgeMap_survives (x : Fin deg)
    (hb : ¬ (wPart).Rel anchorBlock.1 x)
    (hU : ∀ z z' : (wGauged).SourceEdge,
      z ∈ nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x) →
      z' ∈ nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x) →
      wallStar.right pairing z.1.1 = !wRetSide ((wPart).repr x) →
      wallStar.right pairing z'.1.1 = !wRetSide ((wPart).repr x) →
      (wBRes ((wPart).repr x)).newEdge.Rel z.1.2 z'.1.2 → z = z')
    (e : NonDanglingEdge (wGauged))
    (he : e ∈ incidentEdges (wGauged) ((wGauged).sourceEndpoint wW x)) :
    ¬ IsDangling (wCand).datum
      (blockEdgeMap cover fd hc hab hOne wallStar hForest coordinates facet hRows
        hZeroCoord anchorBlock hAnchor pairing x e.1) := by
  classical
  have hMem := mem_block_star_of_incidentEdges cover fd hc hab hOne wallStar hForest
    anchorBlock hAnchor pairing x e he
  obtain ⟨hzS, hzA, hzR⟩ := block_star_mem cover fd hc hab hOne wallStar hForest
    anchorBlock hAnchor pairing hMem
  have hRepr : (wPart).repr e.1.1.2 = (wPart).repr x := hzR.symm
  unfold blockEdgeMap
  by_cases hs : wallStar.right pairing e.1.1.1 = wRetSide ((wPart).repr x)
  · rw [if_pos hs]
    exact ResolutionSurvival.not_isDangling_oldSourceEdge (wCand)
      (gaugedData_valid wSrc pairing wNG wRam wVal).1 e.1 e.2
  · rw [if_neg hs]
    exact (NonTrivalentValencyFourRowEquiv.newSourceEdge_survives_of_unique_fine_survivor
      wSrc pairing wNG wRam wProf wConn wGen wVal (fun hBad ↦ hb (hBad.trans hzR.symm))
      hzS hzA (by rw [hRepr]; exact NonTrivalentValencyFourRowDictionary.bool_eq_not_of_ne hs)
      rfl
      (fine_unique_of_block cover fd hc hab hOne wallStar hForest coordinates facet hRows
        hZeroCoord anchorBlock hAnchor pairing x hU hMem
        (NonTrivalentValencyFourRowDictionary.bool_eq_not_of_ne hs))).1

/-- **(T1) at a non-anchor block, case `U`.**  The retaining endpoint keeps the
whole row-filtered star of the block. -/
theorem incidenceCount_block_unique (x : Fin deg)
    (hb : ¬ (wPart).Rel anchorBlock.1 x)
    (hU : ∀ z z' : (wGauged).SourceEdge,
      z ∈ nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x) →
      z' ∈ nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x) →
      wallStar.right pairing z.1.1 = !wRetSide ((wPart).repr x) →
      wallStar.right pairing z'.1.1 = !wRetSide ((wPart).repr x) →
      (wBRes ((wPart).repr x)).newEdge.Rel z.1.2 z'.1.2 → z = z')
    (row : StablePath (wGauged)) :
    incidenceCount (wGauged) ((wGauged).sourceEndpoint wW x) row =
      incidenceCount (wCand).datum (wEpv (wRetSide ((wPart).repr x)) x) (wRetRow row) := by
  classical
  refine incidenceCount_of_star_map _ _ _
    (NonTrivalentValencyFourTracks.injective_retainedRow cover fd hc hab hOne wallStar
      hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing)
    (fun e he ↦ ⟨blockEdgeMap cover fd hc hab hOne wallStar hForest coordinates facet
      hRows hZeroCoord anchorBlock hAnchor pairing x e.1,
      blockEdgeMap_survives cover fd hc hab hOne wallStar hForest coordinates facet hRows
        hZeroCoord anchorBlock hAnchor pairing x hb hU e he⟩)
    ?_ ?_ ?_ ?_ row
  · intro e he
    obtain ⟨hzS, hzA, hzR⟩ := block_star_mem cover fd hc hab hOne wallStar hForest
      anchorBlock hAnchor pairing
      (mem_block_star_of_incidentEdges cover fd hc hab hOne wallStar hForest anchorBlock
        hAnchor pairing x e he)
    refine (mem_incidentEdges _ _ _).mpr ?_
    by_cases hs : wallStar.right pairing e.1.1.1 = wRetSide ((wPart).repr x)
    · have hVal : blockEdgeMap cover fd hc hab hOne wallStar hForest coordinates facet
          hRows hZeroCoord anchorBlock hAnchor pairing x e.1 = (wCand).oldSourceEdge e.1 := by
        unfold blockEdgeMap
        rw [if_pos hs]
      show Incident (wCand).datum (blockEdgeMap cover fd hc hab hOne wallStar hForest
        coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing x e.1) _
      rw [hVal]
      exact NonTrivalentValencyFourRowDictionary.oldSourceEdge_incident_ret wSrc pairing wNG
        wRam wProf wConn wGen wVal hb hzA hzR hs
    · have hVal : blockEdgeMap cover fd hc hab hOne wallStar hForest coordinates facet
          hRows hZeroCoord anchorBlock hAnchor pairing x e.1 =
          (wCand).newSourceEdge e.1.1.2 := by
        unfold blockEdgeMap
        rw [if_neg hs]
      show Incident (wCand).datum (blockEdgeMap cover fd hc hab hOne wallStar hForest
        coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing x e.1) _
      rw [hVal]
      exact NonTrivalentValencyFourRowDictionary.newSourceEdge_incident_ret wSrc pairing wNG
        wRam wProf wConn wGen wVal hb hzR
  · intro e he
    have hMem := mem_block_star_of_incidentEdges cover fd hc hab hOne wallStar hForest
      anchorBlock hAnchor pairing x e he
    obtain ⟨hzS, hzA, hzR⟩ := block_star_mem cover fd hc hab hOne wallStar hForest
      anchorBlock hAnchor pairing hMem
    have hRepr : (wPart).repr e.1.1.2 = (wPart).repr x := hzR.symm
    rw [NonTrivalentValencyFourRowDictionary.retainedRow_mk wSrc pairing wNG wRam wProf
      wConn wGen wVal e]
    by_cases hs : wallStar.right pairing e.1.1.1 = wRetSide ((wPart).repr x)
    · refine congrArg NonDanglingEdge.stablePath (Subtype.ext ?_)
      show blockEdgeMap cover fd hc hab hOne wallStar hForest coordinates facet hRows
        hZeroCoord anchorBlock hAnchor pairing x e.1 = (wCand).oldSourceEdge e.1
      unfold blockEdgeMap
      rw [if_pos hs]
    · refine Eq.trans (congrArg NonDanglingEdge.stablePath (Subtype.ext ?_))
        (NonTrivalentValencyFourRowEquiv.stablePath_newSourceEdge_eq wSrc pairing wNG wRam
          wProf wConn wGen wVal (fun hBad ↦ hb (hBad.trans hzR.symm)) e.2 hzA
          (by rw [hRepr]
              exact NonTrivalentValencyFourRowDictionary.bool_eq_not_of_ne hs) rfl
          (fine_unique_of_block cover fd hc hab hOne wallStar hForest coordinates facet
            hRows hZeroCoord anchorBlock hAnchor pairing x hU hMem
            (NonTrivalentValencyFourRowDictionary.bool_eq_not_of_ne hs)))
      show blockEdgeMap cover fd hc hab hOne wallStar hForest coordinates facet hRows
        hZeroCoord anchorBlock hAnchor pairing x e.1 = (wCand).newSourceEdge e.1.1.2
      unfold blockEdgeMap
      rw [if_neg hs]
  · intro e₁ e₂ he₁ he₂ hEq
    have hVal : blockEdgeMap cover fd hc hab hOne wallStar hForest coordinates facet hRows
        hZeroCoord anchorBlock hAnchor pairing x e₁.1 =
        blockEdgeMap cover fd hc hab hOne wallStar hForest coordinates facet hRows
          hZeroCoord anchorBlock hAnchor pairing x e₂.1 := congrArg Subtype.val hEq
    unfold blockEdgeMap at hVal
    by_cases hs₁ : wallStar.right pairing e₁.1.1.1 = wRetSide ((wPart).repr x) <;>
      by_cases hs₂ : wallStar.right pairing e₂.1.1.1 = wRetSide ((wPart).repr x)
    · rw [if_pos hs₁, if_pos hs₂] at hVal
      exact Subtype.ext (ResolutionCut.oldSourceEdge_injective (wCand) hVal)
    · rw [if_pos hs₁, if_neg hs₂] at hVal
      exact absurd hVal (NonTrivalentValencyFourRowDictionary.new_ne_old wSrc pairing wNG
        wRam wProf wConn wGen wVal e₂.1.1.2 e₁.1)
    · rw [if_neg hs₁, if_pos hs₂] at hVal
      exact absurd hVal.symm (NonTrivalentValencyFourRowDictionary.new_ne_old wSrc pairing
        wNG wRam wProf wConn wGen wVal e₁.1.1.2 e₂.1)
    · rw [if_neg hs₁, if_neg hs₂] at hVal
      have hMem₁ := mem_block_star_of_incidentEdges cover fd hc hab hOne wallStar hForest
        anchorBlock hAnchor pairing x e₁ he₁
      obtain ⟨h₁S, h₁A, h₁R⟩ := block_star_mem cover fd hc hab hOne wallStar hForest
        anchorBlock hAnchor pairing hMem₁
      have hRel := NonTrivalentValencyFourTracks.newEdge_rel_of_newSourceEdge_eq cover fd hc
        hab hOne wallStar hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor
        pairing x e₁.1.1.2 hb h₁R e₂.1.1.2 hVal.symm
      exact Subtype.ext (hU e₁.1 e₂.1 hMem₁
        (mem_block_star_of_incidentEdges cover fd hc hab hOne wallStar hForest anchorBlock
          hAnchor pairing x e₂ he₂)
        (NonTrivalentValencyFourRowDictionary.bool_eq_not_of_ne hs₁)
        (NonTrivalentValencyFourRowDictionary.bool_eq_not_of_ne hs₂) hRel)
  · exact NonTrivalentValencyFourTracks.nonDanglingValency_ret_le_block cover fd hc hab hOne
      wallStar hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing x hb

/-! ### The second case: two fine-side survivors in one new-edge class -/

/-- **The star map of case `P`**: the block's single retaining-side survivor is
replaced by the block's single surviving new occurrence, and the two fine-side
survivors stay themselves. -/
def blockEdgePairMap (x s : Fin deg) (e : (wGauged).SourceEdge) : (wCand).datum.SourceEdge :=
  if wallStar.right pairing e.1.1 = wRetSide ((wPart).repr x) then
    (wCand).newSourceEdge s
  else (wCand).oldSourceEdge e

/-- **(T1) at a non-anchor block, case `P`.**  When two fine-side survivors of a
trivalent block share a new-edge class, the block has exactly one retaining-side
survivor, the retaining endpoint is divalent, the common fine endpoint is
trivalent, and it keeps the whole row-filtered star of the block: the two
fine-side survivors through their retained copies, the retaining-side survivor
through the single surviving new occurrence, which crosses the divalent
retaining endpoint and so lies on its row. -/
theorem block_pair_transport (x : Fin deg)
    (hb : ¬ (wPart).Rel anchorBlock.1 x)
    (hB : nonDanglingValency (wGauged) ((wGauged).sourceEndpoint wW x) = 3)
    (f₁ f₂ : (wGauged).SourceEdge)
    (hf₁ : f₁ ∈ nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x))
    (hf₂ : f₂ ∈ nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x))
    (hs₁ : wallStar.right pairing f₁.1.1 = !wRetSide ((wPart).repr x))
    (hs₂ : wallStar.right pairing f₂.1.1 = !wRetSide ((wPart).repr x))
    (hcls : (wBRes ((wPart).repr x)).newEdge.Rel f₁.1.2 f₂.1.2)
    (hfNe : f₁ ≠ f₂) :
    nonDanglingValency (wCand).datum (wEpv (!wRetSide ((wPart).repr x)) f₁.1.2) = 3 ∧
      ∀ row : StablePath (wGauged),
        incidenceCount (wGauged) ((wGauged).sourceEndpoint wW x) row =
          incidenceCount (wCand).datum (wEpv (!wRetSide ((wPart).repr x)) f₁.1.2)
            (wRetRow row) := by
  classical
  obtain ⟨h₁S, h₁A, h₁R⟩ := block_star_mem cover fd hc hab hOne wallStar hForest anchorBlock
    hAnchor pairing hf₁
  obtain ⟨h₂S, h₂A, h₂R⟩ := block_star_mem cover fd hc hab hOne wallStar hForest anchorBlock
    hAnchor pairing hf₂
  have hbf₁ : ¬ (wPart).Rel anchorBlock.1 f₁.1.2 := fun hBad ↦ hb (hBad.trans h₁R.symm)
  have hRepr₁ : (wPart).repr f₁.1.2 = (wPart).repr x := h₁R.symm
  have hSum := NonTrivalentValencyFourTracks.card_ret_add_card_fine cover fd hc hab hOne
    wallStar hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing x
  have hFineLe := NonTrivalentValencyFourTracks.card_fine_le_two cover fd hc hab hOne
    wallStar hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing x
  rw [hB] at hSum
  have hPairSub : ({f₁, f₂} : Finset (wGauged).SourceEdge) ⊆
      (nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x)).filter
        (fun z ↦ wallStar.right pairing z.1.1 = !wRetSide ((wPart).repr x)) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hf₁, hs₁⟩
    · exact Finset.mem_filter.mpr ⟨hf₂, hs₂⟩
  have hPairCard : ({f₁, f₂} : Finset (wGauged).SourceEdge).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hfNe), Finset.card_singleton]
  have hFineGe : 2 ≤ ((nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x)).filter
      (fun z ↦ wallStar.right pairing z.1.1 = !wRetSide ((wPart).repr x))).card := by
    have := Finset.card_le_card hPairSub
    omega
  have hRetOne : ((nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x)).filter
      (fun z ↦ wallStar.right pairing z.1.1 = wRetSide ((wPart).repr x))).card = 1 := by
    omega
  have hFinePair : (nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x)).filter
      (fun z ↦ wallStar.right pairing z.1.1 = !wRetSide ((wPart).repr x)) = {f₁, f₂} := by
    refine (Finset.eq_of_subset_of_card_le hPairSub ?_).symm
    omega
  obtain ⟨z, hzEq⟩ := Finset.card_eq_one.mp hRetOne
  have hzFilter : z ∈ (nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x)).filter
      (fun w ↦ wallStar.right pairing w.1.1 = wRetSide ((wPart).repr x)) := by
    rw [hzEq]
    exact Finset.mem_singleton_self z
  obtain ⟨hzMem, hzSide⟩ := Finset.mem_filter.mp hzFilter
  obtain ⟨hzS, hzA, hzR⟩ := block_star_mem cover fd hc hab hOne wallStar hForest anchorBlock
    hAnchor pairing hzMem
  have hNewPair : (wCand).newSourceEdge f₂.1.2 = (wCand).newSourceEdge f₁.1.2 :=
    (NonTrivalentValencyFourDictionary.newSourceEdge_eq_of_rel wSrc pairing wNG wRam wProf
      wConn wGen wVal
      ((NonTrivalentValencyFourRowEquiv.candidate_newEdge_rel_block wSrc pairing wNG wRam
        wProf wConn wGen wVal hbf₁ f₂.1.2).mpr (by rw [hRepr₁]; exact hcls))).symm
  have hMove : wEpv (!wRetSide ((wPart).repr x)) f₂.1.2 =
      wEpv (!wRetSide ((wPart).repr x)) f₁.1.2 := by
    have h := NonTrivalentValencyFourRowEquiv.endpointVertex_fine_eq wSrc pairing wNG wRam
      wProf wConn wGen wVal hbf₁ (y := f₂.1.2) (by rw [hRepr₁]; exact hcls)
    rwa [hRepr₁] at h
  -- the retaining endpoint has only the retained `z` and the block's new occurrence
  have hRetSubset : nonDanglingIncident (wCand).datum
      (wEpv (wRetSide ((wPart).repr x)) x) ⊆
      {(wCand).oldSourceEdge z, (wCand).newSourceEdge f₁.1.2} := by
    intro w hw
    obtain ⟨hwS, hwI⟩ := (mem_nonDanglingIncident _ _ _).mp hw
    rcases NonTrivalentValencyFourRowEquiv.nonDanglingIncident_ret_dichotomy wSrc pairing wNG
      wRam wProf wConn wGen wVal hb hwS hwI with
      ⟨old, hOldS, hOldA, hOldSide, hOldR, rfl⟩ | ⟨old, hOldS, hOldA, hOldSide, hOldR, rfl⟩
    · have hOldMem : old ∈ (nonDanglingIncident (wGauged)
          ((wGauged).sourceEndpoint wW x)).filter
          (fun w ↦ wallStar.right pairing w.1.1 = wRetSide ((wPart).repr x)) :=
        Finset.mem_filter.mpr ⟨mem_block_star cover fd hc hab hOne wallStar hForest
          anchorBlock hAnchor pairing hOldS hOldA hOldR, hOldSide⟩
      rw [hzEq, Finset.mem_singleton] at hOldMem
      rw [hOldMem]
      exact Finset.mem_insert_self _ _
    · have hOldMem : old ∈ (nonDanglingIncident (wGauged)
          ((wGauged).sourceEndpoint wW x)).filter
          (fun w ↦ wallStar.right pairing w.1.1 = !wRetSide ((wPart).repr x)) :=
        Finset.mem_filter.mpr ⟨mem_block_star cover fd hc hab hOne wallStar hForest
          anchorBlock hAnchor pairing hOldS hOldA hOldR, hOldSide⟩
      rw [hFinePair, Finset.mem_insert, Finset.mem_singleton] at hOldMem
      refine Finset.mem_insert_of_mem (Finset.mem_singleton.mpr ?_)
      rcases hOldMem with rfl | rfl
      · rfl
      · exact hNewPair
  have hOldZIncident : Incident (wCand).datum ((wCand).oldSourceEdge z)
      (wEpv (wRetSide ((wPart).repr x)) x) :=
    NonTrivalentValencyFourRowDictionary.oldSourceEdge_incident_ret wSrc pairing wNG wRam
      wProf wConn wGen wVal hb hzA hzR hzSide
  have hOldZSurv : ¬ IsDangling (wCand).datum ((wCand).oldSourceEdge z) :=
    ResolutionSurvival.not_isDangling_oldSourceEdge (wCand)
      (gaugedData_valid wSrc pairing wNG wRam wVal).1 _ hzS
  have hRetTwo : nonDanglingValency (wCand).datum
      (wEpv (wRetSide ((wPart).repr x)) x) = 2 := by
    have hLe : nonDanglingValency (wCand).datum
        (wEpv (wRetSide ((wPart).repr x)) x) ≤ 2 := by
      rw [← card_nonDanglingIncident]
      exact le_trans (Finset.card_le_card hRetSubset)
        (le_trans (Finset.card_insert_le _ _) (by simp))
    have hNe0 : nonDanglingValency (wCand).datum
        (wEpv (wRetSide ((wPart).repr x)) x) ≠ 0 :=
      ClassInjectivity.nonDanglingValency_ne_zero_of_incident (wCand).datum hOldZSurv
        hOldZIncident
    have hNe1 := NonDanglingValency.nonDanglingValency_ne_one (wCand).datum
      ((wCand).datum_valid (gaugedData_valid wSrc pairing wNG wRam wVal)).1
      (wEpv (wRetSide ((wPart).repr x)) x)
    omega
  have hNewSurv : ¬ IsDangling (wCand).datum ((wCand).newSourceEdge f₁.1.2) := by
    intro hDang
    have hSub : nonDanglingIncident (wCand).datum (wEpv (wRetSide ((wPart).repr x)) x) ⊆
        {(wCand).oldSourceEdge z} := by
      intro w hw
      rcases Finset.mem_insert.mp (hRetSubset hw) with h | h
      · exact Finset.mem_singleton.mpr h
      · exact absurd ((mem_nonDanglingIncident _ _ _).mp hw).1
          (by rw [Finset.mem_singleton] at h; rw [h]; exact fun hh ↦ hh hDang)
    have hLe := Finset.card_le_card hSub
    rw [card_nonDanglingIncident, hRetTwo, Finset.card_singleton] at hLe
    omega
  -- the star map into the common fine endpoint
  have hΦsurv : ∀ (e : NonDanglingEdge (wGauged)),
      e ∈ incidentEdges (wGauged) ((wGauged).sourceEndpoint wW x) →
      ¬ IsDangling (wCand).datum
        (blockEdgePairMap cover fd hc hab hOne wallStar hForest coordinates facet hRows
          hZeroCoord anchorBlock hAnchor pairing x f₁.1.2 e.1) := by
    intro e _
    unfold blockEdgePairMap
    by_cases hs : wallStar.right pairing e.1.1.1 = wRetSide ((wPart).repr x)
    · rw [if_pos hs]
      exact hNewSurv
    · rw [if_neg hs]
      exact ResolutionSurvival.not_isDangling_oldSourceEdge (wCand)
        (gaugedData_valid wSrc pairing wNG wRam wVal).1 e.1 e.2
  have hΦmem : ∀ (e : NonDanglingEdge (wGauged))
      (he : e ∈ incidentEdges (wGauged) ((wGauged).sourceEndpoint wW x)),
      (⟨blockEdgePairMap cover fd hc hab hOne wallStar hForest coordinates facet hRows
        hZeroCoord anchorBlock hAnchor pairing x f₁.1.2 e.1, hΦsurv e he⟩ :
          NonDanglingEdge (wCand).datum) ∈
        incidentEdges (wCand).datum (wEpv (!wRetSide ((wPart).repr x)) f₁.1.2) := by
    intro e he
    have hMem := mem_block_star_of_incidentEdges cover fd hc hab hOne wallStar hForest
      anchorBlock hAnchor pairing x e he
    refine (mem_incidentEdges _ _ _).mpr ?_
    by_cases hs : wallStar.right pairing e.1.1.1 = wRetSide ((wPart).repr x)
    · have hVal : blockEdgePairMap cover fd hc hab hOne wallStar hForest coordinates facet
          hRows hZeroCoord anchorBlock hAnchor pairing x f₁.1.2 e.1 =
          (wCand).newSourceEdge f₁.1.2 := by
        unfold blockEdgePairMap
        rw [if_pos hs]
      show Incident (wCand).datum (blockEdgePairMap cover fd hc hab hOne wallStar hForest
        coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing x f₁.1.2 e.1) _
      rw [hVal]
      exact NonTrivalentValencyFourRows.bridgeEdge_incident wSrc pairing wNG wRam wProf
        wConn wGen wVal (!wRetSide ((wPart).repr x)) f₁.1.2
    · have hVal : blockEdgePairMap cover fd hc hab hOne wallStar hForest coordinates facet
          hRows hZeroCoord anchorBlock hAnchor pairing x f₁.1.2 e.1 =
          (wCand).oldSourceEdge e.1 := by
        unfold blockEdgePairMap
        rw [if_neg hs]
      show Incident (wCand).datum (blockEdgePairMap cover fd hc hab hOne wallStar hForest
        coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing x f₁.1.2 e.1) _
      rw [hVal]
      have hMemF : e.1 ∈ (nonDanglingIncident (wGauged)
          ((wGauged).sourceEndpoint wW x)).filter
          (fun w ↦ wallStar.right pairing w.1.1 = !wRetSide ((wPart).repr x)) :=
        Finset.mem_filter.mpr ⟨hMem,
          NonTrivalentValencyFourRowDictionary.bool_eq_not_of_ne hs⟩
      rw [hFinePair, Finset.mem_insert, Finset.mem_singleton] at hMemF
      obtain ⟨hS, hA, _⟩ := block_star_mem cover fd hc hab hOne wallStar hForest anchorBlock
        hAnchor pairing hMem
      have hI := NonTrivalentValencyFourRows.retainedEdge_incident wSrc pairing wNG wRam
        wProf wConn wGen wVal e.1.1.1 hA (!wRetSide ((wPart).repr x))
        (NonTrivalentValencyFourRowDictionary.bool_eq_not_of_ne hs) e.1.1.2
      rw [GluingDatum.sourceEdge_self] at hI
      rcases hMemF with hEq | hEq
      · rw [hEq] at hI ⊢
        exact hI
      · rw [hEq] at hI ⊢
        rwa [hMove] at hI
  have hΦinj : ∀ (e₁ e₂ : NonDanglingEdge (wGauged))
      (he₁ : e₁ ∈ incidentEdges (wGauged) ((wGauged).sourceEndpoint wW x))
      (he₂ : e₂ ∈ incidentEdges (wGauged) ((wGauged).sourceEndpoint wW x)),
      (⟨blockEdgePairMap cover fd hc hab hOne wallStar hForest coordinates facet hRows
        hZeroCoord anchorBlock hAnchor pairing x f₁.1.2 e₁.1, hΦsurv e₁ he₁⟩ :
          NonDanglingEdge (wCand).datum) =
        ⟨blockEdgePairMap cover fd hc hab hOne wallStar hForest coordinates facet hRows
          hZeroCoord anchorBlock hAnchor pairing x f₁.1.2 e₂.1, hΦsurv e₂ he₂⟩ →
        e₁ = e₂ := by
    intro e₁ e₂ he₁ he₂ hEq
    have hVal : blockEdgePairMap cover fd hc hab hOne wallStar hForest coordinates facet
        hRows hZeroCoord anchorBlock hAnchor pairing x f₁.1.2 e₁.1 =
        blockEdgePairMap cover fd hc hab hOne wallStar hForest coordinates facet hRows
          hZeroCoord anchorBlock hAnchor pairing x f₁.1.2 e₂.1 := congrArg Subtype.val hEq
    unfold blockEdgePairMap at hVal
    by_cases hs₁ : wallStar.right pairing e₁.1.1.1 = wRetSide ((wPart).repr x) <;>
      by_cases hs₂ : wallStar.right pairing e₂.1.1.1 = wRetSide ((wPart).repr x)
    · have hMem₁ : e₁.1 ∈ (nonDanglingIncident (wGauged)
          ((wGauged).sourceEndpoint wW x)).filter
          (fun w ↦ wallStar.right pairing w.1.1 = wRetSide ((wPart).repr x)) :=
        Finset.mem_filter.mpr ⟨mem_block_star_of_incidentEdges cover fd hc hab hOne wallStar
          hForest anchorBlock hAnchor pairing x e₁ he₁, hs₁⟩
      have hMem₂ : e₂.1 ∈ (nonDanglingIncident (wGauged)
          ((wGauged).sourceEndpoint wW x)).filter
          (fun w ↦ wallStar.right pairing w.1.1 = wRetSide ((wPart).repr x)) :=
        Finset.mem_filter.mpr ⟨mem_block_star_of_incidentEdges cover fd hc hab hOne wallStar
          hForest anchorBlock hAnchor pairing x e₂ he₂, hs₂⟩
      rw [hzEq, Finset.mem_singleton] at hMem₁ hMem₂
      exact Subtype.ext (hMem₁.trans hMem₂.symm)
    · rw [if_pos hs₁, if_neg hs₂] at hVal
      exact absurd hVal.symm (NonTrivalentValencyFourRowDictionary.new_ne_old wSrc pairing
        wNG wRam wProf wConn wGen wVal f₁.1.2 e₂.1)
    · rw [if_neg hs₁, if_pos hs₂] at hVal
      exact absurd hVal (NonTrivalentValencyFourRowDictionary.new_ne_old wSrc pairing wNG
        wRam wProf wConn wGen wVal f₁.1.2 e₁.1)
    · rw [if_neg hs₁, if_neg hs₂] at hVal
      exact Subtype.ext (ResolutionCut.oldSourceEdge_injective (wCand) hVal)
  have hThree : nonDanglingValency (wCand).datum
      (wEpv (!wRetSide ((wPart).repr x)) f₁.1.2) = 3 := by
    have hGe := nonDanglingValency_le_of_star_map ((wGauged).sourceEndpoint wW x)
      (wEpv (!wRetSide ((wPart).repr x)) f₁.1.2) _ hΦmem hΦinj
    have hLe := NonTrivalentValencyFourExit.nonDanglingValency_fine_le cover fd hc hab hOne
      wallStar hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing f₁.1.2
      hbf₁
    rw [hRepr₁] at hLe
    omega
  refine ⟨hThree, fun row ↦ ?_⟩
  refine incidenceCount_of_star_map _ _ _
    (NonTrivalentValencyFourTracks.injective_retainedRow cover fd hc hab hOne wallStar
      hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing)
    _ hΦmem ?_ hΦinj (by omega) row
  intro e he
  have hMem := mem_block_star_of_incidentEdges cover fd hc hab hOne wallStar hForest
    anchorBlock hAnchor pairing x e he
  rw [NonTrivalentValencyFourRowDictionary.retainedRow_mk wSrc pairing wNG wRam wProf wConn
    wGen wVal e]
  by_cases hs : wallStar.right pairing e.1.1.1 = wRetSide ((wPart).repr x)
  · have hEz : e.1 = z := by
      have hMem₁ : e.1 ∈ (nonDanglingIncident (wGauged)
          ((wGauged).sourceEndpoint wW x)).filter
          (fun w ↦ wallStar.right pairing w.1.1 = wRetSide ((wPart).repr x)) :=
        Finset.mem_filter.mpr ⟨hMem, hs⟩
      rw [hzEq, Finset.mem_singleton] at hMem₁
      exact hMem₁
    have hVal : blockEdgePairMap cover fd hc hab hOne wallStar hForest coordinates facet
        hRows hZeroCoord anchorBlock hAnchor pairing x f₁.1.2 e.1 =
        (wCand).newSourceEdge f₁.1.2 := by
      unfold blockEdgePairMap
      rw [if_pos hs]
    refine Eq.trans (congrArg NonDanglingEdge.stablePath
      (Subtype.ext hVal : (⟨blockEdgePairMap cover fd hc hab hOne wallStar hForest
        coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing x f₁.1.2 e.1,
        hΦsurv e he⟩ : NonDanglingEdge (wCand).datum) =
        ⟨(wCand).newSourceEdge f₁.1.2, hNewSurv⟩)) ?_
    refine stablePath_eq_of_consecutive ⟨?_, wEpv (wRetSide ((wPart).repr x)) x,
      NonTrivalentValencyFourRowDictionary.newSourceEdge_incident_ret wSrc pairing wNG wRam
        wProf wConn wGen wVal hb h₁R, ?_, hRetTwo⟩
    · intro hBad
      exact NonTrivalentValencyFourRowDictionary.new_ne_old wSrc pairing wNG wRam wProf
        wConn wGen wVal f₁.1.2 e.1 (congrArg Subtype.val hBad).symm
    · show Incident (wCand).datum ((wCand).oldSourceEdge e.1) _
      rw [hEz]
      exact hOldZIncident
  · refine congrArg NonDanglingEdge.stablePath (Subtype.ext ?_)
    show blockEdgePairMap cover fd hc hab hOne wallStar hForest coordinates facet hRows
      hZeroCoord anchorBlock hAnchor pairing x f₁.1.2 e.1 = (wCand).oldSourceEdge e.1
    unfold blockEdgePairMap
    rw [if_neg hs]

/-! ### (T1) at every branch vertex of the gauged wall datum -/

/-- **(T1) at a non-anchor wall block**, in the packaged form
`NonTrivalentValencyFourTracks.candVertex` consumes: some endpoint over the block
is trivalent and keeps the block's whole row-filtered star. -/
theorem exists_block_transport (x : Fin deg)
    (hb : ¬ (wPart).Rel anchorBlock.1 x)
    (hB : nonDanglingValency (wGauged) ((wGauged).sourceEndpoint wW x) = 3) :
    ∃ (side : Bool) (s : Fin deg), (wPart).Rel x s ∧
      nonDanglingValency (wCand).datum (wEpv side s) = 3 ∧
      ∀ row : StablePath (wGauged),
        incidenceCount (wGauged) ((wGauged).sourceEndpoint wW x) row =
          incidenceCount (wCand).datum (wEpv side s) (wRetRow row) := by
  classical
  by_cases hU : ∀ z z' : (wGauged).SourceEdge,
      z ∈ nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x) →
      z' ∈ nonDanglingIncident (wGauged) ((wGauged).sourceEndpoint wW x) →
      wallStar.right pairing z.1.1 = !wRetSide ((wPart).repr x) →
      wallStar.right pairing z'.1.1 = !wRetSide ((wPart).repr x) →
      (wBRes ((wPart).repr x)).newEdge.Rel z.1.2 z'.1.2 → z = z'
  · exact ⟨wRetSide ((wPart).repr x), x, rfl,
      NonTrivalentValencyFourExit.nonDanglingValency_ret_eq_three_of_unique cover fd hc hab
        hOne wallStar hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing
        x hb hB hU,
      incidenceCount_block_unique cover fd hc hab hOne wallStar hForest coordinates facet
        hRows hZeroCoord anchorBlock hAnchor pairing x hb hU⟩
  · push Not at hU
    obtain ⟨f₁, f₂, hf₁, hf₂, hs₁, hs₂, hcls, hfNe⟩ := hU
    obtain ⟨hThree, hCount⟩ := block_pair_transport cover fd hc hab hOne wallStar hForest
      coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing x hb hB f₁ f₂ hf₁ hf₂
      hs₁ hs₂ hcls hfNe
    obtain ⟨-, -, h₁R⟩ := block_star_mem cover fd hc hab hOne wallStar hForest anchorBlock
      hAnchor pairing hf₁
    exact ⟨!wRetSide ((wPart).repr x), f₁.1.2, h₁R, hThree, hCount⟩

/-- **(T1) at a branch vertex over a non-anchor wall block.** -/
theorem incidenceCount_block_candVertex
    (w : {w : BranchVertex (wGauged) //
      w.1 ≠ NonTrivalentValencyFourTracks.gaugedAnchorVertex cover fd hc hab hOne wallStar
        hForest anchorBlock hAnchor pairing})
    (hw : w.1.1.1.1 = wW) (row : StablePath (wGauged)) :
    incidenceCount (wGauged) w.1.1 row =
      incidenceCount (wCand).datum
        (NonTrivalentValencyFourTracks.candVertex cover fd hc hab hOne wallStar hForest
          coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing w)
        (wRetRow row) := by
  classical
  obtain ⟨side, s, hs, hThree, hCount⟩ := exists_block_transport cover fd hc hab hOne
    wallStar hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing
    w.1.1.1.2
    (NonTrivalentValencyFourTracks.not_rel_anchor_of_ne cover fd hc hab hOne wallStar
      hForest anchorBlock hAnchor pairing w.1.1 hw w.2)
    (NonTrivalentValencyFourTracks.nonDanglingValency_gaugedBlock_eq_three cover fd hc hab
      hOne wallStar hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing
      w.1 hw w.2)
  obtain ⟨-, hUniq⟩ := NonTrivalentValencyFourTracks.candVertex_spec_wall cover fd hc hab
    hOne wallStar hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing w hw
  rw [← hUniq side s hs hThree,
    ← NonTrivalentValencyFourTracks.sourceEndpoint_self_gauged cover fd hc hab hOne wallStar
      hForest anchorBlock hAnchor pairing w.1.1 hw]
  exact hCount row

/-- **(T1), at every branch vertex of the gauged wall datum other than the
anchor.**  Off the wall this is
`NonTrivalentValencyFourTracks.incidenceCount_retainedVertex_retainedRow`; over
a non-anchor wall block it is
the block census above. -/
theorem incidenceCount_candVertex
    (w : {w : BranchVertex (wGauged) //
      w.1 ≠ NonTrivalentValencyFourTracks.gaugedAnchorVertex cover fd hc hab hOne wallStar
        hForest anchorBlock hAnchor pairing})
    (row : StablePath (wGauged)) :
    incidenceCount (wGauged) w.1.1 row =
      incidenceCount (wCand).datum
        (NonTrivalentValencyFourTracks.candVertex cover fd hc hab hOne wallStar hForest
          coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing w)
        (wRetRow row) := by
  classical
  by_cases hw : w.1.1.1.1 = wW
  · exact incidenceCount_block_candVertex cover fd hc hab hOne wallStar hForest coordinates
      facet hRows hZeroCoord anchorBlock hAnchor pairing w hw row
  · rw [NonTrivalentValencyFourTracks.candVertex_away cover fd hc hab hOne wallStar hForest
      coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing w hw]
    exact NonTrivalentValencyFourTracks.incidenceCount_retainedVertex_retainedRow cover fd
      hc hab hOne wallStar hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor
      pairing w.1.1 hw row

end Ordinary

/-! ## 2.  The three transports at a four-valent wall of the outer walk -/

section Wall

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)
  (wallStar : W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne)
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
local notation "vRelab" =>
  (NonTrivalentValencyFourKZero.PrescribedPairing.relabeling vSrc pairing vNG vRam)
local notation "vRetRow" =>
  (NonTrivalentValencyFourRowDictionary.retainedRow vSrc pairing vNG vRam vProf vConn vGen
    vVal)
local notation "vBridgeRow" =>
  (NonTrivalentValencyFourRowEquivFinal.bridgeRow vSrc pairing vNG vRam vProf vConn vGen vVal)
local notation "vRowEq" =>
  (NonTrivalentValencyFourRetainedInjective.rowEquiv_of_single_row wd.cover wd.fullDim wd.hc
    wd.hab wd.hOne wallStar (wd.hForest m) wd.coordinates (label m.base) wd.hRows
    wd.hZeroCoord anchorBlock hAnchor pairing)
local notation "vAnchorV" =>
  (NonTrivalentValencyFourTracks.gaugedAnchorVertex wd.cover wd.fullDim wd.hc wd.hab wd.hOne
    wallStar (wd.hForest m) anchorBlock hAnchor pairing)
local notation "vCandV" =>
  (NonTrivalentValencyFourTracks.candVertex wd.cover wd.fullDim wd.hc wd.hab wd.hOne wallStar
    (wd.hForest m) wd.coordinates (label m.base) wd.hRows wd.hZeroCoord anchorBlock hAnchor
    pairing)
local notation "vBranchMap" =>
  (NonTrivalentValencyFourTracks.candBranchMap wd.cover wd.fullDim wd.hc wd.hab wd.hOne
    wallStar (wd.hForest m) wd.coordinates (label m.base) wd.hRows wd.hZeroCoord anchorBlock
    hAnchor pairing)
local notation "vBranchEquiv" =>
  (NonTrivalentValencyFourTracks.candBranchEquiv wd.cover wd.fullDim wd.hc wd.hab wd.hOne
    wallStar (wd.hForest m) wd.coordinates (label m.base) wd.hRows wd.hZeroCoord anchorBlock
    hAnchor pairing)
local notation "vGaugeEquiv" =>
  (NonTrivalentValencyFourTracks.gaugeBranchEquivAnchorComplement wd.cover wd.fullDim wd.hc
    wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor pairing)
local notation "vBranchAC" =>
  (NonTrivalentValencyFourTracks.branchEquivAnchorComplement m wd wallStar anchorBlock
    hAnchor)
local notation "vVertexEquiv" =>
  (NonTrivalentValencyFourTracks.vertexEquiv m wd wallStar anchorBlock hAnchor pairing)
local notation "vOutFD" =>
  (NonTrivalentValencyFourExit.wallOutgoingFD m wd wallStar anchorBlock hAnchor pairing)
local notation "vIncRow" =>
  (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m))

/-! ### (T1) and (T2) -/

/-- **(T1), at every branch vertex of the gauged wall datum other than the
anchor**, read at the wall data of the outer walk. -/
theorem incidenceCount_cand (w : {w : BranchVertex (vGauged) // w.1 ≠ vAnchorV})
    (row : StablePath (vGauged)) :
    incidenceCount (vGauged) w.1.1 row =
      incidenceCount (vCand).datum ((vCandV) w) (vRetRow row) :=
  incidenceCount_candVertex wd.cover wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hForest m)
    wd.coordinates (label m.base) wd.hRows wd.hZeroCoord anchorBlock hAnchor pairing w row

/-- The stable row of the gauged wall datum named by a stable row of the wall
datum, across the block-preserving branch gauge.  It is the row leg against
which `NonTrivalentValencyFourExit.outLabelling_row_retained` is stated. -/
def gaugedRow (p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    StablePath (vGauged) :=
  SheetRelabelStable.stablePathEquiv (vRelab) (vVal).1 p

/-- **(T2), free.**  The block-preserving branch gauge is a sheet relabelling,
so it moves no row-filtered star. -/
theorem incidenceCount_gauge (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (contractDatum wd.cover wd.hc wd.hab wd.hOne) w p =
      incidenceCount (vGauged) ((vRelab).sourceVertexEquiv w)
        (gaugedRow m wd wallStar anchorBlock hAnchor pairing p) :=
  StableGraphIncidence.incidenceCount_sheetRelabel (vRelab) (vVal).1 w p

/-! ### (T3) -/

include wallStar in
/-- The injectivity of the incoming-row map, with no receipt at a four-valent
wall (`noContractedReturn_of_fourStar`). -/
theorem injective_incomingRow : Function.Injective (vIncRow) :=
  WallSplitIncidence.injective_incomingRow_of_noContractedReturn wd.cover wd.fullDim wd.hc
    wd.hab wd.hOne (wd.hCompat m) (wd.hForest m)
    (StablePathFacetContraction.noContractedReturn_of_fourStar wd.cover wd.fullDim wd.hc
      wd.hab wd.hOne wallStar)

include wallStar hAnchor in
/-- **(T3), at every wall-datum vertex other than the anchor.**  Every pruned
fibre of a four-valent wall carries at most one internal occurrence
(`W4IncomingPrunedFibre`), so the valency-agnostic
`WallSplitIncidenceOrdinary.incidenceCount_unramified` applies with no
ramification bookkeeping. -/
theorem incidenceCount_wall_eq_incoming
    (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hne : w ≠ NonTrivalentValencyFourTracks.anchorVertex m wd anchorBlock)
    (u : wd.cover.SourceVertex)
    (hMapU : sourceVertexMap wd.cover wd.hc wd.hab wd.hOne u = w)
    (hThreeU : 3 ≤ nonDanglingValency wd.cover u)
    (p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (contractDatum wd.cover wd.hc wd.hab wd.hOne) w p =
      incidenceCount wd.cover u ((vIncRow) p) :=
  WallSplitIncidenceOrdinary.incidenceCount_unramified wd.cover wd.fullDim wd.hc wd.hab
    wd.hOne (wd.hCompat m) (wd.hForest m) (injective_incomingRow m wd wallStar)
    wd.fullDim.connected w u hMapU hThreeU
    (NonTrivalentValencyFourTracks.wallDatum_trivalent_away_anchor m wd wallStar anchorBlock
      hAnchor w hne)
    wd.fullDim.trivalent
    (W4IncomingPrunedFibre.internalEdges_subsingleton wd.cover wd.fullDim wd.hc wd.hab
      wd.hOne wallStar w) p

/-! ### The dart side, and the chart rows of the outgoing presentation -/

/-- A retained chart row is not the vanishing one. -/
theorem labelling_row_incomingRow_ne_base
    (p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    wd.fullDim.labelling.row ((vIncRow) p) ≠ label m.base := by
  intro hBad
  refine incomingRow_ne_facet wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m)
    (wd.hForest m) wd.coordinates (label m.base) wd.hZeroCoord wd.hPosCoord wd.hFacetZero
    p ?_
  exact (Equiv.eq_symm_apply _).mpr hBad

/-- Away from the two ends of the vanishing occurrence the moved star of a chart
row is the star of the incoming cover. -/
theorem natCard_moved_of_ne (u : BranchVertex wd.cover)
    (hBase : wd.tracks.iso.dart
      (NonTrivalentValencyFourTracks.facetDartLeft m wd wallStar) = m.base)
    (hul : u.1 ≠ NonTrivalentValencyFourTracks.leftEnd m wd)
    (hur : u.1 ≠ NonTrivalentValencyFourTracks.rightEnd m wd)
    (row : StablePath wd.cover) :
    Nat.card {d : D // graph.vert (m.perm d) = wd.tracks.iso.vtx u ∧
        label d = wd.fullDim.labelling.row row} =
      incidenceCount wd.cover u.1 row := by
  have hNeBase : wd.tracks.iso.vtx u ≠ graph.vert m.base := by
    rw [NonTrivalentValencyFourTracks.vert_base_eq m wd wallStar hBase]
    intro hBad
    exact hul (congrArg Subtype.val (wd.tracks.iso.vtx.injective hBad))
  have hNeOp : wd.tracks.iso.vtx u ≠ graph.vert (graph.op m.base) := by
    rw [NonTrivalentValencyFourTracks.vert_opBase_eq m wd wallStar hBase]
    intro hBad
    exact hur (congrArg Subtype.val (wd.tracks.iso.vtx.injective hBad))
  rw [NonTrivalentValencyFourTracks.card_star_eq_incidenceCount m wd u row]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun d ↦ and_congr_left'
    (NonTrivalentValencyFourTracks.move_vert_eq_iff_of_ne m hNeBase hNeOp d))

/-- A retained row of the outgoing presentation keeps the chart coordinate of
its own incoming row (`NonTrivalentValencyFourExit`). -/
theorem outFD_row_retained (p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    (vOutFD).labelling.row
        ((vRetRow) (gaugedRow m wd wallStar anchorBlock hAnchor pairing p)) =
      wd.fullDim.labelling.row ((vIncRow) p) :=
  NonTrivalentValencyFourExit.outLabelling_row_retained wd.cover wd.fullDim wd.hc wd.hab
    wd.hOne wallStar (wd.hForest m) wd.coordinates (label m.base) wd.hRows wd.hZeroCoord
    anchorBlock hAnchor pairing wd.hPosCoord wd.hFacetZero p

/-- The bridge row of the outgoing presentation occupies the vanishing chart row
`label m.base` (`NonTrivalentValencyFourExit`). -/
theorem outFD_row_bridge : (vOutFD).labelling.row (vBridgeRow) = label m.base :=
  NonTrivalentValencyFourExit.outLabelling_row_bridge wd.cover wd.fullDim wd.hc wd.hab
    wd.hOne wallStar (wd.hForest m) wd.coordinates (label m.base) wd.hRows wd.hZeroCoord
    anchorBlock hAnchor pairing wd.hPosCoord wd.hFacetZero

/-! ## 3.  At the anchor -/

/-- The surviving occurrence of the side-`false` target direction named by
`which`, read in the wall datum. -/
def selectedWallEdge (which : Bool) :
    NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne) :=
  ⟨(vSrc).sourceEdge (NonTrivalentValencyFourTracks.selectedLabel pairing false which),
    (vSrc).sourceEdge_survives _⟩

theorem selectedLift_eq (which : Bool) :
    NonTrivalentValencyFourTracks.selectedLift m wd wallStar anchorBlock hAnchor pairing
        false which =
      NonTrivalentValencyFourTracks.liftEdge m wd
        (selectedWallEdge m wd wallStar anchorBlock hAnchor pairing which) := rfl

/-- The gauge carries that occurrence to
`NonTrivalentValencyFourDictionary.survivorEdge`. -/
theorem sourceEdgeEquiv_selectedWallEdge (which : Bool) :
    (vRelab).sourceEdgeEquiv
        (selectedWallEdge m wd wallStar anchorBlock hAnchor pairing which).1 =
      NonTrivalentValencyFourDictionary.survivorEdge vSrc pairing vNG vRam
        (NonTrivalentValencyFourTracks.selectedLabel pairing false which) :=
  SheetRelabelPruning.sourceEdgeEquiv_sourceEdge (vRelab) _ _

/-- The retained copy at `A_1` of one side-`false` anchor survivor. -/
def selectedCandEdge (which : Bool) : NonDanglingEdge (vCand).datum :=
  ResolutionAwayFromWall.retainedEdge (vCand) (gaugedData_valid vSrc pairing vNG vRam vVal).1
    (SheetRelabelStable.nonDanglingEdgeEquiv (vRelab) (vVal).1
      (selectedWallEdge m wd wallStar anchorBlock hAnchor pairing which))

theorem selectedCandEdge_val_false :
    (selectedCandEdge m wd wallStar anchorBlock hAnchor pairing false).1 =
      (vCand).oldSourceEdge
        (NonTrivalentValencyFourDictionary.survivorEdge vSrc pairing vNG vRam
          (PrescribedPairing.firstLabel pairing false)) :=
  congrArg (vCand).oldSourceEdge
    (sourceEdgeEquiv_selectedWallEdge m wd wallStar anchorBlock hAnchor pairing false)

theorem selectedCandEdge_val_true :
    (selectedCandEdge m wd wallStar anchorBlock hAnchor pairing true).1 =
      (vCand).oldSourceEdge
        (NonTrivalentValencyFourDictionary.survivorEdge vSrc pairing vNG vRam
          (PrescribedPairing.secondLabel pairing false)) :=
  congrArg (vCand).oldSourceEdge
    (sourceEdgeEquiv_selectedWallEdge m wd wallStar anchorBlock hAnchor pairing true)

/-- Its row is the retained row of the survivor's own wall row. -/
theorem stablePath_selectedCandEdge (which : Bool) :
    (selectedCandEdge m wd wallStar anchorBlock hAnchor pairing which).stablePath =
      (vRetRow) (gaugedRow m wd wallStar anchorBlock hAnchor pairing
        (selectedWallEdge m wd wallStar anchorBlock hAnchor pairing which).stablePath) := by
  unfold gaugedRow
  rw [SheetRelabelStable.stablePathEquiv_mk]
  exact (NonTrivalentValencyFourRowDictionary.retainedRow_mk vSrc pairing vNG vRam vProf
    vConn vGen vVal _).symm

/-- The bridge occurrence, as a surviving occurrence of the candidate. -/
def bridgeND : NonDanglingEdge (vCand).datum :=
  ⟨NonTrivalentValencyFourRows.bridgeEdge vSrc pairing vNG vRam vProf vConn vGen vVal
      (selectedRepresentative vSrc pairing),
    NonTrivalentValencyFourDictionary.bridgeEdge_survives vSrc pairing vNG vRam vProf vConn
      vGen vVal⟩

theorem stablePath_bridgeND :
    (bridgeND m wd wallStar anchorBlock hAnchor pairing).stablePath = (vBridgeRow) := rfl

theorem selectedCandEdge_ne :
    selectedCandEdge m wd wallStar anchorBlock hAnchor pairing false ≠
      selectedCandEdge m wd wallStar anchorBlock hAnchor pairing true := by
  intro hBad
  have hVal : (vCand).oldSourceEdge
      (NonTrivalentValencyFourDictionary.survivorEdge vSrc pairing vNG vRam
        (PrescribedPairing.firstLabel pairing false)) =
      (vCand).oldSourceEdge
        (NonTrivalentValencyFourDictionary.survivorEdge vSrc pairing vNG vRam
          (PrescribedPairing.secondLabel pairing false)) := by
    rw [← selectedCandEdge_val_false m wd wallStar anchorBlock hAnchor pairing,
      ← selectedCandEdge_val_true m wd wallStar anchorBlock hAnchor pairing]
    exact congrArg Subtype.val hBad
  exact NonTrivalentValencyFourDictionary.survivorEdge_ne vSrc pairing vNG vRam
    (PrescribedPairing.firstLabel_ne_secondLabel pairing false)
    (ResolutionCut.oldSourceEdge_injective (vCand) hVal)

/-- **The exact star at `A_1`** of `NonTrivalentValencyFourDictionary`, read on
surviving occurrences: the bridge
and the retained copies of the two survivors that the pairing assigns to the
side `false`. -/
theorem incidentEdges_endpointVertex_false :
    incidentEdges (vCand).datum
        ((vEpv) false (selectedRepresentative vSrc pairing)) =
      {bridgeND m wd wallStar anchorBlock hAnchor pairing,
        selectedCandEdge m wd wallStar anchorBlock hAnchor pairing false,
        selectedCandEdge m wd wallStar anchorBlock hAnchor pairing true} := by
  classical
  ext e
  rw [mem_incidentEdges]
  constructor
  · intro hInc
    have h : e.1 ∈ nonDanglingIncident (vCand).datum
        ((vEpv) false (selectedRepresentative vSrc pairing)) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨e.2, hInc⟩
    rw [NonTrivalentValencyFourDictionary.nonDanglingIncident_endpointVertex vSrc pairing
      vNG vRam vProf vConn vGen vVal false] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
    rcases h with h | h | h
    · exact Or.inl (Subtype.ext h)
    · refine Or.inr (Or.inl (Subtype.ext ?_))
      rw [selectedCandEdge_val_false m wd wallStar anchorBlock hAnchor pairing]
      exact h
    · refine Or.inr (Or.inr (Subtype.ext ?_))
      rw [selectedCandEdge_val_true m wd wallStar anchorBlock hAnchor pairing]
      exact h
  · intro h
    have h2 : e.1 ∈ nonDanglingIncident (vCand).datum
        ((vEpv) false (selectedRepresentative vSrc pairing)) := by
      rw [NonTrivalentValencyFourDictionary.nonDanglingIncident_endpointVertex vSrc pairing
        vNG vRam vProf vConn vGen vVal false]
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl
      · exact Finset.mem_insert_self _ _
      · rw [selectedCandEdge_val_false m wd wallStar anchorBlock hAnchor pairing]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · rw [selectedCandEdge_val_true m wd wallStar anchorBlock hAnchor pairing]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    exact ((mem_nonDanglingIncident _ _ _).mp h2).2

/-- The chart label of the dart of a side-`false` anchor survivor. -/
theorem label_dart_selected (d : StableSourceDarts.Dart wd.cover) (which : Bool)
    (hd : d.2.1 = NonTrivalentValencyFourTracks.selectedLift m wd wallStar anchorBlock
      hAnchor pairing false which) :
    label (wd.tracks.iso.dart d) = wd.fullDim.labelling.row ((vIncRow)
      (selectedWallEdge m wd wallStar anchorBlock hAnchor pairing which).stablePath) := by
  rw [wd.tracks.row_map d]
  refine congrArg wd.fullDim.labelling.row ?_
  show NonDanglingEdge.stablePath d.2.1 = _
  rw [hd, selectedLift_eq m wd wallStar anchorBlock hAnchor pairing which]
  exact NonTrivalentValencyFourTracks.stablePath_liftEdge m wd _

theorem label_dart_selected_iff (d : StableSourceDarts.Dart wd.cover) (which : Bool)
    (hd : d.2.1 = NonTrivalentValencyFourTracks.selectedLift m wd wallStar anchorBlock
      hAnchor pairing false which)
    (p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    (label (wd.tracks.iso.dart d) = wd.fullDim.labelling.row ((vIncRow) p)) ↔
      (selectedWallEdge m wd wallStar anchorBlock hAnchor pairing which).stablePath = p := by
  rw [label_dart_selected m wd wallStar anchorBlock hAnchor pairing d which hd]
  constructor
  · intro h
    exact injective_incomingRow m wd wallStar (wd.fullDim.labelling.row.injective h)
  · intro h
    exact congrArg _ (congrArg _ h)

theorem label_dart_selected_ne_base (d : StableSourceDarts.Dart wd.cover) (which : Bool)
    (hd : d.2.1 = NonTrivalentValencyFourTracks.selectedLift m wd wallStar anchorBlock
      hAnchor pairing false which) :
    label (wd.tracks.iso.dart d) ≠ label m.base := by
  rw [label_dart_selected m wd wallStar anchorBlock hAnchor pairing d which hd]
  exact labelling_row_incomingRow_ne_base m wd _

theorem stablePath_selectedCandEdge_iff (which : Bool)
    (p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    ((selectedCandEdge m wd wallStar anchorBlock hAnchor pairing which).stablePath =
        (vRetRow) (gaugedRow m wd wallStar anchorBlock hAnchor pairing p)) ↔
      (selectedWallEdge m wd wallStar anchorBlock hAnchor pairing which).stablePath = p := by
  rw [stablePath_selectedCandEdge m wd wallStar anchorBlock hAnchor pairing which]
  constructor
  · intro h
    refine (SheetRelabelStable.stablePathEquiv (vRelab) (vVal).1).injective ?_
    exact NonTrivalentValencyFourTracks.injective_retainedRow wd.cover wd.fullDim wd.hc
      wd.hab wd.hOne wallStar (wd.hForest m) wd.coordinates (label m.base) wd.hRows
      wd.hZeroCoord anchorBlock hAnchor pairing h
  · intro h
    exact congrArg _ (congrArg _ h)

/-- **The star count at `A_1`, on a retained row.**  The exact star of
`NonTrivalentValencyFourDictionary` is matched dart by dart with the star (H-IV)
prescribes: `m.base` carries the vanishing chart row, and the two remaining darts
carry the incoming rows of the two side-`false` anchor survivors. -/
theorem incidence_inr_false_retained
    (hPres : NonTrivalentValencyFourTracks.PrescribedPairingMove m wd wallStar anchorBlock
      hAnchor pairing)
    (p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (vCand).datum ((vBranchMap) (Sum.inr false)).1
        ((vRetRow) (gaugedRow m wd wallStar anchorBlock hAnchor pairing p)) =
      Nat.card {d : D // graph.vert (m.perm d) =
          (vVertexEquiv) ((vBranchMap) (Sum.inr false)) ∧
        label d = (vOutFD).labelling.row
          ((vRetRow) (gaugedRow m wd wallStar anchorBlock hAnchor pairing p))} := by
  classical
  obtain ⟨hBase, first, second, hFirst, hSecond, hStar⟩ := hPres
  rw [NonTrivalentValencyFourTracks.vertexEquiv_anchor_false m wd wallStar anchorBlock
      hAnchor pairing hBase,
    outFD_row_retained m wd wallStar anchorBlock hAnchor pairing p]
  have hRHS : Nat.card {d : D // graph.vert (m.perm d) = graph.vert m.base ∧
      label d = wd.fullDim.labelling.row ((vIncRow) p)} =
      ((Finset.univ.filter fun d : D ↦ graph.vert (m.perm d) = graph.vert m.base).filter
        fun d ↦ label d = wd.fullDim.labelling.row ((vIncRow) p)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter]
  have hBridgeRow : ¬ ((bridgeND m wd wallStar anchorBlock hAnchor pairing).stablePath =
      (vRetRow) (gaugedRow m wd wallStar anchorBlock hAnchor pairing p)) := by
    rw [stablePath_bridgeND m wd wallStar anchorBlock hAnchor pairing]
    exact fun h ↦ NonTrivalentValencyFourRowDictionary.retainedRow_ne_bridgeRow vSrc pairing
      vNG vRam vProf vConn vGen vVal _ h.symm
  rw [hRHS, NonTrivalentValencyThreeStarCount.filter_moved_base m wd first second hStar,
    Finset.filter_insert,
    if_neg (Ne.symm (labelling_row_incomingRow_ne_base m wd p)),
    NonTrivalentValencyThreeStarCount.card_filter_pair _ _
      (NonTrivalentValencyThreeStarCount.dart_ne m wd first second hStar)]
  show incidenceCount (vCand).datum ((vEpv) false (selectedRepresentative vSrc pairing))
    ((vRetRow) (gaugedRow m wd wallStar anchorBlock hAnchor pairing p)) = _
  unfold incidenceCount
  rw [incidentEdges_endpointVertex_false m wd wallStar anchorBlock hAnchor pairing,
    Finset.filter_insert, if_neg hBridgeRow,
    NonTrivalentValencyThreeStarCount.card_filter_pair _ _
      (selectedCandEdge_ne m wd wallStar anchorBlock hAnchor pairing),
    if_congr (stablePath_selectedCandEdge_iff m wd wallStar anchorBlock hAnchor pairing
      false p) rfl rfl,
    if_congr (stablePath_selectedCandEdge_iff m wd wallStar anchorBlock hAnchor pairing
      true p) rfl rfl,
    if_congr (label_dart_selected_iff m wd wallStar anchorBlock hAnchor pairing first false
      hFirst p) rfl rfl,
    if_congr (label_dart_selected_iff m wd wallStar anchorBlock hAnchor pairing second true
      hSecond p) rfl rfl]

/-- **The star count at `A_1`, on the bridge row.**  Both sides are one: the
bridge occurrence `h_1` downstairs, the contracted dart `m.base` upstairs. -/
theorem incidence_inr_false_bridge
    (hPres : NonTrivalentValencyFourTracks.PrescribedPairingMove m wd wallStar anchorBlock
      hAnchor pairing) :
    incidenceCount (vCand).datum ((vBranchMap) (Sum.inr false)).1 (vBridgeRow) =
      Nat.card {d : D // graph.vert (m.perm d) =
          (vVertexEquiv) ((vBranchMap) (Sum.inr false)) ∧
        label d = (vOutFD).labelling.row (vBridgeRow)} := by
  classical
  obtain ⟨hBase, first, second, hFirst, hSecond, hStar⟩ := hPres
  rw [NonTrivalentValencyFourTracks.vertexEquiv_anchor_false m wd wallStar anchorBlock
      hAnchor pairing hBase,
    outFD_row_bridge m wd wallStar anchorBlock hAnchor pairing]
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
    · exact label_dart_selected_ne_base m wd wallStar anchorBlock hAnchor pairing first
        false hFirst
    · exact label_dart_selected_ne_base m wd wallStar anchorBlock hAnchor pairing second
        true hSecond
  have hR : ((Finset.univ.filter fun d : D ↦ graph.vert (m.perm d) = graph.vert m.base).filter
      fun d ↦ label d = label m.base).card = 1 := by
    rw [NonTrivalentValencyThreeStarCount.filter_moved_base m wd first second hStar,
      Finset.filter_insert, if_pos rfl, hEmptyD]
    simp
  rw [hRHS, hR]
  show incidenceCount (vCand).datum ((vEpv) false (selectedRepresentative vSrc pairing))
    (vBridgeRow) = 1
  have hEmptyC : (({selectedCandEdge m wd wallStar anchorBlock hAnchor pairing false,
      selectedCandEdge m wd wallStar anchorBlock hAnchor pairing true} :
        Finset (NonDanglingEdge (vCand).datum)).filter
      fun e ↦ e.stablePath = (vBridgeRow)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · rw [stablePath_selectedCandEdge m wd wallStar anchorBlock hAnchor pairing false]
      exact NonTrivalentValencyFourRowDictionary.retainedRow_ne_bridgeRow vSrc pairing vNG
        vRam vProf vConn vGen vVal _
    · rw [stablePath_selectedCandEdge m wd wallStar anchorBlock hAnchor pairing true]
      exact NonTrivalentValencyFourRowDictionary.retainedRow_ne_bridgeRow vSrc pairing vNG
        vRam vProf vConn vGen vVal _
  unfold incidenceCount
  rw [incidentEdges_endpointVertex_false m wd wallStar anchorBlock hAnchor pairing,
    Finset.filter_insert,
    if_pos (stablePath_bridgeND m wd wallStar anchorBlock hAnchor pairing), hEmptyC]
  simp

/-! ## 4.  Away from the anchor -/

/-- **The star count at a branch vertex away from the anchor, on a retained
row.**  It is (T1), then (T2), then (T3), then the incoming tracking. -/
theorem incidence_inl_retained
    (hBase : wd.tracks.iso.dart
      (NonTrivalentValencyFourTracks.facetDartLeft m wd wallStar) = m.base)
    (w : {w : BranchVertex (vGauged) // w.1 ≠ vAnchorV})
    (p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (vCand).datum ((vBranchMap) (Sum.inl w)).1
        ((vRetRow) (gaugedRow m wd wallStar anchorBlock hAnchor pairing p)) =
      Nat.card {d : D // graph.vert (m.perm d) =
          (vVertexEquiv) ((vBranchMap) (Sum.inl w)) ∧
        label d = (vOutFD).labelling.row
          ((vRetRow) (gaugedRow m wd wallStar anchorBlock hAnchor pairing p))} := by
  classical
  have hGauge : w.1.1 = (vRelab).sourceVertexEquiv ((vGaugeEquiv).symm w).1.1 :=
    (congrArg (fun y ↦ y.1.1) ((vGaugeEquiv).apply_symm_apply w)).symm.trans
      (NonTrivalentValencyFourTracks.gaugeBranchEquivAnchorComplement_apply wd.cover
        wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor pairing
        ((vGaugeEquiv).symm w))
  have hMapU : sourceVertexMap wd.cover wd.hc wd.hab wd.hOne
      ((vBranchAC).symm ((vGaugeEquiv).symm w)).1.1 = ((vGaugeEquiv).symm w).1.1 :=
    (NonTrivalentValencyFourTracks.branchEquivAnchorComplement_apply m wd wallStar
      anchorBlock hAnchor ((vBranchAC).symm ((vGaugeEquiv).symm w))).symm.trans
      (congrArg (fun y ↦ y.1.1) ((vBranchAC).apply_symm_apply ((vGaugeEquiv).symm w)))
  rw [NonTrivalentValencyFourTracks.vertexEquiv_inl m wd wallStar anchorBlock hAnchor
      pairing w,
    outFD_row_retained m wd wallStar anchorBlock hAnchor pairing p,
    natCard_moved_of_ne m wd wallStar ((vBranchAC).symm ((vGaugeEquiv).symm w)).1 hBase
      ((vBranchAC).symm ((vGaugeEquiv).symm w)).2.1
      ((vBranchAC).symm ((vGaugeEquiv).symm w)).2.2]
  refine Eq.trans ?_ (incidenceCount_wall_eq_incoming m wd wallStar anchorBlock hAnchor
    ((vGaugeEquiv).symm w).1.1 ((vGaugeEquiv).symm w).2
    ((vBranchAC).symm ((vGaugeEquiv).symm w)).1.1 hMapU
    ((vBranchAC).symm ((vGaugeEquiv).symm w)).1.2 p)
  rw [incidenceCount_gauge m wd wallStar anchorBlock hAnchor pairing
    ((vGaugeEquiv).symm w).1.1 p, ← hGauge]
  exact (incidenceCount_cand m wd wallStar anchorBlock hAnchor pairing w
    (gaugedRow m wd wallStar anchorBlock hAnchor pairing p)).symm

include wallStar in
/-- The vanishing row of the incoming cover meets only the two ends of its
single occurrence. -/
theorem incidenceCount_facetRow_eq_zero (v : wd.cover.SourceVertex)
    (hl : v ≠ NonTrivalentValencyFourTracks.leftEnd m wd)
    (hr : v ≠ NonTrivalentValencyFourTracks.rightEnd m wd) :
    incidenceCount wd.cover v (NonTrivalentValencyFourTracks.facetRow m wd) = 0 := by
  classical
  unfold incidenceCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hRow
  have hEq := NonTrivalentValencyFourTracks.eq_facetEdge m wd wallStar e hRow
  have hInc := (mem_incidentEdges _ _ _).mp he
  rw [hEq] at hInc
  rcases hInc with h | h
  · exact hl h.symm
  · exact hr h.symm

/-- A branch vertex of the candidate away from the anchor is neither `A_1` nor
`A_2`. -/
theorem endpointVertex_ne_candBranchMap_inl (side : Bool)
    (w : {w : BranchVertex (vGauged) // w.1 ≠ vAnchorV}) :
    (vEpv) side (selectedRepresentative vSrc pairing) ≠ ((vBranchMap) (Sum.inl w)).1 := by
  intro hBad
  exact Sum.inr_ne_inl (NonTrivalentValencyFourTracks.candBranchMap_injective wd.cover
    wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hForest m) wd.coordinates (label m.base)
    wd.hRows wd.hZeroCoord anchorBlock hAnchor pairing (Subtype.ext hBad))

/-- The bridge row does not reach a branch vertex of the candidate away from the
anchor: its only occurrence joins `A_1` to `A_2`. -/
theorem incidenceCount_bridgeRow_inl_eq_zero
    (w : {w : BranchVertex (vGauged) // w.1 ≠ vAnchorV}) :
    incidenceCount (vCand).datum ((vBranchMap) (Sum.inl w)).1 (vBridgeRow) = 0 := by
  classical
  unfold incidenceCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hRow
  have hVal := NonTrivalentValencyFourDictionary.bridgeEdge_isolated vSrc pairing vNG vRam
    vProf vConn vGen vVal e hRow
  have hInc := (mem_incidentEdges _ _ _).mp he
  rw [hVal] at hInc
  have hInc' : ((vCand).datum.sourceEnds
        (NonTrivalentValencyFourRows.bridgeEdge vSrc pairing vNG vRam vProf vConn vGen vVal
          (selectedRepresentative vSrc pairing))).1 = ((vBranchMap) (Sum.inl w)).1 ∨
      ((vCand).datum.sourceEnds
        (NonTrivalentValencyFourRows.bridgeEdge vSrc pairing vNG vRam vProf vConn vGen vVal
          (selectedRepresentative vSrc pairing))).2 = ((vBranchMap) (Sum.inl w)).1 := hInc
  rw [NonTrivalentValencyFourDictionary.sourceEnds_bridgeEdge vSrc pairing vNG vRam vProf
    vConn vGen vVal _] at hInc'
  rcases hInc' with h | h
  · exact endpointVertex_ne_candBranchMap_inl m wd wallStar anchorBlock hAnchor pairing
      false w h
  · exact endpointVertex_ne_candBranchMap_inl m wd wallStar anchorBlock hAnchor pairing
      true w h

/-- **The star count at a branch vertex away from the anchor, on the bridge
row.**  Both sides vanish: downstairs the bridge joins `A_1` to `A_2`, upstairs
the vanishing chart row is the single occurrence `h_1`. -/
theorem incidence_inl_bridge
    (hBase : wd.tracks.iso.dart
      (NonTrivalentValencyFourTracks.facetDartLeft m wd wallStar) = m.base)
    (w : {w : BranchVertex (vGauged) // w.1 ≠ vAnchorV}) :
    incidenceCount (vCand).datum ((vBranchMap) (Sum.inl w)).1 (vBridgeRow) =
      Nat.card {d : D // graph.vert (m.perm d) =
          (vVertexEquiv) ((vBranchMap) (Sum.inl w)) ∧
        label d = (vOutFD).labelling.row (vBridgeRow)} := by
  classical
  rw [incidenceCount_bridgeRow_inl_eq_zero m wd wallStar anchorBlock hAnchor pairing w]
  symm
  rw [NonTrivalentValencyFourTracks.vertexEquiv_inl m wd wallStar anchorBlock hAnchor
      pairing w,
    outFD_row_bridge m wd wallStar anchorBlock hAnchor pairing]
  have h := natCard_moved_of_ne m wd wallStar ((vBranchAC).symm ((vGaugeEquiv).symm w)).1
    hBase ((vBranchAC).symm ((vGaugeEquiv).symm w)).2.1
    ((vBranchAC).symm ((vGaugeEquiv).symm w)).2.2
    (NonTrivalentValencyFourTracks.facetRow m wd)
  rw [show wd.fullDim.labelling.row (NonTrivalentValencyFourTracks.facetRow m wd) =
    label m.base from Equiv.apply_symm_apply _ _] at h
  refine h.trans (incidenceCount_facetRow_eq_zero m wd wallStar _ ?_ ?_)
  · exact ((vBranchAC).symm ((vGaugeEquiv).symm w)).2.1
  · exact ((vBranchAC).symm ((vGaugeEquiv).symm w)).2.2

/-! ## 5.  The leftover equation at `A_2`, and the link -/

/-- Every stable row of the candidate is the bridge row or a retained row of the
wall datum. -/
theorem stablePath_cases (r : StablePath (vCand).datum) :
    r = (vBridgeRow) ∨ ∃ p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne),
      r = (vRetRow) (gaugedRow m wd wallStar anchorBlock hAnchor pairing p) := by
  classical
  rcases hEq : (vRowEq) r with _ | r₀
  · refine Or.inl ((vRowEq).injective ?_)
    rw [hEq, NonTrivalentValencyFourExit.rowEquiv_bridgeRow wd.cover wd.fullDim wd.hc wd.hab
      wd.hOne wallStar (wd.hForest m) wd.coordinates (label m.base) wd.hRows wd.hZeroCoord
      anchorBlock hAnchor pairing]
  · refine Or.inr ⟨(SheetRelabelStable.stablePathEquiv (vRelab) (vVal).1).symm r₀,
      (vRowEq).injective ?_⟩
    rw [hEq, NonTrivalentValencyFourRetainedInjective.rowEquiv_of_single_row_retainedRow
      wd.cover wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hForest m) wd.coordinates
      (label m.base) wd.hRows wd.hZeroCoord anchorBlock hAnchor pairing]
    exact congrArg some
      ((SheetRelabelStable.stablePathEquiv (vRelab) (vVal).1).apply_symm_apply r₀).symm

/-- **The star count at every branch vertex except `A_2`.** -/
theorem incidence_of_ne_rightAnchor
    (hPres : NonTrivalentValencyFourTracks.PrescribedPairingMove m wd wallStar anchorBlock
      hAnchor pairing)
    (v : BranchVertex (vCand).datum) (hv : v ≠ (vBranchMap) (Sum.inr true))
    (r : StablePath (vCand).datum) :
    incidenceCount (vCand).datum v.1 r =
      Nat.card {d : D // graph.vert (m.perm d) = (vVertexEquiv) v ∧
        label d = (vOutFD).labelling.row r} := by
  classical
  obtain ⟨x, rfl⟩ : ∃ x, (vBranchMap) x = v :=
    ⟨(vBranchEquiv).symm v, (vBranchEquiv).apply_symm_apply v⟩
  rcases stablePath_cases m wd wallStar anchorBlock hAnchor pairing r with rfl | ⟨p, rfl⟩
  · cases x with
    | inl w =>
      exact incidence_inl_bridge m wd wallStar anchorBlock hAnchor pairing hPres.1 w
    | inr side =>
      cases side with
      | true => exact absurd rfl hv
      | false =>
        exact incidence_inr_false_bridge m wd wallStar anchorBlock hAnchor pairing hPres
  · cases x with
    | inl w =>
      exact incidence_inl_retained m wd wallStar anchorBlock hAnchor pairing hPres.1 w p
    | inr side =>
      cases side with
      | true => exact absurd rfl hv
      | false =>
        exact incidence_inr_false_retained m wd wallStar anchorBlock hAnchor pairing hPres p

/-- **The star count at `A_2`, from the leftover equation.**  A stable row of the
candidate meets its branch vertices twice in all, a chart row carries two darts
of the moved graph, `vertexEquiv` is a bijection, and the count agrees at every
other branch vertex; so it agrees at `A_2` too. -/
theorem incidence_inr_true
    (hPres : NonTrivalentValencyFourTracks.PrescribedPairingMove m wd wallStar anchorBlock
      hAnchor pairing)
    (r : StablePath (vCand).datum) :
    incidenceCount (vCand).datum ((vBranchMap) (Sum.inr true)).1 r =
      Nat.card {d : D // graph.vert (m.perm d) = (vVertexEquiv) ((vBranchMap) (Sum.inr true)) ∧
        label d = (vOutFD).labelling.row r} := by
  classical
  set v₀ := (vBranchMap) (Sum.inr true) with hv₀
  set f : BranchVertex (vCand).datum → ℕ :=
    fun v ↦ incidenceCount (vCand).datum v.1 r with hf
  set g : BranchVertex (vCand).datum → ℕ :=
    fun v ↦ Nat.card {d : D // graph.vert (m.perm d) = (vVertexEquiv) v ∧
      label d = (vOutFD).labelling.row r} with hg
  have hSumF : ∑ v, f v = 2 :=
    NonTrivalentValencyThreeStarCount.sum_incidenceCount_branchVertex (vCand).datum
      (vOutFD).connected (vOutFD).pathEnds r
  have hSumG : ∑ v, g v = 2 := by
    rw [Fintype.sum_equiv (vVertexEquiv) g
      (fun x : V ↦ Nat.card {d : D // graph.vert (m.perm d) = x ∧
        label d = (vOutFD).labelling.row r}) (fun v ↦ rfl)]
    exact NonTrivalentValencyThreeStarCount.sum_natCard_moved m wd ((vOutFD).labelling.row r)
  have hAway : ∀ v ∈ Finset.univ.erase v₀, f v = g v := by
    intro v hv
    exact incidence_of_ne_rightAnchor m wd wallStar anchorBlock hAnchor pairing hPres v
      (Finset.mem_erase.mp hv).1 r
  have hfsum := Finset.add_sum_erase Finset.univ f (Finset.mem_univ v₀)
  have hgsum := Finset.add_sum_erase Finset.univ g (Finset.mem_univ v₀)
  have hEq : ∑ x ∈ Finset.univ.erase v₀, f x = ∑ x ∈ Finset.univ.erase v₀, g x :=
    Finset.sum_congr rfl hAway
  show f v₀ = g v₀
  omega

/-- **The star count, at every branch vertex and every row.**  This is the one
geometric hypothesis of `NonTrivalentValencyFourTracks.typeChangeLink_of_incidence`,
proved here under (H-IV). -/
theorem incidence_of_prescribedPairingMove
    (hPres : NonTrivalentValencyFourTracks.PrescribedPairingMove m wd wallStar anchorBlock
      hAnchor pairing)
    (v : BranchVertex (vCand).datum) (r : StablePath (vCand).datum) :
    incidenceCount (vCand).datum v.1 r =
      Nat.card {d : D // graph.vert (m.perm d) = (vVertexEquiv) v ∧
        label d = (vOutFD).labelling.row r} := by
  classical
  by_cases hv : v = (vBranchMap) (Sum.inr true)
  · subst hv
    exact incidence_inr_true m wd wallStar anchorBlock hAnchor pairing hPres r
  · exact incidence_of_ne_rightAnchor m wd wallStar anchorBlock hAnchor pairing hPres v hv r

/-- **`OuterWalk.TypeChangeLink` at a four-valent wall under (H-IV).**
`NonTrivalentValencyFourTracks` reduces the link to the star count; this
proves it. -/
def typeChangeLink_of_prescribedPairingMove
    (hPres : NonTrivalentValencyFourTracks.PrescribedPairingMove m wd wallStar anchorBlock
      hAnchor pairing) :
    TypeChangeLink m wd :=
  NonTrivalentValencyFourTracks.typeChangeLink_of_incidence m wd wallStar anchorBlock
    hAnchor pairing
    (incidence_of_prescribedPairingMove m wd wallStar anchorBlock hAnchor pairing hPres)

end Wall

/-! ## 6.  The link at an actual four-valent wall -/

section Corollary

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)

/-- **`OuterWalk.TypeChangeLink` at an actual four-valent wall, from the valency
hypothesis `h4`, the prescribed pairing and (H-IV) alone.**  The four-valent
target star, the anchor block and its surviving valency four come from
`exists_anchor_of_wallData` (in `NonTrivalentValencyFourExitLink`), so the only
inputs are `pairing` and (H-IV). -/
theorem nonempty_typeChangeLink_of_prescribedPairingMove
    (h4 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 4) (pairing : Fin 3)
    (hPres : ∀ (wallStar : W4TargetPairings.FourStar
        (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
      (anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
      (hAnchor : nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩ anchorBlock) = 4),
      NonTrivalentValencyFourTracks.PrescribedPairingMove m wd wallStar anchorBlock hAnchor
        pairing) :
    Nonempty (TypeChangeLink m wd) := by
  obtain ⟨wallStar⟩ : Nonempty (W4TargetPairings.FourStar
      (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :=
    ⟨W4TargetPairings.FourStar.of_card h4⟩
  obtain ⟨anchorBlock, hAnchor⟩ :=
    NonTrivalentUniqueFourValent.exists_wallBlock_nonDanglingValency_eq_four wd.cover
      wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hCompat m) wd.coordinates (label m.base)
      wd.hZeroCoord wd.hPosCoord wd.hFacetZero
  exact ⟨typeChangeLink_of_prescribedPairingMove m wd wallStar anchorBlock hAnchor pairing
    (hPres wallStar anchorBlock hAnchor)⟩

end Corollary

end

end DraismaVargas.LocalCases.NonTrivalentValencyFourStarCount
