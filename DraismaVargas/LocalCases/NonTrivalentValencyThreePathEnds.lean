import DraismaVargas.LocalCases.WallDatumPathEnds
import DraismaVargas.LocalCases.NonTrivalentValencyThreeExit

/-!
# `HasPathEnds` of the valency-three Type III candidate, and the finished link

Source: Vargas, Part II (arXiv:2609.09109), Section 5.1 (Lemma
`lemma-above-w0`, the labelling convention, and the vanishing-row no-return
dichotomy) together with Section 5.3 (Case `{v3-nd4}`, Type III, base tree
`T2`).

`NonTrivalentValencyThreeExit.outgoingFD` / `.typeChangeLink_of_receipts`
assemble the outgoing full-dimensional presentation at a three-valent wall with
exactly two geometric fields as hypotheses: `hPathEnds :
W4StableSource.HasPathEnds (Prescribed.validCandidate src hNoGlue hValid).datum`,
reduced by `.hasPathEnds_of_retainedRowEnds` to *every retained row of the
candidate has a path end*, and `tracks`.  `WallDatumPathEnds` proves
`HasPathEnds` of the **wall datum** itself (`hasPathEnds_contractDatum`) and
the transport of a wall-datum path end to a path end of the Type III candidate
on the same retained row (`Three.exists_isPathEnd_of_wall_end`).  This module
composes the two into the candidate's `HasPathEnds`, and reads the result at
`OuterWalk.WallData`, so that `tracks` is the only hypothesis left in
`TypeChangeLink`.

## What is proved

* `hasPathEnds_candidate` : **`HasPathEnds` of the outgoing Type III
  candidate**, at an actual valency-three wall of an arbitrary
  `FullDimensionalSourcePresentation`.  The proof is exactly the valency-two
  composition `WallDatumPathEnds.hasPathEnds_candidate`, read at valency three:
  `WallDatumPathEnds.hasPathEnds_contractDatum`'s weak no-return hypothesis
  comes from
  `NonTrivalentValencyThreeRowDictionary.noContractedReturn_of_threeStar`
  (the strong `NoContractedReturn`, unconditional from a `ThreeStar`) weakened
  by `LeafFacetNoReturn.noContractedReturnOffRow_of_noContractedReturn`; a wall
  path end is transported by
  `WallDatumPathEnds.Three.exists_isPathEnd_of_wall_end` and fed to
  `NonTrivalentValencyThreeExit.hasPathEnds_of_retainedRowEnds`.  Unlike
  valency two, no `OrdinaryTrivalent` receipt is needed
  (`hasPathEnds_of_retainedRowEnds` itself takes none at valency three).
* `hasPathEnds_wallData` : the same read at `OuterWalk.WallData`, taking a
  `ThreeStar` of the merged target vertex in place of a `NoContractedReturn`
  hypothesis (paralleling
  `NonTrivalentValencyThreeExit.noContractedReturn_of_valency_three`, which
  needs the same `ThreeStar` and no other receipt).
* `typeChangeLink_of_receipts'` : `NonTrivalentValencyThreeExit.typeChangeLink_of_receipts`
  with `hPathEnds` removed -- an inhabitant of `OuterWalk.TypeChangeLink` at a
  three-valent wall from `src`, `hNoGlue`, `hValid` (the existential output of
  `NonTrivalentValencyThreeExit.exists_anchor_of_wallData`) and `tracks` alone.

## Hypotheses left explicit here

1. `tracks : InteriorGraphTracking.Tracks (wallOutgoingFD ...) (graph.move m)
   label`.  The dart-level dictionary between the candidate's stable graph and
   the Whitehead move of the tracked ambient graph.  Its row half is
   `outLabelling_row_bridge` / `outLabelling_row_retained`; the whole dictionary
   is supplied by `NonTrivalentValencyThreeTracks` together with the star count
   of `NonTrivalentValencyThreeStarCount`.
2. `wallStar : ThirdEquation.ThreeStar (contract wd.coverTarget wd.hab
   wd.hOne) ⟨wd.a, wd.hab⟩`.  A dispatcher choosing the actual wall valency
   (two, three or four) and producing this witness at an actual three-valent
   wall of the outer walk is `OuterWalk.WallData.valency` plus
   `ThirdEquation.ThreeStar.of_card`; it is not built here
   (`NonTrivalentValencyThreeExit.exists_anchor_of_wallData` carries the same
   hypothesis).

No new structure is introduced: `hasPathEnds_candidate`,
`hasPathEnds_wallData` and `typeChangeLink_of_receipts'` are all compositions
of existing declarations, so there is nothing beyond the definitions themselves
to witness for non-vacuity.

## Consumers

`OuterWalk.TypeChangeLink` (hence the `link` hypothesis of
`OuterWalk.coneEntry_of_reaches`) at Part II Case `{v3-nd4}`, with `tracks` the
only remaining receipt.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyThreePathEnds

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.ThirdEquation
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.NonTrivalentValencyThreeAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyThreeCandidate

/-! ## 1.  `HasPathEnds` of the outgoing Type III candidate -/

section Candidate

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
  {wallStar : ThreeStar (contract targetIn hab hOne) ⟨a, hab⟩}
  {anchorBlk : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩}
  (src : ThreeBranchAnchor (contractDatum cover hc hab hOne) wallStar anchorBlk)
  (hNoGlue : DanglingEdgeNoGlue (contractDatum cover hc hab hOne))
  (hValid : (contractDatum cover hc hab hOne).Valid)

include fd hForest coordinates facet hZeroCoord hPosCoord hFacetZero in
/-- **`HasPathEnds` of the outgoing valency-three Type III candidate.**  This
discharges the geometric field `hPathEnds` of
`NonTrivalentValencyThreeExit.outgoingFD` / `.typeChangeLink_of_receipts`, by
composing `WallDatumPathEnds.hasPathEnds_contractDatum` (the wall datum's own
`HasPathEnds`, from the weak no-return condition supplied here by
`NonTrivalentValencyThreeRowDictionary.noContractedReturn_of_threeStar`) with
`WallDatumPathEnds.Three.exists_isPathEnd_of_wall_end` through
`NonTrivalentValencyThreeExit.hasPathEnds_of_retainedRowEnds`. -/
theorem hasPathEnds_candidate :
    HasPathEnds (Prescribed.validCandidate src hNoGlue hValid).datum := by
  classical
  have hEnds : HasPathEnds (contractDatum cover hc hab hOne) :=
    WallDatumPathEnds.hasPathEnds_contractDatum cover fd hc hab hOne hForest coordinates facet
      (LeafFacetNoReturn.noContractedReturnOffRow_of_noContractedReturn cover contracted
        (fd.labelling.row.symm facet)
        (NonTrivalentValencyThreeRowDictionary.noContractedReturn_of_threeStar cover fd hc hab
          hOne wallStar))
      hZeroCoord hPosCoord hFacetZero
  refine NonTrivalentValencyThreeExit.hasPathEnds_of_retainedRowEnds cover hc hab hOne src hNoGlue
    hValid ?_
  intro r
  obtain ⟨g, hg⟩ := Quot.exists_rep r
  have hgr : NonDanglingEdge.stablePath g = r := hg
  obtain ⟨wallEdge, w, hRow, hInc, hNd⟩ := hEnds g
  obtain ⟨first, vertex, hFirst, hEnd⟩ :=
    WallDatumPathEnds.Three.exists_isPathEnd_of_wall_end src hNoGlue hValid hInc hNd
  refine ⟨first, vertex, ?_, hEnd⟩
  rw [hFirst, ← NonTrivalentValencyThreeDescent.retainedRow_mk src hNoGlue hValid wallEdge, hRow,
    hgr]

end

end Candidate

/-! ## 2.  The link at a three-valent wall of the outer walk -/

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
  {wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
  (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)

/-- **The path-ends receipt at the wall data of the outer walk, at a
three-valent wall.**  No `NoContractedReturn` hypothesis is needed:
`NonTrivalentValencyThreeRowDictionary.noContractedReturn_of_threeStar` is
applied internally from `wallStar`, just
as `NonTrivalentValencyThreeExit.noContractedReturn_of_valency_three` does for
the presentation itself. -/
theorem hasPathEnds_wallData :
    HasPathEnds (Prescribed.validCandidate src hNoGlue hValid).datum :=
  hasPathEnds_candidate wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m) wd.coordinates
    (label m.base) wd.hZeroCoord wd.hPosCoord wd.hFacetZero src hNoGlue hValid

/-- **`NonTrivalentValencyThreeExit.typeChangeLink_of_receipts` with the
path-ends hypothesis discharged.**  What remains is exactly `tracks`, the dart
dictionary of the move. -/
def typeChangeLink_of_receipts'
    (tracks : Tracks (NonTrivalentValencyThreeExit.wallOutgoingFD m wd src hNoGlue hValid
      (hasPathEnds_wallData m wd src hNoGlue hValid)) (graph.move m) label) :
    TypeChangeLink m wd :=
  NonTrivalentValencyThreeExit.typeChangeLink_of_receipts m wd src hNoGlue hValid
    (hasPathEnds_wallData m wd src hNoGlue hValid) tracks

end

end Link

end DraismaVargas.LocalCases.NonTrivalentValencyThreePathEnds
