module

public import DraismaVargas.LocalCases.NonTrivalentValencyTwoStarCount
public import DraismaVargas.LocalCases.NonTrivalentValencyTwoTracksLeaf

@[expose] public section

/-!
# The valency-two Base II star count at all three incoming sub-cases

Source: Vargas, Part II (arXiv:2609.09109), §5.1 (a combinatorial type change
is a Whitehead move on the *ambient* tracked graph; the labelling conventions
(1)--(2) at a non-trivalent wall, and `lemma-above-w0`, whose `val u = 1` case
makes the vanishing row a two-occurrence path above a leaf) and §5.4 (case
`{v2-nd4}`, base tree `T_2` = Base II, the Configuration A `2 + 2` subcases and
the Configuration B `3 + 1` subcases), together with Draisma--Vargas Part I:
the stable graph `H(M)` of a gluing datum, the induced row labels of a limit
(§5.2, inherited properties), and `lemma-ndval-of-GqA0`.

`NonTrivalentValencyTwoStarCount` proves the star count at a `2 + 2` two-valent
Base II wall, against the presentation `NonTrivalentValencyTwoExit.wallOutgoingFD`
and under the strong `StablePathFacetContraction.NoContractedReturn`.
`NonTrivalentValencyTwoTracksLeaf` unifies the three incoming sub-cases:
`exists_anchorEnds` produces the `AnchorEnds` pair at **every** two-valent
Base II wall, and `typeChangeLink_of_incidence` turns a single star count
against the no-return-free presentation
`NonTrivalentValencyTwoExitFree.wallOutgoingFD'` into
`OuterWalk.TypeChangeLink`.  This module discharges that single star count, so
the valency-two Base II link follows from (H-II), the wall datum and the
incoming two-valent star alone.

## What is proved

### 1.  The incoming-row map, with no strong no-return hypothesis

`injective_incomingRow`: `NonTrivalentValencyTwoStarCount` reads
`Function.Injective (incomingRow ...)` off the strong `NoContractedReturn`,
which is false at a leaf wall.
`NonTrivalentValencyTwoBaseOneExit.noContractedReturnOffRow_two` supplies the
weakened `LeafFacetNoReturn.NoContractedReturnOffRow` at every two-valent wall
with no sub-case hypothesis, and the chain re-run with the weakened condition
(`WallSplitIncidence.injective_incomingRow_of_noContractedReturnOffRow`) turns
it into the same injectivity.  This is the only place where the no-return
hypothesis of `NonTrivalentValencyTwoStarCount` does work away from the anchor.

### 2.  (T2) at every wall-datum vertex other than the anchor

`incidenceCount_wall_eq_incoming`: the one of `NonTrivalentValencyTwoStarCount`,
with the input above.  Its two other inputs --
`NonTrivalentValencyTwoStarCount.internalEdges_subsingleton_of_ne_anchor` (an
ordinary wall block is unramified) and `wallDatum_trivalent_away_anchor` -- are
generic in the wall block and are reused verbatim, as is (T1),
`NonTrivalentValencyTwoStarCount.incidenceCount_candVertex`.

### 3.  The chart rows of the no-return-free presentation

`outFD'_row_retained`, `outFD'_row_bridge`:
`NonTrivalentValencyTwoStarCount.outFD_row_retained` / `outFD_row_bridge`
restated against `NonTrivalentValencyTwoExitFree.wallOutgoingFD'`, with
`NonTrivalentValencyTwoExit.wallLab_row_val` (available only under the strong
hypothesis) replaced by the abstract `hRowVal` of that presentation.

### 4.  The abstract pair of vanishing ends

* `VanishingEnds`: `NonTrivalentValencyTwoTracksLeaf.AnchorEnds` -- two
  distinct branch vertices over the anchor exhausting the anchor fibre -- plus
  the one extra fact the count needs and `AnchorEnds` does not record, that
  each end actually meets the vanishing row.  `swapEnds` exchanges the two ends.
* `incidenceCount_facetRow_eq_zero`: **the vanishing row meets no branch vertex
  other than the two ends.**  At a `2 + 2` wall this follows from
  `NonTrivalentValencyTwoTracks.eq_facetEdge` (the vanishing row is one
  occurrence), which fails at a leaf wall, where the row is a two-occurrence
  path through a divalent fold.  The argument here is a count valid in all
  three sub-cases: a stable row meets its branch vertices twice in all
  (`NonTrivalentValencyThreeStarCount.sum_incidenceCount_branchVertex`) and the
  two distinct ends already account for both incidences.  The divalent fold is
  not a branch vertex, so it does not enter the sum.

### 5.  (H-II) in one shape for all three sub-cases

* `PrescribedMergedMoveOn`: (H-II) read against a named `VanishingEnds`.  The
  orientation clause of `NonTrivalentValencyTwoTracks.PrescribedMergedMove` and
  of `NonTrivalentValencyTwoTracksLeaf.PrescribedMergedMoveLeaf` names a dart of
  the vanishing row at the `A_u` end; its whole content for the star count is
  the pair of vertex equalities `graph.vert m.base = vtx A_u`,
  `graph.vert (graph.op m.base) = vtx A_v`, and in that form one clause covers a
  `2 + 2` wall (one occurrence, two ends) and a leaf wall (two occurrences, two
  *outer* ends).  The survivor clause is that of `PrescribedMergedMove`
  verbatim and covers Configuration A and Configuration B.
* `PrescribedMergedMoveAny`: **the single name the downstream dispatcher
  consumes.**  It quantifies the two ends internally, so it mentions no
  no-return receipt, no leaf fold and no pair of anchor ends.
  `prescribedMergedMoveAny_of_prescribedMergedMove` and
  `prescribedMergedMoveAny_of_leaf` derive it from the two sub-case
  predicates, `prescribedMergedMoveAny_of_occurrence` from the
  occurrence-level survivor clause, and `prescribedMergedMoveAny_of_rows` from
  the orientation data together with two moved darts carrying the two merged
  rows -- the shape `IncomingPairing.exists_movedStar_darts` produces, at which
  separation is automatic (`IncomingPairing.vertex_of_movedStar_eq_pair`); and
  `prescribedMergedMoveOn_of_any` orients an arbitrary pair of ends against it
  (the two vertices it names are branch vertices meeting the vanishing row,
  hence the two ends in one of the two orders; they are distinct because
  `m.base` is a non-loop dart).

### 6--7.  The count

* `natCard_moved_of_ne`, `incidence_inl_retained`, `incidence_inl_bridge`: away
  from the anchor, the (T1)-then-(T2)-then-tracking composite of
  `NonTrivalentValencyTwoStarCount`, with the bridge row handled by §4's
  counting lemma.
* `vertexEquiv_anchor_false` / `_true`, `label_dart_merged_iff`,
  `incidence_inr_false_retained`, `incidence_inr_false_bridge`: **at `A_u`.**
  The exact star `{h_1, e_first, e_second}`
  (`NonTrivalentValencyTwoStarCount.incidentEdges_endpointVertex_false`, generic
  in the sub-case) is matched dart by dart with the moved star (H-II)
  prescribes.  At a leaf wall the occurrence of the vanishing row that `A_u`
  sees is the *outer* one, the fold's two occurrences being one row; that is
  exactly what the orientation clause of `PrescribedMergedMoveOn` records.
* `incidence_inr_true`: **at `A_v`, from the leftover equation** -- as in
  `NonTrivalentValencyTwoStarCount`, against `wallOutgoingFD'`.
* `incidence_of_prescribedMergedMove`: the star count at every branch vertex and
  every row, at **any** two-valent Base II wall.
* `typeChangeLink_of_prescribedMergedMove_two`: `OuterWalk.TypeChangeLink` from
  (H-II) at any two-valent Base II wall, through
  `NonTrivalentValencyTwoTracksLeaf.typeChangeLink_of_incidence`.

### 8.  Producers and the headline

* `vanishingEnds_of_leafFold`, `vanishingEnds_of_noContractedReturn`,
  `nonempty_vanishingEnds`: the non-vacuity witnesses of `VanishingEnds`, at a
  leaf wall, at a `2 + 2` wall, and unconditionally at every two-valent Base II
  wall (the trichotomy of `NonTrivalentValencyTwoTracksLeaf`, carrying the two
  extra incidence facts).
* `prescribedMergedMoveAny_prescribedMove`,
  `prescribedMergedMoveAny_prescribedMove_leaf`: non-vacuity of (H-II) in
  relative form, from the `prescribedMove` of `NonTrivalentValencyTwoTracks`
  and of `NonTrivalentValencyTwoTracksLeaf`.
* `nonempty_typeChangeLink_of_prescribedMergedMoveAny`, and its two sub-case
  corollaries `nonempty_typeChangeLink_of_prescribedMergedMove` and
  `nonempty_typeChangeLink_of_prescribedMergedMoveLeaf`.
* `exists_typeChangeLink_of_prescribedMergedMove_of_wallData`: **the headline.**
  `NonTrivalentValencyTwoTracksLeaf.exists_typeChangeLink_of_incidence_of_wallData`
  with its star-count input replaced by (H-II): from `wd` and the incoming
  `W2R1Target.TwoStar` alone it produces the anchor block, and for *every*
  `sel` the outgoing `FullDimensionalSourcePresentation` on the incoming chart,
  the common minor `AgreeOffColumn` that `TypeChangeLink.agree` asks for, and
  the link as soon as `PrescribedMergedMoveAny` is supplied.

## What is not proved -- the explicit hypotheses

1. `PrescribedMergedMoveAny m wd sel`, i.e. (H-II): the Whitehead move `m` is
   oriented along the vanishing row and places with `m.base` exactly two darts
   carrying the stable **rows** of the two survivors `sel` merges (row level,
   not occurrence level -- see the note on `PrescribedMergedMoveOn`).  Its
   relative witnesses are `prescribedMergedMoveAny_prescribedMove(_leaf)`; the
   geometric input of those is `NonTrivalentValencyTwoTracks.MergedSeparated` /
   `NonTrivalentValencyTwoTracksLeaf.MergedSeparatedLeaf`, which are named
   hypotheses there and are **not** derived here.
2. `wallStar : W2R1Target.TwoStar (contract wd.coverTarget ...) ⟨wd.a, wd.hab⟩`,
   the incoming two-valent star at the contracted wall.  The valency dispatcher
   of `OuterWalk.WallData.valency` -- which decides valency 4 / 3 / 2 and, at
   valency two, Base I versus Base II -- is not built here.
3. Nothing else.  The headline discharges `anchorBlock`, `src`, `sel`'s
   `OrdinaryTrivalent`, the inputs `labelling₀` / `hRowVal` / `hMatrixWall` of
   the no-return-free presentation, `HasPathEnds` and the whole incoming
   `2 + 2` / `1 + 3` / `3 + 1` trichotomy internally, and no no-return receipt of
   any kind appears in any statement of this module except in the two sub-case
   adapters that consume `NonTrivalentValencyTwoTracks.PrescribedMergedMove`.

`VanishingEnds` is the one structure introduced; `vanishingEnds_of_leafFold`,
`vanishingEnds_of_noContractedReturn` and `nonempty_vanishingEnds` inhabit it,
the last unconditionally at every two-valent Base II wall.  The `Prop`
definitions `PrescribedMergedMoveOn` and `PrescribedMergedMoveAny` come with
`prescribedMergedMoveOn_of_any` and the two relative witnesses.

## Consumers

`OuterWalk.TypeChangeLink` at Part II case `{v2-nd4}`, Base II, in **all three**
incoming sub-cases, hence `OuterWalk.coneEntry_of_reaches` and the type-change
link `NonTrivalentValencyTwoBaseOneLink.link_all` that the outer walk consumes,
once the valency dispatcher supplies `wallStar` and the walk supplies (H-II).
`NonTrivalentValencyTwoStarCount.typeChangeLink_of_prescribedMergedMove` is the
`2 + 2`-only form against `NonTrivalentValencyTwoExit.wallOutgoingFD`; the
headline here covers all three sub-cases.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoStarCountAll

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
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRowEquiv
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk

noncomputable section

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)

/-! ## 1.  The incoming-row map is injective at every two-valent wall -/

/-- **The incoming-row map is injective at every two-valent wall.**
`NonTrivalentValencyTwoStarCount` reads this off the strong
`StablePathFacetContraction.NoContractedReturn`, which is false at a leaf wall;
`NonTrivalentValencyTwoBaseOneExit.noContractedReturnOffRow_two` supplies the
weakened condition of `LeafFacetNoReturn` with no sub-case hypothesis, and the
chain of `StablePathFacetContraction`, re-run with that condition, turns it
into the same injectivity. -/
theorem injective_incomingRow
    (wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    Function.Injective (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
      (wd.hCompat m) (wd.hForest m)) :=
  WallSplitIncidence.injective_incomingRow_of_noContractedReturnOffRow wd.cover wd.fullDim
    wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m) wd.coordinates (label m.base)
    wd.hZeroCoord wd.hPosCoord wd.hFacetZero
    (NonTrivalentValencyTwoBaseOneExit.noContractedReturnOffRow_two wd.cover wd.fullDim wd.hc
      wd.hab wd.hOne wd.coordinates (label m.base) wd.hZeroCoord wd.hPosCoord wd.hFacetZero
      wallStar)

section Wall

variable {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hOrd : OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk)

/-! ## 2.  (T2) at every wall-datum vertex other than the anchor -/

include src hOrd in
/-- **(T2), at every wall-datum vertex other than the anchor**, with no
no-return hypothesis: `NonTrivalentValencyTwoStarCount.incidenceCount_wall_eq_incoming`
with its `injective_incomingRow` input taken from the weakened condition
instead. -/
theorem incidenceCount_wall_eq_incoming
    (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hne : w ≠ NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk)
    (u : wd.cover.SourceVertex)
    (hMapU : sourceVertexMap wd.cover wd.hc wd.hab wd.hOne u = w)
    (hThreeU : 3 ≤ nonDanglingValency wd.cover u)
    (row : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (contractDatum wd.cover wd.hc wd.hab wd.hOne) w row =
      incidenceCount wd.cover u (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
        (wd.hCompat m) (wd.hForest m) row) :=
  WallSplitIncidenceOrdinary.incidenceCount_unramified wd.cover wd.fullDim wd.hc wd.hab wd.hOne
    (wd.hCompat m) (wd.hForest m) (injective_incomingRow m wd wallStar) wd.fullDim.connected
    w u hMapU hThreeU
    (NonTrivalentValencyTwoTracks.wallDatum_trivalent_away_anchor m wd hOrd w hne)
    wd.fullDim.trivalent
    (NonTrivalentValencyTwoStarCount.internalEdges_subsingleton_of_ne_anchor m wd src w hne) row

/-! ## 3.  The chart rows of the no-return-free outgoing presentation -/

variable (labelling₀ : StableLengthMatrixLabelling (contractDatum wd.cover wd.hc wd.hab wd.hOne)
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

/-- **A retained row of `wallOutgoingFD'` keeps the chart coordinate of its own
incoming row.**  `NonTrivalentValencyTwoStarCount.outFD_row_retained` against
`NonTrivalentValencyTwoExitFree.wallOutgoingFD'`: `wallLab_row_val` is replaced
by the abstract `hRowVal`. -/
theorem outFD'_row_retained (p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    (NonTrivalentValencyTwoExitFree.wallOutgoingFD' m wd src sel hOrd labelling₀ hRowVal
        hMatrixWall).labelling.row
      (NonTrivalentValencyTwoDescent.retainedRow src sel
        (NonTrivalentValencyTwoTracks.wallValid m wd) p) =
      wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
        (wd.hCompat m) (wd.hForest m) p) := by
  show (NonTrivalentValencyTwoExit.rowChart wd.cover wd.fullDim (label m.base)
      (contracted := wd.contracted))
      ((NonTrivalentValencyTwoRowEquiv.labelling src sel
        (NonTrivalentValencyTwoTracks.wallValid m wd) hOrd labelling₀).row
        (NonTrivalentValencyTwoDescent.retainedRow src sel
          (NonTrivalentValencyTwoTracks.wallValid m wd) p)) = _
  rw [NonTrivalentValencyTwoRowEquiv.labelling_row_retained src sel
      (NonTrivalentValencyTwoTracks.wallValid m wd) hOrd _ p,
    NonTrivalentValencyTwoExit.rowChart_some, hRowVal p,
    Equiv.swap_comm (label m.base) (wd.fullDim.labelling.targetEdge.symm wd.contracted)]
  exact Equiv.swap_apply_self _ _ _

/-- **The bridge row of `wallOutgoingFD'` occupies the vanishing chart row.** -/
theorem outFD'_row_bridge :
    (NonTrivalentValencyTwoExitFree.wallOutgoingFD' m wd src sel hOrd labelling₀ hRowVal
        hMatrixWall).labelling.row
      (NonTrivalentValencyTwoRowEquiv.bridgeRow src sel
        (NonTrivalentValencyTwoTracks.wallValid m wd)) = label m.base := by
  show (NonTrivalentValencyTwoExit.rowChart wd.cover wd.fullDim (label m.base)
      (contracted := wd.contracted))
      ((NonTrivalentValencyTwoRowEquiv.labelling src sel
        (NonTrivalentValencyTwoTracks.wallValid m wd) hOrd labelling₀).row
        (NonTrivalentValencyTwoRowEquiv.bridgeRow src sel
          (NonTrivalentValencyTwoTracks.wallValid m wd))) = label m.base
  rw [NonTrivalentValencyTwoRowEquiv.labelling_row_bridge src sel
    (NonTrivalentValencyTwoTracks.wallValid m wd) hOrd _]
  rfl

end Wall

/-! ## 4.  The abstract pair of anchor ends -/

section Ends

variable {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}

/-- **The abstract pair of anchor ends of a two-valent Base II wall.**
`NonTrivalentValencyTwoTracksLeaf.AnchorEnds` -- two distinct branch vertices of
the incoming cover, both over the anchor, exhausting the anchor fibre's branch
vertices -- together with the one extra fact the star count needs and
`AnchorEnds` does not record: each of the two ends actually meets the vanishing
row. At a `2 + 2` wall the pair is the two ends of the single vanishing
occurrence; at a `1 + 3` or `3 + 1` wall it is the two *outer* ends of the
two-occurrence vanishing path. Both are produced in §8. -/
structure VanishingEnds
    (anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) where
  /-- the `A_u` end -/
  left : wd.cover.SourceVertex
  /-- the `A_v` end -/
  right : wd.cover.SourceVertex
  /-- the six facts of `NonTrivalentValencyTwoTracksLeaf.AnchorEnds` about the pair -/
  ends : NonTrivalentValencyTwoTracksLeaf.AnchorEnds m wd anchorBlk left right
  /-- the vanishing row reaches the `A_u` end -/
  leftMeets : 0 < incidenceCount wd.cover left (NonTrivalentValencyTwoTracks.facetRow m wd)
  /-- the vanishing row reaches the `A_v` end -/
  rightMeets : 0 < incidenceCount wd.cover right (NonTrivalentValencyTwoTracks.facetRow m wd)

variable {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}

/-- The pair with its two ends exchanged: `AnchorEnds` is symmetric. -/
def swapEnds (E : VanishingEnds m wd anchorBlk) : VanishingEnds m wd anchorBlk where
  left := E.right
  right := E.left
  ends := ⟨E.ends.1.symm, E.ends.2.2.1, E.ends.2.1, E.ends.2.2.2.2.1, E.ends.2.2.2.1,
    fun u hu h3 ↦ (E.ends.2.2.2.2.2 u hu h3).symm⟩
  leftMeets := E.rightMeets
  rightMeets := E.leftMeets

/-- **The vanishing row meets no branch vertex other than the two ends.**  Every
stable row of the incoming cover meets its branch vertices twice in all
(`sum_incidenceCount_branchVertex`), and the two distinct ends already account
for both incidences. At a `2 + 2` wall this is the `eq_facetEdge` argument of
`NonTrivalentValencyTwoTracks`; at a leaf wall the vanishing row has two
occurrences and a divalent fold between them, and the counting argument covers
both. -/
theorem incidenceCount_facetRow_eq_zero (E : VanishingEnds m wd anchorBlk)
    (u : BranchVertex wd.cover) (hl : u.1 ≠ E.left) (hr : u.1 ≠ E.right) :
    incidenceCount wd.cover u.1 (NonTrivalentValencyTwoTracks.facetRow m wd) = 0 := by
  classical
  have hSum := NonTrivalentValencyThreeStarCount.sum_incidenceCount_branchVertex wd.cover
    wd.fullDim.connected wd.fullDim.pathEnds (NonTrivalentValencyTwoTracks.facetRow m wd)
  set L : BranchVertex wd.cover := ⟨E.left, E.ends.2.1⟩ with hLdef
  set R : BranchVertex wd.cover := ⟨E.right, E.ends.2.2.1⟩ with hRdef
  have hLR : L ≠ R := fun h ↦ E.ends.1 (congrArg Subtype.val h)
  have hUL : u ≠ L := fun h ↦ hl (congrArg Subtype.val h)
  have hUR : u ≠ R := fun h ↦ hr (congrArg Subtype.val h)
  have hLe : ∑ w ∈ ({L, R, u} : Finset (BranchVertex wd.cover)),
      incidenceCount wd.cover w.1 (NonTrivalentValencyTwoTracks.facetRow m wd) ≤
      ∑ w : BranchVertex wd.cover,
        incidenceCount wd.cover w.1 (NonTrivalentValencyTwoTracks.facetRow m wd) :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [show ({L, R, u} : Finset (BranchVertex wd.cover)) = insert L {R, u} from rfl,
    Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact not_or.mpr ⟨hLR, fun h ↦ hUL h.symm⟩),
    Finset.sum_pair (fun h ↦ hUR h.symm)] at hLe
  have hLpos : 0 < incidenceCount wd.cover L.1
      (NonTrivalentValencyTwoTracks.facetRow m wd) := E.leftMeets
  have hRpos : 0 < incidenceCount wd.cover R.1
      (NonTrivalentValencyTwoTracks.facetRow m wd) := E.rightMeets
  omega

end Ends

/-! ## 5.  (H-II) in the dispatcher's shape -/

section Prescribed

variable {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)

/-- **(H-II) read against a named pair of anchor ends.**  The orientation clause
of `NonTrivalentValencyTwoTracks.PrescribedMergedMove` and of
`NonTrivalentValencyTwoTracksLeaf.PrescribedMergedMoveLeaf` says that the dart
`m.base` is the dart of the vanishing row at the `A_u` end; its whole content
for the star count is the pair of vertex equalities below, and in that form one
clause covers all three incoming sub-cases.  The survivor clause is that of
`PrescribedMergedMove` verbatim: the moved star of `graph.vert m.base` with
`m.base` removed is a pair of darts carrying the two stable **rows** of the
survivors `sel` merges.  It is at row level (`d.2.1.stablePath = ...`) because
that is what the count consumes (`IncomingPairing.label_dart_of_row`) and
because a merged survivor may reach its end of the vanishing row through a
pass-through occurrence over the contracted target edge. -/
def PrescribedMergedMoveOn (E : VanishingEnds m wd anchorBlk) : Prop :=
  graph.vert m.base =
      wd.tracks.iso.vtx (NonTrivalentValencyTwoTracksLeaf.leftBranch m wd E.ends) ∧
    graph.vert (graph.op m.base) =
        wd.tracks.iso.vtx (NonTrivalentValencyTwoTracksLeaf.rightBranch m wd E.ends) ∧
      ∃ first second : StableSourceDarts.Dart wd.cover,
        first.2.1.stablePath =
            (NonTrivalentValencyTwoTracks.selectedLift m wd sel false).stablePath ∧
          second.2.1.stablePath =
              (NonTrivalentValencyTwoTracks.selectedLift m wd sel true).stablePath ∧
            (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
              {wd.tracks.iso.dart first, wd.tracks.iso.dart second}

/-- **(H-II) at any two-valent Base II wall -- the single name the dispatcher
consumes.** It mentions neither a no-return receipt, nor a leaf fold, nor a pair
of anchor ends: the ends of the vanishing row are quantified inside. At a
`2 + 2` wall it is implied by
`NonTrivalentValencyTwoTracks.PrescribedMergedMove` and at a leaf wall by
`NonTrivalentValencyTwoTracksLeaf.PrescribedMergedMoveLeaf` (§8), so both
sub-case predicates feed the same headline. -/
def PrescribedMergedMoveAny : Prop :=
  (∃ u v : BranchVertex wd.cover,
      0 < incidenceCount wd.cover u.1 (NonTrivalentValencyTwoTracks.facetRow m wd) ∧
        0 < incidenceCount wd.cover v.1 (NonTrivalentValencyTwoTracks.facetRow m wd) ∧
          graph.vert m.base = wd.tracks.iso.vtx u ∧
            graph.vert (graph.op m.base) = wd.tracks.iso.vtx v) ∧
    ∃ first second : StableSourceDarts.Dart wd.cover,
      first.2.1.stablePath =
          (NonTrivalentValencyTwoTracks.selectedLift m wd sel false).stablePath ∧
        second.2.1.stablePath =
            (NonTrivalentValencyTwoTracks.selectedLift m wd sel true).stablePath ∧
          (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
            {wd.tracks.iso.dart first, wd.tracks.iso.dart second}

/-- **The occurrence-level clause implies the dispatcher's (H-II).**  The
occurrence-level form of the survivor clause is strictly stronger; the converse
fails at every Configuration B incoming and at the split incomings of
Configuration A, where a merged survivor reaches its end of the vanishing row
through a pass-through occurrence over the contracted target edge. -/
theorem prescribedMergedMoveAny_of_occurrence
    (hEnds : ∃ u v : BranchVertex wd.cover,
      0 < incidenceCount wd.cover u.1 (NonTrivalentValencyTwoTracks.facetRow m wd) ∧
        0 < incidenceCount wd.cover v.1 (NonTrivalentValencyTwoTracks.facetRow m wd) ∧
          graph.vert m.base = wd.tracks.iso.vtx u ∧
            graph.vert (graph.op m.base) = wd.tracks.iso.vtx v)
    (first second : StableSourceDarts.Dart wd.cover)
    (hFirst : first.2.1 = NonTrivalentValencyTwoTracks.selectedLift m wd sel false)
    (hSecond : second.2.1 = NonTrivalentValencyTwoTracks.selectedLift m wd sel true)
    (hStar : (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
      {wd.tracks.iso.dart first, wd.tracks.iso.dart second}) :
    PrescribedMergedMoveAny m wd sel :=
  ⟨hEnds, first, second, by rw [hFirst], by rw [hSecond], hStar⟩

/-- **The dispatcher's (H-II) from the orientation clause and two moved darts
carrying the two merged rows.**  This is the shape the valency dispatcher
consumes: the two darts come from `IncomingPairing.exists_movedStar_darts`,
which also places one at each end of the vanishing row, so no separation
hypothesis is needed here; the orientation data `hEnds` is what
`prescribedMergedMoveAny_of_prescribedMergedMove` and
`prescribedMergedMoveAny_of_leaf` build from the two sub-case orientation
clauses.  For the other order of the pair, apply it to `y`, `x` after
`Finset.pair_comm`. -/
theorem prescribedMergedMoveAny_of_rows
    (hEnds : ∃ u v : BranchVertex wd.cover,
      0 < incidenceCount wd.cover u.1 (NonTrivalentValencyTwoTracks.facetRow m wd) ∧
        0 < incidenceCount wd.cover v.1 (NonTrivalentValencyTwoTracks.facetRow m wd) ∧
          graph.vert m.base = wd.tracks.iso.vtx u ∧
            graph.vert (graph.op m.base) = wd.tracks.iso.vtx v)
    (x y : StableSourceDarts.Dart wd.cover)
    (hx : x.2.1.stablePath =
      (NonTrivalentValencyTwoTracks.selectedLift m wd sel false).stablePath)
    (hy : y.2.1.stablePath =
      (NonTrivalentValencyTwoTracks.selectedLift m wd sel true).stablePath)
    (hStar : (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
      {wd.tracks.iso.dart x, wd.tracks.iso.dart y}) :
    PrescribedMergedMoveAny m wd sel :=
  ⟨hEnds, x, y, hx, hy, hStar⟩

/-- **(H-II) orients any pair of anchor ends.**  The two vertices it names are
branch vertices meeting the vanishing row, hence are the two ends in one of the
two orders; `graph.vert m.base ≠ graph.vert (graph.op m.base)` because the
Whitehead move is at a non-loop dart. -/
theorem prescribedMergedMoveOn_of_any (E : VanishingEnds m wd anchorBlk)
    (h : PrescribedMergedMoveAny m wd sel) :
    PrescribedMergedMoveOn m wd sel E ∨ PrescribedMergedMoveOn m wd sel (swapEnds m wd E) := by
  classical
  obtain ⟨⟨u, v, hu, hv, hbu, hbv⟩, hSurv⟩ := h
  have hne : u ≠ v := by
    intro hBad
    refine m.nonloop ?_
    show graph.vert (graph.op m.base) = graph.vert m.base
    rw [hbv, hbu, hBad]
  have hu' : u.1 = E.left ∨ u.1 = E.right := by
    by_contra hc
    obtain ⟨h1, h2⟩ := not_or.mp hc
    rw [incidenceCount_facetRow_eq_zero m wd E u h1 h2] at hu
    omega
  have hv' : v.1 = E.left ∨ v.1 = E.right := by
    by_contra hc
    obtain ⟨h1, h2⟩ := not_or.mp hc
    rw [incidenceCount_facetRow_eq_zero m wd E v h1 h2] at hv
    omega
  rcases hu' with hul | hur
  · rcases hv' with hvl | hvr
    · exact absurd (Subtype.ext (hul.trans hvl.symm) : u = v) hne
    · refine Or.inl ⟨?_, ?_, hSurv⟩
      · rw [hbu]
        exact congrArg wd.tracks.iso.vtx (Subtype.ext hul)
      · rw [hbv]
        exact congrArg wd.tracks.iso.vtx (Subtype.ext hvr)
  · rcases hv' with hvl | hvr
    · refine Or.inr ⟨?_, ?_, hSurv⟩
      · rw [hbu]
        exact congrArg wd.tracks.iso.vtx (Subtype.ext hur)
      · rw [hbv]
        exact congrArg wd.tracks.iso.vtx (Subtype.ext hvl)
    · exact absurd (Subtype.ext (hur.trans hvr.symm) : u = v) hne

end Prescribed

/-! ## 6.  Away from the anchor -/

section Away

variable {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hOrd : OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk)
  (labelling₀ : StableLengthMatrixLabelling (contractDatum wd.cover wd.hc wd.hab wd.hOne)
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

/-- **Away from the two ends of the vanishing row the moved star of a chart row
is the star of the incoming cover.**  `NonTrivalentValencyTwoStarCount.natCard_moved_of_ne`,
with the two vertex equalities of (H-II) in place of the `2 + 2` orientation
clause. -/
theorem natCard_moved_of_ne (E : VanishingEnds m wd anchorBlk)
    (hBase : graph.vert m.base =
      wd.tracks.iso.vtx (NonTrivalentValencyTwoTracksLeaf.leftBranch m wd E.ends))
    (hOpBase : graph.vert (graph.op m.base) =
      wd.tracks.iso.vtx (NonTrivalentValencyTwoTracksLeaf.rightBranch m wd E.ends))
    (u : BranchVertex wd.cover) (hul : u.1 ≠ E.left) (hur : u.1 ≠ E.right)
    (row : StablePath wd.cover) :
    Nat.card {d : D // graph.vert (m.perm d) = wd.tracks.iso.vtx u ∧
        label d = wd.fullDim.labelling.row row} =
      incidenceCount wd.cover u.1 row := by
  have hNeBase : wd.tracks.iso.vtx u ≠ graph.vert m.base := by
    rw [hBase]
    intro hBad
    exact hul (congrArg Subtype.val (wd.tracks.iso.vtx.injective hBad))
  have hNeOp : wd.tracks.iso.vtx u ≠ graph.vert (graph.op m.base) := by
    rw [hOpBase]
    intro hBad
    exact hur (congrArg Subtype.val (wd.tracks.iso.vtx.injective hBad))
  rw [NonTrivalentValencyTwoTracks.card_star_eq_incidenceCount m wd u row]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun d ↦ and_congr_left'
    (NonTrivalentValencyTwoTracks.move_vert_eq_iff_of_ne m hNeBase hNeOp d))

include hOrd in
/-- **The star count at a branch vertex away from the anchor, on a retained
row.**  `NonTrivalentValencyTwoStarCount.incidence_inl_retained` against
`NonTrivalentValencyTwoExitFree.wallOutgoingFD'`: (T1), then (T2), then the
incoming tracking. -/
theorem incidence_inl_retained (E : VanishingEnds m wd anchorBlk)
    (hPres : PrescribedMergedMoveOn m wd sel E)
    (w : {w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
      w.1 ≠ NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk})
    (r₀ : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (Prescribed.validCandidate sel).datum
        (NonTrivalentValencyTwoTracks.candBranchMap m wd src sel hOrd (Sum.inl w)).1
        (NonTrivalentValencyTwoDescent.retainedRow src sel
          (NonTrivalentValencyTwoTracks.wallValid m wd) r₀) =
      Nat.card {d : D // graph.vert (m.perm d) =
          NonTrivalentValencyTwoTracksLeaf.vertexEquiv m wd src sel hOrd E.ends
            (NonTrivalentValencyTwoTracks.candBranchMap m wd src sel hOrd (Sum.inl w)) ∧
        label d = (NonTrivalentValencyTwoExitFree.wallOutgoingFD' m wd src sel hOrd labelling₀
            hRowVal hMatrixWall).labelling.row
          (NonTrivalentValencyTwoDescent.retainedRow src sel
            (NonTrivalentValencyTwoTracks.wallValid m wd) r₀)} := by
  classical
  set j := (NonTrivalentValencyTwoTracksLeaf.branchEquivAnchorComplement m wd hOrd E.ends).symm w
    with hj
  have hMapU : sourceVertexMap wd.cover wd.hc wd.hab wd.hOne j.1.1 = w.1.1 := by
    have h := NonTrivalentValencyTwoTracksLeaf.branchEquivAnchorComplement_apply m wd hOrd
      E.ends j
    rw [hj, Equiv.apply_symm_apply] at h
    exact h.symm
  rw [NonTrivalentValencyTwoTracksLeaf.vertexEquiv_inl m wd src sel hOrd E.ends w,
    outFD'_row_retained m wd src sel hOrd labelling₀ hRowVal hMatrixWall r₀,
    natCard_moved_of_ne m wd E hPres.1 hPres.2.1 j.1 j.2.1 j.2.2]
  refine Eq.trans ?_ (incidenceCount_wall_eq_incoming m wd src hOrd w.1.1 w.2 j.1.1 hMapU
    j.1.2 r₀)
  exact (NonTrivalentValencyTwoStarCount.incidenceCount_candVertex m wd src sel hOrd w.1.1 w.2
    r₀).symm

include hOrd in
/-- **The star count at a branch vertex away from the anchor, on the bridge
row.**  Both sides vanish: downstairs the bridge occurrence joins `A_u` to
`A_v`, upstairs the vanishing chart row reaches only the two ends. -/
theorem incidence_inl_bridge (E : VanishingEnds m wd anchorBlk)
    (hPres : PrescribedMergedMoveOn m wd sel E)
    (w : {w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
      w.1 ≠ NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk}) :
    incidenceCount (Prescribed.validCandidate sel).datum
        (NonTrivalentValencyTwoTracks.candBranchMap m wd src sel hOrd (Sum.inl w)).1
        (NonTrivalentValencyTwoRowEquiv.bridgeRow src sel
          (NonTrivalentValencyTwoTracks.wallValid m wd)) =
      Nat.card {d : D // graph.vert (m.perm d) =
          NonTrivalentValencyTwoTracksLeaf.vertexEquiv m wd src sel hOrd E.ends
            (NonTrivalentValencyTwoTracks.candBranchMap m wd src sel hOrd (Sum.inl w)) ∧
        label d = (NonTrivalentValencyTwoExitFree.wallOutgoingFD' m wd src sel hOrd labelling₀
            hRowVal hMatrixWall).labelling.row
          (NonTrivalentValencyTwoRowEquiv.bridgeRow src sel
            (NonTrivalentValencyTwoTracks.wallValid m wd))} := by
  classical
  set j := (NonTrivalentValencyTwoTracksLeaf.branchEquivAnchorComplement m wd hOrd E.ends).symm w
    with hj
  rw [NonTrivalentValencyTwoStarCount.incidenceCount_bridgeRow_inl_eq_zero m wd src sel hOrd w]
  symm
  rw [NonTrivalentValencyTwoTracksLeaf.vertexEquiv_inl m wd src sel hOrd E.ends w,
    outFD'_row_bridge m wd src sel hOrd labelling₀ hRowVal hMatrixWall]
  have h := natCard_moved_of_ne m wd E hPres.1 hPres.2.1 j.1 j.2.1 j.2.2
    (NonTrivalentValencyTwoTracks.facetRow m wd)
  rw [show wd.fullDim.labelling.row (NonTrivalentValencyTwoTracks.facetRow m wd) = label m.base
    from Equiv.apply_symm_apply _ _] at h
  exact h.trans (incidenceCount_facetRow_eq_zero m wd E j.1 j.2.1 j.2.2)

end Away

/-! ## 7.  At the two anchor ends, and the star count -/

section Anchor

variable {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hOrd : OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk)

/-- The chart label of the dart of a merged survivor determines its incoming
row: `NonTrivalentValencyTwoStarCount.label_dart_merged_iff` with the
injectivity of the incoming-row map taken from the weakened no-return
condition. -/
theorem label_dart_merged_iff (d : StableSourceDarts.Dart wd.cover) (side : Bool)
    (hd : d.2.1.stablePath =
      (NonTrivalentValencyTwoTracks.selectedLift m wd sel side).stablePath)
    (r₀ : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    (label (wd.tracks.iso.dart d) = wd.fullDim.labelling.row
        (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m)
          (wd.hForest m) r₀)) ↔
      (NonTrivalentValencyTwoStarCount.mergedWall m wd sel side).stablePath = r₀ := by
  rw [NonTrivalentValencyTwoStarCount.label_dart_merged m wd sel d side hd]
  constructor
  · intro h
    exact injective_incomingRow m wd wallStar (wd.fullDim.labelling.row.injective h)
  · intro h
    exact congrArg _ (congrArg _ h)

variable (labelling₀ : StableLengthMatrixLabelling (contractDatum wd.cover wd.hc wd.hab wd.hOne)
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

/-- **`A_u` goes to `graph.vert m.base`.** -/
theorem vertexEquiv_anchor_false (E : VanishingEnds m wd anchorBlk)
    (hBase : graph.vert m.base =
      wd.tracks.iso.vtx (NonTrivalentValencyTwoTracksLeaf.leftBranch m wd E.ends)) :
    NonTrivalentValencyTwoTracksLeaf.vertexEquiv m wd src sel hOrd E.ends
        (NonTrivalentValencyTwoTracks.candBranchMap m wd src sel hOrd (Sum.inr false)) =
      graph.vert m.base := by
  rw [NonTrivalentValencyTwoTracksLeaf.vertexEquiv_anchor m wd src sel hOrd E.ends false, hBase]
  rfl

/-- **`A_v` goes to `graph.vert (graph.op m.base)`.** -/
theorem vertexEquiv_anchor_true (E : VanishingEnds m wd anchorBlk)
    (hOpBase : graph.vert (graph.op m.base) =
      wd.tracks.iso.vtx (NonTrivalentValencyTwoTracksLeaf.rightBranch m wd E.ends)) :
    NonTrivalentValencyTwoTracksLeaf.vertexEquiv m wd src sel hOrd E.ends
        (NonTrivalentValencyTwoTracks.candBranchMap m wd src sel hOrd (Sum.inr true)) =
      graph.vert (graph.op m.base) := by
  rw [NonTrivalentValencyTwoTracksLeaf.vertexEquiv_anchor m wd src sel hOrd E.ends true, hOpBase]
  rfl

include hOrd in
/-- **The star count at `A_u`, on a retained row.**  The exact star
`{h_1, e_first, e_second}` at `A_u` is matched dart by dart with the star (H-II)
prescribes: `m.base` carries the vanishing chart row, and the two remaining
darts carry the incoming rows of the two merged survivors.  This is
`NonTrivalentValencyTwoStarCount.incidence_inr_false_retained` with the `2 + 2`
orientation clause replaced by the dispatcher's, and with
`NonTrivalentValencyTwoExitFree.wallOutgoingFD'` in place of
`NonTrivalentValencyTwoExit.wallOutgoingFD` -- the leaf sub-cases included,
where the vanishing row contributes the *outer* occurrence at each end. -/
theorem incidence_inr_false_retained (E : VanishingEnds m wd anchorBlk)
    (hPres : PrescribedMergedMoveOn m wd sel E)
    (r₀ : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (Prescribed.validCandidate sel).datum
        (NonTrivalentValencyTwoTracks.candBranchMap m wd src sel hOrd (Sum.inr false)).1
        (NonTrivalentValencyTwoDescent.retainedRow src sel
          (NonTrivalentValencyTwoTracks.wallValid m wd) r₀) =
      Nat.card {d : D // graph.vert (m.perm d) =
          NonTrivalentValencyTwoTracksLeaf.vertexEquiv m wd src sel hOrd E.ends
            (NonTrivalentValencyTwoTracks.candBranchMap m wd src sel hOrd (Sum.inr false)) ∧
        label d = (NonTrivalentValencyTwoExitFree.wallOutgoingFD' m wd src sel hOrd labelling₀
            hRowVal hMatrixWall).labelling.row
          (NonTrivalentValencyTwoDescent.retainedRow src sel
            (NonTrivalentValencyTwoTracks.wallValid m wd) r₀)} := by
  classical
  obtain ⟨hBase, hOpBase, first, second, hFirst, hSecond, hStar⟩ := hPres
  rw [vertexEquiv_anchor_false m wd src sel hOrd E hBase,
    outFD'_row_retained m wd src sel hOrd labelling₀ hRowVal hMatrixWall r₀]
  have hRHS : Nat.card {d : D // graph.vert (m.perm d) = graph.vert m.base ∧
      label d = wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
        (wd.hCompat m) (wd.hForest m) r₀)} =
      ((Finset.univ.filter fun d : D ↦ graph.vert (m.perm d) = graph.vert m.base).filter
        fun d ↦ label d = wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab
          wd.hOne (wd.hCompat m) (wd.hForest m) r₀)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter]
  have hBridgeRow : ¬ ((NonTrivalentValencyTwoStarCount.bridgeND m wd src sel).stablePath =
      NonTrivalentValencyTwoDescent.retainedRow src sel
        (NonTrivalentValencyTwoTracks.wallValid m wd) r₀) := by
    rw [NonTrivalentValencyTwoStarCount.stablePath_bridgeND m wd src sel]
    exact fun h ↦ NonTrivalentValencyTwoStarCount.retainedRow_ne_bridgeRow src sel
      (NonTrivalentValencyTwoTracks.wallValid m wd) hOrd r₀ h.symm
  rw [hRHS, NonTrivalentValencyThreeStarCount.filter_moved_base m wd first second hStar,
    Finset.filter_insert,
    ite_eq_right (Ne.symm (NonTrivalentValencyThreeStarCount.labelling_row_incomingRow_ne_base m wd r₀)),
    NonTrivalentValencyThreeStarCount.card_filter_pair _ _
      (NonTrivalentValencyThreeStarCount.dart_ne m wd first second hStar)]
  show incidenceCount (Prescribed.validCandidate sel).datum
    (NonTrivalentValencyTwoRows.endpointVertex sel false
      (Prescribed.selectedRepresentative sel))
    (NonTrivalentValencyTwoDescent.retainedRow src sel
      (NonTrivalentValencyTwoTracks.wallValid m wd) r₀) = _
  unfold incidenceCount
  rw [NonTrivalentValencyTwoStarCount.incidentEdges_endpointVertex_false m wd src sel,
    Finset.filter_insert, ite_eq_right hBridgeRow,
    NonTrivalentValencyThreeStarCount.card_filter_pair _ _
      (NonTrivalentValencyTwoStarCount.mergedRetained_ne m wd sel)]
  have hcond : ∀ side : Bool,
      ((NonTrivalentValencyTwoStarCount.mergedRetained m wd sel side).stablePath =
        NonTrivalentValencyTwoDescent.retainedRow src sel
          (NonTrivalentValencyTwoTracks.wallValid m wd) r₀) ↔
      (NonTrivalentValencyTwoStarCount.mergedWall m wd sel side).stablePath = r₀ := by
    intro side
    rw [NonTrivalentValencyTwoStarCount.stablePath_mergedRetained m wd src sel side]
    exact ⟨fun h ↦ NonTrivalentValencyTwoStarCount.injective_retainedRow src sel
      (NonTrivalentValencyTwoTracks.wallValid m wd) hOrd h, fun h ↦ congrArg _ h⟩
  rw [if_congr (hcond false) rfl rfl, if_congr (hcond true) rfl rfl,
    if_congr (label_dart_merged_iff m wd sel first false hFirst r₀) rfl rfl,
    if_congr (label_dart_merged_iff m wd sel second true hSecond r₀) rfl rfl]

include hOrd in
/-- **The star count at `A_u`, on the bridge row.**  Both sides are one: the
bridge occurrence downstairs, the contracted dart `m.base` upstairs. -/
theorem incidence_inr_false_bridge (E : VanishingEnds m wd anchorBlk)
    (hPres : PrescribedMergedMoveOn m wd sel E) :
    incidenceCount (Prescribed.validCandidate sel).datum
        (NonTrivalentValencyTwoTracks.candBranchMap m wd src sel hOrd (Sum.inr false)).1
        (NonTrivalentValencyTwoRowEquiv.bridgeRow src sel
          (NonTrivalentValencyTwoTracks.wallValid m wd)) =
      Nat.card {d : D // graph.vert (m.perm d) =
          NonTrivalentValencyTwoTracksLeaf.vertexEquiv m wd src sel hOrd E.ends
            (NonTrivalentValencyTwoTracks.candBranchMap m wd src sel hOrd (Sum.inr false)) ∧
        label d = (NonTrivalentValencyTwoExitFree.wallOutgoingFD' m wd src sel hOrd labelling₀
            hRowVal hMatrixWall).labelling.row
          (NonTrivalentValencyTwoRowEquiv.bridgeRow src sel
            (NonTrivalentValencyTwoTracks.wallValid m wd))} := by
  classical
  obtain ⟨hBase, hOpBase, first, second, hFirst, hSecond, hStar⟩ := hPres
  rw [vertexEquiv_anchor_false m wd src sel hOrd E hBase,
    outFD'_row_bridge m wd src sel hOrd labelling₀ hRowVal hMatrixWall]
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
    · exact NonTrivalentValencyTwoStarCount.label_dart_merged_ne_base m wd sel first false hFirst
    · exact NonTrivalentValencyTwoStarCount.label_dart_merged_ne_base m wd sel second true hSecond
  have hR : ((Finset.univ.filter fun d : D ↦ graph.vert (m.perm d) = graph.vert m.base).filter
      fun d ↦ label d = label m.base).card = 1 := by
    rw [NonTrivalentValencyThreeStarCount.filter_moved_base m wd first second hStar,
      Finset.filter_insert, ite_eq_left rfl, hEmptyD]
    simp
  rw [hRHS, hR]
  show incidenceCount (Prescribed.validCandidate sel).datum
    (NonTrivalentValencyTwoRows.endpointVertex sel false
      (Prescribed.selectedRepresentative sel))
    (NonTrivalentValencyTwoRowEquiv.bridgeRow src sel
      (NonTrivalentValencyTwoTracks.wallValid m wd)) = 1
  have hEmptyC : (({NonTrivalentValencyTwoStarCount.mergedRetained m wd sel false,
        NonTrivalentValencyTwoStarCount.mergedRetained m wd sel true} :
        Finset (NonDanglingEdge (Prescribed.validCandidate sel).datum)).filter
      fun e ↦ e.stablePath =
        NonTrivalentValencyTwoRowEquiv.bridgeRow src sel
          (NonTrivalentValencyTwoTracks.wallValid m wd)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · rw [NonTrivalentValencyTwoStarCount.stablePath_mergedRetained m wd src sel false]
      exact NonTrivalentValencyTwoStarCount.retainedRow_ne_bridgeRow src sel
        (NonTrivalentValencyTwoTracks.wallValid m wd) hOrd _
    · rw [NonTrivalentValencyTwoStarCount.stablePath_mergedRetained m wd src sel true]
      exact NonTrivalentValencyTwoStarCount.retainedRow_ne_bridgeRow src sel
        (NonTrivalentValencyTwoTracks.wallValid m wd) hOrd _
  unfold incidenceCount
  rw [NonTrivalentValencyTwoStarCount.incidentEdges_endpointVertex_false m wd src sel,
    Finset.filter_insert,
    ite_eq_left (NonTrivalentValencyTwoStarCount.stablePath_bridgeND m wd src sel), hEmptyC]
  simp

include hOrd in
/-- **The star count at every branch vertex except `A_v`.** -/
theorem incidence_of_ne_rightAnchor (E : VanishingEnds m wd anchorBlk)
    (hPres : PrescribedMergedMoveOn m wd sel E)
    (v : BranchVertex (Prescribed.validCandidate sel).datum)
    (hv : v ≠ NonTrivalentValencyTwoTracks.candBranchMap m wd src sel hOrd (Sum.inr true))
    (r : StablePath (Prescribed.validCandidate sel).datum) :
    incidenceCount (Prescribed.validCandidate sel).datum v.1 r =
      Nat.card {d : D // graph.vert (m.perm d) =
          NonTrivalentValencyTwoTracksLeaf.vertexEquiv m wd src sel hOrd E.ends v ∧
        label d = (NonTrivalentValencyTwoExitFree.wallOutgoingFD' m wd src sel hOrd labelling₀
          hRowVal hMatrixWall).labelling.row r} := by
  classical
  obtain ⟨x, rfl⟩ : ∃ x, NonTrivalentValencyTwoTracks.candBranchMap m wd src sel hOrd x = v :=
    ⟨(NonTrivalentValencyTwoTracks.candBranchEquiv m wd src sel hOrd).symm v,
      (NonTrivalentValencyTwoTracks.candBranchEquiv m wd src sel hOrd).apply_symm_apply v⟩
  obtain ⟨r', rfl⟩ : ∃ r', NonTrivalentValencyTwoRowEquiv.rowMap src sel
      (NonTrivalentValencyTwoTracks.wallValid m wd) r' = r :=
    ⟨NonTrivalentValencyTwoRowEquiv.rowEquiv src sel
        (NonTrivalentValencyTwoTracks.wallValid m wd) hOrd r,
      (NonTrivalentValencyTwoRowEquiv.rowEquiv src sel
        (NonTrivalentValencyTwoTracks.wallValid m wd) hOrd).left_inv r⟩
  cases x with
  | inl w =>
    cases r' with
    | none =>
      exact incidence_inl_bridge m wd src sel hOrd labelling₀ hRowVal hMatrixWall E hPres w
    | some r₀ =>
      exact incidence_inl_retained m wd src sel hOrd labelling₀ hRowVal hMatrixWall E hPres w r₀
  | inr side =>
    cases side with
    | true => exact absurd rfl hv
    | false =>
      cases r' with
      | none =>
        exact incidence_inr_false_bridge m wd src sel hOrd labelling₀ hRowVal hMatrixWall E hPres
      | some r₀ =>
        exact incidence_inr_false_retained m wd src sel hOrd labelling₀ hRowVal hMatrixWall E
          hPres r₀

include hOrd in
/-- **The star count at `A_v`, from the leftover equation.**  A stable row of the
candidate meets its branch vertices twice in all, a chart row carries two darts
of the moved graph, `vertexEquiv` is a bijection, and the count agrees at every
other branch vertex; so it agrees at `A_v` too. -/
theorem incidence_inr_true (E : VanishingEnds m wd anchorBlk)
    (hPres : PrescribedMergedMoveOn m wd sel E)
    (r : StablePath (Prescribed.validCandidate sel).datum) :
    incidenceCount (Prescribed.validCandidate sel).datum
        (NonTrivalentValencyTwoTracks.candBranchMap m wd src sel hOrd (Sum.inr true)).1 r =
      Nat.card {d : D // graph.vert (m.perm d) =
          NonTrivalentValencyTwoTracksLeaf.vertexEquiv m wd src sel hOrd E.ends
            (NonTrivalentValencyTwoTracks.candBranchMap m wd src sel hOrd (Sum.inr true)) ∧
        label d = (NonTrivalentValencyTwoExitFree.wallOutgoingFD' m wd src sel hOrd labelling₀
          hRowVal hMatrixWall).labelling.row r} := by
  classical
  set outFD := NonTrivalentValencyTwoExitFree.wallOutgoingFD' m wd src sel hOrd labelling₀
    hRowVal hMatrixWall with houtFD
  set v₀ := NonTrivalentValencyTwoTracks.candBranchMap m wd src sel hOrd (Sum.inr true) with hv₀
  set f : BranchVertex (Prescribed.validCandidate sel).datum → ℕ :=
    fun v ↦ incidenceCount (Prescribed.validCandidate sel).datum v.1 r with hf
  set g : BranchVertex (Prescribed.validCandidate sel).datum → ℕ :=
    fun v ↦ Nat.card {d : D // graph.vert (m.perm d) =
        NonTrivalentValencyTwoTracksLeaf.vertexEquiv m wd src sel hOrd E.ends v ∧
      label d = outFD.labelling.row r} with hg
  have hSumF : ∑ v, f v = 2 :=
    NonTrivalentValencyThreeStarCount.sum_incidenceCount_branchVertex
      (Prescribed.validCandidate sel).datum outFD.connected outFD.pathEnds r
  have hSumG : ∑ v, g v = 2 := by
    rw [Fintype.sum_equiv (NonTrivalentValencyTwoTracksLeaf.vertexEquiv m wd src sel hOrd E.ends)
      g (fun x : V ↦ Nat.card {d : D // graph.vert (m.perm d) = x ∧
        label d = outFD.labelling.row r}) (fun v ↦ rfl)]
    exact NonTrivalentValencyThreeStarCount.sum_natCard_moved m wd (outFD.labelling.row r)
  have hAway : ∀ v ∈ Finset.univ.erase v₀, f v = g v := by
    intro v hv
    exact incidence_of_ne_rightAnchor m wd src sel hOrd labelling₀ hRowVal hMatrixWall E hPres v
      (Finset.mem_erase.mp hv).1 r
  have hfsum := Finset.add_sum_erase Finset.univ f (Finset.mem_univ v₀)
  have hgsum := Finset.add_sum_erase Finset.univ g (Finset.mem_univ v₀)
  have hEq : ∑ x ∈ Finset.univ.erase v₀, f x = ∑ x ∈ Finset.univ.erase v₀, g x :=
    Finset.sum_congr rfl hAway
  show f v₀ = g v₀
  omega

include hOrd in
/-- **The star count, at every branch vertex and every row, at any two-valent
Base II wall.**  This is the one geometric input of
`NonTrivalentValencyTwoTracksLeaf.typeChangeLink_of_incidence`, here under
(H-II) alone. -/
theorem incidence_of_prescribedMergedMove (E : VanishingEnds m wd anchorBlk)
    (hPres : PrescribedMergedMoveOn m wd sel E)
    (v : BranchVertex (Prescribed.validCandidate sel).datum)
    (r : StablePath (Prescribed.validCandidate sel).datum) :
    incidenceCount (Prescribed.validCandidate sel).datum v.1 r =
      Nat.card {d : D // graph.vert (m.perm d) =
          NonTrivalentValencyTwoTracksLeaf.vertexEquiv m wd src sel hOrd E.ends v ∧
        label d = (NonTrivalentValencyTwoExitFree.wallOutgoingFD' m wd src sel hOrd labelling₀
          hRowVal hMatrixWall).labelling.row r} := by
  classical
  by_cases hv : v = NonTrivalentValencyTwoTracks.candBranchMap m wd src sel hOrd (Sum.inr true)
  · subst hv
    exact incidence_inr_true m wd src sel hOrd labelling₀ hRowVal hMatrixWall E hPres r
  · exact incidence_of_ne_rightAnchor m wd src sel hOrd labelling₀ hRowVal hMatrixWall E hPres v
      hv r

include hOrd in
/-- **`OuterWalk.TypeChangeLink` at ANY two-valent Base II wall under (H-II).**
`NonTrivalentValencyTwoTracksLeaf` reduces the link at all three incoming
sub-cases to one star count against `wallOutgoingFD'`; this discharges it. -/
def typeChangeLink_of_prescribedMergedMove_two (E : VanishingEnds m wd anchorBlk)
    (hPres : PrescribedMergedMoveOn m wd sel E) : TypeChangeLink m wd :=
  NonTrivalentValencyTwoTracksLeaf.typeChangeLink_of_incidence m wd src sel hOrd labelling₀
    hRowVal hMatrixWall E.ends
    (incidence_of_prescribedMergedMove m wd src sel hOrd labelling₀ hRowVal hMatrixWall E hPres)

end Anchor

/-! ## 8.  Producers, non-vacuity, and the receipt-free headline -/

section Producers

variable {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hOrd : OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk)

/-- **The vanishing ends at a `1 + 3` or `3 + 1` leaf wall**: the two *outer*
ends of the two-occurrence vanishing path of `NonTrivalentValencyTwoTracksLeaf`. -/
def vanishingEnds_of_leafFold (F : NonTrivalentValencyTwoTracksLeaf.LeafFold wd) :
    VanishingEnds m wd anchorBlk where
  left := NonTrivalentValencyTwoTracksLeaf.leftEnd m wd F
  right := NonTrivalentValencyTwoTracksLeaf.rightEnd m wd F
  ends := NonTrivalentValencyTwoTracksLeaf.anchorEnds_leaf m wd F src hOrd
  leftMeets := (incidenceCount_pos_iff wd.cover _ _).mpr
    ⟨NonTrivalentValencyTwoTracks.facetEdge m wd,
      NonTrivalentValencyTwoTracksLeaf.incident_facetEdge_leftEnd m wd F,
      NonTrivalentValencyTwoTracks.facetEdge_stablePath m wd⟩
  rightMeets := (incidenceCount_pos_iff wd.cover _ _).mpr
    ⟨NonTrivalentValencyTwoTracksLeaf.secondEdge m wd F,
      NonTrivalentValencyTwoTracksLeaf.incident_secondEdge_rightEnd m wd F,
      NonTrivalentValencyTwoTracksLeaf.secondEdge_stablePath m wd F⟩

/-- **The vanishing ends at a `2 + 2` wall**: the two ends of the single
vanishing occurrence of `NonTrivalentValencyTwoTracks`. -/
def vanishingEnds_of_noContractedReturn
    (hNoReturn : NoContractedReturn wd.cover wd.contracted) :
    VanishingEnds m wd anchorBlk where
  left := NonTrivalentValencyTwoTracks.leftEnd m wd
  right := NonTrivalentValencyTwoTracks.rightEnd m wd
  ends := NonTrivalentValencyTwoTracksLeaf.anchorEnds_of_noContractedReturn m wd src hOrd
    hNoReturn
  leftMeets := (incidenceCount_pos_iff wd.cover _ _).mpr
    ⟨NonTrivalentValencyTwoTracks.facetEdge m wd,
      NonTrivalentValencyTwoTracks.incident_facetEdge_leftEnd m wd,
      NonTrivalentValencyTwoTracks.facetEdge_stablePath m wd⟩
  rightMeets := (incidenceCount_pos_iff wd.cover _ _).mpr
    ⟨NonTrivalentValencyTwoTracks.facetEdge m wd,
      NonTrivalentValencyTwoTracks.incident_facetEdge_rightEnd m wd,
      NonTrivalentValencyTwoTracks.facetEdge_stablePath m wd⟩

include src hOrd in
/-- **Vanishing ends at every two-valent Base II wall**, and the non-vacuity
witness of `VanishingEnds`.  The `exists_anchorEnds` trichotomy of
`NonTrivalentValencyTwoTracksLeaf`, carrying the two extra incidence facts. -/
theorem nonempty_vanishingEnds : Nonempty (VanishingEnds m wd anchorBlk) := by
  classical
  obtain ⟨hMerge, hA1, hA3, hB1, hB3, -, -⟩ := WallProgress.endpoints_of_contraction wd.cover
    wd.hc wd.hab wd.hOne wd.fullDim.valid wd.fullDim.changeMinimal
  have hStar := wallStar.card_incidentEdges
  by_cases hLeafA : (GluingDatum.incidentEdges (target := wd.coverTarget) wd.a).card = 1
  · exact ⟨vanishingEnds_of_leafFold m wd src hOrd
      (NonTrivalentValencyTwoTracksLeaf.leafFold_of_leaf_left m wd hLeafA)⟩
  · by_cases hLeafB : (GluingDatum.incidentEdges (target := wd.coverTarget) wd.b).card = 1
    · exact ⟨vanishingEnds_of_leafFold m wd src hOrd
        (NonTrivalentValencyTwoTracksLeaf.leafFold_of_leaf_right m wd hLeafB)⟩
    · exact ⟨vanishingEnds_of_noContractedReturn m wd src hOrd
        (NonTrivalentValencyTwoExit.noContractedReturn_of_two_two m wd (by omega) (by omega))⟩

section Any

variable (sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
  anchorBlk)

/-- **The `2 + 2` form of (H-II) (`NonTrivalentValencyTwoTracks.PrescribedMergedMove`)
implies the dispatcher's.** -/
theorem prescribedMergedMoveAny_of_prescribedMergedMove
    (hNoReturn : NoContractedReturn wd.cover wd.contracted)
    (hPres : NonTrivalentValencyTwoTracks.PrescribedMergedMove m wd hNoReturn sel) :
    PrescribedMergedMoveAny m wd sel := by
  obtain ⟨hBase, first, second, hFirst, hSecond, hStar⟩ := hPres
  exact ⟨⟨NonTrivalentValencyTwoTracks.leftBranch m wd hNoReturn,
      NonTrivalentValencyTwoTracks.rightBranch m wd hNoReturn,
      (incidenceCount_pos_iff wd.cover _ _).mpr
        ⟨NonTrivalentValencyTwoTracks.facetEdge m wd,
          NonTrivalentValencyTwoTracks.incident_facetEdge_leftEnd m wd,
          NonTrivalentValencyTwoTracks.facetEdge_stablePath m wd⟩,
      (incidenceCount_pos_iff wd.cover _ _).mpr
        ⟨NonTrivalentValencyTwoTracks.facetEdge m wd,
          NonTrivalentValencyTwoTracks.incident_facetEdge_rightEnd m wd,
          NonTrivalentValencyTwoTracks.facetEdge_stablePath m wd⟩,
      NonTrivalentValencyTwoTracks.vert_base_eq m wd hNoReturn hBase,
      (NonTrivalentValencyTwoTracks.vert_opBase_eq m wd hNoReturn hBase).2⟩,
    first, second, hFirst, hSecond, hStar⟩

/-- **The leaf form of (H-II)
(`NonTrivalentValencyTwoTracksLeaf.PrescribedMergedMoveLeaf`) implies the
dispatcher's.** -/
theorem prescribedMergedMoveAny_of_leaf (F : NonTrivalentValencyTwoTracksLeaf.LeafFold wd)
    (hPres : NonTrivalentValencyTwoTracksLeaf.PrescribedMergedMoveLeaf m wd F sel) :
    PrescribedMergedMoveAny m wd sel := by
  obtain ⟨hBase, first, second, hFirst, hSecond, hStar⟩ := hPres
  exact ⟨⟨(NonTrivalentValencyTwoTracksLeaf.facetDartLeft m wd F).1,
      (NonTrivalentValencyTwoTracksLeaf.facetDartRight m wd F).1,
      (incidenceCount_pos_iff wd.cover _ _).mpr
        ⟨NonTrivalentValencyTwoTracks.facetEdge m wd,
          NonTrivalentValencyTwoTracksLeaf.incident_facetEdge_leftEnd m wd F,
          NonTrivalentValencyTwoTracks.facetEdge_stablePath m wd⟩,
      (incidenceCount_pos_iff wd.cover _ _).mpr
        ⟨NonTrivalentValencyTwoTracksLeaf.secondEdge m wd F,
          NonTrivalentValencyTwoTracksLeaf.incident_secondEdge_rightEnd m wd F,
          NonTrivalentValencyTwoTracksLeaf.secondEdge_stablePath m wd F⟩,
      NonTrivalentValencyTwoTracksLeaf.vert_base_eq m wd F hBase,
      (NonTrivalentValencyTwoTracksLeaf.vert_opBase_eq m wd F hBase).2⟩,
    first, second, hFirst, hSecond, hStar⟩

end Any

end Producers

/-! ### Non-vacuity of the dispatcher's (H-II), in relative form -/

section NonVacuity

variable {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)

/-- **Non-vacuity of the dispatcher's (H-II) at a `2 + 2` wall, in relative
form**: `NonTrivalentValencyTwoTracks.prescribedMove`, which contracts the same
occurrence as `m`, satisfies it. -/
theorem prescribedMergedMoveAny_prescribedMove
    (hNoReturn : NoContractedReturn wd.cover wd.contracted)
    (hSep : NonTrivalentValencyTwoTracks.MergedSeparated m wd sel)
    (hBase : wd.tracks.iso.dart (NonTrivalentValencyTwoTracks.facetDartLeft m wd hNoReturn) =
      m.base) :
    PrescribedMergedMoveAny
      (NonTrivalentValencyTwoTracks.prescribedMove m wd hNoReturn sel hSep hBase) wd sel :=
  prescribedMergedMoveAny_of_prescribedMergedMove
    (NonTrivalentValencyTwoTracks.prescribedMove m wd hNoReturn sel hSep hBase) wd sel hNoReturn
    (NonTrivalentValencyTwoTracks.prescribedMergedMove_prescribedMove m wd hNoReturn sel hSep
      hBase)

/-- **Non-vacuity of the dispatcher's (H-II) at a leaf wall, in relative
form**: `NonTrivalentValencyTwoTracksLeaf.prescribedMove` satisfies it. -/
theorem prescribedMergedMoveAny_prescribedMove_leaf
    (F : NonTrivalentValencyTwoTracksLeaf.LeafFold wd)
    (hSep : NonTrivalentValencyTwoTracksLeaf.MergedSeparatedLeaf m wd F sel)
    (hBase : wd.tracks.iso.dart (NonTrivalentValencyTwoTracksLeaf.facetDartLeft m wd F) =
      m.base) :
    PrescribedMergedMoveAny
      (NonTrivalentValencyTwoTracksLeaf.prescribedMove m wd F sel hSep hBase) wd sel :=
  prescribedMergedMoveAny_of_leaf
    (NonTrivalentValencyTwoTracksLeaf.prescribedMove m wd F sel hSep hBase) wd sel F
    (NonTrivalentValencyTwoTracksLeaf.prescribedMergedMove_prescribedMove m wd F sel hSep hBase)

end NonVacuity

/-! ### The link, and the receipt-free headline -/

section Headline

variable {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hOrd : OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk)
  (labelling₀ : StableLengthMatrixLabelling (contractDatum wd.cover wd.hc wd.hab wd.hOne)
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

include src hOrd labelling₀ hRowVal hMatrixWall in
/-- **`OuterWalk.TypeChangeLink` at any two-valent Base II wall, from the
dispatcher's (H-II) alone.**  The incoming `2 + 2` / `1 + 3` / `3 + 1`
trichotomy and the orientation of the two ends are discharged internally. -/
theorem nonempty_typeChangeLink_of_prescribedMergedMoveAny
    (hPres : PrescribedMergedMoveAny m wd sel) : Nonempty (TypeChangeLink m wd) := by
  classical
  obtain ⟨E⟩ := nonempty_vanishingEnds m wd src hOrd
  rcases prescribedMergedMoveOn_of_any m wd sel E hPres with h | h
  · exact ⟨typeChangeLink_of_prescribedMergedMove_two m wd src sel hOrd labelling₀ hRowVal
      hMatrixWall E h⟩
  · exact ⟨typeChangeLink_of_prescribedMergedMove_two m wd src sel hOrd labelling₀ hRowVal
      hMatrixWall (swapEnds m wd E) h⟩

include src hOrd labelling₀ hRowVal hMatrixWall in
/-- **The link at a `2 + 2` wall from the `2 + 2` form of (H-II)**, so the
headline of `NonTrivalentValencyTwoStarCount` is recovered at the no-return-free
presentation with no no-return hypothesis in the conclusion's shape. -/
theorem nonempty_typeChangeLink_of_prescribedMergedMove
    (hNoReturn : NoContractedReturn wd.cover wd.contracted)
    (hPres : NonTrivalentValencyTwoTracks.PrescribedMergedMove m wd hNoReturn sel) :
    Nonempty (TypeChangeLink m wd) :=
  nonempty_typeChangeLink_of_prescribedMergedMoveAny m wd src sel hOrd labelling₀ hRowVal
    hMatrixWall (prescribedMergedMoveAny_of_prescribedMergedMove m wd sel hNoReturn hPres)

include src hOrd labelling₀ hRowVal hMatrixWall in
/-- **The link at a `1 + 3` or `3 + 1` leaf wall from the leaf form of (H-II)**
-- the sub-cases outside the reach of `NonTrivalentValencyTwoStarCount`. -/
theorem nonempty_typeChangeLink_of_prescribedMergedMoveLeaf
    (F : NonTrivalentValencyTwoTracksLeaf.LeafFold wd)
    (hPres : NonTrivalentValencyTwoTracksLeaf.PrescribedMergedMoveLeaf m wd F sel) :
    Nonempty (TypeChangeLink m wd) :=
  nonempty_typeChangeLink_of_prescribedMergedMoveAny m wd src sel hOrd labelling₀ hRowVal
    hMatrixWall (prescribedMergedMoveAny_of_leaf m wd sel F hPres)

end Headline

/-- **The Base II type-changing exit at a two-valent wall of the outer walk,
with the star count discharged.**
`NonTrivalentValencyTwoTracksLeaf.exists_typeChangeLink_of_incidence_of_wallData`
with its star-count input replaced by (H-II) in the dispatcher's single shape:
from the wall data and the incoming two-valent star alone this produces the
anchor block, and for **every** `sel` the outgoing full-dimensional presentation
on the incoming chart, the common minor `AgreeOffColumn` that
`TypeChangeLink.agree` asks for, and the link itself as soon as (H-II) is
supplied. No receipt about the candidate, no no-return hypothesis and no
incoming sub-case dispatch is needed. -/
theorem exists_typeChangeLink_of_prescribedMergedMove_of_wallData
    (wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    ∃ (anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
      (_src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlock),
      ∀ sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
          anchorBlock,
        ∃ out : FullDimensionalSourcePresentation (Prescribed.validCandidate sel).datum
            coordinate,
          AgreeOffColumn wd.incomingMatrix
              (GluingDatum.LengthMatrixPresentation.matrix out.labelling.presentation)
              wd.column ∧
            (PrescribedMergedMoveAny m wd sel → Nonempty (TypeChangeLink m wd)) := by
  classical
  obtain ⟨anchorBlock, src, -, hSelection⟩ :=
    NonTrivalentValencyTwoRowEquiv.exists_rowEquiv_of_wall_metric wd.cover wd.fullDim wd.hc
      wd.hab wd.hOne (wd.hForest m) wallStar wd.coordinates (label m.base) wd.hRows
      wd.hZeroCoord wd.hPosCoord wd.hFacetZero
  obtain ⟨-, -, hOrd, -, -⟩ := hSelection (Prescribed.Selection.default src)
  obtain ⟨labelling₀, hRowVal, hMatrixWall⟩ :=
    NonTrivalentValencyTwoBaseOneRowDictionary.exists_wallLabelling_two wd.cover wd.fullDim
      wd.hc wd.hab wd.hOne (wd.hForest m) (label m.base) wallStar wd.coordinates wd.hRows
      wd.hZeroCoord wd.hPosCoord wd.hFacetZero
  refine ⟨anchorBlock, src, fun sel ↦ ?_⟩
  refine ⟨NonTrivalentValencyTwoExitFree.wallOutgoingFD' m wd src sel hOrd labelling₀ hRowVal
    hMatrixWall, ?_, ?_⟩
  · have h := NonTrivalentValencyTwoExitFree.agreeOffColumn_outLabelling' wd.cover wd.fullDim
      wd.hc wd.hab wd.hOne (wd.hForest m) (label m.base) labelling₀ src sel hOrd hRowVal
      hMatrixWall wd.coordinates wd.hZeroCoord wd.hPosCoord wd.hFacetZero
    rw [wd.targetEdge_symm_contracted] at h
    exact h
  · intro hPres
    exact nonempty_typeChangeLink_of_prescribedMergedMoveAny m wd src sel hOrd labelling₀
      hRowVal hMatrixWall hPres

end

end DraismaVargas.LocalCases.NonTrivalentValencyTwoStarCountAll
