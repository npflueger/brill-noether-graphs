import DraismaVargas.LocalCases.OuterWalk
import DraismaVargas.LocalCases.NonTrivalentValencyTwoRowDictionary

/-!
# The valency-two Base II exit: the outgoing full-dimensional presentation

Source: Vargas, Part II (arXiv:2609.09109), Section 5.1 (the labelling
convention at a non-trivalent wall, and `lm:change-comb-type`: the wall matrix
is the common minor `A_{\varphi_0}` of the two incoming matrices) together with
Section 5.4 (Case {v2-nd4}, base tree `T_2` = Base II, the merge member).  The
consumer interface is `OuterWalk.TypeChangeLink`.

This module supplies the *exit* at a two-valent wall.  The Base II candidate,
its stable rows, its row equivalence and its entrywise common-minor identity
are in `NonTrivalentValencyTwoCandidate`, `NonTrivalentValencyTwoRows`,
`NonTrivalentValencyTwoRowEquiv` and `NonTrivalentValencyTwoRowDictionary`;
what they do not provide is the object `OuterWalk.TypeChangeLink` actually
asks for: a `FullDimensionalSourcePresentation` of the outgoing candidate **on
the incoming chart index type**, together with the `AgreeOffColumn` statement
against the incoming honest matrix.

## The labelling convention, and why `chartLabelling` is re-indexed

`NonTrivalentValencyTwoRowDictionary.chartLabelling` re-indexes the candidate's
honest labelling along a *single* equivalence `Option coordinate₀ ≃ coordinate`.
That ties the bridge row and the new target occurrence to one and the same
coordinate.  At a Part II wall they must sit in *different* coordinates: the
new target occurrence goes into the vanishing **column** `t_1`
(`fd.labelling.targetEdge.symm contracted`) and the bridge row goes into the
vanishing **row** `h_1` (`facet`, which along the walk is `label m.base`).
`reindexLabelling₂` therefore re-indexes rows and columns by two different
equivalences -- `rowChart` sending `none` to `facet`, `colChart` sending `none`
to the contracted column -- and `rowChart` absorbs exactly the transposition
`Equiv.swap facet (targetEdge.symm contracted)` that
`StablePathFacetContraction.wallRowIndex` built into the wall datum's square
labelling.  With this choice, and only with it, the outgoing matrix agrees with
the incoming one in *every* row off the contracted column.

## What is proved

* `ofTypeChange`: `StableGraphFullDimensional.presentationOfEquivalence`
  does not apply across a type change (there is no stable-graph equivalence);
  this constructor takes the outgoing `valid`, `targetConnected`,
  `targetGenus`, `labelling`, `det_ne_zero`, `trivalent`, `pathEnds` and
  **derives `saturated`** from the incoming presentation, the equality of target
  edge counts, and source-genus preservation.
* `genus_sourceGraph_contractDatum`: the wall contraction preserves the source
  genus, from the contraction forest alone (one source vertex and one source
  occurrence disappear together in every fibre:
  `WallAdmissibility.card_side_eq`, `card_inducedEdges_eq` at `S = T = univ`).
  Unlike `W4Bridge.genus_sourceGraph_contractDatum_eq` this needs no
  change-minimality hypothesis away from the wall.
* `reindexLabelling₂`, `matrix_reindexLabelling₂`, `wallLab`, `rowChart`,
  `colChart`, `outLabelling`: the outgoing honest labelling in the incoming
  chart, with the convention above.
* `matrix_outLabelling_eq_incoming`: entry by entry, the outgoing matrix in a
  retained row and a retained column is the incoming matrix's own entry -- the
  common minor, obtained by composing
  `NonTrivalentValencyTwoRowDictionary.matrix_candidateLabelling` with
  `StablePathFacetContraction.matrix_wallLabelling`.
* `matrix_outLabelling_facet_eq_zero` and `matrix_outLabelling_corner_pos`: the
  bridge row of the outgoing matrix vanishes off the contracted column and its
  corner entry is `1 / index(h_1) > 0` (`bridgeEdge_isolated` says the bridge is
  alone in its stable class, and its only occurrence lies over the new target
  occurrence).
* `agreeOffColumn_outLabelling`: the `AgreeOffColumn` shape
  `OuterWalk.TypeChangeLink.agree` asks for, and `det_outLabelling_ne_zero`, the
  outgoing nonsingularity, by `NonTrivalentLinkMatrix.det_ne_zero`.
* `outgoing_targetConnected`, `outgoing_targetGenus`, `outgoing_targetEdgeCard`:
  the expanded wall target is connected of genus zero and has as many edges as
  the incoming target (one contracted, one regrown).
* `wallDatum_trivalent_away` and `candidate_trivalent`: **the outgoing candidate
  is trivalent**.  Away from the wall the incoming trivalence descends twice
  (`WallDegeneration.nonDanglingValency_sourceVertexMap`, then
  `ResolutionAwayFromWall.nonDanglingValency_retainedVertex`); at the anchor the
  two endpoint classes have surviving valency three and the Configuration B
  subdivision vertex surviving valency two (`NonTrivalentValencyTwoRows`); at an
  ordinary block the census of `NonTrivalentValencyTwoDescent` together with
  `OrdinaryTrivalent` bounds both sides by three.
* `outgoingFD`: the outgoing `FullDimensionalSourcePresentation` on `coordinate`.
* `typeChangeLink_of_receipts`: an inhabitant of
  `OuterWalk.TypeChangeLink` at a two-valent wall, with `base` the wall datum,
  `baseValid` the wall datum's own validity, `candidate` the Base II merge
  member, `outgoingFD` the presentation above and `agree` the common minor.
  Every declaration of this file that mentions the candidate carries the merged
  pair as an explicit parameter
  `sel : NonTrivalentValencyTwoCandidate.Prescribed.Selection ...`, so
  `typeChangeLink_of_receipts` is universally quantified over the prescribed
  pair: a consumer matching the darts of the Whitehead move `m` may *choose*
  which two of the thick survivors are merged, which in Configuration B
  (`3 + 1`, three merge members) is exactly what a prescribed move requires.
* `exists_anchor_of_wallData`: the anchor block, its `TwoBranchAnchor`
  classification and `OrdinaryTrivalent` at an actual two-valent wall, with no
  further hypothesis, from
  `NonTrivalentValencyTwoRowEquiv.exists_rowEquiv_of_wall_metric`.
* `noContractedReturn_of_two_two`: the `2 + 2` sub-case discharge of
  `hNoReturn`.

## What is NOT proved -- the hypotheses that remain explicit

1. `hNoReturn : StablePathFacetContraction.NoContractedReturn wd.cover wd.contracted`.
   Discharged here in the `2 + 2` sub-case (`noContractedReturn_of_two_two`).
   In the `1 + 3` sub-case the predicate is false and the replacement is
   `LeafFacetNoReturn.NoContractedReturnOffRow`.
   `NonTrivalentValencyTwoExitFree` treats that case, using
   `NonTrivalentValencyTwoBaseOneRowDictionary.exists_wallLabelling_two` and
   `NonTrivalentValencyTwoBaseOneExit.noContractedReturnOffRow_two`, which need
   no no-return hypothesis.
2. `hPathEnds : W4StableSource.HasPathEnds (Prescribed.validCandidate sel).datum`.
   The only geometric hypothesis of the outgoing presentation left open here.
   It does not come from the usual producers of `HasPathEnds`, which all go
   through `StableGraphIncidence.Equivalence`, which does not exist across a
   type change; `WallDatumPathEnds` proves `HasPathEnds` of the wall datum
   directly and transports it (`WallDatumPathEnds.typeChangeLink_of_receipts'`).
3. `tracks : InteriorGraphTracking.Tracks (outgoingFD ...) (graph.move m) label`:
   the dart-level dictionary between the candidate's stable graph and the
   Whitehead move of the tracked ambient graph.  It is carried here as a
   hypothesis of `typeChangeLink_of_receipts`, so the rest of the link is
   proved here.  The matching of `m`'s darts to the two merged thick survivors
   is expressed through the parameter `sel`, and `CubicDartGraph.MoveData.swap`
   (with `move_swap`) lets the matching read `m` from either end of the
   contracted edge; `NonTrivalentValencyTwoTracks` builds the dictionary.

Nothing here identifies a graph by a matrix.

## Consumers

`OuterWalk.TypeChangeLink` (hence `OuterWalk.coneEntry_of_reaches` and the
type-change link of the outer walk) at Part II, Case {v2-nd4}.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoExit

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRows
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRowEquiv

noncomputable section






/-! ### ofTypeChange -/

def ofTypeChange {target₁ target₂ : CFGraph} {degree : ℕ}
    {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (source : FullDimensionalSourcePresentation first coordinate)
    (destinationValid : second.Valid)
    (destinationTargetConnected : graph_connected target₂)
    (destinationTargetGenus : genus target₂ = 0)
    (targetEdgeCard : target₂.edges.card = target₁.edges.card)
    (sourceGenus : genus second.sourceGraph = genus first.sourceGraph)
    (destinationLabelling : StableLengthMatrixLabelling second coordinate)
    (destinationDet : (GluingDatum.LengthMatrixPresentation.matrix
      destinationLabelling.presentation).det ≠ 0)
    (destinationTrivalent : ∀ vertex : second.SourceVertex,
      nonDanglingValency second vertex ≤ 3)
    (destinationPathEnds : HasPathEnds second) :
    FullDimensionalSourcePresentation second coordinate where
  valid := destinationValid
  targetConnected := destinationTargetConnected
  targetGenus := destinationTargetGenus
  saturated := by rw [targetEdgeCard, sourceGenus]; exact source.saturated
  labelling := destinationLabelling
  det_ne_zero := destinationDet
  trivalent := destinationTrivalent
  pathEnds := destinationPathEnds

/-! ### genus preservation under the wall contraction -/

theorem genus_sourceGraph_contractDatum {target : CFGraph} {degree : ℕ}
    {a b : target.V} {contracted : target.edges}
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted) :
    genus (contractDatum data hc hab hOne).sourceGraph = genus data.sourceGraph := by
  classical
  have hmem : ∀ u : data.SourceVertex,
      u ∈ (Finset.univ : Finset data.SourceVertex) ↔
        sourceVertexMap data hc hab hOne u ∈
          (Finset.univ : Finset (contractDatum data hc hab hOne).SourceVertex) := by
    intro u; simp
  have hV := WallAdmissibility.card_side_eq data hc hab hOne hForest hmem
  have hE := WallAdmissibility.card_inducedEdges_eq data hc hab hOne hmem
  have hFilterUp : ((Finset.univ : Finset data.SourceEdge).filter
      fun e => (data.sourceEnds e).1 ∈ (Finset.univ : Finset data.SourceVertex) ∧
        (data.sourceEnds e).2 ∈ (Finset.univ : Finset data.SourceVertex)) =
      (Finset.univ : Finset data.SourceEdge) := by
    apply Finset.filter_true_of_mem; intro e _; exact ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  have hFilterDown : ((Finset.univ : Finset (contractDatum data hc hab hOne).SourceEdge).filter
      fun e => ((contractDatum data hc hab hOne).sourceEnds e).1 ∈
          (Finset.univ : Finset (contractDatum data hc hab hOne).SourceVertex) ∧
        ((contractDatum data hc hab hOne).sourceEnds e).2 ∈
          (Finset.univ : Finset (contractDatum data hc hab hOne).SourceVertex)) =
      (Finset.univ : Finset (contractDatum data hc hab hOne).SourceEdge) := by
    apply Finset.filter_true_of_mem; intro e _; exact ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  rw [hFilterUp, hFilterDown, Finset.card_univ, Finset.card_univ] at hE
  rw [Finset.card_univ, Finset.card_univ] at hV
  have hEdgeUp : Multiset.card data.sourceGraph.edges = Fintype.card data.SourceEdge := by
    simp [GluingDatum.sourceGraph]
  have hEdgeDown : Multiset.card (contractDatum data hc hab hOne).sourceGraph.edges =
      Fintype.card (contractDatum data hc hab hOne).SourceEdge := by
    simp [GluingDatum.sourceGraph]
  have hVertUp : Fintype.card data.sourceGraph.V = Fintype.card data.SourceVertex := rfl
  have hVertDown : Fintype.card (contractDatum data hc hab hOne).sourceGraph.V =
      Fintype.card (contractDatum data hc hab hOne).SourceVertex := rfl
  unfold genus
  rw [hEdgeUp, hEdgeDown, hVertUp, hVertDown]
  omega





/-! ### A labelling re-indexed by two independent equivalences -/

def reindexLabelling₂ {targetX : CFGraph} {deg : ℕ} {datum : GluingDatum targetX deg}
    {X C : Type*} (eRow : X ≃ C) (eCol : X ≃ C)
    (labelling : StableLengthMatrixLabelling datum X) :
    StableLengthMatrixLabelling datum C where
  targetEdge := eCol.symm.trans labelling.targetEdge
  row := labelling.row.trans eRow

theorem matrix_reindexLabelling₂ {targetX : CFGraph} {deg : ℕ}
    {datum : GluingDatum targetX deg} {X C : Type*} [Fintype X] [DecidableEq X]
    [Fintype C] [DecidableEq C] (eRow : X ≃ C) (eCol : X ≃ C)
    (labelling : StableLengthMatrixLabelling datum X) (row column : X) :
    GluingDatum.LengthMatrixPresentation.matrix
        (reindexLabelling₂ eRow eCol labelling).presentation (eRow row) (eCol column) =
      GluingDatum.LengthMatrixPresentation.matrix labelling.presentation row column := by
  classical
  rw [StableSourceMatrix.labelling_matrix_eq, StableSourceMatrix.labelling_matrix_eq]
  have hCol : (reindexLabelling₂ eRow eCol labelling).targetEdge (eCol column) =
      labelling.targetEdge column := by
    show labelling.targetEdge (eCol.symm (eCol column)) = _
    rw [Equiv.symm_apply_apply]
  have hRow : (reindexLabelling₂ eRow eCol labelling).row.symm (eRow row) =
      labelling.row.symm row := by
    rw [Equiv.symm_apply_eq]
    show eRow row = eRow (labelling.row (labelling.row.symm row))
    rw [Equiv.apply_symm_apply]
  rw [hCol, hRow]





variable {targetIn : CFGraph} {deg : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (cover : GluingDatum targetIn deg)
  (fd : FullDimensionalSourcePresentation cover coordinate)
  {a b : targetIn.V} {contracted : targetIn.edges}
  (hc : (contracted : targetIn.V × targetIn.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges targetIn a b = 1)
  (hForest : ContractionForest cover a b contracted)
  (hNoReturn : NoContractedReturn cover contracted)
  (coordinates : coordinate → ℚ) (facet : coordinate)
  (hRows : ∀ row, row ≠ facet →
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates row ≠ 0)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
  (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
    0 < coordinates column)
  (hFacetZero :
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates facet = 0)

/-- The wall datum's own square honest labelling, with `DanglingCompatible`
derived from the contraction forest. -/
def wallLab :
    StableLengthMatrixLabelling (contractDatum cover hc hab hOne)
      {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted} :=
  wallLabelling cover fd hc hab hOne
    (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne hForest)
    hForest hNoReturn coordinates facet hRows hZeroCoord hPosCoord hFacetZero

theorem wallLab_row_val (p : StablePath (contractDatum cover hc hab hOne)) :
    ((wallLab cover fd hc hab hOne hForest hNoReturn coordinates facet hRows hZeroCoord
        hPosCoord hFacetZero).row p).1 =
      Equiv.swap facet (fd.labelling.targetEdge.symm contracted)
        (fd.labelling.row (incomingRow cover fd hc hab hOne
          (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne hForest)
          hForest p)) := rfl

/-- The column chart: `none` (the new target occurrence) sits in the contracted
column. -/
def colChart :
    Option {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted} ≃
      coordinate :=
  Equiv.optionSubtypeNe (fd.labelling.targetEdge.symm contracted)

/-- The row chart: `none` (the bridge row) sits in the vanishing row. -/
def rowChart :
    Option {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted} ≃
      coordinate :=
  (Equiv.optionCongr (punctureEquiv (fd.labelling.targetEdge.symm contracted) facet)).trans
    (Equiv.optionSubtypeNe facet)

@[simp] theorem colChart_none : colChart cover fd (contracted := contracted) none =
    fd.labelling.targetEdge.symm contracted := rfl

@[simp] theorem colChart_some
    (d : {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted}) :
    colChart cover fd (contracted := contracted) (some d) = d.1 := rfl

@[simp] theorem rowChart_none : rowChart cover fd facet (contracted := contracted) none = facet := rfl

@[simp] theorem rowChart_some
    (d : {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted}) :
    rowChart cover fd facet (contracted := contracted) (some d) =
      Equiv.swap (fd.labelling.targetEdge.symm contracted) facet d.1 := rfl

variable {wallStar : TwoStar (contract targetIn hab hOne) ⟨a, hab⟩}
  {anchorBlk : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩}
  (src : TwoBranchAnchor (contractDatum cover hc hab hOne) wallStar anchorBlk)
  (sel : Prescribed.Selection (contractDatum cover hc hab hOne) wallStar anchorBlk)
  (hOrd : OrdinaryTrivalent (contractDatum cover hc hab hOne) ⟨a, hab⟩ anchorBlk)

/-- **The outgoing honest labelling.** -/
def outLabelling :
    StableLengthMatrixLabelling (Prescribed.validCandidate sel).datum coordinate :=
  reindexLabelling₂ (rowChart cover fd facet) (colChart cover fd)
    (NonTrivalentValencyTwoRowEquiv.labelling src sel
      (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest) hOrd
      (wallLab cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
        hZeroCoord hPosCoord hFacetZero))

theorem matrix_outLabelling_eq_incoming (i j : coordinate) (hi : i ≠ facet)
    (hj : j ≠ fd.labelling.targetEdge.symm contracted) :
    GluingDatum.LengthMatrixPresentation.matrix
        (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
          hZeroCoord hPosCoord hFacetZero src sel hOrd).presentation i j =
      GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation i j := by
  classical
  have hd : Equiv.swap (fd.labelling.targetEdge.symm contracted) facet i ≠
      fd.labelling.targetEdge.symm contracted := by
    intro h
    apply hi
    have h2 := congrArg (Equiv.swap (fd.labelling.targetEdge.symm contracted) facet) h
    rwa [Equiv.swap_apply_self, Equiv.swap_apply_left] at h2
  set d : {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted} :=
    ⟨Equiv.swap (fd.labelling.targetEdge.symm contracted) facet i, hd⟩ with hdDef
  set p := (wallLab cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
    hZeroCoord hPosCoord hFacetZero).row.symm d with hpDef
  have hrow : (wallLab cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
      hZeroCoord hPosCoord hFacetZero).row p = d := Equiv.apply_symm_apply _ _
  have hi' : rowChart cover fd facet (contracted := contracted) (some d) = i := by
    rw [rowChart_some]
    exact Equiv.swap_apply_self _ _ i
  have hMid := matrix_reindexLabelling₂ (rowChart cover fd facet)
    (colChart cover fd (contracted := contracted))
    (NonTrivalentValencyTwoRowEquiv.labelling src sel
      (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest) hOrd
      (wallLab cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
        hZeroCoord hPosCoord hFacetZero)) (some d) (some ⟨j, hj⟩)
  rw [hi'] at hMid
  have hPath : fd.labelling.row (incomingRow cover fd hc hab hOne
      (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne hForest)
      hForest p) = i := by
    have hval := wallLab_row_val cover fd hc hab hOne hForest hNoReturn coordinates facet
      hRows hZeroCoord hPosCoord hFacetZero p
    rw [hrow] at hval
    refine (Equiv.swap facet (fd.labelling.targetEdge.symm contracted)).injective ?_
    rw [← hval, Equiv.swap_comm]
  refine Eq.trans hMid ?_
  rw [← hrow]
  refine Eq.trans (NonTrivalentValencyTwoRowDictionary.matrix_candidateLabelling src sel
    (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest) hOrd
    (wallLab cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
      hZeroCoord hPosCoord hFacetZero) p ⟨j, hj⟩) ?_
  refine Eq.trans (matrix_wallLabelling cover fd hc hab hOne
    (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne hForest)
    hForest hNoReturn coordinates facet hRows hZeroCoord hPosCoord hFacetZero p ⟨j, hj⟩) ?_
  rw [hPath]


/-! ### The bridge row of the outgoing matrix -/

theorem outLabelling_row_symm_facet :
    (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
        hZeroCoord hPosCoord hFacetZero src sel hOrd).row.symm facet =
      NonTrivalentValencyTwoRowEquiv.bridgeRow src sel
        (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest) := by
  have h : (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
      hZeroCoord hPosCoord hFacetZero src sel hOrd).row
        (NonTrivalentValencyTwoRowEquiv.bridgeRow src sel
          (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest)) = facet := by
    show (rowChart cover fd facet (contracted := contracted))
        ((NonTrivalentValencyTwoRowEquiv.labelling src sel
          (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest) hOrd
          (wallLab cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
            hZeroCoord hPosCoord hFacetZero)).row
          (NonTrivalentValencyTwoRowEquiv.bridgeRow src sel
            (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest))) = facet
    have hb : (NonTrivalentValencyTwoRowEquiv.labelling src sel
        (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest) hOrd
        (wallLab cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
          hZeroCoord hPosCoord hFacetZero)).row
        (NonTrivalentValencyTwoRowEquiv.bridgeRow src sel
          (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest)) = none :=
      NonTrivalentValencyTwoRowEquiv.labelling_row_bridge src sel _ hOrd _
    rw [hb]
    rfl
  exact (Equiv.symm_apply_eq _).mpr h.symm

/-- The only surviving occurrence of the bridge row lies over the new target
occurrence, so the bridge row of the outgoing matrix vanishes off the
contracted column. -/
theorem occurrences_bridgeRow_of_ne (t : (TargetExpansion.graph (contract targetIn hab hOne)
      ⟨a, hab⟩ (Prescribed.validCandidate sel).right).edges)
    (ht : t ≠ TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
      (Prescribed.validCandidate sel).right none) :
    StableSourceMatrix.occurrences (Prescribed.validCandidate sel).datum
      (NonTrivalentValencyTwoRowEquiv.bridgeRow src sel
        (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest)) t = ∅ := by
  classical
  refine Finset.eq_empty_iff_forall_notMem.mpr ?_
  intro e he
  obtain ⟨⟨hSurv, hRow⟩, hTarget⟩ := (StableSourceMatrix.mem_occurrences _ t e).mp he
  have hEq := NonTrivalentValencyTwoRows.bridgeEdge_isolated src sel
    (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest)
    ⟨e, hSurv⟩ hRow
  have hEq' : e = NonTrivalentValencyTwoRows.bridgeEdge sel
      (Prescribed.selectedRepresentative sel) := hEq
  apply ht
  rw [← hTarget, hEq']
  exact BalancedGlobal.Candidate.newSourceEdge_target _ _

theorem occurrences_bridgeRow_new :
    StableSourceMatrix.occurrences (Prescribed.validCandidate sel).datum
        (NonTrivalentValencyTwoRowEquiv.bridgeRow src sel
          (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest))
        (TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
          (Prescribed.validCandidate sel).right none) =
      {NonTrivalentValencyTwoRows.bridgeEdge sel (Prescribed.selectedRepresentative sel)} := by
  classical
  refine Finset.Subset.antisymm ?_ ?_
  · intro e he
    obtain ⟨⟨hSurv, hRow⟩, -⟩ := (StableSourceMatrix.mem_occurrences _ _ e).mp he
    exact Finset.mem_singleton.mpr (NonTrivalentValencyTwoRows.bridgeEdge_isolated src sel
      (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest) ⟨e, hSurv⟩ hRow)
  · intro e he
    rw [Finset.mem_singleton] at he
    subst he
    refine (StableSourceMatrix.mem_occurrences _ _ _).mpr ⟨⟨?_, rfl⟩, ?_⟩
    · exact NonTrivalentValencyTwoRows.bridgeEdge_survives src sel
        (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest)
    · exact BalancedGlobal.Candidate.newSourceEdge_target _ _

theorem matrix_outLabelling_facet_eq_zero (j : coordinate)
    (hj : j ≠ fd.labelling.targetEdge.symm contracted) :
    GluingDatum.LengthMatrixPresentation.matrix
        (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
          hZeroCoord hPosCoord hFacetZero src sel hOrd).presentation facet j = 0 := by
  classical
  rw [StableSourceMatrix.labelling_matrix_eq, outLabelling_row_symm_facet]
  have hTarget : (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
        hZeroCoord hPosCoord hFacetZero src sel hOrd).targetEdge j ≠
      TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
        (Prescribed.validCandidate sel).right none := by
    have hSymm : (colChart cover fd (contracted := contracted)).symm j = some ⟨j, hj⟩ :=
      Equiv.optionSubtypeNe_symm_of_ne hj
    show TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
        (Prescribed.validCandidate sel).right
        (Option.map _ ((colChart cover fd (contracted := contracted)).symm j)) ≠ _
    intro hBad
    have hNone := (TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
      (Prescribed.validCandidate sel).right).injective hBad
    rw [hSymm] at hNone
    simp at hNone
  unfold StableSourceMatrix.matrix
  rw [occurrences_bridgeRow_of_ne cover fd hc hab hOne hForest src sel _ hTarget,
    Finset.sum_empty]

theorem matrix_outLabelling_corner_pos :
    0 < GluingDatum.LengthMatrixPresentation.matrix
        (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
          hZeroCoord hPosCoord hFacetZero src sel hOrd).presentation facet
        (fd.labelling.targetEdge.symm contracted) := by
  classical
  rw [StableSourceMatrix.labelling_matrix_eq, outLabelling_row_symm_facet]
  have hSymm : (colChart cover fd (contracted := contracted)).symm
      (fd.labelling.targetEdge.symm contracted) = none :=
    Equiv.optionSubtypeNe_symm_self _
  have hTarget : (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
        hZeroCoord hPosCoord hFacetZero src sel hOrd).targetEdge
        (fd.labelling.targetEdge.symm contracted) =
      TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
        (Prescribed.validCandidate sel).right none := by
    show TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
        (Prescribed.validCandidate sel).right
        (Option.map _ ((colChart cover fd (contracted := contracted)).symm
          (fd.labelling.targetEdge.symm contracted))) = _
    rw [hSymm]
    rfl
  rw [hTarget]
  unfold StableSourceMatrix.matrix
  rw [occurrences_bridgeRow_new cover fd hc hab hOne hForest src sel, Finset.sum_singleton]
  exact div_pos one_pos (by exact_mod_cast (Prescribed.validCandidate sel).datum.sourceEdgeIndex_pos _)

/-! ### Nonnegativity, the common minor, and nonsingularity -/

theorem matrix_labelling_nonneg {targetX : CFGraph} {deg' : ℕ}
    {datum : GluingDatum targetX deg'} {C : Type*} [Fintype C] [DecidableEq C]
    (labelling : StableLengthMatrixLabelling datum C) (row column : C) :
    0 ≤ GluingDatum.LengthMatrixPresentation.matrix labelling.presentation row column := by
  classical
  rw [StableSourceMatrix.labelling_matrix_eq]
  unfold StableSourceMatrix.matrix
  refine Finset.sum_nonneg fun e _ ↦ ?_
  exact le_of_lt (div_pos one_pos (by exact_mod_cast datum.sourceEdgeIndex_pos e))

include hZeroCoord hPosCoord hFacetZero in
/-- The incoming vanishing row is supported on the contracted column. -/
theorem incoming_facet_eq_zero (j : coordinate)
    (hj : j ≠ fd.labelling.targetEdge.symm contracted) :
    GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation facet j = 0 :=
  NonTrivalentLinkMatrix.row_supported_of_zero_image
    (fun row column ↦ matrix_labelling_nonneg fd.labelling row column)
    hZeroCoord hPosCoord hFacetZero j hj

/-- **The common minor.**  The outgoing honest matrix agrees with the incoming
one in every row off the contracted column. -/
theorem agreeOffColumn_outLabelling :
    AgreeOffColumn (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation)
      (GluingDatum.LengthMatrixPresentation.matrix
        (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
          hZeroCoord hPosCoord hFacetZero src sel hOrd).presentation)
      (fd.labelling.targetEdge.symm contracted) := by
  intro i j hj
  by_cases hi : i = facet
  · rw [hi]
    rw [matrix_outLabelling_facet_eq_zero cover fd hc hab hOne hForest hNoReturn coordinates
      facet hRows hZeroCoord hPosCoord hFacetZero src sel hOrd j hj]
    exact incoming_facet_eq_zero cover fd coordinates facet hZeroCoord hPosCoord
      hFacetZero j hj
  · exact (matrix_outLabelling_eq_incoming cover fd hc hab hOne hForest hNoReturn coordinates
      facet hRows hZeroCoord hPosCoord hFacetZero src sel hOrd i j hi hj).symm

/-- **Nonsingularity of the outgoing matrix**, by the common-minor expansion
along the bridge row (`NonTrivalentLinkMatrix.det_ne_zero`). -/
theorem det_outLabelling_ne_zero :
    (GluingDatum.LengthMatrixPresentation.matrix
      (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
        hZeroCoord hPosCoord hFacetZero src sel hOrd).presentation).det ≠ 0 :=
  NonTrivalentLinkMatrix.det_ne_zero
    (agreeOffColumn_outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet
      hRows hZeroCoord hPosCoord hFacetZero src sel hOrd)
    (fun j hj ↦ incoming_facet_eq_zero cover fd coordinates facet hZeroCoord
      hPosCoord hFacetZero j hj)
    (fun j hj ↦ matrix_outLabelling_facet_eq_zero cover fd hc hab hOne hForest hNoReturn
      coordinates facet hRows hZeroCoord hPosCoord hFacetZero src sel hOrd j hj)
    fd.det_ne_zero
    (matrix_outLabelling_corner_pos cover fd hc hab hOne hForest hNoReturn coordinates facet
      hRows hZeroCoord hPosCoord hFacetZero src sel hOrd).ne'

/-! ### The outgoing target: connected, genus zero, and the same edge count -/

include fd in
theorem outgoing_targetConnected :
    graph_connected (TargetExpansion.graph (contract targetIn hab hOne) ⟨a, hab⟩
      (Prescribed.validCandidate sel).right) :=
  TargetExpansion.graph_connected (contract targetIn hab hOne) ⟨a, hab⟩ _
    (NonTrivalentUniqueFourValent.wall_target_connected cover fd hab hOne)

include fd in
theorem outgoing_targetGenus :
    genus (TargetExpansion.graph (contract targetIn hab hOne) ⟨a, hab⟩
      (Prescribed.validCandidate sel).right) = 0 :=
  (TargetExpansion.graph_genus (contract targetIn hab hOne) ⟨a, hab⟩ _).trans
    (NonTrivalentUniqueFourValent.wall_target_genus cover fd hab hOne)

/-- **The outgoing target has as many edges as the incoming one**: one target
occurrence contracts and one is regrown. -/
theorem outgoing_targetEdgeCard :
    (TargetExpansion.graph (contract targetIn hab hOne) ⟨a, hab⟩
      (Prescribed.validCandidate sel).right).edges.card = targetIn.edges.card :=
  (TargetExpansion.graph_edge_card (contract targetIn hab hOne) ⟨a, hab⟩ _).trans
    (WallDegeneration.edge_card_contract hab hOne).symm

/-! ### Trivalence of the outgoing candidate -/

include fd hForest in
/-- **The wall datum is trivalent away from the merged vertex**: there the
contraction changes no surviving star (`WallDegeneration.nonDanglingValency_sourceVertexMap`),
so the incoming cover's trivalence descends. -/
theorem wallDatum_trivalent_away (v : (contractDatum cover hc hab hOne).SourceVertex)
    (hv : v.1.1 ≠ (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)) :
    nonDanglingValency (contractDatum cover hc hab hOne) v ≤ 3 := by
  classical
  obtain ⟨w, hw⟩ := sourceVertexMap_surjective cover hc hab hOne v
  have hTarget : GraphContraction.fold targetIn hab w.1.1 = v.1.1 :=
    congrArg (fun z : (contractDatum cover hc hab hOne).SourceVertex ↦ z.1.1) hw
  have hwb : w.1.1 ≠ b := by
    intro hEq
    apply hv
    rw [← hTarget, hEq, GraphContraction.fold_self]
  have hwa : w.1.1 ≠ a := by
    intro hEq
    apply hv
    rw [← hTarget, hEq, GraphContraction.fold_a]
  rw [← hw, WallDegeneration.nonDanglingValency_sourceVertexMap cover
    (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne hForest)
    w hwa hwb]
  exact fd.trivalent w

/-- Every source vertex of the candidate over one side of the new target edge
is the endpoint vertex of its own sheet. -/
theorem eq_endpointVertex (sideValue : Bool)
    (v : (Prescribed.validCandidate sel).datum.SourceVertex)
    (hv : v.1.1 = (if sideValue then TargetExpansion.freshVertex (contract targetIn hab hOne)
      else TargetExpansion.oldVertex (contract targetIn hab hOne) ⟨a, hab⟩)) :
    NonTrivalentValencyTwoRows.endpointVertex sel sideValue v.1.2 = v := by
  exact ((Prescribed.validCandidate sel).datum.sourceEndpoint_eq_iff _ _ _).mpr
    ⟨hv.symm, rfl⟩

include src fd hForest hOrd in
/-- **The outgoing candidate is trivalent.**  Off the wall the incoming
trivalence descends through `ResolutionAwayFromWall`; at the anchor the two
endpoint classes have surviving valency three and the Configuration B
subdivision vertex has surviving valency two; at an ordinary block the census of
`NonTrivalentValencyTwoDescent` and `OrdinaryTrivalent` bound both sides. -/
theorem candidate_trivalent (v : (Prescribed.validCandidate sel).datum.SourceVertex) :
    nonDanglingValency (Prescribed.validCandidate sel).datum v ≤ 3 := by
  classical
  have hValid : (contractDatum cover hc hab hOne).Valid :=
    NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest
  have hGenus : genus (Prescribed.validCandidate sel).datum.sourceGraph =
      genus (contractDatum cover hc hab hOne).sourceGraph :=
    NonTrivalentValencyTwoRows.candidate_sourceGenus sel
  have hWall : ∀ sideValue : Bool,
      v.1.1 = (if sideValue then TargetExpansion.freshVertex (contract targetIn hab hOne)
        else TargetExpansion.oldVertex (contract targetIn hab hOne) ⟨a, hab⟩) →
      nonDanglingValency (Prescribed.validCandidate sel).datum v ≤ 3 := by
    intro sideValue hv
    rw [← eq_endpointVertex cover hc hab hOne sel sideValue v hv]
    by_cases hAnchor : ((contractDatum cover hc hab hOne).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).Rel anchorBlk.1 v.1.2
    · cases sideValue with
      | true =>
        have hRel : ((contractDatum cover hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
            (Prescribed.selectedRepresentative sel) v.1.2 :=
          (NonTrivalentValencyTwoRows.rep_wall_rel sel).symm.trans hAnchor
        rw [← NonTrivalentValencyTwoRows.endpointVertex_eq sel true
          (NonTrivalentValencyTwoRows.rep_wall_rel sel) hRel,
          NonTrivalentValencyTwoRows.nonDanglingValency_endpointVertex_true src sel hValid]
      | false =>
        obtain ⟨edge, hEdge, hFine⟩ :=
          NonTrivalentValencyTwoRows.exists_retained_rel src sel hAnchor
        have hEq := NonTrivalentValencyTwoRows.endpointVertex_eq sel false
          (occurrenceSheet_wall_rel edge) hFine
        rw [← hEq]
        by_cases hFirst : edge = Prescribed.firstSelected sel
        · rw [hFirst]
          exact le_of_eq (NonTrivalentValencyTwoRows.nonDanglingValency_endpointVertex_false
            src sel hValid)
        · rw [NonTrivalentValencyTwoRows.nonDanglingValency_extraEndpointVertex src sel hValid
            hEdge hFirst]
          omega
    · have hCard := NonTrivalentValencyTwoDescent.card_ordinaryStar_add
        (data := contractDatum cover hc hab hOne) (star := wallStar) (anchor := anchorBlk) v.1.2
      have hBound := hOrd v.1.2 hAnchor
      by_cases hDang : IsDangling (Prescribed.validCandidate sel).datum
          ((Prescribed.validCandidate sel).newSourceEdge v.1.2)
      · rw [NonTrivalentValencyTwoDescent.nonDanglingValency_endpointVertex_of_new_dangling
          sel hValid sideValue hAnchor hDang]
        cases sideValue <;> omega
      · have hNe := NonTrivalentValencyTwoDescent.ordinaryStar_card_ne_zero_of_new_survives
          sel hValid (!sideValue) hAnchor hDang
        rw [NonTrivalentValencyTwoDescent.nonDanglingValency_endpointVertex_of_new_survives
          sel hValid sideValue hAnchor hDang]
        cases sideValue <;> simp only [Bool.not_false, Bool.not_true] at hNe <;> omega
  rcases hcase : (v.1.1 : TargetExpansion.Vertex (contract targetIn hab hOne)) with place | u
  · by_cases hIsWall : place = (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)
    · exact hWall false (by rw [hcase, hIsWall]; rfl)
    · obtain ⟨old, hOld, hRet⟩ := ResolutionAwayFromWall.exists_retainedVertex_of_target
        (Prescribed.validCandidate sel) v place hIsWall hcase
      rw [← hRet, ResolutionAwayFromWall.nonDanglingValency_retainedVertex
        (Prescribed.validCandidate sel) hValid hGenus old (by rw [hOld]; exact hIsWall)]
      exact wallDatum_trivalent_away cover fd hc hab hOne hForest old
        (by rw [hOld]; exact hIsWall)
  · exact hWall true (by rw [hcase]; cases u; rfl)

/-! ### Path ends: the bridge row, and the reduction to the retained rows -/

include fd hForest hOrd in
/-- **`HasPathEnds` for the outgoing candidate reduces to the retained rows.**
Through `NonTrivalentValencyTwoRowEquiv.rowEquiv` every stable row of the
candidate is either the bridge row -- whose occurrence `h_1` has both ends at
the two trivalent endpoint classes, so it is a path end outright -- or the
retained row of a stable row of the wall datum.  Only the second half is left
open. -/
theorem hasPathEnds_of_retainedRowEnds
    (hRetained : ∀ r : StablePath (contractDatum cover hc hab hOne),
      ∃ (first : NonDanglingEdge (Prescribed.validCandidate sel).datum)
        (vertex : (Prescribed.validCandidate sel).datum.SourceVertex),
        first.stablePath = NonTrivalentValencyTwoDescent.retainedRow src sel
            (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest) r ∧
          IsPathEnd (Prescribed.validCandidate sel).datum first.1 vertex) :
    HasPathEnds (Prescribed.validCandidate sel).datum := by
  classical
  intro e
  have hValid : (contractDatum cover hc hab hOne).Valid :=
    NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest
  have hBack := (NonTrivalentValencyTwoRowEquiv.rowEquiv src sel hValid hOrd).symm_apply_apply
    e.stablePath
  cases hCase : NonTrivalentValencyTwoRowEquiv.rowEquiv src sel hValid hOrd e.stablePath with
  | none =>
    rw [hCase] at hBack
    have hRow : e.stablePath = NonTrivalentValencyTwoRowEquiv.bridgeRow src sel hValid := hBack.symm
    refine ⟨⟨NonTrivalentValencyTwoRows.bridgeEdge sel (Prescribed.selectedRepresentative sel),
      NonTrivalentValencyTwoRows.bridgeEdge_survives src sel hValid⟩,
      NonTrivalentValencyTwoRows.endpointVertex sel false
        (Prescribed.selectedRepresentative sel), hRow.symm, ?_, ?_⟩
    · exact NonTrivalentValencyTwoRows.bridgeEdge_incident sel false _
    · rw [NonTrivalentValencyTwoRows.nonDanglingValency_endpointVertex_false src sel hValid]
      omega
  | some r =>
    rw [hCase] at hBack
    have hRow : e.stablePath =
        NonTrivalentValencyTwoDescent.retainedRow src sel hValid r := hBack.symm
    obtain ⟨first, vertex, hFirst, hEnd⟩ := hRetained r
    exact ⟨first, vertex, hFirst.trans hRow.symm, hEnd⟩

/-! ### The outgoing full-dimensional presentation -/

/-- **The outgoing full-dimensional source presentation at a two-valent wall.**
Everything is derived except `HasPathEnds` of the outgoing candidate, which is
carried as an explicit hypothesis. -/
def outgoingFD (hPathEnds : HasPathEnds (Prescribed.validCandidate sel).datum) :
    FullDimensionalSourcePresentation (Prescribed.validCandidate sel).datum coordinate :=
  ofTypeChange fd
    (Prescribed.validCandidate_datum_valid sel
      (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest))
    (outgoing_targetConnected cover fd hc hab hOne sel)
    (outgoing_targetGenus cover fd hc hab hOne sel)
    (outgoing_targetEdgeCard cover hc hab hOne sel)
    ((NonTrivalentValencyTwoRows.candidate_sourceGenus sel).trans
      (genus_sourceGraph_contractDatum cover hc hab hOne hForest))
    (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
      hZeroCoord hPosCoord hFacetZero src sel hOrd)
    (det_outLabelling_ne_zero cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
      hZeroCoord hPosCoord hFacetZero src sel hOrd)
    (candidate_trivalent cover fd hc hab hOne hForest src sel hOrd)
    hPathEnds

@[simp] theorem outgoingFD_labelling
    (hPathEnds : HasPathEnds (Prescribed.validCandidate sel).datum) :
    (outgoingFD cover fd hc hab hOne hForest hNoReturn coordinates facet hRows hZeroCoord
        hPosCoord hFacetZero src sel hOrd hPathEnds).labelling =
      outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
        hZeroCoord hPosCoord hFacetZero src sel hOrd := rfl

end

/-! ## The link at a wall of the outer walk -/

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

/-- **The `2 + 2` sub-case discharge of `NoContractedReturn`.**  When neither
endpoint of the contracted target occurrence is a leaf of the incoming target
tree, change-minimality of the incoming cover forbids a stable path from
returning to the contracted column
(`StablePathFacetContraction.noContractedReturn_of_nonleaf`). -/
theorem noContractedReturn_of_two_two
    (hLeft : 2 ≤ (GluingDatum.incidentEdges (target := wd.coverTarget) wd.a).card)
    (hRight : 2 ≤ (GluingDatum.incidentEdges (target := wd.coverTarget) wd.b).card) :
    NoContractedReturn wd.cover wd.contracted :=
  noContractedReturn_of_nonleaf wd.cover wd.fullDim wd.hc hLeft hRight

/-- **The anchor of a two-valent wall, with no further hypothesis.**
`NonTrivalentValencyTwoRowEquiv.exists_rowEquiv_of_wall_metric` read at the
wall data of the outer walk. -/
theorem exists_anchor_of_wallData
    (wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    ∃ (anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
      (_src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk),
      (∀ sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          wallStar anchorBlk, (Prescribed.validCandidate sel).datum.Valid) ∧
        OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
          anchorBlk := by
  obtain ⟨anchorBlk, src, -, hSelection⟩ :=
    NonTrivalentValencyTwoRowEquiv.exists_rowEquiv_of_wall_metric wd.cover wd.fullDim wd.hc
      wd.hab wd.hOne (wd.hForest m) wallStar wd.coordinates (label m.base) wd.hRows
      wd.hZeroCoord wd.hPosCoord wd.hFacetZero
  obtain ⟨-, -, hOrd, -, -⟩ :=
    hSelection (NonTrivalentValencyTwoCandidate.Prescribed.Selection.default src)
  exact ⟨anchorBlk, src, fun sel ↦ (hSelection sel).1, hOrd⟩

variable (hNoReturn : NoContractedReturn wd.cover wd.contracted)
  {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hOrd : OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
    anchorBlk)
  (hPathEnds : HasPathEnds (Prescribed.validCandidate sel).datum)

/-- The outgoing presentation at the wall data of the outer walk. -/
def wallOutgoingFD : FullDimensionalSourcePresentation (Prescribed.validCandidate sel).datum
    coordinate :=
  outgoingFD wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m) hNoReturn wd.coordinates
    (label m.base) wd.hRows wd.hZeroCoord wd.hPosCoord wd.hFacetZero src sel hOrd hPathEnds

/-- **An inhabitant of `OuterWalk.TypeChangeLink`.**  At a two-valent
wall the base of the outgoing payload is the wall datum itself (no branch
gauge), the candidate is the Base II merge member, the presentation is
`wallOutgoingFD`, and the common minor is `agreeOffColumn_outLabelling`. -/
def typeChangeLink_of_receipts
    (tracks : Tracks (wallOutgoingFD m wd hNoReturn src sel hOrd hPathEnds) (graph.move m) label) :
    TypeChangeLink m wd where
  base := wd.wallDatum
  baseValid := wd.wallDatum_valid m
  candidate := Prescribed.validCandidate sel
  outgoingFD := wallOutgoingFD m wd hNoReturn src sel hOrd hPathEnds
  tracks := tracks
  agree := by
    have h := agreeOffColumn_outLabelling wd.cover wd.fullDim wd.hc wd.hab wd.hOne
      (wd.hForest m) hNoReturn wd.coordinates (label m.base) wd.hRows wd.hZeroCoord
      wd.hPosCoord wd.hFacetZero src sel hOrd
    rw [wd.targetEdge_symm_contracted] at h
    exact h

end

end Link

end DraismaVargas.LocalCases.NonTrivalentValencyTwoExit
