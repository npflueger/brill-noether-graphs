module

public import DraismaVargas.LocalCases.NonTrivalentValencyTwoExit
public import DraismaVargas.LocalCases.NonTrivalentValencyThreeRowDictionary

@[expose] public section

/-!
# The valency-three Type III exit: the outgoing full-dimensional presentation

Source: Vargas, Part II, Section 5.1 (the labelling convention at a
non-trivalent wall, and Lemma `lm:change-comb-type`: the wall matrix is the
common minor `A_{\varphi_0}` of the two incoming matrices) together with
Section 5.3, case `{v3-nd4}` (base tree `T_2`, the Type III member).  The
interface this module serves is `OuterWalk.TypeChangeLink`.

This is the valency-three sibling of `NonTrivalentValencyTwoExit`.  The Type III
candidate, its exact anchor stars, its ordinary-block census, its row
equivalence and its entrywise common-minor identity are in
`NonTrivalentValencyThreeCandidate`, `NonTrivalentValencyThreeRows`,
`NonTrivalentValencyThreeDescent`, `NonTrivalentValencyThreeRowEquiv` and
`NonTrivalentValencyThreeRowDictionary`.  This module builds the object
`OuterWalk.TypeChangeLink` asks for -- a `FullDimensionalSourcePresentation` of
the outgoing candidate **on the incoming chart index type**, with the
`AgreeOffColumn` statement against the incoming honest matrix.

## What is reused by import, and what is new

The generic infrastructure is `NonTrivalentValencyTwoExit`'s and is used
verbatim, not copied: `ofTypeChange` (the type-change constructor, which derives
`saturated`), `genus_sourceGraph_contractDatum` (the wall contraction preserves
the source genus, receipt-free), `reindexLabelling₂` / `matrix_reindexLabelling₂`
(two **independent** charts -- the new target occurrence goes into the vanishing
column `t_1`, the bridge row into the vanishing row `h_1 = label m.base`; a
single chart cannot satisfy `TypeChangeLink.agree`),
`rowChart` / `colChart` (the row chart absorbing exactly the transposition
`StablePathFacetContraction.wallRowIndex` builds into the wall datum's square
labelling), `wallLab`, `matrix_labelling_nonneg`, `incoming_facet_eq_zero` and
`wallDatum_trivalent_away`.

What is new here is everything that mentions the valency-three candidate.

## What is proved

* `outLabelling`, `matrix_outLabelling_eq_incoming`: the outgoing honest
  labelling in the incoming chart, and the entrywise common minor, obtained by
  composing `NonTrivalentValencyThreeRowDictionary.matrix_candidateLabelling`
  (which carries **no** ordinary-block trivalence hypothesis, unlike valency
  two) with `StablePathFacetContraction.matrix_wallLabelling`.
* `matrix_outLabelling_facet_eq_zero`, `matrix_outLabelling_corner_pos`: the
  bridge row vanishes off the contracted column and its corner entry is
  `1 / index(h_1) > 0`.  `NonTrivalentValencyThreeRows.bridgeEdge_isolated` says
  the bridge is alone in its stable class -- at valency three because **both**
  ends `A_u`, `A_v` of the anchor are trivalent -- and its only occurrence lies
  over the new target occurrence.
* `outLabelling_row_bridge` and `outLabelling_row_retained`: the **row half of
  the `Tracks.row_map` obligation**.  The bridge row occupies the vanishing row
  `facet` (= `label m.base` along the walk) and every retained row keeps the
  incoming chart coordinate of its own incoming row, so the label function does
  not change across the wall.  Only the dart/vertex half of `tracks` is left.
* `agreeOffColumn_outLabelling` and `det_outLabelling_ne_zero`: the
  `AgreeOffColumn` shape `TypeChangeLink.agree` asks for, and the outgoing
  nonsingularity by `NonTrivalentLinkMatrix.det_ne_zero`.
* `outgoing_targetConnected`, `outgoing_targetGenus`, `outgoing_targetEdgeCard`:
  the expanded wall target is connected of genus zero with as many edges as the
  incoming target.
* `ordinaryBlock_trivalent` and `candidate_trivalent`: **the outgoing candidate
  is trivalent.**  Away from the wall the incoming trivalence descends twice
  (`WallDegeneration.nonDanglingValency_sourceVertexMap`, then
  `ResolutionAwayFromWall.nonDanglingValency_retainedVertex`); at the anchor
  `nd(A_u) = nd(A_v) = 3`
  (`NonTrivalentValencyThreeRows.nonDanglingValency_endpointVertex`) while a
  singleton fine class over the anchor carries at most one survivor; at an
  ordinary block the census of `NonTrivalentValencyThreeDescent` gives
  `nd(C_u) ≤ 2` on the divalent side and `nd(B_v) = nd(B)` on the trivalent
  side, and `nd(B) ≤ 3` is
  `NonTrivalentAnchorValency.nonDanglingValency_wallBlock_le_three_of_threeStar`
  at the anchor's own `nd(A) = 4`.
* `hasPathEnds_of_retainedRowEnds`: `HasPathEnds` of the outgoing candidate
  reduces, through `NonTrivalentValencyThreeRowEquiv.rowEquiv`, to the retained
  rows -- the bridge row is a path end outright because `A_u` is trivalent.
* `outgoingFD`, `wallOutgoingFD`: the outgoing
  `FullDimensionalSourcePresentation` on `coordinate`.
* `exists_anchor_of_wallData`: the anchor block, its `ThreeBranchAnchor`
  classification, `DanglingEdgeNoGlue`, the wall datum's validity and the
  anchor's `nd = 4` at an actual three-valent wall of the outer walk, with no
  receipt (`NonTrivalentValencyThreeRowEquiv.exists_rowEquiv_of_wall_metric`
  read at `OuterWalk.WallData`).
* `noContractedReturn_of_valency_three`: **no no-return hypothesis is needed at
  valency three** --
  `NonTrivalentValencyThreeRowDictionary.noContractedReturn_of_threeStar`
  discharges it from the `{2,3}` valency split forced by a `ThreeStar`.
* `typeChangeLink_of_receipts`: an inhabitant of `OuterWalk.TypeChangeLink` at a
  three-valent wall, with `base` the **unchanged** wall datum (Type III lives
  over the wall datum: there is no branch gauge, unlike valency four).

## The hypotheses that remain explicit here

1. `hPathEnds : W4StableSource.HasPathEnds (Prescribed.validCandidate src hNoGlue
   hValid).datum`, reduced as far as `hasPathEnds_of_retainedRowEnds` allows:
   only the retained rows are left open.  The producers of `HasPathEnds` that
   go through `StableGraphIncidence.Equivalence` do not apply, since no such
   equivalence exists across a type change;
   `NonTrivalentValencyThreePathEnds.typeChangeLink_of_receipts'` removes this
   hypothesis.
2. `tracks : InteriorGraphTracking.Tracks (wallOutgoingFD ...) (graph.move m)
   label`: the dart-level dictionary between the candidate's stable graph and
   the Whitehead move of the tracked ambient graph.  Its `row_map` half is
   `outLabelling_row_bridge` / `outLabelling_row_retained` above; its `iso` half
   needs a branch-vertex/incidence dictionary across the wall contraction
   (`WallDegeneration.nonDanglingValency_sourceVertexMap` stops away from the
   wall), so `tracks` is carried as a hypothesis of
   `typeChangeLink_of_receipts` and the rest of the link is proved here.
   `NonTrivalentValencyThreeTracks` supplies that dictionary under the condition
   (H-III), which `NonTrivalentValencyThreeDispatcher` discharges.

Nothing here identifies a graph by a matrix.  No new structure is introduced,
so there is nothing to witness for non-vacuity beyond the definitions
themselves, each of which is applied.

## Used by

`OuterWalk.TypeChangeLink` (hence `OuterWalk.coneEntry_of_reaches` and its
`link` hypothesis) at Part II case `{v3-nd4}`.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyThreeExit

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.ThirdEquation
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.NonTrivalentValencyThreeAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyThreeCandidate

noncomputable section

/-! ### A small transport of source endpoints along the wall partition -/

theorem sourceEndpoint_eq_of_rel {target : CFGraph} {degree : ℕ} {wall : target.V}
    {dat : GluingDatum target degree} {x y : Fin degree}
    (hRel : (dat.vertexPartition wall).Rel x y) :
    dat.sourceEndpoint wall x = dat.sourceEndpoint wall y := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact hRel

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
  {wallStar : ThreeStar (contract targetIn hab hOne) ⟨a, hab⟩}
  {anchorBlk : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩}
  (src : ThreeBranchAnchor (contractDatum cover hc hab hOne) wallStar anchorBlk)
  (hNoGlue : DanglingEdgeNoGlue (contractDatum cover hc hab hOne))
  (hValid : (contractDatum cover hc hab hOne).Valid)

/-! ### The outgoing honest labelling on the incoming chart -/

/-- **The outgoing honest labelling.**  The two independent charts of
`NonTrivalentValencyTwoExit` applied to the valency-three candidate labelling
over the wall datum's own square labelling: the bridge row goes into the
vanishing row `facet`, the new target
occurrence into the vanishing column. -/
def outLabelling :
    StableLengthMatrixLabelling (Prescribed.validCandidate src hNoGlue hValid).datum
      coordinate :=
  NonTrivalentValencyTwoExit.reindexLabelling₂
    (NonTrivalentValencyTwoExit.rowChart cover fd facet (contracted := contracted))
    (NonTrivalentValencyTwoExit.colChart cover fd (contracted := contracted))
    (NonTrivalentValencyThreeRowEquiv.labelling src hNoGlue hValid
      (NonTrivalentValencyTwoExit.wallLab cover fd hc hab hOne hForest hNoReturn coordinates
        facet hRows hZeroCoord hPosCoord hFacetZero))

/-- **The common minor, entry by entry.**  In a retained row and a retained
column the outgoing matrix is the incoming matrix's own entry. -/
theorem matrix_outLabelling_eq_incoming (i j : coordinate) (hi : i ≠ facet)
    (hj : j ≠ fd.labelling.targetEdge.symm contracted) :
    GluingDatum.LengthMatrixPresentation.matrix
        (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
          hZeroCoord hPosCoord hFacetZero src hNoGlue hValid).presentation i j =
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
  set p := (NonTrivalentValencyTwoExit.wallLab cover fd hc hab hOne hForest hNoReturn
    coordinates facet hRows hZeroCoord hPosCoord hFacetZero).row.symm d with hpDef
  have hrow : (NonTrivalentValencyTwoExit.wallLab cover fd hc hab hOne hForest hNoReturn
      coordinates facet hRows hZeroCoord hPosCoord hFacetZero).row p = d :=
    Equiv.apply_symm_apply _ _
  have hi' : NonTrivalentValencyTwoExit.rowChart cover fd facet (contracted := contracted)
      (some d) = i := by
    rw [NonTrivalentValencyTwoExit.rowChart_some]
    exact Equiv.swap_apply_self _ _ i
  have hMid := NonTrivalentValencyTwoExit.matrix_reindexLabelling₂
    (NonTrivalentValencyTwoExit.rowChart cover fd facet (contracted := contracted))
    (NonTrivalentValencyTwoExit.colChart cover fd (contracted := contracted))
    (NonTrivalentValencyThreeRowEquiv.labelling src hNoGlue hValid
      (NonTrivalentValencyTwoExit.wallLab cover fd hc hab hOne hForest hNoReturn coordinates
        facet hRows hZeroCoord hPosCoord hFacetZero)) (some d) (some ⟨j, hj⟩)
  rw [hi'] at hMid
  have hPath : fd.labelling.row (incomingRow cover fd hc hab hOne
      (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne hForest)
      hForest p) = i := by
    have hval := NonTrivalentValencyTwoExit.wallLab_row_val cover fd hc hab hOne hForest
      hNoReturn coordinates facet hRows hZeroCoord hPosCoord hFacetZero p
    rw [hrow] at hval
    refine (Equiv.swap facet (fd.labelling.targetEdge.symm contracted)).injective ?_
    rw [← hval, Equiv.swap_comm]
  refine Eq.trans hMid ?_
  rw [← hrow]
  refine Eq.trans (NonTrivalentValencyThreeRowDictionary.matrix_candidateLabelling src hNoGlue
    hValid (NonTrivalentValencyTwoExit.wallLab cover fd hc hab hOne hForest hNoReturn
      coordinates facet hRows hZeroCoord hPosCoord hFacetZero) p ⟨j, hj⟩) ?_
  refine Eq.trans (matrix_wallLabelling cover fd hc hab hOne
    (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne hForest)
    hForest hNoReturn coordinates facet hRows hZeroCoord hPosCoord hFacetZero p ⟨j, hj⟩) ?_
  rw [hPath]

/-! ### The bridge row of the outgoing matrix -/

/-- **The bridge row of the candidate occupies the vanishing row of the
incoming chart.**  Along the outer walk `facet` is `label m.base`, so the new
bridge takes over the slot of the contracted row and the label function does not
change across the wall. -/
theorem outLabelling_row_bridge :
    (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
        hZeroCoord hPosCoord hFacetZero src hNoGlue hValid).row
      (NonTrivalentValencyThreeRowEquiv.bridgeRow src hNoGlue hValid) = facet := by
  show (NonTrivalentValencyTwoExit.rowChart cover fd facet (contracted := contracted))
      ((NonTrivalentValencyThreeRowEquiv.labelling src hNoGlue hValid
        (NonTrivalentValencyTwoExit.wallLab cover fd hc hab hOne hForest hNoReturn
          coordinates facet hRows hZeroCoord hPosCoord hFacetZero)).row
        (NonTrivalentValencyThreeRowEquiv.bridgeRow src hNoGlue hValid)) = facet
  rw [NonTrivalentValencyThreeRowEquiv.labelling_row_bridge src hNoGlue hValid]
  rfl

theorem outLabelling_row_symm_facet :
    (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
        hZeroCoord hPosCoord hFacetZero src hNoGlue hValid).row.symm facet =
      NonTrivalentValencyThreeRowEquiv.bridgeRow src hNoGlue hValid :=
  (Equiv.symm_apply_eq _).mpr
    (outLabelling_row_bridge cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
      hZeroCoord hPosCoord hFacetZero src hNoGlue hValid).symm

/-- **A retained row keeps the incoming chart coordinate of its own incoming
row.**  The row chart's transposition cancels exactly the one
`StablePathFacetContraction.wallRowIndex` builds in, so off the bridge the
outgoing chart labels agree with the incoming ones.  This is the row half of the
`InteriorGraphTracking.Tracks.row_map` obligation at a type change. -/
theorem outLabelling_row_retained (p : StablePath (contractDatum cover hc hab hOne)) :
    (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
        hZeroCoord hPosCoord hFacetZero src hNoGlue hValid).row
      (NonTrivalentValencyThreeDescent.retainedRow src hNoGlue hValid p) =
      fd.labelling.row (incomingRow cover fd hc hab hOne
        (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne hForest)
        hForest p) := by
  show (NonTrivalentValencyTwoExit.rowChart cover fd facet (contracted := contracted))
      ((NonTrivalentValencyThreeRowEquiv.labelling src hNoGlue hValid
        (NonTrivalentValencyTwoExit.wallLab cover fd hc hab hOne hForest hNoReturn
          coordinates facet hRows hZeroCoord hPosCoord hFacetZero)).row
        (NonTrivalentValencyThreeDescent.retainedRow src hNoGlue hValid p)) = _
  rw [NonTrivalentValencyThreeRowEquiv.labelling_row_retained src hNoGlue hValid _ p,
    NonTrivalentValencyTwoExit.rowChart_some,
    NonTrivalentValencyTwoExit.wallLab_row_val cover fd hc hab hOne hForest hNoReturn
      coordinates facet hRows hZeroCoord hPosCoord hFacetZero p,
    Equiv.swap_comm facet (fd.labelling.targetEdge.symm contracted)]
  exact Equiv.swap_apply_self _ _ _

/-- The only surviving occurrence of the bridge row lies over the new target
occurrence, so the bridge row of the outgoing matrix vanishes off the contracted
column. -/
theorem occurrences_bridgeRow_of_ne (t : (TargetExpansion.graph (contract targetIn hab hOne)
      ⟨a, hab⟩ (Prescribed.validCandidate src hNoGlue hValid).right).edges)
    (ht : t ≠ TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
      (Prescribed.validCandidate src hNoGlue hValid).right none) :
    StableSourceMatrix.occurrences (Prescribed.validCandidate src hNoGlue hValid).datum
      (NonTrivalentValencyThreeRowEquiv.bridgeRow src hNoGlue hValid) t = ∅ := by
  classical
  refine Finset.eq_empty_iff_forall_notMem.mpr ?_
  intro e he
  obtain ⟨⟨hSurv, hRow⟩, hTarget⟩ := (StableSourceMatrix.mem_occurrences _ t e).mp he
  have hEq := NonTrivalentValencyThreeRows.bridgeEdge_isolated src hNoGlue hValid ⟨e, hSurv⟩ hRow
  have hEq' : e = NonTrivalentValencyThreeRows.bridgeEdge src hNoGlue hValid
      (Prescribed.selectedRepresentative src) := hEq
  apply ht
  rw [← hTarget, hEq']
  exact BalancedGlobal.Candidate.newSourceEdge_target _ _

theorem occurrences_bridgeRow_new :
    StableSourceMatrix.occurrences (Prescribed.validCandidate src hNoGlue hValid).datum
        (NonTrivalentValencyThreeRowEquiv.bridgeRow src hNoGlue hValid)
        (TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
          (Prescribed.validCandidate src hNoGlue hValid).right none) =
      {NonTrivalentValencyThreeRows.bridgeEdge src hNoGlue hValid
        (Prescribed.selectedRepresentative src)} := by
  classical
  refine Finset.Subset.antisymm ?_ ?_
  · intro e he
    obtain ⟨⟨hSurv, hRow⟩, -⟩ := (StableSourceMatrix.mem_occurrences _ _ e).mp he
    exact Finset.mem_singleton.mpr
      (NonTrivalentValencyThreeRows.bridgeEdge_isolated src hNoGlue hValid ⟨e, hSurv⟩ hRow)
  · intro e he
    rw [Finset.mem_singleton] at he
    subst he
    refine (StableSourceMatrix.mem_occurrences _ _ _).mpr ⟨⟨?_, rfl⟩, ?_⟩
    · exact NonTrivalentValencyThreeRows.bridgeEdge_survives src hNoGlue hValid
    · exact BalancedGlobal.Candidate.newSourceEdge_target _ _

theorem matrix_outLabelling_facet_eq_zero (j : coordinate)
    (hj : j ≠ fd.labelling.targetEdge.symm contracted) :
    GluingDatum.LengthMatrixPresentation.matrix
        (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
          hZeroCoord hPosCoord hFacetZero src hNoGlue hValid).presentation facet j = 0 := by
  classical
  rw [StableSourceMatrix.labelling_matrix_eq, outLabelling_row_symm_facet]
  have hTarget : (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
        hZeroCoord hPosCoord hFacetZero src hNoGlue hValid).targetEdge j ≠
      TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
        (Prescribed.validCandidate src hNoGlue hValid).right none := by
    have hSymm : (NonTrivalentValencyTwoExit.colChart cover fd (contracted := contracted)).symm
        j = some ⟨j, hj⟩ := Equiv.optionSubtypeNe_symm_of_ne hj
    show TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
        (Prescribed.validCandidate src hNoGlue hValid).right
        (Option.map _ ((NonTrivalentValencyTwoExit.colChart cover fd
          (contracted := contracted)).symm j)) ≠ _
    intro hBad
    have hNone := (TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
      (Prescribed.validCandidate src hNoGlue hValid).right).injective hBad
    rw [hSymm] at hNone
    simp at hNone
  unfold StableSourceMatrix.matrix
  rw [occurrences_bridgeRow_of_ne cover hc hab hOne src hNoGlue hValid _ hTarget,
    Finset.sum_empty]

theorem matrix_outLabelling_corner_pos :
    0 < GluingDatum.LengthMatrixPresentation.matrix
        (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
          hZeroCoord hPosCoord hFacetZero src hNoGlue hValid).presentation facet
        (fd.labelling.targetEdge.symm contracted) := by
  classical
  rw [StableSourceMatrix.labelling_matrix_eq, outLabelling_row_symm_facet]
  have hSymm : (NonTrivalentValencyTwoExit.colChart cover fd (contracted := contracted)).symm
      (fd.labelling.targetEdge.symm contracted) = none :=
    Equiv.optionSubtypeNe_symm_self _
  have hTarget : (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
        hZeroCoord hPosCoord hFacetZero src hNoGlue hValid).targetEdge
        (fd.labelling.targetEdge.symm contracted) =
      TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
        (Prescribed.validCandidate src hNoGlue hValid).right none := by
    show TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
        (Prescribed.validCandidate src hNoGlue hValid).right
        (Option.map _ ((NonTrivalentValencyTwoExit.colChart cover fd
          (contracted := contracted)).symm (fd.labelling.targetEdge.symm contracted))) = _
    rw [hSymm]
    rfl
  rw [hTarget]
  unfold StableSourceMatrix.matrix
  rw [occurrences_bridgeRow_new cover hc hab hOne src hNoGlue hValid, Finset.sum_singleton]
  exact div_pos one_pos
    (by exact_mod_cast (Prescribed.validCandidate src hNoGlue hValid).datum.sourceEdgeIndex_pos _)

/-! ### The common minor and nonsingularity -/

/-- **The common minor.**  The outgoing honest matrix agrees with the incoming
one in every row off the contracted column. -/
theorem agreeOffColumn_outLabelling :
    AgreeOffColumn (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation)
      (GluingDatum.LengthMatrixPresentation.matrix
        (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
          hZeroCoord hPosCoord hFacetZero src hNoGlue hValid).presentation)
      (fd.labelling.targetEdge.symm contracted) := by
  intro i j hj
  by_cases hi : i = facet
  · rw [hi]
    rw [matrix_outLabelling_facet_eq_zero cover fd hc hab hOne hForest hNoReturn coordinates
      facet hRows hZeroCoord hPosCoord hFacetZero src hNoGlue hValid j hj]
    exact NonTrivalentValencyTwoExit.incoming_facet_eq_zero cover fd coordinates facet
      hZeroCoord hPosCoord hFacetZero j hj
  · exact (matrix_outLabelling_eq_incoming cover fd hc hab hOne hForest hNoReturn coordinates
      facet hRows hZeroCoord hPosCoord hFacetZero src hNoGlue hValid i j hi hj).symm

/-- **Nonsingularity of the outgoing matrix**, by the common-minor expansion
along the bridge row (`NonTrivalentLinkMatrix.det_ne_zero`). -/
theorem det_outLabelling_ne_zero :
    (GluingDatum.LengthMatrixPresentation.matrix
      (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
        hZeroCoord hPosCoord hFacetZero src hNoGlue hValid).presentation).det ≠ 0 :=
  NonTrivalentLinkMatrix.det_ne_zero
    (agreeOffColumn_outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet
      hRows hZeroCoord hPosCoord hFacetZero src hNoGlue hValid)
    (fun j hj ↦ NonTrivalentValencyTwoExit.incoming_facet_eq_zero cover fd coordinates facet
      hZeroCoord hPosCoord hFacetZero j hj)
    (fun j hj ↦ matrix_outLabelling_facet_eq_zero cover fd hc hab hOne hForest hNoReturn
      coordinates facet hRows hZeroCoord hPosCoord hFacetZero src hNoGlue hValid j hj)
    fd.det_ne_zero
    (matrix_outLabelling_corner_pos cover fd hc hab hOne hForest hNoReturn coordinates facet
      hRows hZeroCoord hPosCoord hFacetZero src hNoGlue hValid).ne'

/-! ### The outgoing target: connected, genus zero, and the same edge count -/

include fd in
theorem outgoing_targetConnected :
    graph_connected (TargetExpansion.graph (contract targetIn hab hOne) ⟨a, hab⟩
      (Prescribed.validCandidate src hNoGlue hValid).right) :=
  TargetExpansion.graph_connected (contract targetIn hab hOne) ⟨a, hab⟩ _
    (NonTrivalentUniqueFourValent.wall_target_connected cover fd hab hOne)

include fd in
theorem outgoing_targetGenus :
    genus (TargetExpansion.graph (contract targetIn hab hOne) ⟨a, hab⟩
      (Prescribed.validCandidate src hNoGlue hValid).right) = 0 :=
  (TargetExpansion.graph_genus (contract targetIn hab hOne) ⟨a, hab⟩ _).trans
    (NonTrivalentUniqueFourValent.wall_target_genus cover fd hab hOne)

/-- **The outgoing target has as many edges as the incoming one**: one target
occurrence contracts and one is regrown. -/
theorem outgoing_targetEdgeCard :
    (TargetExpansion.graph (contract targetIn hab hOne) ⟨a, hab⟩
      (Prescribed.validCandidate src hNoGlue hValid).right).edges.card =
      targetIn.edges.card :=
  (TargetExpansion.graph_edge_card (contract targetIn hab hOne) ⟨a, hab⟩ _).trans
    (WallDegeneration.edge_card_contract hab hOne).symm

/-! ### Trivalence of the outgoing candidate -/

/-- Every source vertex of the candidate over one side of the new target edge is
the endpoint vertex of its own sheet. -/
theorem eq_endpointVertex (sideValue : Bool)
    (v : (Prescribed.validCandidate src hNoGlue hValid).datum.SourceVertex)
    (hv : v.1.1 = (if sideValue then TargetExpansion.freshVertex (contract targetIn hab hOne)
      else TargetExpansion.oldVertex (contract targetIn hab hOne) ⟨a, hab⟩)) :
    NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid sideValue v.1.2 = v :=
  ((Prescribed.validCandidate src hNoGlue hValid).datum.sourceEndpoint_eq_iff _ _ _).mpr
    ⟨hv.symm, rfl⟩

include fd hForest src in
/-- **The wall datum is trivalent at every ordinary block.**  The non-anchor
bound of `NonTrivalentAnchorValency` at a three-valent wall, read at the source
endpoint of a sheet
rather than at a canonical wall block. -/
theorem ordinaryBlock_trivalent (y : Fin deg)
    (hy : ¬ ((contractDatum cover hc hab hOne).vertexPartition
      (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).Rel anchorBlk.1 y) :
    nonDanglingValency (contractDatum cover hc hab hOne)
      ((contractDatum cover hc hab hOne).sourceEndpoint ⟨a, hab⟩ y) ≤ 3 := by
  classical
  have hRepr : ((contractDatum cover hc hab hOne).vertexPartition
      (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).Rel y
        (((contractDatum cover hc hab hOne).vertexPartition ⟨a, hab⟩).repr y) :=
    ((contractDatum cover hc hab hOne).vertexPartition ⟨a, hab⟩).rel_repr_right y
  have hEq : (contractDatum cover hc hab hOne).sourceEndpoint ⟨a, hab⟩
      (((contractDatum cover hc hab hOne).vertexPartition ⟨a, hab⟩).repr y) =
        (contractDatum cover hc hab hOne).sourceEndpoint ⟨a, hab⟩ y :=
    sourceEndpoint_eq_of_rel hRepr.symm
  rw [← hEq]
  exact NonTrivalentAnchorValency.nonDanglingValency_wallBlock_le_three_of_threeStar cover fd
    hc hab hOne wallStar hForest anchorBlk
    (NonTrivalentValencyThreeRows.nonDanglingValency_anchor src)
    (WallBlock.ofSheet (contractDatum cover hc hab hOne) ⟨a, hab⟩ y)
    (fun h ↦ hy (h.trans hRepr.symm))

include fd hForest in
/-- **The outgoing candidate is trivalent.**  Off the wall the incoming
trivalence descends through `ResolutionAwayFromWall`; at the anchor both
endpoint classes `A_u`, `A_v` are trivalent and every other fine class over the
anchor is a singleton carrying at most one survivor; at an ordinary block the
census of `NonTrivalentValencyThreeDescent` gives `nd(C_u) ≤ 2` and
`nd(B_v) = nd(B) ≤ 3`. -/
theorem candidate_trivalent
    (v : (Prescribed.validCandidate src hNoGlue hValid).datum.SourceVertex) :
    nonDanglingValency (Prescribed.validCandidate src hNoGlue hValid).datum v ≤ 3 := by
  classical
  have hGenus : genus (Prescribed.validCandidate src hNoGlue hValid).datum.sourceGraph =
      genus (contractDatum cover hc hab hOne).sourceGraph :=
    NonTrivalentValencyThreeRows.candidate_sourceGenus src hNoGlue hValid
  have hWall : ∀ sideValue : Bool,
      v.1.1 = (if sideValue then TargetExpansion.freshVertex (contract targetIn hab hOne)
        else TargetExpansion.oldVertex (contract targetIn hab hOne) ⟨a, hab⟩) →
      nonDanglingValency (Prescribed.validCandidate src hNoGlue hValid).datum v ≤ 3 := by
    intro sideValue hv
    rw [← eq_endpointVertex cover hc hab hOne src hNoGlue hValid sideValue v hv]
    by_cases hAnchor : ((contractDatum cover hc hab hOne).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).Rel anchorBlk.1 v.1.2
    · cases sideValue with
      | true =>
        have hRel : ((contractDatum cover hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
            (Prescribed.selectedRepresentative src) v.1.2 :=
          (NonTrivalentValencyThreeRows.rep_wall_rel src).symm.trans hAnchor
        rw [← NonTrivalentValencyThreeRows.endpointVertex_eq src hNoGlue hValid true
          (NonTrivalentValencyThreeRows.rep_wall_rel src) hRel,
          NonTrivalentValencyThreeRows.nonDanglingValency_endpointVertex src hNoGlue hValid true]
      | false =>
        by_cases hFine : (Prescribed.finePartition src).Rel
            (Prescribed.selectedRepresentative src) v.1.2
        · rw [← NonTrivalentValencyThreeRows.endpointVertex_eq src hNoGlue hValid false
            (NonTrivalentValencyThreeRows.rep_wall_rel src) hFine,
            NonTrivalentValencyThreeRows.nonDanglingValency_endpointVertex src hNoGlue hValid
              false]
        · rcases Prescribed.finePartition_rel_or_singleton src v.1.2 hAnchor with hRel | hSing
          · exact absurd hRel hFine
          · have hCard := Finset.card_le_card
              (NonTrivalentValencyThreeRows.nonDanglingIncident_singleton_subset src hNoGlue
                hValid hAnchor hSing hFine)
            rw [card_nonDanglingIncident, Finset.card_singleton] at hCard
            omega
    · cases sideValue with
      | false =>
        have hCard := Finset.card_le_card
          (NonTrivalentValencyThreeDescent.nonDanglingIncident_endpointVertex_false_subset_ordinary
            src hNoGlue hValid hAnchor)
        rw [card_nonDanglingIncident] at hCard
        have hPair := Finset.card_insert_le
          ((Prescribed.validCandidate src hNoGlue hValid).oldSourceEdge
            (NonTrivalentValencyThreeDescent.doubledOccurrence src v.1.2))
          ({(Prescribed.validCandidate src hNoGlue hValid).newSourceEdge v.1.2} :
            Finset (Prescribed.validCandidate src hNoGlue hValid).datum.SourceEdge)
        rw [Finset.card_singleton] at hPair
        omega
      | true =>
        rw [NonTrivalentValencyThreeDescent.nonDanglingValency_endpointVertex_true_ordinary
          src hNoGlue hValid hAnchor]
        exact ordinaryBlock_trivalent cover fd hc hab hOne hForest src v.1.2 hAnchor
  rcases hcase : (v.1.1 : TargetExpansion.Vertex (contract targetIn hab hOne)) with place | u
  · by_cases hIsWall : place = (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)
    · exact hWall false (by rw [hcase, hIsWall]; rfl)
    · obtain ⟨old, hOld, hRet⟩ := ResolutionAwayFromWall.exists_retainedVertex_of_target
        (Prescribed.validCandidate src hNoGlue hValid) v place hIsWall hcase
      rw [← hRet, ResolutionAwayFromWall.nonDanglingValency_retainedVertex
        (Prescribed.validCandidate src hNoGlue hValid) hValid hGenus old
        (by rw [hOld]; exact hIsWall)]
      exact NonTrivalentValencyTwoExit.wallDatum_trivalent_away cover fd hc hab hOne hForest old
        (by rw [hOld]; exact hIsWall)
  · exact hWall true (by rw [hcase]; cases u; rfl)

/-! ### Path ends: the bridge row, and the reduction to the retained rows -/

/-- **`HasPathEnds` for the outgoing candidate reduces to the retained rows.**
Through `NonTrivalentValencyThreeRowEquiv.rowEquiv` every stable row of the
candidate is either the bridge row -- whose occurrence `h_1` has both ends at
the two trivalent endpoint classes, so it is a path end outright -- or the
retained row of a stable row of the wall datum.  Only the second half is left
as a hypothesis. -/
theorem hasPathEnds_of_retainedRowEnds
    (hRetained : ∀ r : StablePath (contractDatum cover hc hab hOne),
      ∃ (first : NonDanglingEdge (Prescribed.validCandidate src hNoGlue hValid).datum)
        (vertex : (Prescribed.validCandidate src hNoGlue hValid).datum.SourceVertex),
        first.stablePath =
            NonTrivalentValencyThreeDescent.retainedRow src hNoGlue hValid r ∧
          IsPathEnd (Prescribed.validCandidate src hNoGlue hValid).datum first.1 vertex) :
    HasPathEnds (Prescribed.validCandidate src hNoGlue hValid).datum := by
  classical
  intro e
  have hBack :=
    (NonTrivalentValencyThreeRowEquiv.rowEquiv src hNoGlue hValid).symm_apply_apply e.stablePath
  cases hCase :
      NonTrivalentValencyThreeRowEquiv.rowEquiv src hNoGlue hValid e.stablePath with
  | none =>
    rw [hCase] at hBack
    have hRow : e.stablePath =
        NonTrivalentValencyThreeRowEquiv.bridgeRow src hNoGlue hValid := hBack.symm
    refine ⟨⟨NonTrivalentValencyThreeRows.bridgeEdge src hNoGlue hValid
        (Prescribed.selectedRepresentative src),
      NonTrivalentValencyThreeRows.bridgeEdge_survives src hNoGlue hValid⟩,
      NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid false
        (Prescribed.selectedRepresentative src), hRow.symm, ?_, ?_⟩
    · exact NonTrivalentValencyThreeRows.bridgeEdge_incident src hNoGlue hValid false _
    · rw [NonTrivalentValencyThreeRows.nonDanglingValency_endpointVertex src hNoGlue hValid false]
      omega
  | some r =>
    rw [hCase] at hBack
    have hRow : e.stablePath =
        NonTrivalentValencyThreeDescent.retainedRow src hNoGlue hValid r := hBack.symm
    obtain ⟨first, vertex, hFirst, hEnd⟩ := hRetained r
    exact ⟨first, vertex, hFirst.trans hRow.symm, hEnd⟩

/-! ### The outgoing full-dimensional presentation -/

/-- **The outgoing full-dimensional source presentation at a three-valent
wall.**  Everything is derived except `HasPathEnds` of the outgoing candidate,
which is carried as an explicit hypothesis. -/
def outgoingFD
    (hPathEnds : HasPathEnds (Prescribed.validCandidate src hNoGlue hValid).datum) :
    FullDimensionalSourcePresentation (Prescribed.validCandidate src hNoGlue hValid).datum
      coordinate :=
  NonTrivalentValencyTwoExit.ofTypeChange fd
    (Prescribed.validCandidate_datum_valid src hNoGlue hValid)
    (outgoing_targetConnected cover fd hc hab hOne src hNoGlue hValid)
    (outgoing_targetGenus cover fd hc hab hOne src hNoGlue hValid)
    (outgoing_targetEdgeCard cover hc hab hOne src hNoGlue hValid)
    ((NonTrivalentValencyThreeRows.candidate_sourceGenus src hNoGlue hValid).trans
      (NonTrivalentValencyTwoExit.genus_sourceGraph_contractDatum cover hc hab hOne hForest))
    (outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows hZeroCoord
      hPosCoord hFacetZero src hNoGlue hValid)
    (det_outLabelling_ne_zero cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
      hZeroCoord hPosCoord hFacetZero src hNoGlue hValid)
    (candidate_trivalent cover fd hc hab hOne hForest src hNoGlue hValid)
    hPathEnds

@[simp] theorem outgoingFD_labelling
    (hPathEnds : HasPathEnds (Prescribed.validCandidate src hNoGlue hValid).datum) :
    (outgoingFD cover fd hc hab hOne hForest hNoReturn coordinates facet hRows hZeroCoord
        hPosCoord hFacetZero src hNoGlue hValid hPathEnds).labelling =
      outLabelling cover fd hc hab hOne hForest hNoReturn coordinates facet hRows
        hZeroCoord hPosCoord hFacetZero src hNoGlue hValid := rfl

end

/-! ## The link at a three-valent wall of the outer walk -/

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

/-- **`NoContractedReturn` needs no receipt at a three-valent wall.**
A `ThreeStar` at the merged vertex forces the target-valency split `{2, 3}`, so
neither endpoint of the contracted occurrence is a leaf and
`StablePathFacetContraction.noContractedReturn_of_nonleaf` applies.  This is the
valency-three replacement for `NonTrivalentValencyTwoExit.noContractedReturn_of_two_two`,
and unlike it there is no residual sub-case. -/
theorem noContractedReturn_of_valency_three
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    NoContractedReturn wd.cover wd.contracted :=
  NonTrivalentValencyThreeRowDictionary.noContractedReturn_of_threeStar wd.cover wd.fullDim
    wd.hc wd.hab wd.hOne wallStar

/-- **The anchor of a three-valent wall, with no receipt.**
`NonTrivalentValencyThreeRowEquiv.exists_rowEquiv_of_wall_metric` read at the
wall data of the outer walk: the anchor block, its
`ThreeBranchAnchor` classification, `DanglingEdgeNoGlue`, the wall datum's
validity, the anchor's surviving valency four and the candidate's validity. -/
theorem exists_anchor_of_wallData
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    ∃ (anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
      (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
        anchorBlk)
      (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
      (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid),
      nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            ⟨wd.a, wd.hab⟩ anchorBlk) = 4 ∧
        (Prescribed.validCandidate src hNoGlue hValid).datum.Valid := by
  obtain ⟨anchorBlk, src, hNoGlue, hValid, hNd, hCandValid, -, -, -⟩ :=
    NonTrivalentValencyThreeRowEquiv.exists_rowEquiv_of_wall_metric wd.cover wd.fullDim wd.hc
      wd.hab wd.hOne (wd.hForest m) wallStar wd.coordinates (label m.base) wd.hRows
      wd.hZeroCoord wd.hPosCoord wd.hFacetZero
  exact ⟨anchorBlk, src, hNoGlue, hValid, hNd, hCandValid⟩

variable {wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
  (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)
  (hPathEnds : HasPathEnds (Prescribed.validCandidate src hNoGlue hValid).datum)

/-- The outgoing presentation at the wall data of the outer walk.  No
`NoContractedReturn` hypothesis: it is discharged from `wallStar`. -/
def wallOutgoingFD :
    FullDimensionalSourcePresentation (Prescribed.validCandidate src hNoGlue hValid).datum
      coordinate :=
  outgoingFD wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m)
    (noContractedReturn_of_valency_three m wd wallStar) wd.coordinates (label m.base) wd.hRows
    wd.hZeroCoord wd.hPosCoord wd.hFacetZero src hNoGlue hValid hPathEnds

/-- **The type-change link at a three-valent wall.**  Type III lives over the
**unchanged** wall datum -- there is no branch gauge, unlike valency four -- so
`base` is `wd.wallDatum` and `baseValid` is the wall datum's own validity.  The
candidate is the Type III member of `NonTrivalentValencyThreeCandidate`, the
presentation is `wallOutgoingFD` and the common minor is
`agreeOffColumn_outLabelling`.  Exactly two receipts are hypotheses:
`hPathEnds` and `tracks` (the dart dictionary). -/
def typeChangeLink_of_receipts
    (tracks : Tracks (wallOutgoingFD m wd src hNoGlue hValid hPathEnds) (graph.move m) label) :
    TypeChangeLink m wd where
  base := wd.wallDatum
  baseValid := wd.wallDatum_valid m
  candidate := Prescribed.validCandidate src hNoGlue hValid
  outgoingFD := wallOutgoingFD m wd src hNoGlue hValid hPathEnds
  tracks := tracks
  agree := by
    have h := agreeOffColumn_outLabelling wd.cover wd.fullDim wd.hc wd.hab wd.hOne
      (wd.hForest m) (noContractedReturn_of_valency_three m wd wallStar) wd.coordinates
      (label m.base) wd.hRows wd.hZeroCoord wd.hPosCoord wd.hFacetZero src hNoGlue hValid
    rw [wd.targetEdge_symm_contracted] at h
    exact h

end

end Link

end DraismaVargas.LocalCases.NonTrivalentValencyThreeExit
