import DraismaVargas.LocalCases.NonTrivalentValencyTwoExit
import DraismaVargas.LocalCases.NonTrivalentValencyFourRetainedInjective
import DraismaVargas.LocalCases.WallDatumPathEnds
import DraismaVargas.LocalCases.StableGraphIncidence
import DraismaVargas.LocalCases.SheetRelabelIncidence

/-!
# The valency-four `K = 0` exit: the outgoing full-dimensional presentation

Source: Vargas, Part II (arXiv:2609.09109), Section 5.1 (the labelling
convention at a non-trivalent wall, and Lemma `lm:change-comb-type`: the wall
matrix is the common minor `A_{\varphi_0}` of the two incoming matrices)
together with Section 5.2 (Case `{v4-nd4}`, the `K = 0` resolution of the unique
four-valent vertex `A` into the two trivalent endpoints `A_1^{(q)}`,
`A_2^{(q)}` joined by the contracting edge `h_1^{(q)}`).  The consumer
interface is `OuterWalk.TypeChangeLink`.

This is the valency-four sibling of `NonTrivalentValencyTwoExit` and
`NonTrivalentValencyThreeExit`.  The modules `NonTrivalentValencyFourRowEquiv`,
`NonTrivalentValencyFourRowDictionary`, `NonTrivalentValencyFourRowEquivFinal`
and `NonTrivalentValencyFourRetainedInjective` construct the `K = 0` candidate
over the block-preserving branch gauge of the wall datum, its exact endpoint
stars, its row equivalence and its entrywise common-minor identity.  This file
builds the object `OuterWalk.TypeChangeLink` asks for -- a
`FullDimensionalSourcePresentation` of the outgoing candidate **on the incoming
chart index type**, with the `AgreeOffColumn` statement against the incoming
honest matrix.

## What is reused by import, and what is new

The generic infrastructure is `NonTrivalentValencyTwoExit`'s and is used
verbatim, not copied: `ofTypeChange`, `genus_sourceGraph_contractDatum`,
`reindexLabelling₂` / `matrix_reindexLabelling₂` (two **independent** charts --
the new target occurrence goes into the vanishing column `t_1`, the bridge row
into the vanishing row `h_1 = label m.base`; a single chart cannot satisfy
`TypeChangeLink.agree`, as `NonTrivalentValencyTwoExit` explains), `rowChart` /
`colChart`, `wallLab`, `matrix_labelling_nonneg`, `incoming_facet_eq_zero` and
`wallDatum_trivalent_away`.  Everything specific to valency four comes from the
four modules named above.

The one structural difference from valency two and three is that the `K = 0`
candidate does **not** live over the wall datum but over its block-preserving
branch gauge `NonTrivalentValencyFourKZero.PrescribedPairing.gaugedData`, so the
wall datum's own square labelling has to be transported across the gauge before
it can index the candidate.  `NonTrivalentValencyFourRowDictionary.relabelLabelling`
does that, and `NonTrivalentValencyFourRowDictionary.candidateLabelling` is the
`Option`-indexed labelling this file re-indexes with two charts.

## What is proved here

* `outLabelling`, `matrix_outLabelling_eq_incoming`: the outgoing honest
  labelling in the incoming chart, and the entrywise common minor, obtained by
  composing `NonTrivalentValencyFourRowDictionary.matrix_candidateLabelling`
  (with the unconditional row equivalence
  `NonTrivalentValencyFourRetainedInjective.rowEquiv_of_single_row` and its
  compatibility) with
  `StablePathFacetContraction.matrix_wallLabelling`.
* `outLabelling_row_bridge`, `outLabelling_row_retained`: the **row half of the
  `InteriorGraphTracking.Tracks.row_map` obligation**.  The bridge row occupies
  the vanishing row `facet` (= `label m.base` along the walk) and a retained
  row keeps the incoming chart coordinate of its own incoming row, through the
  sheet gauge's stable-row equivalence.
* `matrix_outLabelling_facet_eq_zero`, `matrix_outLabelling_corner_pos`: the
  bridge row vanishes off the contracted column and its corner entry is
  `1 / index(h_1) > 0`.  `NonTrivalentValencyFourDictionary.bridgeEdge_isolated`
  says the bridge is alone in its stable class -- at valency four because
  **both** `K = 0` endpoints are trivalent.
* `agreeOffColumn_outLabelling` and `det_outLabelling_ne_zero`: the
  `AgreeOffColumn` shape `TypeChangeLink.agree` asks for, and the outgoing
  nonsingularity by `NonTrivalentLinkMatrix.det_ne_zero`.
* `outgoing_targetConnected`, `outgoing_targetGenus`, `outgoing_targetEdgeCard`:
  the expanded wall target is connected of genus zero with as many edges as the
  incoming target.
* `gauged_trivalent_away`, `card_side_le_two`, `nonDanglingValency_ret_le`,
  `nonDanglingValency_fine_le`, `nonDanglingValency_block_le` and
  **`candidate_trivalent`**: the outgoing candidate is trivalent.  Away from the
  wall the incoming trivalence descends across the sheet gauge
  (`SheetRelabelStable.nonDanglingValency_map` and
  `NonTrivalentValencyTwoExit.wallDatum_trivalent_away`) and then through
  `ResolutionAwayFromWall`; at the anchor both `K = 0` endpoint classes have
  `nd = 3` (`NonTrivalentValencyFourRowDictionary`) while a fine class over the
  anchor outside the selected block is a singleton carrying at most one
  survivor; at a non-anchor block the retaining endpoint injects into the
  block's surviving star in the gauged datum
  (`NonTrivalentValencyFourRowEquiv.nonDanglingIncident_ret_dichotomy`) and a
  fine endpoint into that star's fine side together with the block's new
  occurrence, whose size is bounded by
  `NonTrivalentValencyFourRowEquivFinal.eq_of_three_on_side` (a `2 + 2` pairing
  has two labels per side).
* `hasPathEnds_of_retainedRowEnds`: `HasPathEnds` of the outgoing candidate
  reduces, through the row equivalence, to the retained rows -- the bridge row
  is a path end outright because both its ends are trivalent.

## What is not proved here

The retained-row half of `HasPathEnds`, the outgoing presentation itself and
the `OuterWalk.TypeChangeLink` inhabitant: those are in
`NonTrivalentValencyFourExitLink`.  Nothing here identifies a graph by a
matrix, and no new structure is introduced, so there is nothing to witness for
non-vacuity beyond the definitions themselves, each of which is applied.

## Consumers

`NonTrivalentValencyFourExitLink`, and through it `OuterWalk.TypeChangeLink`
(hence the `link` hypothesis of `OuterWalk.coneEntry_of_reaches`) at Part II
Case `{v4-nd4}`.
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

/-! ### A small transport of source endpoints along the wall partition -/

theorem sourceEndpoint_eq_of_rel {target : CFGraph} {degree : ℕ} {wall : target.V}
    {dat : GluingDatum target degree} {x y : Fin degree}
    (hRel : (dat.vertexPartition wall).Rel x y) :
    dat.sourceEndpoint wall x = dat.sourceEndpoint wall y := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact hRel

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

/-! ### The outgoing honest labelling on the incoming chart -/

/-- **The outgoing honest labelling.** -/
def outLabelling :
    StableLengthMatrixLabelling (wCand).datum coordinate :=
  NonTrivalentValencyTwoExit.reindexLabelling₂
    (NonTrivalentValencyTwoExit.rowChart cover fd facet (contracted := contracted))
    (NonTrivalentValencyTwoExit.colChart cover fd (contracted := contracted))
    (NonTrivalentValencyFourRowDictionary.candidateLabelling wSrc pairing wNG wRam wProf
      wConn wGen wVal wWallLab wRowEq)

/-- **The common minor, entry by entry.** -/
theorem matrix_outLabelling_eq_incoming (i j : coordinate) (hi : i ≠ facet)
    (hj : j ≠ fd.labelling.targetEdge.symm contracted) :
    GluingDatum.LengthMatrixPresentation.matrix
        (outLabelling cover fd hc hab hOne wallStar hForest coordinates facet hRows
          hZeroCoord anchorBlock hAnchor pairing hPosCoord hFacetZero).presentation i j =
      GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation i j := by
  classical
  have hd : Equiv.swap (fd.labelling.targetEdge.symm contracted) facet i ≠
      fd.labelling.targetEdge.symm contracted := by
    intro h
    apply hi
    have h2 := congrArg (Equiv.swap (fd.labelling.targetEdge.symm contracted) facet) h
    rwa [Equiv.swap_apply_self, Equiv.swap_apply_left] at h2
  set d : {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted} :=
    ⟨Equiv.swap (fd.labelling.targetEdge.symm contracted) facet i, hd⟩
  set p := (wWallLab).row.symm d
  have hrow : (wWallLab).row p = d := Equiv.apply_symm_apply _ _
  have hi' : NonTrivalentValencyTwoExit.rowChart cover fd facet (contracted := contracted)
      (some d) = i := by
    rw [NonTrivalentValencyTwoExit.rowChart_some]
    exact Equiv.swap_apply_self _ _ i
  have hMid := NonTrivalentValencyTwoExit.matrix_reindexLabelling₂
    (NonTrivalentValencyTwoExit.rowChart cover fd facet (contracted := contracted))
    (NonTrivalentValencyTwoExit.colChart cover fd (contracted := contracted))
    (NonTrivalentValencyFourRowDictionary.candidateLabelling wSrc pairing wNG wRam wProf
      wConn wGen wVal wWallLab wRowEq) (some d) (some ⟨j, hj⟩)
  rw [hi'] at hMid
  have hPath : fd.labelling.row (incomingRow cover fd hc hab hOne wCompat hForest p) = i := by
    have hval := NonTrivalentValencyTwoExit.wallLab_row_val cover fd hc hab hOne hForest
      wNoRet coordinates facet hRows hZeroCoord hPosCoord hFacetZero p
    rw [hrow] at hval
    refine (Equiv.swap facet (fd.labelling.targetEdge.symm contracted)).injective ?_
    rw [← hval, Equiv.swap_comm]
  refine Eq.trans hMid ?_
  rw [← hrow]
  refine Eq.trans (NonTrivalentValencyFourRowDictionary.matrix_candidateLabelling wSrc
    pairing wNG wRam wProf wConn wGen wVal wWallLab wRowEq
    (NonTrivalentValencyFourRetainedInjective.rowEquiv_of_single_row_retainedRow cover fd hc
      hab hOne wallStar hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor
      pairing) p ⟨j, hj⟩) ?_
  refine Eq.trans (matrix_wallLabelling cover fd hc hab hOne wCompat hForest wNoRet
    coordinates facet hRows hZeroCoord hPosCoord hFacetZero p ⟨j, hj⟩) ?_
  rw [hPath]

/-! ### The bridge row of the outgoing matrix -/

/-- The row equivalence sends the bridge row to the vanishing coordinate. -/
theorem rowEquiv_bridgeRow :
    (wRowEq) (NonTrivalentValencyFourRowEquivFinal.bridgeRow wSrc pairing wNG wRam wProf
      wConn wGen wVal) = none :=
  (Equiv.eq_symm_apply _).mp rfl

/-- **The bridge row of the candidate occupies the vanishing row of the incoming
chart.** -/
theorem outLabelling_row_bridge :
    (outLabelling cover fd hc hab hOne wallStar hForest coordinates facet hRows
        hZeroCoord anchorBlock hAnchor pairing hPosCoord hFacetZero).row
      (NonTrivalentValencyFourRowEquivFinal.bridgeRow wSrc pairing wNG wRam wProf wConn
        wGen wVal) = facet := by
  show (NonTrivalentValencyTwoExit.rowChart cover fd facet (contracted := contracted))
      ((NonTrivalentValencyFourRowDictionary.candidateLabelling wSrc pairing wNG wRam wProf
        wConn wGen wVal wWallLab wRowEq).row
        (NonTrivalentValencyFourRowEquivFinal.bridgeRow wSrc pairing wNG wRam wProf wConn
          wGen wVal)) = facet
  rw [NonTrivalentValencyFourRowDictionary.candidateLabelling_row wSrc pairing wNG wRam
    wProf wConn wGen wVal wWallLab wRowEq,
    rowEquiv_bridgeRow cover fd hc hab hOne wallStar hForest coordinates facet hRows
      hZeroCoord anchorBlock hAnchor pairing]
  rfl

theorem outLabelling_row_symm_facet :
    (outLabelling cover fd hc hab hOne wallStar hForest coordinates facet hRows
        hZeroCoord anchorBlock hAnchor pairing hPosCoord hFacetZero).row.symm facet =
      NonTrivalentValencyFourRowEquivFinal.bridgeRow wSrc pairing wNG wRam wProf wConn
        wGen wVal :=
  (Equiv.symm_apply_eq _).mpr
    (outLabelling_row_bridge cover fd hc hab hOne wallStar hForest coordinates facet hRows
      hZeroCoord anchorBlock hAnchor pairing hPosCoord hFacetZero).symm

/-- **A retained row keeps the incoming chart coordinate of its own incoming row.**
The gauged stable row of an incoming wall row is the one the sheet gauge names. -/
theorem outLabelling_row_retained (p : StablePath (contractDatum cover hc hab hOne)) :
    (outLabelling cover fd hc hab hOne wallStar hForest coordinates facet hRows
        hZeroCoord anchorBlock hAnchor pairing hPosCoord hFacetZero).row
      (NonTrivalentValencyFourRowDictionary.retainedRow wSrc pairing wNG wRam wProf wConn
        wGen wVal
        (SheetRelabelStable.stablePathEquiv
          (NonTrivalentValencyFourKZero.PrescribedPairing.relabeling wSrc pairing wNG wRam)
          (wVal).1 p)) =
      fd.labelling.row (incomingRow cover fd hc hab hOne wCompat hForest p) := by
  show (NonTrivalentValencyTwoExit.rowChart cover fd facet (contracted := contracted))
      ((NonTrivalentValencyFourRowDictionary.candidateLabelling wSrc pairing wNG wRam wProf
        wConn wGen wVal wWallLab wRowEq).row _) = _
  rw [NonTrivalentValencyFourRowDictionary.candidateLabelling_row wSrc pairing wNG wRam
    wProf wConn wGen wVal wWallLab wRowEq,
    NonTrivalentValencyFourRetainedInjective.rowEquiv_of_single_row_retainedRow cover fd hc
      hab hOne wallStar hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor
      pairing (SheetRelabelStable.stablePathEquiv
        (NonTrivalentValencyFourKZero.PrescribedPairing.relabeling wSrc pairing wNG wRam)
        (wVal).1 p)]
  have hRelab : (NonTrivalentValencyFourRowDictionary.relabelLabelling wSrc pairing wNG wRam
        (wVal) wWallLab).row
      (SheetRelabelStable.stablePathEquiv
        (NonTrivalentValencyFourKZero.PrescribedPairing.relabeling wSrc pairing wNG wRam)
        (wVal).1 p) = (wWallLab).row p := by
    show (wWallLab).row ((SheetRelabelStable.stablePathEquiv
        (NonTrivalentValencyFourKZero.PrescribedPairing.relabeling wSrc pairing wNG wRam)
        (wVal).1).symm ((SheetRelabelStable.stablePathEquiv
        (NonTrivalentValencyFourKZero.PrescribedPairing.relabeling wSrc pairing wNG wRam)
        (wVal).1) p)) = _
    rw [Equiv.symm_apply_apply]
  refine Eq.trans (congrArg (fun z ↦ NonTrivalentValencyTwoExit.rowChart cover fd facet
    (contracted := contracted) (some z)) hRelab) ?_
  show Equiv.swap (fd.labelling.targetEdge.symm contracted) facet ((wWallLab).row p).1 = _
  rw [NonTrivalentValencyTwoExit.wallLab_row_val cover fd hc hab hOne hForest wNoRet
      coordinates facet hRows hZeroCoord hPosCoord hFacetZero p,
    Equiv.swap_comm facet (fd.labelling.targetEdge.symm contracted)]
  exact Equiv.swap_apply_self _ _ _

/-- The only surviving occurrence of the bridge row lies over the new target
occurrence, so the bridge row of the outgoing matrix vanishes off the contracted
column. -/
theorem occurrences_bridgeRow_of_ne
    (t : (TargetExpansion.graph (contract targetIn hab hOne) ⟨a, hab⟩ (wCand).right).edges)
    (ht : t ≠ TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
      (wCand).right none) :
    StableSourceMatrix.occurrences (wCand).datum
      (NonTrivalentValencyFourRowEquivFinal.bridgeRow wSrc pairing wNG wRam wProf wConn
        wGen wVal) t = ∅ := by
  classical
  refine Finset.eq_empty_iff_forall_notMem.mpr ?_
  intro e he
  obtain ⟨⟨hSurv, hRow⟩, hTarget⟩ := (StableSourceMatrix.mem_occurrences _ t e).mp he
  have hEq' : e = NonTrivalentValencyFourRows.bridgeEdge wSrc pairing wNG wRam wProf wConn
      wGen wVal (selectedRepresentative wSrc pairing) :=
    NonTrivalentValencyFourDictionary.bridgeEdge_isolated wSrc pairing wNG wRam wProf wConn
      wGen wVal ⟨e, hSurv⟩ hRow
  apply ht
  rw [← hTarget, hEq']
  exact BalancedGlobal.Candidate.newSourceEdge_target _ _

theorem occurrences_bridgeRow_new :
    StableSourceMatrix.occurrences (wCand).datum
        (NonTrivalentValencyFourRowEquivFinal.bridgeRow wSrc pairing wNG wRam wProf wConn
          wGen wVal)
        (TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
          (wCand).right none) =
      {NonTrivalentValencyFourRows.bridgeEdge wSrc pairing wNG wRam wProf wConn wGen wVal
        (selectedRepresentative wSrc pairing)} := by
  classical
  refine Finset.Subset.antisymm ?_ ?_
  · intro e he
    obtain ⟨⟨hSurv, hRow⟩, -⟩ := (StableSourceMatrix.mem_occurrences _ _ e).mp he
    exact Finset.mem_singleton.mpr
      (NonTrivalentValencyFourDictionary.bridgeEdge_isolated wSrc pairing wNG wRam wProf
        wConn wGen wVal ⟨e, hSurv⟩ hRow)
  · intro e he
    rw [Finset.mem_singleton] at he
    subst he
    refine (StableSourceMatrix.mem_occurrences _ _ _).mpr ⟨⟨?_, rfl⟩, ?_⟩
    · exact NonTrivalentValencyFourDictionary.bridgeEdge_survives wSrc pairing wNG wRam
        wProf wConn wGen wVal
    · exact BalancedGlobal.Candidate.newSourceEdge_target _ _

theorem matrix_outLabelling_facet_eq_zero (j : coordinate)
    (hj : j ≠ fd.labelling.targetEdge.symm contracted) :
    GluingDatum.LengthMatrixPresentation.matrix
        (outLabelling cover fd hc hab hOne wallStar hForest coordinates facet hRows
          hZeroCoord anchorBlock hAnchor pairing hPosCoord hFacetZero).presentation
        facet j = 0 := by
  classical
  rw [StableSourceMatrix.labelling_matrix_eq,
    outLabelling_row_symm_facet cover fd hc hab hOne wallStar hForest coordinates facet
      hRows hZeroCoord anchorBlock hAnchor pairing hPosCoord hFacetZero]
  have hTarget : (outLabelling cover fd hc hab hOne wallStar hForest coordinates facet
        hRows hZeroCoord anchorBlock hAnchor pairing hPosCoord hFacetZero).targetEdge j ≠
      TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
        (wCand).right none := by
    have hSymm : (NonTrivalentValencyTwoExit.colChart cover fd (contracted := contracted)).symm
        j = some ⟨j, hj⟩ := Equiv.optionSubtypeNe_symm_of_ne hj
    show TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
        (wCand).right
        (Option.map _ ((NonTrivalentValencyTwoExit.colChart cover fd
          (contracted := contracted)).symm j)) ≠ _
    intro hBad
    have hNone := (TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
      (wCand).right).injective hBad
    rw [hSymm] at hNone
    simp at hNone
  unfold StableSourceMatrix.matrix
  rw [occurrences_bridgeRow_of_ne cover fd hc hab hOne wallStar hForest coordinates facet
    hRows hZeroCoord anchorBlock hAnchor pairing _ hTarget, Finset.sum_empty]

theorem matrix_outLabelling_corner_pos :
    0 < GluingDatum.LengthMatrixPresentation.matrix
        (outLabelling cover fd hc hab hOne wallStar hForest coordinates facet hRows
          hZeroCoord anchorBlock hAnchor pairing hPosCoord hFacetZero).presentation facet
        (fd.labelling.targetEdge.symm contracted) := by
  classical
  rw [StableSourceMatrix.labelling_matrix_eq,
    outLabelling_row_symm_facet cover fd hc hab hOne wallStar hForest coordinates facet
      hRows hZeroCoord anchorBlock hAnchor pairing hPosCoord hFacetZero]
  have hSymm : (NonTrivalentValencyTwoExit.colChart cover fd (contracted := contracted)).symm
      (fd.labelling.targetEdge.symm contracted) = none :=
    Equiv.optionSubtypeNe_symm_self _
  have hTarget : (outLabelling cover fd hc hab hOne wallStar hForest coordinates facet
        hRows hZeroCoord anchorBlock hAnchor pairing hPosCoord hFacetZero).targetEdge
        (fd.labelling.targetEdge.symm contracted) =
      TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
        (wCand).right none := by
    show TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
        (wCand).right
        (Option.map _ ((NonTrivalentValencyTwoExit.colChart cover fd
          (contracted := contracted)).symm (fd.labelling.targetEdge.symm contracted))) = _
    rw [hSymm]
    rfl
  rw [hTarget]
  unfold StableSourceMatrix.matrix
  rw [occurrences_bridgeRow_new cover fd hc hab hOne wallStar hForest coordinates facet
    hRows hZeroCoord anchorBlock hAnchor pairing, Finset.sum_singleton]
  exact div_pos one_pos
    (by exact_mod_cast (wCand).datum.sourceEdgeIndex_pos _)

/-! ### The common minor and nonsingularity -/

/-- **The common minor.** -/
theorem agreeOffColumn_outLabelling :
    AgreeOffColumn (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation)
      (GluingDatum.LengthMatrixPresentation.matrix
        (outLabelling cover fd hc hab hOne wallStar hForest coordinates facet hRows
          hZeroCoord anchorBlock hAnchor pairing hPosCoord hFacetZero).presentation)
      (fd.labelling.targetEdge.symm contracted) := by
  intro i j hj
  by_cases hi : i = facet
  · rw [hi]
    rw [matrix_outLabelling_facet_eq_zero cover fd hc hab hOne wallStar hForest coordinates
      facet hRows hZeroCoord anchorBlock hAnchor pairing hPosCoord hFacetZero j hj]
    exact NonTrivalentValencyTwoExit.incoming_facet_eq_zero cover fd coordinates facet
      hZeroCoord hPosCoord hFacetZero j hj
  · exact (matrix_outLabelling_eq_incoming cover fd hc hab hOne wallStar hForest coordinates
      facet hRows hZeroCoord anchorBlock hAnchor pairing hPosCoord hFacetZero i j hi hj).symm

/-- **Nonsingularity of the outgoing matrix.** -/
theorem det_outLabelling_ne_zero :
    (GluingDatum.LengthMatrixPresentation.matrix
      (outLabelling cover fd hc hab hOne wallStar hForest coordinates facet hRows
        hZeroCoord anchorBlock hAnchor pairing hPosCoord hFacetZero).presentation).det ≠ 0 :=
  NonTrivalentLinkMatrix.det_ne_zero
    (agreeOffColumn_outLabelling cover fd hc hab hOne wallStar hForest coordinates facet
      hRows hZeroCoord anchorBlock hAnchor pairing hPosCoord hFacetZero)
    (fun j hj ↦ NonTrivalentValencyTwoExit.incoming_facet_eq_zero cover fd coordinates facet
      hZeroCoord hPosCoord hFacetZero j hj)
    (fun j hj ↦ matrix_outLabelling_facet_eq_zero cover fd hc hab hOne wallStar hForest
      coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing hPosCoord hFacetZero
      j hj)
    fd.det_ne_zero
    (matrix_outLabelling_corner_pos cover fd hc hab hOne wallStar hForest coordinates facet
      hRows hZeroCoord anchorBlock hAnchor pairing hPosCoord hFacetZero).ne'

/-! ### The outgoing target: connected, genus zero, and the same edge count -/

theorem outgoing_targetConnected :
    graph_connected (TargetExpansion.graph (contract targetIn hab hOne) ⟨a, hab⟩
      (wCand).right) :=
  TargetExpansion.graph_connected (contract targetIn hab hOne) ⟨a, hab⟩ _
    (NonTrivalentUniqueFourValent.wall_target_connected cover fd hab hOne)

theorem outgoing_targetGenus :
    genus (TargetExpansion.graph (contract targetIn hab hOne) ⟨a, hab⟩ (wCand).right) = 0 :=
  (TargetExpansion.graph_genus (contract targetIn hab hOne) ⟨a, hab⟩ _).trans
    (NonTrivalentUniqueFourValent.wall_target_genus cover fd hab hOne)

/-- **The outgoing target has as many edges as the incoming one.** -/
theorem outgoing_targetEdgeCard :
    (TargetExpansion.graph (contract targetIn hab hOne) ⟨a, hab⟩ (wCand).right).edges.card =
      targetIn.edges.card :=
  (TargetExpansion.graph_edge_card (contract targetIn hab hOne) ⟨a, hab⟩ _).trans
    (WallDegeneration.edge_card_contract hab hOne).symm

/-! ### Trivalence of the outgoing candidate -/

/-- **The gauged wall datum is trivalent away from the merged vertex.**  The
block-preserving branch gauge is a sheet relabelling, so it moves no surviving
valency, and `NonTrivalentValencyTwoExit.wallDatum_trivalent_away` applies to
the pullback. -/
theorem gauged_trivalent_away (v : (wGauged).SourceVertex)
    (hv : v.1.1 ≠ (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)) :
    nonDanglingValency (wGauged) v ≤ 3 := by
  obtain ⟨w, rfl⟩ := (NonTrivalentValencyFourKZero.PrescribedPairing.relabeling wSrc pairing
    wNG wRam).sourceVertexEquiv.surjective v
  exact le_of_eq_of_le
    (SheetRelabelStable.nonDanglingValency_map
      (NonTrivalentValencyFourKZero.PrescribedPairing.relabeling wSrc pairing wNG wRam)
      (wVal).1 w)
    (NonTrivalentValencyTwoExit.wallDatum_trivalent_away cover fd hc hab hOne hForest w hv)

/-- Every source vertex of the candidate over one side of the new target edge is
the endpoint vertex of its own sheet. -/
theorem eq_endpointVertex (sideValue : Bool) (v : (wCand).datum.SourceVertex)
    (hv : v.1.1 = (if sideValue then TargetExpansion.freshVertex (contract targetIn hab hOne)
      else TargetExpansion.oldVertex (contract targetIn hab hOne) ⟨a, hab⟩)) :
    NonTrivalentValencyFourRows.endpointVertex wSrc pairing wNG wRam wProf wConn wGen wVal
      sideValue v.1.2 = v :=
  ((wCand).datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨hv.symm, rfl⟩

/-- **At most two surviving occurrences of a wall block sit on one side of the
prescribed pairing** (`eq_of_three_on_side`, in counting form). -/
theorem card_side_le_two (x : Fin deg) (sideValue : Bool) :
    ((nonDanglingIncident (wGauged)
        (WallBlock.sourceVertex (wGauged) ⟨a, hab⟩
          (WallBlock.ofSheet (wGauged) ⟨a, hab⟩ x))).filter
      (fun old ↦ wallStar.right pairing old.1.1 = sideValue)).card ≤ 2 := by
  classical
  by_contra hBig
  have hBig' : 3 ≤ ((nonDanglingIncident (wGauged)
        (WallBlock.sourceVertex (wGauged) ⟨a, hab⟩
          (WallBlock.ofSheet (wGauged) ⟨a, hab⟩ x))).filter
      (fun old ↦ wallStar.right pairing old.1.1 = sideValue)).card := by omega
  obtain ⟨t, hSub, hCard⟩ := Finset.exists_subset_card_eq hBig'
  obtain ⟨o₁, o₂, o₃, h₁₂, h₁₃, h₂₃, rfl⟩ := Finset.card_eq_three.mp hCard
  have hMem : ∀ o ∈ ({o₁, o₂, o₃} : Finset (wGauged).SourceEdge),
      (¬ IsDangling (wGauged) o ∧ o.1.1 ∈ GluingDatum.incidentEdges (⟨a, hab⟩ :
          GraphContraction.Vertex targetIn b) ∧
        ((wGauged).vertexPartition ⟨a, hab⟩).Rel x o.1.2) ∧
      wallStar.right pairing o.1.1 = sideValue := by
    intro o ho
    obtain ⟨hIncFilter, hSideO⟩ := Finset.mem_filter.mp (hSub ho)
    obtain ⟨hSurvO, hIncO⟩ := (mem_nonDanglingIncident _ _ _).mp hIncFilter
    obtain ⟨hAtO, hBlockO⟩ := (incident_wallBlock_sourceVertex_iff (wGauged) _ o).mp hIncO
    refine ⟨⟨hSurvO, hAtO, ?_⟩, hSideO⟩
    have hRepr : ((wGauged).vertexPartition ⟨a, hab⟩).repr o.1.2 =
        ((wGauged).vertexPartition ⟨a, hab⟩).repr x := congrArg Subtype.val hBlockO
    exact hRepr.symm
  obtain ⟨⟨hS₁, hA₁, hR₁⟩, hD₁⟩ := hMem o₁ (by simp)
  obtain ⟨⟨hS₂, hA₂, hR₂⟩, hD₂⟩ := hMem o₂ (by simp)
  obtain ⟨⟨hS₃, hA₃, hR₃⟩, hD₃⟩ := hMem o₃ (by simp)
  rcases NonTrivalentValencyFourRowEquivFinal.eq_of_three_on_side wSrc pairing wNG wRam
    (NonTrivalentValencyFourRowEquivFinal.gauged_starInjective_of_single_row cover fd hc hab
      hOne wallStar hForest anchorBlock hAnchor pairing x)
    o₁ o₂ o₃ hS₁ hS₂ hS₃ hA₁ hA₂ hA₃ hR₁ hR₂ hR₃ hD₁ hD₂ hD₃ with h | h | h
  · exact h₁₂ h
  · exact h₁₃ h
  · exact h₂₃ h

/-- **The retaining endpoint of a non-anchor block is trivalent at most.**  Every
survivor there is a retained survivor of the block on the retaining side or the
new occurrence of a fine class of the block, and both are named by a survivor of
the block in the gauged wall datum. -/
theorem nonDanglingValency_ret_le (x : Fin deg)
    (hb : ¬ ((wGauged).vertexPartition (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).Rel
      anchorBlock.1 x) :
    nonDanglingValency (wCand).datum
      (wEpv (wRetSide (((wGauged).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x)) x) ≤ 3 := by
  classical
  have hSub : nonDanglingIncident (wCand).datum
        (wEpv (wRetSide (((wGauged).vertexPartition
          (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x)) x) ⊆
      (nonDanglingIncident (wGauged) (WallBlock.sourceVertex (wGauged) (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)
          (WallBlock.ofSheet (wGauged) (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x))).image
        (fun old ↦ if wallStar.right pairing old.1.1 =
            wRetSide (((wGauged).vertexPartition
              (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x) then
          (wCand).oldSourceEdge old else (wCand).newSourceEdge old.1.2) := by
    intro f hf
    obtain ⟨hSurv, hInc⟩ := (mem_nonDanglingIncident _ _ _).mp hf
    rcases NonTrivalentValencyFourRowEquiv.nonDanglingIncident_ret_dichotomy wSrc pairing wNG
      wRam wProf wConn wGen wVal hb hSurv hInc with
      ⟨old, hOldSurv, hAt, hSide, hRel, rfl⟩ | ⟨old, hOldSurv, hAt, hSide, hRel, rfl⟩
    · refine Finset.mem_image.mpr ⟨old,
        NonTrivalentValencyFourRowEquivFinal.mem_nonDanglingIncident_block wSrc pairing wNG
          wRam hOldSurv hAt hRel, ?_⟩
      rw [if_pos hSide]
    · refine Finset.mem_image.mpr ⟨old,
        NonTrivalentValencyFourRowEquivFinal.mem_nonDanglingIncident_block wSrc pairing wNG
          wRam hOldSurv hAt hRel, ?_⟩
      rw [if_neg (by rw [hSide]; exact Bool.not_ne_self _)]
  rw [← card_nonDanglingIncident]
  refine le_trans (Finset.card_le_card hSub) (le_trans Finset.card_image_le ?_)
  rw [card_nonDanglingIncident]
  exact NonTrivalentValencyFourRowEquivFinal.gauged_valency_of_single_row cover fd hc hab
    hOne wallStar hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing x hb

/-- **A fine endpoint of a non-anchor block is trivalent at most**: the block's
new occurrence on that sheet, together with the retained survivors of the block
on the fine side, of which there are at most two. -/
theorem nonDanglingValency_fine_le (x : Fin deg)
    (hb : ¬ ((wGauged).vertexPartition (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).Rel
      anchorBlock.1 x) :
    nonDanglingValency (wCand).datum
      (wEpv (!wRetSide (((wGauged).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x)) x) ≤ 3 := by
  classical
  have hSub : nonDanglingIncident (wCand).datum
        (wEpv (!wRetSide (((wGauged).vertexPartition
          (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x)) x) ⊆
      insert ((wCand).newSourceEdge x)
        (((nonDanglingIncident (wGauged) (WallBlock.sourceVertex (wGauged) (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)
          (WallBlock.ofSheet (wGauged) (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x))).filter
          (fun old ↦ wallStar.right pairing old.1.1 =
            !wRetSide (((wGauged).vertexPartition
              (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x))).image
          (wCand).oldSourceEdge) := by
    intro f hf
    obtain ⟨hSurv, hInc⟩ := (mem_nonDanglingIncident _ _ _).mp hf
    rcases NonTrivalentValencyFourDescent.nonDanglingIncident_fine_cases wSrc pairing wNG
      wRam wProf wConn wGen wVal hb hSurv hInc with hNew | ⟨old, hOldSurv, hAt, hSide, hRel, rfl⟩
    · rw [hNew]
      exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨old,
        Finset.mem_filter.mpr ⟨?_, hSide⟩, rfl⟩)
      exact NonTrivalentValencyFourRowEquivFinal.mem_nonDanglingIncident_block wSrc pairing
        wNG wRam hOldSurv hAt
        ((NonTrivalentValencyFourDescent.blockRes_newEdge_refines wSrc pairing wNG wRam wProf
          _).rel hRel)
  rw [← card_nonDanglingIncident]
  refine le_trans (Finset.card_le_card hSub) ?_
  have hTwo := le_trans (Finset.card_image_le
    (s := (nonDanglingIncident (wGauged) (WallBlock.sourceVertex (wGauged) (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)
          (WallBlock.ofSheet (wGauged) (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x))).filter
      (fun old ↦ wallStar.right pairing old.1.1 =
        !wRetSide (((wGauged).vertexPartition
          (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x)))
    (f := (wCand).oldSourceEdge))
    (card_side_le_two cover fd hc hab hOne wallStar hForest anchorBlock hAnchor pairing x
      (!wRetSide (((wGauged).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x)))
  have hIns := Finset.card_insert_le ((wCand).newSourceEdge x)
    (((nonDanglingIncident (wGauged) (WallBlock.sourceVertex (wGauged) (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)
          (WallBlock.ofSheet (wGauged) (⟨a, hab⟩ : GraphContraction.Vertex targetIn b) x))).filter
      (fun old ↦ wallStar.right pairing old.1.1 =
        !wRetSide (((wGauged).vertexPartition
          (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x))).image
      (wCand).oldSourceEdge)
  omega

/-- **Both endpoint vertices of a non-anchor wall block are trivalent at most.** -/
theorem nonDanglingValency_block_le (sideValue : Bool) (x : Fin deg)
    (hb : ¬ ((wGauged).vertexPartition (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).Rel
      anchorBlock.1 x) :
    nonDanglingValency (wCand).datum (wEpv sideValue x) ≤ 3 := by
  by_cases hT : sideValue = wRetSide (((wGauged).vertexPartition
      (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).repr x)
  · rw [hT]
    exact nonDanglingValency_ret_le cover fd hc hab hOne wallStar hForest coordinates facet
      hRows hZeroCoord anchorBlock hAnchor pairing x hb
  · rw [NonTrivalentValencyFourRowDictionary.bool_eq_not_of_ne hT]
    exact nonDanglingValency_fine_le cover fd hc hab hOne wallStar hForest coordinates facet
      hRows hZeroCoord anchorBlock hAnchor pairing x hb

/-- **The outgoing candidate is trivalent.**  Off the wall the incoming
trivalence descends through `ResolutionAwayFromWall` and the sheet gauge; at the
anchor both `K = 0` endpoint classes are trivalent and every other fine class
over the anchor carries at most one survivor; at a non-anchor block the two
endpoint censuses bound both sides by three. -/
theorem candidate_trivalent (v : (wCand).datum.SourceVertex) :
    nonDanglingValency (wCand).datum v ≤ 3 := by
  classical
  have hGenus : genus (wCand).datum.sourceGraph = genus (wGauged).sourceGraph :=
    NonTrivalentValencyFourRows.candidate_sourceGenus wSrc pairing wNG wRam wProf wConn wGen
      wVal
  have hRepRel : ((wGauged).vertexPartition
      (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).Rel anchorBlock.1
        (selectedRepresentative wSrc pairing) :=
    (NonTrivalentValencyFourRows.gauged_rel_iff wSrc pairing wNG wRam _ _).mpr
      ((wSrc).sheet_wall_rel _)
  have hWall : ∀ sideValue : Bool,
      v.1.1 = (if sideValue then TargetExpansion.freshVertex (contract targetIn hab hOne)
        else TargetExpansion.oldVertex (contract targetIn hab hOne) ⟨a, hab⟩) →
      nonDanglingValency (wCand).datum v ≤ 3 := by
    intro sideValue hv
    rw [← eq_endpointVertex cover fd hc hab hOne wallStar hForest coordinates facet hRows
      hZeroCoord anchorBlock hAnchor pairing sideValue v hv]
    by_cases hAnchorRel : ((wGauged).vertexPartition
        (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)).Rel anchorBlock.1 v.1.2
    · by_cases hSide : sideValue = smallerSide wSrc pairing
      · by_cases hFine : (finePartition wSrc pairing wNG wRam).Rel
            (selectedRepresentative wSrc pairing) v.1.2
        · rw [← NonTrivalentValencyFourRows.endpointVertex_eq wSrc pairing wNG wRam wProf
              wConn wGen wVal sideValue hRepRel
              (by rw [hSide, NonTrivalentValencyFourDictionary.endpointForSide_smaller wSrc
                pairing wNG wRam]; exact hFine),
            NonTrivalentValencyFourDictionary.nonDanglingValency_endpointVertex wSrc pairing
              wNG wRam wProf wConn wGen wVal sideValue]
        · have hSingle : (finePartition wSrc pairing wNG wRam).block v.1.2 = {v.1.2} := by
            rcases finePartition_rel_or_singleton wSrc pairing wNG wRam v.1.2
              ((NonTrivalentValencyFourRows.gauged_rel_iff wSrc pairing wNG wRam _ _).mp
                hAnchorRel) with hRel | hSing
            · exact absurd hRel hFine
            · exact hSing
          rw [hSide]
          have hCard := Finset.card_le_card
            (NonTrivalentValencyFourDictionary.nonDanglingIncident_singleton_subset wSrc
              pairing wNG wRam wProf wConn wGen wVal hAnchorRel hSingle hFine)
          rw [card_nonDanglingIncident, Finset.card_singleton] at hCard
          omega
      · rw [← NonTrivalentValencyFourRows.endpointVertex_eq wSrc pairing wNG wRam wProf
            wConn wGen wVal sideValue hRepRel
            (by rw [NonTrivalentValencyFourRowDictionary.bool_eq_not_of_ne hSide,
              NonTrivalentValencyFourRowDictionary.endpointForSide_not_smaller wSrc pairing
                wNG wRam]; exact hRepRel.symm.trans hAnchorRel),
          NonTrivalentValencyFourDictionary.nonDanglingValency_endpointVertex wSrc pairing
            wNG wRam wProf wConn wGen wVal sideValue]
    · exact nonDanglingValency_block_le cover fd hc hab hOne wallStar hForest coordinates
        facet hRows hZeroCoord anchorBlock hAnchor pairing sideValue v.1.2 hAnchorRel
  rcases hcase : (v.1.1 : TargetExpansion.Vertex (contract targetIn hab hOne)) with place | u
  · by_cases hIsWall : place = (⟨a, hab⟩ : GraphContraction.Vertex targetIn b)
    · exact hWall false (by rw [hcase, hIsWall]; rfl)
    · obtain ⟨old, hOld, hRet⟩ := ResolutionAwayFromWall.exists_retainedVertex_of_target
        (wCand) v place hIsWall hcase
      rw [← hRet, ResolutionAwayFromWall.nonDanglingValency_retainedVertex (wCand)
        (gaugedData_valid wSrc pairing wNG wRam wVal) hGenus old
        (by rw [hOld]; exact hIsWall)]
      exact gauged_trivalent_away cover fd hc hab hOne wallStar hForest anchorBlock hAnchor
        pairing old (by rw [hOld]; exact hIsWall)
  · exact hWall true (by rw [hcase]; cases u; rfl)

/-! ### Path ends: the bridge row, and the reduction to the retained rows -/

/-- **`HasPathEnds` for the outgoing candidate reduces to the retained rows.**
Through the row equivalence every stable row of the candidate is either the
bridge row -- whose occurrence `h_1` has both ends at the two trivalent `K = 0`
endpoint classes, so it is a path end outright -- or the retained row of a
stable row of the gauged wall datum. -/
theorem hasPathEnds_of_retainedRowEnds
    (hRetained : ∀ r : StablePath (wGauged),
      ∃ (first : NonDanglingEdge (wCand).datum) (vertex : (wCand).datum.SourceVertex),
        first.stablePath = NonTrivalentValencyFourRowDictionary.retainedRow wSrc pairing wNG
            wRam wProf wConn wGen wVal r ∧
          IsPathEnd (wCand).datum first.1 vertex) :
    HasPathEnds (wCand).datum := by
  classical
  intro e
  have hBack := (wRowEq).symm_apply_apply e.stablePath
  cases hCase : (wRowEq) e.stablePath with
  | none =>
    rw [hCase] at hBack
    have hRow : e.stablePath = NonTrivalentValencyFourRowEquivFinal.bridgeRow wSrc pairing
        wNG wRam wProf wConn wGen wVal := hBack.symm
    refine ⟨⟨NonTrivalentValencyFourRows.bridgeEdge wSrc pairing wNG wRam wProf wConn wGen
        wVal (selectedRepresentative wSrc pairing),
      NonTrivalentValencyFourDictionary.bridgeEdge_survives wSrc pairing wNG wRam wProf wConn
        wGen wVal⟩,
      wEpv false (selectedRepresentative wSrc pairing), hRow.symm, ?_, ?_⟩
    · exact NonTrivalentValencyFourRows.bridgeEdge_incident wSrc pairing wNG wRam wProf wConn
        wGen wVal false _
    · rw [NonTrivalentValencyFourDictionary.nonDanglingValency_endpointVertex wSrc pairing
        wNG wRam wProf wConn wGen wVal false]
      omega
  | some r =>
    rw [hCase] at hBack
    have hRow : e.stablePath = NonTrivalentValencyFourRowDictionary.retainedRow wSrc pairing
        wNG wRam wProf wConn wGen wVal r := hBack.symm
    obtain ⟨first, vertex, hFirst, hEnd⟩ := hRetained r
    exact ⟨first, vertex, hFirst.trans hRow.symm, hEnd⟩


end Presentation

end

end DraismaVargas.LocalCases.NonTrivalentValencyFourExit
