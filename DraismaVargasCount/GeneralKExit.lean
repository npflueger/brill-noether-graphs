import DraismaVargasCount.GeneralKRowsK

/-!
# The general-`K` exit at a four-valent wall: the outgoing presentation

Vargas, Part II: the labelling conventions of the combinatorial setup for a change of
combinatorial type (`subsec-setup-determinants`), the wall matrix `A_{φ₀}` as the common
minor in the proof of `lm:change-comb-type`, and the valency-four case `{v4-nd4}`
(`subsec-case-v4`), for every admissible `K`. The valency-four limits feed the type changes
at merged-vertex valency four (step 3 of `Assembly`).

This is the general-`K` counterpart of the `K = 0` construction
`NonTrivalentValencyFourExit.outLabelling` / `agreeOffColumn_outLabelling` /
`det_outLabelling_ne_zero` and `NonTrivalentValencyFourExit.outgoingFD`.

## What is proved

* `candLab`, `outLabK`: the outgoing honest labelling of
  `GeneralKExitSetup.candK`, first over `Option` of the wall chart (built from
  the row dictionary `GeneralKRowsK.rowEquivK`, the gauge
  `GeneralKRowGauge.gaugeIso` and the wall datum's own labelling
  `NonTrivalentValencyTwoExit.wallLab`), then re-indexed onto the incoming chart
  by the two independent charts `rowChart` / `colChart`.
* The labelling dictionary: `outLabK_row` (the explicit row formula),
  `outLabK_row_retained`, `outLabK_row_bridge` (the bridge row is the vanishing
  row `label m.base`), `outLabK_targetEdge_col` (the wall column is the new
  target occurrence) and `outLabK_targetEdge_ne` (every other column keeps its
  incoming target occurrence).
* `matrix_outLabK_eq_incoming`: the common minor, entry by entry;
  `matrix_outLabK_facet_eq_zero`: the bridge row vanishes off the wall column;
  `matrix_outLabK_corner`: its corner entry is `1 / k₁` with
  `k₁ = |A₋ ∩ A₊| ≥ 1`; `agreeOffColumn_outLabK` and `det_outLabK_ne_zero`.
* `outgoingFDK`: the outgoing `FullDimensionalSourcePresentation`, through
  `NonTrivalentValencyTwoExit.ofTypeChange`, with validity from
  `Position.candidate_datum_valid` and source genus, trivalence and path ends
  from `GeneralKSourceFacts` (`GeneralKSourceFacts.candidate_sourceGenus`,
  `candidate_trivalent`, `hasPathEnds_candidate`).
* **Main statements.** `exists_outgoingFD`: over
  `GeneralKSourceFacts.LocalCanonicalBackground`, an outgoing full-dimensional presentation
  agreeing with the incoming matrix off the wall column, with the column and row dictionary
  that `GeneralKLink.exists_typeChangeLinkK_of_equivalence` asks for.
  `exists_outgoingFD_skeleton`: the bare existence of such a presentation.
  `exists_background_outgoingFD`: with the background produced by
  `GeneralKSourceFacts.exists_localCanonicalBackground`, so with **no
  hypothesis** beyond the wall data and the position.

## What is NOT proved

* Nothing is stated over `GeneralKExitSetup.CanonicalBackground`, which need not
  be satisfiable (`GeneralKBackground.not_exists_literalBackground`).  The
  statements here are over its localized form `LocalCanonicalBackground`, which
  is inhabited at every wall.
* The `Tracks` obligation of the type-change link, and any identification of the
  general-`K` stable graph with the `K = 0` one (a `StableGraphIncidence.Equivalence`):
  only the row dictionary `rowEquivK` / `rowEquivWall` is supplied.
* `K`-rigidity, that different `K` give different classes (see `ValencyFourSplit`).
-/

set_option autoImplicit false

namespace DraismaVargas.Count.GeneralKExit

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero.PrescribedPairing
open DraismaVargas.Count.GeneralKReceipts
open DraismaVargas.Count.GeneralKExitSetup
open DraismaVargas.Count.GeneralKRowCore
open DraismaVargas.Count.GeneralKRowStar
open DraismaVargas.Count.GeneralKRowEquiv
open DraismaVargas.Count.GeneralKRowGauge
open DraismaVargas.Count.GeneralKRowsK

section Wall

open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource

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

variable (position : GeneralKReceipts.Position
    (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc wd.hab wd.hOne
      wallStar (wd.hForest m) anchorBlock hAnchor) pairing
    (smallerSide (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc
      wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor) pairing))
  (geometry : GeneralKReceipts.PairingBackground position.datum wallStar pairing
    anchorBlock.1)

local notation "cK" => (candK m wd wallStar anchorBlock hAnchor pairing position geometry)
local notation "vNoRet" =>
  (StablePathFacetContraction.noContractedReturn_of_fourStar wd.cover wd.fullDim wd.hc wd.hab
    wd.hOne wallStar)
local notation "vWallLab" =>
  (NonTrivalentValencyTwoExit.wallLab wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m)
    vNoRet wd.coordinates (label m.base) wd.hRows wd.hZeroCoord wd.hPosCoord wd.hFacetZero)
local notation "vRowChart" =>
  (NonTrivalentValencyTwoExit.rowChart wd.cover wd.fullDim (label m.base)
    (contracted := wd.contracted))
local notation "vColChart" =>
  (NonTrivalentValencyTwoExit.colChart wd.cover wd.fullDim (contracted := wd.contracted))

/-! ## 5.  The outgoing honest labelling on the incoming chart -/

/-- The candidate's honest labelling over `Option` of the wall chart: `none` is
the new target occurrence and the bridge row. -/
noncomputable def candLab
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry) :
    StableLengthMatrixLabelling (cK).datum
      (Option {column : coordinate //
        column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted}) where
  targetEdge := (Equiv.optionCongr (vWallLab).targetEdge).trans
    (occurrenceEquiv (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ (cK).right)
  row := (rowEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg).trans
    (Equiv.optionCongr ((gaugeRow m wd wallStar anchorBlock hAnchor pairing position).symm.trans
      (vWallLab).row))

/-- **The outgoing honest labelling**, re-indexed onto the incoming chart by two
independent charts: the new target occurrence in the contracted column, the
bridge row in the vanishing row `label m.base`. -/
noncomputable def outLabK
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry) :
    StableLengthMatrixLabelling (cK).datum coordinate :=
  NonTrivalentValencyTwoExit.reindexLabelling₂ vRowChart vColChart
    (candLab m wd wallStar anchorBlock hAnchor pairing position geometry hBg)

theorem candLab_row_retained
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry)
    (p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    (candLab m wd wallStar anchorBlock hAnchor pairing position geometry hBg).row
        (retainedRowK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
          (gaugeRow m wd wallStar anchorBlock hAnchor pairing position p)) =
      some ((vWallLab).row p) := by
  show Equiv.optionCongr _ (rowEquivK m wd wallStar anchorBlock hAnchor pairing position
    geometry hBg (retainedRowK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
      (gaugeRow m wd wallStar anchorBlock hAnchor pairing position p))) = _
  rw [rowEquivK_retainedRow]
  show some (((gaugeRow m wd wallStar anchorBlock hAnchor pairing position).symm.trans
    (vWallLab).row) (gaugeRow m wd wallStar anchorBlock hAnchor pairing position p)) = _
  rw [Equiv.trans_apply,
    Equiv.symm_apply_apply (gaugeRow m wd wallStar anchorBlock hAnchor pairing position) p]

theorem candLab_row_bridge
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry) :
    (candLab m wd wallStar anchorBlock hAnchor pairing position geometry hBg).row
        (bridgeRowK m wd wallStar anchorBlock hAnchor pairing position geometry hBg) = none := by
  show Equiv.optionCongr _ (rowEquivK m wd wallStar anchorBlock hAnchor pairing position
    geometry hBg (bridgeRowK m wd wallStar anchorBlock hAnchor pairing position geometry hBg)) = _
  rw [rowEquivK_bridgeRow]
  rfl

/-- **The common minor of the `Option`-indexed labelling**: a retained row has
the wall datum's entry in every old column. -/
theorem matrix_candLab_some
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry)
    (p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (c : {column : coordinate // column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted}) :
    GluingDatum.LengthMatrixPresentation.matrix
        (candLab m wd wallStar anchorBlock hAnchor pairing position geometry hBg).presentation
        (some ((vWallLab).row p)) (some c) =
      GluingDatum.LengthMatrixPresentation.matrix (vWallLab).presentation
        ((vWallLab).row p) c := by
  classical
  rw [StableSourceMatrix.labelling_matrix_eq, StableSourceMatrix.labelling_matrix_eq,
    Equiv.symm_apply_apply (vWallLab).row p]
  have hRow : (candLab m wd wallStar anchorBlock hAnchor pairing position geometry hBg).row.symm
      (some ((vWallLab).row p)) =
      retainedRowK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
        (gaugeRow m wd wallStar anchorBlock hAnchor pairing position p) :=
    (Equiv.symm_apply_eq _).mpr
      (candLab_row_retained m wd wallStar anchorBlock hAnchor pairing position geometry hBg p).symm
  rw [hRow]
  exact (GeneralKRowEquiv.matrix_retainedRow_old
    (starHyp m wd wallStar anchorBlock hAnchor pairing position geometry hBg)
    (anchorHyp m wd wallStar anchorBlock hAnchor pairing position geometry hBg) _ _).trans
    ((gaugeIso wallStar position.gauge).matrix_map vVal.1 p _)

/-! ## 6.  The common minor and nonsingularity -/

theorem outLabK_row
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry) :
    (outLabK m wd wallStar anchorBlock hAnchor pairing position geometry hBg).row =
      (rowEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg).trans
        ((Equiv.optionCongr ((gaugeRow m wd wallStar anchorBlock hAnchor pairing position).symm.trans
          (vWallLab).row)).trans vRowChart) := rfl

/-- **A retained row keeps the incoming chart coordinate of its wall row.** -/
theorem outLabK_row_retained
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry)
    (p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    (outLabK m wd wallStar anchorBlock hAnchor pairing position geometry hBg).row
        (retainedRowK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
          (gaugeRow m wd wallStar anchorBlock hAnchor pairing position p)) =
      vRowChart (some ((vWallLab).row p)) := by
  show vRowChart ((candLab m wd wallStar anchorBlock hAnchor pairing position geometry hBg).row
    _) = _
  rw [candLab_row_retained]

/-- **The bridge row occupies the vanishing row `label m.base`.** -/
theorem outLabK_row_bridge
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry) :
    (outLabK m wd wallStar anchorBlock hAnchor pairing position geometry hBg).row
        (bridgeRowK m wd wallStar anchorBlock hAnchor pairing position geometry hBg) =
      label m.base := by
  show vRowChart ((candLab m wd wallStar anchorBlock hAnchor pairing position geometry hBg).row
    _) = _
  rw [candLab_row_bridge]
  rfl

theorem outLabK_row_symm_facet
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry) :
    (outLabK m wd wallStar anchorBlock hAnchor pairing position geometry hBg).row.symm
        (label m.base) =
      bridgeRowK m wd wallStar anchorBlock hAnchor pairing position geometry hBg :=
  (Equiv.symm_apply_eq _).mpr
    (outLabK_row_bridge m wd wallStar anchorBlock hAnchor pairing position geometry hBg).symm

/-- **The new target occurrence sits in the contracted column.** -/
theorem outLabK_targetEdge_col
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry) :
    (outLabK m wd wallStar anchorBlock hAnchor pairing position geometry hBg).targetEdge
        (wd.fullDim.labelling.targetEdge.symm wd.contracted) =
      occurrenceEquiv (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ (cK).right none := by
  have hSymm : (vColChart).symm (wd.fullDim.labelling.targetEdge.symm wd.contracted) = none :=
    Equiv.optionSubtypeNe_symm_self _
  show occurrenceEquiv (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ (cK).right
      (Option.map _ ((vColChart).symm (wd.fullDim.labelling.targetEdge.symm wd.contracted))) = _
  rw [hSymm]
  rfl

/-- **Every other column keeps its incoming target occurrence.** -/
theorem outLabK_targetEdge_ne
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry)
    (j : {column : coordinate // column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted}) :
    (outLabK m wd wallStar anchorBlock hAnchor pairing position geometry hBg).targetEdge j.1 =
      occurrenceEquiv (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ (cK).right
        (some (StablePathFacetContraction.punctureTargetEquiv wd.fullDim.labelling wd.hc wd.hab
          wd.hOne j)) := by
  have hSymm : (vColChart).symm j.1 = some j := Equiv.optionSubtypeNe_symm_of_ne j.2
  show occurrenceEquiv (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ (cK).right
      (Option.map _ ((vColChart).symm j.1)) = _
  rw [hSymm]
  rfl

/-- **The common minor, entry by entry.** -/
theorem matrix_outLabK_eq_incoming
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry)
    (i j : coordinate) (hi : i ≠ label m.base)
    (hj : j ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted) :
    GluingDatum.LengthMatrixPresentation.matrix
        (outLabK m wd wallStar anchorBlock hAnchor pairing position geometry hBg).presentation
        i j =
      GluingDatum.LengthMatrixPresentation.matrix wd.fullDim.labelling.presentation i j := by
  classical
  have hd : Equiv.swap (wd.fullDim.labelling.targetEdge.symm wd.contracted) (label m.base) i ≠
      wd.fullDim.labelling.targetEdge.symm wd.contracted := by
    intro h
    apply hi
    have h2 := congrArg (Equiv.swap (wd.fullDim.labelling.targetEdge.symm wd.contracted)
      (label m.base)) h
    rwa [Equiv.swap_apply_self, Equiv.swap_apply_left] at h2
  set d : {column : coordinate // column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted} :=
    ⟨Equiv.swap (wd.fullDim.labelling.targetEdge.symm wd.contracted) (label m.base) i, hd⟩
  set p := (vWallLab).row.symm d
  have hrow : (vWallLab).row p = d := Equiv.apply_symm_apply _ _
  have hi' : vRowChart (some d) = i := by
    rw [NonTrivalentValencyTwoExit.rowChart_some]
    exact Equiv.swap_apply_self _ _ i
  have hMid := NonTrivalentValencyTwoExit.matrix_reindexLabelling₂ vRowChart vColChart
    (candLab m wd wallStar anchorBlock hAnchor pairing position geometry hBg) (some d)
    (some ⟨j, hj⟩)
  rw [hi'] at hMid
  have hPath : wd.fullDim.labelling.row
      (StablePathFacetContraction.incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
        (WallAdmissibility.danglingCompatible_of_contractionForest wd.cover wd.hc wd.hab wd.hOne
          (wd.hForest m)) (wd.hForest m) p) = i := by
    have hval := NonTrivalentValencyTwoExit.wallLab_row_val wd.cover wd.fullDim wd.hc wd.hab
      wd.hOne (wd.hForest m) vNoRet wd.coordinates (label m.base) wd.hRows wd.hZeroCoord
      wd.hPosCoord wd.hFacetZero p
    rw [hrow] at hval
    refine (Equiv.swap (label m.base) (wd.fullDim.labelling.targetEdge.symm wd.contracted)).injective
      ?_
    rw [← hval, Equiv.swap_comm]
  refine Eq.trans hMid ?_
  rw [← hrow]
  refine (matrix_candLab_some m wd wallStar anchorBlock hAnchor pairing position geometry hBg p
    ⟨j, hj⟩).trans ?_
  refine (StablePathFacetContraction.matrix_wallLabelling wd.cover wd.fullDim wd.hc wd.hab wd.hOne
    (WallAdmissibility.danglingCompatible_of_contractionForest wd.cover wd.hc wd.hab wd.hOne
      (wd.hForest m)) (wd.hForest m) vNoRet wd.coordinates (label m.base) wd.hRows wd.hZeroCoord
    wd.hPosCoord wd.hFacetZero p ⟨j, hj⟩).trans ?_
  rw [hPath]

/-- The bridge row vanishes off the contracted column. -/
theorem matrix_outLabK_facet_eq_zero
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry)
    (j : coordinate) (hj : j ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted) :
    GluingDatum.LengthMatrixPresentation.matrix
        (outLabK m wd wallStar anchorBlock hAnchor pairing position geometry hBg).presentation
        (label m.base) j = 0 := by
  classical
  rw [StableSourceMatrix.labelling_matrix_eq,
    outLabK_row_symm_facet m wd wallStar anchorBlock hAnchor pairing position geometry hBg,
    outLabK_targetEdge_ne m wd wallStar anchorBlock hAnchor pairing position geometry hBg ⟨j, hj⟩]
  exact GeneralKRowEquiv.matrix_bridgeRow_old
    (starHyp m wd wallStar anchorBlock hAnchor pairing position geometry hBg)
    (anchorHyp m wd wallStar anchorBlock hAnchor pairing position geometry hBg) _

/-- The corner entry of the bridge row is positive. -/
theorem matrix_outLabK_corner_pos
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry) :
    0 < GluingDatum.LengthMatrixPresentation.matrix
        (outLabK m wd wallStar anchorBlock hAnchor pairing position geometry hBg).presentation
        (label m.base) (wd.fullDim.labelling.targetEdge.symm wd.contracted) := by
  classical
  rw [StableSourceMatrix.labelling_matrix_eq,
    outLabK_row_symm_facet m wd wallStar anchorBlock hAnchor pairing position geometry hBg,
    outLabK_targetEdge_col m wd wallStar anchorBlock hAnchor pairing position geometry hBg]
  exact GeneralKRowEquiv.matrix_bridgeRow_new_pos
    (anchorHyp m wd wallStar anchorBlock hAnchor pairing position geometry hBg)

/-- **The corner entry is `1 / k₁`**, with `k₁ = |A₋ ∩ A₊|` the index of the
bridge (`k₁ + 2K + 1 = k_α + k_β`, `Position.bridgeSheets_card_add_two_K`). -/
theorem matrix_outLabK_corner
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry) :
    GluingDatum.LengthMatrixPresentation.matrix
        (outLabK m wd wallStar anchorBlock hAnchor pairing position geometry hBg).presentation
        (label m.base) (wd.fullDim.labelling.targetEdge.symm wd.contracted) =
      1 / (position.split.bridgeSheets.card : ℚ) := by
  classical
  rw [StableSourceMatrix.labelling_matrix_eq,
    outLabK_row_symm_facet m wd wallStar anchorBlock hAnchor pairing position geometry hBg,
    outLabK_targetEdge_col m wd wallStar anchorBlock hAnchor pairing position geometry hBg]
  refine (GeneralKRowEquiv.matrix_bridgeRow_new
    (anchorHyp m wd wallStar anchorBlock hAnchor pairing position geometry hBg)).trans ?_
  have h₁ := position.candidate_newSourceEdge_index vConn vGen vNG geometry
  have h₂ := position.bridgeSheets_card_add_two_K
  have hEq : (cK).datum.sourceEdgeIndex ((cK).newSourceEdge position.split.bridge) =
      position.split.bridgeSheets.card := by
    have : (cK).datum.sourceEdgeIndex ((cK).newSourceEdge position.split.bridge) + 2 *
        position.split.K + 1 = position.split.bridgeSheets.card + 2 * position.split.K + 1 :=
      h₁.trans h₂.symm
    omega
  rw [hEq]

/-- **The common minor**: `AgreeOffColumn` against the incoming honest matrix. -/
theorem agreeOffColumn_outLabK
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry) :
    AgreeOffColumn (GluingDatum.LengthMatrixPresentation.matrix wd.fullDim.labelling.presentation)
      (GluingDatum.LengthMatrixPresentation.matrix
        (outLabK m wd wallStar anchorBlock hAnchor pairing position geometry hBg).presentation)
      (wd.fullDim.labelling.targetEdge.symm wd.contracted) := by
  intro i j hj
  by_cases hi : i = label m.base
  · rw [hi, matrix_outLabK_facet_eq_zero m wd wallStar anchorBlock hAnchor pairing position
      geometry hBg j hj]
    exact NonTrivalentValencyTwoExit.incoming_facet_eq_zero wd.cover wd.fullDim wd.coordinates
      (label m.base) wd.hZeroCoord wd.hPosCoord wd.hFacetZero j hj
  · exact (matrix_outLabK_eq_incoming m wd wallStar anchorBlock hAnchor pairing position geometry
      hBg i j hi hj).symm

/-- **Nonsingularity of the outgoing matrix.** -/
theorem det_outLabK_ne_zero
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry) :
    (GluingDatum.LengthMatrixPresentation.matrix
      (outLabK m wd wallStar anchorBlock hAnchor pairing position geometry hBg).presentation).det ≠
      0 :=
  NonTrivalentLinkMatrix.det_ne_zero
    (agreeOffColumn_outLabK m wd wallStar anchorBlock hAnchor pairing position geometry hBg)
    (fun j hj ↦ NonTrivalentValencyTwoExit.incoming_facet_eq_zero wd.cover wd.fullDim
      wd.coordinates (label m.base) wd.hZeroCoord wd.hPosCoord wd.hFacetZero j hj)
    (fun j hj ↦ matrix_outLabK_facet_eq_zero m wd wallStar anchorBlock hAnchor pairing position
      geometry hBg j hj)
    wd.fullDim.det_ne_zero
    (matrix_outLabK_corner_pos m wd wallStar anchorBlock hAnchor pairing position geometry hBg).ne'

/-! ## 7.  The outgoing full-dimensional presentation -/

/-- **The outgoing full-dimensional presentation of the general-`K` candidate**,
on the incoming chart.  Validity is `Position.candidate_datum_valid`; the source
genus, trivalence and path ends come from `GeneralKSourceFacts`; the labelling,
its common minor and its nonsingularity are proved above. -/
noncomputable def outgoingFDK
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry) :
    FullDimensionalSourcePresentation (cK).datum coordinate :=
  NonTrivalentValencyTwoExit.ofTypeChange wd.fullDim
    (position.candidate_datum_valid vConn vGen vNG geometry vVal)
    (TargetExpansion.graph_connected _ _ _ vConn)
    ((TargetExpansion.graph_genus _ _ _).trans vGen)
    ((TargetExpansion.graph_edge_card _ _ _).trans
      (WallDegeneration.edge_card_contract wd.hab wd.hOne).symm)
    ((GeneralKSourceFacts.candidate_sourceGenus m wd wallStar anchorBlock hAnchor pairing position
      geometry hBg).trans
      (NonTrivalentValencyTwoExit.genus_sourceGraph_contractDatum wd.cover wd.hc wd.hab wd.hOne
        (wd.hForest m)))
    (outLabK m wd wallStar anchorBlock hAnchor pairing position geometry hBg)
    (det_outLabK_ne_zero m wd wallStar anchorBlock hAnchor pairing position geometry hBg)
    (GeneralKSourceFacts.candidate_trivalent m wd wallStar anchorBlock hAnchor pairing position
      geometry hBg)
    (GeneralKSourceFacts.hasPathEnds_candidate m wd wallStar anchorBlock hAnchor pairing position
      geometry hBg)

@[simp] theorem outgoingFDK_labelling
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry) :
    (outgoingFDK m wd wallStar anchorBlock hAnchor pairing position geometry hBg).labelling =
      outLabK m wd wallStar anchorBlock hAnchor pairing position geometry hBg :=
  rfl

/-- **The outgoing presentation with its dictionary.**  Over the localized canonical
background, the general-`K` candidate has an outgoing full-dimensional
presentation on the incoming chart whose matrix agrees with the incoming one
off the wall column, and whose labelling is the explicit dictionary that
`GeneralKLink.exists_typeChangeLinkK_of_equivalence` asks for:
* the wall column is the new target occurrence;
* every other column keeps its incoming target occurrence;
* the rows are `rowEquivK` (retained rows to the gauged wall rows, the bridge
  row to `none`), then the gauge back to the wall datum, the wall datum's own
  labelling, and the row chart (`none` to the vanishing row `label m.base`). -/
theorem exists_outgoingFD
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry) :
    ∃ fdOut : FullDimensionalSourcePresentation (cK).datum coordinate,
      AgreeOffColumn wd.incomingMatrix
        (GluingDatum.LengthMatrixPresentation.matrix fdOut.labelling.presentation) wd.column ∧
      fdOut.labelling.targetEdge wd.column =
        occurrenceEquiv (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ (cK).right none ∧
      (∀ j : {column : coordinate //
          column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted},
        fdOut.labelling.targetEdge j.1 =
          occurrenceEquiv (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ (cK).right
            (some (StablePathFacetContraction.punctureTargetEquiv wd.fullDim.labelling
              wd.hc wd.hab wd.hOne j))) ∧
      fdOut.labelling.row =
        (rowEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg).trans
          ((Equiv.optionCongr ((gaugeRow m wd wallStar anchorBlock hAnchor pairing position).symm.trans
            (vWallLab).row)).trans vRowChart) := by
  refine ⟨outgoingFDK m wd wallStar anchorBlock hAnchor pairing position geometry hBg,
    ?_, ?_, ?_, rfl⟩
  · have h := agreeOffColumn_outLabK m wd wallStar anchorBlock hAnchor pairing position geometry
      hBg
    rw [wd.targetEdge_symm_contracted] at h
    exact h
  · have h := outLabK_targetEdge_col m wd wallStar anchorBlock hAnchor pairing position geometry
      hBg
    rw [wd.targetEdge_symm_contracted] at h
    exact h
  · exact outLabK_targetEdge_ne m wd wallStar anchorBlock hAnchor pairing position geometry hBg

/-- **The bare existence statement**: an outgoing full-dimensional presentation whose
matrix agrees with the incoming one off the wall column, over `LocalCanonicalBackground`
and with no other hypothesis. -/
theorem exists_outgoingFD_skeleton
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry) :
    ∃ fdOut : FullDimensionalSourcePresentation (cK).datum coordinate,
      AgreeOffColumn wd.incomingMatrix
        (GluingDatum.LengthMatrixPresentation.matrix fdOut.labelling.presentation) wd.column := by
  obtain ⟨fdOut, h, -⟩ := exists_outgoingFD m wd wallStar anchorBlock hAnchor pairing position
    geometry hBg
  exact ⟨fdOut, h⟩

omit geometry in
/-- **The outgoing presentation with no hypothesis at all**: every general-`K` position at
the wall data of the outer walk carries a localized canonical background over which the
candidate has the outgoing presentation, the common minor and the labelling dictionary. -/
theorem exists_background_outgoingFD :
    ∃ geometry : GeneralKReceipts.PairingBackground position.datum wallStar pairing
        anchorBlock.1,
      GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
        position geometry ∧
      ∃ fdOut : FullDimensionalSourcePresentation
          (candK m wd wallStar anchorBlock hAnchor pairing position geometry).datum coordinate,
        AgreeOffColumn wd.incomingMatrix
          (GluingDatum.LengthMatrixPresentation.matrix fdOut.labelling.presentation)
          wd.column ∧
        fdOut.labelling.targetEdge wd.column =
          occurrenceEquiv (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
            (candK m wd wallStar anchorBlock hAnchor pairing position geometry).right none ∧
        ∀ j : {column : coordinate //
            column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted},
          fdOut.labelling.targetEdge j.1 =
            occurrenceEquiv (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
              (candK m wd wallStar anchorBlock hAnchor pairing position geometry).right
              (some (StablePathFacetContraction.punctureTargetEquiv wd.fullDim.labelling
                wd.hc wd.hab wd.hOne j)) := by
  obtain ⟨geometry, hBg⟩ := GeneralKSourceFacts.exists_localCanonicalBackground m wd wallStar
    anchorBlock hAnchor pairing position
  obtain ⟨fdOut, h₁, h₂, h₃, -⟩ := exists_outgoingFD m wd wallStar anchorBlock hAnchor pairing
    position geometry hBg
  exact ⟨geometry, hBg, fdOut, h₁, h₂, h₃⟩

end Wall

end DraismaVargas.Count.GeneralKExit
