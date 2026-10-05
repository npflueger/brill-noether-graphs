module

public import DraismaVargasCount.ValencyThreeGeneral

@[expose] public section

/-!
# The column receipt of a type-change link, at every facet datum

**Source.**  Vargas, Part II (arXiv:2609.09109), the combinatorial setup of the section on
changing combinatorial type (`subsec-setup-determinants`): the outgoing labelling at a
non-trivalent wall re-uses the wall labelling on every retained column and puts the new target
occurrence into the vanishing column.  This module proves that the type-change links of the
Part I library carry this column dictionary explicitly, and deduces the facet-level predicates
`ColumnLinkReceipts` and `MetricLinkReceipts` of `ValencyThreeGeneral` at every facet datum.
Through `ValencyTwoSplit`, `ValencyThreeCensus` and `GeneralKExitSetup` these feed the type
changes of the genus-six assembly (`Assembly.typeChanges_genusSix`, step 3).  The module builds
on `FacetAdapterPilot` and `LinkReceiptExport`.

## What is proved

* **§1, the data-carrying receipt.**  `ColumnReceipt link` strengthens
  `FacetAdapterPilot.LinkLimitReceipt` (`ColumnReceipt.toLinkLimitReceipt`): besides
  `column_new`, it carries an *explicit* `GeometricDatumIso link.base wd.wallDatum` whose
  inverse target map sends the wall labelling's column `j` (`punctureTargetEquiv`) to the
  base edge the outgoing labelling puts in column `j` (as an old occurrence of the regrown
  target).  `ColumnReceiptLink m wd := ∃ link, ColumnReceipt link`.
* **§2, the wall labelling's target dictionary.**  `exists_wallLabelling_two'`:
  `NonTrivalentValencyTwoBaseOneRowDictionary.exists_wallLabelling_two` with a third
  conjunct `hTarget` -- in all three sub-cases (`2 + 2`, `1 + 3`, `3 + 1`) the labelling's
  `targetEdge` is `punctureTargetEquiv` (definitionally: both `wallLabelling` and
  `wallLabelling'` are built that way).  The original statement does not export this.
* **§3, the six exits carry the column receipt.**
  `columnReceipt_threeIII`, `columnReceipt_four`, `columnReceipt_simple` with no new
  hypothesis; `columnReceipt_free`, `columnReceipt_baseOne`, `columnReceipt_split` with
  `hTarget` on the supplied wall labelling `labelling₀`.  In every case the base isomorphism
  is the one of `LinkReceiptExport` (`refl`, or one/two `DatumIso.ofSheetRelabeling`, whose
  target maps are `Equiv.refl`), and the column clause is `targetEdge_reindex` at
  `colChart.symm j = some j` (`colChart_symm_of_ne`) followed by `rfl` (the candidate
  labelling is `optionCongr labelling₀.targetEdge` then `occurrenceEquiv`), plus `hTarget`
  where `labelling₀` is supplied.
* **§4--§6, the dispatchers with the column receipt.**  The valency-four, -three and -two
  dispatch of `LinkReceiptExport` (itself a copy of the dispatchers of the Part I library),
  copied with `ReceiptLink` read as `ColumnReceiptLink`, the leaves replaced by §3's, the
  three `exists_wallLabelling_two` calls replaced by `exists_wallLabelling_two'` (threading
  `hTarget` through `columnReceiptLink_of_prescribedMergedMoveAny` and
  `columnReceiptLink_of_thick_rows`), and the swap/mirror wrappers transporting `base_col`
  (both keep every field the clause mentions).  Headline `exists_link_with_columnReceipt`:
  at **every** wall datum of every Whitehead move, of every valency,
  `∃ link, ColumnReceipt link`, no hypothesis.
* **§7, the facet level.**  `column_of_receipt`: a column receipt at the synthetic facet
  arrival gives the limit isomorphism `ColumnLinkReceipts` asks for -- the same composite as
  `FacetAdapterPilot.ofLeft_eq_ofRight_farRegrowth`,
  `((limitIsoWallDatum …).trans hbase.symm).trans far.symm`, now with its target map
  computed column by column (`unfoldEdge_contractDatumIsoOfEdgeEq`,
  `seedDatumIso_targetEdge`, `W4LimitContraction.occurrenceEquiv_edgeEquiv`).
  **`columnLinkReceipts`** and **`columnLinkReceipts_rev`** (both ways, with no hypothesis
  beyond the binders), `metricLinkReceipts`, `metricLinkReceipts_rev`, the unconditional
  metric existence transfers `exists_odd_mSpecializesRight/Left`, and the restatement
  **`facetParity_of_metricUniqueness`** with the receipt binders discharged (only `huniqL`,
  `huniqR` left).  The closing `example` inhabits `ColumnReceiptLink` at `cat_step`.

## Remarks

* Every exit builds its base isomorphism explicitly (never by an opaque `Nonempty`
  argument: the `base_iso` fields of `LinkReceiptExport` are all `⟨explicit iso⟩`), and
  every exit's outgoing labelling is the reindexed wall labelling on retained columns, by
  definition.  The one place the column dictionary is *hidden* is not an exit but the
  valency-two wall labelling: `exists_wallLabelling_two` is an existential whose witness's
  `targetEdge` is not exported, and the three valency-two exits take `labelling₀` as a
  hypothesis constrained only on rows and matrix entries.  §2 re-proves that lemma with the
  target dictionary; nothing else is needed.
* At `cat_step` the column receipt holds as an instance of the general statement (the
  closing `example`).
* No exit relabels a retained column: under the base isomorphism (identity on target edges
  at every exit) the outgoing column `j` is the wall datum's column `j`.  `SameMetricLimit`
  needs no reading up to a permutation.

## What is not proved here

* **`FacetParity` is not proved here at any step.**  `facetParity_of_metricUniqueness` takes
  exactly `huniqL`, `huniqR` (labelled-metric uniqueness on each side), and these do not hold
  at every step (see the remark before it); the type changes of the assembly use the census
  of `FacetCensus` instead.
* **The link `moveLink` / `link_all` returns is not shown to carry the column receipt**
  (a `Nonempty.some` cannot be inspected); `ColumnLinkReceipts` is existential in the link,
  and some link carries it.
* **Duplication.**  §4--§6 duplicate the dispatch of `LinkReceiptExport` (about 1 250 lines),
  which itself duplicates the dispatchers of the Part I library; §2 duplicates
  `exists_wallLabelling_two` (40 lines).  If one of those dispatchers changes, neither copy
  follows it.  The duplication would disappear if the original statements were strengthened
  in place (`ReceiptLink` to `ColumnReceiptLink`, `exists_wallLabelling_two` to the primed
  form).
* `3 ≤ degree` (the `MemberSeed` input of `FacetAdapterPilot`) remains explicit in the
  existence transfers and in `facetParity_of_metricUniqueness`; `2 ≤ degree` in the receipts.
* New `Prop`s: `ColumnReceipt` (`LinkLimitReceipt` plus the column clause, strictly
  stronger in form, `ColumnReceipt.toLinkLimitReceipt`; consumer `column_of_receipt`;
  inhabited at `cat_step`) and `ColumnReceiptLink` (definitionally
  `∃ link, ColumnReceipt link`).  Both are proved at every wall datum, so neither is an open
  input.
-/

set_option autoImplicit false

namespace DraismaVargas.Count.ColumnReceiptExport

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.OuterWalk
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.Count (GeometricDatumIso)

/-! ## 1.  The data-carrying receipt -/

section Receipt

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] {degree : ℕ}
  {graph : CubicDartGraph D V} {label : D → coordinate} {m : graph.MoveData}
  {arrival : FacetArrival degree graph label (label m.base)} {wd : WallData arrival}

/-- **The column receipt of a type-change link**: `FacetAdapterPilot.LinkLimitReceipt` with
the base isomorphism made explicit and tied to the column labels.  `column_new`: the outgoing
vanishing column is the regrown occurrence (as in `LinkLimitReceipt`).  `base_col`: a geometric
isomorphism of the link's base with the wall datum under which, for every retained column
`j`, the outgoing labelling's target edge of `j` is the old occurrence (in the regrown
target) over the base edge corresponding to the wall labelling's edge of `j`
(`punctureTargetEquiv`, the incoming target edge of `j`, folded).

It is `LinkLimitReceipt` plus the column clause (`toLinkLimitReceipt`), is consumed by
`column_of_receipt`, and is proved at every wall datum (`exists_link_with_columnReceipt`). -/
structure ColumnReceipt (link : TypeChangeLink m wd) : Prop where
  column_new : link.outgoingFD.labelling.targetEdge wd.column =
    occurrenceEquiv (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
      link.candidate.right none
  base_col : ∃ iso : GeometricDatumIso link.base wd.wallDatum,
    ∀ j : {column : coordinate // column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted},
      link.outgoingFD.labelling.targetEdge j.1 =
        occurrenceEquiv (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
          link.candidate.right
          (some (iso.targetEdge.symm (StablePathFacetContraction.punctureTargetEquiv
            wd.fullDim.labelling wd.hc wd.hab wd.hOne j)))

/-- A column receipt forgets to `FacetAdapterPilot.LinkLimitReceipt`. -/
theorem ColumnReceipt.toLinkLimitReceipt {link : TypeChangeLink m wd} (h : ColumnReceipt link) :
    FacetAdapterPilot.LinkLimitReceipt link :=
  ⟨h.column_new, h.base_col.elim fun iso _ ↦ ⟨iso⟩⟩

/-- **The column-receipt-carrying link**: definitionally
`∃ link : TypeChangeLink m wd, ColumnReceipt link`. -/
abbrev ColumnReceiptLink {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
    {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] {degree : ℕ}
    {graph : CubicDartGraph D V} {label : D → coordinate} (m : graph.MoveData)
    {arrival : FacetArrival degree graph label (label m.base)} (wd : WallData arrival) : Prop :=
  ∃ link : TypeChangeLink m wd, ColumnReceipt link

end Receipt

/-! ## 2.  The valency-two wall labelling, with its target dictionary -/

section WallLabelling

open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.WallDegeneration

variable {targetIn : CFGraph} {deg : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (cover : GluingDatum targetIn deg)
  (fd : FullDimensionalSourcePresentation cover coordinate)
  {a b : targetIn.V} {contracted : targetIn.edges}
  (hc : (contracted : targetIn.V × targetIn.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges targetIn a b = 1)
  (hForest : ContractionForest cover a b contracted)
  (facet : coordinate)
  (wallStar : TwoStar (contract targetIn hab hOne) ⟨a, hab⟩)

include wallStar in
/-- **`NonTrivalentValencyTwoBaseOneRowDictionary.exists_wallLabelling_two` with the target
dictionary exported.**  The same proof, verbatim, with one more conjunct: in all three
sub-cases (`2 + 2`, `1 + 3`, `3 + 1`) the labelling it produces reads column `j` as the
incoming target edge of `j`, folded (`punctureTargetEquiv`, definitionally). -/
theorem exists_wallLabelling_two'
    (coordinates : coordinate → ℚ)
    (hRows : ∀ row, row ≠ facet →
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates row ≠ 0)
    (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
    (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
      0 < coordinates column)
    (hFacetZero :
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates facet = 0) :
    ∃ wallLab : StableLengthMatrixLabelling (contractDatum cover hc hab hOne)
        {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted},
      (∀ p : StablePath (contractDatum cover hc hab hOne),
        (wallLab.row p).1 =
          Equiv.swap facet (fd.labelling.targetEdge.symm contracted)
            (fd.labelling.row (incomingRow cover fd hc hab hOne
              (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
                hForest) hForest p))) ∧
      (∀ (p : StablePath (contractDatum cover hc hab hOne))
        (column : {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted}),
        GluingDatum.LengthMatrixPresentation.matrix wallLab.presentation
            (wallLab.row p) column =
          GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
            (fd.labelling.row (incomingRow cover fd hc hab hOne
              (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
                hForest) hForest p)) column.1) ∧
      ∀ j, wallLab.targetEdge j = punctureTargetEquiv fd.labelling hc hab hOne j := by
  classical
  have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
    hForest
  by_cases hA : (GluingDatum.incidentEdges a).card = 1
  · refine ⟨LeafFacetNoReturn.wallLabelling' cover fd hc hab hOne hCompat hForest coordinates
      facet (NonTrivalentValencyTwoLeafDictionary.noContractedReturnOffRow_of_leaf cover fd
        hc hab hOne wallStar coordinates facet hZeroCoord hPosCoord hFacetZero hA)
      hRows hZeroCoord hPosCoord hFacetZero, fun _ ↦ rfl, ?_, fun _ ↦ rfl⟩
    exact fun p column ↦ LeafFacetNoReturn.matrix_wallLabelling' cover fd hc hab hOne hCompat
      hForest coordinates facet _ hRows hZeroCoord hPosCoord hFacetZero p column
  · by_cases hB : (GluingDatum.incidentEdges b).card = 1
    · refine ⟨LeafFacetNoReturn.wallLabelling' cover fd hc hab hOne hCompat hForest coordinates
        facet (NonTrivalentValencyTwoLeafDictionary.noContractedReturnOffRow_of_leaf_right
          cover fd hc hab hOne wallStar coordinates facet hZeroCoord hPosCoord hFacetZero hB)
        hRows hZeroCoord hPosCoord hFacetZero, fun _ ↦ rfl, ?_, fun _ ↦ rfl⟩
      exact fun p column ↦ LeafFacetNoReturn.matrix_wallLabelling' cover fd hc hab hOne hCompat
        hForest coordinates facet _ hRows hZeroCoord hPosCoord hFacetZero p column
    · have hLeftMem := (WallProgress.endpoints_of_contraction cover hc hab hOne fd.valid
        fd.changeMinimal).2.1
      have hRightMem := (WallProgress.endpoints_of_contraction cover hc hab hOne fd.valid
        fd.changeMinimal).2.2.2.1
      have hLeft : 2 ≤ (GluingDatum.incidentEdges a).card := by omega
      have hRight : 2 ≤ (GluingDatum.incidentEdges b).card := by omega
      have hNoReturn : NoContractedReturn cover contracted :=
        noContractedReturn_of_nonleaf cover fd hc hLeft hRight
      refine ⟨wallLabelling cover fd hc hab hOne hCompat hForest hNoReturn coordinates facet
        hRows hZeroCoord hPosCoord hFacetZero, fun _ ↦ rfl, ?_, fun _ ↦ rfl⟩
      exact fun p column ↦ matrix_wallLabelling cover fd hc hab hOne hCompat hForest hNoReturn
        coordinates facet hRows hZeroCoord hPosCoord hFacetZero p column

end WallLabelling

/-! ## 3.  The six exits carry the column receipt

The base isomorphisms are those of `LinkReceiptExport.receipt_*`; the column clause is
`targetEdge_reindex` at `colChart.symm j = some j`, then `rfl` (or `hTarget`). -/

section Leaves

/-- The column chart reads a retained column as `some` of itself. -/
theorem colChart_symm_of_ne {targetIn : CFGraph} {deg : ℕ} {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate] {cover : GluingDatum targetIn deg}
    (fd : FullDimensionalSource.FullDimensionalSourcePresentation cover coordinate)
    {contracted : targetIn.edges}
    (j : {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted}) :
    (NonTrivalentValencyTwoExit.colChart cover fd (contracted := contracted)).symm j.1 = some j :=
  Equiv.optionSubtypeNe_symm_of_ne j.2

section ThreeIII

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)
  {wallStar : ThirdEquation.ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : W4Assembly.WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : NonTrivalentValencyThreeAnchor.ThreeBranchAnchor
    (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hNoGlue : W4StableSource.DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
  (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)
  (hPathEnds : W4StableSource.HasPathEnds
    (NonTrivalentValencyThreeCandidate.Prescribed.validCandidate src hNoGlue hValid).datum)

/-- **Valency three, Type III** (the base is the wall datum itself). -/
theorem columnReceipt_threeIII
    (tracks : Tracks (NonTrivalentValencyThreeExit.wallOutgoingFD m wd src hNoGlue hValid
      hPathEnds) (graph.move m) label) :
    ColumnReceipt (NonTrivalentValencyThreeExit.typeChangeLink_of_receipts m wd src hNoGlue
      hValid hPathEnds tracks) := by
  refine ⟨(FacetAdapterPilot.linkLimitReceipt_valencyThreeTypeIII m wd src hNoGlue hValid
    hPathEnds tracks).column_new, GeometricDatumIso.refl _, fun j ↦ ?_⟩
  exact congrArg (NonTrivalentValencyThreeRowEquiv.labelling src hNoGlue hValid
    (NonTrivalentValencyTwoExit.wallLab wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m)
      (NonTrivalentValencyThreeExit.noContractedReturn_of_valency_three m wd wallStar)
      wd.coordinates (label m.base) wd.hRows wd.hZeroCoord wd.hPosCoord wd.hFacetZero)).targetEdge
    (colChart_symm_of_ne wd.fullDim j)

end ThreeIII

section Four

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

/-- **Valency four** (`PrescribedPairing.gaugedData` is one sheet relabelling). -/
theorem columnReceipt_four
    (tracks : Tracks (NonTrivalentValencyFourExit.wallOutgoingFD m wd wallStar anchorBlock
      hAnchor pairing) (graph.move m) label) :
    ColumnReceipt (NonTrivalentValencyFourExit.typeChangeLink_of_receipts m wd wallStar
      anchorBlock hAnchor pairing tracks) := by
  refine ⟨?_, (GeometricDatumIso.ofStrict (Count.Transport.DatumIso.ofSheetRelabeling _)).symm,
    fun j ↦ (LinkReceiptExport.targetEdge_reindex _ _ _ (colChart_symm_of_ne wd.fullDim j)).trans
      rfl⟩
  have h2 : (NonTrivalentValencyTwoExit.colChart wd.cover wd.fullDim
      (contracted := wd.contracted)).symm wd.column = none := by
    rw [← wd.targetEdge_symm_contracted]
    exact Equiv.optionSubtypeNe_symm_self _
  exact (LinkReceiptExport.targetEdge_reindex _ _ _ h2).trans rfl

end Four

section Free
open NonTrivalentValencyTwoRowEquiv NonTrivalentValencyTwoCandidate NonTrivalentValencyTwoAnchor
  W2R1Target
variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)
  {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hOrd : OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
    anchorBlk)
  (labelling₀ : StableLengthMatrixLabelling (contractDatum wd.cover wd.hc wd.hab wd.hOne)
    {column : coordinate // column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted})
  (hRowVal : ∀ p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne),
    (labelling₀.row p).1 =
      Equiv.swap (label m.base) (wd.fullDim.labelling.targetEdge.symm wd.contracted)
        (wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (WallAdmissibility.danglingCompatible_of_contractionForest wd.cover wd.hc wd.hab
            wd.hOne (wd.hForest m)) (wd.hForest m) p)))
  (hMatrixWall : ∀ (p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (column : {column : coordinate //
      column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted}),
    GluingDatum.LengthMatrixPresentation.matrix labelling₀.presentation
        (labelling₀.row p) column =
      GluingDatum.LengthMatrixPresentation.matrix wd.fullDim.labelling.presentation
        (wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (WallAdmissibility.danglingCompatible_of_contractionForest wd.cover wd.hc wd.hab
            wd.hOne (wd.hForest m)) (wd.hForest m) p)) column.1)

/-- **Valency two, Base II merge** (the base is the wall datum itself). -/
theorem columnReceipt_free
    (hTarget : ∀ j, labelling₀.targetEdge j =
      punctureTargetEquiv wd.fullDim.labelling wd.hc wd.hab wd.hOne j)
    (tracks : Tracks (NonTrivalentValencyTwoExitFree.wallOutgoingFD' m wd src sel hOrd labelling₀
      hRowVal hMatrixWall) (graph.move m) label) :
    ColumnReceipt (NonTrivalentValencyTwoExitFree.typeChangeLink_of_receipts_free m wd src sel
      hOrd labelling₀ hRowVal hMatrixWall tracks) := by
  refine ⟨?_, GeometricDatumIso.refl _,
    fun j ↦ (LinkReceiptExport.targetEdge_reindex _ _ _ (colChart_symm_of_ne wd.fullDim j)).trans
      (congrArg (fun z ↦ occurrenceEquiv _ _ _ (some z)) (hTarget j))⟩
  have h2 : (NonTrivalentValencyTwoExit.colChart wd.cover wd.fullDim
      (contracted := wd.contracted)).symm wd.column = none := by
    rw [← wd.targetEdge_symm_contracted]
    exact Equiv.optionSubtypeNe_symm_self _
  exact (LinkReceiptExport.targetEdge_reindex _ _ _ h2).trans rfl

end Free

section BaseOne
open NonTrivalentValencyTwoGauge NonTrivalentValencyTwoBaseOne W2R1Target
variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)
  (wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
  (anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
  (thickSheet thinSheet : Fin degree)
  (labelling₀ : StableLengthMatrixLabelling (contractDatum wd.cover wd.hc wd.hab wd.hOne)
    {column : coordinate //
      column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted})
  (setup : BaseOneSetup
    (gaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      thickSheet thinSheet) wallStar
    (gaugedAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      thickSheet thinSheet))
  (hGauged : (gaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
    thickSheet thinSheet).Valid)
  (hOrd : NonTrivalentValencyTwoRowEquiv.OrdinaryTrivalent
    (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk)
  (hRowVal : ∀ p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne),
    (labelling₀.row p).1 =
      Equiv.swap (label m.base) (wd.fullDim.labelling.targetEdge.symm wd.contracted)
        (wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (WallAdmissibility.danglingCompatible_of_contractionForest wd.cover wd.hc wd.hab
            wd.hOne (wd.hForest m)) (wd.hForest m) p)))
  (hMatrixWall : ∀ (p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (column : {column : coordinate //
      column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted}),
    GluingDatum.LengthMatrixPresentation.matrix labelling₀.presentation
        (labelling₀.row p) column =
      GluingDatum.LengthMatrixPresentation.matrix wd.fullDim.labelling.presentation
        (wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (WallAdmissibility.danglingCompatible_of_contractionForest wd.cover wd.hc wd.hab
            wd.hOne (wd.hForest m)) (wd.hForest m) p)) column.1)

/-- **Valency two, Base I** (the gauge `NonTrivalentValencyTwoGauge.gaugedData` is one sheet
relabelling). -/
theorem columnReceipt_baseOne
    (hTarget : ∀ j, labelling₀.targetEdge j =
      punctureTargetEquiv wd.fullDim.labelling wd.hc wd.hab wd.hOne j)
    (tracks : Tracks (NonTrivalentValencyTwoBaseOneExit.wallOutgoingFD m wd wallStar anchorBlk
      thickSheet thinSheet labelling₀ setup hGauged hOrd hRowVal hMatrixWall) (graph.move m) label) :
    ColumnReceipt (NonTrivalentValencyTwoBaseOneExit.typeChangeLink_of_receipts_baseOne m wd
      wallStar anchorBlk thickSheet thinSheet labelling₀ setup hGauged hOrd hRowVal hMatrixWall
      tracks) := by
  refine ⟨?_, (GeometricDatumIso.ofStrict (Count.Transport.DatumIso.ofSheetRelabeling _)).symm,
    fun j ↦ (LinkReceiptExport.targetEdge_reindex _ _ _ (colChart_symm_of_ne wd.fullDim j)).trans
      (congrArg (fun z ↦ occurrenceEquiv _ _ _ (some z)) (hTarget j))⟩
  have h2 : (NonTrivalentValencyTwoExit.colChart wd.cover wd.fullDim
      (contracted := wd.contracted)).symm wd.column = none := by
    rw [← wd.targetEdge_symm_contracted]
    exact Equiv.optionSubtypeNe_symm_self _
  exact (LinkReceiptExport.targetEdge_reindex _ _ _ h2).trans rfl

end BaseOne

section Split
open NonTrivalentValencyTwoSplitGauge NonTrivalentValencyTwoSplitCandidate W2R1Target
  NonTrivalentValencyTwoSplitRows
variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)
  (wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
  (anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
  (thickSheet thinSheet : Fin degree)
  (labelling₀ : StableLengthMatrixLabelling (contractDatum wd.cover wd.hc wd.hab wd.hOne)
    {column : coordinate //
      column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted})
  (ra : SplitAnchor
    (splitGaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      thickSheet thinSheet) wallStar
    (splitGaugedAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      thickSheet thinSheet))
  (hGauged : (splitGaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
    anchorBlk thickSheet thinSheet).Valid)
  (hOrdGauged : NonTrivalentValencyTwoRowEquiv.OrdinaryTrivalent (splitGaugedData
    (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet thinSheet)
    ⟨wd.a, wd.hab⟩
    (splitGaugedAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      thickSheet thinSheet))
  (hRowVal : ∀ p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne),
    (labelling₀.row p).1 =
      Equiv.swap (label m.base) (wd.fullDim.labelling.targetEdge.symm wd.contracted)
        (wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (WallAdmissibility.danglingCompatible_of_contractionForest wd.cover wd.hc wd.hab
            wd.hOne (wd.hForest m)) (wd.hForest m) p)))
  (hMatrixWall : ∀ (p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (column : {column : coordinate //
      column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted}),
    GluingDatum.LengthMatrixPresentation.matrix labelling₀.presentation
        (labelling₀.row p) column =
      GluingDatum.LengthMatrixPresentation.matrix wd.fullDim.labelling.presentation
        (wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (WallAdmissibility.danglingCompatible_of_contractionForest wd.cover wd.hc wd.hab
            wd.hOne (wd.hForest m)) (wd.hForest m) p)) column.1)

/-- **Valency two, Configuration A split** (the gauge
`NonTrivalentValencyTwoSplitGauge.splitGaugedData` is one sheet relabelling). -/
theorem columnReceipt_split
    (hTarget : ∀ j, labelling₀.targetEdge j =
      punctureTargetEquiv wd.fullDim.labelling wd.hc wd.hab wd.hOne j)
    (tracks : Tracks (NonTrivalentValencyTwoSplitExit.wallOutgoingFD m wd wallStar anchorBlk
      thickSheet thinSheet labelling₀ ra hGauged hOrdGauged hRowVal hMatrixWall)
      (graph.move m) label) :
    ColumnReceipt (NonTrivalentValencyTwoSplitExit.typeChangeLink_of_receipts_split m wd
      wallStar anchorBlk thickSheet thinSheet labelling₀ ra hGauged hOrdGauged hRowVal
      hMatrixWall tracks) := by
  refine ⟨?_, (GeometricDatumIso.ofStrict (Count.Transport.DatumIso.ofSheetRelabeling _)).symm,
    fun j ↦ (LinkReceiptExport.targetEdge_reindex _ _ _ (colChart_symm_of_ne wd.fullDim j)).trans
      (congrArg (fun z ↦ occurrenceEquiv _ _ _ (some z)) (hTarget j))⟩
  have h2 : (NonTrivalentValencyTwoExit.colChart wd.cover wd.fullDim
      (contracted := wd.contracted)).symm wd.column = none := by
    rw [← wd.targetEdge_symm_contracted]
    exact Equiv.optionSubtypeNe_symm_self _
  exact (LinkReceiptExport.targetEdge_reindex _ _ _ h2).trans rfl

end Split

section Simple
open NonTrivalentValencyThreeSimpleCandidate ThirdEquation
variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)
  {wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (simpleBase : SimpleBase (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)

/-- **Valency three, Types I/II** (`SimpleBase.gaugedData` is two sheet relabellings). -/
theorem columnReceipt_simple
    (tracks : Tracks (NonTrivalentValencyThreeSimpleExit.wallOutgoingFD m wd simpleBase hValid)
      (graph.move m) label) :
    ColumnReceipt (NonTrivalentValencyThreeSimpleExit.typeChangeLink_of_receipts m wd
      simpleBase hValid tracks) := by
  refine ⟨?_, ((GeometricDatumIso.ofStrict (Count.Transport.DatumIso.ofSheetRelabeling _)).trans
    (GeometricDatumIso.ofStrict (Count.Transport.DatumIso.ofSheetRelabeling _))).symm,
    fun j ↦ (LinkReceiptExport.targetEdge_reindex _ _ _ (colChart_symm_of_ne wd.fullDim j)).trans
      rfl⟩
  have h2 : (NonTrivalentValencyTwoExit.colChart wd.cover wd.fullDim
      (contracted := wd.contracted)).symm wd.column = none := by
    rw [← wd.targetEdge_symm_contracted]
    exact Equiv.optionSubtypeNe_symm_self _
  exact (LinkReceiptExport.targetEdge_reindex _ _ _ h2).trans rfl

end Simple

end Leaves

/-! ## 4.  The swap and mirror wrappers transport the column receipt -/

section Wrappers

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)

theorem ColumnReceiptLink.nonempty (h : ColumnReceiptLink m wd) : Nonempty (TypeChangeLink m wd) :=
  let ⟨link, _⟩ := h; ⟨link⟩

/-- **The swap wrapper transports the column receipt** (as the wrapper of
`LinkReceiptExport` does the receipt): `NonTrivalentValencyFourDispatcher.linkOfSwap` keeps
`base`, `candidate` and `outgoingFD` literally, and `swapWallData` keeps every field of the
wall data. -/
theorem ColumnReceiptLink.ofSwap (hL : label (graph.op m.base) = label m.base)
    (h : ColumnReceiptLink m.swap (NonTrivalentValencyFourDispatcher.swapWallData m wd hL)) :
    ColumnReceiptLink m wd :=
  let ⟨link, hrec⟩ := h
  ⟨NonTrivalentValencyFourDispatcher.linkOfSwap m wd hL link, hrec.column_new, hrec.base_col⟩

/-- **The mirror wrapper transports the column receipt** (as the wrapper of
`LinkReceiptExport` does the receipt): `MoveMirror.linkOfMirror` changes only `tracks`. -/
theorem ColumnReceiptLink.ofMirror (hL : label (graph.op m.base) = label m.base)
    (h : ColumnReceiptLink (MoveMirror.mirror m) wd) : ColumnReceiptLink m wd :=
  let ⟨link, hrec⟩ := h
  ⟨MoveMirror.linkOfMirror m wd hL link, hrec.column_new, hrec.base_col⟩

end Wrappers

/-! ## 4b.  Valency four: `NonTrivalentValencyFourDispatcher.typeChangeLink_four` with the column
receipt

The proofs below are those of `NonTrivalentValencyFourDispatcher`, copied verbatim except that
the leaf returns the column receipt (`columnReceipt_four`) and the swap branch uses
`ColumnReceiptLink.ofSwap`.  They follow `LinkReceiptExport.receiptLink_of_orientation_four` /
`receiptLink_four`, with `ReceiptLink` read as `ColumnReceiptLink`. -/

section DispatchFour

open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero.PrescribedPairing
open DraismaVargas.LocalCases.NonTrivalentValencyFourTracks
open DraismaVargas.LocalCases.NonTrivalentValencyFourDispatcher

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)

theorem columnReceiptLink_of_orientation_four
    (h4 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 4)
    (hBase : wd.tracks.iso.dart
      (facetDartLeft m wd (W4TargetPairings.FourStar.of_card h4)) = m.base) :
    ColumnReceiptLink m wd := by
  classical
  set star₀ := W4TargetPairings.FourStar.of_card h4 with hstar₀
  obtain ⟨anchorBlock, hAnchor⟩ :=
    NonTrivalentUniqueFourValent.exists_wallBlock_nonDanglingValency_eq_four wd.cover
      wd.fullDim wd.hc wd.hab wd.hOne star₀ (wd.hCompat m) wd.coordinates (label m.base)
      wd.hZeroCoord wd.hPosCoord wd.hFacetZero
  obtain ⟨x, y, hx1, hy1, -, -, hStar⟩ := IncomingPairing.exists_movedStar_darts m wd
  -- the orientation identifies the two ends of the vanishing occurrence
  have hbd : IncomingPairing.baseDart m wd = facetDartLeft m wd star₀ :=
    IncomingPairing.baseDart_eq_facetDartLeft_four m wd star₀ hBase
  have hod : IncomingPairing.opBaseDart m wd = facetDartRight m wd star₀ :=
    IncomingPairing.opBaseDart_eq_facetDartRight_four m wd star₀ hBase
  have hxv : x.1.1 = leftEnd m wd := by rw [hx1, hbd]; rfl
  have hyv : y.1.1 = rightEnd m wd := by rw [hy1, hod]; rfl
  have hxInc : Incident wd.cover x.2.1.1 (leftEnd m wd) := by rw [← hxv]; exact x.2.2
  have hyInc : Incident wd.cover y.2.1.1 (rightEnd m wd) := by rw [← hyv]; exact y.2.2
  -- neither of them is the vanishing occurrence
  have hxmem : wd.tracks.iso.dart x ∈
      (Finset.univ.filter fun c ↦ (graph.move m).vert c = graph.vert m.base).erase m.base := by
    rw [hStar]
    exact Finset.mem_insert_self _ _
  have hymem : wd.tracks.iso.dart y ∈
      (Finset.univ.filter fun c ↦ (graph.move m).vert c = graph.vert m.base).erase m.base := by
    rw [hStar]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hxne : x.2.1 ≠ facetEdge m wd := row_ne_facet_of_mem_movedStar m wd x hxmem
  have hyne : y.2.1 ≠ facetEdge m wd := row_ne_facet_of_mem_movedStar m wd y hymem
  -- they descend to two survivors at the anchor
  have hTx : (x.2.1.1.1.1 : wd.coverTarget.edges) ≠ wd.contracted :=
    target_ne_contracted_of_incident_end m wd star₀ x.2.1 (leftEnd m wd)
      (incident_facetEdge_leftEnd m wd) hxInc hxne
  have hTy : (y.2.1.1.1.1 : wd.coverTarget.edges) ≠ wd.contracted :=
    target_ne_contracted_of_incident_end m wd star₀ y.2.1 (rightEnd m wd)
      (incident_facetEdge_rightEnd m wd) hyInc hyne
  have hIncX : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (descent m wd x.2.1 hTx).1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlock) := by
    have h := incident_descent m wd x.2.1 hTx hxInc
    rwa [sourceVertexMap_leftEnd_eq_anchorVertex m wd star₀ anchorBlock hAnchor] at h
  have hIncY : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (descent m wd y.2.1 hTy).1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlock) := by
    have h := incident_descent m wd y.2.1 hTy hyInc
    rw [← sourceVertexMap_leftEnd_eq_rightEnd m wd,
      sourceVertexMap_leftEnd_eq_anchorVertex m wd star₀ anchorBlock hAnchor] at h
    exact h
  -- the two target directions are different
  set sx : {edge : (contract wd.coverTarget wd.hab wd.hOne).edges //
      edge ∈ GluingDatum.incidentEdges
        (⟨wd.a, wd.hab⟩ : (contract wd.coverTarget wd.hab wd.hOne).V)} :=
    ⟨(descent m wd x.2.1 hTx).1.1.1,
      mem_incidentEdges_of_incident_anchor m wd anchorBlock _ hIncX⟩ with hsx
  set sy : {edge : (contract wd.coverTarget wd.hab wd.hOne).edges //
      edge ∈ GluingDatum.incidentEdges
        (⟨wd.a, wd.hab⟩ : (contract wd.coverTarget wd.hab wd.hOne).V)} :=
    ⟨(descent m wd y.2.1 hTy).1.1.1,
      mem_incidentEdges_of_incident_anchor m wd anchorBlock _ hIncY⟩ with hsy
  have hsne : sx ≠ sy := by
    intro hBad
    have hT : ((descent m wd x.2.1 hTx).1.1.1 :
        (contract wd.coverTarget wd.hab wd.hOne).edges) =
        star₀.edge (star₀.label.symm sx) := by
      show sx.1 = (star₀.label (star₀.label.symm sx)).1
      rw [Equiv.apply_symm_apply]
    have hT' : ((descent m wd y.2.1 hTy).1.1.1 :
        (contract wd.coverTarget wd.hab wd.hOne).edges) =
        star₀.edge (star₀.label.symm sx) := by
      show sy.1 = (star₀.label (star₀.label.symm sx)).1
      rw [Equiv.apply_symm_apply, hBad]
    have hsrc₀ := NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc
      wd.hab wd.hOne star₀ (wd.hForest m) anchorBlock hAnchor
    have hEqX := eq_sourceEdge_of_target m wd anchorBlock star₀ hsrc₀ (star₀.label.symm sx)
      (descent m wd x.2.1 hTx) hIncX hT
    have hEqY := eq_sourceEdge_of_target m wd anchorBlock star₀ hsrc₀ (star₀.label.symm sx)
      (descent m wd y.2.1 hTy) hIncY hT'
    have hEq : descent m wd x.2.1 hTx = descent m wd y.2.1 hTy :=
      Subtype.ext (hEqX.trans hEqY.symm)
    have hxy : x.2.1 = y.2.1 := by
      rw [← liftEdge_descent m wd x.2.1 hTx, ← liftEdge_descent m wd y.2.1 hTy, hEq]
    exact not_incident_both_ends m wd anchorBlock star₀ hAnchor x.2.1 hxInc
      (by rw [hxy]; exact hyInc) hTx
  -- relabel the star so that the two directions carry the labels 2 and 3
  set star := relabel star₀ sx sy with hstar
  have hs2 : star.edge 2 = (descent m wd x.2.1 hTx).1.1.1 := relabel_two star₀ sx sy hsne
  have hs3 : star.edge 3 = (descent m wd y.2.1 hTy).1.1.1 := relabel_three star₀ sx sy
  have hsrc := NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc
    wd.hab wd.hOne star (wd.hForest m) anchorBlock hAnchor
  have hGx : (descent m wd x.2.1 hTx).1 = hsrc.sourceEdge 2 :=
    eq_sourceEdge_of_target m wd anchorBlock star hsrc 2 (descent m wd x.2.1 hTx) hIncX hs2.symm
  have hGy : (descent m wd y.2.1 hTy).1 = hsrc.sourceEdge 3 :=
    eq_sourceEdge_of_target m wd anchorBlock star hsrc 3 (descent m wd y.2.1 hTy) hIncY hs3.symm
  have hLiftX : liftEdge m wd ⟨hsrc.sourceEdge 2, hsrc.sourceEdge_survives 2⟩ = x.2.1 := by
    rw [show (⟨hsrc.sourceEdge 2, hsrc.sourceEdge_survives 2⟩ :
      NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)) =
        descent m wd x.2.1 hTx from Subtype.ext hGx.symm]
    exact liftEdge_descent m wd x.2.1 hTx
  have hLiftY : liftEdge m wd ⟨hsrc.sourceEdge 3, hsrc.sourceEdge_survives 3⟩ = y.2.1 := by
    rw [show (⟨hsrc.sourceEdge 3, hsrc.sourceEdge_survives 3⟩ :
      NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)) =
        descent m wd y.2.1 hTy from Subtype.ext hGy.symm]
    exact liftEdge_descent m wd y.2.1 hTy
  have hSel : ∀ (which : Bool) (lbl : Fin 4), selectedLabel 0 false which = lbl →
      selectedLift m wd star anchorBlock hAnchor 0 false which =
        liftEdge m wd ⟨hsrc.sourceEdge lbl, hsrc.sourceEdge_survives lbl⟩ := by
    intro which lbl h
    subst h
    rfl
  -- (H-IV) for the pairing `0`
  have key : ∀ hPres : NonTrivalentValencyFourTracks.PrescribedPairingMove m wd star anchorBlock
      hAnchor 0, ColumnReceiptLink m wd := fun hPres ↦
    ⟨NonTrivalentValencyFourStarCount.typeChangeLink_of_prescribedPairingMove m wd star
      anchorBlock hAnchor 0 hPres, columnReceipt_four _ _ _ _ _ _ _⟩
  refine key ⟨hBase, ?_⟩
  rcases first_second_zero_false with ⟨hf, hs⟩ | ⟨hf, hs⟩
  · exact ⟨x, y, ((hSel false 2 hf).trans hLiftX).symm,
      ((hSel true 3 hs).trans hLiftY).symm, hStar⟩
  · exact ⟨y, x, ((hSel false 3 hf).trans hLiftY).symm,
      ((hSel true 2 hs).trans hLiftX).symm, by rw [hStar, Finset.pair_comm]⟩

/-- **`OuterWalk.TypeChangeLink` at every four-valent wall datum of every Whitehead
move, from the valency hypothesis alone.**  If the vanishing occurrence is
oriented the other way, the move is re-read from the other end of the contracted
edge (`CubicDartGraph.MoveData.swap`), which leaves the moved graph and the whole wall
payload unchanged. -/
theorem columnReceiptLink_four
    (h4 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 4) :
    ColumnReceiptLink m wd := by
  classical
  rcases dart_facetDartLeft_cases m wd (W4TargetPairings.FourStar.of_card h4) with h | h
  · exact columnReceiptLink_of_orientation_four m wd h4 h
  · have hL : label (graph.op m.base) = label m.base :=
      MovedIncidenceIso.label_op_of_tracks _ wd.fullDim wd.tracks m.base
    have hBase' : (swapWallData m wd hL).tracks.iso.dart
        (facetDartLeft m.swap (swapWallData m wd hL)
          (W4TargetPairings.FourStar.of_card h4)) = m.swap.base :=
      (congrArg wd.tracks.iso.dart
        (facetDartLeft_swap m wd hL (W4TargetPairings.FourStar.of_card h4))).trans h
    exact ColumnReceiptLink.ofSwap m wd hL
      (columnReceiptLink_of_orientation_four m.swap (swapWallData m wd hL) h4 hBase')

end DispatchFour

/-! ## 5.  Valency three: `NonTrivalentValencyThreeDispatcher.typeChangeLink_three` with the
column receipt

The proofs of `NonTrivalentValencyThreeDispatcher`, verbatim except at the leaves (`leafIII`,
`leafSimple`: the receipt of the Type III and Types I/II exits) and the wrappers
(`ColumnReceiptLink.ofMirror`, `ColumnReceiptLink.ofSwap`). -/

section DispatchThree

open DraismaVargas.LocalCases.ThirdEquation
open DraismaVargas.LocalCases.StablePathCount
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.NonTrivalentValencyThreeAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyThreeCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyThreeTracks
open DraismaVargas.LocalCases.MoveMirror
open DraismaVargas.LocalCases.NonTrivalentValencyThreeDispatcher
open DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleCandidate

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}

/-- **Type III leaf**: the Type III link carries the receipt
(`columnReceipt_threeIII`).  Same arguments as
`NonTrivalentValencyThreeStarCount.typeChangeLink_of_prescribedDoubledMove`. -/
theorem leafIII
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)
    (hPres : NonTrivalentValencyThreeTracks.PrescribedDoubledMove m wd wallStar src) :
    ColumnReceiptLink m wd :=
  ⟨NonTrivalentValencyThreeStarCount.typeChangeLink_of_prescribedDoubledMove m wd wallStar src
      hNoGlue hValid hPres,
    columnReceipt_threeIII m wd src hNoGlue hValid _ _⟩

/-- **Types I/II leaf**: the simple link carries the receipt (`columnReceipt_simple`).
Same arguments as
    `NonTrivalentValencyThreeSimpleStarCount.typeChangeLink_of_prescribedSimpleMove`. -/
theorem leafSimple {wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
    (base : SimpleBase (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)
    (hPres : NonTrivalentValencyThreeSimpleTracks.PrescribedSimpleMove m wd base) :
    ColumnReceiptLink m wd :=
  ⟨NonTrivalentValencyThreeSimpleStarCount.typeChangeLink_of_prescribedSimpleMove m wd base
      hValid hPres, columnReceipt_simple _ _ _ _ _⟩

variable (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
  (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)
  (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))

variable (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base)

include wallStar src hValid hNoGlue hBase in
/-- **Type III**: the move puts the two doubled-direction survivors at
`graph.vert m.base`. -/
theorem columnReceiptLink_of_doubled (j : Bool)
    (hk : keptRow m wd = (doubledND src j).stablePath)
    (hb : broughtRow m wd = (doubledND src (!j)).stablePath) :
    ColumnReceiptLink m wd := by
  classical
  have hlift : ∀ b : Bool, (doubledLift m wd src b).stablePath =
      inRow m wd ((doubledND src b).stablePath) := by
    intro b
    rw [doubledLift_eq m wd wallStar src b]
    exact stablePath_liftEdge' m wd (doubledND src b)
  have hStar := movedStar_darts m wd
  have hkr : inRow m wd (keptRow m wd) = (coverDart m wd (thirdLeft m)).2.1.stablePath :=
    inRow_keptRow m wd
  have hbr : inRow m wd (broughtRow m wd) = (coverDart m wd m.right).2.1.stablePath :=
    inRow_broughtRow m wd
  cases j
  · simp only [Bool.not_false] at hb
    refine leafIII m wd
      wallStar src hNoGlue hValid
      (NonTrivalentValencyThreeTracks.prescribedDoubledMove_of_rows m wd wallStar src hBase
        (coverDart m wd (thirdLeft m)) (coverDart m wd m.right) ?_ ?_ hStar)
    · rw [← hkr, hk, hlift false]
    · rw [← hbr, hb, hlift true]
  · simp only [Bool.not_true] at hb
    refine leafIII m wd
      wallStar src hNoGlue hValid
      (NonTrivalentValencyThreeTracks.prescribedDoubledMove_of_rows m wd wallStar src hBase
        (coverDart m wd m.right) (coverDart m wd (thirdLeft m)) ?_ ?_ ?_)
    · rw [← hbr, hb, hlift false]
    · rw [← hkr, hk, hlift true]
    · rw [hStar, Finset.pair_comm]

include wallStar src hValid hNoGlue hBase in
/-- **Types I and II**: the move puts one simple and one doubled survivor at
`graph.vert m.base`, and that pair is the realisable one. -/
theorem columnReceiptLink_of_simple (i j : Bool) (hR : Realisable m wd wallStar src i j)
    (hpair : (keptRow m wd = (simpleND src i).stablePath ∧
        broughtRow m wd = (doubledND src j).stablePath) ∨
      (keptRow m wd = (doubledND src j).stablePath ∧
        broughtRow m wd = (simpleND src i).stablePath)) :
    ColumnReceiptLink m wd := by
  classical
  have hStar := movedStar_darts m wd
  have halpha : (NonTrivalentValencyThreeSimpleTracks.alphaLift m wd
      (simpleBaseOf m wd wallStar src hNoGlue i j hR)).stablePath =
      inRow m wd ((simpleND src i).stablePath) := by
    rw [alphaLift_eq m wd wallStar src hNoGlue i j hR]
    exact stablePath_liftEdge' m wd (simpleND src i)
  have hdelta : (NonTrivalentValencyThreeSimpleTracks.deltaLift m wd
      (simpleBaseOf m wd wallStar src hNoGlue i j hR)).stablePath =
      inRow m wd ((doubledND src j).stablePath) := by
    rw [deltaLift_eq m wd wallStar src hNoGlue i j hR]
    exact stablePath_liftEdge' m wd (doubledND src j)
  rcases hpair with ⟨hk, hb⟩ | ⟨hk, hb⟩
  · refine leafSimple m wd
      (simpleBaseOf m wd wallStar src hNoGlue i j hR) hValid
      (NonTrivalentValencyThreeSimpleTracks.prescribedSimpleMove_of_rows m wd
        (simpleBaseOf m wd wallStar src hNoGlue i j hR) hBase
        (coverDart m wd (thirdLeft m)) (coverDart m wd m.right) ?_ ?_ hStar)
    · rw [halpha, ← hk]
      exact (inRow_keptRow m wd).symm
    · rw [hdelta, ← hb]
      exact (inRow_broughtRow m wd).symm
  · refine leafSimple m wd
      (simpleBaseOf m wd wallStar src hNoGlue i j hR) hValid
      (NonTrivalentValencyThreeSimpleTracks.prescribedSimpleMove_of_rows m wd
        (simpleBaseOf m wd wallStar src hNoGlue i j hR) hBase
        (coverDart m wd m.right) (coverDart m wd (thirdLeft m)) ?_ ?_ ?_)
    · rw [halpha, ← hb]
      exact (inRow_broughtRow m wd).symm
    · rw [hdelta, ← hk]
      exact (inRow_keptRow m wd).symm
    · rw [hStar, Finset.pair_comm]

include wallStar src hValid hNoGlue hBase in
/-- **The link at a three-valent wall whose vanishing occurrence is oriented
with its `A_u` end at `graph.vert m.base`.**  The move puts one row from each
end of the vanishing occurrence at `graph.vert m.base`; the census identifies
that pair with a pair of anchor survivors, and the mirror move supplies the
complementary pair whenever the pair the move names is not the one the
candidate of that partition realises. -/
theorem columnReceiptLink_of_orientation_three : ColumnReceiptLink m wd := by
  classical
  have hL : label (graph.op m.base) = label m.base :=
    MovedIncidenceIso.label_op_of_tracks _ wd.fullDim wd.tracks m.base
  have hBase' : wd.tracks.iso.dart (facetDartLeft (mirror m) wd wallStar) = (mirror m).base := hBase
  rcases classify m wd wallStar src hValid hBase with hA | hB | hC
  · obtain ⟨j, hk, hb⟩ := hA
    exact columnReceiptLink_of_doubled m wd wallStar src hValid hNoGlue hBase j hk hb
  · obtain ⟨j, hs, hst⟩ := hB
    refine ColumnReceiptLink.ofMirror m wd hL ?_
    refine columnReceiptLink_of_doubled (mirror m) wd wallStar src hValid hNoGlue hBase' j ?_ ?_
    · rw [keptRow_mirror m wd wallStar]
      exact hs
    · rw [broughtRow_mirror m wd wallStar]
      exact hst
  · obtain ⟨i, j, hp, hq⟩ := hC
    rcases realisable_or m wd wallStar src i j with hR | hR
    · exact columnReceiptLink_of_simple m wd wallStar src hValid hNoGlue hBase i j hR hp
    · refine ColumnReceiptLink.ofMirror m wd hL ?_
      refine columnReceiptLink_of_simple (mirror m) wd wallStar src hValid hNoGlue hBase' (!i)
          (!j) hR ?_
      rw [keptRow_mirror m wd wallStar, broughtRow_mirror m wd wallStar]
      exact hq.symm

end DispatchThree

section HeadlineThree

open DraismaVargas.LocalCases.ThirdEquation
open DraismaVargas.LocalCases.NonTrivalentValencyThreeTracks
open DraismaVargas.LocalCases.NonTrivalentValencyThreeDispatcher

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)

/-- **`OuterWalk.TypeChangeLink` at every three-valent wall datum of every
Whitehead move, from the wall valency alone.** -/
theorem columnReceiptLink_three
    (h3 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 3) :
    ColumnReceiptLink m wd := by
  classical
  obtain ⟨anchorBlk, src, hNoGlue, hValid, -, -⟩ :=
    NonTrivalentValencyThreeExit.exists_anchor_of_wallData m wd (ThreeStar.of_card h3)
  rcases dart_facetDartLeft_cases_three m wd (ThreeStar.of_card h3) with h | h
  · exact columnReceiptLink_of_orientation_three m wd (ThreeStar.of_card h3) src hValid hNoGlue h
  · have hL : label (graph.op m.base) = label m.base :=
      MovedIncidenceIso.label_op_of_tracks _ wd.fullDim wd.tracks m.base
    have hBase' : (NonTrivalentValencyFourDispatcher.swapWallData m wd hL).tracks.iso.dart
        (facetDartLeft m.swap (NonTrivalentValencyFourDispatcher.swapWallData m wd hL)
          (ThreeStar.of_card h3)) = m.swap.base :=
      (congrArg wd.tracks.iso.dart
        (facetDartLeft_swap_three m wd hL (ThreeStar.of_card h3))).trans h
    exact ColumnReceiptLink.ofSwap m wd hL (columnReceiptLink_of_orientation_three m.swap
      (NonTrivalentValencyFourDispatcher.swapWallData m wd hL) (ThreeStar.of_card h3) src hValid
      hNoGlue hBase')


end HeadlineThree

/-! ## 6.  Valency two

The proofs of `NonTrivalentValencyTwoDispatcher`, verbatim except at the leaves (the Base II
merge, Base I and split exits, whose column receipts are `columnReceipt_free`,
`columnReceipt_baseOne`, `columnReceipt_split`, each fed the wall labelling's target
dictionary `hTarget` from `exists_wallLabelling_two'`) and the swap wrapper
(`ColumnReceiptLink.ofSwap`). -/

section MergeAny

open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.StablePathCount
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.PrunedFibreValency
open DraismaVargas.LocalCases.PrunedFibreTree
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.ClassInjectivity
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRowEquiv
open DraismaVargas.LocalCases.NonTrivalentValencyTwoStarCountAll

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)

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
  (hTarget : ∀ j, labelling₀.targetEdge j =
    punctureTargetEquiv wd.fullDim.labelling wd.hc wd.hab wd.hOne j)


include src hOrd labelling₀ hRowVal hMatrixWall hTarget in
/-- **`OuterWalk.TypeChangeLink` at any two-valent Base II wall, from the
dispatcher's (H-II) alone.**  The incoming `2 + 2` / `1 + 3` / `3 + 1`
trichotomy and the orientation of the two ends are discharged internally. -/
theorem columnReceiptLink_of_prescribedMergedMoveAny
    (hPres : PrescribedMergedMoveAny m wd sel) : ColumnReceiptLink m wd := by
  classical
  obtain ⟨E⟩ := nonempty_vanishingEnds m wd src hOrd
  rcases prescribedMergedMoveOn_of_any m wd sel E hPres with h | h
  · exact ⟨typeChangeLink_of_prescribedMergedMove_two m wd src sel hOrd labelling₀ hRowVal
      hMatrixWall E h, columnReceipt_free (hTarget := hTarget) ..⟩
  · exact ⟨typeChangeLink_of_prescribedMergedMove_two m wd src sel hOrd labelling₀ hRowVal
      hMatrixWall (swapEnds m wd E) h, columnReceipt_free (hTarget := hTarget) ..⟩

end MergeAny

section DispatchTwo

open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.StablePathCount
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRowEquiv
open DraismaVargas.LocalCases.NonTrivalentValencyTwoDispatcher

noncomputable local instance instDecidableEqEdges (target : CFGraph) :
    DecidableEq target.edges := Classical.decEq _

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)

variable {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
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
  (hTarget : ∀ j, labelling₀.targetEdge j =
    punctureTargetEquiv wd.fullDim.labelling wd.hc wd.hab wd.hOne j)

include src hOrd labelling₀ hRowVal hMatrixWall hTarget in
/-- **The link when the two survivors the move brings together lie over the *same*
target direction** -- the Base II merge.  Nothing but the wall data and the two named
survivors enters: the Base II star count turns (H-II) into the link at any two-valent Base II
wall (`columnReceiptLink_of_prescribedMergedMoveAny`), and (H-II) is discharged here from the
moved star (`IncomingPairing.exists_movedStar_darts` in the explicit form `movedStar_base`). -/
theorem columnReceiptLink_of_thick_rows
    (g g' : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hg : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g.1
      (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk))
    (hg' : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g'.1
      (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk))
    (hne : g ≠ g')
    (hgT : IsThickSurv m wd wallStar anchorBlk g)
    (hgT' : IsThickSurv m wd wallStar anchorBlk g')
    (hrow : survRow m wd g = rowT m wd) (hrow' : survRow m wd g' = rowR m wd) :
    ColumnReceiptLink m wd := by
  classical
  refine columnReceiptLink_of_prescribedMergedMoveAny m wd src
    { first := ⟨g.1, hg⟩
      second := ⟨g'.1, hg'⟩
      first_ne_second := fun h ↦ hne (Subtype.ext (congrArg
        (fun e : IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk) ↦ e.1) h))
      first_mem := (mem_directionSurvivors _ _ _ _ _).mpr
        ⟨(W3R1SourceProfile.mem_survivors _ _ _).mpr g.2, hgT⟩
      second_mem := (mem_directionSurvivors _ _ _ _ _).mpr
        ⟨(W3R1SourceProfile.mem_survivors _ _ _).mpr g'.2, hgT'⟩ }
    hOrd labelling₀ hRowVal hMatrixWall hTarget ?_
  refine NonTrivalentValencyTwoStarCountAll.prescribedMergedMoveAny_of_rows m wd _
    ⟨(IncomingPairing.baseDart m wd).1, (IncomingPairing.opBaseDart m wd).1,
      incidenceCount_facetRow_baseEnd_pos m wd, incidenceCount_facetRow_opEnd_pos m wd,
      (IncomingPairing.vtx_baseDart m wd).symm, (IncomingPairing.vtx_opBaseDart m wd).symm⟩
    (coverDart m wd (thirdBase m)) (coverDart m wd m.right) ?_ ?_ ?_
  · exact hrow.symm
  · exact hrow'.symm
  · rw [movedStar_base m, dart_coverDart, dart_coverDart]


/-- **The valency-two dispatch.**  At every two-valent wall datum, either the link is
already there -- the two survivors the move brings together lie over the same target
direction, so the Base II merge realises it, possibly after re-reading the move from the
other end of the contracted edge (`CubicDartGraph.MoveData.swap`) -- or the wall carries the
Configuration A `2 + 2` distribution and the move names a **cross pair**: one survivor
over each direction, whose incoming rows are the rows of the two occurrences the move
brings together, in one of the two orders.

This is the whole content of the dispatcher: the census
(`incidenceCount_anchor_eq_ends`) matches the four occurrences the move sorts at the two
ends of the vanishing row with the four survivors at the anchor, and at least two
survivors lie over the thick direction. -/
theorem columnReceiptLink_or_crossPair
    (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 2) :
    ColumnReceiptLink m wd ∨
      ∃ (blk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
        (g g' : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)),
        TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            (TwoStar.of_card h2) blk ∧
          (∀ direction : Fin 2, (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
              (TwoStar.of_card h2) blk direction).card = 2) ∧
            Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g.1
                (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
                  ⟨wd.a, wd.hab⟩ blk) ∧
              Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g'.1
                  (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
                    ⟨wd.a, wd.hab⟩ blk) ∧
                (g.1.1.1 : (contract wd.coverTarget wd.hab wd.hOne).edges) ≠ g'.1.1.1 ∧
                  ((survRow m wd g = rowT m wd ∧ survRow m wd g' = rowR m wd) ∨
                    (survRow m wd g = rowR m wd ∧ survRow m wd g' = rowT m wd)) := by
  classical
  set wallStar := TwoStar.of_card (target := contract wd.coverTarget wd.hab wd.hOne)
    (wall := ⟨wd.a, wd.hab⟩) h2 with hwallStar
  obtain ⟨anchorBlock, hNd, src⟩ :=
    NonTrivalentAnchorValency.twoBranchAnchor_of_single_row wd.cover wd.fullDim wd.hc wd.hab
      wd.hOne (wd.hForest m) wd.coordinates (label m.base) wd.hRows wd.hZeroCoord wd.hPosCoord
      wd.hFacetZero wallStar
  have hOrd := NonTrivalentValencyTwoRowEquiv.ordinaryTrivalent_of_wall_metric wd.cover
    wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m) wallStar wd.coordinates (label m.base)
    wd.hRows wd.hZeroCoord anchorBlock hNd
  obtain ⟨labelling₀, hRowVal, hMatrixWall, hTarget⟩ :=
    exists_wallLabelling_two' wd.cover wd.fullDim
      wd.hc wd.hab wd.hOne (wd.hForest m) (label m.base) wallStar wd.coordinates wd.hRows
      wd.hZeroCoord wd.hPosCoord wd.hFacetZero
  obtain ⟨E⟩ := NonTrivalentValencyTwoStarCountAll.nonempty_vanishingEnds m wd src hOrd
  have hEnds := anchorEnds_base m wd E
  have hInj : ∀ i j : Fin 4, i ≠ j →
      (survEquiv m wd hEnds src hOrd i).1 ≠ (survEquiv m wd hEnds src hOrd j).1 := by
    intro i j hij hBad
    exact hij ((survEquiv m wd hEnds src hOrd).injective (Subtype.ext hBad))
  -- the `2 + 2` fact in the cross case
  have hTwoTwo : ∀ {i j : Fin 4}, i ≠ j →
      ¬ IsThickSurv m wd wallStar anchorBlock (survEquiv m wd hEnds src hOrd i).1 →
      ¬ IsThickSurv m wd wallStar anchorBlock (survEquiv m wd hEnds src hOrd j).1 →
      ∀ direction : Fin 2,
        (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
          anchorBlock direction).card = 2 := by
    intro i j hij hi hj
    have hsub : ({i, j} : Finset (Fin 4)) ⊆ Finset.univ.filter (fun k : Fin 4 ↦
        ¬ IsThickSurv m wd wallStar anchorBlock (survEquiv m wd hEnds src hOrd k).1) := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    have hle : ({i, j} : Finset (Fin 4)).card ≤ (Finset.univ.filter (fun k : Fin 4 ↦
        ¬ IsThickSurv m wd wallStar anchorBlock (survEquiv m wd hEnds src hOrd k).1)).card :=
      Finset.card_le_card hsub
    rw [Finset.card_pair hij] at hle
    have hsum := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 4)))
      (p := fun k : Fin 4 ↦ IsThickSurv m wd wallStar anchorBlock
        (survEquiv m wd hEnds src hOrd k).1)
    have hcard : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
    rw [card_thickPos_eq m wd hEnds src hOrd] at hsum
    have hge := Prescribed.two_le_card_thick src
    have hthick : (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
        anchorBlock (Prescribed.thickDirection (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          wallStar anchorBlock)).card = 2 := by omega
    have hsplit := Prescribed.card_thick_add_card_thin src
    have hthin : (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
        anchorBlock (Prescribed.thinDirection (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          wallStar anchorBlock)).card = 2 := by omega
    intro direction
    by_cases hd : direction = Prescribed.thickDirection
      (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlock
    · rw [hd]; exact hthick
    · have hd' : direction = Prescribed.thickDirection
          (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlock + 1 := by
        revert hd
        generalize (Prescribed.thickDirection (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          wallStar anchorBlock) = t
        revert direction t
        decide
      rw [hd']; exact hthin
  rcases thick_trichotomy m wd hEnds src hOrd with ⟨ht1, ht2⟩ | ⟨ht3, ht0⟩ |
    ⟨(⟨ht1, ht2⟩ | ⟨ht2, ht1⟩), hOther⟩
  · exact Or.inl (columnReceiptLink_of_thick_rows m wd src hOrd labelling₀ hRowVal
      hMatrixWall hTarget _ _ (incident_survEquiv m wd hEnds src hOrd 1)
      (incident_survEquiv m wd hEnds src hOrd 2) (hInj 1 2 (by decide)) ht1 ht2
      (survRow_survEquiv m wd hEnds src hOrd 1) (survRow_survEquiv m wd hEnds src hOrd 2))
  · have hL : label (graph.op m.base) = label m.base :=
      MovedIncidenceIso.label_op_of_tracks _ wd.fullDim wd.tracks m.base
    have hRowVal' : ∀ pth : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne),
        (labelling₀.row pth).1 =
          Equiv.swap (label (graph.op m.base))
            (wd.fullDim.labelling.targetEdge.symm wd.contracted)
            (wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
              (WallAdmissibility.danglingCompatible_of_contractionForest wd.cover wd.hc wd.hab
                wd.hOne (wd.hForest m)) (wd.hForest m) pth)) := by
      intro pth
      rw [hL]
      exact hRowVal pth
    exact Or.inl (ColumnReceiptLink.ofSwap m wd hL (columnReceiptLink_of_thick_rows m.swap
      (NonTrivalentValencyFourDispatcher.swapWallData m wd hL) src hOrd labelling₀ hRowVal'
      hMatrixWall hTarget _ _ (incident_survEquiv m wd hEnds src hOrd 3)
      (incident_survEquiv m wd hEnds src hOrd 0) (hInj 3 0 (by decide)) ht3 ht0
      (survRow_survEquiv m wd hEnds src hOrd 3)
      (survRow_survEquiv m wd hEnds src hOrd 0)))
  · refine Or.inr ⟨anchorBlock, _, _, src, ?_, incident_survEquiv m wd hEnds src hOrd 1,
      incident_survEquiv m wd hEnds src hOrd 2, ?_,
      Or.inl ⟨survRow_survEquiv m wd hEnds src hOrd 1, survRow_survEquiv m wd hEnds src hOrd 2⟩⟩
    · rcases hOther with h | h
      · exact hTwoTwo (by decide : (2 : Fin 4) ≠ 3) ht2 h
      · exact hTwoTwo (by decide : (2 : Fin 4) ≠ 0) ht2 h
    · intro hBad
      exact ht2 (hBad.symm.trans ht1)
  · refine Or.inr ⟨anchorBlock, _, _, src, ?_, incident_survEquiv m wd hEnds src hOrd 2,
      incident_survEquiv m wd hEnds src hOrd 1, ?_,
      Or.inr ⟨survRow_survEquiv m wd hEnds src hOrd 2, survRow_survEquiv m wd hEnds src hOrd 1⟩⟩
    · rcases hOther with h | h
      · exact hTwoTwo (by decide : (1 : Fin 4) ≠ 3) ht1 h
      · exact hTwoTwo (by decide : (1 : Fin 4) ≠ 0) ht1 h
    · intro hBad
      exact ht1 (hBad.symm.trans ht2)

end DispatchTwo

section BaseOneAndSplit

open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.Infrastructure.ContractionFibre
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.StablePathCount
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoGauge
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOne
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneTracks
open DraismaVargas.LocalCases.NonTrivalentValencyTwoDispatcher
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRowEquiv (OrdinaryTrivalent)
open DraismaVargas.LocalCases.NonTrivalentValencyTwoTracksLeaf (AnchorEnds)
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneLink
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneStarCount
  (typeChangeLink_of_prescribedBaseOneMove)

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {deg : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}

/-- **The link from a gauged Base I setup whose `A₁` pair carries the two rows the
move names.**  The Base I star count, with (H-BaseI) discharged by
`prescribedBaseOneMove_of_unordered_rows`; the wall labelling, the anchor ends and
the ordinary-block trivalence are produced from the wall data. -/
theorem columnReceiptLink_of_gauged_setup (m : graph.MoveData)
    {arrival : FacetArrival deg graph label (label m.base)} (wd : WallData arrival)
    (wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (thickSheet thinSheet : Fin deg)
    (setup : BaseOneSetup
      (gaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        thickSheet thinSheet) wallStar
      (gaugedAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        thickSheet thinSheet))
    (hA1 : ((crossLift m wd thickSheet thinSheet setup false false).stablePath = rowT m wd ∧
          (crossLift m wd thickSheet thinSheet setup false true).stablePath = rowR m wd) ∨
        ((crossLift m wd thickSheet thinSheet setup false false).stablePath = rowR m wd ∧
          (crossLift m wd thickSheet thinSheet setup false true).stablePath = rowT m wd)) :
    ColumnReceiptLink m wd := by
  classical
  have hNd := NonTrivalentValencyTwoRows.nonDanglingValency_anchor src
  have hOrd := NonTrivalentValencyTwoRowEquiv.ordinaryTrivalent_of_wall_metric wd.cover
    wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m) wallStar wd.coordinates (label m.base)
    wd.hRows wd.hZeroCoord anchorBlk hNd
  obtain ⟨labelling₀, hRowVal, hMatrixWall, hTarget⟩ :=
    exists_wallLabelling_two' wd.cover wd.fullDim
      wd.hc wd.hab wd.hOne (wd.hForest m) (label m.base) wallStar wd.coordinates wd.hRows
      wd.hZeroCoord wd.hPosCoord wd.hFacetZero
  obtain ⟨Ends⟩ := NonTrivalentValencyTwoStarCountAll.nonempty_vanishingEnds m wd src hOrd
  have hEnds := anchorEnds_base m wd Ends
  have hGauged := gaugedData_valid (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
    anchorBlk thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd)
  exact ⟨typeChangeLink_of_prescribedBaseOneMove m wd thickSheet thinSheet setup hGauged hOrd
    src labelling₀ hRowVal hMatrixWall hEnds
    (prescribedBaseOneMove_of_unordered_rows m wd thickSheet thinSheet setup hA1),
    columnReceipt_baseOne (hTarget := hTarget) ..⟩

/-- **The Base I link at a Configuration A cross pair, with the two members named by
direction.**  `P` lies over `star.edge 0`, `Q` over `star.edge 1`, they have equal
dilation indices, and their incoming rows are the two rows the move names.  The
`t₃`-alignment gauge `NonTrivalentValencyTwoGauge.gaugedData` turns the two index equalities
into a Base I setup; `crossPair_identification` says the pair the setup puts at `A₁` is
`{P, Q}` or the complementary pair, and in the second case the same construction discharges
the move read from the other end of the contracted edge (`MoveData.swap`), whose own pair is
exactly the complementary one. -/
theorem columnReceiptLink_of_crossPair_oriented (m : graph.MoveData)
    {arrival : FacetArrival deg graph label (label m.base)} (wd : WallData arrival)
    (wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hsplit : ∀ direction : Fin 2,
      (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        direction).card = 2)
    (P Q : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hPi : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) P.1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlk))
    (hQi : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) Q.1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlk))
    (hP : (⟨P.1, hPi⟩ : IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩ anchorBlk)) ∈
      directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk 0)
    (hQ : (⟨Q.1, hQi⟩ : IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩ anchorBlk)) ∈
      directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk 1)
    (hk : (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex P.1 =
      (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex Q.1)
    (hrows : (survRow m wd P = rowT m wd ∧ survRow m wd Q = rowR m wd) ∨
      (survRow m wd P = rowR m wd ∧ survRow m wd Q = rowT m wd)) :
    ColumnReceiptLink m wd := by
  classical
  have hConn : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Connected :=
    (NonTrivalentValencyTwoTracks.wallValid m wd).1
  have hNd := NonTrivalentValencyTwoRows.nonDanglingValency_anchor src
  obtain ⟨R, hR, hRne⟩ := other_of_pair (hsplit 0) hP
  obtain ⟨S, hS, hSne⟩ := other_of_pair (hsplit 1) hQ
  -- the second index equality, from the two direction sums
  have hIndexSecond : (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex R.1 =
      (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex S.1 := by
    have h0 := src.direction_index_sum 0
    have h1 := src.direction_index_sum 1
    rw [directionSurvivors_eq_pair (hsplit 0) hP hR (Ne.symm hRne),
      Finset.sum_pair (Ne.symm hRne)] at h0
    rw [directionSurvivors_eq_pair (hsplit 1) hQ hS (Ne.symm hSne),
      Finset.sum_pair (Ne.symm hSne)] at h1
    have hPQ : (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex
          (⟨P.1, hPi⟩ : IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
              ⟨wd.a, wd.hab⟩ anchorBlk)).1 =
        (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex
          (⟨Q.1, hQi⟩ : IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
              ⟨wd.a, wd.hab⟩ anchorBlk)).1 := hk
    rw [hPQ] at h0
    have hZ : ((contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex R.1 : ℤ) =
        ((contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex S.1 : ℤ) := by
      linarith [h0, h1]
    exact_mod_cast hZ
  -- the gauged Base I setup and the two pair conjuncts
  obtain ⟨setup, -, -, -, -, -, -, hPairFirst, hPairSecond⟩ :=
    exists_gauged_candidate_of_contraction' wd.cover wd.fullDim wd.hc wd.hab wd.hOne
      (wd.hForest m) (wd.hCompat m) wallStar anchorBlk hNd hsplit ⟨P.1, hPi⟩ R ⟨Q.1, hQi⟩ S
      hP hR hQ hS (Ne.symm hRne) (Ne.symm hSne) hk hIndexSecond
  rcases crossPair_identification (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
      anchorBlk hConn hsplit hP hR hQ hS (Ne.symm hRne) (Ne.symm hSne) setup hPairFirst
      hPairSecond with ⟨hT, hN⟩ | ⟨hT, hN⟩
  · -- the move's own pair sits at `A₁`
    have e0 := crossLift_stablePath_eq_survRow m wd _ _ setup false false P
      (congrArg Subtype.val hT)
    have e1 := crossLift_stablePath_eq_survRow m wd _ _ setup false true Q
      (congrArg Subtype.val hN)
    refine columnReceiptLink_of_gauged_setup m wd wallStar anchorBlk src _ _ setup ?_
    rcases hrows with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl ⟨e0.trans ha, e1.trans hb⟩
    · exact Or.inr ⟨e0.trans ha, e1.trans hb⟩
  · -- the complementary pair sits at `A₁`: read the move from the other end
    have hOrd := NonTrivalentValencyTwoRowEquiv.ordinaryTrivalent_of_wall_metric wd.cover
      wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m) wallStar wd.coordinates (label m.base)
      wd.hRows wd.hZeroCoord anchorBlk hNd
    obtain ⟨Ends⟩ := NonTrivalentValencyTwoStarCountAll.nonempty_vanishingEnds m wd src hOrd
    have hEnds := anchorEnds_base m wd Ends
    have hRnd : ¬ IsDangling (contractDatum wd.cover wd.hc wd.hab wd.hOne) R.1 :=
      NonTrivalentValencyTwoRows.survivor_not_isDangling hR
    have hSnd : ¬ IsDangling (contractDatum wd.cover wd.hc wd.hab wd.hOne) S.1 :=
      NonTrivalentValencyTwoRows.survivor_not_isDangling hS
    have hPt : P.1.1.1 = wallStar.edge 0 := survivor_target hP
    have hQt : Q.1.1.1 = wallStar.edge 1 := survivor_target hQ
    have hRt : R.1.1.1 = wallStar.edge 0 := survivor_target hR
    have hSt : S.1.1.1 = wallStar.edge 1 := survivor_target hS
    have hzo : wallStar.edge 0 ≠ wallStar.edge 1 := wallStar.edge_injective.ne (by decide)
    have hcross : ∀ x y : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne),
        x.1.1.1 = wallStar.edge 0 → y.1.1.1 = wallStar.edge 1 → x ≠ y := by
      intro x y hx hy hxy
      exact hzo (by rw [← hx, ← hy, hxy])
    have hPR : P ≠ (⟨R.1, hRnd⟩ :
        NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)) := by
      intro hbad
      exact hRne (Subtype.ext (congrArg Subtype.val hbad).symm)
    have hQS : Q ≠ (⟨S.1, hSnd⟩ :
        NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)) := by
      intro hbad
      exact hSne (Subtype.ext (congrArg Subtype.val hbad).symm)
    have hcomp := rows_of_complement m wd src hOrd hEnds P Q ⟨R.1, hRnd⟩ ⟨S.1, hSnd⟩
      hPi hQi R.2 S.2 (hcross P Q hPt hQt) hPR (hcross P ⟨S.1, hSnd⟩ hPt hSt)
      ((hcross ⟨R.1, hRnd⟩ Q hRt hQt).symm) hQS (hcross ⟨R.1, hRnd⟩ ⟨S.1, hSnd⟩ hRt hSt) hrows
    have e0 := crossLift_stablePath_eq_survRow m wd _ _ setup false false
      (⟨R.1, hRnd⟩ : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
      (congrArg Subtype.val hT)
    have e1 := crossLift_stablePath_eq_survRow m wd _ _ setup false true
      (⟨S.1, hSnd⟩ : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
      (congrArg Subtype.val hN)
    have hL : label (graph.op m.base) = label m.base :=
      MovedIncidenceIso.label_op_of_tracks _ wd.fullDim wd.tracks m.base
    refine ColumnReceiptLink.ofSwap m wd hL (columnReceiptLink_of_gauged_setup m.swap
      (NonTrivalentValencyFourDispatcher.swapWallData m wd hL) wallStar anchorBlk src _ _ setup ?_)
    rcases hcomp with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inr ⟨e0.trans ha, e1.trans hb⟩
    · exact Or.inl ⟨e0.trans ha, e1.trans hb⟩

/-- **The Base I link at a Configuration A cross pair.**  Neither member is named by
direction: the two survivors lie over different target occurrences, so one lies over
each direction of the incoming two-valent star. -/
theorem columnReceiptLink_of_crossPair (m : graph.MoveData)
    {arrival : FacetArrival deg graph label (label m.base)} (wd : WallData arrival)
    (wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (g g' : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hsplit : ∀ direction : Fin 2,
      (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        direction).card = 2)
    (hg : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g.1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlk))
    (hg' : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g'.1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlk))
    (hne : (g.1.1.1 : (contract wd.coverTarget wd.hab wd.hOne).edges) ≠ g'.1.1.1)
    (hrows : (survRow m wd g = rowT m wd ∧ survRow m wd g' = rowR m wd) ∨
      (survRow m wd g = rowR m wd ∧ survRow m wd g' = rowT m wd))
    (hk : (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex g.1 =
      (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex g'.1) :
    ColumnReceiptLink m wd := by
  classical
  have hgd : (⟨g.1, hg⟩ : IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩ anchorBlk)) ∈
      directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        (survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
          ⟨g.1, hg⟩) :=
    (mem_directionSurvivors _ _ _ _ _).mpr
      ⟨(W3R1SourceProfile.mem_survivors _ _ _).mpr g.2, (edge_survivorLabel _ _ _ _).symm⟩
  have hg'd : (⟨g'.1, hg'⟩ : IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩ anchorBlk)) ∈
      directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        (survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
          ⟨g'.1, hg'⟩) :=
    (mem_directionSurvivors _ _ _ _ _).mpr
      ⟨(W3R1SourceProfile.mem_survivors _ _ _).mpr g'.2, (edge_survivorLabel _ _ _ _).symm⟩
  have hdne : survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        ⟨g.1, hg⟩ ≠
      survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        ⟨g'.1, hg'⟩ := by
    intro hbad
    refine hne ?_
    rw [← edge_survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        ⟨g.1, hg⟩,
      ← edge_survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        ⟨g'.1, hg'⟩, hbad]
  have hcase : ∀ d : Fin 2, d = 0 ∨ d = 1 := by decide
  rcases hcase (survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      ⟨g.1, hg⟩) with hd | hd
  · rcases hcase (survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        ⟨g'.1, hg'⟩) with hd' | hd'
    · exact absurd (hd.trans hd'.symm) hdne
    · rw [hd] at hgd
      rw [hd'] at hg'd
      exact columnReceiptLink_of_crossPair_oriented m wd wallStar anchorBlk src hsplit g g' hg
          hg' hgd hg'd
        hk hrows
  · rcases hcase (survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        ⟨g'.1, hg'⟩) with hd' | hd'
    · rw [hd] at hgd
      rw [hd'] at hg'd
      refine columnReceiptLink_of_crossPair_oriented m wd wallStar anchorBlk src hsplit g' g hg'
          hg hg'd hgd
        hk.symm ?_
      rcases hrows with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inr ⟨hb, ha⟩
      · exact Or.inl ⟨hb, ha⟩
    · exact absurd (hd.trans hd'.symm) hdne

section Split

open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitExit (relabelStar
  directionSurvivors_relabelStar_zero directionSurvivors_relabelStar_one
  twoBranchAnchor_relabelStar split_relabelStar ordinaryTrivalent_splitGauged)

variable (m : graph.MoveData) {arrival : FacetArrival deg graph label (label m.base)}
  (wd : WallData arrival)
  (wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
  (anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)

/-- **The split link from a gauged split anchor whose pair at `S` carries the two rows
the move names.**  The split star count
(`NonTrivalentValencyTwoSplitStarCount.typeChangeLink_of_prescribedSplitMove`) with (H-split)
discharged: the survivor clause of `PrescribedSplitMove` does not order the pair, so either
assignment works. -/
theorem columnReceiptLink_of_splitAnchor
    (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (thickSheet thinSheet : Fin deg)
    (ra : NonTrivalentValencyTwoSplitRows.SplitAnchor
      (NonTrivalentValencyTwoSplitGauge.splitGaugedData
        (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet thinSheet)
      wallStar
      (NonTrivalentValencyTwoSplitGauge.splitGaugedAnchor
        (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet thinSheet))
    (A Dl : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hA : (NonTrivalentValencyTwoSplitTracks.ungaugeSurvivor
      (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet thinSheet
      ra.alphaEdge).1 = A.1)
    (hD : (NonTrivalentValencyTwoSplitTracks.ungaugeSurvivor
      (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet thinSheet
      ra.deltaEdge).1 = Dl.1)
    (hrows : (survRow m wd A = rowT m wd ∧ survRow m wd Dl = rowR m wd) ∨
      (survRow m wd A = rowR m wd ∧ survRow m wd Dl = rowT m wd)) :
    ColumnReceiptLink m wd := by
  classical
  have hNd := NonTrivalentValencyTwoRows.nonDanglingValency_anchor src
  have hOrd := NonTrivalentValencyTwoRowEquiv.ordinaryTrivalent_of_wall_metric wd.cover
    wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m) wallStar wd.coordinates (label m.base)
    wd.hRows wd.hZeroCoord anchorBlk hNd
  have hValid := NonTrivalentValencyTwoTracks.wallValid m wd
  have hGauged := NonTrivalentValencyTwoSplitGauge.splitGaugedData_valid
    (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet thinSheet hValid
  have hOrdGauged := ordinaryTrivalent_splitGauged
    (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet thinSheet
    hValid.1 hOrd
  obtain ⟨labelling₀, hRowVal, hMatrixWall, hTarget⟩ :=
    exists_wallLabelling_two' wd.cover wd.fullDim
      wd.hc wd.hab wd.hOne (wd.hForest m) (label m.base) wallStar wd.coordinates wd.hRows
      wd.hZeroCoord wd.hPosCoord wd.hFacetZero
  obtain ⟨Ends⟩ := NonTrivalentValencyTwoStarCountAll.nonempty_vanishingEnds m wd src hOrd
  have hEnds := anchorEnds_base m wd Ends
  have e0 := splitLift_stablePath_eq_survRow m wd wallStar anchorBlk thickSheet thinSheet ra
    false A hA
  have e1 := splitLift_stablePath_eq_survRow m wd wallStar anchorBlk thickSheet thinSheet ra
    true Dl hD
  have key := fun hPres ↦
      (⟨NonTrivalentValencyTwoSplitStarCount.typeChangeLink_of_prescribedSplitMove
    m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd src labelling₀ hRowVal hMatrixWall hEnds
    hPres, columnReceipt_split (hTarget := hTarget) ..⟩ : ColumnReceiptLink m wd)
  refine key ⟨⟨rfl, rfl⟩, ?_⟩
  rcases hrows with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · refine ⟨coverDart m wd (thirdBase m), coverDart m wd m.right, (e0.trans ha).symm,
      (e1.trans hb).symm, ?_⟩
    rw [movedStar_base m, dart_coverDart, dart_coverDart]
  · refine ⟨coverDart m wd m.right, coverDart m wd (thirdBase m), (e0.trans ha).symm,
      (e1.trans hb).symm, ?_⟩
    rw [movedStar_base m, dart_coverDart, dart_coverDart,
      Finset.pair_comm (thirdBase m) m.right]

/-- **The split link at a Configuration A cross pair with the splitting member named.**
`A` lies over `star.edge 0`, `Dl` over `star.edge 1`, and `k_delta < k_alpha` (Part II, the
valency-two subcase `{v2-nd4-t3-k2<k3}` of Configuration A: exactly the case in which there
is no member with Base I). -/
theorem columnReceiptLink_of_splitPair_oriented
    (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hsplit : ∀ direction : Fin 2,
      (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        direction).card = 2)
    (A Dl : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hAi : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) A.1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlk))
    (hDi : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) Dl.1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlk))
    (hA : (⟨A.1, hAi⟩ : IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩ anchorBlk)) ∈
      directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk 0)
    (hD : (⟨Dl.1, hDi⟩ : IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩ anchorBlk)) ∈
      directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk 1)
    (hIdx : (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex Dl.1 <
      (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex A.1)
    (hrows : (survRow m wd A = rowT m wd ∧ survRow m wd Dl = rowR m wd) ∨
      (survRow m wd A = rowR m wd ∧ survRow m wd Dl = rowT m wd)) :
    ColumnReceiptLink m wd := by
  classical
  obtain ⟨B, hB, hBne⟩ := other_of_pair (hsplit 0) hA
  obtain ⟨Eps, hEps, hEpsNe⟩ := other_of_pair (hsplit 1) hD
  have hValid := NonTrivalentValencyTwoTracks.wallValid m wd
  refine columnReceiptLink_of_splitAnchor m wd wallStar anchorBlk src _ _
    (NonTrivalentValencyTwoSplitRows.splitAnchor_gauged src hsplit
      (NonTrivalentUniqueFourValent.wall_target_connected wd.cover wd.fullDim wd.hab wd.hOne)
      (NonTrivalentUniqueFourValent.wall_target_genus wd.cover wd.fullDim wd.hab wd.hOne)
      hValid.1 hA hB hD hEps (Ne.symm hBne) (Ne.symm hEpsNe) hIdx) A Dl ?_ ?_ hrows
  · exact congrArg Subtype.val
      ((NonTrivalentValencyTwoSplitGauge.splitSurvivorEquiv
        (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk _ _).symm_apply_apply _)
  · exact congrArg Subtype.val
      ((NonTrivalentValencyTwoSplitGauge.splitSurvivorEquiv
        (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk _ _).symm_apply_apply _)

/-- The same with only the two directions named: the strict index inequality picks the
member, and when it points the other way the mirror member
(`NonTrivalentValencyTwoSplitExit.relabelStar`) realises the pairing. -/
theorem columnReceiptLink_of_splitPair_dir
    (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hsplit : ∀ direction : Fin 2,
      (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        direction).card = 2)
    (g g' : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hgi : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g.1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlk))
    (hg'i : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g'.1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlk))
    (hgd : (⟨g.1, hgi⟩ : IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩ anchorBlk)) ∈
      directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk 0)
    (hg'd : (⟨g'.1, hg'i⟩ : IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩ anchorBlk)) ∈
      directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk 1)
    (hk : (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex g.1 ≠
      (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex g'.1)
    (hrows : (survRow m wd g = rowT m wd ∧ survRow m wd g' = rowR m wd) ∨
      (survRow m wd g = rowR m wd ∧ survRow m wd g' = rowT m wd)) :
    ColumnReceiptLink m wd := by
  classical
  have hz : directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (relabelStar wallStar) anchorBlk 0 =
      directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk 1 :=
    directionSurvivors_relabelStar_zero wallStar
  have ho : directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (relabelStar wallStar) anchorBlk 1 =
      directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk 0 :=
    directionSurvivors_relabelStar_one wallStar
  rcases lt_or_gt_of_ne hk with hlt | hlt
  · refine columnReceiptLink_of_splitPair_oriented m wd (relabelStar wallStar) anchorBlk
      (twoBranchAnchor_relabelStar src) (split_relabelStar hsplit) g' g hg'i hgi ?_ ?_ hlt ?_
    · rw [hz]
      exact hg'd
    · rw [ho]
      exact hgd
    · rcases hrows with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inr ⟨hb, ha⟩
      · exact Or.inl ⟨hb, ha⟩
  · exact columnReceiptLink_of_splitPair_oriented m wd wallStar anchorBlk src hsplit g g' hgi
      hg'i hgd hg'd
      hlt hrows

/-- **The split link at a Configuration A cross pair.**  Neither member is named by
direction; the two survivors lie over different target occurrences, so one lies over
each direction. -/
theorem columnReceiptLink_of_splitPair
    (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hsplit : ∀ direction : Fin 2,
      (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        direction).card = 2)
    (g g' : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hgi : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g.1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlk))
    (hg'i : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g'.1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlk))
    (hne : (g.1.1.1 : (contract wd.coverTarget wd.hab wd.hOne).edges) ≠ g'.1.1.1)
    (hk : (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex g.1 ≠
      (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex g'.1)
    (hrows : (survRow m wd g = rowT m wd ∧ survRow m wd g' = rowR m wd) ∨
      (survRow m wd g = rowR m wd ∧ survRow m wd g' = rowT m wd)) :
    ColumnReceiptLink m wd := by
  classical
  have hgd : (⟨g.1, hgi⟩ : IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩ anchorBlk)) ∈
      directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        (survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
          ⟨g.1, hgi⟩) :=
    (mem_directionSurvivors _ _ _ _ _).mpr
      ⟨(W3R1SourceProfile.mem_survivors _ _ _).mpr g.2, (edge_survivorLabel _ _ _ _).symm⟩
  have hg'd : (⟨g'.1, hg'i⟩ : IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩ anchorBlk)) ∈
      directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        (survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
          ⟨g'.1, hg'i⟩) :=
    (mem_directionSurvivors _ _ _ _ _).mpr
      ⟨(W3R1SourceProfile.mem_survivors _ _ _).mpr g'.2, (edge_survivorLabel _ _ _ _).symm⟩
  have hdne : survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        ⟨g.1, hgi⟩ ≠
      survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        ⟨g'.1, hg'i⟩ := by
    intro hbad
    refine hne ?_
    rw [← edge_survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        ⟨g.1, hgi⟩,
      ← edge_survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        ⟨g'.1, hg'i⟩, hbad]
  have hcase : ∀ d : Fin 2, d = 0 ∨ d = 1 := by decide
  rcases hcase (survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      ⟨g.1, hgi⟩) with hd | hd
  · rcases hcase (survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
        anchorBlk ⟨g'.1, hg'i⟩) with hd' | hd'
    · exact absurd (hd.trans hd'.symm) hdne
    · rw [hd] at hgd
      rw [hd'] at hg'd
      exact columnReceiptLink_of_splitPair_dir m wd wallStar anchorBlk src hsplit g g' hgi hg'i
          hgd hg'd
        hk hrows
  · rcases hcase (survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
        anchorBlk ⟨g'.1, hg'i⟩) with hd' | hd'
    · rw [hd] at hgd
      rw [hd'] at hg'd
      refine columnReceiptLink_of_splitPair_dir m wd wallStar anchorBlk src hsplit g' g hg'i hgi
          hg'd hgd
        (Ne.symm hk) ?_
      rcases hrows with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inr ⟨hb, ha⟩
      · exact Or.inl ⟨hb, ha⟩
    · exact absurd (hd.trans hd'.symm) hdne

end Split

end BaseOneAndSplit

/-! ## 6b.  The headline: the column receipt at every wall -/

section Headline

open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)

/-- **Valency two with the column receipt.**  `NonTrivalentValencyTwoDispatcher.typeChangeLink_two`
fed with the two cross-pair halves `NonTrivalentValencyTwoBaseOneLink.baseOneCrossLink` and
`splitCrossLink`, split along the index dichotomy exactly as
`crossPairLink_of_index_dichotomy` does. -/
theorem columnReceiptLink_two
    (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 2) :
    ColumnReceiptLink m wd := by
  classical
  rcases columnReceiptLink_or_crossPair m wd h2 with h | ⟨blk, g, g', hsrc, hsplit, hg, hg', hne,
      hrows⟩
  · exact h
  · by_cases hk : (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex g.1 =
        (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex g'.1
    · exact columnReceiptLink_of_crossPair m wd (TwoStar.of_card h2) blk g g' hsrc hsplit hg hg'
        hne hrows hk
    · exact columnReceiptLink_of_splitPair m wd (TwoStar.of_card h2) blk hsrc hsplit g g' hg hg'
        hne hk hrows

/-- **The column-receipt-carrying `link_all`**.  At every wall datum of
every Whitehead move -- valency two, three or four, by `OuterWalk.WallData.valency` -- there
is a Part I type-change link carrying `ColumnReceipt`: its outgoing
vanishing column is the regrown occurrence, and its base is the wall datum by a geometric
isomorphism under which every retained outgoing column is the wall labelling's column.
No hypothesis. -/
theorem exists_link_with_columnReceipt :
    ∃ link : TypeChangeLink m wd, ColumnReceipt link := by
  rcases NonTrivalentValencyFourDispatcher.valency_four_or_three_or_two m wd with h | h | h
  · exact columnReceiptLink_four m wd h
  · exact columnReceiptLink_three m wd h
  · exact columnReceiptLink_two m wd h

/-- The same in the shape of `NonTrivalentValencyTwoBaseOneLink.link_all`'s binder. -/
theorem link_all_columnReceipt {G : CubicDartGraph D V} :
    ∀ K : CubicDartGraph D V, CubicDartGraph.Reaches G K →
      ∀ (m : K.MoveData) (arrival : FacetArrival degree K label (label m.base))
        (wd : WallData arrival), ∃ link : TypeChangeLink m wd, ColumnReceipt link :=
  fun _ _ m _ wd ↦ exists_link_with_columnReceipt m wd

end Headline



/-! ## 7.  The facet level: `ColumnLinkReceipts` and `MetricLinkReceipts` both ways -/

section Composite

open FacetAdapterPilot MemberCertifiedPencil ValencyThreeGeneral FacetMachine
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore)
open DraismaVargas.Count.WallStar (Regrowth)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)

variable {n p degree : ℕ} {c : CubicCore n p} {y₀ : Fin p → ℚ} {ε : ℚ}

theorem column_of_receipt (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree)
    (w : Regrowth c.core y₀ degree) (ms : MemberSeed (w.frame.member y₀))
    (link : TypeChangeLink (pulledMove w ms m') (moveWallData m' hd hG hDegree w ms))
    (hrec : ColumnReceipt link) :
    ∃ iso : GeometricDatumIso w.limit (farRegrowth m' hd hG hDegree w ms link).limit,
      ∀ e, limitCol (farRegrowth m' hd hG hDegree w ms link) (iso.targetEdge e) =
        limitCol w e := by
  obtain ⟨hbase, hcol⟩ := hrec.base_col
  let far : GeometricDatumIso (farRegrowth m' hd hG hDegree w ms link).limit link.base :=
    candidateLimitIso link.candidate rfl (fst_ne_snd _)
      ((farRegrowth m' hd hG hDegree w ms link).frame.numEdges_edgeOf w.column) hrec.column_new
  refine ⟨((limitIsoWallDatum m' hd hG hDegree w ms).trans hbase.symm).trans far.symm, ?_⟩
  intro e
  have hu : w.frame.fullDim.labelling.targetEdge (limitCol w e) = unfoldEdge rfl
      (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) e := by
    rw [limitCol, Equiv.apply_symm_apply]
  have h1 : unfoldEdge (moveWallData m' hd hG hDegree w ms).hc
      (moveWallData m' hd hG hDegree w ms).hab (moveWallData m' hd hG hDegree w ms).hOne
      ((limitIsoWallDatum m' hd hG hDegree w ms).targetEdge e) =
      ms.fullDim.labelling.targetEdge (limitCol w e) := by
    have := GeometricLimitTransport.unfoldEdge_contractDatumIsoOfEdgeEq (seedDatumIso w ms)
      (w.frame.edgeOf w.column) (ms.fullDim.labelling.targetEdge w.column)
      (seedDatumIso_targetEdge w ms w.column) (w.frame.numEdges_edgeOf w.column)
      (moveWallData m' hd hG hDegree w ms).hOne e
    refine this.trans ?_
    rw [← hu]
    exact seedDatumIso_targetEdge w ms (limitCol w e)
  have hjne : limitCol w e ≠
      (moveWallData m' hd hG hDegree w ms).fullDim.labelling.targetEdge.symm
        (moveWallData m' hd hG hDegree w ms).contracted := by
    rw [(moveWallData m' hd hG hDegree w ms).targetEdge_symm_contracted]
    exact limitCol_ne_column w e
  have h2 : (limitIsoWallDatum m' hd hG hDegree w ms).targetEdge e =
      StablePathFacetContraction.punctureTargetEquiv
        (moveWallData m' hd hG hDegree w ms).fullDim.labelling
        (moveWallData m' hd hG hDegree w ms).hc (moveWallData m' hd hG hDegree w ms).hab
        (moveWallData m' hd hG hDegree w ms).hOne ⟨limitCol w e, hjne⟩ := by
    rw [StablePathFacetContraction.punctureTargetEquiv_apply]
    apply (foldEdgeEquiv (moveWallData m' hd hG hDegree w ms).hc
      (moveWallData m' hd hG hDegree w ms).hab (moveWallData m' hd hG hDegree w
          ms).hOne).symm.injective
    apply Subtype.ext
    show unfoldEdge _ _ _ _ = unfoldEdge _ _ _ (foldEdge _ _ _ _)
    rw [unfoldEdge_foldEdge]
    exact h1
  have h3 := hcol ⟨limitCol w e, hjne⟩
  rw [← h2] at h3
  show link.outgoingFD.labelling.targetEdge.symm (unfoldEdge _ _ _ (far.targetEdge.symm
    (hbase.targetEdge.symm ((limitIsoWallDatum m' hd hG hDegree w ms).targetEdge e)))) = _
  have h4 := W4LimitContraction.occurrenceEquiv_edgeEquiv rfl (fst_ne_snd _)
    ((farRegrowth m' hd hG hDegree w ms link).frame.numEdges_edgeOf w.column) hrec.column_new
    (far.targetEdge.symm
      (hbase.targetEdge.symm ((limitIsoWallDatum m' hd hG hDegree w ms).targetEdge e)))
  have h5 : W4LimitContraction.edgeEquiv rfl (fst_ne_snd _)
    ((farRegrowth m' hd hG hDegree w ms link).frame.numEdges_edgeOf w.column) hrec.column_new
    (far.targetEdge.symm
      (hbase.targetEdge.symm ((limitIsoWallDatum m' hd hG hDegree w ms).targetEdge e))) =
      hbase.targetEdge.symm ((limitIsoWallDatum m' hd hG hDegree w ms).targetEdge e) :=
    far.targetEdge.apply_symm_apply _
  have h6 := h4.symm.trans ((congrArg (fun z ↦ occurrenceEquiv
    (contract (moveWallData m' hd hG hDegree w ms).coverTarget
      (moveWallData m' hd hG hDegree w ms).hab (moveWallData m' hd hG hDegree w ms).hOne)
    ⟨(moveWallData m' hd hG hDegree w ms).a, (moveWallData m' hd hG hDegree w ms).hab⟩
    link.candidate.right (some z)) h5).trans h3.symm)
  exact (congrArg link.outgoingFD.labelling.targetEdge.symm h6).trans
    (Equiv.symm_apply_apply _ _)


/-- **`ColumnLinkReceipts` at every facet datum**, with no hypothesis beyond the
binders. -/
theorem columnLinkReceipts (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree) :
    ColumnLinkReceipts m' hd hG hDegree := by
  intro w ms
  obtain ⟨link, hrec⟩ := exists_link_with_columnReceipt (pulledMove w ms m')
    (moveWallData m' hd hG hDegree w ms)
  obtain ⟨iso, hiso⟩ := column_of_receipt m' hd hG hDegree w ms link hrec
  exact ⟨link, iso, hiso⟩

/-- Its reverse twin, at the reversed move and the reversed facet datum. -/
theorem columnLinkReceipts_rev (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree) :
    ColumnLinkReceipts (revMove m') (facetDatum_rev m' hd) hG hDegree :=
  columnLinkReceipts (revMove m') (facetDatum_rev m' hd) hG hDegree

/-- **`MetricLinkReceipts` at every facet datum.** -/
theorem metricLinkReceipts (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree) :
    MetricLinkReceipts m' hd hG hDegree :=
  metricLinkReceipts_of_column m' hd hG hDegree (columnLinkReceipts m' hd hG hDegree)

/-- **`MetricLinkReceipts` at the reversed move.** -/
theorem metricLinkReceipts_rev (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree) :
    MetricLinkReceipts (revMove m') (facetDatum_rev m' hd) hG hDegree :=
  metricLinkReceipts (revMove m') (facetDatum_rev m' hd) hG hDegree

/-- **Metric existence transfer, forward, unconditional.** -/
theorem exists_odd_mSpecializesRight (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree)
    (m : MetricFacetLimit c.core (farCore m').core y₀ degree) (x : FrameClass c.core degree)
    (hx : x.IsOdd) (hs : MSpecializesLeft x m) :
    ∃ x' : FrameClass (farCore m').core degree, x'.IsOdd ∧ MSpecializesRight x' m :=
  ValencyThreeGeneral.exists_odd_mSpecializesRight m' hd hG hDegree
    (metricLinkReceipts m' hd hG (by omega)) m x hx hs

/-- **Metric existence transfer, reverse, unconditional.** -/
theorem exists_odd_mSpecializesLeft (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree)
    (m : MetricFacetLimit c.core (farCore m').core y₀ degree)
    (x' : FrameClass (farCore m').core degree) (hx : x'.IsOdd) (hs : MSpecializesRight x' m) :
    ∃ x : FrameClass c.core degree, x.IsOdd ∧ MSpecializesLeft x m :=
  ValencyThreeGeneral.exists_odd_mSpecializesLeft (revMove m') (farCore_revMove m')
    (facetDatum_rev m' hd) hG hDegree (metricLinkReceipts_rev m' hd hG (by omega)) m x' hx hs

/-! **The uniqueness hypotheses below do not hold at every step.**  At valency-four metric
limits of the `K` family, Part II counts `min(k₂-1, |A|-k₅)+1` members of each type, which is
two at `(|A|; k) = (3; 2,2,2,2)` and `(4; 2,2,3,3)` in degree four; this occurs in genus six.
The implication below is valid, but its hypotheses cannot be discharged at every step, so the
type changes of the assembly use instead a census inside each labelled metric limit with
equal counts through an index (`K` at valency four): `FacetCensus.MetricCensus`, assembled
in `CensusAssembly`. -/
/-- **Facet parity from labelled-metric uniqueness, at a Whitehead step, with the receipts
discharged**: `FacetParity` from labelled-metric uniqueness on each side alone
(`ValencyThreeGeneral.facetParity_of_metricUniqueness` with `hrec`, `hrec'` proved). -/
theorem facetParity_of_metricUniqueness (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree)
    (huniqL : ∀ (m : MetricFacetLimit c.core (farCore m').core y₀ degree)
      (x x' : FrameClass c.core degree),
      x.IsOdd → MSpecializesLeft x m → x'.IsOdd → MSpecializesLeft x' m → x = x')
    (huniqR : ∀ (m : MetricFacetLimit c.core (farCore m').core y₀ degree)
      (x x' : FrameClass (farCore m').core degree),
      x.IsOdd → MSpecializesRight x m → x'.IsOdd → MSpecializesRight x' m → x = x') :
    FacetParity c.core (farCore m').core degree y₀ :=
  ValencyThreeGeneral.facetParity_of_metricUniqueness m' hd hG hDegree huniqL huniqR
    (metricLinkReceipts m' hd hG (by omega)) (metricLinkReceipts_rev m' hd hG (by omega))

end Composite

section Caterpillar

open FacetAdapterPilot MemberCertifiedPencil ValencyThreeGeneral FacetMachine
open DraismaVargas.Count.StepSupplyGenusSix (catCubicCore)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)

variable {y₀ : Fin (6 * 2 + 3) → ℚ} {ε : ℚ}

/-- `ColumnReceiptLink` is inhabited: at a facet-generic facet datum of
`FacetMachine.cat_step`, the caterpillar regrowth's synthetic wall data carry a
column-receipt-carrying link. -/
example : ∃ (y₀ : Fin (6 * 2 + 3) → ℚ) (ε : ℚ)
    (hd : FacetDatum catCubicCore.core catLoopCore.core (2 + 2) catLoopMove.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric (2 + 2) y₀)
    (ms : MemberSeed ((catRegrowth hd.point).frame.member y₀)),
    ColumnReceiptLink (pulledMove (catRegrowth hd.point) ms catLoopMove)
      (moveWallData catLoopMove hd hG (by norm_num) (catRegrowth hd.point) ms) := by
  obtain ⟨y₀, ε, hd, hG⟩ := cat_exists_facetDatum_generic
  obtain ⟨ms⟩ := MemberSeedExists.nonempty_memberSeed_of_member
    ((catRegrowth hd.point).frame.member y₀) (by norm_num)
  exact ⟨y₀, ε, hd, hG, ms, exists_link_with_columnReceipt _ _⟩

end Caterpillar

end DraismaVargas.Count.ColumnReceiptExport
