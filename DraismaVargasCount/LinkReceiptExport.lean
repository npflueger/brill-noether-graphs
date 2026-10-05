module

public import DraismaVargasCount.FacetAdapterPilot

@[expose] public section

/-!
# Exporting `LinkLimitReceipt` through the type-change dispatchers

**Source.**  Vargas, Part II (arXiv:2609.09109), the section on changing combinatorial
type: the labelling convention at a non-trivalent wall (subsection *Combinatorial setup
and local determinants*) and the valency-4, valency-3 and valency-2 cases; Part I's
type-change exits.  The consumer is `FacetAdapterPilot`, whose Stage A takes
`FacetLinkReceipts` as a hypothesis.  This is an input of the type-change parity
(step 3 of `Assembly`).

## The obligation, and what is proved

`FacetAdapterPilot.LinkLimitReceipt link` has two fields: the outgoing vanishing column is
the regrown occurrence (`column_new`), and the link's base is geometrically the wall datum
(`base_iso`).  `FacetAdapterPilot` proves it at the valency-three Type III exit only; the
dispatchers return `Nonempty (TypeChangeLink m wd)`, which forgets it.

* **§1, the six exits carry the receipt.**
  `receipt_four` (valency four, `NonTrivalentValencyFourExit.typeChangeLink_of_receipts`),
  `receipt_simple` (valency three, Types I/II), `receipt_free` (valency two, Base II merge),
  `receipt_baseOne` (Base I), `receipt_split` (Configuration A split), plus
  `FacetAdapterPilot.linkLimitReceipt_valencyThreeTypeIII`.  In every case `column_new` is
  the reindexing lemma `targetEdge_reindex` at `colChart.symm wd.column = none` followed by
  `rfl` (each exit's labelling sends `none` to `occurrenceEquiv … none` definitionally), and
  `base_iso` is: `GeometricDatumIso.refl` at Base II; `(ofStrict (DatumIso.ofSheetRelabeling
  _)).symm` at valency four, Base I and split (each gauge is `relabeling.apply` of one
  `GluingDatum.SheetRelabeling`); the composite of two such at Types I/II
  (`SimpleBase.gaugedData = secondRelabeling.apply` over `middleData = firstRelabeling.apply`).
* **§2, the wrappers transport it.**  `ReceiptLink.ofSwap` (`linkOfSwap` keeps
  `base`/`candidate`/`outgoingFD`, `swapWallData` keeps every field) and
  `ReceiptLink.ofMirror` (`linkOfMirror` changes only `tracks`); both are one-line.
* **§3--§5, the dispatchers with the receipt.**  The valency-four dispatcher
  (`receiptLink_of_orientation_four`, `receiptLink_four`), the valency-three dispatcher
  (`leafIII`, `leafSimple`, `receiptLink_of_doubled`, `receiptLink_of_simple`,
  `receiptLink_of_orientation_three`, `receiptLink_three`), and the valency-two chain
  (`receiptLink_of_prescribedMergedMoveAny`, `receiptLink_of_thick_rows`,
  `receiptLink_or_crossPair`, `receiptLink_of_gauged_setup`,
  `receiptLink_of_crossPair_oriented`, `receiptLink_of_crossPair`,
  `receiptLink_of_splitAnchor`, `receiptLink_of_splitPair_oriented`,
  `receiptLink_of_splitPair_dir`, `receiptLink_of_splitPair`, `receiptLink_two`).  Each
  proof is that of the corresponding dispatcher, copied, with
  `Nonempty (TypeChangeLink m wd)` replaced by `ReceiptLink m wd`, the leaf `⟨exit …⟩` by
  `⟨exit …, receipt_…⟩`, and `.map linkOfSwap` / `nonempty_typeChangeLink_of_mirror` by
  the §2 wrappers.
* **§6, the main theorem.**  `exists_link_with_receipt`: at **every** wall datum of every
  Whitehead move, of every valency (two, three, four -- `OuterWalk.WallData.valency`),
  `∃ link : TypeChangeLink m wd, LinkLimitReceipt link`, with no hypothesis;
  `link_all_receipt` is the same quantified over every graph reached by Whitehead moves.
  Hence `facetLinkReceipts` / `facetLinkReceipts_rev`: `FacetAdapterPilot.FacetLinkReceipts`
  at every facet datum of `FacetAdapterPilot`, for `m'` and for `revMove m'`;
  `exists_odd_specializesRight` (the existence transfer `hLR` with no receipt);
  `facetParity_of_uniqueness` (`facetParity_of_uniqueness_and_receipts` with `hrec`,
  `hrec'` discharged); and `cat_obligation_of_uniqueness`
  (`cat_obligation_of_residues` likewise).

## What is NOT proved -- every hypothesis

* **`FacetParity` is not proved here at any step.**  `facetParity_of_uniqueness` and
  `cat_obligation_of_uniqueness` take the two uniqueness halves `huniqL`, `huniqR`
  (near-side uniqueness, reduced in `FacetAdapterPilot` to limit-injectivity of ballot
  members; far-side uniqueness, the valency-3 limits of Part II plus core-label pinning).
  Nothing here touches them.
* **The link chosen by `FacetAdapterPilot.moveLink` is not shown to carry the receipt.**
  `moveLink` is `Nonempty.some` of the dispatchers, and a choice term cannot be inspected;
  what is proved is that *some* link carries it, which is all `FacetLinkReceipts` (an
  existential) asks.  A consumer that needs the receipt at `moveLink` itself must instead
  choose from `exists_link_with_receipt`.
* The dispatcher proofs are duplicated from the dispatcher modules (about 1150 lines).
  If a dispatcher changes, this copy does not follow it; the duplication could be removed
  by stating the `ReceiptLink` versions in the dispatcher files themselves.
* `3 ≤ degree` (the `MemberSeed` receipt of `FacetAdapterPilot`) remains explicit in the
  facet corollaries.
* No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`, no `#eval`.
-/

set_option autoImplicit false

namespace DraismaVargas.Count.LinkReceiptExport

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
open DraismaVargas.Count.FacetAdapterPilot (LinkLimitReceipt)
open DraismaVargas.Count (GeometricDatumIso)

/-! ## 0.  Preliminaries -/

/-- The reindexed labelling reads the target edge of a column through the column chart. -/
theorem targetEdge_reindex {targetX : CFGraph} {deg : ℕ} {datum : GluingDatum targetX deg}
    {X C : Type*} {eRow eCol : X ≃ C} (L : StableLengthMatrixLabelling datum X) (x : C) (y : X)
    (h : eCol.symm x = y) :
    (NonTrivalentValencyTwoExit.reindexLabelling₂ eRow eCol L).targetEdge x = L.targetEdge y := by
  subst h; rfl

/-- **The receipt-carrying link.**  Definitionally
`∃ link : TypeChangeLink m wd, FacetAdapterPilot.LinkLimitReceipt link`, the inner shape of
`FacetAdapterPilot.FacetLinkReceipts`. -/
abbrev ReceiptLink {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
    {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] {degree : ℕ}
    {graph : CubicDartGraph D V} {label : D → coordinate} (m : graph.MoveData)
    {arrival : FacetArrival degree graph label (label m.base)} (wd : WallData arrival) : Prop :=
  ∃ link : TypeChangeLink m wd, LinkLimitReceipt link


/-! ## 1.  The six exits carry the receipt -/

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
theorem receipt_four
    (tracks : Tracks (NonTrivalentValencyFourExit.wallOutgoingFD m wd wallStar anchorBlock
      hAnchor pairing) (graph.move m) label) :
    LinkLimitReceipt (NonTrivalentValencyFourExit.typeChangeLink_of_receipts m wd wallStar
      anchorBlock hAnchor pairing tracks) := by
  refine ⟨?_, ⟨(GeometricDatumIso.ofStrict
    (Count.Transport.DatumIso.ofSheetRelabeling _)).symm⟩⟩
  have h2 : (NonTrivalentValencyTwoExit.colChart wd.cover wd.fullDim
      (contracted := wd.contracted)).symm wd.column = none := by
    rw [← wd.targetEdge_symm_contracted]
    exact Equiv.optionSubtypeNe_symm_self _
  exact (targetEdge_reindex _ _ _ h2).trans rfl

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
theorem receipt_free
    (tracks : Tracks (NonTrivalentValencyTwoExitFree.wallOutgoingFD' m wd src sel hOrd labelling₀
      hRowVal hMatrixWall) (graph.move m) label) :
    LinkLimitReceipt (NonTrivalentValencyTwoExitFree.typeChangeLink_of_receipts_free m wd src sel
      hOrd labelling₀ hRowVal hMatrixWall tracks) := by
  refine ⟨?_, ⟨GeometricDatumIso.refl _⟩⟩
  have h2 : (NonTrivalentValencyTwoExit.colChart wd.cover wd.fullDim
      (contracted := wd.contracted)).symm wd.column = none := by
    rw [← wd.targetEdge_symm_contracted]
    exact Equiv.optionSubtypeNe_symm_self _
  exact (targetEdge_reindex _ _ _ h2).trans rfl

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

/-- **Valency two, Base I** (the Base I gauge is one sheet relabelling). -/
theorem receipt_baseOne
    (tracks : Tracks (NonTrivalentValencyTwoBaseOneExit.wallOutgoingFD m wd wallStar anchorBlk
      thickSheet thinSheet labelling₀ setup hGauged hOrd hRowVal hMatrixWall) (graph.move m) label) :
    LinkLimitReceipt (NonTrivalentValencyTwoBaseOneExit.typeChangeLink_of_receipts_baseOne m wd
      wallStar anchorBlk thickSheet thinSheet labelling₀ setup hGauged hOrd hRowVal hMatrixWall
      tracks) := by
  refine ⟨?_, ⟨(GeometricDatumIso.ofStrict (Count.Transport.DatumIso.ofSheetRelabeling _)).symm⟩⟩
  have h2 : (NonTrivalentValencyTwoExit.colChart wd.cover wd.fullDim
      (contracted := wd.contracted)).symm wd.column = none := by
    rw [← wd.targetEdge_symm_contracted]
    exact Equiv.optionSubtypeNe_symm_self _
  exact (targetEdge_reindex _ _ _ h2).trans rfl

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

/-- **Valency two, Configuration A split** (the split gauge is one sheet relabelling). -/
theorem receipt_split
    (tracks : Tracks (NonTrivalentValencyTwoSplitExit.wallOutgoingFD m wd wallStar anchorBlk
      thickSheet thinSheet labelling₀ ra hGauged hOrdGauged hRowVal hMatrixWall)
      (graph.move m) label) :
    LinkLimitReceipt (NonTrivalentValencyTwoSplitExit.typeChangeLink_of_receipts_split m wd
      wallStar anchorBlk thickSheet thinSheet labelling₀ ra hGauged hOrdGauged hRowVal
      hMatrixWall tracks) := by
  refine ⟨?_, ⟨(GeometricDatumIso.ofStrict (Count.Transport.DatumIso.ofSheetRelabeling _)).symm⟩⟩
  have h2 : (NonTrivalentValencyTwoExit.colChart wd.cover wd.fullDim
      (contracted := wd.contracted)).symm wd.column = none := by
    rw [← wd.targetEdge_symm_contracted]
    exact Equiv.optionSubtypeNe_symm_self _
  exact (targetEdge_reindex _ _ _ h2).trans rfl

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
theorem receipt_simple
    (tracks : Tracks (NonTrivalentValencyThreeSimpleExit.wallOutgoingFD m wd simpleBase hValid)
      (graph.move m) label) :
    LinkLimitReceipt (NonTrivalentValencyThreeSimpleExit.typeChangeLink_of_receipts m wd
      simpleBase hValid tracks) := by
  refine ⟨?_, ⟨((GeometricDatumIso.ofStrict (Count.Transport.DatumIso.ofSheetRelabeling _)).trans
    (GeometricDatumIso.ofStrict (Count.Transport.DatumIso.ofSheetRelabeling _))).symm⟩⟩
  have h2 : (NonTrivalentValencyTwoExit.colChart wd.cover wd.fullDim
      (contracted := wd.contracted)).symm wd.column = none := by
    rw [← wd.targetEdge_symm_contracted]
    exact Equiv.optionSubtypeNe_symm_self _
  exact (targetEdge_reindex _ _ _ h2).trans rfl

end Simple

/-! ## 2.  The swap and mirror wrappers transport the receipt -/

section Wrappers

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)

theorem ReceiptLink.nonempty (h : ReceiptLink m wd) : Nonempty (TypeChangeLink m wd) :=
  let ⟨link, _⟩ := h; ⟨link⟩

/-- **The swap wrapper transports the receipt**:
`NonTrivalentValencyFourDispatcher.linkOfSwap` keeps `base`, `candidate` and `outgoingFD`
literally, and `swapWallData` keeps every field of the wall data. -/
theorem ReceiptLink.ofSwap (hL : label (graph.op m.base) = label m.base)
    (h : ReceiptLink m.swap (NonTrivalentValencyFourDispatcher.swapWallData m wd hL)) :
    ReceiptLink m wd :=
  let ⟨link, hrec⟩ := h
  ⟨NonTrivalentValencyFourDispatcher.linkOfSwap m wd hL link, hrec.column_new, hrec.base_iso⟩

/-- **The mirror wrapper transports the receipt**:
`MoveMirror.linkOfMirror` changes only `tracks`. -/
theorem ReceiptLink.ofMirror (hL : label (graph.op m.base) = label m.base)
    (h : ReceiptLink (MoveMirror.mirror m) wd) : ReceiptLink m wd :=
  let ⟨link, hrec⟩ := h
  ⟨MoveMirror.linkOfMirror m wd hL link, hrec.column_new, hrec.base_iso⟩

end Wrappers

/-! ## 3.  Valency four: `NonTrivalentValencyFourDispatcher.typeChangeLink_four` with the receipt

The proofs below are those of `NonTrivalentValencyFourDispatcher`, copied verbatim except
that the leaf returns the receipt (`receipt_four`) and the swap branch uses
`ReceiptLink.ofSwap`. -/

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

theorem receiptLink_of_orientation_four
    (h4 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 4)
    (hBase : wd.tracks.iso.dart
      (facetDartLeft m wd (W4TargetPairings.FourStar.of_card h4)) = m.base) :
    ReceiptLink m wd := by
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
      hAnchor 0, ReceiptLink m wd := fun hPres ↦
    ⟨NonTrivalentValencyFourStarCount.typeChangeLink_of_prescribedPairingMove m wd star
      anchorBlock hAnchor 0 hPres, receipt_four _ _ _ _ _ _ _⟩
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
theorem receiptLink_four
    (h4 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 4) :
    ReceiptLink m wd := by
  classical
  rcases dart_facetDartLeft_cases m wd (W4TargetPairings.FourStar.of_card h4) with h | h
  · exact receiptLink_of_orientation_four m wd h4 h
  · have hL : label (graph.op m.base) = label m.base :=
      MovedIncidenceIso.label_op_of_tracks _ wd.fullDim wd.tracks m.base
    have hBase' : (swapWallData m wd hL).tracks.iso.dart
        (facetDartLeft m.swap (swapWallData m wd hL)
          (W4TargetPairings.FourStar.of_card h4)) = m.swap.base :=
      (congrArg wd.tracks.iso.dart
        (facetDartLeft_swap m wd hL (W4TargetPairings.FourStar.of_card h4))).trans h
    exact ReceiptLink.ofSwap m wd hL
      (receiptLink_of_orientation_four m.swap (swapWallData m wd hL) h4 hBase')

end DispatchFour

/-! ## 4.  Valency three: `NonTrivalentValencyThreeDispatcher.typeChangeLink_three` with the receipt

The proofs of `NonTrivalentValencyThreeDispatcher`, verbatim except at the leaves
(`leafIII`, `leafSimple`: the receipt of the
Type III and Types I/II exits) and the wrappers (`ReceiptLink.ofMirror`, `ReceiptLink.ofSwap`). -/

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
(`FacetAdapterPilot.linkLimitReceipt_valencyThreeTypeIII`).  Same arguments as
`NonTrivalentValencyThreeStarCount.typeChangeLink_of_prescribedDoubledMove`. -/
theorem leafIII
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)
    (hPres : NonTrivalentValencyThreeTracks.PrescribedDoubledMove m wd wallStar src) :
    ReceiptLink m wd :=
  ⟨NonTrivalentValencyThreeStarCount.typeChangeLink_of_prescribedDoubledMove m wd wallStar src
      hNoGlue hValid hPres,
    FacetAdapterPilot.linkLimitReceipt_valencyThreeTypeIII m wd src hNoGlue hValid _ _⟩

/-- **Types I/II leaf**: the simple link carries the receipt (`receipt_simple`).
Same arguments as `NonTrivalentValencyThreeSimpleStarCount.typeChangeLink_of_prescribedSimpleMove`. -/
theorem leafSimple {wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
    (base : SimpleBase (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)
    (hPres : NonTrivalentValencyThreeSimpleTracks.PrescribedSimpleMove m wd base) :
    ReceiptLink m wd :=
  ⟨NonTrivalentValencyThreeSimpleStarCount.typeChangeLink_of_prescribedSimpleMove m wd base
      hValid hPres, receipt_simple _ _ _ _ _⟩

variable (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
  (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)
  (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))

variable (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base)

include wallStar src hValid hNoGlue hBase in
/-- **Type III**: the move puts the two doubled-direction survivors at
`graph.vert m.base`. -/
theorem receiptLink_of_doubled (j : Bool)
    (hk : keptRow m wd = (doubledND src j).stablePath)
    (hb : broughtRow m wd = (doubledND src (!j)).stablePath) :
    ReceiptLink m wd := by
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
theorem receiptLink_of_simple (i j : Bool) (hR : Realisable m wd wallStar src i j)
    (hpair : (keptRow m wd = (simpleND src i).stablePath ∧
        broughtRow m wd = (doubledND src j).stablePath) ∨
      (keptRow m wd = (doubledND src j).stablePath ∧
        broughtRow m wd = (simpleND src i).stablePath)) :
    ReceiptLink m wd := by
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
theorem receiptLink_of_orientation_three : ReceiptLink m wd := by
  classical
  have hL : label (graph.op m.base) = label m.base :=
    MovedIncidenceIso.label_op_of_tracks _ wd.fullDim wd.tracks m.base
  have hBase' : wd.tracks.iso.dart (facetDartLeft (mirror m) wd wallStar) = (mirror m).base := hBase
  rcases classify m wd wallStar src hValid hBase with hA | hB | hC
  · obtain ⟨j, hk, hb⟩ := hA
    exact receiptLink_of_doubled m wd wallStar src hValid hNoGlue hBase j hk hb
  · obtain ⟨j, hs, hst⟩ := hB
    refine ReceiptLink.ofMirror m wd hL ?_
    refine receiptLink_of_doubled (mirror m) wd wallStar src hValid hNoGlue hBase' j ?_ ?_
    · rw [keptRow_mirror m wd wallStar]
      exact hs
    · rw [broughtRow_mirror m wd wallStar]
      exact hst
  · obtain ⟨i, j, hp, hq⟩ := hC
    rcases realisable_or m wd wallStar src i j with hR | hR
    · exact receiptLink_of_simple m wd wallStar src hValid hNoGlue hBase i j hR hp
    · refine ReceiptLink.ofMirror m wd hL ?_
      refine receiptLink_of_simple (mirror m) wd wallStar src hValid hNoGlue hBase' (!i) (!j) hR ?_
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
theorem receiptLink_three
    (h3 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 3) :
    ReceiptLink m wd := by
  classical
  obtain ⟨anchorBlk, src, hNoGlue, hValid, -, -⟩ :=
    NonTrivalentValencyThreeExit.exists_anchor_of_wallData m wd (ThreeStar.of_card h3)
  rcases dart_facetDartLeft_cases_three m wd (ThreeStar.of_card h3) with h | h
  · exact receiptLink_of_orientation_three m wd (ThreeStar.of_card h3) src hValid hNoGlue h
  · have hL : label (graph.op m.base) = label m.base :=
      MovedIncidenceIso.label_op_of_tracks _ wd.fullDim wd.tracks m.base
    have hBase' : (NonTrivalentValencyFourDispatcher.swapWallData m wd hL).tracks.iso.dart
        (facetDartLeft m.swap (NonTrivalentValencyFourDispatcher.swapWallData m wd hL)
          (ThreeStar.of_card h3)) = m.swap.base :=
      (congrArg wd.tracks.iso.dart
        (facetDartLeft_swap_three m wd hL (ThreeStar.of_card h3))).trans h
    exact ReceiptLink.ofSwap m wd hL (receiptLink_of_orientation_three m.swap
      (NonTrivalentValencyFourDispatcher.swapWallData m wd hL) (ThreeStar.of_card h3) src hValid
      hNoGlue hBase')


end HeadlineThree

/-! ## 5.  Valency two

The proofs of the valency-two dispatcher chain, verbatim except at the leaves (the Base II merge, Base I and
split exits, whose receipts are `receipt_free`, `receipt_baseOne`, `receipt_split`) and the
swap wrapper (`ReceiptLink.ofSwap`). -/

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


include src hOrd labelling₀ hRowVal hMatrixWall in
/-- **`OuterWalk.TypeChangeLink` at any two-valent Base II wall, from the
dispatcher's (H-II) alone.**  The incoming `2 + 2` / `1 + 3` / `3 + 1`
trichotomy and the orientation of the two ends are discharged internally. -/
theorem receiptLink_of_prescribedMergedMoveAny
    (hPres : PrescribedMergedMoveAny m wd sel) : ReceiptLink m wd := by
  classical
  obtain ⟨E⟩ := nonempty_vanishingEnds m wd src hOrd
  rcases prescribedMergedMoveOn_of_any m wd sel E hPres with h | h
  · exact ⟨typeChangeLink_of_prescribedMergedMove_two m wd src sel hOrd labelling₀ hRowVal
      hMatrixWall E h, receipt_free ..⟩
  · exact ⟨typeChangeLink_of_prescribedMergedMove_two m wd src sel hOrd labelling₀ hRowVal
      hMatrixWall (swapEnds m wd E) h, receipt_free ..⟩

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

include src hOrd labelling₀ hRowVal hMatrixWall in
/-- **The link when the two survivors the move brings together lie over the *same*
target direction** -- the Base II merge.  Nothing but the wall data and the two named
survivors enters: the Base II merge theorem turns (H-II) into the link at any two-valent Base II
wall, and (H-II) is discharged here from the moved star
(`IncomingPairing.exists_movedStar_darts` in the explicit form `movedStar_base`). -/
theorem receiptLink_of_thick_rows
    (g g' : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hg : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g.1
      (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk))
    (hg' : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g'.1
      (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk))
    (hne : g ≠ g')
    (hgT : IsThickSurv m wd wallStar anchorBlk g)
    (hgT' : IsThickSurv m wd wallStar anchorBlk g')
    (hrow : survRow m wd g = rowT m wd) (hrow' : survRow m wd g' = rowR m wd) :
    ReceiptLink m wd := by
  classical
  refine receiptLink_of_prescribedMergedMoveAny m wd src
    { first := ⟨g.1, hg⟩
      second := ⟨g'.1, hg'⟩
      first_ne_second := fun h ↦ hne (Subtype.ext (congrArg
        (fun e : IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk) ↦ e.1) h))
      first_mem := (mem_directionSurvivors _ _ _ _ _).mpr
        ⟨(W3R1SourceProfile.mem_survivors _ _ _).mpr g.2, hgT⟩
      second_mem := (mem_directionSurvivors _ _ _ _ _).mpr
        ⟨(W3R1SourceProfile.mem_survivors _ _ _).mpr g'.2, hgT'⟩ }
    hOrd labelling₀ hRowVal hMatrixWall ?_
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
theorem receiptLink_or_crossPair
    (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 2) :
    ReceiptLink m wd ∨
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
  obtain ⟨labelling₀, hRowVal, hMatrixWall⟩ :=
    NonTrivalentValencyTwoBaseOneRowDictionary.exists_wallLabelling_two wd.cover wd.fullDim
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
  · exact Or.inl (receiptLink_of_thick_rows m wd src hOrd labelling₀ hRowVal
      hMatrixWall _ _ (incident_survEquiv m wd hEnds src hOrd 1)
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
    exact Or.inl (ReceiptLink.ofSwap m wd hL (receiptLink_of_thick_rows m.swap
      (NonTrivalentValencyFourDispatcher.swapWallData m wd hL) src hOrd labelling₀ hRowVal'
      hMatrixWall _ _ (incident_survEquiv m wd hEnds src hOrd 3)
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
move names.**  The Base I star count with (H-BaseI) discharged by
`prescribedBaseOneMove_of_unordered_rows`; the wall labelling, the anchor ends and
the ordinary-block trivalence are produced from the wall data. -/
theorem receiptLink_of_gauged_setup (m : graph.MoveData)
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
    ReceiptLink m wd := by
  classical
  have hNd := NonTrivalentValencyTwoRows.nonDanglingValency_anchor src
  have hOrd := NonTrivalentValencyTwoRowEquiv.ordinaryTrivalent_of_wall_metric wd.cover
    wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m) wallStar wd.coordinates (label m.base)
    wd.hRows wd.hZeroCoord anchorBlk hNd
  obtain ⟨labelling₀, hRowVal, hMatrixWall⟩ :=
    NonTrivalentValencyTwoBaseOneRowDictionary.exists_wallLabelling_two wd.cover wd.fullDim
      wd.hc wd.hab wd.hOne (wd.hForest m) (label m.base) wallStar wd.coordinates wd.hRows
      wd.hZeroCoord wd.hPosCoord wd.hFacetZero
  obtain ⟨Ends⟩ := NonTrivalentValencyTwoStarCountAll.nonempty_vanishingEnds m wd src hOrd
  have hEnds := anchorEnds_base m wd Ends
  have hGauged := gaugedData_valid (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
    anchorBlk thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd)
  exact ⟨typeChangeLink_of_prescribedBaseOneMove m wd thickSheet thinSheet setup hGauged hOrd
    src labelling₀ hRowVal hMatrixWall hEnds
    (prescribedBaseOneMove_of_unordered_rows m wd thickSheet thinSheet setup hA1),
    receipt_baseOne ..⟩

/-- **The Base I link at a Configuration A cross pair, with the two members named by
direction.**  `P` lies over `star.edge 0`, `Q` over `star.edge 1`, they have equal
dilation indices, and their incoming rows are the two rows the move names.  The
`t₃`-alignment gauge of the Base I construction turns the two index equalities into a Base I setup;
`crossPair_identification` says the pair the setup puts at `A₁` is `{P, Q}` or the
complementary pair, and in the second case the same construction discharges the move
read from the other end of the contracted edge (`MoveData.swap`), whose own pair is
exactly the complementary one. -/
theorem receiptLink_of_crossPair_oriented (m : graph.MoveData)
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
    ReceiptLink m wd := by
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
    refine receiptLink_of_gauged_setup m wd wallStar anchorBlk src _ _ setup ?_
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
    refine ReceiptLink.ofSwap m wd hL (receiptLink_of_gauged_setup m.swap
      (NonTrivalentValencyFourDispatcher.swapWallData m wd hL) wallStar anchorBlk src _ _ setup ?_)
    rcases hcomp with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inr ⟨e0.trans ha, e1.trans hb⟩
    · exact Or.inl ⟨e0.trans ha, e1.trans hb⟩

/-- **The Base I link at a Configuration A cross pair.**  Neither member is named by
direction: the two survivors lie over different target occurrences, so one lies over
each direction of the incoming two-valent star. -/
theorem receiptLink_of_crossPair (m : graph.MoveData)
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
    ReceiptLink m wd := by
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
      exact receiptLink_of_crossPair_oriented m wd wallStar anchorBlk src hsplit g g' hg hg' hgd hg'd
        hk hrows
  · rcases hcase (survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        ⟨g'.1, hg'⟩) with hd' | hd'
    · rw [hd] at hgd
      rw [hd'] at hg'd
      refine receiptLink_of_crossPair_oriented m wd wallStar anchorBlk src hsplit g' g hg' hg hg'd hgd
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
the move names.**  The split star count with (H-split) discharged: the survivor clause
of `PrescribedSplitMove` does not order the pair, so either assignment works. -/
theorem receiptLink_of_splitAnchor
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
    ReceiptLink m wd := by
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
  obtain ⟨labelling₀, hRowVal, hMatrixWall⟩ :=
    NonTrivalentValencyTwoBaseOneRowDictionary.exists_wallLabelling_two wd.cover wd.fullDim
      wd.hc wd.hab wd.hOne (wd.hForest m) (label m.base) wallStar wd.coordinates wd.hRows
      wd.hZeroCoord wd.hPosCoord wd.hFacetZero
  obtain ⟨Ends⟩ := NonTrivalentValencyTwoStarCountAll.nonempty_vanishingEnds m wd src hOrd
  have hEnds := anchorEnds_base m wd Ends
  have e0 := splitLift_stablePath_eq_survRow m wd wallStar anchorBlk thickSheet thinSheet ra
    false A hA
  have e1 := splitLift_stablePath_eq_survRow m wd wallStar anchorBlk thickSheet thinSheet ra
    true Dl hD
  have key := fun hPres ↦ (⟨NonTrivalentValencyTwoSplitStarCount.typeChangeLink_of_prescribedSplitMove
    m wd thickSheet thinSheet ra hGauged hOrdGauged hOrd src labelling₀ hRowVal hMatrixWall hEnds
    hPres, receipt_split ..⟩ : ReceiptLink m wd)
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
`A` lies over `star.edge 0`, `Dl` over `star.edge 1`, and `k_delta < k_alpha` (in Part II's
valency-2 limits, Configuration A: exactly the case in which the Base I member does not
exist). -/
theorem receiptLink_of_splitPair_oriented
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
    ReceiptLink m wd := by
  classical
  obtain ⟨B, hB, hBne⟩ := other_of_pair (hsplit 0) hA
  obtain ⟨Eps, hEps, hEpsNe⟩ := other_of_pair (hsplit 1) hD
  have hValid := NonTrivalentValencyTwoTracks.wallValid m wd
  refine receiptLink_of_splitAnchor m wd wallStar anchorBlk src _ _
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
member, and when it points the other way the mirror member (`relabelStar`)
realises the pairing. -/
theorem receiptLink_of_splitPair_dir
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
    ReceiptLink m wd := by
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
  · refine receiptLink_of_splitPair_oriented m wd (relabelStar wallStar) anchorBlk
      (twoBranchAnchor_relabelStar src) (split_relabelStar hsplit) g' g hg'i hgi ?_ ?_ hlt ?_
    · rw [hz]
      exact hg'd
    · rw [ho]
      exact hgd
    · rcases hrows with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inr ⟨hb, ha⟩
      · exact Or.inl ⟨hb, ha⟩
  · exact receiptLink_of_splitPair_oriented m wd wallStar anchorBlk src hsplit g g' hgi hg'i hgd hg'd
      hlt hrows

/-- **The split link at a Configuration A cross pair.**  Neither member is named by
direction; the two survivors lie over different target occurrences, so one lies over
each direction. -/
theorem receiptLink_of_splitPair
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
    ReceiptLink m wd := by
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
      exact receiptLink_of_splitPair_dir m wd wallStar anchorBlk src hsplit g g' hgi hg'i hgd hg'd
        hk hrows
  · rcases hcase (survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
        anchorBlk ⟨g'.1, hg'i⟩) with hd' | hd'
    · rw [hd] at hgd
      rw [hd'] at hg'd
      refine receiptLink_of_splitPair_dir m wd wallStar anchorBlk src hsplit g' g hg'i hgi hg'd hgd
        (Ne.symm hk) ?_
      rcases hrows with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inr ⟨hb, ha⟩
      · exact Or.inl ⟨hb, ha⟩
    · exact absurd (hd.trans hd'.symm) hdne

end Split

end BaseOneAndSplit

/-! ## 6.  The headline: the receipt at every wall, and `FacetLinkReceipts` both ways -/

section Headline

open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)

/-- **Valency two with the receipt.**  `NonTrivalentValencyTwoDispatcher.typeChangeLink_two`
fed with the two cross-pair halves (`baseOneCrossLink`, `splitCrossLink`), split along
the index dichotomy exactly as `crossPairLink_of_index_dichotomy` does. -/
theorem receiptLink_two
    (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 2) :
    ReceiptLink m wd := by
  classical
  rcases receiptLink_or_crossPair m wd h2 with h | ⟨blk, g, g', hsrc, hsplit, hg, hg', hne, hrows⟩
  · exact h
  · by_cases hk : (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex g.1 =
        (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex g'.1
    · exact receiptLink_of_crossPair m wd (TwoStar.of_card h2) blk g g' hsrc hsplit hg hg' hne
        hrows hk
    · exact receiptLink_of_splitPair m wd (TwoStar.of_card h2) blk hsrc hsplit g g' hg hg' hne
        hk hrows

/-- **Receipt-carrying links exist everywhere.**  At every wall datum of
every Whitehead move -- valency two, three or four, by `OuterWalk.WallData.valency` -- there
is a Part I type-change link carrying `FacetAdapterPilot.LinkLimitReceipt`: its outgoing
vanishing column is the regrown occurrence, and its base is geometrically the wall datum.
No hypothesis. -/
theorem exists_link_with_receipt :
    ∃ link : TypeChangeLink m wd, LinkLimitReceipt link := by
  rcases NonTrivalentValencyFourDispatcher.valency_four_or_three_or_two m wd with h | h | h
  · exact receiptLink_four m wd h
  · exact receiptLink_three m wd h
  · exact receiptLink_two m wd h

/-- The same, quantified over every graph reached by Whitehead moves. -/
theorem link_all_receipt {G : CubicDartGraph D V} :
    ∀ K : CubicDartGraph D V, CubicDartGraph.Reaches G K →
      ∀ (m : K.MoveData) (arrival : FacetArrival degree K label (label m.base))
        (wd : WallData arrival), ∃ link : TypeChangeLink m wd, LinkLimitReceipt link :=
  fun _ _ m _ wd ↦ exists_link_with_receipt m wd

end Headline

section Facet

open DraismaVargas.LocalCases.CoreOfDarts (CubicCore)
open DraismaVargas.Count.WallStar (Regrowth)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)
open DraismaVargas.Count.FacetMachine
open DraismaVargas.Count.FacetAdapterPilot

variable {n p degree : ℕ} {c : CubicCore n p} {y₀ : Fin p → ℚ} {ε : ℚ}

/-- **`FacetLinkReceipts` at every facet datum of `FacetAdapterPilot`.**  The residue of its
Stage A, discharged: the move is arbitrary, so this covers both `m'` and `revMove m'`. -/
theorem facetLinkReceipts (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree) :
    FacetLinkReceipts m' hd hG hDegree :=
  fun _ _ ↦ exists_link_with_receipt _ _

/-- The reverse direction, at the reversed move and the reversed facet datum. -/
theorem facetLinkReceipts_rev (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree) :
    FacetLinkReceipts (revMove m') (facetDatum_rev m' hd) hG hDegree :=
  facetLinkReceipts (revMove m') (facetDatum_rev m' hd) hG hDegree

/-! **Caution: the per-coarse-limit uniqueness hypotheses of the next theorem fail in
general, at valency three as well as four** (computer experiments find coarse limits with
two odd classes on a side, at genus four and at genus six).  The implication stands but its
hypotheses cannot be discharged in general; `ValencyThreeGeneral.facetParity_of_metricUniqueness`
uses uniqueness per labelled metric limit instead. -/
/-- **`FacetParity` at a Whitehead step from the two uniqueness halves alone.**
`FacetAdapterPilot.facetParity_of_uniqueness_and_receipts` with both receipt hypotheses
discharged. -/
theorem facetParity_of_uniqueness (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree)
    (huniqL : ∀ (l : FacetLimit c.core (farCore m').core y₀ degree)
      (x x' : FrameClass c.core degree),
      x.IsOdd → SpecializesLeft x l → x'.IsOdd → SpecializesLeft x' l → x = x')
    (huniqR : ∀ (l : FacetLimit c.core (farCore m').core y₀ degree)
      (x x' : FrameClass (farCore m').core degree),
      x.IsOdd → SpecializesRight x l → x'.IsOdd → SpecializesRight x' l → x = x') :
    FacetParity c.core (farCore m').core degree y₀ :=
  facetParity_of_uniqueness_and_receipts m' hd hG hDegree huniqL huniqR
    (facetLinkReceipts m' hd hG (by omega)) (facetLinkReceipts_rev m' hd hG (by omega))

/-- **Existence transfer with no receipt hypothesis** (`hLR` of
`FacetParityPilot.facetParity_of_unique`): an odd class specialising on the near side has an
odd partner specialising to the same facet limit on the far side. -/
theorem exists_odd_specializesRight (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree)
    (l : FacetLimit c.core (farCore m').core y₀ degree) (x : FrameClass c.core degree)
    (hx : x.IsOdd) (hs : SpecializesLeft x l) :
    ∃ x' : FrameClass (farCore m').core degree, x'.IsOdd ∧ SpecializesRight x' l :=
  exists_odd_specializesRight_of_receipts m' hd hG hDegree
    (facetLinkReceipts m' hd hG (by omega)) l x hx hs

/-- **The caterpillar step's obligation from the two uniqueness halves alone**:
`FacetAdapterPilot.cat_obligation_of_residues` with `hrec`, `hrec'` discharged. -/
theorem cat_obligation_of_uniqueness {y₀ : Fin (6 * 2 + 3) → ℚ} {ε : ℚ}
    (hd : FacetDatum StepSupplyGenusSix.catCubicCore.core catLoopCore.core (2 + 2)
      catLoopMove.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric (2 + 2) y₀)
    (huniqL : ∀ (l : FacetLimit StepSupplyGenusSix.catCubicCore.core catLoopCore.core y₀ (2 + 2))
      (x x' : FrameClass StepSupplyGenusSix.catCubicCore.core (2 + 2)),
      x.IsOdd → SpecializesLeft x l → x'.IsOdd → SpecializesLeft x' l → x = x')
    (huniqR : ∀ (l : FacetLimit StepSupplyGenusSix.catCubicCore.core catLoopCore.core y₀ (2 + 2))
      (x x' : FrameClass catLoopCore.core (2 + 2)),
      x.IsOdd → SpecializesRight x l → x'.IsOdd → SpecializesRight x' l → x = x') :
    ∃ y y' : Fin (6 * 2 + 3) → ℚ,
      SimpleWallSupply.PositiveGeneral StepSupplyGenusSix.catCubicCore.core (2 + 2) y ∧
      SimpleWallSupply.PositiveGeneral catLoopCore.core (2 + 2) y' ∧
        CountTransportLink.CountLink (2 + 2) StepSupplyGenusSix.catCubicCore.core y
          catLoopCore.core y' :=
  cat_obligation_of_residues hd hG huniqL huniqR
    (facetLinkReceipts catLoopMove hd hG (by norm_num))
    (facetLinkReceipts_rev catLoopMove hd hG (by norm_num))

/-- Non-vacuity of `ReceiptLink`: at a generic facet datum of `FacetMachine.cat_step`
(`cat_exists_facetDatum_generic`), the caterpillar regrowth's synthetic wall data carry a
receipt-carrying link. -/
example : ∃ (y₀ : Fin (6 * 2 + 3) → ℚ) (ε : ℚ)
    (hd : FacetDatum StepSupplyGenusSix.catCubicCore.core catLoopCore.core (2 + 2)
      catLoopMove.base.1 y₀ ε) (hG : FacetGenericity.FacetGeneric (2 + 2) y₀)
    (ms : MemberCertifiedPencil.MemberSeed ((catRegrowth hd.point).frame.member y₀)),
    ReceiptLink (pulledMove (catRegrowth hd.point) ms catLoopMove)
      (moveWallData catLoopMove hd hG (by norm_num) (catRegrowth hd.point) ms) := by
  obtain ⟨y₀, ε, hd, hG⟩ := cat_exists_facetDatum_generic
  obtain ⟨ms⟩ := MemberSeedExists.nonempty_memberSeed_of_member
    ((catRegrowth hd.point).frame.member y₀) (by norm_num)
  exact ⟨y₀, ε, hd, hG, ms, exists_link_with_receipt _ _⟩

end Facet

end DraismaVargas.Count.LinkReceiptExport
