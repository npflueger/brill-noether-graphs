module

public import DraismaVargas.LocalCases.W2M1kLimitColumns
public import DraismaVargas.LocalCases.W2M1kStableIncidence
public import DraismaVargas.LocalCases.W2M1kLeafStableGraph
public import DraismaVargas.LocalCases.SheetRelabelIncidence

@[expose] public section

/-!
# Figure 33 as a `BalancedGlobal.GaugeFamily`, in both orientations

Source: Draisma--Vargas Part I, case `{w2-r2-nd3-M-1k}`, Figure 33 and
**Equation (7)**, with the factor of two in the second bracket of Equation (7)
explained in `W2M1kCommonBalance`.

`W2M1kLimitColumns` inhabits `W2M1kCommonBalance.LimitColumns` on the case's
actual input, so Equation (7) holds unconditionally.  What the wall-input
dispatcher `WallProgress.presentedProgressOfWallInputs` consumes is not that
receipt but a `BalancedGlobal.GaugeFamily` -- `WallProgress.WallInput.family`
is one -- and this file packages Figure 33 into one.  It is the M-1k analogue of
`W2MkkArbitraryExit` §7 and §11 for Figure 34, and every remark recorded there
applies here verbatim:

* `LimitMember` deliberately keeps only the outgoing datum, so the
  occurrence-level `BalancedGlobal.Candidate` that `GaugeFamily.candidate` wants
  has to be re-supplied alongside the receipt;
* every field is then `rfl`-level against the receipt
  (`alignedPresentation_matrix`, `separatedPresentation_matrix`), and **no
  hypothesis is added** beyond the ones `W2M1kLimitColumns.limitColumns` already
  carries;
* `presentation` is written with term-mode equations.  A tactic-mode
  `intro i; match i with …` does not refine the expected type per branch and the
  ensuing `isDefEq` on `LimitColumns.squareMatrix` does not terminate within the
  default heartbeat budget.

## One family per orientation, not one on `limitColumns`

`W2M1kLimitColumns.limitColumns` is a `dite` on the decidable
`pinSheet profile 0 = pinSheet profile 1`, so `(limitColumns …).member 0` does
**not** reduce to a named member and none of the `rfl`s below would hold on it.
As for M-kk in `W2MkkArbitraryExit`, the family is therefore built on each
orientation separately --
`W2M1kLimitColumns.alignedOrientation` and `…separatedOrientation` -- and
`W2M1kLimitColumns.limitColumns_eq_alignedOrientation` /
`…_eq_separatedOrientation` are the one-line bridges back to the `dite` for any
consumer that wants it.  No conversion of a `GaugeFamily` is needed: a
`BalancedGlobal.GaugeFamily 3 data wall` does not mention the receipt it was
built from, so the two families are already the same type.

Which orientation occurs is decided by the datum and by nothing else
(`W2M1kSourceCandidates.exists_leafPair_or_dividedData`,
`not_leafPair_and_dividedData`), so the pair of families below is exhaustive and
neither is vacuous.

## What is here

* §1 `initialLabelling`, `labelling_self`, `squareMatrix_self`,
  `squareMatrix_self_ne_zero`, `wallColumn_initialLabelling` -- one identified
  member's honest labelling read back at position `0`, the M-1k copies of
  `W2MkkArbitraryExit` §7.  These are generic in the receipt: no orientation,
  no dictionary and no case data enter, only `LimitMember.row` and
  `LimitColumns.columnEquiv`, both of which are receipt fields.
* §2 the aligned orientation's `base`, `candidate`, `presentation` and
  `alignedGaugeFamily`.
* §3 the same for the separated orientation.
* §4 the three stable-incidence dictionaries and the three source-genus
  receipts per orientation.  For the two positions over the incoming datum they
  are `W2M1kLeafStableGraph.leafEquivalence` / `W2M1kGraphData.dividedEquivalence`
  / `joinedEquivalence` with `W2M1kSourceCandidates.leaf_sourceGenus` /
  `divided_sourceGenus` / `joined_sourceGenus`; at the remote position the
  branch swap contributes `SheetRelabelIncidence.equivalence` and
  `SheetRelabelIncidence.sourceGenus_eq` and nothing else, so **no condition is
  carried**.

`WallProgress` is not imported: this is the gauge family for `w2M1k`, stated
where the members are.  The wall input, the `FullDimSupply` and the
`RoutedWall` are in `A04M1kWiring`.
-/

namespace DraismaVargas.LocalCases.W2M1kGaugeFamily

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open StableSourceMatrix
open ResolutionM11 ResolutionM1k GlobalM11Arbitrary
open FullDimensionalSource
open W2M1kSourceCandidates
open W2M1kRowDescent W2M1kLeafRowDescent
open W2M1kTransport
open W2M1kCommonBalance (LimitMember LimitColumns)
open W2M1kLimitColumns (alignedOrientation separatedOrientation localLeafMember
  localDividedMember joinedMember remoteDividedMember remoteLeafMember remoteDivided
  remoteLeaf limitColumns limitColumns_eq_alignedOrientation
  limitColumns_eq_separatedOrientation)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}
  {shape : Shape profile}

/-! ## §1  Reading a receipt in the identified member's own coordinates

One identified member's honest labelling fixes the common square coordinate
order, and transport to the receipt's position `0` and back is the identity on
it.  No stable-incidence dictionary enters:
`W2M1kCommonBalance.LimitColumns.labelling` builds each member's row map out of
`LimitMember.row`, which is part of the receipt, so the cancellation is between
the receipt's own row bijections. -/

section OriginalCoordinates

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- A stable length-matrix labelling is its two equivalences. -/
private theorem labelling_eq_of_fields {datum : GluingDatum target degree}
    {first second : StableLengthMatrixLabelling datum coordinate}
    (hTarget : first.targetEdge = second.targetEdge) (hRow : first.row = second.row) :
    first = second := by
  cases first
  cases second
  cases hTarget
  cases hRow
  rfl

/-- One identified member's honest labelling, read back at position `0`: the
only source of the common square coordinate order. -/
noncomputable def initialLabelling (limit : LimitColumns profile shape) (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation (limit.member incoming).datum coordinate) :
    StableLengthMatrixLabelling (limit.member 0).datum coordinate where
  row := ((limit.member 0).row).symm.trans
    (((limit.member incoming).row).trans incomingFD.labelling.row)
  targetEdge := incomingFD.labelling.targetEdge.trans
    ((limit.columnEquiv incoming).symm.trans (limit.columnEquiv 0))

/-- **Transport to position `0` and back is the identity.**  Both the row
bijection and the occurrence dictionary cancel. -/
theorem labelling_self (limit : LimitColumns profile shape) (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation (limit.member incoming).datum coordinate) :
    limit.labelling (initialLabelling limit incoming incomingFD) incoming =
      incomingFD.labelling := by
  refine labelling_eq_of_fields ?_ ?_
  · ext column
    simp [LimitColumns.labelling, LimitColumns.targetCoordinates, initialLabelling]
  · ext path
    simp [LimitColumns.labelling, LimitColumns.sourceCoordinates, initialLabelling]

/-- Hence the identified member's own honest square matrix is its own. -/
theorem squareMatrix_self (limit : LimitColumns profile shape) (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation (limit.member incoming).datum coordinate) :
    limit.squareMatrix (initialLabelling limit incoming incomingFD) incoming =
      GluingDatum.LengthMatrixPresentation.matrix incomingFD.labelling.presentation := by
  unfold LimitColumns.squareMatrix
  rw [labelling_self limit incoming incomingFD]

/-- And it is nonsingular, because the identified member is full-dimensional. -/
theorem squareMatrix_self_ne_zero (limit : LimitColumns profile shape) (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation (limit.member incoming).datum coordinate) :
    (limit.squareMatrix (initialLabelling limit incoming incomingFD) incoming).det ≠ 0 := by
  rw [squareMatrix_self limit incoming incomingFD]
  exact incomingFD.det_ne_zero

/-- **The common wall coordinate is the identified member's own wall column.** -/
theorem wallColumn_initialLabelling (limit : LimitColumns profile shape) (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation (limit.member incoming).datum coordinate) :
    limit.wallColumn (initialLabelling limit incoming incomingFD) =
      incomingFD.labelling.targetEdge.symm
        (occurrenceEquiv target wall (limit.member incoming).right none) := by
  simp [LimitColumns.wallColumn, LimitColumns.targetCoordinates, initialLabelling,
    LimitColumns.columnEquiv]

end OriginalCoordinates

/-! ## §2  Base I.a: the aligned orientation as a gauge family -/

section Aligned

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- Base I.a's three base data: the incoming datum, the branch-swapped copy,
the incoming datum.  Position `1` is the remote one. -/
noncomputable def alignedBase (pair : LeafPair profile) : Fin 3 → GluingDatum target degree
  | 0 => data
  | 1 => (swapRelabeling profile pair.second pair.rel_second).apply
  | 2 => data

/-- Its three candidates, each over its own base. -/
noncomputable def alignedCandidate (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (hTargetConnected : graph_connected target)
    (hGenus : genus target = 0) :
    ∀ i : Fin 3, BalancedGlobal.Candidate target degree (alignedBase pair i) wall
  | 0 => LeafPair.candidate input shape pair
  | 1 => DividedData.candidate (swapShape shape input.valid.1 pair.second pair.rel_second)
      (remoteDivided input shape pair hTargetConnected hGenus)
  | 2 => joinedCandidate star (pair.geometry shape)

/-- The receipt's own honest presentations, typed at those candidates. -/
noncomputable def alignedPresentation (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (hTargetConnected : graph_connected target)
    (hGenus : genus target = 0)
    (initial : StableLengthMatrixLabelling
      ((alignedOrientation input shape pair hTargetConnected hGenus).member 0).datum
      coordinate) :
    ∀ i : Fin 3,
      (alignedCandidate input shape pair hTargetConnected hGenus i).datum.LengthMatrixPresentation
        coordinate
  | 0 => ((alignedOrientation input shape pair hTargetConnected hGenus).labelling initial
      0).presentation
  | 1 => ((alignedOrientation input shape pair hTargetConnected hGenus).labelling initial
      1).presentation
  | 2 => ((alignedOrientation input shape pair hTargetConnected hGenus).labelling initial
      2).presentation

omit [Fintype coordinate] in
theorem alignedPresentation_matrix (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (hTargetConnected : graph_connected target)
    (hGenus : genus target = 0)
    (initial : StableLengthMatrixLabelling
      ((alignedOrientation input shape pair hTargetConnected hGenus).member 0).datum
      coordinate) (i : Fin 3) :
    GluingDatum.LengthMatrixPresentation.matrix
        (alignedPresentation input shape pair hTargetConnected hGenus initial i) =
      (alignedOrientation input shape pair hTargetConnected hGenus).squareMatrix initial i := by
  fin_cases i <;> rfl

/-- **Figure 33 as a gauge family, Base I.a orientation.**  The weights are
Equation (7)'s `1`, `2(k-1)`, `2(k+1)` -- the members' own new-edge block
cardinalities, doubled at the two positions whose boxes are not already doubled
-- the balance is `W2M1kCommonBalance.LimitColumns.positiveBalance`, and the
off-wall agreement is the retained-column receipt. -/
noncomputable def alignedGaugeFamily (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (hTargetConnected : graph_connected target)
    (hGenus : genus target = 0)
    (initial : StableLengthMatrixLabelling
      ((alignedOrientation input shape pair hTargetConnected hGenus).member 0).datum
      coordinate) :
    BalancedGlobal.GaugeFamily (coordinate := coordinate) 3 data wall where
  base := alignedBase pair
  valid_of_old := fun i hValid ↦ by
    match i with
    | 0 => exact hValid
    | 1 => exact (swapRelabeling profile pair.second pair.rel_second).valid hValid
    | 2 => exact hValid
  candidate := alignedCandidate input shape pair hTargetConnected hGenus
  presentation := alignedPresentation input shape pair hTargetConnected hGenus initial
  wallColumn := (alignedOrientation input shape pair hTargetConnected hGenus).wallColumn initial
  weight := ![1, 2 * ((shape.k : ℚ) - 1), 2 * ((shape.k : ℚ) + 1)]
  positiveBalance := by
    have h := (alignedOrientation input shape pair hTargetConnected hGenus).positiveBalance
      input initial
    exact ⟨h.1, by simpa only [alignedPresentation_matrix] using h.2⟩
  agreeOffWall := fun first second ↦ by
    rw [alignedPresentation_matrix, alignedPresentation_matrix]
    exact (alignedOrientation input shape pair hTargetConnected hGenus).matrices_agree initial
      first second

@[simp] theorem alignedGaugeFamily_wallColumn (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0)
    (initial : StableLengthMatrixLabelling
      ((alignedOrientation input shape pair hTargetConnected hGenus).member 0).datum
      coordinate) :
    (alignedGaugeFamily input shape pair hTargetConnected hGenus initial).wallColumn =
      (alignedOrientation input shape pair hTargetConnected hGenus).wallColumn initial := rfl

end Aligned

/-! ## §3  Base II.2.2.M: the separated orientation as a gauge family -/

section Separated

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- Base II.2.2.M's three base data: the branch-swapped copy, the incoming
datum, the incoming datum.  Here it is position `0` that is remote. -/
noncomputable def separatedBase (profile : W2R2SourceProfile.SourceProfile data star block) :
    Fin 3 → GluingDatum target degree
  | 0 => (swapRelabeling profile (pinSheet profile 1)
      (W2SourceTransport.alignedTogether profile)).apply
  | 1 => data
  | 2 => data

/-- Its three candidates, each over its own base. -/
noncomputable def separatedCandidate (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (hTargetConnected : graph_connected target)
    (hGenus : genus target = 0) :
    ∀ i : Fin 3, BalancedGlobal.Candidate target degree (separatedBase profile i) wall
  | 0 => LeafPair.candidate
      (swapInput input (pinSheet profile 1) (W2SourceTransport.alignedTogether profile))
      (swapShape shape input.valid.1 (pinSheet profile 1)
        (W2SourceTransport.alignedTogether profile))
      (remoteLeaf input shape hTargetConnected hGenus)
  | 1 => DividedData.candidate shape divided
  | 2 => joinedCandidate star (divided.geometry shape)

/-- The receipt's own honest presentations, typed at those candidates. -/
noncomputable def separatedPresentation (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (hTargetConnected : graph_connected target)
    (hGenus : genus target = 0)
    (initial : StableLengthMatrixLabelling
      ((separatedOrientation input shape divided hTargetConnected hGenus).member 0).datum
      coordinate) :
    ∀ i : Fin 3,
      (separatedCandidate input shape divided hTargetConnected
        hGenus i).datum.LengthMatrixPresentation coordinate
  | 0 => ((separatedOrientation input shape divided hTargetConnected hGenus).labelling initial
      0).presentation
  | 1 => ((separatedOrientation input shape divided hTargetConnected hGenus).labelling initial
      1).presentation
  | 2 => ((separatedOrientation input shape divided hTargetConnected hGenus).labelling initial
      2).presentation

omit [Fintype coordinate] in
theorem separatedPresentation_matrix (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (hTargetConnected : graph_connected target)
    (hGenus : genus target = 0)
    (initial : StableLengthMatrixLabelling
      ((separatedOrientation input shape divided hTargetConnected hGenus).member 0).datum
      coordinate) (i : Fin 3) :
    GluingDatum.LengthMatrixPresentation.matrix
        (separatedPresentation input shape divided hTargetConnected hGenus initial i) =
      (separatedOrientation input shape divided hTargetConnected hGenus).squareMatrix initial
        i := by
  fin_cases i <;> rfl

/-- **Figure 33 as a gauge family, Base II.2.2.M orientation.** -/
noncomputable def separatedGaugeFamily (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (hTargetConnected : graph_connected target)
    (hGenus : genus target = 0)
    (initial : StableLengthMatrixLabelling
      ((separatedOrientation input shape divided hTargetConnected hGenus).member 0).datum
      coordinate) :
    BalancedGlobal.GaugeFamily (coordinate := coordinate) 3 data wall where
  base := separatedBase profile
  valid_of_old := fun i hValid ↦ by
    match i with
    | 0 => exact (swapRelabeling profile (pinSheet profile 1)
             (W2SourceTransport.alignedTogether profile)).valid hValid
    | 1 => exact hValid
    | 2 => exact hValid
  candidate := separatedCandidate input shape divided hTargetConnected hGenus
  presentation := separatedPresentation input shape divided hTargetConnected hGenus initial
  wallColumn := (separatedOrientation input shape divided hTargetConnected hGenus).wallColumn
    initial
  weight := ![1, 2 * ((shape.k : ℚ) - 1), 2 * ((shape.k : ℚ) + 1)]
  positiveBalance := by
    have h := (separatedOrientation input shape divided hTargetConnected hGenus).positiveBalance
      input initial
    exact ⟨h.1, by simpa only [separatedPresentation_matrix] using h.2⟩
  agreeOffWall := fun first second ↦ by
    rw [separatedPresentation_matrix, separatedPresentation_matrix]
    exact (separatedOrientation input shape divided hTargetConnected hGenus).matrices_agree
      initial first second

@[simp] theorem separatedGaugeFamily_wallColumn (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0)
    (initial : StableLengthMatrixLabelling
      ((separatedOrientation input shape divided hTargetConnected hGenus).member 0).datum
      coordinate) :
    (separatedGaugeFamily input shape divided hTargetConnected hGenus initial).wallColumn =
      (separatedOrientation input shape divided hTargetConnected hGenus).wallColumn
        initial := rfl

end Separated


/-! ## §4  The three dictionaries and the three source-genus receipts

`W2M1kStableIncidence.presentationAtOfDictionaries` consumes, at each position,
a `StableGraphIncidence.Equivalence` against the **incoming** stable graph and a
source-genus receipt.  For the two positions over the incoming datum both are
already theorems; at the remote position the branch swap contributes
`SheetRelabelIncidence.equivalence` and `SheetRelabelIncidence.sourceGenus_eq`
and nothing else, so neither family below carries a condition.  This is the
M-1k form of what `W2MkkArbitraryExit.firstOrientationDictionary` /
`firstOrientationSourceGenus` do for Figure 34, with the difference that here
the leaf dictionary (`W2M1kLeafStableGraph.leafEquivalence`) rather than a
second divided one occupies a position. -/

section Dictionaries

/-- The three Base I.a dictionaries against the incoming stable graph, the
remote one included. -/
noncomputable def alignedDictionary (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (hTargetConnected : graph_connected target)
    (hGenus : genus target = 0) :
    ∀ position : Fin 3, StableGraphIncidence.Equivalence data
      ((alignedOrientation input shape pair hTargetConnected hGenus).member position).datum
  | 0 => W2M1kLeafStableGraph.leafEquivalence input shape pair
  | 1 => (SheetRelabelIncidence.equivalence
      (swapRelabeling profile pair.second pair.rel_second) input.valid.1).trans
      (W2M1kGraphData.dividedEquivalence (swapInput input pair.second pair.rel_second)
        (swapShape shape input.valid.1 pair.second pair.rel_second)
        (remoteDivided input shape pair hTargetConnected hGenus))
  | 2 => W2M1kGraphData.joinedEquivalence input shape (pair.geometry shape)

/-- and the three Base I.a source-genus receipts. -/
theorem alignedMemberGenus (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (hTargetConnected : graph_connected target)
    (hGenus : genus target = 0) :
    ∀ position : Fin 3,
      genus ((alignedOrientation input shape pair hTargetConnected
        hGenus).member position).datum.sourceGraph = genus data.sourceGraph
  | 0 => leaf_sourceGenus input shape pair
  | 1 => (divided_sourceGenus (swapShape shape input.valid.1 pair.second pair.rel_second)
      (remoteDivided input shape pair hTargetConnected hGenus)).trans
      (SheetRelabelIncidence.sourceGenus_eq
        (swapRelabeling profile pair.second pair.rel_second))
  | 2 => joined_sourceGenus (pair.geometry shape)

/-- The three Base II.2.2.M dictionaries against the incoming stable graph; here
it is position `0` that is remote. -/
noncomputable def separatedDictionary (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (hTargetConnected : graph_connected target)
    (hGenus : genus target = 0) :
    ∀ position : Fin 3, StableGraphIncidence.Equivalence data
      ((separatedOrientation input shape divided hTargetConnected hGenus).member position).datum
  | 0 => (SheetRelabelIncidence.equivalence
      (swapRelabeling profile (pinSheet profile 1)
        (W2SourceTransport.alignedTogether profile)) input.valid.1).trans
      (W2M1kLeafStableGraph.leafEquivalence
        (swapInput input (pinSheet profile 1) (W2SourceTransport.alignedTogether profile))
        (swapShape shape input.valid.1 (pinSheet profile 1)
          (W2SourceTransport.alignedTogether profile))
        (remoteLeaf input shape hTargetConnected hGenus))
  | 1 => W2M1kGraphData.dividedEquivalence input shape divided
  | 2 => W2M1kGraphData.joinedEquivalence input shape (divided.geometry shape)

/-- and the three Base II.2.2.M source-genus receipts. -/
theorem separatedMemberGenus (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (hTargetConnected : graph_connected target)
    (hGenus : genus target = 0) :
    ∀ position : Fin 3,
      genus ((separatedOrientation input shape divided hTargetConnected
        hGenus).member position).datum.sourceGraph = genus data.sourceGraph
  | 0 => (leaf_sourceGenus
      (swapInput input (pinSheet profile 1) (W2SourceTransport.alignedTogether profile))
      (swapShape shape input.valid.1 (pinSheet profile 1)
        (W2SourceTransport.alignedTogether profile))
      (remoteLeaf input shape hTargetConnected hGenus)).trans
      (SheetRelabelIncidence.sourceGenus_eq
        (swapRelabeling profile (pinSheet profile 1)
          (W2SourceTransport.alignedTogether profile)))
  | 1 => divided_sourceGenus shape divided
  | 2 => joined_sourceGenus (divided.geometry shape)

end Dictionaries

end DraismaVargas.LocalCases.W2M1kGaugeFamily
