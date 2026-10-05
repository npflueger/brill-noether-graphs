module

public import DraismaVargas.LocalCases.A04MoreTags
public import DraismaVargas.LocalCases.W2M1kGaugeFamily

@[expose] public section

/-!
# The routed wall for `w2M1k`: wall input and full-dimensional supply

Source: Draisma--Vargas Part I, case `{w2-r2-nd3-M-1k}`, Figure 33 and
Equation (7), with the factor of two in the second bracket of Equation (7)
explained in `W2M1kCommonBalance`.

`A04MoreTags` bundles what one wall has to supply as `RoutedWall` -- a
`WallProgress.WallInput` for the dispatcher
`WallProgress.presentedProgressOfWallInputs`, an `A04FourTags.FullDimSupply` on
it, duplicate-free rows, and the state--classifier triple -- and inhabits it for
seven of the ten tags.  `w2M1k` is one of the three it leaves out, because a
`BalancedGlobal.Family` does not suffice there: what is needed is the gauge
form.  `W2M1kGaugeFamily` supplies the gauge form; this file is the wiring, in
exactly the shape §3 of `A04MoreTags` uses for `w2Mkk`.

| orientation | wall input | supply | carried |
|---|---|---|---|
| Base I.a (`p₀ = p₁`) | `ofW2M1kAligned` (`WallInput.ofGauge` on `W2M1kGaugeFamily.alignedGaugeFamily`) | `m1kAlignedSupply` | `hChart` |
| Base II.2.2.M (`p₀ ≠ p₁`) | `ofW2M1kSeparated` (`ofGauge` on `separatedGaugeFamily`) | `m1kSeparatedSupply` | `hChart` |

`hChart` is the **state--classifier equation** and nothing else: that the chart
the march currently occupies is the identified incoming member's own honest
length matrix.  It is one named hypothesis, never more, because it is not
local-case data.

## Why two entries and not one

`W2M1kLimitColumns.limitColumns` is a `dite` on `pinSheet profile 0 = pinSheet
profile 1`, and every `rfl` in `W2M1kGaugeFamily` is against a named orientation,
not against the `dite`.  So, exactly as `A04MoreTags` does for `w2Mkk`'s two
bases, there is one entry per orientation.  The two are exhaustive and mutually
exclusive over any one datum
(`W2M1kSourceCandidates.exists_leafPair_or_dividedData`,
`not_leafPair_and_dividedData`), and
`W2M1kLimitColumns.limitColumns_eq_alignedOrientation` /
`…_eq_separatedOrientation` are the bridges back to the `dite` for a consumer
that prefers to quantify over `limitColumns`.

## What is *not* carried

1. **Duplicate-free rows** (the `nodup` field of `RoutedWall`) --
   `A04MoreTags.nodup_labelling_path`, because both families present their
   members by `StableLengthMatrixLabelling.presentation`.
2. **The remote dictionary and its genus receipt** --
   `W2M1kGaugeFamily.alignedDictionary` / `alignedMemberGenus` and their
   separated twins discharge all three positions from
   `SheetRelabelIncidence.equivalence`, `SheetRelabelIncidence.sourceGenus_eq`
   and the case's own three dictionaries, so `m1kAlignedSupply` and
   `m1kSeparatedSupply` take no dictionary argument.
3. **The incoming determinant** -- `W2M1kGaugeFamily.squareMatrix_self` makes the
   identified member's own honest square matrix literally its own, so the
   `incomingNonzero` field is `incomingFD.det_ne_zero` and the `incomingMatrix`
   field is `hChart` transported.

## What *is* carried

`hChart`, and `hwallColumn` -- that the family's regrown column is the coordinate
the march crosses.  `m1kAlignedFamily_wallColumn` and
`m1kSeparatedFamily_wallColumn` say what that column is (the identified member's
own wall occurrence).  The incoming position itself, its full-dimensional
presentation and the clause pinning `hwallColumn` to the original contracted
column belong to the identification of the incoming `w2M1k` datum
(`W2M1kIncomingCensus`, `W2M1kIncomingMatching`), not to this file; `incoming`
and `incomingFD` are parameters here for exactly that reason.
-/

namespace DraismaVargas.LocalCases.A04M1kWiring

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.ClassifiedContinuation
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.SecondEquation
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.WallProgress
open DraismaVargas.LocalCases.W2M1kSourceCandidates
open DraismaVargas.LocalCases.A04FourTags (FullDimSupply)
open DraismaVargas.LocalCases.A04MoreTags (RoutedWall nodup_labelling_path)

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {degree : ℕ} {wall : coordinate}

/-! ## 1.  Base I.a, the aligned orientation -/

section Aligned

variable {target : CFGraph.{0}} {wallVertex : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wallVertex}
  {block : WallBlock data wallVertex}
  {profile : W2R2SourceProfile.SourceProfile data star block}
  (input : W2SourceInput data star) (shape : Shape profile)
  (pair : LeafPair profile)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (incoming : Fin 3)
  (incomingFD : FullDimensionalSourcePresentation
    ((W2M1kLimitColumns.alignedOrientation input shape pair hConnected
      hGenus).member incoming).datum coordinate)

/-- Figure 33's honest family in the identified member's own square
coordinates, Base I.a. -/
noncomputable def m1kAlignedFamily :
    GaugeFamily (coordinate := coordinate) 3 data wallVertex :=
  W2M1kGaugeFamily.alignedGaugeFamily input shape pair hConnected hGenus
    (W2M1kGaugeFamily.initialLabelling
      (W2M1kLimitColumns.alignedOrientation input shape pair hConnected hGenus)
      incoming incomingFD)

/-- **Figure 33's wall input, Base I.a.**  Gauge-mixed: position `1` lives over
the branch-swapped copy, which is exactly what `WallInput.ofGauge` exists
for. -/
noncomputable def ofW2M1kAligned
    (hwallColumn :
      (m1kAlignedFamily input shape pair hConnected hGenus incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    WallInput degree coordinate wall :=
  WallInput.ofGauge (m1kAlignedFamily input shape pair hConnected hGenus incoming incomingFD)
    input.valid SourceCase.w2M1k rfl hwallColumn hConnected hGenus root

@[simp] theorem ofW2M1kAligned_case
    (hwallColumn :
      (m1kAlignedFamily input shape pair hConnected hGenus incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    (ofW2M1kAligned (wall := wall) input shape pair hConnected hGenus incoming incomingFD
      hwallColumn root).case = SourceCase.w2M1k := rfl

/-- Figure 33's three outgoing presentations in the Base I.a orientation, one
`W2M1kStableIncidence.presentationAtOfDictionaries` per member. -/
noncomputable def alignedFullDim
    (dictionary : ∀ position : Fin 3, StableGraphIncidence.Equivalence data
      ((W2M1kLimitColumns.alignedOrientation input shape pair hConnected
        hGenus).member position).datum)
    (memberGenus : ∀ position : Fin 3,
      genus ((W2M1kLimitColumns.alignedOrientation input shape pair hConnected
        hGenus).member position).datum.sourceGraph = genus data.sourceGraph) :
    ∀ outgoing : Fin 3,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((m1kAlignedFamily input shape pair hConnected hGenus incoming
          incomingFD).presentation outgoing)).det ≠ 0 →
      FullDimensionalSourcePresentation
        ((m1kAlignedFamily input shape pair hConnected hGenus incoming
          incomingFD).candidate outgoing).datum coordinate
  | 0 => fun hdet ↦ W2M1kStableIncidence.presentationAtOfDictionaries
      (W2M1kLimitColumns.alignedOrientation input shape pair hConnected hGenus) incoming 0
      (dictionary incoming) (dictionary 0) input.valid hConnected hGenus
      (memberGenus incoming) (memberGenus 0)
      (W2M1kGaugeFamily.initialLabelling _ incoming incomingFD) incomingFD hdet
  | 1 => fun hdet ↦ W2M1kStableIncidence.presentationAtOfDictionaries
      (W2M1kLimitColumns.alignedOrientation input shape pair hConnected hGenus) incoming 1
      (dictionary incoming) (dictionary 1) input.valid hConnected hGenus
      (memberGenus incoming) (memberGenus 1)
      (W2M1kGaugeFamily.initialLabelling _ incoming incomingFD) incomingFD hdet
  | 2 => fun hdet ↦ W2M1kStableIncidence.presentationAtOfDictionaries
      (W2M1kLimitColumns.alignedOrientation input shape pair hConnected hGenus) incoming 2
      (dictionary incoming) (dictionary 2) input.valid hConnected hGenus
      (memberGenus incoming) (memberGenus 2)
      (W2M1kGaugeFamily.initialLabelling _ incoming incomingFD) incomingFD hdet

/-- **The full-dimensional supply for `w2M1k`, Base I.a, against a supplied
dictionary family.** -/
noncomputable def w2M1kAlignedSupply
    (dictionary : ∀ position : Fin 3, StableGraphIncidence.Equivalence data
      ((W2M1kLimitColumns.alignedOrientation input shape pair hConnected
        hGenus).member position).datum)
    (memberGenus : ∀ position : Fin 3,
      genus ((W2M1kLimitColumns.alignedOrientation input shape pair hConnected
        hGenus).member position).datum.sourceGraph = genus data.sourceGraph)
    (hwallColumn :
      (m1kAlignedFamily input shape pair hConnected hGenus incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    FullDimSupply (ofW2M1kAligned (wall := wall) input shape pair hConnected hGenus incoming
      incomingFD hwallColumn root) where
  fullDim := alignedFullDim input shape pair hConnected hGenus incoming incomingFD dictionary
    memberGenus
  presentation_eq := by
    intro outgoing hdet
    fin_cases outgoing <;> rfl

/-- **The full-dimensional supply for `w2M1k`, Base I.a, with nothing
carried.**  The three dictionaries
and the three source-genus receipts are `W2M1kGaugeFamily` §4. -/
noncomputable def m1kAlignedSupply
    (hwallColumn :
      (m1kAlignedFamily input shape pair hConnected hGenus incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    FullDimSupply (ofW2M1kAligned (wall := wall) input shape pair hConnected hGenus incoming
      incomingFD hwallColumn root) :=
  w2M1kAlignedSupply input shape pair hConnected hGenus incoming incomingFD
    (W2M1kGaugeFamily.alignedDictionary input shape pair hConnected hGenus)
    (W2M1kGaugeFamily.alignedMemberGenus input shape pair hConnected hGenus)
    hwallColumn root

/-! ### The incoming side -/

/-- The family's presented matrices are the orientation's own square matrices. -/
theorem ofW2M1kAligned_presentation_matrix
    (hwallColumn :
      (m1kAlignedFamily input shape pair hConnected hGenus incoming incomingFD).wallColumn = wall)
    (root : target.V) (i : Fin 3) :
    GluingDatum.LengthMatrixPresentation.matrix
        ((ofW2M1kAligned (wall := wall) input shape pair hConnected hGenus incoming incomingFD
          hwallColumn root).family.presentation i) =
      (W2M1kLimitColumns.alignedOrientation input shape pair hConnected hGenus).squareMatrix
        (W2M1kGaugeFamily.initialLabelling
          (W2M1kLimitColumns.alignedOrientation input shape pair hConnected hGenus)
          incoming incomingFD) i :=
  W2M1kGaugeFamily.alignedPresentation_matrix input shape pair hConnected hGenus
    (W2M1kGaugeFamily.initialLabelling
      (W2M1kLimitColumns.alignedOrientation input shape pair hConnected hGenus)
      incoming incomingFD) i

/-- **The `incomingNonzero` field for `w2M1k`, Base I.a.** -/
theorem ofW2M1kAligned_incomingNonzero
    (hwallColumn :
      (m1kAlignedFamily input shape pair hConnected hGenus incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    (GluingDatum.LengthMatrixPresentation.matrix
      ((ofW2M1kAligned (wall := wall) input shape pair hConnected hGenus incoming incomingFD
        hwallColumn root).family.presentation incoming)).det ≠ 0 := by
  rw [ofW2M1kAligned_presentation_matrix input shape pair hConnected hGenus incoming incomingFD
    hwallColumn root]
  exact W2M1kGaugeFamily.squareMatrix_self_ne_zero _ incoming incomingFD

/-- **The `incomingMatrix` field for `w2M1k`, Base I.a, modulo the
state--classifier equation.** -/
theorem ofW2M1kAligned_incomingMatrix
    (hwallColumn :
      (m1kAlignedFamily input shape pair hConnected hGenus incoming incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart) :
    GluingDatum.LengthMatrixPresentation.matrix
        ((ofW2M1kAligned (wall := wall) input shape pair hConnected hGenus incoming incomingFD
          hwallColumn root).family.presentation incoming) = chart := by
  rw [ofW2M1kAligned_presentation_matrix input shape pair hConnected hGenus incoming incomingFD
    hwallColumn root, W2M1kGaugeFamily.squareMatrix_self]
  exact hChart

/-- **Duplicate-free rows for `w2M1k`, Base I.a.** -/
theorem ofW2M1kAligned_nodup
    (hwallColumn :
      (m1kAlignedFamily input shape pair hConnected hGenus incoming incomingFD).wallColumn = wall)
    (root : target.V) (i : Fin 3) (row : coordinate) :
    (((ofW2M1kAligned (wall := wall) input shape pair hConnected hGenus incoming incomingFD
      hwallColumn root).family.presentation i).path row).Nodup := by
  fin_cases i <;> exact nodup_labelling_path _ row

/-- The Base I.a family is honestly presented. -/
theorem ofW2M1kAligned_honestlyPresented
    (hwallColumn :
      (m1kAlignedFamily input shape pair hConnected hGenus incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    RoutedWall.HonestlyPresented (ofW2M1kAligned (wall := wall) input shape pair hConnected
      hGenus incoming incomingFD hwallColumn root) := by
  intro i
  fin_cases i <;> exact ⟨_, rfl⟩

/-- **`w2M1k` as a routed wall, Base I.a.**  Nothing is carried but `hChart`. -/
noncomputable def routedW2M1kAligned
    (hwallColumn :
      (m1kAlignedFamily input shape pair hConnected hGenus incoming incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart) :
    RoutedWall degree coordinate chart wall :=
  RoutedWall.ofHonestSupply
    (ofW2M1kAligned (wall := wall) input shape pair hConnected hGenus incoming incomingFD
      hwallColumn root)
    (m1kAlignedSupply input shape pair hConnected hGenus incoming incomingFD hwallColumn root)
    (ofW2M1kAligned_honestlyPresented input shape pair hConnected hGenus incoming incomingFD
      hwallColumn root)
    incoming
    (ofW2M1kAligned_incomingNonzero input shape pair hConnected hGenus incoming incomingFD
      hwallColumn root)
    (ofW2M1kAligned_incomingMatrix input shape pair hConnected hGenus incoming incomingFD
      hwallColumn root chart hChart)

/-- The Base I.a family's regrown column, read on the identified member's own
occurrence dictionary. -/
theorem m1kAlignedFamily_wallColumn :
    (m1kAlignedFamily input shape pair hConnected hGenus incoming incomingFD).wallColumn =
      incomingFD.labelling.targetEdge.symm
        (occurrenceEquiv target wallVertex
          ((W2M1kLimitColumns.alignedOrientation input shape pair hConnected
            hGenus).member incoming).right none) :=
  W2M1kGaugeFamily.wallColumn_initialLabelling _ incoming incomingFD

end Aligned

/-! ## 2.  Base II.2.2.M, the separated orientation -/

section Separated

variable {target : CFGraph.{0}} {wallVertex : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wallVertex}
  {block : WallBlock data wallVertex}
  {profile : W2R2SourceProfile.SourceProfile data star block}
  (input : W2SourceInput data star) (shape : Shape profile)
  (divided : DividedData profile)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (incoming : Fin 3)
  (incomingFD : FullDimensionalSourcePresentation
    ((W2M1kLimitColumns.separatedOrientation input shape divided hConnected
      hGenus).member incoming).datum coordinate)

/-- Figure 33's honest family in the identified member's own square
coordinates, Base II.2.2.M. -/
noncomputable def m1kSeparatedFamily :
    GaugeFamily (coordinate := coordinate) 3 data wallVertex :=
  W2M1kGaugeFamily.separatedGaugeFamily input shape divided hConnected hGenus
    (W2M1kGaugeFamily.initialLabelling
      (W2M1kLimitColumns.separatedOrientation input shape divided hConnected hGenus)
      incoming incomingFD)

/-- **Figure 33's wall input, Base II.2.2.M.**  Gauge-mixed: here it is position
`0` that lives over the branch-swapped copy. -/
noncomputable def ofW2M1kSeparated
    (hwallColumn : (m1kSeparatedFamily input shape divided hConnected hGenus incoming
      incomingFD).wallColumn = wall)
    (root : target.V) :
    WallInput degree coordinate wall :=
  WallInput.ofGauge (m1kSeparatedFamily input shape divided hConnected hGenus incoming
    incomingFD) input.valid SourceCase.w2M1k rfl hwallColumn hConnected hGenus root

@[simp] theorem ofW2M1kSeparated_case
    (hwallColumn : (m1kSeparatedFamily input shape divided hConnected hGenus incoming
      incomingFD).wallColumn = wall)
    (root : target.V) :
    (ofW2M1kSeparated (wall := wall) input shape divided hConnected hGenus incoming incomingFD
      hwallColumn root).case = SourceCase.w2M1k := rfl

/-- Figure 33's three outgoing presentations in the Base II.2.2.M
orientation. -/
noncomputable def separatedFullDim
    (dictionary : ∀ position : Fin 3, StableGraphIncidence.Equivalence data
      ((W2M1kLimitColumns.separatedOrientation input shape divided hConnected
        hGenus).member position).datum)
    (memberGenus : ∀ position : Fin 3,
      genus ((W2M1kLimitColumns.separatedOrientation input shape divided hConnected
        hGenus).member position).datum.sourceGraph = genus data.sourceGraph) :
    ∀ outgoing : Fin 3,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((m1kSeparatedFamily input shape divided hConnected hGenus incoming
          incomingFD).presentation outgoing)).det ≠ 0 →
      FullDimensionalSourcePresentation
        ((m1kSeparatedFamily input shape divided hConnected hGenus incoming
          incomingFD).candidate outgoing).datum coordinate
  | 0 => fun hdet ↦ W2M1kStableIncidence.presentationAtOfDictionaries
      (W2M1kLimitColumns.separatedOrientation input shape divided hConnected hGenus) incoming 0
      (dictionary incoming) (dictionary 0) input.valid hConnected hGenus
      (memberGenus incoming) (memberGenus 0)
      (W2M1kGaugeFamily.initialLabelling _ incoming incomingFD) incomingFD hdet
  | 1 => fun hdet ↦ W2M1kStableIncidence.presentationAtOfDictionaries
      (W2M1kLimitColumns.separatedOrientation input shape divided hConnected hGenus) incoming 1
      (dictionary incoming) (dictionary 1) input.valid hConnected hGenus
      (memberGenus incoming) (memberGenus 1)
      (W2M1kGaugeFamily.initialLabelling _ incoming incomingFD) incomingFD hdet
  | 2 => fun hdet ↦ W2M1kStableIncidence.presentationAtOfDictionaries
      (W2M1kLimitColumns.separatedOrientation input shape divided hConnected hGenus) incoming 2
      (dictionary incoming) (dictionary 2) input.valid hConnected hGenus
      (memberGenus incoming) (memberGenus 2)
      (W2M1kGaugeFamily.initialLabelling _ incoming incomingFD) incomingFD hdet

/-- **The full-dimensional supply for `w2M1k`, Base II.2.2.M, against a
supplied dictionary family.** -/
noncomputable def w2M1kSeparatedSupply
    (dictionary : ∀ position : Fin 3, StableGraphIncidence.Equivalence data
      ((W2M1kLimitColumns.separatedOrientation input shape divided hConnected
        hGenus).member position).datum)
    (memberGenus : ∀ position : Fin 3,
      genus ((W2M1kLimitColumns.separatedOrientation input shape divided hConnected
        hGenus).member position).datum.sourceGraph = genus data.sourceGraph)
    (hwallColumn : (m1kSeparatedFamily input shape divided hConnected hGenus incoming
      incomingFD).wallColumn = wall)
    (root : target.V) :
    FullDimSupply (ofW2M1kSeparated (wall := wall) input shape divided hConnected hGenus
      incoming incomingFD hwallColumn root) where
  fullDim := separatedFullDim input shape divided hConnected hGenus incoming incomingFD
    dictionary memberGenus
  presentation_eq := by
    intro outgoing hdet
    fin_cases outgoing <;> rfl

/-- **The full-dimensional supply for `w2M1k`, Base II.2.2.M, with nothing
carried.** -/
noncomputable def m1kSeparatedSupply
    (hwallColumn : (m1kSeparatedFamily input shape divided hConnected hGenus incoming
      incomingFD).wallColumn = wall)
    (root : target.V) :
    FullDimSupply (ofW2M1kSeparated (wall := wall) input shape divided hConnected hGenus
      incoming incomingFD hwallColumn root) :=
  w2M1kSeparatedSupply input shape divided hConnected hGenus incoming incomingFD
    (W2M1kGaugeFamily.separatedDictionary input shape divided hConnected hGenus)
    (W2M1kGaugeFamily.separatedMemberGenus input shape divided hConnected hGenus)
    hwallColumn root

/-! ### The incoming side -/

theorem ofW2M1kSeparated_presentation_matrix
    (hwallColumn : (m1kSeparatedFamily input shape divided hConnected hGenus incoming
      incomingFD).wallColumn = wall)
    (root : target.V) (i : Fin 3) :
    GluingDatum.LengthMatrixPresentation.matrix
        ((ofW2M1kSeparated (wall := wall) input shape divided hConnected hGenus incoming
          incomingFD hwallColumn root).family.presentation i) =
      (W2M1kLimitColumns.separatedOrientation input shape divided hConnected
        hGenus).squareMatrix
        (W2M1kGaugeFamily.initialLabelling
          (W2M1kLimitColumns.separatedOrientation input shape divided hConnected hGenus)
          incoming incomingFD) i :=
  W2M1kGaugeFamily.separatedPresentation_matrix input shape divided hConnected hGenus
    (W2M1kGaugeFamily.initialLabelling
      (W2M1kLimitColumns.separatedOrientation input shape divided hConnected hGenus)
      incoming incomingFD) i

/-- **The `incomingNonzero` field for `w2M1k`, Base II.2.2.M.** -/
theorem ofW2M1kSeparated_incomingNonzero
    (hwallColumn : (m1kSeparatedFamily input shape divided hConnected hGenus incoming
      incomingFD).wallColumn = wall)
    (root : target.V) :
    (GluingDatum.LengthMatrixPresentation.matrix
      ((ofW2M1kSeparated (wall := wall) input shape divided hConnected hGenus incoming
        incomingFD hwallColumn root).family.presentation incoming)).det ≠ 0 := by
  rw [ofW2M1kSeparated_presentation_matrix input shape divided hConnected hGenus incoming
    incomingFD hwallColumn root]
  exact W2M1kGaugeFamily.squareMatrix_self_ne_zero _ incoming incomingFD

/-- **The `incomingMatrix` field for `w2M1k`, Base II.2.2.M, modulo the
state--classifier equation.** -/
theorem ofW2M1kSeparated_incomingMatrix
    (hwallColumn : (m1kSeparatedFamily input shape divided hConnected hGenus incoming
      incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart) :
    GluingDatum.LengthMatrixPresentation.matrix
        ((ofW2M1kSeparated (wall := wall) input shape divided hConnected hGenus incoming
          incomingFD hwallColumn root).family.presentation incoming) = chart := by
  rw [ofW2M1kSeparated_presentation_matrix input shape divided hConnected hGenus incoming
    incomingFD hwallColumn root, W2M1kGaugeFamily.squareMatrix_self]
  exact hChart

/-- **Duplicate-free rows for `w2M1k`, Base II.2.2.M.** -/
theorem ofW2M1kSeparated_nodup
    (hwallColumn : (m1kSeparatedFamily input shape divided hConnected hGenus incoming
      incomingFD).wallColumn = wall)
    (root : target.V) (i : Fin 3) (row : coordinate) :
    (((ofW2M1kSeparated (wall := wall) input shape divided hConnected hGenus incoming
      incomingFD hwallColumn root).family.presentation i).path row).Nodup := by
  fin_cases i <;> exact nodup_labelling_path _ row

/-- The Base II.2.2.M family is honestly presented. -/
theorem ofW2M1kSeparated_honestlyPresented
    (hwallColumn : (m1kSeparatedFamily input shape divided hConnected hGenus incoming
      incomingFD).wallColumn = wall)
    (root : target.V) :
    RoutedWall.HonestlyPresented (ofW2M1kSeparated (wall := wall) input shape divided
      hConnected hGenus incoming incomingFD hwallColumn root) := by
  intro i
  fin_cases i <;> exact ⟨_, rfl⟩

/-- **`w2M1k` as a routed wall, Base II.2.2.M.**  Nothing is carried but
`hChart`. -/
noncomputable def routedW2M1kSeparated
    (hwallColumn : (m1kSeparatedFamily input shape divided hConnected hGenus incoming
      incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart) :
    RoutedWall degree coordinate chart wall :=
  RoutedWall.ofHonestSupply
    (ofW2M1kSeparated (wall := wall) input shape divided hConnected hGenus incoming incomingFD
      hwallColumn root)
    (m1kSeparatedSupply input shape divided hConnected hGenus incoming incomingFD hwallColumn
      root)
    (ofW2M1kSeparated_honestlyPresented input shape divided hConnected hGenus incoming
      incomingFD hwallColumn root)
    incoming
    (ofW2M1kSeparated_incomingNonzero input shape divided hConnected hGenus incoming incomingFD
      hwallColumn root)
    (ofW2M1kSeparated_incomingMatrix input shape divided hConnected hGenus incoming incomingFD
      hwallColumn root chart hChart)

/-- The Base II.2.2.M family's regrown column, read on the identified member's
own occurrence dictionary. -/
theorem m1kSeparatedFamily_wallColumn :
    (m1kSeparatedFamily input shape divided hConnected hGenus incoming incomingFD).wallColumn =
      incomingFD.labelling.targetEdge.symm
        (occurrenceEquiv target wallVertex
          ((W2M1kLimitColumns.separatedOrientation input shape divided hConnected
            hGenus).member incoming).right none) :=
  W2M1kGaugeFamily.wallColumn_initialLabelling _ incoming incomingFD

end Separated

end DraismaVargas.LocalCases.A04M1kWiring
