module

public import DraismaVargas.LocalCases.TrackedWallProgress
public import DraismaVargas.LocalCases.A04M1kWiring
public import DraismaVargas.LocalCases.W2M1kGraphTracking
public import DraismaVargas.LocalCases.W2MkkGraphTracking
public import DraismaVargas.LocalCases.W3TrackedExit

@[expose] public section

/-!
# The last three tags of the tracked march, and the all-tags dispatch

Source: Vargas, Part II, arXiv:2609.09109, Section 4.4 (the outer walk), read against
Draisma–Vargas Part I, arXiv:1909.12924, cases `{w2-r2-nd3-M-1k}` (Figure 33),
`{w2-r2-nd3-M-kk}` (Figure 34) and `{w3-r1-nd3-t2-(a=k₄)}` (Figure 28 and
Equation (2)).

`TrackedWallProgress` introduces `TrackedRoutedWall` -- an
`A04MoreTags.RoutedWall` together with one `InteriorGraphTracking.Tracks` at
each of its supply's gated full-dimensional presentations -- and its uniform
mechanism `TrackedRoutedWall.ofIncidence`, and inhabits it at seven of the ten
tags.  This file treats the remaining three and states the dispatch.

## What is proved here

* `trackedW2M1kAligned`, `trackedW2M1kSeparated` (Figure 33, both bases) and
  `trackedW2MkkFirst`, `trackedW2MkkSecond` (Figure 34, both bases).  The one
  input not already in the bundle -- `hDictionaryRow`, that the
  case's own three stable-incidence dictionaries read the limit receipt's own
  member rows -- is proved here beside each supply
  (`alignedDictionary_row`, `separatedDictionary_row`, `mkkFirstDictionary_row`,
  `mkkSecondDictionary_row`), position by position by `rfl`, because
  `SheetRelabelIncidence.equivalence` and
  `LimitChainCore.Gauge.ofSheetRelabeling` take their row maps from the same
  `SheetRelabelStable.stablePathEquiv`, the remote slot included.  With it,
  `W2M1kGraphTracking.labelling_row` and `W2MkkGraphTracking.labelling_row` are
  exactly the row formula `ofIncidence` consumes at `A04M1kWiring`'s and
  `A04MoreTags`' own supplies, and nothing else is carried.

* `routedW3FourHonest` and `trackedW3Four` (Figure 28).  This is the one tag
  that needed geometry rather than plumbing, and the geometry is Figure 28's
  branch-gauge row coherence: the four members' gauge copies are
  `StableGraphIncidence.sheetRelabel`s along the branch swap composed with the
  member-to-member equivalences of Figure 28, packaged as
  `W3FourRegrownColumnSeam.MemberCertificates` (`dictionary`, `memberGenus`,
  and the sixteen ordered `certificate i j`), and their row coherence with the
  four honest labellings is `W3TrackedAnchoring.RowsCompatible`, produced by
  `W3TrackedAnchoring.exists_tracked_anchoredCertificates_withExtra` through
  `rowsCompatible_of_natural`.  Equation (2)'s family is taken at the
  *identified member's own* labelling -- `W3FourHonestReceipts.gaugeFamily`,
  which is `W3FourHonestBalance.HonestFigure28.gaugeFamily` reordered and whose
  `presentation` at every member is that member's own honest labelling -- so
  the wall input, the supply, `hW25Nodup` and the incoming pair are all `rfl`
  or one rewrite, and `W3TrackedExit.outgoingLabelling_row` is the row formula
  at an *arbitrary* incoming full-dimensional cover, exactly as at the other
  nine tags.

* `figure28FullDim_row` and `trackedW3FourFixed`, the same tag against
  `A04MoreTags.routedW3Four` itself.  That routed wall presents Equation (2)
  at Figure 28's *fixed* order (the limit's own stable rows, columns
  `Option target.edges`), so its supply's `fullDim` at a member is
  `StableGraphFullDimensional.presentationOfEquivalence` along
  `certificate incoming outgoing` but lands on
  `A04MoreTags.figure28Labelling`, whose row map is
  `W3FourHonestBalance.honestLabelling`'s -- the incoming cover's own row map
  never enters it.  So one equation remains there and is carried by name:
  `hIncomingRow`, that the incoming cover is presented at the identified
  member's own honest rows.  `normalizedIncoming` and `normalizedIncoming_row`
  show it is not vacuous: the transported incoming presentation satisfies it by
  `rfl`.

* `TrackedClassified`, `trackedProgressOfTrackedClassification` and
  `exists_terminal_tracked_caterpillar_of_trackedClassification`: the tracked
  analogue of `A04MoreTags.presentedProgressOfRoutedClassification`, so that
  `TrackedWallProgress.trackedProgressOfRoutedWalls` has a producer at every
  classified wall, and
  `TrackedWallProgress.exists_terminal_tracked_caterpillar_of_routedWalls`
  composed with it.

## The producer at every tag

| tag | tracked constructor |
|---|---|
| `w4` | `TrackedWallProgress.trackedW4` |
| `w3Shift` | `TrackedWallProgress.trackedW3Shift` |
| `w3Nd2CoarseFine` | `TrackedWallProgress.trackedNd2` |
| `w3Nd3CoarseFine` | `TrackedWallProgress.trackedNd3` |
| `w2M11` | `TrackedWallProgress.trackedW2M11` |
| `w2P` | `TrackedWallProgress.trackedW2P` |
| `w2R1` | `TrackedWallProgress.trackedW2R1` |
| `w2M1k` Base I.a | `trackedW2M1kAligned` |
| `w2M1k` Base II.2.2.M | `trackedW2M1kSeparated` |
| `w2Mkk` Base II.2.1.M | `trackedW2MkkFirst` |
| `w2Mkk` Base II.2.2.M | `trackedW2MkkSecond` |
| `w3Four` | `trackedW3Four` (and `trackedW3FourFixed`) |

## What is NOT proved here

No family geometry, determinant balance, positive exit, census, incoming
identification or graph identification is re-derived; every producer is
consumed verbatim.  Matrix equality is never used to identify
a graph: every tracking travels along the actual member-to-member
`StableGraphIncidence.Equivalence` the full-dimensional package is transported
along, and the candidate and base stage of each member are the producers' own.

The hypotheses that remain explicit are, per tag, exactly the ones the
untracked `routed*` constructor already takes, plus one incoming `Tracks`; and
for `w3Four` additionally `W3TrackedAnchoring.RowsCompatible` at a stable path
labelling of the wall datum (`trackedW3FourFixed` also takes `hIncomingRow`).
`TrackedProgress` stays conditional exactly as in `TrackedWallProgress`: it needs
a `TrackedRoutedWall` at the crossed coordinate, which the interior
classification supplies (`InteriorProgress`, `InteriorBridgesAll`), and the
wall-level inputs of `IncomingSourceCases.exists_classification` (`hStable`,
`hCompat`, `hTrivalent`) are not treated in this file (they are discharged in
`InteriorProgress`).  `2 ≤ degree` remains explicit wherever a successor payload
is rebuilt.

Consumers: the outer walk of Part II, Section 4.4, through
`TrackedState.exists_terminal_reachable_of_tracked_progress` and
`TrackedPencil.exists_chain_to_core` at the terminal tracked state.
-/

namespace DraismaVargas.LocalCases.TrackedWallProgressMore

open Utilities
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.Infrastructure.RationalAffineWall
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.A04MoreTags
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.WallProgress
open DraismaVargas.LocalCases.TrackedWallProgress
open DraismaVargas.LocalCases.A04FourTags (FullDimSupply)
open DraismaVargas.LocalCases.ClassifiedContinuation (SourceCase)

/-! ## 1.  Figure 33, the `w2M1k` tag, in both bases -/

section M1k

open DraismaVargas.LocalCases.SecondEquation
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W2M1kSourceCandidates
open DraismaVargas.LocalCases.W2M1kLimitColumns (alignedOrientation separatedOrientation)

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {wall : coordinate} {graph : CubicDartGraph D V}
  {label : D → coordinate}
  {target : CFGraph.{0}} {wallVertex : target.V}
  {data : GluingDatum target degree}
  {star : TwoStar target wallVertex} {block : WallBlock data wallVertex}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-! ### Base I.a, the aligned orientation -/

section Aligned

variable (input : W2SourceInput data star) (shape : Shape profile) (pair : LeafPair profile)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (incoming : Fin 3)
  (incomingFD : FullDimensionalSourcePresentation
    ((alignedOrientation input shape pair hConnected hGenus).member incoming).datum coordinate)

/-- **`hDictionaryRow` for Base I.a.**  The three dictionaries
`A04M1kWiring.m1kAlignedSupply` uses read the limit receipt's own member rows.
The remote slot (position `1`) is `rfl` too, because
`SheetRelabelIncidence.equivalence` and `LimitChainCore.Gauge.ofSheetRelabeling`
take their row maps from the same `SheetRelabelStable.stablePathEquiv`. -/
theorem alignedDictionary_row (position : Fin 3) :
    (W2M1kGaugeFamily.alignedDictionary input shape pair hConnected hGenus position).row =
      ((alignedOrientation input shape pair hConnected hGenus).member position).row := by
  fin_cases position <;> rfl

/-- Figure 33's member-to-member incidence equivalences in Base I.a, read on the
routed wall's own gauge-family slots. -/
noncomputable def m1kAlignedBetween :
    ∀ outgoing : Fin 3,
      StableGraphIncidence.Equivalence
        ((alignedOrientation input shape pair hConnected hGenus).member incoming).datum
        ((A04M1kWiring.m1kAlignedFamily input shape pair hConnected hGenus incoming
          incomingFD).candidate outgoing).datum
  | 0 => (W2M1kGaugeFamily.alignedDictionary input shape pair hConnected hGenus
      incoming).symm.trans
      (W2M1kGaugeFamily.alignedDictionary input shape pair hConnected hGenus 0)
  | 1 => (W2M1kGaugeFamily.alignedDictionary input shape pair hConnected hGenus
      incoming).symm.trans
      (W2M1kGaugeFamily.alignedDictionary input shape pair hConnected hGenus 1)
  | 2 => (W2M1kGaugeFamily.alignedDictionary input shape pair hConnected hGenus
      incoming).symm.trans
      (W2M1kGaugeFamily.alignedDictionary input shape pair hConnected hGenus 2)

/-- **The row formula for Figure 33, Base I.a**,
`W2M1kGraphTracking.labelling_row`, read at the full-dimensional supply of
`A04M1kWiring`. -/
theorem m1kAlignedFullDim_row :
    ∀ (outgoing : Fin 3)
      (hdet : (GluingDatum.LengthMatrixPresentation.matrix
        ((A04M1kWiring.m1kAlignedFamily input shape pair hConnected hGenus incoming
          incomingFD).presentation outgoing)).det ≠ 0),
      (A04M1kWiring.alignedFullDim input shape pair hConnected hGenus incoming incomingFD
        (W2M1kGaugeFamily.alignedDictionary input shape pair hConnected hGenus)
        (W2M1kGaugeFamily.alignedMemberGenus input shape pair hConnected hGenus)
        outgoing hdet).labelling.row =
        (m1kAlignedBetween input shape pair hConnected hGenus incoming incomingFD
          outgoing).row.symm.trans incomingFD.labelling.row
  | 0, _ => W2M1kGraphTracking.labelling_row _
      (W2M1kGaugeFamily.alignedDictionary input shape pair hConnected hGenus)
      (alignedDictionary_row input shape pair hConnected hGenus) incoming 0 incomingFD
  | 1, _ => W2M1kGraphTracking.labelling_row _
      (W2M1kGaugeFamily.alignedDictionary input shape pair hConnected hGenus)
      (alignedDictionary_row input shape pair hConnected hGenus) incoming 1 incomingFD
  | 2, _ => W2M1kGraphTracking.labelling_row _
      (W2M1kGaugeFamily.alignedDictionary input shape pair hConnected hGenus)
      (alignedDictionary_row input shape pair hConnected hGenus) incoming 2 incomingFD

/-- **Figure 33, Base I.a, as a tracked routed wall.**  Exactly
`A04M1kWiring.routedW2M1kAligned`'s hypotheses plus one incoming tracking. -/
noncomputable def trackedW2M1kAligned
    (hwallColumn : (A04M1kWiring.m1kAlignedFamily input shape pair hConnected hGenus incoming
      incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart)
    (current : Tracks incomingFD graph label) :
    TrackedRoutedWall degree coordinate chart wall graph label :=
  TrackedRoutedWall.ofIncidence
    (A04M1kWiring.routedW2M1kAligned (wall := wall) input shape pair hConnected hGenus incoming
      incomingFD hwallColumn root chart hChart)
    incomingFD current
    (m1kAlignedBetween input shape pair hConnected hGenus incoming incomingFD)
    (m1kAlignedFullDim_row input shape pair hConnected hGenus incoming incomingFD)

@[simp] theorem trackedW2M1kAligned_toRoutedWall
    (hwallColumn : (A04M1kWiring.m1kAlignedFamily input shape pair hConnected hGenus incoming
      incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart)
    (current : Tracks incomingFD graph label) :
    (trackedW2M1kAligned (wall := wall) (graph := graph) (label := label) input shape pair
      hConnected hGenus incoming incomingFD hwallColumn root chart hChart current).toRoutedWall =
      A04M1kWiring.routedW2M1kAligned (wall := wall) input shape pair hConnected hGenus incoming
        incomingFD hwallColumn root chart hChart := rfl

end Aligned

/-! ### Base II.2.2.M, the separated orientation -/

section Separated

variable (input : W2SourceInput data star) (shape : Shape profile)
  (divided : DividedData profile)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (incoming : Fin 3)
  (incomingFD : FullDimensionalSourcePresentation
    ((separatedOrientation input shape divided hConnected hGenus).member incoming).datum
      coordinate)

/-- **`hDictionaryRow` for Base II.2.2.M.**  Here it is position `0` that is
remote, and it is `rfl` for the same reason. -/
theorem separatedDictionary_row (position : Fin 3) :
    (W2M1kGaugeFamily.separatedDictionary input shape divided hConnected hGenus position).row =
      ((separatedOrientation input shape divided hConnected hGenus).member position).row := by
  fin_cases position <;> rfl

/-- Figure 33's member-to-member incidence equivalences in Base II.2.2.M. -/
noncomputable def m1kSeparatedBetween :
    ∀ outgoing : Fin 3,
      StableGraphIncidence.Equivalence
        ((separatedOrientation input shape divided hConnected hGenus).member incoming).datum
        ((A04M1kWiring.m1kSeparatedFamily input shape divided hConnected hGenus incoming
          incomingFD).candidate outgoing).datum
  | 0 => (W2M1kGaugeFamily.separatedDictionary input shape divided hConnected hGenus
      incoming).symm.trans
      (W2M1kGaugeFamily.separatedDictionary input shape divided hConnected hGenus 0)
  | 1 => (W2M1kGaugeFamily.separatedDictionary input shape divided hConnected hGenus
      incoming).symm.trans
      (W2M1kGaugeFamily.separatedDictionary input shape divided hConnected hGenus 1)
  | 2 => (W2M1kGaugeFamily.separatedDictionary input shape divided hConnected hGenus
      incoming).symm.trans
      (W2M1kGaugeFamily.separatedDictionary input shape divided hConnected hGenus 2)

/-- **The row formula for Figure 33, Base II.2.2.M.** -/
theorem m1kSeparatedFullDim_row :
    ∀ (outgoing : Fin 3)
      (hdet : (GluingDatum.LengthMatrixPresentation.matrix
        ((A04M1kWiring.m1kSeparatedFamily input shape divided hConnected hGenus incoming
          incomingFD).presentation outgoing)).det ≠ 0),
      (A04M1kWiring.separatedFullDim input shape divided hConnected hGenus incoming incomingFD
        (W2M1kGaugeFamily.separatedDictionary input shape divided hConnected hGenus)
        (W2M1kGaugeFamily.separatedMemberGenus input shape divided hConnected hGenus)
        outgoing hdet).labelling.row =
        (m1kSeparatedBetween input shape divided hConnected hGenus incoming incomingFD
          outgoing).row.symm.trans incomingFD.labelling.row
  | 0, _ => W2M1kGraphTracking.labelling_row _
      (W2M1kGaugeFamily.separatedDictionary input shape divided hConnected hGenus)
      (separatedDictionary_row input shape divided hConnected hGenus) incoming 0 incomingFD
  | 1, _ => W2M1kGraphTracking.labelling_row _
      (W2M1kGaugeFamily.separatedDictionary input shape divided hConnected hGenus)
      (separatedDictionary_row input shape divided hConnected hGenus) incoming 1 incomingFD
  | 2, _ => W2M1kGraphTracking.labelling_row _
      (W2M1kGaugeFamily.separatedDictionary input shape divided hConnected hGenus)
      (separatedDictionary_row input shape divided hConnected hGenus) incoming 2 incomingFD

/-- **Figure 33, Base II.2.2.M, as a tracked routed wall.** -/
noncomputable def trackedW2M1kSeparated
    (hwallColumn : (A04M1kWiring.m1kSeparatedFamily input shape divided hConnected hGenus
      incoming incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart)
    (current : Tracks incomingFD graph label) :
    TrackedRoutedWall degree coordinate chart wall graph label :=
  TrackedRoutedWall.ofIncidence
    (A04M1kWiring.routedW2M1kSeparated (wall := wall) input shape divided hConnected hGenus
      incoming incomingFD hwallColumn root chart hChart)
    incomingFD current
    (m1kSeparatedBetween input shape divided hConnected hGenus incoming incomingFD)
    (m1kSeparatedFullDim_row input shape divided hConnected hGenus incoming incomingFD)

@[simp] theorem trackedW2M1kSeparated_toRoutedWall
    (hwallColumn : (A04M1kWiring.m1kSeparatedFamily input shape divided hConnected hGenus
      incoming incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart)
    (current : Tracks incomingFD graph label) :
    (trackedW2M1kSeparated (wall := wall) (graph := graph) (label := label) input shape divided
      hConnected hGenus incoming incomingFD hwallColumn root chart hChart current).toRoutedWall =
      A04M1kWiring.routedW2M1kSeparated (wall := wall) input shape divided hConnected hGenus
        incoming incomingFD hwallColumn root chart hChart := rfl

end Separated

end M1k

/-! ## 2.  Figure 34, the `w2Mkk` tag, in both bases -/

section Mkk

open DraismaVargas.LocalCases.SecondEquation
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W2MkkSourceCandidates
open DraismaVargas.LocalCases.W2MkkLimitColumns (firstOrientation secondOrientation)

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {wall : coordinate} {graph : CubicDartGraph D V}
  {label : D → coordinate}
  {target : CFGraph.{0}} {wallVertex : target.V}
  {data : GluingDatum target degree}
  {star : TwoStar target wallVertex} {block : WallBlock data wallVertex}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-! ### Base II.2.1.M -/

section First

variable (input : W2SourceInput data star) (shape : Shape profile)
  (member : FirstMember profile) (distinguished : Fin degree)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (incoming : Fin 3)
  (incomingFD : FullDimensionalSourcePresentation
    ((firstOrientation input shape member distinguished hConnected hGenus).member
      incoming).datum coordinate)

/-- **`hDictionaryRow` for Base II.2.1.M.**  `A04MoreTags.mkkFirstDictionary`'s
three dictionaries read the limit receipt's own member rows; the remote slot
(position `1`) is `rfl` because the branch-swap dictionary is
`StableGraphIncidence.sheetRelabel`, whose row map is
`SheetRelabelStable.stablePathEquiv`, the gauge's own. -/
theorem mkkFirstDictionary_row (position : Fin 3) :
    (A04MoreTags.mkkFirstDictionary input shape member distinguished hConnected hGenus
      position).row =
      ((firstOrientation input shape member distinguished hConnected hGenus).member
        position).row := by
  fin_cases position <;> rfl

/-- Figure 34's member-to-member incidence equivalences in Base II.2.1.M. -/
noncomputable def mkkFirstBetween :
    ∀ outgoing : Fin 3,
      StableGraphIncidence.Equivalence
        ((firstOrientation input shape member distinguished hConnected hGenus).member
          incoming).datum
        ((A04MoreTags.mkkFirstFamily input shape member distinguished hConnected hGenus
          incoming incomingFD).candidate outgoing).datum
  | 0 => (A04MoreTags.mkkFirstDictionary input shape member distinguished hConnected hGenus
      incoming).symm.trans
      (A04MoreTags.mkkFirstDictionary input shape member distinguished hConnected hGenus 0)
  | 1 => (A04MoreTags.mkkFirstDictionary input shape member distinguished hConnected hGenus
      incoming).symm.trans
      (A04MoreTags.mkkFirstDictionary input shape member distinguished hConnected hGenus 1)
  | 2 => (A04MoreTags.mkkFirstDictionary input shape member distinguished hConnected hGenus
      incoming).symm.trans
      (A04MoreTags.mkkFirstDictionary input shape member distinguished hConnected hGenus 2)

/-- **The row formula for Figure 34, Base II.2.1.M**,
`W2MkkGraphTracking.labelling_row`, read at the full-dimensional supply of
`A04MoreTags`. -/
theorem mkkFirstFullDim_row :
    ∀ (outgoing : Fin 3)
      (hdet : (GluingDatum.LengthMatrixPresentation.matrix
        ((A04MoreTags.mkkFirstFamily input shape member distinguished hConnected hGenus
          incoming incomingFD).presentation outgoing)).det ≠ 0),
      (A04MoreTags.mkkFirstFullDim input shape member distinguished hConnected hGenus incoming
        incomingFD
        (A04MoreTags.mkkFirstDictionary input shape member distinguished hConnected hGenus)
        (A04MoreTags.mkkFirstMemberGenus input shape member distinguished hConnected hGenus)
        outgoing hdet).labelling.row =
        (mkkFirstBetween input shape member distinguished hConnected hGenus incoming incomingFD
          outgoing).row.symm.trans incomingFD.labelling.row
  | 0, _ => W2MkkGraphTracking.labelling_row _
      (A04MoreTags.mkkFirstDictionary input shape member distinguished hConnected hGenus)
      (mkkFirstDictionary_row input shape member distinguished hConnected hGenus) incoming 0
      incomingFD
  | 1, _ => W2MkkGraphTracking.labelling_row _
      (A04MoreTags.mkkFirstDictionary input shape member distinguished hConnected hGenus)
      (mkkFirstDictionary_row input shape member distinguished hConnected hGenus) incoming 1
      incomingFD
  | 2, _ => W2MkkGraphTracking.labelling_row _
      (A04MoreTags.mkkFirstDictionary input shape member distinguished hConnected hGenus)
      (mkkFirstDictionary_row input shape member distinguished hConnected hGenus) incoming 2
      incomingFD

/-- **Figure 34, Base II.2.1.M, as a tracked routed wall.** -/
noncomputable def trackedW2MkkFirst
    (hwallColumn : (A04MoreTags.mkkFirstFamily input shape member distinguished hConnected
      hGenus incoming incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart)
    (current : Tracks incomingFD graph label) :
    TrackedRoutedWall degree coordinate chart wall graph label :=
  TrackedRoutedWall.ofIncidence
    (A04MoreTags.routedW2MkkFirst (wall := wall) input shape member distinguished hConnected
      hGenus incoming incomingFD hwallColumn root chart hChart)
    incomingFD current
    (mkkFirstBetween input shape member distinguished hConnected hGenus incoming incomingFD)
    (mkkFirstFullDim_row input shape member distinguished hConnected hGenus incoming incomingFD)

@[simp] theorem trackedW2MkkFirst_toRoutedWall
    (hwallColumn : (A04MoreTags.mkkFirstFamily input shape member distinguished hConnected
      hGenus incoming incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart)
    (current : Tracks incomingFD graph label) :
    (trackedW2MkkFirst (wall := wall) (graph := graph) (label := label) input shape member
      distinguished hConnected hGenus incoming incomingFD hwallColumn root chart hChart
      current).toRoutedWall =
      A04MoreTags.routedW2MkkFirst (wall := wall) input shape member distinguished hConnected
        hGenus incoming incomingFD hwallColumn root chart hChart := rfl

end First

/-! ### Base II.2.2.M -/

section Second

variable (input : W2SourceInput data star) (shape : Shape profile)
  (member : SecondMember profile) (distinguished : Fin degree)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (incoming : Fin 3)
  (incomingFD : FullDimensionalSourcePresentation
    ((secondOrientation input shape member distinguished hConnected hGenus).member
      incoming).datum coordinate)

/-- **`hDictionaryRow` for Base II.2.2.M.**  Here position `0` is the remote
one. -/
theorem mkkSecondDictionary_row (position : Fin 3) :
    (A04MoreTags.mkkSecondDictionary input shape member distinguished hConnected hGenus
      position).row =
      ((secondOrientation input shape member distinguished hConnected hGenus).member
        position).row := by
  fin_cases position <;> rfl

/-- Figure 34's member-to-member incidence equivalences in Base II.2.2.M. -/
noncomputable def mkkSecondBetween :
    ∀ outgoing : Fin 3,
      StableGraphIncidence.Equivalence
        ((secondOrientation input shape member distinguished hConnected hGenus).member
          incoming).datum
        ((A04MoreTags.mkkSecondFamily input shape member distinguished hConnected hGenus
          incoming incomingFD).candidate outgoing).datum
  | 0 => (A04MoreTags.mkkSecondDictionary input shape member distinguished hConnected hGenus
      incoming).symm.trans
      (A04MoreTags.mkkSecondDictionary input shape member distinguished hConnected hGenus 0)
  | 1 => (A04MoreTags.mkkSecondDictionary input shape member distinguished hConnected hGenus
      incoming).symm.trans
      (A04MoreTags.mkkSecondDictionary input shape member distinguished hConnected hGenus 1)
  | 2 => (A04MoreTags.mkkSecondDictionary input shape member distinguished hConnected hGenus
      incoming).symm.trans
      (A04MoreTags.mkkSecondDictionary input shape member distinguished hConnected hGenus 2)

/-- **The row formula for Figure 34, Base II.2.2.M.** -/
theorem mkkSecondFullDim_row :
    ∀ (outgoing : Fin 3)
      (hdet : (GluingDatum.LengthMatrixPresentation.matrix
        ((A04MoreTags.mkkSecondFamily input shape member distinguished hConnected hGenus
          incoming incomingFD).presentation outgoing)).det ≠ 0),
      (A04MoreTags.mkkSecondFullDim input shape member distinguished hConnected hGenus incoming
        incomingFD
        (A04MoreTags.mkkSecondDictionary input shape member distinguished hConnected hGenus)
        (A04MoreTags.mkkSecondMemberGenus input shape member distinguished hConnected hGenus)
        outgoing hdet).labelling.row =
        (mkkSecondBetween input shape member distinguished hConnected hGenus incoming
          incomingFD outgoing).row.symm.trans incomingFD.labelling.row
  | 0, _ => W2MkkGraphTracking.labelling_row _
      (A04MoreTags.mkkSecondDictionary input shape member distinguished hConnected hGenus)
      (mkkSecondDictionary_row input shape member distinguished hConnected hGenus) incoming 0
      incomingFD
  | 1, _ => W2MkkGraphTracking.labelling_row _
      (A04MoreTags.mkkSecondDictionary input shape member distinguished hConnected hGenus)
      (mkkSecondDictionary_row input shape member distinguished hConnected hGenus) incoming 1
      incomingFD
  | 2, _ => W2MkkGraphTracking.labelling_row _
      (A04MoreTags.mkkSecondDictionary input shape member distinguished hConnected hGenus)
      (mkkSecondDictionary_row input shape member distinguished hConnected hGenus) incoming 2
      incomingFD

/-- **Figure 34, Base II.2.2.M, as a tracked routed wall.** -/
noncomputable def trackedW2MkkSecond
    (hwallColumn : (A04MoreTags.mkkSecondFamily input shape member distinguished hConnected
      hGenus incoming incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart)
    (current : Tracks incomingFD graph label) :
    TrackedRoutedWall degree coordinate chart wall graph label :=
  TrackedRoutedWall.ofIncidence
    (A04MoreTags.routedW2MkkSecond (wall := wall) input shape member distinguished hConnected
      hGenus incoming incomingFD hwallColumn root chart hChart)
    incomingFD current
    (mkkSecondBetween input shape member distinguished hConnected hGenus incoming incomingFD)
    (mkkSecondFullDim_row input shape member distinguished hConnected hGenus incoming incomingFD)

@[simp] theorem trackedW2MkkSecond_toRoutedWall
    (hwallColumn : (A04MoreTags.mkkSecondFamily input shape member distinguished hConnected
      hGenus incoming incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart)
    (current : Tracks incomingFD graph label) :
    (trackedW2MkkSecond (wall := wall) (graph := graph) (label := label) input shape member
      distinguished hConnected hGenus incoming incomingFD hwallColumn root chart hChart
      current).toRoutedWall =
      A04MoreTags.routedW2MkkSecond (wall := wall) input shape member distinguished hConnected
        hGenus incoming incomingFD hwallColumn root chart hChart := rfl

end Second

end Mkk

/-! ## 3.  Figure 28, the `w3Four` tag

This is the tag that needs a mathematical argument rather than plumbing: the
four members of Equation (2) live over *different* gauge copies of the incoming
datum (Part I treats gluing data up to isomorphism, where branch swaps identify
these copies; for a fixed gluing datum they have to be kept apart), so a
member-to-member dictionary is the composite of the two members' dictionaries
to the incoming datum, and the four honest labellings
that Figure 28's receipts carry are only existentially honest.
`W3FourRegrownColumnSeam.MemberCertificates` is the bundle of the four
dictionaries and the four source-genus receipts -- the gauge copies are
`StableGraphIncidence.sheetRelabel`s along the branch swap composed with the
three member equivalences of Figure 28, as `W3FourStableIncidence.positionOneDictionary`,
`positionTwoDictionary` and `growDictionary` spell out and
`exists_figure28Dictionaries` packages -- and `MemberCertificates.certificate`
is the sixteen ordered transports.  `W3TrackedAnchoring.RowsCompatible` is the
row coherence at a stable path labelling of the wall datum, and
`W3TrackedAnchoring.exists_tracked_anchoredCertificates_withExtra` together with
`rowsCompatible_of_natural` produces it from the concrete two-branch
constructor.  Only nonsingular members are ever compared. -/

section W3Four

open DraismaVargas.LocalCases.W3FourClosure (FourStarGeometry)
open DraismaVargas.LocalCases.W3FourRegrownColumnSeam (MemberCertificates)
open DraismaVargas.LocalCases.W3TrackedAnchoring (RowsCompatible)
open DraismaVargas.LocalCases.W3FourHonestReceipts (gaugeFamily labelling wallColumn
  gaugeFamily_presentation_start)

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {wall : coordinate} {graph : CubicDartGraph D V}
  {label : D → coordinate}
  {target : CFGraph.{0}} {wallVertex : target.V}
  {data : GluingDatum target degree}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

variable {geometry : FourStarGeometry data wallVertex}
  (certified : MemberCertificates data wallVertex geometry)
  (hValid : data.Valid) (hConnected : graph_connected target) (hGenus : genus target = 0)
  (incoming : Fin 4)

/-! ### 3.1  Equation (2) at the identified member's own coordinates

`W3FourHonestReceipts.gaugeFamily certified incoming incomingFD.labelling` is
Equation (2)'s honest gauge family reordered so that the identified member is
presented at the incoming cover's *own* labelling
(`W3FourHonestReceipts.labelling_start`).  Every member is presented at its own
induced honest labelling, so `presentation_eq` and `HonestlyPresented` are
`rfl`, and `W3TrackedExit.outgoingLabelling_row` is the row formula at an
arbitrary incoming cover -- exactly the situation at the other nine tags. -/

section Honest

variable (incomingFD : FullDimensionalSourcePresentation
  (certified.receipts.candidate incoming).datum coordinate)

/-- **Figure 28's wall input at the identified member's own coordinates.**
Gauge-mixed, which is what `WallProgress.WallInput.ofGauge` exists for. -/
noncomputable def ofW3FourHonest
    (hwallColumn : wallColumn certified incoming incomingFD.labelling = wall)
    (root : target.V) :
    WallInput degree coordinate wall :=
  WallInput.ofGauge (gaugeFamily certified incoming incomingFD.labelling) hValid
    SourceCase.w3Four rfl hwallColumn hConnected hGenus root

@[simp] theorem ofW3FourHonest_case
    (hwallColumn : wallColumn certified incoming incomingFD.labelling = wall)
    (root : target.V) :
    (ofW3FourHonest (wall := wall) certified hValid hConnected hGenus incoming incomingFD
      hwallColumn root).case = SourceCase.w3Four := rfl

/-- The family's regrown column is the coordinate the incoming cover's own
labelling puts its regrown occurrence in. -/
theorem w3FourHonest_wallColumn :
    wallColumn certified incoming incomingFD.labelling =
      incomingFD.labelling.targetEdge.symm
        (occurrenceEquiv target wallVertex
          (certified.receipts.candidate incoming).right none) := rfl

/-- **The full-dimensional supply for `w3Four` at those coordinates.**  Each member's outgoing
presentation is `W3FourStableIncidence.outgoingPresentation` -- that is,
`StableGraphFullDimensional.presentationOfEquivalence` -- along the actual
member-to-member certificate, landing on that member's own induced honest
labelling, so `presentation_eq` is `rfl`. -/
noncomputable def w3FourHonestSupply
    (hwallColumn : wallColumn certified incoming incomingFD.labelling = wall)
    (root : target.V) :
    FullDimSupply (ofW3FourHonest (wall := wall) certified hValid hConnected hGenus incoming
      incomingFD hwallColumn root) where
  fullDim := fun outgoing hdet ↦ W3FourStableIncidence.outgoingPresentation (data := data)
    (certified.certificate incoming outgoing)
    (certified.receipts.candidate_valid outgoing hValid) hConnected hGenus
    (certified.memberGenus incoming) (certified.memberGenus outgoing) incomingFD
    (labelling certified incoming incomingFD.labelling outgoing) hdet
  presentation_eq := fun _ _ ↦ rfl

/-- The family is honestly presented. -/
theorem ofW3FourHonest_honestlyPresented
    (hwallColumn : wallColumn certified incoming incomingFD.labelling = wall)
    (root : target.V) :
    RoutedWall.HonestlyPresented (ofW3FourHonest (wall := wall) certified hValid hConnected
      hGenus incoming incomingFD hwallColumn root) :=
  fun i ↦ ⟨labelling certified incoming incomingFD.labelling i, rfl⟩

/-- **`hW25IncomingNonzero` for `w3Four`.**  The identified member is presented
at the incoming cover's own labelling, so this is `incomingFD.det_ne_zero`. -/
theorem ofW3FourHonest_incomingNonzero
    (hwallColumn : wallColumn certified incoming incomingFD.labelling = wall)
    (root : target.V) :
    (GluingDatum.LengthMatrixPresentation.matrix
      ((ofW3FourHonest (wall := wall) certified hValid hConnected hGenus incoming incomingFD
        hwallColumn root).family.presentation incoming)).det ≠ 0 := by
  show (GluingDatum.LengthMatrixPresentation.matrix
    ((gaugeFamily certified incoming incomingFD.labelling).presentation incoming)).det ≠ 0
  rw [gaugeFamily_presentation_start]
  exact incomingFD.det_ne_zero

/-- **`hW25IncomingMatrix` for `w3Four`, modulo the state--classifier
equation.**  `hChart` is the single named hypothesis, and it is the ordinary
one: the chart the march occupies is the incoming cover's own length matrix. -/
theorem ofW3FourHonest_incomingMatrix
    (hwallColumn : wallColumn certified incoming incomingFD.labelling = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart) :
    GluingDatum.LengthMatrixPresentation.matrix
      ((ofW3FourHonest (wall := wall) certified hValid hConnected hGenus incoming incomingFD
        hwallColumn root).family.presentation incoming) = chart := by
  show GluingDatum.LengthMatrixPresentation.matrix
    ((gaugeFamily certified incoming incomingFD.labelling).presentation incoming) = chart
  rw [gaugeFamily_presentation_start]
  exact hChart

/-- **`w3Four` as a routed wall at the identified member's own coordinates.**
Nothing is carried but `hChart` and `hwallColumn`; the four dictionaries and the
four source-genus receipts are `MemberCertificates`' own fields. -/
noncomputable def routedW3FourHonest
    (hwallColumn : wallColumn certified incoming incomingFD.labelling = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart) :
    RoutedWall degree coordinate chart wall :=
  RoutedWall.ofHonestSupply
    (ofW3FourHonest (wall := wall) certified hValid hConnected hGenus incoming incomingFD
      hwallColumn root)
    (w3FourHonestSupply (wall := wall) certified hValid hConnected hGenus incoming incomingFD
      hwallColumn root)
    (ofW3FourHonest_honestlyPresented (wall := wall) certified hValid hConnected hGenus incoming
      incomingFD hwallColumn root)
    incoming
    (ofW3FourHonest_incomingNonzero (wall := wall) certified hValid hConnected hGenus incoming
      incomingFD hwallColumn root)
    (ofW3FourHonest_incomingMatrix (wall := wall) certified hValid hConnected hGenus incoming
      incomingFD hwallColumn root chart hChart)

/-- **Figure 28 as a tracked routed wall.**  One incoming tracking at an
arbitrary full-dimensional cover of the identified member, the sixteen ordered
member-to-member certificates of `MemberCertificates`, and Figure 28's branch
gauge row coherence `RowsCompatible` give a tracking at every nonsingular
member of Equation (2)'s family, along the actual incidence equivalence the
full-dimensional package is transported along.  No matrix identifies a graph
and no candidate or base stage is replaced. -/
noncomputable def trackedW3Four
    (wallLabelling : StablePathLabelling data)
    (hRows : RowsCompatible certified wallLabelling)
    (hwallColumn : wallColumn certified incoming incomingFD.labelling = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart)
    (current : Tracks incomingFD graph label) :
    TrackedRoutedWall degree coordinate chart wall graph label :=
  TrackedRoutedWall.ofIncidence
    (routedW3FourHonest (wall := wall) certified hValid hConnected hGenus incoming incomingFD
      hwallColumn root chart hChart)
    incomingFD current
    (fun outgoing ↦ certified.certificate incoming outgoing)
    (fun outgoing hdet ↦ W3TrackedExit.outgoingLabelling_row certified wallLabelling hRows
      incoming incomingFD outgoing hdet)

@[simp] theorem trackedW3Four_toRoutedWall
    (wallLabelling : StablePathLabelling data)
    (hRows : RowsCompatible certified wallLabelling)
    (hwallColumn : wallColumn certified incoming incomingFD.labelling = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart)
    (current : Tracks incomingFD graph label) :
    (trackedW3Four (wall := wall) (graph := graph) (label := label) certified hValid hConnected
      hGenus incoming incomingFD wallLabelling hRows hwallColumn root chart
      hChart current).toRoutedWall =
      routedW3FourHonest (wall := wall) certified hValid hConnected hGenus incoming incomingFD
        hwallColumn root chart hChart := rfl

end Honest

/-! ### 3.2  The same tag against `A04MoreTags.routedW3Four`

`A04MoreTags.routedW3Four` presents Equation (2) at Figure 28's *fixed* order:
its family is `A04MoreTags.figure28HonestFamily`, whose presentations are
`A04MoreTags.figure28Labelling` -- the four receipts' own honest labellings
`W3FourHonestBalance.HonestFigure28.labelling`, moved to the ambient coordinate
by `relabel`.  Its supply's `fullDim` at a member *is*
`StableGraphFullDimensional.presentationOfEquivalence` along the certificate
supplied to `routedW3Four` (through
`W3FourStableIncidence.HonestFigure28Exit.presentationAt` and
`A04MoreTags.reindexFullDim`), which is what `ofIncidence` needs; but the
labelling it lands on is the member's own fixed-order honest labelling, in which
the incoming cover's row map does not appear.  So one equation has to be added
there, and is named `hIncomingRow`: that the incoming cover is presented at the
identified member's own honest rows.  It is not vacuous --
`normalizedIncoming_row` discharges it by `rfl` for the transported incoming
presentation -- and it is exactly what §3.1 avoids by reordering the family
instead. -/

section Fixed

variable (relabel : coordinate ≃ Option target.edges)
  (incomingFD : FullDimensionalSourcePresentation
    (certified.receipts.candidate incoming).datum (Option target.edges))

/-- **The row formula at `A04MoreTags.routedW3Four`'s own supply**, under the
one named equation `hIncomingRow`. -/
theorem figure28FullDim_row
    (wallLabelling : StablePathLabelling data)
    (hRows : RowsCompatible certified wallLabelling)
    (hincoming : (GluingDatum.LengthMatrixPresentation.matrix
      (certified.receipts.gaugeFamily.presentation incoming)).det ≠ 0)
    (hIncomingRow : incomingFD.labelling.row = (certified.receipts.labelling incoming).row)
    (outgoing : Fin 4)
    (hdet : (GluingDatum.LengthMatrixPresentation.matrix
      ((figure28HonestFamily certified.receipts relabel).presentation outgoing)).det ≠ 0) :
    (figure28FullDim certified.receipts relabel certified.certificate certified.memberGenus
      hValid hConnected hGenus incoming incomingFD outgoing hdet).labelling.row =
      (certified.certificate incoming outgoing).row.symm.trans
        (reindexFullDim relabel incomingFD).labelling.row := by
  have hOut : (GluingDatum.LengthMatrixPresentation.matrix
      (certified.receipts.gaugeFamily.presentation outgoing)).det ≠ 0 := by
    rw [← figure28HonestFamily_det certified.receipts relabel outgoing]
    exact hdet
  have hEnd := hRows outgoing hOut
  have hStart := hRows incoming hincoming
  have hLHS : (figure28FullDim certified.receipts relabel certified.certificate
      certified.memberGenus hValid hConnected hGenus incoming incomingFD outgoing
      hdet).labelling.row =
      (certified.receipts.labelling outgoing).row.trans relabel.symm := rfl
  rw [hLHS, hEnd]
  ext r
  simp [reindexLabelling, hIncomingRow, hStart, MemberCertificates.certificate,
    StableGraphIncidence.Equivalence.symm, StableGraphIncidence.Equivalence.trans]

/-- **Figure 28 as a tracked routed wall, at Figure 28's own fixed order.** -/
noncomputable def trackedW3FourFixed
    (wallLabelling : StablePathLabelling data)
    (hRows : RowsCompatible certified wallLabelling)
    (hincoming : (GluingDatum.LengthMatrixPresentation.matrix
      (certified.receipts.gaugeFamily.presentation incoming)).det ≠ 0)
    (hIncomingRow : incomingFD.labelling.row = (certified.receipts.labelling incoming).row)
    (root : target.V) (hrelabel : relabel wall = none)
    (chart : Matrix coordinate coordinate ℚ)
    (hChart : (GluingDatum.LengthMatrixPresentation.matrix
      (certified.receipts.gaugeFamily.presentation incoming)).submatrix relabel relabel = chart)
    (current : Tracks (reindexFullDim relabel incomingFD) graph label) :
    TrackedRoutedWall degree coordinate chart wall graph label :=
  TrackedRoutedWall.ofIncidence
    (routedW3Four (wall := wall) certified.receipts relabel certified.certificate
      certified.memberGenus hValid hConnected hGenus incoming incomingFD hincoming root
      hrelabel chart hChart)
    (reindexFullDim relabel incomingFD) current
    (fun outgoing ↦ certified.certificate incoming outgoing)
    (fun outgoing hdet ↦ figure28FullDim_row certified hValid hConnected hGenus incoming
      relabel incomingFD wallLabelling hRows hincoming hIncomingRow outgoing hdet)

@[simp] theorem trackedW3FourFixed_toRoutedWall
    (wallLabelling : StablePathLabelling data)
    (hRows : RowsCompatible certified wallLabelling)
    (hincoming : (GluingDatum.LengthMatrixPresentation.matrix
      (certified.receipts.gaugeFamily.presentation incoming)).det ≠ 0)
    (hIncomingRow : incomingFD.labelling.row = (certified.receipts.labelling incoming).row)
    (root : target.V) (hrelabel : relabel wall = none)
    (chart : Matrix coordinate coordinate ℚ)
    (hChart : (GluingDatum.LengthMatrixPresentation.matrix
      (certified.receipts.gaugeFamily.presentation incoming)).submatrix relabel relabel = chart)
    (current : Tracks (reindexFullDim relabel incomingFD) graph label) :
    (trackedW3FourFixed (wall := wall) (graph := graph) (label := label) certified hValid
      hConnected hGenus incoming relabel incomingFD wallLabelling hRows hincoming hIncomingRow
      root hrelabel chart hChart current).toRoutedWall =
      routedW3Four (wall := wall) certified.receipts relabel certified.certificate
        certified.memberGenus hValid hConnected hGenus incoming incomingFD hincoming root
        hrelabel chart hChart := rfl

/-- **The transported incoming presentation**: the same member, the same
candidate and base stage, presented at the member's own honest labelling in
Figure 28's fixed order. -/
noncomputable def normalizedIncoming
    (hincoming : (GluingDatum.LengthMatrixPresentation.matrix
      (certified.receipts.gaugeFamily.presentation incoming)).det ≠ 0) :
    FullDimensionalSourcePresentation (certified.receipts.candidate incoming).datum
      (Option target.edges) :=
  W3FourStableIncidence.HonestFigure28Exit.presentationAt certified.receipts incoming incoming
    (certified.certificate incoming incoming) hValid hConnected hGenus
    (certified.memberGenus incoming) (certified.memberGenus incoming) incomingFD hincoming

/-- **`hIncomingRow` is not vacuous.** -/
theorem normalizedIncoming_row
    (hincoming : (GluingDatum.LengthMatrixPresentation.matrix
      (certified.receipts.gaugeFamily.presentation incoming)).det ≠ 0) :
    (normalizedIncoming certified hValid hConnected hGenus incoming incomingFD
      hincoming).labelling.row = (certified.receipts.labelling incoming).row := rfl

end Fixed

end W3Four

/-! ## 4.  The all-tags dispatch -/

section Dispatch

open DraismaVargas.LocalCases.SemanticAtlasMarch

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  {baseStart baseFinish : coordinate → ℚ}

/-- **The tracked local-classification obligation at one chart.**  At every
*first wall* of the segment from `start` to `finish` -- the only coordinate the
march crosses, and the only one carrying an interior wall metric -- the state's
classification is one of the ten tags, each of which inhabits
`TrackedRoutedWall` (the table in the module header).

The guard is `SemanticAtlasMarch.IsFirstWall`, the same one every field of
`SemanticAtlasMarch.State.PresentedProgress` carries;
`InteriorProgress.admissibleColumn_of_firstWall` is what turns it into the wall
metric the ten tag constructors consume. -/
def TrackedClassified (degree : ℕ) (coordinate : Type) [Fintype coordinate]
    [DecidableEq coordinate] (chart : Matrix coordinate coordinate ℚ)
    (start finish : coordinate → ℚ)
    {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    (graph : CubicDartGraph D V) (label : D → coordinate) : Prop :=
  ∀ wall : coordinate, IsFirstWall start finish wall →
    Nonempty (TrackedRoutedWall degree coordinate chart wall graph label)

/-- The untracked residue of a tracked classification is
`A04MoreTags.presentedProgressOfRoutedClassification`'s input, verbatim. -/
theorem nonempty_routedWall_of_trackedClassified
    {chart : Matrix coordinate coordinate ℚ} {start finish : coordinate → ℚ}
    (routed : TrackedClassified degree coordinate chart start finish graph label)
    (wall : coordinate) (hw : IsFirstWall start finish wall) :
    Nonempty (RoutedWall degree coordinate chart wall) :=
  (routed wall hw).elim fun w ↦ ⟨w.toRoutedWall⟩

/-- **The tracked analogue of
`A04MoreTags.presentedProgressOfRoutedClassification`.**  Its underlying
presented progress is `A04MoreTags.presentedProgressOfRoutedWalls` of the
selected routed walls, so `tracksAt` is asked at literally each wall's
`supply.fullDim`. -/
noncomputable def trackedProgressOfTrackedClassification
    (current : TrackedState degree graph label
      (atlasChartMatrix coordinate degree) baseStart baseFinish)
    (routed : TrackedClassified degree coordinate
      (atlasChartMatrix coordinate degree current.toMatrixState.label)
      current.toMatrixState.currentStart current.toMatrixState.currentFinish
      graph label)
    (hA02Generic : SimpleNegativeCrossings current.toMatrixState.currentStart
      current.toMatrixState.currentFinish) :
    TrackedProgress current :=
  trackedProgressOfRoutedWalls current (fun wall hw ↦ (routed wall hw).some) hA02Generic

/-- **The tracked step from a tracked classification.** -/
theorem exists_step_of_trackedClassification (hDegree : 2 ≤ degree)
    (current : TrackedState degree graph label
      (atlasChartMatrix coordinate degree) baseStart baseFinish)
    (routed : TrackedClassified degree coordinate
      (atlasChartMatrix coordinate degree current.toMatrixState.label)
      current.toMatrixState.currentStart current.toMatrixState.currentFinish
      graph label)
    (hA02Generic : SimpleNegativeCrossings current.toMatrixState.currentStart
      current.toMatrixState.currentFinish)
    (hNonterminal : ¬ TrackedState.Terminal current) :
    ∃ next : TrackedState degree graph label
      (atlasChartMatrix coordinate degree) baseStart baseFinish,
      TrackedState.Step current next :=
  exists_step_of_trackedRoutedWalls hDegree current
    (fun wall hw ↦ (routed wall hw).some) hA02Generic hNonterminal

end Dispatch

/-! ## 5.  The composite from the tracked caterpillar seed -/

section Seed

/-- **The composite, end to end, on the tracked classification.**
`TrackedWallProgress.exists_terminal_tracked_caterpillar_of_routedWalls` with
the per-wall bundles replaced by their `Nonempty` form, which is what the ten
tag constructors produce.  The caterpillar seed, a tracked classification at
every nonterminal reached state, and the genericity of the start give a reachable terminal
tracked state whose payload still carries the ambient row-labelled graph, its
row labels and the source genus, together with the cleared terminal face and the
rank-one pencil.

The remaining inputs are entirely inside `routed`: at each wall the
classification inputs of `IncomingSourceCases.exists_classification` --
`hStable`, `hCompat` and `hTrivalent` -- are what select the tag, and the tag's
own constructor then takes exactly the hypotheses its untracked `routed*`
constructor takes plus one incoming tracking (plus `RowsCompatible` at
`w3Four`).  `2 ≤ degree` is automatic here, the caterpillar's degree being
`m + 2`. -/
theorem exists_terminal_tracked_caterpillar_of_trackedClassification (m : ℕ)
    (coordinates : Fin (6 * m + 3) → ℚ) (hPositive : ∀ i, 0 < coordinates i)
    (baseStart baseFinish : Fin (6 * m + 3) → ℚ)
    (hMap : (CaterpillarGenericSeed.matrix m).mulVec coordinates = baseStart)
    (routed : ∀ current : TrackedState (m + 2)
        (TrackedPencil.seedGraph (CaterpillarSeed.seed m)
          (CaterpillarSeed.seedFullDim m (CaterpillarRows.fullDim m)))
        (TrackedPencil.seedLabel (CaterpillarSeed.seed m)
          (CaterpillarSeed.seedFullDim m (CaterpillarRows.fullDim m)))
        (MatrixAtlas.atlasMatrix (coordinate := Fin (6 * m + 3)) (degree := m + 2))
        baseStart baseFinish,
      ¬ TrackedState.Terminal current →
      TrackedClassified (m + 2) (Fin (6 * m + 3))
        (MatrixAtlas.atlasMatrix current.toMatrixState.label)
        current.toMatrixState.currentStart current.toMatrixState.currentFinish
        (TrackedPencil.seedGraph (CaterpillarSeed.seed m)
          (CaterpillarSeed.seedFullDim m (CaterpillarRows.fullDim m)))
        (TrackedPencil.seedLabel (CaterpillarSeed.seed m)
          (CaterpillarSeed.seedFullDim m (CaterpillarRows.fullDim m))))
    (hGeneric : ∀ current : TrackedState (m + 2)
        (TrackedPencil.seedGraph (CaterpillarSeed.seed m)
          (CaterpillarSeed.seedFullDim m (CaterpillarRows.fullDim m)))
        (TrackedPencil.seedLabel (CaterpillarSeed.seed m)
          (CaterpillarSeed.seedFullDim m (CaterpillarRows.fullDim m)))
        (MatrixAtlas.atlasMatrix (coordinate := Fin (6 * m + 3)) (degree := m + 2))
        baseStart baseFinish,
      SimpleNegativeCrossings current.toMatrixState.currentStart
        current.toMatrixState.currentFinish) :
    ∃ final, Relation.ReflTransGen TrackedState.Step
        (TrackedState.caterpillarGeneric m coordinates hPositive baseStart baseFinish
          hMap) final ∧
      TrackedState.Terminal final ∧
      TrackedPencil (m + 2)
        (TrackedPencil.seedGraph (CaterpillarSeed.seed m)
          (CaterpillarSeed.seedFullDim m (CaterpillarRows.fullDim m)))
        (TrackedPencil.seedLabel (CaterpillarSeed.seed m)
          (CaterpillarSeed.seedFullDim m (CaterpillarRows.fullDim m)))
        (MatrixAtlas.atlasMatrix final.toMatrixState.label)
        final.toMatrixState.currentStart ∧
      SemanticAtlasMarch.CarriesClearedFace (m + 2)
        (MatrixAtlas.atlasMatrix final.toMatrixState.label)
        final.toMatrixState.currentFinish ∧
      ∃ source : CFGraph.{0}, BNExists source 1 (m + 2) :=
  exists_terminal_tracked_caterpillar_of_routedWalls m coordinates hPositive baseStart
    baseFinish hMap
    (fun current hNonterminal wall hw ↦ (routed current hNonterminal wall hw).some)
    hGeneric

end Seed

end DraismaVargas.LocalCases.TrackedWallProgressMore
