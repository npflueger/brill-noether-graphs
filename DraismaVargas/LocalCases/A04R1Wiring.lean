import DraismaVargas.LocalCases.A04MoreTags
import DraismaVargas.LocalCases.W2R1ArbitraryIncomingExit

/-!
# The wall dispatcher and the full-dimensional supply at the `w2R1` tag

`A04FourTags` defines `FullDimSupply` -- the two gated fields of
`SemanticAtlasMarch.State.PresentedProgress` at one `WallProgress.WallInput` -- and
inhabits it for `w3Nd2CoarseFine`, `w3Nd3CoarseFine` and `w4`; `A04MoreTags`
does `w2P`, `w2Mkk` in both orientations and `w3Four`, and bundles the per-wall
data as `RoutedWall`; `A04M11Wiring` does `w2M11` and `A04ShiftWiring` does
`w3Shift`.  This file does Equation (10)'s tag, `w2R1`, which completes the ten.

| tag | wall input | supply | routed | carried |
|---|---|---|---|---|
| `w2R1` | `ofW2R1` (`WallInput.ofTrivalent` on `W2R1GraphData.family`) | `w2R1Supply` | `routedW2R1` | `hChart` |

`hChart` is the **state–classifier equation** and nothing else: that the chart
the march currently occupies is the identified incoming member's own honest
length matrix.  As at `w2P`, `w2Mkk`, `w3Four`, `w2M11` and `w3Shift`, it is one
named hypothesis and there are no others.

## Why the family must be the honest one

A wall input whose family presented the two candidates by the raw split census
`oldPath`/`newSheets` would not do: neither of the two supply fields could be
literal on it, exactly as `A04FourTags` §"`w4`" records for `ofFourValent`.

The wall input used here is the one `w2P` uses, `WallInput.ofTrivalent`, on the
**honest** family `W2R1GraphData.family` — `ofTrivalent` is not about trivalence
of the wall, it is the constructor that takes a `BalancedGlobal.PresentedFamily`
over one datum in the ambient coordinate and forwards it unchanged (its own
docstring says so; `SourceCase.w2R1.arity` is `2`, and `rfl` proves it).
`W2R1GraphData.family` is
`W2R1CommonBalance.LimitColumns.honestPresentedFamily` at
`W2R1GraphData.initialLabelling`, so every `presentation position` is that
member's own `StableLengthMatrixLabelling.presentation` and the two supply
fields are `W2R1GraphData.familyFullDim` and `familyFullDim_presentation`
verbatim, the latter proved `fun _ _ ↦ rfl`.

## The incoming side

`W2R1ArbitraryIncomingExit` states `hW25IncomingNonzero` and
`hW25IncomingMatrix` on `W2R1GraphData.family` itself, since
`WallInput.ofTrivalent` only forwards `family`.  This file reads them at the
wall input: `ofW2R1_incomingNonzero` and `ofW2R1_incomingMatrix` are
`family_incoming_nonzero` and `family_incoming_matrix` there.  No
`Classical.choose` is needed anywhere: `W2R1GraphData.outgoingPresentation` is
a constructive per-member transport along `W2R1GraphData.between`, so the
supply is data, not a choice out of an existential.
-/

namespace DraismaVargas.LocalCases.A04R1Wiring

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.ClassifiedContinuation
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.SecondEquation
open DraismaVargas.LocalCases.W2R1SourceCandidates
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.WallProgress
open DraismaVargas.LocalCases.A04FourTags (FullDimSupply)
open DraismaVargas.LocalCases.A04MoreTags (RoutedWall)

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {degree : ℕ} {wall : coordinate}

variable {target : CFGraph.{0}} {wallVertex : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wallVertex}
  (pair : Pair data star) (input : W2SourceInput data star)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (incoming : Fin 2)
  (incomingFD : FullDimensionalSourcePresentation
    (pair.candidate incoming).datum coordinate)

/-! ## 1.  The wall input -/

/-- **Equation (10)'s wall input.**  `WallInput.ofTrivalent` on the honest
presented family of the two `{w2-r1}` members, in the identified incoming
member's own square coordinates. -/
noncomputable def ofW2R1
    (hwallColumn : (W2R1GraphData.family pair input incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    WallInput degree coordinate wall :=
  WallInput.ofTrivalent (W2R1GraphData.family pair input incoming incomingFD)
    input.valid SourceCase.w2R1 rfl hwallColumn hConnected hGenus root

@[simp] theorem ofW2R1_case
    (hwallColumn : (W2R1GraphData.family pair input incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    (ofW2R1 (wall := wall) pair input hConnected hGenus incoming incomingFD
      hwallColumn root).case = SourceCase.w2R1 := rfl

/-! ## 2.  The gated pair -/

/-- **The supply for `w2R1`.**  Both fields are `W2R1GraphData`'s, unchanged: the
outgoing presentation is `StableGraphFullDimensional.presentationOfEquivalence`
along the two-block stable-incidence dictionary `W2R1GraphData.between`, and it
is a presentation *of that member* because the family carries the honest
labellings the transport installs. -/
noncomputable def w2R1Supply
    (hwallColumn : (W2R1GraphData.family pair input incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    FullDimSupply (ofW2R1 (wall := wall) pair input hConnected hGenus incoming
      incomingFD hwallColumn root) where
  fullDim := W2R1GraphData.familyFullDim pair input hConnected hGenus incoming incomingFD
  presentation_eq := W2R1GraphData.familyFullDim_presentation pair input hConnected
    hGenus incoming incomingFD

/-! ## 3.  The incoming side -/

/-- **The `w2R1` family presents the identified incoming member by its own
honest labelling.**  `W2R1GraphData.outgoingLabelling_self`, read at the wall
input. -/
theorem ofW2R1_presentation_incoming
    (hwallColumn : (W2R1GraphData.family pair input incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    (ofW2R1 (wall := wall) pair input hConnected hGenus incoming incomingFD
        hwallColumn root).family.presentation incoming =
      StableLengthMatrixLabelling.presentation incomingFD.labelling :=
  W2R1ArbitraryIncomingExit.family_presentation_incoming pair incoming input incomingFD

/-- **`hW25IncomingNonzero` for `w2R1`.**
`W2R1ArbitraryIncomingExit.family_incoming_nonzero`. -/
theorem ofW2R1_incomingNonzero
    (hwallColumn : (W2R1GraphData.family pair input incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    (GluingDatum.LengthMatrixPresentation.matrix
      ((ofW2R1 (wall := wall) pair input hConnected hGenus incoming incomingFD
        hwallColumn root).family.presentation incoming)).det ≠ 0 :=
  W2R1ArbitraryIncomingExit.family_incoming_nonzero pair incoming input incomingFD

/-- **`hW25IncomingMatrix` for `w2R1`, modulo the state–classifier equation.**
`hChart` is the single named hypothesis;
`W2R1ArbitraryIncomingExit.family_incoming_matrix` is the rest. -/
theorem ofW2R1_incomingMatrix
    (hwallColumn : (W2R1GraphData.family pair input incoming incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart) :
    GluingDatum.LengthMatrixPresentation.matrix
        ((ofW2R1 (wall := wall) pair input hConnected hGenus incoming incomingFD
          hwallColumn root).family.presentation incoming) = chart :=
  W2R1ArbitraryIncomingExit.family_incoming_matrix pair incoming input incomingFD chart
    hChart

/-- **`hW25Nodup` for `w2R1`.**  The family's presentations are the honest
labellings' own, so `A04MoreTags.nodup_labelling_path` applies with no case
data. -/
theorem ofW2R1_nodup
    (hwallColumn : (W2R1GraphData.family pair input incoming incomingFD).wallColumn = wall)
    (root : target.V) (i : Fin 2) (row : coordinate) :
    (((ofW2R1 (wall := wall) pair input hConnected hGenus incoming incomingFD
      hwallColumn root).family.presentation i).path row).Nodup :=
  A04MoreTags.nodup_labelling_path
    (W2R1GraphData.outgoingLabelling pair input.valid incoming incomingFD i) row

/-- The `w2R1` family is honestly presented. -/
theorem ofW2R1_honestlyPresented
    (hwallColumn : (W2R1GraphData.family pair input incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    RoutedWall.HonestlyPresented (ofW2R1 (wall := wall) pair input hConnected hGenus
      incoming incomingFD hwallColumn root) :=
  fun i ↦ ⟨W2R1GraphData.outgoingLabelling pair input.valid incoming incomingFD i, rfl⟩

/-! ## 4.  The routed wall -/

/-- **`w2R1` as a routed wall.**  Nothing is carried but `hChart`. -/
noncomputable def routedW2R1
    (hwallColumn : (W2R1GraphData.family pair input incoming incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart) :
    RoutedWall degree coordinate chart wall :=
  RoutedWall.ofHonestSupply
    (ofW2R1 (wall := wall) pair input hConnected hGenus incoming incomingFD hwallColumn
      root)
    (w2R1Supply pair input hConnected hGenus incoming incomingFD hwallColumn root)
    (ofW2R1_honestlyPresented pair input hConnected hGenus incoming incomingFD
      hwallColumn root)
    incoming
    (ofW2R1_incomingNonzero pair input hConnected hGenus incoming incomingFD hwallColumn
      root)
    (ofW2R1_incomingMatrix pair input hConnected hGenus incoming incomingFD hwallColumn
      root chart hChart)

/-! ### Where the incoming position comes from

An arbitrary incoming `{w2-r1}` cover **is** one of Equation (10)'s two
members (`W2R1IncomingMatching.exists_member_normalization`), with the literal
`Option` column dictionary, whose `none` entry is the contracted occurrence
(`M11IncomingCoordinates.incomingColumnEquiv_none`).  So the member's `position`
is `hW25Incoming`, its full-dimensional presentation `fd` is the `incomingFD`
above, its matrix clause is `hChart`, and its column clause against the
incoming cover's own presentation `fullDim` is literally

```
fd.labelling.targetEdge.symm (W2R1CommonBalance.columnEquiv pair position none)
  = fullDim.labelling.targetEdge.symm contracted
```

whose left-hand side is this family's regrown column by `r1Family_wallColumn`
below.  So `routedW2R1` produces a `RoutedWall` at this tag as soon as the
march's crossed coordinate is the original contracted column -- an
identification made by the tracked march, not by the local case, exactly as at
every other tag. -/

/-- The `w2R1` family's regrown column, read on the identified member's own
occurrence dictionary: transport to member `0` and back cancels, exactly as at
`w2P` (`A04MoreTags.ofW2P_family_wallColumn`) and `w2M11`
(`A04M11Wiring.m11Family_wallColumn`). -/
theorem r1Family_wallColumn :
    (W2R1GraphData.family pair input incoming incomingFD).wallColumn =
      incomingFD.labelling.targetEdge.symm
        (W2R1CommonBalance.columnEquiv pair incoming none) := by
  show ((incomingFD.labelling.targetEdge.trans
      ((W2R1CommonBalance.columnEquiv pair incoming).symm.trans
        (W2R1CommonBalance.columnEquiv pair 0))).trans
      (W2R1CommonBalance.columnEquiv pair 0).symm).symm none = _
  refine (Equiv.symm_apply_eq _).mpr ?_
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

end DraismaVargas.LocalCases.A04R1Wiring
