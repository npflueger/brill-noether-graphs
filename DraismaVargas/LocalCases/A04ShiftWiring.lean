import DraismaVargas.LocalCases.A04MoreTags
import DraismaVargas.LocalCases.W3ShiftStableIncidence
import DraismaVargas.LocalCases.W3WallInput

/-!
# Routed walls at the `w3Shift` tag

`A04FourTags` defines `FullDimSupply` — the two gated full-dimensional fields of
`WallProgress.presentedProgressOfWallInputs` at one `WallProgress.WallInput` —
and inhabits it for `w3Nd2CoarseFine`, `w3Nd3CoarseFine` and `w4`;
`A04MoreTags` adds `w2P`, `w2Mkk` in both orientations and `w3Four`, and bundles
the per-wall input as `RoutedWall`; `A04M11Wiring` adds `w2M11`.  This file
treats Equation (3)'s tag, `w3Shift`.

| tag | wall input | supply | routed | carried |
|---|---|---|---|---|
| `w3Shift` | `ofW3Shift` (`W3WallInput.ofShift` on `shiftRows`) | `w3ShiftSupply` | `routedW3Shift` | `hChart` |

`hChart` is the **state–classifier equation** and nothing else: that the chart
the march currently occupies is the identified incoming member's own honest
length matrix.  As at `w2P`, `w2Mkk` and `w2M11`, it is one named hypothesis and
there are no others.

## The two inputs of the supply

A `w3Shift` supply is `A04MoreTags` §2's proof verbatim, and its
`presentation_eq` is `rfl` for the same reason, once Figure 29 has

1. a `W3ShiftClosure.LimitRows` at an arbitrary
   `W4StableSource.StableLengthMatrixLabelling` of one member, and
2. a `StableGraphIncidence.Equivalence` between the two members of the pair.

These are supplied as follows:

1. is `W3ShiftHonestBalance.limitRows`, a `LimitRows` on
   `W3ShiftLimitRows.shiftMembers` whose `presentation i` is literally
   `(W3ShiftHonestBalance.labelling shrink hValid initial i).presentation`
   (`honestLabelling_matrix` is `rfl`) and whose `wallColumn` is whatever
   coordinate the supplied labelling puts the regrown occurrence in;
2. is `W3ShiftGraphData.between`, and
   `W3ShiftStableIncidence.outgoingPresentation` is
   `StableGraphFullDimensional.presentationOfEquivalence` along it.

So this file is `A04MoreTags` §2 verbatim, at `initial :=
W3ShiftStableIncidence.initialLabelling`, and `routedW3Shift` is the routed wall
at this tag.

## Why `presentation_eq` is `rfl`

`W3ShiftStableIncidence.outgoingLabelling shrink hValid incoming incomingFD
outgoing` *is* `W3ShiftHonestBalance.labelling shrink hValid
(W3ShiftStableIncidence.initialLabelling shrink hValid incoming incomingFD)
outgoing`, by definition; `shiftRows` is `W3ShiftHonestBalance.limitRows` at that
same `initial`, so the family's `presentation outgoing` is that labelling's own
presentation, and `presentationOfEquivalence`'s `labelling` field is the
argument verbatim (`W3ShiftStableIncidence.outgoingPresentation_labelling` is
`rfl`).  The supply's second field is therefore literal at both positions, as it
is for every honest tag.

## What the wall input is

`W3WallInput.ofShift`, which is `WallProgress.WallInput.ofTrivalent` on
`W3WallInput.shiftFamily` with `case := SourceCase.w3Shift` and arity
`rfl : 2 = SourceCase.w3Shift.arity`.  `hValid` is the *incoming* datum's
validity — Equation (3)'s pair lives over `data` itself
(`W3ShiftLimitRows.shiftMembers shrink : Fin 2 → Candidate target degree data
wallVertex`), so `base` is `data` and `ofShift`'s `hBase` is `hValid`, with no
gauge copy in between.

`W3WallInput.ofShiftReindexed` is **not** used and is not needed.  It exists
because `W3ShiftLimitRows.limitRows` is stated at `Option target.edges` with
`wallColumn = none`; `W3ShiftHonestBalance.limitRows` is stated at the ambient
`coordinate` already, with its wall column the coordinate the identified
member's own labelling puts the regrown occurrence in — which
`shiftRows_wallColumn` identifies with
`incomingFD.labelling.targetEdge.symm (occurrenceEquiv … none)`, the left-hand
side of the wall clause of `W3ShiftGraphTracking.exists_matched_tracking`.  So no
reindexing equivalence enters and none is written.
-/

namespace DraismaVargas.LocalCases.A04ShiftWiring

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.ClassifiedContinuation
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.ThirdEquation
open DraismaVargas.LocalCases.W3R1SourceProfile
open DraismaVargas.LocalCases.W3ShiftSourceCandidates
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.WallProgress
open DraismaVargas.LocalCases.A04FourTags (FullDimSupply)
open DraismaVargas.LocalCases.A04MoreTags (RoutedWall)
open DraismaVargas.LocalCases.W3ShiftLimitRows (shiftMembers)

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {degree : ℕ} {wall : coordinate}

variable {target : CFGraph.{0}} {wallVertex : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wallVertex}
  {input : W3SourceInput data star} {shift : ShiftProfile input}
  (shrink : ShrinkData shift) (hValid : data.Valid)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (incoming : Fin 2)
  (incomingFD : FullDimensionalSourcePresentation
    (shiftMembers shrink incoming).datum coordinate)

/-! ## 1.  The wall input -/

/-- **Equation (3)'s limit rows in the identified member's own square
coordinates.**  `W3ShiftHonestBalance.limitRows` at
`W3ShiftStableIncidence.initialLabelling`: the same `initial` the outgoing
transport is taken at, which is the whole reason the supply's second field is
`rfl` below. -/
noncomputable def shiftRows :
    W3ShiftClosure.LimitRows (coordinate := coordinate) (shiftMembers shrink) :=
  W3ShiftHonestBalance.limitRows shrink hValid
    (W3ShiftStableIncidence.initialLabelling shrink hValid incoming incomingFD)

@[simp] theorem shiftRows_presentation (outgoing : Fin 2) :
    (shiftRows shrink hValid incoming incomingFD).presentation outgoing =
      StableLengthMatrixLabelling.presentation
        (W3ShiftStableIncidence.outgoingLabelling shrink hValid incoming incomingFD
          outgoing) := rfl

/-- **Figure 29's wall input.**  Trivalent: both members of the pair live over
`data` itself, so `ofShift`'s `base` is the incoming datum and its `hBase` is
`hValid`. -/
noncomputable def ofW3Shift
    (hwallColumn : (shiftRows shrink hValid incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    WallInput degree coordinate wall :=
  W3WallInput.ofShift (shiftMembers shrink) (shiftRows shrink hValid incoming incomingFD)
    hValid hwallColumn hConnected hGenus root

@[simp] theorem ofW3Shift_case
    (hwallColumn : (shiftRows shrink hValid incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    (ofW3Shift (wall := wall) shrink hValid hConnected hGenus incoming incomingFD
      hwallColumn root).case = SourceCase.w3Shift := rfl

/-! ## 2.  The gated full-dimensional pair -/

/-- Figure 29's two outgoing presentations, one
`W3ShiftStableIncidence.outgoingPresentation` per member: the transport of the
identified member's own full-dimensional presentation along
`W3ShiftGraphData.between`. -/
noncomputable def shiftFullDim : ∀ outgoing : Fin 2,
    (GluingDatum.LengthMatrixPresentation.matrix
      ((shiftRows shrink hValid incoming incomingFD).presentation outgoing)).det ≠ 0 →
    FullDimensionalSourcePresentation (shiftMembers shrink outgoing).datum coordinate :=
  fun outgoing hdet ↦ W3ShiftStableIncidence.outgoingPresentation shrink hValid
    hConnected hGenus incoming outgoing incomingFD hdet

/-- **The full-dimensional supply for `w3Shift`, with nothing carried.**  On
exactly the hypotheses
`ofW3Shift` and `W3ShiftStableIncidence.outgoingPresentation` already take. -/
noncomputable def w3ShiftSupply
    (hwallColumn : (shiftRows shrink hValid incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    FullDimSupply (ofW3Shift (wall := wall) shrink hValid hConnected hGenus incoming
      incomingFD hwallColumn root) where
  fullDim := shiftFullDim shrink hValid hConnected hGenus incoming incomingFD
  presentation_eq := fun _ _ ↦ rfl

/-! ## 3.  The incoming side -/

/-- **The `w3Shift` family presents the identified incoming member by its own
honest labelling.**  `W3ShiftStableIncidence.outgoingLabelling_self`: transport
to member `0` and back cancels both the row equivalence and the
target-occurrence equivalence. -/
theorem ofW3Shift_presentation_incoming
    (hwallColumn : (shiftRows shrink hValid incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    (ofW3Shift (wall := wall) shrink hValid hConnected hGenus incoming incomingFD
        hwallColumn root).family.presentation incoming =
      StableLengthMatrixLabelling.presentation incomingFD.labelling := by
  change StableLengthMatrixLabelling.presentation
    (W3ShiftStableIncidence.outgoingLabelling shrink hValid incoming incomingFD
      incoming) = _
  rw [W3ShiftStableIncidence.outgoingLabelling_self shrink hValid incoming incomingFD]

/-- **`hW25IncomingNonzero` for `w3Shift`.**  The identified member's own
`det_ne_zero`; equivalently `W3ShiftStableIncidence.incomingDet_ne_zero`. -/
theorem ofW3Shift_incomingNonzero
    (hwallColumn : (shiftRows shrink hValid incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    (GluingDatum.LengthMatrixPresentation.matrix
      ((ofW3Shift (wall := wall) shrink hValid hConnected hGenus incoming incomingFD
        hwallColumn root).family.presentation incoming)).det ≠ 0 := by
  rw [ofW3Shift_presentation_incoming shrink hValid hConnected hGenus incoming
    incomingFD hwallColumn root]
  exact incomingFD.det_ne_zero

/-- **`hW25IncomingMatrix` for `w3Shift`, modulo the state–classifier
equation.**  `hChart` is the single named hypothesis; the rest is
`outgoingLabelling_self`. -/
theorem ofW3Shift_incomingMatrix
    (hwallColumn : (shiftRows shrink hValid incoming incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart) :
    GluingDatum.LengthMatrixPresentation.matrix
        ((ofW3Shift (wall := wall) shrink hValid hConnected hGenus incoming incomingFD
          hwallColumn root).family.presentation incoming) = chart := by
  rw [ofW3Shift_presentation_incoming shrink hValid hConnected hGenus incoming
    incomingFD hwallColumn root]
  exact hChart

/-- **`hW25Nodup` for `w3Shift`.**  The family's presentations are the honest
labellings' own, so `A04MoreTags.nodup_labelling_path` applies with no case data. -/
theorem ofW3Shift_nodup
    (hwallColumn : (shiftRows shrink hValid incoming incomingFD).wallColumn = wall)
    (root : target.V) (i : Fin 2) (row : coordinate) :
    (((ofW3Shift (wall := wall) shrink hValid hConnected hGenus incoming incomingFD
      hwallColumn root).family.presentation i).path row).Nodup :=
  A04MoreTags.nodup_labelling_path
    (W3ShiftStableIncidence.outgoingLabelling shrink hValid incoming incomingFD i) row

/-- The `w3Shift` family is honestly presented. -/
theorem ofW3Shift_honestlyPresented
    (hwallColumn : (shiftRows shrink hValid incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    RoutedWall.HonestlyPresented (ofW3Shift (wall := wall) shrink hValid hConnected
      hGenus incoming incomingFD hwallColumn root) :=
  fun i ↦ ⟨W3ShiftStableIncidence.outgoingLabelling shrink hValid incoming incomingFD i,
    rfl⟩

/-! ## 4.  The routed wall -/

/-- **`w3Shift` as a routed wall.**  The `w3Shift` counterpart of the routed
walls of `A04MoreTags`; nothing is carried but `hChart`. -/
noncomputable def routedW3Shift
    (hwallColumn : (shiftRows shrink hValid incoming incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart) :
    RoutedWall degree coordinate chart wall :=
  RoutedWall.ofHonestSupply
    (ofW3Shift (wall := wall) shrink hValid hConnected hGenus incoming incomingFD
      hwallColumn root)
    (w3ShiftSupply shrink hValid hConnected hGenus incoming incomingFD hwallColumn root)
    (ofW3Shift_honestlyPresented shrink hValid hConnected hGenus incoming incomingFD
      hwallColumn root)
    incoming
    (ofW3Shift_incomingNonzero shrink hValid hConnected hGenus incoming incomingFD
      hwallColumn root)
    (ofW3Shift_incomingMatrix shrink hValid hConnected hGenus incoming incomingFD
      hwallColumn root chart hChart)

/-! ### Where the incoming position comes from

`W3ShiftGraphTracking.exists_matched_tracking` (on
`W3ShiftIncomingMatching.exists_member_normalization`) says an arbitrary incoming
`w3Shift` cover **is** a named Figure 29 member of the pair carrying an honest
presentation in the original coordinates.  Its `index` is `hW25Incoming`, its
`fd` is the `incomingFD` above, its matrix clause is `hChart`, and its column
clause is literally

```
fd.labelling.targetEdge.symm
  (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
    (shiftMembers shrink index).right none)
  = fullDim.labelling.targetEdge.symm contracted
```

whose left-hand side is these rows' regrown column by `shiftRows_wallColumn`
below.  So `hwallColumn` is discharged by that clause the moment the march's
crossed coordinate is the original contracted column, and it is stated as a
hypothesis here for the same reason it is at every other tag: the identification
of the march's coordinate belongs to the march, not to the local case. -/

/-- The `w3Shift` rows' regrown column, read on the identified member's own
occurrence dictionary: transport to member `0` and back cancels, exactly as at
`w2P` (`A04MoreTags.ofW2P_family_wallColumn`) and `w2M11`
(`A04M11Wiring.m11Family_wallColumn`). -/
theorem shiftRows_wallColumn :
    (shiftRows shrink hValid incoming incomingFD).wallColumn =
      incomingFD.labelling.targetEdge.symm
        (occurrenceEquiv target wallVertex (shiftMembers shrink incoming).right none) := by
  show ((incomingFD.labelling.targetEdge.trans
      ((occurrenceEquiv target wallVertex (shiftMembers shrink incoming).right).symm.trans
        (occurrenceEquiv target wallVertex (shiftMembers shrink 0).right))).trans
      (occurrenceEquiv target wallVertex (shiftMembers shrink 0).right).symm).symm none = _
  refine (Equiv.symm_apply_eq _).mpr ?_
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

end DraismaVargas.LocalCases.A04ShiftWiring
