module

public import DraismaVargas.LocalCases.W3WallInput
public import DraismaVargas.LocalCases.W4PositiveExit

@[expose] public section

/-!
# The full-dimensional supply at a wall, for the tags with a stable-incidence dictionary

`WallProgress.presentedProgressOfWallInputs` assembles a
`SemanticAtlasMarch.State.PresentedProgress` from nine inputs.  The last two are the
outgoing full-dimensional presentations and the statement that they present
the outgoing members:

```
fullDim : ∀ wall (outgoing : Fin (input wall).case.arity),
  (matrix ((input wall).family.presentation outgoing)).det ≠ 0 →
  FullDimensionalSourcePresentation ((input wall).family.candidate outgoing).datum coordinate
hFullDim : ∀ wall outgoing hdet,
  (fullDim wall outgoing hdet).labelling.presentation =
    (input wall).family.presentation outgoing
```

Both are gated on the outgoing member's nonsingularity; the total form is
unsatisfiable (`W3WallInput.no_total_fullDim_of_singularFamily`).
`FullDimSupply` below is that pair for **one** wall input, and
`fullDimOfSupplies`/`fullDimPresentation_of_supplies` are the composite: a
supply at every wall is literally the two hypotheses, in the order and shape in
which `WallProgress.presentedProgressOfWallInputs` consumes them
(`presentedProgressOfSupplies`).

## What is supplied here, and what is not

Nothing below derives a `FullDimensionalSourcePresentation`.  Every inhabitant
is one `outgoingPresentation` per outgoing index, and every
`presentation_eq` is `rfl`, because in each case the wall input's family
carries the *honest* presentations
`(StableLengthMatrixLabelling.presentation ∘ outgoingLabelling)` that
`StableGraphFullDimensional.presentationOfEquivalence` transports.  That
coincidence is the whole content of this file, and it is exactly what fails
for the other two routes.

| tag | wall input | supply |
|---|---|---|
| `w3Nd2CoarseFine` | `W3WallInput.ofNd2CoarseFine` | `nd2Supply`, on `W3Nd2PositiveExit.outgoingPresentation` |
| `w3Nd3CoarseFine` | `W3WallInput.ofNd3CoarseFine` | `nd3Supply`, on `W3Nd3ArbitraryExit.outgoingPresentation` |
| `w4` | `ofFourValentHonest` (this file) | `w4Supply`, on `W4PositiveExit.outgoingPresentation` |
| `w2M11` | `A04M11Wiring.ofW2M11` (`WallInput.ofGauge`) | `A04M11Wiring.w2M11Supply` |
| `w3Shift` | `A04ShiftWiring.ofW3Shift` (`W3WallInput.ofShift`) | `A04ShiftWiring.w3ShiftSupply` |
| `w2R1` | `A04R1Wiring.ofW2R1` (`WallInput.ofTrivalent` on `W2R1GraphData.family`) | `A04R1Wiring.w2R1Supply` |
| `w3Four` | `W3WallInput.ofFour` (a gauge family) | `A04MoreTags.w3FourSupply` |

### `w4`: the wall input must be `ofTrivalent`, not `ofFourValent`

`WallProgress.WallInput.ofFourValent` builds its family from
`W4StableSource.AuxR0SourceInput.presentedFamily`, whose `presentation` field is
the **raw census path data** `oldPath`/`newSheets` -- certified neither to
survive nor to be the actual `StablePath` rows of the outgoing datum (see
`W4OutgoingSurvival`) -- reindexed by an arbitrary
`relabel : coordinate ≃ Option target.edges` that no hypothesis ties to the
incoming presentation. The *candidates* do match:
`W4OutgoingStableRows.member_eq` is `rfl`, so `fullDim` alone typechecks. What
cannot be produced is `presentation_eq`: the only identification available for
those raw presentations is `W4OutgoingLimitMatrix.presentedFamily_matrix_eq`, an
equality of **matrices**, and the field pair needs an equality of
`LengthMatrixPresentation`s (`targetEdge` *and* `path`).

`WallProgress.WallInput.ofTrivalent` is not restricted to trivalent tags -- its
`case` and the arity equation are parameters -- so the honest family
`W4CommonBalance.honestPresentedFamily`, already parametric in the ambient
coordinate and already presented by `W4CommonBalance.labelling`, goes through
it unreindexed.  `ofFourValentHonest` is that wall input; it carries
`case = SourceCase.w4` and its arity is `3`.

### `w2M11`: the type-level obstruction, and the gauge family that removes it

The family of case `{w2-r2-nd3-M-11}` (Figure 32 of Draisma--Vargas Part I)
cannot be carried by a `BalancedGlobal.PresentedFamily`.
`M11FullDimensional.outgoingPresentation` lands on
`M11RemoteCandidates.candidates input profile hCard`, which is
`GlobalM11Arbitrary.candidates … = ![first.certified, remoteCertified …, third.certified]`,
and its **middle member is not a `BalancedGlobal.Candidate target degree data
wallVertex` at all**: `GlobalM11Arbitrary.remoteCertified` is a
`CertifiedCandidate data` assembled from a `SplitPattern` over the *swapped*
datum `GlobalM11Arbitrary.SwappedDatum data wall root hRoot distinguished other
hTogether`, with `valid_of_old` routed through
`wallBranchSwap_preserves_valid`.  `BalancedGlobal.PresentedFamily.candidate`
fixes one datum, so no `PresentedFamily` can carry the M11 family in the
coordinates `M11FullDimensional` works in.

`BalancedGlobal.GaugeFamily` removes the obstruction.  It has a per-member
`base : Fin n → GluingDatum target degree` and its own `valid_of_old`;
`WallProgress.WallInput.family` and `SemanticAtlasMarch.State.PresentedProgress.familyAt`
carry it, and `WallProgress.WallInput.ofGauge` is the constructor
(`W3WallInput.ofFour` uses it for Figure 28's four gauge copies).  What each
divalent tag needs is its family in gauge form, with the presentations kept
(`M11CommonBalance.family` is a `BalancedGlobal.Family`, which forgets them):

* `w2M11`: `M11HonestGaugeFamily.gaugeFamily`, assembled from
  `GlobalM11Arbitrary.SwappedDatum` and `wallBranchSwap_preserves_valid` with
  the three `M11CommonBalance` labellings, and wired by `A04M11Wiring`;
* `w2M1k`: `W2M1kGaugeFamily.alignedGaugeFamily`/`separatedGaugeFamily`, wired
  by `A04M1kWiring`;
* `w2Mkk`: `W2MkkArbitraryExit.firstGaugeFamily`, wired by
  `A04MoreTags.mkkFirstSupply`.
-/

namespace DraismaVargas.LocalCases.A04FourTags

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.ClassifiedContinuation
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.ThirdEquation
open DraismaVargas.LocalCases.W3R1SourceProfile
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W4TargetPairings
open DraismaVargas.LocalCases.WallProgress

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {degree : ℕ} {wall : coordinate}

/-! ## 1.  The pair, at one wall -/

/-- **The full-dimensional supply at one wall.**  Exactly the two gated fields
of `SemanticAtlasMarch.State.PresentedProgress` that the wall input does not
determine, read at one `WallProgress.WallInput`: an outgoing full-dimensional
presentation at every nonsingular member of the wall's family, and the statement
that it presents that member. -/
structure FullDimSupply (input : WallInput degree coordinate wall) where
  /-- The outgoing full-dimensional presentation, gated on nonsingularity. -/
  fullDim : ∀ outgoing : Fin input.case.arity,
    (GluingDatum.LengthMatrixPresentation.matrix
      (input.family.presentation outgoing)).det ≠ 0 →
    FullDimensionalSourcePresentation (input.family.candidate outgoing).datum coordinate
  /-- It is a presentation *of that member*. -/
  presentation_eq : ∀ (outgoing : Fin input.case.arity)
    (hdet : (GluingDatum.LengthMatrixPresentation.matrix
      (input.family.presentation outgoing)).det ≠ 0),
    (fullDim outgoing hdet).labelling.presentation = input.family.presentation outgoing

namespace FullDimSupply

/-- A supply is the existential form `W3WallInput.presentedProgress_fullDim_gated`
reads off a `PresentedProgress`, so the two shapes agree. -/
theorem exists_fullDim {input : WallInput degree coordinate wall}
    (supply : FullDimSupply input) (outgoing : Fin input.case.arity)
    (hdet : (GluingDatum.LengthMatrixPresentation.matrix
      (input.family.presentation outgoing)).det ≠ 0) :
    ∃ fd : FullDimensionalSourcePresentation
        (input.family.candidate outgoing).datum coordinate,
      fd.labelling.presentation = input.family.presentation outgoing :=
  ⟨supply.fullDim outgoing hdet, supply.presentation_eq outgoing hdet⟩

/-- **A supply forces its own family nonsingular where it is defined.**  The
converse direction of `W3WallInput.fullDim_forces_det_ne_zero`: the gate is not
decoration, it is the only reason the pair is satisfiable. -/
theorem det_ne_zero_of_fullDim {input : WallInput degree coordinate wall}
    (supply : FullDimSupply input) (outgoing : Fin input.case.arity)
    (hdet : (GluingDatum.LengthMatrixPresentation.matrix
      (input.family.presentation outgoing)).det ≠ 0) :
    (GluingDatum.LengthMatrixPresentation.matrix
      ((supply.fullDim outgoing hdet).labelling.presentation)).det ≠ 0 :=
  (supply.fullDim outgoing hdet).det_ne_zero

end FullDimSupply

/-! ## 2.  `w3Nd2CoarseFine`

The wall input is `W3WallInput.ofNd2CoarseFine` at the initial labelling
`W3Nd2PositiveExit.initialLabelling` induced by one identified member's own
full-dimensional presentation — the same instantiation
`W3WallInput.nd2_exists_fullDim` makes.  Its family is `W3WallInput.nd2Family`,
whose presentations are `W3Nd2CommonBalance.labelling`'s, which is what
`W3Nd2PositiveExit.outgoingPresentation` is built on; so both fields are
literal. -/

section Nd2

variable {target : CFGraph.{0}} {wallVertex : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wallVertex}
  (input : W3SourceInput data star)
  (profile : Nd2Profile data input.distinguishedBlock)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (incoming : Fin 2)
  (incomingFD : FullDimensionalSourcePresentation
    (W3Nd2CommonBalance.candidates input profile incoming).datum coordinate)

/-- Equation (5)'s outgoing presentations, one `W3Nd2PositiveExit.outgoingPresentation`
per member. -/
noncomputable def nd2FullDim : ∀ outgoing : Fin 2,
    (GluingDatum.LengthMatrixPresentation.matrix
      ((W3WallInput.nd2Family input profile
        (W3Nd2PositiveExit.initialLabelling input profile incoming
          incomingFD)).presentation outgoing)).det ≠ 0 →
    FullDimensionalSourcePresentation
      ((W3WallInput.nd2Family input profile
        (W3Nd2PositiveExit.initialLabelling input profile incoming
          incomingFD)).candidate outgoing).datum coordinate
  | 0 => fun hdet ↦ W3Nd2PositiveExit.outgoingPresentation input profile hConnected
      hGenus incoming 0 incomingFD hdet
  | 1 => fun hdet ↦ W3Nd2PositiveExit.outgoingPresentation input profile hConnected
      hGenus incoming 1 incomingFD hdet

/-- **The supply for `w3Nd2CoarseFine`.**  On exactly the hypotheses
`W3WallInput.ofNd2CoarseFine` and `W3Nd2PositiveExit.outgoingPresentation`
already take. -/
noncomputable def nd2Supply
    (hwallColumn : W3Nd2CommonBalance.wallColumn input profile
      (W3Nd2PositiveExit.initialLabelling input profile incoming incomingFD) = wall)
    (root : target.V) :
    FullDimSupply (W3WallInput.ofNd2CoarseFine (wall := wall) input profile
      (W3Nd2PositiveExit.initialLabelling input profile incoming incomingFD)
      hwallColumn hConnected hGenus root) where
  fullDim := nd2FullDim input profile hConnected hGenus incoming incomingFD
  presentation_eq := by
    intro outgoing hdet
    fin_cases outgoing <;> rfl

end Nd2

/-! ## 3.  `w3Nd3CoarseFine`

Identical in shape, over `W3Nd3CommonBalance.honestPresentedFamily` and
`W3Nd3ArbitraryExit.outgoingPresentation`. -/

section Nd3

variable {target : CFGraph.{0}} {wallVertex : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wallVertex}
  (input : W3SourceInput data star)
  (profile : Nd3Profile data input.distinguishedBlock)
  (hSame : profile.first.1.1.1 = profile.second.1.1.1)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (incoming : Fin 2)
  (incomingFD : FullDimensionalSourcePresentation
    (W3Nd3CommonBalance.candidates input profile hSame incoming).datum coordinate)

/-- Equation (4)'s outgoing presentations. -/
noncomputable def nd3FullDim : ∀ outgoing : Fin 2,
    (GluingDatum.LengthMatrixPresentation.matrix
      ((W3Nd3CommonBalance.honestPresentedFamily input profile hSame
        (W3Nd3ArbitraryExit.initialLabelling input profile hSame incoming
          incomingFD)).presentation outgoing)).det ≠ 0 →
    FullDimensionalSourcePresentation
      ((W3Nd3CommonBalance.honestPresentedFamily input profile hSame
        (W3Nd3ArbitraryExit.initialLabelling input profile hSame incoming
          incomingFD)).candidate outgoing).datum coordinate
  | 0 => fun hdet ↦ W3Nd3ArbitraryExit.outgoingPresentation input profile hSame
      hConnected hGenus incoming 0 incomingFD hdet
  | 1 => fun hdet ↦ W3Nd3ArbitraryExit.outgoingPresentation input profile hSame
      hConnected hGenus incoming 1 incomingFD hdet

/-- **The supply for `w3Nd3CoarseFine`.** -/
noncomputable def nd3Supply
    (hwallColumn : W3Nd3CommonBalance.wallColumn input profile hSame
      (W3Nd3ArbitraryExit.initialLabelling input profile hSame incoming incomingFD) = wall)
    (root : target.V) :
    FullDimSupply (W3WallInput.ofNd3CoarseFine (wall := wall) input profile hSame
      (W3Nd3ArbitraryExit.initialLabelling input profile hSame incoming incomingFD)
      hwallColumn hConnected hGenus root) where
  fullDim := nd3FullDim input profile hSame hConnected hGenus incoming incomingFD
  presentation_eq := by
    intro outgoing hdet
    fin_cases outgoing <;> rfl

end Nd3

/-! ## 4.  `w4`, through the honest family

See the header for why no supply can be built on
`WallProgress.WallInput.ofFourValent`. `ofFourValentHonest` is the `w4` wall
input built from the honest family the W4 exit actually uses; it differs from
`ofFourValent` only in which presentations the family carries, and it needs no
reindexing because `W4CommonBalance.honestPresentedFamily` is already parametric
in the ambient coordinate. -/

section W4

variable {target : CFGraph.{0}} {wallVertex : target.V} [DecidableEq target.edges]
  {data : GluingDatum target degree} {star : FourStar target wallVertex}
  (source : AuxR0SourceInput data star)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (incoming : Fin 3)
  (incomingFD : FullDimensionalSourcePresentation
    (W4OutgoingStableRows.member source incoming).datum coordinate)

/-- **The four-valent wall input in the identified member's own coordinates.**
`W4CommonBalance.honestPresentedFamily` at `W4PositiveExit.initialLabelling`,
through the generic `WallInput.ofTrivalent` at `case := SourceCase.w4`; the
regrown column is `W4PositiveExit.wallColumn`. -/
noncomputable def ofFourValentHonest
    (hwallColumn : W4PositiveExit.wallColumn source incoming incomingFD = wall)
    (root : target.V) :
    WallInput degree coordinate wall :=
  WallInput.ofTrivalent
    (W4CommonBalance.honestPresentedFamily source
      (W4PositiveExit.initialLabelling source incoming incomingFD))
    source.valid SourceCase.w4 rfl hwallColumn hConnected hGenus root

@[simp] theorem ofFourValentHonest_case
    (hwallColumn : W4PositiveExit.wallColumn source incoming incomingFD = wall)
    (root : target.V) :
    (ofFourValentHonest (wall := wall) source hConnected hGenus incoming incomingFD
      hwallColumn root).case = SourceCase.w4 := rfl

/-- Equation (1)'s outgoing presentations, one
`W4PositiveExit.outgoingPresentation` per member. -/
noncomputable def w4FullDim : ∀ outgoing : Fin 3,
    (GluingDatum.LengthMatrixPresentation.matrix
      ((W4CommonBalance.honestPresentedFamily source
        (W4PositiveExit.initialLabelling source incoming
          incomingFD)).presentation outgoing)).det ≠ 0 →
    FullDimensionalSourcePresentation
      ((W4CommonBalance.honestPresentedFamily source
        (W4PositiveExit.initialLabelling source incoming
          incomingFD)).candidate outgoing).datum coordinate
  | 0 => fun hdet ↦ W4PositiveExit.outgoingPresentation source incoming incomingFD
      hConnected hGenus 0 hdet
  | 1 => fun hdet ↦ W4PositiveExit.outgoingPresentation source incoming incomingFD
      hConnected hGenus 1 hdet
  | 2 => fun hdet ↦ W4PositiveExit.outgoingPresentation source incoming incomingFD
      hConnected hGenus 2 hdet

/-- **The supply for `w4`.**  On exactly the hypotheses
`W4PositiveExit.outgoingPresentation` already takes. -/
noncomputable def w4Supply
    (hwallColumn : W4PositiveExit.wallColumn source incoming incomingFD = wall)
    (root : target.V) :
    FullDimSupply (ofFourValentHonest (wall := wall) source hConnected hGenus incoming
      incomingFD hwallColumn root) where
  fullDim := w4FullDim source hConnected hGenus incoming incomingFD
  presentation_eq := by
    intro outgoing hdet
    fin_cases outgoing <;> rfl

end W4

/-! ## 5.  The composite, in the shape the dispatcher consumes

`fullDimOfSupplies` and `fullDimPresentation_of_supplies` are literally the
arguments `fullDim` and `hFullDim` of
`WallProgress.presentedProgressOfWallInputs`, and
`presentedProgressOfSupplies` is the check that the dispatcher accepts them in
that form. -/

section Composite

open DraismaVargas.Infrastructure.RationalAffineWall
open DraismaVargas.LocalCases.SemanticAtlasMarch

variable {baseStart baseFinish : coordinate → ℚ}

/-- **The `fullDim` argument from a supply at every wall.** -/
noncomputable def fullDimOfSupplies {Guard : coordinate → Prop}
    (hW25 : ∀ wall : coordinate, Guard wall → WallInput degree coordinate wall)
    (supply : ∀ (wall : coordinate) (hw : Guard wall),
      FullDimSupply (hW25 wall hw)) :
    ∀ (wall : coordinate) (hw : Guard wall)
      (outgoing : Fin (hW25 wall hw).case.arity),
      (GluingDatum.LengthMatrixPresentation.matrix
        ((hW25 wall hw).family.presentation outgoing)).det ≠ 0 →
      FullDimensionalSourcePresentation
        ((hW25 wall hw).family.candidate outgoing).datum coordinate :=
  fun wall hw outgoing hdet ↦ (supply wall hw).fullDim outgoing hdet

/-- **The `hFullDim` argument from the same supply.** -/
theorem fullDimPresentation_of_supplies {Guard : coordinate → Prop}
    (hW25 : ∀ wall : coordinate, Guard wall → WallInput degree coordinate wall)
    (supply : ∀ (wall : coordinate) (hw : Guard wall),
      FullDimSupply (hW25 wall hw)) :
    ∀ (wall : coordinate) (hw : Guard wall)
      (outgoing : Fin (hW25 wall hw).case.arity)
      (hdet : (GluingDatum.LengthMatrixPresentation.matrix
        ((hW25 wall hw).family.presentation outgoing)).det ≠ 0),
      (fullDimOfSupplies hW25 supply wall hw outgoing hdet).labelling.presentation =
        (hW25 wall hw).family.presentation outgoing :=
  fun wall hw outgoing hdet ↦ (supply wall hw).presentation_eq outgoing hdet

/-- **The dispatcher accepts the pair.**  This is
`WallProgress.presentedProgressOfWallInputs` with its last two arguments
discharged by supplies; the other seven are the current state, the wall
dispatcher `hW25` with its row condition `hW25Nodup`, the genericity hypothesis
`hA02Generic` (simple negative crossings), and the state–classifier
compatibility triple `hW25Incoming`, `hW25IncomingNonzero`,
`hW25IncomingMatrix`, unchanged. Every wall-indexed input is asked only at a
first wall of the state's segment (`SemanticAtlasMarch.IsFirstWall`, carried as
`hw`). -/
noncomputable def presentedProgressOfSupplies
    (current : State degree (atlasChartMatrix coordinate degree) baseStart baseFinish)
    (hW25 : ∀ wall : coordinate, current.FirstWall wall →
      WallInput degree coordinate wall)
    (supply : ∀ (wall : coordinate) (hw : current.FirstWall wall),
      FullDimSupply (hW25 wall hw))
    (hW25Nodup : ∀ (wall : coordinate) (hw : current.FirstWall wall)
      (i : Fin (hW25 wall hw).case.arity) row,
      (((hW25 wall hw).family.presentation i).path row).Nodup)
    (hA02Generic : SimpleNegativeCrossings current.toMatrixState.currentStart
      current.toMatrixState.currentFinish)
    (hW25Incoming : ∀ (wall : coordinate) (hw : current.FirstWall wall),
      Fin (hW25 wall hw).case.arity)
    (hW25IncomingNonzero : ∀ (wall : coordinate) (hw : current.FirstWall wall),
      (GluingDatum.LengthMatrixPresentation.matrix
        ((hW25 wall hw).family.presentation (hW25Incoming wall hw))).det ≠ 0)
    (hW25IncomingMatrix : ∀ (wall : coordinate) (hw : current.FirstWall wall),
      GluingDatum.LengthMatrixPresentation.matrix
          ((hW25 wall hw).family.presentation (hW25Incoming wall hw)) =
        atlasChartMatrix coordinate degree current.toMatrixState.label) :
    current.PresentedProgress :=
  presentedProgressOfWallInputs current hW25 hW25Nodup hA02Generic hW25Incoming
    hW25IncomingNonzero hW25IncomingMatrix (fullDimOfSupplies hW25 supply)
    (fullDimPresentation_of_supplies hW25 supply)

end Composite

end DraismaVargas.LocalCases.A04FourTags
