import DraismaVargas.LocalCases.TrackedState
import DraismaVargas.LocalCases.A04MoreTags
import DraismaVargas.LocalCases.A04ShiftWiring
import DraismaVargas.LocalCases.A04M11Wiring
import DraismaVargas.LocalCases.A04R1Wiring
import DraismaVargas.LocalCases.W2M11GraphTracking
import DraismaVargas.LocalCases.W2PGraphTracking
import DraismaVargas.LocalCases.W2R1GraphTracking
import DraismaVargas.LocalCases.W3Nd2GraphTracking
import DraismaVargas.LocalCases.W3Nd3GraphTracking

/-!
# Wiring the tracked successor into the tracked march

Source: Vargas, Part II (arXiv:2609.09109), §4.3--§4.4 (wall crossing, and the
outer sequence of cone marches and type changes in the proofs of the main
theorems), read against the Part I atlas march of `SemanticAtlasMarch`, its
per-wall dispatcher `WallProgress` and the routing layer `A04FourTags` /
`A04MoreTags` that supplies the full-dimensional presentations at each wall.

`TrackedProgress.tracksAt` (in `TrackedState`) asks for an
`InteriorGraphTracking.Tracks` of the ambient row-labelled graph **at the very
witness** `SemanticAtlasMarch.State.PresentedProgress.fullDimAt wall outgoing
hdet`, while a tracked certified exit (`W3ShiftGraphTracking.TrackedCertifiedExit`)
hands its outgoing full-dimensional presentation over inside an existential
binder, where it is not named as `(familyAt wall).candidate outgoing`.  This
file bridges the two without trying to identify two existential witnesses after
the fact.  It observes instead that

* `fullDimAt`/`fullDimPresentation` are *supplied*, not derived: they are the
  full-dimensional supply, carried by `A04FourTags.FullDimSupply` and packaged
  per wall by `A04MoreTags.RoutedWall`; and
* every supply builds its `fullDim` as
  `StableGraphFullDimensional.presentationOfEquivalence` along a
  member-to-member incidence `StableGraphIncidence.Equivalence`, whose row
  formula is exactly the hypothesis `InteriorGraphTracking.throughIncidence`
  consumes.

So the tracking travels from one incoming cover to *every* nonsingular member of
the wall's family along the same actual incidence equivalence the
full-dimensional package is transported along.  No matrix-level identification
is used anywhere, and no candidate or base stage is replaced.

## What is proved here

* `TrackedRoutedWall`: an `A04MoreTags.RoutedWall` together with one `Tracks` at
  each of its supply's gated full-dimensional presentations.  Nothing else is
  added, so the untracked route is the `toRoutedWall` projection verbatim.
* `TrackedRoutedWall.ofIncidence`: the uniform mechanism.  One incoming tracking,
  a per-member incidence equivalence and the per-member row formula give all the
  trackings.
* `trackedProgressOfRoutedWalls`: a `TrackedRoutedWall` at every coordinate plus
  the genericity hypothesis (simple negative crossings) is a `TrackedProgress`,
  whose underlying presented progress is literally
  `A04MoreTags.presentedProgressOfRoutedWalls` of the underlying routed walls.
* `exists_step_of_trackedRoutedWalls`, `exists_terminal_of_trackedProgress`,
  `exists_terminal_tracked_caterpillar` and
  `exists_terminal_tracked_caterpillar_of_routedWalls`: the composite from the
  tracked caterpillar seed `TrackedState.caterpillarGeneric` to a terminal
  tracked state, the last one stated directly on tracked routed walls.
* `trackedW4`, `trackedW3Shift`, `trackedNd2`, `trackedNd3`, `trackedW2M11`,
  `trackedW2P`, `trackedW2R1`: seven of the ten tags -- Equation (1), Figure 29,
  Figure 31, Figure 30, Figure 32, Figure 35 and Equation (10) -- as actual
  `TrackedRoutedWall`s, on exactly the hypotheses their `routed*` constructors
  already take plus one incoming tracking.  These are the non-vacuity witnesses
  of the structure.
* `trackedPencil_of_certifiedExit`: a `TrackedCertifiedExit` *is* a tracked
  march payload on the far side of the wall: its retained base target, base
  datum, wall and actual `BalancedGlobal.Candidate` are kept, its cleared-pencil
  data are literally the fields of `BalancedGlobal.Candidate.ClearedPencil`, and
  `TrackedPencil.of_tracks` assembles them, deriving the genus conjunct from the
  tracking.

## What is NOT proved here

No family geometry, determinant balance, positive exit, census or graph
identification is re-derived; every producer is consumed verbatim.

`TrackedProgress` is conditional: a `PresentedProgress` has no unconditional
inhabitant, so a `TrackedRoutedWall` at *every* coordinate is a hypothesis
here, and each routed wall carries its own
`incoming`/`incomingNonzero`/`incomingMatrix` triple, as in `A04MoreTags`.
`2 ≤ degree` is explicit wherever a successor payload is rebuilt, because that
is what `TrackedPencil.of_tracks` uses.

The other three tags are made tracked routed walls in `TrackedWallProgressMore`.
`w2M1k` and `w2Mkk` prove their row formula
(`W2M1kGraphTracking.labelling_row`, `W2MkkGraphTracking.labelling_row`) only
under an extra `hDictionaryRow` receipt about the `LimitColumns` dictionary --
`∀ p, (dictionary p).row = (limit.member p).row` -- which
`TrackedWallProgressMore.alignedDictionary_row`, `separatedDictionary_row`,
`mkkFirstDictionary_row` and `mkkSecondDictionary_row` supply for the supplies'
own dictionaries (`fin_cases … <;> rfl`, remote slot included).  `w3Four` has
a member-to-member incidence row formula, `W3TrackedExit.outgoingLabelling_row`,
on `W3TrackedAnchoring.RowsCompatible` and the sixteen ordered certificates of
`W3FourRegrownColumnSeam.MemberCertificates`;
`TrackedWallProgressMore.trackedW3Four` uses it.

Consumers: the outer walk of Part II, §4.4, through
`TrackedState.exists_terminal_reachable_of_tracked_progress` and
`TrackedPencil.exists_chain_to_core` at the terminal tracked state.
-/

namespace DraismaVargas.LocalCases.TrackedWallProgress

open Utilities
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.Infrastructure.RationalAffineWall
open DraismaVargas.LocalCases.A04MoreTags
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.WallProgress

/-! ## 1.  The tracked routed wall -/

section Wall

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

/-- **What a tracked local classification owes at one coordinate.**  Exactly an
`A04MoreTags.RoutedWall` -- the dispatcher's wall input, the gated
full-dimensional supply on it, duplicate-free rows and the state--classifier
triple -- together with one actual `InteriorGraphTracking.Tracks` of the ambient
row-labelled graph at each of that supply's presentations.

The tracking is asked at `supply.fullDim outgoing hdet`, the witness the march
reads, not at another presentation of the same matrix: a matrix does not
determine its candidate. -/
structure TrackedRoutedWall (degree : ℕ) (coordinate : Type) [Fintype coordinate]
    [DecidableEq coordinate] (chart : Matrix coordinate coordinate ℚ)
    (wall : coordinate) {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V]
    [DecidableEq V] (graph : CubicDartGraph D V) (label : D → coordinate) where
  /-- The untracked routed wall, unchanged. -/
  toRoutedWall : RoutedWall degree coordinate chart wall
  /-- The ambient graph is tracked by the supply's own outgoing presentation,
  member by member, gated on the same nonsingularity. -/
  tracks : ∀ (outgoing : Fin toRoutedWall.input.case.arity)
    (hdet : (GluingDatum.LengthMatrixPresentation.matrix
      (toRoutedWall.input.family.presentation outgoing)).det ≠ 0),
    Nonempty (Tracks (toRoutedWall.supply.fullDim outgoing hdet) graph label)

namespace TrackedRoutedWall

variable {degree : ℕ} {chart : Matrix coordinate coordinate ℚ} {wall : coordinate}
  {graph : CubicDartGraph D V} {label : D → coordinate}

/-- **The uniform mechanism.**  One tracking at one full-dimensional cover, a
member-to-member incidence equivalence for every member of the wall's family and
the row formula those equivalences satisfy give a tracking at every nonsingular
member.

Nothing is identified by matrices: each tracking travels along the actual
incidence equivalence, which is the same one
`StableGraphFullDimensional.presentationOfEquivalence` transports the
full-dimensional package along inside `A04FourTags.FullDimSupply`. -/
noncomputable def ofIncidence {source : CFGraph} {sourceDegree : ℕ}
    {incomingDatum : GluingDatum source sourceDegree}
    (routed : RoutedWall degree coordinate chart wall)
    (incomingFD : FullDimensionalSourcePresentation incomingDatum coordinate)
    (current : Tracks incomingFD graph label)
    (between : ∀ outgoing : Fin routed.input.case.arity,
      StableGraphIncidence.Equivalence incomingDatum
        (routed.input.family.candidate outgoing).datum)
    (hRow : ∀ (outgoing : Fin routed.input.case.arity)
      (hdet : (GluingDatum.LengthMatrixPresentation.matrix
        (routed.input.family.presentation outgoing)).det ≠ 0),
      (routed.supply.fullDim outgoing hdet).labelling.row =
        (between outgoing).row.symm.trans incomingFD.labelling.row) :
    TrackedRoutedWall degree coordinate chart wall graph label where
  toRoutedWall := routed
  tracks := fun outgoing hdet ↦
    ⟨throughIncidence current (routed.supply.fullDim outgoing hdet) (between outgoing)
      (hRow outgoing hdet)⟩

@[simp] theorem ofIncidence_toRoutedWall {source : CFGraph} {sourceDegree : ℕ}
    {incomingDatum : GluingDatum source sourceDegree}
    (routed : RoutedWall degree coordinate chart wall)
    (incomingFD : FullDimensionalSourcePresentation incomingDatum coordinate)
    (current : Tracks incomingFD graph label)
    (between : ∀ outgoing : Fin routed.input.case.arity,
      StableGraphIncidence.Equivalence incomingDatum
        (routed.input.family.candidate outgoing).datum)
    (hRow : ∀ (outgoing : Fin routed.input.case.arity)
      (hdet : (GluingDatum.LengthMatrixPresentation.matrix
        (routed.input.family.presentation outgoing)).det ≠ 0),
      (routed.supply.fullDim outgoing hdet).labelling.row =
        (between outgoing).row.symm.trans incomingFD.labelling.row) :
    (ofIncidence routed incomingFD current between hRow).toRoutedWall = routed := rfl

end TrackedRoutedWall

end Wall

/-! ## 2.  The tracked progress package -/

section Progress

open DraismaVargas.LocalCases.SemanticAtlasMarch

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  {baseStart baseFinish : coordinate → ℚ}

/-- **The assembly.**  A `TrackedRoutedWall` at every coordinate and the
genericity hypothesis (simple negative crossings) produce a `TrackedProgress`.

Its `toPresentedProgress` is `A04MoreTags.presentedProgressOfRoutedWalls` of the
underlying routed walls -- the same term the untracked march uses -- so
`tracksAt` is asked at literally each wall's `supply.fullDim`, and is that
wall's `tracks`. -/
noncomputable def trackedProgressOfRoutedWalls
    (current : TrackedState degree graph label
      (atlasChartMatrix coordinate degree) baseStart baseFinish)
    (routed : ∀ (wall : coordinate), current.toSemanticState.FirstWall wall →
      TrackedRoutedWall degree coordinate
        (atlasChartMatrix coordinate degree current.toMatrixState.label) wall graph label)
    (hA02Generic : SimpleNegativeCrossings current.toMatrixState.currentStart
      current.toMatrixState.currentFinish) :
    TrackedProgress current :=
  TrackedProgress.ofPresented
    (presentedProgressOfRoutedWalls current.toSemanticState
      (fun wall hw ↦ (routed wall hw).toRoutedWall) hA02Generic)
    (fun wall hw outgoing hdet ↦ (routed wall hw).tracks outgoing hdet)

/-- **The tracked step.**  Every nonterminal tracked state with a
`TrackedRoutedWall` at every coordinate has a tracked successor: the ambient
row-labelled graph, its labels and the source genus survive the crossing, on the
actual candidate the classifier selects. -/
theorem exists_step_of_trackedRoutedWalls (hDegree : 2 ≤ degree)
    (current : TrackedState degree graph label
      (atlasChartMatrix coordinate degree) baseStart baseFinish)
    (routed : ∀ (wall : coordinate), current.toSemanticState.FirstWall wall →
      TrackedRoutedWall degree coordinate
        (atlasChartMatrix coordinate degree current.toMatrixState.label) wall graph label)
    (hA02Generic : SimpleNegativeCrossings current.toMatrixState.currentStart
      current.toMatrixState.currentFinish)
    (hNonterminal : ¬ TrackedState.Terminal current) :
    ∃ next : TrackedState degree graph label
      (atlasChartMatrix coordinate degree) baseStart baseFinish,
      TrackedState.Step current next :=
  (trackedProgressOfRoutedWalls current routed hA02Generic).exists_step hDegree
    (fun l ↦ atlasChartMatrix_det_ne_zero l) hNonterminal

/-- **Tracked global termination in the universal atlas.**  This is
`TrackedState.exists_terminal_reachable_of_tracked_progress` with the atlas's own
nonsingularity projection supplied, so the only other input is one
`TrackedProgress` per nonterminal state -- which
`trackedProgressOfRoutedWalls` builds. -/
theorem exists_terminal_of_trackedProgress (hDegree : 2 ≤ degree)
    (localProgress : ∀ current : TrackedState degree graph label
        (atlasChartMatrix coordinate degree) baseStart baseFinish,
      ¬ TrackedState.Terminal current → TrackedProgress current)
    (initial : TrackedState degree graph label
      (atlasChartMatrix coordinate degree) baseStart baseFinish) :
    ∃ final, Relation.ReflTransGen TrackedState.Step initial final ∧
      TrackedState.Terminal final ∧
      TrackedPencil degree graph label
        (atlasChartMatrix coordinate degree final.toMatrixState.label)
        final.toMatrixState.currentStart ∧
      SemanticAtlasMarch.CarriesClearedFace degree
        (atlasChartMatrix coordinate degree final.toMatrixState.label)
        final.toMatrixState.currentFinish ∧
      ∃ source : CFGraph.{0}, BNExists source 1 degree :=
  TrackedState.exists_terminal_reachable_of_tracked_progress hDegree
    (fun l ↦ atlasChartMatrix_det_ne_zero l) localProgress initial

end Progress

/-! ## 3.  Seven of the ten tags -/

section Tags

open DraismaVargas.LocalCases.ThirdEquation
open DraismaVargas.LocalCases.W3R1SourceProfile
open DraismaVargas.LocalCases.W4TargetPairings
open DraismaVargas.LocalCases.W4OutgoingStableRows

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {wall : coordinate} {graph : CubicDartGraph D V}
  {label : D → coordinate}
  {target : CFGraph.{0}} {wallVertex : target.V}
  {data : GluingDatum target degree}

/-! ### Equation (1), the `w4` tag: the interior four-valent crossing -/

section W4

variable [DecidableEq target.edges] {star : FourStar target wallVertex}
  (source : W4StableSource.AuxR0SourceInput data star)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (incoming : Fin 3)
  (incomingFD : FullDimensionalSourcePresentation
    (member source incoming).datum coordinate)

/-- Equation (1)'s member-to-member incidence equivalences, read on the routed
wall's own family slots.  These are `W4PositiveExit.between`, the very
equivalences `A04FourTags.w4FullDim` transports along. -/
noncomputable def w4Between :
    ∀ outgoing : Fin 3,
      StableGraphIncidence.Equivalence (member source incoming).datum
        ((W4CommonBalance.honestPresentedFamily source
          (W4PositiveExit.initialLabelling source incoming
            incomingFD)).candidate outgoing).datum
  | 0 => W4PositiveExit.between source incoming 0
  | 1 => W4PositiveExit.between source incoming 1
  | 2 => W4PositiveExit.between source incoming 2

/-- **The row formula for Equation (1)**,
`InteriorGraphTracking.outgoingLabelling_row`, read at the full-dimensional
supply. -/
theorem w4FullDim_row :
    ∀ (outgoing : Fin 3)
      (hdet : (GluingDatum.LengthMatrixPresentation.matrix
        ((W4CommonBalance.honestPresentedFamily source
          (W4PositiveExit.initialLabelling source incoming
            incomingFD)).presentation outgoing)).det ≠ 0),
      (A04FourTags.w4FullDim source hConnected hGenus incoming incomingFD outgoing
        hdet).labelling.row =
        (w4Between source incoming incomingFD outgoing).row.symm.trans
          incomingFD.labelling.row
  | 0, _ => outgoingLabelling_row source incoming incomingFD 0
  | 1, _ => outgoingLabelling_row source incoming incomingFD 1
  | 2, _ => outgoingLabelling_row source incoming incomingFD 2

/-- **Equation (1) as a tracked routed wall.**  The identified incoming member's
own tracking is carried to all three members of the four-valent family along
`W4PositiveExit.between`. -/
noncomputable def trackedW4
    (hwallColumn : W4PositiveExit.wallColumn source incoming incomingFD = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ) (position : Fin 3)
    (hNonzero : (GluingDatum.LengthMatrixPresentation.matrix
      ((A04FourTags.ofFourValentHonest (wall := wall) source hConnected hGenus incoming
        incomingFD hwallColumn root).family.presentation position)).det ≠ 0)
    (hMatrix : GluingDatum.LengthMatrixPresentation.matrix
      ((A04FourTags.ofFourValentHonest (wall := wall) source hConnected hGenus incoming
        incomingFD hwallColumn root).family.presentation position) = chart)
    (current : Tracks incomingFD graph label) :
    TrackedRoutedWall degree coordinate chart wall graph label :=
  TrackedRoutedWall.ofIncidence
    (routedW4 (wall := wall) source hConnected hGenus incoming incomingFD hwallColumn
      root chart position hNonzero hMatrix)
    incomingFD current (w4Between source incoming incomingFD)
    (w4FullDim_row source hConnected hGenus incoming incomingFD)

end W4

/-! ### Figure 29, the `w3Shift` tag -/

section Shift

open DraismaVargas.LocalCases.A04ShiftWiring
open DraismaVargas.LocalCases.W3ShiftSourceCandidates
open DraismaVargas.LocalCases.W3ShiftLimitRows (shiftMembers)

variable {star : ThreeStar target wallVertex} {input : W3SourceInput data star}
  {shift : ShiftProfile input} (shrink : ShrinkData shift) (hValid : data.Valid)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (incoming : Fin 2)
  (incomingFD : FullDimensionalSourcePresentation
    (shiftMembers shrink incoming).datum coordinate)

/-- **Figure 29 as a tracked routed wall.**  `A04ShiftWiring.shiftFullDim` is
uniform in the member, and `W3ShiftGraphTracking.outgoingLabelling_row` is its
row formula at `W3ShiftGraphData.between`. -/
noncomputable def trackedW3Shift
    (hwallColumn : (shiftRows shrink hValid incoming incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart)
    (current : Tracks incomingFD graph label) :
    TrackedRoutedWall degree coordinate chart wall graph label :=
  TrackedRoutedWall.ofIncidence
    (routedW3Shift (wall := wall) shrink hValid hConnected hGenus incoming incomingFD
      hwallColumn root chart hChart)
    incomingFD current
    (fun outgoing ↦ W3ShiftGraphData.between shrink hValid incoming outgoing)
    (fun outgoing _ ↦ W3ShiftGraphTracking.outgoingLabelling_row shrink hValid incoming
      incomingFD outgoing)

end Shift

/-! ### Figure 31, the `w3Nd2CoarseFine` tag -/

section Nd2

variable {star : ThreeStar target wallVertex} (input : W3SourceInput data star)
  (profile : Nd2Profile data input.distinguishedBlock)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (incoming : Fin 2)
  (incomingFD : FullDimensionalSourcePresentation
    (W3Nd2CommonBalance.candidates input profile incoming).datum coordinate)

/-- Figure 31's member-to-member incidence equivalences, read on the routed
wall's own family slots: `W3Nd2PositiveExit.between`. -/
noncomputable def nd2Between :
    ∀ outgoing : Fin 2,
      StableGraphIncidence.Equivalence
        (W3Nd2CommonBalance.candidates input profile incoming).datum
        ((W3WallInput.nd2Family input profile
          (W3Nd2PositiveExit.initialLabelling input profile incoming
            incomingFD)).candidate outgoing).datum
  | 0 => W3Nd2PositiveExit.between input profile incoming 0
  | 1 => W3Nd2PositiveExit.between input profile incoming 1

/-- **The row formula for Figure 31**,
`W3Nd2GraphTracking.outgoingLabelling_row`, read at the full-dimensional
supply. -/
theorem nd2FullDim_row :
    ∀ (outgoing : Fin 2)
      (hdet : (GluingDatum.LengthMatrixPresentation.matrix
        ((W3WallInput.nd2Family input profile
          (W3Nd2PositiveExit.initialLabelling input profile incoming
            incomingFD)).presentation outgoing)).det ≠ 0),
      (A04FourTags.nd2FullDim input profile hConnected hGenus incoming incomingFD
        outgoing hdet).labelling.row =
        (nd2Between input profile incoming incomingFD outgoing).row.symm.trans
          incomingFD.labelling.row
  | 0, _ => W3Nd2GraphTracking.outgoingLabelling_row input profile incoming incomingFD 0
  | 1, _ => W3Nd2GraphTracking.outgoingLabelling_row input profile incoming incomingFD 1

/-- **Figure 31 as a tracked routed wall.** -/
noncomputable def trackedNd2
    (hwallColumn : W3Nd2CommonBalance.wallColumn input profile
      (W3Nd2PositiveExit.initialLabelling input profile incoming incomingFD) = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ) (position : Fin 2)
    (hNonzero : (GluingDatum.LengthMatrixPresentation.matrix
      ((W3WallInput.ofNd2CoarseFine (wall := wall) input profile
        (W3Nd2PositiveExit.initialLabelling input profile incoming incomingFD)
        hwallColumn hConnected hGenus root).family.presentation position)).det ≠ 0)
    (hMatrix : GluingDatum.LengthMatrixPresentation.matrix
      ((W3WallInput.ofNd2CoarseFine (wall := wall) input profile
        (W3Nd2PositiveExit.initialLabelling input profile incoming incomingFD)
        hwallColumn hConnected hGenus root).family.presentation position) = chart)
    (current : Tracks incomingFD graph label) :
    TrackedRoutedWall degree coordinate chart wall graph label :=
  TrackedRoutedWall.ofIncidence
    (routedNd2 (wall := wall) input profile hConnected hGenus incoming incomingFD
      hwallColumn root chart position hNonzero hMatrix)
    incomingFD current (nd2Between input profile incoming incomingFD)
    (nd2FullDim_row input profile hConnected hGenus incoming incomingFD)

end Nd2

/-! ### Figure 30, the `w3Nd3CoarseFine` tag -/

section Nd3

variable {star : ThreeStar target wallVertex} (input : W3SourceInput data star)
  (profile : Nd3Profile data input.distinguishedBlock)
  (hSame : profile.first.1.1.1 = profile.second.1.1.1)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (incoming : Fin 2)
  (incomingFD : FullDimensionalSourcePresentation
    (W3Nd3CommonBalance.candidates input profile hSame incoming).datum coordinate)

/-- Figure 30's member-to-member incidence equivalences, read on the routed
wall's own family slots: `W3Nd3ArbitraryExit.between`. -/
noncomputable def nd3Between :
    ∀ outgoing : Fin 2,
      StableGraphIncidence.Equivalence
        (W3Nd3CommonBalance.candidates input profile hSame incoming).datum
        ((W3Nd3CommonBalance.honestPresentedFamily input profile hSame
          (W3Nd3ArbitraryExit.initialLabelling input profile hSame incoming
            incomingFD)).candidate outgoing).datum
  | 0 => W3Nd3ArbitraryExit.between input profile hSame incoming 0
  | 1 => W3Nd3ArbitraryExit.between input profile hSame incoming 1

/-- **The row formula for Figure 30**,
`W3Nd3GraphTracking.outgoingLabelling_row`, read at the full-dimensional
supply. -/
theorem nd3FullDim_row :
    ∀ (outgoing : Fin 2)
      (hdet : (GluingDatum.LengthMatrixPresentation.matrix
        ((W3Nd3CommonBalance.honestPresentedFamily input profile hSame
          (W3Nd3ArbitraryExit.initialLabelling input profile hSame incoming
            incomingFD)).presentation outgoing)).det ≠ 0),
      (A04FourTags.nd3FullDim input profile hSame hConnected hGenus incoming incomingFD
        outgoing hdet).labelling.row =
        (nd3Between input profile hSame incoming incomingFD outgoing).row.symm.trans
          incomingFD.labelling.row
  | 0, _ => W3Nd3GraphTracking.outgoingLabelling_row input profile hSame incoming
      incomingFD 0
  | 1, _ => W3Nd3GraphTracking.outgoingLabelling_row input profile hSame incoming
      incomingFD 1

/-- **Figure 30 as a tracked routed wall.** -/
noncomputable def trackedNd3
    (hwallColumn : W3Nd3CommonBalance.wallColumn input profile hSame
      (W3Nd3ArbitraryExit.initialLabelling input profile hSame incoming incomingFD) = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ) (position : Fin 2)
    (hNonzero : (GluingDatum.LengthMatrixPresentation.matrix
      ((W3WallInput.ofNd3CoarseFine (wall := wall) input profile hSame
        (W3Nd3ArbitraryExit.initialLabelling input profile hSame incoming incomingFD)
        hwallColumn hConnected hGenus root).family.presentation position)).det ≠ 0)
    (hMatrix : GluingDatum.LengthMatrixPresentation.matrix
      ((W3WallInput.ofNd3CoarseFine (wall := wall) input profile hSame
        (W3Nd3ArbitraryExit.initialLabelling input profile hSame incoming incomingFD)
        hwallColumn hConnected hGenus root).family.presentation position) = chart)
    (current : Tracks incomingFD graph label) :
    TrackedRoutedWall degree coordinate chart wall graph label :=
  TrackedRoutedWall.ofIncidence
    (routedNd3 (wall := wall) input profile hSame hConnected hGenus incoming incomingFD
      hwallColumn root chart position hNonzero hMatrix)
    incomingFD current (nd3Between input profile hSame incoming incomingFD)
    (nd3FullDim_row input profile hSame hConnected hGenus incoming incomingFD)

end Nd3

/-! ### Figure 32, the `w2M11` tag -/

section M11

open DraismaVargas.LocalCases.SecondEquation
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.W4Assembly

variable {star : TwoStar target wallVertex} {block : WallBlock data wallVertex}
  (input : W2SourceInput data star)
  (profile : W2R2SourceProfile.SourceProfile data star block)
  (hCard : (data.vertexPartition wallVertex).blockCard block.1 = 2)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (incoming : Fin 3)
  (incomingFD : FullDimensionalSourcePresentation
    (M11RemoteCandidates.candidates input profile hCard incoming).datum coordinate)

/-- Figure 32's member-to-member incidence equivalences, read on the routed
wall's own gauge-family slots: `M11StableGraphs.between`.  The remote position
is not special. -/
noncomputable def m11Between :
    ∀ outgoing : Fin 3,
      StableGraphIncidence.Equivalence
        (M11RemoteCandidates.candidates input profile hCard incoming).datum
        ((A04M11Wiring.m11Family input profile hCard hConnected hGenus incoming
          incomingFD).candidate outgoing).datum
  | 0 => M11StableGraphs.between input profile hCard incoming 0
  | 1 => M11StableGraphs.between input profile hCard incoming 1
  | 2 => M11StableGraphs.between input profile hCard incoming 2

/-- **The row formula for Figure 32**,
`W2M11GraphTracking.outgoingLabelling_row`, read at the full-dimensional
supply. -/
theorem m11FullDim_row :
    ∀ (outgoing : Fin 3)
      (hdet : (GluingDatum.LengthMatrixPresentation.matrix
        ((A04M11Wiring.m11Family input profile hCard hConnected hGenus incoming
          incomingFD).presentation outgoing)).det ≠ 0),
      (A04M11Wiring.m11FullDim input profile hCard hConnected hGenus incoming incomingFD
        outgoing hdet).labelling.row =
        (m11Between input profile hCard hConnected hGenus incoming incomingFD
          outgoing).row.symm.trans incomingFD.labelling.row
  | 0, _ => W2M11GraphTracking.outgoingLabelling_row input profile hCard incoming
      incomingFD 0
  | 1, _ => W2M11GraphTracking.outgoingLabelling_row input profile hCard incoming
      incomingFD 1
  | 2, _ => W2M11GraphTracking.outgoingLabelling_row input profile hCard incoming
      incomingFD 2

/-- **Figure 32 as a tracked routed wall.** -/
noncomputable def trackedW2M11
    (hwallColumn : (A04M11Wiring.m11Family input profile hCard hConnected hGenus incoming
      incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart)
    (current : Tracks incomingFD graph label) :
    TrackedRoutedWall degree coordinate chart wall graph label :=
  TrackedRoutedWall.ofIncidence
    (A04M11Wiring.routedW2M11 (wall := wall) input profile hCard hConnected hGenus incoming
      incomingFD hwallColumn root chart hChart)
    incomingFD current
    (m11Between input profile hCard hConnected hGenus incoming incomingFD)
    (m11FullDim_row input profile hCard hConnected hGenus incoming incomingFD)

end M11

/-! ### Figure 35, the `w2P` tag -/

section W2P

open DraismaVargas.LocalCases.SecondEquation
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.W4Assembly

variable {star : TwoStar target wallVertex} {block : WallBlock data wallVertex}
  {profile : W2R2SourceProfile.SourceProfile data star block}
  (input : W2SourceInput data star) (shape : W2PSourceCandidates.Shape profile)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (incoming : Fin 3)
  (incomingFD : FullDimensionalSourcePresentation
    (W2PCommonBalance.members profile shape incoming).datum coordinate)

/-- **Figure 35 as a tracked routed wall.**  `W2PArbitraryExit.familyFullDim` is
uniform in the member, and `W2PGraphTracking.outgoingLabelling_row` is its row
formula at `W2PArbitraryExit.between`. -/
noncomputable def trackedW2P
    (hwallColumn :
      (W2PArbitraryExit.family input shape incoming incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart)
    (current : Tracks incomingFD graph label) :
    TrackedRoutedWall degree coordinate chart wall graph label :=
  TrackedRoutedWall.ofIncidence
    (routedW2P (wall := wall) input shape hConnected hGenus incoming incomingFD
      hwallColumn root chart hChart)
    incomingFD current
    (fun outgoing ↦ W2PArbitraryExit.between input shape incoming outgoing)
    (fun outgoing _ ↦ W2PGraphTracking.outgoingLabelling_row input shape incoming
      incomingFD outgoing)

end W2P

/-! ### Equation (10), the `w2R1` tag -/

section R1

open DraismaVargas.LocalCases.SecondEquation
open DraismaVargas.LocalCases.W2R1Target

variable {star : TwoStar target wallVertex}
  (pair : W2R1SourceCandidates.Pair data star) (input : W2SourceInput data star)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (incoming : Fin 2)
  (incomingFD : FullDimensionalSourcePresentation
    (pair.candidate incoming).datum coordinate)

/-- **Equation (10) as a tracked routed wall.**  `W2R1GraphData.familyFullDim` is
uniform in the member, and `W2R1GraphTracking.outgoingLabelling_row` is its row
formula at `W2R1GraphData.between`. -/
noncomputable def trackedW2R1
    (hwallColumn :
      (W2R1GraphData.family pair input incoming incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart)
    (current : Tracks incomingFD graph label) :
    TrackedRoutedWall degree coordinate chart wall graph label :=
  TrackedRoutedWall.ofIncidence
    (A04R1Wiring.routedW2R1 (wall := wall) pair input hConnected hGenus incoming
      incomingFD hwallColumn root chart hChart)
    incomingFD current
    (fun outgoing ↦ W2R1GraphData.between pair input.valid incoming outgoing)
    (fun outgoing _ ↦ W2R1GraphTracking.outgoingLabelling_row pair input.valid incoming
      incomingFD outgoing)

end R1

end Tags

/-! ## 4.  A tracked certified exit as a march payload -/

section Successor

open GraphContraction GluingContraction ContractionRamification WallDegeneration
open W4Assembly

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}

/-- **A tracked certified exit is a tracked march payload.**  Everything
`TrackedPencil` asks for is already under `TrackedCertifiedExit`'s binders: the
base target, base datum, wall and actual `BalancedGlobal.Candidate`, the base
stage's validity, connectedness and genus zero, the outgoing full-dimensional
presentation, its `Tracks`, and -- as the literal fields of
`BalancedGlobal.Candidate.ClearedPencil` -- the integral realization, its
positive scale, the target-length identity and the rank-one pencil.  The genus
conjunct is derived by `TrackedPencil.of_tracks`, so `2 ≤ degree` is the only new
hypothesis.

Nothing is identified by matrices and no candidate is replaced: the payload is
stated on the exit's own retained candidate and its own presentation. -/
theorem trackedPencil_of_certifiedExit (hDegree : 2 ≤ degree)
    {target : CFGraph.{0}} {data : GluingDatum target degree}
    {fullDim : FullDimensionalSourcePresentation data coordinate}
    {z incomingVelocity : coordinate → ℚ}
    (exit : W3ShiftGraphTracking.TrackedCertifiedExit fullDim graph label z
      incomingVelocity) :
    ∃ (outgoingMatrix : Matrix coordinate coordinate ℚ) (velocity : coordinate → ℚ)
      (δ : ℚ), 0 < δ ∧
      (GluingDatum.LengthMatrixPresentation.matrix
        fullDim.labelling.presentation).det * outgoingMatrix.det < 0 ∧
      ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • velocity) i) ∧
        outgoingMatrix.mulVec (z + t • velocity) =
          (GluingDatum.LengthMatrixPresentation.matrix
            fullDim.labelling.presentation).mulVec z +
            t • (GluingDatum.LengthMatrixPresentation.matrix
              fullDim.labelling.presentation).mulVec incomingVelocity ∧
        TrackedPencil degree graph label outgoingMatrix (z + t • velocity) := by
  obtain ⟨baseTarget, base, wall, candidate, hBaseValid, hBaseConnected, hBaseGenus,
    _hOutValid, _hIncidence, outgoingFD, ⟨tracking⟩, hSign, velocity, δ, hδ, hStep⟩ :=
    exit
  refine ⟨_, velocity, δ, hδ, hSign, ?_⟩
  intro t ht htδ
  obtain ⟨hPositive, hMetric, realization, scale, hScale, hLength, hBn⟩ := hStep t ht htδ
  exact ⟨hPositive, hMetric,
    TrackedPencil.of_tracks hDegree baseTarget base wall candidate outgoingFD rfl
      hBaseValid hBaseConnected hBaseGenus
      ⟨realization, scale, hScale, hLength, hBn⟩ tracking⟩

end Successor

/-! ## 5.  The composite from the tracked caterpillar seed -/

section Seed

/-- **From the tracked seed to a terminal tracked state.**  The time-zero state is
`TrackedState.caterpillarGeneric` -- `CaterpillarGenericSeed.state` with the seed
cover's own stable graph and row labels attached -- and the conclusion is
`TrackedState.exists_terminal_reachable_of_tracked_progress` at it: a reachable
terminal tracked state whose payload still carries the ambient graph, its row
labels and the source genus, together with the cleared terminal face and the
rank-one pencil.

The only input beyond the seed is one `TrackedProgress` per nonterminal state,
which `trackedProgressOfRoutedWalls` builds from a `TrackedRoutedWall` at every
coordinate.  `2 ≤ degree` is automatic here, since the caterpillar's degree is
`m + 2`. -/
theorem exists_terminal_tracked_caterpillar (m : ℕ)
    (coordinates : Fin (6 * m + 3) → ℚ) (hPositive : ∀ i, 0 < coordinates i)
    (baseStart baseFinish : Fin (6 * m + 3) → ℚ)
    (hMap : (CaterpillarGenericSeed.matrix m).mulVec coordinates = baseStart)
    (localProgress : ∀ current : TrackedState (m + 2)
        (TrackedPencil.seedGraph (CaterpillarSeed.seed m)
          (CaterpillarSeed.seedFullDim m (CaterpillarRows.fullDim m)))
        (TrackedPencil.seedLabel (CaterpillarSeed.seed m)
          (CaterpillarSeed.seedFullDim m (CaterpillarRows.fullDim m)))
        (MatrixAtlas.atlasMatrix (coordinate := Fin (6 * m + 3)) (degree := m + 2))
        baseStart baseFinish,
      ¬ TrackedState.Terminal current → TrackedProgress current) :
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
  TrackedState.exists_terminal_reachable_of_tracked_progress (by omega)
    (fun l ↦ MatrixAtlas.atlasMatrix_det_ne_zero l) localProgress _

/-- **The composite, end to end.**  The caterpillar seed, a `TrackedRoutedWall`
at every coordinate of every nonterminal reached state, and the genericity
hypothesis give a terminal tracked state.  This is the statement the outer walk consumes;
it checks that `trackedProgressOfRoutedWalls` -- stated at
`WallProgress.atlasChartMatrix` -- is exactly what the caterpillar march, stated
at `MatrixAtlas.atlasMatrix`, takes.

`hGeneric` is the genericity clause of
`CaterpillarGenericSeed.exists_initializedMarch`, which holds at *every* state of
the perturbed seed's march with no reachability hypothesis; the tracked wall
inputs are hypotheses, as everywhere else in this file. -/
theorem exists_terminal_tracked_caterpillar_of_routedWalls (m : ℕ)
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
      ∀ (wall : Fin (6 * m + 3)), current.toSemanticState.FirstWall wall →
      TrackedRoutedWall (m + 2) (Fin (6 * m + 3))
        (MatrixAtlas.atlasMatrix current.toMatrixState.label) wall
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
  exists_terminal_tracked_caterpillar m coordinates hPositive baseStart baseFinish hMap
    (fun current hNonterminal ↦
      trackedProgressOfRoutedWalls current (routed current hNonterminal)
        (hGeneric current))

end Seed

end DraismaVargas.LocalCases.TrackedWallProgress
