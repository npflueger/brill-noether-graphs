import DraismaVargas.LocalCases.TrackedPencil

/-!
# The march state that carries its row-labelled graph

Source: Draisma--Vargas Part I, the atlas march of
`DraismaVargas/LocalCases/SemanticAtlasMarch.lean`, read against Vargas,
Part II (arXiv:2609.09109), Section 4.

`SemanticAtlasMarch.State` is `FiniteAtlasMarch.State` plus a
`CarriesClearedPencil` payload.  This file is the same construction one level
up: `TrackedState` is `FiniteAtlasMarch.State` plus a `TrackedPencil` payload.

**It is deliberately NOT `SemanticAtlasMarch.State` together with a separate
tracking field.**  That shape would put two independent existential binders at
one chart matrix -- the state's own candidate and the tracked one -- with
nothing identifying them, which is exactly the loss the header of
`InteriorGraphTracking.lean` records.  Here the graph, the labels, the
candidate, its full-dimensional presentation and its cleared pencil all sit
under a single binder, and `toSemanticState` recovers the old state by
`TrackedPencil.toCarriesClearedPencil`, so nothing downstream has to change.

`(D, V, graph, label)` are *parameters* of the state, fixed for the whole
march.  That is what makes the tracked march an invariant rather than a
decoration: a `Step` cannot change the ambient graph, and
`TrackedPencil`'s genus conjunct is stated against `graph.genus`, so
source-graph genus invariance along the march is a consequence of the shape.

What is proved here: the state, its projection, `Terminal`/`Step`/`march`/
`clearedFace` reused through that projection, the seed instance (the literal
caterpillar seed of `CaterpillarGenericSeed`, tracked), the tracked progress
package, and its successor theorem -- which is the strengthened conclusion of
`SemanticAtlasMarch.State.PresentedProgress.exists_step` plus `tracksAt`, with
no new mathematics -- and the terminal-reachability corollary.

What is not proved here.  `TrackedProgress` is a *conditional* witness: it is
inhabited exactly when a `SemanticAtlasMarch.State.PresentedProgress` is --
the output of the exhaustive local classification -- together with one tracking
at each `fullDimAt` output.  Producing those is not done here.  `2 ≤ degree`
remains an explicit hypothesis wherever a successor payload has to be rebuilt,
because that is what `TrackedPencil.of_tracks` uses to derive the genus
conjunct.

Consumers: the finite Whitehead-chain assembly of `OuterWalk`, through
`TrackedPencil.exists_chain_to_core` at the terminal tracked state.
-/

namespace DraismaVargas.LocalCases

open Utilities
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.Infrastructure.RationalAffineWall
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.StableSourceDarts
open DraismaVargas.LocalCases.InteriorGraphTracking

section General

variable {coordinate chart D V : Type*}
  [Fintype coordinate] [DecidableEq coordinate]
  [Fintype chart] [DecidableEq chart]
  [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

/-- **The tracked march state.**  A finite-atlas state whose positive restart
carries an actual candidate, its full-dimensional presentation, its cleared
pencil, a tracking of the fixed ambient row-labelled graph by that same
presentation, and the source genus of that same cover -- all under one
existential binder. -/
structure TrackedState (degree : ℕ) (graph : CubicDartGraph D V)
    (label : D → coordinate)
    (matrix : chart → Matrix coordinate coordinate ℚ)
    (baseStart baseFinish : coordinate → ℚ) where
  toMatrixState : FiniteAtlasMarch.State matrix baseStart baseFinish
  carriesTrackedPencil : TrackedPencil degree graph label
    (matrix toMatrixState.label) toMatrixState.currentStart

namespace TrackedState

variable {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  {matrix : chart → Matrix coordinate coordinate ℚ}
  {baseStart baseFinish : coordinate → ℚ}

/-- **Backwards compatibility.**  Forgetting the graph is the existing semantic
state, so every theorem about `SemanticAtlasMarch.State` applies verbatim. -/
def toSemanticState (current : TrackedState degree graph label matrix baseStart baseFinish) :
    SemanticAtlasMarch.State degree matrix baseStart baseFinish where
  toMatrixState := current.toMatrixState
  carriesPencil := current.carriesTrackedPencil.toCarriesClearedPencil

omit [Fintype chart] [DecidableEq chart] in
@[simp] theorem toSemanticState_toMatrixState
    (current : TrackedState degree graph label matrix baseStart baseFinish) :
    current.toSemanticState.toMatrixState = current.toMatrixState := rfl

/-- A matrix state with a tracked seed payload starts the tracked march. -/
def initial
    (matrixState : FiniteAtlasMarch.State matrix baseStart baseFinish)
    (pencil : TrackedPencil degree graph label
      (matrix matrixState.label) matrixState.currentStart) :
    TrackedState degree graph label matrix baseStart baseFinish where
  toMatrixState := matrixState
  carriesTrackedPencil := pencil

/-- Terminality is the matrix-level condition, read through the projection. -/
def Terminal (current : TrackedState degree graph label matrix baseStart baseFinish) : Prop :=
  SemanticAtlasMarch.State.Terminal current.toSemanticState

/-- Steps are the matrix-level steps, read through the projection. -/
def Step (current next : TrackedState degree graph label matrix baseStart baseFinish) : Prop :=
  SemanticAtlasMarch.State.Step current.toSemanticState next.toSemanticState

omit [Fintype chart] [DecidableEq chart] in
theorem terminal_iff (current : TrackedState degree graph label matrix baseStart baseFinish) :
    Terminal current ↔ FiniteAtlasMarch.State.Terminal current.toMatrixState := Iff.rfl

omit [Fintype chart] [DecidableEq chart] in
theorem step_iff (current next : TrackedState degree graph label matrix baseStart baseFinish) :
    Step current next ↔
      FiniteAtlasMarch.State.Step current.toMatrixState next.toMatrixState := Iff.rfl

omit [Fintype chart] [DecidableEq chart] in
/-- A terminal tracked state clears the exact nonnegative endpoint, exactly as
the untracked one does. -/
theorem clearedFace (current : TrackedState degree graph label matrix baseStart baseFinish)
    (hTerminal : Terminal current) :
    SemanticAtlasMarch.CarriesClearedFace degree
      (matrix current.toMatrixState.label) current.toMatrixState.currentFinish :=
  current.toSemanticState.clearedFace hTerminal

/-- The tracked wrapper has the same fixed event set and termination measure as
the matrix march. -/
noncomputable def march (degree : ℕ) (graph : CubicDartGraph D V)
    (label : D → coordinate)
    (matrix : chart → Matrix coordinate coordinate ℚ)
    (hdet : ∀ l, (matrix l).det ≠ 0)
    (baseStart baseFinish : coordinate → ℚ) :
    FiniteStrictMarch (TrackedState degree graph label matrix baseStart baseFinish) where
  eventTimes := FiniteAtlasMarch.eventTimes matrix baseStart baseFinish
  time := fun current ↦ current.toMatrixState.lastWallTime
  step := Step
  step_time_lt := by
    intro current next hstep
    exact (FiniteAtlasMarch.State.march matrix hdet baseStart baseFinish).step_time_lt hstep
  step_time_mem := by
    intro current next hstep
    exact (FiniteAtlasMarch.State.march matrix hdet baseStart baseFinish).step_time_mem hstep

end TrackedState

/-- **The tracked local-classification package.**  A presented progress at the
underlying semantic state, together with one actual tracking of the ambient
graph at every full-dimensional presentation the classifier can hand over.

`tracksAt` is asked at exactly `fullDimAt`'s four arguments -- the wall, the
proof that it is a first wall of the state's segment, the outgoing member and
its nonsingularity -- so the tracking is attached to the very presentation the
successor payload is built from, not to another witness at the same matrix.  No
genus companion is needed: `TrackedPencil.of_tracks` derives the genus conjunct
from the tracking. -/
structure TrackedProgress {degree : ℕ} {graph : CubicDartGraph D V}
    {label : D → coordinate}
    {matrix : chart → Matrix coordinate coordinate ℚ}
    {baseStart baseFinish : coordinate → ℚ}
    (current : TrackedState degree graph label matrix baseStart baseFinish) where
  toPresentedProgress :
    SemanticAtlasMarch.State.PresentedProgress current.toSemanticState
  tracksAt : ∀ (wall : coordinate)
    (hw : current.toSemanticState.FirstWall wall)
    (outgoing : Fin (toPresentedProgress.caseAt wall hw).arity)
    (hdet : (GluingDatum.LengthMatrixPresentation.matrix
      ((toPresentedProgress.familyAt wall hw).presentation outgoing)).det ≠ 0),
    Nonempty (Tracks (toPresentedProgress.fullDimAt wall hw outgoing hdet) graph label)

namespace TrackedProgress

variable {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  {matrix : chart → Matrix coordinate coordinate ℚ}
  {baseStart baseFinish : coordinate → ℚ}
  {current : TrackedState degree graph label matrix baseStart baseFinish}

/-- The conditional non-vacuity witness: a presented progress plus one tracking
per reachable outgoing full-dimensional presentation is a tracked progress.
Nothing else is required: a presented progress is the output of the local
classification. -/
def ofPresented
    (progress : SemanticAtlasMarch.State.PresentedProgress current.toSemanticState)
    (tracks : ∀ (wall : coordinate)
      (hw : current.toSemanticState.FirstWall wall)
      (outgoing : Fin (progress.caseAt wall hw).arity)
      (hdet : (GluingDatum.LengthMatrixPresentation.matrix
        ((progress.familyAt wall hw).presentation outgoing)).det ≠ 0),
      Nonempty (Tracks (progress.fullDimAt wall hw outgoing hdet) graph label)) :
    TrackedProgress current where
  toPresentedProgress := progress
  tracksAt := tracks

omit [Fintype chart] [DecidableEq chart] in
/-- **The tracked successor.**  Nothing new is proved: the strengthened
conclusion of `PresentedProgress.exists_step` names the selected wall, the
selected outgoing member, the nonsingularity proof at which `fullDimAt` is
read, the successor's chart label and the cleared pencil on that very
`fullDimAt` witness; `tracksAt` supplies the tracking at the same witness; and
`TrackedPencil.of_tracks` assembles them, deriving the genus conjunct. -/
theorem exists_step (hDegree : 2 ≤ degree) (progress : TrackedProgress current)
    (hdet : ∀ l, (matrix l).det ≠ 0)
    (hNonterminal : ¬ TrackedState.Terminal current) :
    ∃ next : TrackedState degree graph label matrix baseStart baseFinish,
      TrackedState.Step current next := by
  obtain ⟨next, hstep, wall, hw, outgoing, houtgoing, hlabel, hpencil⟩ :=
    progress.toPresentedProgress.exists_step hdet hNonterminal
  refine ⟨⟨next.toMatrixState, ?_⟩, hstep⟩
  refine TrackedPencil.of_tracks hDegree
    (progress.toPresentedProgress.targetAt wall hw)
    ((progress.toPresentedProgress.familyAt wall hw).base outgoing)
    (progress.toPresentedProgress.targetWallAt wall hw)
    ((progress.toPresentedProgress.familyAt wall hw).candidate outgoing)
    (progress.toPresentedProgress.fullDimAt wall hw outgoing houtgoing) ?_
    ((progress.toPresentedProgress.familyAt wall hw).valid_of_old outgoing
      (progress.toPresentedProgress.validAt wall hw))
    (progress.toPresentedProgress.targetConnectedAt wall hw)
    (progress.toPresentedProgress.targetGenusAt wall hw)
    (Classical.choice hpencil)
    (Classical.choice (progress.tracksAt wall hw outgoing houtgoing))
  rw [progress.toPresentedProgress.fullDimPresentation wall hw outgoing houtgoing,
    hlabel, progress.toPresentedProgress.outgoingMatrix wall hw outgoing houtgoing]

end TrackedProgress

namespace TrackedState

variable {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  {matrix : chart → Matrix coordinate coordinate ℚ}
  {baseStart baseFinish : coordinate → ℚ}

omit [DecidableEq chart] in
/-- **Tracked global termination.**  The finite event set is reached exactly as
for the untracked march, and the final state's payload still carries the
ambient graph, its row
labels and the source genus, so the Whitehead-chain interface of
`TrackedPencil` applies at the terminal state. -/
theorem exists_terminal_reachable_of_tracked_progress (hDegree : 2 ≤ degree)
    (hdet : ∀ l, (matrix l).det ≠ 0)
    (localProgress : ∀ current : TrackedState degree graph label matrix baseStart baseFinish,
      ¬ Terminal current → TrackedProgress current)
    (initial : TrackedState degree graph label matrix baseStart baseFinish) :
    ∃ final, Relation.ReflTransGen Step initial final ∧ Terminal final ∧
      TrackedPencil degree graph label
        (matrix final.toMatrixState.label) final.toMatrixState.currentStart ∧
      SemanticAtlasMarch.CarriesClearedFace degree
        (matrix final.toMatrixState.label) final.toMatrixState.currentFinish ∧
      ∃ source : CFGraph.{0}, BNExists source 1 degree := by
  obtain ⟨final, hreach, hterminal⟩ :=
    (march degree graph label matrix hdet baseStart baseFinish).exists_terminal_reachable
      Terminal (fun current ↦ by
        by_cases hterminal : Terminal current
        · exact Or.inl hterminal
        · exact Or.inr ((localProgress current hterminal).exists_step hDegree hdet hterminal))
      initial
  exact ⟨final, hreach, hterminal, final.carriesTrackedPencil,
    final.clearedFace hterminal, final.carriesTrackedPencil.exists_bnExists⟩

end TrackedState

end General

/-! ## Non-vacuity: the tracked seed

`InitialState.matrixState` and the seed payload theorems live at
`coordinate : Type`, so this section repeats the ambient binders at universe
zero.  Nothing else changes. -/

section Seed

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

namespace TrackedState

/-- The tracked time-zero state of an arbitrary `SeedCandidate.Seed`: the
matrix half is the existing `InitialState.matrixState`, and the payload is the
seed's own cover tracking its own `ofDatum` graph at literal row labels. -/
noncomputable def ofSeed {degree : ℕ} (hDegree : 2 ≤ degree)
    (seed : SeedCandidate.Seed degree)
    (fullDim : FullDimensionalSourcePresentation seed.candidate.datum coordinate)
    (baseFinish : coordinate → ℚ) :
    TrackedState degree (TrackedPencil.seedGraph seed fullDim)
      (TrackedPencil.seedLabel seed fullDim)
      (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := degree))
      ((GluingDatum.LengthMatrixPresentation.matrix
        fullDim.labelling.presentation).mulVec fun _ ↦ (1 : ℚ))
      baseFinish where
  toMatrixState := InitialState.matrixState fullDim.labelling.presentation
    fullDim.decomposes.nodup fullDim.det_ne_zero baseFinish
  carriesTrackedPencil := by
    simpa only [InitialState.matrixState_label, InitialState.matrixState_currentStart,
      InitialState.atlasMatrix_presentationChart] using
      TrackedPencil.ofSeed hDegree seed fullDim (fun _ ↦ (1 : ℚ)) (fun _ ↦ one_pos)

/-- **The literal caterpillar seed, tracked.**  The genus-`2m+2`,
degree-`m+2` caterpillar cover of `CaterpillarSeed`/`CaterpillarGenericSeed`
enters the tracked march with its own stable graph and row labels attached. -/
noncomputable def caterpillar (m : ℕ) (baseFinish : Fin (6 * m + 3) → ℚ) :
    TrackedState (m + 2)
      (TrackedPencil.seedGraph (CaterpillarSeed.seed m)
        (CaterpillarSeed.seedFullDim m (CaterpillarRows.fullDim m)))
      (TrackedPencil.seedLabel (CaterpillarSeed.seed m)
        (CaterpillarSeed.seedFullDim m (CaterpillarRows.fullDim m)))
      (MatrixAtlas.atlasMatrix (coordinate := Fin (6 * m + 3)) (degree := m + 2))
      ((GluingDatum.LengthMatrixPresentation.matrix
        (CaterpillarSeed.seedFullDim m
          (CaterpillarRows.fullDim m)).labelling.presentation).mulVec fun _ ↦ (1 : ℚ))
      baseFinish :=
  ofSeed (by omega) (CaterpillarSeed.seed m)
    (CaterpillarSeed.seedFullDim m (CaterpillarRows.fullDim m)) baseFinish

/-- **The caterpillar seed at a generic starting metric, tracked.**  This is
`CaterpillarGenericSeed.state` -- the time-zero state that
`CaterpillarGenericSeed.exists_genericInitialState` perturbs into general
position -- with the seed cover's own stable graph and row labels attached.
The matrix half is literally the one that file builds; only the payload is
strengthened. -/
noncomputable def caterpillarGeneric (m : ℕ)
    (coordinates : Fin (6 * m + 3) → ℚ) (hPositive : ∀ i, 0 < coordinates i)
    (baseStart baseFinish : Fin (6 * m + 3) → ℚ)
    (hMap : (CaterpillarGenericSeed.matrix m).mulVec coordinates = baseStart) :
    TrackedState (m + 2)
      (TrackedPencil.seedGraph (CaterpillarSeed.seed m)
        (CaterpillarSeed.seedFullDim m (CaterpillarRows.fullDim m)))
      (TrackedPencil.seedLabel (CaterpillarSeed.seed m)
        (CaterpillarSeed.seedFullDim m (CaterpillarRows.fullDim m)))
      (MatrixAtlas.atlasMatrix (coordinate := Fin (6 * m + 3)) (degree := m + 2))
      baseStart baseFinish where
  toMatrixState := FiniteAtlasMarch.State.initial (CaterpillarGenericSeed.label m)
    coordinates
    (FiniteAtlasMarch.chartCoordinates
      (MatrixAtlas.atlasMatrix (CaterpillarGenericSeed.label m)) baseFinish)
    hPositive
    (by rw [CaterpillarGenericSeed.atlasMatrix_label]; exact hMap)
    (FiniteAtlasMarch.mulVec_chartCoordinates _
      (MatrixAtlas.atlasMatrix_det_ne_zero _) baseFinish)
  carriesTrackedPencil := by
    change TrackedPencil (m + 2) _ _
      (MatrixAtlas.atlasMatrix (CaterpillarGenericSeed.label m)) coordinates
    rw [CaterpillarGenericSeed.atlasMatrix_label]
    exact TrackedPencil.caterpillar m coordinates hPositive

end TrackedState

end Seed

end DraismaVargas.LocalCases
