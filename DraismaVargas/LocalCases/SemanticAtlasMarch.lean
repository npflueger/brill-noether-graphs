import DraismaVargas.LocalCases.FiniteAtlasMarch
import DraismaVargas.LocalCases.ClosedFaceRealization
import DraismaVargas.LocalCases.FullDimensionalSource

/-!
# A finite atlas march retaining subdivision pencils

`FiniteAtlasMarch.State` deliberately stores only rational matrices and the
invariants needed for finite termination.  This file adds the semantic payload
needed by Part I: every positive restart is tied to an actual globally
assembled candidate, its length-matrix presentation, and its cleared rank-one
pencil.

The wrapper leaves the finite event argument untouched.  Local source
classification has to provide a balanced family at every nonterminal state --
a `BalancedGlobal.GaugeFamily`, whose members may each sit over their own
branch-swapped copy of the wall datum -- and treating zero coordinates at the
final closed endpoint is a separate contraction step.
-/

namespace DraismaVargas.LocalCases.SemanticAtlasMarch

open Utilities
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.RationalAffineWall
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.ClassifiedContinuation
open DraismaVargas.LocalCases.FullDimensionalSource

variable {coordinate chart : Type*}
  [Fintype coordinate] [DecidableEq coordinate]
  [Fintype chart] [DecidableEq chart]

/-! ### The first wall of a segment

The march crosses exactly one coordinate at a time: the coordinate whose
crossing time is least, selected from the incoming coordinates alone by
`RationalAffineWall.exists_first_positiveOrthant_exit`.  Every source-side
input below is asked *only there*.

This guard is what makes the source-side demand satisfiable.  A wall input at a
coordinate carries an interior (non-type-changing) wall metric of the incoming
cover -- a nonnegative chart point vanishing at that coordinate with all stable
rows alive -- and `InteriorProgress.not_admissibleColumn_of_stablePath_over_column`
exhibits coordinates with no such metric at all: those over which a whole stable
class of the cover lies.  Contracting one of those is a type change, and the
march never crosses it, so a *total* `∀ wall` demand is not merely unproved but
false in general.  `IsFirstWall` restricts the demand to the coordinate the
march actually crosses, where
`InteriorProgress.exists_admissibleColumn_of_nonterminal` supplies the metric. -/

/-- **`wall` is a first wall of the segment from `start` to `finish`**: at some
interior time the segment vanishes at `wall` and is strictly positive at every
other coordinate.  This is exactly the conclusion
`RationalAffineWall.exists_first_positiveOrthant_exit` returns about the
coordinate it selects, minus the "no earlier event" clause no consumer uses. -/
def IsFirstWall (start finish : coordinate → ℚ) (wall : coordinate) : Prop :=
  ∃ time : ℚ, 0 < time ∧ time < 1 ∧
    RationalAffineWall.segment start finish time wall = 0 ∧
    ∀ i, i ≠ wall → 0 < RationalAffineWall.segment start finish time i

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- The selected coordinate of a positive-orthant exit is a first wall. -/
theorem isFirstWall_of_exit {start finish : coordinate → ℚ} {wall : coordinate}
    {time : ℚ} (htimePos : 0 < time) (htimeLt : time < 1)
    (hzero : RationalAffineWall.segment start finish time wall = 0)
    (hother : ∀ i, i ≠ wall →
      0 < RationalAffineWall.segment start finish time i) :
    IsFirstWall start finish wall :=
  ⟨time, htimePos, htimeLt, hzero, hother⟩

/-- **Non-vacuity.**  Every nonterminal simple segment has a first wall, so the
guarded demand is never empty where the march needs it. -/
theorem exists_isFirstWall (start finish : coordinate → ℚ)
    (hstart : ∀ i, 0 < start i) (houtside : ∃ i, finish i < 0)
    (hsimple : SimpleNegativeCrossings start finish) :
    ∃ wall : coordinate, IsFirstWall start finish wall := by
  obtain ⟨wall, time, htimePos, htimeLt, hzero, hother, -⟩ :=
    exists_first_positiveOrthant_exit start finish hstart houtside hsimple
  exact ⟨wall, isFirstWall_of_exit htimePos htimeLt hzero hother⟩

omit [Fintype coordinate] in
/-- The wall point of a first wall is a nonnegative point of the segment
vanishing at the wall: the metric input of
`InteriorProgress.admissibleColumn_of_state`. -/
theorem IsFirstWall.exists_nonneg_zero {start finish : coordinate → ℚ}
    {wall : coordinate} (h : IsFirstWall start finish wall) :
    ∃ time : ℚ, 0 ≤ time ∧ time < 1 ∧
      (∀ i, 0 ≤ RationalAffineWall.segment start finish time i) ∧
      RationalAffineWall.segment start finish time wall = 0 := by
  obtain ⟨time, htimePos, htimeLt, hzero, hother⟩ := h
  refine ⟨time, htimePos.le, htimeLt, fun i ↦ ?_, hzero⟩
  by_cases hi : i = wall
  · subst hi; exact le_of_eq hzero.symm
  · exact (hother i hi).le

/-- A chart matrix and positive coordinate vector are semantically realized by
an actual Draisma--Vargas candidate carrying an explicit cleared subdivision
pencil.  The
contracted target, gluing datum, and wall are existential because they may
change at every atlas transition.

**The presentation is a `FullDimensionalSourcePresentation`, not a bare
`LengthMatrixPresentation`, and it is bound by the same `∃` as the candidate.**
Both halves of that are forced.  The continuation factors through
`IncomingSourceCases.exists_classification`, whose first source-side hypothesis
is a `FullDimensionalSourcePresentation` of the datum whose honest stable length
matrix is the chart matrix; four of its eight fields (`saturated`, the honest
`labelling`, `trivalent`, `pathEnds`) are not recoverable from validity,
connectedness and genus zero, so they have to travel in the state.  And a chart
matrix does not determine its candidate — a bad candidate can realize a good
matrix — so a certificate stated outside the binder would have to hold for
*every* candidate and fails outright.  The three admissibility hypotheses
`exists_classification` also takes are **not**
carried: `WallAdmissibility.danglingCompatible_of_fullDimensional`,
`WallAdmissibilityStable.trivalent_of_fullDimensional` and
`WallAdmissibilityStable.stablePath_equiv` derive all three from the metric
facts at the wall event.

The three facts recorded about the incoming stage — validity of the incoming
datum, connectedness of the incoming target and its genus zero — are exactly
the hypothesis triple of `TerminalGluing.nonempty_contractedGluing_of_incoming`
and of `ZeroFreeTerminalFace.contractedGluing`, so a
terminal face reads them off the receipt with no transport step.  They are
strictly stronger than their expanded counterparts, which
`Candidate.datum_valid`, `TargetExpansion.graph_connected` and
`TargetExpansion.graph_genus` recover across the one-edge vertex split. -/
def CarriesClearedPencil (degree : ℕ)
    (matrix : Matrix coordinate coordinate ℚ) (coordinates : coordinate → ℚ) :
    Prop :=
  ∃ (target : CFGraph.{0}) (data : GluingDatum target degree) (wall : target.V),
    ∃ (candidate : Candidate target degree data wall),
      ∃ fullDim : FullDimensionalSourcePresentation candidate.datum coordinate,
        GluingDatum.LengthMatrixPresentation.matrix
            fullDim.labelling.presentation = matrix ∧
        data.Valid ∧
        graph_connected target ∧
        genus target = 0 ∧
        Nonempty (Candidate.ClearedPencil candidate
          fullDim.labelling.presentation coordinates)

/-- A closed-cone coordinate vector is attached to the same kind of actual
candidate and presentation, but carries a nonnegative realization whose zero
occurrences are still awaiting contraction.

It records the same incoming-stage triple as `CarriesClearedPencil`: those are
the three hypotheses the contracted gluing receipt of the terminal face needs,
and nothing in `Candidate.ClearedFace` or in the source-contraction topology
supplies them. -/
def CarriesClearedFace (degree : ℕ)
    (matrix : Matrix coordinate coordinate ℚ) (coordinates : coordinate → ℚ) :
    Prop :=
  ∃ (target : CFGraph.{0}) (data : GluingDatum target degree) (wall : target.V),
    ∃ (candidate : Candidate target degree data wall),
      ∃ presentation : candidate.datum.LengthMatrixPresentation coordinate,
        GluingDatum.LengthMatrixPresentation.matrix presentation = matrix ∧
        data.Valid ∧
        graph_connected target ∧
        genus target = 0 ∧
        Nonempty (Candidate.ClearedFace candidate presentation coordinates)

/-- A semantic chart receipt exposes an actual finite graph with the required
rank-one degree-`degree` pencil.  `Fintype coordinate` cannot be omitted
here: the payload's presentation slot is a `FullDimensionalSourcePresentation`,
whose honest stable labelling needs the coordinate type finite. -/
theorem CarriesClearedPencil.exists_bnExists
    {degree : ℕ} {matrix : Matrix coordinate coordinate ℚ}
    {coordinates : coordinate → ℚ}
    (receipt : CarriesClearedPencil degree matrix coordinates) :
    ∃ source : CFGraph.{0}, BNExists source 1 degree := by
  rcases receipt with
    ⟨target, data, wall, candidate, fullDim, _, _, _, _, ⟨pencil⟩⟩
  exact ⟨pencil.realization.sourceSpec.graph, pencil.bnExists⟩

/-- A finite-atlas state together with an actual cleared pencil at its positive
restart.  Its matrix-only projection is exactly the state consumed by the
finite strict march. -/
structure State (degree : ℕ)
    (matrix : chart → Matrix coordinate coordinate ℚ)
    (baseStart baseFinish : coordinate → ℚ) where
  toMatrixState :
    DraismaVargas.LocalCases.FiniteAtlasMarch.State matrix baseStart baseFinish
  carriesPencil : CarriesClearedPencil degree
    (matrix toMatrixState.label) toMatrixState.currentStart

namespace State

variable {degree : ℕ}
  {matrix : chart → Matrix coordinate coordinate ℚ}
  {baseStart baseFinish : coordinate → ℚ}

/-- A matrix state with a seed pencil starts the semantic march.

`pencil` is the strengthened payload, so the seed must supply a
`FullDimensionalSourcePresentation`.
`InitialState.stateOfFullDimensional` is the form that consumes exactly that and
nothing else. -/
def initial
    (matrixState : DraismaVargas.LocalCases.FiniteAtlasMarch.State
      matrix baseStart baseFinish)
    (pencil : CarriesClearedPencil degree
      (matrix matrixState.label) matrixState.currentStart) :
    State degree matrix baseStart baseFinish where
  toMatrixState := matrixState
  carriesPencil := pencil

/-- A semantic state is terminal exactly when its registered chart contains
the closed endpoint in the nonnegative coordinate orthant. -/
def Terminal (state : State degree matrix baseStart baseFinish) : Prop :=
  DraismaVargas.LocalCases.FiniteAtlasMarch.State.Terminal state.toMatrixState

/-- **The march's guard at a semantic state**: `wall` is the first wall of the
state's own current segment.  Every source-side field of `PresentedProgress`
below is asked only here, and `PresentedProgress.exists_step` discharges it at
the coordinate `RationalAffineWall.exists_first_positiveOrthant_exit` selects.
This is `IsFirstWall` read at the state, and it is reducible, so a consumer may
use either spelling. -/
abbrev FirstWall (current : State degree matrix baseStart baseFinish)
    (wall : coordinate) : Prop :=
  IsFirstWall current.toMatrixState.currentStart
    current.toMatrixState.currentFinish wall

omit [Fintype chart] [DecidableEq chart] in
/-- A terminal semantic state reuses its retained candidate and presentation
to clear the exact nonnegative endpoint, including all zero occurrences. -/
theorem clearedFace (state : State degree matrix baseStart baseFinish)
    (hTerminal : Terminal state) :
    CarriesClearedFace degree (matrix state.toMatrixState.label)
      state.toMatrixState.currentFinish := by
  rcases state.carriesPencil with
    ⟨target, data, wall, candidate, fullDim, hmatrix, hvalid, hconnected,
      hgenus, _⟩
  have hNonnegative : ∀ i, 0 ≤ state.toMatrixState.currentFinish i := by
    exact hTerminal
  exact ⟨target, data, wall, candidate, fullDim.labelling.presentation, hmatrix,
    hvalid, hconnected, hgenus,
    ⟨Candidate.clearedFace candidate fullDim.labelling.presentation
      state.toMatrixState.currentFinish hNonnegative⟩⟩

/-- Semantic atlas steps use the same wall and time relation as matrix steps;
the successor's `carriesPencil` field retains the additional proof object. -/
def Step (current next : State degree matrix baseStart baseFinish) : Prop :=
  DraismaVargas.LocalCases.FiniteAtlasMarch.State.Step
    current.toMatrixState next.toMatrixState

/-- The semantic wrapper has the same fixed event set and termination measure
as the matrix march. -/
noncomputable def march
    (matrix : chart → Matrix coordinate coordinate ℚ)
    (hdet : ∀ label, (matrix label).det ≠ 0)
    (baseStart baseFinish : coordinate → ℚ) :
    FiniteStrictMarch (State degree matrix baseStart baseFinish) where
  eventTimes := DraismaVargas.LocalCases.FiniteAtlasMarch.eventTimes
    matrix baseStart baseFinish
  time := fun state ↦ state.toMatrixState.lastWallTime
  step := Step
  step_time_lt := by
    intro current next hstep
    exact
      (DraismaVargas.LocalCases.FiniteAtlasMarch.State.march matrix hdet
        baseStart baseFinish).step_time_lt hstep
  step_time_mem := by
    intro current next hstep
    exact
      (DraismaVargas.LocalCases.FiniteAtlasMarch.State.march matrix hdet
        baseStart baseFinish).step_time_mem hstep

/-! ### Wall-indexed local continuation

The wall datum at a coordinate is the incoming cover with *that coordinate's*
target occurrence contracted, so it changes with the coordinate: different
occurrences give different contracted targets and different vertex partitions
(`W4Bridge.auxR0SourceInput_of_contraction` concludes about
`contractDatum data hc hab hOne`, and `hc` names the contracted occurrence).
The continuation theorems below therefore take the target, the datum, its
validity, its target's connectedness and genus, and the potential-theory
basepoint as functions of the coordinate.

They are local copies, suffixed `_local`, of the corresponding theorems of
`MarchContinuation` and `FiniteAtlasMarch`, restated with those inputs indexed
by the coordinate.
Each proof is the original one with those six inputs read at the selected
wall; no step depends on the datum before `exists_first_positiveOrthant_exit`
has fixed the wall from the incoming coordinates alone. -/

/-- Wall-indexed local form of
`MarchContinuation.exists_valid_positive_exit_with_pencil_at_first_wall`: the
contracted wall datum is supplied per coordinate, because the contraction that
produces it depends on the occurrence crossed.  The wall is chosen by
`exists_first_positiveOrthant_exit`, which sees only the incoming coordinates,
so the classified exit is read at the selected wall's datum alone. -/
theorem exists_valid_positive_exit_with_pencil_at_first_wall_local
    (start finish : coordinate → ℚ)
    (targetAt : ∀ wall, IsFirstWall start finish wall → CFGraph.{0})
    (dataAt : ∀ wall hw, GluingDatum (targetAt wall hw) degree)
    (hValidAt : ∀ wall hw, (dataAt wall hw).Valid)
    (hTargetConnectedAt : ∀ wall hw, graph_connected (targetAt wall hw))
    (hTargetGenusAt : ∀ wall hw, genus (targetAt wall hw) = 0)
    (rootAt : ∀ wall hw, (targetAt wall hw).V)
    (hstart : ∀ i, 0 < start i) (houtside : ∃ i, finish i < 0)
    (hsimple : SimpleNegativeCrossings start finish)
    (targetWallAt : ∀ wall hw, (targetAt wall hw).V)
    (caseAt : ∀ wall, IsFirstWall start finish wall → SourceCase)
    (familyAt : ∀ wall hw, GaugeFamily (coordinate := coordinate)
      (caseAt wall hw).arity (dataAt wall hw) (targetWallAt wall hw))
    (hwallColumn : ∀ wall hw, (familyAt wall hw).wallColumn = wall)
    (incomingAt : ∀ wall hw, Fin (caseAt wall hw).arity)
    (hincomingNonzero : ∀ wall hw,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall hw).presentation (incomingAt wall hw))).det ≠ 0)
    (outgoingVelocity : ∀ wall hw,
      Fin (caseAt wall hw).arity → coordinate → ℚ)
    (hSystems : ∀ wall hw outgoing,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall hw).presentation outgoing)).det ≠ 0 →
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall hw).presentation (incomingAt wall hw))).mulVec
          (fun i => finish i - start i) =
        (GluingDatum.LengthMatrixPresentation.matrix
          ((familyAt wall hw).presentation outgoing)).mulVec
            (outgoingVelocity wall hw outgoing)) :
    ∃ wall : coordinate, ∃ hw : IsFirstWall start finish wall, ∃ time : ℚ,
      0 < time ∧ time < 1 ∧
      RationalAffineWall.segment start finish time wall = 0 ∧
      ∃ outgoing : Fin (caseAt wall hw).arity,
        ((familyAt wall hw).candidate outgoing).datum.Valid ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall hw).presentation (incomingAt wall hw))).det *
          (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall hw).presentation outgoing)).det < 0 ∧
        ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
          (∀ i, 0 < (RationalAffineWall.segment start finish time +
            t • outgoingVelocity wall hw outgoing) i) ∧
          (GluingDatum.LengthMatrixPresentation.matrix
              ((familyAt wall hw).presentation outgoing)).mulVec
                (RationalAffineWall.segment start finish time +
                  t • outgoingVelocity wall hw outgoing) =
            (GluingDatum.LengthMatrixPresentation.matrix
              ((familyAt wall hw).presentation (incomingAt wall hw))).mulVec
                (RationalAffineWall.segment start finish time) +
              t • (GluingDatum.LengthMatrixPresentation.matrix
                ((familyAt wall hw).presentation (incomingAt wall hw))).mulVec
                  (fun i => finish i - start i) ∧
          Nonempty (Candidate.ClearedPencil
            ((familyAt wall hw).candidate outgoing)
            ((familyAt wall hw).presentation outgoing)
            (RationalAffineWall.segment start finish time +
              t • outgoingVelocity wall hw outgoing)) := by
  obtain ⟨wall, time, htimePos, htimeLt, hzero, hother, _⟩ :=
    exists_first_positiveOrthant_exit start finish hstart houtside hsimple
  have hw : IsFirstWall start finish wall :=
    isFirstWall_of_exit htimePos htimeLt hzero hother
  have hfinishWall : finish wall < 0 := by
    by_contra hnot
    have hfinishNonneg : 0 ≤ finish wall := le_of_not_gt hnot
    have hstartPart : 0 < (1 - time) * start wall :=
      mul_pos (sub_pos.mpr htimeLt) (hstart wall)
    have hfinishPart : 0 ≤ time * finish wall :=
      mul_nonneg htimePos.le hfinishNonneg
    unfold RationalAffineWall.segment at hzero
    nlinarith
  -- `ClassifiedContinuation.PresentedWallEvent` bundles exactly these
  -- arguments, but its `family` slot is a `PresentedFamily` over one datum, so
  -- the gauge-mixed family is handed to `BalancedGlobal`'s exit directly.  The
  -- fields below are that structure's, in its order.
  obtain ⟨outgoing, hvalid, hsign, hstep⟩ :=
    (familyAt wall hw).exists_valid_positive_exit_with_pencil (hValidAt wall hw)
      (hTargetConnectedAt wall hw) (hTargetGenusAt wall hw) (rootAt wall hw)
      (incomingAt wall hw) (hincomingNonzero wall hw)
      (RationalAffineWall.segment start finish time)
      (fun i => finish i - start i) (outgoingVelocity wall hw)
      (by
        rw [hwallColumn wall hw]
        exact hzero)
      (by
        intro i hi
        apply hother i
        intro hiWall
        apply hi
        exact hiWall.trans (hwallColumn wall hw).symm)
      (hSystems wall hw)
      (by
        rw [hwallColumn wall hw]
        linarith [hstart wall, hfinishWall])
  exact ⟨wall, hw, time, htimePos, htimeLt, hzero, outgoing, hvalid, hsign,
    hstep⟩

/-- Wall-indexed local form of
`MarchContinuation.exists_valid_resumed_segment_with_pencil_at_first_wall`.
Only the first-wall exit below it sees the datum; the rebasing is matrix
algebra at the selected wall. -/
theorem exists_valid_resumed_segment_with_pencil_at_first_wall_local
    (start finish : coordinate → ℚ)
    (targetAt : ∀ wall, IsFirstWall start finish wall → CFGraph.{0})
    (dataAt : ∀ wall hw, GluingDatum (targetAt wall hw) degree)
    (hValidAt : ∀ wall hw, (dataAt wall hw).Valid)
    (hTargetConnectedAt : ∀ wall hw, graph_connected (targetAt wall hw))
    (hTargetGenusAt : ∀ wall hw, genus (targetAt wall hw) = 0)
    (rootAt : ∀ wall hw, (targetAt wall hw).V)
    (hstart : ∀ i, 0 < start i) (houtside : ∃ i, finish i < 0)
    (hsimple : SimpleNegativeCrossings start finish)
    (targetWallAt : ∀ wall hw, (targetAt wall hw).V)
    (caseAt : ∀ wall, IsFirstWall start finish wall → SourceCase)
    (familyAt : ∀ wall hw, GaugeFamily (coordinate := coordinate)
      (caseAt wall hw).arity (dataAt wall hw) (targetWallAt wall hw))
    (hwallColumn : ∀ wall hw, (familyAt wall hw).wallColumn = wall)
    (incomingAt : ∀ wall hw, Fin (caseAt wall hw).arity)
    (hincomingNonzero : ∀ wall hw,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall hw).presentation (incomingAt wall hw))).det ≠ 0)
    (outgoingVelocity : ∀ wall hw,
      Fin (caseAt wall hw).arity → coordinate → ℚ)
    (hSystems : ∀ wall hw outgoing,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall hw).presentation outgoing)).det ≠ 0 →
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall hw).presentation (incomingAt wall hw))).mulVec
          (fun i => finish i - start i) =
        (GluingDatum.LengthMatrixPresentation.matrix
          ((familyAt wall hw).presentation outgoing)).mulVec
            (outgoingVelocity wall hw outgoing)) :
    ∃ wall : coordinate, ∃ hw : IsFirstWall start finish wall, ∃ time : ℚ,
      ∃ outgoing : Fin (caseAt wall hw).arity, ∃ ε : ℚ,
        0 < time ∧ time < 1 ∧ 0 < ε ∧ ε < 1 - time ∧
        RationalAffineWall.segment start finish time wall = 0 ∧
        ((familyAt wall hw).candidate outgoing).datum.Valid ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall hw).presentation (incomingAt wall hw))).det *
          (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall hw).presentation outgoing)).det < 0 ∧
        (∀ i, 0 < (RationalAffineWall.segment start finish time +
          ε • outgoingVelocity wall hw outgoing) i) ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall hw).presentation outgoing)).mulVec
              (RationalAffineWall.segment start finish time +
                ε • outgoingVelocity wall hw outgoing) =
          (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall hw).presentation (incomingAt wall hw))).mulVec
              (RationalAffineWall.segment start finish (time + ε)) ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall hw).presentation outgoing)).mulVec
              (RationalAffineWall.segment start finish time +
                (1 - time) • outgoingVelocity wall hw outgoing) =
          (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall hw).presentation (incomingAt wall hw))).mulVec finish ∧
        Nonempty (Candidate.ClearedPencil
          ((familyAt wall hw).candidate outgoing)
          ((familyAt wall hw).presentation outgoing)
          (RationalAffineWall.segment start finish time +
            ε • outgoingVelocity wall hw outgoing)) := by
  obtain ⟨wall, hw, time, htimePos, htimeLt, hwallZero, outgoing, hvalid, hsign,
      δ, hδ, hstep⟩ :=
    exists_valid_positive_exit_with_pencil_at_first_wall_local start finish
      targetAt dataAt hValidAt hTargetConnectedAt hTargetGenusAt rootAt
      hstart houtside hsimple targetWallAt caseAt familyAt hwallColumn
      incomingAt hincomingNonzero outgoingVelocity hSystems
  let ε : ℚ := min δ ((1 - time) / 2)
  have hHalfPos : 0 < (1 - time) / 2 := by linarith
  have hεPos : 0 < ε := lt_min hδ hHalfPos
  have hεLe : ε ≤ δ := min_le_left _ _
  have hεLtRemaining : ε < 1 - time := by
    exact (min_le_right _ _).trans_lt (by linarith)
  obtain ⟨hpositive, hmap, hpencil⟩ := hstep ε hεPos hεLe
  let incomingMatrix := GluingDatum.LengthMatrixPresentation.matrix
    ((familyAt wall hw).presentation (incomingAt wall hw))
  let outgoingMatrix := GluingDatum.LengthMatrixPresentation.matrix
    ((familyAt wall hw).presentation outgoing)
  let wallPoint := RationalAffineWall.segment start finish time
  let incomingVelocity : coordinate → ℚ := fun i => finish i - start i
  let selectedOutgoingVelocity := outgoingVelocity wall hw outgoing
  have hSystem : incomingMatrix.mulVec incomingVelocity =
      outgoingMatrix.mulVec selectedOutgoingVelocity :=
    hSystems wall hw outgoing (det_ne_zero_of_mul_det_neg hsign)
  have hWallMap : outgoingMatrix.mulVec wallPoint =
      incomingMatrix.mulVec wallPoint := by
    have hExpanded := hmap
    change outgoingMatrix.mulVec
        (wallPoint + ε • selectedOutgoingVelocity) =
      incomingMatrix.mulVec wallPoint +
        ε • incomingMatrix.mulVec incomingVelocity at hExpanded
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hSystem] at hExpanded
    ext i
    have hi := congrFun hExpanded i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
    linarith
  have hSegmentStep :
      RationalAffineWall.segment start finish (time + ε) =
        wallPoint + ε • incomingVelocity := by
    ext i
    simp only [RationalAffineWall.segment, wallPoint, incomingVelocity,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hStepMap :
      outgoingMatrix.mulVec (wallPoint + ε • selectedOutgoingVelocity) =
        incomingMatrix.mulVec
          (RationalAffineWall.segment start finish (time + ε)) := by
    calc
      outgoingMatrix.mulVec (wallPoint + ε • selectedOutgoingVelocity) =
          incomingMatrix.mulVec wallPoint +
            ε • incomingMatrix.mulVec incomingVelocity := hmap
      _ = incomingMatrix.mulVec
          (RationalAffineWall.segment start finish (time + ε)) := by
            rw [hSegmentStep, Matrix.mulVec_add, Matrix.mulVec_smul]
  have hFinishCoordinates :
      finish = wallPoint + (1 - time) • incomingVelocity := by
    ext i
    simp only [RationalAffineWall.segment, wallPoint, incomingVelocity,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hFinishMap :
      outgoingMatrix.mulVec
          (wallPoint + (1 - time) • selectedOutgoingVelocity) =
        incomingMatrix.mulVec finish := by
    calc
      outgoingMatrix.mulVec
          (wallPoint + (1 - time) • selectedOutgoingVelocity) =
          outgoingMatrix.mulVec wallPoint +
            (1 - time) • outgoingMatrix.mulVec selectedOutgoingVelocity := by
              rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      _ = incomingMatrix.mulVec wallPoint +
          (1 - time) • incomingMatrix.mulVec incomingVelocity := by
            rw [hWallMap, hSystem]
      _ = incomingMatrix.mulVec
          (wallPoint + (1 - time) • incomingVelocity) := by
            rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      _ = incomingMatrix.mulVec finish := by rw [← hFinishCoordinates]
  exact ⟨wall, hw, time, outgoing, ε, htimePos, htimeLt, hεPos,
    hεLtRemaining, hwallZero, hvalid, hsign, hpositive, hStepMap, hFinishMap,
    hpencil⟩

/-- Wall-indexed local form of
`MarchContinuation.exists_valid_resumed_global_segment_with_pencil_at_first_wall`. -/
theorem exists_valid_resumed_global_segment_with_pencil_at_first_wall_local
    (currentStart currentFinish : coordinate → ℚ)
    (targetAt : ∀ wall, IsFirstWall currentStart currentFinish wall → CFGraph.{0})
    (dataAt : ∀ wall hw, GluingDatum (targetAt wall hw) degree)
    (hValidAt : ∀ wall hw, (dataAt wall hw).Valid)
    (hTargetConnectedAt : ∀ wall hw, graph_connected (targetAt wall hw))
    (hTargetGenusAt : ∀ wall hw, genus (targetAt wall hw) = 0)
    (rootAt : ∀ wall hw, (targetAt wall hw).V)
    (baseStart baseFinish : coordinate → ℚ)
    (currentTime : ℚ) (hcurrentTime : currentTime < 1)
    (hstart : ∀ i, 0 < currentStart i)
    (houtside : ∃ i, currentFinish i < 0)
    (hsimple : SimpleNegativeCrossings currentStart currentFinish)
    (targetWallAt : ∀ wall hw, (targetAt wall hw).V)
    (caseAt : ∀ wall, IsFirstWall currentStart currentFinish wall → SourceCase)
    (familyAt : ∀ wall hw, GaugeFamily (coordinate := coordinate)
      (caseAt wall hw).arity (dataAt wall hw) (targetWallAt wall hw))
    (hwallColumn : ∀ wall hw, (familyAt wall hw).wallColumn = wall)
    (incomingAt : ∀ wall hw, Fin (caseAt wall hw).arity)
    (hincomingNonzero : ∀ wall hw,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall hw).presentation (incomingAt wall hw))).det ≠ 0)
    (currentMatrix : Matrix coordinate coordinate ℚ)
    (hincomingMatrix : ∀ wall hw,
      GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall hw).presentation (incomingAt wall hw)) = currentMatrix)
    (hcurrentStartMap : currentMatrix.mulVec currentStart =
      RationalAffineWall.segment baseStart baseFinish currentTime)
    (hcurrentFinishMap : currentMatrix.mulVec currentFinish = baseFinish)
    (outgoingVelocity : ∀ wall hw,
      Fin (caseAt wall hw).arity → coordinate → ℚ)
    (hSystems : ∀ wall hw outgoing,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall hw).presentation outgoing)).det ≠ 0 →
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall hw).presentation (incomingAt wall hw))).mulVec
          (fun i => currentFinish i - currentStart i) =
        (GluingDatum.LengthMatrixPresentation.matrix
          ((familyAt wall hw).presentation outgoing)).mulVec
            (outgoingVelocity wall hw outgoing)) :
    ∃ wall : coordinate, ∃ hw : IsFirstWall currentStart currentFinish wall,
      ∃ localTime : ℚ, ∃ outgoing : Fin (caseAt wall hw).arity, ∃ ε : ℚ,
        0 < localTime ∧ localTime < 1 ∧
        0 < ε ∧ ε < 1 - localTime ∧
        RationalAffineWall.segment currentStart currentFinish
          localTime wall = 0 ∧
        currentTime < currentTime + (1 - currentTime) * localTime ∧
        currentTime + (1 - currentTime) * localTime <
          currentTime + (1 - currentTime) * (localTime + ε) ∧
        currentTime + (1 - currentTime) * (localTime + ε) < 1 ∧
        ((familyAt wall hw).candidate outgoing).datum.Valid ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall hw).presentation (incomingAt wall hw))).det *
          (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall hw).presentation outgoing)).det < 0 ∧
        (∀ i, 0 < (RationalAffineWall.segment currentStart currentFinish
          localTime + ε • outgoingVelocity wall hw outgoing) i) ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall hw).presentation outgoing)).mulVec
              (RationalAffineWall.segment currentStart currentFinish localTime +
                ε • outgoingVelocity wall hw outgoing) =
          RationalAffineWall.segment baseStart baseFinish
            (currentTime + (1 - currentTime) * (localTime + ε)) ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall hw).presentation outgoing)).mulVec
              (RationalAffineWall.segment currentStart currentFinish localTime +
                (1 - localTime) • outgoingVelocity wall hw outgoing) =
          baseFinish ∧
        Nonempty (Candidate.ClearedPencil
          ((familyAt wall hw).candidate outgoing)
          ((familyAt wall hw).presentation outgoing)
          (RationalAffineWall.segment currentStart currentFinish localTime +
            ε • outgoingVelocity wall hw outgoing)) := by
  obtain ⟨wall, hw, localTime, outgoing, ε, hlocalTimePos, hlocalTimeLt,
      hεPos, hεLt, hwallZero, hvalid, hsign, hpositive, hrestartMap,
      hfinishMap, hpencil⟩ :=
    exists_valid_resumed_segment_with_pencil_at_first_wall_local currentStart
      currentFinish targetAt dataAt hValidAt hTargetConnectedAt hTargetGenusAt
      rootAt hstart houtside hsimple targetWallAt caseAt familyAt
      hwallColumn incomingAt hincomingNonzero outgoingVelocity hSystems
  have hremainingPos : 0 < 1 - currentTime := sub_pos.mpr hcurrentTime
  have hlocalRestartLt : localTime + ε < 1 := by linarith
  have hwallAdvance :
      currentTime < currentTime + (1 - currentTime) * localTime := by
    nlinarith [mul_pos hremainingPos hlocalTimePos]
  have hrestartAdvance :
      currentTime + (1 - currentTime) * localTime <
        currentTime + (1 - currentTime) * (localTime + ε) := by
    nlinarith [mul_pos hremainingPos hεPos]
  have hrestartLt :
      currentTime + (1 - currentTime) * (localTime + ε) < 1 := by
    have hlocalRemaining : 0 < 1 - (localTime + ε) :=
      sub_pos.mpr hlocalRestartLt
    nlinarith [mul_pos hremainingPos hlocalRemaining]
  have hcurrentSegmentMap (time : ℚ) :
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall hw).presentation (incomingAt wall hw))).mulVec
          (RationalAffineWall.segment currentStart currentFinish time) =
        RationalAffineWall.segment baseStart baseFinish
          (currentTime + (1 - currentTime) * time) := by
    rw [hincomingMatrix wall hw,
      DraismaVargas.LocalCases.MarchContinuation.mulVec_segment,
      hcurrentStartMap, hcurrentFinishMap,
      DraismaVargas.LocalCases.MarchContinuation.segment_rebase_right]
  have hglobalRestartMap :
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall hw).presentation outgoing)).mulVec
          (RationalAffineWall.segment currentStart currentFinish localTime +
            ε • outgoingVelocity wall hw outgoing) =
        RationalAffineWall.segment baseStart baseFinish
          (currentTime + (1 - currentTime) * (localTime + ε)) := by
    exact hrestartMap.trans (hcurrentSegmentMap (localTime + ε))
  have hglobalFinishMap :
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall hw).presentation outgoing)).mulVec
          (RationalAffineWall.segment currentStart currentFinish localTime +
            (1 - localTime) • outgoingVelocity wall hw outgoing) =
        baseFinish := by
    calc
      _ = (GluingDatum.LengthMatrixPresentation.matrix
          ((familyAt wall hw).presentation (incomingAt wall hw))).mulVec
            currentFinish := hfinishMap
      _ = currentMatrix.mulVec currentFinish := by rw [hincomingMatrix wall hw]
      _ = baseFinish := hcurrentFinishMap
  exact ⟨wall, hw, localTime, outgoing, ε, hlocalTimePos, hlocalTimeLt,
    hεPos, hεLt, hwallZero, hwallAdvance, hrestartAdvance, hrestartLt, hvalid,
    hsign, hpositive, hglobalRestartMap, hglobalFinishMap, hpencil⟩

omit [Fintype chart] [DecidableEq chart] in
/-- Wall-indexed local form of
`FiniteAtlasMarch.State.exists_step_of_presented_classified_first_wall`,
producing the matrix-level atlas successor together with the selected
candidate's cleared pencil. -/
theorem exists_step_of_presented_classified_first_wall_matrix_local
    (matrix : chart → Matrix coordinate coordinate ℚ)
    (baseStart baseFinish : coordinate → ℚ)
    (current : DraismaVargas.LocalCases.FiniteAtlasMarch.State
      matrix baseStart baseFinish)
    (targetAt : ∀ wall,
      IsFirstWall current.currentStart current.currentFinish wall → CFGraph.{0})
    (dataAt : ∀ wall hw, GluingDatum (targetAt wall hw) degree)
    (hValidAt : ∀ wall hw, (dataAt wall hw).Valid)
    (hTargetConnectedAt : ∀ wall hw, graph_connected (targetAt wall hw))
    (hTargetGenusAt : ∀ wall hw, genus (targetAt wall hw) = 0)
    (rootAt : ∀ wall hw, (targetAt wall hw).V)
    (houtside : ∃ i, current.currentFinish i < 0)
    (hsimple : SimpleNegativeCrossings
      current.currentStart current.currentFinish)
    (targetWallAt : ∀ wall hw, (targetAt wall hw).V)
    (caseAt : ∀ wall,
      IsFirstWall current.currentStart current.currentFinish wall → SourceCase)
    (familyAt : ∀ wall hw, GaugeFamily (coordinate := coordinate)
      (caseAt wall hw).arity (dataAt wall hw) (targetWallAt wall hw))
    (hwallColumn : ∀ wall hw, (familyAt wall hw).wallColumn = wall)
    (incomingAt : ∀ wall hw, Fin (caseAt wall hw).arity)
    (hincomingNonzero : ∀ wall hw,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall hw).presentation (incomingAt wall hw))).det ≠ 0)
    (hincomingMatrix : ∀ wall hw,
      GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall hw).presentation (incomingAt wall hw)) =
          matrix current.label)
    (outgoingVelocity : ∀ wall hw,
      Fin (caseAt wall hw).arity → coordinate → ℚ)
    (hSystems : ∀ wall hw outgoing,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall hw).presentation outgoing)).det ≠ 0 →
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall hw).presentation (incomingAt wall hw))).mulVec
          (fun i => current.currentFinish i - current.currentStart i) =
        (GluingDatum.LengthMatrixPresentation.matrix
          ((familyAt wall hw).presentation outgoing)).mulVec
            (outgoingVelocity wall hw outgoing))
    (outgoingLabel : ∀ wall hw, Fin (caseAt wall hw).arity → chart)
    (houtgoingMatrix : ∀ wall hw outgoing,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall hw).presentation outgoing)).det ≠ 0 →
      matrix (outgoingLabel wall hw outgoing) =
        GluingDatum.LengthMatrixPresentation.matrix
          ((familyAt wall hw).presentation outgoing)) :
    ∃ wall : coordinate, ∃ hw : IsFirstWall current.currentStart current.currentFinish wall,
      ∃ outgoing : Fin (caseAt wall hw).arity,
      ∃ next : DraismaVargas.LocalCases.FiniteAtlasMarch.State
        matrix baseStart baseFinish,
        DraismaVargas.LocalCases.FiniteAtlasMarch.State.Step current next ∧
        next.label = outgoingLabel wall hw outgoing ∧
        ((familyAt wall hw).candidate outgoing).datum.Valid ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall hw).presentation (incomingAt wall hw))).det *
          (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall hw).presentation outgoing)).det < 0 ∧
        Nonempty (Candidate.ClearedPencil
          ((familyAt wall hw).candidate outgoing)
          ((familyAt wall hw).presentation outgoing) next.currentStart) := by
  classical
  obtain ⟨wall, hw, localTime, outgoing, ε, hlocalTimePos, hlocalTimeLt,
      hεPos, hεLt, hwallZero, hwallAdvance, hrestartAdvance, hrestartLt,
      hvalid, hsign, hpositive, hrestartMap, hfinishMap, hpencil⟩ :=
    exists_valid_resumed_global_segment_with_pencil_at_first_wall_local
      current.currentStart current.currentFinish
      targetAt dataAt hValidAt hTargetConnectedAt hTargetGenusAt rootAt
      baseStart baseFinish current.restartTime
      current.restart_lt_one current.currentStart_positive houtside hsimple
      targetWallAt caseAt familyAt hwallColumn incomingAt hincomingNonzero
      (matrix current.label) hincomingMatrix current.currentStart_map
      current.currentFinish_map outgoingVelocity hSystems
  let outgoingStart : coordinate → ℚ :=
    segment current.currentStart current.currentFinish localTime +
      ε • outgoingVelocity wall hw outgoing
  let outgoingFinish : coordinate → ℚ :=
    segment current.currentStart current.currentFinish localTime +
      (1 - localTime) • outgoingVelocity wall hw outgoing
  let next : DraismaVargas.LocalCases.FiniteAtlasMarch.State
      matrix baseStart baseFinish :=
    { label := outgoingLabel wall hw outgoing
      lastWallTime :=
        current.restartTime + (1 - current.restartTime) * localTime
      restartTime :=
        current.restartTime + (1 - current.restartTime) * (localTime + ε)
      lastWall_lt_restart := hrestartAdvance
      restart_lt_one := hrestartLt
      currentStart := outgoingStart
      currentFinish := outgoingFinish
      currentStart_positive := by simpa [outgoingStart] using hpositive
      currentStart_map := by
        rw [houtgoingMatrix wall hw outgoing
          (det_ne_zero_of_mul_det_neg hsign)]
        simpa [outgoingStart] using hrestartMap
      currentFinish_map := by
        rw [houtgoingMatrix wall hw outgoing
          (det_ne_zero_of_mul_det_neg hsign)]
        simpa [outgoingFinish] using hfinishMap }
  have hstep : DraismaVargas.LocalCases.FiniteAtlasMarch.State.Step
      current next := by
    refine ⟨wall, localTime, hlocalTimePos, hwallZero, ?_⟩
    rfl
  have hpencilNext : Nonempty (Candidate.ClearedPencil
      ((familyAt wall hw).candidate outgoing)
      ((familyAt wall hw).presentation outgoing) next.currentStart) := by
    simpa [next, outgoingStart] using hpencil
  exact ⟨wall, hw, outgoing, next, hstep, rfl, hvalid, hsign, hpencilNext⟩

/-- All source-dependent data required to continue one nonterminal semantic
state.  This is the target of the exhaustive local classification of Part I:
it includes actual presented candidate families and
their registration in the fixed finite chart catalogue.  Outgoing velocities
and their system identities are derived canonically from the registered
nonsingular chart matrices rather than supplied by the source classifier.

**Everything source-side is indexed by the coordinate whose wall is crossed.**
The wall datum at a coordinate is the incoming cover with *that coordinate's*
target occurrence contracted (`W4Bridge.auxR0SourceInput_of_contraction`
concludes about `contractDatum data hc hab hOne`, and `hc` names the
contracted occurrence), so different occurrences give different contracted
targets and different vertex partitions.  One target, one datum and one
potential-theory basepoint cannot serve all walls, and the fields below
therefore read `targetAt wall hw`, `dataAt wall hw`, `rootAt wall hw` exactly as
the wall-indexed continuation theorems above do.  Only `simpleCrossings`, which
is a genericity condition on the incoming segment alone, stays unindexed.

**And every source-side field is asked only at a first wall.**
Each wall-indexed field carries `hw : current.FirstWall wall` -- the guard
`IsFirstWall` at this state's own segment -- because a wall input at a
coordinate carries an interior wall metric of the incoming cover, and a
coordinate over which a whole stable class of the cover lies has none
(`InteriorProgress.not_admissibleColumn_of_stablePath_over_column`): the march
never crosses such a coordinate, and demanding wall data there was not merely
unproved but false.  `exists_step` discharges the guard at the coordinate
`RationalAffineWall.exists_first_positiveOrthant_exit` selects, and returns it
alongside the selected wall, so a consumer reads the fields at the same proof.
Proof irrelevance makes the choice of `hw` immaterial. -/
structure PresentedProgress
    (current : State degree matrix baseStart baseFinish) where
  /-- The wall's contracted target, **at the first wall only**.  `IsFirstWall`
  is the guard the whole source side is restricted by; see the note above
  `IsFirstWall`. -/
  targetAt : ∀ wall, current.FirstWall wall → CFGraph.{0}
  dataAt : ∀ wall hw, GluingDatum (targetAt wall hw) degree
  validAt : ∀ wall hw, (dataAt wall hw).Valid
  targetConnectedAt : ∀ wall hw, graph_connected (targetAt wall hw)
  targetGenusAt : ∀ wall hw, genus (targetAt wall hw) = 0
  rootAt : ∀ wall hw, (targetAt wall hw).V
  simpleCrossings : SimpleNegativeCrossings
    current.toMatrixState.currentStart current.toMatrixState.currentFinish
  targetWallAt : ∀ wall hw, (targetAt wall hw).V
  caseAt : ∀ wall, current.FirstWall wall → SourceCase
  /-- **The wall's balanced family, with one base datum per member.**  The
  members of several of the paper's wall figures do not share a gluing datum:
  Figure 28's four members sit over branch-swapped copies of `dataAt wall hw`,
  and so does the middle member of `GlobalM11Arbitrary.candidates`.  So this is a
  `BalancedGlobal.GaugeFamily`, whose `candidate i` is a
  `Candidate (targetAt wall hw) degree (base i) (targetWallAt wall hw)` and whose
  `valid_of_old` carries `validAt wall hw` to each `base i`.  A family over one
  datum reaches the field through `BalancedGlobal.PresentedFamily.toGaugeFamily`,
  verbatim. -/
  familyAt : ∀ wall hw, GaugeFamily (coordinate := coordinate)
    (caseAt wall hw).arity (dataAt wall hw) (targetWallAt wall hw)
  wallColumn : ∀ wall hw, (familyAt wall hw).wallColumn = wall
  incomingAt : ∀ wall hw, Fin (caseAt wall hw).arity
  incomingNonzero : ∀ wall hw,
    (GluingDatum.LengthMatrixPresentation.matrix
      ((familyAt wall hw).presentation (incomingAt wall hw))).det ≠ 0
  incomingMatrix : ∀ wall hw,
    GluingDatum.LengthMatrixPresentation.matrix
      ((familyAt wall hw).presentation (incomingAt wall hw)) =
        matrix current.toMatrixState.label
  outgoingLabel : ∀ wall hw, Fin (caseAt wall hw).arity → chart
  outgoingMatrix : ∀ wall hw outgoing,
    (GluingDatum.LengthMatrixPresentation.matrix
      ((familyAt wall hw).presentation outgoing)).det ≠ 0 →
    matrix (outgoingLabel wall hw outgoing) =
      GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall hw).presentation outgoing)
  /-- **The outgoing full-dimensional source presentations, gated on
  nonsingularity.**  The successor state carries `CarriesClearedPencil`, whose
  presentation slot is a `FullDimensionalSourcePresentation`; `familyAt`
  carries only a bare `LengthMatrixPresentation` per member, so the classifier
  has to hand the full-dimensional package over with every exit it can take.
  The member's datum is `((familyAt wall hw).candidate outgoing).datum`, over
  that member's own `base`, so this field is asked at the gauge copy the member
  actually lives on.  This is exactly the requirement to *preserve the
  full-dimensional presentation across a wall step*, appearing as a field; the
  positive exits of the local cases (for instance `W4PositiveExit`) produce
  one.

  The determinant hypothesis is the gate `outgoingMatrix` already carries, and
  it is not optional: a `FullDimensionalSourcePresentation` has
  `det_ne_zero` about its own labelling, so a *total* `fullDimAt` together with
  `fullDimPresentation` would force every member of every family to be
  nonsingular, which `ClassifiedContinuation.SingularMember.singularFamily`
  refutes (`W3WallInput.no_total_fullDim_of_singularFamily`).  The march reads
  the field only at the selected outgoing member, whose nonsingularity is
  `det_ne_zero_of_mul_det_neg` of the sign condition. -/
  fullDimAt : ∀ wall hw (outgoing : Fin (caseAt wall hw).arity),
    (GluingDatum.LengthMatrixPresentation.matrix
      ((familyAt wall hw).presentation outgoing)).det ≠ 0 →
    FullDimensionalSourcePresentation
      ((familyAt wall hw).candidate outgoing).datum coordinate
  /-- and each one displays its member's registered presentation, so the chart
  matrix of the successor is the honest stable length matrix of the outgoing
  full-dimensional source. -/
  fullDimPresentation : ∀ wall hw outgoing
    (hdet : (GluingDatum.LengthMatrixPresentation.matrix
      ((familyAt wall hw).presentation outgoing)).det ≠ 0),
    (fullDimAt wall hw outgoing hdet).labelling.presentation =
      (familyAt wall hw).presentation outgoing

omit [Fintype chart] [DecidableEq chart] in
/-- A presented classified wall constructs a semantic successor, not merely a
matrix state.  The selected candidate's presentation is registered against the
successor label and its cleared pencil populates the successor payload.

The source-side inputs are wall-indexed, for the reason recorded above
`exists_valid_positive_exit_with_pencil_at_first_wall_local`: the contracted
datum depends on the occurrence crossed.  The `CarriesClearedPencil` receipt
of the successor is therefore assembled from the selected wall's target,
datum and incoming-stage triple.

`fullDimAt` and `hfullDimPresentation` are the one genuinely new input the
strengthened payload forces: the successor's receipt carries a
`FullDimensionalSourcePresentation` of the *outgoing* candidate's datum, and a
balanced family does not have one.  Nothing here derives it, and nothing can:
it is the whole content of preserving the full-dimensional presentation across
the step.  Both are gated on the outgoing member's
nonsingularity, and the selected exit has it: `det_ne_zero_of_mul_det_neg` of
the sign condition the matrix-level step returns.

The last conjunct of the conclusion exposes the cleared pencil on the **named**
selected pair `(wall, outgoing)` and on the selected member's own
full-dimensional presentation, together with the nonsingularity proof that
`fullDimAt` is read at.  It is the second half of the successor's
`carriesPencil`; returning it keeps the successor's payload from being
existential over an anonymous candidate.  A graph-tracked wrapper needs the
pencil attached to the same `fullDimAt` witness its tracking is stated at. -/
theorem exists_step_of_presented_classified_first_wall
    (matrix : chart → Matrix coordinate coordinate ℚ)
    (baseStart baseFinish : coordinate → ℚ)
    (current : State degree matrix baseStart baseFinish)
    (targetAt : ∀ wall, current.FirstWall wall → CFGraph.{0})
    (dataAt : ∀ wall hw, GluingDatum (targetAt wall hw) degree)
    (hValidAt : ∀ wall hw, (dataAt wall hw).Valid)
    (hTargetConnectedAt : ∀ wall hw, graph_connected (targetAt wall hw))
    (hTargetGenusAt : ∀ wall hw, genus (targetAt wall hw) = 0)
    (rootAt : ∀ wall hw, (targetAt wall hw).V)
    (houtside : ∃ i, current.toMatrixState.currentFinish i < 0)
    (hsimple : SimpleNegativeCrossings
      current.toMatrixState.currentStart current.toMatrixState.currentFinish)
    (targetWallAt : ∀ wall hw, (targetAt wall hw).V)
    (caseAt : ∀ wall, current.FirstWall wall → SourceCase)
    (familyAt : ∀ wall hw, GaugeFamily (coordinate := coordinate)
      (caseAt wall hw).arity (dataAt wall hw) (targetWallAt wall hw))
    (hwallColumn : ∀ wall hw, (familyAt wall hw).wallColumn = wall)
    (incomingAt : ∀ wall hw, Fin (caseAt wall hw).arity)
    (hincomingNonzero : ∀ wall hw,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall hw).presentation (incomingAt wall hw))).det ≠ 0)
    (hincomingMatrix : ∀ wall hw,
      GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall hw).presentation (incomingAt wall hw)) =
          matrix current.toMatrixState.label)
    (outgoingVelocity : ∀ wall hw,
      Fin (caseAt wall hw).arity → coordinate → ℚ)
    (hSystems : ∀ wall hw outgoing,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall hw).presentation outgoing)).det ≠ 0 →
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall hw).presentation (incomingAt wall hw))).mulVec
          (fun i => current.toMatrixState.currentFinish i -
            current.toMatrixState.currentStart i) =
        (GluingDatum.LengthMatrixPresentation.matrix
          ((familyAt wall hw).presentation outgoing)).mulVec
            (outgoingVelocity wall hw outgoing))
    (outgoingLabel : ∀ wall hw, Fin (caseAt wall hw).arity → chart)
    (houtgoingMatrix : ∀ wall hw outgoing,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall hw).presentation outgoing)).det ≠ 0 →
      matrix (outgoingLabel wall hw outgoing) =
        GluingDatum.LengthMatrixPresentation.matrix
          ((familyAt wall hw).presentation outgoing))
    (fullDimAt : ∀ wall hw (outgoing : Fin (caseAt wall hw).arity),
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall hw).presentation outgoing)).det ≠ 0 →
      FullDimensionalSourcePresentation
        ((familyAt wall hw).candidate outgoing).datum coordinate)
    (hfullDimPresentation : ∀ wall hw outgoing
      (hdet : (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall hw).presentation outgoing)).det ≠ 0),
      (fullDimAt wall hw outgoing hdet).labelling.presentation =
        (familyAt wall hw).presentation outgoing) :
    ∃ wall : coordinate, ∃ hw : current.FirstWall wall,
      ∃ outgoing : Fin (caseAt wall hw).arity,
      ∃ next : State degree matrix baseStart baseFinish,
        Step current next ∧
        next.toMatrixState.label = outgoingLabel wall hw outgoing ∧
        ((familyAt wall hw).candidate outgoing).datum.Valid ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall hw).presentation (incomingAt wall hw))).det *
          (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall hw).presentation outgoing)).det < 0 ∧
        ∃ hdet : (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall hw).presentation outgoing)).det ≠ 0,
          Nonempty (Candidate.ClearedPencil
            ((familyAt wall hw).candidate outgoing)
            (fullDimAt wall hw outgoing hdet).labelling.presentation
            next.toMatrixState.currentStart) := by
  classical
  obtain ⟨wall, hw, outgoing, nextMatrix, hstep, hlabel, hvalid, hsign,
      hpencil⟩ :=
    exists_step_of_presented_classified_first_wall_matrix_local
      matrix baseStart baseFinish current.toMatrixState targetAt dataAt
      hValidAt hTargetConnectedAt hTargetGenusAt rootAt houtside hsimple
      targetWallAt caseAt familyAt hwallColumn incomingAt hincomingNonzero
      hincomingMatrix outgoingVelocity hSystems outgoingLabel houtgoingMatrix
  have houtgoingNonzero :
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall hw).presentation outgoing)).det ≠ 0 :=
    det_ne_zero_of_mul_det_neg hsign
  have hmatrix :
      GluingDatum.LengthMatrixPresentation.matrix
          ((familyAt wall hw).presentation outgoing) = matrix nextMatrix.label := by
    rw [hlabel, houtgoingMatrix wall hw outgoing houtgoingNonzero]
  have hcarries : CarriesClearedPencil degree
      (matrix nextMatrix.label) nextMatrix.currentStart := by
    refine ⟨targetAt wall hw, (familyAt wall hw).base outgoing, targetWallAt wall hw,
      (familyAt wall hw).candidate outgoing,
      fullDimAt wall hw outgoing houtgoingNonzero, ?_,
      (familyAt wall hw).valid_of_old outgoing (hValidAt wall hw),
      hTargetConnectedAt wall hw, hTargetGenusAt wall hw, ?_⟩
    · rw [hfullDimPresentation wall hw outgoing houtgoingNonzero]
      exact hmatrix
    · rw [hfullDimPresentation wall hw outgoing houtgoingNonzero]
      exact hpencil
  let next : State degree matrix baseStart baseFinish :=
    { toMatrixState := nextMatrix
      carriesPencil := hcarries }
  refine ⟨wall, hw, outgoing, next, hstep, hlabel, hvalid, hsign,
    houtgoingNonzero, ?_⟩
  rw [hfullDimPresentation wall hw outgoing houtgoingNonzero]
  exact hpencil

omit [Fintype chart] [DecidableEq chart] in
/-- A populated `PresentedProgress` package gives a semantic successor for
every nonterminal state.  Nonsingularity supplies the outgoing velocities by
inverse chart coordinates and proves the lower-level system identities.

The successor comes with the **named** selected wall and outgoing member, the
nonsingularity proof at which `fullDimAt` is read, the successor's chart label,
and the cleared pencil on that very `fullDimAt` witness.  All four were already
produced by `exists_step_of_presented_classified_first_wall`; returning them
lets a caller rebuild the successor's payload at a *named* full-dimensional
presentation instead of the anonymous one inside `carriesPencil`. -/
theorem PresentedProgress.exists_step
    (progress : PresentedProgress current)
    (hdet : ∀ label, (matrix label).det ≠ 0)
    (hNonterminal : ¬ Terminal current) :
    ∃ next : State degree matrix baseStart baseFinish, Step current next ∧
      ∃ (wall : coordinate) (hw : current.FirstWall wall)
        (outgoing : Fin (progress.caseAt wall hw).arity)
        (houtgoing : (GluingDatum.LengthMatrixPresentation.matrix
          ((progress.familyAt wall hw).presentation outgoing)).det ≠ 0),
        next.toMatrixState.label = progress.outgoingLabel wall hw outgoing ∧
        Nonempty (Candidate.ClearedPencil
          ((progress.familyAt wall hw).candidate outgoing)
          (progress.fullDimAt wall hw outgoing houtgoing).labelling.presentation
          next.toMatrixState.currentStart) := by
  let incomingVelocity : coordinate → ℚ := fun i ↦
    current.toMatrixState.currentFinish i -
      current.toMatrixState.currentStart i
  let outgoingVelocity : ∀ wall (hw : current.FirstWall wall),
      Fin (progress.caseAt wall hw).arity → coordinate → ℚ :=
    fun wall hw outgoing ↦
      DraismaVargas.LocalCases.FiniteAtlasMarch.chartCoordinates
        (matrix (progress.outgoingLabel wall hw outgoing))
        ((matrix current.toMatrixState.label).mulVec incomingVelocity)
  have hSystems : ∀ wall hw outgoing,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((progress.familyAt wall hw).presentation outgoing)).det ≠ 0 →
      (GluingDatum.LengthMatrixPresentation.matrix
        ((progress.familyAt wall hw).presentation
          (progress.incomingAt wall hw))).mulVec incomingVelocity =
        (GluingDatum.LengthMatrixPresentation.matrix
          ((progress.familyAt wall hw).presentation outgoing)).mulVec
            (outgoingVelocity wall hw outgoing) := by
    intro wall hw outgoing houtgoingNonzero
    rw [progress.incomingMatrix wall hw,
      ← progress.outgoingMatrix wall hw outgoing houtgoingNonzero]
    exact
      (DraismaVargas.LocalCases.FiniteAtlasMarch.mulVec_chartCoordinates
        (matrix (progress.outgoingLabel wall hw outgoing))
        (hdet (progress.outgoingLabel wall hw outgoing))
        ((matrix current.toMatrixState.label).mulVec incomingVelocity)).symm
  have houtside : ∃ i, current.toMatrixState.currentFinish i < 0 := by
    by_contra hnone
    apply hNonterminal
    intro i
    exact not_lt.mp (fun hi ↦ hnone ⟨i, hi⟩)
  obtain ⟨wall, hw, outgoing, next, hstep, hlabel, _, _, houtgoing, hpencil⟩ :=
    exists_step_of_presented_classified_first_wall matrix baseStart baseFinish
      current progress.targetAt progress.dataAt progress.validAt
      progress.targetConnectedAt progress.targetGenusAt progress.rootAt
      houtside progress.simpleCrossings progress.targetWallAt
      progress.caseAt progress.familyAt progress.wallColumn progress.incomingAt
      progress.incomingNonzero progress.incomingMatrix
      outgoingVelocity hSystems progress.outgoingLabel progress.outgoingMatrix
      progress.fullDimAt progress.fullDimPresentation
  exact ⟨next, hstep, wall, hw, outgoing, houtgoing, hlabel, hpencil⟩

omit [DecidableEq chart] in
/-- If every nonterminal semantic state has a presented successor, the fixed
finite event set reaches a terminal semantic state.  The conclusion exposes
the final state's actual cleared pencil in addition to the transition chain. -/
theorem exists_terminal_reachable
    (matrix : chart → Matrix coordinate coordinate ℚ)
    (hdet : ∀ label, (matrix label).det ≠ 0)
    (baseStart baseFinish : coordinate → ℚ)
    (progress : ∀ current : State degree matrix baseStart baseFinish,
      Terminal current ∨ ∃ next, Step current next)
    (initial : State degree matrix baseStart baseFinish) :
    ∃ final, Relation.ReflTransGen Step initial final ∧ Terminal final ∧
      CarriesClearedPencil degree
        (matrix final.toMatrixState.label) final.toMatrixState.currentStart ∧
      CarriesClearedFace degree
        (matrix final.toMatrixState.label) final.toMatrixState.currentFinish ∧
      ∃ source : CFGraph.{0}, BNExists source 1 degree := by
  obtain ⟨final, hreach, hterminal⟩ :=
    (march matrix hdet baseStart baseFinish).exists_terminal_reachable
      Terminal progress initial
  exact ⟨final, hreach, hterminal, final.carriesPencil,
    final.clearedFace hterminal,
    final.carriesPencil.exists_bnExists⟩

omit [DecidableEq chart] in
/-- Global semantic termination from one reusable local-classification
interface.  The only state-dependent input is a `PresentedProgress` package
for each nonterminal state. -/
theorem exists_terminal_reachable_of_presented_progress
    (matrix : chart → Matrix coordinate coordinate ℚ)
    (hdet : ∀ label, (matrix label).det ≠ 0)
    (baseStart baseFinish : coordinate → ℚ)
    (localProgress : ∀ current : State degree matrix baseStart baseFinish,
      ¬ Terminal current → PresentedProgress current)
    (initial : State degree matrix baseStart baseFinish) :
    ∃ final, Relation.ReflTransGen Step initial final ∧ Terminal final ∧
      CarriesClearedPencil degree
        (matrix final.toMatrixState.label) final.toMatrixState.currentStart ∧
      CarriesClearedFace degree
        (matrix final.toMatrixState.label) final.toMatrixState.currentFinish ∧
      ∃ source : CFGraph.{0}, BNExists source 1 degree := by
  apply exists_terminal_reachable matrix hdet baseStart baseFinish _ initial
  intro current
  by_cases hterminal : Terminal current
  · exact Or.inl hterminal
  · obtain ⟨next, hstep, _⟩ :=
      (localProgress current hterminal).exists_step hdet hterminal
    exact Or.inr ⟨next, hstep⟩

end State

end DraismaVargas.LocalCases.SemanticAtlasMarch
