module

public import Utilities.IntegralGeometry.FiniteStrictMarch
public import DraismaVargas.LocalCases.MarchContinuation

@[expose] public section

/-!
# Finite event times for a rational Draisma--Vargas cone atlas

Fix a rational source-metric deformation and a finite catalogue of square,
nonsingular cone matrices.  Pulling the two endpoints through each inverse
matrix gives canonical coordinates in that chart.  Every coordinate wall then
has one explicit rational crossing time, so the product of chart labels and
coordinate labels gives one finite global event set.

The main theorem proves that a wall found after an arbitrary positive restart
belongs to this fixed set.  Its proof uses the exact global reparameterization
from `MarchContinuation`; the current coordinates need not have been chosen by
an inverse formula, since nonsingularity makes them equal to the canonical
coordinates.  The finite chart catalogue is a separate input (the universal
atlas of `MatrixAtlas`).
-/

namespace DraismaVargas.LocalCases.FiniteAtlasMarch

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.RationalAffineWall
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.ClassifiedContinuation

variable {coordinate chart : Type*}
  [Fintype coordinate] [DecidableEq coordinate]
  [Fintype chart] [DecidableEq chart]

/-- Canonical cone coordinates of a stable metric in a square rational chart. -/
noncomputable def chartCoordinates
    (matrix : Matrix coordinate coordinate ℚ) (metric : coordinate → ℚ) :
    coordinate → ℚ :=
  matrix⁻¹.mulVec metric

/-- A nonsingular chart matrix maps its canonical coordinates back to the
represented stable metric. -/
theorem mulVec_chartCoordinates (matrix : Matrix coordinate coordinate ℚ)
    (hdet : matrix.det ≠ 0) (metric : coordinate → ℚ) :
    matrix.mulVec (chartCoordinates matrix metric) = metric := by
  have hunit : IsUnit matrix.det := isUnit_iff_ne_zero.mpr hdet
  unfold chartCoordinates
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv matrix hunit]
  simp

/-- Nonsingularity identifies any solution of the chart length system with
the canonical inverse coordinates. -/
theorem chartCoordinates_eq_of_mulVec_eq
    (matrix : Matrix coordinate coordinate ℚ) (hdet : matrix.det ≠ 0)
    {coordinates metric : coordinate → ℚ}
    (hmap : matrix.mulVec coordinates = metric) :
    chartCoordinates matrix metric = coordinates := by
  have hunit : IsUnit matrix.det := isUnit_iff_ne_zero.mpr hdet
  unfold chartCoordinates
  rw [← hmap, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul matrix hunit]
  simp

/-- Inverse chart coordinates preserve affine segments. -/
theorem chartCoordinates_segment (matrix : Matrix coordinate coordinate ℚ)
    (start finish : coordinate → ℚ) (time : ℚ) :
    chartCoordinates matrix (segment start finish time) =
      segment (chartCoordinates matrix start)
        (chartCoordinates matrix finish) time := by
  exact MarchContinuation.mulVec_segment matrix⁻¹ start finish time

/-- The explicit global crossing time attached to one chart-coordinate pair. -/
noncomputable def chartCrossingTime
    (matrix : chart → Matrix coordinate coordinate ℚ)
    (start finish : coordinate → ℚ) (event : chart × coordinate) : ℚ :=
  coordinateCrossingTime
    (chartCoordinates (matrix event.1) start)
    (chartCoordinates (matrix event.1) finish) event.2

/-- The fixed finite set of all coordinate-wall times in a finite rational
chart catalogue. -/
noncomputable def eventTimes
    (matrix : chart → Matrix coordinate coordinate ℚ)
    (start finish : coordinate → ℚ) : Finset ℚ :=
  Finset.univ.image (chartCrossingTime matrix start finish)

omit [DecidableEq chart] in
/-- A coordinate wall encountered after any positive restart has its global
time in the fixed finite atlas event set.

The current coordinate vectors only need to solve the chart systems at the
restart point and endpoint.  Nonsingularity recovers the canonical inverse
coordinates used to define `eventTimes`. -/
theorem globalWallTime_mem_eventTimes
    (matrix : chart → Matrix coordinate coordinate ℚ)
    (hdet : ∀ label, (matrix label).det ≠ 0)
    (baseStart baseFinish currentStart currentFinish : coordinate → ℚ)
    (label : chart) (wall : coordinate) (currentTime localTime : ℚ)
    (hcurrentStartMap : (matrix label).mulVec currentStart =
      segment baseStart baseFinish currentTime)
    (hcurrentFinishMap : (matrix label).mulVec currentFinish = baseFinish)
    (hcurrentPositive : 0 < currentStart wall)
    (hwallZero : segment currentStart currentFinish localTime wall = 0) :
    currentTime + (1 - currentTime) * localTime ∈
      eventTimes matrix baseStart baseFinish := by
  let globalTime := currentTime + (1 - currentTime) * localTime
  let canonicalStart := chartCoordinates (matrix label) baseStart
  let canonicalFinish := chartCoordinates (matrix label) baseFinish
  have hcanonicalCurrent :
      segment canonicalStart canonicalFinish currentTime = currentStart := by
    rw [← chartCoordinates_segment]
    exact chartCoordinates_eq_of_mulVec_eq (matrix label) (hdet label)
      hcurrentStartMap
  have hcurrentSegmentMap :
      (matrix label).mulVec (segment currentStart currentFinish localTime) =
        segment baseStart baseFinish globalTime := by
    rw [MarchContinuation.mulVec_segment, hcurrentStartMap,
      hcurrentFinishMap, MarchContinuation.segment_rebase_right]
  have hcanonicalWall :
      segment canonicalStart canonicalFinish globalTime =
        segment currentStart currentFinish localTime := by
    rw [← chartCoordinates_segment]
    exact chartCoordinates_eq_of_mulVec_eq (matrix label) (hdet label)
      hcurrentSegmentMap
  have hcoordinateDiff : canonicalStart wall ≠ canonicalFinish wall := by
    intro heq
    have hcurrentAtWall := congrFun hcanonicalCurrent wall
    have hwallAtWall := congrFun hcanonicalWall wall
    simp only [RationalAffineWall.segment, heq, sub_self, mul_zero, add_zero]
      at hcurrentAtWall hwallAtWall
    have hwallZero' := hwallZero
    simp only [RationalAffineWall.segment] at hwallZero'
    linarith
  have hevalDiff :
      (coordinateWall wall).eval canonicalStart ≠
        (coordinateWall wall).eval canonicalFinish := by
    simpa using hcoordinateDiff
  have hevalZero :
      (coordinateWall wall).eval
          (segment canonicalStart canonicalFinish globalTime) = 0 := by
    simp only [eval_coordinateWall]
    rw [hcanonicalWall]
    exact hwallZero
  have htime :
      globalTime = coordinateCrossingTime canonicalStart canonicalFinish wall :=
    eq_crossingTime_of_eval_segment_eq_zero (coordinateWall wall)
      canonicalStart canonicalFinish hevalDiff hevalZero
  apply Finset.mem_image.mpr
  refine ⟨(label, wall), Finset.mem_univ _, ?_⟩
  exact htime.symm

/-! ## A finite-atlas march state -/

/-- One chart currently representing the fixed stable-metric deformation.

`lastWallTime` is the event used by the termination measure, while
`restartTime` is a slightly later point where every current chart coordinate
is again positive.  Keeping the two parameters separate permits a strict
positive restart without losing membership of transition times in the fixed
finite event set. -/
structure State (matrix : chart → Matrix coordinate coordinate ℚ)
    (baseStart baseFinish : coordinate → ℚ) where
  label : chart
  lastWallTime : ℚ
  restartTime : ℚ
  lastWall_lt_restart : lastWallTime < restartTime
  restart_lt_one : restartTime < 1
  currentStart : coordinate → ℚ
  currentFinish : coordinate → ℚ
  currentStart_positive : ∀ i, 0 < currentStart i
  currentStart_map : (matrix label).mulVec currentStart =
    segment baseStart baseFinish restartTime
  currentFinish_map : (matrix label).mulVec currentFinish = baseFinish

namespace State

variable {matrix : chart → Matrix coordinate coordinate ℚ}
  {baseStart baseFinish : coordinate → ℚ}

/-- The starting state at global time zero, with a sentinel last-event time
`-1` strictly before the deformation interval. -/
def initial (label : chart) (currentStart currentFinish : coordinate → ℚ)
    (hstartPositive : ∀ i, 0 < currentStart i)
    (hstartMap : (matrix label).mulVec currentStart = baseStart)
    (hfinishMap : (matrix label).mulVec currentFinish = baseFinish) :
    State matrix baseStart baseFinish where
  label := label
  lastWallTime := -1
  restartTime := 0
  lastWall_lt_restart := by norm_num
  restart_lt_one := by norm_num
  currentStart := currentStart
  currentFinish := currentFinish
  currentStart_positive := hstartPositive
  currentStart_map := by
    rw [hstartMap]
    ext i
    simp [RationalAffineWall.segment]
  currentFinish_map := hfinishMap

/-- A terminal chart contains the actual closed endpoint in its nonnegative
coordinate orthant. -/
def Terminal (state : State matrix baseStart baseFinish) : Prop :=
  ∀ i, 0 ≤ state.currentFinish i

/-- One atlas step records the next coordinate wall.  The successor state
itself carries the positive outgoing restart and both global metric identities;
the relation only needs to identify its preceding wall time. -/
def Step (current next : State matrix baseStart baseFinish) : Prop :=
  ∃ wall : coordinate, ∃ localTime : ℚ,
    0 < localTime ∧
    segment current.currentStart current.currentFinish localTime wall = 0 ∧
    next.lastWallTime =
      current.restartTime + (1 - current.restartTime) * localTime

/-- The finite strict march underlying a finite rational chart atlas.  Strict
advance and membership in the fixed event set are consequences of the state
and step invariants. -/
noncomputable def march
    (matrix : chart → Matrix coordinate coordinate ℚ)
    (hdet : ∀ label, (matrix label).det ≠ 0)
    (baseStart baseFinish : coordinate → ℚ) :
    FiniteStrictMarch (State matrix baseStart baseFinish) where
  eventTimes := eventTimes matrix baseStart baseFinish
  time := State.lastWallTime
  step := Step
  step_time_lt := by
    intro current next hstep
    rcases hstep with ⟨wall, localTime, hlocalTime, hwall, hnext⟩
    rw [hnext]
    apply current.lastWall_lt_restart.trans
    have hremaining : 0 < 1 - current.restartTime :=
      sub_pos.mpr current.restart_lt_one
    nlinarith [mul_pos hremaining hlocalTime]
  step_time_mem := by
    intro current next hstep
    rcases hstep with ⟨wall, localTime, hlocalTime, hwall, hnext⟩
    rw [hnext]
    exact globalWallTime_mem_eventTimes matrix hdet baseStart baseFinish
      current.currentStart current.currentFinish current.label wall
      current.restartTime localTime current.currentStart_map
      current.currentFinish_map (current.currentStart_positive wall) hwall

omit [Fintype chart] [DecidableEq chart] in
/-- Registering every outgoing local matrix under a finite catalogue label
turns the classified first-wall continuation into an actual atlas successor.
The returned receipt retains validity of the chosen outgoing gluing datum and
the opposite determinant sign, while `Step` retains exactly the information
used by finite termination. -/
theorem exists_step_of_classified_first_wall
    {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
    (matrix : chart → Matrix coordinate coordinate ℚ)
    (baseStart baseFinish : coordinate → ℚ)
    (current : State matrix baseStart baseFinish)
    (hValid : data.Valid)
    (houtside : ∃ i, current.currentFinish i < 0)
    (hsimple : SimpleNegativeCrossings
      current.currentStart current.currentFinish)
    (caseAt : coordinate → SourceCase)
    (familyAt : ∀ wall, Family (coordinate := coordinate)
      (caseAt wall).arity data)
    (hwallColumn : ∀ wall, (familyAt wall).wallColumn = wall)
    (incomingAt : ∀ wall, Fin (caseAt wall).arity)
    (hincomingNonzero : ∀ wall,
      ((familyAt wall).matrix (incomingAt wall)).det ≠ 0)
    (hincomingMatrix : ∀ wall,
      (familyAt wall).matrix (incomingAt wall) = matrix current.label)
    (outgoingVelocity : ∀ wall,
      Fin (caseAt wall).arity → coordinate → ℚ)
    (hSystems : ∀ wall outgoing,
      ((familyAt wall).matrix outgoing).det ≠ 0 →
      ((familyAt wall).matrix (incomingAt wall)).mulVec
          (fun i => current.currentFinish i - current.currentStart i) =
        ((familyAt wall).matrix outgoing).mulVec
          (outgoingVelocity wall outgoing))
    (outgoingLabel : ∀ wall, Fin (caseAt wall).arity → chart)
    (houtgoingMatrix : ∀ wall outgoing,
      ((familyAt wall).matrix outgoing).det ≠ 0 →
      matrix (outgoingLabel wall outgoing) =
        (familyAt wall).matrix outgoing) :
    ∃ wall : coordinate, ∃ outgoing : Fin (caseAt wall).arity,
      ∃ next : State matrix baseStart baseFinish,
        Step current next ∧
        next.label = outgoingLabel wall outgoing ∧
        ((familyAt wall).candidate outgoing).datum.Valid ∧
        ((familyAt wall).matrix (incomingAt wall)).det *
            ((familyAt wall).matrix outgoing).det < 0 := by
  classical
  obtain ⟨wall, localTime, outgoing, ε, hlocalTimePos, hlocalTimeLt,
      hεPos, hεLt, hwallZero, hwallAdvance, hrestartAdvance, hrestartLt,
      hvalid, hsign, hpositive, hmaps⟩ :=
    MarchContinuation.exists_valid_resumed_global_segment_at_first_wall
      hValid baseStart baseFinish current.currentStart current.currentFinish
      current.restartTime current.restart_lt_one current.currentStart_positive
      houtside hsimple caseAt familyAt hwallColumn incomingAt
      hincomingNonzero (matrix current.label) hincomingMatrix
      current.currentStart_map current.currentFinish_map outgoingVelocity hSystems
  have hrestartMap := hmaps.1
  have hfinishMap := hmaps.2
  let outgoingStart : coordinate → ℚ :=
    segment current.currentStart current.currentFinish localTime +
      ε • outgoingVelocity wall outgoing
  let outgoingFinish : coordinate → ℚ :=
    segment current.currentStart current.currentFinish localTime +
      (1 - localTime) • outgoingVelocity wall outgoing
  let next : State matrix baseStart baseFinish :=
    { label := outgoingLabel wall outgoing
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
        rw [houtgoingMatrix wall outgoing
          (det_ne_zero_of_mul_det_neg hsign)]
        simpa [outgoingStart] using hrestartMap
      currentFinish_map := by
        rw [houtgoingMatrix wall outgoing
          (det_ne_zero_of_mul_det_neg hsign)]
        simpa [outgoingFinish] using hfinishMap }
  have hstep : Step current next := by
    refine ⟨wall, localTime, hlocalTimePos, hwallZero, ?_⟩
    rfl
  exact ⟨wall, outgoing, next, hstep, rfl, hvalid, hsign⟩

omit [Fintype chart] [DecidableEq chart] in
/-- Presentation-preserving atlas successor.  The ordinary `State` still
carries exactly the finite-march invariants, while the step receipt identifies
the selected global candidate and retains its cleared pencil at the successor's
positive restart coordinates. -/
theorem exists_step_of_presented_classified_first_wall
    {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
    (matrix : chart → Matrix coordinate coordinate ℚ)
    (baseStart baseFinish : coordinate → ℚ)
    (current : State matrix baseStart baseFinish)
    (hValid : data.Valid)
    (hTargetConnected : graph_connected target)
    (hTargetGenus : genus target = 0) (root : target.V)
    (houtside : ∃ i, current.currentFinish i < 0)
    (hsimple : SimpleNegativeCrossings
      current.currentStart current.currentFinish)
    (targetWallAt : coordinate → target.V)
    (caseAt : coordinate → SourceCase)
    (familyAt : ∀ wall, PresentedFamily (coordinate := coordinate)
      (caseAt wall).arity data (targetWallAt wall))
    (hwallColumn : ∀ wall, (familyAt wall).wallColumn = wall)
    (incomingAt : ∀ wall, Fin (caseAt wall).arity)
    (hincomingNonzero : ∀ wall,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall).presentation (incomingAt wall))).det ≠ 0)
    (hincomingMatrix : ∀ wall,
      GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall).presentation (incomingAt wall)) =
          matrix current.label)
    (outgoingVelocity : ∀ wall,
      Fin (caseAt wall).arity → coordinate → ℚ)
    (hSystems : ∀ wall outgoing,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall).presentation outgoing)).det ≠ 0 →
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall).presentation (incomingAt wall))).mulVec
          (fun i => current.currentFinish i - current.currentStart i) =
        (GluingDatum.LengthMatrixPresentation.matrix
          ((familyAt wall).presentation outgoing)).mulVec
            (outgoingVelocity wall outgoing))
    (outgoingLabel : ∀ wall, Fin (caseAt wall).arity → chart)
    (houtgoingMatrix : ∀ wall outgoing,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall).presentation outgoing)).det ≠ 0 →
      matrix (outgoingLabel wall outgoing) =
        GluingDatum.LengthMatrixPresentation.matrix
          ((familyAt wall).presentation outgoing)) :
    ∃ wall : coordinate, ∃ outgoing : Fin (caseAt wall).arity,
      ∃ next : State matrix baseStart baseFinish,
        Step current next ∧
        next.label = outgoingLabel wall outgoing ∧
        ((familyAt wall).candidate outgoing).datum.Valid ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall).presentation (incomingAt wall))).det *
          (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall).presentation outgoing)).det < 0 ∧
        Nonempty (Candidate.ClearedPencil
          ((familyAt wall).candidate outgoing)
          ((familyAt wall).presentation outgoing) next.currentStart) := by
  classical
  obtain ⟨wall, localTime, outgoing, ε, hlocalTimePos, hlocalTimeLt,
      hεPos, hεLt, hwallZero, hwallAdvance, hrestartAdvance, hrestartLt,
      hvalid, hsign, hpositive, hrestartMap, hfinishMap, hpencil⟩ :=
    MarchContinuation.exists_valid_resumed_global_segment_with_pencil_at_first_wall
      hValid hTargetConnected hTargetGenus root baseStart baseFinish
      current.currentStart current.currentFinish current.restartTime
      current.restart_lt_one current.currentStart_positive houtside hsimple
      targetWallAt caseAt familyAt hwallColumn incomingAt hincomingNonzero
      (matrix current.label) hincomingMatrix current.currentStart_map
      current.currentFinish_map outgoingVelocity hSystems
  let outgoingStart : coordinate → ℚ :=
    segment current.currentStart current.currentFinish localTime +
      ε • outgoingVelocity wall outgoing
  let outgoingFinish : coordinate → ℚ :=
    segment current.currentStart current.currentFinish localTime +
      (1 - localTime) • outgoingVelocity wall outgoing
  let next : State matrix baseStart baseFinish :=
    { label := outgoingLabel wall outgoing
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
        rw [houtgoingMatrix wall outgoing
          (det_ne_zero_of_mul_det_neg hsign)]
        simpa [outgoingStart] using hrestartMap
      currentFinish_map := by
        rw [houtgoingMatrix wall outgoing
          (det_ne_zero_of_mul_det_neg hsign)]
        simpa [outgoingFinish] using hfinishMap }
  have hstep : Step current next := by
    refine ⟨wall, localTime, hlocalTimePos, hwallZero, ?_⟩
    rfl
  have hpencilNext : Nonempty (Candidate.ClearedPencil
      ((familyAt wall).candidate outgoing)
      ((familyAt wall).presentation outgoing) next.currentStart) := by
    simpa [next, outgoingStart] using hpencil
  exact ⟨wall, outgoing, next, hstep, rfl, hvalid, hsign, hpencilNext⟩

omit [DecidableEq chart] in
/-- If local continuation supplies a successor for every nonterminal atlas
state, finitely many rational wall events suffice to reach a chart containing
the actual closed endpoint. -/
theorem exists_terminal_reachable
    (matrix : chart → Matrix coordinate coordinate ℚ)
    (hdet : ∀ label, (matrix label).det ≠ 0)
    (baseStart baseFinish : coordinate → ℚ)
    (progress : ∀ current : State matrix baseStart baseFinish,
      Terminal current ∨ ∃ next, Step current next)
    (initial : State matrix baseStart baseFinish) :
    ∃ final, Relation.ReflTransGen Step initial final ∧ Terminal final := by
  exact (march matrix hdet baseStart baseFinish).exists_terminal_reachable
    Terminal progress initial

end State

end DraismaVargas.LocalCases.FiniteAtlasMarch
