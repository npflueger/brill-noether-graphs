import DraismaVargas.LocalCases.NonTrivalentWallSetup

/-!
# Interior row positivity on the actual reachable march

Part II's outer path runs an inner march from a positive point to a
nonnegative endpoint. `NonTrivalentWallSetup.rows_ne_zero_of_lt_one` proves
that its interior walls have no vanishing stable row, but asks for
`0 ≤ restartTime`. An arbitrary `FiniteAtlasMarch.State` does not carry that
inequality. Every state reached from the time-zero initial state does.

We derive this invariant from the step relation of `FiniteAtlasMarch`, without
changing the state or any wall constructor. The terminal theorem below needs
progress only on states reachable from the chosen initial state. Thus the
invariant can actually be used by the progress producer; it is not an extra
hypothesis about every abstract state of `FiniteAtlasMarch.State`.

This does not supply the graph-identification invariant or a wall candidate.
It discharges, independently of those, the clock and row-positivity input that
the wall setup of `NonTrivalentWallSetup` and the march from its initial state
need.
-/

namespace DraismaVargas.Infrastructure.FiniteStrictMarch

variable {state : Type*}

/-- Termination needs progress only on the component reached from the seed.
The measure is the existing finite event count, with no new finiteness input. -/
theorem exists_terminal_after_reachable (march : FiniteStrictMarch state)
    (terminal : state → Prop) (initial : state)
    (progress : ∀ current, Relation.ReflTransGen march.step initial current →
      terminal current ∨ ∃ next, march.step current next)
    (current : state) (hcurrent : Relation.ReflTransGen march.step initial current) :
    ∃ final, Relation.ReflTransGen march.step current final ∧ terminal final := by
  rcases progress current hcurrent with hterminal | ⟨next, hstep⟩
  · exact ⟨current, .refl, hterminal⟩
  · obtain ⟨final, hreach, hterminal⟩ :=
      exists_terminal_after_reachable march terminal initial progress next
        (hcurrent.tail hstep)
    exact ⟨final, (Relation.ReflTransGen.single hstep).trans hreach, hterminal⟩
termination_by remainingEventCount march.eventTimes (march.time current)
decreasing_by exact march.remaining_lt_of_step hstep

/-- The reachable-state version of `exists_terminal_reachable`. -/
theorem exists_terminal_reachable_of_reachable_progress
    (march : FiniteStrictMarch state) (terminal : state → Prop) (initial : state)
    (progress : ∀ current, Relation.ReflTransGen march.step initial current →
      terminal current ∨ ∃ next, march.step current next) :
    ∃ final, Relation.ReflTransGen march.step initial final ∧ terminal final :=
  march.exists_terminal_after_reachable terminal initial progress initial .refl

end DraismaVargas.Infrastructure.FiniteStrictMarch

namespace DraismaVargas.LocalCases.FiniteAtlasMarch.State

variable {coordinate chart : Type*} [Fintype coordinate]
  {matrix : chart → Matrix coordinate coordinate ℚ}
  {baseStart baseFinish : coordinate → ℚ}

/-- A step's wall is strictly after the current restart; the next restart
is strictly after that wall. -/
theorem restartTime_lt_of_step {current next : State matrix baseStart baseFinish}
    (hstep : Step current next) : current.restartTime < next.restartTime := by
  obtain ⟨wall, time, htime, _, hwall⟩ := hstep
  have hremaining : 0 < 1 - current.restartTime := sub_pos.mpr current.restart_lt_one
  have hadvance : 0 < (1 - current.restartTime) * time := mul_pos hremaining htime
  have hbefore : current.restartTime < next.lastWallTime := by
    rw [hwall]
    linarith
  exact hbefore.trans next.lastWall_lt_restart

/-- The clock is monotone along every finite chain of actual steps. -/
theorem restartTime_le_of_reachable {initial current : State matrix baseStart baseFinish}
    (hreach : Relation.ReflTransGen Step initial current) :
    initial.restartTime ≤ current.restartTime := by
  induction hreach with
  | refl => exact le_rfl
  | tail _ hstep ih => exact ih.trans (restartTime_lt_of_step hstep).le

/-- In particular a time-zero seed never acquires a negative restart. -/
theorem restartTime_nonneg_of_reachable {initial current : State matrix baseStart baseFinish}
    (hzero : initial.restartTime = 0)
    (hreach : Relation.ReflTransGen Step initial current) :
    0 ≤ current.restartTime := by
  simpa only [hzero] using restartTime_le_of_reachable hreach

end DraismaVargas.LocalCases.FiniteAtlasMarch.State

namespace DraismaVargas.LocalCases.SemanticAtlasMarch.State

open DraismaVargas.Infrastructure

variable {coordinate chart : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {degree : ℕ} {matrix : chart → Matrix coordinate coordinate ℚ}
  {baseStart baseFinish : coordinate → ℚ}

/-- Forgetting the pencil maps an actual semantic path to the matrix path. -/
theorem matrix_reachable {initial current : State degree matrix baseStart baseFinish}
    (hreach : Relation.ReflTransGen Step initial current) :
    Relation.ReflTransGen FiniteAtlasMarch.State.Step
      initial.toMatrixState current.toMatrixState := by
  induction hreach with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail hstep

theorem restartTime_nonneg_of_reachable
    {initial current : State degree matrix baseStart baseFinish}
    (hzero : initial.toMatrixState.restartTime = 0)
    (hreach : Relation.ReflTransGen Step initial current) :
    0 ≤ current.toMatrixState.restartTime :=
  FiniteAtlasMarch.State.restartTime_nonneg_of_reachable hzero (matrix_reachable hreach)

/-- The honest matrix in a reached state's payload has nonzero stable rows
at every inner wall. The restart inequality is produced, not assumed. -/
theorem rows_ne_zero_of_reachable
    {target : CFGraph} {data : GluingDatum target degree}
    (fullDim : FullDimensionalSource.FullDimensionalSourcePresentation data coordinate)
    {initial current : State degree matrix baseStart baseFinish}
    (hzero : initial.toMatrixState.restartTime = 0)
    (hreach : Relation.ReflTransGen Step initial current)
    (hmatrix : GluingDatum.LengthMatrixPresentation.matrix
      fullDim.labelling.presentation = matrix current.toMatrixState.label)
    (hstart : ∀ i, 0 < baseStart i) (hfinish : ∀ i, 0 ≤ baseFinish i)
    {time : ℚ} (h0 : 0 ≤ time) (h1 : time < 1) :
    ∀ row, (GluingDatum.LengthMatrixPresentation.matrix
        fullDim.labelling.presentation).mulVec
      (RationalAffineWall.segment current.toMatrixState.currentStart
        current.toMatrixState.currentFinish time) row ≠ 0 :=
  NonTrivalentWallSetup.rows_ne_zero_of_lt_one fullDim current.toMatrixState
    hmatrix hstart hfinish (restartTime_nonneg_of_reachable hzero hreach) h0 h1

/-- The source-facing termination interface may use seed-dependent
reachability facts when it constructs each `PresentedProgress`. -/
theorem exists_terminal_of_reachable_presented_progress
    [Fintype chart] [DecidableEq chart]
    (hdet : ∀ label, (matrix label).det ≠ 0)
    (initial : State degree matrix baseStart baseFinish)
    (progress : ∀ current : State degree matrix baseStart baseFinish,
      Relation.ReflTransGen Step initial current →
      ¬ Terminal current → PresentedProgress current) :
    ∃ final, Relation.ReflTransGen Step initial final ∧ Terminal final := by
  apply (march matrix hdet baseStart baseFinish).exists_terminal_reachable_of_reachable_progress
    Terminal initial
  intro current hreach
  by_cases hterminal : Terminal current
  · exact Or.inl hterminal
  · obtain ⟨next, hstep, _⟩ := (progress current hreach hterminal).exists_step hdet hterminal
    exact Or.inr ⟨next, hstep⟩

end DraismaVargas.LocalCases.SemanticAtlasMarch.State
