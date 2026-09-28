import Mathlib.Tactic

/-!
# Termination of a march through finitely many strict event times

This file isolates the combinatorial termination argument used by the global
deformation argument of Draisma--Vargas Part I (arXiv:1909.12924).  A
transition may change the entire state type's internal presentation; the only
global data retained are its rational time and a fixed finite set of possible
event times.  If every transition lands at an event time and strictly
increases time, the number of remaining events strictly decreases.
Consequently, a system in which every nonterminal state can step must reach a
terminal state after finitely many transitions.

The theorem does not postulate any Draisma--Vargas transition.  An application
must build `step` itself, for instance from a first orthant exit
(`Utilities.IntegralGeometry.PositiveOrthantExit`) followed by a classification
of the wall event reached there.
-/

namespace DraismaVargas.Infrastructure

/-- Number of listed event times strictly after `current`. -/
def remainingEventCount (eventTimes : Finset ℚ) (current : ℚ) : ℕ :=
  (eventTimes.filter fun event => current < event).card

/-- Moving strictly forward to a listed event strictly decreases the number
of remaining listed events. -/
theorem remainingEventCount_lt_of_lt_mem (eventTimes : Finset ℚ)
    {current next : ℚ} (hlt : current < next) (hnext : next ∈ eventTimes) :
    remainingEventCount eventTimes next < remainingEventCount eventTimes current := by
  unfold remainingEventCount
  have hsubset :
      eventTimes.filter (fun event => next < event) ⊆
        eventTimes.filter (fun event => current < event) := by
    intro event hevent
    have h := Finset.mem_filter.mp hevent
    exact Finset.mem_filter.mpr ⟨h.1, hlt.trans h.2⟩
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset hsubset).2
  refine ⟨next, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨hnext, hlt⟩
  · simp

/-- A transition system whose steps occur at strictly increasing times from a
fixed finite event set. -/
structure FiniteStrictMarch (state : Type*) where
  eventTimes : Finset ℚ
  time : state → ℚ
  step : state → state → Prop
  step_time_lt : ∀ {current next}, step current next → time current < time next
  step_time_mem : ∀ {current next}, step current next → time next ∈ eventTimes

namespace FiniteStrictMarch

variable {state : Type*}

/-- The remaining-event count strictly decreases at every march step. -/
theorem remaining_lt_of_step {current next : state}
    (march : FiniteStrictMarch state)
    (hstep : march.step current next) :
    remainingEventCount march.eventTimes (march.time next) <
      remainingEventCount march.eventTimes (march.time current) :=
  remainingEventCount_lt_of_lt_mem march.eventTimes
    (march.step_time_lt hstep) (march.step_time_mem hstep)

/-- If every nonterminal state has a strict listed-event successor, then a
terminal state is reachable by finitely many transitions. -/
theorem exists_terminal_reachable (terminal : state → Prop)
    (march : FiniteStrictMarch state)
    (progress : ∀ current, terminal current ∨ ∃ next, march.step current next)
    (initial : state) :
    ∃ final, Relation.ReflTransGen march.step initial final ∧ terminal final := by
  rcases progress initial with hinitial | ⟨next, hstep⟩
  · exact ⟨initial, Relation.ReflTransGen.refl, hinitial⟩
  · obtain ⟨final, hreach, hterminal⟩ :=
      exists_terminal_reachable terminal march progress next
    exact ⟨final, (Relation.ReflTransGen.single hstep).trans hreach, hterminal⟩
termination_by remainingEventCount march.eventTimes (march.time initial)
decreasing_by exact march.remaining_lt_of_step hstep

end FiniteStrictMarch

end DraismaVargas.Infrastructure
