module

public import DraismaVargasMarkedCount.MarkedCountGeneral.DropUnique

@[expose] public section

/-!
# The drop lemma: walks, their stops and their ends (for the lift, I5)

Generic facts on the walks of module `DropWalk`:

* an isomorphism carries the stop of a walk to the stop of the image walk (`stop_map`);
* an occurrence of the walk meets only its entry and exit vertices (`eq_A_or_exit`), and before
  the stop every exit, and after the start every entry, is a vertex where the row continues; so a
  vertex where the row does not continue meets the walk only at its start or at its stop
  (`eq_zero_of_incident`, `incident_branch`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.MarkedCount

namespace MarkedWalk

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {M : Finset data.SourceVertex} {e₀ : data.SourceEdge} {A₀ : data.SourceVertex}

/-- **An occurrence of the walk meets only its entry and its exit.** -/
theorem eq_A_or_exit (h₀ : Incident data e₀ A₀) (j : ℕ) {Y : data.SourceVertex}
    (hY : Incident data (E (M := M) e₀ A₀ j) Y) :
    Y = A (M := M) e₀ A₀ j ∨ Y = exit (M := M) e₀ A₀ j :=
  eq_or_eq_otherEnd data (incident_A h₀ j) hY

/-- **After the start, every entry is a vertex where the row continues.** -/
theorem continues_A (h₀ : Incident data e₀ A₀) (hNd : ¬ IsDangling data e₀)
    (hEnd : ¬ Continues data M A₀) {j : ℕ} (hj : j ≤ stop h₀ hNd hEnd) (hj₀ : j ≠ 0) :
    Continues data M (A (M := M) e₀ A₀ j) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj₀
  have hC := continues_of_lt_stop h₀ hNd hEnd (show l < stop h₀ hNd hEnd by omega)
  rw [A_succ hC]
  exact hC

/-- **A vertex where the row does not continue meets the walk only at the start or at the
stop.** -/
theorem incident_branch (h₀ : Incident data e₀ A₀) (hNd : ¬ IsDangling data e₀)
    (hEnd : ¬ Continues data M A₀) {j : ℕ} (hj : j ≤ stop h₀ hNd hEnd) {Y : data.SourceVertex}
    (hY : Incident data (E (M := M) e₀ A₀ j) Y) (hYc : ¬ Continues data M Y) :
    (j = 0 ∧ Y = A₀) ∨ (j = stop h₀ hNd hEnd ∧ Y = exit (M := M) e₀ A₀ j) := by
  rcases eq_A_or_exit (M := M) h₀ j hY with h | h
  · by_cases hj₀ : j = 0
    · left; subst hj₀; exact ⟨rfl, h⟩
    · exact absurd (h ▸ continues_A h₀ hNd hEnd hj hj₀) hYc
  · rcases Nat.lt_or_ge j (stop h₀ hNd hEnd) with hlt | hge
    · exact absurd (h ▸ continues_of_lt_stop h₀ hNd hEnd hlt) hYc
    · right; exact ⟨le_antisymm hj hge, h⟩

/-- Before the stop, a vertex where the row does not continue meets the walk only at the start. -/
theorem eq_zero_of_incident (h₀ : Incident data e₀ A₀) (hNd : ¬ IsDangling data e₀)
    (hEnd : ¬ Continues data M A₀) {j : ℕ} (hj : j < stop h₀ hNd hEnd) {Y : data.SourceVertex}
    (hY : Incident data (E (M := M) e₀ A₀ j) Y) (hYc : ¬ Continues data M Y) :
    j = 0 ∧ Y = A₀ := by
  rcases incident_branch h₀ hNd hEnd hj.le hY hYc with h | h
  · exact h
  · exact absurd h.1 hj.ne

/-! ## The stop under an isomorphism -/

variable {target₁ target₂ : CFGraph} {D₁ : GluingDatum target₁ degree}
  {D₂ : GluingDatum target₂ degree} (φ : GeometricDatumIso D₁ D₂) (hConn : D₁.Connected)
  {M₁ : Finset D₁.SourceVertex} {M₂ : Finset D₂.SourceVertex}
  (hMarks : ∀ Y, φ.sourceVertexEquiv Y ∈ M₂ ↔ Y ∈ M₁)

include hConn hMarks in
/-- An isomorphism carries the exits of a walk to the exits of the image walk. -/
theorem exit_map {e₁ : D₁.SourceEdge} {A₁ : D₁.SourceVertex} (h₀ : Incident D₁ e₁ A₁)
    (hNd : ¬ IsDangling D₁ e₁) (j : ℕ) :
    φ.sourceVertexEquiv (exit (M := M₁) e₁ A₁ j) =
      exit (M := M₂) (φ.sourceEdgeEquiv e₁) (φ.sourceVertexEquiv A₁) j := by
  change φ.sourceVertexEquiv (otherEnd D₁ _ _) = otherEnd D₂ _ _
  rw [otherEnd_map φ (incident_A h₀ j), (seq_map φ hConn hMarks h₀ hNd j).1,
    (seq_map φ hConn hMarks h₀ hNd j).2]

include hConn hMarks in
/-- **An isomorphism carries the stop of a walk to the stop of the image walk.** -/
theorem stop_map {e₁ : D₁.SourceEdge} {A₁ : D₁.SourceVertex} (h₀ : Incident D₁ e₁ A₁)
    (hNd : ¬ IsDangling D₁ e₁) (hEnd : ¬ Continues D₁ M₁ A₁)
    (h₀' : Incident D₂ (φ.sourceEdgeEquiv e₁) (φ.sourceVertexEquiv A₁))
    (hNd' : ¬ IsDangling D₂ (φ.sourceEdgeEquiv e₁))
    (hEnd' : ¬ Continues D₂ M₂ (φ.sourceVertexEquiv A₁)) :
    stop (M := M₂) h₀' hNd' hEnd' = stop (M := M₁) h₀ hNd hEnd := by
  classical
  unfold stop
  refine Nat.find_congr' fun {j} ↦ ?_
  rw [← exit_map φ hConn hMarks h₀ hNd j, continues_map φ hConn hMarks]

end MarkedWalk

end DraismaVargas.Count.MarkedCountGeneral
