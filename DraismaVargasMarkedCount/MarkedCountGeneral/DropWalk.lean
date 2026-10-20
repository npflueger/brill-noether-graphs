module

public import DraismaVargasMarkedCount.MarkedCount.MarkedPath

@[expose] public section

/-!
# The drop lemma: the walk along a marked row

The marked twin of `W4StableSource.traverse`, as a sequence. From an occurrence `e₀` entered at
`A₀`, the walk steps through every vertex at which the marked row **continues** (surviving
valency two, not a mark; `Continues`) to the other surviving occurrence there
(`W4StableSource.stepEdge`): `seq e₀ A₀ j = (E j, A j)`, the `j`-th occurrence and its entry
vertex, and `exit j` its other end. If `A₀` is an **end** of the row (the row does not continue
there) the walk is injective until it stops (`walk_injective`), so it stops (`exists_stop`, at
`stop`), and it lists the whole marked row (`exists_index`). Two occurrences of the row that meet
at a vertex where it continues are **consecutive** in the walk (`adjacent_of_meet`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.MarkedCount

namespace MarkedWalk

variable {target : CFGraph} {degree : ℕ} (data : GluingDatum target degree)
  (M : Finset data.SourceVertex)

/-- **A marked row continues** through a surviving valency-two vertex that is not a mark. -/
def Continues (Y : data.SourceVertex) : Prop := nonDanglingValency data Y = 2 ∧ Y ∉ M

open Classical in
/-- **The walk**: the `j`-th occurrence and its entry vertex. It stays put once the row stops. -/
noncomputable def seq (e₀ : data.SourceEdge) (A₀ : data.SourceVertex) :
    ℕ → data.SourceEdge × data.SourceVertex
  | 0 => (e₀, A₀)
  | j + 1 =>
    if h : Continues data M (otherEnd data (seq e₀ A₀ j).1 (seq e₀ A₀ j).2) then
      (stepEdge data h.1 (seq e₀ A₀ j).1, otherEnd data (seq e₀ A₀ j).1 (seq e₀ A₀ j).2)
    else seq e₀ A₀ j

variable {data M} {e₀ : data.SourceEdge} {A₀ : data.SourceVertex}

/-- The `j`-th occurrence. -/
noncomputable abbrev E (e₀ : data.SourceEdge) (A₀ : data.SourceVertex) (j : ℕ) : data.SourceEdge :=
  (seq data M e₀ A₀ j).1

/-- The entry vertex of the `j`-th occurrence. -/
noncomputable abbrev A (e₀ : data.SourceEdge) (A₀ : data.SourceVertex) (j : ℕ) :
    data.SourceVertex :=
  (seq data M e₀ A₀ j).2

/-- The exit vertex of the `j`-th occurrence. -/
noncomputable abbrev exit (e₀ : data.SourceEdge) (A₀ : data.SourceVertex) (j : ℕ) :
    data.SourceVertex :=
  otherEnd data (E (M := M) e₀ A₀ j) (A (M := M) e₀ A₀ j)

/-- The walk starts at its start. -/
theorem seq_zero : seq data M e₀ A₀ 0 = (e₀, A₀) := rfl

/-- A step of the walk where the row continues. -/
theorem seq_succ_of_continues {j : ℕ} (h : Continues data M (exit (M := M) e₀ A₀ j)) :
    seq data M e₀ A₀ (j + 1) =
      (stepEdge data h.1 (E (M := M) e₀ A₀ j), exit (M := M) e₀ A₀ j) := by
  rw [seq, dite_eq_left h]

/-- The walk stays put once the row stops. -/
theorem seq_succ_of_not {j : ℕ} (h : ¬ Continues data M (exit (M := M) e₀ A₀ j)) :
    seq data M e₀ A₀ (j + 1) = seq data M e₀ A₀ j := by
  rw [seq, dite_eq_right h]

/-! ## 1.  Local facts -/

/-- The far end of an occurrence entered at an incident vertex is the other end. -/
theorem otherEnd_ne {e : data.SourceEdge} {Y : data.SourceVertex} (h : Incident data e Y) :
    otherEnd data e Y ≠ Y := by
  unfold otherEnd
  split_ifs with h'
  · rw [← h']; exact (data.sourceEnds_ne e).symm
  · rcases h with h | h
    · exact absurd h h'
    · rw [← h]; exact data.sourceEnds_ne e

/-- Every occurrence of the walk is entered at an incident vertex. -/
theorem incident_A (h₀ : Incident data e₀ A₀) (j : ℕ) :
    Incident data (E (M := M) e₀ A₀ j) (A (M := M) e₀ A₀ j) := by
  induction j with
  | zero => exact h₀
  | succ j ih =>
    by_cases h : Continues data M (exit (M := M) e₀ A₀ j)
    · rw [E, A, seq_succ_of_continues h]
      exact stepEdge_incident data h.1 _
    · rw [E, A, seq_succ_of_not h]
      exact ih

/-- Every occurrence of the walk survives. -/
theorem not_isDangling_E (h₀ : ¬ IsDangling data e₀) (j : ℕ) :
    ¬ IsDangling data (E (M := M) e₀ A₀ j) := by
  induction j with
  | zero => exact h₀
  | succ j ih =>
    by_cases h : Continues data M (exit (M := M) e₀ A₀ j)
    · rw [E, seq_succ_of_continues h]
      exact stepEdge_not_dangling data h.1 _
    · rw [E, seq_succ_of_not h]
      exact ih

/-- The walk continues to the step occurrence. -/
theorem E_succ {j : ℕ} (h : Continues data M (exit (M := M) e₀ A₀ j)) :
    E (M := M) e₀ A₀ (j + 1) = stepEdge data h.1 (E (M := M) e₀ A₀ j) := by
  rw [E, seq_succ_of_continues h]

/-- The next entry is the exit, where the row continues. -/
theorem A_succ {j : ℕ} (h : Continues data M (exit (M := M) e₀ A₀ j)) :
    A (M := M) e₀ A₀ (j + 1) = exit (M := M) e₀ A₀ j := by
  rw [A, seq_succ_of_continues h]

/-! ## 2.  Injectivity and the stop -/

/-- **The row continues along the walk up to `j`.** -/
def RunsTo (e₀ : data.SourceEdge) (A₀ : data.SourceVertex) (j : ℕ) : Prop :=
  ∀ i < j, Continues data M (exit (M := M) e₀ A₀ i)

/-- The two surviving occurrences at a vertex where the row continues. -/
theorem eq_or_eq_of_continues {Y : data.SourceVertex} (hY : Continues data M Y)
    {e f g : data.SourceEdge} (he : ¬ IsDangling data e) (heY : Incident data e Y)
    (hf : ¬ IsDangling data f) (hfY : Incident data f Y) (hg : ¬ IsDangling data g)
    (hgY : Incident data g Y) (hef : e ≠ f) : g = e ∨ g = f := by
  rcases eq_or_eq_stepEdge data hY.1 he heY hg hgY with h | h
  · exact Or.inl h
  · rcases eq_or_eq_stepEdge data hY.1 he heY hf hfY with h' | h'
    · exact absurd h'.symm hef
    · exact Or.inr (h.trans h'.symm)

/-- **The walk from an end is injective while it runs** (a vertex where the row continues carries
only two surviving occurrences, and the start is an end). -/
theorem walk_injective (h₀ : Incident data e₀ A₀) (hNd : ¬ IsDangling data e₀)
    (hEnd : ¬ Continues data M A₀) {l : ℕ} (hRun : RunsTo (M := M) e₀ A₀ l) :
    ∀ j < l + 1, ∀ i < j, E (M := M) e₀ A₀ i ≠ E (M := M) e₀ A₀ j := by
  -- by strong induction on `j`
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj i hij hEq
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hC : Continues data M (exit (M := M) e₀ A₀ j') := hRun j' (by omega)
  -- the entry of `E (j'+1)` is the exit of `E j'`, where both `E j'` and `E (j'+1)` sit
  have hAj : A (M := M) e₀ A₀ (j' + 1) = exit (M := M) e₀ A₀ j' := A_succ hC
  have hEj : E (M := M) e₀ A₀ (j' + 1) = stepEdge data hC.1 (E (M := M) e₀ A₀ j') := E_succ hC
  have hne : E (M := M) e₀ A₀ (j' + 1) ≠ E (M := M) e₀ A₀ j' := by
    rw [hEj]; exact stepEdge_ne data hC.1 _
  have hInc₁ : Incident data (E (M := M) e₀ A₀ j') (exit (M := M) e₀ A₀ j') :=
    incident_otherEnd data _ _
  have hInc₂ : Incident data (E (M := M) e₀ A₀ (j' + 1)) (exit (M := M) e₀ A₀ j') := by
    rw [← hAj]; exact incident_A h₀ _
  have hNdj := not_isDangling_E (M := M) (A₀ := A₀) hNd j'
  have hNdj1 := not_isDangling_E (M := M) (A₀ := A₀) hNd (j' + 1)
  -- `E i = E (j'+1)` meets the exit of `E j'`
  have hIncI : Incident data (E (M := M) e₀ A₀ i) (exit (M := M) e₀ A₀ j') := hEq ▸ hInc₂
  -- the exit of `E j'` is an end of `E i`: its entry or its exit
  rcases eq_or_eq_otherEnd data (incident_A h₀ i) hIncI with hY | hY
  · -- the exit of `E j'` is the entry of `E i`
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact hEnd ((congrArg (Continues data M) hY).mp hC)
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have hCi : Continues data M (exit (M := M) e₀ A₀ i') := hRun i' (by omega)
      have hAi : A (M := M) e₀ A₀ (i' + 1) = exit (M := M) e₀ A₀ i' := A_succ hCi
      -- at that vertex sit `E i'`, `E (i'+1)` and `E j'`
      have hI'inc : Incident data (E (M := M) e₀ A₀ i') (exit (M := M) e₀ A₀ j') := by
        rw [hY, hAi]; exact incident_otherEnd data _ _
      have hEi : E (M := M) e₀ A₀ (i' + 1) = stepEdge data hCi.1 (E (M := M) e₀ A₀ i') := E_succ hCi
      have hne' : E (M := M) e₀ A₀ (i' + 1) ≠ E (M := M) e₀ A₀ i' := by
        rw [hEi]; exact stepEdge_ne data hCi.1 _
      rcases eq_or_eq_of_continues hC hNdj hInc₁ hNdj1 hInc₂
          (not_isDangling_E hNd i') hI'inc hne.symm with h | h
      · -- `E i' = E j'` with `i' < j'`
        exact ih j' (by omega) (by omega) i' (by omega) h
      · -- `E i' = E (j'+1) = E (i'+1)`
        exact hne' (hEq.trans h.symm)
  · -- the exit of `E j'` is the exit of `E i`
    rcases Nat.lt_or_ge i j' with hij' | hij'
    swap
    · have hi : i = j' := by omega
      subst hi
      exact hne hEq.symm
    have hCi : Continues data M (exit (M := M) e₀ A₀ i) := (congrArg (Continues data M) hY).mp hC
    have hEi : E (M := M) e₀ A₀ (i + 1) = stepEdge data hCi.1 (E (M := M) e₀ A₀ i) := E_succ hCi
    have hAi : A (M := M) e₀ A₀ (i + 1) = exit (M := M) e₀ A₀ i := A_succ hCi
    have hIinc : Incident data (E (M := M) e₀ A₀ (i + 1)) (exit (M := M) e₀ A₀ j') :=
      (congrArg (Incident data (E (M := M) e₀ A₀ (i + 1))) (hAi.trans hY.symm)).mp
        (incident_A h₀ _)
    rcases eq_or_eq_of_continues hC hNdj hInc₁ hNdj1 hInc₂ (not_isDangling_E hNd (i + 1)) hIinc
        hne.symm with h | h
    · -- `E (i+1) = E j'`
      rcases Nat.lt_or_ge (i + 1) j' with hlt | hge
      · exact ih j' (by omega) (by omega) (i + 1) hlt h
      · -- then `i + 1 = j'`: the entry and exit of `E j'` coincide
        have hij : i + 1 = j' := by omega
        subst hij
        exact otherEnd_ne (incident_A h₀ (i + 1)) (hY.trans hAi.symm)
    · -- `E (i+1) = E (j'+1) = E i`
      exact stepEdge_ne data hCi.1 _ ((hEi.symm.trans h).trans hEq.symm)

/-- **The walk from an end stops.** -/
theorem exists_stop (h₀ : Incident data e₀ A₀) (hNd : ¬ IsDangling data e₀)
    (hEnd : ¬ Continues data M A₀) :
    ∃ N, ¬ Continues data M (exit (M := M) e₀ A₀ N) := by
  by_contra hAll
  push Not at hAll
  have hInj : Function.Injective (E (M := M) e₀ A₀) := by
    intro i j h
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact walk_injective h₀ hNd hEnd (l := j) (fun k _ ↦ hAll k) j (by omega) i hlt h
    · exact walk_injective h₀ hNd hEnd (l := i) (fun k _ ↦ hAll k) i (by omega) j hlt h.symm
  exact not_injective_infinite_finite _ hInj

open Classical in
/-- **The stop**: the first occurrence whose exit is an end. -/
noncomputable def stop (h₀ : Incident data e₀ A₀) (hNd : ¬ IsDangling data e₀)
    (hEnd : ¬ Continues data M A₀) : ℕ :=
  Nat.find (exists_stop (M := M) h₀ hNd hEnd)

/-- The row does not continue at the exit of the stop. -/
theorem not_continues_stop (h₀ : Incident data e₀ A₀) (hNd : ¬ IsDangling data e₀)
    (hEnd : ¬ Continues data M A₀) :
    ¬ Continues data M (exit (M := M) e₀ A₀ (stop h₀ hNd hEnd)) := by
  classical
  exact Nat.find_spec (exists_stop (M := M) h₀ hNd hEnd)

/-- Before the stop, the row continues at every exit. -/
theorem continues_of_lt_stop (h₀ : Incident data e₀ A₀) (hNd : ¬ IsDangling data e₀)
    (hEnd : ¬ Continues data M A₀) {i : ℕ} (hi : i < stop h₀ hNd hEnd) :
    Continues data M (exit (M := M) e₀ A₀ i) := by
  classical
  by_contra h
  exact Nat.find_min (exists_stop (M := M) h₀ hNd hEnd) hi h

/-- The walk runs to its stop. -/
theorem runsTo_stop (h₀ : Incident data e₀ A₀) (hNd : ¬ IsDangling data e₀)
    (hEnd : ¬ Continues data M A₀) : RunsTo (M := M) e₀ A₀ (stop h₀ hNd hEnd) :=
  fun _ hi ↦ continues_of_lt_stop h₀ hNd hEnd hi

/-- Injectivity up to the stop. -/
theorem E_injOn (h₀ : Incident data e₀ A₀) (hNd : ¬ IsDangling data e₀)
    (hEnd : ¬ Continues data M A₀) {i j : ℕ} (hi : i ≤ stop h₀ hNd hEnd)
    (hj : j ≤ stop h₀ hNd hEnd) (h : E (M := M) e₀ A₀ i = E (M := M) e₀ A₀ j) : i = j := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact walk_injective h₀ hNd hEnd (runsTo_stop h₀ hNd hEnd) j (by omega) i hlt h
  · exact walk_injective h₀ hNd hEnd (runsTo_stop h₀ hNd hEnd) i (by omega) j hlt h.symm

/-! ## 3.  The walk lists the row -/

/-- Consecutive occurrences of the walk lie on one marked row. -/
theorem markedRow_succ (h₀ : Incident data e₀ A₀) (hNd : ¬ IsDangling data e₀) {j : ℕ}
    (h : Continues data M (exit (M := M) e₀ A₀ j)) :
    markedRow M (⟨E (M := M) e₀ A₀ (j + 1), not_isDangling_E hNd _⟩ : NonDanglingEdge data) =
      markedRow M ⟨E (M := M) e₀ A₀ j, not_isDangling_E hNd _⟩ := by
  refine (markedRow_eq_of_markedConsecutive ⟨fun h' ↦ ?_, exit (M := M) e₀ A₀ j, ?_, ?_, h.1, h.2⟩).symm
  · have h'' : E (M := M) e₀ A₀ j = E (M := M) e₀ A₀ (j + 1) := congrArg Subtype.val h'
    rw [E_succ h] at h''
    exact stepEdge_ne data h.1 _ h''.symm
  · exact incident_otherEnd data _ _
  · rw [← A_succ h]; exact incident_A h₀ _

/-- Every occurrence of the walk lies on the row of `e₀`. -/
theorem markedRow_E (h₀ : Incident data e₀ A₀) (hNd : ¬ IsDangling data e₀) (j : ℕ) :
    markedRow M (⟨E (M := M) e₀ A₀ j, not_isDangling_E hNd _⟩ : NonDanglingEdge data) =
      markedRow M ⟨e₀, hNd⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    by_cases h : Continues data M (exit (M := M) e₀ A₀ j)
    · rw [markedRow_succ h₀ hNd h]; exact ih
    · have hEq : E (M := M) e₀ A₀ (j + 1) = E (M := M) e₀ A₀ j := by rw [E, seq_succ_of_not h]
      have : (⟨E (M := M) e₀ A₀ (j + 1), not_isDangling_E hNd _⟩ : NonDanglingEdge data) =
          ⟨E (M := M) e₀ A₀ j, not_isDangling_E hNd _⟩ := Subtype.ext hEq
      rw [this]; exact ih

/-- **Closure**: an occurrence meeting an occurrence of the walk where the row continues is in the
walk, at an adjacent index. -/
theorem adjacent_of_meet (h₀ : Incident data e₀ A₀) (hNd : ¬ IsDangling data e₀)
    (hEnd : ¬ Continues data M A₀) {j : ℕ} (hj : j ≤ stop h₀ hNd hEnd) {f : data.SourceEdge}
    (hf : ¬ IsDangling data f) (hne : f ≠ E (M := M) e₀ A₀ j) {Y : data.SourceVertex}
    (hjY : Incident data (E (M := M) e₀ A₀ j) Y) (hfY : Incident data f Y)
    (hY : Continues data M Y) :
    (j < stop h₀ hNd hEnd ∧ Y = exit (M := M) e₀ A₀ j ∧ f = E (M := M) e₀ A₀ (j + 1)) ∨
      (∃ i, j = i + 1 ∧ Y = exit (M := M) e₀ A₀ i ∧ f = E (M := M) e₀ A₀ i) := by
  rcases eq_or_eq_otherEnd data (incident_A h₀ j) hjY with hYA | hYE
  · -- `Y` is the entry of `E j`
    right
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · exact absurd ((congrArg (Continues data M) hYA).mp hY) hEnd
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hC : Continues data M (exit (M := M) e₀ A₀ i) :=
        continues_of_lt_stop h₀ hNd hEnd (by omega)
      have hAi : A (M := M) e₀ A₀ (i + 1) = exit (M := M) e₀ A₀ i := A_succ hC
      refine ⟨i, rfl, hYA.trans hAi, ?_⟩
      have hIi : Incident data (E (M := M) e₀ A₀ i) Y := by
        rw [hYA, hAi]; exact incident_otherEnd data _ _
      have hEi : E (M := M) e₀ A₀ (i + 1) = stepEdge data hC.1 (E (M := M) e₀ A₀ i) := E_succ hC
      have hne' : E (M := M) e₀ A₀ (i + 1) ≠ E (M := M) e₀ A₀ i := by
        rw [hEi]; exact stepEdge_ne data hC.1 _
      rcases eq_or_eq_of_continues hY (not_isDangling_E hNd (i + 1)) hjY (not_isDangling_E hNd i)
          hIi hf hfY hne' with h | h
      · exact absurd h hne
      · exact h
  · -- `Y` is the exit of `E j`
    left
    have hC : Continues data M (exit (M := M) e₀ A₀ j) := (congrArg (Continues data M) hYE).mp hY
    have hjlt : j < stop h₀ hNd hEnd := by
      rcases Nat.lt_or_ge j (stop h₀ hNd hEnd) with h | h
      · exact h
      · have hjs : j = stop h₀ hNd hEnd := by omega
        subst hjs
        exact absurd hC (not_continues_stop h₀ hNd hEnd)
    refine ⟨hjlt, hYE, ?_⟩
    rw [E_succ hC]
    have hfE : Incident data f (exit (M := M) e₀ A₀ j) := (congrArg (Incident data f) hYE).mp hfY
    rcases eq_or_eq_stepEdge data hC.1 (not_isDangling_E hNd j) (incident_otherEnd data _ _) hf
        hfE with h | h
    · exact absurd h hne
    · exact h

/-- **The walk lists the marked row**: every occurrence of the row of `e₀` is `E j` for some
`j ≤ stop`. -/
theorem exists_index (h₀ : Incident data e₀ A₀) (hNd : ¬ IsDangling data e₀)
    (hEnd : ¬ Continues data M A₀) (f : NonDanglingEdge data)
    (hf : markedRow M f = markedRow M ⟨e₀, hNd⟩) :
    ∃ j ≤ stop h₀ hNd hEnd, f.1 = E (M := M) e₀ A₀ j := by
  -- the set of walk occurrences is closed under marked consecutiveness
  let P : NonDanglingEdge data → Prop := fun g ↦ ∃ j ≤ stop h₀ hNd hEnd, g.1 = E (M := M) e₀ A₀ j
  have hClosed : ∀ g₁ g₂, MarkedConsecutive data M g₁ g₂ → P g₁ → P g₂ := by
    rintro g₁ g₂ ⟨hne, Y, h₁, h₂, hY2, hYM⟩ ⟨j, hj, hg₁⟩
    rw [hg₁] at h₁
    rcases adjacent_of_meet h₀ hNd hEnd hj g₂.2 (fun h ↦ hne (Subtype.ext (hg₁.trans h.symm)))
        h₁ h₂ ⟨hY2, hYM⟩ with ⟨hlt, -, h⟩ | ⟨i, rfl, -, h⟩
    · exact ⟨j + 1, by omega, h⟩
    · exact ⟨i, by omega, h⟩
  have hSymm : ∀ g₁ g₂, MarkedConsecutive data M g₁ g₂ → MarkedConsecutive data M g₂ g₁ := by
    rintro g₁ g₂ ⟨hne, Y, h₁, h₂, h3, h4⟩
    exact ⟨hne.symm, Y, h₂, h₁, h3, h4⟩
  have hGen : ∀ g₁ g₂, Relation.EqvGen (MarkedConsecutive data M) g₁ g₂ → (P g₁ ↔ P g₂) := by
    intro g₁ g₂ h
    induction h with
    | rel a b hab => exact ⟨hClosed a b hab, hClosed b a (hSymm a b hab)⟩
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have hP₀ : P ⟨e₀, hNd⟩ := ⟨0, Nat.zero_le _, rfl⟩
  exact (hGen _ _ (Quot.eqvGen_exact hf)).mpr hP₀

end MarkedWalk

end DraismaVargas.Count.MarkedCountGeneral
