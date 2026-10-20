module

public import DraismaVargasMarkedCount.MarkedCountGeneral.DropTypeZero
public import DraismaVargasMarkedCount.MarkedCount.Core

@[expose] public section

/-!
# The drop lemma: one more mark

The bookkeeping of the
drop lemma (`Drop.typedCount_dropLast`), kept apart from module `Drop` so that the modules of the
drop can use it: the marks and types of `subdivide core s` (`snocMark`, `snocType`), the merged
request (`mergeRequest`), and the marked cubic core with one more mark (`isMarkedCubic_snoc`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.Count.MarkedCount
open GenusSixExistence.Tripod.Gadget (subdivide incidenceDegree_subdivide_castSucc
  incidenceDegree_subdivide_last)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p k degree : ℕ}

/-! ## 1.  One more mark -/

/-- The marks of `subdivide core s`: the old marks, then the new vertex. -/
def snocMark (mark : Fin k → Fin n) : Fin (k + 1) → Fin (n + 1) :=
  Fin.lastCases (motive := fun _ ↦ Fin (n + 1)) (Fin.last n) fun j ↦ (mark j).castSucc

/-- The types with one more mark, of type `a`. -/
def snocType (types : Fin k → ℕ) (a : ℕ) : Fin (k + 1) → ℕ :=
  Fin.lastCases (motive := fun _ ↦ ℕ) a types

/-- The once-marked mark is a snoc of the empty mark. -/
theorem onceMark_eq_snocMark (n : ℕ) (mark : Fin 0 → Fin n) :
    onceMark n = snocMark mark := by
  funext j
  fin_cases j
  rfl

/-- The twice-marked marks are a snoc of the once-marked mark. -/
theorem twiceMark_eq_snocMark (n : ℕ) : twiceMark n = snocMark (onceMark n) := by
  funext j
  fin_cases j <;> rfl

/-- A one-entry type vector is a snoc. -/
theorem vecOne_eq_snocType (types : Fin 0 → ℕ) (a : ℕ) : ![a] = snocType types a := by
  funext j
  fin_cases j
  rfl

/-- A two-entry type vector is a snoc. -/
theorem vecTwo_eq_snocType (a b : ℕ) : ![a, b] = snocType ![a] b := by
  funext j
  fin_cases j <;> rfl

/-- **The merged request** on `core`, from a request on `subdivide core s`: the two pieces of
`s` (slots `s.castSucc` and `last p`) are joined. -/
def mergeRequest (s : Fin p) (y : Fin (p + 1) → ℚ) : Fin p → ℚ :=
  fun i ↦ y i.castSucc + if i = s then y (Fin.last p) else 0

/-- The merged request is positive when the request is. -/
theorem mergeRequest_pos {s : Fin p} {y : Fin (p + 1) → ℚ} (hy : ∀ i, 0 < y i) (i : Fin p) :
    0 < mergeRequest s y i := by
  unfold mergeRequest
  split_ifs
  · linarith [hy i.castSucc, hy (Fin.last p)]
  · linarith [hy i.castSucc]

/-- **`subdivide core s` with one more mark is marked-cubic**: the new vertex has incidence
degree two, the old ones keep theirs. -/
theorem isMarkedCubic_snoc {core : Core n p} {mark : Fin k → Fin n} (hc : IsMarkedCubic core mark)
    (s : Fin p) : IsMarkedCubic (subdivide core s) (snocMark mark) where
  injective := by
    intro i j hij
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => rfl
      | cast j =>
        simp only [snocMark, Fin.lastCases_last, Fin.lastCases_castSucc] at hij
        exact absurd hij.symm (Fin.castSucc_lt_last _).ne
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [snocMark, Fin.lastCases_last, Fin.lastCases_castSucc] at hij
        exact absurd hij (Fin.castSucc_lt_last _).ne
      | cast j =>
        simp only [snocMark, Fin.lastCases_castSucc] at hij
        exact congrArg _ (hc.injective (Fin.castSucc_injective _ hij))
  mark_degree j := by
    induction j using Fin.lastCases with
    | last =>
      simp only [snocMark, Fin.lastCases_last]
      exact incidenceDegree_subdivide_last core s
    | cast j =>
      simp only [snocMark, Fin.lastCases_castSucc]
      rw [incidenceDegree_subdivide_castSucc]
      exact hc.mark_degree j
  other_degree v hv := by
    induction v using Fin.lastCases with
    | last => exact absurd ⟨Fin.last k, by simp [snocMark]⟩ hv
    | cast v =>
      rw [incidenceDegree_subdivide_castSucc]
      refine hc.other_degree v fun ⟨j, hj⟩ ↦ hv ⟨j.castSucc, ?_⟩
      simp [snocMark, hj]

end DraismaVargas.Count.MarkedCountGeneral
