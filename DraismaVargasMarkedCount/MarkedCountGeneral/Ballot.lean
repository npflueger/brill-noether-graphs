module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# Slope sequences, ballot numbers, and the chain-tail identity

The tail counts of the two-point ramified count, and the identity that solves its triangular
system. Pure combinatorics: nothing here mentions a graph.

* `IsSlopeSeq a j s`, `SlopeSeq a j`: the slope sequences of a caterpillar tail of genus `a ≥ 1`
  with `j` ascents (the indices of the path edges of a member over the tail, which by the rigidity
  of the tail change by `±1` along it; the same sequences parametrize the regrowth): `s : Fin a → ℕ`
  (0-indexed, so `s 0 = s_1` and `s (a - 1) = s_a`), with `s_a = 2`, `s_i ≥ 1`, `s_{i+1} - s_i = ±1`
  and `s_1 = a + 1 - 2j`. They are finite because `s_i + i ≤ a + 1` (`IsSlopeSeq.add_le`).
* `ballot a j = C(a, j) - C(a, j - 1)`, the **formal** ballot number, with `C(a, -1) = 0` and no
  truncation for `2j > a`: `ballot a (a + 1) = -1` (the proof of the chain-tail identity uses the
  formal `M_j` on `0 ≤ j ≤ a + 1`).
* **The slope count** `card_slopeSeq`: `#SlopeSeq a j = ballot a j` for `2j ≤ a`.
* **The chain-tail identity** `chainTail_identity`: for `g = 2L + a + b`, `L ≥ 1`,
  `Σ_{j ≤ a/2} Σ_{k ≤ b/2} M_j(a) M_k(b) (C(g, L+a+k-j) - C(g, L+j+k-1)) = C_{L+a+b}`, the sums
  truncated at `a/2` and `b/2` (the range of the slope count) and the `M` formal.

## Proved here

**`card_slopeSeq`** (the slope count, by deleting the first slope:
`ascentEquiv`, `descentEquiv`, and Pascal's rule `ballot_succ`), `catalan_eq_choose_sub`, the
one-variable reflection identity `ballot_reflection_sum` (two reflections and four Vandermonde
sums, as in the proof of the chain-tail identity), **`chainTail_identity`** and its once-marked form
`chainTail_identity_once`.
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open Finset

/-! ## 1.  Slope sequences -/

/-- **A slope sequence** of a caterpillar tail of genus `a` with `j` ascents (0-indexed):
positive, ending at `2`, steps `±1`, starting at `a + 1 - 2j`. -/
def IsSlopeSeq (a j : ℕ) (s : Fin a → ℕ) : Prop :=
  (∀ i, 1 ≤ s i) ∧ (∀ i : Fin a, i.val + 1 = a → s i = 2) ∧
    (∀ i i' : Fin a, i'.val = i.val + 1 → s i' = s i + 1 ∨ s i = s i' + 1) ∧
    (∀ i : Fin a, i.val = 0 → s i + 2 * j = a + 1)

/-- The slope sequences of genus `a` with `j` ascents. -/
def SlopeSeq (a j : ℕ) : Type := {s : Fin a → ℕ // IsSlopeSeq a j s}

/-- A slope sequence descends to `2` in unit steps, so `s_i + i ≤ a + 1`. -/
theorem IsSlopeSeq.add_le {a j : ℕ} {s : Fin a → ℕ} (h : IsSlopeSeq a j s) (i : Fin a) :
    s i + i.val ≤ a + 1 := by
  suffices H : ∀ m (i : Fin a), a - 1 - i.val = m → s i + i.val ≤ a + 1 from H _ i rfl
  intro m
  induction m with
  | zero =>
    intro i hi
    rw [h.2.1 i (by omega)]
    omega
  | succ m ih =>
    intro i hi
    have hlt : i.val + 1 < a := by omega
    have h' := ih ⟨i.val + 1, hlt⟩ (by simp; omega)
    rcases h.2.2.1 i ⟨i.val + 1, hlt⟩ rfl with h1 | h1 <;> simp only at h' <;> omega

instance (a j : ℕ) : Finite (SlopeSeq a j) :=
  Finite.of_injective (fun s : SlopeSeq a j ↦ fun i ↦
      (⟨s.1 i, by have := s.2.add_le i; omega⟩ : Fin (a + 2)))
    fun s t h ↦ Subtype.ext (funext fun i ↦ by simpa using congrFun h i)

noncomputable instance (a j : ℕ) : Fintype (SlopeSeq a j) := Fintype.ofFinite _

/-! ## 2.  Ballot numbers -/

/-- **The formal ballot number** `M_j(a) = C(a, j) - C(a, j - 1)`, with `C(a, -1) = 0`. -/
def ballot (a j : ℕ) : ℤ := (a.choose j : ℤ) - if j = 0 then 0 else (a.choose (j - 1) : ℤ)

@[simp] theorem ballot_zero (a : ℕ) : ballot a 0 = 1 := by simp [ballot]

/-- Pascal's rule for the formal ballot numbers. -/
theorem ballot_succ (a j : ℕ) :
    ballot (a + 1) j = ballot a j + if j = 0 then 0 else ballot a (j - 1) := by
  unfold ballot
  rcases j with _ | _ | j
  · simp
  · simp [Nat.choose_succ_succ]
  · simp only [Nat.add_one_sub_one, add_eq_zero, one_ne_zero, and_false, ite_false,
      Nat.choose_succ_succ]
    push_cast
    ring

/-- At the middle `2j = a + 1` the formal ballot number vanishes. -/
theorem ballot_middle {a j : ℕ} (h : 2 * j = a + 1) : ballot a j = 0 := by
  unfold ballot
  rw [ite_eq_right (by omega), ← Nat.choose_symm (by omega : j ≤ a),
    show a - j = j - 1 by omega, sub_self]

/-! ### The slope count -/

section Card

variable {a j : ℕ}

/-- Deleting the first slope. -/
theorem IsSlopeSeq.tail {s : Fin (a + 1) → ℕ} (h : IsSlopeSeq (a + 1) j s) (ha : 1 ≤ a) {j' : ℕ}
    (hj' : s ⟨1, by omega⟩ + 2 * j' = a + 1) : IsSlopeSeq a j' (Fin.tail s) := by
  refine ⟨fun i ↦ h.1 _, fun i hi ↦ h.2.1 _ (by simp; omega), fun i i' hi ↦ ?_, fun i hi ↦ ?_⟩
  · exact h.2.2.1 i.succ i'.succ (by simp; omega)
  · have : i.succ = ⟨1, by omega⟩ := Fin.ext (by simp; omega)
    simpa [Fin.tail, this] using hj'

/-- Adding a first slope. -/
theorem IsSlopeSeq.cons {t : Fin a → ℕ} {j' : ℕ} (h : IsSlopeSeq a j' t) (ha : 1 ≤ a) {x : ℕ}
    (hx : 1 ≤ x) (hstep : t ⟨0, ha⟩ = x + 1 ∨ x = t ⟨0, ha⟩ + 1) (hfirst : x + 2 * j = a + 2) :
    IsSlopeSeq (a + 1) j (Fin.cons x t : Fin (a + 1) → ℕ) := by
  refine ⟨fun i ↦ ?_, fun i hi ↦ ?_, fun i i' hi ↦ ?_, fun i hi ↦ ?_⟩
  · refine Fin.cases ?_ (fun i ↦ ?_) i
    · simpa using hx
    · simpa using h.1 i
  · refine Fin.cases (fun h0 ↦ ?_) (fun i hi ↦ ?_) i hi
    · simp at h0; omega
    · simpa using h.2.1 i (by simp at hi; omega)
  · revert hi
    refine Fin.cases (fun hi ↦ ?_) (fun i hi ↦ ?_) i
    · obtain rfl : i' = (⟨0, ha⟩ : Fin a).succ := Fin.ext (by simp at hi ⊢; omega)
      rw [Fin.cons_succ, Fin.cons_zero]
      exact hstep
    · revert hi
      refine Fin.cases (fun hi ↦ absurd hi (by simp)) (fun i'' hi ↦ ?_) i'
      rw [Fin.cons_succ, Fin.cons_succ]
      exact h.2.2.1 i i'' (by simp at hi; omega)
  · have : i = 0 := Fin.ext hi
    subst this
    simpa using hfirst

/-- The first two slopes, as elements of `Fin (a + 1)`. -/
def first (a : ℕ) : Fin (a + 1) := ⟨0, by omega⟩
/-- The second slope. -/
def second (a : ℕ) (ha : 1 ≤ a) : Fin (a + 1) := ⟨1, by omega⟩

/-- **Sequences starting with an ascent** are the sequences of genus `a` with one ascent fewer. -/
noncomputable def ascentEquiv (ha : 1 ≤ a) (hj : 1 ≤ j) (hj' : 2 * j ≤ a + 1) :
    {s : SlopeSeq (a + 1) j // s.1 (second a ha) = s.1 (first a) + 1} ≃ SlopeSeq a (j - 1) where
  toFun s := ⟨Fin.tail s.1.1, s.1.2.tail ha (by
    have h1 := s.1.2.2.2.2 (first a) rfl
    have h2 := s.2
    simp only [first, second] at h1 h2 ⊢
    omega)⟩
  invFun t := ⟨⟨Fin.cons (t.1 ⟨0, ha⟩ - 1) t.1, t.2.cons ha (by
      have := t.2.2.2.2 ⟨0, ha⟩ rfl; omega) (Or.inl (by
      have := t.2.2.2.2 ⟨0, ha⟩ rfl; omega)) (by
      have := t.2.2.2.2 ⟨0, ha⟩ rfl; omega)⟩, by
    have := t.2.2.2.2 ⟨0, ha⟩ rfl
    simp only [first, second]
    rw [show (⟨1, by omega⟩ : Fin (a + 1)) = (⟨0, ha⟩ : Fin a).succ from Fin.ext rfl,
      Fin.cons_succ, show (⟨0, by omega⟩ : Fin (a + 1)) = 0 from rfl, Fin.cons_zero]
    omega⟩
  left_inv s := by
    obtain ⟨⟨s, hs⟩, hup⟩ := s
    refine Subtype.ext (Subtype.ext ?_)
    simp only
    conv_rhs => rw [← Fin.cons_self_tail s]
    congr 1
    simp only [first, second] at hup
    rw [show (⟨0, ha⟩ : Fin a) = ⟨0, ha⟩ from rfl, Fin.tail,
      show (⟨0, ha⟩ : Fin a).succ = (⟨1, by omega⟩ : Fin (a + 1)) from Fin.ext rfl, hup]
    rfl
  right_inv t := by
    refine Subtype.ext ?_
    simp

/-- **Sequences starting with a descent** are the sequences of genus `a` with as many ascents. -/
noncomputable def descentEquiv (ha : 1 ≤ a) :
    {s : SlopeSeq (a + 1) j // ¬ s.1 (second a ha) = s.1 (first a) + 1} ≃ SlopeSeq a j where
  toFun s := ⟨Fin.tail s.1.1, s.1.2.tail ha (by
    have h1 := s.1.2.2.2.2 (first a) rfl
    have h3 := s.1.2.2.2.1 (first a) (second a ha) rfl
    have h2 := s.2
    simp only [first, second] at h1 h2 h3 ⊢
    omega)⟩
  invFun t := ⟨⟨Fin.cons (t.1 ⟨0, ha⟩ + 1) t.1, t.2.cons ha (by omega) (Or.inr rfl) (by
      have := t.2.2.2.2 ⟨0, ha⟩ rfl; omega)⟩, by
    simp only [first, second]
    rw [show (⟨1, by omega⟩ : Fin (a + 1)) = (⟨0, ha⟩ : Fin a).succ from Fin.ext rfl,
      Fin.cons_succ, show (⟨0, by omega⟩ : Fin (a + 1)) = 0 from rfl, Fin.cons_zero]
    omega⟩
  left_inv s := by
    obtain ⟨⟨s, hs⟩, hdown⟩ := s
    refine Subtype.ext (Subtype.ext ?_)
    simp only
    conv_rhs => rw [← Fin.cons_self_tail s]
    congr 1
    have h3 := hs.2.2.1 (first a) (second a ha) rfl
    simp only [first, second] at hdown h3
    rw [Fin.tail, show (⟨0, ha⟩ : Fin a).succ = (⟨1, by omega⟩ : Fin (a + 1)) from Fin.ext rfl]
    change _ = s ⟨0, by omega⟩
    omega
  right_inv t := by
    refine Subtype.ext ?_
    simp

theorem card_ascent (ha : 1 ≤ a) (hj' : 2 * j ≤ a + 1) :
    Fintype.card {s : SlopeSeq (a + 1) j // s.1 (second a ha) = s.1 (first a) + 1} =
      if j = 0 then 0 else Fintype.card (SlopeSeq a (j - 1)) := by
  split_ifs with hj
  · subst hj
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun s ↦ ?_⟩
    have h1 := s.1.2.2.2.2 (first a) rfl
    have hle := s.1.2.add_le (second a ha)
    have h2 := s.2
    simp only [first, second] at h1 h2 hle
    omega
  · exact Fintype.card_congr (ascentEquiv ha (by omega) hj')

theorem card_descent (ha : 1 ≤ a) (hj' : 2 * j ≤ a + 1) :
    Fintype.card {s : SlopeSeq (a + 1) j // ¬ s.1 (second a ha) = s.1 (first a) + 1} =
      if 2 * j ≤ a then Fintype.card (SlopeSeq a j) else 0 := by
  split_ifs with hj
  · exact Fintype.card_congr (descentEquiv ha)
  · rw [Fintype.card_eq_zero_iff]
    refine ⟨fun s ↦ ?_⟩
    have h1 := s.1.2.2.2.2 (first a) rfl
    have h3 := s.1.2.2.2.1 (first a) (second a ha) rfl
    have hpos := s.1.2.1 (second a ha)
    have h2 := s.2
    simp only [first, second] at h1 h2 h3 hpos
    omega

end Card

/-- **The slope count**: the slope sequences with `j` ascents number `C(a, j) - C(a, j - 1)`.

*Proof.* Delete the first slope: a sequence of genus `a + 1` with `s_1 = a + 2 - 2j`
restricts to one of genus `a` starting at `s_1 + 1` (an ascent, `j - 1` ascents left,
`ascentEquiv`) or at `s_1 - 1` (a descent, possible iff `2j ≤ a`, `descentEquiv`). The formal
ballot numbers satisfy the same recursion (`ballot_succ`, `ballot_middle`). -/
theorem card_slopeSeq {a j : ℕ} (ha : 1 ≤ a) (hj : 2 * j ≤ a) :
    (Fintype.card (SlopeSeq a j) : ℤ) = ballot a j := by
  induction a generalizing j with
  | zero => omega
  | succ a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha'
    · -- genus one: the single sequence `(2)`
      obtain rfl : j = 0 := by omega
      have : Fintype.card (SlopeSeq 1 0) = 1 := by
        rw [Fintype.card_eq_one_iff]
        refine ⟨⟨fun _ ↦ 2, fun _ ↦ by simp, fun _ _ ↦ rfl,
          fun i i' h ↦ absurd h (by have := i'.isLt; omega), fun _ _ ↦ rfl⟩,
          fun s ↦ Subtype.ext (funext fun i ↦ ?_)⟩
        exact s.2.2.1 i (by omega)
      rw [this]
      simp
    · have hSplit := Fintype.card_congr (Equiv.sumCompl fun s : SlopeSeq (a + 1) j ↦
        s.1 (second a ha') = s.1 (first a) + 1)
      rw [Fintype.card_sum, card_ascent ha' hj, card_descent ha' hj] at hSplit
      rw [← hSplit, ballot_succ]
      push_cast
      have hA : (if j = 0 then (0 : ℤ) else (Fintype.card (SlopeSeq a (j - 1)) : ℤ)) =
          if j = 0 then 0 else ballot a (j - 1) := by
        split_ifs with h0
        · rfl
        · exact ih ha' (by omega)
      have hB : (if 2 * j ≤ a then (Fintype.card (SlopeSeq a j) : ℤ) else 0) = ballot a j := by
        split_ifs with h2
        · exact ih ha' h2
        · exact (ballot_middle (by omega)).symm
      rw [hA, hB]
      ring

/-! ## 3.  Catalan numbers as a difference of binomials -/

/-- `C_m = C(2m, m) - C(2m, m - 1)` for `m ≥ 1`. -/
theorem catalan_eq_choose_sub {m : ℕ} (hm : 1 ≤ m) :
    (catalan m : ℤ) = ((2 * m).choose m : ℤ) - ((2 * m).choose (m - 1) : ℤ) := by
  have hc := succ_mul_catalan_eq_centralBinom m
  rw [Nat.centralBinom_eq_two_mul_choose] at hc
  have hp := Nat.choose_succ_right_eq (2 * m) (m - 1)
  rw [show m - 1 + 1 = m by omega, show 2 * m - (m - 1) = m + 1 by omega] at hp
  have hc' : ((m : ℤ) + 1) * catalan m = ((2 * m).choose m : ℤ) := by exact_mod_cast hc
  have hp' : ((2 * m).choose m : ℤ) * m = ((2 * m).choose (m - 1) : ℤ) * (m + 1) := by
    exact_mod_cast hp
  have hne : ((m : ℤ) + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ hne
  linear_combination hc' - hp'

/-! ## 4.  Vandermonde, in the shape needed -/

/-- `Σ_{i ≤ a} C(a, i) C(G, k - i) = C(a + G, k)` for `a ≤ k`. -/
theorem vandermonde_range (a G k : ℕ) (hk : a ≤ k) :
    ∑ i ∈ range (a + 1), (a.choose i : ℤ) * (G.choose (k - i) : ℤ) = ((a + G).choose k : ℤ) := by
  have h := Nat.add_choose_eq a G k
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ a.choose i * G.choose j) k] at h
  rw [h]
  push_cast
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i hi hni
    simp only [Finset.mem_range] at hi hni
    rw [Nat.choose_eq_zero_of_lt (by omega : a < i)]
    simp

/-! ## 5.  The one-variable reflection identity -/

section Reflection

variable (G a c : ℕ)

/-- The summand `M_j(a) (C(G, c + a - j) - C(G, c + j - 1))`. -/
def reflSummand (j : ℕ) : ℤ :=
  ballot a j * ((G.choose (c + a - j) : ℤ) - (G.choose (c + j - 1) : ℤ))

variable {G a c}

/-- The four Vandermonde sums of the chain-tail identity, over the formal range `0 ≤ j ≤ a + 1`. -/
theorem reflSummand_full_sum (hc : 1 ≤ c) :
    ∑ j ∈ range (a + 2), reflSummand G a c j =
      2 * (((G + a).choose (c + a) : ℤ) - ((G + a).choose (c + a - 1) : ℤ)) := by
  -- the four sums
  have S1 : ∑ j ∈ range (a + 2), (a.choose j : ℤ) * (G.choose (c + a - j) : ℤ) =
      ((G + a).choose (c + a) : ℤ) := by
    rw [Finset.sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero,
      vandermonde_range a G (c + a) (by omega), add_comm a G]
  have S2 : ∑ j ∈ range (a + 2), (a.choose j : ℤ) * (G.choose (c + j - 1) : ℤ) =
      ((G + a).choose (c + a - 1) : ℤ) := by
    rw [Finset.sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero]
    rw [add_comm G a, ← vandermonde_range a G (c + a - 1) (by omega)]
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    simp only [Finset.mem_range] at hj
    rw [show a + 1 - 1 - j = a - j by omega, Nat.choose_symm (by omega : j ≤ a)]
    congr 3
    omega
  have S3 : ∑ j ∈ range (a + 2),
      (if j = 0 then 0 else (a.choose (j - 1) : ℤ)) * (G.choose (c + a - j) : ℤ) =
      ((G + a).choose (c + a - 1) : ℤ) := by
    rw [Finset.sum_range_succ', ite_eq_left rfl, zero_mul, add_zero, add_comm G a,
      ← vandermonde_range a G (c + a - 1) (by omega)]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [ite_eq_right (Nat.succ_ne_zero j), Nat.add_sub_cancel]
    congr 3
    omega
  have S4 : ∑ j ∈ range (a + 2),
      (if j = 0 then 0 else (a.choose (j - 1) : ℤ)) * (G.choose (c + j - 1) : ℤ) =
      ((G + a).choose (c + a) : ℤ) := by
    rw [Finset.sum_range_succ', ite_eq_left rfl, zero_mul, add_zero, add_comm G a,
      ← vandermonde_range a G (c + a) (by omega)]
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    simp only [Finset.mem_range] at hj
    rw [ite_eq_right (Nat.succ_ne_zero _), Nat.add_sub_cancel,
      show a + 1 - 1 - j = a - j by omega, Nat.choose_symm (by omega : j ≤ a)]
    congr 3
    omega
  have hExpand : ∀ j, reflSummand G a c j =
      (a.choose j : ℤ) * (G.choose (c + a - j) : ℤ) -
        (a.choose j : ℤ) * (G.choose (c + j - 1) : ℤ) -
        (if j = 0 then 0 else (a.choose (j - 1) : ℤ)) * (G.choose (c + a - j) : ℤ) +
        (if j = 0 then 0 else (a.choose (j - 1) : ℤ)) * (G.choose (c + j - 1) : ℤ) := by
    intro j
    unfold reflSummand ballot
    ring
  simp only [hExpand, Finset.sum_add_distrib, Finset.sum_sub_distrib, S1, S2, S3, S4]
  ring

/-- The formal ballot numbers change sign under `j ↦ a + 1 - j`. -/
theorem ballot_reflect {j : ℕ} (hj : j ≤ a + 1) : ballot a (a + 1 - j) = -ballot a j := by
  unfold ballot
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · simp [Nat.choose_succ_self]
  · rcases Nat.lt_or_ge j (a + 1) with hlt | hge
    · have h1 : a + 1 - j ≠ 0 := by omega
      rw [ite_eq_right h1, ite_eq_right (by omega : j ≠ 0), show a + 1 - j - 1 = a - j by omega,
        Nat.choose_symm (by omega : j ≤ a),
        show a + 1 - j = a - (j - 1) by omega, Nat.choose_symm (by omega : j - 1 ≤ a)]
      ring
    · have hj' : j = a + 1 := by omega
      subst hj'
      simp [Nat.choose_succ_self]

/-- **The summand is symmetric** under `j ↦ a + 1 - j` (both factors change sign). -/
theorem reflSummand_reflect (hc : 1 ≤ c) {j : ℕ} (hj : j ≤ a + 1) :
    reflSummand G a c (a + 1 - j) = reflSummand G a c j := by
  unfold reflSummand
  rw [ballot_reflect hj, show c + a - (a + 1 - j) = c + j - 1 by omega,
    show c + (a + 1 - j) - 1 = c + a - j by omega]
  ring

/-- At the fixed point `j = (a + 1)/2` (`a` odd) the summand vanishes. -/
theorem reflSummand_fixed (hc : 1 ≤ c) {j : ℕ} (hj : 2 * j = a + 1) :
    reflSummand G a c j = 0 := by
  unfold reflSummand
  rw [show c + a - j = c + j - 1 by omega, sub_self, mul_zero]

/-- **The one-variable reflection identity** (the first reflection in the proof of the chain-tail
identity): for `c ≥ 1`,
`Σ_{j ≤ a/2} M_j(a) (C(G, c + a - j) - C(G, c + j - 1)) = C(G + a, c + a) - C(G + a, c + a - 1)`.
The sum over the formal range `0 ≤ j ≤ a + 1` is twice the truncated one, by the symmetry of the
summand, and is computed by Vandermonde. -/
theorem ballot_reflection_sum (hc : 1 ≤ c) :
    ∑ j ∈ range (a / 2 + 1), reflSummand G a c j =
      ((G + a).choose (c + a) : ℤ) - ((G + a).choose (c + a - 1) : ℤ) := by
  have hFull := reflSummand_full_sum (G := G) (a := a) hc
  set m := a / 2 with hm
  have hSplit : ∑ j ∈ range (a + 2), reflSummand G a c j =
      ∑ j ∈ range (m + 1), reflSummand G a c j +
        ∑ j ∈ range (a + 1 - m), reflSummand G a c (m + 1 + j) := by
    rw [show a + 2 = (m + 1) + (a + 1 - m) by omega, Finset.sum_range_add]
  have hSecond : ∑ j ∈ range (a + 1 - m), reflSummand G a c (m + 1 + j) =
      ∑ j ∈ range (a + 1 - m), reflSummand G a c j := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    simp only [Finset.mem_range] at hj
    rw [← reflSummand_reflect hc (by omega : m + 1 + (a + 1 - m - 1 - j) ≤ a + 1)]
    congr 1
    omega
  have hHalf : ∑ j ∈ range (a + 1 - m), reflSummand G a c j =
      ∑ j ∈ range (m + 1), reflSummand G a c j := by
    rcases Nat.even_or_odd a with ⟨r, hr⟩ | ⟨r, hr⟩
    · rw [show a + 1 - m = m + 1 by omega]
    · rw [show a + 1 - m = m + 1 + 1 by omega, Finset.sum_range_succ,
        reflSummand_fixed hc (by omega : 2 * (m + 1) = a + 1), add_zero]
  rw [hSplit, hSecond, hHalf] at hFull
  linarith

end Reflection

/-! ## 6.  The chain-tail identity -/

/-- **The chain-tail identity**. With `g = 2L + a + b` and `L ≥ 1` (so `d = L + a + b + 1`
and `L = g - d + 1`), and `f(j, k) = N(g; a - 2j, b - 2k)_{d - j - k}
= C(g, L + a + k - j) - C(g, L + j + k - 1)`:

  `Σ_{j ≤ a/2} Σ_{k ≤ b/2} M_j(a) M_k(b) f(j, k) = C_{L + a + b} = C_{(g + a + b)/2}`,

with the formal ballot numbers `M`. *Proof:* the one-variable identity in `j` at
`c = L + k`, then `C(g + a, L + a + k) = C(g + a, L + a + b - k)` and the one-variable identity in
`k` at `c = L + a`. -/
theorem chainTail_identity {g a b L : ℕ} (hL : 1 ≤ L) (hg : g = 2 * L + a + b) :
    ∑ j ∈ range (a / 2 + 1), ∑ k ∈ range (b / 2 + 1),
        ballot a j * ballot b k *
          ((g.choose (L + a + k - j) : ℤ) - (g.choose (L + j + k - 1) : ℤ)) =
      catalan (L + a + b) := by
  rw [Finset.sum_comm]
  have hInner : ∀ k ∈ range (b / 2 + 1),
      ∑ j ∈ range (a / 2 + 1), ballot a j * ballot b k *
          ((g.choose (L + a + k - j) : ℤ) - (g.choose (L + j + k - 1) : ℤ)) =
        ballot b k * (((g + a).choose (L + a + b - k) : ℤ) -
          ((g + a).choose (L + a + k - 1) : ℤ)) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have h := ballot_reflection_sum (G := g) (a := a) (c := L + k) (by omega)
    unfold reflSummand at h
    rw [show L + k + a = L + a + k by ring] at h
    rw [show (g + a).choose (L + a + b - k) = (g + a).choose (L + a + k) by
      rw [← Nat.choose_symm (by omega : L + a + k ≤ g + a)]; congr 1; omega]
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    simp only [Finset.mem_range] at hj
    rw [show L + k + j - 1 = L + j + k - 1 by omega]
    ring
  rw [Finset.sum_congr rfl hInner]
  have h := ballot_reflection_sum (G := g + a) (a := b) (c := L + a) (by omega)
  unfold reflSummand at h
  rw [h, show g + a + b = 2 * (L + a + b) by omega, show L + a + b = L + a + b from rfl,
    catalan_eq_choose_sub (by omega : 1 ≤ L + a + b)]

/-- **The chain-tail identity, once-marked form** (`b = 0`):
`Σ_{j ≤ a/2} M_j(a) (C(g, L + a - j) - C(g, L + j - 1)) = C_{L + a}` for `g = 2L + a`. -/
theorem chainTail_identity_once {g a L : ℕ} (hL : 1 ≤ L) (hg : g = 2 * L + a) :
    ∑ j ∈ range (a / 2 + 1),
        ballot a j * ((g.choose (L + a - j) : ℤ) - (g.choose (L + j - 1) : ℤ)) =
      catalan (L + a) := by
  have h := chainTail_identity (b := 0) hL (by omega : g = 2 * L + a + 0)
  simp only [Nat.zero_div, zero_add, Finset.sum_range_one, ballot_zero, mul_one, add_zero] at h
  exact h

end DraismaVargas.Count.MarkedCountGeneral
