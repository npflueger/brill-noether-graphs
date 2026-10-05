module

public import Utilities.Gluing.HandleGraph
public import Utilities.Foundations.RankOne

@[expose] public section

/-!
# Restricting a pencil from a long handle

The restriction step of the long-handle lemma (`Utilities/Gluing/LongHandle.lean`; step (b) of
the prose proof in `Research/long-handle-lemma.md`). Let `E` be an effective divisor on
`handleGraph G x y m` of rank at least one, with at most one chip on the new vertices of the
handle, and let the handle be long: `2 * (deg E * (|V(G)| - 1)) < m + 2`. Then the old part of
`E`, with the one handle chip pushed to its nearer end, has rank at least one on `G`.

The argument. Take a test vertex `w` of `G` and a script `f` on the handle graph that makes
`E - w` effective. Along the handle put `s j = f (position j) - f (position (j - 1))` for
`1 ≤ j ≤ m + 2`. Effectivity at a handle vertex says `s (j + 1) ≥ s j - E (position j)`, so the
slopes are nondecreasing except for a drop of one after the chip. Their sum is `f y - f x`, which
is bounded by `deg E * (|V(G)| - 1)` in absolute value: `f` changes by at most `deg E` along
every edge (`Utilities.abs_script_sub_le_deg_of_effective_sub_add_prin`) and `G` is connected.
On a long handle this forces `s 1 ≤ 0 ≤ s (m + 2)`, up to the one unit the chip allows on its own
side. By `prin_handleGraph_inl`, the restricted script then works on `G`.

Headlines:

* `sub_le_mul_card_sub_one_of_edge_bound`: a function on a connected graph that changes by at
  most `c` along every edge changes by at most `c * (|V| - 1)` overall;
* `rank_handleRestrict_ge_one_of_interior_zero`: no chip on the handle;
* `rank_handleRestrict_ge_one_of_single_chip`: one chip on the handle.

Internally the slopes are indexed from zero: `t i = f (position (i + 1)) - f (position i)` for
`i ≤ m + 1`, so `t 0 = s 1` and `t (m + 1) = s (m + 2)`. The integer facts about such a sequence
are `handleSlope_head_le` and `handleSlope_tail_ge`; the second is the first applied to the
reversed, negated sequence.
-/

namespace Utilities

universe u

open Finset

/-! ## Integer facts about a sequence of slopes -/

/-- Slopes that never drop except by one after index `b` stay at least the first slope before `b`
and at least one less than it everywhere. -/
theorem handleSlope_lower (t : ℕ → ℤ) (n b : ℕ)
    (hstep : ∀ j, j + 1 < n + 1 → t j - (if j + 1 = b then 1 else 0) ≤ t (j + 1)) :
    ∀ i, i < n + 1 → (i < b → t 0 ≤ t i) ∧ t 0 - 1 ≤ t i := by
  intro i
  induction i with
  | zero => intro _; exact ⟨fun _ => le_rfl, by omega⟩
  | succ i ih =>
    intro hi
    have h := hstep i hi
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    constructor
    · intro hib
      have h1 := ih1 (by omega)
      rw [ite_eq_right (by omega)] at h
      omega
    · by_cases hb : i + 1 = b
      · rw [ite_eq_left hb] at h
        have h1 := ih1 (by omega)
        omega
      · rw [ite_eq_right hb] at h
        omega

/-- **The first slope.** If `n + 1` slopes that drop by at most one, after index `b`, have sum at
most `B` with `2 * B < n + 1`, then the first slope is at most one, and at most zero when
`n + 1 ≤ 2 * b`. -/
theorem handleSlope_head_le (t : ℕ → ℤ) (n b : ℕ) (B : ℤ) (hB : 2 * B < (n : ℤ) + 1)
    (hsum : ∑ i ∈ range (n + 1), t i ≤ B)
    (hstep : ∀ j, j + 1 < n + 1 → t j - (if j + 1 = b then 1 else 0) ≤ t (j + 1)) :
    t 0 ≤ 1 ∧ (n + 1 ≤ 2 * b → t 0 ≤ 0) := by
  have hlow := handleSlope_lower t n b hstep
  constructor
  · -- Otherwise every slope is at least one, and the sum is at least `n + 1`.
    by_contra h0
    have h0 := not_le.mp h0
    have hle : ∑ _i ∈ range (n + 1), (1 : ℤ) ≤ ∑ i ∈ range (n + 1), t i :=
      Finset.sum_le_sum fun i hi => by
        have := (hlow i (Finset.mem_range.mp hi)).2
        omega
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hle
    push_cast at hle
    omega
  · -- Otherwise the slopes before `b` are at least one and the rest are nonnegative, so the
    -- sum is at least `min b (n + 1)`, which is at least `(n + 1) / 2`.
    intro hb
    by_contra h0
    have h0 := not_le.mp h0
    have hpart : ∀ p, p ≤ n + 1 →
        (p ≤ b → (p : ℤ) ≤ ∑ i ∈ range p, t i) ∧ (b ≤ p → (b : ℤ) ≤ ∑ i ∈ range p, t i) := by
      intro p
      induction p with
      | zero => intro _; simp
      | succ p ih =>
        intro hp
        obtain ⟨ih1, ih2⟩ := ih (by omega)
        obtain ⟨hl1, hl2⟩ := hlow p (by omega)
        rw [Finset.sum_range_succ]
        push_cast
        constructor
        · intro hpb
          have := ih1 (by omega)
          have := hl1 (by omega)
          omega
        · intro hbp
          by_cases hpb : b ≤ p
          · have := ih2 hpb
            omega
          · have := ih1 (by omega)
            have := hl1 (by omega)
            have : b = p + 1 := by omega
            subst this
            push_cast
            omega
    by_cases hbn : b ≤ n + 1
    · have := (hpart (n + 1) le_rfl).2 hbn
      omega
    · have := (hpart (n + 1) le_rfl).1 (by omega)
      push_cast at this
      omega

/-- **The last slope.** Under the same hypotheses, with the sum at least `-B`, the last slope is
at least minus one, and at least zero when `2 * b ≤ n + 1`. This is `handleSlope_head_le` for the
reversed, negated slopes, whose drop sits after index `n + 1 - b`. -/
theorem handleSlope_tail_ge (t : ℕ → ℤ) (n b : ℕ) (B : ℤ) (hB : 2 * B < (n : ℤ) + 1)
    (hsum : -B ≤ ∑ i ∈ range (n + 1), t i)
    (hstep : ∀ j, j + 1 < n + 1 → t j - (if j + 1 = b then 1 else 0) ≤ t (j + 1)) :
    -1 ≤ t n ∧ (2 * b ≤ n + 1 → 0 ≤ t n) := by
  set t' : ℕ → ℤ := fun i => -t (n - i) with ht'
  have hsum' : ∑ i ∈ range (n + 1), t' i ≤ B := by
    have hr := Finset.sum_range_reflect t (n + 1)
    rw [Nat.add_sub_cancel] at hr
    have : ∑ i ∈ range (n + 1), t' i = -∑ i ∈ range (n + 1), t i := by
      rw [← hr, ← Finset.sum_neg_distrib]
    rw [this]
    omega
  have hstep' : ∀ j, j + 1 < n + 1 →
      t' j - (if j + 1 = n + 1 - b then 1 else 0) ≤ t' (j + 1) := by
    intro j hj
    have h := hstep (n - j - 1) (by omega)
    have he : n - j - 1 + 1 = n - j := by omega
    rw [he] at h
    have he2 : n - (j + 1) = n - j - 1 := by omega
    simp only [ht', he2]
    by_cases hc : n - j = b
    · rw [ite_eq_left hc] at h
      rw [ite_eq_left (by omega)]
      omega
    · rw [ite_eq_right hc] at h
      rw [ite_eq_right (by omega)]
      omega
  obtain ⟨h1, h2⟩ := handleSlope_head_le t' n (n + 1 - b) B hB hsum' hstep'
  simp only [ht', Nat.sub_zero] at h1 h2
  refine ⟨by omega, fun hb => ?_⟩
  have := h2 (by omega)
  omega

/-! ## Winnability through a script -/

/-- An effective `D + prin H g` makes `D` winnable. -/
theorem winnable_of_effective_add_prin_script {H : CFGraph} {D : CFDiv H} (g : firing_script H)
    (h : effective (D + prin H g)) : winnable H D :=
  ⟨D + prin H g, mem_Eff.mpr h, (principal_iff_eq_prin H _).mpr ⟨g, add_sub_cancel_left D _⟩⟩

/-- A winnable divisor becomes effective after adding the principal divisor of some script. -/
theorem exists_script_effective_add_prin_of_winnable {H : CFGraph} {D : CFDiv H}
    (h : winnable H D) : ∃ g : firing_script H, effective (D + prin H g) := by
  obtain ⟨D', hD', hlin⟩ := h
  obtain ⟨g, hg⟩ := (principal_iff_eq_prin H _).mp hlin
  refine ⟨g, ?_⟩
  rw [← hg, add_sub_cancel D D']
  exact mem_Eff.mp hD'

/-! ## The oscillation bound -/

variable {G : CFGraph.{u}} {x y : G.V} {m : ℕ}

/-- **Oscillation on a connected graph.** A function that changes by at most `c` along every
edge changes by at most `c * (|V| - 1)` between any two vertices. -/
theorem sub_le_mul_card_sub_one_of_edge_bound (hG : graph_connected G) (g : G.V → ℤ) (c : ℤ)
    (hc : 0 ≤ c) (hEdge : ∀ a b : G.V, 0 < num_edges G a b → g a - g b ≤ c) (a b : G.V) :
    g a - g b ≤ c * ((Fintype.card G.V : ℤ) - 1) := by
  -- Proof idea: the sets `A_j = {v | g a - j * c ≤ g v}` contain `a`; while `A_j` is not
  -- everything, connectedness gives an edge leaving it, and its far end lies in `A_{j+1}`,
  -- so `j + 1 ≤ |A_j|` or `A_j` is everything.  At `j = |V| - 1` it is everything.
  classical
  let A : ℕ → Finset G.V := fun j => Finset.univ.filter fun v => g a - (j : ℤ) * c ≤ g v
  have hmem : ∀ j v, v ∈ A j ↔ g a - (j : ℤ) * c ≤ g v := fun j v => by simp [A]
  have hmono : ∀ j, A j ⊆ A (j + 1) := by
    intro j v hv
    rw [hmem] at hv ⊢
    push_cast
    nlinarith
  have hgrow : ∀ j, A j = Finset.univ ∨ j + 1 ≤ (A j).card := by
    intro j
    induction j with
    | zero =>
      right
      have : a ∈ A 0 := (hmem 0 a).mpr (by simp)
      simpa using Finset.card_pos.mpr ⟨a, this⟩
    | succ j ih =>
      by_cases hU : A (j + 1) = Finset.univ
      · exact Or.inl hU
      right
      have hUj : A j ≠ Finset.univ := by
        intro h
        apply hU
        exact Finset.eq_univ_of_forall fun v => hmono j (h ▸ Finset.mem_univ v)
      have hcard := ih.resolve_left hUj
      obtain ⟨w₀, hw₀⟩ : ∃ w₀, w₀ ∉ A j := by
        by_contra h
        push Not at h
        exact hUj (Finset.eq_univ_of_forall h)
      obtain ⟨u, hu, v, hv, huv⟩ :=
        hG (A j) ⟨a, w₀, (hmem j a).mpr (by nlinarith), hw₀⟩
      have hvA : v ∈ A (j + 1) := by
        rw [hmem] at hu ⊢
        have := hEdge u v huv
        push_cast
        linarith
      have hss : A j ⊂ A (j + 1) :=
        (Finset.ssubset_iff_of_subset (hmono j)).mpr ⟨v, hvA, hv⟩
      have := Finset.card_lt_card hss
      omega
  have hpos : 0 < Fintype.card G.V := Fintype.card_pos
  have hall : A (Fintype.card G.V - 1) = Finset.univ := by
    rcases hgrow (Fintype.card G.V - 1) with h | h
    · exact h
    · apply Finset.eq_univ_of_card
      have := Finset.card_le_univ (A (Fintype.card G.V - 1))
      omega
  have hb : b ∈ A (Fintype.card G.V - 1) := hall ▸ Finset.mem_univ b
  rw [hmem] at hb
  have hcast : ((Fintype.card G.V - 1 : ℕ) : ℤ) = (Fintype.card G.V : ℤ) - 1 := by
    push_cast [Nat.one_le_iff_ne_zero.mpr hpos.ne']
    ring
  rw [hcast] at hb
  linarith

/-- The two ends of the handle have script values within `deg E * (|V(G)| - 1)`. -/
theorem abs_script_handle_ends_le (hG : graph_connected G)
    {E : CFDiv (handleGraph G x y m)} {w : G.V} {f : firing_script (handleGraph G x y m)}
    (hE : effective E)
    (hWin : effective (E - one_chip (handleInl w) + prin (handleGraph G x y m) f)) :
    |f (handleInl x) - f (handleInl y)| ≤ deg E * ((Fintype.card G.V : ℤ) - 1) := by
  -- `abs_script_sub_le_deg_of_effective_sub_add_prin` on the handle graph, at the edges
  -- `handleInl a — handleInl b` (`num_edges_handleGraph_inl_inl`), then the oscillation lemma
  -- applied to `fun a => f (handleInl a)` in both directions.
  have hdeg : 0 ≤ deg E := Finset.sum_nonneg fun v _ => hE v
  have hEdge : ∀ a b : G.V, 0 < num_edges G a b →
      |f (handleInl a) - f (handleInl b)| ≤ deg E := by
    intro a b hab
    have hab' : 0 < num_edges (handleGraph G x y m) (handleInl a) (handleInl b) := by
      rw [num_edges_handleGraph_inl_inl]
      exact hab
    exact abs_script_sub_le_deg_of_effective_sub_add_prin hE (eff_one_chip _) hWin hab'
  have h1 := sub_le_mul_card_sub_one_of_edge_bound hG (fun a => f (handleInl a)) (deg E) hdeg
    (fun a b hab => (abs_le.mp (hEdge a b hab)).2) x y
  have h2 := sub_le_mul_card_sub_one_of_edge_bound hG (fun a => f (handleInl a)) (deg E) hdeg
    (fun a b hab => (abs_le.mp (hEdge a b hab)).2) y x
  exact abs_sub_le_iff.mpr ⟨h1, h2⟩

/-! ## The slopes at the two ends of a long handle -/

/-- **End slopes.** If `E` has at most one chip on the handle, at position `b`, and a script `f`
makes `E - w` effective, then on a long handle the first slope `s 1` is at most one (at most zero
when `m + 2 ≤ 2 * b`) and the last slope `s (m + 2)` is at least minus one (at least zero when
`2 * b ≤ m + 2`). With no chip on the handle, any `b` may be used. -/
theorem handle_end_slopes (hG : graph_connected G)
    {E : CFDiv (handleGraph G x y m)} (hE : effective E)
    (hLong : 2 * (deg E * ((Fintype.card G.V : ℤ) - 1)) < (m : ℤ) + 2)
    (b : ℕ) (hInt : ∀ i : Fin (m + 1), E (handleInr i) ≤ if (i : ℕ) + 1 = b then 1 else 0)
    {w : G.V} {f : firing_script (handleGraph G x y m)}
    (hWin : effective (E - one_chip (handleInl w) + prin (handleGraph G x y m) f)) :
    (f (handlePoint G x y m 1) - f (handlePoint G x y m 0) ≤ 1 ∧
      (m + 2 ≤ 2 * b → f (handlePoint G x y m 1) - f (handlePoint G x y m 0) ≤ 0)) ∧
    (-1 ≤ f (handlePoint G x y m (m + 2)) - f (handlePoint G x y m (m + 1)) ∧
      (2 * b ≤ m + 2 →
        0 ≤ f (handlePoint G x y m (m + 2)) - f (handlePoint G x y m (m + 1)))) := by
  set B := deg E * ((Fintype.card G.V : ℤ) - 1) with hBdef
  set t : ℕ → ℤ := fun i => f (handlePoint G x y m (i + 1)) - f (handlePoint G x y m i) with ht
  -- Effectivity at the handle vertex at position `j + 1`.
  have hstep : ∀ j, j + 1 < (m + 1) + 1 → t j - (if j + 1 = b then 1 else 0) ≤ t (j + 1) := by
    intro j hj
    have hjm : j < m + 1 := by omega
    have hP : handlePoint G x y m (j + 1) = handleInr ⟨j, hjm⟩ :=
      handlePoint_succ G x y m ⟨j, hjm⟩
    have hEj : E (handlePoint G x y m (j + 1)) ≤ if j + 1 = b then 1 else 0 := by
      rw [hP]
      exact hInt ⟨j, hjm⟩
    have hOj : one_chip (handleInl w) (handlePoint G x y m (j + 1)) = 0 := by
      rw [hP]
      exact one_chip_handleInl_apply_handleInr w ⟨j, hjm⟩
    have h0 := hWin (handlePoint G x y m (j + 1))
    rw [Pi.add_apply, Pi.sub_apply, prin_handleGraph_point G x y m f (by omega : j ≤ m),
      hOj] at h0
    show f (handlePoint G x y m (j + 1)) - f (handlePoint G x y m j) -
        (if j + 1 = b then 1 else 0) ≤
      f (handlePoint G x y m (j + 2)) - f (handlePoint G x y m (j + 1))
    linarith
  -- The slopes telescope to `f y - f x`.
  have hsum : ∑ i ∈ range ((m + 1) + 1), t i = f (handleInl y) - f (handleInl x) := by
    rw [Finset.sum_range_sub (fun i => f (handlePoint G x y m i))]
    rw [show m + 1 + 1 = m + 2 from rfl, handlePoint_last, handlePoint_zero]
  have hends := abs_le.mp (abs_script_handle_ends_le hG hE hWin)
  have hB : 2 * B < ((m + 1 : ℕ) : ℤ) + 1 := by push_cast; linarith
  have hhead := handleSlope_head_le t (m + 1) b B hB (by rw [hsum]; linarith) hstep
  have htail := handleSlope_tail_ge t (m + 1) b B hB (by rw [hsum]; linarith) hstep
  exact ⟨hhead, htail⟩

/-! ## Restriction to the old graph -/

/-- **Restriction of a winning script.** If a script `f` makes `E - w` effective on the handle
graph and `D` dominates the old part of `E` corrected by the two end slopes, then the restriction
of `f` makes `D - w` effective on `G`. The two corrections may land on the same vertex. -/
theorem effective_sub_one_chip_add_prin_restrict
    {E : CFDiv (handleGraph G x y m)} {w : G.V} {f : firing_script (handleGraph G x y m)}
    (hWin : effective (E - one_chip (handleInl w) + prin (handleGraph G x y m) f))
    (D : CFDiv G)
    (hD : ∀ a : G.V, E (handleInl a) +
        (if a = x then f (handlePoint G x y m 1) - f (handlePoint G x y m 0) else 0) +
        (if a = y then f (handlePoint G x y m (m + 1)) - f (handlePoint G x y m (m + 2))
          else 0) ≤ D a) :
    effective (D - one_chip w + prin G (fun a => f (handleInl a))) := by
  intro a
  have h := hWin (handleInl a)
  rw [Pi.add_apply, Pi.sub_apply, prin_handleGraph_inl G x y m f a,
    one_chip_handleInl_apply_handleInl] at h
  have := hD a
  rw [Pi.add_apply, Pi.sub_apply]
  linarith

/-! ## The two restriction theorems -/

/-- **Restriction with no chip on the handle.** -/
theorem rank_handleRestrict_ge_one_of_interior_zero (hG : graph_connected G)
    {E : CFDiv (handleGraph G x y m)} (hE : effective E)
    (hLong : 2 * (deg E * ((Fintype.card G.V : ℤ) - 1)) < (m : ℤ) + 2)
    (hRank : rank (handleGraph G x y m) E ≥ 1)
    (hInt : ∀ i : Fin (m + 1), E (handleInr i) = 0) :
    rank G (handleRestrict E) ≥ 1 := by
  rw [rank_ge_one_iff_winnable_sub_one_chip] at hRank ⊢
  intro w
  obtain ⟨f, hf⟩ := exists_script_effective_add_prin_of_winnable (hRank (handleInl w))
  have hInt' : ∀ b : ℕ, ∀ i : Fin (m + 1),
      E (handleInr i) ≤ if (i : ℕ) + 1 = b then 1 else 0 := by
    intro b i
    rw [hInt i]
    split_ifs <;> norm_num
  -- With no chip, take the drop past the far end for `s 1` and before the near end for `s k`.
  have h1 := (handle_end_slopes hG hE hLong (m + 2) (hInt' _) hf).1.2 (by omega)
  have h2 := (handle_end_slopes hG hE hLong 0 (hInt' _) hf).2.2 (by omega)
  apply winnable_of_effective_add_prin_script (fun a => f (handleInl a))
  apply effective_sub_one_chip_add_prin_restrict hf
  intro a
  rw [handleRestrict_apply]
  split_ifs <;> linarith

/-- **Restriction with one chip on the handle.** The chip is at `handleInr i₀`, that is, at
position `i₀ + 1` of the `m + 2` steps from `x` to `y`. Pushed to its nearer end it keeps rank at
least one; at the exact middle it can be dropped. -/
theorem rank_handleRestrict_ge_one_of_single_chip (hG : graph_connected G)
    {E : CFDiv (handleGraph G x y m)} (hE : effective E)
    (hLong : 2 * (deg E * ((Fintype.card G.V : ℤ) - 1)) < (m : ℤ) + 2)
    (hRank : rank (handleGraph G x y m) E ≥ 1)
    (i₀ : Fin (m + 1)) (hOne : E (handleInr i₀) = 1)
    (hOther : ∀ i : Fin (m + 1), i ≠ i₀ → E (handleInr i) = 0) :
    (2 * ((i₀ : ℕ) + 1) ≤ m + 2 → rank G (handleRestrict E + one_chip x) ≥ 1) ∧
    (m + 2 ≤ 2 * ((i₀ : ℕ) + 1) → rank G (handleRestrict E + one_chip y) ≥ 1) ∧
    (2 * ((i₀ : ℕ) + 1) = m + 2 → rank G (handleRestrict E) ≥ 1) := by
  rw [rank_ge_one_iff_winnable_sub_one_chip] at hRank
  have hInt : ∀ i : Fin (m + 1),
      E (handleInr i) ≤ if (i : ℕ) + 1 = (i₀ : ℕ) + 1 then 1 else 0 := by
    intro i
    by_cases hi : i = i₀
    · subst hi
      rw [hOne, ite_eq_left rfl]
    · rw [hOther i hi, ite_eq_right (fun h => hi (Fin.ext (by omega)))]
  refine ⟨fun hb => ?_, fun hb => ?_, fun hb => ?_⟩
  · -- The chip is in the first half: add a chip at `x`.
    rw [rank_ge_one_iff_winnable_sub_one_chip]
    intro w
    obtain ⟨f, hf⟩ := exists_script_effective_add_prin_of_winnable (hRank (handleInl w))
    have hs := handle_end_slopes hG hE hLong ((i₀ : ℕ) + 1) hInt hf
    have h1 := hs.1.1
    have h2 := hs.2.2 hb
    apply winnable_of_effective_add_prin_script (fun a => f (handleInl a))
    apply effective_sub_one_chip_add_prin_restrict hf
    intro a
    rw [Pi.add_apply, handleRestrict_apply]
    simp only [one_chip]
    split_ifs <;> linarith
  · -- The chip is in the second half: add a chip at `y`.
    rw [rank_ge_one_iff_winnable_sub_one_chip]
    intro w
    obtain ⟨f, hf⟩ := exists_script_effective_add_prin_of_winnable (hRank (handleInl w))
    have hs := handle_end_slopes hG hE hLong ((i₀ : ℕ) + 1) hInt hf
    have h1 := hs.1.2 hb
    have h2 := hs.2.1
    apply winnable_of_effective_add_prin_script (fun a => f (handleInl a))
    apply effective_sub_one_chip_add_prin_restrict hf
    intro a
    rw [Pi.add_apply, handleRestrict_apply]
    simp only [one_chip]
    split_ifs <;> linarith
  · -- The chip is at the midpoint: drop it.
    rw [rank_ge_one_iff_winnable_sub_one_chip]
    intro w
    obtain ⟨f, hf⟩ := exists_script_effective_add_prin_of_winnable (hRank (handleInl w))
    have hs := handle_end_slopes hG hE hLong ((i₀ : ℕ) + 1) hInt hf
    have h1 := hs.1.2 (by omega)
    have h2 := hs.2.2 (by omega)
    apply winnable_of_effective_add_prin_script (fun a => f (handleInl a))
    apply effective_sub_one_chip_add_prin_restrict hf
    intro a
    rw [handleRestrict_apply]
    split_ifs <;> linarith

end Utilities
