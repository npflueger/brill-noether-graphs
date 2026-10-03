import Utilities.Foundations.ScriptClamping
import Mathlib.Tactic

/-!
# A graph with a handle

`handleGraph G x y m` is `G` together with a path from `x` to `y` through `m + 1` new vertices
`q₀, …, q_m`:

```text
x — q₀ — q₁ — ⋯ — q_m — y
```

The path has `m + 2` edges. The vertex type is `G.V ⊕ Fin (m + 1)`, so divisors and scripts on
`G` and on the handle are the two summands of a divisor or script on the handle graph.

This file is the graph side of the long-handle lemma (`Utilities/Gluing/LongHandle.lean`): the
edge multiplicities, the principal divisor of a script at an old vertex and at a handle vertex,
the genus, connectedness, and the bookkeeping of the chips on the handle (their number and their
moment). Nothing here mentions rank.

**Use `handleInl` and `handleInr`, never `Sum.inl` and `Sum.inr`.** The vertex type
`(handleGraph G x y m).V` is `G.V ⊕ Fin (m + 1)` only after unfolding `handleGraph`, so a
statement written with `Sum.inl` is not type-correct at reducible transparency and `rw` refuses
to work on it. The two wrappers have the right type by declaration. Everything downstream is
stated through them, through `sum_handleGraph` and through `handleGraph_cases`.

Positions on the handle are natural numbers: `handlePoint` sends `0` to `x`, the positions
`1, …, m + 1` to the new vertices, and every larger position to `y`.
-/

namespace Utilities

universe u

open Multiset Finset

variable (G : CFGraph.{u}) (x y : G.V) (m : ℕ)

/-- The edges of the handle, each once: `x — q₀`, `q_m — y`, and `q_i — q_{i+1}`. -/
def handleEdges : Multiset ((G.V ⊕ Fin (m + 1)) × (G.V ⊕ Fin (m + 1))) :=
  (Sum.inl x, Sum.inr 0) ::ₘ (Sum.inr (Fin.last m), Sum.inl y) ::ₘ
    (Finset.univ : Finset (Fin m)).val.map fun i => (Sum.inr i.castSucc, Sum.inr i.succ)

/-- `G` with a path of `m + 2` edges attached from `x` to `y`. -/
def handleGraph : CFGraph.{u} where
  V := G.V ⊕ Fin (m + 1)
  edges := G.edges.map (Prod.map Sum.inl Sum.inl) + handleEdges G x y m
  loopless := by
    intro v hv
    rw [Multiset.mem_add] at hv
    rcases hv with h | h
    · obtain ⟨⟨a, b⟩, hab, heq⟩ := Multiset.mem_map.mp h
      have h1 : Sum.inl a = v := (Prod.mk.inj heq).1
      have h2 : Sum.inl b = v := (Prod.mk.inj heq).2
      have hEq : a = b := Sum.inl.inj (h1.trans h2.symm)
      subst hEq
      exact G.loopless a hab
    · simp only [handleEdges, Multiset.mem_cons, Multiset.mem_map, Finset.mem_val,
        Finset.mem_univ, true_and] at h
      rcases h with h | h | ⟨i, hi⟩
      · have := (Prod.mk.inj h).1.symm.trans (Prod.mk.inj h).2
        cases this
      · have := (Prod.mk.inj h).1.symm.trans (Prod.mk.inj h).2
        cases this
      · have h1 : (Sum.inr i.castSucc : G.V ⊕ Fin (m + 1)) = v := (Prod.mk.inj hi).1
        have h2 : (Sum.inr i.succ : G.V ⊕ Fin (m + 1)) = v := (Prod.mk.inj hi).2
        have hEq : i.castSucc = i.succ := Sum.inr.inj (h1.trans h2.symm)
        have := congrArg Fin.val hEq
        simp at this

variable {G x y m}

/-- An old vertex, as a vertex of the handle graph. -/
def handleInl (a : G.V) : (handleGraph G x y m).V := Sum.inl a

/-- The new vertex `q_i` of the handle. It sits at position `i + 1`. -/
def handleInr (i : Fin (m + 1)) : (handleGraph G x y m).V := Sum.inr i

theorem handleInl_injective :
    Function.Injective (handleInl : G.V → (handleGraph G x y m).V) :=
  fun _ _ h => Sum.inl.inj h

theorem handleInr_injective :
    Function.Injective (handleInr : Fin (m + 1) → (handleGraph G x y m).V) :=
  fun _ _ h => Sum.inr.inj h

theorem handleInl_ne_handleInr (a : G.V) (i : Fin (m + 1)) :
    (handleInl a : (handleGraph G x y m).V) ≠ handleInr i :=
  fun h => by cases h

/-- `handleInl_injective` as a `simp` rewrite. -/
private theorem handleInl_inj {a b : G.V} :
    (handleInl a : (handleGraph G x y m).V) = handleInl b ↔ a = b :=
  handleInl_injective.eq_iff

/-- `handleInr_injective` as a `simp` rewrite. -/
private theorem handleInr_inj {i j : Fin (m + 1)} :
    (handleInr i : (handleGraph G x y m).V) = handleInr j ↔ i = j :=
  handleInr_injective.eq_iff

/-- `handleInl_ne_handleInr`, the other way round. -/
private theorem handleInr_ne_handleInl (i : Fin (m + 1)) (a : G.V) :
    (handleInr i : (handleGraph G x y m).V) ≠ handleInl a :=
  fun h => handleInl_ne_handleInr a i h.symm

/-- Every vertex of the handle graph is an old vertex or a new one. -/
theorem handleGraph_cases (v : (handleGraph G x y m).V) :
    (∃ a : G.V, v = handleInl a) ∨ (∃ i : Fin (m + 1), v = handleInr i) := by
  rcases v with a | i
  · exact Or.inl ⟨a, rfl⟩
  · exact Or.inr ⟨i, rfl⟩

/-- A sum over the vertices of the handle graph splits into the old vertices and the new. -/
theorem sum_handleGraph (F : (handleGraph G x y m).V → ℤ) :
    ∑ v, F v = ∑ a : G.V, F (handleInl a) + ∑ i : Fin (m + 1), F (handleInr i) :=
  Fintype.sum_sum_type F

variable (G x y m)

/-- Position `j` on the handle: `0` is `x`, positions `1, …, m + 1` are the new vertices, and
every larger position is `y`. -/
def handlePoint (j : ℕ) : (handleGraph G x y m).V :=
  if j = 0 then handleInl x
  else if h : j ≤ m + 1 then handleInr ⟨j - 1, by omega⟩
  else handleInl y

@[simp] theorem handlePoint_zero : handlePoint G x y m 0 = handleInl x := by
  rw [handlePoint, if_pos rfl]

theorem handlePoint_succ (i : Fin (m + 1)) :
    handlePoint G x y m (i + 1) = handleInr i := by
  have hi : (i : ℕ) + 1 ≤ m + 1 := i.isLt
  rw [handlePoint, if_neg (Nat.succ_ne_zero _), dif_pos hi]
  rfl

@[simp] theorem handlePoint_last : handlePoint G x y m (m + 2) = handleInl y := by
  rw [handlePoint, if_neg (by omega), dif_neg (by omega)]

/-- Position `1` is the first new vertex. -/
private theorem handlePoint_one : handlePoint G x y m 1 = handleInr 0 :=
  handlePoint_succ G x y m 0

/-- Position `m + 1` is the last new vertex. -/
private theorem handlePoint_succ_last : handlePoint G x y m (m + 1) = handleInr (Fin.last m) :=
  handlePoint_succ G x y m (Fin.last m)

/-- An old vertex sits at position `0` (if it is `x`) or at the positions past the handle (if it
is `y`). -/
private theorem handleInl_eq_handlePoint_iff (b : G.V) (n : ℕ) :
    handleInl b = handlePoint G x y m n ↔ (n = 0 ∧ b = x) ∨ (m + 2 ≤ n ∧ b = y) := by
  unfold handlePoint
  split_ifs with h0 h1
  · simp only [handleInl_inj, h0, true_and]
    constructor
    · exact Or.inl
    · rintro (h | ⟨h, _⟩)
      · exact h
      · omega
  · simp only [handleInl_ne_handleInr, false_iff, not_or, not_and]
    constructor <;> intro h <;> omega
  · simp only [handleInl_inj, h0, false_and, false_or]
    constructor
    · intro h
      exact ⟨by omega, h⟩
    · exact fun h => h.2

/-- The new vertex `q_k` sits at position `k + 1` and nowhere else. -/
private theorem handleInr_eq_handlePoint_iff (k : Fin (m + 1)) (n : ℕ) :
    handleInr k = handlePoint G x y m n ↔ n = k + 1 := by
  have hk := k.isLt
  unfold handlePoint
  split_ifs with h0 h1
  · simp only [handleInr_ne_handleInl, false_iff]
    omega
  · rw [handleInr_inj, Fin.ext_iff]
    simp only
    omega
  · simp only [handleInr_ne_handleInl, false_iff]
    omega

/-- A discrete intermediate value theorem: a property of `ℕ` that differs at `0` and at `k`
changes between some `n < k` and `n + 1`. -/
private theorem exists_step_of_not_iff (P : ℕ → Prop) {k : ℕ} (h : ¬ (P 0 ↔ P k)) :
    ∃ n < k, ¬ (P n ↔ P (n + 1)) := by
  induction k with
  | zero => exact absurd Iff.rfl h
  | succ k ih =>
    by_cases hk : P k ↔ P (k + 1)
    · obtain ⟨n, hn, h'⟩ := ih fun h0 => h (h0.trans hk)
      exact ⟨n, by omega, h'⟩
    · exact ⟨k, by omega, hk⟩

/-! ## Edge multiplicities -/

/-- The edge multiplicity in the handle graph, split into the old edges, the two end edges of the
handle, and its interior edges. -/
private theorem num_edges_handleGraph_eq (v w : (handleGraph G x y m).V) :
    num_edges (handleGraph G x y m) v w =
      Multiset.card (G.edges.filter fun e =>
          ((handleInl e.1, handleInl e.2) : (handleGraph G x y m).V × (handleGraph G x y m).V) =
              (v, w) ∨ (handleInl e.1, handleInl e.2) = (w, v)) +
        ((Finset.univ.filter fun i : Fin m =>
            ((handleInr i.castSucc, handleInr i.succ) :
                (handleGraph G x y m).V × (handleGraph G x y m).V) = (v, w) ∨
              (handleInr i.castSucc, handleInr i.succ) = (w, v)).card +
          (if ((handleInr (Fin.last m), handleInl y) :
                (handleGraph G x y m).V × (handleGraph G x y m).V) = (v, w) ∨
              (handleInr (Fin.last m), handleInl y) = (w, v) then 1 else 0) +
          (if ((handleInl x, handleInr 0) : (handleGraph G x y m).V × (handleGraph G x y m).V) =
              (v, w) ∨ (handleInl x, handleInr 0) = (w, v) then 1 else 0)) := by
  show Multiset.card (Multiset.filter
      (fun e : (G.V ⊕ Fin (m + 1)) × (G.V ⊕ Fin (m + 1)) =>
        e = ((v, w) : (G.V ⊕ Fin (m + 1)) × (G.V ⊕ Fin (m + 1))) ∨
          e = ((w, v) : (G.V ⊕ Fin (m + 1)) × (G.V ⊕ Fin (m + 1))))
      (G.edges.map (Prod.map Sum.inl Sum.inl) + handleEdges G x y m)) = _
  rw [← Multiset.countP_eq_card_filter, Multiset.countP_add, Multiset.countP_map, handleEdges,
    Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_map]
  rfl

/-- Old vertices keep their old edges. -/
theorem num_edges_handleGraph_inl_inl (a b : G.V) :
    num_edges (handleGraph G x y m) (handleInl a) (handleInl b) = num_edges G a b := by
  rw [num_edges_handleGraph_eq]
  simp only [Prod.mk.injEq, handleInl_inj, handleInr_ne_handleInl, and_false, false_and, or_self,
    Finset.filter_false, Finset.card_empty, ↓reduceIte, add_zero]
  unfold num_edges
  apply congrArg Multiset.card
  apply Multiset.filter_congr
  rintro ⟨c, d⟩ _
  simp only [Prod.mk.injEq]

/-- An old vertex meets the handle only at its two ends. -/
theorem num_edges_handleGraph_inl_inr (a : G.V) (i : Fin (m + 1)) :
    num_edges (handleGraph G x y m) (handleInl a) (handleInr i) =
      (if a = x ∧ i = 0 then 1 else 0) + (if a = y ∧ i = Fin.last m then 1 else 0) := by
  rw [num_edges_handleGraph_eq]
  simp only [Prod.mk.injEq, handleInl_inj, handleInr_inj, handleInr_ne_handleInl,
    handleInl_ne_handleInr, and_false, false_and, or_self, or_false, false_or,
    Finset.filter_false, Finset.card_empty, Multiset.filter_false, Multiset.card_zero, zero_add,
    @eq_comm _ x a, @eq_comm _ y a, @eq_comm _ (0 : Fin (m + 1)) i,
    @eq_comm _ (Fin.last m) i, and_comm (a := i = Fin.last m) (b := a = y)]
  rw [add_comm]

/-- Two handle vertices are joined exactly when they are consecutive. -/
theorem num_edges_handleGraph_inr_inr (i j : Fin (m + 1)) :
    num_edges (handleGraph G x y m) (handleInr i) (handleInr j) =
      if (j : ℕ) = i + 1 ∨ (i : ℕ) = j + 1 then 1 else 0 := by
  rw [num_edges_handleGraph_eq]
  simp only [Prod.mk.injEq, handleInr_inj, handleInl_ne_handleInr, and_false, false_and, or_self,
    ↓reduceIte, Multiset.filter_false, Multiset.card_zero, zero_add, add_zero]
  have hi := i.isLt
  have hj := j.isLt
  split_ifs with h
  · rcases h with h | h
    · rw [Finset.card_eq_one]
      refine ⟨⟨i, by omega⟩, ?_⟩
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff,
        Fin.val_castSucc, Fin.val_succ]
      omega
    · rw [Finset.card_eq_one]
      refine ⟨⟨j, by omega⟩, ?_⟩
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff,
        Fin.val_castSucc, Fin.val_succ]
      omega
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k _
    simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
    omega

/-- The new vertex `q_i` is joined to positions `i` and `i + 2`, once each (twice to `x = y` when
the handle has a single new vertex). -/
private theorem num_edges_handleGraph_handleInr (i : Fin (m + 1)) (u : (handleGraph G x y m).V) :
    num_edges (handleGraph G x y m) (handleInr i) u =
      (if u = handlePoint G x y m i then 1 else 0) +
        (if u = handlePoint G x y m (i + 2) then 1 else 0) := by
  have hi := i.isLt
  rcases handleGraph_cases u with ⟨b, rfl⟩ | ⟨k, rfl⟩
  · rw [num_edges_symmetric, num_edges_handleGraph_inl_inr]
    simp only [handleInl_eq_handlePoint_iff, Fin.ext_iff, Fin.val_zero, Fin.val_last]
    congr 1
    · refine if_congr ?_ rfl rfl
      constructor
      · rintro ⟨h1, h2⟩
        exact Or.inl ⟨h2, h1⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, _⟩)
        · exact ⟨h2, h1⟩
        · omega
    · refine if_congr ?_ rfl rfl
      constructor
      · rintro ⟨h1, h2⟩
        exact Or.inr ⟨by omega, h1⟩
      · rintro (⟨h1, _⟩ | ⟨h1, h2⟩)
        · omega
        · exact ⟨h2, by omega⟩
  · rw [num_edges_handleGraph_inr_inr]
    simp only [handleInr_eq_handlePoint_iff]
    split_ifs <;> omega

/-- Consecutive positions on the handle are joined by an edge. -/
private theorem num_edges_handlePoint_succ_pos {n : ℕ} (hn : n ≤ m) :
    0 < num_edges (handleGraph G x y m) (handlePoint G x y m (n + 1)) (handlePoint G x y m n) := by
  have hp : handlePoint G x y m (n + 1) = handleInr ⟨n, by omega⟩ :=
    handlePoint_succ G x y m ⟨n, by omega⟩
  rw [hp, num_edges_handleGraph_handleInr, if_pos rfl]
  omega

/-! ## Principal divisors -/

/-- At an old vertex, the principal divisor of a script on the handle graph is the principal
divisor of its restriction to `G`, plus the flow along the first handle edge at `x` and along the
last handle edge at `y`. -/
theorem prin_handleGraph_inl (σ : firing_script (handleGraph G x y m)) (a : G.V) :
    prin (handleGraph G x y m) σ (handleInl a) =
      prin G (fun b => σ (handleInl b)) a +
        (if a = x then σ (handlePoint G x y m 1) - σ (handlePoint G x y m 0) else 0) +
        (if a = y then σ (handlePoint G x y m (m + 1)) - σ (handlePoint G x y m (m + 2))
          else 0) := by
  rw [prin_apply, sum_handleGraph, prin_apply]
  simp only [num_edges_handleGraph_inl_inl, num_edges_handleGraph_inl_inr, Nat.cast_add,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_add, Finset.sum_add_distrib, ite_and, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, handlePoint_zero, handlePoint_one, handlePoint_succ_last,
    handlePoint_last]
  rw [add_assoc]
  split_ifs <;> subst_vars <;> rfl

/-- At a handle vertex, the principal divisor is the second difference of the script along the
handle: for `1 ≤ j ≤ m + 1`, the value at position `j` is
`(σ (j - 1) - σ j) + (σ (j + 1) - σ j)`. It is stated at position `j + 1` to avoid subtraction. -/
theorem prin_handleGraph_point (σ : firing_script (handleGraph G x y m)) {j : ℕ}
    (hj : j ≤ m) :
    prin (handleGraph G x y m) σ (handlePoint G x y m (j + 1)) =
      (σ (handlePoint G x y m j) - σ (handlePoint G x y m (j + 1))) +
        (σ (handlePoint G x y m (j + 2)) - σ (handlePoint G x y m (j + 1))) := by
  have hj' : j < m + 1 := by omega
  have hp : handlePoint G x y m (j + 1) = handleInr ⟨j, hj'⟩ := handlePoint_succ G x y m ⟨j, hj'⟩
  rw [hp, prin_apply]
  simp only [num_edges_handleGraph_handleInr, Nat.cast_add, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-! ## Genus and connectedness -/

/-- A handle adds one to the genus. -/
theorem genus_handleGraph : genus (handleGraph G x y m) = genus G + 1 := by
  have hE : Multiset.card (handleGraph G x y m).edges = Multiset.card G.edges + (m + 2) := by
    show Multiset.card (G.edges.map (Prod.map Sum.inl Sum.inl) + handleEdges G x y m :
      Multiset ((G.V ⊕ Fin (m + 1)) × (G.V ⊕ Fin (m + 1)))) = _
    rw [Multiset.card_add, Multiset.card_map, handleEdges, Multiset.card_cons, Multiset.card_cons,
      Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
  have hV : Fintype.card (handleGraph G x y m).V = Fintype.card G.V + (m + 1) := by
    show Fintype.card (G.V ⊕ Fin (m + 1)) = _
    rw [Fintype.card_sum, Fintype.card_fin]
  unfold genus
  rw [hE, hV]
  push_cast
  ring

/-- A handle on a connected graph gives a connected graph. -/
theorem graph_connected_handleGraph (hG : graph_connected G) :
    graph_connected (handleGraph G x y m) := by
  intro S ⟨v, w, hv, hw⟩
  by_cases hsep : ∃ a b : G.V, handleInl a ∈ S ∧ handleInl b ∉ S
  · -- `S` separates two old vertices: use an old edge across.
    obtain ⟨a, b, ha, hb⟩ := hsep
    obtain ⟨c, hc, d, hd, hcd⟩ := hG (Finset.univ.filter fun a : G.V => handleInl a ∈ S)
      ⟨a, b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩,
        fun h => hb (Finset.mem_filter.mp h).2⟩
    refine ⟨handleInl c, (Finset.mem_filter.mp hc).2, handleInl d,
      fun h => hd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩), ?_⟩
    rwa [num_edges_handleGraph_inl_inl]
  · -- All old vertices lie on the side of `x`; some new vertex lies on the other side.
    simp only [not_exists, not_and, not_not] at hsep
    have hold : ∀ a : G.V, handleInl a ∈ S ↔ handleInl x ∈ S :=
      fun a => ⟨fun h => hsep a x h, fun h => hsep x a h⟩
    obtain ⟨i, hi⟩ : ∃ i : Fin (m + 1), ¬ (handleInl x ∈ S ↔ handleInr i ∈ S) := by
      by_cases hx : handleInl x ∈ S
      · rcases handleGraph_cases w with ⟨b, rfl⟩ | ⟨i, rfl⟩
        · exact absurd ((hold b).mpr hx) hw
        · exact ⟨i, fun h => hw (h.mp hx)⟩
      · rcases handleGraph_cases v with ⟨a, rfl⟩ | ⟨i, rfl⟩
        · exact absurd ((hold a).mp hv) hx
        · exact ⟨i, fun h => hx (h.mpr hv)⟩
    have hP : ¬ (handlePoint G x y m 0 ∈ S ↔ handlePoint G x y m (i + 1) ∈ S) := by
      rwa [handlePoint_zero, handlePoint_succ]
    obtain ⟨n, hn, hstep⟩ := exists_step_of_not_iff (fun n => handlePoint G x y m n ∈ S) hP
    have hnm : n ≤ m := by omega
    have hedge := num_edges_handlePoint_succ_pos G x y m hnm
    by_cases hin : handlePoint G x y m n ∈ S
    · refine ⟨handlePoint G x y m n, hin, handlePoint G x y m (n + 1),
        fun h => hstep ⟨fun _ => h, fun _ => hin⟩, ?_⟩
      rw [num_edges_symmetric]
      exact hedge
    · exact ⟨handlePoint G x y m (n + 1), by tauto, handlePoint G x y m n, hin, hedge⟩

/-! ## Divisors: the old part and the chips on the handle -/

variable {G x y m}

/-- The part of a divisor on the old vertices. -/
def handleRestrict (D : CFDiv (handleGraph G x y m)) : CFDiv G :=
  fun a => D (handleInl a)

/-- The number of chips on the new vertices of the handle. -/
def handleInterior (D : CFDiv (handleGraph G x y m)) : ℤ :=
  ∑ i : Fin (m + 1), D (handleInr i)

/-- The moment of the chips on the handle: a chip at `handleInr i` has position `i + 1`. -/
def handleMoment (D : CFDiv (handleGraph G x y m)) : ℤ :=
  ∑ i : Fin (m + 1), ((i : ℤ) + 1) * D (handleInr i)

@[simp] theorem handleRestrict_apply (D : CFDiv (handleGraph G x y m)) (a : G.V) :
    handleRestrict D a = D (handleInl a) := rfl

theorem handleRestrict_add (D D' : CFDiv (handleGraph G x y m)) :
    handleRestrict (D + D') = handleRestrict D + handleRestrict D' := rfl

theorem handleRestrict_sub (D D' : CFDiv (handleGraph G x y m)) :
    handleRestrict (D - D') = handleRestrict D - handleRestrict D' := rfl

/-- The degree splits into the old part and the chips on the handle. -/
theorem deg_handleGraph (D : CFDiv (handleGraph G x y m)) :
    deg D = deg (handleRestrict D) + handleInterior D :=
  sum_handleGraph D

/-- A chip at an old vertex, evaluated at an old vertex. -/
theorem one_chip_handleInl_apply_handleInl (w a : G.V) :
    one_chip (G := handleGraph G x y m) (handleInl w) (handleInl a) = one_chip w a := by
  simp only [one_chip, handleInl_inj]

/-- A chip at an old vertex puts nothing on the handle. -/
theorem one_chip_handleInl_apply_handleInr (w : G.V) (i : Fin (m + 1)) :
    one_chip (G := handleGraph G x y m) (handleInl w) (handleInr i) = 0 :=
  one_chip_apply_other' _ _ (handleInr_ne_handleInl i w)

/-- A chip on the handle puts nothing on the old vertices. -/
theorem one_chip_handleInr_apply_handleInl (i : Fin (m + 1)) (a : G.V) :
    one_chip (G := handleGraph G x y m) (handleInr i) (handleInl a) = 0 :=
  one_chip_apply_other' _ _ (handleInl_ne_handleInr a i)

/-- A chip on the handle, evaluated on the handle. -/
theorem one_chip_handleInr_apply_handleInr (i j : Fin (m + 1)) :
    one_chip (G := handleGraph G x y m) (handleInr i) (handleInr j) =
      if j = i then 1 else 0 := by
  simp only [one_chip, handleInr_inj]

/-- An effective divisor has an effective old part. -/
theorem effective_handleRestrict {D : CFDiv (handleGraph G x y m)} (hD : effective D) :
    effective (handleRestrict D) :=
  fun a => hD (handleInl a)

/-- An effective divisor has a nonnegative number of chips on the handle. -/
theorem handleInterior_nonneg {D : CFDiv (handleGraph G x y m)} (hD : effective D) :
    0 ≤ handleInterior D :=
  Finset.sum_nonneg fun i _ => hD (handleInr i)

end Utilities
