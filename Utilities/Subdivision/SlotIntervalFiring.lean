import Utilities.Gonality.LegalFiringChain
import Utilities.Gonality.GonalityTransport
import Utilities.Subdivision.SubdivisionSeparator

/-!
# Slot points, interval firing and confinement

A slot of a unit presentation becomes a path of length `N` after subdivision.
Only `0 < N` is needed here; parity and genus play no role.

* `slotPoint g t` is the vertex at offset `t` from the tail of slot `g`.
  Offsets zero and `N` are its core endpoints.
* `vertex_cases` separates core vertices from strict interior slot points.
* `outdeg_slotPoint` counts the two possible neighbours outside a firing set.
* `interval_firing` fires an interior interval with chips at both ends, or a
  double chip when the interval is a singleton.
* `sum_interior_le_one_of_qReduced` (and `sum_interior_le_one_of_qReduced_core`)
  bounds the interior chips on a slot away from the reducing vertex by one.
* `edge_confinement` shows that an interval of a legal firing set capped by
  nonmembers needs at least two chips.
* `slotInterior_disjoint_of_chip_le_one` excludes such an interval on a slot
  with at most one interior chip and both endpoints outside the firing set.

Statements use an abstract `Spec` to avoid expanding concrete graph data.
`Utilities/Subdivision/SlotPropagation.lean` continues the analysis of a legal
firing set along a slot.
-/

namespace Utilities.Certificate

open Finset

namespace SubdivisionGraph

namespace Spec

variable {n p : ℕ} (spec : Spec n p) (N : ℕ) (hN : 0 < N)

/-! ## The unit presentation and its `N`-fold refinement -/

/-- Every slot of `spec` has length one: `spec.graph` is the graph `G` itself,
presented occurrence-safely, and `spec.scale N hN` is `G^{(N)}`. -/
def IsUnit : Prop := ∀ e : Fin p, spec.length e = 1

/-- On a unit presentation the `N`-fold refinement has slots of fine length
exactly `N`. -/
theorem length_scale (hunit : spec.IsUnit) (g : Fin p) :
    (spec.scale N hN).length g = N := by
  show N * spec.length g = N
  rw [hunit g, Nat.mul_one]

/-! ## Slot points: the fine vertices of one slot, indexed by offset -/

/-- The path position at offset `t` from the tail of `g`, clamped so that the
definition is total. -/
def slotPos (g : Fin p) (t : ℕ) : (spec.scale N hN).PathPosition g :=
  ⟨min t (N * spec.length g), by simp only [scale_length]; omega⟩

/-- **The fine vertex at offset `t` from the tail of the slot `g`**, in the
`N`-fold refinement.  On a unit presentation the meaningful range is
`0 ≤ t ≤ N`: offset `0` is `coreVertex (tail g)`, offset `N` is
`coreVertex (head g)`, and `0 < t < N` gives the interior vertices in order.
Offsets beyond the slot are clamped to the head. -/
def slotPoint (g : Fin p) (t : ℕ) : (spec.scale N hN).Vertex :=
  (spec.scale N hN).pathVertex g (spec.slotPos N hN g t)

theorem slotPoint_eq_pathVertex (g : Fin p) (t : ℕ) :
    spec.slotPoint N hN g t
      = (spec.scale N hN).pathVertex g (spec.slotPos N hN g t) := rfl

theorem slotPos_val (hunit : spec.IsUnit) (g : Fin p) {t : ℕ} (ht : t ≤ N) :
    (spec.slotPos N hN g t).val = t := by
  show min t (N * spec.length g) = t
  rw [hunit g, Nat.mul_one]
  omega

/-! ### Private: reading a `pathVertex` off its numerical position -/

private theorem pathVertex_of_val_zero {m q : ℕ} (sp : Spec m q) {e : Fin q}
    (P : sp.PathPosition e) (hP : P.val = 0) :
    sp.pathVertex e P = sp.coreVertex (sp.core.tail e) := by
  unfold pathVertex
  rw [dif_pos hP]

private theorem pathVertex_of_val_length {m q : ℕ} (sp : Spec m q) {e : Fin q}
    (P : sp.PathPosition e) (hP : P.val = sp.length e) :
    sp.pathVertex e P = sp.coreVertex (sp.core.head e) := by
  have hpos := sp.length_pos e
  unfold pathVertex
  rw [dif_neg (by omega), dif_pos hP]

private theorem coreVertex_ne_interiorVertex {m q : ℕ} (sp : Spec m q) (u : Fin m)
    (e : Fin q) (j : Fin (sp.length e - 1)) :
    sp.coreVertex u ≠ sp.interiorVertex e j := by
  simp [coreVertex, interiorVertex]

/-! ### The two core endpoints, and the interior offsets -/

/-- Offset `0` is the tail of the slot. -/
theorem slotPoint_zero (g : Fin p) :
    spec.slotPoint N hN g 0 = (spec.scale N hN).coreVertex (spec.core.tail g) := by
  have h : (spec.slotPos N hN g 0).val = 0 := by
    show min 0 (N * spec.length g) = 0
    omega
  rw [slotPoint_eq_pathVertex, pathVertex_of_val_zero _ _ h, scale_core]

/-- Offset `N` is the head of the slot. -/
theorem slotPoint_last (hunit : spec.IsUnit) (g : Fin p) :
    spec.slotPoint N hN g N = (spec.scale N hN).coreVertex (spec.core.head g) := by
  have h : (spec.slotPos N hN g N).val = (spec.scale N hN).length g := by
    rw [spec.slotPos_val N hN hunit g (le_refl N), spec.length_scale N hN hunit g]
  rw [slotPoint_eq_pathVertex, pathVertex_of_val_length _ _ h, scale_core]

private theorem slotPos_isInterior (hunit : spec.IsUnit) (g : Fin p) {t : ℕ}
    (h0 : 0 < t) (ht : t < N) :
    (spec.scale N hN).IsInteriorPosition g (spec.slotPos N hN g t) := by
  have hv := spec.slotPos_val N hN hunit g (le_of_lt ht)
  have hL := spec.length_scale N hN hunit g
  constructor <;> omega

/-- An interior offset names an interior fine vertex. -/
theorem exists_interiorVertex_eq_slotPoint (hunit : spec.IsUnit) (g : Fin p)
    {t : ℕ} (h0 : 0 < t) (ht : t < N) :
    ∃ j : Fin ((spec.scale N hN).length g - 1),
      spec.slotPoint N hN g t = (spec.scale N hN).interiorVertex g j :=
  ⟨_, by
    rw [slotPoint_eq_pathVertex, (spec.scale N hN).pathVertex_eq_interiorVertex g _
      (spec.slotPos_isInterior N hN hunit g h0 ht)]⟩

/-- Conversely every interior fine vertex is a slot point, at the offset one
more than its `Fin`-coordinate. -/
theorem interiorVertex_eq_slotPoint (hunit : spec.IsUnit) (g : Fin p)
    (j : Fin ((spec.scale N hN).length g - 1)) :
    (spec.scale N hN).interiorVertex g j = spec.slotPoint N hN g (j.val + 1) := by
  have hL := spec.length_scale N hN hunit g
  have hjlt : j.val + 1 < N := by have := j.isLt; omega
  have hint := spec.slotPos_isInterior N hN hunit g (Nat.succ_pos j.val) hjlt
  have hv := spec.slotPos_val N hN hunit g (le_of_lt hjlt)
  rw [slotPoint_eq_pathVertex, (spec.scale N hN).pathVertex_eq_interiorVertex g _ hint]
  congr 1
  apply Fin.ext
  show j.val = (spec.slotPos N hN g (j.val + 1)).val - 1
  omega

/-- No core vertex is a slot point at an interior offset. -/
theorem coreVertex_ne_slotPoint (hunit : spec.IsUnit) (v : Fin n) (g : Fin p)
    {t : ℕ} (h0 : 0 < t) (ht : t < N) :
    (spec.scale N hN).coreVertex v ≠ spec.slotPoint N hN g t := by
  obtain ⟨j, hj⟩ := spec.exists_interiorVertex_eq_slotPoint N hN hunit g h0 ht
  rw [hj]
  exact coreVertex_ne_interiorVertex (spec.scale N hN) v g j

/-- Distinct offsets in `[0, N]` give distinct fine vertices. -/
theorem slotPoint_ne (hunit : spec.IsUnit) (g : Fin p) {s t : ℕ} (hs : s ≤ N)
    (ht : t ≤ N) (hst : s ≠ t) :
    spec.slotPoint N hN g s ≠ spec.slotPoint N hN g t := by
  intro heq
  rw [slotPoint_eq_pathVertex, slotPoint_eq_pathVertex] at heq
  have hval := congrArg Fin.val ((spec.scale N hN).pathVertex_injective g heq)
  rw [spec.slotPos_val N hN hunit g hs, spec.slotPos_val N hN hunit g ht] at hval
  exact hst hval

/-! ## Local geometry: adjacency and outdegree at an interior slot point -/

/-- **The two fine neighbours of an interior slot point** are the slot points at
the neighbouring offsets, and nothing else. -/
theorem slotPoint_adj_iff (hunit : spec.IsUnit) (g : Fin p) {t : ℕ} (h0 : 0 < t)
    (ht : t < N) (y : (spec.scale N hN).graph.V) :
    0 < num_edges (spec.scale N hN).graph (spec.slotPoint N hN g t) y ↔
      y = spec.slotPoint N hN g (t - 1) ∨ y = spec.slotPoint N hN g (t + 1) := by
  have hint := spec.slotPos_isInterior N hN hunit g h0 ht
  have hv := spec.slotPos_val N hN hunit g (le_of_lt ht)
  have hm := spec.slotPos_val N hN hunit g (show t - 1 ≤ N by omega)
  have hp := spec.slotPos_val N hN hunit g (show t + 1 ≤ N by omega)
  rw [slotPoint_eq_pathVertex, slotPoint_eq_pathVertex, slotPoint_eq_pathVertex,
    (spec.scale N hN).pathVertex_num_edges_pos_iff g _ hint y]
  have e1 : (spec.scale N hN).previousPathPosition g (spec.slotPos N hN g t) hint.1
      = spec.slotPos N hN g (t - 1) := by
    apply Fin.ext
    show (spec.slotPos N hN g t).val - 1 = (spec.slotPos N hN g (t - 1)).val
    omega
  have e2 : (spec.scale N hN).nextPathPosition g (spec.slotPos N hN g t) hint.2
      = spec.slotPos N hN g (t + 1) := by
    apply Fin.ext
    show (spec.slotPos N hN g t).val + 1 = (spec.slotPos N hN g (t + 1)).val
    omega
  rw [e1, e2]

/-- Fine edges at an interior slot point are simple. -/
theorem num_edges_slotPoint_le_one (hunit : spec.IsUnit) (g : Fin p) {t : ℕ}
    (h0 : 0 < t) (ht : t < N) (y : (spec.scale N hN).graph.V) :
    num_edges (spec.scale N hN).graph (spec.slotPoint N hN g t) y ≤ 1 := by
  obtain ⟨j, hj⟩ := spec.exists_interiorVertex_eq_slotPoint N hN hunit g h0 ht
  rw [hj]
  exact (spec.scale N hN).num_edges_interior_le_one g j y

/-- Consecutive slot points are adjacent. -/
theorem num_edges_slotPoint_succ_pos (hunit : spec.IsUnit) (g : Fin p) {t : ℕ}
    (ht : t < N) :
    0 < num_edges (spec.scale N hN).graph (spec.slotPoint N hN g t)
      (spec.slotPoint N hN g (t + 1)) := by
  have hL := spec.length_scale N hN hunit g
  have hoff : t < (spec.scale N hN).length g := by omega
  have h1 : (spec.scale N hN).stepLeftPosition g ⟨t, hoff⟩ = spec.slotPos N hN g t := by
    apply Fin.ext
    rw [spec.slotPos_val N hN hunit g (le_of_lt ht)]
    rfl
  have h2 : (spec.scale N hN).stepRightPosition g ⟨t, hoff⟩
      = spec.slotPos N hN g (t + 1) := by
    apply Fin.ext
    rw [spec.slotPos_val N hN hunit g (show t + 1 ≤ N by omega)]
    rfl
  have hpos := (spec.scale N hN).consecutive_num_edges_pos g ⟨t, hoff⟩
  rw [h1, h2] at hpos
  rw [slotPoint_eq_pathVertex, slotPoint_eq_pathVertex]
  exact hpos

/-- **Consecutive slot points are joined by exactly one fine edge**, as soon as
one of the two is interior.  (At `N = 1` the two ends of a slot are both core
vertices and parallel slots make the multiplicity larger, which is why `2 ≤ N`
is needed and not merely `0 < N`.) -/
theorem num_edges_slotPoint_succ (hunit : spec.IsUnit) (h2N : 2 ≤ N) (g : Fin p)
    {t : ℕ} (ht : t < N) :
    num_edges (spec.scale N hN).graph (spec.slotPoint N hN g t)
      (spec.slotPoint N hN g (t + 1)) = 1 := by
  have hpos := spec.num_edges_slotPoint_succ_pos N hN hunit g ht
  rcases Nat.eq_zero_or_pos t with rfl | h0
  · have hle := spec.num_edges_slotPoint_le_one N hN hunit g (t := 0 + 1)
      (by omega) (by omega) (spec.slotPoint N hN g 0)
    rw [num_edges_symmetric] at hle
    omega
  · have hle := spec.num_edges_slotPoint_le_one N hN hunit g h0 ht
      (spec.slotPoint N hN g (t + 1))
    omega

/-- **Every fine vertex is a core vertex or an interior slot point.**  (The
`Vertex` type of a `Spec` is `Fin n ⊕ Σ g, Fin (len g - 1)`, and
`interiorVertex_eq_slotPoint` names the second summand by its offset.) -/
theorem vertex_cases (hunit : spec.IsUnit)
    (v : (spec.scale N hN).graph.V) :
    (∃ u : Fin n, v = (spec.scale N hN).coreVertex u) ∨
      ∃ (g : Fin p) (i : ℕ), 0 < i ∧ i < N ∧ v = spec.slotPoint N hN g i := by
  rcases v with u | ⟨g, o⟩
  · exact Or.inl ⟨u, rfl⟩
  · have hL := spec.length_scale N hN hunit g
    have ho := o.isLt
    exact Or.inr ⟨g, o.val + 1, by omega, by omega,
      spec.interiorVertex_eq_slotPoint N hN hunit g o⟩

/-! ### Private: outdegree at a vertex of fine degree two -/

/-- The outdegree of a two-valent simple vertex relative to a set: each of the
two neighbours outside the set contributes one. -/
private theorem outdeg_of_two_nbrs {G : CFGraph} (T : Finset G.V) {x a b : G.V}
    (hab : a ≠ b) (hadj : ∀ y : G.V, 0 < num_edges G x y ↔ y = a ∨ y = b)
    (hle : ∀ y : G.V, num_edges G x y ≤ 1) :
    outdeg_S G T x = (if a ∈ T then 0 else 1) + (if b ∈ T then 0 else 1) := by
  classical
  have hna : num_edges G x a = 1 := by
    have h1 : 0 < num_edges G x a := (hadj a).mpr (Or.inl rfl)
    have h2 := hle a
    omega
  have hnb : num_edges G x b = 1 := by
    have h1 : 0 < num_edges G x b := (hadj b).mpr (Or.inr rfl)
    have h2 := hle b
    omega
  have hform : outdeg_S G T x
      = ∑ y ∈ (Finset.univ : Finset G.V),
          (if y ∈ T then (0 : ℤ) else (num_edges G x y : ℤ)) := by
    rw [outdeg_S_eq_sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : y ∈ T <;> simp [hy]
  have hrestrict : ∑ y ∈ ({a, b} : Finset G.V),
        (if y ∈ T then (0 : ℤ) else (num_edges G x y : ℤ))
      = ∑ y ∈ (Finset.univ : Finset G.V),
          (if y ∈ T then (0 : ℤ) else (num_edges G x y : ℤ)) := by
    refine Finset.sum_subset (Finset.subset_univ _) fun y _ hy2 => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy2
    have hz : num_edges G x y = 0 := by
      by_contra hne
      rcases (hadj y).mp (Nat.pos_of_ne_zero hne) with h | h
      · exact hy2 (Or.inl h)
      · exact hy2 (Or.inr h)
    simp [hz]
  rw [hform, ← hrestrict, Finset.sum_pair hab, hna, hnb]
  split_ifs <;> norm_num

/-- **The outdegree of an interior slot point**: it counts which of the two
neighbouring offsets lies outside the set. -/
theorem outdeg_slotPoint (hunit : spec.IsUnit) (S : Finset (spec.scale N hN).graph.V)
    (g : Fin p) {t : ℕ} (h0 : 0 < t) (ht : t < N) :
    outdeg_S (spec.scale N hN).graph S (spec.slotPoint N hN g t)
      = (if spec.slotPoint N hN g (t - 1) ∈ S then 0 else 1)
        + (if spec.slotPoint N hN g (t + 1) ∈ S then 0 else 1) :=
  outdeg_of_two_nbrs S
    (spec.slotPoint_ne N hN hunit g (by omega) (by omega) (by omega))
    (spec.slotPoint_adj_iff N hN hunit g h0 ht)
    (spec.num_edges_slotPoint_le_one N hN hunit g h0 ht)

/-- **An interior slot point has fine degree two.** -/
theorem vertex_degree_slotPoint (hunit : spec.IsUnit) (g : Fin p) {t : ℕ}
    (h0 : 0 < t) (ht : t < N) :
    vertex_degree (spec.scale N hN).graph (spec.slotPoint N hN g t) = 2 := by
  have h := spec.outdeg_slotPoint N hN hunit (∅ : Finset (spec.scale N hN).graph.V)
    g h0 ht
  simp only [Finset.notMem_empty, if_false] at h
  rw [show vertex_degree (spec.scale N hN).graph (spec.slotPoint N hN g t)
      = outdeg_S (spec.scale N hN).graph ∅ (spec.slotPoint N hN g t) by
    simp [vertex_degree, outdeg_S]]
  rw [h]
  norm_num

/-! ## Firing an interval of interior slot points -/

/-- The set of fine points of the slot `g` at offsets `s, …, t`. -/
def slotInterval (g : Fin p) (s t : ℕ) : Finset (spec.scale N hN).graph.V :=
  (Finset.Icc s t).image (spec.slotPoint N hN g)

theorem mem_slotInterval_iff (g : Fin p) (s t : ℕ)
    (x : (spec.scale N hN).graph.V) :
    x ∈ spec.slotInterval N hN g s t ↔
      ∃ j, s ≤ j ∧ j ≤ t ∧ spec.slotPoint N hN g j = x := by
  simp only [slotInterval, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨j, ⟨h1, h2⟩, h3⟩
    exact ⟨j, h1, h2, h3⟩
  · rintro ⟨j, h1, h2, h3⟩
    exact ⟨j, ⟨h1, h2⟩, h3⟩

theorem slotPoint_mem_slotInterval_iff (hunit : spec.IsUnit) (g : Fin p)
    {s t j : ℕ} (htN : t ≤ N) (hj : j ≤ N) :
    spec.slotPoint N hN g j ∈ spec.slotInterval N hN g s t ↔ s ≤ j ∧ j ≤ t := by
  rw [spec.mem_slotInterval_iff N hN g]
  constructor
  · rintro ⟨k, h1, h2, h3⟩
    have hk : k = j := by
      by_contra hne
      exact spec.slotPoint_ne N hN hunit g (le_trans h2 htN) hj hne h3
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨j, h1, h2, rfl⟩

/-- **Interval firing.**
Let `D ≥ 0` on the `N`-fold refinement of a unit presentation, let `g` be a slot
and `1 ≤ s ≤ t < N`.  If the interior slot points at offsets `s` and `t` each
carry a chip — two chips if `s = t` — then the run of interior points at offsets
`s, …, t` is a legal firing set for `D`, and it contains no core vertex. -/
theorem interval_firing (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} (hD : effective D) (g : Fin p) {s t : ℕ}
    (hs : 1 ≤ s) (hst : s ≤ t) (htN : t < N)
    (hDs : 1 ≤ D (spec.slotPoint N hN g s))
    (hDt : 1 ≤ D (spec.slotPoint N hN g t))
    (hdbl : s = t → 2 ≤ D (spec.slotPoint N hN g s)) :
    legal_set (spec.scale N hN).graph D (spec.slotInterval N hN g s t) ∧
      ∀ v : Fin n,
        (spec.scale N hN).coreVertex v ∉ spec.slotInterval N hN g s t := by
  constructor
  · intro x hx
    obtain ⟨j, hj1, hj2, rfl⟩ := (spec.mem_slotInterval_iff N hN g s t x).mp hx
    have hj0 : 0 < j := by omega
    have hjN : j < N := by omega
    have hDj := hD (spec.slotPoint N hN g j)
    have hlo := spec.slotPoint_mem_slotInterval_iff N hN hunit g (s := s) (t := t)
      (j := j - 1) (le_of_lt htN) (by omega)
    have hhi := spec.slotPoint_mem_slotInterval_iff N hN hunit g (s := s) (t := t)
      (j := j + 1) (le_of_lt htN) (by omega)
    rw [spec.outdeg_slotPoint N hN hunit _ g hj0 hjN]
    by_cases h1 : spec.slotPoint N hN g (j - 1) ∈ spec.slotInterval N hN g s t
    · by_cases h2 : spec.slotPoint N hN g (j + 1) ∈ spec.slotInterval N hN g s t
      · rw [if_pos h1, if_pos h2]
        omega
      · -- the top of the run: `j = t`
        rw [if_pos h1, if_neg h2]
        have hnot : ¬(s ≤ j + 1 ∧ j + 1 ≤ t) := fun hc => h2 (hhi.mpr hc)
        have hjt : j = t := by omega
        subst hjt
        omega
    · by_cases h2 : spec.slotPoint N hN g (j + 1) ∈ spec.slotInterval N hN g s t
      · -- the bottom of the run: `j = s`
        rw [if_neg h1, if_pos h2]
        have hnot : ¬(s ≤ j - 1 ∧ j - 1 ≤ t) := fun hc => h1 (hlo.mpr hc)
        have hjs : j = s := by omega
        subst hjs
        omega
      · -- a one-point run: `s = j = t`, and the doubled chip pays for it
        rw [if_neg h1, if_neg h2]
        have hnot1 : ¬(s ≤ j - 1 ∧ j - 1 ≤ t) := fun hc => h1 (hlo.mpr hc)
        have hnot2 : ¬(s ≤ j + 1 ∧ j + 1 ≤ t) := fun hc => h2 (hhi.mpr hc)
        have hjs : j = s := by omega
        have hjt : s = t := by omega
        subst hjs
        have := hdbl hjt
        omega
  · intro v hv
    obtain ⟨j, hj1, hj2, hj3⟩ := (spec.mem_slotInterval_iff N hN g s t _).mp hv
    exact spec.coreVertex_ne_slotPoint N hN hunit v g (t := j) (by omega) (by omega)
      hj3.symm

/-! ## Confinement of a legal set inside one slot -/

/-- **Edge confinement.**
Let `S` be legal for the effective divisor `D`, and let `[a, r]` be a maximal
run of interior offsets of the slot `g` whose slot points lie in `S` — maximal
in the sense that the slot points at offsets `a - 1` and `r + 1` do **not**
(when `a = 1` and `r = N - 1` those are the two core endpoints of `g`).  Then
the run carries at least two chips. -/
theorem edge_confinement (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} (hD : effective D)
    {S : Finset (spec.scale N hN).graph.V}
    (hS : legal_set (spec.scale N hN).graph D S) (g : Fin p) {a r : ℕ}
    (ha : 1 ≤ a) (har : a ≤ r) (hrN : r < N)
    (hlo : spec.slotPoint N hN g (a - 1) ∉ S)
    (hhi : spec.slotPoint N hN g (r + 1) ∉ S)
    (hmem : ∀ j, a ≤ j → j ≤ r → spec.slotPoint N hN g j ∈ S) :
    2 ≤ ∑ j ∈ Finset.Icc a r, D (spec.slotPoint N hN g j) := by
  -- Both caps of the run are genuine fine neighbours of its two ends.
  have hedgeLo : 1 ≤ num_edges (spec.scale N hN).graph (spec.slotPoint N hN g a)
      (spec.slotPoint N hN g (a - 1)) := by
    have h := spec.num_edges_slotPoint_succ_pos N hN hunit g
      (t := a - 1) (by omega)
    rw [show a - 1 + 1 = a by omega, num_edges_symmetric] at h
    omega
  have hedgeHi : 1 ≤ num_edges (spec.scale N hN).graph (spec.slotPoint N hN g r)
      (spec.slotPoint N hN g (r + 1)) :=
    spec.num_edges_slotPoint_succ_pos N hN hunit g hrN
  rcases eq_or_lt_of_le har with rfl | hlt
  · -- a single point: its outdegree is two, so it must carry two chips
    have hne := spec.slotPoint_ne N hN hunit g (s := a - 1) (t := a + 1)
      (by omega) (by omega) (by omega)
    have hbound := Gonality.two_num_edges_le_outdeg_S S (spec.slotPoint N hN g a) hne hlo hhi
    have hlegal := hS _ (hmem a le_rfl le_rfl)
    have hcastLo : (1 : ℤ) ≤ (num_edges (spec.scale N hN).graph
        (spec.slotPoint N hN g a) (spec.slotPoint N hN g (a - 1)) : ℤ) := by
      exact_mod_cast hedgeLo
    have hcastHi : (1 : ℤ) ≤ (num_edges (spec.scale N hN).graph
        (spec.slotPoint N hN g a) (spec.slotPoint N hN g (a + 1)) : ℤ) := by
      exact_mod_cast hedgeHi
    rw [Finset.Icc_self, Finset.sum_singleton]
    omega
  · -- a genuine interval: each end carries a chip
    have hDa : 1 ≤ D (spec.slotPoint N hN g a) := by
      have hbound := Gonality.num_edges_le_outdeg_S S (spec.slotPoint N hN g a) hlo
      have hlegal := hS _ (hmem a le_rfl (le_of_lt hlt))
      have hcast : (1 : ℤ) ≤ (num_edges (spec.scale N hN).graph
          (spec.slotPoint N hN g a) (spec.slotPoint N hN g (a - 1)) : ℤ) := by
        exact_mod_cast hedgeLo
      omega
    have hDr : 1 ≤ D (spec.slotPoint N hN g r) := by
      have hbound := Gonality.num_edges_le_outdeg_S S (spec.slotPoint N hN g r) hhi
      have hlegal := hS _ (hmem r (le_of_lt hlt) le_rfl)
      have hcast : (1 : ℤ) ≤ (num_edges (spec.scale N hN).graph
          (spec.slotPoint N hN g r) (spec.slotPoint N hN g (r + 1)) : ℤ) := by
        exact_mod_cast hedgeHi
      omega
    have hsub : ({a, r} : Finset ℕ) ⊆ Finset.Icc a r := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_Icc]
      rcases hx with rfl | rfl <;> omega
    have hpair := Finset.sum_le_sum_of_subset_of_nonneg (f := fun j : ℕ =>
      D (spec.slotPoint N hN g j)) hsub (fun x _ _ => hD _)
    rw [Finset.sum_pair (by omega : a ≠ r)] at hpair
    omega

/-! ## Reduced divisors and one-chip slots -/

/-- **At most one interior chip per slot.**  A `q`-reduced effective divisor
carries at most one chip on the interior of each slot, as long as `q` is not
itself interior to that slot.  (Some such hypothesis is needed: `2 · q` at an
interior point `q` is `q`-reduced.) -/
theorem sum_interior_le_one_of_qReduced (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} (hD : effective D)
    {q : (spec.scale N hN).graph.V}
    (hred : q_reduced (spec.scale N hN).graph q D) (g : Fin p)
    (hq : ∀ j, 0 < j → j < N → q ≠ spec.slotPoint N hN g j) :
    ∑ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN g j) ≤ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  -- The offsets that actually carry a chip.
  set T : Finset ℕ :=
    (Finset.Ioo 0 N).filter (fun j => 1 ≤ D (spec.slotPoint N hN g j)) with hTdef
  have hsplit : ∑ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN g j)
      = ∑ j ∈ T, D (spec.slotPoint N hN g j) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro x hx hxT
    have hnn := hD (spec.slotPoint N hN g x)
    have hlt : ¬(1 ≤ D (spec.slotPoint N hN g x)) := fun h =>
      hxT (Finset.mem_filter.mpr ⟨hx, h⟩)
    omega
  have hTne : T.Nonempty := by
    rcases Finset.eq_empty_or_nonempty T with h | h
    · rw [h, Finset.sum_empty] at hsplit
      omega
    · exact h
  set s := T.min' hTne with hsdef
  set t := T.max' hTne with htdef
  have hsT : s ∈ T := T.min'_mem hTne
  have htT : t ∈ T := T.max'_mem hTne
  have hsIoo := Finset.mem_Ioo.mp (Finset.mem_filter.mp hsT).1
  have htIoo := Finset.mem_Ioo.mp (Finset.mem_filter.mp htT).1
  have hDs : 1 ≤ D (spec.slotPoint N hN g s) := (Finset.mem_filter.mp hsT).2
  have hDt : 1 ≤ D (spec.slotPoint N hN g t) := (Finset.mem_filter.mp htT).2
  have hst : s ≤ t := T.min'_le t htT
  have hdbl : s = t → 2 ≤ D (spec.slotPoint N hN g s) := by
    intro heq
    have hTsingle : T = {s} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hsT, fun x hx => le_antisymm ?_ ?_⟩
      · rw [heq]; exact T.le_max' x hx
      · exact T.min'_le x hx
    rw [hTsingle, Finset.sum_singleton] at hsplit
    omega
  obtain ⟨hlegal, -⟩ := spec.interval_firing N hN hunit hD g (by omega) hst
    (by omega) hDs hDt hdbl
  refine hred.2 (spec.slotInterval N hN g s t) ?_ ?_ hlegal
  · intro hqmem
    obtain ⟨j, hj1, hj2, hj3⟩ := (spec.mem_slotInterval_iff N hN g s t q).mp hqmem
    exact hq j (by omega) (by omega) hj3.symm
  · exact ⟨spec.slotPoint N hN g s,
      (spec.mem_slotInterval_iff N hN g s t _).mpr ⟨s, le_rfl, hst, rfl⟩⟩

/-- **At most one interior chip per slot, reducing at a core vertex.**  A
divisor reduced at a core vertex carries at most one chip on the interior of
every slot. -/
theorem sum_interior_le_one_of_qReduced_core (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} (hD : effective D) {v : Fin n}
    (hred : q_reduced (spec.scale N hN).graph ((spec.scale N hN).coreVertex v) D)
    (g : Fin p) :
    ∑ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN g j) ≤ 1 :=
  spec.sum_interior_le_one_of_qReduced N hN hunit hD hred g
    (fun _ hj0 hjN => spec.coreVertex_ne_slotPoint N hN hunit v g hj0 hjN)

/-- **A one-chip slot with both ends outside a legal set misses it.**  A slot
carrying at most one chip in its interior, neither of whose endpoints lies in
the legal set `S`, does not meet `S` at all. -/
theorem slotInterior_disjoint_of_chip_le_one (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} (hD : effective D)
    {S : Finset (spec.scale N hN).graph.V}
    (hS : legal_set (spec.scale N hN).graph D S) (g : Fin p)
    (hchip : ∑ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN g j) ≤ 1)
    (htail : (spec.scale N hN).coreVertex (spec.core.tail g) ∉ S)
    (hhead : (spec.scale N hN).coreVertex (spec.core.head g) ∉ S)
    {t : ℕ} (h0 : 0 < t) (htN : t < N) :
    spec.slotPoint N hN g t ∉ S := by
  classical
  intro hmemS
  have h0S : spec.slotPoint N hN g 0 ∉ S := by
    rw [spec.slotPoint_zero N hN g]; exact htail
  have hNS : spec.slotPoint N hN g N ∉ S := by
    rw [spec.slotPoint_last N hN hunit g]; exact hhead
  -- The lower end of the maximal run of `S` through offset `t`.
  set B : Finset ℕ := (Finset.Icc 1 t).filter
    (fun i => ∀ k ∈ Finset.Icc i t, spec.slotPoint N hN g k ∈ S) with hBdef
  have htB : t ∈ B := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h0, le_rfl⟩, fun k hk => ?_⟩
    rw [Finset.mem_Icc] at hk
    rw [show k = t by omega]
    exact hmemS
  have hBne : B.Nonempty := ⟨t, htB⟩
  set a := B.min' hBne with hadef
  have haB : a ∈ B := B.min'_mem hBne
  have haIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp haB).1
  have haS : ∀ k, a ≤ k → k ≤ t → spec.slotPoint N hN g k ∈ S := by
    intro k h1 h2
    exact (Finset.mem_filter.mp haB).2 k (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  have hlo : spec.slotPoint N hN g (a - 1) ∉ S := by
    rcases Nat.eq_or_lt_of_le haIcc.1 with h | h
    · rw [show a - 1 = 0 by omega]
      exact h0S
    · intro hc
      have hmemB : a - 1 ∈ B := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
          fun k hk => ?_⟩
        rw [Finset.mem_Icc] at hk
        rcases Nat.eq_or_lt_of_le hk.1 with hk1 | hk1
        · rw [← hk1]; exact hc
        · exact haS k (by omega) hk.2
      have := B.min'_le _ hmemB
      omega
  -- The upper end.
  set C : Finset ℕ := (Finset.Icc t (N - 1)).filter
    (fun i => ∀ k ∈ Finset.Icc t i, spec.slotPoint N hN g k ∈ S) with hCdef
  have htC : t ∈ C := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, fun k hk => ?_⟩
    rw [Finset.mem_Icc] at hk
    rw [show k = t by omega]
    exact hmemS
  have hCne : C.Nonempty := ⟨t, htC⟩
  set r := C.max' hCne with hrdef
  have hrC : r ∈ C := C.max'_mem hCne
  have hrIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hrC).1
  have hrS : ∀ k, t ≤ k → k ≤ r → spec.slotPoint N hN g k ∈ S := by
    intro k h1 h2
    exact (Finset.mem_filter.mp hrC).2 k (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  have hhi : spec.slotPoint N hN g (r + 1) ∉ S := by
    rcases Nat.eq_or_lt_of_le hrIcc.2 with h | h
    · rw [show r + 1 = N by omega]
      exact hNS
    · intro hc
      have hmemC : r + 1 ∈ C := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
          fun k hk => ?_⟩
        rw [Finset.mem_Icc] at hk
        rcases Nat.eq_or_lt_of_le hk.2 with hk2 | hk2
        · rw [hk2]; exact hc
        · exact hrS k hk.1 (by omega)
      have := C.le_max' _ hmemC
      omega
  -- Confinement on the run contradicts the one-chip bound.
  have hrun : ∀ j, a ≤ j → j ≤ r → spec.slotPoint N hN g j ∈ S := by
    intro j h1 h2
    by_cases hjt : j ≤ t
    · exact haS j h1 hjt
    · exact hrS j (by omega) h2
  have htwo := spec.edge_confinement N hN hunit hD hS g (a := a) (r := r)
    haIcc.1 (le_trans haIcc.2 hrIcc.1) (by omega) hlo hhi hrun
  have hsub : Finset.Icc a r ⊆ Finset.Ioo 0 N := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_Ioo]
    omega
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun j : ℕ =>
    D (spec.slotPoint N hN g j)) hsub (fun x _ _ => hD _)
  omega

end Spec

end SubdivisionGraph

end Utilities.Certificate

