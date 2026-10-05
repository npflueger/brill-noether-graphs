module

public import Utilities.Subdivision.SlotIntervalFiring

@[expose] public section

/-!
# Propagation of a legal firing set along a slot

Suppose a divisor has at most one interior chip per slot, a firing set is legal,
and it contains a chipless core vertex. Along an incident chipless slot the
whole path, including its other endpoint, belongs to the firing set
(`propagate_chipless`, `core_closure`). On a one-chip slot, membership
propagates up to the chip and, unless the far endpoint is in the set, no
further (`propagate_upto_chip`, `not_mem_beyond_chip`); if both core endpoints
are chipless members of the firing set, the whole slot is in it
(`propagate_both_ends`).

`sidePoint g z k` measures offset `k` from the chosen endpoint `z`: it is
`slotPoint g k` from the tail and `slotPoint g (N-k)` from the head. The basic
adjacency and outgoing-degree formulas follow from the tail-relative formulas.
All results use an abstract unit presentation and an arbitrary positive scale.
-/

namespace Utilities.Certificate

open Finset

namespace SubdivisionGraph

namespace Spec

variable {n p : ℕ} (spec : Spec n p) (N : ℕ) (hN : 0 < N)

/-! ## Fine points measured from a chosen endpoint of the slot -/

/-- **The fine vertex at offset `k` from the endpoint `z` of the slot `g`**, in
the `N`-fold refinement.  It is `slotPoint g k` when `z` is the tail of `g` and
`slotPoint g (N - k)` otherwise, so on a unit presentation offset `0` is
`coreVertex z`, offset `N` is the other endpoint of `g`, and the offsets
`0 < k < N` are the interior vertices in order away from `z`.

The definition is total: when `z` is not an endpoint of `g` at all it reads the
slot from the head, which is harmless because every lemma below either fixes the
orientation explicitly or carries the incidence hypothesis. -/
def sidePoint (g : Fin p) (z : Fin n) (k : ℕ) : (spec.scale N hN).Vertex :=
  if spec.core.tail g = z then spec.slotPoint N hN g k
  else spec.slotPoint N hN g (N - k)

theorem sidePoint_of_tail (g : Fin p) {z : Fin n} (hz : spec.core.tail g = z)
    (k : ℕ) : spec.sidePoint N hN g z k = spec.slotPoint N hN g k := by
  unfold sidePoint
  rw [ite_eq_left hz]

theorem sidePoint_of_ne (g : Fin p) {z : Fin n} (hz : spec.core.tail g ≠ z)
    (k : ℕ) : spec.sidePoint N hN g z k = spec.slotPoint N hN g (N - k) := by
  unfold sidePoint
  rw [ite_eq_right hz]

/-- Read from the tail, `sidePoint` *is* `slotPoint`. -/
theorem sidePoint_tail (g : Fin p) (k : ℕ) :
    spec.sidePoint N hN g (spec.core.tail g) k = spec.slotPoint N hN g k :=
  spec.sidePoint_of_tail N hN g rfl k

/-- Read from the head, `sidePoint` is `slotPoint` at the reflected offset.
(Looplessness of the core is what makes the head different from the tail.) -/
theorem sidePoint_head (g : Fin p) (k : ℕ) :
    spec.sidePoint N hN g (spec.core.head g) k = spec.slotPoint N hN g (N - k) :=
  spec.sidePoint_of_ne N hN g (spec.core_loopless g) k

/-- Offset `0` from `z` is the core vertex `z` itself. -/
theorem sidePoint_zero (hunit : spec.IsUnit) (g : Fin p) {z : Fin n}
    (hinc : spec.core.tail g = z ∨ spec.core.head g = z) :
    spec.sidePoint N hN g z 0 = (spec.scale N hN).coreVertex z := by
  by_cases hc : spec.core.tail g = z
  · rw [spec.sidePoint_of_tail N hN g hc, spec.slotPoint_zero N hN g, hc]
  · rw [spec.sidePoint_of_ne N hN g hc, Nat.sub_zero,
      spec.slotPoint_last N hN hunit g, hinc.resolve_left hc]

/-- Offset `N` from the tail is the head. -/
theorem sidePoint_last_of_tail (hunit : spec.IsUnit) (g : Fin p) {z : Fin n}
    (hz : spec.core.tail g = z) :
    spec.sidePoint N hN g z N = (spec.scale N hN).coreVertex (spec.core.head g) := by
  rw [spec.sidePoint_of_tail N hN g hz, spec.slotPoint_last N hN hunit g]

/-- Offset `N` from anything else — in particular from the head — is the tail. -/
theorem sidePoint_last_of_ne (g : Fin p) {z : Fin n} (hz : spec.core.tail g ≠ z) :
    spec.sidePoint N hN g z N = (spec.scale N hN).coreVertex (spec.core.tail g) := by
  rw [spec.sidePoint_of_ne N hN g hz, Nat.sub_self, spec.slotPoint_zero N hN g]

/-- Distinct offsets in `[0, N]` give distinct fine vertices. -/
theorem sidePoint_ne (hunit : spec.IsUnit) (g : Fin p) (z : Fin n) {k l : ℕ}
    (hk : k ≤ N) (hl : l ≤ N) (hkl : k ≠ l) :
    spec.sidePoint N hN g z k ≠ spec.sidePoint N hN g z l := by
  by_cases hc : spec.core.tail g = z
  · rw [spec.sidePoint_of_tail N hN g hc, spec.sidePoint_of_tail N hN g hc]
    exact spec.slotPoint_ne N hN hunit g hk hl hkl
  · rw [spec.sidePoint_of_ne N hN g hc, spec.sidePoint_of_ne N hN g hc]
    exact spec.slotPoint_ne N hN hunit g (by omega) (by omega) (by omega)

/-- Consecutive offsets are adjacent. -/
theorem num_edges_sidePoint_succ_pos (hunit : spec.IsUnit) (g : Fin p) (z : Fin n)
    {k : ℕ} (hk : k < N) :
    0 < num_edges (spec.scale N hN).graph (spec.sidePoint N hN g z k)
      (spec.sidePoint N hN g z (k + 1)) := by
  by_cases hc : spec.core.tail g = z
  · rw [spec.sidePoint_of_tail N hN g hc, spec.sidePoint_of_tail N hN g hc]
    exact spec.num_edges_slotPoint_succ_pos N hN hunit g hk
  · rw [spec.sidePoint_of_ne N hN g hc, spec.sidePoint_of_ne N hN g hc,
      num_edges_symmetric]
    have h := spec.num_edges_slotPoint_succ_pos N hN hunit g (t := N - (k + 1))
      (by omega)
    rwa [show N - (k + 1) + 1 = N - k by omega] at h

/-- **The two fine neighbours of an interior point**, in the `sidePoint`
vocabulary: the offsets `k - 1` and `k + 1` from the same end. -/
theorem sidePoint_adj_iff (hunit : spec.IsUnit) (g : Fin p) (z : Fin n) {k : ℕ}
    (h0 : 0 < k) (hk : k < N) (y : (spec.scale N hN).graph.V) :
    0 < num_edges (spec.scale N hN).graph (spec.sidePoint N hN g z k) y ↔
      y = spec.sidePoint N hN g z (k - 1) ∨ y = spec.sidePoint N hN g z (k + 1) := by
  by_cases hc : spec.core.tail g = z
  · rw [spec.sidePoint_of_tail N hN g hc, spec.sidePoint_of_tail N hN g hc,
      spec.sidePoint_of_tail N hN g hc]
    exact spec.slotPoint_adj_iff N hN hunit g h0 hk y
  · rw [spec.sidePoint_of_ne N hN g hc, spec.sidePoint_of_ne N hN g hc,
      spec.sidePoint_of_ne N hN g hc,
      spec.slotPoint_adj_iff N hN hunit g (t := N - k) (by omega) (by omega) y,
      show N - k - 1 = N - (k + 1) by omega, show N - k + 1 = N - (k - 1) by omega]
    exact or_comm

/-- **The outdegree at an interior point**, in the `sidePoint` vocabulary. -/
theorem outdeg_sidePoint (hunit : spec.IsUnit)
    (S : Finset (spec.scale N hN).graph.V) (g : Fin p) (z : Fin n) {k : ℕ}
    (h0 : 0 < k) (hk : k < N) :
    outdeg_S (spec.scale N hN).graph S (spec.sidePoint N hN g z k)
      = (if spec.sidePoint N hN g z (k - 1) ∈ S then 0 else 1)
        + (if spec.sidePoint N hN g z (k + 1) ∈ S then 0 else 1) := by
  by_cases hc : spec.core.tail g = z
  · rw [spec.sidePoint_of_tail N hN g hc, spec.sidePoint_of_tail N hN g hc,
      spec.sidePoint_of_tail N hN g hc]
    exact spec.outdeg_slotPoint N hN hunit S g h0 hk
  · rw [spec.sidePoint_of_ne N hN g hc, spec.sidePoint_of_ne N hN g hc,
      spec.sidePoint_of_ne N hN g hc,
      spec.outdeg_slotPoint N hN hunit S g (t := N - k) (by omega) (by omega),
      show N - k - 1 = N - (k + 1) by omega, show N - k + 1 = N - (k - 1) by omega]
    exact add_comm _ _

/-! ## Reading the one-chip hypothesis from either end

`sum_interior_le_one_of_qReduced_core` (in `SlotIntervalFiring.lean`) produces
the one-chip hypothesis in the tail-relative form
`∑_{j ∈ Ioo 0 N} D (slotPoint g j) ≤ 1`.  The two lemmas here turn it into the
statement propagation actually uses: *every interior offset other than the one
carrying the chip is chipless*, measured from whichever end one likes. -/

/-- With at most one chip on the interior of `g`, a chip at offset `a` empties
every other interior offset. -/
private theorem slotPoint_eq_zero_of_chip {D : CFDiv (spec.scale N hN).graph}
    (hD : effective D) (g : Fin p)
    (hchip : ∑ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN g j) ≤ 1)
    {a b : ℕ} (ha : a ∈ Finset.Ioo 0 N) (hb : b ∈ Finset.Ioo 0 N) (hab : a ≠ b)
    (hDa : 1 ≤ D (spec.slotPoint N hN g a)) :
    D (spec.slotPoint N hN g b) = 0 := by
  have hsub : ({a, b} : Finset ℕ) ⊆ Finset.Ioo 0 N := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun j : ℕ =>
    D (spec.slotPoint N hN g j)) hsub (fun x _ _ => hD _)
  rw [Finset.sum_pair hab] at hle
  have := hD (spec.slotPoint N hN g b)
  omega

/-- **The one-chip hypothesis, read from the endpoint `z`.**  If the interior of
`g` carries at most one chip and there is a chip at offset `t` from `z`, then
every other interior offset from `z` is chipless. -/
theorem sidePoint_apply_eq_zero_of_chip
    {D : CFDiv (spec.scale N hN).graph} (hD : effective D) (g : Fin p) (z : Fin n)
    (hchip : ∑ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN g j) ≤ 1)
    {t : ℕ} (ht0 : 0 < t) (htN : t < N)
    (hDt : 1 ≤ D (spec.sidePoint N hN g z t))
    {k : ℕ} (hk0 : 0 < k) (hkN : k < N) (hkt : k ≠ t) :
    D (spec.sidePoint N hN g z k) = 0 := by
  by_cases hc : spec.core.tail g = z
  · rw [spec.sidePoint_of_tail N hN g hc] at hDt ⊢
    exact spec.slotPoint_eq_zero_of_chip N hN hD g hchip
      (Finset.mem_Ioo.mpr ⟨ht0, htN⟩) (Finset.mem_Ioo.mpr ⟨hk0, hkN⟩)
      (Ne.symm hkt) hDt
  · rw [spec.sidePoint_of_ne N hN g hc] at hDt ⊢
    exact spec.slotPoint_eq_zero_of_chip N hN hD g hchip
      (Finset.mem_Ioo.mpr ⟨by omega, by omega⟩)
      (Finset.mem_Ioo.mpr ⟨by omega, by omega⟩) (by omega) hDt

/-- A chipless slot is chipless read from either end. -/
theorem sidePoint_apply_eq_zero_of_chipless
    {D : CFDiv (spec.scale N hN).graph} (g : Fin p) (z : Fin n)
    (hfree : ∀ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN g j) = 0)
    {k : ℕ} (hk0 : 0 < k) (hkN : k < N) :
    D (spec.sidePoint N hN g z k) = 0 := by
  by_cases hc : spec.core.tail g = z
  · rw [spec.sidePoint_of_tail N hN g hc]
    exact hfree k (Finset.mem_Ioo.mpr ⟨hk0, hkN⟩)
  · rw [spec.sidePoint_of_ne N hN g hc]
    exact hfree (N - k) (Finset.mem_Ioo.mpr ⟨by omega, by omega⟩)

/-! ## Closure at a core vertex -/

/-- **Closure at a core vertex.**  A chipless core vertex of a legal set absorbs
all of its fine neighbours: legality reads
`outdeg_S (coreVertex w) ≤ D (coreVertex w) = 0`, so no edge at `coreVertex w`
leaves `S`.  (This is `Gonality.mem_of_apply_le_zero` at a core vertex.) -/
theorem mem_of_coreVertex_mem {D : CFDiv (spec.scale N hN).graph}
    {S : Finset (spec.scale N hN).graph.V}
    (hS : legal_set (spec.scale N hN).graph D S) {w : Fin n}
    (hwS : (spec.scale N hN).coreVertex w ∈ S)
    (hwD : D ((spec.scale N hN).coreVertex w) = 0)
    {y : (spec.scale N hN).graph.V}
    (hy : 0 < num_edges (spec.scale N hN).graph
      ((spec.scale N hN).coreVertex w) y) : y ∈ S :=
  Gonality.mem_of_apply_le_zero hS hwS (le_of_eq hwD) hy

/-- **Closure at a core vertex, the form propagation starts from**: the
offset-one point of every slot at a chipless core vertex of a legal set lies in
the set. -/
theorem sidePoint_one_mem (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph}
    {S : Finset (spec.scale N hN).graph.V}
    (hS : legal_set (spec.scale N hN).graph D S) (g : Fin p) {w : Fin n}
    (hinc : spec.core.tail g = w ∨ spec.core.head g = w)
    (hwS : (spec.scale N hN).coreVertex w ∈ S)
    (hwD : D ((spec.scale N hN).coreVertex w) = 0) :
    spec.sidePoint N hN g w 1 ∈ S := by
  have hadj := spec.num_edges_sidePoint_succ_pos N hN hunit g w (k := 0) hN
  rw [spec.sidePoint_zero N hN hunit g hinc] at hadj
  exact Gonality.mem_of_apply_le_zero hS hwS (le_of_eq hwD) hadj

/-! ## A chipless slot is absorbed whole -/

/-- **A chipless slot is absorbed whole.**  Let `S` be legal for `D`, let `w` be a
core vertex with `coreVertex w ∈ S` and `D (coreVertex w) = 0`, and let `g` be a
slot at `w` carrying no interior chip.  Then *every* point of `g` measured from
`w` lies in `S` — all `N - 1` interior vertices and, at offset `N`, the far
endpoint.

The proof is an induction on the offset: `D` vanishes at `sidePoint g w k` for
every `k < N` (at `k = 0` by hypothesis, in the interior by chiplessness), so
the closure lemma carries membership from offset `k` to offset `k + 1`. -/
theorem propagate_chipless (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph}
    {S : Finset (spec.scale N hN).graph.V}
    (hS : legal_set (spec.scale N hN).graph D S) (g : Fin p) {w : Fin n}
    (hinc : spec.core.tail g = w ∨ spec.core.head g = w)
    (hwS : (spec.scale N hN).coreVertex w ∈ S)
    (hwD : D ((spec.scale N hN).coreVertex w) = 0)
    (hfree : ∀ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN g j) = 0) :
    ∀ k, k ≤ N → spec.sidePoint N hN g w k ∈ S := by
  intro k
  induction k with
  | zero =>
      intro _
      rw [spec.sidePoint_zero N hN hunit g hinc]
      exact hwS
  | succ k ih =>
      intro hk
      have hkN : k < N := by omega
      have hkS := ih (by omega)
      have hzero : D (spec.sidePoint N hN g w k) = 0 := by
        rcases Nat.eq_zero_or_pos k with rfl | h0
        · rw [spec.sidePoint_zero N hN hunit g hinc]
          exact hwD
        · exact spec.sidePoint_apply_eq_zero_of_chipless N hN g w hfree h0 hkN
      exact Gonality.mem_of_apply_le_zero hS hkS (le_of_eq hzero)
        (spec.num_edges_sidePoint_succ_pos N hN hunit g w hkN)

/-! ## Closure of the core part of a legal set -/

/-- **Closure of the core part of a legal set.**  Write
`U = {v : Fin n | coreVertex v ∈ S}` for the core part of a legal set.  If
`w ∈ U` is chipless and `g` is a chipless slot at `w`, then *both* endpoints of
`g` lie in `U`.  This is the input for showing that `U` is closed in the core
with the chip-carrying slots deleted. -/
theorem core_closure (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph}
    {S : Finset (spec.scale N hN).graph.V}
    (hS : legal_set (spec.scale N hN).graph D S) (g : Fin p) {w : Fin n}
    (hinc : spec.core.tail g = w ∨ spec.core.head g = w)
    (hwS : (spec.scale N hN).coreVertex w ∈ S)
    (hwD : D ((spec.scale N hN).coreVertex w) = 0)
    (hfree : ∀ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN g j) = 0) :
    (spec.scale N hN).coreVertex (spec.core.tail g) ∈ S ∧
      (spec.scale N hN).coreVertex (spec.core.head g) ∈ S := by
  have hfar := spec.propagate_chipless N hN hunit hS g hinc hwS hwD hfree N le_rfl
  by_cases hc : spec.core.tail g = w
  · rw [spec.sidePoint_last_of_tail N hN hunit g hc] at hfar
    exact ⟨hc ▸ hwS, hfar⟩
  · rw [spec.sidePoint_last_of_ne N hN g hc] at hfar
    exact ⟨hfar, (hinc.resolve_left hc) ▸ hwS⟩

/-! ## A slot with one chip, from the near end -/

/-- **A one-chip slot, the near half.**  With at most one interior chip on `g` and
that chip at offset `t` from the chipless core vertex `w ∈ S`, propagation runs
from `w` up to and including the chip: `sidePoint g w k ∈ S` for every
`k ≤ t`. -/
theorem propagate_upto_chip (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} (hD : effective D)
    {S : Finset (spec.scale N hN).graph.V}
    (hS : legal_set (spec.scale N hN).graph D S) (g : Fin p) {w : Fin n}
    (hinc : spec.core.tail g = w ∨ spec.core.head g = w)
    (hwS : (spec.scale N hN).coreVertex w ∈ S)
    (hwD : D ((spec.scale N hN).coreVertex w) = 0)
    (hchip : ∑ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN g j) ≤ 1)
    {t : ℕ} (ht0 : 0 < t) (htN : t < N)
    (hDt : 1 ≤ D (spec.sidePoint N hN g w t)) :
    ∀ k, k ≤ t → spec.sidePoint N hN g w k ∈ S := by
  intro k
  induction k with
  | zero =>
      intro _
      rw [spec.sidePoint_zero N hN hunit g hinc]
      exact hwS
  | succ k ih =>
      intro hk
      have hkN : k < N := by omega
      have hkS := ih (by omega)
      have hzero : D (spec.sidePoint N hN g w k) = 0 := by
        rcases Nat.eq_zero_or_pos k with rfl | h0
        · rw [spec.sidePoint_zero N hN hunit g hinc]
          exact hwD
        · exact spec.sidePoint_apply_eq_zero_of_chip N hN hD g w hchip ht0 htN hDt
            h0 hkN (by omega)
      exact Gonality.mem_of_apply_le_zero hS hkS (le_of_eq hzero)
        (spec.num_edges_sidePoint_succ_pos N hN hunit g w hkN)

/-- **A one-chip slot, the far half.**  With at most one interior chip on `g`, at
offset `t` from `w`, propagation stops there unless the far endpoint of `g` is
itself in `S`: if it is not, then no offset beyond `t` meets `S`.

Together with `propagate_upto_chip`: if `w` is a chipless member of `S` and the
far endpoint is not in `S`, then `S` meets the interior of `g` exactly in the
offsets `1, …, t` from `w`.  The proof is the maximal-run argument of
`slotInterior_disjoint_of_chip_le_one`: the maximal run of `S` above the chip
ends at some `r`, its cap `sidePoint g w (r + 1)` is outside `S`, and
`D (sidePoint g w r) = 0` because the slot's only chip is at `t < r`, so
`outdeg_S (sidePoint g w r) ≥ 1 > 0 = D` is illegal. -/
theorem not_mem_beyond_chip (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} (hD : effective D)
    {S : Finset (spec.scale N hN).graph.V}
    (hS : legal_set (spec.scale N hN).graph D S) (g : Fin p) {w : Fin n}
    (hchip : ∑ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN g j) ≤ 1)
    {t : ℕ} (ht0 : 0 < t) (htN : t < N)
    (hDt : 1 ≤ D (spec.sidePoint N hN g w t))
    (hfar : spec.sidePoint N hN g w N ∉ S)
    {k : ℕ} (hkt : t < k) (hkN : k < N) :
    spec.sidePoint N hN g w k ∉ S := by
  classical
  intro hkS
  -- The upper end of the maximal run of `S` through offset `k`.
  set C : Finset ℕ := (Finset.Icc k (N - 1)).filter
    (fun i => ∀ j ∈ Finset.Icc k i, spec.sidePoint N hN g w j ∈ S) with hCdef
  have hkC : k ∈ C := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, fun j hj => ?_⟩
    rw [Finset.mem_Icc] at hj
    rw [show j = k by omega]
    exact hkS
  have hCne : C.Nonempty := ⟨k, hkC⟩
  set r := C.max' hCne with hrdef
  have hrC : r ∈ C := C.max'_mem hCne
  have hrIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hrC).1
  have hrS : ∀ j, k ≤ j → j ≤ r → spec.sidePoint N hN g w j ∈ S := by
    intro j h1 h2
    exact (Finset.mem_filter.mp hrC).2 j (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  -- Its cap is outside `S`: either it is the far endpoint, or maximality bites.
  have hhi : spec.sidePoint N hN g w (r + 1) ∉ S := by
    rcases Nat.eq_or_lt_of_le hrIcc.2 with h | h
    · rw [show r + 1 = N by omega]
      exact hfar
    · intro hc
      have hmemC : r + 1 ∈ C := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
          fun j hj => ?_⟩
        rw [Finset.mem_Icc] at hj
        rcases Nat.eq_or_lt_of_le hj.2 with hj2 | hj2
        · rw [hj2]; exact hc
        · exact hrS j hj.1 (by omega)
      have := C.le_max' _ hmemC
      omega
  -- But the run's top offset is chipless, so it cannot afford the escaping edge.
  have hrN : r < N := by omega
  have hzero : D (spec.sidePoint N hN g w r) = 0 :=
    spec.sidePoint_apply_eq_zero_of_chip N hN hD g w hchip ht0 htN hDt
      (by omega) hrN (by omega)
  have hlegal := hS _ (hrS r (by omega) le_rfl)
  have hbound := Gonality.num_edges_le_outdeg_S S (spec.sidePoint N hN g w r) hhi
  have hcast : (1 : ℤ) ≤ (num_edges (spec.scale N hN).graph
      (spec.sidePoint N hN g w r) (spec.sidePoint N hN g w (r + 1)) : ℤ) := by
    exact_mod_cast spec.num_edges_sidePoint_succ_pos N hN hunit g w hrN
  omega

/-! ## A one-chip slot with both endpoints in the set -/

/-- **A one-chip slot with both endpoints in the set.**  If both endpoints of `g`
are chipless members of the legal set `S` and the interior of `g` carries at
most one chip, then the whole of `g` lies in `S`: propagate from each end up to
the chip, and the two runs cover every offset (the two ends included, at `k = 0`
and `k = N`).

So a single chip on a slot only delays propagation: a chip at offset `t` stops
propagation short of the far vertex, but once the far vertex has been reached by
another route the slot is filled from both ends. -/
theorem propagate_both_ends (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} (hD : effective D)
    {S : Finset (spec.scale N hN).graph.V}
    (hS : legal_set (spec.scale N hN).graph D S) (g : Fin p)
    (htailS : (spec.scale N hN).coreVertex (spec.core.tail g) ∈ S)
    (htailD : D ((spec.scale N hN).coreVertex (spec.core.tail g)) = 0)
    (hheadS : (spec.scale N hN).coreVertex (spec.core.head g) ∈ S)
    (hheadD : D ((spec.scale N hN).coreVertex (spec.core.head g)) = 0)
    (hchip : ∑ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN g j) ≤ 1)
    {k : ℕ} (hkN : k ≤ N) :
    spec.slotPoint N hN g k ∈ S := by
  classical
  by_cases hfree : ∀ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN g j) = 0
  · -- No chip at all: one run from the tail suffices.
    have h := spec.propagate_chipless N hN hunit hS g (w := spec.core.tail g)
      (Or.inl rfl) htailS htailD hfree k (by omega)
    rwa [spec.sidePoint_tail N hN g k] at h
  · -- One chip, at offset `t` from the tail and `N - t` from the head.
    push Not at hfree
    obtain ⟨t, htIoo, htne⟩ := hfree
    obtain ⟨ht0, htN⟩ := Finset.mem_Ioo.mp htIoo
    have hDt : 1 ≤ D (spec.slotPoint N hN g t) := by
      have := hD (spec.slotPoint N hN g t)
      omega
    by_cases hkt : k ≤ t
    · have h := spec.propagate_upto_chip N hN hunit hD hS g (w := spec.core.tail g)
        (Or.inl rfl) htailS htailD hchip ht0 htN
        (by rw [spec.sidePoint_tail N hN g t]; exact hDt) k hkt
      rwa [spec.sidePoint_tail N hN g k] at h
    · have hhead : 1 ≤ D (spec.sidePoint N hN g (spec.core.head g) (N - t)) := by
        rw [spec.sidePoint_head N hN g (N - t), show N - (N - t) = t by omega]
        exact hDt
      have h := spec.propagate_upto_chip N hN hunit hD hS g (w := spec.core.head g)
        (Or.inr rfl) hheadS hheadD hchip (t := N - t) (by omega) (by omega) hhead
        (N - k) (by omega)
      rwa [spec.sidePoint_head N hN g (N - k), show N - (N - k) = k by omega] at h

end Spec

end SubdivisionGraph

end Utilities.Certificate

