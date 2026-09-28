import GenusSixOddDescent.Hole
import Utilities.Subdivision.SlotPropagation
import Utilities.Subdivision.CoreCutsAndFlats

/-!
# Lemma H4: the two hole moves are the *only* moves

Fix a unit presentation `spec`, a scale `N`, a slot `f`, a chip offset `t` and an
index `j` with `1 ≤ j`, `2 * j ≤ t` and `t - j < N` (`t < N` would be too
strong, because `holeDiv` reads offsets from `spec.core.tail f` and a
head-oriented state has `t > N`; `t - j < N` says the far hole chip is interior,
and `2 * j ≤ t` then gives `j ≤ t - j < N`).  Let `R` be a *rest* divisor which

* is effective,
* is chipless on the core and on the whole of `f` (so the two chips of
  `holeDiv f t R j` are the only chips of the slot `f`),
* carries at most one chip on the interior of every slot, and
* is chipless outside a set `E ∋ f` of slots whose complement `G − E` is
  connected.

Then the **only** proper non-empty legal sets for `D = holeDiv f t R j` are the
two hole sets: `backSet f t j` always, and `fwdSet f t j` exactly when
`2 * (j + 1) ≤ t`.  Legality of the two survivors, and their targets, are H2/H1
(`GenusSixOddDescent/Hole.lean`); this module is the converse.

## The proof

The proof has three steps.  With `U := {u : coreVertex u ∈ T}`:

* **Step 1** (`core_dichotomy`): `D` vanishes on the core, so every `u ∈ U` has
  `outdeg_T (coreVertex u) = 0` and `core_closure` pushes `U` across every
  chipless slot — i.e. across every slot outside `E`.  `ConnectedOff E` then
  forces `U = ∅` or `U = univ`.
* **Step 2** (`step_two`, `U = ∅`): `slotInterior_disjoint_of_chip_le_one`
  empties every slot but `f`, and the maximal run of `T` through *any* member is
  pinned to `[a_j, a_{t-j}]` by `edge_confinement` (chip sum `≥ 2`) together
  with the two end conditions (`outdeg ≥ 1` needs a chip).  So
  `T = backSet f t j`.
* **Step 3** (`step_three`, `U = univ`): every slot `g ≠ f` fills by
  `propagate_both_ends`, and the maximal run of `Tᶜ` through any member of
  `int(f) ∖ T` is pinned to `[a_{j+1}, a_{t-j-1}]` by the same end condition
  applied to its two `T`-neighbours.  So `T = fwdSet f t j`, and the gap
  `int(f) ∖ T` is non-empty only when `2 * (j + 1) ≤ t`.

The slot and propagation lemmas are those of
`Utilities/Subdivision/SlotIntervalFiring.lean` and
`Utilities/Subdivision/SlotPropagation.lean`.  Two features of the argument are
worth recording:

* **No propagation along `f`.**  A propagation lemma such as
  `propagate_upto_chip` assumes at most one chip on the interior of the slot,
  which is exactly what `f` violates.  So Step 3 never touches `f` with a
  propagation lemma: the maximal run of `Tᶜ` and the two chipped `T`-neighbours
  capping it do all the work.  `propagate_both_ends` is used only on the slots
  `g ≠ f`, where the one-chip hypothesis is genuine.
* **The run construction is applied at every member, not at one.**  Running the
  same argument at each member of `T ∩ int(f)` (resp. of `int(f) ∖ T`) pins each
  of them into `[j, t-j]` (resp. `[j+1, t-j-1]`), so no separate argument is
  needed to exclude a second run.

Everything is stated at the abstract `Spec`; no concrete subdivided graph is
ever unfolded.
-/

namespace Utilities.Certificate

open Finset

namespace SubdivisionGraph

namespace Spec

variable {n p : ℕ} (spec : Spec n p) (N : ℕ) (hN : 0 < N)

/-! ## Evaluation of a chip at a slot point

Outgoing-degree and legal-set membership bounds are shared in the generic
legal-firing module. The helper below handles slot-coordinate evaluation. -/

/-- A chip parked at offset `a` is seen at offset `b` exactly when `a = b`. -/
private theorem one_chip_slotPoint (hunit : spec.IsUnit) (g : Fin p) {a b : ℕ}
    (ha : a ≤ N) (hb : b ≤ N) :
    (one_chip (spec.slotPoint N hN g a) : CFDiv (spec.scale N hN).graph)
        (spec.slotPoint N hN g b) = if b = a then 1 else 0 := by
  by_cases h : b = a
  · rw [if_pos h, h]
    exact one_chip_apply_v _
  · rw [if_neg h]
    exact one_chip_apply_other' _ _ (spec.slotPoint_ne N hN hunit g hb ha h)

/-! ## The fine vertices: core points and interior slot points -/

/-- **Distinct slots have disjoint interiors.** -/
private theorem slotPoint_ne_of_slot_ne (hunit : spec.IsUnit) {g g' : Fin p}
    (hgg : g ≠ g') {i i' : ℕ} (hi0 : 0 < i) (hiN : i < N) (hi0' : 0 < i')
    (hiN' : i' < N) :
    spec.slotPoint N hN g i ≠ spec.slotPoint N hN g' i' := by
  obtain ⟨o, ho⟩ := spec.exists_interiorVertex_eq_slotPoint N hN hunit g hi0 hiN
  obtain ⟨o', ho'⟩ := spec.exists_interiorVertex_eq_slotPoint N hN hunit g' hi0' hiN'
  rw [ho, ho']
  intro hc
  simp only [interiorVertex, Sum.inr.injEq, Sigma.mk.injEq] at hc
  exact hgg hc.1

/-! ## The values of a hole divisor -/

section Values

variable (f : Fin p) {t j : ℕ} {R : CFDiv (spec.scale N hN).graph}

/-- **`D` vanishes on the core** (Lemma H3 plus `R`'s vanishing there). -/
private theorem holeDiv_core_eq_zero (hunit : spec.IsUnit) (hj : 1 ≤ j)
    (hjt : 2 * j ≤ t) (htj : t - j < N)
    (hRcore : ∀ u : Fin n, R ((spec.scale N hN).coreVertex u) = 0) (u : Fin n) :
    spec.holeDiv N hN f t R j ((spec.scale N hN).coreVertex u) = 0 := by
  rw [spec.holeDiv_coreVertex N hN hunit f hj hjt htj R u]
  exact hRcore u

/-- **`D` on the slot `f`**: exactly the two hole chips, at offsets `j` and
`t - j` (a doubled chip when `2 * j = t`).  The formula is valid at the two core
endpoints as well, where both indicators vanish.  (Pure evaluation, so `1 ≤ j`
is not needed: `2 * j ≤ t` and `t - j < N` already put both offsets in
`[0, N]`.) -/
private theorem holeDiv_slotPoint_self (hunit : spec.IsUnit)
    (hjt : 2 * j ≤ t) (htj : t - j < N)
    (hRf : ∀ i, R (spec.slotPoint N hN f i) = 0) (i : ℕ) (hi : i ≤ N) :
    spec.holeDiv N hN f t R j (spec.slotPoint N hN f i)
      = (if i = j then 1 else 0) + (if i = t - j then 1 else 0) := by
  by_cases hjN : j ≤ N
  · by_cases htjN : t - j ≤ N
    · simp only [holeDiv, Pi.add_apply,
        spec.one_chip_slotPoint N hN hunit f hjN hi,
        spec.one_chip_slotPoint N hN hunit f htjN hi, hRf i]
      ring
    · omega
  · omega

/-- **`D` off the slot `f`** is the rest divisor. -/
private theorem holeDiv_slotPoint_other (hunit : spec.IsUnit) (hj : 1 ≤ j)
    (hjt : 2 * j ≤ t) (htj : t - j < N) {g : Fin p} (hgf : g ≠ f) {i : ℕ}
    (hi0 : 0 < i) (hiN : i < N) :
    spec.holeDiv N hN f t R j (spec.slotPoint N hN g i)
      = R (spec.slotPoint N hN g i) := by
  simp only [holeDiv, Pi.add_apply]
  rw [one_chip_apply_other' _ _
      (spec.slotPoint_ne_of_slot_ne N hN hunit hgf hi0 hiN (by omega) (by omega)),
    one_chip_apply_other' _ _
      (spec.slotPoint_ne_of_slot_ne N hN hunit hgf hi0 hiN (by omega) (by omega))]
  ring

end Values

/-! ## The maximal run of a set inside one slot

A `B.min'` / `C.max'` construction, stated once so that both Step 2 (run of `T`)
and Step 3 (run of `Tᶜ`) can use it. -/

/-- **The maximal run through a member.**  If neither core endpoint of `g` lies
in `T` and the interior point at offset `i` does, then `i` lies in a maximal run
`[a, r]` of interior offsets whose points lie in `T`, capped at both ends by
offsets whose points do not. -/
private theorem exists_maximal_run (g : Fin p)
    {T : Finset (spec.scale N hN).graph.V}
    (h0T : spec.slotPoint N hN g 0 ∉ T) (hNT : spec.slotPoint N hN g N ∉ T)
    {i : ℕ} (hi0 : 0 < i) (hiN : i < N) (hmem : spec.slotPoint N hN g i ∈ T) :
    ∃ a r : ℕ, 1 ≤ a ∧ a ≤ i ∧ i ≤ r ∧ r < N ∧
      spec.slotPoint N hN g (a - 1) ∉ T ∧ spec.slotPoint N hN g (r + 1) ∉ T ∧
      ∀ k, a ≤ k → k ≤ r → spec.slotPoint N hN g k ∈ T := by
  classical
  -- The lower end of the maximal run of `T` through offset `i`.
  set B : Finset ℕ := (Finset.Icc 1 i).filter
    (fun b => ∀ k ∈ Finset.Icc b i, spec.slotPoint N hN g k ∈ T) with hBdef
  have hiB : i ∈ B := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hi0, le_rfl⟩, fun k hk => ?_⟩
    rw [Finset.mem_Icc] at hk
    rw [show k = i by omega]
    exact hmem
  have hBne : B.Nonempty := ⟨i, hiB⟩
  set a := B.min' hBne with hadef
  have haB : a ∈ B := B.min'_mem hBne
  have haIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp haB).1
  have haS : ∀ k, a ≤ k → k ≤ i → spec.slotPoint N hN g k ∈ T := by
    intro k h1 h2
    exact (Finset.mem_filter.mp haB).2 k (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  have hlo : spec.slotPoint N hN g (a - 1) ∉ T := by
    rcases Nat.eq_or_lt_of_le haIcc.1 with h | h
    · rw [show a - 1 = 0 by omega]
      exact h0T
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
  set C : Finset ℕ := (Finset.Icc i (N - 1)).filter
    (fun c => ∀ k ∈ Finset.Icc i c, spec.slotPoint N hN g k ∈ T) with hCdef
  have hiC : i ∈ C := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, fun k hk => ?_⟩
    rw [Finset.mem_Icc] at hk
    rw [show k = i by omega]
    exact hmem
  have hCne : C.Nonempty := ⟨i, hiC⟩
  set r := C.max' hCne with hrdef
  have hrC : r ∈ C := C.max'_mem hCne
  have hrIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hrC).1
  have hrS : ∀ k, i ≤ k → k ≤ r → spec.slotPoint N hN g k ∈ T := by
    intro k h1 h2
    exact (Finset.mem_filter.mp hrC).2 k (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  have hhi : spec.slotPoint N hN g (r + 1) ∉ T := by
    rcases Nat.eq_or_lt_of_le hrIcc.2 with h | h
    · rw [show r + 1 = N by omega]
      exact hNT
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
  refine ⟨a, r, haIcc.1, haIcc.2, hrIcc.1, by omega, hlo, hhi, fun k h1 h2 => ?_⟩
  by_cases hki : k ≤ i
  · exact haS k h1 hki
  · exact hrS k (by omega) h2

/-- Consecutive slot points are adjacent, read downwards. -/
private theorem num_edges_slotPoint_pred_pos (hunit : spec.IsUnit) (g : Fin p)
    {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    0 < num_edges (spec.scale N hN).graph (spec.slotPoint N hN g k)
      (spec.slotPoint N hN g (k - 1)) := by
  have h := spec.num_edges_slotPoint_succ_pos N hN hunit g (t := k - 1) (by omega)
  rw [show k - 1 + 1 = k by omega, num_edges_symmetric] at h
  exact h

/-- **A chip is needed to feed an escaping edge.**  A member of a legal set with
a fine neighbour outside the set carries at least one chip. -/
private theorem one_le_of_escape {D : CFDiv (spec.scale N hN).graph}
    {T : Finset (spec.scale N hN).graph.V}
    (hT : legal_set (spec.scale N hN).graph D T)
    {x y : (spec.scale N hN).graph.V} (hx : x ∈ T) (hy : y ∉ T)
    (hadj : 0 < num_edges (spec.scale N hN).graph x y) : 1 ≤ D x := by
  have hbound := Gonality.num_edges_le_outdeg_S T x hy
  have hlegal := hT x hx
  have hcast : (1 : ℤ) ≤ (num_edges (spec.scale N hN).graph x y : ℤ) := by
    exact_mod_cast hadj
  omega

/-! ## The standing hypotheses of Lemma H4 -/

section H4

variable (hunit : spec.IsUnit) (f : Fin p) {t j : ℕ}
  {R : CFDiv (spec.scale N hN).graph} {E : Finset (Fin p)}
  {T : Finset (spec.scale N hN).graph.V}

include hunit

/-- **Step 1.**  The core part of a proper legal set for a hole divisor is
everything or nothing: `D` is chipless on the core, so the core part is closed
under every chipless slot — in particular under every slot outside `E` — and
`G − E` is connected. -/
private theorem core_dichotomy (hj : 1 ≤ j) (hjt : 2 * j ≤ t) (htj : t - j < N)
    (hRcore : ∀ u : Fin n, R ((spec.scale N hN).coreVertex u) = 0)
    (hfE : f ∈ E)
    (hout : ∀ g : Fin p, g ∉ E → ∀ i ∈ Finset.Ioo 0 N,
      R (spec.slotPoint N hN g i) = 0)
    (hconn : spec.core.ConnectedOff E)
    (hT : legal_set (spec.scale N hN).graph (spec.holeDiv N hN f t R j) T) :
    (∀ u : Fin n, (spec.scale N hN).coreVertex u ∉ T) ∨
      (∀ u : Fin n, (spec.scale N hN).coreVertex u ∈ T) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨u, hu⟩, ⟨w, hw⟩⟩ := hcon
  -- The core part of `T`, as a vertex set of the core graph.
  set U : Finset (Fin n) :=
    Finset.univ.filter (fun v => (spec.scale N hN).coreVertex v ∈ T) with hUdef
  have hmemU : ∀ v : Fin n, v ∈ U ↔ (spec.scale N hN).coreVertex v ∈ T := by
    intro v
    simp [hUdef]
  -- `U` is non-trivial, so some slot outside `E` crosses it.
  obtain ⟨e, heE, hcross⟩ :=
    hconn U ⟨u, w, (hmemU u).mpr hu, fun hc => hw ((hmemU w).mp hc)⟩
  have hef : e ≠ f := fun hc => heE (hc ▸ hfE)
  -- That slot is chipless for `D`, so propagation carries `U` across it.
  have hfree : ∀ i ∈ Finset.Ioo 0 N,
      spec.holeDiv N hN f t R j (spec.slotPoint N hN e i) = 0 := by
    intro i hi
    have hi' := Finset.mem_Ioo.mp hi
    rw [spec.holeDiv_slotPoint_other N hN f hunit hj hjt htj hef hi'.1 hi'.2]
    exact hout e heE i hi
  have hzero := spec.holeDiv_core_eq_zero N hN f hunit hj hjt htj hRcore
  rcases hcross with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hcl := spec.core_closure N hN hunit hT e (w := spec.core.tail e)
      (Or.inl rfl) ((hmemU _).mp h1) (hzero _) hfree
    exact h2 ((hmemU _).mpr hcl.2)
  · have hcl := spec.core_closure N hN hunit hT e (w := spec.core.head e)
      (Or.inr rfl) ((hmemU _).mp h1) (hzero _) hfree
    exact h2 ((hmemU _).mpr hcl.1)

/-- **Step 2.**  With no core vertex in `T`, the set is the back-step run. -/
private theorem step_two (hj : 1 ≤ j) (hjt : 2 * j ≤ t) (htj : t - j < N)
    (hReff : effective R)
    (hRf : ∀ i, R (spec.slotPoint N hN f i) = 0)
    (hRchip : ∀ g : Fin p, ∑ i ∈ Finset.Ioo 0 N, R (spec.slotPoint N hN g i) ≤ 1)
    (hT : legal_set (spec.scale N hN).graph (spec.holeDiv N hN f t R j) T)
    (hTne : T ≠ ∅) (hcore : ∀ u : Fin n, (spec.scale N hN).coreVertex u ∉ T) :
    T = spec.backSet N hN f t j := by
  classical
  have hjN : j < N := by omega
  have hjtj : j ≤ t - j := by omega
  have htjN : t - j < N := by omega
  have hDeff : effective (spec.holeDiv N hN f t R j) :=
    spec.effective_holeDiv N hN f t hReff j
  have hDf := spec.holeDiv_slotPoint_self N hN f hunit hjt htj hRf
  -- `slotInterior_disjoint_of_chip_le_one` empties every slot but `f`.
  have hother : ∀ g : Fin p, g ≠ f → ∀ i, 0 < i → i < N →
      spec.slotPoint N hN g i ∉ T := by
    intro g hgf i hi0 hiN
    refine spec.slotInterior_disjoint_of_chip_le_one N hN hunit hDeff hT g ?_
      (hcore _) (hcore _) hi0 hiN
    refine le_trans (le_of_eq (Finset.sum_congr rfl ?_)) (hRchip g)
    intro x hx
    have hx' := Finset.mem_Ioo.mp hx
    exact spec.holeDiv_slotPoint_other N hN f hunit hj hjt htj hgf hx'.1 hx'.2
  -- Neither core endpoint of `f` is in `T`.
  have h0T : spec.slotPoint N hN f 0 ∉ T := by
    rw [spec.slotPoint_zero N hN f]; exact hcore _
  have hNT : spec.slotPoint N hN f N ∉ T := by
    rw [spec.slotPoint_last N hN hunit f]; exact hcore _
  -- **The key.**  The maximal run of `T` through *any* member of `int(f)` is
  -- `[a_j, a_{t-j}]`: it carries chip sum `≥ 2` by `edge_confinement`, hence holds both
  -- hole chips, and each of its two ends must itself carry a chip.
  have hkey : ∀ i, 0 < i → i < N → spec.slotPoint N hN f i ∈ T →
      j ≤ i ∧ i ≤ t - j ∧
        ∀ k, j ≤ k → k ≤ t - j → spec.slotPoint N hN f k ∈ T := by
    intro i hi0 hiN hiT
    obtain ⟨a, r, ha1, hai, hir, hrN, hlo, hhi, hrun⟩ :=
      spec.exists_maximal_run N hN f h0T hNT hi0 hiN hiT
    have har : a ≤ r := le_trans hai hir
    have hconf := spec.edge_confinement N hN hunit hDeff hT f ha1 har hrN hlo hhi hrun
    have hsum : ∑ k ∈ Finset.Icc a r,
          spec.holeDiv N hN f t R j (spec.slotPoint N hN f k)
        = (if j ∈ Finset.Icc a r then (1 : ℤ) else 0)
          + (if t - j ∈ Finset.Icc a r then (1 : ℤ) else 0) := by
      rw [Finset.sum_congr rfl (fun k hk =>
        hDf k (by have := (Finset.mem_Icc.mp hk).2; omega))]
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq']
    rw [hsum] at hconf
    have hjIcc : j ∈ Finset.Icc a r := by
      by_contra hc
      rw [if_neg hc] at hconf
      split_ifs at hconf <;> omega
    have htjIcc : t - j ∈ Finset.Icc a r := by
      by_contra hc
      rw [if_neg hc] at hconf
      split_ifs at hconf
      omega
    have hja := Finset.mem_Icc.mp hjIcc
    have htja := Finset.mem_Icc.mp htjIcc
    -- The two ends of the run feed an escaping edge, so they carry chips.
    have hDa : 1 ≤ spec.holeDiv N hN f t R j (spec.slotPoint N hN f a) :=
      spec.one_le_of_escape N hN hT (hrun a le_rfl har) hlo
        (spec.num_edges_slotPoint_pred_pos N hN hunit f ha1 (by omega))
    have hDr : 1 ≤ spec.holeDiv N hN f t R j (spec.slotPoint N hN f r) :=
      spec.one_le_of_escape N hN hT (hrun r har le_rfl) hhi
        (spec.num_edges_slotPoint_succ_pos N hN hunit f hrN)
    have haj : a = j := by
      rw [hDf a (by omega)] at hDa
      split_ifs at hDa <;> omega
    have hrtj : r = t - j := by
      rw [hDf r (by omega)] at hDr
      split_ifs at hDr <;> omega
    exact ⟨by omega, by omega, fun k hk1 hk2 => hrun k (by omega) (by omega)⟩
  -- A witness inside `int(f)`, and the run through it.
  obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hTne
  obtain ⟨i₀, hi₀0, hi₀N, hi₀T⟩ :
      ∃ i, 0 < i ∧ i < N ∧ spec.slotPoint N hN f i ∈ T := by
    rcases spec.vertex_cases N hN hunit x₀ with ⟨u, rfl⟩ | ⟨g, i, hi0, hiN, rfl⟩
    · exact absurd hx₀ (hcore u)
    · by_cases hgf : g = f
      · subst hgf
        exact ⟨i, hi0, hiN, hx₀⟩
      · exact absurd hx₀ (hother g hgf i hi0 hiN)
  obtain ⟨-, -, hfill⟩ := hkey i₀ hi₀0 hi₀N hi₀T
  simp only [backSet]
  ext x
  constructor
  · intro hxT
    rcases spec.vertex_cases N hN hunit x with ⟨u, rfl⟩ | ⟨g, i, hi0, hiN, rfl⟩
    · exact absurd hxT (hcore u)
    · by_cases hgf : g = f
      · subst hgf
        obtain ⟨h1, h2, -⟩ := hkey i hi0 hiN hxT
        exact (spec.mem_slotInterval_iff N hN g j (t - j) _).mpr ⟨i, h1, h2, rfl⟩
      · exact absurd hxT (hother g hgf i hi0 hiN)
  · intro hxB
    obtain ⟨k, hk1, hk2, rfl⟩ := (spec.mem_slotInterval_iff N hN f j (t - j) x).mp hxB
    exact hfill k hk1 hk2

/-- **Step 3.**  With every core vertex in `T`, the set is the forward-step
complement — and then the gap it omits is non-empty, which is `2 * (j+1) ≤ t`. -/
private theorem step_three (hj : 1 ≤ j) (hjt : 2 * j ≤ t) (htj : t - j < N)
    (hReff : effective R)
    (hRcore : ∀ u : Fin n, R ((spec.scale N hN).coreVertex u) = 0)
    (hRf : ∀ i, R (spec.slotPoint N hN f i) = 0)
    (hRchip : ∀ g : Fin p, ∑ i ∈ Finset.Ioo 0 N, R (spec.slotPoint N hN g i) ≤ 1)
    (hT : legal_set (spec.scale N hN).graph (spec.holeDiv N hN f t R j) T)
    (hTuniv : T ≠ Finset.univ)
    (hcore : ∀ u : Fin n, (spec.scale N hN).coreVertex u ∈ T) :
    2 * (j + 1) ≤ t ∧ T = spec.fwdSet N hN f t j := by
  classical
  have hjN : j < N := by omega
  have hjtj : j ≤ t - j := by omega
  have htjN : t - j < N := by omega
  have hDeff : effective (spec.holeDiv N hN f t R j) :=
    spec.effective_holeDiv N hN f t hReff j
  have hDf := spec.holeDiv_slotPoint_self N hN f hunit hjt htj hRf
  have hzero := spec.holeDiv_core_eq_zero N hN f hunit hj hjt htj hRcore
  -- `propagate_both_ends` fills every slot but `f`, where the one-chip hypothesis holds.
  have hfill : ∀ g : Fin p, g ≠ f → ∀ k, k ≤ N → spec.slotPoint N hN g k ∈ T := by
    intro g hgf k hk
    refine spec.propagate_both_ends N hN hunit hDeff hT g (hcore _) (hzero _)
      (hcore _) (hzero _) ?_ hk
    refine le_trans (le_of_eq (Finset.sum_congr rfl ?_)) (hRchip g)
    intro x hx
    have hx' := Finset.mem_Ioo.mp hx
    exact spec.holeDiv_slotPoint_other N hN f hunit hj hjt htj hgf hx'.1 hx'.2
  -- Both core endpoints of `f` are in `T`.
  have h0T : spec.slotPoint N hN f 0 ∈ T := by
    rw [spec.slotPoint_zero N hN f]; exact hcore _
  have hNT : spec.slotPoint N hN f N ∈ T := by
    rw [spec.slotPoint_last N hN hunit f]; exact hcore _
  -- **The key.**  The maximal run of the *complement* through any hole of `T`
  -- inside `int(f)` is `[a_{j+1}, a_{t-j-1}]`: its two capping neighbours lie in
  -- `T` with a neighbour outside, so each of them carries a chip.
  have hkey : ∀ i, 0 < i → i < N → spec.slotPoint N hN f i ∉ T →
      j + 1 ≤ i ∧ i ≤ t - j - 1 ∧ 2 * (j + 1) ≤ t ∧
        ∀ k, j + 1 ≤ k → k ≤ t - j - 1 → spec.slotPoint N hN f k ∉ T := by
    intro i hi0 hiN hiT
    obtain ⟨a, r, ha1, hai, hir, hrN, hlo, hhi, hrun⟩ :=
      spec.exists_maximal_run N hN f (T := Tᶜ) (by simpa using h0T)
        (by simpa using hNT) hi0 hiN (by simpa using hiT)
    have har : a ≤ r := le_trans hai hir
    have hloT : spec.slotPoint N hN f (a - 1) ∈ T := by simpa using hlo
    have hhiT : spec.slotPoint N hN f (r + 1) ∈ T := by simpa using hhi
    have hrunT : ∀ k, a ≤ k → k ≤ r → spec.slotPoint N hN f k ∉ T := by
      intro k h1 h2
      simpa using hrun k h1 h2
    have hadjlo : 0 < num_edges (spec.scale N hN).graph
        (spec.slotPoint N hN f (a - 1)) (spec.slotPoint N hN f a) := by
      have h := spec.num_edges_slotPoint_succ_pos N hN hunit f (t := a - 1) (by omega)
      rwa [show a - 1 + 1 = a from by omega] at h
    have hadjhi : 0 < num_edges (spec.scale N hN).graph
        (spec.slotPoint N hN f (r + 1)) (spec.slotPoint N hN f r) := by
      simpa using
        spec.num_edges_slotPoint_pred_pos N hN hunit f (k := r + 1) (by omega) (by omega)
    have hDlo : 1 ≤ spec.holeDiv N hN f t R j (spec.slotPoint N hN f (a - 1)) :=
      spec.one_le_of_escape N hN hT hloT (hrunT a le_rfl har) hadjlo
    have hDhi : 1 ≤ spec.holeDiv N hN f t R j (spec.slotPoint N hN f (r + 1)) :=
      spec.one_le_of_escape N hN hT hhiT (hrunT r har le_rfl) hadjhi
    have hcaplo : a - 1 = j ∨ a - 1 = t - j := by
      rw [hDf (a - 1) (by omega)] at hDlo
      split_ifs at hDlo <;> omega
    have hcaphi : r + 1 = j ∨ r + 1 = t - j := by
      rw [hDf (r + 1) (by omega)] at hDhi
      split_ifs at hDhi <;> omega
    -- `a - 1 < r + 1` and `j ≤ t - j` leave only `a - 1 = j`, `r + 1 = t - j`.
    have haj : a = j + 1 := by omega
    have hrj : r = t - j - 1 := by omega
    exact ⟨by omega, by omega, by omega,
      fun k hk1 hk2 => hrunT k (by omega) (by omega)⟩
  -- `T` is proper, and the vertex it misses lies inside `int(f)`.
  obtain ⟨x₀, hx₀⟩ : ∃ x, x ∉ T := by
    by_contra hc
    push Not at hc
    exact hTuniv (Finset.eq_univ_iff_forall.mpr hc)
  obtain ⟨i₀, hi₀0, hi₀N, hi₀T⟩ :
      ∃ i, 0 < i ∧ i < N ∧ spec.slotPoint N hN f i ∉ T := by
    rcases spec.vertex_cases N hN hunit x₀ with ⟨u, rfl⟩ | ⟨g, i, hi0, hiN, rfl⟩
    · exact absurd (hcore u) hx₀
    · by_cases hgf : g = f
      · subst hgf
        exact ⟨i, hi0, hiN, hx₀⟩
      · exact absurd (hfill g hgf i (by omega)) hx₀
  obtain ⟨-, -, hgap, hhole⟩ := hkey i₀ hi₀0 hi₀N hi₀T
  refine ⟨hgap, ?_⟩
  simp only [fwdSet, backSet]
  ext x
  simp only [Finset.mem_compl]
  constructor
  · intro hxT hxI
    obtain ⟨k, hk1, hk2, rfl⟩ :=
      (spec.mem_slotInterval_iff N hN f (j + 1) (t - (j + 1)) x).mp hxI
    exact hhole k hk1 (by omega) hxT
  · intro hxI
    rcases spec.vertex_cases N hN hunit x with ⟨u, rfl⟩ | ⟨g, i, hi0, hiN, rfl⟩
    · exact hcore u
    · by_cases hgf : g = f
      · subst hgf
        by_contra hc
        obtain ⟨h1, h2, -, -⟩ := hkey i hi0 hiN hc
        exact hxI ((spec.mem_slotInterval_iff N hN g (j + 1) (t - (j + 1)) _).mpr
          ⟨i, h1, by omega, rfl⟩)
      · exact hfill g hgf i (by omega)

end H4

/-! ## Lemma H4 -/

/-- **Lemma H4 (hole classification).**

Let `R` be effective, chipless on the core and on the slot `f`, carrying at most
one chip on the interior of each slot and no chip at all outside a slot set
`E ∋ f` with `G − E` connected.  Then for `1 ≤ j`, `2 * j ≤ t` and `t - j < N`
the only proper non-empty legal sets for the hole divisor `holeDiv f t R j` are
the two hole sets of `GenusSixOddDescent/Hole.lean`: the back-step run
`backSet f t j`, and — only when `2 * (j + 1) ≤ t`, i.e. `j < ⌊t/2⌋` — the
forward-step complement `fwdSet f t j`. -/
theorem hole_legal_sets (hunit : spec.IsUnit) (f : Fin p) {t j : ℕ}
    (hj : 1 ≤ j) (hjt : 2 * j ≤ t) (htj : t - j < N)
    {R : CFDiv (spec.scale N hN).graph} (hReff : effective R)
    (hRcore : ∀ u : Fin n, R ((spec.scale N hN).coreVertex u) = 0)
    (hRf : ∀ i, R (spec.slotPoint N hN f i) = 0)
    (hRchip : ∀ g : Fin p, ∑ i ∈ Finset.Ioo 0 N, R (spec.slotPoint N hN g i) ≤ 1)
    {E : Finset (Fin p)} (hfE : f ∈ E)
    (hout : ∀ g : Fin p, g ∉ E → ∀ i ∈ Finset.Ioo 0 N,
      R (spec.slotPoint N hN g i) = 0)
    (hconn : spec.core.ConnectedOff E)
    {T : Finset (spec.scale N hN).graph.V}
    (hT : legal_set (spec.scale N hN).graph (spec.holeDiv N hN f t R j) T)
    (hTne : T ≠ ∅) (hTuniv : T ≠ Finset.univ) :
    T = spec.backSet N hN f t j ∨
      (2 * (j + 1) ≤ t ∧ T = spec.fwdSet N hN f t j) := by
  rcases spec.core_dichotomy N hN hunit f hj hjt htj hRcore hfE hout hconn hT with
    hempty | hfull
  · exact Or.inl (spec.step_two N hN hunit f hj hjt htj hReff hRf hRchip hT
      hTne hempty)
  · exact Or.inr (spec.step_three N hN hunit f hj hjt htj hReff hRcore hRf hRchip
      hT hTuniv hfull)

/-! ## Corollary H4': the degree of a hole divisor in the firing graph -/

/-- **The proper non-empty legal sets of a hole divisor.**  Its cardinality is
the degree of `holeDiv f t R j` in the firing graph of the class. -/
def holeLegalSets (g : Fin p) (t : ℕ) (R : CFDiv (spec.scale N hN).graph) (j : ℕ) :
    Finset (Finset (spec.scale N hN).graph.V) :=
  Finset.univ.filter fun T =>
    legal_set (spec.scale N hN).graph (spec.holeDiv N hN g t R j) T ∧
      T ≠ ∅ ∧ T ≠ Finset.univ

theorem mem_holeLegalSets (g : Fin p) (t : ℕ)
    (R : CFDiv (spec.scale N hN).graph) (j : ℕ)
    (T : Finset (spec.scale N hN).graph.V) :
    T ∈ spec.holeLegalSets N hN g t R j ↔
      legal_set (spec.scale N hN).graph (spec.holeDiv N hN g t R j) T ∧
        T ≠ ∅ ∧ T ≠ Finset.univ := by
  simp [holeLegalSets]

section Degree

variable (hunit : spec.IsUnit) (f : Fin p) {t j : ℕ}
  {R : CFDiv (spec.scale N hN).graph} {E : Finset (Fin p)}

include hunit

/-- A back-step run holds no core vertex (it is a run of *interior* offsets). -/
private theorem coreVertex_not_mem_backSet (hj : 1 ≤ j) (htj : t - j < N) (u : Fin n) :
    (spec.scale N hN).coreVertex u ∉ spec.backSet N hN f t j := by
  simp only [backSet]
  intro hmem
  obtain ⟨k, hk1, hk2, hk3⟩ := (spec.mem_slotInterval_iff N hN f j (t - j) _).mp hmem
  exact spec.coreVertex_ne_slotPoint N hN hunit u f (t := k) (by omega) (by omega)
    hk3.symm

variable (hj : 1 ≤ j) (hjt : 2 * j ≤ t) (htj : t - j < N) (hReff : effective R)
  (hRcore : ∀ u : Fin n, R ((spec.scale N hN).coreVertex u) = 0)
  (hRf : ∀ i, R (spec.slotPoint N hN f i) = 0)
  (hRchip : ∀ g : Fin p, ∑ i ∈ Finset.Ioo 0 N, R (spec.slotPoint N hN g i) ≤ 1)
  (hfE : f ∈ E)
  (hout : ∀ g : Fin p, g ∉ E → ∀ i ∈ Finset.Ioo 0 N,
    R (spec.slotPoint N hN g i) = 0)
  (hconn : spec.core.ConnectedOff E)

include hj hjt htj hReff hRcore hRf hRchip hfE hout hconn

/-- **H4 as an inclusion**: every proper non-empty legal set is one of the two
hole sets. -/
theorem holeLegalSets_subset :
    spec.holeLegalSets N hN f t R j
      ⊆ {spec.backSet N hN f t j, spec.fwdSet N hN f t j} := by
  intro T hTmem
  rw [spec.mem_holeLegalSets N hN f t R j T] at hTmem
  rcases spec.hole_legal_sets N hN hunit f hj hjt htj hReff hRcore hRf hRchip hfE
    hout hconn hTmem.1 hTmem.2.1 hTmem.2.2 with h | ⟨-, h⟩ <;> simp [h]

/-- **Corollary H4' (degree at most two).**  A hole divisor has at most two
proper non-empty legal sets, i.e. degree at most two in the firing graph. -/
theorem hole_degree : (spec.holeLegalSets N hN f t R j).card ≤ 2 := by
  refine le_trans (Finset.card_le_card (spec.holeLegalSets_subset N hN hunit f hj
    hjt htj hReff hRcore hRf hRchip hfE hout hconn)) ?_
  exact le_trans (Finset.card_insert_le _ _) (by simp)

/-- **Corollary H4' (the leaf).**  When `2 * (j + 1) > t` — i.e. at the end
`j = ⌊t/2⌋` of the branch — the back step is the *only* proper non-empty legal
set, so the hole divisor is a leaf of the firing graph. -/
theorem hole_degree_leaf (hleaf : t < 2 * (j + 1)) :
    spec.holeLegalSets N hN f t R j = {spec.backSet N hN f t j} := by
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun T hTmem => ?_⟩
  · rw [spec.mem_holeLegalSets N hN f t R j _]
    refine ⟨spec.legal_backSet N hN hunit f hj hjt htj hReff, ?_, ?_⟩
    · exact Finset.ne_empty_of_mem (a := spec.slotPoint N hN f j)
        ((spec.mem_slotInterval_iff N hN f j (t - j) _).mpr ⟨j, le_rfl, by omega, rfl⟩)
    · intro hc
      have hnot := spec.coreVertex_not_mem_backSet N hN hunit f hj htj
        ⟨0, spec.core_nonempty⟩
      rw [hc] at hnot
      exact hnot (Finset.mem_univ _)
  · rw [spec.mem_holeLegalSets N hN f t R j T] at hTmem
    rcases spec.hole_legal_sets N hN hunit f hj hjt htj hReff hRcore hRf hRchip hfE
      hout hconn hTmem.1 hTmem.2.1 hTmem.2.2 with h | ⟨hge, -⟩
    · exact h
    · omega

/-- **Corollary H4' (the interior of the branch).**  When `2 * (j + 1) ≤ t` —
i.e. for `1 ≤ j < ⌊t/2⌋` — the two hole sets are *both* legal and distinct, so
the hole divisor has degree exactly two. -/
theorem hole_degree_two (hfwd : 2 * (j + 1) ≤ t) :
    spec.holeLegalSets N hN f t R j
      = {spec.backSet N hN f t j, spec.fwdSet N hN f t j} := by
  have hcoreF : ∀ u : Fin n,
      (spec.scale N hN).coreVertex u ∈ spec.fwdSet N hN f t j := by
    intro u
    simp only [fwdSet, Finset.mem_compl]
    -- at index `j + 1`, so the interiority hypothesis is `t - (j + 1) < N`
    exact spec.coreVertex_not_mem_backSet N hN hunit f (by omega) (by omega) u
  have hgapF : spec.slotPoint N hN f (j + 1) ∉ spec.fwdSet N hN f t j := by
    simp only [fwdSet, Finset.mem_compl, not_not, backSet]
    exact (spec.mem_slotInterval_iff N hN f (j + 1) (t - (j + 1)) _).mpr
      ⟨j + 1, le_rfl, by omega, rfl⟩
  refine Finset.Subset.antisymm (spec.holeLegalSets_subset N hN hunit f hj hjt htj
    hReff hRcore hRf hRchip hfE hout hconn) ?_
  intro T hTmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hTmem
  rw [spec.mem_holeLegalSets N hN f t R j T]
  rcases hTmem with rfl | rfl
  · refine ⟨spec.legal_backSet N hN hunit f hj hjt htj hReff, ?_, ?_⟩
    · exact Finset.ne_empty_of_mem (a := spec.slotPoint N hN f j)
        ((spec.mem_slotInterval_iff N hN f j (t - j) _).mpr ⟨j, le_rfl, by omega, rfl⟩)
    · intro hc
      have hnot := spec.coreVertex_not_mem_backSet N hN hunit f hj htj
        ⟨0, spec.core_nonempty⟩
      rw [hc] at hnot
      exact hnot (Finset.mem_univ _)
  · refine ⟨spec.legal_fwdSet N hN hunit f hfwd htj hReff, ?_, ?_⟩
    · exact Finset.ne_empty_of_mem (hcoreF ⟨0, spec.core_nonempty⟩)
    · intro hc
      rw [hc] at hgapF
      exact hgapF (Finset.mem_univ _)

end Degree

end Spec

end SubdivisionGraph

end Utilities.Certificate
