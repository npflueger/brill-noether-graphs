import Utilities.Subdivision.SlotIntervalFiring
import Utilities.Gonality.LegalFiringChain

/-!
# The hole branch at a general scale: the two moves and their bookkeeping

A state carries one chip at a core vertex and one chip on each of three slots.
When the core chip sits at an endpoint of one of these slots `f`, the two chips
form a pair on the closed slot `f`, and legal firings move the pair
symmetrically along `f`.  This module sets up the resulting **hole branch**
and proves three lemmas about it, labelled **H1** (the forward step), **H2**
(the back step) and **H3** (the bookkeeping);
`GenusSixOddDescent/HoleClass.lean` adds **H4**, which says the two steps are
the only moves.  Everything is stated at the abstract `Spec` and for the
**tail** orientation of the slot only.  (A state at the head of the slot is
handled by a change of index, explained below; nothing here needs the head
orientation.)

Fix a unit presentation `spec`, a scale `N`, a slot `f`, and read offsets from
the tail of `f`, writing `a_j` for `spec.slotPoint N hN f j`, so that
`a_0 = coreVertex (tail f)` and `a_N = coreVertex (head f)`.  For a *rest*
divisor `R` (in the application, the two remaining chips `x_k + x_l` of the
state; here it is left completely abstract) and a chip offset `t` the
**hole divisors** are

```
holeDiv f t R j = a_j + a_{t-j} + R          (0 ≤ 2 * j ≤ t)
```

with `holeDiv f t R 0 = q + a_t + R` the state itself.  The two moves are firing

```
backSet f t j = slotInterval f j (t - j)     (the run `[a_j, a_{t-j}]`)
fwdSet  f t j = (backSet f t (j + 1))ᶜ
```

and they step `j ↦ j - 1` and `j ↦ j + 1` respectively.

## What is here

* `setFiring_slotInterval` — the general geometric identity behind both moves:
  firing a run `[a_s, a_{t'}]` of interior slot points moves one chip off each
  end of the run onto the two neighbours just outside it,
  `D ↦ D - a_s - a_{t'} + a_{s-1} + a_{t'+1}`.  The degenerate case `s = t'` is
  covered by the *same* formula, which then reads `D - 2 a_s + a_{s-1} + a_{s+1}`.
* `legal_backSet` / `setFiring_backSet` — **Lemma H2**.  Legality is the
  interval-firing lemma `interval_firing`
  (`Utilities/Subdivision/SlotIntervalFiring.lean`), the target is
  `setFiring_slotInterval`.
* `legal_fwdSet` / `setFiring_fwdSet` — **Lemma H1**, obtained from H2 at `j + 1`
  by reversibility (`Utilities.Gonality.legalSet_compl_setFiring` and
  `set_firing_compl_set_firing`); `legal_fwdSet'` / `setFiring_fwdSet'` are the
  same statements under the sharp hypothesis `t - (j + 1) < N`.
* `deg_holeDiv`, `effective_holeDiv`, `holeDiv_coreVertex`,
  `offsetSum_holeDiv` — **Lemma H3**.

## Hypotheses on `R`

None beyond `effective R` (and even that only where effectivity or legality is
asserted).  In the application `R = x_k + x_l` lies off the slot `f`, but no
statement below needs it: the hole pair sits at offsets `j` and `t - j`, both
*interior* whenever `1 ≤ j`, `2 * j ≤ t` and `t - j < N`, and every claim is an identity
relating `holeDiv f t R j` to `R` rather than an absolute value.  In particular
`holeDiv_coreVertex` says the hole pair contributes **no** core chip, not that
the result vanishes.

## The interiority hypothesis: `t - j < N`, not `t < N`

`holeDiv` reads offsets from `spec.core.tail f`, an orientation the caller does
not get to choose: a state sitting at the *head* of `f` with its `f`-chip at
offset `t'` from that head is `holeDiv f (2 * N - t') R (N - t')`, whose first
index `t = 2 * N - t'` exceeds `N`.  So `t < N` is the wrong hypothesis.  What
the proofs below actually use is

* `t - j < N` — the *far* hole chip `a_{t-j}` is interior, and
* `j ≤ t - j`, i.e. `2 * j ≤ t`, which then gives `j < N` for free.

Both are recorded as `htj : t - j < N` together with the existing `2 * j ≤ t`.
At `j = 0` the two agree (`t - 0 < N` is `t < N`), so nothing is lost at the
tail-hub state; at the head-hub state the failing hypothesis is `t - j < N`
(there `t - j = N`, the head core vertex), exactly mirroring the failure of
`1 ≤ j` at the tail-hub state.  The forward move is the one move a hub state
still has, so `legal_fwdSet'`/`setFiring_fwdSet'` are stated under the strictly
weaker `t - (j + 1) < N`, which both hub states satisfy; the unprimed
`legal_fwdSet`/`setFiring_fwdSet` keep the uniform hypothesis `t - j < N`.

Everything is stated at the abstract `Spec`; no concrete subdivided graph is
ever unfolded.
-/

namespace Utilities.Certificate

open Finset

namespace SubdivisionGraph

namespace Spec

variable {n p : ℕ} (spec : Spec n p) (N : ℕ) (hN : 0 < N)

/-! ## Auxiliary evaluations of `one_chip` and `num_edges` at slot points -/

/-- A chip parked at offset `a` is seen at offset `b` exactly when `a = b`. -/
private theorem one_chip_slot (hunit : spec.IsUnit) (g : Fin p) {a b : ℕ}
    (ha : a ≤ N) (hb : b ≤ N) :
    (one_chip (spec.slotPoint N hN g a) : CFDiv (spec.scale N hN).graph)
        (spec.slotPoint N hN g b) = if b = a then 1 else 0 := by
  by_cases h : b = a
  · rw [if_pos h, h]
    exact one_chip_apply_v _
  · rw [if_neg h]
    exact one_chip_apply_other' _ _ (spec.slotPoint_ne N hN hunit g hb ha h)

/-- Two slot points at non-consecutive offsets are non-adjacent. -/
private theorem num_edges_slotPoint_eq_zero (hunit : spec.IsUnit) (g : Fin p)
    {a b : ℕ} (ha : a ≤ N) (hb0 : 0 < b) (hbN : b < N) (h1 : a ≠ b - 1)
    (h2 : a ≠ b + 1) :
    num_edges (spec.scale N hN).graph (spec.slotPoint N hN g a)
      (spec.slotPoint N hN g b) = 0 := by
  by_contra hne
  have hpos : 0 < num_edges (spec.scale N hN).graph (spec.slotPoint N hN g b)
      (spec.slotPoint N hN g a) := by
    rw [num_edges_symmetric]
    omega
  rcases (spec.slotPoint_adj_iff N hN hunit g hb0 hbN _).mp hpos with h | h
  · exact spec.slotPoint_ne N hN hunit g ha (by omega) h1 h
  · exact spec.slotPoint_ne N hN hunit g ha (by omega) h2 h

/-- A sum over a run of slot points is a sum over the offsets. -/
private theorem sum_slotInterval (hunit : spec.IsUnit) (g : Fin p) {s t' : ℕ}
    (ht' : t' ≤ N) (F : (spec.scale N hN).graph.V → ℤ) :
    ∑ w ∈ spec.slotInterval N hN g s t', F w
      = ∑ j ∈ Finset.Icc s t', F (spec.slotPoint N hN g j) := by
  refine Finset.sum_image ?_
  intro x hx y hy hxy
  simp only [Finset.mem_coe, Finset.mem_Icc] at hx hy
  by_contra hne
  exact spec.slotPoint_ne N hN hunit g (le_trans hx.2 ht') (le_trans hy.2 ht') hne hxy

/-- **The two entry points of a run.**  A vertex outside the run
`[a_s, a_{t'}]` receives a chip from it exactly when it is one of the two
neighbours `a_{s-1}`, `a_{t'+1}` capping the run, and then exactly one. -/
private theorem outdeg_compl_slotInterval (hunit : spec.IsUnit) (g : Fin p)
    {s t' : ℕ} (hs : 1 ≤ s) (hst : s ≤ t') (ht' : t' < N)
    {v : (spec.scale N hN).graph.V} (hv : v ∉ spec.slotInterval N hN g s t') :
    outdeg_S (spec.scale N hN).graph (spec.slotInterval N hN g s t')ᶜ v
      = (if v = spec.slotPoint N hN g (s - 1) then 1 else 0)
        + (if v = spec.slotPoint N hN g (t' + 1) then 1 else 0) := by
  classical
  have h2N : 2 ≤ N := by omega
  -- The set fired into is the run itself, so the outdegree is a sum over offsets.
  have hsdiff : (Finset.univ \ (spec.slotInterval N hN g s t')ᶜ)
      = spec.slotInterval N hN g s t' := by
    ext w
    simp
  have hsum : outdeg_S (spec.scale N hN).graph (spec.slotInterval N hN g s t')ᶜ v
      = ∑ j ∈ Finset.Icc s t',
          (num_edges (spec.scale N hN).graph v (spec.slotPoint N hN g j) : ℤ) := by
    unfold outdeg_S
    rw [hsdiff]
    exact sum_slotInterval spec N hN hunit g (le_of_lt ht') _
  by_cases h1 : v = spec.slotPoint N hN g (s - 1)
  · subst h1
    have hzero : ∀ b ∈ Finset.Icc s t', b ≠ s →
        (num_edges (spec.scale N hN).graph (spec.slotPoint N hN g (s - 1))
          (spec.slotPoint N hN g b) : ℤ) = 0 := by
      intro b hb hbs
      rw [Finset.mem_Icc] at hb
      rw [num_edges_slotPoint_eq_zero spec N hN hunit g (a := s - 1) (b := b)
        (by omega) (by omega) (by omega) (by omega) (by omega)]
      norm_num
    have hone := spec.num_edges_slotPoint_succ N hN hunit h2N g (t := s - 1) (by omega)
    rw [show s - 1 + 1 = s by omega] at hone
    rw [if_pos rfl,
      if_neg (spec.slotPoint_ne N hN hunit g (by omega) (by omega) (by omega)), hsum,
      Finset.sum_eq_single_of_mem s (Finset.mem_Icc.mpr ⟨le_rfl, hst⟩) hzero, hone]
    norm_num
  · by_cases h2 : v = spec.slotPoint N hN g (t' + 1)
    · subst h2
      have hzero : ∀ b ∈ Finset.Icc s t', b ≠ t' →
          (num_edges (spec.scale N hN).graph (spec.slotPoint N hN g (t' + 1))
            (spec.slotPoint N hN g b) : ℤ) = 0 := by
        intro b hb hbt
        rw [Finset.mem_Icc] at hb
        rw [num_edges_slotPoint_eq_zero spec N hN hunit g (a := t' + 1) (b := b)
          (by omega) (by omega) (by omega) (by omega) (by omega)]
        norm_num
      have hone := spec.num_edges_slotPoint_succ N hN hunit h2N g (t := t') ht'
      rw [num_edges_symmetric] at hone
      rw [if_neg h1, if_pos rfl, hsum,
        Finset.sum_eq_single_of_mem t' (Finset.mem_Icc.mpr ⟨hst, le_rfl⟩) hzero, hone]
      norm_num
    · rw [if_neg h1, if_neg h2, hsum]
      refine (Finset.sum_eq_zero fun j hj => ?_).trans (by norm_num)
      rw [Finset.mem_Icc] at hj
      have hz : num_edges (spec.scale N hN).graph v (spec.slotPoint N hN g j) = 0 := by
        by_contra hne
        have hpos : 0 < num_edges (spec.scale N hN).graph (spec.slotPoint N hN g j) v := by
          rw [num_edges_symmetric]
          omega
        rcases (spec.slotPoint_adj_iff N hN hunit g (show 0 < j by omega)
          (show j < N by omega) v).mp hpos with h | h
        · rcases Nat.eq_or_lt_of_le hj.1 with heq | hlt
          · exact h1 (h.trans (by rw [show j - 1 = s - 1 from by omega]))
          · exact hv ((spec.mem_slotInterval_iff N hN g s t' v).mpr
              ⟨j - 1, by omega, by omega, h.symm⟩)
        · rcases Nat.eq_or_lt_of_le hj.2 with heq | hlt
          · exact h2 (h.trans (by rw [show j + 1 = t' + 1 from by omega]))
          · exact hv ((spec.mem_slotInterval_iff N hN g s t' v).mpr
              ⟨j + 1, by omega, by omega, h.symm⟩)
      rw [hz]
      norm_num

/-! ## The geometric identity behind both moves -/

/-- **Firing a run of interior slot points.**  For `1 ≤ s ≤ t' < N` the run
`[a_s, a_{t'}]` of slot points of `g` moves one chip off each of its two ends
onto the two vertices capping it.  When `s = t'` the formula reads
`D - 2 • a_s + a_{s-1} + a_{s+1}`, which is what the single member of a one-point
run does: it has outdegree two. -/
theorem setFiring_slotInterval (hunit : spec.IsUnit)
    (D : CFDiv (spec.scale N hN).graph) (g : Fin p) {s t' : ℕ} (hs : 1 ≤ s)
    (hst : s ≤ t') (ht' : t' < N) :
    set_firing (spec.scale N hN).graph D (spec.slotInterval N hN g s t')
      = D - one_chip (spec.slotPoint N hN g s)
          - one_chip (spec.slotPoint N hN g t')
          + one_chip (spec.slotPoint N hN g (s - 1))
          + one_chip (spec.slotPoint N hN g (t' + 1)) := by
  classical
  funext v
  simp only [Pi.add_apply, Pi.sub_apply]
  by_cases hvS : v ∈ spec.slotInterval N hN g s t'
  · obtain ⟨j, hj1, hj2, rfl⟩ := (spec.mem_slotInterval_iff N hN g s t' v).mp hvS
    have hmem1 := spec.slotPoint_mem_slotInterval_iff N hN hunit g (s := s) (t := t')
      (j := j - 1) (le_of_lt ht') (by omega)
    have hmem2 := spec.slotPoint_mem_slotInterval_iff N hN hunit g (s := s) (t := t')
      (j := j + 1) (le_of_lt ht') (by omega)
    have hm1 : (spec.slotPoint N hN g (j - 1) ∈ spec.slotInterval N hN g s t')
        ↔ s + 1 ≤ j := by rw [hmem1]; omega
    have hm2 : (spec.slotPoint N hN g (j + 1) ∈ spec.slotInterval N hN g s t')
        ↔ j + 1 ≤ t' := by rw [hmem2]; omega
    rw [set_firing_apply_of_mem _ _ hvS,
      spec.outdeg_slotPoint N hN hunit _ g (show 0 < j by omega) (show j < N by omega),
      one_chip_slot spec N hN hunit g (a := s) (b := j) (by omega) (by omega),
      one_chip_slot spec N hN hunit g (a := t') (b := j) (by omega) (by omega),
      one_chip_slot spec N hN hunit g (a := s - 1) (b := j) (by omega) (by omega),
      one_chip_slot spec N hN hunit g (a := t' + 1) (b := j) (by omega) (by omega)]
    simp only [hm1, hm2]
    split_ifs <;> omega
  · have hmemS : spec.slotPoint N hN g s ∈ spec.slotInterval N hN g s t' :=
      (spec.mem_slotInterval_iff N hN g s t' _).mpr ⟨s, le_rfl, hst, rfl⟩
    have hmemT : spec.slotPoint N hN g t' ∈ spec.slotInterval N hN g s t' :=
      (spec.mem_slotInterval_iff N hN g s t' _).mpr ⟨t', hst, le_rfl, rfl⟩
    have hns : v ≠ spec.slotPoint N hN g s := fun h => hvS (by rw [h]; exact hmemS)
    have hnt : v ≠ spec.slotPoint N hN g t' := fun h => hvS (by rw [h]; exact hmemT)
    rw [set_firing_apply_of_not_mem _ _ hvS,
      outdeg_compl_slotInterval spec N hN hunit g hs hst ht' hvS,
      one_chip_apply_other' _ _ hns, one_chip_apply_other' _ _ hnt]
    simp only [one_chip]
    ring

/-! ## The hole divisors and the two hole sets -/

/-- **The hole divisors**: a pair of chips at offsets `j` and `t - j` of the slot
`g`, on top of a rest divisor `R`.  At `j = 0` this is the state `q + a_t + R`,
with `q = a_0` the tail core vertex of `g`. -/
def holeDiv (g : Fin p) (t : ℕ) (R : CFDiv (spec.scale N hN).graph) (j : ℕ) :
    CFDiv (spec.scale N hN).graph :=
  one_chip (spec.slotPoint N hN g j) + one_chip (spec.slotPoint N hN g (t - j)) + R

/-- **The back-step set** `Back_j = {a_j, …, a_{t-j}}`. -/
def backSet (g : Fin p) (t j : ℕ) : Finset (spec.scale N hN).graph.V :=
  spec.slotInterval N hN g j (t - j)

/-- **The forward-step set** `Fwd_j = V ∖ {a_{j+1}, …, a_{t-j-1}}`, the
complement of the next back-step set. -/
def fwdSet (g : Fin p) (t j : ℕ) : Finset (spec.scale N hN).graph.V :=
  (spec.backSet N hN g t (j + 1))ᶜ

/-! ## Lemma H3: bookkeeping -/

/-- **H3, degree.**  A hole divisor carries exactly two chips over the rest. -/
theorem deg_holeDiv (g : Fin p) (t : ℕ) (R : CFDiv (spec.scale N hN).graph)
    (j : ℕ) : deg (spec.holeDiv N hN g t R j) = deg R + 2 := by
  simp only [holeDiv, _root_.map_add, deg_one_chip]
  ring

/-- **H3, effectivity.** -/
theorem effective_holeDiv (g : Fin p) (t : ℕ) {R : CFDiv (spec.scale N hN).graph}
    (hR : effective R) (j : ℕ) : effective (spec.holeDiv N hN g t R j) := by
  intro v
  have h1 := eff_one_chip (spec.slotPoint N hN g j) v
  have h2 := eff_one_chip (spec.slotPoint N hN g (t - j)) v
  have h3 := hR v
  simp only [holeDiv, Pi.add_apply]
  omega

/-- **H3, core-freeness.**  For `1 ≤ j` and `t - j < N` both chips of the hole
pair are interior to `g`, so the hole divisor agrees with the rest at every core
vertex.  (`1 ≤ j` excludes the tail core vertex `a_0` and `t - j < N` the head
core vertex `a_N`; each fails at exactly one of the two hub states.) -/
theorem holeDiv_coreVertex (hunit : spec.IsUnit) (g : Fin p) {t j : ℕ}
    (hj : 1 ≤ j) (hjt : 2 * j ≤ t) (htj : t - j < N)
    (R : CFDiv (spec.scale N hN).graph) (v : Fin n) :
    spec.holeDiv N hN g t R j ((spec.scale N hN).coreVertex v)
      = R ((spec.scale N hN).coreVertex v) := by
  simp only [holeDiv, Pi.add_apply]
  rw [one_chip_apply_other' _ _
      (spec.coreVertex_ne_slotPoint N hN hunit v g (t := j) (by omega) (by omega)),
    one_chip_apply_other' _ _
      (spec.coreVertex_ne_slotPoint N hN hunit v g (t := t - j) (by omega) (by omega))]
  ring

/-- **H3, offset sum.**  The pair of chips contributes `j + (t - j) = t` to the
offset sum of the slot `g`, for every `j` on the branch — including `j = 0`,
where the chip at offset `0` sits at a core vertex and contributes nothing.
This is the statement that `σ_f`, and hence `Δ`, is constant along the branch.

The hypothesis `_ht0 : 0 < t` is not used by the proof: with the interiority
hypothesis `t - j < N` the statement is true at `t = 0` as well. -/
theorem offsetSum_holeDiv (hunit : spec.IsUnit) (g : Fin p) {t j : ℕ}
    (_ht0 : 0 < t) (hjt : 2 * j ≤ t) (htj : t - j < N)
    (R : CFDiv (spec.scale N hN).graph) :
    ∑ i ∈ Finset.Ioo 0 N, i • spec.holeDiv N hN g t R j (spec.slotPoint N hN g i)
      = (t : ℤ) + ∑ i ∈ Finset.Ioo 0 N, i • R (spec.slotPoint N hN g i) := by
  classical
  -- A single chip at offset `k < N` contributes exactly `k`; at `k = 0` it sits at
  -- a core vertex and contributes nothing, which is again `k`.
  have key : ∀ k : ℕ, k < N →
      ∑ i ∈ Finset.Ioo 0 N,
          i • (one_chip (spec.slotPoint N hN g k) : CFDiv (spec.scale N hN).graph)
            (spec.slotPoint N hN g i) = (k : ℤ) := by
    intro k hkN
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · refine (Finset.sum_eq_zero fun i hi => ?_).trans (by norm_num)
      rw [Finset.mem_Ioo] at hi
      rw [one_chip_slot spec N hN hunit g (a := 0) (b := i) (by omega) (by omega),
        if_neg (by omega)]
      simp
    · have hzero : ∀ b ∈ Finset.Ioo 0 N, b ≠ k →
          b • (one_chip (spec.slotPoint N hN g k) : CFDiv (spec.scale N hN).graph)
            (spec.slotPoint N hN g b) = 0 := by
        intro b hb hbk
        rw [Finset.mem_Ioo] at hb
        rw [one_chip_slot spec N hN hunit g (a := k) (b := b) (by omega) (by omega),
          if_neg hbk]
        simp
      rw [Finset.sum_eq_single_of_mem k (Finset.mem_Ioo.mpr ⟨hk0, hkN⟩) hzero,
        one_chip_slot spec N hN hunit g (a := k) (b := k) (by omega) (by omega),
        if_pos rfl]
      simp
  have hsplit : ∀ i ∈ Finset.Ioo 0 N,
      i • spec.holeDiv N hN g t R j (spec.slotPoint N hN g i)
        = i • (one_chip (spec.slotPoint N hN g j) : CFDiv (spec.scale N hN).graph)
              (spec.slotPoint N hN g i)
          + i • (one_chip (spec.slotPoint N hN g (t - j)) : CFDiv (spec.scale N hN).graph)
              (spec.slotPoint N hN g i)
          + i • R (spec.slotPoint N hN g i) := by
    intro i _
    simp only [holeDiv, Pi.add_apply, smul_add]
  rw [Finset.sum_congr rfl hsplit]
  simp only [Finset.sum_add_distrib]
  rw [key j (by omega), key (t - j) (by omega)]
  have : (j : ℤ) + ((t - j : ℕ) : ℤ) = (t : ℤ) := by omega
  omega

/-! ## Lemma H2: the back step -/

/-- **Lemma H2 (back step), legality.**  For `1 ≤ j`, `2 * j ≤ t` and
`t - j < N` the run `Back_j = [a_j, a_{t-j}]` is legal for `holeDiv g t R j`:
its two ends carry the hole pair, doubled when `j = t - j`, which is exactly
the hypothesis of `interval_firing`. -/
theorem legal_backSet (hunit : spec.IsUnit) (g : Fin p) {t j : ℕ} (hj : 1 ≤ j)
    (hjt : 2 * j ≤ t) (htj : t - j < N) {R : CFDiv (spec.scale N hN).graph}
    (hR : effective R) :
    legal_set (spec.scale N hN).graph (spec.holeDiv N hN g t R j)
      (spec.backSet N hN g t j) := by
  have hR1 := hR (spec.slotPoint N hN g j)
  have hR2 := hR (spec.slotPoint N hN g (t - j))
  -- The two ends of the run carry the hole pair; they coincide when `2 * j = t`.
  have hlo : spec.holeDiv N hN g t R j (spec.slotPoint N hN g j)
      = 1 + (if j = t - j then 1 else 0) + R (spec.slotPoint N hN g j) := by
    simp only [holeDiv, Pi.add_apply]
    rw [one_chip_slot spec N hN hunit g (a := j) (b := j) (by omega) (by omega), if_pos rfl,
      one_chip_slot spec N hN hunit g (a := t - j) (b := j) (by omega) (by omega)]
  have hhi : spec.holeDiv N hN g t R j (spec.slotPoint N hN g (t - j))
      = (if t - j = j then 1 else 0) + 1 + R (spec.slotPoint N hN g (t - j)) := by
    simp only [holeDiv, Pi.add_apply]
    rw [one_chip_slot spec N hN hunit g (a := j) (b := t - j) (by omega) (by omega),
      one_chip_slot spec N hN hunit g (a := t - j) (b := t - j) (by omega) (by omega),
      if_pos rfl]
  simp only [backSet]
  refine (spec.interval_firing N hN hunit (spec.effective_holeDiv N hN g t hR j) g hj
    (by omega) (by omega) ?_ ?_ ?_).1
  · rw [hlo]; split_ifs <;> omega
  · rw [hhi]; split_ifs <;> omega
  · intro heq
    rw [hlo, if_pos heq]
    omega

/-- **Lemma H2 (back step), target.**  Firing `Back_j` steps the hole inwards by
one: the chips at offsets `j` and `t - j` move to `j - 1` and `t - j + 1`. -/
theorem setFiring_backSet (hunit : spec.IsUnit) (g : Fin p) {t j : ℕ}
    (hj : 1 ≤ j) (hjt : 2 * j ≤ t) (htj : t - j < N)
    (R : CFDiv (spec.scale N hN).graph) :
    set_firing (spec.scale N hN).graph (spec.holeDiv N hN g t R j)
        (spec.backSet N hN g t j)
      = spec.holeDiv N hN g t R (j - 1) := by
  simp only [backSet]
  rw [spec.setFiring_slotInterval N hN hunit _ g hj (by omega) (by omega)]
  simp only [holeDiv]
  rw [show t - (j - 1) = t - j + 1 from by omega]
  abel

/-! ## Lemma H1: the forward step -/

/-- **Lemma H1 (forward step), legality — sharp form.**  For `2 * (j + 1) ≤ t`
and `t - (j + 1) < N` the complement `Fwd_j = (Back_{j+1})ᶜ` is legal for
`holeDiv g t R j`.  This is H2 at `j + 1` run backwards through
`legalSet_compl_setFiring`, so it needs interiority only at `j + 1`: the state
`holeDiv g t R j` being fired *from* may still have its far chip on the head
core vertex (`t - j = N`), which is the head-hub state.  `legal_fwdSet` is the
same statement under the uniform hypothesis `t - j < N`. -/
theorem legal_fwdSet' (hunit : spec.IsUnit) (g : Fin p) {t j : ℕ}
    (hjt : 2 * (j + 1) ≤ t) (htj : t - (j + 1) < N)
    {R : CFDiv (spec.scale N hN).graph} (hR : effective R) :
    legal_set (spec.scale N hN).graph (spec.holeDiv N hN g t R j)
      (spec.fwdSet N hN g t j) := by
  have hfire := spec.setFiring_backSet N hN hunit g (t := t) (j := j + 1)
    (by omega) hjt htj R
  simp only [Nat.add_sub_cancel] at hfire
  have hcompl := Utilities.Gonality.legalSet_compl_setFiring
    (spec.effective_holeDiv N hN g t hR (j + 1))
    (spec.legal_backSet N hN hunit g (by omega) hjt htj hR)
  rw [hfire] at hcompl
  exact hcompl

/-- **Lemma H1 (forward step), legality.**  For `2 * (j + 1) ≤ t` and
`t - j < N` the complement `Fwd_j = (Back_{j+1})ᶜ` is legal for
`holeDiv g t R j`. -/
theorem legal_fwdSet (hunit : spec.IsUnit) (g : Fin p) {t j : ℕ}
    (hjt : 2 * (j + 1) ≤ t) (htj : t - j < N) {R : CFDiv (spec.scale N hN).graph}
    (hR : effective R) :
    legal_set (spec.scale N hN).graph (spec.holeDiv N hN g t R j)
      (spec.fwdSet N hN g t j) :=
  spec.legal_fwdSet' N hN hunit g hjt (by omega) hR

/-- **Lemma H1 (forward step), target — sharp form.**  Firing `Fwd_j` steps the
hole outwards by one, landing on `holeDiv g t R (j + 1)`; interiority is needed
only at `j + 1`.  See `legal_fwdSet'`. -/
theorem setFiring_fwdSet' (hunit : spec.IsUnit) (g : Fin p) {t j : ℕ}
    (hjt : 2 * (j + 1) ≤ t) (htj : t - (j + 1) < N)
    (R : CFDiv (spec.scale N hN).graph) :
    set_firing (spec.scale N hN).graph (spec.holeDiv N hN g t R j)
        (spec.fwdSet N hN g t j)
      = spec.holeDiv N hN g t R (j + 1) := by
  have hfire := spec.setFiring_backSet N hN hunit g (t := t) (j := j + 1)
    (by omega) hjt htj R
  simp only [Nat.add_sub_cancel] at hfire
  simp only [fwdSet]
  rw [← hfire, Utilities.Gonality.set_firing_compl_set_firing]

/-- **Lemma H1 (forward step), target.**  Firing `Fwd_j` steps the hole outwards
by one, landing on `holeDiv g t R (j + 1)`. -/
theorem setFiring_fwdSet (hunit : spec.IsUnit) (g : Fin p) {t j : ℕ}
    (hjt : 2 * (j + 1) ≤ t) (htj : t - j < N) (R : CFDiv (spec.scale N hN).graph) :
    set_firing (spec.scale N hN).graph (spec.holeDiv N hN g t R j)
        (spec.fwdSet N hN g t j)
      = spec.holeDiv N hN g t R (j + 1) :=
  spec.setFiring_fwdSet' N hN hunit g hjt (by omega) R

end Spec

end SubdivisionGraph

end Utilities.Certificate
