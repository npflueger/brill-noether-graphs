module

public import Utilities.Gonality.LegalFiring
public import Utilities.Foundations.ScriptClamping

@[expose] public section

/-!
# Legal firing chains and the reduced-divisor maximum principle

Generic chip-firing facts for an abstract finite graph:

* Legal set firing preserves effectivity and adds the principal divisor of
  the indicator script, fixing the sign convention used throughout
  (`legalSet_iff_outdeg_le`, `setFiring_eq_add_prin`, `effective_setFiring`).
* `exists_legal_fireChain` joins linearly equivalent effective divisors through
  effective legal firings. Its construction fires the upper level sets of a
  truncated script, in increasing order of level-set size.
* A script carrying a reduced divisor to an effective one attains its maximum
  at the reducing vertex (`le_apply_of_qReduced`, the maximum principle); dually,
  a script carrying an effective divisor to a reduced one attains its minimum
  there (`apply_le_of_qReduced`).
* Complementary firings reverse each other (`legalSet_compl_setFiring`). Edge
  multiplicity bounds on outgoing degree propagate membership of a legal set
  through a chipless vertex (`mem_of_apply_le_zero`).

All divisor algebra is stated for an abstract `CFGraph`, so consumers can reuse
it without unfolding concrete subdivision vertices.
-/

namespace Utilities.Gonality

open Finset

variable {G : CFGraph}

/-! ## Bounds for legal firing sets -/

/-- One edge into the complement of `S` is a lower bound for `outdeg_S`. -/
theorem num_edges_le_outdeg_S {G : CFGraph} (S : Finset G.V) (x : G.V)
    {y : G.V} (hy : y ∉ S) : (num_edges G x y : ℤ) ≤ outdeg_S G S x := by
  unfold outdeg_S
  exact Finset.single_le_sum (f := fun w : G.V => (num_edges G x w : ℤ))
    (fun _ _ => Int.natCast_nonneg _) (by simp [hy])

/-- Two edges into the complement of `S` bound `outdeg_S` from below. -/
theorem two_num_edges_le_outdeg_S {G : CFGraph} (S : Finset G.V) (x : G.V)
    {y z : G.V} (hyz : y ≠ z) (hy : y ∉ S) (hz : z ∉ S) :
    (num_edges G x y : ℤ) + (num_edges G x z : ℤ) ≤ outdeg_S G S x := by
  have hsub : ({y, z} : Finset G.V) ⊆ Finset.univ \ S := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl <;> simp [hy, hz]
  unfold outdeg_S
  rw [← Finset.sum_pair (f := fun w : G.V => (num_edges G x w : ℤ)) hyz]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun _ _ _ => Int.natCast_nonneg _)

/-- **The closure lemma**: a chipless member of a legal set has every neighbour
in the set, since a single edge leaving the set already makes its outdegree
positive. -/
theorem mem_of_apply_le_zero {G : CFGraph} {D : CFDiv G} {S : Finset G.V}
    (hS : legal_set G D S) {x : G.V} (hx : x ∈ S) (hle : D x ≤ 0)
    {y : G.V} (hy : 0 < num_edges G x y) : y ∈ S := by
  by_contra hyS
  have hlegal := hS x hx
  have hedge := num_edges_le_outdeg_S S x hyS
  have hpos : (0 : ℤ) < (num_edges G x y : ℤ) := by exact_mod_cast hy
  omega

/-! ## The set-firing interface

The first three statements of this section restate lemmas of the dependency in
the form used below: legality as an outdegree bound, the fired divisor as the
addition of a principal divisor, and effectivity of the result. -/

/-- **Legality.**  A set `S` is legal for `D` exactly when firing it keeps every
vertex of `S` out of debt: `outdeg_S G S v ≤ D v` for `v ∈ S`. -/
theorem legalSet_iff_outdeg_le (D : CFDiv G) (S : Finset G.V) :
    legal_set G D S ↔ ∀ v ∈ S, outdeg_S G S v ≤ D v := Iff.rfl

/-- **The fired divisor.**  Firing `S` once adds the principal divisor of the
indicator script.  Concretely, `prin G (indicator_script G S)` is `-outdeg_S` on
`S`, and at a vertex off `S` it is the number of edges arriving from `S`. -/
theorem setFiring_eq_add_prin (D : CFDiv G) (S : Finset G.V) :
    set_firing G D S = D + prin G (indicator_script G S) :=
  set_firing_eq_add_prin_indicator_script G D S

/-- **Effectivity of the result.**  Firing a legal set of an effective divisor
leaves an effective divisor. -/
theorem effective_setFiring {D : CFDiv G} {S : Finset G.V} (hD : effective D)
    (hS : legal_set G D S) : effective (set_firing G D S) :=
  effective_set_firing_of_legal_set G hD hS

/-- **Reversibility of a firing move.**  If `S` is legal for `D` then `Sᶜ` is
legal for the fired divisor, and firing it returns `D`
(`set_firing_compl_set_firing`).  So legal set firings between effective
divisors form a symmetric move relation: every move can be undone by a legal
move. -/
theorem legalSet_compl_setFiring {D : CFDiv G} {S : Finset G.V} (hD : effective D)
    (hS : legal_set G D S) : legal_set G (set_firing G D S) Sᶜ := by
  -- `outdeg_{Sᶜ}(v) = indeg_S(v)` for `v ∉ S`, and the fired divisor at such a
  -- `v` is `D v + indeg_S v ≥ indeg_S v` because `D` is effective.  Legality of
  -- `S` for `D` is not needed: the complement of *any* set is legal for the
  -- fired divisor as soon as `D` itself is effective.  (`hS` is kept in the
  -- signature because callers have it to hand; it is not used.)
  have _ : legal_set G D S := hS
  intro v hv
  have hvS : v ∉ S := Finset.mem_compl.mp hv
  have hDv := hD v
  rw [set_firing_apply_of_not_mem G D hvS]
  omega

/-! ## Chains of legal firings -/

/-- **The firing chain.**  Any two effective divisors in one linear equivalence
class are joined by a finite chain of *legal* set firings, every intermediate
divisor effective.

Write `D' = D + prin F` with `F ≥ 0`, and interpolate by
`D_c := D + prin ((F - c)⁺)` for `c = max F, …, 0`.  Each `D_c` is effective by
`effective_add_prin_truncate`, and
`D_c = D_{c+1} + prin (indicator_script {F ≥ c+1})`, i.e. the **upper** level
sets are fired, smallest first.  (The order matters.  Truncating from above
instead, through `D + prin (min F c)` for `c = 0, 1, …`, fires the largest level
set first and can lose effectivity: on the path `a—b—c` with `D = (2,0,0)` and
`F = (2,1,0)`, `D + prin (min F 1)` is not effective.) -/
theorem exists_legal_fireChain {D D' : CFDiv G} (hD : effective D)
    (hD' : effective D') (hlin : linear_equiv G D D') :
    ∃ (k : ℕ) (U : ℕ → Finset G.V),
      (∀ i, i < k → legal_set G (fireChain G D U i) (U i)) ∧
        fireChain G D U k = D' := by
  classical
  -- The script carrying `D` to `D'`, normalized to vanish at an argmin, so that
  -- it is nonnegative.  (`prin` kills constants, so this is free.)
  obtain ⟨x₀, hx₀⟩ := (principal_iff_eq_prin G (D' - D)).mp hlin
  obtain ⟨m, -, hm⟩ := Finset.exists_min_image (Finset.univ : Finset G.V) x₀
    ⟨Classical.arbitrary G.V, Finset.mem_univ _⟩
  set x : firing_script G := fun v => x₀ v - x₀ m with hxdef
  have hxnonneg : ∀ v : G.V, 0 ≤ x v := by
    intro v
    have h := hm v (Finset.mem_univ v)
    simp only [hxdef]
    omega
  have hD'eq : D' = D + prin G x := by
    rw [hxdef, prin_sub_const]
    funext v
    have h := congrFun hx₀ v
    simp only [Pi.sub_apply] at h
    simp only [Pi.add_apply]
    omega
  have hDx : effective (D + prin G x) := by rw [← hD'eq]; exact hD'
  -- The top level of the script, and the number of firings.
  obtain ⟨p, -, hp⟩ :=
    Finset.exists_max_image (Finset.univ : Finset G.V) x ⟨m, Finset.mem_univ m⟩
  set K : ℤ := x p with hK
  have hK0 : 0 ≤ K := by rw [hK]; exact hxnonneg p
  set k : ℕ := K.toNat with hk
  have hkK : (k : ℤ) = K := Int.toNat_of_nonneg hK0
  -- The **upper** level sets, fired from the top downwards (smallest first).
  set U : ℕ → Finset G.V := fun i => Finset.univ.filter (fun v => K - (i : ℤ) ≤ x v)
    with hU
  have hmemU : ∀ (i : ℕ) (v : G.V), v ∈ U i ↔ K - (i : ℤ) ≤ x v := by
    intro i v
    simp [hU]
  -- Firing the first `t` of them realizes the truncation `(x - (K - t))⁺`.
  have hchain : ∀ t : ℕ,
      fireChain G D U t = D + prin G (fun v => max (x v - (K - (t : ℤ))) 0) := by
    intro t
    induction t with
    | zero =>
        have h0 : (fun v => max (x v - (K - ((0 : ℕ) : ℤ))) 0) = (0 : firing_script G) := by
          funext v
          have hpv := hp v (Finset.mem_univ v)
          show max (x v - (K - ((0 : ℕ) : ℤ))) 0 = 0
          push_cast
          omega
        rw [fireChain_zero, h0, map_zero]
        simp
    | succ t ih =>
        have key : (fun v : G.V => max (x v - (K - ((t : ℤ) + 1))) 0)
            = (fun v : G.V => max (x v - (K - (t : ℤ))) 0) + indicator_script G (U t) := by
          funext v
          show max (x v - (K - ((t : ℤ) + 1))) 0
              = max (x v - (K - (t : ℤ))) 0 + indicator_script G (U t) v
          by_cases h : K - (t : ℤ) ≤ x v
          · rw [indicator_script, ite_eq_left ((hmemU t v).mpr h)]
            omega
          · rw [indicator_script, ite_eq_right (fun hc => h ((hmemU t v).mp hc))]
            omega
        rw [fireChain_succ, ih, set_firing_eq_add_prin_indicator_script]
        push_cast
        rw [key, map_add]
        abel
  -- Hence every divisor of the chain is effective, by the truncation lemma …
  have heff : ∀ t : ℕ, effective (fireChain G D U t) := by
    intro t
    rw [hchain]
    exact effective_add_prin_truncate hD hDx _
  refine ⟨k, U, ?_, ?_⟩
  · -- … and effectivity of the next divisor *is* legality of the current step.
    intro i _ u hu
    have h := heff (i + 1) u
    rw [fireChain_succ, set_firing_apply_of_mem G _ hu] at h
    omega
  · -- The last truncation is `x` itself, because `x ≥ 0`.
    rw [hchain, hD'eq, hkK]
    congr 1
    congr 1
    funext v
    have h := hxnonneg v
    show max (x v - (K - K)) 0 = x v
    omega

/-! ## The max principle for reduced divisors -/

/-- **The argmax set absorbs its own outdegree.**  If `S` is exactly the set of
vertices where the script `F` attains its maximum, then at every `u ∈ S` each
summand of `prin G F u` is `≤ 0` and each of the `outdeg_S G S u` edges leaving
`S` contributes `≤ -1`, so `prin G F u ≤ -outdeg_S G S u`.

This is the dependency's private `maxset_of_script`
(`ChipFiringWithLean/Basic.lean`), reproved here in the form the maximum
principle below needs; it is private because it duplicates that lemma. -/
private theorem prin_le_neg_outdeg_of_argmax (F : firing_script G)
    {S : Finset G.V} (hS : ∀ u : G.V, u ∈ S ↔ ∀ w : G.V, F w ≤ F u)
    {v : G.V} (hv : v ∈ S) :
    prin G F v ≤ -outdeg_S G S v := by
  classical
  have hmax : ∀ w : G.V, F w ≤ F v := (hS v).mp hv
  -- Off the argmax set the script drops by at least one.
  have hdrop : ∀ u : G.V, u ∉ S → F u - F v ≤ -1 := by
    intro u hu
    have hle := hmax u
    have hne : F u ≠ F v := fun h => hu ((hS u).mpr fun w => h ▸ hmax w)
    omega
  have hout : outdeg_S G S v
      = ∑ u : G.V, (if u ∈ S then (0 : ℤ) else (num_edges G v u : ℤ)) := by
    rw [outdeg_S_eq_sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u ∈ S
    · rw [ite_eq_left hu, ite_eq_right (not_not_intro hu)]
    · rw [ite_eq_right hu, ite_eq_left hu]
  rw [prin_apply, hout, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun u _ => ?_
  by_cases hu : u ∈ S
  · have heq : F u = F v := le_antisymm (hmax u) ((hS u).mp hu v)
    rw [ite_eq_left hu, heq, sub_self, zero_mul, neg_zero]
  · rw [ite_eq_right hu]
    calc (F u - F v) * (num_edges G v u : ℤ)
        ≤ (-1) * (num_edges G v u : ℤ) :=
          mul_le_mul_of_nonneg_right (hdrop u hu) (Int.natCast_nonneg _)
      _ = -(num_edges G v u : ℤ) := by ring

/-- **The maximum principle for reduced divisors.**  If `D` is `q`-reduced and
`D + prin G F` is effective, then the script `F` attains its maximum at `q`.

The proof is three lines: on the argmax set `S` every summand of `prin G F` is
`≤ 0` and each of the `outdeg_S G S u` edges leaving `S` contributes `≤ -1`, so
`prin G F u ≤ -outdeg_S G S u`; effectivity of `D + prin G F` then makes `S`
legal for `D`, and `q`-reducedness forces `q ∈ S`. -/
theorem le_apply_of_qReduced {q : G.V} {D : CFDiv G} (hred : q_reduced G q D)
    {F : firing_script G} (hF : effective (D + prin G F)) (v : G.V) :
    F v ≤ F q := by
  classical
  -- The argmax set, described by "no vertex is higher".
  set S : Finset G.V := Finset.univ.filter (fun u => ∀ w : G.V, F w ≤ F u) with hSdef
  have hSmem : ∀ u : G.V, u ∈ S ↔ ∀ w : G.V, F w ≤ F u := by
    intro u
    rw [hSdef]
    simp
  -- It is nonempty: it contains an argmax.
  obtain ⟨p, -, hp⟩ :=
    Finset.exists_max_image (Finset.univ : Finset G.V) F ⟨q, Finset.mem_univ q⟩
  have hpS : p ∈ S := (hSmem p).mpr fun w => hp w (Finset.mem_univ w)
  -- It is legal for `D`: `prin G F u ≤ -outdeg_S G S u` on `S`, and
  -- `D u + prin G F u ≥ 0`.
  have hlegal : legal_set G D S := by
    intro u hu
    have h1 := prin_le_neg_outdeg_of_argmax F hSmem hu
    have h2 := hF u
    simp only [Pi.add_apply] at h2
    omega
  -- A `q`-reduced divisor has no nonempty legal set avoiding `q`, so `q ∈ S`.
  have hqS : q ∈ S := by
    by_contra hq
    exact hred.2 S hq ⟨p, hpS⟩ hlegal
  exact (hSmem q).mp hqS v

/-- The companion **min principle**: if `D` is `q`-reduced and
`D = D' + prin G F` with `D'` effective, then `F` attains its *minimum* at `q`.
(Apply `le_apply_of_qReduced` to the script `-F`, using
`prin G (-F) = -prin G F`.) -/
theorem apply_le_of_qReduced {q : G.V} {D D' : CFDiv G} (hred : q_reduced G q D)
    (hD' : effective D') {F : firing_script G} (hF : D = D' + prin G F) (v : G.V) :
    F q ≤ F v := by
  -- `D + prin G (-F) = D'` is effective, so the max principle applied to `-F`
  -- gives `-F v ≤ -F q`.
  have heff : effective (D + prin G (-F)) := by
    rw [hF, map_neg]
    have h : D' + prin G F + -prin G F = D' := by abel
    rw [h]
    exact hD'
  have h := le_apply_of_qReduced hred heff v
  simp only [Pi.neg_apply] at h
  omega

end Utilities.Gonality
