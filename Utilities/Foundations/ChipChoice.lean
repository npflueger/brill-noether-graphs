module

public import Utilities.Foundations.RiemannRochWinnable

@[expose] public section

/-!
# The chip-choice lemma and `W_a − W_b = Pic^{a−b}` in the range `max(a, b) ≥ g − 1`

* `exists_effective_sub_winnable` (**chip-choice lemma**): if `M` is winnable and
  `0 ≤ e ≤ deg M`, some effective `F` of degree `e` has `M − F` winnable. Take `F` inside an
  effective representative of `M` (`effective_divisor_decomposition`).
* `exists_effective_rank_ge_of_canonical_sub_winnable` (**the Riemann--Roch form**): a condition
  `rank(X + F) ≥ k` whose threshold is the Riemann--Roch one, `deg(X + F) = g − 1 + k`, is
  winnability of `K − X − F`; so if `K − X` is winnable of degree `≥ e`, some effective `F` of
  degree `e` satisfies it.
* `winnable_of_genus_le_deg` (Riemann): a divisor of degree at least `g` is winnable.
* `exists_effective_pair_of_deg` (**the corollary**): `W_a − W_b = Pic^{a−b}` on every connected
  graph of genus `g` with a vertex, whenever `a, b ≥ 0`, `a + b ≥ g` and `max(a, b) ≥ g − 1`.
  Stated concretely: for every divisor `c` of degree `a − b` there are effective `A`, `B` of
  degrees `a`, `b` with `c + B ∼ A` (`linear_equiv G (c + B) A`, i.e. `A − (c + B)` is
  principal). The vertex is needed: the empty graph has genus one and no effective divisor of
  degree one.

In transmission problems these settle every condition that is "one effectivity or single-rank
condition on `D`, one on a translate of `D`", with one of the two classes of degree `≥ g − 1`:
choose the free chips inside an effective representative.
-/

namespace Utilities

/-- **Chip-choice lemma.** If `M` is winnable and `0 ≤ e ≤ deg M`, some effective `F` of degree
`e` has `M − F` winnable: take `F` inside an effective representative of `M`. -/
theorem exists_effective_sub_winnable {G : CFGraph} {M : CFDiv G} (hM : winnable G M) {e : ℤ}
    (he : 0 ≤ e) (hdeg : e ≤ deg M) :
    ∃ F : CFDiv G, effective F ∧ deg F = e ∧ winnable G (M - F) := by
  obtain ⟨E, hE, hME⟩ := (winnable_iff_exists_effective G M).mp hM
  have hdegE : deg E = deg M := (linear_equiv_preserves_deg G M E hME).symm
  obtain ⟨F, R, hF, hR, hFdeg, -, hsplit⟩ :=
    effective_divisor_decomposition G E e.toNat (deg M - e).toNat hE (by omega)
  refine ⟨F, hF, by omega, ?_⟩
  refine (winnable_iff_exists_effective G (M - F)).mpr ⟨R, hR, ?_⟩
  unfold linear_equiv at hME ⊢
  have hEq : R - (M - F) = E - M := by
    rw [hsplit]
    abel
  rw [hEq]
  exact hME

/-- The chip-choice lemma in rank form: `rank M ≥ 0` is winnability. -/
theorem exists_effective_sub_winnable_of_rank {G : CFGraph} {M : CFDiv G} (hM : rank G M ≥ 0)
    {e : ℤ} (he : 0 ≤ e) (hdeg : e ≤ deg M) :
    ∃ F : CFDiv G, effective F ∧ deg F = e ∧ winnable G (M - F) :=
  exists_effective_sub_winnable
    ((rank_nonneg_iff_winnable G M).mp ((rank_geq_iff G M 0).mpr hM)) he hdeg

/-- **Riemann**: a divisor of degree at least `g` is winnable. -/
theorem winnable_of_genus_le_deg {G : CFGraph} (hG : graph_connected G) {M : CFDiv G}
    (hM : (genus G : ℤ) ≤ deg M) : winnable G M := by
  have hRR := riemann_roch_for_graphs hG M
  have hDual := rank_geq_neg_one G (canonical_divisor G - M)
  have h : rank G M ≥ deg M - (genus G : ℤ) := by omega
  exact (rank_nonneg_iff_winnable G M).mp ((rank_geq_iff G M 0).mpr (by omega))

/-- **Chip choice through Riemann--Roch.** If `K − X` is winnable of degree at least `e ≥ 0`, and
`deg X + e = g − 1 + k` (the Riemann--Roch threshold), some effective `F` of degree `e` has
`rank(X + F) ≥ k`. -/
theorem exists_effective_rank_ge_of_canonical_sub_winnable {G : CFGraph}
    (hG : graph_connected G) {X : CFDiv G} {e k : ℤ} (he : 0 ≤ e)
    (hK : winnable G (canonical_divisor G - X)) (hdegK : e ≤ deg (canonical_divisor G - X))
    (hk : deg X + e = (genus G : ℤ) - 1 + k) :
    ∃ F : CFDiv G, effective F ∧ deg F = e ∧ rank G (X + F) ≥ k := by
  obtain ⟨F, hF, hFdeg, hwin⟩ := exists_effective_sub_winnable hK he hdegK
  refine ⟨F, hF, hFdeg, ?_⟩
  have hdeg : deg (X + F) = (genus G : ℤ) - 1 + k := by
    rw [deg.map_add, hFdeg, hk]
  refine (rank_ge_iff_canonical_sub_winnable_of_degree hG (X + F) k hdeg).mpr ?_
  have hEq : canonical_divisor G - (X + F) = canonical_divisor G - X - F := by abel
  rw [hEq]
  exact hwin

/-- The case `a ≥ g − 1` of `exists_effective_pair_of_deg`. -/
theorem exists_effective_pair_of_deg_of_left {G : CFGraph} (hG : graph_connected G)
    [Nonempty G.V] (c : CFDiv G) (a b : ℤ) (ha0 : 0 ≤ a) (hb : 0 ≤ b) (hc : deg c = a - b)
    (hab : (genus G : ℤ) ≤ a + b) (ha : (genus G : ℤ) - 1 ≤ a) :
    ∃ A B : CFDiv G, effective A ∧ effective B ∧ deg A = a ∧ deg B = b ∧
      linear_equiv G (c + B) A := by
  -- It suffices to find `B` effective of degree `b` with `c + B` winnable.
  suffices hB : ∃ B : CFDiv G, effective B ∧ deg B = b ∧ winnable G (c + B) by
    obtain ⟨B, hB, hBdeg, hwin⟩ := hB
    obtain ⟨A, hA, hcA⟩ := (winnable_iff_exists_effective G (c + B)).mp hwin
    refine ⟨A, B, hA, hB, ?_, hBdeg, hcA⟩
    rw [← linear_equiv_preserves_deg G _ _ hcA, deg.map_add, hc, hBdeg]
    ring
  rcases le_or_gt (genus G : ℤ) a with hga | hga
  · -- `deg(c + B) = a ≥ g`: any `B` works (Riemann).
    obtain ⟨q⟩ := ‹Nonempty G.V›
    refine ⟨b • one_chip q, fun x ↦ ?_, ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg hb (eff_one_chip q x)
    · rw [map_zsmul, deg_one_chip, smul_eq_mul, mul_one]
    · apply winnable_of_genus_le_deg hG
      rw [deg.map_add, map_zsmul, deg_one_chip, hc]
      simp only [smul_eq_mul, mul_one]
      omega
  · -- `a = g − 1`, so `b ≥ 1` and `deg(K − c) = g − 1 + b ≥ g`.
    have hdegK : deg (canonical_divisor G - c) = (genus G : ℤ) - 1 + b := by
      rw [deg.map_sub, degree_of_canonical_divisor, hc]
      omega
    obtain ⟨B, hB, hBdeg, hrank⟩ := exists_effective_rank_ge_of_canonical_sub_winnable (X := c) hG hb
      (winnable_of_genus_le_deg hG (by omega)) (by omega) (k := 0) (by omega)
    exact ⟨B, hB, hBdeg, (rank_nonneg_iff_winnable G _).mp ((rank_geq_iff G _ 0).mpr hrank)⟩

/-- **`W_a − W_b = Pic^{a−b}` when `a + b ≥ g` and `max(a, b) ≥ g − 1`**. For every
divisor `c` of degree `a − b` on a connected graph of genus `g` with a vertex, there are
effective `A`, `B` of degrees `a`, `b` with `c + B ∼ A`. -/
theorem exists_effective_pair_of_deg {G : CFGraph} (hG : graph_connected G) [Nonempty G.V]
    (c : CFDiv G) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : deg c = a - b)
    (hab : (genus G : ℤ) ≤ a + b) (hmax : (genus G : ℤ) - 1 ≤ max a b) :
    ∃ A B : CFDiv G, effective A ∧ effective B ∧ deg A = a ∧ deg B = b ∧
      linear_equiv G (c + B) A := by
  rcases le_total b a with hba | hab'
  · exact exists_effective_pair_of_deg_of_left hG c a b ha hb hc hab (by
      rw [max_eq_left hba] at hmax; exact hmax)
  · obtain ⟨A', B', hA', hB', hA'deg, hB'deg, hequiv⟩ :=
      exists_effective_pair_of_deg_of_left hG (-c) b a hb ha (by rw [map_neg, hc]; ring)
        (by omega) (by rw [max_eq_right hab'] at hmax; exact hmax)
    refine ⟨B', A', hB', hA', hB'deg, hA'deg, ?_⟩
    unfold linear_equiv at hequiv ⊢
    have hEq : B' - (c + A') = -(A' - (-c + B')) := by abel
    rw [hEq]
    exact neg_mem hequiv

end Utilities
