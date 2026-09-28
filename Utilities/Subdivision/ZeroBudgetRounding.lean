import Utilities.Subdivision.ScaleComposition
import Utilities.Subdivision.InteriorFiring

/-!
# Zero-budget rounding onto the coarse grid

A degree-four pencil on an `M`-fold refinement whose support lies on the
`M`-grid descends to the coarse graph.  The mechanism is
`Spec.rank_ge_of_rank_scale_ge_nearest` (from
`Utilities.Subdivision.OddSubdivisionDescent`) at `D₀ = 0` with four chips:
when every chip already sits on a coarse vertex its `Spec.roundDist` is zero,
so the budget hypothesis `Σ roundDist < N` is just `0 < N`.

## What is proved

* `exists_four_chips` — an effective divisor of degree four is a sum of four
  vertex chips (from `effective_divisor_decomposition` of
  `ChipFiringWithLean.Basic` and `Utilities.Foundations.BrillNoetherRank`).
* **`bnExists_of_onGrid`** — from an effective degree-four divisor of rank at
  least one on `(S.scale M).graph` whose support is on the `M`-grid, one gets
  `BNExists S.graph 1 4`.
* **`bnExists_of_onGrid_scale`** — the same with the divisor presented on
  `(spec.scale (M * u)).graph`, pulled back along the `LaplacianEquiv` of
  `Utilities.Subdivision.ScaleComposition`; `bnExists_of_onGrid_pow` is the
  case `M = 2 ^ a`.
* `bnExists_of_slotMoment` — a convenience composite that runs the
  interior-firing lemma (`Utilities.Subdivision.InteriorFiring`), the scale
  composition and the rounding in sequence, from the slot-moment hypothesis
  directly.  The three results remain separately usable; this is only their
  composition.
* `segment_bnExists_of_onGrid` — the rounding instantiated at `segmentSpec`
  with `u = 3` and `2 ^ a = 2`, so every index and length is a concrete
  numeral.

## What is NOT proved here

The hypotheses on the divisor are all explicit and none is discharged:
effectivity, `deg D = 4`, `rank ≥ 1`, and grid support (respectively, for
`bnExists_of_slotMoment`, divisibility of every slot moment).  Nothing produces
such a divisor; in applications it comes from the Draisma--Vargas count,
through a tropical morphism realized on a refinement.  Nothing here says the
resulting `u` is odd; oddness is a property of the `u` the caller chooses, not
of this step.  No connectivity, genus, bridgelessness or looplessness
hypothesis is used or available.

## Consumers

The Draisma--Vargas count, where it is used to construct the odd-subdivision
witness `GenusSixOddDescent.GenusSixOddSubdivisionWitness`.
-/

namespace DraismaVargas.Count.ZeroBudgetRounding

open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open DraismaVargas.Count.SlotGrid DraismaVargas.Count.ScaleComposition
open DraismaVargas.Count.InteriorFiring

variable {n p : ℕ}

/-- The embedding of the zero divisor is zero. -/
theorem embed_zero (S : Spec n p) (M : ℕ) (hM : 0 < M) :
    S.embed M hM (0 : CFDiv S.graph) = 0 := by
  funext y
  simp [Spec.embed]

/-- An effective divisor of degree four is a sum of four vertex chips. -/
theorem exists_four_chips {G : CFGraph} (D : CFDiv G) (hEff : effective D)
    (hDeg : deg D = 4) :
    ∃ ys : Fin 4 → G.V, D = ∑ i, one_chip (ys i) := by
  obtain ⟨E, F, hE, hF, hEdeg, hFdeg, hsplit⟩ :=
    effective_divisor_decomposition G D 2 2 hEff (by rw [hDeg]; norm_num)
  obtain ⟨x₁, x₂, hx⟩ :=
    exists_chip_pair_of_effective_deg_two _ E hE (by rw [hEdeg]; norm_num)
  obtain ⟨y₁, y₂, hy⟩ :=
    exists_chip_pair_of_effective_deg_two _ F hF (by rw [hFdeg]; norm_num)
  refine ⟨![x₁, x₂, y₁, y₂], ?_⟩
  rw [Fin.sum_univ_four, hsplit, hx, hy]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  abel

/-- Every chip in a finite sum of chips carries at least one chip at its own vertex. -/
theorem one_le_sum_chips {G : CFGraph} {m : ℕ} (ys : Fin m → G.V) (i : Fin m) :
    (1 : ℤ) ≤ (∑ j, one_chip (ys j) : CFDiv G) (ys i) := by
  classical
  have hterm : (1 : ℤ) = (one_chip (ys i) : CFDiv G) (ys i) := by
    simp [one_chip]
  rw [hterm]
  have := Finset.single_le_sum
    (f := fun j => (one_chip (ys j) : CFDiv G) (ys i))
    (fun j _ => eff_one_chip (ys j) (ys i)) (Finset.mem_univ i)
  simpa using this

/-- Zero-budget rounding: an effective degree-four divisor of rank at least one on an
`M`-fold refinement, supported on the `M`-grid, gives `BNExists _ 1 4` on the coarse
graph. -/
theorem bnExists_of_onGrid (S : Spec n p) (M : ℕ) (hM : 0 < M)
    (D : CFDiv (S.scale M hM).graph)
    (hEff : effective D) (hDeg : deg D = 4)
    (hGrid : ∀ y : (S.scale M hM).Vertex, D y ≠ 0 → OnGrid (S.scale M hM) M y)
    (hRank : rank (S.scale M hM).graph D ≥ 1) :
    BNExists S.graph 1 4 := by
  classical
  obtain ⟨ys, hys⟩ := exists_four_chips D hEff hDeg
  have hchip : ∀ i : Fin 4, D (ys i) ≠ 0 := by
    intro i
    rw [hys]
    have := one_le_sum_chips (G := (S.scale M hM).graph) ys i
    omega
  have hdist : ∀ i : Fin 4, S.roundDist M hM (ys i) = 0 := fun i =>
    roundDist_eq_zero_of_onGrid S M hM (hGrid (ys i) (hchip i))
  have hbudget : (∑ i : Fin 4, (S.roundDist M hM (ys i) : ℤ)) < M := by
    have hz : (∑ i : Fin 4, (S.roundDist M hM (ys i) : ℤ)) = 0 :=
      Finset.sum_eq_zero (fun i _ => by rw [hdist i]; norm_num)
    rw [hz]
    exact_mod_cast hM
  have hrank' : rank (S.scale M hM).graph
      (S.embed M hM 0 + ∑ i : Fin 4, one_chip (ys i)) ≥ 1 := by
    rw [embed_zero, zero_add, ← hys]
    exact hRank
  have hcoarse := S.rank_ge_of_rank_scale_ge_nearest M hM ys 0 1 hbudget hrank'
  refine ⟨_, ?_, hcoarse⟩
  rw [zero_add, map_sum]
  simp

/-- The same with the divisor presented on `spec.scale (M * u)`, through the composition
relabelling. -/
theorem bnExists_of_onGrid_scale (spec : Spec n p) (u M : ℕ) (hu : 0 < u) (hM : 0 < M)
    (D : CFDiv (spec.scale (M * u) (Nat.mul_pos hM hu)).graph)
    (hEff : effective D) (hDeg : deg D = 4)
    (hGrid : ∀ y : (spec.scale (M * u) (Nat.mul_pos hM hu)).Vertex,
      D y ≠ 0 → OnGrid (spec.scale (M * u) (Nat.mul_pos hM hu)) M y)
    (hRank : rank (spec.scale (M * u) (Nat.mul_pos hM hu)).graph D ≥ 1) :
    BNExists (spec.scale u hu).graph 1 4 := by
  classical
  set L := scaleScaleLaplacianEquiv spec u M hu hM with hL
  refine bnExists_of_onGrid (spec.scale u hu) M hM (L.symm.mapDiv D) ?_ ?_ ?_ ?_
  · exact (L.symm.effective_mapDiv_iff D).mpr hEff
  · rw [L.symm.deg_mapDiv D]; exact hDeg
  · intro y hy
    have hy' : D (L.toEquiv y) ≠ 0 := by
      have : L.symm.mapDiv D y = D (L.toEquiv y) := rfl
      rwa [this] at hy
    have := hGrid (L.toEquiv y) hy'
    rw [hL, scaleScaleLaplacianEquiv_toEquiv] at this
    exact (onGrid_vertexEquiv_iff spec u M hu hM M y).mp this
  · exact (L.symm.rank_mapDiv_ge_iff D 1).mpr hRank

/-- Zero-budget rounding with the refinement factor written as a power of two. -/
theorem bnExists_of_onGrid_pow (spec : Spec n p) (u a : ℕ) (hu : 0 < u)
    (D : CFDiv (spec.scale (2 ^ a * u) (Nat.mul_pos (Nat.two_pow_pos a) hu)).graph)
    (hEff : effective D) (hDeg : deg D = 4)
    (hGrid : ∀ y : (spec.scale (2 ^ a * u) (Nat.mul_pos (Nat.two_pow_pos a) hu)).Vertex,
      D y ≠ 0 → OnGrid (spec.scale (2 ^ a * u) (Nat.mul_pos (Nat.two_pow_pos a) hu)) (2 ^ a) y)
    (hRank : rank (spec.scale (2 ^ a * u) (Nat.mul_pos (Nat.two_pow_pos a) hu)).graph D ≥ 1) :
    BNExists (spec.scale u hu).graph 1 4 :=
  bnExists_of_onGrid_scale spec u (2 ^ a) hu (Nat.two_pow_pos a) D hEff hDeg hGrid hRank

/-- The three steps in sequence: interior firing, scale composition and
zero-budget rounding. -/
theorem bnExists_of_slotMoment (spec : Spec n p) (u a : ℕ) (hu : 0 < u)
    (D : CFDiv (spec.scale (2 ^ a * u) (Nat.mul_pos (Nat.two_pow_pos a) hu)).graph)
    (hEff : effective D) (hDeg : deg D = 4)
    (hmom : ∀ e, ((2 ^ a : ℕ) : ℤ) ∣
      slotMoment (spec.scale (2 ^ a * u) (Nat.mul_pos (Nat.two_pow_pos a) hu)) D e)
    (hRank : rank (spec.scale (2 ^ a * u) (Nat.mul_pos (Nat.two_pow_pos a) hu)).graph D ≥ 1) :
    BNExists (spec.scale u hu).graph 1 4 := by
  obtain ⟨D', _hlin, hEff', hDeg', hRank', hGrid'⟩ :=
    exists_onGrid_scale spec (2 ^ a * u) (Nat.mul_pos (Nat.two_pow_pos a) hu) (2 ^ a)
      (Dvd.intro u rfl) D hEff hmom 1 hRank
  exact bnExists_of_onGrid_pow spec u a hu D' hEff' (by rw [hDeg', hDeg]) hGrid' hRank'

/-! ## The rounding at a concrete small specification -/

/-- Zero-budget rounding at the unit segment with `u = 3` and `2 ^ a = 2`. -/
theorem segment_bnExists_of_onGrid
    (D : CFDiv (segmentSpec.scale (2 * 3) (by norm_num)).graph)
    (hEff : effective D) (hDeg : deg D = 4)
    (hGrid : ∀ y : (segmentSpec.scale (2 * 3) (by norm_num)).Vertex,
      D y ≠ 0 → OnGrid (segmentSpec.scale (2 * 3) (by norm_num)) 2 y)
    (hRank : rank (segmentSpec.scale (2 * 3) (by norm_num)).graph D ≥ 1) :
    BNExists (segmentSpec.scale 3 (by norm_num)).graph 1 4 :=
  bnExists_of_onGrid_scale segmentSpec 3 2 (by norm_num) (by norm_num) D hEff hDeg hGrid hRank

end DraismaVargas.Count.ZeroBudgetRounding
