module

public import DraismaVargasCount.StepSupplyReduction
public import DraismaVargasCount.CaterpillarBallotCount
public import DraismaVargasCount.MemberCertifiedPencil

@[expose] public section

/-!
# Genus-six cores: their indices, and the caterpillar as a base core

Two facts used by the propagation step of the count (step 4 of `DraismaVargasCount.Assembly`,
`Assembly.c34_genusSix`).

* `three_mul_eq_two_mul_of_cubic` -- the handshake identity for an ordered core: cubicity forces
  `3 * n = 2 * p`.  Generic in `n` and `p`, no other hypothesis.  With the genus equation,
  `index_of_genusSix` pins a connected cubic core of genus six to `n = 10`, `p = 15`, which is
  what lets a statement proved at fixed indices be quantified the way `CountSchedule.C34`
  quantifies it.
* `catCubicCore` -- the genus-six caterpillar of loops as a bundled connected cubic core, from
  `MemberCertifiedPencil.catCore_two_cubic` and `MemberCertifiedPencil.catCore_two_connected`.
  It is the base core from which the parity of the count is propagated.
-/

namespace DraismaVargas.Count.StepSupplyGenusSix

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.Count.FibreCaterpillar (catCore)
open DraismaVargas.Count.StepSupplyReduction
open Utilities.Certificate.ExplicitPotential (Core)
open Finset

/-! ## 1.  The handshake identity -/

/-- **Cubicity forces `3n = 2p`.**  Summing the occurrence-sensitive incidence
degree over vertices counts every slot endpoint once, so the total is `2p`; if
every vertex has degree three the total is `3n`.  Generic in `n` and `p`. -/
theorem three_mul_eq_two_mul_of_cubic {n p : ℕ} {core : Core n p} (h : core.Cubic) :
    3 * n = 2 * p := by
  classical
  have h1 : (∑ v : Fin n, core.incidenceDegree v) = 3 * n := by
    rw [Finset.sum_congr rfl fun v _ ↦ h v]
    simp [Finset.sum_const, Nat.mul_comm]
  have h2 : (∑ v : Fin n, core.incidenceDegree v) = 2 * p := by
    simp only [Core.incidenceDegree]
    rw [Finset.sum_comm]
    have hcol : ∀ e : Fin p, (∑ v : Fin n,
        ((if core.tail e = v then 1 else 0) + (if core.head e = v then 1 else 0))) = 2 := by
      intro e
      rw [Finset.sum_add_distrib]
      simp
    rw [Finset.sum_congr rfl fun e _ ↦ hcol e]
    simp [Finset.sum_const, Nat.mul_comm]
  omega

/-- **A connected cubic core of genus six has ten vertices and fifteen slots.**
Truncated subtraction is handled by `omega`: `p + 1 - n = 6` already forces
`n ≤ p + 1`. -/
theorem index_of_genusSix {n p : ℕ} {core : Core n p} (h : core.Cubic)
    (hg : p + 1 - n = 2 * 2 + 2) : n = 4 * 2 + 2 ∧ p = 6 * 2 + 3 := by
  have := three_mul_eq_two_mul_of_cubic h
  omega

/-! ## 2.  The caterpillar base as a bundled core -/

/-- **The genus-six caterpillar of loops as a connected cubic core.** -/
def catCubicCore : CoreOfDarts.CubicCore (4 * 2 + 2) (6 * 2 + 3) where
  core := catCore 2
  cubic := MemberCertifiedPencil.catCore_two_cubic
  connected := MemberCertifiedPencil.catCore_two_connected

@[simp] theorem catCubicCore_core : catCubicCore.core = catCore 2 := rfl

end DraismaVargas.Count.StepSupplyGenusSix
