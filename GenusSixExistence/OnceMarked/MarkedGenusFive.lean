module

public import Utilities.Foundations.ConditionalInduction
public import Utilities.Foundations.CommonComplement
public import Utilities.Transmission.TransmissionCorner

@[expose] public section

/-!
# The marked genus-five transmission profile

This file concerns the following marked statement about a graph `H` of genus five with two
marked vertices `x` and `y`: there is a degree-four rank-one divisor `D` such that `D - x - y`
is winnable.  This is `NearRectangle H x y 1 4`.

The marked condition is encoded by a two-corner transmission profile.  Its
central row asks for rank one, while the row at `(-1,1)` asks that the two
marked chips can be removed.  The ASP permutation with this profile has shift `-1`, finite
core `(2,3,1,0)`, and inversion length five.

This file isolates the graph-theoretic part of that identification.  Once an
ASP permutation is shown to have the stated two-corner profile, transmission
existence for it is *equivalent* to the marked genus-five near rectangle.
-/

namespace MarkedGraphs

open Utilities

/-- Every prescribed effective pair `x+y` can be completed by two effective
chips to a degree-four rank-one divisor. -/
def MarkedRankOneCompletion (H : CFGraph) (x y : H.V) : Prop :=
  ∃ E : CFDiv H,
    effective E ∧
    deg E = 2 ∧
    rank H (one_chip x + one_chip y + E) ≥ 1

/-- The effective-completion formulation is exactly the near-rectangle
formulation used by edge induction.  This equivalence does not require a genus
assumption. -/
theorem markedRankOneCompletion_iff_nearRectangle
    (H : CFGraph) (x y : H.V) :
    MarkedRankOneCompletion H x y ↔ NearRectangle H x y 1 4 := by
  constructor
  · rintro ⟨E, hEEffective, hEDegree, hRank⟩
    refine ⟨one_chip x + one_chip y + E, ?_, hRank, ?_⟩
    · rw [deg.map_add, deg.map_add, deg_one_chip, deg_one_chip, hEDegree]
      norm_num
    · have hDifference :
          one_chip x + one_chip y + E - one_chip x - one_chip y = E := by
        abel
      rw [hDifference]
      apply (rank_geq_iff H E 0).mp
      apply (rank_nonneg_iff_winnable H E).mpr
      exact winnable_of_effective H E hEEffective
  · rintro ⟨D, hDDegree, hDRank, hSecantRank⟩
    have hSecantRankGeq :
        rank_geq H (D - one_chip x - one_chip y) 0 :=
      (rank_geq_iff H (D - one_chip x - one_chip y) 0).mpr hSecantRank
    have hSecantWinnable : winnable H (D - one_chip x - one_chip y) :=
      (rank_nonneg_iff_winnable H (D - one_chip x - one_chip y)).mp
        hSecantRankGeq
    obtain ⟨E, hEEffective, hSecantEquiv⟩ :=
      (winnable_iff_exists_effective H
        (D - one_chip x - one_chip y)).mp hSecantWinnable
    have hEDegree : deg E = 2 := by
      have hDegreeEq := linear_equiv_preserves_deg H
        (D - one_chip x - one_chip y) E hSecantEquiv
      rw [deg.map_sub, deg.map_sub, deg_one_chip, deg_one_chip, hDDegree] at hDegreeEq
      omega
    have hDEquiv :
        linear_equiv H D (one_chip x + one_chip y + E) := by
      unfold linear_equiv at hSecantEquiv ⊢
      have hDifference :
          (one_chip x + one_chip y + E) - D =
            E - (D - one_chip x - one_chip y) := by
        abel
      rw [hDifference]
      exact hSecantEquiv
    refine ⟨E, hEEffective, hEDegree, ?_⟩
    rw [← rank_eq_of_linear_equiv H hDEquiv]
    exact hDRank

/-- Pairwise intersection in the T2a Helly formulation is automatic.  A
degree-six rank-two divisor admits a degree-two effective subtraction whose
residual can still pay either of two prescribed vertices.

The proof is the exact common-complement argument: make `B-v-w` effective,
split that degree-four representative into `E+F`, and use `F+w` and `F+v` as
the two effective residual representatives. -/
theorem exists_pairwise_rank_one_subtraction
    (H : CFGraph) (B : CFDiv H) (v w : H.V)
    (hBDegree : deg B = 6) (hBRank : rank H B ≥ 2) :
    ∃ E : CFDiv H,
      effective E ∧
      deg E = 2 ∧
      winnable H (B - one_chip v - E) ∧
      winnable H (B - one_chip w - E) := by
  let A : CFDiv H := one_chip v + one_chip w
  have hAEffective : effective A :=
    (Eff H).add_mem (eff_one_chip v) (eff_one_chip w)
  have hADegree : deg A = 2 := by
    simp [A]
  have hResidualWinnable : winnable H (B - A) :=
    winnable_sub_effective_of_rank_ge B A 2
      hBRank hAEffective hADegree
  obtain ⟨M, hMEffective, hResidualEquiv⟩ :=
    (winnable_iff_exists_effective H (B - A)).mp hResidualWinnable
  have hMDegree : deg M = (2 : ℕ) + (2 : ℕ) := by
    have hDegreeEq :=
      linear_equiv_preserves_deg H (B - A) M hResidualEquiv
    dsimp [A] at hDegreeEq
    rw [deg.map_sub, deg.map_add, deg_one_chip, deg_one_chip, hBDegree] at hDegreeEq
    norm_num at hDegreeEq ⊢
    exact hDegreeEq.symm
  obtain ⟨E, F, hEEffective, hFEffective, hEDegree, _hFDegree, hMSplit⟩ :=
    effective_divisor_decomposition H M 2 2 hMEffective hMDegree
  have hFirstEquiv :
      linear_equiv H (B - one_chip v - E) (F + one_chip w) := by
    unfold linear_equiv at hResidualEquiv ⊢
    rw [hMSplit] at hResidualEquiv
    have hDifference :
        (F + one_chip w) - (B - one_chip v - E) =
          (E + F) - (B - A) := by
      dsimp [A]
      abel
    rw [hDifference]
    exact hResidualEquiv
  have hSecondEquiv :
      linear_equiv H (B - one_chip w - E) (F + one_chip v) := by
    unfold linear_equiv at hResidualEquiv ⊢
    rw [hMSplit] at hResidualEquiv
    have hDifference :
        (F + one_chip v) - (B - one_chip w - E) =
          (E + F) - (B - A) := by
      dsimp [A]
      abel
    rw [hDifference]
    exact hResidualEquiv
  have hFirstEffective : effective (F + one_chip w) :=
    (Eff H).add_mem hFEffective (eff_one_chip w)
  have hSecondEffective : effective (F + one_chip v) :=
    (Eff H).add_mem hFEffective (eff_one_chip v)
  have hFirstWinnable : winnable H (B - one_chip v - E) :=
    winnable_equiv_winnable H (F + one_chip w)
      (B - one_chip v - E)
      (winnable_of_effective H (F + one_chip w) hFirstEffective)
      hFirstEquiv.symm
  have hSecondWinnable : winnable H (B - one_chip w - E) :=
    winnable_equiv_winnable H (F + one_chip v)
      (B - one_chip w - E)
      (winnable_of_effective H (F + one_chip v) hSecondEffective)
      hSecondEquiv.symm
  exact ⟨E, hEEffective, hEDegree, hFirstWinnable, hSecondWinnable⟩

/-- Numerical and corner data for the minimal transmission permutation that
encodes the marked genus-five completion problem.

The two corners are `(0,0,1)` and `(-1,1,0)`: respectively
`rank D ≥ 1` and `rank (D-x-y) ≥ 0`. -/
def MarkedGenusFiveTransmissionProfile (τ : AspPerm) : Prop :=
  τ.χ = -1 ∧
  τ.s 1 0 = 2 ∧
  τ.s 0 1 = 1 ∧
  CornersDominate τ [(0, 0, 1), (-1, 1, 0)]

/-- For a connected genus-five graph, transmission existence for any ASP
permutation with the marked two-corner profile is equivalent to the marked
near-rectangle statement `NearRectangle H x y 1 4`. -/
theorem transmissionExists_iff_nearRectangle_genus_five
    (H : CFGraph) (hH : graph_connected H) (hGenus : genus H = 5)
    (x y : H.V) (τ : AspPerm)
    (hProfile : MarkedGenusFiveTransmissionProfile τ) :
    TransmissionExists H x y τ ↔ NearRectangle H x y 1 4 := by
  rcases hProfile with ⟨hChi, hCentral, hSecant, hDom⟩
  constructor
  · rintro ⟨D, hTransmission⟩
    have hDegree := degree_of_satisfiesTransmission hTransmission
    have hCentralRank :=
      rank_twist_of_satisfiesTransmission hTransmission 0 0
    have hSecantRank :=
      rank_twist_of_satisfiesTransmission hTransmission (-1) 1
    refine ⟨D, ?_, ?_, ?_⟩
    · rw [hChi, hGenus] at hDegree
      norm_num at hDegree ⊢
      exact hDegree
    · norm_num at hCentralRank
      rw [hCentral] at hCentralRank
      omega
    · norm_num at hSecantRank
      rw [hSecant] at hSecantRank
      have hTwist :
          D + -one_chip x - one_chip y =
            D - one_chip x - one_chip y := by
        abel
      rw [hTwist] at hSecantRank
      simpa using hSecantRank
  · rintro ⟨D, hDegree, hRank, hSecantRank⟩
    refine ⟨D, satisfiesTransmission_of_corners
      hH x y τ D [(0, 0, 1), (-1, 1, 0)] ?_ hDom ?_⟩
    · rw [hChi, hGenus]
      norm_num
      exact hDegree
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · simpa using hRank
      · have hTwist :
            D + (-1 : ℤ) • one_chip x - (1 : ℤ) • one_chip y =
              D - one_chip x - one_chip y := by
          funext z
          simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        dsimp only
        rw [hTwist]
        simpa using hSecantRank

/-- Combining the two equivalences gives the original effective-completion
form of the marked genus-five problem. -/
theorem transmissionExists_iff_markedRankOneCompletion_genus_five
    (H : CFGraph) (hH : graph_connected H) (hGenus : genus H = 5)
    (x y : H.V) (τ : AspPerm)
    (hProfile : MarkedGenusFiveTransmissionProfile τ) :
    TransmissionExists H x y τ ↔ MarkedRankOneCompletion H x y := by
  rw [markedRankOneCompletion_iff_nearRectangle]
  exact transmissionExists_iff_nearRectangle_genus_five
    H hH hGenus x y τ hProfile

end MarkedGraphs
