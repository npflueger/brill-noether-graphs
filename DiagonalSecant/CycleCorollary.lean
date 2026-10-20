module

public import DiagonalSecant.Main
public import GenusSixExistence.OnceMarked

@[expose] public section

/-!
# Ramified pencils at two marks, from the diagonal secant theorem by a cycle gadget

> **Theorem.** Let `G` be a connected graph of genus `g ≥ 4` with `g ≡ 0` or `1 (mod 4)`, and
> `u, v` vertices. Then some effective `F` of degree two has `r((g − 2)u + F) ≥ 1` with
> `(g − 2)u + F − 2v` winnable: a `g^1_g` with a `(g − 2)`-fold point at `u` and a double point
> at `v`.

On a general twice-marked curve this is the ramification type `(g − 3, 1)` in degree `g`, whose
count is `C(g, 2) − 1 = (g + 1)(g − 2)/2`, the once-marked count `N(g + 1; g − 3, 0)` of genus
`g + 1`; it is odd exactly when `g ≡ 0, 1 (mod 4)`. The proof is that identity read
tropically. Attach a cycle at `v` (the digon `GenusSixExistence.digonSpec`). The wedge is
connected of genus `g + 1 ≡ 1, 2 (mod 4)`, so the diagonal secant theorem
(`DiagonalSecant.diagonalSecant`) at the mark `u` gives `(g − 2)u + F'` of rank at least one
there. Collapsing the cycle onto `v` (`Utilities.rank_wedgeCollapseLeft_ge_one`, the cycle being
pointed rigid of genus one) keeps the rank and makes the collapse minus `2v` winnable; the
collapse fixes `(g − 2)u` and sends `F'` to an effective `F` of the same degree.

Headline: `cycleSecant`, the theorem above. At `g = 4` it gives a pencil of degree four with a
double point at `u` and a double point at `v`, from the diagonal secant theorem in genus five.
-/

namespace DiagonalSecant

open Utilities GenusSixExistence

universe u v

section Collapse

variable (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)

/-- The right restriction of a wedge divisor ignores a left chip. -/
theorem wedgeRestrictRightDivisor_smul_inl_add (n : ℤ) (a : G.V)
    (Q : CFDiv (vertexWedge G H x y)) :
    wedgeRestrictRightDivisor G H x y (n • one_chip (Sum.inl a) + Q) =
      wedgeRestrictRightDivisor G H x y Q := by
  funext b
  by_cases hb : b = y
  · simp [wedgeRestrictRightDivisor, hb]
  · have hApply : (n • one_chip (Sum.inl a) + Q : CFDiv (vertexWedge G H x y))
        (Sum.inr ⟨b, hb⟩) = n * one_chip (G := vertexWedge G H x y) (Sum.inl a) (Sum.inr ⟨b, hb⟩) + Q (Sum.inr ⟨b, hb⟩) :=
      rfl
    simp only [wedgeRestrictRightDivisor, hb, dite_false, hApply]
    simp [one_chip]

/-- The left restriction of a wedge divisor reads a left chip as the same chip. -/
theorem wedgeRestrictLeftDivisor_smul_inl_add (n : ℤ) (a : G.V)
    (Q : CFDiv (vertexWedge G H x y)) :
    wedgeRestrictLeftDivisor G H x y (n • one_chip (Sum.inl a) + Q) =
      n • one_chip a + wedgeRestrictLeftDivisor G H x y Q := by
  funext b
  have hApply : (n • one_chip (Sum.inl a) + Q : CFDiv (vertexWedge G H x y)) (Sum.inl b) =
      n * one_chip (G := vertexWedge G H x y) (Sum.inl a) (Sum.inl b) + Q (Sum.inl b) := rfl
  have hApply' : (n • one_chip a + wedgeRestrictLeftDivisor G H x y Q : CFDiv G) b =
      n * one_chip a b + wedgeRestrictLeftDivisor G H x y Q b := rfl
  rw [hApply']
  simp only [wedgeRestrictLeftDivisor, hApply]
  simp only [one_chip, mul_ite, mul_one, mul_zero, ite_add, zero_add]
  split_ifs with hWedge hba hba
  · rfl
  · exact absurd (Sum.inl_injective hWedge) hba
  · exact absurd (hba ▸ rfl) hWedge
  · rfl

/-- Collapsing fixes a multiple of a left chip. -/
theorem wedgeCollapseLeft_smul_inl_add (n : ℤ) (a : G.V) (Q : CFDiv (vertexWedge G H x y)) :
    wedgeCollapseLeft G H x y (n • one_chip (Sum.inl a) + Q) =
      n • one_chip a + wedgeCollapseLeft G H x y Q := by
  rw [wedgeCollapseLeft, wedgeCollapseLeft, wedgeRestrictLeftDivisor_smul_inl_add,
    wedgeRestrictRightDivisor_smul_inl_add, add_assoc]

/-- Collapsing preserves effectivity. -/
theorem effective_wedgeCollapseLeft (Q : CFDiv (vertexWedge G H x y)) (hQ : effective Q) :
    effective (wedgeCollapseLeft G H x y Q) := by
  have hRight : effective (wedgeRestrictRightDivisor G H x y Q) := by
    intro b
    by_cases hb : b = y
    · simp [wedgeRestrictRightDivisor, hb]
    · simpa [wedgeRestrictRightDivisor, hb] using hQ (Sum.inr ⟨b, hb⟩)
  have hDeg := deg_of_eff_nonneg _ hRight
  intro a
  have hLeft : (0 : ℤ) ≤ wedgeRestrictLeftDivisor G H x y Q a := hQ (Sum.inl a)
  have hChip : (0 : ℤ) ≤ one_chip x a := by
    unfold one_chip
    split_ifs <;> norm_num
  simp only [wedgeCollapseLeft, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have := mul_nonneg hDeg hChip
  linarith

end Collapse

/-- **Ramified pencils at two marks.** On every connected graph `G` of genus `g ≥ 4` with
`g ≡ 0` or `1 (mod 4)`, and every pair of vertices `u, v`, some effective divisor `F` of degree
two has `rank ((g − 2) • u + F) ≥ 1` and `(g − 2) • u + F − 2 • v` winnable. -/
theorem cycleSecant (G : CFGraph.{0}) (hG : graph_connected G) (hg4 : 4 ≤ genus G)
    (hmod : genus G % 4 = 0 ∨ genus G % 4 = 1) (u v : G.V) :
    ∃ F : CFDiv G, effective F ∧ deg F = 2 ∧
      rank G ((genus G - 2) • one_chip u + F) ≥ 1 ∧
      winnable G ((genus G - 2) • one_chip u + F - (2 : ℤ) • one_chip v) := by
  have hW : graph_connected (vertexWedge G digonSpec.graph v digonMark) :=
    graph_connected_vertexWedge G _ v _ hG (TwoPathCycle.connected _ _)
  have hWGenus : genus (vertexWedge G digonSpec.graph v digonMark) = genus G + 1 := by
    rw [genus_vertexWedge, TwoPathCycle.genus_one]
  obtain ⟨F', hF'eff, hF'deg, hF'rank⟩ :=
    diagonalSecant _ hW (by omega) (by omega) (Sum.inl u)
  obtain ⟨hRank, hWin⟩ := rank_wedgeCollapseLeft_ge_one G digonSpec.graph v digonMark
    (TwoPathCycle.pointedGenusOneRigid _ _ digonMark) _ hF'rank
  have hCollapse : wedgeCollapseLeft G digonSpec.graph v digonMark
      ((genus (vertexWedge G digonSpec.graph v digonMark) - 3) • one_chip (Sum.inl u) + F') =
        (genus G - 2) • one_chip u + wedgeCollapseLeft G digonSpec.graph v digonMark F' := by
    rw [wedgeCollapseLeft_smul_inl_add, hWGenus]
    congr 2
    ring
  rw [hCollapse] at hRank hWin
  refine ⟨wedgeCollapseLeft G digonSpec.graph v digonMark F',
    effective_wedgeCollapseLeft _ _ _ _ F' hF'eff, ?_, hRank, hWin⟩
  rw [deg_wedgeCollapseLeft, hF'deg]

end DiagonalSecant
