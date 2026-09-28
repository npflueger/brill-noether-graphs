import Utilities.Gluing.VertexWedgeGenusOne
import Utilities.Gluing.VertexWedgeRankFormula

/-!
# Collapsing a rigid genus-one wedge

`rank_wedgeLiftLeft_ge_one_iff` (in `Utilities/Gluing/VertexWedgeGenusOne.lean`)
is the exact rank-one criterion for a divisor supported on the left factor of
`vertexWedge G H x y`, when `H` is a pointed rigid genus-one graph:

`rank (lift D) ≥ 1 ↔ rank G D ≥ 1 ∧ D - 2x winnable`.

This module supplies the missing half for an *arbitrary* wedge divisor. Collapse
the right factor onto the common vertex. That is, keep the left restriction and
add all the degree carried by `H` as chips at `x`. The collapsed divisor has the
same degree, has rank at least one, and contains `2x`
(`rank_wedgeCollapseLeft_ge_one`). Together the two halves give

`BNExists (vertexWedge G H x y) 1 d ↔
  ∃ D, deg D = d ∧ rank G D ≥ 1 ∧ winnable G (D - 2x)`

(`bnExists_vertexWedge_one_iff`). This is the tropical form of the elliptic-tail
argument: a pencil on `G` with a genus-one cycle attached at `x` is a pencil on
`G` with a cusp at `x`.

The proof uses only the winnability convolution
`winnable_vertexWedge_iff_exists_chipShift`, at every left vertex and at one
non-marked vertex of `H`. The degree bound `deg ≥ 0` for winnable divisors
controls every left test. Rigidity (`y - p` is not principal on `H`) excludes
the one boundary case of the right test.
-/

namespace Utilities

universe u v

/-- Collapse a wedge divisor onto the left factor. Every chip of the right
factor, including its share of the common vertex, is moved to the common
vertex `x`. -/
def wedgeCollapseLeft (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (Q : CFDiv (vertexWedge G H x y)) : CFDiv G :=
  wedgeRestrictLeftDivisor G H x y Q +
    deg (wedgeRestrictRightDivisor G H x y Q) • one_chip x

/-- Collapsing preserves degree. -/
theorem deg_wedgeCollapseLeft (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V) (Q : CFDiv (vertexWedge G H x y)) :
    deg (wedgeCollapseLeft G H x y Q) = deg Q := by
  rw [wedgeCollapseLeft, deg.map_add, map_zsmul, deg_one_chip, smul_eq_mul, mul_one,
    deg_wedgeRestrictions]

/-- A left chip of the wedge is the wedge sum of a left chip and zero. -/
theorem one_chip_inl_eq_wedgeAddDivisor (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V) (a : G.V) :
    one_chip (G := vertexWedge G H x y) (Sum.inl a) =
      wedgeAddDivisor G H x y (one_chip a) 0 := by
  funext z
  cases z with
  | inl q =>
      rw [wedgeAddDivisor_left]
      change (if (Sum.inl q : Sum G.V {b : H.V // b ≠ y}) = Sum.inl a then 1 else 0) =
        (if q = a then 1 else 0) + if q = x then 0 else 0
      simp
  | inr q =>
      rw [wedgeAddDivisor_right]
      simp [one_chip]

/-- A non-marked right chip of the wedge is the wedge sum of zero and a right
chip. -/
theorem one_chip_inr_eq_wedgeAddDivisor (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V) (p : {b : H.V // b ≠ y}) :
    one_chip (G := vertexWedge G H x y) (Sum.inr p) =
      wedgeAddDivisor G H x y 0 (one_chip p.1) := by
  funext z
  cases z with
  | inl q =>
      rw [wedgeAddDivisor_left]
      change (if (Sum.inl q : Sum G.V {b : H.V // b ≠ y}) = Sum.inr p then 1 else 0) =
        0 + if q = x then (if y = p.1 then 1 else 0) else 0
      simp [Ne.symm p.2]
  | inr q =>
      rw [wedgeAddDivisor_right]
      change (if (Sum.inr q : Sum G.V {b : H.V // b ≠ y}) = Sum.inr p then 1 else 0) =
        (if q.1 = p.1 then 1 else 0)
      simp [Subtype.ext_iff]

/-- The chip-shift allocated to a winnable right factor is bounded by that
factor's degree. -/
theorem le_deg_of_winnable_chipShift_neg (H : CFGraph.{v}) (B : CFDiv H)
    (y : H.V) (t : ℤ) (hWin : winnable H (chipShift H B y (-t))) :
    t ≤ deg B := by
  have hDegree := deg_nonneg_of_winnable H _ hWin
  rw [chipShift, deg.map_add, map_zsmul, deg_one_chip, smul_eq_mul, mul_one] at hDegree
  omega

/-- **Collapsing a rigid genus-one wedge.** If `H` is a pointed rigid
genus-one graph and `Q` has rank at least one on `vertexWedge G H x y`, then
the collapsed divisor has rank at least one on `G` and contains `2x`. -/
theorem rank_wedgeCollapseLeft_ge_one
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (hH : PointedGenusOneRigid H y) (Q : CFDiv (vertexWedge G H x y))
    (hQ : rank (vertexWedge G H x y) Q ≥ 1) :
    rank G (wedgeCollapseLeft G H x y Q) ≥ 1 ∧
      winnable G (wedgeCollapseLeft G H x y Q - (2 : ℤ) • one_chip x) := by
  set A := wedgeRestrictLeftDivisor G H x y Q with hA
  set B := wedgeRestrictRightDivisor G H x y Q with hB
  have hQsplit : Q = wedgeAddDivisor G H x y A B :=
    (wedgeAddDivisor_restrict G H x y Q).symm
  have hTests := (rank_ge_one_iff_winnable_sub_one_chip _ Q).mp hQ
  -- The left test at `a` moves the whole right degree to `x`.
  have hLeftTest : ∀ a : G.V, ∃ t : ℤ, t ≤ deg B ∧
      winnable G (chipShift G (A - one_chip a) x t) ∧
      winnable H (chipShift H B y (-t)) := by
    intro a
    have hWin := hTests (Sum.inl a)
    rw [hQsplit, one_chip_inl_eq_wedgeAddDivisor, wedgeAddDivisor_sub, sub_zero] at hWin
    obtain ⟨t, hLeft, hRight⟩ :=
      (winnable_vertexWedge_iff_exists_chipShift G H x y _ _).mp hWin
    exact ⟨t, le_deg_of_winnable_chipShift_neg H B y t hRight, hLeft, hRight⟩
  have hShift : ∀ (a : G.V) (s : ℤ),
      chipShift G (A - one_chip a) x s = A - one_chip a + s • one_chip x := fun _ _ => rfl
  constructor
  · rw [rank_ge_one_iff_winnable_sub_one_chip]
    intro a
    obtain ⟨t, ht, hLeft, _⟩ := hLeftTest a
    have hMono := winnable_add_zsmul_one_chip_mono G (A - one_chip a) x t (deg B) ht
      (by rw [← hShift]; exact hLeft)
    convert hMono using 1
    rw [wedgeCollapseLeft]
    abel
  · have hGoal : wedgeCollapseLeft G H x y Q - (2 : ℤ) • one_chip x =
        A - one_chip x + (deg B - 1) • one_chip x := by
      rw [wedgeCollapseLeft, sub_smul, one_smul, two_smul]
      abel
    rw [hGoal]
    obtain ⟨s, hs, hLeft, hRight⟩ := hLeftTest x
    rw [hShift] at hLeft
    by_cases hsLow : s ≤ deg B - 1
    · exact winnable_add_zsmul_one_chip_mono G _ x s _ hsLow hLeft
    -- Boundary case: the right factor absorbs its whole degree at `y`.
    have hsEq : s = deg B := by omega
    subst hsEq
    have hZeroB := linear_equiv_zero_of_winnable_deg_zero H _ hRight (by
      rw [chipShift, deg.map_add, map_zsmul, deg_one_chip]
      simp)
    obtain ⟨p, hp⟩ := hH.exists_ne
    have hWin := hTests (Sum.inr ⟨p, hp⟩)
    rw [hQsplit, one_chip_inr_eq_wedgeAddDivisor, wedgeAddDivisor_sub, sub_zero] at hWin
    obtain ⟨t, hLeftT, hRightT⟩ :=
      (winnable_vertexWedge_iff_exists_chipShift G H x y _ _).mp hWin
    have ht : t ≤ deg B - 1 := by
      have := le_deg_of_winnable_chipShift_neg H _ y t hRightT
      rw [deg.map_sub, deg_one_chip] at this
      exact this
    by_cases htLow : t ≤ deg B - 2
    · have hMono := winnable_add_zsmul_one_chip_mono G A x t (deg B - 2) htLow hLeftT
      convert hMono using 1
      rw [sub_smul, sub_smul, one_smul, two_smul]
      abel
    -- Second boundary case: `y - p` would be principal on `H`.
    exfalso
    have htEq : t = deg B - 1 := by omega
    subst htEq
    have hZeroP := linear_equiv_zero_of_winnable_deg_zero H _ hRightT (by
      rw [chipShift, deg.map_add, deg.map_sub, map_zsmul, deg_one_chip, deg_one_chip]
      simp)
    apply hH.nontrivial p hp
    have hDiff : (0 : CFDiv H) - (one_chip y - one_chip p) =
        ((0 : CFDiv H) - chipShift H (B - one_chip p) y (-(deg B - 1))) -
          ((0 : CFDiv H) - chipShift H B y (-deg B)) := by
      rw [chipShift, chipShift, neg_sub, neg_smul, sub_smul, one_smul]
      abel
    unfold linear_equiv at hZeroB hZeroP ⊢
    rw [hDiff]
    exact (principal_divisors H).sub_mem hZeroP hZeroB

/-- **Rank-one pencils on a rigid genus-one wedge.** A degree-`d` divisor of
rank at least one exists on `vertexWedge G H x y` exactly when `G` has one that
contains `2x`. -/
theorem bnExists_vertexWedge_one_iff
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (hH : PointedGenusOneRigid H y) (d : ℤ) :
    BNExists (vertexWedge G H x y) 1 d ↔
      ∃ D : CFDiv G, deg D = d ∧ rank G D ≥ 1 ∧
        winnable G (D - (2 : ℤ) • one_chip x) := by
  constructor
  · rintro ⟨Q, hDeg, hRank⟩
    obtain ⟨hRankD, hTwo⟩ := rank_wedgeCollapseLeft_ge_one G H x y hH Q hRank
    exact ⟨wedgeCollapseLeft G H x y Q, by rw [deg_wedgeCollapseLeft, hDeg], hRankD, hTwo⟩
  · rintro ⟨D, hDeg, hRank, hTwo⟩
    exact ⟨wedgeLiftLeftDivisor G H x y D, by rw [deg_wedgeLiftLeftDivisor, hDeg],
      (rank_wedgeLiftLeft_ge_one_iff G H x y hH D).mpr ⟨hRank, hTwo⟩⟩

end Utilities
