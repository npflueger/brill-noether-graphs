import GenusSixExistence.OnceMarked.OnceMarkedLowGenus
import GenusSixExistence.OnceMarked.MarkedGenusFive

/-!
# Once-marked Brill--Noether existence in genus five

For a connected graph of genus five, the entire once-marked existence
statement has one genuinely new partition orbit.  Hooks are supplied by
marked Riemann--Roch, the square `(2,2)` follows from ordinary degree-four
rank-one existence, and transposition pairs `(3,2)` with `(2,2,1)`.

On the diagonal, the remaining `(3,2)` condition says exactly that two chips
at the marked point can be completed by an effective divisor of degree two to
a divisor of rank one.  Thus genus-five once-marked Brill--Noether existence
is equivalent to `MarkedRankOneCompletion G u u`.
-/

namespace MarkedGraphs

open Utilities

/-- The Young diagram `(3,2)`, the unique new transpose orbit in genus five. -/
def threeTwoYoungDiagram : YoungDiagram :=
  YoungDiagram.ofRowLens [3, 2] (by decide)

@[simp] theorem threeTwoYoungDiagram_rowLens :
    threeTwoYoungDiagram.rowLens = [3, 2] := by
  exact YoungDiagram.rowLens_ofRowLens_eq_self (by simp)

/-- The diagonal marked completion problem supplies ordinary degree-four,
rank-one Brill--Noether existence. -/
theorem BNExists_one_four_of_markedRankOneCompletion_diagonal
    (G : CFGraph) (u : G.V) :
    MarkedRankOneCompletion G u u -> BNExists G 1 4 := by
  rintro ⟨E, hEEffective, hEDegree, hRank⟩
  refine ⟨one_chip u + one_chip u + E, ?_, hRank⟩
  rw [deg.map_add, deg.map_add, hEDegree]
  norm_num

/-- In genus five, the pointed partition `(3,2)` is exactly diagonal marked
rank-one completion. -/
theorem onceMarkedBNExists_iff_markedRankOneCompletion_of_rowLens_eq_three_two
    (G : CFGraph) (hFive : genus G = 5) (u : G.V)
    (lambda : YoungDiagram) (hRows : lambda.rowLens = [3, 2]) :
    OnceMarkedBNExists G u lambda <-> MarkedRankOneCompletion G u u := by
  rw [onceMarkedBNExists_iff_rank_rows]
  constructor
  · rintro ⟨D, hDDegree, hRanks⟩
    have hFirst := hRanks 0 (by simp [hRows])
    have hSecond := hRanks 1 (by simp [hRows])
    have hFirst' :
        rank G (D + ((0 : ℤ) - 3) • one_chip u) >= 0 := by
      simpa [hRows] using hFirst
    have hSecond' :
        rank G (D + ((1 : ℤ) - 2) • one_chip u) >= 1 := by
      simpa [hRows] using hSecond
    have hFirstTwist :
        D + ((0 : ℤ) - 3) • one_chip u =
          D - (3 : ℤ) • one_chip u := by
      funext v
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hSecondTwist :
        D + ((1 : ℤ) - 2) • one_chip u = D - one_chip u := by
      funext v
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hFirstTwist] at hFirst'
    rw [hSecondTwist] at hSecond'
    have hFirstWinnable : winnable G (D - (3 : ℤ) • one_chip u) := by
      apply (rank_nonneg_iff_winnable G _).mp
      exact (rank_geq_iff G _ 0).mpr hFirst'
    obtain ⟨E, hEEffective, hResidualEquiv⟩ :=
      (winnable_iff_exists_effective G
        (D - (3 : ℤ) • one_chip u)).mp hFirstWinnable
    have hEDegree : deg E = 2 := by
      have hDegreeEq := linear_equiv_preserves_deg G
        (D - (3 : ℤ) • one_chip u) E hResidualEquiv
      rw [deg.map_sub, map_zsmul, deg_one_chip, hDDegree, hFive] at hDegreeEq
      norm_num at hDegreeEq ⊢
      exact hDegreeEq.symm
    have hRankEquiv :
        linear_equiv G (D - one_chip u)
          (one_chip u + one_chip u + E) := by
      unfold linear_equiv at hResidualEquiv ⊢
      have hDifference :
          (one_chip u + one_chip u + E) - (D - one_chip u) =
            E - (D - (3 : ℤ) • one_chip u) := by
        funext v
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hDifference]
      exact hResidualEquiv
    refine ⟨E, hEEffective, hEDegree, ?_⟩
    rw [← rank_eq_of_linear_equiv G hRankEquiv]
    exact hSecond'
  · rintro ⟨E, hEEffective, hEDegree, hRank⟩
    let D : CFDiv G := (3 : ℤ) • one_chip u + E
    refine ⟨D, ?_, ?_⟩
    · dsimp [D]
      rw [deg.map_add, map_zsmul, deg_one_chip, hEDegree, hFive]
      norm_num
    · intro i hi
      have hi' : i < [3, 2].length := by simpa [hRows] using hi
      have hiCases : i = 0 ∨ i = 1 := by
        simp at hi'
        omega
      rcases hiCases with rfl | rfl
      · simp only [hRows]
        change rank G (D + ((0 : ℤ) - 3) • one_chip u) >= 0
        have hRewrite :
            D + ((0 : ℤ) - 3) • one_chip u = E := by
          dsimp [D]
          funext v
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [hRewrite]
        apply (rank_geq_iff G E 0).mp
        apply (rank_nonneg_iff_winnable G E).mpr
        exact winnable_of_effective G E hEEffective
      · simp only [hRows]
        change rank G (D + ((1 : ℤ) - 2) • one_chip u) >= 1
        have hRewrite :
            D + ((1 : ℤ) - 2) • one_chip u =
              one_chip u + one_chip u + E := by
          dsimp [D]
          funext v
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [hRewrite]
        exact hRank

/-- The decreasing positive partitions of five. -/
private theorem sortedPositive_sum_eq_five_cases
    (rows : List ℕ) (hs : rows.SortedGE)
    (hp : ∀ x ∈ rows, 0 < x) (hSum : rows.sum = 5) :
    rows = [5] ∨
      rows = [4, 1] ∨
      rows = [3, 2] ∨
      rows = [3, 1, 1] ∨
      rows = [2, 2, 1] ∨
      rows = [2, 1, 1, 1] ∨
      rows = [1, 1, 1, 1, 1] := by
  rcases rows with _ | ⟨a, rows⟩
  · simp_all
  rcases rows with _ | ⟨b, rows⟩
  · simp_all [List.sortedGE_iff_pairwise]
  rcases rows with _ | ⟨c, rows⟩
  · simp_all [List.sortedGE_iff_pairwise]
    omega
  rcases rows with _ | ⟨d, rows⟩
  · simp_all [List.sortedGE_iff_pairwise]
    omega
  rcases rows with _ | ⟨e, rows⟩
  · simp_all [List.sortedGE_iff_pairwise]
    omega
  rcases rows with _ | ⟨f, rows⟩
  · simp_all [List.sortedGE_iff_pairwise]
    omega
  simp_all
  omega

/-- A Young diagram is determined by its row-length list. -/
private theorem youngDiagram_eq_of_rowLens_eq_genus_five
    (lambda : YoungDiagram) (rows : List ℕ) (hs : rows.SortedGE)
    (hRows : lambda.rowLens = rows) :
    lambda = YoungDiagram.ofRowLens rows hs := by
  subst rows
  exact YoungDiagram.ofRowLens_to_rowLens_eq_self.symm

private theorem transpose_rowLens_eq_three_two
    (lambda : YoungDiagram) (hRows : lambda.rowLens = [2, 2, 1]) :
    lambda.transpose.rowLens = [3, 2] := by
  let hs : [2, 2, 1].SortedGE := by decide
  let hst : [3, 2].SortedGE := by decide
  rw [youngDiagram_eq_of_rowLens_eq_genus_five lambda [2, 2, 1] hs hRows]
  have hDiagram :
      (YoungDiagram.ofRowLens [2, 2, 1] hs).transpose =
        YoungDiagram.ofRowLens [3, 2] hst := by
    apply YoungDiagram.ext
    decide
  rw [hDiagram]
  exact YoungDiagram.rowLens_ofRowLens_eq_self (by simp)

/-- For a connected genus-five graph, the complete once-marked
Brill--Noether existence statement is equivalent to the single diagonal
marked rank-one completion problem. -/
theorem onceMarkedBNExistence_iff_markedRankOneCompletion_genus_five
    (G : CFGraph) (hG : graph_connected G) (hFive : genus G = 5)
    (u : G.V) :
    OnceMarkedBNExistence G u <-> MarkedRankOneCompletion G u u := by
  constructor
  · intro hMarked
    have hSize : (threeTwoYoungDiagram.card : ℤ) <= genus G := by
      rw [← youngDiagram_rowLens_sum_eq_card]
      simp [hFive]
    exact
      (onceMarkedBNExists_iff_markedRankOneCompletion_of_rowLens_eq_three_two
        G hFive u threeTwoYoungDiagram threeTwoYoungDiagram_rowLens).mp
        (hMarked threeTwoYoungDiagram hSize)
  · intro hCompletion lambda hSize
    have hSizeRows : (lambda.rowLens.sum : ℤ) <= genus G := by
      rw [youngDiagram_rowLens_sum_eq_card]
      exact hSize
    have hSizeFive : lambda.rowLens.sum <= 5 := by
      exact_mod_cast hSizeRows.trans_eq hFive
    have hBNFour : BNExists G 1 (genus G - 1) := by
      have h := BNExists_one_four_of_markedRankOneCompletion_diagonal
        G u hCompletion
      simpa [hFive] using h
    by_cases hAtMostFour : lambda.rowLens.sum <= 4
    · have hOrbit := rowLens_mem_genusFourRepresentativeRows_or_transpose
        lambda hAtMostFour
      rcases hOrbit with hDirect | hTranspose
      · exact onceMarkedBNExists_of_mem_genusFourPartitionRows
          G hG u lambda hSizeRows hDirect (fun _ => hBNFour)
      · apply (onceMarkedBNExists_transpose_iff hG u lambda).mpr
        apply onceMarkedBNExists_of_mem_genusFourPartitionRows
          G hG u lambda.transpose
        · rw [youngDiagram_rowLens_sum_eq_card,
              youngDiagram_transpose_card,
              ← youngDiagram_rowLens_sum_eq_card]
          exact hSizeRows
        · exact hTranspose
        · intro _
          exact hBNFour
    · have hSumFive : lambda.rowLens.sum = 5 := by omega
      have hCases := sortedPositive_sum_eq_five_cases
        lambda.rowLens lambda.rowLens_sorted lambda.pos_of_mem_rowLens hSumFive
      rcases hCases with hRows | hRows | hRows | hRows | hRows | hRows | hRows
      · apply onceMarkedBNExists_of_rowLens_eq_singleton
          G u lambda 5 hRows
        omega
      · apply onceMarkedBNExists_of_rowLens_eq_hook
          G hG u lambda 4 1 hRows
        · omega
        · omega
        · omega
      · exact
          (onceMarkedBNExists_iff_markedRankOneCompletion_of_rowLens_eq_three_two
            G hFive u lambda hRows).mpr hCompletion
      · apply onceMarkedBNExists_of_rowLens_eq_hook
          G hG u lambda 3 2 hRows
        · omega
        · omega
        · omega
      · apply (onceMarkedBNExists_transpose_iff hG u lambda).mpr
        apply
          (onceMarkedBNExists_iff_markedRankOneCompletion_of_rowLens_eq_three_two
            G hFive u lambda.transpose
              (transpose_rowLens_eq_three_two lambda hRows)).mpr
        exact hCompletion
      · apply onceMarkedBNExists_of_rowLens_eq_hook
          G hG u lambda 2 3 hRows
        · omega
        · omega
        · omega
      · apply onceMarkedBNExists_of_rowLens_eq_hook
          G hG u lambda 1 4 hRows
        · omega
        · omega
        · omega

end MarkedGraphs
