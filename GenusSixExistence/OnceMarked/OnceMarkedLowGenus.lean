module

public import Utilities.Grassmannian.OnceMarked
public import GenusSixExistence.OnceMarked.OnceMarkedGenusFourCatalog

@[expose] public section

/-!
# Once-marked Brill--Noether existence through genus four

Every nonempty partition of size at most four is either a hook or the square
`(2,2)`.  The hook cases are unconditional Riemann--Roch splittings.  The
square case is exactly ordinary genus-four `W^1_3` existence.  This file makes
that reduction precise; the square case is then discharged route by route from the generated
catalogue `OnceMarkedGenusFourCatalog`.
-/

namespace MarkedGraphs

open Utilities

/-- Compressed normalized rank conditions for the hook partition
`(a, 1, ..., 1)` with `b` trailing ones.  The intermediate rows follow from
the last row by removing chips at `u`. -/
def HookPartitionExists (G : CFGraph) (u : G.V) (a b : ℕ) : Prop :=
  ∃ D : CFDiv G,
    deg D = genus G ∧
    rank G (D - (a : ℤ) • one_chip u) ≥ 0 ∧
    rank G (D + ((b : ℤ) - 1) • one_chip u) ≥ (b : ℤ)

/-- Every hook of size at most the genus occurs in the once-marked divisor
census.  This is stronger than the genus-four application. -/
theorem hookPartitionExists
    (G : CFGraph) (hG : graph_connected G) (u : G.V)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hSize : (a : ℤ) + (b : ℤ) ≤ genus G) :
    HookPartitionExists G u a b := by
  let B : CFDiv G := ((a : ℤ) + (b : ℤ) - 1) • one_chip u
  have hBNonneg : 0 ≤ (a : ℤ) + (b : ℤ) - 1 := by omega
  have hBEff : effective B := by
    dsimp [B, effective]
    intro v
    by_cases h : v = u
    · subst v
      simp [one_chip]
      omega
    · simp [one_chip, h]
  have hBDeg : deg B = (a : ℤ) + (b : ℤ) - 1 := by
    dsimp [B]
    rw [map_zsmul, deg_one_chip]
    change ((a : ℤ) + (b : ℤ) - 1) * 1 = _
    ring
  have hBRank : rank G B ≥ 0 := by
    apply (rank_geq_iff G B 0).mp
    apply (rank_nonneg_iff_winnable G B).mpr
    exact winnable_of_effective G B hBEff
  have hCompRank : rank G (canonical_divisor G - B) ≥ 0 := by
    have hRR := riemann_roch_for_graphs hG B
    rw [hBDeg] at hRR
    omega
  have hCompWin : winnable G (canonical_divisor G - B) := by
    apply (rank_nonneg_iff_winnable G (canonical_divisor G - B)).mp
    exact (rank_geq_iff G (canonical_divisor G - B) 0).mpr hCompRank
  obtain ⟨M, hMEff, hMEquiv⟩ :=
    (winnable_iff_exists_effective G (canonical_divisor G - B)).mp hCompWin
  let e : ℕ := (genus G - (a : ℤ)).toNat
  let f : ℕ := (genus G - (b : ℤ) - 1).toNat
  have heNonneg : 0 ≤ genus G - (a : ℤ) := by omega
  have hfNonneg : 0 ≤ genus G - (b : ℤ) - 1 := by omega
  have heCast : (e : ℤ) = genus G - (a : ℤ) := by
    dsimp [e]
    exact Int.toNat_of_nonneg heNonneg
  have hfCast : (f : ℤ) = genus G - (b : ℤ) - 1 := by
    dsimp [f]
    exact Int.toNat_of_nonneg hfNonneg
  have hMDeg : deg M = (e : ℤ) + (f : ℤ) := by
    have hEq := linear_equiv_preserves_deg G (canonical_divisor G - B) M hMEquiv
    rw [deg.map_sub, degree_of_canonical_divisor, hBDeg] at hEq
    rw [heCast, hfCast]
    omega
  have hMDegNat : deg M = e + f := by
    exact_mod_cast hMDeg
  obtain ⟨E, F, hEEff, hFEff, hEDeg, _hFDeg, hMSplit⟩ :=
    effective_divisor_decomposition G M e f hMEff hMDegNat
  let D : CFDiv G := (a : ℤ) • one_chip u + E
  have hDDeg : deg D = genus G := by
    dsimp [D]
    rw [deg.map_add, map_zsmul, deg_one_chip, hEDeg, heCast]
    ring
  have hResidual : D - (a : ℤ) • one_chip u = E := by
    dsimp [D]
    abel
  have hResidualRank : rank G (D - (a : ℤ) • one_chip u) ≥ 0 := by
    rw [hResidual]
    apply (rank_geq_iff G E 0).mp
    apply (rank_nonneg_iff_winnable G E).mpr
    exact winnable_of_effective G E hEEff
  let X : CFDiv G := D + ((b : ℤ) - 1) • one_chip u
  have hXEq : X = B + E := by
    dsimp [X, D, B]
    funext v
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hXDeg : deg X = genus G + (b : ℤ) - 1 := by
    dsimp [X]
    rw [deg.map_add, map_zsmul, deg_one_chip, hDDeg]
    ring
  have hComplement : linear_equiv G (canonical_divisor G - X) F := by
    unfold linear_equiv at hMEquiv ⊢
    rw [hMSplit] at hMEquiv
    have hDifference :
        F - (canonical_divisor G - X) =
          (E + F) - (canonical_divisor G - B) := by
      rw [hXEq]
      abel
    rw [hDifference]
    exact hMEquiv
  have hFRank : rank G F ≥ 0 := by
    apply (rank_geq_iff G F 0).mp
    apply (rank_nonneg_iff_winnable G F).mpr
    exact winnable_of_effective G F hFEff
  have hXRank : rank G X ≥ (b : ℤ) := by
    have hRR := riemann_roch_for_graphs hG X
    rw [rank_eq_of_linear_equiv G hComplement, hXDeg] at hRR
    omega
  exact ⟨D, hDDeg, hResidualRank, by simpa [X] using hXRank⟩

/-- An integral nonnegative multiple of one marked chip is effective. -/
private theorem effective_zsmul_one_chip_of_nonneg
    {G : CFGraph} (u : G.V) (n : ℤ) (hn : 0 ≤ n) :
    effective (n • one_chip u) := by
  intro v
  by_cases h : v = u
  · subst v
    simp [one_chip]
    exact hn
  · simp [one_chip, h]

/-- The empty partition imposes no rank conditions. -/
theorem onceMarkedBNExists_of_rowLens_eq_nil
    (G : CFGraph) (u : G.V) (lambda : YoungDiagram)
    (hRows : lambda.rowLens = []) :
    OnceMarkedBNExists G u lambda := by
  rw [onceMarkedBNExists_iff_rank_rows]
  refine ⟨(genus G) • one_chip u, ?_, ?_⟩
  · rw [map_zsmul, deg_one_chip]
    ring
  · intro i hi
    rw [hRows] at hi
    simp at hi

/-- A one-row partition `(a)` occurs whenever `a <= g`. -/
theorem onceMarkedBNExists_of_rowLens_eq_singleton
    (G : CFGraph) (u : G.V) (lambda : YoungDiagram) (a : ℕ)
    (hRows : lambda.rowLens = [a])
    (hSize : (a : ℤ) ≤ genus G) :
    OnceMarkedBNExists G u lambda := by
  rw [onceMarkedBNExists_iff_rank_rows]
  let D : CFDiv G := (genus G) • one_chip u
  refine ⟨D, ?_, ?_⟩
  · dsimp [D]
    rw [map_zsmul, deg_one_chip]
    ring
  · intro i hi
    have hiZero : i = 0 := by
      rw [hRows] at hi
      simp at hi
      omega
    subst i
    have hRewrite :
        D + ((0 : ℤ) - (lambda.rowLens[0]'(by simp [hRows]) : ℤ)) • one_chip u =
          (genus G - (a : ℤ)) • one_chip u := by
      rw [show lambda.rowLens[0]'(by simp [hRows]) = a by simp [hRows]]
      dsimp [D]
      funext v
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    change rank G
      (D + ((0 : ℤ) - (lambda.rowLens[0]'(by simp [hRows]) : ℤ)) • one_chip u) ≥ 0
    rw [hRewrite]
    apply (rank_geq_iff G _ 0).mp
    apply (rank_nonneg_iff_winnable G _).mpr
    apply winnable_of_effective G
    exact effective_zsmul_one_chip_of_nonneg u _ (by omega)

/-- The compressed hook construction supplies every row of the corresponding
Young diagram. -/
theorem onceMarkedBNExists_of_rowLens_eq_hook
    (G : CFGraph) (hG : graph_connected G) (u : G.V)
    (lambda : YoungDiagram) (a b : ℕ)
    (hRows : lambda.rowLens = a :: List.replicate b 1)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hSize : (a : ℤ) + (b : ℤ) ≤ genus G) :
    OnceMarkedBNExists G u lambda := by
  obtain ⟨D, hDDeg, hFirst, hLast⟩ :=
    hookPartitionExists G hG u a b ha hb hSize
  rw [onceMarkedBNExists_iff_rank_rows]
  refine ⟨D, hDDeg, ?_⟩
  intro i hi
  have hi' : i < (a :: List.replicate b 1).length := by
    simpa [hRows] using hi
  simp only [hRows]
  by_cases hiZero : i = 0
  · subst i
    have hRewrite :
        D + ((0 : ℤ) - (a : ℤ)) • one_chip u =
          D - (a : ℤ) • one_chip u := by
      funext v
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    change rank G (D + ((0 : ℤ) - (a : ℤ)) • one_chip u) ≥ 0
    rw [hRewrite]
    exact hFirst
  · have hiLe : i ≤ b := by
      simp only [List.length_cons, List.length_replicate] at hi'
      omega
    have hRow : (a :: List.replicate b 1)[i] = 1 := by
      simp [List.getElem_cons, hiZero]
    rw [hRow]
    have hTransport := rank_sub_nsmul_one_chip_ge
      (D + ((b : ℤ) - 1) • one_chip u) u (b - i)
    have hRewrite :
        (D + ((b : ℤ) - 1) • one_chip u) -
            ((b - i : ℕ) : ℤ) • one_chip u =
          D + ((i : ℤ) - 1) • one_chip u := by
      funext v
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [Nat.cast_sub hiLe]
      ring
    rw [hRewrite] at hTransport
    rw [Nat.cast_sub hiLe] at hTransport
    norm_num at hLast hTransport ⊢
    omega

/-- The pointed square `(2,2)` is exactly ordinary rank-one, degree-`g-1`
Brill--Noether existence. -/
theorem onceMarkedBNExists_iff_BNExists_of_rowLens_eq_square
    (G : CFGraph) (u : G.V) (lambda : YoungDiagram)
    (hRows : lambda.rowLens = [2, 2]) :
    OnceMarkedBNExists G u lambda ↔ BNExists G 1 (genus G - 1) := by
  rw [onceMarkedBNExists_iff_rank_rows]
  constructor
  · rintro ⟨D, hDDeg, hRanks⟩
    have hRow := hRanks 1 (by simp [hRows])
    have hTwist :
        D + ((1 : ℤ) - (lambda.rowLens[1]'(by simp [hRows]) : ℤ)) • one_chip u =
          D - one_chip u := by
      rw [show lambda.rowLens[1]'(by simp [hRows]) = 2 by simp [hRows]]
      funext v
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hRow' :
        rank G
          (D + ((1 : ℤ) - (lambda.rowLens[1]'(by simp [hRows]) : ℤ)) • one_chip u) ≥ 1 := by
      simpa only [Nat.cast_one] using hRow
    rw [hTwist] at hRow'
    refine ⟨D - one_chip u, ?_, ?_⟩
    · rw [deg.map_sub, deg_one_chip, hDDeg]
    · exact hRow'
  · rintro ⟨E, hEDeg, hERank⟩
    let D : CFDiv G := E + one_chip u
    refine ⟨D, ?_, ?_⟩
    · dsimp [D]
      rw [deg.map_add, deg_one_chip, hEDeg]
      ring
    · intro i hi
      have hi' : i < [2, 2].length := by simpa [hRows] using hi
      have hiCases : i = 0 ∨ i = 1 := by
        simp at hi'
        omega
      rcases hiCases with rfl | rfl
      · simp only [hRows]
        change rank G (D + ((0 : ℤ) - 2) • one_chip u) ≥ 0
        have hRewrite :
            D + ((0 : ℤ) - 2) • one_chip u = E - one_chip u := by
          dsimp [D]
          funext v
          simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [hRewrite]
        exact rank_sub_one_chip_ge_of_rank_ge_succ E u 0 (by omega)
      · simp only [hRows]
        change rank G (D + ((1 : ℤ) - 2) • one_chip u) ≥ 1
        have hRewrite : D + ((1 : ℤ) - 2) • one_chip u = E := by
          dsimp [D]
          funext v
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [hRewrite]
        exact hERank

/-! ## Kernel-checked catalog routing -/

abbrev genusFourRepresentativeRows : List (List ℕ) :=
  Generated.OnceMarkedGenusFourCatalog.entries.map
    OnceMarkedCatalog.Entry.rows

/-- Handwritten kernel check that the C-emitted catalog has the independent
literal row table expected by the mathematical completeness proof. -/
theorem generatedGenusFourCatalog_rows_eq_expected :
    Generated.OnceMarkedGenusFourCatalog.entries.map
        OnceMarkedCatalog.Entry.rows =
      Generated.OnceMarkedGenusFourCatalog.expectedRepresentativeRows := by
  decide

/-- Handwritten size check for the passive generated catalog. -/
theorem generatedGenusFourCatalog_entry_count :
    Generated.OnceMarkedGenusFourCatalog.entries.length = 8 := by
  decide

/-- Handwritten validator for the generated route tag of one catalog entry. -/
def checkGenusFourCatalogRoute
    (entry : OnceMarkedCatalog.Entry) : Bool :=
  match entry.route with
  | .empty => decide (entry.rows = [])
  | .square => decide (entry.rows = [2, 2])
  | .hook =>
      match entry.rows with
      | [] => false
      | a :: rest => decide (0 < a) && rest.all (· == 1)

/-- The kernel checks every C-emitted route tag. -/
theorem generatedGenusFourCatalog_routes_valid :
    Generated.OnceMarkedGenusFourCatalog.entries.all
      checkGenusFourCatalogRoute = true := by
  decide

/-- Handwritten completeness of the unquotiented reference table: every
weakly decreasing positive row list of size at most four occurs in it.  This
theorem, not the C enumerator, is the logical reason the table is exhaustive. -/
theorem sortedPositive_sum_le_four_mem_genusFourAllPartitionRows
    (rows : List ℕ) (hs : rows.SortedGE)
    (hp : ∀ x ∈ rows, 0 < x) (hcard : rows.sum ≤ 4) :
    rows ∈ Generated.OnceMarkedGenusFourCatalog.expectedRows := by
  rcases rows with _ | ⟨a, rows⟩
  · simp [Generated.OnceMarkedGenusFourCatalog.expectedRows]
  rcases rows with _ | ⟨b, rows⟩
  · simp_all [Generated.OnceMarkedGenusFourCatalog.expectedRows,
      List.sortedGE_iff_pairwise]
    omega
  rcases rows with _ | ⟨c, rows⟩
  · simp_all [Generated.OnceMarkedGenusFourCatalog.expectedRows,
      List.sortedGE_iff_pairwise]
    omega
  rcases rows with _ | ⟨d, rows⟩
  · simp_all [Generated.OnceMarkedGenusFourCatalog.expectedRows,
      List.sortedGE_iff_pairwise]
    omega
  rcases rows with _ | ⟨e, rows⟩
  · simp_all [Generated.OnceMarkedGenusFourCatalog.expectedRows,
      List.sortedGE_iff_pairwise]
    omega
  simp_all
  omega

/-- A Young diagram is determined by its row-length list. -/
private theorem youngDiagram_eq_of_rowLens_eq
    (lambda : YoungDiagram) (rows : List ℕ) (hs : rows.SortedGE)
    (hRows : lambda.rowLens = rows) :
    lambda = YoungDiagram.ofRowLens rows hs := by
  subst rows
  exact YoungDiagram.ofRowLens_to_rowLens_eq_self.symm

private theorem transpose_rowLens_eq_two_ones
    (lambda : YoungDiagram) (hRows : lambda.rowLens = [1, 1]) :
    lambda.transpose.rowLens = [2] := by
  let hs : [1, 1].SortedGE := by decide
  let hst : [2].SortedGE := by decide
  rw [youngDiagram_eq_of_rowLens_eq lambda [1, 1] hs hRows]
  have hDiagram :
      (YoungDiagram.ofRowLens [1, 1] hs).transpose =
        YoungDiagram.ofRowLens [2] hst := by
    apply YoungDiagram.ext
    decide
  rw [hDiagram]
  exact YoungDiagram.rowLens_ofRowLens_eq_self (by simp)

private theorem transpose_rowLens_eq_three_ones
    (lambda : YoungDiagram) (hRows : lambda.rowLens = [1, 1, 1]) :
    lambda.transpose.rowLens = [3] := by
  let hs : [1, 1, 1].SortedGE := by decide
  let hst : [3].SortedGE := by decide
  rw [youngDiagram_eq_of_rowLens_eq lambda [1, 1, 1] hs hRows]
  have hDiagram :
      (YoungDiagram.ofRowLens [1, 1, 1] hs).transpose =
        YoungDiagram.ofRowLens [3] hst := by
    apply YoungDiagram.ext
    decide
  rw [hDiagram]
  exact YoungDiagram.rowLens_ofRowLens_eq_self (by simp)

private theorem transpose_rowLens_eq_two_one_one
    (lambda : YoungDiagram) (hRows : lambda.rowLens = [2, 1, 1]) :
    lambda.transpose.rowLens = [3, 1] := by
  let hs : [2, 1, 1].SortedGE := by decide
  let hst : [3, 1].SortedGE := by decide
  rw [youngDiagram_eq_of_rowLens_eq lambda [2, 1, 1] hs hRows]
  have hDiagram :
      (YoungDiagram.ofRowLens [2, 1, 1] hs).transpose =
        YoungDiagram.ofRowLens [3, 1] hst := by
    apply YoungDiagram.ext
    decide
  rw [hDiagram]
  exact YoungDiagram.rowLens_ofRowLens_eq_self (by simp)

private theorem transpose_rowLens_eq_four_ones
    (lambda : YoungDiagram) (hRows : lambda.rowLens = [1, 1, 1, 1]) :
    lambda.transpose.rowLens = [4] := by
  let hs : [1, 1, 1, 1].SortedGE := by decide
  let hst : [4].SortedGE := by decide
  rw [youngDiagram_eq_of_rowLens_eq lambda [1, 1, 1, 1] hs hRows]
  have hDiagram :
      (YoungDiagram.ofRowLens [1, 1, 1, 1] hs).transpose =
        YoungDiagram.ofRowLens [4] hst := by
    apply YoungDiagram.ext
    decide
  rw [hDiagram]
  exact YoungDiagram.rowLens_ofRowLens_eq_self (by simp)

/-- Every partition of size at most four has either itself or its transpose in
the eight-entry generated representative table. -/
theorem rowLens_mem_genusFourRepresentativeRows_or_transpose
    (lambda : YoungDiagram) (hcard : lambda.rowLens.sum ≤ 4) :
    lambda.rowLens ∈ genusFourRepresentativeRows ∨
      lambda.transpose.rowLens ∈ genusFourRepresentativeRows := by
  have hAll := sortedPositive_sum_le_four_mem_genusFourAllPartitionRows
    lambda.rowLens lambda.rowLens_sorted lambda.pos_of_mem_rowLens hcard
  change lambda.rowLens ∈
      Generated.OnceMarkedGenusFourCatalog.entries.map
        OnceMarkedCatalog.Entry.rows ∨
    lambda.transpose.rowLens ∈
      Generated.OnceMarkedGenusFourCatalog.entries.map
        OnceMarkedCatalog.Entry.rows
  rw [generatedGenusFourCatalog_rows_eq_expected]
  simp [Generated.OnceMarkedGenusFourCatalog.expectedRows] at hAll
  rcases hAll with hRows | hRows | hRows | hRows | hRows | hRows |
      hRows | hRows | hRows | hRows | hRows | hRows
  · left; simp [Generated.OnceMarkedGenusFourCatalog.expectedRepresentativeRows,
      hRows]
  · left; simp [Generated.OnceMarkedGenusFourCatalog.expectedRepresentativeRows,
      hRows]
  · left; simp [Generated.OnceMarkedGenusFourCatalog.expectedRepresentativeRows,
      hRows]
  · right
    rw [transpose_rowLens_eq_two_ones lambda hRows]
    simp [Generated.OnceMarkedGenusFourCatalog.expectedRepresentativeRows]
  · left; simp [Generated.OnceMarkedGenusFourCatalog.expectedRepresentativeRows,
      hRows]
  · left; simp [Generated.OnceMarkedGenusFourCatalog.expectedRepresentativeRows,
      hRows]
  · right
    rw [transpose_rowLens_eq_three_ones lambda hRows]
    simp [Generated.OnceMarkedGenusFourCatalog.expectedRepresentativeRows]
  · left; simp [Generated.OnceMarkedGenusFourCatalog.expectedRepresentativeRows,
      hRows]
  · left; simp [Generated.OnceMarkedGenusFourCatalog.expectedRepresentativeRows,
      hRows]
  · left; simp [Generated.OnceMarkedGenusFourCatalog.expectedRepresentativeRows,
      hRows]
  · right
    rw [transpose_rowLens_eq_two_one_one lambda hRows]
    simp [Generated.OnceMarkedGenusFourCatalog.expectedRepresentativeRows]
  · right
    rw [transpose_rowLens_eq_four_ones lambda hRows]
    simp [Generated.OnceMarkedGenusFourCatalog.expectedRepresentativeRows]

/-- Sound routing for every entry in the generated genus-four catalog.  All
entries except `(2,2)` are discharged unconditionally; the last argument is
consulted only in the square branch. -/
theorem onceMarkedBNExists_of_mem_genusFourPartitionRows
    (G : CFGraph) (hG : graph_connected G) (u : G.V)
    (lambda : YoungDiagram)
    (hSize : (lambda.rowLens.sum : ℤ) ≤ genus G)
    (hMem : lambda.rowLens ∈ genusFourRepresentativeRows)
    (hSquare : lambda.rowLens = [2, 2] →
      BNExists G 1 (genus G - 1)) :
    OnceMarkedBNExists G u lambda := by
  change lambda.rowLens ∈
    Generated.OnceMarkedGenusFourCatalog.entries.map
      OnceMarkedCatalog.Entry.rows at hMem
  obtain ⟨entry, hEntry, hRows⟩ := List.mem_map.mp hMem
  have hCheck : checkGenusFourCatalogRoute entry = true :=
    (List.all_eq_true.mp generatedGenusFourCatalog_routes_valid) entry hEntry
  cases hRoute : entry.route with
  | empty =>
      have hEmpty : entry.rows = [] := by
        simpa [checkGenusFourCatalogRoute, hRoute] using hCheck
      apply onceMarkedBNExists_of_rowLens_eq_nil G u lambda
      rw [← hRows]
      exact hEmpty
  | square =>
      have hSquareRows : entry.rows = [2, 2] := by
        simpa [checkGenusFourCatalogRoute, hRoute] using hCheck
      have hLambdaRows : lambda.rowLens = [2, 2] := by
        rw [← hRows]
        exact hSquareRows
      apply (onceMarkedBNExists_iff_BNExists_of_rowLens_eq_square
        G u lambda hLambdaRows).2
      exact hSquare hLambdaRows
  | hook =>
      cases hEntryRows : entry.rows with
      | nil =>
          simp [checkGenusFourCatalogRoute, hRoute, hEntryRows] at hCheck
      | cons a rest =>
          have hHook := hCheck
          simp only [checkGenusFourCatalogRoute, hRoute, hEntryRows,
            decide_eq_true_eq, Bool.and_eq_true, List.all_eq_true,
            beq_iff_eq] at hHook
          obtain ⟨ha, hRest⟩ := hHook
          cases rest with
          | nil =>
              have hLambdaRows : lambda.rowLens = [a] := by
                rw [← hRows, hEntryRows]
              apply onceMarkedBNExists_of_rowLens_eq_singleton
                G u lambda a hLambdaRows
              simpa [hLambdaRows] using hSize
          | cons x xs =>
              let rest := x :: xs
              have hRestEq : rest = List.replicate rest.length 1 :=
                List.eq_replicate_of_mem hRest
              have hLambdaRows :
                  lambda.rowLens = a :: List.replicate rest.length 1 := by
                rw [← hRows, hEntryRows]
                exact congrArg (a :: ·) hRestEq
              apply onceMarkedBNExists_of_rowLens_eq_hook
                G hG u lambda a rest.length hLambdaRows
              · omega
              · simp [rest]
              · simpa [hLambdaRows] using hSize

/-- Sharp reduction through genus four: the only input not supplied by the
uniform hook theorem is the ordinary genus-four rank-one degree-three case. -/
theorem onceMarkedBNExistence_of_genus_le_four_of_critical
    (G : CFGraph) (hG : graph_connected G) (u : G.V)
    (hLow : genus G ≤ 4)
    (hCritical : genus G = 4 → BNExists G 1 3) :
    OnceMarkedBNExistence G u := by
  intro lambda hSize
  have hSizeRows : (lambda.rowLens.sum : ℤ) ≤ genus G := by
    rw [youngDiagram_rowLens_sum_eq_card]
    exact hSize
  have hCardInt : (lambda.rowLens.sum : ℤ) ≤ 4 := hSizeRows.trans hLow
  have hCardNat : lambda.rowLens.sum ≤ 4 := by exact_mod_cast hCardInt
  have hOrbit := rowLens_mem_genusFourRepresentativeRows_or_transpose
    lambda hCardNat
  have proveRepresentative :
      ∀ mu : YoungDiagram,
        (mu.rowLens.sum : ℤ) ≤ genus G →
        mu.rowLens ∈ genusFourRepresentativeRows →
        OnceMarkedBNExists G u mu := by
    intro mu hMuSize hMem
    apply onceMarkedBNExists_of_mem_genusFourPartitionRows
      G hG u mu hMuSize hMem
    intro hSquareRows
    have hFour : genus G = 4 := by
      have hSquareSize : mu.rowLens.sum = 4 := by simp [hSquareRows]
      rw [hSquareSize] at hMuSize
      omega
    simpa [hFour] using hCritical hFour
  rcases hOrbit with hDirect | hDual
  · exact proveRepresentative lambda hSizeRows hDirect
  · apply (onceMarkedBNExists_transpose_iff hG u lambda).mpr
    apply proveRepresentative lambda.transpose
    · rw [youngDiagram_rowLens_sum_eq_card,
        youngDiagram_transpose_card, ← youngDiagram_rowLens_sum_eq_card]
      exact hSizeRows
    · exact hDual

/-- Unconditional once-marked existence in genus at most three. -/
theorem onceMarkedBNExistence_of_genus_le_three
    (G : CFGraph) (hG : graph_connected G) (u : G.V)
    (hLow : genus G ≤ 3) :
    OnceMarkedBNExistence G u :=
  onceMarkedBNExistence_of_genus_le_four_of_critical G hG u (by omega)
    (fun hFour => by omega)

/-- The Young diagram `(2,2)`. -/
def squareYoungDiagram : YoungDiagram :=
  YoungDiagram.ofRowLens [2, 2] (by decide)

@[simp] theorem squareYoungDiagram_rowLens :
    squareYoungDiagram.rowLens = [2, 2] := by
  exact YoungDiagram.rowLens_ofRowLens_eq_self (by simp)

/-- In genus four the once-marked existence conjecture is equivalent, for
every choice of mark, to ordinary `W^1_3` existence. -/
theorem onceMarkedBNExistence_iff_BNExists_genus_four
    (G : CFGraph) (hG : graph_connected G) (hFour : genus G = 4)
    (u : G.V) :
    OnceMarkedBNExistence G u ↔ BNExists G 1 3 := by
  constructor
  · intro hMarked
    have hSquareSize : (squareYoungDiagram.card : ℤ) ≤ genus G := by
      rw [← youngDiagram_rowLens_sum_eq_card]
      simp [hFour]
    have hSquareMarked := hMarked squareYoungDiagram hSquareSize
    have hSquare :=
      (onceMarkedBNExists_iff_BNExists_of_rowLens_eq_square
        G u squareYoungDiagram squareYoungDiagram_rowLens).1 hSquareMarked
    simpa [hFour] using hSquare
  · intro hCritical
    exact onceMarkedBNExistence_of_genus_le_four_of_critical
      G hG u (by omega) (fun _ => hCritical)

end MarkedGraphs
