module

public import DraismaVargasMarkedCount.MarkedCountGeneral.RegrowMatrix
public import DraismaVargasMarkedCount.MarkedCountGeneral.RegrowWindow
public import DraismaVargasMarkedCount.MarkedCountGeneral.TypedFrame

@[expose] public section

/-!
# The denominator step of the drop, part 1: an unmarked regrowth of any typed frame

For the denominator step `DropSmooth.rowDenominator_split`.

The public row calculus (`SharpRowDenominator`, `RowWalk`, `RowGeodesic`) is stated for unmarked
full-dimensional presentations. To read it on the marked rows of a typed frame `φ` we attach a
caterpillar tail at every mark (the generic regrowth `CatRegrow.CatBranching.regrowDatum`),
which makes every mark trivalent: the marked rows of `φ` become stable rows of the regrowth, with
the same occurrences and indices (`CatRegrow.CatBranching.stablePathEquiv`,
`sourceEdgeIndex_psiSE`), and the length matrix is block diagonal (`matrix_inl_oldE`).

`CatRegrow.branching` takes the degree hypothesis `IsTailDegree` of the headline count, which it
uses only for `shed J ≤ degree`. Here the regrowth is built for a typed frame of **any** type, in
its own degree, with one shed sheet per mark: tail genus `c j = types j + 1`, one ascent
(`J j = 1`), regrown degree `degree + k`, and the slope sequence `slope` (`types j + 1`, then
`types j + 2, types j + 1, …, 2`). The construction is that of `RegrowFrame` and the `fullDim`
part of `RegrowAssemble`, specialized; every generic lemma is from the regrowth modules.

* `branching φ`: the caterpillar branching (`CatRegrow.CatBranching`);
* `fullDim φ hc`: a `FullDimensionalSourcePresentation` of the regrowth, with coordinates
  `Fin p ⊕ TE (cc types)` and the block-diagonal matrix `fromBlocks φ.matrix 0 0 diag`
  (`matrix_labelling`).

**Imports.** This module is imported by `DropSmooth`, so everything downstream of the drop sees
its import closure. It deliberately imports only `RegrowMatrix`, `RegrowWindow` and `TypedFrame`,
not `RegrowFrame`/`RegrowAssemble`: their closure contains `RigidSpine`, whose
`MarkedCountGeneral.eq_or_eq_otherEnd` shadows `W4StableSource.eq_or_eq_otherEnd` inside the
namespace `MarkedCountGeneral` and breaks `DropUnique`.
-/

namespace DraismaVargas.Count.MarkedCountGeneral

namespace DenomRegrow

noncomputable section

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.MarkedCount
open CatRegrow CatSlot TailV
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}

/-! ## 1.  The slopes -/

/-- The tail parameter at mark `j`: a caterpillar tail of genus `types j + 2`. -/
def cc (types : Fin k → ℕ) : Fin k → ℕ := fun j ↦ types j + 1

/-- **The slope sequence with one ascent**: `types j + 1`, then `types j + 2`, descending to `2`. -/
def slope (types : Fin k → ℕ) (j : Fin k) : Fin (cc types j + 1) → ℕ :=
  fun i ↦ if i.val = 0 then types j + 1 else types j + 3 - i.val

/-- The first slope. -/
theorem slope_zero (j : Fin k) : slope types j 0 = types j + 1 := by
  simp [slope]

/-- The second slope. -/
theorem slope_one (j : Fin k) (h : 1 < cc types j + 1) : slope types j ⟨1, h⟩ = types j + 2 := by
  simp [slope]

/-- `slope` is a slope sequence with one ascent. -/
theorem isSlopeSeq_slope (j : Fin k) : IsSlopeSeq (cc types j + 1) 1 (slope types j) := by
  refine ⟨fun i ↦ ?_, fun i hi ↦ ?_, fun i i' hi ↦ ?_, fun i hi ↦ ?_⟩
  · have := i.2; unfold slope cc at *; split_ifs <;> omega
  · unfold slope cc at *; split_ifs <;> omega
  · have := i'.2; unfold slope cc at *; split_ifs <;> omega
  · unfold slope cc at *; rw [ite_eq_left hi]

/-- The window bound of `slope`. -/
theorem slope_hM (j : Fin k) : types j + 2 = slope types j 0 + 1 := by
  rw [slope_zero]

/-- The low end of the second window is `0`. -/
theorem winLo_one (j : Fin k) (h : 1 < cc types j + 1) : winLo (slope types j) ⟨1, h⟩ = 0 := by
  unfold winLo
  rw [slope_one j h]
  have h0 : slope types j 0 = types j + 1 := slope_zero j
  simp only [h0]
  omega

/-! ## 2.  The sheets and the line-up -/

/-- **The sheets of the regrowth**: the old ones, then one new sheet per mark. -/
def sheetEquiv (degree k : ℕ) : Fin degree ⊕ Fin k ≃ Fin (degree + k) := finSumFinEquiv

variable (φ : TypedFrame core mark types degree)

/-- The block of mark `j` in `φ`. -/
def markBlock (j : Fin k) : Finset (Fin degree) :=
  (φ.data.vertexPartition (φ.markSource j).1.1).block (φ.markSource j).1.2

/-- (D4′): the block of mark `j` has at least `types j + 1` sheets. -/
theorem firstSlope_le (j : Fin k) : types j + 1 ≤ (markBlock φ j).card := (φ.typed j).2

/-- **The line-up of `types j + 1` sheets of the block of mark `j`.** -/
def lineUp (j : Fin k) (r : Fin (types j + 1)) : Fin degree :=
  ((markBlock φ j).orderEmbOfFin rfl) (Fin.castLE (firstSlope_le φ j) r)

/-- The line-up is injective. -/
theorem lineUp_injective (j : Fin k) : Function.Injective (lineUp φ j) := fun _ _ h ↦
  Fin.castLE_injective _ (((markBlock φ j).orderEmbOfFin rfl).injective h)

/-- The line-up lies in the block of the mark. -/
theorem lineUp_mem (j : Fin k) (r : Fin (types j + 1)) : lineUp φ j r ∈ markBlock φ j :=
  Finset.orderEmbOfFin_mem _ _ _

/-- **The sheets of tail `j`, lined up**: `types j + 1` sheets of the block of the mark, then the
new sheet `j`. -/
def tailSheet (j : Fin k) (r : ℕ) : Fin (degree + k) :=
  if h : r < types j + 1 then old (sheetEquiv degree k) (lineUp φ j ⟨r, h⟩)
  else if r = types j + 1 then new (sheetEquiv degree k) j
  else old (sheetEquiv degree k) ⟨0, φ.data.degree_pos⟩

/-- The tail sheets below the top are old. -/
theorem tailSheet_lt {j : Fin k} {r : ℕ} (h : r < types j + 1) :
    tailSheet φ j r = old (sheetEquiv degree k) (lineUp φ j ⟨r, h⟩) := by
  unfold tailSheet; rw [dite_eq_left h]

/-- The top tail sheet is the new sheet `j`. -/
theorem tailSheet_top (j : Fin k) :
    tailSheet φ j (types j + 1) = new (sheetEquiv degree k) j := by
  unfold tailSheet; rw [dite_eq_right (by omega), ite_eq_left rfl]

/-- The tail sheets are distinct. -/
theorem tailSheet_injOn (j : Fin k) : Set.InjOn (tailSheet φ j) (Set.Iio (types j + 2)) := by
  intro r hr r' hr' h
  simp only [Set.mem_Iio] at hr hr'
  by_cases h1 : r < types j + 1 <;> by_cases h2 : r' < types j + 1
  · rw [tailSheet_lt φ h1, tailSheet_lt φ h2, old_inj] at h
    exact congrArg Fin.val (lineUp_injective φ j h)
  · obtain rfl : r' = types j + 1 := by omega
    rw [tailSheet_lt φ h1, tailSheet_top] at h
    exact absurd h (old_ne_new _ _)
  · obtain rfl : r = types j + 1 := by omega
    rw [tailSheet_top, tailSheet_lt φ h2] at h
    exact absurd h (new_ne_old _ _)
  · omega

/-! ## 3.  The chains and the branching -/

/-- **The chain at mark `j`**: the window chain of `slope` through the line-up. -/
def chain (j : Fin k) : TailChain (degree + k) (cc types j) :=
  windowChain (slope types j) (tailSheet φ j)

/-- The chain is valid. -/
theorem chain_valid (j : Fin k) : (chain φ j).Valid :=
  windowChain_valid (tailSheet_injOn φ j) (isSlopeSeq_slope j) (slope_hM j)

/-- Membership in a block of the chain. -/
theorem mem_chain_P {j : Fin k} {i : Fin (cc types j + 1)} {q : Fin (degree + k)} :
    q ∈ (chain φ j).P i ↔ ∃ r, winLo (slope types j) i ≤ r ∧
      r < winLo (slope types j) i + slope types j i ∧ tailSheet φ j r = q := mem_window

/-- Membership in the first block of the chain. -/
theorem mem_chain_P_zero {j : Fin k} {q : Fin (degree + k)} :
    q ∈ (chain φ j).P 0 ↔ ∃ r, r < types j + 1 ∧ tailSheet φ j r = q := by
  rw [mem_chain_P, winLo_zero, slope_zero]
  simp only [zero_le, true_and, zero_add]

/-- The blocks of the chain stay below the top sheet. -/
theorem chain_P_bound (j : Fin k) (i : Fin (cc types j + 1)) :
    winLo (slope types j) i + slope types j i ≤ types j + 2 :=
  winHi_le_M (isSlopeSeq_slope j) (slope_hM j) i

/-- The sheets of the chain past `P_1` are the new sheet of the tail. -/
theorem fresh_chain {j : Fin k} {i : Fin (cc types j + 1)} {q : Fin (degree + k)}
    (hq : q ∈ (chain φ j).P i) (hq0 : q ∉ (chain φ j).P 0) :
    q = new (sheetEquiv degree k) j := by
  obtain ⟨r, hr1, hr2, rfl⟩ := (mem_chain_P φ).mp hq
  have hb := chain_P_bound j i
  by_cases h : r < types j + 1
  · exact absurd ((mem_chain_P_zero φ).mpr ⟨r, h, rfl⟩) hq0
  · obtain rfl : r = types j + 1 := by omega
    exact tailSheet_top φ j

/-- **The new sheet of tail `j` enters the chain** at the second block. -/
theorem new_mem_chain (j : Fin k) :
    new (sheetEquiv degree k) j ∈ (chain φ j).P ⟨1, by unfold cc; omega⟩ := by
  refine (mem_chain_P φ).mpr ⟨types j + 1, ?_, ?_, tailSheet_top φ j⟩
  · rw [winLo_one]; omega
  · rw [winLo_one, slope_one]; omega

/-- **The caterpillar branching of a typed frame**, one shed sheet per mark. -/
def branching : CatBranching φ.data (Fin k) (degree + k) (cc types) where
  e := sheetEquiv degree k
  mark := φ.markSource
  chain := chain φ
  valid := chain_valid φ
  P0_sub j q hq := by
    obtain ⟨r, hr, rfl⟩ := (mem_chain_P_zero φ).mp hq
    refine ⟨lineUp φ j ⟨r, hr⟩, tailSheet_lt φ hr, ?_⟩
    exact ((φ.data.vertexPartition _).mem_block_iff _ _).mp (lineUp_mem φ j _)
  fresh j i q hq hq0 := ⟨j, fresh_chain φ hq hq0⟩
  fresh_disjoint j j' i i' q hq hq' hq0 := by
    have hq1 := fresh_chain φ hq hq0
    subst hq1
    by_cases h0 : new (sheetEquiv degree k) j ∈ (chain φ j').P 0
    · obtain ⟨r', hr', h⟩ := (mem_chain_P_zero φ).mp h0
      rw [tailSheet_lt φ hr'] at h
      exact absurd h (old_ne_new _ _)
    · have h := fresh_chain φ hq' h0
      rw [new_inj] at h
      exact h
  new_used nn := ⟨nn, ⟨1, by unfold cc; omega⟩, new_mem_chain φ nn⟩

@[simp] theorem branching_mark (j : Fin k) : (branching φ).mark j = φ.markSource j := rfl

/-- The first block has `types j + 1` sheets. -/
theorem card_P_zero (j : Fin k) : (((branching φ).chain j).P 0).card = types j + 1 := by
  have h := card_windowChain_P (tailSheet_injOn φ j) (isSlopeSeq_slope j) (slope_hM j) 0
  rw [slope_zero] at h
  exact h

/-! ## 4.  The hypotheses of the regrowth lemmas -/

/-- The datum is connected. -/
theorem hψ : φ.data.Connected := φ.fullDim.valid.1
/-- The target is connected. -/
theorem hT : graph_connected φ.target := φ.fullDim.targetConnected
/-- The target is a tree. -/
theorem hT0 : genus φ.target = 0 := φ.fullDim.targetGenus

/-- The marks survive. -/
theorem hMark (j : Fin k) : nonDanglingValency φ.data ((branching φ).mark j) ≠ 0 := by
  rw [branching_mark, φ.fullDim.markValency _ (mem_markSet _ j)]; omega

/-- The marks of a typed frame are distinct source vertices. -/
theorem hInj (hc : IsMarkedCubic core mark) : Function.Injective (branching φ).mark := by
  intro i j h
  apply hc.injective
  rw [← φ.ident.vertex_mark i, ← φ.ident.vertex_mark j]
  congr 1
  exact Subtype.ext h

/-- Riemann--Hurwitz at the marks: (D4′) gives `r ≥ types j`. -/
theorem hRam (j : Fin k) :
    (((branching φ).chain j).P 0).card - 1 ≤ markRamification φ.data ((branching φ).mark j) := by
  rw [card_P_zero, branching_mark]
  have := (φ.typed j).1
  push_cast
  linarith

/-! ## 5.  The full-dimensional presentation of the regrowth -/

section Frame

local notation "β" => branching φ

/-- The column dictionary: core columns, then tail columns. -/
def colEquiv : Fin p ⊕ TE (cc types) ≃ (catTarget (cc types) φ.target (β).x).edges :=
  (Equiv.sumCongr φ.fullDim.labelling.targetEdge (Equiv.refl _)).trans
    (occEquiv (cc types) (β).x)

@[simp] theorem colEquiv_inl (i : Fin p) :
    colEquiv φ (.inl i) = oldE (cc types) (β).x (φ.fullDim.labelling.targetEdge i) := rfl
@[simp] theorem colEquiv_inr (t : TE (cc types)) :
    colEquiv φ (.inr t) = tailE (cc types) (β).x t := rfl

/-- The row dictionary of the labelling. -/
def labRow : MarkedStablePath φ.data (markSet φ.markSource) ⊕ TE (cc types) ≃
    Fin p ⊕ TE (cc types) :=
  Equiv.sumCongr φ.fullDim.labelling.row (Equiv.refl _)

/-- The stable paths of the regrowth, by rows. -/
abbrev pathEquiv : StablePath (β).regrowDatum ≃
    MarkedStablePath φ.data (markSet φ.markSource) ⊕ TE (cc types) :=
  (β).stablePathEquiv (hψ φ) (hT φ) (hT0 φ) (hMark φ)

/-- **The stable labelling of the regrowth**, by core slots and tail slots. -/
def labelling : StableLengthMatrixLabelling (β).regrowDatum (Fin p ⊕ TE (cc types)) where
  targetEdge := colEquiv φ
  row := (pathEquiv φ).trans (labRow φ)

/-- The row of the labelling at a core slot. -/
theorem labelling_row_symm_inl (i : Fin p) :
    (labelling φ).row.symm (.inl i) =
      (β).tagPath (hψ φ) (hT φ) (hT0 φ) (hMark φ) (.inl (φ.fullDim.labelling.row.symm i)) := by
  simp only [labelling, Equiv.symm_trans_apply]
  rfl

/-- The block matrix: the marked matrix of `φ`, then the diagonal of the tails. -/
def blockMatrix : Matrix (Fin p ⊕ TE (cc types)) (Fin p ⊕ TE (cc types)) ℚ :=
  Matrix.fromBlocks φ.matrix 0 0 (Matrix.diagonal (β).tailDiag)

open Classical in
/-- An entry of the marked matrix, as a sum over the surviving edges. -/
theorem markedEntry_eq (P : MarkedStablePath φ.data (markSet φ.markSource))
    (ε : φ.target.edges) :
    (∑ F : NonDanglingEdge φ.data,
        if markedRow (markSet φ.markSource) F = P ∧ F.1.1.1 = ε then
          (1 : ℚ) / φ.data.sourceEdgeIndex F.1 else 0) =
      markedMatrix φ.data (markSet φ.markSource) P ε := by
  classical
  unfold markedMatrix markedOccurrences
  symm
  convert MarkedCount.Regrow.sum_filter_nonDangling φ.data
    (fun F ↦ markedRow (markSet φ.markSource) F = P) ε
    (fun e ↦ (1 : ℚ) / φ.data.sourceEdgeIndex e) using 1

/-- **The matrix of the regrowth is block diagonal.** -/
theorem matrix_labelling :
    GluingDatum.LengthMatrixPresentation.matrix (labelling φ).presentation = blockMatrix φ := by
  funext z w
  rw [StableSourceMatrix.labelling_matrix_eq]
  have hRow : (labelling φ).row.symm z =
      (β).tagPath (hψ φ) (hT φ) (hT0 φ) (hMark φ) ((labRow φ).symm z) := by
    simp only [labelling, Equiv.symm_trans_apply]
    rfl
  have hCol : (labelling φ).targetEdge w = colEquiv φ w := rfl
  rw [hRow, hCol]
  rcases z with i | t <;> rcases w with i' | t'
  · rw [colEquiv_inl]
    refine ((β).matrix_inl_oldE (hψ φ) (hT φ) (hT0 φ) (hMark φ)
      (φ.fullDim.labelling.row.symm i) (φ.fullDim.labelling.targetEdge i')).trans ?_
    rw [blockMatrix, Matrix.fromBlocks_apply₁₁, TypedFrame.matrix, MarkedLabelling.matrix_eq]
    exact markedEntry_eq φ _ _
  · rw [colEquiv_inr]
    refine ((β).matrix_inl_tailE (hψ φ) (hT φ) (hT0 φ) (hMark φ)
      (φ.fullDim.labelling.row.symm i) t').trans ?_
    rw [blockMatrix, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
  · rw [colEquiv_inl]
    refine ((β).matrix_inr_oldE (hψ φ) (hT φ) (hT0 φ) (hMark φ) t
      (φ.fullDim.labelling.targetEdge i')).trans ?_
    rw [blockMatrix, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
  · rw [colEquiv_inr]
    refine ((β).matrix_inr_tailE (hψ φ) (hT φ) (hT0 φ) (hMark φ) t t').trans ?_
    rw [blockMatrix, Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply]

/-- The determinant of the regrowth does not vanish. -/
theorem det_labelling_ne_zero :
    (GluingDatum.LengthMatrixPresentation.matrix (labelling φ).presentation).det ≠ 0 := by
  rw [matrix_labelling, blockMatrix, Matrix.det_fromBlocks_zero₂₁, Matrix.det_diagonal]
  exact mul_ne_zero φ.det_ne_zero (Finset.prod_ne_zero_iff.mpr fun t _ ↦ ((β).tailDiag_pos t).ne')

/-- **The dimension count of the regrowth**, from the typed one. -/
theorem saturated :
    ((catTarget (cc types) φ.target (β).x).edges.card : ℤ) =
      2 * genus (β).regrowDatum.sourceGraph + 2 * (degree + k : ℕ) - 5 := by
  have hE := card_edges_catTarget (cc types) (β).x
  have hG := (β).genus_regrowDatum (hT0 φ)
  have hκ := φ.fullDim.saturated
  have hgc : ∀ j, 2 * ((β).chain j).genusContribution =
      3 * cc types j + 4 - ((types j : ℤ) + 1) := fun j ↦ by
    rw [((β).valid j).two_mul_genusContribution, card_P_zero]
    push_cast; ring
  have hsum : 2 * ∑ j, ((β).chain j).genusContribution =
      ∑ j, ((3 * cc types j + 2 : ℕ) : ℤ) - typeExcess types := by
    rw [Finset.mul_sum, typeExcess]
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hgc j]
    ring
  rw [hE, hG]
  have hN : (Fintype.card (Fin k) : ℤ) = k := by simp
  rw [hN]
  push_cast at hκ hsum ⊢
  linarith

/-- **The full-dimensional presentation of the regrowth.** -/
def fullDim (hc : IsMarkedCubic core mark) :
    FullDimensionalSource.FullDimensionalSourcePresentation (β).regrowDatum
      (Fin p ⊕ TE (cc types)) where
  valid := ⟨(β).connected_regrowDatum (hψ φ) (hT φ),
    (β).riemannHurwitz_regrowDatum (hInj φ hc) (hRam φ) φ.fullDim.valid.2⟩
  targetConnected := catTarget_connected (cc types) (β).x (hT φ)
  targetGenus := (genus_catTarget (cc types) (β).x).trans (hT0 φ)
  saturated := saturated φ
  labelling := labelling φ
  det_ne_zero := det_labelling_ne_zero φ
  trivalent := (β).nonDanglingValency_le_three (hψ φ) (hT φ) (hT0 φ) (hMark φ)
    φ.fullDim.trivalent (fun j ↦ φ.fullDim.markValency _ (mem_markSet _ j)) (hInj φ hc)
  pathEnds := (β).hasPathEnds_regrowDatum (hψ φ) (hT φ) (hT0 φ) (hMark φ) φ.fullDim.pathEnds

end Frame

end

end DenomRegrow

end DraismaVargas.Count.MarkedCountGeneral
