module

public import DraismaVargasMarkedCount.MarkedCountGeneral.RestrictTailRows
public import DraismaVargasMarkedCount.MarkedCount.RestrictFrame

@[expose] public section

/-!
# Restriction over the tails: the marked labelling of `ψ` and the block decomposition of `A_φ`

By the rigidity of the tails (module `Rigidity`), after reordering rows and columns,

  `A_φ = A_{ψ;u} ⊕ diag(1/s_{i+1}, 1/2, 2)`,

the tail block being diagonal: `1/s_{i+1}` on the path rows, `1/2` on the bridge rows, `2` on the
loop rows (`submatrix_eq_fromBlocks`). Hence `|det A_φ| = |det A_ψ| · ∏ (tail weights)`
(`abs_det_labelling`), the coordinates split (`coords_blocks`), and the row denominators are
`D_φ = D_ψ · ∏ (s_{i+1}; 2; 1)` (`denominatorProduct_labelling`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral.TailRestrict

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.MarkedCount.Restrict
open DraismaVargas.Count.MarkedCountGeneral.Sheets (IsNew IsLone restrictSheets inclSV inclSE)
open Utilities.Certificate.ExplicitPotential (Core)
open CatSlot
open scoped DraismaVargas.Infrastructure.GluingContraction
open scoped Matrix

noncomputable section

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {c : Fin k → ℕ}
  (T : Tailed core mark c) (hc : IsMarkedCubic core mark) {y : Fin T.P → ℚ}
  (M : FibreMember T.H y degree) (m : ℕ) (hm : m + nShed T hc M = degree)

/-! ## 1.  The marked labelling -/

theorem card_rTarget_edges' : Fintype.card (rTarget T hc M).edges = p := by
  rw [Multiset.card_coe, card_rTarget_edges]

/-- The target edges of `T'`, numbered. -/
def targetEdge' : Fin p ≃ (rTarget T hc M).edges :=
  (Fintype.equivFinOfCardEq (card_rTarget_edges' T hc M)).symm

/-- **The marked labelling of `ψ`**: rows by core slots, columns by `targetEdge'`. -/
def labelling : MarkedLabelling (dat T hc M m hm) (marks T hc M m hm) (Fin p) :=
  ⟨targetEdge' T hc M, rowEquiv T hc M m hm⟩

/-- The column of `A_φ` of a kept target edge. -/
def colIncl (i : Fin p) : Fin T.P :=
  M.fullDim.labelling.targetEdge.symm (edgeIncl (targetEdge' T hc M i))

/-- The row of `A_φ` of a core slot. -/
def rowIncl (i : Fin p) : Fin T.P := M.fullDim.labelling.row (M.ident.row.symm (T.coreSlot i))

/-- **The marked matrix of `ψ` is a submatrix of `A_φ`.** -/
theorem matrix_labelling (i j : Fin p) :
    GluingDatum.LengthMatrixPresentation.matrix (labelling T hc M m hm).presentation i j =
      GluingDatum.LengthMatrixPresentation.matrix M.fullDim.labelling.presentation
        (rowIncl T M i) (colIncl T hc M j) := by
  classical
  have hj' : j = (labelling T hc M m hm).targetEdge.symm ((labelling T hc M m hm).targetEdge j) :=
    (Equiv.symm_apply_apply _ _).symm
  conv_lhs => rw [hj']
  rw [markedMatrix_eq_sum, colIncl, LeafFibre.matrix_eq_sum_fibre]
  refine Finset.sum_bij (fun E _ ↦ cSE T hc M m hm E) ?_ ?_ ?_ ?_
  · intro E hE
    obtain ⟨⟨hS, hR⟩, hT⟩ := (mem_markedRowFibre _ _ _ _).mp hE
    refine (LeafFibre.mem_rowFibre _ _ _ _).mpr ⟨⟨(ndInc T hc M m hm ⟨E, hS⟩).2, ?_⟩, ?_⟩
    · have := (rowEquiv_markedRow_eq_iff T hc M m hm ⟨E, hS⟩ i).mp hR
      exact congrArg M.fullDim.labelling.row this
    · change edgeIncl (inclSE E).1.1 = _
      rw [show (inclSE E).1.1 = E.1.1 from rfl, hT]
      rfl
  · intro E _ F _ h
    exact cSE_injective T hc M m hm h
  · intro F hF
    obtain ⟨⟨hS, hR⟩, hT⟩ := (LeafFibre.mem_rowFibre _ _ _ _).mp hF
    have hk : KeptEdge (Keep T M) F.1.1 := by rw [hT]; exact keptEdge_edgeIncl _
    obtain ⟨E, hE⟩ := exists_cSE_of_survivor T hc M m hm hS hk
    have hS' : ¬ IsDangling (dat T hc M m hm) E := not_isDangling_dat_of T hc M m hm (hE ▸ hS)
    refine ⟨E, (mem_markedRowFibre _ _ _ _).mpr ⟨⟨hS', ?_⟩, ?_⟩, hE⟩
    · refine (rowEquiv_markedRow_eq_iff T hc M m hm ⟨E, hS'⟩ i).mpr ?_
      have hn : ndInc T hc M m hm ⟨E, hS'⟩ = ⟨F, hS⟩ := Subtype.ext hE
      rw [hn]
      exact M.fullDim.labelling.row.injective hR
    · apply edgeIncl_injective
      change (cSE T hc M m hm E).1.1 = _
      rw [hE, hT]; rfl
  · intro E _
    rw [sourceEdgeIndex_cSE]

/-! ## 2.  The block decomposition -/

/-- The slots of `T.H`: core slots, then tail slots. -/
abbrev SlotT : Type := Fin p ⊕ (Σ j, CatSlot (c j))

/-- The rows of `A_φ`, by slots. -/
def rowBlocks : SlotT (p := p) (c := c) ≃ Fin T.P :=
  T.slotEquiv.trans (M.ident.row.symm.trans M.fullDim.labelling.row)

theorem rowBlocks_inl (i : Fin p) : rowBlocks T M (Sum.inl i) = rowIncl T M i := rfl

theorem rowBlocks_inr (j : Fin k) (s : CatSlot (c j)) :
    rowBlocks T M (Sum.inr ⟨j, s⟩) = M.fullDim.labelling.row (TailAt.row (cat T j) M s) := rfl

/-- The column function: kept target edges, then tail edges. -/
def colFun : SlotT (p := p) (c := c) → Fin T.P :=
  Sum.elim (colIncl T hc M) fun q ↦ M.fullDim.labelling.targetEdge.symm (tEdge T hc M q.1 q.2)

theorem colFun_injective : Function.Injective (colFun T hc M) := by
  have hK : ∀ (i : Fin p) (q : Σ j, CatSlot (c j)),
      edgeIncl (targetEdge' T hc M i) ≠ tEdge T hc M q.1 q.2 := fun i q h ↦
    not_keptEdge_tEdge T hc M q.1 q.2 (h ▸ keptEdge_edgeIncl _)
  rintro (a | a) (b | b) h <;>
    simp only [colFun, colIncl, Sum.elim_inl, Sum.elim_inr, EmbeddingLike.apply_eq_iff_eq] at h
  · exact congrArg Sum.inl ((targetEdge' T hc M).injective (edgeIncl_injective h))
  · exact absurd h (hK a b)
  · exact absurd h.symm (hK b a)
  · exact congrArg Sum.inr (tailEdge_injective T hc M h)

theorem card_slotT : Fintype.card (SlotT (p := p) (c := c)) = T.P := by
  rw [Fintype.card_sum, Fintype.card_fin, card_catSlot, T.card_slots]

/-- The columns of `A_φ`, by slots. -/
def colBlocks : SlotT (p := p) (c := c) ≃ Fin T.P :=
  Equiv.ofBijective (colFun T hc M) ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨colFun_injective T hc M, by rw [card_slotT, Fintype.card_fin]⟩)

theorem colBlocks_apply (s : SlotT (p := p) (c := c)) : colBlocks T hc M s = colFun T hc M s := rfl

/-- **The tail weights**: `1/s_{i+1}`, `1/2`, `2`. -/
def tailWeight : (Σ j, CatSlot (c j)) → ℚ
  | ⟨j, Sum.inl i⟩ => 1 / (sPath T hc M j i : ℚ)
  | ⟨_, Sum.inr (Sum.inl _)⟩ => 1 / 2
  | ⟨_, Sum.inr (Sum.inr _)⟩ => 2

/-- The tail block. -/
def tailBlock : Matrix (Σ j, CatSlot (c j)) (Σ j, CatSlot (c j)) ℚ :=
  Matrix.diagonal (tailWeight T hc M)

theorem row_inj {j j' : Fin k} {s : CatSlot (c j)} {s' : CatSlot (c j')}
    (h : TailAt.row (cat T j) M s = TailAt.row (cat T j') M s') :
    (⟨j, s⟩ : Σ j, CatSlot (c j)) = ⟨j', s'⟩ :=
  Sum.inr_injective (T.slotEquiv.injective (M.ident.row.symm.injective h))

theorem matrix_eq_zero_of_fibre (r : Fin T.P) (e : M.target.edges)
    (h : ∀ F : NonDanglingEdge M.data, M.fullDim.labelling.row F.stablePath = r → F.1.1.1 ≠ e) :
    GluingDatum.LengthMatrixPresentation.matrix M.fullDim.labelling.presentation r
      (M.fullDim.labelling.targetEdge.symm e) = 0 := by
  rw [LeafFibre.matrix_eq_sum_fibre]
  refine Finset.sum_eq_zero fun E hE ↦ ?_
  obtain ⟨⟨hS, hR⟩, hT⟩ := (LeafFibre.mem_rowFibre _ _ _ _).mp hE
  exact absurd hT (h ⟨E, hS⟩ hR)

/-- The tail columns. -/
theorem matrix_tail_column (r : Fin T.P) (j : Fin k) (s : CatSlot (c j)) :
    GluingDatum.LengthMatrixPresentation.matrix M.fullDim.labelling.presentation r
        (M.fullDim.labelling.targetEdge.symm (tEdge T hc M j s)) =
      if r = M.fullDim.labelling.row (TailAt.row (cat T j) M s) then tailWeight T hc M ⟨j, s⟩
      else 0 := by
  rcases s with i | i | i
  · have h := MarkedCount.Lollipops.matrix_column_of_unique M.fullDim
      (TailAt.pathE (cat T j) M (T.cubic hc) i).2
      (fun F hF hT ↦ (TailAt.lone_pathE (cat T j) M (T.cubic hc) i).2 F hF hT) r
    refine h.trans (if_congr ?_ rfl rfl)
    exact Iff.of_eq (congrArg (fun q ↦ r = M.fullDim.labelling.row q)
      (TailAt.lone_pathE (cat T j) M (T.cubic hc) i).stablePath)
  · have h := MarkedCount.Lollipops.matrix_column_of_unique M.fullDim
      (TailAt.bridgeAt (cat T j) M i.castSucc).2
      (fun F hF hT ↦ LoopAt.eq_bridgeE M ((cat T j).isLoop i.castSucc) hF hT) r
    have hR := TailAt.bridgeAt_stablePath (cat T j) M (T.cubic hc) i.castSucc
    rw [bulbBridge_castSucc] at hR
    refine h.trans (if_congr ?_ ?_ rfl)
    · exact Iff.of_eq (congrArg (fun q ↦ r = M.fullDim.labelling.row q) hR)
    · show _ = (1 / 2 : ℚ)
      rw [TailAt.bridgeAt_index]
      norm_num
  · have h := LeafFibre.matrix_leafEdge_column M.fullDim (LoopAt.vC_isLeaf M ((cat T j).isLoop i)) r
    refine h.trans (if_congr ?_ rfl rfl)
    exact Iff.of_eq (congrArg (fun q ↦ r = q)
      (LollipopLeafRow.leafRow_loopLeaf M ((cat T j).isLoop i)))

theorem ite_neg' {α : Sort*} {p' : Prop} [Decidable p'] (h : ¬ p') (a b : α) :
    (if p' then a else b) = b := by simp [h]

/-- **The block decomposition** `A_φ ≅ A_ψ ⊕ diag(1/s, 1/2, 2)` (rigidity (5)). -/
theorem submatrix_eq_fromBlocks :
    (GluingDatum.LengthMatrixPresentation.matrix M.fullDim.labelling.presentation).submatrix
        (rowBlocks T M) (colBlocks T hc M) =
      Matrix.fromBlocks
        (GluingDatum.LengthMatrixPresentation.matrix (labelling T hc M m hm).presentation) 0 0
        (tailBlock T hc M) := by
  ext (i | ⟨j, s⟩) (i' | ⟨j', s'⟩)
  · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, rowBlocks_inl]
    exact (matrix_labelling T hc M m hm i i').symm
  · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, rowBlocks_inl]
    refine matrix_eq_zero_of_fibre T M _ _ fun F hF hT ↦ ?_
    have hr : F.stablePath = M.ident.row.symm (T.coreSlot i) :=
      M.fullDim.labelling.row.injective hF
    have hk := (keptRow_iff T hc M (M.ident.row.symm (T.coreSlot i))).mpr
      ⟨i, by rw [Equiv.apply_symm_apply]⟩
    rw [← hr] at hk
    exact not_keptEdge_tEdge T hc M j' s' (hT ▸ (keptRow_mk (hP := deletionPattern T hc M) F).mp hk)
  · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, rowBlocks_inr]
    refine matrix_eq_zero_of_fibre T M _ _ fun F hF hT ↦ ?_
    have hr : F.stablePath = TailAt.row (cat T j) M s := M.fullDim.labelling.row.injective hF
    have hT' := TailAt.over_tcol_of_onRow (cat T j) M (T.cubic hc) s hr
    exact not_keptEdge_tEdge T hc M j s (by rw [tEdge, ← hT', hT]; exact keptEdge_edgeIncl _)
  · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, rowBlocks_inr]
    change GluingDatum.LengthMatrixPresentation.matrix _ _
      (M.fullDim.labelling.targetEdge.symm (tEdge T hc M j' s')) = _
    rw [matrix_tail_column, tailBlock, Matrix.diagonal_apply]
    by_cases h : (⟨j, s⟩ : Σ j, CatSlot (c j)) = ⟨j', s'⟩
    · obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp h
      obtain rfl := eq_of_heq h2
      simp
    · rw [ite_neg' h, ite_neg']
      intro h'
      exact h (row_inj T M (M.fullDim.labelling.row.injective h'))

/-! ## 3.  The determinant -/

/-- **`|det A_φ| = |det A_ψ| · ∏ (tail weights)`.** -/
theorem abs_det_labelling :
    |(GluingDatum.LengthMatrixPresentation.matrix M.fullDim.labelling.presentation).det| =
      |(GluingDatum.LengthMatrixPresentation.matrix (labelling T hc M m hm).presentation).det| *
        |∏ q, tailWeight T hc M q| := by
  set A := GluingDatum.LengthMatrixPresentation.matrix M.fullDim.labelling.presentation
  have h := congrArg Matrix.det (submatrix_eq_fromBlocks T hc M m hm)
  rw [Matrix.det_fromBlocks_zero₂₁, tailBlock, Matrix.det_diagonal] at h
  have hσ : A.submatrix (rowBlocks T M) (colBlocks T hc M) =
      (A.submatrix id ((rowBlocks T M).symm.trans (colBlocks T hc M))).submatrix (rowBlocks T M)
        (rowBlocks T M) := by
    ext a b
    simp
  rw [hσ, Matrix.det_submatrix_equiv_self, Matrix.det_permute'] at h
  rw [← abs_mul, ← h]
  rcases Int.units_eq_one_or (Equiv.Perm.sign ((rowBlocks T M).symm.trans (colBlocks T hc M))) with
    hs | hs <;> simp [hs]

theorem tailWeight_ne_zero (q : Σ j, CatSlot (c j)) : tailWeight T hc M q ≠ 0 := by
  rcases q with ⟨j, i | i | i⟩
  · simp only [tailWeight]
    have := one_le_sPath T hc M j i
    positivity
  · simp [tailWeight]
  · simp [tailWeight]

theorem det_labelling_ne_zero :
    (GluingDatum.LengthMatrixPresentation.matrix (labelling T hc M m hm).presentation).det ≠ 0 := by
  intro h
  have := abs_det_labelling T hc M m hm
  rw [h, abs_zero, zero_mul] at this
  exact M.fullDim.det_ne_zero (abs_eq_zero.mp this)

/-! ## 4.  Coordinates -/

theorem slot_rowBlocks (q : SlotT (p := p) (c := c)) :
    M.ident.row (M.fullDim.labelling.row.symm (rowBlocks T M q)) = T.slotEquiv q := by
  simp [rowBlocks]

/-- **The coordinates split**: for any solution of the
realization equation, the core coordinates solve `ψ`'s system, and each tail coordinate is the
tail length over the tail weight. -/
theorem coords_blocks (Y : Fin T.P → ℚ) (z : Fin T.P → ℚ)
    (hz : GluingDatum.LengthMatrixPresentation.matrix M.fullDim.labelling.presentation *ᵥ z =
      fun row ↦ Y (M.ident.row (M.fullDim.labelling.row.symm row))) :
    (GluingDatum.LengthMatrixPresentation.matrix (labelling T hc M m hm).presentation *ᵥ
        (fun i ↦ z (colIncl T hc M i)) = fun i ↦ Y (T.coreSlot i)) ∧
      ∀ q : Σ j, CatSlot (c j), tailWeight T hc M q *
          z (M.fullDim.labelling.targetEdge.symm (tEdge T hc M q.1 q.2)) =
        Y (T.tailSlot q.1 q.2) := by
  set A := GluingDatum.LengthMatrixPresentation.matrix M.fullDim.labelling.presentation
  have hBlocks := submatrix_eq_fromBlocks T hc M m hm
  have hEq : A.submatrix (rowBlocks T M) (colBlocks T hc M) *ᵥ (z ∘ colBlocks T hc M) =
      fun q ↦ Y (T.slotEquiv q) := by
    rw [Matrix.submatrix_mulVec_equiv]
    funext q
    simp only [Function.comp_apply]
    have : (z ∘ ⇑(colBlocks T hc M)) ∘ ⇑(colBlocks T hc M).symm = z := by
      funext c'; simp
    rw [this, hz]
    exact congrArg Y (slot_rowBlocks T M q)
  rw [hBlocks, Matrix.fromBlocks_mulVec] at hEq
  simp only [Matrix.zero_mulVec, add_zero, zero_add] at hEq
  refine ⟨?_, fun q ↦ ?_⟩
  · funext i
    have := congrFun hEq (Sum.inl i)
    simp only [Sum.elim_inl] at this
    exact this
  · have := congrFun hEq (Sum.inr q)
    simp only [Sum.elim_inr, tailBlock, Matrix.mulVec_diagonal, Function.comp_apply] at this
    exact this

/-! ## 5.  Row denominators -/

section Denominators

open DraismaVargas.Count.TrivalentWeight (commonDenominator_equiv)

theorem rowDenominator_rowBlocks (t : SlotT (p := p) (c := c)) :
    Count.rowDenominator M.fullDim.labelling.presentation (rowBlocks T M t) =
      commonDenominator Finset.univ (fun s' ↦ Matrix.fromBlocks
        (GluingDatum.LengthMatrixPresentation.matrix (labelling T hc M m hm).presentation) 0 0
        (tailBlock T hc M) t s') := by
  rw [← submatrix_eq_fromBlocks T hc M m hm, Count.rowDenominator,
    ← commonDenominator_equiv (colBlocks T hc M)]
  rfl

theorem rowDenominator_inl (i : Fin p) :
    Count.rowDenominator M.fullDim.labelling.presentation (rowBlocks T M (Sum.inl i)) =
      Count.rowDenominator (labelling T hc M m hm).presentation i := by
  rw [rowDenominator_rowBlocks T hc M m hm]
  have : (fun s' ↦ Matrix.fromBlocks
      (GluingDatum.LengthMatrixPresentation.matrix (labelling T hc M m hm).presentation) 0 0
      (tailBlock T hc M) (Sum.inl i) s') =
      Sum.elim (GluingDatum.LengthMatrixPresentation.matrix (labelling T hc M m hm).presentation i)
        (fun _ ↦ 0) := by
    funext s'; rcases s' with a | b <;> simp
  rw [this, MarkedCount.Lollipops.commonDenominator_sumElim,
    MarkedCount.Lollipops.commonDenominator_zero, Nat.lcm_one_right]
  rfl

include hm in
theorem rowDenominator_inr (q : Σ j, CatSlot (c j)) :
    Count.rowDenominator M.fullDim.labelling.presentation (rowBlocks T M (Sum.inr q)) =
      (tailWeight T hc M q).den := by
  classical
  rw [rowDenominator_rowBlocks T hc M m hm]
  have : (fun s' ↦ Matrix.fromBlocks
      (GluingDatum.LengthMatrixPresentation.matrix (labelling T hc M m hm).presentation) 0 0
      (tailBlock T hc M) (Sum.inr q) s') =
      fun s' ↦ if s' = Sum.inr q then tailWeight T hc M q else 0 := by
    funext s'
    rcases s' with a | b
    · simp
    · simp only [Matrix.fromBlocks_apply₂₂, tailBlock, Matrix.diagonal_apply]
      by_cases h : q = b
      · subst h; simp
      · rw [ite_neg' h, ite_neg' (fun h' ↦ h (Sum.inr_injective h').symm)]
  rw [this, MarkedCount.Lollipops.commonDenominator_single]

/-- **`D_φ = D_ψ · ∏ (denominators of the tail weights)`.** -/
theorem denominatorProduct_labelling :
    Count.denominatorProduct M.fullDim.labelling.presentation =
      Count.denominatorProduct (labelling T hc M m hm).presentation *
        ∏ q, (tailWeight T hc M q).den := by
  rw [Count.denominatorProduct, ← Fintype.prod_equiv (rowBlocks T M) _ _ (fun _ ↦ rfl),
    Fintype.prod_sum_type]
  simp only [rowDenominator_inl T hc M m hm, rowDenominator_inr T hc M m hm]
  rfl

end Denominators

/-- **The tail factor**: `D · |det|` grows by `2^{a}` per tail of genus `a` (the slopes cancel). -/
theorem tailWeight_den_mul_abs (q : Σ j, CatSlot (c j)) :
    ((tailWeight T hc M q).den : ℚ) * |tailWeight T hc M q| =
      match q with
      | ⟨_, Sum.inl _⟩ => 1
      | ⟨_, Sum.inr (Sum.inl _)⟩ => 1
      | ⟨_, Sum.inr (Sum.inr _)⟩ => 2 := by
  rcases q with ⟨j, i | i | i⟩
  · simp only [tailWeight]
    have hs := one_le_sPath T hc M j i
    have hpos : (0 : ℚ) < sPath T hc M j i := by exact_mod_cast hs
    rw [abs_of_pos (by positivity)]
    have hden : (1 / (sPath T hc M j i : ℚ)).den = sPath T hc M j i := by
      rw [one_div, Rat.inv_natCast_den]
      simp only [ite_eq_right_iff]
      omega
    rw [hden]
    field_simp
  · simp [tailWeight]
  · simp [tailWeight]

end

end DraismaVargas.Count.MarkedCountGeneral.TailRestrict
