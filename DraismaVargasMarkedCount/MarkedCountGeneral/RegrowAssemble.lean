module

public import DraismaVargasMarkedCount.MarkedCountGeneral.RegrowFrame

@[expose] public section

/-!
# Regrowth, part 11: the regrown frame

The regrowth
of a typed frame `κ` with slopes `s` is a frame over the tailed core `T.H`:

* `fullDim`: every field of `FullDimensionalSourcePresentation`, with the labelling by the slots of
  `T.H` (`T.slotEquiv`: core slots, then the tail slots), the block-diagonal matrix
  `A_κ ⊕ diag(tailDiag)` (`matrix_labelling`, `det_labelling`), and the dimension count from the
  typed one (`saturated`: the tails add `3a_j - 1` target edges and genus `a_j`, the new sheets
  the degree);
* `ident`: the identification of the stable graph with `T.H`, through `T.vertexEquiv` and
  `T.slotEquiv`, with the incidences of the caterpillar (`coreIncidence_*`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral

namespace CatRegrow

noncomputable section

open DraismaVargas.Infrastructure CatSlot TailV
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open DraismaVargas.Count.MarkedCount
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {c : Fin k → ℕ}

/-! ## 1.  Incidences of the tailed core -/

section Incidence

variable (T : Tailed core mark c)

theorem coreIncidence_old_core (v : Fin n) (i : Fin p) :
    Count.coreIncidence T.H (T.vertexEquiv (.inl v)) (T.slotEquiv (.inl i)) =
      Count.coreIncidence core v i := by
  unfold Count.coreIncidence
  rw [T.tail_core, T.head_core]
  simp only [EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq]

theorem coreIncidence_tail_core (j : Fin k) (w : CatVertex (c j)) (i : Fin p) :
    Count.coreIncidence T.H (T.vertexEquiv (.inr ⟨j, w⟩)) (T.slotEquiv (.inl i)) = 0 := by
  unfold Count.coreIncidence
  rw [T.tail_core, T.head_core]
  simp

theorem tailName_eq_inl_iff (j : Fin k) (o : Option (CatVertex (c j))) (v : Fin n) :
    Tailed.tailName mark c j o = .inl v ↔ o = none ∧ mark j = v := by
  rcases o with _ | x <;> simp [Tailed.tailName]

theorem tailName_eq_inr_self (j : Fin k) (o : Option (CatVertex (c j))) (w : CatVertex (c j)) :
    Tailed.tailName mark c j o = .inr ⟨j, w⟩ ↔ o = some w := by
  rcases o with _ | x
  · simp [Tailed.tailName]
  · simp [Tailed.tailName]

theorem tailName_ne_inr {j j' : Fin k} (hj : j ≠ j') (o : Option (CatVertex (c j)))
    (w : CatVertex (c j')) : Tailed.tailName mark c j o ≠ .inr ⟨j', w⟩ := by
  rcases o with _ | x
  · simp [Tailed.tailName]
  · simp [Tailed.tailName, hj]

/-- `lTail` is the caterpillar's tail end, read in `TailV`. -/
theorem lTail_eq_map {c' : ℕ} (s : CatSlot c') :
    lTail s = (catTail (none : Option (CatVertex c')) some s).map Sum.inl := by
  rcases s with i | i | i
  · induction i using Fin.cases <;> simp [lTail, catTail]
  · simp [lTail, catTail]
  · simp [lTail, catTail]

theorem catTail_none_some_eq_none_iff {c' : ℕ} (s : CatSlot c') :
    catTail (none : Option (CatVertex c')) some s = none ↔ s = path 0 := by
  rw [← lTail_eq_none_iff, lTail_eq_map, Option.map_eq_none_iff]

theorem catHead_none_some_ne_none {c' : ℕ} (s : CatSlot c') :
    catHead (none : Option (CatVertex c')) some s ≠ none := by
  rcases s with i | i | i
  · induction i using Fin.lastCases <;> simp [catHead]
  · simp [catHead]
  · simp [catHead]

theorem coreIncidence_old_tail (v : Fin n) (t : TE c) :
    Count.coreIncidence T.H (T.vertexEquiv (.inl v)) (T.slotEquiv (.inr t)) =
      if t.2 = path 0 ∧ mark t.1 = v then 1 else 0 := by
  obtain ⟨j, s⟩ := t
  unfold Count.coreIncidence
  rw [T.tail_slotEquiv, T.head_slotEquiv, Tailed.canonicalTail_inr, Tailed.canonicalHead_inr]
  simp only [EmbeddingLike.apply_eq_iff_eq, tailName_eq_inl_iff, catTail_none_some_eq_none_iff,
    catHead_none_some_ne_none s, false_and, ite_false, add_zero]

theorem catTail_none_some_eq_some_iff {c' : ℕ} (s : CatSlot c') (w : CatVertex c') :
    catTail (none : Option (CatVertex c')) some s = some w ↔ lTail s = some (Sum.inl w) := by
  rw [lTail_eq_map]
  cases catTail (none : Option (CatVertex c')) some s <;> simp

theorem catHead_none_some_eq_some_iff {c' : ℕ} {s : CatSlot c'} (hs : ∀ i, s ≠ loop i)
    (w : CatVertex c') :
    catHead (none : Option (CatVertex c')) some s = some w ↔ lHead s = Sum.inl w := by
  rcases slot_cases s with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · induction i using Fin.lastCases with
    | last =>
      simp only [lHead_path_last, bulb]
      simp [catHead, path]
    | cast i =>
      simp only [lHead_path_castSucc, spine]
      simp [catHead, path]
  · simp only [lHead_bridge, bulb]
    simp [catHead, bridge]
  · exact absurd rfl (hs i)

/-- **The incidences of a tail slot at a tail vertex of `T.H`.** -/
theorem coreIncidence_tail_tail (j : Fin k) (w : CatVertex (c j)) (s : CatSlot (c j)) :
    Count.coreIncidence T.H (T.vertexEquiv (.inr ⟨j, w⟩)) (T.slotEquiv (.inr ⟨j, s⟩)) =
      if s ∈ incSlots (Sum.inl w) then (if ∃ i, s = loop i then 2 else 1) else 0 := by
  classical
  unfold Count.coreIncidence
  rw [T.tail_slotEquiv, T.head_slotEquiv, Tailed.canonicalTail_inr, Tailed.canonicalHead_inr]
  simp only [EmbeddingLike.apply_eq_iff_eq]
  simp only [tailName_eq_inr_self, mem_incSlots]
  by_cases hs : ∃ i, s = loop i
  · obtain ⟨i, rfl⟩ := hs
    simp only [lTail_loop, lHead_loop, Option.some.injEq, bulb, tip, reduceCtorEq, or_false]
    simp only [catTail, catHead, loop, Option.some.injEq]
    by_cases h : Sum.inr i = w
    · subst h; simp
    · simp [h]
  · rw [ite_eq_right hs]
    simp only [catTail_none_some_eq_some_iff, catHead_none_some_eq_some_iff (fun i h ↦ hs ⟨i, h⟩)]
    by_cases h1 : lTail s = some (Sum.inl w)
    · have h2 : lHead s ≠ Sum.inl w := by
        intro h2
        exact lTail_ne_lHead s (by rw [h1, h2])
      simp [h1, h2]
    · simp [h1]

theorem coreIncidence_tail_tail_ne {j j' : Fin k} (hj : j' ≠ j) (w : CatVertex (c j))
    (s : CatSlot (c j')) :
    Count.coreIncidence T.H (T.vertexEquiv (.inr ⟨j, w⟩)) (T.slotEquiv (.inr ⟨j', s⟩)) = 0 := by
  unfold Count.coreIncidence
  rw [T.tail_slotEquiv, T.head_slotEquiv, Tailed.canonicalTail_inr, Tailed.canonicalHead_inr]
  simp only [EmbeddingLike.apply_eq_iff_eq, tailName_ne_inr hj, ite_false, add_zero]

end Incidence

/-! ## 2.  The frame -/

section Frame

variable (T : Tailed core mark c) (hd : IsTailDegree n p c degree)
  (J : LowerIndex c) (κ : TypedFrame core mark (lowerType c J) (degree - shed J))
  (s : SlopeData c J)

local notation "β" => branching hd J κ s

/-- The column dictionary: core columns, then tail columns. -/
def colEquiv : Fin p ⊕ TE c ≃ (catTarget c κ.target (β).x).edges :=
  (Equiv.sumCongr κ.fullDim.labelling.targetEdge (Equiv.refl _)).trans (occEquiv c (β).x)

@[simp] theorem colEquiv_inl (i : Fin p) :
    colEquiv hd J κ s (.inl i) = oldE c (β).x (κ.fullDim.labelling.targetEdge i) := rfl
@[simp] theorem colEquiv_inr (t : TE c) : colEquiv hd J κ s (.inr t) = tailE c (β).x t := rfl

/-- The row dictionary of the labelling. -/
def labRow : MarkedStablePath κ.data (markSet κ.markSource) ⊕ TE c ≃ Fin p ⊕ TE c :=
  Equiv.sumCongr κ.fullDim.labelling.row (Equiv.refl _)

/-- The row dictionary of the label. -/
def identRow : MarkedStablePath κ.data (markSet κ.markSource) ⊕ TE c ≃ Fin p ⊕ TE c :=
  Equiv.sumCongr κ.ident.row (Equiv.refl _)

/-- The stable paths of the regrowth, by rows. -/
abbrev pathEquiv : StablePath (β).regrowDatum ≃ MarkedStablePath κ.data (markSet κ.markSource) ⊕ TE c :=
  (β).stablePathEquiv (hψ J κ) (hT J κ) (hT0 J κ) (hMark hd J κ s)

/-- **The stable labelling of the regrowth**, by the slots of `T.H`. -/
def labelling : StableLengthMatrixLabelling (β).regrowDatum (Fin T.P) where
  targetEdge := T.slotEquiv.symm.trans (colEquiv hd J κ s)
  row := (pathEquiv hd J κ s).trans ((labRow J κ).trans T.slotEquiv)

/-- The block matrix: the marked matrix of `κ`, then the diagonal of the tails. -/
def blockMatrix : Matrix (Fin p ⊕ TE c) (Fin p ⊕ TE c) ℚ :=
  Matrix.fromBlocks κ.matrix 0 0 (Matrix.diagonal (β).tailDiag)

open Classical in
theorem markedEntry_eq (P : MarkedStablePath κ.data (markSet κ.markSource)) (ε : κ.target.edges) :
    (∑ F : NonDanglingEdge κ.data,
        if markedRow (markSet κ.markSource) F = P ∧ F.1.1.1 = ε then
          (1 : ℚ) / κ.data.sourceEdgeIndex F.1 else 0) =
      markedMatrix κ.data (markSet κ.markSource) P ε := by
  classical
  unfold markedMatrix markedOccurrences
  symm
  convert MarkedCount.Regrow.sum_filter_nonDangling κ.data
    (fun F ↦ markedRow (markSet κ.markSource) F = P) ε
    (fun e ↦ (1 : ℚ) / κ.data.sourceEdgeIndex e) using 1

theorem matrix_labelling :
    GluingDatum.LengthMatrixPresentation.matrix (labelling T hd J κ s).presentation =
      (blockMatrix hd J κ s).submatrix T.slotEquiv.symm T.slotEquiv.symm := by
  funext r col
  obtain ⟨z, rfl⟩ := T.slotEquiv.surjective r
  obtain ⟨w, rfl⟩ := T.slotEquiv.surjective col
  rw [StableSourceMatrix.labelling_matrix_eq, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  have hRow : (labelling T hd J κ s).row.symm (T.slotEquiv z) =
      (β).tagPath (hψ J κ) (hT J κ) (hT0 J κ) (hMark hd J κ s) ((labRow J κ).symm z) := by
    simp only [labelling, Equiv.symm_trans_apply, Equiv.symm_apply_apply]
    rfl
  have hCol : (labelling T hd J κ s).targetEdge (T.slotEquiv w) = colEquiv hd J κ s w := by
    simp [labelling]
  rw [hRow, hCol]
  rcases z with i | t <;> rcases w with i' | t'
  · rw [colEquiv_inl]
    refine ((β).matrix_inl_oldE (hψ J κ) (hT J κ) (hT0 J κ) (hMark hd J κ s)
      (κ.fullDim.labelling.row.symm i) (κ.fullDim.labelling.targetEdge i')).trans ?_
    rw [blockMatrix, Matrix.fromBlocks_apply₁₁, MarkedFrameBase.matrix, MarkedLabelling.matrix_eq]
    exact markedEntry_eq J κ _ _
  · rw [colEquiv_inr]
    refine ((β).matrix_inl_tailE (hψ J κ) (hT J κ) (hT0 J κ) (hMark hd J κ s)
      (κ.fullDim.labelling.row.symm i) t').trans ?_
    rw [blockMatrix, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
  · rw [colEquiv_inl]
    refine ((β).matrix_inr_oldE (hψ J κ) (hT J κ) (hT0 J κ) (hMark hd J κ s) t
      (κ.fullDim.labelling.targetEdge i')).trans ?_
    rw [blockMatrix, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
  · rw [colEquiv_inr]
    refine ((β).matrix_inr_tailE (hψ J κ) (hT J κ) (hT0 J κ) (hMark hd J κ s) t t').trans ?_
    rw [blockMatrix, Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply]

/-- **The determinant of the regrowth**: block diagonal. -/
theorem det_labelling :
    (GluingDatum.LengthMatrixPresentation.matrix (labelling T hd J κ s).presentation).det =
      κ.matrix.det * ∏ t, (β).tailDiag t := by
  rw [matrix_labelling, Matrix.det_submatrix_equiv_self, blockMatrix,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_diagonal]

theorem det_labelling_ne_zero :
    (GluingDatum.LengthMatrixPresentation.matrix (labelling T hd J κ s).presentation).det ≠ 0 := by
  rw [det_labelling]
  exact mul_ne_zero κ.det_ne_zero (Finset.prod_ne_zero_iff.mpr fun t _ ↦ ((β).tailDiag_pos t).ne')

/-- **The dimension count of the regrowth**, from the typed one. -/
theorem saturated :
    ((catTarget c κ.target (β).x).edges.card : ℤ) =
      2 * genus (β).regrowDatum.sourceGraph + 2 * degree - 5 := by
  have hE := card_edges_catTarget c (β).x
  have hG := (β).genus_regrowDatum (hT0 J κ)
  have hκ := κ.fullDim.saturated
  have hshed := shed_le hd J
  have hgc : ∀ j, 2 * ((β).chain j).genusContribution =
      3 * c j + 4 - ((lowerType c J j : ℤ) + 1) := fun j ↦ by
    rw [((β).valid j).two_mul_genusContribution, card_P_zero]
    push_cast; ring
  have hlt : ∀ j, (lowerType c J j : ℤ) = c j + 1 - 2 * (J j : ℕ) := fun j ↦ by
    unfold lowerType
    have := (J j).2
    push_cast [show 2 * (J j : ℕ) ≤ c j + 1 by omega]
    ring
  have hsum : 2 * ∑ j, ((β).chain j).genusContribution =
      ∑ j, ((3 * c j + 2 : ℕ) : ℤ) - typeExcess (lowerType c J) := by
    rw [Finset.mul_sum]
    simp only [typeExcess]
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hgc j, hlt j]
    ring
  rw [hE, hG]
  have hN : (Fintype.card (Fin (shed J)) : ℤ) = shed J := by simp
  rw [hN]
  push_cast [hshed] at hκ hsum ⊢
  linarith

/-- **The full-dimensional presentation of the regrowth**. -/
def fullDim (hc : IsMarkedCubic core mark) :
    FullDimensionalSource.FullDimensionalSourcePresentation (β).regrowDatum (Fin T.P) where
  valid := ⟨(β).connected_regrowDatum (hψ J κ) (hT J κ),
    (β).riemannHurwitz_regrowDatum (hInj hd J κ s hc) (hRam hd J κ s) κ.fullDim.valid.2⟩
  targetConnected := catTarget_connected c (β).x (hT J κ)
  targetGenus := (genus_catTarget c (β).x).trans (hT0 J κ)
  saturated := saturated hd J κ s
  labelling := labelling T hd J κ s
  det_ne_zero := det_labelling_ne_zero T hd J κ s
  trivalent := (β).nonDanglingValency_le_three (hψ J κ) (hT J κ) (hT0 J κ) (hMark hd J κ s)
    κ.fullDim.trivalent (fun j ↦ κ.fullDim.markValency _ (mem_markSet _ j)) (hInj hd J κ s hc)
  pathEnds := (β).hasPathEnds_regrowDatum (hψ J κ) (hT J κ) (hT0 J κ) (hMark hd J κ s)
    κ.fullDim.pathEnds

/-- The branch vertices of the regrowth, by kinds. -/
abbrev bvEquiv (hc : IsMarkedCubic core mark) :
    MarkedBranchVertex κ.data (markSet κ.markSource) ⊕ (Σ j, CatVertex (c j)) ≃
      BranchVertex (β).regrowDatum :=
  (β).branchVertexEquiv (hψ J κ) (hT J κ) (hT0 J κ) (hMark hd J κ s) (hInj hd J κ s hc)

/-- The vertex dictionary of the label: marked core vertices, then the tail vertices. -/
def vertexSum : MarkedBranchVertex κ.data (markSet κ.markSource) ⊕ (Σ j, CatVertex (c j)) ≃
    Fin T.N :=
  (Equiv.sumCongr κ.ident.vertex (Equiv.refl _)).trans T.vertexEquiv

theorem ident_mark_iff (j : Fin k) (Y : MarkedBranchVertex κ.data (markSet κ.markSource)) :
    κ.markSource j = Y.1 ↔ mark j = κ.ident.vertex Y := by
  rw [← κ.ident.vertex_mark j]
  constructor
  · intro h; congr 1; exact Subtype.ext h
  · intro h; exact congrArg Subtype.val (κ.ident.vertex.injective h)

/-- **The label of the regrowth**: the label of `κ` on the core part, and the caterpillar on the
tails. -/
def ident (hc : IsMarkedCubic core mark) : Count.CoreIdentification T.H (β).regrowDatum where
  vertex := (bvEquiv hd J κ s hc).symm.trans (vertexSum T J κ)
  row := (pathEquiv hd J κ s).trans ((identRow J κ).trans T.slotEquiv)
  incidence := by
    intro branch slot
    obtain ⟨z, rfl⟩ := (bvEquiv hd J κ s hc).surjective branch
    obtain ⟨t, rfl⟩ := ((identRow J κ).trans T.slotEquiv).surjective slot
    have hRow : ((pathEquiv hd J κ s).trans ((identRow J κ).trans T.slotEquiv)).symm
        (((identRow J κ).trans T.slotEquiv) t) =
        (β).tagPath (hψ J κ) (hT J κ) (hT0 J κ) (hMark hd J κ s) t := by
      simp only [Equiv.symm_trans_apply, Equiv.symm_apply_apply]
      rfl
    rw [hRow, Equiv.trans_apply, Equiv.symm_apply_apply]
    rcases z with Y | ⟨j, w⟩ <;> rcases t with P | ⟨j', s'⟩
    · refine ((β).incidenceCount_psiSV_inl (hψ J κ) (hT J κ) (hT0 J κ) (hMark hd J κ s)
        Y.1 P).trans ?_
      change _ = Count.coreIncidence T.H (T.vertexEquiv (.inl (κ.ident.vertex Y)))
          (T.slotEquiv (.inl (κ.ident.row P)))
      rw [coreIncidence_old_core, ← κ.ident.incidence Y, Equiv.symm_apply_apply]
      rfl
    · refine ((β).incidenceCount_psiSV_inr (hψ J κ) (hT J κ) (hT0 J κ) (hMark hd J κ s)
        Y.1 ⟨j', s'⟩).trans ?_
      change _ = Count.coreIncidence T.H (T.vertexEquiv (.inl (κ.ident.vertex Y)))
          (T.slotEquiv (.inr ⟨j', s'⟩))
      rw [coreIncidence_old_tail]
      exact if_congr (and_congr Iff.rfl (ident_mark_iff J κ j' Y)) rfl rfl
    · refine ((β).incidenceCount_tailSV_inl (hψ J κ) (hT J κ) (hT0 J κ) (hMark hd J κ s)
        ⟨j, Sum.inl w⟩ _ P).trans ?_
      change _ = Count.coreIncidence T.H (T.vertexEquiv (.inr ⟨j, w⟩))
          (T.slotEquiv (.inl (κ.ident.row P)))
      rw [coreIncidence_tail_core]
    · refine ((β).incidenceCount_blockSV_inr (hψ J κ) (hT J κ) (hT0 J κ) (hMark hd J κ s)
        ⟨j, Sum.inl w⟩ ⟨j', s'⟩).trans ?_
      change _ = Count.coreIncidence T.H (T.vertexEquiv (.inr ⟨j, w⟩))
          (T.slotEquiv (.inr ⟨j', s'⟩))
      by_cases hj : j' = j
      · subst hj
        rw [coreIncidence_tail_tail]
        simp only [tail_incident_iff, CatBranching.card_rowIdx]
      · rw [coreIncidence_tail_tail_ne T hj, ite_eq_right]
        intro h
        exact hj (tail_incident_mark c (β).x h)

end Frame

end

end CatRegrow

end DraismaVargas.Count.MarkedCountGeneral
