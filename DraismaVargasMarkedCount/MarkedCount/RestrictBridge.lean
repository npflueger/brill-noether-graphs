module

public import DraismaVargasMarkedCount.MarkedCount.RestrictLollipop

@[expose] public section

/-!
# The bridge of a lollipop is a single source edge

The clause `h_b = ⟨w, e_b, u⟩` of the bridge-and-loop lemma (Draisma--Vargas Part I,
arXiv:1909.12924, `lemma-loop-bridge`): the far end of the bridge occurrence `e_b` is a
branch vertex, hence the mark `u`.  This clause is not in the public lollipop package (which
gives `m(e_b) = 2` and the fibre clause only).  The proof
here is Part I's column-dependence argument.  Let `Y` be the far end of `e_b`, over `x`, and
suppose `Y` has surviving valency two, with second survivor `E₂` over `s ≠ φ(e_b)`.  The column
of `φ(e_b)` is `½ e_{h_b}`, since `e_b` is the only survivor over it.

* `x` is not a leaf: `E₂` lies over an edge at `x` other than `φ(e_b)`.
* If `x` is divalent, every survivor over `s` is `E₂`: a block over `x` other than `Y` has no
  survivor over `φ(e_b)`, so all its survivors lie over `s`, and then its local ramification
  is at least its local degree `≥ 2`, above the change budget `1`.  So the column of `s` is a
  multiple of `e_{h_b}` too.
* If `x` is trivalent, `PassOnceLollipop.partner_of_block` matches the survivors over the two
  other edges `s, t` in every row but `h_b`, so `col s - col t` is a multiple of `e_{h_b}`.

Either way three columns are dependent, against `det A_φ ≠ 0`.
-/

namespace DraismaVargas.Count.MarkedCount.Lollipops

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.RowWalk (OnRow)
open Utilities.Certificate.ExplicitPotential (Core)
open scoped DraismaVargas.Infrastructure.GluingContraction

noncomputable section

/-! ## 1.  Generic facts -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Three columns with a nontrivial vanishing combination kill the determinant. -/
theorem det_eq_zero_of_columns (A : Matrix ι ι ℚ) {p q l : ι} (hpq : p ≠ q) (hpl : p ≠ l)
    {a b c : ℚ} (ha : a ≠ 0) (h : ∀ r, a * A r p + b * A r q + c * A r l = 0) : A.det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨a • Pi.single p 1 + b • Pi.single q 1 + c • Pi.single l 1, ?_, ?_⟩
  · intro hv
    have := congrFun hv p
    simp [hpq.symm, hpl.symm] at this
    exact ha this
  · ext r
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_single, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.col_apply, MulOpposite.op_one, one_smul]
    linarith [h r]

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}

/-- **The indices of incident occurrences over one target edge add up to at most the local
degree**: their sheet blocks are disjoint inside the vertex block. -/
theorem sum_index_le_blockCard {Z : data.SourceVertex} {t : target.edges}
    (S : Finset (IncidentSourceEdge data Z)) (hS : ∀ F ∈ S, F.1.1.1 = t) :
    (∑ F ∈ S, (data.sourceEdgeIndex F.1 : ℤ)) ≤
      ((data.vertexPartition Z.1.1).blockCard Z.1.2 : ℤ) := by
  classical
  have hBlocks : ∀ F ∈ S, (data.edgePartition t).block F.1.1.2 ⊆
      (data.vertexPartition Z.1.1).block Z.1.2 := by
    intro F hF σ hσ
    obtain ⟨hMem, hRel⟩ := (incident_iff_target_mem_and_rel data F.1 Z).mp F.2
    have hRef := StableLocalProperties.refines_of_mem_incidentEdges data hMem
    rw [SheetPartition.mem_block_iff] at hσ ⊢
    rw [← hS F hF] at hσ
    exact hRel.trans (hRef.rel hσ)
  have hIndex : ∀ F ∈ S, (data.sourceEdgeIndex F.1 : ℤ) =
      ((data.edgePartition t).block F.1.1.2).card := by
    intro F hF
    unfold GluingDatum.sourceEdgeIndex SheetPartition.blockCard
    rw [hS F hF]
  have hDisj : (S : Set (IncidentSourceEdge data Z)).PairwiseDisjoint
      (fun F ↦ (data.edgePartition t).block F.1.1.2) := by
    intro F hF G hG hFG
    rw [Function.onFun, Finset.disjoint_left]
    intro σ h1 h2
    apply hFG
    rw [SheetPartition.mem_block_iff] at h1 h2
    have hF2 := F.1.2
    have hG2 := G.1.2
    rw [hS F hF] at hF2
    rw [hS G hG] at hG2
    have : F.1.1.2 = G.1.1.2 := by
      have e1 : (data.edgePartition t).repr F.1.1.2 = (data.edgePartition t).repr σ := h1
      have e2 : (data.edgePartition t).repr G.1.1.2 = (data.edgePartition t).repr σ := h2
      rw [← hF2, ← hG2, e1, e2]
    exact Subtype.ext (Subtype.ext (Prod.ext ((hS F hF).trans (hS G hG).symm) this))
  rw [Finset.sum_congr rfl hIndex]
  have hCard := Finset.card_biUnion hDisj
  have hSub : S.biUnion (fun F ↦ (data.edgePartition t).block F.1.1.2) ⊆
      (data.vertexPartition Z.1.1).block Z.1.2 :=
    Finset.biUnion_subset.mpr hBlocks
  have := Finset.card_le_card hSub
  unfold SheetPartition.blockCard
  exact_mod_cast (show (∑ F ∈ S, ((data.edgePartition t).block F.1.1.2).card) ≤ _ by omega)

end Generic

/-! ## 2.  The far end of a lone survivor -/

section FarEnd

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (fd : FullDimensionalSourcePresentation data coordinate)

/-- The column of a target edge over which a single occurrence survives. -/
theorem matrix_column_of_unique {E : data.SourceEdge} (hE : ¬ IsDangling data E)
    (hUnique : ∀ F, ¬ IsDangling data F → F.1.1 = E.1.1 → F = E) (r : coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation r
        (fd.labelling.targetEdge.symm E.1.1) =
      if r = fd.labelling.row (NonDanglingEdge.stablePath (⟨E, hE⟩ : NonDanglingEdge data))
      then 1 / (data.sourceEdgeIndex E : ℚ) else 0 := by
  classical
  rw [LeafFibre.matrix_eq_sum_fibre]
  split_ifs with hr
  · rw [Finset.sum_eq_single E]
    · intro F hF hFE
      obtain ⟨⟨hFS, -⟩, hFT⟩ := (LeafFibre.mem_rowFibre _ _ _ _).mp hF
      exact absurd (hUnique F hFS hFT) hFE
    · intro hNot
      exact absurd ((LeafFibre.mem_rowFibre _ _ _ _).mpr ⟨⟨hE, hr.symm⟩, rfl⟩) hNot
  · refine Finset.sum_eq_zero fun F hF ↦ ?_
    obtain ⟨⟨hFS, hFR⟩, hFT⟩ := (LeafFibre.mem_rowFibre _ _ _ _).mp hF
    have := hUnique F hFS hFT
    subst this
    exact absurd hFR.symm hr

include fd in
/-- **The far end of a lone survivor is not interior to a stable row.**  If `E` is the only
survivor over its target edge, neither of its ends has surviving valency two.  This is the
column-dependence argument of Part I. -/
theorem nonDanglingValency_ne_two_of_unique {E : data.SourceEdge} (hE : ¬ IsDangling data E)
    (hUnique : ∀ F, ¬ IsDangling data F → F.1.1 = E.1.1 → F = E) {Y : data.SourceVertex}
    (hY : Incident data E Y) : nonDanglingValency data Y ≠ 2 := by
  classical
  intro h2
  set L := fd.labelling
  set x := Y.1.1 with hx
  obtain ⟨E2, ⟨hNe, hE2, hInc2⟩, -⟩ :=
    exists_unique_other_of_nonDanglingValency_eq_two data h2 hE hY
  set t := E.1.1 with ht
  set s := E2.1.1 with hs
  have hst : s ≠ t := fun h ↦ hNe (hUnique E2 hE2 h)
  have hsMem : s ∈ GluingDatum.incidentEdges x :=
    ((incident_iff_target_mem_and_rel data E2 Y).mp hInc2).1
  have htMem : t ∈ GluingDatum.incidentEdges x :=
    ((incident_iff_target_mem_and_rel data E Y).mp hY).1
  set rowE := L.row (NonDanglingEdge.stablePath (⟨E, hE⟩ : NonDanglingEdge data)) with hRowE
  have hRow2 : L.row (NonDanglingEdge.stablePath (⟨E2, hE2⟩ : NonDanglingEdge data)) = rowE := by
    rw [hRowE, stablePath_eq_of_consecutive
      (⟨fun h ↦ hNe (congrArg Subtype.val h), Y, hInc2, hY, h2⟩ :
        Consecutive data ⟨E2, hE2⟩ ⟨E, hE⟩)]
  -- survivors at the other blocks over `x` avoid `t`
  have hOther : ∀ Z : data.SourceVertex, Z.1.1 = x → Z ≠ Y → ∀ F, ¬ IsDangling data F →
      Incident data F Z → F.1.1 ≠ t := by
    intro Z hZ hZY F hF hFZ hFt
    have hFE := hUnique F hF hFt
    subst hFE
    exact hZY (LollipopBridgeFibre.eq_of_incident_of_target_eq hZ hFZ hY)
  -- a survivor over an edge at `x`, seen from the block of its sheet
  have hBlockInc : ∀ (u : target.edges), u ∈ GluingDatum.incidentEdges x →
      ∀ g : data.SourceEdge, g.1.1 = u → Incident data g (data.sourceEndpoint x g.1.2) := by
    intro u hu g hgT
    have h := incident_sourceEdge_sourceEndpoint data x u hu g.1.2
    rwa [show data.sourceEdge u g.1.2 = g by rw [← hgT]; exact GluingDatum.sourceEdge_self data g]
      at h
  -- the valency of `x`
  have hRamY := IndexPattern.localRamification_le_targetChange fd (wall := x) ⟨Y.1.2, Y.2⟩
  rw [IndexPattern.targetChange_eq_three_sub_valency fd x] at hRamY
  have hNonnegY := data.localRamification_nonneg x (fd.valid.2 x) ⟨Y.1.2, Y.2⟩
  have hTwoLe : 2 ≤ (GluingDatum.incidentEdges x).card := by
    have : ({s, t} : Finset target.edges) ⊆ GluingDatum.incidentEdges x := by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact hsMem
      · exact htMem
    have h' := Finset.card_le_card this
    rwa [Finset.card_pair hst] at h'
  have hColT := matrix_column_of_unique fd hE hUnique
  have hIdxE : (data.sourceEdgeIndex E : ℚ) ≠ 0 := by
    exact_mod_cast (StableLocalProperties.sourceEdgeIndex_pos data E).ne'
  have hIdxE2 : (data.sourceEdgeIndex E2 : ℚ) ≠ 0 := by
    exact_mod_cast (StableLocalProperties.sourceEdgeIndex_pos data E2).ne'
  have hCard3 : (GluingDatum.incidentEdges x).card ≤ 3 := by omega
  rcases (show (GluingDatum.incidentEdges x).card = 2 ∨ (GluingDatum.incidentEdges x).card = 3 by
    omega) with hVal | hVal
  · -- divalent: the column of `s` is supported on `h_b` too
    have hEdges : GluingDatum.incidentEdges x = {s, t} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl
        · exact hsMem
        · exact htMem
      · rw [hVal, Finset.card_pair hst]
    have hOnlyE2 : ∀ F, ¬ IsDangling data F → F.1.1 = s → F = E2 := by
      intro F hF hFs
      set Z := data.sourceEndpoint x F.1.2
      have hFZ : Incident data F Z := hBlockInc s hsMem F hFs
      by_cases hZY : Z = Y
      · rcases IndexPattern.eq_or_eq_of_nonDanglingValency_two h2 hE hY hE2 hInc2 hNe.symm hF
          (hZY ▸ hFZ) with h | h
        · subst h; exact absurd hFs hst.symm
        · exact h
      · exfalso
        have hZx : Z.1.1 = x := rfl
        -- every survivor at `Z` lies over `s`
        have hAllS : ∀ G : IncidentSourceEdge data Z, ¬ IsDangling data G.1 → G.1.1.1 = s := by
          intro G hG
          have hMem := ((incident_iff_target_mem_and_rel data G.1 Z).mp G.2).1
          rw [hZx, hEdges] at hMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hMem
          rcases hMem with h | h
          · exact h
          · exact absurd h (hOther Z hZx hZY G.1 hG G.2)
        have hPos : 0 < nonDanglingValency data Z :=
          LollipopBridgeFibre.nonDanglingValency_pos_of_survivor hF hFZ
        have hNeOne := NonDanglingValency.nonDanglingValency_ne_one data fd.connected Z
        have hForm := StableLocalProperties.localRamification_eq_nonDangling_form data
          fd.danglingEdgeNoGlue Z
        have hSum := sum_index_le_blockCard
          ((Finset.univ : Finset (IncidentSourceEdge data Z)).filter
            (fun G ↦ ¬ IsDangling data G.1)) (t := s)
          (fun G hG ↦ hAllS G (Finset.mem_filter.mp hG).2)
        have hSumGe : ((nonDanglingValency data Z : ℕ) : ℤ) ≤
            ∑ G ∈ (Finset.univ : Finset (IncidentSourceEdge data Z)).filter
              (fun G ↦ ¬ IsDangling data G.1), (data.sourceEdgeIndex G.1 : ℤ) := by
          rw [← StableLocalProperties.card_filter_not_isDangling_eq_nonDanglingValency]
          rw [Finset.card_eq_sum_ones, Nat.cast_sum]
          exact Finset.sum_le_sum fun G _ ↦ by
            exact_mod_cast StableLocalProperties.sourceEdgeIndex_pos data G.1
        have hRamZ := IndexPattern.localRamification_le_targetChange fd (wall := x) ⟨Z.1.2, Z.2⟩
        rw [IndexPattern.targetChange_eq_three_sub_valency fd x, hVal] at hRamZ
        change data.localRamification Z.1.1 ⟨Z.1.2, Z.2⟩ ≤ _ at hRamZ
        omega
    have hColS : ∀ r, GluingDatum.LengthMatrixPresentation.matrix L.presentation r
        (L.targetEdge.symm s) = if r = rowE then 1 / (data.sourceEdgeIndex E2 : ℚ) else 0 := by
      intro r
      rw [hRow2.symm]
      exact matrix_column_of_unique fd hE2 (fun F hF hFs ↦ hOnlyE2 F hF hFs) r
    refine fd.det_ne_zero (det_eq_zero_of_columns _ (p := L.targetEdge.symm s)
      (q := L.targetEdge.symm t) (l := L.targetEdge.symm t)
      (fun h ↦ hst (L.targetEdge.symm.injective h)) (fun h ↦ hst (L.targetEdge.symm.injective h))
      (a := data.sourceEdgeIndex E2) (b := -(data.sourceEdgeIndex E : ℚ)) (c := 0) hIdxE2 ?_)
    intro r
    rw [hColS r, hColT r]
    split_ifs <;> field_simp <;> ring
  · -- trivalent: the columns of the two other edges agree off `h_b`
    obtain ⟨u, huMem, hus, hut⟩ : ∃ u ∈ GluingDatum.incidentEdges x, u ≠ s ∧ u ≠ t := by
      by_contra hNo
      push Not at hNo
      have hSub : GluingDatum.incidentEdges x ⊆ {s, t} := by
        intro e he
        by_cases hes : e = s
        · simp [hes]
        · simp [hNo e he hes]
      have := Finset.card_le_card hSub
      rw [Finset.card_pair hst] at this
      omega
    have hNoSurvAt : ∀ (v : target.edges), v ∈ GluingDatum.incidentEdges x →
        ∀ (g : data.SourceEdge) (hgS : ¬ IsDangling data g), g.1.1 = v → v ≠ t →
        L.row (NonDanglingEdge.stablePath (⟨g, hgS⟩ : NonDanglingEdge data)) ≠ rowE →
        ∀ F : data.SourceEdge, ¬ IsDangling data F →
          Incident data F (data.sourceEndpoint x g.1.2) → F.1.1 ≠ t := by
      intro v hv g hgS hgT hvt hgRow F hF hFI
      have hgI := hBlockInc v hv g hgT
      refine hOther (data.sourceEndpoint x g.1.2) rfl ?_ F hF hFI
      intro hBY
      rw [hBY] at hgI
      rcases IndexPattern.eq_or_eq_of_nonDanglingValency_two h2 hE hY hE2 hInc2 hNe.symm hgS hgI
        with h | h
      · subst h; exact hvt hgT.symm
      · subst h; exact hgRow hRow2
    have hColumn : ∀ (v w : target.edges), v ∈ GluingDatum.incidentEdges x →
        w ∈ GluingDatum.incidentEdges x → v ≠ t → w ≠ t → v ≠ w → ∀ r, r ≠ rowE →
        GluingDatum.LengthMatrixPresentation.matrix L.presentation r (L.targetEdge.symm v) =
          GluingDatum.LengthMatrixPresentation.matrix L.presentation r (L.targetEdge.symm w) := by
      intro v w hv hw hvt hwt hvw r hr
      rw [LeafFibre.matrix_eq_sum_fibre, LeafFibre.matrix_eq_sum_fibre]
      refine Finset.sum_nbij' (fun g ↦ data.sourceEdge w g.1.2) (fun g ↦ data.sourceEdge v g.1.2)
        ?_ ?_ ?_ ?_ ?_
      · intro g hg
        obtain ⟨⟨hgS, hgRow⟩, hgT⟩ := (LeafFibre.mem_rowFibre _ _ _ _).mp hg
        obtain ⟨hS, hPath, -, -⟩ := PassOnceLollipop.partner_of_block fd
          (B := data.sourceEndpoint x g.1.2) hVal htMem hv hw hvt hwt hvw
          (hNoSurvAt v hv g hgS hgT hvt (by rw [hgRow]; exact hr))
          hgS (hBlockInc v hv g hgT) hgT
        exact (LeafFibre.mem_rowFibre _ _ _ _).mpr ⟨⟨hS, by rw [hPath]; exact hgRow⟩, rfl⟩
      · intro g hg
        obtain ⟨⟨hgS, hgRow⟩, hgT⟩ := (LeafFibre.mem_rowFibre _ _ _ _).mp hg
        obtain ⟨hS, hPath, -, -⟩ := PassOnceLollipop.partner_of_block fd
          (B := data.sourceEndpoint x g.1.2) hVal htMem hw hv hwt hvt (Ne.symm hvw)
          (hNoSurvAt w hw g hgS hgT hwt (by rw [hgRow]; exact hr))
          hgS (hBlockInc w hw g hgT) hgT
        exact (LeafFibre.mem_rowFibre _ _ _ _).mpr ⟨⟨hS, by rw [hPath]; exact hgRow⟩, rfl⟩
      · intro g hg
        obtain ⟨⟨hgS, hgRow⟩, hgT⟩ := (LeafFibre.mem_rowFibre _ _ _ _).mp hg
        exact (PassOnceLollipop.partner_of_block fd
          (B := data.sourceEndpoint x g.1.2) hVal htMem hv hw hvt hwt hvw
          (hNoSurvAt v hv g hgS hgT hvt (by rw [hgRow]; exact hr))
          hgS (hBlockInc v hv g hgT) hgT).2.2.2
      · intro g hg
        obtain ⟨⟨hgS, hgRow⟩, hgT⟩ := (LeafFibre.mem_rowFibre _ _ _ _).mp hg
        exact (PassOnceLollipop.partner_of_block fd
          (B := data.sourceEndpoint x g.1.2) hVal htMem hw hv hwt hvt (Ne.symm hvw)
          (hNoSurvAt w hw g hgS hgT hwt (by rw [hgRow]; exact hr))
          hgS (hBlockInc w hw g hgT) hgT).2.2.2
      · intro g hg
        obtain ⟨⟨hgS, hgRow⟩, hgT⟩ := (LeafFibre.mem_rowFibre _ _ _ _).mp hg
        rw [(PassOnceLollipop.partner_of_block fd
          (B := data.sourceEndpoint x g.1.2) hVal htMem hv hw hvt hwt hvw
          (hNoSurvAt v hv g hgS hgT hvt (by rw [hgRow]; exact hr))
          hgS (hBlockInc v hv g hgT) hgT).2.2.1]
    set c := GluingDatum.LengthMatrixPresentation.matrix L.presentation rowE (L.targetEdge.symm s) -
      GluingDatum.LengthMatrixPresentation.matrix L.presentation rowE (L.targetEdge.symm u)
    refine fd.det_ne_zero (det_eq_zero_of_columns _ (p := L.targetEdge.symm s)
      (q := L.targetEdge.symm u) (l := L.targetEdge.symm t)
      (fun h ↦ hus (L.targetEdge.symm.injective h).symm)
      (fun h ↦ hst (L.targetEdge.symm.injective h))
      (a := 1) (b := -1) (c := -(c * data.sourceEdgeIndex E)) one_ne_zero ?_)
    intro r
    rw [hColT r]
    split_ifs with hr
    · rw [hr]
      field_simp
      ring
    · rw [hColumn s u hsMem huMem hst hut (Ne.symm hus) r hr]
      ring

end FarEnd

/-! ## 3.  The slots of the lollipop core -/

section Slots

variable {n p k : ℕ}

theorem slot_cases (s : Fin (p + (k + k))) :
    (∃ i, s = coreSlot k i) ∨ (∃ j, s = bridgeSlot p j) ∨ (∃ j, s = loopSlot p j) := by
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) s
  · exact Or.inl ⟨i, rfl⟩
  · refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · exact Or.inr (Or.inl ⟨j, rfl⟩)
    · exact Or.inr (Or.inr ⟨j, rfl⟩)

theorem coreSlot_injective : Function.Injective (coreSlot (p := p) k) :=
  Fin.castAdd_injective _ _

theorem bridgeSlot_injective : Function.Injective (bridgeSlot (k := k) p) :=
  fun _ _ h ↦ Fin.castAdd_injective _ _ (Fin.natAdd_injective _ _ h)

theorem loopSlot_injective : Function.Injective (loopSlot (k := k) p) :=
  fun _ _ h ↦ Fin.natAdd_injective _ _ (Fin.natAdd_injective _ _ h)

theorem coreSlot_ne_bridgeSlot (i : Fin p) (j : Fin k) : coreSlot k i ≠ bridgeSlot p j := by
  intro h; have := congrArg Fin.val h; simp [coreSlot, bridgeSlot] at this; omega

theorem coreSlot_ne_loopSlot (i : Fin p) (j : Fin k) : coreSlot k i ≠ loopSlot p j := by
  intro h; have := congrArg Fin.val h; simp [coreSlot, loopSlot] at this; omega

theorem bridgeSlot_ne_loopSlot (i j : Fin k) : bridgeSlot p i ≠ loopSlot p j := by
  intro h; have := congrArg Fin.val h; simp [bridgeSlot, loopSlot] at this; omega

variable (core : Core n p) (mark : Fin k → Fin n)

theorem coreIncidence_lollipopVertex_pos {j : Fin k} {s : Fin (p + (k + k))}
    (h : 0 < Count.coreIncidence (attachLollipops core mark) (lollipopVertex n j) s) :
    s = bridgeSlot p j ∨ s = loopSlot p j := by
  unfold Count.coreIncidence at h
  rcases slot_cases s with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp [(lollipopVertex_ne_oldVertex j _).symm] at h
  · simp only [attachLollipops_tail_bridge, attachLollipops_head_bridge,
      (lollipopVertex_ne_oldVertex j _).symm, lollipopVertex_inj, ite_false, zero_add] at h
    split_ifs at h with hij
    · exact Or.inl (by rw [hij])
    · simp at h
  · simp only [attachLollipops_tail_loop, attachLollipops_head_loop, lollipopVertex_inj] at h
    split_ifs at h with hij
    · exact Or.inr (by rw [hij])
    · simp at h

theorem coreIncidence_bridgeSlot_pos {j : Fin k} {c : Fin (n + k)}
    (h : 0 < Count.coreIncidence (attachLollipops core mark) c (bridgeSlot p j)) :
    c = oldVertex k (mark j) ∨ c = lollipopVertex n j := by
  unfold Count.coreIncidence at h
  rw [attachLollipops_tail_bridge, attachLollipops_head_bridge] at h
  split_ifs at h with h1 h2 h2
  · exact Or.inl h1.symm
  · exact Or.inl h1.symm
  · exact Or.inr h2.symm
  · simp at h

end Slots

/-! ## 4.  The bridge joins `w` to `u` -/

section Member

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n}
  {y : Fin (p + (k + k)) → ℚ} (M : FibreMember (attachLollipops core mark) y degree)

/-- The stable path of the bridge. -/
def bridgePath (j : Fin k) : StablePath M.data :=
  NonDanglingEdge.stablePath (⟨bridgeE M j, bridgeE_survives M j⟩ : NonDanglingEdge M.data)

theorem incidenceCount_pos_of_incident {X : M.data.SourceVertex} {E : M.data.SourceEdge}
    (hE : ¬ IsDangling M.data E) (hX : Incident M.data E X) :
    0 < StablePathCount.incidenceCount M.data X
      (NonDanglingEdge.stablePath (⟨E, hE⟩ : NonDanglingEdge M.data)) :=
  (StablePathCount.incidenceCount_pos_iff _ _ _).mpr ⟨⟨E, hE⟩, hX, rfl⟩

theorem coreIncidence_pos_of_incident (X : StableGraphIncidence.BranchVertex M.data)
    {E : M.data.SourceEdge} (hE : ¬ IsDangling M.data E) (hX : Incident M.data E X.1) :
    0 < Count.coreIncidence (attachLollipops core mark) (M.ident.vertex X)
      (M.ident.row (NonDanglingEdge.stablePath (⟨E, hE⟩ : NonDanglingEdge M.data))) := by
  have h := M.ident.incidence X
    (M.ident.row (NonDanglingEdge.stablePath (⟨E, hE⟩ : NonDanglingEdge M.data)))
  rw [Equiv.symm_apply_apply] at h
  rw [← h]
  exact incidenceCount_pos_of_incident M hE hX

/-- **The bridge row is the bridge slot.** -/
theorem ident_row_bridgePath (j : Fin k) : M.ident.row (bridgePath M j) = bridgeSlot p j := by
  have h := coreIncidence_pos_of_incident M ⟨loopV M j, three_le_loopV M j⟩
    (bridgeE_survives M j) (bridgeE_incident_loopV M j)
  rw [ident_loopV] at h
  rcases coreIncidence_lollipopVertex_pos core mark h with h' | h'
  · exact h'
  · exfalso
    apply (bridgeE_spec M j).2.2.1
    refine ⟨bridgeE_survives M j, ?_⟩
    change bridgePath M j = M.ident.row.symm (loopSlot p j)
    rw [← h', Equiv.symm_apply_apply]
    rfl

theorem bridgePath_eq (j : Fin k) : bridgePath M j = M.ident.row.symm (bridgeSlot p j) := by
  rw [← ident_row_bridgePath, Equiv.symm_apply_apply]

/-- The far end of the bridge, the end other than `w`. -/
def farEnd (j : Fin k) : M.data.SourceVertex :=
  if (M.data.sourceEnds (bridgeE M j)).1 = loopV M j then (M.data.sourceEnds (bridgeE M j)).2
  else (M.data.sourceEnds (bridgeE M j)).1

theorem farEnd_incident (j : Fin k) : Incident M.data (bridgeE M j) (farEnd M j) := by
  unfold farEnd
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem farEnd_ne_loopV (j : Fin k) : farEnd M j ≠ loopV M j := by
  unfold farEnd
  split_ifs with h
  · intro h'
    exact M.data.sourceEnds_ne _ (h.trans h'.symm)
  · exact h

/-- **The bridge-and-loop lemma, `h_b = ⟨w, e_b, u⟩`**: the far end of the bridge is the mark. -/
theorem farEnd_eq_markV (j : Fin k) : farEnd M j = markV M j := by
  have hND : nonDanglingValency M.data (farEnd M j) = 3 := by
    have hne2 := nonDanglingValency_ne_two_of_unique M.fullDim (bridgeE_survives M j)
      (fun F hF hFt ↦ eq_bridgeE M hF hFt) (farEnd_incident M j)
    have hpos := LollipopBridgeFibre.nonDanglingValency_pos_of_survivor (bridgeE_survives M j)
      (farEnd_incident M j)
    have hne1 := NonDanglingValency.nonDanglingValency_ne_one M.data M.fullDim.connected
      (farEnd M j)
    have hle := M.fullDim.trivalent (farEnd M j)
    omega
  have h := coreIncidence_pos_of_incident M ⟨farEnd M j, hND.ge⟩ (bridgeE_survives M j)
    (farEnd_incident M j)
  change 0 < Count.coreIncidence _ _ (M.ident.row (bridgePath M j)) at h
  rw [ident_row_bridgePath] at h
  rcases coreIncidence_bridgeSlot_pos core mark h with h' | h'
  · have : (⟨farEnd M j, hND.ge⟩ : StableGraphIncidence.BranchVertex M.data) =
        M.ident.vertex.symm (oldVertex k (mark j)) := by
      apply M.ident.vertex.injective
      rw [Equiv.apply_symm_apply]
      exact h'
    exact congrArg Subtype.val this
  · exfalso
    apply farEnd_ne_loopV M j
    have : (⟨farEnd M j, hND.ge⟩ : StableGraphIncidence.BranchVertex M.data) =
        ⟨loopV M j, three_le_loopV M j⟩ := by
      apply M.ident.vertex.injective
      rw [h', ident_loopV]
    exact congrArg Subtype.val this

theorem bridgeE_incident_markV (j : Fin k) : Incident M.data (bridgeE M j) (markV M j) :=
  farEnd_eq_markV M j ▸ farEnd_incident M j

/-- The two ends of the bridge: `w` and `u`. -/
theorem incident_bridgeE_iff (j : Fin k) (X : M.data.SourceVertex) :
    Incident M.data (bridgeE M j) X ↔ X = loopV M j ∨ X = markV M j := by
  constructor
  · intro hX
    have hw := bridgeE_incident_loopV M j
    have hf := farEnd_incident M j
    rw [farEnd_eq_markV] at hf
    rcases hX with h | h <;> rcases hw with h1 | h1 <;> rcases hf with h2 | h2 <;>
      first
      | exact Or.inl (h.symm.trans h1)
      | exact Or.inr (h.symm.trans h2)
      | exact absurd (h1.symm.trans h2) (loopV_ne_markV M j j)
  · rintro (rfl | rfl)
    · exact bridgeE_incident_loopV M j
    · exact bridgeE_incident_markV M j

theorem tb_mem_xV (j : Fin k) : tb M j ∈ GluingDatum.incidentEdges (xV M j) :=
  ((incident_iff_target_mem_and_rel M.data _ _).mp (bridgeE_incident_markV M j)).1

theorem xV_ne_uP (j : Fin k) : xV M j ≠ uP M j := by
  intro h
  exact loopV_ne_markV M j j (LollipopBridgeFibre.eq_of_incident_of_target_eq h.symm
    (bridgeE_incident_loopV M j) (bridgeE_incident_markV M j))

/-- The ends of `φ(e_b)` are `φ(u)` and `φ(w)`. -/
theorem tb_ends (j : Fin k) :
    ((tb M j : M.target.V × M.target.V).1 = xV M j ∧
        (tb M j : M.target.V × M.target.V).2 = uP M j) ∨
      ((tb M j : M.target.V × M.target.V).1 = uP M j ∧
        (tb M j : M.target.V × M.target.V).2 = xV M j) := by
  have hx := Count.fst_eq_or_snd_eq_of_mem_incidentEdges (tb_mem_xV M j)
  have hu := Count.fst_eq_or_snd_eq_of_mem_incidentEdges (tb_mem_uP M j)
  have hne := GluingContraction.fst_ne_snd (tb M j)
  rcases hx with hx | hx <;> rcases hu with hu | hu
  · exact absurd (hx.symm.trans hu) (xV_ne_uP M j)
  · exact Or.inl ⟨hx, hu⟩
  · exact Or.inr ⟨hu, hx⟩
  · exact absurd (hx.symm.trans hu) (xV_ne_uP M j)

end Member

end

end DraismaVargas.Count.MarkedCount.Lollipops
