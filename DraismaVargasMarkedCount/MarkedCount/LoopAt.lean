module

public import DraismaVargasCount.PassOnceLollipopWitness
public import DraismaVargasCount.PendantFibre

@[expose] public section

/-!
# The lollipop at a core loop

A **lollipop** of a core `H` is a loop slot `ℓ` (`H.tail ℓ = H.head ℓ`) together with the slot
through which it hangs off the rest of `H`. The public lollipop package (`LollipopLeafRow`,
`LollipopDivalent`, `LollipopBridgeFibreWitness`, `PassOnceLollipopWitness`) describes a member
`M` over `H` near any core loop; this module assembles it into the shape the marked counts use,
at the lollipops of `attachLollipops` (module `RestrictLollipop`) and at the bulbs of a
caterpillar tail (module `MarkedCountGeneral.Rigidity`).

**Generic facts** (namespace `Lollipops`): three columns with a vanishing combination kill the
determinant (`det_eq_zero_of_columns`); the column of a target edge with a single survivor
(`matrix_column_of_unique`); and Part I's column-dependence argument (Draisma--Vargas Part I,
arXiv:1909.12924, `lemma-loop-bridge`), **an end of a lone survivor is not interior to a stable
row** (`nonDanglingValency_ne_two_of_unique`). Let `Y` be an end of the lone survivor `E`, over
`x`, and suppose `Y` has surviving valency two, with second survivor `E₂` over `s ≠ φ(E)`. The
column of `φ(E)` is supported on the row of `E`.

* `x` is not a leaf: `E₂` lies over an edge at `x` other than `φ(E)`.
* If `x` is divalent, every survivor over `s` is `E₂`: a block over `x` other than `Y` has no
  survivor over `φ(E)`, so all its survivors lie over `s`, and then its local ramification is at
  least its local degree `≥ 2`, above the change budget `1`. So the column of `s` is supported on
  the same row.
* If `x` is trivalent, `PassOnceLollipop.partner_of_block` matches the survivors over the two
  other edges `s, t` in every row but that one, so `col s - col t` is supported on it too.

Either way three columns are dependent, against `det A_φ ≠ 0`. Also: block counts of partitions
with one pair or no pair (`card_blocks_of_pair`, `card_blocks_of_discrete`).

**The lollipop at a loop slot `ℓ`** (namespace `LoopAt`), at the core vertex `A := H.tail ℓ`:

* `loopV M hℓ` (`w`, the branch vertex of `A`), `bridgeE M hℓ` (the bridge occurrence, index `2`),
  `farEnd M hℓ` (its other end, a branch vertex: `nonDanglingValency_farEnd`);
* `uP = φ(w)` (divalent), `vC` (the loop leaf), `tb = φ(bridgeE)`, `tl` (the leaf edge), with
  `incidentEdges_uP = {tb, tl}`, `incidentEdges_vC = {tl}`;
* the fibre clauses (`eq_bridgeE`, `nonDanglingValency_over_uP`, `nonDanglingValency_over_vC`,
  `onRow_of_over_tl`), the blocks (`block_tb_eq_block_uP`, `refines_uP_xV`, `refines_vC_uP`)
  and the block counts (`card_blocks_uP`, `card_blocks_vC`, `card_blocks_tb`, `card_blocks_tl`);
* the bridge row is the single edge `bridgeE` (`eq_bridgeE_of_stablePath_eq`), and it is a slot
  of `H` at `A` other than `ℓ` (`ident_row_bridgePath_ne`, `coreIncidence_bridgePath_loopVertex`).
-/

namespace DraismaVargas.Count.MarkedCount.Lollipops

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource

noncomputable section

/-! ## Generic facts: columns -/

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

/-! ## Generic facts: the far end of a lone survivor -/

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

/-! ## Generic facts: sheet partitions -/

theorem eq_of_blockCard_eq_one {d : ℕ} {P : SheetPartition d} {i a b : Fin d}
    (h : P.blockCard i = 1) (ha : P.Rel i a) (hb : P.Rel i b) : a = b := by
  have hBlock := P.block_eq_singleton_of_blockCard_eq_one i h
  have ha' : a ∈ P.block i := (P.mem_block_iff i a).mpr ha
  have hb' : b ∈ P.block i := (P.mem_block_iff i b).mpr hb
  rw [hBlock, Finset.mem_singleton] at ha' hb'
  rw [ha', hb']

theorem rel_sourceEndpoint {d : ℕ} {T : CFGraph} (D : GluingDatum T d) (v : T.V) (a : Fin d) :
    (D.vertexPartition v).Rel (D.sourceEndpoint v a).1.2 a :=
  (D.vertexPartition v).rel_repr_left a

theorem card_blocks_of_pair {d : ℕ} (P : SheetPartition d) (hd : 0 < d) (b₀ : P.Blocks)
    (h2 : P.blockCard b₀.1 = 2) (h1 : ∀ b : P.Blocks, b ≠ b₀ → P.blockCard b.1 = 1) :
    Fintype.card P.Blocks + 1 = d := by
  classical
  have hSum := SheetPartition.sum_blockCard_blocks_eq_degree P hd
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b₀), h2,
    Finset.sum_congr rfl fun b hb ↦ by rw [h1 b (Finset.mem_erase.mp hb).1]] at hSum
  simp only [Nat.cast_one, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_erase_of_mem (Finset.mem_univ b₀), Finset.card_univ] at hSum
  have hPos : 0 < Fintype.card P.Blocks := Fintype.card_pos_iff.mpr ⟨b₀⟩
  push_cast [Nat.cast_sub hPos] at hSum
  omega

theorem card_blocks_of_discrete {d : ℕ} (P : SheetPartition d) (hd : 0 < d)
    (h1 : ∀ b : P.Blocks, P.blockCard b.1 = 1) : Fintype.card P.Blocks = d := by
  classical
  have hSum := SheetPartition.sum_blockCard_blocks_eq_degree P hd
  simp only [h1, Nat.cast_one, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]
    at hSum
  exact_mod_cast hSum

end

end DraismaVargas.Count.MarkedCount.Lollipops

namespace DraismaVargas.Count.MarkedCount.LoopAt

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.RowWalk (OnRow)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.MarkedCount.Lollipops (nonDanglingValency_ne_two_of_unique
  eq_of_blockCard_eq_one rel_sourceEndpoint card_blocks_of_pair card_blocks_of_discrete)
open scoped DraismaVargas.Infrastructure.GluingContraction

noncomputable section

variable {N P degree : ℕ} {H : Core N P} {y : Fin P → ℚ} (M : FibreMember H y degree)
  {ℓ : Fin P} (hℓ : H.tail ℓ = H.head ℓ)

/-! ## 1.  The source vertex and the bridge -/

/-- `w`, the branch vertex of the loop vertex. -/
def loopV : M.data.SourceVertex := LollipopDivalent.loopBranch M hℓ

theorem three_le_loopV : 3 ≤ nonDanglingValency M.data (loopV M hℓ) :=
  LollipopDivalent.three_le_loopBranch M hℓ

theorem nonDanglingValency_loopV : nonDanglingValency M.data (loopV M hℓ) = 3 :=
  le_antisymm (M.fullDim.trivalent _) (three_le_loopV M hℓ)

theorem ident_loopV : M.ident.vertex ⟨loopV M hℓ, three_le_loopV M hℓ⟩ = H.tail ℓ := by
  change M.ident.vertex (M.ident.vertex.symm _) = _
  rw [Equiv.apply_symm_apply]

/-- `e_b`, the bridge occurrence at `w`. -/
def bridgeE : M.data.SourceEdge := (LollipopBridgeFibreWitness.exists_bridge_loopBranch M hℓ).choose

theorem bridgeE_spec :
    ¬ IsDangling M.data (bridgeE M hℓ) ∧ Incident M.data (bridgeE M hℓ) (loopV M hℓ) ∧
      ¬ OnRow M.data (LollipopBridgeFibreWitness.loopRow M ℓ) (bridgeE M hℓ) ∧
      M.data.sourceEdgeIndex (bridgeE M hℓ) = 2 :=
  (LollipopBridgeFibreWitness.exists_bridge_loopBranch M hℓ).choose_spec

theorem bridgeE_survives : ¬ IsDangling M.data (bridgeE M hℓ) := (bridgeE_spec M hℓ).1

theorem bridgeE_incident_loopV : Incident M.data (bridgeE M hℓ) (loopV M hℓ) :=
  (bridgeE_spec M hℓ).2.1

theorem bridgeE_index : M.data.sourceEdgeIndex (bridgeE M hℓ) = 2 := (bridgeE_spec M hℓ).2.2.2

/-! ## 2.  The target vertices and edges of the lollipop -/

/-- `φ(w)`. -/
def uP : M.target.V := (loopV M hℓ).1.1

/-- The leaf of the loop row. -/
def vC : M.target.V := LollipopLeafRow.loopLeaf M hℓ

theorem vC_isLeaf : Count.IsLeafVertex M.target (vC M hℓ) :=
  LollipopLeafRow.loopLeaf_isLeafVertex M hℓ

/-- The leaf edge at `vC`. -/
def tl : M.target.edges := Count.leafEdge (vC_isLeaf M hℓ)

/-- `φ(e_b)`. -/
def tb : M.target.edges := (bridgeE M hℓ).1.1

theorem uP_divalent : (GluingDatum.incidentEdges (uP M hℓ)).card = 2 :=
  LollipopDivalent.loopImage_divalent M hℓ

theorem tl_mem_uP : tl M hℓ ∈ GluingDatum.incidentEdges (uP M hℓ) :=
  PassOnceLollipopWitness.loopLeafAdjacent M hℓ

theorem tl_mem_vC : tl M hℓ ∈ GluingDatum.incidentEdges (vC M hℓ) :=
  Count.leafEdge_mem (vC_isLeaf M hℓ)

theorem tb_mem_uP : tb M hℓ ∈ GluingDatum.incidentEdges (uP M hℓ) :=
  ((incident_iff_target_mem_and_rel M.data _ _).mp (bridgeE_incident_loopV M hℓ)).1

variable (ℓ) in
/-- The loop row, as a stable path. -/
def loopRow : StablePath M.data := M.ident.row.symm ℓ

/-- A source vertex with no survivor is a single sheet. -/
theorem blockCard_eq_one_of_nonDanglingValency_zero {X : M.data.SourceVertex}
    (h0 : nonDanglingValency M.data X = 0) :
    (M.data.vertexPartition X.1.1).blockCard X.1.2 = 1 :=
  (PendantFibre.degree_one_of_nonDanglingValency_zero M.fullDim X h0).1

/-- **Every survivor over the leaf edge lies on the loop row.** -/
theorem onRow_of_over_tl {E : M.data.SourceEdge} (hE : ¬ IsDangling M.data E)
    (hT : E.1.1 = tl M hℓ) :
    NonDanglingEdge.stablePath (⟨E, hE⟩ : NonDanglingEdge M.data) = loopRow M ℓ := by
  have hMem : E ∈ LeafFibre.leafSurvivors (data := M.data) (vC_isLeaf M hℓ) :=
    (LeafFibre.mem_leafSurvivors _).mpr ⟨hE, hT⟩
  have h1 := LeafFibre.row_eq_leafRow M.fullDim (vC_isLeaf M hℓ) hMem hE
  have h2 := LollipopLeafRow.leafRow_loopLeaf M hℓ
  exact M.fullDim.labelling.row.injective (h1.trans h2)

theorem tb_ne_tl : tb M hℓ ≠ tl M hℓ := by
  intro h
  apply (bridgeE_spec M hℓ).2.2.1
  exact ⟨bridgeE_survives M hℓ, onRow_of_over_tl M hℓ (bridgeE_survives M hℓ) h⟩

theorem incidentEdges_uP : GluingDatum.incidentEdges (uP M hℓ) = {tb M hℓ, tl M hℓ} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact tb_mem_uP M hℓ
    · exact tl_mem_uP M hℓ
  · rw [uP_divalent, Finset.card_pair (tb_ne_tl M hℓ)]

theorem incidentEdges_vC : GluingDatum.incidentEdges (vC M hℓ) = {tl M hℓ} :=
  Count.incidentEdges_eq_leafEdge (vC_isLeaf M hℓ)

/-! ## 3.  The fibre clauses -/

/-- **`e_b` is the only survivor over `φ(e_b)`.** -/
theorem eq_bridgeE {E : M.data.SourceEdge} (hE : ¬ IsDangling M.data E) (hT : E.1.1 = tb M hℓ) :
    E = bridgeE M hℓ :=
  PassOnceLollipopWitness.eq_bridge_of_surviving_loopBranch M hℓ
    (bridgeE_survives M hℓ) (bridgeE_incident_loopV M hℓ) (bridgeE_spec M hℓ).2.2.1 hE hT

/-- **`w` is the only non-dangling vertex over `φ(w)`.** -/
theorem nonDanglingValency_over_uP {X : M.data.SourceVertex} (hX : X.1.1 = uP M hℓ)
    (hNe : X ≠ loopV M hℓ) : nonDanglingValency M.data X = 0 :=
  PassOnceLollipopWitness.nonDanglingValency_eq_zero_of_ne_loopBranch M hℓ hX hNe

/-- **Over the leaf `vC` the only non-dangling vertex is the core vertex, of valency two.** -/
theorem nonDanglingValency_over_vC {X : M.data.SourceVertex} (hX : X.1.1 = vC M hℓ) :
    nonDanglingValency M.data X = 0 ∨ nonDanglingValency M.data X = 2 := by
  have hLeaf : Count.IsLeafVertex M.target X.1.1 := hX ▸ vC_isLeaf M hℓ
  by_cases h0 : nonDanglingValency M.data X = 0
  · exact Or.inl h0
  · right
    have hC := LollipopDivalentWitness.eq_coreVertex_of_surviving M.fullDim
      (Nat.pos_of_ne_zero h0) hLeaf
    rw [hC]
    exact LeafFibre.nonDanglingValency_coreVertex M.fullDim hLeaf

/-! ## 4.  The bridge row and the far end -/

/-- The stable path of the bridge. -/
def bridgePath : StablePath M.data :=
  NonDanglingEdge.stablePath (⟨bridgeE M hℓ, bridgeE_survives M hℓ⟩ : NonDanglingEdge M.data)

/-- The far end of the bridge, the end other than `w`. -/
def farEnd : M.data.SourceVertex :=
  if (M.data.sourceEnds (bridgeE M hℓ)).1 = loopV M hℓ then (M.data.sourceEnds (bridgeE M hℓ)).2
  else (M.data.sourceEnds (bridgeE M hℓ)).1

theorem farEnd_incident : Incident M.data (bridgeE M hℓ) (farEnd M hℓ) := by
  unfold farEnd
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem farEnd_ne_loopV : farEnd M hℓ ≠ loopV M hℓ := by
  unfold farEnd
  split_ifs with h
  · intro h'
    exact M.data.sourceEnds_ne _ (h.trans h'.symm)
  · exact h

/-- **The far end of the bridge is a branch vertex** (the column-dependence argument of
`Lollipops.nonDanglingValency_ne_two_of_unique`). -/
theorem nonDanglingValency_farEnd : nonDanglingValency M.data (farEnd M hℓ) = 3 := by
  have hne2 := nonDanglingValency_ne_two_of_unique M.fullDim (bridgeE_survives M hℓ)
    (fun F hF hFt ↦ eq_bridgeE M hℓ hF hFt) (farEnd_incident M hℓ)
  have hpos := LollipopBridgeFibre.nonDanglingValency_pos_of_survivor (bridgeE_survives M hℓ)
    (farEnd_incident M hℓ)
  have hne1 := NonDanglingValency.nonDanglingValency_ne_one M.data M.fullDim.connected
    (farEnd M hℓ)
  have hle := M.fullDim.trivalent (farEnd M hℓ)
  omega

theorem three_le_farEnd : 3 ≤ nonDanglingValency M.data (farEnd M hℓ) :=
  (nonDanglingValency_farEnd M hℓ).ge

/-- The two ends of the bridge: `w` and the far end. -/
theorem incident_bridgeE_iff (X : M.data.SourceVertex) :
    Incident M.data (bridgeE M hℓ) X ↔ X = loopV M hℓ ∨ X = farEnd M hℓ := by
  constructor
  · intro hX
    have hw := bridgeE_incident_loopV M hℓ
    have hf := farEnd_incident M hℓ
    rcases hX with h | h <;> rcases hw with h1 | h1 <;> rcases hf with h2 | h2 <;>
      first
      | exact Or.inl (h.symm.trans h1)
      | exact Or.inr (h.symm.trans h2)
      | exact absurd (h1.symm.trans h2) (farEnd_ne_loopV M hℓ).symm
  · rintro (rfl | rfl)
    · exact bridgeE_incident_loopV M hℓ
    · exact farEnd_incident M hℓ

/-! ### A survivor whose ends are branch vertices is a whole row -/

section Lone

variable {target : CFGraph} {d : ℕ} {data : GluingDatum target d}

/-- **A survivor whose two ends have surviving valency other than two is consecutive to
nothing**, so its stable path contains it alone. -/
theorem eq_of_stablePath_eq_of_ends {E F : NonDanglingEdge data}
    (hEnds : ∀ X, Incident data E.1 X → nonDanglingValency data X ≠ 2)
    (h : F.stablePath = E.stablePath) : F = E := by
  have hNo : ∀ G, ¬ Consecutive data E G ∧ ¬ Consecutive data G E := by
    intro G
    constructor
    · rintro ⟨-, X, hE, -, h2⟩; exact hEnds X hE h2
    · rintro ⟨-, X, -, hE, h2⟩; exact hEnds X hE h2
  have key : ∀ A B, Relation.EqvGen (Consecutive data) A B → (A = E ↔ B = E) := by
    intro A B hAB
    induction hAB with
    | rel A B hR =>
      constructor
      · rintro rfl; exact absurd hR (hNo B).1
      · rintro rfl; exact absurd hR (hNo A).2
    | refl => exact Iff.rfl
    | symm A B _ ih => exact ih.symm
    | trans A B C _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (key F E ((stablePath_eq_iff F E).mp h)).mpr rfl

end Lone

theorem bridgeE_ends_ne_two (X : M.data.SourceVertex) (hX : Incident M.data (bridgeE M hℓ) X) :
    nonDanglingValency M.data X ≠ 2 := by
  rcases (incident_bridgeE_iff M hℓ X).mp hX with rfl | rfl
  · rw [nonDanglingValency_loopV]; omega
  · rw [nonDanglingValency_farEnd]; omega

/-- **The bridge row is the single edge `e_b`.** -/
theorem eq_bridgeE_of_stablePath_eq (F : NonDanglingEdge M.data)
    (h : F.stablePath = bridgePath M hℓ) : F = ⟨bridgeE M hℓ, bridgeE_survives M hℓ⟩ :=
  eq_of_stablePath_eq_of_ends (bridgeE_ends_ne_two M hℓ) h

theorem incidenceCount_pos_of_incident {X : M.data.SourceVertex} {E : M.data.SourceEdge}
    (hE : ¬ IsDangling M.data E) (hX : Incident M.data E X) :
    0 < StablePathCount.incidenceCount M.data X
      (NonDanglingEdge.stablePath (⟨E, hE⟩ : NonDanglingEdge M.data)) :=
  (StablePathCount.incidenceCount_pos_iff _ _ _).mpr ⟨⟨E, hE⟩, hX, rfl⟩

/-- A branch vertex on the row of a survivor sits at an end of the corresponding slot. -/
theorem coreIncidence_pos_of_incident (X : StableGraphIncidence.BranchVertex M.data)
    {E : M.data.SourceEdge} (hE : ¬ IsDangling M.data E) (hX : Incident M.data E X.1) :
    0 < Count.coreIncidence H (M.ident.vertex X)
      (M.ident.row (NonDanglingEdge.stablePath (⟨E, hE⟩ : NonDanglingEdge M.data))) := by
  have h := M.ident.incidence X
    (M.ident.row (NonDanglingEdge.stablePath (⟨E, hE⟩ : NonDanglingEdge M.data)))
  rw [Equiv.symm_apply_apply] at h
  rw [← h]
  exact incidenceCount_pos_of_incident M hE hX

/-- **The bridge row is not the loop row.** -/
theorem ident_row_bridgePath_ne : M.ident.row (bridgePath M hℓ) ≠ ℓ := by
  intro h
  apply (bridgeE_spec M hℓ).2.2.1
  refine ⟨bridgeE_survives M hℓ, ?_⟩
  exact (Equiv.eq_symm_apply _).mpr h

/-- **The bridge row is a slot at the loop vertex.** -/
theorem coreIncidence_bridgePath_loopVertex :
    0 < Count.coreIncidence H (H.tail ℓ) (M.ident.row (bridgePath M hℓ)) := by
  have h := coreIncidence_pos_of_incident M ⟨loopV M hℓ, three_le_loopV M hℓ⟩
    (bridgeE_survives M hℓ) (bridgeE_incident_loopV M hℓ)
  rwa [ident_loopV] at h

/-- **The bridge row is a slot at the vertex of the far end.** -/
theorem coreIncidence_bridgePath_farEnd :
    0 < Count.coreIncidence H (M.ident.vertex ⟨farEnd M hℓ, three_le_farEnd M hℓ⟩)
      (M.ident.row (bridgePath M hℓ)) :=
  coreIncidence_pos_of_incident M ⟨farEnd M hℓ, three_le_farEnd M hℓ⟩
    (bridgeE_survives M hℓ) (farEnd_incident M hℓ)

theorem ident_farEnd_ne_loopVertex :
    M.ident.vertex ⟨farEnd M hℓ, three_le_farEnd M hℓ⟩ ≠ H.tail ℓ := by
  intro h
  apply farEnd_ne_loopV M hℓ
  have : (⟨farEnd M hℓ, three_le_farEnd M hℓ⟩ : StableGraphIncidence.BranchVertex M.data) =
      ⟨loopV M hℓ, three_le_loopV M hℓ⟩ := by
    apply M.ident.vertex.injective
    rw [h, ident_loopV]
  exact congrArg Subtype.val this

/-! ## 5.  The far end's image -/

/-- `φ(far end)`. -/
def xV : M.target.V := (farEnd M hℓ).1.1

theorem tb_mem_xV : tb M hℓ ∈ GluingDatum.incidentEdges (xV M hℓ) :=
  ((incident_iff_target_mem_and_rel M.data _ _).mp (farEnd_incident M hℓ)).1

theorem xV_ne_uP : xV M hℓ ≠ uP M hℓ := by
  intro h
  exact farEnd_ne_loopV M hℓ (LollipopBridgeFibre.eq_of_incident_of_target_eq h
    (farEnd_incident M hℓ) (bridgeE_incident_loopV M hℓ))

/-- The ends of `φ(e_b)` are `φ(far end)` and `φ(w)`. -/
theorem tb_ends :
    ((tb M hℓ : M.target.V × M.target.V).1 = xV M hℓ ∧
        (tb M hℓ : M.target.V × M.target.V).2 = uP M hℓ) ∨
      ((tb M hℓ : M.target.V × M.target.V).1 = uP M hℓ ∧
        (tb M hℓ : M.target.V × M.target.V).2 = xV M hℓ) := by
  have hx := Count.fst_eq_or_snd_eq_of_mem_incidentEdges (tb_mem_xV M hℓ)
  have hu := Count.fst_eq_or_snd_eq_of_mem_incidentEdges (tb_mem_uP M hℓ)
  have hne := GluingContraction.fst_ne_snd (tb M hℓ)
  rcases hx with hx | hx <;> rcases hu with hu | hu
  · exact absurd (hx.symm.trans hu) (xV_ne_uP M hℓ)
  · exact Or.inl ⟨hx, hu⟩
  · exact Or.inr ⟨hu, hx⟩
  · exact absurd (hx.symm.trans hu) (xV_ne_uP M hℓ)

theorem uP_ne_vC : uP M hℓ ≠ vC M hℓ := by
  intro h
  have h1 := uP_divalent M hℓ
  have h2 : (GluingDatum.incidentEdges (vC M hℓ)).card = 1 := vC_isLeaf M hℓ
  rw [h] at h1
  omega

theorem xV_ne_vC : xV M hℓ ≠ vC M hℓ := by
  intro h
  have := nonDanglingValency_over_vC M hℓ (X := farEnd M hℓ) h
  have := nonDanglingValency_farEnd M hℓ
  omega

/-- The ends of the leaf edge are `uP` and `vC`. -/
theorem tl_ends :
    ((tl M hℓ : M.target.V × M.target.V).1 = uP M hℓ ∧
        (tl M hℓ : M.target.V × M.target.V).2 = vC M hℓ) ∨
      ((tl M hℓ : M.target.V × M.target.V).1 = vC M hℓ ∧
        (tl M hℓ : M.target.V × M.target.V).2 = uP M hℓ) := by
  have hx := Count.fst_eq_or_snd_eq_of_mem_incidentEdges (tl_mem_uP M hℓ)
  have hu := Count.fst_eq_or_snd_eq_of_mem_incidentEdges (tl_mem_vC M hℓ)
  rcases hx with hx | hx <;> rcases hu with hu | hu
  · exact absurd (hx.symm.trans hu) (uP_ne_vC M hℓ)
  · exact Or.inl ⟨hx, hu⟩
  · exact Or.inr ⟨hu, hx⟩
  · exact absurd (hx.symm.trans hu) (uP_ne_vC M hℓ)

/-! ## 6.  Blocks over the lollipop -/

/-- **The block of `w` over `φ(w)` is the block of `e_b`.** -/
theorem block_tb_eq_block_uP :
    (M.data.edgePartition (tb M hℓ)).block (bridgeE M hℓ).1.2 =
      (M.data.vertexPartition (uP M hℓ)).block (bridgeE M hℓ).1.2 := by
  have hRef := StableLocalProperties.refines_of_mem_incidentEdges M.data (tb_mem_uP M hℓ)
  have hRelW : (M.data.vertexPartition (uP M hℓ)).Rel (loopV M hℓ).1.2 (bridgeE M hℓ).1.2 :=
    ((incident_iff_target_mem_and_rel M.data _ _).mp (bridgeE_incident_loopV M hℓ)).2
  apply Finset.eq_of_subset_of_card_le
  · intro σ hσ
    rw [SheetPartition.mem_block_iff] at hσ ⊢
    exact hRef.rel hσ
  · have h1 : ((M.data.edgePartition (tb M hℓ)).block (bridgeE M hℓ).1.2).card = 2 :=
      bridgeE_index M hℓ
    have h2 : ((M.data.vertexPartition (uP M hℓ)).block (bridgeE M hℓ).1.2).card = 2 := by
      rw [← SheetPartition.block_eq_of_rel _ hRelW]
      exact LollipopBridgeFibreWitness.blockCard_loopBranch M hℓ
    omega

theorem blockCard_loopV :
    (M.data.vertexPartition (loopV M hℓ).1.1).blockCard (loopV M hℓ).1.2 = 2 :=
  LollipopBridgeFibreWitness.blockCard_loopBranch M hℓ

/-- The partition at `φ(w)` refines the one at `φ(far end)`. -/
theorem refines_uP_xV :
    (M.data.vertexPartition (uP M hℓ)).Refines (M.data.vertexPartition (xV M hℓ)) := by
  intro a b hab
  set X := M.data.sourceEndpoint (uP M hℓ) a
  by_cases hX : X = loopV M hℓ
  · have hRelW : (M.data.vertexPartition (uP M hℓ)).Rel (loopV M hℓ).1.2 (bridgeE M hℓ).1.2 :=
      ((incident_iff_target_mem_and_rel M.data _ _).mp (bridgeE_incident_loopV M hℓ)).2
    have hXa : (M.data.vertexPartition (uP M hℓ)).Rel X.1.2 a :=
      rel_sourceEndpoint M.data (uP M hℓ) a
    rw [hX] at hXa
    have hσa : (M.data.vertexPartition (uP M hℓ)).Rel (bridgeE M hℓ).1.2 a :=
      (SheetPartition.rel_iff _ _ _).mpr (hRelW.symm.trans hXa)
    have hσb : (M.data.vertexPartition (uP M hℓ)).Rel (bridgeE M hℓ).1.2 b :=
      (SheetPartition.rel_iff _ _ _).mpr (hσa.trans hab)
    have ha := (SheetPartition.mem_block_iff _ _ _).mpr hσa
    have hb := (SheetPartition.mem_block_iff _ _ _).mpr hσb
    rw [← block_tb_eq_block_uP, SheetPartition.mem_block_iff] at ha hb
    have hRefX := StableLocalProperties.refines_of_mem_incidentEdges M.data (tb_mem_xV M hℓ)
    exact hRefX.rel ((SheetPartition.rel_iff _ _ _).mpr (ha.symm.trans hb))
  · have h0 := nonDanglingValency_over_uP M hℓ (X := X) rfl hX
    have h1 := blockCard_eq_one_of_nonDanglingValency_zero M h0
    have hXa := rel_sourceEndpoint M.data (uP M hℓ) a
    have hXb : (M.data.vertexPartition (uP M hℓ)).Rel X.1.2 b :=
      (SheetPartition.rel_iff _ _ _).mpr (hXa.trans hab)
    have := eq_of_blockCard_eq_one h1 hXa hXb
    subst this
    exact (SheetPartition.rel_iff _ _ _).mpr rfl

/-- The partition at the leaf refines the one at `φ(w)`. -/
theorem refines_vC_uP :
    (M.data.vertexPartition (vC M hℓ)).Refines (M.data.vertexPartition (uP M hℓ)) := by
  classical
  intro a b hab
  set X := M.data.sourceEndpoint (vC M hℓ) a
  have hXa := rel_sourceEndpoint M.data (vC M hℓ) a
  have hXb : (M.data.vertexPartition (vC M hℓ)).Rel X.1.2 b :=
    (SheetPartition.rel_iff _ _ _).mpr (hXa.trans hab)
  rcases nonDanglingValency_over_vC M hℓ (X := X) rfl with h0 | h2
  · have h1 := blockCard_eq_one_of_nonDanglingValency_zero M h0
    have := eq_of_blockCard_eq_one h1 hXa hXb
    subst this
    exact (SheetPartition.rel_iff _ _ _).mpr rfl
  · have hLeaf := vC_isLeaf M hℓ
    have hC : X = LeafFibre.coreVertex M.fullDim hLeaf :=
      LollipopDivalentWitness.eq_coreVertex_of_surviving M.fullDim (by omega) hLeaf
    obtain ⟨e₁, e₂, hne, hpair⟩ := Finset.card_eq_two.mp
      (LeafFibre.leafSurvivors_card M.fullDim hLeaf)
    have hmem₁ : e₁ ∈ LeafFibre.leafSurvivors (data := M.data) hLeaf := by rw [hpair]; simp
    have hmem₂ : e₂ ∈ LeafFibre.leafSurvivors (data := M.data) hLeaf := by rw [hpair]; simp
    have hW : ∀ e ∈ LeafFibre.leafSurvivors (data := M.data) hLeaf,
        (M.data.vertexPartition (uP M hℓ)).Rel (loopV M hℓ).1.2 e.1.2 := by
      intro e he
      obtain ⟨heS, heT⟩ := (LeafFibre.mem_leafSurvivors hLeaf).mp he
      have hInc : Incident M.data e (M.data.sourceEndpoint (uP M hℓ) e.1.2) := by
        have h := incident_sourceEdge_sourceEndpoint M.data (uP M hℓ) (tl M hℓ)
          (tl_mem_uP M hℓ) e.1.2
        rwa [show M.data.sourceEdge (tl M hℓ) e.1.2 = e by
          rw [← show e.1.1 = tl M hℓ from heT]; exact GluingDatum.sourceEdge_self M.data e] at h
      have hEq : M.data.sourceEndpoint (uP M hℓ) e.1.2 = loopV M hℓ := by
        by_contra hne'
        have := nonDanglingValency_over_uP M hℓ
          (X := M.data.sourceEndpoint (uP M hℓ) e.1.2) rfl hne'
        have := LollipopBridgeFibre.nonDanglingValency_pos_of_survivor heS hInc
        omega
      rw [← hEq]
      exact ((incident_iff_target_mem_and_rel M.data _ _).mp hInc).2
    have hC₁ := LeafFibre.incident_coreVertex_of_mem_leafSurvivors M.fullDim hLeaf hmem₁
    have hC₂ := LeafFibre.incident_coreVertex_of_mem_leafSurvivors M.fullDim hLeaf hmem₂
    rw [← hC] at hC₁ hC₂
    have hR₁ := ((incident_iff_target_mem_and_rel M.data _ _).mp hC₁).2
    have hR₂ := ((incident_iff_target_mem_and_rel M.data _ _).mp hC₂).2
    have hσ : e₁.1.2 ≠ e₂.1.2 := by
      intro h
      apply hne
      have hT₁ := ((LeafFibre.mem_leafSurvivors hLeaf).mp hmem₁).2
      have hT₂ := ((LeafFibre.mem_leafSurvivors hLeaf).mp hmem₂).2
      exact Subtype.ext (Prod.ext (hT₁.trans hT₂.symm) h)
    have hCard : (M.data.vertexPartition (vC M hℓ)).blockCard X.1.2 = 2 := by
      rw [hC]
      exact LeafFibre.blockCard_coreBlock M.fullDim hLeaf
    have hBlock : (M.data.vertexPartition (vC M hℓ)).block X.1.2 = {e₁.1.2, e₂.1.2} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro σ hσ'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hσ'
        rw [SheetPartition.mem_block_iff]
        rcases hσ' with rfl | rfl
        · exact hR₁
        · exact hR₂
      · rw [Finset.card_pair hσ]
        exact hCard.le
    have ha : a ∈ ({e₁.1.2, e₂.1.2} : Finset _) := by
      rw [← hBlock, SheetPartition.mem_block_iff]; exact hXa
    have hb : b ∈ ({e₁.1.2, e₂.1.2} : Finset _) := by
      rw [← hBlock, SheetPartition.mem_block_iff]; exact hXb
    have hW₁ := hW e₁ hmem₁
    have hW₂ := hW e₂ hmem₂
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      first
      | exact (SheetPartition.rel_iff _ _ _).mpr rfl
      | exact (SheetPartition.rel_iff _ _ _).mpr (hW₁.symm.trans hW₂)
      | exact (SheetPartition.rel_iff _ _ _).mpr (hW₂.symm.trans hW₁)

/-! ## 7.  Block counts over the lollipop -/

theorem card_blocks_uP :
    Fintype.card (M.data.vertexPartition (uP M hℓ)).Blocks + 1 = degree := by
  refine card_blocks_of_pair _ M.data.degree_pos ⟨(loopV M hℓ).1.2, (loopV M hℓ).2⟩
    (LollipopBridgeFibreWitness.blockCard_loopBranch M hℓ) fun b hb ↦ ?_
  refine blockCard_eq_one_of_nonDanglingValency_zero M (X := ⟨(uP M hℓ, b.1), b.2⟩) ?_
  refine nonDanglingValency_over_uP M hℓ rfl fun h ↦ hb ?_
  exact Subtype.ext (congrArg (fun X : M.data.SourceVertex ↦ X.1.2) h)

theorem card_blocks_vC :
    Fintype.card (M.data.vertexPartition (vC M hℓ)).Blocks + 1 = degree :=
  LeafFibre.card_blocks_leaf M.fullDim (vC_isLeaf M hℓ)

theorem card_blocks_tb :
    Fintype.card (M.data.edgePartition (tb M hℓ)).Blocks + 1 = degree := by
  refine card_blocks_of_pair _ M.data.degree_pos ⟨(bridgeE M hℓ).1.2, (bridgeE M hℓ).2⟩
    (bridgeE_index M hℓ) fun b hb ↦ ?_
  set E : M.data.SourceEdge := ⟨(tb M hℓ, b.1), b.2⟩
  have hD : IsDangling M.data E := by
    by_contra hS
    apply hb
    have := eq_bridgeE M hℓ hS rfl
    exact Subtype.ext (congrArg (fun F : M.data.SourceEdge ↦ F.1.2) this)
  exact M.fullDim.danglingEdgeNoGlue E hD

theorem card_blocks_tl :
    Fintype.card (M.data.edgePartition (tl M hℓ)).Blocks = degree :=
  card_blocks_of_discrete _ M.data.degree_pos fun b ↦
    LeafFibre.sourceEdgeIndex_eq_one_above_leaf M.fullDim (vC_isLeaf M hℓ)
      (edge := ⟨(tl M hℓ, b.1), b.2⟩) rfl

end

end DraismaVargas.Count.MarkedCount.LoopAt
