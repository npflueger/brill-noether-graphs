module

public import DraismaVargasMarkedCount.MarkedCount.Lollipop
public import DraismaVargasMarkedCount.MarkedCount.RegrowMatrix
public import DraismaVargasMarkedCount.MarkedCount.RegrowIso

@[expose] public section

/-!
# Regrowth

Regrowth is the inverse of restriction (module `Restriction`): it grows a lollipop back at every
mark of a marked frame, as an operation on gluing data, and it does not depend on the choice of
the 2-subset `P` below.

**Regrowth** attaches to a marked frame, at every mark `u_G` over `x = φ(u_G)` with block `S`,
`|S| = m(u_G) ≥ 2`, a path `x — u' — v_C` of two new target edges `t_b, t_l`: over `t_b` and at
`u'`, `v_C` the partition `{P} ∪ singletons` for a 2-subset `P ⊆ S`, over `t_l` the discrete
partition. Per mark this is the public tripod's `Gluing.leafTarget` twice with the first leaf edge
carrying `SheetOps.pair`; for `k` marks it is built in one step (`Regrow.regrowTarget`, vertices
`T.V ⊕ (Fin k ⊕ Fin k)`), so that no recursion on `k` is needed.

## Contents

* `regrowFrame`: the construction, for every number `k` of marks;
* `regrowFrame_respects`: regrowth descends to classes, including the independence of `P`.

The construction is generic, in namespace `Regrow`:

* `RegrowTarget`: the target `regrowTarget T x`, its occurrence dictionary `occEquiv` and names
  `oldV`, `midV`, `tipV`, `oldE`, `bridgeE`, `leafE`; connectedness, genus, edge count;
* `RegrowDatum`: `Branching D k` (marks and second sheets), `regrowDatum β`, the source
  dictionary (`oldSV`, `midSV`, `tipSV`, `oldSE`, `bridgeSE`, `leafSE`; the lollipop `wSV`, `cSV`,
  `ebSE`, `e₁SE`, `e₂SE`), the incidence table, Riemann--Hurwitz, connectedness, genus `+ k`;
* `RegrowDangling`: the dangling dictionary and the surviving valencies;
* `RegrowStable`: stable paths (`stablePathEquiv`), branch vertices (`branchVertexEquiv`),
  incidence counts, trivalence, path ends;
* `RegrowMatrix`: the length matrix, block by block;
* `RegrowIso`: isomorphisms of data extend over the branches (`regrowIso`).

Here they are applied to a marked frame (`Regrow.branching`, `Regrow.fullDim`, `Regrow.ident`).

**Also proved here:** `MarkedFrame.two_le_markIndex`, `m(u_G) ≥ 2` at a ramified mark (the part
regrowth needs of the fact that a ramified mark has index at least two and lies over a leaf or a
divalent vertex), from Riemann--Hurwitz alone.
-/

namespace DraismaVargas.Count.MarkedCount

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.GeometricSegmentWalls (FrameIso)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n}

/-- **A ramified mark has local degree at least two** (what regrowth needs: the block of `u_G`
has a 2-subset `P`).

*Why true.* If `m(u_G) = |S| = 1`, every target edge at `x` has exactly one edge block inside
`S` (`blockCountWithin ≤ blockCard` and refinement), so
`r(u_G) = val x - 2 - 1 · (val x - 2) = 0`, contradicting `κ.ramified`. This uses neither
change-minimality nor nonsingularity. -/
theorem MarkedFrame.two_le_markIndex (κ : MarkedFrame core mark degree) (j : Fin k) :
    2 ≤ (κ.data.vertexPartition (κ.markSource j).1.1).blockCard (κ.markSource j).1.2 := by
  have hr := κ.ramified j
  set v := κ.markSource j
  by_contra hlt
  push Not at hlt
  have hpos := (κ.data.vertexPartition v.1.1).blockCard_pos v.1.2
  have hone : (κ.data.vertexPartition v.1.1).blockCard v.1.2 = 1 := by omega
  have hle : ∀ edge ∈ GluingDatum.incidentEdges v.1.1,
      (κ.data.edgePartition edge).blockCountWithin (κ.data.vertexPartition v.1.1) v.1.2 ≤ 1 := by
    intro edge hIncident
    have hEnds := (Finset.mem_filter.mp hIncident).2
    have hRefines : (κ.data.edgePartition edge).Refines (κ.data.vertexPartition v.1.1) := by
      rcases hEnds with hLeft | hRight
      · simpa [hLeft] using κ.data.refines_left edge
      · simpa [hRight] using κ.data.refines_right edge
    have h := SheetPartition.blockCountWithin_le_blockCard _ _ hRefines ⟨v.1.2, v.2⟩
    rw [← hone]
    exact h
  have hsum : (∑ edge ∈ GluingDatum.incidentEdges v.1.1,
      ((κ.data.edgePartition edge).blockCountWithin (κ.data.vertexPartition v.1.1) v.1.2 : ℤ)) ≤
      ((GluingDatum.incidentEdges v.1.1).card : ℤ) := by
    have h := Finset.sum_le_card_nsmul _ _ 1 hle
    simp only [smul_eq_mul, mul_one] at h
    exact_mod_cast h
  unfold markRamification GluingDatum.localRamification at hr
  dsimp only at hr
  rw [hone] at hr
  push_cast at hr
  linarith

/-! ## The regrown frame

The construction is generic (modules `RegrowTarget`, `RegrowDatum`, `RegrowDangling`,
`RegrowStable`, `RegrowMatrix`, namespace `Regrow`); here it is applied to a marked frame. -/

namespace Regrow

open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)

variable (κ : MarkedFrame core mark degree)

theorem one_lt_blockCard_mark (j : Fin k) :
    1 < (κ.data.vertexPartition (κ.markSource j).1.1).blockCard (κ.markSource j).1.2 :=
  κ.two_le_markIndex j

/-- **The branching of a marked frame**: its marks, and for each a second sheet of its block,
chosen (`two_le_markIndex`). -/
noncomputable abbrev branching : Branching κ.data k where
  mark := κ.markSource
  other j := ((κ.data.vertexPartition (κ.markSource j).1.1).exists_other_of_one_lt_blockCard
    _ (one_lt_blockCard_mark κ j)).choose
  rel j := ((κ.data.vertexPartition (κ.markSource j).1.1).exists_other_of_one_lt_blockCard
    _ (one_lt_blockCard_mark κ j)).choose_spec.1
  ne j := ((κ.data.vertexPartition (κ.markSource j).1.1).exists_other_of_one_lt_blockCard
    _ (one_lt_blockCard_mark κ j)).choose_spec.2

theorem marks_branching : marks (branching κ) = markSet κ.markSource := rfl

theorem connected : κ.data.Connected := κ.fullDim.valid.1

theorem markValency (j : Fin k) : nonDanglingValency κ.data (κ.markSource j) = 2 :=
  κ.fullDim.markValency _ (mem_markSet _ j)

theorem markValency_ne_zero (j : Fin k) :
    nonDanglingValency κ.data ((branching κ).mark j) ≠ 0 := by
  change nonDanglingValency κ.data (κ.markSource j) ≠ 0
  rw [markValency κ j]; omega

/-- The marks of a marked frame are distinct source vertices. -/
theorem markSource_injective (hc : IsMarkedCubic core mark) :
    Function.Injective κ.markSource := by
  intro i j h
  apply hc.injective
  rw [← κ.ident.vertex_mark i, ← κ.ident.vertex_mark j]
  congr 1
  exact Subtype.ext h

/-- The regrown datum of a marked frame. -/
noncomputable abbrev datum : GluingDatum (regrowTarget κ.target (branching κ).x) degree :=
  regrowDatum (branching κ)

theorem valid (hc : IsMarkedCubic core mark) : (datum κ).Valid :=
  ⟨connected_regrowDatum _ (connected κ),
    riemannHurwitz_regrowDatum _ κ.fullDim.valid.2 (markSource_injective κ hc) κ.ramified⟩

/-- The column dictionary: core columns, bridge columns, loop columns. -/
noncomputable def colEquiv :
    Fin p ⊕ (Fin k ⊕ Fin k) ≃ (regrowTarget κ.target (branching κ).x).edges :=
  (Equiv.sumCongr κ.fullDim.labelling.targetEdge (Equiv.refl _)).trans
    ((Equiv.sumComm _ _).trans (occEquiv (branching κ).x))

@[simp] theorem colEquiv_inl (i : Fin p) :
    colEquiv κ (.inl i) = oldE (branching κ).x (κ.fullDim.labelling.targetEdge i) := rfl
@[simp] theorem colEquiv_bridge (j : Fin k) :
    colEquiv κ (.inr (.inl j)) = bridgeE (branching κ).x j := rfl
@[simp] theorem colEquiv_loop (j : Fin k) :
    colEquiv κ (.inr (.inr j)) = leafE (branching κ).x j := rfl

/-- `Fin p ⊕ (Fin k ⊕ Fin k) ≃ Fin (p + (k + k))`: core slots, bridges, loops. -/
def slotEquiv : Fin p ⊕ (Fin k ⊕ Fin k) ≃ Fin (p + (k + k)) :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv

@[simp] theorem slotEquiv_inl (i : Fin p) : slotEquiv (k := k) (.inl i) = coreSlot k i := by
  simp [slotEquiv, coreSlot]
@[simp] theorem slotEquiv_bridge (j : Fin k) :
    slotEquiv (p := p) (.inr (.inl j)) = bridgeSlot p j := by
  simp [slotEquiv, bridgeSlot]
@[simp] theorem slotEquiv_loop (j : Fin k) : slotEquiv (p := p) (.inr (.inr j)) = loopSlot p j := by
  simp [slotEquiv, loopSlot]

/-- The row dictionary of the labelling. -/
noncomputable def labRow :
    MarkedStablePath κ.data (marks (branching κ)) ⊕ (Fin k ⊕ Fin k) ≃ Fin p ⊕ (Fin k ⊕ Fin k) :=
  Equiv.sumCongr κ.fullDim.labelling.row (Equiv.refl _)

theorem labRow_symm_inl (i : Fin p) :
    (labRow κ).symm (.inl i) = .inl (κ.fullDim.labelling.row.symm i) := rfl

theorem labRow_symm_inr (t : Fin k ⊕ Fin k) : (labRow κ).symm (.inr t) = .inr t := rfl

/-- The row dictionary of the label. -/
noncomputable def identRow :
    MarkedStablePath κ.data (marks (branching κ)) ⊕ (Fin k ⊕ Fin k) ≃ Fin p ⊕ (Fin k ⊕ Fin k) :=
  Equiv.sumCongr κ.ident.row (Equiv.refl _)

/-- **The stable labelling of the regrowth.** -/
noncomputable def labelling :
    StableLengthMatrixLabelling (datum κ) (Fin (p + (k + k))) where
  targetEdge := slotEquiv.symm.trans (colEquiv κ)
  row := (stablePathEquiv (branching κ) (connected κ) (markValency_ne_zero κ)).trans
    ((labRow κ).trans slotEquiv)

/-- The block matrix: the marked matrix of `κ`, then `diag(1/2, …, 2, …)`. -/
noncomputable def blockMatrix : Matrix (Fin p ⊕ (Fin k ⊕ Fin k)) (Fin p ⊕ (Fin k ⊕ Fin k)) ℚ :=
  Matrix.fromBlocks κ.matrix 0 0
    (Matrix.diagonal (Sum.elim (fun _ ↦ (1 : ℚ) / 2) (fun _ ↦ 2)))

theorem markedEntry_eq (P : MarkedStablePath κ.data (marks (branching κ)))
    (t : κ.target.edges) :
    markedEntry (branching κ) P t = markedMatrix κ.data (markSet κ.markSource) P t := by
  classical
  unfold markedMatrix markedOccurrences markedEntry
  symm
  convert sum_filter_nonDangling κ.data (fun F ↦ markedRow (markSet κ.markSource) F = P) t
    (fun e ↦ (1 : ℚ) / κ.data.sourceEdgeIndex e) using 1

theorem matrix_labelling :
    GluingDatum.LengthMatrixPresentation.matrix (labelling κ).presentation =
      (blockMatrix κ).submatrix slotEquiv.symm slotEquiv.symm := by
  funext r c
  obtain ⟨z, rfl⟩ := slotEquiv.surjective r
  obtain ⟨w, rfl⟩ := slotEquiv.surjective c
  rw [StableSourceMatrix.labelling_matrix_eq, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  have hRow : (labelling κ).row.symm (slotEquiv z) =
      tagPath (branching κ) (connected κ) (markValency_ne_zero κ) ((labRow κ).symm z) := by
    simp [labelling, stablePathEquiv_symm_apply]
  have hCol : (labelling κ).targetEdge (slotEquiv w) = colEquiv κ w := by
    simp [labelling]
  rw [hRow, hCol]
  rcases z with i | j | j <;> rcases w with i' | j' | j'
  · rw [labRow_symm_inl, colEquiv_inl, matrix_inl_oldE, markedEntry_eq, blockMatrix,
      Matrix.fromBlocks_apply₁₁, MarkedFrame.matrix, MarkedLabelling.matrix_eq]
  · rw [labRow_symm_inl, colEquiv_bridge, matrix_inl_bridgeE, blockMatrix,
      Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
  · rw [labRow_symm_inl, colEquiv_loop, matrix_inl_leafE, blockMatrix,
      Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
  · rw [labRow_symm_inr, colEquiv_inl, matrix_bridge_oldE, blockMatrix,
      Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
  · rw [labRow_symm_inr, colEquiv_bridge, matrix_bridge_bridgeE, blockMatrix,
      Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply]
    by_cases h : j = j' <;> simp [h]
  · rw [labRow_symm_inr, colEquiv_loop, matrix_bridge_leafE, blockMatrix,
      Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply, ite_eq_right (by simp)]
  · rw [labRow_symm_inr, colEquiv_inl, matrix_loop_oldE, blockMatrix,
      Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
  · rw [labRow_symm_inr, colEquiv_bridge, matrix_loop_bridgeE, blockMatrix,
      Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply, ite_eq_right (by simp)]
  · rw [labRow_symm_inr, colEquiv_loop, matrix_loop_leafE, blockMatrix,
      Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply]
    by_cases h : j = j' <;> simp [h]

theorem det_blockMatrix : (blockMatrix κ).det = κ.matrix.det := by
  rw [blockMatrix, Matrix.det_fromBlocks_zero₂₁, Matrix.det_diagonal, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← mul_pow]
  norm_num

/-- **The determinant of the regrowth** is that of `κ`: block diagonal, with `(1/2) · 2 = 1` per
lollipop. -/
theorem det_labelling :
    (GluingDatum.LengthMatrixPresentation.matrix (labelling κ).presentation).det =
      κ.matrix.det := by
  rw [matrix_labelling, Matrix.det_submatrix_equiv_self, det_blockMatrix]

/-- **The full-dimensional presentation of the regrowth.** -/
noncomputable def fullDim (hc : IsMarkedCubic core mark) :
    FullDimensionalSource.FullDimensionalSourcePresentation (datum κ) (Fin (p + (k + k))) where
  valid := valid κ hc
  targetConnected := regrowTarget_connected _ κ.fullDim.targetConnected
  targetGenus := by rw [genus_regrowTarget]; exact κ.fullDim.targetGenus
  saturated := by
    rw [card_edges_regrowTarget, genus_regrowDatum]
    have := κ.fullDim.saturated
    push_cast
    linarith
  labelling := labelling κ
  det_ne_zero := by rw [det_labelling]; exact κ.det_ne_zero
  trivalent := nonDanglingValency_le_three (branching κ) (connected κ) (markValency_ne_zero κ)
    κ.fullDim.trivalent (markValency κ) (markSource_injective κ hc)
  pathEnds := hasPathEnds_regrowDatum (branching κ) (connected κ) (markValency_ne_zero κ)
    κ.fullDim.pathEnds

/-- The vertex dictionary of the label: marked core vertices, then the new vertices `w_j`. -/
def vertexSum : Fin n ⊕ Fin k ≃ Fin (n + k) := finSumFinEquiv

theorem coreIncidence_old_core (v : Fin n) (i : Fin p) :
    Count.coreIncidence (attachLollipops core mark) (oldVertex k v) (coreSlot k i) =
      Count.coreIncidence core v i := by
  simp [Count.coreIncidence]

theorem coreIncidence_old_bridge (v : Fin n) (j : Fin k) :
    Count.coreIncidence (attachLollipops core mark) (oldVertex k v) (bridgeSlot p j) =
      if mark j = v then 1 else 0 := by
  simp [Count.coreIncidence, (lollipopVertex_ne_oldVertex j v)]

theorem coreIncidence_old_loop (v : Fin n) (j : Fin k) :
    Count.coreIncidence (attachLollipops core mark) (oldVertex k v) (loopSlot p j) = 0 := by
  simp [Count.coreIncidence, (lollipopVertex_ne_oldVertex j v)]

theorem coreIncidence_new_core (j : Fin k) (i : Fin p) :
    Count.coreIncidence (attachLollipops core mark) (lollipopVertex n j) (coreSlot k i) = 0 := by
  simp [Count.coreIncidence, (lollipopVertex_ne_oldVertex j _).symm]

theorem coreIncidence_new_bridge (j j' : Fin k) :
    Count.coreIncidence (attachLollipops core mark) (lollipopVertex n j) (bridgeSlot p j') =
      if j' = j then 1 else 0 := by
  simp [Count.coreIncidence, (lollipopVertex_ne_oldVertex j _).symm]

theorem coreIncidence_new_loop (j j' : Fin k) :
    Count.coreIncidence (attachLollipops core mark) (lollipopVertex n j) (loopSlot p j') =
      if j' = j then 2 else 0 := by
  by_cases h : j' = j <;> simp [Count.coreIncidence, h]

/-- **The label of the regrowth**: the label of `κ` on the core part, and the lollipop vertices,
bridges and loops. -/
noncomputable def ident (hc : IsMarkedCubic core mark) :
    Count.CoreIdentification (attachLollipops core mark) (datum κ) where
  vertex := (branchVertexEquiv (branching κ) (connected κ) (markValency_ne_zero κ)
      (markSource_injective κ hc)).symm.trans
    ((Equiv.sumCongr κ.ident.vertex (Equiv.refl _)).trans vertexSum)
  row := (stablePathEquiv (branching κ) (connected κ) (markValency_ne_zero κ)).trans
    ((identRow κ).trans slotEquiv)
  incidence := by
    intro branch slot
    obtain ⟨z, rfl⟩ := (branchVertexEquiv (branching κ) (connected κ) (markValency_ne_zero κ)
      (markSource_injective κ hc)).surjective branch
    obtain ⟨t, rfl⟩ := ((identRow κ).trans slotEquiv).surjective slot
    have hRow : ((stablePathEquiv (branching κ) (connected κ) (markValency_ne_zero κ)).trans
        ((identRow κ).trans slotEquiv)).symm (((identRow κ).trans slotEquiv) t) =
        tagPath (branching κ) (connected κ) (markValency_ne_zero κ) t := by
      simp [stablePathEquiv_symm_apply]
    rw [hRow, Equiv.trans_apply, Equiv.symm_apply_apply]
    rcases z with Y | j <;> rcases t with P | j' | j'
    · rw [branchVertexEquiv_inl, incidenceCount_oldSV_inl]
      simp only [identRow, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, slotEquiv_inl,
        vertexSum, finSumFinEquiv_apply_left]
      rw [show (Fin.castAdd k (κ.ident.vertex Y)) = oldVertex k (κ.ident.vertex Y) from rfl,
        coreIncidence_old_core, ← κ.ident.incidence Y (κ.ident.row P), Equiv.symm_apply_apply]
    · rw [branchVertexEquiv_inl, incidenceCount_oldSV_bridge]
      simp only [identRow, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply,
        Sum.map_inl, slotEquiv_bridge, vertexSum, finSumFinEquiv_apply_left]
      rw [show (Fin.castAdd k (κ.ident.vertex Y)) = oldVertex k (κ.ident.vertex Y) from rfl,
        coreIncidence_old_bridge]
      have hiff : (branching κ).mark j' = Y.1 ↔ mark j' = κ.ident.vertex Y := by
        rw [← κ.ident.vertex_mark j']
        constructor
        · intro h; congr 1; exact Subtype.ext h
        · intro h; exact congrArg Subtype.val (κ.ident.vertex.injective h)
      exact if_congr hiff rfl rfl
    · rw [branchVertexEquiv_inl, incidenceCount_oldSV_loop]
      simp only [identRow, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply,
        slotEquiv_loop, vertexSum, Sum.map_inl, finSumFinEquiv_apply_left]
      rw [show (Fin.castAdd k (κ.ident.vertex Y)) = oldVertex k (κ.ident.vertex Y) from rfl,
        coreIncidence_old_loop]
    · rw [branchVertexEquiv_inr, incidenceCount_wSV_inl]
      simp only [identRow, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, slotEquiv_inl,
        vertexSum, Sum.map_inr, Equiv.refl_apply, finSumFinEquiv_apply_right]
      rw [show (Fin.natAdd n j) = lollipopVertex n j from rfl, coreIncidence_new_core]
    · rw [branchVertexEquiv_inr, incidenceCount_wSV_bridge]
      simp only [identRow, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply,
        slotEquiv_bridge, vertexSum, finSumFinEquiv_apply_right]
      rw [show (Fin.natAdd n j) = lollipopVertex n j from rfl, coreIncidence_new_bridge]
    · rw [branchVertexEquiv_inr, incidenceCount_wSV_loop]
      simp only [identRow, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply,
        slotEquiv_loop, vertexSum, finSumFinEquiv_apply_right]
      rw [show (Fin.natAdd n j) = lollipopVertex n j from rfl, coreIncidence_new_loop]

theorem ident_vertex_apply (hc : IsMarkedCubic core mark)
    (z : MarkedBranchVertex κ.data (marks (branching κ)) ⊕ Fin k) :
    (ident κ hc).vertex (branchVertexEquiv (branching κ) (connected κ) (markValency_ne_zero κ)
      (markSource_injective κ hc) z) = vertexSum (Sum.map κ.ident.vertex id z) := by
  simp only [ident, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

theorem ident_row_stablePath (hc : IsMarkedCubic core mark) (E : NonDanglingEdge (datum κ)) :
    (ident κ hc).row E.stablePath =
      slotEquiv (identRow κ (rowTag (branching κ) (connected κ) (markValency_ne_zero κ) E)) := by
  simp only [ident, Equiv.trans_apply, stablePathEquiv_stablePath]

/-! ## Isomorphisms -/

variable {κ} {κ' : MarkedFrame core mark degree}

theorem iso_x (iso : MarkedFrameIso κ κ') (j : Fin k) :
    iso.datum.targetVertex ((branching κ).x j) = (branching κ').x j := by
  change iso.datum.targetVertex (κ.markSource j).1.1 = (κ'.markSource j).1.1
  rw [← iso.mark j]
  rfl

theorem iso_a (iso : MarkedFrameIso κ κ') (j : Fin k) :
    iso.datum.vertexPerm ((branching κ).x j) ((branching κ).a j) = (branching κ').a j := by
  change iso.datum.vertexPerm (κ.markSource j).1.1 (κ.markSource j).1.2 = (κ'.markSource j).1.2
  rw [← iso.mark j]
  rfl

/-- The isomorphism of regrown data induced by a marked isomorphism. -/
noncomputable def datumIso (iso : MarkedFrameIso κ κ') :
    Count.GeometricDatumIso (datum κ) (datum κ') :=
  regrowIso (branching κ) (branching κ') iso.datum (iso_x iso) (iso_a iso)

end Regrow

/-- **Regrowth**: a lollipop at every mark.

*Construction.* At mark `j`, with `x := (κ.markSource j).1.1`, `a := (κ.markSource j).1.2` and
`S` the block of `a` (`two_le_markIndex` gives a second sheet `b ≠ a` in `S`, chosen by
`Regrow.branching`), attach the path `x — u' — v_C` (`Regrow.regrowTarget`); partitions
`pair a b` over `t_b`, at `u'` and at `v_C`, discrete over `t_l`, unchanged elsewhere
(`Regrow.regrowDatum`). The branches of distinct marks are disjoint. The frame fields
(`Regrow.fullDim`, `Regrow.ident`):

* `valid`: Riemann--Hurwitz at `u_G` is `r⁺(u_G) = r_κ(u_G) - 1 ≥ 0` (this is where
  `κ.ramified` is used), unchanged elsewhere (`Regrow.riemannHurwitz_regrowDatum`);
  connectedness (`Regrow.connected_regrowDatum`);
* `saturated`: `|E(T)| + 2k = 2 (g(G) + k) + 2d - 5` from `κ.fullDim.saturated`
  (`Regrow.genus_regrowDatum`);
* `labelling`: the marked rows of `κ` (core slots) together with the bridge rows `{e_b}` and the
  loop rows `{e_1, e_2}` (`Regrow.stablePathEquiv`);
* `det_ne_zero`: block diagonal `A_κ ⊕ diag(1/2, …, 2, …)` (`Regrow.det_labelling`);
* `trivalent`: `u_G` acquires surviving valency three, `w` has three, `C` two;
* `pathEnds`: the bridge and loop rows end at `w`; the rows of `κ` keep their ends (a mark is now
  a branch vertex);
* `ident`: `κ.ident` on the core part, `lollipopVertex j` for `w`, `bridgeSlot j`, `loopSlot j`. -/
noncomputable def regrowFrame (hc : IsMarkedCubic core mark) (κ : MarkedFrame core mark degree) :
    Frame (attachLollipops core mark) degree where
  target := Regrow.regrowTarget κ.target (Regrow.branching κ).x
  data := Regrow.datum κ
  fullDim := Regrow.fullDim κ hc
  ident := Regrow.ident κ hc

open Regrow DraismaVargas.LocalCases.W4StableSource in
/-- **Regrowth descends to classes**, and does not depend on the choice of `P`: regrowth is well
defined on classes.

*Proof.* An isomorphism `κ ≅ κ'` extends over the new branches (`Regrow.regrowIso`): the identity
on the new target vertices and edges, and over the branch of mark `j` the sheet permutation
`swap (σ b) b' ∘ σ`, `σ` the permutation at `x`. It carries `{a, b}` to `{a', b'}` and moves
sheets only inside the block `S'`, so it is compatible with the unchanged partitions at `x'`.
Over the identity of the lollipop core: on the old part this is `iso.overCore_vertex` and
`iso.overCore_row`, and the lollipop vertices, bridges and loops go to their namesakes. -/
theorem regrowFrame_respects (hc : IsMarkedCubic core mark)
    {κ κ' : MarkedFrame core mark degree} (iso : MarkedFrameIso κ κ') :
    Nonempty (FrameIso (regrowFrame hc κ) (regrowFrame hc κ')) := by
  have hD := connected κ
  have hD' := connected κ'
  have hM := markValency_ne_zero κ
  have hM' := markValency_ne_zero κ'
  have hI := markSource_injective κ hc
  have hI' := markSource_injective κ' hc
  have hV : (regrowFrame hc κ).fullDim.valid.1 = (valid κ hc).1 := rfl
  refine ⟨⟨datumIso iso, fun branch ↦ ?_, fun path ↦ ?_⟩⟩
  · -- vertices
    change (ident κ' hc).vertex ((datumIso iso).branchVertexEquiv (valid κ hc).1 branch) =
      (ident κ hc).vertex branch
    obtain ⟨z, rfl⟩ := (branchVertexEquiv (branching κ) hD hM hI).surjective branch
    rcases z with Y | j
    · have hY' : 3 ≤ nonDanglingValency κ'.data (iso.datum.sourceVertexEquiv Y.1) ∨
          iso.datum.sourceVertexEquiv Y.1 ∈ markSet κ'.markSource := by
        rw [iso.datum.nonDanglingValency_map hD, iso.mem_markSet_map]
        exact Y.2
      have hImg : (datumIso iso).branchVertexEquiv (valid κ hc).1
          (branchVertexEquiv (branching κ) hD hM hI (.inl Y)) =
          branchVertexEquiv (branching κ') hD' hM' hI' (.inl ⟨_, hY'⟩) := Subtype.ext rfl
      rw [hImg, ident_vertex_apply, ident_vertex_apply]
      exact congrArg (fun v ↦ vertexSum (Sum.inl v)) (iso.overCore_vertex Y hY')
    · have hImg : (datumIso iso).branchVertexEquiv (valid κ hc).1
          (branchVertexEquiv (branching κ) hD hM hI (.inr j)) =
          branchVertexEquiv (branching κ') hD' hM' hI' (.inr j) :=
        Subtype.ext (sourceVertexEquiv_wSV (branching κ) (branching κ') iso.datum
          (iso_x iso) (iso_a iso) j)
      rw [hImg, ident_vertex_apply, ident_vertex_apply]
      rfl
  · -- rows
    change (ident κ' hc).row ((datumIso iso).stablePathEquiv (valid κ hc).1 path) =
      (ident κ hc).row path
    obtain ⟨t, rfl⟩ := (stablePathEquiv (branching κ) hD hM).symm.surjective path
    rw [stablePathEquiv_symm_apply]
    rcases t with P | j | j
    · induction P using Quot.ind with
      | mk F =>
        change (ident κ' hc).row
            ((datumIso iso).stablePathEquiv _ (oldND (branching κ) hD hM F).stablePath) =
          (ident κ hc).row (oldND (branching κ) hD hM F).stablePath
        rw [Count.GeometricDatumIso.stablePathEquiv_mk]
        have hE : (datumIso iso).nonDanglingEdgeEquiv (valid κ hc).1
            (oldND (branching κ) hD hM F) =
            oldND (branching κ') hD' hM' (iso.datum.nonDanglingEdgeEquiv hD F) :=
          Subtype.ext (sourceEdgeEquiv_oldSE (branching κ) (branching κ') iso.datum
            (iso_x iso) (iso_a iso) F.1)
        rw [hE, ident_row_stablePath, ident_row_stablePath, rowTag_oldND, rowTag_oldND]
        change slotEquiv (Sum.inl (κ'.ident.row _)) = slotEquiv (Sum.inl (κ.ident.row _))
        rw [iso.overCore_row F]
    · change (ident κ' hc).row
          ((datumIso iso).stablePathEquiv _ (ebND (branching κ) hD hM j).stablePath) =
        (ident κ hc).row (ebND (branching κ) hD hM j).stablePath
      rw [Count.GeometricDatumIso.stablePathEquiv_mk]
      have hE : (datumIso iso).nonDanglingEdgeEquiv (valid κ hc).1
          (ebND (branching κ) hD hM j) = ebND (branching κ') hD' hM' j :=
        Subtype.ext (sourceEdgeEquiv_ebSE (branching κ) (branching κ') iso.datum
          (iso_x iso) (iso_a iso) j)
      rw [hE, ident_row_stablePath, ident_row_stablePath, rowTag_ebND, rowTag_ebND]
      rfl
    · change (ident κ' hc).row
          ((datumIso iso).stablePathEquiv _ (e₁ND (branching κ) hD hM j).stablePath) =
        (ident κ hc).row (e₁ND (branching κ) hD hM j).stablePath
      rw [Count.GeometricDatumIso.stablePathEquiv_mk]
      have hE : (datumIso iso).nonDanglingEdgeEquiv (valid κ hc).1
          (e₁ND (branching κ) hD hM j) = e₁ND (branching κ') hD' hM' j :=
        Subtype.ext (sourceEdgeEquiv_e₁SE (branching κ) (branching κ') iso.datum
          (iso_x iso) (iso_a iso) j)
      rw [hE, ident_row_stablePath, ident_row_stablePath, rowTag_e₁ND, rowTag_e₁ND]
      rfl

end DraismaVargas.Count.MarkedCount
