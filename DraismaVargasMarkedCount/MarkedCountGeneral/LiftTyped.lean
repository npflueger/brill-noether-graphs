module

public import DraismaVargasMarkedCount.MarkedCountGeneral.LiftRows

@[expose] public section

/-!
# The drop lemma: the lift is a typed frame over the subdivided core (I5)

At a position `P` (module `LiftFrame`), every field of `TypedFrame (subdivide core s)` for the
subdivided datum, its marks `markSrc P` and the identification of module `LiftRows`:

* the columns (`colEquiv`): `c'` last, the old target edges by the labelling of `κ`;
* the determinant (`det_ne_zero`): the matrix of `κ` is the merge of the lift's
  (`matrix_merge`, `matrix_col`), so `DropDet.abs_det_eq_of_merge` applies, in the direction
  opposite to the drop;
* validity (`DivalentExpansion.valid`), the dimension count (`saturated`), trivalence, the
  valency of the marks, path ends and (D4′) at every mark;

and the frame `liftFrame P`.
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.MarkedCountGeneral.DivalentContraction
open DraismaVargas.Count.MarkedCountGeneral.MarkedWalk
open GenusSixExistence.Tripod.Gadget (subdivide subdivide_tail_castSucc subdivide_head_castSucc)
open Utilities.Certificate.ExplicitPotential (Core)

namespace LiftSmooth

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}
  {s : Fin p} {κ : TypedFrame core mark types degree} (P : Pos s κ)

/-! ## 1.  The marks keep their labels -/

/-- A lifted old mark is not `V'`. -/
theorem lv_ne_V' (j : Fin k) : lv P (κ.markSource j) ≠ V' P := fun h ↦
  lv_not_x P _ (congrArg (fun X : (D P).SourceVertex ↦ X.1.1) h)

/-- **The marks keep their labels.** -/
theorem vertex_mark (j : Fin (k + 1)) :
    vertexEquiv P ⟨markSrc P j, Or.inr (mem_markSet _ j)⟩ = snocMark mark j := by
  change vertLab P ⟨markSrc P j, Or.inr (mem_markSet _ j)⟩ = _
  induction j using Fin.lastCases with
  | last =>
    exact (vertLab_V' P (B := ⟨markSrc P (Fin.last k), Or.inr (mem_markSet _ _)⟩)
      (markSrc_last P)).trans DropSmooth.snocMark_last.symm
  | cast j =>
    have h : markSrc P j.castSucc ≠ V' P := by rw [markSrc_castSucc]; exact lv_ne_V' P j
    refine (vertLab_of_ne P (B := ⟨markSrc P j.castSucc, Or.inr (mem_markSet _ _)⟩) h).trans ?_
    rw [DropSmooth.snocMark_castSucc]
    congr 1
    unfold oldLab
    have hB : brι P ((S P).branchEquiv (markHyp P) ⟨⟨markSrc P j.castSucc, Or.inr (mem_markSet _ _)⟩, h⟩) =
        ⟨κ.markSource j, Or.inr (mem_markSet _ j)⟩ := by
      apply Subtype.ext
      change (ι P).sourceVertexEquiv ((S P).vmap (markSrc P j.castSucc)) = κ.markSource j
      rw [markSrc_castSucc]
      exact ι_lv P _
    rw [hB, κ.ident.vertex_mark]

/-! ## 2.  The columns and the matrix -/

/-- **The columns of the lift**: the old columns, then `c'`. -/
noncomputable def colEquiv : Fin (p + 1) ≃ (DivalentExpansion.T' (w := w P) (t := t P)).edges :=
  finSuccEquivLast.trans ((Equiv.optionCongr κ.fullDim.labelling.targetEdge).trans
    (occurrenceEquiv κ.target (w P) (DivalentExpansion.place (t P))))

/-- The old columns. -/
theorem colEquiv_castSucc (j : Fin p) :
    colEquiv P j.castSucc = occurrenceEquiv κ.target (w P) (DivalentExpansion.place (t P))
      (some (κ.fullDim.labelling.targetEdge j)) := by
  simp [colEquiv]

/-- The last column is `c'`. -/
theorem colEquiv_last : colEquiv P (Fin.last p) = (S P).c := by
  simp [colEquiv]; rfl

/-- **The labelling of the lift.** -/
noncomputable def labelling : MarkedLabelling (D P) (MM P) (Fin (p + 1)) where
  targetEdge := colEquiv P
  row := rowEquiv P

/-- The entries of the lift. -/
theorem matrix_lift (r c : Fin (p + 1)) :
    GluingDatum.LengthMatrixPresentation.matrix (labelling P).presentation r c =
      markedMatrix (D P) (MM P) ((rowEquiv P).symm r) (colEquiv P c) :=
  MarkedLabelling.matrix_eq _ r c

/-- The contraction isomorphism on columns. -/
theorem ι_col (e : κ.target.edges)
    (he : occurrenceEquiv κ.target (w P) (DivalentExpansion.place (t P)) (some e) ≠ (S P).c) :
    (ι P).targetEdge ((S P).col ⟨_, he⟩) = e := by
  have h := congrArg (fun f : κ.data.SourceEdge ↦ f.1.1)
    (DivalentExpansion.contractIso_emap κ.data (hw P) κ.fullDim.targetConnected
      κ.fullDim.targetGenus (κ.data.sourceEdge e ⟨0, κ.data.degree_pos⟩))
  exact h

/-- The old entries, read on the contraction. -/
theorem matrix_old (R : MarkedStablePath (S P).D (MD P)) (e : κ.target.edges)
    (he : occurrenceEquiv κ.target (w P) (DivalentExpansion.place (t P)) (some e) ≠ (S P).c) :
    markedMatrix κ.data (M κ) (ρ P R) e = markedMatrix (S P).D (MD P) R ((S P).col ⟨_, he⟩) := by
  have h := markedMatrix_map (ι P) (S_valid P).1 (hMarksι P) R ((S P).col ⟨_, he⟩)
  rw [ι_col] at h
  exact h

/-- An old occurrence is not the new edge. -/
theorem occ_ne_c (e : κ.target.edges) :
    occurrenceEquiv κ.target (w P) (DivalentExpansion.place (t P)) (some e) ≠ (S P).c := fun h ↦
  Option.some_ne_none e ((occurrenceEquiv κ.target (w P) (DivalentExpansion.place (t P))).injective h)

/-- The old row of a matrix row of `κ`, as a slot of the subdivided core. -/
noncomputable def θ (_ : Pos s κ) : Fin p ≃ {r : Fin (p + 1) // r ≠ s.castSucc} :=
  (κ.fullDim.labelling.row.symm.trans κ.ident.row).trans
    (Equiv.ofBijective _ (DropSmooth.oldSlot_bijective s))

/-- The value of `θ`. -/
theorem θ_val (i : Fin p) : (θ P i).1 =
    DropSmooth.oldSlot s (κ.ident.row (κ.fullDim.labelling.row.symm i)) := rfl

/-- The matrix row of `κ` merged at `V'`. -/
noncomputable abbrev i₀ (_ : Pos s κ) : Fin p := κ.fullDim.labelling.row (κ.ident.row.symm s)

/-- The merged matrix row goes to the row `last p`. -/
theorem θ_i₀ : (θ P (i₀ P)).1 = Fin.last p := by
  rw [θ_val]; simp [DropSmooth.oldSlot]

/-- **The matrix of `κ` is the merge of the lift's.** -/
theorem matrix_merge (i j : Fin p) :
    κ.matrix i j = GluingDatum.LengthMatrixPresentation.matrix (labelling P).presentation
        (θ P i).1 ((finSuccAboveEquiv (Fin.last p)) j).1 +
      if i = i₀ P then GluingDatum.LengthMatrixPresentation.matrix (labelling P).presentation
        s.castSucc ((finSuccAboveEquiv (Fin.last p)) j).1 else 0 := by
  have hcol : ((finSuccAboveEquiv (Fin.last p)) j).1 = j.castSucc := by
    rw [finSuccAboveEquiv_apply]; exact Fin.succAbove_last_apply j
  rw [matrix_lift, matrix_lift, hcol, colEquiv_castSucc, θ_val,
    show κ.matrix i j = markedMatrix κ.data (M κ) (κ.fullDim.labelling.row.symm i)
      (κ.fullDim.labelling.targetEdge j) from MarkedLabelling.matrix_eq _ i j]
  set R := κ.fullDim.labelling.row.symm i
  set e := κ.fullDim.labelling.targetEdge j
  by_cases hi : i = i₀ P
  · have hR : κ.ident.row R = s := by
      simp only [R, hi, i₀, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    rw [ite_eq_left hi, hR]
    simp only [DropSmooth.oldSlot, ite_true]
    rw [rowEquiv_symm_last, rowEquiv_symm_cs]
    have hRs : R = ρ P (rmap P (rfc P)) := by rw [ρ_rfc, ← hR, Equiv.symm_apply_apply]
    rw [hRs, matrix_old P _ e (occ_ne_c P e),
      (S P).markedMatrix_rowMap_fc (markHyp P) (row_fc_ne_fo P)]
    ring
  · have hR : κ.ident.row R ≠ s := by
      intro h
      apply hi
      simp only [R] at h
      rw [i₀, ← h, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    rw [ite_eq_right hi, add_zero]
    simp only [DropSmooth.oldSlot, hR, ite_false]
    set r := (rowEquiv P).symm (κ.ident.row R).castSucc
    have h₁ : r ≠ rfc P := by
      rw [← rowEquiv_symm_cs]
      exact fun h ↦ hR (Fin.castSucc_injective _ ((rowEquiv P).symm.injective h))
    have h₂ : r ≠ rfo P := by
      rw [← rowEquiv_symm_last]
      exact fun h ↦ (Fin.castSucc_lt_last _).ne ((rowEquiv P).symm.injective h)
    have hlab := rowLab_of_ne P h₁ h₂
    rw [← rowEquiv_apply, Equiv.apply_symm_apply] at hlab
    have hρ : ρ P (rmap P r) = R := by
      have := Fin.castSucc_injective _ hlab
      rw [← Equiv.symm_apply_eq] at this
      exact this.symm.trans (by rw [Equiv.symm_apply_apply])
    rw [← hρ, matrix_old P _ e (occ_ne_c P e),
      (S P).markedMatrix_rowMap_of_ne (markHyp P) h₁ h₂]

/-- The column of the moved `t`. -/
noncomputable abbrev c₂ : Fin (p + 1) := (κ.fullDim.labelling.targetEdge.symm (t P)).castSucc

/-- The column `c₂` is the moved `t`. -/
theorem colEquiv_c₂ : colEquiv P (c₂ P) = (S P).other := by
  rw [colEquiv_castSucc, Equiv.apply_symm_apply, DivalentExpansion.site_other]

/-- The index at `V'`. -/
noncomputable abbrev m : ℕ := (D P).sourceEdgeIndex ((S P).fc (markHyp P)).1

/-- **The two columns at `x'`**: they agree off the rows through `V'`. -/
theorem matrix_col (r : Fin (p + 1)) :
    GluingDatum.LengthMatrixPresentation.matrix (labelling P).presentation r (Fin.last p) -
        GluingDatum.LengthMatrixPresentation.matrix (labelling P).presentation r (c₂ P) =
      (1 : ℚ) / m P * ((if r = s.castSucc then 1 else 0) - (if r = Fin.last p then 1 else 0)) := by
  have h := (S P).markedMatrix_c_add (markHyp P) ((rowEquiv P).symm r)
  rw [matrix_lift, matrix_lift, colEquiv_last, colEquiv_c₂]
  have hc₁ : rfc P = (rowEquiv P).symm r ↔ r = s.castSucc := by
    rw [← rowEquiv_symm_cs, (rowEquiv P).symm.injective.eq_iff, eq_comm]
  have hc₂ : rfo P = (rowEquiv P).symm r ↔ r = Fin.last p := by
    rw [← rowEquiv_symm_last, (rowEquiv P).symm.injective.eq_iff, eq_comm]
  change markedMatrix (D P) (MM P) _ (S P).c +
      (if rfo P = (rowEquiv P).symm r then _ else 0) =
    markedMatrix (D P) (MM P) _ (S P).other + (if rfc P = (rowEquiv P).symm r then _ else 0) at h
  simp only [hc₁, hc₂] at h
  split_ifs at h ⊢ <;> linarith

/-- The index at `V'` is positive. -/
theorem m_pos : 0 < m P := SheetPartition.blockCard_pos _ _

/-- **The determinant of the lift**: `|det A_lift| = |det A_κ| / m`. -/
theorem abs_det : |(GluingDatum.LengthMatrixPresentation.matrix (labelling P).presentation).det| =
    |(1 : ℚ) / m P| * |κ.matrix.det| :=
  abs_det_eq_of_merge (GluingDatum.LengthMatrixPresentation.matrix
      (labelling P).presentation) κ.matrix (r₁ := s.castSucc) (r₂ := Fin.last p)
    (c₁ := Fin.last p) (c₂ := c₂ P) (Fin.castSucc_lt_last s).ne (Fin.castSucc_lt_last _).ne
    (θ P) (finSuccAboveEquiv (Fin.last p)) (θ_i₀ P) _ (matrix_merge P) (matrix_col P)

/-- (D3) for the lift. -/
theorem det_ne_zero :
    (GluingDatum.LengthMatrixPresentation.matrix (labelling P).presentation).det ≠ 0 := by
  intro h
  have h' := abs_det P
  have hm : (0 : ℚ) < m P := by exact_mod_cast m_pos P
  rw [h, abs_zero] at h'
  have h'' : |κ.matrix.det| = 0 := by
    rcases mul_eq_zero.mp h'.symm with h₁ | h₁
    · exact absurd h₁ (abs_ne_zero.mpr (by positivity))
    · exact h₁
  exact κ.det_ne_zero (abs_eq_zero.mp h'')

/-! ## 3.  The remaining fields -/

/-- `r` is invariant under an isomorphism. -/
theorem markRamification_iso {target₁ target₂ : CFGraph} {first : GluingDatum target₁ degree}
    {second : GluingDatum target₂ degree} (iso : GeometricDatumIso first second)
    (Y : first.SourceVertex) :
    markRamification second (iso.sourceVertexEquiv Y) = markRamification first Y :=
  localRamification_map iso Y.1.1 ⟨Y.1.2, Y.2⟩ (iso.sourceVertexEquiv Y).2

/-- The local degree is invariant under an isomorphism. -/
theorem markIndex_iso {target₁ target₂ : CFGraph} {first : GluingDatum target₁ degree}
    {second : GluingDatum target₂ degree} (iso : GeometricDatumIso first second)
    (Y : first.SourceVertex) :
    markIndex second (iso.sourceVertexEquiv Y) = markIndex first Y := by
  unfold markIndex
  change (second.vertexPartition (iso.targetVertex Y.1.1)).blockCard (iso.vertexPerm Y.1.1 Y.1.2) = _
  rw [iso.vertexPartition]
  exact (first.vertexPartition Y.1.1).relabel_blockCard _ _

/-- Lifted vertices keep their surviving valency. -/
theorem nd_lv (Y : κ.data.SourceVertex) :
    nonDanglingValency (D P) (lv P Y) = nonDanglingValency κ.data Y := by
  rw [← (S P).nonDanglingValency_vmap (lv_not_x P Y),
    ← GeometricDatumIso.nonDanglingValency_map (ι P) (S_valid P).1, ι_lv]

/-- The dimension count of the lift. -/
theorem saturated :
    ((DivalentExpansion.T' (w := w P) (t := t P)).edges.card : ℤ) + typeExcess (snocType types 0) =
      2 * genus (D P).sourceGraph + 2 * degree - 5 := by
  have hSat := κ.fullDim.saturated
  have hG : genus (D P).sourceGraph = genus κ.data.sourceGraph :=
    ((S P).genus_sourceGraph).symm.trans (GeometricDatumIso.sourceGenus_map (ι P)).symm
  rw [DropSmooth.typeExcess_snoc, hG]
  have hCard := TargetExpansion.graph_edge_card κ.target (w P) (DivalentExpansion.place (t P))
  change ((Multiset.card (TargetExpansion.graph κ.target (w P) (DivalentExpansion.place (t P))).edges :
    ℕ) : ℤ) + _ = _
  rw [hCard]
  push_cast
  linarith

/-- Trivalence of the lift. -/
theorem trivalent (Y : (D P).SourceVertex) : nonDanglingValency (D P) Y ≤ 3 := by
  by_cases hY : Y.1.1 = (S P).x
  · exact ((S P).nonDanglingValency_le_two hY).trans (by norm_num)
  · rw [← (S P).nonDanglingValency_vmap hY,
      ← GeometricDatumIso.nonDanglingValency_map (ι P) (S_valid P).1]
    exact κ.fullDim.trivalent _

/-- The marks of the lift have surviving valency two. -/
theorem markValency (Y : (D P).SourceVertex) (hY : Y ∈ MM P) : nonDanglingValency (D P) Y = 2 := by
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hY
  induction j using Fin.lastCases with
  | last => rw [markSrc_last]; exact (markHyp P).valency
  | cast j =>
    rw [markSrc_castSucc, nd_lv]
    exact κ.fullDim.markValency _ (mem_markSet _ _)

/-- **Path ends of the lift**, from its incidences. -/
theorem pathEnds : HasMarkedPathEnds (D P) (MM P) := by
  intro f
  obtain ⟨u, hu⟩ := DropSmooth.exists_end_ne_last (core := core) (s := s)
    (rowEquiv P (markedRow (MM P) f))
  set B := (vertexEquiv P).symm u.castSucc
  have hCount := incidence P B (rowEquiv P (markedRow (MM P) f))
  rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply] at hCount
  rw [← hCount] at hu
  obtain ⟨f', hf'⟩ := Finset.card_pos.mp hu
  obtain ⟨hInc, hRow⟩ := Finset.mem_filter.mp hf'
  refine ⟨f', B.1, hRow, (StablePathCount.mem_incidentEdges _ _ _).mp hInc, ?_⟩
  rcases B.2 with h | h
  · left; omega
  · right; exact h

/-- (D4′) at every mark of the lift. -/
theorem typed (j : Fin (k + 1)) : IsTyped (D P) (markSrc P j) (snocType types 0 j) := by
  induction j using Fin.lastCases with
  | last =>
    rw [markSrc_last, DropSmooth.snocType_last]
    refine ⟨?_, ?_⟩
    · exact_mod_cast markRamification_nonneg (D_valid P) _
    · exact SheetPartition.blockCard_pos _ _
  | cast j =>
    rw [markSrc_castSucc, DropSmooth.snocType_castSucc]
    have h := κ.typed j
    unfold IsTyped at h ⊢
    rw [← (S P).markRamification_vmap (lv_not_x P _), ← (S P).markIndex_vmap (lv_not_x P _),
      ← markRamification_iso (ι P), ← markIndex_iso (ι P), ι_lv]
    exact h

/-- **The lift of `κ` at the position `P`**: a typed frame over the subdivided core. -/
noncomputable def liftFrame :
    TypedFrame (subdivide core s) (snocMark mark) (snocType types 0) degree where
  target := DivalentExpansion.T' (w := w P) (t := t P)
  data := D P
  markSource := markSrc P
  fullDim :=
    { valid := D_valid P
      targetConnected := DivalentExpansion.T'_connected κ.fullDim.targetConnected
      targetGenus := DivalentExpansion.T'_genus κ.fullDim.targetGenus
      saturated := saturated P
      labelling := labelling P
      det_ne_zero := det_ne_zero P
      trivalent := trivalent P
      markValency := markValency P
      pathEnds := pathEnds P }
  ident :=
    { vertex := vertexEquiv P
      row := rowEquiv P
      incidence := incidence P
      vertex_mark := vertex_mark P }
  typed := typed P

end LiftSmooth

end DraismaVargas.Count.MarkedCountGeneral
