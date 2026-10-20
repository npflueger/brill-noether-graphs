module

public import DraismaVargasMarkedCount.MarkedCountGeneral.DropExtend
public import DraismaVargasMarkedCount.MarkedCountGeneral.LoopHairpin

@[expose] public section

/-!
# The drop lemma: the lift is unique (I6)

An isomorphism `φ` of the drops of two typed frames `κ₁, κ₂` over `subdivide core s`:

* fixes the start of the walk of the merged row (the vertex labelled `tail s`), and, unless `s`
  is a loop of `core`, its first occurrence (`φ_start`);
* hence carries the walk to the walk (`MarkedWalk.seq_map`), and the lengths along it to the
  lengths (`rowLen_map`);
* so when both frames are open at `y`, it carries the occurrence `g₁` through `V₁` to `g₂`, and
  the end of `g₁` where the walk enters to the end of `g₂` (`φ_g`): both occurrences are the one
  whose interval contains `y(cs s)` (`DropPos.position`, `index_eq_of_mem`);
* and then it extends over the dropped vertex (`extendIso`, module statement below).

If `s` is a loop of `core`, `φ` may reverse the loop row; it is then composed with the automorphism
of the drop reversing it (`exists_loop_reversal`).

`extendIso` (the isomorphism extends over `x_v`) is proved in module `DropExtend`.
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.MarkedCountGeneral.DivalentContraction
open DraismaVargas.Count.MarkedCountGeneral.MarkedWalk
open GenusSixExistence.Tripod.Gadget (subdivide)
open Utilities.Certificate.ExplicitPotential (Core)

/-! ## 1.  Walks under isomorphisms -/

namespace MarkedWalk

variable {target₁ target₂ : CFGraph} {degree : ℕ} {D₁ : GluingDatum target₁ degree}
  {D₂ : GluingDatum target₂ degree} (φ : GeometricDatumIso D₁ D₂) (hConn : D₁.Connected)
  {M₁ : Finset D₁.SourceVertex} {M₂ : Finset D₂.SourceVertex}
  (hMarks : ∀ Y, φ.sourceVertexEquiv Y ∈ M₂ ↔ Y ∈ M₁)

/-- An isomorphism carries the far end to the far end. -/
theorem otherEnd_map {e : D₁.SourceEdge} {Y : D₁.SourceVertex} (h : Incident D₁ e Y) :
    φ.sourceVertexEquiv (otherEnd D₁ e Y) =
      otherEnd D₂ (φ.sourceEdgeEquiv e) (φ.sourceVertexEquiv Y) := by
  have hInc : Incident D₂ (φ.sourceEdgeEquiv e) (φ.sourceVertexEquiv (otherEnd D₁ e Y)) :=
    (φ.incident_map_iff _ _).mpr (incident_otherEnd D₁ e Y)
  have hY : Incident D₂ (φ.sourceEdgeEquiv e) (φ.sourceVertexEquiv Y) :=
    (φ.incident_map_iff _ _).mpr h
  rcases eq_or_eq_otherEnd D₂ hY hInc with h' | h'
  · exact absurd (φ.sourceVertexEquiv.injective h') (otherEnd_ne h)
  · exact h'

include hConn hMarks in
/-- An isomorphism carries the vertices where a row continues to such vertices. -/
theorem continues_map (Y : D₁.SourceVertex) :
    Continues D₂ M₂ (φ.sourceVertexEquiv Y) ↔ Continues D₁ M₁ Y := by
  unfold Continues
  rw [GeometricDatumIso.nonDanglingValency_map φ hConn, hMarks]

include hConn hMarks in
/-- **An isomorphism carries the walk to the walk.** -/
theorem seq_map {e₀ : D₁.SourceEdge} {A₀ : D₁.SourceVertex} (h₀ : Incident D₁ e₀ A₀)
    (hNd : ¬ IsDangling D₁ e₀) (j : ℕ) :
    φ.sourceEdgeEquiv (E (M := M₁) e₀ A₀ j) =
        E (M := M₂) (φ.sourceEdgeEquiv e₀) (φ.sourceVertexEquiv A₀) j ∧
      φ.sourceVertexEquiv (A (M := M₁) e₀ A₀ j) =
        A (M := M₂) (φ.sourceEdgeEquiv e₀) (φ.sourceVertexEquiv A₀) j := by
  induction j with
  | zero => exact ⟨rfl, rfl⟩
  | succ j ih =>
    obtain ⟨hE, hA⟩ := ih
    have hExit : φ.sourceVertexEquiv (exit (M := M₁) e₀ A₀ j) =
        exit (M := M₂) (φ.sourceEdgeEquiv e₀) (φ.sourceVertexEquiv A₀) j := by
      change φ.sourceVertexEquiv (otherEnd D₁ _ _) = otherEnd D₂ _ _
      rw [otherEnd_map φ (incident_A h₀ j), hE, hA]
    by_cases hC : Continues D₁ M₁ (exit (M := M₁) e₀ A₀ j)
    · have hC₂ : Continues D₂ M₂ (exit (M := M₂) (φ.sourceEdgeEquiv e₀) (φ.sourceVertexEquiv A₀) j) := by
        rw [← hExit]; exact (continues_map φ hConn hMarks _).mpr hC
      rw [E_succ hC, E_succ hC₂, A_succ hC, A_succ hC₂]
      refine ⟨?_, hExit⟩
      -- the step occurrence goes to the step occurrence
      have hNdj := not_isDangling_E (M := M₁) (A₀ := A₀) hNd j
      have hNdj₂ : ¬ IsDangling D₂ (E (M := M₂) (φ.sourceEdgeEquiv e₀) (φ.sourceVertexEquiv A₀) j) := by
        rw [← hE]; exact (φ.isDangling_map_iff hConn _).not.mpr hNdj
      have hStep : ¬ IsDangling D₂ (φ.sourceEdgeEquiv (stepEdge D₁ hC.1 (E (M := M₁) e₀ A₀ j))) :=
        (φ.isDangling_map_iff hConn _).not.mpr (stepEdge_not_dangling D₁ hC.1 _)
      have hStepInc : Incident D₂ (φ.sourceEdgeEquiv (stepEdge D₁ hC.1 (E (M := M₁) e₀ A₀ j)))
          (exit (M := M₂) (φ.sourceEdgeEquiv e₀) (φ.sourceVertexEquiv A₀) j) := by
        rw [← hExit]; exact (φ.incident_map_iff _ _).mpr (stepEdge_incident D₁ hC.1 _)
      rcases eq_or_eq_stepEdge D₂ hC₂.1 hNdj₂ (incident_otherEnd D₂ _ _) hStep hStepInc with h | h
      · exfalso
        rw [← hE] at h
        exact stepEdge_ne D₁ hC.1 _ (φ.sourceEdgeEquiv.injective h)
      · exact h
    · have hC₂ : ¬ Continues D₂ M₂ (exit (M := M₂) (φ.sourceEdgeEquiv e₀) (φ.sourceVertexEquiv A₀) j) := by
        rw [← hExit]; exact fun h ↦ hC ((continues_map φ hConn hMarks _).mp h)
      rw [E, A, seq_succ_of_not hC, E, A, seq_succ_of_not hC₂]
      exact ⟨hE, hA⟩

end MarkedWalk

/-! ## 2.  Coordinates and lengths under isomorphisms -/

namespace DropSmooth

variable {n p k degree : ℕ}

section Lengths

variable {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}
  {τ₁ τ₂ : TypedFrame core mark types degree} (φ : TypedFrameIso τ₁ τ₂)

/-- **An isomorphism carries coordinates to coordinates**, column by column. -/
theorem coordsAt_map (y : Fin p → ℚ) (t : τ₁.target.edges) :
    τ₂.coordsAt y (τ₂.fullDim.labelling.targetEdge.symm (φ.datum.targetEdge t)) =
      τ₁.coordsAt y (τ₁.fullDim.labelling.targetEdge.symm t) := by
  have hSolve : τ₂.coordsAt y = fun c ↦ τ₁.coordsAt y (φ.columnPerm c) := by
    refine τ₂.coordsAt_eq_of_mulVec y _ ?_
    funext row
    rw [φ.matrix_eq_submatrix, ← φ.slot_rowPerm]
    refine Eq.trans ?_ (congrFun (τ₁.mulVec_coordsAt y) (φ.rowPerm row))
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
    exact Fintype.sum_equiv φ.columnPerm _ _ fun _ ↦ rfl
  rw [hSolve]
  simp [MarkedFrameBase.Iso.columnPerm]

/-- **An isomorphism preserves lengths.** -/
theorem rowLen_map (y : Fin p → ℚ) (e : τ₁.data.SourceEdge) :
    rowLen τ₂ y (φ.datum.sourceEdgeEquiv e) = rowLen τ₁ y e := by
  unfold rowLen
  rw [GeometricDatumIso.sourceEdgeIndex_map]
  exact congrArg (· / (τ₁.data.sourceEdgeIndex e : ℚ)) (coordsAt_map φ y e.1.1)

end Lengths

/-! ## 3.  Intervals along a walk -/

/-- **Two indices whose intervals contain one point are equal** (positive lengths). -/
theorem index_eq_of_mem {len : ℕ → ℚ} (hpos : ∀ j, 0 < len j) {Y : ℚ} {i₁ i₂ : ℕ}
    (h₁ : ∑ l ∈ Finset.range i₁, len l < Y ∧ Y < ∑ l ∈ Finset.range i₁, len l + len i₁)
    (h₂ : ∑ l ∈ Finset.range i₂, len l < Y ∧ Y < ∑ l ∈ Finset.range i₂, len l + len i₂) :
    i₁ = i₂ := by
  have hmono : ∀ a b, a ≤ b → ∑ l ∈ Finset.range a, len l ≤ ∑ l ∈ Finset.range b, len l := by
    intro a b hab
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
      fun j _ _ ↦ (hpos j).le
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := hmono (i₁ + 1) i₂ hlt
    rw [Finset.sum_range_succ] at this
    linarith [h₁.2, h₂.1]
  · have := hmono (i₂ + 1) i₁ hlt
    rw [Finset.sum_range_succ] at this
    linarith [h₂.2, h₁.1]

/-! ## 4.  The two inputs: extension and loop reversal -/

variable {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ} {s : Fin p}
  (hc : IsMarkedCubic core mark)

/-- **The extension of an isomorphism of drops over the dropped vertex.** If `φ` carries
the occurrence `g₁` through `V₁` to `g₂`, and the image of the far end of the occurrence over `c₁`
to that over `c₂`, then `κ₁ ≅ κ₂`.

*Proof.* Module `DropExtend` (`DropSmooth.extendIso'`): `κᵢ.data` is the resolution expansion of
`(site κᵢ hc).D` at the merged vertex (`M11WallExhaustion.datumIso`), and `φ` lifts between the two
expansions (`ResolutionExpansionFree.liftFree`) with its sheet permutations corrected inside blocks;
the lift commutes with the contractions, carries `V₁ ↦ V₂`, `fc₁ ↦ fc₂`, `fo₁ ↦ fo₂`, and the
over-core clauses descend from `φ`'s. -/
theorem extendIso {κ₁ κ₂ : TypedFrame (subdivide core s) (snocMark mark) (snocType types 0) degree}
    (φ : TypedFrameIso (dropFrame' hc κ₁) (dropFrame' hc κ₂))
    (hg : φ.datum.sourceEdgeEquiv ((site κ₁ hc).edgeMap ((site κ₁ hc).fc (markHyp κ₁ hc)).1) =
      (site κ₂ hc).edgeMap ((site κ₂ hc).fc (markHyp κ₂ hc)).1)
    (hm : φ.datum.sourceVertexEquiv
        ((site κ₁ hc).vmap (Site.far (V κ₁) ((site κ₁ hc).fc (markHyp κ₁ hc)))) =
      (site κ₂ hc).vmap (Site.far (V κ₂) ((site κ₂ hc).fc (markHyp κ₂ hc)))) :
    Nonempty (TypedFrameIso κ₁ κ₂) :=
  ⟨extendIso' hc φ hg hm⟩

include hc in
/-- **The loop reversal.** If `s` is a loop of `core`, a typed frame over `core` has an
automorphism over the identity of `core` exchanging the two occurrences of the loop row at its
branch vertex.

*Proof sketch.* Part I `lemma-loop-bridge`: the loop row is the hairpin `⟨A, e₁, C, e₂, A⟩` over one
leaf edge `t` (its two occurrences, of index one, over `t`; `C` over the leaf). The sheet swap
exchanging the sheets of `e₁` and `e₂` over `t` and the leaf (identity elsewhere; `e₁`, `e₂` lie in
one block at `φ(A)`) is an automorphism fixing every target vertex and edge, the marks, the branch
vertices and every row. The hairpin is read on a caterpillar regrowth (`regrowTailed`,
`c j = types j + 1`, `J j = 1`), where `s` is a loop slot of the cubic core `T.H`, from
`PassOnceLollipopWitness.loopRowLengthTwo` (a frame is a `FibreMember` at `y := A z`); the
regrowth adds singleton sheets only, so the loop row and its occurrences are those of `τ`.

*Proof.* `LoopHairpin.exists_loop_reversal_of_cubic`: the hairpin is read on `DenomRegrow`'s
unmarked regrowth through the fd-level public lemmas (`LoopHairpin.hairpin`), and the swap is
`LoopSwap.exists_swap`. The hypothesis `hc` (distinct marks) is what the regrowth needs, one
caterpillar tail per mark; the only consumer, `exists_iso_start`, has it. -/
theorem exists_loop_reversal (hLoop : core.tail s = core.head s)
    (τ : TypedFrame core mark types degree)
    {e e' : NonDanglingEdge τ.data}
    (he : Incident τ.data e.1 (τ.ident.vertex.symm (core.tail s)).1)
    (he' : Incident τ.data e'.1 (τ.ident.vertex.symm (core.tail s)).1)
    (hRe : τ.ident.row (markedRow (markSet τ.markSource) e) = s)
    (hRe' : τ.ident.row (markedRow (markSet τ.markSource) e') = s) :
    ∃ α : TypedFrameIso τ τ, α.datum.sourceEdgeEquiv e.1 = e'.1 :=
  LoopHairpin.exists_loop_reversal_of_cubic τ hc hLoop he he' hRe hRe'

/-! ## 5.  The start of the walk under an isomorphism -/

/-- The start of the walk is a marked branch vertex of the drop. -/
theorem Â₀_branch (κ : TypedFrame (subdivide core s) (snocMark mark) (snocType types 0) degree) :
    3 ≤ nonDanglingValency (site κ hc).D (Â₀ κ hc) ∨ Â₀ κ hc ∈ MD κ hc := by
  rcases (Btail κ).2 with h | h
  · left; rw [(site κ hc).nonDanglingValency_vmap (Btail_not_over_x κ hc)]; exact h
  · right; exact ((markHyp κ hc).marks _ (Btail_not_over_x κ hc)).mpr h

/-- **The start of the walk is labelled `tail s`.** -/
theorem Â₀_label (κ : TypedFrame (subdivide core s) (snocMark mark) (snocType types 0) degree) :
    (dropFrame' hc κ).ident.vertex ⟨Â₀ κ hc, Â₀_branch hc κ⟩ = core.tail s := by
  have hEq : (⟨Â₀ κ hc, Â₀_branch hc κ⟩ : MarkedBranchVertex (site κ hc).D (MD κ hc)) =
      (site κ hc).branchEquiv (markHyp κ hc) ⟨Btail κ, Btail_ne κ⟩ := Subtype.ext rfl
  change vertexEquiv κ hc _ = _
  refine (congrArg (vertexEquiv κ hc) hEq).trans ?_
  apply Fin.castSucc_injective
  rw [vertexEquiv_branchEquiv]
  unfold Btail
  rw [Equiv.apply_symm_apply]

variable {κ₁ κ₂ : TypedFrame (subdivide core s) (snocMark mark) (snocType types 0) degree}

/-- **An isomorphism of drops fixes the start of the walk.** -/
theorem iso_Â₀ (φ : TypedFrameIso (dropFrame' hc κ₁) (dropFrame' hc κ₂)) :
    φ.datum.sourceVertexEquiv (Â₀ κ₁ hc) = Â₀ κ₂ hc := by
  have hImage : 3 ≤ nonDanglingValency (dropFrame' hc κ₂).data (φ.datum.sourceVertexEquiv (Â₀ κ₁ hc)) ∨
      φ.datum.sourceVertexEquiv (Â₀ κ₁ hc) ∈ markSet (dropFrame' hc κ₂).markSource := by
    rcases Â₀_branch hc κ₁ with h | h
    · left
      exact h.trans_eq (GeometricDatumIso.nonDanglingValency_map φ.datum
        (dropFrame' hc κ₁).fullDim.valid.1 (Â₀ κ₁ hc)).symm
    · right; exact (φ.mem_markSet_map _).mpr h
  have h := φ.overCore_vertex ⟨Â₀ κ₁ hc, Â₀_branch hc κ₁⟩ hImage
  rw [Â₀_label hc κ₁, ← Â₀_label hc κ₂] at h
  exact congrArg Subtype.val ((dropFrame' hc κ₂).ident.vertex.injective h)

/-- The occurrences of the merged row at the start: as many as `s` has ends at `tail s`. -/
theorem card_start (κ : TypedFrame (subdivide core s) (snocMark mark) (snocType types 0) degree) :
    markedIncidenceCount (site κ hc).D (MD κ hc) (Â₀ κ hc) ((rowEquiv κ hc).symm s) =
      coreIncidence core (core.tail s) s := by
  have h := (dropFrame' hc κ).ident.incidence ⟨Â₀ κ hc, Â₀_branch hc κ⟩ s
  rw [Â₀_label hc κ] at h
  exact h

open Classical in
/-- The first occurrence lies on the merged row, at the start. -/
theorem ê₀_mem (κ : TypedFrame (subdivide core s) (snocMark mark) (snocType types 0) degree) :
    (⟨ê₀ κ hc, start_nd κ hc⟩ : NonDanglingEdge (site κ hc).D) ∈
      (StablePathCount.incidentEdges (site κ hc).D (Â₀ κ hc)).filter fun e ↦
        markedRow (MD κ hc) e = (rowEquiv κ hc).symm s := by
  refine Finset.mem_filter.mpr ⟨(StablePathCount.mem_incidentEdges _ _ _).mpr (start_incident κ hc), ?_⟩
  rw [rowEquiv_symm]
  unfold rowOf
  rw [← row_fc κ hc]
  exact start_row κ hc

/-- **An isomorphism of drops may be chosen to fix the first occurrence of the walk.** -/
theorem exists_iso_start (φ : TypedFrameIso (dropFrame' hc κ₁) (dropFrame' hc κ₂)) :
    ∃ ψ : TypedFrameIso (dropFrame' hc κ₁) (dropFrame' hc κ₂),
      ψ.datum.sourceEdgeEquiv (ê₀ κ₁ hc) = ê₀ κ₂ hc := by
  -- the image of the first occurrence is an occurrence of the merged row at the start
  set e' : NonDanglingEdge (site κ₂ hc).D :=
    φ.datum.nonDanglingEdgeEquiv (dropFrame' hc κ₁).fullDim.valid.1 ⟨ê₀ κ₁ hc, start_nd κ₁ hc⟩
  have he'Inc : Incident (site κ₂ hc).D e'.1 (Â₀ κ₂ hc) := by
    rw [← iso_Â₀ hc φ]
    exact (φ.datum.incident_map_iff _ _).mpr (start_incident κ₁ hc)
  have he'Row : markedRow (MD κ₂ hc) e' = (rowEquiv κ₂ hc).symm s := by
    rw [Equiv.eq_symm_apply]
    have h := φ.overCore_row ⟨ê₀ κ₁ hc, start_nd κ₁ hc⟩
    refine h.trans ?_
    show rowEquiv κ₁ hc (markedRow (MD κ₁ hc) ⟨ê₀ κ₁ hc, start_nd κ₁ hc⟩) = s
    rw [start_row, rowEquiv_rowMap, row_fc κ₁ hc, Equiv.apply_symm_apply]
    simp [merge]
  have he'Mem : e' ∈ (StablePathCount.incidentEdges (site κ₂ hc).D (Â₀ κ₂ hc)).filter fun e ↦
      markedRow (MD κ₂ hc) e = (rowEquiv κ₂ hc).symm s :=
    Finset.mem_filter.mpr ⟨(StablePathCount.mem_incidentEdges _ _ _).mpr he'Inc, he'Row⟩
  by_cases hEq : e'.1 = ê₀ κ₂ hc
  · exact ⟨φ, hEq⟩
  · -- two occurrences of the merged row at the start: `s` is a loop
    have hTwo : 2 ≤ markedIncidenceCount (site κ₂ hc).D (MD κ₂ hc) (Â₀ κ₂ hc)
        ((rowEquiv κ₂ hc).symm s) := by
      unfold markedIncidenceCount
      have hne : e' ≠ ⟨ê₀ κ₂ hc, start_nd κ₂ hc⟩ := fun h ↦ hEq (congrArg Subtype.val h)
      refine (Finset.card_le_card ?_).trans' (Finset.card_pair hne).ge
      intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact he'Mem
      · rw [Finset.mem_singleton.mp hf]; exact ê₀_mem hc κ₂
    rw [card_start hc κ₂] at hTwo
    have hLoop : core.tail s = core.head s := by
      unfold coreIncidence at hTwo
      by_contra h
      rw [ite_eq_left rfl, ite_eq_right (Ne.symm h)] at hTwo
      omega
    have hTailB : (dropFrame' hc κ₂).ident.vertex.symm (core.tail s) =
        ⟨Â₀ κ₂ hc, Â₀_branch hc κ₂⟩ :=
      (Equiv.symm_apply_eq _).mpr (Â₀_label hc κ₂).symm
    obtain ⟨α, hα⟩ := exists_loop_reversal hc hLoop (dropFrame' hc κ₂) (e := e')
      (e' := ⟨ê₀ κ₂ hc, start_nd κ₂ hc⟩)
      (by rw [hTailB]; exact he'Inc) (by rw [hTailB]; exact start_incident κ₂ hc)
      ((congrArg (rowEquiv κ₂ hc) he'Row).trans (Equiv.apply_symm_apply _ _))
      (by
        show rowEquiv κ₂ hc (markedRow (MD κ₂ hc) ⟨ê₀ κ₂ hc, start_nd κ₂ hc⟩) = s
        rw [start_row, rowEquiv_rowMap, row_fc κ₂ hc, Equiv.apply_symm_apply]
        simp [merge])
    exact ⟨φ.trans α, hα⟩

/-! ## 6.  I6 -/

/-- **I6: the lift is unique.** -/
theorem liftUnique {y : Fin (p + 1) → ℚ} (h₁ : κ₁.OpenAt y) (h₂ : κ₂.OpenAt y)
    (φ : TypedFrameIso (dropFrame' hc κ₁) (dropFrame' hc κ₂)) : Nonempty (TypedFrameIso κ₁ κ₂) := by
  obtain ⟨ψ, hψ⟩ := exists_iso_start hc φ
  have hA := iso_Â₀ hc ψ
  have hMarks : ∀ Y, ψ.datum.sourceVertexEquiv Y ∈ MD κ₂ hc ↔ Y ∈ MD κ₁ hc :=
    fun Y ↦ ψ.mem_markSet_map Y
  have hWalk := fun j ↦ seq_map (M₁ := MD κ₁ hc) (M₂ := MD κ₂ hc) ψ.datum
    (dropFrame' hc κ₁).fullDim.valid.1 hMarks (start_incident κ₁ hc) (start_nd κ₁ hc) j
  rw [hψ, hA] at hWalk
  -- lengths along the walks agree
  have hLen : ∀ j, rowLen (dropFrame' hc κ₂) (mergeRequest s y)
      (E (M := MD κ₂ hc) (ê₀ κ₂ hc) (Â₀ κ₂ hc) j) =
        rowLen (dropFrame' hc κ₁) (mergeRequest s y) (E (M := MD κ₁ hc) (ê₀ κ₁ hc) (Â₀ κ₁ hc) j) := by
    intro j
    rw [← (hWalk j).1]
    exact rowLen_map ψ _ _
  have hPre : ∀ j, pre κ₂ hc y j = pre κ₁ hc y j := fun j ↦
    Finset.sum_congr rfl fun l _ ↦ hLen l
  -- the two positions
  have hPos₁ := position κ₁ hc h₁
  have hPos₂ := position κ₂ hc h₂
  rw [← hPre, ← hLen] at hPos₁
  have hOpen₂ := openAt_dropFrame' κ₂ hc h₂
  have hi := index_eq_of_mem (len := fun j ↦ rowLen (dropFrame' hc κ₂) (mergeRequest s y)
      (E (M := MD κ₂ hc) (ê₀ κ₂ hc) (Â₀ κ₂ hc) j))
    (fun j ↦ rowLen_pos _ hOpen₂ _) hPos₁ hPos₂
  -- `ψ` carries `g₁` to `g₂` and the entry to the entry
  refine extendIso hc ψ ?_ ?_
  · refine (congrArg ψ.datum.sourceEdgeEquiv (iV_spec κ₁ hc)).trans ?_
    refine ((hWalk _).1).trans ?_
    rw [hi]
    exact (iV_spec κ₂ hc).symm
  · refine (congrArg ψ.datum.sourceVertexEquiv (orient κ₁ hc).symm).trans ?_
    refine ((hWalk _).2).trans ?_
    rw [hi]
    exact orient κ₂ hc

end DropSmooth

end DraismaVargas.Count.MarkedCountGeneral
