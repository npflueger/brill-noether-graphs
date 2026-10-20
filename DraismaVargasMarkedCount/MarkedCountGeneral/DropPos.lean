module

public import DraismaVargasMarkedCount.MarkedCountGeneral.DropTransport
public import DraismaVargasMarkedCount.MarkedCountGeneral.DropSide

@[expose] public section

/-!
# The drop lemma: the position of the dropped mark

For a typed frame `κ` over `subdivide core s`, walk the merged row of its drop (`rowOf s`) from
the branch vertex labelled `tail s` (`walkSetup`): the occurrence `g` through `V` is the
`i`-th, and the walk enters it at the image of the far end of the occurrence over `c`
(`orient`; otherwise the row labelled `cs s` would be the row labelled `last p`). So the row
labelled `cs s` is the side of the walk before `g`, plus the occurrence over `c` at `V`
(`DivalentContraction.Site.SideSetup.row_eq_iff_side`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.MarkedCountGeneral.DivalentContraction
open DraismaVargas.Count.MarkedCountGeneral.MarkedWalk
open GenusSixExistence.Tripod.Gadget (subdivide subdivide_tail_castSucc subdivide_head_castSucc)
open Utilities.Certificate.ExplicitPotential (Core)

namespace DropSmooth

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}
  {s : Fin p} (κ : TypedFrame (subdivide core s) (snocMark mark) (snocType types 0) degree)
  (hc : IsMarkedCubic core mark)

/-! ## 1.  The start of the walk -/

/-- The branch vertex labelled `tail s`. -/
noncomputable def Btail : MarkedBranchVertex κ.data (M κ) :=
  κ.ident.vertex.symm (core.tail s).castSucc

/-- The branch vertex labelled `tail s` is not the dropped mark. -/
theorem Btail_ne : (Btail κ).1 ≠ V κ := by
  intro h
  have := (ident_vertex_eq_last_iff κ (Btail κ)).mpr h
  unfold Btail at this
  rw [Equiv.apply_symm_apply] at this
  exact (Fin.castSucc_lt_last _).ne this

/-- The row `cs s` has an occurrence at the branch vertex labelled `tail s`. -/
theorem exists_ftail : ∃ f : NonDanglingEdge κ.data, Incident κ.data f.1 (Btail κ).1 ∧
    markedRow (M κ) f = κ.ident.row.symm s.castSucc := by
  have h := κ.ident.incidence (Btail κ) s.castSucc
  unfold Btail at h
  rw [Equiv.apply_symm_apply] at h
  have hPos : 0 < markedIncidenceCount κ.data (M κ) (κ.ident.vertex.symm (core.tail s).castSucc).1
      (κ.ident.row.symm s.castSucc) := by
    rw [h]
    unfold coreIncidence
    rw [subdivide_tail_castSucc]
    simp
  obtain ⟨f, hf⟩ := Finset.card_pos.mp hPos
  obtain ⟨hInc, hRow⟩ := Finset.mem_filter.mp hf
  exact ⟨f, (StablePathCount.mem_incidentEdges _ _ _).mp hInc, hRow⟩

/-- An occurrence of the row `cs s` at the branch vertex labelled `tail s`. -/
noncomputable def ftail : NonDanglingEdge κ.data := (exists_ftail κ).choose

/-- The chosen occurrence at `tail s` on the row `cs s`. -/
theorem ftail_spec : Incident κ.data (ftail κ).1 (Btail κ).1 ∧
    markedRow (M κ) (ftail κ) = κ.ident.row.symm s.castSucc :=
  (exists_ftail κ).choose_spec

/-- The branch vertex labelled `tail s` is not over `x`. -/
theorem Btail_not_over_x : (Btail κ).1.1.1 ≠ (site κ hc).x :=
  (site κ hc).not_over_x (markHyp κ hc) (Btail κ) (Btail_ne κ)

/-- The first occurrence of the walk. -/
noncomputable abbrev ê₀ : (site κ hc).D.SourceEdge := (site κ hc).edgeMap (ftail κ).1

/-- The start of the walk. -/
noncomputable abbrev Â₀ : (site κ hc).D.SourceVertex := (site κ hc).vmap (Btail κ).1

/-- The start occurrence of the drop's walk meets the start vertex. -/
theorem start_incident : Incident (site κ hc).D (ê₀ κ hc) (Â₀ κ hc) :=
  (site κ hc).incident_edgeMap (Btail_not_over_x κ hc) (ftail_spec κ).1

/-- The start occurrence of the drop's walk survives. -/
theorem start_nd : ¬ IsDangling (site κ hc).D (ê₀ κ hc) :=
  ((site κ hc).isDangling_edgeMap_iff _).not.mpr (ftail κ).2

/-- The row does not continue at the start vertex of the drop's walk. -/
theorem start_end : ¬ Continues (site κ hc).D (MD κ hc) (Â₀ κ hc) := by
  rintro ⟨h2, hM⟩
  rcases (Btail κ).2 with h | h
  · rw [(site κ hc).nonDanglingValency_vmap (Btail_not_over_x κ hc)] at h2
    omega
  · exact hM (((markHyp κ hc).marks _ (Btail_not_over_x κ hc)).mpr h)

/-- The chosen occurrence at `tail s` is on the row of `fc`. -/
theorem row_ftail : markedRow (M κ) (ftail κ) = markedRow (M κ) ((site κ hc).fc (markHyp κ hc)) := by
  rw [(ftail_spec κ).2, row_fc]

/-- The start of the drop's walk is on the merged row. -/
theorem start_row : markedRow (MD κ hc) (⟨ê₀ κ hc, start_nd κ hc⟩ : NonDanglingEdge (site κ hc).D) =
    (site κ hc).rowMap (markHyp κ hc) (markedRow (M κ) ((site κ hc).fc (markHyp κ hc))) := by
  rw [← row_ftail κ hc]
  rfl

/-- `g`, the occurrence through `V`, in the walk. -/
theorem exists_iV : ∃ i ≤ stop (start_incident κ hc) (start_nd κ hc) (start_end κ hc),
    (site κ hc).edgeMap ((site κ hc).fc (markHyp κ hc)).1 =
      E (M := MD κ hc) (ê₀ κ hc) (Â₀ κ hc) i :=
  exists_index (start_incident κ hc) (start_nd κ hc) (start_end κ hc)
    ((site κ hc).ndMap ((site κ hc).fc (markHyp κ hc))) (start_row κ hc).symm

/-- The index of `g` in the walk. -/
noncomputable def iV : ℕ := (exists_iV κ hc).choose

/-- The index of `g` is at most the stop. -/
theorem iV_le : iV κ hc ≤ stop (start_incident κ hc) (start_nd κ hc) (start_end κ hc) :=
  (exists_iV κ hc).choose_spec.1

/-- The index of `g` in the drop's walk. -/
theorem iV_spec : (site κ hc).edgeMap ((site κ hc).fc (markHyp κ hc)).1 =
    E (M := MD κ hc) (ê₀ κ hc) (Â₀ κ hc) (iV κ hc) :=
  (exists_iV κ hc).choose_spec.2

/-- A side setup with a given orientation. -/
noncomputable def setupWith {fs : NonDanglingEdge κ.data} (hfs : (site κ hc).AtV (markHyp κ hc) fs)
    (hOrient : A (M := MD κ hc) (ê₀ κ hc) (Â₀ κ hc) (iV κ hc) = (site κ hc).vmap (Site.far (V κ) fs)) :
    (site κ hc).SideSetup (markHyp κ hc) where
  ê₀ := ê₀ κ hc
  Â₀ := Â₀ κ hc
  h₀ := start_incident κ hc
  hNd := start_nd κ hc
  hEnd := start_end κ hc
  hRow := start_row κ hc
  i := iV κ hc
  hi := iV_le κ hc
  hg := iV_spec κ hc
  fs := fs
  hfs := hfs
  hOrient := hOrient

/-- **The walk enters `g` at the image of the far end of the occurrence over `c`.** -/
theorem orient : A (M := MD κ hc) (ê₀ κ hc) (Â₀ κ hc) (iV κ hc) =
    (site κ hc).vmap (Site.far (V κ) ((site κ hc).fc (markHyp κ hc))) := by
  have hInc : Incident (site κ hc).D ((site κ hc).edgeMap ((site κ hc).fc (markHyp κ hc)).1)
      (A (M := MD κ hc) (ê₀ κ hc) (Â₀ κ hc) (iV κ hc)) := by
    rw [iV_spec]; exact incident_A (start_incident κ hc) _
  rcases (site κ hc).incident_g (markHyp κ hc) hInc with h | h
  · exact h
  · exfalso
    set W := setupWith κ hc (fs := (site κ hc).fo (markHyp κ hc)) (Or.inr rfl) h
    have hSide : W.Side (ftail κ) := by
      rcases Nat.eq_zero_or_pos (iV κ hc) with h0 | hpos
      · -- `g` is the first occurrence
        right
        have hE : (site κ hc).edgeMap (ftail κ).1 =
            (site κ hc).edgeMap ((site κ hc).fc (markHyp κ hc)).1 := by
          rw [iV_spec, h0]; rfl
        have hAt := (site κ hc).atV_of_edgeMap_eq (markHyp κ hc) hE
        have hB : (Btail κ).1 = Site.far (V κ) ((site κ hc).fo (markHyp κ hc)) := by
          refine ((site κ hc).vmap_inj (Btail_not_over_x κ hc)
            ((site κ hc).far_not_over_x (markHyp κ hc) (Or.inr rfl))).mp ?_
          rw [← h, h0]; rfl
        rcases hAt with hfc | hfo
        · exfalso
          refine (site κ hc).not_incident_far (markHyp κ hc) (Or.inr rfl) (Or.inl rfl)
            ((site κ hc).fc_ne_fo (markHyp κ hc)).symm ?_
          rw [← hB, ← hfc]; exact (ftail_spec κ).1
        · exact hfo
      · left
        exact ⟨0, hpos, rfl⟩
    have hFib : (site κ hc).rowMap (markHyp κ hc) (markedRow (M κ) (ftail κ)) =
        (site κ hc).rowMap (markHyp κ hc) (markedRow (M κ) ((site κ hc).fc (markHyp κ hc))) := by
      rw [row_ftail κ hc]
    have hRowEq := (W.row_eq_iff_side hFib).mpr hSide
    rw [row_ftail κ hc] at hRowEq
    exact row_fc_ne_fo κ hc hRowEq

/-- **The side setup of the drop**: the walk from `tail s`, entering `g` on the side of `c`. -/
noncomputable def walkSetup : (site κ hc).SideSetup (markHyp κ hc) :=
  setupWith κ hc (Or.inl rfl) (orient κ hc)

/-- **The row labelled `cs s` is the side of the walk before `g`.** -/
theorem row_cs_iff {f : NonDanglingEdge κ.data}
    (hf : (site κ hc).rowMap (markHyp κ hc) (markedRow (M κ) f) =
      (site κ hc).rowMap (markHyp κ hc) (markedRow (M κ) ((site κ hc).fc (markHyp κ hc)))) :
    markedRow (M κ) f = κ.ident.row.symm s.castSucc ↔ (walkSetup κ hc).Side f := by
  rw [← row_fc κ hc]
  exact (walkSetup κ hc).row_eq_iff_side hf

/-! ## 2.  Lengths -/

/-- **The length of an occurrence** of a typed frame at a request: its column's coordinate over its
index. -/
noncomputable def rowLen {n' p' k' : ℕ} {core' : Core n' p'} {mark' : Fin k' → Fin n'}
    {types' : Fin k' → ℕ} (τ : TypedFrame core' mark' types' degree) (y : Fin p' → ℚ)
    (e : τ.data.SourceEdge) : ℚ :=
  τ.coordsAt y (τ.fullDim.labelling.targetEdge.symm e.1.1) / τ.data.sourceEdgeIndex e

/-- The occurrences mapping to an occurrence of the contraction away from `c`. -/
theorem edgeMap_eq_emap_iff (f : κ.data.SourceEdge)
    (e : {e : κ.data.SourceEdge // e.1.1 ≠ (site κ hc).c}) :
    (site κ hc).edgeMap f = (site κ hc).emap e ↔
      f = e.1 ∨ (e.1.1.1 = (site κ hc).other ∧ f = (site κ hc).cPartner e.1) := by
  constructor
  · intro h
    have hmu : (site κ hc).mu f = e :=
      GluingContraction.sourceEdgeMap_injective κ.data (contracted := (site κ hc).c) rfl _ _ h
    by_cases hf : f.1.1 = (site κ hc).c
    · right
      rw [(site κ hc).mu_of_eq hf] at hmu
      have hp : (site κ hc).partner f = e.1 := congrArg Subtype.val hmu
      refine ⟨by rw [← hp]; rfl, ?_⟩
      rw [← hp, (site κ hc).cPartner_partner hf]
    · left
      rw [(site κ hc).mu_of_ne hf] at hmu
      exact congrArg Subtype.val hmu
  · rintro (rfl | ⟨he, rfl⟩)
    · rw [(site κ hc).edgeMap_of_ne e.2]
    · unfold Site.edgeMap
      rw [(site κ hc).mu_of_eq (e := (site κ hc).cPartner e.1) rfl]
      congr 1
      exact Subtype.ext ((site κ hc).partner_cPartner he)

open Classical in
/-- The coordinate of the drop at the image of an old column. -/
theorem dropCoords_colEquiv_symm (z : Fin (p + 1) → ℚ) (f : κ.target.edges)
    (hf : f ≠ (site κ hc).c) :
    dropCoords κ hc z ((colEquiv κ hc).symm ((site κ hc).col ⟨f, hf⟩)) =
      z ((L κ).targetEdge.symm f) + if f = (site κ hc).other then z (c₀ κ) else 0 := by
  have hne : (L κ).targetEdge.symm f ≠ c₀ κ := fun h ↦ hf ((L κ).targetEdge.symm.injective h)
  obtain ⟨j₀, hj₀⟩ := Fin.exists_succAbove_eq hne
  have hcol : colEquiv κ hc j₀ = (site κ hc).col ⟨f, hf⟩ := by
    rw [colEquiv_apply]
    congr 1
    apply Subtype.ext
    simp only [hj₀, Equiv.apply_symm_apply]
  rw [← hcol, Equiv.symm_apply_apply]
  unfold dropCoords
  rw [hj₀]
  congr 1
  by_cases hfo : f = (site κ hc).other
  · rw [ite_eq_left hfo, ite_eq_left (by rw [hfo])]
  · rw [ite_eq_right hfo, ite_eq_right fun h ↦ hfo ((L κ).targetEdge.symm.injective h)]

open Classical in
/-- **The length of an occurrence of the drop is the total length of its fibre.** -/
theorem rowLen_drop (y : Fin (p + 1) → ℚ) (ê : (site κ hc).D.SourceEdge) :
    rowLen (dropFrame' hc κ) (mergeRequest s y) ê =
      ∑ f : κ.data.SourceEdge, if (site κ hc).edgeMap f = ê then rowLen κ y f else 0 := by
  obtain ⟨e, rfl⟩ := ContractionFibre.sourceEdgeMap_surjective κ.data (contracted := (site κ hc).c)
    rfl (GluingContraction.fst_ne_snd _) (hOne κ) ê
  have hIdx : (site κ hc).D.sourceEdgeIndex ((site κ hc).emap e) = κ.data.sourceEdgeIndex e.1 :=
    ContractionFibre.sourceEdgeIndex_sourceEdgeMap κ.data rfl _ _ e
  -- the fibre
  have hFib : ∀ f, (site κ hc).edgeMap f = (site κ hc).emap e ↔
      f = e.1 ∨ (e.1.1.1 = (site κ hc).other ∧ f = (site κ hc).cPartner e.1) :=
    fun f ↦ edgeMap_eq_emap_iff κ hc f e
  have hLHS : rowLen (dropFrame' hc κ) (mergeRequest s y) ((site κ hc).emap e) =
      (κ.coordsAt y ((L κ).targetEdge.symm e.1.1.1) +
        if e.1.1.1 = (site κ hc).other then κ.coordsAt y (c₀ κ) else 0) /
          κ.data.sourceEdgeIndex e.1 := by
    unfold rowLen
    rw [coordsAt_dropFrame']
    change dropCoords κ hc (κ.coordsAt y) ((colEquiv κ hc).symm ((site κ hc).col ⟨e.1.1.1, e.2⟩)) /
      ((site κ hc).D.sourceEdgeIndex ((site κ hc).emap e) : ℚ) = _
    rw [hIdx, dropCoords_colEquiv_symm κ hc _ e.1.1.1 e.2]
  rw [hLHS]
  by_cases ho : e.1.1.1 = (site κ hc).other
  · have hne : (site κ hc).cPartner e.1 ≠ e.1 := by
      intro h
      have := congrArg (fun g : κ.data.SourceEdge ↦ g.1.1) h
      exact e.2 (this.symm.trans rfl)
    rw [Finset.sum_eq_add (e.1) ((site κ hc).cPartner e.1) hne.symm]
    · rw [ite_eq_left ((hFib _).mpr (Or.inl rfl)),
        ite_eq_left ((hFib _).mpr (Or.inr ⟨ho, rfl⟩)), ite_eq_left ho]
      have hIdx' : κ.data.sourceEdgeIndex ((site κ hc).cPartner e.1) = κ.data.sourceEdgeIndex e.1 := by
        have h := (site κ hc).sourceEdgeIndex_partner (e := (site κ hc).cPartner e.1) rfl
        rw [(site κ hc).partner_cPartner ho] at h
        exact h.symm
      unfold rowLen
      rw [hIdx']
      have hc₀ : (L κ).targetEdge.symm ((site κ hc).cPartner e.1).1.1 = c₀ κ := rfl
      rw [hc₀]
      ring
    · intro f _ hf
      refine ite_eq_right fun h ↦ ?_
      rcases (hFib f).mp h with h | ⟨-, h⟩
      · exact absurd h hf.1
      · exact absurd h hf.2
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_single e.1]
    · rw [ite_eq_left ((hFib _).mpr (Or.inl rfl)), ite_eq_right ho, add_zero]
      rfl
    · intro f _ hf
      rw [ite_eq_right fun h ↦ by
        rcases (hFib f).mp h with h | ⟨h', -⟩
        · exact hf h
        · exact ho h']
    · intro h; exact absurd (Finset.mem_univ _) h

open Classical in
/-- **A row of the matrix against coordinates** is the sum of the lengths along the row. -/
theorem mulVec_eq_sum {n' p' k' : ℕ} {core' : Core n' p'} {mark' : Fin k' → Fin n'}
    {types' : Fin k' → ℕ} (τ : TypedFrame core' mark' types' degree) (z : Fin p' → ℚ)
    (r : Fin p') :
    τ.matrix.mulVec z r = ∑ f : τ.data.SourceEdge,
      if (∃ hNd : ¬ IsDangling τ.data f, markedRow (markSet τ.markSource)
          (⟨f, hNd⟩ : NonDanglingEdge τ.data) = τ.fullDim.labelling.row.symm r) then
        z (τ.fullDim.labelling.targetEdge.symm f.1.1) / τ.data.sourceEdgeIndex f else 0 := by
  unfold Matrix.mulVec dotProduct
  simp only [TypedFrame.matrix, MarkedLabelling.matrix_eq, DivalentContraction.Site.markedMatrix_eq_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ ↦ ?_
  rw [Finset.sum_eq_single (τ.fullDim.labelling.targetEdge.symm f.1.1)]
  · simp only [Equiv.apply_symm_apply, true_and]
    split_ifs <;> ring
  · intro c _ hc
    rw [ite_eq_right fun h ↦ hc (by rw [h.1, Equiv.symm_apply_apply]), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The prefix length of the walk before index `j`. -/
noncomputable def pre (y : Fin (p + 1) → ℚ) (j : ℕ) : ℚ :=
  ∑ l ∈ Finset.range j,
    rowLen (dropFrame' hc κ) (mergeRequest s y) (E (M := MD κ hc) (ê₀ κ hc) (Â₀ κ hc) l)

open Classical in
/-- **The row labelled `cs s` is as long as the prefix, plus the half of `g` over `c`.** -/
theorem length_cs (y : Fin (p + 1) → ℚ) :
    y s.castSucc = pre κ hc y (iV κ hc) + rowLen κ y ((site κ hc).fc (markHyp κ hc)).1 := by
  -- the row as a sum
  have hRow := mulVec_eq_sum κ (κ.coordsAt y) ((L κ).row (κ.ident.row.symm s.castSucc))
  rw [κ.mulVec_coordsAt] at hRow
  have hSlot : κ.slot ((L κ).row (κ.ident.row.symm s.castSucc)) = s.castSucc := by
    change κ.ident.row ((L κ).row.symm ((L κ).row (κ.ident.row.symm s.castSucc))) = _
    rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  simp only [hSlot, Equiv.symm_apply_apply] at hRow
  have hPre : pre κ hc y (iV κ hc) = ∑ l ∈ Finset.range (iV κ hc), ∑ f : κ.data.SourceEdge,
      if (site κ hc).edgeMap f = E (M := MD κ hc) (ê₀ κ hc) (Â₀ κ hc) l then rowLen κ y f else 0 :=
    Finset.sum_congr rfl fun l _ ↦ rowLen_drop κ hc y _
  rw [hRow, hPre]
  set W := walkSetup κ hc
  set g := (site κ hc).fc (markHyp κ hc)
  -- the indicator of the row is the side
  have hInd : ∀ f : κ.data.SourceEdge,
      (∃ hNd : ¬ IsDangling κ.data f, markedRow (M κ) (⟨f, hNd⟩ : NonDanglingEdge κ.data) =
        κ.ident.row.symm s.castSucc) ↔
      ((∃ j < iV κ hc, (site κ hc).edgeMap f = E (M := MD κ hc) (ê₀ κ hc) (Â₀ κ hc) j) ∨
        f = g.1) := by
    intro f
    constructor
    · rintro ⟨hNd, hR⟩
      have hFib : (site κ hc).rowMap (markHyp κ hc) (markedRow (M κ) ⟨f, hNd⟩) =
          (site κ hc).rowMap (markHyp κ hc) (markedRow (M κ) g) := by
        rw [hR, ← row_fc κ hc]
      rcases ((row_cs_iff κ hc hFib).mp hR) with h | h
      · exact Or.inl h
      · exact Or.inr (congrArg Subtype.val h)
    · rintro (⟨j, hj, hfj⟩ | rfl)
      · have hNdE := not_isDangling_E (M := MD κ hc) (A₀ := Â₀ κ hc) (start_nd κ hc) j
        have hNd : ¬ IsDangling κ.data f :=
          ((site κ hc).isDangling_edgeMap_iff f).not.mp (hfj ▸ hNdE)
        refine ⟨hNd, (row_cs_iff κ hc ?_).mpr (Or.inl ⟨j, hj, hfj⟩)⟩
        have hRowE := markedRow_E (M := MD κ hc) (start_incident κ hc) (start_nd κ hc) j
        rw [start_row] at hRowE
        have hEq : (site κ hc).ndMap ⟨f, hNd⟩ =
            ⟨E (M := MD κ hc) (ê₀ κ hc) (Â₀ κ hc) j, hNdE⟩ := Subtype.ext hfj
        change markedRow (MD κ hc) ((site κ hc).ndMap ⟨f, hNd⟩) = _
        rw [hEq]; exact hRowE
      · exact ⟨g.2, (row_cs_iff κ hc rfl).mpr (Or.inr rfl)⟩
  simp only [hInd]
  -- split off `g`
  have hgNot : ¬ ∃ j < iV κ hc, (site κ hc).edgeMap g.1 = E (M := MD κ hc) (ê₀ κ hc) (Â₀ κ hc) j := by
    rintro ⟨j, hj, hgj⟩
    have := E_injOn (start_incident κ hc) (start_nd κ hc) (start_end κ hc) (by
      have := iV_le κ hc; omega) (iV_le κ hc) (hgj.symm.trans (iV_spec κ hc))
    omega
  have hSplit : ∀ f : κ.data.SourceEdge,
      (if (∃ j < iV κ hc, (site κ hc).edgeMap f = E (M := MD κ hc) (ê₀ κ hc) (Â₀ κ hc) j) ∨ f = g.1
        then κ.coordsAt y ((L κ).targetEdge.symm f.1.1) / κ.data.sourceEdgeIndex f else 0) =
      (if (∃ j < iV κ hc, (site κ hc).edgeMap f = E (M := MD κ hc) (ê₀ κ hc) (Â₀ κ hc) j)
        then rowLen κ y f else 0) + (if f = g.1 then rowLen κ y f else 0) := by
    intro f
    by_cases h₁ : ∃ j < iV κ hc, (site κ hc).edgeMap f = E (M := MD κ hc) (ê₀ κ hc) (Â₀ κ hc) j
    · have h₂ : f ≠ g.1 := fun h ↦ hgNot (h ▸ h₁)
      simp [h₁, h₂, rowLen]
    · by_cases h₂ : f = g.1
      · subst h₂
        simp [hgNot, rowLen]
      · simp [h₁, h₂]
  rw [Finset.sum_congr rfl fun f _ ↦ hSplit f, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  congr 1
  -- the prefix, regrouped by the walk
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ ↦ ?_
  by_cases h₁ : ∃ j < iV κ hc, (site κ hc).edgeMap f = E (M := MD κ hc) (ê₀ κ hc) (Â₀ κ hc) j
  · obtain ⟨j, hj, hfj⟩ := h₁
    rw [ite_eq_left ⟨j, hj, hfj⟩, Finset.sum_eq_single j]
    · rw [ite_eq_left hfj]
    · intro l hl hlj
      refine ite_eq_right fun h ↦ hlj ?_
      exact E_injOn (start_incident κ hc) (start_nd κ hc) (start_end κ hc)
        (by have := Finset.mem_range.mp hl; have := iV_le κ hc; omega)
        (by have := iV_le κ hc; omega) (h.symm.trans hfj)
    · intro h; exact absurd (Finset.mem_range.mpr hj) h
  · rw [ite_eq_right h₁]
    refine (Finset.sum_eq_zero fun l hl ↦ ite_eq_right fun h ↦ h₁ ⟨l, Finset.mem_range.mp hl, h⟩).symm

/-- Lengths are positive in an open frame. -/
theorem rowLen_pos {n' p' k' : ℕ} {core' : Core n' p'} {mark' : Fin k' → Fin n'}
    {types' : Fin k' → ℕ} (τ : TypedFrame core' mark' types' degree) {y : Fin p' → ℚ}
    (hOpen : τ.OpenAt y) (e : τ.data.SourceEdge) : 0 < rowLen τ y e := by
  unfold rowLen
  have hIdx : (0 : ℚ) < τ.data.sourceEdgeIndex e := by
    exact_mod_cast SheetPartition.blockCard_pos _ _
  exact div_pos (hOpen _) hIdx

open Classical in
/-- **The length of `g` is the sum of its two halves.** -/
theorem rowLen_g (y : Fin (p + 1) → ℚ) :
    rowLen (dropFrame' hc κ) (mergeRequest s y)
        ((site κ hc).edgeMap ((site κ hc).fc (markHyp κ hc)).1) =
      rowLen κ y ((site κ hc).fc (markHyp κ hc)).1 + rowLen κ y ((site κ hc).fo (markHyp κ hc)).1 := by
  rw [rowLen_drop κ hc y]
  have hne : ((site κ hc).fc (markHyp κ hc)).1 ≠ ((site κ hc).fo (markHyp κ hc)).1 :=
    fun h ↦ (site κ hc).fc_ne_fo (markHyp κ hc) (Subtype.ext h)
  rw [Finset.sum_eq_add _ _ hne]
  · rw [ite_eq_left rfl, ite_eq_left ((site κ hc).edgeMap_fo (markHyp κ hc))]
  · intro f _ hf
    refine ite_eq_right fun h ↦ ?_
    have hNd : ¬ IsDangling κ.data f := ((site κ hc).isDangling_edgeMap_iff f).not.mp
      (h ▸ ((site κ hc).isDangling_edgeMap_iff _).not.mpr ((site κ hc).fc (markHyp κ hc)).2)
    rcases (site κ hc).atV_of_edgeMap_eq (markHyp κ hc) (f := ⟨f, hNd⟩) h with h' | h'
    · exact absurd (congrArg Subtype.val h') hf.1
    · exact absurd (congrArg Subtype.val h') hf.2
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The position of the dropped mark**: at an open frame, `y(cs s)` lies strictly inside
the interval of `g` in the walk. -/
theorem position {y : Fin (p + 1) → ℚ} (hOpen : κ.OpenAt y) :
    pre κ hc y (iV κ hc) < y s.castSucc ∧
      y s.castSucc < pre κ hc y (iV κ hc) + rowLen (dropFrame' hc κ) (mergeRequest s y)
        (E (M := MD κ hc) (ê₀ κ hc) (Â₀ κ hc) (iV κ hc)) := by
  rw [length_cs κ hc y]
  have h₁ := rowLen_pos κ hOpen ((site κ hc).fc (markHyp κ hc)).1
  have h₂ := rowLen_pos κ hOpen ((site κ hc).fo (markHyp κ hc)).1
  have hg : rowLen (dropFrame' hc κ) (mergeRequest s y)
      (E (M := MD κ hc) (ê₀ κ hc) (Â₀ κ hc) (iV κ hc)) =
        rowLen κ y ((site κ hc).fc (markHyp κ hc)).1 + rowLen κ y ((site κ hc).fo (markHyp κ hc)).1 :=
    (congrArg (rowLen (dropFrame' hc κ) (mergeRequest s y)) (iV_spec κ hc)).symm.trans
      (rowLen_g κ hc y)
  rw [hg]
  constructor <;> linarith

end DropSmooth

end DraismaVargas.Count.MarkedCountGeneral
