module

public import DraismaVargasMarkedCount.MarkedCountGeneral.RestrictTailFrame

@[expose] public section

/-!
# Restriction over the tails: the images of the marks, their ramification, and the leaves

* the marks have distinct images (`xMark_injective`), of valency two or three (`two_le_val_xMark`);
* **a fold forces a ramified mark** (`two_le_sPath_of_divalent`; `φ(u_j)` is divalent in `T` exactly
  when it is a leaf of `T'`, i.e. when the restriction folds at `u_j`): if `φ(u_j)` is divalent
  then `s_1 = m(u_j) ≥ 2`;
* `r_ψ(u_j) = r_φ(u_j) + s_1 - 1` and `m_ψ(u_j) = m_φ(u_j) ≥ s_1` (`localRamification_markSrc`,
  `sPath_le_blockCard_markSrc`);
* the leaves: `l(T) = #(other kept leaves) + Σⱼ aⱼ` and `l(T') = #(other kept leaves) +
  #{j | φ(u_j) divalent}` (`leafCount_target_eq`, `leafCount_rTarget_eq`).
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

noncomputable section

/-! ## 1.  Generic: the index form at a vertex with three survivors -/

section Generic

variable {target : CFGraph.{0}} {d : ℕ} {data : GluingDatum target d}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (fd : FullDimensionalSourcePresentation data coordinate)

include fd in
theorem sum_index_of_three {B : data.SourceVertex} {a b c' : data.SourceEdge}
    (hab : a ≠ b) (hac : a ≠ c') (hbc : b ≠ c') (ha : Incident data a B) (hb : Incident data b B)
    (hc' : Incident data c' B)
    (hAll : ∀ F, ¬ IsDangling data F → Incident data F B → F = a ∨ F = b ∨ F = c') :
    ∑ item : IncidentSourceEdge data B, ((data.sourceEdgeIndex item.1 : ℤ) - 1) =
      data.sourceEdgeIndex a + data.sourceEdgeIndex b + data.sourceEdgeIndex c' - 3 := by
  classical
  set i₁ : IncidentSourceEdge data B := ⟨a, ha⟩
  set i₂ : IncidentSourceEdge data B := ⟨b, hb⟩
  set i₃ : IncidentSourceEdge data B := ⟨c', hc'⟩
  have h12 : i₁ ≠ i₂ := fun e ↦ hab (congrArg Subtype.val e)
  have h13 : i₁ ≠ i₃ := fun e ↦ hac (congrArg Subtype.val e)
  have h23 : i₂ ≠ i₃ := fun e ↦ hbc (congrArg Subtype.val e)
  have hRestrict : (∑ item ∈ ({i₁, i₂, i₃} : Finset (IncidentSourceEdge data B)),
      ((data.sourceEdgeIndex item.1 : ℤ) - 1)) =
      ∑ item : IncidentSourceEdge data B, ((data.sourceEdgeIndex item.1 : ℤ) - 1) := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro x _ hx
    have hDang : IsDangling data x.1 := by
      by_contra hs
      rcases hAll x.1 hs x.2 with e | e | e
      · exact hx (by rw [show x = i₁ from Subtype.ext e]; simp)
      · exact hx (by rw [show x = i₂ from Subtype.ext e]; simp)
      · exact hx (by rw [show x = i₃ from Subtype.ext e]; simp)
    rw [fd.danglingEdgeNoGlue x.1 hDang]
    norm_num
  rw [← hRestrict, Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
    Finset.sum_singleton]
  ring

end Generic

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {c : Fin k → ℕ}
  (T : Tailed core mark c) (hc : IsMarkedCubic core mark) {y : Fin T.P → ℚ}
  (M : FibreMember T.H y degree)

include hc

/-! ## 2.  The germs at a mark -/

/-- The first path edge at a mark. -/
abbrev e₁ (j : Fin k) : M.data.SourceEdge := (TailAt.pathE (cat T j) M (T.cubic hc) 0).1

/-- **The two germs of the marked core at `u_j`.** -/
theorem exists_germs (j : Fin k) : ∃ g₁ g₂ : M.data.SourceEdge, g₁ ≠ g₂ ∧
    g₁ ≠ e₁ T hc M j ∧ g₂ ≠ e₁ T hc M j ∧
    ¬ IsDangling M.data g₁ ∧ ¬ IsDangling M.data g₂ ∧
    Incident M.data g₁ (uSource T M j) ∧ Incident M.data g₂ (uSource T M j) ∧
    (∀ F, ¬ IsDangling M.data F → Incident M.data F (uSource T M j) →
      F = e₁ T hc M j ∨ F = g₁ ∨ F = g₂) := by
  classical
  have hS := SpineStep.card_survivorsAt (data := M.data) (uSource T M j)
  rw [nonDanglingValency_uSource] at hS
  have hmem : e₁ T hc M j ∈ SpineStep.survivorsAt M.data (uSource T M j) :=
    SpineStep.mem_survivorsAt.mpr ⟨(TailAt.pathE (cat T j) M (T.cubic hc) 0).2,
      uSource_incident_pathE T hc M j⟩
  obtain ⟨g₁, g₂, hg, hpair⟩ := Finset.card_eq_two.mp
    (show ((SpineStep.survivorsAt M.data (uSource T M j)).erase (e₁ T hc M j)).card = 2 by
      rw [Finset.card_erase_of_mem hmem, hS])
  have h1 : g₁ ∈ (SpineStep.survivorsAt M.data (uSource T M j)).erase (e₁ T hc M j) := by
    rw [hpair]; simp
  have h2 : g₂ ∈ (SpineStep.survivorsAt M.data (uSource T M j)).erase (e₁ T hc M j) := by
    rw [hpair]; simp
  obtain ⟨h1ne, h1S⟩ := Finset.mem_erase.mp h1
  obtain ⟨h2ne, h2S⟩ := Finset.mem_erase.mp h2
  obtain ⟨h1s, h1i⟩ := SpineStep.mem_survivorsAt.mp h1S
  obtain ⟨h2s, h2i⟩ := SpineStep.mem_survivorsAt.mp h2S
  refine ⟨g₁, g₂, hg, h1ne, h2ne, h1s, h2s, h1i, h2i, fun F hF hFI ↦ ?_⟩
  by_cases hFe : F = e₁ T hc M j
  · exact Or.inl hFe
  · have : F ∈ (SpineStep.survivorsAt M.data (uSource T M j)).erase (e₁ T hc M j) :=
      Finset.mem_erase.mpr ⟨hFe, SpineStep.mem_survivorsAt.mpr ⟨hF, hFI⟩⟩
    rw [hpair] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    exact Or.inr this

theorem germ_target_ne {j : Fin k} {g : M.data.SourceEdge} (hg : ¬ IsDangling M.data g)
    (hne : g ≠ e₁ T hc M j) : g.1.1 ≠ tEdge T hc M j (Sum.inl 0) := fun h ↦
  hne (TailAt.eq_pathE_of_over (cat T j) M (T.cubic hc) 0 hg h)

/-! ## 3.  The images of the marks -/

theorem two_le_val_xMark (j : Fin k) : 2 ≤ (GluingDatum.incidentEdges (xMark T M j)).card := by
  obtain ⟨g₁, -, -, h1ne, -, h1s, -, h1i, -, -⟩ := exists_germs T hc M j
  have hg := SpineStep.target_mem_of_incident h1i
  have ht := tEdge_zero_mem_xMark T hc M j
  have hne := germ_target_ne T hc M h1s h1ne
  have : ({g₁.1.1, tEdge T hc M j (Sum.inl 0)} : Finset M.target.edges) ⊆
      GluingDatum.incidentEdges (xMark T M j) := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact hg
    · exact ht
  have h := Finset.card_le_card this
  rwa [Finset.card_pair hne] at h

omit hc in
theorem val_xMark_le_three (j : Fin k) : (GluingDatum.incidentEdges (xMark T M j)).card ≤ 3 := by
  have hChange := M.data.targetChange_nonneg M.fullDim.valid (xMark T M j)
  rw [IndexPattern.targetChange_eq_three_sub_valency M.fullDim] at hChange
  omega

/-- **Distinct marks have distinct images** (as the ramification-one `xV_injective`). -/
theorem xMark_injective : Function.Injective (xMark T M) := by
  classical
  intro i j hij
  by_contra hne
  have hti := tEdge_zero_mem_xMark T hc M i
  have htj : tEdge T hc M j (Sum.inl 0) ∈ GluingDatum.incidentEdges (xMark T M i) := by
    rw [hij]; exact tEdge_zero_mem_xMark T hc M j
  have htij : tEdge T hc M i (Sum.inl 0) ≠ tEdge T hc M j (Sum.inl 0) := fun h ↦
    hne (congrArg Sigma.fst (tailEdge_injective T hc M (a₁ := ⟨i, Sum.inl 0⟩) (a₂ := ⟨j, Sum.inl 0⟩) h))
  obtain ⟨g₁, g₂, hg, h1ne, h2ne, h1s, h2s, h1i, h2i, hAll⟩ := exists_germs T hc M i
  -- the germs avoid both tail edges
  have hAvoid : ∀ g, g ≠ e₁ T hc M i → ¬ IsDangling M.data g → Incident M.data g (uSource T M i) →
      g.1.1 ∈ ((GluingDatum.incidentEdges (xMark T M i)).erase (tEdge T hc M i (Sum.inl 0))).erase
        (tEdge T hc M j (Sum.inl 0)) := by
    intro g hgne hgS hgI
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨germ_target_ne T hc M hgS hgne,
      SpineStep.target_mem_of_incident hgI⟩⟩
    intro hgt
    have := TailAt.eq_pathE_of_over (cat T j) M (T.cubic hc) 0 hgS hgt
    subst this
    have hu : uSource T M i = uSource T M j := LollipopBridgeFibre.eq_of_incident_of_target_eq hij hgI
      (uSource_incident_pathE T hc M j)
    exact hne (uSource_injective T M hc hu)
  have hA₁ := hAvoid g₁ h1ne h1s h1i
  have hA₂ := hAvoid g₂ h2ne h2s h2i
  have hVal3 : (GluingDatum.incidentEdges (xMark T M i)).card = 3 := by
    have h4 : 1 ≤ (((GluingDatum.incidentEdges (xMark T M i)).erase (tEdge T hc M i (Sum.inl 0))).erase
        (tEdge T hc M j (Sum.inl 0))).card := Finset.card_pos.mpr ⟨_, hA₁⟩
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨htij.symm, htj⟩),
      Finset.card_erase_of_mem hti] at h4
    have hle : (GluingDatum.incidentEdges (xMark T M i)).card ≤ 3 := val_xMark_le_three T M i
    omega
  have hOne : (((GluingDatum.incidentEdges (xMark T M i)).erase (tEdge T hc M i (Sum.inl 0))).erase
      (tEdge T hc M j (Sum.inl 0))).card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨htij.symm, htj⟩),
      Finset.card_erase_of_mem hti, hVal3]
  have hShare : g₁.1.1 = g₂.1.1 := Finset.card_le_one.mp hOne.le _ hA₁ _ hA₂
  have hRam := PassOnceLollipop.localRamification_eq_zero_of_trivalent M.fullDim hVal3
    ⟨(uSource T M i).1.2, (uSource T M i).2⟩
  exact PassOnceLollipop.not_three_survivors_sharing_direction M.fullDim hRam
    (nonDanglingValency_uSource T M i) hg h1ne h2ne h1s h1i h2s h2i
    (TailAt.pathE (cat T i) M (T.cubic hc) 0).2 (uSource_incident_pathE T hc M i) hShare

/-- **A fold forces a ramified mark**: if `φ(u_j)` is divalent, `s_1 = m(u_j) ≥ 2`. -/
theorem two_le_sPath_of_divalent (j : Fin k)
    (h2 : (GluingDatum.incidentEdges (xMark T M j)).card = 2) : 2 ≤ sPath T hc M j 0 := by
  classical
  obtain ⟨g₁, g₂, hg, h1ne, h2ne, h1s, h2s, h1i, h2i, hAll⟩ := exists_germs T hc M j
  set u := uSource T M j
  -- both germs lie over the second edge at `φ(u)`
  have hShare : g₁.1.1 = g₂.1.1 := by
    have hti := tEdge_zero_mem_xMark T hc M j
    have hOne : ((GluingDatum.incidentEdges (xMark T M j)).erase
        (tEdge T hc M j (Sum.inl 0))).card = 1 := by
      rw [Finset.card_erase_of_mem hti, h2]
    have hm₁ : g₁.1.1 ∈ (GluingDatum.incidentEdges (xMark T M j)).erase
        (tEdge T hc M j (Sum.inl 0)) :=
      Finset.mem_erase.mpr ⟨germ_target_ne T hc M h1s h1ne, SpineStep.target_mem_of_incident h1i⟩
    have hm₂ : g₂.1.1 ∈ (GluingDatum.incidentEdges (xMark T M j)).erase
        (tEdge T hc M j (Sum.inl 0)) :=
      Finset.mem_erase.mpr ⟨germ_target_ne T hc M h2s h2ne, SpineStep.target_mem_of_incident h2i⟩
    exact Finset.card_le_one.mp hOne.le _ hm₁ _ hm₂
  have hPair := RowWalk.sourceEdgeIndex_add_le_blockCard M.data h1i h2i hg hShare
  have hS₀ := StableLocalProperties.sourceEdgeIndex_le_blockCard M.data u
    ⟨e₁ T hc M j, uSource_incident_pathE T hc M j⟩
  have hForm := StableLocalProperties.localRamification_eq_index_form M.data u
  rw [sum_index_of_three M.fullDim (Ne.symm h1ne) (Ne.symm h2ne) hg
    (uSource_incident_pathE T hc M j) h1i h2i hAll] at hForm
  have hLe := IndexPattern.localRamification_le_targetChange M.fullDim (wall := u.1.1) ⟨u.1.2, u.2⟩
  rw [IndexPattern.targetChange_eq_three_sub_valency M.fullDim] at hLe
  change _ ≤ 3 - ((GluingDatum.incidentEdges (xMark T M j)).card : ℤ) at hLe
  rw [h2] at hLe
  have h1 := StableLocalProperties.sourceEdgeIndex_pos M.data g₁
  have h2' := StableLocalProperties.sourceEdgeIndex_pos M.data g₂
  unfold sPath
  simp only [e₁] at hForm hS₀
  push_cast at hForm hLe hPair hS₀
  omega

/-! ## 4.  The ramification and the block at a mark of `ψ` -/

variable (m : ℕ) (hm : m + nShed T hc M = degree)

/-- **`r_ψ(u_j) = r_φ(u_j) + s_1 - 1`**. -/
theorem localRamification_markSrc (j : Fin k) :
    MarkedCount.markRamification (dat T hc M m hm) (markSrc T hc M m hm j) =
      MarkedCount.markRamification M.data (uSource T M j) + ((sPath T hc M j 0 : ℤ) - 1) := by
  classical
  unfold MarkedCount.markRamification
  rw [← Sheets.localRamification_inclSV (markSrc T hc M m hm j)]
  have h := localRamification_restrict_index (D := M.data) (Keep := Keep T M)
    (hKeep := Keep_nonempty T hc M) (inclSV (markSrc T hc M m hm j))
  refine h.trans ?_
  have hu : svIncl (inclSV (markSrc T hc M m hm j)) = uSource T M j := cSV_markSrc T hc M m hm j
  rw [hu]
  congr 1
  rw [Finset.sum_eq_single (e₁ T hc M j)]
  · rfl
  · intro E hE hne
    obtain ⟨hI, hk⟩ := (Finset.mem_filter.mp hE).2
    by_cases hS : IsDangling M.data E
    · rw [M.fullDim.danglingEdgeNoGlue E hS]; norm_num
    · exfalso
      obtain ⟨i, rfl, hi⟩ := eq_pathE_of_lol T hc M (xMark_mem_Keep T hc M j) ⟨hS, hk⟩ hI
      exact hne (by rw [uSource_injective T M hc hi.symm])
  · intro h
    exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, uSource_incident_pathE T hc M j,
      not_keptEdge_tEdge T hc M j (Sum.inl 0)⟩) h

theorem blockCard_markSrc (j : Fin k) :
    markIndex (dat T hc M m hm) (markSrc T hc M m hm j) =
      (M.data.vertexPartition (uSource T M j).1.1).blockCard (uSource T M j).1.2 := by
  unfold markIndex
  rw [← Sheets.blockCard_inclSV, ← blockCard_svIncl]
  have hu : svIncl (inclSV (markSrc T hc M m hm j)) = uSource T M j := cSV_markSrc T hc M m hm j
  rw [hu]

theorem sPath_le_blockCard_markSrc (j : Fin k) :
    sPath T hc M j 0 ≤ markIndex (dat T hc M m hm) (markSrc T hc M m hm j) := by
  rw [blockCard_markSrc]
  exact StableLocalProperties.sourceEdgeIndex_le_blockCard M.data _
    ⟨e₁ T hc M j, uSource_incident_pathE T hc M j⟩

/-! ## 5.  The leaves -/

section Leaves

/-- At a kept vertex, the deleted target edges are the first path edges of the marks over it. -/
theorem card_notKept_at {v : M.target.V} (hv : v ∈ Keep T M) :
    ((GluingDatum.incidentEdges v).filter (fun e ↦ ¬ KeptEdge (Keep T M) e)).card =
      (Finset.univ.filter (fun j ↦ xMark T M j = v)).card := by
  classical
  symm
  refine Finset.card_bij (fun j _ ↦ tEdge T hc M j (Sum.inl 0)) ?_ ?_ ?_
  · intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    exact Finset.mem_filter.mpr ⟨hj' ▸ tEdge_zero_mem_xMark T hc M j,
      not_keptEdge_tEdge T hc M j (Sum.inl 0)⟩
  · intro i _ j _ h
    exact congrArg Sigma.fst (tailEdge_injective T hc M (a₁ := ⟨i, Sum.inl 0⟩)
      (a₂ := ⟨j, Sum.inl 0⟩) h)
  · intro e he
    obtain ⟨heI, hk⟩ := Finset.mem_filter.mp he
    obtain ⟨j, rfl, hj⟩ := eq_tEdge_zero_of_kept T hc M hv heI hk
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩

theorem card_marks_at (v : M.target.V) :
    (Finset.univ.filter (fun j ↦ xMark T M j = v)).card =
      if v ∈ Set.range (xMark T M) then 1 else 0 := by
  classical
  split_ifs with h
  · obtain ⟨j, rfl⟩ := h
    rw [Finset.card_eq_one]
    refine ⟨j, ?_⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h ↦ xMark_injective T hc M h, fun h ↦ h ▸ rfl⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun j _ hj ↦ h ⟨j, hj⟩

theorem card_kept_at {v : M.target.V} (hv : v ∈ Keep T M) :
    ((GluingDatum.incidentEdges v).filter (KeptEdge (Keep T M))).card +
        (if v ∈ Set.range (xMark T M) then 1 else 0) = (GluingDatum.incidentEdges v).card := by
  rw [← card_marks_at T hc M, ← card_notKept_at T hc M hv]
  exact Finset.card_filter_add_card_filter_not _

/-- The kept leaves of `T` that are not images of marks. -/
noncomputable def otherLeaves : Finset M.target.V := by
  classical
  exact Finset.univ.filter fun v ↦ v ∈ Keep T M ∧ v ∉ Set.range (xMark T M) ∧
    (GluingDatum.incidentEdges v).card = 1

omit hc in
theorem mem_otherLeaves {v : M.target.V} :
    v ∈ otherLeaves T M ↔ v ∈ Keep T M ∧ v ∉ Set.range (xMark T M) ∧
      (GluingDatum.incidentEdges v).card = 1 := by
  classical
  unfold otherLeaves
  simp

/-- The marks whose image is divalent (the folds). -/
noncomputable def folds : Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun j ↦ (GluingDatum.incidentEdges (xMark T M j)).card = 2

omit hc in
theorem mem_folds {j : Fin k} : j ∈ folds T M ↔ (GluingDatum.incidentEdges (xMark T M j)).card = 2 := by
  classical
  unfold folds
  simp

/-- **The leaves of `T'`**: the other kept leaves and the images of the folds. -/
theorem leafCount_rTarget_eq :
    Count.leafCount (rTarget T hc M) = (otherLeaves T M).card + (folds T M).card := by
  classical
  have hImage : (Count.leafVertices (rTarget T hc M)).map ⟨vIncl, vIncl_injective⟩ =
      otherLeaves T M ∪ (folds T M).image (xMark T M) := by
    ext v
    simp only [Finset.mem_map, Count.mem_leafVertices, Function.Embedding.coeFn_mk,
      Finset.mem_union, Finset.mem_image, mem_otherLeaves, mem_folds]
    constructor
    · rintro ⟨v', hLeaf, rfl⟩
      have hK := card_kept_at T hc M (vIncl_mem v')
      have hL : ((GluingDatum.incidentEdges (vIncl v')).filter
          (KeptEdge (Keep T M))).card = 1 := by
        rw [← card_incidentEdges_restrict]; exact hLeaf
      rw [hL] at hK
      split_ifs at hK with hx
      · obtain ⟨j, hj⟩ := hx
        right
        exact ⟨j, by rw [hj]; omega, hj⟩
      · left
        exact ⟨vIncl_mem v', hx, by omega⟩
    · rintro (⟨hv, hx, h1⟩ | ⟨j, h2, rfl⟩)
      · refine ⟨vRestrict v hv, ?_, rfl⟩
        change (GluingDatum.incidentEdges (vRestrict (hKeep := Keep_nonempty T hc M) v hv)).card = 1
        have hK := card_kept_at T hc M hv
        rw [ite_neg' hx] at hK
        rw [card_incidentEdges_restrict]
        exact (show ((GluingDatum.incidentEdges v).filter (KeptEdge (Keep T M))).card = 1 by omega)
      · refine ⟨vRestrict (xMark T M j) (xMark_mem_Keep T hc M j), ?_, rfl⟩
        change (GluingDatum.incidentEdges (vRestrict (hKeep := Keep_nonempty T hc M) (xMark T M j)
          (xMark_mem_Keep T hc M j))).card = 1
        have hK := card_kept_at T hc M (xMark_mem_Keep T hc M j)
        rw [show (if xMark T M j ∈ Set.range (xMark T M) then 1 else 0) = 1 by simp] at hK
        rw [card_incidentEdges_restrict]
        exact (show ((GluingDatum.incidentEdges (xMark T M j)).filter
          (KeptEdge (Keep T M))).card = 1 by omega)
  have hDisj : Disjoint (otherLeaves T M) ((folds T M).image (xMark T M)) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hv'
    exact ((mem_otherLeaves T M).mp hv).2.1 ⟨j, rfl⟩
  rw [Count.leafCount, ← Finset.card_map ⟨vIncl, vIncl_injective⟩, hImage,
    Finset.card_union_of_disjoint hDisj,
    Finset.card_image_of_injective _ (xMark_injective T hc M)]

/-- The leaves of the tails. -/
def tailLeaf (q : Σ j, Fin (c j + 1)) : M.target.V := xLeaf T M q.1 q.2

theorem tailLeaf_injective : Function.Injective (tailLeaf T M) := by
  rintro ⟨j, i⟩ ⟨j', i'⟩ h
  have := tailVertex_injective T hc M (a₁ := ⟨j, Sum.inr (Sum.inr i)⟩)
    (a₂ := ⟨j', Sum.inr (Sum.inr i')⟩) h
  simp only [Sigma.mk.inj_iff] at this ⊢
  obtain ⟨rfl, h2⟩ := this
  simp only [heq_eq_eq, Sum.inr.injEq] at h2
  exact ⟨rfl, heq_of_eq h2⟩

/-- **The leaves of `T`**: the other kept leaves and the leaves of the tails, `Σⱼ (c j + 1)`. -/
theorem leafCount_target_eq :
    Count.leafCount M.target = (otherLeaves T M).card + ∑ j, (c j + 1) := by
  classical
  have hEq : Count.leafVertices M.target = otherLeaves T M ∪ Finset.univ.image (tailLeaf T M) := by
    ext v
    simp only [Count.mem_leafVertices, Finset.mem_union, mem_otherLeaves, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · intro hLeaf
      by_cases hv : v ∈ Keep T M
      · left
        refine ⟨hv, ?_, hLeaf⟩
        rintro ⟨j, rfl⟩
        have := two_le_val_xMark T hc M j
        have h1 : (GluingDatum.incidentEdges (xMark T M j)).card = 1 := hLeaf
        omega
      · right
        obtain ⟨⟨j, t⟩, rfl⟩ := exists_tailVertex_of_notMem T M hv
        rcases t with i | i | i
        · have := xSpine_trivalent T hc M j i
          have h1 : (GluingDatum.incidentEdges (xSpine T M j i)).card = 1 := hLeaf
          omega
        · have := xBulb_divalent T M j i
          have h1 : (GluingDatum.incidentEdges (xBulb T M j i)).card = 1 := hLeaf
          omega
        · exact ⟨⟨j, i⟩, rfl⟩
    · rintro (⟨-, -, h1⟩ | ⟨⟨j, i⟩, rfl⟩)
      · exact h1
      · exact xLeaf_isLeaf T M j i
  have hDisj : Disjoint (otherLeaves T M) (Finset.univ.image (tailLeaf T M)) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hv'
    exact xLeaf_notMem_Keep T M q.1 q.2 ((mem_otherLeaves T M).mp hv).1
  rw [Count.leafCount, hEq, Finset.card_union_of_disjoint hDisj,
    Finset.card_image_of_injective _ (tailLeaf_injective T hc M), Finset.card_univ,
    Fintype.card_sigma]
  simp

end Leaves

end

end DraismaVargas.Count.MarkedCountGeneral.TailRestrict
