module

public import DraismaVargasMarkedCount.MarkedCount.RestrictBridge
public import DraismaVargasMarkedCount.MarkedCount.RestrictDatum

@[expose] public section

/-!
# The branches of all lollipops, and the kept target vertices

For a member `M` over the lollipop core, the deleted target vertices are
`Del M = {φ(w_j)} ∪ {φ(C_j)}`, the kept ones `Keep M = (Del M)ᶜ`.  This file proves that the
branches of distinct lollipops are disjoint, that the deleted target edges are exactly the
`tb j` and `tl j`, and that `restrictDatum` (module `RestrictDatum`) applies:

* the retraction `retract M` of the target (each branch to the image `φ(u_j)` of its mark),
  along which the deleted partitions refine;
* the deletion pattern (`deletionPattern`): a kept source vertex meets at most one deleted
  survivor, the bridge at a mark;
* the images `φ(u_j)` are distinct (`xV_injective`) and every one is divalent or trivalent;
* the block counts over the branch, for the genus.

Everything holds for any number `k` of lollipops.
-/

namespace DraismaVargas.Count.MarkedCount.Lollipops

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.RowWalk (OnRow)
open DraismaVargas.Count.MarkedCount.Restrict
open Utilities.Certificate.ExplicitPotential (Core)
open scoped DraismaVargas.Infrastructure.GluingContraction

noncomputable section

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n}
  {y : Fin (p + (k + k)) → ℚ} (M : FibreMember (attachLollipops core mark) y degree)

/-! ## 1.  Distinctness -/

theorem uP_injective : Function.Injective (uP M) := by
  intro i j h
  have := LollipopDivalent.loopImage_inj M (hLoop i) (hLoop j) h
  simp only [attachLollipops_tail_loop, lollipopVertex_inj] at this
  exact this

theorem vC_injective : Function.Injective (vC M) := by
  intro i j h
  exact loopSlot_injective (LollipopLeafRow.loopLeaf_inj M (hLoop i) (hLoop j) h)

theorem uP_ne_vC (i j : Fin k) : uP M i ≠ vC M j := by
  intro h
  have h1 := uP_divalent M i
  have h2 : (GluingDatum.incidentEdges (vC M j)).card = 1 := vC_isLeaf M j
  rw [h] at h1
  omega

theorem xV_ne_uP' (i j : Fin k) : xV M i ≠ uP M j := by
  intro h
  have := nonDanglingValency_over_uP M (j := j) (X := markV M i) h
    (fun h' ↦ loopV_ne_markV M j i h'.symm)
  have := nonDanglingValency_markV M i
  omega

theorem xV_ne_vC (i j : Fin k) : xV M i ≠ vC M j := by
  intro h
  have := nonDanglingValency_over_vC M (j := j) (X := markV M i) h
  have := nonDanglingValency_markV M i
  omega

/-- The ends of the leaf edge `tl j` are `uP j` and `vC j`. -/
theorem tl_ends (j : Fin k) :
    ((tl M j : M.target.V × M.target.V).1 = uP M j ∧
        (tl M j : M.target.V × M.target.V).2 = vC M j) ∨
      ((tl M j : M.target.V × M.target.V).1 = vC M j ∧
        (tl M j : M.target.V × M.target.V).2 = uP M j) :=
  LoopAt.tl_ends M (hLoop j)

theorem tb_injective : Function.Injective (tb M) := by
  intro i j h
  have hE : bridgeE M i = bridgeE M j := eq_bridgeE M (bridgeE_survives M i) h
  have hInc := bridgeE_incident_loopV M i
  rw [hE, incident_bridgeE_iff] at hInc
  rcases hInc with h' | h'
  · exact loopV_injective M h'
  · exact absurd h' (loopV_ne_markV M i j)

theorem tl_injective : Function.Injective (tl M) := by
  intro i j h
  rcases tl_ends M i with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases tl_ends M j with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
    rw [h] at a1 a2
  · exact vC_injective M (a2.symm.trans b2)
  · exact absurd (b1.symm.trans a1) (uP_ne_vC M i j).symm
  · exact absurd (a1.symm.trans b1) (uP_ne_vC M j i).symm
  · exact vC_injective M (a1.symm.trans b1)

theorem tb_ne_tl' (i j : Fin k) : tb M i ≠ tl M j := by
  intro h
  rcases tb_ends M i with ⟨hx, -⟩ | ⟨-, hx⟩ <;> rw [h] at hx <;>
    rcases tl_ends M j with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact xV_ne_uP' M i j (hx.symm.trans h1)
  · exact xV_ne_vC M i j (hx.symm.trans h1)
  · exact xV_ne_vC M i j (hx.symm.trans h2)
  · exact xV_ne_uP' M i j (hx.symm.trans h2)

/-! ## 2.  The deleted target vertices -/

/-- The deleted target vertices `{φ(w_j)} ∪ {φ(C_j)}`. -/
def Del : Finset M.target.V := Finset.univ.image (uP M) ∪ Finset.univ.image (vC M)

/-- The kept target vertices. -/
def Keep : Finset M.target.V := (Del M)ᶜ

theorem mem_Del {v : M.target.V} : v ∈ Del M ↔ (∃ j, uP M j = v) ∨ ∃ j, vC M j = v := by
  simp [Del]

theorem mem_Keep {v : M.target.V} : v ∈ Keep M ↔ v ∉ Del M := Finset.mem_compl

theorem uP_notMem_Keep (j : Fin k) : uP M j ∉ Keep M := by
  rw [mem_Keep, not_not, mem_Del]; exact Or.inl ⟨j, rfl⟩

theorem vC_notMem_Keep (j : Fin k) : vC M j ∉ Keep M := by
  rw [mem_Keep, not_not, mem_Del]; exact Or.inr ⟨j, rfl⟩

theorem xV_mem_Keep (j : Fin k) : xV M j ∈ Keep M := by
  rw [mem_Keep, mem_Del]
  rintro (⟨i, hi⟩ | ⟨i, hi⟩)
  · exact xV_ne_uP' M j i hi.symm
  · exact xV_ne_vC M j i hi.symm

theorem Keep_nonempty : (Keep M).Nonempty := by
  by_cases hk : Nonempty (Fin k)
  · obtain ⟨j⟩ := hk
    exact ⟨xV M j, xV_mem_Keep M j⟩
  · rw [not_nonempty_iff] at hk
    obtain ⟨v⟩ := M.target.instNonempty
    refine ⟨v, (mem_Keep M).mpr ?_⟩
    rw [mem_Del]
    rintro (⟨i, -⟩ | ⟨i, -⟩) <;> exact hk.elim i

/-- **The deleted target edges are the `tb j` and the `tl j`.** -/
theorem not_keptEdge_iff (e : M.target.edges) :
    ¬ KeptEdge (Keep M) e ↔ (∃ j, e = tb M j) ∨ ∃ j, e = tl M j := by
  constructor
  · intro h
    have hEnd : ∃ v, v ∈ Del M ∧ e ∈ GluingDatum.incidentEdges v := by
      unfold KeptEdge at h
      rw [not_and_or] at h
      rcases h with h | h
      · refine ⟨_, by rwa [mem_Keep, not_not] at h, ?_⟩
        simp [GluingDatum.incidentEdges]
      · refine ⟨_, by rwa [mem_Keep, not_not] at h, ?_⟩
        simp [GluingDatum.incidentEdges]
    obtain ⟨v, hv, he⟩ := hEnd
    rcases (mem_Del M).mp hv with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [incidentEdges_uP] at he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact Or.inl ⟨j, rfl⟩
      · exact Or.inr ⟨j, rfl⟩
    · rw [incidentEdges_vC, Finset.mem_singleton] at he
      exact Or.inr ⟨j, he⟩
  · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩) ⟨h1, h2⟩
    · rcases tb_ends M j with ⟨-, h⟩ | ⟨h, -⟩
      · rw [h] at h2; exact uP_notMem_Keep M j h2
      · rw [h] at h1; exact uP_notMem_Keep M j h1
    · rcases tl_ends M j with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h] at h1; exact uP_notMem_Keep M j h1
      · rw [h] at h1; exact vC_notMem_Keep M j h1

/-! ## 3.  The partitions over a branch refine the one at the mark -/

theorem refines_uP_xV (j : Fin k) :
    (M.data.vertexPartition (uP M j)).Refines (M.data.vertexPartition (xV M j)) :=
  xV_eq M j ▸ LoopAt.refines_uP_xV M (hLoop j)

theorem refines_vC_uP (j : Fin k) :
    (M.data.vertexPartition (vC M j)).Refines (M.data.vertexPartition (uP M j)) :=
  LoopAt.refines_vC_uP M (hLoop j)

/-! ## 4.  The retraction of the target -/

theorem exists_branch_of_notMem_Keep {v : M.target.V} (h : v ∉ Keep M) :
    ∃ j, uP M j = v ∨ vC M j = v := by
  rw [mem_Keep, not_not, mem_Del] at h
  rcases h with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact ⟨j, Or.inl hj⟩
  · exact ⟨j, Or.inr hj⟩

/-- The lollipop whose branch contains a deleted target vertex. -/
def branchOf {v : M.target.V} (h : v ∉ Keep M) : Fin k :=
  (exists_branch_of_notMem_Keep M h).choose

theorem branchOf_uP (j : Fin k) : branchOf M (uP_notMem_Keep M j) = j := by
  rcases (exists_branch_of_notMem_Keep M (uP_notMem_Keep M j)).choose_spec with h | h
  · exact uP_injective M h
  · exact absurd h.symm (uP_ne_vC M _ _)

theorem branchOf_vC (j : Fin k) : branchOf M (vC_notMem_Keep M j) = j := by
  rcases (exists_branch_of_notMem_Keep M (vC_notMem_Keep M j)).choose_spec with h | h
  · exact absurd h (uP_ne_vC M _ _)
  · exact vC_injective M h

/-- **The retraction**: the branch of lollipop `j` goes to `φ(u_j)`. -/
def retract (v : M.target.V) : (restrictTarget (Keep M) (Keep_nonempty M)).V :=
  if h : v ∈ Keep M then vRestrict v h else vRestrict (xV M (branchOf M h)) (xV_mem_Keep M _)

theorem retract_of_mem {v : M.target.V} (h : v ∈ Keep M) : retract M v = vRestrict v h :=
  by simp only [retract, h, ↓reduceDIte]

theorem retract_uP (j : Fin k) : retract M (uP M j) = vRestrict (xV M j) (xV_mem_Keep M j) := by
  simp only [retract, uP_notMem_Keep M j, ↓reduceDIte]
  congr 1
  rw [branchOf_uP]

theorem retract_vC (j : Fin k) : retract M (vC M j) = vRestrict (xV M j) (xV_mem_Keep M j) := by
  simp only [retract, vC_notMem_Keep M j, ↓reduceDIte]
  congr 1
  rw [branchOf_vC]

theorem retract_edge (e : M.target.edges) (he : ¬ KeptEdge (Keep M) e) :
    retract M (e : M.target.V × M.target.V).1 = retract M (e : M.target.V × M.target.V).2 := by
  rcases (not_keptEdge_iff M e).mp he with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rcases tb_ends M j with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2, retract_uP,
      retract_of_mem M (xV_mem_Keep M j)]
  · rcases tl_ends M j with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2, retract_uP, retract_vC]

theorem retract_refines (v : M.target.V) (hv : v ∉ Keep M) :
    (M.data.vertexPartition v).Refines (M.data.vertexPartition (vIncl (retract M v))) := by
  obtain ⟨j, hj | hj⟩ := exists_branch_of_notMem_Keep M hv <;> subst hj
  · rw [retract_uP, vIncl_vRestrict]; exact refines_uP_xV M j
  · rw [retract_vC, vIncl_vRestrict]; exact (refines_vC_uP M j).trans (refines_uP_xV M j)

/-! ## 5.  The deleted survivors at kept vertices -/

/-- A deleted target edge at a kept vertex is the bridge image of a lollipop at that vertex. -/
theorem eq_tb_of_mem_incidentEdges {v : M.target.V} (hv : v ∈ Keep M) {e : M.target.edges}
    (he : e ∈ GluingDatum.incidentEdges v) (hk : ¬ KeptEdge (Keep M) e) :
    ∃ j, e = tb M j ∧ xV M j = v := by
  have hEnds := Count.fst_eq_or_snd_eq_of_mem_incidentEdges he
  rcases (not_keptEdge_iff M e).mp hk with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · refine ⟨j, rfl, ?_⟩
    rcases tb_ends M j with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hEnds with h | h
    · exact h1.symm.trans h
    · exact absurd (h2.symm.trans h ▸ hv) (uP_notMem_Keep M j)
    · exact absurd (h1.symm.trans h ▸ hv) (uP_notMem_Keep M j)
    · exact h2.symm.trans h
  · exfalso
    rcases tl_ends M j with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hEnds with h | h
    · exact uP_notMem_Keep M j (h1.symm.trans h ▸ hv)
    · exact vC_notMem_Keep M j (h2.symm.trans h ▸ hv)
    · exact vC_notMem_Keep M j (h1.symm.trans h ▸ hv)
    · exact uP_notMem_Keep M j (h2.symm.trans h ▸ hv)

/-- The deleted survivors: survivors over deleted target edges. -/
def Lol (E : M.data.SourceEdge) : Prop :=
  ¬ IsDangling M.data E ∧ ¬ KeptEdge (Keep M) E.1.1

/-- **A deleted survivor at a kept vertex is the bridge at a mark.** -/
theorem eq_bridgeE_of_lol {X : M.data.SourceVertex} (hX : X.1.1 ∈ Keep M) {E : M.data.SourceEdge}
    (hE : Lol M E) (hInc : Incident M.data E X) : ∃ j, E = bridgeE M j ∧ X = markV M j := by
  have hMem := ((incident_iff_target_mem_and_rel M.data E X).mp hInc).1
  obtain ⟨j, hj, -⟩ := eq_tb_of_mem_incidentEdges M hX hMem hE.2
  have hEq := eq_bridgeE M hE.1 hj
  subst hEq
  refine ⟨j, rfl, ?_⟩
  rcases (incident_bridgeE_iff M j X).mp hInc with h | h
  · subst h; exact absurd hX (uP_notMem_Keep M j)
  · exact h

open GenusSixExistence.Tripod.Gluing (wCount) in
theorem wCount_lol_markV (hc : IsMarkedCubic core mark) (j : Fin k) :
    wCount M.data (Lol M) (markV M j) = 1 := by
  classical
  unfold wCount
  rw [Finset.card_eq_one]
  refine ⟨bridgeE M j, ?_⟩
  ext E
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨hE, hInc⟩
    obtain ⟨i, rfl, hi⟩ := eq_bridgeE_of_lol M (xV_mem_Keep M j) hE hInc
    rw [markV_injective M hc hi]
  · rintro rfl
    refine ⟨⟨bridgeE_survives M j, ?_⟩, bridgeE_incident_markV M j⟩
    rw [not_keptEdge_iff]
    exact Or.inl ⟨j, rfl⟩

open GenusSixExistence.Tripod.Gluing (wCount) in
theorem wCount_lol_eq_zero {X : M.data.SourceVertex} (hX : X.1.1 ∈ Keep M)
    (hne : ∀ j, markV M j ≠ X) : wCount M.data (Lol M) X = 0 := by
  classical
  unfold wCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_of_forall_notMem
  intro E hE
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hE
  obtain ⟨j, -, hj⟩ := eq_bridgeE_of_lol M hX hE.1 hE.2
  exact hne j hj.symm

/-- **The deletion pattern of the lollipops.** -/
theorem deletionPattern (hc : IsMarkedCubic core mark) :
    DeletionPattern (Keep M) M.data (Lol M) where
  lol_iff _ := Iff.rfl
  kept X hX := by
    by_cases h : ∃ j, markV M j = X
    · obtain ⟨j, rfl⟩ := h
      exact Or.inr ⟨wCount_lol_markV M hc j, nonDanglingValency_markV M j⟩
    · push Not at h
      exact Or.inl (wCount_lol_eq_zero M hX h)
  deleted X hX := by
    have hAll : GenusSixExistence.Tripod.Gluing.wCount M.data (Lol M) X =
        nonDanglingValency M.data X := by
      rw [GenusSixExistence.Tripod.Gluing.nonDanglingValency_eq_wCount]
      apply GenusSixExistence.Tripod.Gluing.wCount_congr
      intro E hE
      refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun hk ↦ hX (target_mem_of_incident hk hE)⟩⟩
    rw [hAll]
    exact NonDanglingValency.nonDanglingValency_ne_one M.data M.fullDim.connected X

/-! ## 6.  The images of the marks -/

/-- The local ramification at a mark is at most the change at its image. -/
theorem valency_xV (j : Fin k) :
    (GluingDatum.incidentEdges (xV M j)).card = 2 ∨
      (GluingDatum.incidentEdges (xV M j)).card = 3 := by
  have hLe := IndexPattern.localRamification_le_targetChange M.fullDim (wall := xV M j)
    ⟨(markV M j).1.2, (markV M j).2⟩
  rw [IndexPattern.targetChange_eq_three_sub_valency M.fullDim] at hLe
  have hNonneg := M.data.localRamification_nonneg (xV M j) (M.fullDim.valid.2 _)
    ⟨(markV M j).1.2, (markV M j).2⟩
  have hPos := StableLocalProperties.incidentEdges_card_pos_of_changeMinimalAt M.data (xV M j)
    (M.fullDim.changeMinimal _)
  have hNotLeaf : (GluingDatum.incidentEdges (xV M j)).card ≠ 1 := by
    intro hCard
    have hLeaf : Count.IsLeafVertex M.target (markV M j).1.1 := hCard
    have hCore := LollipopDivalentWitness.eq_coreVertex_of_surviving M.fullDim
      (by have := nonDanglingValency_markV M j; omega) hLeaf
    have hTwo := LeafFibre.nonDanglingValency_coreVertex M.fullDim hLeaf
    rw [← hCore, nonDanglingValency_markV] at hTwo
    omega
  omega

/-- **Fold or transition**: `r(u) = 1` exactly when `φ(u)` is divalent, and
otherwise `r(u) = 0` and `φ(u)` is trivalent. -/
theorem markRamification_eq_one_iff (j : Fin k) :
    M.data.localRamification (xV M j) ⟨(markV M j).1.2, (markV M j).2⟩ = 1 ↔
      (GluingDatum.incidentEdges (xV M j)).card = 2 := by
  have hLe := IndexPattern.localRamification_le_targetChange M.fullDim (wall := xV M j)
    ⟨(markV M j).1.2, (markV M j).2⟩
  rw [IndexPattern.targetChange_eq_three_sub_valency M.fullDim] at hLe
  have hNonneg := M.data.localRamification_nonneg (xV M j) (M.fullDim.valid.2 _)
    ⟨(markV M j).1.2, (markV M j).2⟩
  rcases valency_xV M j with h | h
  · have h1 : 1 ≤ M.data.localRamification (xV M j) ⟨(markV M j).1.2, (markV M j).2⟩ :=
      LollipopDivalent.one_le_localRamification_of_three_le_of_divalent
        (data := M.data) (three_le_markV M j) h
    constructor
    · intro; exact h
    · intro; rw [h] at hLe; omega
  · rw [h] at hLe
    constructor
    · intro h1; omega
    · intro h2; omega

/-- **Distinct marks have distinct images.**  Two marks over one target vertex `x` would make
`x` trivalent (two bridge images and the image of the germs), so both marks unramified; but
the two germs at a mark then share the third direction. -/
theorem xV_injective (hc : IsMarkedCubic core mark) : Function.Injective (xV M) := by
  classical
  intro i j hij
  by_contra hne
  set x := xV M i
  have hti := tb_mem_xV M i
  have htj : tb M j ∈ GluingDatum.incidentEdges x := by rw [show x = xV M j from hij]; exact tb_mem_xV M j
  have htij : tb M i ≠ tb M j := fun h ↦ hne (tb_injective M h)
  -- the survivors at `u_i`
  set S := (Finset.univ : Finset M.data.SourceEdge).filter
    (fun E ↦ ¬ IsDangling M.data E ∧ Incident M.data E (markV M i)) with hS
  have hScard : S.card = 3 := by
    rw [← nonDanglingValency_markV M i, nonDanglingValency]
    congr 1
    ext E
    simp [hS]
  have hbS : bridgeE M i ∈ S := by
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨bridgeE_survives M i, bridgeE_incident_markV M i⟩
  obtain ⟨g₁, g₂, hg, hpair⟩ := Finset.card_eq_two.mp
    (show (S.erase (bridgeE M i)).card = 2 by rw [Finset.card_erase_of_mem hbS, hScard])
  have hmem : ∀ g, g ∈ S.erase (bridgeE M i) →
      g ≠ bridgeE M i ∧ ¬ IsDangling M.data g ∧ Incident M.data g (markV M i) := by
    intro g hg'
    obtain ⟨hgne, hgS⟩ := Finset.mem_erase.mp hg'
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hgS
    exact ⟨hgne, hgS⟩
  have h₁ := hmem g₁ (by rw [hpair]; simp)
  have h₂ := hmem g₂ (by rw [hpair]; simp)
  -- the germs avoid both bridge images
  have hAvoid : ∀ g, g ≠ bridgeE M i → ¬ IsDangling M.data g → Incident M.data g (markV M i) →
      g.1.1 ∈ ((GluingDatum.incidentEdges x).erase (tb M i)).erase (tb M j) := by
    intro g hgne hgS hgI
    have hgMem := ((incident_iff_target_mem_and_rel M.data g _).mp hgI).1
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hgMem⟩⟩
    · intro hgt
      have := eq_bridgeE M hgS hgt
      subst this
      rcases (incident_bridgeE_iff M j _).mp hgI with h | h
      · exact loopV_ne_markV M j i h.symm
      · exact hne (markV_injective M hc h)
    · intro hgt
      exact hgne (eq_bridgeE M hgS hgt)
  have hA₁ := hAvoid g₁ h₁.1 h₁.2.1 h₁.2.2
  have hA₂ := hAvoid g₂ h₂.1 h₂.2.1 h₂.2.2
  -- valency of `x`
  have hVal3 : (GluingDatum.incidentEdges x).card = 3 := by
    have h4 : 1 ≤ (((GluingDatum.incidentEdges x).erase (tb M i)).erase (tb M j)).card :=
      Finset.card_pos.mpr ⟨_, hA₁⟩
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨htij.symm, htj⟩),
      Finset.card_erase_of_mem hti] at h4
    rcases valency_xV M i with h | h <;> omega
  have hOne : (((GluingDatum.incidentEdges x).erase (tb M i)).erase (tb M j)).card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨htij.symm, htj⟩),
      Finset.card_erase_of_mem hti, hVal3]
  have hShare : g₁.1.1 = g₂.1.1 := Finset.card_le_one.mp hOne.le _ hA₁ _ hA₂
  have hRam := PassOnceLollipop.localRamification_eq_zero_of_trivalent M.fullDim hVal3
    ⟨(markV M i).1.2, (markV M i).2⟩
  exact PassOnceLollipop.not_three_survivors_sharing_direction M.fullDim hRam
    (nonDanglingValency_markV M i) hg h₁.1 h₂.1 h₁.2.1 h₁.2.2 h₂.2.1 h₂.2.2
    (bridgeE_survives M i) (bridgeE_incident_markV M i) hShare

/-! ## 7.  Block counts over the branch -/

theorem card_blocks_uP (j : Fin k) :
    Fintype.card (M.data.vertexPartition (uP M j)).Blocks + 1 = degree :=
  LoopAt.card_blocks_uP M (hLoop j)

theorem card_blocks_vC (j : Fin k) :
    Fintype.card (M.data.vertexPartition (vC M j)).Blocks + 1 = degree :=
  LoopAt.card_blocks_vC M (hLoop j)

theorem card_blocks_tb (j : Fin k) :
    Fintype.card (M.data.edgePartition (tb M j)).Blocks + 1 = degree :=
  LoopAt.card_blocks_tb M (hLoop j)

theorem card_blocks_tl (j : Fin k) :
    Fintype.card (M.data.edgePartition (tl M j)).Blocks = degree :=
  LoopAt.card_blocks_tl M (hLoop j)

/-! ## 8.  Sums over the branches -/

theorem sum_Del {β : Type*} [AddCommMonoid β] (g : M.target.V → β) :
    ∑ v ∈ (Keep M)ᶜ, g v = ∑ j, (g (uP M j) + g (vC M j)) := by
  classical
  have hK : (Keep M)ᶜ = Del M := by rw [Keep, compl_compl]
  rw [hK, Del, Finset.sum_union, Finset.sum_image (fun i _ j _ h ↦ uP_injective M h),
    Finset.sum_image (fun i _ j _ h ↦ vC_injective M h), Finset.sum_add_distrib]
  rw [Finset.disjoint_left]
  intro v hv hv'
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨j, -, h⟩ := Finset.mem_image.mp hv'
  exact uP_ne_vC M i j h.symm

theorem sum_notKept {β : Type*} [AddCommMonoid β] (g : M.target.edges → β) :
    ∑ e ∈ Finset.univ.filter (fun e ↦ ¬ KeptEdge (Keep M) e), g e =
      ∑ j, (g (tb M j) + g (tl M j)) := by
  classical
  have hF : Finset.univ.filter (fun e ↦ ¬ KeptEdge (Keep M) e) =
      Finset.univ.image (tb M) ∪ Finset.univ.image (tl M) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_keptEdge_iff, Finset.mem_union,
      Finset.mem_image]
    constructor
    · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
      · exact Or.inl ⟨j, rfl⟩
      · exact Or.inr ⟨j, rfl⟩
    · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
      · exact Or.inl ⟨j, rfl⟩
      · exact Or.inr ⟨j, rfl⟩
  rw [hF, Finset.sum_union, Finset.sum_image (fun i _ j _ h ↦ tb_injective M h),
    Finset.sum_image (fun i _ j _ h ↦ tl_injective M h), Finset.sum_add_distrib]
  rw [Finset.disjoint_left]
  intro v hv hv'
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨j, -, h⟩ := Finset.mem_image.mp hv'
  exact tb_ne_tl' M i j h.symm

theorem card_Del : ((Keep M)ᶜ).card = k + k := by
  rw [Finset.card_eq_sum_ones, sum_Del]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

theorem card_notKept :
    (Finset.univ.filter (fun e ↦ ¬ KeptEdge (Keep M) e)).card = k + k := by
  rw [Finset.card_eq_sum_ones, sum_notKept]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

/-- The blocks over the deleted vertices and edges: `2k(d-1)` and `k(d-1) + kd`. -/
theorem sum_blocks_Del :
    ∑ v ∈ (Keep M)ᶜ, Fintype.card (M.data.vertexPartition v).Blocks + (k + k) =
      k * degree + k * degree := by
  rw [sum_Del]
  have hs : ∑ j : Fin k, (Fintype.card (M.data.vertexPartition (uP M j)).Blocks +
      Fintype.card (M.data.vertexPartition (vC M j)).Blocks + 2) =
      ∑ _j : Fin k, (degree + degree) :=
    Finset.sum_congr rfl fun j _ ↦ by
      have h1 := card_blocks_uP M j
      have h2 := card_blocks_vC M j
      omega
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hs ⊢
  linarith

theorem sum_blocks_notKept :
    ∑ e ∈ Finset.univ.filter (fun e ↦ ¬ KeptEdge (Keep M) e),
        Fintype.card (M.data.edgePartition e).Blocks + k =
      k * degree + k * degree := by
  rw [sum_notKept]
  have hs : ∑ j : Fin k, (Fintype.card (M.data.edgePartition (tb M j)).Blocks +
      Fintype.card (M.data.edgePartition (tl M j)).Blocks + 1) =
      ∑ _j : Fin k, (degree + degree) :=
    Finset.sum_congr rfl fun j _ ↦ by
      have h1 := card_blocks_tb M j
      have h2 := card_blocks_tl M j
      omega
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hs ⊢
  linarith

/-! ## 9.  The deleted occurrences at a mark -/

/-- At `u_j`, the deleted occurrences are those over `φ(e_b)`; they add `1` to the index sum:
`e_b` has index two and the others are dangling. -/
theorem sum_deleted_index_markV (hc : IsMarkedCubic core mark) (j : Fin k) :
    ∑ E ∈ Finset.univ.filter
        (fun E : M.data.SourceEdge ↦ Incident M.data E (markV M j) ∧ ¬ KeptEdge (Keep M) E.1.1),
      ((M.data.sourceEdgeIndex E : ℤ) - 1) = 1 := by
  classical
  rw [Finset.sum_eq_single (bridgeE M j)]
  · rw [bridgeE_index]; norm_num
  · intro E hE hne
    obtain ⟨hInc, hk⟩ := (Finset.mem_filter.mp hE).2
    have hMem := ((incident_iff_target_mem_and_rel M.data E _).mp hInc).1
    obtain ⟨i, hi, hx⟩ := eq_tb_of_mem_incidentEdges M (xV_mem_Keep M j) hMem hk
    have hij : i = j := xV_injective M hc hx
    subst hij
    have hD : IsDangling M.data E := by
      by_contra hS
      exact hne (eq_bridgeE M hS hi)
    rw [M.fullDim.danglingEdgeNoGlue E hD]
    norm_num
  · intro h
    exfalso
    apply h
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, bridgeE_incident_markV M j, ?_⟩
    rw [not_keptEdge_iff]
    exact Or.inl ⟨j, rfl⟩

end

end DraismaVargas.Count.MarkedCount.Lollipops
