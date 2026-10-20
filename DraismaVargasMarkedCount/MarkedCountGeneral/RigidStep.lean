module

public import DraismaVargasMarkedCount.MarkedCountGeneral.RigidLoop

@[expose] public section

/-!
# The step of the downward induction along a caterpillar tail

The rigidity of a caterpillar tail (module `Rigidity`) is proved by downward induction on `i` of
the statement `(I_i)`: the spine vertex `x_i` is trivalent, `B_i` is the only non-dangling vertex
over it, `r(B_i) = 0`, and the path edge `e_i` at `B_i` is the only survivor over its target edge.
This module is its step, a generic local lemma, in any full-dimensional datum. Let `B` be a branch
vertex (surviving valency `3`) carrying two survivors `E₁, E₂`, each the **only** survivor over its
target edge. Then (the case "(r0-nd3)" of the proof of `(I_i)`):

* the third survivor `E₃` at `B` lies over a third target edge, and `x = φ(B)` is trivalent with
  exactly these three edges (`spineStep_incidentEdges`);
* `r(B) = 0` (`spineStep_localRamification`);
* `B` is the only non-dangling vertex over `x` (`spineStep_unique_vertex`);
* `E₃` is the only survivor over its target edge (`spineStep_unique_edge`);
* `m(E₁) + m(E₂) + m(E₃) = 2 m(B) + 1` (`spineStep_index`).

The far end of `E₃` is then a branch vertex by `RestrictBridge.nonDanglingValency_ne_two_of_unique`
(Part I's column dependence), which covers all four cases (r2-nd2), (r1-nd2), (r0-nd2) of the
step at once, including the trivalent case excluded by the three-column relation.
-/

namespace DraismaVargas.Count.MarkedCountGeneral.SpineStep

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open scoped DraismaVargas.Infrastructure.GluingContraction

noncomputable section

variable {target : CFGraph.{0}} {d : ℕ} {data : GluingDatum target d}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (fd : FullDimensionalSourcePresentation data coordinate)

/-- The survivors at a source vertex. -/
def survivorsAt (data : GluingDatum target d) (B : data.SourceVertex) : Finset data.SourceEdge :=
  Finset.univ.filter fun F ↦ ¬ IsDangling data F ∧ Incident data F B

theorem mem_survivorsAt {B : data.SourceVertex} {F : data.SourceEdge} :
    F ∈ survivorsAt data B ↔ ¬ IsDangling data F ∧ Incident data F B := by
  simp [survivorsAt]

theorem card_survivorsAt (B : data.SourceVertex) :
    (survivorsAt data B).card = nonDanglingValency data B := by
  classical
  unfold survivorsAt nonDanglingValency
  congr 1
  ext F
  simp

/-- A survivor of a non-dangling vertex exists. -/
theorem exists_survivor {X : data.SourceVertex} (h : nonDanglingValency data X ≠ 0) :
    ∃ g, ¬ IsDangling data g ∧ Incident data g X := by
  by_contra hNo
  push Not at hNo
  exact h ((DanglingSideStructure.nonDanglingValency_eq_zero_iff data X).mpr
    fun g hg ↦ by by_contra hS; exact hNo g hS hg)

variable {B : data.SourceVertex} {E₁ E₂ : data.SourceEdge}

/-- The hypotheses of the step: a branch vertex with two lone survivors. -/
structure Hyp (data : GluingDatum target d) (B : data.SourceVertex) (E₁ E₂ : data.SourceEdge) :
    Prop where
  valency : nonDanglingValency data B = 3
  surv₁ : ¬ IsDangling data E₁
  surv₂ : ¬ IsDangling data E₂
  ne : E₁ ≠ E₂
  inc₁ : Incident data E₁ B
  inc₂ : Incident data E₂ B
  unique₁ : ∀ F, ¬ IsDangling data F → F.1.1 = E₁.1.1 → F = E₁
  unique₂ : ∀ F, ¬ IsDangling data F → F.1.1 = E₂.1.1 → F = E₂

variable (h : Hyp data B E₁ E₂)
include h

theorem target_ne₁₂ : E₁.1.1 ≠ E₂.1.1 := fun ht ↦ h.ne (h.unique₁ E₂ h.surv₂ ht.symm).symm

/-- **The third survivor.** -/
theorem exists_third : ∃ E₃, E₃ ∈ survivorsAt data B ∧ E₃ ≠ E₁ ∧ E₃ ≠ E₂ ∧
    ∀ F ∈ survivorsAt data B, F = E₁ ∨ F = E₂ ∨ F = E₃ := by
  classical
  have h1 : E₁ ∈ survivorsAt data B := mem_survivorsAt.mpr ⟨h.surv₁, h.inc₁⟩
  have h2 : E₂ ∈ survivorsAt data B := mem_survivorsAt.mpr ⟨h.surv₂, h.inc₂⟩
  have hCard := card_survivorsAt (data := data) B
  rw [h.valency] at hCard
  have h2' : E₂ ∈ (survivorsAt data B).erase E₁ := Finset.mem_erase.mpr ⟨h.ne.symm, h2⟩
  have hCard' : (((survivorsAt data B).erase E₁).erase E₂).card = 1 := by
    rw [Finset.card_erase_of_mem h2', Finset.card_erase_of_mem h1, hCard]
  obtain ⟨E₃, hE₃⟩ := Finset.card_eq_one.mp hCard'
  have hMem : E₃ ∈ ((survivorsAt data B).erase E₁).erase E₂ := by rw [hE₃]; simp
  simp only [Finset.mem_erase] at hMem
  refine ⟨E₃, hMem.2.2, hMem.2.1, hMem.1, fun F hF ↦ ?_⟩
  by_cases hF1 : F = E₁
  · exact Or.inl hF1
  by_cases hF2 : F = E₂
  · exact Or.inr (Or.inl hF2)
  have : F ∈ ((survivorsAt data B).erase E₁).erase E₂ := by
    simp only [Finset.mem_erase]; exact ⟨hF2, hF1, hF⟩
  rw [hE₃, Finset.mem_singleton] at this
  exact Or.inr (Or.inr this)

/-- The third survivor, chosen. -/
def third : data.SourceEdge := (exists_third h).choose

theorem third_mem : third h ∈ survivorsAt data B := (exists_third h).choose_spec.1
theorem third_survives : ¬ IsDangling data (third h) := (mem_survivorsAt.mp (third_mem h)).1
theorem third_incident : Incident data (third h) B := (mem_survivorsAt.mp (third_mem h)).2
theorem third_ne₁ : third h ≠ E₁ := (exists_third h).choose_spec.2.1
theorem third_ne₂ : third h ≠ E₂ := (exists_third h).choose_spec.2.2.1
theorem survivor_cases {F : data.SourceEdge} (hF : ¬ IsDangling data F) (hI : Incident data F B) :
    F = E₁ ∨ F = E₂ ∨ F = third h :=
  (exists_third h).choose_spec.2.2.2 F (mem_survivorsAt.mpr ⟨hF, hI⟩)

theorem target_ne₁₃ : E₁.1.1 ≠ (third h).1.1 := fun ht ↦
  third_ne₁ h (h.unique₁ _ (third_survives h) ht.symm)

theorem target_ne₂₃ : E₂.1.1 ≠ (third h).1.1 := fun ht ↦
  third_ne₂ h (h.unique₂ _ (third_survives h) ht.symm)

omit h in
theorem target_mem_of_incident {F : data.SourceEdge} {X : data.SourceVertex}
    (hI : Incident data F X) : F.1.1 ∈ GluingDatum.incidentEdges X.1.1 :=
  ((incident_iff_target_mem_and_rel data F X).mp hI).1

include fd in
/-- **`φ(B)` is trivalent, with exactly the three directions of the survivors.** -/
theorem spineStep_incidentEdges :
    GluingDatum.incidentEdges B.1.1 = {E₁.1.1, E₂.1.1, (third h).1.1} := by
  have hSub : ({E₁.1.1, E₂.1.1, (third h).1.1} : Finset target.edges) ⊆
      GluingDatum.incidentEdges B.1.1 := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact target_mem_of_incident h.inc₁
    · exact target_mem_of_incident h.inc₂
    · exact target_mem_of_incident (third_incident h)
  have h3 : ({E₁.1.1, E₂.1.1, (third h).1.1} : Finset target.edges).card = 3 :=
    Finset.card_eq_three.mpr ⟨_, _, _, target_ne₁₂ h, target_ne₁₃ h, target_ne₂₃ h, rfl⟩
  have hChange := data.targetChange_nonneg fd.valid B.1.1
  rw [IndexPattern.targetChange_eq_three_sub_valency fd] at hChange
  refine (Finset.eq_of_subset_of_card_le hSub ?_).symm
  rw [h3]
  omega

include fd in
theorem spineStep_trivalent : (GluingDatum.incidentEdges B.1.1).card = 3 := by
  rw [spineStep_incidentEdges fd h]
  exact Finset.card_eq_three.mpr ⟨_, _, _, target_ne₁₂ h, target_ne₁₃ h, target_ne₂₃ h, rfl⟩

include fd in
/-- **`r(B) = 0`.** -/
theorem spineStep_localRamification : data.localRamification B.1.1 ⟨B.1.2, B.2⟩ = 0 :=
  PassOnceLollipop.localRamification_eq_zero_of_trivalent fd (spineStep_trivalent fd h) _

include fd in
/-- **`B` is the only non-dangling vertex over `φ(B)`.** -/
theorem spineStep_unique_vertex {X : data.SourceVertex} (hX : X.1.1 = B.1.1)
    (hNd : nonDanglingValency data X ≠ 0) : X = B := by
  by_contra hXB
  have hNo : ∀ (E : data.SourceEdge), ¬ IsDangling data E →
      (∀ F, ¬ IsDangling data F → F.1.1 = E.1.1 → F = E) → Incident data E B →
      ∀ g, ¬ IsDangling data g → Incident data g X → g.1.1 ≠ E.1.1 := by
    intro E _ hU hEB g hg hgX hgE
    have := hU g hg hgE
    subst this
    exact hXB (LollipopBridgeFibre.eq_of_incident_of_target_eq hX hgX hEB)
  have hNo₁ := hNo E₁ h.surv₁ h.unique₁ h.inc₁
  have hNo₂ := hNo E₂ h.surv₂ h.unique₂ h.inc₂
  obtain ⟨g, hg, hgX⟩ := exists_survivor hNd
  have hTri : (GluingDatum.incidentEdges X.1.1).card = 3 := by
    rw [hX]; exact spineStep_trivalent fd h
  have ht₁ : E₁.1.1 ∈ GluingDatum.incidentEdges X.1.1 := by
    rw [hX]; exact target_mem_of_incident h.inc₁
  have hVal := PassOnceLollipop.nonDanglingValency_eq_two_of_survivor fd hTri ht₁
    (fun x hx hxI ↦ hNo₁ x hx hxI) hg hgX
  obtain ⟨g', ⟨hg'Ne, hg'S, hg'I⟩, -⟩ :=
    exists_unique_other_of_nonDanglingValency_eq_two data hVal hg hgX
  have hRam : data.localRamification X.1.1 ⟨X.1.2, X.2⟩ = 0 :=
    PassOnceLollipop.localRamification_eq_zero_of_trivalent fd hTri _
  have hT := RowWalk.target_ne_of_localRamification_le_one fd.danglingEdgeNoGlue hVal
    (by omega) hg hgX hg'S hg'I (Ne.symm hg'Ne)
  have hEdges := spineStep_incidentEdges fd h
  have hgT : g.1.1 = (third h).1.1 := by
    have hm := target_mem_of_incident hgX
    rw [hX, hEdges] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm | hm
    · exact absurd hm (hNo₁ g hg hgX)
    · exact absurd hm (hNo₂ g hg hgX)
    · exact hm
  have hg'T : g'.1.1 = (third h).1.1 := by
    have hm := target_mem_of_incident hg'I
    rw [hX, hEdges] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm | hm
    · exact absurd hm (hNo₁ g' hg'S hg'I)
    · exact absurd hm (hNo₂ g' hg'S hg'I)
    · exact hm
  exact hT (hgT.trans hg'T.symm)

include fd in
/-- **The third survivor is the only one over its target edge.** -/
theorem spineStep_unique_edge {F : data.SourceEdge} (hF : ¬ IsDangling data F)
    (hT : F.1.1 = (third h).1.1) : F = third h := by
  have hMem : F.1.1 ∈ GluingDatum.incidentEdges B.1.1 := by
    rw [hT]; exact target_mem_of_incident (third_incident h)
  set Y := data.sourceEndpoint B.1.1 F.1.2
  have hFY : Incident data F Y := by
    have := incident_sourceEdge_sourceEndpoint data B.1.1 F.1.1 hMem F.1.2
    rwa [GluingDatum.sourceEdge_self] at this
  have hY : Y = B := spineStep_unique_vertex fd h rfl
    (LollipopBridgeFibre.nonDanglingValency_pos_of_survivor hF hFY).ne'
  rw [hY] at hFY
  rcases survivor_cases h hF hFY with rfl | rfl | rfl
  · exact absurd hT (target_ne₁₃ h)
  · exact absurd hT (target_ne₂₃ h)
  · rfl

include fd in
/-- **The index relation** `m(E₁) + m(E₂) + m(E₃) = 2 m(B) + 1` (`r(B) = 0`, index form). -/
theorem spineStep_index :
    data.sourceEdgeIndex E₁ + data.sourceEdgeIndex E₂ + data.sourceEdgeIndex (third h) =
      2 * (data.vertexPartition B.1.1).blockCard B.1.2 + 1 := by
  classical
  have hForm := StableLocalProperties.localRamification_eq_index_form data B
  rw [spineStep_localRamification fd h] at hForm
  set i₁ : IncidentSourceEdge data B := ⟨E₁, h.inc₁⟩
  set i₂ : IncidentSourceEdge data B := ⟨E₂, h.inc₂⟩
  set i₃ : IncidentSourceEdge data B := ⟨third h, third_incident h⟩
  have h12 : i₁ ≠ i₂ := fun e ↦ h.ne (congrArg Subtype.val e)
  have h13 : i₁ ≠ i₃ := fun e ↦ third_ne₁ h (congrArg Subtype.val e).symm
  have h23 : i₂ ≠ i₃ := fun e ↦ third_ne₂ h (congrArg Subtype.val e).symm
  have hRestrict : (∑ item ∈ ({i₁, i₂, i₃} : Finset (IncidentSourceEdge data B)),
      ((data.sourceEdgeIndex item.1 : ℤ) - 1)) =
      ∑ item : IncidentSourceEdge data B, ((data.sourceEdgeIndex item.1 : ℤ) - 1) := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro x _ hx
    have hDang : IsDangling data x.1 := by
      by_contra hs
      rcases survivor_cases h hs x.2 with e | e | e
      · exact hx (by rw [show x = i₁ from Subtype.ext e]; simp)
      · exact hx (by rw [show x = i₂ from Subtype.ext e]; simp)
      · exact hx (by rw [show x = i₃ from Subtype.ext e]; simp)
    rw [fd.danglingEdgeNoGlue x.1 hDang]
    norm_num
  rw [← hRestrict, Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
    Finset.sum_singleton] at hForm
  have : (data.sourceEdgeIndex E₁ : ℤ) + data.sourceEdgeIndex E₂ +
      data.sourceEdgeIndex (third h) = 2 * ((data.vertexPartition B.1.1).blockCard B.1.2) + 1 := by
    change (0 : ℤ) = _ - (((data.sourceEdgeIndex E₁ : ℤ) - 1) + (((data.sourceEdgeIndex E₂ : ℤ) - 1) +
      ((data.sourceEdgeIndex (third h) : ℤ) - 1))) at hForm
    linarith
  exact_mod_cast this

include fd in
/-- **The far end of the third survivor is a branch vertex.** -/
theorem third_farEnd_valency {Y : data.SourceVertex} (hY : Incident data (third h) Y) :
    nonDanglingValency data Y = 3 := by
  have hne2 := MarkedCount.Lollipops.nonDanglingValency_ne_two_of_unique fd (third_survives h)
    (fun F hF hFt ↦ spineStep_unique_edge fd h hF hFt) hY
  have hpos := LollipopBridgeFibre.nonDanglingValency_pos_of_survivor (third_survives h) hY
  have hne1 := NonDanglingValency.nonDanglingValency_ne_one data fd.connected Y
  have hle := fd.trivalent Y
  omega

end

end DraismaVargas.Count.MarkedCountGeneral.SpineStep
