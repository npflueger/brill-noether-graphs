module

public import DraismaVargasMarkedCount.MarkedCountGeneral.RegrowIso

@[expose] public section

/-!
# The inverse laws, part 1: adjusting a sheet permutation inside a block

Part of the two inverse laws of the decomposition (module `Correspondence`; compare the in-block
transpositions of `MarkedCount.CorrRegrowRestrict`). Groundwork for comparing two regrowths whose
tail chains differ: along a tail, the sheet permutation is corrected vertex by vertex, each time
inside one block (the regrowth does not depend on its choices, since each choice is a permutation
of sheets inside one block at one target vertex, extended along the far side of that vertex).

`adjust τ B A₁ A₂ a₁ a₂` is `τ` followed by a permutation supported in `B` that carries `τ A₁`
onto `A₂` and `τ a₁` to `a₂` (when `τ A₁ ⊆ B`, `A₂ ⊆ B`, `|A₁| = |A₂|`); otherwise it is `τ`.
Proved here: it agrees with `τ` wherever `τ` lands outside `B` (`adjust_out`), keeps `B`
(`adjust_mem_B`), carries `A₁` onto `A₂` (`adjust_map`) and `a₁` to `a₂` (`adjust_anchor`); and the
compatibility of two such permutations along an incidence (`rel_of_agree`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral.CatRegrow

open DraismaVargas.Infrastructure

section Adjust

variable {d : ℕ}

/-- The conditions under which `adjust` corrects `τ`. -/
def AdjustOK (τ : Equiv.Perm (Fin d)) (B A₁ A₂ : Finset (Fin d)) (a₁ a₂ : Fin d) : Prop :=
  (∀ q ∈ A₁, τ q ∈ B) ∧ A₂ ⊆ B ∧ A₁.card = A₂.card ∧ a₁ ∈ A₁ ∧ a₂ ∈ A₂

theorem exists_adjust {τ : Equiv.Perm (Fin d)} {B A₁ A₂ : Finset (Fin d)} {a₁ a₂ : Fin d}
    (h : AdjustOK τ B A₁ A₂ a₁ a₂) :
    ∃ ζ : Equiv.Perm (Fin d), (∀ q, q ∉ B → ζ q = q) ∧ (∀ q ∈ A₁, ζ (τ q) ∈ A₂) ∧
      ζ (τ a₁) = a₂ := by
  classical
  obtain ⟨h1, h2, hc, ha₁, ha₂⟩ := h
  let f : Fin A₁.card → Fin d := fun r ↦ τ (A₁.equivFin.symm r).1
  let g : Fin A₁.card → Fin d := fun r ↦ (A₂.equivFin.symm (Fin.cast hc r)).1
  have hf : Function.Injective f := fun r r' h ↦
    A₁.equivFin.symm.injective (Subtype.ext (τ.injective h))
  have hg : Function.Injective g := fun r r' h ↦
    Fin.cast_injective hc (A₂.equivFin.symm.injective (Subtype.ext h))
  obtain ⟨ζ₁, hζ₁, hζ₁B⟩ := exists_perm_extend B f g hf hg
    (fun r ↦ h1 _ (A₁.equivFin.symm r).2) (fun r ↦ h2 (A₂.equivFin.symm _).2)
  have hmem : ∀ q ∈ A₁, ζ₁ (τ q) ∈ A₂ := by
    intro q hq
    have := hζ₁ (A₁.equivFin ⟨q, hq⟩)
    simp only [f, g, Equiv.symm_apply_apply] at this
    rw [this]
    exact (A₂.equivFin.symm _).2
  refine ⟨ζ₁.trans (Equiv.swap (ζ₁ (τ a₁)) a₂), fun q hq ↦ ?_, fun q hq ↦ ?_, ?_⟩
  · rw [Equiv.trans_apply, hζ₁B q hq]
    have hne1 : q ≠ ζ₁ (τ a₁) := fun h' ↦ hq (h' ▸ h2 (hmem a₁ ha₁))
    have hne2 : q ≠ a₂ := fun h' ↦ hq (h' ▸ h2 ha₂)
    exact Equiv.swap_apply_of_ne_of_ne hne1 hne2
  · rw [Equiv.trans_apply]
    have hm := hmem q hq
    by_cases h' : ζ₁ (τ q) = ζ₁ (τ a₁)
    · rw [h', Equiv.swap_apply_left]; exact ha₂
    · by_cases h'' : ζ₁ (τ q) = a₂
      · rw [h'', Equiv.swap_apply_right]; exact hmem a₁ ha₁
      · rw [Equiv.swap_apply_of_ne_of_ne h' h'']; exact hm
  · rw [Equiv.trans_apply, Equiv.swap_apply_left]

/-- **Adjusting a permutation inside a block.** -/
noncomputable def adjust (τ : Equiv.Perm (Fin d)) (B A₁ A₂ : Finset (Fin d)) (a₁ a₂ : Fin d) :
    Equiv.Perm (Fin d) := by
  classical
  exact if h : AdjustOK τ B A₁ A₂ a₁ a₂ then τ.trans (exists_adjust h).choose else τ

variable {τ : Equiv.Perm (Fin d)} {B A₁ A₂ : Finset (Fin d)} {a₁ a₂ : Fin d}

theorem adjust_apply (h : AdjustOK τ B A₁ A₂ a₁ a₂) (q : Fin d) :
    adjust τ B A₁ A₂ a₁ a₂ q = (exists_adjust h).choose (τ q) := by
  classical
  unfold adjust
  rw [dite_eq_left h]
  rfl

theorem adjust_out (h : AdjustOK τ B A₁ A₂ a₁ a₂) {q : Fin d} (hq : τ q ∉ B) :
    adjust τ B A₁ A₂ a₁ a₂ q = τ q := by
  rw [adjust_apply h]
  exact (exists_adjust h).choose_spec.1 _ hq

/-- Wherever `τ` lands outside `B`, `adjust` is `τ` (whether or not the conditions hold). -/
theorem adjust_out' {q : Fin d} (hq : τ q ∉ B) : adjust τ B A₁ A₂ a₁ a₂ q = τ q := by
  classical
  by_cases h : AdjustOK τ B A₁ A₂ a₁ a₂
  · exact adjust_out h hq
  · unfold adjust; rw [dite_eq_right h]

theorem adjust_mem (h : AdjustOK τ B A₁ A₂ a₁ a₂) {q : Fin d} (hq : q ∈ A₁) :
    adjust τ B A₁ A₂ a₁ a₂ q ∈ A₂ := by
  rw [adjust_apply h]
  exact (exists_adjust h).choose_spec.2.1 q hq

theorem adjust_anchor (h : AdjustOK τ B A₁ A₂ a₁ a₂) : adjust τ B A₁ A₂ a₁ a₂ a₁ = a₂ := by
  rw [adjust_apply h]
  exact (exists_adjust h).choose_spec.2.2

theorem adjust_mem_B (h : AdjustOK τ B A₁ A₂ a₁ a₂) {q : Fin d} (hq : τ q ∈ B) :
    adjust τ B A₁ A₂ a₁ a₂ q ∈ B := by
  rw [adjust_apply h]
  exact perm_mem_of_mem (exists_adjust h).choose_spec.1 hq

theorem adjust_map (h : AdjustOK τ B A₁ A₂ a₁ a₂) :
    A₁.map (adjust τ B A₁ A₂ a₁ a₂).toEmbedding = A₂ := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro q hq
    obtain ⟨q', hq', rfl⟩ := Finset.mem_map.mp hq
    exact adjust_mem h hq'
  · rw [Finset.card_map, h.2.2.1]

/-- A permutation carrying `B₁` onto `B₂`, read on `B₂`. -/
theorem mem_iff_of_map {σ : Equiv.Perm (Fin d)} {B₁ B₂ : Finset (Fin d)}
    (h : B₁.map σ.toEmbedding = B₂) (q : Fin d) : σ q ∈ B₂ ↔ q ∈ B₁ := by
  rw [← h, Finset.mem_map_equiv, Equiv.symm_apply_apply]

/-- **Compatibility along an incidence**: two permutations carrying the block `B₁` of the vertex
onto `B₂`, and agreeing outside it, are compatible (`GeometricDatumIso.compatible`) for the
one-block partition. -/
theorem rel_of_agree {B₁ B₂ : Finset (Fin d)} {b : Fin d} (hb : Anchored B₁ b)
    {τv τe : Equiv.Perm (Fin d)} (hv : B₁.map τv.toEmbedding = B₂)
    (he : ∀ q, q ∈ B₁ → τe q ∈ B₂) (hout : ∀ q, q ∉ B₁ → τe q = τv q) (q : Fin d) :
    (blockPart B₁ b).Rel (τv.symm (τe q)) q := by
  rw [blockPart_rel_iff hb]
  by_cases hq : q ∈ B₁
  · right
    refine ⟨?_, hq⟩
    rw [← mem_iff_of_map hv, Equiv.apply_symm_apply]
    exact he q hq
  · left
    rw [hout q hq, Equiv.symm_apply_apply]

/-- A permutation carrying `A` into `B`, with `|A| = |B|`, carries `A` onto `B`. -/
theorem map_eq_of_maps {σ : Equiv.Perm (Fin d)} {A B : Finset (Fin d)} (h : ∀ q ∈ A, σ q ∈ B)
    (hc : A.card = B.card) : A.map σ.toEmbedding = B := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro q hq
    obtain ⟨q', hq', rfl⟩ := Finset.mem_map.mp hq
    exact h q' hq'
  · rw [Finset.card_map, hc]

/-- **Compatibility at the head of a slot**: the vertex permutation is the slot's, corrected
inside the vertex block. -/
theorem compat_head {B A : Finset (Fin d)} {a₁ a₂ b : Fin d} (hb : Anchored A b)
    (h : AdjustOK τ B A B a₁ a₂) (q : Fin d) :
    (blockPart A b).Rel ((adjust τ B A B a₁ a₂).symm (τ q)) q := by
  have hmap : A.map τ.toEmbedding = B := map_eq_of_maps h.1 h.2.2.1
  refine rel_of_agree hb (adjust_map h) (fun q hq ↦ h.1 q hq) (fun q hq ↦ ?_) q
  have : τ q ∉ B := by rw [mem_iff_of_map hmap]; exact hq
  exact (adjust_out h this).symm

/-- **Compatibility at the tail of a slot**: the slot permutation is the vertex's, corrected inside
the vertex block. -/
theorem compat_tailEnd {B₁ B₂ A₁ A₂ : Finset (Fin d)} {a₁ a₂ b : Fin d} (hb : Anchored B₁ b)
    (hv : B₁.map τ.toEmbedding = B₂) (q : Fin d) :
    (blockPart B₁ b).Rel (τ.symm (adjust τ B₂ A₁ A₂ a₁ a₂ q)) q := by
  classical
  refine rel_of_agree hb hv (fun q hq ↦ ?_) (fun q hq ↦ ?_) q
  · have hq' : τ q ∈ B₂ := (mem_iff_of_map hv q).mpr hq
    by_cases h : AdjustOK τ B₂ A₁ A₂ a₁ a₂
    · exact adjust_mem_B h hq'
    · unfold adjust; rw [dite_eq_right h]; exact hq'
  · exact adjust_out' (by rw [mem_iff_of_map hv]; exact hq)

end Adjust

end DraismaVargas.Count.MarkedCountGeneral.CatRegrow
