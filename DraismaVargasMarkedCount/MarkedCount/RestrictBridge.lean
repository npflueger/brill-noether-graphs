module

public import DraismaVargasMarkedCount.MarkedCount.RestrictLollipop

@[expose] public section

/-!
# The bridge of a lollipop joins its loop to the mark

The clause `h_b = ⟨w, e_b, u⟩` of the bridge-and-loop lemma (Draisma--Vargas Part I,
arXiv:1909.12924, `lemma-loop-bridge`): the far end of the bridge occurrence `e_b` is a branch
vertex (`LoopAt.nonDanglingValency_farEnd`, by Part I's column-dependence argument
`Lollipops.nonDanglingValency_ne_two_of_unique`), and the bridge slot of the lollipop core joins
`w_j` only to the mark, so the far end is the mark `u_j` (`farEnd_eq_markV`).
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

/-! ## 1.  The slots of the lollipop core -/

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

/-! ## 2.  The bridge joins `w` to `u` -/

section Member

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n}
  {y : Fin (p + (k + k)) → ℚ} (M : FibreMember (attachLollipops core mark) y degree)

/-- The stable path of the bridge. -/
def bridgePath (j : Fin k) : StablePath M.data :=
  NonDanglingEdge.stablePath (⟨bridgeE M j, bridgeE_survives M j⟩ : NonDanglingEdge M.data)

/-- **The bridge row is the bridge slot.** -/
theorem ident_row_bridgePath (j : Fin k) : M.ident.row (bridgePath M j) = bridgeSlot p j := by
  have h := LoopAt.coreIncidence_bridgePath_loopVertex M (hLoop j)
  rw [attachLollipops_tail_loop] at h
  exact (coreIncidence_lollipopVertex_pos core mark h).resolve_right
    (LoopAt.ident_row_bridgePath_ne M (hLoop j))

theorem bridgePath_eq (j : Fin k) : bridgePath M j = M.ident.row.symm (bridgeSlot p j) := by
  rw [← ident_row_bridgePath, Equiv.symm_apply_apply]

/-- The far end of the bridge, the end other than `w`. -/
def farEnd (j : Fin k) : M.data.SourceVertex := LoopAt.farEnd M (hLoop j)

/-- **The bridge-and-loop lemma, `h_b = ⟨w, e_b, u⟩`**: the far end of the bridge is the mark. -/
theorem farEnd_eq_markV (j : Fin k) : farEnd M j = markV M j := by
  have h := LoopAt.coreIncidence_bridgePath_farEnd M (hLoop j)
  change 0 < Count.coreIncidence _ _ (M.ident.row (bridgePath M j)) at h
  rw [ident_row_bridgePath] at h
  rcases coreIncidence_bridgeSlot_pos core mark h with h' | h'
  · have : (⟨farEnd M j, LoopAt.three_le_farEnd M (hLoop j)⟩ :
        StableGraphIncidence.BranchVertex M.data) = M.ident.vertex.symm (oldVertex k (mark j)) := by
      apply M.ident.vertex.injective
      rw [Equiv.apply_symm_apply]
      exact h'
    exact congrArg Subtype.val this
  · exact absurd (h'.trans (attachLollipops_tail_loop core mark j).symm)
      (LoopAt.ident_farEnd_ne_loopVertex M (hLoop j))

theorem bridgeE_incident_markV (j : Fin k) : Incident M.data (bridgeE M j) (markV M j) :=
  farEnd_eq_markV M j ▸ LoopAt.farEnd_incident M (hLoop j)

/-- The image of the mark is the image of the far end of the bridge. -/
theorem xV_eq (j : Fin k) : xV M j = LoopAt.xV M (hLoop j) :=
  congrArg (fun X : M.data.SourceVertex ↦ X.1.1) (farEnd_eq_markV M j).symm

/-- The two ends of the bridge: `w` and `u`. -/
theorem incident_bridgeE_iff (j : Fin k) (X : M.data.SourceVertex) :
    Incident M.data (bridgeE M j) X ↔ X = loopV M j ∨ X = markV M j := by
  rw [← farEnd_eq_markV]
  exact LoopAt.incident_bridgeE_iff M (hLoop j) X

theorem tb_mem_xV (j : Fin k) : tb M j ∈ GluingDatum.incidentEdges (xV M j) :=
  xV_eq M j ▸ LoopAt.tb_mem_xV M (hLoop j)

/-- The ends of `φ(e_b)` are `φ(u)` and `φ(w)`. -/
theorem tb_ends (j : Fin k) :
    ((tb M j : M.target.V × M.target.V).1 = xV M j ∧
        (tb M j : M.target.V × M.target.V).2 = uP M j) ∨
      ((tb M j : M.target.V × M.target.V).1 = uP M j ∧
        (tb M j : M.target.V × M.target.V).2 = xV M j) :=
  xV_eq M j ▸ LoopAt.tb_ends M (hLoop j)

end Member

end

end DraismaVargas.Count.MarkedCount.Lollipops
