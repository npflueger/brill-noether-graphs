module

public import DraismaVargasMarkedCount.MarkedCountGeneral.RigidSpine

@[expose] public section

/-!
# The tail columns of a caterpillar tail (rigidity (5), module `Rigidity`)

For a caterpillar tail `C` in a cubic core and a member `M`, every tail slot `s` has a **tail
column** `tcol s` (the target edge of its lone survivor for a path edge or a bridge, the leaf edge
for a loop), and the tail rows are private:

* `onRow_of_over_tcol`: every survivor over `tcol s` lies on the row of `s`;
* `over_tcol_of_onRow`: every survivor on the row of `s` lies over `tcol s`;
* `tcol_injective`.
-/

namespace DraismaVargas.Count.MarkedCountGeneral.TailAt

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open Utilities.Certificate.ExplicitPotential (Core)
open CatSlot
open scoped DraismaVargas.Infrastructure.GluingContraction

noncomputable section

variable {N P degree : ℕ} {H : Core N P} {w : Fin N} {c : ℕ} {y : Fin P → ℚ}
  (C : CaterpillarAt H w c) (M : FibreMember H y degree) (hH : H.Cubic)

/-- **The tail column** of a tail slot. -/
def tcol : CatSlot c → M.target.edges
  | Sum.inl i => (pathE C M hH i).1.1.1
  | Sum.inr (Sum.inl i) => (bridgeAt C M i.castSucc).1.1.1
  | Sum.inr (Sum.inr i) => LoopAt.tl M (C.isLoop i)

theorem loopRow_eq (i : Fin (c + 1)) :
    LoopAt.loopRow M (C.slot (Sum.inr (Sum.inr i))) = row C M (Sum.inr (Sum.inr i)) := rfl

/-- **Every survivor over a tail column lies on its row.** -/
theorem onRow_of_over_tcol (s : CatSlot c) {F : M.data.SourceEdge} (hF : ¬ IsDangling M.data F)
    (hT : F.1.1 = tcol C M hH s) :
    NonDanglingEdge.stablePath (⟨F, hF⟩ : NonDanglingEdge M.data) = row C M s := by
  rcases s with i | i | i
  · have h := (lone_pathE C M hH i).2 F hF hT
    have : (⟨F, hF⟩ : NonDanglingEdge M.data) = pathE C M hH i := Subtype.ext h
    rw [this]; exact (lone_pathE C M hH i).stablePath
  · have h := (lone_bridgeAt C M hH i.castSucc).2 F hF hT
    have : (⟨F, hF⟩ : NonDanglingEdge M.data) = bridgeAt C M i.castSucc := Subtype.ext h
    rw [this, (lone_bridgeAt C M hH i.castSucc).stablePath, bulbBridge_castSucc]
  · exact LoopAt.onRow_of_over_tl M (C.isLoop i) hF hT

/-- **Every survivor on a tail row lies over its tail column.** -/
theorem over_tcol_of_onRow (s : CatSlot c) {F : NonDanglingEdge M.data}
    (h : F.stablePath = row C M s) : F.1.1.1 = tcol C M hH s := by
  rcases s with i | i | i
  · rw [((lone_pathE C M hH i).1 F).mp h]; rfl
  · rw [← bulbBridge_castSucc] at h
    rw [((lone_bridgeAt C M hH i.castSucc).1 F).mp h]; rfl
  · obtain ⟨col, hcol⟩ := PassOnceLollipopWitness.exists_rowSingleColumn_core_loop M
      (C.isLoop i)
    obtain ⟨e, he, hS⟩ := M.fullDim.noDanglingTargetFibres (LoopAt.tl M (C.isLoop i))
    have heRow := LoopAt.onRow_of_over_tl M (C.isLoop i) hS he
    have he' : e ∈ EdgeDenominator.rowEdges M.fullDim.labelling
        (M.fullDim.labelling.row (M.ident.row.symm (C.slot (Sum.inr (Sum.inr i))))) :=
      (EdgeDenominator.mem_rowEdges _ _ _).mpr ⟨hS, by rw [heRow]; rfl⟩
    have hF' : F.1 ∈ EdgeDenominator.rowEdges M.fullDim.labelling
        (M.fullDim.labelling.row (M.ident.row.symm (C.slot (Sum.inr (Sum.inr i))))) :=
      (EdgeDenominator.mem_rowEdges _ _ _).mpr ⟨F.2, by
        change M.fullDim.labelling.row F.stablePath = _
        rw [h]; rfl⟩
    rw [hcol F.1 hF', ← hcol e he', he]
    rfl

theorem tcol_injective : Function.Injective (tcol C M hH) := by
  intro s s' h
  obtain ⟨e, he, hS⟩ := M.fullDim.noDanglingTargetFibres (tcol C M hH s)
  have h1 := onRow_of_over_tcol C M hH s hS he
  have h2 := onRow_of_over_tcol C M hH s' hS (he.trans h)
  exact row_injective C M (h1.symm.trans h2)

/-- The survivors over a non-loop tail column: the lone survivor. -/
theorem eq_pathE_of_over (i : Fin (c + 1)) {F : M.data.SourceEdge} (hF : ¬ IsDangling M.data F)
    (hT : F.1.1 = tcol C M hH (Sum.inl i)) : F = (pathE C M hH i).1 :=
  (lone_pathE C M hH i).2 F hF hT

theorem eq_bridgeAt_of_over (i : Fin c) {F : M.data.SourceEdge} (hF : ¬ IsDangling M.data F)
    (hT : F.1.1 = tcol C M hH (Sum.inr (Sum.inl i))) : F = (bridgeAt C M i.castSucc).1 :=
  (lone_bridgeAt C M hH i.castSucc).2 F hF hT

end

end DraismaVargas.Count.MarkedCountGeneral.TailAt
