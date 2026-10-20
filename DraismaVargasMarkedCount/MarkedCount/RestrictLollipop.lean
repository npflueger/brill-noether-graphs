module

public import DraismaVargasMarkedCount.MarkedCount.Core
public import DraismaVargasCount.PassOnceLollipopWitness
public import DraismaVargasCount.PendantFibre

@[expose] public section

/-!
# The branch of a lollipop, at a member over the lollipop core

For a member `M` over `attachLollipops core mark` and a mark `j`:

* `loopV M j` (`w`), `markV M j` (`u`), the bridge occurrence `bridgeE M j` (`e_b`);
* the target vertices `uP M j = φ(w)`, `vC M j = φ(C)` (a leaf), `xV M j = φ(u)`, and the
  target edges `tb M j = φ(e_b)`, `tl M j` (the leaf edge at `vC`).

The **branch** of lollipop `j` is `(tb, uP, tl, vC)`. Proved here: its shape in the target
(`incidentEdges_uP`, `incidentEdges_vC`), the fibre clause of the bridge-and-loop lemma, and the
facts the restriction needs.
-/

namespace DraismaVargas.Count.MarkedCount.Lollipops

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.RowWalk (OnRow)
open Utilities.Certificate.ExplicitPotential (Core)
open scoped DraismaVargas.Infrastructure.GluingContraction

noncomputable section

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n}
  {y : Fin (p + (k + k)) → ℚ} (M : FibreMember (attachLollipops core mark) y degree)

theorem hLoop (j : Fin k) :
    (attachLollipops core mark).tail (loopSlot p j) =
      (attachLollipops core mark).head (loopSlot p j) :=
  attachLollipops_loop_isLoop core mark j

/-! ## 1.  The source vertices and the bridge -/

/-- `w_j`, the branch vertex of the lollipop vertex. -/
def loopV (j : Fin k) : M.data.SourceVertex := LollipopDivalent.loopBranch M (hLoop j)

/-- `u_j`, the branch vertex of the mark. -/
def markV (j : Fin k) : M.data.SourceVertex := (M.ident.vertex.symm (oldVertex k (mark j))).1

theorem three_le_loopV (j : Fin k) : 3 ≤ nonDanglingValency M.data (loopV M j) :=
  LollipopDivalent.three_le_loopBranch M (hLoop j)

theorem three_le_markV (j : Fin k) : 3 ≤ nonDanglingValency M.data (markV M j) :=
  (M.ident.vertex.symm (oldVertex k (mark j))).2

theorem nonDanglingValency_loopV (j : Fin k) : nonDanglingValency M.data (loopV M j) = 3 :=
  le_antisymm (M.fullDim.trivalent _) (three_le_loopV M j)

theorem nonDanglingValency_markV (j : Fin k) : nonDanglingValency M.data (markV M j) = 3 :=
  le_antisymm (M.fullDim.trivalent _) (three_le_markV M j)

theorem ident_loopV (j : Fin k) :
    M.ident.vertex ⟨loopV M j, three_le_loopV M j⟩ = lollipopVertex n j := by
  change M.ident.vertex (M.ident.vertex.symm _) = _
  rw [Equiv.apply_symm_apply, attachLollipops_tail_loop]

theorem ident_markV (j : Fin k) :
    M.ident.vertex ⟨markV M j, three_le_markV M j⟩ = oldVertex k (mark j) := by
  change M.ident.vertex (M.ident.vertex.symm _) = _
  rw [Equiv.apply_symm_apply]

theorem loopV_ne_markV (i j : Fin k) : loopV M i ≠ markV M j := by
  intro h
  have h1 := ident_loopV M i
  have h2 := ident_markV M j
  have : (⟨loopV M i, three_le_loopV M i⟩ : StableGraphIncidence.BranchVertex M.data) =
      ⟨markV M j, three_le_markV M j⟩ := Subtype.ext h
  rw [this, h2] at h1
  exact lollipopVertex_ne_oldVertex i (mark j) h1.symm

theorem markV_injective (hc : IsMarkedCubic core mark) : Function.Injective (markV M) := by
  intro i j h
  have : (M.ident.vertex.symm (oldVertex k (mark i))) =
      M.ident.vertex.symm (oldVertex k (mark j)) := Subtype.ext h
  exact hc.injective (oldVertex_inj.mp (M.ident.vertex.symm.injective this))

theorem loopV_injective : Function.Injective (loopV M) := by
  intro i j h
  have h1 := ident_loopV M i
  have h2 := ident_loopV M j
  have : (⟨loopV M i, three_le_loopV M i⟩ : StableGraphIncidence.BranchVertex M.data) =
      ⟨loopV M j, three_le_loopV M j⟩ := Subtype.ext h
  rw [this, h2] at h1
  exact lollipopVertex_inj.mp h1.symm

/-- `e_b`, the bridge occurrence at `w_j`. -/
def bridgeE (j : Fin k) : M.data.SourceEdge :=
  (LollipopBridgeFibreWitness.exists_bridge_loopBranch M (hLoop j)).choose

theorem bridgeE_spec (j : Fin k) :
    ¬ IsDangling M.data (bridgeE M j) ∧ Incident M.data (bridgeE M j) (loopV M j) ∧
      ¬ OnRow M.data (LollipopBridgeFibreWitness.loopRow M (loopSlot p j)) (bridgeE M j) ∧
      M.data.sourceEdgeIndex (bridgeE M j) = 2 :=
  (LollipopBridgeFibreWitness.exists_bridge_loopBranch M (hLoop j)).choose_spec

theorem bridgeE_survives (j : Fin k) : ¬ IsDangling M.data (bridgeE M j) := (bridgeE_spec M j).1

theorem bridgeE_incident_loopV (j : Fin k) : Incident M.data (bridgeE M j) (loopV M j) :=
  (bridgeE_spec M j).2.1

theorem bridgeE_index (j : Fin k) : M.data.sourceEdgeIndex (bridgeE M j) = 2 :=
  (bridgeE_spec M j).2.2.2

/-! ## 2.  The target vertices and edges of the branch -/

/-- `φ(w_j)`. -/
def uP (j : Fin k) : M.target.V := (loopV M j).1.1

/-- `φ(u_j)`. -/
def xV (j : Fin k) : M.target.V := (markV M j).1.1

/-- `φ(C_j)`, the leaf of the loop row. -/
def vC (j : Fin k) : M.target.V := LollipopLeafRow.loopLeaf M (hLoop j)

theorem vC_isLeaf (j : Fin k) : Count.IsLeafVertex M.target (vC M j) :=
  LollipopLeafRow.loopLeaf_isLeafVertex M (hLoop j)

/-- The leaf edge at `vC`. -/
def tl (j : Fin k) : M.target.edges := Count.leafEdge (vC_isLeaf M j)

/-- `φ(e_b)`. -/
def tb (j : Fin k) : M.target.edges := (bridgeE M j).1.1

theorem uP_divalent (j : Fin k) : (GluingDatum.incidentEdges (uP M j)).card = 2 :=
  LollipopDivalent.loopImage_divalent M (hLoop j)

theorem tl_mem_uP (j : Fin k) : tl M j ∈ GluingDatum.incidentEdges (uP M j) :=
  PassOnceLollipopWitness.loopLeafAdjacent M (hLoop j)

theorem tl_mem_vC (j : Fin k) : tl M j ∈ GluingDatum.incidentEdges (vC M j) :=
  Count.leafEdge_mem (vC_isLeaf M j)

theorem tb_mem_uP (j : Fin k) : tb M j ∈ GluingDatum.incidentEdges (uP M j) :=
  ((incident_iff_target_mem_and_rel M.data _ _).mp (bridgeE_incident_loopV M j)).1

/-- The loop row of lollipop `j`, as a stable path. -/
def loopRow (j : Fin k) : StablePath M.data := M.ident.row.symm (loopSlot p j)

/-- **Every survivor over the leaf edge lies on the loop row.** -/
theorem onRow_of_over_tl {E : M.data.SourceEdge} (hE : ¬ IsDangling M.data E)
    (hT : E.1.1 = tl M j) :
    NonDanglingEdge.stablePath (⟨E, hE⟩ : NonDanglingEdge M.data) = loopRow M j := by
  have hMem : E ∈ LeafFibre.leafSurvivors (data := M.data) (vC_isLeaf M j) :=
    (LeafFibre.mem_leafSurvivors _).mpr ⟨hE, hT⟩
  have h1 := LeafFibre.row_eq_leafRow M.fullDim (vC_isLeaf M j) hMem hE
  have h2 := LollipopLeafRow.leafRow_loopLeaf M (hLoop j)
  exact M.fullDim.labelling.row.injective (h1.trans h2)

theorem tb_ne_tl (j : Fin k) : tb M j ≠ tl M j := by
  intro h
  apply (bridgeE_spec M j).2.2.1
  exact ⟨bridgeE_survives M j, onRow_of_over_tl M (bridgeE_survives M j) h⟩

theorem incidentEdges_uP (j : Fin k) :
    GluingDatum.incidentEdges (uP M j) = {tb M j, tl M j} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact tb_mem_uP M j
    · exact tl_mem_uP M j
  · rw [uP_divalent, Finset.card_pair (tb_ne_tl M j)]

theorem incidentEdges_vC (j : Fin k) : GluingDatum.incidentEdges (vC M j) = {tl M j} :=
  Count.incidentEdges_eq_leafEdge (vC_isLeaf M j)

/-! ## 3.  The fibre clause -/

/-- **`e_b` is the only survivor over `φ(e_b)`.** -/
theorem eq_bridgeE {E : M.data.SourceEdge} (hE : ¬ IsDangling M.data E) (hT : E.1.1 = tb M j) :
    E = bridgeE M j :=
  PassOnceLollipopWitness.eq_bridge_of_surviving_loopBranch M (hLoop j)
    (bridgeE_survives M j) (bridgeE_incident_loopV M j) (bridgeE_spec M j).2.2.1 hE hT

/-- **`w` is the only non-dangling vertex over `φ(w)`.** -/
theorem nonDanglingValency_over_uP {X : M.data.SourceVertex} (hX : X.1.1 = uP M j)
    (hNe : X ≠ loopV M j) : nonDanglingValency M.data X = 0 :=
  PassOnceLollipopWitness.nonDanglingValency_eq_zero_of_ne_loopBranch M (hLoop j) hX hNe

/-- **Over the leaf `φ(C)` the only non-dangling vertex is `C`, of surviving valency two.** -/
theorem nonDanglingValency_over_vC {X : M.data.SourceVertex} (hX : X.1.1 = vC M j) :
    nonDanglingValency M.data X = 0 ∨ nonDanglingValency M.data X = 2 := by
  have hLeaf : Count.IsLeafVertex M.target X.1.1 := hX ▸ vC_isLeaf M j
  by_cases h0 : nonDanglingValency M.data X = 0
  · exact Or.inl h0
  · right
    have hC := LollipopDivalentWitness.eq_coreVertex_of_surviving M.fullDim
      (Nat.pos_of_ne_zero h0) hLeaf
    rw [hC]
    exact LeafFibre.nonDanglingValency_coreVertex M.fullDim hLeaf

end

end DraismaVargas.Count.MarkedCount.Lollipops
