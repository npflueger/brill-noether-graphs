module

public import DraismaVargasCount.GeometricInheritedRows
public import DraismaVargasCount.InheritedLimitBranches

@[expose] public section

/-!
# Naturality of inherited branch labels

The normalized permutation at the merged vertex agrees with either original
endpoint permutation modulo the actual joined partition. Hence the literal
source contraction commutes with the geometric source-vertex equivalence,
whether the target occurrence reverses orientation or not. The induced unique
branch dictionary then preserves inherited core labels under frame transport.
-/

namespace DraismaVargas.Count.GeometricInheritedBranches

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction GraphContraction SheetPartition
open GeometricContraction GeometricLimitTransport InheritedLimitBranches

variable {target₁ target₂ : CFGraph.{0}} {degree : ℕ}
  {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}

/-- The contracted permutation agrees with the original one modulo the
actual contracted vertex partition, including either merged endpoint. -/
theorem vertexPerm_fold_rel (iso : GeometricDatumIso first second) (edge : target₁.edges)
    (vertex : target₁.V) (sheet : Fin degree) :
    (contractVertexPartition first (edge : target₁.V × target₁.V).1
      (edge : target₁.V × target₁.V).2 (fold target₁ (fst_ne_snd edge) vertex)).Rel
      ((contractVertexPerm iso edge (fold target₁ (fst_ne_snd edge) vertex)).symm
        (iso.vertexPerm vertex sheet)) sheet := by
  by_cases hb : vertex = (edge : target₁.V × target₁.V).2
  · subst vertex
    have hf : (fold target₁ (fst_ne_snd edge) (edge : target₁.V × target₁.V).2).1 =
        (edge : target₁.V × target₁.V).1 := by rw [fold_self]
    rw [contractVertexPartition_of_eq _ _ _ hf, contractVertexPerm_merged iso edge hf,
      mergedPerm]
    apply WallStar.merged_rel_mergePerm_symm _ _ (Or.inr ?_)
    rw [Equiv.symm_apply_apply]
    rfl
  · have hf : (fold target₁ (fst_ne_snd edge) vertex).1 = vertex := by
      rw [fold_of_ne _ _ hb]
    by_cases ha : vertex = (edge : target₁.V × target₁.V).1
    · have hm := hf.trans ha
      rw [contractVertexPartition_of_eq _ _ _ hm, contractVertexPerm_merged iso edge hm,
        mergedPerm, ha]
      apply WallStar.merged_rel_mergePerm_symm _ _ (Or.inl ?_)
      rw [Equiv.symm_apply_apply]
      rfl
    · have hn : (fold target₁ (fst_ne_snd edge) vertex).1 ≠
          (edge : target₁.V × target₁.V).1 := by rwa [hf]
      rw [contractVertexPartition_of_ne _ _ _ hn,
        contractVertexPerm_of_ne iso edge hn, hf, Equiv.symm_apply_apply]
      rfl

theorem sourceVertexMap_contractDatumIso (iso : GeometricDatumIso first second)
    (edge : target₁.edges)
    (hOne₁ : num_edges target₁ (edge : target₁.V × target₁.V).1
      (edge : target₁.V × target₁.V).2 = 1)
    (hOne₂ : num_edges target₂ (iso.targetEdge edge : target₂.V × target₂.V).1
      (iso.targetEdge edge : target₂.V × target₂.V).2 = 1)
    (vertex : first.SourceVertex) :
    (contractDatumIso iso edge hOne₁ hOne₂).sourceVertexEquiv
      (sourceVertexMap first rfl (fst_ne_snd edge) hOne₁ vertex) =
    sourceVertexMap second rfl (fst_ne_snd (iso.targetEdge edge)) hOne₂
      (iso.sourceVertexEquiv vertex) := by
  apply Subtype.ext
  apply Prod.ext
  · exact contractVertexEquiv_fold iso edge vertex.1.1
  · change contractVertexPerm iso edge (fold target₁ (fst_ne_snd edge) vertex.1.1)
        ((contractDatumAt first edge hOne₁).vertexPartition
          (fold target₁ (fst_ne_snd edge) vertex.1.1) |>.repr vertex.1.2) =
      ((contractDatumAt second (iso.targetEdge edge) hOne₂).vertexPartition
        (fold target₂ (fst_ne_snd (iso.targetEdge edge)) (iso.targetVertex vertex.1.1))).repr
        (iso.vertexPerm vertex.1.1 vertex.1.2)
    rw [← contractVertexEquiv_fold iso edge vertex.1.1]
    rw [show (contractDatumAt second (iso.targetEdge edge) hOne₂).vertexPartition
        (contractVertexEquiv iso edge (fold target₁ (fst_ne_snd edge) vertex.1.1)) = _ from
      (contractDatumIso iso edge hOne₁ hOne₂).vertexPartition _]
    change _ = contractVertexPerm iso edge (fold target₁ (fst_ne_snd edge) vertex.1.1)
      ((contractVertexPartition first (edge : target₁.V × target₁.V).1
        (edge : target₁.V × target₁.V).2 (fold target₁ (fst_ne_snd edge) vertex.1.1)).repr
          ((contractVertexPerm iso edge (fold target₁ (fst_ne_snd edge) vertex.1.1)).symm
            (iso.vertexPerm vertex.1.1 vertex.1.2)))
    exact congrArg _ (vertexPerm_fold_rel iso edge vertex.1.1 vertex.1.2).symm

theorem sourceVertexMap_contractDatumIsoOfEdgeEq (iso : GeometricDatumIso first second)
    (e₁ : target₁.edges) (e₂ : target₂.edges) (h : iso.targetEdge e₁ = e₂)
    (hOne₁ : num_edges target₁ (e₁ : target₁.V × target₁.V).1
      (e₁ : target₁.V × target₁.V).2 = 1)
    (hOne₂ : num_edges target₂ (e₂ : target₂.V × target₂.V).1
      (e₂ : target₂.V × target₂.V).2 = 1)
    (vertex : first.SourceVertex) :
    (contractDatumIsoOfEdgeEq iso e₁ e₂ h hOne₁ hOne₂).sourceVertexEquiv
      (sourceVertexMap first rfl (fst_ne_snd e₁) hOne₁ vertex) =
    sourceVertexMap second rfl (fst_ne_snd e₂) hOne₂ (iso.sourceVertexEquiv vertex) := by
  subst e₂
  exact sourceVertexMap_contractDatumIso iso e₁ hOne₁ hOne₂ vertex

open WallStar (Regrowth Nondegenerate)
open GeometricSegmentWalls (FrameIso)
open Utilities.Certificate.ExplicitPotential (Core)
open StableGraphIncidence (BranchVertex)

variable {n p : ℕ} {core : Core n p} {y : Fin p → ℚ}

theorem vertexMap_limitIso {first second : Regrowth core y degree}
    (fi : FrameIso first.frame second.frame) (vertex : first.frame.data.SourceVertex) :
    (limitIso fi).sourceVertexEquiv (vertexMap first vertex) =
      vertexMap second (fi.datum.sourceVertexEquiv vertex) :=
  sourceVertexMap_contractDatumIsoOfEdgeEq _ _ _ _ _ _ _

theorem branchEquiv_limitIso {first second : Regrowth core y degree}
    (hy : Nondegenerate y) (fi : FrameIso first.frame second.frame)
    (branch : BranchVertex first.frame.data) :
    (limitIso fi).branchVertexEquiv (InheritedLimitRows.limit_connected first)
        (branchEquiv first hy branch) =
      branchEquiv second hy
        (fi.datum.branchVertexEquiv first.frame.fullDim.connected branch) :=
  Subtype.ext (vertexMap_limitIso fi branch.1)

/-- The actual geometric contraction preserves inherited branch labels as
well as rows, not merely their cardinalities. -/
theorem branchLabel_limitIso {first second : Regrowth core y degree}
    (hy : Nondegenerate y) (fi : FrameIso first.frame second.frame)
    (branch : BranchVertex first.limit) :
    branchLabel second hy
        ((limitIso fi).branchVertexEquiv (InheritedLimitRows.limit_connected first) branch) =
      branchLabel first hy branch := by
  obtain ⟨old, rfl⟩ := (branchEquiv first hy).surjective branch
  rw [branchEquiv_limitIso hy fi]
  change second.frame.ident.vertex ((branchEquiv second hy).symm
      (branchEquiv second hy
        (fi.datum.branchVertexEquiv first.frame.fullDim.connected old))) =
    first.frame.ident.vertex ((branchEquiv first hy).symm (branchEquiv first hy old))
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact fi.overCore_vertex old

end DraismaVargas.Count.GeometricInheritedBranches
