module

public import DraismaVargasCount.GeometricLimitTransport
public import DraismaVargasCount.InheritedLimitRows

@[expose] public section

/-!
# Naturality of inherited row labels

The literal retained source-occurrence embedding commutes with geometric
contraction transport, including its sheet permutation. Descending this square
to stable paths proves that the actual inherited core-row labels are preserved
by every over-core frame isomorphism. No row-label preservation is assumed
for the contracted datum.
-/

namespace DraismaVargas.Count.GeometricInheritedRows

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction W4StableSource
open SegmentWalls (Frame)
open WallStar (Regrowth Nondegenerate)
open GeometricSegmentWalls (FrameIso)
open GeometricLimitTransport InheritedLimitRows
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

theorem edgePerm_contractDatumIsoOfEdgeEq {target₁ target₂ : CFGraph.{0}}
    {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
    (iso : GeometricDatumIso first second) (e₁ : target₁.edges) (e₂ : target₂.edges)
    (h : iso.targetEdge e₁ = e₂)
    (hOne₁ : num_edges target₁ (e₁ : target₁.V × target₁.V).1
      (e₁ : target₁.V × target₁.V).2 = 1)
    (hOne₂ : num_edges target₂ (e₂ : target₂.V × target₂.V).1
      (e₂ : target₂.V × target₂.V).2 = 1)
    (edge : (contractTarget e₁ hOne₁).edges) :
    (contractDatumIsoOfEdgeEq iso e₁ e₂ h hOne₁ hOne₂).edgePerm edge =
      iso.edgePerm (unfoldEdge rfl (fst_ne_snd e₁) hOne₁ edge) := by
  subst e₂
  rfl

theorem edgeEmbedding_limitIso {first second : Regrowth core y degree}
    (fi : FrameIso first.frame second.frame) (edge : first.limit.SourceEdge) :
    edgeEmbedding second ((limitIso fi).sourceEdgeEquiv edge) =
      fi.datum.sourceEdgeEquiv (edgeEmbedding first edge) := by
  apply Subtype.ext
  rw [show (edgeEmbedding second ((limitIso fi).sourceEdgeEquiv edge)).1 = _ from
    IncomingNormalizationRows.sourceEdgeEmbedding_val _ _ _ _ _]
  change (unfoldEdge rfl (fst_ne_snd (second.frame.edgeOf second.column))
      (second.frame.numEdges_edgeOf second.column) ((limitIso fi).targetEdge edge.1.1),
      (limitIso fi).edgePerm edge.1.1 edge.1.2) =
    (fi.datum.targetEdge (edgeEmbedding first edge).1.1,
      fi.datum.edgePerm (edgeEmbedding first edge).1.1 (edgeEmbedding first edge).1.2)
  rw [show (edgeEmbedding first edge).1 = _ from
    IncomingNormalizationRows.sourceEdgeEmbedding_val _ _ _ _ _]
  apply Prod.ext
  · exact unfoldEdge_limitIso fi edge.1.1
  · exact congrArg (fun perm : Equiv.Perm (Fin degree) ↦ perm edge.1.2)
      (edgePerm_contractDatumIsoOfEdgeEq _ _ _ _ _ _ _)

theorem rowEquiv_limitIso {first second : Regrowth core y degree}
    (hy : Nondegenerate y) (fi : FrameIso first.frame second.frame)
    (row : StablePath first.limit) :
    rowEquiv second hy ((limitIso fi).stablePathEquiv (limit_connected first) row) =
      fi.datum.stablePathEquiv first.frame.fullDim.connected (rowEquiv first hy row) := by
  refine Quot.inductionOn row ?_
  intro edge
  let lifted : NonDanglingEdge first.frame.data :=
    ⟨edgeEmbedding first edge.1,
      fun h ↦ edge.2 ((edgeEmbedding_dangling first hy edge.1).mp h)⟩
  have hMap := edgeEmbedding_limitIso fi edge.1
  have hPath := congrArg (rowEquiv second hy)
    ((limitIso fi).stablePathEquiv_mk (limit_connected first) edge)
  refine hPath.trans ((rowEquiv_mk second hy _).trans ?_)
  have hLift := fi.datum.stablePathEquiv_mk first.frame.fullDim.connected lifted
  have hRow := congrArg (fi.datum.stablePathEquiv first.frame.fullDim.connected)
    (rowEquiv_mk first hy edge)
  refine Eq.trans ?_ (hLift.symm.trans hRow.symm)
  exact congrArg NonDanglingEdge.stablePath (Subtype.ext hMap)

/-- Actual inherited row labels commute with geometric contraction transport. -/
theorem rowLabel_limitIso {first second : Regrowth core y degree}
    (hy : Nondegenerate y) (fi : FrameIso first.frame second.frame)
    (row : StablePath first.limit) :
    rowLabel second hy ((limitIso fi).stablePathEquiv (limit_connected first) row) =
      rowLabel first hy row := by
  change second.frame.ident.row (rowEquiv second hy
    ((limitIso fi).stablePathEquiv (limit_connected first) row)) = _
  rw [rowEquiv_limitIso hy fi]
  exact fi.overCore_row _

end DraismaVargas.Count.GeometricInheritedRows
