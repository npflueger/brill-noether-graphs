module

public import DraismaVargasCount.GeometricSegmentWalls
public import DraismaVargasCount.GeometricContraction
public import DraismaVargasCount.StarPilot

@[expose] public section

/-!
# Actual metric limits under geometric frame isomorphisms

Contraction and the surviving target lengths are invariant under the actual
orientation-independent over-core frame relation. This is not the assertion
that two arbitrary combinatorially isomorphic limits have the same metric, nor
does a metric limit by itself retain the inherited source-core labels.
-/

namespace DraismaVargas.Count.GeometricLimitTransport

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingContraction
open SegmentWalls (Frame)
open WallStar (Regrowth)
open GeometricSegmentWalls (FrameIso)
open StarPilot (limitLength)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

theorem targetEdge_edgeOf {first second : Frame core degree} (fi : FrameIso first second)
    (col : Fin p) : fi.datum.targetEdge (first.edgeOf col) = second.edgeOf (fi.column col) := by
  show fi.datum.targetEdge (first.fullDim.labelling.targetEdge col) =
    second.fullDim.labelling.targetEdge (fi.column col)
  rw [FrameIso.column, Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply]

theorem column_eq_of_frameIso {first second : Regrowth core y degree}
    (fi : FrameIso first.frame second.frame) : fi.column first.column = second.column :=
  (fi.degenerateAt_map first.degenerate).column_unique second.degenerate

/-- Naming the same second contracted edge differently does not change the
actual contraction isomorphism. -/
noncomputable def contractDatumIsoOfEdgeEq {target₁ target₂ : CFGraph.{0}}
    {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
    (iso : GeometricDatumIso first second) (e₁ : target₁.edges) (e₂ : target₂.edges)
    (h : iso.targetEdge e₁ = e₂)
    (hOne₁ : num_edges target₁ (e₁ : target₁.V × target₁.V).1
      (e₁ : target₁.V × target₁.V).2 = 1)
    (hOne₂ : num_edges target₂ (e₂ : target₂.V × target₂.V).1
      (e₂ : target₂.V × target₂.V).2 = 1) :
    GeometricDatumIso (contractDatumAt first e₁ hOne₁) (contractDatumAt second e₂ hOne₂) := by
  subst e₂
  exact GeometricContraction.contractDatumIso iso e₁ hOne₁ hOne₂

theorem unfoldEdge_contractDatumIsoOfEdgeEq {target₁ target₂ : CFGraph.{0}}
    {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
    (iso : GeometricDatumIso first second) (e₁ : target₁.edges) (e₂ : target₂.edges)
    (h : iso.targetEdge e₁ = e₂)
    (hOne₁ : num_edges target₁ (e₁ : target₁.V × target₁.V).1
      (e₁ : target₁.V × target₁.V).2 = 1)
    (hOne₂ : num_edges target₂ (e₂ : target₂.V × target₂.V).1
      (e₂ : target₂.V × target₂.V).2 = 1)
    (edge : (contractTarget e₁ hOne₁).edges) :
    unfoldEdge rfl (fst_ne_snd e₂) hOne₂
        ((contractDatumIsoOfEdgeEq iso e₁ e₂ h hOne₁ hOne₂).targetEdge edge) =
      iso.targetEdge (unfoldEdge rfl (fst_ne_snd e₁) hOne₁ edge) := by
  subst e₂
  exact GeometricContraction.unfoldEdge_contractEdgeEquiv iso e₁ hOne₁ hOne₂ edge

noncomputable def limitIso {first second : Regrowth core y degree}
    (fi : FrameIso first.frame second.frame) : GeometricDatumIso first.limit second.limit :=
  contractDatumIsoOfEdgeEq fi.datum (first.frame.edgeOf first.column)
    (second.frame.edgeOf second.column)
    (by rw [targetEdge_edgeOf, column_eq_of_frameIso fi])
    (first.frame.numEdges_edgeOf first.column) (second.frame.numEdges_edgeOf second.column)

theorem unfoldEdge_limitIso {first second : Regrowth core y degree}
    (fi : FrameIso first.frame second.frame)
    (edge : (first.frame.limitTarget first.column).edges) :
    unfoldEdge rfl (fst_ne_snd (second.frame.edgeOf second.column))
        (second.frame.numEdges_edgeOf second.column) ((limitIso fi).targetEdge edge) =
      fi.datum.targetEdge (unfoldEdge rfl (fst_ne_snd (first.frame.edgeOf first.column))
        (first.frame.numEdges_edgeOf first.column) edge) :=
  unfoldEdge_contractDatumIsoOfEdgeEq _ _ _ _ _ _ _

/-- The metric equality follows from the real coordinate transport; it is not
an extra field in the frame or contraction isomorphism. -/
theorem limitLength_limitIso {first second : Regrowth core y degree}
    (fi : FrameIso first.frame second.frame)
    (edge : (first.frame.limitTarget first.column).edges) :
    limitLength second ((limitIso fi).targetEdge edge) = limitLength first edge := by
  unfold limitLength
  rw [unfoldEdge_limitIso]
  have h := fi.coordsAt_column y (first.frame.fullDim.labelling.targetEdge.symm
    (unfoldEdge rfl (fst_ne_snd (first.frame.edgeOf first.column))
      (first.frame.numEdges_edgeOf first.column) edge))
  simpa only [FrameIso.column, Equiv.trans_apply, Equiv.apply_symm_apply] using h

/-- Geometric isomorphism of the actual contracted target metric. Source-core
label compatibility is deliberately a separate condition. -/
structure MetricLimitIso (first second : Regrowth core y degree) where
  datum : GeometricDatumIso first.limit second.limit
  metric : ∀ edge, limitLength second (datum.targetEdge edge) = limitLength first edge

namespace MetricLimitIso

noncomputable def ofFrameIso {first second : Regrowth core y degree}
    (fi : FrameIso first.frame second.frame) : MetricLimitIso first second :=
  ⟨limitIso fi, limitLength_limitIso fi⟩

noncomputable def refl (first : Regrowth core y degree) : MetricLimitIso first first :=
  ⟨GeometricDatumIso.refl _, fun _ ↦ rfl⟩

noncomputable def symm {first second : Regrowth core y degree}
    (iso : MetricLimitIso first second) : MetricLimitIso second first := by
  refine ⟨iso.datum.symm, fun edge ↦ ?_⟩
  exact (iso.metric (iso.datum.targetEdge.symm edge)).symm.trans
    (congrArg (limitLength second) (iso.datum.targetEdge.apply_symm_apply edge))

noncomputable def trans {first second third : Regrowth core y degree}
    (left : MetricLimitIso first second) (right : MetricLimitIso second third) :
    MetricLimitIso first third :=
  ⟨left.datum.trans right.datum,
    fun edge ↦ (right.metric (left.datum.targetEdge edge)).trans (left.metric edge)⟩

end MetricLimitIso

end DraismaVargas.Count.GeometricLimitTransport
