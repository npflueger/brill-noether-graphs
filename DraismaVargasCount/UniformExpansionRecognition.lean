module

public import DraismaVargasCount.DiscreteW4Normalization

@[expose] public section

/-!
# Recognizing the uniform expansion, and transporting along an equality of data

Source: Draisma--Vargas Part I (arXiv:1909.12924), the section on inherited properties of
limits (`section-inherited-properties`: the target expansion at a wall vertex), read in the
direction the converse classification needs.

## What is proved

`Count.GeometricUniformExpansion.data base wall right` duplicates the wall
partition at both expanded endpoints and on the regrown occurrence.  This
module proves the **recognition** statement in the opposite direction
(`eq_uniformExpansion`): an arbitrary gluing datum on the expanded target
whose five displayed partitions are the ones the uniform expansion prescribes
*is* the uniform expansion, as a literal equality of gluing data.  Only the
partition fields are compared, because `Infrastructure.gluingDatum_ext` says
the remaining three fields are propositions.

Because that conclusion is an equality of data rather than an isomorphism,
consumers need a way to move an isomorphism across it.  `ofEq` is the geometric
datum isomorphism attached to an equality of data; `ofEq_sourceVertexEquiv` and
`ofEq_sourceEdgeEquiv` say that it changes neither the underlying
target-vertex/sheet pair of a quotient-source vertex nor the
target-occurrence/sheet pair of a quotient-source occurrence, which is all a
`Subtype.ext` comparison downstream ever needs.

`contractSourceVertex_eq_sourceEndpoint` rewrites the uniform expansion's
literal source contraction as a `GluingDatum.sourceEndpoint`, the normal form
in which `Count.W4LimitContraction` states its source dictionary, and
`retainedSourceEdge_val` records the underlying pair of a retained occurrence.

## What is not proved here

Nothing here is specific to W4, to a four-valent wall, or to a discrete wall
partition: the recognition hypotheses are simply assumed.  No validity, full
dimensionality, connectivity, branch, row or core-label statement is made
about either datum.  In particular this module does not say that any
particular candidate satisfies the recognition hypotheses; that is the
consumer's obligation.

## Consumers

The exhaustion arguments at walls (`W4WallExhaustion`, `ResolutionExpansion`,
`StarCensusEngine`, `W4StarParity`, `M11StarParityFree`), which use `ofEq` to move
isomorphisms across the recognised equality of data.
-/

namespace DraismaVargas.Count.UniformExpansionRecognition

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open TargetExpansion

variable {target : CFGraph} {degree : ℕ}

/-- **Recognition of the uniform expansion.**  A gluing datum on the expanded
target that carries the wall partition at both expanded endpoints and on the
regrown occurrence, and the base partitions everywhere else, is literally
`GeometricUniformExpansion.data`. -/
theorem eq_uniformExpansion (base : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool)
    (expanded : GluingDatum (graph target wall right) degree)
    (hOldWall : expanded.vertexPartition (oldVertex target wall) = base.vertexPartition wall)
    (hFresh : expanded.vertexPartition (freshVertex target) = base.vertexPartition wall)
    (hAway : ∀ vertex : target.V, vertex ≠ wall →
      expanded.vertexPartition (oldVertex target vertex) = base.vertexPartition vertex)
    (hNew : expanded.edgePartition (occurrenceEquiv target wall right none) =
      base.vertexPartition wall)
    (hRetained : ∀ edge : target.edges,
      expanded.edgePartition (occurrenceEquiv target wall right (some edge)) =
        base.edgePartition edge) :
    expanded = GeometricUniformExpansion.data base wall right := by
  apply gluingDatum_ext
  · funext vertex
    rw [GeometricUniformExpansion.vertexPartition]
    cases vertex with
    | inl vertex =>
      by_cases h : vertex = wall
      · subst vertex
        exact hOldWall
      · exact hAway vertex h
    | inr vertex =>
      cases vertex
      exact hFresh
  · funext edge
    obtain ⟨label, rfl⟩ := (occurrenceEquiv target wall right).surjective edge
    cases label with
    | none => rw [hNew, GeometricUniformExpansion.edgePartition_none]
    | some edge => rw [hRetained, GeometricUniformExpansion.edgePartition_some]

/-- The geometric datum isomorphism carried by an equality of gluing data. -/
noncomputable def ofEq {first second : GluingDatum target degree} (h : first = second) :
    GeometricDatumIso first second :=
  h ▸ GeometricDatumIso.refl first

/-- Transport along an equality of data leaves the underlying
target-vertex/sheet pair of a quotient-source vertex alone. -/
theorem ofEq_sourceVertexEquiv {first second : GluingDatum target degree} (h : first = second)
    (vertex : first.SourceVertex) : ((ofEq h).sourceVertexEquiv vertex).1 = vertex.1 := by
  cases h
  rfl

/-- Transport along an equality of data leaves the underlying
occurrence/sheet pair of a quotient-source occurrence alone. -/
theorem ofEq_sourceEdgeEquiv {first second : GluingDatum target degree} (h : first = second)
    (edge : first.SourceEdge) : ((ofEq h).sourceEdgeEquiv edge).1 = edge.1 := by
  cases h
  rfl

/-- The uniform expansion's literal source contraction, in the
`sourceEndpoint` normal form used by `Count.W4LimitContraction`. -/
theorem contractSourceVertex_eq_sourceEndpoint (base : GluingDatum target degree)
    (wall : target.V) (right : target.edges → Bool)
    (vertex : (GeometricUniformExpansion.data base wall right).SourceVertex) :
    GeometricUniformExpansion.contractSourceVertex base wall right vertex =
      base.sourceEndpoint (contractVertex target wall vertex.1.1) vertex.1.2 :=
  Subtype.ext (Prod.ext rfl
    (GeometricUniformExpansion.contractSourceVertex base wall right vertex).2.symm)

/-- The underlying pair of a retained quotient-source occurrence. -/
theorem retainedSourceEdge_val (base : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (edge : base.SourceEdge) :
    (GeometricUniformExpansion.retainedSourceEdge base wall right edge).1 =
      (occurrenceEquiv target wall right (some edge.1.1), edge.1.2) := rfl

end DraismaVargas.Count.UniformExpansionRecognition
