import DraismaVargasCount.GeometricTransport
import DraismaVargas.LocalCases.GlobalResolution
import DraismaVargas.LocalCases.W4TargetPairings

/-!
# Geometric base change of a uniform partition expansion

Duplicate the wall partition at both expanded endpoints and on their new
occurrence. This is an actual gluing datum, obtained from the global resolution
constructor `GlobalResolution.datum`. Its validity is not asserted for arbitrary side
assignments. A geometric base isomorphism lifts to this datum whenever the
side assignments agree on its actual occurrence bijection.

The valency-four star arguments (`W4WallExhaustion`, `W4StarParity`) use this datum, with the
limit as base, to compare the members of the star at a `W4` wall with uniform expansions.
-/
namespace DraismaVargas.Count.GeometricUniformExpansion
open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open TargetExpansion ResolutionM11

variable {target otherTarget : CFGraph} {degree : ℕ}

private theorem oldCompatible (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) :
    GlobalResolution.OldCompatible data wall right (joinedResolutionAt (data.vertexPartition wall)) := by
  apply GlobalResolution.oldCompatible_of_wall
  intro edge hIncident
  have h : (data.edgePartition edge).Refines (data.vertexPartition wall) := by
    rcases hIncident with h | h
    · exact h ▸ data.refines_left edge
    · exact h ▸ data.refines_right edge
  cases right edge <;> exact h

noncomputable def data (base : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) : GluingDatum (graph target wall right) degree :=
  GlobalResolution.datum base wall right (joinedResolutionAt (base.vertexPartition wall))
    (oldCompatible base wall right)

theorem vertexPartition (base : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (vertex : (graph target wall right).V) :
    (data base wall right).vertexPartition vertex =
      base.vertexPartition (contractVertex target wall vertex) := by
  cases vertex with
  | inl vertex =>
    by_cases h : vertex = wall
    · subst vertex
      simp [data,GlobalResolution.datum,GlobalResolution.expandedVertexPartition,
        joinedResolutionAt,contractVertex]
    · simp [data,GlobalResolution.datum,GlobalResolution.expandedVertexPartition,
        joinedResolutionAt,contractVertex,h]
  | inr vertex => cases vertex; rfl

theorem vertexPartition_endpoint (base : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (edge : target.edges) (vertex : target.V) :
    (data base wall right).vertexPartition (expandedEndpoint target wall right edge vertex) =
      base.vertexPartition vertex :=
  (vertexPartition base wall right _).trans
    (congrArg base.vertexPartition (contract_expandedEndpoint target wall right edge vertex))

theorem edgePartition_none (base : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) :
    (data base wall right).edgePartition (occurrenceEquiv target wall right none) =
      base.vertexPartition wall :=
  GlobalResolution.expandedEdgePartition_new base wall right _

theorem edgePartition_some (base : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (edge : target.edges) :
    (data base wall right).edgePartition (occurrenceEquiv target wall right (some edge)) =
      base.edgePartition edge :=
  GlobalResolution.expandedEdgePartition_old base wall right _ edge

variable {first : GluingDatum target degree} {second : GluingDatum otherTarget degree}
  (iso : GeometricDatumIso first second)
  (wall : target.V) (otherWall : otherTarget.V)
  (hWall : iso.targetVertex wall = otherWall)
  (right : target.edges → Bool) (otherRight : otherTarget.edges → Bool)
  (hRight : ∀ edge, otherRight (iso.targetEdge edge) = right edge)

/-- For the canonical W4 pairings, side compatibility is a theorem of the
four actual occurrence labels, not a further local resolution choice. -/
theorem right_map_of_star_edges
    (star : W4TargetPairings.FourStar target wall)
    (otherStar : W4TargetPairings.FourStar otherTarget otherWall)
    (hStar : ∀ label, iso.targetEdge (star.edge label) = otherStar.edge label)
    (pairing : Fin 3) (edge : target.edges) :
    otherStar.right pairing (iso.targetEdge edge) = star.right pairing edge := by
  apply Bool.eq_iff_iff.mpr
  rw [W4TargetPairings.FourStar.right_eq_true_iff,W4TargetPairings.FourStar.right_eq_true_iff]
  simp only [W4TargetPairings.FourStar.rightSet,Finset.mem_insert,Finset.mem_singleton]
  rw [← hStar 0,← hStar (Fin.succ pairing)]
  exact or_congr iso.targetEdge.injective.eq_iff iso.targetEdge.injective.eq_iff

def vertices : Vertex target ≃ Vertex otherTarget :=
  Equiv.sumCongr iso.targetVertex (Equiv.refl Unit)

noncomputable def edges : (graph target wall right).edges ≃ (graph otherTarget otherWall otherRight).edges :=
  (occurrenceEquiv target wall right).symm.trans
    (iso.targetEdge.optionCongr.trans (occurrenceEquiv otherTarget otherWall otherRight))

theorem edges_occurrence (label : Option target.edges) :
    edges iso wall otherWall right otherRight (occurrenceEquiv target wall right label) =
      occurrenceEquiv otherTarget otherWall otherRight (label.map iso.targetEdge) := by
  simp only [edges,Equiv.trans_apply,Equiv.symm_apply_apply]
  rfl

include hWall in
theorem contractVertex_vertices (vertex : Vertex target) :
    contractVertex otherTarget otherWall (vertices iso vertex) =
      iso.targetVertex (contractVertex target wall vertex) := by
  cases vertex with
  | inl vertex => rfl
  | inr vertex => cases vertex; exact hWall.symm

include hWall hRight in
theorem expandedEndpoint_vertices (edge : target.edges) (vertex : target.V) :
    vertices iso (expandedEndpoint target wall right edge vertex) =
      expandedEndpoint otherTarget otherWall otherRight (iso.targetEdge edge)
        (iso.targetVertex vertex) := by
  simp only [expandedEndpoint,← hRight edge,← hWall,Equiv.apply_eq_iff_eq]
  split_ifs <;> rfl

include hWall hRight in
theorem edges_ends (edge : (graph target wall right).edges) :
    UnorderedEnds (vertices iso) edge.1
      (edges iso wall otherWall right otherRight edge).1 := by
  obtain ⟨label,rfl⟩ := (occurrenceEquiv target wall right).surjective edge
  rw [edges_occurrence]
  cases label with
  | none =>
    simp only [Option.map_none,occurrenceEquiv_none]
    apply Or.inl
    change (Sum.inl otherWall,Sum.inr ()) = (Sum.inl (iso.targetVertex wall),Sum.inr ())
    rw [hWall]
  | some edge =>
    simp only [Option.map_some,occurrenceEquiv_some,oldEnds]
    rcases iso.ends edge with h | h
    · rw [h]
      exact Or.inl (Prod.ext (expandedEndpoint_vertices iso wall otherWall hWall right otherRight
        hRight edge (edge : target.V × target.V).1).symm
        (expandedEndpoint_vertices iso wall otherWall hWall right otherRight
          hRight edge (edge : target.V × target.V).2).symm)
    · rw [h]
      exact Or.inr (Prod.ext (expandedEndpoint_vertices iso wall otherWall hWall right otherRight
        hRight edge (edge : target.V × target.V).2).symm
        (expandedEndpoint_vertices iso wall otherWall hWall right otherRight
          hRight edge (edge : target.V × target.V).1).symm)

noncomputable def edgePerm (edge : (graph target wall right).edges) : Equiv.Perm (Fin degree) :=
  match (occurrenceEquiv target wall right).symm edge with
  | none => iso.vertexPerm wall
  | some edge => iso.edgePerm edge

theorem edgePerm_none :
    edgePerm iso wall right (occurrenceEquiv target wall right none) = iso.vertexPerm wall := by
  simp only [edgePerm,Equiv.symm_apply_apply]

theorem edgePerm_some (edge : target.edges) :
    edgePerm iso wall right (occurrenceEquiv target wall right (some edge)) = iso.edgePerm edge := by
  simp only [edgePerm,Equiv.symm_apply_apply]

noncomputable def lift :
    GeometricDatumIso (data first wall right) (data second otherWall otherRight) where
  targetVertex := vertices iso
  targetEdge := edges iso wall otherWall right otherRight
  ends := edges_ends iso wall otherWall hWall right otherRight hRight
  vertexPerm vertex := iso.vertexPerm (contractVertex target wall vertex)
  edgePerm := edgePerm iso wall right
  vertexPartition vertex := by
    rw [vertexPartition,vertexPartition]
    exact (congrArg second.vertexPartition
      (contractVertex_vertices iso wall otherWall hWall vertex)).trans (iso.vertexPartition _)
  edgePartition edge := by
    obtain ⟨label,rfl⟩ := (occurrenceEquiv target wall right).surjective edge
    rw [edges_occurrence]
    cases label with
    | none =>
      simp only [Option.map_none,edgePartition_none,edgePerm_none]
      rw [← hWall]
      exact iso.vertexPartition wall
    | some edge =>
      simp only [Option.map_some,edgePartition_some,edgePerm_some]
      exact iso.edgePartition edge
  compatible edge vertex hIncident sheet := by
    obtain ⟨label,rfl⟩ := (occurrenceEquiv target wall right).surjective edge
    cases label with
    | none =>
      simp only [occurrenceEquiv_none,newEnds] at hIncident
      rcases hIncident with rfl | rfl <;>
        simp only [edgePerm_none,contract_oldVertex,contract_freshVertex,
          Equiv.symm_apply_apply,SheetPartition.rel_iff]
    | some edge =>
      simp only [occurrenceEquiv_some,oldEnds] at hIncident
      rcases hIncident with rfl | rfl
      · simpa only [vertexPartition_endpoint,edgePerm_some,contract_expandedEndpoint] using
          iso.compatible edge (edge : target.V × target.V).1 (Or.inl rfl) sheet
      · simpa only [vertexPartition_endpoint,edgePerm_some,contract_expandedEndpoint] using
          iso.compatible edge (edge : target.V × target.V).2 (Or.inr rfl) sheet

/-- Literal source contraction for the duplicated partition datum. Since
its vertex partition already is the base partition at the folded vertex,
the stored sheet representative does not change. -/
def contractSourceVertex (base : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (vertex : (data base wall right).SourceVertex) :
    base.SourceVertex :=
  ⟨(contractVertex target wall vertex.1.1,vertex.1.2),by
    have h := vertex.2
    rw [vertexPartition] at h
    exact h⟩

theorem contractSourceVertex_eq_global (base : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (vertex : (data base wall right).SourceVertex) :
    contractSourceVertex base wall right vertex =
      GlobalResolution.sourceVertexMap base wall right (joinedResolutionAt (base.vertexPartition wall))
        (oldCompatible base wall right) vertex := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact (contractSourceVertex base wall right vertex).2.symm

noncomputable def retainedSourceEdge (base : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (edge : base.SourceEdge) : (data base wall right).SourceEdge :=
  ⟨(occurrenceEquiv target wall right (some edge.1.1),edge.1.2),by
    rw [edgePartition_some]
    exact edge.2⟩

theorem lift_targetEdge_occurrence (label : Option target.edges) :
    (lift iso wall otherWall hWall right otherRight hRight).targetEdge
        (occurrenceEquiv target wall right label) =
      occurrenceEquiv otherTarget otherWall otherRight (label.map iso.targetEdge) :=
  edges_occurrence iso wall otherWall right otherRight label

/-- The actual source-vertex contraction square commutes. This is the
dictionary needed to recover inherited branch labels in the converse direction, where a star
member at a discrete `W4` wall is identified with a uniform expansion (`W4StarParity`). -/
theorem contractSourceVertex_lift (vertex : (data first wall right).SourceVertex) :
    iso.sourceVertexEquiv (contractSourceVertex first wall right vertex) =
      contractSourceVertex second otherWall otherRight
        ((lift iso wall otherWall hWall right otherRight hRight).sourceVertexEquiv vertex) := by
  apply Subtype.ext
  apply Prod.ext
  · exact (contractVertex_vertices iso wall otherWall hWall vertex.1.1).symm
  · rfl

/-- Retained source occurrences commute as well, including their sheet
permutations. The stable-row dictionary is induced by these edges. -/
theorem retainedSourceEdge_lift (edge : first.SourceEdge) :
    (lift iso wall otherWall hWall right otherRight hRight).sourceEdgeEquiv
        (retainedSourceEdge first wall right edge) =
      retainedSourceEdge second otherWall otherRight (iso.sourceEdgeEquiv edge) := by
  apply Subtype.ext
  apply Prod.ext
  · exact lift_targetEdge_occurrence iso wall otherWall hWall right otherRight hRight (some edge.1.1)
  · exact congrArg (fun permutation : Equiv.Perm (Fin degree) ↦ permutation edge.1.2)
      (edgePerm_some iso wall right edge.1.1)

end DraismaVargas.Count.GeometricUniformExpansion
