module

public import DraismaVargas.LocalCases.M11IncomingTargetNormalization

@[expose] public section

/-!
# Literal outer partitions after incoming M11 target normalization

The normalized target maps fix each retained off-wall vertex and each named
retained occurrence.  Transport therefore has exactly the contracted datum's
vertex partitions away from the wall and its edge partitions at every retained
occurrence.  The new occurrence has the original incoming contracted-edge
partition.  These are equalities of representative tables, not merely equality
of block relations.

The two endpoint partitions are the original incoming pair, possibly exchanged
by the explicit target normalization.  The leaf-left, leaf-right, and joined
label-1 corollaries identify that order from the actual placement census.
They do not classify those partitions as selected/background resolutions.

The general `incomingIso` partition APIs specialize definitionally to `splitIso`
with constant-true assignment and `splitPlacement`, or to `joinedIso` with
`star.right` and `joinedPlacement`.  No whole-cover equality, sheet relabelling,
stable-row matching, or M11 incoming-member identification is assumed or proved.
-/

namespace DraismaVargas.LocalCases.M11IncomingOuterPartitions

open DraismaVargas.Infrastructure TargetExpansion GraphContraction GluingContraction
open M11IncomingTargetNormalization M11IncomingCoordinates

section Expansion

variable {target : CFGraph} {wall : target.V}

theorem normalizationIso_oldVertex (first second : target.edges → Bool)
    (hPlacement : (∀ edge ∈ GluingDatum.incidentEdges wall, first edge = second edge) ∨
      (∀ edge ∈ GluingDatum.incidentEdges wall, first edge = !(second edge)))
    (vertex : target.V) (hOff : vertex ≠ wall) :
    (normalizationIso first second hPlacement).vertexEquiv (oldVertex target vertex) =
      oldVertex target vertex := by
  classical
  unfold normalizationIso
  split_ifs
  · rfl
  · exact swapVertices_old_of_ne vertex hOff

end Expansion

section Incoming

variable {incoming : CFGraph} {degree : ℕ} {a b : incoming.V} {contracted : incoming.edges}
variable (data : GluingDatum incoming degree)
    (hc : (contracted : incoming.V × incoming.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges incoming a b = 1)
    (second : (contract incoming hab hOne).edges → Bool)
    (hPlacement :
      (∀ edge ∈ GluingDatum.incidentEdges (target := contract incoming hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = second edge) ∨
      (∀ edge ∈ GluingDatum.incidentEdges (target := contract incoming hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = !(second edge)))

/-- The inverse map at every retained off-wall vertex is its original subtype
value, regardless of whether normalization exchanges the expanded endpoints. -/
theorem incomingIso_symm_oldVertex
    (vertex : (contract incoming hab hOne).V) (hOff : vertex ≠ ⟨a, hab⟩) :
    (incomingIso hc hab hOne second hPlacement).vertexEquiv.symm
      (oldVertex (contract incoming hab hOne) vertex) = vertex.1 := by
  apply (incomingIso hc hab hOne second hPlacement).vertexEquiv.symm_apply_eq.mpr
  rw [incomingIso_vertex]
  have hRestore : (IncomingTargetExpansion.vertexEquiv hab hOne).symm vertex.1 =
      oldVertex (contract incoming hab hOne) vertex :=
    (IncomingTargetExpansion.vertexEquiv hab hOne).symm_apply_eq.mpr rfl
  rw [hRestore]
  exact (normalizationIso_oldVertex _ _ hPlacement vertex hOff).symm

/-- The inverse endpoint pair is explicitly ordered or swapped according to
the actual support decision in the normalization map. -/
theorem incomingIso_symm_endpoints :
    ((incomingIso hc hab hOne second hPlacement).vertexEquiv.symm
        (oldVertex (contract incoming hab hOne) ⟨a, hab⟩),
      (incomingIso hc hab hOne second hPlacement).vertexEquiv.symm
        (freshVertex (contract incoming hab hOne))) =
      if (∀ edge ∈ GluingDatum.incidentEdges (target := contract incoming hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = second edge)
      then (a, b) else (b, a) := by
  classical
  have hA : (IncomingTargetExpansion.vertexEquiv hab hOne).symm a =
      oldVertex (contract incoming hab hOne) ⟨a, hab⟩ :=
    (IncomingTargetExpansion.vertexEquiv hab hOne).symm_apply_eq.mpr rfl
  have hB : (IncomingTargetExpansion.vertexEquiv hab hOne).symm b =
      freshVertex (contract incoming hab hOne) :=
    (IncomingTargetExpansion.vertexEquiv hab hOne).symm_apply_eq.mpr rfl
  by_cases hSupport : ∀ edge ∈ GluingDatum.incidentEdges (target := contract incoming hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne edge = second edge
  · rw [ite_eq_left hSupport]
    apply Prod.ext
    · apply (incomingIso hc hab hOne second hPlacement).vertexEquiv.symm_apply_eq.mpr
      rw [incomingIso_vertex, hA]
      unfold normalizationIso
      rw [dite_eq_left hSupport]
      rfl
    · apply (incomingIso hc hab hOne second hPlacement).vertexEquiv.symm_apply_eq.mpr
      rw [incomingIso_vertex, hB]
      unfold normalizationIso
      rw [dite_eq_left hSupport]
      rfl
  · rw [ite_eq_right hSupport]
    apply Prod.ext
    · apply (incomingIso hc hab hOne second hPlacement).vertexEquiv.symm_apply_eq.mpr
      rw [incomingIso_vertex, hB]
      unfold normalizationIso
      rw [dite_eq_right hSupport]
      exact swapVertices_fresh.symm
    · apply (incomingIso hc hab hOne second hPlacement).vertexEquiv.symm_apply_eq.mpr
      rw [incomingIso_vertex, hA]
      unfold normalizationIso
      rw [dite_eq_right hSupport]
      exact swapVertices_old_wall.symm

/-- Unchanged outer vertex partitions are literally the contracted datum's
partitions; no representative normalization or source-isomorphism assumption. -/
theorem transported_vertexPartition_of_ne
    (vertex : (contract incoming hab hOne).V) (hOff : vertex ≠ ⟨a, hab⟩) :
    (GluingTransport.transport (incomingIso hc hab hOne second hPlacement) data).vertexPartition
      (oldVertex (contract incoming hab hOne) vertex) =
      (contractDatum data hc hab hOne).vertexPartition vertex := by
  exact (congrArg data.vertexPartition
    (incomingIso_symm_oldVertex hc hab hOne second hPlacement vertex hOff)).trans
      (contractVertexPartition_of_ne data a b (fun h => hOff (Subtype.ext h))).symm

/-- Every canonical transported occurrence has its original incoming partition
under the proved literal Option dictionary. -/
theorem transported_edgePartition_column
    (hConnected : graph_connected incoming) (hGenus : genus incoming = 0)
    (column : Option (contract incoming hab hOne).edges) :
    (GluingTransport.transport (incomingIso hc hab hOne second hPlacement) data).edgePartition
      (occurrenceEquiv (contract incoming hab hOne) ⟨a, hab⟩ second column) =
      data.edgePartition (incomingColumnEquiv hc hab hOne column) := by
  rw [GluingTransport.transport_edgePartition]
  exact congrArg data.edgePartition ((GluingTransport.edgeEquiv
    (incomingIso hc hab hOne second hPlacement)).symm_apply_eq.mpr
    (incomingIso_occurrence hc hab hOne second hPlacement hConnected hGenus column).symm)

/-- Each named retained occurrence keeps exactly its wall-data edge partition. -/
theorem transported_edgePartition_retained
    (hConnected : graph_connected incoming) (hGenus : genus incoming = 0)
    (edge : (contract incoming hab hOne).edges) :
    (GluingTransport.transport (incomingIso hc hab hOne second hPlacement) data).edgePartition
      (occurrenceEquiv (contract incoming hab hOne) ⟨a, hab⟩ second (some edge)) =
      (contractDatum data hc hab hOne).edgePartition edge :=
  transported_edgePartition_column data hc hab hOne second hPlacement hConnected hGenus (some edge)

/-- The new occurrence is the actual contracted incoming occurrence, with its
original partition, not a guessed selected-block resolution. -/
theorem transported_edgePartition_new
    (hConnected : graph_connected incoming) (hGenus : genus incoming = 0) :
    (GluingTransport.transport (incomingIso hc hab hOne second hPlacement) data).edgePartition
      (occurrenceEquiv (contract incoming hab hOne) ⟨a, hab⟩ second none) =
      data.edgePartition contracted :=
  transported_edgePartition_column data hc hab hOne second hPlacement hConnected hGenus none

/-- The only vertex partitions not already identified with the contracted
datum are exactly the two original endpoint partitions, ordered or swapped.
Their selected/background classification is not assumed or asserted here. -/
theorem transported_endpointPartitions :
    ((GluingTransport.transport (incomingIso hc hab hOne second hPlacement) data).vertexPartition
        (oldVertex (contract incoming hab hOne) ⟨a, hab⟩),
      (GluingTransport.transport (incomingIso hc hab hOne second hPlacement) data).vertexPartition
        (freshVertex (contract incoming hab hOne))) =
      if (∀ edge ∈ GluingDatum.incidentEdges (target := contract incoming hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = second edge)
      then (data.vertexPartition a, data.vertexPartition b)
      else (data.vertexPartition b, data.vertexPartition a) := by
  classical
  have h := congrArg (fun pair : incoming.V × incoming.V =>
    (data.vertexPartition pair.1, data.vertexPartition pair.2))
    (incomingIso_symm_endpoints hc hab hOne second hPlacement)
  split_ifs with hSupport
  · simp only [ite_eq_left hSupport] at h
    exact h
  · simp only [ite_eq_right hSupport] at h
    exact h

/-- The normalized split retains `a` as the leaf when `a` was the incoming leaf. -/
theorem split_endpointPartitions_of_leaf_left
    (star : W2R1Target.TwoStar (contract incoming hab hOne) ⟨a, hab⟩)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1) :
    ((GluingTransport.transport (splitIso hc hab hOne star (Or.inl hLeaf)) data).vertexPartition
        (oldVertex (contract incoming hab hOne) ⟨a, hab⟩),
      (GluingTransport.transport (splitIso hc hab hOne star (Or.inl hLeaf)) data).vertexPartition
        (freshVertex (contract incoming hab hOne))) =
      (data.vertexPartition a, data.vertexPartition b) := by
  have h := transported_endpointPartitions data hc hab hOne (fun _ => true)
    (splitPlacement hc hab hOne star (Or.inl hLeaf))
  have hSupport : ∀ edge ∈ GluingDatum.incidentEdges (target := contract incoming hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne edge = true := by
    intro edge hAt
    obtain ⟨label, hLabel⟩ := star.label.surjective ⟨edge, hAt⟩
    have hEdge : star.edge label = edge := congrArg Subtype.val hLabel
    rw [← hEdge]
    exact IncomingW2TargetPlacement.right_star_of_leaf_left hc hab hOne star hLeaf label
  simp only [ite_eq_left hSupport] at h
  exact h

/-- If `b` was the incoming leaf, normalization swaps the endpoint partitions. -/
theorem split_endpointPartitions_of_leaf_right
    (star : W2R1Target.TwoStar (contract incoming hab hOne) ⟨a, hab⟩)
    (hLeaf : (GluingDatum.incidentEdges b).card = 1) :
    ((GluingTransport.transport (splitIso hc hab hOne star (Or.inr hLeaf)) data).vertexPartition
        (oldVertex (contract incoming hab hOne) ⟨a, hab⟩),
      (GluingTransport.transport (splitIso hc hab hOne star (Or.inr hLeaf)) data).vertexPartition
        (freshVertex (contract incoming hab hOne))) =
      (data.vertexPartition b, data.vertexPartition a) := by
  have h := transported_endpointPartitions data hc hab hOne (fun _ => true)
    (splitPlacement hc hab hOne star (Or.inr hLeaf))
  have hNotSupport : ¬∀ edge ∈ GluingDatum.incidentEdges (target := contract incoming hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne edge = true := by
    intro hSupport
    have hTrue := hSupport (star.edge 0) (star.edge_mem_incidentEdges 0)
    rw [IncomingW2TargetPlacement.right_star_of_leaf_right hc hab hOne star hLeaf 0] at hTrue
    cases hTrue
  simp only [ite_eq_right hNotSupport] at h
  exact h

/-- For the actual joined orientation (label 1 at the fresh endpoint), the
incoming placement of that same named occurrence determines the endpoint pair. -/
theorem joined_endpointPartitions
    (star : W2R1Target.TwoStar (contract incoming hab hOne) ⟨a, hab⟩)
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2) :
    ((GluingTransport.transport (joinedIso hc hab hOne star hLeft hRight) data).vertexPartition
        (oldVertex (contract incoming hab hOne) ⟨a, hab⟩),
      (GluingTransport.transport (joinedIso hc hab hOne star hLeft hRight) data).vertexPartition
        (freshVertex (contract incoming hab hOne))) =
      if IncomingTargetExpansion.right hc hab hOne (star.edge 1) then
        (data.vertexPartition a, data.vertexPartition b)
      else (data.vertexPartition b, data.vertexPartition a) := by
  classical
  have h := transported_endpointPartitions data hc hab hOne star.right
    (joinedPlacement hc hab hOne star hLeft hRight)
  by_cases hSide : IncomingTargetExpansion.right hc hab hOne (star.edge 1) = true
  · have hSupport : ∀ edge ∈ GluingDatum.incidentEdges (target := contract incoming hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = star.right edge := by
      rcases joinedPlacement hc hab hOne star hLeft hRight with hSame | hSwap
      · exact hSame
      · have hFalse := hSwap (star.edge 1) (star.edge_mem_incidentEdges 1)
        rw [hSide, star.right_edge_one] at hFalse
        cases hFalse
    rw [ite_eq_left hSide]
    simp only [ite_eq_left hSupport] at h
    exact h
  · have hNotSupport : ¬∀ edge ∈ GluingDatum.incidentEdges (target := contract incoming hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = star.right edge := by
      intro hSupport
      have hTrue := hSupport (star.edge 1) (star.edge_mem_incidentEdges 1)
      exact hSide (hTrue.trans star.right_edge_one)
    rw [ite_eq_right hSide]
    simp only [ite_eq_right hNotSupport] at h
    exact h

end Incoming

end DraismaVargas.LocalCases.M11IncomingOuterPartitions
