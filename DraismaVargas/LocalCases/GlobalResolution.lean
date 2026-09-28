import DraismaVargas.Infrastructure.Change
import DraismaVargas.Infrastructure.TargetExpansion
import DraismaVargas.LocalCases.ResolutionM11
import Utilities.Iso.GraphContractionTopology

/-!
# Installing a local resolution in a global gluing datum

This file is the first assembly step from the local partition receipts to
actual outgoing Draisma--Vargas gluing data. Given an old gluing datum, a wall
vertex, an occurrence-wise assignment of old target edges to the two sides,
and a `LocalResolution`, it builds the expanded target datum.

The only additional premise is the exact exterior compatibility condition:
each retained old edge partition must refine the endpoint partition selected
by the expansion. Nonincident endpoints satisfy this from the old datum; the
local case figures prescribe it at the split wall. The distinguished new edge
uses `resolution.newEdge`, whose two refinements are already fields of
`LocalResolution`.
-/

namespace DraismaVargas.LocalCases.GlobalResolution

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases.ResolutionM11
open Utilities.Certificate

variable {target : CFGraph} {degree : ℕ}

/-- Vertex partition selected by a local resolution on the expanded target:
`left` lives at the retained wall and `right` at the fresh wall copy. -/
def expandedVertexPartition (data : GluingDatum target degree)
    (wall : target.V) (resolution : LocalResolution degree) :
    TargetExpansion.Vertex target → SheetPartition degree
  | Sum.inl vertex =>
      if vertex = wall then resolution.left else data.vertexPartition vertex
  | Sum.inr _ => resolution.right

@[simp] theorem expandedVertexPartition_old_wall
    (data : GluingDatum target degree) (wall : target.V)
    (resolution : LocalResolution degree) :
    expandedVertexPartition data wall resolution (oldVertex target wall) =
      resolution.left := by
  simp [expandedVertexPartition, oldVertex]

@[simp] theorem expandedVertexPartition_old_of_ne
    (data : GluingDatum target degree) (wall vertex : target.V)
    (resolution : LocalResolution degree) (hne : vertex ≠ wall) :
    expandedVertexPartition data wall resolution (oldVertex target vertex) =
      data.vertexPartition vertex := by
  simp [expandedVertexPartition, oldVertex, hne]

@[simp] theorem expandedVertexPartition_fresh
    (data : GluingDatum target degree) (wall : target.V)
    (resolution : LocalResolution degree) :
    expandedVertexPartition data wall resolution (freshVertex target) =
      resolution.right := by
  rfl

/-- Exact compatibility required from every retained old edge occurrence.
It is stated on the remapped endpoints, so parallel old occurrences may make
different choices at the wall. -/
def OldCompatible (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree) : Prop :=
  ∀ edge,
    (data.edgePartition edge).Refines
        (expandedVertexPartition data wall resolution
          (oldEnds target wall right edge).1) ∧
      (data.edgePartition edge).Refines
        (expandedVertexPartition data wall resolution
          (oldEnds target wall right edge).2)

/-- Exterior compatibility reduces to the edge partitions incident to the
wall. At every other endpoint it is inherited from the original datum. -/
theorem oldCompatible_of_wall
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hWall : ∀ edge : target.edges,
      ((edge : target.V × target.V).1 = wall ∨
        (edge : target.V × target.V).2 = wall) →
      (data.edgePartition edge).Refines
        (if right edge then resolution.right else resolution.left)) :
    OldCompatible data wall right resolution := by
  intro edge
  constructor
  · cases hRight : right edge with
    | false =>
        by_cases hEndpoint : (edge : target.V × target.V).1 = wall
        · simpa [oldEnds, expandedEndpoint, hRight, hEndpoint,
            expandedVertexPartition, oldVertex] using hWall edge (Or.inl hEndpoint)
        · simpa [oldEnds, expandedEndpoint, hRight, hEndpoint,
            expandedVertexPartition, oldVertex] using data.refines_left edge
    | true =>
        by_cases hEndpoint : (edge : target.V × target.V).1 = wall
        · simpa [oldEnds, expandedEndpoint, hRight, hEndpoint,
            expandedVertexPartition, oldVertex, freshVertex] using
              hWall edge (Or.inl hEndpoint)
        · simpa [oldEnds, expandedEndpoint, hRight, hEndpoint,
            expandedVertexPartition, oldVertex] using data.refines_left edge
  · cases hRight : right edge with
    | false =>
        by_cases hEndpoint : (edge : target.V × target.V).2 = wall
        · simpa [oldEnds, expandedEndpoint, hRight, hEndpoint,
            expandedVertexPartition, oldVertex] using hWall edge (Or.inr hEndpoint)
        · simpa [oldEnds, expandedEndpoint, hRight, hEndpoint,
            expandedVertexPartition, oldVertex] using data.refines_right edge
    | true =>
        by_cases hEndpoint : (edge : target.V × target.V).2 = wall
        · simpa [oldEnds, expandedEndpoint, hRight, hEndpoint,
            expandedVertexPartition, oldVertex, freshVertex] using
              hWall edge (Or.inr hEndpoint)
        · simpa [oldEnds, expandedEndpoint, hRight, hEndpoint,
            expandedVertexPartition, oldVertex] using data.refines_right edge

/-- Edge partition on an expanded occurrence, decoded through the literal
`Option oldOccurrence` equivalence. -/
noncomputable def expandedEdgePartition
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (edge : (TargetExpansion.graph target wall right).edges) :
    SheetPartition degree :=
  match (occurrenceEquiv target wall right).symm edge with
  | none => resolution.newEdge
  | some oldEdge => data.edgePartition oldEdge

@[simp] theorem expandedEdgePartition_new
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree) :
    expandedEdgePartition data wall right resolution
        (occurrenceEquiv target wall right none) = resolution.newEdge := by
  simp [expandedEdgePartition]

@[simp] theorem expandedEdgePartition_old
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (edge : target.edges) :
    expandedEdgePartition data wall right resolution
        (occurrenceEquiv target wall right (some edge)) =
      data.edgePartition edge := by
  simp [expandedEdgePartition]

/-- Install one local resolution into a global gluing datum. The constructor
is occurrence-safe: the inverse occurrence equivalence decides whether an
expanded edge is new or records its unique old emitter. -/
noncomputable def datum (data : GluingDatum target degree)
    (wall : target.V) (right : target.edges → Bool)
    (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution) :
    GluingDatum (TargetExpansion.graph target wall right) degree where
  degree_pos := data.degree_pos
  vertexPartition := expandedVertexPartition data wall resolution
  edgePartition := expandedEdgePartition data wall right resolution
  refines_left := by
    intro expandedEdge
    obtain ⟨label, rfl⟩ := (occurrenceEquiv target wall right).surjective expandedEdge
    cases label with
    | none =>
        rw [expandedEdgePartition_new, occurrenceEquiv_none]
        simpa [newEnds] using resolution.edge_refines_left
    | some edge =>
        rw [expandedEdgePartition_old, occurrenceEquiv_some]
        exact (hCompatible edge).1
  refines_right := by
    intro expandedEdge
    obtain ⟨label, rfl⟩ := (occurrenceEquiv target wall right).surjective expandedEdge
    cases label with
    | none =>
        rw [expandedEdgePartition_new, occurrenceEquiv_none]
        simpa [newEnds] using resolution.edge_refines_right
    | some edge =>
        rw [expandedEdgePartition_old, occurrenceEquiv_some]
        exact (hCompatible edge).2

/-- Contract an expanded quotient-source vertex back to the old quotient
source. At the split wall, either endpoint block is sent to its containing
old wall block. -/
def sourceVertexMap (data : GluingDatum target degree)
    (wall : target.V) (right : target.edges → Bool)
    (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (vertex : (datum data wall right resolution hCompatible).SourceVertex) :
    data.SourceVertex :=
  data.sourceEndpoint
    (contractVertex target wall vertex.1.1) vertex.1.2

/-- The quotient-source vertex map underlying contraction of the new target
edge. -/
def sourceContraction (data : GluingDatum target degree)
    (wall : target.V) (right : target.edges → Bool)
    (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution) :
    GraphContractionCertificate
      (datum data wall right resolution hCompatible).sourceGraph
      data.sourceGraph where
  vertexMap := sourceVertexMap data wall right resolution hCompatible

/-- Every old quotient-source vertex has a lift through the source
contraction. At the wall, choose its block in `resolution.left`; contraction
of the local resolution guarantees that this block remains inside the old
wall block. -/
theorem sourceVertexMap_surjective (data : GluingDatum target degree)
    (wall : target.V) (right : target.edges → Bool)
    (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hContracts : resolution.ContractsTo (data.vertexPartition wall)) :
    Function.Surjective
      (sourceVertexMap data wall right resolution hCompatible) := by
  intro old
  by_cases hVertex : old.1.1 = wall
  · let sheet : Fin degree := resolution.left.repr old.1.2
    let expandedVertex :
        (datum data wall right resolution hCompatible).SourceVertex :=
      ⟨(oldVertex target wall, sheet), by
        change ((datum data wall right resolution hCompatible).vertexPartition
          (oldVertex target wall)).repr sheet = sheet
        simp only [datum, expandedVertexPartition, oldVertex, if_pos]
        exact resolution.left.repr_idem old.1.2⟩
    refine ⟨expandedVertex, ?_⟩
    change data.sourceEndpoint wall sheet = old
    apply (data.sourceEndpoint_eq_iff wall sheet old).mpr
    refine ⟨hVertex.symm, ?_⟩
    have hLeft : resolution.left.Refines (data.vertexPartition wall) :=
      SheetPartition.IsJoin.left_refines hContracts
    exact hLeft.rel (resolution.left.rel_repr_left old.1.2)
  · let expandedVertex :
        (datum data wall right resolution hCompatible).SourceVertex :=
      ⟨(oldVertex target old.1.1, old.1.2), by
        change ((datum data wall right resolution hCompatible).vertexPartition
          (oldVertex target old.1.1)).repr old.1.2 = old.1.2
        simp only [datum, expandedVertexPartition, oldVertex, if_neg hVertex]
        exact old.2⟩
    refine ⟨expandedVertex, ?_⟩
    change data.sourceEndpoint old.1.1 old.1.2 = old
    apply (data.sourceEndpoint_eq_iff old.1.1 old.1.2 old).mpr
    exact ⟨rfl, rfl⟩

theorem sourceContraction_surjective (data : GluingDatum target degree)
    (wall : target.V) (right : target.edges → Bool)
    (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hContracts : resolution.ContractsTo (data.vertexPartition wall)) :
    Function.Surjective
      (sourceContraction data wall right resolution hCompatible).vertexMap :=
  sourceVertexMap_surjective data wall right resolution hCompatible hContracts

@[simp] theorem datum_vertexPartition_old_wall
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution) :
    (datum data wall right resolution hCompatible).vertexPartition
        (oldVertex target wall) = resolution.left := by
  exact expandedVertexPartition_old_wall data wall resolution

@[simp] theorem datum_vertexPartition_old_of_ne
    (data : GluingDatum target degree) (wall vertex : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hne : vertex ≠ wall) :
    (datum data wall right resolution hCompatible).vertexPartition
        (oldVertex target vertex) = data.vertexPartition vertex := by
  exact expandedVertexPartition_old_of_ne data wall vertex resolution hne

@[simp] theorem datum_vertexPartition_fresh
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution) :
    (datum data wall right resolution hCompatible).vertexPartition
        (freshVertex target) = resolution.right := by
  rfl

@[simp] theorem datum_edgePartition_new
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution) :
    (datum data wall right resolution hCompatible).edgePartition
        (occurrenceEquiv target wall right none) = resolution.newEdge := by
  exact expandedEdgePartition_new data wall right resolution

@[simp] theorem datum_edgePartition_old
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (edge : target.edges) :
    (datum data wall right resolution hCompatible).edgePartition
        (occurrenceEquiv target wall right (some edge)) =
      data.edgePartition edge := by
  exact expandedEdgePartition_old data wall right resolution edge

/-- The edge partitions on a canonical split-endpoint incidence list are the
new-edge partition followed by the old wall-edge partitions assigned to that
side. This is the exact list shape used by the local case receipts. -/
theorem datum_edgePartitions_incidentList
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution) (side : Bool) :
    (incidentList target wall right side).map
        (datum data wall right resolution hCompatible).edgePartition =
      resolution.newEdge ::
        (wallEdgesAssigned target wall right side).toList.map
          data.edgePartition := by
  simp [incidentList, List.map_map]

/-- Quotient-source vertex above the retained wall block containing `sheet`. -/
noncomputable def leftSourceVertex (data : GluingDatum target degree)
    (wall : target.V) (right : target.edges → Bool)
    (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (sheet : Fin degree) :
    (datum data wall right resolution hCompatible).SourceVertex :=
  (datum data wall right resolution hCompatible).sourceEndpoint
    (oldVertex target wall) sheet

/-- Quotient-source vertex above the fresh wall block containing `sheet`. -/
noncomputable def rightSourceVertex (data : GluingDatum target degree)
    (wall : target.V) (right : target.edges → Bool)
    (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (sheet : Fin degree) :
    (datum data wall right resolution hCompatible).SourceVertex :=
  (datum data wall right resolution hCompatible).sourceEndpoint
    (freshVertex target) sheet

/-- The new quotient-source edge block containing `sheet`. -/
noncomputable def newSourceEdge (data : GluingDatum target degree)
    (wall : target.V) (right : target.edges → Bool)
    (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (sheet : Fin degree) :
    (datum data wall right resolution hCompatible).SourceEdge :=
  ⟨(occurrenceEquiv target wall right none, resolution.newEdge.repr sheet), by
    change ((datum data wall right resolution hCompatible).edgePartition
      (occurrenceEquiv target wall right none)).repr
        (resolution.newEdge.repr sheet) = resolution.newEdge.repr sheet
    rw [datum_edgePartition_new]
    exact resolution.newEdge.repr_idem sheet⟩

/-- The dilation index of the new quotient-source occurrence is the block
cardinality of the pasted new-edge partition through the chosen sheet. -/
@[simp] theorem sourceEdgeIndex_newSourceEdge
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (sheet : Fin degree) :
    (datum data wall right resolution hCompatible).sourceEdgeIndex
        (newSourceEdge data wall right resolution hCompatible sheet) =
      resolution.newEdge.blockCard sheet := by
  unfold GluingDatum.sourceEdgeIndex newSourceEdge
  rw [datum_edgePartition_new]
  simpa [SheetPartition.blockCard] using congrArg Finset.card
    (resolution.newEdge.block_eq_of_rel
      (resolution.newEdge.rel_repr_left sheet))

/-- The new source edge really joins the left and right endpoint blocks of
its sheet. Refinement of `newEdge` to both endpoint partitions is exactly what
makes the two canonical representatives agree. -/
@[simp] theorem sourceEnds_newSourceEdge
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (sheet : Fin degree) :
    (datum data wall right resolution hCompatible).sourceEnds
        (newSourceEdge data wall right resolution hCompatible sheet) =
      (leftSourceVertex data wall right resolution hCompatible sheet,
        rightSourceVertex data wall right resolution hCompatible sheet) := by
  apply Prod.ext
  · change (datum data wall right resolution hCompatible).sourceEndpoint
      ((occurrenceEquiv target wall right none).1).1
      (resolution.newEdge.repr sheet) =
        leftSourceVertex data wall right resolution hCompatible sheet
    rw [occurrenceEquiv_none]
    apply ((datum data wall right resolution hCompatible).sourceEndpoint_eq_iff
      (oldVertex target wall) (resolution.newEdge.repr sheet)
      (leftSourceVertex data wall right resolution hCompatible sheet)).mpr
    refine ⟨rfl, ?_⟩
    simp only [leftSourceVertex, GluingDatum.sourceEndpoint]
    rw [datum_vertexPartition_old_wall]
    simpa [SheetPartition.Rel, resolution.left.repr_idem] using
      resolution.edge_refines_left.rel
        (resolution.newEdge.rel_repr_left sheet)
  · change (datum data wall right resolution hCompatible).sourceEndpoint
      ((occurrenceEquiv target wall right none).1).2
      (resolution.newEdge.repr sheet) =
        rightSourceVertex data wall right resolution hCompatible sheet
    rw [occurrenceEquiv_none]
    apply ((datum data wall right resolution hCompatible).sourceEndpoint_eq_iff
      (freshVertex target) (resolution.newEdge.repr sheet)
      (rightSourceVertex data wall right resolution hCompatible sheet)).mpr
    refine ⟨rfl, ?_⟩
    simp only [rightSourceVertex, GluingDatum.sourceEndpoint]
    rw [datum_vertexPartition_fresh]
    simpa [SheetPartition.Rel, resolution.right.repr_idem] using
      resolution.edge_refines_right.rel
        (resolution.newEdge.rel_repr_left sheet)

theorem sourceEnds_newSourceEdge_mem
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (sheet : Fin degree) :
    (datum data wall right resolution hCompatible).sourceEnds
        (newSourceEdge data wall right resolution hCompatible sheet) ∈
      (datum data wall right resolution hCompatible).sourceGraph.edges := by
  unfold GluingDatum.sourceGraph
  apply Multiset.mem_map.mpr
  exact ⟨newSourceEdge data wall right resolution hCompatible sheet, by simp, rfl⟩

/-- Each sheet gives a positive-multiplicity new quotient-source edge between
its left and right wall blocks. -/
theorem newSourceEdge_num_edges_pos
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (sheet : Fin degree) :
    0 < num_edges (datum data wall right resolution hCompatible).sourceGraph
      (leftSourceVertex data wall right resolution hCompatible sheet)
      (rightSourceVertex data wall right resolution hCompatible sheet) := by
  unfold num_edges
  rw [Multiset.card_pos_iff_exists_mem]
  refine ⟨(leftSourceVertex data wall right resolution hCompatible sheet,
    rightSourceVertex data wall right resolution hCompatible sheet),
      Multiset.mem_filter.mpr ⟨?_, Or.inl rfl⟩⟩
  unfold GluingDatum.sourceGraph
  apply Multiset.mem_map.mpr
  exact ⟨newSourceEdge data wall right resolution hCompatible sheet, by simp,
    sourceEnds_newSourceEdge data wall right resolution hCompatible sheet⟩

theorem newSourceEdge_num_edges_pos_reverse
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (sheet : Fin degree) :
    0 < num_edges (datum data wall right resolution hCompatible).sourceGraph
      (rightSourceVertex data wall right resolution hCompatible sheet)
      (leftSourceVertex data wall right resolution hCompatible sheet) := by
  unfold num_edges
  rw [Multiset.card_pos_iff_exists_mem]
  refine ⟨(leftSourceVertex data wall right resolution hCompatible sheet,
    rightSourceVertex data wall right resolution hCompatible sheet),
      Multiset.mem_filter.mpr ⟨?_, Or.inr rfl⟩⟩
  unfold GluingDatum.sourceGraph
  apply Multiset.mem_map.mpr
  exact ⟨newSourceEdge data wall right resolution hCompatible sheet, by simp,
    sourceEnds_newSourceEdge data wall right resolution hCompatible sheet⟩

theorem leftSourceVertex_eq_of_rel
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    {first second : Fin degree} (hRel : resolution.left.Rel first second) :
    leftSourceVertex data wall right resolution hCompatible first =
      leftSourceVertex data wall right resolution hCompatible second := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · simp only [leftSourceVertex, GluingDatum.sourceEndpoint]
    rw [datum_vertexPartition_old_wall]
    exact hRel

theorem rightSourceVertex_eq_of_rel
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    {first second : Fin degree} (hRel : resolution.right.Rel first second) :
    rightSourceVertex data wall right resolution hCompatible first =
      rightSourceVertex data wall right resolution hCompatible second := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · simp only [rightSourceVertex, GluingDatum.sourceEndpoint]
    rw [datum_vertexPartition_fresh]
    exact hRel

/-- A cut with no crossing source edge cannot separate the two endpoint
blocks joined by the new edge on any sheet. -/
theorem leftSourceVertex_mem_iff_rightSourceVertex
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (cut : Finset (datum data wall right resolution hCompatible).SourceVertex)
    (hNoCross : ¬ ∃ inside ∈ cut, ∃ outside ∉ cut,
      0 < num_edges (datum data wall right resolution hCompatible).sourceGraph
        inside outside)
    (sheet : Fin degree) :
    (leftSourceVertex data wall right resolution hCompatible sheet ∈ cut ↔
      rightSourceVertex data wall right resolution hCompatible sheet ∈ cut) := by
  constructor
  · intro hLeft
    by_contra hRight
    exact hNoCross ⟨leftSourceVertex data wall right resolution hCompatible sheet,
      hLeft, rightSourceVertex data wall right resolution hCompatible sheet,
      hRight, newSourceEdge_num_edges_pos data wall right resolution hCompatible sheet⟩
  · intro hRight
    by_contra hLeft
    exact hNoCross ⟨rightSourceVertex data wall right resolution hCompatible sheet,
      hRight, leftSourceVertex data wall right resolution hCompatible sheet,
      hLeft,
      newSourceEdge_num_edges_pos_reverse data wall right resolution hCompatible sheet⟩

/-- If no new occurrence crosses a source cut, all left endpoint blocks
inside one old wall block lie on the same side. Old occurrences may cross.
The proof follows the generated relation in `ContractsTo`; right-relation
steps use only the side equality across the new edge on each sheet. -/
theorem leftSourceVertex_mem_iff_of_wall_rel_of_new_edges
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hContracts : resolution.ContractsTo (data.vertexPartition wall))
    (cut : Finset (datum data wall right resolution hCompatible).SourceVertex)
    (hBridge : ∀ sheet : Fin degree,
      leftSourceVertex data wall right resolution hCompatible sheet ∈ cut ↔
        rightSourceVertex data wall right resolution hCompatible sheet ∈ cut)
    {first second : Fin degree}
    (hWall : (data.vertexPartition wall).Rel first second) :
    (leftSourceVertex data wall right resolution hCompatible first ∈ cut ↔
      leftSourceVertex data wall right resolution hCompatible second ∈ cut) := by
  have hLeftRel : ∀ {i j : Fin degree}, resolution.left.Rel i j →
      (leftSourceVertex data wall right resolution hCompatible i ∈ cut ↔
        leftSourceVertex data wall right resolution hCompatible j ∈ cut) := by
    intro i j hij
    rw [leftSourceVertex_eq_of_rel data wall right resolution hCompatible hij]
  have hRightRel : ∀ {i j : Fin degree}, resolution.right.Rel i j →
      (leftSourceVertex data wall right resolution hCompatible i ∈ cut ↔
        leftSourceVertex data wall right resolution hCompatible j ∈ cut) := by
    intro i j hij
    have hRightIff :
        (rightSourceVertex data wall right resolution hCompatible i ∈ cut ↔
          rightSourceVertex data wall right resolution hCompatible j ∈ cut) := by
      rw [rightSourceVertex_eq_of_rel data wall right resolution hCompatible hij]
    exact (hBridge i).trans (hRightIff.trans (hBridge j).symm)
  have hGenerated := (hContracts first second).mp hWall
  have hProp : ∀ {i j : Fin degree},
      Relation.EqvGen
          (fun a b ↦ resolution.left.Rel a b ∨ resolution.right.Rel a b) i j →
        (leftSourceVertex data wall right resolution hCompatible i ∈ cut ↔
          leftSourceVertex data wall right resolution hCompatible j ∈ cut) := by
    intro i j hij
    induction hij with
    | rel i j hij => exact hij.elim hLeftRel hRightRel
    | refl i => exact Iff.rfl
    | symm i j _ ih => exact ih.symm
    | trans i j k _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond
  exact hProp hGenerated

/-- Compatibility form for a cut with no crossing occurrence of any kind. -/
theorem leftSourceVertex_mem_iff_of_wall_rel
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hContracts : resolution.ContractsTo (data.vertexPartition wall))
    (cut : Finset (datum data wall right resolution hCompatible).SourceVertex)
    (hNoCross : ¬ ∃ inside ∈ cut, ∃ outside ∉ cut,
      0 < num_edges (datum data wall right resolution hCompatible).sourceGraph
        inside outside)
    {first second : Fin degree}
    (hWall : (data.vertexPartition wall).Rel first second) :
    (leftSourceVertex data wall right resolution hCompatible first ∈ cut ↔
      leftSourceVertex data wall right resolution hCompatible second ∈ cut) :=
  leftSourceVertex_mem_iff_of_wall_rel_of_new_edges data wall right resolution
    hCompatible hContracts cut
    (leftSourceVertex_mem_iff_rightSourceVertex data wall right resolution hCompatible cut hNoCross) hWall

theorem sourceVertex_eq_left_of_target_eq
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (vertex : (datum data wall right resolution hCompatible).SourceVertex)
    (hTarget : vertex.1.1 = oldVertex target wall) :
    vertex = leftSourceVertex data wall right resolution hCompatible vertex.1.2 := by
  apply Subtype.ext
  apply Prod.ext
  · exact hTarget
  · have hFixed := vertex.2
    rw [hTarget] at hFixed
    exact hFixed.symm

theorem sourceVertex_eq_right_of_target_eq
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (vertex : (datum data wall right resolution hCompatible).SourceVertex)
    (hTarget : vertex.1.1 = freshVertex target) :
    vertex = rightSourceVertex data wall right resolution hCompatible vertex.1.2 := by
  apply Subtype.ext
  apply Prod.ext
  · exact hTarget
  · have hFixed := vertex.2
    rw [hTarget] at hFixed
    exact hFixed.symm

/-- A cut not crossed by any new occurrence is saturated on source-contraction
fibres. This includes separating cuts crossed by one retained old occurrence.
Away from the wall the fibres are singletons; over the wall `ContractsTo`
and the new-edge side equalities give saturation. -/
theorem sourceVertex_mem_iff_of_sourceVertexMap_eq_of_new_edges
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hContracts : resolution.ContractsTo (data.vertexPartition wall))
    (cut : Finset (datum data wall right resolution hCompatible).SourceVertex)
    (hBridge : ∀ sheet : Fin degree,
      leftSourceVertex data wall right resolution hCompatible sheet ∈ cut ↔
        rightSourceVertex data wall right resolution hCompatible sheet ∈ cut)
    (first second : (datum data wall right resolution hCompatible).SourceVertex)
    (hMap : sourceVertexMap data wall right resolution hCompatible first =
      sourceVertexMap data wall right resolution hCompatible second) :
    (first ∈ cut ↔ second ∈ cut) := by
  cases hFirstTarget : first.1.1 with
  | inl firstTarget =>
      cases hSecondTarget : second.1.1 with
      | inl secondTarget =>
          have hTarget : firstTarget = secondTarget := by
            have h := congrArg (fun vertex : data.SourceVertex ↦ vertex.1.1) hMap
            simpa [sourceVertexMap, GluingDatum.sourceEndpoint, contractVertex,
              hFirstTarget, hSecondTarget] using h
          subst secondTarget
          by_cases hWallTarget : firstTarget = wall
          · subst firstTarget
            have hWallRel : (data.vertexPartition wall).Rel first.1.2 second.1.2 := by
              have h := congrArg (fun vertex : data.SourceVertex ↦ vertex.1.2) hMap
              simpa [SheetPartition.Rel, sourceVertexMap, GluingDatum.sourceEndpoint,
                contractVertex, hFirstTarget, hSecondTarget] using h
            have hFirstCanonical := sourceVertex_eq_left_of_target_eq
              data wall right resolution hCompatible first (by
                simpa [oldVertex] using hFirstTarget)
            have hSecondCanonical := sourceVertex_eq_left_of_target_eq
              data wall right resolution hCompatible second (by
                simpa [oldVertex] using hSecondTarget)
            rw [hFirstCanonical, hSecondCanonical]
            exact leftSourceVertex_mem_iff_of_wall_rel_of_new_edges data wall right resolution
              hCompatible hContracts cut hBridge hWallRel
          · have hFirstFixed := first.2
            rw [hFirstTarget] at hFirstFixed
            simp only [datum, expandedVertexPartition, if_neg hWallTarget] at hFirstFixed
            have hSecondFixed := second.2
            rw [hSecondTarget] at hSecondFixed
            simp only [datum, expandedVertexPartition, if_neg hWallTarget] at hSecondFixed
            have hRepresentatives :
                (data.vertexPartition firstTarget).repr first.1.2 =
                  (data.vertexPartition firstTarget).repr second.1.2 := by
              have h := congrArg (fun vertex : data.SourceVertex ↦ vertex.1.2) hMap
              simpa [sourceVertexMap, GluingDatum.sourceEndpoint, contractVertex,
                hFirstTarget, hSecondTarget] using h
            have hSheets : first.1.2 = second.1.2 :=
              hFirstFixed.symm.trans (hRepresentatives.trans hSecondFixed)
            have hVertices : first = second := by
              apply Subtype.ext
              apply Prod.ext
              · exact hFirstTarget.trans hSecondTarget.symm
              · exact hSheets
            rw [hVertices]
      | inr secondFresh =>
          cases secondFresh
          have hTarget : firstTarget = wall := by
            have h := congrArg (fun vertex : data.SourceVertex ↦ vertex.1.1) hMap
            simpa [sourceVertexMap, GluingDatum.sourceEndpoint, contractVertex,
              hFirstTarget, hSecondTarget] using h
          subst firstTarget
          have hWallRel : (data.vertexPartition wall).Rel first.1.2 second.1.2 := by
            have h := congrArg (fun vertex : data.SourceVertex ↦ vertex.1.2) hMap
            simpa [SheetPartition.Rel, sourceVertexMap, GluingDatum.sourceEndpoint,
              contractVertex, hFirstTarget, hSecondTarget] using h
          have hFirstCanonical := sourceVertex_eq_left_of_target_eq
            data wall right resolution hCompatible first (by
              simpa [oldVertex] using hFirstTarget)
          have hSecondCanonical := sourceVertex_eq_right_of_target_eq
            data wall right resolution hCompatible second (by
              simpa [freshVertex] using hSecondTarget)
          rw [hFirstCanonical, hSecondCanonical]
          exact (leftSourceVertex_mem_iff_of_wall_rel_of_new_edges data wall right resolution
            hCompatible hContracts cut hBridge hWallRel).trans (hBridge second.1.2)
  | inr firstFresh =>
      cases firstFresh
      cases hSecondTarget : second.1.1 with
      | inl secondTarget =>
          have hTarget : wall = secondTarget := by
            have h := congrArg (fun vertex : data.SourceVertex ↦ vertex.1.1) hMap
            simpa [sourceVertexMap, GluingDatum.sourceEndpoint, contractVertex,
              hFirstTarget, hSecondTarget] using h
          subst secondTarget
          have hWallRel : (data.vertexPartition wall).Rel first.1.2 second.1.2 := by
            have h := congrArg (fun vertex : data.SourceVertex ↦ vertex.1.2) hMap
            simpa [SheetPartition.Rel, sourceVertexMap, GluingDatum.sourceEndpoint,
              contractVertex, hFirstTarget, hSecondTarget] using h
          have hFirstCanonical := sourceVertex_eq_right_of_target_eq
            data wall right resolution hCompatible first (by
              simpa [freshVertex] using hFirstTarget)
          have hSecondCanonical := sourceVertex_eq_left_of_target_eq
            data wall right resolution hCompatible second (by
              simpa [oldVertex] using hSecondTarget)
          rw [hFirstCanonical, hSecondCanonical]
          exact (hBridge first.1.2).symm.trans
              (leftSourceVertex_mem_iff_of_wall_rel_of_new_edges data wall right resolution
                hCompatible hContracts cut hBridge hWallRel)
      | inr secondFresh =>
          cases secondFresh
          have hWallRel : (data.vertexPartition wall).Rel first.1.2 second.1.2 := by
            have h := congrArg (fun vertex : data.SourceVertex ↦ vertex.1.2) hMap
            simpa [SheetPartition.Rel, sourceVertexMap, GluingDatum.sourceEndpoint,
              contractVertex, hFirstTarget, hSecondTarget] using h
          have hFirstCanonical := sourceVertex_eq_right_of_target_eq
            data wall right resolution hCompatible first (by
              simpa [freshVertex] using hFirstTarget)
          have hSecondCanonical := sourceVertex_eq_right_of_target_eq
            data wall right resolution hCompatible second (by
              simpa [freshVertex] using hSecondTarget)
          rw [hFirstCanonical, hSecondCanonical]
          exact (hBridge first.1.2).symm.trans
              ((leftSourceVertex_mem_iff_of_wall_rel_of_new_edges data wall right resolution
                hCompatible hContracts cut hBridge hWallRel).trans (hBridge second.1.2))

/-- The no-crossing form, which the connectedness arguments use, follows from
the new-edge-only saturation theorem. -/
theorem sourceVertex_mem_iff_of_sourceVertexMap_eq
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hContracts : resolution.ContractsTo (data.vertexPartition wall))
    (cut : Finset (datum data wall right resolution hCompatible).SourceVertex)
    (hNoCross : ¬ ∃ inside ∈ cut, ∃ outside ∉ cut,
      0 < num_edges (datum data wall right resolution hCompatible).sourceGraph
        inside outside)
    (first second : (datum data wall right resolution hCompatible).SourceVertex)
    (hMap : sourceVertexMap data wall right resolution hCompatible first =
      sourceVertexMap data wall right resolution hCompatible second) :
    (first ∈ cut ↔ second ∈ cut) :=
  sourceVertex_mem_iff_of_sourceVertexMap_eq_of_new_edges data wall right resolution
    hCompatible hContracts cut
    (leftSourceVertex_mem_iff_rightSourceVertex data wall right resolution hCompatible cut hNoCross)
    first second hMap

/-- Every expanded endpoint partition refines the old partition at its
contracted target vertex. -/
theorem expandedVertexPartition_refines_contract
    (data : GluingDatum target degree) (wall : target.V)
    (resolution : LocalResolution degree)
    (hContracts : resolution.ContractsTo (data.vertexPartition wall))
    (vertex : TargetExpansion.Vertex target) :
    (expandedVertexPartition data wall resolution vertex).Refines
      (data.vertexPartition (contractVertex target wall vertex)) := by
  cases vertex with
  | inl vertex =>
      by_cases hVertex : vertex = wall
      · subst vertex
        simpa [expandedVertexPartition, contractVertex] using
          SheetPartition.IsJoin.left_refines hContracts
      · simp [expandedVertexPartition, contractVertex, hVertex,
          SheetPartition.Refines.refl]
  | inr fresh =>
      cases fresh
      simpa [expandedVertexPartition, contractVertex] using
        SheetPartition.IsJoin.right_refines hContracts

/-- Contracting a canonical expanded source endpoint recovers the canonical
old source endpoint of the same sheet. -/
theorem sourceVertexMap_sourceEndpoint
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hContracts : resolution.ContractsTo (data.vertexPartition wall))
    (vertex : TargetExpansion.Vertex target) (sheet : Fin degree) :
    sourceVertexMap data wall right resolution hCompatible
        ((datum data wall right resolution hCompatible).sourceEndpoint vertex sheet) =
      data.sourceEndpoint (contractVertex target wall vertex) sheet := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact (expandedVertexPartition_refines_contract data wall resolution
      hContracts vertex).rel
        ((expandedVertexPartition data wall resolution vertex).rel_repr_left sheet)

/-- Lift an old quotient-source edge block to the retained old target
occurrence in the resolved datum. -/
noncomputable def oldSourceEdge (data : GluingDatum target degree)
    (wall : target.V) (right : target.edges → Bool)
    (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (edge : data.SourceEdge) :
    (datum data wall right resolution hCompatible).SourceEdge :=
  ⟨(occurrenceEquiv target wall right (some edge.1.1), edge.1.2), by
    change ((datum data wall right resolution hCompatible).edgePartition
      (occurrenceEquiv target wall right (some edge.1.1))).repr edge.1.2 = edge.1.2
    rw [datum_edgePartition_old]
    exact edge.2⟩

/-- Lifting a retained old source occurrence preserves its dilation index
literally. -/
@[simp] theorem sourceEdgeIndex_oldSourceEdge
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (edge : data.SourceEdge) :
    (datum data wall right resolution hCompatible).sourceEdgeIndex
        (oldSourceEdge data wall right resolution hCompatible edge) =
      data.sourceEdgeIndex edge := by
  unfold GluingDatum.sourceEdgeIndex oldSourceEdge
  rw [datum_edgePartition_old]

/-- The endpoints of a lifted old source edge contract literally to the old
source-edge endpoints. -/
@[simp] theorem sourceVertexMap_sourceEnds_oldSourceEdge
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hContracts : resolution.ContractsTo (data.vertexPartition wall))
    (edge : data.SourceEdge) :
    (sourceVertexMap data wall right resolution hCompatible
        ((datum data wall right resolution hCompatible).sourceEnds
          (oldSourceEdge data wall right resolution hCompatible edge)).1,
      sourceVertexMap data wall right resolution hCompatible
        ((datum data wall right resolution hCompatible).sourceEnds
          (oldSourceEdge data wall right resolution hCompatible edge)).2) =
      data.sourceEnds edge := by
  apply Prod.ext
  · change sourceVertexMap data wall right resolution hCompatible
        ((datum data wall right resolution hCompatible).sourceEndpoint
          ((occurrenceEquiv target wall right (some edge.1.1)).1).1 edge.1.2) =
      data.sourceEndpoint (edge.1.1 : target.V × target.V).1 edge.1.2
    rw [occurrenceEquiv_some]
    simpa [oldEnds] using sourceVertexMap_sourceEndpoint data wall right resolution
      hCompatible hContracts (oldEnds target wall right edge.1.1).1 edge.1.2
  · change sourceVertexMap data wall right resolution hCompatible
        ((datum data wall right resolution hCompatible).sourceEndpoint
          ((occurrenceEquiv target wall right (some edge.1.1)).1).2 edge.1.2) =
      data.sourceEndpoint (edge.1.1 : target.V × target.V).2 edge.1.2
    rw [occurrenceEquiv_some]
    simpa [oldEnds] using sourceVertexMap_sourceEndpoint data wall right resolution
      hCompatible hContracts (oldEnds target wall right edge.1.1).2 edge.1.2

theorem sourceEnds_oldSourceEdge_mem
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (edge : data.SourceEdge) :
    (datum data wall right resolution hCompatible).sourceEnds
        (oldSourceEdge data wall right resolution hCompatible edge) ∈
      (datum data wall right resolution hCompatible).sourceGraph.edges := by
  unfold GluingDatum.sourceGraph
  apply Multiset.mem_map.mpr
  exact ⟨oldSourceEdge data wall right resolution hCompatible edge, by simp, rfl⟩

theorem oldSourceEdge_num_edges_pos
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (edge : data.SourceEdge) :
    0 < num_edges (datum data wall right resolution hCompatible).sourceGraph
      ((datum data wall right resolution hCompatible).sourceEnds
        (oldSourceEdge data wall right resolution hCompatible edge)).1
      ((datum data wall right resolution hCompatible).sourceEnds
        (oldSourceEdge data wall right resolution hCompatible edge)).2 := by
  unfold num_edges
  rw [Multiset.card_pos_iff_exists_mem]
  refine ⟨(datum data wall right resolution hCompatible).sourceEnds
      (oldSourceEdge data wall right resolution hCompatible edge),
        Multiset.mem_filter.mpr ⟨?_, Or.inl rfl⟩⟩
  exact sourceEnds_oldSourceEdge_mem data wall right resolution hCompatible edge

theorem oldSourceEdge_num_edges_pos_reverse
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (edge : data.SourceEdge) :
    0 < num_edges (datum data wall right resolution hCompatible).sourceGraph
      ((datum data wall right resolution hCompatible).sourceEnds
        (oldSourceEdge data wall right resolution hCompatible edge)).2
      ((datum data wall right resolution hCompatible).sourceEnds
        (oldSourceEdge data wall right resolution hCompatible edge)).1 := by
  unfold num_edges
  rw [Multiset.card_pos_iff_exists_mem]
  refine ⟨(datum data wall right resolution hCompatible).sourceEnds
      (oldSourceEdge data wall right resolution hCompatible edge),
        Multiset.mem_filter.mpr ⟨?_, Or.inr rfl⟩⟩
  exact sourceEnds_oldSourceEdge_mem data wall right resolution hCompatible edge

/-- Local resolution preserves connectedness of the quotient source. A
crossing-free expanded cut is saturated on source-contraction fibres, hence
descends to a nontrivial old source cut. Any old crossing source edge has the
explicit lift constructed above, giving the contradiction. -/
theorem datum_connected
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hContracts : resolution.ContractsTo (data.vertexPartition wall))
    (hConnected : data.Connected) :
    (datum data wall right resolution hCompatible).Connected := by
  intro cut hSplit
  classical
  by_contra hNoCross
  let oldCut : Finset data.SourceVertex :=
    cut.image (sourceVertexMap data wall right resolution hCompatible)
  obtain ⟨inside, outside, hInside, hOutside⟩ := hSplit
  have hInsideOld :
      sourceVertexMap data wall right resolution hCompatible inside ∈ oldCut :=
    Finset.mem_image.mpr ⟨inside, hInside, rfl⟩
  have hOutsideOld :
      sourceVertexMap data wall right resolution hCompatible outside ∉ oldCut := by
    intro hOutsideImage
    obtain ⟨source, hSource, hSourceMap⟩ := Finset.mem_image.mp hOutsideImage
    have hSameSide := sourceVertex_mem_iff_of_sourceVertexMap_eq data wall right
      resolution hCompatible hContracts cut hNoCross source outside hSourceMap
    exact hOutside (hSameSide.mp hSource)
  obtain ⟨first, hFirst, second, hSecond, hCrossing⟩ :=
    hConnected oldCut ⟨_, _, hInsideOld, hOutsideOld⟩
  unfold num_edges at hCrossing
  obtain ⟨pair, hPair⟩ := Multiset.card_pos_iff_exists_mem.mp hCrossing
  have hPairData := Multiset.mem_filter.mp hPair
  have hEmitter : ∃ edge : data.SourceEdge, data.sourceEnds edge = pair := by
    have hPairMem := hPairData.1
    change pair ∈ (Finset.univ : Finset data.SourceEdge).val.map data.sourceEnds at hPairMem
    obtain ⟨edge, _, hEnds⟩ := Multiset.mem_map.mp hPairMem
    exact ⟨edge, hEnds⟩
  obtain ⟨edge, hEnds⟩ := hEmitter
  let liftedFirst :=
    ((datum data wall right resolution hCompatible).sourceEnds
      (oldSourceEdge data wall right resolution hCompatible edge)).1
  let liftedSecond :=
    ((datum data wall right resolution hCompatible).sourceEnds
      (oldSourceEdge data wall right resolution hCompatible edge)).2
  have hMapped := sourceVertexMap_sourceEnds_oldSourceEdge data wall right
    resolution hCompatible hContracts edge
  rcases hPairData.2 with hOrder | hOrder
  · have hMapFirst :
        sourceVertexMap data wall right resolution hCompatible liftedFirst = first := by
      have h := congrArg Prod.fst hMapped
      simpa [liftedFirst, hEnds, hOrder] using h
    have hMapSecond :
        sourceVertexMap data wall right resolution hCompatible liftedSecond = second := by
      have h := congrArg Prod.snd hMapped
      simpa [liftedSecond, hEnds, hOrder] using h
    have hLiftedFirst : liftedFirst ∈ cut := by
      obtain ⟨source, hSource, hSourceMap⟩ := Finset.mem_image.mp hFirst
      have hSameSide := sourceVertex_mem_iff_of_sourceVertexMap_eq data wall right
        resolution hCompatible hContracts cut hNoCross source liftedFirst
          (hSourceMap.trans hMapFirst.symm)
      exact hSameSide.mp hSource
    have hLiftedSecond : liftedSecond ∉ cut := by
      intro hLifted
      exact hSecond (Finset.mem_image.mpr ⟨liftedSecond, hLifted, hMapSecond⟩)
    exact hNoCross ⟨liftedFirst, hLiftedFirst, liftedSecond, hLiftedSecond,
      oldSourceEdge_num_edges_pos data wall right resolution hCompatible edge⟩
  · have hMapFirst :
        sourceVertexMap data wall right resolution hCompatible liftedFirst = second := by
      have h := congrArg Prod.fst hMapped
      simpa [liftedFirst, hEnds, hOrder] using h
    have hMapSecond :
        sourceVertexMap data wall right resolution hCompatible liftedSecond = first := by
      have h := congrArg Prod.snd hMapped
      simpa [liftedSecond, hEnds, hOrder] using h
    have hLiftedSecond : liftedSecond ∈ cut := by
      obtain ⟨source, hSource, hSourceMap⟩ := Finset.mem_image.mp hFirst
      have hSameSide := sourceVertex_mem_iff_of_sourceVertexMap_eq data wall right
        resolution hCompatible hContracts cut hNoCross source liftedSecond
          (hSourceMap.trans hMapSecond.symm)
      exact hSameSide.mp hSource
    have hLiftedFirst : liftedFirst ∉ cut := by
      intro hLifted
      exact hSecond (Finset.mem_image.mpr ⟨liftedFirst, hLifted, hMapFirst⟩)
    exact hNoCross ⟨liftedSecond, hLiftedSecond, liftedFirst, hLiftedFirst,
      oldSourceEdge_num_edges_pos_reverse data wall right resolution hCompatible edge⟩

/-- At an unchanged target vertex, an expanded old occurrence is incident
exactly when its original occurrence was incident. -/
theorem oldOccurrence_mem_incidentEdges_old_iff
    (wall vertex : target.V) (right : target.edges → Bool)
    (hne : vertex ≠ wall) (edge : target.edges) :
    occurrenceEquiv target wall right (some edge) ∈
        GluingDatum.incidentEdges (oldVertex target vertex) ↔
      edge ∈ GluingDatum.incidentEdges vertex := by
  unfold GluingDatum.incidentEdges
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    occurrenceEquiv_some]
  change ((oldEnds target wall right edge).1 = oldVertex target vertex ∨
      (oldEnds target wall right edge).2 = oldVertex target vertex) ↔
    ((edge : target.V × target.V).1 = vertex ∨
      (edge : target.V × target.V).2 = vertex)
  simp only [oldEnds]
  rw [expandedEndpoint_eq_oldVertex_iff_of_ne target wall right edge
      (edge : target.V × target.V).1 vertex hne,
    expandedEndpoint_eq_oldVertex_iff_of_ne target wall right edge
      (edge : target.V × target.V).2 vertex hne]

/-- The new target edge is not incident to any unchanged old vertex. -/
theorem newOccurrence_not_mem_incidentEdges_old
    (wall vertex : target.V) (right : target.edges → Bool)
    (hne : vertex ≠ wall) :
    occurrenceEquiv target wall right none ∉
      GluingDatum.incidentEdges (oldVertex target vertex) := by
  unfold GluingDatum.incidentEdges
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    occurrenceEquiv_none]
  have hne' : wall ≠ vertex := Ne.symm hne
  change ¬(oldVertex target wall = oldVertex target vertex ∨
    freshVertex target = oldVertex target vertex)
  intro h
  rcases h with hOld | hFresh
  · exact hne' (Sum.inl.inj hOld)
  · cases hFresh

/-- Splitting another target vertex does not change the valency of an
unchanged old target vertex. -/
theorem incidentEdges_card_old_of_ne
    (wall vertex : target.V) (right : target.edges → Bool)
    (hne : vertex ≠ wall) :
    (GluingDatum.incidentEdges (oldVertex target vertex) :
      Finset (TargetExpansion.graph target wall right).edges).card =
        (GluingDatum.incidentEdges vertex : Finset target.edges).card := by
  classical
  let expandedIncident : Finset (TargetExpansion.graph target wall right).edges :=
    GluingDatum.incidentEdges (oldVertex target vertex)
  let oldIncident : Finset target.edges := GluingDatum.incidentEdges vertex
  have hExpandedCard : expandedIncident.card =
      ∑ edge : (TargetExpansion.graph target wall right).edges,
        if edge ∈ expandedIncident then 1 else 0 := by
    rw [← Finset.sum_filter]
    simp [expandedIncident]
  have hOldCard : oldIncident.card =
      ∑ edge : target.edges, if edge ∈ oldIncident then 1 else 0 := by
    rw [← Finset.sum_filter]
    simp [oldIncident]
  rw [hExpandedCard, hOldCard]
  symm
  calc
    (∑ edge : target.edges, if edge ∈ oldIncident then 1 else 0) =
        ∑ label : Option target.edges,
          if occurrenceEquiv target wall right label ∈ expandedIncident then 1 else 0 := by
      rw [Fintype.sum_option]
      simp [expandedIncident, oldIncident,
        newOccurrence_not_mem_incidentEdges_old wall vertex right hne,
        oldOccurrence_mem_incidentEdges_old_iff wall vertex right hne]
    _ = ∑ edge : (TargetExpansion.graph target wall right).edges,
          if edge ∈ expandedIncident then 1 else 0 := by
      apply Fintype.sum_equiv (occurrenceEquiv target wall right)
      intro label
      rfl

/-- The Riemann--Hurwitz incidence sum at an unchanged old target vertex is
literally preserved by target expansion. -/
theorem sum_blockCountWithin_old_of_ne
    (data : GluingDatum target degree) (wall vertex : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hne : vertex ≠ wall) (sheet : Fin degree) :
    (∑ edge ∈ GluingDatum.incidentEdges (oldVertex target vertex),
      ((datum data wall right resolution hCompatible).edgePartition edge).blockCountWithin
          ((datum data wall right resolution hCompatible).vertexPartition
            (oldVertex target vertex)) sheet : ℤ) =
      ∑ edge ∈ GluingDatum.incidentEdges vertex,
        ((data.edgePartition edge).blockCountWithin
          (data.vertexPartition vertex) sheet : ℤ) := by
  classical
  let expandedIncident : Finset (TargetExpansion.graph target wall right).edges :=
    GluingDatum.incidentEdges (oldVertex target vertex)
  let oldIncident : Finset target.edges := GluingDatum.incidentEdges vertex
  change (∑ edge ∈ expandedIncident,
      ((datum data wall right resolution hCompatible).edgePartition edge).blockCountWithin
          ((datum data wall right resolution hCompatible).vertexPartition
            (oldVertex target vertex)) sheet : ℤ) =
    ∑ edge ∈ oldIncident,
      ((data.edgePartition edge).blockCountWithin
        (data.vertexPartition vertex) sheet : ℤ)
  calc
    (∑ edge ∈ expandedIncident,
        ((datum data wall right resolution hCompatible).edgePartition edge).blockCountWithin
            ((datum data wall right resolution hCompatible).vertexPartition
              (oldVertex target vertex)) sheet : ℤ) =
        ∑ edge : (TargetExpansion.graph target wall right).edges,
        if edge ∈ expandedIncident then
          (((datum data wall right resolution hCompatible).edgePartition edge).blockCountWithin
              ((datum data wall right resolution hCompatible).vertexPartition
                (oldVertex target vertex)) sheet : ℤ)
        else 0 := by
      rw [← Finset.sum_filter]
      simp
    _ =
        ∑ label : Option target.edges,
          if occurrenceEquiv target wall right label ∈ expandedIncident then
            (((datum data wall right resolution hCompatible).edgePartition
              (occurrenceEquiv target wall right label)).blockCountWithin
                ((datum data wall right resolution hCompatible).vertexPartition
                  (oldVertex target vertex)) sheet : ℤ)
          else 0 := by
      symm
      apply Fintype.sum_equiv (occurrenceEquiv target wall right)
      intro label
      rfl
    _ = ∑ edge : target.edges,
        if edge ∈ oldIncident then
          ((data.edgePartition edge).blockCountWithin
            (data.vertexPartition vertex) sheet : ℤ)
        else 0 := by
      rw [Fintype.sum_option]
      simp [expandedIncident, oldIncident,
        newOccurrence_not_mem_incidentEdges_old wall vertex right hne,
        oldOccurrence_mem_incidentEdges_old_iff wall vertex right hne,
        datum_edgePartition_old, datum_vertexPartition_old_of_ne, hne]
    _ = ∑ edge ∈ oldIncident,
        ((data.edgePartition edge).blockCountWithin
          (data.vertexPartition vertex) sheet : ℤ) := by
      rw [← Finset.sum_filter]
      simp

/-- At an unchanged target vertex, the sum of the source edge-block counts is
preserved by target expansion. -/
theorem sum_edgeBlockCard_old_of_ne
    (data : GluingDatum target degree) (wall vertex : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hne : vertex ≠ wall) :
    (∑ edge ∈ GluingDatum.incidentEdges (oldVertex target vertex),
      (Fintype.card
        ((datum data wall right resolution hCompatible).edgePartition edge).Blocks :
          ℤ)) =
      ∑ edge ∈ GluingDatum.incidentEdges vertex,
        (Fintype.card (data.edgePartition edge).Blocks : ℤ) := by
  classical
  let expandedIncident :
      Finset (TargetExpansion.graph target wall right).edges :=
    GluingDatum.incidentEdges (oldVertex target vertex)
  let oldIncident : Finset target.edges := GluingDatum.incidentEdges vertex
  change (∑ edge ∈ expandedIncident,
      (Fintype.card
        ((datum data wall right resolution hCompatible).edgePartition edge).Blocks :
          ℤ)) =
    ∑ edge ∈ oldIncident,
      (Fintype.card (data.edgePartition edge).Blocks : ℤ)
  calc
    (∑ edge ∈ expandedIncident,
        (Fintype.card
          ((datum data wall right resolution hCompatible).edgePartition edge).Blocks :
            ℤ)) =
        ∑ edge : (TargetExpansion.graph target wall right).edges,
          if edge ∈ expandedIncident then
            (Fintype.card
              ((datum data wall right resolution hCompatible).edgePartition edge).Blocks :
                ℤ)
          else 0 := by
      rw [← Finset.sum_filter]
      simp
    _ = ∑ label : Option target.edges,
          if occurrenceEquiv target wall right label ∈ expandedIncident then
            (Fintype.card
              ((datum data wall right resolution hCompatible).edgePartition
                (occurrenceEquiv target wall right label)).Blocks : ℤ)
          else 0 := by
      symm
      apply Fintype.sum_equiv (occurrenceEquiv target wall right)
      intro label
      rfl
    _ = ∑ edge : target.edges,
          if edge ∈ oldIncident then
            (Fintype.card (data.edgePartition edge).Blocks : ℤ)
          else 0 := by
      rw [Fintype.sum_option]
      simp [expandedIncident, oldIncident,
        newOccurrence_not_mem_incidentEdges_old wall vertex right hne,
        oldOccurrence_mem_incidentEdges_old_iff wall vertex right hne,
        datum_edgePartition_old]
    _ = ∑ edge ∈ oldIncident,
        (Fintype.card (data.edgePartition edge).Blocks : ℤ) := by
      rw [← Finset.sum_filter]
      simp

/-- The change is literally unchanged away from the split target vertex. -/
theorem targetChange_old_of_ne
    (data : GluingDatum target degree) (wall vertex : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hne : vertex ≠ wall) :
    (datum data wall right resolution hCompatible).targetChange
        (oldVertex target vertex) =
      data.targetChange vertex := by
  have hExpanded := GluingDatum.targetChange_eq_card_formula
    (datum data wall right resolution hCompatible) (oldVertex target vertex)
  rw [hExpanded, data.targetChange_eq_card_formula]
  rw [sum_edgeBlockCard_old_of_ne data wall vertex right resolution
    hCompatible hne]
  rw [datum_vertexPartition_old_of_ne data wall vertex right resolution
    hCompatible hne]
  rw [incidentEdges_card_old_of_ne wall vertex right hne]

/-- The dimension-formula correction is likewise unchanged away from the
split target vertex. -/
theorem targetExcess_old_of_ne
    (data : GluingDatum target degree) (wall vertex : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hne : vertex ≠ wall) :
    (datum data wall right resolution hCompatible).targetExcess
        (oldVertex target vertex) =
      data.targetExcess vertex := by
  unfold GluingDatum.targetExcess
  rw [targetChange_old_of_ne data wall vertex right resolution
    hCompatible hne]
  rw [incidentEdges_card_old_of_ne wall vertex right hne]

/-- The resolved quotient source retains every old source-edge block and adds
exactly the blocks of the resolving target edge. -/
theorem card_sourceEdge_datum
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution) :
    Fintype.card (datum data wall right resolution hCompatible).SourceEdge =
      Fintype.card data.SourceEdge +
        Fintype.card resolution.newEdge.Blocks := by
  rw [(datum data wall right resolution hCompatible).card_sourceEdge_eq_sum_card_blocks,
    data.card_sourceEdge_eq_sum_card_blocks]
  calc
    (∑ edge : (TargetExpansion.graph target wall right).edges,
        Fintype.card
          ((datum data wall right resolution hCompatible).edgePartition edge).Blocks) =
      ∑ label : Option target.edges,
        Fintype.card
          ((datum data wall right resolution hCompatible).edgePartition
            (occurrenceEquiv target wall right label)).Blocks := by
      symm
      apply Fintype.sum_equiv (occurrenceEquiv target wall right)
      intro label
      rfl
    _ = Fintype.card resolution.newEdge.Blocks +
        ∑ edge : target.edges,
          Fintype.card (data.edgePartition edge).Blocks := by
      rw [Fintype.sum_option]
      simp only [datum_edgePartition_new, datum_edgePartition_old]
    _ = (∑ edge : target.edges,
          Fintype.card (data.edgePartition edge).Blocks) +
        Fintype.card resolution.newEdge.Blocks := by omega

/-- Splitting the wall replaces its old source blocks by the left and right
endpoint blocks; this additive form avoids truncated natural subtraction. -/
theorem card_sourceVertex_datum_add_wall
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution) :
    Fintype.card (datum data wall right resolution hCompatible).SourceVertex +
        Fintype.card (data.vertexPartition wall).Blocks =
      Fintype.card data.SourceVertex +
        Fintype.card resolution.left.Blocks +
        Fintype.card resolution.right.Blocks := by
  rw [(datum data wall right resolution hCompatible).card_sourceVertex_eq_sum_card_blocks,
    data.card_sourceVertex_eq_sum_card_blocks]
  rw [TargetExpansion.sum_vertices]
  have hResolvedOldSum :
      (∑ vertex : target.V,
        Fintype.card
          ((datum data wall right resolution hCompatible).vertexPartition
            (oldVertex target vertex)).Blocks) =
        (∑ vertex ∈ (Finset.univ : Finset target.V).erase wall,
          Fintype.card (data.vertexPartition vertex).Blocks) +
          Fintype.card resolution.left.Blocks := by
    rw [← Finset.sum_erase_add _ _ (by simp :
      wall ∈ (Finset.univ : Finset target.V))]
    congr 1
    apply Finset.sum_congr rfl
    intro vertex hVertex
    have hne : vertex ≠ wall := Finset.ne_of_mem_erase hVertex
    rw [datum_vertexPartition_old_of_ne data wall vertex right resolution
      hCompatible hne]
    rw [datum_vertexPartition_old_wall]
  have hOldSum :
      (∑ vertex : target.V,
        Fintype.card (data.vertexPartition vertex).Blocks) =
        (∑ vertex ∈ (Finset.univ : Finset target.V).erase wall,
          Fintype.card (data.vertexPartition vertex).Blocks) +
          Fintype.card (data.vertexPartition wall).Blocks := by
    exact (Finset.sum_erase_add _ _ (by simp)).symm
  rw [hResolvedOldSum, hOldSum, datum_vertexPartition_fresh]
  omega

/-- The source genus is preserved exactly when the resolving-edge and
endpoint block counts satisfy the corresponding Euler equality.  When
`resolution.ContractsTo` is also available, this is the local connected-fibre
tree count. -/
theorem sourceGraph_genus_eq_iff_block_card
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution) :
    genus (datum data wall right resolution hCompatible).sourceGraph =
        genus data.sourceGraph ↔
      Fintype.card resolution.newEdge.Blocks +
          Fintype.card (data.vertexPartition wall).Blocks =
        Fintype.card resolution.left.Blocks +
          Fintype.card resolution.right.Blocks := by
  have hEdges := card_sourceEdge_datum data wall right resolution hCompatible
  have hVertices := card_sourceVertex_datum_add_wall data wall right resolution
    hCompatible
  simp only [genus, GluingDatum.sourceGraph_edges_card]
  change
    ((Fintype.card
        (datum data wall right resolution hCompatible).SourceEdge : ℤ) -
        (Fintype.card
          (datum data wall right resolution hCompatible).SourceVertex : ℤ) + 1 =
      (Fintype.card data.SourceEdge : ℤ) -
        (Fintype.card data.SourceVertex : ℤ) + 1) ↔ _
  constructor <;> intro h
  all_goals omega

/-- Equation (C) before change-minimality: when contracting the new source
fibre preserves source genus, the old wall correction is the sum of the two
resolved endpoint corrections plus one.  This is the global dimension-formula
proof of the source's contraction identity. -/
theorem targetExcess_wall_eq_endpoints_add_one_of_source_genus_eq
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hSourceGenus :
      genus (datum data wall right resolution hCompatible).sourceGraph =
        genus data.sourceGraph) :
    data.targetExcess wall =
      (datum data wall right resolution hCompatible).targetExcess
          (oldVertex target wall) +
        (datum data wall right resolution hCompatible).targetExcess
          (freshVertex target) + 1 := by
  classical
  let resolved := datum data wall right resolution hCompatible
  have hOldDimension := data.dimensionCorrection
  have hResolvedDimension := resolved.dimensionCorrection
  rw [TargetExpansion.graph_edge_card,
    TargetExpansion.graph_genus, hSourceGenus] at hResolvedDimension
  have hOldSum :
      (∑ vertex : target.V, data.targetExcess vertex) =
        (∑ vertex ∈ (Finset.univ : Finset target.V).erase wall,
          data.targetExcess vertex) + data.targetExcess wall := by
    exact (Finset.sum_erase_add _ _ (by simp)).symm
  have hResolvedOldSum :
      (∑ vertex : target.V,
        resolved.targetExcess (oldVertex target vertex)) =
        (∑ vertex ∈ (Finset.univ : Finset target.V).erase wall,
          data.targetExcess vertex) +
          resolved.targetExcess (oldVertex target wall) := by
    rw [← Finset.sum_erase_add _ _ (by simp :
      wall ∈ (Finset.univ : Finset target.V))]
    congr 1
    apply Finset.sum_congr rfl
    intro vertex hVertex
    have hne : vertex ≠ wall := Finset.ne_of_mem_erase hVertex
    exact targetExcess_old_of_ne data wall vertex right resolution
      hCompatible hne
  have hResolvedSum :
      (∑ vertex : (TargetExpansion.graph target wall right).V,
        resolved.targetExcess vertex) =
        (∑ vertex ∈ (Finset.univ : Finset target.V).erase wall,
          data.targetExcess vertex) +
          resolved.targetExcess (oldVertex target wall) +
          resolved.targetExcess (freshVertex target) := by
    rw [TargetExpansion.sum_vertices, hResolvedOldSum]
  rw [hOldSum] at hOldDimension
  rw [hResolvedSum] at hResolvedDimension
  push_cast at hResolvedDimension
  change data.targetExcess wall =
    resolved.targetExcess (oldVertex target wall) +
      resolved.targetExcess (freshVertex target) + 1
  linarith

/-- A change-minimal resolved datum whose source genus survives contraction
forces Equation (C) at the contracted wall. -/
theorem targetExcess_wall_eq_one_of_changeMinimal
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hSourceGenus :
      genus (datum data wall right resolution hCompatible).sourceGraph =
        genus data.sourceGraph)
    (hMinimal :
      (datum data wall right resolution hCompatible).ChangeMinimal) :
    data.targetExcess wall = 1 := by
  rw [targetExcess_wall_eq_endpoints_add_one_of_source_genus_eq data wall right
    resolution hCompatible hSourceGenus]
  rw [hMinimal (oldVertex target wall), hMinimal (freshVertex target)]
  norm_num

/-- Local Euler form of Equation (C): the block-cardinality tree receipt is
exactly enough to discharge the source-genus premise. -/
theorem targetExcess_wall_eq_one_of_changeMinimal_of_block_card
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hBlockCard :
      Fintype.card resolution.newEdge.Blocks +
          Fintype.card (data.vertexPartition wall).Blocks =
        Fintype.card resolution.left.Blocks +
          Fintype.card resolution.right.Blocks)
    (hMinimal :
      (datum data wall right resolution hCompatible).ChangeMinimal) :
    data.targetExcess wall = 1 := by
  apply targetExcess_wall_eq_one_of_changeMinimal data wall right resolution
    hCompatible
  · exact (sourceGraph_genus_eq_iff_block_card data wall right resolution
      hCompatible).mpr hBlockCard
  · exact hMinimal

/-- To prove Riemann--Hurwitz for the resolved datum, it is enough to check
the two new target vertices. Every unchanged target vertex inherits the old
inequality by the occurrence bijection. -/
theorem datum_riemannHurwitz_of_endpoints
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hRiemannHurwitz : data.RiemannHurwitz)
    (hLeft : (datum data wall right resolution hCompatible).RiemannHurwitzAtTargetVertex
      (oldVertex target wall))
    (hRight : (datum data wall right resolution hCompatible).RiemannHurwitzAtTargetVertex
      (freshVertex target)) :
    (datum data wall right resolution hCompatible).RiemannHurwitz := by
  rw [GluingDatum.riemannHurwitz_iff_forall_targetVertex]
  intro vertex
  cases vertex with
  | inl vertex =>
      by_cases hVertex : vertex = wall
      · subst vertex
        exact hLeft
      · change (datum data wall right resolution hCompatible).RiemannHurwitzAtTargetVertex
          (oldVertex target vertex)
        intro sheet
        have hOld := hRiemannHurwitz vertex sheet
        rw [sum_blockCountWithin_old_of_ne data wall vertex right resolution
          hCompatible hVertex sheet]
        rw [datum_vertexPartition_old_of_ne data wall vertex right resolution
          hCompatible hVertex]
        rw [incidentEdges_card_old_of_ne wall vertex right hVertex]
        exact hOld
  | inr fresh =>
      cases fresh
      exact hRight

/-- Full validity follows from the two endpoint Riemann--Hurwitz checks: source
connectedness is automatic from contraction and old connectedness. -/
theorem datum_valid_of_endpoints
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hContracts : resolution.ContractsTo (data.vertexPartition wall))
    (hValid : data.Valid)
    (hLeft : (datum data wall right resolution hCompatible).RiemannHurwitzAtTargetVertex
      (oldVertex target wall))
    (hRight : (datum data wall right resolution hCompatible).RiemannHurwitzAtTargetVertex
      (freshVertex target)) :
    (datum data wall right resolution hCompatible).Valid :=
  ⟨datum_connected data wall right resolution hCompatible hContracts hValid.1,
    datum_riemannHurwitz_of_endpoints data wall right resolution hCompatible
      hValid.2 hLeft hRight⟩

/-- List-form assembly boundary used by the local case figures. Once two lists
enumerate the actual incidence occurrences at the resolved endpoints, the
local `SheetPartition.RiemannHurwitzAt` receipts imply validity of the whole
outgoing datum. Equality with the incident finsets' underlying multisets
records both coverage and absence of duplicates. -/
theorem datum_valid_of_incidentLists
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hContracts : resolution.ContractsTo (data.vertexPartition wall))
    (hValid : data.Valid)
    (leftEdges rightEdges :
      List (TargetExpansion.graph target wall right).edges)
    (hLeftEdges : (leftEdges : Multiset
        (TargetExpansion.graph target wall right).edges) =
      (GluingDatum.incidentEdges (oldVertex target wall) :
        Finset (TargetExpansion.graph target wall right).edges).val)
    (hRightEdges : (rightEdges : Multiset
        (TargetExpansion.graph target wall right).edges) =
      (GluingDatum.incidentEdges (freshVertex target) :
        Finset (TargetExpansion.graph target wall right).edges).val)
    (hLeft : SheetPartition.RiemannHurwitzAt resolution.left
      (leftEdges.map
        (datum data wall right resolution hCompatible).edgePartition))
    (hRight : SheetPartition.RiemannHurwitzAt resolution.right
      (rightEdges.map
        (datum data wall right resolution hCompatible).edgePartition)) :
    (datum data wall right resolution hCompatible).Valid := by
  apply datum_valid_of_endpoints data wall right resolution hCompatible
    hContracts hValid
  · apply ((datum data wall right resolution hCompatible).riemannHurwitzAtTargetVertex_iff_incidentList
        (oldVertex target wall) leftEdges hLeftEdges).mpr
    simpa using hLeft
  · apply ((datum data wall right resolution hCompatible).riemannHurwitzAtTargetVertex_iff_incidentList
        (freshVertex target) rightEdges hRightEdges).mpr
    simpa using hRight

/-- Canonical assembly boundary: the figure-specific hypotheses mention
only the old wall occurrences assigned to each side, with the resolving edge
inserted first. The occurrence lists and their coverage proofs are supplied
uniformly by `TargetExpansion`. -/
theorem datum_valid_of_assignedLists
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hContracts : resolution.ContractsTo (data.vertexPartition wall))
    (hValid : data.Valid)
    (hLeft : SheetPartition.RiemannHurwitzAt resolution.left
      (resolution.newEdge ::
        (wallEdgesAssigned target wall right false).toList.map
          data.edgePartition))
    (hRight : SheetPartition.RiemannHurwitzAt resolution.right
      (resolution.newEdge ::
        (wallEdgesAssigned target wall right true).toList.map
          data.edgePartition)) :
    (datum data wall right resolution hCompatible).Valid := by
  apply datum_valid_of_incidentLists data wall right resolution hCompatible
    hContracts hValid (leftIncidentList target wall right)
      (rightIncidentList target wall right)
    (leftIncidentList_multiset target wall right)
      (rightIncidentList_multiset target wall right)
  · rw [datum_edgePartitions_incidentList]
    exact hLeft
  · rw [datum_edgePartitions_incidentList]
    exact hRight

/-- Diagram-order assembly boundary. A local figure may enumerate the old
wall occurrences on each side in any convenient order. Multiset equality
certifies that those lists are exactly the assigned occurrences; permutation
invariance of local Riemann--Hurwitz transports the figure receipts to the
canonical incidence lists. -/
theorem datum_valid_of_assignedOccurrences
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hContracts : resolution.ContractsTo (data.vertexPartition wall))
    (hValid : data.Valid) (leftEdges rightEdges : List target.edges)
    (hLeftEdges : (leftEdges : Multiset target.edges) =
      (wallEdgesAssigned target wall right false).val)
    (hRightEdges : (rightEdges : Multiset target.edges) =
      (wallEdgesAssigned target wall right true).val)
    (hLeft : SheetPartition.RiemannHurwitzAt resolution.left
      (resolution.newEdge :: leftEdges.map data.edgePartition))
    (hRight : SheetPartition.RiemannHurwitzAt resolution.right
      (resolution.newEdge :: rightEdges.map data.edgePartition)) :
    (datum data wall right resolution hCompatible).Valid := by
  apply datum_valid_of_assignedLists data wall right resolution hCompatible
    hContracts hValid
  · apply (SheetPartition.riemannHurwitzAt_iff_of_perm resolution.left ?_).mpr
      hLeft
    apply List.Perm.cons
    apply List.Perm.map
    apply Multiset.coe_eq_coe.mp
    rw [Finset.coe_toList, ← hLeftEdges]
  · apply (SheetPartition.riemannHurwitzAt_iff_of_perm resolution.right ?_).mpr
      hRight
    apply List.Perm.cons
    apply List.Perm.map
    apply Multiset.coe_eq_coe.mp
    rw [Finset.coe_toList, ← hRightEdges]

end DraismaVargas.LocalCases.GlobalResolution
