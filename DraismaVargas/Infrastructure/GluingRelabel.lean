import DraismaVargas.Infrastructure.GluingDatum
import Utilities.Subdivision.LaplacianEquiv

/-!
# Global sheet relabelling of a DV gluing datum

A fixed-target-tree DV isomorphism may use one sheet permutation at each
target vertex and another on each target-edge occurrence.  Incidence remains
valid precisely when the relative edge-to-vertex permutation stays inside
every block of the endpoint vertex partition.

This module constructs the relabelled `GluingDatum` and proves that all local
Riemann--Hurwitz inequalities survive.  Connectivity is proved separately, by
exhibiting the relabelling as an adjacency-preserving equivalence of the
literal quotient-source graphs; together these give the full validity
predicate.
-/

namespace DraismaVargas.Infrastructure

open Finset

namespace GluingDatum

variable {target : CFGraph} {degree : ℕ}

/-- Sheet permutations on every target element, with the exact endpoint
compatibility needed to preserve partition refinement. -/
structure SheetRelabeling (data : GluingDatum target degree) where
  vertexPermutation : target.V → Equiv.Perm (Fin degree)
  edgePermutation : target.edges → Equiv.Perm (Fin degree)
  compatible_left : ∀ (edge : target.edges) (sheet : Fin degree),
    (data.vertexPartition (edge : target.V × target.V).1).Rel
      ((vertexPermutation (edge : target.V × target.V).1).symm
        (edgePermutation edge sheet)) sheet
  compatible_right : ∀ (edge : target.edges) (sheet : Fin degree),
    (data.vertexPartition (edge : target.V × target.V).2).Rel
      ((vertexPermutation (edge : target.V × target.V).2).symm
        (edgePermutation edge sheet)) sheet

namespace SheetRelabeling

variable {data : GluingDatum target degree}

/-- Apply compatible sheet permutations to every vertex and edge occurrence
of a gluing datum. -/
def apply (relabeling : data.SheetRelabeling) : GluingDatum target degree where
  degree_pos := data.degree_pos
  vertexPartition vertex :=
    (data.vertexPartition vertex).relabel (relabeling.vertexPermutation vertex)
  edgePartition edge :=
    (data.edgePartition edge).relabel (relabeling.edgePermutation edge)
  refines_left edge :=
    SheetPartition.relabel_refines_of_relative_pointwise
      (data.refines_left edge) (relabeling.edgePermutation edge)
      (relabeling.vertexPermutation (edge : target.V × target.V).1)
      (relabeling.compatible_left edge)
  refines_right edge :=
    SheetPartition.relabel_refines_of_relative_pointwise
      (data.refines_right edge) (relabeling.edgePermutation edge)
      (relabeling.vertexPermutation (edge : target.V × target.V).2)
      (relabeling.compatible_right edge)

/-- Relabelling preserves every local Riemann--Hurwitz inequality. -/
theorem riemannHurwitz (relabeling : data.SheetRelabeling)
    (hRiemannHurwitz : data.RiemannHurwitz) :
    relabeling.apply.RiemannHurwitz := by
  intro vertex sheet
  let originalSheet := (relabeling.vertexPermutation vertex).symm sheet
  have hOriginal := hRiemannHurwitz vertex originalSheet
  have hCounts :
      (∑ edge ∈ incidentEdges vertex,
        (((relabeling.apply.edgePartition edge).blockCountWithin
          (relabeling.apply.vertexPartition vertex) sheet : ℕ) : ℤ)) =
      ∑ edge ∈ incidentEdges vertex,
        (((data.edgePartition edge).blockCountWithin
          (data.vertexPartition vertex) originalSheet : ℕ) : ℤ) := by
    apply Finset.sum_congr rfl
    intro edge hIncident
    have hEndpoint := (Finset.mem_filter.mp hIncident).2
    rcases hEndpoint with hLeft | hRight
    · have hCount :=
        SheetPartition.relabel_blockCountWithin_of_relative_pointwise
          (data.edgePartition edge)
          (data.vertexPartition (edge : target.V × target.V).1)
          (relabeling.edgePermutation edge)
          (relabeling.vertexPermutation (edge : target.V × target.V).1)
          (relabeling.compatible_left edge)
          ((relabeling.vertexPermutation
            (edge : target.V × target.V).1).symm sheet)
      rw [Equiv.apply_symm_apply] at hCount
      subst vertex
      exact_mod_cast hCount
    · have hCount :=
        SheetPartition.relabel_blockCountWithin_of_relative_pointwise
          (data.edgePartition edge)
          (data.vertexPartition (edge : target.V × target.V).2)
          (relabeling.edgePermutation edge)
          (relabeling.vertexPermutation (edge : target.V × target.V).2)
          (relabeling.compatible_right edge)
          ((relabeling.vertexPermutation
            (edge : target.V × target.V).2).symm sheet)
      rw [Equiv.apply_symm_apply] at hCount
      subst vertex
      exact_mod_cast hCount
  have hCard := (data.vertexPartition vertex).relabel_blockCard
    (relabeling.vertexPermutation vertex) originalSheet
  rw [Equiv.apply_symm_apply] at hCard
  change
    (∑ edge ∈ incidentEdges vertex,
      (((relabeling.apply.edgePartition edge).blockCountWithin
        (relabeling.apply.vertexPartition vertex) sheet : ℕ) : ℤ)) - 2 ≥
      ((relabeling.apply.vertexPartition vertex).blockCard sheet : ℤ) *
        (((incidentEdges vertex).card : ℤ) - 2)
  rw [hCounts]
  change
    (∑ edge ∈ incidentEdges vertex,
      (((data.edgePartition edge).blockCountWithin
        (data.vertexPartition vertex) originalSheet : ℕ) : ℤ)) - 2 ≥
      (((data.vertexPartition vertex).relabel
        (relabeling.vertexPermutation vertex)).blockCard sheet : ℤ) *
        (((incidentEdges vertex).card : ℤ) - 2)
  rw [hCard]
  exact hOriginal

/-- Relabelled quotient-source vertices are canonically equivalent to the
original block vertices. -/
def sourceVertexEquiv (relabeling : data.SheetRelabeling) :
    data.SourceVertex ≃ relabeling.apply.SourceVertex where
  toFun sourceVertex :=
    ⟨(sourceVertex.1.1,
      relabeling.vertexPermutation sourceVertex.1.1 sourceVertex.1.2), by
      change relabeling.vertexPermutation sourceVertex.1.1
          ((data.vertexPartition sourceVertex.1.1).repr
            ((relabeling.vertexPermutation sourceVertex.1.1).symm
              (relabeling.vertexPermutation sourceVertex.1.1 sourceVertex.1.2))) =
        relabeling.vertexPermutation sourceVertex.1.1 sourceVertex.1.2
      rw [Equiv.symm_apply_apply, sourceVertex.2]⟩
  invFun targetVertex :=
    ⟨(targetVertex.1.1,
      (relabeling.vertexPermutation targetVertex.1.1).symm targetVertex.1.2), by
      have hRepresentative := targetVertex.2
      change (data.vertexPartition targetVertex.1.1).repr
          ((relabeling.vertexPermutation targetVertex.1.1).symm
            targetVertex.1.2) = _
      apply (relabeling.vertexPermutation targetVertex.1.1).injective
      simpa [apply, SheetPartition.relabel] using hRepresentative⟩
  left_inv := by
    intro sourceVertex
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · simp
  right_inv := by
    intro targetVertex
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · simp

/-- Relabelled quotient-source edge blocks are canonically equivalent to the
original occurrence-labelled blocks. -/
def sourceEdgeEquiv (relabeling : data.SheetRelabeling) :
    data.SourceEdge ≃ relabeling.apply.SourceEdge where
  toFun sourceEdge :=
    ⟨(sourceEdge.1.1, relabeling.edgePermutation sourceEdge.1.1 sourceEdge.1.2), by
      change relabeling.edgePermutation sourceEdge.1.1
          ((data.edgePartition sourceEdge.1.1).repr
            ((relabeling.edgePermutation sourceEdge.1.1).symm
              (relabeling.edgePermutation sourceEdge.1.1 sourceEdge.1.2))) =
        relabeling.edgePermutation sourceEdge.1.1 sourceEdge.1.2
      rw [Equiv.symm_apply_apply, sourceEdge.2]⟩
  invFun targetEdge :=
    ⟨(targetEdge.1.1,
      (relabeling.edgePermutation targetEdge.1.1).symm targetEdge.1.2), by
      have hRepresentative := targetEdge.2
      change (data.edgePartition targetEdge.1.1).repr
          ((relabeling.edgePermutation targetEdge.1.1).symm targetEdge.1.2) = _
      apply (relabeling.edgePermutation targetEdge.1.1).injective
      simpa [apply, SheetPartition.relabel] using hRepresentative⟩
  left_inv := by
    intro sourceEdge
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · simp
  right_inv := by
    intro targetEdge
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · simp

/-- The left endpoint of a relabelled edge is the relabelled original left
endpoint, even when the edge and vertex permutations differ. -/
theorem sourceEnds_sourceEdgeEquiv_fst
    (relabeling : data.SheetRelabeling) (edge : data.SourceEdge) :
    (relabeling.apply.sourceEnds (relabeling.sourceEdgeEquiv edge)).1 =
      relabeling.sourceVertexEquiv (data.sourceEnds edge).1 := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change
      relabeling.vertexPermutation (edge.1.1 : target.V × target.V).1
          ((data.vertexPartition (edge.1.1 : target.V × target.V).1).repr
            ((relabeling.vertexPermutation
              (edge.1.1 : target.V × target.V).1).symm
                (relabeling.edgePermutation edge.1.1 edge.1.2))) =
        relabeling.vertexPermutation (edge.1.1 : target.V × target.V).1
          ((data.vertexPartition (edge.1.1 : target.V × target.V).1).repr edge.1.2)
    exact congrArg
      (relabeling.vertexPermutation (edge.1.1 : target.V × target.V).1)
      (relabeling.compatible_left edge.1.1 edge.1.2)

/-- The analogous endpoint identity at the right end. -/
theorem sourceEnds_sourceEdgeEquiv_snd
    (relabeling : data.SheetRelabeling) (edge : data.SourceEdge) :
    (relabeling.apply.sourceEnds (relabeling.sourceEdgeEquiv edge)).2 =
      relabeling.sourceVertexEquiv (data.sourceEnds edge).2 := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change
      relabeling.vertexPermutation (edge.1.1 : target.V × target.V).2
          ((data.vertexPartition (edge.1.1 : target.V × target.V).2).repr
            ((relabeling.vertexPermutation
              (edge.1.1 : target.V × target.V).2).symm
                (relabeling.edgePermutation edge.1.1 edge.1.2))) =
        relabeling.vertexPermutation (edge.1.1 : target.V × target.V).2
          ((data.vertexPartition (edge.1.1 : target.V × target.V).2).repr edge.1.2)
    exact congrArg
      (relabeling.vertexPermutation (edge.1.1 : target.V × target.V).2)
      (relabeling.compatible_right edge.1.1 edge.1.2)

/-- Relabelling commutes with the ordered endpoint pair of every exact source
edge occurrence. -/
theorem sourceEnds_sourceEdgeEquiv
    (relabeling : data.SheetRelabeling) (edge : data.SourceEdge) :
    relabeling.apply.sourceEnds (relabeling.sourceEdgeEquiv edge) =
      (relabeling.sourceVertexEquiv (data.sourceEnds edge).1,
        relabeling.sourceVertexEquiv (data.sourceEnds edge).2) := by
  apply Prod.ext
  · exact relabeling.sourceEnds_sourceEdgeEquiv_fst edge
  · exact relabeling.sourceEnds_sourceEdgeEquiv_snd edge

/-- Edge multiplicity in a literal quotient source is the finite sum over
its occurrence-labelled source blocks. -/
theorem num_edges_sourceGraph_eq_sum (sourceData : GluingDatum target degree)
    (first second : sourceData.SourceVertex) :
    num_edges sourceData.sourceGraph first second =
      ∑ edge : sourceData.SourceEdge,
        if sourceData.sourceEnds edge = (first, second) ∨
            sourceData.sourceEnds edge = (second, first) then 1 else 0 := by
  unfold num_edges GluingDatum.sourceGraph
  let predicate : sourceData.SourceVertex × sourceData.SourceVertex → Prop :=
    fun endpoints ↦ endpoints = (first, second) ∨ endpoints = (second, first)
  change (((Finset.univ : Finset sourceData.SourceEdge).val.map
    sourceData.sourceEnds).filter predicate).card = _
  calc
    (((Finset.univ : Finset sourceData.SourceEdge).val.map
      sourceData.sourceEnds).filter predicate).card =
        Multiset.countP predicate
          ((Finset.univ : Finset sourceData.SourceEdge).val.map
            sourceData.sourceEnds) :=
      (Multiset.countP_eq_card_filter predicate _).symm
    _ = (((Finset.univ : Finset sourceData.SourceEdge).val.filter
        fun edge ↦ predicate (sourceData.sourceEnds edge))).card := by
      rw [Multiset.countP_map]
    _ = ((Finset.univ : Finset sourceData.SourceEdge).filter
        fun edge ↦ predicate (sourceData.sourceEnds edge)).card := rfl
    _ = ∑ edge : sourceData.SourceEdge,
        if sourceData.sourceEnds edge = (first, second) ∨
            sourceData.sourceEnds edge = (second, first) then 1 else 0 := by
      simp [predicate]

/-- Relabelling preserves every quotient-source edge multiplicity. -/
theorem num_edges_sourceVertexEquiv (relabeling : data.SheetRelabeling)
    (first second : data.SourceVertex) :
    num_edges relabeling.apply.sourceGraph
        (relabeling.sourceVertexEquiv first)
        (relabeling.sourceVertexEquiv second) =
      num_edges data.sourceGraph first second := by
  rw [num_edges_sourceGraph_eq_sum, num_edges_sourceGraph_eq_sum]
  symm
  apply Fintype.sum_equiv relabeling.sourceEdgeEquiv
  intro edge
  rw [relabeling.sourceEnds_sourceEdgeEquiv edge]
  rcases hEnds : data.sourceEnds edge with ⟨left, right⟩
  simp

/-- A global sheet relabelling is an adjacency-preserving equivalence of the
literal quotient-source graphs. -/
noncomputable def sourceGraphLaplacianEquiv
    (relabeling : data.SheetRelabeling) :
    Utilities.Certificate.LaplacianEquiv
      data.sourceGraph relabeling.apply.sourceGraph where
  toEquiv := relabeling.sourceVertexEquiv
  num_edges_eq := relabeling.num_edges_sourceVertexEquiv

/-- Source connectedness survives every compatible global sheet relabelling. -/
theorem connected (relabeling : data.SheetRelabeling)
    (hConnected : data.Connected) : relabeling.apply.Connected :=
  relabeling.sourceGraphLaplacianEquiv.graphConnected hConnected

/-- Hence a compatible global sheet relabelling preserves the full gluing
datum validity predicate. -/
theorem valid (relabeling : data.SheetRelabeling) (hValid : data.Valid) :
    relabeling.apply.Valid :=
  ⟨relabeling.connected hValid.1, relabeling.riemannHurwitz hValid.2⟩

/-! ## Relabelling one selected target region -/

/-- Use a fixed sheet permutation on a selected target element and the
identity elsewhere. -/
def togglePermutation (moved : Bool) (permutation : Equiv.Perm (Fin degree)) :
    Equiv.Perm (Fin degree) :=
  if moved then permutation else Equiv.refl _

/-- Boundary compatibility at the left endpoint is sufficient for the
relative-permutation condition of a region relabelling. -/
private theorem toggle_compatible_left
    (vertexMoved : target.V → Bool) (edgeMoved : target.edges → Bool)
    (permutation : Equiv.Perm (Fin degree))
    (hBoundary : ∀ edge,
      edgeMoved edge ≠ vertexMoved (edge : target.V × target.V).1 →
        ∀ sheet,
          (data.vertexPartition (edge : target.V × target.V).1).Rel
            (permutation sheet) sheet)
    (edge : target.edges) (sheet : Fin degree) :
    (data.vertexPartition (edge : target.V × target.V).1).Rel
      ((togglePermutation (vertexMoved (edge : target.V × target.V).1)
          permutation).symm
        (togglePermutation (edgeMoved edge) permutation sheet)) sheet := by
  by_cases hEdge : edgeMoved edge = true <;>
    by_cases hVertex : vertexMoved (edge : target.V × target.V).1 = true
  · simp [togglePermutation, hEdge, hVertex]
  · simpa [togglePermutation, hEdge, hVertex] using
      hBoundary edge (by simp [hEdge, hVertex]) sheet
  · have hPreserved :=
      hBoundary edge (by simp [hEdge, hVertex]) (permutation.symm sheet)
    simpa [togglePermutation, hEdge, hVertex] using hPreserved.symm
  · simp [togglePermutation, hEdge, hVertex]

/-- The analogous boundary reduction at the right endpoint. -/
private theorem toggle_compatible_right
    (vertexMoved : target.V → Bool) (edgeMoved : target.edges → Bool)
    (permutation : Equiv.Perm (Fin degree))
    (hBoundary : ∀ edge,
      edgeMoved edge ≠ vertexMoved (edge : target.V × target.V).2 →
        ∀ sheet,
          (data.vertexPartition (edge : target.V × target.V).2).Rel
            (permutation sheet) sheet)
    (edge : target.edges) (sheet : Fin degree) :
    (data.vertexPartition (edge : target.V × target.V).2).Rel
      ((togglePermutation (vertexMoved (edge : target.V × target.V).2)
          permutation).symm
        (togglePermutation (edgeMoved edge) permutation sheet)) sheet := by
  by_cases hEdge : edgeMoved edge = true <;>
    by_cases hVertex : vertexMoved (edge : target.V × target.V).2 = true
  · simp [togglePermutation, hEdge, hVertex]
  · simpa [togglePermutation, hEdge, hVertex] using
      hBoundary edge (by simp [hEdge, hVertex]) sheet
  · have hPreserved :=
      hBoundary edge (by simp [hEdge, hVertex]) (permutation.symm sheet)
    simpa [togglePermutation, hEdge, hVertex] using hPreserved.symm
  · simp [togglePermutation, hEdge, hVertex]

/-- Relabel every selected target vertex and edge by one fixed sheet
permutation.  Only incidences crossing the selected/unselected boundary need
a block-preservation proof. -/
def ofRegion (vertexMoved : target.V → Bool)
    (edgeMoved : target.edges → Bool)
    (permutation : Equiv.Perm (Fin degree))
    (hBoundaryLeft : ∀ edge,
      edgeMoved edge ≠ vertexMoved (edge : target.V × target.V).1 →
        ∀ sheet,
          (data.vertexPartition (edge : target.V × target.V).1).Rel
            (permutation sheet) sheet)
    (hBoundaryRight : ∀ edge,
      edgeMoved edge ≠ vertexMoved (edge : target.V × target.V).2 →
        ∀ sheet,
          (data.vertexPartition (edge : target.V × target.V).2).Rel
            (permutation sheet) sheet) :
    data.SheetRelabeling where
  vertexPermutation vertex := togglePermutation (vertexMoved vertex) permutation
  edgePermutation edge := togglePermutation (edgeMoved edge) permutation
  compatible_left :=
    toggle_compatible_left vertexMoved edgeMoved permutation hBoundaryLeft
  compatible_right :=
    toggle_compatible_right vertexMoved edgeMoved permutation hBoundaryRight

end SheetRelabeling

end GluingDatum

end DraismaVargas.Infrastructure
