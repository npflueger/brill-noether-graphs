import DraismaVargas.Infrastructure.GluingRelabel
import Utilities.Foundations.UnderlyingSimpleGraph

/-!
# A target branch as a Boolean relabelling region

Remove a distinguished target vertex and select the connected component of a
root vertex.  This module turns that component into the Boolean vertex/edge
predicates consumed by `GluingDatum.SheetRelabeling.ofRegion`.  An edge is
selected when either endpoint is in the component.  Consequently every
selected/unselected incidence is forced to lie at the removed vertex.

The construction is valid for every finite target graph.  The DV application
uses it on a target tree, where the selected component is literally one of the
branches at the wall vertex.
-/

namespace DraismaVargas.Infrastructure

open Utilities

namespace TargetBranchRegion

variable {target : CFGraph}

/-- The underlying simple target graph induced away from `wall`. -/
def deletedGraph (wall : target.V) : SimpleGraph {vertex : target.V // vertex ≠ wall} :=
  (underlyingSimpleGraph target).induce {vertex | vertex ≠ wall}

instance deletedGraphDecidableAdj (wall : target.V) :
    DecidableRel (deletedGraph wall).Adj := by
  intro left right
  change Decidable ((underlyingSimpleGraph target).Adj left.1 right.1)
  infer_instance

/-- Membership in the component of `root` after deleting `wall`. -/
def VertexMember (wall root : target.V) (hRoot : root ≠ wall)
    (vertex : target.V) : Prop :=
  ∃ hVertex : vertex ≠ wall,
    (deletedGraph wall).Reachable ⟨root, hRoot⟩ ⟨vertex, hVertex⟩

/-- Boolean characteristic function of the chosen deleted-graph component. -/
def vertexMoved (wall root : target.V) (hRoot : root ≠ wall) : target.V → Bool :=
  fun vertex ↦
    if hVertex : vertex ≠ wall then
      decide ((deletedGraph wall).Reachable ⟨root, hRoot⟩ ⟨vertex, hVertex⟩)
    else false

/-- Select an edge occurrence exactly when at least one endpoint lies in the
chosen component.  The sole possible endpoint mismatch is therefore `wall`. -/
def edgeMoved (wall root : target.V) (hRoot : root ≠ wall) : target.edges → Bool :=
  fun edge ↦
    vertexMoved wall root hRoot (edge : target.V × target.V).1 ||
      vertexMoved wall root hRoot (edge : target.V × target.V).2

@[simp] theorem vertexMoved_eq_true_iff (wall root : target.V)
    (hRoot : root ≠ wall) (vertex : target.V) :
    vertexMoved wall root hRoot vertex = true ↔
      VertexMember wall root hRoot vertex := by
  by_cases hVertex : vertex ≠ wall
  · constructor
    · intro hMoved
      have hReachable :
          (deletedGraph wall).Reachable ⟨root, hRoot⟩ ⟨vertex, hVertex⟩ := by
        simpa [vertexMoved, hVertex] using hMoved
      exact ⟨hVertex, hReachable⟩
    · rintro ⟨hVertex', hReachable⟩
      cases Subsingleton.elim hVertex' hVertex
      simpa [vertexMoved, hVertex] using hReachable
  · simp [vertexMoved, hVertex, VertexMember]

@[simp] theorem vertexMoved_wall (wall root : target.V) (hRoot : root ≠ wall) :
    vertexMoved wall root hRoot wall = false := by
  simp [vertexMoved]

/-- Every target edge occurrence gives an adjacency of the underlying simple
graph. -/
theorem edge_underlying_adj (edge : target.edges) :
    (underlyingSimpleGraph target).Adj
      (edge : target.V × target.V).1 (edge : target.V × target.V).2 := by
  rw [underlyingSimpleGraph_adj]
  change 0 < Multiset.card
    (target.edges.filter (fun targetEdge ↦
      targetEdge = ((edge : target.V × target.V).1,
        (edge : target.V × target.V).2) ∨
      targetEdge = ((edge : target.V × target.V).2,
        (edge : target.V × target.V).1)))
  rw [Multiset.card_pos_iff_exists_mem]
  have hMem : (edge : target.V × target.V) ∈ target.edges :=
    Multiset.count_pos.mp (Nat.zero_lt_of_lt edge.2.isLt)
  refine ⟨(edge : target.V × target.V), Multiset.mem_filter.mpr ⟨hMem, ?_⟩⟩
  exact Or.inl (Prod.eta (edge : target.V × target.V)).symm

/-- Component membership propagates across an edge whose other endpoint is not
the deleted wall vertex. -/
theorem vertexMember_of_adj {wall root vertex neighbor : target.V}
    (hRoot : root ≠ wall)
    (hMember : VertexMember wall root hRoot vertex)
    (hNeighbor : neighbor ≠ wall)
    (hAdj : (underlyingSimpleGraph target).Adj vertex neighbor) :
    VertexMember wall root hRoot neighbor := by
  obtain ⟨hVertex, hReachable⟩ := hMember
  refine ⟨hNeighbor, hReachable.trans ?_⟩
  apply SimpleGraph.Adj.reachable
  exact hAdj

/-- A boundary mismatch at the left endpoint can occur only at `wall`. -/
theorem boundary_left (wall root : target.V) (hRoot : root ≠ wall)
    (edge : target.edges)
    (hDifferent : edgeMoved wall root hRoot edge ≠
      vertexMoved wall root hRoot (edge : target.V × target.V).1) :
    (edge : target.V × target.V).1 = wall := by
  by_contra hLeftWall
  have hLeftFalse :
      vertexMoved wall root hRoot (edge : target.V × target.V).1 = false := by
    cases hLeft : vertexMoved wall root hRoot (edge : target.V × target.V).1 <;>
      simp_all [edgeMoved]
  have hRightTrue :
      vertexMoved wall root hRoot (edge : target.V × target.V).2 = true := by
    cases hRight : vertexMoved wall root hRoot (edge : target.V × target.V).2 <;>
      simp_all [edgeMoved]
  have hRightMember : VertexMember wall root hRoot
      (edge : target.V × target.V).2 :=
    (vertexMoved_eq_true_iff wall root hRoot _).mp hRightTrue
  have hLeftMember : VertexMember wall root hRoot
      (edge : target.V × target.V).1 :=
    vertexMember_of_adj hRoot hRightMember hLeftWall (edge_underlying_adj edge).symm
  have hLeftTrue :=
    (vertexMoved_eq_true_iff wall root hRoot _).mpr hLeftMember
  simp_all

/-- A boundary mismatch at the right endpoint can occur only at `wall`. -/
theorem boundary_right (wall root : target.V) (hRoot : root ≠ wall)
    (edge : target.edges)
    (hDifferent : edgeMoved wall root hRoot edge ≠
      vertexMoved wall root hRoot (edge : target.V × target.V).2) :
    (edge : target.V × target.V).2 = wall := by
  by_contra hRightWall
  have hRightFalse :
      vertexMoved wall root hRoot (edge : target.V × target.V).2 = false := by
    cases hLeft : vertexMoved wall root hRoot (edge : target.V × target.V).1 <;>
      cases hRight : vertexMoved wall root hRoot (edge : target.V × target.V).2 <;>
      simp_all [edgeMoved]
  have hLeftTrue :
      vertexMoved wall root hRoot (edge : target.V × target.V).1 = true := by
    cases hLeft : vertexMoved wall root hRoot (edge : target.V × target.V).1 <;>
      simp_all [edgeMoved]
  have hLeftMember : VertexMember wall root hRoot
      (edge : target.V × target.V).1 :=
    (vertexMoved_eq_true_iff wall root hRoot _).mp hLeftTrue
  have hRightMember : VertexMember wall root hRoot
      (edge : target.V × target.V).2 :=
    vertexMember_of_adj hRoot hLeftMember hRightWall (edge_underlying_adj edge)
  have hRightTrue :=
    (vertexMoved_eq_true_iff wall root hRoot _).mpr hRightMember
  simp_all

end TargetBranchRegion

end DraismaVargas.Infrastructure
