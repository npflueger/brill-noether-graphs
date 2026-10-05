module

public import DraismaVargas.LocalCases.NonDanglingValency
public import DraismaVargas.Infrastructure.GluingRelabel
public import Utilities.Subdivision.LeafReduction

@[expose] public section

/-!
# Pruning transport under the actual sheet-relabelling graph equivalence

The remote M11 swap is an isomorphism of literal source graphs, not merely
an equality of local partition counts. This module transports a separating
side through the vertex equivalence and restricts that equivalence to the
induced side. This preserves its genus-zero certificate and therefore actual
danglingness.
-/

namespace DraismaVargas.LocalCases.SheetRelabelPruning

open DraismaVargas.Infrastructure
open W4StableSource
open Utilities Utilities.Certificate

section Graph

variable {G H : CFGraph}

noncomputable def imageSide (equivalence : LaplacianEquiv G H) (side : Finset G.V) : Finset H.V := by
  classical
  exact side.image equivalence.toEquiv

@[simp] theorem mem_imageSide (equivalence : LaplacianEquiv G H) (side : Finset G.V) (vertex : G.V) :
    equivalence.toEquiv vertex ∈ imageSide equivalence side ↔ vertex ∈ side := by
  classical
  simp [imageSide]

/-- Restrict the actual multiplicity-preserving vertex equivalence to an
induced side; its inverse is supplied by image membership. -/
noncomputable def inducedEquiv (equivalence : LaplacianEquiv G H)
    (side : Finset G.V) (hSide : side.Nonempty) :
    LaplacianEquiv (inducedSubgraph G side hSide)
      (inducedSubgraph H (imageSide equivalence side) (hSide.image equivalence.toEquiv)) := by
  classical
  let vertexMap : {vertex // vertex ∈ side} → {vertex // vertex ∈ imageSide equivalence side} :=
    fun vertex ↦ ⟨equivalence.toEquiv vertex.1, (mem_imageSide equivalence side vertex.1).mpr vertex.2⟩
  have hBij : Function.Bijective vertexMap := by
    constructor
    · intro first second hEqual
      exact Subtype.ext (equivalence.toEquiv.injective (congrArg Subtype.val hEqual))
    · intro vertex
      obtain ⟨old, hOld, hEqual⟩ := Finset.mem_image.mp vertex.2
      exact ⟨⟨old, hOld⟩, Subtype.ext hEqual⟩
  refine { toEquiv := Equiv.ofBijective vertexMap hBij
           num_edges_eq := ?_ }
  intro first second
  erw [num_edges_inducedSubgraph, num_edges_inducedSubgraph]
  exact equivalence.num_edges_eq first.1 second.1

noncomputable def mapCut (equivalence : LaplacianEquiv G H) {left right : G.V}
    (cut : SeparatingEdgeCut G left right) :
    SeparatingEdgeCut H (equivalence.toEquiv left) (equivalence.toEquiv right) := by
  classical
  refine { side := imageSide equivalence cut.side
           left_mem := (mem_imageSide equivalence cut.side left).mpr cut.left_mem
           right_not_mem := fun h ↦ cut.right_not_mem ((mem_imageSide equivalence cut.side right).mp h)
           cross_num_edges := ?_ }
  intro first second hFirst hSecond
  obtain ⟨first, rfl⟩ := equivalence.toEquiv.surjective first
  obtain ⟨second, rfl⟩ := equivalence.toEquiv.surjective second
  rw [equivalence.num_edges_eq, cut.cross_num_edges first second
    ((mem_imageSide equivalence cut.side first).mp hFirst)
    (fun h ↦ hSecond ((mem_imageSide equivalence cut.side second).mpr h))]
  by_cases h : first = left ∧ second = right
  · exact (ite_eq_left h).trans (ite_eq_left ⟨congrArg equivalence.toEquiv h.1, congrArg equivalence.toEquiv h.2⟩).symm
  · exact (ite_eq_right h).trans (ite_eq_right (fun hPair ↦ h
      ⟨equivalence.toEquiv.injective hPair.1, equivalence.toEquiv.injective hPair.2⟩)).symm

/-- A genuine dangling side remains genuine under a graph equivalence.
Ambient connectedness supplies the complementary side's connectedness. -/
noncomputable def mapDanglingSide (equivalence : LaplacianEquiv G H)
    (hConnected : graph_connected H) {left right : G.V} (dangling : DanglingSide G left right) :
    DanglingSide H (equivalence.toEquiv left) (equivalence.toEquiv right) where
  toSeparatingEdgeCut := mapCut equivalence dangling.toSeparatingEdgeCut
  side_connected := (inducedEquiv equivalence dangling.side ⟨left, dangling.left_mem⟩).graphConnected dangling.side_connected
  complement_connected := NonDanglingValency.complement_connected_of_unique_cross hConnected _
    (mapCut equivalence dangling.toSeparatingEdgeCut).right_not_mem
    (mapCut equivalence dangling.toSeparatingEdgeCut).cross_num_edges
  side_genus_zero := (inducedEquiv equivalence dangling.side ⟨left, dangling.left_mem⟩).genus_eq.trans dangling.side_genus_zero

end Graph

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}

/-- Transport a single actual dangling occurrence using the exact ordered
endpoint equation; no equality of arbitrarily listed rows is involved. -/
theorem isDangling_map {otherTarget : CFGraph} {otherDegree : ℕ}
    (otherData : GluingDatum otherTarget otherDegree)
    (equivalence : LaplacianEquiv data.sourceGraph otherData.sourceGraph)
    (hConnected : otherData.Connected) (edge : data.SourceEdge) (other : otherData.SourceEdge)
    (hEnds : otherData.sourceEnds other =
      (equivalence.toEquiv (data.sourceEnds edge).1, equivalence.toEquiv (data.sourceEnds edge).2))
    (hDangling : IsDangling data edge) : IsDangling otherData other := by
  unfold IsDangling
  rw [hEnds]
  rcases hDangling with hDangling | hDangling
  · obtain ⟨dangling⟩ := hDangling
    exact Or.inl ⟨mapDanglingSide equivalence hConnected dangling⟩
  · obtain ⟨dangling⟩ := hDangling
    exact Or.inr ⟨mapDanglingSide equivalence hConnected dangling⟩

/-- An actual compatible sheet relabelling preserves pruning in both
directions, including occurrences whose endpoint and edge permutations differ. -/
theorem isDangling_sourceEdgeEquiv_iff (relabeling : data.SheetRelabeling)
    (hConnected : data.Connected) (edge : data.SourceEdge) :
    IsDangling relabeling.apply (relabeling.sourceEdgeEquiv edge) ↔ IsDangling data edge := by
  constructor
  · intro hDangling
    apply isDangling_map data relabeling.sourceGraphLaplacianEquiv.symm hConnected
      (relabeling.sourceEdgeEquiv edge) edge _ hDangling
    rw [relabeling.sourceEnds_sourceEdgeEquiv]
    apply Prod.ext
    · exact (relabeling.sourceVertexEquiv.symm_apply_apply _).symm
    · exact (relabeling.sourceVertexEquiv.symm_apply_apply _).symm
  · exact isDangling_map relabeling.apply relabeling.sourceGraphLaplacianEquiv
      (relabeling.connected hConnected) edge (relabeling.sourceEdgeEquiv edge)
      (relabeling.sourceEnds_sourceEdgeEquiv edge)

/-- Incidence is preserved by the exact source-vertex and source-edge maps. -/
theorem incident_sourceEdgeEquiv_iff (relabeling : data.SheetRelabeling)
    (edge : data.SourceEdge) (vertex : data.SourceVertex) :
    Incident relabeling.apply (relabeling.sourceEdgeEquiv edge) (relabeling.sourceVertexEquiv vertex) ↔
      Incident data edge vertex := by
  unfold Incident
  rw [relabeling.sourceEnds_sourceEdgeEquiv]
  simp only [Equiv.apply_eq_iff_eq]

/-- Canonical endpoints commute with their vertex's sheet permutation. -/
theorem sourceVertexEquiv_sourceEndpoint (relabeling : data.SheetRelabeling)
    (vertex : target.V) (sheet : Fin degree) :
    relabeling.sourceVertexEquiv (data.sourceEndpoint vertex sheet) =
      relabeling.apply.sourceEndpoint vertex (relabeling.vertexPermutation vertex sheet) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change relabeling.vertexPermutation vertex ((data.vertexPartition vertex).repr sheet) =
      relabeling.vertexPermutation vertex ((data.vertexPartition vertex).repr
        ((relabeling.vertexPermutation vertex).symm (relabeling.vertexPermutation vertex sheet)))
    rw [Equiv.symm_apply_apply]

/-- Canonical occurrences commute with the edge's sheet permutation. -/
theorem sourceEdgeEquiv_sourceEdge (relabeling : data.SheetRelabeling)
    (edge : target.edges) (sheet : Fin degree) :
    relabeling.sourceEdgeEquiv (data.sourceEdge edge sheet) =
      relabeling.apply.sourceEdge edge (relabeling.edgePermutation edge sheet) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change relabeling.edgePermutation edge ((data.edgePartition edge).repr sheet) =
      relabeling.edgePermutation edge ((data.edgePartition edge).repr
        ((relabeling.edgePermutation edge).symm (relabeling.edgePermutation edge sheet)))
    rw [Equiv.symm_apply_apply]

end DraismaVargas.LocalCases.SheetRelabelPruning
