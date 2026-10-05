module

public import DraismaVargas.LocalCases.PrunedFibreValency
public import DraismaVargas.Infrastructure.IteratedContraction
public import DraismaVargas.LocalCases.FullContractionFibre

@[expose] public section

/-!
# The induced-subtree count used by the pruned source fibre

A connected induced subgraph of a connected loopless multigraph with
`|E| + 1 = |V|` has the same tree equality.  We pass to the underlying simple
graph only after proving that the full tree count forbids repeated unoriented
occurrences; thus no multiplicities are silently discarded.
-/

namespace DraismaVargas.LocalCases.InducedFibreTreeCount

open Utilities

theorem count_unoriented_edge (graph : CFGraph) (first second : graph.V) :
    (graph.edges.map fun edge ↦ s(edge.1, edge.2)).count s(first, second) =
      num_edges graph first second := by
  classical
  rw [Multiset.count_eq_card_filter_eq, Multiset.filter_map, Multiset.card_map]
  unfold num_edges
  apply congrArg Multiset.card
  apply Multiset.filter_congr
  intro edge _
  simp only [Function.comp_apply, Sym2.eq_iff, Prod.ext_iff]
  tauto

theorem underlying_edgeFinset (graph : CFGraph) :
    (underlyingSimpleGraph graph).edgeFinset =
      (graph.edges.map fun edge ↦ s(edge.1, edge.2)).toFinset := by
  classical
  ext pair
  refine Sym2.ind ?_ pair
  intro first second
  rw [SimpleGraph.mem_edgeFinset, Multiset.mem_toFinset, ← Multiset.count_pos,
    count_unoriented_edge]
  rfl

theorem underlying_card_of_num_edges_le_one (graph : CFGraph)
    (hOne : ∀ first second : graph.V, num_edges graph first second ≤ 1) :
    (underlyingSimpleGraph graph).edgeFinset.card = graph.edges.card := by
  classical
  have hNodup : (graph.edges.map fun edge ↦ s(edge.1, edge.2)).Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro pair
    refine Sym2.ind ?_ pair
    intro first second
    rw [count_unoriented_edge]
    exact hOne first second
  rw [underlying_edgeFinset, Multiset.toFinset_card_of_nodup hNodup, Multiset.card_map]

/-- A connected multigraph with the tree edge count is genuinely a simple
tree.  The established genus-zero no-parallel lemma preserves all occurrences. -/
theorem underlying_tree_and_num_edges_le_one (graph : CFGraph)
    (hConnected : graph_connected graph)
    (hCount : graph.edges.card + 1 = Fintype.card graph.V) :
    (underlyingSimpleGraph graph).IsTree ∧
      ∀ first second : graph.V, num_edges graph first second ≤ 1 := by
  classical
  have hSimpleConnected := (graph_connected_iff_underlyingSimpleGraph_connected graph).mp hConnected
  have hGenus : genus graph = 0 := by
    unfold genus
    omega
  have hOne := DraismaVargas.Infrastructure.IteratedContraction.num_edges_le_one_of_genus_zero_of_connected
    graph hConnected hGenus
  have hSimpleCount := underlying_card_of_num_edges_le_one graph hOne
  constructor
  · apply SimpleGraph.isTree_iff_connected_and_card.mpr
    refine ⟨hSimpleConnected, ?_⟩
    simpa only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, hSimpleCount] using hCount
  · exact hOne

/-- A connected graph embedded in a multigraph tree, with its actual
multiplicities preserved, has the tree occurrence count. -/
theorem connected_multiplicity_embedding_tree_count (graph smaller : CFGraph)
    (hConnected : graph_connected graph)
    (hCount : graph.edges.card + 1 = Fintype.card graph.V)
    (hSmaller : graph_connected smaller) (embedding : smaller.V ↪ graph.V)
    (hMultiplicity : ∀ first second : smaller.V,
      num_edges smaller first second = num_edges graph (embedding first) (embedding second)) :
    smaller.edges.card + 1 = Fintype.card smaller.V := by
  classical
  obtain ⟨hTree, hOne⟩ := underlying_tree_and_num_edges_le_one graph hConnected hCount
  let inclusion : underlyingSimpleGraph smaller →g underlyingSimpleGraph graph :=
    { toFun := embedding
      map_rel' := by
        intro first second hAdj
        change 0 < num_edges graph (embedding first) (embedding second)
        change 0 < num_edges smaller first second at hAdj
        exact hMultiplicity first second ▸ hAdj }
  have hSimpleInduced : (underlyingSimpleGraph smaller).IsTree :=
    ⟨(graph_connected_iff_underlyingSimpleGraph_connected _).mp hSmaller,
      hTree.isAcyclic.comap inclusion embedding.injective⟩
  have hSimpleCount := underlying_card_of_num_edges_le_one smaller (fun first second ↦ by
    rw [hMultiplicity]
    exact hOne (embedding first) (embedding second))
  have hTreeCount := hSimpleInduced.card_edgeFinset
  rwa [hSimpleCount] at hTreeCount

end DraismaVargas.LocalCases.InducedFibreTreeCount

/-!
# The actual graph of a pruned contraction fibre

Source: Draisma–Vargas Part I, arXiv:1909.12924, the discussion of the non-dangling subgraph
above `A_0` preceding `lemma-ndval-of-GqA0` (subsection
`subsection-the-graph-GqA0`).  The inducing vertex set is the literal preimage
of a wall vertex, restricted to vertices carrying survivors.  An occurrence
joins two such vertices exactly when it is one of the surviving internal
contracted occurrences.  The connectedness proved here comes from
`PrunedContractionFibre`, not a user-supplied connectivity hypothesis.
-/

namespace DraismaVargas.LocalCases.PrunedFibreTree

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre
open W4StableSource WallDegeneration PrunedFibreValency
open PrunedContractionFibre ClassInjectivity DanglingDescent
open ContractionRamification FullContractionFibre InducedFibreTreeCount

variable {target : CFGraph} {degree : ℕ}

section Fibre

variable (data : GluingDatum target degree) {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

@[simp] theorem mem_activeFibreVertices
    (vertex : (contractDatum data hc hab hOne).SourceVertex) (first : data.SourceVertex) :
    first ∈ activeFibreVertices data hc hab hOne vertex ↔
      sourceVertexMap data hc hab hOne first = vertex ∧ nonDanglingValency data first ≠ 0 := by
  classical
  simp only [activeFibreVertices, Finset.mem_filter, mem_fibreVertices]

@[simp] theorem mem_internalEdges
    (vertex : (contractDatum data hc hab hOne).SourceVertex) (edge : data.SourceEdge) :
    edge ∈ internalEdges data hc hab hOne vertex ↔
      ¬ IsDangling data edge ∧ edge.1.1 = contracted ∧
        sourceVertexMap data hc hab hOne (data.sourceEnds edge).1 = vertex := by
  classical
  simp only [internalEdges, nonDanglingEdges, Finset.mem_filter, Finset.mem_univ, true_and]

/-- If both endpoints carry surviving occurrences, their joining occurrence
cannot dangle: either genus-zero cut side would kill its endpoint's valency. -/
theorem not_isDangling_of_active_ends (edge : data.SourceEdge)
    (hFirst : nonDanglingValency data (data.sourceEnds edge).1 ≠ 0)
    (hSecond : nonDanglingValency data (data.sourceEnds edge).2 ≠ 0) :
    ¬ IsDangling data edge := by
  intro hDangling
  rcases NonDanglingValency.danglingSide_of_isDangling data
    (edge := edge) (Or.inl rfl) hDangling with hCut | hCut
  · obtain ⟨cut⟩ := hCut
    exact hFirst (nonDanglingValency_eq_zero_of_danglingSide data cut)
  · obtain ⟨cut⟩ := hCut
    exact hSecond (nonDanglingValency_eq_zero_of_danglingSide data cut)

/-- Exact occurrence census for the induced active fibre.  Thus inducing in
the full source graph has already performed the required pruning. -/
theorem sourceEnds_mem_activeFibre_iff
    (vertex : (contractDatum data hc hab hOne).SourceVertex) (edge : data.SourceEdge) :
    ((data.sourceEnds edge).1 ∈ activeFibreVertices data hc hab hOne vertex ∧
      (data.sourceEnds edge).2 ∈ activeFibreVertices data hc hab hOne vertex) ↔
      edge ∈ internalEdges data hc hab hOne vertex := by
  rw [mem_activeFibreVertices, mem_activeFibreVertices, mem_internalEdges]
  constructor
  · rintro ⟨⟨hFirstMap, hFirst⟩, ⟨hSecondMap, hSecond⟩⟩
    refine ⟨not_isDangling_of_active_ends data edge hFirst hSecond, ?_, hFirstMap⟩
    by_contra hNe
    exact sourceVertexMap_sourceEnds_ne data hc hab hOne ⟨edge, hNe⟩
      (hFirstMap.trans hSecondMap.symm)
  · rintro ⟨hSurvive, hTarget, hFirstMap⟩
    have hMap := sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hOne edge hTarget
    exact ⟨⟨hFirstMap, nonDanglingValency_ne_zero_of_incident data hSurvive (Or.inl rfl)⟩,
      ⟨hMap.symm.trans hFirstMap,
        nonDanglingValency_ne_zero_of_incident data hSurvive (Or.inr rfl)⟩⟩

/-- The actual induced graph on the pruned contraction fibre. -/
noncomputable def activeFibreGraph
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNonempty : (activeFibreVertices data hc hab hOne vertex).Nonempty) : CFGraph :=
  Utilities.inducedSubgraph data.sourceGraph
    (activeFibreVertices data hc hab hOne vertex) hNonempty

/-- Its vertices are exactly the active source preimages, without isolated
vertices from dangling branches. -/
theorem activeFibreGraph_vertex_card
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNonempty : (activeFibreVertices data hc hab hOne vertex).Nonempty) :
    Fintype.card (activeFibreGraph data hc hab hOne vertex hNonempty).V =
      (activeFibreVertices data hc hab hOne vertex).card :=
  Utilities.inducedSubgraph_vertex_card _ _ _

/-- Its edges are exactly the surviving contracted occurrences, retaining
multiplicity even when several occurrences have the same endpoints. -/
theorem activeFibreGraph_edge_card
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNonempty : (activeFibreVertices data hc hab hOne vertex).Nonempty) :
    (activeFibreGraph data hc hab hOne vertex hNonempty).edges.card =
      (internalEdges data hc hab hOne vertex).card := by
  classical
  rw [show (activeFibreGraph data hc hab hOne vertex hNonempty).edges.card =
    (data.sourceGraph.edges.filter fun endpoints ↦
      endpoints.1 ∈ activeFibreVertices data hc hab hOne vertex ∧
        endpoints.2 ∈ activeFibreVertices data hc hab hOne vertex).card from
    Utilities.inducedSubgraph_edge_card_eq_filter data.sourceGraph _ hNonempty]
  change ((Finset.univ.val.map data.sourceEnds).filter fun endpoints ↦
    endpoints.1 ∈ activeFibreVertices data hc hab hOne vertex ∧
      endpoints.2 ∈ activeFibreVertices data hc hab hOne vertex).card = _
  rw [Multiset.filter_map, Multiset.card_map, ← Finset.filter_val]
  change (Finset.univ.filter fun edge ↦
    (data.sourceEnds edge).1 ∈ activeFibreVertices data hc hab hOne vertex ∧
      (data.sourceEnds edge).2 ∈ activeFibreVertices data hc hab hOne vertex).card = _
  apply congrArg Finset.card
  ext edge
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact sourceEnds_mem_activeFibre_iff data hc hab hOne vertex edge

/-- A surviving contracted walk lifts to a walk of the actual induced graph,
since its intermediate vertices also carry survivors and remain in the fibre. -/
theorem reach_activeFibreGraph_of_surviving_walk
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNonempty : (activeFibreVertices data hc hab hOne vertex).Nonempty)
    {first second : data.SourceVertex}
    (hFirst : first ∈ activeFibreVertices data hc hab hOne vertex)
    (hWalk : Relation.ReflTransGen (SurvivingFibreStep data contracted) first second) :
    ∀ hSecond : second ∈ activeFibreVertices data hc hab hOne vertex,
      Reach (activeFibreGraph data hc hab hOne vertex hNonempty)
        ⟨first, hFirst⟩ ⟨second, hSecond⟩ := by
  induction hWalk with
  | refl => intro _; exact reach_refl _ _
  | @tail middle last hWalk hStep ih =>
    intro hLast
    obtain ⟨edge, hTarget, hSurvive, hEnds⟩ := hStep
    have hMap := sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hOne edge hTarget
    have hLastMap := ((mem_activeFibreVertices data hc hab hOne vertex last).mp hLast).1
    have hMiddleMap : sourceVertexMap data hc hab hOne middle = vertex := by
      rcases hEnds with hEnds | hEnds
      · rw [hEnds] at hMap
        exact hMap.trans hLastMap
      · rw [hEnds] at hMap
        exact hMap.symm.trans hLastMap
    have hMiddle : middle ∈ activeFibreVertices data hc hab hOne vertex := by
      rw [mem_activeFibreVertices]
      exact ⟨hMiddleMap, nonDanglingValency_ne_zero_of_incident data hSurvive
        (incident_of_sourceEnds data hEnds)⟩
    refine reach_trans (ih hMiddle) (reach_single ?_)
    calc
      0 < num_edges data.sourceGraph middle last := num_edges_pos_of_sourceEnds data hEnds
      _ = num_edges (activeFibreGraph data hc hab hOne vertex hNonempty)
          ⟨middle, hMiddle⟩ ⟨last, hLast⟩ :=
        (Utilities.num_edges_inducedSubgraph data.sourceGraph
          (activeFibreVertices data hc hab hOne vertex) hNonempty
          ⟨middle, hMiddle⟩ ⟨last, hLast⟩).symm

/-- **The actual pruned fibre graph is connected.**  This consumes the proven
walk pruning theorem, with no connectivity or stable-path hypothesis. -/
theorem activeFibreGraph_connected
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNonempty : (activeFibreVertices data hc hab hOne vertex).Nonempty) :
    graph_connected (activeFibreGraph data hc hab hOne vertex hNonempty) := by
  let first := hNonempty.choose
  have hFirst : first ∈ activeFibreVertices data hc hab hOne vertex := hNonempty.choose_spec
  apply graph_connected_of_reach
    (⟨first, hFirst⟩ : (activeFibreGraph data hc hab hOne vertex hNonempty).V)
  intro second
  have hFirstInfo := (mem_activeFibreVertices data hc hab hOne vertex first).mp hFirst
  have hSecondInfo := (mem_activeFibreVertices data hc hab hOne vertex second.1).mp second.2
  have hWalk := (sourceVertexMap_eq_iff_surviving_walk data hc hab hOne
    hFirstInfo.2 hSecondInfo.2).mp (hFirstInfo.1.trans hSecondInfo.1.symm)
  exact reach_activeFibreGraph_of_surviving_walk data hc hab hOne vertex hNonempty
    hFirst hWalk second.2

/-- The connectedness half of the pruned fibre Euler count.  The opposite
inequality still requires the full fibre forest hypothesis. -/
theorem activeFibreVertices_card_le_internalEdges_card_add_one
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNonempty : (activeFibreVertices data hc hab hOne vertex).Nonempty) :
    (activeFibreVertices data hc hab hOne vertex).card ≤
      (internalEdges data hc hab hOne vertex).card + 1 := by
  have hBound := Utilities.graph_connected_card_vertices_le_card_edges_add_one _
    (activeFibreGraph_connected data hc hab hOne vertex hNonempty)
  rwa [activeFibreGraph_vertex_card, activeFibreGraph_edge_card] at hBound

/-- Every wall source vertex has a literal nonempty full preimage. -/
theorem fibreVertices_nonempty
    (vertex : (contractDatum data hc hab hOne).SourceVertex) :
    (fibreVertices data hc hab hOne vertex).Nonempty := by
  obtain ⟨first, hFirst⟩ := sourceVertexMap_surjective data hc hab hOne vertex
  exact ⟨first, (mem_fibreVertices data hc hab hOne vertex first).mpr hFirst⟩

/-- The full, unpruned actual fibre graph. -/
noncomputable def fullFibreGraph (vertex : (contractDatum data hc hab hOne).SourceVertex) : CFGraph :=
  Utilities.inducedSubgraph data.sourceGraph (fibreVertices data hc hab hOne vertex)
    (fibreVertices_nonempty data hc hab hOne vertex)

theorem fullFibreGraph_vertex_card
    (vertex : (contractDatum data hc hab hOne).SourceVertex) :
    Fintype.card (fullFibreGraph data hc hab hOne vertex).V =
      (fibreVertices data hc hab hOne vertex).card :=
  Utilities.inducedSubgraph_vertex_card _ _ _

/-- The full graph's multiset counts exactly the block-level
`fullInternalEdges`, which are identified with actual source occurrences. -/
theorem fullFibreGraph_edge_card
    (block : (mergedPartition data a b).Blocks) :
    (fullFibreGraph data hc hab hOne (mergedVertex data hc hab hOne block)).edges.card =
      (fullInternalEdges data contracted block).card := by
  classical
  let vertex := mergedVertex data hc hab hOne block
  rw [show (fullFibreGraph data hc hab hOne vertex).edges.card =
    (data.sourceGraph.edges.filter fun endpoints ↦
      endpoints.1 ∈ fibreVertices data hc hab hOne vertex ∧
        endpoints.2 ∈ fibreVertices data hc hab hOne vertex).card from
    Utilities.inducedSubgraph_edge_card_eq_filter data.sourceGraph _ _]
  change ((Finset.univ.val.map data.sourceEnds).filter fun endpoints ↦
    endpoints.1 ∈ fibreVertices data hc hab hOne vertex ∧
      endpoints.2 ∈ fibreVertices data hc hab hOne vertex).card = _
  rw [Multiset.filter_map, Multiset.card_map, ← Finset.filter_val]
  change (Finset.univ.filter fun edge ↦
    (data.sourceEnds edge).1 ∈ fibreVertices data hc hab hOne vertex ∧
      (data.sourceEnds edge).2 ∈ fibreVertices data hc hab hOne vertex).card = _
  apply congrArg Finset.card
  ext edge
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact sourceEnds_mem_fibre_mergedVertex_iff data hc hab hOne block edge

theorem reach_fullFibreGraph_of_walk
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    {first second : data.SourceVertex}
    (hFirst : first ∈ fibreVertices data hc hab hOne vertex)
    (hWalk : Relation.ReflTransGen (FibreStep data contracted) first second) :
    ∀ hSecond : second ∈ fibreVertices data hc hab hOne vertex,
      Reach (fullFibreGraph data hc hab hOne vertex) ⟨first, hFirst⟩ ⟨second, hSecond⟩ := by
  induction hWalk with
  | refl => intro _; exact reach_refl _ _
  | @tail middle last hWalk hStep ih =>
    intro hLast
    have hMap := (sourceVertexMap_eq_iff data hc hab hOne middle last).mpr
      hStep.reachThroughContracted
    have hMiddle : middle ∈ fibreVertices data hc hab hOne vertex := by
      rw [mem_fibreVertices]
      exact hMap.trans ((mem_fibreVertices data hc hab hOne vertex last).mp hLast)
    refine reach_trans (ih hMiddle) (reach_single ?_)
    calc
      0 < num_edges data.sourceGraph middle last := hStep.num_edges_pos
      _ = num_edges (fullFibreGraph data hc hab hOne vertex) ⟨middle, hMiddle⟩ ⟨last, hLast⟩ :=
        (Utilities.num_edges_inducedSubgraph data.sourceGraph
          (fibreVertices data hc hab hOne vertex) (fibreVertices_nonempty data hc hab hOne vertex)
          ⟨middle, hMiddle⟩ ⟨last, hLast⟩).symm

theorem fullFibreGraph_connected
    (vertex : (contractDatum data hc hab hOne).SourceVertex) :
    graph_connected (fullFibreGraph data hc hab hOne vertex) := by
  let first := (fibreVertices_nonempty data hc hab hOne vertex).choose
  have hFirst : first ∈ fibreVertices data hc hab hOne vertex :=
    (fibreVertices_nonempty data hc hab hOne vertex).choose_spec
  apply graph_connected_of_reach (⟨first, hFirst⟩ : (fullFibreGraph data hc hab hOne vertex).V)
  intro second
  have hMap := ((mem_fibreVertices data hc hab hOne vertex first).mp hFirst).trans
    ((mem_fibreVertices data hc hab hOne vertex second.1).mp second.2).symm
  exact reach_fullFibreGraph_of_walk data hc hab hOne vertex hFirst
    (reflTransGen_fibreStep_of_reachThroughContracted data contracted
      ((sourceVertexMap_eq_iff data hc hab hOne first second.1).mp hMap)) second.2

theorem fullFibreGraph_tree_count
    (hForest : ContractionForest data a b contracted)
    (block : (mergedPartition data a b).Blocks) :
    (fullFibreGraph data hc hab hOne (mergedVertex data hc hab hOne block)).edges.card + 1 =
      Fintype.card (fullFibreGraph data hc hab hOne (mergedVertex data hc hab hOne block)).V := by
  rw [fullFibreGraph_edge_card, fullFibreGraph_vertex_card]
  exact fullInternalEdges_card_add_one_eq_fibreVertices_card data hc hab hOne hForest block

/-- **The source's pruned fibre is an actual tree.**  Its connectedness was
proved by pruning walks.  Its upper edge bound is inherited from the full fibre
tree count, via the actual multiplicity-preserving vertex inclusion. -/
theorem internalEdges_card_add_one_eq_activeFibreVertices_card
    (hForest : ContractionForest data a b contracted)
    (block : (mergedPartition data a b).Blocks)
    (hNonempty : (activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block)).Nonempty) :
    (internalEdges data hc hab hOne (mergedVertex data hc hab hOne block)).card + 1 =
      (activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block)).card := by
  let vertex := mergedVertex data hc hab hOne block
  let embedding : (activeFibreGraph data hc hab hOne vertex hNonempty).V ↪
      (fullFibreGraph data hc hab hOne vertex).V :=
    { toFun := fun first ↦ ⟨first.1,
        (mem_fibreVertices data hc hab hOne vertex first.1).mpr
          ((mem_activeFibreVertices data hc hab hOne vertex first.1).mp first.2).1⟩
      inj' := fun _ _ h ↦ Subtype.ext
        (congrArg (fun first : (fullFibreGraph data hc hab hOne vertex).V ↦ first.1) h) }
  have hCount := connected_multiplicity_embedding_tree_count
    (fullFibreGraph data hc hab hOne vertex)
    (activeFibreGraph data hc hab hOne vertex hNonempty)
    (fullFibreGraph_connected data hc hab hOne vertex)
    (fullFibreGraph_tree_count data hc hab hOne hForest block)
    (activeFibreGraph_connected data hc hab hOne vertex hNonempty)
    embedding (fun first second ↦
      (Utilities.num_edges_inducedSubgraph data.sourceGraph
        (activeFibreVertices data hc hab hOne vertex) hNonempty first second).trans
        (Utilities.num_edges_inducedSubgraph data.sourceGraph
          (fibreVertices data hc hab hOne vertex) (fibreVertices_nonempty data hc hab hOne vertex)
          (embedding first) (embedding second)).symm)
  rwa [activeFibreGraph_edge_card, activeFibreGraph_vertex_card] at hCount

/-- A wall vertex carrying survivors has at least one active incoming
preimage, by the already-proved occurrence accounting. -/
theorem activeFibreVertices_nonempty_of_nonDanglingValency_ne_zero
    (hCompat : DanglingCompatible data hc hab hOne)
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNonzero : nonDanglingValency (contractDatum data hc hab hOne) vertex ≠ 0) :
    (activeFibreVertices data hc hab hOne vertex).Nonempty := by
  classical
  by_contra hEmpty
  have hAccounting := sum_nonDanglingValency_activeFibre data hc hab hOne hCompat vertex
  rw [Finset.not_nonempty_iff_eq_empty.mp hEmpty, Finset.sum_empty] at hAccounting
  omega

/-- **Draisma–Vargas `lemma-ndval-of-GqA0`.**  The wall valency is two plus
the sum of incoming pruned valency excesses.  Both the tree count and the
occurrence accounting have been derived from the actual contraction. -/
theorem nonDanglingValency_mergedVertex_eq_sum
    (hCompat : DanglingCompatible data hc hab hOne)
    (hForest : ContractionForest data a b contracted)
    (block : (mergedPartition data a b).Blocks)
    (hNonzero : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) ≠ 0) :
    (nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) : ℤ) =
      (∑ first ∈ activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block),
        ((nonDanglingValency data first : ℤ) - 2)) + 2 := by
  have hNonempty := activeFibreVertices_nonempty_of_nonDanglingValency_ne_zero
    data hc hab hOne hCompat _ hNonzero
  have hAccounting :
      (∑ first ∈ activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block),
        (nonDanglingValency data first : ℤ)) =
      (nonDanglingValency (contractDatum data hc hab hOne)
        (mergedVertex data hc hab hOne block) : ℤ) +
        2 * ((internalEdges data hc hab hOne (mergedVertex data hc hab hOne block)).card : ℤ) := by
    exact_mod_cast sum_nonDanglingValency_activeFibre data hc hab hOne hCompat
      (mergedVertex data hc hab hOne block)
  have hTree : ((internalEdges data hc hab hOne (mergedVertex data hc hab hOne block)).card : ℤ) + 1 =
      ((activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block)).card : ℤ) := by
    exact_mod_cast internalEdges_card_add_one_eq_activeFibreVertices_card
      data hc hab hOne hForest block hNonempty
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  omega

/-- A divalent wall fibre contains only divalent active incoming vertices.
This is the source-facing input needed to transport actual stable adjacency
through that pruned fibre. -/
theorem nonDanglingValency_eq_two_of_mem_activeFibre
    (hConnected : graph_connected data.sourceGraph)
    (hCompat : DanglingCompatible data hc hab hOne)
    (hForest : ContractionForest data a b contracted)
    (block : (mergedPartition data a b).Blocks)
    (hTwo : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) = 2)
    (first : data.SourceVertex)
    (hFirst : first ∈ activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block)) :
    nonDanglingValency data first = 2 := by
  have hFormula := nonDanglingValency_mergedVertex_eq_sum data hc hab hOne hCompat hForest block
    (by omega)
  rw [hTwo] at hFormula
  have hSum : (∑ vertex ∈ activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block),
      ((nonDanglingValency data vertex : ℤ) - 2)) = 0 := by omega
  have hNonneg : ∀ vertex ∈ activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block),
      0 ≤ (nonDanglingValency data vertex : ℤ) - 2 := by
    intro vertex hVertex
    have hNeZero := ((mem_activeFibreVertices data hc hab hOne _ _).mp hVertex).2
    have hNeOne := NonDanglingValency.nonDanglingValency_ne_one data hConnected vertex
    omega
  have hZero := (Finset.sum_eq_zero_iff_of_nonneg hNonneg).mp hSum first hFirst
  omega

/-- **The divalent-fibre input for stable-path transport, at every actual
wall source vertex.**  At the merge this is the pruned-tree valency formula;
away from it this is the existing incidence-preserving contraction bijection.
No stable-path correspondence is assumed. -/
theorem nonDanglingValency_eq_two_of_sourceVertexMap_eq
    (hConnected : graph_connected data.sourceGraph)
    (hCompat : DanglingCompatible data hc hab hOne)
    (hForest : ContractionForest data a b contracted)
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hTwo : nonDanglingValency (contractDatum data hc hab hOne) vertex = 2)
    (first : data.SourceVertex)
    (hMap : sourceVertexMap data hc hab hOne first = vertex)
    (hNonzero : nonDanglingValency data first ≠ 0) :
    nonDanglingValency data first = 2 := by
  by_cases hAtMerge : first.1.1 = a ∨ first.1.1 = b
  · have hVertexTarget : vertex.1.1 = ⟨a, hab⟩ := by
      have hProjection := congrArg
        (fun second : (contractDatum data hc hab hOne).SourceVertex ↦ second.1.1) hMap
      change fold target hab first.1.1 = vertex.1.1 at hProjection
      exact hProjection.symm.trans (fold_eq_of_eq_or hab hAtMerge)
    let block : (mergedPartition data a b).Blocks := ⟨vertex.1.2, by
      have hFixed := vertex.2
      change ((contractDatum data hc hab hOne).vertexPartition vertex.1.1).repr vertex.1.2 =
        vertex.1.2 at hFixed
      rw [hVertexTarget, contractDatum_vertexPartition_merge] at hFixed
      exact hFixed⟩
    have hVertex : mergedVertex data hc hab hOne block = vertex :=
      Subtype.ext (Prod.ext hVertexTarget.symm rfl)
    apply nonDanglingValency_eq_two_of_mem_activeFibre data hc hab hOne
      hConnected hCompat hForest block (by rw [hVertex]; exact hTwo) first
    rw [mem_activeFibreVertices]
    exact ⟨hMap.trans hVertex.symm, hNonzero⟩
  · have hFirstA : first.1.1 ≠ a := fun h ↦ hAtMerge (Or.inl h)
    have hFirstB : first.1.1 ≠ b := fun h ↦ hAtMerge (Or.inr h)
    have hPreserved := nonDanglingValency_sourceVertexMap data hCompat first hFirstA hFirstB
    rw [hMap] at hPreserved
    exact hPreserved.symm.trans hTwo

end Fibre

end DraismaVargas.LocalCases.PrunedFibreTree
