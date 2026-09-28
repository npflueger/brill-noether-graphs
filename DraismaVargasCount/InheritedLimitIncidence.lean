import DraismaVargasCount.InheritedLimitBranches

/-!
# Actual inherited stable-core incidence at a positive-request limit

The branch and stable-row dictionaries already come from the literal source
contraction. Here we prove that those dictionaries preserve every incidence
multiplicity, and therefore construct `coreIdentification` with precisely
`InheritedLimitBranches.branchLabel` and `InheritedLimitRows.rowLabel`.

For a fixed incoming branch and row, restrict its contraction fibre to vertices
meeting that row. Every constituent other than the unique incoming branch is
divalent and contributes two row incidences. The induced graph has exactly the
row's surviving internal occurrences; it embeds, with multiplicities, into the
actual full-fibre tree. Its forest bound and the row-wise handshake imply that
the row's boundary count is at least its incoming branch incidence. The actual
retained-occurrence embedding identifies that boundary count with the limit
incidence. Both branch valencies are three, so the inequalities over all rows
sum to equality and hence each is equality.

This argument counts occurrences, not merely which rows meet a branch. Thus a
stable loop's two incidences remain distinct throughout. Forest, pruning, row
and branch bijections, and incidence preservation are all produced from the
actual positive-request `Regrowth`; none is an extra compatibility receipt.
-/

namespace DraismaVargas.Count.InheritedLimitIncidence
open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction GraphContraction ContractionFibre ContractionRamification
open W4StableSource WallDegeneration FullDimensionalSource
open PrunedFibreValency PrunedFibreTree PrunedContractionFibre FullContractionFibre
open StableGraphIncidence InheritedLimitRows InheritedLimitBranches SegmentWalls WallStar
open StablePathCount InducedFibreTreeCount
open Utilities.Certificate.ExplicitPotential (Core)

/-- An occurrence-preserving subgraph of a finite tree is a forest, even if
the subgraph is disconnected. -/
theorem multiplicity_embedding_forest_bound (graph smaller : CFGraph)
    (hConnected : graph_connected graph)
    (hCount : graph.edges.card + 1 = Fintype.card graph.V)
    (embedding : smaller.V ↪ graph.V)
    (hMultiplicity : ∀ first second : smaller.V,
      num_edges smaller first second ≤ num_edges graph (embedding first) (embedding second)) :
    smaller.edges.card + 1 ≤ Fintype.card smaller.V := by
  classical
  obtain ⟨hTree, hOne⟩ := underlying_tree_and_num_edges_le_one graph hConnected hCount
  let inclusion : Utilities.underlyingSimpleGraph smaller →g Utilities.underlyingSimpleGraph graph :=
    { toFun := embedding
      map_rel' := by
        intro first second hAdj
        exact lt_of_lt_of_le hAdj (hMultiplicity first second) }
  have hAcyclic := hTree.isAcyclic.comap inclusion embedding.injective
  obtain ⟨tree, hSub, _, hTree'⟩ :=
    SimpleGraph.Connected.exists_isTree_le_of_le_of_isAcyclic
      (SimpleGraph.connected_top : (⊤ : SimpleGraph smaller.V).Connected) le_top hAcyclic
  have hEdges : (Utilities.underlyingSimpleGraph smaller).edgeFinset.card ≤ tree.edgeFinset.card :=
    Finset.card_mono (by simpa using hSub)
  rw [underlying_card_of_num_edges_le_one smaller (fun first second ↦
    (hMultiplicity first second).trans (hOne _ _))] at hEdges
  have hTreeCount := hTree'.card_edgeFinset
  omega

/-- The row-wise handshake counts literal surviving occurrences, so repeated
stable-row incidences at a branch are retained. -/
theorem sum_incidenceCount_set {target : CFGraph} {degree : ℕ}
    (data : GluingDatum target degree) (vertices : Finset data.SourceVertex)
    (row : StablePath data) :
    ∑ vertex ∈ vertices, incidenceCount data vertex row =
      ∑ edge ∈ classEdges data row,
        ((if (data.sourceEnds edge.1).1 ∈ vertices then 1 else 0) +
          (if (data.sourceEnds edge.1).2 ∈ vertices then 1 else 0)) := by
  classical
  have hAt (vertex : data.SourceVertex) :
      incidenceCount data vertex row =
        ∑ edge ∈ classEdges data row,
          ((if (data.sourceEnds edge.1).1 = vertex then 1 else 0) +
            (if (data.sourceEnds edge.1).2 = vertex then 1 else 0)) := by
    unfold incidenceCount incidentEdges classEdges
    rw [Finset.filter_filter, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro edge _
    have hNe := data.sourceEnds_ne edge.1
    by_cases hr : edge.stablePath = row <;>
      by_cases hFirst : (data.sourceEnds edge.1).1 = vertex <;>
      by_cases hSecond : (data.sourceEnds edge.1).2 = vertex
    all_goals simp_all [Incident]
  simp_rw [hAt]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro edge _
  rw [Finset.sum_add_distrib]
  simp

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)

noncomputable def rowVertices (v : w.limit.SourceVertex) (row : StablePath w.frame.data) :
    Finset w.frame.data.SourceVertex := by
  classical
  exact (PrunedFibreValency.fibreVertices w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
    (w.frame.numEdges_edgeOf w.column) v).filter
    (fun u ↦ 0 < incidenceCount w.frame.data u row)

theorem mem_rowVertices (v : w.limit.SourceVertex) (row : StablePath w.frame.data)
    (u : w.frame.data.SourceVertex) :
    u ∈ rowVertices w v row ↔ vertexMap w u = v ∧ 0 < incidenceCount w.frame.data u row := by
  classical
  simp only [rowVertices, PrunedFibreValency.fibreVertices, Finset.mem_filter,
    Finset.mem_univ, true_and, vertexMap]
  rfl

noncomputable def rowInternalEdges (v : w.limit.SourceVertex) (row : StablePath w.frame.data) :
    Finset (NonDanglingEdge w.frame.data) := by
  classical
  exact (classEdges w.frame.data row).filter (fun e ↦
    e.1.1.1 = w.frame.edgeOf w.column ∧ vertexMap w (w.frame.data.sourceEnds e.1).1 = v)

noncomputable def rowBoundaryEdges (v : w.limit.SourceVertex) (row : StablePath w.frame.data) :
    Finset (NonDanglingEdge w.frame.data) := by
  classical
  exact (classEdges w.frame.data row).filter (fun e ↦
    e.1.1.1 ≠ w.frame.edgeOf w.column ∧
      (vertexMap w (w.frame.data.sourceEnds e.1).1 = v ∨
        vertexMap w (w.frame.data.sourceEnds e.1).2 = v))

set_option backward.isDefEq.respectTransparency.types false in
theorem row_fibre_handshake (v : w.limit.SourceVertex) (row : StablePath w.frame.data) :
    ∑ u ∈ rowVertices w v row, incidenceCount w.frame.data u row =
      (rowBoundaryEdges w v row).card + 2 * (rowInternalEdges w v row).card := by
  classical
  have hSum : ∑ u ∈ rowVertices w v row, incidenceCount w.frame.data u row =
      ∑ u ∈ PrunedFibreValency.fibreVertices w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
        (w.frame.numEdges_edgeOf w.column) v, incidenceCount w.frame.data u row := by
    unfold rowVertices
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro u _
    split_ifs <;> omega
  rw [hSum, sum_incidenceCount_set]
  simp only [PrunedFibreValency.fibreVertices, Finset.mem_filter, Finset.mem_univ, true_and,
    rowBoundaryEdges, rowInternalEdges,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro edge _
  have hmap (u : w.frame.data.SourceVertex) :
      sourceVertexMap w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
        (w.frame.numEdges_edgeOf w.column) u = vertexMap w u := rfl
  simp only [hmap]
  by_cases he : edge.1.1.1 = w.frame.edgeOf w.column
  · have hm := sourceVertexMap_sourceEnds_eq_of_contracted w.frame.data rfl
      (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) edge.1 he
    change vertexMap w (w.frame.data.sourceEnds edge.1).1 =
      vertexMap w (w.frame.data.sourceEnds edge.1).2 at hm
    by_cases hf : vertexMap w (w.frame.data.sourceEnds edge.1).1 = v
    · have hs := hm.symm.trans hf
      simp [he,hf,hs]
    · have hs : vertexMap w (w.frame.data.sourceEnds edge.1).2 ≠ v := fun h ↦ hf (hm.trans h)
      simp [he,hf,hs]
      exact ⟨hf,hs⟩
  · have hm := sourceVertexMap_sourceEnds_ne w.frame.data rfl
      (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) ⟨edge.1,he⟩
    change vertexMap w (w.frame.data.sourceEnds edge.1).1 ≠
      vertexMap w (w.frame.data.sourceEnds edge.1).2 at hm
    by_cases hf : vertexMap w (w.frame.data.sourceEnds edge.1).1 = v <;>
      by_cases hs : vertexMap w (w.frame.data.sourceEnds edge.1).2 = v
    all_goals simp_all <;> first | exact ⟨hf,hs⟩ | exact hf | exact hs

include hy in
theorem divalent_of_fibre_ne_branch (v : BranchVertex w.frame.data)
    (u : w.frame.data.SourceVertex) (hu : vertexMap w u = vertexMap w v.1)
    (hActive : nonDanglingValency w.frame.data u ≠ 0) (hne : u ≠ v.1) :
    nonDanglingValency w.frame.data u = 2 := by
  have hUpper := w.frame.fullDim.trivalent u
  have hNotOne := NonDanglingValency.nonDanglingValency_ne_one _ w.frame.fullDim.connected u
  have hNotThree : nonDanglingValency w.frame.data u ≠ 3 := by
    intro hThree
    have hBranch : (⟨u,by omega⟩ : BranchVertex w.frame.data) = v :=
      branchMap_injective w hy (Subtype.ext hu)
    exact hne (congrArg Subtype.val hBranch)
  omega

include hy in
theorem incidenceCount_rowVertices_ne_branch (v : BranchVertex w.frame.data)
    (row : StablePath w.frame.data) (u : w.frame.data.SourceVertex)
    (hu : u ∈ rowVertices w (vertexMap w v.1) row) (hne : u ≠ v.1) :
    incidenceCount w.frame.data u row = 2 := by
  obtain ⟨hMap,hPos⟩ := (mem_rowVertices w _ _ _).mp hu
  obtain ⟨edge,hInc,_⟩ := (incidenceCount_pos_iff _ _ _).mp hPos
  have hActive := ClassInjectivity.nonDanglingValency_ne_zero_of_incident _ edge.2 hInc
  have hTwo := divalent_of_fibre_ne_branch w hy v u hMap hActive hne
  rcases incidenceCount_eq_zero_or_two w.frame.data hTwo row with hZero | hTwo
  · omega
  · exact hTwo

include hy in
theorem sourceEnds_mem_rowVertices_iff (v : BranchVertex w.frame.data)
    (row : StablePath w.frame.data) (edge : w.frame.data.SourceEdge) :
    ((w.frame.data.sourceEnds edge).1 ∈ rowVertices w (vertexMap w v.1) row ∧
      (w.frame.data.sourceEnds edge).2 ∈ rowVertices w (vertexMap w v.1) row) ↔
      ∃ h : ¬ IsDangling w.frame.data edge,
        (⟨edge,h⟩ : NonDanglingEdge w.frame.data) ∈ rowInternalEdges w (vertexMap w v.1) row := by
  classical
  constructor
  · rintro ⟨hf,hs⟩
    obtain ⟨hmf,hpf⟩ := (mem_rowVertices w _ _ _).mp hf
    obtain ⟨hms,hps⟩ := (mem_rowVertices w _ _ _).mp hs
    obtain ⟨ef,hif,_⟩ := (incidenceCount_pos_iff _ _ _).mp hpf
    obtain ⟨es,his,_⟩ := (incidenceCount_pos_iff _ _ _).mp hps
    have haf := ClassInjectivity.nonDanglingValency_ne_zero_of_incident _ ef.2 hif
    have has := ClassInjectivity.nonDanglingValency_ne_zero_of_incident _ es.2 his
    have hSurvive := not_isDangling_of_active_ends w.frame.data edge haf has
    have hTarget : edge.1.1 = w.frame.edgeOf w.column := by
      by_contra he
      exact sourceVertexMap_sourceEnds_ne w.frame.data rfl
        (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
        ⟨edge,he⟩ (hmf.trans hms.symm)
    have hRow : NonDanglingEdge.stablePath (⟨edge,hSurvive⟩ : NonDanglingEdge w.frame.data) = row := by
      have hAt (u : w.frame.data.SourceVertex)
          (hu : u ∈ rowVertices w (vertexMap w v.1) row)
          (hInc : Incident w.frame.data edge u) (hne : u ≠ v.1) :
          NonDanglingEdge.stablePath (⟨edge,hSurvive⟩ : NonDanglingEdge w.frame.data) = row := by
        obtain ⟨hm,hp⟩ := (mem_rowVertices w _ _ _).mp hu
        obtain ⟨f,hf,hrow⟩ := (incidenceCount_pos_iff _ _ _).mp hp
        have hTwo := divalent_of_fibre_ne_branch w hy v u hm
          (ClassInjectivity.nonDanglingValency_ne_zero_of_incident _ f.2 hf) hne
        exact (PrunedFibreStablePath.stablePath_eq_of_incident_divalent _
          ⟨edge,hSurvive⟩ f u hInc hf hTwo).trans hrow
      by_cases hFirst : (w.frame.data.sourceEnds edge).1 = v.1
      · exact hAt _ hs (Or.inr rfl) (fun h ↦ w.frame.data.sourceEnds_ne edge (hFirst.trans h.symm))
      · exact hAt _ hf (Or.inl rfl) hFirst
    exact ⟨hSurvive,Finset.mem_filter.mpr ⟨(mem_classEdges _ _ _).mpr hRow,hTarget,hmf⟩⟩
  · rintro ⟨hSurvive,hEdge⟩
    obtain ⟨hRow,hTarget,hMap⟩ := Finset.mem_filter.mp hEdge
    have hr := (mem_classEdges _ _ _).mp hRow
    have hm := sourceVertexMap_sourceEnds_eq_of_contracted w.frame.data rfl
      (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) edge hTarget
    exact ⟨(mem_rowVertices w _ _ _).mpr ⟨hMap,
      (incidenceCount_pos_iff _ _ _).mpr ⟨⟨edge,hSurvive⟩,Or.inl rfl,hr⟩⟩,
      (mem_rowVertices w _ _ _).mpr ⟨hm.symm.trans hMap,
      (incidenceCount_pos_iff _ _ _).mpr ⟨⟨edge,hSurvive⟩,Or.inr rfl,hr⟩⟩⟩

noncomputable def rowFibreGraph (v : BranchVertex w.frame.data) (row : StablePath w.frame.data)
    (hPos : 0 < incidenceCount w.frame.data v.1 row) : CFGraph :=
  Utilities.inducedSubgraph w.frame.data.sourceGraph (rowVertices w (vertexMap w v.1) row)
    ⟨v.1,(mem_rowVertices w _ _ _).mpr ⟨rfl,hPos⟩⟩

include hy in
theorem rowFibreGraph_edge_card (v : BranchVertex w.frame.data) (row : StablePath w.frame.data)
    (hPos : 0 < incidenceCount w.frame.data v.1 row) :
    (rowFibreGraph w v row hPos).edges.card = (rowInternalEdges w (vertexMap w v.1) row).card := by
  classical
  rw [show (rowFibreGraph w v row hPos).edges.card =
    (w.frame.data.sourceGraph.edges.filter fun endpoints ↦
      endpoints.1 ∈ rowVertices w (vertexMap w v.1) row ∧
        endpoints.2 ∈ rowVertices w (vertexMap w v.1) row).card from
    Utilities.inducedSubgraph_edge_card_eq_filter w.frame.data.sourceGraph _ _]
  change ((Finset.univ.val.map w.frame.data.sourceEnds).filter fun endpoints ↦
    endpoints.1 ∈ rowVertices w (vertexMap w v.1) row ∧
      endpoints.2 ∈ rowVertices w (vertexMap w v.1) row).card = _
  rw [Multiset.filter_map, Multiset.card_map, ← Finset.filter_val]
  symm
  apply Finset.card_bij (fun edge _ ↦ edge.1)
  · intro edge he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (sourceEnds_mem_rowVertices_iff w hy v row edge.1).mpr ⟨edge.2,he⟩⟩
  · intro e _ f _ h
    exact Subtype.ext h
  · intro edge he
    obtain ⟨hSurvive,hmem⟩ := (sourceEnds_mem_rowVertices_iff w hy v row edge).mp
      (Finset.mem_filter.mp he).2
    exact ⟨⟨edge,hSurvive⟩,hmem,rfl⟩

include hy in
theorem full_fibre_tree_count (v : w.limit.SourceVertex)
    (hMerge : v.1.1 =
      ⟨(w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1,
        fst_ne_snd (w.frame.edgeOf w.column)⟩) :
    (fullFibreGraph w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) v).edges.card + 1 =
      Fintype.card (fullFibreGraph w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
        (w.frame.numEdges_edgeOf w.column) v).V := by
  obtain ⟨block,rfl⟩ := exists_mergedBlock w v hMerge
  exact fullFibreGraph_tree_count w.frame.data rfl
    (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) (forest w hy) block

include hy in
theorem rowInternalEdges_forest_bound_merged (v : BranchVertex w.frame.data)
    (row : StablePath w.frame.data) (hPos : 0 < incidenceCount w.frame.data v.1 row)
    (hMerge : (vertexMap w v.1).1.1 =
      ⟨(w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1,
        fst_ne_snd (w.frame.edgeOf w.column)⟩) :
    (rowInternalEdges w (vertexMap w v.1) row).card + 1 ≤
      (rowVertices w (vertexMap w v.1) row).card := by
  let full := fullFibreGraph w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
    (w.frame.numEdges_edgeOf w.column) (vertexMap w v.1)
  let embedding : (rowFibreGraph w v row hPos).V ↪ full.V :=
    { toFun := fun u ↦ ⟨u.1,(PrunedFibreValency.mem_fibreVertices _ _ _ _ _ _).mpr
        ((mem_rowVertices w _ _ _).mp u.2).1⟩
      inj' := fun _ _ h ↦ Subtype.ext (congrArg (fun u : full.V ↦ u.1) h) }
  have hCount : full.edges.card + 1 = Fintype.card full.V :=
    full_fibre_tree_count w hy _ hMerge
  have hBound := multiplicity_embedding_forest_bound full (rowFibreGraph w v row hPos)
    (fullFibreGraph_connected _ _ _ _ _) hCount embedding (fun first second ↦ by
      exact le_of_eq ((Utilities.num_edges_inducedSubgraph w.frame.data.sourceGraph
        (rowVertices w (vertexMap w v.1) row) _ first second).trans
        (Utilities.num_edges_inducedSubgraph w.frame.data.sourceGraph
          _ _ (embedding first) (embedding second)).symm))
  rw [rowFibreGraph_edge_card w hy v row hPos] at hBound
  exact hBound.trans_eq (Utilities.inducedSubgraph_vertex_card _ _ _)

include hy in
theorem rowInternalEdges_forest_bound (v : BranchVertex w.frame.data)
    (row : StablePath w.frame.data) (hPos : 0 < incidenceCount w.frame.data v.1 row) :
    (rowInternalEdges w (vertexMap w v.1) row).card + 1 ≤
      (rowVertices w (vertexMap w v.1) row).card := by
  classical
  by_cases hMerge : (vertexMap w v.1).1.1 =
      ⟨(w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1,
        fst_ne_snd (w.frame.edgeOf w.column)⟩
  · exact rowInternalEdges_forest_bound_merged w hy v row hPos hMerge
  · have hEmpty : rowInternalEdges w (vertexMap w v.1) row = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro edge he
      obtain ⟨_,hTarget,hMap⟩ := Finset.mem_filter.mp he
      apply hMerge
      have hFirst : (w.frame.data.sourceEnds edge.1).1.1.1 =
          (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1 :=
        congrArg (fun e : w.frame.target.edges ↦ (e : w.frame.target.V × w.frame.target.V).1) hTarget
      exact (congrArg (fun u : w.limit.SourceVertex ↦ u.1.1) hMap).symm.trans
        (fold_eq_of_eq_or _ (Or.inl hFirst))
    rw [hEmpty, Finset.card_empty, zero_add]
    exact Finset.card_pos.mpr ⟨v.1,(mem_rowVertices w _ _ _).mpr ⟨rfl,hPos⟩⟩

include hy in
theorem row_fibre_sum (v : BranchVertex w.frame.data) (row : StablePath w.frame.data)
    (hPos : 0 < incidenceCount w.frame.data v.1 row) :
    (∑ u ∈ rowVertices w (vertexMap w v.1) row, incidenceCount w.frame.data u row) + 2 =
      incidenceCount w.frame.data v.1 row + 2 * (rowVertices w (vertexMap w v.1) row).card := by
  classical
  have hMem : v.1 ∈ rowVertices w (vertexMap w v.1) row :=
    (mem_rowVertices w _ _ _).mpr ⟨rfl,hPos⟩
  have hSum : ∑ u ∈ (rowVertices w (vertexMap w v.1) row).erase v.1,
      incidenceCount w.frame.data u row = 2 * ((rowVertices w (vertexMap w v.1) row).erase v.1).card := by
    calc
      _ = ∑ _u ∈ (rowVertices w (vertexMap w v.1) row).erase v.1, 2 := by
        apply Finset.sum_congr rfl
        intro u hu
        exact incidenceCount_rowVertices_ne_branch w hy v row u
          (Finset.mem_erase.mp hu).2 (Finset.mem_erase.mp hu).1
      _ = _ := by simp [Nat.mul_comm]
  have hTotal := Finset.sum_erase_add (s := rowVertices w (vertexMap w v.1) row)
    (fun u ↦ incidenceCount w.frame.data u row) hMem
  have hCard := Finset.card_erase_add_one hMem
  omega

include hy in
/-- Each branch incidence survives to the boundary of its actual tree fibre;
two incidences belonging to the same row are counted separately. -/
theorem incidenceCount_le_rowBoundary (v : BranchVertex w.frame.data)
    (row : StablePath w.frame.data) :
    incidenceCount w.frame.data v.1 row ≤ (rowBoundaryEdges w (vertexMap w v.1) row).card := by
  by_cases hPos : 0 < incidenceCount w.frame.data v.1 row
  · have hForest := rowInternalEdges_forest_bound w hy v row hPos
    have hSum := row_fibre_sum w hy v row hPos
    have hHandshake := row_fibre_handshake w (vertexMap w v.1) row
    omega
  · omega

noncomputable def survivingEmbedding : NonDanglingEdge w.limit ↪ NonDanglingEdge w.frame.data where
  toFun edge := ⟨edgeEmbedding w edge.1,
    fun h ↦ edge.2 ((edgeEmbedding_dangling w hy edge.1).mp h)⟩
  inj' := fun _ _ h ↦ Subtype.ext ((edgeEmbedding w).injective
    (congrArg (fun edge : NonDanglingEdge w.frame.data ↦ edge.1) h))

theorem survivingEmbedding_row (edge : NonDanglingEdge w.limit) :
    (survivingEmbedding w hy edge).stablePath = rowEquiv w hy edge.stablePath := rfl

theorem edgeEmbedding_sourceEnds (edge : w.limit.SourceEdge) :
    (vertexMap w (w.frame.data.sourceEnds (edgeEmbedding w edge)).1,
      vertexMap w (w.frame.data.sourceEnds (edgeEmbedding w edge)).2) = w.limit.sourceEnds edge := by
  let preimage := (sourceEdgeEquiv w.frame.data rfl
    (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)).symm edge
  have hMap : sourceEdgeMap w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) preimage = edge :=
    (sourceEdgeEquiv w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column)).apply_symm_apply edge
  have h := sourceEnds_sourceEdgeMap w.frame.data rfl
    (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) preimage
  rw [hMap] at h
  exact h.symm

theorem survivingEmbedding_incident (v : w.limit.SourceVertex) (edge : NonDanglingEdge w.limit) :
    (vertexMap w (w.frame.data.sourceEnds (survivingEmbedding w hy edge).1).1 = v ∨
      vertexMap w (w.frame.data.sourceEnds (survivingEmbedding w hy edge).1).2 = v) ↔
      Incident w.limit edge.1 v := by
  have h := edgeEmbedding_sourceEnds w edge.1
  exact or_congr (congrArg (fun ends ↦ ends.1 = v) h ▸ Iff.rfl)
    (congrArg (fun ends ↦ ends.2 = v) h ▸ Iff.rfl)

theorem rowBoundaryEdges_card (v : w.limit.SourceVertex) (row : StablePath w.limit) :
    (rowBoundaryEdges w v (rowEquiv w hy row)).card = incidenceCount w.limit v row := by
  classical
  unfold incidenceCount
  symm
  apply Finset.card_bij (fun edge _ ↦ survivingEmbedding w hy edge)
  · intro edge hEdge
    obtain ⟨hInc,hRow⟩ := Finset.mem_filter.mp hEdge
    apply Finset.mem_filter.mpr
    refine ⟨(mem_classEdges _ _ _).mpr ?_,?_,?_⟩
    · rw [survivingEmbedding_row, hRow]
    · exact sourceEdgeEmbedding_ne_contracted _ _ _ _ edge.1
    · exact (survivingEmbedding_incident w hy v edge).mpr ((mem_incidentEdges _ _ _).mp hInc)
  · intro e _ f _ h
    exact (survivingEmbedding w hy).injective h
  · intro edge hEdge
    obtain ⟨hRow,hTarget,hInc⟩ := Finset.mem_filter.mp hEdge
    obtain ⟨pre,hPre⟩ := exists_sourceEdgeEmbedding_eq w.frame.data rfl
      (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) hTarget
    have hEmbedding : edgeEmbedding w pre = edge.1 := hPre
    have hSurvive : ¬ IsDangling w.limit pre := by
      intro h
      apply edge.2
      rw [← hEmbedding]
      exact (edgeEmbedding_dangling w hy pre).mpr h
    let lift : NonDanglingEdge w.limit := ⟨pre,hSurvive⟩
    have hLift : survivingEmbedding w hy lift = edge := Subtype.ext hEmbedding
    refine ⟨lift,Finset.mem_filter.mpr ⟨?_,?_⟩,hLift⟩
    · apply (mem_incidentEdges _ _ _).mpr
      apply (survivingEmbedding_incident w hy v lift).mp
      rw [hLift]
      exact hInc
    · apply (rowEquiv w hy).injective
      rw [← survivingEmbedding_row, hLift]
      exact (mem_classEdges _ _ _).mp hRow

include hy in
theorem incidenceCount_le (v : BranchVertex w.frame.data) (row : StablePath w.limit) :
    incidenceCount w.frame.data v.1 (rowEquiv w hy row) ≤
      incidenceCount w.limit (branchEquiv w hy v).1 row := by
  exact (incidenceCount_le_rowBoundary w hy v (rowEquiv w hy row)).trans_eq
    (rowBoundaryEdges_card w hy _ row)

/-- Exact stable incidence transport, including the two ends of a stable loop. -/
theorem incidenceCount_eq (v : BranchVertex w.frame.data) (row : StablePath w.limit) :
    incidenceCount w.frame.data v.1 (rowEquiv w hy row) =
      incidenceCount w.limit (branchEquiv w hy v).1 row := by
  classical
  have hOld : (∑ r : StablePath w.limit, incidenceCount w.frame.data v.1 (rowEquiv w hy r)) = 3 := by
    rw [Equiv.sum_comp (rowEquiv w hy), sum_incidenceCount_vertex]
    exact le_antisymm (w.frame.fullDim.trivalent v.1) v.2
  have hNew : (∑ r : StablePath w.limit, incidenceCount w.limit (branchEquiv w hy v).1 r) = 3 := by
    rw [sum_incidenceCount_vertex]
    exact le_antisymm (limit_trivalent w hy _) (branchEquiv w hy v).2
  have hErase := Finset.sum_le_sum (s := (Finset.univ : Finset (StablePath w.limit)).erase row)
    (fun r _ ↦ incidenceCount_le w hy v r)
  have hOldErase := Finset.sum_erase_add (s := (Finset.univ : Finset (StablePath w.limit)))
    (fun r ↦ incidenceCount w.frame.data v.1 (rowEquiv w hy r)) (Finset.mem_univ row)
  have hNewErase := Finset.sum_erase_add (s := (Finset.univ : Finset (StablePath w.limit)))
    (fun r ↦ incidenceCount w.limit (branchEquiv w hy v).1 r) (Finset.mem_univ row)
  have hLe := incidenceCount_le w hy v row
  omega

/-- The actual contraction supplies the entire stable-source incidence dictionary. -/
noncomputable def stableEquivalence : StableGraphIncidence.Equivalence w.frame.data w.limit where
  vertex := branchEquiv w hy
  row := (rowEquiv w hy).symm
  incidence v row := by
    simpa only [Equiv.apply_symm_apply] using incidenceCount_eq w hy v ((rowEquiv w hy).symm row)

/-- Both vertex and row labels are inherited from actual incoming constituents;
their incidence compatibility is proved above, not an input receipt. -/
noncomputable def coreIdentification : CoreIdentification core w.limit where
  vertex := branchLabel w hy
  row := rowLabel w hy
  incidence branch slot := by
    have h := incidenceCount_eq w hy ((branchEquiv w hy).symm branch) ((rowLabel w hy).symm slot)
    have hOld := w.frame.ident.incidence ((branchEquiv w hy).symm branch) slot
    have hRow : rowEquiv w hy ((rowLabel w hy).symm slot) = w.frame.ident.row.symm slot :=
      (rowEquiv w hy).apply_symm_apply (w.frame.ident.row.symm slot)
    rw [hRow, Equiv.apply_symm_apply] at h
    exact h.symm.trans hOld

theorem coreIdentification_vertex : (coreIdentification w hy).vertex = branchLabel w hy := rfl
theorem coreIdentification_row : (coreIdentification w hy).row = rowLabel w hy := rfl

end DraismaVargas.Count.InheritedLimitIncidence

