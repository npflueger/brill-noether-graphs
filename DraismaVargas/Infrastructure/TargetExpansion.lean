import DraismaVargas.Infrastructure.GluingDatum

/-!
# Occurrence-safe target vertex expansion

The local Draisma--Vargas continuations replace one target vertex by two
vertices joined by a new edge. Old target edges are occurrences, not merely
endpoint pairs: parallel occurrences may be assigned to different sides of
the expansion. This file performs that construction by enumerating the old
occurrence type before mapping its endpoints.

The resulting occurrence equivalence is literal:
`Option target.edges` labels the new edge by `none` and every retained old
occurrence by `some`. Contracting the fresh vertex back to the wall recovers
the endpoint pair of every old occurrence and contracts the new edge to a
loop. The expansion adds one vertex and one edge, hence preserves genus.
-/

namespace DraismaVargas.Infrastructure

namespace TargetExpansion

variable (target : CFGraph) (wall : target.V)

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-- Vertices after splitting `wall`; `Sum.inr ()` is the fresh endpoint. -/
abbrev Vertex := target.V ⊕ Unit

/-- The retained copy of an old target vertex. -/
def oldVertex (vertex : target.V) : Vertex target := Sum.inl vertex

/-- The fresh target vertex on the other side of the new edge. -/
def freshVertex : Vertex target := Sum.inr ()

/-- Splitting a vertex always produces a nontrivial target vertex type: the
retained copy of any old vertex is distinct from the fresh vertex. -/
noncomputable instance : Nontrivial (Vertex target) where
  exists_pair_ne :=
    ⟨oldVertex target (Classical.choice inferInstance), freshVertex target,
      Sum.inl_ne_inr⟩

/-- Contract the fresh vertex back to the original wall vertex. -/
def contractVertex : Vertex target → target.V
  | Sum.inl vertex => vertex
  | Sum.inr _ => wall

@[simp] theorem contract_oldVertex (vertex : target.V) :
    contractVertex target wall (oldVertex target vertex) = vertex := rfl

@[simp] theorem contract_freshVertex :
    contractVertex target wall (freshVertex target) = wall := rfl

/-- Move an endpoint equal to `wall` precisely when its edge occurrence was
assigned to the fresh side. -/
def expandedEndpoint (right : target.edges → Bool) (edge : target.edges)
    (vertex : target.V) : Vertex target :=
  if right edge then
    if vertex = wall then freshVertex target else oldVertex target vertex
  else oldVertex target vertex

@[simp] theorem contract_expandedEndpoint (right : target.edges → Bool)
    (edge : target.edges) (vertex : target.V) :
    contractVertex target wall (expandedEndpoint target wall right edge vertex) = vertex := by
  simp only [expandedEndpoint]
  split_ifs with _ h
  · exact h.symm
  · rfl
  · rfl

/-- Away from the split wall, remapping an old endpoint preserves and
reflects equality with the retained old vertex. -/
theorem expandedEndpoint_eq_oldVertex_iff_of_ne
    (right : target.edges → Bool) (edge : target.edges)
    (endpoint vertex : target.V) (hne : vertex ≠ wall) :
    expandedEndpoint target wall right edge endpoint = oldVertex target vertex ↔
      endpoint = vertex := by
  cases hRight : right edge with
  | false => simp [expandedEndpoint, hRight, oldVertex]
  | true =>
      by_cases hEndpoint : endpoint = wall
      · subst endpoint
        have hne' : wall ≠ vertex := Ne.symm hne
        simp [expandedEndpoint, hRight, oldVertex, freshVertex, hne']
      · simp [expandedEndpoint, hRight, hEndpoint, oldVertex]

/-- Remapped endpoints of one old edge occurrence. -/
def oldEnds (right : target.edges → Bool) (edge : target.edges) :
    Vertex target × Vertex target :=
  (expandedEndpoint target wall right edge (edge : target.V × target.V).1,
    expandedEndpoint target wall right edge (edge : target.V × target.V).2)

/-- The new target edge joining the retained and fresh wall vertices. -/
def newEnds : Vertex target × Vertex target :=
  (oldVertex target wall, freshVertex target)

/-- The duplicate-free enumeration multiset of old target occurrences. -/
abbrev enumeratedEdges : Multiset target.edges :=
  (Finset.univ : Finset target.edges).val

/-- Expanded target edges: one distinguished new edge followed by one mapped
copy of every old occurrence. -/
def expandedEdges (right : target.edges → Bool) :
    Multiset (Vertex target × Vertex target) :=
  newEnds target wall ::ₘ
    (enumeratedEdges target).map (oldEnds target wall right)

private theorem oldEnds_ne (right : target.edges → Bool)
    (edge : target.edges) :
    (oldEnds target wall right edge).1 ≠ (oldEnds target wall right edge).2 := by
  intro h
  have hContract := congrArg (contractVertex target wall) h
  simp only [oldEnds, contract_expandedEndpoint] at hContract
  have hEdgeMem : (edge : target.V × target.V) ∈ target.edges :=
    Multiset.coe_mem
  have hPair : (edge : target.V × target.V) =
      ((edge : target.V × target.V).1, (edge : target.V × target.V).1) := by
    apply Prod.ext
    · rfl
    · exact hContract.symm
  rw [hPair] at hEdgeMem
  exact target.loopless (edge : target.V × target.V).1 hEdgeMem

/-- The target graph obtained by splitting `wall` according to the selected
old edge occurrences and adjoining one new edge. -/
def graph (right : target.edges → Bool) : CFGraph where
  V := Vertex target
  instNonempty := ⟨freshVertex target⟩
  edges := expandedEdges target wall right
  loopless := by
    intro vertex hmem
    simp only [expandedEdges, Multiset.mem_cons, Multiset.mem_map,
      Finset.mem_val, Finset.mem_univ, true_and] at hmem
    rcases hmem with hNew | ⟨edge, hOld⟩
    · have hDistinct : oldVertex target wall ≠ freshVertex target := by
        intro h
        cases h
      have hFirst : vertex = oldVertex target wall := congrArg Prod.fst hNew
      have hSecond : vertex = freshVertex target := congrArg Prod.snd hNew
      exact hDistinct (hFirst.symm.trans hSecond)
    · exact oldEnds_ne target wall right edge (by
        rw [hOld])

noncomputable instance (right : target.edges → Bool) :
    Nontrivial (graph target wall right).V :=
  inferInstanceAs (Nontrivial (Vertex target))

@[simp] theorem newEnds_mem_graph_edges (right : target.edges → Bool) :
    newEnds target wall ∈ (graph target wall right).edges := by
  change newEnds target wall ∈ expandedEdges target wall right
  simp only [expandedEdges]
  exact Multiset.mem_cons_self (newEnds target wall) _

theorem oldEnds_mem_graph_edges (right : target.edges → Bool)
    (edge : target.edges) :
    oldEnds target wall right edge ∈ (graph target wall right).edges := by
  change oldEnds target wall right edge ∈ expandedEdges target wall right
  apply Multiset.mem_cons_of_mem
  apply Multiset.mem_map.mpr
  exact ⟨edge, by simp, rfl⟩

private theorem num_edges_pos_of_mem (G : CFGraph) (first second : G.V)
    (hEdge : (first, second) ∈ G.edges) :
    0 < num_edges G first second := by
  unfold num_edges
  rw [Multiset.card_pos_iff_exists_mem]
  exact ⟨(first, second), Multiset.mem_filter.mpr ⟨hEdge, Or.inl rfl⟩⟩

theorem oldEnds_num_edges_pos (right : target.edges → Bool)
    (edge : target.edges) :
    0 < num_edges (graph target wall right)
      (oldEnds target wall right edge).1 (oldEnds target wall right edge).2 := by
  exact num_edges_pos_of_mem _ _ _ (oldEnds_mem_graph_edges target wall right edge)

theorem oldEnds_num_edges_pos_reverse (right : target.edges → Bool)
    (edge : target.edges) :
    0 < num_edges (graph target wall right)
      (oldEnds target wall right edge).2 (oldEnds target wall right edge).1 := by
  unfold num_edges
  rw [Multiset.card_pos_iff_exists_mem]
  refine ⟨oldEnds target wall right edge, Multiset.mem_filter.mpr ⟨?_, Or.inr rfl⟩⟩
  exact oldEnds_mem_graph_edges target wall right edge

theorem newEnds_num_edges_pos (right : target.edges → Bool) :
    0 < num_edges (graph target wall right)
      (newEnds target wall).1 (newEnds target wall).2 := by
  exact num_edges_pos_of_mem _ _ _ (newEnds_mem_graph_edges target wall right)

theorem newEnds_num_edges_pos_reverse (right : target.edges → Bool) :
    0 < num_edges (graph target wall right)
      (newEnds target wall).2 (newEnds target wall).1 := by
  unfold num_edges
  rw [Multiset.card_pos_iff_exists_mem]
  refine ⟨newEnds target wall, Multiset.mem_filter.mpr ⟨?_, Or.inr rfl⟩⟩
  exact newEnds_mem_graph_edges target wall right

/-- If the two copies of the wall lie on the same side of a cut, moving a
wall incidence to the fresh copy does not change its cut membership. -/
theorem expandedEndpoint_mem_iff (right : target.edges → Bool)
    (cut : Finset (Vertex target))
    (hWallSide : oldVertex target wall ∈ cut ↔ freshVertex target ∈ cut)
    (edge : target.edges) (vertex : target.V) :
    expandedEndpoint target wall right edge vertex ∈ cut ↔
      oldVertex target vertex ∈ cut := by
  cases hRight : right edge with
  | false => simp [expandedEndpoint, hRight]
  | true =>
      by_cases hVertex : vertex = wall
      · subst vertex
        simpa [expandedEndpoint, hRight] using hWallSide.symm
      · simp [expandedEndpoint, hRight, hVertex]

/-- Splitting one vertex and adding the resolving edge preserves target
connectedness for every occurrence-wise assignment of old incidences. -/
theorem graph_connected (right : target.edges → Bool)
    (hConnected : _root_.graph_connected target) :
    _root_.graph_connected (graph target wall right) := by
  classical
  intro cut hSplit
  by_cases hWallSide :
      oldVertex target wall ∈ cut ↔ freshVertex target ∈ cut
  · let originalCut : Finset target.V :=
      Finset.univ.filter fun vertex ↦ oldVertex target vertex ∈ cut
    obtain ⟨inside, outside, hInside, hOutside⟩ := hSplit
    have hContractMembership : ∀ vertex : Vertex target,
        oldVertex target (contractVertex target wall vertex) ∈ cut ↔
          vertex ∈ cut := by
      intro vertex
      cases vertex with
      | inl vertex => rfl
      | inr fresh =>
          cases fresh
          exact hWallSide
    have hOriginalSplit :
        ∃ first second : target.V,
          first ∈ originalCut ∧ second ∉ originalCut := by
      refine ⟨contractVertex target wall inside,
        contractVertex target wall outside, ?_, ?_⟩
      · simpa [originalCut] using (hContractMembership inside).mpr hInside
      · simpa [originalCut] using
          (not_congr (hContractMembership outside)).mpr hOutside
    obtain ⟨first, hFirst, second, hSecond, hCrossing⟩ :=
      hConnected originalCut hOriginalSplit
    have hFirstOld : oldVertex target first ∈ cut := by
      simpa [originalCut] using hFirst
    have hSecondOld : oldVertex target second ∉ cut := by
      simpa [originalCut] using hSecond
    unfold num_edges at hCrossing
    obtain ⟨pair, hPair⟩ := Multiset.card_pos_iff_exists_mem.mp hCrossing
    have hPairData := Multiset.mem_filter.mp hPair
    let edge : target.edges :=
      ⟨pair, ⟨0, Multiset.count_pos.mpr hPairData.1⟩⟩
    have hLiftFirst : expandedEndpoint target wall right edge first ∈ cut :=
      (expandedEndpoint_mem_iff target wall right cut hWallSide edge first).mpr
        hFirstOld
    have hLiftSecond : expandedEndpoint target wall right edge second ∉ cut :=
      (not_congr
        (expandedEndpoint_mem_iff target wall right cut hWallSide edge second)).mpr
          hSecondOld
    rcases hPairData.2 with hOrder | hOrder
    · have hEdgeEnds : (edge : target.V × target.V) = (first, second) := hOrder
      refine ⟨expandedEndpoint target wall right edge first, hLiftFirst,
        expandedEndpoint target wall right edge second, hLiftSecond, ?_⟩
      simpa only [oldEnds, hEdgeEnds] using
        oldEnds_num_edges_pos target wall right edge
    · have hEdgeEnds : (edge : target.V × target.V) = (second, first) := hOrder
      refine ⟨expandedEndpoint target wall right edge first, hLiftFirst,
        expandedEndpoint target wall right edge second, hLiftSecond, ?_⟩
      simpa only [oldEnds, hEdgeEnds] using
        oldEnds_num_edges_pos_reverse target wall right edge
  · by_cases hOld : oldVertex target wall ∈ cut
    · have hFresh : freshVertex target ∉ cut := by
        intro hFresh
        exact hWallSide ⟨fun _ ↦ hFresh, fun _ ↦ hOld⟩
      refine ⟨oldVertex target wall, hOld, freshVertex target, hFresh, ?_⟩
      simpa only [newEnds] using newEnds_num_edges_pos target wall right
    · have hFresh : freshVertex target ∈ cut := by
        by_contra hFresh
        exact hWallSide ⟨fun h ↦ (hOld h).elim, fun h ↦ (hFresh h).elim⟩
      refine ⟨freshVertex target, hFresh, oldVertex target wall, hOld, ?_⟩
      simpa only [newEnds] using newEnds_num_edges_pos_reverse target wall right

/-- Enumerating `Finset.univ` neither loses nor duplicates an old target edge
occurrence. -/
noncomputable def enumerationEquiv :
    Multiset.ToType (enumeratedEdges target) ≃ target.edges where
  toFun item := item.1
  invFun edge :=
    ⟨edge, ⟨0, by
      rw [Multiset.count_eq_one_of_mem Finset.univ.nodup (by simp)]
      omega⟩⟩
  left_inv := by
    rintro ⟨edge, index⟩
    have hCount :
        Multiset.count edge (enumeratedEdges target) = 1 :=
      Multiset.count_eq_one_of_mem Finset.univ.nodup (by simp)
    have hSubsingleton : Subsingleton
        (Fin (Multiset.count edge (enumeratedEdges target))) := by
      rw [hCount]
      infer_instance
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      exact hSubsingleton.elim _ _
  right_inv := by
    intro edge
    rfl

/-- Occurrences of the mapped old-edge multiset remain equivalent to the
original old target occurrences. -/
noncomputable def oldOccurrenceEquiv (right : target.edges → Bool) :
    target.edges ≃ Multiset.ToType
      ((enumeratedEdges target).map (oldEnds target wall right)) :=
  (enumerationEquiv target).symm.trans
    (Multiset.mapEquiv (enumeratedEdges target) (oldEnds target wall right))

/-- Label every expanded occurrence by either the new edge (`none`) or its
unique old occurrence (`some edge`). -/
noncomputable def occurrenceEquiv (right : target.edges → Bool) :
    Option target.edges ≃ (graph target wall right).edges :=
  (oldOccurrenceEquiv target wall right).optionCongr.trans
    Multiset.consEquiv.symm

@[simp] theorem occurrenceEquiv_none (right : target.edges → Bool) :
    (occurrenceEquiv target wall right none).1 = newEnds target wall := by
  rfl

@[simp] theorem occurrenceEquiv_some (right : target.edges → Bool)
    (edge : target.edges) :
    (occurrenceEquiv target wall right (some edge)).1 =
      oldEnds target wall right edge := by
  change (((Multiset.consEquiv).symm
      (some (oldOccurrenceEquiv target wall right edge))).1) = _
  simp only [Multiset.consEquiv_symm_some]
  unfold oldOccurrenceEquiv
  change ((Multiset.mapEquiv (enumeratedEdges target)
      (oldEnds target wall right) ((enumerationEquiv target).symm edge)).1) = _
  rw [Multiset.mapEquiv_apply]
  exact congrArg (oldEnds target wall right)
    ((enumerationEquiv target).apply_symm_apply edge)

/-- Old wall-edge occurrences assigned to one side of the split. `false` is
the retained wall vertex and `true` is the fresh vertex. -/
noncomputable def wallEdgesAssigned (right : target.edges → Bool)
    (side : Bool) : Finset target.edges :=
  (Finset.univ : Finset target.edges).filter fun edge ↦
    ((edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) ∧ right edge = side

@[simp] theorem mem_wallEdgesAssigned (right : target.edges → Bool)
    (side : Bool) (edge : target.edges) :
    edge ∈ wallEdgesAssigned target wall right side ↔
      (((edge : target.V × target.V).1 = wall ∨
        (edge : target.V × target.V).2 = wall) ∧ right edge = side) := by
  simp [wallEdgesAssigned]

/-- An old occurrence is incident to the retained wall copy exactly when it
was incident to the original wall and was assigned to the retained side. -/
theorem oldEnds_incident_oldVertex_iff (right : target.edges → Bool)
    (edge : target.edges) :
    ((oldEnds target wall right edge).1 = oldVertex target wall ∨
      (oldEnds target wall right edge).2 = oldVertex target wall) ↔
      (((edge : target.V × target.V).1 = wall ∨
        (edge : target.V × target.V).2 = wall) ∧ right edge = false) := by
  cases hRight : right edge
  · simp [oldEnds, expandedEndpoint, hRight, oldVertex]
  · by_cases hFirst : (edge : target.V × target.V).1 = wall <;>
      by_cases hSecond : (edge : target.V × target.V).2 = wall <;>
      simp [oldEnds, expandedEndpoint, hRight, hFirst, hSecond, oldVertex,
        freshVertex]

/-- An old occurrence is incident to the fresh wall copy exactly when it was
incident to the original wall and was assigned to the fresh side. -/
theorem oldEnds_incident_freshVertex_iff (right : target.edges → Bool)
    (edge : target.edges) :
    ((oldEnds target wall right edge).1 = freshVertex target ∨
      (oldEnds target wall right edge).2 = freshVertex target) ↔
      (((edge : target.V × target.V).1 = wall ∨
        (edge : target.V × target.V).2 = wall) ∧ right edge = true) := by
  cases hRight : right edge
  · simp [oldEnds, expandedEndpoint, hRight, oldVertex, freshVertex]
  · by_cases hFirst : (edge : target.V × target.V).1 = wall <;>
      by_cases hSecond : (edge : target.V × target.V).2 = wall <;>
      simp [oldEnds, expandedEndpoint, hRight, hFirst, hSecond, oldVertex,
        freshVertex]

/-- Canonical occurrence list at one side of a target split: the new edge
comes first, followed by the old wall occurrences assigned to that side. -/
noncomputable def incidentList (right : target.edges → Bool) (side : Bool) :
    List (graph target wall right).edges :=
  occurrenceEquiv target wall right none ::
    (wallEdgesAssigned target wall right side).toList.map fun edge ↦
      occurrenceEquiv target wall right (some edge)

/-- The canonical retained-wall incidence list. -/
noncomputable abbrev leftIncidentList (right : target.edges → Bool) :=
  incidentList target wall right false

/-- The canonical fresh-wall incidence list. -/
noncomputable abbrev rightIncidentList (right : target.edges → Bool) :=
  incidentList target wall right true

theorem incidentList_nodup (right : target.edges → Bool) (side : Bool) :
    (incidentList target wall right side).Nodup := by
  rw [incidentList, List.nodup_cons]
  constructor
  · simp
  · apply List.Nodup.map
    · intro first second hEqual
      exact Option.some.inj ((occurrenceEquiv target wall right).injective hEqual)
    · exact (wallEdgesAssigned target wall right side).nodup_toList

/-- The retained-wall list enumerates exactly its incident expanded edge
occurrences, without repetition. -/
theorem leftIncidentList_multiset (right : target.edges → Bool) :
    (leftIncidentList target wall right :
      Multiset (graph target wall right).edges) =
      (GluingDatum.incidentEdges (oldVertex target wall) :
        Finset (graph target wall right).edges).val := by
  apply (Multiset.Nodup.ext
    (Multiset.coe_nodup.mpr (incidentList_nodup target wall right false))
    (GluingDatum.incidentEdges (oldVertex target wall)).nodup).mpr
  intro expandedEdge
  obtain ⟨label, rfl⟩ :=
    (occurrenceEquiv target wall right).surjective expandedEdge
  cases label with
  | none =>
      apply iff_of_true
      · simp [incidentList]
      · simp only [Finset.mem_val, GluingDatum.incidentEdges,
          Finset.mem_filter, Finset.mem_univ, true_and]
        rw [occurrenceEquiv_none]
        exact Or.inl rfl
  | some edge =>
      have hList :
          occurrenceEquiv target wall right (some edge) ∈
              (leftIncidentList target wall right :
                Multiset (graph target wall right).edges) ↔
            edge ∈ wallEdgesAssigned target wall right false := by
        simp [incidentList]
      have hIncident :
          occurrenceEquiv target wall right (some edge) ∈
              (GluingDatum.incidentEdges (oldVertex target wall) :
                Finset (graph target wall right).edges).val ↔
            (((edge : target.V × target.V).1 = wall ∨
              (edge : target.V × target.V).2 = wall) ∧ right edge = false) := by
        simp only [Finset.mem_val, GluingDatum.incidentEdges,
          Finset.mem_filter, Finset.mem_univ, true_and]
        rw [occurrenceEquiv_some]
        exact oldEnds_incident_oldVertex_iff target wall right edge
      exact hList.trans ((mem_wallEdgesAssigned target wall right false edge).trans
        hIncident.symm)

/-- The fresh-wall list enumerates exactly its incident expanded edge
occurrences, without repetition. -/
theorem rightIncidentList_multiset (right : target.edges → Bool) :
    (rightIncidentList target wall right :
      Multiset (graph target wall right).edges) =
      (GluingDatum.incidentEdges (freshVertex target) :
        Finset (graph target wall right).edges).val := by
  apply (Multiset.Nodup.ext
    (Multiset.coe_nodup.mpr (incidentList_nodup target wall right true))
    (GluingDatum.incidentEdges (freshVertex target)).nodup).mpr
  intro expandedEdge
  obtain ⟨label, rfl⟩ :=
    (occurrenceEquiv target wall right).surjective expandedEdge
  cases label with
  | none =>
      apply iff_of_true
      · simp [incidentList]
      · simp only [Finset.mem_val, GluingDatum.incidentEdges,
          Finset.mem_filter, Finset.mem_univ, true_and]
        rw [occurrenceEquiv_none]
        exact Or.inr rfl
  | some edge =>
      have hList :
          occurrenceEquiv target wall right (some edge) ∈
              (rightIncidentList target wall right :
                Multiset (graph target wall right).edges) ↔
            edge ∈ wallEdgesAssigned target wall right true := by
        simp [incidentList]
      have hIncident :
          occurrenceEquiv target wall right (some edge) ∈
              (GluingDatum.incidentEdges (freshVertex target) :
                Finset (graph target wall right).edges).val ↔
            (((edge : target.V × target.V).1 = wall ∨
              (edge : target.V × target.V).2 = wall) ∧ right edge = true) := by
        simp only [Finset.mem_val, GluingDatum.incidentEdges,
          Finset.mem_filter, Finset.mem_univ, true_and]
        rw [occurrenceEquiv_some]
        exact oldEnds_incident_freshVertex_iff target wall right edge
      exact hList.trans ((mem_wallEdgesAssigned target wall right true edge).trans
        hIncident.symm)

/-- Contracting the fresh endpoint recovers the literal endpoint pair of an
old target occurrence. -/
@[simp] theorem contract_oldEnds (right : target.edges → Bool)
    (edge : target.edges) :
    (contractVertex target wall (oldEnds target wall right edge).1,
      contractVertex target wall (oldEnds target wall right edge).2) =
        (edge : target.V × target.V) := by
  simp [oldEnds]

/-- The distinguished new edge contracts to the wall loop and is therefore
the unique occurrence deleted by the contraction. -/
@[simp] theorem contract_newEnds :
    (contractVertex target wall (newEnds target wall).1,
      contractVertex target wall (newEnds target wall).2) = (wall, wall) := rfl

@[simp] theorem graph_edge_card (right : target.edges → Bool) :
    (graph target wall right).edges.card = target.edges.card + 1 := by
  simp [graph, expandedEdges, enumeratedEdges, Multiset.card_coe]

@[simp] theorem graph_vertex_card (right : target.edges → Bool) :
    Fintype.card (graph target wall right).V = Fintype.card target.V + 1 := by
  change Fintype.card (target.V ⊕ Unit) = Fintype.card target.V + 1
  rw [Fintype.card_sum, Fintype.card_unit]

/-- The expanded target's vertices are literally the old vertices together
with its one fresh vertex. -/
def vertexEquiv (right : target.edges → Bool) :
    (target.V ⊕ Unit) ≃ (graph target wall right).V :=
  Equiv.refl _

/-- Reindex a sum over the expanded target into the old vertices and the one
fresh vertex. -/
theorem sum_vertices (right : target.edges → Bool)
    {A : Type*} [AddCommMonoid A]
    (value : (graph target wall right).V → A) :
    (∑ vertex, value vertex) =
      (∑ vertex : target.V, value (oldVertex target vertex)) +
        value (freshVertex target) := by
  rw [← Equiv.sum_comp (vertexEquiv target wall right) value]
  rw [Fintype.sum_sum_type]
  simp [vertexEquiv, oldVertex, freshVertex]
  rfl

/-- A vertex split adds one edge and one vertex, so it preserves the target
genus. -/
@[simp] theorem graph_genus (right : target.edges → Bool) :
    genus (graph target wall right) = genus target := by
  unfold genus
  rw [graph_edge_card, graph_vertex_card]
  push_cast
  ring

end TargetExpansion

end DraismaVargas.Infrastructure
