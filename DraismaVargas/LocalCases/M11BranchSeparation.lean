module

public import DraismaVargas.LocalCases.M11RemotePruning
public import DraismaVargas.LocalCases.PrunedFibreTree

@[expose] public section

/-!
# The M11 remote swap moves only the double target direction

On a connected genus-zero target, the two incident occurrences at the wall
lead into different components after deleting the wall. This is the global
tree input required to distinguish the two split pairings of Figure 32 of
Draisma--Vargas Part I (Case `{w2-r2-nd3-M-11}`). Local
partition equalities alone do not imply this separation on a cyclic target.
-/

namespace DraismaVargas.LocalCases.M11BranchSeparation

open DraismaVargas.Infrastructure Utilities TargetBranchRegion
open W4Assembly W4StableSource W2R1Target SecondEquation
open M11RemoteCandidates M11RemotePruning

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

/-- A multiplicity-one unoriented edge has only one actual occurrence. -/
theorem target_occurrence_unique {first second : target.V}
    (hOne : num_edges target first second = 1) (edge other : target.edges)
    (hEdge : (edge : target.V × target.V) = (first, second) ∨
      (edge : target.V × target.V) = (second, first))
    (hOther : (other : target.V × target.V) = (first, second) ∨
      (other : target.V × target.V) = (second, first)) : edge = other := by
  classical
  let predicate := fun pair : target.V × target.V ↦ pair = (first, second) ∨ pair = (second, first)
  have hCount : (Finset.univ.filter (fun occurrence : target.edges ↦
      predicate (occurrence : target.V × target.V))).card = 1 := by
    calc
      _ = (((Finset.univ : Finset target.edges).val.map
          (fun occurrence : target.edges ↦ (occurrence : target.V × target.V))).filter predicate).card := by
        rw [Multiset.filter_map, Multiset.card_map]
        rfl
      _ = (target.edges.filter predicate).card := by rw [Multiset.map_univ_coe]
      _ = 1 := hOne
  obtain ⟨unique, hUnique⟩ := Finset.card_eq_one.mp hCount
  have hMem (item : target.edges) (hItem : predicate (item : target.V × target.V)) : item = unique := by
    have h : item ∈ Finset.univ.filter (fun occurrence : target.edges ↦
        predicate (occurrence : target.V × target.V)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ item, hItem⟩
    rw [hUnique, Finset.mem_singleton] at h
    exact h
  exact (hMem edge hEdge).trans (hMem other hOther).symm

theorem branchRoot_injective (hConnected : graph_connected target) (hGenus : genus target = 0)
    (star : TwoStar target wall) : Function.Injective (branchRoot star) := by
  intro first second hEqual
  apply star.edge_injective
  have hOne : num_edges target wall (branchRoot star first) = 1 := by
    have h := IteratedContraction.num_edges_eq_one_of_genus_zero_of_connected target hConnected hGenus (star.edge first)
    rcases branchRoot_ends star first with hEnds | hEnds
    · simpa only [hEnds] using h
    · simpa only [hEnds, num_edges_symmetric target (branchRoot star first) wall] using h
  apply target_occurrence_unique hOne (star.edge first) (star.edge second) (branchRoot_ends star first)
  exact hEqual ▸ branchRoot_ends star second

/-- Two different neighbors of a vertex of a tree cannot be connected after
that vertex is deleted. This reuses Mathlib's characterization of tree edges as
bridges. -/
theorem not_vertexMember_of_distinct_neighbors
    (hTree : (underlyingSimpleGraph target).IsTree)
    {root other : target.V} (hRoot : root ≠ wall) (hOther : other ≠ wall)
    (hDistinct : root ≠ other)
    (hRootAdj : (underlyingSimpleGraph target).Adj root wall)
    (hOtherAdj : (underlyingSimpleGraph target).Adj other wall) :
    ¬ VertexMember wall root hRoot other := by
  rintro ⟨_, hReachable⟩
  let inclusion : deletedGraph wall →g (underlyingSimpleGraph target).deleteEdges {s(root, wall)} :=
    { toFun := Subtype.val
      map_rel' := by
        intro first second hAdj
        apply SimpleGraph.deleteEdges_adj.mpr
        refine ⟨hAdj, ?_⟩
        simp only [Set.mem_singleton_iff, Sym2.eq_iff]
        exact fun h ↦ h.elim (fun hPair ↦ second.2 hPair.2) (fun hPair ↦ first.2 hPair.1) }
  have hOtherUp : ((underlyingSimpleGraph target).deleteEdges {s(root, wall)}).Adj other wall := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨hOtherAdj, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    exact fun h ↦ h.elim (fun hPair ↦ hDistinct hPair.1.symm) (fun hPair ↦ hOther hPair.1)
  have hBridge := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hTree.isAcyclic) hRootAdj
  exact (SimpleGraph.isBridge_iff.mp hBridge) ((hReachable.map inclusion).trans hOtherUp.reachable)

theorem branchRoot_adj (star : TwoStar target wall) (label : Fin 2) :
    (underlyingSimpleGraph target).Adj (branchRoot star label) wall := by
  have h := edge_underlying_adj (star.edge label)
  rcases branchRoot_ends star label with hEnds | hEnds
  · rw [hEnds] at h
    exact h.symm
  · rw [hEnds] at h
    exact h

theorem vertexMoved_branchRoot (star : TwoStar target wall) (label : Fin 2) :
    vertexMoved wall (branchRoot star label) (branchRoot_ne star label) (branchRoot star label) = true :=
  (vertexMoved_eq_true_iff _ _ _ _).mpr ⟨branchRoot_ne star label, SimpleGraph.Reachable.refl _⟩

theorem vertexMoved_other_branchRoot (hConnected : graph_connected target) (hGenus : genus target = 0)
    (star : TwoStar target wall) (first second : Fin 2) (hLabels : first ≠ second) :
    vertexMoved wall (branchRoot star first) (branchRoot_ne star first) (branchRoot star second) = false := by
  have hCount : target.edges.card + 1 = Fintype.card target.V := by
    unfold genus at hGenus
    omega
  have hTree := (InducedFibreTreeCount.underlying_tree_and_num_edges_le_one target hConnected hCount).1
  have hNot := not_vertexMember_of_distinct_neighbors hTree (branchRoot_ne star first)
    (branchRoot_ne star second) ((branchRoot_injective hConnected hGenus star).ne hLabels)
    (branchRoot_adj star first) (branchRoot_adj star second)
  cases hMoved : vertexMoved wall (branchRoot star first) (branchRoot_ne star first) (branchRoot star second)
  · rfl
  · exact (hNot ((vertexMoved_eq_true_iff _ _ _ _).mp hMoved)).elim

theorem edgeMoved_branch (star : TwoStar target wall) (label : Fin 2) :
    edgeMoved wall (branchRoot star label) (branchRoot_ne star label) (star.edge label) = true := by
  unfold edgeMoved
  rcases branchRoot_ends star label with hEnds | hEnds <;>
    rw [hEnds] <;> simp only [vertexMoved_wall, vertexMoved_branchRoot, Bool.false_or, Bool.or_false]

theorem edgeMoved_other_branch (hConnected : graph_connected target) (hGenus : genus target = 0)
    (star : TwoStar target wall) (first second : Fin 2) (hLabels : first ≠ second) :
    edgeMoved wall (branchRoot star first) (branchRoot_ne star first) (star.edge second) = false := by
  unfold edgeMoved
  rcases branchRoot_ends star second with hEnds | hEnds <;>
    rw [hEnds] <;> simp only [vertexMoved_wall,
      vertexMoved_other_branchRoot hConnected hGenus star first second hLabels, Bool.false_or]

theorem branchRelabeling_edge_double {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    (branchRelabeling profile hCard).edgePermutation (star.edge profile.doubleLabel) =
      Equiv.swap block.1 (otherSheet block hCard) := by
  change GluingDatum.SheetRelabeling.togglePermutation
    (edgeMoved wall (branchRoot star profile.doubleLabel) (branchRoot_ne star profile.doubleLabel)
      (star.edge profile.doubleLabel)) _ = _
  rw [edgeMoved_branch]
  rfl

theorem branchRelabeling_edge_single (hConnected : graph_connected target) (hGenus : genus target = 0)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    (branchRelabeling profile hCard).edgePermutation (star.edge profile.singleLabel) = Equiv.refl _ := by
  change GluingDatum.SheetRelabeling.togglePermutation
    (edgeMoved wall (branchRoot star profile.doubleLabel) (branchRoot_ne star profile.doubleLabel)
      (star.edge profile.singleLabel)) _ = _
  rw [edgeMoved_other_branch hConnected hGenus star _ _ profile.labels_ne]
  rfl

/-- The single direction is outside the moved tree branch, so the actual
transported deleted occurrence retains its original sheet. -/
theorem swappedDeleted_sheet (hConnected : graph_connected target) (hGenus : genus target = 0)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    (swappedDeleted profile hCard).1.2 = profile.deleted.edge.1.1.2 := by
  change (branchRelabeling profile hCard).edgePermutation profile.deleted.edge.1.1.1
    profile.deleted.edge.1.1.2 = _
  rw [M11SplitSurvival.deleted_target_eq_single profile hCard,
    branchRelabeling_edge_single hConnected hGenus]
  rfl

/-- Exact canonical occurrence formula on the moved double direction. -/
theorem map_double_sourceEdge {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) (sheet : Fin degree) :
    (branchRelabeling profile hCard).sourceEdgeEquiv (data.sourceEdge (star.edge profile.doubleLabel) sheet) =
      (swappedDatum profile hCard).sourceEdge (star.edge profile.doubleLabel)
        ((Equiv.swap block.1 (otherSheet block hCard)) sheet) := by
  have h := SheetRelabelPruning.sourceEdgeEquiv_sourceEdge (branchRelabeling profile hCard)
    (star.edge profile.doubleLabel) sheet
  rw [branchRelabeling_edge_double] at h
  exact h

/-- The opposite original sheet, measured from the deleted occurrence rather
than the profile's arbitrary enumeration of the two double survivors. -/
noncomputable def oppositeSheet {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) : Fin degree :=
  (Equiv.swap block.1 (otherSheet block hCard)) profile.deleted.edge.1.1.2

theorem oppositeSheet_ne {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    oppositeSheet profile hCard ≠ profile.deleted.edge.1.1.2 := by
  classical
  have hOther := otherSheet_spec block hCard
  have hPair : ({block.1, otherSheet block hCard} : Finset (Fin degree)) =
      (data.vertexPartition wall).block block.1 := by
    apply Finset.eq_of_subset_of_card_le
    · intro sheet hSheet
      rcases Finset.mem_insert.mp hSheet with rfl | hSheet
      · exact ((data.vertexPartition wall).mem_block_iff _ _).mpr rfl
      · rw [Finset.mem_singleton] at hSheet
        exact hSheet ▸ ((data.vertexPartition wall).mem_block_iff _ _).mpr hOther.1
    · rw [Finset.card_pair hOther.2]
      exact le_of_eq hCard
  have hMem := ((data.vertexPartition wall).mem_block_iff _ _).mpr
    (M11SplitSurvival.sheet_rel_of_incident_block profile.deleted.edge)
  rw [← hPair, Finset.mem_insert, Finset.mem_singleton] at hMem
  unfold oppositeSheet
  rcases hMem with hMem | hMem
  · rw [hMem, Equiv.swap_apply_left]
    exact hOther.2.symm
  · rw [hMem, Equiv.swap_apply_right]
    exact hOther.2

theorem oppositeSheet_rel {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    (data.vertexPartition wall).Rel block.1 (oppositeSheet profile hCard) :=
  (M11SplitSurvival.sheet_rel_of_incident_block profile.deleted.edge).trans
    ((data.vertexPartition wall).swap_apply_rel_self_of_rel (otherSheet_spec block hCard).1 _).symm

/-- Figure 32's original `e2` occurrence, with its survival proved from the
original profile rather than inferred from a displayed row label. -/
noncomputable def oppositeDouble {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) : NonDanglingEdge data :=
  ⟨data.sourceEdge (star.edge profile.doubleLabel) (oppositeSheet profile hCard),
    M11SplitSurvival.double_sourceEdge_survives profile hCard _ (oppositeSheet_rel profile hCard)⟩

/-- Selected double-direction blocks are literal singleton occurrences. -/
theorem double_sourceEdge_sheet {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (sheet : Fin degree) (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    (data.sourceEdge (star.edge profile.doubleLabel) sheet).1.2 = sheet := by
  let partition := data.edgePartition (star.edge profile.doubleLabel)
  have hSingleton : partition.block sheet = {sheet} :=
    SheetPartition.block_eq_singleton_of_refines
      (M11SourceCandidates.exterior_refines_splitBlock profile hCard _
        (star.edge_mem_incidentEdges profile.doubleLabel)) sheet
      ((data.vertexPartition wall).splitBlock_block_of_rel block.1 sheet hRel)
  have hMem := (partition.mem_block_iff sheet (partition.repr sheet)).mpr (partition.rel_repr_right sheet)
  rw [hSingleton, Finset.mem_singleton] at hMem
  exact hMem

/-- The original `e2` is genuinely a different occurrence from `e1`.
This does not assert that their stable-path classes are different. -/
theorem oppositeDouble_ne_sameSheet {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    (oppositeDouble profile hCard).1 ≠
      data.sourceEdge (star.edge profile.doubleLabel) profile.deleted.edge.1.1.2 := by
  intro hEqual
  have hSheets := congrArg (fun edge : data.SourceEdge ↦ edge.1.2) hEqual
  apply oppositeSheet_ne profile hCard
  exact (double_sourceEdge_sheet profile hCard _ (oppositeSheet_rel profile hCard)).symm.trans
    (hSheets.trans (double_sourceEdge_sheet profile hCard _
      (M11SplitSurvival.sheet_rel_of_incident_block profile.deleted.edge)))

/-- The retained double occurrence on the swapped deleted sheet is the
actual image of the original opposite-sheet occurrence (`e2` in Figure 32). -/
theorem swapped_retainedDouble_eq (hConnected : graph_connected target) (hGenus : genus target = 0)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    (swappedDatum profile hCard).sourceEdge (star.edge profile.doubleLabel) (swappedDeleted profile hCard).1.2 =
      (branchRelabeling profile hCard).sourceEdgeEquiv
        (data.sourceEdge (star.edge profile.doubleLabel) (oppositeSheet profile hCard)) := by
  rw [map_double_sourceEdge, oppositeSheet, Equiv.swap_apply_self,
    swappedDeleted_sheet hConnected hGenus]

end DraismaVargas.LocalCases.M11BranchSeparation
