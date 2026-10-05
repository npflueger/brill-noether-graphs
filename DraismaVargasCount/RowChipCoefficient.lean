module

public import DraismaVargasCount.PendantRetraction
public import DraismaVargas.Infrastructure.TargetSeparation

@[expose] public section

/-!
# Interior-row coefficients of the actual pendant-contraction fibre

For the canonical actual source retraction constructed in `PendantRetraction`,
this proves the local lemma on chips inside a stable row, used in the descent
of the pencil to an odd subdivision (step 5 of `DraismaVargasCount.Assembly`).
At an interior-row vertex of local degree `m` and local ramification `r`, the
coefficient `c` of the retracted fibre satisfies
(a) `r = 0 ⇒ c ∈ {0, m}`;
(b) `r = 1 ⇒ c ∈ {0, 1, m}`, where `m = k + 1` and the two surviving
    occurrences carry the consecutive indices `k` and `k + 1`;
(c) `r = 2 ⇒ c = 0` when the fibre is rooted at an internal target vertex.

Target-tree separation selects the unique direction toward a distinct root.
Exact branch aggregation and directional harmonicity then identify its
coefficient with the actual number of dangling occurrences in that direction.
The ramification identity produces the arithmetic alternatives, including
consecutive transition indices; leaf-fibre rigidity gives zero in the
ramification-two case.

No chip-coefficient law, branch bijection, prescribed source-edge enumeration,
or arithmetic profile is assumed. No theorem here identifies this canonical
contraction divisor with the divisor carried through a chosen metric
realization and pendant-deletion chain.
-/

namespace DraismaVargas.Count.RowChipCoefficient

open DraismaVargas.Infrastructure GluingDatum
open DraismaVargas.LocalCases
open W4StableSource StableLocalProperties FullDimensionalSource
open DanglingSideStructure DanglingDescent
open PendantRetraction PendantFibre TargetSeparation

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- An avoiding target walk lies in the corresponding deleted-vertex component. -/
theorem vertexMember_of_reachP {wall first last : target.V} (hFirst : first ≠ wall)
    (hReach : ReachP target (fun v ↦ v ≠ wall) first last) :
    TargetBranchRegion.VertexMember wall first hFirst last := by
  induction hReach with
  | refl => exact ⟨hFirst, SimpleGraph.Reachable.refl _⟩
  | tail _ hStep ih =>
    exact TargetBranchRegion.vertexMember_of_adj hFirst ih hStep.2
      (by rw [Utilities.underlyingSimpleGraph_adj]; exact hStep.1)

/-- In a target tree two different directions cannot reach the same root
while avoiding the starting vertex. -/
theorem direction_eq_of_reachP
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    {wall root : target.V} {first second : target.edges}
    (hFirst : first ∈ incidentEdges wall) (hSecond : second ∈ incidentEdges wall)
    (hReachFirst : ReachP target (fun v ↦ v ≠ wall) (farEndpoint wall first) root)
    (hReachSecond : ReachP target (fun v ↦ v ≠ wall) (farEndpoint wall second) root) :
    first = second := by
  have hFirstEnds := (Finset.mem_filter.mp hFirst).2
  have hSecondEnds := (Finset.mem_filter.mp hSecond).2
  obtain ⟨_, hOne⟩ := vertexMember_of_reachP (farEndpoint_ne hFirstEnds) hReachFirst
  obtain ⟨_, hTwo⟩ := vertexMember_of_reachP (farEndpoint_ne hSecondEnds) hReachSecond
  by_contra hNe
  exact not_reachable_farEndpoint hConnected hGenus hFirstEnds hSecondEnds hNe
    (hOne.trans hTwo.symm)

theorem farEndpoint_eq_of_ends {wall next : target.V} {edge : target.edges}
    (hEnds : (edge : target.V × target.V) = (wall, next) ∨
      (edge : target.V × target.V) = (next, wall)) (hNe : next ≠ wall) :
    farEndpoint wall edge = next := by
  rcases hEnds with h | h <;> simp [farEndpoint, h, hNe]

/-- Connectivity produces the unique direction toward a distinct root. -/
theorem exists_direction_to_root (hConnected : graph_connected target)
    {wall root : target.V} (hNe : root ≠ wall) :
    ∃ direction ∈ incidentEdges wall,
      ReachP target (fun v ↦ v ≠ wall) (farEndpoint wall direction) root := by
  obtain ⟨next, hAdj, hReach⟩ := exists_first_step
    (reach_of_graph_connected hConnected wall root) hNe
  obtain ⟨pair, hPair, hEnds⟩ :=
    GraphContraction.exists_mem_edges_of_num_edges_pos target wall next hAdj
  let direction : target.edges := ⟨pair, ⟨0, Multiset.count_pos.mpr hPair⟩⟩
  have hNext : next ≠ wall := by
    intro hEq
    rcases hEnds with h | h <;> rw [h, hEq] at hPair <;>
      exact target.loopless wall hPair
  have hIncident : direction ∈ incidentEdges wall := by
    simp only [incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    change pair.1 = wall ∨ pair.2 = wall
    rcases hEnds with h | h <;> simp [h]
  refine ⟨direction, hIncident, ?_⟩
  rw [farEndpoint_eq_of_ends hEnds hNext]
  exact hReach

/-- The chosen actual pendant side starts beyond its stored target direction. -/
theorem attached_inner_target {vertex : data.SourceVertex}
    (hSurvives : 0 < nonDanglingValency data vertex) (edge : AttachedEdge vertex) :
    (chosenDangling edge.2.2).inner.1.1 = farEndpoint vertex.1.1 edge.1.1.1 := by
  let item := chosenDangling edge.2.2
  have hOuter := outer_eq_of_incident hSurvives item edge.2.1
  have hEnds : (edge.1.1.1 : target.V × target.V) = (vertex.1.1, item.inner.1.1) ∨
      (edge.1.1.1 : target.V × target.V) = (item.inner.1.1, vertex.1.1) := by
    rcases item.ends with h | h
    · right
      exact (congrArg (fun ends : data.SourceVertex × data.SourceVertex ↦
        (ends.1.1.1, ends.2.1.1)) h).trans (by rw [hOuter])
    · left
      exact (congrArg (fun ends : data.SourceVertex × data.SourceVertex ↦
        (ends.1.1.1, ends.2.1.1)) h).trans (by rw [hOuter])
  have hNe : item.inner.1.1 ≠ vertex.1.1 := by
    intro hEq
    have hPair : (edge.1.1.1 : target.V × target.V) = (vertex.1.1, vertex.1.1) := by
      rcases hEnds with h | h <;> simpa [hEq] using h
    exact target.loopless vertex.1.1 (hPair ▸ Multiset.coe_mem)
  exact (farEndpoint_eq_of_ends hEnds hNe).symm

/-- The number of attached occurrences above a direction is the previously
defined actual directional dangling count. -/
theorem sum_attached_direction (vertex : data.SourceVertex) (direction : target.edges) :
    (∑ edge : AttachedEdge vertex,
      if edge.1.1.1 = direction then (1 : ℤ) else 0) =
      ((danglingDirection vertex direction).card : ℤ) := by
  classical
  have hCard : (Finset.univ.filter (fun edge : AttachedEdge vertex ↦
      edge.1.1.1 = direction)).card = (danglingDirection vertex direction).card := by
    refine Finset.card_bij (fun edge _ ↦
      (⟨edge.1, edge.2.1⟩ : IncidentSourceEdge data vertex)) ?_ ?_ ?_
    · intro edge hEdge
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hEdge).2, edge.2.2⟩
    · intro first _ second _ hEq
      exact Subtype.ext (congrArg (fun e : IncidentSourceEdge data vertex ↦ e.1) hEq)
    · intro edge hEdge
      have hMem := (Finset.mem_filter.mp hEdge).2
      refine ⟨⟨edge.1, edge.2, hMem.2⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMem.1⟩
  simpa only [Finset.sum_boole] using congrArg (fun n : ℕ ↦ (n : ℤ)) hCard

/-- If the root differs from the attachment target, its actual retracted
coefficient is the count of dangling occurrences in the unique root direction. -/
theorem retractedFibre_eq_direction_card
    (fd : FullDimensionalSourcePresentation data coordinate)
    {vertex : data.SourceVertex} (hSurvives : 0 < nonDanglingValency data vertex)
    {root : target.V} (hNe : root ≠ vertex.1.1)
    {direction : target.edges} (hDirection : direction ∈ incidentEdges vertex.1.1)
    (hReach : ReachP target (fun v ↦ v ≠ vertex.1.1)
      (farEndpoint vertex.1.1 direction) root) :
    retractedFibre root (retractVertex vertex) =
      ((danglingDirection vertex direction).card : ℤ) := by
  classical
  rw [retractedFibre_eq_branch_sum fd root hSurvives, ite_eq_right (Ne.symm hNe), zero_add]
  rw [← sum_attached_direction vertex direction]
  apply Finset.sum_congr rfl
  intro edge _
  have hTarget := IndexPattern.target_mem_of_incident edge.2.1
  have hIff : ReachP target (fun v ↦ v ≠ vertex.1.1)
      (chosenDangling edge.2.2).inner.1.1 root ↔ edge.1.1.1 = direction := by
    rw [attached_inner_target hSurvives edge]
    constructor
    · intro h
      exact direction_eq_of_reachP fd.targetConnected fd.targetGenus hTarget hDirection h hReach
    · intro h
      rw [h]
      exact hReach
  exact if_congr hIff rfl rfl

/-- Over the attachment target, the fibre has only its direct local-degree
contribution; no pendant side contains a second point over that target. -/
theorem retractedFibre_at_target
    (fd : FullDimensionalSourcePresentation data coordinate)
    {vertex : data.SourceVertex} (hSurvives : 0 < nonDanglingValency data vertex) :
    retractedFibre vertex.1.1 (retractVertex vertex) =
      ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) := by
  classical
  rw [retractedFibre_eq_branch_sum fd vertex.1.1 hSurvives, ite_eq_left rfl]
  have hZero : (∑ edge : AttachedEdge vertex,
      if ReachP target (fun v ↦ v ≠ vertex.1.1)
        (chosenDangling edge.2.2).inner.1.1 vertex.1.1 then (1 : ℤ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro edge _
    apply ite_eq_right
    rw [attached_inner_target hSurvives edge]
    intro h
    have hIncident := IndexPattern.target_mem_of_incident edge.2.1
    have hFar := farEndpoint_ne ((Finset.mem_filter.mp hIncident).2)
    obtain ⟨hNe, _⟩ := vertexMember_of_reachP hFar h
    exact hNe rfl
  rw [hZero, add_zero]

/-- Surviving valency two supplies the actual two source occurrences; no
named row-edge enumeration is an additional hypothesis. -/
theorem exists_two_survivors {vertex : data.SourceVertex}
    (hValency : nonDanglingValency data vertex = 2) :
    ∃ first second : IncidentSourceEdge data vertex,
      ¬ IsDangling data first.1 ∧ ¬ IsDangling data second.1 ∧ first.1 ≠ second.1 := by
  classical
  have hCard := card_nonDanglingIncident data vertex
  rw [hValency] at hCard
  obtain ⟨first, second, hNe, hSet⟩ := Finset.card_eq_two.mp hCard
  have hFirst : first ∈ nonDanglingIncident data vertex := by rw [hSet]; simp
  have hSecond : second ∈ nonDanglingIncident data vertex := by rw [hSet]; simp
  obtain ⟨hFirstSurvives, hFirstInc⟩ := (mem_nonDanglingIncident data vertex first).mp hFirst
  obtain ⟨hSecondSurvives, hSecondInc⟩ := (mem_nonDanglingIncident data vertex second).mp hSecond
  exact ⟨⟨first, hFirstInc⟩, ⟨second, hSecondInc⟩, hFirstSurvives, hSecondSurvives, hNe⟩

/-- Alternative (a), for the actual pendant-contraction divisor: an unramified
interior-row vertex carries either no chips or its entire local degree. -/
theorem coefficient_of_ramification_zero
    (fd : FullDimensionalSourcePresentation data coordinate)
    {vertex : data.SourceVertex} (hValency : nonDanglingValency data vertex = 2)
    (hRam : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 0)
    (root : target.V) :
    retractedFibre root (retractVertex vertex) = 0 ∨
      retractedFibre root (retractVertex vertex) =
        ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) := by
  have hSurvives : 0 < nonDanglingValency data vertex := by omega
  by_cases hRoot : root = vertex.1.1
  · right
    exact hRoot ▸ retractedFibre_at_target fd hSurvives
  obtain ⟨direction, hDirection, hReach⟩ := exists_direction_to_root fd.targetConnected hRoot
  rw [retractedFibre_eq_direction_card fd hSurvives hRoot hDirection hReach]
  obtain ⟨first, second, hFirst, hSecond, hNe⟩ := exists_two_survivors hValency
  have hCount := danglingDirection_card_of_two_survivors fd.danglingEdgeNoGlue vertex
    hValency first second hFirst hSecond hNe direction hDirection
  have hSum := IndexPattern.sourceEdgeIndex_add_sourceEdgeIndex fd hValency
    hFirst first.2 hSecond second.2 hNe
  have hFirstLe := sourceEdgeIndex_le_blockCard data vertex first
  have hSecondLe := sourceEdgeIndex_le_blockCard data vertex second
  rw [hRam] at hSum
  split_ifs at hCount <;> omega

/-- Alternative (b), with local degree `k + 1`: at a transition an interior-row
coefficient is zero, one, or the full local degree. The arithmetic is derived
from harmonicity and ramification, not assumed as a coefficient profile. -/
theorem coefficient_of_ramification_one
    (fd : FullDimensionalSourcePresentation data coordinate)
    {vertex : data.SourceVertex} (hValency : nonDanglingValency data vertex = 2)
    (hRam : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 1)
    (root : target.V) :
    retractedFibre root (retractVertex vertex) = 0 ∨
      retractedFibre root (retractVertex vertex) = 1 ∨
      retractedFibre root (retractVertex vertex) =
        ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) := by
  have hSurvives : 0 < nonDanglingValency data vertex := by omega
  by_cases hRoot : root = vertex.1.1
  · right; right
    exact hRoot ▸ retractedFibre_at_target fd hSurvives
  obtain ⟨direction, hDirection, hReach⟩ := exists_direction_to_root fd.targetConnected hRoot
  rw [retractedFibre_eq_direction_card fd hSurvives hRoot hDirection hReach]
  obtain ⟨first, second, hFirst, hSecond, hNe⟩ := exists_two_survivors hValency
  have hCount := danglingDirection_card_of_two_survivors fd.danglingEdgeNoGlue vertex
    hValency first second hFirst hSecond hNe direction hDirection
  have hSum := IndexPattern.sourceEdgeIndex_add_sourceEdgeIndex fd hValency
    hFirst first.2 hSecond second.2 hNe
  have hFirstLe := sourceEdgeIndex_le_blockCard data vertex first
  have hSecondLe := sourceEdgeIndex_le_blockCard data vertex second
  have hFirstPos := GluingDatum.sourceEdgeIndex_pos data first.1
  have hSecondPos := GluingDatum.sourceEdgeIndex_pos data second.1
  rw [hRam] at hSum
  split_ifs at hCount <;> omega

/-- The consecutive indices and local degree at a ramification-one vertex
are produced from its two actual surviving occurrences. -/
theorem transition_local_degree
    (fd : FullDimensionalSourcePresentation data coordinate)
    {vertex : data.SourceVertex} (hValency : nonDanglingValency data vertex = 2)
    (hRam : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 1) :
    ∃ k : ℕ, 0 < k ∧ (data.vertexPartition vertex.1.1).blockCard vertex.1.2 = k + 1 ∧
      ∃ first second : IncidentSourceEdge data vertex,
        ¬ IsDangling data first.1 ∧ ¬ IsDangling data second.1 ∧ first.1 ≠ second.1 ∧
        data.sourceEdgeIndex first.1 = k ∧ data.sourceEdgeIndex second.1 = k + 1 := by
  obtain ⟨first, second, hFirst, hSecond, hNe⟩ := exists_two_survivors hValency
  have hSum := IndexPattern.sourceEdgeIndex_add_sourceEdgeIndex fd hValency
    hFirst first.2 hSecond second.2 hNe
  have hFirstLe := sourceEdgeIndex_le_blockCard data vertex first
  have hSecondLe := sourceEdgeIndex_le_blockCard data vertex second
  have hFirstPos := GluingDatum.sourceEdgeIndex_pos data first.1
  have hSecondPos := GluingDatum.sourceEdgeIndex_pos data second.1
  rw [hRam] at hSum
  by_cases hLt : data.sourceEdgeIndex first.1 < data.sourceEdgeIndex second.1
  · exact ⟨data.sourceEdgeIndex first.1, hFirstPos, by omega,
      first, second, hFirst, hSecond, hNe, rfl, by omega⟩
  · exact ⟨data.sourceEdgeIndex second.1, hSecondPos, by omega,
      second, first, hSecond, hFirst, Ne.symm hNe, rfl, by omega⟩

/-- Alternative (c): a ramification-two interior-row vertex lies over a leaf and
has zero coefficient in a fibre rooted at an internal target vertex. -/
theorem coefficient_of_ramification_two
    (fd : FullDimensionalSourcePresentation data coordinate)
    {vertex : data.SourceVertex} (hValency : nonDanglingValency data vertex = 2)
    (hRam : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 2)
    {root : target.V} (hInternal : ¬ IsLeafVertex target root) :
    retractedFibre root (retractVertex vertex) = 0 := by
  classical
  obtain ⟨first, second, hFirst, hSecond, hNe⟩ := exists_two_survivors hValency
  have hTarget := IndexPattern.target_mem_of_incident first.2
  have hPositive : 0 < (incidentEdges vertex.1.1).card :=
    Finset.card_pos.mpr ⟨first.1.1.1, hTarget⟩
  have hBound := IndexPattern.localRamification_le_targetChange fd
    (⟨vertex.1.2, vertex.2⟩ : (data.vertexPartition vertex.1.1).Blocks)
  rw [hRam, IndexPattern.targetChange_eq_three_sub_valency fd] at hBound
  have hLeaf : IsLeafVertex target vertex.1.1 := by unfold IsLeafVertex; omega
  have hBlock := LeafFibre.eq_coreBlock_of_localRamification_eq_two fd hLeaf hRam
  have hVertex : vertex = LeafFibre.coreVertex fd hLeaf :=
    congrArg (blockVertex data vertex.1.1) hBlock
  have hSurvives : 0 < nonDanglingValency data vertex := by omega
  have hRoot : vertex.1.1 ≠ root := fun h ↦ hInternal (h ▸ hLeaf)
  rw [retractedFibre_eq_branch_sum fd root hSurvives, ite_eq_right hRoot, zero_add]
  apply Finset.sum_eq_zero
  intro edge _
  have hNot := LeafFibre.not_isDangling_of_incident_coreVertex fd hLeaf
    (Eq.mp (congrArg (Incident data edge.1) hVertex) edge.2.1)
  exact (hNot edge.2.2).elim

end DraismaVargas.Count.RowChipCoefficient
