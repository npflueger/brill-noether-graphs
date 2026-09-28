import DraismaVargas.LocalCases.WallProgress

/-!
# Change-minimal leaf fibres and the monovalent-wall obstruction

The source is Draisma--Vargas, Part I (arXiv:1909.12924), Section 3
("Local properties"): the remark on change-minimal leaves
(`rem-leaves-min-change`) and Lemma `lemma-loop-12`.
The first step of loop-12 identifies the entire surviving fibre of a leaf:
two unramified occurrences meet at one divalent source vertex and therefore
belong to the same stable path.  All objects below retain edge occurrences.

At an adjacent divalent target vertex, the other target direction contributes
exactly one edge block inside each source block: the leaf-direction count is
the block cardinality `m`, and local ramification gives `m + q ≤ 3`, while
refinement gives `1 ≤ q ≤ m`.  Therefore `q = 1`.  This replaces the paper's
general no-return argument by the ordinary incidence count needed here.

If the two surviving leaf sheets remain separate at the divalent endpoint,
every occupied source block there has surviving valency two.  Both adjacent
target columns are then supported in the leaf's single stable row, so the
length matrix is singular.  Otherwise the leaf partition already refines the
divalent partition, and the two parallel leaf occurrences violate the local
forest Euler count.  Thus a full-dimensional incoming datum cannot have a
forest contraction between a leaf and a divalent vertex.

`card_incidentEdges_merge_eq_two_three_or_four` consequently removes the
monovalent alternative from `WallProgress.card_incidentEdges_merge_cases`,
under exactly its existing hypotheses.  It exhausts wall *valencies*, not the
source block profiles within each valency.  We prove the forest-contraction
consequence of loop-12, not its further statement identifying a stable loop
and its attached bridge.

## Neither branch is redundant

`ForestCountWitness` is a degree-three configuration that survives the forest
count: divalent partition `{0,2},{1}`, leaf partition `{0,1},{2}`, the discrete
partition above the contracted occurrence, and `{0,2},{1}` again above the
divalent vertex's other direction.  It is change-minimal at both endpoints —
the leaf's local ramifications are `2 - 2 + 2 = 2` and `1 - 2 + 1 = 0`, so
`ch = 2` against `val = 1`; the divalent vertex's are `2 + 1 - 2 = 1` and
`1 + 1 - 2 = 0`, so `ch = 1` against `val = 2` — and
`ForestCountWitness.contractionForest_count` checks that the merged partition
is the one-block partition with `3 + 1 = 2 + 2`.  Its two leaf sheets
`0` and `1` are separated at the divalent endpoint, so it is excluded only by
`det_ne_zero`.  `ContractionForest` alone therefore does not prove loop-12.
Conversely `det_ne_zero` alone does not either: once the leaf pair *is*
identified at the divalent endpoint, two surviving occurrences above the
contracted edge meet one source block, `target_injective_on_nonDanglingIncident`
fails, and the second target column is no longer confined to the leaf's row.

## Joint satisfiability

The hypotheses are read here only in the combination
`WallProgress.card_incidentEdges_merge_cases` already uses, and `W4Bridge`,
`SecondEquation` and `ThirdEquation` use the same bundle.  A
`FullDimensionalSourcePresentation` is constructed by `CaterpillarRows.fullDim`.
The results below strictly strengthen an existing conclusion under identical
hypotheses, so they add no vacuity of their own.  Nothing here adds a premise
that could conflict
with `ContractionForest`: loop-12 constrains `fd` together with an adjacent
(divalent, leaf) pair of target vertices, and the `ForestCountWitness`
partitions show that a change-minimal forest contraction at such a pair does
exist once `det_ne_zero` is dropped.
-/

namespace DraismaVargas.LocalCases.MonovalentWall

open DraismaVargas.Infrastructure
open W4StableSource StableLocalProperties FullDimensionalSource

variable {target : CFGraph} {degree : ℕ}

/-- Incidence and a source degree of one force an occurrence to dangle. -/
theorem isDangling_of_incident_card_eq_one
    (data : GluingDatum target degree) (hConnected : data.Connected)
    {vertex : data.SourceVertex} {edge : data.SourceEdge}
    (hIncident : Incident data edge vertex)
    (hOne : Fintype.card (IncidentSourceEdge data vertex) = 1) :
    IsDangling data edge := by
  have hDegree : vertex_degree data.sourceGraph vertex = 1 := by
    rw [vertex_degree_sourceGraph_eq_card_incidentSourceEdge, hOne]
    norm_num
  rcases hIncident with hLeft | hRight
  · exact isDangling_of_sourceEnds_fst_degree_eq_one data hConnected edge
      (hLeft ▸ hDegree)
  · exact isDangling_of_sourceEnds_snd_degree_eq_one data hConnected edge
      (hRight ▸ hDegree)

/-- The surviving valency cannot exceed the total number of incident
occurrences. -/
theorem nonDanglingValency_le_card_incidentSourceEdge
    (data : GluingDatum target degree) (vertex : data.SourceVertex) :
    nonDanglingValency data vertex ≤ Fintype.card (IncidentSourceEdge data vertex) := by
  classical
  rw [← card_filter_not_isDangling_eq_nonDanglingValency]
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)

/-- Above a change-minimal leaf, any surviving occurrence meets a block with
two incident occurrences, local degree two, and local ramification two. -/
theorem leaf_block_of_surviving
    (data : GluingDatum target degree) (hValid : data.Valid)
    (hNoDangling : NoDanglingTargetFibres data)
    (leaf : target.V) (hLeaf : (GluingDatum.incidentEdges leaf).card = 1)
    (hMinimal : data.ChangeMinimalAt leaf)
    (block : (data.vertexPartition leaf).Blocks)
    (edge : data.SourceEdge) (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge (blockVertex data leaf block)) :
    Fintype.card (IncidentSourceEdge data (blockVertex data leaf block)) = 2 ∧
      (data.vertexPartition leaf).blockCard block.1 = 2 ∧
      data.localRamification leaf block = 2 := by
  rcases leaf_block_dichotomy data hValid hNoDangling leaf hLeaf hMinimal block
      with ⟨hOne, _⟩ | ⟨hTwo, hCard, hRamification, _⟩
  · exact (hSurvives (isDangling_of_incident_card_eq_one data hValid.1
      hIncident hOne)).elim
  · exact ⟨hTwo, hCard, hRamification⟩

/-- All surviving occurrences over a change-minimal leaf meet the same
source block: two distinct such blocks would each consume the entire change. -/
theorem leaf_surviving_blocks_unique
    (data : GluingDatum target degree) (hValid : data.Valid)
    (leaf : target.V) (hLeaf : (GluingDatum.incidentEdges leaf).card = 1)
    (hMinimal : data.ChangeMinimalAt leaf)
    (first second : (data.vertexPartition leaf).Blocks)
    (hFirst : data.localRamification leaf first = 2)
    (hSecond : data.localRamification leaf second = 2) : first = second := by
  classical
  by_contra hNe
  have hChange : data.targetChange leaf = 2 := by
    change data.targetChange leaf + ((GluingDatum.incidentEdges leaf).card : ℤ) - 3 = 0
      at hMinimal
    rw [hLeaf] at hMinimal
    omega
  have hLe := Finset.sum_le_sum_of_subset_of_nonneg
    (s := ({first, second} : Finset (data.vertexPartition leaf).Blocks))
    (t := Finset.univ) (f := data.localRamification leaf)
    (Finset.subset_univ _) (fun block _ _ ↦
      data.localRamification_nonneg leaf (hValid.2 leaf) block)
  rw [Finset.sum_pair hNe, hFirst, hSecond] at hLe
  change (2 : ℤ) + 2 ≤ data.targetChange leaf at hLe
  omega

/-- The occurrence-safe leaf-fibre description needed by loop-12.  It is
derived from the full-dimensional bundle, with no additional local premise. -/
structure LeafFibre (data : GluingDatum target degree) (leaf : target.V)
    (targetEdge : target.edges) where
  block : (data.vertexPartition leaf).Blocks
  first : NonDanglingEdge data
  second : NonDanglingEdge data
  distinct : first ≠ second
  first_target : first.1.1.1 = targetEdge
  second_target : second.1.1.1 = targetEdge
  first_incident : Incident data first.1 (blockVertex data leaf block)
  second_incident : Incident data second.1 (blockVertex data leaf block)
  source_degree : Fintype.card (IncidentSourceEdge data (blockVertex data leaf block)) = 2
  local_degree : (data.vertexPartition leaf).blockCard block.1 = 2
  ramification : data.localRamification leaf block = 2
  valency : nonDanglingValency data (blockVertex data leaf block) = 2
  fibre : ∀ edge : NonDanglingEdge data,
    edge.1.1.1 = targetEdge ↔ edge = first ∨ edge = second
  indices : ∀ edge : data.SourceEdge, edge.1.1 = targetEdge → data.sourceEdgeIndex edge = 1

namespace LeafFibre

variable {data : GluingDatum target degree} {leaf : target.V} {targetEdge : target.edges}

/-- Both leaf occurrences belong to the same stable path. -/
theorem stablePath_eq (fibre : LeafFibre data leaf targetEdge) :
    fibre.first.stablePath = fibre.second.stablePath :=
  stablePath_eq_of_consecutive ⟨fibre.distinct,
    blockVertex data leaf fibre.block, fibre.first_incident,
    fibre.second_incident, fibre.valency⟩

/-- Every surviving occurrence above the leaf lies on that one stable path. -/
theorem stablePath_eq_of_target (fibre : LeafFibre data leaf targetEdge)
    (edge : NonDanglingEdge data) (hTarget : edge.1.1.1 = targetEdge) :
    edge.stablePath = fibre.first.stablePath := by
  rcases (fibre.fibre edge).mp hTarget with rfl | rfl
  · rfl
  · exact fibre.stablePath_eq.symm

end LeafFibre

/-- A one-sheet block fixes its representative. -/
theorem repr_eq_self_of_blockCard_eq_one (partition : SheetPartition degree)
    (sheet : Fin degree) (hOne : partition.blockCard sheet = 1) :
    partition.repr sheet = sheet := by
  have hMem : partition.repr sheet ∈ partition.block sheet :=
    (partition.mem_block_iff _ _).mpr (partition.rel_repr_right sheet)
  rw [partition.block_eq_singleton_of_blockCard_eq_one sheet hOne] at hMem
  exact Finset.mem_singleton.mp hMem

namespace LeafFibre

variable {data : GluingDatum target degree} {leaf : target.V} {targetEdge : target.edges}

/-- Every block of the target leaf's edge partition is a single sheet. -/
theorem edgePartition_repr (fibre : LeafFibre data leaf targetEdge) (sheet : Fin degree) :
    (data.edgePartition targetEdge).repr sheet = sheet := by
  have hOne := fibre.indices (data.sourceEdge targetEdge sheet) rfl
  change (data.edgePartition targetEdge).blockCard
    ((data.edgePartition targetEdge).repr sheet) = 1 at hOne
  have hSame := (data.edgePartition targetEdge).block_eq_of_rel
    ((data.edgePartition targetEdge).rel_repr_left sheet)
  have hCard : (data.edgePartition targetEdge).blockCard sheet = 1 := by
    simpa only [SheetPartition.blockCard, hSame] using hOne
  exact repr_eq_self_of_blockCard_eq_one _ sheet hCard

/-- The two surviving edge occurrences have different sheet names because
the leaf-edge partition is discrete. -/
theorem sheet_ne (fibre : LeafFibre data leaf targetEdge) :
    fibre.first.1.1.2 ≠ fibre.second.1.1.2 := by
  intro hSame
  apply fibre.distinct
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (fibre.first_target.trans fibre.second_target.symm) hSame

/-- The distinguished leaf block consists precisely of the two surviving
sheet names. -/
theorem block_eq_pair (fibre : LeafFibre data leaf targetEdge) :
    (data.vertexPartition leaf).block fibre.block.1 =
      {fibre.first.1.1.2, fibre.second.1.1.2} := by
  classical
  have hFirst := ((incident_iff_target_mem_and_rel data fibre.first.1 _).mp
    fibre.first_incident).2
  have hSecond := ((incident_iff_target_mem_and_rel data fibre.second.1 _).mp
    fibre.second_incident).2
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro sheet hSheet
    rcases Finset.mem_insert.mp hSheet with rfl | hSheet
    · exact (data.vertexPartition leaf).mem_block_iff _ _ |>.mpr hFirst
    · have hSheet' := Finset.mem_singleton.mp hSheet
      rw [hSheet']
      exact (data.vertexPartition leaf).mem_block_iff _ _ |>.mpr hSecond
  · rw [Finset.card_pair fibre.sheet_ne]
    exact fibre.local_degree.le

/-- If the two surviving leaf sheets are already identified at a second
target vertex, the entire leaf partition refines its partition. -/
theorem refines_of_pair_rel {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (fibre : LeafFibre data leaf targetEdge)
    (fd : FullDimensionalSourcePresentation data coordinate)
    (hLeaf : (GluingDatum.incidentEdges leaf).card = 1)
    (other : target.V)
    (hPair : (data.vertexPartition other).Rel
      fibre.first.1.1.2 fibre.second.1.1.2) :
    (data.vertexPartition leaf).Refines (data.vertexPartition other) := by
  intro first second hRel
  let block := (data.vertexPartition leaf).toBlock first
  have hBlockFirst : (data.vertexPartition leaf).Rel block.1 first :=
    (data.vertexPartition leaf).rel_repr_left first
  have hBlockSecond := hBlockFirst.trans hRel
  rcases leaf_block_dichotomy data fd.valid fd.noDanglingTargetFibres leaf hLeaf
    (fd.changeMinimal leaf) block with ⟨_, hOne, _⟩ | ⟨_, _, hRamification, _⟩
  · have hSingleton := (data.vertexPartition leaf).block_eq_singleton_of_blockCard_eq_one
      block.1 hOne
    have hFirst : first = block.1 := by
      simpa only [hSingleton, Finset.mem_singleton] using
        (data.vertexPartition leaf).mem_block_iff block.1 first |>.mpr hBlockFirst
    have hSecond : second = block.1 := by
      simpa only [hSingleton, Finset.mem_singleton] using
        (data.vertexPartition leaf).mem_block_iff block.1 second |>.mpr hBlockSecond
    rw [hFirst, hSecond]
    rfl
  · have hBlock := leaf_surviving_blocks_unique data fd.valid leaf hLeaf
      (fd.changeMinimal leaf) block fibre.block hRamification fibre.ramification
    rw [hBlock] at hBlockFirst hBlockSecond
    have hFirst : first ∈ ({fibre.first.1.1.2, fibre.second.1.1.2} : Finset (Fin degree)) := by
      rw [← fibre.block_eq_pair]
      exact (data.vertexPartition leaf).mem_block_iff _ _ |>.mpr hBlockFirst
    have hSecond : second ∈ ({fibre.first.1.1.2, fibre.second.1.1.2} : Finset (Fin degree)) := by
      rw [← fibre.block_eq_pair]
      exact (data.vertexPartition leaf).mem_block_iff _ _ |>.mpr hBlockSecond
    simp only [Finset.mem_insert, Finset.mem_singleton] at hFirst hSecond
    rcases hFirst with rfl | rfl <;> rcases hSecond with rfl | rfl
    · rfl
    · exact hPair
    · exact hPair.symm
    · rfl

/-- The parallel-pair branch of loop-12.  If the leaf block is already
identified at the other endpoint, its two edges create a cycle, contradicting
the fibre's Euler forest count.  The statement is orientation independent. -/
theorem false_of_forest_count_of_refines
    (fibre : LeafFibre data leaf targetEdge)
    (other : target.V) (merged : SheetPartition degree)
    (hLeafRefines : (data.vertexPartition leaf).Refines merged)
    (hOtherRefines : (data.vertexPartition other).Refines merged)
    (hMergedRefines : merged.Refines (data.vertexPartition other))
    (hCount : ∀ mergedBlock : merged.Blocks,
      ((data.edgePartition targetEdge).blockCountWithin merged mergedBlock.1 : ℤ) + 1 =
        ((data.vertexPartition other).blockCountWithin merged mergedBlock.1 : ℤ) +
          ((data.vertexPartition leaf).blockCountWithin merged mergedBlock.1 : ℤ)) :
    False := by
  classical
  let mergedBlock := merged.toBlock fibre.block.1
  have hSame : merged.SameBlocks (data.vertexPartition other) :=
    fun _ _ ↦ ⟨hMergedRefines.rel, hOtherRefines.rel⟩
  have hOtherCount : (data.vertexPartition other).blockCountWithin merged
      mergedBlock.1 = 1 := by
    rw [hSame.blockCountWithin_eq_coarse, SheetPartition.blockCountWithin_self]
  have hEdgeCount : (data.edgePartition targetEdge).blockCountWithin merged
      mergedBlock.1 = merged.blockCard mergedBlock.1 := by
    have hRepr : (data.edgePartition targetEdge).repr = id :=
      funext fibre.edgePartition_repr
    simp [SheetPartition.blockCountWithin, hRepr, SheetPartition.blockCard]
  have hMem : fibre.block ∈ SheetPartition.blocksWithin
      (data.vertexPartition leaf) merged mergedBlock := by
    exact (SheetPartition.mem_blocksWithin _ _ _ _).mpr rfl
  have hStrict : ((SheetPartition.blocksWithin (data.vertexPartition leaf)
        merged mergedBlock).card : ℤ) < (merged.blockCard mergedBlock.1 : ℤ) := by
    calc
      ((SheetPartition.blocksWithin (data.vertexPartition leaf) merged mergedBlock).card : ℤ)
          = ∑ _block ∈ SheetPartition.blocksWithin
              (data.vertexPartition leaf) merged mergedBlock, (1 : ℤ) := by simp
      _ < ∑ block ∈ SheetPartition.blocksWithin (data.vertexPartition leaf) merged mergedBlock,
          ((data.vertexPartition leaf).blockCard block.1 : ℤ) := by
        apply Finset.sum_lt_sum
        · intro block _
          exact_mod_cast (data.vertexPartition leaf).blockCard_pos block.1
        · exact ⟨fibre.block, hMem, by rw [fibre.local_degree]; norm_num⟩
      _ = (merged.blockCard mergedBlock.1 : ℤ) :=
        sum_blockCard_blocksWithin _ _ hLeafRefines mergedBlock
  have hForest := hCount mergedBlock
  rw [hEdgeCount, hOtherCount] at hForest
  rw [SheetPartition.card_blocksWithin_eq_blockCountWithin _ _ hLeafRefines] at hStrict
  omega

/-- An honest forest contraction to a leaf cannot identify the leaf's two
surviving sheets at the other endpoint. -/
theorem not_rel_of_contractionForest {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (fibre : LeafFibre data leaf targetEdge)
    (fd : FullDimensionalSourcePresentation data coordinate)
    (hLeaf : (GluingDatum.incidentEdges leaf).card = 1)
    (other : target.V)
    (hc : (targetEdge : target.V × target.V) = (other, leaf))
    (hForest : ContractionRamification.ContractionForest data other leaf targetEdge) :
    ¬ (data.vertexPartition other).Rel fibre.first.1.1.2 fibre.second.1.1.2 := by
  intro hRel
  have hRefines := fibre.refines_of_pair_rel fd hLeaf other hRel
  exact fibre.false_of_forest_count_of_refines other
    (ContractionRamification.mergedPartition data other leaf)
    (SheetPartition.right_refines_join _ _) (SheetPartition.left_refines_join _ _)
    ((SheetPartition.join_refines_iff _ _ _).mpr ⟨fun _ _ h ↦ h, hRefines⟩)
    (ContractionRamification.contractionForest_count data hc hForest)

end LeafFibre

/-- Draisma--Vargas's change-minimal-leaf description, including uniqueness
of the two surviving source occurrences. -/
theorem exists_leafFibre {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    (leaf : target.V) (targetEdge : target.edges)
    (hLeaf : GluingDatum.incidentEdges leaf = {targetEdge}) :
    Nonempty (LeafFibre data leaf targetEdge) := by
  classical
  have hLeafCard : (GluingDatum.incidentEdges leaf).card = 1 := by simp [hLeaf]
  obtain ⟨first, hFirstTarget, hFirstSurvives⟩ := fd.noDanglingTargetFibres targetEdge
  let firstBlock := (data.vertexPartition leaf).toBlock first.1.2
  have hFirstIncident : Incident data first (blockVertex data leaf firstBlock) := by
    apply (incident_iff_target_mem_and_rel data first _).mpr
    exact ⟨by simp [hFirstTarget, hLeaf],
      (data.vertexPartition leaf).rel_repr_left first.1.2⟩
  obtain ⟨hDegree, hLocalDegree, hRamification⟩ := leaf_block_of_surviving data fd.valid
    fd.noDanglingTargetFibres leaf hLeafCard (fd.changeMinimal leaf)
    firstBlock first hFirstSurvives hFirstIncident
  have hValency : nonDanglingValency data (blockVertex data leaf firstBlock) = 2 := by
    have hLe := nonDanglingValency_le_card_incidentSourceEdge data
      (blockVertex data leaf firstBlock)
    have hPos : 0 < nonDanglingValency data (blockVertex data leaf firstBlock) := by
      rw [← card_nonDanglingIncident]
      exact Finset.card_pos.mpr ⟨first, (mem_nonDanglingIncident data _ first).mpr
        ⟨hFirstSurvives, hFirstIncident⟩⟩
    rcases fd.nonDanglingValency_trichotomy (blockVertex data leaf firstBlock)
      with hZero | hTwo | hThree <;> omega
  obtain ⟨second, ⟨hNe, hSecondSurvives, hSecondIncident⟩, _⟩ :=
    exists_unique_other_of_nonDanglingValency_eq_two data hValency
      hFirstSurvives hFirstIncident
  have hTargetOfIncident : ∀ edge : data.SourceEdge,
      Incident data edge (blockVertex data leaf firstBlock) → edge.1.1 = targetEdge := by
    intro edge hIncident
    have hMem := ((incident_iff_target_mem_and_rel data edge _).mp hIncident).1
    simpa [hLeaf] using hMem
  refine ⟨⟨firstBlock, ⟨first, hFirstSurvives⟩, ⟨second, hSecondSurvives⟩,
    (fun h ↦ hNe (congrArg Subtype.val h).symm), hFirstTarget,
    hTargetOfIncident second hSecondIncident, hFirstIncident, hSecondIncident,
    hDegree, hLocalDegree, hRamification, hValency, ?_, ?_⟩⟩
  · intro edge
    constructor
    · intro hTarget
      let block := (data.vertexPartition leaf).toBlock edge.1.1.2
      have hIncident : Incident data edge.1 (blockVertex data leaf block) := by
        apply (incident_iff_target_mem_and_rel data edge.1 _).mpr
        exact ⟨by simp [hTarget, hLeaf],
          (data.vertexPartition leaf).rel_repr_left edge.1.1.2⟩
      have hEdgeRamification := (leaf_block_of_surviving data fd.valid
        fd.noDanglingTargetFibres leaf hLeafCard (fd.changeMinimal leaf)
        block edge.1 edge.2 hIncident).2.2
      have hBlock := leaf_surviving_blocks_unique data fd.valid leaf hLeafCard
        (fd.changeMinimal leaf) block firstBlock hEdgeRamification hRamification
      rw [hBlock] at hIncident
      have hGraphDegree : vertex_degree data.sourceGraph
          (blockVertex data leaf firstBlock) = 2 := by
        rw [vertex_degree_sourceGraph_eq_card_incidentSourceEdge, hDegree]
        norm_num
      rcases eq_of_incident_of_vertex_degree_eq_two data hNe.symm
        hFirstIncident hSecondIncident hGraphDegree hIncident with hFirst | hSecond
      · exact Or.inl (Subtype.ext hFirst)
      · exact Or.inr (Subtype.ext hSecond)
    · rintro (rfl | rfl)
      · exact hFirstTarget
      · exact hTargetOfIncident second hSecondIncident
  · intro edge hTarget
    let block := (data.vertexPartition leaf).toBlock edge.1.2
    have hIncident : Incident data edge (blockVertex data leaf block) := by
      apply (incident_iff_target_mem_and_rel data edge _).mpr
      exact ⟨by simp [hTarget, hLeaf],
        (data.vertexPartition leaf).rel_repr_left edge.1.2⟩
    exact sourceEdgeIndex_eq_one_of_target_leaf data fd.valid fd.noDanglingTargetFibres
      (blockVertex data leaf block) hLeafCard (fd.changeMinimal leaf) ⟨edge, hIncident⟩

/-- **A change-minimal leaf makes its one occurrence's partition discrete**:
`rem-leaves-min-change`, read straight off `exists_leafFibre`.
`W2MkkSelectedCensus.discrete_of_leaf` states the same fact for the contracted
occurrence of a `w2Mkk` wall. -/
theorem discrete_of_leaf {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    (vertex : target.V) (targetEdge : target.edges)
    (hMem : targetEdge ∈ GluingDatum.incidentEdges vertex)
    (hCard : (GluingDatum.incidentEdges vertex).card = 1) (sheet : Fin degree) :
    (data.edgePartition targetEdge).repr sheet = sheet := by
  obtain ⟨only, hOnly⟩ := Finset.card_eq_one.mp hCard
  have hEdge : targetEdge = only := by simpa [hOnly] using hMem
  obtain ⟨fibre⟩ :=
    exists_leafFibre data fd vertex targetEdge (by simpa [hEdge] using hOnly)
  exact fibre.edgePartition_repr sheet

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-- A target-edge partition with one block inside a source vertex contributes
at most one incident source occurrence there. -/
theorem eq_of_target_eq_of_blockCountWithin_eq_one
    (data : GluingDatum target degree) (vertex : data.SourceVertex)
    (targetEdge : target.edges) (hMem : targetEdge ∈ GluingDatum.incidentEdges vertex.1.1)
    (hCount : (data.edgePartition targetEdge).blockCountWithin
      (data.vertexPartition vertex.1.1) vertex.1.2 = 1)
    (first second : data.SourceEdge) (hFirst : Incident data first vertex)
    (hSecond : Incident data second vertex)
    (hFirstTarget : first.1.1 = targetEdge) (hSecondTarget : second.1.1 = targetEdge) :
    first = second := by
  have hAnchor : ∀ edge : data.SourceEdge, Incident data edge vertex →
      edge.1.1 = targetEdge → edge = data.sourceEdge targetEdge vertex.1.2 := by
    intro edge hIncident hTarget
    have hRel := ((incident_iff_target_mem_and_rel data edge vertex).mp hIncident).2
    have hBlocks := (data.edgePartition targetEdge).block_eq_of_refines_of_blockCountWithin_eq_one
      (data.vertexPartition vertex.1.1) (refines_of_mem_incidentEdges data hMem)
      vertex.1.2 hCount
    have hSheetMem := (data.vertexPartition vertex.1.1).mem_block_iff _ _ |>.mpr hRel
    rw [← hBlocks] at hSheetMem
    have hFineRel := (data.edgePartition targetEdge).mem_block_iff _ _ |>.mp hSheetMem
    apply Subtype.ext
    apply Prod.ext hTarget
    have hRepresentative : (data.edgePartition targetEdge).repr edge.1.2 = edge.1.2 := by
      simpa [hTarget] using edge.2
    exact hRepresentative.symm.trans hFineRel.symm
  exact (hAnchor first hFirst hFirstTarget).trans (hAnchor second hSecond hSecondTarget).symm

namespace LeafFibre

variable {data : GluingDatum target degree} {leaf : target.V} {targetEdge : target.edges}

/-- At a divalent target vertex next to a change-minimal leaf, the other
target direction contains exactly one edge block inside every source block.
Indeed the two block counts are `|A|` and `q`, with `|A|+q≤3` and `1≤q≤|A|`. -/
theorem other_blockCountWithin_eq_one {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (fibre : LeafFibre data leaf targetEdge)
    (fd : FullDimensionalSourcePresentation data coordinate)
    (other : target.V) (next : target.edges) (hNe : targetEdge ≠ next)
    (hDivalent : GluingDatum.incidentEdges other = {targetEdge, next})
    (block : (data.vertexPartition other).Blocks) :
    (data.edgePartition next).blockCountWithin (data.vertexPartition other) block.1 = 1 := by
  classical
  have hVal : (GluingDatum.incidentEdges other).card = 2 := by simp [hDivalent, hNe]
  have hChange : data.targetChange other = 1 := by
    have hMinimal := fd.changeMinimal other
    change data.targetChange other + ((GluingDatum.incidentEdges other).card : ℤ) - 3 = 0
      at hMinimal
    rw [hVal] at hMinimal
    omega
  have hRamification : data.localRamification other block ≤ 1 := by
    rw [← hChange]
    exact Finset.single_le_sum (fun b _ ↦
      data.localRamification_nonneg other (fd.valid.2 other) b) (Finset.mem_univ block)
  have hRepr : (data.edgePartition targetEdge).repr = id := funext fibre.edgePartition_repr
  have hLeafCount : (data.edgePartition targetEdge).blockCountWithin
      (data.vertexPartition other) block.1 = (data.vertexPartition other).blockCard block.1 := by
    simp [SheetPartition.blockCountWithin, hRepr, SheetPartition.blockCard]
  have hOtherLe := SheetPartition.blockCountWithin_le_blockCard (data.edgePartition next)
    (data.vertexPartition other)
    (refines_of_mem_incidentEdges data (by simp [hDivalent])) block
  have hOtherPos := SheetPartition.blockCountWithin_pos (data.edgePartition next)
    (data.vertexPartition other) block.1
  have hSum : data.localRamification other block =
      ((data.vertexPartition other).blockCard block.1 : ℤ) +
        ((data.edgePartition next).blockCountWithin (data.vertexPartition other) block.1 : ℤ) - 2 := by
    unfold GluingDatum.localRamification
    rw [hDivalent, Finset.sum_pair hNe, Finset.card_pair hNe, hLeafCount]
    ring
  omega

/-- When the two surviving leaf sheets remain separate at the other endpoint,
surviving occurrences at that endpoint are injective over its two directions. -/
theorem target_injective_on_nonDanglingIncident {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (fibre : LeafFibre data leaf targetEdge)
    (fd : FullDimensionalSourcePresentation data coordinate)
    (other : target.V) (next : target.edges) (hNe : targetEdge ≠ next)
    (hDivalent : GluingDatum.incidentEdges other = {targetEdge, next})
    (hSeparated : ¬ (data.vertexPartition other).Rel
      fibre.first.1.1.2 fibre.second.1.1.2)
    (block : (data.vertexPartition other).Blocks) :
    Set.InjOn (fun edge : data.SourceEdge ↦ edge.1.1)
      (nonDanglingIncident data (blockVertex data other block)) := by
  classical
  intro first hFirst second hSecond hTarget
  obtain ⟨hFirstSurvives, hFirstIncident⟩ := (mem_nonDanglingIncident data _ first).mp hFirst
  obtain ⟨hSecondSurvives, hSecondIncident⟩ := (mem_nonDanglingIncident data _ second).mp hSecond
  have hFirstData := (incident_iff_target_mem_and_rel data first _).mp hFirstIncident
  have hSecondData := (incident_iff_target_mem_and_rel data second _).mp hSecondIncident
  have hMem : first.1.1 = targetEdge ∨ first.1.1 = next := by
    simpa only [blockVertex_target, hDivalent, Finset.mem_insert, Finset.mem_singleton]
      using hFirstData.1
  rcases hMem with hLeafTarget | hNextTarget
  · have hFirstCases := (fibre.fibre ⟨first, hFirstSurvives⟩).mp hLeafTarget
    have hSecondCases := (fibre.fibre ⟨second, hSecondSurvives⟩).mp
      (hTarget.symm.trans hLeafTarget)
    have hRel : (data.vertexPartition other).Rel first.1.2 second.1.2 :=
      hFirstData.2.symm.trans hSecondData.2
    rcases hFirstCases with hFirstEq | hFirstEq <;>
      rcases hSecondCases with hSecondEq | hSecondEq
    · exact (congrArg Subtype.val hFirstEq).trans (congrArg Subtype.val hSecondEq).symm
    · have hFirstVal : first = fibre.first.1 := congrArg Subtype.val hFirstEq
      have hSecondVal : second = fibre.second.1 := congrArg Subtype.val hSecondEq
      rw [hFirstVal, hSecondVal] at hRel
      exact (hSeparated hRel).elim
    · have hFirstVal : first = fibre.second.1 := congrArg Subtype.val hFirstEq
      have hSecondVal : second = fibre.first.1 := congrArg Subtype.val hSecondEq
      rw [hFirstVal, hSecondVal] at hRel
      exact (hSeparated hRel.symm).elim
    · exact (congrArg Subtype.val hFirstEq).trans (congrArg Subtype.val hSecondEq).symm
  · exact eq_of_target_eq_of_blockCountWithin_eq_one data (blockVertex data other block)
      next (by simp [hDivalent]) (fibre.other_blockCountWithin_eq_one fd other next hNe
        hDivalent block) first second hFirstIncident hSecondIncident hNextTarget
      (hTarget.symm.trans hNextTarget)

/-- All occupied source blocks over the divalent endpoint have surviving
valency two when the leaf pair has not already closed to a loop. -/
theorem valency_eq_two_of_separated {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (fibre : LeafFibre data leaf targetEdge)
    (fd : FullDimensionalSourcePresentation data coordinate)
    (other : target.V) (next : target.edges) (hNe : targetEdge ≠ next)
    (hDivalent : GluingDatum.incidentEdges other = {targetEdge, next})
    (hSeparated : ¬ (data.vertexPartition other).Rel
      fibre.first.1.1.2 fibre.second.1.1.2)
    (block : (data.vertexPartition other).Blocks)
    (edge : NonDanglingEdge data) (hIncident : Incident data edge.1 (blockVertex data other block)) :
    nonDanglingValency data (blockVertex data other block) = 2 := by
  classical
  have hInj := fibre.target_injective_on_nonDanglingIncident fd other next hNe
    hDivalent hSeparated block
  have hSubset : (nonDanglingIncident data (blockVertex data other block)).image
      (fun edge : data.SourceEdge ↦ edge.1.1) ⊆ {targetEdge, next} := by
    intro image hImage
    obtain ⟨sourceEdge, hMem, rfl⟩ := Finset.mem_image.mp hImage
    have hInc := (mem_nonDanglingIncident data _ sourceEdge).mp hMem |>.2
    have hTarget := (incident_iff_target_mem_and_rel data sourceEdge _).mp hInc |>.1
    simpa only [blockVertex_target, hDivalent] using hTarget
  have hLe := Finset.card_le_card hSubset
  rw [Finset.card_image_of_injOn hInj, card_nonDanglingIncident, Finset.card_pair hNe] at hLe
  have hPos : 0 < nonDanglingValency data (blockVertex data other block) := by
    rw [← card_nonDanglingIncident]
    exact Finset.card_pos.mpr ⟨edge.1,
      (mem_nonDanglingIncident data _ _).mpr ⟨edge.2, hIncident⟩⟩
  rcases fd.nonDanglingValency_trichotomy (blockVertex data other block)
    with hZero | hTwo | hThree <;> omega

/-- In the non-loop branch, every surviving occurrence over the next target
edge joins the leaf's single stable path through a divalent source vertex. -/
theorem stablePath_eq_of_next_of_separated {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (fibre : LeafFibre data leaf targetEdge)
    (fd : FullDimensionalSourcePresentation data coordinate)
    (other : target.V) (next : target.edges) (hNe : targetEdge ≠ next)
    (hDivalent : GluingDatum.incidentEdges other = {targetEdge, next})
    (hSeparated : ¬ (data.vertexPartition other).Rel
      fibre.first.1.1.2 fibre.second.1.1.2)
    (edge : NonDanglingEdge data) (hTarget : edge.1.1.1 = next) :
    edge.stablePath = fibre.first.stablePath := by
  classical
  let block := (data.vertexPartition other).toBlock edge.1.1.2
  have hIncident : Incident data edge.1 (blockVertex data other block) := by
    apply (incident_iff_target_mem_and_rel data edge.1 _).mpr
    exact ⟨by simp [hTarget, hDivalent], (data.vertexPartition other).rel_repr_left _⟩
  have hValency := fibre.valency_eq_two_of_separated fd other next hNe hDivalent
    hSeparated block edge hIncident
  obtain ⟨companion, ⟨hCompanionNe, hCompanionSurvives, hCompanionIncident⟩, _⟩ :=
    exists_unique_other_of_nonDanglingValency_eq_two data hValency edge.2 hIncident
  have hCompanionTarget : companion.1.1 = targetEdge := by
    have hMem := (incident_iff_target_mem_and_rel data companion _).mp hCompanionIncident |>.1
    have hCases : companion.1.1 = targetEdge ∨ companion.1.1 = next := by
      simpa only [blockVertex_target, hDivalent, Finset.mem_insert, Finset.mem_singleton] using hMem
    rcases hCases with hLeafTarget | hNextTarget
    · exact hLeafTarget
    · apply False.elim
      apply hCompanionNe
      exact eq_of_target_eq_of_blockCountWithin_eq_one data (blockVertex data other block)
        next (by simp [hDivalent])
        (fibre.other_blockCountWithin_eq_one fd other next hNe hDivalent block)
        companion edge.1 hCompanionIncident hIncident hNextTarget hTarget
  have hPath : edge.stablePath =
      NonDanglingEdge.stablePath (⟨companion, hCompanionSurvives⟩ : NonDanglingEdge data) := by
    apply stablePath_eq_of_consecutive
    exact ⟨fun h ↦ hCompanionNe (congrArg Subtype.val h).symm,
      blockVertex data other block, hIncident, hCompanionIncident, hValency⟩
  exact hPath.trans (fibre.stablePath_eq_of_target
    ⟨companion, hCompanionSurvives⟩ hCompanionTarget)

end LeafFibre

/-- If an entire surviving target fibre lies in one stable path, every other
row of that target column vanishes. -/
theorem matrix_column_eq_zero_of_single_stablePath
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    {data : GluingDatum target degree}
    (labelling : StableLengthMatrixLabelling data coordinate)
    (targetEdge : target.edges) (path : StablePath data)
    (hPath : ∀ edge : NonDanglingEdge data,
      edge.1.1.1 = targetEdge → edge.stablePath = path)
    (row : coordinate) (hRow : row ≠ labelling.row path) :
    GluingDatum.LengthMatrixPresentation.matrix labelling.presentation row
      (labelling.targetEdge.symm targetEdge) = 0 := by
  unfold GluingDatum.LengthMatrixPresentation.matrix GluingDatum.LengthMatrixPresentation.row
  apply List.sum_eq_zero
  intro coefficient hCoefficient
  obtain ⟨sourceEdge, hSourceEdge, rfl⟩ := List.mem_map.mp hCoefficient
  obtain ⟨hSurvives, hSourceRow⟩ := (labelling.mem_path_iff row sourceEdge).mp hSourceEdge
  apply GluingDatum.LengthMatrixPresentation.coefficient_eq_zero_of_target_ne
  intro hTarget
  have hTarget' : sourceEdge.1.1 = targetEdge := by
    simpa only [StableLengthMatrixLabelling.presentation, Equiv.apply_symm_apply]
      using hTarget.symm
  have hPath' := hPath ⟨sourceEdge, hSurvives⟩ hTarget'
  exact hRow (hSourceRow.symm.trans (congrArg labelling.row hPath'))

/-- Two distinct columns supported in the same single row are dependent.
The explicit kernel vector also covers the case where one column vanishes. -/
theorem det_eq_zero_of_two_columns_supported_in_one_row
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (matrix : Matrix coordinate coordinate ℚ) (first second row : coordinate)
    (hNe : first ≠ second)
    (hFirst : ∀ i, i ≠ row → matrix i first = 0)
    (hSecond : ∀ i, i ≠ row → matrix i second = 0) : matrix.det = 0 := by
  by_cases hZero : matrix row first = 0
  · apply Matrix.det_eq_zero_of_column_eq_zero first
    intro i
    by_cases hi : i = row
    · simpa [hi] using hZero
    · exact hFirst i hi
  · apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨Pi.single first (matrix row second) - Pi.single second (matrix row first), ?_, ?_⟩
    · intro hVector
      have hAt := congrFun hVector second
      have hEntry : matrix row first = 0 := by
        simpa [Pi.single_apply, hNe.symm] using hAt
      exact hZero hEntry
    · rw [Matrix.mulVec_sub, Matrix.mulVec_single, Matrix.mulVec_single]
      ext i
      change matrix i first * matrix row second - matrix i second * matrix row first = 0
      by_cases hi : i = row
      · rw [hi]
        ring
      · rw [hFirst i hi, hSecond i hi]
        ring

namespace LeafFibre

variable {data : GluingDatum target degree} {leaf : target.V} {targetEdge : target.edges}

/-- The non-loop branch of loop-12 contradicts the nonsingularity of the
honest stable length matrix: both adjacent target columns lie in one row. -/
theorem false_of_divalent_of_separated {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (fibre : LeafFibre data leaf targetEdge)
    (fd : FullDimensionalSourcePresentation data coordinate)
    (other : target.V) (next : target.edges) (hNe : targetEdge ≠ next)
    (hDivalent : GluingDatum.incidentEdges other = {targetEdge, next})
    (hSeparated : ¬ (data.vertexPartition other).Rel
      fibre.first.1.1.2 fibre.second.1.1.2) : False := by
  apply fd.det_ne_zero
  apply det_eq_zero_of_two_columns_supported_in_one_row _
    (fd.labelling.targetEdge.symm targetEdge) (fd.labelling.targetEdge.symm next)
    (fd.labelling.row fibre.first.stablePath)
    (fun h ↦ hNe (fd.labelling.targetEdge.symm.injective h))
  · exact matrix_column_eq_zero_of_single_stablePath fd.labelling targetEdge
      fibre.first.stablePath fibre.stablePath_eq_of_target
  · exact matrix_column_eq_zero_of_single_stablePath fd.labelling next
      fibre.first.stablePath (fibre.stablePath_eq_of_next_of_separated fd other next
        hNe hDivalent hSeparated)

end LeafFibre

/-- The left-leaf orientation of the same forest obstruction. -/
theorem LeafFibre.not_rel_of_contractionForest_left {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate]
    {data : GluingDatum target degree} {leaf : target.V} {targetEdge : target.edges}
    (fibre : LeafFibre data leaf targetEdge)
    (fd : FullDimensionalSourcePresentation data coordinate)
    (hLeaf : (GluingDatum.incidentEdges leaf).card = 1)
    (other : target.V)
    (hc : (targetEdge : target.V × target.V) = (leaf, other))
    (hForest : ContractionRamification.ContractionForest data leaf other targetEdge) :
    ¬ (data.vertexPartition other).Rel fibre.first.1.1.2 fibre.second.1.1.2 := by
  intro hRel
  have hRefines := fibre.refines_of_pair_rel fd hLeaf other hRel
  apply fibre.false_of_forest_count_of_refines other
    (ContractionRamification.mergedPartition data leaf other)
    (SheetPartition.left_refines_join _ _) (SheetPartition.right_refines_join _ _)
    ((SheetPartition.join_refines_iff _ _ _).mpr ⟨hRefines, fun _ _ h ↦ h⟩)
  intro block
  have hCount := ContractionRamification.contractionForest_count data hc hForest block
  linarith

private theorem incidentEdges_eq_singleton_of_card_eq_one
    (vertex : target.V) (edge : target.edges)
    (hCard : (GluingDatum.incidentEdges vertex).card = 1)
    (hMem : edge ∈ GluingDatum.incidentEdges vertex) :
    GluingDatum.incidentEdges vertex = {edge} := by
  obtain ⟨only, hOnly⟩ := Finset.card_eq_one.mp hCard
  have hEdge : edge = only := by simpa [hOnly] using hMem
  simpa [hEdge] using hOnly

private theorem exists_other_incidentEdge_of_card_eq_two
    (vertex : target.V) (edge : target.edges)
    (hCard : (GluingDatum.incidentEdges vertex).card = 2)
    (hMem : edge ∈ GluingDatum.incidentEdges vertex) :
    ∃ next : target.edges, edge ≠ next ∧
      GluingDatum.incidentEdges vertex = {edge, next} := by
  obtain ⟨first, second, hNe, hPair⟩ := Finset.card_eq_two.mp hCard
  have hCases : edge = first ∨ edge = second := by
    simpa only [hPair, Finset.mem_insert, Finset.mem_singleton] using hMem
  rcases hCases with rfl | rfl
  · exact ⟨second, hNe, hPair⟩
  · exact ⟨first, hNe.symm, hPair.trans (Finset.pair_comm _ _)⟩

/-- The contraction-forest consequence of Draisma--Vargas `lemma-loop-12`.
An occurrence between a divalent target vertex and a leaf cannot be contracted
without dropping the source genus.  Full rank rules out the non-loop branch;
the remaining parallel leaf pair violates the forest count. -/
theorem not_contractionForest_of_leaf_divalent {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    (div leaf : target.V) (contracted : target.edges)
    (hc : (contracted : target.V × target.V) = (div, leaf))
    (hDiv : (GluingDatum.incidentEdges div).card = 2)
    (hLeaf : (GluingDatum.incidentEdges leaf).card = 1) :
    ¬ ContractionRamification.ContractionForest data div leaf contracted := by
  intro hForest
  have hLeafSet := incidentEdges_eq_singleton_of_card_eq_one leaf contracted hLeaf
    (ContractionRamification.contracted_mem_incidentEdges_right hc)
  obtain ⟨fibre⟩ := exists_leafFibre data fd leaf contracted hLeafSet
  obtain ⟨next, hNe, hPair⟩ := exists_other_incidentEdge_of_card_eq_two div contracted hDiv
    (ContractionRamification.contracted_mem_incidentEdges_left hc)
  exact fibre.false_of_divalent_of_separated fd div next hNe hPair
    (fibre.not_rel_of_contractionForest fd hLeaf div hc hForest)

/-- The same exclusion with the leaf as the first endpoint of the ordered
target occurrence.  No edge orientation is silently changed. -/
theorem not_contractionForest_of_divalent_leaf {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    (leaf div : target.V) (contracted : target.edges)
    (hc : (contracted : target.V × target.V) = (leaf, div))
    (hLeaf : (GluingDatum.incidentEdges leaf).card = 1)
    (hDiv : (GluingDatum.incidentEdges div).card = 2) :
    ¬ ContractionRamification.ContractionForest data leaf div contracted := by
  intro hForest
  have hLeafSet := incidentEdges_eq_singleton_of_card_eq_one leaf contracted hLeaf
    (ContractionRamification.contracted_mem_incidentEdges_left hc)
  obtain ⟨fibre⟩ := exists_leafFibre data fd leaf contracted hLeafSet
  obtain ⟨next, hNe, hPair⟩ := exists_other_incidentEdge_of_card_eq_two div contracted hDiv
    (ContractionRamification.contracted_mem_incidentEdges_right hc)
  exact fibre.false_of_divalent_of_separated fd div next hNe hPair
    (fibre.not_rel_of_contractionForest_left fd hLeaf div hc hForest)

/-- A monovalent wall is excluded on exactly the hypothesis bundle of
`WallProgress.card_incidentEdges_merge_cases`.  No stable-path or trivalence
condition on the contracted datum is added. -/
theorem card_incidentEdges_merge_ne_one {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (data : GluingDatum target degree)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionRamification.ContractionForest data a b contracted) :
    (GluingDatum.incidentEdges
      (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card ≠ 1 := by
  intro hWall
  obtain ⟨hSum, hAPos, hALe, hBPos, hBLe, _, _⟩ :=
    WallProgress.endpoints_of_contraction data hc hab hOne fullDim.valid fullDim.changeMinimal
  have hCases :
      ((GluingDatum.incidentEdges a).card = 1 ∧ (GluingDatum.incidentEdges b).card = 2) ∨
      ((GluingDatum.incidentEdges a).card = 2 ∧ (GluingDatum.incidentEdges b).card = 1) := by
    omega
  rcases hCases with ⟨hLeaf, hDiv⟩ | ⟨hDiv, hLeaf⟩
  · exact not_contractionForest_of_divalent_leaf data fullDim a b contracted hc hLeaf hDiv hForest
  · exact not_contractionForest_of_leaf_divalent data fullDim a b contracted hc hDiv hLeaf hForest

/-- The wall valencies of the W2, W3 and W4 equations are exhaustive for a
full-dimensional incoming datum and a forest contraction. -/
theorem card_incidentEdges_merge_eq_two_three_or_four {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate] (data : GluingDatum target degree)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionRamification.ContractionForest data a b contracted) :
    (GluingDatum.incidentEdges
        (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card = 2 ∨
      (GluingDatum.incidentEdges
          (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card = 3 ∨
        (GluingDatum.incidentEdges
          (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card = 4 := by
  have hCases := WallProgress.card_incidentEdges_merge_cases data hc hab hOne fullDim hForest
  have hNotOne := card_incidentEdges_merge_ne_one data hc hab hOne fullDim hForest
  omega

/-! ### A degree-three witness that the forest count alone is not enough -/

namespace ForestCountWitness

/-- The divalent endpoint's sheet partition `{0,2},{1}` at degree three. -/
def divalent : SheetPartition 3 := ⟨![0, 1, 0], by decide⟩

/-- The leaf's sheet partition `{0,1},{2}` at degree three.  Its two-sheet
block is the one `rem-leaves-min-change` produces above a change-minimal
leaf. -/
def leafBlocks : SheetPartition 3 := ⟨![0, 0, 2], by decide⟩

/-- Every sheet is joined to sheet `0`: `0 ~ 1` at the leaf and `0 ~ 2` at the
divalent endpoint. -/
theorem joinRel_zero (sheet : Fin 3) :
    SheetPartition.JoinRel divalent leafBlocks 0 sheet := by
  fin_cases sheet
  · exact SheetPartition.joinRel_refl _ _ _
  · exact SheetPartition.joinRel_of_right (by decide)
  · exact SheetPartition.joinRel_of_left (by decide)

/-- The merged partition at this wall is the one-block partition. -/
theorem join_rel (first second : Fin 3) :
    (SheetPartition.join divalent leafBlocks).Rel first second :=
  (SheetPartition.join_rel_iff _ _ _ _).mpr
    ((joinRel_zero first).symm.trans (joinRel_zero second))

theorem join_block (sheet : Fin 3) :
    (SheetPartition.join divalent leafBlocks).block sheet = Finset.univ := by
  ext other
  simp only [SheetPartition.mem_block_iff, Finset.mem_univ, iff_true]
  exact join_rel sheet other

/-- **The contraction-forest count holds for this configuration**: three edge
blocks, one divalent block and two leaf blocks inside the single merged block,
so `E + 1 = p + q` reads `3 + 1 = 2 + 2`.  Since the configuration is also
change-minimal at both endpoints (the arithmetic is in the module docstring),
`ContractionForest` by itself does not exclude a monovalent wall, and the
`det_ne_zero` half of `not_contractionForest_of_leaf_divalent` cannot be
dropped. -/
theorem contractionForest_count (sheet : Fin 3) :
    (SheetPartition.discrete 3).blockCountWithin
        (SheetPartition.join divalent leafBlocks) sheet + 1
      = divalent.blockCountWithin (SheetPartition.join divalent leafBlocks) sheet
        + leafBlocks.blockCountWithin
            (SheetPartition.join divalent leafBlocks) sheet := by
  simp only [SheetPartition.blockCountWithin, join_block]
  decide

end ForestCountWitness

end DraismaVargas.LocalCases.MonovalentWall
