import DraismaVargasCount.Multiplicity
import DraismaVargas.LocalCases.StableLocalProperties

/-!
# Leaf fibres of a full-dimensional tropical morphism, and the leaf columns

**Source.**  Draisma–Vargas Part I (arXiv:1909.12924), the remark on
change-minimal leaves (`rem-leaves-min-change`), whose local input is
`StableLocalProperties.leaf_block_dichotomy`.  The route transcribed here:
`k_i = 1 ⇒ r_i = 0` by dangling-no-glue, `k_i ≥ 2 ⇒ r_i ≥ 2`, and
`Σ_i r_i = ch(v) = 2` leaves exactly one block with `k = m = 2`.  Item (a) of
Vargas, Part II (arXiv:2609.09109), `lemma-edge-deno` is *not* needed here.

Let `v` be a leaf of the target tree `T`, `t_v` its unique incident edge
occurrence, and `φ` a full-dimensional morphism presented by a
`FullDimensionalSourcePresentation`.

## What is proved

* `coreBlock`, `coreVertex` — `A_v`, the **unique** block above `v` with
  `r_φ = 2` (`coreBlocks_card_eq_one`), with
  `blockCard_coreBlock : m(A_v) = 2`,
  `vertex_degree_coreVertex : val(A_v) = 2` and
  `nonDanglingValency_coreVertex : nd(A_v) = 2`; both occurrences at `A_v`
  survive (`not_isDangling_of_incident_coreVertex`).
* `other_block_data`, `vertex_degree_other_block`, `isDangling_of_other_block`
  — every other block above `v` is a single sheet of source degree one whose
  occurrence is dangling: the `d - 2` dangling leaves of the fibre.
* `card_blocks_leaf` — the fibre above `v` has `d - 1` blocks.
* `sourceEdgeIndex_eq_one_above_leaf` and `card_blocks_leafEdge` — **all `d`
  occurrences above `t_v` are unramified**, so there are exactly `d` of them.
* `leafRow` — `h(v)`, the stable row of the two surviving occurrences at
  `A_v`; `stablePath_eq_of_mem_leafSurvivors` is the interiority statement
  (`A_v` lies inside a *single* stable path, because its two surviving
  occurrences are consecutive there).
* `matrix_leafEdge_column` — **the `t_v` column of `A_φ` is `2 · e_{h(v)}`.**
* `leafRow_ne` — `v ↦ h(v)` is injective as soon as distinct leaves carry
  distinct leaf edges, and `leafRow_ne_of_noLeafToLeafEdge` supplies that from
  the combinatorial `NoLeafToLeafEdge` of `DraismaVargasCount.Multiplicity`.
* `matrix_eq_sum_fibre` and `rowFibre` — the reusable presentation of one
  matrix entry as a sum of reciprocal indices over the surviving occurrences
  of that row above that target occurrence.  The same computation appears
  inline in
  `StableLocalProperties.matrix_column_eq_of_divalent_of_surviving_localRamification_zero`;
  `Count.IndexPattern` uses it too.

## Related results

* **Injectivity of `v ↦ h(v)` without a hypothesis.**  `leafRow_ne` carries the
  hypothesis `leafEdge hFirst ≠ leafEdge hSecond`;
  `leafRow_ne_of_noLeafToLeafEdge` discharges it from
  `Count.NoLeafToLeafEdge target` (exactly the hypothesis
  `DraismaVargasCount.Multiplicity` carries for `absMult = |det B'|`), and
  `Count.noLeafToLeafEdge_of_fullDimensional` (in
  `DraismaVargasCount.Integrality`) derives `NoLeafToLeafEdge target` from a
  `FullDimensionalSourcePresentation` alone, by the `pathEnds`-cycle argument,
  with no further hypothesis.  `Caterpillar.noLeafToLeafEdge_catTree` is the
  special case of the caterpillar.
* `d_{h(v)} = 1`, the leaf-row denominator, is
  `Count.EdgeDenominator.rowDenominator_eq_one_of_leafRow` (the edge-denominator
  lemma, Vargas, Part II, `lemma-edge-deno`), with no hypothesis beyond a
  `FullDimensionalSourcePresentation` and `IsLeafVertex`.
* The `B'` form of the leaf column (`(1/2) · 2 · e_{h(v)} = e_{h(v)}`) is
  `Count.clearedMatrix_leafColumn` in `DraismaVargasCount.Integrality`
  (integrality of the cleared matrix), as the standard basis vector `e_{h(v)}`,
  combining this file's `matrix_leafEdge_column` with the leaf-row denominator
  `d_{h(v)} = 1` of the bullet above.
* Nothing here is conditional on integrality, on the genus, or on the degree.

## Consumers

`Count.IndexPattern` (the index pattern along a stable row) consumes `leafRow`,
`matrix_leafEdge_column` and `matrix_eq_sum_fibre`; `Count.EdgeDenominator`
(the edge-denominator lemma) consumes `sourceEdgeIndex_eq_one_above_leaf`;
`DraismaVargasCount.Integrality` consumes the leaf column in its `B'` form.
Through them the leaf fibres enter the multiplicities used at every step of the
count.
-/

namespace DraismaVargas.Count.LeafFibre

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.GluingDatum.LengthMatrixPresentation
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableLocalProperties
open DraismaVargas.LocalCases.FullDimensionalSource

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-! ## The entries of the honest stable length matrix as fibre sums -/

/-- **One entry of the honest stable length matrix**: the sum of the reciprocal
dilation indices of the surviving occurrences of that row lying above that
target occurrence.  This is the computation inlined in
`StableLocalProperties.matrix_column_eq_of_divalent_of_surviving_localRamification_zero`,
isolated here because both the leaf column and the transition relation need
it. -/
noncomputable def rowFibre (labelling : StableLengthMatrixLabelling data coordinate)
    (sourceRow : coordinate) (item : target.edges) : Finset data.SourceEdge := by
  classical
  exact (Finset.univ : Finset data.SourceEdge).filter
    fun edge ↦ (∃ hSurvives : ¬ IsDangling data edge,
        labelling.row (NonDanglingEdge.stablePath
          (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = sourceRow) ∧
      edge.1.1 = item

omit [Fintype coordinate] in
theorem mem_rowFibre (labelling : StableLengthMatrixLabelling data coordinate)
    (sourceRow : coordinate) (item : target.edges) (edge : data.SourceEdge) :
    edge ∈ rowFibre labelling sourceRow item ↔
      (∃ hSurvives : ¬ IsDangling data edge,
          labelling.row (NonDanglingEdge.stablePath
            (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = sourceRow) ∧
        edge.1.1 = item := by
  classical
  simp [rowFibre]

omit [Fintype coordinate] in
theorem matrix_eq_sum_fibre (labelling : StableLengthMatrixLabelling data coordinate)
    (sourceRow : coordinate) (item : target.edges) :
    GluingDatum.LengthMatrixPresentation.matrix labelling.presentation sourceRow
        (labelling.targetEdge.symm item) =
      ∑ edge ∈ rowFibre labelling sourceRow item,
        (1 : ℚ) / data.sourceEdgeIndex edge := by
  classical
  have hFibre : rowFibre labelling sourceRow item =
      (Finset.univ : Finset data.SourceEdge).filter
        (fun edge ↦ (∃ hSurvives : ¬ IsDangling data edge,
            labelling.row (NonDanglingEdge.stablePath
              (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = sourceRow) ∧
          edge.1.1 = item) := by
    ext edge
    rw [mem_rowFibre]
    simp
  rw [hFibre]
  have hNodup : (labelling.path sourceRow).Nodup := by
    unfold StableLengthMatrixLabelling.path
    exact List.Nodup.filter _ (Finset.univ.nodup_toList)
  have hToFinset : (labelling.path sourceRow).toFinset =
      (Finset.univ : Finset data.SourceEdge).filter
        (fun edge ↦ ∃ hSurvives : ¬ IsDangling data edge,
          labelling.row (NonDanglingEdge.stablePath
            (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = sourceRow) := by
    ext edge
    simp [List.mem_toFinset, labelling.mem_path_iff]
  calc
    GluingDatum.LengthMatrixPresentation.matrix labelling.presentation sourceRow
          (labelling.targetEdge.symm item)
        = ((labelling.path sourceRow).map fun edge ↦
            GluingDatum.LengthMatrixPresentation.coefficient
              labelling.presentation edge
              (labelling.targetEdge.symm item)).sum := rfl
    _ = ∑ edge ∈ (labelling.path sourceRow).toFinset,
          GluingDatum.LengthMatrixPresentation.coefficient
            labelling.presentation edge
            (labelling.targetEdge.symm item) :=
        (List.sum_toFinset _ hNodup).symm
    _ = ∑ edge ∈ (Finset.univ : Finset data.SourceEdge).filter
            (fun edge ↦ ∃ hSurvives : ¬ IsDangling data edge,
              labelling.row (NonDanglingEdge.stablePath
                (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = sourceRow),
          GluingDatum.LengthMatrixPresentation.coefficient
            labelling.presentation edge
            (labelling.targetEdge.symm item) := by
        rw [hToFinset]
    _ = ∑ edge ∈ ((Finset.univ : Finset data.SourceEdge).filter
            (fun edge ↦ ∃ hSurvives : ¬ IsDangling data edge,
              labelling.row (NonDanglingEdge.stablePath
                (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = sourceRow)).filter
            (fun edge ↦ edge.1.1 = item),
          (1 : ℚ) / data.sourceEdgeIndex edge := by
        conv_rhs => rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro edge _
        by_cases hCase : edge.1.1 = item
        · rw [if_pos hCase]
          simp [GluingDatum.LengthMatrixPresentation.coefficient,
            StableLengthMatrixLabelling.presentation, hCase]
        · rw [if_neg hCase]
          apply GluingDatum.LengthMatrixPresentation.coefficient_eq_zero_of_target_ne
          simp only [StableLengthMatrixLabelling.presentation,
            Equiv.apply_symm_apply]
          exact fun hEqual ↦ hCase hEqual.symm
    _ = ∑ edge ∈ (Finset.univ : Finset data.SourceEdge).filter
            (fun edge ↦ (∃ hSurvives : ¬ IsDangling data edge,
                labelling.row (NonDanglingEdge.stablePath
                  (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = sourceRow) ∧
              edge.1.1 = item),
          (1 : ℚ) / data.sourceEdgeIndex edge := by
        rw [Finset.filter_filter]

variable (fd : FullDimensionalSourcePresentation data coordinate)

section Leaf

variable {leaf : target.V} (hLeaf : IsLeafVertex target leaf)

include fd hLeaf

theorem targetChange_leaf : data.targetChange leaf = 2 := by
  have hCard : (GluingDatum.incidentEdges leaf).card = 1 := hLeaf
  have h := fd.targetExcess_eq_zero leaf
  unfold GluingDatum.targetExcess at h
  rw [hCard] at h
  omega

theorem dichotomy (block : (data.vertexPartition leaf).Blocks) :
    (Fintype.card (IncidentSourceEdge data (blockVertex data leaf block)) = 1 ∧
        (data.vertexPartition leaf).blockCard block.1 = 1 ∧
        data.localRamification leaf block = 0) ∨
      (Fintype.card (IncidentSourceEdge data (blockVertex data leaf block)) = 2 ∧
        (data.vertexPartition leaf).blockCard block.1 = 2 ∧
        data.localRamification leaf block = 2 ∧
        ∃ edge : IncidentSourceEdge data (blockVertex data leaf block),
          ¬ IsDangling data edge.1) :=
  leaf_block_dichotomy data fd.valid fd.noDanglingTargetFibres leaf hLeaf
    (fd.changeMinimal leaf) block

/-- The blocks above the leaf carrying the whole change. -/
theorem coreBlocks_card_eq_one :
    ((Finset.univ : Finset (data.vertexPartition leaf).Blocks).filter
      fun block ↦ data.localRamification leaf block = 2).card = 1 := by
  classical
  have hSum : (∑ block : (data.vertexPartition leaf).Blocks,
      data.localRamification leaf block) = 2 := targetChange_leaf fd hLeaf
  have hSplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (data.vertexPartition leaf).Blocks)
    (fun block ↦ data.localRamification leaf block = 2)
    (fun block ↦ data.localRamification leaf block)
  have hYes : (∑ block ∈ (Finset.univ : Finset (data.vertexPartition leaf).Blocks).filter
      (fun block ↦ data.localRamification leaf block = 2),
      data.localRamification leaf block) =
      (((Finset.univ : Finset (data.vertexPartition leaf).Blocks).filter
        fun block ↦ data.localRamification leaf block = 2).card : ℤ) * 2 := by
    rw [Finset.sum_congr rfl fun block hblock ↦ (Finset.mem_filter.mp hblock).2,
      Finset.sum_const, nsmul_eq_mul]
  have hNo : (∑ block ∈ (Finset.univ : Finset (data.vertexPartition leaf).Blocks).filter
      (fun block ↦ ¬ data.localRamification leaf block = 2),
      data.localRamification leaf block) = 0 := by
    refine Finset.sum_eq_zero fun block hblock ↦ ?_
    have hNe := (Finset.mem_filter.mp hblock).2
    rcases dichotomy fd hLeaf block with ⟨_, _, hZero⟩ | ⟨_, _, hTwo, _⟩
    · exact hZero
    · exact absurd hTwo hNe
  rw [hYes, hNo, hSum] at hSplit
  omega

/-- `A_v`: the unique block above a leaf carrying local ramification two. -/
noncomputable def coreBlock : (data.vertexPartition leaf).Blocks :=
  (Finset.card_eq_one.mp (coreBlocks_card_eq_one fd hLeaf)).choose

theorem coreBlocks_eq_singleton :
    ((Finset.univ : Finset (data.vertexPartition leaf).Blocks).filter
      fun block ↦ data.localRamification leaf block = 2) = {coreBlock fd hLeaf} :=
  (Finset.card_eq_one.mp (coreBlocks_card_eq_one fd hLeaf)).choose_spec

theorem localRamification_coreBlock :
    data.localRamification leaf (coreBlock fd hLeaf) = 2 := by
  have hMem : coreBlock fd hLeaf ∈
      ((Finset.univ : Finset (data.vertexPartition leaf).Blocks).filter
        fun block ↦ data.localRamification leaf block = 2) := by
    rw [coreBlocks_eq_singleton fd hLeaf]
    exact Finset.mem_singleton_self _
  exact (Finset.mem_filter.mp hMem).2

theorem eq_coreBlock_of_localRamification_eq_two
    {block : (data.vertexPartition leaf).Blocks}
    (hTwo : data.localRamification leaf block = 2) : block = coreBlock fd hLeaf := by
  have hMem : block ∈
      ((Finset.univ : Finset (data.vertexPartition leaf).Blocks).filter
        fun block ↦ data.localRamification leaf block = 2) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTwo⟩
  rw [coreBlocks_eq_singleton fd hLeaf, Finset.mem_singleton] at hMem
  exact hMem

/-- The quotient-source vertex `A_v`. -/
noncomputable def coreVertex : data.SourceVertex :=
  blockVertex data leaf (coreBlock fd hLeaf)

theorem coreVertex_target : (coreVertex fd hLeaf).1.1 = leaf := rfl

/-- The core block has two incident source occurrences and local degree two. -/
theorem coreBlock_data :
    Fintype.card (IncidentSourceEdge data (coreVertex fd hLeaf)) = 2 ∧
      (data.vertexPartition leaf).blockCard (coreBlock fd hLeaf).1 = 2 := by
  rcases dichotomy fd hLeaf (coreBlock fd hLeaf) with ⟨_, _, hZero⟩ | ⟨hCard, hBlock, _, _⟩
  · exact absurd (localRamification_coreBlock fd hLeaf) (by rw [hZero]; decide)
  · exact ⟨hCard, hBlock⟩

theorem blockCard_coreBlock :
    (data.vertexPartition leaf).blockCard (coreBlock fd hLeaf).1 = 2 :=
  (coreBlock_data fd hLeaf).2

/-- Every other block above the leaf is a single sheet with a single incident
occurrence and no ramification. -/
theorem other_block_data {block : (data.vertexPartition leaf).Blocks}
    (hNe : block ≠ coreBlock fd hLeaf) :
    Fintype.card (IncidentSourceEdge data (blockVertex data leaf block)) = 1 ∧
      (data.vertexPartition leaf).blockCard block.1 = 1 ∧
      data.localRamification leaf block = 0 := by
  rcases dichotomy fd hLeaf block with hFirst | ⟨_, _, hTwo, _⟩
  · exact hFirst
  · exact absurd (eq_coreBlock_of_localRamification_eq_two fd hLeaf hTwo) hNe

omit [Fintype coordinate] [DecidableEq coordinate] fd hLeaf in
theorem nonDanglingValency_le_card (vertex : data.SourceVertex) :
    nonDanglingValency data vertex ≤ Fintype.card (IncidentSourceEdge data vertex) := by
  classical
  rw [← card_filter_not_isDangling_eq_nonDanglingValency data vertex]
  simpa [Finset.card_univ] using
    Finset.card_filter_le (Finset.univ : Finset (IncidentSourceEdge data vertex))
      (fun edge ↦ ¬ IsDangling data edge.1)

/-- `A_v` is a core vertex of surviving valency two. -/
theorem nonDanglingValency_coreVertex :
    nonDanglingValency data (coreVertex fd hLeaf) = 2 := by
  classical
  have hLe : nonDanglingValency data (coreVertex fd hLeaf) ≤ 2 := by
    have := nonDanglingValency_le_card (coreVertex fd hLeaf)
    rw [(coreBlock_data fd hLeaf).1] at this
    exact this
  have hPos : nonDanglingValency data (coreVertex fd hLeaf) ≠ 0 := by
    rcases dichotomy fd hLeaf (coreBlock fd hLeaf) with ⟨_, _, hZero⟩ | ⟨_, _, _, edge, hEdge⟩
    · exact absurd (localRamification_coreBlock fd hLeaf) (by rw [hZero]; decide)
    · intro hZero
      have hMem : edge.1 ∈ (Finset.univ : Finset data.SourceEdge).filter
          fun item ↦ ¬ IsDangling data item ∧ Incident data item (coreVertex fd hLeaf) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hEdge, edge.2⟩
      have hEmpty : ((Finset.univ : Finset data.SourceEdge).filter
          fun item ↦ ¬ IsDangling data item ∧
            Incident data item (coreVertex fd hLeaf)) = ∅ :=
        Finset.card_eq_zero.mp hZero
      rw [hEmpty] at hMem
      exact absurd hMem (Finset.notMem_empty _)
  rcases fd.nonDanglingValency_trichotomy (coreVertex fd hLeaf) with h | h | h <;> omega

/-- Every other block above the leaf has no surviving occurrence. -/
theorem nonDanglingValency_other {block : (data.vertexPartition leaf).Blocks}
    (hNe : block ≠ coreBlock fd hLeaf) :
    nonDanglingValency data (blockVertex data leaf block) = 0 := by
  have hLe : nonDanglingValency data (blockVertex data leaf block) ≤ 1 := by
    have := nonDanglingValency_le_card (blockVertex data leaf block)
    rw [(other_block_data fd hLeaf hNe).1] at this
    exact this
  rcases fd.nonDanglingValency_trichotomy (blockVertex data leaf block) with h | h | h <;>
    omega

/-! ### The fibre above the leaf edge -/

/-- The surviving source occurrences above the leaf edge. -/
noncomputable def leafSurvivors : Finset data.SourceEdge := by
  classical
  exact (Finset.univ : Finset data.SourceEdge).filter
    fun edge ↦ ¬ IsDangling data edge ∧ edge.1.1 = leafEdge hLeaf

omit [Fintype coordinate] [DecidableEq coordinate] fd in
theorem mem_leafSurvivors {edge : data.SourceEdge} :
    edge ∈ leafSurvivors (data := data) hLeaf ↔
      ¬ IsDangling data edge ∧ edge.1.1 = leafEdge hLeaf := by
  classical
  simp [leafSurvivors]

omit [Fintype coordinate] [DecidableEq coordinate] fd in
/-- Every occurrence above the leaf edge meets the block of its sheet. -/
theorem incident_blockVertex_of_target_eq {edge : data.SourceEdge}
    (hTarget : edge.1.1 = leafEdge hLeaf) :
    Incident data edge
      (blockVertex data leaf ((data.vertexPartition leaf).toBlock edge.1.2)) := by
  refine (incident_iff_target_mem_and_rel data edge _).mpr ⟨?_, ?_⟩
  · rw [blockVertex_target, hTarget]
    exact leafEdge_mem hLeaf
  · exact (data.vertexPartition leaf).rel_repr_left edge.1.2

/-- A surviving occurrence above the leaf edge meets `A_v`. -/
theorem incident_coreVertex_of_mem_leafSurvivors {edge : data.SourceEdge}
    (hMem : edge ∈ leafSurvivors (data := data) hLeaf) :
    Incident data edge (coreVertex fd hLeaf) := by
  classical
  obtain ⟨hSurvives, hTarget⟩ := (mem_leafSurvivors hLeaf).mp hMem
  set block := (data.vertexPartition leaf).toBlock edge.1.2 with hBlock
  have hIncident := incident_blockVertex_of_target_eq (data := data) hLeaf hTarget
  by_cases hCase : block = coreBlock fd hLeaf
  · rw [coreVertex, ← hCase, hBlock]
    exact hIncident
  · exfalso
    have hZero := nonDanglingValency_other fd hLeaf hCase
    have hMem' : edge ∈ (Finset.univ : Finset data.SourceEdge).filter
        fun item ↦ ¬ IsDangling data item ∧
          Incident data item (blockVertex data leaf block) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSurvives, hIncident⟩
    have hEmpty : ((Finset.univ : Finset data.SourceEdge).filter
        fun item ↦ ¬ IsDangling data item ∧
          Incident data item (blockVertex data leaf block)) = ∅ :=
      Finset.card_eq_zero.mp hZero
    rw [hEmpty] at hMem'
    exact absurd hMem' (Finset.notMem_empty _)

/-- Conversely, a surviving occurrence at `A_v` lies above the leaf edge. -/
theorem mem_leafSurvivors_of_incident_coreVertex {edge : data.SourceEdge}
    (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge (coreVertex fd hLeaf)) :
    edge ∈ leafSurvivors (data := data) hLeaf := by
  refine (mem_leafSurvivors hLeaf).mpr ⟨hSurvives, ?_⟩
  have hTargetMem := ((incident_iff_target_mem_and_rel data edge _).mp hIncident).1
  rw [coreVertex, blockVertex_target] at hTargetMem
  exact eq_leafEdge_of_mem hLeaf hTargetMem

/-- **Exactly two surviving occurrences lie above the leaf edge**, and they are
the two surviving occurrences at `A_v`. -/
theorem leafSurvivors_card : (leafSurvivors (data := data) hLeaf).card = 2 := by
  classical
  have hEq : leafSurvivors (data := data) hLeaf =
      (Finset.univ : Finset data.SourceEdge).filter
        (fun edge ↦ ¬ IsDangling data edge ∧
          Incident data edge (coreVertex fd hLeaf)) := by
    ext edge
    constructor
    · intro hMem
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ((mem_leafSurvivors hLeaf).mp hMem).1,
        incident_coreVertex_of_mem_leafSurvivors fd hLeaf hMem⟩
    · intro hMem
      obtain ⟨hSurvives, hIncident⟩ := (Finset.mem_filter.mp hMem).2
      exact mem_leafSurvivors_of_incident_coreVertex fd hLeaf hSurvives hIncident
  rw [hEq]
  exact nonDanglingValency_coreVertex fd hLeaf

/-- **Every occurrence above the leaf edge is unramified.** -/
theorem sourceEdgeIndex_eq_one_above_leaf {edge : data.SourceEdge}
    (hTarget : edge.1.1 = leafEdge hLeaf) : data.sourceEdgeIndex edge = 1 := by
  have hCard : (GluingDatum.incidentEdges
      (blockVertex data leaf ((data.vertexPartition leaf).toBlock edge.1.2)).1.1).card = 1 :=
    hLeaf
  exact sourceEdgeIndex_eq_one_of_target_leaf data fd.valid fd.noDanglingTargetFibres
    (blockVertex data leaf ((data.vertexPartition leaf).toBlock edge.1.2)) hCard
    (fd.changeMinimal _)
    ⟨edge, incident_blockVertex_of_target_eq (data := data) hLeaf hTarget⟩

/-- **The fibre above a leaf has `d - 1` vertices.** -/
theorem card_blocks_leaf :
    Fintype.card (data.vertexPartition leaf).Blocks + 1 = degree := by
  classical
  have hTotal : (∑ representative : Fin degree,
      if (data.vertexPartition leaf).repr representative = representative then
        ((data.vertexPartition leaf).blockCard representative : ℤ)
      else 0) = degree :=
    SheetPartition.sum_blockCard_representatives_eq_degree _ data.degree_pos
  have hSubtype : (∑ block : (data.vertexPartition leaf).Blocks,
      ((data.vertexPartition leaf).blockCard block.1 : ℤ)) =
      ∑ representative : Fin degree,
        if (data.vertexPartition leaf).repr representative = representative then
          ((data.vertexPartition leaf).blockCard representative : ℤ)
        else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun block _ ↦ block.1)
      (fun block _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, block.2⟩)
      (fun first _ second _ hEq ↦ Subtype.ext hEq)
      (fun representative hMem ↦
        ⟨⟨representative, (Finset.mem_filter.mp hMem).2⟩, Finset.mem_univ _, rfl⟩)
      (fun _ _ ↦ rfl)
  have hSplit := Finset.add_sum_erase
    (Finset.univ : Finset (data.vertexPartition leaf).Blocks)
    (fun block ↦ ((data.vertexPartition leaf).blockCard block.1 : ℤ))
    (Finset.mem_univ (coreBlock fd hLeaf))
  have hOthers : (∑ block ∈ (Finset.univ :
      Finset (data.vertexPartition leaf).Blocks).erase (coreBlock fd hLeaf),
      ((data.vertexPartition leaf).blockCard block.1 : ℤ)) =
      ((Finset.univ : Finset (data.vertexPartition leaf).Blocks).erase
        (coreBlock fd hLeaf)).card := by
    rw [Finset.sum_congr rfl fun block hblock ↦ ?_, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [(other_block_data fd hLeaf (Finset.mem_erase.mp hblock).1).2.1]
    norm_num
  have hErase : ((Finset.univ : Finset (data.vertexPartition leaf).Blocks).erase
      (coreBlock fd hLeaf)).card + 1 = Fintype.card (data.vertexPartition leaf).Blocks := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    have hPos : 0 < Fintype.card (data.vertexPartition leaf).Blocks :=
      Fintype.card_pos_iff.mpr ⟨coreBlock fd hLeaf⟩
    omega
  rw [hOthers, blockCard_coreBlock fd hLeaf] at hSplit
  have hFinal : ((2 : ℕ) : ℤ) +
      (((Finset.univ : Finset (data.vertexPartition leaf).Blocks).erase
        (coreBlock fd hLeaf)).card : ℤ) = (degree : ℤ) := by
    rw [hSplit, hSubtype]
    exact hTotal
  omega


/-! ### The stable row through `A_v` and the leaf column -/

/-- A surviving occurrence above the leaf edge, chosen once. -/
noncomputable def leafSurvivor : data.SourceEdge :=
  (fd.noDanglingTargetFibres (leafEdge hLeaf)).choose

theorem leafSurvivor_spec :
    (leafSurvivor fd hLeaf).1.1 = leafEdge hLeaf ∧
      ¬ IsDangling data (leafSurvivor fd hLeaf) :=
  (fd.noDanglingTargetFibres (leafEdge hLeaf)).choose_spec

theorem leafSurvivor_mem : leafSurvivor fd hLeaf ∈ leafSurvivors (data := data) hLeaf :=
  (mem_leafSurvivors hLeaf).mpr
    ⟨(leafSurvivor_spec fd hLeaf).2, (leafSurvivor_spec fd hLeaf).1⟩

/-- `h(v)`: the stable row interior to which `A_v` sits. -/
noncomputable def leafRow : coordinate :=
  fd.labelling.row (NonDanglingEdge.stablePath
    (⟨leafSurvivor fd hLeaf, (leafSurvivor_spec fd hLeaf).2⟩ : NonDanglingEdge data))

/-- **`A_v` is interior to a single stable row**: the two surviving occurrences
above the leaf edge are consecutive there, hence lie on one stable path. -/
theorem stablePath_eq_of_mem_leafSurvivors {edge : data.SourceEdge}
    (hMem : edge ∈ leafSurvivors (data := data) hLeaf)
    (hSurvives : ¬ IsDangling data edge) :
    NonDanglingEdge.stablePath (⟨edge, hSurvives⟩ : NonDanglingEdge data) =
      NonDanglingEdge.stablePath
        (⟨leafSurvivor fd hLeaf, (leafSurvivor_spec fd hLeaf).2⟩ : NonDanglingEdge data) := by
  by_cases hCase : edge = leafSurvivor fd hLeaf
  · exact congrArg NonDanglingEdge.stablePath (Subtype.ext hCase)
  · refine stablePath_eq_of_consecutive ⟨fun hEq ↦ hCase (congrArg Subtype.val hEq),
      coreVertex fd hLeaf, incident_coreVertex_of_mem_leafSurvivors fd hLeaf hMem,
      incident_coreVertex_of_mem_leafSurvivors fd hLeaf (leafSurvivor_mem fd hLeaf),
      nonDanglingValency_coreVertex fd hLeaf⟩

theorem row_eq_leafRow {edge : data.SourceEdge}
    (hMem : edge ∈ leafSurvivors (data := data) hLeaf)
    (hSurvives : ¬ IsDangling data edge) :
    fd.labelling.row (NonDanglingEdge.stablePath
      (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = leafRow fd hLeaf :=
  congrArg fd.labelling.row (stablePath_eq_of_mem_leafSurvivors fd hLeaf hMem hSurvives)

/-- The fibre of a row above the leaf edge: everything in row `h(v)`, nothing
in any other row. -/
theorem rowFibre_leafEdge (sourceRow : coordinate) :
    rowFibre fd.labelling sourceRow (leafEdge hLeaf) =
      if sourceRow = leafRow fd hLeaf then leafSurvivors (data := data) hLeaf else ∅ := by
  classical
  ext edge
  rw [mem_rowFibre]
  by_cases hCase : sourceRow = leafRow fd hLeaf
  · rw [if_pos hCase]
    constructor
    · rintro ⟨⟨hSurvives, _⟩, hTarget⟩
      exact (mem_leafSurvivors hLeaf).mpr ⟨hSurvives, hTarget⟩
    · intro hMem
      obtain ⟨hSurvives, hTarget⟩ := (mem_leafSurvivors hLeaf).mp hMem
      exact ⟨⟨hSurvives, by rw [row_eq_leafRow fd hLeaf hMem hSurvives, hCase]⟩, hTarget⟩
  · rw [if_neg hCase]
    simp only [Finset.notMem_empty, iff_false]
    rintro ⟨⟨hSurvives, hRow⟩, hTarget⟩
    exact hCase (hRow.symm.trans
      (row_eq_leafRow fd hLeaf ((mem_leafSurvivors hLeaf).mpr ⟨hSurvives, hTarget⟩) hSurvives))

/-- **The leaf column of the edge-length matrix is `2 · e_{h(v)}`.** -/
theorem matrix_leafEdge_column (sourceRow : coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation sourceRow
        (fd.labelling.targetEdge.symm (leafEdge hLeaf)) =
      if sourceRow = leafRow fd hLeaf then 2 else 0 := by
  classical
  rw [matrix_eq_sum_fibre, rowFibre_leafEdge fd hLeaf]
  by_cases hCase : sourceRow = leafRow fd hLeaf
  · rw [if_pos hCase, if_pos hCase]
    have hOnes : ∀ edge ∈ leafSurvivors (data := data) hLeaf,
        (1 : ℚ) / data.sourceEdgeIndex edge = 1 := by
      intro edge hEdge
      rw [sourceEdgeIndex_eq_one_above_leaf fd hLeaf
        ((mem_leafSurvivors hLeaf).mp hEdge).2]
      norm_num
    rw [Finset.sum_congr rfl hOnes, Finset.sum_const, nsmul_eq_mul, mul_one,
      leafSurvivors_card fd hLeaf]
    norm_num
  · rw [if_neg hCase, if_neg hCase, Finset.sum_empty]


/-- **`A_v` has valency two in the source graph.** -/
theorem vertex_degree_coreVertex :
    vertex_degree data.sourceGraph (coreVertex fd hLeaf) = 2 := by
  have hCast := vertex_degree_sourceGraph_eq_card_incidentSourceEdge data
    (coreVertex fd hLeaf)
  rw [(coreBlock_data fd hLeaf).1] at hCast
  omega

/-- **Both occurrences at `A_v` survive**: it has two incident occurrences and
surviving valency two. -/
theorem not_isDangling_of_incident_coreVertex {edge : data.SourceEdge}
    (hIncident : Incident data edge (coreVertex fd hLeaf)) :
    ¬ IsDangling data edge := by
  classical
  have hFilter := card_filter_not_isDangling_eq_nonDanglingValency data
    (coreVertex fd hLeaf)
  rw [nonDanglingValency_coreVertex fd hLeaf] at hFilter
  have hEq : ((Finset.univ : Finset (IncidentSourceEdge data (coreVertex fd hLeaf))).filter
      (fun item ↦ ¬ IsDangling data item.1)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hFilter, (coreBlock_data fd hLeaf).1])
  have hMem : (⟨edge, hIncident⟩ : IncidentSourceEdge data (coreVertex fd hLeaf)) ∈
      ((Finset.univ : Finset (IncidentSourceEdge data (coreVertex fd hLeaf))).filter
        (fun item ↦ ¬ IsDangling data item.1)) := by
    rw [hEq]
    exact Finset.mem_univ _
  exact (Finset.mem_filter.mp hMem).2


/-! ### The dangling leaves of the fibre, and the `d` occurrences above `t_v` -/

/-- Every occurrence at a non-core block above the leaf is dangling: the block
is a leaf of the source graph. -/
theorem isDangling_of_other_block {block : (data.vertexPartition leaf).Blocks}
    (hNe : block ≠ coreBlock fd hLeaf) {edge : data.SourceEdge}
    (hIncident : Incident data edge (blockVertex data leaf block)) :
    IsDangling data edge := by
  classical
  by_contra hSurvives
  have hMem : edge ∈ (Finset.univ : Finset data.SourceEdge).filter
      fun item ↦ ¬ IsDangling data item ∧
        Incident data item (blockVertex data leaf block) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSurvives, hIncident⟩
  have hEmpty : ((Finset.univ : Finset data.SourceEdge).filter
      fun item ↦ ¬ IsDangling data item ∧
        Incident data item (blockVertex data leaf block)) = ∅ :=
    Finset.card_eq_zero.mp (nonDanglingValency_other fd hLeaf hNe)
  rw [hEmpty] at hMem
  exact absurd hMem (Finset.notMem_empty _)

/-- Each of the other `d - 2` blocks above the leaf is a source vertex of graph
degree one. -/
theorem vertex_degree_other_block {block : (data.vertexPartition leaf).Blocks}
    (hNe : block ≠ coreBlock fd hLeaf) :
    vertex_degree data.sourceGraph (blockVertex data leaf block) = 1 := by
  have hCast := vertex_degree_sourceGraph_eq_card_incidentSourceEdge data
    (blockVertex data leaf block)
  rw [(other_block_data fd hLeaf hNe).1] at hCast
  omega

/-- **There are exactly `d` source occurrences above the leaf edge**, since all
of them are unramified. -/
theorem card_blocks_leafEdge :
    Fintype.card (data.edgePartition (leafEdge hLeaf)).Blocks = degree := by
  classical
  have hTotal : (∑ representative : Fin degree,
      if (data.edgePartition (leafEdge hLeaf)).repr representative = representative then
        ((data.edgePartition (leafEdge hLeaf)).blockCard representative : ℤ)
      else 0) = degree :=
    SheetPartition.sum_blockCard_representatives_eq_degree _ data.degree_pos
  have hSubtype : (∑ block : (data.edgePartition (leafEdge hLeaf)).Blocks,
      ((data.edgePartition (leafEdge hLeaf)).blockCard block.1 : ℤ)) =
      ∑ representative : Fin degree,
        if (data.edgePartition (leafEdge hLeaf)).repr representative = representative then
          ((data.edgePartition (leafEdge hLeaf)).blockCard representative : ℤ)
        else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun block _ ↦ block.1)
      (fun block _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, block.2⟩)
      (fun first _ second _ hEq ↦ Subtype.ext hEq)
      (fun representative hMem ↦
        ⟨⟨representative, (Finset.mem_filter.mp hMem).2⟩, Finset.mem_univ _, rfl⟩)
      (fun _ _ ↦ rfl)
  have hOnes : ∀ block : (data.edgePartition (leafEdge hLeaf)).Blocks,
      ((data.edgePartition (leafEdge hLeaf)).blockCard block.1 : ℤ) = 1 := by
    intro block
    have hIndex : data.sourceEdgeIndex
        (⟨(leafEdge hLeaf, block.1), block.2⟩ : data.SourceEdge) = 1 :=
      sourceEdgeIndex_eq_one_above_leaf fd hLeaf rfl
    rw [show ((data.edgePartition (leafEdge hLeaf)).blockCard block.1) =
      data.sourceEdgeIndex (⟨(leafEdge hLeaf, block.1), block.2⟩ : data.SourceEdge) from rfl,
      hIndex]
    norm_num
  rw [Finset.sum_congr rfl fun block _ ↦ hOnes block, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hSubtype
  rw [← hSubtype] at hTotal
  exact_mod_cast hTotal


end Leaf

/-! ## Distinct leaves carry distinct stable rows -/

section Injective

variable {first second : target.V}

include fd

/-- **`v ↦ h(v)` is injective** as soon as distinct leaves carry distinct leaf
edges: two leaves on one stable row would make two columns of the edge-length
matrix equal, contradicting nonsingularity. -/
theorem leafRow_ne (hFirst : IsLeafVertex target first)
    (hSecond : IsLeafVertex target second)
    (hEdgeNe : leafEdge hFirst ≠ leafEdge hSecond) :
    leafRow fd hFirst ≠ leafRow fd hSecond := by
  intro hRow
  apply fd.det_ne_zero
  refine Matrix.det_zero_of_column_eq
    (i := fd.labelling.targetEdge.symm (leafEdge hFirst))
    (j := fd.labelling.targetEdge.symm (leafEdge hSecond))
    (fun hEq ↦ hEdgeNe (fd.labelling.targetEdge.symm.injective hEq)) ?_
  intro sourceRow
  rw [matrix_leafEdge_column fd hFirst, matrix_leafEdge_column fd hSecond, hRow]

omit [Fintype coordinate] [DecidableEq coordinate] fd in
/-- Distinct leaves carry distinct leaf edges as soon as no target edge joins
two leaves; this is the combinatorial hypothesis `NoLeafToLeafEdge` that
`DraismaVargasCount.Multiplicity` already isolates. -/
theorem leafEdge_ne_of_noLeafToLeafEdge (hTarget : NoLeafToLeafEdge target)
    (hFirst : IsLeafVertex target first) (hSecond : IsLeafVertex target second)
    (hNe : first ≠ second) : leafEdge hFirst ≠ leafEdge hSecond := by
  intro hEdge
  have h1 := fst_eq_or_snd_eq_of_mem_incidentEdges (leafEdge_mem hFirst)
  have h2 := fst_eq_or_snd_eq_of_mem_incidentEdges (leafEdge_mem hSecond)
  rw [← hEdge] at h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact hNe (h1.symm.trans h2)
  · exact hTarget _ (by rw [h1]; exact hFirst) (by rw [h2]; exact hSecond)
  · exact hTarget _ (by rw [h2]; exact hSecond) (by rw [h1]; exact hFirst)
  · exact hNe (h1.symm.trans h2)

/-- **`v ↦ h(v)` is injective on the leaves of a target without leaf-to-leaf
edges.** -/
theorem leafRow_ne_of_noLeafToLeafEdge (hTarget : NoLeafToLeafEdge target)
    (hFirst : IsLeafVertex target first) (hSecond : IsLeafVertex target second)
    (hNe : first ≠ second) : leafRow fd hFirst ≠ leafRow fd hSecond :=
  leafRow_ne fd hFirst hSecond
    (leafEdge_ne_of_noLeafToLeafEdge hTarget hFirst hSecond hNe)

end Injective


/-! ## Non-vacuity: the caterpillar of loops -/

section Witness

open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CaterpillarDatum

/-- The tip of the first lollipop is a leaf of `T^CL_g`. -/
theorem isLeafVertex_catTip (m : ℕ) :
    IsLeafVertex (catTree m) (⟨1, by omega⟩ : Fin (6 * m + 4)) :=
  (Caterpillar.isLeafVertex_catTree_iff m _).mpr (Or.inl rfl)

/-- **Non-vacuity of the leaf-fibre package**: at the first lollipop tip of the
caterpillar of loops the leaf column of the edge-length matrix is `2 e_{h(v)}`,
uniformly in the genus `g = 2m + 2`. -/
example (m : ℕ) (sourceRow : Fin (6 * m + 3)) :
    GluingDatum.LengthMatrixPresentation.matrix
        (CaterpillarRows.fullDim m).labelling.presentation sourceRow
        ((CaterpillarRows.fullDim m).labelling.targetEdge.symm
          (leafEdge (isLeafVertex_catTip m))) =
      if sourceRow = leafRow (CaterpillarRows.fullDim m) (isLeafVertex_catTip m) then 2
      else 0 :=
  matrix_leafEdge_column (CaterpillarRows.fullDim m) (isLeafVertex_catTip m) sourceRow

/-- The same datum inhabits the counting half: the leaf fibre has `d - 1`
blocks, `A_v` has local degree two, and there are `d` occurrences above the
leaf edge. -/
example (m : ℕ) :
    Fintype.card ((caterpillarDatum m).vertexPartition
        (⟨1, by omega⟩ : Fin (6 * m + 4))).Blocks + 1 = m + 2 ∧
      ((caterpillarDatum m).vertexPartition (⟨1, by omega⟩ : Fin (6 * m + 4))).blockCard
        (coreBlock (CaterpillarRows.fullDim m) (isLeafVertex_catTip m)).1 = 2 ∧
      Fintype.card ((caterpillarDatum m).edgePartition
        (leafEdge (isLeafVertex_catTip m))).Blocks = m + 2 :=
  ⟨card_blocks_leaf (CaterpillarRows.fullDim m) (isLeafVertex_catTip m),
    blockCard_coreBlock (CaterpillarRows.fullDim m) (isLeafVertex_catTip m),
    card_blocks_leafEdge (CaterpillarRows.fullDim m) (isLeafVertex_catTip m)⟩

end Witness


end DraismaVargas.Count.LeafFibre
