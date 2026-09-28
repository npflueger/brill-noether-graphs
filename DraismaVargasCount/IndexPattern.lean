import DraismaVargasCount.LeafFibre

/-!
# The index pattern along a stable row, from nonsingularity alone

**Source.**  Vargas, Part II (arXiv:2609.09109), `proposition-at-most-two-weights`, and
Draisma--Vargas Part I (arXiv:1909.12924), `lemma-change-zero` (the column identity).
This module gives a direct proof, from full rank, of the index pattern along a stable row
that Part II states as `proposition-at-most-two-weights`; Part II proves that proposition
by contracting and regrowing, and that argument is not followed here.

Everything is derived from full rank (`det A_φ ≠ 0`), change-minimality,
`lem-rphi-nd`, dangling-no-glue and no-return; no limit, no appendix, no Part I
case work.

## What is proved

* `sourceEdgeIndex_add_sourceEdgeIndex` — **the local index identity**
  `m(e_a) + m(e_{a+1}) = 2 m(A) - r_φ(A)` at every source vertex `A` of
  surviving valency two, *uniformly in the valency of the target vertex
  below*.  It is the identity `r(A_a) = |m(e_a) - m(e_{a+1})|` before the case
  split, and it yields `prop-local`(r0)
  (`sourceEdgeIndex_eq_of_localRamification_eq_zero`: an unramified vertex
  carries its local degree in both directions) and
  `sourceEdgeIndex_sub_eq_one_of_transition` (at a transition the two indices
  differ by exactly one).
* `target_ne_of_transition` — **no return at a transition vertex**: the two
  surviving occurrences at a ramified surviving-valency-two vertex lie above
  the two *different* incident target occurrences.  Derived here, not assumed.
* `matrix_sub_eq_of_transition` — **the column relation**:
  `col(t_a) - col(t_{a+1}) = (1/m(e_a) - 1/m(e_{a+1})) · e_h`.  Every block
  above the divalent target vertex other than the transition vertex is
  unramified (change-minimality), so it contributes equally to both columns in
  its own row; the transport that shows this is the one
  `StableLocalProperties.matrix_column_eq_of_divalent_of_surviving_localRamification_zero`
  uses, refitted so that one block may carry `r_φ = 1`.
* `det_eq_zero_of_two_column_relations`, `det_eq_zero_of_column_relation_and_leaf`
  — **the exclusion**, as pure linear algebra over `ℚ`: a vanishing
  nonzero combination of columns forces `det = 0`
  (`Matrix.exists_mulVec_eq_zero_iff`).
* `sourceEdgeIndex_eq_of_consecutive_on_leafRow` and
  `sourceEdgeIndex_eq_one_of_row_eq_leafRow` — **a leaf-passing row has all
  indices one**, unconditionally.  A transition on such a row would combine
  with the leaf column `2 e_{h(v)}` of `Count.LeafFibre` into a vanishing
  combination of distinct columns; the index is then constant along the row by
  the stable-path closure (`W4StableSource.eqvGen_iff_of_closed`) and equals
  `1` at the two occurrences above the leaf edge.
* `not_two_transitions_on_one_row` — **two transitions on one row are
  impossible**, given that they do not use the same unordered pair of target
  occurrences.

## What is not proved here

* **The separation hypothesis `hPairs` of `not_two_transitions_on_one_row`.**
  The linear algebra cannot exclude one configuration: two distinct divalent
  target vertices carrying transitions on the same *unordered pair* of target
  occurrences.  That configuration is a cycle of the target, so `genus target
  = 0` rules it out, but the derivation needs the walk structure of a stable
  row (the image of a leaf-avoiding row is a geodesic, `φ` injective on its edges),
  which is **not** formalized here.  In the paper's own argument the same input
  appears as "the row is a geodesic".  It is discharged from the ordered walk of a
  row in `Count.RowWalk` (`RowWalk.not_two_transitions_on_one_row_of_simpleTarget`).
  The leaf-passing statements above are **free of it**.
* **The global phrasing "a leaf-avoiding row has indices `k` then `k+1`".**
  What is proved is the pointwise content: every non-transition vertex of the
  row keeps the index, and every transition changes it by exactly one, and two
  transitions are excluded (modulo `hPairs`).  Turning that into "the row is
  `k^μ (k+1)^{ν-μ}` up to reversal" again needs the ordered walk.
* The hairpin description of a leaf-passing row (`t_v` traversed exactly twice, the two
  halves geodesics) -- walk structure again.
* Nothing here is conditional on integrality, on the genus, or on the degree.

## Consumers

`Count.EdgeDenominator` consumes `sourceEdgeIndex_eq_one_of_row_eq_leafRow` for case (a)
of Part II's `lemma-edge-deno` and `sourceEdgeIndex_sub_eq_one_of_transition` for case (c);
integrality of the multiplicity (`Count.Integrality`) and the balancing at trivalent walls
consume the index pattern through it.
-/

namespace DraismaVargas.Count.IndexPattern

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.GluingDatum.LengthMatrixPresentation
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableLocalProperties
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.LeafFibre

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-! ## Local algebra above a divalent target vertex -/

/-- If a coarse block receives a single fine block above one incident target
occurrence, then every sheet of the coarse block names the same source
occurrence there.  This is the star-free form of
`W4StableSource.sourceEdge_eq_anchor_of_blockCountWithin_eq_one`. -/
theorem sourceEdge_eq_anchor (vertex : data.SourceVertex) {edge : target.edges}
    (hMem : edge ∈ GluingDatum.incidentEdges vertex.1.1) {sheet : Fin degree}
    (hSheet : (data.vertexPartition vertex.1.1).Rel vertex.1.2 sheet)
    (hCount : (data.edgePartition edge).blockCountWithin
      (data.vertexPartition vertex.1.1) vertex.1.2 = 1) :
    data.sourceEdge edge sheet = data.sourceEdge edge vertex.1.2 := by
  have hBlocks : (data.edgePartition edge).block vertex.1.2 =
      (data.vertexPartition vertex.1.1).block vertex.1.2 :=
    (data.edgePartition edge).block_eq_of_refines_of_blockCountWithin_eq_one
      (data.vertexPartition vertex.1.1) (refines_of_mem_incidentEdges data hMem)
      vertex.1.2 hCount
  have hSheetMem : sheet ∈ (data.vertexPartition vertex.1.1).block vertex.1.2 :=
    ((data.vertexPartition vertex.1.1).mem_block_iff vertex.1.2 sheet).2 hSheet
  rw [← hBlocks] at hSheetMem
  have hFineRel : (data.edgePartition edge).Rel vertex.1.2 sheet :=
    ((data.edgePartition edge).mem_block_iff vertex.1.2 sheet).1 hSheetMem
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact hFineRel.symm

/-- **Above a divalent target vertex the local ramification counts the excess
source degree**: `r_φ(A) = deg(A) - 2`. -/
theorem localRamification_add_two (vertex : data.SourceVertex)
    (hDivalent : (GluingDatum.incidentEdges vertex.1.1).card = 2) :
    data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ + 2 =
      (Fintype.card (IncidentSourceEdge data vertex) : ℤ) := by
  have hFormula := localRamification_eq_vertex_degree data vertex
  rw [vertex_degree_sourceGraph_eq_card_incidentSourceEdge, hDivalent] at hFormula
  have hZero : ((2 : ℕ) : ℤ) - 2 = 0 := by norm_num
  rw [hZero, mul_zero] at hFormula
  omega

/-- The number of incident source occurrences above a divalent target
vertex splits over the two incident target occurrences. -/
theorem card_incidentSourceEdge_eq_pair (vertex : data.SourceVertex)
    {first second : target.edges} (hNe : first ≠ second)
    (hFirst : first ∈ GluingDatum.incidentEdges vertex.1.1)
    (hSecond : second ∈ GluingDatum.incidentEdges vertex.1.1)
    (hDivalent : (GluingDatum.incidentEdges vertex.1.1).card = 2) :
    Fintype.card (IncidentSourceEdge data vertex) =
      (data.edgePartition first).blockCountWithin
          (data.vertexPartition vertex.1.1) vertex.1.2 +
        (data.edgePartition second).blockCountWithin
          (data.vertexPartition vertex.1.1) vertex.1.2 := by
  classical
  have hPair : GluingDatum.incidentEdges vertex.1.1 = {first, second} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro edge hEdge
      rcases Finset.mem_insert.mp hEdge with hCase | hCase
      · rw [hCase]; exact hFirst
      · rw [Finset.mem_singleton.mp hCase]; exact hSecond
    · rw [hDivalent, Finset.card_pair hNe]
  rw [card_incidentSourceEdge_eq_sum_blockCountWithin, hPair, Finset.sum_pair hNe]

/-- `blockCountWithin` never exceeds the coarse block's cardinality. -/
theorem blockCountWithin_le_blockCard (fine coarse : SheetPartition degree)
    (sheet : Fin degree) :
    fine.blockCountWithin coarse sheet ≤ coarse.blockCard sheet :=
  Finset.card_image_le

/-- The block of the sheet of an incident occurrence is the block of the
vertex it meets. -/
theorem toBlock_eq_of_incident {vertex : data.SourceVertex} {edge : data.SourceEdge}
    (hIncident : Incident data edge vertex) :
    (data.vertexPartition vertex.1.1).toBlock edge.1.2 = ⟨vertex.1.2, vertex.2⟩ := by
  have hRel := ((incident_iff_target_mem_and_rel data edge vertex).mp hIncident).2
  apply Subtype.ext
  show (data.vertexPartition vertex.1.1).repr edge.1.2 = vertex.1.2
  exact hRel.symm.trans vertex.2

theorem target_mem_of_incident {vertex : data.SourceVertex} {edge : data.SourceEdge}
    (hIncident : Incident data edge vertex) :
    edge.1.1 ∈ GluingDatum.incidentEdges vertex.1.1 :=
  ((incident_iff_target_mem_and_rel data edge vertex).mp hIncident).1

/-- **A block of vanishing ramification above a divalent target vertex is
unramified in every direction**: all its incident occurrences carry its own
local degree. -/
theorem sourceEdgeIndex_eq_blockCard_of_localRamification_zero
    {vertex : data.SourceVertex}
    (hDivalent : (GluingDatum.incidentEdges vertex.1.1).card = 2)
    (hZero : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 0)
    {edge : data.SourceEdge} (hIncident : Incident data edge vertex) :
    data.sourceEdgeIndex edge =
      (data.vertexPartition vertex.1.1).blockCard vertex.1.2 := by
  have hBlock := toBlock_eq_of_incident hIncident
  have hZero' : data.localRamification vertex.1.1
      ((data.vertexPartition vertex.1.1).toBlock edge.1.2) = 0 := by
    rw [hBlock]; exact hZero
  have hIndex := sourceEdgeIndex_eq_of_divalent_localRamification_zero data
    vertex.1.1 hDivalent edge.1.2 hZero' edge.1.1 (target_mem_of_incident hIncident)
  rw [GluingDatum.sourceEdge_self] at hIndex
  rw [hIndex]
  show ((data.vertexPartition vertex.1.1).block edge.1.2).card = _
  rw [(data.vertexPartition vertex.1.1).block_eq_of_rel
    (((incident_iff_target_mem_and_rel data edge vertex).mp hIncident).2.symm)]
  rfl

section FullDim

variable (fd : FullDimensionalSourcePresentation data coordinate)

include fd

/-- A divalent target vertex of a full-dimensional datum carries change one. -/
theorem targetChange_divalent {wall : target.V}
    (hDivalent : (GluingDatum.incidentEdges wall).card = 2) :
    data.targetChange wall = 1 := by
  have h := fd.targetExcess_eq_zero wall
  unfold GluingDatum.targetExcess at h
  rw [hDivalent] at h
  omega

/-- Local ramification above a divalent target vertex is at most one. -/
theorem localRamification_le_one {wall : target.V}
    (hDivalent : (GluingDatum.incidentEdges wall).card = 2)
    (block : (data.vertexPartition wall).Blocks) :
    data.localRamification wall block ≤ 1 := by
  have hSum : (∑ item : (data.vertexPartition wall).Blocks,
      data.localRamification wall item) = 1 := targetChange_divalent fd hDivalent
  have hNonneg : ∀ item : (data.vertexPartition wall).Blocks,
      0 ≤ data.localRamification wall item := fun item ↦
    data.localRamification_nonneg wall (fd.valid.2 wall) item
  have hLe : data.localRamification wall block ≤
      ∑ item : (data.vertexPartition wall).Blocks, data.localRamification wall item :=
    Finset.single_le_sum (fun item _ ↦ hNonneg item) (Finset.mem_univ _)
  omega

/-- **One transition per divalent target vertex**: a block with `r_φ = 1`
exhausts the change there, so every other block is unramified. -/
theorem localRamification_eq_zero_of_ne {wall : target.V}
    (hDivalent : (GluingDatum.incidentEdges wall).card = 2)
    {ramified block : (data.vertexPartition wall).Blocks}
    (hRamified : data.localRamification wall ramified = 1)
    (hNe : block ≠ ramified) : data.localRamification wall block = 0 := by
  classical
  have hSum : (∑ item : (data.vertexPartition wall).Blocks,
      data.localRamification wall item) = 1 := targetChange_divalent fd hDivalent
  have hNonneg : ∀ item : (data.vertexPartition wall).Blocks,
      0 ≤ data.localRamification wall item := fun item ↦
    data.localRamification_nonneg wall (fd.valid.2 wall) item
  have hSplit := Finset.sum_erase_add
    (Finset.univ : Finset (data.vertexPartition wall).Blocks)
    (fun item ↦ data.localRamification wall item) (Finset.mem_univ ramified)
  rw [hRamified, hSum] at hSplit
  have hEraseSum : (∑ other ∈ (Finset.univ :
      Finset (data.vertexPartition wall).Blocks).erase ramified,
      data.localRamification wall other) = 0 := by omega
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun other _ ↦ hNonneg other)).mp hEraseSum block
    (Finset.mem_erase.mpr ⟨hNe, Finset.mem_univ _⟩)

end FullDim


/-! ## The local index identity at a surviving-valency-two vertex -/

section IndexSum

variable (fd : FullDimensionalSourcePresentation data coordinate)

include fd

/-- **`m(e_a) + m(e_{a+1}) = 2 m(A) - r_φ(A)`.**  At a source vertex of
surviving valency two the two surviving indices are pinned by the local degree
and the local ramification, uniformly in the valency of the target vertex
below: the balancing condition gives `Σ m(e) = val(x) · m(A)` over all
incident occurrences, dangling-no-glue makes the `deg(A) - 2` dangling ones
contribute `1` each, and `lem-rphi-nd` turns `deg(A)` into `r_φ(A)`.  This is
the identity `r(A_a) = |m(e_a) - m(e_{a+1})|` before the case split. -/
theorem sourceEdgeIndex_add_sourceEdgeIndex {vertex : data.SourceVertex}
    (hValency : nonDanglingValency data vertex = 2)
    {first second : data.SourceEdge}
    (hFirstSurvives : ¬ IsDangling data first) (hFirstIncident : Incident data first vertex)
    (hSecondSurvives : ¬ IsDangling data second)
    (hSecondIncident : Incident data second vertex) (hNe : first ≠ second) :
    (data.sourceEdgeIndex first : ℤ) + (data.sourceEdgeIndex second : ℤ) =
      2 * ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) -
        data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ := by
  classical
  set incident := (Finset.univ : Finset (IncidentSourceEdge data vertex)) with hIncidentSet
  set surviving := incident.filter (fun edge ↦ ¬ IsDangling data edge.1) with hSurviving
  have hSurvivingCard : surviving.card = 2 := by
    rw [hSurviving, hIncidentSet, card_filter_not_isDangling_eq_nonDanglingValency, hValency]
  set firstIncident : IncidentSourceEdge data vertex := ⟨first, hFirstIncident⟩
    with hFirstIncidentDef
  set secondIncident : IncidentSourceEdge data vertex := ⟨second, hSecondIncident⟩
    with hSecondIncidentDef
  have hFirstMemS : firstIncident ∈ surviving :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFirstSurvives⟩
  have hSecondMemS : secondIncident ∈ surviving :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSecondSurvives⟩
  have hPairNe : secondIncident ≠ firstIncident :=
    fun hEq ↦ hNe (congrArg Subtype.val hEq).symm
  have hEraseCard : (surviving.erase firstIncident).card = 1 := by
    rw [Finset.card_erase_of_mem hFirstMemS, hSurvivingCard]
  obtain ⟨only, hOnly⟩ := Finset.card_eq_one.mp hEraseCard
  have hSecondErase : secondIncident ∈ surviving.erase firstIncident :=
    Finset.mem_erase.mpr ⟨hPairNe, hSecondMemS⟩
  rw [hOnly, Finset.mem_singleton] at hSecondErase
  have hSurvivingSum : (∑ edge ∈ surviving, (data.sourceEdgeIndex edge.1 : ℤ)) =
      (data.sourceEdgeIndex first : ℤ) + (data.sourceEdgeIndex second : ℤ) := by
    rw [← Finset.add_sum_erase _ _ hFirstMemS, hOnly, ← hSecondErase,
      Finset.sum_singleton]
  have hDanglingSum : (∑ edge ∈ incident.filter
      (fun edge ↦ ¬ ¬ IsDangling data edge.1), (data.sourceEdgeIndex edge.1 : ℤ)) =
      ((incident.filter (fun edge ↦ ¬ ¬ IsDangling data edge.1)).card : ℤ) := by
    rw [Finset.sum_congr rfl fun edge hEdge ↦ ?_, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hDangling := (Finset.mem_filter.mp hEdge).2
    rw [fd.danglingEdgeNoGlue edge.1 (not_not.mp hDangling)]
    norm_num
  have hCardSplit := Finset.card_filter_add_card_filter_not
    (s := incident) (p := fun edge ↦ ¬ IsDangling data edge.1)
  have hSumSplit := Finset.sum_filter_add_sum_filter_not incident
    (fun edge ↦ ¬ IsDangling data edge.1)
    (fun edge ↦ (data.sourceEdgeIndex edge.1 : ℤ))
  have hBalance := sum_sourceEdgeIndex_incident data vertex
  have hRam := localRamification_eq_vertex_degree data vertex
  rw [vertex_degree_sourceGraph_eq_card_incidentSourceEdge] at hRam
  have hCardUniv : incident.card = Fintype.card (IncidentSourceEdge data vertex) := by
    rw [hIncidentSet, Finset.card_univ]
  rw [hSurvivingSum, hDanglingSum] at hSumSplit
  rw [hSurviving] at hSurvivingCard
  rw [hCardUniv] at hCardSplit
  have hBalance' : (∑ edge ∈ incident, (data.sourceEdgeIndex edge.1 : ℤ)) =
      ((GluingDatum.incidentEdges vertex.1.1).card : ℤ) *
        ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) := by
    rw [hIncidentSet]
    exact hBalance
  rw [hBalance'] at hSumSplit
  have hCardCast : ((Fintype.card (IncidentSourceEdge data vertex) : ℕ) : ℤ) =
      (surviving.card : ℤ) +
        ((incident.filter (fun edge ↦ ¬ ¬ IsDangling data edge.1)).card : ℤ) := by
    rw [hSurviving]
    exact_mod_cast hCardSplit.symm
  rw [hSurvivingCard] at hCardCast
  have hValCast : (((GluingDatum.incidentEdges vertex.1.1).card : ℕ) : ℤ) =
      ((GluingDatum.incidentEdges vertex.1.1).card : ℤ) := rfl
  nlinarith [hSumSplit, hCardCast, hRam, hValCast]

end IndexSum


/-! ## Exclusion: a column relation kills the determinant -/

section Exclusion

/-- A nonzero rational combination of columns that vanishes makes the
determinant vanish. -/
theorem det_eq_zero_of_column_relation (matrix : Matrix coordinate coordinate ℚ)
    (weight : coordinate → ℚ) (hWeight : weight ≠ 0)
    (hRelation : ∀ sourceRow, ∑ column, matrix sourceRow column * weight column = 0) :
    matrix.det = 0 :=
  Matrix.exists_mulVec_eq_zero_iff.mp ⟨weight, hWeight, funext hRelation⟩

/-- The coefficient vector `cB (δ_p - δ_q) - cA (δ_r - δ_s)`. -/
noncomputable def pairWeight (coefficientA coefficientB : ℚ)
    (p q r s : coordinate) : coordinate → ℚ := fun column ↦
  coefficientB * ((if column = p then 1 else 0) - (if column = q then 1 else 0)) -
    coefficientA * ((if column = r then 1 else 0) - (if column = s then 1 else 0))

theorem sum_mul_pairWeight (matrix : Matrix coordinate coordinate ℚ)
    (coefficientA coefficientB : ℚ) (p q r s : coordinate) (sourceRow : coordinate) :
    (∑ column, matrix sourceRow column *
        pairWeight coefficientA coefficientB p q r s column) =
      coefficientB * (matrix sourceRow p - matrix sourceRow q) -
        coefficientA * (matrix sourceRow r - matrix sourceRow s) := by
  have hSingle : ∀ x : coordinate,
      (∑ column, matrix sourceRow column * (if column = x then (1 : ℚ) else 0)) =
        matrix sourceRow x := by
    intro x
    rw [Finset.sum_congr rfl fun column _ ↦ (mul_ite _ _ _ _).trans
      (by rw [mul_one, mul_zero])]
    exact Finset.sum_ite_eq' Finset.univ x (fun column ↦ matrix sourceRow column) ▸ by
      simp
  have hExpand : ∀ column : coordinate,
      matrix sourceRow column * pairWeight coefficientA coefficientB p q r s column =
        coefficientB * (matrix sourceRow column * (if column = p then (1 : ℚ) else 0)) -
          coefficientB * (matrix sourceRow column * (if column = q then (1 : ℚ) else 0)) -
          (coefficientA * (matrix sourceRow column * (if column = r then (1 : ℚ) else 0)) -
            coefficientA *
              (matrix sourceRow column * (if column = s then (1 : ℚ) else 0))) := by
    intro column
    unfold pairWeight
    ring
  rw [Finset.sum_congr rfl fun column _ ↦ hExpand column]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    hSingle, hSingle, hSingle, hSingle]
  ring

/-- **Two transitions on one stable row contradict nonsingularity.**  The two
column relations have proportional right-hand sides, so a nonzero combination
of four columns vanishes.  The hypothesis `hPairs` — the two transitions do not
use the *same pair* of target occurrences — is exactly what is needed: if they
did, the combination could cancel, and that configuration is a cycle of the
target, not a row of a geodesic. -/
theorem det_eq_zero_of_two_column_relations
    (matrix : Matrix coordinate coordinate ℚ) {sourceRow p q r s : coordinate}
    {coefficientA coefficientB : ℚ}
    (hB : coefficientB ≠ 0) (hpq : p ≠ q) (hrs : r ≠ s)
    (hPairs : ¬ ((p = r ∧ q = s) ∨ (p = s ∧ q = r)))
    (hRelationA : ∀ row, matrix row p - matrix row q =
      if row = sourceRow then coefficientA else 0)
    (hRelationB : ∀ row, matrix row r - matrix row s =
      if row = sourceRow then coefficientB else 0) :
    matrix.det = 0 := by
  classical
  refine det_eq_zero_of_column_relation matrix
    (pairWeight coefficientA coefficientB p q r s) ?_ ?_
  · intro hWeightZero
    have hp := congrFun hWeightZero p
    have hq := congrFun hWeightZero q
    unfold pairWeight at hp hq
    rw [if_pos (rfl : p = p), if_neg hpq] at hp
    rw [if_neg (Ne.symm hpq), if_pos (rfl : q = q)] at hq
    simp only [Pi.zero_apply] at hp hq
    by_cases hpr : p = r
    · have hps : ¬ (p = s) := fun hEq ↦ hrs (hpr.symm.trans hEq)
      have hqr : ¬ (q = r) := fun hEq ↦ hpq (hpr.trans hEq.symm)
      rw [if_neg hqr] at hq
      by_cases hqs : q = s
      · exact hPairs (Or.inl ⟨hpr, hqs⟩)
      · rw [if_neg hqs] at hq
        exact hB (by linarith)
    · by_cases hps : p = s
      · have hqs : ¬ (q = s) := fun hEq ↦ hpq (hps.trans hEq.symm)
        rw [if_neg hqs] at hq
        by_cases hqr : q = r
        · exact hPairs (Or.inr ⟨hps, hqr⟩)
        · rw [if_neg hqr] at hq
          exact hB (by linarith)
      · rw [if_neg hpr, if_neg hps] at hp
        exact hB (by linarith)
  · intro row
    rw [sum_mul_pairWeight, hRelationA, hRelationB]
    by_cases hCase : row = sourceRow
    · rw [if_pos hCase, if_pos hCase]; ring
    · rw [if_neg hCase, if_neg hCase]; ring

/-- The coefficient vector `2 (δ_p - δ_q) - c δ_t`. -/
noncomputable def leafWeight (coefficient : ℚ) (p q leafColumn : coordinate) :
    coordinate → ℚ := fun column ↦
  2 * ((if column = p then 1 else 0) - (if column = q then 1 else 0)) -
    coefficient * (if column = leafColumn then 1 else 0)

theorem sum_mul_leafWeight (matrix : Matrix coordinate coordinate ℚ)
    (coefficient : ℚ) (p q leafColumn : coordinate) (sourceRow : coordinate) :
    (∑ column, matrix sourceRow column * leafWeight coefficient p q leafColumn column) =
      2 * (matrix sourceRow p - matrix sourceRow q) -
        coefficient * matrix sourceRow leafColumn := by
  have hSingle : ∀ x : coordinate,
      (∑ column, matrix sourceRow column * (if column = x then (1 : ℚ) else 0)) =
        matrix sourceRow x := by
    intro x
    rw [Finset.sum_congr rfl fun column _ ↦ (mul_ite _ _ _ _).trans
      (by rw [mul_one, mul_zero])]
    exact Finset.sum_ite_eq' Finset.univ x (fun column ↦ matrix sourceRow column) ▸ by
      simp
  have hExpand : ∀ column : coordinate,
      matrix sourceRow column * leafWeight coefficient p q leafColumn column =
        2 * (matrix sourceRow column * (if column = p then (1 : ℚ) else 0)) -
          2 * (matrix sourceRow column * (if column = q then (1 : ℚ) else 0)) -
          coefficient *
            (matrix sourceRow column * (if column = leafColumn then (1 : ℚ) else 0)) := by
    intro column
    unfold leafWeight
    ring
  rw [Finset.sum_congr rfl fun column _ ↦ hExpand column]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hSingle, hSingle, hSingle]
  ring

/-- **A transition on a leaf-passing row contradicts nonsingularity.**  Here no
separation hypothesis is needed: the leaf column is `2 e_h`, and whichever of
the two transition columns happens to be the leaf column, the other one still
carries the coefficient `±2 ≠ 0`. -/
theorem det_eq_zero_of_column_relation_and_leaf
    (matrix : Matrix coordinate coordinate ℚ) {sourceRow p q leafColumn : coordinate}
    {coefficient : ℚ} (hpq : p ≠ q)
    (hRelation : ∀ row, matrix row p - matrix row q =
      if row = sourceRow then coefficient else 0)
    (hLeafColumn : ∀ row, matrix row leafColumn =
      if row = sourceRow then 2 else 0) :
    matrix.det = 0 := by
  classical
  refine det_eq_zero_of_column_relation matrix
    (leafWeight coefficient p q leafColumn) ?_ ?_
  · intro hWeightZero
    have hp := congrFun hWeightZero p
    have hq := congrFun hWeightZero q
    unfold leafWeight at hp hq
    rw [if_pos (rfl : p = p), if_neg hpq] at hp
    rw [if_neg (Ne.symm hpq), if_pos (rfl : q = q)] at hq
    simp only [Pi.zero_apply] at hp hq
    by_cases hpLeaf : p = leafColumn
    · have hqLeaf : ¬ (q = leafColumn) := fun hEq ↦ hpq (hpLeaf.trans hEq.symm)
      rw [if_neg hqLeaf] at hq
      norm_num at hq
    · rw [if_neg hpLeaf] at hp
      norm_num at hp
  · intro row
    rw [sum_mul_leafWeight, hRelation, hLeafColumn]
    by_cases hCase : row = sourceRow
    · rw [if_pos hCase, if_pos hCase]; ring
    · rw [if_neg hCase, if_neg hCase]; ring


end Exclusion


/-! ## Transition vertices -/

/-- At a vertex of surviving valency two, two distinct surviving incident
occurrences exhaust the survivors. -/
theorem eq_or_eq_of_nonDanglingValency_two {vertex : data.SourceVertex}
    (hValency : nonDanglingValency data vertex = 2)
    {first second edge : data.SourceEdge}
    (hFirstSurvives : ¬ IsDangling data first) (hFirstIncident : Incident data first vertex)
    (hSecondSurvives : ¬ IsDangling data second)
    (hSecondIncident : Incident data second vertex) (hNe : first ≠ second)
    (hSurvives : ¬ IsDangling data edge) (hIncident : Incident data edge vertex) :
    edge = first ∨ edge = second := by
  classical
  have hSubset : ({first, second} : Finset data.SourceEdge) ⊆
      (Finset.univ : Finset data.SourceEdge).filter
        fun item ↦ ¬ IsDangling data item ∧ Incident data item vertex := by
    intro item hItem
    rcases Finset.mem_insert.mp hItem with hCase | hCase
    · rw [hCase]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFirstSurvives, hFirstIncident⟩
    · rw [Finset.mem_singleton.mp hCase]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSecondSurvives, hSecondIncident⟩
  have hCard : ((Finset.univ : Finset data.SourceEdge).filter
      fun item ↦ ¬ IsDangling data item ∧ Incident data item vertex).card ≤
      ({first, second} : Finset data.SourceEdge).card := by
    rw [Finset.card_pair hNe]
    exact le_of_eq hValency
  have hEq := Finset.eq_of_subset_of_card_le hSubset hCard
  have hMem : edge ∈ ({first, second} : Finset data.SourceEdge) := by
    rw [hEq]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSurvives, hIncident⟩
  rcases Finset.mem_insert.mp hMem with hCase | hCase
  · exact Or.inl hCase
  · exact Or.inr (Finset.mem_singleton.mp hCase)

section FullDimTransition

variable (fd : FullDimensionalSourcePresentation data coordinate)

include fd

/-- **A vertex whose two surviving occurrences have different indices is a
transition vertex**: its local ramification is one.  Over a divalent target
vertex an unramified block carries its own local degree in every direction. -/
theorem localRamification_eq_one_of_sourceEdgeIndex_ne {vertex : data.SourceVertex}
    (hDivalent : (GluingDatum.incidentEdges vertex.1.1).card = 2)
    {first second : data.SourceEdge}
    (hFirstIncident : Incident data first vertex)
    (hSecondIncident : Incident data second vertex)
    (hIndexNe : data.sourceEdgeIndex first ≠ data.sourceEdgeIndex second) :
    data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 1 := by
  have hNonneg := data.localRamification_nonneg vertex.1.1 (fd.valid.2 vertex.1.1)
    ⟨vertex.1.2, vertex.2⟩
  have hLe := localRamification_le_one fd hDivalent ⟨vertex.1.2, vertex.2⟩
  have hNotZero : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ ≠ 0 := by
    intro hZero
    exact hIndexNe
      ((sourceEdgeIndex_eq_blockCard_of_localRamification_zero hDivalent hZero
        hFirstIncident).trans
        (sourceEdgeIndex_eq_blockCard_of_localRamification_zero hDivalent hZero
          hSecondIncident).symm)
  omega

omit [Fintype coordinate] [DecidableEq coordinate] fd in
/-- A transition vertex has exactly three incident source occurrences. -/
theorem card_incidentSourceEdge_transition {vertex : data.SourceVertex}
    (hDivalent : (GluingDatum.incidentEdges vertex.1.1).card = 2)
    (hRamified : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 1) :
    Fintype.card (IncidentSourceEdge data vertex) = 3 := by
  have h := localRamification_add_two vertex hDivalent
  rw [hRamified] at h
  omega

/-- **No return at a transition vertex.**  The two surviving occurrences at a
transition vertex lie above the two *different* incident target occurrences:
a vertex whose survivors both lay above one of them would force its local
degree to be one, and then it would have only two incident occurrences, not
the three a transition has.  This is the no-return condition of Part I in
exactly the local form the column relation needs, derived here rather than
assumed. -/
theorem target_ne_of_transition {vertex : data.SourceVertex}
    (hDivalent : (GluingDatum.incidentEdges vertex.1.1).card = 2)
    (hRamified : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 1)
    (hValency : nonDanglingValency data vertex = 2)
    {first second : data.SourceEdge}
    (hFirstSurvives : ¬ IsDangling data first) (hFirstIncident : Incident data first vertex)
    (hSecondSurvives : ¬ IsDangling data second)
    (hSecondIncident : Incident data second vertex) (hNe : first ≠ second) :
    first.1.1 ≠ second.1.1 := by
  classical
  intro hSame
  have hFirstMem : first.1.1 ∈ GluingDatum.incidentEdges vertex.1.1 :=
    target_mem_of_incident hFirstIncident
  have hFirstRel : (data.vertexPartition vertex.1.1).Rel vertex.1.2 first.1.2 :=
    ((incident_iff_target_mem_and_rel data first vertex).mp hFirstIncident).2
  have hSecondRel : (data.vertexPartition vertex.1.1).Rel vertex.1.2 second.1.2 :=
    ((incident_iff_target_mem_and_rel data second vertex).mp hSecondIncident).2
  have hEraseCard : ((GluingDatum.incidentEdges vertex.1.1).erase first.1.1).card = 1 := by
    rw [Finset.card_erase_of_mem hFirstMem, hDivalent]
  obtain ⟨other, hOtherErase⟩ := Finset.card_pos.mp (by omega :
    0 < ((GluingDatum.incidentEdges vertex.1.1).erase first.1.1).card)
  have hOtherNe : other ≠ first.1.1 := (Finset.mem_erase.mp hOtherErase).1
  have hOtherMem : other ∈ GluingDatum.incidentEdges vertex.1.1 :=
    (Finset.mem_erase.mp hOtherErase).2
  have hThree := card_incidentSourceEdge_transition hDivalent hRamified
  have hSplit := card_incidentSourceEdge_eq_pair vertex (Ne.symm hOtherNe) hFirstMem
    hOtherMem hDivalent
  rw [hThree] at hSplit
  have hPosFirst := SheetPartition.blockCountWithin_pos (data.edgePartition first.1.1)
    (data.vertexPartition vertex.1.1) vertex.1.2
  have hPosOther := SheetPartition.blockCountWithin_pos (data.edgePartition other)
    (data.vertexPartition vertex.1.1) vertex.1.2
  by_cases hOne : (data.edgePartition first.1.1).blockCountWithin
      (data.vertexPartition vertex.1.1) vertex.1.2 = 1
  · apply hNe
    have hFirstAnchor := sourceEdge_eq_anchor vertex hFirstMem hFirstRel hOne
    have hSecondAnchor : data.sourceEdge first.1.1 second.1.2 =
        data.sourceEdge first.1.1 vertex.1.2 :=
      sourceEdge_eq_anchor vertex hFirstMem hSecondRel hOne
    have hFirstSelf : data.sourceEdge first.1.1 first.1.2 = first :=
      GluingDatum.sourceEdge_self data first
    have hSecondSelf : data.sourceEdge second.1.1 second.1.2 = second :=
      GluingDatum.sourceEdge_self data second
    rw [← hSame] at hSecondSelf
    rw [← hFirstSelf, hFirstAnchor, ← hSecondAnchor, hSecondSelf]
  · -- the other direction carries a single occurrence, which must be dangling
    have hOtherOne : (data.edgePartition other).blockCountWithin
        (data.vertexPartition vertex.1.1) vertex.1.2 = 1 := by omega
    have hTwo : (data.edgePartition first.1.1).blockCountWithin
        (data.vertexPartition vertex.1.1) vertex.1.2 = 2 := by omega
    set anchor := data.sourceEdge other vertex.1.2 with hAnchor
    have hAnchorIncident : Incident data anchor vertex := by
      have h := incident_sourceEdge_sourceEndpoint data vertex.1.1 other hOtherMem vertex.1.2
      rwa [GluingDatum.sourceEndpoint_self] at h
    have hAnchorNeFirst : anchor ≠ first := by
      intro hEq
      exact hOtherNe (congrArg (fun edge : data.SourceEdge ↦ edge.1.1) hEq)
    have hAnchorNeSecond : anchor ≠ second := by
      intro hEq
      exact hOtherNe (hSame ▸ congrArg (fun edge : data.SourceEdge ↦ edge.1.1) hEq)
    have hAnchorDangling : IsDangling data anchor := by
      by_contra hSurvives
      rcases eq_or_eq_of_nonDanglingValency_two hValency hFirstSurvives hFirstIncident
        hSecondSurvives hSecondIncident hNe hSurvives hAnchorIncident with hCase | hCase
      · exact hAnchorNeFirst hCase
      · exact hAnchorNeSecond hCase
    have hAnchorIndex : data.sourceEdgeIndex anchor = 1 :=
      fd.danglingEdgeNoGlue anchor hAnchorDangling
    have hAnchorCard : data.sourceEdgeIndex anchor =
        (data.edgePartition other).blockCard vertex.1.2 :=
      GluingDatum.sourceEdgeIndex_sourceEdge data other vertex.1.2
    have hBlockCard : (data.edgePartition other).blockCard vertex.1.2 =
        (data.vertexPartition vertex.1.1).blockCard vertex.1.2 :=
      SheetPartition.blockCard_eq_of_refines_of_blockCountWithin_eq_one
        (data.edgePartition other) (data.vertexPartition vertex.1.1)
        (refines_of_mem_incidentEdges data hOtherMem) vertex.1.2 hOtherOne
    have hLe := blockCountWithin_le_blockCard (data.edgePartition first.1.1)
      (data.vertexPartition vertex.1.1) vertex.1.2
    omega


/-! ## Consequences of the index identity -/

section Consequences

variable (fd : FullDimensionalSourcePresentation data coordinate)

include fd

/-- An unramified vertex of surviving valency two carries its local degree in
both surviving directions, whatever the valency of the target vertex below.
This is `prop-local`(r0). -/
theorem sourceEdgeIndex_eq_of_localRamification_eq_zero {vertex : data.SourceVertex}
    (hValency : nonDanglingValency data vertex = 2)
    (hZero : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 0)
    {first second : data.SourceEdge}
    (hFirstSurvives : ¬ IsDangling data first) (hFirstIncident : Incident data first vertex)
    (hSecondSurvives : ¬ IsDangling data second)
    (hSecondIncident : Incident data second vertex) (hNe : first ≠ second) :
    data.sourceEdgeIndex first = data.sourceEdgeIndex second := by
  have hSum := sourceEdgeIndex_add_sourceEdgeIndex fd hValency hFirstSurvives
    hFirstIncident hSecondSurvives hSecondIncident hNe
  rw [hZero] at hSum
  have hFirstLe : data.sourceEdgeIndex first ≤
      (data.vertexPartition vertex.1.1).blockCard vertex.1.2 :=
    sourceEdgeIndex_le_blockCard data vertex ⟨first, hFirstIncident⟩
  have hSecondLe : data.sourceEdgeIndex second ≤
      (data.vertexPartition vertex.1.1).blockCard vertex.1.2 :=
    sourceEdgeIndex_le_blockCard data vertex ⟨second, hSecondIncident⟩
  omega

/-- Local ramification never exceeds the change of the target vertex below. -/
theorem localRamification_le_targetChange {wall : target.V}
    (block : (data.vertexPartition wall).Blocks) :
    data.localRamification wall block ≤ data.targetChange wall := by
  have hNonneg : ∀ item : (data.vertexPartition wall).Blocks,
      0 ≤ data.localRamification wall item := fun item ↦
    data.localRamification_nonneg wall (fd.valid.2 wall) item
  exact Finset.single_le_sum (fun item _ ↦ hNonneg item) (Finset.mem_univ _)

/-- Change-minimality in the form `ch(x) = 3 - val(x)`. -/
theorem targetChange_eq_three_sub_valency (wall : target.V) :
    data.targetChange wall = 3 - ((GluingDatum.incidentEdges wall).card : ℤ) := by
  have h := fd.targetExcess_eq_zero wall
  unfold GluingDatum.targetExcess at h
  omega

/-- A ramified vertex of surviving valency two lies over a target vertex of
valency at most two. -/
theorem incidentEdges_card_le_two_of_localRamification_pos {wall : target.V}
    (block : (data.vertexPartition wall).Blocks)
    (hPos : 1 ≤ data.localRamification wall block) :
    (GluingDatum.incidentEdges wall).card ≤ 2 := by
  have hLe := localRamification_le_targetChange fd block
  rw [targetChange_eq_three_sub_valency fd wall] at hLe
  omega

end Consequences


/-! ## The column relation at a transition vertex -/

omit [Fintype coordinate] [DecidableEq coordinate] fd in
/-- Any occurrence above a target occurrence incident to `x` meets the block
of its own sheet above `x`. -/
theorem incident_blockVertex {wall : target.V} {edge : data.SourceEdge}
    (hMem : edge.1.1 ∈ GluingDatum.incidentEdges wall) :
    Incident data edge
      (blockVertex data wall ((data.vertexPartition wall).toBlock edge.1.2)) :=
  (incident_iff_target_mem_and_rel data edge _).mpr
    ⟨hMem, (data.vertexPartition wall).rel_repr_left edge.1.2⟩

/-- **Part I `lemma-change-zero` at a transition vertex.**  If the two
surviving occurrences `e_a`, `e_{a+1}` at a transition vertex `A_a` lie on the
stable row `h`, then

    col(t_a) - col(t_{a+1}) = (1/m(e_a) - 1/m(e_{a+1})) · e_h .

Every block above the divalent target vertex other than `A_a` is unramified,
so it contributes the *same* reciprocal index to both columns in its own row;
only `A_a` sees the difference. -/
theorem matrix_sub_eq_of_transition {vertex : data.SourceVertex}
    (hDivalent : (GluingDatum.incidentEdges vertex.1.1).card = 2)
    (hRamified : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 1)
    (hValency : nonDanglingValency data vertex = 2)
    {first second : data.SourceEdge}
    (hFirstSurvives : ¬ IsDangling data first) (hFirstIncident : Incident data first vertex)
    (hSecondSurvives : ¬ IsDangling data second)
    (hSecondIncident : Incident data second vertex) (hNe : first ≠ second)
    (sourceRow : coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation sourceRow
        (fd.labelling.targetEdge.symm first.1.1) -
      GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation sourceRow
        (fd.labelling.targetEdge.symm second.1.1) =
      if sourceRow = fd.labelling.row (NonDanglingEdge.stablePath
          (⟨first, hFirstSurvives⟩ : NonDanglingEdge data)) then
        (1 : ℚ) / data.sourceEdgeIndex first - (1 : ℚ) / data.sourceEdgeIndex second
      else 0 := by
  classical
  have hFirstMem : first.1.1 ∈ GluingDatum.incidentEdges vertex.1.1 :=
    target_mem_of_incident hFirstIncident
  have hSecondMem : second.1.1 ∈ GluingDatum.incidentEdges vertex.1.1 :=
    target_mem_of_incident hSecondIncident
  have hTargetNe : first.1.1 ≠ second.1.1 :=
    target_ne_of_transition fd hDivalent hRamified hValency hFirstSurvives
      hFirstIncident hSecondSurvives hSecondIncident hNe
  -- every surviving occurrence above one of the two target edges other than
  -- `first`, `second` sits on an unramified block
  have hBlockNe : ∀ edge : data.SourceEdge, ¬ IsDangling data edge →
      edge.1.1 ∈ GluingDatum.incidentEdges vertex.1.1 → edge ≠ first → edge ≠ second →
      (data.vertexPartition vertex.1.1).toBlock edge.1.2 ≠ ⟨vertex.1.2, vertex.2⟩ := by
    intro edge hSurvives hMem hNeFirst hNeSecond hBlock
    have hIncident : Incident data edge vertex := by
      have h := incident_blockVertex (data := data) (wall := vertex.1.1) hMem
      rwa [hBlock] at h
    rcases eq_or_eq_of_nonDanglingValency_two hValency hFirstSurvives hFirstIncident
      hSecondSurvives hSecondIncident hNe hSurvives hIncident with hCase | hCase
    · exact hNeFirst hCase
    · exact hNeSecond hCase
  have hZero : ∀ edge : data.SourceEdge, ¬ IsDangling data edge →
      edge.1.1 ∈ GluingDatum.incidentEdges vertex.1.1 → edge ≠ first → edge ≠ second →
      data.localRamification vertex.1.1
        ((data.vertexPartition vertex.1.1).toBlock edge.1.2) = 0 := by
    intro edge hSurvives hMem hNeFirst hNeSecond
    exact localRamification_eq_zero_of_ne fd hDivalent hRamified
      (hBlockNe edge hSurvives hMem hNeFirst hNeSecond)
  -- the transport between the two columns, away from the transition occurrence
  have hTransfer : ∀ one two : data.SourceEdge, one.1.1 ≠ two.1.1 →
      one.1.1 ∈ GluingDatum.incidentEdges vertex.1.1 →
      two.1.1 ∈ GluingDatum.incidentEdges vertex.1.1 →
      Incident data two vertex →
      (∀ edge : data.SourceEdge, ¬ IsDangling data edge → edge.1.1 = one.1.1 →
        edge ≠ one → data.localRamification vertex.1.1
          ((data.vertexPartition vertex.1.1).toBlock edge.1.2) = 0 ∧
          (data.vertexPartition vertex.1.1).toBlock edge.1.2 ≠ ⟨vertex.1.2, vertex.2⟩) →
      ∀ edge ∈ (rowFibre fd.labelling sourceRow one.1.1).erase one,
        data.sourceEdge two.1.1 edge.1.2 ∈
          (rowFibre fd.labelling sourceRow two.1.1).erase two := by
    intro one two hTwoNe hOneMem hTwoMem hTwoIncident hLocal edge hEdge
    obtain ⟨hEdgeNe, hEdgeMem⟩ := Finset.mem_erase.mp hEdge
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ :=
      (mem_rowFibre fd.labelling sourceRow one.1.1 edge).mp hEdgeMem
    obtain ⟨hLocalZero, hLocalNe⟩ := hLocal edge hSurvives hTarget hEdgeNe
    have hSelf : data.sourceEdge one.1.1 edge.1.2 = edge := by
      rw [← hTarget]
      exact GluingDatum.sourceEdge_self data edge
    have hOneSurvives : ¬ IsDangling data (data.sourceEdge one.1.1 edge.1.2) := by
      rw [hSelf]; exact hSurvives
    have hTwoSurvives : ¬ IsDangling data (data.sourceEdge two.1.1 edge.1.2) :=
      fun hDangling ↦ hOneSurvives
        ((isDangling_sourceEdge_iff_of_divalent_localRamification_zero data
          vertex.1.1 hDivalent edge.1.2 hLocalZero hTwoNe hOneMem hTwoMem).2 hDangling)
    have hPathEq := stablePath_sourceEdge_eq_of_divalent_localRamification_zero
      data vertex.1.1 hDivalent edge.1.2 hLocalZero hTwoNe hOneMem hTwoMem
      hOneSurvives hTwoSurvives
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · intro hEq
      apply hLocalNe
      have hRel : (data.edgePartition two.1.1).Rel edge.1.2 two.1.2 := by
        rw [← hEq]
        exact (data.edgePartition two.1.1).rel_repr_right edge.1.2
      have hCoarse : (data.vertexPartition vertex.1.1).Rel edge.1.2 two.1.2 :=
        (refines_of_mem_incidentEdges data hTwoMem).rel hRel
      apply Subtype.ext
      show (data.vertexPartition vertex.1.1).repr edge.1.2 = vertex.1.2
      have hTwoBlock : (data.vertexPartition vertex.1.1).repr two.1.2 = vertex.1.2 :=
        congrArg Subtype.val (toBlock_eq_of_incident hTwoIncident)
      exact hCoarse.trans hTwoBlock
    · refine (mem_rowFibre fd.labelling sourceRow two.1.1 _).mpr ⟨⟨hTwoSurvives, ?_⟩, rfl⟩
      rw [← hPathEq,
        show (⟨data.sourceEdge one.1.1 edge.1.2, hOneSurvives⟩ :
          NonDanglingEdge data) = ⟨edge, hSurvives⟩ from Subtype.ext hSelf]
      exact hRow
  -- the two local hypotheses the transport needs, one per column
  have hLocalFirst : ∀ edge : data.SourceEdge, ¬ IsDangling data edge →
      edge.1.1 = first.1.1 → edge ≠ first →
      data.localRamification vertex.1.1
          ((data.vertexPartition vertex.1.1).toBlock edge.1.2) = 0 ∧
        (data.vertexPartition vertex.1.1).toBlock edge.1.2 ≠ ⟨vertex.1.2, vertex.2⟩ := by
    intro edge hSurvives hTarget hEdgeNe
    have hMem : edge.1.1 ∈ GluingDatum.incidentEdges vertex.1.1 := by
      rw [hTarget]; exact hFirstMem
    have hNeSecond : edge ≠ second := fun hEq ↦ hTargetNe (hTarget ▸ congrArg
      (fun item : data.SourceEdge ↦ item.1.1) hEq)
    exact ⟨hZero edge hSurvives hMem hEdgeNe hNeSecond,
      hBlockNe edge hSurvives hMem hEdgeNe hNeSecond⟩
  have hLocalSecond : ∀ edge : data.SourceEdge, ¬ IsDangling data edge →
      edge.1.1 = second.1.1 → edge ≠ second →
      data.localRamification vertex.1.1
          ((data.vertexPartition vertex.1.1).toBlock edge.1.2) = 0 ∧
        (data.vertexPartition vertex.1.1).toBlock edge.1.2 ≠ ⟨vertex.1.2, vertex.2⟩ := by
    intro edge hSurvives hTarget hEdgeNe
    have hMem : edge.1.1 ∈ GluingDatum.incidentEdges vertex.1.1 := by
      rw [hTarget]; exact hSecondMem
    have hNeFirst : edge ≠ first := fun hEq ↦ hTargetNe (by rw [← hTarget, hEq])
    exact ⟨hZero edge hSurvives hMem hNeFirst hEdgeNe,
      hBlockNe edge hSurvives hMem hNeFirst hEdgeNe⟩
  -- the two columns agree away from the transition occurrence
  have hSumErase : (∑ edge ∈ (rowFibre fd.labelling sourceRow first.1.1).erase first,
        (1 : ℚ) / data.sourceEdgeIndex edge) =
      ∑ edge ∈ (rowFibre fd.labelling sourceRow second.1.1).erase second,
        (1 : ℚ) / data.sourceEdgeIndex edge := by
    refine Finset.sum_nbij' (fun edge ↦ data.sourceEdge second.1.1 edge.1.2)
      (fun edge ↦ data.sourceEdge first.1.1 edge.1.2)
      (hTransfer first second hTargetNe hFirstMem hSecondMem hSecondIncident hLocalFirst)
      (hTransfer second first (Ne.symm hTargetNe) hSecondMem hFirstMem hFirstIncident
        hLocalSecond) ?_ ?_ ?_
    · intro edge hEdge
      obtain ⟨hEdgeNe, hEdgeMem⟩ := Finset.mem_erase.mp hEdge
      obtain ⟨⟨hSurvives, _⟩, hTarget⟩ :=
        (mem_rowFibre fd.labelling sourceRow first.1.1 edge).mp hEdgeMem
      exact sourceEdge_transport_left_inverse_of_divalent_localRamification_zero
        data vertex.1.1 hDivalent first.1.1 second.1.1 hFirstMem hSecondMem edge hTarget
        (hLocalFirst edge hSurvives hTarget hEdgeNe).1
    · intro edge hEdge
      obtain ⟨hEdgeNe, hEdgeMem⟩ := Finset.mem_erase.mp hEdge
      obtain ⟨⟨hSurvives, _⟩, hTarget⟩ :=
        (mem_rowFibre fd.labelling sourceRow second.1.1 edge).mp hEdgeMem
      exact sourceEdge_transport_left_inverse_of_divalent_localRamification_zero
        data vertex.1.1 hDivalent second.1.1 first.1.1 hSecondMem hFirstMem edge hTarget
        (hLocalSecond edge hSurvives hTarget hEdgeNe).1
    · intro edge hEdge
      obtain ⟨hEdgeNe, hEdgeMem⟩ := Finset.mem_erase.mp hEdge
      obtain ⟨⟨hSurvives, _⟩, hTarget⟩ :=
        (mem_rowFibre fd.labelling sourceRow first.1.1 edge).mp hEdgeMem
      have hLocalZero := (hLocalFirst edge hSurvives hTarget hEdgeNe).1
      have hSelf : data.sourceEdge first.1.1 edge.1.2 = edge := by
        rw [← hTarget]
        exact GluingDatum.sourceEdge_self data edge
      have hFirstIndex := sourceEdgeIndex_eq_of_divalent_localRamification_zero
        data vertex.1.1 hDivalent edge.1.2 hLocalZero first.1.1 hFirstMem
      rw [hSelf] at hFirstIndex
      have hSecondIndex := sourceEdgeIndex_eq_of_divalent_localRamification_zero
        data vertex.1.1 hDivalent edge.1.2 hLocalZero second.1.1 hSecondMem
      rw [hFirstIndex, hSecondIndex]
  -- membership of the two transition occurrences
  have hRowSecond : fd.labelling.row (NonDanglingEdge.stablePath
      (⟨second, hSecondSurvives⟩ : NonDanglingEdge data)) =
      fd.labelling.row (NonDanglingEdge.stablePath
        (⟨first, hFirstSurvives⟩ : NonDanglingEdge data)) := by
    refine congrArg fd.labelling.row (stablePath_eq_of_consecutive ⟨?_, vertex,
      hSecondIncident, hFirstIncident, hValency⟩)
    intro hEq
    exact hNe (congrArg Subtype.val hEq).symm
  have hMemFirst : first ∈ rowFibre fd.labelling sourceRow first.1.1 ↔
      sourceRow = fd.labelling.row (NonDanglingEdge.stablePath
        (⟨first, hFirstSurvives⟩ : NonDanglingEdge data)) := by
    rw [mem_rowFibre]
    constructor
    · rintro ⟨⟨hS, hR⟩, -⟩
      exact hR.symm
    · intro hR
      exact ⟨⟨hFirstSurvives, hR.symm⟩, rfl⟩
  have hMemSecond : second ∈ rowFibre fd.labelling sourceRow second.1.1 ↔
      sourceRow = fd.labelling.row (NonDanglingEdge.stablePath
        (⟨first, hFirstSurvives⟩ : NonDanglingEdge data)) := by
    rw [mem_rowFibre]
    constructor
    · rintro ⟨⟨hS, hR⟩, -⟩
      rw [← hR, show (⟨second, hS⟩ : NonDanglingEdge data) = ⟨second, hSecondSurvives⟩ from rfl,
        hRowSecond]
    · intro hR
      exact ⟨⟨hSecondSurvives, by rw [hRowSecond, ← hR]⟩, rfl⟩
  rw [matrix_eq_sum_fibre, matrix_eq_sum_fibre]
  by_cases hCase : sourceRow = fd.labelling.row (NonDanglingEdge.stablePath
      (⟨first, hFirstSurvives⟩ : NonDanglingEdge data))
  · rw [if_pos hCase]
    rw [← Finset.add_sum_erase _ _ (hMemFirst.mpr hCase),
      ← Finset.add_sum_erase _ _ (hMemSecond.mpr hCase), hSumErase]
    ring
  · rw [Finset.erase_eq_of_notMem (fun hMem ↦ hCase (hMemFirst.mp hMem)),
      Finset.erase_eq_of_notMem (fun hMem ↦ hCase (hMemSecond.mp hMem))] at hSumErase
    rw [if_neg hCase, hSumErase]
    ring


end FullDimTransition


/-! ## The index pattern on a leaf-passing row -/

section LeafRow

variable (fd : FullDimensionalSourcePresentation data coordinate)

include fd

/-- **No transition on a leaf-passing row.**  Two surviving occurrences meeting
at a surviving-valency-two vertex of a row that passes above a leaf carry the
same index: a transition there would give a column relation whose right-hand
side is a nonzero multiple of `e_{h(v)}`, and together with the leaf column
`2 e_{h(v)}` that is a vanishing combination of distinct columns. -/
theorem sourceEdgeIndex_eq_of_consecutive_on_leafRow {leaf : target.V}
    (hLeaf : IsLeafVertex target leaf) {vertex : data.SourceVertex}
    (hValency : nonDanglingValency data vertex = 2)
    {first second : data.SourceEdge}
    (hFirstSurvives : ¬ IsDangling data first) (hFirstIncident : Incident data first vertex)
    (hSecondSurvives : ¬ IsDangling data second)
    (hSecondIncident : Incident data second vertex) (hNe : first ≠ second)
    (hRow : fd.labelling.row (NonDanglingEdge.stablePath
      (⟨first, hFirstSurvives⟩ : NonDanglingEdge data)) = leafRow fd hLeaf) :
    data.sourceEdgeIndex first = data.sourceEdgeIndex second := by
  classical
  by_contra hIndexNe
  -- the vertex is ramified
  have hNotZero : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ ≠ 0 := by
    intro hZero
    exact hIndexNe (sourceEdgeIndex_eq_of_localRamification_eq_zero fd hValency hZero
      hFirstSurvives hFirstIncident hSecondSurvives hSecondIncident hNe)
  have hNonneg := data.localRamification_nonneg vertex.1.1 (fd.valid.2 vertex.1.1)
    ⟨vertex.1.2, vertex.2⟩
  have hPos : 1 ≤ data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ := by omega
  have hValCard := incidentEdges_card_le_two_of_localRamification_pos fd
    ⟨vertex.1.2, vertex.2⟩ hPos
  have hValPos : 0 < (GluingDatum.incidentEdges vertex.1.1).card :=
    incidentEdges_card_pos_of_changeMinimalAt data vertex.1.1 (fd.changeMinimal vertex.1.1)
  interval_cases hCard : (GluingDatum.incidentEdges vertex.1.1).card
  · -- the target vertex is a leaf: every occurrence there is unramified
    apply hIndexNe
    rw [sourceEdgeIndex_eq_one_of_target_leaf data fd.valid fd.noDanglingTargetFibres
        vertex hCard (fd.changeMinimal _) ⟨first, hFirstIncident⟩,
      sourceEdgeIndex_eq_one_of_target_leaf data fd.valid fd.noDanglingTargetFibres
        vertex hCard (fd.changeMinimal _) ⟨second, hSecondIncident⟩]
  · -- the target vertex is divalent: a genuine transition, and the determinant dies
    have hRam : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 1 := by
      have hLe := localRamification_le_targetChange fd (wall := vertex.1.1)
        ⟨vertex.1.2, vertex.2⟩
      rw [targetChange_eq_three_sub_valency fd vertex.1.1, hCard] at hLe
      omega
    have hTargetNe : first.1.1 ≠ second.1.1 :=
      target_ne_of_transition fd hCard hRam hValency hFirstSurvives hFirstIncident
        hSecondSurvives hSecondIncident hNe
    have hColumnNe : fd.labelling.targetEdge.symm first.1.1 ≠
        fd.labelling.targetEdge.symm second.1.1 :=
      fun hEq ↦ hTargetNe (fd.labelling.targetEdge.symm.injective hEq)
    apply fd.det_ne_zero
    refine det_eq_zero_of_column_relation_and_leaf
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation)
      (sourceRow := leafRow fd hLeaf)
      (coefficient := (1 : ℚ) / data.sourceEdgeIndex first -
        (1 : ℚ) / data.sourceEdgeIndex second)
      (leafColumn := fd.labelling.targetEdge.symm (leafEdge hLeaf)) hColumnNe ?_ ?_
    · intro row
      rw [matrix_sub_eq_of_transition fd hCard hRam hValency hFirstSurvives hFirstIncident
        hSecondSurvives hSecondIncident hNe row, hRow]
    · intro row
      exact matrix_leafEdge_column fd hLeaf row

/-- **A leaf-passing row has all indices one.**  The index is constant along
the row by the previous theorem, and it is `1` at the two occurrences above
the leaf edge. -/
theorem sourceEdgeIndex_eq_one_of_row_eq_leafRow {leaf : target.V}
    (hLeaf : IsLeafVertex target leaf) {edge : data.SourceEdge}
    (hSurvives : ¬ IsDangling data edge)
    (hRow : fd.labelling.row (NonDanglingEdge.stablePath
      (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = leafRow fd hLeaf) :
    data.sourceEdgeIndex edge = 1 := by
  classical
  set property : NonDanglingEdge data → Prop := fun item ↦
    fd.labelling.row (NonDanglingEdge.stablePath item) = leafRow fd hLeaf →
      data.sourceEdgeIndex item.1 = 1 with hProperty
  have hClosed : ∀ one two : NonDanglingEdge data, Consecutive data one two →
      property one → property two := by
    intro one two hConsecutive hOne hRowTwo
    have hPathEq : NonDanglingEdge.stablePath one = NonDanglingEdge.stablePath two :=
      stablePath_eq_of_consecutive hConsecutive
    obtain ⟨hNeEdges, meeting, hIncidentOne, hIncidentTwo, hValency⟩ := hConsecutive
    have hRowOne : fd.labelling.row (NonDanglingEdge.stablePath one) =
        leafRow fd hLeaf := by rw [hPathEq]; exact hRowTwo
    rw [← hOne hRowOne]
    exact (sourceEdgeIndex_eq_of_consecutive_on_leafRow fd hLeaf hValency one.2
      hIncidentOne two.2 hIncidentTwo (fun hEq ↦ hNeEdges (Subtype.ext hEq))
      hRowOne).symm
  have hBase : property ⟨leafSurvivor fd hLeaf, (leafSurvivor_spec fd hLeaf).2⟩ := by
    intro _
    exact sourceEdgeIndex_eq_one_above_leaf fd hLeaf (leafSurvivor_spec fd hLeaf).1
  have hPath : NonDanglingEdge.stablePath
      (⟨leafSurvivor fd hLeaf, (leafSurvivor_spec fd hLeaf).2⟩ : NonDanglingEdge data) =
      NonDanglingEdge.stablePath (⟨edge, hSurvives⟩ : NonDanglingEdge data) :=
    fd.labelling.row.injective (hRow.symm)
  exact (eqvGen_iff_of_closed hClosed ((stablePath_eq_iff _ _).mp hPath)).mp hBase hRow

end LeafRow

/-! ## Leaf-avoiding rows: two values differing by one, and at most one
transition -/

section LeafAvoiding

variable (fd : FullDimensionalSourcePresentation data coordinate)

include fd

/-- **At a transition the two indices differ by exactly one.**  This is the
identity `r(A_a) = |m(e_a) - m(e_{a+1})|` in the ramified case. -/
theorem sourceEdgeIndex_sub_eq_one_of_transition {vertex : data.SourceVertex}
    (hValency : nonDanglingValency data vertex = 2)
    (hRamified : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 1)
    {first second : data.SourceEdge}
    (hFirstSurvives : ¬ IsDangling data first) (hFirstIncident : Incident data first vertex)
    (hSecondSurvives : ¬ IsDangling data second)
    (hSecondIncident : Incident data second vertex) (hNe : first ≠ second) :
    (data.sourceEdgeIndex first : ℤ) = (data.sourceEdgeIndex second : ℤ) + 1 ∨
      (data.sourceEdgeIndex second : ℤ) = (data.sourceEdgeIndex first : ℤ) + 1 := by
  have hSum := sourceEdgeIndex_add_sourceEdgeIndex fd hValency hFirstSurvives
    hFirstIncident hSecondSurvives hSecondIncident hNe
  rw [hRamified] at hSum
  have hFirstLe : data.sourceEdgeIndex first ≤
      (data.vertexPartition vertex.1.1).blockCard vertex.1.2 :=
    sourceEdgeIndex_le_blockCard data vertex ⟨first, hFirstIncident⟩
  have hSecondLe : data.sourceEdgeIndex second ≤
      (data.vertexPartition vertex.1.1).blockCard vertex.1.2 :=
    sourceEdgeIndex_le_blockCard data vertex ⟨second, hSecondIncident⟩
  omega

/-- **Two transitions on one stable row are impossible.**  Both column
relations have a right-hand side supported on the single row `h`, so a nonzero
combination of the four columns vanishes and `det A_φ = 0`.

The hypothesis `hPairs` says the two transitions do not use the *same unordered
pair* of target occurrences.  That is the only configuration the linear algebra
cannot exclude, and it is exactly a cycle of the target: two distinct divalent
target vertices joined by the same two occurrences.  Deriving `hPairs` from
`genus target = 0` is **not** done here; see the module docstring. -/
theorem not_two_transitions_on_one_row
    {vertexA vertexB : data.SourceVertex}
    (hDivalentA : (GluingDatum.incidentEdges vertexA.1.1).card = 2)
    (hDivalentB : (GluingDatum.incidentEdges vertexB.1.1).card = 2)
    (hRamifiedA : data.localRamification vertexA.1.1 ⟨vertexA.1.2, vertexA.2⟩ = 1)
    (hRamifiedB : data.localRamification vertexB.1.1 ⟨vertexB.1.2, vertexB.2⟩ = 1)
    (hValencyA : nonDanglingValency data vertexA = 2)
    (hValencyB : nonDanglingValency data vertexB = 2)
    {a₁ a₂ b₁ b₂ : data.SourceEdge}
    (ha₁S : ¬ IsDangling data a₁) (ha₁I : Incident data a₁ vertexA)
    (ha₂S : ¬ IsDangling data a₂) (ha₂I : Incident data a₂ vertexA) (haNe : a₁ ≠ a₂)
    (hb₁S : ¬ IsDangling data b₁) (hb₁I : Incident data b₁ vertexB)
    (hb₂S : ¬ IsDangling data b₂) (hb₂I : Incident data b₂ vertexB) (hbNe : b₁ ≠ b₂)
    (hIndexB : data.sourceEdgeIndex b₁ ≠ data.sourceEdgeIndex b₂)
    (hSameRow : fd.labelling.row (NonDanglingEdge.stablePath
        (⟨b₁, hb₁S⟩ : NonDanglingEdge data)) =
      fd.labelling.row (NonDanglingEdge.stablePath
        (⟨a₁, ha₁S⟩ : NonDanglingEdge data)))
    (hPairs : ¬ ((a₁.1.1 = b₁.1.1 ∧ a₂.1.1 = b₂.1.1) ∨
      (a₁.1.1 = b₂.1.1 ∧ a₂.1.1 = b₁.1.1))) :
    False := by
  classical
  have hTargetNeA : a₁.1.1 ≠ a₂.1.1 :=
    target_ne_of_transition fd hDivalentA hRamifiedA hValencyA ha₁S ha₁I ha₂S ha₂I haNe
  have hTargetNeB : b₁.1.1 ≠ b₂.1.1 :=
    target_ne_of_transition fd hDivalentB hRamifiedB hValencyB hb₁S hb₁I hb₂S hb₂I hbNe
  have hCoefficientB : (1 : ℚ) / data.sourceEdgeIndex b₁ -
      (1 : ℚ) / data.sourceEdgeIndex b₂ ≠ 0 := by
    intro hZero
    apply hIndexB
    have hFirstPos : (0 : ℚ) < data.sourceEdgeIndex b₁ := by
      exact_mod_cast GluingDatum.sourceEdgeIndex_pos data b₁
    have hSecondPos : (0 : ℚ) < data.sourceEdgeIndex b₂ := by
      exact_mod_cast GluingDatum.sourceEdgeIndex_pos data b₂
    have hEqRat : (data.sourceEdgeIndex b₁ : ℚ) = data.sourceEdgeIndex b₂ := by
      field_simp at hZero
      linarith
    exact_mod_cast hEqRat
  refine fd.det_ne_zero (det_eq_zero_of_two_column_relations
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation)
    (sourceRow := fd.labelling.row (NonDanglingEdge.stablePath
      (⟨a₁, ha₁S⟩ : NonDanglingEdge data)))
    (coefficientA := (1 : ℚ) / data.sourceEdgeIndex a₁ -
      (1 : ℚ) / data.sourceEdgeIndex a₂)
    (coefficientB := (1 : ℚ) / data.sourceEdgeIndex b₁ -
      (1 : ℚ) / data.sourceEdgeIndex b₂)
    hCoefficientB
    (fun hEq ↦ hTargetNeA (fd.labelling.targetEdge.symm.injective hEq))
    (fun hEq ↦ hTargetNeB (fd.labelling.targetEdge.symm.injective hEq))
    ?_
    (fun row ↦ matrix_sub_eq_of_transition fd hDivalentA hRamifiedA hValencyA
      ha₁S ha₁I ha₂S ha₂I haNe row)
    (fun row ↦ by
      rw [matrix_sub_eq_of_transition fd hDivalentB hRamifiedB hValencyB
        hb₁S hb₁I hb₂S hb₂I hbNe row, hSameRow]))
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact hPairs (Or.inl ⟨fd.labelling.targetEdge.symm.injective h1,
      fd.labelling.targetEdge.symm.injective h2⟩)
  · exact hPairs (Or.inr ⟨fd.labelling.targetEdge.symm.injective h1,
      fd.labelling.targetEdge.symm.injective h2⟩)

end LeafAvoiding



/-! ## Non-vacuity: the caterpillar of loops -/

section Witness

open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CaterpillarDatum

/-- **Non-vacuity of the local index identity.**  At the first lollipop tip of
the caterpillar of loops the leaf fibre really does carry two distinct
surviving occurrences, and the identity `m(e_a) + m(e_{a+1}) = 2 m(A) - r(A)`
evaluates there to `1 + 1 = 2·2 - 2`. -/
example (m : ℕ) : ∃ first second : (caterpillarDatum m).SourceEdge, first ≠ second ∧
    (caterpillarDatum m).sourceEdgeIndex first +
      (caterpillarDatum m).sourceEdgeIndex second = 2 := by
  classical
  obtain ⟨first, hFirst, second, hSecond, hNe⟩ := Finset.one_lt_card.mp
    (by rw [leafSurvivors_card (CaterpillarRows.fullDim m) (isLeafVertex_catTip m)]
        norm_num :
      1 < (leafSurvivors (data := caterpillarDatum m) (isLeafVertex_catTip m)).card)
  refine ⟨first, second, hNe, ?_⟩
  have hIdentity := sourceEdgeIndex_add_sourceEdgeIndex (CaterpillarRows.fullDim m)
    (nonDanglingValency_coreVertex (CaterpillarRows.fullDim m) (isLeafVertex_catTip m))
    ((mem_leafSurvivors (isLeafVertex_catTip m)).mp hFirst).1
    (incident_coreVertex_of_mem_leafSurvivors (CaterpillarRows.fullDim m)
      (isLeafVertex_catTip m) hFirst)
    ((mem_leafSurvivors (isLeafVertex_catTip m)).mp hSecond).1
    (incident_coreVertex_of_mem_leafSurvivors (CaterpillarRows.fullDim m)
      (isLeafVertex_catTip m) hSecond) hNe
  rw [show ((caterpillarDatum m).vertexPartition
      (coreVertex (CaterpillarRows.fullDim m) (isLeafVertex_catTip m)).1.1).blockCard
      (coreVertex (CaterpillarRows.fullDim m) (isLeafVertex_catTip m)).1.2 = 2 from
    blockCard_coreBlock (CaterpillarRows.fullDim m) (isLeafVertex_catTip m),
    show (caterpillarDatum m).localRamification
      (coreVertex (CaterpillarRows.fullDim m) (isLeafVertex_catTip m)).1.1
      ⟨(coreVertex (CaterpillarRows.fullDim m) (isLeafVertex_catTip m)).1.2,
        (coreVertex (CaterpillarRows.fullDim m) (isLeafVertex_catTip m)).2⟩ = 2 from
    localRamification_coreBlock (CaterpillarRows.fullDim m) (isLeafVertex_catTip m)]
    at hIdentity
  omega

/-- **Non-vacuity of the leaf-row conclusion**: every surviving occurrence of
the stable row through the first lollipop tip of the caterpillar of loops is
unramified. -/
example (m : ℕ) (edge : (caterpillarDatum m).SourceEdge)
    (hSurvives : ¬ IsDangling (caterpillarDatum m) edge)
    (hRow : (CaterpillarRows.fullDim m).labelling.row
        (NonDanglingEdge.stablePath (⟨edge, hSurvives⟩ : NonDanglingEdge _)) =
      leafRow (CaterpillarRows.fullDim m) (isLeafVertex_catTip m)) :
    (caterpillarDatum m).sourceEdgeIndex edge = 1 :=
  sourceEdgeIndex_eq_one_of_row_eq_leafRow (CaterpillarRows.fullDim m)
    (isLeafVertex_catTip m) hSurvives hRow

end Witness


end DraismaVargas.Count.IndexPattern
