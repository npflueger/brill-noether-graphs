module

public import DraismaVargasCount.EdgeDenominator
public import DraismaVargasCount.TrivalentWeight

@[expose] public section

/-!
# The ordered walk of a stable row, and the index pattern it gives

**Source.**  Vargas, Part II (arXiv:2609.09109), `proposition-at-most-two-weights`: if no
edge of a stable row lies above an edge incident to a leaf of `T`, then, up to reversing the
row, there are `k ≥ 1` and `1 ≤ μ ≤ ν` with `m(e_i) = k` for `i ≤ μ` and `m(e_i) = k+1` for
`i > μ`.  Its consumers are `lemma-edge-deno` and `prop-signed-mult`(1).

`Count.IndexPattern` supplies the **pointwise** content of that statement; turning it into
"the row is `k^μ (k+1)^{ν-μ}`" needs the ordered walk of a stable row, which this file
builds.

## What is proved

### 1.  The ordered walk, without a square labelling

`W4StableSource.StableLengthMatrixLabelling.orderedPath` traverses a row of a
*square* honest labelling.  The codimension-one incoming datum has one more
stable path than target occurrence and therefore carries no such labelling
(`FullDimensionalSource.stablePath_card_ne_succ`), so that walk is unavailable
exactly at the codimension-one limits of a star.  `orderedRow` is the same traversal
indexed by the stable-path class itself: it needs only `HasPathEnds data`.  Its membership
predicate `OnRow` is the membership of `Count.TrivalentWeight.incomingRowEdges`
and, through `mem_rowEdges_iff_onRow` and `rowEdges_eq_incomingRowEdges`, of
`Count.EdgeDenominator.rowEdges`.  **Every walk statement below therefore covers
the codimension-one limit and the full-dimensional morphism at once.**

### 2.  The local step, from dangling-no-glue alone

`sourceEdgeIndex_add_sourceEdgeIndex_of_noGlue` is
`Count.IndexPattern.sourceEdgeIndex_add_sourceEdgeIndex` with its
`FullDimensionalSourcePresentation` hypothesis replaced by the single
consequence of it that the proof uses, `DanglingEdgeNoGlue data`, which is a
*field* of `SecondEquation.W2SourceInput`.  Likewise
`sourceEdgeIndex_eq_of_localRamification_eq_zero_of_noGlue` and
`sourceEdgeIndex_sub_eq_one_of_transition_of_noGlue`.

### 3.  The walk theorems

* `sourceEdgeIndex_eq_of_rowUnramified` -- **constancy**: on a row with no
  ramified interior vertex every displayed index is the same.
* `exists_index_two_valued_of_rowAtMostOneTransition` -- **two values**: with
  `r ≤ 1` at every interior vertex and at most one transition, the displayed
  indices lie in `{k, k+1}` with `k ≥ 1`.
* `chain_eq_head`, `chain_const`, `chain_two_valued` -- the list engine, stated
  for an arbitrary chain.

### 4.  `hPairs`, discharged

`IndexPattern.not_two_transitions_on_one_row` carries a separation hypothesis
`hPairs`.  It is discharged by
`not_two_transitions_on_one_row_of_simpleTarget` from

* `SimpleTarget target` -- no two target occurrences join the same two target
  vertices; and
* `vertexA ≠ vertexB` -- the two transitions are at different source vertices,

using `sourceVertex_eq_of_localRamification_eq_one` (two ramified blocks over
one divalent target vertex coincide, because the change budget there is one).
Hence `rowAtMostOneTransition_of_simpleTarget`, and with it
`rowIndicesConsecutive_of_simpleTarget` for **every** row, so
`rowDenominator_trichotomy_of_simpleTarget` restates
`Count.EdgeDenominator.rowDenominator_trichotomy` with **no hypothesis beyond
`SimpleTarget`**.

### 5.  No backtracking

`sourceEdgeIndex_add_le_blockCard` is harmonicity in a single direction: the
edge blocks above one target occurrence partition the vertex block, so two
distinct occurrences of one block above one target occurrence have indices
summing to at most `m(A)`.  With the local step this gives
`target_ne_of_localRamification_le_one`: **at a surviving-valency-two vertex of
ramification at most one the two survivors lie above different target
occurrences**, with no hypothesis on the target vertex.  (
`Count.IndexPattern.target_ne_of_transition` proves the `r = 1`, divalent case
by a different count.)  `target_ne_of_row` is the row form: the ordered walk of
a leaf-avoiding row never leaves a vertex by the occurrence it entered by.

### 6.  The consequences for the count

* `forall_index_dvd_of_rowUnramified` -- `∀ e` on the row, `m(e) ∣ m(e₀)`, in
  exactly the shape of the first hypothesis of
  `Count.TrivalentWeight.incomingRowDenominator_eq_of_index_dvd_of_simple` and
  of `Count.IncomingSimpleColumn.incomingRowDenominator_secondRow_eq`.
* `incomingRowDenominator_dvd_of_rowUnramified` -- `d₀ ∣ k`, the **divisibility
  half** of the sharp incoming denominator.
* `occurrences_eq_singleton_of_rowTargetInjective` and
  `dvd_incomingRowDenominator_of_rowTargetInjective` -- the **simple column**
  and the reverse divisibility `k ∣ d₀`, from target injectivity of the row.
  This is an *alternative* to the column-difference route of
  `Count.IncomingSimpleColumn`, not a duplicate of it: that route gets `k ∣ d₀` from
  `secondRow ≠ thirdRow` without any walk, and the two hypotheses are independent.
* `incomingRowDenominator_eq_of_rowUnramified_of_rowTargetInjective` -- the
  sharp `d₀ = k` from the two halves this file supplies.
* `rowIndexConstant_of_rowUnramified`, `rowDenominator_dvd_of_rowUnramified` --
  the same on a square full-dimensional presentation.
* `forall_index_dvd_secondRow`, `forall_index_dvd_thirdRow`,
  `incomingRowDenominator_secondRow_dvd`, `incomingRowDenominator_thirdRow_dvd`,
  and the `_eq` forms -- the two rows `h₂`, `h₃` of the `{w2-r2-nd3-M-1k}`
  incoming datum, where `m(e₂) = m(e₃) = k` by
  `W2M1kSourceCandidates.Shape.second_index` / `third_index`.

## What is not proved here

* **`RowUnramified` itself.**  It fails in general: `lemma-edge-deno` (c) is
  the case of a row with one transition, and `rowIndicesConsecutive` is exactly
  what survives without it.  What is proved is that it is the only remaining condition:
  `rowUnramified_iff_forall_not_isRowTransition` says a row with `r ≤ 1` at
  every interior vertex is unramified iff it carries no transition vertex, and
  `rowRamificationAtMostOne_of_rowAvoidsLeaves` establishes `r ≤ 1` on a
  leaf-avoiding row of a full-dimensional morphism with no further hypothesis.
  For `h₂` and `h₃` of the `{w2-r2-nd3-M-1k}` incoming datum it therefore
  remains an explicit hypothesis, named `RowUnramified data (secondRow profile)`
  and `RowUnramified data (thirdRow profile)`.
* **`RowTargetInjective`, and with it the geodesic statement** (the image of a
  leaf-avoiding row is a geodesic).  Its *local* half is proved (`target_ne_of_row`: the
  walk does not backtrack).  Its *global* half -- a non-backtracking walk in a connected
  genus-zero target never repeats a target occurrence -- is pure target combinatorics: it
  needs a notion of walk and cycle for `CFGraph` and the step "a closed non-backtracking
  walk forces `genus > 0`".  `Count.TargetGeodesic` builds that walk/cycle calculus, and
  `Count.RowGeodesic.rowTargetInjective_of_genusZero` discharges
  `RowTargetInjective data path` from `graph_connected target`,
  `genus target = 0`, `DanglingEdgeNoGlue data` and `HasPathEnds data`, given
  `RowRamificationAtMostOne data path`.  This file cannot call it --
  `Count.RowGeodesic` imports this module, not the other way -- so
  `RowTargetInjective data path` is carried here as an explicit
  hypothesis, with its consumers stated so that the call site discharges it at
  once.  Its relation to the hypothesis `secondRow profile ≠ thirdRow profile` of
  `Count.IncomingSimpleColumn` is worth stating exactly: `RowTargetInjective` does
  **not** prove that hypothesis -- `e₂` and `e₃` lie above *different* target occurrences
  `t₂ ≠ t₃`, so injectivity of the row never compares them, and the hypothesis
  really says the row of `e₂` is not a **loop** of the stable graph at the wall,
  i.e. a closed non-backtracking target walk -- but it makes it **unnecessary**:
  `incomingRowDenominator_secondRow_eq` below reaches the same sharp `d₀ = k`
  from `RowUnramified` and `RowTargetInjective` on that one row, by the simple
  column rather than by the column difference.  Both routes use the same
  target-side theorem; neither subsumes the other.
* **`SimpleTarget target`.**  It says the target multigraph has no parallel
  occurrences, and is the global form of the `num_edges target a b = 1`
  hypothesis that the Part I wall interfaces carry at every contraction.  It
  follows from `graph_connected target` and `genus target = 0`:
  `Count.RowGeodesic.simpleTarget_of_genusZero` proves it, needing no
  spanning-tree argument at all, only
  `Count.TargetGeodesic.TreeRank.eq_of_incident`.  This file cannot call it --
  `Count.RowGeodesic` imports this module, not the other way -- so
  `SimpleTarget target` is carried here as an explicit hypothesis;
  `simpleTarget_catTree` below, proved by hand for the caterpillar target
  `T^CL_g`, is a special case of that theorem.
* **`HasPathEnds data` for the codimension-one datum.**  It is a field of
  `FullDimensionalSourcePresentation` (`pathEnds`) but not of
  `SecondEquation.W2SourceInput`, so the incoming statements carry it.
* Nothing here is conditional on integrality, on the genus of the source, on
  the degree, or on nonsingularity of any member of a limit family.

## Non-vacuity

§10 instantiates on the caterpillar of loops `T^CL_g`: `simpleTarget_catTree`,
`rowUnramified_cat` and `rowTargetInjective_cat` inhabit the three predicates
that are carried as hypotheses elsewhere, and the three `example`s evaluate the
square consequence, the rectangular consequence and the unconditional
trichotomy there.  No structure is introduced by this file; the predicates
it defines (`OnRow`, `RowUnramified`, `RowRamificationAtMostOne`,
`IsRowTransition`, `RowAtMostOneTransition`, `RowAvoidsLeaves`, `SimpleTarget`,
`RowTargetInjective`) are all inhabited there, except `IsRowTransition`, which
is inhabited exactly by `lemma-edge-deno` case (c) and is deliberately empty on
the caterpillar.

## Consumers

The row-denominator trichotomy of `Count.EdgeDenominator`
(`EdgeDenominator.rowDenominator_trichotomy`), the incoming row denominators of the wall
families (`Count.TrivalentWeight`, `Count.IncomingSimpleColumn`), and through them the
balancing identities at walls and the equal multiplicities across type changes.
-/

namespace DraismaVargas.Count.RowWalk

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableLocalProperties
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.IndexPattern

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}

/-! ## 1.  The ordered walk of a stable row, with no square labelling -/

/-- **`edge` is displayed on the stable row `path`**: it survives pruning and
its stable-path class is `path`. -/
def OnRow (data : GluingDatum target degree) (path : StablePath data)
    (edge : data.SourceEdge) : Prop :=
  ∃ hSurvives : ¬ IsDangling data edge,
    NonDanglingEdge.stablePath (⟨edge, hSurvives⟩ : NonDanglingEdge data) = path

theorem OnRow.survives {path : StablePath data} {edge : data.SourceEdge}
    (h : OnRow data path edge) : ¬ IsDangling data edge := h.choose

/-- `OnRow` is the membership of the rectangular row set of `Count.TrivalentWeight`. -/
theorem onRow_iff_mem_incomingRowEdges (path : StablePath data) (edge : data.SourceEdge) :
    OnRow data path edge ↔ edge ∈ TrivalentWeight.incomingRowEdges data path :=
  (TrivalentWeight.mem_incomingRowEdges path edge).symm

/-- A chosen surviving representative of a stable-path class.  Unlike
`StableLengthMatrixLabelling.rowRepresentative` this needs no labelling. -/
noncomputable def pathRepresentative (path : StablePath data) : NonDanglingEdge data :=
  (Quot.exists_rep path).choose

theorem pathRepresentative_stablePath (path : StablePath data) :
    (pathRepresentative path).stablePath = path :=
  (Quot.exists_rep path).choose_spec

/-- A chosen end of the stable row `path`. -/
noncomputable def startEdge (hEnds : HasPathEnds data) (path : StablePath data) :
    NonDanglingEdge data :=
  (hEnds (pathRepresentative path)).choose

/-- The vertex through which the walk of `path` starts. -/
noncomputable def startVertex (hEnds : HasPathEnds data) (path : StablePath data) :
    data.SourceVertex :=
  (hEnds (pathRepresentative path)).choose_spec.choose

theorem startEdge_stablePath (hEnds : HasPathEnds data) (path : StablePath data) :
    (startEdge hEnds path).stablePath = path :=
  ((hEnds (pathRepresentative path)).choose_spec.choose_spec).1.trans
    (pathRepresentative_stablePath path)

theorem startEdge_isPathEnd (hEnds : HasPathEnds data) (path : StablePath data) :
    IsPathEnd data (startEdge hEnds path).1 (startVertex hEnds path) :=
  ((hEnds (pathRepresentative path)).choose_spec.choose_spec).2

/-- **The ordered walk of a stable row.**  Same traversal as
`StableLengthMatrixLabelling.orderedPath`, indexed by the stable-path class
instead of by a square labelling's coordinate, so that it is available at a
codimension-one limit. -/
noncomputable def orderedRow (hEnds : HasPathEnds data) (path : StablePath data) :
    List data.SourceEdge :=
  traverse data ∅ (startEdge hEnds path).1 (startVertex hEnds path)

theorem mem_orderedRow_iff (hEnds : HasPathEnds data) (path : StablePath data)
    (edge : data.SourceEdge) :
    edge ∈ orderedRow hEnds path ↔ OnRow data path edge := by
  constructor
  · intro hMem
    obtain ⟨hSurvives, hPath⟩ := traverse_stablePath data ∅
      (startEdge hEnds path).1 (startVertex hEnds path) (startEdge hEnds path).2 edge hMem
    exact ⟨hSurvives, hPath.trans (startEdge_stablePath hEnds path)⟩
  · rintro ⟨hSurvives, hPath⟩
    exact mem_traverse_of_stablePath_eq data (startEdge_isPathEnd hEnds path)
      ⟨edge, hSurvives⟩ (hPath.trans (startEdge_stablePath hEnds path).symm)

theorem orderedRow_nodup (hEnds : HasPathEnds data) (path : StablePath data) :
    (orderedRow hEnds path).Nodup :=
  (traverse_nodup_notMem data ∅ (startEdge hEnds path).1 (startVertex hEnds path)).1

/-- **Consecutive entries of the walk meet at a surviving valency-two vertex.**
This is the ordering the pointwise index lemmas lack. -/
theorem orderedRow_chain (hEnds : HasPathEnds data) (path : StablePath data) :
    (orderedRow hEnds path).IsChain fun first second ↦
      ∃ vertex : data.SourceVertex, Incident data first vertex ∧
        Incident data second vertex ∧ nonDanglingValency data vertex = 2 :=
  traverse_chain data ∅ (startEdge hEnds path).1 (startVertex hEnds path)

theorem orderedRow_head? (hEnds : HasPathEnds data) (path : StablePath data) :
    (orderedRow hEnds path).head? = some (startEdge hEnds path).1 :=
  traverse_head?_eq_some data ∅ (startEdge hEnds path).1 (startVertex hEnds path) (by simp)

theorem startEdge_mem_orderedRow (hEnds : HasPathEnds data) (path : StablePath data) :
    (startEdge hEnds path).1 ∈ orderedRow hEnds path :=
  (mem_orderedRow_iff hEnds path _).mpr
    ⟨(startEdge hEnds path).2, startEdge_stablePath hEnds path⟩

/-! ### The two survivors at a surviving valency-two vertex -/

theorem exists_pair_of_nonDanglingValency_two {vertex : data.SourceVertex}
    (hValency : nonDanglingValency data vertex = 2) :
    ∃ first second : data.SourceEdge, first ≠ second ∧
      ¬ IsDangling data first ∧ Incident data first vertex ∧
      ¬ IsDangling data second ∧ Incident data second vertex := by
  classical
  have hCard : ((Finset.univ : Finset data.SourceEdge).filter
      fun edge ↦ ¬ IsDangling data edge ∧ Incident data edge vertex).card = 2 := by
    rw [← hValency, nonDanglingValency]
    congr 1
    ext edge
    simp
  obtain ⟨first, second, hNe, hPair⟩ := Finset.card_eq_two.mp hCard
  have hFirst : first ∈ (Finset.univ : Finset data.SourceEdge).filter
      fun edge ↦ ¬ IsDangling data edge ∧ Incident data edge vertex := by
    rw [hPair]; exact Finset.mem_insert_self _ _
  have hSecond : second ∈ (Finset.univ : Finset data.SourceEdge).filter
      fun edge ↦ ¬ IsDangling data edge ∧ Incident data edge vertex := by
    rw [hPair]; simp
  exact ⟨first, second, hNe, (Finset.mem_filter.mp hFirst).2.1,
    (Finset.mem_filter.mp hFirst).2.2, (Finset.mem_filter.mp hSecond).2.1,
    (Finset.mem_filter.mp hSecond).2.2⟩

/-- **The walk does not leave its row**: the partner of a row occurrence at a
surviving valency-two vertex lies on the same row. -/
theorem onRow_of_incident {path : StablePath data} {vertex : data.SourceVertex}
    (hValency : nonDanglingValency data vertex = 2)
    {edge partner : data.SourceEdge} (hEdge : OnRow data path edge)
    (hIncident : Incident data edge vertex)
    (hPartnerSurvives : ¬ IsDangling data partner)
    (hPartnerIncident : Incident data partner vertex) :
    OnRow data path partner := by
  obtain ⟨hSurvives, hPath⟩ := hEdge
  by_cases hEq : partner = edge
  · exact ⟨hPartnerSurvives, by
      rw [show (⟨partner, hPartnerSurvives⟩ : NonDanglingEdge data) =
        ⟨edge, hSurvives⟩ from Subtype.ext hEq]; exact hPath⟩
  · refine ⟨hPartnerSurvives, ?_⟩
    have hCons : Consecutive data (⟨edge, hSurvives⟩ : NonDanglingEdge data)
        ⟨partner, hPartnerSurvives⟩ :=
      ⟨fun hEq' ↦ hEq (congrArg Subtype.val hEq').symm, vertex, hIncident,
        hPartnerIncident, hValency⟩
    exact (stablePath_eq_of_consecutive hCons).symm.trans hPath

/-! ## 2.  The local step, from dangling-no-glue alone -/

/-- **`m(e_a) + m(e_{a+1}) = 2 m(A) - r(A)` from dangling-no-glue alone.**
`Count.IndexPattern.sourceEdgeIndex_add_sourceEdgeIndex` proves this with a
`FullDimensionalSourcePresentation` in scope; the only field of it that the
proof uses is `danglingEdgeNoGlue`, and the codimension-one wall interface
`SecondEquation.W2SourceInput` carries that field outright. -/
theorem sourceEdgeIndex_add_sourceEdgeIndex_of_noGlue
    (hNoGlue : DanglingEdgeNoGlue data) {vertex : data.SourceVertex}
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
    rw [hNoGlue edge.1 (not_not.mp hDangling)]
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

/-- **An unramified surviving valency-two vertex preserves the index**, from
dangling-no-glue alone.  `prop-local`(r0). -/
theorem sourceEdgeIndex_eq_of_localRamification_eq_zero_of_noGlue
    (hNoGlue : DanglingEdgeNoGlue data) {vertex : data.SourceVertex}
    (hValency : nonDanglingValency data vertex = 2)
    (hZero : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 0)
    {first second : data.SourceEdge}
    (hFirstSurvives : ¬ IsDangling data first) (hFirstIncident : Incident data first vertex)
    (hSecondSurvives : ¬ IsDangling data second)
    (hSecondIncident : Incident data second vertex) :
    data.sourceEdgeIndex first = data.sourceEdgeIndex second := by
  by_cases hNe : first = second
  · rw [hNe]
  have hSum := sourceEdgeIndex_add_sourceEdgeIndex_of_noGlue hNoGlue hValency hFirstSurvives
    hFirstIncident hSecondSurvives hSecondIncident hNe
  rw [hZero] at hSum
  have hFirstLe : data.sourceEdgeIndex first ≤
      (data.vertexPartition vertex.1.1).blockCard vertex.1.2 :=
    sourceEdgeIndex_le_blockCard data vertex ⟨first, hFirstIncident⟩
  have hSecondLe : data.sourceEdgeIndex second ≤
      (data.vertexPartition vertex.1.1).blockCard vertex.1.2 :=
    sourceEdgeIndex_le_blockCard data vertex ⟨second, hSecondIncident⟩
  omega

/-- **At a transition the two indices differ by exactly one**, from
dangling-no-glue alone. -/
theorem sourceEdgeIndex_sub_eq_one_of_transition_of_noGlue
    (hNoGlue : DanglingEdgeNoGlue data) {vertex : data.SourceVertex}
    (hValency : nonDanglingValency data vertex = 2)
    (hRamified : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 1)
    {first second : data.SourceEdge}
    (hFirstSurvives : ¬ IsDangling data first) (hFirstIncident : Incident data first vertex)
    (hSecondSurvives : ¬ IsDangling data second)
    (hSecondIncident : Incident data second vertex) (hNe : first ≠ second) :
    data.sourceEdgeIndex first = data.sourceEdgeIndex second + 1 ∨
      data.sourceEdgeIndex second = data.sourceEdgeIndex first + 1 := by
  have hSum := sourceEdgeIndex_add_sourceEdgeIndex_of_noGlue hNoGlue hValency hFirstSurvives
    hFirstIncident hSecondSurvives hSecondIncident hNe
  rw [hRamified] at hSum
  have hFirstLe : data.sourceEdgeIndex first ≤
      (data.vertexPartition vertex.1.1).blockCard vertex.1.2 :=
    sourceEdgeIndex_le_blockCard data vertex ⟨first, hFirstIncident⟩
  have hSecondLe : data.sourceEdgeIndex second ≤
      (data.vertexPartition vertex.1.1).blockCard vertex.1.2 :=
    sourceEdgeIndex_le_blockCard data vertex ⟨second, hSecondIncident⟩
  omega

/-! ## 3.  The list engine -/

/-- A chain whose relation preserves `f` on elements satisfying `P` is constant
at its head. -/
theorem chain_eq_head {α β : Type*} (f : α → β) (R : α → α → Prop) (P : α → Prop)
    (hStep : ∀ a b, P a → P b → R a b → f a = f b) :
    ∀ (L : List α) (hd : α), (∀ x ∈ L, P x) → L.IsChain R → L.head? = some hd →
      ∀ x ∈ L, f x = f hd := by
  intro L
  induction L with
  | nil => intro hd _ _ hHead; simp at hHead
  | cons a t ih =>
    intro hd hP hChain hHead x hx
    simp only [List.head?_cons, Option.some.injEq] at hHead
    subst hHead
    cases t with
    | nil => rw [List.mem_singleton.mp hx]
    | cons b t' =>
      obtain ⟨hR, hTail⟩ := List.isChain_cons_cons.mp hChain
      rcases List.mem_cons.mp hx with hEq | hx'
      · rw [hEq]
      · have hPt : ∀ y ∈ b :: t', P y := fun y hy ↦ hP y (List.mem_cons_of_mem _ hy)
        exact (ih b hPt hTail (by simp) x hx').trans
          (hStep a b (hP a (List.mem_cons_self ..))
            (hP b (List.mem_cons_of_mem _ (List.mem_cons_self ..))) hR).symm

theorem chain_const {α β : Type*} (f : α → β) (R : α → α → Prop) (P : α → Prop)
    (hStep : ∀ a b, P a → P b → R a b → f a = f b) (L : List α)
    (hP : ∀ x ∈ L, P x) (hChain : L.IsChain R) {x y : α} (hx : x ∈ L) (hy : y ∈ L) :
    f x = f y := by
  cases hL : L with
  | nil => rw [hL] at hx; simp at hx
  | cons a t =>
    subst hL
    have hHead : (a :: t).head? = some a := by simp
    exact (chain_eq_head f R P hStep (a :: t) a hP hChain hHead x hx).trans
      (chain_eq_head f R P hStep (a :: t) a hP hChain hHead y hy).symm

/-- **At most one jump on a chain gives two consecutive values.**  The
uniqueness hypothesis says every jump uses the same unordered pair. -/
theorem chain_two_valued {α : Type*} (f : α → ℕ) (R : α → α → Prop) (P : α → Prop)
    (J : α → α → Prop)
    (hStep : ∀ a b, P a → P b → R a b → f a = f b ∨ J a b)
    (hJump : ∀ a b, P a → P b → J a b → f a = f b + 1 ∨ f b = f a + 1) :
    ∀ L : List α, (∀ x ∈ L, P x) → L.Nodup → L.IsChain R →
      (∀ a b c d : α, a ∈ L → b ∈ L → c ∈ L → d ∈ L → J a b → J c d → c = a ∨ c = b) →
      ∃ k : ℕ, ∀ x ∈ L, f x = k ∨ f x = k + 1 := by
  intro L
  induction L with
  | nil => intro _ _ _ _; exact ⟨0, by simp⟩
  | cons a t ih =>
    intro hP hNodup hChain hUnique
    cases t with
    | nil => exact ⟨f a, by intro x hx; rw [List.mem_singleton.mp hx]; exact Or.inl rfl⟩
    | cons b t' =>
      obtain ⟨hR, hTail⟩ := List.isChain_cons_cons.mp hChain
      have hNotMem : a ∉ b :: t' := (List.nodup_cons.mp hNodup).1
      have hPt : ∀ x ∈ b :: t', P x := fun x hx ↦ hP x (List.mem_cons_of_mem _ hx)
      have hPa : P a := hP a (List.mem_cons_self ..)
      have hPb : P b := hPt b (List.mem_cons_self ..)
      have hUniqueTail : ∀ c d e g : α, c ∈ b :: t' → d ∈ b :: t' → e ∈ b :: t' →
          g ∈ b :: t' → J c d → J e g → e = c ∨ e = d := by
        intro c d e g hc hd he hg hcd heg
        exact hUnique c d e g (List.mem_cons_of_mem _ hc) (List.mem_cons_of_mem _ hd)
          (List.mem_cons_of_mem _ he) (List.mem_cons_of_mem _ hg) hcd heg
      obtain ⟨k, hk⟩ := ih hPt (List.nodup_cons.mp hNodup).2 hTail hUniqueTail
      rcases hStep a b hPa hPb hR with hEq | hJ
      · refine ⟨k, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with hxa | hxt
        · rw [hxa, hEq]; exact hk b (List.mem_cons_self ..)
        · exact hk x hxt
      · have hTailFlat : ∀ c d, P c → P d → c ∈ b :: t' → d ∈ b :: t' → R c d → f c = f d := by
          intro c d hPc hPd hc hd hcd
          rcases hStep c d hPc hPd hcd with hFlat | hJcd
          · exact hFlat
          · exfalso
            rcases hUnique c d a b (List.mem_cons_of_mem _ hc) (List.mem_cons_of_mem _ hd)
              (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
              hJcd hJ with hEq | hEq
            · exact hNotMem (hEq ▸ hc)
            · exact hNotMem (hEq ▸ hd)
        have hConst : ∀ x ∈ b :: t', f x = f b := by
          intro x hx
          refine chain_eq_head f R (fun y ↦ P y ∧ y ∈ b :: t') ?_ (b :: t') b
            (fun y hy ↦ ⟨hPt y hy, hy⟩) hTail (by simp) x hx
          rintro c d ⟨hPc, hc⟩ ⟨hPd, hd⟩ hcd
          exact hTailFlat c d hPc hPd hc hd hcd
        rcases hJump a b hPa hPb hJ with hCase | hCase
        · refine ⟨f b, ?_⟩
          intro x hx
          rcases List.mem_cons.mp hx with hxa | hxt
          · exact Or.inr (hxa ▸ hCase)
          · exact Or.inl (hConst x hxt)
        · refine ⟨f a, ?_⟩
          intro x hx
          rcases List.mem_cons.mp hx with hxa | hxt
          · exact Or.inl (by rw [hxa])
          · exact Or.inr ((hConst x hxt).trans hCase)

end DraismaVargas.Count.RowWalk

namespace DraismaVargas.Count.RowWalk

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableLocalProperties
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.IndexPattern

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}

/-! ## 4.  The four row predicates -/

/-- **The row carries no ramified interior vertex.**  This is the hypothesis
under which the indices along the row are constant; `lemma-edge-deno` (c) is
precisely its failure. -/
def RowUnramified (data : GluingDatum target degree) (path : StablePath data) : Prop :=
  ∀ (vertex : data.SourceVertex) (edge : data.SourceEdge), OnRow data path edge →
    Incident data edge vertex → nonDanglingValency data vertex = 2 →
    data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 0

/-- **Every interior vertex of the row is unramified or a transition.**  On a
leaf-avoiding row of a full-dimensional morphism this is a theorem
(`rowRamificationAtMostOne_of_rowAvoidsLeaves`); the excluded case `r = 2` is
the hairpin above a leaf. -/
def RowRamificationAtMostOne (data : GluingDatum target degree)
    (path : StablePath data) : Prop :=
  ∀ (vertex : data.SourceVertex) (edge : data.SourceEdge), OnRow data path edge →
    Incident data edge vertex → nonDanglingValency data vertex = 2 →
    data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 0 ∨
      data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 1

/-- **A transition vertex of the row**: an interior vertex of the row with
`r_φ = 1`, where the index changes by one. -/
def IsRowTransition (data : GluingDatum target degree) (path : StablePath data)
    (vertex : data.SourceVertex) : Prop :=
  nonDanglingValency data vertex = 2 ∧
    data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 1 ∧
    ∃ edge : data.SourceEdge, OnRow data path edge ∧ Incident data edge vertex

/-- **At most one transition on the row.** -/
def RowAtMostOneTransition (data : GluingDatum target degree)
    (path : StablePath data) : Prop :=
  ∀ first second : data.SourceVertex, IsRowTransition data path first →
    IsRowTransition data path second → first = second

/-- **The row avoids leaves**: no displayed occurrence lies above a target
occurrence incident to a leaf.  Compare
`Count.EdgeDenominator.PassesAboveLeaf`. -/
def RowAvoidsLeaves (data : GluingDatum target degree) (path : StablePath data) : Prop :=
  ∀ edge : data.SourceEdge, OnRow data path edge → ∀ vertex : target.V,
    Count.IsLeafVertex target vertex → edge.1.1 ∉ GluingDatum.incidentEdges vertex

theorem RowUnramified.rowRamificationAtMostOne {path : StablePath data}
    (h : RowUnramified data path) : RowRamificationAtMostOne data path :=
  fun vertex edge hEdge hIncident hValency ↦
    Or.inl (h vertex edge hEdge hIncident hValency)

theorem RowUnramified.not_isRowTransition {path : StablePath data}
    (h : RowUnramified data path) (vertex : data.SourceVertex) :
    ¬ IsRowTransition data path vertex := by
  rintro ⟨hValency, hRamified, edge, hEdge, hIncident⟩
  rw [h vertex edge hEdge hIncident hValency] at hRamified
  exact absurd hRamified (by decide)

theorem RowUnramified.rowAtMostOneTransition {path : StablePath data}
    (h : RowUnramified data path) : RowAtMostOneTransition data path :=
  fun first _ hFirst _ ↦ absurd hFirst (h.not_isRowTransition first)

/-- **`RowUnramified` is exactly "no transition"** once the ramification is
bounded by one. -/
theorem rowUnramified_iff_forall_not_isRowTransition {path : StablePath data}
    (hTame : RowRamificationAtMostOne data path) :
    RowUnramified data path ↔ ∀ vertex : data.SourceVertex,
      ¬ IsRowTransition data path vertex := by
  refine ⟨fun h ↦ h.not_isRowTransition, fun h vertex edge hEdge hIncident hValency ↦ ?_⟩
  rcases hTame vertex edge hEdge hIncident hValency with hZero | hOne
  · exact hZero
  · exact absurd ⟨hValency, hOne, edge, hEdge, hIncident⟩ (h vertex)

/-- A row with a single displayed occurrence is unramified: an interior vertex
would supply a second one. -/
theorem rowUnramified_of_unique (path : StablePath data)
    (hUnique : ∀ first second : data.SourceEdge, OnRow data path first →
      OnRow data path second → first = second) :
    RowUnramified data path := by
  intro vertex edge hEdge hIncident hValency
  exfalso
  obtain ⟨first, second, hNe, hFirstS, hFirstI, hSecondS, hSecondI⟩ :=
    exists_pair_of_nonDanglingValency_two hValency
  exact hNe (hUnique first second
    (onRow_of_incident hValency hEdge hIncident hFirstS hFirstI)
    (onRow_of_incident hValency hEdge hIncident hSecondS hSecondI))

/-! ## 5.  The two walk theorems -/

/-- **Constancy along the ordered walk.**  Every occurrence displayed on an
unramified row carries the same index.  Full-dimensionality is not used: only
`HasPathEnds` (no stable path is a cycle) and dangling-no-glue, both of which
the codimension-one wall interface supplies or carries. -/
theorem sourceEdgeIndex_eq_of_rowUnramified
    (hNoGlue : DanglingEdgeNoGlue data) (hEnds : HasPathEnds data)
    {path : StablePath data} (hUnram : RowUnramified data path)
    {first second : data.SourceEdge} (hFirst : OnRow data path first)
    (hSecond : OnRow data path second) :
    data.sourceEdgeIndex first = data.sourceEdgeIndex second := by
  refine chain_const (fun edge ↦ data.sourceEdgeIndex edge)
    (fun a b ↦ ∃ vertex : data.SourceVertex, Incident data a vertex ∧
      Incident data b vertex ∧ nonDanglingValency data vertex = 2)
    (OnRow data path) ?_ (orderedRow hEnds path)
    (fun x hx ↦ (mem_orderedRow_iff hEnds path x).mp hx)
    (orderedRow_chain hEnds path)
    ((mem_orderedRow_iff hEnds path first).mpr hFirst)
    ((mem_orderedRow_iff hEnds path second).mpr hSecond)
  rintro a b hA hB ⟨vertex, hAI, hBI, hValency⟩
  exact sourceEdgeIndex_eq_of_localRamification_eq_zero_of_noGlue hNoGlue hValency
    (hUnram vertex a hA hAI hValency) hA.survives hAI hB.survives hBI

/-- **Two consecutive values along the ordered walk.**  With `r ≤ 1` at every
interior vertex and at most one transition, the displayed indices are `k` and
`k + 1` for a single `k ≥ 1`.  This is Lemma 2(a)'s index statement, and it is
`Count.EdgeDenominator.RowIndicesConsecutive`. -/
theorem exists_index_two_valued_of_rowAtMostOneTransition
    (hNoGlue : DanglingEdgeNoGlue data) (hEnds : HasPathEnds data)
    {path : StablePath data} (hTame : RowRamificationAtMostOne data path)
    (hOne : RowAtMostOneTransition data path) :
    ∃ index : ℕ, 0 < index ∧ ∀ edge : data.SourceEdge, OnRow data path edge →
      data.sourceEdgeIndex edge = index ∨ data.sourceEdgeIndex edge = index + 1 := by
  classical
  set R : data.SourceEdge → data.SourceEdge → Prop :=
    fun a b ↦ ∃ vertex : data.SourceVertex, Incident data a vertex ∧
      Incident data b vertex ∧ nonDanglingValency data vertex = 2 with hR
  set J : data.SourceEdge → data.SourceEdge → Prop :=
    fun a b ↦ a ≠ b ∧ ∃ vertex : data.SourceVertex, Incident data a vertex ∧
      Incident data b vertex ∧ nonDanglingValency data vertex = 2 ∧
      data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 1 with hJ
  have hStep : ∀ a b, OnRow data path a → OnRow data path b → R a b →
      data.sourceEdgeIndex a = data.sourceEdgeIndex b ∨ J a b := by
    rintro a b hA hB ⟨vertex, hAI, hBI, hValency⟩
    by_cases hNe : a = b
    · exact Or.inl (by rw [hNe])
    · rcases hTame vertex a hA hAI hValency with hZero | hRamified
      · exact Or.inl (sourceEdgeIndex_eq_of_localRamification_eq_zero_of_noGlue hNoGlue
          hValency hZero hA.survives hAI hB.survives hBI)
      · exact Or.inr ⟨hNe, vertex, hAI, hBI, hValency, hRamified⟩
  have hJumpStep : ∀ a b, OnRow data path a → OnRow data path b → J a b →
      data.sourceEdgeIndex a = data.sourceEdgeIndex b + 1 ∨
        data.sourceEdgeIndex b = data.sourceEdgeIndex a + 1 := by
    rintro a b hA hB ⟨hNe, vertex, hAI, hBI, hValency, hRamified⟩
    exact sourceEdgeIndex_sub_eq_one_of_transition_of_noGlue hNoGlue hValency hRamified
      hA.survives hAI hB.survives hBI hNe
  have hUnique : ∀ a b c d : data.SourceEdge, a ∈ orderedRow hEnds path →
      b ∈ orderedRow hEnds path → c ∈ orderedRow hEnds path →
      d ∈ orderedRow hEnds path → J a b → J c d → c = a ∨ c = b := by
    rintro a b c d hAmem hBmem hCmem hDmem
      ⟨hNeAB, vertexA, haI, hbI, hValA, hRamA⟩ ⟨hNeCD, vertexC, hcI, hdI, hValC, hRamC⟩
    have hA : OnRow data path a := (mem_orderedRow_iff hEnds path a).mp hAmem
    have hC : OnRow data path c := (mem_orderedRow_iff hEnds path c).mp hCmem
    have hEq : vertexC = vertexA :=
      hOne vertexC vertexA ⟨hValC, hRamC, c, hC, hcI⟩ ⟨hValA, hRamA, a, hA, haI⟩
    subst hEq
    exact eq_or_eq_of_nonDanglingValency_two hValA hA.survives haI
      ((mem_orderedRow_iff hEnds path b).mp hBmem).survives hbI hNeAB hC.survives hcI
  obtain ⟨k, hk⟩ := chain_two_valued (fun edge ↦ data.sourceEdgeIndex edge) R
    (OnRow data path) J hStep hJumpStep (orderedRow hEnds path)
    (fun x hx ↦ (mem_orderedRow_iff hEnds path x).mp hx)
    (orderedRow_nodup hEnds path) (orderedRow_chain hEnds path) hUnique
  by_cases hZero : k = 0
  · refine ⟨1, Nat.one_pos, ?_⟩
    intro edge hEdge
    have hPos := GluingDatum.sourceEdgeIndex_pos data edge
    rcases hk edge ((mem_orderedRow_iff hEnds path edge).mpr hEdge) with hCase | hCase
    · omega
    · exact Or.inl (by omega)
  · exact ⟨k, Nat.pos_of_ne_zero hZero, fun edge hEdge ↦
      hk edge ((mem_orderedRow_iff hEnds path edge).mpr hEdge)⟩

end DraismaVargas.Count.RowWalk

namespace DraismaVargas.Count.RowWalk

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableLocalProperties
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.IndexPattern

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-! ## 6.  The square labelling, leaf avoidance, and `hPairs` -/

omit [Fintype coordinate] in
/-- The square row set of `Count.EdgeDenominator` is the walk's row. -/
theorem mem_rowEdges_iff_onRow (labelling : StableLengthMatrixLabelling data coordinate)
    (sourceRow : coordinate) (edge : data.SourceEdge) :
    edge ∈ EdgeDenominator.rowEdges labelling sourceRow ↔
      OnRow data (labelling.row.symm sourceRow) edge := by
  rw [EdgeDenominator.mem_rowEdges]
  constructor
  · rintro ⟨hSurvives, hRow⟩
    exact ⟨hSurvives, (Equiv.eq_symm_apply _).mpr hRow⟩
  · rintro ⟨hSurvives, hRow⟩
    exact ⟨hSurvives, (Equiv.eq_symm_apply _).mp hRow⟩

omit [Fintype coordinate] in
/-- **The square and the rectangular row sets agree.**  This is what makes one
walk statement serve both `Count.EdgeDenominator` and the rectangular interface of
`Count.TrivalentWeight`. -/
theorem rowEdges_eq_incomingRowEdges
    (labelling : StableLengthMatrixLabelling data coordinate) (sourceRow : coordinate) :
    EdgeDenominator.rowEdges labelling sourceRow =
      TrivalentWeight.incomingRowEdges data (labelling.row.symm sourceRow) := by
  ext edge
  rw [mem_rowEdges_iff_onRow, onRow_iff_mem_incomingRowEdges]

omit [Fintype coordinate] in
theorem rowAvoidsLeaves_iff_not_passesAboveLeaf
    (labelling : StableLengthMatrixLabelling data coordinate) (sourceRow : coordinate) :
    RowAvoidsLeaves data (labelling.row.symm sourceRow) ↔
      ¬ EdgeDenominator.PassesAboveLeaf labelling sourceRow := by
  constructor
  · rintro hAvoid ⟨edge, hEdge, vertex, hLeaf, hMem⟩
    exact hAvoid edge ((mem_rowEdges_iff_onRow labelling sourceRow edge).mp hEdge)
      vertex hLeaf hMem
  · intro hNot edge hEdge vertex hLeaf hMem
    exact hNot ⟨edge, (mem_rowEdges_iff_onRow labelling sourceRow edge).mpr hEdge,
      vertex, hLeaf, hMem⟩

/-- **A leaf-avoiding row of a full-dimensional morphism has `r ≤ 1` at every
interior vertex.**  Change-minimality gives `r ≤ 3 - val`, and leaf avoidance
excludes `val = 1`, where `r = 2` (the hairpin) would be possible. -/
theorem rowRamificationAtMostOne_of_rowAvoidsLeaves
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} (hAvoid : RowAvoidsLeaves data path) :
    RowRamificationAtMostOne data path := by
  intro vertex edge hEdge hIncident _
  have hMem : edge.1.1 ∈ GluingDatum.incidentEdges vertex.1.1 :=
    target_mem_of_incident hIncident
  have hNonneg := data.localRamification_nonneg vertex.1.1 (fd.valid.2 vertex.1.1)
    ⟨vertex.1.2, vertex.2⟩
  have hLe := localRamification_le_targetChange fd (wall := vertex.1.1) ⟨vertex.1.2, vertex.2⟩
  rw [targetChange_eq_three_sub_valency fd vertex.1.1] at hLe
  have hCardPos : 0 < (GluingDatum.incidentEdges vertex.1.1).card :=
    Finset.card_pos.mpr ⟨edge.1.1, hMem⟩
  have hNotLeaf : (GluingDatum.incidentEdges vertex.1.1).card ≠ 1 := fun hOne ↦
    hAvoid edge hEdge vertex.1.1 hOne hMem
  omega

/-- **A transition on a leaf-avoiding row lies over a divalent target vertex.**
`prop-local`(r1). -/
theorem card_incidentEdges_eq_two_of_isRowTransition
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} (hAvoid : RowAvoidsLeaves data path)
    {vertex : data.SourceVertex} (hTransition : IsRowTransition data path vertex) :
    (GluingDatum.incidentEdges vertex.1.1).card = 2 := by
  obtain ⟨_, hRamified, edge, hEdge, hIncident⟩ := hTransition
  have hMem : edge.1.1 ∈ GluingDatum.incidentEdges vertex.1.1 :=
    target_mem_of_incident hIncident
  have hLe := incidentEdges_card_le_two_of_localRamification_pos fd
    (wall := vertex.1.1) ⟨vertex.1.2, vertex.2⟩ (by omega)
  have hCardPos : 0 < (GluingDatum.incidentEdges vertex.1.1).card :=
    Finset.card_pos.mpr ⟨edge.1.1, hMem⟩
  have hNotLeaf : (GluingDatum.incidentEdges vertex.1.1).card ≠ 1 := fun hOne ↦
    hAvoid edge hEdge vertex.1.1 hOne hMem
  omega

/-- **Two ramified blocks over one divalent target vertex coincide.**  The
change budget at a divalent target vertex of a full-dimensional datum is one
(`targetChange_divalent`), so `localRamification_eq_zero_of_ne` applies. -/
theorem sourceVertex_eq_of_localRamification_eq_one
    (fd : FullDimensionalSourcePresentation data coordinate)
    {vertexA vertexB : data.SourceVertex}
    (hWall : vertexA.1.1 = vertexB.1.1)
    (hDivalent : (GluingDatum.incidentEdges vertexA.1.1).card = 2)
    (hRamifiedA : data.localRamification vertexA.1.1 ⟨vertexA.1.2, vertexA.2⟩ = 1)
    (hRamifiedB : data.localRamification vertexB.1.1 ⟨vertexB.1.2, vertexB.2⟩ = 1) :
    vertexA = vertexB := by
  obtain ⟨⟨wa, sa⟩, ha⟩ := vertexA
  obtain ⟨⟨wb, sb⟩, hb⟩ := vertexB
  simp only at hWall hDivalent hRamifiedA hRamifiedB ⊢
  subst hWall
  by_contra hNe
  have hBlockNe : (⟨sb, hb⟩ : (data.vertexPartition wa).Blocks) ≠ ⟨sa, ha⟩ := by
    intro hEq
    exact hNe (by
      have hSheet : sb = sa := congrArg Subtype.val hEq
      subst hSheet
      rfl)
  have hZero := localRamification_eq_zero_of_ne fd hDivalent hRamifiedA hBlockNe
  rw [hZero] at hRamifiedB
  exact absurd hRamifiedB (by decide)

/-- **No two target occurrences join the same two target vertices.**  The global
form of the `num_edges target a b = 1` hypothesis that the Part I wall
interfaces carry at every contraction; it is what `genus target = 0` and
connectedness say about a tree, and it is carried explicitly here. -/
def SimpleTarget (target : CFGraph) : Prop :=
  ∀ (x y : target.V) (first second : target.edges), x ≠ y →
    first ∈ GluingDatum.incidentEdges x → first ∈ GluingDatum.incidentEdges y →
    second ∈ GluingDatum.incidentEdges x → second ∈ GluingDatum.incidentEdges y →
    first = second

/-- **`hPairs` discharged.**  `Count.IndexPattern.not_two_transitions_on_one_row`
leaves open the configuration in which the two transitions use the same
unordered pair of target occurrences; it is exactly a cycle of the target, and
`SimpleTarget` excludes it.  The same-target-vertex case is excluded by the
change budget, not by the target. -/
theorem not_two_transitions_on_one_row_of_simpleTarget
    (fd : FullDimensionalSourcePresentation data coordinate)
    (hSimple : SimpleTarget target)
    {vertexA vertexB : data.SourceVertex}
    (hVertexNe : vertexA ≠ vertexB)
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
        (⟨a₁, ha₁S⟩ : NonDanglingEdge data))) :
    False := by
  refine not_two_transitions_on_one_row fd hDivalentA hDivalentB hRamifiedA hRamifiedB
    hValencyA hValencyB ha₁S ha₁I ha₂S ha₂I haNe hb₁S hb₁I hb₂S hb₂I hbNe hIndexB
    hSameRow ?_
  intro hCase
  have hTargetNeA : a₁.1.1 ≠ a₂.1.1 :=
    target_ne_of_transition fd hDivalentA hRamifiedA hValencyA ha₁S ha₁I ha₂S ha₂I haNe
  have hWallNe : vertexA.1.1 ≠ vertexB.1.1 := fun hEq ↦ hVertexNe
    (sourceVertex_eq_of_localRamification_eq_one fd hEq hDivalentA hRamifiedA hRamifiedB)
  refine hTargetNeA ?_
  rcases hCase with ⟨hOne, hTwo⟩ | ⟨hOne, hTwo⟩
  · exact hSimple vertexA.1.1 vertexB.1.1 a₁.1.1 a₂.1.1 hWallNe
      (target_mem_of_incident ha₁I) (hOne ▸ target_mem_of_incident hb₁I)
      (target_mem_of_incident ha₂I) (hTwo ▸ target_mem_of_incident hb₂I)
  · exact hSimple vertexA.1.1 vertexB.1.1 a₁.1.1 a₂.1.1 hWallNe
      (target_mem_of_incident ha₁I) (hOne ▸ target_mem_of_incident hb₂I)
      (target_mem_of_incident ha₂I) (hTwo ▸ target_mem_of_incident hb₁I)

/-- **At most one transition on a leaf-avoiding row, unconditionally.**  This
is `RowAtMostOneTransition` with no hypothesis beyond `SimpleTarget`. -/
theorem rowAtMostOneTransition_of_simpleTarget
    (fd : FullDimensionalSourcePresentation data coordinate)
    (hSimple : SimpleTarget target) {path : StablePath data}
    (hAvoid : RowAvoidsLeaves data path) :
    RowAtMostOneTransition data path := by
  intro vertexA vertexB hA hB
  by_contra hVertexNe
  obtain ⟨hValencyA, hRamifiedA, edgeA, hEdgeA, hIncidentA⟩ := hA
  obtain ⟨hValencyB, hRamifiedB, edgeB, hEdgeB, hIncidentB⟩ := hB
  have hDivalentA : (GluingDatum.incidentEdges vertexA.1.1).card = 2 :=
    card_incidentEdges_eq_two_of_isRowTransition fd hAvoid
      ⟨hValencyA, hRamifiedA, edgeA, hEdgeA, hIncidentA⟩
  have hDivalentB : (GluingDatum.incidentEdges vertexB.1.1).card = 2 :=
    card_incidentEdges_eq_two_of_isRowTransition fd hAvoid
      ⟨hValencyB, hRamifiedB, edgeB, hEdgeB, hIncidentB⟩
  obtain ⟨a₁, a₂, haNe, ha₁S, ha₁I, ha₂S, ha₂I⟩ :=
    exists_pair_of_nonDanglingValency_two hValencyA
  obtain ⟨b₁, b₂, hbNe, hb₁S, hb₁I, hb₂S, hb₂I⟩ :=
    exists_pair_of_nonDanglingValency_two hValencyB
  have hA₁ : OnRow data path a₁ :=
    onRow_of_incident hValencyA hEdgeA hIncidentA ha₁S ha₁I
  have hB₁ : OnRow data path b₁ :=
    onRow_of_incident hValencyB hEdgeB hIncidentB hb₁S hb₁I
  have hIndexB : data.sourceEdgeIndex b₁ ≠ data.sourceEdgeIndex b₂ := by
    rcases sourceEdgeIndex_sub_eq_one_of_transition_of_noGlue fd.danglingEdgeNoGlue
      hValencyB hRamifiedB hb₁S hb₁I hb₂S hb₂I hbNe with hCase | hCase <;> omega
  have hSameRow : fd.labelling.row (NonDanglingEdge.stablePath
      (⟨b₁, hb₁S⟩ : NonDanglingEdge data)) =
      fd.labelling.row (NonDanglingEdge.stablePath
        (⟨a₁, ha₁S⟩ : NonDanglingEdge data)) := by
    have hPathB : NonDanglingEdge.stablePath (⟨b₁, hb₁S⟩ : NonDanglingEdge data) = path :=
      hB₁.choose_spec
    have hPathA : NonDanglingEdge.stablePath (⟨a₁, ha₁S⟩ : NonDanglingEdge data) = path :=
      hA₁.choose_spec
    rw [hPathA, hPathB]
  exact not_two_transitions_on_one_row_of_simpleTarget fd hSimple hVertexNe
    hDivalentA hDivalentB hRamifiedA hRamifiedB hValencyA hValencyB
    ha₁S ha₁I ha₂S ha₂I haNe hb₁S hb₁I hb₂S hb₂I hbNe hIndexB hSameRow

end DraismaVargas.Count.RowWalk

namespace DraismaVargas.Count.RowWalk

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableLocalProperties
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.IndexPattern

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-! ## 7.  No backtracking along the walk

The target-side half of Lemma 2(a) splits into a *local* statement -- the walk
never leaves a vertex through the target occurrence it entered by -- and a
*global* one -- a non-backtracking walk in a tree never repeats an occurrence.
The first is proved here, for every interior vertex of ramification at most
one; the second is the target-side hypothesis recorded in the module docstring. -/

/-- **Harmonicity in one direction.**  Two distinct source occurrences of one
block above the *same* target occurrence have indices summing to at most the
local degree, because the edge blocks above one target occurrence partition the
vertex block. -/
theorem sourceEdgeIndex_add_le_blockCard (data : GluingDatum target degree)
    {vertex : data.SourceVertex} {first second : data.SourceEdge}
    (hFirstIncident : Incident data first vertex)
    (hSecondIncident : Incident data second vertex)
    (hNe : first ≠ second) (hSame : first.1.1 = second.1.1) :
    data.sourceEdgeIndex first + data.sourceEdgeIndex second ≤
      (data.vertexPartition vertex.1.1).blockCard vertex.1.2 := by
  classical
  obtain ⟨⟨t₁, s₁⟩, h₁⟩ := first
  obtain ⟨⟨t₂, s₂⟩, h₂⟩ := second
  simp only at hSame
  subst hSame
  have hMem : t₁ ∈ GluingDatum.incidentEdges vertex.1.1 :=
    ((incident_iff_target_mem_and_rel data _ vertex).mp hFirstIncident).1
  have hb₁ : (⟨s₁, h₁⟩ : (data.edgePartition t₁).Blocks) ∈
      SheetPartition.blocksWithin (data.edgePartition t₁)
        (data.vertexPartition vertex.1.1) ⟨vertex.1.2, vertex.2⟩ :=
    (SheetPartition.mem_blocksWithin _ _ _ _).mpr
      ((SheetPartition.fineBlockToCoarseBlock_eq_iff_rel _ _ _ _).mpr
        ((incident_iff_target_mem_and_rel data _ vertex).mp hFirstIncident).2)
  have hb₂ : (⟨s₂, h₂⟩ : (data.edgePartition t₁).Blocks) ∈
      SheetPartition.blocksWithin (data.edgePartition t₁)
        (data.vertexPartition vertex.1.1) ⟨vertex.1.2, vertex.2⟩ :=
    (SheetPartition.mem_blocksWithin _ _ _ _).mpr
      ((SheetPartition.fineBlockToCoarseBlock_eq_iff_rel _ _ _ _).mpr
        ((incident_iff_target_mem_and_rel data _ vertex).mp hSecondIncident).2)
  have hBlockNe : (⟨s₁, h₁⟩ : (data.edgePartition t₁).Blocks) ≠ ⟨s₂, h₂⟩ := by
    intro hEq
    exact hNe (Subtype.ext (Prod.ext rfl (congrArg Subtype.val hEq)))
  have hTotal := sum_blockCard_blocksWithin (data.edgePartition t₁)
    (data.vertexPartition vertex.1.1) (refines_of_mem_incidentEdges data hMem)
    ⟨vertex.1.2, vertex.2⟩
  have hSplit := Finset.add_sum_erase
    (SheetPartition.blocksWithin (data.edgePartition t₁)
      (data.vertexPartition vertex.1.1) ⟨vertex.1.2, vertex.2⟩)
    (fun fineBlock ↦ ((data.edgePartition t₁).blockCard fineBlock.1 : ℤ)) hb₁
  have hErase : (⟨s₂, h₂⟩ : (data.edgePartition t₁).Blocks) ∈
      (SheetPartition.blocksWithin (data.edgePartition t₁)
        (data.vertexPartition vertex.1.1) ⟨vertex.1.2, vertex.2⟩).erase ⟨s₁, h₁⟩ :=
    Finset.mem_erase.mpr ⟨Ne.symm hBlockNe, hb₂⟩
  have hSingle : ((data.edgePartition t₁).blockCard s₂ : ℤ) ≤
      ∑ fineBlock ∈ (SheetPartition.blocksWithin (data.edgePartition t₁)
        (data.vertexPartition vertex.1.1) ⟨vertex.1.2, vertex.2⟩).erase ⟨s₁, h₁⟩,
        ((data.edgePartition t₁).blockCard fineBlock.1 : ℤ) :=
    Finset.single_le_sum (f := fun fineBlock : (data.edgePartition t₁).Blocks ↦
      ((data.edgePartition t₁).blockCard fineBlock.1 : ℤ))
      (fun _ _ ↦ by positivity) hErase
  have hCoeFine : ((⟨s₁, h₁⟩ : (data.edgePartition t₁).Blocks) : Fin degree) = s₁ := rfl
  have hCoeCoarse :
      ((⟨vertex.1.2, vertex.2⟩ : (data.vertexPartition vertex.1.1).Blocks) : Fin degree) =
        vertex.1.2 := rfl
  rw [hCoeFine] at hSplit
  rw [hCoeCoarse] at hTotal
  show (data.edgePartition t₁).blockCard s₁ + (data.edgePartition t₁).blockCard s₂ ≤ _
  omega

/-- **No backtracking.**  At a surviving-valency-two source vertex of local
ramification at most one the two survivors lie above *different* target
occurrences.  `Count.IndexPattern.target_ne_of_transition` proves this for
`r = 1` above a divalent target vertex by a counting argument; here it holds for
`r ≤ 1` with no hypothesis on the target vertex, because the two survivors
sharing a direction would force `m(A) ≤ r` while `m(e₁) + m(e₂) ≥ 2` forces
`m(A) ≥ 2`. -/
theorem target_ne_of_localRamification_le_one
    (hNoGlue : DanglingEdgeNoGlue data) {vertex : data.SourceVertex}
    (hValency : nonDanglingValency data vertex = 2)
    (hRamified : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ ≤ 1)
    {first second : data.SourceEdge}
    (hFirstSurvives : ¬ IsDangling data first) (hFirstIncident : Incident data first vertex)
    (hSecondSurvives : ¬ IsDangling data second)
    (hSecondIncident : Incident data second vertex) (hNe : first ≠ second) :
    first.1.1 ≠ second.1.1 := by
  intro hSame
  have hSum := sourceEdgeIndex_add_sourceEdgeIndex_of_noGlue hNoGlue hValency hFirstSurvives
    hFirstIncident hSecondSurvives hSecondIncident hNe
  have hLe := sourceEdgeIndex_add_le_blockCard data hFirstIncident hSecondIncident hNe hSame
  have hFirstPos := GluingDatum.sourceEdgeIndex_pos data first
  have hSecondPos := GluingDatum.sourceEdgeIndex_pos data second
  have hFirstLe : data.sourceEdgeIndex first ≤
      (data.vertexPartition vertex.1.1).blockCard vertex.1.2 :=
    sourceEdgeIndex_le_blockCard data vertex ⟨first, hFirstIncident⟩
  omega

/-- **The ordered walk of a leaf-avoiding row does not backtrack.** -/
theorem target_ne_of_row
    (hNoGlue : DanglingEdgeNoGlue data) {path : StablePath data}
    (hTame : RowRamificationAtMostOne data path) {vertex : data.SourceVertex}
    (hValency : nonDanglingValency data vertex = 2)
    {first second : data.SourceEdge}
    (hFirst : OnRow data path first) (hFirstIncident : Incident data first vertex)
    (hSecond : OnRow data path second) (hSecondIncident : Incident data second vertex)
    (hNe : first ≠ second) :
    first.1.1 ≠ second.1.1 :=
  target_ne_of_localRamification_le_one hNoGlue hValency
    (by rcases hTame vertex first hFirst hFirstIncident hValency with hCase | hCase <;> omega)
    hFirst.survives hFirstIncident hSecond.survives hSecondIncident hNe

/-- **The target-side half of the geodesic statement.**  `φ` is injective on the
occurrences displayed by the row.  `target_ne_of_row` is its local half; the
global half -- a non-backtracking walk in a connected genus-zero target never
repeats a target occurrence -- is pure target combinatorics and is *not* proved
in this repository.  It is carried here as a named hypothesis so that its two
consumers are visible. -/
def RowTargetInjective (data : GluingDatum target degree) (path : StablePath data) : Prop :=
  ∀ first second : data.SourceEdge, OnRow data path first → OnRow data path second →
    first.1.1 = second.1.1 → first = second

/-- **`RowTargetInjective` gives the simple column.**  This is the hypothesis
`Count.TrivalentWeight.dvd_incomingRowDenominator_of_occurrences_eq_singleton`
and `Count.IncomingSimpleColumn`'s background-emptiness both ask for. -/
theorem occurrences_eq_singleton_of_rowTargetInjective
    {path : StablePath data} (hInjective : RowTargetInjective data path)
    {place : target.edges} {edge : data.SourceEdge}
    (hEdge : OnRow data path edge) (hTarget : edge.1.1 = place) :
    StableSourceMatrix.occurrences data path place = {edge} := by
  classical
  refine Finset.eq_singleton_iff_unique_mem.mpr
    ⟨(StableSourceMatrix.mem_occurrences path place edge).mpr ⟨hEdge, hTarget⟩, ?_⟩
  intro other hOther
  obtain ⟨hOnRow, hOtherTarget⟩ :=
    (StableSourceMatrix.mem_occurrences path place other).mp hOther
  exact hInjective other edge hOnRow hEdge (hOtherTarget.trans hTarget.symm)

/-- The **lower** half of the sharp incoming denominator, from
`RowTargetInjective`.  `Count.IncomingSimpleColumn` reaches the same conclusion from a
row-distinctness hypothesis instead; the two routes are independent. -/
theorem dvd_incomingRowDenominator_of_rowTargetInjective
    {path : StablePath data} (hInjective : RowTargetInjective data path)
    {edge : data.SourceEdge} (hEdge : OnRow data path edge) :
    data.sourceEdgeIndex edge ∣ TrivalentWeight.incomingRowDenominator data path :=
  TrivalentWeight.dvd_incomingRowDenominator_of_occurrences_eq_singleton path edge.1.1
    (occurrences_eq_singleton_of_rowTargetInjective hInjective hEdge rfl)

/-! ## 8.  The consequences for the count -/

/-- **The upper half, in the shape the rectangular interface of `Count.TrivalentWeight` wants.**
This is the first hypothesis of
`Count.TrivalentWeight.incomingRowDenominator_eq_of_index_dvd_of_simple` and of
`Count.IncomingSimpleColumn.incomingRowDenominator_secondRow_eq`. -/
theorem forall_index_dvd_of_rowUnramified
    (hNoGlue : DanglingEdgeNoGlue data) (hEnds : HasPathEnds data)
    {path : StablePath data} {edge : data.SourceEdge} (hEdge : OnRow data path edge)
    (hUnram : RowUnramified data path) :
    ∀ other ∈ TrivalentWeight.incomingRowEdges data path,
      data.sourceEdgeIndex other ∣ data.sourceEdgeIndex edge := by
  intro other hOther
  rw [sourceEdgeIndex_eq_of_rowUnramified hNoGlue hEnds hUnram
    ((onRow_iff_mem_incomingRowEdges path other).mpr hOther) hEdge]

/-- **`d₀ ∣ k` on the rectangular incoming matrix.**  The divisibility half of
`lemma-edge-deno` (b) at a codimension-one limit. -/
theorem incomingRowDenominator_dvd_of_rowUnramified
    (hNoGlue : DanglingEdgeNoGlue data) (hEnds : HasPathEnds data)
    {path : StablePath data} {edge : data.SourceEdge} (hEdge : OnRow data path edge)
    (hUnram : RowUnramified data path) :
    TrivalentWeight.incomingRowDenominator data path ∣ data.sourceEdgeIndex edge :=
  TrivalentWeight.incomingRowDenominator_dvd_of_forall_index_dvd path
    (forall_index_dvd_of_rowUnramified hNoGlue hEnds hEdge hUnram)

/-- **`d₀ = k`**, from the two halves this file supplies.  The other route to
the lower half is the column difference of `Count.IncomingSimpleColumn`. -/
theorem incomingRowDenominator_eq_of_rowUnramified_of_rowTargetInjective
    (hNoGlue : DanglingEdgeNoGlue data) (hEnds : HasPathEnds data)
    {path : StablePath data} {edge : data.SourceEdge} (hEdge : OnRow data path edge)
    (hUnram : RowUnramified data path) (hInjective : RowTargetInjective data path) :
    TrivalentWeight.incomingRowDenominator data path = data.sourceEdgeIndex edge :=
  Nat.dvd_antisymm (incomingRowDenominator_dvd_of_rowUnramified hNoGlue hEnds hEdge hUnram)
    (dvd_incomingRowDenominator_of_rowTargetInjective hInjective hEdge)

/-- **`lemma-edge-deno` (b) on a square full-dimensional row**: the row has
constant index. -/
theorem rowIndexConstant_of_rowUnramified
    (fd : FullDimensionalSourcePresentation data coordinate) {sourceRow : coordinate}
    {edge : data.SourceEdge} (hEdge : edge ∈ EdgeDenominator.rowEdges fd.labelling sourceRow)
    (hUnram : RowUnramified data (fd.labelling.row.symm sourceRow)) :
    EdgeDenominator.RowIndexConstant fd.labelling sourceRow (data.sourceEdgeIndex edge) := by
  intro other hOther
  exact sourceEdgeIndex_eq_of_rowUnramified fd.danglingEdgeNoGlue fd.pathEnds hUnram
    ((mem_rowEdges_iff_onRow fd.labelling sourceRow other).mp hOther)
    ((mem_rowEdges_iff_onRow fd.labelling sourceRow edge).mp hEdge)

/-- `d_i ∣ k` on a square full-dimensional row. -/
theorem rowDenominator_dvd_of_rowUnramified
    (fd : FullDimensionalSourcePresentation data coordinate) {sourceRow : coordinate}
    {edge : data.SourceEdge} (hEdge : edge ∈ EdgeDenominator.rowEdges fd.labelling sourceRow)
    (hUnram : RowUnramified data (fd.labelling.row.symm sourceRow)) :
    rowDenominator fd.labelling.presentation sourceRow ∣ data.sourceEdgeIndex edge :=
  EdgeDenominator.rowDenominator_dvd_of_rowIndexConstant fd.labelling sourceRow
    (rowIndexConstant_of_rowUnramified fd hEdge hUnram)

/-- **`Count.EdgeDenominator`'s trichotomy hypothesis, discharged.**  Every row
of a full-dimensional morphism over a simple target has consecutive indices, so
`EdgeDenominator.rowDenominator_trichotomy` becomes unconditional. -/
theorem rowIndicesConsecutive_of_simpleTarget
    (fd : FullDimensionalSourcePresentation data coordinate)
    (hSimple : SimpleTarget target) (sourceRow : coordinate) :
    EdgeDenominator.RowIndicesConsecutive fd.labelling sourceRow := by
  by_cases hPasses : EdgeDenominator.PassesAboveLeaf fd.labelling sourceRow
  · exact EdgeDenominator.rowIndicesConsecutive_of_passesAboveLeaf fd hPasses
  · have hAvoid : RowAvoidsLeaves data (fd.labelling.row.symm sourceRow) :=
      (rowAvoidsLeaves_iff_not_passesAboveLeaf fd.labelling sourceRow).mpr hPasses
    obtain ⟨index, hPos, hTwo⟩ := exists_index_two_valued_of_rowAtMostOneTransition
      fd.danglingEdgeNoGlue fd.pathEnds
      (rowRamificationAtMostOne_of_rowAvoidsLeaves fd hAvoid)
      (rowAtMostOneTransition_of_simpleTarget fd hSimple hAvoid)
    exact ⟨index, hPos, fun other hOther ↦ hTwo other
      ((mem_rowEdges_iff_onRow fd.labelling sourceRow other).mp hOther)⟩

/-- The trichotomy itself, with no hypothesis beyond `SimpleTarget`. -/
theorem rowDenominator_trichotomy_of_simpleTarget
    (fd : FullDimensionalSourcePresentation data coordinate)
    (hSimple : SimpleTarget target) (sourceRow : coordinate) :
    (EdgeDenominator.PassesAboveLeaf fd.labelling sourceRow ∧
        rowDenominator fd.labelling.presentation sourceRow = 1) ∨
      (¬ EdgeDenominator.PassesAboveLeaf fd.labelling sourceRow ∧ ∃ index : ℕ, 0 < index ∧
        EdgeDenominator.RowIndexConstant fd.labelling sourceRow index ∧
        rowDenominator fd.labelling.presentation sourceRow ∣ index) ∨
      (¬ EdgeDenominator.PassesAboveLeaf fd.labelling sourceRow ∧ ∃ index : ℕ, 0 < index ∧
        EdgeDenominator.RowIndexTwoValued fd.labelling sourceRow index ∧
        (∃ edge ∈ EdgeDenominator.rowEdges fd.labelling sourceRow,
          data.sourceEdgeIndex edge = index) ∧
        (∃ edge ∈ EdgeDenominator.rowEdges fd.labelling sourceRow,
          data.sourceEdgeIndex edge = index + 1) ∧
        rowDenominator fd.labelling.presentation sourceRow ∣ index * (index + 1)) :=
  EdgeDenominator.rowDenominator_trichotomy fd sourceRow
    (rowIndicesConsecutive_of_simpleTarget fd hSimple sourceRow)

end DraismaVargas.Count.RowWalk

namespace DraismaVargas.Count.RowWalk

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W2M1kCommonBalance
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.SecondEquation
open DraismaVargas.LocalCases.W2M1kSourceCandidates

/-! ## 9.  The two distinguished rows of `{w2-r2-nd3-M-1k}`

`e₂` and `e₃` have index `k` (`Shape.second_index`, `Shape.third_index`), so the
walk's constancy statement is literally the upper half that
`Count.TrivalentWeight.incomingRowDenominator_eq_of_index_dvd_of_simple` and
`Count.IncomingSimpleColumn` ask for on `h₂` and `h₃`.  The datum here is the
**incoming codimension-one** one; `SecondEquation.W2SourceInput` supplies
`dangling_no_glue` as a field, so only `HasPathEnds data` and `RowUnramified`
remain. -/

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

theorem onRow_secondRow : OnRow data (secondRow profile) profile.second.1 :=
  ⟨profile.second_survives, rfl⟩

theorem onRow_thirdRow : OnRow data (thirdRow profile) profile.third.1 :=
  ⟨profile.third_survives, rfl⟩

/-- **The upper half on `h₂`.**  Hypotheses: the wall interface, no cyclic
stable path, and no transition on `h₂`. -/
theorem forall_index_dvd_secondRow (input : W2SourceInput data star)
    (hEnds : HasPathEnds data) (shape : Shape profile)
    (hUnram : RowUnramified data (secondRow profile)) :
    ∀ edge ∈ TrivalentWeight.incomingRowEdges data (secondRow profile),
      data.sourceEdgeIndex edge ∣ shape.k := by
  intro edge hEdge
  rw [← shape.second_index]
  exact forall_index_dvd_of_rowUnramified input.dangling_no_glue hEnds onRow_secondRow
    hUnram edge hEdge

/-- **The upper half on `h₃`.** -/
theorem forall_index_dvd_thirdRow (input : W2SourceInput data star)
    (hEnds : HasPathEnds data) (shape : Shape profile)
    (hUnram : RowUnramified data (thirdRow profile)) :
    ∀ edge ∈ TrivalentWeight.incomingRowEdges data (thirdRow profile),
      data.sourceEdgeIndex edge ∣ shape.k := by
  intro edge hEdge
  rw [← shape.third_index]
  exact forall_index_dvd_of_rowUnramified input.dangling_no_glue hEnds onRow_thirdRow
    hUnram edge hEdge

/-- `d₀(h₂) ∣ k`. -/
theorem incomingRowDenominator_secondRow_dvd (input : W2SourceInput data star)
    (hEnds : HasPathEnds data) (shape : Shape profile)
    (hUnram : RowUnramified data (secondRow profile)) :
    TrivalentWeight.incomingRowDenominator data (secondRow profile) ∣ shape.k :=
  TrivalentWeight.incomingRowDenominator_dvd_of_forall_index_dvd _
    (forall_index_dvd_secondRow input hEnds shape hUnram)

/-- `d₀(h₃) ∣ k`. -/
theorem incomingRowDenominator_thirdRow_dvd (input : W2SourceInput data star)
    (hEnds : HasPathEnds data) (shape : Shape profile)
    (hUnram : RowUnramified data (thirdRow profile)) :
    TrivalentWeight.incomingRowDenominator data (thirdRow profile) ∣ shape.k :=
  TrivalentWeight.incomingRowDenominator_dvd_of_forall_index_dvd _
    (forall_index_dvd_thirdRow input hEnds shape hUnram)

/-- **The sharp `d₀(h₂) = k`**, if the walk's target-side hypothesis is granted on
`h₂`.  The column-difference route of `Count.IncomingSimpleColumn` reaches the same value
from `secondRow profile ≠ thirdRow profile` instead. -/
theorem incomingRowDenominator_secondRow_eq (input : W2SourceInput data star)
    (hEnds : HasPathEnds data) (shape : Shape profile)
    (hUnram : RowUnramified data (secondRow profile))
    (hInjective : RowTargetInjective data (secondRow profile)) :
    TrivalentWeight.incomingRowDenominator data (secondRow profile) = shape.k :=
  shape.second_index ▸ incomingRowDenominator_eq_of_rowUnramified_of_rowTargetInjective
    input.dangling_no_glue hEnds onRow_secondRow hUnram hInjective

/-- **The sharp `d₀(h₃) = k`.** -/
theorem incomingRowDenominator_thirdRow_eq (input : W2SourceInput data star)
    (hEnds : HasPathEnds data) (shape : Shape profile)
    (hUnram : RowUnramified data (thirdRow profile))
    (hInjective : RowTargetInjective data (thirdRow profile)) :
    TrivalentWeight.incomingRowDenominator data (thirdRow profile) = shape.k :=
  shape.third_index ▸ incomingRowDenominator_eq_of_rowUnramified_of_rowTargetInjective
    input.dangling_no_glue hEnds onRow_thirdRow hUnram hInjective

end DraismaVargas.Count.RowWalk

namespace DraismaVargas.Count.RowWalk

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.CaterpillarDatum
open DraismaVargas.LocalCases.CaterpillarPruning

/-! ## 10.  Non-vacuity on the caterpillar of loops

`Count.EdgeDenominator`'s witness section shows that off the leaf edges a row of
`T^CL_g` displays a single occurrence, which makes it unramified and target
injective outright; and `SimpleTarget` holds of `T^CL_g` itself, so §6's
`hPairs` discharge and §8's unconditional trichotomy are not vacuous there. -/

/-- **`SimpleTarget` is inhabited**: the caterpillar of loops `T^CL_g`, the
target of the base count, is a simple graph.  The maximum of an
occurrence's two endpoint indices is `i + 1`, which determines `i`. -/
theorem simpleTarget_catTree (m : ℕ) : SimpleTarget (catTree m) := by
  intro x y first second hxy hfx hfy hsx hsy
  obtain ⟨i, rfl⟩ := (occ_bijective m).2 first
  obtain ⟨j, rfl⟩ := (occ_bijective m).2 second
  have key : ∀ k : Fin (6 * m + 3), occ m k ∈ GluingDatum.incidentEdges x →
      occ m k ∈ GluingDatum.incidentEdges y → k.val + 1 = max x.val y.val := by
    intro k hkx hky
    have hle := catParent_le m k
    rcases (GluingContraction.mem_incidentEdges_iff x (occ m k)).mp hkx with hx | hx <;>
      rcases (GluingContraction.mem_incidentEdges_iff y (occ m k)).mp hky with hy | hy
    · rw [occ_fst] at hx hy
      exact absurd (hx.symm.trans hy) hxy
    · rw [occ_fst] at hx
      rw [occ_snd] at hy
      have hxv : x.val = (catParent m k).val := congrArg Fin.val hx.symm
      have hyv : y.val = k.val + 1 := congrArg Fin.val hy.symm
      omega
    · rw [occ_snd] at hx
      rw [occ_fst] at hy
      have hxv : x.val = k.val + 1 := congrArg Fin.val hx.symm
      have hyv : y.val = (catParent m k).val := congrArg Fin.val hy.symm
      omega
    · rw [occ_snd] at hx hy
      exact absurd (hx.symm.trans hy) hxy
  have hEq := (key i hfx hfy).trans (key j hsx hsy).symm
  exact congrArg (occ m) (Fin.ext (by omega))

/-- **`RowUnramified` is inhabited**: off the leaf edges a caterpillar row is a
single occurrence, so it has no interior vertex at all. -/
theorem rowUnramified_cat (m : ℕ) {i : Fin (6 * m + 3)} (hNotLeaf : ¬ IsLeafEdge m i) :
    RowUnramified (caterpillarDatum m) ((CaterpillarRows.labelling m).row.symm i) := by
  refine rowUnramified_of_unique _ fun first second hFirst hSecond ↦ ?_
  have hFirstMem :=
    (mem_rowEdges_iff_onRow (CaterpillarRows.labelling m) i first).mpr hFirst
  have hSecondMem :=
    (mem_rowEdges_iff_onRow (CaterpillarRows.labelling m) i second).mpr hSecond
  rw [EdgeDenominator.rowEdges_cat_notLeafEdge m hNotLeaf, Finset.mem_singleton]
    at hFirstMem hSecondMem
  rw [hFirstMem, hSecondMem]

/-- **`RowTargetInjective` is inhabited** on the same rows. -/
theorem rowTargetInjective_cat (m : ℕ) {i : Fin (6 * m + 3)} (hNotLeaf : ¬ IsLeafEdge m i) :
    RowTargetInjective (caterpillarDatum m) ((CaterpillarRows.labelling m).row.symm i) := by
  intro first second hFirst hSecond _
  have hFirstMem :=
    (mem_rowEdges_iff_onRow (CaterpillarRows.labelling m) i first).mpr hFirst
  have hSecondMem :=
    (mem_rowEdges_iff_onRow (CaterpillarRows.labelling m) i second).mpr hSecond
  rw [EdgeDenominator.rowEdges_cat_notLeafEdge m hNotLeaf, Finset.mem_singleton]
    at hFirstMem hSecondMem
  rw [hFirstMem, hSecondMem]

/-- **The square consequence, instantiated**: `d_i ∣ m(e)` on a leaf-free row of
`T^CL_g`.  `Count.EdgeDenominator.rowDenominator_cat_pairEdge` evaluates the
right-hand side to `2` on a pair edge and to `1` on a spine edge. -/
example (m : ℕ) {i : Fin (6 * m + 3)} (hNotLeaf : ¬ IsLeafEdge m i) :
    rowDenominator (CaterpillarRows.labelling m).presentation i ∣
      (caterpillarDatum m).sourceEdgeIndex ((caterpillarDatum m).sourceEdge (occ m i) 0) :=
  rowDenominator_dvd_of_rowUnramified (CaterpillarRows.fullDim m)
    (EdgeDenominator.main_mem_rowEdges m i) (rowUnramified_cat m hNotLeaf)

/-- **The rectangular consequence, instantiated**: the sharp incoming row
denominator, on a datum where both halves are available. -/
example (m : ℕ) {i : Fin (6 * m + 3)} (hNotLeaf : ¬ IsLeafEdge m i) :
    TrivalentWeight.incomingRowDenominator (caterpillarDatum m)
        ((CaterpillarRows.labelling m).row.symm i) =
      (caterpillarDatum m).sourceEdgeIndex ((caterpillarDatum m).sourceEdge (occ m i) 0) :=
  incomingRowDenominator_eq_of_rowUnramified_of_rowTargetInjective
    (CaterpillarRows.fullDim m).danglingEdgeNoGlue (CaterpillarRows.fullDim m).pathEnds
    ((mem_rowEdges_iff_onRow (CaterpillarRows.labelling m) i _).mp
      (EdgeDenominator.main_mem_rowEdges m i))
    (rowUnramified_cat m hNotLeaf) (rowTargetInjective_cat m hNotLeaf)

/-- **The trichotomy of `lemma-edge-deno`, unconditional on `T^CL_g`.**  The
hypothesis `RowIndicesConsecutive` that `Count.EdgeDenominator` had to carry is
now discharged for every row at once. -/
example (m : ℕ) (i : Fin (6 * m + 3)) :
    (EdgeDenominator.PassesAboveLeaf (CaterpillarRows.labelling m) i ∧
        rowDenominator (CaterpillarRows.labelling m).presentation i = 1) ∨
      (¬ EdgeDenominator.PassesAboveLeaf (CaterpillarRows.labelling m) i ∧
        ∃ index : ℕ, 0 < index ∧
          EdgeDenominator.RowIndexConstant (CaterpillarRows.labelling m) i index ∧
          rowDenominator (CaterpillarRows.labelling m).presentation i ∣ index) ∨
      (¬ EdgeDenominator.PassesAboveLeaf (CaterpillarRows.labelling m) i ∧
        ∃ index : ℕ, 0 < index ∧
          EdgeDenominator.RowIndexTwoValued (CaterpillarRows.labelling m) i index ∧
          (∃ edge ∈ EdgeDenominator.rowEdges (CaterpillarRows.labelling m) i,
            (caterpillarDatum m).sourceEdgeIndex edge = index) ∧
          (∃ edge ∈ EdgeDenominator.rowEdges (CaterpillarRows.labelling m) i,
            (caterpillarDatum m).sourceEdgeIndex edge = index + 1) ∧
          rowDenominator (CaterpillarRows.labelling m).presentation i ∣
            index * (index + 1)) :=
  rowDenominator_trichotomy_of_simpleTarget (CaterpillarRows.fullDim m)
    (simpleTarget_catTree m) i

end DraismaVargas.Count.RowWalk
