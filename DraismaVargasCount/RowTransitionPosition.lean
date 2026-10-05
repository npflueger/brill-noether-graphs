module

public import DraismaVargasCount.RowPosition
public import DraismaVargasCount.RowGeodesic

@[expose] public section

/-!
# Actual transition segments and positions

Part of the descent of the pencil to an odd subdivision (step 5 of
`DraismaVargasCount.Assembly`), on a leaf-avoiding row.

The unique-transition and no-repeated-occurrence theorems imply that the actual
ordered source row splits at a transition into two constant-index segments.
The ramification identity makes those indices consecutive. Their literal
length sums, the integral matrix row, the odd denominators of the target
lengths on a leaf-avoiding row (`RowPosition.row_target_length_mem`, when the
multiplicity is odd) and the consecutive-index row lemma
(`SlotMoment.consecutive_row_quotients_mem`) together prove that the transition
position, and its actual weighted fibre coefficient, have odd denominator.
Both increasing and decreasing traversal orientations are covered.

These are the transition terms (`SlotMoment.transition_term_mem`) of the
per-slot moment divisibility `SlotMoment.slotMoment_dvd_two_pow_of_terms`,
produced from the actual row rather than from assumed segment indices or a
cleared row identity. Positions strictly before or after a transition, hairpin
rows, and the identification with the slot offsets of the realized subdivision
are not treated here.
-/

namespace DraismaVargas.Count.RowTransitionPosition

open DraismaVargas.Infrastructure GluingDatum
open DraismaVargas.LocalCases W4StableSource FullDimensionalSource
open StableLocalProperties OrientedTraversal
open RowWalk PendantRetraction RowChipCoefficient SlotMoment RowPosition

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- Away from either occurrence at the unique transition, every connected
sublist of the actual row has constant index. -/
theorem index_constant_away_from_transition
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} (hAvoid : RowAvoidsLeaves data path)
    {vertex : data.SourceVertex} (hValency : nonDanglingValency data vertex = 2)
    (hRam : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 1)
    {first second : data.SourceEdge} (hFirst : OnRow data path first)
    (hFirstIncident : Incident data first vertex) (hSecond : OnRow data path second)
    (hSecondIncident : Incident data second vertex) (hNe : first ≠ second)
    (items : List data.SourceEdge) (hItems : ∀ edge ∈ items, OnRow data path edge)
    (hChain : items.IsChain (TraversalPresentation.MeetsAt data))
    (hExcluded : first ∉ items ∨ second ∉ items)
    {a b : data.SourceEdge} (ha : a ∈ items) (hb : b ∈ items) :
    data.sourceEdgeIndex a = data.sourceEdgeIndex b := by
  have hTame := rowRamificationAtMostOne_of_rowAvoidsLeaves fd hAvoid
  have hOne := rowAtMostOneTransition_of_simpleTarget fd
    (RowGeodesic.simpleTarget_of_genusZero fd.targetConnected fd.targetGenus) hAvoid
  refine chain_const (fun edge ↦ data.sourceEdgeIndex edge)
    (TraversalPresentation.MeetsAt data) (fun edge ↦ OnRow data path edge ∧ edge ∈ items)
    ?_ items (fun edge hMem ↦ ⟨hItems edge hMem, hMem⟩) hChain ha hb
  rintro c d ⟨hC, hc⟩ ⟨hD, hd⟩ ⟨meet, hCI, hDI, hMeet⟩
  rcases hTame meet c hC hCI hMeet with hZero | hJump
  · exact sourceEdgeIndex_eq_of_localRamification_eq_zero_of_noGlue fd.danglingEdgeNoGlue
      hMeet hZero hC.survives hCI hD.survives hDI
  · have hEq : meet = vertex :=
      hOne meet vertex ⟨hMeet, hJump, c, hC, hCI⟩
        ⟨hValency, hRam, first, hFirst, hFirstIncident⟩
    subst meet
    have hCaseC := IndexPattern.eq_or_eq_of_nonDanglingValency_two hValency
      hFirst.survives hFirstIncident hSecond.survives hSecondIncident hNe hC.survives hCI
    have hCaseD := IndexPattern.eq_or_eq_of_nonDanglingValency_two hValency
      hFirst.survives hFirstIncident hSecond.survives hSecondIncident hNe hD.survives hDI
    rcases hExcluded with hExclude | hExclude
    · have hCeq : c = second := hCaseC.resolve_left (fun h ↦ hExclude (h ▸ hc))
      have hDeq : d = second := hCaseD.resolve_left (fun h ↦ hExclude (h ▸ hd))
      rw [hCeq, hDeq]
    · have hCeq : c = first := hCaseC.resolve_right (fun h ↦ hExclude (h ▸ hc))
      have hDeq : d = first := hCaseD.resolve_right (fun h ↦ hExclude (h ▸ hd))
      rw [hCeq, hDeq]

/-- The actual ordered row splits at a transition into two constant-index
segments. The order can be increasing or decreasing; neither is assumed. -/
theorem orderedRow_transition_segments
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} (hAvoid : RowAvoidsLeaves data path)
    {j : ℕ} (hj : j + 1 < (orderedRow fd.pathEnds path).length)
    (hRam : data.localRamification (rowVertex fd path (j + 1)).1.1
      ⟨(rowVertex fd path (j + 1)).1.2, (rowVertex fd path (j + 1)).2⟩ = 1) :
    (∀ edge ∈ (orderedRow fd.pathEnds path).take (j + 1),
      data.sourceEdgeIndex edge = data.sourceEdgeIndex (orderedRow fd.pathEnds path)[j]) ∧
    (∀ edge ∈ (orderedRow fd.pathEnds path).drop (j + 1),
      data.sourceEdgeIndex edge = data.sourceEdgeIndex (orderedRow fd.pathEnds path)[j + 1]) := by
  let items := orderedRow fd.pathEnds path
  have hNodup := orderedRow_nodup fd.pathEnds path
  have hj1 : j + 1 < items.length := hj
  have hj0 : j < items.length := Nat.lt_of_succ_lt hj
  have hFirst : OnRow data path items[j] :=
    (mem_orderedRow_iff fd.pathEnds path _).mp (List.getElem_mem hj0)
  have hSecond : OnRow data path items[j + 1] :=
    (mem_orderedRow_iff fd.pathEnds path _).mp (List.getElem_mem hj)
  have hFirstInc : Incident data items[j] (rowVertex fd path (j + 1)) :=
    walkVertex_succ_incident hj0
  have hSecondInc := rowVertex_incident fd path hj
  have hNe : items[j] ≠ items[j + 1] := by
    intro h
    have := hNodup.getElem_inj_iff.mp h
    omega
  have hFirstMem : items[j] ∈ items.take (j + 1) :=
    List.mem_take_iff_getElem.mpr ⟨j, by omega, rfl⟩
  have hSecondMem : items[j + 1] ∈ items.drop (j + 1) :=
    List.mem_drop_iff_getElem.mpr ⟨0, by omega, rfl⟩
  have hFirstNot : items[j] ∉ items.drop (j + 1) := by
    intro h
    obtain ⟨k, hk, hEq⟩ := List.mem_drop_iff_getElem.mp h
    have := hNodup.getElem_inj_iff.mp hEq
    omega
  have hSecondNot : items[j + 1] ∉ items.take (j + 1) := by
    intro h
    obtain ⟨k, hk, hEq⟩ := List.mem_take_iff_getElem.mp h
    have := hNodup.getElem_inj_iff.mp hEq
    omega
  constructor
  · intro edge hEdge
    exact index_constant_away_from_transition fd hAvoid (rowVertex_valency fd path hj)
      hRam hFirst hFirstInc hSecond hSecondInc hNe (items.take (j + 1))
      (fun e he ↦ (mem_orderedRow_iff fd.pathEnds path e).mp (List.mem_of_mem_take he))
      ((orderedRow_chain fd.pathEnds path).take (j + 1)) (Or.inr hSecondNot) hEdge hFirstMem
  · intro edge hEdge
    exact index_constant_away_from_transition fd hAvoid (rowVertex_valency fd path hj)
      hRam hFirst hFirstInc hSecond hSecondInc hNe (items.drop (j + 1))
      (fun e he ↦ (mem_orderedRow_iff fd.pathEnds path e).mp (List.mem_of_mem_drop he))
      ((orderedRow_chain fd.pathEnds path).drop (j + 1)) (Or.inl hFirstNot) hEdge hSecondMem

/-- Consecutive nonzero indices make both whole-segment positions lie in
the coefficient subring, in either traversal orientation. -/
theorem adjacent_quotients_mem (S : Subring ℚ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hAdjacent : a + 1 = b ∨ b + 1 = a) (y L R : ℚ)
    (hy : y ∈ S) (hL : L ∈ S) (hR : R ∈ S)
    (hEq : y = L / a + R / b) : L / a ∈ S ∧ R / b ∈ S := by
  have haQ : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt ha)
  have hbQ : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hb)
  rcases hAdjacent with h | h
  · subst b
    have hNext : (a : ℚ) + 1 ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
    have hBoth := consecutive_row_quotients_mem S a y L R haQ hNext
      (natCast_mem S a) hy hL hR (by
        rw [hEq]
        push_cast
        field_simp)
    simpa only [Nat.cast_add, Nat.cast_one] using hBoth
  · subst a
    have hNext : (b : ℚ) + 1 ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
    have hBoth := consecutive_row_quotients_mem S b y R L hbQ hNext
      (natCast_mem S b) hy hR hL (by
        rw [hEq]
        push_cast
        field_simp
        ring)
    simpa only [Nat.cast_add, Nat.cast_one] using hBoth.symm

/-- An actual constant-index segment has length its target-length sum
divided by that index. -/
theorem segment_length_of_constant
    (fd : FullDimensionalSourcePresentation data coordinate) (z : coordinate → ℚ)
    (items : List data.SourceEdge) (index : ℕ)
    (hIndex : ∀ edge ∈ items, data.sourceEdgeIndex edge = index) :
    (items.map fun edge ↦ z (fd.labelling.targetEdge.symm edge.1.1) /
      (data.sourceEdgeIndex edge : ℚ)).sum =
      (items.map fun edge ↦ z (fd.labelling.targetEdge.symm edge.1.1)).sum / index := by
  induction items with
  | nil => simp
  | cons first rest ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [hIndex first (List.mem_cons_self ..),
      ih (fun edge hEdge ↦ hIndex edge (List.mem_cons_of_mem first hEdge)), add_div]

/-- The consecutive-index row lemma applied to the actual ordered row, not to an assumed split:
the source vertex at its transition has 2-integral position. -/
theorem transition_prefix_mem
    (fd : FullDimensionalSourcePresentation data coordinate)
    (y : coordinate → ℤ) (z : coordinate → ℚ)
    (hSystem : (LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec z =
      fun row ↦ (y row : ℚ)) (hOdd : Odd (fdAbsMultNat fd))
    {path : StablePath data} (hAvoid : RowAvoidsLeaves data path)
    {j : ℕ} (hj : j + 1 < (orderedRow fd.pathEnds path).length)
    (hRam : data.localRamification (rowVertex fd path (j + 1)).1.1
      ⟨(rowVertex fd path (j + 1)).1.2, (rowVertex fd path (j + 1)).2⟩ = 1) :
    prefixPosition fd z path (j + 1) ∈ oddDenominatorSubring := by
  let items := orderedRow fd.pathEnds path
  let first := items[j]
  let second := items[j + 1]
  let L := ((items.take (j + 1)).map
    fun edge ↦ z (fd.labelling.targetEdge.symm edge.1.1)).sum
  let R := ((items.drop (j + 1)).map
    fun edge ↦ z (fd.labelling.targetEdge.symm edge.1.1)).sum
  have hSegments := orderedRow_transition_segments fd hAvoid hj hRam
  have hPrefix : prefixPosition fd z path (j + 1) = L / data.sourceEdgeIndex first :=
    segment_length_of_constant fd z (items.take (j + 1))
      (data.sourceEdgeIndex first) hSegments.1
  have hSuffix := segment_length_of_constant fd z (items.drop (j + 1))
    (data.sourceEdgeIndex second) hSegments.2
  have hEq : (y (fd.labelling.row path) : ℚ) =
      L / data.sourceEdgeIndex first + R / data.sourceEdgeIndex second := by
    calc
      _ = prefixPosition fd z path items.length :=
        (prefixPosition_full fd z path |>.trans (congrFun hSystem (fd.labelling.row path))).symm
      _ = prefixPosition fd z path (j + 1) +
          ((items.drop (j + 1)).map fun edge ↦
            z (fd.labelling.targetEdge.symm edge.1.1) / (data.sourceEdgeIndex edge : ℚ)).sum := by
        unfold prefixPosition
        rw [List.take_length, ← List.sum_append, ← List.map_append, List.take_append_drop]
      _ = _ := by rw [hPrefix, hSuffix]
  have hMem : ∀ edges : List data.SourceEdge,
      (∀ edge ∈ edges, OnRow data path edge) →
      (edges.map fun edge ↦ z (fd.labelling.targetEdge.symm edge.1.1)).sum
        ∈ oddDenominatorSubring := by
    intro edges hEdges
    apply oddDenominatorSubring.list_sum_mem
    intro value hValue
    obtain ⟨edge, hEdge, rfl⟩ := List.mem_map.mp hValue
    exact row_target_length_mem fd y z hSystem hOdd hAvoid (hEdges edge hEdge)
  have hL : L ∈ oddDenominatorSubring := hMem _ fun edge hEdge ↦
    (mem_orderedRow_iff fd.pathEnds path edge).mp (List.mem_of_mem_take hEdge)
  have hR : R ∈ oddDenominatorSubring := hMem _ fun edge hEdge ↦
    (mem_orderedRow_iff fd.pathEnds path edge).mp (List.mem_of_mem_drop hEdge)
  have hFirst : OnRow data path first :=
    (mem_orderedRow_iff fd.pathEnds path _).mp (List.getElem_mem (Nat.lt_of_succ_lt hj))
  have hSecond : OnRow data path second :=
    (mem_orderedRow_iff fd.pathEnds path _).mp (List.getElem_mem hj)
  have hFirstInc : Incident data first (rowVertex fd path (j + 1)) :=
    walkVertex_succ_incident (Nat.lt_of_succ_lt hj)
  have hSecondInc := rowVertex_incident fd path hj
  have hNe : first ≠ second := by
    intro h
    have := (orderedRow_nodup fd.pathEnds path).getElem_inj_iff.mp h
    omega
  have hDifference := IndexPattern.sourceEdgeIndex_sub_eq_one_of_transition fd
    (rowVertex_valency fd path hj) hRam hFirst.survives hFirstInc
    hSecond.survives hSecondInc hNe
  have hAdjacent : data.sourceEdgeIndex first + 1 = data.sourceEdgeIndex second ∨
      data.sourceEdgeIndex second + 1 = data.sourceEdgeIndex first := by omega
  rw [hPrefix]
  exact (adjacent_quotients_mem oddDenominatorSubring
    (data.sourceEdgeIndex first) (data.sourceEdgeIndex second)
    (GluingDatum.sourceEdgeIndex_pos data first) (GluingDatum.sourceEdgeIndex_pos data second)
    hAdjacent (y (fd.labelling.row path)) L R
    (intCast_mem _ _) hL hR hEq).1

/-- The actual retracted coefficient, including the possible unit chip at
the transition, multiplies the produced transition position in the same ring. -/
theorem weighted_transition_prefix_mem
    (fd : FullDimensionalSourcePresentation data coordinate)
    (y : coordinate → ℤ) (z : coordinate → ℚ)
    (hSystem : (LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec z =
      fun row ↦ (y row : ℚ)) (hOdd : Odd (fdAbsMultNat fd))
    {path : StablePath data} (hAvoid : RowAvoidsLeaves data path)
    (root : target.V) {j : ℕ} (hj : j + 1 < (orderedRow fd.pathEnds path).length)
    (hRam : data.localRamification (rowVertex fd path (j + 1)).1.1
      ⟨(rowVertex fd path (j + 1)).1.2, (rowVertex fd path (j + 1)).2⟩ = 1) :
    (retractedFibre root (retractVertex (rowVertex fd path (j + 1))) : ℚ) *
      prefixPosition fd z path (j + 1) ∈ oddDenominatorSubring :=
  oddDenominatorSubring.mul_mem (intCast_mem _ _)
    (transition_prefix_mem fd y z hSystem hOdd hAvoid hj hRam)

end DraismaVargas.Count.RowTransitionPosition
