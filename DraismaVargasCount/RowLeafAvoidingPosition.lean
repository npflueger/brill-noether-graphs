import DraismaVargasCount.RowTransitionPosition

/-!
# All actual weighted positions on leaf-avoiding rows

Equal adjacent indices imply zero local ramification and identify the local
degree. The actual transition segmentation then proves that the weighted positions
before and after the transition have odd denominator, while `RowTransitionPosition`
handles the transition itself.
`weighted_prefix_mem_of_leafAvoids` decides transition existence internally
and also handles a row with no transition. No arithmetic profile, named chip
coefficient, or position identity is assumed.

These are actual source-walk positions with canonical pendant-retraction
coefficients. Hairpin rows (`RowHairpinPosition`) and the transport of the metric
realization and its offsets are not treated here.
-/

namespace DraismaVargas.Count.RowLeafAvoidingPosition

open DraismaVargas.Infrastructure GluingDatum
open DraismaVargas.LocalCases W4StableSource FullDimensionalSource
open StableLocalProperties OrientedTraversal
open RowWalk PendantRetraction RowChipCoefficient SlotMoment RowPosition RowTransitionPosition

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

theorem getElem_mem_take_of_lt {α : Type*} {items : List α} {i cut : ℕ}
    (hi : i < items.length) (hCut : i < cut) : items[i] ∈ items.take cut :=
  List.mem_take_iff_getElem.mpr ⟨i, by omega, rfl⟩

theorem getElem_mem_drop_of_le {α : Type*} {items : List α} {i cut : ℕ}
    (hi : i < items.length) (hCut : cut ≤ i) : items[i] ∈ items.drop cut := by
  apply List.mem_drop_iff_getElem.mpr
  refine ⟨i - cut, by omega, ?_⟩
  congr 1
  omega

/-- Equal adjacent indices on a leaf-avoiding row force zero ramification
and identify the actual local degree with those indices. -/
theorem ramification_degree_of_equal_indices
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} (hAvoid : RowAvoidsLeaves data path)
    {i : ℕ} (hi : i + 1 < (orderedRow fd.pathEnds path).length)
    (hIndex : data.sourceEdgeIndex (orderedRow fd.pathEnds path)[i] =
      data.sourceEdgeIndex (orderedRow fd.pathEnds path)[i + 1]) :
    data.localRamification (rowVertex fd path (i + 1)).1.1
      ⟨(rowVertex fd path (i + 1)).1.2, (rowVertex fd path (i + 1)).2⟩ = 0 ∧
    (data.vertexPartition (rowVertex fd path (i + 1)).1.1).blockCard
      (rowVertex fd path (i + 1)).1.2 =
        data.sourceEdgeIndex (orderedRow fd.pathEnds path)[i] := by
  have hValency := rowVertex_valency fd path hi
  have hFirst := (mem_orderedRow_iff fd.pathEnds path _).mp
    (List.getElem_mem (Nat.lt_of_succ_lt hi))
  have hSecond := (mem_orderedRow_iff fd.pathEnds path _).mp (List.getElem_mem hi)
  have hFirstInc : Incident data (orderedRow fd.pathEnds path)[i]
      (rowVertex fd path (i + 1)) := walkVertex_succ_incident (Nat.lt_of_succ_lt hi)
  have hSecondInc := rowVertex_incident fd path hi
  have hNe : (orderedRow fd.pathEnds path)[i] ≠ (orderedRow fd.pathEnds path)[i + 1] := by
    intro h
    have := (orderedRow_nodup fd.pathEnds path).getElem_inj_iff.mp h
    omega
  have hTame := rowRamificationAtMostOne_of_rowAvoidsLeaves fd hAvoid
    _ _ hFirst hFirstInc hValency
  have hSum := IndexPattern.sourceEdgeIndex_add_sourceEdgeIndex fd hValency
    hFirst.survives hFirstInc hSecond.survives hSecondInc hNe
  rw [hIndex] at hSum
  constructor <;> omega

/-- Multiplying the literal length of a constant-index segment by its index
cancels every denominator; what remains is a sum of target lengths, which have odd
denominators on a leaf-avoiding row at odd multiplicity (`row_target_length_mem`). -/
theorem index_mul_segment_mem
    (fd : FullDimensionalSourcePresentation data coordinate)
    (y : coordinate → ℤ) (z : coordinate → ℚ)
    (hSystem : (LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec z =
      fun row ↦ (y row : ℚ)) (hOdd : Odd (fdAbsMultNat fd))
    {path : StablePath data} (hAvoid : RowAvoidsLeaves data path)
    (items : List data.SourceEdge) (hItems : ∀ edge ∈ items, OnRow data path edge)
    (index : ℕ) (hIndex : ∀ edge ∈ items, data.sourceEdgeIndex edge = index) :
    (index : ℚ) * (items.map fun edge ↦
      z (fd.labelling.targetEdge.symm edge.1.1) / (data.sourceEdgeIndex edge : ℚ)).sum
        ∈ oddDenominatorSubring := by
  rw [← List.sum_map_mul_left]
  apply oddDenominatorSubring.list_sum_mem
  intro term hTerm
  obtain ⟨edge, hEdge, rfl⟩ := List.mem_map.mp hTerm
  rw [← hIndex edge hEdge]
  have hPos : (data.sourceEdgeIndex edge : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (GluingDatum.sourceEdgeIndex_pos data edge))
  have hCancel : (data.sourceEdgeIndex edge : ℚ) *
      (z (fd.labelling.targetEdge.symm edge.1.1) / (data.sourceEdgeIndex edge : ℚ)) =
      z (fd.labelling.targetEdge.symm edge.1.1) := by field_simp
  rw [hCancel]
  exact row_target_length_mem fd y z hSystem hOdd hAvoid (hItems edge hEdge)

/-- Actual weighted positions strictly before the unique transition. -/
theorem weighted_prefix_before_transition
    (fd : FullDimensionalSourcePresentation data coordinate)
    (y : coordinate → ℤ) (z : coordinate → ℚ)
    (hSystem : (LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec z =
      fun row ↦ (y row : ℚ)) (hOdd : Odd (fdAbsMultNat fd))
    {path : StablePath data} (hAvoid : RowAvoidsLeaves data path) (root : target.V)
    {i j : ℕ} (hi : i < j) (hj : j + 1 < (orderedRow fd.pathEnds path).length)
    (hRam : data.localRamification (rowVertex fd path (j + 1)).1.1
      ⟨(rowVertex fd path (j + 1)).1.2, (rowVertex fd path (j + 1)).2⟩ = 1) :
    (retractedFibre root (retractVertex (rowVertex fd path (i + 1))) : ℚ) *
      prefixPosition fd z path (i + 1) ∈ oddDenominatorSubring := by
  have hiLen : i + 1 < (orderedRow fd.pathEnds path).length := by omega
  have hSegments := orderedRow_transition_segments fd hAvoid hj hRam
  have hFirst := hSegments.1 _ (getElem_mem_take_of_lt (Nat.lt_of_succ_lt hiLen) (by omega))
  have hSecond := hSegments.1 _ (getElem_mem_take_of_lt hiLen (by omega))
  have hLocal := ramification_degree_of_equal_indices fd hAvoid hiLen
    (hFirst.trans hSecond.symm)
  rcases coefficient_of_ramification_zero fd (rowVertex_valency fd path hiLen)
    hLocal.1 root with hZero | hDegree
  · rw [hZero, Int.cast_zero, zero_mul]
    exact oddDenominatorSubring.zero_mem
  rw [hDegree, Int.cast_natCast, hLocal.2, hFirst]
  apply index_mul_segment_mem fd y z hSystem hOdd hAvoid _
    (fun edge hEdge ↦ (mem_orderedRow_iff fd.pathEnds path edge).mp (List.mem_of_mem_take hEdge))
  intro edge hEdge
  apply hSegments.1
  obtain ⟨k, hk, hEq⟩ := List.mem_take_iff_getElem.mp hEdge
  exact List.mem_take_iff_getElem.mpr ⟨k, by omega, hEq⟩

/-- Actual weighted positions strictly after the unique transition. -/
theorem weighted_prefix_after_transition
    (fd : FullDimensionalSourcePresentation data coordinate)
    (y : coordinate → ℤ) (z : coordinate → ℚ)
    (hSystem : (LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec z =
      fun row ↦ (y row : ℚ)) (hOdd : Odd (fdAbsMultNat fd))
    {path : StablePath data} (hAvoid : RowAvoidsLeaves data path) (root : target.V)
    {i j : ℕ} (hj : j < i) (hi : i + 1 < (orderedRow fd.pathEnds path).length)
    (hRam : data.localRamification (rowVertex fd path (j + 1)).1.1
      ⟨(rowVertex fd path (j + 1)).1.2, (rowVertex fd path (j + 1)).2⟩ = 1) :
    (retractedFibre root (retractVertex (rowVertex fd path (i + 1))) : ℚ) *
      prefixPosition fd z path (i + 1) ∈ oddDenominatorSubring := by
  have hjLen : j + 1 < (orderedRow fd.pathEnds path).length := by omega
  have hSegments := orderedRow_transition_segments fd hAvoid hjLen hRam
  have hFirst := hSegments.2 _ (getElem_mem_drop_of_le (Nat.lt_of_succ_lt hi) (by omega))
  have hSecond := hSegments.2 _ (getElem_mem_drop_of_le hi (by omega))
  have hLocal := ramification_degree_of_equal_indices fd hAvoid hi
    (hFirst.trans hSecond.symm)
  rcases coefficient_of_ramification_zero fd (rowVertex_valency fd path hi)
    hLocal.1 root with hZero | hDegree
  · rw [hZero, Int.cast_zero, zero_mul]
    exact oddDenominatorSubring.zero_mem
  rw [hDegree, Int.cast_natCast, hLocal.2, hFirst]
  have hPos : prefixPosition fd z path (i + 1) = prefixPosition fd z path (j + 1) +
      ((((orderedRow fd.pathEnds path).drop (j + 1)).take (i - j)).map fun edge ↦
        z (fd.labelling.targetEdge.symm edge.1.1) / (data.sourceEdgeIndex edge : ℚ)).sum := by
    unfold prefixPosition
    rw [show i + 1 = (j + 1) + (i - j) from by omega, List.take_add,
      List.map_append, List.sum_append]
  rw [hPos, mul_add]
  apply oddDenominatorSubring.add_mem
  · exact oddDenominatorSubring.mul_mem (natCast_mem _ _)
      (transition_prefix_mem fd y z hSystem hOdd hAvoid hjLen hRam)
  · apply index_mul_segment_mem fd y z hSystem hOdd hAvoid _
      (fun edge hEdge ↦ (mem_orderedRow_iff fd.pathEnds path edge).mp
        (List.mem_of_mem_drop (List.mem_of_mem_take hEdge)))
    intro edge hEdge
    exact hSegments.2 edge (List.mem_of_mem_take hEdge)

/-- All interior positions of a leaf-avoiding row with a transition, combining
the before, at, and after producers on the same actual source walk. -/
theorem weighted_prefix_on_transition_row
    (fd : FullDimensionalSourcePresentation data coordinate)
    (y : coordinate → ℤ) (z : coordinate → ℚ)
    (hSystem : (LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec z =
      fun row ↦ (y row : ℚ)) (hOdd : Odd (fdAbsMultNat fd))
    {path : StablePath data} (hAvoid : RowAvoidsLeaves data path) (root : target.V)
    {j : ℕ} (hj : j + 1 < (orderedRow fd.pathEnds path).length)
    (hRam : data.localRamification (rowVertex fd path (j + 1)).1.1
      ⟨(rowVertex fd path (j + 1)).1.2, (rowVertex fd path (j + 1)).2⟩ = 1)
    {i : ℕ} (hi : i + 1 < (orderedRow fd.pathEnds path).length) :
    (retractedFibre root (retractVertex (rowVertex fd path (i + 1))) : ℚ) *
      prefixPosition fd z path (i + 1) ∈ oddDenominatorSubring := by
  rcases lt_trichotomy i j with hBefore | rfl | hAfter
  · exact weighted_prefix_before_transition fd y z hSystem hOdd hAvoid root hBefore hj hRam
  · exact weighted_transition_prefix_mem fd y z hSystem hOdd hAvoid root hi hRam
  · exact weighted_prefix_after_transition fd y z hSystem hOdd hAvoid root hAfter hi hRam

/-- The complete leaf-avoiding-row producer: every actual interior weighted
position has odd denominator. Transition existence is decided internally. -/
theorem weighted_prefix_mem_of_leafAvoids
    (fd : FullDimensionalSourcePresentation data coordinate)
    (y : coordinate → ℤ) (z : coordinate → ℚ)
    (hSystem : (LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec z =
      fun row ↦ (y row : ℚ)) (hOdd : Odd (fdAbsMultNat fd))
    {path : StablePath data} (hAvoid : RowAvoidsLeaves data path) (root : target.V)
    {i : ℕ} (hi : i + 1 < (orderedRow fd.pathEnds path).length) :
    (retractedFibre root (retractVertex (rowVertex fd path (i + 1))) : ℚ) *
      prefixPosition fd z path (i + 1) ∈ oddDenominatorSubring := by
  classical
  by_cases hTransition : ∃ j, ∃ _hj : j + 1 < (orderedRow fd.pathEnds path).length,
      data.localRamification (rowVertex fd path (j + 1)).1.1
        ⟨(rowVertex fd path (j + 1)).1.2, (rowVertex fd path (j + 1)).2⟩ = 1
  · obtain ⟨j, hj, hRam⟩ := hTransition
    exact weighted_prefix_on_transition_row fd y z hSystem hOdd hAvoid root hj hRam hi
  have hZero : ∀ j, ∀ hj : j + 1 < (orderedRow fd.pathEnds path).length,
      data.localRamification (rowVertex fd path (j + 1)).1.1
        ⟨(rowVertex fd path (j + 1)).1.2, (rowVertex fd path (j + 1)).2⟩ = 0 := by
    intro j hj
    have hOn := (mem_orderedRow_iff fd.pathEnds path _).mp (List.getElem_mem hj)
    exact (rowRamificationAtMostOne_of_rowAvoidsLeaves fd hAvoid _ _ hOn
      (rowVertex_incident fd path hj) (rowVertex_valency fd path hj)).resolve_right
        (fun hRam ↦ hTransition ⟨j, hj, hRam⟩)
  have hChain : (orderedRow fd.pathEnds path).IsChain
      (fun a b ↦ data.sourceEdgeIndex a = data.sourceEdgeIndex b) := by
    apply List.isChain_iff_getElem.mpr
    intro j hj
    have hFirst := (mem_orderedRow_iff fd.pathEnds path _).mp
      (List.getElem_mem (Nat.lt_of_succ_lt hj))
    have hSecond := (mem_orderedRow_iff fd.pathEnds path _).mp (List.getElem_mem hj)
    have hFirstInc : Incident data (orderedRow fd.pathEnds path)[j]
        (rowVertex fd path (j + 1)) := walkVertex_succ_incident (Nat.lt_of_succ_lt hj)
    exact sourceEdgeIndex_eq_of_localRamification_eq_zero_of_noGlue fd.danglingEdgeNoGlue
      (rowVertex_valency fd path hj) (hZero j hj) hFirst.survives hFirstInc
      hSecond.survives (rowVertex_incident fd path hj)
  have hConst : ∀ edge ∈ orderedRow fd.pathEnds path,
      data.sourceEdgeIndex edge = data.sourceEdgeIndex (orderedRow fd.pathEnds path)[i] := by
    intro edge hEdge
    exact chain_const (fun item ↦ data.sourceEdgeIndex item)
      (fun a b ↦ data.sourceEdgeIndex a = data.sourceEdgeIndex b) (fun _ ↦ True)
      (fun _ _ _ _ h ↦ h) _ (fun _ _ ↦ True.intro) hChain hEdge
        (List.getElem_mem (Nat.lt_of_succ_lt hi))
  have hLocal := ramification_degree_of_equal_indices fd hAvoid hi
    ((hConst _ (List.getElem_mem hi)).symm)
  rcases coefficient_of_ramification_zero fd (rowVertex_valency fd path hi)
    hLocal.1 root with hNone | hDegree
  · rw [hNone, Int.cast_zero, zero_mul]
    exact oddDenominatorSubring.zero_mem
  rw [hDegree, Int.cast_natCast, hLocal.2]
  exact index_mul_segment_mem fd y z hSystem hOdd hAvoid _
    (fun edge hEdge ↦ (mem_orderedRow_iff fd.pathEnds path edge).mp (List.mem_of_mem_take hEdge))
    _ (fun edge hEdge ↦ hConst edge (List.mem_of_mem_take hEdge))

/-- The full leaf-avoiding-row producer, in the counted member's actual
request-slot coordinates. -/
theorem member_weighted_prefix_mem_of_leafAvoids {n p : ℕ}
    {core : Utilities.Certificate.ExplicitPotential.Core n p} (y : Fin p → ℤ)
    (member : FibreMember core (fun slot ↦ (y slot : ℚ)) degree)
    (hOdd : Odd member.oddMult) (slot : Fin p)
    (hAvoid : RowAvoidsLeaves member.data (member.ident.row.symm slot))
    (root : member.target.V) {i : ℕ}
    (hi : i + 1 < (orderedRow member.fullDim.pathEnds (member.ident.row.symm slot)).length) :
    (retractedFibre root
      (retractVertex (rowVertex member.fullDim (member.ident.row.symm slot) (i + 1))) : ℚ) *
      prefixPosition member.fullDim member.coords (member.ident.row.symm slot) (i + 1)
        ∈ oddDenominatorSubring :=
  weighted_prefix_mem_of_leafAvoids member.fullDim
    (fun row ↦ y (member.ident.row (member.fullDim.labelling.row.symm row)))
    member.coords member.realizes hOdd hAvoid root hi

end DraismaVargas.Count.RowLeafAvoidingPosition
