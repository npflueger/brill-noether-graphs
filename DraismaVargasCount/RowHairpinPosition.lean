module

public import DraismaVargasCount.RowLeafAvoidingPosition

@[expose] public section

/-!
# Hairpin positions by a telescoping leaf correction

Part of the descent of the pencil to an odd subdivision (step 5 of
`DraismaVargasCount.Assembly`): when the multiplicity is odd, every interior
chip term (coefficient times position) along a stable row has odd denominator,
for a fibre rooted at an internal target vertex.  This file treats the rows
that pass above a leaf of the target (the *hairpins*) and combines them with
the leaf-avoiding rows of `RowLeafAvoidingPosition`.

On a unit-index source row, subtract the target leaf-edge length precisely
when the current vertex lies over that leaf. Every corrected step is a
non-leaf length, zero when entering a leaf, or twice a leaf length when
leaving. When the multiplicity is odd, the leaf-adjusted coordinates have odd
denominators (`OddDenominator.odd_leafAdjustedCoords_den`), which makes all of
these 2-integral. The correction starts at zero; its only nonzero cases have
zero actual fibre coefficient, by the ramification-two case of the local lemma
on chips inside a stable row (`RowChipCoefficient.coefficient_of_ramification_two`).

Every leaf-passing row has unit indices
(`EdgeDenominator.sourceEdgeIndex_eq_one_of_passesAboveLeaf`). Combining with
`RowLeafAvoidingPosition` proves `weighted_prefix_mem` for every actual row,
without a coefficient profile, hairpin enumeration, or orientation hypothesis.
These are canonical actual-source retraction positions; their identification
with the realized subdivision divisor and its slot offsets is not made here.
-/

namespace DraismaVargas.Count.RowHairpinPosition

open DraismaVargas.Infrastructure GluingDatum
open DraismaVargas.LocalCases W4StableSource FullDimensionalSource
open StableLocalProperties OrientedTraversal
open RowWalk PendantRetraction RowChipCoefficient SlotMoment RowPosition

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- Half-leaf correction at the current target vertex. It records exactly
the unmatched incoming leaf occurrence of a walk prefix. -/
noncomputable def leafPotential (fd : FullDimensionalSourcePresentation data coordinate)
    (z : coordinate → ℚ) (vertex : target.V) : ℚ :=
  if h : IsLeafVertex target vertex then z (fd.labelling.targetEdge.symm (leafEdge h)) else 0

/-- The corrected increment is a non-leaf length, zero when entering a leaf,
or twice a leaf length when leaving it. Each is 2-integral, because the
leaf-adjusted coordinates have odd denominators when the multiplicity is odd. -/
theorem adjusted_step_mem
    (fd : FullDimensionalSourcePresentation data coordinate)
    (y : coordinate → ℤ) (z : coordinate → ℚ)
    (hSystem : (LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec z =
      fun row ↦ (y row : ℚ)) (hOdd : Odd (fdAbsMultNat fd))
    (edge : target.edges) (first second : target.V)
    (hEnds : (edge : target.V × target.V) = (first, second) ∨
      (edge : target.V × target.V) = (second, first)) :
    z (fd.labelling.targetEdge.symm edge) - leafPotential fd z second +
      leafPotential fd z first ∈ oddDenominatorSubring := by
  classical
  have hFirstInc : edge ∈ incidentEdges first := by
    simp only [incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hEnds with h | h <;> simp [h]
  have hSecondInc : edge ∈ incidentEdges second := by
    simp only [incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hEnds with h | h <;> simp [h]
  have hNoBoth : ¬ (IsLeafVertex target first ∧ IsLeafVertex target second) := by
    rintro ⟨hFirst, hSecond⟩
    have hNo := noLeafToLeafEdge_of_fullDimensional fd edge
    rcases hEnds with h | h <;> rw [h] at hNo
    · exact hNo hFirst hSecond
    · exact hNo hSecond hFirst
  have hAdjusted := OddDenominator.odd_leafAdjustedCoords_den fd y z hSystem hOdd
    (fd.labelling.targetEdge.symm edge)
  by_cases hFirst : IsLeafVertex target first
  · have hSecond : ¬ IsLeafVertex target second := fun h ↦ hNoBoth ⟨hFirst, h⟩
    have hEdge := eq_leafEdge_of_mem hFirst hFirstInc
    have hColumn : fd.labelling.targetEdge.symm edge ∈ leafColumns fd.labelling.presentation := by
      apply (mem_leafColumns _ _).mpr
      exact ⟨first, hFirst, by simpa only [StableLengthMatrixLabelling.presentation,
        Equiv.apply_symm_apply] using hFirstInc⟩
    have hDouble : 2 * z (fd.labelling.targetEdge.symm edge) ∈ oddDenominatorSubring := by
      simpa only [OddDenominator.leafAdjustedCoords, ite_eq_left hColumn,
        mem_oddDenominatorSubring] using hAdjusted
    simp only [leafPotential, dite_eq_right hSecond, dite_eq_left hFirst, sub_zero]
    rw [← hEdge]
    convert hDouble using 1
    ring
  · by_cases hSecond : IsLeafVertex target second
    · have hEdge := eq_leafEdge_of_mem hSecond hSecondInc
      simp only [leafPotential, dite_eq_left hSecond, dite_eq_right hFirst, add_zero]
      rw [← hEdge, sub_self]
      exact oddDenominatorSubring.zero_mem
    · have hColumn : fd.labelling.targetEdge.symm edge ∉ leafColumns fd.labelling.presentation := by
        intro hMem
        obtain ⟨leaf, hLeaf, hInc⟩ := (mem_leafColumns _ _).mp hMem
        have hInc' : edge ∈ incidentEdges leaf := by
          simpa only [StableLengthMatrixLabelling.presentation, Equiv.apply_symm_apply] using hInc
        have hEndpoint := fst_eq_or_snd_eq_of_mem_incidentEdges hInc'
        rcases hEnds with h | h <;> rw [h] at hEndpoint
        · rcases hEndpoint with h | h
          · exact hFirst (Eq.mp (congrArg (IsLeafVertex target) h.symm) hLeaf)
          · exact hSecond (Eq.mp (congrArg (IsLeafVertex target) h.symm) hLeaf)
        · rcases hEndpoint with h | h
          · exact hSecond (Eq.mp (congrArg (IsLeafVertex target) h.symm) hLeaf)
          · exact hFirst (Eq.mp (congrArg (IsLeafVertex target) h.symm) hLeaf)
      simp only [leafPotential, dite_eq_right hSecond, dite_eq_right hFirst, sub_zero, add_zero]
      simpa only [OddDenominator.leafAdjustedCoords, ite_eq_right hColumn,
        mem_oddDenominatorSubring] using hAdjusted

/-- The endpoints of a source traversal step project to the endpoints of
its literal target occurrence, independently of its stored orientation. -/
theorem row_target_ends (fd : FullDimensionalSourcePresentation data coordinate)
    (path : StablePath data) {i : ℕ} (hi : i < (orderedRow fd.pathEnds path).length) :
    (((orderedRow fd.pathEnds path)[i]).1.1 : target.V × target.V) =
        ((rowVertex fd path i).1.1, (rowVertex fd path (i + 1)).1.1) ∨
      (((orderedRow fd.pathEnds path)[i]).1.1 : target.V × target.V) =
        ((rowVertex fd path (i + 1)).1.1, (rowVertex fd path i).1.1) := by
  let edge := (orderedRow fd.pathEnds path)[i]
  let vertex := rowVertex fd path i
  have hInc := rowVertex_incident fd path hi
  have hEnds : data.sourceEnds edge = (vertex, otherEnd data edge vertex) ∨
      data.sourceEnds edge = (otherEnd data edge vertex, vertex) := by
    unfold otherEnd
    split_ifs with h
    · exact Or.inl (Prod.ext h rfl)
    · exact Or.inr (Prod.ext rfl (hInc.resolve_left h))
  have hNext : rowVertex fd path (i + 1) = otherEnd data edge vertex := walkVertex_succ _ _ hi
  rw [hNext]
  rcases hEnds with h | h
  · exact Or.inl (congrArg (fun ends : data.SourceVertex × data.SourceVertex ↦
      (ends.1.1.1, ends.2.1.1)) h)
  · exact Or.inr (congrArg (fun ends : data.SourceVertex × data.SourceVertex ↦
      (ends.1.1.1, ends.2.1.1)) h)

/-- Every surviving source vertex above a target leaf is the unique leaf
core vertex; the remaining leaf blocks are entirely pendant. -/
theorem surviving_leaf_data
    (fd : FullDimensionalSourcePresentation data coordinate)
    {vertex : data.SourceVertex} (hSurvives : 0 < nonDanglingValency data vertex)
    (hLeaf : IsLeafVertex target vertex.1.1) :
    nonDanglingValency data vertex = 2 ∧
      data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 2 := by
  have hBlock : (⟨vertex.1.2, vertex.2⟩ : (data.vertexPartition vertex.1.1).Blocks) =
      LeafFibre.coreBlock fd hLeaf := by
    by_contra hNe
    have hZero := LeafFibre.nonDanglingValency_other fd hLeaf hNe
    change nonDanglingValency data vertex = 0 at hZero
    omega
  have hVertex : vertex = LeafFibre.coreVertex fd hLeaf :=
    congrArg (blockVertex data vertex.1.1) hBlock
  exact ⟨Eq.mp (congrArg (fun v ↦ nonDanglingValency data v = 2) hVertex.symm)
      (LeafFibre.nonDanglingValency_coreVertex fd hLeaf),
    hBlock ▸ LeafFibre.localRamification_coreBlock fd hLeaf⟩

/-- An actual stable-row path end cannot project to a target leaf. -/
theorem start_not_leaf (fd : FullDimensionalSourcePresentation data coordinate)
    (path : StablePath data) : ¬ IsLeafVertex target (rowVertex fd path 0).1.1 := by
  classical
  intro hLeaf
  have hStart := startEdge_isPathEnd fd.pathEnds path
  have hPos : 0 < nonDanglingValency data (startVertex fd.pathEnds path) := by
    rw [← card_nonDanglingIncident]
    apply Finset.card_pos.mpr
    exact ⟨(startEdge fd.pathEnds path).1,
      (mem_nonDanglingIncident data _ _).mpr ⟨(startEdge fd.pathEnds path).2, hStart.1⟩⟩
  exact hStart.2 (surviving_leaf_data fd hPos hLeaf).1

theorem prefixPosition_succ (fd : FullDimensionalSourcePresentation data coordinate)
    (z : coordinate → ℚ) (path : StablePath data)
    {i : ℕ} (hi : i < (orderedRow fd.pathEnds path).length) :
    prefixPosition fd z path (i + 1) = prefixPosition fd z path i +
      z (fd.labelling.targetEdge.symm ((orderedRow fd.pathEnds path)[i]).1.1) /
        (data.sourceEdgeIndex (orderedRow fd.pathEnds path)[i] : ℚ) := by
  simp only [prefixPosition, List.take_succ_eq_append_getElem hi, List.map_append,
    List.map_singleton, List.sum_append, List.sum_singleton]

/-- Telescoping the leaf correction proves 2-integrality on every prefix
of an actual unit-index row, without enumerating its hairpin. -/
theorem corrected_prefix_mem_of_unit
    (fd : FullDimensionalSourcePresentation data coordinate)
    (y : coordinate → ℤ) (z : coordinate → ℚ)
    (hSystem : (LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec z =
      fun row ↦ (y row : ℚ)) (hOdd : Odd (fdAbsMultNat fd))
    {path : StablePath data} (hUnit : ∀ edge, OnRow data path edge → data.sourceEdgeIndex edge = 1)
    (j : ℕ) (hj : j ≤ (orderedRow fd.pathEnds path).length) :
    prefixPosition fd z path j - leafPotential fd z (rowVertex fd path j).1.1
      ∈ oddDenominatorSubring := by
  induction j with
  | zero =>
    simp only [prefixPosition, List.take_zero, List.map_nil, List.sum_nil,
      leafPotential, dite_eq_right (start_not_leaf fd path), sub_zero]
    exact oddDenominatorSubring.zero_mem
  | succ i ih =>
    have hi : i < (orderedRow fd.pathEnds path).length := by omega
    have hOn := (mem_orderedRow_iff fd.pathEnds path _).mp (List.getElem_mem hi)
    have hStep := adjusted_step_mem fd y z hSystem hOdd
      ((orderedRow fd.pathEnds path)[i]).1.1
      (rowVertex fd path i).1.1 (rowVertex fd path (i + 1)).1.1 (row_target_ends fd path hi)
    have hSum := oddDenominatorSubring.add_mem (ih (by omega)) hStep
    rw [prefixPosition_succ fd z path hi, hUnit _ hOn, Nat.cast_one, div_one]
    convert hSum using 1
    ring

/-- On a unit-index row the leaf correction vanishes off target leaves;
at a leaf the actual retracted coefficient vanishes for an internal root. -/
theorem weighted_prefix_mem_of_unit
    (fd : FullDimensionalSourcePresentation data coordinate)
    (y : coordinate → ℤ) (z : coordinate → ℚ)
    (hSystem : (LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec z =
      fun row ↦ (y row : ℚ)) (hOdd : Odd (fdAbsMultNat fd))
    {path : StablePath data} (hUnit : ∀ edge, OnRow data path edge → data.sourceEdgeIndex edge = 1)
    {root : target.V} (hInternal : ¬ IsLeafVertex target root)
    {i : ℕ} (hi : i + 1 < (orderedRow fd.pathEnds path).length) :
    (retractedFibre root (retractVertex (rowVertex fd path (i + 1))) : ℚ) *
      prefixPosition fd z path (i + 1) ∈ oddDenominatorSubring := by
  classical
  by_cases hLeaf : IsLeafVertex target (rowVertex fd path (i + 1)).1.1
  · have hValency := rowVertex_valency fd path hi
    have hRam := (surviving_leaf_data fd (by omega) hLeaf).2
    rw [coefficient_of_ramification_two fd hValency hRam hInternal, Int.cast_zero, zero_mul]
    exact oddDenominatorSubring.zero_mem
  · have hPos := corrected_prefix_mem_of_unit fd y z hSystem hOdd hUnit (i + 1) hi.le
    simp only [leafPotential, dite_eq_right hLeaf, sub_zero] at hPos
    exact oddDenominatorSubring.mul_mem (intCast_mem _ _) hPos

/-- The hairpin case. Unit indices follow from the actual failure of leaf
avoidance (`EdgeDenominator.sourceEdgeIndex_eq_one_of_passesAboveLeaf`); they
are not assumed here. -/
theorem weighted_prefix_mem_of_hairpin
    (fd : FullDimensionalSourcePresentation data coordinate)
    (y : coordinate → ℤ) (z : coordinate → ℚ)
    (hSystem : (LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec z =
      fun row ↦ (y row : ℚ)) (hOdd : Odd (fdAbsMultNat fd))
    {path : StablePath data} (hHairpin : ¬ RowAvoidsLeaves data path)
    {root : target.V} (hInternal : ¬ IsLeafVertex target root)
    {i : ℕ} (hi : i + 1 < (orderedRow fd.pathEnds path).length) :
    (retractedFibre root (retractVertex (rowVertex fd path (i + 1))) : ℚ) *
      prefixPosition fd z path (i + 1) ∈ oddDenominatorSubring := by
  classical
  have hPasses : EdgeDenominator.PassesAboveLeaf fd.labelling (fd.labelling.row path) := by
    by_contra h
    apply hHairpin
    simpa only [Equiv.symm_apply_apply] using
      (rowAvoidsLeaves_iff_not_passesAboveLeaf fd.labelling (fd.labelling.row path)).mpr h
  apply weighted_prefix_mem_of_unit fd y z hSystem hOdd ?_ hInternal hi
  intro edge hEdge
  apply EdgeDenominator.sourceEdgeIndex_eq_one_of_passesAboveLeaf fd hPasses
  apply (mem_rowEdges_iff_onRow fd.labelling (fd.labelling.row path) edge).mpr
  simpa only [Equiv.symm_apply_apply] using hEdge

/-- The complete row-by-row source-position conclusion: every interior chip
term has odd denominator, with its actual coefficient and actual walk position. -/
theorem weighted_prefix_mem
    (fd : FullDimensionalSourcePresentation data coordinate)
    (y : coordinate → ℤ) (z : coordinate → ℚ)
    (hSystem : (LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec z =
      fun row ↦ (y row : ℚ)) (hOdd : Odd (fdAbsMultNat fd))
    (path : StablePath data) {root : target.V} (hInternal : ¬ IsLeafVertex target root)
    {i : ℕ} (hi : i + 1 < (orderedRow fd.pathEnds path).length) :
    (retractedFibre root (retractVertex (rowVertex fd path (i + 1))) : ℚ) *
      prefixPosition fd z path (i + 1) ∈ oddDenominatorSubring := by
  classical
  by_cases hAvoid : RowAvoidsLeaves data path
  · exact RowLeafAvoidingPosition.weighted_prefix_mem_of_leafAvoids fd y z hSystem hOdd
      hAvoid root hi
  · exact weighted_prefix_mem_of_hairpin fd y z hSystem hOdd hAvoid hInternal hi

/-- All row-position terms for a counted member, on its actual request slot. -/
theorem member_weighted_prefix_mem {n p : ℕ}
    {core : Utilities.Certificate.ExplicitPotential.Core n p} (y : Fin p → ℤ)
    (member : FibreMember core (fun slot ↦ (y slot : ℚ)) degree)
    (hOdd : Odd member.oddMult) (slot : Fin p)
    {root : member.target.V} (hInternal : ¬ IsLeafVertex member.target root)
    {i : ℕ}
    (hi : i + 1 < (orderedRow member.fullDim.pathEnds (member.ident.row.symm slot)).length) :
    (retractedFibre root
      (retractVertex (rowVertex member.fullDim (member.ident.row.symm slot) (i + 1))) : ℚ) *
      prefixPosition member.fullDim member.coords (member.ident.row.symm slot) (i + 1)
        ∈ oddDenominatorSubring :=
  weighted_prefix_mem member.fullDim
    (fun row ↦ y (member.ident.row (member.fullDim.labelling.row.symm row)))
    member.coords member.realizes hOdd (member.ident.row.symm slot) hInternal hi

end DraismaVargas.Count.RowHairpinPosition

