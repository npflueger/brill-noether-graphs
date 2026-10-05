module

public import DraismaVargasCount.RowChipCoefficient
public import DraismaVargasCount.RowWalk
public import Utilities.Subdivision.SlotMoment
public import DraismaVargasCount.OddDenominator
public import DraismaVargas.LocalCases.OrientedTraversal

@[expose] public section

/-!
# Ordered-row positions, and 2-integral weighted positions on an unramified row

`rowVertex` follows the source traversal of an ordered stable row; `prefixPosition`
sums its literal source lengths. Its full length is the corresponding matrix
row, and on a counted member it is precisely the request slot selected by
`CoreIdentification.row`. On an unramified leaf-avoiding row of a member of odd
multiplicity the weighted positions are 2-integral: the producer combines the
pendant-retraction coefficients of the chips (`PendantRetraction.retractedFibre`) with the
odd denominators of the coordinates (`OddDenominator.odd_leafAdjustedCoords_den`), and the
local degree cancels the common source index in each prefix term.

Integral slot cuts and orientation reversal preserve each weighted position,
not merely the total moment over a union of slots. Not treated here: rows with a
transition or a hairpin, and the transport from these source-walk positions to the
interior offsets of the realized subdivision divisor.  These are the inputs of the
slot-moment argument by which a pencil descends to an odd subdivision.
-/

namespace DraismaVargas.Count.RowPosition

open DraismaVargas.Infrastructure GluingDatum
open DraismaVargas.LocalCases W4StableSource FullDimensionalSource
open StableLocalProperties OrientedTraversal
open RowWalk PendantRetraction RowChipCoefficient SlotMoment
open Utilities.Certificate.ExplicitPotential (Core)

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- The actual source vertex reached after `j` occurrences of an ordered stable row. -/
noncomputable def rowVertex (fd : FullDimensionalSourcePresentation data coordinate)
    (path : StablePath data) (j : ℕ) : data.SourceVertex :=
  walkVertex data (orderedRow fd.pathEnds path) (startVertex fd.pathEnds path) j

/-- The rational position of that vertex, as the sum of the actual source
edge lengths along the prefix. -/
noncomputable def prefixPosition (fd : FullDimensionalSourcePresentation data coordinate)
    (z : coordinate → ℚ) (path : StablePath data) (j : ℕ) : ℚ :=
  (((orderedRow fd.pathEnds path).take j).map fun edge ↦
    z (fd.labelling.targetEdge.symm edge.1.1) / (data.sourceEdgeIndex edge : ℚ)).sum

theorem orderedRow_start (fd : FullDimensionalSourcePresentation data coordinate)
    (path : StablePath data) (h : 0 < (orderedRow fd.pathEnds path).length) :
    IsPathEnd data (orderedRow fd.pathEnds path)[0] (startVertex fd.pathEnds path) := by
  have hHead := orderedRow_head? fd.pathEnds path
  rw [head?_eq_getElem _ h, Option.some.injEq] at hHead
  rw [hHead]
  exact startEdge_isPathEnd fd.pathEnds path

theorem rowVertex_valency (fd : FullDimensionalSourcePresentation data coordinate)
    (path : StablePath data) {j : ℕ} (h : j + 1 < (orderedRow fd.pathEnds path).length) :
    nonDanglingValency data (rowVertex fd path (j + 1)) = 2 :=
  walkVertex_succ_valency (orderedRow_nodup fd.pathEnds path)
    (fun edge hEdge ↦ ((mem_orderedRow_iff fd.pathEnds path edge).mp hEdge).survives)
    (orderedRow_chain fd.pathEnds path) (orderedRow_start fd path) h

theorem rowVertex_incident (fd : FullDimensionalSourcePresentation data coordinate)
    (path : StablePath data) {j : ℕ} (h : j < (orderedRow fd.pathEnds path).length) :
    Incident data (orderedRow fd.pathEnds path)[j] (rowVertex fd path j) :=
  walkVertex_incident (orderedRow_nodup fd.pathEnds path)
    (fun edge hEdge ↦ ((mem_orderedRow_iff fd.pathEnds path edge).mp hEdge).survives)
    (orderedRow_chain fd.pathEnds path) (orderedRow_start fd path) h

/-- Traversal ordering does not change the actual length-matrix row. -/
theorem prefixPosition_full (fd : FullDimensionalSourcePresentation data coordinate)
    (z : coordinate → ℚ) (path : StablePath data) :
    prefixPosition fd z path (orderedRow fd.pathEnds path).length =
      (LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec z
        (fd.labelling.row path) := by
  have hPerm : (orderedRow fd.pathEnds path).Perm
      (fd.labelling.path (fd.labelling.row path)) := by
    have hNodup : (fd.labelling.path (fd.labelling.row path)).Nodup :=
      List.Nodup.filter _ Finset.univ.nodup_toList
    apply List.perm_ext_iff_of_nodup (orderedRow_nodup fd.pathEnds path)
      hNodup |>.mpr
    intro edge
    rw [mem_orderedRow_iff, fd.labelling.mem_path_iff]
    constructor
    · rintro ⟨hSurvives, hPath⟩
      exact ⟨hSurvives, congrArg fd.labelling.row hPath⟩
    · rintro ⟨hSurvives, hPath⟩
      exact ⟨hSurvives, fd.labelling.row.injective hPath⟩
  unfold prefixPosition
  rw [List.take_length, LengthMatrixPresentation.matrix_mulVec]
  exact (hPerm.map (fun edge ↦
    z (fd.labelling.targetEdge.symm edge.1.1) / (data.sourceEdgeIndex edge : ℚ))).sum_eq

/-- A member's stable row is already identified with one request slot, and
the actual prefix length of the entire row equals precisely that slot length. -/
theorem member_prefixPosition_full {n p : ℕ}
    {core : Core n p} {y : Fin p → ℚ}
    (member : FibreMember core y degree) (slot : Fin p) :
    prefixPosition member.fullDim member.coords (member.ident.row.symm slot)
      (orderedRow member.fullDim.pathEnds (member.ident.row.symm slot)).length = y slot := by
  rw [prefixPosition_full, member.realizes]
  simp

/-- The odd coordinate denominators of an odd-multiplicity presentation
(`OddDenominator.odd_leafAdjustedCoords_den`) make each target length on a leaf-avoiding
actual row 2-integral. -/
theorem row_target_length_mem
    (fd : FullDimensionalSourcePresentation data coordinate)
    (y : coordinate → ℤ) (z : coordinate → ℚ)
    (hSystem : (LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec z =
      fun row ↦ (y row : ℚ)) (hOdd : Odd (fdAbsMultNat fd))
    {path : StablePath data} (hAvoid : RowAvoidsLeaves data path)
    {edge : data.SourceEdge} (hEdge : OnRow data path edge) :
    z (fd.labelling.targetEdge.symm edge.1.1) ∈ oddDenominatorSubring := by
  classical
  have hNot : fd.labelling.targetEdge.symm edge.1.1 ∉
      leafColumns fd.labelling.presentation := by
    intro hMem
    obtain ⟨leaf, hLeaf, hIncident⟩ := (mem_leafColumns _ _).mp hMem
    apply hAvoid edge hEdge leaf hLeaf
    simpa only [StableLengthMatrixLabelling.presentation, Equiv.apply_symm_apply]
      using hIncident
  have hDen := OddDenominator.odd_leafAdjustedCoords_den fd y z hSystem hOdd
    (fd.labelling.targetEdge.symm edge.1.1)
  simpa only [OddDenominator.leafAdjustedCoords, ite_eq_right hNot,
    mem_oddDenominatorSubring] using hDen

/-- At an interior vertex of an unramified row, the local degree equals
the index of every occurrence on that row. -/
theorem local_degree_eq_row_index
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} (hUnram : RowUnramified data path)
    {vertex : data.SourceVertex} (hValency : nonDanglingValency data vertex = 2)
    {edge : data.SourceEdge} (hEdge : OnRow data path edge)
    (hIncident : Incident data edge vertex) {other : data.SourceEdge}
    (hOther : OnRow data path other) :
    (data.vertexPartition vertex.1.1).blockCard vertex.1.2 = data.sourceEdgeIndex other := by
  obtain ⟨first, second, hFirst, hSecond, hNe⟩ := exists_two_survivors hValency
  have hFirstRow := onRow_of_incident hValency hEdge hIncident hFirst first.2
  have hSecondRow := onRow_of_incident hValency hEdge hIncident hSecond second.2
  have hSum := IndexPattern.sourceEdgeIndex_add_sourceEdgeIndex fd hValency
    hFirst first.2 hSecond second.2 hNe
  have hZero := hUnram vertex edge hEdge hIncident hValency
  have hEqFirst := sourceEdgeIndex_eq_of_rowUnramified fd.danglingEdgeNoGlue fd.pathEnds
    hUnram hFirstRow hOther
  have hEqSecond := sourceEdgeIndex_eq_of_rowUnramified fd.danglingEdgeNoGlue fd.pathEnds
    hUnram hSecondRow hOther
  rw [hZero, hEqFirst, hEqSecond] at hSum
  omega

/-- Actual weighted source positions on an unramified leaf-avoiding row
are 2-integral. Both the position and the coefficient are produced from the
ordered source walk and canonical pendant pushforward. -/
theorem weighted_prefix_mem_of_unramified
    (fd : FullDimensionalSourcePresentation data coordinate)
    (y : coordinate → ℤ) (z : coordinate → ℚ)
    (hSystem : (LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec z =
      fun row ↦ (y row : ℚ)) (hOdd : Odd (fdAbsMultNat fd))
    {path : StablePath data} (hUnram : RowUnramified data path)
    (hAvoid : RowAvoidsLeaves data path) (root : target.V)
    {j : ℕ} (hj : j + 1 < (orderedRow fd.pathEnds path).length) :
    (retractedFibre root (retractVertex (rowVertex fd path (j + 1))) : ℚ) *
      prefixPosition fd z path (j + 1) ∈ oddDenominatorSubring := by
  let vertex := rowVertex fd path (j + 1)
  let edge := (orderedRow fd.pathEnds path)[j + 1]
  have hValency := rowVertex_valency fd path hj
  have hIncident := rowVertex_incident fd path hj
  have hEdge : OnRow data path edge :=
    (mem_orderedRow_iff fd.pathEnds path edge).mp (List.getElem_mem hj)
  have hRam := hUnram vertex edge hEdge hIncident hValency
  rcases coefficient_of_ramification_zero fd hValency hRam root with hZero | hDegree
  · rw [hZero, Int.cast_zero, zero_mul]
    exact oddDenominatorSubring.zero_mem
  rw [hDegree, Int.cast_natCast]
  unfold prefixPosition
  rw [← List.sum_map_mul_left]
  apply oddDenominatorSubring.list_sum_mem
  intro term hTerm
  obtain ⟨item, hItem, rfl⟩ := List.mem_map.mp hTerm
  have hOn : OnRow data path item := (mem_orderedRow_iff fd.pathEnds path item).mp
    (List.mem_of_mem_take hItem)
  have hIndex := local_degree_eq_row_index fd hUnram hValency hEdge hIncident hOn
  have hPos : (data.sourceEdgeIndex item : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (GluingDatum.sourceEdgeIndex_pos data item))
  rw [hIndex]
  have hCancel : (data.sourceEdgeIndex item : ℚ) *
      (z (fd.labelling.targetEdge.symm item.1.1) / (data.sourceEdgeIndex item : ℚ)) =
      z (fd.labelling.targetEdge.symm item.1.1) := by field_simp
  rw [hCancel]
  exact row_target_length_mem fd y z hSystem hOdd hAvoid hOn

/-- The same producer on a counted member and its actual request slot. -/
theorem member_weighted_prefix_mem_of_unramified {n p : ℕ}
    {core : Core n p} (y : Fin p → ℤ)
    (member : FibreMember core (fun slot ↦ (y slot : ℚ)) degree)
    (hOdd : Odd member.oddMult) (slot : Fin p)
    (hUnram : RowUnramified member.data (member.ident.row.symm slot))
    (hAvoid : RowAvoidsLeaves member.data (member.ident.row.symm slot))
    (root : member.target.V) {j : ℕ}
    (hj : j + 1 < (orderedRow member.fullDim.pathEnds (member.ident.row.symm slot)).length) :
    (retractedFibre root
      (retractVertex (rowVertex member.fullDim (member.ident.row.symm slot) (j + 1))) : ℚ) *
      prefixPosition member.fullDim member.coords (member.ident.row.symm slot) (j + 1)
        ∈ oddDenominatorSubring :=
  weighted_prefix_mem_of_unramified member.fullDim
    (fun row ↦ y (member.ident.row (member.fullDim.labelling.row.symm row)))
    member.coords member.realizes hOdd hUnram hAvoid root hj

/-- Refining an oriented row at an integral position preserves each weighted
position's 2-integrality. This is the offset, rather than union-of-slots, rule. -/
theorem weighted_offset_mem (coefficient : ℤ) (position : ℚ) (anchor : ℤ)
    (hTerm : (coefficient : ℚ) * position ∈ oddDenominatorSubring) :
    (coefficient : ℚ) * (position - anchor) ∈ oddDenominatorSubring := by
  rw [mul_sub]
  exact oddDenominatorSubring.sub_mem hTerm
    (oddDenominatorSubring.mul_mem (intCast_mem _ coefficient) (intCast_mem _ anchor))

/-- Reversing a slot at integral total length also preserves each weighted
position's 2-integrality; no orientation convention is imposed on consumers. -/
theorem weighted_reverse_mem (coefficient : ℤ) (position : ℚ) (length : ℤ)
    (hTerm : (coefficient : ℚ) * position ∈ oddDenominatorSubring) :
    (coefficient : ℚ) * (length - position) ∈ oddDenominatorSubring := by
  rw [mul_sub]
  exact oddDenominatorSubring.sub_mem
    (oddDenominatorSubring.mul_mem (intCast_mem _ coefficient) (intCast_mem _ length)) hTerm

end DraismaVargas.Count.RowPosition
