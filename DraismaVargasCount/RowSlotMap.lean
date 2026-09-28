import DraismaVargasCount.RowSlotOrientation
import Utilities.Subdivision.SubdivisionSeparator

/-!
# Actual row positions on the scaled request specification

Every position is the literal sum of integral source lengths, measured in the
direction derived from the member's incidence dictionary. Zero-length source
steps therefore have the same image. This is a map, not a row-dictionary field.
-/

namespace DraismaVargas.Count.RowSlotMap

open DraismaVargas.Infrastructure GluingDatum
open DraismaVargas.LocalCases W4StableSource FullDimensionalSource
open RowWalk RowPosition RowRealizedPosition RowSlotOrientation
open Utilities.Certificate.SubdivisionGraph

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

theorem integralPrefix_le_full
    (fd : FullDimensionalSourcePresentation data coordinate)
    (realization : data.NonnegativeIntegralRealization) (path : StablePath data) (j : ℕ) :
    integralPrefix fd realization path j ≤
      integralPrefix fd realization path (orderedRow fd.pathEnds path).length := by
  have hSplit : integralPrefix fd realization path j +
      ((orderedRow fd.pathEnds path).drop j |>.map realization.sourceLength).sum =
      integralPrefix fd realization path (orderedRow fd.pathEnds path).length := by
    simp only [integralPrefix, List.take_length]
    rw [← List.sum_append, ← List.map_append, List.take_append_drop]
  omega

theorem integralPrefix_succ
    (fd : FullDimensionalSourcePresentation data coordinate)
    (realization : data.NonnegativeIntegralRealization) (path : StablePath data)
    {j : ℕ} (hj : j < (orderedRow fd.pathEnds path).length) :
    integralPrefix fd realization path (j + 1) = integralPrefix fd realization path j +
      realization.sourceLength (orderedRow fd.pathEnds path)[j] := by
  simp only [integralPrefix, List.take_succ_eq_append_getElem hj, List.map_append,
    List.map_singleton, List.sum_append, List.sum_singleton]

variable {n p : ℕ} (spec : Spec n p)
  (member : FibreMember spec.core (fun slot ↦ (spec.length slot : ℚ)) degree)
  (hClosed : member.Closed)

theorem member_integralPrefix_le (slot : Fin p) (j : ℕ) :
    integralPrefix member.fullDim (memberRealization member hClosed)
      (member.ident.row.symm slot) j ≤ memberScale member * spec.length slot := by
  have h := integralPrefix_le_full member.fullDim (memberRealization member hClosed)
    (member.ident.row.symm slot) j
  rw [member_integralPrefix_full spec.length member hClosed slot] at h
  exact h

/-- The actual integral offset from the requested slot's tail. -/
noncomputable def rowOffset (slot : Fin p) (j : ℕ) :
    (spec.scale (memberScale member) (memberScale_pos member)).PathPosition slot :=
  ⟨if memberReverse spec member slot then
      memberScale member * spec.length slot - integralPrefix member.fullDim
        (memberRealization member hClosed) (member.ident.row.symm slot) j
    else integralPrefix member.fullDim (memberRealization member hClosed)
      (member.ident.row.symm slot) j,
    by
      have h := member_integralPrefix_le spec member hClosed slot j
      simp only [Spec.scale_length]
      split_ifs <;> omega⟩

/-- The row's source vertex after `j` actual occurrences, placed on the
literal scaled request graph. Endpoint positions are handled by `pathVertex`. -/
noncomputable def rowPoint (slot : Fin p) (j : ℕ) :
    (spec.scale (memberScale member) (memberScale_pos member)).Vertex :=
  (spec.scale (memberScale member) (memberScale_pos member)).pathVertex slot
    (rowOffset spec member hClosed slot j)

theorem rowPoint_eq_of_integralPrefix_eq (slot : Fin p) {i j : ℕ}
    (hEq : integralPrefix member.fullDim (memberRealization member hClosed)
        (member.ident.row.symm slot) i = integralPrefix member.fullDim
        (memberRealization member hClosed) (member.ident.row.symm slot) j) :
    rowPoint spec member hClosed slot i = rowPoint spec member hClosed slot j := by
  unfold rowPoint
  congr 1
  apply Fin.ext
  simp only [rowOffset, hEq]

/-- An actual zero-length occurrence is collapsed by the constructed map. -/
theorem rowPoint_zero_step (slot : Fin p) {j : ℕ}
    (hj : j < (orderedRow member.fullDim.pathEnds (member.ident.row.symm slot)).length)
    (hZero : (memberRealization member hClosed).sourceLength
      (orderedRow member.fullDim.pathEnds (member.ident.row.symm slot))[j] = 0) :
    rowPoint spec member hClosed slot (j + 1) = rowPoint spec member hClosed slot j := by
  apply rowPoint_eq_of_integralPrefix_eq
  rw [integralPrefix_succ _ _ _ hj, hZero, Nat.add_zero]

/-- The first actual row vertex lands at its own branch/core label, in
either source traversal direction. -/
theorem rowPoint_zero (slot : Fin p) :
    rowPoint spec member hClosed slot 0 =
      (spec.scale (memberScale member) (memberScale_pos member)).coreVertex
        (member.ident.vertex (startBranch member.fullDim (member.ident.row.symm slot))) := by
  have hEndpoint := (memberReverse_endpoints spec member slot).1
  unfold rowPoint
  by_cases hReverse : memberReverse spec member slot = true
  · have hOffset : rowOffset spec member hClosed slot 0 =
        ⟨(spec.scale (memberScale member) (memberScale_pos member)).length slot,
          Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp only [rowOffset, hReverse, ↓reduceIte, integralPrefix, List.take_zero,
        List.map_nil, List.sum_nil, Nat.sub_zero, Spec.scale_length]
    rw [hOffset, Spec.pathVertex_length]
    simp only [hReverse] at hEndpoint
    exact congrArg (spec.scale (memberScale member) (memberScale_pos member)).coreVertex hEndpoint.symm
  · have hOffset : rowOffset spec member hClosed slot 0 = ⟨0, by omega⟩ := by
      apply Fin.ext
      simp only [rowOffset, hReverse, Bool.false_eq_true, ↓reduceIte, integralPrefix, List.take_zero,
        List.map_nil, List.sum_nil]
    rw [hOffset, Spec.pathVertex_zero]
    simp only [hReverse] at hEndpoint
    exact congrArg (spec.scale (memberScale member) (memberScale_pos member)).coreVertex hEndpoint.symm

/-- The last actual row vertex likewise lands at its own branch label. -/
theorem rowPoint_full (slot : Fin p) :
    rowPoint spec member hClosed slot
      (orderedRow member.fullDim.pathEnds (member.ident.row.symm slot)).length =
      (spec.scale (memberScale member) (memberScale_pos member)).coreVertex
        (member.ident.vertex (finishBranch member.fullDim (member.ident.row.symm slot))) := by
  have hEndpoint := (memberReverse_endpoints spec member slot).2
  have hFull := member_integralPrefix_full spec.length member hClosed slot
  unfold rowPoint
  by_cases hReverse : memberReverse spec member slot = true
  · have hOffset : rowOffset spec member hClosed slot
          (orderedRow member.fullDim.pathEnds (member.ident.row.symm slot)).length =
        ⟨0, by omega⟩ := by
      apply Fin.ext
      simp only [rowOffset, hReverse, ↓reduceIte, hFull, Nat.sub_self]
    rw [hOffset, Spec.pathVertex_zero]
    simp only [hReverse, ↓reduceIte] at hEndpoint
    exact congrArg (spec.scale (memberScale member) (memberScale_pos member)).coreVertex hEndpoint.symm
  · have hOffset : rowOffset spec member hClosed slot
          (orderedRow member.fullDim.pathEnds (member.ident.row.symm slot)).length =
        ⟨(spec.scale (memberScale member) (memberScale_pos member)).length slot,
          Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp only [rowOffset, hReverse, Bool.false_eq_true, ↓reduceIte, hFull, Spec.scale_length]
    rw [hOffset, Spec.pathVertex_length]
    simp only [hReverse] at hEndpoint
    exact congrArg (spec.scale (memberScale member) (memberScale_pos member)).coreVertex hEndpoint.symm

/-- The constructed graph map has exactly the offset predicate used by the
collision pushforward, including reflected offsets in the reverse direction. -/
theorem rowPoint_eq_interior_iff (slot : Fin p) (j : ℕ)
    (offset : Fin ((spec.scale (memberScale member) (memberScale_pos member)).length slot - 1)) :
    rowPoint spec member hClosed slot j =
      (spec.scale (memberScale member) (memberScale_pos member)).interiorVertex slot offset ↔
    integralPrefix member.fullDim (memberRealization member hClosed)
      (member.ident.row.symm slot) j =
      (if memberReverse spec member slot then
        memberScale member * spec.length slot - (offset.val + 1) else offset.val + 1) := by
  let T := spec.scale (memberScale member) (memberScale_pos member)
  have hOffset : offset.val + 1 < T.length slot := by
    have h := offset.isLt
    change offset.val < T.length slot - 1 at h
    omega
  let point : T.PathPosition slot := ⟨offset.val + 1, by omega⟩
  have hPoint : T.pathVertex slot point = T.interiorVertex slot offset := by
    have hInterior : T.IsInteriorPosition slot point := ⟨by dsimp [point]; omega, hOffset⟩
    rw [T.pathVertex_eq_interiorVertex slot point hInterior]
    congr 1
  change T.pathVertex slot (rowOffset spec member hClosed slot j) = T.interiorVertex slot offset ↔ _
  rw [← hPoint, T.pathVertex_injective slot |>.eq_iff, Fin.ext_iff]
  have hPrefix := member_integralPrefix_le spec member hClosed slot j
  have hOffset' : offset.val + 1 ≤ memberScale member * spec.length slot := by
    simpa only [T, Spec.scale_length] using hOffset.le
  simp only [rowOffset, point]
  split_ifs <;> omega

/-- The previously constructed arithmetic divisor is exactly the finite
pushforward along this actual row map, not an assumed coefficient profile. -/
theorem interiorRowPushforward_eq_row_sum (root : member.target.V) (slot : Fin p)
    (offset : Fin ((spec.scale (memberScale member) (memberScale_pos member)).length slot - 1)) :
    orientedInteriorRowPushforward spec member hClosed root (memberReverse spec member)
      ((spec.scale (memberScale member) (memberScale_pos member)).interiorVertex slot offset) =
    ∑ i : Fin ((orderedRow member.fullDim.pathEnds (member.ident.row.symm slot)).length - 1),
      if rowPoint spec member hClosed slot (i.val + 1) =
        (spec.scale (memberScale member) (memberScale_pos member)).interiorVertex slot offset then
        PendantRetraction.retractedFibre root (PendantRetraction.retractVertex
          (rowVertex member.fullDim (member.ident.row.symm slot) (i.val + 1))) else 0 := by
  classical
  change collisionCoefficient _ _ _ _ _ = _
  unfold collisionCoefficient
  apply Finset.sum_congr rfl
  intro i _
  simp only [rowPoint_eq_interior_iff]

open scoped Classical in
/-- A pointwise identification directly with the original source pullback
fibre. It includes actual pendant retraction and actual integral slot location;
every original source vertex contributes once, even across zero collisions. -/
theorem interiorRowPushforward_eq_source_sum (root : member.target.V) (slot : Fin p)
    (offset : Fin ((spec.scale (memberScale member) (memberScale_pos member)).length slot - 1)) :
    orientedInteriorRowPushforward spec member hClosed root (memberReverse spec member)
      ((spec.scale (memberScale member) (memberScale_pos member)).interiorVertex slot offset) =
    ∑ vertex : member.data.SourceVertex,
      if vertex.1.1 = root ∧
        ∃ i : Fin ((orderedRow member.fullDim.pathEnds (member.ident.row.symm slot)).length - 1),
          PendantRetraction.retractVertex vertex = PendantRetraction.retractVertex
            (rowVertex member.fullDim (member.ident.row.symm slot) (i.val + 1)) ∧
          rowPoint spec member hClosed slot (i.val + 1) =
            (spec.scale (memberScale member) (memberScale_pos member)).interiorVertex slot offset then
        ((member.data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) else 0 := by
  classical
  change collisionCoefficient _ _ _ _ _ = _
  rw [RowVertexEnumeration.collisionCoefficient_eq_raw_fibre_sum]
  apply Finset.sum_congr rfl
  intro vertex _
  simp only [rowPoint_eq_interior_iff]

end DraismaVargas.Count.RowSlotMap

