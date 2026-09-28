import DraismaVargasCount.RowVertexEnumeration

/-!
# Deriving the request-slot orientation from actual source endpoints

The branch/core incidence dictionary, not a new row dictionary receipt,
identifies the two ends of the actual walk with the request slot's ends.
-/

namespace DraismaVargas.Count.RowSlotOrientation

open DraismaVargas.Infrastructure GluingDatum
open DraismaVargas.LocalCases W4StableSource FullDimensionalSource
open StableLocalProperties OrientedTraversal StablePathCount StableGraphIncidence
open RowWalk RowPosition RowVertexEnumeration
open Utilities.Certificate.SubdivisionGraph

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

theorem orderedRow_length_pos
    (fd : FullDimensionalSourcePresentation data coordinate) (path : StablePath data) :
    0 < (orderedRow fd.pathEnds path).length :=
  List.length_pos_of_mem (startEdge_mem_orderedRow fd.pathEnds path)

/-- The actual terminal walk vertex is a path end, not merely an arbitrarily
selected endpoint incident to the last occurrence. -/
theorem finish_valency_ne_two
    (fd : FullDimensionalSourcePresentation data coordinate) (path : StablePath data) :
    nonDanglingValency data
      (rowVertex fd path (orderedRow fd.pathEnds path).length) ≠ 2 := by
  intro hValency
  have hPos := orderedRow_length_pos fd path
  have hLast : (orderedRow fd.pathEnds path).length - 1 <
      (orderedRow fd.pathEnds path).length := by omega
  have hOn := (mem_orderedRow_iff fd.pathEnds path _).mp (List.getElem_mem hLast)
  have hIncident : Incident data
      (orderedRow fd.pathEnds path)[(orderedRow fd.pathEnds path).length - 1]
      (rowVertex fd path (orderedRow fd.pathEnds path).length) := by
    have hI := (walkVertex_succ_incident hLast : Incident data
      (orderedRow fd.pathEnds path)[(orderedRow fd.pathEnds path).length - 1]
      (rowVertex fd path ((orderedRow fd.pathEnds path).length - 1 + 1)))
    have hLen : (orderedRow fd.pathEnds path).length - 1 + 1 =
        (orderedRow fd.pathEnds path).length := by omega
    rw [hLen] at hI
    exact hI
  obtain ⟨i, hEq⟩ := exists_interior_index fd path hValency hOn hIncident
  exact interior_ne_finish fd path (by have := i.isLt; omega) hEq

theorem start_branch (fd : FullDimensionalSourcePresentation data coordinate)
    (path : StablePath data) : 3 ≤ nonDanglingValency data (rowVertex fd path 0) := by
  have hNotTwo := (startEdge_isPathEnd fd.pathEnds path).2
  have hNotOne := NonDanglingValency.nonDanglingValency_ne_one data fd.connected
    (rowVertex fd path 0)
  have hNotZero := ClassInjectivity.nonDanglingValency_ne_zero_of_incident data
    (startEdge fd.pathEnds path).2 (startEdge_isPathEnd fd.pathEnds path).1
  change nonDanglingValency data (rowVertex fd path 0) ≠ 2 at hNotTwo
  change nonDanglingValency data (rowVertex fd path 0) ≠ 0 at hNotZero
  omega

theorem finish_branch (fd : FullDimensionalSourcePresentation data coordinate)
    (path : StablePath data) :
    3 ≤ nonDanglingValency data (rowVertex fd path (orderedRow fd.pathEnds path).length) := by
  have hNotTwo := finish_valency_ne_two fd path
  have hNotOne := NonDanglingValency.nonDanglingValency_ne_one data fd.connected
    (rowVertex fd path (orderedRow fd.pathEnds path).length)
  have hPos := orderedRow_length_pos fd path
  have hLast : (orderedRow fd.pathEnds path).length - 1 <
      (orderedRow fd.pathEnds path).length := by omega
  have hOn := (mem_orderedRow_iff fd.pathEnds path _).mp (List.getElem_mem hLast)
  have hIncident : Incident data
      (orderedRow fd.pathEnds path)[(orderedRow fd.pathEnds path).length - 1]
      (rowVertex fd path (orderedRow fd.pathEnds path).length) := by
    have hI := (walkVertex_succ_incident hLast : Incident data
      (orderedRow fd.pathEnds path)[(orderedRow fd.pathEnds path).length - 1]
      (rowVertex fd path ((orderedRow fd.pathEnds path).length - 1 + 1)))
    have hLen : (orderedRow fd.pathEnds path).length - 1 + 1 =
        (orderedRow fd.pathEnds path).length := by omega
    rw [hLen] at hI
    exact hI
  have hNotZero := ClassInjectivity.nonDanglingValency_ne_zero_of_incident data hOn.survives hIncident
  omega

noncomputable def startBranch (fd : FullDimensionalSourcePresentation data coordinate)
    (path : StablePath data) : BranchVertex data := ⟨rowVertex fd path 0, start_branch fd path⟩

noncomputable def finishBranch (fd : FullDimensionalSourcePresentation data coordinate)
    (path : StablePath data) : BranchVertex data :=
  ⟨rowVertex fd path (orderedRow fd.pathEnds path).length, finish_branch fd path⟩

/-- A branch vertex met by a literal row occurrence is one of that actual
walk's two ends. No interior source vertex can have branch valency. -/
theorem branch_incident_eq_endpoint
    (fd : FullDimensionalSourcePresentation data coordinate) (path : StablePath data)
    (branch : BranchVertex data) {edge : data.SourceEdge}
    (hEdge : OnRow data path edge) (hIncident : Incident data edge branch.1) :
    branch = startBranch fd path ∨ branch = finishBranch fd path := by
  obtain ⟨i, hi, hI⟩ := List.mem_iff_getElem.mp ((mem_orderedRow_iff fd.pathEnds path edge).mpr hEdge)
  have hIncident' : Incident data (orderedRow fd.pathEnds path)[i] branch.1 := hI ▸ hIncident
  rcases eq_or_eq_otherEnd data (rowVertex_incident fd path hi) hIncident' with h | h
  · change branch.1 = rowVertex fd path i at h
    by_cases hi0 : i = 0
    · apply Or.inl
      apply Subtype.ext
      change branch.1 = rowVertex fd path 0
      exact hi0 ▸ h
    · have hPred : i - 1 + 1 = i := by omega
      have hValency := rowVertex_valency fd path (j := i - 1) (by omega)
      rw [hPred, ← h] at hValency
      have := branch.2
      omega
  · have hNext : branch.1 = rowVertex fd path (i + 1) :=
      h.trans (walkVertex_succ _ _ hi).symm
    by_cases hLen : i + 1 = (orderedRow fd.pathEnds path).length
    · apply Or.inr
      apply Subtype.ext
      change branch.1 = rowVertex fd path (orderedRow fd.pathEnds path).length
      exact hLen ▸ hNext
    · have hValency := rowVertex_valency fd path (j := i) (by omega)
      rw [← hNext] at hValency
      have := branch.2
      omega

/-- The actual row's branch labels are exactly the two request-slot labels,
in one order. This derives orientation from the given incidence matching;
there is no assumed geometric `RowDictionary`. -/
theorem member_endpoints {n p : ℕ} (spec : Spec n p)
    (member : FibreMember spec.core (fun slot ↦ (spec.length slot : ℚ)) degree)
    (slot : Fin p) :
    (member.ident.vertex (startBranch member.fullDim (member.ident.row.symm slot)) =
        spec.core.tail slot ∧
      member.ident.vertex (finishBranch member.fullDim (member.ident.row.symm slot)) =
        spec.core.head slot) ∨
    (member.ident.vertex (startBranch member.fullDim (member.ident.row.symm slot)) =
        spec.core.head slot ∧
      member.ident.vertex (finishBranch member.fullDim (member.ident.row.symm slot)) =
        spec.core.tail slot) := by
  classical
  have hEndpoint (label : Fin n)
      (hLabel : label = spec.core.tail slot ∨ label = spec.core.head slot) :
      label = member.ident.vertex (startBranch member.fullDim (member.ident.row.symm slot)) ∨
      label = member.ident.vertex (finishBranch member.fullDim (member.ident.row.symm slot)) := by
    have hPos : 0 < incidenceCount member.data (member.ident.vertex.symm label).1
        (member.ident.row.symm slot) := by
      rw [member.ident.incidence, Equiv.apply_symm_apply]
      unfold coreIncidence
      rcases hLabel with rfl | rfl <;> split_ifs <;> omega
    obtain ⟨edge, hInc, hPath⟩ := (incidenceCount_pos_iff _ _ _).mp hPos
    rcases branch_incident_eq_endpoint member.fullDim (member.ident.row.symm slot)
        (member.ident.vertex.symm label) ⟨edge.2, hPath⟩ hInc with h | h
    · exact Or.inl (by simpa only [Equiv.apply_symm_apply] using congrArg member.ident.vertex h)
    · exact Or.inr (by simpa only [Equiv.apply_symm_apply] using congrArg member.ident.vertex h)
  have hTail := hEndpoint (spec.core.tail slot) (Or.inl rfl)
  have hHead := hEndpoint (spec.core.head slot) (Or.inr rfl)
  have hNe := spec.core_loopless slot
  rcases hTail with hTail | hTail <;> rcases hHead with hHead | hHead
  · exact False.elim (hNe (hTail.trans hHead.symm))
  · exact Or.inl ⟨hTail.symm, hHead.symm⟩
  · exact Or.inr ⟨hHead.symm, hTail.symm⟩
  · exact False.elim (hNe (hTail.trans hHead.symm))

/-- The direction chosen by the actual source/core identification. -/
noncomputable def memberReverse {n p : ℕ} (spec : Spec n p)
    (member : FibreMember spec.core (fun slot ↦ (spec.length slot : ℚ)) degree)
    (slot : Fin p) : Bool :=
  decide (member.ident.vertex (startBranch member.fullDim (member.ident.row.symm slot)) ≠
    spec.core.tail slot)

theorem memberReverse_endpoints {n p : ℕ} (spec : Spec n p)
    (member : FibreMember spec.core (fun slot ↦ (spec.length slot : ℚ)) degree)
    (slot : Fin p) :
    member.ident.vertex (startBranch member.fullDim (member.ident.row.symm slot)) =
        (if memberReverse spec member slot then spec.core.head slot else spec.core.tail slot) ∧
    member.ident.vertex (finishBranch member.fullDim (member.ident.row.symm slot)) =
        (if memberReverse spec member slot then spec.core.tail slot else spec.core.head slot) := by
  classical
  rcases member_endpoints spec member slot with ⟨hStart, hFinish⟩ | ⟨hStart, hFinish⟩
  · have hRev : memberReverse spec member slot = false := by
      unfold memberReverse
      apply decide_eq_false
      exact not_not.mpr hStart
    simp only [hRev, Bool.false_eq_true, ↓reduceIte, hStart, hFinish, and_self]
  · have hNe := (spec.core_loopless slot).symm
    have hRev : memberReverse spec member slot = true := by
      unfold memberReverse
      apply decide_eq_true
      rw [hStart]
      exact hNe
    simp only [hRev, ↓reduceIte, hStart, hFinish, and_self]

end DraismaVargas.Count.RowSlotOrientation

