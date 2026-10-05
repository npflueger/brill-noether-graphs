module

public import DraismaVargasCount.RowRealizedPosition

@[expose] public section

/-!
# Actual interior source vertices, each exactly once

The ordered row is an edge-simple traversal. At an interior vertex its two
surviving occurrences exhaust surviving valency two, so revisiting that
vertex would repeat an occurrence. These are source-vertex statements, before
zero-length contraction: coincident metric positions may still be distinct.
-/

namespace DraismaVargas.Count.RowVertexEnumeration

open DraismaVargas.Infrastructure GluingDatum
open DraismaVargas.LocalCases W4StableSource FullDimensionalSource
open StableLocalProperties OrientedTraversal
open RowWalk RowPosition RowRealizedPosition PendantRetraction

open scoped Classical

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- An occurrence meeting an interior vertex is one of its two adjacent
traversal occurrences. -/
theorem incident_interior_iff
    (fd : FullDimensionalSourcePresentation data coordinate) (path : StablePath data)
    {i : ℕ} (hi : i + 1 < (orderedRow fd.pathEnds path).length)
    {edge : data.SourceEdge} (hEdge : ¬ IsDangling data edge) :
    Incident data edge (rowVertex fd path (i + 1)) ↔
      edge = (orderedRow fd.pathEnds path)[i] ∨
      edge = (orderedRow fd.pathEnds path)[i + 1] := by
  have hi0 : i < (orderedRow fd.pathEnds path).length := by omega
  have hFirst := (mem_orderedRow_iff fd.pathEnds path _).mp (List.getElem_mem hi0)
  have hSecond := (mem_orderedRow_iff fd.pathEnds path _).mp (List.getElem_mem hi)
  have hFirstInc : Incident data (orderedRow fd.pathEnds path)[i]
      (rowVertex fd path (i + 1)) := walkVertex_succ_incident hi0
  have hSecondInc := rowVertex_incident fd path hi
  have hNe : (orderedRow fd.pathEnds path)[i] ≠ (orderedRow fd.pathEnds path)[i + 1] := by
    intro h
    have := (orderedRow_nodup fd.pathEnds path).getElem_inj_iff.mp h
    omega
  constructor
  · exact IndexPattern.eq_or_eq_of_nonDanglingValency_two (rowVertex_valency fd path hi)
      hFirst.survives hFirstInc hSecond.survives hSecondInc hNe hEdge
  · rintro (rfl | rfl)
    · exact hFirstInc
    · exact hSecondInc

/-- The interior enumeration used by the actual collision sum is injective
as an enumeration of source vertices. -/
theorem interior_injective (fd : FullDimensionalSourcePresentation data coordinate)
    (path : StablePath data) :
    Function.Injective (fun i : Fin ((orderedRow fd.pathEnds path).length - 1) ↦
      rowVertex fd path (i.val + 1)) := by
  intro i j hEq
  change rowVertex fd path (i.val + 1) = rowVertex fd path (j.val + 1) at hEq
  have hi : i.val + 1 < (orderedRow fd.pathEnds path).length := by have := i.isLt; omega
  have hj : j.val + 1 < (orderedRow fd.pathEnds path).length := by have := j.isLt; omega
  have hj0 : j.val < (orderedRow fd.pathEnds path).length := by omega
  have hSurvives := ((mem_orderedRow_iff fd.pathEnds path _).mp (List.getElem_mem hj0)).survives
  have hInc : Incident data (orderedRow fd.pathEnds path)[j.val]
      (rowVertex fd path (i.val + 1)) := by
    rw [hEq]
    exact walkVertex_succ_incident hj0
  rcases (incident_interior_iff fd path hi hSurvives).mp hInc with h | h
  · exact Fin.ext ((orderedRow_nodup fd.pathEnds path).getElem_inj_iff.mp h).symm
  · have hji : j.val = i.val + 1 := (orderedRow_nodup fd.pathEnds path).getElem_inj_iff.mp h
    have hSurvives' := ((mem_orderedRow_iff fd.pathEnds path _).mp (List.getElem_mem hj)).survives
    have hInc' : Incident data (orderedRow fd.pathEnds path)[j.val + 1]
        (rowVertex fd path (i.val + 1)) := by
      rw [hEq]
      exact rowVertex_incident fd path hj
    rcases (incident_interior_iff fd path hi hSurvives').mp hInc' with h | h <;>
      have hIndex := (orderedRow_nodup fd.pathEnds path).getElem_inj_iff.mp h <;> omega

theorem interior_ne_start (fd : FullDimensionalSourcePresentation data coordinate)
    (path : StablePath data) {i : ℕ}
    (hi : i + 1 < (orderedRow fd.pathEnds path).length) :
    rowVertex fd path (i + 1) ≠ rowVertex fd path 0 := by
  intro h
  have hVal := rowVertex_valency fd path hi
  rw [h] at hVal
  exact (startEdge_isPathEnd fd.pathEnds path).2 hVal

theorem interior_ne_finish (fd : FullDimensionalSourcePresentation data coordinate)
    (path : StablePath data) {i : ℕ}
    (hi : i + 1 < (orderedRow fd.pathEnds path).length) :
    rowVertex fd path (i + 1) ≠
      rowVertex fd path (orderedRow fd.pathEnds path).length := by
  intro hEq
  let last := (orderedRow fd.pathEnds path).length - 1
  have hLast : last < (orderedRow fd.pathEnds path).length := by dsimp [last]; omega
  have hLen : last + 1 = (orderedRow fd.pathEnds path).length := by dsimp [last]; omega
  have hSurvives := ((mem_orderedRow_iff fd.pathEnds path _).mp (List.getElem_mem hLast)).survives
  have hInc : Incident data (orderedRow fd.pathEnds path)[last]
      (rowVertex fd path (i + 1)) := by
    rw [hEq, ← hLen]
    exact walkVertex_succ_incident hLast
  rcases (incident_interior_iff fd path hi hSurvives).mp hInc with h | h
  · have := (orderedRow_nodup fd.pathEnds path).getElem_inj_iff.mp h
    omega
  · have hIndex := (orderedRow_nodup fd.pathEnds path).getElem_inj_iff.mp h
    have hNot : rowVertex fd path (last + 1) ≠ rowVertex fd path last :=
      walkVertex_ne_succ hLast
    rw [hLen, hIndex] at hNot
    exact hNot hEq.symm

/-- Two displayed occurrences incident at a divalent source vertex meet at
the far end of the earlier occurrence. The walk invariant rules out returning
to its entry end; no guessed path orientation is used. -/
theorem vertex_eq_next_of_incident
    (fd : FullDimensionalSourcePresentation data coordinate) (path : StablePath data)
    {i j : ℕ} (hi : i < (orderedRow fd.pathEnds path).length)
    (hj : j < (orderedRow fd.pathEnds path).length) (hij : i < j)
    {vertex : data.SourceVertex} (hValency : nonDanglingValency data vertex = 2)
    (hFirst : Incident data (orderedRow fd.pathEnds path)[i] vertex)
    (hSecond : Incident data (orderedRow fd.pathEnds path)[j] vertex) :
    vertex = rowVertex fd path (i + 1) := by
  have hInvariant := walk_invariant (orderedRow_nodup fd.pathEnds path)
    (fun edge hEdge ↦ ((mem_orderedRow_iff fd.pathEnds path edge).mp hEdge).survives)
    (orderedRow_chain fd.pathEnds path) (orderedRow_start fd path) i hi
  rcases eq_or_eq_otherEnd data hInvariant.1 hFirst with hSame | hNext
  · change vertex = rowVertex fd path i at hSame
    have hSecond' : Incident data (orderedRow fd.pathEnds path)[j]
        (rowVertex fd path i) := hSame ▸ hSecond
    have hValency' : nonDanglingValency data (rowVertex fd path i) = 2 := hSame ▸ hValency
    have hNe : (orderedRow fd.pathEnds path)[j] ≠ (orderedRow fd.pathEnds path)[i] := by
      intro h
      have := (orderedRow_nodup fd.pathEnds path).getElem_inj_iff.mp h
      omega
    obtain ⟨k, hk, hki, hEq⟩ := hInvariant.2 _
      (((mem_orderedRow_iff fd.pathEnds path _).mp (List.getElem_mem hj)).survives)
      hSecond' hNe hValency'
    have := (orderedRow_nodup fd.pathEnds path).getElem_inj_iff.mp hEq
    omega
  · exact hNext.trans (walkVertex_succ _ _ hi).symm

/-- Every actual surviving divalent vertex on the row is displayed. -/
theorem exists_interior_index
    (fd : FullDimensionalSourcePresentation data coordinate) (path : StablePath data)
    {vertex : data.SourceVertex} (hValency : nonDanglingValency data vertex = 2)
    {edge : data.SourceEdge} (hEdge : OnRow data path edge)
    (hIncident : Incident data edge vertex) :
    ∃ i : Fin ((orderedRow fd.pathEnds path).length - 1),
      rowVertex fd path (i.val + 1) = vertex := by
  obtain ⟨other, ⟨hNe, hSurvives, hOtherInc⟩, -⟩ :=
    exists_unique_other_of_nonDanglingValency_eq_two data hValency hEdge.survives hIncident
  have hOther := onRow_of_incident hValency hEdge hIncident hSurvives hOtherInc
  obtain ⟨i, hi, hI⟩ := List.mem_iff_getElem.mp ((mem_orderedRow_iff fd.pathEnds path edge).mpr hEdge)
  obtain ⟨j, hj, hJ⟩ := List.mem_iff_getElem.mp ((mem_orderedRow_iff fd.pathEnds path other).mpr hOther)
  have hIJ : i ≠ j := by
    intro h
    subst j
    exact hNe (hJ.symm.trans hI)
  have hIInc : Incident data (orderedRow fd.pathEnds path)[i] vertex := hI ▸ hIncident
  have hJInc : Incident data (orderedRow fd.pathEnds path)[j] vertex := hJ ▸ hOtherInc
  rcases lt_or_gt_of_ne hIJ with hij | hji
  · exact ⟨⟨i, by omega⟩,
      (vertex_eq_next_of_incident fd path hi hj hij hValency hIInc hJInc).symm⟩
  · exact ⟨⟨j, by omega⟩,
      (vertex_eq_next_of_incident fd path hj hi hji hValency hJInc hIInc).symm⟩

/-- The finite position index enumerates exactly the original source
vertices on this row's interior, without duplicates or missing vertices. -/
theorem mem_interior_range_iff
    (fd : FullDimensionalSourcePresentation data coordinate) (path : StablePath data)
    (vertex : data.SourceVertex) :
    (∃ i : Fin ((orderedRow fd.pathEnds path).length - 1),
      rowVertex fd path (i.val + 1) = vertex) ↔
    nonDanglingValency data vertex = 2 ∧
      ∃ edge, OnRow data path edge ∧ Incident data edge vertex := by
  constructor
  · rintro ⟨i, rfl⟩
    have hi : i.val + 1 < (orderedRow fd.pathEnds path).length := by have := i.isLt; omega
    refine ⟨rowVertex_valency fd path hi, (orderedRow fd.pathEnds path)[i.val + 1],
      (mem_orderedRow_iff fd.pathEnds path _).mp (List.getElem_mem hi),
      rowVertex_incident fd path hi⟩
  · rintro ⟨hValency, edge, hEdge, hIncident⟩
    exact exists_interior_index fd path hValency hEdge hIncident

/-- The enumeration remains injective after contracting actual pendant
branches: each pendant class contains at most one surviving source vertex. -/
theorem interior_retract_injective
    (fd : FullDimensionalSourcePresentation data coordinate) (path : StablePath data) :
    Function.Injective (fun i : Fin ((orderedRow fd.pathEnds path).length - 1) ↦
      retractVertex (rowVertex fd path (i.val + 1))) := by
  intro i j hEq
  apply interior_injective fd path
  apply surviving_vertex_unique (second := rowVertex fd path (j.val + 1)) ?_ ?_ hEq
  · have hi : i.val + 1 < (orderedRow fd.pathEnds path).length := by have := i.isLt; omega
    rw [rowVertex_valency fd path hi]
    omega
  · have hj : j.val + 1 < (orderedRow fd.pathEnds path).length := by have := j.isLt; omega
    rw [rowVertex_valency fd path hj]
    omega

/-- Distinct stable rows have disjoint interiors in the original source. -/
theorem row_eq_of_interior_eq
    (fd : FullDimensionalSourcePresentation data coordinate)
    (first second : StablePath data) {i j : ℕ}
    (hi : i + 1 < (orderedRow fd.pathEnds first).length)
    (hj : j + 1 < (orderedRow fd.pathEnds second).length)
    (hEq : rowVertex fd first (i + 1) = rowVertex fd second (j + 1)) : first = second := by
  have hFirst := (mem_orderedRow_iff fd.pathEnds first _).mp (List.getElem_mem hi)
  have hSecond := (mem_orderedRow_iff fd.pathEnds second _).mp (List.getElem_mem hj)
  have hIncident : Incident data (orderedRow fd.pathEnds second)[j + 1]
      (rowVertex fd first (i + 1)) := by
    rw [hEq]
    exact rowVertex_incident fd second hj
  have hBoth := onRow_of_incident (rowVertex_valency fd first hi) hFirst
    (rowVertex_incident fd first hi) hSecond.survives hIncident
  obtain ⟨hSurvivesA, hA⟩ := hBoth
  obtain ⟨hSurvivesB, hB⟩ := hSecond
  exact hA.symm.trans hB

/-- Expanding the collision coefficient yields a literal pushforward of the
original pullback fibre, counting each source vertex once. Both pendant
attachments and zero-length metric collisions are handled by the displayed
existence predicate; no coefficient identification is assumed. -/
theorem collisionCoefficient_eq_raw_fibre_sum
    (fd : FullDimensionalSourcePresentation data coordinate)
    (realization : data.NonnegativeIntegralRealization) (root : target.V)
    (path : StablePath data) (offset : ℕ) :
    collisionCoefficient fd realization root path offset =
      ∑ vertex : data.SourceVertex,
        if vertex.1.1 = root ∧
          ∃ i : Fin ((orderedRow fd.pathEnds path).length - 1),
            retractVertex vertex = retractVertex (rowVertex fd path (i.val + 1)) ∧
              integralPrefix fd realization path (i.val + 1) = offset then
          ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) else 0 := by
  classical
  let index := Fin ((orderedRow fd.pathEnds path).length - 1)
  have hExpand : collisionCoefficient fd realization root path offset =
      ∑ i : index, ∑ vertex : data.SourceVertex,
        if integralPrefix fd realization path (i.val + 1) = offset ∧
          retractVertex vertex = retractVertex (rowVertex fd path (i.val + 1)) ∧
          vertex.1.1 = root then
          ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) else 0 := by
    unfold collisionCoefficient
    apply Finset.sum_congr rfl
    intro i _
    by_cases hOffset : integralPrefix fd realization path (i.val + 1) = offset
    · simp only [hOffset, ite_true, retractedFibre, true_and]
    · simp only [hOffset, ite_false, false_and, Finset.sum_const_zero]
  rw [hExpand, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro vertex _
  by_cases hRoot : vertex.1.1 = root
  · by_cases hExists : ∃ i : index,
        retractVertex vertex = retractVertex (rowVertex fd path (i.val + 1)) ∧
          integralPrefix fd realization path (i.val + 1) = offset
    · obtain ⟨i, hClass, hOffset⟩ := hExists
      rw [ite_eq_left ⟨hRoot, i, hClass, hOffset⟩]
      rw [Finset.sum_eq_single i]
      · simp only [hOffset, hClass, hRoot, and_self, ite_true]
      · intro j _ hNe
        have hClassNe : retractVertex vertex ≠ retractVertex (rowVertex fd path (j.val + 1)) := by
          intro h
          exact hNe ((interior_retract_injective fd path) (h.symm.trans hClass))
        simp only [hClassNe, false_and, and_false, ite_false]
      · simp
    · rw [ite_eq_right (by simpa only [hRoot, true_and] using hExists)]
      apply Finset.sum_eq_zero
      intro i _
      split_ifs with h
      · exact False.elim (hExists ⟨i, h.2.1, h.1⟩)
      · rfl
  · simp only [hRoot, and_false, false_and, ite_false, Finset.sum_const_zero]

end DraismaVargas.Count.RowVertexEnumeration

