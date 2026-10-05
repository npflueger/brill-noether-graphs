module

public import DraismaVargasCount.PendantBranch
public import DraismaVargas.LocalCases.W2R1SourceProfile

@[expose] public section

namespace DraismaVargas.Count.PendantFibre

open DraismaVargas.Infrastructure GluingDatum
open DraismaVargas.LocalCases
open W4StableSource StableLocalProperties FullDimensionalSource
open DanglingSideStructure DanglingDescent

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The actual dangling source occurrences at a vertex above one target occurrence. -/
noncomputable def danglingDirection (vertex : data.SourceVertex)
    (direction : target.edges) : Finset (IncidentSourceEdge data vertex) :=
  Finset.univ.filter fun edge ↦ edge.1.1.1 = direction ∧ IsDangling data edge.1

/-- Directional harmonicity splits into the number of unit dangling occurrences
and the indices of the surviving occurrences. -/
theorem danglingDirection_card_add_surviving
    (hNoGlue : DanglingEdgeNoGlue data) (vertex : data.SourceVertex)
    (direction : target.edges) (hDirection : direction ∈ incidentEdges vertex.1.1) :
    ((danglingDirection vertex direction).card : ℤ) +
      (∑ edge : IncidentSourceEdge data vertex,
        if edge.1.1.1 = direction ∧ ¬ IsDangling data edge.1 then
          (data.sourceEdgeIndex edge.1 : ℤ) else 0) =
      ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) := by
  classical
  rw [← W2R1SourceProfile.sum_sourceEdgeIndex_target data vertex direction hDirection]
  have hCard : ((danglingDirection vertex direction).card : ℤ) =
      ∑ edge : IncidentSourceEdge data vertex,
        if edge.1.1.1 = direction ∧ IsDangling data edge.1 then (1 : ℤ) else 0 := by
    simp [danglingDirection, Finset.sum_boole]
  rw [hCard, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro edge _
  by_cases hTarget : edge.1.1.1 = direction
  · by_cases hDangling : IsDangling data edge.1
    · simp [hTarget, hDangling, hNoGlue edge.1 hDangling]
    · simp [hTarget, hDangling]
  · simp [hTarget]

/-- On the interior of an actual stable row, the two named surviving
occurrences account for the entire non-dangling part of directional harmonicity. -/
theorem danglingDirection_card_of_two_survivors
    (hNoGlue : DanglingEdgeNoGlue data) (vertex : data.SourceVertex)
    (hValency : nonDanglingValency data vertex = 2)
    (first second : IncidentSourceEdge data vertex)
    (hFirst : ¬ IsDangling data first.1) (hSecond : ¬ IsDangling data second.1)
    (hNe : first.1 ≠ second.1)
    (direction : target.edges) (hDirection : direction ∈ incidentEdges vertex.1.1) :
    ((danglingDirection vertex direction).card : ℤ) =
      ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) -
        (if first.1.1.1 = direction then (data.sourceEdgeIndex first.1 : ℤ) else 0) -
        (if second.1.1.1 = direction then (data.sourceEdgeIndex second.1 : ℤ) else 0) := by
  classical
  have hEq : (∑ edge : IncidentSourceEdge data vertex,
        if edge.1.1.1 = direction ∧ ¬ IsDangling data edge.1 then
          (data.sourceEdgeIndex edge.1 : ℤ) else 0) =
        (if first.1.1.1 = direction then (data.sourceEdgeIndex first.1 : ℤ) else 0) +
        (if second.1.1.1 = direction then (data.sourceEdgeIndex second.1 : ℤ) else 0) := by
    have hSubtypeNe : first ≠ second := fun h ↦ hNe (congrArg Subtype.val h)
    rw [← Finset.sum_subset (Finset.subset_univ ({first, second} :
      Finset (IncidentSourceEdge data vertex)))]
    · simp [Finset.sum_pair hSubtypeNe, hFirst, hSecond]
    · intro edge _ hOutside
      have hDangling : IsDangling data edge.1 := by
        by_contra hSurvives
        rcases IndexPattern.eq_or_eq_of_nonDanglingValency_two hValency hFirst first.2
          hSecond second.2 hNe hSurvives edge.2 with h | h
        · exact hOutside (Finset.mem_insert.mpr (Or.inl (Subtype.ext h)))
        · exact hOutside (Finset.mem_insert.mpr
            (Or.inr (Finset.mem_singleton.mpr (Subtype.ext h))))
      simp [hDangling]
  have hSum := danglingDirection_card_add_surviving hNoGlue vertex direction hDirection
  rw [hEq] at hSum
  omega

end DraismaVargas.Count.PendantFibre
