module

public import DraismaVargas.LocalCases.W3R1SourceProfile
public import DraismaVargas.LocalCases.FullDimensionalSource

@[expose] public section

/-!
# Local index and no-return formulas at a divalent surviving source vertex

Source: Draisma--Vargas Part I, `lem-noreturn-rphi1` and the cases (r0-nd2)
and (r1-nd2) of the local properties, as used in Base II of Case {w2}. These
statements concern
the actual surviving pair at an arbitrary source vertex. They do not require
a wall input, target star, stable-row labelling, or global pass-once theorem.

The non-dangling ramification formula gives `i+j=2m-r`. For `r≤1`, putting
both survivors in one target direction would give `i+j≤m`, contradicting
positive indices. At `r=0` both indices equal `m`; at `r=1` they are `m-1,m`.
-/

namespace DraismaVargas.LocalCases.DivalentSourceLocal

open DraismaVargas.Infrastructure
open W4StableSource StableLocalProperties W3R1SourceProfile FullDimensionalSource

variable {target : CFGraph} {degree : ℕ}

noncomputable local instance (data : GluingDatum target degree) (vertex : data.SourceVertex) :
    DecidableEq (IncidentSourceEdge data vertex) := Classical.decEq _

/-- Any distinct surviving pair exhausts the incidences at an nd2 vertex. -/
theorem survivingIncidences_eq_pair (data : GluingDatum target degree)
    (vertex : data.SourceVertex) (hNd : nonDanglingValency data vertex = 2)
    (first second : IncidentSourceEdge data vertex) (hNe : first ≠ second)
    (hFirst : ¬ IsDangling data first.1) (hSecond : ¬ IsDangling data second.1) :
    (Finset.univ.filter fun edge : IncidentSourceEdge data vertex ↦ ¬ IsDangling data edge.1) =
      {first, second} := by
  classical
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro edge hEdge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
    rcases hEdge with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFirst⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSecond⟩
  · rw [card_filter_not_isDangling_eq_nonDanglingValency, hNd, Finset.card_pair hNe]

/-- The source's nd2 formula, on its two literal surviving occurrences. -/
theorem sum_indices (data : GluingDatum target degree) (hNoGlue : DanglingEdgeNoGlue data)
    (vertex : data.SourceVertex) (hNd : nonDanglingValency data vertex = 2)
    (first second : IncidentSourceEdge data vertex) (hNe : first ≠ second)
    (hFirst : ¬ IsDangling data first.1) (hSecond : ¬ IsDangling data second.1) :
    (data.sourceEdgeIndex first.1 : ℤ) + data.sourceEdgeIndex second.1 =
      2 * ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) -
        data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ := by
  have hFormula := localRamification_eq_nonDangling_form data hNoGlue vertex
  rw [survivingIncidences_eq_pair data vertex hNd first second hNe hFirst hSecond,
    Finset.sum_pair hNe, hNd] at hFormula
  omega

/-- Ramification at most one forbids a return over a single target direction
at an nd2 source vertex. This is directional harmonicity, not pass-once. -/
theorem targets_ne_of_ramification_le_one
    (data : GluingDatum target degree) (hNoGlue : DanglingEdgeNoGlue data)
    (vertex : data.SourceVertex) (hNd : nonDanglingValency data vertex = 2)
    (hR : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ ≤ 1)
    (first second : IncidentSourceEdge data vertex) (hNe : first ≠ second)
    (hFirst : ¬ IsDangling data first.1) (hSecond : ¬ IsDangling data second.1) :
    first.1.1.1 ≠ second.1.1.1 := by
  classical
  intro hSame
  have hSum := sum_indices data hNoGlue vertex hNd first second hNe hFirst hSecond
  have hIncident := (incident_iff_target_mem_and_rel data first.1 vertex).mp first.2 |>.1
  have hBound := sum_index_le_of_same_target data vertex {first, second}
    first.1.1.1 hIncident (by
      intro edge hEdge
      rcases Finset.mem_insert.mp hEdge with rfl | hSecond
      · rfl
      · exact (Finset.mem_singleton.mp hSecond) ▸ hSame.symm)
  rw [Finset.sum_pair hNe] at hBound
  have hFirstPos := sourceEdgeIndex_pos data first.1
  have hSecondPos := sourceEdgeIndex_pos data second.1
  omega

/-- Equivalently, a literal target occurrence carries at most one surviving
incidence at an nd2 source vertex of ramification at most one. -/
theorem sourceEdge_eq_of_same_target
    (data : GluingDatum target degree) (hNoGlue : DanglingEdgeNoGlue data)
    (vertex : data.SourceVertex) (hNd : nonDanglingValency data vertex = 2)
    (hR : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ ≤ 1)
    (first second : data.SourceEdge)
    (hFirst : ¬ IsDangling data first) (hSecond : ¬ IsDangling data second)
    (hFirstInc : Incident data first vertex) (hSecondInc : Incident data second vertex)
    (hTarget : first.1.1 = second.1.1) : first = second := by
  by_contra hNe
  exact targets_ne_of_ramification_le_one data hNoGlue vertex hNd hR
    ⟨first, hFirstInc⟩ ⟨second, hSecondInc⟩
    (fun h ↦ hNe (congrArg Subtype.val h)) hFirst hSecond hTarget

/-- At a divalent target, the distinct directions of the surviving pair
exhaust its incident target occurrences. -/
theorem exists_surviving_incidence_over_target
    (data : GluingDatum target degree) (hNoGlue : DanglingEdgeNoGlue data)
    (vertex : data.SourceVertex) (hNd : nonDanglingValency data vertex = 2)
    (hR : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ ≤ 1)
    (hDivalent : (GluingDatum.incidentEdges vertex.1.1).card = 2)
    (targetEdge : target.edges) (hIncident : targetEdge ∈ GluingDatum.incidentEdges vertex.1.1) :
    ∃ edge : data.SourceEdge, ¬ IsDangling data edge ∧
      edge.1.1 = targetEdge ∧ Incident data edge vertex := by
  classical
  have hCard : (Finset.univ.filter fun edge : IncidentSourceEdge data vertex ↦
      ¬ IsDangling data edge.1).card = 2 :=
    (card_filter_not_isDangling_eq_nonDanglingValency data vertex).trans hNd
  obtain ⟨first, second, hNe, hPair⟩ := Finset.card_eq_two.mp hCard
  have hFirst : ¬ IsDangling data first.1 := by
    have hMem := hPair.symm ▸ Finset.mem_insert_self first {second}
    exact (Finset.mem_filter.mp hMem).2
  have hSecond : ¬ IsDangling data second.1 := by
    have hMem := hPair.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self second)
    exact (Finset.mem_filter.mp hMem).2
  have hTargets := targets_ne_of_ramification_le_one data hNoGlue vertex hNd hR
    first second hNe hFirst hSecond
  have hDirections : GluingDatum.incidentEdges vertex.1.1 = {first.1.1.1, second.1.1.1} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro edge hEdge
      simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
      rcases hEdge with rfl | rfl
      · exact (incident_iff_target_mem_and_rel data first.1 vertex).mp first.2 |>.1
      · exact (incident_iff_target_mem_and_rel data second.1 vertex).mp second.2 |>.1
    · rw [hDivalent, Finset.card_pair hTargets]
  rw [hDirections, Finset.mem_insert, Finset.mem_singleton] at hIncident
  exact hIncident.elim (fun h ↦ ⟨first.1, hFirst, h.symm, first.2⟩)
    (fun h ↦ ⟨second.1, hSecond, h.symm, second.2⟩)

/-- The two survivors of an unramified nd2 source vertex have equal indices. -/
theorem indices_eq_of_ramification_zero
    (data : GluingDatum target degree) (hNoGlue : DanglingEdgeNoGlue data)
    (vertex : data.SourceVertex) (hNd : nonDanglingValency data vertex = 2)
    (hR : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 0)
    (first second : IncidentSourceEdge data vertex) (hNe : first ≠ second)
    (hFirst : ¬ IsDangling data first.1) (hSecond : ¬ IsDangling data second.1) :
    data.sourceEdgeIndex first.1 = (data.vertexPartition vertex.1.1).blockCard vertex.1.2 ∧
      data.sourceEdgeIndex second.1 = (data.vertexPartition vertex.1.1).blockCard vertex.1.2 := by
  have hSum := sum_indices data hNoGlue vertex hNd first second hNe hFirst hSecond
  have hFirstLe := sourceEdgeIndex_le_blockCard data vertex first
  have hSecondLe := sourceEdgeIndex_le_blockCard data vertex second
  rw [hR] at hSum
  omega

/-- At ramification one the actual surviving indices are precisely `m-1,m`,
with no ordering assumed in the input. -/
theorem indices_of_ramification_one
    (data : GluingDatum target degree) (hNoGlue : DanglingEdgeNoGlue data)
    (vertex : data.SourceVertex) (hNd : nonDanglingValency data vertex = 2)
    (hR : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 1)
    (first second : IncidentSourceEdge data vertex) (hNe : first ≠ second)
    (hFirst : ¬ IsDangling data first.1) (hSecond : ¬ IsDangling data second.1) :
    (data.sourceEdgeIndex first.1 + 1 = data.sourceEdgeIndex second.1 ∧
      data.sourceEdgeIndex second.1 = (data.vertexPartition vertex.1.1).blockCard vertex.1.2) ∨
    (data.sourceEdgeIndex second.1 + 1 = data.sourceEdgeIndex first.1 ∧
      data.sourceEdgeIndex first.1 = (data.vertexPartition vertex.1.1).blockCard vertex.1.2) := by
  have hSum := sum_indices data hNoGlue vertex hNd first second hNe hFirst hSecond
  have hFirstLe := sourceEdgeIndex_le_blockCard data vertex first
  have hSecondLe := sourceEdgeIndex_le_blockCard data vertex second
  rw [hR] at hSum
  omega

/-- With ramification at most one, the two surviving indices differ by at
most one. This form directly pins the internal P index between `k` and `k+2`. -/
theorem indices_close_of_ramification_le_one
    (data : GluingDatum target degree) (hNoGlue : DanglingEdgeNoGlue data)
    (vertex : data.SourceVertex) (hNd : nonDanglingValency data vertex = 2)
    (hR : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ ≤ 1)
    (first second : IncidentSourceEdge data vertex) (hNe : first ≠ second)
    (hFirst : ¬ IsDangling data first.1) (hSecond : ¬ IsDangling data second.1) :
    data.sourceEdgeIndex first.1 ≤ data.sourceEdgeIndex second.1 + 1 ∧
      data.sourceEdgeIndex second.1 ≤ data.sourceEdgeIndex first.1 + 1 := by
  have hSum := sum_indices data hNoGlue vertex hNd first second hNe hFirst hSecond
  have hFirstLe := sourceEdgeIndex_le_blockCard data vertex first
  have hSecondLe := sourceEdgeIndex_le_blockCard data vertex second
  omega

/-- At a nonleaf change-minimal target vertex every source block has
ramification at most one, since its nonnegative contribution is bounded by
the total change `3-val`. -/
theorem localRamification_le_one_of_nonleaf
    (data : GluingDatum target degree) (hValid : data.Valid)
    (vertex : data.SourceVertex) (hMinimal : data.ChangeMinimalAt vertex.1.1)
    (hNonleaf : 2 ≤ (GluingDatum.incidentEdges vertex.1.1).card) :
    data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ ≤ 1 := by
  classical
  have hLe := Finset.single_le_sum
    (f := data.localRamification vertex.1.1)
    (fun block _ ↦ data.localRamification_nonneg vertex.1.1 (hValid.2 _) block)
    (Finset.mem_univ (⟨vertex.1.2, vertex.2⟩ : (data.vertexPartition vertex.1.1).Blocks))
  change _ ≤ data.targetChange vertex.1.1 at hLe
  change data.targetChange vertex.1.1 + ((GluingDatum.incidentEdges vertex.1.1).card : ℤ) - 3 = 0
    at hMinimal
  omega

end DraismaVargas.LocalCases.DivalentSourceLocal
