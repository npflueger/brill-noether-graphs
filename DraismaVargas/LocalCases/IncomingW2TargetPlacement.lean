import DraismaVargas.LocalCases.IncomingTargetExpansion

/-!
# Actual incoming placements at a two-star wall

The reconstructed expansion's side predicate is read from original unfolded
occurrences.  Uniqueness of the contracted edge makes its two endpoint stars
disjoint after deleting that occurrence.  Consequently a leaf at `a` forces
both wall occurrences right, a leaf at `b` forces both left, and two divalent
endpoints force opposite sides.  The source valency split
(`SecondEquation.valencySplit_of_twoStar`) supplies the three cases and their
changes; no further source partition classification is used.

`right_eq_table` and the leaf/singleton corollaries describe the exact predicate
on every retained occurrence.  This is the target-placement census, not a
normalization isomorphism to both fixed M11 target orientations.  In particular
the split candidate uses constant `true` away from the wall, whereas this actual
reconstruction uses `false` there; normalization must compare actual endpoints,
where off-wall predicate values have no effect, rather than claim equality of
those two Boolean functions.  Reversing the contracted endpoint orientation
is a separate step for the other leaf/singleton orientation.
-/

namespace DraismaVargas.LocalCases.IncomingW2TargetPlacement

open DraismaVargas.Infrastructure GraphContraction GluingContraction
open ContractionRamification W2R1Target

variable {target : CFGraph} {a b : target.V} {contracted : target.edges}

/-- The actual unfolded occurrence, not a chosen incidence count, controls
whether the retained occurrence moves to the fresh endpoint. -/
theorem right_eq_true_iff
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (edge : (contract target hab hOne).edges) :
    IncomingTargetExpansion.right hc hab hOne edge = true ↔
      unfoldEdge hc hab hOne edge ∈ GluingDatum.incidentEdges b := by
  simp only [IncomingTargetExpansion.right, decide_eq_true_eq, mem_incidentEdges_iff]

/-- A wall occurrence stays at `a` exactly when its unfolded occurrence meets
`a`; it cannot also meet `b`, since it is not the contracted occurrence. -/
theorem right_eq_false_iff_of_incident
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (edge : (contract target hab hOne).edges)
    (hIncident : edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩) :
    IncomingTargetExpansion.right hc hab hOne edge = false ↔
      unfoldEdge hc hab hOne edge ∈ GluingDatum.incidentEdges a := by
  have hUnion := unfoldEdge_mem_incidentEdges_union hc hab hOne hIncident
  have hNotBoth : ¬(unfoldEdge hc hab hOne edge ∈ GluingDatum.incidentEdges a ∧
      unfoldEdge hc hab hOne edge ∈ GluingDatum.incidentEdges b) := by
    intro hBoth
    have hMem := Finset.mem_inter.mpr hBoth
    rw [incidentEdges_inter hc hab hOne, Finset.mem_singleton] at hMem
    exact unfoldEdge_ne_contracted hc hab hOne edge hMem
  simp only [Bool.eq_false_iff, ne_eq, right_eq_true_iff hc hab hOne edge]
  exact ⟨fun h => (Finset.mem_union.mp hUnion).resolve_right h,
    fun h h' => hNotBoth ⟨h, h'⟩⟩

/-- The actual reconstruction never marks an off-wall occurrence as right. -/
theorem right_eq_false_of_not_incident
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (edge : (contract target hab hOne).edges)
    (hIncident : edge ∉ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩) :
    IncomingTargetExpansion.right hc hab hOne edge = false := by
  simp only [Bool.eq_false_iff, ne_eq, right_eq_true_iff hc hab hOne edge]
  intro hRight
  apply hIncident
  have hFold := foldEdge_mem_incidentEdges_merge hc hab hOne
    (unfoldEdge_ne_contracted hc hab hOne edge) (Finset.mem_union_right _ hRight)
  rwa [foldEdge_unfoldEdge] at hFold

private theorem eq_of_mem_card_one {α : Type*} [DecidableEq α]
    {set : Finset α} {first second : α} (hCard : set.card = 1)
    (hFirst : first ∈ set) (hSecond : second ∈ set) : first = second := by
  obtain ⟨point, hPoint⟩ := Finset.card_eq_one.mp hCard
  rw [hPoint, Finset.mem_singleton] at hFirst hSecond
  exact hFirst.trans hSecond.symm

/-- A leaf at `a` sends both named retained occurrences to `b`. -/
theorem right_star_of_leaf_left
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1) (label : Fin 2) :
    IncomingTargetExpansion.right hc hab hOne (star.edge label) = true := by
  classical
  rw [← Bool.not_eq_false]
  intro hFalse
  have hLeft := (right_eq_false_iff_of_incident hc hab hOne _
    (star.edge_mem_incidentEdges label)).mp hFalse
  exact unfoldEdge_ne_contracted hc hab hOne _
    (eq_of_mem_card_one hLeaf hLeft (contracted_mem_incidentEdges_left hc))

/-- A leaf at `b` leaves both named retained occurrences at `a`. -/
theorem right_star_of_leaf_right
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
    (hLeaf : (GluingDatum.incidentEdges b).card = 1) (label : Fin 2) :
    IncomingTargetExpansion.right hc hab hOne (star.edge label) = false := by
  classical
  simp only [Bool.eq_false_iff, ne_eq, right_eq_true_iff hc hab hOne (star.edge label)]
  intro hRight
  exact unfoldEdge_ne_contracted hc hab hOne _
    (eq_of_mem_card_one hLeaf hRight (contracted_mem_incidentEdges_right hc))

private theorem not_both_mem_of_card_two {α : Type*} [DecidableEq α]
    {set : Finset α} {first second third : α}
    (hCard : set.card = 2) (hFirst : first ∈ set)
    (h₁₂ : first ≠ second) (h₁₃ : first ≠ third) (h₂₃ : second ≠ third) :
    ¬(second ∈ set ∧ third ∈ set) := by
  rintro ⟨hSecond, hThird⟩
  have hSub : ({first, second, third} : Finset α) ⊆ set := by
    intro point hPoint
    simp only [Finset.mem_insert, Finset.mem_singleton] at hPoint
    rcases hPoint with rfl | rfl | rfl <;> assumption
  have hLe := Finset.card_le_card hSub
  simp [h₁₂, h₁₃, h₂₃, hCard] at hLe

/-- Three distinct occurrences cannot meet a divalent endpoint.  Applied to
the contracted occurrence and both unfolded labels, this forces opposite sides. -/
theorem right_star_ne_of_divalent
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2) :
    IncomingTargetExpansion.right hc hab hOne (star.edge 0) ≠
      IncomingTargetExpansion.right hc hab hOne (star.edge 1) := by
  classical
  have hZero := unfoldEdge_ne_contracted hc hab hOne (star.edge 0)
  have hOneEdge := unfoldEdge_ne_contracted hc hab hOne (star.edge 1)
  have hApart : unfoldEdge hc hab hOne (star.edge 0) ≠
      unfoldEdge hc hab hOne (star.edge 1) := by
    intro h
    have hSub : (foldEdgeEquiv hc hab hOne).symm (star.edge 0) =
        (foldEdgeEquiv hc hab hOne).symm (star.edge 1) := Subtype.ext h
    have := star.edge_injective ((foldEdgeEquiv hc hab hOne).symm.injective hSub)
    exact (by decide : (0 : Fin 2) ≠ 1) this
  intro hEq
  cases hValue : IncomingTargetExpansion.right hc hab hOne (star.edge 0) with
  | false =>
    exact not_both_mem_of_card_two hLeft (contracted_mem_incidentEdges_left hc)
      hZero.symm hOneEdge.symm hApart
      ⟨(right_eq_false_iff_of_incident hc hab hOne _ (star.edge_mem_incidentEdges 0)).mp hValue,
        (right_eq_false_iff_of_incident hc hab hOne _ (star.edge_mem_incidentEdges 1)).mp
          (hEq.symm.trans hValue)⟩
  | true =>
    exact not_both_mem_of_card_two hRight (contracted_mem_incidentEdges_right hc)
      hZero.symm hOneEdge.symm hApart
      ⟨(right_eq_true_iff hc hab hOne _).mp hValue,
        (right_eq_true_iff hc hab hOne _).mp (hEq.symm.trans hValue)⟩

/-- The two-star labels are the complete support of the reconstructed side
predicate, including occurrences away from the contracted wall. -/
theorem right_eq_table
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
    (edge : (contract target hab hOne).edges) :
    IncomingTargetExpansion.right hc hab hOne edge =
      if edge = star.edge 0 then IncomingTargetExpansion.right hc hab hOne (star.edge 0)
      else if edge = star.edge 1 then IncomingTargetExpansion.right hc hab hOne (star.edge 1)
      else false := by
  classical
  by_cases hZero : edge = star.edge 0
  · simp only [hZero, ↓reduceIte]
  by_cases hOneEdge : edge = star.edge 1
  · rw [if_neg hZero, if_pos hOneEdge, hOneEdge]
  rw [if_neg hZero, if_neg hOneEdge]
  apply right_eq_false_of_not_incident hc hab hOne
  intro hAt
  obtain ⟨label, hLabel⟩ := star.label.surjective ⟨edge, hAt⟩
  have hEdge : star.edge label = edge := congrArg Subtype.val hLabel
  fin_cases label
  · exact hZero hEdge.symm
  · exact hOneEdge hEdge.symm

/-- Incoming change-minimality selects exactly the two leaf placements or
the opposite-sided divalent placement.  The valency arithmetic is consumed
from `SecondEquation.valencySplit_of_twoStar`, not assumed as a classification. -/
theorem placement_of_twoStar {degree : ℕ} (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (hValid : data.Valid)
    (hMinimal : data.ChangeMinimal)
    (star : TwoStar (contract target hab hOne) ⟨a, hab⟩) :
    ((GluingDatum.incidentEdges a).card = 1 ∧ (GluingDatum.incidentEdges b).card = 3 ∧
        data.targetChange a = 2 ∧ data.targetChange b = 0 ∧
        IncomingTargetExpansion.right hc hab hOne (star.edge 0) = true ∧
        IncomingTargetExpansion.right hc hab hOne (star.edge 1) = true) ∨
      ((GluingDatum.incidentEdges a).card = 3 ∧ (GluingDatum.incidentEdges b).card = 1 ∧
        data.targetChange a = 0 ∧ data.targetChange b = 2 ∧
        IncomingTargetExpansion.right hc hab hOne (star.edge 0) = false ∧
        IncomingTargetExpansion.right hc hab hOne (star.edge 1) = false) ∨
      ((GluingDatum.incidentEdges a).card = 2 ∧ (GluingDatum.incidentEdges b).card = 2 ∧
        data.targetChange a = 1 ∧ data.targetChange b = 1 ∧
        IncomingTargetExpansion.right hc hab hOne (star.edge 0) ≠
          IncomingTargetExpansion.right hc hab hOne (star.edge 1)) := by
  rcases SecondEquation.valencySplit_of_twoStar data hc hab hOne hValid hMinimal star with
    ⟨hLeft, hRight, hChangeLeft, hChangeRight⟩ |
    ⟨hLeft, hRight, hChangeLeft, hChangeRight⟩ |
    ⟨hLeft, hRight, hChangeLeft, hChangeRight⟩
  · exact Or.inr (Or.inr ⟨hLeft, hRight, hChangeLeft, hChangeRight,
      right_star_ne_of_divalent hc hab hOne star hLeft hRight⟩)
  · exact Or.inl ⟨hLeft, hRight, hChangeLeft, hChangeRight,
      right_star_of_leaf_left hc hab hOne star hLeft 0,
      right_star_of_leaf_left hc hab hOne star hLeft 1⟩
  · exact Or.inr (Or.inl ⟨hLeft, hRight, hChangeLeft, hChangeRight,
      right_star_of_leaf_right hc hab hOne star hRight 0,
      right_star_of_leaf_right hc hab hOne star hRight 1⟩)

/-- In the divalent case the exact global side predicate is one of the two
literal singleton predicates.  No arbitrary occurrence bijection is chosen. -/
theorem right_eq_singleton_of_divalent
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2) :
    ∃ label : Fin 2, IncomingTargetExpansion.right hc hab hOne =
      fun edge => decide (edge = star.edge label) := by
  classical
  have hApart := right_star_ne_of_divalent hc hab hOne star hLeft hRight
  cases hZero : IncomingTargetExpansion.right hc hab hOne (star.edge 0) with
  | false =>
    have hOneEdge : IncomingTargetExpansion.right hc hab hOne (star.edge 1) = true := by
      cases hValue : IncomingTargetExpansion.right hc hab hOne (star.edge 1)
      · exact False.elim (hApart (hZero.trans hValue.symm))
      · rfl
    refine ⟨1, funext fun edge => ?_⟩
    rw [right_eq_table hc hab hOne star edge, hZero, hOneEdge]
    by_cases hEdge : edge = star.edge 0
    · have hNotOne : edge ≠ star.edge 1 := by
        rw [hEdge]
        exact star.edge_injective.ne (by decide)
      rw [if_pos hEdge, decide_eq_false hNotOne]
    · simp [hEdge]
  | true =>
    have hOneEdge : IncomingTargetExpansion.right hc hab hOne (star.edge 1) = false := by
      cases hValue : IncomingTargetExpansion.right hc hab hOne (star.edge 1)
      · rfl
      · exact False.elim (hApart (hZero.trans hValue.symm))
    refine ⟨0, funext fun edge => ?_⟩
    rw [right_eq_table hc hab hOne star edge, hZero, hOneEdge]
    simp

/-- Exact global predicate when the retained endpoint is the leaf. -/
theorem right_eq_wall_predicate_of_leaf_left
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1) :
    IncomingTargetExpansion.right hc hab hOne =
      fun edge => decide (edge = star.edge 0 ∨ edge = star.edge 1) := by
  classical
  funext edge
  rw [right_eq_table hc hab hOne star edge,
    right_star_of_leaf_left hc hab hOne star hLeaf 0,
    right_star_of_leaf_left hc hab hOne star hLeaf 1]
  by_cases hZero : edge = star.edge 0 <;> simp [hZero]

/-- Exact global predicate when the restored endpoint is the leaf. -/
theorem right_eq_false_of_leaf_right
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
    (hLeaf : (GluingDatum.incidentEdges b).card = 1) :
    IncomingTargetExpansion.right hc hab hOne = fun _ => false := by
  funext edge
  rw [right_eq_table hc hab hOne star edge,
    right_star_of_leaf_right hc hab hOne star hLeaf 0,
    right_star_of_leaf_right hc hab hOne star hLeaf 1]
  simp

end DraismaVargas.LocalCases.IncomingW2TargetPlacement
