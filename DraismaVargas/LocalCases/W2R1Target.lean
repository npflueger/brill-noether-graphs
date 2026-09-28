import DraismaVargas.Infrastructure.TargetExpansion
import Mathlib.Tactic

/-!
# The unique target expansion at a divalent wall

Source Case `w2-r1` splits a divalent target wall into two divalent endpoints.
Up to exchanging those endpoints there is only one target expansion: one old
edge occurrence stays at the retained endpoint and the other moves to the
fresh endpoint.  This module labels the two actual occurrences and constructs
the assignment and canonical singleton occurrence lists used by global
assembly.
-/

namespace DraismaVargas.LocalCases.W2R1Target

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion

variable {target : CFGraph} {wall : target.V}

/-- An occurrence labelling of the two target edges at the divalent wall. -/
structure TwoStar (target : CFGraph) (wall : target.V) where
  label : Fin 2 ≃ {edge : target.edges // edge ∈ GluingDatum.incidentEdges wall}

/-- Canonically label the incident occurrences of any divalent target vertex. -/
noncomputable def TwoStar.of_card
    (hcard : (GluingDatum.incidentEdges wall).card = 2) :
    TwoStar target wall where
  label := (Fintype.equivFinOfCardEq (by simpa using hcard)).symm

namespace TwoStar

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-- The actual target-edge occurrence carrying a label. -/
def edge (star : TwoStar target wall) (label : Fin 2) : target.edges :=
  (star.label label).1

theorem edge_injective (star : TwoStar target wall) :
    Function.Injective star.edge := by
  intro first second heq
  apply star.label.injective
  exact Subtype.ext heq

@[simp]
theorem edge_mem_incidentEdges (star : TwoStar target wall) (label : Fin 2) :
    star.edge label ∈ GluingDatum.incidentEdges wall :=
  (star.label label).2

/-- Each labelled occurrence partition refines the central wall partition. -/
theorem edgePartition_refines_wall (star : TwoStar target wall)
    (data : GluingDatum target d) (label : Fin 2) :
    (data.edgePartition (star.edge label)).Refines
      (data.vertexPartition wall) := by
  have hIncident := star.edge_mem_incidentEdges label
  simp only [GluingDatum.incidentEdges, Finset.mem_filter,
    Finset.mem_univ, true_and] at hIncident
  rcases hIncident with hLeft | hRight
  · simpa [hLeft] using data.refines_left (star.edge label)
  · simpa [hRight] using data.refines_right (star.edge label)

/-- The fresh endpoint receives label `1`. -/
noncomputable def right (star : TwoStar target wall)
    (targetEdge : target.edges) : Bool :=
  decide (targetEdge = star.edge 1)

/-- The singleton occurrence set moved to the fresh endpoint. -/
noncomputable def rightSet (star : TwoStar target wall) : Finset target.edges :=
  {star.edge 1}

@[simp]
theorem card_rightSet (star : TwoStar target wall) :
    star.rightSet.card = 1 := by
  simp [rightSet]

theorem rightSet_subset_incidentEdges (star : TwoStar target wall) :
    star.rightSet ⊆ GluingDatum.incidentEdges wall := by
  intro edge hEdge
  simp only [rightSet, Finset.mem_singleton] at hEdge
  subst edge
  exact star.edge_mem_incidentEdges 1

@[simp]
theorem right_edge_zero (star : TwoStar target wall) :
    star.right (star.edge 0) = false := by
  simp only [right]
  exact (Bool.decide_false (p := star.edge 0 = star.edge 1))
    (star.edge_injective.ne (show (0 : Fin 2) ≠ 1 by decide))

@[simp]
theorem right_edge_one (star : TwoStar target wall) :
    star.right (star.edge 1) = true := by
  simp [right]

/-- The fresh side contains exactly label `1`. -/
theorem wallEdgesAssigned_true (star : TwoStar target wall) :
    wallEdgesAssigned target wall star.right true = star.rightSet := by
  ext targetEdge
  constructor
  · intro h
    have hAssigned :=
      (mem_wallEdgesAssigned target wall star.right true targetEdge).mp h
    exact Finset.mem_singleton.mpr
      (of_decide_eq_true hAssigned.2)
  · intro h
    have hEdge := Finset.mem_singleton.mp h
    subst targetEdge
    apply (mem_wallEdgesAssigned target wall star.right true _).mpr
    exact ⟨by simpa [GluingDatum.incidentEdges] using
      star.edge_mem_incidentEdges 1, star.right_edge_one⟩

/-- The retained side is the other incident occurrence. -/
theorem wallEdgesAssigned_false (star : TwoStar target wall) :
    wallEdgesAssigned target wall star.right false =
      GluingDatum.incidentEdges wall \ star.rightSet := by
  ext targetEdge
  simp [mem_wallEdgesAssigned, GluingDatum.incidentEdges, right, rightSet]

@[simp]
theorem card_incidentEdges (star : TwoStar target wall) :
    (GluingDatum.incidentEdges wall).card = 2 := by
  rw [← Fintype.card_coe]
  simpa using (Fintype.card_congr star.label).symm

@[simp]
theorem card_wallEdgesAssigned_true (star : TwoStar target wall) :
    (wallEdgesAssigned target wall star.right true).card = 1 := by
  rw [star.wallEdgesAssigned_true]
  exact star.card_rightSet

@[simp]
theorem card_wallEdgesAssigned_false (star : TwoStar target wall) :
    (wallEdgesAssigned target wall star.right false).card = 1 := by
  rw [star.wallEdgesAssigned_false,
    Finset.card_sdiff_of_subset star.rightSet_subset_incidentEdges,
    star.card_incidentEdges, star.card_rightSet]

/-- The canonical old-edge list at the retained endpoint. -/
noncomputable def leftEdges (star : TwoStar target wall) : List target.edges :=
  (GluingDatum.incidentEdges wall \ star.rightSet).toList

/-- The canonical old-edge list at the fresh endpoint. -/
noncomputable def rightEdges (star : TwoStar target wall) : List target.edges :=
  star.rightSet.toList

theorem leftEdges_eq (star : TwoStar target wall) :
    (star.leftEdges : Multiset target.edges) =
      (wallEdgesAssigned target wall star.right false).val := by
  rw [leftEdges, Finset.coe_toList, star.wallEdgesAssigned_false]

theorem rightEdges_eq (star : TwoStar target wall) :
    (star.rightEdges : Multiset target.edges) =
      (wallEdgesAssigned target wall star.right true).val := by
  rw [rightEdges, Finset.coe_toList, star.wallEdgesAssigned_true]

@[simp]
theorem length_leftEdges (star : TwoStar target wall) :
    star.leftEdges.length = 1 := by
  rw [leftEdges, Finset.length_toList,
    Finset.card_sdiff_of_subset star.rightSet_subset_incidentEdges,
    star.card_incidentEdges, star.card_rightSet]

@[simp]
theorem length_rightEdges (star : TwoStar target wall) :
    star.rightEdges.length = 1 := by
  rw [rightEdges, Finset.length_toList, star.card_rightSet]

end TwoStar

end DraismaVargas.LocalCases.W2R1Target
