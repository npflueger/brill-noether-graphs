import DraismaVargas.Infrastructure.TargetExpansion
import Mathlib.Tactic

/-!
# The three target pairings at a four-valent wall

In source Case `{w4}`, the contracted target vertex has four labelled incident
edge occurrences.  Regrowing it as an edge requires a `2+2` split.  Up to
interchanging the two new endpoints, there are exactly three such splits:
`T_{2,3}`, `T_{2,4}`, and `T_{2,5}` in the paper.

This file proves that finite classification and turns each pairing into the
occurrence-wise Boolean assignment consumed by `TargetExpansion`.  It also
proves that every three distinct external branches split `1+2` under each
pairing, identifying the singleton branch used by the r0-nd3 resolution.
-/

namespace DraismaVargas.LocalCases.W4TargetPairings

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion

namespace Pairing

/-- The representative `2+2` split pairing label `0` with one of `1,2,3`. -/
def side (pairing : Fin 3) : Finset (Fin 4) :=
  {0, Fin.succ pairing}

/-- The Boolean endpoint assignment of a star label for one representative
pairing. -/
def labelRight (pairing : Fin 3) (label : Fin 4) : Bool :=
  decide (label ∈ side pairing)

@[simp]
theorem card_side (pairing : Fin 3) : (side pairing).card = 2 := by
  fin_cases pairing <;> decide +kernel

/-- Every two-element subset of four labels is one of the three representative
sides, or its complementary side. -/
theorem exhausts_up_to_complement (selected : Finset (Fin 4))
    (hcard : selected.card = 2) :
    ∃ pairing : Fin 3,
      selected = side pairing ∨ selectedᶜ = side pairing := by
  revert selected
  decide +kernel

/-- Any three distinct branches meet the two sides of a `2+2` pairing in a
singleton and a pair. -/
theorem three_distinct_one_against_two (pairing : Fin 3)
    (first second third : Fin 4) (hFirstSecond : first ≠ second)
    (hFirstThird : first ≠ third) (hSecondThird : second ≠ third) :
    (labelRight pairing first ≠ labelRight pairing second ∧
        labelRight pairing second = labelRight pairing third) ∨
      (labelRight pairing second ≠ labelRight pairing first ∧
        labelRight pairing first = labelRight pairing third) ∨
      (labelRight pairing third ≠ labelRight pairing first ∧
        labelRight pairing first = labelRight pairing second) := by
  revert first second third
  fin_cases pairing <;> decide +kernel

/-- The two labels lying on a prescribed side of a representative pairing. -/
def labelsOnSide (pairing : Fin 3) (sideValue : Bool) : Finset (Fin 4) :=
  Finset.univ.filter fun label => labelRight pairing label = sideValue

@[simp] theorem mem_labelsOnSide (pairing : Fin 3) (sideValue : Bool)
    (label : Fin 4) :
    label ∈ labelsOnSide pairing sideValue ↔
      labelRight pairing label = sideValue := by
  simp [labelsOnSide]

/-- Both sides of every representative W4 pairing contain two labels. -/
@[simp] theorem card_labelsOnSide (pairing : Fin 3) (sideValue : Bool) :
    (labelsOnSide pairing sideValue).card = 2 := by
  fin_cases pairing <;> cases sideValue <;> decide +kernel

/-- Sum a branch quantity over one side of a W4 target pairing. -/
def sideSum (pairing : Fin 3) (sideValue : Bool)
    (value : Fin 4 → ℤ) : ℤ :=
  ∑ label ∈ labelsOnSide pairing sideValue, value label

/-- Two positive branch terms give a side sum of at least two. -/
theorem sideSum_ge_two (pairing : Fin 3) (sideValue : Bool)
    (value : Fin 4 → ℤ) (hPositive : ∀ label, 1 ≤ value label) :
    2 ≤ sideSum pairing sideValue value := by
  have hBound :
      (∑ _label ∈ labelsOnSide pairing sideValue, (1 : ℤ)) ≤
        sideSum pairing sideValue value := by
    apply Finset.sum_le_sum
    intro label _hLabel
    exact hPositive label
  simpa [sideSum] using hBound

/-- The two side sums partition the four labelled branches. -/
theorem sideSum_false_add_true (pairing : Fin 3) (value : Fin 4 → ℤ) :
    sideSum pairing false value + sideSum pairing true value =
      ∑ label : Fin 4, value label := by
  classical
  unfold sideSum labelsOnSide
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin 4))
    (fun label ↦ labelRight pairing label = false) value]
  congr 2
  ext label
  cases hSide : labelRight pairing label <;> simp [hSide]

/-- If exactly one label on a side is selected, a value constant on the
selected and unselected labels has the expected two-term side sum. -/
theorem sideSum_eq_add_of_card_filter_eq_one (pairing : Fin 3)
    (sideValue : Bool) (selected : Finset (Fin 4))
    (hCard : ((labelsOnSide pairing sideValue).filter
      fun label ↦ label ∈ selected).card = 1)
    (value : Fin 4 → ℤ) (selectedValue otherValue : ℤ)
    (hSelected : ∀ label, label ∈ labelsOnSide pairing sideValue →
      label ∈ selected → value label = selectedValue)
    (hOther : ∀ label, label ∈ labelsOnSide pairing sideValue →
      label ∉ selected → value label = otherValue) :
    sideSum pairing sideValue value = selectedValue + otherValue := by
  classical
  let side := labelsOnSide pairing sideValue
  have hCardSide :
      (side.filter fun label ↦ label ∈ selected).card = 1 := by
    simpa [side] using hCard
  have hOtherCard :
      (side.filter fun label ↦ label ∉ selected).card = 1 := by
    have hPartition := Finset.card_filter_add_card_filter_not
      (s := side) (fun label ↦ label ∈ selected)
    rw [hCardSide, show side.card = 2 by simp [side]] at hPartition
    omega
  have hSelectedSum :
      (∑ label ∈ side.filter (fun label ↦ label ∈ selected), value label) =
        selectedValue := by
    calc
      (∑ label ∈ side.filter (fun label ↦ label ∈ selected),
          value label) =
          ∑ _label ∈ side.filter (fun label ↦ label ∈ selected),
            selectedValue := by
        apply Finset.sum_congr rfl
        intro label hLabel
        exact hSelected label (by
          simpa [side] using Finset.mem_of_mem_filter label hLabel)
          (Finset.mem_filter.mp hLabel).2
      _ = selectedValue := by simp [hCardSide]
  have hOtherSum :
      (∑ label ∈ side.filter (fun label ↦ label ∉ selected), value label) =
        otherValue := by
    calc
      (∑ label ∈ side.filter (fun label ↦ label ∉ selected),
          value label) =
          ∑ _label ∈ side.filter (fun label ↦ label ∉ selected),
            otherValue := by
        apply Finset.sum_congr rfl
        intro label hLabel
        exact hOther label (by
          simpa [side] using Finset.mem_of_mem_filter label hLabel)
          (Finset.mem_filter.mp hLabel).2
      _ = otherValue := by simp [hOtherCard]
  have hFilterEq :
      side.filter (fun label ↦ ¬label ∈ selected) =
        side.filter (fun label ↦ label ∉ selected) := by
    ext label
    simp
  unfold sideSum
  change (∑ label ∈ side, value label) = _
  rw [← Finset.sum_filter_add_sum_filter_not side
    (fun label ↦ label ∈ selected) value]
  rw [hFilterEq, hSelectedSum, hOtherSum]

/-- If exactly one label on a side is selected, one positive selected term
and one unselected term bounded below by `otherBound` give the corresponding
lower bound for the whole side. -/
theorem sideSum_ge_add_of_card_filter_eq_one (pairing : Fin 3)
    (sideValue : Bool) (selected : Finset (Fin 4))
    (hCard : ((labelsOnSide pairing sideValue).filter
      fun label ↦ label ∈ selected).card = 1)
    (value : Fin 4 → ℤ) (otherBound : ℤ)
    (hSelected : ∀ label, label ∈ labelsOnSide pairing sideValue →
      label ∈ selected → 1 ≤ value label)
    (hOther : ∀ label, label ∈ labelsOnSide pairing sideValue →
      label ∉ selected → otherBound ≤ value label) :
    otherBound + 1 ≤ sideSum pairing sideValue value := by
  classical
  let side := labelsOnSide pairing sideValue
  have hCardSide :
      (side.filter fun label ↦ label ∈ selected).card = 1 := by
    simpa [side] using hCard
  have hOtherCard :
      (side.filter fun label ↦ label ∉ selected).card = 1 := by
    have hPartition := Finset.card_filter_add_card_filter_not
      (s := side) (fun label ↦ label ∈ selected)
    rw [hCardSide, show side.card = 2 by simp [side]] at hPartition
    omega
  have hSelectedBound :
      1 ≤ ∑ label ∈ side.filter (fun label ↦ label ∈ selected),
        value label := by
    have hBound :
        (∑ _label ∈ side.filter (fun label ↦ label ∈ selected),
          (1 : ℤ)) ≤
          ∑ label ∈ side.filter (fun label ↦ label ∈ selected),
            value label := by
      apply Finset.sum_le_sum
      intro label hLabel
      exact hSelected label (by
        simpa [side] using Finset.mem_of_mem_filter label hLabel)
        (Finset.mem_filter.mp hLabel).2
    simpa [hCardSide] using hBound
  have hOtherBound :
      otherBound ≤
        ∑ label ∈ side.filter (fun label ↦ label ∉ selected),
          value label := by
    have hBound :
        (∑ _label ∈ side.filter (fun label ↦ label ∉ selected),
          otherBound) ≤
          ∑ label ∈ side.filter (fun label ↦ label ∉ selected),
            value label := by
      apply Finset.sum_le_sum
      intro label hLabel
      exact hOther label (by
        simpa [side] using Finset.mem_of_mem_filter label hLabel)
        (Finset.mem_filter.mp hLabel).2
    simpa [hOtherCard] using hBound
  unfold sideSum
  change otherBound + 1 ≤ ∑ label ∈ side, value label
  rw [← Finset.sum_filter_add_sum_filter_not side
    (fun label ↦ label ∈ selected) value]
  have hFilterEq :
      side.filter (fun label ↦ ¬label ∈ selected) =
        side.filter (fun label ↦ label ∉ selected) := by
    ext label
    simp
  rw [hFilterEq]
  omega

end Pairing

variable {target : CFGraph} {wall : target.V}

/-- An occurrence labelling of the four edges incident to a four-valent target
vertex.  Parallel occurrences remain distinct because the codomain is the
subtype of `target.edges`. -/
structure FourStar (target : CFGraph) (wall : target.V) where
  label : Fin 4 ≃ {edge : target.edges // edge ∈ GluingDatum.incidentEdges wall}

/-- Canonically label the incident occurrences of any four-valent target
vertex. -/
noncomputable def FourStar.of_card
    (hcard : (GluingDatum.incidentEdges wall).card = 4) :
    FourStar target wall where
  label := (Fintype.equivFinOfCardEq (by simpa using hcard)).symm

namespace FourStar

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-- The actual target-edge occurrence carrying a star label. -/
def edge (star : FourStar target wall) (label : Fin 4) : target.edges :=
  (star.label label).1

theorem edge_injective (star : FourStar target wall) :
    Function.Injective star.edge := by
  intro first second heq
  apply star.label.injective
  exact Subtype.ext heq

@[simp]
theorem edge_mem_incidentEdges (star : FourStar target wall) (label : Fin 4) :
    star.edge label ∈ GluingDatum.incidentEdges wall :=
  (star.label label).2

/-- Every incident target-edge occurrence has a unique four-star label. -/
theorem exists_edge_eq (star : FourStar target wall) (edge : target.edges)
    (hEdge : edge ∈ GluingDatum.incidentEdges wall) :
    ∃ label : Fin 4, star.edge label = edge := by
  let labelled : {edge : target.edges //
      edge ∈ GluingDatum.incidentEdges wall} := ⟨edge, hEdge⟩
  refine ⟨star.label.symm labelled, ?_⟩
  exact congrArg Subtype.val (star.label.apply_symm_apply labelled)

/-- Every labelled star occurrence carries a sheet partition refining the
partition above the central wall vertex. -/
theorem edgePartition_refines_wall (star : FourStar target wall)
    (data : GluingDatum target d) (label : Fin 4) :
    (data.edgePartition (star.edge label)).Refines
      (data.vertexPartition wall) := by
  have hIncident := star.edge_mem_incidentEdges label
  simp only [GluingDatum.incidentEdges, Finset.mem_filter,
    Finset.mem_univ, true_and] at hIncident
  rcases hIncident with hLeft | hRight
  · simpa [hLeft] using data.refines_left (star.edge label)
  · simpa [hRight] using data.refines_right (star.edge label)

/-- The two actual occurrences placed at the fresh endpoint for one of the
three representative pairings. -/
noncomputable def rightSet (star : FourStar target wall) (pairing : Fin 3) :
    Finset target.edges :=
  {star.edge 0, star.edge (Fin.succ pairing)}

@[simp]
theorem card_rightSet (star : FourStar target wall) (pairing : Fin 3) :
    (star.rightSet pairing).card = 2 := by
  unfold rightSet
  rw [Finset.card_pair]
  intro heq
  have hlabel := star.edge_injective heq
  have hvalue := congrArg Fin.val hlabel
  simp at hvalue

theorem rightSet_subset_incidentEdges (star : FourStar target wall)
    (pairing : Fin 3) :
    star.rightSet pairing ⊆ GluingDatum.incidentEdges wall := by
  intro targetEdge hEdge
  simp only [rightSet, Finset.mem_insert, Finset.mem_singleton] at hEdge
  rcases hEdge with rfl | rfl <;> exact star.edge_mem_incidentEdges _

/-- Occurrence-wise side assignment used by `TargetExpansion`. -/
noncomputable def right (star : FourStar target wall) (pairing : Fin 3)
    (targetEdge : target.edges) : Bool :=
  decide (targetEdge ∈ star.rightSet pairing)

@[simp]
theorem right_eq_true_iff (star : FourStar target wall) (pairing : Fin 3)
    (targetEdge : target.edges) :
    star.right pairing targetEdge = true ↔
      targetEdge ∈ star.rightSet pairing := by
  simp [right]

@[simp]
theorem right_eq_false_iff (star : FourStar target wall) (pairing : Fin 3)
    (targetEdge : target.edges) :
    star.right pairing targetEdge = false ↔
      targetEdge ∉ star.rightSet pairing := by
  simp [right]

/-- On the labelled four-star, the occurrence assignment is exactly the
finite label assignment above. -/
@[simp]
theorem right_edge (star : FourStar target wall) (pairing : Fin 3)
    (label : Fin 4) :
    star.right pairing (star.edge label) = Pairing.labelRight pairing label := by
  simp only [right, rightSet, Pairing.labelRight, Pairing.side,
    Finset.mem_insert, Finset.mem_singleton]
  simp only [star.edge_injective.eq_iff]

/-- For any three distinct actual star branches, exactly one lies on the side
opposite the other two.  The disjunction names that singleton branch. -/
theorem three_distinct_one_against_two (star : FourStar target wall)
    (pairing : Fin 3) (first second third : Fin 4)
    (hFirstSecond : first ≠ second) (hFirstThird : first ≠ third)
    (hSecondThird : second ≠ third) :
    (star.right pairing (star.edge first) ≠
          star.right pairing (star.edge second) ∧
        star.right pairing (star.edge second) =
          star.right pairing (star.edge third)) ∨
      (star.right pairing (star.edge second) ≠
          star.right pairing (star.edge first) ∧
        star.right pairing (star.edge first) =
          star.right pairing (star.edge third)) ∨
      (star.right pairing (star.edge third) ≠
          star.right pairing (star.edge first) ∧
        star.right pairing (star.edge first) =
          star.right pairing (star.edge second)) := by
  simpa only [right_edge] using
    Pairing.three_distinct_one_against_two pairing first second third
      hFirstSecond hFirstThird hSecondThird

/-- Labels placed on the fresh side by an arbitrary occurrence assignment. -/
def selectedLabels (star : FourStar target wall)
    (assignment : target.edges → Bool) : Finset (Fin 4) :=
  Finset.univ.filter fun label => assignment (star.edge label) = true

/-- Every occurrence assignment selecting two of the four wall labels agrees,
up to swapping the new target endpoints, with one of the three paper pairings. -/
theorem exhausts_assignment_up_to_swap (star : FourStar target wall)
    (assignment : target.edges → Bool)
    (hcard : (star.selectedLabels assignment).card = 2) :
    ∃ pairing : Fin 3,
      star.selectedLabels assignment = Pairing.side pairing ∨
      (star.selectedLabels assignment)ᶜ = Pairing.side pairing :=
  Pairing.exhausts_up_to_complement _ hcard

/-- The fresh side contains exactly the chosen two wall occurrences. -/
theorem wallEdgesAssigned_true (star : FourStar target wall) (pairing : Fin 3) :
    wallEdgesAssigned target wall (star.right pairing) true =
      star.rightSet pairing := by
  ext targetEdge
  constructor
  · intro h
    have hAssigned :=
      (mem_wallEdgesAssigned target wall (star.right pairing) true targetEdge).mp h
    exact (right_eq_true_iff star pairing targetEdge).mp hAssigned.2
  · intro h
    apply (mem_wallEdgesAssigned target wall (star.right pairing) true targetEdge).mpr
    refine ⟨?_, (right_eq_true_iff star pairing targetEdge).mpr h⟩
    have hIncident := star.rightSet_subset_incidentEdges pairing h
    simpa [GluingDatum.incidentEdges] using hIncident

/-- The retained side contains the other two wall occurrences. -/
theorem wallEdgesAssigned_false (star : FourStar target wall) (pairing : Fin 3) :
    wallEdgesAssigned target wall (star.right pairing) false =
      GluingDatum.incidentEdges wall \ star.rightSet pairing := by
  ext targetEdge
  simp [mem_wallEdgesAssigned, GluingDatum.incidentEdges, right]

@[simp]
theorem card_incidentEdges (star : FourStar target wall) :
    (GluingDatum.incidentEdges wall).card = 4 := by
  rw [← Fintype.card_coe]
  simpa using (Fintype.card_congr star.label).symm

@[simp]
theorem card_wallEdgesAssigned_true (star : FourStar target wall)
    (pairing : Fin 3) :
    (wallEdgesAssigned target wall (star.right pairing) true).card = 2 := by
  rw [star.wallEdgesAssigned_true]
  exact star.card_rightSet pairing

@[simp]
theorem card_wallEdgesAssigned_false (star : FourStar target wall)
    (pairing : Fin 3) :
    (wallEdgesAssigned target wall (star.right pairing) false).card = 2 := by
  rw [star.wallEdgesAssigned_false,
    Finset.card_sdiff_of_subset (star.rightSet_subset_incidentEdges pairing),
    star.card_incidentEdges, star.card_rightSet]

/-- A canonical occurrence list for the fresh side of an expansion. -/
noncomputable def rightEdges (star : FourStar target wall) (pairing : Fin 3) :
    List target.edges :=
  (star.rightSet pairing).toList

/-- A canonical occurrence list for the retained side of an expansion. -/
noncomputable def leftEdges (star : FourStar target wall) (pairing : Fin 3) :
    List target.edges :=
  (GluingDatum.incidentEdges wall \ star.rightSet pairing).toList

/-- The canonical fresh-side list enumerates exactly its assigned old
occurrences. -/
theorem rightEdges_eq (star : FourStar target wall) (pairing : Fin 3) :
    (star.rightEdges pairing : Multiset target.edges) =
      (wallEdgesAssigned target wall (star.right pairing) true).val := by
  rw [rightEdges, Finset.coe_toList, star.wallEdgesAssigned_true]

/-- The canonical retained-side list enumerates exactly its assigned old
occurrences. -/
theorem leftEdges_eq (star : FourStar target wall) (pairing : Fin 3) :
    (star.leftEdges pairing : Multiset target.edges) =
      (wallEdgesAssigned target wall (star.right pairing) false).val := by
  rw [leftEdges, Finset.coe_toList, star.wallEdgesAssigned_false]

/-- Summing a quantity over the four labels is the same as summing it over
the actual incident target-edge occurrences. -/
theorem sum_edge_eq_sum_incident (star : FourStar target wall)
    {R : Type*} [AddCommMonoid R] (value : target.edges → R) :
    ∑ label : Fin 4, value (star.edge label) =
      ∑ edge ∈ GluingDatum.incidentEdges wall, value edge := by
  calc
    ∑ label : Fin 4, value (star.edge label) =
        ∑ edge : {edge : target.edges //
          edge ∈ GluingDatum.incidentEdges wall}, value edge.1 := by
      apply Fintype.sum_equiv star.label
      intro label
      rfl
    _ = ∑ edge ∈ GluingDatum.incidentEdges wall, value edge := by
      exact Finset.sum_attach (GluingDatum.incidentEdges wall) value

/-- At a four-valent target wall, the original Riemann--Hurwitz condition is
the lower bound `2m + 2` for the four labelled branch counts. -/
theorem branchCount_sum_ge_two_mul_add_two
    (star : FourStar target wall) (data : GluingDatum target degree)
    (hRiemannHurwitz : data.RiemannHurwitzAtTargetVertex wall)
    (sheet : Fin degree) :
    2 * ((data.vertexPartition wall).blockCard sheet : ℤ) + 2 ≤
      ∑ label : Fin 4,
        ((data.edgePartition (star.edge label)).blockCountWithin
          (data.vertexPartition wall) sheet : ℤ) := by
  have hWall := hRiemannHurwitz sheet
  rw [← star.sum_edge_eq_sum_incident (fun edge ↦
    ((data.edgePartition edge).blockCountWithin
      (data.vertexPartition wall) sheet : ℤ))] at hWall
  rw [star.card_incidentEdges] at hWall
  omega

/-- The canonical fresh-side list sums exactly the label terms assigned
`true` by the pairing. -/
theorem sum_rightEdges (star : FourStar target wall) (pairing : Fin 3)
    {R : Type*} [AddCommMonoid R] (value : target.edges → R) :
    ((star.rightEdges pairing).map value).sum =
      ∑ label : Fin 4,
        if Pairing.labelRight pairing label then value (star.edge label)
        else 0 := by
  classical
  rw [rightEdges]
  rw [← List.sum_toFinset value (Finset.nodup_toList (star.rightSet pairing))]
  simp only [Finset.toList_toFinset]
  fin_cases pairing <;>
    simp [rightSet, Pairing.labelRight, Pairing.side, Fin.sum_univ_succ,
      star.edge_injective.eq_iff]

/-- The canonical retained-side list sums exactly the label terms assigned
`false` by the pairing. -/
theorem sum_leftEdges (star : FourStar target wall) (pairing : Fin 3)
    {R : Type*} [AddCommGroup R] (value : target.edges → R) :
    ((star.leftEdges pairing).map value).sum =
      ∑ label : Fin 4,
        if Pairing.labelRight pairing label then 0
        else value (star.edge label) := by
  classical
  apply add_right_cancel (b := ((star.rightEdges pairing).map value).sum)
  calc
    ((star.leftEdges pairing).map value).sum +
        ((star.rightEdges pairing).map value).sum =
        ∑ edge ∈ GluingDatum.incidentEdges wall, value edge := by
      rw [leftEdges, rightEdges]
      rw [← List.sum_toFinset value (Finset.nodup_toList
        (GluingDatum.incidentEdges wall \ star.rightSet pairing))]
      rw [← List.sum_toFinset value
        (Finset.nodup_toList (star.rightSet pairing))]
      simp only [Finset.toList_toFinset]
      exact Finset.sum_sdiff (star.rightSet_subset_incidentEdges pairing)
    _ = ∑ label : Fin 4, value (star.edge label) :=
      (star.sum_edge_eq_sum_incident value).symm
    _ = (∑ label : Fin 4,
          if Pairing.labelRight pairing label then 0
          else value (star.edge label)) +
        ∑ label : Fin 4,
          if Pairing.labelRight pairing label then value (star.edge label)
          else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro label _
      cases Pairing.labelRight pairing label <;> simp
    _ = (∑ label : Fin 4,
          if Pairing.labelRight pairing label then 0
          else value (star.edge label)) +
        ((star.rightEdges pairing).map value).sum := by
      rw [star.sum_rightEdges pairing value]

/-- Fresh-side occurrence sums in the common `Pairing.sideSum` notation. -/
theorem sum_rightEdges_eq_sideSum (star : FourStar target wall)
    (pairing : Fin 3) (value : target.edges → ℤ) :
    ((star.rightEdges pairing).map value).sum =
      Pairing.sideSum pairing true (fun label ↦ value (star.edge label)) := by
  rw [star.sum_rightEdges pairing value]
  simp [Pairing.sideSum, Pairing.labelsOnSide, Finset.sum_filter]

/-- Retained-side occurrence sums in the common `Pairing.sideSum` notation. -/
theorem sum_leftEdges_eq_sideSum (star : FourStar target wall)
    (pairing : Fin 3) (value : target.edges → ℤ) :
    ((star.leftEdges pairing).map value).sum =
      Pairing.sideSum pairing false (fun label ↦ value (star.edge label)) := by
  rw [star.sum_leftEdges pairing value]
  unfold Pairing.sideSum Pairing.labelsOnSide
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro label _hLabel
  cases Pairing.labelRight pairing label <;> simp

@[simp]
theorem length_rightEdges (star : FourStar target wall) (pairing : Fin 3) :
    (star.rightEdges pairing).length = 2 := by
  rw [rightEdges, Finset.length_toList, star.card_rightSet]

@[simp]
theorem length_leftEdges (star : FourStar target wall) (pairing : Fin 3) :
    (star.leftEdges pairing).length = 2 := by
  rw [leftEdges, Finset.length_toList,
    Finset.card_sdiff_of_subset (star.rightSet_subset_incidentEdges pairing),
    star.card_incidentEdges, star.card_rightSet]

end FourStar

end DraismaVargas.LocalCases.W4TargetPairings
