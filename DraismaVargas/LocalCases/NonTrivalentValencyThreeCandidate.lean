module

public import DraismaVargas.LocalCases.NonTrivalentValencyFourKZero
public import DraismaVargas.LocalCases.NonTrivalentValencyThreeRigidity

@[expose] public section

/-!
# Part II, valency three: the prescribed candidate of case `{v3-nd4}`

Source: Vargas, Part II (arXiv:2609.09109), Section 5.3 (valency-3 limits,
Case {v3-nd4}) and its figures.

## The construction

At a three-valent wall `w0` the contracted edge `t1` has a divalent end `u`
and a trivalent end `v`, so the outgoing base tree is the old star with one
subdivision point `u` placed on one of `t2, t3, t4`.  The anchor `A` above
`w0` has `r0(A) = 1` and four surviving occurrences distributed `2+1+1` over
the three star directions (`NonTrivalentValencyThreeAnchor.ThreeBranchAnchor`).

This module constructs the base tree `T_2` of the source: the subdivision
point is placed on the *doubled* direction.  In the paper's notation that is
the choice with `|A_u| = k_1' = k_2 + k_5` and `|A_v| = |A|`, i.e. Type III
(`H_{2,5}`); the paper's own remark is that its two vertex inequalities,
`|A| >= k_2 + k_5` and `|A| >= k_3, k_4`, hold unconditionally, while the
Type I and Type II choices each need one of the complementary numerical
conditions `k_4 + k_2 <= |A|` or `k_4 + k_2 >= |A| + 1`.  This module supplies
Type III unconditionally.  On the prescribed-type route of the outer walk
(`OuterWalk.TypeChangeLink` realizes a prescribed Whitehead move) every wall
needs a candidate of each of Types I, II and III;
`NonTrivalentValencyThreeSimpleCandidate` supplies Types I and II over a
two-fold block-preserving branch gauge, with the index-order subcases
`{v3-nd4-1}`/`{v3-nd4-2}` selecting the Type I pair.

Concretely, and unlike the valency-four `K = 0` construction, no
block-preserving branch gauge is used: the two surviving occurrences of the
doubled direction are two distinct classes of the *same* edge partition, hence
already disjoint, and the new bridge class is their honest union, of size
exactly `k_2 + k_5` (not `k_2 + k_5 - 1`).

## What is proved

* `selectedSheets`, `finePartition`, `selectedResolution`: the local
  resolution at `A`, its contraction and its exact endpoint sizes.
* `selected_riemannHurwitz_left` / `selected_riemannHurwitz_right`: both
  endpoint Riemann--Hurwitz inequalities at `A` from the exact block counts.
  The divalent (`u`) side is automatic; the trivalent (`v`) side holds with
  *equality* and is exactly where identity `(boxplus)` of the source enters.
* `SubdivisionBackground`, `candidate`: the installation into the guarded
  background of the other wall blocks through
  `GlobalM11Arbitrary.Background.install`.
* `subdivisionBackground`: the background **producer**.  At a
  trivalent wall the rigid blocks need no census at all: the single global
  resolution `fineResolution (vertexPartition wall) (edgePartition doubled)`
  serves every block, its exterior refinement is global, its divalent endpoint
  is automatic, and its trivalent endpoint inequality is literally the
  incoming datum's own Riemann--Hurwitz condition at `wall`.  So no analogue of
  `NonTrivalentValencyFourBackground.OrdinaryBlockProfile` is needed, and no
  `nd <= 3` residual off the anchor remains.
* `validCandidate`, `validCandidate_datum_valid` and
  `exists_valid_candidate_of_contraction`: the candidate and the validity of its
  outgoing datum, with **no** background hypothesis -- the last one stated
  directly from an incoming full-dimensional cover and its contraction forest.

## What is NOT proved

* `nd(A) = 4` at the wall block is an explicit hypothesis throughout
  (`NonTrivalentUniqueFourValent.card_branchFibreVertices_add_two_eq_nonDanglingValency`
  reduces it to "the anchor's fibre has exactly two incoming branch vertices").
* No stable type, row dictionary, honest matrix or pencil: those follow in
  `NonTrivalentValencyThreeRows` and the modules after it, mirroring
  `NonTrivalentValencyFourRows`.

## Consumers

The boundary dispatcher for Part II, Case {v3-nd4}
(`NonTrivalentValencyThreeDispatcher`).
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyThreeCandidate

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases.GlobalM11Arbitrary
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionCoarseFine
open DraismaVargas.LocalCases.ResolutionM1k
open DraismaVargas.LocalCases.NonTrivalentValencyThreeAnchor
open DraismaVargas.LocalCases.ThirdEquation
open DraismaVargas.LocalCases.W3R1SourceProfile
open W4Assembly W4StableSource

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (data : GluingDatum target degree)
    (vertex : data.SourceVertex) : DecidableEq (IncidentSourceEdge data vertex) :=
  Classical.decEq _

variable {data : GluingDatum target degree} {star : ThreeStar target wall}
  {anchor : WallBlock data wall}

/-! ## 1.  The three star directions, rotated to put the doubled one first -/

/-- The three labels of a trivalent star, listed from any chosen one. -/
private theorem sum_fin_three_rotate {M : Type*} [AddCommMonoid M]
    (label : Fin 3) (value : Fin 3 → M) :
    ∑ other : Fin 3, value other =
      value label + value (label + 1) + value (label + 2) := by
  fin_cases label <;> simp [Fin.sum_univ_three] <;> abel

private theorem rotate_ne_self (label : Fin 3) : label + 1 ≠ label := by
  revert label; decide

private theorem rotate_two_ne_self (label : Fin 3) : label + 2 ≠ label := by
  revert label; decide

private theorem rotate_ne_rotate_two (label : Fin 3) : label + 1 ≠ label + 2 := by
  revert label; decide

namespace Prescribed

variable (source : ThreeBranchAnchor data star anchor)

/-- The unique target direction carrying two surviving occurrences: the
paper's `t_2`, the edge on which the outgoing base tree `T_2` puts its
divalent subdivision point `u`. -/
noncomputable def doubled : Fin 3 := source.distribution.doubledDirection

/-- The literal doubled target occurrence. -/
noncomputable def doubledEdge : target.edges := directionEdge star (doubled source)

/-- The first simple direction, the paper's `t_3`. -/
noncomputable def firstSimple : Fin 3 := doubled source + 1

/-- The second simple direction, the paper's `t_4`. -/
noncomputable def secondSimple : Fin 3 := doubled source + 2

theorem firstSimple_ne : firstSimple source ≠ doubled source :=
  rotate_ne_self _

theorem secondSimple_ne : secondSimple source ≠ doubled source :=
  rotate_two_ne_self _

theorem firstSimple_ne_secondSimple :
    firstSimple source ≠ secondSimple source :=
  rotate_ne_rotate_two _

theorem doubledEdge_mem_incidentEdges :
    doubledEdge source ∈ GluingDatum.incidentEdges wall :=
  directionEdge_mem_incidentEdges star (doubled source)

theorem directionEdge_refines (label : Fin 3) :
    (data.edgePartition (directionEdge star label)).Refines
      (data.vertexPartition wall) :=
  edgePartition_refines_of_mem_incidentEdges data wall _
    (directionEdge_mem_incidentEdges star label)

theorem doubledEdge_refines :
    (data.edgePartition (doubledEdge source)).Refines
      (data.vertexPartition wall) :=
  directionEdge_refines (data := data) (star := star) (doubled source)

/-! ## 2.  Every star direction is its surviving classes plus dangling
singletons inside the anchor block -/

/-- The sheet named by an incident source occurrence. -/
def occurrenceSheet {vertex : data.SourceVertex}
    (edge : IncidentSourceEdge data vertex) : Fin degree := edge.1.1.2

theorem occurrenceSheet_wall_rel
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)) :
    (data.vertexPartition wall).Rel anchor.1 (occurrenceSheet edge) := by
  have hIncident := (incident_wallBlock_sourceVertex_iff data anchor edge.1).mp edge.2
  have hRepr : (data.vertexPartition wall).repr (occurrenceSheet edge) = anchor.1 :=
    congrArg Subtype.val hIncident.2
  unfold SheetPartition.Rel
  rw [hRepr]
  exact anchor.2

theorem sourceEdgeIndex_eq_blockCard {label : Fin 3}
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor label) :
    data.sourceEdgeIndex edge.1 =
      (data.edgePartition (directionEdge star label)).blockCard
        (occurrenceSheet edge) := by
  have hTarget : edge.1.1.1 = directionEdge star label :=
    ((mem_directionSurvivors data star anchor label edge).mp hEdge).2
  unfold GluingDatum.sourceEdgeIndex occurrenceSheet
  rw [hTarget]

/-- Inside the anchor's wall block, each target direction consists of the
classes of its surviving occurrences together with dangling singletons.  This
is the valency-three form of
`NonTrivalentValencyFourKZero.PrescribedPairing.mem_branchBlock_or_block_singleton`;
unlike there, a direction may carry two surviving classes. -/
theorem mem_survivorBlock_or_singleton (hNoGlue : DanglingEdgeNoGlue data)
    (label : Fin 3) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel anchor.1 sheet) :
    (∃ edge ∈ directionSurvivors data star anchor label,
        (data.edgePartition (directionEdge star label)).Rel
          (occurrenceSheet edge) sheet) ∨
      (data.edgePartition (directionEdge star label)).block sheet = {sheet} := by
  classical
  by_cases hDangling :
      IsDangling data (data.sourceEdge (directionEdge star label) sheet)
  · right
    apply (data.edgePartition
      (directionEdge star label)).block_eq_singleton_of_blockCard_eq_one
    rw [← data.sourceEdgeIndex_sourceEdge]
    exact hNoGlue _ hDangling
  · left
    have hReprRel :
        (data.vertexPartition wall).Rel anchor.1
          ((data.edgePartition (directionEdge star label)).repr sheet) := by
      refine hWall.trans ?_
      exact ((directionEdge_refines (data := data) (star := star) label).rel
          ((data.edgePartition (directionEdge star label)).rel_repr_right sheet))
    have hIncident :
        Incident data (data.sourceEdge (directionEdge star label) sheet)
          (WallBlock.sourceVertex data wall anchor) := by
      refine (incident_wallBlock_sourceVertex_iff data anchor _).mpr
        ⟨directionEdge_mem_incidentEdges star label, ?_⟩
      apply Subtype.ext
      change (data.vertexPartition wall).repr
        ((data.edgePartition (directionEdge star label)).repr sheet) = anchor.1
      unfold SheetPartition.Rel at hReprRel
      rw [← hReprRel, anchor.2]
    refine ⟨⟨data.sourceEdge (directionEdge star label) sheet, hIncident⟩, ?_, ?_⟩
    · refine (mem_directionSurvivors data star anchor label _).mpr ⟨?_, rfl⟩
      exact (mem_survivors data anchor _).mpr hDangling
    · exact (data.edgePartition (directionEdge star label)).rel_repr_left sheet

/-! ## 3.  The exact block counts inside the anchor -/

/-- Identity `(boxplus)` of the source, split over the three star directions:
the doubled direction carries `k_2 + k_5`, the two simple directions carry
`k_3` and `k_4`, and the total is `2|A| + 1`. -/
theorem sum_directionSurvivors_index :
    (∑ edge ∈ directionSurvivors data star anchor (doubled source),
        data.sourceEdgeIndex edge.1) +
      (∑ edge ∈ directionSurvivors data star anchor (firstSimple source),
        data.sourceEdgeIndex edge.1) +
      (∑ edge ∈ directionSurvivors data star anchor (secondSimple source),
        data.sourceEdgeIndex edge.1) =
      2 * (data.vertexPartition wall).blockCard anchor.1 + 1 := by
  classical
  have hFiber :
      ∑ label : Fin 3, ∑ edge ∈ directionSurvivors data star anchor label,
          (data.sourceEdgeIndex edge.1 : ℤ) =
        ∑ edge ∈ survivors data anchor, (data.sourceEdgeIndex edge.1 : ℤ) := by
    simp only [directionSurvivors]
    exact Finset.sum_fiberwise_of_maps_to (fun _ _ ↦ Finset.mem_univ _) _
  rw [sum_fin_three_rotate (doubled source)] at hFiber
  rw [source.survivor_index_sum] at hFiber
  have hCast : ((∑ edge ∈ directionSurvivors data star anchor (doubled source),
        data.sourceEdgeIndex edge.1) +
      (∑ edge ∈ directionSurvivors data star anchor (firstSimple source),
        data.sourceEdgeIndex edge.1) +
      (∑ edge ∈ directionSurvivors data star anchor (secondSimple source),
        data.sourceEdgeIndex edge.1) : ℤ) =
      2 * ((data.vertexPartition wall).blockCard anchor.1 : ℤ) + 1 := by
    push_cast
    exact hFiber
  exact_mod_cast hCast

/-- A simple direction has exactly one surviving class, so its induced block
count inside `A` is `|A| + 1 - k`. -/
theorem simple_blockCountWithin_add_sum (hNoGlue : DanglingEdgeNoGlue data)
    (label : Fin 3) (hLabel : label ≠ doubled source) :
    (data.edgePartition (directionEdge star label)).blockCountWithin
        (data.vertexPartition wall) anchor.1 +
      (∑ edge ∈ directionSurvivors data star anchor label,
        data.sourceEdgeIndex edge.1) =
      (data.vertexPartition wall).blockCard anchor.1 + 1 := by
  classical
  obtain ⟨only, hOnly⟩ := Finset.card_eq_one.mp
    (source.distribution.other_count label hLabel)
  have hMem : only ∈ directionSurvivors data star anchor label := by
    rw [hOnly]; exact Finset.mem_singleton_self only
  have hCount := NonTrivalentValencyFourKZero.PrescribedPairing.blockCountWithin_add_blockCard_eq
    (data.edgePartition (directionEdge star label)) (data.vertexPartition wall)
    anchor.1 (occurrenceSheet only)
    (occurrenceSheet_wall_rel only)
    (directionEdge_refines (data := data) (star := star) label) (by
      intro sheet hWall
      rcases mem_survivorBlock_or_singleton (star := star) hNoGlue label sheet hWall with
        ⟨edge, hEdge, hRel⟩ | hSingleton
      · left
        rw [hOnly, Finset.mem_singleton] at hEdge
        rwa [hEdge] at hRel
      · exact Or.inr hSingleton)
  rw [hOnly, Finset.sum_singleton, sourceEdgeIndex_eq_blockCard hMem]
  exact hCount

/-! ## 4.  The two surviving classes of the doubled direction -/

theorem exists_doubled_pair :
    ∃ first second, first ≠ second ∧
      directionSurvivors data star anchor (doubled source) = {first, second} :=
  Finset.card_eq_two.mp source.distribution.doubled_count

/-- The paper's occurrence `e_2`. -/
noncomputable def firstDoubled :
    IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor) :=
  Classical.choose (exists_doubled_pair source)

/-- The paper's occurrence `e_5`. -/
noncomputable def secondDoubled :
    IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor) :=
  Classical.choose (Classical.choose_spec (exists_doubled_pair source))

theorem firstDoubled_ne_secondDoubled :
    firstDoubled source ≠ secondDoubled source :=
  (Classical.choose_spec (Classical.choose_spec (exists_doubled_pair source))).1

theorem directionSurvivors_doubled_eq_pair :
    directionSurvivors data star anchor (doubled source) =
      {firstDoubled source, secondDoubled source} :=
  (Classical.choose_spec (Classical.choose_spec (exists_doubled_pair source))).2

theorem firstDoubled_mem :
    firstDoubled source ∈ directionSurvivors data star anchor (doubled source) := by
  rw [directionSurvivors_doubled_eq_pair]; exact Finset.mem_insert_self _ _

theorem secondDoubled_mem :
    secondDoubled source ∈ directionSurvivors data star anchor (doubled source) := by
  rw [directionSurvivors_doubled_eq_pair]
  exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- The two doubled-direction sheets are distinct fixed points of the same
edge partition; this is why no branch gauge is needed at a trivalent wall. -/
theorem occurrenceSheet_doubled_ne :
    occurrenceSheet (firstDoubled source) ≠ occurrenceSheet (secondDoubled source) := by
  intro hEq
  apply firstDoubled_ne_secondDoubled source
  have hFirst : (firstDoubled source).1.1.1 = doubledEdge source :=
    ((mem_directionSurvivors data star anchor _ _).mp (firstDoubled_mem source)).2
  have hSecond : (secondDoubled source).1.1.1 = doubledEdge source :=
    ((mem_directionSurvivors data star anchor _ _).mp (secondDoubled_mem source)).2
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rw [hFirst, hSecond]
  · exact hEq

theorem not_rel_occurrenceSheet_doubled :
    ¬ (data.edgePartition (doubledEdge source)).Rel
      (occurrenceSheet (firstDoubled source)) (occurrenceSheet (secondDoubled source)) := by
  intro hRel
  apply occurrenceSheet_doubled_ne source
  have hFirst : (data.edgePartition (doubledEdge source)).repr
      (occurrenceSheet (firstDoubled source)) = occurrenceSheet (firstDoubled source) := by
    have hTarget : (firstDoubled source).1.1.1 = doubledEdge source :=
      ((mem_directionSurvivors data star anchor _ _).mp (firstDoubled_mem source)).2
    have := (firstDoubled source).1.2
    rw [hTarget] at this
    exact this
  have hSecond : (data.edgePartition (doubledEdge source)).repr
      (occurrenceSheet (secondDoubled source)) = occurrenceSheet (secondDoubled source) := by
    have hTarget : (secondDoubled source).1.1.1 = doubledEdge source :=
      ((mem_directionSurvivors data star anchor _ _).mp (secondDoubled_mem source)).2
    have := (secondDoubled source).1.2
    rw [hTarget] at this
    exact this
  unfold SheetPartition.Rel at hRel
  rw [hFirst, hSecond] at hRel
  exact hRel

/-! ## 5.  The endpoint over the divalent subdivision point `u` -/

/-- The literal `A_u` of the paper: the honest union of the two surviving
classes of the doubled direction.  It needs no gauge, because the two classes
are distinct blocks of one and the same edge partition. -/
noncomputable def selectedSheets : Finset (Fin degree) :=
  (data.edgePartition (doubledEdge source)).block
      (occurrenceSheet (firstDoubled source)) ∪
    (data.edgePartition (doubledEdge source)).block
      (occurrenceSheet (secondDoubled source))

/-- The canonical sheet naming the new bridge class. -/
noncomputable def selectedRepresentative : Fin degree :=
  occurrenceSheet (firstDoubled source)

theorem selectedRepresentative_mem :
    selectedRepresentative source ∈ selectedSheets source :=
  Finset.mem_union_left _
    ((data.edgePartition (doubledEdge source)).self_mem_block _)

theorem selectedSheets_subset_wall :
    selectedSheets source ⊆ (data.vertexPartition wall).block anchor.1 := by
  apply Finset.union_subset
  · intro sheet hSheet
    rw [SheetPartition.mem_block_iff] at hSheet
    refine ((data.vertexPartition wall).mem_block_iff _ _).mpr ?_
    exact (occurrenceSheet_wall_rel (firstDoubled source)).trans
      ((doubledEdge_refines source).rel hSheet)
  · intro sheet hSheet
    rw [SheetPartition.mem_block_iff] at hSheet
    refine ((data.vertexPartition wall).mem_block_iff _ _).mpr ?_
    exact (occurrenceSheet_wall_rel (secondDoubled source)).trans
      ((doubledEdge_refines source).rel hSheet)

/-- The exact size of the new bridge class: `|A_u| = k_2 + k_5`.  At valency
four the corresponding union has size `k_a + k_b - 1`; here the two classes
are disjoint, so nothing is lost. -/
theorem selectedSheets_card :
    (selectedSheets source).card =
      ∑ edge ∈ directionSurvivors data star anchor (doubled source),
        data.sourceEdgeIndex edge.1 := by
  classical
  have hDisjoint :
      (data.edgePartition (doubledEdge source)).block
          (occurrenceSheet (firstDoubled source)) ∩
        (data.edgePartition (doubledEdge source)).block
          (occurrenceSheet (secondDoubled source)) = ∅ := by
    refine Finset.eq_empty_of_forall_notMem ?_
    intro sheet hSheet
    rw [Finset.mem_inter, SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
      at hSheet
    exact not_rel_occurrenceSheet_doubled source (hSheet.1.trans hSheet.2.symm)
  have hUnion := Finset.card_union_add_card_inter
    ((data.edgePartition (doubledEdge source)).block
      (occurrenceSheet (firstDoubled source)))
    ((data.edgePartition (doubledEdge source)).block
      (occurrenceSheet (secondDoubled source)))
  rw [hDisjoint] at hUnion
  simp only [Finset.card_empty, Nat.add_zero] at hUnion
  rw [directionSurvivors_doubled_eq_pair,
    Finset.sum_pair (firstDoubled_ne_secondDoubled source),
    sourceEdgeIndex_eq_blockCard (firstDoubled_mem source),
    sourceEdgeIndex_eq_blockCard (secondDoubled_mem source)]
  exact hUnion

/-- The paper's vertex inequality `|A| >= k_2 + k_5`, which is why the base
tree `T_2` (Type III) is admissible with no index-order condition: the two
surviving classes of the doubled direction are disjoint subsets of `A`. -/
theorem selectedSheets_card_le_blockCard :
    (∑ edge ∈ directionSurvivors data star anchor (doubled source),
        data.sourceEdgeIndex edge.1) ≤
      (data.vertexPartition wall).blockCard anchor.1 := by
  rw [← selectedSheets_card source]
  exact Finset.card_le_card (selectedSheets_subset_wall source)

/-- The endpoint partition over the divalent subdivision point: the new bridge
class on the anchor block, singletons on the rest of the anchor block, and the
old wall partition elsewhere. -/
noncomputable def finePartition : SheetPartition degree :=
  NonTrivalentValencyFourKZero.PrescribedPairing.withSelectedBlock
    (data.vertexPartition wall) anchor.1 (selectedRepresentative source)
    (selectedSheets source) (selectedRepresentative_mem source)
    (selectedSheets_subset_wall source)

theorem finePartition_refines :
    (finePartition source).Refines (data.vertexPartition wall) :=
  NonTrivalentValencyFourKZero.PrescribedPairing.withSelectedBlock.refines _ _ _ _ _ _

theorem finePartition_selected_block :
    (finePartition source).block (selectedRepresentative source) =
      selectedSheets source :=
  NonTrivalentValencyFourKZero.PrescribedPairing.withSelectedBlock.block_representative
    _ _ _ _ _ _

/-- The exact new-edge size on the local resolution: `k_1' = k_2 + k_5`. -/
theorem finePartition_selected_card :
    (finePartition source).blockCard (selectedRepresentative source) =
      ∑ edge ∈ directionSurvivors data star anchor (doubled source),
        data.sourceEdgeIndex edge.1 := by
  unfold finePartition
  rw [NonTrivalentValencyFourKZero.PrescribedPairing.withSelectedBlock.blockCard_representative]
  exact selectedSheets_card source

theorem finePartition_rel_or_singleton (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel anchor.1 sheet) :
    (finePartition source).Rel (selectedRepresentative source) sheet ∨
      (finePartition source).block sheet = {sheet} := by
  classical
  by_cases hSelected : sheet ∈ selectedSheets source
  · left
    rw [← (finePartition source).mem_block_iff, finePartition_selected_block]
    exact hSelected
  · right
    unfold finePartition
    exact NonTrivalentValencyFourKZero.PrescribedPairing.withSelectedBlock.block_of_not_mem_of_rel
      _ _ _ _ _ _ hSelected hWall

/-- The counting identity for the new endpoint inside `A`. -/
theorem finePartition_blockCountWithin_add_card :
    (finePartition source).blockCountWithin (data.vertexPartition wall) anchor.1 +
        (selectedSheets source).card =
      (data.vertexPartition wall).blockCard anchor.1 + 1 := by
  have hCount := NonTrivalentValencyFourKZero.PrescribedPairing.blockCountWithin_add_blockCard_eq
    (finePartition source) (data.vertexPartition wall) anchor.1
    (selectedRepresentative source)
    ((data.vertexPartition wall).mem_block_iff _ _ |>.mp
      (selectedSheets_subset_wall source (selectedRepresentative_mem source)))
    (finePartition_refines source)
    (finePartition_rel_or_singleton source)
  rw [finePartition_selected_card source, ← selectedSheets_card source] at hCount
  exact hCount

/-- Every surviving class of the doubled direction lies inside the new bridge
class, and every other sheet of `A` is a singleton there: this is the exterior
compatibility of the resolution on its divalent side. -/
theorem doubledEdge_refines_finePartition (hNoGlue : DanglingEdgeNoGlue data) :
    (data.edgePartition (doubledEdge source)).Refines (finePartition source) := by
  classical
  apply NonTrivalentValencyFourKZero.PrescribedPairing.refines_withSelectedBlock_of_one_class
    (active := selectedSheets source)
  · exact doubledEdge_refines source
  · exact Finset.Subset.refl _
  · intro first hFirst second hRel
    rcases Finset.mem_union.mp hFirst with hMem | hMem
    · refine Finset.mem_union_left _ ?_
      rw [SheetPartition.mem_block_iff] at hMem ⊢
      exact hMem.trans hRel
    · refine Finset.mem_union_right _ ?_
      rw [SheetPartition.mem_block_iff] at hMem ⊢
      exact hMem.trans hRel
  · intro sheet hWall
    rcases mem_survivorBlock_or_singleton (star := star) hNoGlue (doubled source)
      sheet hWall with ⟨edge, hEdge, hRel⟩ | hSingleton
    · left
      rw [directionSurvivors_doubled_eq_pair, Finset.mem_insert,
        Finset.mem_singleton] at hEdge
      rcases hEdge with rfl | rfl
      · exact Finset.mem_union_left _
          ((SheetPartition.mem_block_iff _ _ _).mpr hRel)
      · exact Finset.mem_union_right _
          ((SheetPartition.mem_block_iff _ _ _).mpr hRel)
    · exact Or.inr hSingleton

/-! ## 6.  The local resolution at the anchor -/

/-- The prescribed local resolution of case `{v3-nd4}`, base tree `T_2`: the
divalent side `u` carries the refined partition and the trivalent side `v`
keeps the whole old wall block, so `|A_v| = |A|`. -/
noncomputable def selectedResolution : LocalResolution degree :=
  fineResolution (data.vertexPartition wall) (finePartition source)
    (finePartition_refines source)

@[simp] theorem selectedResolution_left :
    (selectedResolution source).left = finePartition source := rfl

@[simp] theorem selectedResolution_right :
    (selectedResolution source).right = data.vertexPartition wall := rfl

@[simp] theorem selectedResolution_newEdge :
    (selectedResolution source).newEdge = finePartition source := rfl

theorem selectedResolution_contracts :
    (selectedResolution source).ContractsTo (data.vertexPartition wall) :=
  fineResolution_contracts _ _ _

/-! ## 7.  The outgoing base tree `T_2` and its occurrence assignment -/

/-- The occurrence assignment of base tree `T_2`: the divalent end `u` of the
new edge keeps the doubled direction, the trivalent end `v` keeps the other
two.  This is the *only* assignment the existence route needs; the paper's
Type I and Type II assignments put a simple direction on `u` and each require
one of the two complementary index conditions. -/
noncomputable def rightAssignment : target.edges → Bool :=
  fun edge ↦ decide (edge ≠ doubledEdge source)

@[simp] theorem rightAssignment_doubled :
    rightAssignment source (doubledEdge source) = false := by
  simp [rightAssignment]

theorem rightAssignment_eq_false_iff (edge : target.edges) :
    rightAssignment source edge = false ↔ edge = doubledEdge source := by
  simp [rightAssignment]

theorem rightAssignment_of_ne {edge : target.edges}
    (hEdge : edge ≠ doubledEdge source) : rightAssignment source edge = true := by
  simp [rightAssignment, hEdge]

/-- The single old occurrence at the divalent end `u`. -/
noncomputable def leftEdges : List target.edges := [doubledEdge source]

/-- The two old occurrences at the trivalent end `v`. -/
noncomputable def rightEdges : List target.edges :=
  [directionEdge star (firstSimple source), directionEdge star (secondSimple source)]

theorem directionEdge_firstSimple_ne :
    directionEdge star (firstSimple source) ≠ doubledEdge source := by
  intro hEq
  exact firstSimple_ne source (directionEdge_injective star hEq)

theorem directionEdge_secondSimple_ne :
    directionEdge star (secondSimple source) ≠ doubledEdge source := by
  intro hEq
  exact secondSimple_ne source (directionEdge_injective star hEq)

theorem directionEdge_simple_ne :
    directionEdge star (firstSimple source) ≠ directionEdge star (secondSimple source) := by
  intro hEq
  exact firstSimple_ne_secondSimple source (directionEdge_injective star hEq)

theorem incidentEdges_eq_triple :
    GluingDatum.incidentEdges wall =
      {doubledEdge source, directionEdge star (firstSimple source),
        directionEdge star (secondSimple source)} := by
  classical
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro edge hEdge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
    rcases hEdge with rfl | rfl | rfl
    · exact doubledEdge_mem_incidentEdges source
    · exact directionEdge_mem_incidentEdges star _
    · exact directionEdge_mem_incidentEdges star _
  · rw [star.card_incidentEdges]
    rw [Finset.card_insert_of_notMem (by
        simp [Ne.symm (directionEdge_firstSimple_ne source),
          Ne.symm (directionEdge_secondSimple_ne source)]),
      Finset.card_insert_of_notMem (by simp [directionEdge_simple_ne source]),
      Finset.card_singleton]

theorem wallEdgesAssigned_false :
    wallEdgesAssigned target wall (rightAssignment source) false =
      {doubledEdge source} := by
  classical
  ext edge
  rw [mem_wallEdgesAssigned, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hSide⟩
    exact (rightAssignment_eq_false_iff source edge).mp hSide
  · rintro rfl
    refine ⟨?_, rightAssignment_doubled source⟩
    exact (GluingContraction.mem_incidentEdges_iff wall _).mp
      (doubledEdge_mem_incidentEdges source)

theorem wallEdgesAssigned_true :
    wallEdgesAssigned target wall (rightAssignment source) true =
      {directionEdge star (firstSimple source),
        directionEdge star (secondSimple source)} := by
  classical
  ext edge
  rw [mem_wallEdgesAssigned, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hIncident, hSide⟩
    have hMem : edge ∈ GluingDatum.incidentEdges wall :=
      (GluingContraction.mem_incidentEdges_iff wall edge).mpr hIncident
    rw [incidentEdges_eq_triple source] at hMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hMem
    rcases hMem with rfl | hMem | hMem
    · rw [rightAssignment_doubled source] at hSide
      exact absurd hSide (by simp)
    · exact Or.inl hMem
    · exact Or.inr hMem
  · intro hEdge
    rcases hEdge with rfl | rfl
    · exact ⟨(GluingContraction.mem_incidentEdges_iff wall _).mp
        (directionEdge_mem_incidentEdges star _),
        rightAssignment_of_ne source (directionEdge_firstSimple_ne source)⟩
    · exact ⟨(GluingContraction.mem_incidentEdges_iff wall _).mp
        (directionEdge_mem_incidentEdges star _),
        rightAssignment_of_ne source (directionEdge_secondSimple_ne source)⟩

theorem leftEdges_eq :
    ((leftEdges source : List target.edges) : Multiset target.edges) =
      (wallEdgesAssigned target wall (rightAssignment source) false).val := by
  rw [wallEdgesAssigned_false source]
  rfl

theorem rightEdges_eq :
    ((rightEdges source : List target.edges) : Multiset target.edges) =
      (wallEdgesAssigned target wall (rightAssignment source) true).val := by
  classical
  rw [wallEdgesAssigned_true source,
    Finset.insert_val_of_notMem (by simp [directionEdge_simple_ne source])]
  rfl

/-! ## 8.  Both endpoint inequalities at the anchor -/

private theorem blockCountWithin_congr (fine coarse : SheetPartition degree)
    {first second : Fin degree} (hRel : coarse.Rel first second) :
    fine.blockCountWithin coarse first = fine.blockCountWithin coarse second := by
  unfold SheetPartition.blockCountWithin
  rw [coarse.block_eq_of_rel hRel]

private theorem blockCard_congr' (partition : SheetPartition degree)
    {first second : Fin degree} (hRel : partition.Rel first second) :
    partition.blockCard first = partition.blockCard second := by
  unfold SheetPartition.blockCard
  rw [partition.block_eq_of_rel hRel]

/-- The divalent endpoint `u` needs no source input: it carries two
occurrences. -/
theorem selected_riemannHurwitz_left (block : Fin degree) :
    LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
      (selectedResolution source).left
      ((selectedResolution source).newEdge ::
        (leftEdges source).map data.edgePartition) block := by
  simpa [leftEdges] using riemannHurwitzAtBlock_divalent (data.vertexPartition wall)
    (selectedResolution source).left (selectedResolution source).newEdge
    (data.edgePartition (doubledEdge source)) block

/-- The trivalent endpoint `v` keeps the whole old block `|A_v| = |A|`, and its
Riemann--Hurwitz inequality holds with *equality*: this is precisely where the
source's identity `(boxplus)` `k_2 + k_3 + k_4 + k_5 = 2|A| + 1` is used. -/
theorem selected_riemannHurwitz_right (hNoGlue : DanglingEdgeNoGlue data)
    (block : Fin degree)
    (hBlock : (data.vertexPartition wall).Rel anchor.1 block) :
    LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
      (selectedResolution source).right
      ((selectedResolution source).newEdge ::
        (rightEdges source).map data.edgePartition) block := by
  classical
  have hCounts : ∀ sheet, (data.vertexPartition wall).Rel block sheet →
      (finePartition source).blockCountWithin (data.vertexPartition wall) sheet +
          (data.edgePartition (directionEdge star (firstSimple source))).blockCountWithin
            (data.vertexPartition wall) sheet +
          (data.edgePartition (directionEdge star (secondSimple source))).blockCountWithin
            (data.vertexPartition wall) sheet ≥
        (data.vertexPartition wall).blockCard sheet + 2 := by
    intro sheet hSheet
    have hWall : (data.vertexPartition wall).Rel anchor.1 sheet := hBlock.trans hSheet
    rw [blockCountWithin_congr _ _ hWall.symm, blockCountWithin_congr _ _ hWall.symm,
      blockCountWithin_congr _ _ hWall.symm, blockCard_congr' _ hWall.symm]
    have hFine := finePartition_blockCountWithin_add_card source
    have hCard := selectedSheets_card source
    have hFirst := simple_blockCountWithin_add_sum source hNoGlue (firstSimple source)
      (firstSimple_ne source)
    have hSecond := simple_blockCountWithin_add_sum source hNoGlue (secondSimple source)
      (secondSimple_ne source)
    have hTotal := sum_directionSurvivors_index source
    omega
  simpa [rightEdges] using
    riemannHurwitzAtBlock_trivalent_of_counts (data.vertexPartition wall)
      (selectedResolution source).right (selectedResolution source).newEdge
      (data.edgePartition (directionEdge star (firstSimple source)))
      (data.edgePartition (directionEdge star (secondSimple source))) block hCounts

/-- Exterior compatibility of the local resolution with every old occurrence
at the wall. -/
theorem selected_exterior (hNoGlue : DanglingEdgeNoGlue data) (edge : target.edges)
    (hIncident : (edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) :
    (data.edgePartition edge).Refines
      (if rightAssignment source edge then (selectedResolution source).right
        else (selectedResolution source).left) := by
  classical
  have hMem : edge ∈ GluingDatum.incidentEdges wall :=
    (GluingContraction.mem_incidentEdges_iff wall edge).mpr hIncident
  by_cases hEdge : edge = doubledEdge source
  · subst hEdge
    rw [rightAssignment_doubled source, ite_eq_right (by simp)]
    exact doubledEdge_refines_finePartition source hNoGlue
  · rw [rightAssignment_of_ne source hEdge, ite_eq_left rfl]
    exact edgePartition_refines_of_mem_incidentEdges data wall edge hMem

/-! ## 9.  The guarded background and the installed candidate -/

/-- The source geometry still required away from the distinguished anchor
class: exactly the guarded background resolutions of the other wall blocks.
No fine partition, no selected-block Riemann--Hurwitz receipt and no validity
of the outgoing datum is supplied here. -/
structure SubdivisionBackground where
  resolution : Fin degree → LocalResolution degree
  contracts : ∀ block, ¬(data.vertexPartition wall).Rel anchor.1 block →
    (resolution block).ContractsTo (data.vertexPartition wall)
  exterior : ∀ edge : target.edges,
    ((edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) →
    ∀ block, ¬(data.vertexPartition wall).Rel anchor.1 block →
      (data.edgePartition edge).Refines
        (if rightAssignment source edge then (resolution block).right
          else (resolution block).left)
  left_riemannHurwitz : ∀ block,
    (data.vertexPartition wall).repr block = block →
    ¬(data.vertexPartition wall).Rel anchor.1 block →
      LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
        (resolution block).left
        ((resolution block).newEdge ::
          (leftEdges source).map data.edgePartition) block
  right_riemannHurwitz : ∀ block,
    (data.vertexPartition wall).repr block = block →
    ¬(data.vertexPartition wall).Rel anchor.1 block →
      LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
        (resolution block).right
        ((resolution block).newEdge ::
          (rightEdges source).map data.edgePartition) block

namespace SubdivisionBackground

/-- Package the guarded receipts with the base tree `T_2` assignment. -/
noncomputable def background (geometry : SubdivisionBackground source) :
    GlobalM11Arbitrary.Background data wall anchor.1 where
  right := rightAssignment source
  resolution := geometry.resolution
  contracts := geometry.contracts
  exterior := geometry.exterior
  leftEdges := leftEdges source
  rightEdges := rightEdges source
  leftEdges_eq := leftEdges_eq source
  rightEdges_eq := rightEdges_eq source
  left_riemannHurwitz := geometry.left_riemannHurwitz
  right_riemannHurwitz := geometry.right_riemannHurwitz

end SubdivisionBackground

/-- The prescribed valency-three resolution installed into the guarded
background: an actual globally assembled candidate over the *unchanged*
incoming datum, since no branch gauge is needed. -/
noncomputable def candidate (geometry : SubdivisionBackground source)
    (hNoGlue : DanglingEdgeNoGlue data) :
    BalancedGlobal.Candidate target degree data wall := by
  apply (SubdivisionBackground.background source geometry).install
    (selectedResolution source) (selectedResolution_contracts source)
    (selected_exterior source hNoGlue)
  · intro block _ _
    exact selected_riemannHurwitz_left source block
  · intro block hRel _
    exact selected_riemannHurwitz_right source hNoGlue block hRel

/-- Incoming validity is the only validity input: there is no gauge to
transport it through. -/
theorem candidate_datum_valid (geometry : SubdivisionBackground source)
    (hNoGlue : DanglingEdgeNoGlue data) (hValid : data.Valid) :
    (candidate source geometry hNoGlue).datum.Valid :=
  (candidate source geometry hNoGlue).datum_valid hValid

theorem candidate_resolution_of_wall_rel (geometry : SubdivisionBackground source)
    (hNoGlue : DanglingEdgeNoGlue data) (block : Fin degree)
    (hRel : (data.vertexPartition wall).Rel anchor.1 block) :
    (candidate source geometry hNoGlue).resolution block =
      selectedResolution source := by
  unfold candidate SubdivisionBackground.background
    GlobalM11Arbitrary.Background.install
  exact LocalResolution.onBlock_of_rel _ _ _ _ _ hRel

theorem candidate_resolution_anchor (geometry : SubdivisionBackground source)
    (hNoGlue : DanglingEdgeNoGlue data) :
    (candidate source geometry hNoGlue).resolution anchor.1 =
      selectedResolution source :=
  candidate_resolution_of_wall_rel source geometry hNoGlue anchor.1 rfl

/-- Exact bridge size on the candidate's distinguished local resolution:
`k_1' = k_2 + k_5`, with no `-1`. -/
theorem candidate_newEdge_blockCard (geometry : SubdivisionBackground source)
    (hNoGlue : DanglingEdgeNoGlue data) :
    ((candidate source geometry hNoGlue).resolution anchor.1).newEdge.blockCard
        (selectedRepresentative source) =
      ∑ edge ∈ directionSurvivors data star anchor (doubled source),
        data.sourceEdgeIndex edge.1 := by
  rw [candidate_resolution_anchor source geometry hNoGlue, selectedResolution_newEdge]
  exact finePartition_selected_card source

/-- The same bridge size read in the outgoing gluing datum itself. -/
theorem candidate_newSourceEdge_index (geometry : SubdivisionBackground source)
    (hNoGlue : DanglingEdgeNoGlue data) :
    (candidate source geometry hNoGlue).datum.sourceEdgeIndex
        ((candidate source geometry hNoGlue).newSourceEdge
          (selectedRepresentative source)) =
      ∑ edge ∈ directionSurvivors data star anchor (doubled source),
        data.sourceEdgeIndex edge.1 := by
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge,
    LocalResolution.paste_newEdge_blockCard]
  have hRepr : (data.vertexPartition wall).Rel anchor.1
      ((data.vertexPartition wall).repr (selectedRepresentative source)) := by
    refine ?_
    exact ((data.vertexPartition wall).mem_block_iff _ _).mp
      (selectedSheets_subset_wall source (selectedRepresentative_mem source))
      |>.trans ((data.vertexPartition wall).rel_repr_right _)
  rw [candidate_resolution_of_wall_rel source geometry hNoGlue _ hRepr,
    selectedResolution_newEdge]
  exact finePartition_selected_card source

/-- The exact endpoint sizes: `|A_u| = k_2 + k_5` on the divalent side and
`|A_v| = |A|` on the trivalent side. -/
theorem candidate_endpoint_blockCard (geometry : SubdivisionBackground source)
    (hNoGlue : DanglingEdgeNoGlue data) (sideValue : Bool) :
    (if sideValue then
        ((candidate source geometry hNoGlue).resolution anchor.1).right
      else ((candidate source geometry hNoGlue).resolution anchor.1).left).blockCard
        (selectedRepresentative source) =
      if sideValue then (data.vertexPartition wall).blockCard anchor.1
      else ∑ edge ∈ directionSurvivors data star anchor (doubled source),
        data.sourceEdgeIndex edge.1 := by
  rw [candidate_resolution_anchor source geometry hNoGlue]
  cases sideValue
  · simpa using finePartition_selected_card source
  · simp only [selectedResolution_right]
    exact blockCard_congr' _
      (((data.vertexPartition wall).mem_block_iff _ _).mp
        (selectedSheets_subset_wall source (selectedRepresentative_mem source))).symm

/-! ## 10.  The background producer: at a trivalent wall the rigid blocks
need no census -/

/-- The resolution installed on every ordinary wall block: split along the
doubled direction on the divalent side, keep the whole block on the trivalent
side.  One global resolution serves every block. -/
noncomputable def ordinaryResolution : LocalResolution degree :=
  fineResolution (data.vertexPartition wall)
    (data.edgePartition (doubledEdge source)) (doubledEdge_refines source)

theorem incidentList_eq :
    ((doubledEdge source :: rightEdges source : List target.edges) :
        Multiset target.edges) =
      (GluingDatum.incidentEdges wall).val := by
  classical
  rw [incidentEdges_eq_triple source,
    Finset.insert_val_of_notMem (by
      simp [Ne.symm (directionEdge_firstSimple_ne source),
        Ne.symm (directionEdge_secondSimple_ne source)]),
    Finset.insert_val_of_notMem (by simp [directionEdge_simple_ne source])]
  rfl

/-- **The background producer.**  Incoming validity alone supplies every
guarded receipt: the divalent endpoint inequality is automatic, and the
trivalent endpoint inequality is literally the incoming datum's own
Riemann--Hurwitz condition at the wall, because the outgoing trivalent vertex
`v` sees the same three occurrence partitions as `w_0` did. -/
noncomputable def subdivisionBackground (hValid : data.Valid) :
    SubdivisionBackground source where
  resolution := fun _ ↦ ordinaryResolution source
  contracts := fun _ _ ↦ fineResolution_contracts _ _ _
  exterior := by
    intro edge hIncident block _
    classical
    have hMem : edge ∈ GluingDatum.incidentEdges wall :=
      (GluingContraction.mem_incidentEdges_iff wall edge).mpr hIncident
    by_cases hEdge : edge = doubledEdge source
    · subst hEdge
      rw [rightAssignment_doubled source, ite_eq_right (by simp)]
      exact SheetPartition.Refines.refl _
    · rw [rightAssignment_of_ne source hEdge, ite_eq_left rfl]
      exact edgePartition_refines_of_mem_incidentEdges data wall edge hMem
  left_riemannHurwitz := by
    intro block _ _
    simpa [leftEdges, ordinaryResolution, fineResolution] using
      riemannHurwitzAtBlock_divalent (data.vertexPartition wall)
        (ordinaryResolution source).left (ordinaryResolution source).newEdge
        (data.edgePartition (doubledEdge source)) block
  right_riemannHurwitz := by
    intro block hCanonical _
    have hList := (data.riemannHurwitzAtTargetVertex_iff_incidentList wall
      (doubledEdge source :: rightEdges source) (incidentList_eq source)).mp
        (hValid.2 wall)
    have hBlocks := (LocalResolution.riemannHurwitzAt_iff_forall_wallBlock
      (data.vertexPartition wall) (data.vertexPartition wall)
      ((doubledEdge source :: rightEdges source).map data.edgePartition)).mp
        hList block hCanonical
    simpa [ordinaryResolution, fineResolution] using hBlocks

/-- Non-vacuity of the guarded background: it is inhabited for every valid
incoming datum, with no census, no target-direction injectivity receipt and no
`nd <= 3` bound away from the anchor.  (There is no degree-one witness: a
`ThreeBranchAnchor` forces `2|A| + 1 >= 4`, hence `|A| >= 2`.) -/
theorem nonempty_subdivisionBackground (hValid : data.Valid) :
    Nonempty (SubdivisionBackground source) :=
  ⟨subdivisionBackground source hValid⟩

/-- The valency-three candidate itself, with **no** background hypothesis. -/
noncomputable def validCandidate (hNoGlue : DanglingEdgeNoGlue data)
    (hValid : data.Valid) : BalancedGlobal.Candidate target degree data wall :=
  candidate source (subdivisionBackground source hValid) hNoGlue

theorem validCandidate_datum_valid (hNoGlue : DanglingEdgeNoGlue data)
    (hValid : data.Valid) :
    (validCandidate source hNoGlue hValid).datum.Valid :=
  candidate_datum_valid source _ hNoGlue hValid

theorem validCandidate_newEdge_blockCard (hNoGlue : DanglingEdgeNoGlue data)
    (hValid : data.Valid) :
    ((validCandidate source hNoGlue hValid).resolution anchor.1).newEdge.blockCard
        (selectedRepresentative source) =
      ∑ edge ∈ directionSurvivors data star anchor (doubled source),
        data.sourceEdgeIndex edge.1 :=
  candidate_newEdge_blockCard source _ hNoGlue

theorem validCandidate_endpoint_blockCard (hNoGlue : DanglingEdgeNoGlue data)
    (hValid : data.Valid) (sideValue : Bool) :
    (if sideValue then
        ((validCandidate source hNoGlue hValid).resolution anchor.1).right
      else ((validCandidate source hNoGlue hValid).resolution anchor.1).left).blockCard
        (selectedRepresentative source) =
      if sideValue then (data.vertexPartition wall).blockCard anchor.1
      else ∑ edge ∈ directionSurvivors data star anchor (doubled source),
        data.sourceEdgeIndex edge.1 :=
  candidate_endpoint_blockCard source _ hNoGlue sideValue

end Prescribed

/-! ## 11.  The incoming-cover form

The shape of `NonTrivalentUniqueFourValent.exists_valid_candidate_of_single_row`
at valency three.  Everything except `hNd` is supplied by the incoming
full-dimensional cover and its contraction forest; `hNd` (the anchor's
surviving valency is four) stays an explicit hypothesis, exactly as in the
valency-four uniqueness argument (`NonTrivalentUniqueFourValent`). -/

section Incoming

open GraphContraction GluingContraction ContractionFibre ContractionRamification
open FullDimensionalSource WallDegeneration

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- From an actual incoming full-dimensional cover, its contraction forest and
an anchor of surviving valency four above a trivalent wall: the prescribed
valency-three candidate exists, its outgoing datum is valid, and its bridge
and endpoint sizes are the exact source values `k_2 + k_5` and `|A|`.  No
background, census or ramification receipt is supplied. -/
theorem exists_valid_candidate_of_contraction
    (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (anchorBlock : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne)
      (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩
        anchorBlock) = 4) :
    ∃ (source : ThreeBranchAnchor (contractDatum data hc hab hOne) star anchorBlock)
      (hNoGlue : DanglingEdgeNoGlue (contractDatum data hc hab hOne))
      (hValid : (contractDatum data hc hab hOne).Valid),
      (Prescribed.validCandidate source hNoGlue hValid).datum.Valid ∧
      ((Prescribed.validCandidate source hNoGlue hValid).resolution
          anchorBlock.1).newEdge.blockCard
            (Prescribed.selectedRepresentative source) =
        ∑ edge ∈ directionSurvivors (contractDatum data hc hab hOne) star
            anchorBlock (Prescribed.doubled source),
          (contractDatum data hc hab hOne).sourceEdgeIndex edge.1 ∧
      ∀ sideValue : Bool,
        (if sideValue then
            ((Prescribed.validCandidate source hNoGlue hValid).resolution
              anchorBlock.1).right
          else ((Prescribed.validCandidate source hNoGlue hValid).resolution
            anchorBlock.1).left).blockCard
              (Prescribed.selectedRepresentative source) =
          if sideValue then
            ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
              anchorBlock.1
          else ∑ edge ∈ directionSurvivors (contractDatum data hc hab hOne) star
              anchorBlock (Prescribed.doubled source),
            (contractDatum data hc hab hOne).sourceEdgeIndex edge.1 := by
  refine ⟨NonTrivalentValencyThreeRigidity.threeBranchAnchor data fd hc hab hOne
      hForest hCompat star anchorBlock hNd,
    danglingEdgeNoGlue_contractDatum data hCompat.2 fd.danglingEdgeNoGlue,
    valid_contractDatum data hc hab hOne hForest fd.valid, ?_, ?_, ?_⟩
  · exact Prescribed.validCandidate_datum_valid _ _ _
  · exact Prescribed.validCandidate_newEdge_blockCard _ _ _
  · exact Prescribed.validCandidate_endpoint_blockCard _ _ _

end Incoming

end DraismaVargas.LocalCases.NonTrivalentValencyThreeCandidate
