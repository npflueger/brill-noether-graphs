import DraismaVargas.LocalCases.BlockPreservingBranchSwap
import DraismaVargas.LocalCases.GlobalM11Arbitrary
import DraismaVargas.LocalCases.NonTrivalentWallSetup
import DraismaVargas.LocalCases.SheetRelabelStable

/-!
# Part II, valency four: source classifier for the K = 0 construction

This is the first existence-only construction in Vargas, Part II
(arXiv:2609.09109), Section 5.2 (Case {v4-nd4}).  It
does not count the resolutions.  For a prescribed `2+2` resolution of the
four target branches, the smaller side has total index at most `|A|+1` by
identity `(square)`.  A block-preserving branch swap puts its two actual
source classes in one-sheet intersection.  Their union is then the endpoint
and bridge class of the `K=0` resolution.

`FourBranchAnchor` is the local classifier input: it says that all
four target directions occur at the distinguished source vertex and that no
direction contains two distinct surviving source occurrences there.  It does
not contain a fine partition, a local-resolution receipt, or an RH receipt.
From that actual source classifier, this module derives the labelled index
identity `(square)`, constructs the block-preserving branch gauge and literal
fine endpoint, proves both selected-block RH inequalities, and installs the
result as a globally valid candidate over arbitrary guarded background blocks.
Its final theorem gives the exact new-edge dilation index in the outgoing
gluing datum itself.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyFourKZero

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases.BlockPreservingBranchSwap
open DraismaVargas.LocalCases.GlobalM11Arbitrary
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionCoarseFine
open W4Assembly W4StableSource

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}

/-! ## The honest four-branch source classifier -/

/-- The literal source fact in case `{v4-nd4}`: every target-star direction
has a surviving occurrence at `A`, and the target direction is injective on
the surviving neighbourhood of `A`. -/
structure FourBranchAnchor (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (anchor : WallBlock data wall) : Prop where
  active_all : activeLabels data star anchor = Finset.univ
  target_injective : NonDanglingStarInjective data star anchor

namespace FourBranchAnchor

variable {star : W4TargetPairings.FourStar target wall}
  {anchor : WallBlock data wall}

theorem label_active (source : FourBranchAnchor data star anchor)
    (label : Fin 4) : label ∈ activeLabels data star anchor := by
  rw [source.active_all]
  simp

/-- An actual sheet in the unique surviving class over one star direction. -/
noncomputable def sheet (source : FourBranchAnchor data star anchor)
    (label : Fin 4) : Fin degree :=
  activeWitnessSheet data star anchor label (source.label_active label)

theorem sheet_wall_rel (source : FourBranchAnchor data star anchor)
    (label : Fin 4) :
    (data.vertexPartition wall).Rel anchor.1 (source.sheet label) :=
  activeSheet_rel data star anchor label (source.label_active label)

/-- The actual non-dangling occurrence selected on a star direction. -/
noncomputable def sourceEdge (source : FourBranchAnchor data star anchor)
    (label : Fin 4) : data.SourceEdge :=
  data.sourceEdge (star.edge label) (source.sheet label)

theorem sourceEdge_survives (source : FourBranchAnchor data star anchor)
    (label : Fin 4) : ¬ IsDangling data (source.sourceEdge label) :=
  activeSheet_survives data star anchor label (source.label_active label)

/-- The dilation index of the actual class on a labelled target branch. -/
noncomputable def index (source : FourBranchAnchor data star anchor)
    (label : Fin 4) : ℕ :=
  (data.edgePartition (star.edge label)).blockCard (source.sheet label)

theorem index_pos (source : FourBranchAnchor data star anchor)
    (label : Fin 4) : 0 < source.index label :=
  (data.edgePartition (star.edge label)).blockCard_pos _

/-- The classifier really has non-dangling valency four. -/
theorem nonDanglingValency_eq_four
    (source : FourBranchAnchor data star anchor) :
    nonDanglingValency data (WallBlock.sourceVertex data wall anchor) = 4 := by
  calc
    nonDanglingValency data (WallBlock.sourceVertex data wall anchor) =
        Fintype.card (NonDanglingIncidentEdge data wall anchor) :=
      (card_nonDanglingIncidentEdge_eq_nonDanglingValency data wall anchor).symm
    _ = Fintype.card {label // label ∈ activeLabels data star anchor} :=
      Fintype.card_congr
        (activeLabelEquivNonDanglingIncidentEdge star anchor
          source.target_injective)
    _ = (activeLabels data star anchor).card := Fintype.card_coe _
    _ = 4 := by rw [source.active_all]; decide +kernel

/-- The sum over the four named branch classes is the literal survivor sum
in `StableLocalProperties.localRamification_eq_nonDangling_form`. -/
theorem sum_index_eq_survivor_sum
    (source : FourBranchAnchor data star anchor) :
    (∑ label : Fin 4, (source.index label : ℤ)) =
      ∑ edge ∈ (Finset.univ :
          Finset (IncidentSourceEdge data
            (WallBlock.sourceVertex data wall anchor))).filter
            (fun edge ↦ ¬ IsDangling data edge.1),
        (data.sourceEdgeIndex edge.1 : ℤ) := by
  classical
  let surviving := {edge : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall anchor) // ¬ IsDangling data edge.1}
  let fullActive : Fin 4 ≃ {label // label ∈ activeLabels data star anchor} := {
    toFun := fun label ↦ ⟨label, source.label_active label⟩
    invFun := fun label ↦ label.1
    left_inv := fun _ ↦ rfl
    right_inv := fun label ↦ Subtype.ext rfl }
  let asSurviving : NonDanglingIncidentEdge data wall anchor ≃ surviving := {
    toFun := fun edge ↦ ⟨⟨edge.1, edge.2.2⟩, edge.2.1⟩
    invFun := fun edge ↦ ⟨edge.1.1, edge.2, edge.1.2⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }
  let equivalence : Fin 4 ≃ surviving :=
    fullActive.trans
      ((activeLabelEquivNonDanglingIncidentEdge star anchor
        source.target_injective).symm.trans asSurviving)
  calc
    (∑ label : Fin 4, (source.index label : ℤ)) =
        ∑ edge : surviving, (data.sourceEdgeIndex edge.1.1 : ℤ) := by
      apply Fintype.sum_equiv equivalence
      intro label
      change ((data.edgePartition (star.edge label)).blockCard
          (source.sheet label) : ℤ) = _
      rw [← GluingDatum.sourceEdgeIndex_sourceEdge data
        (star.edge label) (source.sheet label)]
      congr 2
      apply source.target_injective.unique label
      · exact WallBlock.ofSourceEdge_eq_of_rel data star anchor label
          (source.sheet label) (source.sheet_wall_rel label)
      · exact ((incident_wallBlock_sourceVertex_iff data anchor
          (equivalence label).1.1).mp (equivalence label).1.2).2
      · rfl
      · exact (((activeLabelEquivNonDanglingIncidentEdge star anchor
          source.target_injective).symm (fullActive label)).edge_starLabel star).symm.trans
          (congrArg star.edge (congrArg Subtype.val
            ((activeLabelEquivNonDanglingIncidentEdge star anchor
              source.target_injective).apply_symm_apply (fullActive label))))
      · exact source.sourceEdge_survives label
      · exact (equivalence label).2
    _ = ∑ edge ∈ (Finset.univ :
          Finset (IncidentSourceEdge data
            (WallBlock.sourceVertex data wall anchor))).filter
            (fun edge ↦ ¬ IsDangling data edge.1),
        (data.sourceEdgeIndex edge.1 : ℤ) := by
      exact (Finset.sum_subtype
        (p := fun edge : IncidentSourceEdge data
          (WallBlock.sourceVertex data wall anchor) ↦
            ¬ IsDangling data edge.1)
        ((Finset.univ : Finset (IncidentSourceEdge data
          (WallBlock.sourceVertex data wall anchor))).filter
            (fun edge ↦ ¬ IsDangling data edge.1))
        (fun edge ↦ by simp)
        (fun edge ↦ (data.sourceEdgeIndex edge.1 : ℤ))).symm

/-- Identity `(square)` for the four actual labelled branch classes, derived
from the non-dangling excess theorem rather than supplied by the candidate
constructor. -/
theorem sum_index_eq_two_mul_add_two
    (source : FourBranchAnchor data star anchor)
    (hNoGlue : DanglingEdgeNoGlue data)
    (hRamification : data.localRamification wall anchor = 0) :
    (∑ label : Fin 4, (source.index label : ℤ)) =
      2 * ((data.vertexPartition wall).blockCard anchor.1 : ℤ) + 2 := by
  rw [source.sum_index_eq_survivor_sum]
  rw [NonTrivalentWallSetup.sum_sourceEdgeIndex_of_nonDanglingValency_four
    data hNoGlue wall anchor source.nonDanglingValency_eq_four,
    hRamification]
  omega

end FourBranchAnchor

/-! ## Orienting a prescribed pairing -/

namespace PrescribedPairing

variable {star : W4TargetPairings.FourStar target wall}
  {anchor : WallBlock data wall}

/-- The sum of the two actual source indices on one side of a prescribed
target pairing. -/
noncomputable def sideIndex (source : FourBranchAnchor data star anchor)
    (pairing : Fin 3) (sideValue : Bool) : ℕ :=
  ∑ label ∈ W4TargetPairings.Pairing.labelsOnSide pairing sideValue,
    source.index label

theorem sideIndex_false_add_true
    (source : FourBranchAnchor data star anchor) (pairing : Fin 3) :
    sideIndex source pairing false + sideIndex source pairing true =
      ∑ label : Fin 4, source.index label := by
  classical
  unfold sideIndex W4TargetPairings.Pairing.labelsOnSide
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin 4))
    (fun label ↦ W4TargetPairings.Pairing.labelRight pairing label = false)
    source.index]
  congr 2
  ext label
  cases hSide : W4TargetPairings.Pairing.labelRight pairing label <;>
    simp [hSide]

/-- Orient the prescribed pairing toward its smaller total source index. -/
noncomputable def smallerSide (source : FourBranchAnchor data star anchor)
    (pairing : Fin 3) : Bool :=
  decide (sideIndex source pairing true < sideIndex source pairing false)

theorem sideIndex_smaller_le_wall_add_one
    (source : FourBranchAnchor data star anchor)
    (pairing : Fin 3) (hNoGlue : DanglingEdgeNoGlue data)
    (hRamification : data.localRamification wall anchor = 0) :
    sideIndex source pairing (smallerSide source pairing) ≤
      (data.vertexPartition wall).blockCard anchor.1 + 1 := by
  have hTotal := sideIndex_false_add_true source pairing
  have hSquare : (∑ label : Fin 4, source.index label) =
      2 * (data.vertexPartition wall).blockCard anchor.1 + 2 := by
    exact_mod_cast source.sum_index_eq_two_mul_add_two hNoGlue hRamification
  rw [hSquare] at hTotal
  by_cases hSmaller : sideIndex source pairing true <
      sideIndex source pairing false
  · rw [show smallerSide source pairing = true by
      simp [smallerSide, hSmaller]]
    omega
  · rw [show smallerSide source pairing = false by
      simp [smallerSide, hSmaller]]
    omega

/-- A canonical first label on either two-element side. -/
noncomputable def firstLabel (pairing : Fin 3) (sideValue : Bool) : Fin 4 :=
  Classical.choose (Finset.card_pos.mp (by
    rw [W4TargetPairings.Pairing.card_labelsOnSide]
    omega : 0 < (W4TargetPairings.Pairing.labelsOnSide pairing sideValue).card))

theorem firstLabel_mem (pairing : Fin 3) (sideValue : Bool) :
    firstLabel pairing sideValue ∈
      W4TargetPairings.Pairing.labelsOnSide pairing sideValue :=
  Classical.choose_spec (Finset.card_pos.mp (by
    rw [W4TargetPairings.Pairing.card_labelsOnSide]
    omega : 0 < (W4TargetPairings.Pairing.labelsOnSide pairing sideValue).card))

/-- The other label on the same side of the prescribed pairing. -/
noncomputable def secondLabel (pairing : Fin 3) (sideValue : Bool) : Fin 4 :=
  Classical.choose (Finset.exists_mem_ne (by
    rw [W4TargetPairings.Pairing.card_labelsOnSide]
    omega : 1 < (W4TargetPairings.Pairing.labelsOnSide pairing sideValue).card)
    (firstLabel pairing sideValue))

theorem secondLabel_mem (pairing : Fin 3) (sideValue : Bool) :
    secondLabel pairing sideValue ∈
      W4TargetPairings.Pairing.labelsOnSide pairing sideValue :=
  (Classical.choose_spec (Finset.exists_mem_ne (by
    rw [W4TargetPairings.Pairing.card_labelsOnSide]
    omega : 1 < (W4TargetPairings.Pairing.labelsOnSide pairing sideValue).card)
    (firstLabel pairing sideValue))).1

theorem firstLabel_ne_secondLabel (pairing : Fin 3) (sideValue : Bool) :
    firstLabel pairing sideValue ≠ secondLabel pairing sideValue :=
  (Classical.choose_spec (Finset.exists_mem_ne (by
    rw [W4TargetPairings.Pairing.card_labelsOnSide]
    omega : 1 < (W4TargetPairings.Pairing.labelsOnSide pairing sideValue).card)
    (firstLabel pairing sideValue))).2.symm

theorem labelsOnSide_eq_pair (pairing : Fin 3) (sideValue : Bool) :
    W4TargetPairings.Pairing.labelsOnSide pairing sideValue =
      {firstLabel pairing sideValue, secondLabel pairing sideValue} := by
  apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro label hLabel
    simp only [Finset.mem_insert, Finset.mem_singleton] at hLabel
    rcases hLabel with rfl | rfl
    · exact firstLabel_mem pairing sideValue
    · exact secondLabel_mem pairing sideValue
  · rw [W4TargetPairings.Pairing.card_labelsOnSide]
    simp [firstLabel_ne_secondLabel]

theorem sideIndex_eq_add (source : FourBranchAnchor data star anchor)
    (pairing : Fin 3) (sideValue : Bool) :
    sideIndex source pairing sideValue =
      source.index (firstLabel pairing sideValue) +
        source.index (secondLabel pairing sideValue) := by
  rw [sideIndex, labelsOnSide_eq_pair]
  simp [firstLabel_ne_secondLabel]

/-- The actual edge-partition block belonging to one surviving labelled
source occurrence. -/
noncomputable def branchBlock (source : FourBranchAnchor data star anchor)
    (label : Fin 4) : Finset (Fin degree) :=
  (data.edgePartition (star.edge label)).block (source.sheet label)

theorem branchBlock_card (source : FourBranchAnchor data star anchor)
    (label : Fin 4) :
    (branchBlock source label).card = source.index label := rfl

theorem branchBlock_subset_wall
    (source : FourBranchAnchor data star anchor) (label : Fin 4) :
    branchBlock source label ⊆ (data.vertexPartition wall).block anchor.1 := by
  intro sheet hSheet
  have hEdge := ((data.edgePartition (star.edge label)).mem_block_iff _ _).mp hSheet
  have hWall := (star.edgePartition_refines_wall data label).rel hEdge
  exact ((data.vertexPartition wall).mem_block_iff _ _).mpr
    ((source.sheet_wall_rel label).trans hWall)

/-- Inside the distinguished wall block, a labelled target branch consists
of its unique surviving class and singleton dangling classes.  This is
derived from neighbourhood injectivity and dangling-no-glue. -/
theorem mem_branchBlock_or_block_singleton
    (source : FourBranchAnchor data star anchor)
    (hNoGlue : DanglingEdgeNoGlue data) (label : Fin 4)
    (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel anchor.1 sheet) :
    sheet ∈ branchBlock source label ∨
      (data.edgePartition (star.edge label)).block sheet = {sheet} := by
  by_cases hDangling : IsDangling data
      (data.sourceEdge (star.edge label) sheet)
  · right
    apply (data.edgePartition (star.edge label)).block_eq_singleton_of_blockCard_eq_one
    rw [← data.sourceEdgeIndex_sourceEdge]
    exact hNoGlue _ hDangling
  · left
    have hEqual := source.target_injective.unique label
      (source.sourceEdge label) (data.sourceEdge (star.edge label) sheet)
      (WallBlock.ofSourceEdge_eq_of_rel data star anchor label
        (source.sheet label) (source.sheet_wall_rel label))
      (WallBlock.ofSourceEdge_eq_of_rel data star anchor label sheet hWall)
      rfl rfl (source.sourceEdge_survives label) hDangling
    have hRepresentative := congrArg
      (fun edge : data.SourceEdge ↦ edge.1.2) hEqual
    exact ((data.edgePartition (star.edge label)).mem_block_iff _ _).mpr
      hRepresentative

/-- The finite gauge promised by the smaller-side inequality.  It acts only
inside the distinguished wall block and makes the two actual branch classes
meet in exactly one sheet. -/
theorem exists_overlap_gauge
    (source : FourBranchAnchor data star anchor) (pairing : Fin 3)
    (hNoGlue : DanglingEdgeNoGlue data)
    (hRamification : data.localRamification wall anchor = 0) :
    ∃ permutation : Equiv.Perm (Fin degree),
      (∀ sheet ∈ (data.vertexPartition wall).block anchor.1,
        permutation sheet ∈ (data.vertexPartition wall).block anchor.1) ∧
      (∀ sheet, sheet ∉ (data.vertexPartition wall).block anchor.1 →
        permutation sheet = sheet) ∧
      (branchBlock source
          (firstLabel pairing (smallerSide source pairing)) ∩
        (branchBlock source
          (secondLabel pairing (smallerSide source pairing))).image
            permutation).card = 1 := by
  let sideValue := smallerSide source pairing
  apply exists_perm_image_inter_card_one
  · exact branchBlock_subset_wall source _
  · exact branchBlock_subset_wall source _
  · simpa [branchBlock_card] using source.index_pos (firstLabel pairing sideValue)
  · simpa [branchBlock_card] using source.index_pos (secondLabel pairing sideValue)
  · rw [branchBlock_card, branchBlock_card, ← sideIndex_eq_add]
    exact sideIndex_smaller_le_wall_add_one source pairing hNoGlue hRamification

section Gauge

variable (source : FourBranchAnchor data star anchor) (pairing : Fin 3)
  (hNoGlue : DanglingEdgeNoGlue data)
  (hRamification : data.localRamification wall anchor = 0)

/-- The chosen block-preserving permutation for the prescribed pairing. -/
noncomputable def permutation : Equiv.Perm (Fin degree) :=
  Classical.choose (exists_overlap_gauge source pairing hNoGlue hRamification)

theorem permutation_inside (sheet : Fin degree)
    (hSheet : sheet ∈ (data.vertexPartition wall).block anchor.1) :
    permutation source pairing hNoGlue hRamification sheet ∈
      (data.vertexPartition wall).block anchor.1 :=
  (Classical.choose_spec
    (exists_overlap_gauge source pairing hNoGlue hRamification)).1 sheet hSheet

theorem permutation_outside (sheet : Fin degree)
    (hSheet : sheet ∉ (data.vertexPartition wall).block anchor.1) :
    permutation source pairing hNoGlue hRamification sheet = sheet :=
  (Classical.choose_spec
    (exists_overlap_gauge source pairing hNoGlue hRamification)).2.1 sheet hSheet

theorem permutation_overlap :
    (branchBlock source
          (firstLabel pairing (smallerSide source pairing)) ∩
        (branchBlock source
          (secondLabel pairing (smallerSide source pairing))).image
            (permutation source pairing hNoGlue hRamification)).card = 1 :=
  (Classical.choose_spec
    (exists_overlap_gauge source pairing hNoGlue hRamification)).2.2

/-- The literal `K=0` endpoint block: the two actual branch classes after
putting the second class in one-sheet overlap with the first. -/
noncomputable def selectedSheets : Finset (Fin degree) :=
  branchBlock source (firstLabel pairing (smallerSide source pairing)) ∪
    (branchBlock source
      (secondLabel pairing (smallerSide source pairing))).image
        (permutation source pairing hNoGlue hRamification)

theorem selectedSheets_subset_wall :
    selectedSheets source pairing hNoGlue hRamification ⊆
      (data.vertexPartition wall).block anchor.1 := by
  apply Finset.union_subset
  · exact branchBlock_subset_wall source _
  · intro sheet hSheet
    obtain ⟨original, hOriginal, rfl⟩ := Finset.mem_image.mp hSheet
    exact permutation_inside source pairing hNoGlue hRamification original
      (branchBlock_subset_wall source _ hOriginal)

theorem selectedSheets_card :
    (selectedSheets source pairing hNoGlue hRamification).card + 1 =
      sideIndex source pairing (smallerSide source pairing) := by
  classical
  have hUnion := Finset.card_union_add_card_inter
    (branchBlock source (firstLabel pairing (smallerSide source pairing)))
    ((branchBlock source
      (secondLabel pairing (smallerSide source pairing))).image
        (permutation source pairing hNoGlue hRamification))
  have hImage :
      ((branchBlock source
        (secondLabel pairing (smallerSide source pairing))).image
          (permutation source pairing hNoGlue hRamification)).card =
        (branchBlock source
          (secondLabel pairing (smallerSide source pairing))).card :=
    Finset.card_image_of_injective _
      (permutation source pairing hNoGlue hRamification).injective
  rw [permutation_overlap source pairing hNoGlue hRamification,
    hImage, branchBlock_card, branchBlock_card] at hUnion
  rw [selectedSheets, sideIndex_eq_add]
  omega

/-- A concrete sheet naming the selected endpoint block. -/
noncomputable def selectedRepresentative : Fin degree :=
  source.sheet (firstLabel pairing (smallerSide source pairing))

theorem selectedRepresentative_mem :
    selectedRepresentative source pairing ∈
      selectedSheets source pairing hNoGlue hRamification := by
  apply Finset.mem_union_left
  exact (data.edgePartition
    (star.edge (firstLabel pairing (smallerSide source pairing)))).self_mem_block _

end Gauge

/-! ## The literal fine endpoint partition -/

private def selectedBlockRepr (coarse : SheetPartition degree)
    (anchor representative : Fin degree) (selected : Finset (Fin degree))
    (sheet : Fin degree) : Fin degree :=
  if sheet ∈ selected then representative
  else if coarse.Rel anchor sheet then sheet
  else coarse.repr sheet

private theorem selectedBlockRepr_idem (coarse : SheetPartition degree)
    (anchor representative : Fin degree) (selected : Finset (Fin degree))
    (hRepresentative : representative ∈ selected)
    (hSelected : selected ⊆ coarse.block anchor) (sheet : Fin degree) :
    selectedBlockRepr coarse anchor representative selected
        (selectedBlockRepr coarse anchor representative selected sheet) =
      selectedBlockRepr coarse anchor representative selected sheet := by
  by_cases hSheet : sheet ∈ selected
  · simp [selectedBlockRepr, hSheet, hRepresentative]
  by_cases hWall : coarse.Rel anchor sheet
  · have hValue :
        selectedBlockRepr coarse anchor representative selected sheet = sheet := by
      rw [selectedBlockRepr, if_neg hSheet, if_pos hWall]
    rw [hValue]
    exact hValue
  · have hReprWall : ¬coarse.Rel anchor (coarse.repr sheet) := by
      intro h
      apply hWall
      unfold SheetPartition.Rel at h ⊢
      simpa only [coarse.repr_idem sheet] using h
    have hReprSelected : coarse.repr sheet ∉ selected := by
      intro h
      exact hReprWall ((coarse.mem_block_iff anchor _).mp (hSelected h))
    have hValue : selectedBlockRepr coarse anchor representative selected sheet =
        coarse.repr sheet := by
      rw [selectedBlockRepr, if_neg hSheet, if_neg hWall]
    rw [hValue]
    rw [selectedBlockRepr, if_neg hReprSelected, if_neg hReprWall,
      coarse.repr_idem]

/-- Refine one coarse block to a prescribed nonempty sub-block, leaving the
remaining sheets of that coarse block singleton and every other block
unchanged. -/
def withSelectedBlock (coarse : SheetPartition degree)
    (anchor representative : Fin degree) (selected : Finset (Fin degree))
    (hRepresentative : representative ∈ selected)
    (hSelected : selected ⊆ coarse.block anchor) : SheetPartition degree where
  repr := selectedBlockRepr coarse anchor representative selected
  repr_idem := selectedBlockRepr_idem coarse anchor representative selected
    hRepresentative hSelected

namespace withSelectedBlock

variable (coarse : SheetPartition degree) (anchor representative : Fin degree)
  (selected : Finset (Fin degree))
  (hRepresentative : representative ∈ selected)
  (hSelected : selected ⊆ coarse.block anchor)

@[simp] theorem repr_of_mem {sheet : Fin degree} (hSheet : sheet ∈ selected) :
    (withSelectedBlock coarse anchor representative selected hRepresentative
      hSelected).repr sheet = representative := by
  simp [withSelectedBlock, selectedBlockRepr, hSheet]

theorem repr_of_not_mem_of_rel {sheet : Fin degree} (hSheet : sheet ∉ selected)
    (hWall : coarse.Rel anchor sheet) :
    (withSelectedBlock coarse anchor representative selected hRepresentative
      hSelected).repr sheet = sheet := by
  change selectedBlockRepr coarse anchor representative selected sheet = sheet
  rw [selectedBlockRepr, if_neg hSheet, if_pos hWall]

theorem repr_of_not_rel {sheet : Fin degree} (hWall : ¬coarse.Rel anchor sheet) :
    (withSelectedBlock coarse anchor representative selected hRepresentative
      hSelected).repr sheet = coarse.repr sheet := by
  have hSheet : sheet ∉ selected := by
    intro h
    exact hWall ((coarse.mem_block_iff anchor _).mp (hSelected h))
  change selectedBlockRepr coarse anchor representative selected sheet = coarse.repr sheet
  rw [selectedBlockRepr, if_neg hSheet, if_neg hWall]

theorem repr_rel (sheet : Fin degree) :
    coarse.Rel
      ((withSelectedBlock coarse anchor representative selected hRepresentative
        hSelected).repr sheet) sheet := by
  by_cases hSheet : sheet ∈ selected
  · rw [repr_of_mem coarse anchor representative selected hRepresentative
      hSelected hSheet]
    exact ((coarse.mem_block_iff anchor representative).mp
      (hSelected hRepresentative)).symm.trans
        ((coarse.mem_block_iff anchor sheet).mp (hSelected hSheet))
  · by_cases hWall : coarse.Rel anchor sheet
    · rw [repr_of_not_mem_of_rel coarse anchor representative selected
        hRepresentative hSelected hSheet hWall]
      exact rfl
    · rw [repr_of_not_rel coarse anchor representative selected
        hRepresentative hSelected hWall]
      exact coarse.rel_repr_left sheet

theorem refines :
    (withSelectedBlock coarse anchor representative selected hRepresentative
      hSelected).Refines coarse := by
  intro first second hFine
  have hFirst := repr_rel coarse anchor representative selected hRepresentative
    hSelected first
  have hSecond := repr_rel coarse anchor representative selected hRepresentative
    hSelected second
  exact hFirst.symm.trans ((congrArg coarse.repr hFine).trans hSecond)

theorem block_representative :
    (withSelectedBlock coarse anchor representative selected hRepresentative
      hSelected).block representative = selected := by
  ext sheet
  rw [SheetPartition.mem_block_iff, SheetPartition.rel_iff,
    repr_of_mem coarse anchor representative selected hRepresentative hSelected
      hRepresentative]
  constructor
  · intro hRepr
    by_contra hSheet
    by_cases hWall : coarse.Rel anchor sheet
    · rw [repr_of_not_mem_of_rel coarse anchor representative selected
        hRepresentative hSelected hSheet hWall] at hRepr
      subst sheet
      exact hSheet hRepresentative
    · rw [repr_of_not_rel coarse anchor representative selected
        hRepresentative hSelected hWall] at hRepr
      apply hWall
      have hRepWall := (coarse.mem_block_iff anchor representative).mp
        (hSelected hRepresentative)
      unfold SheetPartition.Rel at hRepWall ⊢
      exact hRepWall.trans
        ((congrArg coarse.repr hRepr).trans (coarse.repr_idem sheet))
  · intro hSheet
    exact (repr_of_mem coarse anchor representative selected hRepresentative
      hSelected hSheet).symm

theorem block_of_not_mem_of_rel {sheet : Fin degree} (hSheet : sheet ∉ selected)
    (hWall : coarse.Rel anchor sheet) :
    (withSelectedBlock coarse anchor representative selected hRepresentative
      hSelected).block sheet = {sheet} := by
  ext other
  rw [SheetPartition.mem_block_iff, SheetPartition.rel_iff,
    repr_of_not_mem_of_rel coarse anchor representative selected hRepresentative
      hSelected hSheet hWall, Finset.mem_singleton]
  constructor
  · intro hRepr
    by_cases hOther : other ∈ selected
    · rw [repr_of_mem coarse anchor representative selected hRepresentative
        hSelected hOther] at hRepr
      subst sheet
      exact (hSheet hRepresentative).elim
    · have hOtherWall : coarse.Rel anchor other := by
        have hCoarse : coarse.Rel sheet other := by
          rw [hRepr]
          exact repr_rel coarse anchor representative selected hRepresentative
            hSelected other
        exact hWall.trans hCoarse
      rw [repr_of_not_mem_of_rel coarse anchor representative selected
        hRepresentative hSelected hOther hOtherWall] at hRepr
      exact hRepr.symm
  · rintro rfl
    rw [repr_of_not_mem_of_rel coarse anchor representative selected
      hRepresentative hSelected hSheet hWall]

theorem blockCard_of_not_mem_of_rel {sheet : Fin degree}
    (hSheet : sheet ∉ selected) (hWall : coarse.Rel anchor sheet) :
    (withSelectedBlock coarse anchor representative selected hRepresentative
      hSelected).blockCard sheet = 1 := by
  simp [SheetPartition.blockCard,
    block_of_not_mem_of_rel coarse anchor representative selected hRepresentative
      hSelected hSheet hWall]

theorem blockCard_representative :
    (withSelectedBlock coarse anchor representative selected hRepresentative
      hSelected).blockCard representative = selected.card := by
  simp [SheetPartition.blockCard,
    block_representative coarse anchor representative selected hRepresentative
      hSelected]

end withSelectedBlock

/-- A partition with one distinguished nonsingleton class and singleton
complement on the chosen coarse block refines the literal selected-block
endpoint whenever that distinguished class is selected. -/
theorem refines_withSelectedBlock_of_one_class
    (coarse edge : SheetPartition degree) (anchor representative : Fin degree)
    (selected active : Finset (Fin degree))
    (hRepresentative : representative ∈ selected)
    (hSelected : selected ⊆ coarse.block anchor)
    (hEdge : edge.Refines coarse) (hActive : active ⊆ selected)
    (hActiveClosed : ∀ first, first ∈ active → ∀ second,
      edge.Rel first second → second ∈ active)
    (hShape : ∀ sheet, coarse.Rel anchor sheet →
      sheet ∈ active ∨ edge.block sheet = {sheet}) :
    edge.Refines (withSelectedBlock coarse anchor representative selected
      hRepresentative hSelected) := by
  intro first second hTogether
  by_cases hFirstWall : coarse.Rel anchor first
  · have hSecondWall : coarse.Rel anchor second :=
      hFirstWall.trans (hEdge.rel hTogether)
    rcases hShape first hFirstWall with hFirstActive | hSingleton
    · have hFirstSelected := hActive hFirstActive
      have hSecondSelected := hActive (hActiveClosed first hFirstActive second hTogether)
      unfold SheetPartition.Rel
      rw [withSelectedBlock.repr_of_mem coarse anchor representative selected
        hRepresentative hSelected hFirstSelected,
        withSelectedBlock.repr_of_mem coarse anchor representative selected
          hRepresentative hSelected hSecondSelected]
    · have hSecondMem : second ∈ edge.block first :=
        (edge.mem_block_iff first second).mpr hTogether
      rw [hSingleton, Finset.mem_singleton] at hSecondMem
      subst second
      exact rfl
  · have hSecondWall : ¬coarse.Rel anchor second := by
      intro h
      exact hFirstWall (h.trans (hEdge.rel hTogether).symm)
    unfold SheetPartition.Rel
    rw [withSelectedBlock.repr_of_not_rel coarse anchor representative selected
      hRepresentative hSelected hFirstWall,
      withSelectedBlock.repr_of_not_rel coarse anchor representative selected
        hRepresentative hSelected hSecondWall]
    exact hEdge.rel hTogether

/-- Counting one distinguished fine block and singleton complement inside a
coarse block gives `#fine blocks + distinguished size = coarse size + 1`. -/
theorem blockCountWithin_add_blockCard_eq
    (fine coarse : SheetPartition degree) (anchor active : Fin degree)
    (hActiveWall : coarse.Rel anchor active) (hRefines : fine.Refines coarse)
    (hShape : ∀ sheet, coarse.Rel anchor sheet →
      fine.Rel active sheet ∨ fine.block sheet = {sheet}) :
    fine.blockCountWithin coarse anchor + fine.blockCard active =
      coarse.blockCard anchor + 1 := by
  classical
  let wallBlock := coarse.block anchor
  let activeBlock := fine.block active
  have hActiveSubset : activeBlock ⊆ wallBlock := by
    intro sheet hSheet
    exact (coarse.mem_block_iff anchor sheet).mpr
      (hActiveWall.trans (hRefines.rel
        ((fine.mem_block_iff active sheet).mp hSheet)))
  have hImage : wallBlock.image fine.repr =
      insert (fine.repr active) (wallBlock \ activeBlock) := by
    ext representative
    constructor
    · intro hRepresentative
      obtain ⟨sheet, hSheetWall, rfl⟩ := Finset.mem_image.mp hRepresentative
      by_cases hSheetActive : sheet ∈ activeBlock
      · apply Finset.mem_insert.mpr
        left
        exact ((fine.mem_block_iff active sheet).mp hSheetActive).symm
      · apply Finset.mem_insert.mpr
        right
        have hSingleton := (hShape sheet
          ((coarse.mem_block_iff anchor sheet).mp hSheetWall)).resolve_left
            (fun h ↦ hSheetActive ((fine.mem_block_iff active sheet).mpr h))
        have hReprEq : fine.repr sheet = sheet := by
          have hMem : fine.repr sheet ∈ fine.block sheet :=
            (fine.mem_block_iff sheet _).mpr (fine.rel_repr_right sheet)
          rwa [hSingleton, Finset.mem_singleton] at hMem
        rw [hReprEq]
        exact Finset.mem_sdiff.mpr ⟨hSheetWall, hSheetActive⟩
    · intro hRepresentative
      rcases Finset.mem_insert.mp hRepresentative with hRep | hOther
      · subst representative
        exact Finset.mem_image.mpr
          ⟨active, (coarse.mem_block_iff anchor active).mpr hActiveWall, rfl⟩
      · have hOther' := Finset.mem_sdiff.mp hOther
        have hSingleton := (hShape representative
          ((coarse.mem_block_iff anchor representative).mp hOther'.1)).resolve_left
            (fun h ↦ hOther'.2 ((fine.mem_block_iff active representative).mpr h))
        have hReprEq : fine.repr representative = representative := by
          have hMem : fine.repr representative ∈ fine.block representative :=
            (fine.mem_block_iff representative _).mpr
              (fine.rel_repr_right representative)
          rwa [hSingleton, Finset.mem_singleton] at hMem
        exact Finset.mem_image.mpr ⟨representative, hOther'.1, hReprEq⟩
  have hReprActive : fine.repr active ∈ activeBlock :=
    (fine.mem_block_iff active _).mpr (fine.rel_repr_right active)
  have hNotMem : fine.repr active ∉ wallBlock \ activeBlock := by
    simp [hReprActive]
  have hSdiffCard : (wallBlock \ activeBlock).card + activeBlock.card =
      wallBlock.card := by
    have hCardLe := Finset.card_le_card hActiveSubset
    rw [Finset.card_sdiff_of_subset hActiveSubset]
    omega
  unfold SheetPartition.blockCountWithin SheetPartition.blockCard
  change (wallBlock.image fine.repr).card + activeBlock.card =
    wallBlock.card + 1
  rw [hImage, Finset.card_insert_of_notMem hNotMem]
  omega

section FinePartition

variable (source : FourBranchAnchor data star anchor) (pairing : Fin 3)
  (hNoGlue : DanglingEdgeNoGlue data)
  (hRamification : data.localRamification wall anchor = 0)

/-- The `K=0` endpoint partition itself. -/
noncomputable def finePartition : SheetPartition degree :=
  withSelectedBlock (data.vertexPartition wall) anchor.1
    (selectedRepresentative source pairing)
    (selectedSheets source pairing hNoGlue hRamification)
    (selectedRepresentative_mem source pairing hNoGlue hRamification)
    (selectedSheets_subset_wall source pairing hNoGlue hRamification)

theorem finePartition_refines :
    (finePartition source pairing hNoGlue hRamification).Refines
      (data.vertexPartition wall) :=
  withSelectedBlock.refines _ _ _ _ _ _

theorem finePartition_selected_block :
    (finePartition source pairing hNoGlue hRamification).block
        (selectedRepresentative source pairing) =
      selectedSheets source pairing hNoGlue hRamification :=
  withSelectedBlock.block_representative _ _ _ _ _ _

theorem finePartition_selected_card :
    (finePartition source pairing hNoGlue hRamification).blockCard
        (selectedRepresentative source pairing) + 1 =
      sideIndex source pairing (smallerSide source pairing) := by
  unfold finePartition
  rw [withSelectedBlock.blockCard_representative]
  exact selectedSheets_card source pairing hNoGlue hRamification

end FinePartition

/-! ## The actual branch gauge -/

section BranchGauge

variable (source : FourBranchAnchor data star anchor) (pairing : Fin 3)
  (hNoGlue : DanglingEdgeNoGlue data)
  (hRamification : data.localRamification wall anchor = 0)

noncomputable def firstSelectedLabel : Fin 4 :=
  firstLabel pairing (smallerSide source pairing)

noncomputable def secondSelectedLabel : Fin 4 :=
  secondLabel pairing (smallerSide source pairing)

theorem firstSelectedLabel_ne_secondSelectedLabel :
    firstSelectedLabel source pairing ≠ secondSelectedLabel source pairing :=
  firstLabel_ne_secondLabel pairing (smallerSide source pairing)

theorem selectedEdge_incident (label : Fin 4) :
    ((star.edge label : target.V × target.V).1 = wall ∨
      (star.edge label : target.V × target.V).2 = wall) :=
  (GluingContraction.mem_incidentEdges_iff wall (star.edge label)).mp
    (star.edge_mem_incidentEdges label)

/-- The canonical branch relabelling: only the component behind the second
selected target occurrence receives the overlap permutation. -/
noncomputable def relabeling : data.SheetRelabeling :=
  branchSwapOfPerm data wall
    (TargetSeparation.farEndpoint wall
      (star.edge (secondSelectedLabel source pairing)))
    (TargetSeparation.farEndpoint_ne
      (selectedEdge_incident (star := star)
        (secondSelectedLabel source pairing)))
    (permutation source pairing hNoGlue hRamification)
    (rel_of_stabilizes_block (data.vertexPartition wall) anchor.1
      (permutation source pairing hNoGlue hRamification)
      (permutation_inside source pairing hNoGlue hRamification)
      (permutation_outside source pairing hNoGlue hRamification))

/-- The incoming datum after making the selected branch classes overlap. -/
noncomputable def gaugedData : GluingDatum target degree :=
  (relabeling source pairing hNoGlue hRamification).apply

theorem gaugedData_vertexPartition_wall :
    (gaugedData source pairing hNoGlue hRamification).vertexPartition wall =
      data.vertexPartition wall := by
  unfold gaugedData relabeling
  apply branchSwapOfPerm_vertexPartition_wall

theorem gaugedData_edgePartition_first
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    (gaugedData source pairing hNoGlue hRamification).edgePartition
        (star.edge (firstSelectedLabel source pairing)) =
      data.edgePartition (star.edge (firstSelectedLabel source pairing)) := by
  apply branchSwapOfPerm_edgePartition_of_fixed
  apply TargetSeparation.edgeMoved_eq_false hConnected hGenus
    (selectedEdge_incident (star := star) (secondSelectedLabel source pairing))
    (selectedEdge_incident (star := star) (firstSelectedLabel source pairing))
  intro hEqual
  exact (firstSelectedLabel_ne_secondSelectedLabel source pairing)
    (star.edge_injective hEqual).symm

theorem gaugedData_edgePartition_second :
    (gaugedData source pairing hNoGlue hRamification).edgePartition
        (star.edge (secondSelectedLabel source pairing)) =
      (data.edgePartition
        (star.edge (secondSelectedLabel source pairing))).relabel
          (permutation source pairing hNoGlue hRamification) := by
  apply branchSwapOfPerm_edgePartition_of_moved
  exact TargetSeparation.edgeMoved_self_eq_true
    (selectedEdge_incident (star := star) (secondSelectedLabel source pairing))

theorem gaugedData_edgePartition_other
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (label : Fin 4) (hOther : label ≠ secondSelectedLabel source pairing) :
    (gaugedData source pairing hNoGlue hRamification).edgePartition
        (star.edge label) = data.edgePartition (star.edge label) := by
  apply branchSwapOfPerm_edgePartition_of_fixed
  apply TargetSeparation.edgeMoved_eq_false hConnected hGenus
    (selectedEdge_incident (star := star) (secondSelectedLabel source pairing))
    (selectedEdge_incident (star := star) label)
  intro hEqual
  exact hOther (star.edge_injective hEqual).symm

theorem gaugedData_valid (hValid : data.Valid) :
    (gaugedData source pairing hNoGlue hRamification).Valid :=
  (relabeling source pairing hNoGlue hRamification).valid hValid

theorem first_edgePartition_refines_fine
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    ((gaugedData source pairing hNoGlue hRamification).edgePartition
      (star.edge (firstSelectedLabel source pairing))).Refines
        (finePartition source pairing hNoGlue hRamification) := by
  rw [gaugedData_edgePartition_first source pairing hNoGlue hRamification
    hConnected hGenus]
  unfold finePartition
  apply refines_withSelectedBlock_of_one_class
    (active := branchBlock source (firstSelectedLabel source pairing))
  · exact star.edgePartition_refines_wall data _
  · exact Finset.subset_union_left
  · intro first hFirst second hTogether
    exact ((data.edgePartition
      (star.edge (firstSelectedLabel source pairing))).mem_block_iff _ _).mpr
        (((data.edgePartition
          (star.edge (firstSelectedLabel source pairing))).mem_block_iff _ _).mp
            hFirst |>.trans hTogether)
  · intro sheet hWall
    exact mem_branchBlock_or_block_singleton source hNoGlue _ sheet hWall

theorem permutation_symm_inside (sheet : Fin degree)
    (hSheet : sheet ∈ (data.vertexPartition wall).block anchor.1) :
    (permutation source pairing hNoGlue hRamification).symm sheet ∈
      (data.vertexPartition wall).block anchor.1 := by
  by_contra hOutside
  have hFixed := permutation_outside source pairing hNoGlue hRamification
    ((permutation source pairing hNoGlue hRamification).symm sheet) hOutside
  have hEq : sheet =
      (permutation source pairing hNoGlue hRamification).symm sheet := by
    rw [← hFixed]
    simp
  exact hOutside (hEq ▸ hSheet)

theorem second_edgePartition_refines_fine :
    ((gaugedData source pairing hNoGlue hRamification).edgePartition
      (star.edge (secondSelectedLabel source pairing))).Refines
        (finePartition source pairing hNoGlue hRamification) := by
  rw [gaugedData_edgePartition_second source pairing hNoGlue hRamification]
  unfold finePartition
  let oldEdge := data.edgePartition (star.edge (secondSelectedLabel source pairing))
  let p := permutation source pairing hNoGlue hRamification
  apply refines_withSelectedBlock_of_one_class
    (active := (branchBlock source
      (secondSelectedLabel source pairing)).image p)
  · have hRefines := star.edgePartition_refines_wall
        (gaugedData source pairing hNoGlue hRamification)
        (secondSelectedLabel source pairing)
    rw [gaugedData_vertexPartition_wall source pairing hNoGlue hRamification,
      gaugedData_edgePartition_second source pairing hNoGlue hRamification] at hRefines
    exact hRefines
  · exact Finset.subset_union_right
  · intro first hFirst second hTogether
    have hBlock : (oldEdge.relabel p).block
        (p (source.sheet (secondSelectedLabel source pairing))) =
          (branchBlock source
            (secondSelectedLabel source pairing)).image p := by
      exact oldEdge.relabel_block p _
    have hFirstBlock : first ∈ (oldEdge.relabel p).block
        (p (source.sheet (secondSelectedLabel source pairing))) := by
      rwa [hBlock]
    have hFirstRel := ((oldEdge.relabel p).mem_block_iff _ _).mp hFirstBlock
    have hSecondRel := hFirstRel.trans hTogether
    rwa [← hBlock, (oldEdge.relabel p).mem_block_iff]
  · intro sheet hWall
    let original := p.symm sheet
    have hSheetMem : sheet ∈ (data.vertexPartition wall).block anchor.1 :=
      ((data.vertexPartition wall).mem_block_iff _ _).mpr hWall
    have hOriginalMem : original ∈
        (data.vertexPartition wall).block anchor.1 := by
      exact permutation_symm_inside source pairing hNoGlue hRamification
        sheet hSheetMem
    have hOriginalWall : (data.vertexPartition wall).Rel anchor.1 original :=
      ((data.vertexPartition wall).mem_block_iff _ _).mp hOriginalMem
    rcases mem_branchBlock_or_block_singleton source hNoGlue
      (secondSelectedLabel source pairing) original hOriginalWall with
        hActive | hSingleton
    · left
      exact Finset.mem_image.mpr ⟨original, hActive, by simp [original, p]⟩
    · right
      have hRelabelBlock := oldEdge.relabel_block p original
      have hImageSingleton := congrArg (Finset.image p) hSingleton
      have hSheetEq : sheet = p original := by simp [original, p]
      rw [hSheetEq, hRelabelBlock, hImageSingleton]
      simp

theorem gauged_edgePartition_refines_fine_of_small
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (label : Fin 4)
    (hSmall : W4TargetPairings.Pairing.labelRight pairing label =
      smallerSide source pairing) :
    ((gaugedData source pairing hNoGlue hRamification).edgePartition
      (star.edge label)).Refines
        (finePartition source pairing hNoGlue hRamification) := by
  have hMem : label ∈ W4TargetPairings.Pairing.labelsOnSide pairing
      (smallerSide source pairing) :=
    (W4TargetPairings.Pairing.mem_labelsOnSide _ _ _).mpr hSmall
  rw [labelsOnSide_eq_pair] at hMem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hMem
  rcases hMem with hFirst | hSecond
  · rw [hFirst]
    exact first_edgePartition_refines_fine source pairing hNoGlue hRamification
      hConnected hGenus
  · rw [hSecond]
    exact second_edgePartition_refines_fine source pairing hNoGlue hRamification

theorem fine_blockCount_wall_add_selectedCard :
    (finePartition source pairing hNoGlue hRamification).blockCountWithin
          (data.vertexPartition wall) anchor.1 +
        (selectedSheets source pairing hNoGlue hRamification).card =
      (data.vertexPartition wall).blockCard anchor.1 + 1 := by
  have hCount := blockCountWithin_add_blockCard_eq
    (finePartition source pairing hNoGlue hRamification)
    (data.vertexPartition wall) anchor.1
    (selectedRepresentative source pairing)
    (source.sheet_wall_rel (firstSelectedLabel source pairing))
    (finePartition_refines source pairing hNoGlue hRamification) (by
      intro sheet hWall
      by_cases hSelected : sheet ∈
          selectedSheets source pairing hNoGlue hRamification
      · left
        rw [← (finePartition source pairing hNoGlue hRamification).mem_block_iff,
          finePartition_selected_block source pairing hNoGlue hRamification]
        exact hSelected
      · right
        unfold finePartition
        exact withSelectedBlock.block_of_not_mem_of_rel _ _ _ _ _ _
          hSelected hWall)
  unfold finePartition at hCount
  rw [withSelectedBlock.blockCard_representative] at hCount
  exact hCount

theorem old_edge_blockCount_wall_add_index
    (hNoGlue : DanglingEdgeNoGlue data) (label : Fin 4) :
    (data.edgePartition (star.edge label)).blockCountWithin
          (data.vertexPartition wall) anchor.1 + source.index label =
      (data.vertexPartition wall).blockCard anchor.1 + 1 := by
  have hCount := blockCountWithin_add_blockCard_eq
    (data.edgePartition (star.edge label)) (data.vertexPartition wall)
    anchor.1 (source.sheet label) (source.sheet_wall_rel label)
    (star.edgePartition_refines_wall data label) (by
      intro sheet hWall
      rcases mem_branchBlock_or_block_singleton source hNoGlue label sheet hWall with
        hActive | hSingleton
      · left
        exact ((data.edgePartition (star.edge label)).mem_block_iff _ _).mp hActive
      · exact Or.inr hSingleton)
  exact hCount

theorem first_edge_blockCount_fine_add_index
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    ((gaugedData source pairing hNoGlue hRamification).edgePartition
          (star.edge (firstSelectedLabel source pairing))).blockCountWithin
          (finePartition source pairing hNoGlue hRamification)
          (selectedRepresentative source pairing) +
        source.index (firstSelectedLabel source pairing) =
      (finePartition source pairing hNoGlue hRamification).blockCard
          (selectedRepresentative source pairing) + 1 := by
  rw [gaugedData_edgePartition_first source pairing hNoGlue hRamification
    hConnected hGenus]
  apply blockCountWithin_add_blockCard_eq
  · apply ((finePartition source pairing hNoGlue hRamification).mem_block_iff
      _ _).mp
    rw [finePartition_selected_block]
    exact Finset.mem_union_left _
      ((data.edgePartition
        (star.edge (firstSelectedLabel source pairing))).self_mem_block _)
  · have hRefines := first_edgePartition_refines_fine source pairing hNoGlue
        hRamification hConnected hGenus
    rw [gaugedData_edgePartition_first source pairing hNoGlue hRamification
      hConnected hGenus] at hRefines
    exact hRefines
  · intro sheet hFine
    have hSelected : sheet ∈
        selectedSheets source pairing hNoGlue hRamification := by
      rw [← finePartition_selected_block source pairing hNoGlue hRamification,
        (finePartition source pairing hNoGlue hRamification).mem_block_iff]
      exact hFine
    have hWall := (finePartition_refines source pairing hNoGlue hRamification).rel
      hFine
    rcases mem_branchBlock_or_block_singleton source hNoGlue
      (firstSelectedLabel source pairing) sheet
      ((source.sheet_wall_rel _).trans hWall) with hActive | hSingleton
    · left
      exact ((data.edgePartition
        (star.edge (firstSelectedLabel source pairing))).mem_block_iff _ _).mp hActive
    · exact Or.inr hSingleton

theorem second_edge_blockCount_fine_add_index :
    ((gaugedData source pairing hNoGlue hRamification).edgePartition
          (star.edge (secondSelectedLabel source pairing))).blockCountWithin
          (finePartition source pairing hNoGlue hRamification)
          (selectedRepresentative source pairing) +
        source.index (secondSelectedLabel source pairing) =
      (finePartition source pairing hNoGlue hRamification).blockCard
          (selectedRepresentative source pairing) + 1 := by
  let p := permutation source pairing hNoGlue hRamification
  let oldEdge := data.edgePartition (star.edge (secondSelectedLabel source pairing))
  rw [gaugedData_edgePartition_second source pairing hNoGlue hRamification]
  have hCount := blockCountWithin_add_blockCard_eq (oldEdge.relabel p)
    (finePartition source pairing hNoGlue hRamification)
    (selectedRepresentative source pairing)
    (p (source.sheet (secondSelectedLabel source pairing))) (by
      apply ((finePartition source pairing hNoGlue hRamification).mem_block_iff
        _ _).mp
      rw [finePartition_selected_block]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,
        oldEdge.self_mem_block _, rfl⟩))
    (by
      have hRefines := second_edgePartition_refines_fine source pairing hNoGlue
        hRamification
      rw [gaugedData_edgePartition_second source pairing hNoGlue hRamification]
        at hRefines
      exact hRefines) (by
      intro sheet hFine
      let original := p.symm sheet
      have hSelected : sheet ∈
          selectedSheets source pairing hNoGlue hRamification := by
        rw [← finePartition_selected_block source pairing hNoGlue hRamification,
          (finePartition source pairing hNoGlue hRamification).mem_block_iff]
        exact hFine
      have hWall := (finePartition_refines source pairing hNoGlue hRamification).rel
        hFine
      have hSheetWall : (data.vertexPartition wall).Rel anchor.1 sheet :=
        (source.sheet_wall_rel _).trans hWall
      have hOriginalMem := permutation_symm_inside source pairing hNoGlue
        hRamification sheet
        (((data.vertexPartition wall).mem_block_iff anchor.1 sheet).mpr hSheetWall)
      have hOriginalWall := ((data.vertexPartition wall).mem_block_iff _ _).mp
        hOriginalMem
      rcases mem_branchBlock_or_block_singleton source hNoGlue
        (secondSelectedLabel source pairing) original hOriginalWall with
          hActive | hSingleton
      · left
        rw [show sheet = p original by simp [original, p]]
        apply (oldEdge.relabel_rel_iff p _ _).mpr
        exact ((oldEdge.mem_block_iff _ _).mp hActive)
      · right
        have hRelabelBlock := oldEdge.relabel_block p original
        have hImageSingleton := congrArg (Finset.image p) hSingleton
        have hSheetEq : sheet = p original := by simp [original, p]
        rw [hSheetEq, hRelabelBlock, hImageSingleton]
        simp)
  have hCard := oldEdge.relabel_blockCard p
    (source.sheet (secondSelectedLabel source pairing))
  rw [hCard] at hCount
  exact hCount

theorem second_edge_blockCount_wall_add_index :
    ((gaugedData source pairing hNoGlue hRamification).edgePartition
          (star.edge (secondSelectedLabel source pairing))).blockCountWithin
          (data.vertexPartition wall) anchor.1 +
        source.index (secondSelectedLabel source pairing) =
      (data.vertexPartition wall).blockCard anchor.1 + 1 := by
  rw [gaugedData_edgePartition_second source pairing hNoGlue hRamification]
  let p := permutation source pairing hNoGlue hRamification
  let oldEdge := data.edgePartition (star.edge (secondSelectedLabel source pairing))
  have hCount := SheetPartition.relabel_blockCountWithin_fixed_of_pointwise
    oldEdge (data.vertexPartition wall) p
    (fun sheet ↦ rel_of_stabilizes_block (data.vertexPartition wall) anchor.1 p
      (permutation_inside source pairing hNoGlue hRamification)
      (permutation_outside source pairing hNoGlue hRamification) sheet) anchor.1
  rw [hCount]
  exact old_edge_blockCount_wall_add_index source hNoGlue _

theorem gauged_edge_blockCount_wall_add_index
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (label : Fin 4) :
    ((gaugedData source pairing hNoGlue hRamification).edgePartition
          (star.edge label)).blockCountWithin
          (data.vertexPartition wall) anchor.1 + source.index label =
      (data.vertexPartition wall).blockCard anchor.1 + 1 := by
  by_cases hSecond : label = secondSelectedLabel source pairing
  · subst label
    exact second_edge_blockCount_wall_add_index source pairing hNoGlue
      hRamification
  · rw [gaugedData_edgePartition_other source pairing hNoGlue hRamification
      hConnected hGenus label hSecond]
    exact old_edge_blockCount_wall_add_index source hNoGlue label

theorem sideIndex_smaller_add_other (hNoGlue : DanglingEdgeNoGlue data)
    (hRamification : data.localRamification wall anchor = 0) :
    sideIndex source pairing (smallerSide source pairing) +
        sideIndex source pairing (!(smallerSide source pairing)) =
      2 * (data.vertexPartition wall).blockCard anchor.1 + 2 := by
  have hTotal := sideIndex_false_add_true source pairing
  have hSquare : (∑ label : Fin 4, source.index label) =
      2 * (data.vertexPartition wall).blockCard anchor.1 + 2 := by
    exact_mod_cast source.sum_index_eq_two_mul_add_two hNoGlue hRamification
  rw [hSquare] at hTotal
  cases smallerSide source pairing <;> simp <;> omega

theorem small_side_fine_count_sum
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    W4TargetPairings.Pairing.sideSum pairing (smallerSide source pairing)
      (fun label ↦
        (((gaugedData source pairing hNoGlue hRamification).edgePartition
          (star.edge label)).blockCountWithin
            (finePartition source pairing hNoGlue hRamification)
            (selectedRepresentative source pairing) : ℤ)) =
      (finePartition source pairing hNoGlue hRamification).blockCard
        (selectedRepresentative source pairing) + 1 := by
  have hFirst := first_edge_blockCount_fine_add_index source pairing hNoGlue
    hRamification hConnected hGenus
  have hSecond := second_edge_blockCount_fine_add_index source pairing hNoGlue
    hRamification
  have hSelected := finePartition_selected_card source pairing hNoGlue
    hRamification
  have hSmallIndex :
      sideIndex source pairing (smallerSide source pairing) =
        source.index (firstSelectedLabel source pairing) +
          source.index (secondSelectedLabel source pairing) := by
    simpa only [firstSelectedLabel, secondSelectedLabel] using
      sideIndex_eq_add source pairing (smallerSide source pairing)
  unfold W4TargetPairings.Pairing.sideSum
  rw [labelsOnSide_eq_pair]
  simp [firstLabel_ne_secondLabel]
  exact_mod_cast (by omega :
    ((gaugedData source pairing hNoGlue hRamification).edgePartition
          (star.edge (firstSelectedLabel source pairing))).blockCountWithin
            (finePartition source pairing hNoGlue hRamification)
            (selectedRepresentative source pairing) +
        ((gaugedData source pairing hNoGlue hRamification).edgePartition
          (star.edge (secondSelectedLabel source pairing))).blockCountWithin
            (finePartition source pairing hNoGlue hRamification)
            (selectedRepresentative source pairing) =
      (finePartition source pairing hNoGlue hRamification).blockCard
        (selectedRepresentative source pairing) + 1)

theorem other_side_wall_count_sum
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    W4TargetPairings.Pairing.sideSum pairing (!(smallerSide source pairing))
      (fun label ↦
        (((gaugedData source pairing hNoGlue hRamification).edgePartition
          (star.edge label)).blockCountWithin
            (data.vertexPartition wall) anchor.1 : ℤ)) =
      (selectedSheets source pairing hNoGlue hRamification).card + 1 := by
  let other := !(smallerSide source pairing)
  let first := firstLabel pairing other
  let second := secondLabel pairing other
  have hFirst := gauged_edge_blockCount_wall_add_index source pairing hNoGlue
    hRamification hConnected hGenus first
  have hSecond := gauged_edge_blockCount_wall_add_index source pairing hNoGlue
    hRamification hConnected hGenus second
  have hOtherIndex := sideIndex_eq_add source pairing other
  have hTotal := sideIndex_smaller_add_other source pairing hNoGlue hRamification
  have hSelected := selectedSheets_card source pairing hNoGlue hRamification
  change sideIndex source pairing other =
    source.index first + source.index second at hOtherIndex
  change sideIndex source pairing (smallerSide source pairing) +
      sideIndex source pairing other =
    2 * (data.vertexPartition wall).blockCard anchor.1 + 2 at hTotal
  unfold W4TargetPairings.Pairing.sideSum
  rw [labelsOnSide_eq_pair]
  simp [firstLabel_ne_secondLabel]
  exact_mod_cast (by omega :
    ((gaugedData source pairing hNoGlue hRamification).edgePartition
          (star.edge first)).blockCountWithin
            (data.vertexPartition wall) anchor.1 +
        ((gaugedData source pairing hNoGlue hRamification).edgePartition
          (star.edge second)).blockCountWithin
            (data.vertexPartition wall) anchor.1 =
      (selectedSheets source pairing hNoGlue hRamification).card + 1)

/-! ## The oriented local resolution -/

/-- The endpoint partition assigned to one Boolean side: fine on the chosen
smaller side and the old wall partition on the other side. -/
noncomputable def endpointForSide (sideValue : Bool) : SheetPartition degree :=
  if sideValue = smallerSide source pairing then
    finePartition source pairing hNoGlue hRamification
  else (gaugedData source pairing hNoGlue hRamification).vertexPartition wall

noncomputable def baseResolution : LocalResolution degree :=
  fineResolution
    ((gaugedData source pairing hNoGlue hRamification).vertexPartition wall)
    (finePartition source pairing hNoGlue hRamification) (by
      rw [gaugedData_vertexPartition_wall source pairing hNoGlue hRamification]
      exact finePartition_refines source pairing hNoGlue hRamification)

/-- The actual `K=0` local resolution, reversed exactly when the selected
smaller side is the `true` endpoint of the prescribed target pairing. -/
noncomputable def selectedResolution : LocalResolution degree :=
  if smallerSide source pairing then
    (baseResolution source pairing hNoGlue hRamification).reverse
  else baseResolution source pairing hNoGlue hRamification

theorem selectedResolution_left :
    (selectedResolution source pairing hNoGlue hRamification).left =
      endpointForSide source pairing hNoGlue hRamification false := by
  cases hSide : smallerSide source pairing <;>
    simp [selectedResolution, endpointForSide, baseResolution, fineResolution,
      hSide]

theorem selectedResolution_right :
    (selectedResolution source pairing hNoGlue hRamification).right =
      endpointForSide source pairing hNoGlue hRamification true := by
  cases hSide : smallerSide source pairing <;>
    simp [selectedResolution, endpointForSide, baseResolution, fineResolution,
      hSide]

theorem selectedResolution_newEdge :
    (selectedResolution source pairing hNoGlue hRamification).newEdge =
      finePartition source pairing hNoGlue hRamification := by
  cases hSide : smallerSide source pairing <;>
    simp [selectedResolution, baseResolution, fineResolution, hSide]

theorem selectedResolution_contracts :
    (selectedResolution source pairing hNoGlue hRamification).ContractsTo
      ((gaugedData source pairing hNoGlue hRamification).vertexPartition wall) := by
  have hBase := fineResolution_contracts
    ((gaugedData source pairing hNoGlue hRamification).vertexPartition wall)
    (finePartition source pairing hNoGlue hRamification) (by
      rw [gaugedData_vertexPartition_wall source pairing hNoGlue hRamification]
      exact finePartition_refines source pairing hNoGlue hRamification)
  cases hSide : smallerSide source pairing
  · simpa [selectedResolution, baseResolution, hSide] using hBase
  · simpa [selectedResolution, baseResolution, hSide] using
      (LocalResolution.reverse_contracts hBase)

@[simp] theorem selectedResolution_endpoint (sideValue : Bool) :
    (if sideValue then
        (selectedResolution source pairing hNoGlue hRamification).right
      else (selectedResolution source pairing hNoGlue hRamification).left) =
      endpointForSide source pairing hNoGlue hRamification sideValue := by
  cases sideValue <;>
    simp [selectedResolution_left, selectedResolution_right]

theorem finePartition_rel_or_singleton (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel anchor.1 sheet) :
    (finePartition source pairing hNoGlue hRamification).Rel
        (selectedRepresentative source pairing) sheet ∨
      (finePartition source pairing hNoGlue hRamification).block sheet =
        {sheet} := by
  by_cases hSelected : sheet ∈
      selectedSheets source pairing hNoGlue hRamification
  · left
    rw [← (finePartition source pairing hNoGlue hRamification).mem_block_iff,
      finePartition_selected_block source pairing hNoGlue hRamification]
    exact hSelected
  · right
    unfold finePartition
    exact withSelectedBlock.block_of_not_mem_of_rel _ _ _ _ _ _
      hSelected hWall

theorem small_side_fine_count_sum_of_rel
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (sheet : Fin degree)
    (hFine : (finePartition source pairing hNoGlue hRamification).Rel
      (selectedRepresentative source pairing) sheet) :
    W4TargetPairings.Pairing.sideSum pairing (smallerSide source pairing)
      (fun label ↦
        (((gaugedData source pairing hNoGlue hRamification).edgePartition
          (star.edge label)).blockCountWithin
            (finePartition source pairing hNoGlue hRamification) sheet : ℤ)) =
      (finePartition source pairing hNoGlue hRamification).blockCard sheet + 1 := by
  have hBase := small_side_fine_count_sum source pairing hNoGlue
    hRamification hConnected hGenus
  have hCounts :
      W4TargetPairings.Pairing.sideSum pairing (smallerSide source pairing)
          (fun label ↦
            (((gaugedData source pairing hNoGlue hRamification).edgePartition
              (star.edge label)).blockCountWithin
                (finePartition source pairing hNoGlue hRamification) sheet : ℤ)) =
        W4TargetPairings.Pairing.sideSum pairing (smallerSide source pairing)
          (fun label ↦
            (((gaugedData source pairing hNoGlue hRamification).edgePartition
              (star.edge label)).blockCountWithin
                (finePartition source pairing hNoGlue hRamification)
                (selectedRepresentative source pairing) : ℤ)) := by
    unfold W4TargetPairings.Pairing.sideSum
    apply Finset.sum_congr rfl
    intro label _
    have hNat := ContractionRamification.blockCountWithin_congr
      ((gaugedData source pairing hNoGlue hRamification).edgePartition
      (star.edge label))
      (finePartition source pairing hNoGlue hRamification) hFine
    change
      (((gaugedData source pairing hNoGlue hRamification).edgePartition
        (star.edge label)).blockCountWithin
          (finePartition source pairing hNoGlue hRamification) sheet : ℤ) =
      (((gaugedData source pairing hNoGlue hRamification).edgePartition
        (star.edge label)).blockCountWithin
          (finePartition source pairing hNoGlue hRamification)
          (selectedRepresentative source pairing) : ℤ)
    exact_mod_cast hNat.symm
  have hCard := ContractionRamification.blockCard_congr
    (finePartition source pairing hNoGlue hRamification) hFine
  rw [hCounts, hBase, hCard]

theorem other_side_wall_count_sum_of_rel
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (sheet : Fin degree) (hWall : (data.vertexPartition wall).Rel anchor.1 sheet) :
    W4TargetPairings.Pairing.sideSum pairing (!(smallerSide source pairing))
      (fun label ↦
        (((gaugedData source pairing hNoGlue hRamification).edgePartition
          (star.edge label)).blockCountWithin
            (data.vertexPartition wall) sheet : ℤ)) =
      (selectedSheets source pairing hNoGlue hRamification).card + 1 := by
  have hBase := other_side_wall_count_sum source pairing hNoGlue
    hRamification hConnected hGenus
  have hCounts :
      W4TargetPairings.Pairing.sideSum pairing (!(smallerSide source pairing))
          (fun label ↦
            (((gaugedData source pairing hNoGlue hRamification).edgePartition
              (star.edge label)).blockCountWithin
                (data.vertexPartition wall) sheet : ℤ)) =
        W4TargetPairings.Pairing.sideSum pairing (!(smallerSide source pairing))
          (fun label ↦
            (((gaugedData source pairing hNoGlue hRamification).edgePartition
              (star.edge label)).blockCountWithin
                (data.vertexPartition wall) anchor.1 : ℤ)) := by
    unfold W4TargetPairings.Pairing.sideSum
    apply Finset.sum_congr rfl
    intro label _
    have hNat := ContractionRamification.blockCountWithin_congr
      ((gaugedData source pairing hNoGlue hRamification).edgePartition
        (star.edge label)) (data.vertexPartition wall) hWall
    change
      (((gaugedData source pairing hNoGlue hRamification).edgePartition
        (star.edge label)).blockCountWithin (data.vertexPartition wall) sheet : ℤ) =
      (((gaugedData source pairing hNoGlue hRamification).edgePartition
        (star.edge label)).blockCountWithin
          (data.vertexPartition wall) anchor.1 : ℤ)
    exact_mod_cast hNat.symm
  rw [hCounts, hBase]

theorem fine_blockCount_wall_add_selectedCard_of_rel
    (sheet : Fin degree) (hWall : (data.vertexPartition wall).Rel anchor.1 sheet) :
    (finePartition source pairing hNoGlue hRamification).blockCountWithin
          (data.vertexPartition wall) sheet +
        (selectedSheets source pairing hNoGlue hRamification).card =
      (data.vertexPartition wall).blockCard sheet + 1 := by
  rw [ContractionRamification.blockCountWithin_congr _ _ hWall.symm,
    ContractionRamification.blockCard_congr _ hWall.symm]
  exact fine_blockCount_wall_add_selectedCard source pairing hNoGlue hRamification

/-! ## The actual global candidate -/

/-- The source geometry still required away from the distinguished four-valent
class.  These are precisely the guarded background resolutions of the other
wall blocks; no fine partition, selected-block RH inequality, or candidate
validity is supplied here. -/
structure PairingBackground where
  resolution : Fin degree → LocalResolution degree
  contracts : ∀ block,
    ¬((gaugedData source pairing hNoGlue hRamification).vertexPartition wall).Rel
        anchor.1 block →
      (resolution block).ContractsTo
        ((gaugedData source pairing hNoGlue hRamification).vertexPartition wall)
  exterior : ∀ edge : target.edges,
    ((edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) →
    ∀ block,
      ¬((gaugedData source pairing hNoGlue hRamification).vertexPartition wall).Rel
          anchor.1 block →
        ((gaugedData source pairing hNoGlue hRamification).edgePartition edge).Refines
          (if star.right pairing edge then (resolution block).right
            else (resolution block).left)
  left_riemannHurwitz : ∀ block,
    ((gaugedData source pairing hNoGlue hRamification).vertexPartition wall).repr
        block = block →
    ¬((gaugedData source pairing hNoGlue hRamification).vertexPartition wall).Rel
        anchor.1 block →
      LocalResolution.RiemannHurwitzAtBlock
        ((gaugedData source pairing hNoGlue hRamification).vertexPartition wall)
        (resolution block).left
        ((resolution block).newEdge ::
          (star.leftEdges pairing).map
            (gaugedData source pairing hNoGlue hRamification).edgePartition)
        block
  right_riemannHurwitz : ∀ block,
    ((gaugedData source pairing hNoGlue hRamification).vertexPartition wall).repr
        block = block →
    ¬((gaugedData source pairing hNoGlue hRamification).vertexPartition wall).Rel
        anchor.1 block →
      LocalResolution.RiemannHurwitzAtBlock
        ((gaugedData source pairing hNoGlue hRamification).vertexPartition wall)
        (resolution block).right
        ((resolution block).newEdge ::
          (star.rightEdges pairing).map
            (gaugedData source pairing hNoGlue hRamification).edgePartition)
        block

namespace PairingBackground

/-- Package the guarded source geometry with the prescribed target pairing's
actual occurrence assignment and canonical occurrence lists. -/
noncomputable def background
    (geometry : PairingBackground source pairing hNoGlue hRamification) :
    GlobalM11Arbitrary.Background
      (gaugedData source pairing hNoGlue hRamification) wall anchor.1 where
  right := star.right pairing
  resolution := geometry.resolution
  contracts := geometry.contracts
  exterior := geometry.exterior
  leftEdges := star.leftEdges pairing
  rightEdges := star.rightEdges pairing
  leftEdges_eq := star.leftEdges_eq pairing
  rightEdges_eq := star.rightEdges_eq pairing
  left_riemannHurwitz := geometry.left_riemannHurwitz
  right_riemannHurwitz := geometry.right_riemannHurwitz

end PairingBackground

/-- Every actual old occurrence refines the endpoint prescribed for its side:
the two selected occurrences refine the fine endpoint, and the other two
refine the unchanged wall endpoint. -/
theorem selected_exterior
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (edge : target.edges)
    (hIncident : (edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) :
    ((gaugedData source pairing hNoGlue hRamification).edgePartition edge).Refines
      (if star.right pairing edge then
        (selectedResolution source pairing hNoGlue hRamification).right
      else (selectedResolution source pairing hNoGlue hRamification).left) := by
  have hMem : edge ∈ GluingDatum.incidentEdges wall :=
    (GluingContraction.mem_incidentEdges_iff wall edge).mpr hIncident
  obtain ⟨label, rfl⟩ := star.exists_edge_eq edge hMem
  rw [star.right_edge, selectedResolution_endpoint]
  unfold endpointForSide
  by_cases hSmall : W4TargetPairings.Pairing.labelRight pairing label =
      smallerSide source pairing
  · rw [if_pos hSmall]
    exact gauged_edgePartition_refines_fine_of_small source pairing hNoGlue
      hRamification hConnected hGenus label hSmall
  · rw [if_neg hSmall]
    exact star.edgePartition_refines_wall
      (gaugedData source pairing hNoGlue hRamification) label

/-- The selected four-valent block satisfies the endpoint RH inequality on
either side.  This is derived from the exact K=0 block counts above; it is not
part of `PairingBackground`. -/
theorem selected_riemannHurwitzAtBlock_side
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (sideValue : Bool) (block : Fin degree)
    (hBlock :
      ((gaugedData source pairing hNoGlue hRamification).vertexPartition wall).Rel
        anchor.1 block) :
    LocalResolution.RiemannHurwitzAtBlock
      ((gaugedData source pairing hNoGlue hRamification).vertexPartition wall)
      (endpointForSide source pairing hNoGlue hRamification sideValue)
      ((finePartition source pairing hNoGlue hRamification) ::
        (W4Assembly.oldEdgesAtSide star pairing sideValue).map
          (gaugedData source pairing hNoGlue hRamification).edgePartition)
      block := by
  rw [gaugedData_vertexPartition_wall source pairing hNoGlue hRamification]
    at hBlock ⊢
  intro sheet hSheet
  have hWall : (data.vertexPartition wall).Rel anchor.1 sheet :=
    hBlock.trans hSheet
  have hLength :
      (W4Assembly.oldEdgesAtSide star pairing sideValue).length = 2 := by
    cases sideValue <;> simp [W4Assembly.oldEdgesAtSide]
  simp only [List.map_cons, List.sum_cons, List.map_map, List.length_cons,
    List.length_map, hLength]
  rw [W4Assembly.sum_oldEdgesAtSide_eq_sideSum]
  simp only [Function.comp_apply]
  by_cases hSide : sideValue = smallerSide source pairing
  · rw [endpointForSide, if_pos hSide]
    rw [hSide]
    rcases finePartition_rel_or_singleton source pairing hNoGlue hRamification
      sheet hWall with hFine | hSingleton
    · have hOld := small_side_fine_count_sum_of_rel source pairing hNoGlue
        hRamification hConnected hGenus sheet hFine
      simp only [SheetPartition.blockCountWithin_self]
      omega
    · have hFineCard :
          (finePartition source pairing hNoGlue hRamification).blockCard sheet =
            1 := by
        unfold SheetPartition.blockCard
        rw [hSingleton]
        simp
      have hOld :
          W4TargetPairings.Pairing.sideSum pairing
            (smallerSide source pairing)
              (fun label ↦
                (((gaugedData source pairing hNoGlue hRamification).edgePartition
                  (star.edge label)).blockCountWithin
                    (finePartition source pairing hNoGlue hRamification)
                    sheet : ℤ)) = 2 := by
        unfold W4TargetPairings.Pairing.sideSum
        calc
          (∑ label ∈ W4TargetPairings.Pairing.labelsOnSide pairing
              (smallerSide source pairing),
              (((gaugedData source pairing hNoGlue hRamification).edgePartition
                (star.edge label)).blockCountWithin
                  (finePartition source pairing hNoGlue hRamification)
                  sheet : ℤ)) =
              ∑ _label ∈ W4TargetPairings.Pairing.labelsOnSide pairing
                (smallerSide source pairing), (1 : ℤ) := by
                  apply Finset.sum_congr rfl
                  intro label _
                  exact_mod_cast
                    SheetPartition.blockCountWithin_eq_one_of_block_eq_singleton
                      ((gaugedData source pairing hNoGlue hRamification).edgePartition
                        (star.edge label))
                      (finePartition source pairing hNoGlue hRamification)
                      sheet hSingleton
          _ = 2 := by simp
      simp only [SheetPartition.blockCountWithin_self]
      omega
  · have hOther : sideValue = !(smallerSide source pairing) := by
      cases hValue : sideValue <;>
        cases hSmall : smallerSide source pairing <;> simp_all
    rw [endpointForSide, if_neg hSide,
      gaugedData_vertexPartition_wall source pairing hNoGlue hRamification]
    have hFineCount := fine_blockCount_wall_add_selectedCard_of_rel
      source pairing hNoGlue hRamification sheet hWall
    have hOld := other_side_wall_count_sum_of_rel source pairing hNoGlue
      hRamification hConnected hGenus sheet hWall
    rw [hOther]
    omega

/-- The prescribed K=0 local resolution installed into the actual guarded
background. -/
noncomputable def candidate
    (geometry : PairingBackground source pairing hNoGlue hRamification)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    BalancedGlobal.Candidate target degree
      (gaugedData source pairing hNoGlue hRamification) wall := by
  apply geometry.background.install
    (selectedResolution source pairing hNoGlue hRamification)
    (selectedResolution_contracts source pairing hNoGlue hRamification)
    (selected_exterior source pairing hNoGlue hRamification hConnected hGenus)
  · intro block hRel _hCanonical
    rw [selectedResolution_left, selectedResolution_newEdge]
    simpa [W4Assembly.oldEdgesAtSide, PairingBackground.background] using
      selected_riemannHurwitzAtBlock_side source pairing hNoGlue
        hRamification hConnected hGenus false block hRel
  · intro block hRel _hCanonical
    rw [selectedResolution_right, selectedResolution_newEdge]
    simpa [W4Assembly.oldEdgesAtSide, PairingBackground.background] using
      selected_riemannHurwitzAtBlock_side source pairing hNoGlue
        hRamification hConnected hGenus true block hRel

/-- Incoming validity, transported through the actual branch gauge, is the
only validity input to the assembled outgoing candidate. -/
theorem candidate_datum_valid
    (geometry : PairingBackground source pairing hNoGlue hRamification)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hValid : data.Valid) :
    (candidate source pairing hNoGlue hRamification geometry hConnected
      hGenus).datum.Valid :=
  (candidate source pairing hNoGlue hRamification geometry hConnected
    hGenus).datum_valid
      (gaugedData_valid source pairing hNoGlue hRamification hValid)

/-- On the distinguished wall block, the candidate really uses the selected
K=0 resolution rather than a supplied background resolution. -/
theorem candidate_resolution_anchor
    (geometry : PairingBackground source pairing hNoGlue hRamification)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    (candidate source pairing hNoGlue hRamification geometry hConnected
      hGenus).resolution anchor.1 =
        selectedResolution source pairing hNoGlue hRamification := by
  unfold candidate PairingBackground.background
    GlobalM11Arbitrary.Background.install
  apply LocalResolution.onBlock_of_rel
  simp

theorem candidate_resolution_of_wall_rel
    (geometry : PairingBackground source pairing hNoGlue hRamification)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (block : Fin degree)
    (hRel :
      ((gaugedData source pairing hNoGlue hRamification).vertexPartition wall).Rel
        anchor.1 block) :
    (candidate source pairing hNoGlue hRamification geometry hConnected
      hGenus).resolution block =
        selectedResolution source pairing hNoGlue hRamification := by
  unfold candidate PairingBackground.background
    GlobalM11Arbitrary.Background.install
  exact LocalResolution.onBlock_of_rel _ _ _ _ _ hRel

/-- Exact K=0 bridge size on the actual candidate's distinguished local
resolution: the new class has size one less than the selected side index. -/
theorem candidate_newEdge_blockCard_add_one
    (geometry : PairingBackground source pairing hNoGlue hRamification)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    ((candidate source pairing hNoGlue hRamification geometry hConnected
      hGenus).resolution anchor.1).newEdge.blockCard
        (selectedRepresentative source pairing) + 1 =
      sideIndex source pairing (smallerSide source pairing) := by
  rw [candidate_resolution_anchor source pairing hNoGlue hRamification
    geometry hConnected hGenus, selectedResolution_newEdge]
  exact finePartition_selected_card source pairing hNoGlue hRamification

/-- The exact bridge size in the outgoing gluing datum itself, stated as the
dilation index of the canonical new quotient-source occurrence. -/
theorem candidate_newSourceEdge_index_add_one
    (geometry : PairingBackground source pairing hNoGlue hRamification)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    (candidate source pairing hNoGlue hRamification geometry hConnected
      hGenus).datum.sourceEdgeIndex
        ((candidate source pairing hNoGlue hRamification geometry hConnected
          hGenus).newSourceEdge (selectedRepresentative source pairing)) + 1 =
      sideIndex source pairing (smallerSide source pairing) := by
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge,
    LocalResolution.paste_newEdge_blockCard]
  have hRepresentative :
      ((gaugedData source pairing hNoGlue hRamification).vertexPartition wall).Rel
        anchor.1 (selectedRepresentative source pairing) := by
    rw [gaugedData_vertexPartition_wall source pairing hNoGlue hRamification]
    exact source.sheet_wall_rel (firstSelectedLabel source pairing)
  have hRepr :
      ((gaugedData source pairing hNoGlue hRamification).vertexPartition wall).Rel
        anchor.1
        (((gaugedData source pairing hNoGlue hRamification).vertexPartition wall).repr
          (selectedRepresentative source pairing)) :=
    hRepresentative.trans
      (((gaugedData source pairing hNoGlue hRamification).vertexPartition wall).rel_repr_right
        (selectedRepresentative source pairing))
  rw [candidate_resolution_of_wall_rel source pairing hNoGlue hRamification
    geometry hConnected hGenus _ hRepr, selectedResolution_newEdge]
  exact finePartition_selected_card source pairing hNoGlue hRamification

/-! ## Localizing the rigid background blocks -/

/-- The block-local form of the background data.  Unlike
`GlobalM11Arbitrary.Background`, its exterior compatibility is required only
on the wall block being resolved.  This is exactly the form produced by the
canonical pairing census of Case {w4}. -/
structure BlockLocalBackground where
  resolution : Fin degree → LocalResolution degree
  contracts : ∀ block,
    ¬((gaugedData source pairing hNoGlue hRamification).vertexPartition wall).Rel
        anchor.1 block →
      (resolution block).ContractsTo
        ((gaugedData source pairing hNoGlue hRamification).vertexPartition wall)
  exterior : ∀ edge : target.edges,
    ((edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) →
    ∀ block,
      ¬((gaugedData source pairing hNoGlue hRamification).vertexPartition wall).Rel
          anchor.1 block →
        ((gaugedData source pairing hNoGlue hRamification).edgePartition edge).RefinesOnBlock
          (if star.right pairing edge then (resolution block).right
            else (resolution block).left)
          ((gaugedData source pairing hNoGlue hRamification).vertexPartition wall)
          block
  left_riemannHurwitz : ∀ block,
    ((gaugedData source pairing hNoGlue hRamification).vertexPartition wall).repr
        block = block →
    ¬((gaugedData source pairing hNoGlue hRamification).vertexPartition wall).Rel
        anchor.1 block →
      LocalResolution.RiemannHurwitzAtBlock
        ((gaugedData source pairing hNoGlue hRamification).vertexPartition wall)
        (resolution block).left
        ((resolution block).newEdge ::
          (star.leftEdges pairing).map
            (gaugedData source pairing hNoGlue hRamification).edgePartition)
        block
  right_riemannHurwitz : ∀ block,
    ((gaugedData source pairing hNoGlue hRamification).vertexPartition wall).repr
        block = block →
    ¬((gaugedData source pairing hNoGlue hRamification).vertexPartition wall).Rel
        anchor.1 block →
      LocalResolution.RiemannHurwitzAtBlock
        ((gaugedData source pairing hNoGlue hRamification).vertexPartition wall)
        (resolution block).right
        ((resolution block).newEdge ::
          (star.rightEdges pairing).map
            (gaugedData source pairing hNoGlue hRamification).edgePartition)
        block

namespace BlockLocalBackground

noncomputable abbrev coarsePartition : SheetPartition degree :=
  (gaugedData source pairing hNoGlue hRamification).vertexPartition wall

local notation "gauged" =>
  (gaugedData source pairing hNoGlue hRamification)
local notation "coarse" =>
  (coarsePartition source pairing hNoGlue hRamification)

/-- Localize the resolution for `block`: paste it on that wall block and use
the neutral joined resolution everywhere else.  The outer `dite` gives a
harmless total value on the distinguished nd4 block, where background data is
deliberately absent. -/
noncomputable def localizedResolution
    (geometry : BlockLocalBackground source pairing hNoGlue hRamification)
    (block : Fin degree) (hBlock : ¬(coarse).Rel anchor.1 block) :
    LocalResolution degree :=
  LocalResolution.paste coarse
    (LocalResolution.onBlock coarse block (geometry.resolution block)
      (fun _ ↦ joinedResolutionAt coarse))
    (LocalResolution.onBlock_contracts coarse block
      (geometry.resolution block) (fun _ ↦ joinedResolutionAt coarse)
      (geometry.contracts block hBlock)
      (fun _ ↦ joinedResolutionAt_contracts coarse))

theorem localizedResolution_contracts
    (geometry : BlockLocalBackground source pairing hNoGlue hRamification)
    (block : Fin degree) (hBlock : ¬(coarse).Rel anchor.1 block) :
    (localizedResolution (source := source) (pairing := pairing)
      (hNoGlue := hNoGlue) (hRamification := hRamification)
      geometry block hBlock).ContractsTo coarse :=
  LocalResolution.paste_contracts coarse _ _

/-- A global refinement to `coarse` plus a refinement on the selected block
refines the partition obtained by pasting that selected endpoint into
`coarse`.  This is the narrow local-to-global adapter needed by the background
API of the M11 case (`GlobalM11Arbitrary.Background`). -/
theorem refines_paste_onBlock
    (fine : SheetPartition degree)
    (family : Fin degree → SheetPartition degree)
    (hFine : fine.Refines coarse)
    (hFamily : ∀ other, (family other).Refines coarse)
    (hLocal : ∀ first second, (coarse).Rel first second →
      fine.Rel first second → (family ((coarse).repr first)).Rel first second) :
    fine.Refines ((coarse).paste family hFamily) := by
  intro first second hRel
  rw [(coarse).paste_rel_iff]
  exact hLocal first second (hFine.rel hRel) hRel

/-- Block-local exterior compatibility becomes the global refinement demanded
by `GlobalM11Arbitrary.Background` after localization. -/
theorem exterior_localizedResolution
    (geometry : BlockLocalBackground source pairing hNoGlue hRamification)
    (edge : target.edges)
    (hIncident : (edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall)
    (block : Fin degree) (hBlock : ¬(coarse).Rel anchor.1 block) :
    ((gauged).edgePartition edge).Refines
      (if star.right pairing edge then
        (localizedResolution (source := source) (pairing := pairing)
          (hNoGlue := hNoGlue) (hRamification := hRamification)
          geometry block hBlock).right
      else (localizedResolution (source := source) (pairing := pairing)
        (hNoGlue := hNoGlue) (hRamification := hRamification)
        geometry block hBlock).left) := by
  classical
  unfold localizedResolution
  let localRes := LocalResolution.onBlock coarse block (geometry.resolution block)
    (fun _ ↦ joinedResolutionAt coarse)
  let hContracts : ∀ other, (localRes other).ContractsTo coarse :=
    LocalResolution.onBlock_contracts coarse block (geometry.resolution block)
      (fun _ ↦ joinedResolutionAt coarse) (geometry.contracts block hBlock)
      (fun _ ↦ joinedResolutionAt_contracts coarse)
  have hFine : ((gauged).edgePartition edge).Refines coarse :=
    W4StableSource.edgePartition_refines_of_mem_incidentEdges gauged wall edge
      ((GluingContraction.mem_incidentEdges_iff wall edge).mpr hIncident)
  have hBlockRepr : (coarse).Rel block ((coarse).repr block) :=
    (coarse).rel_repr_right block
  cases hSide : star.right pairing edge
  · change ((gauged).edgePartition edge).Refines
      (LocalResolution.paste coarse localRes hContracts).left
    change ((gauged).edgePartition edge).Refines
      ((coarse).paste (fun other ↦ (localRes other).left)
        (fun other ↦ (hContracts other).left_refines))
    apply refines_paste_onBlock (source := source) (pairing := pairing)
      (hNoGlue := hNoGlue) (hRamification := hRamification)
      (fine := (gauged).edgePartition edge)
      (family := fun other ↦ (localRes other).left) hFine
      (fun other ↦ (hContracts other).left_refines)
    intro first second hCoarse hEdge
    by_cases hOther : (coarse).Rel block ((coarse).repr first)
    · rw [show localRes ((coarse).repr first) = geometry.resolution block by
        exact LocalResolution.onBlock_of_rel _ _ _ _ _ hOther]
      have hLocal : ((gauged).edgePartition edge).RefinesOnBlock
          (geometry.resolution block).left coarse block := by
        simpa [hSide] using geometry.exterior edge hIncident block hBlock
      exact hLocal.rel
        (hOther.trans ((coarse).rel_repr_left first)) hEdge
    · rw [show localRes ((coarse).repr first) = joinedResolutionAt coarse by
        exact LocalResolution.onBlock_of_not_rel _ _ _ _ _ hOther]
      exact hFine.rel hEdge
  · change ((gauged).edgePartition edge).Refines
      (LocalResolution.paste coarse localRes hContracts).right
    change ((gauged).edgePartition edge).Refines
      ((coarse).paste (fun other ↦ (localRes other).right)
        (fun other ↦ (hContracts other).right_refines))
    apply refines_paste_onBlock (source := source) (pairing := pairing)
      (hNoGlue := hNoGlue) (hRamification := hRamification)
      (fine := (gauged).edgePartition edge)
      (family := fun other ↦ (localRes other).right) hFine
      (fun other ↦ (hContracts other).right_refines)
    intro first second hCoarse hEdge
    by_cases hOther : (coarse).Rel block ((coarse).repr first)
    · rw [show localRes ((coarse).repr first) = geometry.resolution block by
        exact LocalResolution.onBlock_of_rel _ _ _ _ _ hOther]
      have hLocal : ((gauged).edgePartition edge).RefinesOnBlock
          (geometry.resolution block).right coarse block := by
        simpa [hSide] using geometry.exterior edge hIncident block hBlock
      exact hLocal.rel
        (hOther.trans ((coarse).rel_repr_left first)) hEdge
    · rw [show localRes ((coarse).repr first) = joinedResolutionAt coarse by
        exact LocalResolution.onBlock_of_not_rel _ _ _ _ _ hOther]
      exact hFine.rel hEdge

/-- The localized left endpoint has exactly the canonical local counts on the
block where it was installed. -/
theorem localizedResolution_left_riemannHurwitz
    (geometry : BlockLocalBackground source pairing hNoGlue hRamification)
    (block : Fin degree) (hCanonical : (coarse).repr block = block)
    (hBlock : ¬(coarse).Rel anchor.1 block) :
    LocalResolution.RiemannHurwitzAtBlock coarse
      (localizedResolution (source := source) (pairing := pairing)
        (hNoGlue := hNoGlue) (hRamification := hRamification)
        geometry block hBlock).left
      ((localizedResolution (source := source) (pairing := pairing)
          (hNoGlue := hNoGlue) (hRamification := hRamification)
          geometry block hBlock).newEdge ::
        (star.leftEdges pairing).map (gauged).edgePartition) block := by
  classical
  unfold localizedResolution
  let localRes := LocalResolution.onBlock coarse block (geometry.resolution block)
    (fun _ ↦ joinedResolutionAt coarse)
  let hContracts : ∀ other, (localRes other).ContractsTo coarse :=
    LocalResolution.onBlock_contracts coarse block (geometry.resolution block)
      (fun _ ↦ joinedResolutionAt coarse) (geometry.contracts block hBlock)
      (fun _ ↦ joinedResolutionAt_contracts coarse)
  intro sheet hSheet
  have hRepr : (coarse).repr sheet = block := hSheet.symm.trans hCanonical
  have hLocal := geometry.left_riemannHurwitz block hCanonical hBlock sheet hSheet
  simp only [List.map_cons, List.sum_cons, List.length_cons] at hLocal ⊢
  rw [LocalResolution.paste_newEdge_blockCountWithin_left,
    LocalResolution.paste_left_blockCard, hRepr]
  simp_rw [LocalResolution.blockCountWithin_paste_left]
  rw [hRepr]
  simpa [localRes, LocalResolution.onBlock_of_rel _ _ _ _ _
    ((coarse).rel_repr_right block)] using hLocal

/-- The right-endpoint counterpart of
`localizedResolution_left_riemannHurwitz`. -/
theorem localizedResolution_right_riemannHurwitz
    (geometry : BlockLocalBackground source pairing hNoGlue hRamification)
    (block : Fin degree) (hCanonical : (coarse).repr block = block)
    (hBlock : ¬(coarse).Rel anchor.1 block) :
    LocalResolution.RiemannHurwitzAtBlock coarse
      (localizedResolution (source := source) (pairing := pairing)
        (hNoGlue := hNoGlue) (hRamification := hRamification)
        geometry block hBlock).right
      ((localizedResolution (source := source) (pairing := pairing)
          (hNoGlue := hNoGlue) (hRamification := hRamification)
          geometry block hBlock).newEdge ::
        (star.rightEdges pairing).map (gauged).edgePartition) block := by
  classical
  unfold localizedResolution
  let localRes := LocalResolution.onBlock coarse block (geometry.resolution block)
    (fun _ ↦ joinedResolutionAt coarse)
  let hContracts : ∀ other, (localRes other).ContractsTo coarse :=
    LocalResolution.onBlock_contracts coarse block (geometry.resolution block)
      (fun _ ↦ joinedResolutionAt coarse) (geometry.contracts block hBlock)
      (fun _ ↦ joinedResolutionAt_contracts coarse)
  intro sheet hSheet
  have hRepr : (coarse).repr sheet = block := hSheet.symm.trans hCanonical
  have hLocal := geometry.right_riemannHurwitz block hCanonical hBlock sheet hSheet
  simp only [List.map_cons, List.sum_cons, List.length_cons] at hLocal ⊢
  rw [LocalResolution.paste_newEdge_blockCountWithin_right,
    LocalResolution.paste_right_blockCard, hRepr]
  simp_rw [LocalResolution.blockCountWithin_paste_right]
  rw [hRepr]
  simpa [localRes, LocalResolution.onBlock_of_rel _ _ _ _ _
    ((coarse).rel_repr_right block)] using hLocal

/-- Convert block-local Case {w4} background receipts to the global background
contract of the M11 case (`GlobalM11Arbitrary.Background`) by localizing each
canonical resolution to its own wall block. -/
noncomputable def pairingBackground
    (geometry : BlockLocalBackground source pairing hNoGlue hRamification) :
    PairingBackground source pairing hNoGlue hRamification where
  resolution := fun block ↦ if hBlock : (coarse).Rel anchor.1 block then
      joinedResolutionAt coarse
    else localizedResolution (source := source) (pairing := pairing)
      (hNoGlue := hNoGlue) (hRamification := hRamification)
      geometry block hBlock
  contracts := by
    intro block hBlock
    simp only [hBlock, dite_false]
    exact localizedResolution_contracts (source := source)
      (pairing := pairing) (hNoGlue := hNoGlue)
      (hRamification := hRamification) geometry block hBlock
  exterior := by
    intro edge hIncident block hBlock
    simp only [hBlock, dite_false]
    exact exterior_localizedResolution (source := source)
      (pairing := pairing) (hNoGlue := hNoGlue)
      (hRamification := hRamification) geometry edge hIncident block hBlock
  left_riemannHurwitz := by
    intro block hCanonical hBlock
    simp only [hBlock, dite_false]
    exact localizedResolution_left_riemannHurwitz (source := source)
      (pairing := pairing) (hNoGlue := hNoGlue)
      (hRamification := hRamification) geometry block hCanonical hBlock
  right_riemannHurwitz := by
    intro block hCanonical hBlock
    simp only [hBlock, dite_false]
    exact localizedResolution_right_riemannHurwitz (source := source)
      (pairing := pairing) (hNoGlue := hNoGlue)
      (hRamification := hRamification) geometry block hCanonical hBlock

end BlockLocalBackground

/-- Exact endpoint sizes in the selected local resolution: the chosen side is
the K=0 union of size `sideIndex - 1`, while the opposite side is the complete
old wall block. -/
theorem endpointForSide_blockCard_add_one (sideValue : Bool) :
    (endpointForSide source pairing hNoGlue hRamification sideValue).blockCard
        (selectedRepresentative source pairing) + 1 =
      if sideValue = smallerSide source pairing then
        sideIndex source pairing (smallerSide source pairing)
      else (data.vertexPartition wall).blockCard anchor.1 + 1 := by
  by_cases hSide : sideValue = smallerSide source pairing
  · rw [endpointForSide, if_pos hSide, if_pos hSide]
    exact finePartition_selected_card source pairing hNoGlue hRamification
  · rw [endpointForSide, if_neg hSide, if_neg hSide,
      gaugedData_vertexPartition_wall source pairing hNoGlue hRamification]
    have hRel := source.sheet_wall_rel (firstSelectedLabel source pairing)
    change (data.vertexPartition wall).blockCard
        (source.sheet (firstSelectedLabel source pairing)) + 1 =
      (data.vertexPartition wall).blockCard anchor.1 + 1
    rw [ContractionRamification.blockCard_congr _ hRel.symm]

/-- The same two endpoint sizes read directly from the installed candidate. -/
theorem candidate_endpoint_blockCard_add_one
    (geometry : PairingBackground source pairing hNoGlue hRamification)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (sideValue : Bool) :
    (if sideValue then
        ((candidate source pairing hNoGlue hRamification geometry hConnected
          hGenus).resolution anchor.1).right
      else ((candidate source pairing hNoGlue hRamification geometry hConnected
        hGenus).resolution anchor.1).left).blockCard
          (selectedRepresentative source pairing) + 1 =
      if sideValue = smallerSide source pairing then
        sideIndex source pairing (smallerSide source pairing)
      else (data.vertexPartition wall).blockCard anchor.1 + 1 := by
  rw [candidate_resolution_anchor source pairing hNoGlue hRamification
    geometry hConnected hGenus, selectedResolution_endpoint]
  exact endpointForSide_blockCard_add_one source pairing hNoGlue hRamification
    sideValue

end BranchGauge

end PrescribedPairing

end DraismaVargas.LocalCases.NonTrivalentValencyFourKZero
