module

public import DraismaVargas.LocalCases.ResolutionM11

@[expose] public section

/-!
# Block-preserving branch swaps with prescribed one-sheet overlap

This module contains the finite-set gauge move used by the first valency-four
candidate of Vargas, Part II.  Two positive sheet classes contained in one wall
block can be put in general position with intersection exactly one whenever
their cardinalities sum to at most one more than the wall-block cardinality.

The accompanying branch swap applies the resulting permutation on one target
branch.  It leaves the wall partition literally fixed and preserves validity.
-/

namespace DraismaVargas.LocalCases.BlockPreservingBranchSwap

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.ResolutionM11

variable {target : CFGraph} {degree : ℕ}

/-! ## The finite permutation -/

/-- Membership in the image of a finset under a transposition. -/
private theorem mem_image_swap {first second : Fin degree}
    (sheets : Finset (Fin degree)) (sheet : Fin degree) :
    sheet ∈ sheets.image (Equiv.swap first second) ↔
      (Equiv.swap first second) sheet ∈ sheets := by
  classical
  constructor
  · intro hMem
    obtain ⟨source, hSource, rfl⟩ := Finset.mem_image.mp hMem
    simpa using hSource
  · intro hMem
    exact Finset.mem_image.mpr
      ⟨(Equiv.swap first second) sheet, hMem, by simp⟩

private theorem exists_perm_image_inter_card_one_aux
    (whole small : Finset (Fin degree))
    (hSmall : small ⊆ whole) (hSmallPos : 0 < small.card) :
    ∀ steps (other : Finset (Fin degree)),
      (small ∩ other).card ≤ steps + 1 →
      other ⊆ whole → 0 < other.card →
      small.card + other.card ≤ whole.card + 1 →
      ∃ permutation : Equiv.Perm (Fin degree),
        (∀ sheet ∈ whole, permutation sheet ∈ whole) ∧
          (∀ sheet, sheet ∉ whole → permutation sheet = sheet) ∧
          (small ∩ other.image permutation).card = 1 := by
  classical
  intro steps
  induction steps with
  | zero =>
      intro other hLe hOther hOtherPos _hSum
      have hInterLe : (small ∩ other).card ≤ 1 := by omega
      by_cases hInterZero : (small ∩ other).card = 0
      · have hDisjoint : Disjoint small other := by
          rw [Finset.disjoint_iff_inter_eq_empty]
          exact Finset.card_eq_zero.mp hInterZero
        obtain ⟨first, hFirst⟩ := Finset.card_pos.mp hSmallPos
        obtain ⟨second, hSecond⟩ := Finset.card_pos.mp hOtherPos
        have hFirstWhole : first ∈ whole := hSmall hFirst
        have hSecondWhole : second ∈ whole := hOther hSecond
        have hFirstNotOther : first ∉ other := by
          exact Finset.disjoint_left.mp hDisjoint hFirst
        have hSecondNotSmall : second ∉ small := by
          exact Finset.disjoint_right.mp hDisjoint hSecond
        have hNe : first ≠ second := by
          rintro rfl
          exact hFirstNotOther hSecond
        refine ⟨Equiv.swap first second, ?_, ?_, ?_⟩
        · intro sheet hSheet
          rw [Equiv.swap_apply_def]
          split_ifs
          · exact hSecondWhole
          · exact hFirstWhole
          · exact hSheet
        · intro sheet hSheet
          apply Equiv.swap_apply_of_ne_of_ne
          · rintro rfl
            exact hSheet hFirstWhole
          · rintro rfl
            exact hSheet hSecondWhole
        · have hIntersection :
              small ∩ other.image (Equiv.swap first second) = {first} := by
            ext sheet
            simp only [Finset.mem_inter, mem_image_swap, Finset.mem_singleton]
            constructor
            · rintro ⟨hSheetSmall, hSheetOther⟩
              by_cases hFirst : sheet = first
              · exact hFirst
              have hSecond : sheet ≠ second := by
                rintro rfl
                exact hSecondNotSmall hSheetSmall
              rw [Equiv.swap_apply_of_ne_of_ne hFirst hSecond] at hSheetOther
              exact (Finset.disjoint_left.mp hDisjoint hSheetSmall hSheetOther).elim
            · rintro rfl
              exact ⟨hFirst, by simpa using hSecond⟩
          rw [hIntersection]
          simp
      · refine ⟨Equiv.refl _, fun _ h ↦ h, fun _ _ ↦ rfl, ?_⟩
        have hImage : other.image (Equiv.refl _) = other := by
          ext sheet
          simp
        rw [hImage]
        omega
  | succ steps ih =>
      intro other hLe hOther hOtherPos hSum
      by_cases hSmallInter : (small ∩ other).card ≤ 1
      · exact ih other (by omega) hOther hOtherPos hSum
      · have hInterTwo : 2 ≤ (small ∩ other).card := by omega
        obtain ⟨shared, hShared⟩ :=
          Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) hInterTwo)
        have hSharedSmall : shared ∈ small := (Finset.mem_inter.mp hShared).1
        have hSharedOther : shared ∈ other := (Finset.mem_inter.mp hShared).2
        have hUnionSub : small ∪ other ⊆ whole :=
          Finset.union_subset hSmall hOther
        have hUnionCard := Finset.card_union_add_card_inter small other
        have hFreeExists : (whole \ (small ∪ other)).Nonempty := by
          rw [← Finset.card_pos, Finset.card_sdiff,
            Finset.inter_eq_left.mpr hUnionSub]
          omega
        obtain ⟨free, hFree⟩ := hFreeExists
        have hFreeWhole : free ∈ whole := (Finset.mem_sdiff.mp hFree).1
        have hFreeNot : free ∉ small ∪ other := (Finset.mem_sdiff.mp hFree).2
        have hFreeSmall : free ∉ small :=
          fun h ↦ hFreeNot (Finset.mem_union_left _ h)
        have hFreeOther : free ∉ other :=
          fun h ↦ hFreeNot (Finset.mem_union_right _ h)
        have hSharedWhole : shared ∈ whole := hSmall hSharedSmall
        have hStepWhole : ∀ sheet, sheet ∈ whole →
            (Equiv.swap free shared) sheet ∈ whole := by
          intro sheet hSheet
          rw [Equiv.swap_apply_def]
          split_ifs
          · exact hSharedWhole
          · exact hFreeWhole
          · exact hSheet
        have hStepOut : ∀ sheet, sheet ∉ whole →
            (Equiv.swap free shared) sheet = sheet := by
          intro sheet hSheet
          apply Equiv.swap_apply_of_ne_of_ne
          · rintro rfl
            exact hSheet hFreeWhole
          · rintro rfl
            exact hSheet hSharedWhole
        let next := other.image (Equiv.swap free shared)
        have hNextSub : next ⊆ whole := by
          intro sheet hSheet
          obtain ⟨source, hSource, rfl⟩ := Finset.mem_image.mp hSheet
          exact hStepWhole source (hOther hSource)
        have hNextCard : next.card = other.card :=
          Finset.card_image_of_injective _ (Equiv.injective _)
        have hNextInter :
            small ∩ next = (small ∩ other).erase shared := by
          ext sheet
          simp only [next, Finset.mem_inter, Finset.mem_erase, mem_image_swap]
          constructor
          · rintro ⟨hSheetSmall, hSheetOther⟩
            have hNeShared : sheet ≠ shared := by
              rintro rfl
              rw [Equiv.swap_apply_right] at hSheetOther
              exact hFreeOther hSheetOther
            have hNeFree : sheet ≠ free :=
              fun h ↦ hFreeSmall (h ▸ hSheetSmall)
            exact ⟨hNeShared, hSheetSmall, by
              rwa [Equiv.swap_apply_of_ne_of_ne hNeFree hNeShared] at hSheetOther⟩
          · rintro ⟨hNeShared, hSheetSmall, hSheetOther⟩
            have hNeFree : sheet ≠ free :=
              fun h ↦ hFreeSmall (h ▸ hSheetSmall)
            exact ⟨hSheetSmall, by
              rwa [Equiv.swap_apply_of_ne_of_ne hNeFree hNeShared]⟩
        have hNextLe : (small ∩ next).card ≤ steps + 1 := by
          rw [hNextInter, Finset.card_erase_of_mem hShared]
          omega
        obtain ⟨rest, hRestWhole, hRestOut, hRestInter⟩ :=
          ih next hNextLe hNextSub (by omega) (by omega)
        refine ⟨(Equiv.swap free shared).trans rest, ?_, ?_, ?_⟩
        · intro sheet hSheet
          exact hRestWhole _ (hStepWhole sheet hSheet)
        · intro sheet hSheet
          simp only [Equiv.trans_apply]
          rw [hStepOut sheet hSheet]
          exact hRestOut sheet hSheet
        · have hImage :
              other.image ((Equiv.swap free shared).trans rest) =
                next.image rest := by
            rw [Finset.image_image]
            rfl
          rw [hImage]
          exact hRestInter

/-- Two positive subsets of one finite wall block can be moved to meet in
exactly one sheet whenever their sizes sum to at most `|A| + 1`.  The
permutation preserves `A` and fixes every sheet outside it. -/
theorem exists_perm_image_inter_card_one
    (whole small other : Finset (Fin degree))
    (hSmall : small ⊆ whole) (hOther : other ⊆ whole)
    (hSmallPos : 0 < small.card) (hOtherPos : 0 < other.card)
    (hCard : small.card + other.card ≤ whole.card + 1) :
    ∃ permutation : Equiv.Perm (Fin degree),
      (∀ sheet ∈ whole, permutation sheet ∈ whole) ∧
        (∀ sheet, sheet ∉ whole → permutation sheet = sheet) ∧
        (small ∩ other.image permutation).card = 1 := by
  exact exists_perm_image_inter_card_one_aux whole small hSmall hSmallPos
    (small ∩ other).card other (by omega) hOther hOtherPos hCard

/-! ## Applying the permutation on one target branch -/

/-- Apply one wall-block-preserving permutation throughout the component of
`root` in the target with `wall` deleted. -/
def branchSwapOfPerm (data : GluingDatum target degree)
    (wall root : target.V) (hRoot : root ≠ wall)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel
      (permutation sheet) sheet) : data.SheetRelabeling :=
  GluingDatum.SheetRelabeling.ofRegion
    (TargetBranchRegion.vertexMoved wall root hRoot)
    (TargetBranchRegion.edgeMoved wall root hRoot)
    permutation
    (fun edge hDifferent sheet ↦ by
      rw [TargetBranchRegion.boundary_left wall root hRoot edge hDifferent]
      exact hFix sheet)
    (fun edge hDifferent sheet ↦ by
      rw [TargetBranchRegion.boundary_right wall root hRoot edge hDifferent]
      exact hFix sheet)

theorem branchSwapOfPerm_vertexPartition_wall
    (data : GluingDatum target degree) (wall root : target.V)
    (hRoot : root ≠ wall) (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel
      (permutation sheet) sheet) :
    (branchSwapOfPerm data wall root hRoot permutation hFix).apply.vertexPartition
        wall = data.vertexPartition wall := by
  change (data.vertexPartition wall).relabel
    (GluingDatum.SheetRelabeling.togglePermutation
      (TargetBranchRegion.vertexMoved wall root hRoot wall) permutation) = _
  rw [TargetBranchRegion.vertexMoved_wall]
  cases hPartition : data.vertexPartition wall
  rfl

theorem branchSwapOfPerm_edgePartition_of_fixed
    (data : GluingDatum target degree) (wall root : target.V)
    (hRoot : root ≠ wall) (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel
      (permutation sheet) sheet) (edge : target.edges)
    (hFixed : TargetBranchRegion.edgeMoved wall root hRoot edge = false) :
    (branchSwapOfPerm data wall root hRoot permutation hFix).apply.edgePartition
        edge = data.edgePartition edge := by
  change (data.edgePartition edge).relabel
    (GluingDatum.SheetRelabeling.togglePermutation
      (TargetBranchRegion.edgeMoved wall root hRoot edge) permutation) = _
  rw [hFixed]
  cases hPartition : data.edgePartition edge
  rfl

theorem branchSwapOfPerm_edgePartition_of_moved
    (data : GluingDatum target degree) (wall root : target.V)
    (hRoot : root ≠ wall) (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel
      (permutation sheet) sheet) (edge : target.edges)
    (hMoved : TargetBranchRegion.edgeMoved wall root hRoot edge = true) :
    (branchSwapOfPerm data wall root hRoot permutation hFix).apply.edgePartition
        edge = (data.edgePartition edge).relabel permutation := by
  change (data.edgePartition edge).relabel
    (GluingDatum.SheetRelabeling.togglePermutation
      (TargetBranchRegion.edgeMoved wall root hRoot edge) permutation) = _
  rw [hMoved]
  rfl

/-- A permutation preserving one wall block and fixing its complement moves
every sheet inside its old wall block. -/
theorem rel_of_stabilizes_block (partition : SheetPartition degree)
    (anchor : Fin degree) (permutation : Equiv.Perm (Fin degree))
    (hInside : ∀ sheet ∈ partition.block anchor,
      permutation sheet ∈ partition.block anchor)
    (hOutside : ∀ sheet, sheet ∉ partition.block anchor →
      permutation sheet = sheet) (sheet : Fin degree) :
    partition.Rel (permutation sheet) sheet := by
  by_cases hMem : sheet ∈ partition.block anchor
  · exact ((partition.mem_block_iff anchor _).mp (hInside sheet hMem)).symm.trans
      ((partition.mem_block_iff anchor sheet).mp hMem)
  · rw [hOutside sheet hMem]
    exact rfl

end DraismaVargas.LocalCases.BlockPreservingBranchSwap
