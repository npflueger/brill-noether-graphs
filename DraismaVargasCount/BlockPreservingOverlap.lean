import DraismaVargas.LocalCases.BlockPreservingBranchSwap

/-!
# Block-preserving branch swaps with prescribed overlap of any size

`BlockPreservingBranchSwap.exists_perm_image_inter_card_one` produces a
wall-block-preserving permutation putting two subsets of one wall block in
intersection exactly **one**.  That is the `K = 0` instance of the construction
in the valency-four case of Vargas, Part II (arXiv:2609.09109,
`subsec-case-v4`), whose regrowths are parametrised by an integer `K ≥ 0` with
`|A_minus| = k_alpha + k_beta - 1 - K`.  That equation is equivalent to
`|e_alpha ∩ e_beta| = K + 1`, so the general construction needs a prescribed
overlap `overlap = K + 1`.

This module widens the combinatorial core to an arbitrary target overlap.  It
feeds the valency-four type changes (step 3 of
`DraismaVargasCount/Assembly.lean`) through `GeneralKReceipts`.
The feasibility condition is the set-theoretic one:

    max (0, small.card + other.card - whole.card) ≤ overlap ≤ min small.card other.card

stated as the three hypotheses `overlap ≤ small.card`, `overlap ≤ other.card`
and `small.card + other.card ≤ whole.card + overlap`.  Note that the positivity
hypotheses `0 < small.card`, `0 < other.card` of the `K = 0` theorem
are literally the `overlap = 1` instance of the first two, so this is a
widening of that theorem and not a different statement;
`exists_perm_image_inter_card_eq_one` below reproves it from the general form.

The proof is a single induction on a step budget for `|card - overlap|`.  Each
step moves the overlap one closer to the target by one transposition inside
`whole`:

* too large: swap a shared sheet with a sheet free of `small ∪ other`, which
  exists because `small.card + other.card ≤ whole.card + overlap` and
  `overlap < (small ∩ other).card` force `(small ∪ other).card < whole.card`;
* too small: swap a sheet of `small \ other` with a sheet of `other \ small`,
  both nonempty because the overlap is below `overlap ≤ min small.card
  other.card`.
-/

namespace DraismaVargas.LocalCases.BlockPreservingOverlap

open DraismaVargas.Infrastructure

variable {degree : ℕ}

/-! ## The finite permutation with prescribed overlap -/

/-- Membership in the image of a finset under a transposition.  (A private
copy of `BlockPreservingBranchSwap.mem_image_swap`, which is private there.) -/
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

/-- The step-budget induction.  `steps` bounds the distance from the current
overlap to the target overlap in both directions; each recursive call spends
one step and one transposition. -/
private theorem exists_perm_image_inter_card_eq_aux
    (whole small : Finset (Fin degree)) (overlap : ℕ)
    (hSmall : small ⊆ whole) (hSmallLe : overlap ≤ small.card) :
    ∀ steps (other : Finset (Fin degree)),
      other ⊆ whole → overlap ≤ other.card →
      small.card + other.card ≤ whole.card + overlap →
      (small ∩ other).card ≤ overlap + steps →
      overlap ≤ (small ∩ other).card + steps →
      ∃ permutation : Equiv.Perm (Fin degree),
        (∀ sheet ∈ whole, permutation sheet ∈ whole) ∧
          (∀ sheet, sheet ∉ whole → permutation sheet = sheet) ∧
          (small ∩ other.image permutation).card = overlap := by
  classical
  intro steps
  induction steps with
  | zero =>
      intro other _hOther _hOtherLe _hSum hUpper hLower
      refine ⟨Equiv.refl _, fun _ h ↦ h, fun _ _ ↦ rfl, ?_⟩
      have hImage : other.image (Equiv.refl (Fin degree)) = other := by
        ext sheet
        simp
      rw [hImage]
      omega
  | succ steps ih =>
      intro other hOther hOtherLe hSum hUpper hLower
      rcases lt_trichotomy (small ∩ other).card overlap with hLt | hEq | hGt
      · -- The overlap is too small: import one sheet of `small` into the image.
        have hSmallDiff : (small \ other).Nonempty := by
          rw [Finset.sdiff_nonempty]
          intro hSubset
          rw [Finset.inter_eq_left.mpr hSubset] at hLt
          omega
        have hOtherDiff : (other \ small).Nonempty := by
          rw [Finset.sdiff_nonempty]
          intro hSubset
          rw [Finset.inter_eq_right.mpr hSubset] at hLt
          omega
        obtain ⟨fresh, hFresh⟩ := hSmallDiff
        obtain ⟨drop, hDrop⟩ := hOtherDiff
        have hFreshSmall : fresh ∈ small := (Finset.mem_sdiff.mp hFresh).1
        have hFreshOther : fresh ∉ other := (Finset.mem_sdiff.mp hFresh).2
        have hDropOther : drop ∈ other := (Finset.mem_sdiff.mp hDrop).1
        have hDropSmall : drop ∉ small := (Finset.mem_sdiff.mp hDrop).2
        have hFreshWhole : fresh ∈ whole := hSmall hFreshSmall
        have hDropWhole : drop ∈ whole := hOther hDropOther
        have hStepWhole : ∀ sheet, sheet ∈ whole →
            (Equiv.swap fresh drop) sheet ∈ whole := by
          intro sheet hSheet
          rw [Equiv.swap_apply_def]
          split_ifs
          · exact hDropWhole
          · exact hFreshWhole
          · exact hSheet
        have hStepOut : ∀ sheet, sheet ∉ whole →
            (Equiv.swap fresh drop) sheet = sheet := by
          intro sheet hSheet
          apply Equiv.swap_apply_of_ne_of_ne
          · rintro rfl
            exact hSheet hFreshWhole
          · rintro rfl
            exact hSheet hDropWhole
        let next := other.image (Equiv.swap fresh drop)
        have hNextSub : next ⊆ whole := by
          intro sheet hSheet
          obtain ⟨origin, hOrigin, rfl⟩ := Finset.mem_image.mp hSheet
          exact hStepWhole origin (hOther hOrigin)
        have hNextCard : next.card = other.card :=
          Finset.card_image_of_injective _ (Equiv.injective _)
        have hNextInter : small ∩ next = insert fresh (small ∩ other) := by
          ext sheet
          simp only [next, Finset.mem_inter, Finset.mem_insert, mem_image_swap]
          constructor
          · rintro ⟨hSheetSmall, hSheetOther⟩
            by_cases hIsFresh : sheet = fresh
            · exact Or.inl hIsFresh
            · have hNeDrop : sheet ≠ drop :=
                fun hEq ↦ hDropSmall (hEq ▸ hSheetSmall)
              rw [Equiv.swap_apply_of_ne_of_ne hIsFresh hNeDrop] at hSheetOther
              exact Or.inr ⟨hSheetSmall, hSheetOther⟩
          · rintro (rfl | ⟨hSheetSmall, hSheetOther⟩)
            · exact ⟨hFreshSmall, by rw [Equiv.swap_apply_left]; exact hDropOther⟩
            · have hIsFresh : sheet ≠ fresh :=
                fun hEq ↦ hFreshOther (hEq ▸ hSheetOther)
              have hNeDrop : sheet ≠ drop :=
                fun hEq ↦ hDropSmall (hEq ▸ hSheetSmall)
              refine ⟨hSheetSmall, ?_⟩
              rw [Equiv.swap_apply_of_ne_of_ne hIsFresh hNeDrop]
              exact hSheetOther
        have hNextInterCard : (small ∩ next).card = (small ∩ other).card + 1 := by
          rw [hNextInter, Finset.card_insert_of_notMem (by simp [hFreshOther])]
        obtain ⟨rest, hRestWhole, hRestOut, hRestInter⟩ :=
          ih next hNextSub (by omega) (by omega) (by omega) (by omega)
        refine ⟨(Equiv.swap fresh drop).trans rest, ?_, ?_, ?_⟩
        · intro sheet hSheet
          exact hRestWhole _ (hStepWhole sheet hSheet)
        · intro sheet hSheet
          simp only [Equiv.trans_apply]
          rw [hStepOut sheet hSheet]
          exact hRestOut sheet hSheet
        · have hImage :
              other.image ((Equiv.swap fresh drop).trans rest) =
                next.image rest := by
            rw [Finset.image_image]
            rfl
          rw [hImage]
          exact hRestInter
      · exact ih other hOther hOtherLe hSum (by omega) (by omega)
      · -- The overlap is too large: export one shared sheet to a free sheet.
        obtain ⟨shared, hShared⟩ :=
          Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le overlap) hGt)
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
          fun hMem ↦ hFreeNot (Finset.mem_union_left _ hMem)
        have hFreeOther : free ∉ other :=
          fun hMem ↦ hFreeNot (Finset.mem_union_right _ hMem)
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
          obtain ⟨origin, hOrigin, rfl⟩ := Finset.mem_image.mp hSheet
          exact hStepWhole origin (hOther hOrigin)
        have hNextCard : next.card = other.card :=
          Finset.card_image_of_injective _ (Equiv.injective _)
        have hNextInter : small ∩ next = (small ∩ other).erase shared := by
          ext sheet
          simp only [next, Finset.mem_inter, Finset.mem_erase, mem_image_swap]
          constructor
          · rintro ⟨hSheetSmall, hSheetOther⟩
            have hNeShared : sheet ≠ shared := by
              rintro rfl
              rw [Equiv.swap_apply_right] at hSheetOther
              exact hFreeOther hSheetOther
            have hNeFree : sheet ≠ free :=
              fun hEq ↦ hFreeSmall (hEq ▸ hSheetSmall)
            exact ⟨hNeShared, hSheetSmall, by
              rwa [Equiv.swap_apply_of_ne_of_ne hNeFree hNeShared] at hSheetOther⟩
          · rintro ⟨hNeShared, hSheetSmall, hSheetOther⟩
            have hNeFree : sheet ≠ free :=
              fun hEq ↦ hFreeSmall (hEq ▸ hSheetSmall)
            exact ⟨hSheetSmall, by
              rwa [Equiv.swap_apply_of_ne_of_ne hNeFree hNeShared]⟩
        have hNextInterCard :
            (small ∩ next).card + 1 = (small ∩ other).card := by
          rw [hNextInter, Finset.card_erase_of_mem hShared]
          omega
        obtain ⟨rest, hRestWhole, hRestOut, hRestInter⟩ :=
          ih next hNextSub (by omega) (by omega) (by omega) (by omega)
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

/-- **Layer 1.**  Two subsets of one finite wall block can be moved to meet in
exactly `overlap` sheets whenever the set-theoretic feasibility condition
`max (0, small.card + other.card - whole.card) ≤ overlap ≤
min small.card other.card` holds.  The permutation preserves `whole` and fixes
every sheet outside it.

At `overlap = 1` this is
`BlockPreservingBranchSwap.exists_perm_image_inter_card_one`; see
`exists_perm_image_inter_card_eq_one`. -/
theorem exists_perm_image_inter_card_eq
    (whole small other : Finset (Fin degree)) (overlap : ℕ)
    (hSmall : small ⊆ whole) (hOther : other ⊆ whole)
    (hSmallLe : overlap ≤ small.card) (hOtherLe : overlap ≤ other.card)
    (hCard : small.card + other.card ≤ whole.card + overlap) :
    ∃ permutation : Equiv.Perm (Fin degree),
      (∀ sheet ∈ whole, permutation sheet ∈ whole) ∧
        (∀ sheet, sheet ∉ whole → permutation sheet = sheet) ∧
        (small ∩ other.image permutation).card = overlap :=
  exists_perm_image_inter_card_eq_aux whole small overlap hSmall hSmallLe
    ((small ∩ other).card + overlap) other hOther hOtherLe hCard
    (by omega) (by omega)

/-- The `overlap = 1` corollary: the statement of
`BlockPreservingBranchSwap.exists_perm_image_inter_card_one`, reproved from the
general form.  The positivity hypotheses there are exactly the `overlap = 1`
instance of `overlap ≤ small.card` and `overlap ≤ other.card`. -/
theorem exists_perm_image_inter_card_eq_one
    (whole small other : Finset (Fin degree))
    (hSmall : small ⊆ whole) (hOther : other ⊆ whole)
    (hSmallPos : 0 < small.card) (hOtherPos : 0 < other.card)
    (hCard : small.card + other.card ≤ whole.card + 1) :
    ∃ permutation : Equiv.Perm (Fin degree),
      (∀ sheet ∈ whole, permutation sheet ∈ whole) ∧
        (∀ sheet, sheet ∉ whole → permutation sheet = sheet) ∧
        (small ∩ other.image permutation).card = 1 :=
  exists_perm_image_inter_card_eq whole small other 1 hSmall hOther
    hSmallPos hOtherPos hCard

end DraismaVargas.LocalCases.BlockPreservingOverlap
