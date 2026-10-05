module

public import DraismaVargasCount.GeneralKResolution
public import DraismaVargasCount.BlockPreservingOverlap
public import DraismaVargas.LocalCases.SheetRelabelIncidence
public import DraismaVargasCount.GeometricTransport
public import DraismaVargas.LocalCases.M11SourceGenus

@[expose] public section

/-!
# The `K ≥ 1` local resolution receipts at a four-valent wall

A. Vargas, *Catalan-many tropical morphisms to trees; Part II: A space and a count*,
arXiv:2609.09109, subsection "Valency-4 limits: Case {v4-nd4}" (`subsec-case-v4`).

`GeneralKResolution` builds the general-`K` `LocalResolution` (`SplitData.resolution`) with its
contraction, `Refines` and Riemann--Hurwitz receipts, taking the gauge and the *joint*
cardinality condition as inputs.  This file supplies those inputs, installs the resolution into
an actual gauged gluing datum, and shows that every admissible `K` is realised.  It feeds the
valency-four case of the type-change step (step 3 of `DraismaVargasCount.Assembly`), through
`GeneralKExitSetup`.

## Main results

1. **The overlap gauge** (`overlapGauge_of_feasible`, `feasible_of_overlapGauge`,
   `overlapGauge_iff`): `GeneralKResolution.OverlapGauge` is *equivalent* to the three
   set-theoretic feasibility inequalities (compare `BlockPreservingOverlap`).
2. **The joint condition** (`exists_joint_gauge`, `exists_splitData_of_joint_gauge`,
   `exists_gauged_splitData`): with the first class fixed and the other **three** classes moved
   by block-preserving permutations, both overlaps (`K + 1` and `K' + 1`) and `A₋ ∪ A₊ = A` hold
   at once, so `exists_splitData_of_gauged_sides`'s hypotheses, including the joint
   `|A₋ ∩ A₊| + K + K' = |A|`, are all discharged.
3. **Strictness of the gauge** (`union_ne_whole_of_fixed_firsts`,
   `fy_pairingII_single_side_fails`, `fy_pairingII_joint_gauge`): gauging only the second class
   of each side (the shape of the `K = 0` relabelling) cannot reach the joint condition in
   general.  For the branch classes `{0,1},{0,2} | {0,1},{0,2}` of a three-sheet block at `K = 1`
   it fails for every choice, and the three-class joint gauge succeeds.
4. **The admissible range** (`Admissible`, `admissible_smallerSide_iff`,
   `admissible_smallerSide_iff_of_pairing`, `admissible_zero`, `admissible_of_position`,
   `admissible_iff_exists_position`): at the smaller side, `Admissible` is exactly
   `K + 1 ≤ min k` and `K + max k ≤ |A|`, which is Part II's range
   `0 ≤ K ≤ min(k₂-1, |A|-k₅)`.  It does not depend on the pairing, and it is exactly the set of
   `K` realised by a `Position`.
5. **The gauged datum** (`LabelGauge`, `LabelGauge.gaugedData`, `gaugedData_edgePartition`,
   `gaugedData_valid`): one block-preserving branch swap per star label, over a tree target.
   Each star occurrence is the incoming one relabelled by its own permutation.
6. **A general-`K` position and its receipts** (`Position`, `exists_position`,
   `refines_left/right`, `count_left/right`, `oldCount_left/right`,
   `riemannHurwitz_left/right`, `split_euler`, `selected_euler`,
   `datum_blockCard_eq_of_not_rel`): the old occurrences refine their endpoints.  Their induced
   counts add up to exactly `k₁ + 1`, which is `resolution_receipts`'s `hLeftOld`/`hRightOld`
   with equality.  The anchor block satisfies the blockwise Euler identity; the `K = 0` exit gets
   that identity from `IsStar`, which is false for `K ≥ 1`.
7. **Installation** (`PairingBackground`, `Position.candidate`, `candidate_datum_valid`,
   `candidate_resolution_anchor`, `candidate_K_receipts`, `candidate_newSourceEdge_index`,
   `candidate_sourceGenus`): over any guarded background of the other wall blocks, the installed
   candidate has the following properties.
   * It is a valid `BalancedGlobal.Candidate`.
   * It uses the general-`K` resolution on the anchor block.
   * It records `K + 1` and `K' + 1` as the new edge's induced counts at the bridge sheet.
   * Its new source edge has index `k₁ = k_α + k_β - 1 - 2K`.
   * It preserves the source genus, given the background's Euler identity.
8. **Headline** (`exists_position_of_range`): for every `K` in Part II's range a position exists
   at the smaller side.

## Scope

* **The background of the other wall blocks.**  `Position.candidate` takes a
  `PairingBackground`, and `candidate_sourceGenus` takes its Euler identity.  The `K = 0` exit
  produces both from `NonTrivalentValencyFourBackground.OrdinaryBlockProfile`
  (`blockLocalBackground`); `datum_blockCard_eq_of_not_rel` is the transport a port of that
  construction to `LabelGauge.gaugedData` would need.  The general-`K` exit instead uses a
  background localized to the anchor block (`GeneralKSourceFacts.LocalCanonicalBackground`).
* **Everything downstream of the candidate** -- trivalence of the outgoing source, the dangling
  behaviour of the `K` singleton new-edge occurrences, `HasPathEnds`, the outgoing
  `FullDimensionalSourcePresentation` with its row dictionary and `AgreeOffColumn`,
  `OuterWalk.TypeChangeLink`, and the regrowth and `FrameClass` it defines with that class's
  metric limit -- is proved downstream, in `GeneralKSourceFacts`, `GeneralKStarCount` and
  `ValencyFourRealisation`.  That two positions with the same `K` give isomorphic frames
  (`K`-rigidity) is `ValencyFourRigidity.kIndexL_injective_of_v4` and
  `ValencyFourRigidity.kIndexR_injective_of_v4`.
* **Uniqueness of the gauge.**  `exists_position` picks *some* gauge representative for each
  `K`; nothing here counts gauge classes.
* **The hypotheses that remain on the headlines:** `hNoGlue`, `hRamification` (identity
  `(square)`), and a connected genus-zero target (`hConnected`, `hGenus`) for the branch swaps.
  The `K = 0` exit carries the same ones, and at an actual wall they are discharged by
  `NonTrivalentUniqueFourValent`.
-/

set_option autoImplicit false

namespace DraismaVargas.Count.GeneralKReceipts

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.GeneralKResolution

variable {degree : ℕ}

/-- A permutation that preserves one wall block and fixes its complement. -/
def BlockPreserving (whole : Finset (Fin degree)) (permutation : Equiv.Perm (Fin degree)) :
    Prop :=
  (∀ sheet ∈ whole, permutation sheet ∈ whole) ∧
    (∀ sheet, sheet ∉ whole → permutation sheet = sheet)

theorem blockPreserving_refl (whole : Finset (Fin degree)) :
    BlockPreserving whole (Equiv.refl (Fin degree)) :=
  ⟨fun _ h ↦ h, fun _ _ ↦ rfl⟩

theorem BlockPreserving.image_subset {whole sheets : Finset (Fin degree)}
    {permutation : Equiv.Perm (Fin degree)} (hPerm : BlockPreserving whole permutation)
    (hSheets : sheets ⊆ whole) : sheets.image permutation ⊆ whole := by
  intro sheet hSheet
  obtain ⟨original, hOriginal, rfl⟩ := Finset.mem_image.mp hSheet
  exact hPerm.1 original (hSheets hOriginal)

theorem BlockPreserving.symm_mem {whole : Finset (Fin degree)}
    {permutation : Equiv.Perm (Fin degree)} (hPerm : BlockPreserving whole permutation)
    {sheet : Fin degree} (hSheet : sheet ∈ whole) : permutation.symm sheet ∈ whole := by
  by_contra hOutside
  have hFixed := hPerm.2 (permutation.symm sheet) hOutside
  rw [Equiv.apply_symm_apply] at hFixed
  exact hOutside (hFixed ▸ hSheet)

/-! ## 1.  The overlap gauge -/

/-- **The overlap gauge, sufficiency.**  The widened overlap gauge exists under the
set-theoretic feasibility conditions. -/
theorem overlapGauge_of_feasible {whole first second : Finset (Fin degree)} {overlap : ℕ}
    (hFirst : first ⊆ whole) (hSecond : second ⊆ whole)
    (hFirstLe : overlap ≤ first.card) (hSecondLe : overlap ≤ second.card)
    (hCard : first.card + second.card ≤ whole.card + overlap) :
    OverlapGauge whole first second overlap :=
  BlockPreservingOverlap.exists_perm_image_inter_card_eq whole first second overlap
    hFirst hSecond hFirstLe hSecondLe hCard

/-- **The overlap gauge, necessity.** -/
theorem feasible_of_overlapGauge {whole first second : Finset (Fin degree)} {overlap : ℕ}
    (hFirst : first ⊆ whole) (hSecond : second ⊆ whole)
    (hGauge : OverlapGauge whole first second overlap) :
    overlap ≤ first.card ∧ overlap ≤ second.card ∧
      first.card + second.card ≤ whole.card + overlap := by
  obtain ⟨permutation, hInside, hOutside, hOverlap⟩ := hGauge
  have hImage : (second.image permutation).card = second.card :=
    Finset.card_image_of_injective _ permutation.injective
  have hSub : first ∪ second.image permutation ⊆ whole :=
    Finset.union_subset hFirst
      (BlockPreserving.image_subset ⟨hInside, hOutside⟩ hSecond)
  have hUnion := Finset.card_union_add_card_inter first (second.image permutation)
  have hLe := Finset.card_le_card hSub
  have hInterLeft := Finset.card_le_card
    (Finset.inter_subset_left : first ∩ second.image permutation ⊆ first)
  have hInterRight := Finset.card_le_card
    (Finset.inter_subset_right : first ∩ second.image permutation ⊆ second.image permutation)
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- **The overlap gauge as an interface.**  `OverlapGauge` is equivalent to the three
feasibility inequalities. -/
theorem overlapGauge_iff {whole first second : Finset (Fin degree)} {overlap : ℕ}
    (hFirst : first ⊆ whole) (hSecond : second ⊆ whole) :
    OverlapGauge whole first second overlap ↔
      overlap ≤ first.card ∧ overlap ≤ second.card ∧
        first.card + second.card ≤ whole.card + overlap :=
  ⟨feasible_of_overlapGauge hFirst hSecond,
    fun h ↦ overlapGauge_of_feasible hFirst hSecond h.1 h.2.1 h.2.2⟩

/-- Any two subsets of one block with the same cardinality are related by a
block-preserving permutation. -/
theorem exists_blockPreserving_image_eq {whole source goal : Finset (Fin degree)}
    (hSource : source ⊆ whole) (hGoal : goal ⊆ whole) (hCard : source.card = goal.card) :
    ∃ permutation : Equiv.Perm (Fin degree),
      BlockPreserving whole permutation ∧ source.image permutation = goal := by
  have hGoalLe := Finset.card_le_card hGoal
  obtain ⟨permutation, hInside, hOutside, hOverlap⟩ :=
    BlockPreservingOverlap.exists_perm_image_inter_card_eq whole goal source goal.card
      hGoal hSource le_rfl (by omega) (by omega)
  refine ⟨permutation, ⟨hInside, hOutside⟩, ?_⟩
  have hImage : (source.image permutation).card = goal.card := by
    rw [Finset.card_image_of_injective _ permutation.injective]
    exact hCard
  have hInterEq : goal ∩ source.image permutation = goal :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have hGoalSub : goal ⊆ source.image permutation := by
    rw [← hInterEq]
    exact Finset.inter_subset_right
  exact (Finset.eq_of_subset_of_card_le hGoalSub (by omega)).symm

/-! ## 2.  The joint condition -/

/-- **The joint gauge.**  Four branch classes inside one wall block, the first
one unmoved.  If each side is feasible for its own overlap (`K + 1` on the
minus side, `coK + 1` on the plus side) and the two sides have the paper's
cardinalities `|A₋| = |A| - coK`, `|A₊| = |A| - K`, then three block-preserving
permutations (on the second, third and fourth class) realise both overlaps
**and** make the two endpoint sets exhaust the block. -/
theorem exists_joint_gauge {whole first second third fourth : Finset (Fin degree)}
    {K coK : ℕ}
    (hFirst : first ⊆ whole) (hSecond : second ⊆ whole)
    (hThird : third ⊆ whole) (hFourth : fourth ⊆ whole)
    (hFirstK : K + 1 ≤ first.card) (hSecondK : K + 1 ≤ second.card)
    (hThirdK : coK + 1 ≤ third.card) (hFourthK : coK + 1 ≤ fourth.card)
    (hMinus : first.card + second.card + coK = whole.card + K + 1)
    (hPlus : third.card + fourth.card + K = whole.card + coK + 1) :
    ∃ secondPerm thirdPerm fourthPerm : Equiv.Perm (Fin degree),
      BlockPreserving whole secondPerm ∧ BlockPreserving whole thirdPerm ∧
        BlockPreserving whole fourthPerm ∧
        (first ∩ second.image secondPerm).card = K + 1 ∧
        (third.image thirdPerm ∩ fourth.image fourthPerm).card = coK + 1 ∧
        (first ∪ second.image secondPerm) ∪
            (third.image thirdPerm ∪ fourth.image fourthPerm) = whole := by
  classical
  -- the minus side
  obtain ⟨secondPerm, hSecondInside, hSecondOutside, hSecondOverlap⟩ :=
    BlockPreservingOverlap.exists_perm_image_inter_card_eq whole first second (K + 1)
      hFirst hSecond hFirstK hSecondK (by omega)
  have hSecondPerm : BlockPreserving whole secondPerm := ⟨hSecondInside, hSecondOutside⟩
  have hSecondImage : (second.image secondPerm).card = second.card :=
    Finset.card_image_of_injective _ secondPerm.injective
  have hMinusSub : first ∪ second.image secondPerm ⊆ whole :=
    Finset.union_subset hFirst (hSecondPerm.image_subset hSecond)
  have hMinusCard : (first ∪ second.image secondPerm).card + coK = whole.card := by
    have hUnion := Finset.card_union_add_card_inter first (second.image secondPerm)
    omega
  have hFirstLeMinus : first.card ≤ (first ∪ second.image secondPerm).card :=
    Finset.card_le_card Finset.subset_union_left
  set minus := first ∪ second.image secondPerm with hMinusDef
  -- the rest of the block, and the plus-side target set
  set rest := whole \ minus with hRestDef
  have hRestCard : rest.card = coK := by
    rw [hRestDef, Finset.card_sdiff_of_subset hMinusSub]
    omega
  obtain ⟨shared, hSharedSub, hSharedCard⟩ :=
    Finset.exists_subset_card_eq (s := minus) (n := minus.card - K) (by omega)
  set plus := rest ∪ shared with hPlusDef
  have hDisjoint : Disjoint rest shared := by
    rw [Finset.disjoint_left]
    intro sheet hRest hShared
    exact (Finset.mem_sdiff.mp hRest).2 (hSharedSub hShared)
  have hPlusCard : plus.card + K = whole.card := by
    rw [hPlusDef, Finset.card_union_of_disjoint hDisjoint]
    omega
  have hPlusSub : plus ⊆ whole :=
    Finset.union_subset Finset.sdiff_subset (hSharedSub.trans hMinusSub)
  -- the two plus-side goal sets
  obtain ⟨thirdGoal, hThirdGoalSub, hThirdGoalCard⟩ :=
    Finset.exists_subset_card_eq (s := plus) (n := third.card) (by omega)
  obtain ⟨common, hCommonSub, hCommonCard⟩ :=
    Finset.exists_subset_card_eq (s := thirdGoal) (n := coK + 1) (by omega)
  set fourthGoal := (plus \ thirdGoal) ∪ common with hFourthGoalDef
  have hGoalDisjoint : Disjoint (plus \ thirdGoal) common := by
    rw [Finset.disjoint_left]
    intro sheet hOut hCommon
    exact (Finset.mem_sdiff.mp hOut).2 (hCommonSub hCommon)
  have hFourthGoalCard : fourthGoal.card = fourth.card := by
    rw [hFourthGoalDef, Finset.card_union_of_disjoint hGoalDisjoint,
      Finset.card_sdiff_of_subset hThirdGoalSub]
    omega
  have hFourthGoalSub : fourthGoal ⊆ plus :=
    Finset.union_subset Finset.sdiff_subset (hCommonSub.trans hThirdGoalSub)
  obtain ⟨thirdPerm, hThirdPerm, hThirdImage⟩ :=
    exists_blockPreserving_image_eq hThird (hThirdGoalSub.trans hPlusSub)
      hThirdGoalCard.symm
  obtain ⟨fourthPerm, hFourthPerm, hFourthImage⟩ :=
    exists_blockPreserving_image_eq hFourth (hFourthGoalSub.trans hPlusSub)
      hFourthGoalCard.symm
  refine ⟨secondPerm, thirdPerm, fourthPerm, hSecondPerm, hThirdPerm, hFourthPerm,
    hSecondOverlap, ?_, ?_⟩
  · rw [hThirdImage, hFourthImage]
    have hInter : thirdGoal ∩ fourthGoal = common := by
      ext sheet
      simp only [hFourthGoalDef, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro ⟨hIn, hOut | hCommon⟩
        · exact absurd hIn hOut.2
        · exact hCommon
      · intro hCommon
        exact ⟨hCommonSub hCommon, Or.inr hCommon⟩
    rw [hInter, hCommonCard]
  · rw [hThirdImage, hFourthImage]
    have hPlusEq : thirdGoal ∪ fourthGoal = plus := by
      apply Finset.Subset.antisymm (Finset.union_subset hThirdGoalSub hFourthGoalSub)
      intro sheet hSheet
      by_cases hIn : sheet ∈ thirdGoal
      · exact Finset.mem_union_left _ hIn
      · exact Finset.mem_union_right _
          (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hSheet, hIn⟩))
    rw [hPlusEq]
    apply Finset.Subset.antisymm (Finset.union_subset hMinusSub hPlusSub)
    intro sheet hSheet
    by_cases hIn : sheet ∈ minus
    · exact Finset.mem_union_left _ hIn
    · exact Finset.mem_union_right _
        (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hSheet, hIn⟩))

/-- The joint gauge, read as the input of
`GeneralKResolution.exists_splitData_of_gauged_sides`: the per-side
cardinalities and the **joint** cardinality all hold, and a bridge sheet
exists. -/
theorem splitCards_of_joint {whole minus plus : Finset (Fin degree)} {K coK : ℕ}
    (hMinusCard : minus.card + coK = whole.card) (hPlusCard : plus.card + K = whole.card)
    (hUnion : minus ∪ plus = whole) (hMinusBig : K + 1 ≤ minus.card) :
    (minus ∩ plus).card + K + coK = whole.card ∧ (minus ∩ plus).Nonempty := by
  have hCount := Finset.card_union_add_card_inter minus plus
  rw [hUnion] at hCount
  refine ⟨by omega, ?_⟩
  rw [← Finset.card_pos]
  omega

/-- **The joint condition, discharged.**  From the four branch classes and the
two feasibility conditions, a `SplitData` over the wall block exists with the
prescribed `K` and `coK`, whose endpoint sets are the two gauged unions. -/
theorem exists_splitData_of_joint_gauge {coarse : SheetPartition degree} {anchor : Fin degree}
    {first second third fourth : Finset (Fin degree)} {K coK : ℕ}
    (hFirst : first ⊆ coarse.block anchor) (hSecond : second ⊆ coarse.block anchor)
    (hThird : third ⊆ coarse.block anchor) (hFourth : fourth ⊆ coarse.block anchor)
    (hFirstK : K + 1 ≤ first.card) (hSecondK : K + 1 ≤ second.card)
    (hThirdK : coK + 1 ≤ third.card) (hFourthK : coK + 1 ≤ fourth.card)
    (hMinus : first.card + second.card + coK = coarse.blockCard anchor + K + 1)
    (hPlus : third.card + fourth.card + K = coarse.blockCard anchor + coK + 1) :
    ∃ secondPerm thirdPerm fourthPerm : Equiv.Perm (Fin degree),
      BlockPreserving (coarse.block anchor) secondPerm ∧
        BlockPreserving (coarse.block anchor) thirdPerm ∧
        BlockPreserving (coarse.block anchor) fourthPerm ∧
        ∃ split : SplitData coarse anchor,
          split.minusSheets = first ∪ second.image secondPerm ∧
            split.plusSheets = third.image thirdPerm ∪ fourth.image fourthPerm ∧
            split.K = K ∧ split.coK = coK := by
  obtain ⟨secondPerm, thirdPerm, fourthPerm, hSecondPerm, hThirdPerm, hFourthPerm,
    hMinusOverlap, hPlusOverlap, hUnion⟩ :=
    exists_joint_gauge hFirst hSecond hThird hFourth hFirstK hSecondK hThirdK hFourthK
      hMinus hPlus
  have hBlockCard : (coarse.block anchor).card = coarse.blockCard anchor := rfl
  have hMinusSub : first ∪ second.image secondPerm ⊆ coarse.block anchor :=
    Finset.union_subset hFirst (hSecondPerm.image_subset hSecond)
  have hPlusSub : third.image thirdPerm ∪ fourth.image fourthPerm ⊆ coarse.block anchor :=
    Finset.union_subset (hThirdPerm.image_subset hThird)
      (hFourthPerm.image_subset hFourth)
  have hMinusCard :
      (first ∪ second.image secondPerm).card + coK = coarse.blockCard anchor := by
    have hImage : (second.image secondPerm).card = second.card :=
      Finset.card_image_of_injective _ secondPerm.injective
    have hCount := Finset.card_union_add_card_inter first (second.image secondPerm)
    omega
  have hPlusCard : (third.image thirdPerm ∪ fourth.image fourthPerm).card + K
      = coarse.blockCard anchor := by
    have hThirdImage : (third.image thirdPerm).card = third.card :=
      Finset.card_image_of_injective _ thirdPerm.injective
    have hFourthImage : (fourth.image fourthPerm).card = fourth.card :=
      Finset.card_image_of_injective _ fourthPerm.injective
    have hCount := Finset.card_union_add_card_inter (third.image thirdPerm)
      (fourth.image fourthPerm)
    omega
  have hMinusBig : K + 1 ≤ (first ∪ second.image secondPerm).card :=
    hFirstK.trans (Finset.card_le_card Finset.subset_union_left)
  obtain ⟨hJoint, bridge, hBridge⟩ :=
    splitCards_of_joint (hBlockCard ▸ hMinusCard)
      (hBlockCard ▸ hPlusCard) hUnion hMinusBig
  obtain ⟨split, _, hSplitMinus, hSplitPlus, hSplitK, hSplitcoK⟩ :=
    exists_splitData_of_gauged_sides (bridge := bridge) hMinusSub hPlusSub
      (Finset.mem_inter.mp hBridge).1 (Finset.mem_inter.mp hBridge).2 hMinusCard
      hPlusCard hJoint
  exact ⟨secondPerm, thirdPerm, fourthPerm, hSecondPerm, hThirdPerm, hFourthPerm,
    split, hSplitMinus, hSplitPlus, hSplitK, hSplitcoK⟩

/-! ### Strictness: one moved class per side is not enough -/

/-- A class meeting an equally large class in all its sheets *is* that class. -/
theorem eq_of_inter_card_eq {first other : Finset (Fin degree)}
    (hCard : other.card = first.card) (hInter : (first ∩ other).card = first.card) :
    other = first := by
  have hLeft : first ∩ other = first :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have hRight : first ∩ other = other :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
  rw [← hRight, hLeft]

/-- **The single-side gauge is not enough.**  If the gauge may move only the
*second* class on each side (as the `K = 0` relabelling does), then at a
presentation whose two first classes coincide the joint condition fails at
the top of the range: both sides collapse to the common first class, which
does not exhaust the block. -/
theorem union_ne_whole_of_fixed_firsts {whole first second third fourth : Finset (Fin degree)}
    {K coK : ℕ} (hSame : third = first)
    (hSecondCard : second.card = first.card) (hFourthCard : fourth.card = third.card)
    (hK : K + 1 = first.card) (hcoK : coK + 1 = third.card)
    (hSmall : first.card < whole.card)
    (secondPerm fourthPerm : Equiv.Perm (Fin degree))
    (hMinus : (first ∩ second.image secondPerm).card = K + 1)
    (hPlus : (third ∩ fourth.image fourthPerm).card = coK + 1) :
    (first ∪ second.image secondPerm) ∪ (third ∪ fourth.image fourthPerm) ≠ whole := by
  have hSecond : second.image secondPerm = first :=
    eq_of_inter_card_eq
      (by rw [Finset.card_image_of_injective _ secondPerm.injective]; exact hSecondCard)
      (by omega)
  have hFourth : fourth.image fourthPerm = third :=
    eq_of_inter_card_eq
      (by rw [Finset.card_image_of_injective _ fourthPerm.injective]; exact hFourthCard)
      (by omega)
  rw [hSecond, hFourth, hSame, Finset.union_self, Finset.union_self]
  intro hEq
  rw [hEq] at hSmall
  exact lt_irrefl _ hSmall

/-- A concrete instance: pairing II of a four-valent wall with profile
`(3; 2,2,2,2)`, as sheet sets -- the four branch classes
`{0,1}, {0,2} | {0,1}, {0,2}` in a three-sheet block, `K = 1`.  No gauge of the
two second classes realises the `K = 1` split. -/
theorem fy_pairingII_single_side_fails (secondPerm fourthPerm : Equiv.Perm (Fin 3))
    (hMinus : (({0, 1} : Finset (Fin 3)) ∩ ({0, 2} : Finset (Fin 3)).image secondPerm).card
      = 1 + 1)
    (hPlus : (({0, 1} : Finset (Fin 3)) ∩ ({0, 2} : Finset (Fin 3)).image fourthPerm).card
      = 1 + 1) :
    (({0, 1} : Finset (Fin 3)) ∪ ({0, 2} : Finset (Fin 3)).image secondPerm) ∪
        (({0, 1} : Finset (Fin 3)) ∪ ({0, 2} : Finset (Fin 3)).image fourthPerm)
      ≠ Finset.univ :=
  union_ne_whole_of_fixed_firsts rfl (by decide) (by decide) (by decide) (by decide)
    (by decide) secondPerm fourthPerm hMinus hPlus

/-- The same configuration **does** admit the `K = 1` split once the third
class may move too: the joint gauge of `exists_joint_gauge` exists there.  With
`fy_pairingII_single_side_fails` this is the Lean form of "positions for
`K ≥ 1` must be built over the right gauge representative". -/
theorem fy_pairingII_joint_gauge :
    ∃ secondPerm thirdPerm fourthPerm : Equiv.Perm (Fin 3),
      BlockPreserving Finset.univ secondPerm ∧ BlockPreserving Finset.univ thirdPerm ∧
        BlockPreserving Finset.univ fourthPerm ∧
        (({0, 1} : Finset (Fin 3)) ∩ ({0, 2} : Finset (Fin 3)).image secondPerm).card
          = 1 + 1 ∧
        ((({0, 1} : Finset (Fin 3)).image thirdPerm) ∩
            ({0, 2} : Finset (Fin 3)).image fourthPerm).card = 1 + 1 ∧
        (({0, 1} : Finset (Fin 3)) ∪ ({0, 2} : Finset (Fin 3)).image secondPerm) ∪
            ((({0, 1} : Finset (Fin 3)).image thirdPerm) ∪
              ({0, 2} : Finset (Fin 3)).image fourthPerm) = Finset.univ :=
  exists_joint_gauge (Finset.subset_univ _) (Finset.subset_univ _) (Finset.subset_univ _)
    (Finset.subset_univ _) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-! ## 3.  At an actual four-branch anchor -/

section Anchor

open NonTrivalentValencyFourKZero
open NonTrivalentValencyFourKZero.PrescribedPairing

variable {target : CFGraph} {wall : target.V} {data : GluingDatum target degree}
  {star : W4TargetPairings.FourStar target wall} {anchor : W4Assembly.WallBlock data wall}

/-- The admissible values of `K` at one oriented side `side` (the paper's
`A₋`) of a prescribed pairing: the two minus-side classes can overlap in
`K + 1` sheets, the two plus-side classes fit into `|A| - K` sheets, and the
minus side is small enough for `coK` to be a natural number.

At the smaller side this is equivalent to the paper's pairing-independent range
`0 ≤ K ≤ min(k₂-1, |A|-k₅)` (`admissible_smallerSide_iff`). -/
def Admissible (source : FourBranchAnchor data star anchor) (pairing : Fin 3)
    (side : Bool) (K : ℕ) : Prop :=
  K + 1 ≤ source.index (firstLabel pairing side) ∧
    K + 1 ≤ source.index (secondLabel pairing side) ∧
    K + source.index (firstLabel pairing (!side)) ≤
      (data.vertexPartition wall).blockCard anchor.1 ∧
    K + source.index (secondLabel pairing (!side)) ≤
      (data.vertexPartition wall).blockCard anchor.1 ∧
    sideIndex source pairing side ≤ (data.vertexPartition wall).blockCard anchor.1 + 1 + K

/-- The mirror index `K'` of the plus side, `|A| + 1 + K - (k_α + k_β)`. -/
noncomputable def coIndex (source : FourBranchAnchor data star anchor) (pairing : Fin 3)
    (side : Bool) (K : ℕ) : ℕ :=
  (data.vertexPartition wall).blockCard anchor.1 + 1 + K - sideIndex source pairing side

theorem index_le_blockCard (source : FourBranchAnchor data star anchor) (label : Fin 4) :
    source.index label ≤ (data.vertexPartition wall).blockCard anchor.1 := by
  rw [← branchBlock_card]
  exact Finset.card_le_card (branchBlock_subset_wall source label)

/-- The two sides of any prescribed pairing sum to `2|A| + 2` (identity
`(square)`), whichever side is called the minus side. -/
theorem sideIndex_add_not (source : FourBranchAnchor data star anchor) (pairing : Fin 3)
    (side : Bool) (hNoGlue : W4StableSource.DanglingEdgeNoGlue data)
    (hRamification : data.localRamification wall anchor = 0) :
    sideIndex source pairing side + sideIndex source pairing (!side) =
      2 * (data.vertexPartition wall).blockCard anchor.1 + 2 := by
  have hTotal := sideIndex_false_add_true source pairing
  have hSquare : (∑ label : Fin 4, source.index label) =
      2 * (data.vertexPartition wall).blockCard anchor.1 + 2 := by
    exact_mod_cast source.sum_index_eq_two_mul_add_two hNoGlue hRamification
  rw [hSquare] at hTotal
  cases side <;> simp <;> omega

/-- Every label is one of the two labels of its own side. -/
theorem eq_first_or_second (pairing : Fin 3) (label : Fin 4) :
    label = firstLabel pairing (W4TargetPairings.Pairing.labelRight pairing label) ∨
      label = secondLabel pairing (W4TargetPairings.Pairing.labelRight pairing label) := by
  have hMem : label ∈ W4TargetPairings.Pairing.labelsOnSide pairing
      (W4TargetPairings.Pairing.labelRight pairing label) :=
    (W4TargetPairings.Pairing.mem_labelsOnSide _ _ _).mpr rfl
  rw [labelsOnSide_eq_pair] at hMem
  simpa using hMem

/-- Every label is one of the four oriented labels. -/
theorem eq_oriented_label (pairing : Fin 3) (side : Bool) (label : Fin 4) :
    label = firstLabel pairing side ∨ label = secondLabel pairing side ∨
      label = firstLabel pairing (!side) ∨ label = secondLabel pairing (!side) := by
  rcases eq_first_or_second pairing label with h | h <;>
    cases hSide : W4TargetPairings.Pairing.labelRight pairing label <;>
    cases side <;> rw [hSide] at h <;> simp [h]

/-- **The paper's range, at the smaller side.**  `Admissible` at the smaller
side is exactly `K + 1 ≤ min k` and `K + max k ≤ |A|` over all four
branches -- i.e. `0 ≤ K ≤ min(k₂ - 1, |A| - k₅)`, which does not depend on the
pairing. -/
theorem admissible_smallerSide_iff (source : FourBranchAnchor data star anchor)
    (pairing : Fin 3) (hNoGlue : W4StableSource.DanglingEdgeNoGlue data)
    (hRamification : data.localRamification wall anchor = 0) (K : ℕ) :
    Admissible source pairing (smallerSide source pairing) K ↔
      (∀ label, K + 1 ≤ source.index label) ∧
        (∀ label, K + source.index label ≤ (data.vertexPartition wall).blockCard anchor.1) := by
  set side := smallerSide source pairing with hSideDef
  have hSmall := sideIndex_smaller_le_wall_add_one source pairing hNoGlue hRamification
  have hTotal := sideIndex_add_not source pairing side hNoGlue hRamification
  have hMinusEq := sideIndex_eq_add source pairing side
  have hPlusEq := sideIndex_eq_add source pairing (!side)
  rw [← hSideDef] at hSmall
  constructor
  · rintro ⟨hFirst, hSecond, hThird, hFourth, _⟩
    constructor
    · intro label
      rcases eq_oriented_label pairing side label with h | h | h | h <;> rw [h] <;> omega
    · intro label
      rcases eq_oriented_label pairing side label with h | h | h | h <;> rw [h] <;> omega
  · rintro ⟨hLower, hUpper⟩
    exact ⟨hLower _, hLower _, hUpper _, hUpper _, by omega⟩

/-- The admissible range is the same for all three pairings, as in Part II,
where each of the three combinatorial types has the same number
`min(k₂ - 1, |A| - k₅) + 1` of full-dimensional morphisms. -/
theorem admissible_smallerSide_iff_of_pairing (source : FourBranchAnchor data star anchor)
    (pairing pairing' : Fin 3) (hNoGlue : W4StableSource.DanglingEdgeNoGlue data)
    (hRamification : data.localRamification wall anchor = 0) (K : ℕ) :
    Admissible source pairing (smallerSide source pairing) K ↔
      Admissible source pairing' (smallerSide source pairing') K := by
  rw [admissible_smallerSide_iff source pairing hNoGlue hRamification,
    admissible_smallerSide_iff source pairing' hNoGlue hRamification]

/-- `K = 0` is always admissible at the smaller side: the `K = 0` construction
is the bottom of the range. -/
theorem admissible_zero (source : FourBranchAnchor data star anchor)
    (pairing : Fin 3) (hNoGlue : W4StableSource.DanglingEdgeNoGlue data)
    (hRamification : data.localRamification wall anchor = 0) :
    Admissible source pairing (smallerSide source pairing) 0 := by
  rw [admissible_smallerSide_iff source pairing hNoGlue hRamification]
  refine ⟨fun label ↦ ?_, fun label ↦ ?_⟩
  · have := source.index_pos label
    omega
  · have := index_le_blockCard source label
    omega

/-- **The joint condition at an actual anchor.**  For every admissible `K`
there is a block-preserving gauge of three of the four branch classes (the
minus side's first class is not moved) and a `SplitData` over the wall block
with exactly this `K` and with `coK = coIndex`, whose endpoint sets are the
two gauged side unions. -/
theorem exists_gauged_splitData (source : FourBranchAnchor data star anchor)
    (pairing : Fin 3) (side : Bool) (hNoGlue : W4StableSource.DanglingEdgeNoGlue data)
    (hRamification : data.localRamification wall anchor = 0) {K : ℕ}
    (hAdmissible : Admissible source pairing side K) :
    ∃ secondPerm thirdPerm fourthPerm : Equiv.Perm (Fin degree),
      BlockPreserving ((data.vertexPartition wall).block anchor.1) secondPerm ∧
        BlockPreserving ((data.vertexPartition wall).block anchor.1) thirdPerm ∧
        BlockPreserving ((data.vertexPartition wall).block anchor.1) fourthPerm ∧
        ∃ split : SplitData (data.vertexPartition wall) anchor.1,
          split.minusSheets = branchBlock source (firstLabel pairing side) ∪
              (branchBlock source (secondLabel pairing side)).image secondPerm ∧
            split.plusSheets =
              (branchBlock source (firstLabel pairing (!side))).image thirdPerm ∪
                (branchBlock source (secondLabel pairing (!side))).image fourthPerm ∧
            split.K = K ∧ split.coK = coIndex source pairing side K := by
  obtain ⟨hFirst, hSecond, hThird, hFourth, hSide⟩ := hAdmissible
  have hTotal := sideIndex_add_not source pairing side hNoGlue hRamification
  have hMinusEq := sideIndex_eq_add source pairing side
  have hPlusEq := sideIndex_eq_add source pairing (!side)
  have hThirdPos := source.index_pos (firstLabel pairing (!side))
  have hFourthPos := source.index_pos (secondLabel pairing (!side))
  unfold coIndex
  apply exists_splitData_of_joint_gauge (branchBlock_subset_wall source _)
    (branchBlock_subset_wall source _) (branchBlock_subset_wall source _)
    (branchBlock_subset_wall source _) <;> simp only [branchBlock_card] <;> omega

end Anchor

/-! ## 3b.  The blockwise Euler identity of a general-`K` split -/

section Euler

open NonTrivalentValencyFourKZero.PrescribedPairing

/-- A selected-block partition induces `|A| + 1 - |selected|` classes on any
sheet of the anchor block. -/
theorem withSelectedBlock_blockCountWithin (coarse : SheetPartition degree)
    (anchor representative : Fin degree) (selected : Finset (Fin degree))
    (hRepresentative : representative ∈ selected) (hSelected : selected ⊆ coarse.block anchor)
    (block : Fin degree) (hBlock : coarse.Rel anchor block) :
    (withSelectedBlock coarse anchor representative selected hRepresentative
        hSelected).blockCountWithin coarse block + selected.card =
      coarse.blockCard anchor + 1 := by
  have hRepWall : coarse.Rel anchor representative :=
    (coarse.mem_block_iff _ _).mp (hSelected hRepresentative)
  have hCount := blockCountWithin_add_blockCard_eq
    (withSelectedBlock coarse anchor representative selected hRepresentative hSelected)
    coarse block representative (hBlock.symm.trans hRepWall)
    (withSelectedBlock.refines coarse anchor representative selected hRepresentative
      hSelected)
    (by
      intro sheet hSheet
      have hWall : coarse.Rel anchor sheet := hBlock.trans hSheet
      by_cases hMem : sheet ∈ selected
      · left
        rw [← SheetPartition.mem_block_iff, withSelectedBlock.block_representative]
        exact hMem
      · right
        exact withSelectedBlock.block_of_not_mem_of_rel coarse anchor representative
          selected hRepresentative hSelected hMem hWall)
  rw [withSelectedBlock.blockCard_representative,
    ← ContractionRamification.blockCard_congr coarse hBlock] at hCount
  exact hCount

/-- **The blockwise Euler identity** of the general-`K` resolution on the
anchor block: `#newEdge + 1 = #left + #right` there, i.e.
`(1 + K + K') + 1 = (1 + K') + (1 + K)`.  This is what
`M11SourceGenus.candidate_sourceGenus_of_blockwise_euler` consumes; the `K = 0`
exit gets it from `IsStar`, which fails for `K ≥ 1` (both endpoints are
proper refinements). -/
theorem split_euler {coarse : SheetPartition degree} {anchor : Fin degree}
    (split : SplitData coarse anchor) (block : Fin degree) (hBlock : coarse.Rel anchor block) :
    split.newEdge.blockCountWithin coarse block + 1 =
      split.left.blockCountWithin coarse block + split.right.blockCountWithin coarse block := by
  have hLeft := withSelectedBlock_blockCountWithin coarse anchor split.bridge split.minusSheets
    split.bridge_mem_minus split.minus_subset block hBlock
  have hRight := withSelectedBlock_blockCountWithin coarse anchor split.bridge
    split.plusSheets split.bridge_mem_plus split.plus_subset block hBlock
  have hNew := withSelectedBlock_blockCountWithin coarse anchor split.bridge
    split.bridgeSheets split.bridge_mem_bridgeSheets split.bridgeSheets_subset block hBlock
  have hCards := split.card_bridgeSheets_add
  have hMinus := split.bridgeSheets_card_add_K
  have hPlus := split.bridgeSheets_card_add_coK
  change split.newEdge.blockCountWithin coarse block + split.bridgeSheets.card
    = coarse.blockCard anchor + 1 at hNew
  change split.left.blockCountWithin coarse block + split.minusSheets.card
    = coarse.blockCard anchor + 1 at hLeft
  change split.right.blockCountWithin coarse block + split.plusSheets.card
    = coarse.blockCard anchor + 1 at hRight
  omega

end Euler

/-! ## 4.  The gauged datum: one branch swap per star label -/

section Datum

open NonTrivalentValencyFourKZero
open NonTrivalentValencyFourKZero.PrescribedPairing
open BlockPreservingBranchSwap
open ResolutionM11

variable {target : CFGraph} {wall : target.V}

/-- One block-preserving branch swap across the star occurrence `label`. -/
noncomputable def swapStep (star : W4TargetPairings.FourStar target wall)
    (current : GluingDatum target degree) (label : Fin 4)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (current.vertexPartition wall).Rel (permutation sheet) sheet) :
    GluingDatum target degree :=
  (branchSwapOfPerm current wall
    (TargetSeparation.farEndpoint wall (star.edge label))
    (TargetSeparation.farEndpoint_ne (selectedEdge_incident (star := star) label))
    permutation hFix).apply

theorem swapStep_vertexPartition_wall (star : W4TargetPairings.FourStar target wall)
    (current : GluingDatum target degree) (label : Fin 4)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (current.vertexPartition wall).Rel (permutation sheet) sheet) :
    (swapStep star current label permutation hFix).vertexPartition wall =
      current.vertexPartition wall :=
  branchSwapOfPerm_vertexPartition_wall _ _ _ _ _ _

theorem swapStep_valid (star : W4TargetPairings.FourStar target wall)
    (current : GluingDatum target degree) (label : Fin 4)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (current.vertexPartition wall).Rel (permutation sheet) sheet)
    (hValid : current.Valid) : (swapStep star current label permutation hFix).Valid :=
  GluingDatum.SheetRelabeling.valid _ hValid

/-- A swap across `label` relabels that occurrence and, in a tree target, no
other star occurrence. -/
theorem swapStep_edgePartition (star : W4TargetPairings.FourStar target wall)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (current : GluingDatum target degree) (label : Fin 4)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (current.vertexPartition wall).Rel (permutation sheet) sheet)
    (other : Fin 4) :
    (swapStep star current label permutation hFix).edgePartition (star.edge other) =
      if other = label then (current.edgePartition (star.edge other)).relabel permutation
      else current.edgePartition (star.edge other) := by
  split_ifs with hOther
  · subst other
    exact branchSwapOfPerm_edgePartition_of_moved _ _ _ _ _ _ _
      (TargetSeparation.edgeMoved_self_eq_true (selectedEdge_incident (star := star) label))
  · apply branchSwapOfPerm_edgePartition_of_fixed
    apply TargetSeparation.edgeMoved_eq_false hConnected hGenus
      (selectedEdge_incident (star := star) label)
      (selectedEdge_incident (star := star) other)
    intro hEqual
    exact hOther (star.edge_injective hEqual).symm

theorem swapStep_sourceGenus (star : W4TargetPairings.FourStar target wall)
    (current : GluingDatum target degree) (label : Fin 4)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (current.vertexPartition wall).Rel (permutation sheet) sheet) :
    genus (swapStep star current label permutation hFix).sourceGraph =
      genus current.sourceGraph :=
  SheetRelabelIncidence.sourceGenus_eq _

/-- One swap step is a geometric datum isomorphism. -/
noncomputable def swapStepIso (star : W4TargetPairings.FourStar target wall)
    (current : GluingDatum target degree) (label : Fin 4)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (current.vertexPartition wall).Rel (permutation sheet) sheet) :
    GeometricDatumIso current (swapStep star current label permutation hFix) :=
  GeometricDatumIso.ofStrict (Transport.DatumIso.ofSheetRelabeling _)

/-- A block-preserving permutation for each of the four star labels. -/
structure LabelGauge (data : GluingDatum target degree) (wall : target.V)
    (anchor : Fin degree) where
  perm : Fin 4 → Equiv.Perm (Fin degree)
  preserving : ∀ label, BlockPreserving ((data.vertexPartition wall).block anchor) (perm label)

namespace LabelGauge

variable {data : GluingDatum target degree} {anchor : Fin degree}

theorem fix (gauge : LabelGauge data wall anchor) (label : Fin 4) (sheet : Fin degree) :
    (data.vertexPartition wall).Rel (gauge.perm label sheet) sheet :=
  rel_of_stabilizes_block (data.vertexPartition wall) anchor (gauge.perm label)
    (gauge.preserving label).1 (gauge.preserving label).2 sheet

variable (star : W4TargetPairings.FourStar target wall) (gauge : LabelGauge data wall anchor)

noncomputable def stage1 : GluingDatum target degree :=
  swapStep star data 0 (gauge.perm 0) (gauge.fix 0)

theorem stage1_wall : (gauge.stage1 star).vertexPartition wall = data.vertexPartition wall :=
  swapStep_vertexPartition_wall _ _ _ _ _

noncomputable def stage2 : GluingDatum target degree :=
  swapStep star (gauge.stage1 star) 1 (gauge.perm 1)
    (fun sheet ↦ by rw [stage1_wall]; exact gauge.fix 1 sheet)

theorem stage2_wall : (gauge.stage2 star).vertexPartition wall = data.vertexPartition wall := by
  unfold stage2
  rw [swapStep_vertexPartition_wall, stage1_wall]

noncomputable def stage3 : GluingDatum target degree :=
  swapStep star (gauge.stage2 star) 2 (gauge.perm 2)
    (fun sheet ↦ by rw [stage2_wall]; exact gauge.fix 2 sheet)

theorem stage3_wall : (gauge.stage3 star).vertexPartition wall = data.vertexPartition wall := by
  unfold stage3
  rw [swapStep_vertexPartition_wall, stage2_wall]

/-- The gauged incoming datum: every star branch relabelled by its own
permutation. -/
noncomputable def gaugedData : GluingDatum target degree :=
  swapStep star (gauge.stage3 star) 3 (gauge.perm 3)
    (fun sheet ↦ by rw [stage3_wall]; exact gauge.fix 3 sheet)

theorem gaugedData_vertexPartition_wall :
    (gauge.gaugedData star).vertexPartition wall = data.vertexPartition wall := by
  unfold gaugedData
  rw [swapStep_vertexPartition_wall, stage3_wall]

theorem gaugedData_valid (hValid : data.Valid) : (gauge.gaugedData star).Valid :=
  swapStep_valid _ _ _ _ _ (swapStep_valid _ _ _ _ _ (swapStep_valid _ _ _ _ _
    (swapStep_valid _ _ _ _ _ hValid)))

/-- The gauge does not change the source genus. -/
theorem gaugedData_sourceGenus :
    genus (gauge.gaugedData star).sourceGraph = genus data.sourceGraph := by
  unfold gaugedData
  rw [swapStep_sourceGenus]
  unfold stage3
  rw [swapStep_sourceGenus]
  unfold stage2
  rw [swapStep_sourceGenus]
  unfold stage1
  rw [swapStep_sourceGenus]

/-- The gauged datum is geometrically isomorphic to the incoming one (the shape
`ColumnReceipt.base_col` asks for). -/
noncomputable def gaugedDataIso : GeometricDatumIso data (gauge.gaugedData star) :=
  ((swapStepIso _ _ _ _ _).trans (swapStepIso _ _ _ _ _)).trans
    ((swapStepIso _ _ _ _ _).trans (swapStepIso _ _ _ _ _))

section Edges

variable (hConnected : graph_connected target) (hGenus : genus target = 0)
include hConnected hGenus

theorem stage1_edgePartition (label : Fin 4) :
    (gauge.stage1 star).edgePartition (star.edge label) =
      if label.val < 1 then (data.edgePartition (star.edge label)).relabel (gauge.perm label)
      else data.edgePartition (star.edge label) := by
  unfold stage1
  rw [swapStep_edgePartition star hConnected hGenus]
  fin_cases label <;> simp

theorem stage2_edgePartition (label : Fin 4) :
    (gauge.stage2 star).edgePartition (star.edge label) =
      if label.val < 2 then (data.edgePartition (star.edge label)).relabel (gauge.perm label)
      else data.edgePartition (star.edge label) := by
  unfold stage2
  rw [swapStep_edgePartition star hConnected hGenus, stage1_edgePartition star gauge
    hConnected hGenus]
  fin_cases label <;> simp

theorem stage3_edgePartition (label : Fin 4) :
    (gauge.stage3 star).edgePartition (star.edge label) =
      if label.val < 3 then (data.edgePartition (star.edge label)).relabel (gauge.perm label)
      else data.edgePartition (star.edge label) := by
  unfold stage3
  rw [swapStep_edgePartition star hConnected hGenus, stage2_edgePartition star gauge
    hConnected hGenus]
  fin_cases label <;> simp

/-- Each star occurrence of the gauged datum is the original one relabelled by
its own permutation. -/
theorem gaugedData_edgePartition (label : Fin 4) :
    (gauge.gaugedData star).edgePartition (star.edge label) =
      (data.edgePartition (star.edge label)).relabel (gauge.perm label) := by
  unfold gaugedData
  rw [swapStep_edgePartition star hConnected hGenus, stage3_edgePartition star gauge
    hConnected hGenus]
  fin_cases label <;> simp

end Edges

end LabelGauge

/-! ## 5.  A general-`K` position and its local receipts -/

variable {data : GluingDatum target degree} {star : W4TargetPairings.FourStar target wall}
  {anchor : W4Assembly.WallBlock data wall}

/-- The gauged branch class of one star label. -/
noncomputable def gaugedBlock (source : FourBranchAnchor data star anchor)
    (gauge : LabelGauge data wall anchor.1) (label : Fin 4) : Finset (Fin degree) :=
  (branchBlock source label).image (gauge.perm label)

/-- **A general-`K` position**, oriented at `side` (the paper's `A₋` side):
a gauge of the four star branches and a split of the wall block such that the
two gauged branch classes on each side lie in that side's endpoint set, with
the paper's cardinalities `|A₋| + K + 1 = k_α + k_β` and
`|A₊| + K' + 1 = k_γ + k_δ`. -/
structure Position (source : FourBranchAnchor data star anchor) (pairing : Fin 3)
    (side : Bool) where
  gauge : LabelGauge data wall anchor.1
  split : SplitData (data.vertexPartition wall) anchor.1
  minus_sub : ∀ label, W4TargetPairings.Pairing.labelRight pairing label = side →
    gaugedBlock source gauge label ⊆ split.minusSheets
  plus_sub : ∀ label, W4TargetPairings.Pairing.labelRight pairing label = !side →
    gaugedBlock source gauge label ⊆ split.plusSheets
  minus_card : split.minusSheets.card + split.K + 1 = sideIndex source pairing side
  plus_card : split.plusSheets.card + split.coK + 1 = sideIndex source pairing (!side)

theorem labelRight_firstLabel (pairing : Fin 3) (side : Bool) :
    W4TargetPairings.Pairing.labelRight pairing (firstLabel pairing side) = side :=
  (W4TargetPairings.Pairing.mem_labelsOnSide _ _ _).mp (firstLabel_mem pairing side)

theorem labelRight_secondLabel (pairing : Fin 3) (side : Bool) :
    W4TargetPairings.Pairing.labelRight pairing (secondLabel pairing side) = side :=
  (W4TargetPairings.Pairing.mem_labelsOnSide _ _ _).mp (secondLabel_mem pairing side)

/-- The gauge assembling three permutations on the oriented labels. -/
noncomputable def orientedPerm (pairing : Fin 3) (side : Bool)
    (secondPerm thirdPerm fourthPerm : Equiv.Perm (Fin degree)) (label : Fin 4) :
    Equiv.Perm (Fin degree) :=
  if label = secondLabel pairing side then secondPerm
  else if label = firstLabel pairing (!side) then thirdPerm
  else if label = secondLabel pairing (!side) then fourthPerm
  else Equiv.refl (Fin degree)

theorem oriented_labels_ne (pairing : Fin 3) (side : Bool) :
    firstLabel pairing side ≠ secondLabel pairing side ∧
      firstLabel pairing side ≠ firstLabel pairing (!side) ∧
      firstLabel pairing side ≠ secondLabel pairing (!side) ∧
      secondLabel pairing side ≠ firstLabel pairing (!side) ∧
      secondLabel pairing side ≠ secondLabel pairing (!side) ∧
      firstLabel pairing (!side) ≠ secondLabel pairing (!side) := by
  have h1 := labelRight_firstLabel pairing side
  have h2 := labelRight_secondLabel pairing side
  have h3 := labelRight_firstLabel pairing (!side)
  have h4 := labelRight_secondLabel pairing (!side)
  have hFlip : side ≠ !side := by cases side <;> simp
  refine ⟨firstLabel_ne_secondLabel pairing side, fun hEq ↦ hFlip ?_, fun hEq ↦ hFlip ?_,
    fun hEq ↦ hFlip ?_, fun hEq ↦ hFlip ?_, firstLabel_ne_secondLabel pairing (!side)⟩
  · exact h1.symm.trans ((congrArg _ hEq).trans h3)
  · exact h1.symm.trans ((congrArg _ hEq).trans h4)
  · exact h2.symm.trans ((congrArg _ hEq).trans h3)
  · exact h2.symm.trans ((congrArg _ hEq).trans h4)

/-- **Existence of a general-`K` position** for every admissible `K`. -/
theorem exists_position (source : FourBranchAnchor data star anchor)
    (pairing : Fin 3) (side : Bool) (hNoGlue : W4StableSource.DanglingEdgeNoGlue data)
    (hRamification : data.localRamification wall anchor = 0) {K : ℕ}
    (hAdmissible : Admissible source pairing side K) :
    ∃ position : Position source pairing side,
      position.split.K = K ∧ position.split.coK = coIndex source pairing side K ∧
      position.split.minusSheets = gaugedBlock source position.gauge (firstLabel pairing side) ∪
        gaugedBlock source position.gauge (secondLabel pairing side) ∧
      position.split.plusSheets =
        gaugedBlock source position.gauge (firstLabel pairing (!side)) ∪
          gaugedBlock source position.gauge (secondLabel pairing (!side)) := by
  obtain ⟨secondPerm, thirdPerm, fourthPerm, hSecond, hThird, hFourth, split,
    hSplitMinus, hSplitPlus, hSplitK, hSplitcoK⟩ :=
    exists_gauged_splitData source pairing side hNoGlue hRamification hAdmissible
  obtain ⟨hne12, hne13, hne14, hne23, hne24, hne34⟩ := oriented_labels_ne pairing side
  let gauge : LabelGauge data wall anchor.1 :=
    { perm := orientedPerm pairing side secondPerm thirdPerm fourthPerm
      preserving := by
        intro label
        unfold orientedPerm
        split_ifs
        · exact hSecond
        · exact hThird
        · exact hFourth
        · exact blockPreserving_refl _ }
  have hPermFirst : gauge.perm (firstLabel pairing side) = Equiv.refl _ := by
    simp [gauge, orientedPerm, hne12, hne13, hne14]
  have hPermSecond : gauge.perm (secondLabel pairing side) = secondPerm := by
    simp [gauge, orientedPerm]
  have hPermThird : gauge.perm (firstLabel pairing (!side)) = thirdPerm := by
    simp [gauge, orientedPerm, hne23.symm]
  have hPermFourth : gauge.perm (secondLabel pairing (!side)) = fourthPerm := by
    simp [gauge, orientedPerm, hne24.symm, hne34.symm]
  have hAdm := hAdmissible
  obtain ⟨_, _, _, _, hSide⟩ := hAdm
  have hTotal := sideIndex_add_not source pairing side hNoGlue hRamification
  have hMinusCard := split.card_minus_add_coK
  have hPlusCard := split.card_plus_add_K
  have hcoK : split.coK = coIndex source pairing side K := hSplitcoK
  unfold coIndex at hcoK
  have hFirstBlock : gaugedBlock source gauge (firstLabel pairing side) =
      branchBlock source (firstLabel pairing side) := by
    rw [gaugedBlock, hPermFirst]
    ext sheet
    simp
  refine ⟨Position.mk gauge split ?_ ?_ (by omega) (by omega), hSplitK, hSplitcoK, ?_, ?_⟩
  · intro label hLabel
    rcases eq_first_or_second pairing label with h | h <;> rw [hLabel] at h <;> subst h
    · rw [gaugedBlock, hPermFirst, hSplitMinus]
      intro sheet hSheet
      apply Finset.mem_union_left
      simpa using hSheet
    · rw [gaugedBlock, hPermSecond, hSplitMinus]
      exact Finset.subset_union_right
  · intro label hLabel
    rcases eq_first_or_second pairing label with h | h <;> rw [hLabel] at h <;> subst h
    · rw [gaugedBlock, hPermThird, hSplitPlus]
      exact Finset.subset_union_left
    · rw [gaugedBlock, hPermFourth, hSplitPlus]
      exact Finset.subset_union_right
  · show split.minusSheets = gaugedBlock source gauge (firstLabel pairing side) ∪
      gaugedBlock source gauge (secondLabel pairing side)
    rw [hFirstBlock, gaugedBlock, hPermSecond, hSplitMinus]
  · show split.plusSheets = gaugedBlock source gauge (firstLabel pairing (!side)) ∪
      gaugedBlock source gauge (secondLabel pairing (!side))
    rw [gaugedBlock, gaugedBlock, hPermThird, hPermFourth, hSplitPlus]

/-! ### The shape of a relabelled branch occurrence -/

section Shape

variable (source : FourBranchAnchor data star anchor) (gauge : LabelGauge data wall anchor.1)

/-- The relabelled old occurrence of `label`. -/
noncomputable abbrev gaugedEdge {anchorSheet : Fin degree}
    (star : W4TargetPairings.FourStar target wall)
    (gauge : LabelGauge data wall anchorSheet) (label : Fin 4) : SheetPartition degree :=
  (data.edgePartition (star.edge label)).relabel (gauge.perm label)

theorem gaugedEdge_block (label : Fin 4) :
    (gaugedEdge star gauge label).block (gauge.perm label (source.sheet label)) =
      gaugedBlock source gauge label :=
  SheetPartition.relabel_block _ _ _

theorem gaugedEdge_rel_of_mem (label : Fin 4) {sheet : Fin degree}
    (hSheet : sheet ∈ gaugedBlock source gauge label) :
    (gaugedEdge star gauge label).Rel (gauge.perm label (source.sheet label)) sheet := by
  rw [← gaugedEdge_block source gauge label] at hSheet
  exact ((gaugedEdge star gauge label).mem_block_iff _ _).mp hSheet

theorem gaugedBlock_closed (label : Fin 4) {first second : Fin degree}
    (hFirst : first ∈ gaugedBlock source gauge label)
    (hRel : (gaugedEdge star gauge label).Rel first second) :
    second ∈ gaugedBlock source gauge label := by
  rw [← gaugedEdge_block source gauge label, SheetPartition.mem_block_iff]
  exact (gaugedEdge_rel_of_mem source gauge label hFirst).trans hRel

theorem active_mem_gaugedBlock (label : Fin 4) :
    gauge.perm label (source.sheet label) ∈ gaugedBlock source gauge label :=
  Finset.mem_image_of_mem _ ((data.edgePartition (star.edge label)).self_mem_block _)

theorem gaugedBlock_subset_wall (label : Fin 4) :
    gaugedBlock source gauge label ⊆ (data.vertexPartition wall).block anchor.1 :=
  (gauge.preserving label).image_subset (branchBlock_subset_wall source label)

/-- Inside the wall block, a relabelled branch occurrence consists of its
gauged surviving class and singletons. -/
theorem gaugedEdge_shape (hNoGlue : W4StableSource.DanglingEdgeNoGlue data)
    (label : Fin 4) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel anchor.1 sheet) :
    sheet ∈ gaugedBlock source gauge label ∨
      (gaugedEdge star gauge label).block sheet = {sheet} := by
  let permutation := gauge.perm label
  let original := permutation.symm sheet
  have hOriginalMem : original ∈ (data.vertexPartition wall).block anchor.1 :=
    (gauge.preserving label).symm_mem
      (((data.vertexPartition wall).mem_block_iff _ _).mpr hWall)
  have hOriginalWall := ((data.vertexPartition wall).mem_block_iff _ _).mp hOriginalMem
  have hSheetEq : sheet = permutation original := by simp [original]
  rcases mem_branchBlock_or_block_singleton source hNoGlue label original hOriginalWall with
    hActive | hSingleton
  · left
    rw [hSheetEq]
    exact Finset.mem_image_of_mem _ hActive
  · right
    rw [hSheetEq, gaugedEdge, SheetPartition.relabel_block, hSingleton,
      Finset.image_singleton]

theorem gaugedEdge_refines_wall (hConnected : graph_connected target)
    (hGenus : genus target = 0) (label : Fin 4) :
    (gaugedEdge star gauge label).Refines (data.vertexPartition wall) := by
  have hRefines := star.edgePartition_refines_wall (gauge.gaugedData star) label
  rw [gauge.gaugedData_vertexPartition_wall star,
    gauge.gaugedData_edgePartition star hConnected hGenus label] at hRefines
  exact hRefines

theorem gaugedEdge_blockCard (label : Fin 4) :
    (gaugedEdge star gauge label).blockCard (gauge.perm label (source.sheet label)) =
      source.index label :=
  SheetPartition.relabel_blockCard _ _ _

end Shape

/-! ### The background owed by the other wall blocks -/

/-- The guarded background resolutions of the *other* wall blocks, over a
gauged datum `gData`, for a prescribed pairing.  Field for field this is
`NonTrivalentValencyFourKZero.PrescribedPairing.PairingBackground` with the
`K = 0` gauged datum replaced by an arbitrary one; nothing about the
distinguished block is supplied here. -/
structure PairingBackground (gData : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall) (pairing : Fin 3)
    (distinguished : Fin degree) where
  resolution : Fin degree → LocalResolution degree
  contracts : ∀ block, ¬(gData.vertexPartition wall).Rel distinguished block →
    (resolution block).ContractsTo (gData.vertexPartition wall)
  exterior : ∀ edge : target.edges,
    ((edge : target.V × target.V).1 = wall ∨ (edge : target.V × target.V).2 = wall) →
    ∀ block, ¬(gData.vertexPartition wall).Rel distinguished block →
      (gData.edgePartition edge).Refines
        (if star.right pairing edge then (resolution block).right
          else (resolution block).left)
  left_riemannHurwitz : ∀ block, (gData.vertexPartition wall).repr block = block →
    ¬(gData.vertexPartition wall).Rel distinguished block →
      LocalResolution.RiemannHurwitzAtBlock (gData.vertexPartition wall)
        (resolution block).left
        ((resolution block).newEdge :: (star.leftEdges pairing).map gData.edgePartition) block
  right_riemannHurwitz : ∀ block, (gData.vertexPartition wall).repr block = block →
    ¬(gData.vertexPartition wall).Rel distinguished block →
      LocalResolution.RiemannHurwitzAtBlock (gData.vertexPartition wall)
        (resolution block).right
        ((resolution block).newEdge :: (star.rightEdges pairing).map gData.edgePartition) block

/-- Package the background with the pairing's occurrence assignment. -/
noncomputable def PairingBackground.background {gData : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall} {pairing : Fin 3} {distinguished : Fin degree}
    (geometry : PairingBackground gData star pairing distinguished) :
    GlobalM11Arbitrary.Background gData wall distinguished where
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

namespace Position

variable {source : FourBranchAnchor data star anchor} {pairing : Fin 3} {side : Bool}
  (position : Position source pairing side)

/-- The gauged incoming datum of the position. -/
noncomputable abbrev datum : GluingDatum target degree := position.gauge.gaugedData star

theorem datum_vertexPartition_wall :
    position.datum.vertexPartition wall = data.vertexPartition wall :=
  position.gauge.gaugedData_vertexPartition_wall star

theorem datum_valid (hValid : data.Valid) : position.datum.Valid :=
  position.gauge.gaugedData_valid star hValid

section Receipts

variable (hConnected : graph_connected target) (hGenus : genus target = 0)
  (hNoGlue : W4StableSource.DanglingEdgeNoGlue data)
include hConnected hGenus hNoGlue

/-- **Exterior receipt, minus side.** -/
theorem refines_left (label : Fin 4)
    (hLabel : W4TargetPairings.Pairing.labelRight pairing label = side) :
    (gaugedEdge star position.gauge label).Refines position.split.left :=
  refines_withSelectedBlock_of_one_class (data.vertexPartition wall) _ anchor.1
    position.split.bridge position.split.minusSheets (gaugedBlock source position.gauge label)
    position.split.bridge_mem_minus position.split.minus_subset
    (gaugedEdge_refines_wall position.gauge hConnected hGenus label)
    (position.minus_sub label hLabel)
    (fun _ hFirst _ hRel ↦ gaugedBlock_closed source position.gauge label hFirst hRel)
    (gaugedEdge_shape source position.gauge hNoGlue label)

/-- **Exterior receipt, plus side.** -/
theorem refines_right (label : Fin 4)
    (hLabel : W4TargetPairings.Pairing.labelRight pairing label = !side) :
    (gaugedEdge star position.gauge label).Refines position.split.right :=
  refines_withSelectedBlock_of_one_class (data.vertexPartition wall) _ anchor.1
    position.split.bridge position.split.plusSheets (gaugedBlock source position.gauge label)
    position.split.bridge_mem_plus position.split.plus_subset
    (gaugedEdge_refines_wall position.gauge hConnected hGenus label)
    (position.plus_sub label hLabel)
    (fun _ hFirst _ hRel ↦ gaugedBlock_closed source position.gauge label hFirst hRel)
    (gaugedEdge_shape source position.gauge hNoGlue label)

/-- The induced count of one minus-side branch inside `A₋`. -/
theorem count_left (label : Fin 4)
    (hLabel : W4TargetPairings.Pairing.labelRight pairing label = side)
    (sheet : Fin degree) (hRel : position.split.left.Rel position.split.bridge sheet) :
    (gaugedEdge star position.gauge label).blockCountWithin position.split.left sheet +
        source.index label = position.split.minusSheets.card + 1 := by
  have hActiveMinus := position.minus_sub label hLabel
    (active_mem_gaugedBlock source position.gauge label)
  have hCount := blockCountWithin_add_blockCard_eq (gaugedEdge star position.gauge label)
    position.split.left sheet (position.gauge.perm label (source.sheet label))
    (hRel.symm.trans ((position.split.left_rel_bridge_iff _).mpr hActiveMinus))
    (position.refines_left hConnected hGenus hNoGlue label hLabel)
    (by
      intro other hOther
      have hMinus : other ∈ position.split.minusSheets :=
        (position.split.left_rel_bridge_iff other).mp (hRel.trans hOther)
      have hWall : (data.vertexPartition wall).Rel anchor.1 other :=
        ((data.vertexPartition wall).mem_block_iff _ _).mp
          (position.split.minus_subset hMinus)
      rcases gaugedEdge_shape source position.gauge hNoGlue label other hWall with
        hIn | hSingleton
      · exact Or.inl (gaugedEdge_rel_of_mem source position.gauge label hIn)
      · exact Or.inr hSingleton)
  rw [gaugedEdge_blockCard source position.gauge label,
    ← ContractionRamification.blockCard_congr position.split.left hRel,
    position.split.left_blockCard_bridge] at hCount
  exact hCount

/-- The induced count of one plus-side branch inside `A₊`. -/
theorem count_right (label : Fin 4)
    (hLabel : W4TargetPairings.Pairing.labelRight pairing label = !side)
    (sheet : Fin degree) (hRel : position.split.right.Rel position.split.bridge sheet) :
    (gaugedEdge star position.gauge label).blockCountWithin position.split.right sheet +
        source.index label = position.split.plusSheets.card + 1 := by
  have hActivePlus := position.plus_sub label hLabel
    (active_mem_gaugedBlock source position.gauge label)
  have hCount := blockCountWithin_add_blockCard_eq (gaugedEdge star position.gauge label)
    position.split.right sheet (position.gauge.perm label (source.sheet label))
    (hRel.symm.trans ((position.split.right_rel_bridge_iff _).mpr hActivePlus))
    (position.refines_right hConnected hGenus hNoGlue label hLabel)
    (by
      intro other hOther
      have hPlus : other ∈ position.split.plusSheets :=
        (position.split.right_rel_bridge_iff other).mp (hRel.trans hOther)
      have hWall : (data.vertexPartition wall).Rel anchor.1 other :=
        ((data.vertexPartition wall).mem_block_iff _ _).mp
          (position.split.plus_subset hPlus)
      rcases gaugedEdge_shape source position.gauge hNoGlue label other hWall with
        hIn | hSingleton
      · exact Or.inl (gaugedEdge_rel_of_mem source position.gauge label hIn)
      · exact Or.inr hSingleton)
  rw [gaugedEdge_blockCard source position.gauge label,
    ← ContractionRamification.blockCard_congr position.split.right hRel,
    position.split.right_blockCard_bridge] at hCount
  exact hCount

/-- **The old occurrence counts on the minus side**: they add up to exactly
`k₁ + 1`, which is the hypothesis `hLeftOld` of
`GeneralKResolution.SplitData.resolution_receipts`, with equality. -/
theorem oldCount_left (sheet : Fin degree)
    (hRel : position.split.left.Rel position.split.bridge sheet) :
    (((W4Assembly.oldEdgesAtSide star pairing side).map position.datum.edgePartition).map
        fun edge => (edge.blockCountWithin position.split.left sheet : ℤ)).sum =
      (position.split.bridgeSheets.card : ℤ) + 1 := by
  rw [List.map_map, W4Assembly.sum_oldEdgesAtSide_eq_sideSum]
  unfold W4TargetPairings.Pairing.sideSum
  rw [labelsOnSide_eq_pair, Finset.sum_pair (firstLabel_ne_secondLabel pairing side)]
  simp only [Function.comp_apply,
    position.gauge.gaugedData_edgePartition star hConnected hGenus]
  have hFirst := position.count_left hConnected hGenus hNoGlue (firstLabel pairing side)
    (labelRight_firstLabel pairing side) sheet hRel
  have hSecond := position.count_left hConnected hGenus hNoGlue (secondLabel pairing side)
    (labelRight_secondLabel pairing side) sheet hRel
  dsimp only [gaugedEdge] at hFirst hSecond
  have hIndex := sideIndex_eq_add source pairing side
  have hCard := position.minus_card
  have hK := position.split.bridgeSheets_card_add_K
  omega

/-- The mirror: the plus-side counts add up to exactly `k₁ + 1`. -/
theorem oldCount_right (sheet : Fin degree)
    (hRel : position.split.right.Rel position.split.bridge sheet) :
    (((W4Assembly.oldEdgesAtSide star pairing (!side)).map position.datum.edgePartition).map
        fun edge => (edge.blockCountWithin position.split.right sheet : ℤ)).sum =
      (position.split.bridgeSheets.card : ℤ) + 1 := by
  rw [List.map_map, W4Assembly.sum_oldEdgesAtSide_eq_sideSum]
  unfold W4TargetPairings.Pairing.sideSum
  rw [labelsOnSide_eq_pair, Finset.sum_pair (firstLabel_ne_secondLabel pairing (!side))]
  simp only [Function.comp_apply,
    position.gauge.gaugedData_edgePartition star hConnected hGenus]
  have hFirst := position.count_right hConnected hGenus hNoGlue (firstLabel pairing (!side))
    (labelRight_firstLabel pairing (!side)) sheet hRel
  have hSecond := position.count_right hConnected hGenus hNoGlue
    (secondLabel pairing (!side)) (labelRight_secondLabel pairing (!side)) sheet hRel
  dsimp only [gaugedEdge] at hFirst hSecond
  have hIndex := sideIndex_eq_add source pairing (!side)
  have hCard := position.plus_card
  have hcoK := position.split.bridgeSheets_card_add_coK
  omega

omit hConnected hGenus hNoGlue in
theorem oldEdgesAtSide_length (b : Bool) :
    ((W4Assembly.oldEdgesAtSide star pairing b).map position.datum.edgePartition).length = 2 := by
  cases b <;> simp [W4Assembly.oldEdgesAtSide]

/-- **Selected-block Riemann--Hurwitz at `A₋`**, over the actual gauged
datum. -/
theorem riemannHurwitz_left (block : Fin degree)
    (hBlock : (data.vertexPartition wall).Rel anchor.1 block) :
    LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall) position.split.left
      (position.split.newEdge ::
        (W4Assembly.oldEdgesAtSide star pairing side).map position.datum.edgePartition)
      block :=
  position.split.left_riemannHurwitzAtBlock _ (position.oldEdgesAtSide_length side)
    (fun sheet hRel ↦
      (position.oldCount_left hConnected hGenus hNoGlue sheet hRel).symm.le) block hBlock

/-- **Selected-block Riemann--Hurwitz at `A₊`**, over the actual gauged
datum. -/
theorem riemannHurwitz_right (block : Fin degree)
    (hBlock : (data.vertexPartition wall).Rel anchor.1 block) :
    LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall) position.split.right
      (position.split.newEdge ::
        (W4Assembly.oldEdgesAtSide star pairing (!side)).map position.datum.edgePartition)
      block :=
  position.split.right_riemannHurwitzAtBlock _ (position.oldEdgesAtSide_length (!side))
    (fun sheet hRel ↦
      (position.oldCount_right hConnected hGenus hNoGlue sheet hRel).symm.le) block hBlock

end Receipts

/-! ### Orientation and installation -/

/-- The endpoint partition for one Boolean side of the pairing: `A₋` on the
oriented side, `A₊` on the other. -/
noncomputable def endpoint (b : Bool) : SheetPartition degree :=
  if b = side then position.split.left else position.split.right

/-- The general-`K` local resolution, reversed exactly when the minus side is
the `true` side of the pairing. -/
noncomputable def selected : LocalResolution degree :=
  if side then position.split.resolution.reverse else position.split.resolution

theorem selected_left : position.selected.left = position.endpoint false := by
  cases side <;> simp [selected, endpoint]

theorem selected_right : position.selected.right = position.endpoint true := by
  cases side <;> simp [selected, endpoint]

theorem selected_newEdge : position.selected.newEdge = position.split.newEdge := by
  cases side <;> simp [selected]

theorem selected_endpoint (b : Bool) :
    (if b then position.selected.right else position.selected.left) = position.endpoint b := by
  cases b <;> simp [selected_left, selected_right]

theorem endpoint_side : position.endpoint side = position.split.left := by
  simp [endpoint]

theorem endpoint_not_side : position.endpoint (!side) = position.split.right := by
  cases side <;> simp [endpoint]

theorem selected_contracts :
    position.selected.ContractsTo (position.datum.vertexPartition wall) := by
  rw [position.datum_vertexPartition_wall]
  unfold selected
  cases side
  · exact position.split.resolution_contracts
  · exact LocalResolution.reverse_contracts position.split.resolution_contracts

/-- Off the anchor block the gauged datum has the incoming branch classes. -/
theorem datum_blockCard_eq_of_not_rel (hConnected : graph_connected target)
    (hGenus : genus target = 0) (label : Fin 4) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel anchor.1 sheet) :
    (position.datum.edgePartition (star.edge label)).blockCard sheet =
      (data.edgePartition (star.edge label)).blockCard sheet := by
  rw [position.gauge.gaugedData_edgePartition star hConnected hGenus]
  have hFixed : position.gauge.perm label sheet = sheet :=
    (position.gauge.preserving label).2 sheet
      (fun hMem ↦ hSheet (((data.vertexPartition wall).mem_block_iff _ _).mp hMem))
  have hCard := SheetPartition.relabel_blockCard (data.edgePartition (star.edge label))
    (position.gauge.perm label) sheet
  rw [hFixed] at hCard
  exact hCard

/-- The selected resolution satisfies the blockwise Euler identity on the
anchor block. -/
theorem selected_euler (block : Fin degree)
    (hBlock : (data.vertexPartition wall).Rel anchor.1 block) :
    position.selected.newEdge.blockCountWithin (data.vertexPartition wall) block + 1 =
      position.selected.left.blockCountWithin (data.vertexPartition wall) block +
        position.selected.right.blockCountWithin (data.vertexPartition wall) block := by
  have h := split_euler position.split block hBlock
  unfold selected
  cases side
  · exact h
  · simp only [ite_true, LocalResolution.reverse_newEdge, LocalResolution.reverse_left,
      LocalResolution.reverse_right, SplitData.resolution_newEdge, SplitData.resolution_left,
      SplitData.resolution_right]
    omega

section Install

variable (hConnected : graph_connected target) (hGenus : genus target = 0)
  (hNoGlue : W4StableSource.DanglingEdgeNoGlue data)
include hConnected hGenus hNoGlue

/-- **Exterior receipt** in the shape `GlobalM11Arbitrary.Background.install`
consumes. -/
theorem selected_exterior (edge : target.edges)
    (hIncident : (edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) :
    (position.datum.edgePartition edge).Refines
      (if star.right pairing edge then position.selected.right
        else position.selected.left) := by
  have hMem : edge ∈ GluingDatum.incidentEdges wall :=
    (GluingContraction.mem_incidentEdges_iff wall edge).mpr hIncident
  obtain ⟨label, rfl⟩ := star.exists_edge_eq edge hMem
  rw [star.right_edge, selected_endpoint,
    position.gauge.gaugedData_edgePartition star hConnected hGenus]
  unfold endpoint
  split_ifs with hSide
  · exact position.refines_left hConnected hGenus hNoGlue label hSide
  · apply position.refines_right hConnected hGenus hNoGlue label
    cases hValue : W4TargetPairings.Pairing.labelRight pairing label <;>
      cases side <;> simp_all

/-- **Riemann--Hurwitz receipt** on either side, over the gauged datum. -/
theorem selected_riemannHurwitz (b : Bool) (block : Fin degree)
    (hBlock : (position.datum.vertexPartition wall).Rel anchor.1 block) :
    LocalResolution.RiemannHurwitzAtBlock (position.datum.vertexPartition wall)
      (position.endpoint b)
      (position.split.newEdge ::
        (W4Assembly.oldEdgesAtSide star pairing b).map position.datum.edgePartition) block := by
  rw [position.datum_vertexPartition_wall] at hBlock ⊢
  by_cases hSide : b = side
  · subst hSide
    rw [endpoint_side]
    exact position.riemannHurwitz_left hConnected hGenus hNoGlue block hBlock
  · have hOther : b = !side := by cases b <;> cases side <;> simp_all
    subst hOther
    rw [endpoint_not_side]
    exact position.riemannHurwitz_right hConnected hGenus hNoGlue block hBlock

/-- **The general-`K` global candidate**: the selected general-`K` local
resolution installed into the guarded background of the other wall blocks,
over the gauged datum. -/
noncomputable def candidate
    (geometry : PairingBackground position.datum star pairing anchor.1) :
    BalancedGlobal.Candidate target degree position.datum wall :=
  geometry.background.install position.selected position.selected_contracts
    (position.selected_exterior hConnected hGenus hNoGlue)
    (fun block hRel _ ↦ by
      rw [selected_left, selected_newEdge]
      simpa [W4Assembly.oldEdgesAtSide, PairingBackground.background] using
        position.selected_riemannHurwitz hConnected hGenus hNoGlue false block hRel)
    (fun block hRel _ ↦ by
      rw [selected_right, selected_newEdge]
      simpa [W4Assembly.oldEdgesAtSide, PairingBackground.background] using
        position.selected_riemannHurwitz hConnected hGenus hNoGlue true block hRel)

variable (geometry : PairingBackground position.datum star pairing anchor.1)

theorem candidate_datum_valid (hValid : data.Valid) :
    (position.candidate hConnected hGenus hNoGlue geometry).datum.Valid :=
  (position.candidate hConnected hGenus hNoGlue geometry).datum_valid
    (position.datum_valid hValid)

/-- On the distinguished wall block the candidate uses the general-`K`
resolution itself. -/
theorem candidate_resolution_of_wall_rel (block : Fin degree)
    (hRel : (position.datum.vertexPartition wall).Rel anchor.1 block) :
    (position.candidate hConnected hGenus hNoGlue geometry).resolution block =
      position.selected := by
  unfold candidate PairingBackground.background GlobalM11Arbitrary.Background.install
  exact LocalResolution.onBlock_of_rel _ _ _ _ _ hRel

theorem candidate_resolution_anchor :
    (position.candidate hConnected hGenus hNoGlue geometry).resolution anchor.1 =
      position.selected :=
  position.candidate_resolution_of_wall_rel hConnected hGenus hNoGlue geometry anchor.1
    rfl

/-- **`K` is recorded in the candidate.**  At the distinguished block, on the
minus endpoint, the new edge induces exactly `K + 1` classes at the bridge
sheet; on the plus endpoint, `K' + 1`. -/
theorem candidate_K_receipts :
    ((position.candidate hConnected hGenus hNoGlue geometry).resolution
        anchor.1).newEdge.blockCountWithin (position.endpoint side) position.split.bridge =
        position.split.K + 1 ∧
      ((position.candidate hConnected hGenus hNoGlue geometry).resolution
        anchor.1).newEdge.blockCountWithin (position.endpoint (!side)) position.split.bridge =
        position.split.coK + 1 := by
  rw [position.candidate_resolution_anchor hConnected hGenus hNoGlue geometry,
    selected_newEdge, endpoint_side, endpoint_not_side]
  exact ⟨position.split.newEdge_blockCountWithin_left_eq,
    position.split.newEdge_blockCountWithin_right_eq⟩

omit hConnected hGenus hNoGlue in
/-- The paper's `k₁ = k_α + k_β - 1 - 2K`. -/
theorem bridgeSheets_card_add_two_K :
    position.split.bridgeSheets.card + 2 * position.split.K + 1 =
      sideIndex source pairing side := by
  have hCard := position.minus_card
  have hK := position.split.bridgeSheets_card_add_K
  omega

/-- **The new source edge has index `k₁ = k_α + k_β - 1 - 2K`** in the
outgoing gluing datum itself. -/
theorem candidate_newSourceEdge_index :
    (position.candidate hConnected hGenus hNoGlue geometry).datum.sourceEdgeIndex
        ((position.candidate hConnected hGenus hNoGlue geometry).newSourceEdge
          position.split.bridge) + 2 * position.split.K + 1 =
      sideIndex source pairing side := by
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge,
    LocalResolution.paste_newEdge_blockCard]
  have hBridge : (position.datum.vertexPartition wall).Rel anchor.1 position.split.bridge := by
    rw [position.datum_vertexPartition_wall]
    exact ((data.vertexPartition wall).mem_block_iff _ _).mp
      (position.split.bridgeSheets_subset position.split.bridge_mem_bridgeSheets)
  have hRepr : (position.datum.vertexPartition wall).Rel anchor.1
      ((position.datum.vertexPartition wall).repr position.split.bridge) :=
    hBridge.trans ((position.datum.vertexPartition wall).rel_repr_right _)
  rw [position.candidate_resolution_of_wall_rel hConnected hGenus hNoGlue geometry _ hRepr,
    selected_newEdge, position.split.newEdge_blockCard_bridge]
  exact position.bridgeSheets_card_add_two_K

/-- **The general-`K` candidate preserves the source genus**, given the
blockwise Euler identity of the background at the other wall blocks (the
`K = 0` exit gets that from its canonical W4 patterns being stars). -/
theorem candidate_sourceGenus
    (hEuler : ∀ block, ¬(position.datum.vertexPartition wall).Rel anchor.1 block →
      (geometry.resolution block).newEdge.blockCountWithin
          (position.datum.vertexPartition wall) block + 1 =
        (geometry.resolution block).left.blockCountWithin
            (position.datum.vertexPartition wall) block +
          (geometry.resolution block).right.blockCountWithin
            (position.datum.vertexPartition wall) block) :
    genus (position.candidate hConnected hGenus hNoGlue geometry).datum.sourceGraph =
      genus position.datum.sourceGraph := by
  apply M11SourceGenus.candidate_sourceGenus_of_blockwise_euler
  intro block _
  by_cases hBlock : (position.datum.vertexPartition wall).Rel anchor.1 block
  · rw [position.candidate_resolution_of_wall_rel hConnected hGenus hNoGlue geometry block
      hBlock, position.datum_vertexPartition_wall]
    rw [position.datum_vertexPartition_wall] at hBlock
    exact position.selected_euler block hBlock
  · have hRes : (position.candidate hConnected hGenus hNoGlue geometry).resolution block =
        geometry.resolution block := by
      unfold candidate PairingBackground.background GlobalM11Arbitrary.Background.install
      exact LocalResolution.onBlock_of_not_rel _ _ _ _ _ hBlock
    rw [hRes]
    exact hEuler block hBlock

end Install

end Position

end Datum

/-! ## 6.  Headline -/

section Headline

open NonTrivalentValencyFourKZero
open NonTrivalentValencyFourKZero.PrescribedPairing

variable {target : CFGraph} {wall : target.V} {data : GluingDatum target degree}
  {star : W4TargetPairings.FourStar target wall} {anchor : W4Assembly.WallBlock data wall}

/-- **Headline.**  At a four-branch anchor, for every prescribed pairing and
every `K` in the paper's range `K + 1 ≤ min k`, `K + max k ≤ |A|`
(Part II's `0 ≤ K ≤ min(k₂-1, |A|-k₅)`), a general-`K` position exists at the
smaller side, with exactly this `K`. -/
theorem exists_position_of_range (source : FourBranchAnchor data star anchor)
    (pairing : Fin 3) (hNoGlue : W4StableSource.DanglingEdgeNoGlue data)
    (hRamification : data.localRamification wall anchor = 0) {K : ℕ}
    (hLower : ∀ label, K + 1 ≤ source.index label)
    (hUpper : ∀ label,
      K + source.index label ≤ (data.vertexPartition wall).blockCard anchor.1) :
    ∃ position : Position source pairing (smallerSide source pairing),
      position.split.K = K ∧
        position.split.coK = coIndex source pairing (smallerSide source pairing) K :=
  (exists_position source pairing _ hNoGlue hRamification
    ((admissible_smallerSide_iff source pairing hNoGlue hRamification K).mpr
      ⟨hLower, hUpper⟩)).imp fun _ h ↦ ⟨h.1, h.2.1⟩

/-- **The range is sharp.**  Every position, at either side, has its `K` in
the admissible range: `Admissible` is exactly the set of `K` realised by
positions (with `exists_position`). -/
theorem admissible_of_position (source : FourBranchAnchor data star anchor)
    (pairing : Fin 3) {side : Bool} (position : Position source pairing side) :
    Admissible source pairing side position.split.K := by
  have hMinusCard := position.minus_card
  have hPlusCard := position.plus_card
  have hMinusCoK := position.split.card_minus_add_coK
  have hPlusK := position.split.card_plus_add_K
  have hIndexMinus := sideIndex_eq_add source pairing side
  have hLe (label : Fin 4) (sheets : Finset (Fin degree))
      (hSub : gaugedBlock source position.gauge label ⊆ sheets) :
      source.index label ≤ sheets.card := by
    have hCard : (gaugedBlock source position.gauge label).card = source.index label := by
      unfold gaugedBlock
      rw [Finset.card_image_of_injective _ (position.gauge.perm label).injective]
      rfl
    rw [← hCard]
    exact Finset.card_le_card hSub
  have h1 := hLe _ _ (position.minus_sub _ (labelRight_firstLabel pairing side))
  have h2 := hLe _ _ (position.minus_sub _ (labelRight_secondLabel pairing side))
  have h3 := hLe _ _ (position.plus_sub _ (labelRight_firstLabel pairing (!side)))
  have h4 := hLe _ _ (position.plus_sub _ (labelRight_secondLabel pairing (!side)))
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- **`Admissible` as an interface**: it holds exactly at the values of `K`
realised by a position. -/
theorem admissible_iff_exists_position (source : FourBranchAnchor data star anchor)
    (pairing : Fin 3) (side : Bool) (hNoGlue : W4StableSource.DanglingEdgeNoGlue data)
    (hRamification : data.localRamification wall anchor = 0) (K : ℕ) :
    Admissible source pairing side K ↔
      ∃ position : Position source pairing side, position.split.K = K := by
  constructor
  · intro hAdmissible
    obtain ⟨position, hK, -⟩ :=
      exists_position source pairing side hNoGlue hRamification hAdmissible
    exact ⟨position, hK⟩
  · rintro ⟨position, rfl⟩
    exact admissible_of_position source pairing position

end Headline

end DraismaVargas.Count.GeneralKReceipts
