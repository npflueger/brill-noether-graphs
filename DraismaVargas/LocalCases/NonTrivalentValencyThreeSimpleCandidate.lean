import DraismaVargas.LocalCases.NonTrivalentValencyThreeCandidate

/-!
# Part II, valency three: the prescribed candidates of Types I and II

Source: Vargas, Part II (arXiv:2609.09109), Section 5.3 (valency-3 limits,
Case {v3-nd4}), in particular the paragraph on the base trees `T_alpha`,
`alpha` in `{3,4}`.

## What this module adds to `NonTrivalentValencyThreeCandidate`

That module builds the base tree `T_2` of the source, i.e. the outgoing
resolution whose divalent subdivision point `u` lies on the *doubled*
direction; that is Type III (`H_{2,5}`).  The outer walk realizes a
*prescribed* Whitehead move, and the source proves that at a three-valent wall
each of Types I, II and III is realized, so the prescribed-type route also
needs the two base trees `T_alpha` with `alpha` a *simple* direction.  This
module builds those.

Labels, in the source's numbering: `e_2, e_5` are the two surviving
occurrences above the doubled direction `t_2`, `e_3` above `t_3` and `e_4`
above `t_4`, and the wall identity is
`k_2 + k_3 + k_4 + k_5 = 2|A| + 1`  (the identity `(boxplus)` of
`NonTrivalentValencyThreeCandidate`).
For a base tree `T_alpha` with `alpha` simple, `beta` the other simple
direction, and `delta` one of the two doubled survivors (`gamma` the other),
the anchor `A` resolves into **three** vertices:

* `A_u` above the divalent subdivision point `u`, with `|A_u| = k_alpha`,
  incident to `e_alpha`, the bridge `e_1` (above `t_1`, of index
  `k_1 = k_alpha - k_delta`) and a second occurrence `e'` above `t_1` of index
  `k_delta`;
* `A'` above `v`, divalent, with `|A'| = k_delta`: it carries `e'` on one side
  and `e_delta` on the other, so the stable edge `h_delta` runs
  `A_u -> A' -> e_delta` passing above `t_1`;
* `A_v` above `v`, with `|A_v| = |A| - k_delta`, incident to `e_1`, `e_beta`
  and `e_gamma`.

The realizability condition is `|A| >= k_beta + k_delta` (equivalently
`k_alpha + k_gamma >= |A| + 1`), which also forces `k_alpha > k_delta`.  The
resulting type has `{h_alpha, h_delta}` meeting at `A_u` and
`{h_beta, h_gamma}` at `A_v`.

## The two sheet gauges

Unlike Type III, these resolutions cannot be installed over the incoming
datum itself.  `A' = e' = e_delta` forces the `delta` class to sit *inside*
the `alpha` class, and `A'` must miss the `beta` class.  Both are arranged by
block-preserving branch swaps (`BlockPreservingBranchSwap.branchSwapOfPerm`),
one across the doubled direction and one across `t_beta`; the two branches of
a genus-zero connected target are separated, so the swaps commute with the
data they must not move.  The first swap needs `k_delta <= k_alpha` and the
second needs `k_beta <= |A| - k_delta`: exactly the paper's two vertex
inequalities.  The candidate therefore lives over `gaugedData`, as at valency
four (`NonTrivalentValencyFourKZero.PrescribedPairing.gaugedData`).

## What is proved

* `exists_perm_image_subset`: the finite gauge move (one class into another).
* `blockRefine`: the three-block refinement of one wall block, and its block
  calculus.
* `SimpleBase`, `leftPartition`, `newEdgePartition`, `rightPartition`,
  `selectedResolution`: the local resolution at the anchor and its
  contraction, with the exact block sizes `|A_u| = k_alpha`,
  `|A'| = k_delta`, `|A_v| = |A| - k_delta`.
* `selected_riemannHurwitz_left` / `selected_riemannHurwitz_right`: both
  endpoint inequalities.  The divalent side `u` is automatic; on the
  trivalent side both new vertices `A'` and `A_v` hold with *equality*
  (`selected_counts_eq`, i.e. `r = 0` at each of them), and that is where
  `(boxplus)` enters.
* `SubdivisionBackground`, `subdivisionBackground`,
  `nonempty_subdivisionBackground`: the guarded background of the other wall
  blocks.  At `T_alpha` the single global resolution is
  `fineResolution (vertexPartition wall) (edgePartition (directionEdge star alpha))`
  -- the subdivision point lies on a simple direction, so the
  `edgePartition doubled` of `NonTrivalentValencyThreeCandidate` is replaced by
  the `alpha` direction; the producer is otherwise the same and is re-proved
  here, the Type III producer not being parametric in the direction.
* `validCandidate`, `validCandidate_datum_valid`: the candidate and the
  validity of its outgoing datum.
* `meeting_at_divalent_endpoint`, identifying the two surviving directions that
  meet at `A_u`.

The prescribed choices are: the pair `(alpha, delta) = (4,2)`, available
unconditionally, for Type II; and for Type I the pair `(3,2)` when
`k_4 + k_2 <= |A|`, else `(4,5)`.

## What is NOT proved

* `nd(A) = 4` at the wall block stays an explicit hypothesis, as in
  `NonTrivalentValencyThreeCandidate`.
* `graph_connected target` and `genus target = 0` are explicit hypotheses:
  the two branch swaps need the target's branches to be separated.  The
  Type III candidate of `NonTrivalentValencyThreeCandidate` needs neither.
* No stable type, row dictionary, honest matrix or pencil: those follow in
  `NonTrivalentValencyThreeSimpleRows` and the modules after it.

## Consumers

The boundary dispatcher for Part II, Case {v3-nd4}
(`NonTrivalentValencyThreeDispatcher`), and through it
`OuterWalk.TypeChangeLink`.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleCandidate

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases.GlobalM11Arbitrary
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionCoarseFine
open DraismaVargas.LocalCases.ResolutionM1k
open DraismaVargas.LocalCases.NonTrivalentValencyThreeAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyThreeCandidate
open DraismaVargas.LocalCases.BlockPreservingBranchSwap
open DraismaVargas.LocalCases.ThirdEquation
open W4Assembly W4StableSource

/-! ## 1.  Moving one finite class inside another

The gauge move of this module.  `BlockPreservingBranchSwap` has the valency-four
version, which puts two classes in one-sheet overlap; here one class must be
carried *inside* another, which is possible exactly when it is no larger. -/

private theorem exists_perm_image_subset_aux {degree : ℕ}
    (whole small : Finset (Fin degree)) (hSmall : small ⊆ whole) :
    ∀ steps (other : Finset (Fin degree)),
      (other \ small).card ≤ steps → other ⊆ whole →
      other.card ≤ small.card →
      ∃ permutation : Equiv.Perm (Fin degree),
        (∀ sheet ∈ whole, permutation sheet ∈ whole) ∧
          (∀ sheet, sheet ∉ whole → permutation sheet = sheet) ∧
          other.image permutation ⊆ small := by
  classical
  intro steps
  induction steps with
  | zero =>
      intro other hLe hOther _
      refine ⟨Equiv.refl _, fun _ h ↦ h, fun _ _ ↦ rfl, ?_⟩
      have hEmpty : other \ small = ∅ :=
        Finset.card_eq_zero.mp (Nat.le_zero.mp hLe)
      have hSubset : other ⊆ small := Finset.sdiff_eq_empty_iff_subset.mp hEmpty
      intro sheet hSheet
      obtain ⟨original, hOriginal, rfl⟩ := Finset.mem_image.mp hSheet
      simpa using hSubset hOriginal
  | succ steps ih =>
      intro other hLe hOther hCard
      by_cases hEmpty : (other \ small).card = 0
      · exact ih other (by omega) hOther hCard
      · obtain ⟨moved, hMoved⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hEmpty)
        have hMovedOther : moved ∈ other := (Finset.mem_sdiff.mp hMoved).1
        have hMovedSmall : moved ∉ small := (Finset.mem_sdiff.mp hMoved).2
        have hOtherSplit := Finset.card_sdiff_add_card_inter other small
        have hSmallSplit := Finset.card_sdiff_add_card_inter small other
        have hInter : (other ∩ small).card = (small ∩ other).card := by
          rw [Finset.inter_comm]
        have hFreeCard : 0 < (small \ other).card := by omega
        obtain ⟨free, hFree⟩ := Finset.card_pos.mp hFreeCard
        have hFreeSmall : free ∈ small := (Finset.mem_sdiff.mp hFree).1
        have hFreeOther : free ∉ other := (Finset.mem_sdiff.mp hFree).2
        have hMovedWhole : moved ∈ whole := hOther hMovedOther
        have hFreeWhole : free ∈ whole := hSmall hFreeSmall
        have hStepWhole : ∀ sheet, sheet ∈ whole →
            (Equiv.swap moved free) sheet ∈ whole := by
          intro sheet hSheet
          rw [Equiv.swap_apply_def]
          split_ifs
          · exact hFreeWhole
          · exact hMovedWhole
          · exact hSheet
        have hStepOut : ∀ sheet, sheet ∉ whole →
            (Equiv.swap moved free) sheet = sheet := by
          intro sheet hSheet
          apply Equiv.swap_apply_of_ne_of_ne
          · rintro rfl
            exact hSheet hMovedWhole
          · rintro rfl
            exact hSheet hFreeWhole
        set next := other.image (Equiv.swap moved free) with hNextDef
        have hNextSub : next ⊆ whole := by
          intro sheet hSheet
          obtain ⟨original, hOriginal, rfl⟩ := Finset.mem_image.mp hSheet
          exact hStepWhole original (hOther hOriginal)
        have hNextCard : next.card = other.card :=
          Finset.card_image_of_injective _ (Equiv.injective _)
        have hNextSdiff : next \ small ⊆ (other \ small).erase moved := by
          intro sheet hSheet
          rw [Finset.mem_sdiff] at hSheet
          obtain ⟨original, hOriginal, hImage⟩ := Finset.mem_image.mp hSheet.1
          have hOriginalNeFree : original ≠ free := by
            rintro rfl
            exact hFreeOther hOriginal
          have hOriginalNeMoved : original ≠ moved := by
            rintro rfl
            rw [Equiv.swap_apply_left] at hImage
            exact hSheet.2 (hImage ▸ hFreeSmall)
          rw [Equiv.swap_apply_of_ne_of_ne hOriginalNeMoved hOriginalNeFree]
            at hImage
          subst hImage
          exact Finset.mem_erase.mpr
            ⟨hOriginalNeMoved, Finset.mem_sdiff.mpr ⟨hOriginal, hSheet.2⟩⟩
        have hNextLe : (next \ small).card ≤ steps := by
          have hErase := Finset.card_erase_of_mem hMoved
          have hLeErase := Finset.card_le_card hNextSdiff
          omega
        obtain ⟨rest, hRestWhole, hRestOut, hRestImage⟩ :=
          ih next hNextLe hNextSub (by omega)
        refine ⟨(Equiv.swap moved free).trans rest, ?_, ?_, ?_⟩
        · intro sheet hSheet
          exact hRestWhole _ (hStepWhole sheet hSheet)
        · intro sheet hSheet
          simp only [Equiv.trans_apply]
          rw [hStepOut sheet hSheet]
          exact hRestOut sheet hSheet
        · have hImage : other.image ((Equiv.swap moved free).trans rest) =
              next.image rest := by
            rw [hNextDef, Finset.image_image]
            rfl
          rw [hImage]
          exact hRestImage

/-- **The gauge move.**  A class no larger than another, both inside one wall
block, can be carried inside it by a permutation that preserves the block and
fixes every sheet outside it. -/
theorem exists_perm_image_subset {degree : ℕ}
    (whole small other : Finset (Fin degree))
    (hSmall : small ⊆ whole) (hOther : other ⊆ whole)
    (hCard : other.card ≤ small.card) :
    ∃ permutation : Equiv.Perm (Fin degree),
      (∀ sheet ∈ whole, permutation sheet ∈ whole) ∧
        (∀ sheet, sheet ∉ whole → permutation sheet = sheet) ∧
        other.image permutation ⊆ small :=
  exists_perm_image_subset_aux whole small hSmall (other \ small).card other
    le_rfl hOther hCard

/-! ## 2.  Refining one wall block by a choice of representatives

The Type I/II resolution needs a wall block cut into *three* pieces, so the
one-distinguished-class constructor
`NonTrivalentValencyFourKZero.PrescribedPairing.withSelectedBlock` does not
suffice.  `blockRefine` refines a single coarse block along an arbitrary
idempotent choice of representatives inside it. -/

section BlockRefine

variable {degree : ℕ}

/-- Refine the coarse block of `anchor` by an idempotent representative
choice `pick`, leaving every other coarse block unchanged. -/
def blockRefine (coarse : SheetPartition degree) (anchor : Fin degree)
    (pick : Fin degree → Fin degree)
    (hPick : ∀ sheet, coarse.Rel anchor sheet → coarse.Rel anchor (pick sheet))
    (hIdem : ∀ sheet, coarse.Rel anchor sheet → pick (pick sheet) = pick sheet) :
    SheetPartition degree where
  repr := fun sheet ↦
    if coarse.Rel anchor sheet then pick sheet else coarse.repr sheet
  repr_idem := by
    intro sheet
    by_cases hSheet : coarse.Rel anchor sheet
    · rw [if_pos hSheet, if_pos (hPick sheet hSheet), hIdem sheet hSheet]
    · have hNot : ¬coarse.Rel anchor (coarse.repr sheet) := by
        intro hRel
        exact hSheet (hRel.trans (coarse.rel_repr_left sheet))
      rw [if_neg hSheet, if_neg hNot, coarse.repr_idem]

namespace blockRefine

variable (coarse : SheetPartition degree) (anchor : Fin degree)
  (pick : Fin degree → Fin degree)
  (hPick : ∀ sheet, coarse.Rel anchor sheet → coarse.Rel anchor (pick sheet))
  (hIdem : ∀ sheet, coarse.Rel anchor sheet → pick (pick sheet) = pick sheet)

theorem repr_of_rel {sheet : Fin degree} (hSheet : coarse.Rel anchor sheet) :
    (blockRefine coarse anchor pick hPick hIdem).repr sheet = pick sheet := by
  change (if coarse.Rel anchor sheet then pick sheet else coarse.repr sheet) = _
  rw [if_pos hSheet]

theorem repr_of_not_rel {sheet : Fin degree} (hSheet : ¬coarse.Rel anchor sheet) :
    (blockRefine coarse anchor pick hPick hIdem).repr sheet =
      coarse.repr sheet := by
  change (if coarse.Rel anchor sheet then pick sheet else coarse.repr sheet) = _
  rw [if_neg hSheet]

theorem refines :
    (blockRefine coarse anchor pick hPick hIdem).Refines coarse := by
  intro first second hFine
  rw [SheetPartition.rel_iff] at hFine
  by_cases hFirst : coarse.Rel anchor first
  · by_cases hSecond : coarse.Rel anchor second
    · exact hFirst.symm.trans hSecond
    · exfalso
      apply hSecond
      rw [repr_of_rel coarse anchor pick hPick hIdem hFirst,
        repr_of_not_rel coarse anchor pick hPick hIdem hSecond] at hFine
      have hMoved := hPick first hFirst
      unfold SheetPartition.Rel at hMoved ⊢
      rw [hFine] at hMoved
      simpa only [coarse.repr_idem] using hMoved
  · by_cases hSecond : coarse.Rel anchor second
    · exfalso
      apply hFirst
      rw [repr_of_not_rel coarse anchor pick hPick hIdem hFirst,
        repr_of_rel coarse anchor pick hPick hIdem hSecond] at hFine
      have hMoved := hPick second hSecond
      unfold SheetPartition.Rel at hMoved ⊢
      rw [← hFine] at hMoved
      simpa only [coarse.repr_idem] using hMoved
    · rw [repr_of_not_rel coarse anchor pick hPick hIdem hFirst,
        repr_of_not_rel coarse anchor pick hPick hIdem hSecond] at hFine
      exact hFine

theorem rel_iff_of_rel {first second : Fin degree}
    (hFirst : coarse.Rel anchor first) (hSecond : coarse.Rel anchor second) :
    (blockRefine coarse anchor pick hPick hIdem).Rel first second ↔
      pick first = pick second := by
  unfold SheetPartition.Rel
  rw [repr_of_rel coarse anchor pick hPick hIdem hFirst,
    repr_of_rel coarse anchor pick hPick hIdem hSecond]

/-- The block calculus: inside the refined coarse block, blocks are the
fibres of `pick`. -/
theorem block_of_rel {sheet : Fin degree} (hSheet : coarse.Rel anchor sheet) :
    (blockRefine coarse anchor pick hPick hIdem).block sheet =
      (coarse.block anchor).filter (fun other ↦ pick other = pick sheet) := by
  classical
  ext other
  rw [SheetPartition.mem_block_iff, Finset.mem_filter, SheetPartition.mem_block_iff]
  constructor
  · intro hRel
    have hOther : coarse.Rel anchor other := by
      exact hSheet.trans (refines coarse anchor pick hPick hIdem |>.rel hRel)
    exact ⟨hOther,
      ((rel_iff_of_rel coarse anchor pick hPick hIdem hSheet hOther).mp hRel).symm⟩
  · rintro ⟨hOther, hEq⟩
    exact (rel_iff_of_rel coarse anchor pick hPick hIdem hSheet hOther).mpr hEq.symm

/-- Comparing two refinements of the same coarse block. -/
theorem refines_blockRefine (coarse : SheetPartition degree) (anchor : Fin degree)
    (fine coarseChoice : Fin degree → Fin degree)
    (hFine : ∀ sheet, coarse.Rel anchor sheet → coarse.Rel anchor (fine sheet))
    (hFineIdem : ∀ sheet, coarse.Rel anchor sheet → fine (fine sheet) = fine sheet)
    (hCoarse : ∀ sheet, coarse.Rel anchor sheet → coarse.Rel anchor (coarseChoice sheet))
    (hCoarseIdem : ∀ sheet, coarse.Rel anchor sheet →
      coarseChoice (coarseChoice sheet) = coarseChoice sheet)
    (hCompatible : ∀ first second, coarse.Rel anchor first → coarse.Rel anchor second →
      fine first = fine second → coarseChoice first = coarseChoice second) :
    (blockRefine coarse anchor fine hFine hFineIdem).Refines
      (blockRefine coarse anchor coarseChoice hCoarse hCoarseIdem) := by
  intro first second hRel
  have hCoarseRel : coarse.Rel first second :=
    (refines coarse anchor fine hFine hFineIdem).rel hRel
  by_cases hFirst : coarse.Rel anchor first
  · have hSecond : coarse.Rel anchor second := hFirst.trans hCoarseRel
    refine (rel_iff_of_rel coarse anchor coarseChoice hCoarse hCoarseIdem
      hFirst hSecond).mpr ?_
    exact hCompatible first second hFirst hSecond
      ((rel_iff_of_rel coarse anchor fine hFine hFineIdem hFirst hSecond).mp hRel)
  · have hSecond : ¬coarse.Rel anchor second := by
      intro hMem
      exact hFirst (hMem.trans hCoarseRel.symm)
    unfold SheetPartition.Rel
    rw [repr_of_not_rel coarse anchor coarseChoice hCoarse hCoarseIdem hFirst,
      repr_of_not_rel coarse anchor coarseChoice hCoarse hCoarseIdem hSecond]
    exact hCoarseRel

/-- Identify one block of a refined coarse block by a membership criterion. -/
theorem block_eq_of_iff (coarse : SheetPartition degree) (anchor : Fin degree)
    (pick : Fin degree → Fin degree)
    (hPick : ∀ sheet, coarse.Rel anchor sheet → coarse.Rel anchor (pick sheet))
    (hIdem : ∀ sheet, coarse.Rel anchor sheet → pick (pick sheet) = pick sheet)
    {sheet : Fin degree} (hSheet : coarse.Rel anchor sheet)
    (selected : Finset (Fin degree)) (hSubset : selected ⊆ coarse.block anchor)
    (hCriterion : ∀ other, coarse.Rel anchor other →
      (pick other = pick sheet ↔ other ∈ selected)) :
    (blockRefine coarse anchor pick hPick hIdem).block sheet = selected := by
  classical
  rw [block_of_rel coarse anchor pick hPick hIdem hSheet]
  ext other
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hWall, hEq⟩
    exact (hCriterion other ((coarse.mem_block_iff anchor other).mp hWall)).mp hEq
  · intro hOther
    have hWall := hSubset hOther
    exact ⟨hWall,
      (hCriterion other ((coarse.mem_block_iff anchor other).mp hWall)).mpr hOther⟩

end blockRefine

theorem blockCountWithin_congr (fine coarse : SheetPartition degree)
    {first second : Fin degree} (hRel : coarse.Rel first second) :
    fine.blockCountWithin coarse first = fine.blockCountWithin coarse second := by
  unfold SheetPartition.blockCountWithin
  rw [coarse.block_eq_of_rel hRel]

theorem blockCard_congr (partition : SheetPartition degree)
    {first second : Fin degree} (hRel : partition.Rel first second) :
    partition.blockCard first = partition.blockCard second := by
  unfold SheetPartition.blockCard
  rw [partition.block_eq_of_rel hRel]

/-- Two partitions refining a common coarse one join back to it as soon as
every sheet of each coarse block is joined to one hub sheet by one of them. -/
theorem isJoin_of_hub (left right coarse : SheetPartition degree)
    (anchor hub : Fin degree) (hLeft : left.Refines coarse)
    (hRight : right.Refines coarse)
    (hOutside : ∀ first second, ¬coarse.Rel anchor first → coarse.Rel first second →
      left.Rel first second)
    (hInside : ∀ sheet, coarse.Rel anchor sheet →
      left.Rel sheet hub ∨ right.Rel sheet hub) :
    SheetPartition.IsJoin left right coarse := by
  have hStep : ∀ sheet, coarse.Rel anchor sheet →
      Relation.EqvGen (fun a b ↦ left.Rel a b ∨ right.Rel a b) sheet hub := by
    intro sheet hSheet
    rcases hInside sheet hSheet with hRel | hRel
    · exact Relation.EqvGen.rel _ _ (Or.inl hRel)
    · exact Relation.EqvGen.rel _ _ (Or.inr hRel)
  intro first second
  constructor
  · intro hRel
    by_cases hFirst : coarse.Rel anchor first
    · have hSecond : coarse.Rel anchor second := hFirst.trans hRel
      exact Relation.EqvGen.trans first hub second (hStep first hFirst)
        (Relation.EqvGen.symm _ _ (hStep second hSecond))
    · exact Relation.EqvGen.rel first second
        (Or.inl (hOutside first second hFirst hRel))
  · intro hGenerated
    induction hGenerated with
    | rel x y hxy => exact hxy.elim hLeft.rel hRight.rel
    | refl => exact rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ hFirst hSecond => exact hFirst.trans hSecond

end BlockRefine


/-! ## 3.  The four surviving classes at the anchor

The classifier `NonTrivalentValencyThreeAnchor.ThreeBranchAnchor` gives the
`2+1+1` distribution of the four surviving
occurrences over the three star directions.  Here they are named in the
source's order: the two doubled survivors `delta`, `gamma` and the two simple
survivors `alpha`, `beta`. -/

section Anchor

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (data : GluingDatum target degree)
    (vertex : data.SourceVertex) : DecidableEq (IncidentSourceEdge data vertex) :=
  Classical.decEq _

variable {data : GluingDatum target degree} {star : ThreeStar target wall}
  {anchor : WallBlock data wall}

/-- The literal sheet class of one source occurrence. -/
noncomputable def occurrenceBlock (data : GluingDatum target degree)
    {vertex : data.SourceVertex} (edge : IncidentSourceEdge data vertex) :
    Finset (Fin degree) :=
  (data.edgePartition edge.1.1.1).block (Prescribed.occurrenceSheet edge)

theorem occurrenceBlock_card {vertex : data.SourceVertex}
    (edge : IncidentSourceEdge data vertex) :
    (occurrenceBlock data edge).card = data.sourceEdgeIndex edge.1 := rfl

theorem occurrenceSheet_mem_occurrenceBlock {vertex : data.SourceVertex}
    (edge : IncidentSourceEdge data vertex) :
    Prescribed.occurrenceSheet edge ∈ occurrenceBlock data edge :=
  (data.edgePartition edge.1.1.1).self_mem_block _

theorem occurrenceBlock_eq_direction {label : Fin 3}
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor label) :
    occurrenceBlock data edge =
      (data.edgePartition (directionEdge star label)).block
        (Prescribed.occurrenceSheet edge) := by
  unfold occurrenceBlock
  rw [((mem_directionSurvivors data star anchor label edge).mp hEdge).2]

theorem mem_occurrenceBlock_iff {label : Fin 3}
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor label) (sheet : Fin degree) :
    sheet ∈ occurrenceBlock data edge ↔
      (data.edgePartition (directionEdge star label)).Rel
        (Prescribed.occurrenceSheet edge) sheet := by
  rw [occurrenceBlock_eq_direction hEdge, SheetPartition.mem_block_iff]

theorem occurrenceBlock_subset_wall {label : Fin 3}
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor label) :
    occurrenceBlock data edge ⊆ (data.vertexPartition wall).block anchor.1 := by
  intro sheet hSheet
  rw [mem_occurrenceBlock_iff hEdge] at hSheet
  refine ((data.vertexPartition wall).mem_block_iff _ _).mpr ?_
  exact (Prescribed.occurrenceSheet_wall_rel edge).trans
    ((Prescribed.directionEdge_refines (data := data) (star := star) label).rel hSheet)

/-- The index sum of the surviving occurrences of one star direction: `k_3`
or `k_4` at a simple direction, `k_2 + k_5` at the doubled one. -/
noncomputable def directionIndex (data : GluingDatum target degree)
    (star : ThreeStar target wall) (anchor : WallBlock data wall)
    (label : Fin 3) : ℕ :=
  ∑ edge ∈ directionSurvivors data star anchor label, data.sourceEdgeIndex edge.1

/-- The unique surviving occurrence of a simple direction. -/
noncomputable def simpleSurvivor (source : ThreeBranchAnchor data star anchor)
    (label : Fin 3) (hLabel : label ≠ Prescribed.doubled source) :
    IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor) :=
  Classical.choose
    (Finset.card_eq_one.mp (source.distribution.other_count label hLabel))

theorem directionSurvivors_simple_eq (source : ThreeBranchAnchor data star anchor)
    (label : Fin 3) (hLabel : label ≠ Prescribed.doubled source) :
    directionSurvivors data star anchor label = {simpleSurvivor source label hLabel} :=
  Classical.choose_spec
    (Finset.card_eq_one.mp (source.distribution.other_count label hLabel))

theorem simpleSurvivor_mem (source : ThreeBranchAnchor data star anchor)
    (label : Fin 3) (hLabel : label ≠ Prescribed.doubled source) :
    simpleSurvivor source label hLabel ∈ directionSurvivors data star anchor label := by
  rw [directionSurvivors_simple_eq source label hLabel]
  exact Finset.mem_singleton_self _

theorem directionIndex_simple (source : ThreeBranchAnchor data star anchor)
    (label : Fin 3) (hLabel : label ≠ Prescribed.doubled source) :
    directionIndex data star anchor label =
      data.sourceEdgeIndex (simpleSurvivor source label hLabel).1 := by
  rw [directionIndex, directionSurvivors_simple_eq source label hLabel,
    Finset.sum_singleton]

/-- Inside the anchor block a simple direction is its unique surviving class
together with dangling singletons. -/
theorem simple_shape (source : ThreeBranchAnchor data star anchor)
    (hNoGlue : DanglingEdgeNoGlue data) (label : Fin 3)
    (hLabel : label ≠ Prescribed.doubled source) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel anchor.1 sheet) :
    sheet ∈ occurrenceBlock data (simpleSurvivor source label hLabel) ∨
      (data.edgePartition (directionEdge star label)).block sheet = {sheet} := by
  rcases Prescribed.mem_survivorBlock_or_singleton (star := star) hNoGlue
      label sheet hWall with ⟨edge, hEdge, hRel⟩ | hSingleton
  · left
    rw [directionSurvivors_simple_eq source label hLabel, Finset.mem_singleton] at hEdge
    subst hEdge
    exact (mem_occurrenceBlock_iff (simpleSurvivor_mem source label hLabel) sheet).mpr hRel
  · exact Or.inr hSingleton

/-- One of the two surviving occurrences of the doubled direction, selected by
a Boolean. -/
noncomputable def doubledSurvivor (source : ThreeBranchAnchor data star anchor)
    (choice : Bool) : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor) :=
  if choice then Prescribed.secondDoubled source else Prescribed.firstDoubled source

@[simp] theorem doubledSurvivor_false (source : ThreeBranchAnchor data star anchor) :
    doubledSurvivor source false = Prescribed.firstDoubled source := rfl

@[simp] theorem doubledSurvivor_true (source : ThreeBranchAnchor data star anchor) :
    doubledSurvivor source true = Prescribed.secondDoubled source := rfl

theorem doubledSurvivor_mem (source : ThreeBranchAnchor data star anchor)
    (choice : Bool) :
    doubledSurvivor source choice ∈
      directionSurvivors data star anchor (Prescribed.doubled source) := by
  cases choice
  · exact Prescribed.firstDoubled_mem source
  · exact Prescribed.secondDoubled_mem source

theorem doubledSurvivor_ne (source : ThreeBranchAnchor data star anchor)
    (choice : Bool) :
    doubledSurvivor source choice ≠ doubledSurvivor source (!choice) := by
  cases choice
  · exact Prescribed.firstDoubled_ne_secondDoubled source
  · exact (Prescribed.firstDoubled_ne_secondDoubled source).symm

theorem directionIndex_doubled (source : ThreeBranchAnchor data star anchor)
    (choice : Bool) :
    directionIndex data star anchor (Prescribed.doubled source) =
      data.sourceEdgeIndex (doubledSurvivor source choice).1 +
        data.sourceEdgeIndex (doubledSurvivor source (!choice)).1 := by
  rw [directionIndex, Prescribed.directionSurvivors_doubled_eq_pair,
    Finset.sum_pair (Prescribed.firstDoubled_ne_secondDoubled source)]
  cases choice
  · rfl
  · exact Nat.add_comm _ _

/-- The two doubled classes are disjoint: they are distinct blocks of one and
the same edge partition. -/
theorem doubledSurvivor_block_disjoint (source : ThreeBranchAnchor data star anchor)
    (choice : Bool) :
    occurrenceBlock data (doubledSurvivor source choice) ∩
      occurrenceBlock data (doubledSurvivor source (!choice)) = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem ?_
  intro sheet hSheet
  rw [Finset.mem_inter,
    mem_occurrenceBlock_iff (doubledSurvivor_mem source choice),
    mem_occurrenceBlock_iff (doubledSurvivor_mem source (!choice))] at hSheet
  have hRel := hSheet.1.trans hSheet.2.symm
  have hMain := Prescribed.not_rel_occurrenceSheet_doubled source
  cases choice
  · exact hMain hRel
  · exact hMain hRel.symm

/-- Inside the anchor block the doubled direction is its two surviving
classes together with dangling singletons. -/
theorem doubled_shape (source : ThreeBranchAnchor data star anchor)
    (hNoGlue : DanglingEdgeNoGlue data) (choice : Bool) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel anchor.1 sheet) :
    sheet ∈ occurrenceBlock data (doubledSurvivor source choice) ∨
      sheet ∈ occurrenceBlock data (doubledSurvivor source (!choice)) ∨
      (data.edgePartition (Prescribed.doubledEdge source)).block sheet = {sheet} := by
  rcases Prescribed.mem_survivorBlock_or_singleton (star := star) hNoGlue
      (Prescribed.doubled source) sheet hWall with ⟨edge, hEdge, hRel⟩ | hSingleton
  · rw [Prescribed.directionSurvivors_doubled_eq_pair, Finset.mem_insert,
      Finset.mem_singleton] at hEdge
    have key : ∀ other : Bool, doubledSurvivor source other = edge →
        sheet ∈ occurrenceBlock data (doubledSurvivor source other) := by
      intro other hOther
      refine (mem_occurrenceBlock_iff (doubledSurvivor_mem source other) sheet).mpr ?_
      rw [hOther]
      exact hRel
    cases choice <;> rcases hEdge with rfl | rfl
    · exact Or.inl (key false rfl)
    · exact Or.inr (Or.inl (key true rfl))
    · exact Or.inr (Or.inl (key false rfl))
    · exact Or.inl (key true rfl)
  · exact Or.inr (Or.inr hSingleton)

end Anchor


/-! ## 4.  The prescribed pair `(alpha, delta)` and its arithmetic -/

section Base

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (data : GluingDatum target degree)
    (vertex : data.SourceVertex) : DecidableEq (IncidentSourceEdge data vertex) :=
  Classical.decEq _

variable {data : GluingDatum target degree} {star : ThreeStar target wall}
  {anchor : WallBlock data wall}

/-- The two simple directions of a trivalent star are the two rotations of
the doubled one. -/
private theorem fin_three_pair (doubled first second : Fin 3)
    (hFirst : first ≠ doubled) (hSecond : second ≠ doubled)
    (hDistinct : second ≠ first) :
    (first = doubled + 1 ∧ second = doubled + 2) ∨
      (first = doubled + 2 ∧ second = doubled + 1) := by
  revert doubled first second
  decide

/-- Identity `(boxplus)` read off any labelling of the two simple directions
and any choice of the doubled survivor.  This is the form the Type I / Type II
dispatcher needs *before* a `SimpleBase` exists. -/
theorem sum_index_of_labels (source : ThreeBranchAnchor data star anchor)
    (first second : Fin 3) (hFirst : first ≠ Prescribed.doubled source)
    (hSecond : second ≠ Prescribed.doubled source) (hDistinct : second ≠ first)
    (choice : Bool) :
    directionIndex data star anchor first + directionIndex data star anchor second +
        data.sourceEdgeIndex (doubledSurvivor source choice).1 +
        data.sourceEdgeIndex (doubledSurvivor source (!choice)).1 =
      2 * (data.vertexPartition wall).blockCard anchor.1 + 1 := by
  have hTotal :
      directionIndex data star anchor (Prescribed.doubled source) +
          directionIndex data star anchor (Prescribed.firstSimple source) +
          directionIndex data star anchor (Prescribed.secondSimple source) =
        2 * (data.vertexPartition wall).blockCard anchor.1 + 1 :=
    Prescribed.sum_directionSurvivors_index source
  have hDoubled := directionIndex_doubled source choice
  have hSimple :
      directionIndex data star anchor (Prescribed.firstSimple source) +
          directionIndex data star anchor (Prescribed.secondSimple source) =
        directionIndex data star anchor first +
          directionIndex data star anchor second := by
    rcases fin_three_pair (Prescribed.doubled source) first second hFirst hSecond
        hDistinct with ⟨hOne, hTwo⟩ | ⟨hOne, hTwo⟩
    · simp only [Prescribed.firstSimple, Prescribed.secondSimple, ← hOne, ← hTwo]
    · simp only [Prescribed.firstSimple, Prescribed.secondSimple, ← hOne, ← hTwo]
      exact Nat.add_comm _ _
  omega

/-- The two doubled classes are disjoint subsets of `A`, in the form the
dispatcher needs. -/
theorem doubled_index_le (source : ThreeBranchAnchor data star anchor)
    (choice : Bool) :
    data.sourceEdgeIndex (doubledSurvivor source choice).1 +
        data.sourceEdgeIndex (doubledSurvivor source (!choice)).1 ≤
      (data.vertexPartition wall).blockCard anchor.1 := by
  have hLe : directionIndex data star anchor (Prescribed.doubled source) ≤
      (data.vertexPartition wall).blockCard anchor.1 :=
    Prescribed.selectedSheets_card_le_blockCard source
  have hDoubled := directionIndex_doubled source choice
  omega

/-- **The prescribed Type I / Type II choice** at a three-valent wall: a
simple direction `alpha` carrying the divalent subdivision point `u`, the
other simple direction `beta`, and one of the two doubled survivors, `delta`.
`realizable` is the source's vertex inequality `|A| >= k_beta + k_delta`; the
three target hypotheses are the ones the two branch gauges consume. -/
structure SimpleBase (data : GluingDatum target degree)
    (star : ThreeStar target wall) (anchor : WallBlock data wall) where
  /-- The valency-three anchor classifier. -/
  source : ThreeBranchAnchor data star anchor
  /-- Dangling occurrences are never glued. -/
  noGlue : DanglingEdgeNoGlue data
  /-- The target is connected; used only to separate the two gauged branches. -/
  connected : graph_connected target
  /-- The target is a tree; used only to separate the two gauged branches. -/
  genusZero : genus target = 0
  /-- The simple direction incident to the new divalent point `u`. -/
  alphaLabel : Fin 3
  /-- The other simple direction. -/
  betaLabel : Fin 3
  alpha_ne : alphaLabel ≠ Prescribed.doubled source
  beta_ne : betaLabel ≠ Prescribed.doubled source
  beta_ne_alpha : betaLabel ≠ alphaLabel
  /-- Which of the two doubled survivors plays the paper's `e_delta`. -/
  swapDoubled : Bool
  /-- The source's realizability inequality `|A| >= k_beta + k_delta`. -/
  realizable :
    directionIndex data star anchor betaLabel +
        data.sourceEdgeIndex (doubledSurvivor source swapDoubled).1 ≤
      (data.vertexPartition wall).blockCard anchor.1

namespace SimpleBase

variable (base : SimpleBase data star anchor)

/-- The surviving occurrence `e_alpha` above `t_alpha`. -/
noncomputable def alphaSurvivor :
    IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor) :=
  simpleSurvivor base.source base.alphaLabel base.alpha_ne

/-- The surviving occurrence `e_beta` above `t_beta`. -/
noncomputable def betaSurvivor :
    IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor) :=
  simpleSurvivor base.source base.betaLabel base.beta_ne

/-- The doubled survivor `e_delta`, which becomes the divalent vertex `A'`. -/
noncomputable def deltaSurvivor :
    IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor) :=
  doubledSurvivor base.source base.swapDoubled

/-- The other doubled survivor `e_gamma`, which stays at `A_v`. -/
noncomputable def gammaSurvivor :
    IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor) :=
  doubledSurvivor base.source (!base.swapDoubled)

/-- The anchor block `A` itself. -/
noncomputable def wholeBlock (_base : SimpleBase data star anchor) :
    Finset (Fin degree) :=
  (data.vertexPartition wall).block anchor.1

/-- `|A|`. -/
noncomputable def wallCard (_base : SimpleBase data star anchor) : ℕ :=
  (data.vertexPartition wall).blockCard anchor.1

theorem wholeBlock_card : base.wholeBlock.card = base.wallCard := rfl

/-- The class of `e_alpha`; it will be the divalent endpoint `A_u`. -/
noncomputable def alphaBlock : Finset (Fin degree) :=
  occurrenceBlock data base.alphaSurvivor

/-- The class of `e_beta`. -/
noncomputable def betaBlock : Finset (Fin degree) :=
  occurrenceBlock data base.betaSurvivor

/-- The class of `e_delta`. -/
noncomputable def deltaBlock : Finset (Fin degree) :=
  occurrenceBlock data base.deltaSurvivor

/-- The class of `e_gamma`. -/
noncomputable def gammaBlock : Finset (Fin degree) :=
  occurrenceBlock data base.gammaSurvivor

/-- `k_alpha`. -/
noncomputable def kAlpha : ℕ := data.sourceEdgeIndex base.alphaSurvivor.1

/-- `k_beta`. -/
noncomputable def kBeta : ℕ := data.sourceEdgeIndex base.betaSurvivor.1

/-- `k_delta`. -/
noncomputable def kDelta : ℕ := data.sourceEdgeIndex base.deltaSurvivor.1

/-- `k_gamma`. -/
noncomputable def kGamma : ℕ := data.sourceEdgeIndex base.gammaSurvivor.1

theorem alphaBlock_card : base.alphaBlock.card = base.kAlpha := rfl

theorem betaBlock_card : base.betaBlock.card = base.kBeta := rfl

theorem deltaBlock_card : base.deltaBlock.card = base.kDelta := rfl

theorem gammaBlock_card : base.gammaBlock.card = base.kGamma := rfl

theorem alphaSurvivor_mem :
    base.alphaSurvivor ∈ directionSurvivors data star anchor base.alphaLabel :=
  simpleSurvivor_mem base.source base.alphaLabel base.alpha_ne

theorem betaSurvivor_mem :
    base.betaSurvivor ∈ directionSurvivors data star anchor base.betaLabel :=
  simpleSurvivor_mem base.source base.betaLabel base.beta_ne

theorem deltaSurvivor_mem :
    base.deltaSurvivor ∈
      directionSurvivors data star anchor (Prescribed.doubled base.source) :=
  doubledSurvivor_mem base.source base.swapDoubled

theorem gammaSurvivor_mem :
    base.gammaSurvivor ∈
      directionSurvivors data star anchor (Prescribed.doubled base.source) :=
  doubledSurvivor_mem base.source (!base.swapDoubled)

theorem alphaBlock_subset : base.alphaBlock ⊆ base.wholeBlock :=
  occurrenceBlock_subset_wall base.alphaSurvivor_mem

theorem betaBlock_subset : base.betaBlock ⊆ base.wholeBlock :=
  occurrenceBlock_subset_wall base.betaSurvivor_mem

theorem deltaBlock_subset : base.deltaBlock ⊆ base.wholeBlock :=
  occurrenceBlock_subset_wall base.deltaSurvivor_mem

theorem gammaBlock_subset : base.gammaBlock ⊆ base.wholeBlock :=
  occurrenceBlock_subset_wall base.gammaSurvivor_mem

theorem deltaBlock_inter_gammaBlock : base.deltaBlock ∩ base.gammaBlock = ∅ :=
  doubledSurvivor_block_disjoint base.source base.swapDoubled

theorem simple_index_sum :
    directionIndex data star anchor (Prescribed.firstSimple base.source) +
        directionIndex data star anchor (Prescribed.secondSimple base.source) =
      base.kAlpha + base.kBeta := by
  have hAlpha := directionIndex_simple base.source base.alphaLabel base.alpha_ne
  have hBeta := directionIndex_simple base.source base.betaLabel base.beta_ne
  rcases fin_three_pair (Prescribed.doubled base.source) base.alphaLabel
      base.betaLabel base.alpha_ne base.beta_ne base.beta_ne_alpha with
    ⟨hFirst, hSecond⟩ | ⟨hFirst, hSecond⟩
  · simp only [Prescribed.firstSimple, Prescribed.secondSimple, ← hFirst, ← hSecond]
    rw [hAlpha, hBeta]
    rfl
  · simp only [Prescribed.firstSimple, Prescribed.secondSimple, ← hFirst, ← hSecond]
    rw [hAlpha, hBeta]
    exact Nat.add_comm _ _

/-- Identity `(boxplus)` of the source, in the Type I / Type II labelling. -/
theorem boxplus :
    base.kAlpha + base.kBeta + base.kDelta + base.kGamma = 2 * base.wallCard + 1 := by
  have hIdentity := sum_index_of_labels base.source base.alphaLabel base.betaLabel
    base.alpha_ne base.beta_ne base.beta_ne_alpha base.swapDoubled
  rw [directionIndex_simple base.source base.alphaLabel base.alpha_ne,
    directionIndex_simple base.source base.betaLabel base.beta_ne] at hIdentity
  exact hIdentity

/-- The two doubled classes are disjoint subsets of `A`. -/
theorem doubled_le : base.kDelta + base.kGamma ≤ base.wallCard :=
  doubled_index_le base.source base.swapDoubled

/-- The realizability inequality in the named indices. -/
theorem beta_delta_le : base.kBeta + base.kDelta ≤ base.wallCard := by
  have hBeta := directionIndex_simple base.source base.betaLabel base.beta_ne
  have hField := base.realizable
  have hDelta : data.sourceEdgeIndex (doubledSurvivor base.source base.swapDoubled).1 =
      base.kDelta := rfl
  rw [hBeta, hDelta] at hField
  exact hField

/-- The paper's consequence `k_alpha > k_delta`: the bridge `e_1` is a genuine
occurrence.  This is what makes the first gauge possible. -/
theorem delta_lt_alpha : base.kDelta < base.kAlpha := by
  have hBox := base.boxplus
  have hDoubled := base.doubled_le
  have hBeta := base.beta_delta_le
  omega


/-! ### The two branch gauges

`A'` must be a subset of `A_u` and must miss the `beta` class.  The first is
arranged by a permutation carried on the doubled branch, the second by a
permutation carried on the `t_beta` branch; the two branches of a connected
genus-zero target are separated, so neither swap disturbs what the other
arranged. -/

theorem exists_deltaPerm :
    ∃ permutation : Equiv.Perm (Fin degree),
      (∀ sheet ∈ base.wholeBlock, permutation sheet ∈ base.wholeBlock) ∧
        (∀ sheet, sheet ∉ base.wholeBlock → permutation sheet = sheet) ∧
        base.deltaBlock.image permutation ⊆ base.alphaBlock :=
  exists_perm_image_subset base.wholeBlock base.alphaBlock base.deltaBlock
    base.alphaBlock_subset base.deltaBlock_subset
    (by rw [base.deltaBlock_card, base.alphaBlock_card]; exact base.delta_lt_alpha.le)

/-- The gauge carrying the class of `e_delta` inside the class of
`e_alpha`. -/
noncomputable def deltaPerm : Equiv.Perm (Fin degree) :=
  Classical.choose base.exists_deltaPerm

theorem deltaPerm_inside :
    ∀ sheet ∈ base.wholeBlock, base.deltaPerm sheet ∈ base.wholeBlock :=
  (Classical.choose_spec base.exists_deltaPerm).1

theorem deltaPerm_outside :
    ∀ sheet, sheet ∉ base.wholeBlock → base.deltaPerm sheet = sheet :=
  (Classical.choose_spec base.exists_deltaPerm).2.1

/-- The literal `A'`: the gauged class of `e_delta`. -/
noncomputable def newDeltaBlock : Finset (Fin degree) :=
  base.deltaBlock.image base.deltaPerm

theorem newDeltaBlock_subset_alpha : base.newDeltaBlock ⊆ base.alphaBlock :=
  (Classical.choose_spec base.exists_deltaPerm).2.2

theorem newDeltaBlock_subset_whole : base.newDeltaBlock ⊆ base.wholeBlock :=
  base.newDeltaBlock_subset_alpha.trans base.alphaBlock_subset

theorem newDeltaBlock_card : base.newDeltaBlock.card = base.kDelta := by
  rw [newDeltaBlock, Finset.card_image_of_injective _ base.deltaPerm.injective,
    base.deltaBlock_card]

theorem exists_betaPerm :
    ∃ permutation : Equiv.Perm (Fin degree),
      (∀ sheet ∈ base.wholeBlock, permutation sheet ∈ base.wholeBlock) ∧
        (∀ sheet, sheet ∉ base.wholeBlock → permutation sheet = sheet) ∧
        base.betaBlock.image permutation ⊆ base.wholeBlock \ base.newDeltaBlock := by
  refine exists_perm_image_subset base.wholeBlock
    (base.wholeBlock \ base.newDeltaBlock) base.betaBlock Finset.sdiff_subset
    base.betaBlock_subset ?_
  rw [Finset.card_sdiff_of_subset base.newDeltaBlock_subset_whole, base.betaBlock_card,
    base.newDeltaBlock_card, base.wholeBlock_card]
  have hBeta := base.beta_delta_le
  omega

/-- The gauge carrying the class of `e_beta` off `A'`. -/
noncomputable def betaPerm : Equiv.Perm (Fin degree) :=
  Classical.choose base.exists_betaPerm

theorem betaPerm_inside :
    ∀ sheet ∈ base.wholeBlock, base.betaPerm sheet ∈ base.wholeBlock :=
  (Classical.choose_spec base.exists_betaPerm).1

theorem betaPerm_outside :
    ∀ sheet, sheet ∉ base.wholeBlock → base.betaPerm sheet = sheet :=
  (Classical.choose_spec base.exists_betaPerm).2.1

/-- The gauged class of `e_beta`. -/
noncomputable def newBetaBlock : Finset (Fin degree) :=
  base.betaBlock.image base.betaPerm

theorem newBetaBlock_subset_sdiff :
    base.newBetaBlock ⊆ base.wholeBlock \ base.newDeltaBlock :=
  (Classical.choose_spec base.exists_betaPerm).2.2

theorem newBetaBlock_card : base.newBetaBlock.card = base.kBeta := by
  rw [newBetaBlock, Finset.card_image_of_injective _ base.betaPerm.injective,
    base.betaBlock_card]

/-! ### The gauged incoming datum -/

theorem doubledEdge_incident :
    ((Prescribed.doubledEdge base.source : target.V × target.V).1 = wall ∨
      (Prescribed.doubledEdge base.source : target.V × target.V).2 = wall) :=
  (GluingContraction.mem_incidentEdges_iff wall _).mp
    (Prescribed.doubledEdge_mem_incidentEdges base.source)

theorem directionEdge_incident (label : Fin 3) :
    ((directionEdge star label : target.V × target.V).1 = wall ∨
      (directionEdge star label : target.V × target.V).2 = wall) :=
  (GluingContraction.mem_incidentEdges_iff wall _).mp
    (directionEdge_mem_incidentEdges star label)

theorem doubledEdge_ne_direction (label : Fin 3)
    (hLabel : label ≠ Prescribed.doubled base.source) :
    Prescribed.doubledEdge base.source ≠ directionEdge star label := by
  intro hEq
  simp only [Prescribed.doubledEdge] at hEq
  exact hLabel (directionEdge_injective star hEq).symm

/-- The first branch swap, carried across the doubled direction. -/
noncomputable def firstRelabeling : data.SheetRelabeling :=
  branchSwapOfPerm data wall
    (TargetSeparation.farEndpoint wall (Prescribed.doubledEdge base.source))
    (TargetSeparation.farEndpoint_ne base.doubledEdge_incident)
    base.deltaPerm
    (rel_of_stabilizes_block (data.vertexPartition wall) anchor.1 base.deltaPerm
      base.deltaPerm_inside base.deltaPerm_outside)

/-- The incoming datum after the first gauge. -/
noncomputable def middleData : GluingDatum target degree :=
  base.firstRelabeling.apply

theorem middleData_vertexPartition_wall :
    base.middleData.vertexPartition wall = data.vertexPartition wall := by
  unfold middleData firstRelabeling
  apply branchSwapOfPerm_vertexPartition_wall

theorem middleData_edgePartition_doubled :
    base.middleData.edgePartition (Prescribed.doubledEdge base.source) =
      (data.edgePartition (Prescribed.doubledEdge base.source)).relabel
        base.deltaPerm := by
  unfold middleData firstRelabeling
  apply branchSwapOfPerm_edgePartition_of_moved
  exact TargetSeparation.edgeMoved_self_eq_true base.doubledEdge_incident

theorem middleData_edgePartition_simple (label : Fin 3)
    (hLabel : label ≠ Prescribed.doubled base.source) :
    base.middleData.edgePartition (directionEdge star label) =
      data.edgePartition (directionEdge star label) := by
  unfold middleData firstRelabeling
  apply branchSwapOfPerm_edgePartition_of_fixed
  exact TargetSeparation.edgeMoved_eq_false base.connected base.genusZero
    base.doubledEdge_incident (directionEdge_incident (star := star) label)
    (base.doubledEdge_ne_direction label hLabel)

theorem middleData_valid (hValid : data.Valid) : base.middleData.Valid :=
  base.firstRelabeling.valid hValid

/-- The second branch swap, carried across `t_beta`. -/
noncomputable def secondRelabeling : base.middleData.SheetRelabeling :=
  branchSwapOfPerm base.middleData wall
    (TargetSeparation.farEndpoint wall (directionEdge star base.betaLabel))
    (TargetSeparation.farEndpoint_ne (directionEdge_incident (star := star) base.betaLabel))
    base.betaPerm
    (by
      rw [base.middleData_vertexPartition_wall]
      exact rel_of_stabilizes_block (data.vertexPartition wall) anchor.1
        base.betaPerm base.betaPerm_inside base.betaPerm_outside)

/-- **The gauged incoming datum.**  It is isomorphic to `data`: only the
sheet labelling behind two of the three star directions has changed. -/
noncomputable def gaugedData : GluingDatum target degree :=
  base.secondRelabeling.apply

theorem gaugedData_vertexPartition_wall :
    base.gaugedData.vertexPartition wall = data.vertexPartition wall := by
  have hSecond : base.gaugedData.vertexPartition wall =
      base.middleData.vertexPartition wall := by
    unfold gaugedData secondRelabeling
    apply branchSwapOfPerm_vertexPartition_wall
  rw [hSecond, base.middleData_vertexPartition_wall]

theorem gaugedData_edgePartition_beta :
    base.gaugedData.edgePartition (directionEdge star base.betaLabel) =
      (data.edgePartition (directionEdge star base.betaLabel)).relabel
        base.betaPerm := by
  have hSecond : base.gaugedData.edgePartition (directionEdge star base.betaLabel) =
      (base.middleData.edgePartition
        (directionEdge star base.betaLabel)).relabel base.betaPerm := by
    unfold gaugedData secondRelabeling
    apply branchSwapOfPerm_edgePartition_of_moved
    exact TargetSeparation.edgeMoved_self_eq_true
      (directionEdge_incident (star := star) base.betaLabel)
  rw [hSecond, base.middleData_edgePartition_simple base.betaLabel base.beta_ne]

theorem gaugedData_edgePartition_alpha :
    base.gaugedData.edgePartition (directionEdge star base.alphaLabel) =
      data.edgePartition (directionEdge star base.alphaLabel) := by
  have hSecond : base.gaugedData.edgePartition (directionEdge star base.alphaLabel) =
      base.middleData.edgePartition (directionEdge star base.alphaLabel) := by
    unfold gaugedData secondRelabeling
    apply branchSwapOfPerm_edgePartition_of_fixed
    refine TargetSeparation.edgeMoved_eq_false base.connected base.genusZero
      (directionEdge_incident (star := star) base.betaLabel)
      (directionEdge_incident (star := star) base.alphaLabel) ?_
    intro hEq
    exact base.beta_ne_alpha (directionEdge_injective star hEq)
  rw [hSecond, base.middleData_edgePartition_simple base.alphaLabel base.alpha_ne]

theorem gaugedData_edgePartition_doubled :
    base.gaugedData.edgePartition (Prescribed.doubledEdge base.source) =
      (data.edgePartition (Prescribed.doubledEdge base.source)).relabel
        base.deltaPerm := by
  have hSecond : base.gaugedData.edgePartition (Prescribed.doubledEdge base.source) =
      base.middleData.edgePartition (Prescribed.doubledEdge base.source) := by
    unfold gaugedData secondRelabeling
    apply branchSwapOfPerm_edgePartition_of_fixed
    refine TargetSeparation.edgeMoved_eq_false base.connected base.genusZero
      (directionEdge_incident (star := star) base.betaLabel) base.doubledEdge_incident ?_
    intro hEq
    exact base.doubledEdge_ne_direction base.betaLabel base.beta_ne hEq.symm
  rw [hSecond, base.middleData_edgePartition_doubled]

theorem gaugedData_valid (hValid : data.Valid) : base.gaugedData.Valid :=
  base.secondRelabeling.valid (base.middleData_valid hValid)


/-! ### The three new vertices

`A_u` is the class of `e_alpha`, `A'` is the gauged class of `e_delta` inside
it, and `A_v` is the rest of the anchor block.  `hubSheet` is a sheet of the
bridge `e_1 = A_u \ A'`; it names both `e_1` and `A_v`, and it is also the hub
through which the contraction of the new edge is proved. -/

theorem alphaBlock_sdiff_nonempty : (base.alphaBlock \ base.newDeltaBlock).Nonempty := by
  rw [← Finset.card_pos, Finset.card_sdiff_of_subset base.newDeltaBlock_subset_alpha,
    base.alphaBlock_card, base.newDeltaBlock_card]
  have hLt := base.delta_lt_alpha
  omega

/-- A sheet of the bridge `e_1`. -/
noncomputable def hubSheet : Fin degree := base.alphaBlock_sdiff_nonempty.choose

theorem hubSheet_mem_sdiff :
    base.hubSheet ∈ base.alphaBlock \ base.newDeltaBlock :=
  base.alphaBlock_sdiff_nonempty.choose_spec

theorem hubSheet_mem_alpha : base.hubSheet ∈ base.alphaBlock :=
  (Finset.mem_sdiff.mp base.hubSheet_mem_sdiff).1

theorem hubSheet_not_mem_newDelta : base.hubSheet ∉ base.newDeltaBlock :=
  (Finset.mem_sdiff.mp base.hubSheet_mem_sdiff).2

theorem hubSheet_wall : (data.vertexPartition wall).Rel anchor.1 base.hubSheet :=
  ((data.vertexPartition wall).mem_block_iff _ _).mp
    (base.alphaBlock_subset base.hubSheet_mem_alpha)

/-- The sheet naming `A'`. -/
noncomputable def deltaRepr : Fin degree :=
  base.deltaPerm (Prescribed.occurrenceSheet base.deltaSurvivor)

theorem deltaRepr_mem : base.deltaRepr ∈ base.newDeltaBlock :=
  Finset.mem_image.mpr
    ⟨Prescribed.occurrenceSheet base.deltaSurvivor,
      occurrenceSheet_mem_occurrenceBlock base.deltaSurvivor, rfl⟩

theorem deltaRepr_mem_alpha : base.deltaRepr ∈ base.alphaBlock :=
  base.newDeltaBlock_subset_alpha base.deltaRepr_mem

theorem deltaRepr_wall : (data.vertexPartition wall).Rel anchor.1 base.deltaRepr :=
  ((data.vertexPartition wall).mem_block_iff _ _).mp
    (base.alphaBlock_subset base.deltaRepr_mem_alpha)

theorem hubSheet_ne_deltaRepr : base.hubSheet ≠ base.deltaRepr := by
  intro hEq
  exact base.hubSheet_not_mem_newDelta (hEq ▸ base.deltaRepr_mem)

/-! ### The three endpoint partitions -/

/-- Representative choice over the divalent point `u`: the whole class of
`e_alpha` becomes one vertex `A_u`, every other sheet of `A` a dangling
singleton. -/
noncomputable def leftPick : Fin degree → Fin degree :=
  fun sheet ↦ if sheet ∈ base.alphaBlock then base.hubSheet else sheet

/-- Representative choice on the new edge `t_1`: the bridge `e_1` and the
second occurrence `e' = A'`. -/
noncomputable def newEdgePick : Fin degree → Fin degree :=
  fun sheet ↦ if sheet ∈ base.newDeltaBlock then base.deltaRepr
    else if sheet ∈ base.alphaBlock then base.hubSheet else sheet

/-- Representative choice over the trivalent point `v`: the divalent vertex
`A'` and the rest of the anchor block, `A_v`. -/
noncomputable def rightPick : Fin degree → Fin degree :=
  fun sheet ↦ if sheet ∈ base.newDeltaBlock then base.deltaRepr else base.hubSheet

theorem leftPick_of_mem {sheet : Fin degree} (hSheet : sheet ∈ base.alphaBlock) :
    base.leftPick sheet = base.hubSheet := by
  rw [leftPick, if_pos hSheet]

theorem leftPick_of_not_mem {sheet : Fin degree} (hSheet : sheet ∉ base.alphaBlock) :
    base.leftPick sheet = sheet := by
  rw [leftPick, if_neg hSheet]

theorem newEdgePick_of_mem {sheet : Fin degree} (hSheet : sheet ∈ base.newDeltaBlock) :
    base.newEdgePick sheet = base.deltaRepr := by
  rw [newEdgePick, if_pos hSheet]

theorem newEdgePick_of_bridge {sheet : Fin degree}
    (hDelta : sheet ∉ base.newDeltaBlock) (hAlpha : sheet ∈ base.alphaBlock) :
    base.newEdgePick sheet = base.hubSheet := by
  rw [newEdgePick, if_neg hDelta, if_pos hAlpha]

theorem newEdgePick_of_outside {sheet : Fin degree} (hAlpha : sheet ∉ base.alphaBlock) :
    base.newEdgePick sheet = sheet := by
  have hDelta : sheet ∉ base.newDeltaBlock := fun hMem ↦
    hAlpha (base.newDeltaBlock_subset_alpha hMem)
  rw [newEdgePick, if_neg hDelta, if_neg hAlpha]

theorem rightPick_of_mem {sheet : Fin degree} (hSheet : sheet ∈ base.newDeltaBlock) :
    base.rightPick sheet = base.deltaRepr := by
  rw [rightPick, if_pos hSheet]

theorem rightPick_of_not_mem {sheet : Fin degree} (hSheet : sheet ∉ base.newDeltaBlock) :
    base.rightPick sheet = base.hubSheet := by
  rw [rightPick, if_neg hSheet]

theorem leftPick_wall (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel anchor.1 sheet) :
    (data.vertexPartition wall).Rel anchor.1 (base.leftPick sheet) := by
  by_cases hAlpha : sheet ∈ base.alphaBlock
  · rw [base.leftPick_of_mem hAlpha]
    exact base.hubSheet_wall
  · rw [base.leftPick_of_not_mem hAlpha]
    exact hSheet

theorem leftPick_idem (sheet : Fin degree)
    (_hSheet : (data.vertexPartition wall).Rel anchor.1 sheet) :
    base.leftPick (base.leftPick sheet) = base.leftPick sheet := by
  by_cases hAlpha : sheet ∈ base.alphaBlock
  · rw [base.leftPick_of_mem hAlpha, base.leftPick_of_mem base.hubSheet_mem_alpha]
  · rw [base.leftPick_of_not_mem hAlpha, base.leftPick_of_not_mem hAlpha]

theorem newEdgePick_wall (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel anchor.1 sheet) :
    (data.vertexPartition wall).Rel anchor.1 (base.newEdgePick sheet) := by
  by_cases hDelta : sheet ∈ base.newDeltaBlock
  · rw [base.newEdgePick_of_mem hDelta]
    exact base.deltaRepr_wall
  · by_cases hAlpha : sheet ∈ base.alphaBlock
    · rw [base.newEdgePick_of_bridge hDelta hAlpha]
      exact base.hubSheet_wall
    · rw [base.newEdgePick_of_outside hAlpha]
      exact hSheet

theorem newEdgePick_idem (sheet : Fin degree)
    (_hSheet : (data.vertexPartition wall).Rel anchor.1 sheet) :
    base.newEdgePick (base.newEdgePick sheet) = base.newEdgePick sheet := by
  by_cases hDelta : sheet ∈ base.newDeltaBlock
  · rw [base.newEdgePick_of_mem hDelta,
      base.newEdgePick_of_mem base.deltaRepr_mem]
  · by_cases hAlpha : sheet ∈ base.alphaBlock
    · rw [base.newEdgePick_of_bridge hDelta hAlpha,
        base.newEdgePick_of_bridge base.hubSheet_not_mem_newDelta
          base.hubSheet_mem_alpha]
    · rw [base.newEdgePick_of_outside hAlpha, base.newEdgePick_of_outside hAlpha]

theorem rightPick_wall (sheet : Fin degree)
    (_hSheet : (data.vertexPartition wall).Rel anchor.1 sheet) :
    (data.vertexPartition wall).Rel anchor.1 (base.rightPick sheet) := by
  by_cases hDelta : sheet ∈ base.newDeltaBlock
  · rw [base.rightPick_of_mem hDelta]
    exact base.deltaRepr_wall
  · rw [base.rightPick_of_not_mem hDelta]
    exact base.hubSheet_wall

theorem rightPick_idem (sheet : Fin degree)
    (_hSheet : (data.vertexPartition wall).Rel anchor.1 sheet) :
    base.rightPick (base.rightPick sheet) = base.rightPick sheet := by
  by_cases hDelta : sheet ∈ base.newDeltaBlock
  · rw [base.rightPick_of_mem hDelta, base.rightPick_of_mem base.deltaRepr_mem]
  · rw [base.rightPick_of_not_mem hDelta,
      base.rightPick_of_not_mem base.hubSheet_not_mem_newDelta]

/-- The endpoint partition over the divalent subdivision point `u`. -/
noncomputable def leftPartition : SheetPartition degree :=
  blockRefine (data.vertexPartition wall) anchor.1 base.leftPick base.leftPick_wall
    base.leftPick_idem

/-- The occurrence partition of the new edge `t_1`. -/
noncomputable def newEdgePartition : SheetPartition degree :=
  blockRefine (data.vertexPartition wall) anchor.1 base.newEdgePick
    base.newEdgePick_wall base.newEdgePick_idem

/-- The endpoint partition over the trivalent point `v`. -/
noncomputable def rightPartition : SheetPartition degree :=
  blockRefine (data.vertexPartition wall) anchor.1 base.rightPick
    base.rightPick_wall base.rightPick_idem

theorem leftPartition_refines :
    base.leftPartition.Refines (data.vertexPartition wall) :=
  blockRefine.refines _ _ _ _ _

theorem newEdgePartition_refines :
    base.newEdgePartition.Refines (data.vertexPartition wall) :=
  blockRefine.refines _ _ _ _ _

theorem rightPartition_refines :
    base.rightPartition.Refines (data.vertexPartition wall) :=
  blockRefine.refines _ _ _ _ _

/-! ### The literal blocks of the three partitions -/

/-- `A_u` is exactly the class of `e_alpha`, so `|A_u| = k_alpha`. -/
theorem leftPartition_block_hub :
    base.leftPartition.block base.hubSheet = base.alphaBlock := by
  refine blockRefine.block_eq_of_iff _ _ _ _ _ base.hubSheet_wall _
    base.alphaBlock_subset ?_
  intro other _
  rw [base.leftPick_of_mem base.hubSheet_mem_alpha]
  by_cases hAlpha : other ∈ base.alphaBlock
  · rw [base.leftPick_of_mem hAlpha]
    simp [hAlpha]
  · rw [base.leftPick_of_not_mem hAlpha]
    constructor
    · intro hEq
      exact absurd (hEq ▸ base.hubSheet_mem_alpha) hAlpha
    · intro hMem
      exact absurd hMem hAlpha

theorem leftPartition_block_singleton {sheet : Fin degree}
    (hWall : (data.vertexPartition wall).Rel anchor.1 sheet)
    (hAlpha : sheet ∉ base.alphaBlock) :
    base.leftPartition.block sheet = {sheet} := by
  refine blockRefine.block_eq_of_iff _ _ _ _ _ hWall _ ?_ ?_
  · intro other hOther
    rw [Finset.mem_singleton] at hOther
    subst hOther
    exact ((data.vertexPartition wall).mem_block_iff _ _).mpr hWall
  · intro other _
    rw [base.leftPick_of_not_mem hAlpha, Finset.mem_singleton]
    by_cases hOther : other ∈ base.alphaBlock
    · rw [base.leftPick_of_mem hOther]
      constructor
      · intro hEq
        exact absurd (hEq ▸ base.hubSheet_mem_alpha) hAlpha
      · intro hEq
        exact absurd (hEq ▸ hOther) hAlpha
    · rw [base.leftPick_of_not_mem hOther]

/-- `A'` is exactly the gauged class of `e_delta`, so `|A'| = k_delta`. -/
theorem newEdgePartition_block_delta :
    base.newEdgePartition.block base.deltaRepr = base.newDeltaBlock := by
  refine blockRefine.block_eq_of_iff _ _ _ _ _ base.deltaRepr_wall _
    base.newDeltaBlock_subset_whole ?_
  intro other _
  rw [base.newEdgePick_of_mem base.deltaRepr_mem]
  by_cases hDelta : other ∈ base.newDeltaBlock
  · rw [base.newEdgePick_of_mem hDelta]
    simp [hDelta]
  · constructor
    · intro hEq
      by_cases hAlpha : other ∈ base.alphaBlock
      · rw [base.newEdgePick_of_bridge hDelta hAlpha] at hEq
        exact absurd hEq base.hubSheet_ne_deltaRepr
      · rw [base.newEdgePick_of_outside hAlpha] at hEq
        exact absurd (hEq ▸ base.deltaRepr_mem) hDelta
    · intro hMem
      exact absurd hMem hDelta

/-- The bridge `e_1 = A_u \ A'` has index `k_alpha - k_delta`. -/
theorem newEdgePartition_block_hub :
    base.newEdgePartition.block base.hubSheet =
      base.alphaBlock \ base.newDeltaBlock := by
  refine blockRefine.block_eq_of_iff _ _ _ _ _ base.hubSheet_wall _
    (Finset.sdiff_subset.trans base.alphaBlock_subset) ?_
  intro other _
  rw [base.newEdgePick_of_bridge base.hubSheet_not_mem_newDelta
    base.hubSheet_mem_alpha, Finset.mem_sdiff]
  by_cases hDelta : other ∈ base.newDeltaBlock
  · rw [base.newEdgePick_of_mem hDelta]
    constructor
    · intro hEq
      exact absurd hEq.symm base.hubSheet_ne_deltaRepr
    · rintro ⟨_, hNot⟩
      exact absurd hDelta hNot
  · by_cases hAlpha : other ∈ base.alphaBlock
    · rw [base.newEdgePick_of_bridge hDelta hAlpha]
      simp [hAlpha, hDelta]
    · rw [base.newEdgePick_of_outside hAlpha]
      constructor
      · intro hEq
        exact absurd (hEq ▸ base.hubSheet_mem_alpha) hAlpha
      · rintro ⟨hMem, _⟩
        exact absurd hMem hAlpha

theorem newEdgePartition_block_singleton {sheet : Fin degree}
    (hWall : (data.vertexPartition wall).Rel anchor.1 sheet)
    (hAlpha : sheet ∉ base.alphaBlock) :
    base.newEdgePartition.block sheet = {sheet} := by
  refine blockRefine.block_eq_of_iff _ _ _ _ _ hWall _ ?_ ?_
  · intro other hOther
    rw [Finset.mem_singleton] at hOther
    subst hOther
    exact ((data.vertexPartition wall).mem_block_iff _ _).mpr hWall
  · intro other _
    rw [base.newEdgePick_of_outside hAlpha, Finset.mem_singleton]
    by_cases hDelta : other ∈ base.newDeltaBlock
    · rw [base.newEdgePick_of_mem hDelta]
      constructor
      · intro hEq
        exact absurd (hEq ▸ base.deltaRepr_mem_alpha) hAlpha
      · intro hEq
        exact absurd (hEq ▸ base.newDeltaBlock_subset_alpha hDelta) hAlpha
    · by_cases hOther : other ∈ base.alphaBlock
      · rw [base.newEdgePick_of_bridge hDelta hOther]
        constructor
        · intro hEq
          exact absurd (hEq ▸ base.hubSheet_mem_alpha) hAlpha
        · intro hEq
          exact absurd (hEq ▸ hOther) hAlpha
      · rw [base.newEdgePick_of_outside hOther]

/-- The divalent vertex `A'` over `v`. -/
theorem rightPartition_block_delta :
    base.rightPartition.block base.deltaRepr = base.newDeltaBlock := by
  refine blockRefine.block_eq_of_iff _ _ _ _ _ base.deltaRepr_wall _
    base.newDeltaBlock_subset_whole ?_
  intro other _
  rw [base.rightPick_of_mem base.deltaRepr_mem]
  by_cases hDelta : other ∈ base.newDeltaBlock
  · rw [base.rightPick_of_mem hDelta]
    simp [hDelta]
  · rw [base.rightPick_of_not_mem hDelta]
    constructor
    · intro hEq
      exact absurd hEq base.hubSheet_ne_deltaRepr
    · intro hMem
      exact absurd hMem hDelta

/-- The trivalent vertex `A_v`, of size `|A| - k_delta`. -/
theorem rightPartition_block_hub :
    base.rightPartition.block base.hubSheet =
      base.wholeBlock \ base.newDeltaBlock := by
  refine blockRefine.block_eq_of_iff _ _ _ _ _ base.hubSheet_wall _
    Finset.sdiff_subset ?_
  intro other hOther
  rw [base.rightPick_of_not_mem base.hubSheet_not_mem_newDelta, Finset.mem_sdiff]
  by_cases hDelta : other ∈ base.newDeltaBlock
  · rw [base.rightPick_of_mem hDelta]
    constructor
    · intro hEq
      exact absurd hEq.symm base.hubSheet_ne_deltaRepr
    · rintro ⟨_, hNot⟩
      exact absurd hDelta hNot
  · rw [base.rightPick_of_not_mem hDelta]
    exact ⟨fun _ ↦ ⟨((data.vertexPartition wall).mem_block_iff _ _).mpr hOther,
      hDelta⟩, fun _ ↦ rfl⟩


/-! ### The local resolution at the anchor -/

theorem leftPick_newEdgePick (sheet : Fin degree) :
    base.leftPick (base.newEdgePick sheet) = base.leftPick sheet := by
  by_cases hDelta : sheet ∈ base.newDeltaBlock
  · rw [base.newEdgePick_of_mem hDelta,
      base.leftPick_of_mem base.deltaRepr_mem_alpha,
      base.leftPick_of_mem (base.newDeltaBlock_subset_alpha hDelta)]
  · by_cases hAlpha : sheet ∈ base.alphaBlock
    · rw [base.newEdgePick_of_bridge hDelta hAlpha,
        base.leftPick_of_mem base.hubSheet_mem_alpha,
        base.leftPick_of_mem hAlpha]
    · rw [base.newEdgePick_of_outside hAlpha]

theorem rightPick_newEdgePick (sheet : Fin degree) :
    base.rightPick (base.newEdgePick sheet) = base.rightPick sheet := by
  by_cases hDelta : sheet ∈ base.newDeltaBlock
  · rw [base.newEdgePick_of_mem hDelta, base.rightPick_of_mem base.deltaRepr_mem,
      base.rightPick_of_mem hDelta]
  · by_cases hAlpha : sheet ∈ base.alphaBlock
    · rw [base.newEdgePick_of_bridge hDelta hAlpha,
        base.rightPick_of_not_mem base.hubSheet_not_mem_newDelta,
        base.rightPick_of_not_mem hDelta]
    · rw [base.newEdgePick_of_outside hAlpha]

theorem newEdgePartition_refines_left :
    base.newEdgePartition.Refines base.leftPartition := by
  refine blockRefine.refines_blockRefine _ _ _ _ _ _ _ _ ?_
  intro first second _ _ hEq
  rw [← base.leftPick_newEdgePick first, ← base.leftPick_newEdgePick second, hEq]

theorem newEdgePartition_refines_right :
    base.newEdgePartition.Refines base.rightPartition := by
  refine blockRefine.refines_blockRefine _ _ _ _ _ _ _ _ ?_
  intro first second _ _ hEq
  rw [← base.rightPick_newEdgePick first, ← base.rightPick_newEdgePick second, hEq]

/-- **The prescribed local resolution** of base tree `T_alpha`: the divalent
point `u` carries `A_u`, and the trivalent point `v` carries the two vertices
`A'` and `A_v`. -/
noncomputable def selectedResolution : LocalResolution degree where
  left := base.leftPartition
  right := base.rightPartition
  newEdge := base.newEdgePartition
  edge_refines_left := base.newEdgePartition_refines_left
  edge_refines_right := base.newEdgePartition_refines_right

@[simp] theorem selectedResolution_left :
    base.selectedResolution.left = base.leftPartition := rfl

@[simp] theorem selectedResolution_right :
    base.selectedResolution.right = base.rightPartition := rfl

@[simp] theorem selectedResolution_newEdge :
    base.selectedResolution.newEdge = base.newEdgePartition := rfl

/-- Contracting the new edge `t_1` rejoins `A_u`, `A'` and `A_v` to `A`. -/
theorem selectedResolution_contracts :
    base.selectedResolution.ContractsTo (data.vertexPartition wall) := by
  refine isJoin_of_hub base.leftPartition base.rightPartition
    (data.vertexPartition wall) anchor.1 base.hubSheet base.leftPartition_refines
    base.rightPartition_refines ?_ ?_
  · intro first second hFirst hRel
    have hSecond : ¬(data.vertexPartition wall).Rel anchor.1 second := by
      intro hMem
      exact hFirst (hMem.trans hRel.symm)
    unfold SheetPartition.Rel leftPartition
    rw [blockRefine.repr_of_not_rel _ _ _ _ _ hFirst,
      blockRefine.repr_of_not_rel _ _ _ _ _ hSecond]
    exact hRel
  · intro sheet hSheet
    by_cases hAlpha : sheet ∈ base.alphaBlock
    · left
      refine (blockRefine.rel_iff_of_rel _ _ _ _ _ hSheet base.hubSheet_wall).mpr ?_
      rw [base.leftPick_of_mem hAlpha, base.leftPick_of_mem base.hubSheet_mem_alpha]
    · right
      have hDelta : sheet ∉ base.newDeltaBlock := fun hMem ↦
        hAlpha (base.newDeltaBlock_subset_alpha hMem)
      refine (blockRefine.rel_iff_of_rel _ _ _ _ _ hSheet base.hubSheet_wall).mpr ?_
      rw [base.rightPick_of_not_mem hDelta,
        base.rightPick_of_not_mem base.hubSheet_not_mem_newDelta]

/-! ### The exact sizes `|A_u| = k_alpha`, `|A'| = k_delta`,
`|A_v| = |A| - k_delta` and `k_1 = k_alpha - k_delta` -/

theorem leftPartition_blockCard_hub :
    base.leftPartition.blockCard base.hubSheet = base.kAlpha := by
  rw [SheetPartition.blockCard, base.leftPartition_block_hub, base.alphaBlock_card]

theorem newEdgePartition_blockCard_delta :
    base.newEdgePartition.blockCard base.deltaRepr = base.kDelta := by
  rw [SheetPartition.blockCard, base.newEdgePartition_block_delta,
    base.newDeltaBlock_card]

theorem newEdgePartition_blockCard_hub :
    base.newEdgePartition.blockCard base.hubSheet + base.kDelta = base.kAlpha := by
  rw [SheetPartition.blockCard, base.newEdgePartition_block_hub,
    Finset.card_sdiff_of_subset base.newDeltaBlock_subset_alpha,
    base.alphaBlock_card, base.newDeltaBlock_card]
  have hLt := base.delta_lt_alpha
  omega

theorem rightPartition_blockCard_delta :
    base.rightPartition.blockCard base.deltaRepr = base.kDelta := by
  rw [SheetPartition.blockCard, base.rightPartition_block_delta,
    base.newDeltaBlock_card]

theorem rightPartition_blockCard_hub :
    base.rightPartition.blockCard base.hubSheet + base.kDelta = base.wallCard := by
  rw [SheetPartition.blockCard, base.rightPartition_block_hub,
    Finset.card_sdiff_of_subset base.newDeltaBlock_subset_whole,
    base.wholeBlock_card, base.newDeltaBlock_card]
  have hDoubled := base.doubled_le
  omega


/-! ### The shape of the gauged occurrence partitions inside the anchor block -/

theorem perm_symm_inside (permutation : Equiv.Perm (Fin degree))
    (_hInside : ∀ sheet ∈ base.wholeBlock, permutation sheet ∈ base.wholeBlock)
    (hOutside : ∀ sheet, sheet ∉ base.wholeBlock → permutation sheet = sheet)
    (sheet : Fin degree) (hSheet : sheet ∈ base.wholeBlock) :
    permutation.symm sheet ∈ base.wholeBlock := by
  by_contra hNot
  have hFixed := hOutside (permutation.symm sheet) hNot
  have hEq : sheet = permutation.symm sheet := by
    rw [← hFixed]
    simp
  exact hNot (hEq ▸ hSheet)

theorem deltaBlock_eq :
    base.deltaBlock =
      (data.edgePartition (Prescribed.doubledEdge base.source)).block
        (Prescribed.occurrenceSheet base.deltaSurvivor) :=
  occurrenceBlock_eq_direction base.deltaSurvivor_mem

theorem gammaBlock_eq :
    base.gammaBlock =
      (data.edgePartition (Prescribed.doubledEdge base.source)).block
        (Prescribed.occurrenceSheet base.gammaSurvivor) :=
  occurrenceBlock_eq_direction base.gammaSurvivor_mem

theorem betaBlock_eq :
    base.betaBlock =
      (data.edgePartition (directionEdge star base.betaLabel)).block
        (Prescribed.occurrenceSheet base.betaSurvivor) :=
  occurrenceBlock_eq_direction base.betaSurvivor_mem

theorem alphaBlock_eq :
    base.alphaBlock =
      (data.edgePartition (directionEdge star base.alphaLabel)).block
        (Prescribed.occurrenceSheet base.alphaSurvivor) :=
  occurrenceBlock_eq_direction base.alphaSurvivor_mem

/-- The gauged class of `e_gamma`, which stays inside `A_v`. -/
noncomputable def newGammaBlock : Finset (Fin degree) :=
  base.gammaBlock.image base.deltaPerm

theorem newGammaBlock_inter_newDeltaBlock :
    base.newGammaBlock ∩ base.newDeltaBlock = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem ?_
  intro sheet hSheet
  rw [Finset.mem_inter] at hSheet
  obtain ⟨first, hFirst, hFirstEq⟩ := Finset.mem_image.mp hSheet.1
  obtain ⟨second, hSecond, hSecondEq⟩ := Finset.mem_image.mp hSheet.2
  have hEq : first = second :=
    base.deltaPerm.injective (hFirstEq.trans hSecondEq.symm)
  subst hEq
  have hEmpty := base.deltaBlock_inter_gammaBlock
  have hMem : first ∈ base.deltaBlock ∩ base.gammaBlock :=
    Finset.mem_inter.mpr ⟨hSecond, hFirst⟩
  rw [hEmpty] at hMem
  exact absurd hMem (Finset.notMem_empty first)

theorem gaugedDoubled_block_delta :
    (base.gaugedData.edgePartition (Prescribed.doubledEdge base.source)).block
        base.deltaRepr = base.newDeltaBlock := by
  rw [base.gaugedData_edgePartition_doubled, deltaRepr,
    SheetPartition.relabel_block, ← base.deltaBlock_eq]
  rfl

theorem gaugedDoubled_block_gamma :
    (base.gaugedData.edgePartition (Prescribed.doubledEdge base.source)).block
        (base.deltaPerm (Prescribed.occurrenceSheet base.gammaSurvivor)) =
      base.newGammaBlock := by
  rw [base.gaugedData_edgePartition_doubled, SheetPartition.relabel_block,
    ← base.gammaBlock_eq]
  rfl

theorem gaugedBeta_block_beta :
    (base.gaugedData.edgePartition (directionEdge star base.betaLabel)).block
        (base.betaPerm (Prescribed.occurrenceSheet base.betaSurvivor)) =
      base.newBetaBlock := by
  rw [base.gaugedData_edgePartition_beta, SheetPartition.relabel_block,
    ← base.betaBlock_eq]
  rfl

theorem gaugedDoubled_shape (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel anchor.1 sheet) :
    sheet ∈ base.newDeltaBlock ∨ sheet ∈ base.newGammaBlock ∨
      (base.gaugedData.edgePartition (Prescribed.doubledEdge base.source)).block
        sheet = {sheet} := by
  classical
  set original := base.deltaPerm.symm sheet with hOriginal
  have hSheetEq : base.deltaPerm original = sheet := by
    rw [hOriginal]
    simp
  have hSheetMem : sheet ∈ base.wholeBlock :=
    ((data.vertexPartition wall).mem_block_iff _ _).mpr hWall
  have hOriginalMem : original ∈ base.wholeBlock :=
    base.perm_symm_inside base.deltaPerm base.deltaPerm_inside base.deltaPerm_outside
      sheet hSheetMem
  have hOriginalWall : (data.vertexPartition wall).Rel anchor.1 original :=
    ((data.vertexPartition wall).mem_block_iff _ _).mp hOriginalMem
  rcases doubled_shape base.source base.noGlue base.swapDoubled original
      hOriginalWall with hDelta | hGamma | hSingleton
  · left
    rw [← hSheetEq]
    exact Finset.mem_image.mpr ⟨original, hDelta, rfl⟩
  · right; left
    rw [← hSheetEq]
    exact Finset.mem_image.mpr ⟨original, hGamma, rfl⟩
  · right; right
    rw [base.gaugedData_edgePartition_doubled, ← hSheetEq,
      SheetPartition.relabel_block, hSingleton]
    simp

theorem gaugedBeta_shape (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel anchor.1 sheet) :
    sheet ∈ base.newBetaBlock ∨
      (base.gaugedData.edgePartition (directionEdge star base.betaLabel)).block
        sheet = {sheet} := by
  classical
  set original := base.betaPerm.symm sheet with hOriginal
  have hSheetEq : base.betaPerm original = sheet := by
    rw [hOriginal]
    simp
  have hSheetMem : sheet ∈ base.wholeBlock :=
    ((data.vertexPartition wall).mem_block_iff _ _).mpr hWall
  have hOriginalMem : original ∈ base.wholeBlock :=
    base.perm_symm_inside base.betaPerm base.betaPerm_inside base.betaPerm_outside
      sheet hSheetMem
  have hOriginalWall : (data.vertexPartition wall).Rel anchor.1 original :=
    ((data.vertexPartition wall).mem_block_iff _ _).mp hOriginalMem
  rcases simple_shape base.source base.noGlue base.betaLabel base.beta_ne original
      hOriginalWall with hBeta | hSingleton
  · left
    rw [← hSheetEq]
    exact Finset.mem_image.mpr ⟨original, hBeta, rfl⟩
  · right
    rw [base.gaugedData_edgePartition_beta, ← hSheetEq,
      SheetPartition.relabel_block, hSingleton]
    simp

/-! ### Exterior compatibility of the resolution -/

theorem refines_blockRefine_of_shape (edge : SheetPartition degree)
    (hRefines : edge.Refines (data.vertexPartition wall))
    (pick : Fin degree → Fin degree)
    (hPick : ∀ sheet, (data.vertexPartition wall).Rel anchor.1 sheet →
      (data.vertexPartition wall).Rel anchor.1 (pick sheet))
    (hIdem : ∀ sheet, (data.vertexPartition wall).Rel anchor.1 sheet →
      pick (pick sheet) = pick sheet)
    (hShape : ∀ first second, (data.vertexPartition wall).Rel anchor.1 first →
      edge.Rel first second → pick first = pick second) :
    edge.Refines
      (blockRefine (data.vertexPartition wall) anchor.1 pick hPick hIdem) := by
  intro first second hRel
  by_cases hFirst : (data.vertexPartition wall).Rel anchor.1 first
  · have hSecond : (data.vertexPartition wall).Rel anchor.1 second :=
      hFirst.trans (hRefines.rel hRel)
    exact (blockRefine.rel_iff_of_rel _ _ _ _ _ hFirst hSecond).mpr
      (hShape first second hFirst hRel)
  · have hSecond : ¬(data.vertexPartition wall).Rel anchor.1 second := by
      intro hMem
      exact hFirst (hMem.trans (hRefines.rel hRel).symm)
    unfold SheetPartition.Rel
    rw [blockRefine.repr_of_not_rel _ _ _ _ _ hFirst,
      blockRefine.repr_of_not_rel _ _ _ _ _ hSecond]
    exact hRefines.rel hRel

theorem gaugedAlpha_refines_left :
    (base.gaugedData.edgePartition (directionEdge star base.alphaLabel)).Refines
      base.leftPartition := by
  rw [base.gaugedData_edgePartition_alpha]
  refine refines_blockRefine_of_shape _
    (Prescribed.directionEdge_refines (data := data) (star := star) base.alphaLabel)
    _ _ _ ?_
  intro first second hFirst hRel
  rcases simple_shape base.source base.noGlue base.alphaLabel base.alpha_ne first
      hFirst with hAlpha | hSingleton
  · have hAlphaMem : first ∈ base.alphaBlock := hAlpha
    have hSecond : second ∈ base.alphaBlock := by
      rw [base.alphaBlock_eq, SheetPartition.mem_block_iff] at hAlphaMem ⊢
      exact hAlphaMem.trans hRel
    rw [base.leftPick_of_mem hAlphaMem, base.leftPick_of_mem hSecond]
  · have hMem : second ∈
        (data.edgePartition (directionEdge star base.alphaLabel)).block first :=
      (SheetPartition.mem_block_iff _ _ _).mpr hRel
    rw [hSingleton, Finset.mem_singleton] at hMem
    rw [hMem]

theorem gaugedDoubled_refines_right :
    (base.gaugedData.edgePartition (Prescribed.doubledEdge base.source)).Refines
      base.rightPartition := by
  refine refines_blockRefine_of_shape _ ?_ _ _ _ ?_
  · rw [base.gaugedData_edgePartition_doubled]
    refine SheetPartition.relabel_refines_fixed_of_pointwise
      (Prescribed.directionEdge_refines (data := data) (star := star)
        (Prescribed.doubled base.source)) base.deltaPerm ?_
    exact rel_of_stabilizes_block (data.vertexPartition wall) anchor.1
      base.deltaPerm base.deltaPerm_inside base.deltaPerm_outside
  · intro first second hFirst hRel
    rcases base.gaugedDoubled_shape first hFirst with hDelta | hGamma | hSingleton
    · have hSecond : second ∈ base.newDeltaBlock := by
        rw [← base.gaugedDoubled_block_delta, SheetPartition.mem_block_iff] at hDelta ⊢
        exact hDelta.trans hRel
      rw [base.rightPick_of_mem hDelta, base.rightPick_of_mem hSecond]
    · have hSecond : second ∈ base.newGammaBlock := by
        rw [← base.gaugedDoubled_block_gamma, SheetPartition.mem_block_iff] at hGamma ⊢
        exact hGamma.trans hRel
      have hDisjoint := base.newGammaBlock_inter_newDeltaBlock
      have hFirstNot : first ∉ base.newDeltaBlock := by
        intro hMem
        have : first ∈ base.newGammaBlock ∩ base.newDeltaBlock :=
          Finset.mem_inter.mpr ⟨hGamma, hMem⟩
        rw [hDisjoint] at this
        exact absurd this (Finset.notMem_empty first)
      have hSecondNot : second ∉ base.newDeltaBlock := by
        intro hMem
        have : second ∈ base.newGammaBlock ∩ base.newDeltaBlock :=
          Finset.mem_inter.mpr ⟨hSecond, hMem⟩
        rw [hDisjoint] at this
        exact absurd this (Finset.notMem_empty second)
      rw [base.rightPick_of_not_mem hFirstNot, base.rightPick_of_not_mem hSecondNot]
    · have hMem : second ∈
          (base.gaugedData.edgePartition (Prescribed.doubledEdge base.source)).block
            first := (SheetPartition.mem_block_iff _ _ _).mpr hRel
      rw [hSingleton, Finset.mem_singleton] at hMem
      rw [hMem]

theorem gaugedBeta_refines_right :
    (base.gaugedData.edgePartition (directionEdge star base.betaLabel)).Refines
      base.rightPartition := by
  refine refines_blockRefine_of_shape _ ?_ _ _ _ ?_
  · rw [base.gaugedData_edgePartition_beta]
    refine SheetPartition.relabel_refines_fixed_of_pointwise
      (Prescribed.directionEdge_refines (data := data) (star := star) base.betaLabel)
      base.betaPerm ?_
    exact rel_of_stabilizes_block (data.vertexPartition wall) anchor.1
      base.betaPerm base.betaPerm_inside base.betaPerm_outside
  · intro first second hFirst hRel
    rcases base.gaugedBeta_shape first hFirst with hBeta | hSingleton
    · have hSecond : second ∈ base.newBetaBlock := by
        rw [← base.gaugedBeta_block_beta, SheetPartition.mem_block_iff] at hBeta ⊢
        exact hBeta.trans hRel
      have hFirstNot : first ∉ base.newDeltaBlock :=
        (Finset.mem_sdiff.mp (base.newBetaBlock_subset_sdiff hBeta)).2
      have hSecondNot : second ∉ base.newDeltaBlock :=
        (Finset.mem_sdiff.mp (base.newBetaBlock_subset_sdiff hSecond)).2
      rw [base.rightPick_of_not_mem hFirstNot, base.rightPick_of_not_mem hSecondNot]
    · have hMem : second ∈
          (base.gaugedData.edgePartition (directionEdge star base.betaLabel)).block
            first := (SheetPartition.mem_block_iff _ _ _).mpr hRel
      rw [hSingleton, Finset.mem_singleton] at hMem
      rw [hMem]


/-! ### The six induced block counts at the trivalent point `v` -/

/-- The sheet naming the gauged class of `e_gamma`. -/
noncomputable def gammaRepr : Fin degree :=
  base.deltaPerm (Prescribed.occurrenceSheet base.gammaSurvivor)

/-- The sheet naming the gauged class of `e_beta`. -/
noncomputable def betaRepr : Fin degree :=
  base.betaPerm (Prescribed.occurrenceSheet base.betaSurvivor)

theorem gammaRepr_mem : base.gammaRepr ∈ base.newGammaBlock :=
  Finset.mem_image.mpr
    ⟨Prescribed.occurrenceSheet base.gammaSurvivor,
      occurrenceSheet_mem_occurrenceBlock base.gammaSurvivor, rfl⟩

theorem betaRepr_mem : base.betaRepr ∈ base.newBetaBlock :=
  Finset.mem_image.mpr
    ⟨Prescribed.occurrenceSheet base.betaSurvivor,
      occurrenceSheet_mem_occurrenceBlock base.betaSurvivor, rfl⟩

theorem newGammaBlock_card : base.newGammaBlock.card = base.kGamma := by
  rw [newGammaBlock, Finset.card_image_of_injective _ base.deltaPerm.injective,
    base.gammaBlock_card]

theorem newGammaBlock_subset_whole : base.newGammaBlock ⊆ base.wholeBlock := by
  intro sheet hSheet
  obtain ⟨original, hOriginal, rfl⟩ := Finset.mem_image.mp hSheet
  exact base.deltaPerm_inside original (base.gammaBlock_subset hOriginal)

theorem newGammaBlock_not_mem_delta {sheet : Fin degree}
    (hSheet : sheet ∈ base.newGammaBlock) : sheet ∉ base.newDeltaBlock := by
  intro hMem
  have hInter : sheet ∈ base.newGammaBlock ∩ base.newDeltaBlock :=
    Finset.mem_inter.mpr ⟨hSheet, hMem⟩
  rw [base.newGammaBlock_inter_newDeltaBlock] at hInter
  exact absurd hInter (Finset.notMem_empty sheet)

theorem mem_newDeltaBlock_of_right_rel {sheet : Fin degree}
    (hSheet : base.rightPartition.Rel base.deltaRepr sheet) :
    sheet ∈ base.newDeltaBlock := by
  rw [← base.rightPartition_block_delta]
  exact (SheetPartition.mem_block_iff _ _ _).mpr hSheet

theorem mem_sdiff_of_right_hub_rel {sheet : Fin degree}
    (hSheet : base.rightPartition.Rel base.hubSheet sheet) :
    sheet ∈ base.wholeBlock \ base.newDeltaBlock := by
  rw [← base.rightPartition_block_hub]
  exact (SheetPartition.mem_block_iff _ _ _).mpr hSheet

theorem right_rel_delta_of_mem {sheet : Fin degree}
    (hSheet : sheet ∈ base.newDeltaBlock) :
    base.rightPartition.Rel base.deltaRepr sheet := by
  rw [← base.rightPartition_block_delta] at hSheet
  exact (SheetPartition.mem_block_iff _ _ _).mp hSheet

theorem right_rel_hub_of_mem {sheet : Fin degree}
    (hSheet : sheet ∈ base.wholeBlock \ base.newDeltaBlock) :
    base.rightPartition.Rel base.hubSheet sheet := by
  rw [← base.rightPartition_block_hub] at hSheet
  exact (SheetPartition.mem_block_iff _ _ _).mp hSheet

/-- The bridge is the only new occurrence inside `A'`: `A'` sees exactly one
class of the new edge. -/
theorem newEdge_count_delta :
    base.newEdgePartition.blockCountWithin base.rightPartition base.deltaRepr = 1 := by
  have hCount :=
    NonTrivalentValencyFourKZero.PrescribedPairing.blockCountWithin_add_blockCard_eq
      base.newEdgePartition base.rightPartition base.deltaRepr base.deltaRepr rfl
      base.newEdgePartition_refines_right (by
        intro sheet hSheet
        left
        rw [← SheetPartition.mem_block_iff, base.newEdgePartition_block_delta]
        exact base.mem_newDeltaBlock_of_right_rel hSheet)
  rw [base.newEdgePartition_blockCard_delta, base.rightPartition_blockCard_delta]
    at hCount
  omega

/-- `A'` sees exactly one class of the doubled direction, namely itself. -/
theorem doubled_count_delta :
    (base.gaugedData.edgePartition (Prescribed.doubledEdge base.source)).blockCountWithin
      base.rightPartition base.deltaRepr = 1 := by
  have hCard : (base.gaugedData.edgePartition
      (Prescribed.doubledEdge base.source)).blockCard base.deltaRepr = base.kDelta := by
    rw [SheetPartition.blockCard, base.gaugedDoubled_block_delta,
      base.newDeltaBlock_card]
  have hCount :=
    NonTrivalentValencyFourKZero.PrescribedPairing.blockCountWithin_add_blockCard_eq
      (base.gaugedData.edgePartition (Prescribed.doubledEdge base.source))
      base.rightPartition base.deltaRepr base.deltaRepr rfl
      base.gaugedDoubled_refines_right (by
        intro sheet hSheet
        left
        rw [← SheetPartition.mem_block_iff, base.gaugedDoubled_block_delta]
        exact base.mem_newDeltaBlock_of_right_rel hSheet)
  rw [hCard, base.rightPartition_blockCard_delta] at hCount
  omega

/-- Every occurrence of `t_beta` inside `A'` is dangling: `A'` sees `k_delta`
of them.  This is where `|A| >= k_beta + k_delta` is used. -/
theorem beta_count_delta :
    (base.gaugedData.edgePartition (directionEdge star base.betaLabel)).blockCountWithin
      base.rightPartition base.deltaRepr = base.kDelta := by
  have hSingleton : ∀ sheet ∈ base.newDeltaBlock,
      (base.gaugedData.edgePartition (directionEdge star base.betaLabel)).block
        sheet = {sheet} := by
    intro sheet hSheet
    have hWall : (data.vertexPartition wall).Rel anchor.1 sheet :=
      ((data.vertexPartition wall).mem_block_iff _ _).mp
        (base.newDeltaBlock_subset_whole hSheet)
    rcases base.gaugedBeta_shape sheet hWall with hBeta | hOther
    · exact absurd hSheet
        (Finset.mem_sdiff.mp (base.newBetaBlock_subset_sdiff hBeta)).2
    · exact hOther
  have hCard : (base.gaugedData.edgePartition
      (directionEdge star base.betaLabel)).blockCard base.deltaRepr = 1 := by
    rw [SheetPartition.blockCard, hSingleton base.deltaRepr base.deltaRepr_mem]
    exact Finset.card_singleton _
  have hCount :=
    NonTrivalentValencyFourKZero.PrescribedPairing.blockCountWithin_add_blockCard_eq
      (base.gaugedData.edgePartition (directionEdge star base.betaLabel))
      base.rightPartition base.deltaRepr base.deltaRepr rfl
      base.gaugedBeta_refines_right (by
        intro sheet hSheet
        right
        exact hSingleton sheet (base.mem_newDeltaBlock_of_right_rel hSheet))
  rw [hCard, base.rightPartition_blockCard_delta] at hCount
  omega

/-- `A_v` sees the bridge and one dangling new occurrence per sheet outside
`A_u`. -/
theorem newEdge_count_hub :
    base.newEdgePartition.blockCountWithin base.rightPartition base.hubSheet +
        base.newEdgePartition.blockCard base.hubSheet =
      base.rightPartition.blockCard base.hubSheet + 1 :=
  NonTrivalentValencyFourKZero.PrescribedPairing.blockCountWithin_add_blockCard_eq
    base.newEdgePartition base.rightPartition base.hubSheet base.hubSheet rfl
    base.newEdgePartition_refines_right (by
      intro sheet hSheet
      have hMem := base.mem_sdiff_of_right_hub_rel hSheet
      have hWall : (data.vertexPartition wall).Rel anchor.1 sheet :=
        ((data.vertexPartition wall).mem_block_iff _ _).mp
          (Finset.mem_sdiff.mp hMem).1
      by_cases hAlpha : sheet ∈ base.alphaBlock
      · left
        rw [← SheetPartition.mem_block_iff, base.newEdgePartition_block_hub]
        exact Finset.mem_sdiff.mpr ⟨hAlpha, (Finset.mem_sdiff.mp hMem).2⟩
      · right
        exact base.newEdgePartition_block_singleton hWall hAlpha)

/-- `A_v` sees the class of `e_gamma` and one dangling occurrence per other
sheet. -/
theorem doubled_count_hub :
    (base.gaugedData.edgePartition (Prescribed.doubledEdge base.source)).blockCountWithin
          base.rightPartition base.hubSheet + base.kGamma =
      base.rightPartition.blockCard base.hubSheet + 1 := by
  have hCard : (base.gaugedData.edgePartition
      (Prescribed.doubledEdge base.source)).blockCard base.gammaRepr = base.kGamma := by
    rw [SheetPartition.blockCard, gammaRepr, base.gaugedDoubled_block_gamma,
      base.newGammaBlock_card]
  have hActive : base.rightPartition.Rel base.hubSheet base.gammaRepr :=
    base.right_rel_hub_of_mem (Finset.mem_sdiff.mpr
      ⟨base.newGammaBlock_subset_whole base.gammaRepr_mem,
        base.newGammaBlock_not_mem_delta base.gammaRepr_mem⟩)
  have hCount :=
    NonTrivalentValencyFourKZero.PrescribedPairing.blockCountWithin_add_blockCard_eq
      (base.gaugedData.edgePartition (Prescribed.doubledEdge base.source))
      base.rightPartition base.hubSheet base.gammaRepr hActive
      base.gaugedDoubled_refines_right (by
        intro sheet hSheet
        have hMem := base.mem_sdiff_of_right_hub_rel hSheet
        have hWall : (data.vertexPartition wall).Rel anchor.1 sheet :=
          ((data.vertexPartition wall).mem_block_iff _ _).mp
            (Finset.mem_sdiff.mp hMem).1
        rcases base.gaugedDoubled_shape sheet hWall with hDelta | hGamma | hSingle
        · exact absurd hDelta (Finset.mem_sdiff.mp hMem).2
        · left
          rw [← SheetPartition.mem_block_iff, gammaRepr,
            base.gaugedDoubled_block_gamma]
          exact hGamma
        · right
          exact hSingle)
  rw [hCard] at hCount
  exact hCount

/-- `A_v` sees the class of `e_beta` and one dangling occurrence per other
sheet. -/
theorem beta_count_hub :
    (base.gaugedData.edgePartition (directionEdge star base.betaLabel)).blockCountWithin
          base.rightPartition base.hubSheet + base.kBeta =
      base.rightPartition.blockCard base.hubSheet + 1 := by
  have hCard : (base.gaugedData.edgePartition
      (directionEdge star base.betaLabel)).blockCard base.betaRepr = base.kBeta := by
    rw [SheetPartition.blockCard, betaRepr, base.gaugedBeta_block_beta,
      base.newBetaBlock_card]
  have hActive : base.rightPartition.Rel base.hubSheet base.betaRepr :=
    base.right_rel_hub_of_mem (base.newBetaBlock_subset_sdiff base.betaRepr_mem)
  have hCount :=
    NonTrivalentValencyFourKZero.PrescribedPairing.blockCountWithin_add_blockCard_eq
      (base.gaugedData.edgePartition (directionEdge star base.betaLabel))
      base.rightPartition base.hubSheet base.betaRepr hActive
      base.gaugedBeta_refines_right (by
        intro sheet hSheet
        have hMem := base.mem_sdiff_of_right_hub_rel hSheet
        have hWall : (data.vertexPartition wall).Rel anchor.1 sheet :=
          ((data.vertexPartition wall).mem_block_iff _ _).mp
            (Finset.mem_sdiff.mp hMem).1
        rcases base.gaugedBeta_shape sheet hWall with hBeta | hSingle
        · left
          rw [← SheetPartition.mem_block_iff, betaRepr, base.gaugedBeta_block_beta]
          exact hBeta
        · right
          exact hSingle)
  rw [hCard] at hCount
  exact hCount


/-! ### Both endpoint Riemann--Hurwitz inequalities at the anchor -/

/-- The divalent endpoint `u` needs no source input: it carries two
occurrences, `e_alpha` and the new edge. -/
theorem selected_riemannHurwitz_left (block : Fin degree) :
    LocalResolution.RiemannHurwitzAtBlock (base.gaugedData.vertexPartition wall)
      base.selectedResolution.left
      (base.selectedResolution.newEdge ::
        ([directionEdge star base.alphaLabel] : List target.edges).map
          base.gaugedData.edgePartition) block := by
  simpa using riemannHurwitzAtBlock_divalent
    (base.gaugedData.vertexPartition wall) base.selectedResolution.left
    base.selectedResolution.newEdge
    (base.gaugedData.edgePartition (directionEdge star base.alphaLabel)) block

/-- The three induced counts at every sheet of the anchor block.  Both new
vertices over `v` hold with equality: at `A'` this is `1 + 1 + k_delta`, and
at `A_v` it is exactly identity `(boxplus)`. -/
theorem selected_counts (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel anchor.1 sheet) :
    base.newEdgePartition.blockCountWithin base.rightPartition sheet +
          (base.gaugedData.edgePartition
            (Prescribed.doubledEdge base.source)).blockCountWithin
              base.rightPartition sheet +
          (base.gaugedData.edgePartition
            (directionEdge star base.betaLabel)).blockCountWithin
              base.rightPartition sheet ≥
      base.rightPartition.blockCard sheet + 2 := by
  by_cases hDelta : sheet ∈ base.newDeltaBlock
  · have hRel : base.rightPartition.Rel sheet base.deltaRepr :=
      (base.right_rel_delta_of_mem hDelta).symm
    rw [blockCountWithin_congr _ _ hRel, blockCountWithin_congr _ _ hRel,
      blockCountWithin_congr _ _ hRel, blockCard_congr _ hRel,
      base.newEdge_count_delta, base.doubled_count_delta, base.beta_count_delta,
      base.rightPartition_blockCard_delta]
    omega
  · have hMem : sheet ∈ base.wholeBlock \ base.newDeltaBlock :=
      Finset.mem_sdiff.mpr
        ⟨((data.vertexPartition wall).mem_block_iff _ _).mpr hSheet, hDelta⟩
    have hRel : base.rightPartition.Rel sheet base.hubSheet :=
      (base.right_rel_hub_of_mem hMem).symm
    rw [blockCountWithin_congr _ _ hRel, blockCountWithin_congr _ _ hRel,
      blockCountWithin_congr _ _ hRel, blockCard_congr _ hRel]
    have hNew := base.newEdge_count_hub
    have hDoubledCount := base.doubled_count_hub
    have hBetaCount := base.beta_count_hub
    have hBridge := base.newEdgePartition_blockCard_hub
    have hVertex := base.rightPartition_blockCard_hub
    have hBox := base.boxplus
    have hLe := base.doubled_le
    omega

/-- The same three counts, as an **equality**: the source's `r = 0` at both
new vertices over `v`.  At `A'` it reads `1 + 1 + k_delta = k_delta + 2`; at
`A_v` it is identity `(boxplus)`.  The row dictionary
(`NonTrivalentValencyThreeSimpleRows`) needs this exact form, not just the
inequality. -/
theorem selected_counts_eq (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel anchor.1 sheet) :
    base.newEdgePartition.blockCountWithin base.rightPartition sheet +
          (base.gaugedData.edgePartition
            (Prescribed.doubledEdge base.source)).blockCountWithin
              base.rightPartition sheet +
          (base.gaugedData.edgePartition
            (directionEdge star base.betaLabel)).blockCountWithin
              base.rightPartition sheet =
      base.rightPartition.blockCard sheet + 2 := by
  by_cases hDelta : sheet ∈ base.newDeltaBlock
  · have hRel : base.rightPartition.Rel sheet base.deltaRepr :=
      (base.right_rel_delta_of_mem hDelta).symm
    rw [blockCountWithin_congr _ _ hRel, blockCountWithin_congr _ _ hRel,
      blockCountWithin_congr _ _ hRel, blockCard_congr _ hRel,
      base.newEdge_count_delta, base.doubled_count_delta, base.beta_count_delta,
      base.rightPartition_blockCard_delta]
    omega
  · have hMem : sheet ∈ base.wholeBlock \ base.newDeltaBlock :=
      Finset.mem_sdiff.mpr
        ⟨((data.vertexPartition wall).mem_block_iff _ _).mpr hSheet, hDelta⟩
    have hRel : base.rightPartition.Rel sheet base.hubSheet :=
      (base.right_rel_hub_of_mem hMem).symm
    rw [blockCountWithin_congr _ _ hRel, blockCountWithin_congr _ _ hRel,
      blockCountWithin_congr _ _ hRel, blockCard_congr _ hRel]
    have hNew := base.newEdge_count_hub
    have hDoubledCount := base.doubled_count_hub
    have hBetaCount := base.beta_count_hub
    have hBridge := base.newEdgePartition_blockCard_hub
    have hVertex := base.rightPartition_blockCard_hub
    have hBox := base.boxplus
    have hLe := base.doubled_le
    omega

/-- The trivalent endpoint `v`, carrying both `A'` and `A_v`. -/
theorem selected_riemannHurwitz_right (block : Fin degree)
    (hBlock : (data.vertexPartition wall).Rel anchor.1 block) :
    LocalResolution.RiemannHurwitzAtBlock (base.gaugedData.vertexPartition wall)
      base.selectedResolution.right
      (base.selectedResolution.newEdge ::
        ([Prescribed.doubledEdge base.source, directionEdge star base.betaLabel] :
          List target.edges).map base.gaugedData.edgePartition) block := by
  rw [base.gaugedData_vertexPartition_wall]
  have hCounts : ∀ sheet, (data.vertexPartition wall).Rel block sheet →
      base.newEdgePartition.blockCountWithin base.rightPartition sheet +
          (base.gaugedData.edgePartition
            (Prescribed.doubledEdge base.source)).blockCountWithin
              base.rightPartition sheet +
          (base.gaugedData.edgePartition
            (directionEdge star base.betaLabel)).blockCountWithin
              base.rightPartition sheet ≥
        base.rightPartition.blockCard sheet + 2 := by
    intro sheet hRel
    exact base.selected_counts sheet (hBlock.trans hRel)
  simpa using riemannHurwitzAtBlock_trivalent_of_counts (data.vertexPartition wall)
    base.selectedResolution.right base.selectedResolution.newEdge
    (base.gaugedData.edgePartition (Prescribed.doubledEdge base.source))
    (base.gaugedData.edgePartition (directionEdge star base.betaLabel)) block
    hCounts

/-! ### The outgoing base tree `T_alpha` and its occurrence assignment -/

/-- Base tree `T_alpha`: the divalent end `u` keeps the simple direction
`t_alpha`, the trivalent end `v` keeps `t_2` and `t_beta`. -/
noncomputable def rightAssignment : target.edges → Bool :=
  fun edge ↦ decide (edge ≠ directionEdge star base.alphaLabel)

/-- The single old occurrence at the divalent end `u`. -/
noncomputable def leftEdges : List target.edges :=
  [directionEdge star base.alphaLabel]

/-- The two old occurrences at the trivalent end `v`. -/
noncomputable def rightEdges : List target.edges :=
  [Prescribed.doubledEdge base.source, directionEdge star base.betaLabel]

@[simp] theorem rightAssignment_alpha :
    base.rightAssignment (directionEdge star base.alphaLabel) = false := by
  simp [rightAssignment]

theorem rightAssignment_eq_false_iff (edge : target.edges) :
    base.rightAssignment edge = false ↔ edge = directionEdge star base.alphaLabel := by
  simp [rightAssignment]

theorem rightAssignment_of_ne {edge : target.edges}
    (hEdge : edge ≠ directionEdge star base.alphaLabel) :
    base.rightAssignment edge = true := by
  simp [rightAssignment, hEdge]

theorem alphaEdge_ne_betaEdge :
    directionEdge star base.alphaLabel ≠ directionEdge star base.betaLabel := by
  intro hEq
  exact base.beta_ne_alpha (directionEdge_injective star hEq).symm

theorem alphaEdge_ne_doubledEdge :
    directionEdge star base.alphaLabel ≠ Prescribed.doubledEdge base.source :=
  fun hEq ↦ base.doubledEdge_ne_direction base.alphaLabel base.alpha_ne hEq.symm

theorem betaEdge_ne_doubledEdge :
    directionEdge star base.betaLabel ≠ Prescribed.doubledEdge base.source :=
  fun hEq ↦ base.doubledEdge_ne_direction base.betaLabel base.beta_ne hEq.symm

theorem incidentEdges_eq_triple :
    GluingDatum.incidentEdges wall =
      {directionEdge star base.alphaLabel, Prescribed.doubledEdge base.source,
        directionEdge star base.betaLabel} := by
  classical
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro edge hEdge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
    rcases hEdge with rfl | rfl | rfl
    · exact directionEdge_mem_incidentEdges star _
    · exact Prescribed.doubledEdge_mem_incidentEdges _
    · exact directionEdge_mem_incidentEdges star _
  · rw [star.card_incidentEdges,
      Finset.card_insert_of_notMem (by
        simp [base.alphaEdge_ne_doubledEdge, base.alphaEdge_ne_betaEdge]),
      Finset.card_insert_of_notMem (by
        simp [Ne.symm base.betaEdge_ne_doubledEdge]),
      Finset.card_singleton]

theorem wallEdgesAssigned_false :
    wallEdgesAssigned target wall base.rightAssignment false =
      {directionEdge star base.alphaLabel} := by
  classical
  ext edge
  rw [mem_wallEdgesAssigned, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hSide⟩
    exact (base.rightAssignment_eq_false_iff edge).mp hSide
  · rintro rfl
    exact ⟨(GluingContraction.mem_incidentEdges_iff wall _).mp
      (directionEdge_mem_incidentEdges star _), base.rightAssignment_alpha⟩

theorem wallEdgesAssigned_true :
    wallEdgesAssigned target wall base.rightAssignment true =
      {Prescribed.doubledEdge base.source, directionEdge star base.betaLabel} := by
  classical
  ext edge
  rw [mem_wallEdgesAssigned, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hIncident, hSide⟩
    have hMem : edge ∈ GluingDatum.incidentEdges wall :=
      (GluingContraction.mem_incidentEdges_iff wall edge).mpr hIncident
    rw [base.incidentEdges_eq_triple] at hMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hMem
    rcases hMem with rfl | hMem | hMem
    · rw [base.rightAssignment_alpha] at hSide
      exact absurd hSide (by simp)
    · exact Or.inl hMem
    · exact Or.inr hMem
  · intro hEdge
    rcases hEdge with rfl | rfl
    · exact ⟨(GluingContraction.mem_incidentEdges_iff wall _).mp
        (Prescribed.doubledEdge_mem_incidentEdges _),
        base.rightAssignment_of_ne (Ne.symm base.alphaEdge_ne_doubledEdge)⟩
    · exact ⟨(GluingContraction.mem_incidentEdges_iff wall _).mp
        (directionEdge_mem_incidentEdges star _),
        base.rightAssignment_of_ne (Ne.symm base.alphaEdge_ne_betaEdge)⟩

theorem leftEdges_eq :
    ((base.leftEdges : List target.edges) : Multiset target.edges) =
      (wallEdgesAssigned target wall base.rightAssignment false).val := by
  rw [base.wallEdgesAssigned_false]
  rfl

theorem rightEdges_eq :
    ((base.rightEdges : List target.edges) : Multiset target.edges) =
      (wallEdgesAssigned target wall base.rightAssignment true).val := by
  classical
  rw [base.wallEdgesAssigned_true,
    Finset.insert_val_of_notMem (by simp [Ne.symm base.betaEdge_ne_doubledEdge])]
  rfl

/-- Exterior compatibility with every old occurrence at the wall. -/
theorem selected_exterior (edge : target.edges)
    (hIncident : (edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) :
    (base.gaugedData.edgePartition edge).Refines
      (if base.rightAssignment edge then base.selectedResolution.right
        else base.selectedResolution.left) := by
  classical
  have hMem : edge ∈ GluingDatum.incidentEdges wall :=
    (GluingContraction.mem_incidentEdges_iff wall edge).mpr hIncident
  rw [base.incidentEdges_eq_triple] at hMem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hMem
  rcases hMem with rfl | rfl | rfl
  · rw [base.rightAssignment_alpha, if_neg (by simp)]
    exact base.gaugedAlpha_refines_left
  · rw [base.rightAssignment_of_ne (Ne.symm base.alphaEdge_ne_doubledEdge),
      if_pos rfl]
    exact base.gaugedDoubled_refines_right
  · rw [base.rightAssignment_of_ne (Ne.symm base.alphaEdge_ne_betaEdge), if_pos rfl]
    exact base.gaugedBeta_refines_right

end SimpleBase

/-! ## 9.  The guarded background and the installed candidate -/

/-- The source geometry still required away from the distinguished anchor
class: exactly the guarded background resolutions of the other wall blocks of
the *gauged* incoming datum.  No fine partition, no selected-block
Riemann--Hurwitz receipt and no validity of the outgoing datum is supplied
here. -/
structure SubdivisionBackground (base : SimpleBase data star anchor) where
  resolution : Fin degree → LocalResolution degree
  contracts : ∀ block, ¬(base.gaugedData.vertexPartition wall).Rel anchor.1 block →
    (resolution block).ContractsTo (base.gaugedData.vertexPartition wall)
  exterior : ∀ edge : target.edges,
    ((edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) →
    ∀ block, ¬(base.gaugedData.vertexPartition wall).Rel anchor.1 block →
      (base.gaugedData.edgePartition edge).Refines
        (if base.rightAssignment edge then (resolution block).right
          else (resolution block).left)
  left_riemannHurwitz : ∀ block,
    (base.gaugedData.vertexPartition wall).repr block = block →
    ¬(base.gaugedData.vertexPartition wall).Rel anchor.1 block →
      LocalResolution.RiemannHurwitzAtBlock (base.gaugedData.vertexPartition wall)
        (resolution block).left
        ((resolution block).newEdge ::
          base.leftEdges.map base.gaugedData.edgePartition) block
  right_riemannHurwitz : ∀ block,
    (base.gaugedData.vertexPartition wall).repr block = block →
    ¬(base.gaugedData.vertexPartition wall).Rel anchor.1 block →
      LocalResolution.RiemannHurwitzAtBlock (base.gaugedData.vertexPartition wall)
        (resolution block).right
        ((resolution block).newEdge ::
          base.rightEdges.map base.gaugedData.edgePartition) block

namespace SubdivisionBackground

/-- Package the guarded receipts with the base tree `T_alpha` assignment. -/
noncomputable def background (base : SimpleBase data star anchor)
    (geometry : SubdivisionBackground base) :
    GlobalM11Arbitrary.Background base.gaugedData wall anchor.1 where
  right := base.rightAssignment
  resolution := geometry.resolution
  contracts := geometry.contracts
  exterior := geometry.exterior
  leftEdges := base.leftEdges
  rightEdges := base.rightEdges
  leftEdges_eq := base.leftEdges_eq
  rightEdges_eq := base.rightEdges_eq
  left_riemannHurwitz := geometry.left_riemannHurwitz
  right_riemannHurwitz := geometry.right_riemannHurwitz

end SubdivisionBackground

/-- **The prescribed Type I / Type II resolution installed** into the guarded
background: an actual globally assembled candidate over the gauged incoming
datum. -/
noncomputable def candidate (base : SimpleBase data star anchor)
    (geometry : SubdivisionBackground base) :
    BalancedGlobal.Candidate target degree base.gaugedData wall := by
  refine (SubdivisionBackground.background base geometry).install
    base.selectedResolution ?_ base.selected_exterior ?_ ?_
  · rw [base.gaugedData_vertexPartition_wall]
    exact base.selectedResolution_contracts
  · intro block _ _
    exact base.selected_riemannHurwitz_left block
  · intro block hRel _
    refine base.selected_riemannHurwitz_right block ?_
    rwa [base.gaugedData_vertexPartition_wall] at hRel

theorem candidate_resolution_of_wall_rel (base : SimpleBase data star anchor)
    (geometry : SubdivisionBackground base) (block : Fin degree)
    (hRel : (base.gaugedData.vertexPartition wall).Rel anchor.1 block) :
    (candidate base geometry).resolution block = base.selectedResolution := by
  unfold candidate SubdivisionBackground.background
    GlobalM11Arbitrary.Background.install
  exact LocalResolution.onBlock_of_rel _ _ _ _ _ hRel

theorem candidate_resolution_anchor (base : SimpleBase data star anchor)
    (geometry : SubdivisionBackground base) :
    (candidate base geometry).resolution anchor.1 = base.selectedResolution :=
  candidate_resolution_of_wall_rel base geometry anchor.1 rfl

/-- Incoming validity is the only validity input; the gauge transports it. -/
theorem candidate_datum_valid (base : SimpleBase data star anchor)
    (geometry : SubdivisionBackground base) (hValid : data.Valid) :
    (candidate base geometry).datum.Valid :=
  (candidate base geometry).datum_valid (base.gaugedData_valid hValid)

/-! ## 10.  The background producer at a simple direction

At `T_alpha` the subdivision point lies on a *simple* direction, so the single
global resolution splits along `edgePartition (directionEdge star alpha)`
rather than along the doubled direction as in the Type III producer of
`NonTrivalentValencyThreeCandidate`.
Everything else is the same: the divalent endpoint inequality is automatic,
and the trivalent endpoint inequality is literally the gauged datum's own
Riemann--Hurwitz condition at `wall`. -/

/-- The resolution installed on every ordinary wall block. -/
noncomputable def ordinaryResolution (base : SimpleBase data star anchor) :
    LocalResolution degree :=
  fineResolution (base.gaugedData.vertexPartition wall)
    (base.gaugedData.edgePartition (directionEdge star base.alphaLabel))
    (edgePartition_refines_of_mem_incidentEdges base.gaugedData wall _
      (directionEdge_mem_incidentEdges star base.alphaLabel))

theorem incidentList_eq (base : SimpleBase data star anchor) :
    ((directionEdge star base.alphaLabel :: base.rightEdges : List target.edges) :
        Multiset target.edges) = (GluingDatum.incidentEdges wall).val := by
  classical
  rw [base.incidentEdges_eq_triple,
    Finset.insert_val_of_notMem (by
      simp [base.alphaEdge_ne_doubledEdge, base.alphaEdge_ne_betaEdge]),
    Finset.insert_val_of_notMem (by
      simp [Ne.symm base.betaEdge_ne_doubledEdge])]
  rfl

/-- **The background producer.**  Incoming validity alone supplies every
guarded receipt; at a trivalent wall the rigid blocks need no census. -/
noncomputable def subdivisionBackground (base : SimpleBase data star anchor)
    (hValid : data.Valid) : SubdivisionBackground base where
  resolution := fun _ ↦ ordinaryResolution base
  contracts := fun _ _ ↦ fineResolution_contracts _ _ _
  exterior := by
    intro edge hIncident block _
    classical
    have hMem : edge ∈ GluingDatum.incidentEdges wall :=
      (GluingContraction.mem_incidentEdges_iff wall edge).mpr hIncident
    by_cases hEdge : edge = directionEdge star base.alphaLabel
    · subst hEdge
      rw [base.rightAssignment_alpha, if_neg (by simp)]
      exact SheetPartition.Refines.refl _
    · rw [base.rightAssignment_of_ne hEdge, if_pos rfl]
      exact edgePartition_refines_of_mem_incidentEdges base.gaugedData wall edge hMem
  left_riemannHurwitz := by
    intro block _ _
    simpa [SimpleBase.leftEdges, ordinaryResolution, fineResolution] using
      riemannHurwitzAtBlock_divalent (base.gaugedData.vertexPartition wall)
        (ordinaryResolution base).left (ordinaryResolution base).newEdge
        (base.gaugedData.edgePartition (directionEdge star base.alphaLabel)) block
  right_riemannHurwitz := by
    intro block hCanonical _
    have hList := (base.gaugedData.riemannHurwitzAtTargetVertex_iff_incidentList wall
      (directionEdge star base.alphaLabel :: base.rightEdges)
      (incidentList_eq base)).mp ((base.gaugedData_valid hValid).2 wall)
    have hBlocks := (LocalResolution.riemannHurwitzAt_iff_forall_wallBlock
      (base.gaugedData.vertexPartition wall) (base.gaugedData.vertexPartition wall)
      ((directionEdge star base.alphaLabel :: base.rightEdges).map
        base.gaugedData.edgePartition)).mp hList block hCanonical
    simpa [ordinaryResolution, fineResolution] using hBlocks

/-- Non-vacuity of the guarded background: it is inhabited for every valid
incoming datum, with no census and no `nd <= 3` bound away from the anchor. -/
theorem nonempty_subdivisionBackground (base : SimpleBase data star anchor)
    (hValid : data.Valid) : Nonempty (SubdivisionBackground base) :=
  ⟨subdivisionBackground base hValid⟩

/-- **The Type I / Type II candidate**, with no background hypothesis. -/
noncomputable def validCandidate (base : SimpleBase data star anchor)
    (hValid : data.Valid) :
    BalancedGlobal.Candidate target degree base.gaugedData wall :=
  candidate base (subdivisionBackground base hValid)

theorem validCandidate_datum_valid (base : SimpleBase data star anchor)
    (hValid : data.Valid) : (validCandidate base hValid).datum.Valid :=
  candidate_datum_valid base _ hValid

theorem validCandidate_resolution_of_wall_rel (base : SimpleBase data star anchor)
    (hValid : data.Valid) (block : Fin degree)
    (hRel : (base.gaugedData.vertexPartition wall).Rel anchor.1 block) :
    (validCandidate base hValid).resolution block = base.selectedResolution :=
  candidate_resolution_of_wall_rel base _ block hRel

theorem validCandidate_resolution_anchor (base : SimpleBase data star anchor)
    (hValid : data.Valid) :
    (validCandidate base hValid).resolution anchor.1 = base.selectedResolution :=
  candidate_resolution_anchor base _


/-! ## 11.  The exact sizes and the resulting combinatorial type -/

/-- The three new vertices and the bridge, with the source's exact sizes:
`|A_u| = k_alpha`, `|A'| = k_delta`, `|A_v| = |A| - k_delta` and
`k_1 = k_alpha - k_delta`. -/
theorem validCandidate_sizes (base : SimpleBase data star anchor)
    (hValid : data.Valid) :
    ((validCandidate base hValid).resolution anchor.1).left.blockCard
          base.hubSheet = base.kAlpha ∧
      ((validCandidate base hValid).resolution anchor.1).right.blockCard
          base.deltaRepr = base.kDelta ∧
      ((validCandidate base hValid).resolution anchor.1).right.blockCard
          base.hubSheet + base.kDelta = base.wallCard ∧
      ((validCandidate base hValid).resolution anchor.1).newEdge.blockCard
          base.deltaRepr = base.kDelta ∧
      ((validCandidate base hValid).resolution anchor.1).newEdge.blockCard
          base.hubSheet + base.kDelta = base.kAlpha := by
  rw [validCandidate_resolution_anchor base hValid]
  exact ⟨base.leftPartition_blockCard_hub, base.rightPartition_blockCard_delta,
    base.rightPartition_blockCard_hub, base.newEdgePartition_blockCard_delta,
    base.newEdgePartition_blockCard_hub⟩

theorem validCandidate_newSourceEdge_index_delta (base : SimpleBase data star anchor)
    (hValid : data.Valid) :
    (validCandidate base hValid).datum.sourceEdgeIndex
        ((validCandidate base hValid).newSourceEdge base.deltaRepr) = base.kDelta := by
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge,
    LocalResolution.paste_newEdge_blockCard]
  have hRepr : (base.gaugedData.vertexPartition wall).Rel anchor.1
      ((base.gaugedData.vertexPartition wall).repr base.deltaRepr) := by
    rw [base.gaugedData_vertexPartition_wall]
    exact base.deltaRepr_wall.trans
      ((data.vertexPartition wall).rel_repr_right base.deltaRepr)
  rw [validCandidate_resolution_of_wall_rel base hValid _ hRepr]
  exact base.newEdgePartition_blockCard_delta

theorem validCandidate_newSourceEdge_index_hub (base : SimpleBase data star anchor)
    (hValid : data.Valid) :
    (validCandidate base hValid).datum.sourceEdgeIndex
          ((validCandidate base hValid).newSourceEdge base.hubSheet) + base.kDelta =
      base.kAlpha := by
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge,
    LocalResolution.paste_newEdge_blockCard]
  have hRepr : (base.gaugedData.vertexPartition wall).Rel anchor.1
      ((base.gaugedData.vertexPartition wall).repr base.hubSheet) := by
    rw [base.gaugedData_vertexPartition_wall]
    exact base.hubSheet_wall.trans
      ((data.vertexPartition wall).rel_repr_right base.hubSheet)
  rw [validCandidate_resolution_of_wall_rel base hValid _ hRepr]
  exact base.newEdgePartition_blockCard_hub

/-- **The resulting combinatorial type**, at the level of sheet classes: the
vertex `A_u` over the divalent point is exactly the class of `e_alpha`, and the
class `A'` of `e_delta` sits inside it as one class of the new edge and as a
whole vertex over `v`.  So the two stable edges through `A_u` are `h_alpha`
and `h_delta`; the classes of `e_beta` and `e_gamma` lie in the other vertex
`A_v` over `v`, so `h_beta` and `h_gamma` meet there. -/
theorem meeting_at_divalent_endpoint (base : SimpleBase data star anchor)
    (hValid : data.Valid) :
    ((validCandidate base hValid).resolution anchor.1).left.block base.hubSheet =
        base.alphaBlock ∧
      (base.gaugedData.edgePartition
          (directionEdge star base.alphaLabel)).block
            (Prescribed.occurrenceSheet base.alphaSurvivor) = base.alphaBlock ∧
      ((validCandidate base hValid).resolution anchor.1).newEdge.block
          base.deltaRepr = base.newDeltaBlock ∧
      ((validCandidate base hValid).resolution anchor.1).right.block
          base.deltaRepr = base.newDeltaBlock ∧
      (base.gaugedData.edgePartition
          (Prescribed.doubledEdge base.source)).block base.deltaRepr =
        base.newDeltaBlock ∧
      base.newDeltaBlock ⊆ base.alphaBlock ∧
      base.newBetaBlock ⊆
        ((validCandidate base hValid).resolution anchor.1).right.block
          base.hubSheet ∧
      base.newGammaBlock ⊆
        ((validCandidate base hValid).resolution anchor.1).right.block
          base.hubSheet := by
  have hAlphaBlock : (base.gaugedData.edgePartition
      (directionEdge star base.alphaLabel)).block
        (Prescribed.occurrenceSheet base.alphaSurvivor) = base.alphaBlock := by
    rw [base.gaugedData_edgePartition_alpha, ← base.alphaBlock_eq]
  rw [validCandidate_resolution_anchor base hValid]
  refine ⟨base.leftPartition_block_hub, hAlphaBlock,
    base.newEdgePartition_block_delta, base.rightPartition_block_delta,
    base.gaugedDoubled_block_delta, base.newDeltaBlock_subset_alpha, ?_, ?_⟩
  · rw [SimpleBase.selectedResolution_right, base.rightPartition_block_hub]
    exact base.newBetaBlock_subset_sdiff
  · rw [SimpleBase.selectedResolution_right, base.rightPartition_block_hub]
    intro sheet hSheet
    exact Finset.mem_sdiff.mpr ⟨base.newGammaBlock_subset_whole hSheet,
      base.newGammaBlock_not_mem_delta hSheet⟩

end Base

end DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleCandidate
