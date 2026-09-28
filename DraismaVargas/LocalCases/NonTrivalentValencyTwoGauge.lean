import DraismaVargas.LocalCases.BlockPreservingBranchSwap
import DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOne
import DraismaVargas.LocalCases.SheetRelabelStable

/-!
# Part II, valency two, Configuration A: the `t₃`-branch alignment gauge

Source: Vargas, Part II, Section 5.4, Configuration A of case `{v2-nd4}` (case
`{v2-nd4-t3}`), together with Draisma--Vargas Part I, Case `{w2-r2}`, Base I.

`NonTrivalentValencyTwoBaseOne` builds the Base I candidates of
Configuration A from the geometric receipt

```text
Aligned data star anchor :=
  (data.edgePartition (star.edge 1)).RefinesOnBlock
    (data.edgePartition (star.edge 0)) (data.vertexPartition wall) anchor.1
```

("above the anchor block the `t₃`-classes are the `t₂`-classes"), and proves
that `Aligned` implies the paper's numerical condition `|e_α| = |e_β|`
(`sourceEdgeIndex_eq_of_meet`), while its failure kills Base I
(`not_aligned_of_sourceEdgeIndex_ne`).  The converse is **false over a fixed
datum** -- which of Type I and Type II is realized is a property of the datum,
not of the four indices -- and **true after a block-preserving branch gauge**,
exactly as at valency four (`NonTrivalentValencyFourKZero.PrescribedPairing.gaugedData`).  This
module supplies that gauge.

## What is proved

* `exists_perm_matching_pair`, `exists_alignment_perm`: the finite gauge move.
  Two two-class decompositions of one wall block with matching class
  cardinalities are carried onto one another by a permutation that fixes the
  block's complement pointwise and stabilizes the block; after relabelling, the
  `t₃`-blocks inside the anchor are literally the `t₂`-blocks.  This is the
  transversal-matching companion of
  `BlockPreservingBranchSwap.exists_perm_image_inter_card_one`, which only
  produces a prescribed one-sheet overlap.
* `IsAlignmentGauge`, `gaugePerm`, `relabeling`, `gaugedData`, `gaugedAnchor`:
  the gauge applied on the `t₃` branch through
  `BlockPreservingBranchSwap.branchSwapOfPerm` at the far endpoint of
  `star.edge 1`.  `IsAlignmentGauge` carries the **prescribed cross pairing**
  as two sheet arguments `thickSheet`, `thinSheet` (the classes that are to
  meet at the first new vertex `A₁`), because the block alignment alone does
  not say which `t₃`-class lands on which `t₂`-class, and that choice is
  exactly the Type I / Type II dispatch; `gaugePerm_pairing` reads it back.
  `gaugePerm` is total: it is block-preserving for every datum
  (`gaugePerm_outside`, `gaugePerm_inside`, `gaugePerm_rel`) and aligning as
  soon as an aligning permutation exists, so `gaugedData` needs no hypothesis.
  The wall partition is untouched (`gaugedData_vertexPartition_wall`), the `t₂`
  partition is untouched (`gaugedData_edgePartition_zero`, through
  `TargetSeparation.edgeMoved_eq_false`, which is where
  `graph_connected target` and `genus target = 0` enter), and the `t₃`
  partition is relabelled (`gaugedData_edgePartition_one`).
* `gauged_aligned`: `Aligned gaugedData star gaugedAnchor` -- the receipt
  `NonTrivalentValencyTwoBaseOne` assumes, produced here from the two index
  equalities.
* `gaugedData_valid`, `survivorEquiv`, `survivors_gauged`,
  `directionSurvivors_gauged`, `activeTargets_gauged`,
  `gaugedSource`: the transport of `TwoBranchAnchor` and of Configuration A
  (`split_gauged`) across the gauge.  The gauge permutes sheets only inside the
  anchor block and only on the `t₃` side, so the whole survivor census is
  carried by the literal source-edge equivalence of the relabelling.
* `baseOneSetup_gauged`: the assembled `BaseOneSetup` at the gauged datum.
* `exists_gauged_candidate_of_contraction`: the incoming-cover form,
  `NonTrivalentValencyTwoBaseOne.exists_valid_candidate_of_contraction` with
  `Aligned` replaced by the two index equalities.  `data.Valid`, the
  contraction forest and `DanglingCompatible` are consumed exactly where
  `NonTrivalentValencyTwoBaseOne` consumes them
  (through `valid_contractDatum` and
  `NonTrivalentValencyTwoRigidity.twoBranchAnchor`); the target connectivity
  and genus the gauge needs come from the presentation through
  `graph_connected_contract` and `genus_contract`.
* `gauge_model_not_aligned`, `gauge_model_exists`: a literal four-sheet model
  in which the numerical condition holds, `Aligned` **fails**, and the gauge
  exists -- so the gauge is not cosmetic and `IsAlignmentGauge` is inhabited.
* `exists_baseOne_candidate_of_indices`: the Configuration A dispatcher of
  `NonTrivalentValencyTwoBaseOne`
  with the receipt `Aligned` replaced by the **numerical** condition
  `|e_α| = |e_β|`, `|e_γ| = |e_δ|`, over the gauged datum, returning the gauge
  itself (`gaugePerm` and the three partition identities relating `gaugedData`
  to `data`) so that later stages can follow the move.

## What is not proved here

* `nd(A) = 4` at the wall block, Configuration A (the `2 + 2` survivor split)
  and the classifier `TwoBranchAnchor` stay explicit hypotheses about the
  *incoming* datum, exactly as in `NonTrivalentValencyTwoCandidate` and
  `NonTrivalentValencyTwoBaseOne`; they are transported here, not produced.
* `graph_connected target`, `genus target = 0` and `data.Connected` are
  explicit: the first two separate the two star branches, the third is what
  makes pruning transport along a sheet relabelling.
* Nothing here proves stable types, rows, matrices or pencils.  Over the
  gauged datum this module produces, rows, descent and `rowEquiv` are in
  `NonTrivalentValencyTwoBaseOneRows` and `NonTrivalentValencyTwoBaseOneRowEquiv`,
  and the common minor and the exit in
  `NonTrivalentValencyTwoBaseOneRowDictionary` /
  `NonTrivalentValencyTwoBaseOneExit`.  The gauge exposed here is exactly what
  that row bookkeeping tracks.
* Change-minimality of the gauged datum is not asserted; only `Valid` is
  transported.

## Used by

The boundary dispatcher for Part II case `{v2-nd4}`, which must supply each
outgoing type once at every wall, and the valency-two row modules that follow
the move.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoGauge

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BlockPreservingBranchSwap
open DraismaVargas.LocalCases.GlobalM11Arbitrary
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOne
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.W3R1SourceProfile (survivors mem_survivors card_survivors)
open DraismaVargas.LocalCases.NonTrivalentValencyThreeAnchor (activeTargets
  mem_activeTargets)
open DraismaVargas.LocalCases.W4Assembly DraismaVargas.LocalCases.W4StableSource

/-! ## 0.  The finite transversal-matching gauge move -/

section Finite

/-- Two two-block decompositions of one finite set with matching sizes are
carried onto one another by a permutation fixing the complement. -/
theorem exists_perm_matching_pair {d : ℕ}
    (whole first second target₁ target₂ : Finset (Fin d))
    (hSourceUnion : first ∪ second = whole) (hSourceDisjoint : Disjoint first second)
    (hTargetUnion : target₁ ∪ target₂ = whole)
    (hTargetDisjoint : Disjoint target₁ target₂)
    (hCardOne : first.card = target₁.card) (hCardTwo : second.card = target₂.card) :
    ∃ permutation : Equiv.Perm (Fin d),
      (∀ sheet, sheet ∉ whole → permutation sheet = sheet) ∧
        (∀ sheet ∈ whole, permutation sheet ∈ whole) ∧
          first.image permutation = target₁ ∧ second.image permutation = target₂ := by
  classical
  have hFirstSub : first ⊆ whole := hSourceUnion ▸ Finset.subset_union_left
  have hSecondSub : second ⊆ whole := hSourceUnion ▸ Finset.subset_union_right
  have hTargetOneSub : target₁ ⊆ whole := hTargetUnion ▸ Finset.subset_union_left
  have hTargetTwoSub : target₂ ⊆ whole := hTargetUnion ▸ Finset.subset_union_right
  let matchOne := Finset.equivOfCardEq hCardOne
  let matchTwo := Finset.equivOfCardEq hCardTwo
  let move : Fin d → Fin d := fun sheet ↦
    if hOne : sheet ∈ first then (matchOne ⟨sheet, hOne⟩ : Fin d)
    else if hTwo : sheet ∈ second then (matchTwo ⟨sheet, hTwo⟩ : Fin d) else sheet
  have hMoveOne : ∀ sheet, ∀ hOne : sheet ∈ first,
      move sheet = (matchOne ⟨sheet, hOne⟩ : Fin d) := by
    intro sheet hOne
    simp only [move, dif_pos hOne]
  have hMoveTwo : ∀ sheet, sheet ∉ first → ∀ hTwo : sheet ∈ second,
      move sheet = (matchTwo ⟨sheet, hTwo⟩ : Fin d) := by
    intro sheet hOne hTwo
    simp only [move, dif_neg hOne, dif_pos hTwo]
  have hMoveNone : ∀ sheet, sheet ∉ first → sheet ∉ second → move sheet = sheet := by
    intro sheet hOne hTwo
    simp only [move, dif_neg hOne, dif_neg hTwo]
  have hIntoOne : ∀ sheet ∈ first, move sheet ∈ target₁ := by
    intro sheet hOne
    rw [hMoveOne sheet hOne]
    exact (matchOne ⟨sheet, hOne⟩).2
  have hIntoTwo : ∀ sheet, sheet ∉ first → sheet ∈ second → move sheet ∈ target₂ := by
    intro sheet hOne hTwo
    rw [hMoveTwo sheet hOne hTwo]
    exact (matchTwo ⟨sheet, hTwo⟩).2
  have hInjective : Function.Injective move := by
    intro left right hEq
    by_cases hLeftOne : left ∈ first
    · by_cases hRightOne : right ∈ first
      · have : matchOne ⟨left, hLeftOne⟩ = matchOne ⟨right, hRightOne⟩ := by
          apply Subtype.ext
          rw [← hMoveOne left hLeftOne, ← hMoveOne right hRightOne]
          exact hEq
        exact congrArg Subtype.val (matchOne.injective this)
      · by_cases hRightTwo : right ∈ second
        · exact absurd (hEq ▸ hIntoOne left hLeftOne)
            (Finset.disjoint_right.mp hTargetDisjoint (hIntoTwo right hRightOne hRightTwo))
        · rw [hMoveNone right hRightOne hRightTwo] at hEq
          exact absurd (hEq ▸ hIntoOne left hLeftOne)
            (fun hMem ↦ hRightOne (by
              have : right ∈ whole := hTargetOneSub hMem
              rcases Finset.mem_union.mp (hSourceUnion ▸ this) with h | h
              · exact h
              · exact absurd h hRightTwo))
    · by_cases hLeftTwo : left ∈ second
      · by_cases hRightOne : right ∈ first
        · exact absurd (hEq ▸ hIntoTwo left hLeftOne hLeftTwo)
            (Finset.disjoint_right.mp hTargetDisjoint.symm (hIntoOne right hRightOne))
        · by_cases hRightTwo : right ∈ second
          · have : matchTwo ⟨left, hLeftTwo⟩ = matchTwo ⟨right, hRightTwo⟩ := by
              apply Subtype.ext
              rw [← hMoveTwo left hLeftOne hLeftTwo, ← hMoveTwo right hRightOne hRightTwo]
              exact hEq
            exact congrArg Subtype.val (matchTwo.injective this)
          · rw [hMoveNone right hRightOne hRightTwo] at hEq
            have hRightWhole : right ∈ whole :=
              hTargetTwoSub (hEq ▸ hIntoTwo left hLeftOne hLeftTwo)
            rcases Finset.mem_union.mp (hSourceUnion ▸ hRightWhole) with h | h
            · exact absurd h hRightOne
            · exact absurd h hRightTwo
      · rw [hMoveNone left hLeftOne hLeftTwo] at hEq
        by_cases hRightOne : right ∈ first
        · have hLeftWhole : left ∈ whole := hTargetOneSub (hEq ▸ hIntoOne right hRightOne)
          rcases Finset.mem_union.mp (hSourceUnion ▸ hLeftWhole) with h | h
          · exact absurd h hLeftOne
          · exact absurd h hLeftTwo
        · by_cases hRightTwo : right ∈ second
          · have hLeftWhole : left ∈ whole :=
              hTargetTwoSub (hEq ▸ hIntoTwo right hRightOne hRightTwo)
            rcases Finset.mem_union.mp (hSourceUnion ▸ hLeftWhole) with h | h
            · exact absurd h hLeftOne
            · exact absurd h hLeftTwo
          · rw [hMoveNone right hRightOne hRightTwo] at hEq
            exact hEq
  let gauge : Equiv.Perm (Fin d) :=
    Equiv.ofBijective move (Finite.injective_iff_bijective.mp hInjective)
  have hApply : ∀ sheet, gauge sheet = move sheet := fun _ ↦ rfl
  refine ⟨gauge, ?_, ?_, ?_, ?_⟩
  · intro sheet hSheet
    rw [hApply]
    exact hMoveNone sheet (fun h ↦ hSheet (hFirstSub h)) (fun h ↦ hSheet (hSecondSub h))
  · intro sheet hSheet
    rw [hApply]
    by_cases hOne : sheet ∈ first
    · exact hTargetOneSub (hIntoOne sheet hOne)
    · by_cases hTwo : sheet ∈ second
      · exact hTargetTwoSub (hIntoTwo sheet hOne hTwo)
      · rw [hMoveNone sheet hOne hTwo]
        exact hSheet
  · refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro sheet hSheet
      obtain ⟨origin, hOrigin, rfl⟩ := Finset.mem_image.mp hSheet
      rw [hApply]
      exact hIntoOne origin hOrigin
    · rw [Finset.card_image_of_injective _ gauge.injective]
      exact le_of_eq hCardOne.symm
  · refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro sheet hSheet
      obtain ⟨origin, hOrigin, rfl⟩ := Finset.mem_image.mp hSheet
      rw [hApply]
      exact hIntoTwo origin (fun h ↦ Finset.disjoint_left.mp hSourceDisjoint h hOrigin) hOrigin
    · rw [Finset.card_image_of_injective _ gauge.injective]
      exact le_of_eq hCardTwo.symm


/-- **The `t₃`-branch alignment gauge, partition form.**  Two two-class
decompositions of one wall block, matched in size, are carried onto one another
by a permutation that fixes the block's complement pointwise. -/
theorem exists_alignment_perm {d : ℕ} (thin thick wall : SheetPartition d)
    (anchor : Fin d) (hThin : thin.Refines wall) (hThick : thick.Refines wall)
    (thinFirst thinSecond thickFirst thickSecond : Fin d)
    (hThinFirstWall : wall.Rel anchor thinFirst)
    (hThinSecondWall : wall.Rel anchor thinSecond)
    (hThickFirstWall : wall.Rel anchor thickFirst)
    (hThickSecondWall : wall.Rel anchor thickSecond)
    (hThinSplit : ¬ thin.Rel thinFirst thinSecond)
    (hThickSplit : ¬ thick.Rel thickFirst thickSecond)
    (hThinCover : ∀ sheet, wall.Rel anchor sheet →
      thin.Rel thinFirst sheet ∨ thin.Rel thinSecond sheet)
    (hThickCover : ∀ sheet, wall.Rel anchor sheet →
      thick.Rel thickFirst sheet ∨ thick.Rel thickSecond sheet)
    (hCardFirst : thin.blockCard thinFirst = thick.blockCard thickFirst)
    (hCardSecond : thin.blockCard thinSecond = thick.blockCard thickSecond) :
    ∃ gauge : Equiv.Perm (Fin d),
      (∀ sheet, sheet ∉ wall.block anchor → gauge sheet = sheet) ∧
        (∀ sheet ∈ wall.block anchor, gauge sheet ∈ wall.block anchor) ∧
          (∀ sheet, wall.Rel anchor sheet →
              (thin.relabel gauge).block sheet = thick.block sheet) ∧
            thick.Rel thickFirst (gauge thinFirst) ∧
              thick.Rel thickSecond (gauge thinSecond) := by
  classical
  have hBlockSub : ∀ fine : SheetPartition d, fine.Refines wall → ∀ representative,
      wall.Rel anchor representative → fine.block representative ⊆ wall.block anchor := by
    intro fine hRefines representative hWall sheet hSheet
    rw [SheetPartition.mem_block_iff] at hSheet ⊢
    exact hWall.trans (hRefines.rel hSheet)
  have hSplitDisjoint : ∀ fine : SheetPartition d, ∀ left right,
      ¬ fine.Rel left right → Disjoint (fine.block left) (fine.block right) := by
    intro fine left right hSplit
    refine Finset.disjoint_left.mpr fun sheet hLeft hRight ↦ hSplit ?_
    rw [SheetPartition.mem_block_iff] at hLeft hRight
    exact hLeft.trans hRight.symm
  have hSplitUnion : ∀ fine : SheetPartition d, fine.Refines wall → ∀ left right,
      wall.Rel anchor left → wall.Rel anchor right →
      (∀ sheet, wall.Rel anchor sheet → fine.Rel left sheet ∨ fine.Rel right sheet) →
      fine.block left ∪ fine.block right = wall.block anchor := by
    intro fine hRefines left right hLeft hRight hCover
    apply Finset.Subset.antisymm
    · exact Finset.union_subset (hBlockSub fine hRefines left hLeft)
        (hBlockSub fine hRefines right hRight)
    · intro sheet hSheet
      rw [SheetPartition.mem_block_iff] at hSheet
      rcases hCover sheet hSheet with hCase | hCase
      · exact Finset.mem_union_left _ ((fine.mem_block_iff _ _).mpr hCase)
      · exact Finset.mem_union_right _ ((fine.mem_block_iff _ _).mpr hCase)
  obtain ⟨gauge, hOutside, hInside, hImageFirst, hImageSecond⟩ :=
    exists_perm_matching_pair (wall.block anchor) (thin.block thinFirst)
      (thin.block thinSecond) (thick.block thickFirst) (thick.block thickSecond)
      (hSplitUnion thin hThin thinFirst thinSecond hThinFirstWall hThinSecondWall
        hThinCover)
      (hSplitDisjoint thin thinFirst thinSecond hThinSplit)
      (hSplitUnion thick hThick thickFirst thickSecond hThickFirstWall
        hThickSecondWall hThickCover)
      (hSplitDisjoint thick thickFirst thickSecond hThickSplit) hCardFirst hCardSecond
  refine ⟨gauge, hOutside, hInside, ?_, ?_, ?_⟩
  case refine_2 =>
    refine (thick.mem_block_iff _ _).mp ?_
    rw [← hImageFirst]
    exact Finset.mem_image.mpr ⟨thinFirst, thin.self_mem_block thinFirst, rfl⟩
  case refine_3 =>
    refine (thick.mem_block_iff _ _).mp ?_
    rw [← hImageSecond]
    exact Finset.mem_image.mpr ⟨thinSecond, thin.self_mem_block thinSecond, rfl⟩
  intro sheet hSheet
  have hSheetMem : sheet ∈ wall.block anchor := (wall.mem_block_iff anchor sheet).mpr hSheet
  have hOriginMem : gauge.symm sheet ∈ wall.block anchor := by
    by_contra hNot
    have hFixed := hOutside _ hNot
    rw [Equiv.apply_symm_apply] at hFixed
    exact hNot (hFixed ▸ hSheetMem)
  have hOriginWall : wall.Rel anchor (gauge.symm sheet) :=
    (wall.mem_block_iff anchor _).mp hOriginMem
  have hRestore : gauge (gauge.symm sheet) = sheet := gauge.apply_symm_apply sheet
  rcases hThinCover _ hOriginWall with hCase | hCase
  · have hBlock : (thin.relabel gauge).block sheet = thick.block thickFirst := by
      rw [← hRestore, thin.relabel_block gauge, ← thin.block_eq_of_rel hCase, hImageFirst]
    rw [hBlock]
    refine thick.block_eq_of_rel ((thick.mem_block_iff _ _).mp ?_)
    rw [← hImageFirst]
    exact Finset.mem_image.mpr ⟨gauge.symm sheet,
      (thin.mem_block_iff _ _).mpr hCase, hRestore⟩
  · have hBlock : (thin.relabel gauge).block sheet = thick.block thickSecond := by
      rw [← hRestore, thin.relabel_block gauge, ← thin.block_eq_of_rel hCase, hImageSecond]
    rw [hBlock]
    refine thick.block_eq_of_rel ((thick.mem_block_iff _ _).mp ?_)
    rw [← hImageSecond]
    exact Finset.mem_image.mpr ⟨gauge.symm sheet,
      (thin.mem_block_iff _ _).mpr hCase, hRestore⟩

end Finite

/-! ## 1.  The gauge at an actual divalent wall -/

section Wall

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (data : GluingDatum target degree)
    (vertex : data.SourceVertex) : DecidableEq (IncidentSourceEdge data vertex) :=
  Classical.decEq _

/-- Both occurrences of a divalent target star are incident to the wall. -/
theorem star_edge_incident (star : TwoStar target wall) (label : Fin 2) :
    ((star.edge label : target.V × target.V).1 = wall ∨
      (star.edge label : target.V × target.V).2 = wall) :=
  (GluingContraction.mem_incidentEdges_iff wall (star.edge label)).mp
    (star.edge_mem_incidentEdges label)

/-- **The defining property of the `t₃`-branch alignment gauge.**  It fixes
the anchor block's complement pointwise, stabilizes the anchor block, and after
relabelling carries every `t₃`-class inside the anchor onto the `t₂`-class of
the same sheet. -/
def IsAlignmentGauge (data : GluingDatum target degree) (star : TwoStar target wall)
    (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) (gauge : Equiv.Perm (Fin degree)) : Prop :=
  (∀ sheet, sheet ∉ (data.vertexPartition wall).block anchor.1 → gauge sheet = sheet) ∧
    (∀ sheet ∈ (data.vertexPartition wall).block anchor.1,
        gauge sheet ∈ (data.vertexPartition wall).block anchor.1) ∧
      (∀ sheet, (data.vertexPartition wall).Rel anchor.1 sheet →
          ((data.edgePartition (star.edge 1)).relabel gauge).block sheet =
            (data.edgePartition (star.edge 0)).block sheet) ∧
        (data.edgePartition (star.edge 0)).Rel thickSheet (gauge thinSheet)

/-- A block-preserving permutation is always available; it aligns the two
directions exactly when some permutation does. -/
private theorem exists_conditional_gauge (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) :
    ∃ gauge : Equiv.Perm (Fin degree),
      (∀ sheet, sheet ∉ (data.vertexPartition wall).block anchor.1 →
          gauge sheet = sheet) ∧
        (∀ sheet ∈ (data.vertexPartition wall).block anchor.1,
            gauge sheet ∈ (data.vertexPartition wall).block anchor.1) ∧
          ((∃ other, IsAlignmentGauge data star anchor thickSheet thinSheet other) →
            IsAlignmentGauge data star anchor thickSheet thinSheet gauge) := by
  by_cases hExists : ∃ other, IsAlignmentGauge data star anchor thickSheet thinSheet other
  · obtain ⟨other, hOutside, hInside, hBlock, hPair⟩ := hExists
    exact ⟨other, hOutside, hInside, fun _ ↦ ⟨hOutside, hInside, hBlock, hPair⟩⟩
  · exact ⟨Equiv.refl _, fun _ _ ↦ rfl, fun _ hSheet ↦ hSheet,
      fun hOther ↦ absurd hOther hExists⟩

/-- **The gauge permutation.**  Unconditionally block-preserving; aligning as
soon as the two index equalities of Part II's Base I condition hold. -/
noncomputable def gaugePerm (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) :
    Equiv.Perm (Fin degree) :=
  Classical.choose (exists_conditional_gauge data star anchor thickSheet thinSheet)

theorem gaugePerm_outside (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) (sheet : Fin degree)
    (hSheet : sheet ∉ (data.vertexPartition wall).block anchor.1) :
    gaugePerm data star anchor thickSheet thinSheet sheet = sheet :=
  (Classical.choose_spec
    (exists_conditional_gauge data star anchor thickSheet thinSheet)).1 sheet hSheet

theorem gaugePerm_inside (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) (sheet : Fin degree)
    (hSheet : sheet ∈ (data.vertexPartition wall).block anchor.1) :
    gaugePerm data star anchor thickSheet thinSheet sheet ∈
      (data.vertexPartition wall).block anchor.1 :=
  (Classical.choose_spec
    (exists_conditional_gauge data star anchor thickSheet thinSheet)).2.1 sheet hSheet

theorem gaugePerm_isAlignmentGauge (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree)
    (hExists : ∃ other, IsAlignmentGauge data star anchor thickSheet thinSheet other) :
    IsAlignmentGauge data star anchor thickSheet thinSheet
      (gaugePerm data star anchor thickSheet thinSheet) :=
  (Classical.choose_spec
    (exists_conditional_gauge data star anchor thickSheet thinSheet)).2.2 hExists

/-- The gauge realizes the **prescribed** cross pairing: the named `t₂` class
is the one the named `t₃` class lands in. -/
theorem gaugePerm_pairing (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree)
    (hExists : ∃ other, IsAlignmentGauge data star anchor thickSheet thinSheet other) :
    (data.edgePartition (star.edge 0)).Rel thickSheet
      (gaugePerm data star anchor thickSheet thinSheet thinSheet) :=
  (gaugePerm_isAlignmentGauge data star anchor thickSheet thinSheet hExists).2.2.2

theorem gaugePerm_rel (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) (sheet : Fin degree) :
    (data.vertexPartition wall).Rel
      (gaugePerm data star anchor thickSheet thinSheet sheet) sheet :=
  rel_of_stabilizes_block (data.vertexPartition wall) anchor.1
    (gaugePerm data star anchor thickSheet thinSheet)
    (gaugePerm_inside data star anchor thickSheet thinSheet)
    (gaugePerm_outside data star anchor thickSheet thinSheet) sheet

/-! ## 2.  The gauged datum -/

/-- The canonical branch relabelling: only the component behind the `t₃`
occurrence receives the alignment permutation. -/
noncomputable def relabeling (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) :
    data.SheetRelabeling :=
  branchSwapOfPerm data wall
    (TargetSeparation.farEndpoint wall (star.edge 1))
    (TargetSeparation.farEndpoint_ne (star_edge_incident star 1))
    (gaugePerm data star anchor thickSheet thinSheet)
    (gaugePerm_rel data star anchor thickSheet thinSheet)

/-- The datum after aligning the `t₃` branch with the `t₂` branch above the
anchor. -/
noncomputable def gaugedData (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) :
    GluingDatum target degree :=
  (relabeling data star anchor thickSheet thinSheet).apply

theorem gaugedData_vertexPartition_wall (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) :
    (gaugedData data star anchor thickSheet thinSheet).vertexPartition wall =
      data.vertexPartition wall := by
  unfold gaugedData relabeling
  apply branchSwapOfPerm_vertexPartition_wall

theorem gaugedData_edgePartition_one (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) :
    (gaugedData data star anchor thickSheet thinSheet).edgePartition (star.edge 1) =
      (data.edgePartition (star.edge 1)).relabel
        (gaugePerm data star anchor thickSheet thinSheet) := by
  apply branchSwapOfPerm_edgePartition_of_moved
  exact TargetSeparation.edgeMoved_self_eq_true (star_edge_incident star 1)

theorem gaugedData_edgePartition_zero (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    (gaugedData data star anchor thickSheet thinSheet).edgePartition (star.edge 0) =
      data.edgePartition (star.edge 0) := by
  apply branchSwapOfPerm_edgePartition_of_fixed
  apply TargetSeparation.edgeMoved_eq_false hConnected hGenus
    (star_edge_incident star 1) (star_edge_incident star 0)
  exact star.edge_injective.ne (by decide)

/-- The anchor block, read in the gauged datum. -/
noncomputable def gaugedAnchor (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) :
    WallBlock (gaugedData data star anchor thickSheet thinSheet) wall :=
  ⟨anchor.1, by
    rw [gaugedData_vertexPartition_wall data star anchor thickSheet thinSheet]
    exact anchor.2⟩

@[simp] theorem gaugedAnchor_val (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) :
    (gaugedAnchor data star anchor thickSheet thinSheet).1 = anchor.1 := rfl

theorem gaugedData_valid (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) (hValid : data.Valid) :
    (gaugedData data star anchor thickSheet thinSheet).Valid :=
  (relabeling data star anchor thickSheet thinSheet).valid hValid

/-! ## 3.  Producing the alignment from the two index equalities -/

variable {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall}

/-- Under Configuration A a named pair of distinct survivors of one direction
is the whole direction fibre. -/
theorem directionSurvivors_eq_pair {label : Fin 2}
    (hSplit : (directionSurvivors data star anchor label).card = 2)
    {first second : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hFirst : first ∈ directionSurvivors data star anchor label)
    (hSecond : second ∈ directionSurvivors data star anchor label)
    (hNe : first ≠ second) :
    directionSurvivors data star anchor label = {first, second} := by
  classical
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro edge hEdge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
    rcases hEdge with rfl | rfl
    · exact hFirst
    · exact hSecond
  · rw [hSplit, Finset.card_insert_of_notMem (by simp [hNe]), Finset.card_singleton]

/-- **Configuration A's `2 + 2` distribution read inside the anchor.**  The two
classes named by a pair of distinct survivors exhaust the anchor block. -/
theorem pair_cover (source : TwoBranchAnchor data star anchor) {label : Fin 2}
    (hSplit : (directionSurvivors data star anchor label).card = 2)
    {first second : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hFirst : first ∈ directionSurvivors data star anchor label)
    (hSecond : second ∈ directionSurvivors data star anchor label)
    (hNe : first ≠ second) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel anchor.1 sheet) :
    (data.edgePartition (star.edge label)).Rel (occurrenceSheet first) sheet ∨
      (data.edgePartition (star.edge label)).Rel (occurrenceSheet second) sheet := by
  classical
  have hMem : sheet ∈ (data.vertexPartition wall).block anchor.1 :=
    ((data.vertexPartition wall).mem_block_iff _ _).mpr hSheet
  rw [← biUnion_block_eq_wallBlock source label,
    directionSurvivors_eq_pair hSplit hFirst hSecond hNe] at hMem
  rw [Finset.biUnion_insert, Finset.singleton_biUnion] at hMem
  rcases Finset.mem_union.mp hMem with hCase | hCase
  · exact Or.inl ((SheetPartition.mem_block_iff _ _ _).mp hCase)
  · exact Or.inr ((SheetPartition.mem_block_iff _ _ _).mp hCase)

/-- **Part II's Base I condition in its geometric form.**  The prescribed cross pairing
`[e_α, e_β; e_γ, e_δ]` together with the two index equalities `|e_α| = |e_β|`
and `|e_γ| = |e_δ|` produces a block-preserving alignment gauge on the `t₃`
branch. -/
theorem exists_isAlignmentGauge (source : TwoBranchAnchor data star anchor)
    (hSplit : ∀ label : Fin 2, (directionSurvivors data star anchor label).card = 2)
    {thickFirst thickSecond thinFirst thinSecond :
      IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hThickFirst : thickFirst ∈ directionSurvivors data star anchor 0)
    (hThickSecond : thickSecond ∈ directionSurvivors data star anchor 0)
    (hThinFirst : thinFirst ∈ directionSurvivors data star anchor 1)
    (hThinSecond : thinSecond ∈ directionSurvivors data star anchor 1)
    (hThickNe : thickFirst ≠ thickSecond) (hThinNe : thinFirst ≠ thinSecond)
    (hIndexFirst : data.sourceEdgeIndex thickFirst.1 = data.sourceEdgeIndex thinFirst.1)
    (hIndexSecond : data.sourceEdgeIndex thickSecond.1 = data.sourceEdgeIndex thinSecond.1) :
    ∃ gauge : Equiv.Perm (Fin degree),
      IsAlignmentGauge data star anchor (occurrenceSheet thickFirst)
        (occurrenceSheet thinFirst) gauge := by
  obtain ⟨gauge, hOutside, hInside, hBlock, hPair, _⟩ :=
    exists_alignment_perm (data.edgePartition (star.edge 1))
      (data.edgePartition (star.edge 0)) (data.vertexPartition wall) anchor.1
      (star.edgePartition_refines_wall data 1) (star.edgePartition_refines_wall data 0)
      (occurrenceSheet thinFirst) (occurrenceSheet thinSecond)
      (occurrenceSheet thickFirst) (occurrenceSheet thickSecond)
      (occurrenceSheet_wall_rel thinFirst) (occurrenceSheet_wall_rel thinSecond)
      (occurrenceSheet_wall_rel thickFirst) (occurrenceSheet_wall_rel thickSecond)
      (not_rel_occurrenceSheet hThinFirst hThinSecond hThinNe)
      (not_rel_occurrenceSheet hThickFirst hThickSecond hThickNe)
      (fun sheet hSheet ↦ pair_cover source (hSplit 1) hThinFirst hThinSecond hThinNe hSheet)
      (fun sheet hSheet ↦ pair_cover source (hSplit 0) hThickFirst hThickSecond hThickNe hSheet)
      (by
        rw [← sourceEdgeIndex_eq_blockCard hThinFirst,
          ← sourceEdgeIndex_eq_blockCard hThickFirst, hIndexFirst])
      (by
        rw [← sourceEdgeIndex_eq_blockCard hThinSecond,
          ← sourceEdgeIndex_eq_blockCard hThickSecond, hIndexSecond])
  exact ⟨gauge, hOutside, hInside, hBlock, hPair⟩

/-- **The receipt of `NonTrivalentValencyTwoBaseOne`, produced.**  After the
gauge the `t₃`-classes
above the anchor are literally the `t₂`-classes. -/
theorem gauged_aligned (data : GluingDatum target degree) (star : TwoStar target wall)
    (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) (hConnected : graph_connected target)
    (hGenus : genus target = 0)
    (hExists : ∃ gauge : Equiv.Perm (Fin degree),
      IsAlignmentGauge data star anchor thickSheet thinSheet gauge) :
    Aligned (gaugedData data star anchor thickSheet thinSheet) star
      (gaugedAnchor data star anchor thickSheet thinSheet) := by
  have hAlign :=
    (gaugePerm_isAlignmentGauge data star anchor thickSheet thinSheet hExists).2.2.1
  show ∀ first second,
    ((gaugedData data star anchor thickSheet thinSheet).vertexPartition wall).Rel anchor.1 first →
      ((gaugedData data star anchor thickSheet thinSheet).edgePartition
          (star.edge 1)).Rel first second →
        ((gaugedData data star anchor thickSheet thinSheet).edgePartition
          (star.edge 0)).Rel first second
  intro first second hWall hFine
  rw [gaugedData_vertexPartition_wall data star anchor thickSheet thinSheet] at hWall
  rw [gaugedData_edgePartition_one data star anchor thickSheet thinSheet] at hFine
  rw [gaugedData_edgePartition_zero data star anchor thickSheet thinSheet hConnected hGenus]
  have hMem : second ∈ ((data.edgePartition (star.edge 1)).relabel
      (gaugePerm data star anchor thickSheet thinSheet)).block first :=
    (SheetPartition.mem_block_iff _ _ _).mpr hFine
  rw [hAlign first hWall] at hMem
  exact (SheetPartition.mem_block_iff _ _ _).mp hMem

/-! ## 4.  Transporting the survivor census across the gauge -/

theorem gauge_vertexPermutation_wall (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) :
    (relabeling data star anchor thickSheet thinSheet).vertexPermutation wall =
      Equiv.refl (Fin degree) := by
  show GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.vertexMoved wall _ _ wall)
    (gaugePerm data star anchor thickSheet thinSheet) = _
  rw [TargetBranchRegion.vertexMoved_wall]
  rfl

theorem gauged_sourceVertex_eq (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) :
    (relabeling data star anchor thickSheet thinSheet).sourceVertexEquiv
        (WallBlock.sourceVertex data wall anchor) =
      WallBlock.sourceVertex (gaugedData data star anchor thickSheet thinSheet) wall
        (gaugedAnchor data star anchor thickSheet thinSheet) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · show (relabeling data star anchor thickSheet thinSheet).vertexPermutation wall
        ((data.vertexPartition wall).repr anchor.1) =
      ((gaugedData data star anchor thickSheet thinSheet).vertexPartition wall).repr anchor.1
    rw [gauge_vertexPermutation_wall data star anchor thickSheet thinSheet,
      gaugedData_vertexPartition_wall data star anchor thickSheet thinSheet]
    rfl

/-- **The gauge's census map.**  Incident source occurrences at the anchor are
carried by the literal source-edge equivalence of the relabelling. -/
noncomputable def survivorEquiv (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) :
    IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor) ≃
      IncidentSourceEdge (gaugedData data star anchor thickSheet thinSheet)
        (WallBlock.sourceVertex (gaugedData data star anchor thickSheet thinSheet) wall
          (gaugedAnchor data star anchor thickSheet thinSheet)) :=
  (relabeling data star anchor thickSheet thinSheet).sourceEdgeEquiv.subtypeEquiv fun edge ↦ by
    rw [← gauged_sourceVertex_eq data star anchor thickSheet thinSheet]
    exact (SheetRelabelPruning.incident_sourceEdgeEquiv_iff
      (relabeling data star anchor thickSheet thinSheet) edge
      (WallBlock.sourceVertex data wall anchor)).symm

@[simp] theorem survivorEquiv_val (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)) :
    (survivorEquiv data star anchor thickSheet thinSheet edge).1 =
      (relabeling data star anchor thickSheet thinSheet).sourceEdgeEquiv edge.1 := rfl

/-- The gauge never changes which target occurrence a source occurrence lies
above. -/
@[simp] theorem survivorEquiv_target (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)) :
    (survivorEquiv data star anchor thickSheet thinSheet edge).1.1.1 = edge.1.1.1 := rfl

theorem survivorEquiv_index (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)) :
    (gaugedData data star anchor thickSheet thinSheet).sourceEdgeIndex
        (survivorEquiv data star anchor thickSheet thinSheet edge).1 =
      data.sourceEdgeIndex edge.1 :=
  SheetRelabelStable.sourceEdgeIndex_map (relabeling data star anchor thickSheet thinSheet) edge.1

theorem gauged_isDangling_iff (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree)
    (hConnected : data.Connected)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)) :
    IsDangling (gaugedData data star anchor thickSheet thinSheet)
        (survivorEquiv data star anchor thickSheet thinSheet edge).1 ↔
      IsDangling data edge.1 :=
  SheetRelabelPruning.isDangling_sourceEdgeEquiv_iff
    (relabeling data star anchor thickSheet thinSheet)
    hConnected edge.1

theorem mem_survivors_gauged (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree)
    (hConnected : data.Connected)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)) :
    survivorEquiv data star anchor thickSheet thinSheet edge ∈
        survivors (gaugedData data star anchor thickSheet thinSheet)
          (gaugedAnchor data star anchor thickSheet thinSheet) ↔
      edge ∈ survivors data anchor := by
  rw [mem_survivors, mem_survivors]
  exact not_congr (gauged_isDangling_iff data star anchor thickSheet thinSheet hConnected edge)

theorem survivors_gauged (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree)
    (hConnected : data.Connected) :
    survivors (gaugedData data star anchor thickSheet thinSheet)
        (gaugedAnchor data star anchor thickSheet thinSheet) =
      (survivors data anchor).image (survivorEquiv data star anchor thickSheet thinSheet) := by
  classical
  ext edge
  obtain ⟨edge, rfl⟩ := (survivorEquiv data star anchor thickSheet thinSheet).surjective edge
  rw [mem_survivors_gauged data star anchor thickSheet thinSheet hConnected]
  constructor
  · intro hSurvives
    exact Finset.mem_image.mpr ⟨edge, hSurvives, rfl⟩
  · intro hImage
    obtain ⟨other, hOther, hEq⟩ := Finset.mem_image.mp hImage
    exact (survivorEquiv data star anchor thickSheet thinSheet).injective hEq ▸ hOther

theorem directionSurvivors_gauged (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree)
    (hConnected : data.Connected) (label : Fin 2) :
    directionSurvivors (gaugedData data star anchor thickSheet thinSheet) star
        (gaugedAnchor data star anchor thickSheet thinSheet) label =
      (directionSurvivors data star anchor label).image
        (survivorEquiv data star anchor thickSheet thinSheet) := by
  classical
  ext edge
  obtain ⟨edge, rfl⟩ := (survivorEquiv data star anchor thickSheet thinSheet).surjective edge
  rw [mem_directionSurvivors, survivorEquiv_target,
    mem_survivors_gauged data star anchor thickSheet thinSheet hConnected]
  constructor
  · rintro ⟨hSurvives, hTarget⟩
    exact Finset.mem_image.mpr ⟨edge,
      (mem_directionSurvivors data star anchor label edge).mpr ⟨hSurvives, hTarget⟩, rfl⟩
  · intro hImage
    obtain ⟨other, hOther, hEq⟩ := Finset.mem_image.mp hImage
    have hSame : other = edge := (survivorEquiv data star anchor thickSheet thinSheet).injective hEq
    subst hSame
    exact (mem_directionSurvivors data star anchor label other).mp hOther

theorem card_directionSurvivors_gauged (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree)
    (hConnected : data.Connected) (label : Fin 2) :
    (directionSurvivors (gaugedData data star anchor thickSheet thinSheet) star
        (gaugedAnchor data star anchor thickSheet thinSheet) label).card =
      (directionSurvivors data star anchor label).card := by
  classical
  rw [directionSurvivors_gauged data star anchor thickSheet thinSheet hConnected label,
    Finset.card_image_of_injective _
      (survivorEquiv data star anchor thickSheet thinSheet).injective]

theorem activeTargets_gauged (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree)
    (hConnected : data.Connected) :
    activeTargets (gaugedData data star anchor thickSheet thinSheet)
        (gaugedAnchor data star anchor thickSheet thinSheet) =
      activeTargets data anchor := by
  classical
  unfold activeTargets
  rw [survivors_gauged data star anchor thickSheet thinSheet hConnected, Finset.image_image]
  rfl

theorem gauged_blockCard (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) :
    ((gaugedData data star anchor thickSheet thinSheet).vertexPartition wall).blockCard anchor.1 =
      (data.vertexPartition wall).blockCard anchor.1 := by
  rw [gaugedData_vertexPartition_wall data star anchor thickSheet thinSheet]

/-- **Configuration A survives the gauge.**  The `2 + 2` survivor split at the
anchor is unchanged. -/
theorem split_gauged (data : GluingDatum target degree) (star : TwoStar target wall)
    (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) (hConnected : data.Connected)
    (hSplit : ∀ label : Fin 2, (directionSurvivors data star anchor label).card = 2)
    (label : Fin 2) :
    (directionSurvivors (gaugedData data star anchor thickSheet thinSheet) star
      (gaugedAnchor data star anchor thickSheet thinSheet) label).card = 2 := by
  rw [card_directionSurvivors_gauged data star anchor thickSheet thinSheet hConnected label]
  exact hSplit label

/-- **The valency-two classifier survives the block-preserving branch gauge.**
Every field of `TwoBranchAnchor` is a count or an index sum over the survivor
census, and the census is carried by `survivorEquiv`. -/
theorem gaugedSource (data : GluingDatum target degree) (star : TwoStar target wall)
    (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) (hConnected : data.Connected)
    (source : TwoBranchAnchor data star anchor) :
    TwoBranchAnchor (gaugedData data star anchor thickSheet thinSheet) star
      (gaugedAnchor data star anchor thickSheet thinSheet) where
  active_all := by
    rw [activeTargets_gauged data star anchor thickSheet thinSheet hConnected]
    exact source.active_all
  distribution := by
    rcases source.distribution with hEven | ⟨tripled, hTripled, hSingle⟩
    · refine Or.inl fun label ↦ ?_
      rw [card_directionSurvivors_gauged data star anchor thickSheet thinSheet hConnected label]
      exact hEven label
    · refine Or.inr ⟨tripled, ?_, fun label hNe ↦ ?_⟩
      · rw [card_directionSurvivors_gauged data star anchor thickSheet thinSheet
          hConnected tripled]
        exact hTripled
      · rw [card_directionSurvivors_gauged data star anchor thickSheet thinSheet hConnected label]
        exact hSingle label hNe
  direction_index_sum := by
    intro label
    classical
    rw [directionSurvivors_gauged data star anchor thickSheet thinSheet hConnected label,
      Finset.sum_image (fun _ _ _ _ hEq ↦
        (survivorEquiv data star anchor thickSheet thinSheet).injective hEq)]
    rw [show ((gaugedAnchor data star anchor thickSheet thinSheet).1) = anchor.1 from rfl,
      gauged_blockCard data star anchor thickSheet thinSheet]
    rw [← source.direction_index_sum label]
    exact Finset.sum_congr rfl fun edge _ ↦ by
      rw [survivorEquiv_index data star anchor thickSheet thinSheet edge]
  survivor_index_sum := by
    classical
    rw [survivors_gauged data star anchor thickSheet thinSheet hConnected,
      Finset.sum_image (fun _ _ _ _ hEq ↦
        (survivorEquiv data star anchor thickSheet thinSheet).injective hEq)]
    rw [show ((gaugedAnchor data star anchor thickSheet thinSheet).1) = anchor.1 from rfl,
      gauged_blockCard data star anchor thickSheet thinSheet]
    rw [← source.survivor_index_sum]
    exact Finset.sum_congr rfl fun edge _ ↦ by
      rw [survivorEquiv_index data star anchor thickSheet thinSheet edge]

/-! ## 5.  Sheet bookkeeping and the Base I setup at the gauged datum -/

theorem gauge_edgePermutation_one (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) :
    (relabeling data star anchor thickSheet thinSheet).edgePermutation (star.edge 1) =
      gaugePerm data star anchor thickSheet thinSheet := by
  show GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.edgeMoved wall _ _ (star.edge 1))
    (gaugePerm data star anchor thickSheet thinSheet) = _
  rw [TargetSeparation.edgeMoved_self_eq_true (star_edge_incident star 1)]
  rfl

theorem gauge_edgePermutation_zero (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    (relabeling data star anchor thickSheet thinSheet).edgePermutation (star.edge 0) =
      Equiv.refl (Fin degree) := by
  show GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.edgeMoved wall _ _ (star.edge 0))
    (gaugePerm data star anchor thickSheet thinSheet) = _
  rw [TargetSeparation.edgeMoved_eq_false hConnected hGenus (star_edge_incident star 1)
    (star_edge_incident star 0) (star.edge_injective.ne (by decide))]
  rfl

theorem occurrenceSheet_survivorEquiv (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)) :
    occurrenceSheet (survivorEquiv data star anchor thickSheet thinSheet edge) =
      (relabeling data star anchor thickSheet thinSheet).edgePermutation edge.1.1.1
        (occurrenceSheet edge) := rfl

/-- The `t₂` side is untouched: a survivor above `t₂` keeps its sheet. -/
theorem occurrenceSheet_survivorEquiv_zero (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor 0) :
    occurrenceSheet (survivorEquiv data star anchor thickSheet thinSheet edge) =
      occurrenceSheet edge := by
  rw [occurrenceSheet_survivorEquiv, survivor_target hEdge,
    gauge_edgePermutation_zero data star anchor thickSheet thinSheet hConnected hGenus]
  rfl

/-- The `t₃` side moves by the gauge permutation. -/
theorem occurrenceSheet_survivorEquiv_one (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree)
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor 1) :
    occurrenceSheet (survivorEquiv data star anchor thickSheet thinSheet edge) =
      gaugePerm data star anchor thickSheet thinSheet (occurrenceSheet edge) := by
  rw [occurrenceSheet_survivorEquiv, survivor_target hEdge,
    gauge_edgePermutation_one data star anchor thickSheet thinSheet]

theorem mem_directionSurvivors_gauged (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) (hConnected : data.Connected) (label : Fin 2)
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor label) :
    survivorEquiv data star anchor thickSheet thinSheet edge ∈
      directionSurvivors (gaugedData data star anchor thickSheet thinSheet) star
        (gaugedAnchor data star anchor thickSheet thinSheet) label := by
  classical
  rw [directionSurvivors_gauged data star anchor thickSheet thinSheet hConnected label]
  exact Finset.mem_image.mpr ⟨edge, hEdge, rfl⟩

/-- **The Base I input of `NonTrivalentValencyTwoBaseOne`, assembled at the
gauged datum.** -/
theorem baseOneSetup_gauged (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hSourceConnected : data.Connected) (source : TwoBranchAnchor data star anchor)
    (hSplit : ∀ label : Fin 2, (directionSurvivors data star anchor label).card = 2)
    (hExists : ∃ other, IsAlignmentGauge data star anchor thickSheet thinSheet other) :
    BaseOneSetup (gaugedData data star anchor thickSheet thinSheet) star
      (gaugedAnchor data star anchor thickSheet thinSheet) where
  anchor_source :=
    gaugedSource data star anchor thickSheet thinSheet hSourceConnected source
  split := fun label ↦
    split_gauged data star anchor thickSheet thinSheet hSourceConnected hSplit label
  aligned :=
    gauged_aligned data star anchor thickSheet thinSheet hConnected hGenus hExists

/-! ## 6.  The numerical dispatcher -/

/-- **Part II, subcases `{v2-nd4-t3-k2=k4}` and `{v2-nd4-t3-k2=k3}`, Types I
and II, with the numerical hypothesis.**
Given the prescribed cross pairing `[e_α, e_β; e_γ, e_δ]` and *only* the
paper's index equalities `|e_α| = |e_β|`, `|e_γ| = |e_δ|`, the `t₃`-branch
gauge produces a datum carrying the Base I alignment of
`NonTrivalentValencyTwoBaseOne`, and over it the Base I candidate exists with
all of that module's exact block data.  The gauge is
returned with the candidate: the wall partition and the `t₂` partition are
literally unchanged, and the `t₃` partition is relabelled by `gaugePerm`. -/
theorem exists_baseOne_candidate_of_indices (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hValid : data.Valid) (source : TwoBranchAnchor data star anchor)
    (hSplit : ∀ label : Fin 2, (directionSurvivors data star anchor label).card = 2)
    (thickFirst thickSecond thinFirst thinSecond :
      IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor))
    (hThickFirst : thickFirst ∈ directionSurvivors data star anchor 0)
    (hThickSecond : thickSecond ∈ directionSurvivors data star anchor 0)
    (hThinFirst : thinFirst ∈ directionSurvivors data star anchor 1)
    (hThinSecond : thinSecond ∈ directionSurvivors data star anchor 1)
    (hThickNe : thickFirst ≠ thickSecond) (hThinNe : thinFirst ≠ thinSecond)
    (hIndexFirst : data.sourceEdgeIndex thickFirst.1 = data.sourceEdgeIndex thinFirst.1)
    (hIndexSecond : data.sourceEdgeIndex thickSecond.1 =
      data.sourceEdgeIndex thinSecond.1) :
    ∃ setup : BaseOneSetup
        (gaugedData data star anchor (occurrenceSheet thickFirst)
          (occurrenceSheet thinFirst)) star
        (gaugedAnchor data star anchor (occurrenceSheet thickFirst)
          (occurrenceSheet thinFirst)),
      ∃ outgoing : BalancedGlobal.Candidate target degree
          (gaugedData data star anchor (occurrenceSheet thickFirst)
            (occurrenceSheet thinFirst)) wall,
        outgoing.datum.Valid ∧
          outgoing.resolution anchor.1 = selectedResolution setup ∧
            (gaugedData data star anchor (occurrenceSheet thickFirst)
                (occurrenceSheet thinFirst)).vertexPartition wall =
              data.vertexPartition wall ∧
            (gaugedData data star anchor (occurrenceSheet thickFirst)
                (occurrenceSheet thinFirst)).edgePartition (star.edge 0) =
              data.edgePartition (star.edge 0) ∧
            (gaugedData data star anchor (occurrenceSheet thickFirst)
                (occurrenceSheet thinFirst)).edgePartition (star.edge 1) =
              (data.edgePartition (star.edge 1)).relabel
                (gaugePerm data star anchor (occurrenceSheet thickFirst)
                  (occurrenceSheet thinFirst)) ∧
            (data.edgePartition (star.edge 0)).Rel (occurrenceSheet thickFirst)
              (gaugePerm data star anchor (occurrenceSheet thickFirst)
                (occurrenceSheet thinFirst) (occurrenceSheet thinFirst)) ∧
            (data.edgePartition (star.edge 0)).Rel (occurrenceSheet thickSecond)
              (gaugePerm data star anchor (occurrenceSheet thickFirst)
                (occurrenceSheet thinFirst) (occurrenceSheet thinSecond)) ∧
            (outgoing.resolution anchor.1).right.blockCard
                (occurrenceSheet thickFirst) = data.sourceEdgeIndex thickFirst.1 ∧
            (outgoing.resolution anchor.1).right.blockCard
                (occurrenceSheet thickSecond) = data.sourceEdgeIndex thickSecond.1 ∧
            ¬(outgoing.resolution anchor.1).right.Rel (occurrenceSheet thickFirst)
              (occurrenceSheet thickSecond) ∧
            (outgoing.resolution anchor.1).left.blockCard setup.foldFirst = 2 ∧
            (∀ sheet, (data.vertexPartition wall).Rel anchor.1 sheet →
              outgoing.datum.sourceEdgeIndex (outgoing.newSourceEdge sheet) = 1) := by
  classical
  have hExists := exists_isAlignmentGauge source hSplit hThickFirst hThickSecond
    hThinFirst hThinSecond hThickNe hThinNe hIndexFirst hIndexSecond
  have hSourceConnected : data.Connected := hValid.1
  refine ⟨baseOneSetup_gauged data star anchor (occurrenceSheet thickFirst)
    (occurrenceSheet thinFirst) hConnected hGenus hSourceConnected source hSplit hExists, ?_⟩
  have hZeroSheet : ∀ edge ∈ directionSurvivors data star anchor 0,
      occurrenceSheet (survivorEquiv data star anchor (occurrenceSheet thickFirst)
        (occurrenceSheet thinFirst) edge) = occurrenceSheet edge :=
    fun _ hEdge ↦ occurrenceSheet_survivorEquiv_zero data star anchor _ _
      hConnected hGenus hEdge
  have hOneSheet : ∀ edge ∈ directionSurvivors data star anchor 1,
      occurrenceSheet (survivorEquiv data star anchor (occurrenceSheet thickFirst)
          (occurrenceSheet thinFirst) edge) =
        gaugePerm data star anchor (occurrenceSheet thickFirst)
          (occurrenceSheet thinFirst) (occurrenceSheet edge) :=
    fun _ hEdge ↦ occurrenceSheet_survivorEquiv_one data star anchor _ _ hEdge
  have hMeet : ((gaugedData data star anchor (occurrenceSheet thickFirst)
        (occurrenceSheet thinFirst)).edgePartition (star.edge 0)).Rel
      (occurrenceSheet (survivorEquiv data star anchor (occurrenceSheet thickFirst)
        (occurrenceSheet thinFirst) thickFirst))
      (occurrenceSheet (survivorEquiv data star anchor (occurrenceSheet thickFirst)
        (occurrenceSheet thinFirst) thinFirst)) := by
    rw [gaugedData_edgePartition_zero data star anchor _ _ hConnected hGenus,
      hZeroSheet thickFirst hThickFirst, hOneSheet thinFirst hThinFirst]
    exact gaugePerm_pairing data star anchor _ _ hExists
  obtain ⟨outgoing, hOutValid, hRes, _hIndexA, _hIndexB, hPartner, hCardFirst,
      hCardSecond, hNotRel, hFold, hNew⟩ :=
    exists_baseOne_candidate_of_prescribed
      (baseOneSetup_gauged data star anchor (occurrenceSheet thickFirst)
        (occurrenceSheet thinFirst) hConnected hGenus hSourceConnected source hSplit hExists)
      (gaugedData_valid data star anchor _ _ hValid)
      (mem_directionSurvivors_gauged data star anchor _ _ hSourceConnected 0 hThickFirst)
      (mem_directionSurvivors_gauged data star anchor _ _ hSourceConnected 0 hThickSecond)
      (mem_directionSurvivors_gauged data star anchor _ _ hSourceConnected 1 hThinFirst)
      (mem_directionSurvivors_gauged data star anchor _ _ hSourceConnected 1 hThinSecond)
      ((survivorEquiv data star anchor (occurrenceSheet thickFirst)
        (occurrenceSheet thinFirst)).injective.ne (Ne.symm hThickNe))
      ((survivorEquiv data star anchor (occurrenceSheet thickFirst)
        (occurrenceSheet thinFirst)).injective.ne (Ne.symm hThinNe)) hMeet
  rw [gaugedData_edgePartition_zero data star anchor _ _ hConnected hGenus,
    hZeroSheet thickSecond hThickSecond, hOneSheet thinSecond hThinSecond] at hPartner
  rw [hZeroSheet thickFirst hThickFirst,
    survivorEquiv_index data star anchor _ _ thickFirst] at hCardFirst
  rw [hZeroSheet thickSecond hThickSecond,
    survivorEquiv_index data star anchor _ _ thickSecond] at hCardSecond
  rw [hZeroSheet thickFirst hThickFirst, hZeroSheet thickSecond hThickSecond] at hNotRel
  refine ⟨outgoing, hOutValid, hRes,
    gaugedData_vertexPartition_wall data star anchor _ _,
    gaugedData_edgePartition_zero data star anchor _ _ hConnected hGenus,
    gaugedData_edgePartition_one data star anchor _ _,
    gaugePerm_pairing data star anchor _ _ hExists, hPartner, hCardFirst, hCardSecond,
    hNotRel, hFold, fun sheet hSheet ↦ hNew sheet ?_⟩
  show ((gaugedData data star anchor (occurrenceSheet thickFirst)
    (occurrenceSheet thinFirst)).vertexPartition wall).Rel anchor.1 sheet
  rw [gaugedData_vertexPartition_wall data star anchor (occurrenceSheet thickFirst)
    (occurrenceSheet thinFirst)]
  exact hSheet

end Wall

/-! ## 7.  The incoming-cover form -/

section Incoming

open GraphContraction GluingContraction ContractionFibre ContractionRamification
open FullDimensionalSource WallDegeneration

variable {target : CFGraph} {degree : ℕ}
variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **Base I from an incoming full-dimensional cover, with the numerical
hypothesis only.**  Everything except `hNd` (the anchor's surviving valency),
`hSplit` (Configuration A) and the prescribed cross pairing with its two index
equalities is supplied by the incoming cover and its contraction forest; the
receipt `Aligned` is not an input -- it is produced by the gauge,
whose effect on the contracted datum is returned alongside the candidate. -/
theorem exists_gauged_candidate_of_contraction
    (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hEdge : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    (hCompat : DanglingCompatible data hc hab hEdge)
    (star : W2R1Target.TwoStar (contract target hab hEdge) ⟨a, hab⟩)
    (anchorBlock : WallBlock (contractDatum data hc hab hEdge) ⟨a, hab⟩)
    (hNd : nonDanglingValency (contractDatum data hc hab hEdge)
      (WallBlock.sourceVertex (contractDatum data hc hab hEdge) ⟨a, hab⟩ anchorBlock) = 4)
    (hSplit : ∀ label : Fin 2,
      (directionSurvivors (contractDatum data hc hab hEdge) star anchorBlock label).card = 2)
    (thickFirst thickSecond thinFirst thinSecond :
      IncidentSourceEdge (contractDatum data hc hab hEdge)
        (WallBlock.sourceVertex (contractDatum data hc hab hEdge) ⟨a, hab⟩ anchorBlock))
    (hThickFirst : thickFirst ∈
      directionSurvivors (contractDatum data hc hab hEdge) star anchorBlock 0)
    (hThickSecond : thickSecond ∈
      directionSurvivors (contractDatum data hc hab hEdge) star anchorBlock 0)
    (hThinFirst : thinFirst ∈
      directionSurvivors (contractDatum data hc hab hEdge) star anchorBlock 1)
    (hThinSecond : thinSecond ∈
      directionSurvivors (contractDatum data hc hab hEdge) star anchorBlock 1)
    (hThickNe : thickFirst ≠ thickSecond) (hThinNe : thinFirst ≠ thinSecond)
    (hIndexFirst : (contractDatum data hc hab hEdge).sourceEdgeIndex thickFirst.1 =
      (contractDatum data hc hab hEdge).sourceEdgeIndex thinFirst.1)
    (hIndexSecond : (contractDatum data hc hab hEdge).sourceEdgeIndex thickSecond.1 =
      (contractDatum data hc hab hEdge).sourceEdgeIndex thinSecond.1) :
    ∃ setup : BaseOneSetup
        (gaugedData (contractDatum data hc hab hEdge) star anchorBlock
          (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)) star
        (gaugedAnchor (contractDatum data hc hab hEdge) star anchorBlock
          (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)),
      ∃ outgoing : BalancedGlobal.Candidate (contract target hab hEdge) degree
          (gaugedData (contractDatum data hc hab hEdge) star anchorBlock
            (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)) ⟨a, hab⟩,
        outgoing.datum.Valid ∧
          outgoing.resolution anchorBlock.1 = selectedResolution setup ∧
            (gaugedData (contractDatum data hc hab hEdge) star anchorBlock
                (occurrenceSheet thickFirst)
                (occurrenceSheet thinFirst)).vertexPartition ⟨a, hab⟩ =
              (contractDatum data hc hab hEdge).vertexPartition ⟨a, hab⟩ ∧
            (gaugedData (contractDatum data hc hab hEdge) star anchorBlock
                (occurrenceSheet thickFirst)
                (occurrenceSheet thinFirst)).edgePartition (star.edge 0) =
              (contractDatum data hc hab hEdge).edgePartition (star.edge 0) ∧
            (gaugedData (contractDatum data hc hab hEdge) star anchorBlock
                (occurrenceSheet thickFirst)
                (occurrenceSheet thinFirst)).edgePartition (star.edge 1) =
              ((contractDatum data hc hab hEdge).edgePartition (star.edge 1)).relabel
                (gaugePerm (contractDatum data hc hab hEdge) star anchorBlock
                  (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)) ∧
            (outgoing.resolution anchorBlock.1).left.blockCard setup.foldFirst = 2 ∧
            (∀ sheet, ((contractDatum data hc hab hEdge).vertexPartition ⟨a, hab⟩).Rel
                anchorBlock.1 sheet →
              outgoing.datum.sourceEdgeIndex (outgoing.newSourceEdge sheet) = 1) := by
  obtain ⟨setup, outgoing, hOutValid, hRes, hWall, hZero, hThird, _hPairFirst,
      _hPairSecond, _hCardFirst, _hCardSecond, _hNotRel, hFold, hNew⟩ :=
    exists_baseOne_candidate_of_indices (contractDatum data hc hab hEdge) star anchorBlock
      (graph_connected_contract target hab hEdge fd.targetConnected)
      ((genus_contract target hab hEdge).trans fd.targetGenus)
      (valid_contractDatum data hc hab hEdge hForest fd.valid)
      (NonTrivalentValencyTwoRigidity.twoBranchAnchor data fd hc hab hEdge hForest
        hCompat star anchorBlock hNd)
      hSplit thickFirst thickSecond thinFirst thinSecond hThickFirst hThickSecond
      hThinFirst hThinSecond hThickNe hThinNe hIndexFirst hIndexSecond
  exact ⟨setup, outgoing, hOutValid, hRes, hWall, hZero, hThird, hFold, hNew⟩

end Incoming

/-! ## 8.  Non-vacuity -/

section NonVacuity

/-- The literal wall partition of the misaligned model: one block carrying all
four sheets, so the anchor block is the whole local degree. -/
def gaugeWall : SheetPartition 4 := ⟨fun _ ↦ 0, by decide⟩

/-- The literal `t₂` partition inside the anchor: the classes `{0, 1}` and
`{2, 3}`, i.e. `k_α = k_γ = 2`. -/
def gaugeThick : SheetPartition 4 := ⟨fun i ↦ if i.val < 2 then 0 else 2, by decide⟩

/-- The literal `t₃` partition inside the anchor: the classes `{0, 2}` and
`{1, 3}`, i.e. `k_β = k_δ = 2`.  The paper's numerical condition
`|e_α| = |e_β|`, `|e_γ| = |e_δ|` holds, yet this datum is **not** aligned. -/
def gaugeThin : SheetPartition 4 := ⟨fun i ↦ if i.val % 2 = 0 then 0 else 1, by decide⟩

theorem gaugeThick_refines : gaugeThick.Refines gaugeWall := by decide

theorem gaugeThin_refines : gaugeThin.Refines gaugeWall := by decide

/-- The class sizes match on both sides of the prescribed cross pairing. -/
theorem gauge_model_cards :
    gaugeThin.blockCard 0 = gaugeThick.blockCard 0 ∧
      gaugeThin.blockCard 1 = gaugeThick.blockCard 2 := by decide

/-- **Why a gauge is needed at all.**  Over this fixed datum the numerical
condition holds but the receipt `Aligned` fails, so the converse of
`sourceEdgeIndex_eq_of_meet` is false without a branch move. -/
theorem gauge_model_not_aligned : ¬ gaugeThin.RefinesOnBlock gaugeThick gaugeWall 0 := by
  intro hAligned
  exact absurd (hAligned 0 2 (by decide) (by decide)) (by decide)

/-- **A literal inhabitant of the alignment gauge's defining property.**  The
same datum does carry a block-preserving permutation taking the `t₃`-classes
onto the `t₂`-classes, realizing the prescribed cross pairing `0 ↦ 0`,
`1 ↦ 2`.  These are exactly the four clauses of `IsAlignmentGauge`. -/
theorem gauge_model_exists :
    ∃ gauge : Equiv.Perm (Fin 4),
      (∀ sheet, sheet ∉ gaugeWall.block 0 → gauge sheet = sheet) ∧
        (∀ sheet ∈ gaugeWall.block 0, gauge sheet ∈ gaugeWall.block 0) ∧
          (∀ sheet, gaugeWall.Rel 0 sheet →
              (gaugeThin.relabel gauge).block sheet = gaugeThick.block sheet) ∧
            gaugeThick.Rel 0 (gauge 0) ∧ gaugeThick.Rel 2 (gauge 1) :=
  exists_alignment_perm gaugeThin gaugeThick gaugeWall 0 gaugeThin_refines
    gaugeThick_refines 0 1 0 2 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Configuration A, subcase `{v2-nd4-t3-k2=k4}`: `|A| = 4`,
`k = (2,2,2,2)`.  Both cross pairings satisfy the index condition, so after the
gauge both Base I morphisms exist: Types I and II. -/
theorem gauge_equal_witness :
    (2 + 2 : ℕ) = 4 ∧ (2 + 2 : ℕ) = 4 ∧ (2 : ℕ) = 2 ∧ (2 : ℕ) = 2 := by
  norm_num

/-- Configuration A, subcase `{v2-nd4-t3-k2=k3}`: `k = (1,1,2,2)`,
`|A| = 3`.  Exactly one cross pairing has equal indices on both sides, so the
gauge produces exactly one Base I morphism: Type I. -/
theorem gauge_semiEqual_witness :
    (1 + 2 : ℕ) = 3 ∧ (1 + 2 : ℕ) = 3 ∧ (1 : ℕ) = 1 ∧ (2 : ℕ) = 2 ∧
      (1 : ℕ) ≠ 2 := by
  norm_num

end NonVacuity

end DraismaVargas.LocalCases.NonTrivalentValencyTwoGauge
