import DraismaVargas.LocalCases.W4OutgoingStableRows

/-!
# The regrown column, and the presented W4 matrices are the honest ones

`W4OutgoingStableRows` produces the occurrence-induced stable-row equivalence
`stablePathEquiv` of each outgoing W4 candidate, the branch/row incidence
equivalence `equivalence`, and `matrix_retained`: every column of
`StableSourceMatrix.matrix` other than the regrown one is literally the incoming
wall column read through that equivalence.  Of the regrown column it settles
only the support (`mem_occurrences_new_iff`), and it says nothing about
`AuxR0SourceInput.presentedFamily`, whose matrices come from raw
`LengthMatrixPresentation.path` lists.

This module does both.

* `matrix_new` — **the regrown column, evaluated.**  On the outgoing image of
  an incoming stable row `path` it is
  `∑ 1 / |e(A₀)|`, summed over the old wall blocks `A₀` that actually regrow a
  surviving occurrence carrying `path`, where `e(A₀)` is that block's canonical
  incoming occurrence (`W4OutgoingStableRows.blockOldSourceEdge`): the first
  active branch of an opposite-side nd2 block, the isolated branch of an nd3
  block.  A dangling block and a same-side nd2 block regrow nothing.  The
  per-block reciprocal index is the source's own `1/|e'| = 1/|e_α|` of Case
  `{aux-r0}`, proved here as
  `sourceEdgeIndex_newSourceEdge_regrownSheet` from Equation (C) through
  `AuxR0Profile.nd2_active_blockCard` in the nd2 case and from the nd3 local
  resolution in the nd3 case.  The proof runs through the literal surviving
  occurrences: `occurrences_new` exhibits the regrown column's support as the
  image of the regrowing wall blocks under their canonical regrown sheet, with
  `newSourceEdge_eq_regrownSheet` showing that a surviving regrown occurrence
  is the canonical one of its own block.
* `presented_matrix_eq` — **the presented matrices are the natural stable-length
  matrices.** For every row label `row : Option target.edges` and column label
  `column`, the presented entry of `(input.presentedFamily data star)` at
  `(row, column)` equals `StableSourceMatrix.matrix` of the outgoing candidate
  at the stable row
  `stablePathEquiv input pairing (input.labelling.row.symm row)` and the column
  `occurrenceEquiv … column`. It goes **through the row equivalence**: the
  retained columns through `W4OutgoingStableRows.matrix_retained`, the regrown
  column through `matrix_new`. No cardinality bijection is used anywhere; in
  particular `mem_oldPath_iff`/`oldPath_toFinset_filter` and
  `mem_newSheets_iff`/`newSheets_toFinset` prove that the raw lists enumerate
  exactly the surviving occurrences of the corresponding literal stable row,
  once each, rather than merely having the right length.

`presentedFamily_matrix_eq` states the same thing directly for
`AuxR0SourceInput.presentedFamily`, `presented_matrix_submatrix` restates it as
one matrix equation, and `presented_matrix_some_eq` re-derives the presented family's
off-wall agreement from the honest columns instead of from the list
construction.

* `sum_matrix_new_eq_sum_wall` — **Equation (1) at one stable row, before
  cofactors.**  Summed over the three outgoing candidates, the regrown column
  of the natural stable-length matrix is the sum of the four incoming wall
  columns of the natural stable-length matrix of the wall datum.  Block by
  block this is exactly the source's Equations (w4-nd2) and (w4-nd3), proved
  here as `sum_pairings_blockColumnTerm_nd2` and
  `sum_pairings_blockColumnTerm_nd3`: an nd2 block regrows for exactly two of
  the three pairings (`card_separating_pairings`) and its two active branches
  share both row and index, while an nd3 block regrows for all three, each
  isolating a different active branch (`image_singletonLabel`,
  `singletonLabel_injective`).  The old-column side is matched block by block
  by `wallOccurrences_filter_eq`, which identifies the surviving wall
  occurrences of a row above a block with that block's canonical branch
  occurrences.

**Not proved here.**  Equation (1) itself: the cofactor weighting of
`sum_matrix_new_eq_sum_wall`, the vanishing `∑_{j=2}^{5} σ(j) = 0` of the wall
datum, and the assembly of a balanced family.  That is `W4CommonBalance`, on
the template of `M11CommonBalance` and `W3Nd2CommonBalance`.

**Which side of the wall bridge.**  Everything is stated for an
`AuxR0SourceInput`, exactly as `W4OutgoingSurvival` and `W4OutgoingStableRows`
are, and no `FullDimensionalSourcePresentation` appears; the two cannot share a
datum (`FullDimensionalSource.false_of_changeMinimal_auxR0SourceInput`), so
staying on this side is deliberate.  The hypotheses are the five fields of
`AuxR0SourceInput` and `[DecidableEq target.edges]`, nothing more, so every
statement applies to the inputs produced by
`AuxR0SourceInput.ofChangeMinimalExpansion`.

Source: Draisma--Vargas Part I, §5.2 (the induced labellings and
`lemma-limit-matrix-change`), Cases `{aux-r0-nd2}` and `{aux-r0-nd3}`, and case
`{w4}` (Equations (w4-nd2), (w4-nd3) and (1)).  Part I constructs the induced
labelling only in the downward direction and takes the identification of the
stable graphs for granted; `W4OutgoingStableRows` proves both as theorems.
-/

namespace DraismaVargas.LocalCases.W4OutgoingLimitMatrix

open DraismaVargas.Infrastructure TargetExpansion
open ResolutionM11 W4Assembly GlobalW4 W4StableSource W4StableGraph
open W4SourceClassification ResolutionAwayFromWall W4OutgoingSurvival
open StableGraphIncidence StablePathCount StableSourceMatrix
open W4OutgoingStableRows

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

section Candidate

variable {data : GluingDatum target degree}
  {star : W4TargetPairings.FourStar target wall}
  [DecidableEq target.edges]

/-- The sheet above which a wall block regrows, when it regrows at all: the
block's own anchor for an opposite-side nd2 block and the isolated branch's
honest active sheet for an nd3 block.  The value at a block that does not
regrow is never used. -/
noncomputable def regrownSheet (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) : Fin degree :=
  match input.blockPicture sourceBlock with
  | .dangling _ => sourceBlock.1
  | .nd2 _ _ => sourceBlock.1
  | .nd3 block picture => picture.activeSheet (block.singletonLabel pairing)

omit [DecidableEq target.edges] in
theorem regrownSheet_dangling (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall)
    (old_dangling : ∀ (edge : data.SourceEdge) (label : Fin 4),
      WallBlock.ofSheet data wall edge.1.2 = sourceBlock →
      star.edge label = edge.1.1 → IsDangling data edge)
    (hPicture : input.blockPicture sourceBlock = .dangling old_dangling) :
    regrownSheet input pairing sourceBlock = sourceBlock.1 := by
  rw [regrownSheet, hPicture]

omit [DecidableEq target.edges] in
theorem regrownSheet_nd2 (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) (block : Nd2Block)
    (picture : AuxR0Nd2Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd2 block picture) :
    regrownSheet input pairing sourceBlock = sourceBlock.1 := by
  rw [regrownSheet, hPicture]

omit [DecidableEq target.edges] in
theorem regrownSheet_nd3 (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) (block : Nd3Block)
    (picture : AuxR0Nd3Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd3 block picture) :
    regrownSheet input pairing sourceBlock =
      picture.activeSheet (block.singletonLabel pairing) := by
  rw [regrownSheet, hPicture]

omit [DecidableEq target.edges] in
/-- The canonical regrown sheet of a wall block lies in that block. -/
theorem rel_regrownSheet (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) :
    (data.vertexPartition wall).Rel sourceBlock.1
      (regrownSheet input pairing sourceBlock) := by
  cases hPicture : input.blockPicture sourceBlock with
  | dangling old_dangling =>
      rw [regrownSheet_dangling input pairing sourceBlock old_dangling hPicture]
      rfl
  | nd2 block picture =>
      rw [regrownSheet_nd2 input pairing sourceBlock block picture hPicture]
      rfl
  | nd3 block picture =>
      rw [regrownSheet_nd3 input pairing sourceBlock block picture hPicture]
      exact picture.active_sheet _ (block.singletonLabel_mem_activeLabels pairing)

omit [DecidableEq target.edges] in
theorem ofSheet_regrownSheet (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) :
    WallBlock.ofSheet data wall (regrownSheet input pairing sourceBlock) =
      sourceBlock :=
  WallBlock.ofSheet_eq_of_rel data wall sourceBlock _
    (rel_regrownSheet input pairing sourceBlock)

omit [DecidableEq target.edges] in
/-- The canonical incoming occurrence read off the regrown sheet is the one
read off the block itself. -/
theorem newOldSourceEdge_regrownSheet (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) :
    newOldSourceEdge input pairing (regrownSheet input pairing sourceBlock) =
      blockOldSourceEdge input pairing sourceBlock :=
  congrArg (blockOldSourceEdge input pairing)
    (ofSheet_regrownSheet input pairing sourceBlock)

/-! ## The incoming row carried by a block's regrown occurrence -/

/-- The incoming stable row carried by a wall block's regrown occurrence, when
that block regrows at all: `none` above a dangling block and above a same-side
nd2 block, where nothing regrows; the two active branches' common row above an
opposite-side nd2 block; the isolated branch's own row above an nd3 block. -/
noncomputable def blockRegrownRow (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) :
    Option (StablePath data) :=
  match input.blockPicture sourceBlock with
  | .dangling _ => none
  | .nd2 block picture =>
      if W4TargetPairings.Pairing.labelRight pairing block.first =
          W4TargetPairings.Pairing.labelRight pairing block.second then none
      else some (branchEdge data star block.first sourceBlock.1
        picture.first_survives).stablePath
  | .nd3 _block picture => some (nd3SingletonEdge picture pairing).stablePath

omit [DecidableEq target.edges] in
theorem blockRegrownRow_dangling (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall)
    (old_dangling : ∀ (edge : data.SourceEdge) (label : Fin 4),
      WallBlock.ofSheet data wall edge.1.2 = sourceBlock →
      star.edge label = edge.1.1 → IsDangling data edge)
    (hPicture : input.blockPicture sourceBlock = .dangling old_dangling) :
    blockRegrownRow input pairing sourceBlock = none := by
  rw [blockRegrownRow, hPicture]

omit [DecidableEq target.edges] in
theorem blockRegrownRow_nd2_same (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) (block : Nd2Block)
    (picture : AuxR0Nd2Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd2 block picture)
    (hSame : W4TargetPairings.Pairing.labelRight pairing block.first =
      W4TargetPairings.Pairing.labelRight pairing block.second) :
    blockRegrownRow input pairing sourceBlock = none := by
  rw [blockRegrownRow, hPicture]
  exact if_pos hSame

omit [DecidableEq target.edges] in
theorem blockRegrownRow_nd2_ne (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) (block : Nd2Block)
    (picture : AuxR0Nd2Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd2 block picture)
    (hNe : W4TargetPairings.Pairing.labelRight pairing block.first ≠
      W4TargetPairings.Pairing.labelRight pairing block.second) :
    blockRegrownRow input pairing sourceBlock =
      some (branchEdge data star block.first sourceBlock.1
        picture.first_survives).stablePath := by
  rw [blockRegrownRow, hPicture]
  exact if_neg hNe

omit [DecidableEq target.edges] in
theorem blockRegrownRow_nd3 (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) (block : Nd3Block)
    (picture : AuxR0Nd3Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd3 block picture) :
    blockRegrownRow input pairing sourceBlock =
      some (nd3SingletonEdge picture pairing).stablePath := by
  rw [blockRegrownRow, hPicture]

/-- **A block regrows a surviving occurrence exactly when it carries a
row.**  This direction is the one used to move from the block index to the
literal outgoing occurrence. -/
theorem regrownSheet_survives (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall)
    (path : StablePath data)
    (hRow : blockRegrownRow input pairing sourceBlock = some path) :
    ¬ IsDangling (member input pairing).datum
      ((member input pairing).newSourceEdge
        (regrownSheet input pairing sourceBlock)) := by
  cases hPicture : input.blockPicture sourceBlock with
  | dangling old_dangling =>
      rw [blockRegrownRow_dangling input pairing sourceBlock old_dangling
        hPicture] at hRow
      exact absurd hRow (by simp)
  | nd2 block picture =>
      by_cases hSame : W4TargetPairings.Pairing.labelRight pairing block.first =
          W4TargetPairings.Pairing.labelRight pairing block.second
      · rw [blockRegrownRow_nd2_same input pairing sourceBlock block picture
          hPicture hSame] at hRow
        exact absurd hRow (by simp)
      · rw [regrownSheet_nd2 input pairing sourceBlock block picture hPicture]
        exact nd2_new_survives_of_ne input pairing sourceBlock block picture
          hPicture hSame
  | nd3 block picture =>
      rw [regrownSheet_nd3 input pairing sourceBlock block picture hPicture]
      exact nd3_new_survives_activeSheet input pairing sourceBlock block picture
        hPicture

/-- **The row a block's surviving regrown occurrence actually sits on.**  It is
the row of that block's canonical incoming occurrence, as the reverse
assignment of `W4OutgoingStableRows` computes it. -/
theorem blockRegrownRow_eq_some (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall)
    (hSurvives : ¬ IsDangling (member input pairing).datum
      ((member input pairing).newSourceEdge
        (regrownSheet input pairing sourceBlock))) :
    blockRegrownRow input pairing sourceBlock =
      some (newOldEdge input pairing (regrownSheet input pairing sourceBlock)
        hSurvives).stablePath := by
  have hValue : (newOldEdge input pairing
      (regrownSheet input pairing sourceBlock) hSurvives).1 =
      blockOldSourceEdge input pairing sourceBlock :=
    newOldSourceEdge_regrownSheet input pairing sourceBlock
  cases hPicture : input.blockPicture sourceBlock with
  | dangling old_dangling =>
      exact absurd (dangling_new_dangles input pairing sourceBlock old_dangling
        hPicture _ (rel_regrownSheet input pairing sourceBlock)) hSurvives
  | nd2 block picture =>
      by_cases hSame : W4TargetPairings.Pairing.labelRight pairing block.first =
          W4TargetPairings.Pairing.labelRight pairing block.second
      · exact absurd (nd2_new_dangles_of_same input pairing sourceBlock block
          picture hPicture hSame _
          (rel_regrownSheet input pairing sourceBlock)) hSurvives
      · rw [blockRegrownRow_nd2_ne input pairing sourceBlock block picture
          hPicture hSame]
        refine congrArg some (congrArg NonDanglingEdge.stablePath
          (Subtype.ext ?_)).symm
        rw [hValue]
        exact blockOldSourceEdge_nd2 input pairing sourceBlock block picture
          hPicture
  | nd3 block picture =>
      rw [blockRegrownRow_nd3 input pairing sourceBlock block picture hPicture]
      refine congrArg some (congrArg NonDanglingEdge.stablePath
        (Subtype.ext ?_)).symm
      rw [hValue]
      exact blockOldSourceEdge_nd3 input pairing sourceBlock block picture
        hPicture

/-! ## Every surviving regrown occurrence is a block's canonical one -/

/-- A regrown occurrence is classified by the old wall block of its sheet. -/
theorem ofSheet_newSourceEdge (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sheet : Fin degree) :
    WallBlock.ofSheet data wall
        ((member input pairing).newSourceEdge sheet).1.2 =
      WallBlock.ofSheet data wall sheet :=
  PairingReceipts.wallBlock_newSourceEdge (inputReceipts input pairing) sheet

/-- **A surviving regrown occurrence is the canonical regrown occurrence of its
own old wall block.**  Above an opposite-side nd2 block the regrown edge keeps
the whole block; above an nd3 block survival forces the sheet into the isolated
branch's own edge class. -/
theorem newSourceEdge_eq_regrownSheet (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (member input pairing).datum
      ((member input pairing).newSourceEdge sheet)) :
    (member input pairing).newSourceEdge
        (regrownSheet input pairing (WallBlock.ofSheet data wall sheet)) =
      (member input pairing).newSourceEdge sheet := by
  have hSheet := rel_ofSheet data wall sheet
  cases hPicture : input.blockPicture (WallBlock.ofSheet data wall sheet) with
  | dangling old_dangling =>
      exact absurd (dangling_new_dangles input pairing _ old_dangling hPicture
        sheet hSheet) hSurvives
  | nd2 block picture =>
      by_cases hSame : W4TargetPairings.Pairing.labelRight pairing block.first =
          W4TargetPairings.Pairing.labelRight pairing block.second
      · exact absurd (nd2_new_dangles_of_same input pairing _ block picture
          hPicture hSame sheet hSheet) hSurvives
      · have hPattern : input.activeProfile.blockPattern
            (WallBlock.ofSheet data wall sheet).1 = .nd2 block :=
          blockPattern_eq_nd2_of_picture input _ block picture hPicture
        rw [regrownSheet_nd2 input pairing _ block picture hPicture]
        refine (newSourceEdge_eq_iff (inputReceipts input pairing) _ sheet).mpr ?_
        rw [wholeResolution_newEdge_rel, (WallBlock.ofSheet data wall sheet).2,
          nd2_ne_newEdge data star input.activeProfile.blockPattern pairing _
            block hPattern hSame]
        exact hSheet
  | nd3 block picture =>
      have hPattern : input.activeProfile.blockPattern
          (WallBlock.ofSheet data wall sheet).1 = .nd3 block :=
        blockPattern_eq_nd3_of_picture input _ block picture hPicture
      have hRel := (nd3_new_survives_iff input pairing _ block picture hPicture
        sheet hSheet).mp hSurvives
      have hRepr : (data.vertexPartition wall).repr
          (picture.activeSheet (block.singletonLabel pairing)) =
            (WallBlock.ofSheet data wall sheet).1 :=
        ((picture.active_sheet _
          (block.singletonLabel_mem_activeLabels pairing)).symm.trans
            (WallBlock.ofSheet data wall sheet).2)
      rw [regrownSheet_nd3 input pairing _ block picture hPicture]
      refine (newSourceEdge_eq_iff (inputReceipts input pairing) _ sheet).mpr ?_
      rw [wholeResolution_newEdge_rel, hRepr,
        nd3_newEdge data star input.activeProfile.blockPattern pairing _ block
          hPattern]
      exact hRel.symm

/-- The wall blocks that regrow an occurrence on one incoming stable row. -/
noncomputable def regrowingBlocks (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (path : StablePath data) :
    Finset (WallBlock data wall) := by
  classical
  exact Finset.univ.filter fun sourceBlock ↦
    blockRegrownRow input pairing sourceBlock = some path

omit [DecidableEq target.edges] in
theorem mem_regrowingBlocks (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (path : StablePath data)
    (sourceBlock : WallBlock data wall) :
    sourceBlock ∈ regrowingBlocks input pairing path ↔
      blockRegrownRow input pairing sourceBlock = some path := by
  classical
  simp [regrowingBlocks]

/-- Distinct wall blocks regrow distinct occurrences. -/
theorem newSourceEdge_regrownSheet_injective (input : AuxR0SourceInput data star)
    (pairing : Fin 3) :
    Function.Injective fun sourceBlock : WallBlock data wall ↦
      (member input pairing).newSourceEdge
        (regrownSheet input pairing sourceBlock) := by
  intro first second hEq
  have hBlock := congrArg (fun edge : (member input pairing).datum.SourceEdge ↦
    WallBlock.ofSheet data wall edge.1.2) hEq
  simp only [ofSheet_newSourceEdge, ofSheet_regrownSheet] at hBlock
  exact hBlock

/-! ## The regrown column -/

/-- **The dilation index of a block's regrown occurrence is the index of that
block's canonical incoming occurrence.**  This is the source's own
`|e'| = |e_alpha|`: above an opposite-side nd2 block the regrown edge keeps the
whole old wall block, which Equation (C) makes equal to each active branch's
class; above an nd3 block it keeps the isolated branch's own class. -/
theorem sourceEdgeIndex_newSourceEdge_regrownSheet
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (path : StablePath data)
    (hRow : blockRegrownRow input pairing sourceBlock = some path) :
    (member input pairing).datum.sourceEdgeIndex
        ((member input pairing).newSourceEdge
          (regrownSheet input pairing sourceBlock)) =
      data.sourceEdgeIndex (blockOldSourceEdge input pairing sourceBlock) := by
  cases hPicture : input.blockPicture sourceBlock with
  | dangling old_dangling =>
      rw [blockRegrownRow_dangling input pairing sourceBlock old_dangling
        hPicture] at hRow
      exact absurd hRow (by simp)
  | nd2 block picture =>
      by_cases hSame : W4TargetPairings.Pairing.labelRight pairing block.first =
          W4TargetPairings.Pairing.labelRight pairing block.second
      · rw [blockRegrownRow_nd2_same input pairing sourceBlock block picture
          hPicture hSame] at hRow
        exact absurd hRow (by simp)
      · have hPattern : input.activeProfile.blockPattern sourceBlock.1 =
            .nd2 block :=
          blockPattern_eq_nd2_of_picture input sourceBlock block picture hPicture
        have hCard := (input.auxProfile.nd2_active_blockCard sourceBlock.1 block
          hPattern sourceBlock.1 rfl).1
        rw [regrownSheet_nd2 input pairing sourceBlock block picture hPicture,
          blockOldSourceEdge_nd2 input pairing sourceBlock block picture hPicture]
        refine PairingReceipts.sourceEdgeIndex_newSourceEdge_nd2_eq_first
          (inputReceipts input pairing) sourceBlock.1 block ?_ hSame hCard
        rw [sourceBlock.2]
        exact hPattern
  | nd3 block picture =>
      have hPattern : input.activeProfile.blockPattern sourceBlock.1 =
          .nd3 block :=
        blockPattern_eq_nd3_of_picture input sourceBlock block picture hPicture
      have hRepr : (data.vertexPartition wall).repr
          (picture.activeSheet (block.singletonLabel pairing)) = sourceBlock.1 :=
        (picture.active_sheet _
          (block.singletonLabel_mem_activeLabels pairing)).symm.trans sourceBlock.2
      rw [regrownSheet_nd3 input pairing sourceBlock block picture hPicture,
        blockOldSourceEdge_nd3 input pairing sourceBlock block picture hPicture]
      refine PairingReceipts.sourceEdgeIndex_newSourceEdge_nd3_eq_old
        (inputReceipts input pairing) _ block ?_
      rw [hRepr]
      exact hPattern

/-- **The support of the regrown column, block by block.**  Every surviving
outgoing occurrence over the regrown wall edge whose outgoing row is the image
of `path` is the canonical regrown occurrence of exactly one old wall block,
and that block is one that carries `path` on its canonical incoming
occurrence. -/
theorem occurrences_new (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (path : StablePath data) :
    occurrences (member input pairing).datum
        (stablePathEquiv input pairing path)
        (occurrenceEquiv target wall (member input pairing).right none) =
      (regrowingBlocks input pairing path).image fun sourceBlock ↦
        (member input pairing).newSourceEdge
          (regrownSheet input pairing sourceBlock) := by
  classical
  ext edge
  rw [mem_occurrences_new_iff, Finset.mem_image]
  constructor
  · rintro ⟨sheet, hSurvives, rfl, hRow⟩
    have hSame := newSourceEdge_eq_regrownSheet input pairing sheet hSurvives
    have hSurvives' : ¬ IsDangling (member input pairing).datum
        ((member input pairing).newSourceEdge
          (regrownSheet input pairing (WallBlock.ofSheet data wall sheet))) := by
      rw [hSame]; exact hSurvives
    refine ⟨WallBlock.ofSheet data wall sheet, ?_, hSame⟩
    rw [mem_regrowingBlocks,
      blockRegrownRow_eq_some input pairing _ hSurvives', ← hRow]
    refine congrArg some (congrArg NonDanglingEdge.stablePath (Subtype.ext ?_))
    show newOldSourceEdge input pairing
        (regrownSheet input pairing (WallBlock.ofSheet data wall sheet)) =
      newOldSourceEdge input pairing sheet
    rw [newOldSourceEdge_regrownSheet]
    rfl
  · rintro ⟨sourceBlock, hBlock, rfl⟩
    rw [mem_regrowingBlocks] at hBlock
    have hSurvives := regrownSheet_survives input pairing sourceBlock path hBlock
    exact ⟨regrownSheet input pairing sourceBlock, hSurvives, rfl,
      Option.some.inj ((blockRegrownRow_eq_some input pairing sourceBlock
        hSurvives).symm.trans hBlock)⟩

/-- **The regrown column of an outgoing W4 candidate, evaluated.**  On the
outgoing image of an incoming stable row it is the sum, over the old wall
blocks that actually regrow a surviving occurrence carrying that row, of the
reciprocal dilation index of that block's canonical incoming occurrence.  A
dangling block and a same-side nd2 block contribute nothing; an opposite-side
nd2 block contributes `1/|e_alpha|` and an nd3 block `1/|e_alpha|` for its own
isolated branch, which is the source's per-block term in Equations (w4-nd2)
and (w4-nd3) with the row cofactor stripped off. -/
theorem matrix_new (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (path : StablePath data) :
    matrix (member input pairing).datum (stablePathEquiv input pairing path)
        (occurrenceEquiv target wall (member input pairing).right none) =
      ∑ sourceBlock ∈ regrowingBlocks input pairing path,
        (1 : ℚ) /
          data.sourceEdgeIndex (blockOldSourceEdge input pairing sourceBlock) := by
  classical
  unfold matrix
  rw [occurrences_new, Finset.sum_image
    fun first _ second _ hEq ↦ newSourceEdge_regrownSheet_injective input pairing hEq]
  refine Finset.sum_congr rfl fun sourceBlock hBlock ↦ ?_
  rw [sourceEdgeIndex_newSourceEdge_regrownSheet input pairing sourceBlock path
    ((mem_regrowingBlocks input pairing path sourceBlock).mp hBlock)]

/-! ## The presented path lists of `AuxR0SourceInput.presentedFamily`

The presented matrices are built from raw `List` data.  Nothing in the
construction says that those lists enumerate surviving occurrences, or that
their row index is a stable row of the outgoing datum.  The lemmas below read
the lists back and then identify the presented matrix with the natural one.
-/

/-- The presented length-matrix presentation of one actual member, with its
type ascribed through `member`. -/
noncomputable def presented (input : AuxR0SourceInput data star)
    (pairing : Fin 3) :
    (member input pairing).datum.LengthMatrixPresentation
      (Option target.edges) :=
  (input.presentedFamily data star).presentation pairing

theorem presented_eq (input : AuxR0SourceInput data star) (pairing : Fin 3) :
    presented input pairing =
      (input.presentedFamily data star).presentation pairing := rfl

theorem presented_targetEdge (input : AuxR0SourceInput data star)
    (pairing : Fin 3) :
    (presented input pairing).targetEdge =
      occurrenceEquiv target wall (member input pairing).right := rfl

theorem presented_path (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (row : Option target.edges) :
    (presented input pairing).path row =
      (input.family.assignment.oldPath row).map
          (member input pairing).oldSourceEdge ++
        (input.family.assignment.newSheets pairing row).map
          (member input pairing).newSourceEdge := rfl

omit [DecidableEq target.edges] in
/-- The row label of an old occurrence is its literal stable row. -/
theorem oldRowOf_eq_some_iff (labelling : StablePathLabelling data)
    (edge : data.SourceEdge) (row : Option target.edges) :
    labelling.oldRowOf edge = some row ↔
      ∃ hSurvives : ¬ IsDangling data edge,
        NonDanglingEdge.stablePath (⟨edge, hSurvives⟩ : NonDanglingEdge data) =
          labelling.row.symm row := by
  constructor
  · intro hEq
    by_cases hDangling : IsDangling data edge
    · rw [(labelling.oldRowOf_eq_none_iff edge).2 hDangling] at hEq
      exact absurd hEq (by simp)
    · refine ⟨hDangling, ?_⟩
      rw [labelling.oldRowOf_eq_some ⟨edge, hDangling⟩] at hEq
      exact (Equiv.eq_symm_apply _).2 (Option.some.inj hEq)
  · rintro ⟨hSurvives, hPath⟩
    rw [labelling.oldRowOf_eq_some ⟨edge, hSurvives⟩, hPath]
    simp

omit [DecidableEq target.edges] in
theorem assignment_oldRowOf (input : AuxR0SourceInput data star)
    (edge : data.SourceEdge) :
    input.family.assignment.oldRowOf edge = input.labelling.oldRowOf edge := rfl

theorem mem_oldPath_iff (input : AuxR0SourceInput data star)
    (row : Option target.edges) (edge : data.SourceEdge) :
    edge ∈ input.family.assignment.oldPath row ↔
      input.labelling.oldRowOf edge = some row := by
  classical
  simp [W4StablePathAssignment.PathAssignment.oldPath, assignment_oldRowOf,
    eq_comm]

theorem oldPath_nodup (input : AuxR0SourceInput data star)
    (row : Option target.edges) :
    (input.family.assignment.oldPath row).Nodup := by
  classical
  refine List.Nodup.filterMap ?_ (Finset.univ.nodup_toList)
  intro first second edge hFirst hSecond
  have hFirstEq : first = edge := by
    by_cases hRow : input.family.assignment.oldRowOf first = some row
    · simpa [hRow] using hFirst
    · simp [hRow] at hFirst
  have hSecondEq : second = edge := by
    by_cases hRow : input.family.assignment.oldRowOf second = some row
    · simpa [hRow] using hSecond
    · simp [hRow] at hSecond
  exact hFirstEq.trans hSecondEq.symm

/-- **The old path list of a presented row is the honest stable row.**  Its
occurrences above one retained target edge are exactly the natural
occurrence set of the corresponding incoming stable row. -/
theorem oldPath_toFinset_filter (input : AuxR0SourceInput data star)
    (row : Option target.edges) (place : target.edges) :
    ((input.family.assignment.oldPath row).toFinset.filter
        fun edge ↦ edge.1.1 = place) =
      occurrences data (input.labelling.row.symm row) place := by
  classical
  ext edge
  rw [Finset.mem_filter, List.mem_toFinset, mem_oldPath_iff,
    oldRowOf_eq_some_iff, mem_occurrences]

/-! ## Reading the presented rows -/

theorem coefficient_oldSourceEdge (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (edge : data.SourceEdge) (column : Option target.edges) :
    GluingDatum.LengthMatrixPresentation.coefficient (presented input pairing)
        ((member input pairing).oldSourceEdge edge) column =
      if column = some edge.1.1 then
        (1 : ℚ) / (data.sourceEdgeIndex edge : ℚ) else 0 :=
  canonicalPresentationOfPaths_coefficient_oldSourceEdge
    (fun p ↦ input.auxProfile.pairingCounts p) input.family.assignment.oldPath
    input.family.assignment.newSheets pairing edge column

theorem coefficient_newSourceEdge_some (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sheet : Fin degree) (place : target.edges) :
    GluingDatum.LengthMatrixPresentation.coefficient (presented input pairing)
        ((member input pairing).newSourceEdge sheet) (some place) = 0 :=
  canonicalPresentationOfPaths_coefficient_newSourceEdge_some
    (fun p ↦ input.auxProfile.pairingCounts p) input.family.assignment.oldPath
    input.family.assignment.newSheets pairing sheet place

theorem coefficient_newSourceEdge_none (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sheet : Fin degree) :
    GluingDatum.LengthMatrixPresentation.coefficient (presented input pairing)
        ((member input pairing).newSourceEdge sheet) none =
      (1 : ℚ) / ((member input pairing).datum.sourceEdgeIndex
        ((member input pairing).newSourceEdge sheet) : ℚ) := by
  classical
  have hTarget : (presented input pairing).targetEdge.symm
      ((member input pairing).newSourceEdge sheet).1.1 = none := by
    rw [presented_targetEdge]
    exact (occurrenceEquiv target wall
      (member input pairing).right).symm_apply_apply none
  unfold GluingDatum.LengthMatrixPresentation.coefficient
  rw [hTarget, if_pos rfl]

theorem row_eq_sum (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (path : List (member input pairing).datum.SourceEdge)
    (column : Option target.edges) :
    GluingDatum.LengthMatrixPresentation.row (presented input pairing) path
        column =
      (path.map fun edge ↦ GluingDatum.LengthMatrixPresentation.coefficient
        (presented input pairing) edge column).sum := rfl

theorem row_old_some (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (edges : List data.SourceEdge) (place : target.edges) :
    GluingDatum.LengthMatrixPresentation.row (presented input pairing)
        (edges.map (member input pairing).oldSourceEdge) (some place) =
      (edges.map fun edge ↦ if edge.1.1 = place then
        (1 : ℚ) / (data.sourceEdgeIndex edge : ℚ) else 0).sum := by
  classical
  rw [row_eq_sum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun edge _ ↦ ?_)
  rw [Function.comp_apply, coefficient_oldSourceEdge]
  by_cases hPlace : edge.1.1 = place
  · rw [if_pos hPlace, if_pos (congrArg some hPlace.symm)]
  · rw [if_neg hPlace, if_neg (fun hEq ↦ hPlace (Option.some.inj hEq).symm)]

theorem row_old_none (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (edges : List data.SourceEdge) :
    GluingDatum.LengthMatrixPresentation.row (presented input pairing)
        (edges.map (member input pairing).oldSourceEdge) none = 0 := by
  classical
  rw [row_eq_sum, List.map_map]
  refine List.sum_eq_zero fun value hValue ↦ ?_
  obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hValue
  rw [Function.comp_apply, coefficient_oldSourceEdge, if_neg (by simp)]

theorem row_new_some (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sheets : List (Fin degree)) (place : target.edges) :
    GluingDatum.LengthMatrixPresentation.row (presented input pairing)
        (sheets.map (member input pairing).newSourceEdge) (some place) = 0 := by
  classical
  rw [row_eq_sum, List.map_map]
  refine List.sum_eq_zero fun value hValue ↦ ?_
  obtain ⟨sheet, _, rfl⟩ := List.mem_map.mp hValue
  exact coefficient_newSourceEdge_some input pairing sheet place

theorem row_new_none (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sheets : List (Fin degree)) :
    GluingDatum.LengthMatrixPresentation.row (presented input pairing)
        (sheets.map (member input pairing).newSourceEdge) none =
      (sheets.map fun sheet ↦ (1 : ℚ) /
        ((member input pairing).datum.sourceEdgeIndex
          ((member input pairing).newSourceEdge sheet) : ℚ)).sum := by
  classical
  rw [row_eq_sum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun sheet _ ↦ ?_)
  exact coefficient_newSourceEdge_none input pairing sheet

/-! ## The presented matrix is the natural stable-length matrix -/

/-- **Every retained column of a presented W4 matrix is the honest column.**
The presented entry is computed from the raw path list; it equals the natural
stable-length entry of the incoming wall datum on the corresponding literal
stable row. -/
theorem presented_matrix_some (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (row : Option target.edges) (place : target.edges) :
    GluingDatum.LengthMatrixPresentation.matrix (presented input pairing) row
        (some place) =
      matrix data (input.labelling.row.symm row) place := by
  classical
  have hMatrix : GluingDatum.LengthMatrixPresentation.matrix
        (presented input pairing) row (some place) =
      GluingDatum.LengthMatrixPresentation.row (presented input pairing)
        ((presented input pairing).path row) (some place) := rfl
  rw [hMatrix, presented_path, GluingDatum.LengthMatrixPresentation.row_append,
    row_old_some, row_new_some, add_zero,
    ← List.sum_toFinset _ (oldPath_nodup input row), ← Finset.sum_filter,
    oldPath_toFinset_filter]
  rfl

/-! ## The presented regrown-sheet lists -/

omit [DecidableEq target.edges] in
theorem family_block (input : AuxR0SourceInput data star)
    (sourceBlock : WallBlock data wall) :
    input.family.block sourceBlock = input.blockPicture sourceBlock := rfl

omit [DecidableEq target.edges] in
theorem family_labelling (input : AuxR0SourceInput data star) :
    input.family.labelling = input.labelling := rfl

omit [DecidableEq target.edges] in
/-- **The presented regrowth choice is the geometric one.**  The raw
`AuxR0Family.regrown` datum names exactly the block's canonical regrown sheet,
labelled by the row of that block's canonical incoming occurrence. -/
theorem family_regrown_eq (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) :
    input.family.regrown pairing sourceBlock =
      (blockRegrownRow input pairing sourceBlock).map fun path ↦
        (input.labelling.row path, regrownSheet input pairing sourceBlock) := by
  cases hPicture : input.blockPicture sourceBlock with
  | dangling old_dangling =>
      rw [blockRegrownRow_dangling input pairing sourceBlock old_dangling
        hPicture]
      simp [AuxR0Family.regrown, family_block, hPicture]
  | nd2 block picture =>
      by_cases hSame : W4TargetPairings.Pairing.labelRight pairing block.first =
          W4TargetPairings.Pairing.labelRight pairing block.second
      · rw [blockRegrownRow_nd2_same input pairing sourceBlock block picture
          hPicture hSame]
        simp [AuxR0Family.regrown, family_block, hPicture, hSame]
      · rw [blockRegrownRow_nd2_ne input pairing sourceBlock block picture
          hPicture hSame,
          regrownSheet_nd2 input pairing sourceBlock block picture hPicture]
        simp [AuxR0Family.regrown, family_block, family_labelling, hPicture,
          hSame, AuxR0Nd2Picture.oldRow, AuxR0Nd2Picture.first, branchEdge]
  | nd3 block picture =>
      rw [blockRegrownRow_nd3 input pairing sourceBlock block picture hPicture,
        regrownSheet_nd3 input pairing sourceBlock block picture hPicture]
      simp only [AuxR0Family.regrown, family_block, family_labelling, hPicture,
        Option.map_some]
      rw [picture.oldRow_active input.labelling (block.singletonLabel pairing)
        (block.singletonLabel_mem_activeLabels pairing)]
      rfl

omit [DecidableEq target.edges] in
theorem family_regrown_eq_some_iff (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall)
    (row : Option target.edges) (sheet : Fin degree) :
    input.family.regrown pairing sourceBlock = some (row, sheet) ↔
      blockRegrownRow input pairing sourceBlock =
          some (input.labelling.row.symm row) ∧
        regrownSheet input pairing sourceBlock = sheet := by
  rw [family_regrown_eq]
  cases hRow : blockRegrownRow input pairing sourceBlock with
  | none => simp
  | some path =>
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨hLabel, hSheet⟩
        exact ⟨(Equiv.eq_symm_apply _).2 hLabel, hSheet⟩
      · rintro ⟨hPath, hSheet⟩
        refine ⟨?_, hSheet⟩
        rw [hPath]
        simp

theorem mem_newSheets_iff (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (row : Option target.edges) (sheet : Fin degree) :
    sheet ∈ input.family.assignment.newSheets pairing row ↔
      blockRegrownRow input pairing (WallBlock.ofSheet data wall sheet) =
          some (input.labelling.row.symm row) ∧
        regrownSheet input pairing (WallBlock.ofSheet data wall sheet) =
          sheet := by
  classical
  simp only [W4StablePathAssignment.PathAssignment.newSheets,
    List.mem_filterMap, Finset.mem_toList, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨other, hOther⟩
    by_cases hRegrown : input.family.assignment.regrown pairing
        (WallBlock.ofSheet data wall other) = some (row, other)
    · rw [if_pos hRegrown] at hOther
      have hEq : other = sheet := Option.some.inj hOther
      subst hEq
      rw [AuxR0Family.assignment_regrown] at hRegrown
      exact (family_regrown_eq_some_iff input pairing _ row other).mp hRegrown
    · rw [if_neg hRegrown] at hOther
      exact absurd hOther (by simp)
  · intro hSheet
    refine ⟨sheet, ?_⟩
    have hRegrown : input.family.assignment.regrown pairing
        (WallBlock.ofSheet data wall sheet) = some (row, sheet) := by
      rw [AuxR0Family.assignment_regrown]
      exact (family_regrown_eq_some_iff input pairing _ row sheet).mpr hSheet
    rw [if_pos hRegrown]

theorem newSheets_nodup (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (row : Option target.edges) :
    (input.family.assignment.newSheets pairing row).Nodup := by
  classical
  refine List.Nodup.filterMap ?_ (Finset.univ.nodup_toList)
  intro first second sheet hFirst hSecond
  have hFirstEq : first = sheet := by
    by_cases hRegrown : input.family.assignment.regrown pairing
        (WallBlock.ofSheet data wall first) = some (row, first)
    · rw [Option.mem_def, if_pos hRegrown] at hFirst
      exact Option.some.inj hFirst
    · rw [Option.mem_def, if_neg hRegrown] at hFirst
      exact absurd hFirst (by simp)
  have hSecondEq : second = sheet := by
    by_cases hRegrown : input.family.assignment.regrown pairing
        (WallBlock.ofSheet data wall second) = some (row, second)
    · rw [Option.mem_def, if_pos hRegrown] at hSecond
      exact Option.some.inj hSecond
    · rw [Option.mem_def, if_neg hRegrown] at hSecond
      exact absurd hSecond (by simp)
  exact hFirstEq.trans hSecondEq.symm

/-- **The presented regrown-sheet list of a row is the geometric one.**  It
enumerates, once each, the canonical regrown sheets of exactly the wall blocks
that regrow a surviving occurrence on that row. -/
theorem newSheets_toFinset (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (row : Option target.edges) :
    (input.family.assignment.newSheets pairing row).toFinset =
      (regrowingBlocks input pairing (input.labelling.row.symm row)).image
        (regrownSheet input pairing) := by
  classical
  ext sheet
  rw [List.mem_toFinset, mem_newSheets_iff, Finset.mem_image]
  constructor
  · rintro ⟨hRow, hSheet⟩
    exact ⟨WallBlock.ofSheet data wall sheet,
      (mem_regrowingBlocks _ _ _ _).mpr hRow, hSheet⟩
  · rintro ⟨sourceBlock, hBlock, rfl⟩
    rw [ofSheet_regrownSheet]
    exact ⟨(mem_regrowingBlocks _ _ _ _).mp hBlock, rfl⟩

omit [DecidableEq target.edges] in
theorem regrownSheet_injective (input : AuxR0SourceInput data star)
    (pairing : Fin 3) : Function.Injective (regrownSheet input pairing) := by
  intro first second hEq
  rw [← ofSheet_regrownSheet input pairing first, hEq,
    ofSheet_regrownSheet input pairing second]

/-- **The regrown column of a presented W4 matrix is the honest regrown
column.** -/
theorem presented_matrix_none (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (row : Option target.edges) :
    GluingDatum.LengthMatrixPresentation.matrix (presented input pairing) row
        none =
      matrix (member input pairing).datum
        (stablePathEquiv input pairing (input.labelling.row.symm row))
        (occurrenceEquiv target wall (member input pairing).right none) := by
  classical
  have hMatrix : GluingDatum.LengthMatrixPresentation.matrix
        (presented input pairing) row none =
      GluingDatum.LengthMatrixPresentation.row (presented input pairing)
        ((presented input pairing).path row) none := rfl
  rw [hMatrix, presented_path, GluingDatum.LengthMatrixPresentation.row_append,
    row_old_none, row_new_none, zero_add,
    ← List.sum_toFinset _ (newSheets_nodup input pairing row),
    newSheets_toFinset,
    Finset.sum_image
      (fun first _ second _ hEq ↦ regrownSheet_injective input pairing hEq),
    matrix_new]
  refine Finset.sum_congr rfl fun sourceBlock hBlock ↦ ?_
  rw [sourceEdgeIndex_newSourceEdge_regrownSheet input pairing sourceBlock _
    ((mem_regrowingBlocks input pairing _ sourceBlock).mp hBlock)]

/-- **The presented W4 matrices are the natural stable-length matrices.**  Row
`row` of the presented matrix of the outgoing candidate `pairing` is the row
of `StableSourceMatrix.matrix` at the literal outgoing stable row obtained
from `input.labelling`'s incoming row through the occurrence-induced
equivalence `stablePathEquiv`, and columns correspond under
`occurrenceEquiv`.

It is proved through the row equivalence, not through any count: the retained columns go through
`matrix_retained`, and the regrown column through `matrix_new`, whose support
is the set of literal surviving regrown occurrences. -/
theorem presented_matrix_eq (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (row column : Option target.edges) :
    GluingDatum.LengthMatrixPresentation.matrix (presented input pairing) row
        column =
      matrix (member input pairing).datum
        (stablePathEquiv input pairing (input.labelling.row.symm row))
        (occurrenceEquiv target wall (member input pairing).right column) := by
  cases column with
  | none => exact presented_matrix_none input pairing row
  | some place =>
      rw [presented_matrix_some input pairing row place]
      exact (matrix_retained input pairing (input.labelling.row.symm row)
        place).symm

/-- `presented_matrix_eq` stated directly for
`AuxR0SourceInput.presentedFamily`. -/
theorem presentedFamily_matrix_eq (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (row column : Option target.edges) :
    GluingDatum.LengthMatrixPresentation.matrix
        ((input.presentedFamily data star).presentation pairing) row column =
      matrix (member input pairing).datum
        (stablePathEquiv input pairing (input.labelling.row.symm row))
        (occurrenceEquiv target wall (member input pairing).right column) :=
  presented_matrix_eq input pairing row column

/-- The row correspondence carried by the presented matrices: a presented row
label names an incoming stable row through `input.labelling`, and that row
names an outgoing one through the occurrence-induced equivalence. -/
noncomputable def rowEquiv (input : AuxR0SourceInput data star) (pairing : Fin 3) :
    Option target.edges ≃ StablePath (member input pairing).datum :=
  input.labelling.row.symm.trans (stablePathEquiv input pairing)

/-- `presented_matrix_eq` as one matrix equation. -/
theorem presented_matrix_submatrix (input : AuxR0SourceInput data star)
    (pairing : Fin 3) :
    GluingDatum.LengthMatrixPresentation.matrix (presented input pairing) =
      (matrix (member input pairing).datum).submatrix (rowEquiv input pairing)
        (occurrenceEquiv target wall (member input pairing).right) := by
  ext row column
  exact presented_matrix_eq input pairing row column

/-- **The presented family's off-wall agreement, for the honest reason.**  Both
entries are the same entry of the incoming wall matrix. -/
theorem presented_matrix_some_eq (input : AuxR0SourceInput data star)
    (first second : Fin 3) (row : Option target.edges) (place : target.edges) :
    GluingDatum.LengthMatrixPresentation.matrix (presented input first) row
        (some place) =
      GluingDatum.LengthMatrixPresentation.matrix (presented input second) row
        (some place) := by
  rw [presented_matrix_some, presented_matrix_some]

/-! ## Block-by-block form of the regrown column

This is the input Equation (1) consumes: the three candidates' regrown columns
summed block by block.  The two evaluations below are the source's Equations
(w4-nd2) and (w4-nd3) with the stable-row cofactor stripped off.
-/

/-- The contribution of one incoming occurrence to one incoming stable row:
its reciprocal dilation index if it survives and carries the row, and zero
otherwise. -/
noncomputable def rowTerm (data : GluingDatum target degree)
    (path : StablePath data) (edge : data.SourceEdge) : ℚ := by
  classical
  exact if ∃ hSurvives : ¬ IsDangling data edge,
      NonDanglingEdge.stablePath (⟨edge, hSurvives⟩ : NonDanglingEdge data) =
        path then
    (1 : ℚ) / (data.sourceEdgeIndex edge : ℚ)
  else 0

omit [DecidableEq target.edges] in
theorem rowTerm_of_survives (path : StablePath data)
    (edge : NonDanglingEdge data) :
    rowTerm data path edge.1 =
      if edge.stablePath = path then
        (1 : ℚ) / (data.sourceEdgeIndex edge.1 : ℚ) else 0 := by
  classical
  unfold rowTerm
  by_cases hRow : edge.stablePath = path
  · rw [if_pos ⟨edge.2, hRow⟩, if_pos hRow]
  · rw [if_neg fun hExists ↦ hRow hExists.choose_spec, if_neg hRow]

/-- One old wall block's contribution to one candidate's regrown column at one
incoming stable row. -/
noncomputable def blockColumnTerm (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (path : StablePath data)
    (sourceBlock : WallBlock data wall) : ℚ := by
  classical
  exact if blockRegrownRow input pairing sourceBlock = some path then
      (1 : ℚ) /
        (data.sourceEdgeIndex (blockOldSourceEdge input pairing sourceBlock) : ℚ)
    else 0

omit [DecidableEq target.edges] in
theorem blockColumnTerm_pos (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (path : StablePath data)
    (sourceBlock : WallBlock data wall)
    (hRow : blockRegrownRow input pairing sourceBlock = some path) :
    blockColumnTerm input pairing path sourceBlock =
      (1 : ℚ) /
        (data.sourceEdgeIndex (blockOldSourceEdge input pairing sourceBlock) :
          ℚ) := by
  classical
  rw [blockColumnTerm, if_pos hRow]

omit [DecidableEq target.edges] in
theorem blockColumnTerm_neg (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (path : StablePath data)
    (sourceBlock : WallBlock data wall)
    (hRow : ¬ blockRegrownRow input pairing sourceBlock = some path) :
    blockColumnTerm input pairing path sourceBlock = 0 := by
  classical
  rw [blockColumnTerm, if_neg hRow]

theorem matrix_new_eq_sum (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (path : StablePath data) :
    matrix (member input pairing).datum (stablePathEquiv input pairing path)
        (occurrenceEquiv target wall (member input pairing).right none) =
      ∑ sourceBlock : WallBlock data wall,
        blockColumnTerm input pairing path sourceBlock := by
  classical
  rw [matrix_new]
  refine Eq.trans (Finset.sum_congr rfl fun sourceBlock hBlock ↦ ?_)
    (Finset.sum_subset (Finset.subset_univ _) fun sourceBlock _ hBlock ↦ ?_)
  · exact (blockColumnTerm_pos input pairing path sourceBlock
      ((mem_regrowingBlocks input pairing path sourceBlock).mp hBlock)).symm
  · exact blockColumnTerm_neg input pairing path sourceBlock
      fun hRow ↦ hBlock
        ((mem_regrowingBlocks input pairing path sourceBlock).mpr hRow)

/-- **The three candidates' regrown columns, summed block by block.**  This is
the left-hand side of the source's Equation (1) at one stable row. -/
theorem sum_matrix_new (input : AuxR0SourceInput data star)
    (path : StablePath data) :
    ∑ pairing : Fin 3, matrix (member input pairing).datum
        (stablePathEquiv input pairing path)
        (occurrenceEquiv target wall (member input pairing).right none) =
      ∑ sourceBlock : WallBlock data wall, ∑ pairing : Fin 3,
        blockColumnTerm input pairing path sourceBlock := by
  rw [Finset.sum_congr rfl fun pairing _ ↦ matrix_new_eq_sum input pairing path]
  exact Finset.sum_comm

/-! ## The two pairing counts behind Equations (w4-nd2) and (w4-nd3) -/

omit [DecidableEq target.edges] in
/-- Exactly two of the three `2+2` pairings separate two distinct star
labels. -/
theorem card_separating_pairings (first second : Fin 4) (hNe : first ≠ second) :
    ((Finset.univ : Finset (Fin 3)).filter fun pairing ↦
      W4TargetPairings.Pairing.labelRight pairing first ≠
        W4TargetPairings.Pairing.labelRight pairing second).card = 2 := by
  revert hNe
  revert first second
  decide

omit [DecidableEq target.edges] in
/-- Distinct pairings isolate distinct branches of an nd3 block. -/
theorem singletonLabel_injective (block : Nd3Block) :
    Function.Injective block.singletonLabel := by
  rcases block with ⟨first, second, third, h12, h13, h23⟩
  revert first second third
  decide

omit [DecidableEq target.edges] in
/-- **Each of the three active nd3 branches is isolated by exactly one
pairing.**  This is the combinatorial content of Equation (w4-nd3). -/
theorem image_singletonLabel (block : Nd3Block) :
    (Finset.univ : Finset (Fin 3)).image block.singletonLabel =
      block.activeLabels := by
  rcases block with ⟨first, second, third, h12, h13, h23⟩
  revert first second third
  decide

/-! ## Equations (w4-nd2) and (w4-nd3), block by block -/

omit [DecidableEq target.edges] in
theorem rowTerm_branchEdge (path : StablePath data) (label : Fin 4)
    (sheet : Fin degree)
    (hSurvives : ¬ IsDangling data (data.sourceEdge (star.edge label) sheet)) :
    rowTerm data path (data.sourceEdge (star.edge label) sheet) =
      if (branchEdge data star label sheet hSurvives).stablePath = path then
        (1 : ℚ) /
          (data.sourceEdgeIndex (data.sourceEdge (star.edge label) sheet) : ℚ)
      else 0 :=
  rowTerm_of_survives path (branchEdge data star label sheet hSurvives)

omit [DecidableEq target.edges] in
/-- A dangling wall block contributes nothing to any regrown column. -/
theorem sum_pairings_blockColumnTerm_dangling (input : AuxR0SourceInput data star)
    (sourceBlock : WallBlock data wall)
    (old_dangling : ∀ (edge : data.SourceEdge) (label : Fin 4),
      WallBlock.ofSheet data wall edge.1.2 = sourceBlock →
      star.edge label = edge.1.1 → IsDangling data edge)
    (hPicture : input.blockPicture sourceBlock = .dangling old_dangling)
    (path : StablePath data) :
    ∑ pairing : Fin 3, blockColumnTerm input pairing path sourceBlock = 0 := by
  refine Finset.sum_eq_zero fun pairing _ ↦ ?_
  refine blockColumnTerm_neg input pairing path sourceBlock ?_
  rw [blockRegrownRow_dangling input pairing sourceBlock old_dangling hPicture]
  simp

omit [DecidableEq target.edges] in
/-- **Equation (w4-nd2).**  Over the three candidates an nd2 wall block
contributes twice the term of its first active branch — the source's
`c(e_α)/|e_α| + c(e_β)/|e_β|`, since the two active branches share both their
stable row and their dilation index. -/
theorem sum_pairings_blockColumnTerm_nd2 (input : AuxR0SourceInput data star)
    (sourceBlock : WallBlock data wall) (block : Nd2Block)
    (picture : AuxR0Nd2Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd2 block picture)
    (path : StablePath data) :
    ∑ pairing : Fin 3, blockColumnTerm input pairing path sourceBlock =
      2 * rowTerm data path
        (data.sourceEdge (star.edge block.first) sourceBlock.1) := by
  classical
  rw [rowTerm_branchEdge path block.first sourceBlock.1 picture.first_survives]
  set contribution : ℚ :=
    if (branchEdge data star block.first sourceBlock.1
        picture.first_survives).stablePath = path then
      (1 : ℚ) / (data.sourceEdgeIndex
        (data.sourceEdge (star.edge block.first) sourceBlock.1) : ℚ)
    else 0 with hContribution
  have hTerm : ∀ pairing : Fin 3,
      blockColumnTerm input pairing path sourceBlock =
        if W4TargetPairings.Pairing.labelRight pairing block.first ≠
            W4TargetPairings.Pairing.labelRight pairing block.second then
          contribution else 0 := by
    intro pairing
    by_cases hSame : W4TargetPairings.Pairing.labelRight pairing block.first =
        W4TargetPairings.Pairing.labelRight pairing block.second
    · rw [blockColumnTerm_neg input pairing path sourceBlock (by
        rw [blockRegrownRow_nd2_same input pairing sourceBlock block picture
          hPicture hSame]
        simp), if_neg (by simpa using hSame)]
    · rw [blockColumnTerm, blockRegrownRow_nd2_ne input pairing sourceBlock
        block picture hPicture hSame,
        blockOldSourceEdge_nd2 input pairing sourceBlock block picture hPicture,
        if_pos hSame, hContribution]
      by_cases hRow : (branchEdge data star block.first sourceBlock.1
          picture.first_survives).stablePath = path
      · rw [if_pos (congrArg some hRow), if_pos hRow]
      · rw [if_neg fun hEq ↦ hRow (Option.some.inj hEq), if_neg hRow]
  rw [Finset.sum_congr rfl fun pairing _ ↦ hTerm pairing, ← Finset.sum_filter,
    Finset.sum_const,
    card_separating_pairings block.first block.second block.distinct,
    nsmul_eq_mul]
  norm_num

omit [DecidableEq target.edges] in
theorem rowTerm_nd3SingletonEdge {sourceBlock : WallBlock data wall}
    {block : Nd3Block} (picture : AuxR0Nd3Picture data star sourceBlock block)
    (pairing : Fin 3) (path : StablePath data) :
    rowTerm data path (data.sourceEdge (star.edge (block.singletonLabel pairing))
        (picture.activeSheet (block.singletonLabel pairing))) =
      if (nd3SingletonEdge picture pairing).stablePath = path then
        (1 : ℚ) / (data.sourceEdgeIndex
          (data.sourceEdge (star.edge (block.singletonLabel pairing))
            (picture.activeSheet (block.singletonLabel pairing))) : ℚ)
      else 0 :=
  rowTerm_of_survives path (nd3SingletonEdge picture pairing)

omit [DecidableEq target.edges] in
/-- **Equation (w4-nd3).**  Over the three candidates an nd3 wall block
contributes exactly once for each of its three active branches, on that
branch's own stable row: the source's
`c(e_α)/|e_α| + c(e_β)/|e_β| + c(e_γ)/|e_γ|`. -/
theorem sum_pairings_blockColumnTerm_nd3 (input : AuxR0SourceInput data star)
    (sourceBlock : WallBlock data wall) (block : Nd3Block)
    (picture : AuxR0Nd3Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd3 block picture)
    (path : StablePath data) :
    ∑ pairing : Fin 3, blockColumnTerm input pairing path sourceBlock =
      ∑ label ∈ block.activeLabels, rowTerm data path
        (data.sourceEdge (star.edge label) (picture.activeSheet label)) := by
  classical
  rw [← image_singletonLabel block,
    Finset.sum_image fun first _ second _ hEq ↦
      singletonLabel_injective block hEq]
  refine Finset.sum_congr rfl fun pairing _ ↦ ?_
  rw [blockColumnTerm,
    blockRegrownRow_nd3 input pairing sourceBlock block picture hPicture,
    blockOldSourceEdge_nd3 input pairing sourceBlock block picture hPicture,
    rowTerm_nd3SingletonEdge picture pairing path]
  by_cases hRow : (nd3SingletonEdge picture pairing).stablePath = path
  · rw [if_pos (congrArg some hRow), if_pos hRow]
  · rw [if_neg fun hEq ↦ hRow (Option.some.inj hEq), if_neg hRow]

/-! ## The four incoming wall columns, block by block -/

/-- The surviving occurrences on one incoming stable row that lie over one of
the four wall branches. -/
noncomputable def wallOccurrences (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall) (path : StablePath data) :
    Finset data.SourceEdge := by
  classical
  exact (Finset.univ : Finset (Fin 4)).biUnion fun label ↦
    occurrences data path (star.edge label)

omit [DecidableEq target.edges] in
theorem mem_wallOccurrences (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall) (path : StablePath data)
    (edge : data.SourceEdge) :
    edge ∈ wallOccurrences data star path ↔
      (∃ hSurvives : ¬ IsDangling data edge,
          NonDanglingEdge.stablePath (⟨edge, hSurvives⟩ : NonDanglingEdge data) =
            path) ∧
        ∃ label : Fin 4, star.edge label = edge.1.1 := by
  classical
  simp only [wallOccurrences, Finset.mem_biUnion, Finset.mem_univ, true_and,
    mem_occurrences]
  constructor
  · rintro ⟨label, hRow, hTarget⟩
    exact ⟨hRow, label, hTarget.symm⟩
  · rintro ⟨hRow, label, hTarget⟩
    exact ⟨label, hRow, hTarget.symm⟩

omit [DecidableEq target.edges] in
/-- The four incoming wall columns at one stable row, added up. -/
theorem sum_matrix_star (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall) (path : StablePath data) :
    ∑ label : Fin 4, matrix data path (star.edge label) =
      ∑ edge ∈ wallOccurrences data star path,
        (1 : ℚ) / (data.sourceEdgeIndex edge : ℚ) := by
  classical
  unfold wallOccurrences matrix
  refine (Finset.sum_biUnion ?_).symm
  intro first _ second _ hNe
  refine Finset.disjoint_left.mpr fun edge hFirst hSecond ↦ hNe ?_
  exact star.edge_injective
    (((mem_occurrences _ _ _).mp hFirst).2.symm.trans
      ((mem_occurrences _ _ _).mp hSecond).2)

omit [DecidableEq target.edges] in
theorem sum_wallOccurrences_fiberwise (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall) (path : StablePath data) :
    ∑ edge ∈ wallOccurrences data star path,
        (1 : ℚ) / (data.sourceEdgeIndex edge : ℚ) =
      ∑ sourceBlock : WallBlock data wall,
        ∑ edge ∈ (wallOccurrences data star path).filter
            (fun edge ↦ WallBlock.ofSheet data wall edge.1.2 = sourceBlock),
          (1 : ℚ) / (data.sourceEdgeIndex edge : ℚ) := by
  classical
  exact (Finset.sum_fiberwise _ _ _).symm

/-- The canonical branch occurrences of one old wall block: none above a
dangling block, the two active branches above an nd2 block, the three active
branches above an nd3 block. -/
noncomputable def blockBranchOccurrences (input : AuxR0SourceInput data star)
    (sourceBlock : WallBlock data wall) : Finset data.SourceEdge := by
  classical
  exact match input.blockPicture sourceBlock with
  | .dangling _ => ∅
  | .nd2 block _ =>
      {data.sourceEdge (star.edge block.first) sourceBlock.1,
        data.sourceEdge (star.edge block.second) sourceBlock.1}
  | .nd3 block picture =>
      block.activeLabels.image fun label ↦
        data.sourceEdge (star.edge label) (picture.activeSheet label)

omit [DecidableEq target.edges] in
theorem blockBranchOccurrences_dangling (input : AuxR0SourceInput data star)
    (sourceBlock : WallBlock data wall)
    (old_dangling : ∀ (edge : data.SourceEdge) (label : Fin 4),
      WallBlock.ofSheet data wall edge.1.2 = sourceBlock →
      star.edge label = edge.1.1 → IsDangling data edge)
    (hPicture : input.blockPicture sourceBlock = .dangling old_dangling) :
    blockBranchOccurrences input sourceBlock = ∅ := by
  classical
  rw [blockBranchOccurrences, hPicture]

omit [DecidableEq target.edges] in
theorem blockBranchOccurrences_nd2 (input : AuxR0SourceInput data star)
    (sourceBlock : WallBlock data wall) (block : Nd2Block)
    (picture : AuxR0Nd2Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd2 block picture) :
    blockBranchOccurrences input sourceBlock =
      {data.sourceEdge (star.edge block.first) sourceBlock.1,
        data.sourceEdge (star.edge block.second) sourceBlock.1} := by
  classical
  rw [blockBranchOccurrences, hPicture]

omit [DecidableEq target.edges] in
theorem blockBranchOccurrences_nd3 (input : AuxR0SourceInput data star)
    (sourceBlock : WallBlock data wall) (block : Nd3Block)
    (picture : AuxR0Nd3Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd3 block picture) :
    blockBranchOccurrences input sourceBlock =
      block.activeLabels.image fun label ↦
        data.sourceEdge (star.edge label) (picture.activeSheet label) := by
  classical
  rw [blockBranchOccurrences, hPicture]

omit [DecidableEq target.edges] in
/-- **The incoming wall occurrences of one stable row above one wall block are
exactly that block's canonical branch occurrences on that row.**  Forward this
is the `only_surviving` field of the three source pictures; backward it is the
survival and placement of those canonical occurrences. -/
theorem wallOccurrences_filter_eq (input : AuxR0SourceInput data star)
    (path : StablePath data) (sourceBlock : WallBlock data wall) :
    (wallOccurrences data star path).filter
        (fun edge ↦ WallBlock.ofSheet data wall edge.1.2 = sourceBlock) =
      (blockBranchOccurrences input sourceBlock).filter
        (fun edge ↦ ∃ hSurvives : ¬ IsDangling data edge,
          NonDanglingEdge.stablePath (⟨edge, hSurvives⟩ : NonDanglingEdge data) =
            path) := by
  classical
  ext edge
  rw [Finset.mem_filter, Finset.mem_filter, mem_wallOccurrences]
  constructor
  · rintro ⟨⟨hRow, label, hTarget⟩, hBlock⟩
    obtain ⟨hSurvives, hPath⟩ := hRow
    refine ⟨?_, hSurvives, hPath⟩
    cases hPicture : input.blockPicture sourceBlock with
    | dangling old_dangling =>
        exact absurd (old_dangling edge label hBlock hTarget) hSurvives
    | nd2 block picture =>
        rw [blockBranchOccurrences_nd2 input sourceBlock block picture hPicture]
        rcases picture.only_surviving edge hBlock ⟨label, hTarget⟩ hSurvives with
          hValue | hValue
        · exact Finset.mem_insert.mpr (Or.inl hValue)
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hValue))
    | nd3 block picture =>
        rw [blockBranchOccurrences_nd3 input sourceBlock block picture hPicture]
        obtain ⟨other, hActive, hValue⟩ :=
          picture.only_surviving edge hBlock ⟨label, hTarget⟩ hSurvives
        exact Finset.mem_image.mpr ⟨other, hActive, hValue.symm⟩
  · rintro ⟨hMem, hSurvives, hPath⟩
    refine ⟨⟨⟨hSurvives, hPath⟩, ?_⟩, ?_⟩
    · cases hPicture : input.blockPicture sourceBlock with
      | dangling old_dangling =>
          rw [blockBranchOccurrences_dangling input sourceBlock old_dangling
            hPicture] at hMem
          exact absurd hMem (by simp)
      | nd2 block picture =>
          rw [blockBranchOccurrences_nd2 input sourceBlock block picture
            hPicture] at hMem
          rcases Finset.mem_insert.mp hMem with hValue | hValue
          · exact ⟨block.first, by rw [hValue, data.sourceEdge_target]⟩
          · exact ⟨block.second, by
              rw [Finset.mem_singleton.mp hValue, data.sourceEdge_target]⟩
      | nd3 block picture =>
          rw [blockBranchOccurrences_nd3 input sourceBlock block picture
            hPicture] at hMem
          obtain ⟨other, _, hValue⟩ := Finset.mem_image.mp hMem
          exact ⟨other, by rw [← hValue, data.sourceEdge_target]⟩
    · cases hPicture : input.blockPicture sourceBlock with
      | dangling old_dangling =>
          rw [blockBranchOccurrences_dangling input sourceBlock old_dangling
            hPicture] at hMem
          exact absurd hMem (by simp)
      | nd2 block picture =>
          rw [blockBranchOccurrences_nd2 input sourceBlock block picture
            hPicture] at hMem
          rcases Finset.mem_insert.mp hMem with hValue | hValue
          · rw [hValue]
            exact WallBlock.ofSourceEdge_eq_of_rel data star sourceBlock
              block.first sourceBlock.1 rfl
          · rw [Finset.mem_singleton.mp hValue]
            exact WallBlock.ofSourceEdge_eq_of_rel data star sourceBlock
              block.second sourceBlock.1 rfl
      | nd3 block picture =>
          rw [blockBranchOccurrences_nd3 input sourceBlock block picture
            hPicture] at hMem
          obtain ⟨other, hActive, hValue⟩ := Finset.mem_image.mp hMem
          rw [← hValue]
          exact WallBlock.ofSourceEdge_eq_of_rel data star sourceBlock other _
            (picture.active_sheet other hActive)

omit [DecidableEq target.edges] in
theorem sum_fiber_eq_sum_rowTerm (input : AuxR0SourceInput data star)
    (path : StablePath data) (sourceBlock : WallBlock data wall) :
    ∑ edge ∈ (wallOccurrences data star path).filter
        (fun edge ↦ WallBlock.ofSheet data wall edge.1.2 = sourceBlock),
        (1 : ℚ) / (data.sourceEdgeIndex edge : ℚ) =
      ∑ edge ∈ blockBranchOccurrences input sourceBlock,
        rowTerm data path edge := by
  classical
  rw [wallOccurrences_filter_eq input path sourceBlock, Finset.sum_filter]
  exact Finset.sum_congr rfl fun edge _ ↦ by rw [rowTerm]

omit [DecidableEq target.edges] in
/-- The two active branches of an nd2 wall block contribute equally: Case
`{aux-r0-nd2}` gives them one stable row, and Equation (C) gives them one
dilation index. -/
theorem rowTerm_nd2_second (input : AuxR0SourceInput data star)
    (sourceBlock : WallBlock data wall) (block : Nd2Block)
    (picture : AuxR0Nd2Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd2 block picture)
    (path : StablePath data) :
    rowTerm data path (data.sourceEdge (star.edge block.second) sourceBlock.1) =
      rowTerm data path
        (data.sourceEdge (star.edge block.first) sourceBlock.1) := by
  have hPattern :=
    blockPattern_eq_nd2_of_picture input sourceBlock block picture hPicture
  obtain ⟨hFirstCard, hSecondCard⟩ :=
    input.auxProfile.nd2_active_blockCard sourceBlock.1 block hPattern
      sourceBlock.1 rfl
  rw [rowTerm_branchEdge path block.second sourceBlock.1 picture.second_survives,
    rowTerm_branchEdge path block.first sourceBlock.1 picture.first_survives,
    nd2_old_stablePath_eq picture, GluingDatum.sourceEdgeIndex_sourceEdge,
    GluingDatum.sourceEdgeIndex_sourceEdge, hFirstCard, hSecondCard]

omit [DecidableEq target.edges] in
/-- **The three candidates' regrown columns are the four incoming wall columns,
block by block.** -/
theorem sum_pairings_blockColumnTerm_eq (input : AuxR0SourceInput data star)
    (path : StablePath data) (sourceBlock : WallBlock data wall) :
    ∑ pairing : Fin 3, blockColumnTerm input pairing path sourceBlock =
      ∑ edge ∈ blockBranchOccurrences input sourceBlock,
        rowTerm data path edge := by
  classical
  cases hPicture : input.blockPicture sourceBlock with
  | dangling old_dangling =>
      rw [sum_pairings_blockColumnTerm_dangling input sourceBlock old_dangling
          hPicture path,
        blockBranchOccurrences_dangling input sourceBlock old_dangling hPicture,
        Finset.sum_empty]
  | nd2 block picture =>
      rw [sum_pairings_blockColumnTerm_nd2 input sourceBlock block picture
          hPicture path,
        blockBranchOccurrences_nd2 input sourceBlock block picture hPicture,
        Finset.sum_pair (sourceEdge_ne_of_label_ne' data star block.distinct
          sourceBlock.1 sourceBlock.1),
        rowTerm_nd2_second input sourceBlock block picture hPicture path]
      ring
  | nd3 block picture =>
      rw [sum_pairings_blockColumnTerm_nd3 input sourceBlock block picture
          hPicture path,
        blockBranchOccurrences_nd3 input sourceBlock block picture hPicture,
        Finset.sum_image fun first _ second _ hEq ↦ star.edge_injective
          (congrArg (fun edge : data.SourceEdge ↦ edge.1.1) hEq)]

/-- **Equation (1) at one stable row, before cofactors.**  Summed over the
three outgoing candidates, the regrown column of the natural stable-length
matrix equals the sum of the four incoming wall columns of the natural
stable-length matrix of the wall datum.  Block by block this is exactly
Equations (w4-nd2) and (w4-nd3) of the source: a dangling block contributes
nothing on either side, an nd2 block contributes `1/|e_α| + 1/|e_β|`, and an
nd3 block `1/|e_α| + 1/|e_β| + 1/|e_γ|`.

Multiplying by the stable row's cofactor and summing over rows is the source's
Equation (1); the cofactors and the balance are `W4CommonBalance`. -/
theorem sum_matrix_new_eq_sum_wall (input : AuxR0SourceInput data star)
    (path : StablePath data) :
    ∑ pairing : Fin 3, matrix (member input pairing).datum
        (stablePathEquiv input pairing path)
        (occurrenceEquiv target wall (member input pairing).right none) =
      ∑ label : Fin 4, matrix data path (star.edge label) := by
  rw [sum_matrix_new, sum_matrix_star, sum_wallOccurrences_fiberwise]
  exact Finset.sum_congr rfl fun sourceBlock _ ↦
    (sum_pairings_blockColumnTerm_eq input path sourceBlock).trans
      (sum_fiber_eq_sum_rowTerm input path sourceBlock).symm

end Candidate

end DraismaVargas.LocalCases.W4OutgoingLimitMatrix
