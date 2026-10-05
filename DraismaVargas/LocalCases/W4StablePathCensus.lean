module

public import DraismaVargas.LocalCases.W4SourceClassification
public import Mathlib.Algebra.Order.Group.Multiset

@[expose] public section

/-!
# Stable-path occurrence census for W4

This module states W4's multiset data as literal pointwise multiplicities in
one common family of old stable paths and three
families of regrown-sheet paths.  Generic count lemmas expose the multiplicity
of each canonical source occurrence.  The nd2 and nd3 records then state the
two source pictures before candidate lifting; both lower to
`GlobalW4.CanonicalBlockClassification`.

`ExpectedBlockCensus` is selected by the active-label classification, so a
source proof does not choose a second W4 pattern.  Constructing these counts
from the stable graph `H(M)` and the inherited dangling/no-return/pass-once
properties is a separate step, not taken here.
-/

namespace DraismaVargas.LocalCases.W4StablePathCensus

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.GlobalW4
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.W4SourceClassification

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

private theorem count_filterMap_tagged
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (items : List α) (keep : α → Prop) [DecidablePred keep]
    (tag : β) (item : α) :
    (Multiset.ofList (items.filterMap fun candidate ↦
      if keep candidate then some (tag, candidate) else none)).count
        (tag, item) =
      if keep item then items.count item else 0 := by
  induction items with
  | nil => simp
  | cons head tail ih =>
      rw [Multiset.coe_count] at ih
      by_cases hHead : keep head
      · by_cases hEq : head = item
        · subst head
          simp [hHead, ih]
        · by_cases hItem : keep item
          · simp [hHead, hEq, hItem, ih]
          · simp [hHead, hEq, hItem, ih]
      · by_cases hEq : head = item
        · subst head
          simp [hHead]
        · by_cases hItem : keep item
          · rw [List.count_cons_of_ne hEq]
            simp [hHead, hItem, ih]
          · simp [hHead, hItem]

theorem count_canonicalNewSheetOccurrences
    [DecidableEq target.edges]
    (sourceBlock : WallBlock data wall)
    (newSheets : Option target.edges → List (Fin degree))
    (row : Option target.edges) (sheet : Fin degree) :
    (canonicalNewSheetOccurrences sourceBlock newSheets).count (row, sheet) =
      if WallBlock.ofSheet data wall sheet = sourceBlock then
        (newSheets row).count sheet
      else 0 := by
  classical
  unfold canonicalNewSheetOccurrences
  rw [← Multiset.coe_countAddMonoidHom]
  rw [map_sum]
  rw [Multiset.coe_countAddMonoidHom]
  rw [Finset.sum_eq_single row]
  · exact count_filterMap_tagged (newSheets row)
      (fun candidate ↦ WallBlock.ofSheet data wall candidate = sourceBlock)
      row sheet
  · intro other _hOther hne
    simp [hne]
  · simp

theorem count_canonicalOldPathOccurrences
    (star : W4TargetPairings.FourStar target wall)
    [DecidableEq target.edges]
    (sourceBlock : WallBlock data wall)
    (oldPath : Option target.edges → List data.SourceEdge)
    (row : Option target.edges) (edge : data.SourceEdge) :
    (canonicalOldPathOccurrences star sourceBlock oldPath).count (row, edge) =
      if WallBlock.ofSheet data wall edge.1.2 = sourceBlock ∧
          some edge.1.1 ∈ canonicalW4OldColumns star then
        (oldPath row).count edge
      else 0 := by
  classical
  unfold canonicalOldPathOccurrences
  rw [← Multiset.coe_countAddMonoidHom]
  rw [map_sum]
  rw [Multiset.coe_countAddMonoidHom]
  by_cases hColumn : some edge.1.1 ∈ canonicalW4OldColumns star
  · rw [Finset.sum_eq_single (some edge.1.1)]
    · rw [← Multiset.coe_countAddMonoidHom]
      rw [map_sum]
      rw [Multiset.coe_countAddMonoidHom]
      rw [Finset.sum_eq_single row]
      · unfold canonicalOldPathRowOccurrences
        simpa [hColumn] using
          (count_filterMap_tagged (oldPath row)
            (fun candidate ↦
              WallBlock.ofSheet data wall candidate.1.2 = sourceBlock ∧
                some edge.1.1 = some candidate.1.1)
            row edge)
      · intro other _hOther hne
        unfold canonicalOldPathRowOccurrences
        simp [hne]
      · simp
    · intro other _hOther hne
      rw [← Multiset.coe_countAddMonoidHom]
      rw [map_sum]
      rw [Multiset.coe_countAddMonoidHom]
      apply Finset.sum_eq_zero
      intro otherRow _hOtherRow
      unfold canonicalOldPathRowOccurrences
      simp [hne]
    · exact fun hNotMem ↦ (hNotMem hColumn).elim
  · rw [Finset.sum_eq_zero]
    · simp [hColumn]
    · intro column hColumnMem
      rw [← Multiset.coe_countAddMonoidHom]
      rw [map_sum]
      rw [Multiset.coe_countAddMonoidHom]
      apply Finset.sum_eq_zero
      intro otherRow _hOtherRow
      unfold canonicalOldPathRowOccurrences
      have hne : column ≠ some edge.1.1 := by
        intro hEq
        subst column
        exact hColumn hColumnMem
      simp [hne]

/-- Common retained stable paths and candidate-specific regrown-sheet paths.
The source construction obtains these lists from the stable graph `H(M)`; this
record keeps only their occurrence-sensitive output. -/
structure PathCensus (data : GluingDatum target degree) where
  oldPath : Option target.edges → List data.SourceEdge
  newSheets : Fin 3 → Option target.edges → List (Fin degree)

/-- An entirely dangling wall block has no retained old stable-path
occurrence and no regrown stable occurrence in any candidate. -/
structure DanglingBlockCensus
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    [DecidableEq target.edges]
    (paths : PathCensus data)
    (sourceBlock : WallBlock data wall) where
  marker : Unit := ()
  new_sheet_count : ∀ pairing row sheet,
    WallBlock.ofSheet data wall sheet = sourceBlock →
    (paths.newSheets pairing row).count sheet = 0
  old_path_count : ∀ row edge,
    WallBlock.ofSheet data wall edge.1.2 = sourceBlock →
    some edge.1.1 ∈ canonicalW4OldColumns star →
    (paths.oldPath row).count edge = 0

namespace DanglingBlockCensus

/-- Pointwise absence gives an empty canonical regrown-occurrence multiset. -/
theorem newSheetOccurrences
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    [DecidableEq target.edges]
    {paths : PathCensus data}
    {sourceBlock : WallBlock data wall}
    (census : DanglingBlockCensus data star paths sourceBlock)
    (pairing : Fin 3) :
    0 = canonicalNewSheetOccurrences sourceBlock
      (paths.newSheets pairing) := by
  ext occurrence
  rcases occurrence with ⟨row, sheet⟩
  rw [count_canonicalNewSheetOccurrences]
  by_cases hBlock : WallBlock.ofSheet data wall sheet = sourceBlock
  · simp [hBlock, census.new_sheet_count pairing row sheet hBlock]
  · simp [hBlock]

/-- Pointwise absence gives an empty canonical retained-old multiset. -/
theorem oldPathOccurrences
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    [DecidableEq target.edges]
    {paths : PathCensus data}
    {sourceBlock : WallBlock data wall}
    (census : DanglingBlockCensus data star paths sourceBlock) :
    0 = canonicalOldPathOccurrences star sourceBlock paths.oldPath := by
  ext occurrence
  rcases occurrence with ⟨row, edge⟩
  rw [count_canonicalOldPathOccurrences]
  by_cases hBlock : WallBlock.ofSheet data wall edge.1.2 = sourceBlock
  · by_cases hColumn : some edge.1.1 ∈ canonicalW4OldColumns star
    · simp [hBlock, hColumn,
        census.old_path_count row edge hBlock hColumn]
    · simp [hBlock, hColumn]
  · simp [hBlock]

/-- A dangling census lowers directly to the zero determinant branch. -/
noncomputable def canonicalBlockClassification
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    [DecidableEq target.edges]
    {paths : PathCensus data}
    {sourceBlock : WallBlock data wall}
    (census : DanglingBlockCensus data star paths sourceBlock)
    (blockPattern : BlockPattern)
    (hPattern : pattern sourceBlock.1 = blockPattern) :
    CanonicalBlockClassification data star pattern paths.oldPath
      paths.newSheets sourceBlock :=
  .zero blockPattern hPattern census.newSheetOccurrences
    census.oldPathOccurrences

end DanglingBlockCensus

/-- The canonical old source edge on one labelled W4 branch lies in the wall
block whose representative was used to select it. -/
theorem wallBlock_sourceEdge_anchor
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (sourceBlock : WallBlock data wall) (label : Fin 4) :
    WallBlock.ofSheet data wall
        (data.sourceEdge (star.edge label) sourceBlock.1).1.2 =
      sourceBlock := by
  apply Subtype.ext
  exact (star.edgePartition_refines_wall data label).rel
    ((data.edgePartition (star.edge label)).rel_repr_left sourceBlock.1) |>.trans
      sourceBlock.2

/-- A labelled W4 source edge belongs to the corresponding retained target
column. -/
theorem sourceEdge_column_mem
    (star : W4TargetPairings.FourStar target wall) [DecidableEq target.edges]
    (label : Fin 4) :
    some (star.edge label) ∈ canonicalW4OldColumns star := by
  simp [canonicalW4OldColumns]

/-- Literal source membership/count data for an nd2 block.  Counts are stated
before quotient-source edges are lifted to any outgoing candidate.  They say
that the two active old branch occurrences are the only stable occurrences
at this block, and that precisely the pairings separating them regrow one
occurrence. -/
structure Nd2BlockCensus
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    [DecidableEq target.edges]
    (paths : PathCensus data)
    (sourceBlock : WallBlock data wall) (block : Nd2Block) where
  newRow : Fin 3 → Option target.edges
  oldRow : Fin 4 → Option target.edges
  new_sheet_count : ∀ pairing row sheet,
    WallBlock.ofSheet data wall sheet = sourceBlock →
    (paths.newSheets pairing row).count sheet =
      if W4TargetPairings.Pairing.labelRight pairing block.first =
          W4TargetPairings.Pairing.labelRight pairing block.second then
        0
      else if row = newRow pairing ∧ sheet = sourceBlock.1 then 1 else 0
  old_path_count : ∀ row edge,
    WallBlock.ofSheet data wall edge.1.2 = sourceBlock →
    some edge.1.1 ∈ canonicalW4OldColumns star →
    (paths.oldPath row).count edge =
      ({(oldRow block.first,
          data.sourceEdge (star.edge block.first) sourceBlock.1),
        (oldRow block.second,
          data.sourceEdge (star.edge block.second) sourceBlock.1)} :
        Multiset (Option target.edges × data.SourceEdge)).count (row, edge)
  new_row : ∀ pairing,
    W4TargetPairings.Pairing.labelRight pairing block.first ≠
      W4TargetPairings.Pairing.labelRight pairing block.second →
    newRow pairing = oldRow block.first
  old_row : oldRow block.first = oldRow block.second

namespace Nd2BlockCensus

/-- The source-level nd2 count census proves the exact occurrence multiset
consumed by the canonical W4 lowering. -/
theorem newSheetOccurrences
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    [DecidableEq target.edges]
    {paths : PathCensus data}
    {sourceBlock : WallBlock data wall} {block : Nd2Block}
    (census : Nd2BlockCensus data star paths sourceBlock block)
    (pairing : Fin 3) :
    (if W4TargetPairings.Pairing.labelRight pairing block.first =
          W4TargetPairings.Pairing.labelRight pairing block.second then 0
      else {(census.newRow pairing, sourceBlock.1)}) =
        canonicalNewSheetOccurrences sourceBlock
          (paths.newSheets pairing) := by
  classical
  apply Multiset.ext.mpr
  intro occurrence
  rcases occurrence with ⟨row, sheet⟩
  rw [count_canonicalNewSheetOccurrences]
  by_cases hBlock : WallBlock.ofSheet data wall sheet = sourceBlock
  · rw [ite_eq_left hBlock, census.new_sheet_count pairing row sheet hBlock]
    by_cases hSame :
        W4TargetPairings.Pairing.labelRight pairing block.first =
          W4TargetPairings.Pairing.labelRight pairing block.second
    · simp [hSame]
    · rw [ite_eq_right hSame, Multiset.count_singleton]
      by_cases hRow : row = census.newRow pairing
      · by_cases hSheet : sheet = sourceBlock.1
        · simp [hRow, hSheet]
          exact hSame
        · simp [hRow, hSheet]
      · simp [hRow]
  · rw [ite_eq_right hBlock]
    by_cases hSame :
        W4TargetPairings.Pairing.labelRight pairing block.first =
          W4TargetPairings.Pairing.labelRight pairing block.second
    · simp [hSame]
    · have hPair : (row, sheet) ≠ (census.newRow pairing, sourceBlock.1) := by
        intro hEq
        have hSheet : sheet = sourceBlock.1 := congrArg Prod.snd hEq
        subst sheet
        exact hBlock (WallBlock.ofSheet_anchor data wall sourceBlock)
      simp [hSame, hPair]

/-- The source-level nd2 count census likewise proves that the two active old
branches, with their stable rows, are exactly the retained W4 occurrences of
this wall block. -/
theorem oldPathOccurrences
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    [DecidableEq target.edges]
    {paths : PathCensus data}
    {sourceBlock : WallBlock data wall} {block : Nd2Block}
    (census : Nd2BlockCensus data star paths sourceBlock block) :
    {(census.oldRow block.first,
        data.sourceEdge (star.edge block.first) sourceBlock.1),
      (census.oldRow block.second,
        data.sourceEdge (star.edge block.second) sourceBlock.1)} =
      canonicalOldPathOccurrences star sourceBlock paths.oldPath := by
  classical
  apply Multiset.ext.mpr
  intro occurrence
  rcases occurrence with ⟨row, edge⟩
  rw [count_canonicalOldPathOccurrences]
  by_cases hBlock : WallBlock.ofSheet data wall edge.1.2 = sourceBlock
  · by_cases hColumn : some edge.1.1 ∈ canonicalW4OldColumns star
    · rw [ite_eq_left ⟨hBlock, hColumn⟩]
      exact (census.old_path_count row edge hBlock hColumn).symm
    · rw [ite_eq_right (fun h ↦ hColumn h.2)]
      have hFirst :
          edge ≠ data.sourceEdge (star.edge block.first) sourceBlock.1 := by
        intro hEq
        subst edge
        exact hColumn (sourceEdge_column_mem star block.first)
      have hSecond :
          edge ≠ data.sourceEdge (star.edge block.second) sourceBlock.1 := by
        intro hEq
        subst edge
        exact hColumn (sourceEdge_column_mem star block.second)
      simp [hFirst, hSecond]
  · rw [ite_eq_right (fun h ↦ hBlock h.1)]
    have hFirst :
        edge ≠ data.sourceEdge (star.edge block.first) sourceBlock.1 := by
      intro hEq
      subst edge
      exact hBlock (wallBlock_sourceEdge_anchor data star sourceBlock block.first)
    have hSecond :
        edge ≠ data.sourceEdge (star.edge block.second) sourceBlock.1 := by
      intro hEq
      subst edge
      exact hBlock (wallBlock_sourceEdge_anchor data star sourceBlock block.second)
    simp [hFirst, hSecond]

/-- A literal nd2 stable-path census constructs the existing complete W4
block classification. -/
noncomputable def canonicalBlockClassification
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    [DecidableEq target.edges]
    {paths : PathCensus data}
    {sourceBlock : WallBlock data wall} {block : Nd2Block}
    (census : Nd2BlockCensus data star paths sourceBlock block)
    (hPattern : pattern sourceBlock.1 = .nd2 block) :
    CanonicalBlockClassification data star pattern paths.oldPath
      paths.newSheets sourceBlock :=
  .nd2 block hPattern census.newRow census.oldRow census.newSheetOccurrences
    census.oldPathOccurrences census.new_row census.old_row

end Nd2BlockCensus

/-- A canonical source edge through any sheet in a wall block remains assigned
to that wall block. -/
theorem wallBlock_sourceEdge_of_rel
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (sourceBlock : WallBlock data wall) (label : Fin 4)
    (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel sourceBlock.1 sheet) :
    WallBlock.ofSheet data wall
        (data.sourceEdge (star.edge label) sheet).1.2 = sourceBlock := by
  apply Subtype.ext
  exact (star.edgePartition_refines_wall data label).rel
    ((data.edgePartition (star.edge label)).rel_repr_left sheet) |>.trans
      (hSheet.symm.trans sourceBlock.2)

/-- Literal source membership/count data for an nd3 block.  The active sheets
are representatives of the three actual branch edge classes, not a possibly
unrelated representative of the larger wall vertex block. -/
structure Nd3BlockCensus
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    [DecidableEq target.edges]
    (paths : PathCensus data)
    (sourceBlock : WallBlock data wall) (block : Nd3Block) where
  activeSheet : Fin 4 → Fin degree
  active_sheet : ∀ label, label ∈ block.activeLabels →
    (data.vertexPartition wall).Rel sourceBlock.1 (activeSheet label)
  newRow : Fin 3 → Option target.edges
  oldRow : Fin 4 → Option target.edges
  new_sheet_count : ∀ pairing row sheet,
    WallBlock.ofSheet data wall sheet = sourceBlock →
    (paths.newSheets pairing row).count sheet =
      if row = newRow pairing ∧
          sheet = activeSheet (block.singletonLabel pairing) then 1 else 0
  old_path_count : ∀ row edge,
    WallBlock.ofSheet data wall edge.1.2 = sourceBlock →
    some edge.1.1 ∈ canonicalW4OldColumns star →
    (paths.oldPath row).count edge =
      ({(oldRow block.first,
          data.sourceEdge (star.edge block.first) (activeSheet block.first)),
        (oldRow block.second,
          data.sourceEdge (star.edge block.second) (activeSheet block.second)),
        (oldRow block.third,
          data.sourceEdge (star.edge block.third) (activeSheet block.third))} :
        Multiset (Option target.edges × data.SourceEdge)).count (row, edge)
  new_row : ∀ pairing,
    newRow pairing = oldRow (block.singletonLabel pairing)

namespace Nd3BlockCensus

/-- The nd3 count census proves the unique regrown occurrence selected by
each `2+2` target pairing. -/
theorem newSheetOccurrences
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    [DecidableEq target.edges]
    {paths : PathCensus data}
    {sourceBlock : WallBlock data wall} {block : Nd3Block}
    (census : Nd3BlockCensus data star paths sourceBlock block)
    (pairing : Fin 3) :
    {(census.newRow pairing,
        census.activeSheet (block.singletonLabel pairing))} =
      canonicalNewSheetOccurrences sourceBlock
        (paths.newSheets pairing) := by
  classical
  apply Multiset.ext.mpr
  intro occurrence
  rcases occurrence with ⟨row, sheet⟩
  rw [count_canonicalNewSheetOccurrences]
  by_cases hBlock : WallBlock.ofSheet data wall sheet = sourceBlock
  · rw [ite_eq_left hBlock, census.new_sheet_count pairing row sheet hBlock]
    rw [Multiset.count_singleton]
    by_cases hRow : row = census.newRow pairing
    · by_cases hSheet :
          sheet = census.activeSheet (block.singletonLabel pairing)
      · simp [hRow, hSheet]
      · simp [hRow, hSheet]
    · simp [hRow]
  · rw [ite_eq_right hBlock]
    have hActive := census.active_sheet (block.singletonLabel pairing)
      (block.singletonLabel_mem_activeLabels pairing)
    have hSelectedBlock :
        WallBlock.ofSheet data wall
            (census.activeSheet (block.singletonLabel pairing)) =
          sourceBlock := by
      apply Subtype.ext
      exact hActive.symm.trans sourceBlock.2
    have hPair :
        (row, sheet) ≠
          (census.newRow pairing,
            census.activeSheet (block.singletonLabel pairing)) := by
      intro hEq
      have hSheet :
          sheet = census.activeSheet (block.singletonLabel pairing) :=
        congrArg Prod.snd hEq
      subst sheet
      exact hBlock hSelectedBlock
    simp [hPair]

/-- The nd3 count census proves that its three explicitly represented active
branches are exactly the retained W4 occurrences of this wall block. -/
theorem oldPathOccurrences
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    [DecidableEq target.edges]
    {paths : PathCensus data}
    {sourceBlock : WallBlock data wall} {block : Nd3Block}
    (census : Nd3BlockCensus data star paths sourceBlock block) :
    {(census.oldRow block.first,
        data.sourceEdge (star.edge block.first) (census.activeSheet block.first)),
      (census.oldRow block.second,
        data.sourceEdge (star.edge block.second) (census.activeSheet block.second)),
      (census.oldRow block.third,
        data.sourceEdge (star.edge block.third) (census.activeSheet block.third))} =
      canonicalOldPathOccurrences star sourceBlock paths.oldPath := by
  classical
  apply Multiset.ext.mpr
  intro occurrence
  rcases occurrence with ⟨row, edge⟩
  rw [count_canonicalOldPathOccurrences]
  by_cases hBlock : WallBlock.ofSheet data wall edge.1.2 = sourceBlock
  · by_cases hColumn : some edge.1.1 ∈ canonicalW4OldColumns star
    · rw [ite_eq_left ⟨hBlock, hColumn⟩]
      exact (census.old_path_count row edge hBlock hColumn).symm
    · rw [ite_eq_right (fun h ↦ hColumn h.2)]
      have hFirst :
          edge ≠ data.sourceEdge (star.edge block.first)
            (census.activeSheet block.first) := by
        intro hEq
        subst edge
        exact hColumn (sourceEdge_column_mem star block.first)
      have hSecond :
          edge ≠ data.sourceEdge (star.edge block.second)
            (census.activeSheet block.second) := by
        intro hEq
        subst edge
        exact hColumn (sourceEdge_column_mem star block.second)
      have hThird :
          edge ≠ data.sourceEdge (star.edge block.third)
            (census.activeSheet block.third) := by
        intro hEq
        subst edge
        exact hColumn (sourceEdge_column_mem star block.third)
      simp [hFirst, hSecond, hThird]
  · rw [ite_eq_right (fun h ↦ hBlock h.1)]
    have hFirstBlock := wallBlock_sourceEdge_of_rel data star sourceBlock
      block.first (census.activeSheet block.first)
      (census.active_sheet block.first (by simp [Nd3Block.activeLabels]))
    have hSecondBlock := wallBlock_sourceEdge_of_rel data star sourceBlock
      block.second (census.activeSheet block.second)
      (census.active_sheet block.second (by simp [Nd3Block.activeLabels]))
    have hThirdBlock := wallBlock_sourceEdge_of_rel data star sourceBlock
      block.third (census.activeSheet block.third)
      (census.active_sheet block.third (by simp [Nd3Block.activeLabels]))
    have hFirst :
        edge ≠ data.sourceEdge (star.edge block.first)
          (census.activeSheet block.first) := by
      intro hEq
      subst edge
      exact hBlock hFirstBlock
    have hSecond :
        edge ≠ data.sourceEdge (star.edge block.second)
          (census.activeSheet block.second) := by
      intro hEq
      subst edge
      exact hBlock hSecondBlock
    have hThird :
        edge ≠ data.sourceEdge (star.edge block.third)
          (census.activeSheet block.third) := by
      intro hEq
      subst edge
      exact hBlock hThirdBlock
    simp [hFirst, hSecond, hThird]

/-- A literal nd3 stable-path census constructs the existing complete W4
block classification. -/
noncomputable def canonicalBlockClassification
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    [DecidableEq target.edges]
    {paths : PathCensus data}
    {sourceBlock : WallBlock data wall} {block : Nd3Block}
    (census : Nd3BlockCensus data star paths sourceBlock block)
    (hPattern : pattern sourceBlock.1 = .nd3 block) :
    CanonicalBlockClassification data star pattern paths.oldPath
      paths.newSheets sourceBlock :=
  .nd3 block hPattern census.activeSheet census.active_sheet census.newRow
    census.oldRow census.newSheetOccurrences census.oldPathOccurrences
    census.new_row

end Nd3BlockCensus

/-- The literal source census required by the active-label classification of
one wall block.  The return type is chosen canonically by
`ActiveBranchProfile.classification`; the source does not select another
`BlockPattern`. -/
def ExpectedBlockCensus
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    [DecidableEq target.edges]
    (active : ActiveBranchProfile data star)
    (paths : PathCensus data)
    (sourceBlock : WallBlock data wall) : Type :=
  match active.classification sourceBlock with
  | .dangling _ => DanglingBlockCensus data star paths sourceBlock
  | .nd2 block _ => Nd2BlockCensus data star paths sourceBlock block
  | .nd3 block _ => Nd3BlockCensus data star paths sourceBlock block

namespace ExpectedBlockCensus

/-- Lower either literal source census to the canonical block classification
already consumed by `GlobalW4`. -/
noncomputable def canonicalBlockClassification
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    [DecidableEq target.edges]
    {active : ActiveBranchProfile data star}
    {paths : PathCensus data}
    {sourceBlock : WallBlock data wall}
    (census : ExpectedBlockCensus data star active paths sourceBlock) :
    CanonicalBlockClassification data star active.blockPattern paths.oldPath
      paths.newSheets sourceBlock := by
  cases hClassification : active.classification sourceBlock with
  | dangling hActive =>
      have hPattern : active.blockPattern sourceBlock.1 =
          ActiveBlockClassification.pattern (.dangling hActive) := by
        rw [active.blockPattern_anchor sourceBlock, hClassification]
      unfold ExpectedBlockCensus at census
      rw [hClassification] at census
      exact census.canonicalBlockClassification _ hPattern
  | nd2 block hActive =>
      have hPattern : active.blockPattern sourceBlock.1 = .nd2 block := by
        rw [active.blockPattern_anchor sourceBlock, hClassification]
        rfl
      unfold ExpectedBlockCensus at census
      rw [hClassification] at census
      exact census.canonicalBlockClassification hPattern
  | nd3 block hActive =>
      have hPattern : active.blockPattern sourceBlock.1 = .nd3 block := by
        rw [active.blockPattern_anchor sourceBlock, hClassification]
        rfl
      unfold ExpectedBlockCensus at census
      rw [hClassification] at census
      exact census.canonicalBlockClassification hPattern

end ExpectedBlockCensus

/-- One common stable-path enumeration and a source-local nd2/nd3 count census
for every old wall block. -/
structure FamilyCensus
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    [DecidableEq target.edges]
    (active : ActiveBranchProfile data star) where
  paths : PathCensus data
  block : ∀ sourceBlock : WallBlock data wall,
    ExpectedBlockCensus data star active paths sourceBlock

/-- W4 semantic family from the source's active-branch profile and literal
stable-path multiplicity census.  This endpoint does not ask the source to
state `CanonicalBlockClassification` or either downstream multiset equality. -/
noncomputable def presentedFamilyOfStablePathCensus
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    [DecidableEq target.edges]
    (hValid : data.Valid)
    (active : ActiveBranchProfile data star)
    (hChangeZero :
      ∑ sourceBlock : WallBlock data wall,
        AuxR0Profile.wallBlockRamification data star sourceBlock = 0)
    (census : FamilyCensus data star active) :
    PresentedFamily (coordinate := Option target.edges) 3 data wall :=
  presentedFamilyOfActiveBranches data star hValid active hChangeZero
    census.paths.oldPath census.paths.newSheets fun sourceBlock ↦
      (census.block sourceBlock).canonicalBlockClassification

end DraismaVargas.LocalCases.W4StablePathCensus
