import DraismaVargasCount.SpineRowLengthWitness
import DraismaVargasCount.PassOnceLollipopWitness

/-!
# The spine rows of `A_φ`: the single-column property, and where it lives

**Source.**  Vargas, Part II (arXiv:2609.09109), the proof of
`lm:combinatorial-structure-caterpillar-of-loops`: each path edge `h_i` contains a single
edge of `G`, so the edge-length matrix `A_φ` is diagonal.

`Count/SpineRowLengthWitness.lean` reduces this, for a caterpillar member, to two
statements: the loop-leaf adjacency `LoopLeafAdjacent` at every loop, and the separation of
the spine columns.  `LoopLeafAdjacent` is proved in `PassOnceLollipopWitness`, so §1--§3
below carry the statements of `SpineRowLengthWitness` over with no hypothesis, and §4
restates what is left in a form that mentions no lollipop at all.

## Three observations

1. **There is no analogue of the loop-leaf adjacency for a spine row, and there cannot be
   one of the same shape.**  Its mechanism is a descent (`PassOnceLollipop`
   §2--§7): if the loop row were longer than two, the *two* surviving
   occurrences above one and the same target edge --- the leaf edge, whose
   fibre `LeafFibre.leafSurvivors_card` pins at exactly two --- would sit at
   two distinct interior walk vertices, and the local analysis at their common
   target vertex contradicts `fd.det_ne_zero`.  Every step of that
   argument needs a target edge the row passes above **twice**.  A spine row
   passes above no edge twice: it is leaf-avoiding
   (`SpineRowLengthWitness.exists_loopSlot_of_passesAboveLeaf`), hence
   target-injective by
   `SharpRowDenominator.rowFibre_eq_singleton_of_not_passesAboveLeaf`.  So the
   spine obligation is not "the row does not repeat a column" --- that is
   already proved --- but "the row does not occupy a *second* column", which no
   single-row argument can see: §5's
   `exists_meets_common_column_of_two_le_rowSupport` shows the second column is
   necessarily shared with another free row.  The spine half of the single-column
   property is a statement about *pairs* of rows; the loop half was a statement about one.
2. **Counting alone is circular.**  `SpineRowLengthWitness.freeRows_card` is an equation
   (`g - 3` free rows) and `spineColumns_card_le` an inequality (`≤ g - 3`
   columns) in the same quantity; `g - 3` nonempty supports inside `g - 3`
   columns force singletons **only** given pairwise disjointness, which is the
   obligation itself.  §5 proves exactly that implication, and its
   contrapositive, so the direction of the inequality is usable but only with
   the separation in hand.
3. **What is left is one sentence**, §4's
   `LeafAvoidingSeparated`: *distinct leaf-avoiding rows never meet a common
   column.*  No `LoopLeafAdjacent`, no lollipop edge set, no `hOff` carve-out for the
   bridge columns, no edge budget.

## What is proved

* §0 `passesAboveLeaf_of_meets_leafEdge`; `rowSingleColumn_iff_rowSupport_eq_singleton`
  --- the single-column predicate **is** "the row support of `A_φ` is a singleton", which
  is the dictionary between `Count/SpineOffDiagonal.lean` §1 and §3.
* §1 `loopLeafAdjacent_all` --- `LoopLeafAdjacent` at every self-loop slot of
  `catCore m`, from `PassOnceLollipopWitness.loopLeafAdjacent`, in the shape the statements
  of `SpineRowLengthWitness` take as a hypothesis.
* §2 `rowSingleColumn_loopRow` --- **a loop row of a caterpillar member meets
  only its own leaf column**, unconditionally; then
  `targetEdge_eq_loopLeafEdge_of_meets_loopRow`,
  `not_passesAboveLeaf_of_meets`, `not_passesAboveLeaf_of_freeRow`.
* §3 `meets_row_unique_loopBridgeEdge`, `lollipopEdges_card`,
  `notMem_lollipopEdges_of_meets`, `spineColumns_card_le` ---
  `Count/SpineRowLengthWitness.lean` §3--§5 with `LoopLeafAdjacent` discharged.
* §4 `LeafAvoidingSeparated` and `meets_row_unique_of_leafAvoiding`,
  `exists_rowSingleColumn_of_leafAvoiding`,
  `card_rowEdges_eq_one_of_not_passesAboveLeaf`,
  `exists_perm_member_matrix_diagonal_of_leafAvoiding` --- the remaining statement, and
  everything the spine argument wants from it: `hOff` on **every** column, the
  single-column property on every row, Part II's spine bound, and `A_φ` monomial.
  `leafAvoidingSeparated_iff_freeColumnsSeparated` proves it equivalent to
  `SpineRowLengthWitness.FreeColumnsSeparated`, so nothing has been strengthened.
* §5 `rowSupport_card_eq_one_of_free_of_separated`,
  `exists_rowSingleColumn_free_of_separated`,
  `card_rowEdges_eq_one_of_free_of_separated` --- Part II's count, run in the
  direction that works: separation of the free rows plus the edge budget plus
  `freeRows_card` gives singletons **without** going through the column map.
  `exists_meets_common_column_of_two_le_rowSupport` is its contrapositive: a
  free row with two columns forces two distinct free rows onto one column.
* §6 `exists_third_survivor`, `not_isLeafVertex_of_branch`,
  `target_ne_of_branch_of_trivalent`, `incidentEdges_card_branch` --- **where
  the concatenated spine walk can backtrack.**  No branch vertex of the source
  lies above a leaf; above a *trivalent* target vertex the three surviving
  occurrences at a branch vertex have pairwise distinct target images, because
  the change budget there is `3 - 3 = 0`
  (`PassOnceLollipop.localRamification_eq_zero_of_trivalent` and
  `not_three_survivors_sharing_direction`).  So Part II's *"since `T` is a
  tree, `φ` is injective on `P`"* can fail only at a branch vertex lying above
  a **divalent** target vertex --- which is exactly what the loop branch
  vertices are (`LollipopDivalent.loopImage_divalent`), where the sharing pair
  is the hairpin and lies on one row.

## What is not proved here

* **`LeafAvoidingSeparated` is not proved here.**  It is
  `SpineRowLengthWitness.FreeColumnsSeparated` in another form (§4, proved equivalent).
  Every statement of §4 and §5 carries it, or the free-row form of it, as a hypothesis.
  It is proved at every member in `TrivalentFibreUnique`
  (`TrivalentFibreUnique.leafAvoidingSeparated`), through the reduction of
  `BranchSharedDirection`.
* **Nothing here concatenates two rows.**  §6 supplies the *local*
  non-backtracking datum at a trivalent-image joint and nothing more; the
  transfer from a non-backtracking chain to distinct target images,
  `RowGeodesic.isWalkFrom_of_isChain`, hard-codes
  `nonDanglingValency data meet = 2` in its chain relation and therefore cannot
  be applied across a branch vertex.  A branch-vertex version of that lemma
  (which must additionally exclude a third occurrence of the walk at the joint)
  is not a corollary of it; `TrivalentFibreUnique` avoids the walk altogether, by a count
  and a tree rank.
* **The divalent-image branch vertices are not treated here.**  At a branch vertex
  above a divalent target vertex two of the three survivors share a direction;
  that those two lie on a common stable row is `BranchSharedDirection`.
* **No census of divalent images, no spine path, no genus-four hypothesis.**  Nothing
  below mentions `divalentCount`, `SpinePath`, a walk, `Neigh`, a slope or a ballot
  sequence.  `lollipopEdges_card` and `spineColumns_card_le` in §3 and every
  statement of §5 take `1 ≤ m`, inherited from
  `SpineRowLengthWitness.lollipopEdges_card` and `freeRows_card`; §0, §1, §2,
  §4 and §6 take no numerical hypothesis.
* Nothing below mentions `Open`, `HasOddMult`, `GeometricFibre`,
  `openOddCount`, `BallotFamily`, `BallotClassification` or genericity of the
  request: every member-level statement is about an arbitrary
  `FibreMember (catCore m) request (m + 2)`, and §0 and §6 are about an
  arbitrary full-dimensional presentation over an arbitrary target.
-/

namespace DraismaVargas.Count.SpineSingleColumn

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.FibreCaterpillar
open DraismaVargas.Count.LeafFibre
open DraismaVargas.Count.EdgeDenominator
open DraismaVargas.Count.RowWalk
open DraismaVargas.Count.SpineOffDiagonal
open DraismaVargas.Count.SpineRowLength
open DraismaVargas.Count.SpineRowLengthWitness
open Utilities.Certificate.ExplicitPotential (Core)

/-! ## 0.  Two generic dictionary lemmas -/

section Generic

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **A row meeting a leaf column passes above that leaf.** -/
theorem passesAboveLeaf_of_meets_leafEdge
    (fd : FullDimensionalSourcePresentation data coordinate)
    {vertex : target.V} (hLeaf : IsLeafVertex target vertex)
    {sourceRow column : coordinate}
    (hColumn : fd.labelling.targetEdge column = leafEdge hLeaf)
    (hMeets : Meets fd.labelling sourceRow column) :
    PassesAboveLeaf fd.labelling sourceRow := by
  obtain ⟨edge, hEdge, hTarget⟩ := hMeets
  refine ⟨edge, hEdge, vertex, hLeaf, ?_⟩
  rw [hTarget, hColumn]
  exact leafEdge_mem hLeaf

/-- **`RowSingleColumn` is "the row support is a singleton".**  The support is
the set of columns in which the length matrix is nonzero
(`SpineOffDiagonal.rowSupport`), so this is the dictionary between the single-column
predicate and the linear algebra of §1 of `Count/SpineOffDiagonal.lean`. -/
theorem rowSingleColumn_iff_rowSupport_eq_singleton
    (fd : FullDimensionalSourcePresentation data coordinate) (sourceRow column : coordinate) :
    RowSingleColumn fd.labelling sourceRow column ↔
      rowSupport (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation)
        sourceRow = {column} := by
  classical
  constructor
  · intro hSingle
    ext c
    rw [mem_rowSupport, Finset.mem_singleton, matrix_ne_zero_iff_meets]
    constructor
    · intro hMeets
      by_contra hne
      exact not_meets_of_rowSingleColumn hSingle hne hMeets
    · rintro rfl
      exact meets_of_rowSingleColumn hSingle
  · intro hSupport edge hEdge
    have hMeets : Meets fd.labelling sourceRow
        (fd.labelling.targetEdge.symm edge.1.1) :=
      ⟨edge, hEdge, by rw [Equiv.apply_symm_apply]⟩
    have hMem : fd.labelling.targetEdge.symm edge.1.1 ∈
        rowSupport (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation)
          sourceRow :=
      mem_rowSupport.mpr ((matrix_ne_zero_iff_meets fd.labelling _ _).mpr hMeets)
    rw [hSupport, Finset.mem_singleton] at hMem
    rw [← hMem, Equiv.apply_symm_apply]

end Generic

variable {m : ℕ} {request : Fin (6 * m + 3) → ℚ}

/-! ## 1.  `LoopLeafAdjacent` discharged -/

theorem loopLeafAdjacent_all (member : FibreMember (catCore m) request (m + 2)) :
    ∀ (slot : Fin (6 * m + 3)) (hLoop : (catCore m).tail slot = (catCore m).head slot),
      LollipopBridgeFibreWitness.LoopLeafAdjacent member hLoop :=
  fun _ hLoop ↦ PassOnceLollipopWitness.loopLeafAdjacent member hLoop

/-! ## 2.  A loop row meets only its own leaf column -/

theorem rowSingleColumn_loopRow (member : FibreMember (catCore m) request (m + 2))
    {slot : Fin (6 * m + 3)} (hLoop : (catCore m).tail slot = (catCore m).head slot) :
    RowSingleColumn member.fullDim.labelling (loopRowIndex member slot)
      (member.fullDim.labelling.targetEdge.symm (loopLeafEdge member hLoop)) := by
  have hCard := (RowSingleColumnProof.card_rowEdges_core_loop_iff member hLoop).mp
    (PassOnceLollipopWitness.exists_rowSingleColumn_core_loop member hLoop)
  have hLeafRow := LollipopLeafRow.leafRow_loopLeaf member hLoop
  rw [← hLeafRow] at hCard
  have hSingle := (RowSingleColumnProof.rowSingleColumn_leafRow_iff member.fullDim
    (LollipopLeafRow.loopLeaf_isLeafVertex member hLoop)).mpr hCard
  rw [hLeafRow] at hSingle
  exact hSingle

theorem targetEdge_eq_loopLeafEdge_of_meets_loopRow
    (member : FibreMember (catCore m) request (m + 2))
    {slot : Fin (6 * m + 3)} (hLoop : (catCore m).tail slot = (catCore m).head slot)
    {column : Fin (6 * m + 3)}
    (hMeets : Meets member.fullDim.labelling (loopRowIndex member slot) column) :
    member.fullDim.labelling.targetEdge column = loopLeafEdge member hLoop := by
  obtain ⟨edge, hEdge, hTarget⟩ := hMeets
  have hSingle := rowSingleColumn_loopRow member hLoop edge hEdge
  rw [Equiv.apply_symm_apply] at hSingle
  exact hTarget.symm.trans hSingle

theorem not_passesAboveLeaf_of_meets (member : FibreMember (catCore m) request (m + 2))
    {sourceRow column : Fin (6 * m + 3)}
    (hColumn : ∀ (slot : Fin (6 * m + 3))
      (hLoop : (catCore m).tail slot = (catCore m).head slot),
      member.fullDim.labelling.targetEdge column ≠ loopLeafEdge member hLoop)
    (hMeets : Meets member.fullDim.labelling sourceRow column) :
    ¬ PassesAboveLeaf member.fullDim.labelling sourceRow := by
  intro hPasses
  obtain ⟨slot, hLoop, hRow⟩ := exists_loopSlot_of_passesAboveLeaf member hPasses
  subst hRow
  exact hColumn slot hLoop (targetEdge_eq_loopLeafEdge_of_meets_loopRow member hLoop hMeets)

theorem not_passesAboveLeaf_of_freeRow (member : FibreMember (catCore m) request (m + 2))
    {sourceRow : Fin (6 * m + 3)} (hFree : FreeRow member sourceRow) :
    ¬ PassesAboveLeaf member.fullDim.labelling sourceRow := by
  intro hPasses
  obtain ⟨slot, hLoop, hRow⟩ := exists_loopSlot_of_passesAboveLeaf member hPasses
  exact hFree.1 slot hLoop hRow

/-! ## 3.  `Count/SpineRowLengthWitness.lean` with `LoopLeafAdjacent` discharged -/

/-- **`hOff` on a lollipop bridge column, unconditionally.** -/
theorem meets_row_unique_loopBridgeEdge (member : FibreMember (catCore m) request (m + 2))
    {slot : Fin (6 * m + 3)} (hLoop : (catCore m).tail slot = (catCore m).head slot)
    {sourceRow sourceRow' column : Fin (6 * m + 3)}
    (hColumn : member.fullDim.labelling.targetEdge column = loopBridgeEdge member hLoop)
    (hMeets : Meets member.fullDim.labelling sourceRow column)
    (hMeets' : Meets member.fullDim.labelling sourceRow' column) :
    sourceRow = sourceRow' :=
  SpineRowLength.meets_row_unique_loopBridgeEdge member hLoop
    (loopLeafAdjacent_all member slot hLoop) hColumn hMeets hMeets'

/-- **The `2g` lollipop edges are `2g` in number, unconditionally.** -/
theorem lollipopEdges_card (hm : 1 ≤ m) (member : FibreMember (catCore m) request (m + 2)) :
    (SpineRowLengthWitness.lollipopEdges m member).card = 2 * (2 * m + 2) :=
  SpineRowLengthWitness.lollipopEdges_card m hm member (loopLeafAdjacent_all member)

/-- **A column met by a free row is not a lollipop edge, unconditionally.** -/
theorem notMem_lollipopEdges_of_meets (member : FibreMember (catCore m) request (m + 2))
    {sourceRow column : Fin (6 * m + 3)} (hFree : FreeRow member sourceRow)
    (hMeets : Meets member.fullDim.labelling sourceRow column) :
    member.fullDim.labelling.targetEdge column ∉ SpineRowLengthWitness.lollipopEdges m member :=
  SpineRowLengthWitness.notMem_lollipopEdges_of_meets m member
    (loopLeafAdjacent_all member) hFree hMeets

/-- **Part II's `|φ(P)| ≤ g - 3`, unconditionally.** -/
theorem spineColumns_card_le (hm : 1 ≤ m) (member : FibreMember (catCore m) request (m + 2))
    (columns : Finset (Fin (6 * m + 3)))
    (hColumns : ∀ column ∈ columns, ∃ sourceRow, FreeRow member sourceRow ∧
      Meets member.fullDim.labelling sourceRow column) :
    columns.card + 3 ≤ 2 * m + 2 :=
  SpineRowLengthWitness.spineColumns_card_le m hm member (loopLeafAdjacent_all member)
    columns hColumns

/-! ## 4.  `LeafAvoidingSeparated`, with the lollipop vocabulary eliminated -/

/-- **Distinct leaf-avoiding rows never meet a common column** -- the statement the
single-column property of the spine rows reduces to.

This is `SpineRowLengthWitness.FreeColumnsSeparated` with both side conditions
on the column -- "not a lollipop leaf edge", "not a lollipop bridge edge", each
of which needed `LoopLeafAdjacent` to exploit -- traded for a single condition on the two
rows.  §4's `leafAvoidingSeparated_iff_freeColumnsSeparated` proves the two
equivalent.  It holds at every member (`TrivalentFibreUnique.leafAvoidingSeparated`). -/
def LeafAvoidingSeparated (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2)) : Prop :=
  ∀ sourceRow sourceRow' column : Fin (6 * m + 3),
    ¬ PassesAboveLeaf member.fullDim.labelling sourceRow →
    ¬ PassesAboveLeaf member.fullDim.labelling sourceRow' →
    Meets member.fullDim.labelling sourceRow column →
    Meets member.fullDim.labelling sourceRow' column →
    sourceRow = sourceRow'

/-- **`hOff` on every column, from `LeafAvoidingSeparated` alone.**  The leaf columns are
`SpineRowLength.meets_row_unique_loopLeafEdge`, unconditional; on any other
column both rows are leaf-avoiding by §2, so `LeafAvoidingSeparated` applies.  No
`LoopLeafAdjacent`, and no case for the bridge columns. -/
theorem meets_row_unique_of_leafAvoiding (member : FibreMember (catCore m) request (m + 2))
    (hSep : LeafAvoidingSeparated m member)
    (sourceRow sourceRow' column : Fin (6 * m + 3))
    (hMeets : Meets member.fullDim.labelling sourceRow column)
    (hMeets' : Meets member.fullDim.labelling sourceRow' column) :
    sourceRow = sourceRow' := by
  by_cases hLeafColumn : ∃ (slot : Fin (6 * m + 3))
      (hLoop : (catCore m).tail slot = (catCore m).head slot),
      member.fullDim.labelling.targetEdge column = loopLeafEdge member hLoop
  · obtain ⟨slot, hLoop, hEq⟩ := hLeafColumn
    exact SpineRowLength.meets_row_unique_loopLeafEdge member hLoop hEq hMeets hMeets'
  · have hNe : ∀ (slot : Fin (6 * m + 3))
        (hLoop : (catCore m).tail slot = (catCore m).head slot),
        member.fullDim.labelling.targetEdge column ≠ loopLeafEdge member hLoop :=
      fun slot hLoop hEq ↦ hLeafColumn ⟨slot, hLoop, hEq⟩
    exact hSep sourceRow sourceRow' column
      (not_passesAboveLeaf_of_meets member hNe hMeets)
      (not_passesAboveLeaf_of_meets member hNe hMeets') hMeets hMeets'

/-- **The single-column property at an arbitrary caterpillar member, from
`LeafAvoidingSeparated` alone.** -/
theorem exists_rowSingleColumn_of_leafAvoiding
    (member : FibreMember (catCore m) request (m + 2))
    (hSep : LeafAvoidingSeparated m member) :
    ∃ σ : Fin (6 * m + 3) → Fin (6 * m + 3), Function.Bijective σ ∧
      ∀ sourceRow, RowSingleColumn member.fullDim.labelling sourceRow (σ sourceRow) :=
  SpineOffDiagonal.member_rowSingleColumn_of_meets_row_unique member
    (meets_row_unique_of_leafAvoiding member hSep)

/-- **The spine bound, from `LeafAvoidingSeparated` alone**: Part II's *"each path edge
`h_i` contains a single edge of `G`"*. -/
theorem card_rowEdges_eq_one_of_not_passesAboveLeaf
    (member : FibreMember (catCore m) request (m + 2))
    (hSep : LeafAvoidingSeparated m member) {sourceRow : Fin (6 * m + 3)}
    (hAvoid : ¬ PassesAboveLeaf member.fullDim.labelling sourceRow) :
    (rowEdges member.fullDim.labelling sourceRow).card = 1 := by
  obtain ⟨σ, -, hSingle⟩ := exists_rowSingleColumn_of_leafAvoiding member hSep
  exact RowSingleColumnProof.card_rowEdges_eq_one_of_rowSingleColumn_of_not_passesAboveLeaf
    member.fullDim hAvoid (hSingle sourceRow)

/-- **`A_φ` is a monomial matrix at an arbitrary caterpillar member, from
`LeafAvoidingSeparated` alone.**  The diagonal representatives of
`CaterpillarAllMembers.exists_diagonal_rep` are built from this. -/
theorem exists_perm_member_matrix_diagonal_of_leafAvoiding
    (member : FibreMember (catCore m) request (m + 2))
    (hSep : LeafAvoidingSeparated m member) :
    ∃ e : Equiv.Perm (Fin (6 * m + 3)),
      (∀ sourceRow column : Fin (6 * m + 3), column ≠ e sourceRow →
        member.matrix sourceRow column = 0) ∧
      (∀ sourceRow : Fin (6 * m + 3), member.matrix sourceRow (e sourceRow) ≠ 0) := by
  obtain ⟨σ, -, hSingle⟩ := exists_rowSingleColumn_of_leafAvoiding member hSep
  exact SpineOffDiagonal.exists_perm_member_matrix_diagonal member hSingle

/-- **The two forms agree.**  Left to right needs §2 (a loop row
meets only its own leaf column); right to left needs `LoopLeafAdjacent`, which §1
supplies. -/
theorem leafAvoidingSeparated_iff_freeColumnsSeparated
    (member : FibreMember (catCore m) request (m + 2)) :
    LeafAvoidingSeparated m member ↔ SpineRowLengthWitness.FreeColumnsSeparated m member := by
  constructor
  · intro hSep sourceRow sourceRow' column hNotLeaf _ hMeets hMeets'
    exact hSep sourceRow sourceRow' column
      (not_passesAboveLeaf_of_meets member hNotLeaf hMeets)
      (not_passesAboveLeaf_of_meets member hNotLeaf hMeets') hMeets hMeets'
  · intro hFree sourceRow sourceRow' column hAvoid _ hMeets hMeets'
    by_cases hLeafColumn : ∃ (slot : Fin (6 * m + 3))
        (hLoop : (catCore m).tail slot = (catCore m).head slot),
        member.fullDim.labelling.targetEdge column = loopLeafEdge member hLoop
    · obtain ⟨slot, hLoop, hEq⟩ := hLeafColumn
      exact absurd (passesAboveLeaf_of_meets_leafEdge member.fullDim
        (LollipopLeafRow.loopLeaf_isLeafVertex member hLoop) hEq hMeets) hAvoid
    by_cases hBridgeColumn : ∃ (slot : Fin (6 * m + 3))
        (hLoop : (catCore m).tail slot = (catCore m).head slot),
        member.fullDim.labelling.targetEdge column = loopBridgeEdge member hLoop
    · obtain ⟨slot, hLoop, hEq⟩ := hBridgeColumn
      exact meets_row_unique_loopBridgeEdge member hLoop hEq hMeets hMeets'
    · exact hFree sourceRow sourceRow' column
        (fun slot hLoop hEq ↦ hLeafColumn ⟨slot, hLoop, hEq⟩)
        (fun slot hLoop hEq ↦ hBridgeColumn ⟨slot, hLoop, hEq⟩) hMeets hMeets'

/-! ## 5.  Part II's count, in the only direction that is usable -/

theorem member_matrix_ne_zero_iff_meets (member : FibreMember (catCore m) request (m + 2))
    (sourceRow column : Fin (6 * m + 3)) :
    member.matrix sourceRow column ≠ 0 ↔
      Meets member.fullDim.labelling sourceRow column :=
  matrix_ne_zero_iff_meets member.fullDim.labelling sourceRow column

/-- **Part II's counting step, with its real hypothesis.**  `g - 3` free rows
with nonempty supports inside at most `g - 3` free columns force singletons
**only** once the supports are known to be pairwise disjoint; that separation is
supplied here as `hSep`.  Nothing but
`SpineOffDiagonal.rowSupport_nonempty` is taken from the determinant. -/
theorem rowSupport_card_eq_one_of_free_of_separated (hm : 1 ≤ m)
    (member : FibreMember (catCore m) request (m + 2))
    (hSep : ∀ first second column : Fin (6 * m + 3), FreeRow member first →
      FreeRow member second → Meets member.fullDim.labelling first column →
      Meets member.fullDim.labelling second column → first = second)
    {sourceRow : Fin (6 * m + 3)} (hFree : FreeRow member sourceRow) :
    (rowSupport member.matrix sourceRow).card = 1 := by
  classical
  have hmem : ∀ row : Fin (6 * m + 3),
      row ∈ (SpineRowLengthWitness.lollipopRows m member)ᶜ ↔ FreeRow member row := by
    intro row
    rw [Finset.mem_compl]
    exact (SpineRowLengthWitness.freeRow_iff_notMem_lollipopRows m member row).symm
  have hDisj : ∀ x ∈ (SpineRowLengthWitness.lollipopRows m member)ᶜ,
      ∀ y ∈ (SpineRowLengthWitness.lollipopRows m member)ᶜ, x ≠ y →
      Disjoint (rowSupport member.matrix x) (rowSupport member.matrix y) := by
    intro x hx y hy hne
    rw [Finset.disjoint_left]
    intro column hcx hcy
    exact hne (hSep x y column ((hmem x).mp hx) ((hmem y).mp hy)
      ((member_matrix_ne_zero_iff_meets member x column).mp (mem_rowSupport.mp hcx))
      ((member_matrix_ne_zero_iff_meets member y column).mp (mem_rowSupport.mp hcy)))
  have hBiUnion := Finset.card_biUnion hDisj
  have hCols : ∀ column ∈ (SpineRowLengthWitness.lollipopRows m member)ᶜ.biUnion
      (rowSupport member.matrix), ∃ row, FreeRow member row ∧
      Meets member.fullDim.labelling row column := by
    intro column hcolumn
    obtain ⟨row, hrow, hcol⟩ := Finset.mem_biUnion.mp hcolumn
    exact ⟨row, (hmem row).mp hrow,
      (member_matrix_ne_zero_iff_meets member row column).mp (mem_rowSupport.mp hcol)⟩
  have hLe := spineColumns_card_le hm member _ hCols
  have hRows := SpineRowLengthWitness.freeRows_card m hm member
  have hPos : ∀ row ∈ (SpineRowLengthWitness.lollipopRows m member)ᶜ,
      1 ≤ (rowSupport member.matrix row).card := fun row _ ↦
    Finset.card_pos.mpr (rowSupport_nonempty member.det_matrix_ne_zero row)
  have hSumLe : ∑ row ∈ (SpineRowLengthWitness.lollipopRows m member)ᶜ,
      (rowSupport member.matrix row).card
      ≤ (SpineRowLengthWitness.lollipopRows m member)ᶜ.card := by
    rw [← hBiUnion]; omega
  have hEq : ∑ _row ∈ (SpineRowLengthWitness.lollipopRows m member)ᶜ, 1 =
      ∑ row ∈ (SpineRowLengthWitness.lollipopRows m member)ᶜ,
        (rowSupport member.matrix row).card :=
    le_antisymm (Finset.sum_le_sum hPos) (by simpa using hSumLe)
  exact ((Finset.sum_eq_sum_iff_of_le hPos).mp hEq sourceRow ((hmem sourceRow).mpr hFree)).symm

/-- **The single-column property on the free rows, by Part II's count.**  Independent of
`meets_row_unique_of_leafAvoiding`: this route uses the edge budget of §3 and
the row count of `SpineRowLengthWitness.freeRows_card`, not the bijectivity of
the column map. -/
theorem exists_rowSingleColumn_free_of_separated (hm : 1 ≤ m)
    (member : FibreMember (catCore m) request (m + 2))
    (hSep : ∀ first second column : Fin (6 * m + 3), FreeRow member first →
      FreeRow member second → Meets member.fullDim.labelling first column →
      Meets member.fullDim.labelling second column → first = second)
    {sourceRow : Fin (6 * m + 3)} (hFree : FreeRow member sourceRow) :
    ∃ column, RowSingleColumn member.fullDim.labelling sourceRow column := by
  obtain ⟨column, hcolumn⟩ := Finset.card_eq_one.mp
    (rowSupport_card_eq_one_of_free_of_separated hm member hSep hFree)
  exact ⟨column, (rowSingleColumn_iff_rowSupport_eq_singleton member.fullDim sourceRow
    column).mpr hcolumn⟩

/-- **Part II's *"each path edge `h_i` contains a single edge of `G`"*, on the
free rows, by the count.** -/
theorem card_rowEdges_eq_one_of_free_of_separated (hm : 1 ≤ m)
    (member : FibreMember (catCore m) request (m + 2))
    (hSep : ∀ first second column : Fin (6 * m + 3), FreeRow member first →
      FreeRow member second → Meets member.fullDim.labelling first column →
      Meets member.fullDim.labelling second column → first = second)
    {sourceRow : Fin (6 * m + 3)} (hFree : FreeRow member sourceRow) :
    (rowEdges member.fullDim.labelling sourceRow).card = 1 := by
  obtain ⟨column, hcolumn⟩ := exists_rowSingleColumn_free_of_separated hm member hSep hFree
  exact RowSingleColumnProof.card_rowEdges_eq_one_of_rowSingleColumn_of_not_passesAboveLeaf
    member.fullDim (not_passesAboveLeaf_of_freeRow member hFree) hcolumn

/-- **The failure mode is always a shared column.**  If any free row of a
caterpillar member occupies two columns then two *distinct* free rows meet a
common column: the budget leaves no room for anything else.  So the single-column
property of the spine rows and their separation are the same statement, by counting
alone. -/
theorem exists_meets_common_column_of_two_le_rowSupport (hm : 1 ≤ m)
    (member : FibreMember (catCore m) request (m + 2))
    {sourceRow : Fin (6 * m + 3)} (hFree : FreeRow member sourceRow)
    (hCard : 2 ≤ (rowSupport member.matrix sourceRow).card) :
    ∃ first second column : Fin (6 * m + 3), first ≠ second ∧ FreeRow member first ∧
      FreeRow member second ∧ Meets member.fullDim.labelling first column ∧
      Meets member.fullDim.labelling second column := by
  by_contra hcon
  have hSep : ∀ first second column : Fin (6 * m + 3), FreeRow member first →
      FreeRow member second → Meets member.fullDim.labelling first column →
      Meets member.fullDim.labelling second column → first = second := by
    intro first second column hfirst hsecond hmeets hmeets'
    by_contra hne
    exact hcon ⟨first, second, column, hne, hfirst, hsecond, hmeets, hmeets'⟩
  have := rowSupport_card_eq_one_of_free_of_separated hm member hSep hFree
  omega

/-! ## 6.  Where the concatenated spine walk can backtrack -/

section Local

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- The surviving occurrences incident to a source vertex. -/
noncomputable def survivorsAt (data : GluingDatum target degree) (B : data.SourceVertex) :
    Finset (IncidentSourceEdge data B) := by
  classical
  exact (Finset.univ : Finset (IncidentSourceEdge data B)).filter
    fun item ↦ ¬ IsDangling data item.1

theorem card_survivorsAt (data : GluingDatum target degree) (B : data.SourceVertex) :
    (survivorsAt data B).card = nonDanglingValency data B :=
  StableLocalProperties.card_filter_not_isDangling_eq_nonDanglingValency data B

theorem survives_of_mem_survivorsAt {B : data.SourceVertex}
    {item : IncidentSourceEdge data B} (hMem : item ∈ survivorsAt data B) :
    ¬ IsDangling data item.1 :=
  (Finset.mem_filter.mp hMem).2

theorem mem_survivorsAt {B : data.SourceVertex} (item : IncidentSourceEdge data B)
    (hSurvives : ¬ IsDangling data item.1) : item ∈ survivorsAt data B :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSurvives⟩

/-- A source vertex of surviving valency three carries a third survivor beside
any two given ones. -/
theorem exists_third_survivor {B : data.SourceVertex}
    (hValency : nonDanglingValency data B = 3)
    {a b : data.SourceEdge} (hab : a ≠ b)
    (haS : ¬ IsDangling data a) (haI : Incident data a B)
    (hbS : ¬ IsDangling data b) (hbI : Incident data b B) :
    ∃ c : data.SourceEdge, c ≠ a ∧ c ≠ b ∧ ¬ IsDangling data c ∧ Incident data c B := by
  classical
  obtain ⟨itemA, hItemA⟩ : ∃ x : IncidentSourceEdge data B, x.1 = a := ⟨⟨a, haI⟩, rfl⟩
  obtain ⟨itemB, hItemB⟩ : ∃ x : IncidentSourceEdge data B, x.1 = b := ⟨⟨b, hbI⟩, rfl⟩
  have hNe : itemA ≠ itemB := fun h ↦ hab (hItemA ▸ hItemB ▸ congrArg Subtype.val h)
  have hCard : (survivorsAt data B).card = 3 := (card_survivorsAt data B).trans hValency
  have hAmem : itemA ∈ survivorsAt data B := mem_survivorsAt itemA (by rw [hItemA]; exact haS)
  have hBmem : itemB ∈ survivorsAt data B := mem_survivorsAt itemB (by rw [hItemB]; exact hbS)
  have hSub : ({itemA, itemB} : Finset (IncidentSourceEdge data B)) ⊆ survivorsAt data B := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact hAmem
    · rw [Finset.mem_singleton] at hx'
      exact hx' ▸ hBmem
  have hPair : ({itemA, itemB} : Finset (IncidentSourceEdge data B)).card = 2 := by
    rw [Finset.card_insert_of_notMem (fun h ↦ hNe (Finset.mem_singleton.mp h)),
      Finset.card_singleton]
  have hSS : ({itemA, itemB} : Finset (IncidentSourceEdge data B)) ⊂ survivorsAt data B := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hSub, fun hEq ↦ ?_⟩
    rw [hEq, hCard] at hPair
    omega
  obtain ⟨c, hcMem, hcNot⟩ := (Finset.ssubset_iff_of_subset hSub).mp hSS
  refine ⟨c.1, fun h ↦ hcNot ?_, fun h ↦ hcNot ?_, survives_of_mem_survivorsAt hcMem, c.2⟩
  · exact Finset.mem_insert.mpr (Or.inl (Subtype.ext (h.trans hItemA.symm)))
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
      (Subtype.ext (h.trans hItemB.symm))))

/-- **No branch vertex of the source lies above a leaf of the target.**  Its
three surviving occurrences would all lie above the leaf edge, of which
`LeafFibre.leafSurvivors_card` says there are exactly two. -/
theorem not_isLeafVertex_of_branch (fd : FullDimensionalSourcePresentation data coordinate)
    {B : data.SourceVertex} (hValency : nonDanglingValency data B = 3) :
    ¬ IsLeafVertex target B.1.1 := by
  classical
  intro hLeaf
  have hCard : (survivorsAt data B).card = 3 := (card_survivorsAt data B).trans hValency
  obtain ⟨itemA, hA, itemB, hB, hNe⟩ :=
    Finset.one_lt_card.mp (by rw [hCard]; omega : 1 < (survivorsAt data B).card)
  have haS := survives_of_mem_survivorsAt hA
  have hbS := survives_of_mem_survivorsAt hB
  have hab : itemA.1 ≠ itemB.1 := fun h ↦ hNe (Subtype.ext h)
  obtain ⟨c, hca, hcb, hcS, hcI⟩ :=
    exists_third_survivor hValency hab haS itemA.2 hbS itemB.2
  have hTarget : ∀ {x : data.SourceEdge}, Incident data x B →
      (x.1.1 : target.edges) = leafEdge hLeaf := fun {x} hx ↦
    eq_leafEdge_of_mem hLeaf ((incident_iff_target_mem_and_rel data x B).mp hx).1
  have hSub : ({itemA.1, itemB.1, c} : Finset data.SourceEdge) ⊆
      leafSurvivors (data := data) hLeaf := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact (mem_leafSurvivors hLeaf).mpr ⟨haS, hTarget itemA.2⟩
    · exact (mem_leafSurvivors hLeaf).mpr ⟨hbS, hTarget itemB.2⟩
    · exact (mem_leafSurvivors hLeaf).mpr ⟨hcS, hTarget hcI⟩
  have hThree := RowSingleColumnWitness.three_le_card_of_mem_of_ne
    (hSub (by simp)) (hSub (by simp)) (hSub (by simp))
    hab (Ne.symm hca) (Ne.symm hcb)
  rw [leafSurvivors_card (data := data) fd hLeaf] at hThree
  omega

/-- **Non-backtracking at a branch vertex above a trivalent target vertex.**
Distinct surviving occurrences at a source vertex of surviving valency three
whose image is trivalent have distinct target images.

This is the local input that Part II's concatenation of the spine rows needs at
a joint: the change budget above a trivalent target vertex is `3 - 3 = 0`, so
the block is unramified
(`PassOnceLollipop.localRamification_eq_zero_of_trivalent`), and an unramified
block of surviving valency three cannot have two survivors sharing a direction
(`PassOnceLollipop.not_three_survivors_sharing_direction`). -/
theorem target_ne_of_branch_of_trivalent
    (fd : FullDimensionalSourcePresentation data coordinate)
    {B : data.SourceVertex} (hTri : (GluingDatum.incidentEdges B.1.1).card = 3)
    (hValency : nonDanglingValency data B = 3)
    {a b : data.SourceEdge} (hab : a ≠ b)
    (haS : ¬ IsDangling data a) (haI : Incident data a B)
    (hbS : ¬ IsDangling data b) (hbI : Incident data b B) :
    (a.1.1 : target.edges) ≠ b.1.1 := by
  intro hShare
  obtain ⟨c, hca, hcb, hcS, hcI⟩ := exists_third_survivor hValency hab haS haI hbS hbI
  exact PassOnceLollipop.not_three_survivors_sharing_direction fd
    (PassOnceLollipop.localRamification_eq_zero_of_trivalent fd hTri _) hValency
    hab (Ne.symm hca) (Ne.symm hcb) haS haI hbS hbI hcS hcI hShare

/-- **The image of a branch vertex is divalent or trivalent.**  With
`target_ne_of_branch_of_trivalent`, the concatenated spine walk of Part II can
backtrack only at a branch vertex lying above a **divalent** target vertex. -/
theorem incidentEdges_card_branch (fd : FullDimensionalSourcePresentation data coordinate)
    {B : data.SourceVertex} (hValency : nonDanglingValency data B = 3) :
    (GluingDatum.incidentEdges B.1.1).card = 2 ∨
      (GluingDatum.incidentEdges B.1.1).card = 3 := by
  have hPos : 0 < (GluingDatum.incidentEdges B.1.1).card :=
    StableLocalProperties.incidentEdges_card_pos_of_changeMinimalAt data B.1.1
      (fd.changeMinimal B.1.1)
  have hLe : ((GluingDatum.incidentEdges B.1.1).card : ℤ) ≤ 3 := by
    have hRam := IndexPattern.localRamification_le_targetChange fd (wall := B.1.1) ⟨B.1.2, B.2⟩
    rw [IndexPattern.targetChange_eq_three_sub_valency fd B.1.1] at hRam
    have hNonneg := data.localRamification_nonneg B.1.1 (fd.valid.2 B.1.1) ⟨B.1.2, B.2⟩
    omega
  have hLe' : (GluingDatum.incidentEdges B.1.1).card ≤ 3 := by exact_mod_cast hLe
  have hNotOne : (GluingDatum.incidentEdges B.1.1).card ≠ 1 :=
    fun hOne ↦ not_isLeafVertex_of_branch fd hValency hOne
  omega

end Local

end DraismaVargas.Count.SpineSingleColumn
