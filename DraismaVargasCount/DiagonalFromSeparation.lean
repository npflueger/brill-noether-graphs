module

public import DraismaVargasCount.DiagonalClassification
public import DraismaVargasCount.BranchSharedDirection

@[expose] public section

/-!
# The `diagonal` field of `DiagonalClassification` from `LeafAvoidingSeparated`

The `diagonal` field of `Count.BallotSlopes.DiagonalClassification` asks for a diagonal
*representative* of each open odd class.
`BallotSlopes.diagonalRepresentatives_of_rowSingleColumn` shows that field is implied by
`SpineOffDiagonal.RowSingleColumn` on every open odd member, and
`SpineSingleColumn.exists_rowSingleColumn_of_leafAvoiding` reduces `RowSingleColumn` at a
caterpillar member to the single sentence `SpineSingleColumn.LeafAvoidingSeparated`.  This
module joins the two, so the `diagonal` field costs exactly `LeafAvoidingSeparated`: the
global half of the injectivity of the spine path in Part II's
`lm:combinatorial-structure-caterpillar-of-loops` (Vargas, arXiv:2609.09109).

## What is proved

* `diagonal_of_leafAvoidingSeparated` -- **the `diagonal` field from
  `LeafAvoidingSeparated` alone.**
* `diagonalClassification_of_leafAvoidingSeparated` -- the whole classification, with
  `extract` and `rigid` still explicit arguments and `diagonal` discharged.
* `meets_twistColumns`, `leafAvoidingSeparated_twistColumns_iff` --
  `LeafAvoidingSeparated` is invariant under permuting the column labelling of a member.

## What is not proved here

* **`SpineSingleColumn.LeafAvoidingSeparated` is not proved here.**  It is the
  hypothesis `hSeparated` of every statement below.  `Count/BranchSharedDirection.lean`
  proves its local half, the joint condition at every branch vertex, and reduces it to the
  trivalent target vertices; `TrivalentFibreUnique.leafAvoidingSeparated` proves it at
  every member.
* `extract` and `rigid` are explicit arguments of
  `diagonalClassification_of_leafAvoidingSeparated`, and nothing here proves them.  The
  genus-six classification is `CaterpillarAllMembers.diagonalClassification_genusSix`.
-/

namespace DraismaVargas.Count.DiagonalFromSeparation

open DraismaVargas.Count
open DraismaVargas.Count.FibreCaterpillar

variable {m : ℕ} {request : Fin (6 * m + 3) → ℚ}

/-- **The `diagonal` field of `BallotSlopes.DiagonalClassification`, from
`SpineSingleColumn.LeafAvoidingSeparated` alone.**

`SpineSingleColumn.exists_rowSingleColumn_of_leafAvoiding` turns the hypothesis
into `SpineOffDiagonal.RowSingleColumn` on every row of the member, and
`BallotSlopes.diagonalRepresentatives_of_rowSingleColumn` turns that into a
diagonal representative of the same geometric class. -/
theorem diagonal_of_leafAvoidingSeparated
    (hSeparated : ∀ mem : FibreMember (catCore m) request (m + 2),
      mem.Open → mem.HasOddMult → SpineSingleColumn.LeafAvoidingSeparated m mem)
    (mem : FibreMember (catCore m) request (m + 2)) (hOpen : mem.Open)
    (hOdd : mem.HasOddMult) :
    ∃ rep : FibreMember (catCore m) request (m + 2),
      rep.Open ∧ rep.HasOddMult ∧ rep.Diagonal ∧
        GeometricFibre.cls rep = GeometricFibre.cls mem :=
  BallotSlopes.diagonalRepresentatives_of_rowSingleColumn
    (fun mem' hOpen' hOdd' ↦ by
      obtain ⟨σ, -, hσ⟩ := SpineSingleColumn.exists_rowSingleColumn_of_leafAvoiding mem'
        (hSeparated mem' hOpen' hOdd')
      exact ⟨σ, hσ⟩)
    mem hOpen hOdd

/-- **The classification, with its `diagonal` field discharged by
`LeafAvoidingSeparated`.**  `extract` (the core diagonal is a ballot diagonal) and `rigid`
(the core diagonal determines the class) stay explicit. -/
theorem diagonalClassification_of_leafAvoidingSeparated
    (hSeparated : ∀ mem : FibreMember (catCore m) request (m + 2),
      mem.Open → mem.HasOddMult → SpineSingleColumn.LeafAvoidingSeparated m mem)
    (extract : ∀ mem : FibreMember (catCore m) request (m + 2),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        ∃ s : Slopes (2 * (m + 1)), mem.coreDiag = BallotSlopes.ballotCoreDiag m s)
    (rigid : ∀ first second : FibreMember (catCore m) request (m + 2),
      first.Open → first.HasOddMult → first.Diagonal →
        second.Open → second.HasOddMult → second.Diagonal →
          first.coreDiag = second.coreDiag →
            GeometricFibre.cls first = GeometricFibre.cls second) :
    BallotSlopes.DiagonalClassification m request where
  diagonal := diagonal_of_leafAvoidingSeparated hSeparated
  extract := extract
  rigid := rigid

/-! ## `LeafAvoidingSeparated` is invariant under the column twist -/

/-- `Meets` at a column-twisted member is `Meets` at the twisted column. -/
theorem meets_twistColumns (σ : Equiv.Perm (Fin (6 * m + 3)))
    (member : FibreMember (catCore m) request (m + 2)) (sourceRow column : Fin (6 * m + 3)) :
    SpineOffDiagonal.Meets (ColumnTwist.twistColumns σ member).fullDim.labelling
        sourceRow column ↔
      SpineOffDiagonal.Meets member.fullDim.labelling sourceRow (σ column) :=
  Iff.rfl

/-- **`LeafAvoidingSeparated` is invariant under the column twist.**  Permuting the
column labelling of a member (`ColumnTwist.twistColumns`) changes the matrix but not the
geometric class, so a condition on members that is to be read on classes must be
invariant under it.  `SpineSingleColumn.LeafAvoidingSeparated` quantifies over *all*
columns and mentions the labelling's `targetEdge` only through that quantifier, while
`PassesAboveLeaf` and `rowEdges` do not mention it at all -- so the twist moves it to an
equivalent statement.

This is a robustness check, not an inhabitation: nothing here says it holds at any
member. -/
theorem leafAvoidingSeparated_twistColumns_iff (σ : Equiv.Perm (Fin (6 * m + 3)))
    (member : FibreMember (catCore m) request (m + 2)) :
    SpineSingleColumn.LeafAvoidingSeparated m (ColumnTwist.twistColumns σ member) ↔
      SpineSingleColumn.LeafAvoidingSeparated m member := by
  constructor
  · intro hSep first second column hAvoid hAvoid' hMeets hMeets'
    refine hSep first second (σ.symm column) hAvoid hAvoid' ?_ ?_
    · rw [meets_twistColumns, Equiv.apply_symm_apply]; exact hMeets
    · rw [meets_twistColumns, Equiv.apply_symm_apply]; exact hMeets'
  · intro hSep first second column hAvoid hAvoid' hMeets hMeets'
    rw [meets_twistColumns] at hMeets hMeets'
    exact hSep first second (σ column) hAvoid hAvoid' hMeets hMeets'

end DraismaVargas.Count.DiagonalFromSeparation
