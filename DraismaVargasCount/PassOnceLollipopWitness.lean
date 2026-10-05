module

public import DraismaVargasCount.PassOnceLollipop
public import DraismaVargasCount.LollipopBridgeFibreWitness
public import DraismaVargasCount.RowSingleColumnWitness

@[expose] public section

/-!
# Pass-once at the lollipop, at a member of the labelled fibre

The member-level companion of `Count/PassOnceLollipop.lean`.  It proves the hypothesis
`LoopLeafAdjacent` that `Count/LollipopBridgeFibre.lean` and
`Count/LollipopBridgeFibreWitness.lean` carry -- Part I's pass-once condition at the
lollipop -- from `PassOnceLollipop.leafAdjacent_of_loopRow`, **with no hypothesis added**:
the member is an arbitrary `FibreMember core y degree` over an arbitrary core with a
self-loop.

## What is proved

* `loopLeafAdjacent` -- `LoopLeafAdjacent member hLoop` itself.
* `loopRowLengthTwo` -- its equivalent form `LoopRowLengthTwo member hLoop`,
  i.e. Part II's `h_l = ⟨A, e₁, C, e₂, A⟩`.
* `nonDanglingValency_eq_zero_of_ne_loopBranch`,
  `eq_bridge_of_surviving_loopBranch` -- **the fibre clause of Part II's
  `lm:bridge-and-loop` at a member**, unconditionally: every source vertex above `φ(A)`
  other than `A` is completely dangling, and `e_b` is the only surviving occurrence above
  `φ(e_b)`.
* `card_rowEdges_eq_two_of_loopRow`, `exists_rowSingleColumn_loopRow`,
  `exists_rowSingleColumn_core_loop` -- **the spine half on the loop rows**: each loop row
  occupies a single column, obtained from the same statement through
  `Count/RowSingleColumnWitness.lean`'s reduction.

## What is not proved here

* Nothing here is an exhaustion of the fibre: no statement mentions
  `GeometricFibre`, `openOddCount`, `BallotFamily` or `BallotClassification`.
* Nothing about the **spine rows**: only the loop rows are treated, which is all
  `Count/RowSingleColumnWitness.lean` reduces to this statement.
* No genericity, `Open`, `HasOddMult`, request or length hypothesis is used or
  supplied.
-/

namespace DraismaVargas.Count.PassOnceLollipopWitness

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.RowWalk
open Utilities.Certificate.ExplicitPotential (Core)

variable {degree n p : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- **Pass-once at the lollipop, member level.**  For every member of the
labelled fibre over a core with a self-loop, the branch vertex of that self-loop
has an image adjacent to the leaf its loop row passes above. -/
theorem loopLeafAdjacent (member : FibreMember core y degree)
    {slot : Fin p} (hLoop : core.tail slot = core.head slot) :
    LollipopBridgeFibreWitness.LoopLeafAdjacent member hLoop :=
  PassOnceLollipop.leafAdjacent_of_loopRow member.fullDim
    (branch := LollipopDivalent.loopBranch member hLoop)
    (path := member.ident.row.symm slot)
    (by have := LollipopDivalent.three_le_loopBranch member hLoop; omega)
    (LollipopLeafRow.incidenceCount_eq_two_of_core_loop member hLoop)
    (LollipopLeafRow.loopLeaf_isLeafVertex member hLoop)
    (LollipopLeafRow.leafRow_loopLeaf member hLoop)

/-- **The length-two clause of `lm:bridge-and-loop`, member level**: the loop
row really is `h_l = ⟨A, e₁, C, e₂, A⟩`. -/
theorem loopRowLengthTwo (member : FibreMember core y degree)
    {slot : Fin p} (hLoop : core.tail slot = core.head slot) :
    LollipopBridgeFibreWitness.LoopRowLengthTwo member hLoop :=
  (LollipopBridgeFibreWitness.loopLeafAdjacent_iff_loopRowLengthTwo member hLoop).mp
    (loopLeafAdjacent member hLoop)

/-- **The fibre clause above `φ(A)`, member level**, with no hypothesis. -/
theorem nonDanglingValency_eq_zero_of_ne_loopBranch (member : FibreMember core y degree)
    {slot : Fin p} (hLoop : core.tail slot = core.head slot)
    {vertex : member.data.SourceVertex}
    (hTarget : (vertex.1.1 : member.target.V) = LollipopDivalent.loopImage member hLoop)
    (hNe : vertex ≠ LollipopDivalent.loopBranch member hLoop) :
    nonDanglingValency member.data vertex = 0 :=
  LollipopBridgeFibreWitness.nonDanglingValency_eq_zero_of_ne_loopBranch member hLoop
    (loopLeafAdjacent member hLoop) hTarget hNe

/-- **The fibre clause above `φ(e_b)`, member level**, with no hypothesis. -/
theorem eq_bridge_of_surviving_loopBranch (member : FibreMember core y degree)
    {slot : Fin p} (hLoop : core.tail slot = core.head slot)
    {bridge : member.data.SourceEdge} (hBridgeSurvives : ¬ IsDangling member.data bridge)
    (hBridgeIncident : Incident member.data bridge (LollipopDivalent.loopBranch member hLoop))
    (hBridgeNotOnRow : ¬ OnRow member.data
      (LollipopBridgeFibreWitness.loopRow member slot) bridge)
    {edge : member.data.SourceEdge} (hSurvives : ¬ IsDangling member.data edge)
    (hTarget : edge.1.1 = bridge.1.1) :
    edge = bridge :=
  LollipopBridgeFibreWitness.eq_bridge_of_surviving_loopBranch member hLoop
    (loopLeafAdjacent member hLoop) hBridgeSurvives hBridgeIncident hBridgeNotOnRow
    hSurvives hTarget

/-! ## The spine half on the loop rows -/

open DraismaVargas.Count.SpineOffDiagonal in
open DraismaVargas.LocalCases.StablePathCount in
/-- **A loop row displays exactly two occurrences**, unconditionally. -/
theorem card_rowEdges_eq_two_of_loopRow {target : CFGraph.{0}} {degree : ℕ}
    {data : GluingDatum target degree} {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : 3 ≤ nonDanglingValency data branch)
    (hTwo : StablePathCount.incidenceCount data branch path = 2)
    {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    (hLeafRow : LeafFibre.leafRow fd hLeaf = fd.labelling.row path) :
    (EdgeDenominator.rowEdges fd.labelling (fd.labelling.row path)).card = 2 :=
  (RowSingleColumnWitness.eq_two_iff_exists_end_above_leafEdge fd (by omega) hTwo hLeaf
      hLeafRow).mpr
    (PassOnceLollipop.exists_end_above_leafEdge_of_loopRow fd hBranch hTwo hLeaf hLeafRow)

open DraismaVargas.Count.SpineOffDiagonal in
open DraismaVargas.LocalCases.StablePathCount in
/-- **A loop row occupies a single column of `A_φ`**, unconditionally. -/
theorem exists_rowSingleColumn_loopRow {target : CFGraph.{0}} {degree : ℕ}
    {data : GluingDatum target degree} {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : 3 ≤ nonDanglingValency data branch)
    (hTwo : StablePathCount.incidenceCount data branch path = 2)
    {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    (hLeafRow : LeafFibre.leafRow fd hLeaf = fd.labelling.row path) :
    ∃ column, RowSingleColumn fd.labelling (fd.labelling.row path) column :=
  (RowSingleColumnWitness.exists_rowSingleColumn_loopRow_iff fd (by omega) hTwo hLeaf
      hLeafRow).mpr
    (PassOnceLollipop.exists_end_above_leafEdge_of_loopRow fd hBranch hTwo hLeaf hLeafRow)

open DraismaVargas.Count.SpineOffDiagonal in
/-- **A loop row occupies a single column, member level**, unconditionally. -/
theorem exists_rowSingleColumn_core_loop (member : FibreMember core y degree)
    {slot : Fin p} (hLoop : core.tail slot = core.head slot) :
    ∃ column, RowSingleColumn member.fullDim.labelling
      (member.fullDim.labelling.row (member.ident.row.symm slot)) column :=
  (RowSingleColumnWitness.exists_rowSingleColumn_core_loop_iff member hLoop).mpr
    (PassOnceLollipop.exists_end_above_leafEdge_of_loopRow member.fullDim
      (branch := (member.ident.vertex.symm (core.tail slot)).1)
      (member.ident.vertex.symm (core.tail slot)).2
      (LollipopLeafRow.incidenceCount_eq_two_of_core_loop member hLoop)
      (LollipopLeafRow.loopLeaf_isLeafVertex member hLoop)
      (LollipopLeafRow.leafRow_loopLeaf member hLoop))

end DraismaVargas.Count.PassOnceLollipopWitness
