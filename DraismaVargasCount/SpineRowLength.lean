import DraismaVargasCount.RowSingleColumnWitness
import DraismaVargasCount.LollipopBridgeFibreWitness
import DraismaVargasCount.SpinePath

/-!
# The lollipop columns of `A_φ`, and what is left of the spine after them

**Source.**  Vargas, Part II (arXiv:2609.09109), the proof of
`lm:combinatorial-structure-caterpillar-of-loops`: by `lm:bridge-and-loop` the
image `φ(N(L(A_i)))` of the neighbourhood of each loop vertex is a path of
length two with interior vertex `u_i` and leaf endpoint `v_i`; these account
for `2g` distinct edges of `T` with completely determined fibres, the image
`φ(P)` of the spine path is disjoint from them, and so `φ(P)` has at most
`(3g - 3) - 2g = g - 3` edges.  This module treats the lollipop columns of the
edge-length matrix, towards that edge budget and the diagonality of `A_φ`; it
is part of the analysis of the members over the caterpillar of loops that the
base count relies on (step 1 of `DraismaVargasCount/Assembly.lean`).

## What this module is

`SpineOffDiagonal` reduces the diagonality of `A_φ` to a single sentence,

```
hOff : ∀ sourceRow sourceRow' column,
  Meets labelling sourceRow column → Meets labelling sourceRow' column →
    sourceRow = sourceRow'
```

("distinct rows meet distinct columns"), and `rowSingleColumn_of_meets_row_unique`
turns it into `RowSingleColumn` for every row.

This module proves it for the lollipop columns:

* **unconditionally** for the `g` leaf columns `φ(e_1) = t_{v_i}`;
* **conditionally on `LollipopBridgeFibreWitness.LoopLeafAdjacent`**
  (Draisma–Vargas Part I's pass-once condition, `lemma-pass-once`, at the
  lollipop) for the `g` bridge columns `φ(e_b^i)`.

So after this module `hOff` is needed only on the remaining `g-3` columns,
which are Part II's `φ(P)`.  `DraismaVargasCount.SpineRowLengthWitness`
carries these statements to `catCore m` and shows that `hOff` restricted to the
non-lollipop columns is enough for the whole of diagonality, and hence for the
spine bound `¬ PassesAboveLeaf → card = 1` and for `A_φ` monomial.

## What is proved

* §1 `eq_leafRow_of_meets`, `meets_row_unique_leafEdge` --- **the leaf columns,
  with no hypothesis at all.**  Only `h(v)` meets `t_v`.  This is
  `LeafFibre.rowFibre_leafEdge` read as a statement about `Meets`.
* §2 `loopLeafEdge`, `loopBridge`, `loopBridgeEdge` --- the two target edges of
  the lollipop at a self-loop slot of an arbitrary core, together with
  `loopBridgeEdge_mem_incidentEdges` and **`loopBridgeEdge_ne_loopLeafEdge`,
  which is unconditional**: the bridge occurrence would otherwise lie on the
  loop row.
* §3 `mem_incidentEdges_loopImage_iff` (under `LoopLeafAdjacent`: `φ(A_i)`'s
  two edges *are* the leaf edge and the bridge edge), `loopLeafEdge_inj`
  (unconditional), `eq_loopRow_of_meets_loopLeafEdge`,
  `eq_bridgeRow_of_meets_loopBridgeEdge` and `meets_row_unique_loopBridgeEdge`
  (under `LoopLeafAdjacent`).

## Scope

* **`LoopLeafAdjacent` is a hypothesis wherever the bridge column appears.**
  Nothing below proves it; it is proved downstream, as
  `PassOnceLollipopWitness.loopLeafAdjacent`.
* **`hOff` is not proved here on any non-lollipop column**, so no row is shown
  here to have a single column.  `DraismaVargasCount.SpineRowLengthWitness`
  says exactly what is left.
* Nothing here constructs a spine path, in the source or the target, and no
  statement below mentions a walk, the neighbourhood `N(L(A_i))`, or a slope.
* Nothing below mentions `catCore`, `Open`, `HasOddMult`, `GeometricFibre`,
  `openOddCount` or a request: every statement is for an arbitrary
  `FibreMember core y degree` over an arbitrary core, or for an arbitrary
  full-dimensional presentation.
-/

namespace DraismaVargas.Count.SpineRowLength

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.LeafFibre
open DraismaVargas.Count.EdgeDenominator
open DraismaVargas.Count.RowWalk
open DraismaVargas.Count.SpineOffDiagonal
open Utilities.Certificate.ExplicitPotential (Core)

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-! ## 1.  The leaf columns: unconditional -/

/-- **A row meeting the leaf edge of `v` is `h(v)`.**  The two surviving
occurrences above `t_v` are consecutive at the leaf core vertex `A_v`
(`LeafFibre.leafSurvivors_card`), so they lie on one stable row; any occurrence
a row displays above `t_v` is one of them. -/
theorem eq_leafRow_of_meets (fd : FullDimensionalSourcePresentation data coordinate)
    {vertex : target.V} (hLeaf : IsLeafVertex target vertex)
    {sourceRow column : coordinate}
    (hColumn : fd.labelling.targetEdge column = leafEdge hLeaf)
    (hMeets : Meets fd.labelling sourceRow column) :
    sourceRow = leafRow fd hLeaf := by
  obtain ⟨edge, hEdge, hTarget⟩ := hMeets
  obtain ⟨hSurvives, hRow⟩ := (mem_rowEdges fd.labelling sourceRow edge).mp hEdge
  have hMem : edge ∈ leafSurvivors (data := data) hLeaf :=
    (mem_leafSurvivors hLeaf).mpr ⟨hSurvives, hTarget.trans hColumn⟩
  rw [← hRow]
  exact row_eq_leafRow fd hLeaf hMem hSurvives

/-- **`hOff` on a leaf column, with no hypothesis whatever**: only `h(v)` meets
`t_v`, so distinct rows meet distinct columns there. -/
theorem meets_row_unique_leafEdge (fd : FullDimensionalSourcePresentation data coordinate)
    {vertex : target.V} (hLeaf : IsLeafVertex target vertex)
    {sourceRow sourceRow' column : coordinate}
    (hColumn : fd.labelling.targetEdge column = leafEdge hLeaf)
    (hMeets : Meets fd.labelling sourceRow column)
    (hMeets' : Meets fd.labelling sourceRow' column) :
    sourceRow = sourceRow' :=
  (eq_leafRow_of_meets fd hLeaf hColumn hMeets).trans
    (eq_leafRow_of_meets fd hLeaf hColumn hMeets').symm

/-! ## 2.  The two target edges of a lollipop -/

section Member

variable {n p : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- `t_{v_i}`: the leaf edge of the leaf that the loop row of a self-loop slot
passes above.  Part II's `φ(e_1) = φ(e_2)`. -/
noncomputable def loopLeafEdge (member : FibreMember core y degree) {slot : Fin p}
    (hLoop : core.tail slot = core.head slot) : member.target.edges :=
  leafEdge (LollipopLeafRow.loopLeaf_isLeafVertex member hLoop)

/-- `e_b^i`: the bridge occurrence at the branch vertex of a self-loop slot,
chosen once.  `LollipopBridgeFibreWitness.exists_bridge_loopBranch` produces it
with no hypothesis beyond `core.tail slot = core.head slot`. -/
noncomputable def loopBridge (member : FibreMember core y degree) {slot : Fin p}
    (hLoop : core.tail slot = core.head slot) : member.data.SourceEdge :=
  (LollipopBridgeFibreWitness.exists_bridge_loopBranch member hLoop).choose

theorem loopBridge_spec (member : FibreMember core y degree) {slot : Fin p}
    (hLoop : core.tail slot = core.head slot) :
    ¬ IsDangling member.data (loopBridge member hLoop) ∧
      Incident member.data (loopBridge member hLoop)
        (LollipopDivalent.loopBranch member hLoop) ∧
      ¬ OnRow member.data (LollipopBridgeFibreWitness.loopRow member slot)
        (loopBridge member hLoop) ∧
      member.data.sourceEdgeIndex (loopBridge member hLoop) = 2 :=
  (LollipopBridgeFibreWitness.exists_bridge_loopBranch member hLoop).choose_spec

/-- `φ(e_b^i)`: the target edge below the bridge. -/
noncomputable def loopBridgeEdge (member : FibreMember core y degree) {slot : Fin p}
    (hLoop : core.tail slot = core.head slot) : member.target.edges :=
  (loopBridge member hLoop).1.1

/-- The bridge edge is one of the two edges at the divalent vertex `φ(A_i)`. -/
theorem loopBridgeEdge_mem_incidentEdges (member : FibreMember core y degree) {slot : Fin p}
    (hLoop : core.tail slot = core.head slot) :
    loopBridgeEdge member hLoop ∈
      GluingDatum.incidentEdges (LollipopDivalent.loopImage member hLoop) :=
  ((incident_iff_target_mem_and_rel member.data (loopBridge member hLoop)
    (LollipopDivalent.loopBranch member hLoop)).mp (loopBridge_spec member hLoop).2.1).1

/-- **The bridge edge is not the leaf edge, with no hypothesis at all.**  An
occurrence above `t_{v_i}` lies on the leaf row `h(v_i)`, which is the loop row
(`LollipopLeafRow.leafRow_loopLeaf`); the bridge is off that row by
construction. -/
theorem loopBridgeEdge_ne_loopLeafEdge (member : FibreMember core y degree) {slot : Fin p}
    (hLoop : core.tail slot = core.head slot) :
    loopBridgeEdge member hLoop ≠ loopLeafEdge member hLoop := by
  intro hEq
  obtain ⟨hSurvives, -, hOffRow, -⟩ := loopBridge_spec member hLoop
  have hMem : loopBridge member hLoop ∈
      leafSurvivors (data := member.data) (LollipopLeafRow.loopLeaf_isLeafVertex member hLoop) :=
    (mem_leafSurvivors _).mpr ⟨hSurvives, hEq⟩
  have hRow := (row_eq_leafRow member.fullDim
    (LollipopLeafRow.loopLeaf_isLeafVertex member hLoop) hMem hSurvives).trans
      (LollipopLeafRow.leafRow_loopLeaf member hLoop)
  exact hOffRow ⟨hSurvives, member.fullDim.labelling.row.injective hRow⟩

/-! ## 3.  The lollipop columns -/

/-- **Under `LoopLeafAdjacent`, `φ(A_i)`'s two edges are exactly the leaf edge
and the bridge edge.**  `LollipopDivalent.loopImage_divalent` says there are two
of them, §2 says both of these are among them and that they differ, so a third
would make three. -/
theorem mem_incidentEdges_loopImage_iff (member : FibreMember core y degree) {slot : Fin p}
    (hLoop : core.tail slot = core.head slot)
    (hAdj : LollipopBridgeFibreWitness.LoopLeafAdjacent member hLoop)
    (edge : member.target.edges) :
    edge ∈ GluingDatum.incidentEdges (LollipopDivalent.loopImage member hLoop) ↔
      edge = loopLeafEdge member hLoop ∨ edge = loopBridgeEdge member hLoop := by
  classical
  constructor
  · intro hEdge
    by_contra hNe
    rw [not_or] at hNe
    have hThree := RowSingleColumnWitness.three_le_card_of_mem_of_ne
      (S := GluingDatum.incidentEdges (LollipopDivalent.loopImage member hLoop))
      hAdj (loopBridgeEdge_mem_incidentEdges member hLoop) hEdge
      (Ne.symm (loopBridgeEdge_ne_loopLeafEdge member hLoop))
      (Ne.symm hNe.1) (Ne.symm hNe.2)
    rw [LollipopDivalent.loopImage_divalent member hLoop] at hThree
    omega
  · rintro (rfl | rfl)
    · exact hAdj
    · exact loopBridgeEdge_mem_incidentEdges member hLoop

/-- **Distinct self-loop slots carry distinct leaf edges**, with no hypothesis.
Equal leaf edges give equal leaf survivor sets, hence equal leaf rows, hence
equal slots through `LollipopLeafRow.leafRow_loopLeaf`. -/
theorem loopLeafEdge_inj (member : FibreMember core y degree) {first second : Fin p}
    (hFirst : core.tail first = core.head first)
    (hSecond : core.tail second = core.head second)
    (hEdge : loopLeafEdge member hFirst = loopLeafEdge member hSecond) : first = second := by
  set hL1 := LollipopLeafRow.loopLeaf_isLeafVertex member hFirst with hL1def
  set hL2 := LollipopLeafRow.loopLeaf_isLeafVertex member hSecond with hL2def
  have hMem : leafSurvivor member.fullDim hL1 ∈ leafSurvivors (data := member.data) hL2 :=
    (mem_leafSurvivors hL2).mpr
      ⟨(leafSurvivor_spec member.fullDim hL1).2,
        (leafSurvivor_spec member.fullDim hL1).1.trans hEdge⟩
  have hRowEq : leafRow member.fullDim hL1 = leafRow member.fullDim hL2 :=
    row_eq_leafRow member.fullDim hL2 hMem (leafSurvivor_spec member.fullDim hL1).2
  have hRows := ((LollipopLeafRow.leafRow_loopLeaf member hFirst).symm.trans hRowEq).trans
    (LollipopLeafRow.leafRow_loopLeaf member hSecond)
  exact member.ident.row.symm.injective (member.fullDim.labelling.row.injective hRows)

/-- **`hOff` on the leaf column of a lollipop**: only the loop row meets it. -/
theorem eq_loopRow_of_meets_loopLeafEdge (member : FibreMember core y degree) {slot : Fin p}
    (hLoop : core.tail slot = core.head slot) {sourceRow column : Fin p}
    (hColumn : member.fullDim.labelling.targetEdge column = loopLeafEdge member hLoop)
    (hMeets : Meets member.fullDim.labelling sourceRow column) :
    sourceRow = member.fullDim.labelling.row (member.ident.row.symm slot) :=
  (eq_leafRow_of_meets member.fullDim (LollipopLeafRow.loopLeaf_isLeafVertex member hLoop)
    hColumn hMeets).trans (LollipopLeafRow.leafRow_loopLeaf member hLoop)

/-- **`hOff` on the bridge column of a lollipop, under `LoopLeafAdjacent`.**
Above `φ(e_b)` the bridge is the only surviving occurrence
(`LollipopBridgeFibreWitness.eq_bridge_of_surviving_loopBranch`), so any row
meeting the column displays the bridge and is therefore the bridge's row. -/
theorem eq_bridgeRow_of_meets_loopBridgeEdge (member : FibreMember core y degree)
    {slot : Fin p} (hLoop : core.tail slot = core.head slot)
    (hAdj : LollipopBridgeFibreWitness.LoopLeafAdjacent member hLoop)
    {sourceRow column : Fin p}
    (hColumn : member.fullDim.labelling.targetEdge column = loopBridgeEdge member hLoop)
    (hMeets : Meets member.fullDim.labelling sourceRow column) :
    sourceRow = member.fullDim.labelling.row (NonDanglingEdge.stablePath
      (⟨loopBridge member hLoop, (loopBridge_spec member hLoop).1⟩ :
        NonDanglingEdge member.data)) := by
  obtain ⟨edge, hEdge, hTarget⟩ := hMeets
  obtain ⟨hSurvives, hRow⟩ := (mem_rowEdges member.fullDim.labelling sourceRow edge).mp hEdge
  obtain ⟨hBridgeSurvives, hBridgeIncident, hBridgeOffRow, -⟩ := loopBridge_spec member hLoop
  have hEq : edge = loopBridge member hLoop :=
    LollipopBridgeFibreWitness.eq_bridge_of_surviving_loopBranch member hLoop hAdj
      hBridgeSurvives hBridgeIncident hBridgeOffRow hSurvives (hTarget.trans hColumn)
  rw [← hRow]
  exact congrArg member.fullDim.labelling.row (congrArg NonDanglingEdge.stablePath
    (Subtype.ext hEq))

/-- **`hOff` on a lollipop bridge column, under `LoopLeafAdjacent`.** -/
theorem meets_row_unique_loopBridgeEdge (member : FibreMember core y degree)
    {slot : Fin p} (hLoop : core.tail slot = core.head slot)
    (hAdj : LollipopBridgeFibreWitness.LoopLeafAdjacent member hLoop)
    {sourceRow sourceRow' column : Fin p}
    (hColumn : member.fullDim.labelling.targetEdge column = loopBridgeEdge member hLoop)
    (hMeets : Meets member.fullDim.labelling sourceRow column)
    (hMeets' : Meets member.fullDim.labelling sourceRow' column) :
    sourceRow = sourceRow' :=
  (eq_bridgeRow_of_meets_loopBridgeEdge member hLoop hAdj hColumn hMeets).trans
    (eq_bridgeRow_of_meets_loopBridgeEdge member hLoop hAdj hColumn hMeets').symm

/-- **`hOff` on a lollipop leaf column.** -/
theorem meets_row_unique_loopLeafEdge (member : FibreMember core y degree)
    {slot : Fin p} (hLoop : core.tail slot = core.head slot)
    {sourceRow sourceRow' column : Fin p}
    (hColumn : member.fullDim.labelling.targetEdge column = loopLeafEdge member hLoop)
    (hMeets : Meets member.fullDim.labelling sourceRow column)
    (hMeets' : Meets member.fullDim.labelling sourceRow' column) :
    sourceRow = sourceRow' :=
  (eq_loopRow_of_meets_loopLeafEdge member hLoop hColumn hMeets).trans
    (eq_loopRow_of_meets_loopLeafEdge member hLoop hColumn hMeets').symm

end Member

end DraismaVargas.Count.SpineRowLength
