module

public import DraismaVargasCount.LollipopBridgeFibre

@[expose] public section

/-!
# The loop-and-bridge lemma at a member of the labelled fibre

**Source.**  Vargas, Part II (arXiv:2609.09109), `lm:bridge-and-loop`, whose proof is
Draisma--Vargas Part I (arXiv:1909.12924), `lemma-loop-bridge`: at a trivalent vertex `A`
of `H(φ)` incident to a loop `h_l` and a bridge `h_b`, one has
`h_l = ⟨A, e₁, C, e₂, A⟩` (the **length-two clause**), `φ(C)` is a leaf, `φ(A)` is
divalent, and `r_φ(A) = 1` and `m(e_b) = 2` (the **bridge clause**); moreover
`e_b, A, e₁, e₂, C` are the only non-dangling elements in the fibres of `φ(e_b)`,
`φ(A)`, `φ(e₁)` and `φ(C)` (the **fibre clause**).

This is the companion of `DraismaVargasCount.LollipopBridgeFibre`, carrying its
statements -- and the bridge-clause statements of `DraismaVargasCount.LollipopDivalent`
-- over an arbitrary `FibreMember core y degree` whose core has a self-loop.  The
statements of `LollipopDivalent` (`blockCard_and_bridge_index` and its corollaries) are
about a source vertex with `incidenceCount = 2`; the transport to the branch vertex
`loopBranch` of a self-loop slot is `LollipopLeafRow.incidenceCount_eq_two_of_core_loop`,
exactly as `LollipopDivalent.loopImage_divalent` uses it.  Like those modules, it serves the
description of the members over the caterpillar of loops behind the base count
(`CaterpillarAllMembers`, step 1 of `DraismaVargasCount.Assembly`).

## What is proved

* `loopRow` -- the stable row of a self-loop slot.
* `localRamification_loopBranch` (`r_φ(A) = 1`),
  `card_incidentSourceEdge_loopBranch` (`N(A) = 3`, so no occurrence at `A` is
  dangling), `blockCard_loopBranch` (`m(A) = 2`), `onRow_of_ne_bridge_loopBranch`,
  `exists_bridge_loopBranch` and
  `sourceEdgeIndex_eq_two_of_not_onRow_loopBranch` (`m(e_b) = 2`) -- **the
  bridge clause at a member**, with no hypothesis beyond
  `core.tail slot = core.head slot`.
* `LoopRowLengthTwo`, `LoopLeafAdjacent` and
  `loopLeafAdjacent_iff_loopRowLengthTwo` -- the two equivalent forms of the
  length-two clause.
* `nonDanglingValency_eq_zero_of_ne_loopBranch`,
  `eq_bridge_of_surviving_loopBranch` -- **the fibre clause above `φ(A)` and
  above `φ(e_b)` at a member**, conditional on that clause.

## What is not proved here (every hypothesis, explicitly)

* `LoopLeafAdjacent` is a **hypothesis here**, not a theorem.  It is Part I's
  pass-once condition (`lemma-pass-once`) at the lollipop.  It is proved
  unconditionally as `PassOnceLollipopWitness.loopLeafAdjacent`, from
  `PassOnceLollipop.leafAdjacent_of_loopRow`; the statements below keep it as a
  hypothesis because that module imports this one.
* Nothing here is an exhaustion of the fibre, and nothing below mentions
  `Open`, `HasOddMult`, a request, a length, or a constructed datum.
* Nothing about the spine half of the caterpillar structure (Part II,
  `lm:combinatorial-structure-caterpillar-of-loops`).
-/
namespace DraismaVargas.Count.LollipopBridgeFibreWitness

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.RowWalk
open Utilities.Certificate.ExplicitPotential (Core)

variable {degree n p : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- The stable row of a self-loop slot of the core. -/
noncomputable def loopRow (member : FibreMember core y degree) (slot : Fin p) :
    StablePath member.data :=
  member.ident.row.symm slot

/-! ## 1.  The bridge clause at a member -/

/-- **`r_φ(A) = 1`, member level.** -/
theorem localRamification_loopBranch (member : FibreMember core y degree) {slot : Fin p}
    (hLoop : core.tail slot = core.head slot) :
    member.data.localRamification (LollipopDivalent.loopImage member hLoop)
        ⟨(LollipopDivalent.loopBranch member hLoop).1.2,
          (LollipopDivalent.loopBranch member hLoop).2⟩ = 1 :=
  LollipopDivalent.localRamification_eq_one_of_incidenceCount_eq_two member.fullDim
    (LollipopDivalent.three_le_loopBranch member hLoop)
    (LollipopLeafRow.incidenceCount_eq_two_of_core_loop member hLoop)

/-- **`A` carries exactly three incident occurrences, member level**: none of
them is dangling. -/
theorem card_incidentSourceEdge_loopBranch (member : FibreMember core y degree) {slot : Fin p}
    (hLoop : core.tail slot = core.head slot) :
    Fintype.card (IncidentSourceEdge member.data (LollipopDivalent.loopBranch member hLoop))
      = 3 :=
  LollipopDivalent.card_incidentSourceEdge_eq_three member.fullDim
    (LollipopDivalent.three_le_loopBranch member hLoop)
    (LollipopLeafRow.incidenceCount_eq_two_of_core_loop member hLoop)

/-- **`m(A) = 2`, member level.** -/
theorem blockCard_loopBranch (member : FibreMember core y degree) {slot : Fin p}
    (hLoop : core.tail slot = core.head slot) :
    (member.data.vertexPartition (LollipopDivalent.loopImage member hLoop)).blockCard
        (LollipopDivalent.loopBranch member hLoop).1.2 = 2 :=
  LollipopDivalent.blockCard_eq_two_of_incidenceCount_eq_two member.fullDim
    (LollipopDivalent.three_le_loopBranch member hLoop)
    (LollipopLeafRow.incidenceCount_eq_two_of_core_loop member hLoop)

/-- **Every surviving occurrence at `A` other than the bridge lies on the loop
row, member level.** -/
theorem onRow_of_ne_bridge_loopBranch (member : FibreMember core y degree) {slot : Fin p}
    (hLoop : core.tail slot = core.head slot)
    {bridge : member.data.SourceEdge} (hBridgeSurvives : ¬ IsDangling member.data bridge)
    (hBridgeIncident : Incident member.data bridge (LollipopDivalent.loopBranch member hLoop))
    (hBridgeNotOnRow : ¬ OnRow member.data (loopRow member slot) bridge)
    {edge : member.data.SourceEdge} (hSurvives : ¬ IsDangling member.data edge)
    (hIncident : Incident member.data edge (LollipopDivalent.loopBranch member hLoop))
    (hNe : edge ≠ bridge) :
    OnRow member.data (loopRow member slot) edge :=
  LollipopDivalent.onRow_of_ne_bridge member.fullDim
    (LollipopDivalent.three_le_loopBranch member hLoop)
    (LollipopLeafRow.incidenceCount_eq_two_of_core_loop member hLoop)
    hBridgeSurvives hBridgeIncident hBridgeNotOnRow hSurvives hIncident hNe

/-- **The bridge occurrence exists, member level**, with `m(e_b) = 2`. -/
theorem exists_bridge_loopBranch (member : FibreMember core y degree) {slot : Fin p}
    (hLoop : core.tail slot = core.head slot) :
    ∃ bridge : member.data.SourceEdge, ¬ IsDangling member.data bridge ∧
      Incident member.data bridge (LollipopDivalent.loopBranch member hLoop) ∧
      ¬ OnRow member.data (loopRow member slot) bridge ∧
      member.data.sourceEdgeIndex bridge = 2 := by
  obtain ⟨bridge, hSurv, hInc, hOff⟩ :=
    LollipopDivalent.exists_bridge member.fullDim
      (LollipopDivalent.three_le_loopBranch member hLoop)
      (LollipopLeafRow.incidenceCount_eq_two_of_core_loop member hLoop)
  exact ⟨bridge, hSurv, hInc, hOff,
    LollipopDivalent.sourceEdgeIndex_eq_two_of_not_onRow member.fullDim
      (LollipopDivalent.three_le_loopBranch member hLoop)
      (LollipopLeafRow.incidenceCount_eq_two_of_core_loop member hLoop) hSurv hInc hOff⟩

/-- **`m(e_b) = 2`, member level.** -/
theorem sourceEdgeIndex_eq_two_of_not_onRow_loopBranch (member : FibreMember core y degree)
    {slot : Fin p} (hLoop : core.tail slot = core.head slot)
    {bridge : member.data.SourceEdge} (hBridgeSurvives : ¬ IsDangling member.data bridge)
    (hBridgeIncident : Incident member.data bridge (LollipopDivalent.loopBranch member hLoop))
    (hBridgeNotOnRow : ¬ OnRow member.data (loopRow member slot) bridge) :
    member.data.sourceEdgeIndex bridge = 2 :=
  LollipopDivalent.sourceEdgeIndex_eq_two_of_not_onRow member.fullDim
    (LollipopDivalent.three_le_loopBranch member hLoop)
    (LollipopLeafRow.incidenceCount_eq_two_of_core_loop member hLoop)
    hBridgeSurvives hBridgeIncident hBridgeNotOnRow

/-! ## 2.  The length-two clause, and the conditional fibre clause at a member -/

/-- The length-two clause of Part II's `lm:bridge-and-loop` at a member: the
two ends of the loop row lie above the **leaf edge** of the leaf that row
passes above, so that `h_l = ⟨A, e₁, C, e₂, A⟩`. -/
def LoopRowLengthTwo (member : FibreMember core y degree) {slot : Fin p}
    (hLoop : core.tail slot = core.head slot) : Prop :=
  ∀ edge : member.data.SourceEdge, OnRow member.data (loopRow member slot) edge →
    Incident member.data edge (LollipopDivalent.loopBranch member hLoop) →
    edge.1.1 = leafEdge (LollipopLeafRow.loopLeaf_isLeafVertex member hLoop)

/-- The same clause in its **target-side** form: `φ(A)` is adjacent to the leaf
that its loop row passes above.  This is Part I's pass-once condition
(`lemma-pass-once`) at the lollipop.  It is proved in the downstream module
`DraismaVargasCount.PassOnceLollipopWitness` (`loopLeafAdjacent`) and is a
hypothesis in this file. -/
def LoopLeafAdjacent (member : FibreMember core y degree) {slot : Fin p}
    (hLoop : core.tail slot = core.head slot) : Prop :=
  leafEdge (LollipopLeafRow.loopLeaf_isLeafVertex member hLoop) ∈
    GluingDatum.incidentEdges (LollipopDivalent.loopImage member hLoop)

/-- **The two forms of the length-two clause agree.**  So, given the rest of
this file, the length-two clause of `lm:bridge-and-loop` is equivalent to the
target-side sentence "`φ(A)` is adjacent to the leaf of its loop row". -/
theorem loopLeafAdjacent_iff_loopRowLengthTwo (member : FibreMember core y degree)
    {slot : Fin p} (hLoop : core.tail slot = core.head slot) :
    LoopLeafAdjacent member hLoop ↔ LoopRowLengthTwo member hLoop := by
  constructor
  · intro hAdj edge hRow hInc
    exact LollipopBridgeFibre.onRow_target_eq_leafEdge member.fullDim
      (LollipopDivalent.three_le_loopBranch member hLoop)
      (LollipopLeafRow.incidenceCount_eq_two_of_core_loop member hLoop)
      (LollipopLeafRow.loopLeaf_isLeafVertex member hLoop) hAdj hRow hInc
  · intro hEnds
    obtain ⟨first, -, -, -, hFirstInc, hFirstRow, -, -, -⟩ :=
      LollipopBridgeFibre.exists_row_ends
        (LollipopLeafRow.incidenceCount_eq_two_of_core_loop member hLoop)
    have hTarget := hEnds first hFirstRow hFirstInc
    have hMem := ((incident_iff_target_mem_and_rel member.data first
      (LollipopDivalent.loopBranch member hLoop)).mp hFirstInc).1
    rw [hTarget] at hMem
    exact hMem

/-- **The fibre clause above `φ(A)`, member level**, conditional on
`LoopLeafAdjacent`: every source vertex above `φ(A)` other than `A` is
completely dangling. -/
theorem nonDanglingValency_eq_zero_of_ne_loopBranch (member : FibreMember core y degree)
    {slot : Fin p} (hLoop : core.tail slot = core.head slot)
    (hAdj : LoopLeafAdjacent member hLoop)
    {vertex : member.data.SourceVertex}
    (hTarget : (vertex.1.1 : member.target.V) = LollipopDivalent.loopImage member hLoop)
    (hNe : vertex ≠ LollipopDivalent.loopBranch member hLoop) :
    nonDanglingValency member.data vertex = 0 :=
  LollipopBridgeFibre.nonDanglingValency_eq_zero_of_ne_of_leafAdjacent member.fullDim
    (LollipopDivalent.three_le_loopBranch member hLoop)
    (LollipopLeafRow.incidenceCount_eq_two_of_core_loop member hLoop)
    (LollipopLeafRow.loopLeaf_isLeafVertex member hLoop) hAdj hTarget hNe

/-- **The fibre clause above `φ(e_b)`, member level**, conditional on
`LoopLeafAdjacent`: the bridge `e_b` is the only surviving occurrence above its
target occurrence. -/
theorem eq_bridge_of_surviving_loopBranch (member : FibreMember core y degree)
    {slot : Fin p} (hLoop : core.tail slot = core.head slot)
    (hAdj : LoopLeafAdjacent member hLoop)
    {bridge : member.data.SourceEdge} (hBridgeSurvives : ¬ IsDangling member.data bridge)
    (hBridgeIncident : Incident member.data bridge (LollipopDivalent.loopBranch member hLoop))
    (hBridgeNotOnRow : ¬ OnRow member.data (loopRow member slot) bridge)
    {edge : member.data.SourceEdge} (hSurvives : ¬ IsDangling member.data edge)
    (hTarget : edge.1.1 = bridge.1.1) :
    edge = bridge :=
  LollipopBridgeFibre.eq_bridge_of_surviving_of_leafAdjacent member.fullDim
    (LollipopDivalent.three_le_loopBranch member hLoop)
    (LollipopLeafRow.incidenceCount_eq_two_of_core_loop member hLoop)
    (LollipopLeafRow.loopLeaf_isLeafVertex member hLoop) hAdj
    hBridgeSurvives hBridgeIncident hBridgeNotOnRow hSurvives hTarget

end DraismaVargas.Count.LollipopBridgeFibreWitness
