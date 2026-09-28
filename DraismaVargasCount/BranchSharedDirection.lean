import DraismaVargasCount.SpineSingleColumn

/-!
# A shared direction at a branch vertex is a lollipop hairpin

**Source.**  Vargas, Part II (arXiv:2609.09109), the proof of
`lm:combinatorial-structure-caterpillar-of-loops`: the interior vertices of the spine path
`P` lie above vertices of change zero, so they have `r_φ = 0`, and by Case (r0) of
`prop-local` consecutive edges along `P` map to distinct edges of `T`.  This module is one
step of the proof that the spine path of a caterpillar member maps injectively to the target.

## What this module adds

`SpineSingleColumn` §6 reduces Part II's *"since `T` is a tree, `φ` is injective on `P`"* to
**local non-backtracking at each joint of the concatenated spine walk**, and discharges it at
the joints lying above a **trivalent** target vertex
(`SpineSingleColumn.target_ne_of_branch_of_trivalent`, from the zero change budget there).
The remaining local case is a branch vertex above a divalent target vertex, where two of the
three survivors share a direction.

§2--§4 below treat that case, **unconditionally and at every `m`**: at a branch vertex above
a divalent target vertex of a caterpillar member the two survivors that share a direction are
the two occurrences of the *loop row*, so the sharing pair always lies on one row and is
always a hairpin above a leaf.  Consequently a branch vertex is never a place where two
*leaf-avoiding* rows can meet a common column (§4).

## The three inputs

1. `LollipopDivalent.divalentCount_eq_catCore` -- the target of a caterpillar
   member has **exactly** `g = 2m+2` divalent vertices; and
   `LollipopDivalent.genus_le_divalentCount_catCore` exhibits `g` of them as
   the images `φ(A_i)` of the `g` lollipop branch vertices.  Counting turns
   that injection into a **bijection**: §1's
   `exists_loopSlot_of_divalent` -- *every* divalent target vertex is some
   `φ(A_i)`.
2. `LollipopBridgeFibreWitness.nonDanglingValency_eq_zero_of_ne_loopBranch` --
   above `φ(A_i)` the only surviving source vertex is `A_i` itself.  Its hypothesis
   `LoopLeafAdjacent` is discharged by `SpineSingleColumn.loopLeafAdjacent_all`.
3. `SpineRowLength.mem_incidentEdges_loopImage_iff` and
   `LollipopBridgeFibreWitness.eq_bridge_of_surviving_loopBranch` -- the two
   edges at `φ(A_i)` are the leaf edge and the bridge edge, and the bridge is
   the *only* survivor above the bridge edge.

## What is proved

* §1 `exists_loopSlot_of_divalent` -- every divalent vertex of the target of a
  caterpillar member is the image of a lollipop branch vertex.
* §2 `exists_loopSlot_eq_loopBranch_of_divalent` -- **every surviving source
  vertex above a divalent target vertex is a lollipop branch vertex `A_i`**
  (not merely every branch vertex: surviving valency `> 0` suffices);
  `incidentEdges_card_eq_three_of_branch_of_ne` -- a branch vertex that is no
  `A_i` therefore lies above a **trivalent** target vertex.
* §3 `exists_loopSlot_of_share_at_branch` -- **the headline.**  Two distinct
  survivors at a branch vertex lying above one and the same target edge force
  the vertex to be some `A_i`, the shared edge to be that lollipop's leaf edge,
  and both survivors to be leaf survivors; `row_eq_of_share_at_branch` -- they
  lie on one and the same stable row, which is the loop row.
* §4 `target_ne_of_branch_of_not_passesAboveLeaf`,
  `target_ne_of_branch_of_row`, `eq_of_meets_common_at_branch` --
  **non-backtracking at every branch vertex, on every leaf-avoiding row**, with
  no trivalence hypothesis: this is the local datum Part II's concatenation of
  the spine rows needs at each of its joints, available at *all* of them.
* §5 `row_eq_of_share_at_vertex` -- §4 at a source vertex of *either* surviving
  valency; and `leafAvoidingSeparated_of_fibreVertexUnique` --
  `SpineSingleColumn.LeafAvoidingSeparated` follows from "no target
  vertex carries two distinct surviving source vertices".
* §6 `eq_of_target_eq_of_divalent`, `eq_of_target_eq_of_leaf` -- that
  hypothesis **discharged** above every divalent target vertex and above every
  leaf, i.e. at `2g` of the target's `3g - 2` vertices; and
  `leafAvoidingSeparated_of_trivalentFibreUnique` -- the hypothesis needed only at
  the remaining `g - 2` **trivalent** target vertices.

## What is not proved here

* **`SpineSingleColumn.LeafAvoidingSeparated` itself is not proved here.**  §1--§4
  are *local*: every statement there is about occurrences incident to **one** source
  vertex.  §5 and §6 reduce it, they do not prove it: the hypothesis `hTrivalent` of
  `leafAvoidingSeparated_of_trivalentFibreUnique` is the **global** step -- Part II's
  *"since `T` is a tree, `φ` is injective on `P`"* -- and it is proved in
  `TrivalentFibreUnique` (`TrivalentFibreUnique.leafAvoidingSeparated`).  The converse
  also holds, so §5's reformulation is exactly equivalent to `LeafAvoidingSeparated`:
  two surviving source vertices above a trivalent target vertex carry survivors above a
  common target edge, on rows that are necessarily distinct (a common row would
  meet that column twice, so it would pass above a leaf, so it would be a loop
  row, whose occurrences meet only divalent- and leaf-image vertices) and
  necessarily leaf-avoiding, which is a failure of `LeafAvoidingSeparated`.
  That converse is *not* formalised below.
* **Nothing here concatenates two rows**, constructs the spine path of
  `catCore m`, or states a branch-vertex form of
  `RowGeodesic.isWalkFrom_of_isChain`.
* Nothing below mentions `Open`, `HasOddMult`, `GeometricFibre`,
  `openOddCount`, `BallotFamily`, `BallotClassification`, a slope sequence, or
  genericity of the request: every statement is about an arbitrary
  `FibreMember (catCore m) request (m + 2)`.
* No numerical hypothesis is taken: unlike
  `SpineSingleColumn.spineColumns_card_le`, nothing here assumes `1 ≤ m`.
-/

namespace DraismaVargas.Count.BranchSharedDirection

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.FibreCaterpillar
open DraismaVargas.Count.LeafFibre
open DraismaVargas.Count.EdgeDenominator
open DraismaVargas.Count.RowWalk
open DraismaVargas.Count.SpineRowLength
open Utilities.Certificate.ExplicitPotential (Core)

variable {m : ℕ} {request : Fin (6 * m + 3) → ℚ}

/-! ## 1.  Every divalent target vertex is a lollipop image -/

section Divalent

/-- The `g` lollipop slots of `catCore m`, as a subtype. -/
private abbrev LoopSlot (m : ℕ) : Type :=
  {slot : Fin (6 * m + 3) // (catCore m).tail slot = (catCore m).head slot}

/-- The divalent vertices of a member's target, as a subtype. -/
private abbrev DivalentVertex (member : FibreMember (catCore m) request (m + 2)) : Type :=
  {vertex : member.target.V // vertex ∈ LollipopDivalent.divalentVertices member.target}

/-- `A_i ↦ φ(A_i)`, landing in the divalent vertices by
`LollipopDivalent.loopImage_divalent`. -/
private noncomputable def loopImageMap (member : FibreMember (catCore m) request (m + 2)) :
    LoopSlot m → DivalentVertex member := fun slot ↦
  ⟨LollipopDivalent.loopImage member slot.2, by
    simpa only [LollipopDivalent.divalentVertices, Finset.mem_filter, Finset.mem_univ,
      true_and] using LollipopDivalent.loopImage_divalent member slot.2⟩

private theorem loopImageMap_injective (member : FibreMember (catCore m) request (m + 2)) :
    Function.Injective (loopImageMap member) := by
  intro first second hEq
  exact Subtype.ext (LollipopDivalent.catCore_tail_inj_of_loop m first.1 second.1
    first.2 second.2
    (LollipopDivalent.loopImage_inj member first.2 second.2 (congrArg Subtype.val hEq)))

private theorem loopImageMap_bijective (member : FibreMember (catCore m) request (m + 2)) :
    Function.Bijective (loopImageMap member) := by
  classical
  refine (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨loopImageMap_injective member, ?_⟩
  rw [LollipopLeafRow.card_catCore_loopSlots m, Fintype.card_coe,
    ← LollipopDivalent.divalentCount, LollipopDivalent.divalentCount_eq_catCore m member]

/-- **Every divalent vertex of the target of a caterpillar member is the image
of a lollipop branch vertex.**

`LollipopDivalent.genus_le_divalentCount_catCore` injects the `g` lollipop
slots into the divalent vertices and `LollipopDivalent.divalentCount_eq_catCore`
says there are exactly `g` of the latter, so the injection is onto.  Both
inputs are unconditional, so this is too. -/
theorem exists_loopSlot_of_divalent (member : FibreMember (catCore m) request (m + 2))
    {vertex : member.target.V}
    (hDivalent : (GluingDatum.incidentEdges vertex).card = 2) :
    ∃ (slot : Fin (6 * m + 3)) (hLoop : (catCore m).tail slot = (catCore m).head slot),
      LollipopDivalent.loopImage member hLoop = vertex := by
  classical
  have hMem : vertex ∈ LollipopDivalent.divalentVertices member.target := by
    simpa only [LollipopDivalent.divalentVertices, Finset.mem_filter, Finset.mem_univ,
      true_and] using hDivalent
  obtain ⟨slot, hSlot⟩ := (loopImageMap_bijective member).2 ⟨vertex, hMem⟩
  exact ⟨slot.1, slot.2, congrArg Subtype.val hSlot⟩

end Divalent

/-! ## 2.  A surviving source vertex above a divalent target vertex is `A_i` -/

section Fibre

/-- **The whole surviving fibre above a divalent target vertex is one lollipop
branch vertex.**  §1 names the vertex as some `φ(A_i)`, and
`LollipopBridgeFibreWitness.nonDanglingValency_eq_zero_of_ne_loopBranch` -- the
vertex clause of the fibre statement of Part II's `lm:bridge-and-loop`, whose hypothesis
`LoopLeafAdjacent` `SpineSingleColumn.loopLeafAdjacent_all` discharges -- says every
other source vertex there is entirely dangling.

Note the hypothesis: *surviving*, not *branch*.  A source vertex of surviving
valency two above a divalent target vertex is already excluded. -/
theorem exists_loopSlot_eq_loopBranch_of_divalent
    (member : FibreMember (catCore m) request (m + 2))
    {B : member.data.SourceVertex} (hSurvives : 0 < nonDanglingValency member.data B)
    (hDivalent : (GluingDatum.incidentEdges (B.1.1 : member.target.V)).card = 2) :
    ∃ (slot : Fin (6 * m + 3)) (hLoop : (catCore m).tail slot = (catCore m).head slot),
      B = LollipopDivalent.loopBranch member hLoop := by
  obtain ⟨slot, hLoop, hImage⟩ := exists_loopSlot_of_divalent member hDivalent
  refine ⟨slot, hLoop, ?_⟩
  by_contra hNe
  have hZero := LollipopBridgeFibreWitness.nonDanglingValency_eq_zero_of_ne_loopBranch
    member hLoop (SpineSingleColumn.loopLeafAdjacent_all member slot hLoop)
    (by rw [hImage]) hNe
  omega

/-- **A branch vertex that is no `A_i` lies above a trivalent target vertex.**
`SpineSingleColumn.incidentEdges_card_branch` leaves only the divalent case,
which §2 identifies. -/
theorem incidentEdges_card_eq_three_of_branch_of_ne
    (member : FibreMember (catCore m) request (m + 2))
    {B : member.data.SourceVertex} (hValency : nonDanglingValency member.data B = 3)
    (hNe : ∀ (slot : Fin (6 * m + 3))
      (hLoop : (catCore m).tail slot = (catCore m).head slot),
      B ≠ LollipopDivalent.loopBranch member hLoop) :
    (GluingDatum.incidentEdges (B.1.1 : member.target.V)).card = 3 := by
  rcases SpineSingleColumn.incidentEdges_card_branch member.fullDim hValency with
    hDiv | hTri
  · obtain ⟨slot, hLoop, hEq⟩ :=
      exists_loopSlot_eq_loopBranch_of_divalent member (by omega) hDiv
    exact absurd hEq (hNe slot hLoop)
  · exact hTri

end Fibre

/-! ## 3.  A shared direction at a branch vertex is a lollipop hairpin -/

section Share

/-- **The headline.**  If two *distinct* surviving occurrences at a branch
vertex of a caterpillar member lie above one and the same target edge, then the
vertex is the branch vertex `A_i` of a lollipop, the shared edge is that
lollipop's leaf edge `t_{v_i}`, and both occurrences are leaf survivors -- so
they are the pair `e_1, e_2` of the hairpin.

The trivalent case is `SpineSingleColumn.target_ne_of_branch_of_trivalent`
(zero change budget); the leaf case is
`SpineSingleColumn.not_isLeafVertex_of_branch`; the divalent case is §2 together with
the fibre clause of `lm:bridge-and-loop` above the bridge edge
(`LollipopBridgeFibreWitness.eq_bridge_of_surviving_loopBranch`). -/
theorem exists_loopSlot_of_share_at_branch
    (member : FibreMember (catCore m) request (m + 2))
    {B : member.data.SourceVertex} (hValency : nonDanglingValency member.data B = 3)
    {a b : member.data.SourceEdge} (hab : a ≠ b)
    (haS : ¬ IsDangling member.data a) (haI : Incident member.data a B)
    (hbS : ¬ IsDangling member.data b) (hbI : Incident member.data b B)
    (hShare : (a.1.1 : member.target.edges) = b.1.1) :
    ∃ (slot : Fin (6 * m + 3)) (hLoop : (catCore m).tail slot = (catCore m).head slot),
      B = LollipopDivalent.loopBranch member hLoop ∧
        (a.1.1 : member.target.edges) = loopLeafEdge member hLoop ∧
        a ∈ leafSurvivors (data := member.data)
          (LollipopLeafRow.loopLeaf_isLeafVertex member hLoop) ∧
        b ∈ leafSurvivors (data := member.data)
          (LollipopLeafRow.loopLeaf_isLeafVertex member hLoop) := by
  rcases SpineSingleColumn.incidentEdges_card_branch member.fullDim hValency with
    hDiv | hTri
  · obtain ⟨slot, hLoop, hEq⟩ :=
      exists_loopSlot_eq_loopBranch_of_divalent member (by omega) hDiv
    refine ⟨slot, hLoop, hEq, ?_⟩
    have hAdj := SpineSingleColumn.loopLeafAdjacent_all member slot hLoop
    have hMem : (a.1.1 : member.target.edges) ∈
        GluingDatum.incidentEdges (LollipopDivalent.loopImage member hLoop) := by
      have := ((incident_iff_target_mem_and_rel member.data a B).mp haI).1
      rwa [show (B.1.1 : member.target.V) = LollipopDivalent.loopImage member hLoop from
        congrArg (fun v : member.data.SourceVertex ↦ (v.1.1 : member.target.V)) hEq] at this
    rcases (mem_incidentEdges_loopImage_iff member hLoop hAdj _).mp hMem with hLeaf | hBridge
    · exact ⟨hLeaf, (mem_leafSurvivors _).mpr ⟨haS, hLeaf⟩,
        (mem_leafSurvivors _).mpr ⟨hbS, hShare ▸ hLeaf⟩⟩
    · exfalso
      obtain ⟨hBrS, hBrI, hBrOff, -⟩ := loopBridge_spec member hLoop
      have hA : a = loopBridge member hLoop :=
        LollipopBridgeFibreWitness.eq_bridge_of_surviving_loopBranch member hLoop hAdj
          hBrS hBrI hBrOff haS hBridge
      have hB : b = loopBridge member hLoop :=
        LollipopBridgeFibreWitness.eq_bridge_of_surviving_loopBranch member hLoop hAdj
          hBrS hBrI hBrOff hbS (hShare ▸ hBridge)
      exact hab (hA.trans hB.symm)
  · exact absurd hShare (SpineSingleColumn.target_ne_of_branch_of_trivalent
      member.fullDim hTri hValency hab haS haI hbS hbI)

/-- **The sharing pair lies on one stable row.**  Both occurrences are leaf
survivors of the same leaf, and `LeafFibre.row_eq_leafRow` sends every leaf
survivor to that leaf's row. -/
theorem row_eq_of_share_at_branch
    (member : FibreMember (catCore m) request (m + 2))
    {B : member.data.SourceVertex} (hValency : nonDanglingValency member.data B = 3)
    {a b : member.data.SourceEdge} (hab : a ≠ b)
    (haS : ¬ IsDangling member.data a) (haI : Incident member.data a B)
    (hbS : ¬ IsDangling member.data b) (hbI : Incident member.data b B)
    (hShare : (a.1.1 : member.target.edges) = b.1.1) :
    member.fullDim.labelling.row
        (NonDanglingEdge.stablePath (⟨a, haS⟩ : NonDanglingEdge member.data)) =
      member.fullDim.labelling.row
        (NonDanglingEdge.stablePath (⟨b, hbS⟩ : NonDanglingEdge member.data)) := by
  obtain ⟨slot, hLoop, -, -, haMem, hbMem⟩ :=
    exists_loopSlot_of_share_at_branch member hValency hab haS haI hbS hbI hShare
  exact (row_eq_leafRow member.fullDim (LollipopLeafRow.loopLeaf_isLeafVertex member hLoop)
    haMem haS).trans
    (row_eq_leafRow member.fullDim (LollipopLeafRow.loopLeaf_isLeafVertex member hLoop)
      hbMem hbS).symm

end Share

/-! ## 4.  Non-backtracking at every branch vertex of a leaf-avoiding row -/

section NonBacktracking

/-- **The joint condition Part II's concatenation needs, at every joint.**  At
a branch vertex, an occurrence whose row is leaf-avoiding has a target edge
different from that of every other survivor there.

`SpineSingleColumn.target_ne_of_branch_of_trivalent` is this statement under
the hypothesis that the branch vertex lies above a trivalent target vertex;
§3 removes that hypothesis. -/
theorem target_ne_of_branch_of_row
    (member : FibreMember (catCore m) request (m + 2))
    {B : member.data.SourceVertex} (hValency : nonDanglingValency member.data B = 3)
    {a b : member.data.SourceEdge} (hab : a ≠ b)
    (haS : ¬ IsDangling member.data a) (haI : Incident member.data a B)
    (hbS : ¬ IsDangling member.data b) (hbI : Incident member.data b B)
    {sourceRow : Fin (6 * m + 3)}
    (hRow : a ∈ rowEdges member.fullDim.labelling sourceRow)
    (hAvoid : ¬ PassesAboveLeaf member.fullDim.labelling sourceRow) :
    (a.1.1 : member.target.edges) ≠ b.1.1 := by
  intro hShare
  obtain ⟨slot, hLoop, -, hLeafEdge, -, -⟩ :=
    exists_loopSlot_of_share_at_branch member hValency hab haS haI hbS hbI hShare
  refine hAvoid ⟨a, hRow, LollipopLeafRow.loopLeaf member hLoop,
    LollipopLeafRow.loopLeaf_isLeafVertex member hLoop, ?_⟩
  rw [hLeafEdge]
  exact leafEdge_mem (LollipopLeafRow.loopLeaf_isLeafVertex member hLoop)

/-- The same, with leaf avoidance stated for the row the occurrence names. -/
theorem target_ne_of_branch_of_not_passesAboveLeaf
    (member : FibreMember (catCore m) request (m + 2))
    {B : member.data.SourceVertex} (hValency : nonDanglingValency member.data B = 3)
    {a b : member.data.SourceEdge} (hab : a ≠ b)
    (haS : ¬ IsDangling member.data a) (haI : Incident member.data a B)
    (hbS : ¬ IsDangling member.data b) (hbI : Incident member.data b B)
    (hAvoid : ¬ PassesAboveLeaf member.fullDim.labelling
      (member.fullDim.labelling.row
        (NonDanglingEdge.stablePath (⟨a, haS⟩ : NonDanglingEdge member.data)))) :
    (a.1.1 : member.target.edges) ≠ b.1.1 :=
  target_ne_of_branch_of_row member hValency hab haS haI hbS hbI
    ((mem_rowEdges member.fullDim.labelling _ a).mpr ⟨haS, rfl⟩) hAvoid

/-- **Two leaf-avoiding rows meeting a common column at a common branch vertex
are equal.**  This is `SpineSingleColumn.LeafAvoidingSeparated` restricted to
the occurrences at one branch vertex -- its local shadow, and the only part of it
that a local argument can reach. -/
theorem eq_of_meets_common_at_branch
    (member : FibreMember (catCore m) request (m + 2))
    {B : member.data.SourceVertex} (hValency : nonDanglingValency member.data B = 3)
    {a b : member.data.SourceEdge}
    (haS : ¬ IsDangling member.data a) (haI : Incident member.data a B)
    (hbS : ¬ IsDangling member.data b) (hbI : Incident member.data b B)
    {first second : Fin (6 * m + 3)}
    (hFirst : a ∈ rowEdges member.fullDim.labelling first)
    (hSecond : b ∈ rowEdges member.fullDim.labelling second)
    (hAvoid : ¬ PassesAboveLeaf member.fullDim.labelling first)
    (hShare : (a.1.1 : member.target.edges) = b.1.1) :
    first = second := by
  by_cases hab : a = b
  · subst hab
    obtain ⟨hFirstS, hFirstRow⟩ := (mem_rowEdges member.fullDim.labelling first a).mp hFirst
    obtain ⟨hSecondS, hSecondRow⟩ := (mem_rowEdges member.fullDim.labelling second a).mp hSecond
    rw [← hFirstRow, ← hSecondRow]
  · exact absurd hShare
      (target_ne_of_branch_of_row member hValency hab haS haI hbS hbI hFirst hAvoid)

end NonBacktracking

/-! ## 5.  `LeafAvoidingSeparated`, restated as a statement about the target's vertex
fibres -/

section FibreReduction

/-- **Two survivors at a common source vertex above a common target edge lie on
one row**, as soon as one of the two rows is leaf-avoiding.

Both possible surviving valencies are covered: at a branch vertex this is §4,
and at a surviving valency-two vertex the partner of a row occurrence is on the
same row (`RowWalk.onRow_of_incident`).  No other valency occurs, because two
distinct survivors already force `2 ≤ nd` and
`FullDimensionalSourcePresentation.trivalent` caps it at three. -/
theorem row_eq_of_share_at_vertex
    (member : FibreMember (catCore m) request (m + 2))
    {V : member.data.SourceVertex} {a b : member.data.SourceEdge}
    (haS : ¬ IsDangling member.data a) (haI : Incident member.data a V)
    (hbS : ¬ IsDangling member.data b) (hbI : Incident member.data b V)
    {first second : Fin (6 * m + 3)}
    (hFirst : a ∈ rowEdges member.fullDim.labelling first)
    (hSecond : b ∈ rowEdges member.fullDim.labelling second)
    (hAvoid : ¬ PassesAboveLeaf member.fullDim.labelling first)
    (hShare : (a.1.1 : member.target.edges) = b.1.1) :
    first = second := by
  classical
  by_cases hab : a = b
  · subst hab
    obtain ⟨hFirstS, hFirstRow⟩ := (mem_rowEdges member.fullDim.labelling first a).mp hFirst
    obtain ⟨hSecondS, hSecondRow⟩ := (mem_rowEdges member.fullDim.labelling second a).mp hSecond
    rw [← hFirstRow, ← hSecondRow]
  · have hTwo : 2 ≤ nonDanglingValency member.data V := by
      have hlt : 1 < (SpineSingleColumn.survivorsAt member.data V).card :=
        Finset.one_lt_card.mpr
          ⟨⟨a, haI⟩, SpineSingleColumn.mem_survivorsAt _ haS,
            ⟨b, hbI⟩, SpineSingleColumn.mem_survivorsAt _ hbS,
            fun h ↦ hab (congrArg Subtype.val h)⟩
      rwa [SpineSingleColumn.card_survivorsAt] at hlt
    have hThree : nonDanglingValency member.data V ≤ 3 := member.fullDim.trivalent V
    interval_cases hVal : nonDanglingValency member.data V
    · have hOnA := (mem_rowEdges_iff_onRow member.fullDim.labelling first a).mp hFirst
      have hOnB := onRow_of_incident hVal hOnA haI hbS hbI
      have hbFirst := (mem_rowEdges_iff_onRow member.fullDim.labelling first b).mpr hOnB
      obtain ⟨hS₁, hRow₁⟩ := (mem_rowEdges member.fullDim.labelling first b).mp hbFirst
      obtain ⟨hS₂, hRow₂⟩ := (mem_rowEdges member.fullDim.labelling second b).mp hSecond
      rw [← hRow₁, ← hRow₂]
    · exact eq_of_meets_common_at_branch member hVal haS haI hbS hbI hFirst hSecond
        hAvoid hShare

/-- **`SpineSingleColumn.LeafAvoidingSeparated`, reduced to the fibres of the target's
vertices.**  If no target vertex carries two distinct *surviving* source
vertices, then distinct leaf-avoiding rows never meet a common column -- which
is `SpineSingleColumn.LeafAvoidingSeparated`, the global half of the injectivity of the
spine path.

The reduction is more than a restatement, because §2 already
discharges the hypothesis above **every divalent target vertex** (only the
lollipop branch vertex `A_i` survives there) and
`LeafFibre.leafSurvivors_card` does the same above every **leaf** (the two
survivors above a leaf edge are the hairpin, incident to one source vertex on
the leaf side).  What is left is the `g - 2` **trivalent** target vertices
(§6, `leafAvoidingSeparated_of_trivalentFibreUnique`). -/
theorem leafAvoidingSeparated_of_fibreVertexUnique
    (member : FibreMember (catCore m) request (m + 2))
    (hUnique : ∀ X Y : member.data.SourceVertex,
      (X.1.1 : member.target.V) = (Y.1.1 : member.target.V) →
        0 < nonDanglingValency member.data X → 0 < nonDanglingValency member.data Y →
          X = Y) :
    SpineSingleColumn.LeafAvoidingSeparated m member := by
  classical
  rintro first second column hAvoid _ ⟨a, haRow, haTarget⟩ ⟨b, hbRow, hbTarget⟩
  obtain ⟨haS, -⟩ := (mem_rowEdges member.fullDim.labelling first a).mp haRow
  obtain ⟨hbS, -⟩ := (mem_rowEdges member.fullDim.labelling second b).mp hbRow
  have hTargetEq : (a.1.1 : member.target.edges) = b.1.1 := haTarget.trans hbTarget.symm
  set X : member.data.SourceVertex := (member.data.sourceEnds a).1 with hXdef
  set X' : member.data.SourceVertex := (member.data.sourceEnds b).1 with hX'def
  have haX : Incident member.data a X := Or.inl rfl
  have hbX' : Incident member.data b X' := Or.inl rfl
  have hXpos : 0 < nonDanglingValency member.data X :=
    LollipopBridgeFibre.nonDanglingValency_pos_of_survivor haS haX
  have hX'pos : 0 < nonDanglingValency member.data X' :=
    LollipopBridgeFibre.nonDanglingValency_pos_of_survivor hbS hbX'
  have hEndX : TargetGeodesic.IsEnd (a.1.1 : member.target.edges) (X.1.1 : member.target.V) :=
    RowGeodesic.isEnd_of_incident haX
  have hEndX' : TargetGeodesic.IsEnd (a.1.1 : member.target.edges) (X'.1.1 : member.target.V) := by
    rw [hTargetEq]; exact RowGeodesic.isEnd_of_incident hbX'
  have hCases : (X'.1.1 : member.target.V) = X.1.1 ∨
      (X'.1.1 : member.target.V) =
        TargetGeodesic.otherEndOf (a.1.1 : member.target.edges) X.1.1 := by
    rcases TargetGeodesic.ends_pair_of_isEnd hEndX with hPair | hPair <;>
      rcases hEndX' with hEnd | hEnd <;> rw [hPair] at hEnd <;> simp at hEnd
    · exact Or.inl hEnd.symm
    · exact Or.inr hEnd.symm
    · exact Or.inr hEnd.symm
    · exact Or.inl hEnd.symm
  rcases hCases with hEq | hEq
  · have hVertexEq : X' = X := hUnique X' X hEq hX'pos hXpos
    exact row_eq_of_share_at_vertex member haS haX hbS (hVertexEq ▸ hbX') haRow hbRow
      hAvoid hTargetEq
  · have hFar : (X'.1.1 : member.target.V) = (otherEnd member.data a X).1.1 := by
      rw [hEq, RowGeodesic.otherEndOf_eq haX]
    have hFarPos : 0 < nonDanglingValency member.data (otherEnd member.data a X) :=
      LollipopBridgeFibre.nonDanglingValency_pos_of_survivor haS
        (incident_otherEnd member.data a X)
    have hVertexEq : X' = otherEnd member.data a X := hUnique X' _ hFar hX'pos hFarPos
    exact row_eq_of_share_at_vertex member haS (incident_otherEnd member.data a X) hbS
      (hVertexEq ▸ hbX') haRow hbRow hAvoid hTargetEq

end FibreReduction

/-! ## 6.  The fibre hypothesis, discharged above every leaf and every divalent
target vertex -/

section FibreDischarge

/-- **Above a divalent target vertex the surviving fibre is one source
vertex.**  §2 identifies each of the two as the lollipop branch vertex `A_i`
for its own slot, and `LollipopDivalent.sourceVertex_eq_of_divalent_of_three_le`
then identifies them with each other. -/
theorem eq_of_target_eq_of_divalent
    (member : FibreMember (catCore m) request (m + 2))
    {X Y : member.data.SourceVertex}
    (hTarget : (X.1.1 : member.target.V) = (Y.1.1 : member.target.V))
    (hDivalent : (GluingDatum.incidentEdges (X.1.1 : member.target.V)).card = 2)
    (hX : 0 < nonDanglingValency member.data X)
    (hY : 0 < nonDanglingValency member.data Y) :
    X = Y := by
  obtain ⟨s, hs, hXeq⟩ := exists_loopSlot_eq_loopBranch_of_divalent member hX hDivalent
  obtain ⟨t, ht, hYeq⟩ := exists_loopSlot_eq_loopBranch_of_divalent member hY
    (by rw [← hTarget]; exact hDivalent)
  refine LollipopDivalent.sourceVertex_eq_of_divalent_of_three_le member.fullDim ?_ ?_
    hTarget hDivalent
  · rw [hXeq]; exact LollipopDivalent.three_le_loopBranch member hs
  · rw [hYeq]; exact LollipopDivalent.three_le_loopBranch member ht

/-- **Above a leaf of the target the surviving fibre is one source vertex.**
Every occurrence at a source vertex above a leaf lies above the leaf edge, of
which `LeafFibre.leafSurvivors_card` says exactly two survive; the valency
trichotomy forbids surviving valency one, so each surviving source vertex there
carries *both* of them, and two source vertices above one target vertex sharing
an incident occurrence coincide. -/
theorem eq_of_target_eq_of_leaf
    (member : FibreMember (catCore m) request (m + 2))
    {X Y : member.data.SourceVertex}
    (hTarget : (X.1.1 : member.target.V) = (Y.1.1 : member.target.V))
    (hLeaf : IsLeafVertex member.target (X.1.1 : member.target.V))
    (hX : 0 < nonDanglingValency member.data X)
    (hY : 0 < nonDanglingValency member.data Y) :
    X = Y := by
  classical
  have hLeafCard : (leafSurvivors (data := member.data) hLeaf).card = 2 :=
    leafSurvivors_card (data := member.data) member.fullDim hLeaf
  have hSubX : ((Finset.univ : Finset member.data.SourceEdge).filter
      fun item ↦ ¬ IsDangling member.data item ∧ Incident member.data item X) ⊆
      leafSurvivors (data := member.data) hLeaf := by
    intro e he
    obtain ⟨hS, hI⟩ := (Finset.mem_filter.mp he).2
    exact (mem_leafSurvivors hLeaf).mpr ⟨hS, eq_leafEdge_of_mem hLeaf
      ((incident_iff_target_mem_and_rel member.data e X).mp hI).1⟩
  have hSubY : ((Finset.univ : Finset member.data.SourceEdge).filter
      fun item ↦ ¬ IsDangling member.data item ∧ Incident member.data item Y) ⊆
      leafSurvivors (data := member.data) hLeaf := by
    intro e he
    obtain ⟨hS, hI⟩ := (Finset.mem_filter.mp he).2
    have hMem := ((incident_iff_target_mem_and_rel member.data e Y).mp hI).1
    rw [← hTarget] at hMem
    exact (mem_leafSurvivors hLeaf).mpr ⟨hS, eq_leafEdge_of_mem hLeaf hMem⟩
  have hcardX := LollipopBridgeFibre.card_survivors_eq_nonDanglingValency (data := member.data) X
  have hcardY := LollipopBridgeFibre.card_survivors_eq_nonDanglingValency (data := member.data) Y
  have hXle := Finset.card_le_card hSubX
  have hYle := Finset.card_le_card hSubY
  have hXtwo : nonDanglingValency member.data X = 2 := by
    rcases member.fullDim.nonDanglingValency_trichotomy X with h | h | h <;> omega
  have hYtwo : nonDanglingValency member.data Y = 2 := by
    rcases member.fullDim.nonDanglingValency_trichotomy Y with h | h | h <;> omega
  have hEqX : ((Finset.univ : Finset member.data.SourceEdge).filter
      fun item ↦ ¬ IsDangling member.data item ∧ Incident member.data item X) =
      leafSurvivors (data := member.data) hLeaf :=
    Finset.eq_of_subset_of_card_le hSubX (by omega)
  have hEqY : ((Finset.univ : Finset member.data.SourceEdge).filter
      fun item ↦ ¬ IsDangling member.data item ∧ Incident member.data item Y) =
      leafSurvivors (data := member.data) hLeaf :=
    Finset.eq_of_subset_of_card_le hSubY (by omega)
  obtain ⟨a, ha⟩ : ((Finset.univ : Finset member.data.SourceEdge).filter
      fun item ↦ ¬ IsDangling member.data item ∧ Incident member.data item X).Nonempty :=
    Finset.card_pos.mp (by omega)
  have haY : a ∈ (Finset.univ : Finset member.data.SourceEdge).filter
      fun item ↦ ¬ IsDangling member.data item ∧ Incident member.data item Y := by
    rw [hEqY, ← hEqX]; exact ha
  exact LollipopBridgeFibre.eq_of_incident_of_target_eq hTarget
    (Finset.mem_filter.mp ha).2.2 (Finset.mem_filter.mp haY).2.2

/-- **`SpineSingleColumn.LeafAvoidingSeparated`, localised to the trivalent target
vertices.**  It follows from the fibre hypothesis of §5 at the `g - 2` **trivalent**
target vertices alone: §6 discharges it at the `g` leaves and the `g` divalent vertices,
and change-minimality leaves no other valency.

This is still the *global* statement Part II proves by concatenating the free rows into
one path, but stated about `g - 2` vertex fibres rather than about rows and columns.  The
hypothesis `hTrivalent` is proved in `TrivalentFibreUnique`, which applies this theorem to
obtain `TrivalentFibreUnique.leafAvoidingSeparated`. -/
theorem leafAvoidingSeparated_of_trivalentFibreUnique
    (member : FibreMember (catCore m) request (m + 2))
    (hTrivalent : ∀ X Y : member.data.SourceVertex,
      (X.1.1 : member.target.V) = (Y.1.1 : member.target.V) →
        (GluingDatum.incidentEdges (X.1.1 : member.target.V)).card = 3 →
          0 < nonDanglingValency member.data X →
            0 < nonDanglingValency member.data Y → X = Y) :
    SpineSingleColumn.LeafAvoidingSeparated m member := by
  refine leafAvoidingSeparated_of_fibreVertexUnique member fun X Y hTarget hX hY ↦ ?_
  have hPos : 0 < (GluingDatum.incidentEdges (X.1.1 : member.target.V)).card :=
    StableLocalProperties.incidentEdges_card_pos_of_changeMinimalAt member.data X.1.1
      (member.fullDim.changeMinimal X.1.1)
  have hLe : (GluingDatum.incidentEdges (X.1.1 : member.target.V)).card ≤ 3 :=
    GluingDatum.incidentEdges_card_le_three_of_changeMinimalAt member.data
      member.fullDim.valid X.1.1 (member.fullDim.changeMinimal X.1.1)
  interval_cases hCard : (GluingDatum.incidentEdges (X.1.1 : member.target.V)).card
  · exact eq_of_target_eq_of_leaf member hTarget hCard hX hY
  · exact eq_of_target_eq_of_divalent member hTarget hCard hX hY
  · exact hTrivalent X Y hTarget hCard hX hY

end FibreDischarge

end DraismaVargas.Count.BranchSharedDirection
