module

public import DraismaVargasCount.RowGeodesic
public import DraismaVargasCount.Integrality

@[expose] public section

/-!
# A stable row that returns to its own branch vertex passes above a leaf

**Source.**  Draisma--Vargas Part I (arXiv:1909.12924), `lemma-loop-bridge`
(loop and bridge), cited by Vargas, Part II (arXiv:2609.09109) as
`lm:bridge-and-loop` and used there to start the proof of
`lm:combinatorial-structure-caterpillar-of-loops`.

## Where this sits in the base count

The exhaustion field `BallotClassification.member_surjective` of
`CaterpillarBallotCount` is about an **arbitrary**
`FibreMember (catCore m) request (m + 2)`, whose target tree, gluing datum and
sheet partitions are all existentially given; its first ingredient is the local
structure of the fibre at the lollipops (`lm:bridge-and-loop`).
Nothing here is about a constructed datum: no `caterpillarDatum`, no
`ballotDatum`, no slope sequence occurs below.

This file proves the first two named conclusions of `lm:bridge-and-loop`, in
the generality the exhaustion argument needs them:

> a stable row **both of whose ends lie at one branch vertex** passes above a
> leaf of the target, and is the leaf row of that leaf.

In Part II's notation, that is "`φ(C)` is a leaf", and the identification of
`C` with the leaf core vertex `A_v`.  **It is not the clause
`h_l = ⟨A, e₁, C, e₂, A⟩`**: `exists_leafRow_eq_of_loopRow` names the row
without bounding its length, and the length-two clause is a separate obligation
(`LollipopBridgeFibreWitness.LoopRowLengthTwo`, equivalently
`LoopLeafAdjacent`) which nothing here proves.

## The argument, and why it is shorter than the paper's

Part I argues that `r_φ(A) = 0` is impossible because case
(r0-nd3) of `prop-local` puts the three surviving occurrences at `A` above
three distinct target edges, so the loop would pass above two leaves,
contradicting `rem-leaves-min-change`.

The target walk calculus of `TargetGeodesic` gives a shorter argument.  A row with
both ends at one vertex is a **closed** walk of the source.  If it avoided the
leaves of the target it would be non-backtracking
(`RowWalk.rowRamificationAtMostOne_of_rowAvoidsLeaves` supplies `r ≤ 1`, and
`RowWalk.target_ne_of_row` turns that into distinct consecutive target
occurrences), so its image would be a closed non-backtracking walk in a tree.
`TargetGeodesic.not_isEnd_of_mem_tail_of_genusZero` -- *a non-backtracking walk
never touches its starting vertex again* -- forbids exactly that.  No case of
`prop-local` is used, and no change-minimal-leaves remark.

## What is proved

* `isWalkFrom_orderedRow` -- the ordered walk of a stable row of ramification
  at most one is a non-backtracking target walk from its start vertex.  This
  statement was internal to the proof of
  `RowGeodesic.rowTargetInjective_of_genusZero`; it is lifted out here because
  the loop argument needs the walk itself, not merely its injectivity.
* `startVertex_eq_of_incidenceCount_eq_two` -- a source vertex of surviving
  valency other than two that carries **both** ends of a stable path *is* that
  path's start vertex.
* `not_rowAvoidsLeaves_of_loopRow` -- **the headline**: such a row does not
  avoid the leaves of the target.
* `exists_leaf_onRow` -- the leaf, named, together with a surviving occurrence
  of the row above its leaf edge.
* `exists_leafRow_eq_of_loopRow` -- the row **is** `LeafFibre.leafRow` of that
  leaf, so Part II's `C` is the leaf core vertex `A_v` of
  `LeafFibre` and `φ(C) = v`.
* `incidenceCount_eq_two_of_core_loop`, `exists_leafRow_of_core_loop` -- the
  member-level form, for a slot of the core with
  `core.tail slot = core.head slot`.
* `loopLeaf`, `loopLeaf_inj`, `loopLeafMap_injective`,
  `card_loopSlots_le_leafCount` -- distinct self-loop slots of the core give
  distinct leaves of the target, so the target of **every** member has at least
  as many leaves as the core has self-loops.
* `catCore_tail_eq_head_iff`, `card_catCore_loopSlots`,
  `genus_le_leafCount_catCore` -- that bound at `catCore m`:
  `2 * m + 2 ≤ leafCount member.target`.

## What is NOT proved here (every hypothesis, explicitly)

* **Nothing here is an exhaustion of the fibre.**  No statement below mentions
  `GeometricFibre`, `openOddCount`, `BallotFamily` or `BallotClassification`.
* **The bridge side of `lm:bridge-and-loop` is not here.**  `m(e_b) = 2`,
  `r_φ(A) = 1` and "`φ(A)` is divalent" are not proved or stated below; they
  are proved in `LollipopBridgeFibreWitness` and `LollipopDivalent`.
* **The divalent half of the valency census is not here.**  That the `g` images
  `φ(A_i)` are divalent and pairwise *distinct* is the other ingredient of the
  valency census of the target (see §7); this file supplies only the **leaf**
  half (`card_loopSlots_le_leafCount`).
* **Nothing about the spine.**  `A_φ` is not shown diagonal, `φ` is not shown
  injective on the spine path, and no slope sequence is extracted.
* **No genericity, openness or oddness hypothesis is used or supplied.**  No
  statement below mentions a length, `Open`, `HasOddMult` or a request; the
  member-level statements take an arbitrary `FibreMember core y degree`.
* The core-level statements are about `core.tail slot = core.head slot`, i.e. a
  **self-loop of the core**.  `catCore m` has `2m + 2` of them
  (`card_catCore_loopSlots`); nothing below asserts that a core with no
  self-loop has any consequence at all.
-/

namespace DraismaVargas.Count.LollipopLeafRow

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.TargetGeodesic
open DraismaVargas.Count.RowWalk
open Utilities.Certificate.ExplicitPotential (Core)

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-! ## 1.  The ordered row as a non-backtracking target walk

`RowGeodesic.rowTargetInjective_of_genusZero` builds this walk and then throws
it away, keeping only the injectivity of the occurrence map.  The loop argument
of §3 needs the walk itself, so the construction is repeated here as a named
theorem.  Its helper `isChain_ne_of_nodup` is private in `RowGeodesic` and is
reproved. -/

/-- For a list with no duplicates, consecutive entries are distinct. -/
private theorem isChain_ne_of_nodup {α : Type*} {R : α → α → Prop} :
    ∀ {l : List α}, l.Nodup → l.IsChain R → l.IsChain fun a b ↦ R a b ∧ a ≠ b := by
  intro l
  induction l with
  | nil => intro _ _; exact List.isChain_nil
  | cons a t ih =>
      intro hNodup hChain
      cases t with
      | nil => exact List.isChain_singleton _
      | cons b t' =>
          rw [List.isChain_cons_cons] at hChain ⊢
          refine ⟨⟨hChain.1, ?_⟩, ih (List.Nodup.of_cons hNodup) hChain.2⟩
          intro hEq
          exact (List.nodup_cons.mp hNodup).1 (by rw [hEq]; simp)

/-- **The ordered walk of a stable row is a non-backtracking target walk.**
The hypotheses are exactly those of
`RowGeodesic.rowTargetInjective_of_genusZero`, and the conclusion is the
intermediate statement that proof produces. -/
theorem isWalkFrom_orderedRow (hNoGlue : DanglingEdgeNoGlue data)
    (hEnds : HasPathEnds data) {path : StablePath data}
    (hTame : RowRamificationAtMostOne data path) :
    IsWalkFrom (startVertex hEnds path).1.1
      ((orderedRow hEnds path).map fun edge ↦ (edge.1.1 : target.edges)) := by
  classical
  set row := orderedRow hEnds path with hrow
  have hMem : ∀ edge, edge ∈ row ↔ OnRow data path edge := mem_orderedRow_iff hEnds path
  have hNodup : row.Nodup := orderedRow_nodup hEnds path
  have hSurv : ∀ edge ∈ row, ¬ IsDangling data edge :=
    fun edge hedge ↦ ((hMem edge).mp hedge).survives
  have hChain : row.IsChain fun first second ↦ (∃ meet : data.SourceVertex,
      Incident data first meet ∧ Incident data second meet ∧
        nonDanglingValency data meet = 2) ∧
      (first.1.1 : target.edges) ≠ second.1.1 := by
    refine (isChain_ne_of_nodup hNodup (orderedRow_chain hEnds path)).imp_of_mem_imp ?_
    intro a b ha hb hab
    obtain ⟨⟨meet, hAMeet, hBMeet, hValency⟩, hNe⟩ := hab
    exact ⟨⟨meet, hAMeet, hBMeet, hValency⟩,
      target_ne_of_row hNoGlue hTame hValency ((hMem a).mp ha) hAMeet
        ((hMem b).mp hb) hBMeet hNe⟩
  obtain ⟨hIncidentStart, hValencyStart⟩ := startEdge_isPathEnd hEnds path
  refine RowGeodesic.isWalkFrom_of_isChain row (startVertex hEnds path) hNodup hSurv hChain
    (fun head hhead ↦ ?_) (Or.inl hValencyStart)
  have hheadEq : head = (startEdge hEnds path).1 := by
    have h' := hhead
    rw [orderedRow_head? hEnds path] at h'
    simpa using h'.symm
  rw [hheadEq]
  exact hIncidentStart

/-! ## 2.  A vertex carrying both ends of a path is that path's start vertex

`StablePathCount.endCount_eq_two` says a stable path has exactly two ends,
counted as incidences at the source vertices of surviving valency other than
two.  So if one such vertex already accounts for both, every other one accounts
for none -- and the start vertex of the ordered walk is one of them. -/

open DraismaVargas.LocalCases.StablePathCount in
/-- **Both ends at one vertex pins the start vertex.** -/
theorem startVertex_eq_of_incidenceCount_eq_two
    (hNeOne : ∀ vertex : data.SourceVertex, nonDanglingValency data vertex ≠ 1)
    (hEnds : HasPathEnds data) {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : nonDanglingValency data branch ≠ 2)
    (hTwo : incidenceCount data branch path = 2) :
    startVertex hEnds path = branch := by
  classical
  by_contra hNe
  have hStartEnd := startEdge_isPathEnd hEnds path
  have hPos : 0 < incidenceCount data (startVertex hEnds path) path :=
    (incidenceCount_pos_iff data (startVertex hEnds path) path).mpr
      ⟨startEdge hEnds path, hStartEnd.1, startEdge_stablePath hEnds path⟩
  have hsub : ({branch, startVertex hEnds path} : Finset data.SourceVertex) ⊆
      (Finset.univ : Finset data.SourceVertex).filter
        (fun vertex ↦ ¬ nonDanglingValency data vertex = 2) := by
    intro vertex hvertex
    rcases Finset.mem_insert.mp hvertex with hEq | hEq
    · subst hEq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hBranch⟩
    · rw [Finset.mem_singleton] at hEq
      subst hEq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hStartEnd.2⟩
  have hle := Finset.sum_le_sum_of_subset (f := fun vertex ↦ incidenceCount data vertex path)
    hsub
  rw [Finset.sum_pair (fun hEq ↦ hNe hEq.symm)] at hle
  have hEnd : endCount data path = 2 := endCount_eq_two data hNeOne hEnds path
  unfold endCount at hEnd
  omega

/-! ## 3.  The headline: a loop row passes above a leaf

If the row avoided the leaves it would be non-backtracking, so §1 makes its
image a non-backtracking walk of the target starting at the image of `branch`.
The *second* end of the row is another surviving occurrence at `branch`, so it
lies in the tail of the walk and still has the starting vertex as an end --
which `TargetGeodesic.not_isEnd_of_mem_tail_of_genusZero` forbids in a tree. -/

open DraismaVargas.LocalCases.StablePathCount in
/-- **A stable row with both ends at one branch vertex does not avoid the leaves
of the target.**  This replaces the `r_φ(A) ≠ 0` step of Part I's
`lemma-loop-bridge`, and it uses no case of `prop-local`. -/
theorem not_rowAvoidsLeaves_of_loopRow
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : nonDanglingValency data branch ≠ 2)
    (hTwo : incidenceCount data branch path = 2) :
    ¬ RowAvoidsLeaves data path := by
  classical
  intro hAvoid
  have hNeOne := DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one
    data fd.connected
  have hStart : startVertex fd.pathEnds path = branch :=
    startVertex_eq_of_incidenceCount_eq_two hNeOne fd.pathEnds hBranch hTwo
  have hWalk := isWalkFrom_orderedRow fd.danglingEdgeNoGlue fd.pathEnds
    (rowRamificationAtMostOne_of_rowAvoidsLeaves fd hAvoid)
  -- the two ends of the row at `branch`, as surviving occurrences
  set ends := (incidentEdges data branch).filter (fun edge ↦ edge.stablePath = path) with hends
  have hCard : ends.card = 2 := hTwo
  have hOneLt : 1 < ends.card := by omega
  obtain ⟨firstEnd, hfirstMem, otherEnd, hotherMem, hEndsNe⟩ := Finset.one_lt_card.mp hOneLt
  obtain ⟨second, hsecondMem, hsecondNe⟩ :
      ∃ second ∈ ends, second ≠ startEdge fd.pathEnds path := by
    by_cases hcase : firstEnd = startEdge fd.pathEnds path
    · exact ⟨otherEnd, hotherMem, fun hEq ↦ hEndsNe (hcase.trans hEq.symm)⟩
    · exact ⟨firstEnd, hfirstMem, hcase⟩
  have hsecondIncident : Incident data second.1 branch :=
    (mem_incidentEdges data branch second).mp (Finset.mem_filter.mp hsecondMem).1
  have hsecondOnRow : OnRow data path second.1 :=
    ⟨second.2, (Finset.mem_filter.mp hsecondMem).2⟩
  -- it lies in the tail of the ordered row
  have hsecondEdgeNe : second.1 ≠ (startEdge fd.pathEnds path).1 :=
    fun hEq ↦ hsecondNe (Subtype.ext hEq)
  have hsecondMemRow : second.1 ∈ orderedRow fd.pathEnds path :=
    (mem_orderedRow_iff fd.pathEnds path second.1).mpr hsecondOnRow
  have hHead := orderedRow_head? fd.pathEnds path
  have hTail : ((second.1).1.1 : target.edges) ∈
      ((orderedRow fd.pathEnds path).map fun edge ↦ (edge.1.1 : target.edges)).tail := by
    cases hrow : orderedRow fd.pathEnds path with
    | nil =>
        rw [hrow] at hsecondMemRow
        exact absurd hsecondMemRow (by simp)
    | cons head rest =>
        rw [hrow] at hHead hsecondMemRow
        have hHeadEq : head = (startEdge fd.pathEnds path).1 := by
          simpa using hHead
        have hInRest : second.1 ∈ rest := by
          rcases List.mem_cons.mp hsecondMemRow with hEq | hMem
          · exact absurd (hEq.trans hHeadEq) hsecondEdgeNe
          · exact hMem
        simpa using List.mem_map_of_mem (f := fun edge ↦ (edge.1.1 : target.edges)) hInRest
  refine not_isEnd_of_mem_tail_of_genusZero fd.targetConnected fd.targetGenus hWalk hTail ?_
  rw [hStart]
  exact RowGeodesic.isEnd_of_incident hsecondIncident

/-! ## 4.  Naming the leaf: the loop row **is** a leaf row

`LeafFibre` determines the whole fibre above a leaf
`v`: a single core block `A_v` of surviving valency two carries both surviving
occurrences over the leaf edge `t_v`, every other block above `v` is a dangling
leaf, and the two survivors lie on **one** stable row `h(v) = leafRow`.  So the
leaf produced by §3 names the row completely. -/

open DraismaVargas.LocalCases.StablePathCount in
/-- **The leaf, named.**  A loop row carries a surviving occurrence above the
leaf edge of some leaf of the target. -/
theorem exists_leaf_onRow (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : nonDanglingValency data branch ≠ 2)
    (hTwo : incidenceCount data branch path = 2) :
    ∃ (leaf : target.V) (hLeaf : IsLeafVertex target leaf) (edge : data.SourceEdge),
      OnRow data path edge ∧ edge.1.1 = leafEdge hLeaf := by
  classical
  have hNot := not_rowAvoidsLeaves_of_loopRow fd hBranch hTwo
  unfold RowAvoidsLeaves at hNot
  push Not at hNot
  obtain ⟨edge, hOnRow, leaf, hLeaf, hIncident⟩ := hNot
  refine ⟨leaf, hLeaf, edge, hOnRow, ?_⟩
  have hSingle : GluingDatum.incidentEdges leaf = {leafEdge hLeaf} :=
    incidentEdges_eq_leafEdge hLeaf
  rw [hSingle, Finset.mem_singleton] at hIncident
  exact hIncident

open DraismaVargas.LocalCases.StablePathCount in
/-- **`φ(C)` is a leaf**, in the form the length matrix reads it: a stable row
with both ends at one branch vertex is the leaf row `h(v)` of a leaf `v` of the
target.  This is the first named conclusion of Part II's `lm:bridge-and-loop`,
for an arbitrary full-dimensional presentation. -/
theorem exists_leafRow_eq_of_loopRow
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : nonDanglingValency data branch ≠ 2)
    (hTwo : incidenceCount data branch path = 2) :
    ∃ (leaf : target.V) (hLeaf : IsLeafVertex target leaf),
      LeafFibre.leafRow fd hLeaf = fd.labelling.row path := by
  classical
  obtain ⟨leaf, hLeaf, edge, hOnRow, hTarget⟩ := exists_leaf_onRow fd hBranch hTwo
  refine ⟨leaf, hLeaf, ?_⟩
  have hSurvives : ¬ IsDangling data edge := hOnRow.survives
  have hMem : edge ∈ LeafFibre.leafSurvivors (data := data) hLeaf :=
    (LeafFibre.mem_leafSurvivors hLeaf).mpr ⟨hSurvives, hTarget⟩
  have hRow := LeafFibre.row_eq_leafRow fd hLeaf hMem hSurvives
  have hPath : NonDanglingEdge.stablePath (⟨edge, hSurvives⟩ : NonDanglingEdge data) = path := by
    obtain ⟨hSurv, hEq⟩ := hOnRow
    exact hEq
  rw [hPath] at hRow
  exact hRow.symm

/-! ## 5.  The member-level form

A `FibreMember core y degree` carries `ident`, whose `incidence` field matches
every incidence multiplicity of the stable graph with `coreIncidence`.  At a
**self-loop of the core** -- a slot with `core.tail slot = core.head slot` --
that multiplicity is `2` at a single branch vertex, which is exactly the
hypothesis of §3.  Nothing else about the member is used: not `Open`, not
`HasOddMult`, not the request, and nothing about which datum it is. -/

section Member

variable {n p : ℕ} {core : Core n p} {y : Fin p → ℚ}

open DraismaVargas.LocalCases.StablePathCount in
/-- A self-loop slot of the core puts **both** ends of its stable row at one
branch vertex. -/
theorem incidenceCount_eq_two_of_core_loop (member : FibreMember core y degree)
    {slot : Fin p} (hLoop : core.tail slot = core.head slot) :
    incidenceCount member.data (member.ident.vertex.symm (core.tail slot)).1
      (member.ident.row.symm slot) = 2 := by
  have hInc := member.ident.incidence (member.ident.vertex.symm (core.tail slot)) slot
  rw [Equiv.apply_symm_apply] at hInc
  rw [hInc, coreIncidence, ite_eq_left rfl, ite_eq_left hLoop.symm]

/-- **`φ(C)` is a leaf, for every member over a core with a self-loop.**  The
stable row of a self-loop slot is the leaf row `h(v)` of a leaf `v` of that
member's target tree.

The quantification is the point: `member` is an arbitrary member of the
labelled fibre over an arbitrary core and an arbitrary length vector, with no
positivity, openness, oddness or genericity hypothesis, and with its target
tree, gluing datum and sheet partitions all existentially given. -/
theorem exists_leafRow_of_core_loop (member : FibreMember core y degree)
    {slot : Fin p} (hLoop : core.tail slot = core.head slot) :
    ∃ (leaf : member.target.V) (hLeaf : IsLeafVertex member.target leaf),
      LeafFibre.leafRow member.fullDim hLeaf =
        member.fullDim.labelling.row (member.ident.row.symm slot) := by
  refine exists_leafRow_eq_of_loopRow member.fullDim (branch :=
    (member.ident.vertex.symm (core.tail slot)).1) ?_
    (incidenceCount_eq_two_of_core_loop member hLoop)
  have hThree := (member.ident.vertex.symm (core.tail slot)).2
  omega

/-! ## 6.  Distinct self-loops give distinct leaves -/

/-- The leaf of the member's target selected by a self-loop slot of the core. -/
noncomputable def loopLeaf (member : FibreMember core y degree) {slot : Fin p}
    (hLoop : core.tail slot = core.head slot) : member.target.V :=
  (exists_leafRow_of_core_loop member hLoop).choose

theorem loopLeaf_isLeafVertex (member : FibreMember core y degree) {slot : Fin p}
    (hLoop : core.tail slot = core.head slot) :
    IsLeafVertex member.target (loopLeaf member hLoop) :=
  (exists_leafRow_of_core_loop member hLoop).choose_spec.choose

theorem leafRow_loopLeaf (member : FibreMember core y degree) {slot : Fin p}
    (hLoop : core.tail slot = core.head slot) :
    LeafFibre.leafRow member.fullDim (loopLeaf_isLeafVertex member hLoop) =
      member.fullDim.labelling.row (member.ident.row.symm slot) :=
  (exists_leafRow_of_core_loop member hLoop).choose_spec.choose_spec

/-- **Distinct self-loop slots of the core select distinct leaves of the
target.**  Two self-loops landing on one leaf would share the leaf's row `h(v)`,
and the row determines the slot through `labelling.row` and `ident.row`. -/
theorem loopLeaf_inj (member : FibreMember core y degree) {first second : Fin p}
    (hFirst : core.tail first = core.head first)
    (hSecond : core.tail second = core.head second)
    (hEq : loopLeaf member hFirst = loopLeaf member hSecond) : first = second := by
  have hTransport : ∀ (v w : member.target.V) (hv : IsLeafVertex member.target v)
      (hw : IsLeafVertex member.target w), v = w →
      LeafFibre.leafRow member.fullDim hv = LeafFibre.leafRow member.fullDim hw := by
    intro v w hv hw hvw
    subst hvw
    rfl
  have hLeafRowEq := hTransport _ _ (loopLeaf_isLeafVertex member hFirst)
    (loopLeaf_isLeafVertex member hSecond) hEq
  have hRows := ((leafRow_loopLeaf member hFirst).symm.trans hLeafRowEq).trans
    (leafRow_loopLeaf member hSecond)
  exact member.ident.row.symm.injective (member.fullDim.labelling.row.injective hRows)


/-- The injection of §6, as a map of subtypes. -/
noncomputable def loopLeafMap (member : FibreMember core y degree) :
    {slot : Fin p // core.tail slot = core.head slot} →
      {vertex : member.target.V // IsLeafVertex member.target vertex} :=
  fun slot ↦ ⟨loopLeaf member slot.2, loopLeaf_isLeafVertex member slot.2⟩

theorem loopLeafMap_injective (member : FibreMember core y degree) :
    Function.Injective (loopLeafMap member) := by
  intro first second hEq
  exact Subtype.ext (loopLeaf_inj member first.2 second.2 (congrArg Subtype.val hEq))

/-- **The leaf half of the valency census.**  The
target tree of **every** member of the labelled fibre over `(core, y)` has at
least as many leaves as the core has self-loops. -/
theorem card_loopSlots_le_leafCount (member : FibreMember core y degree) :
    Fintype.card {slot : Fin p // core.tail slot = core.head slot}
      ≤ leafCount member.target := by
  classical
  have hle := Fintype.card_le_of_injective _ (loopLeafMap_injective member)
  have hcard : Fintype.card {vertex : member.target.V // IsLeafVertex member.target vertex}
      = leafCount member.target := by
    simp [leafCount, leafVertices, Fintype.card_subtype]
  omega

end Member
/-! ## 7.  At the caterpillar of loops

`catCore m` is the stable core of `H^CL_g` for `g = 2m + 2`, and its self-loops
are exactly its leaf rows (`catCore_tail_eq_head_iff`), of which there are
`g` (`Count.Caterpillar.card_leafEdges`).  So §6 reads, at the caterpillar:
**every** member's target tree has at least `g` leaves.

This is the leaf half of the valency census of the target.  Together with the
*divalent* half -- `φ(A_i)` divalent and pairwise distinct, which is not proved
here -- it would force the entire valency census of `T`, hence Part II's "every
vertex other than `u_i` and `v_i` has change 0" (in the proof of
`lm:combinatorial-structure-caterpillar-of-loops`). -/

section CaterpillarOfLoops

open DraismaVargas.Count.FibreCaterpillar
open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases.CaterpillarPruning (IsLeafEdge)

/-- **The self-loops of `catCore m` are its leaf rows.**  A row's two ends agree
exactly over a leaf edge of `T^CL_g`; over a stem or a spine edge the head is
the child vertex and the tail its strictly smaller parent. -/
theorem catCore_tail_eq_head_iff (m : ℕ) (slot : Fin (6 * m + 3)) :
    (catCore m).tail slot = (catCore m).head slot ↔ IsLeafEdge m slot := by
  rw [Fin.ext_iff]
  show branchIdx (catTailVal m slot) = branchIdx (catHeadVal m slot) ↔ IsLeafEdge m slot
  rw [branchIdx_inj (catTailVal_mod m slot) (catHeadVal_mod m slot)]
  unfold catTailVal catHeadVal
  by_cases hLeaf : IsLeafEdge m slot
  · rw [ite_eq_left hLeaf]
    simp [hLeaf]
  · rw [ite_eq_right hLeaf]
    have hPred := parentIndex_le_pred (slot.val + 1)
    simp only [hLeaf, iff_false]
    omega

/-- `catCore m` has `g = 2m + 2` self-loops. -/
theorem card_catCore_loopSlots (m : ℕ) :
    Fintype.card {slot : Fin (6 * m + 3) //
      (catCore m).tail slot = (catCore m).head slot} = 2 * m + 2 := by
  classical
  have hsets : ((Finset.univ : Finset (Fin (6 * m + 3))).filter
        fun slot ↦ (catCore m).tail slot = (catCore m).head slot)
      = (Finset.univ : Finset (Fin (6 * m + 3))).filter fun slot ↦ IsLeafEdge m slot := by
    ext slot
    simp [catCore_tail_eq_head_iff m slot]
  rw [Fintype.card_subtype, hsets, Caterpillar.card_leafEdges]

/-- **The target of every member over the caterpillar of loops has at least `g`
leaves.**  No hypothesis on the request, and none on the member: not `Open`, not
`HasOddMult`, not genericity of the lengths. -/
theorem genus_le_leafCount_catCore (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2)) :
    2 * m + 2 ≤ leafCount member.target := by
  have hle := card_loopSlots_le_leafCount member
  rwa [card_catCore_loopSlots m] at hle

end CaterpillarOfLoops

end DraismaVargas.Count.LollipopLeafRow
