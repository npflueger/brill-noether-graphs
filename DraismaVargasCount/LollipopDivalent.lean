module

public import DraismaVargasCount.LollipopDivalentWitness
public import DraismaVargasCount.RowHairpinPosition

@[expose] public section

/-!
# The image of a lollipop branch vertex: divalence and distinctness

**Source.**  Draisma--Vargas Part I (arXiv:1909.12924), the loop-and-bridge
lemma `lemma-loop-bridge`, cited by Vargas, Part II (arXiv:2609.09109) as
`lm:bridge-and-loop`: at a trivalent vertex `A` of `H(φ)` incident to a loop and
a bridge, `φ(A)` is divalent, `r_φ(A) = 1` and the bridge carries index
`m(e_b) = 2`.  Part II's proof of
`lm:combinatorial-structure-caterpillar-of-loops` applies it to the `g`
lollipops of the caterpillar of loops, whose images are `2g` **distinct** edges
of the target: this needs `g` distinct leaves, and `g` branch vertices `A_i`
with **divalent** and **pairwise distinct** images `φ(A_i)`.  This file proves
the second half (divalence and distinctness).

This is the companion of `DraismaVargasCount.LollipopLeafRow`, which proves the
*leaf* half (`card_loopSlots_le_leafCount`, `genus_le_leafCount_catCore`).  Both
feed the description of the members over the caterpillar of loops behind the
base count (`CaterpillarAllMembers`, step 1 of `DraismaVargasCount.Assembly`).

## What is proved

All statements are about an **arbitrary** full-dimensional presentation, and
the member-level ones about an **arbitrary** `FibreMember core y degree` -- no
`Open`, no `HasOddMult`, no genericity, no assumption that the datum is a
constructed `ballotDatum`.

* `not_isLeafVertex_of_three_le` -- a source vertex of surviving valency three
  does not lie above a **leaf** of the target.  Immediate from
  `RowHairpinPosition.surviving_leaf_data`.
* `blockCard_eq_one_of_localRamification_zero_of_two_unit_survivors` -- at a
  source vertex of surviving valency three, two of whose survivors carry index
  one, vanishing local ramification forces a **single sheet**.  This is
  Observation I of Part I (in the proof of `lemma-dangling-no-glue`;
  `StableLocalProperties.blockCard_eq_one_of_localRamification_zero`) with the
  third survivor as the distinguished occurrence.
* `card_incidentEdges_eq_two_of_unit_survivors` -- **divalence**, from the two
  hypotheses "both row ends at the branch vertex carry index one" and "they lie
  above **one** target occurrence".
* `card_incidentEdges_eq_two_of_incidenceCount_eq_two` -- **divalence, local
  form**, for a stable row with both ends at one branch vertex, with **no
  further hypothesis**.  The index hypothesis is discharged because the row is
  a leaf row, so all its indices are one (`Count.IndexPattern` through
  `Count.LollipopLeafRow`); the one-direction hypothesis is discharged by
  `Count.LollipopDivalentWitness.loopReturnsSameDirection`.
* `localRamification_eq_one_of_incidenceCount_eq_two`,
  `card_incidentSourceEdge_eq_three`, `onRow_of_ne_bridge`, `exists_bridge`,
  `blockCard_and_bridge_index`, `blockCard_eq_two_of_incidenceCount_eq_two`,
  `sourceEdgeIndex_eq_two_of_not_onRow` -- **the bridge clause of
  `lm:bridge-and-loop`**: `r_phi(A) = 1`, `A`
  carries exactly three incident occurrences (so none is dangling), exactly one
  of them is off the loop row, and the local degree at `A` and the index of that
  bridge occurrence are both `2`.
* `sourceVertex_eq_of_divalent_of_three_le` -- **pairwise distinctness**, in the
  form that carries it: two source vertices of surviving valency three above one
  **divalent** target vertex coincide.  The change budget at a divalent target
  vertex is `1`, and each such block already spends `1`.
* the member-level forms `loopBranch`, `loopImage`, `loopImage_divalent`,
  `loopImage_inj`, and at the caterpillar `catCore_tail_inj_of_loop`,
  `genus_le_divalentCount_catCore`.
* `two_mul_leafCount_add_divalentCount` -- the valency census `2L + D = |E| + 3`
  of a genus-zero change-minimal target, `leafCount_add_divalentCount_add_trivalentCount`
  and `card_vertices_eq_edges_card_add_one`; and `leafCount_eq_catCore`,
  `divalentCount_eq_catCore`, `trivalentCount_eq_catCore` -- `L = D = g` and
  `Tr = g - 2` at a caterpillar member, from this file's `D ≥ g`,
  `LollipopLeafRow`'s `L ≥ g` and the census.  This is the change count in
  Part II's proof of `lm:combinatorial-structure-caterpillar-of-loops`: every
  target vertex other than the `g` leaves and the `g` divalent vertices is
  trivalent, i.e. has change zero.

## What is not proved here (every hypothesis, explicitly)

* Nothing here is an exhaustion of the fibre: no statement mentions
  `GeometricFibre`, `openOddCount`, `BallotFamily` or `BallotClassification`.
* **The fibre clause of `lm:bridge-and-loop` above the bridge is only partly
  here.**  `card_incidentSourceEdge_eq_three` says `A` itself carries no
  dangling occurrence; that the fibre above the bridge occurrence contains no
  other non-dangling element is `LollipopBridgeFibre.eq_bridge_of_surviving`
  (given the length-two clause) and, at a member,
  `PassOnceLollipopWitness.eq_bridge_of_surviving_loopBranch`.
* Nothing about the spine: not the spine path, not the diagonality of `A_phi`,
  not the slope sequence.
* No **member-level** form of the bridge clause is stated here:
  `blockCard_and_bridge_index` and its corollaries are about a source vertex
  with `incidenceCount = 2`, and nothing below transports them to `loopBranch`
  or names `e_b` as a core slot.  That transport is
  `DraismaVargasCount.LollipopBridgeFibreWitness`.
-/

namespace DraismaVargas.Count.LollipopDivalent

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.RowWalk
open Utilities.Certificate.ExplicitPotential (Core)

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-! ## 1.  A branch vertex does not lie above a leaf

`RowHairpinPosition.surviving_leaf_data` records that every *surviving* source
vertex above a target leaf is the unique leaf core vertex of
`DraismaVargasCount.LeafFibre`, whose surviving valency is two.  A vertex of
surviving valency three is therefore not above a leaf, with no further
input. -/

/-- **A source vertex of surviving valency at least three does not lie above a
leaf of the target.** -/
theorem not_isLeafVertex_of_three_le (fd : FullDimensionalSourcePresentation data coordinate)
    {branch : data.SourceVertex} (hBranch : 3 ≤ nonDanglingValency data branch) :
    ¬ IsLeafVertex target branch.1.1 := by
  intro hLeaf
  have hTwo := (RowHairpinPosition.surviving_leaf_data fd (by omega) hLeaf).1
  omega

/-! ## 2.  Observation I at a branch vertex with two unit survivors

`StableLocalProperties.blockCard_eq_one_of_localRamification_zero` says: if all
the incident occurrences of a block but one carry index one, and the block is
unramified, then the block is a single sheet (and the exceptional occurrence
carries index one too).  At a vertex of surviving valency three, two of whose
survivors carry index one, the hypothesis holds with the *third* survivor as
the exceptional occurrence: every other incident occurrence is dangling, and
dangling occurrences carry index one (`fd.danglingEdgeNoGlue`). -/

/-- The three surviving occurrences at a vertex of surviving valency three,
as a `Finset`. -/
private theorem survivors_eq_triple {branch : data.SourceVertex}
    (hValency : nonDanglingValency data branch = 3)
    {first second third : data.SourceEdge}
    (hFirstSurvives : ¬ IsDangling data first) (hFirstIncident : Incident data first branch)
    (hSecondSurvives : ¬ IsDangling data second) (hSecondIncident : Incident data second branch)
    (hThirdSurvives : ¬ IsDangling data third) (hThirdIncident : Incident data third branch)
    (hFS : first ≠ second) (hFT : first ≠ third) (hST : second ≠ third) :
    ((Finset.univ : Finset data.SourceEdge).filter
        fun edge ↦ ¬ IsDangling data edge ∧ Incident data edge branch)
      = {first, second, third} := by
  classical
  have hCard : ((Finset.univ : Finset data.SourceEdge).filter
      fun edge ↦ ¬ IsDangling data edge ∧ Incident data edge branch).card = 3 := by
    rw [← hValency, nonDanglingValency]
    congr 1
    ext edge
    simp
  have hsub : ({first, second, third} : Finset data.SourceEdge) ⊆
      (Finset.univ : Finset data.SourceEdge).filter
        fun edge ↦ ¬ IsDangling data edge ∧ Incident data edge branch := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact ⟨hFirstSurvives, hFirstIncident⟩
    · exact ⟨hSecondSurvives, hSecondIncident⟩
    · exact ⟨hThirdSurvives, hThirdIncident⟩
  have hthree : ({first, second, third} : Finset data.SourceEdge).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hFS, hFT]),
      Finset.card_insert_of_notMem (by simp [hST]), Finset.card_singleton]
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

/-- A third survivor exists at a vertex of surviving valency three. -/
private theorem exists_third_survivor {branch : data.SourceVertex}
    (hValency : nonDanglingValency data branch = 3)
    {first second : data.SourceEdge}
    (hFirstSurvives : ¬ IsDangling data first) (hFirstIncident : Incident data first branch)
    (hSecondSurvives : ¬ IsDangling data second) (hSecondIncident : Incident data second branch)
    (hFS : first ≠ second) :
    ∃ third : data.SourceEdge, ¬ IsDangling data third ∧ Incident data third branch ∧
      first ≠ third ∧ second ≠ third := by
  classical
  set survivors := (Finset.univ : Finset data.SourceEdge).filter
    fun edge ↦ ¬ IsDangling data edge ∧ Incident data edge branch with hsurv
  have hCard : survivors.card = 3 := by
    rw [hsurv, ← hValency, nonDanglingValency]
    congr 1
    ext edge
    simp
  have hPair : ({first, second} : Finset data.SourceEdge) ⊆ survivors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [hsurv, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl
    · exact ⟨hFirstSurvives, hFirstIncident⟩
    · exact ⟨hSecondSurvives, hSecondIncident⟩
  have hPairCard : ({first, second} : Finset data.SourceEdge).card = 2 :=
    Finset.card_pair hFS
  have hLt : ({first, second} : Finset data.SourceEdge).card < survivors.card := by omega
  obtain ⟨third, hMem, hNotMem⟩ :
      ∃ third ∈ survivors, third ∉ ({first, second} : Finset data.SourceEdge) := by
    by_contra hNo
    push Not at hNo
    exact absurd (Finset.card_le_card hNo) (by omega)
  simp only [hsurv, Finset.mem_filter, Finset.mem_univ, true_and] at hMem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hNotMem
  push Not at hNotMem
  exact ⟨third, hMem.1, hMem.2, fun h ↦ hNotMem.1 h.symm, fun h ↦ hNotMem.2 h.symm⟩

/-- **Observation I at a lollipop branch vertex.**  At a source vertex of
surviving valency three, two of whose survivors carry index one, vanishing
local ramification forces the block to be a single sheet. -/
theorem blockCard_eq_one_of_localRamification_zero_of_two_unit_survivors
    (fd : FullDimensionalSourcePresentation data coordinate)
    {branch : data.SourceVertex} (hValency : nonDanglingValency data branch = 3)
    {first second : data.SourceEdge}
    (hFirstSurvives : ¬ IsDangling data first) (hFirstIncident : Incident data first branch)
    (hSecondSurvives : ¬ IsDangling data second) (hSecondIncident : Incident data second branch)
    (hFS : first ≠ second)
    (hFirstIndex : data.sourceEdgeIndex first = 1)
    (hSecondIndex : data.sourceEdgeIndex second = 1)
    (hZero : data.localRamification branch.1.1 ⟨branch.1.2, branch.2⟩ = 0) :
    (data.vertexPartition branch.1.1).blockCard branch.1.2 = 1 := by
  classical
  obtain ⟨third, hThirdSurvives, hThirdIncident, hFT, hST⟩ :=
    exists_third_survivor hValency hFirstSurvives hFirstIncident hSecondSurvives
      hSecondIncident hFS
  have hTriple := survivors_eq_triple hValency hFirstSurvives hFirstIncident
    hSecondSurvives hSecondIncident hThirdSurvives hThirdIncident hFS hFT hST
  refine (StableLocalProperties.blockCard_eq_one_of_localRamification_zero data branch
    ⟨third, hThirdIncident⟩ ?_ hZero).1
  intro edge hNe
  by_cases hDangling : IsDangling data edge.1
  · exact fd.danglingEdgeNoGlue edge.1 hDangling
  · have hMem : edge.1 ∈ ((Finset.univ : Finset data.SourceEdge).filter
        fun item ↦ ¬ IsDangling data item ∧ Incident data item branch) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDangling, edge.2⟩
    rw [hTriple] at hMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hMem
    rcases hMem with h | h | h
    · rw [h]; exact hFirstIndex
    · rw [h]; exact hSecondIndex
    · exact absurd (Subtype.ext h) hNe

/-! ## 3.  Divalence

`fd.trivalent` bounds the surviving valency by three and
`GluingDatum.incidentEdges_card_le_three_of_changeMinimalAt` bounds the target
valency by three, so the image of a branch vertex is a leaf, divalent or
trivalent.  §1 excludes the leaf.  Trivalence of the *target* vertex is
excluded by §2: there the change budget is `3 - 3 = 0`, so the block is
unramified, hence a single sheet -- and two occurrences of index one above
**one** target occurrence need a block of at least two sheets
(`RowWalk.sourceEdgeIndex_add_le_blockCard`). -/

/-- **Divalence, in its local form.**  A source vertex of surviving valency
three carrying two distinct occurrences of index one above **one** target
occurrence lies above a **divalent** target vertex. -/
theorem card_incidentEdges_eq_two_of_unit_survivors
    (fd : FullDimensionalSourcePresentation data coordinate)
    {branch : data.SourceVertex} (hValency : nonDanglingValency data branch = 3)
    {first second : data.SourceEdge}
    (hFirstSurvives : ¬ IsDangling data first) (hFirstIncident : Incident data first branch)
    (hSecondSurvives : ¬ IsDangling data second) (hSecondIncident : Incident data second branch)
    (hFS : first ≠ second)
    (hFirstIndex : data.sourceEdgeIndex first = 1)
    (hSecondIndex : data.sourceEdgeIndex second = 1)
    (hSame : (first.1.1 : target.edges) = second.1.1) :
    (GluingDatum.incidentEdges branch.1.1).card = 2 := by
  classical
  have hPos : 0 < (GluingDatum.incidentEdges branch.1.1).card :=
    StableLocalProperties.incidentEdges_card_pos_of_changeMinimalAt data branch.1.1
      (fd.changeMinimal branch.1.1)
  have hLe : (GluingDatum.incidentEdges branch.1.1).card ≤ 3 :=
    GluingDatum.incidentEdges_card_le_three_of_changeMinimalAt data fd.valid branch.1.1
      (fd.changeMinimal branch.1.1)
  have hNotLeaf : (GluingDatum.incidentEdges branch.1.1).card ≠ 1 :=
    not_isLeafVertex_of_three_le fd (by omega)
  have hNotThree : (GluingDatum.incidentEdges branch.1.1).card ≠ 3 := by
    intro hThree
    have hChange := IndexPattern.targetChange_eq_three_sub_valency fd branch.1.1
    rw [hThree] at hChange
    have hLeChange := IndexPattern.localRamification_le_targetChange fd
      (wall := branch.1.1) ⟨branch.1.2, branch.2⟩
    have hNonneg := data.localRamification_nonneg branch.1.1 (fd.valid.2 branch.1.1)
      ⟨branch.1.2, branch.2⟩
    have hZero : data.localRamification branch.1.1 ⟨branch.1.2, branch.2⟩ = 0 := by omega
    have hBlock := blockCard_eq_one_of_localRamification_zero_of_two_unit_survivors fd
      hValency hFirstSurvives hFirstIncident hSecondSurvives hSecondIncident hFS
      hFirstIndex hSecondIndex hZero
    have hAdd := sourceEdgeIndex_add_le_blockCard data hFirstIncident hSecondIncident hFS hSame
    omega
  omega

/-! ## 4.  The loop row: discharging the index hypothesis

`LollipopLeafRow.exists_leafRow_eq_of_loopRow` proves that a stable row with
both ends at one branch vertex is the leaf row `h(v)` of a leaf `v` of the
target, and `Count.IndexPattern.sourceEdgeIndex_eq_one_of_row_eq_leafRow` says
every occurrence of a leaf row carries index one.  So the only other hypothesis
of §3 at a loop row -- that its two ends lie above one target occurrence -- is
`LollipopDivalentWitness.loopReturnsSameDirection`. -/

/-- Every occurrence of a loop row carries index one. -/
theorem sourceEdgeIndex_eq_one_of_loopRow
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : nonDanglingValency data branch ≠ 2)
    (hTwo : StablePathCount.incidenceCount data branch path = 2)
    {edge : data.SourceEdge} (hEdge : OnRow data path edge) :
    data.sourceEdgeIndex edge = 1 := by
  obtain ⟨leaf, hLeaf, hRow⟩ := LollipopLeafRow.exists_leafRow_eq_of_loopRow fd hBranch hTwo
  obtain ⟨hSurvives, hPath⟩ := hEdge
  refine IndexPattern.sourceEdgeIndex_eq_one_of_row_eq_leafRow fd hLeaf hSurvives ?_
  rw [hPath, ← hRow]

open DraismaVargas.LocalCases.StablePathCount in
/-- **Divalence, local form.**  A branch vertex carrying both ends of one
stable row lies above a **divalent** target vertex.  The two ends leave in the
same direction by `LollipopDivalentWitness.loopReturnsSameDirection`, so no
hypothesis on the directions is needed.

The quantification is the point: `fd` is an arbitrary full-dimensional
presentation, `path` an arbitrary stable row, and `branch` an arbitrary source
vertex of surviving valency three carrying both of its ends. -/
theorem card_incidentEdges_eq_two_of_incidenceCount_eq_two
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : 3 ≤ nonDanglingValency data branch)
    (hTwo : StablePathCount.incidenceCount data branch path = 2) :
    (GluingDatum.incidentEdges branch.1.1).card = 2 := by
  classical
  have hValency : nonDanglingValency data branch = 3 := by
    have := fd.trivalent branch
    omega
  -- the two ends of the row at `branch`
  set ends := (incidentEdges data branch).filter (fun edge ↦ edge.stablePath = path) with hends
  have hCard : ends.card = 2 := hTwo
  have hOneLt : 1 < ends.card := by omega
  obtain ⟨first, hFirstMem, second, hSecondMem, hNe⟩ := Finset.one_lt_card.mp hOneLt
  have hFirstIncident : Incident data first.1 branch :=
    (mem_incidentEdges data branch first).mp (Finset.mem_filter.mp hFirstMem).1
  have hSecondIncident : Incident data second.1 branch :=
    (mem_incidentEdges data branch second).mp (Finset.mem_filter.mp hSecondMem).1
  have hFirstRow : OnRow data path first.1 :=
    ⟨first.2, (Finset.mem_filter.mp hFirstMem).2⟩
  have hSecondRow : OnRow data path second.1 :=
    ⟨second.2, (Finset.mem_filter.mp hSecondMem).2⟩
  refine card_incidentEdges_eq_two_of_unit_survivors fd hValency first.2 hFirstIncident
    second.2 hSecondIncident (fun hEq ↦ hNe (Subtype.ext hEq))
    (sourceEdgeIndex_eq_one_of_loopRow fd (by omega) hTwo hFirstRow)
    (sourceEdgeIndex_eq_one_of_loopRow fd (by omega) hTwo hSecondRow)
    (LollipopDivalentWitness.loopReturnsSameDirection fd (by omega) hTwo first.1 second.1
      hFirstRow hFirstIncident hSecondRow hSecondIncident)

/-! ## 4a.  The bridge

With divalence in hand the rest of Part II's `lm:bridge-and-loop` at `A` is
arithmetic.  The change budget at a divalent target vertex is `1` and the block
`A` already spends at least `1`, so `r_phi(A) = 1` exactly; then
`N(A) = r + 2 + m·(val - 2) = 3`, so `A` carries exactly three incident
occurrences, all surviving.  Two of them are the ends of the loop row, of index
one and (by the hairpin) above one target occurrence, which forces the local
degree `m(A) ≥ 2`; the balancing identity
`StableLocalProperties.sum_sourceEdgeIndex_incident` then pins
`m(A) = 2` and `m(e_b) = 2`. -/

/-- A block of surviving valency at least three above a divalent target vertex
is ramified. -/
theorem one_le_localRamification_of_three_le_of_divalent
    {vertex : data.SourceVertex} (hValency : 3 ≤ nonDanglingValency data vertex)
    (hDivalent : (GluingDatum.incidentEdges vertex.1.1).card = 2) :
    1 ≤ data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ := by
  have hForm :=
    NonDanglingValency.card_incidentSourceEdge_eq_localRamification_form data vertex
  rw [hDivalent] at hForm
  norm_num at hForm
  have hLe := NonDanglingValency.nonDanglingValency_le_card_incidentSourceEdge data vertex
  omega

open DraismaVargas.LocalCases.StablePathCount in
/-- **`r_phi(A) = 1`** at a lollipop branch vertex. -/
theorem localRamification_eq_one_of_incidenceCount_eq_two
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : 3 ≤ nonDanglingValency data branch)
    (hTwo : StablePathCount.incidenceCount data branch path = 2) :
    data.localRamification branch.1.1 ⟨branch.1.2, branch.2⟩ = 1 := by
  have hDiv := card_incidentEdges_eq_two_of_incidenceCount_eq_two fd hBranch hTwo
  have hLower := one_le_localRamification_of_three_le_of_divalent hBranch hDiv
  have hUpper := IndexPattern.localRamification_le_targetChange fd
    (wall := branch.1.1) ⟨branch.1.2, branch.2⟩
  rw [IndexPattern.targetChange_eq_three_sub_valency fd branch.1.1, hDiv] at hUpper
  omega

open DraismaVargas.LocalCases.StablePathCount in
/-- **A lollipop branch vertex carries exactly three incident occurrences**, so
none of them is dangling. -/
theorem card_incidentSourceEdge_eq_three
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : 3 ≤ nonDanglingValency data branch)
    (hTwo : StablePathCount.incidenceCount data branch path = 2) :
    Fintype.card (IncidentSourceEdge data branch) = 3 := by
  have hDiv := card_incidentEdges_eq_two_of_incidenceCount_eq_two fd hBranch hTwo
  have hForm :=
    NonDanglingValency.card_incidentSourceEdge_eq_localRamification_form data branch
  rw [hDiv, localRamification_eq_one_of_incidenceCount_eq_two fd hBranch hTwo] at hForm
  norm_num at hForm
  omega

open DraismaVargas.LocalCases.StablePathCount in
/-- Every surviving occurrence at a lollipop branch vertex other than the bridge
lies on the loop row. -/
theorem onRow_of_ne_bridge
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : 3 ≤ nonDanglingValency data branch)
    (hTwo : StablePathCount.incidenceCount data branch path = 2)
    {bridge : data.SourceEdge} (hBridgeSurvives : ¬ IsDangling data bridge)
    (hBridgeIncident : Incident data bridge branch)
    (hBridgeNotOnRow : ¬ OnRow data path bridge)
    {edge : data.SourceEdge} (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge branch) (hNe : edge ≠ bridge) :
    OnRow data path edge := by
  classical
  by_contra hNotRow
  have hValency : nonDanglingValency data branch = 3 := by
    have := fd.trivalent branch
    omega
  set ends := (incidentEdges data branch).filter (fun item ↦ item.stablePath = path) with hends
  have hCard : ends.card = 2 := hTwo
  have hOneLt : 1 < ends.card := by omega
  obtain ⟨first, hfirstMem, second, hsecondMem, hFirstSecondNe⟩ := Finset.one_lt_card.mp hOneLt
  have hfirstIncident : Incident data first.1 branch :=
    (mem_incidentEdges data branch first).mp (Finset.mem_filter.mp hfirstMem).1
  have hsecondIncident : Incident data second.1 branch :=
    (mem_incidentEdges data branch second).mp (Finset.mem_filter.mp hsecondMem).1
  have hfirstRow : OnRow data path first.1 := ⟨first.2, (Finset.mem_filter.mp hfirstMem).2⟩
  have hsecondRow : OnRow data path second.1 := ⟨second.2, (Finset.mem_filter.mp hsecondMem).2⟩
  have hsub : ({first.1, second.1, bridge, edge} : Finset data.SourceEdge) ⊆
      (Finset.univ : Finset data.SourceEdge).filter
        fun item ↦ ¬ IsDangling data item ∧ Incident data item branch := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨first.2, hfirstIncident⟩
    · exact ⟨second.2, hsecondIncident⟩
    · exact ⟨hBridgeSurvives, hBridgeIncident⟩
    · exact ⟨hSurvives, hIncident⟩
  have hFourCard : ({first.1, second.1, bridge, edge} : Finset data.SourceEdge).card = 4 := by
    have hFB : first.1 ≠ bridge := fun h ↦ hBridgeNotOnRow (h ▸ hfirstRow)
    have hSB : second.1 ≠ bridge := fun h ↦ hBridgeNotOnRow (h ▸ hsecondRow)
    have hFE : first.1 ≠ edge := fun h ↦ hNotRow (h ▸ hfirstRow)
    have hSE : second.1 ≠ edge := fun h ↦ hNotRow (h ▸ hsecondRow)
    have hFS : first.1 ≠ second.1 := fun h ↦ hFirstSecondNe (Subtype.ext h)
    rw [Finset.card_insert_of_notMem (by simp [hFS, hFB, hFE]),
      Finset.card_insert_of_notMem (by simp [hSB, hSE]),
      Finset.card_insert_of_notMem (by simp [hNe.symm]), Finset.card_singleton]
  have hle := Finset.card_le_card hsub
  rw [hFourCard] at hle
  have hSurvCard : ((Finset.univ : Finset data.SourceEdge).filter
      fun item ↦ ¬ IsDangling data item ∧ Incident data item branch).card = 3 := by
    rw [← hValency, nonDanglingValency]
    congr 1
    ext item
    simp
  omega

open DraismaVargas.LocalCases.StablePathCount in
/-- **`m(A) = 2` and `m(e_b) = 2`**: the local degree at a lollipop branch vertex
and the index of its bridge occurrence.  This is the rest of the bridge clause
of Part II's `lm:bridge-and-loop` at `A`. -/
theorem blockCard_and_bridge_index
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : 3 ≤ nonDanglingValency data branch)
    (hTwo : StablePathCount.incidenceCount data branch path = 2)
    {bridge : data.SourceEdge} (hBridgeSurvives : ¬ IsDangling data bridge)
    (hBridgeIncident : Incident data bridge branch)
    (hBridgeNotOnRow : ¬ OnRow data path bridge) :
    (data.vertexPartition branch.1.1).blockCard branch.1.2 = 2 ∧
      data.sourceEdgeIndex bridge = 2 := by
  classical
  have hDiv := card_incidentEdges_eq_two_of_incidenceCount_eq_two fd hBranch hTwo
  have hCard := card_incidentSourceEdge_eq_three fd hBranch hTwo
  -- every incident occurrence but the bridge carries index one
  have hOthers : ∀ item : IncidentSourceEdge data branch,
      item ≠ ⟨bridge, hBridgeIncident⟩ → data.sourceEdgeIndex item.1 = 1 := by
    intro item hNe
    by_cases hDangling : IsDangling data item.1
    · exact fd.danglingEdgeNoGlue item.1 hDangling
    · exact sourceEdgeIndex_eq_one_of_loopRow fd (by omega) hTwo
        (onRow_of_ne_bridge fd hBranch hTwo hBridgeSurvives hBridgeIncident hBridgeNotOnRow
          hDangling item.2
          (fun hEq ↦ hNe (Subtype.ext hEq)))
  have hShift : (∑ item : IncidentSourceEdge data branch,
      ((data.sourceEdgeIndex item.1 : ℤ) - 1)) = (data.sourceEdgeIndex bridge : ℤ) - 1 :=
    Fintype.sum_eq_single (f := fun item : IncidentSourceEdge data branch ↦
        ((data.sourceEdgeIndex item.1 : ℤ) - 1))
      (⟨bridge, hBridgeIncident⟩ : IncidentSourceEdge data branch)
      (fun item hNe ↦ by simp only [hOthers item hNe]; ring)
  have hBalance := StableLocalProperties.sum_sourceEdgeIndex_incident data branch
  rw [hDiv] at hBalance
  rw [Finset.sum_sub_distrib, hBalance] at hShift
  simp only [Finset.sum_const, Finset.card_univ, hCard, nsmul_eq_mul, mul_one] at hShift
  -- the two ends of the loop row lie above one target occurrence, both of index one
  have hTwoLe : 2 ≤ (data.vertexPartition branch.1.1).blockCard branch.1.2 := by
    set ends := (incidentEdges data branch).filter (fun item ↦ item.stablePath = path) with hends
    have hCardEnds : ends.card = 2 := hTwo
    have hOneLt : 1 < ends.card := by omega
    obtain ⟨first, hfirstMem, second, hsecondMem, hFirstSecondNe⟩ := Finset.one_lt_card.mp hOneLt
    have hfirstIncident : Incident data first.1 branch :=
      (mem_incidentEdges data branch first).mp (Finset.mem_filter.mp hfirstMem).1
    have hsecondIncident : Incident data second.1 branch :=
      (mem_incidentEdges data branch second).mp (Finset.mem_filter.mp hsecondMem).1
    have hfirstRow : OnRow data path first.1 := ⟨first.2, (Finset.mem_filter.mp hfirstMem).2⟩
    have hsecondRow : OnRow data path second.1 := ⟨second.2, (Finset.mem_filter.mp hsecondMem).2⟩
    have hEdgeNe : first.1 ≠ second.1 := fun h ↦ hFirstSecondNe (Subtype.ext h)
    have hSame := LollipopDivalentWitness.loopReturnsSameDirection fd (by omega) hTwo
      first.1 second.1 hfirstRow hfirstIncident hsecondRow hsecondIncident
    have hAdd := sourceEdgeIndex_add_le_blockCard data hfirstIncident hsecondIncident
      hEdgeNe hSame
    have h1 := sourceEdgeIndex_eq_one_of_loopRow fd (branch := branch) (by omega) hTwo hfirstRow
    have h2 := sourceEdgeIndex_eq_one_of_loopRow fd (branch := branch) (by omega) hTwo hsecondRow
    omega
  have hLeBridge : data.sourceEdgeIndex bridge
      ≤ (data.vertexPartition branch.1.1).blockCard branch.1.2 :=
    StableLocalProperties.sourceEdgeIndex_le_blockCard data branch ⟨bridge, hBridgeIncident⟩
  omega

open DraismaVargas.LocalCases.StablePathCount in
/-- **The bridge occurrence exists**: at a lollipop branch vertex exactly one of
the three survivors is off the loop row. -/
theorem exists_bridge (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : 3 ≤ nonDanglingValency data branch)
    (hTwo : StablePathCount.incidenceCount data branch path = 2) :
    ∃ bridge : data.SourceEdge, ¬ IsDangling data bridge ∧ Incident data bridge branch ∧
      ¬ OnRow data path bridge := by
  classical
  have hValency : nonDanglingValency data branch = 3 := by
    have := fd.trivalent branch
    omega
  set ends := (incidentEdges data branch).filter (fun item ↦ item.stablePath = path) with hends
  have hCard : ends.card = 2 := hTwo
  have hOneLt : 1 < ends.card := by omega
  obtain ⟨first, hfirstMem, second, hsecondMem, hFirstSecondNe⟩ := Finset.one_lt_card.mp hOneLt
  have hfirstIncident : Incident data first.1 branch :=
    (mem_incidentEdges data branch first).mp (Finset.mem_filter.mp hfirstMem).1
  have hsecondIncident : Incident data second.1 branch :=
    (mem_incidentEdges data branch second).mp (Finset.mem_filter.mp hsecondMem).1
  have hEndsEq : ends = {first, second} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hfirstMem
      · exact hsecondMem
    · rw [hCard, Finset.card_pair hFirstSecondNe]
  obtain ⟨third, hThirdSurvives, hThirdIncident, hFT, hST⟩ :=
    exists_third_survivor hValency first.2 hfirstIncident second.2 hsecondIncident
      (fun hEq ↦ hFirstSecondNe (Subtype.ext hEq))
  refine ⟨third, hThirdSurvives, hThirdIncident, ?_⟩
  rintro ⟨hSurv, hPath⟩
  have hMem : (⟨third, hThirdSurvives⟩ : NonDanglingEdge data) ∈ ends :=
    Finset.mem_filter.mpr ⟨(mem_incidentEdges data branch _).mpr hThirdIncident, hPath⟩
  rw [hEndsEq] at hMem
  rcases Finset.mem_insert.mp hMem with hEq | hEq
  · exact hFT (congrArg Subtype.val hEq).symm
  · exact hST (congrArg Subtype.val (Finset.mem_singleton.mp hEq)).symm

open DraismaVargas.LocalCases.StablePathCount in
/-- **`m(A) = 2`**: the local degree at a lollipop branch vertex, with no data
given. -/
theorem blockCard_eq_two_of_incidenceCount_eq_two
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : 3 ≤ nonDanglingValency data branch)
    (hTwo : StablePathCount.incidenceCount data branch path = 2) :
    (data.vertexPartition branch.1.1).blockCard branch.1.2 = 2 := by
  obtain ⟨bridge, hSurv, hInc, hOff⟩ := exists_bridge fd hBranch hTwo
  exact (blockCard_and_bridge_index fd hBranch hTwo hSurv hInc hOff).1

open DraismaVargas.LocalCases.StablePathCount in
/-- **`m(e_b) = 2`**: every surviving occurrence at a lollipop branch vertex off
the loop row carries index two.  With `exists_bridge` this completes the bridge
clause of Part II's `lm:bridge-and-loop` at `A`. -/
theorem sourceEdgeIndex_eq_two_of_not_onRow
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : 3 ≤ nonDanglingValency data branch)
    (hTwo : StablePathCount.incidenceCount data branch path = 2)
    {bridge : data.SourceEdge} (hBridgeSurvives : ¬ IsDangling data bridge)
    (hBridgeIncident : Incident data bridge branch)
    (hBridgeNotOnRow : ¬ OnRow data path bridge) :
    data.sourceEdgeIndex bridge = 2 :=
  (blockCard_and_bridge_index fd hBranch hTwo hBridgeSurvives hBridgeIncident hBridgeNotOnRow).2

/-! ## 5.  Pairwise distinctness

Above a **divalent** target vertex the change budget is `ch = 3 - 2 = 1`
(`IndexPattern.targetChange_eq_three_sub_valency`), and a block of surviving
valency at least three already spends `r = N - 2 ≥ 1` of it
(`NonDanglingValency.card_incidentSourceEdge_eq_localRamification_form` with
`val = 2`).  Two such blocks would spend two. -/

/-- **Pairwise distinctness, in the form that carries it.**  Two source vertices
of surviving valency at least three above **one divalent** target vertex are
equal. -/
theorem sourceVertex_eq_of_divalent_of_three_le
    (fd : FullDimensionalSourcePresentation data coordinate)
    {first second : data.SourceVertex}
    (hFirst : 3 ≤ nonDanglingValency data first)
    (hSecond : 3 ≤ nonDanglingValency data second)
    (hTarget : (first.1.1 : target.V) = second.1.1)
    (hDivalent : (GluingDatum.incidentEdges first.1.1).card = 2) :
    first = second := by
  classical
  by_contra hNe
  obtain ⟨⟨placeFirst, sheetFirst⟩, hReprFirst⟩ := first
  obtain ⟨⟨placeSecond, sheetSecond⟩, hReprSecond⟩ := second
  simp only at hTarget hDivalent hFirst hSecond
  subst hTarget
  have hSheetNe : sheetFirst ≠ sheetSecond := by
    intro hEq
    subst hEq
    exact hNe rfl
  have hReprOne : (data.vertexPartition placeFirst).repr sheetFirst = sheetFirst := hReprFirst
  have hReprTwo : (data.vertexPartition placeFirst).repr sheetSecond = sheetSecond := hReprSecond
  have hBlockNe : (⟨sheetFirst, hReprOne⟩ : (data.vertexPartition placeFirst).Blocks)
      ≠ ⟨sheetSecond, hReprTwo⟩ := fun hEq ↦ hSheetNe (congrArg Subtype.val hEq)
  have hFirstRam : 1 ≤ data.localRamification placeFirst ⟨sheetFirst, hReprOne⟩ :=
    one_le_localRamification_of_three_le_of_divalent
      (vertex := (⟨(placeFirst, sheetFirst), hReprFirst⟩ : data.SourceVertex)) hFirst hDivalent
  have hSecondRam : 1 ≤ data.localRamification placeFirst ⟨sheetSecond, hReprTwo⟩ :=
    one_le_localRamification_of_three_le_of_divalent
      (vertex := (⟨(placeFirst, sheetSecond), hReprSecond⟩ : data.SourceVertex)) hSecond hDivalent
  have hNonneg : ∀ block : (data.vertexPartition placeFirst).Blocks,
      0 ≤ data.localRamification placeFirst block := fun block ↦
    data.localRamification_nonneg placeFirst (fd.valid.2 placeFirst) block
  have hsub : ({⟨sheetFirst, hReprOne⟩, ⟨sheetSecond, hReprTwo⟩} :
      Finset (data.vertexPartition placeFirst).Blocks) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hpair : (∑ block ∈ ({⟨sheetFirst, hReprOne⟩, ⟨sheetSecond, hReprTwo⟩} :
        Finset (data.vertexPartition placeFirst).Blocks),
        data.localRamification placeFirst block)
      = data.localRamification placeFirst ⟨sheetFirst, hReprOne⟩ +
        data.localRamification placeFirst ⟨sheetSecond, hReprTwo⟩ :=
    Finset.sum_pair hBlockNe
  have hle := hpair.symm.trans_le
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun block _ _ ↦ hNonneg block))
  have hChange := IndexPattern.targetChange_eq_three_sub_valency fd placeFirst
  rw [hDivalent] at hChange
  unfold GluingDatum.targetChange at hChange
  omega

/-! ## 6.  The member-level form -/

section Member

variable {n p : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- The branch vertex of the member carrying the self-loop slot `slot`. -/
noncomputable def loopBranch (member : FibreMember core y degree) {slot : Fin p}
    (_hLoop : core.tail slot = core.head slot) : member.data.SourceVertex :=
  (member.ident.vertex.symm (core.tail slot)).1

theorem three_le_loopBranch (member : FibreMember core y degree) {slot : Fin p}
    (hLoop : core.tail slot = core.head slot) :
    3 ≤ nonDanglingValency member.data (loopBranch member hLoop) :=
  (member.ident.vertex.symm (core.tail slot)).2

/-- Its image in the member's target tree: Part II's `phi(A_i)`. -/
noncomputable def loopImage (member : FibreMember core y degree) {slot : Fin p}
    (hLoop : core.tail slot = core.head slot) : member.target.V :=
  (loopBranch member hLoop).1.1

/-- **Divalence, member level.**  For every member of the
labelled fibre over a core with a self-loop, the branch vertex of that self-loop
has a **divalent** image in the member's target tree. -/
theorem loopImage_divalent (member : FibreMember core y degree) {slot : Fin p}
    (hLoop : core.tail slot = core.head slot) :
    (GluingDatum.incidentEdges (loopImage member hLoop)).card = 2 :=
  card_incidentEdges_eq_two_of_incidenceCount_eq_two member.fullDim
    (three_le_loopBranch member hLoop)
    (LollipopLeafRow.incidenceCount_eq_two_of_core_loop member hLoop)

/-- **Distinctness, member level.**  Self-loops at distinct core vertices have
distinct images. -/
theorem loopImage_inj (member : FibreMember core y degree) {first second : Fin p}
    (hFirst : core.tail first = core.head first)
    (hSecond : core.tail second = core.head second)
    (hEq : loopImage member hFirst = loopImage member hSecond) :
    core.tail first = core.tail second := by
  have hVertexEq : loopBranch member hFirst = loopBranch member hSecond :=
    sourceVertex_eq_of_divalent_of_three_le member.fullDim
      (three_le_loopBranch member hFirst) (three_le_loopBranch member hSecond) hEq
      (loopImage_divalent member hFirst)
  have hBranchEq : member.ident.vertex.symm (core.tail first)
      = member.ident.vertex.symm (core.tail second) := Subtype.ext hVertexEq
  simpa using congrArg member.ident.vertex hBranchEq

/-! ## 7.  Counting the divalent vertices -/

end Member

/-- The divalent vertices of the target. -/
def divalentVertices (target : CFGraph) : Finset target.V :=
  Finset.univ.filter fun vertex ↦ (GluingDatum.incidentEdges vertex).card = 2

/-- `D`, the number of divalent vertices of the target. -/
def divalentCount (target : CFGraph) : ℕ := (divalentVertices target).card

/-- The trivalent vertices of the target. -/
def trivalentVertices (target : CFGraph) : Finset target.V :=
  Finset.univ.filter fun vertex ↦ (GluingDatum.incidentEdges vertex).card = 3

/-- `Tr`, the number of trivalent vertices of the target. -/
def trivalentCount (target : CFGraph) : ℕ := (trivalentVertices target).card

section Member

variable {n p : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- **The divalent analogue of `LollipopLeafRow.card_loopSlots_le_leafCount`.**
The target tree of every member has at least as many **divalent** vertices as
the core has self-loops, provided distinct self-loops sit at distinct core
vertices. -/
theorem card_loopSlots_le_divalentCount (member : FibreMember core y degree)
    (hTails : ∀ first second : Fin p, core.tail first = core.head first →
      core.tail second = core.head second → core.tail first = core.tail second →
        first = second) :
    Fintype.card {slot : Fin p // core.tail slot = core.head slot}
      ≤ divalentCount member.target := by
  classical
  have hInj : Function.Injective
      (fun slot : {slot : Fin p // core.tail slot = core.head slot} ↦
        (⟨loopImage member slot.2, by
            simpa only [divalentVertices, Finset.mem_filter, Finset.mem_univ, true_and] using
              loopImage_divalent member slot.2⟩ :
          {vertex : member.target.V // vertex ∈ divalentVertices member.target})) := by
    intro first second hEq
    exact Subtype.ext (hTails first.1 second.1 first.2 second.2
      (loopImage_inj member first.2 second.2 (congrArg Subtype.val hEq)))
  have hle := Fintype.card_le_of_injective _ hInj
  simpa only [divalentCount, Fintype.card_coe] using hle

end Member

/-! ## 8.  The valency census of the target

Change-minimality gives `ch(v) = 3 - val(v)` at every target vertex and bounds
`val(v)` between one and three, so `sum_v ch(v) = 2L + D`.  The same sum is
computed by the Draisma--Vargas total-change formula
(`GluingDatum.totalChange`), which at `genus target = 0` and a saturated
dimension formula is `|E(T)| + 3`.  Over the caterpillar of loops
(`|E(T)| = 3g - 3`) this is `2L + D = 3g`, the Riemann--Hurwitz count in Part
II's proof of `lm:combinatorial-structure-caterpillar-of-loops`, with no
Riemann--Hurwitz input beyond what change-minimality already gives. -/

private theorem sum_indicator (P : target.V → Prop) [DecidablePred P] (c : ℤ) :
    (∑ vertex : target.V, if P vertex then c else 0)
      = ((Finset.univ.filter P).card : ℤ) * c := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- **The total change of a full-dimensional datum is `|E(T)| + 3`.** -/
theorem sum_targetChange_eq_edges_card_add_three
    (fd : FullDimensionalSourcePresentation data coordinate) :
    (∑ vertex : target.V, data.targetChange vertex) = (target.edges.card : ℤ) + 3 := by
  rw [data.totalChange, fd.targetGenus, fd.saturated]
  ring

/-- **`2L + D = |E(T)| + 3`**, the valency census of the target. -/
theorem two_mul_leafCount_add_divalentCount
    (fd : FullDimensionalSourcePresentation data coordinate) :
    2 * leafCount target + divalentCount target = target.edges.card + 3 := by
  have hPoint : ∀ vertex : target.V, data.targetChange vertex =
      (if IsLeafVertex target vertex then (2 : ℤ) else 0) +
        (if (GluingDatum.incidentEdges vertex).card = 2 then (1 : ℤ) else 0) := by
    intro vertex
    have hChange := IndexPattern.targetChange_eq_three_sub_valency fd vertex
    have hPos := StableLocalProperties.incidentEdges_card_pos_of_changeMinimalAt data vertex
      (fd.changeMinimal vertex)
    have hLe := GluingDatum.incidentEdges_card_le_three_of_changeMinimalAt data fd.valid vertex
      (fd.changeMinimal vertex)
    unfold IsLeafVertex
    split_ifs <;> omega
  have hSum : (∑ vertex : target.V, data.targetChange vertex)
      = 2 * (leafCount target : ℤ) + (divalentCount target : ℤ) := by
    simp_rw [hPoint]
    rw [Finset.sum_add_distrib, sum_indicator, sum_indicator]
    simp only [leafCount, leafVertices, divalentCount, divalentVertices]
    ring
  have hTotal := sum_targetChange_eq_edges_card_add_three fd
  rw [hSum] at hTotal
  omega

/-- **`L + D + Tr = |V(T)|`.**  Every target vertex of a change-minimal datum is
a leaf, divalent or trivalent. -/
theorem leafCount_add_divalentCount_add_trivalentCount
    (fd : FullDimensionalSourcePresentation data coordinate) :
    leafCount target + divalentCount target + trivalentCount target
      = Fintype.card target.V := by
  have hPoint : ∀ vertex : target.V, (1 : ℤ) =
      (if IsLeafVertex target vertex then (1 : ℤ) else 0) +
        (if (GluingDatum.incidentEdges vertex).card = 2 then (1 : ℤ) else 0) +
        (if (GluingDatum.incidentEdges vertex).card = 3 then (1 : ℤ) else 0) := by
    intro vertex
    have hPos := StableLocalProperties.incidentEdges_card_pos_of_changeMinimalAt data vertex
      (fd.changeMinimal vertex)
    have hLe := GluingDatum.incidentEdges_card_le_three_of_changeMinimalAt data fd.valid vertex
      (fd.changeMinimal vertex)
    unfold IsLeafVertex
    split_ifs <;> omega
  have hSum : ((Fintype.card target.V : ℤ))
      = (leafCount target : ℤ) + (divalentCount target : ℤ) + (trivalentCount target : ℤ) := by
    have hOne : ((Fintype.card target.V : ℤ)) = ∑ _vertex : target.V, (1 : ℤ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [hOne, Finset.sum_congr rfl (fun vertex _ ↦ hPoint vertex),
      Finset.sum_add_distrib, Finset.sum_add_distrib, sum_indicator, sum_indicator,
      sum_indicator]
    simp only [leafCount, leafVertices, divalentCount, divalentVertices, trivalentCount,
      trivalentVertices]
    ring
  omega

/-- The number of vertices of a genus-zero target is one more than its number of
occurrences. -/
theorem card_vertices_eq_edges_card_add_one
    (fd : FullDimensionalSourcePresentation data coordinate) :
    Fintype.card target.V = target.edges.card + 1 := by
  have hGenus := fd.targetGenus
  unfold genus at hGenus
  omega

/-! ## 9.  At the caterpillar of loops

Over `catCore m` the self-loops are the leaf edges, and their tails are
pairwise distinct: the tail of a leaf slot is the slot itself. -/

section CaterpillarOfLoops

open DraismaVargas.Count.FibreCaterpillar
open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases.CaterpillarPruning (IsLeafEdge)

/-- Over a leaf edge of `T^CL_g` the stable row's tail vertex is indexed by the
slot itself. -/
theorem catTailVal_eq_of_isLeafEdge (m : ℕ) {slot : Fin (6 * m + 3)}
    (hLeaf : IsLeafEdge m slot) : catTailVal m slot = slot.val := by
  have hlt := slot.isLt
  unfold IsLeafEdge at hLeaf
  unfold catTailVal parentIndex
  split_ifs <;> omega

/-- **Distinct self-loops of `catCore m` sit at distinct core vertices.** -/
theorem catCore_tail_inj_of_loop (m : ℕ) (first second : Fin (6 * m + 3))
    (hFirst : (catCore m).tail first = (catCore m).head first)
    (hSecond : (catCore m).tail second = (catCore m).head second)
    (hEq : (catCore m).tail first = (catCore m).tail second) : first = second := by
  rw [LollipopLeafRow.catCore_tail_eq_head_iff] at hFirst hSecond
  have hVal : branchIdx (catTailVal m first) = branchIdx (catTailVal m second) :=
    congrArg Fin.val hEq
  have hTail := (branchIdx_inj (catTailVal_mod m first) (catTailVal_mod m second)).mp hVal
  rw [catTailVal_eq_of_isLeafEdge m hFirst, catTailVal_eq_of_isLeafEdge m hSecond] at hTail
  exact Fin.ext hTail

variable {n p : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- The target of a member has one occurrence per request slot. -/
theorem target_edges_card (member : FibreMember core y degree) :
    member.target.edges.card = p := by
  have hCard := member.fullDim.stablePath_card
  rw [Fintype.card_congr member.ident.row, Fintype.card_fin] at hCard
  exact hCard.symm

/-- **The divalent analogue of `LollipopLeafRow.genus_le_leafCount_catCore`.**
The target tree of every member over the caterpillar of loops has at least `g`
divalent vertices. -/
theorem genus_le_divalentCount_catCore (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2)) :
    2 * m + 2 ≤ divalentCount member.target := by
  have hle := card_loopSlots_le_divalentCount member (catCore_tail_inj_of_loop m)
  rwa [LollipopLeafRow.card_catCore_loopSlots m] at hle

/-- **`L = g`**: the leaf count of the target of a caterpillar member. -/
theorem leafCount_eq_catCore (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2)) :
    leafCount member.target = 2 * m + 2 := by
  have hCensus := two_mul_leafCount_add_divalentCount member.fullDim
  rw [target_edges_card member] at hCensus
  have hLeaf := LollipopLeafRow.genus_le_leafCount_catCore m member
  have hDiv := genus_le_divalentCount_catCore m member
  omega

/-- **`D = g`**: the divalent count of the target of a caterpillar member. -/
theorem divalentCount_eq_catCore (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2)) :
    divalentCount member.target = 2 * m + 2 := by
  have hCensus := two_mul_leafCount_add_divalentCount member.fullDim
  rw [target_edges_card member] at hCensus
  have hLeaf := LollipopLeafRow.genus_le_leafCount_catCore m member
  have hDiv := genus_le_divalentCount_catCore m member
  omega

/-- **`Tr = g - 2`**: the trivalent count of the target of a caterpillar member.
Together with the two statements above this is the whole valency census of
`T^CL_g`: every vertex other than the `g` leaves and the `g` divalent vertices
is trivalent, so has change zero, as in Part II's proof of
`lm:combinatorial-structure-caterpillar-of-loops`. -/
theorem trivalentCount_eq_catCore (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2)) :
    trivalentCount member.target = 2 * m := by
  have hPartition := leafCount_add_divalentCount_add_trivalentCount member.fullDim
  have hVertices := card_vertices_eq_edges_card_add_one member.fullDim
  rw [target_edges_card member] at hVertices
  rw [leafCount_eq_catCore m member, divalentCount_eq_catCore m member,
    hVertices] at hPartition
  omega

end CaterpillarOfLoops

end DraismaVargas.Count.LollipopDivalent
