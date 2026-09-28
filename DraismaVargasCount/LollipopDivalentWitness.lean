import DraismaVargasCount.LollipopLeafRow
import DraismaVargasCount.RowPosition

/-!
# The hairpin: a loop row leaves and returns in one direction

**Module name.**  Despite its name, this file contains no witness: its content
is the *hairpin*, one of the two inputs to the divalence of the image of a
lollipop branch vertex.

`DraismaVargasCount.LollipopDivalent` -- which **imports** this file -- proves
that the lollipop branch vertices `A_i` have divalent and pairwise distinct
images, as Vargas, Part II (arXiv:2609.09109) needs in its proof of
`lm:combinatorial-structure-caterpillar-of-loops`.  It does so from two inputs:
a local change-budget count, and the statement proved here, that the two ends of
a stable row with both ends at one branch vertex lie above **one** target
occurrence.  That is Part I's exclusion of case (r0-nd3) of `prop-local`.

## The argument

Draisma--Vargas Part I (arXiv:1909.12924), in the proof of the loop-and-bridge
lemma `lemma-loop-bridge`, excludes the three-direction configuration by
entering case (r0-nd3) of `prop-local` and then contradicting
`rem-leaves-min-change`.  Here the argument instead plays a closed stable row
against the tree rank of the target, as `DraismaVargasCount.LollipopLeafRow`
does:

* the loop row passes above exactly **one** leaf `v` -- at least one by
  `LollipopLeafRow.not_rowAvoidsLeaves_of_loopRow`, at most one because a row
  above two leaves would make two columns of the length matrix equal
  (`LeafFibre.leafRow_ne_of_noLeafToLeafEdge`);
* so the **only** interior vertex of the row at which the target walk
  backtracks is the leaf core vertex `A_v` of `DraismaVargasCount.LeafFibre`: everywhere
  else `r_phi <= 1` and `RowWalk.target_ne_of_localRamification_le_one` applies;
* the row therefore splits at `A_v` into two **non-backtracking** target walks,
  both starting at `phi(A)`, both containing the leaf occurrence `t_v`;
* two non-backtracking walks leaving one vertex by *different* occurrences share
  no occurrence (`edges_disjoint_of_fork`, proved here by reversing the first
  and appending the second, and applying
  `TargetGeodesic.TreeRank.nodup_edges` to the result).

Hence the two ends lie above one occurrence.

## What is proved

* `edges_disjoint_of_fork` -- the fork statement for the target, from
  connectivity and genus zero alone.  Nothing about gluing data enters.
* `eq_coreVertex_of_surviving`, `leaf_eq_of_leafRow_eq`,
  `localRamification_le_one_of_ne_coreVertex` -- the row backtracks above its
  leaf and nowhere else.
* `index_eq_zero_or_last`, `loopRow_ends`, `exists_split`,
  `target_ne_of_index_ne` -- where the ends and the hairpin sit in the ordered
  row of `DraismaVargasCount.RowWalk`.
* `loopReturnsSameDirection` -- **the headline**, for an arbitrary
  full-dimensional presentation and an arbitrary stable row with both ends at
  one branch vertex.  No genericity, no `Open`, no `HasOddMult`, no assumption
  that the datum is a constructed one.

## What is not proved here

* Nothing here is an exhaustion of the fibre.
* The **bridge** clause of Part II's `lm:bridge-and-loop` (`m(e_b) = 2`,
  `r_phi(A) = 1`) and its fibre clause above the bridge are not in this file;
  they are `LollipopBridgeFibreWitness.exists_bridge_loopBranch` and
  `PassOnceLollipopWitness.eq_bridge_of_surviving_loopBranch`.  Nothing here
  concerns the spine half of Part II's
  `lm:combinatorial-structure-caterpillar-of-loops`.
-/

namespace DraismaVargas.Count.LollipopDivalentWitness

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.OrientedTraversal
open DraismaVargas.Count.RowWalk
open DraismaVargas.Count.TargetGeodesic
open Utilities.Certificate.ExplicitPotential (Core)

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-! ## 1.  The fork: two walks leaving one vertex in different directions

Reversing the first walk and appending the second gives a single
non-backtracking walk, and `TargetGeodesic.TreeRank.nodup_edges` says a
non-backtracking walk never repeats an occurrence. -/

/-- **Two non-backtracking walks that leave one vertex by different occurrences
share no occurrence.** -/
theorem edges_disjoint_of_fork (hConn : graph_connected target) (hGenus : genus target = 0)
    {vertex : target.V} {firstEdge secondEdge : target.edges}
    {firstRest secondRest : List target.edges}
    (hFirst : IsWalkFrom vertex (firstEdge :: firstRest))
    (hSecond : IsWalkFrom vertex (secondEdge :: secondRest))
    (hNe : firstEdge ≠ secondEdge)
    {edge : target.edges} (hMemFirst : edge ∈ firstEdge :: firstRest)
    (hMemSecond : edge ∈ secondEdge :: secondRest) : False := by
  classical
  set rank := (exists_treeRank target hConn hGenus).some with hrank
  set dartsOne := dartsFrom vertex (firstEdge :: firstRest) with hdartsOne
  set dartsTwo := dartsFrom vertex (secondEdge :: secondRest) with hdartsTwo
  have hWalkOne : IsWalk dartsOne := isWalk_dartsFrom vertex _ hFirst
  have hWalkTwo : IsWalk dartsTwo := isWalk_dartsFrom vertex _ hSecond
  have hRev : IsWalk ((dartsOne.map Dart.reverse).reverse) := isWalk_reverse hWalkOne
  -- the two darts at the seam
  have hHeadOne : dartsOne.head? = some (dartOf firstEdge (otherEndOf firstEdge vertex)) :=
    head?_dartsFrom vertex firstEdge firstRest
  have hHeadTwo : dartsTwo.head? = some (dartOf secondEdge (otherEndOf secondEdge vertex)) :=
    head?_dartsFrom vertex secondEdge secondRest
  have hTailOne : (dartOf firstEdge (otherEndOf firstEdge vertex)).tail = vertex :=
    dartOf_tail (ends_pair_of_isEnd hFirst.1)
  have hTailTwo : (dartOf secondEdge (otherEndOf secondEdge vertex)).tail = vertex :=
    dartOf_tail (ends_pair_of_isEnd hSecond.1)
  have hLast : ((dartsOne.map Dart.reverse).reverse).getLast?
      = some (dartOf firstEdge (otherEndOf firstEdge vertex)).reverse := by
    rw [List.getLast?_reverse, List.head?_map, hHeadOne]
    rfl
  have hSeam : ∀ x ∈ ((dartsOne.map Dart.reverse).reverse).getLast?,
      ∀ y ∈ dartsTwo.head?, Step x y := by
    intro x hx y hy
    rw [hLast, Option.mem_def, Option.some.injEq] at hx
    rw [hHeadTwo, Option.mem_def, Option.some.injEq] at hy
    subst hx
    subst hy
    refine ⟨?_, ?_⟩
    · rw [Dart.reverse_head, hTailOne, hTailTwo]
    · rw [Dart.reverse_edge, dartOf_edge, dartOf_edge]
      exact hNe
  have hApp : IsWalk (((dartsOne.map Dart.reverse).reverse) ++ dartsTwo) :=
    List.IsChain.append hRev hWalkTwo hSeam
  have hNodup := rank.nodup_edges hApp
  rw [List.map_append] at hNodup
  have hMapOne : ((dartsOne.map Dart.reverse).reverse).map Dart.edge
      = (firstEdge :: firstRest).reverse := by
    rw [List.map_reverse, List.map_map]
    congr 1
    rw [show (Dart.edge ∘ Dart.reverse : Dart target → target.edges) = Dart.edge from rfl,
      hdartsOne, map_edge_dartsFrom]
  have hMapTwo : dartsTwo.map Dart.edge = secondEdge :: secondRest := by
    rw [hdartsTwo, map_edge_dartsFrom]
  rw [hMapOne, hMapTwo, List.nodup_append] at hNodup
  exact hNodup.2.2 edge (List.mem_reverse.mpr hMemFirst) edge hMemSecond rfl

/-! ## 2.  A surviving vertex above a leaf is the leaf core vertex -/

/-- **A surviving source vertex above a target leaf is `A_v`.**  The content of
`Count.RowHairpinPosition.surviving_leaf_data`, in the form this file needs. -/
theorem eq_coreVertex_of_surviving (fd : FullDimensionalSourcePresentation data coordinate)
    {x : data.SourceVertex} (hSurvives : 0 < nonDanglingValency data x)
    (hLeaf : IsLeafVertex target x.1.1) : x = LeafFibre.coreVertex fd hLeaf := by
  have hBlock : (⟨x.1.2, x.2⟩ : (data.vertexPartition x.1.1).Blocks)
      = LeafFibre.coreBlock fd hLeaf := by
    by_contra hNe
    have hZero := LeafFibre.nonDanglingValency_other fd hLeaf hNe
    change nonDanglingValency data x = 0 at hZero
    omega
  exact congrArg (StableLocalProperties.blockVertex data x.1.1) hBlock

/-- **A row passes above at most one leaf**: two leaves on one stable row make
two columns of the length matrix equal. -/
theorem leaf_eq_of_leafRow_eq (fd : FullDimensionalSourcePresentation data coordinate)
    {leaf other : target.V} (hLeaf : IsLeafVertex target leaf)
    (hOther : IsLeafVertex target other)
    (hRow : LeafFibre.leafRow fd hLeaf = LeafFibre.leafRow fd hOther) : leaf = other := by
  by_contra hNe
  exact LeafFibre.leafRow_ne_of_noLeafToLeafEdge fd
    (noLeafToLeafEdge_of_fullDimensional fd) hLeaf hOther hNe hRow

/-! ## 3.  Off the leaf, the row does not backtrack -/

/-- **Every interior vertex of a leaf row other than `A_v` has `r_phi ≤ 1`.**
Change-minimality gives `r ≤ 3 - val`; the only way to exceed one is a target
leaf, and there the vertex is that leaf's core vertex, whose row is the leaf
row -- so by §2 the leaf is `leaf` itself. -/
theorem localRamification_le_one_of_ne_coreVertex
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    (hRow : LeafFibre.leafRow fd hLeaf = fd.labelling.row path)
    {x : data.SourceVertex} (hValency : nonDanglingValency data x = 2)
    {edge : data.SourceEdge} (hEdge : OnRow data path edge) (hIncident : Incident data edge x)
    (hNe : x ≠ LeafFibre.coreVertex fd hLeaf) :
    data.localRamification x.1.1 ⟨x.1.2, x.2⟩ ≤ 1 := by
  have hLe := IndexPattern.localRamification_le_targetChange fd (wall := x.1.1) ⟨x.1.2, x.2⟩
  rw [IndexPattern.targetChange_eq_three_sub_valency fd x.1.1] at hLe
  have hPos := StableLocalProperties.incidentEdges_card_pos_of_changeMinimalAt data x.1.1
    (fd.changeMinimal x.1.1)
  by_cases hCard : (GluingDatum.incidentEdges x.1.1).card = 1
  · exfalso
    have hLeafX : IsLeafVertex target x.1.1 := hCard
    have hCoreX : x = LeafFibre.coreVertex fd hLeafX :=
      eq_coreVertex_of_surviving fd (by omega) hLeafX
    have hMem : edge ∈ LeafFibre.leafSurvivors (data := data) hLeafX :=
      LeafFibre.mem_leafSurvivors_of_incident_coreVertex fd hLeafX hEdge.survives
        (hCoreX ▸ hIncident)
    have hRowX := LeafFibre.row_eq_leafRow fd hLeafX hMem hEdge.survives
    obtain ⟨hSurvives, hPath⟩ := hEdge
    rw [hPath] at hRowX
    have hLeafEq : leaf = x.1.1 :=
      leaf_eq_of_leafRow_eq fd hLeaf hLeafX (hRow.trans hRowX)
    subst hLeafEq
    exact hNe hCoreX
  · omega

/-! ## 4.  Where the ends of the row sit

The ordered row of `DraismaVargasCount.RowWalk` is traversed from a chosen path end.
Its walk vertices are `Count.RowPosition.rowVertex`, and every interior one has
surviving valency two, so an occurrence incident to a vertex of surviving
valency three can only be the first or the last. -/

/-- **A row occurrence incident to a path end is the first or the last one.** -/
theorem index_eq_zero_or_last (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : nonDanglingValency data branch ≠ 2)
    {i : ℕ} (hi : i < (orderedRow fd.pathEnds path).length)
    (hIncident : Incident data (orderedRow fd.pathEnds path)[i] branch) :
    i = 0 ∨ (i + 1 = (orderedRow fd.pathEnds path).length ∧
      RowPosition.rowVertex fd path (i + 1) = branch) := by
  have hIncI := RowPosition.rowVertex_incident fd path hi
  have hSucc : RowPosition.rowVertex fd path (i + 1)
      = otherEnd data (orderedRow fd.pathEnds path)[i] (RowPosition.rowVertex fd path i) :=
    walkVertex_succ _ _ hi
  rcases eq_or_eq_otherEnd data hIncI hIncident with hCase | hCase
  · left
    by_contra hiNe
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hVal := RowPosition.rowVertex_valency fd path (j := j) (by omega)
    rw [← hCase] at hVal
    exact hBranch hVal
  · have hEq : RowPosition.rowVertex fd path (i + 1) = branch := hSucc.trans hCase.symm
    refine Or.inr ⟨?_, hEq⟩
    by_contra hlen
    have hVal := RowPosition.rowVertex_valency fd path (j := i) (by omega)
    rw [hEq] at hVal
    exact hBranch hVal

open DraismaVargas.LocalCases.StablePathCount in
/-- **The two ends of a loop row are its first and last occurrences**, and the
walk returns to the branch vertex. -/
theorem loopRow_ends (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : nonDanglingValency data branch ≠ 2)
    (hTwo : incidenceCount data branch path = 2) :
    ∃ (last : ℕ) (_ : last < (orderedRow fd.pathEnds path).length), 1 ≤ last ∧
      last + 1 = (orderedRow fd.pathEnds path).length ∧
      RowPosition.rowVertex fd path (last + 1) = branch ∧
      Incident data (orderedRow fd.pathEnds path)[last] branch := by
  classical
  have hStart : startVertex fd.pathEnds path = branch :=
    LollipopLeafRow.startVertex_eq_of_incidenceCount_eq_two
      (NonDanglingValency.nonDanglingValency_ne_one data fd.connected) fd.pathEnds hBranch hTwo
  set ends := (incidentEdges data branch).filter (fun edge ↦ edge.stablePath = path) with hends
  have hCard : ends.card = 2 := hTwo
  have hOneLt : 1 < ends.card := by omega
  obtain ⟨firstEnd, hfirstMem, otherEnd', hotherMem, hEndsNe⟩ := Finset.one_lt_card.mp hOneLt
  obtain ⟨second, hsecondMem, hsecondNe⟩ :
      ∃ item ∈ ends, item ≠ startEdge fd.pathEnds path := by
    by_cases hcase : firstEnd = startEdge fd.pathEnds path
    · exact ⟨otherEnd', hotherMem, fun hEq ↦ hEndsNe (hcase.trans hEq.symm)⟩
    · exact ⟨firstEnd, hfirstMem, hcase⟩
  have hsecondIncident : Incident data second.1 branch :=
    (mem_incidentEdges data branch second).mp (Finset.mem_filter.mp hsecondMem).1
  have hsecondRow : OnRow data path second.1 :=
    ⟨second.2, (Finset.mem_filter.mp hsecondMem).2⟩
  have hMem : second.1 ∈ orderedRow fd.pathEnds path :=
    (mem_orderedRow_iff fd.pathEnds path second.1).mpr hsecondRow
  obtain ⟨i, hi, hEq⟩ := List.getElem_of_mem hMem
  have hHead : (orderedRow fd.pathEnds path)[0]'(by omega)
      = (startEdge fd.pathEnds path).1 := by
    have h := (orderedRow_head? fd.pathEnds path).symm.trans
      (head?_eq_getElem (orderedRow fd.pathEnds path) (by omega))
    simpa using h.symm
  have hiNe : i ≠ 0 := by
    intro h0
    refine hsecondNe (Subtype.ext ?_)
    rw [← hEq]
    subst h0
    exact hHead
  rcases index_eq_zero_or_last fd hBranch hi (hEq ▸ hsecondIncident) with hCase | ⟨hLen, hVertex⟩
  · exact absurd hCase hiNe
  · exact ⟨i, hi, by omega, hLen, hVertex, hEq ▸ hsecondIncident⟩

/-! ## 5.  The row backtracks at the leaf, and only there -/

open DraismaVargas.LocalCases.StablePathCount in
/-- **The leaf core vertex is an interior walk vertex of the loop row.**  The
two occurrences of the row above the leaf edge are therefore *adjacent* in the
ordered row. -/
theorem exists_split (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : nonDanglingValency data branch ≠ 2)
    (hTwo : incidenceCount data branch path = 2)
    {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    (hLeafRow : LeafFibre.leafRow fd hLeaf = fd.labelling.row path) :
    ∃ k, ∃ _ : k + 1 < (orderedRow fd.pathEnds path).length,
      RowPosition.rowVertex fd path (k + 1) = LeafFibre.coreVertex fd hLeaf := by
  classical
  have hStart : startVertex fd.pathEnds path = branch :=
    LollipopLeafRow.startVertex_eq_of_incidenceCount_eq_two
      (NonDanglingValency.nonDanglingValency_ne_one data fd.connected) fd.pathEnds hBranch hTwo
  have hUVal : nonDanglingValency data (LeafFibre.coreVertex fd hLeaf) = 2 :=
    LeafFibre.nonDanglingValency_coreVertex fd hLeaf
  have hSurv : ¬ IsDangling data (LeafFibre.leafSurvivor fd hLeaf) :=
    (LeafFibre.leafSurvivor_spec fd hLeaf).2
  have hPathEq : NonDanglingEdge.stablePath
      (⟨LeafFibre.leafSurvivor fd hLeaf, hSurv⟩ : NonDanglingEdge data) = path :=
    fd.labelling.row.injective hLeafRow
  have hMem : LeafFibre.leafSurvivor fd hLeaf ∈ orderedRow fd.pathEnds path :=
    (mem_orderedRow_iff fd.pathEnds path _).mpr ⟨hSurv, hPathEq⟩
  have hIncidentU : Incident data (LeafFibre.leafSurvivor fd hLeaf)
      (LeafFibre.coreVertex fd hLeaf) :=
    LeafFibre.incident_coreVertex_of_mem_leafSurvivors fd hLeaf (LeafFibre.leafSurvivor_mem fd hLeaf)
  obtain ⟨i, hi, hEq⟩ := List.getElem_of_mem hMem
  have hIncI := RowPosition.rowVertex_incident fd path hi
  have hSucc : RowPosition.rowVertex fd path (i + 1)
      = otherEnd data (orderedRow fd.pathEnds path)[i] (RowPosition.rowVertex fd path i) :=
    walkVertex_succ _ _ hi
  rcases eq_or_eq_otherEnd data hIncI (hEq ▸ hIncidentU) with hCase | hCase
  · -- the leaf core vertex is the walk vertex before this occurrence
    have hiNe : i ≠ 0 := by
      intro h0
      rw [h0] at hCase
      have hZero : RowPosition.rowVertex fd path 0 = branch := hStart
      rw [hZero] at hCase
      exact hBranch (hCase ▸ hUVal)
    refine ⟨i - 1, by omega, ?_⟩
    rw [show i - 1 + 1 = i by omega, ← hCase]
  · -- or the walk vertex after it
    have hEnd := loopRow_ends fd hBranch hTwo
    obtain ⟨last, hlast, hlastPos, hlastLen, hlastVertex, -⟩ := hEnd
    have hiNe : i + 1 ≠ (orderedRow fd.pathEnds path).length := by
      intro hlen
      have hEqVertex : RowPosition.rowVertex fd path (i + 1) = branch := by
        rw [show i + 1 = last + 1 by omega]
        exact hlastVertex
      have : LeafFibre.coreVertex fd hLeaf = branch := by
        rw [hCase, ← hSucc, hEqVertex]
      exact hBranch (this ▸ hUVal)
    exact ⟨i, by omega, by rw [hSucc, ← hCase]⟩

open DraismaVargas.LocalCases.StablePathCount in
/-- **Away from the split index the target walk does not backtrack.**  At the
meeting vertex of two consecutive occurrences either the vertex is the leaf core
vertex -- and then the pair *is* the split pair -- or `r_phi ≤ 1` and
`RowWalk.target_ne_of_localRamification_le_one` applies. -/
theorem target_ne_of_index_ne (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    (hLeafRow : LeafFibre.leafRow fd hLeaf = fd.labelling.row path)
    {k : ℕ} (hk : k + 1 < (orderedRow fd.pathEnds path).length)
    (hCore : RowPosition.rowVertex fd path (k + 1) = LeafFibre.coreVertex fd hLeaf)
    {j : ℕ} (hj : j + 1 < (orderedRow fd.pathEnds path).length) (hjk : j ≠ k) :
    ((orderedRow fd.pathEnds path)[j].1.1 : target.edges)
      ≠ (orderedRow fd.pathEnds path)[j + 1].1.1 := by
  classical
  set row := orderedRow fd.pathEnds path with hrow
  have hNodup : row.Nodup := orderedRow_nodup fd.pathEnds path
  have hSurvives : ∀ e ∈ row, ¬ IsDangling data e := fun e he ↦
    ((mem_orderedRow_iff fd.pathEnds path e).mp he).survives
  have hOnRow : ∀ e ∈ row, OnRow data path e := fun e he ↦
    (mem_orderedRow_iff fd.pathEnds path e).mp he
  -- the meeting vertex of the pair at `j`
  have hMeetVal : nonDanglingValency data (RowPosition.rowVertex fd path (j + 1)) = 2 :=
    RowPosition.rowVertex_valency fd path hj
  have hIncJ : Incident data row[j] (RowPosition.rowVertex fd path (j + 1)) :=
    walkVertex_succ_incident (by omega)
  have hIncJ' : Incident data row[j + 1] (RowPosition.rowVertex fd path (j + 1)) :=
    RowPosition.rowVertex_incident fd path hj
  have hPairNe : row[j] ≠ row[j + 1] := by
    intro hEq
    exact absurd (hNodup.getElem_inj_iff.mp hEq) (by omega)
  by_cases hMeet : RowPosition.rowVertex fd path (j + 1) = LeafFibre.coreVertex fd hLeaf
  · exfalso
    -- the split pair is also incident there, and three survivors do not fit
    have hIncK : Incident data row[k] (LeafFibre.coreVertex fd hLeaf) := by
      rw [← hCore]; exact walkVertex_succ_incident (by omega)
    have hIncK' : Incident data row[k + 1] (LeafFibre.coreVertex fd hLeaf) := by
      rw [← hCore]; exact RowPosition.rowVertex_incident fd path hk
    rw [hMeet] at hIncJ hIncJ'
    have hUVal : nonDanglingValency data (LeafFibre.coreVertex fd hLeaf) = 2 :=
      LeafFibre.nonDanglingValency_coreVertex fd hLeaf
    have hIndex : ∀ (a b : ℕ) (ha : a < row.length) (hb : b < row.length),
        row[a]'ha = row[b]'hb → a = b :=
      fun _ _ _ _ hEq ↦ hNodup.getElem_inj_iff.mp hEq
    have hKmem : k = j ∨ k = j + 1 := by
      by_contra hno
      push Not at hno
      refine RowGeodesic.not_three_survivors hUVal (first := row[j]) (second := row[j + 1])
        (third := row[k]) hPairNe ?_ ?_ (hSurvives _ (List.getElem_mem (by omega)))
        hIncJ (hSurvives _ (List.getElem_mem (by omega))) hIncJ'
        (hSurvives _ (List.getElem_mem (by omega))) hIncK
      · intro hEq
        exact hno.1 (hIndex _ _ (by omega) (by omega) hEq).symm
      · intro hEq
        exact hno.2 (hIndex _ _ (by omega) (by omega) hEq).symm
    have hKmem' : k + 1 = j ∨ k + 1 = j + 1 := by
      by_contra hno
      push Not at hno
      refine RowGeodesic.not_three_survivors hUVal (first := row[j]) (second := row[j + 1])
        (third := row[k + 1]) hPairNe ?_ ?_ (hSurvives _ (List.getElem_mem (by omega)))
        hIncJ (hSurvives _ (List.getElem_mem (by omega))) hIncJ'
        (hSurvives _ (List.getElem_mem (by omega))) hIncK'
      · intro hEq
        exact hno.1 (hIndex _ _ (by omega) (by omega) hEq).symm
      · intro hEq
        exact hno.2 (hIndex _ _ (by omega) (by omega) hEq).symm
    omega
  · have hRam := localRamification_le_one_of_ne_coreVertex fd hLeaf hLeafRow hMeetVal
      (hOnRow _ (List.getElem_mem (show j < row.length by omega))) hIncJ hMeet
    exact target_ne_of_localRamification_le_one fd.danglingEdgeNoGlue hMeetVal hRam
      (hSurvives _ (List.getElem_mem (by omega))) hIncJ
      (hSurvives _ (List.getElem_mem (by omega))) hIncJ' hPairNe

/-- The fork statement in the shape §6 produces it. -/
theorem edges_disjoint_of_fork' (hConn : graph_connected target) (hGenus : genus target = 0)
    {vertex : target.V} {listOne listTwo : List target.edges}
    (hOne : IsWalkFrom vertex listOne) (hTwo : IsWalkFrom vertex listTwo)
    {headOne headTwo : target.edges} (hHeadOne : listOne.head? = some headOne)
    (hHeadTwo : listTwo.head? = some headTwo) (hNe : headOne ≠ headTwo)
    {edge : target.edges} (hMemOne : edge ∈ listOne) (hMemTwo : edge ∈ listTwo) : False := by
  cases listOne with
  | nil => exact absurd hHeadOne (by simp)
  | cons a restOne =>
      cases listTwo with
      | nil => exact absurd hHeadTwo (by simp)
      | cons b restTwo =>
          have ha : a = headOne := by simpa using hHeadOne
          have hb : b = headTwo := by simpa using hHeadTwo
          subst ha
          subst hb
          exact edges_disjoint_of_fork hConn hGenus hOne hTwo hNe hMemOne hMemTwo

/-! ## 6.  The hairpin hypothesis, discharged -/

open DraismaVargas.LocalCases.StablePathCount in
/-- **The hairpin.**  The two ends of a stable row with both ends at one branch
vertex lie above **one** target occurrence. -/
theorem loopReturnsSameDirection (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : nonDanglingValency data branch ≠ 2)
    (hTwo : incidenceCount data branch path = 2) :
    ∀ first second : data.SourceEdge, OnRow data path first → Incident data first branch →
      OnRow data path second → Incident data second branch →
        (first.1.1 : target.edges) = second.1.1 := by
  classical
  have hNodup : (orderedRow fd.pathEnds path).Nodup := orderedRow_nodup fd.pathEnds path
  have hSurvives : ∀ e ∈ orderedRow fd.pathEnds path, ¬ IsDangling data e := fun e he ↦
    ((mem_orderedRow_iff fd.pathEnds path e).mp he).survives
  have hStart : startVertex fd.pathEnds path = branch :=
    LollipopLeafRow.startVertex_eq_of_incidenceCount_eq_two
      (NonDanglingValency.nonDanglingValency_ne_one data fd.connected) fd.pathEnds hBranch hTwo
  obtain ⟨leaf, hLeaf, hLeafRow⟩ := LollipopLeafRow.exists_leafRow_eq_of_loopRow fd hBranch hTwo
  obtain ⟨k, hk, hCore⟩ := exists_split fd hBranch hTwo hLeaf hLeafRow
  obtain ⟨last, hlast, hlastPos, hlastLen, hlastVertex, hlastIncident⟩ :=
    loopRow_ends fd hBranch hTwo
  -- the pair meeting the leaf carries one target occurrence
  have hLeafEdge : ∀ i : ℕ, ∀ hi : i < (orderedRow fd.pathEnds path).length,
      Incident data (orderedRow fd.pathEnds path)[i] (LeafFibre.coreVertex fd hLeaf) →
      ((orderedRow fd.pathEnds path)[i].1.1 : target.edges) = leafEdge hLeaf := by
    intro i hi hIncident
    have hMem := LeafFibre.mem_leafSurvivors_of_incident_coreVertex fd hLeaf
      (hSurvives _ (List.getElem_mem hi)) hIncident
    exact ((LeafFibre.mem_leafSurvivors hLeaf).mp hMem).2
  have hSplitOne : ((orderedRow fd.pathEnds path)[k].1.1 : target.edges) = leafEdge hLeaf :=
    hLeafEdge k (by omega) (by rw [← hCore]; exact walkVertex_succ_incident (by omega))
  have hSplitTwo : ((orderedRow fd.pathEnds path)[k + 1].1.1 : target.edges) = leafEdge hLeaf :=
    hLeafEdge (k + 1) hk (by rw [← hCore]; exact RowPosition.rowVertex_incident fd path hk)
  -- the key equality
  have hKey : ((orderedRow fd.pathEnds path)[0]'(by omega) : data.SourceEdge).1.1
      = ((orderedRow fd.pathEnds path)[last]'hlast : data.SourceEdge).1.1 := by
    by_contra hKeyNe
    -- the prefix, as a walk from the branch vertex
    have hWalkOne : IsWalkFrom branch.1.1
        (((orderedRow fd.pathEnds path).take (k + 1)).map
          fun e ↦ (e.1.1 : target.edges)) := by
      refine RowGeodesic.isWalkFrom_of_isChain _ branch
        (hNodup.sublist (List.take_sublist _ _))
        (fun e he ↦ hSurvives e (List.mem_of_mem_take he)) ?_ ?_ (Or.inl hBranch)
      · rw [List.isChain_iff_getElem]
        intro i hi
        rw [List.length_take] at hi
        simp only [List.getElem_take]
        exact ⟨⟨RowPosition.rowVertex fd path (i + 1),
          walkVertex_succ_incident (by omega),
          RowPosition.rowVertex_incident fd path (by omega),
          RowPosition.rowVertex_valency fd path (by omega)⟩,
          target_ne_of_index_ne fd hLeaf hLeafRow hk hCore (by omega) (by omega)⟩
      · intro e he
        rw [head?_eq_getElem _ (by rw [List.length_take]; omega)] at he
        simp only [Option.mem_def, Option.some.injEq, List.getElem_take] at he
        rw [← he]
        exact hStart ▸ (RowPosition.orderedRow_start fd path (by omega)).1
    -- the reversed suffix, as a walk from the branch vertex
    have hWalkTwo : IsWalkFrom branch.1.1
        ((((orderedRow fd.pathEnds path).reverse).take
          ((orderedRow fd.pathEnds path).length - (k + 1))).map
          fun e ↦ (e.1.1 : target.edges)) := by
      refine RowGeodesic.isWalkFrom_of_isChain _ branch
        ((List.nodup_reverse.mpr hNodup).sublist (List.take_sublist _ _))
        (fun e he ↦ hSurvives e (List.mem_reverse.mp (List.mem_of_mem_take he))) ?_ ?_
        (Or.inl hBranch)
      · rw [List.isChain_iff_getElem]
        intro i hi
        rw [List.length_take, List.length_reverse] at hi
        simp only [List.getElem_take, List.getElem_reverse]
        have hjk : (orderedRow fd.pathEnds path).length - 1 - (i + 1) ≠ k := by omega
        have hjs : (orderedRow fd.pathEnds path).length - 1 - (i + 1) + 1
            = (orderedRow fd.pathEnds path).length - 1 - i := by omega
        refine ⟨⟨RowPosition.rowVertex fd path
            ((orderedRow fd.pathEnds path).length - 1 - i), ?_, ?_, ?_⟩, ?_⟩
        · exact RowPosition.rowVertex_incident fd path (by omega)
        · rw [← hjs]
          exact walkVertex_succ_incident (by omega)
        · rw [← hjs]
          exact RowPosition.rowVertex_valency fd path (by omega)
        · have := target_ne_of_index_ne fd hLeaf hLeafRow hk hCore
            (j := (orderedRow fd.pathEnds path).length - 1 - (i + 1)) (by omega) hjk
          simp only [hjs] at this
          exact this.symm
      · intro e he
        rw [head?_eq_getElem _ (by rw [List.length_take, List.length_reverse]; omega)] at he
        simp only [Option.mem_def, Option.some.injEq, List.getElem_take,
          List.getElem_reverse] at he
        rw [← he]
        have hidx : (orderedRow fd.pathEnds path).length - 1 - 0 = last := by omega
        simp only [hidx]
        exact hlastIncident
    -- the two heads, and the shared leaf occurrence
    have hHeadOne : (((orderedRow fd.pathEnds path).take (k + 1)).map
        fun e ↦ (e.1.1 : target.edges)).head?
        = some ((orderedRow fd.pathEnds path)[0]'(by omega) : data.SourceEdge).1.1 := by
      rw [head?_eq_getElem _ (by rw [List.length_map, List.length_take]; omega)]
      simp only [List.getElem_map, List.getElem_take]
    have hHeadTwo : (((orderedRow fd.pathEnds path).reverse.take
        ((orderedRow fd.pathEnds path).length - (k + 1))).map
        fun e ↦ (e.1.1 : target.edges)).head?
        = some ((orderedRow fd.pathEnds path)[last]'hlast : data.SourceEdge).1.1 := by
      rw [head?_eq_getElem _ (by
        rw [List.length_map, List.length_take, List.length_reverse]; omega)]
      simp only [List.getElem_map, List.getElem_take, List.getElem_reverse]
      have hidx : (orderedRow fd.pathEnds path).length - 1 - 0 = last := by omega
      simp only [hidx]
    have hMemOne : (leafEdge hLeaf) ∈ (((orderedRow fd.pathEnds path).take (k + 1)).map
        fun e ↦ (e.1.1 : target.edges)) := by
      rw [← hSplitOne]
      refine List.mem_map_of_mem ?_
      have : ((orderedRow fd.pathEnds path).take (k + 1))[k]'(by
        rw [List.length_take]; omega) = (orderedRow fd.pathEnds path)[k]'(by omega) := by
        simp only [List.getElem_take]
      rw [← this]
      exact List.getElem_mem _
    have hMemTwo : (leafEdge hLeaf) ∈ (((orderedRow fd.pathEnds path).reverse.take
        ((orderedRow fd.pathEnds path).length - (k + 1))).map
        fun e ↦ (e.1.1 : target.edges)) := by
      rw [← hSplitTwo]
      refine List.mem_map_of_mem ?_
      have hi : (orderedRow fd.pathEnds path).length - (k + 1) - 1
          < ((orderedRow fd.pathEnds path).reverse.take
            ((orderedRow fd.pathEnds path).length - (k + 1))).length := by
        rw [List.length_take, List.length_reverse]; omega
      have hval : ((orderedRow fd.pathEnds path).reverse.take
          ((orderedRow fd.pathEnds path).length - (k + 1)))[
            (orderedRow fd.pathEnds path).length - (k + 1) - 1]'hi
          = (orderedRow fd.pathEnds path)[k + 1]'hk := by
        simp only [List.getElem_take, List.getElem_reverse]
        have hidx : (orderedRow fd.pathEnds path).length - 1 -
            ((orderedRow fd.pathEnds path).length - (k + 1) - 1) = k + 1 := by omega
        simp only [hidx]
      rw [← hval]
      exact List.getElem_mem _
    exact edges_disjoint_of_fork' fd.targetConnected fd.targetGenus hWalkOne hWalkTwo
      hHeadOne hHeadTwo hKeyNe hMemOne hMemTwo
  -- every surviving row occurrence at the branch vertex is the first or the last
  have hClassify : ∀ e : data.SourceEdge, OnRow data path e → Incident data e branch →
      (e.1.1 : target.edges)
        = ((orderedRow fd.pathEnds path)[0]'(by omega) : data.SourceEdge).1.1 := by
    intro e he hinc
    obtain ⟨i, hi, hEq⟩ := List.getElem_of_mem ((mem_orderedRow_iff fd.pathEnds path e).mpr he)
    rcases index_eq_zero_or_last fd hBranch hi (hEq ▸ hinc) with h0 | ⟨hlen, -⟩
    · subst h0
      rw [← hEq]
    · have hiEq : i = last := by omega
      subst hiEq
      rw [← hEq]
      exact hKey.symm
  intro first second hFirstRow hFirstInc hSecondRow hSecondInc
  rw [hClassify first hFirstRow hFirstInc, hClassify second hSecondRow hSecondInc]

end DraismaVargas.Count.LollipopDivalentWitness
