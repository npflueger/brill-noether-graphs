module

public import DraismaVargasCount.LollipopBridgeFibre

@[expose] public section

/-!
# Pass-once at the lollipop: `φ(A)` is adjacent to the leaf of its loop row

**Source.**  Draisma--Vargas Part I (arXiv:1909.12924), `lemma-pass-once`, whose Figure 7
column relation `a₂ = a₁ + a₃` is §7 below.  Vargas, Part II (arXiv:2609.09109), uses the
conclusion as the length-two clause `h_l = ⟨A, e₁, C, e₂, A⟩` of `lm:bridge-and-loop`.

This is the statement to which both the lollipop and the spine halves of the caterpillar
structure lemma reduce:

* `Count/LollipopBridgeFibre.lean` names it as
  `hAdj : leafEdge hLeaf ∈ incidentEdges branch.1.1`, the hypothesis of its
  fibre-clause statements, and proves it equivalent to "some end of the loop row
  lies above the leaf edge" (`leafAdjacent_iff_exists_end_above_leafEdge`);
* `Count/RowSingleColumnWitness.lean` reaches the same sentence from the spine side
  (`eq_two_iff_exists_end_above_leafEdge`).

## What is proved

### The headline (§8)

* `leafAdjacent_of_loopRow` -- for an **arbitrary** full-dimensional
  presentation, an arbitrary stable row `h` with both ends at one branch vertex
  `A`, and the leaf `v` whose leaf row `h` is:
  `leafEdge hLeaf ∈ GluingDatum.incidentEdges branch.1.1`.  No genericity, no
  `Open`, no `HasOddMult`, no request, no assumption that the datum is a
  constructed one.
* `onRow_target_eq_leafEdge_of_loopRow`, `exists_end_above_leafEdge_of_loopRow`
  -- the two other forms of the same statement, so that the fibre-clause statements of
  `Count/LollipopBridgeFibre.lean` and the spine-side reduction of
  `Count/RowSingleColumnWitness.lean` both follow directly.

### The route

* §1 `not_isLeafVertex_of_ne_coreVertex`,
  `localRamification_eq_zero_of_ne_coreVertex` -- **a leaf row is unramified
  away from its leaf core vertex**: the ramification there is at most one
  (`LollipopDivalentWitness.localRamification_le_one_of_ne_coreVertex`) and a
  transition would make two indices differ by one, while every index on a leaf
  row is `1` (`IndexPattern.sourceEdgeIndex_eq_one_of_row_eq_leafRow`).
* §2 `exists_pair_above_far_end` -- **the descent.**  If `φ(A)` is *not*
  adjacent to the leaf, the ordered row of `Count/RowWalk.lean` has its leaf
  split at an index `k` with `1 ≤ k` and `k + 2 ≤ last`, and the walk vertices
  `V_k`, `V_{k+2}` are two **distinct** surviving-valency-two source vertices
  above the far end `w` of the leaf edge, each carrying one of the two leaf
  survivors.  These are Part I's two passes through `w`.
* §3 `not_divalent_far_end` -- **the divalent branch.**  If `w` is divalent,
  `LollipopBridgeFibre.exists_survivor_above_leafEdge` makes every surviving
  block above `w` one of those two, §1 makes both unramified, and
  `StableLocalProperties.matrix_column_eq_of_divalent_of_surviving_localRamification_zero`
  equates the two columns of `A_φ` at `w`.
* §5--§7 -- **the trivalent branch**, Part I's Figure 7.  Above a trivalent
  target vertex every block is unramified (`localRamification_eq_zero_of_trivalent`,
  the change budget is zero), and a block with no survivor above the leaf edge
  cannot have three survivors (`not_three_survivors_sharing_direction`,
  from the index form of the local ramification against harmonicity), so it has
  exactly two, one above each of the other two occurrences, each carrying the
  whole local degree and both on one stable row (`partner_of_block`).  Hence
  `g ↦ data.sourceEdge t g.1.2` is an index-preserving bijection between the
  two columns' fibres in **every row but the leaf row**
  (`trivalentPassOnce`), and `IndexPattern.det_eq_zero_of_column_relation_and_leaf`
  finishes against the leaf column `2 e_{h(v)}`.

## What is not proved here

* Nothing here is an exhaustion of the fibre: no statement mentions
  `GeometricFibre`, `openOddCount`, `BallotFamily` or `BallotClassification`.
* Nothing about the **spine rows**.  On the spine side only the **loop** rows are
  treated, which is what `Count/RowSingleColumnWitness.lean` reduces to this statement;
  the member form is in `Count/PassOnceLollipopWitness.lean`.
* Nothing here is the **pass-once condition in general** (Part I
  `lemma-pass-once` for every row of `H`): only its conclusion at a row with
  both ends at one branch vertex is proved.  A row with a single end at a
  branch vertex, or a leaf-avoiding row, is untouched -- the latter is
  `SharpRowDenominator.rowTargetInjective_of_not_passesAboveLeaf`.
* `TrivalentPassOnce` is stated as a predicate on `data` in §4 and proved in §7
  (`trivalentPassOnce`), so it is **not** a hypothesis of the headline; the
  conditional form `leafAdjacent_of_loopRow_of_trivalentPassOnce` is kept only
  to separate the two halves of the argument.
-/

namespace DraismaVargas.Count.PassOnceLollipop

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.OrientedTraversal
open DraismaVargas.Count.RowWalk

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-! ## 1.  A leaf row is unramified away from its leaf core vertex -/

/-- **The target vertex under an interior vertex of a leaf row, other than the
leaf core vertex, is not a leaf.** -/
theorem not_isLeafVertex_of_ne_coreVertex
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    (hLeafRow : LeafFibre.leafRow fd hLeaf = fd.labelling.row path)
    {x : data.SourceVertex} (hValency : nonDanglingValency data x = 2)
    {edge : data.SourceEdge} (hEdge : OnRow data path edge) (hIncident : Incident data edge x)
    (hNe : x ≠ LeafFibre.coreVertex fd hLeaf) :
    ¬ IsLeafVertex target x.1.1 := by
  intro hLeafX
  have hCoreX : x = LeafFibre.coreVertex fd hLeafX :=
    LollipopDivalentWitness.eq_coreVertex_of_surviving fd (by omega) hLeafX
  have hMem : edge ∈ LeafFibre.leafSurvivors (data := data) hLeafX :=
    LeafFibre.mem_leafSurvivors_of_incident_coreVertex fd hLeafX hEdge.survives
      (hCoreX ▸ hIncident)
  have hRowX := LeafFibre.row_eq_leafRow fd hLeafX hMem hEdge.survives
  obtain ⟨hSurvives, hPath⟩ := hEdge
  rw [hPath] at hRowX
  have hLeafEq : leaf = x.1.1 :=
    LollipopDivalentWitness.leaf_eq_of_leafRow_eq fd hLeaf hLeafX (hLeafRow.trans hRowX)
  subst hLeafEq
  exact hNe hCoreX

/-- **A leaf row carries no transition away from its leaf core vertex.**  The
ramification there is at most one, and a transition would make the two indices
differ by one -- but every index on a leaf row is `1`. -/
theorem localRamification_eq_zero_of_ne_coreVertex
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    (hLeafRow : LeafFibre.leafRow fd hLeaf = fd.labelling.row path)
    {x : data.SourceVertex} (hValency : nonDanglingValency data x = 2)
    {edge : data.SourceEdge} (hEdge : OnRow data path edge) (hIncident : Incident data edge x)
    (hNe : x ≠ LeafFibre.coreVertex fd hLeaf) :
    data.localRamification x.1.1 ⟨x.1.2, x.2⟩ = 0 := by
  have hLe := LollipopDivalentWitness.localRamification_le_one_of_ne_coreVertex fd hLeaf
    hLeafRow hValency hEdge hIncident hNe
  have hNonneg := data.localRamification_nonneg x.1.1 (fd.valid.2 x.1.1) ⟨x.1.2, x.2⟩
  by_contra hNonzero
  have hOne : data.localRamification x.1.1 ⟨x.1.2, x.2⟩ = 1 := by omega
  obtain ⟨first, second, hNeEdges, hFirstS, hFirstI, hSecondS, hSecondI⟩ :=
    exists_pair_of_nonDanglingValency_two hValency
  have hRowFirst : OnRow data path first :=
    onRow_of_incident hValency hEdge hIncident hFirstS hFirstI
  have hRowSecond : OnRow data path second :=
    onRow_of_incident hValency hEdge hIncident hSecondS hSecondI
  have hIndexFirst : data.sourceEdgeIndex first = 1 :=
    IndexPattern.sourceEdgeIndex_eq_one_of_row_eq_leafRow fd hLeaf hFirstS
      (by rw [hRowFirst.choose_spec]; exact hLeafRow.symm)
  have hIndexSecond : data.sourceEdgeIndex second = 1 :=
    IndexPattern.sourceEdgeIndex_eq_one_of_row_eq_leafRow fd hLeaf hSecondS
      (by rw [hRowSecond.choose_spec]; exact hLeafRow.symm)
  rcases IndexPattern.sourceEdgeIndex_sub_eq_one_of_transition fd hValency hOne
    hFirstS hFirstI hSecondS hSecondI hNeEdges with h | h <;>
    rw [hIndexFirst, hIndexSecond] at h <;> omega

/-! ## 2.  The two neighbours of the leaf, when the row is longer than two -/

/-- The end of a target occurrence other than a given one. -/
theorem eq_otherEndOf {edge : target.edges} {vertex x : target.V}
    (hVertex : TargetGeodesic.IsEnd edge vertex) (hX : TargetGeodesic.IsEnd edge x)
    (hNe : x ≠ vertex) : x = TargetGeodesic.otherEndOf edge vertex := by
  unfold TargetGeodesic.IsEnd at hX
  rcases TargetGeodesic.ends_pair_of_isEnd hVertex with h | h <;> rw [h] at hX <;>
    simp only at hX <;> rcases hX with h' | h'
  · exact absurd h'.symm hNe
  · exact h'.symm
  · exact h'.symm
  · exact absurd h'.symm hNe

/-- **A source vertex above one end of the leaf edge, other than the leaf
itself, sits above the far end.** -/
theorem target_eq_otherEndOf {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    {edge : data.SourceEdge} (hTarget : (edge.1.1 : target.edges) = leafEdge hLeaf)
    {x : data.SourceVertex} (hIncident : Incident data edge x) (hNe : x.1.1 ≠ leaf) :
    x.1.1 = TargetGeodesic.otherEndOf (leafEdge hLeaf) leaf := by
  have hEndLeaf : TargetGeodesic.IsEnd (leafEdge hLeaf) leaf := by
    exact fst_eq_or_snd_eq_of_mem_incidentEdges (leafEdge_mem hLeaf)
  have hEndX : TargetGeodesic.IsEnd (leafEdge hLeaf) x.1.1 := by
    rw [← hTarget]
    exact RowGeodesic.isEnd_of_incident hIncident
  exact eq_otherEndOf hEndLeaf hEndX hNe

open DraismaVargas.LocalCases.StablePathCount in
/-- **When `φ(A)` is not adjacent to the leaf its loop row passes above, the
far end of the leaf edge carries two distinct interior vertices of that row.**
These are Part I's two passes through the leaf's neighbour `w`, in the proof of
`lemma-pass-once`. -/
theorem exists_pair_above_far_end
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : nonDanglingValency data branch ≠ 2)
    (hTwo : incidenceCount data branch path = 2)
    {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    (hLeafRow : LeafFibre.leafRow fd hLeaf = fd.labelling.row path)
    (hNotAdj : leafEdge hLeaf ∉ GluingDatum.incidentEdges branch.1.1) :
    ∃ X X' : data.SourceVertex, ∃ e e' : data.SourceEdge,
      X ≠ X' ∧ X.1.1 = X'.1.1 ∧
      nonDanglingValency data X = 2 ∧ nonDanglingValency data X' = 2 ∧
      X ≠ LeafFibre.coreVertex fd hLeaf ∧ X' ≠ LeafFibre.coreVertex fd hLeaf ∧
      OnRow data path e ∧ OnRow data path e' ∧
      (e.1.1 : target.edges) = leafEdge hLeaf ∧ (e'.1.1 : target.edges) = leafEdge hLeaf ∧
      Incident data e X ∧ Incident data e' X' := by
  classical
  obtain ⟨k, hk, hCore⟩ := LollipopDivalentWitness.exists_split fd hBranch hTwo hLeaf hLeafRow
  obtain ⟨last, hlast, hlastPos, hlastLen, hlastVertex, hlastIncident⟩ :=
    LollipopDivalentWitness.loopRow_ends fd hBranch hTwo
  set row := orderedRow fd.pathEnds path with hrow
  have hNodup : row.Nodup := orderedRow_nodup fd.pathEnds path
  have hSurv : ∀ e ∈ row, ¬ IsDangling data e := fun e he ↦
    ((mem_orderedRow_iff fd.pathEnds path e).mp he).survives
  have hOn : ∀ e ∈ row, OnRow data path e := fun e he ↦
    (mem_orderedRow_iff fd.pathEnds path e).mp he
  have hStart : startVertex fd.pathEnds path = branch :=
    LollipopLeafRow.startVertex_eq_of_incidenceCount_eq_two
      (NonDanglingValency.nonDanglingValency_ne_one data fd.connected) fd.pathEnds hBranch hTwo
  -- both occurrences at the split lie above the leaf edge
  have hLeafEdge : ∀ i : ℕ, ∀ hi : i < row.length,
      Incident data row[i] (LeafFibre.coreVertex fd hLeaf) →
      ((row[i]).1.1 : target.edges) = leafEdge hLeaf := by
    intro i hi hIncident
    have hMem := LeafFibre.mem_leafSurvivors_of_incident_coreVertex fd hLeaf
      (hSurv _ (List.getElem_mem hi)) hIncident
    exact ((LeafFibre.mem_leafSurvivors hLeaf).mp hMem).2
  have hIncKC : Incident data row[k] (LeafFibre.coreVertex fd hLeaf) := by
    rw [← hCore]; exact walkVertex_succ_incident (by omega)
  have hIncK1C : Incident data row[k + 1] (LeafFibre.coreVertex fd hLeaf) := by
    rw [← hCore]; exact RowPosition.rowVertex_incident fd path hk
  have hSplitOne : ((row[k]).1.1 : target.edges) = leafEdge hLeaf :=
    hLeafEdge k (by omega) hIncKC
  have hSplitTwo : ((row[k + 1]).1.1 : target.edges) = leafEdge hLeaf :=
    hLeafEdge (k + 1) hk hIncK1C
  -- the row is longer than two, on both sides of the split
  have hkNe : k ≠ 0 := by
    intro h0
    subst h0
    apply hNotAdj
    have hInc : Incident data row[0] branch := by
      rw [← hStart]; exact (RowPosition.orderedRow_start fd path (by omega)).1
    have hMem := ((incident_iff_target_mem_and_rel data row[0] branch).mp hInc).1
    rwa [hSplitOne] at hMem
  have hkLast : k + 1 ≠ last := by
    intro h
    subst h
    apply hNotAdj
    have hMem :=
      ((incident_iff_target_mem_and_rel data row[k + 1] branch).mp hlastIncident).1
    rwa [hSplitTwo] at hMem
  have hk2 : k + 2 < row.length := by omega
  -- the surviving valencies of the two neighbours
  have hValX : nonDanglingValency data (RowPosition.rowVertex fd path k) = 2 := by
    have h := RowPosition.rowVertex_valency fd path (j := k - 1) (by omega)
    rwa [show k - 1 + 1 = k by omega] at h
  have hValX' : nonDanglingValency data (RowPosition.rowVertex fd path (k + 2)) = 2 :=
    RowPosition.rowVertex_valency fd path (j := k + 1) (by omega)
  have hIncX : Incident data row[k] (RowPosition.rowVertex fd path k) :=
    RowPosition.rowVertex_incident fd path (by omega)
  have hIncX' : Incident data row[k + 1] (RowPosition.rowVertex fd path (k + 2)) :=
    walkVertex_succ_incident hk
  have hIndex : ∀ (a b : ℕ) (ha : a < row.length) (hb : b < row.length),
      row[a]'ha = row[b]'hb → a = b :=
    fun _ _ _ _ hEq' ↦ hNodup.getElem_inj_iff.mp hEq'
  have hNeC : RowPosition.rowVertex fd path k ≠ LeafFibre.coreVertex fd hLeaf := by
    rw [← hCore]; exact Ne.symm (walkVertex_ne_succ (by omega))
  have hNeC' : RowPosition.rowVertex fd path (k + 2) ≠ LeafFibre.coreVertex fd hLeaf := by
    rw [← hCore]; exact walkVertex_ne_succ (by omega)
  -- the two neighbours are distinct
  have hXX' : RowPosition.rowVertex fd path k ≠ RowPosition.rowVertex fd path (k + 2) := by
    intro hEq
    have hIncPrev : Incident data row[k - 1] (RowPosition.rowVertex fd path k) := by
      have h := walkVertex_succ_incident (data := data) (row := row)
        (start := startVertex fd.pathEnds path) (j := k - 1) (by omega)
      rwa [show k - 1 + 1 = k by omega] at h
    have hIncNext : Incident data row[k + 1] (RowPosition.rowVertex fd path k) := by
      rw [hEq]; exact hIncX'
    refine RowGeodesic.not_three_survivors hValX
      (first := row[k - 1]) (second := row[k]) (third := row[k + 1])
      (fun h ↦ absurd (hIndex _ _ (by omega) (by omega) h) (by omega))
      (fun h ↦ absurd (hIndex _ _ (by omega) (by omega) h) (by omega))
      (fun h ↦ absurd (hIndex _ _ (by omega) (by omega) h) (by omega))
      (hSurv _ (List.getElem_mem (by omega))) hIncPrev
      (hSurv _ (List.getElem_mem (by omega))) hIncX
      (hSurv _ (List.getElem_mem hk)) hIncNext
  -- and lie above the same target vertex
  have hTargetX : (RowPosition.rowVertex fd path k).1.1 =
      TargetGeodesic.otherEndOf (leafEdge hLeaf) leaf := by
    refine target_eq_otherEndOf hLeaf hSplitOne hIncX ?_
    intro hLeafEq
    exact not_isLeafVertex_of_ne_coreVertex fd hLeaf hLeafRow hValX
      (hOn _ (List.getElem_mem (by omega))) hIncX hNeC (hLeafEq ▸ hLeaf)
  have hTargetX' : (RowPosition.rowVertex fd path (k + 2)).1.1 =
      TargetGeodesic.otherEndOf (leafEdge hLeaf) leaf := by
    refine target_eq_otherEndOf hLeaf hSplitTwo hIncX' ?_
    intro hLeafEq
    exact not_isLeafVertex_of_ne_coreVertex fd hLeaf hLeafRow hValX'
      (hOn _ (List.getElem_mem hk)) hIncX' hNeC' (hLeafEq ▸ hLeaf)
  exact ⟨RowPosition.rowVertex fd path k, RowPosition.rowVertex fd path (k + 2),
    row[k], row[k + 1], hXX', hTargetX.trans hTargetX'.symm, hValX, hValX', hNeC, hNeC',
    hOn _ (List.getElem_mem (by omega)), hOn _ (List.getElem_mem hk),
    hSplitOne, hSplitTwo, hIncX, hIncX'⟩

/-! ## 3.  The divalent branch -/

/-- Transport of vanishing ramification from a source vertex to the block that
names it. -/
theorem localRamification_block_eq_zero {w : target.V}
    {block : (data.vertexPartition w).Blocks} {y : data.SourceVertex}
    (h : StableLocalProperties.blockVertex data w block = y)
    (hy : data.localRamification y.1.1 ⟨y.1.2, y.2⟩ = 0) :
    data.localRamification w block = 0 := by
  subst h
  exact hy

/-- **The divalent branch of pass-once.**  If the far end of the leaf edge is
*divalent*, the configuration of §2 cannot occur: every surviving block above it
is one of the two neighbours, both are unramified, and the two columns of `A_φ`
indexed by its incident occurrences become equal. -/
theorem not_divalent_far_end
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data}
    {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    (hLeafRow : LeafFibre.leafRow fd hLeaf = fd.labelling.row path)
    {X X' : data.SourceVertex} {e e' : data.SourceEdge}
    (hXX' : X ≠ X') (hTarget : X.1.1 = X'.1.1)
    (hValX : nonDanglingValency data X = 2) (hValX' : nonDanglingValency data X' = 2)
    (hNeC : X ≠ LeafFibre.coreVertex fd hLeaf) (hNeC' : X' ≠ LeafFibre.coreVertex fd hLeaf)
    (hOnE : OnRow data path e) (hOnE' : OnRow data path e')
    (hTargetE : (e.1.1 : target.edges) = leafEdge hLeaf)
    (hTargetE' : (e'.1.1 : target.edges) = leafEdge hLeaf)
    (hIncE : Incident data e X) (hIncE' : Incident data e' X')
    (hDivalent : (GluingDatum.incidentEdges X.1.1).card = 2) :
    False := by
  classical
  have hLeafMem : leafEdge hLeaf ∈ GluingDatum.incidentEdges X.1.1 :=
    hTargetE ▸ ((incident_iff_target_mem_and_rel data e X).mp hIncE).1
  -- the two leaf survivors are distinct and exhaust the leaf fibre
  have hEeNe : e ≠ e' := by
    intro hEq
    exact hXX' (LollipopBridgeFibre.eq_of_incident_of_target_eq hTarget hIncE (hEq ▸ hIncE'))
  have hSet : LeafFibre.leafSurvivors (data := data) hLeaf = {e, e'} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact (LeafFibre.mem_leafSurvivors hLeaf).mpr ⟨hOnE.survives, hTargetE⟩
      · rw [Finset.mem_singleton] at hx
        subst hx
        exact (LeafFibre.mem_leafSurvivors hLeaf).mpr ⟨hOnE'.survives, hTargetE'⟩
    · rw [LeafFibre.leafSurvivors_card fd hLeaf, Finset.card_pair hEeNe]
  -- both neighbours are unramified
  have hRamX : data.localRamification X.1.1 ⟨X.1.2, X.2⟩ = 0 :=
    localRamification_eq_zero_of_ne_coreVertex fd hLeaf hLeafRow hValX hOnE hIncE hNeC
  have hRamX' : data.localRamification X'.1.1 ⟨X'.1.2, X'.2⟩ = 0 :=
    localRamification_eq_zero_of_ne_coreVertex fd hLeaf hLeafRow hValX' hOnE' hIncE' hNeC'
  -- every surviving block above the far end is one of them
  have hSurvivingBlocks : ∀ f : data.SourceEdge, ¬ IsDangling data f →
      (f.1.1 : target.edges) ∈ GluingDatum.incidentEdges X.1.1 →
      data.localRamification X.1.1
        ((data.vertexPartition X.1.1).toBlock f.1.2) = 0 := by
    intro f hSurvives hMem
    set B := StableLocalProperties.blockVertex data X.1.1
      ((data.vertexPartition X.1.1).toBlock f.1.2) with hB
    have hIncB : Incident data f B := IndexPattern.incident_blockVertex hMem
    have hBTarget : (B.1.1 : target.V) = X.1.1 := rfl
    obtain ⟨g, hgSurv, hgTarget, hgInc⟩ :=
      LollipopBridgeFibre.exists_survivor_above_leafEdge fd hLeaf (vertex := B)
        (by rw [hBTarget]; exact hDivalent) (by rw [hBTarget]; exact hLeafMem)
        (LollipopBridgeFibre.nonDanglingValency_pos_of_survivor hSurvives hIncB)
    have hgMem : g ∈ LeafFibre.leafSurvivors (data := data) hLeaf :=
      (LeafFibre.mem_leafSurvivors hLeaf).mpr ⟨hgSurv, hgTarget⟩
    rw [hSet] at hgMem
    rcases Finset.mem_insert.mp hgMem with rfl | hgMem
    · exact localRamification_block_eq_zero
        (LollipopBridgeFibre.eq_of_incident_of_target_eq hBTarget hgInc hIncE) hRamX
    · rw [Finset.mem_singleton] at hgMem
      subst hgMem
      exact localRamification_block_eq_zero
        (LollipopBridgeFibre.eq_of_incident_of_target_eq (hBTarget.trans hTarget) hgInc hIncE')
        hRamX'
  -- two equal columns
  obtain ⟨first, second, hNeCols, hPair⟩ := Finset.card_eq_two.mp hDivalent
  have hFirst : first ∈ GluingDatum.incidentEdges X.1.1 := by rw [hPair]; simp
  have hSecond : second ∈ GluingDatum.incidentEdges X.1.1 := by rw [hPair]; simp
  refine fd.det_ne_zero (Matrix.det_zero_of_column_eq
    (i := fd.labelling.targetEdge.symm first) (j := fd.labelling.targetEdge.symm second)
    (fun hEq ↦ hNeCols (fd.labelling.targetEdge.symm.injective hEq)) ?_)
  intro sourceRow
  exact StableLocalProperties.matrix_column_eq_of_divalent_of_surviving_localRamification_zero
    fd.labelling X.1.1 hDivalent hSurvivingBlocks hNeCols hFirst hSecond sourceRow

/-! ## 4.  The trivalent obstruction, isolated -/

/-- **The trivalent branch of pass-once, as a named predicate.**  This is Part
I's Figure 7 configuration in the proof of `lemma-pass-once`: a *trivalent* target vertex
`w` adjacent to a leaf `v`, above which two distinct source vertices of surviving valency
two each carry a surviving occurrence over the leaf edge `t_v`.  Part I excludes it by the
column relation `a₂ = a₁ + a₃`.  Everything else in this file is unconditional; this
predicate is proved in §7 (`trivalentPassOnce`). -/
def TrivalentPassOnce (data : GluingDatum target degree) : Prop :=
  ∀ (leaf : target.V) (hLeaf : IsLeafVertex target leaf) (X X' : data.SourceVertex)
    (e e' : data.SourceEdge), X ≠ X' → X.1.1 = X'.1.1 →
    (GluingDatum.incidentEdges X.1.1).card = 3 →
    nonDanglingValency data X = 2 → nonDanglingValency data X' = 2 →
    ¬ IsDangling data e → ¬ IsDangling data e' →
    (e.1.1 : target.edges) = leafEdge hLeaf → (e'.1.1 : target.edges) = leafEdge hLeaf →
    Incident data e X → Incident data e' X' → False

open DraismaVargas.LocalCases.StablePathCount in
/-- **Pass-once at the lollipop, conditional on the trivalent configuration.**
The unconditional form is `leafAdjacent_of_loopRow` in §8, once §7 has
discharged `TrivalentPassOnce`. -/
theorem leafAdjacent_of_loopRow_of_trivalentPassOnce
    (fd : FullDimensionalSourcePresentation data coordinate)
    (hTri : TrivalentPassOnce data)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : nonDanglingValency data branch ≠ 2)
    (hTwo : incidenceCount data branch path = 2)
    {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    (hLeafRow : LeafFibre.leafRow fd hLeaf = fd.labelling.row path) :
    leafEdge hLeaf ∈ GluingDatum.incidentEdges branch.1.1 := by
  classical
  by_contra hNotAdj
  obtain ⟨X, X', e, e', hXX', hTarget, hValX, hValX', hNeC, hNeC',
    hOnE, hOnE', hTargetE, hTargetE', hIncE, hIncE'⟩ :=
    exists_pair_above_far_end fd hBranch hTwo hLeaf hLeafRow hNotAdj
  have hPos : 0 < (GluingDatum.incidentEdges X.1.1).card :=
    StableLocalProperties.incidentEdges_card_pos_of_changeMinimalAt data X.1.1
      (fd.changeMinimal X.1.1)
  have hLe : ((GluingDatum.incidentEdges X.1.1).card : ℤ) ≤ 3 := by
    have hRam := IndexPattern.localRamification_le_targetChange fd (wall := X.1.1)
      ⟨X.1.2, X.2⟩
    rw [IndexPattern.targetChange_eq_three_sub_valency fd X.1.1] at hRam
    have hNonneg := data.localRamification_nonneg X.1.1 (fd.valid.2 X.1.1) ⟨X.1.2, X.2⟩
    omega
  have hLe' : (GluingDatum.incidentEdges X.1.1).card ≤ 3 := by exact_mod_cast hLe
  interval_cases hCard : (GluingDatum.incidentEdges X.1.1).card
  · exact not_isLeafVertex_of_ne_coreVertex fd hLeaf hLeafRow hValX hOnE hIncE hNeC hCard
  · exact not_divalent_far_end fd hLeaf hLeafRow hXX' hTarget hValX hValX' hNeC hNeC'
      hOnE hOnE' hTargetE hTargetE' hIncE hIncE' hCard
  · exact hTri leaf hLeaf X X' e e' hXX' hTarget hCard hValX hValX'
      hOnE.survives hOnE'.survives hTargetE hTargetE' hIncE hIncE'

/-! ## 5.  Blocks above a trivalent target vertex -/

/-- **Above a trivalent target vertex every block is unramified**: the change
budget there is zero. -/
theorem localRamification_eq_zero_of_trivalent
    (fd : FullDimensionalSourcePresentation data coordinate) {wall : target.V}
    (hTri : (GluingDatum.incidentEdges wall).card = 3)
    (block : (data.vertexPartition wall).Blocks) :
    data.localRamification wall block = 0 := by
  have hLe := IndexPattern.localRamification_le_targetChange fd (wall := wall) block
  rw [IndexPattern.targetChange_eq_three_sub_valency fd wall, hTri] at hLe
  have hNonneg := data.localRamification_nonneg wall (fd.valid.2 wall) block
  omega

/-- **An unramified block has no three survivors two of which share a
direction.**  The index form of the local ramification makes the surviving
indices sum to `2 m(A) + 1`, while harmonicity caps them at `2 m(A)`. -/
theorem not_three_survivors_sharing_direction
    (fd : FullDimensionalSourcePresentation data coordinate)
    {B : data.SourceVertex}
    (hRam : data.localRamification B.1.1 ⟨B.1.2, B.2⟩ = 0)
    (hValency : nonDanglingValency data B = 3)
    {a b c : data.SourceEdge} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haS : ¬ IsDangling data a) (haI : Incident data a B)
    (hbS : ¬ IsDangling data b) (hbI : Incident data b B)
    (hcS : ¬ IsDangling data c) (hcI : Incident data c B)
    (hShare : (a.1.1 : target.edges) = b.1.1) : False := by
  classical
  obtain ⟨itemA, hItemA⟩ : ∃ x : IncidentSourceEdge data B, x.1 = a := ⟨⟨a, haI⟩, rfl⟩
  obtain ⟨itemB, hItemB⟩ : ∃ x : IncidentSourceEdge data B, x.1 = b := ⟨⟨b, hbI⟩, rfl⟩
  obtain ⟨itemC, hItemC⟩ : ∃ x : IncidentSourceEdge data B, x.1 = c := ⟨⟨c, hcI⟩, rfl⟩
  have hNeAB : itemA ≠ itemB := fun h ↦ hab (hItemA ▸ hItemB ▸ congrArg Subtype.val h)
  have hNeAC : itemA ≠ itemC := fun h ↦ hac (hItemA ▸ hItemC ▸ congrArg Subtype.val h)
  have hNeBC : itemB ≠ itemC := fun h ↦ hbc (hItemB ▸ hItemC ▸ congrArg Subtype.val h)
  -- the surviving incident occurrences are exactly `a`, `b`, `c`
  have hCard : ((Finset.univ : Finset (IncidentSourceEdge data B)).filter
      (fun item ↦ ¬ IsDangling data item.1)).card = 3 :=
    (StableLocalProperties.card_filter_not_isDangling_eq_nonDanglingValency data B).trans
      hValency
  have hSub : ({itemA, itemB, itemC} : Finset (IncidentSourceEdge data B)) ⊆
      (Finset.univ : Finset (IncidentSourceEdge data B)).filter
        (fun item ↦ ¬ IsDangling data item.1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases hx with rfl | rfl | rfl
    · rw [hItemA]; exact haS
    · rw [hItemB]; exact hbS
    · rw [hItemC]; exact hcS
  have hTripleCard : ({itemA, itemB, itemC} : Finset (IncidentSourceEdge data B)).card = 3 :=
    Finset.card_eq_three.mpr ⟨itemA, itemB, itemC, hNeAB, hNeAC, hNeBC, rfl⟩
  have hSet : (Finset.univ : Finset (IncidentSourceEdge data B)).filter
      (fun item ↦ ¬ IsDangling data item.1) = {itemA, itemB, itemC} :=
    (Finset.eq_of_subset_of_card_le hSub (by rw [hCard, hTripleCard])).symm
  -- the index form, evaluated on the three survivors
  have hForm := StableLocalProperties.localRamification_eq_index_form data B
  rw [hRam] at hForm
  have hRestrict : (∑ item ∈ ({itemA, itemB, itemC} : Finset (IncidentSourceEdge data B)),
      ((data.sourceEdgeIndex item.1 : ℤ) - 1)) =
      ∑ item : IncidentSourceEdge data B, ((data.sourceEdgeIndex item.1 : ℤ) - 1) := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro x _ hx
    have hDang : IsDangling data x.1 := by
      by_contra hs
      exact hx (hSet ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)
    rw [fd.danglingEdgeNoGlue x.1 hDang]
    norm_num
  have hTriple : (∑ item ∈ ({itemA, itemB, itemC} : Finset (IncidentSourceEdge data B)),
      ((data.sourceEdgeIndex item.1 : ℤ) - 1)) =
      (data.sourceEdgeIndex a : ℤ) + (data.sourceEdgeIndex b : ℤ) +
        (data.sourceEdgeIndex c : ℤ) - 3 := by
    rw [Finset.sum_insert (by simp [hNeAB, hNeAC]), Finset.sum_insert (by simp [hNeBC]),
      Finset.sum_singleton, hItemA, hItemB, hItemC]
    ring
  rw [hTriple] at hRestrict
  rw [← hRestrict] at hForm
  -- harmonicity caps the surviving indices
  have hPair := RowWalk.sourceEdgeIndex_add_le_blockCard data haI hbI hab hShare
  have hThird := StableLocalProperties.sourceEdgeIndex_le_blockCard data B ⟨c, hcI⟩
  have hPairZ : (data.sourceEdgeIndex a : ℤ) + (data.sourceEdgeIndex b : ℤ) ≤
      ((data.vertexPartition B.1.1).blockCard B.1.2 : ℤ) := by exact_mod_cast hPair
  have hThirdZ : (data.sourceEdgeIndex c : ℤ) ≤
      ((data.vertexPartition B.1.1).blockCard B.1.2 : ℤ) := by exact_mod_cast hThird
  omega

/-- **A block above a trivalent target vertex with a survivor, but none above
one of the three incident occurrences, has surviving valency exactly two.**
Three survivors would have to share a direction. -/
theorem nonDanglingValency_eq_two_of_survivor
    (fd : FullDimensionalSourcePresentation data coordinate)
    {B : data.SourceVertex} (hTri : (GluingDatum.incidentEdges B.1.1).card = 3)
    {t₁ : target.edges} (ht₁ : t₁ ∈ GluingDatum.incidentEdges B.1.1)
    (hNoSurv : ∀ x : data.SourceEdge, ¬ IsDangling data x → Incident data x B →
      (x.1.1 : target.edges) ≠ t₁)
    {g : data.SourceEdge} (hgS : ¬ IsDangling data g) (hgI : Incident data g B) :
    nonDanglingValency data B = 2 := by
  classical
  have hPos : 0 < nonDanglingValency data B :=
    LollipopBridgeFibre.nonDanglingValency_pos_of_survivor hgS hgI
  have hNeOne := NonDanglingValency.nonDanglingValency_ne_one data fd.connected B
  have hLe := fd.trivalent B
  by_contra hNe
  have hThree : nonDanglingValency data B = 3 := by omega
  have hCard : ((Finset.univ : Finset (IncidentSourceEdge data B)).filter
      (fun item ↦ ¬ IsDangling data item.1)).card = 3 :=
    (StableLocalProperties.card_filter_not_isDangling_eq_nonDanglingValency data B).trans hThree
  obtain ⟨u, v, x, huv, hux, hvx, hSet⟩ := Finset.card_eq_three.mp hCard
  have hMem : ∀ y : IncidentSourceEdge data B, y ∈ ({u, v, x} :
      Finset (IncidentSourceEdge data B)) → ¬ IsDangling data y.1 := by
    intro y hy
    rw [← hSet] at hy
    exact (Finset.mem_filter.mp hy).2
  have huS := hMem u (by simp)
  have hvS := hMem v (by simp)
  have hxS := hMem x (by simp)
  have hRam : data.localRamification B.1.1 ⟨B.1.2, B.2⟩ = 0 :=
    localRamification_eq_zero_of_trivalent fd hTri _
  -- each survivor lies above one of the two occurrences other than `t₁`
  have hTargetMem : ∀ y : IncidentSourceEdge data B, ¬ IsDangling data y.1 →
      (y.1.1.1 : target.edges) ∈ (GluingDatum.incidentEdges B.1.1).erase t₁ := by
    intro y hyS
    exact Finset.mem_erase.mpr ⟨hNoSurv y.1 hyS y.2,
      ((incident_iff_target_mem_and_rel data y.1 B).mp y.2).1⟩
  have hEraseCard : ((GluingDatum.incidentEdges B.1.1).erase t₁).card = 2 := by
    rw [Finset.card_erase_of_mem ht₁, hTri]
  -- two of the three share a direction
  have hShare : (u.1.1.1 : target.edges) = v.1.1.1 ∨ (u.1.1.1 : target.edges) = x.1.1.1 ∨
      (v.1.1.1 : target.edges) = x.1.1.1 := by
    by_contra hno
    push Not at hno
    obtain ⟨huv', hux', hvx'⟩ := hno
    have hSub : ({u.1.1.1, v.1.1.1, x.1.1.1} : Finset target.edges) ⊆
        (GluingDatum.incidentEdges B.1.1).erase t₁ := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact hTargetMem u huS
      · exact hTargetMem v hvS
      · exact hTargetMem x hxS
    have hCard3 : ({u.1.1.1, v.1.1.1, x.1.1.1} : Finset target.edges).card = 3 :=
      Finset.card_eq_three.mpr ⟨_, _, _, huv', hux', hvx', rfl⟩
    have := Finset.card_le_card hSub
    omega
  have hUV : u.1 ≠ v.1 := fun h ↦ huv (Subtype.ext h)
  have hUX : u.1 ≠ x.1 := fun h ↦ hux (Subtype.ext h)
  have hVX : v.1 ≠ x.1 := fun h ↦ hvx (Subtype.ext h)
  rcases hShare with h | h | h
  · exact not_three_survivors_sharing_direction fd hRam hThree hUV hUX hVX
      huS u.2 hvS v.2 hxS x.2 h
  · exact not_three_survivors_sharing_direction fd hRam hThree hUX hUV (Ne.symm hVX)
      huS u.2 hxS x.2 hvS v.2 h
  · exact not_three_survivors_sharing_direction fd hRam hThree hVX (Ne.symm hUV)
      (Ne.symm hUX) hvS v.2 hxS x.2 huS u.2 h

/-- **The partner of a survivor at such a block.**  Above the third incident
occurrence the block has exactly one occurrence, it is the second survivor, it
lies on the same stable row and it carries the same index. -/
theorem partner_of_block
    (fd : FullDimensionalSourcePresentation data coordinate)
    {B : data.SourceVertex} (hTri : (GluingDatum.incidentEdges B.1.1).card = 3)
    {t₁ s t : target.edges}
    (ht₁ : t₁ ∈ GluingDatum.incidentEdges B.1.1)
    (hs : s ∈ GluingDatum.incidentEdges B.1.1) (ht : t ∈ GluingDatum.incidentEdges B.1.1)
    (hst₁ : s ≠ t₁) (htt₁ : t ≠ t₁) (hst : s ≠ t)
    (hNoSurv : ∀ x : data.SourceEdge, ¬ IsDangling data x → Incident data x B →
      (x.1.1 : target.edges) ≠ t₁)
    {g : data.SourceEdge} (hgS : ¬ IsDangling data g) (hgI : Incident data g B)
    (hgT : (g.1.1 : target.edges) = s) :
    ∃ hS : ¬ IsDangling data (data.sourceEdge t g.1.2),
      NonDanglingEdge.stablePath (⟨data.sourceEdge t g.1.2, hS⟩ : NonDanglingEdge data) =
          NonDanglingEdge.stablePath (⟨g, hgS⟩ : NonDanglingEdge data) ∧
        data.sourceEdgeIndex (data.sourceEdge t g.1.2) = data.sourceEdgeIndex g ∧
        data.sourceEdge s (data.sourceEdge t g.1.2).1.2 = g := by
  classical
  have hValB := nonDanglingValency_eq_two_of_survivor fd hTri ht₁ hNoSurv hgS hgI
  have hRamB : data.localRamification B.1.1 ⟨B.1.2, B.2⟩ = 0 :=
    localRamification_eq_zero_of_trivalent fd hTri _
  obtain ⟨g', ⟨hg'Ne, hg'S, hg'I⟩, -⟩ :=
    exists_unique_other_of_nonDanglingValency_eq_two data hValB hgS hgI
  have hTargetNe : (g'.1.1 : target.edges) ≠ g.1.1 :=
    RowWalk.target_ne_of_localRamification_le_one fd.danglingEdgeNoGlue hValB (by omega)
      hg'S hg'I hgS hgI hg'Ne
  have hg'Mem : (g'.1.1 : target.edges) ∈ GluingDatum.incidentEdges B.1.1 :=
    ((incident_iff_target_mem_and_rel data g' B).mp hg'I).1
  have hEq : GluingDatum.incidentEdges B.1.1 = {t₁, s, t} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact ht₁
      · exact hs
      · exact ht
    · rw [hTri]
      exact le_of_eq
        (Finset.card_eq_three.mpr ⟨t₁, s, t, Ne.symm hst₁, Ne.symm htt₁, hst, rfl⟩).symm
  have hg'T : (g'.1.1 : target.edges) = t := by
    rw [hEq] at hg'Mem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg'Mem
    rcases hg'Mem with h | h | h
    · exact absurd h (hNoSurv g' hg'S hg'I)
    · exact absurd (h.trans hgT.symm) hTargetNe
    · exact h
  -- both survivors carry the whole local degree
  have hSum := IndexPattern.sourceEdgeIndex_add_sourceEdgeIndex fd hValB hgS hgI hg'S hg'I
    (Ne.symm hg'Ne)
  rw [hRamB, sub_zero] at hSum
  have hLeG : data.sourceEdgeIndex g ≤ (data.vertexPartition B.1.1).blockCard B.1.2 :=
    StableLocalProperties.sourceEdgeIndex_le_blockCard data B ⟨g, hgI⟩
  have hLeG' : data.sourceEdgeIndex g' ≤ (data.vertexPartition B.1.1).blockCard B.1.2 :=
    StableLocalProperties.sourceEdgeIndex_le_blockCard data B ⟨g', hg'I⟩
  have hmG : data.sourceEdgeIndex g = (data.vertexPartition B.1.1).blockCard B.1.2 := by omega
  have hmG' : data.sourceEdgeIndex g' = (data.vertexPartition B.1.1).blockCard B.1.2 := by omega
  -- an occurrence of the block carrying the whole local degree is the only one
  -- above its direction
  have hUnique : ∀ {y z : data.SourceEdge}, Incident data y B → Incident data z B →
      (y.1.1 : target.edges) = z.1.1 →
      data.sourceEdgeIndex z = (data.vertexPartition B.1.1).blockCard B.1.2 → y = z := by
    intro y z hy hz hT hm
    by_contra hne
    have hAdd := RowWalk.sourceEdgeIndex_add_le_blockCard data hy hz hne hT
    have hPos := GluingDatum.sourceEdgeIndex_pos data y
    omega
  -- the canonical occurrence above `t` through `g`'s sheet is the partner
  have hEndpoint : data.sourceEndpoint B.1.1 g.1.2 = B :=
    (data.sourceEndpoint_eq_iff B.1.1 g.1.2 B).mpr
      ⟨rfl, ((incident_iff_target_mem_and_rel data g B).mp hgI).2.symm⟩
  have hCanonInc : Incident data (data.sourceEdge t g.1.2) B := by
    have h := incident_sourceEdge_sourceEndpoint data B.1.1 t ht g.1.2
    rwa [hEndpoint] at h
  have hCanonEq : data.sourceEdge t g.1.2 = g' :=
    hUnique hCanonInc hg'I (by rw [hg'T]; rfl) hmG'
  refine ⟨hCanonEq ▸ hg'S, ?_, ?_, ?_⟩
  · have hCons : Consecutive data (⟨g', hg'S⟩ : NonDanglingEdge data) ⟨g, hgS⟩ :=
      ⟨fun h ↦ hg'Ne (congrArg Subtype.val h), B, hg'I, hgI, hValB⟩
    have hPath := stablePath_eq_of_consecutive hCons
    simpa only [hCanonEq] using hPath
  · rw [hCanonEq, hmG, hmG']
  · rw [hCanonEq]
    have hEndpoint' : data.sourceEndpoint B.1.1 g'.1.2 = B :=
      (data.sourceEndpoint_eq_iff B.1.1 g'.1.2 B).mpr
        ⟨rfl, ((incident_iff_target_mem_and_rel data g' B).mp hg'I).2.symm⟩
    have hBackInc : Incident data (data.sourceEdge s g'.1.2) B := by
      have h := incident_sourceEdge_sourceEndpoint data B.1.1 s hs g'.1.2
      rwa [hEndpoint'] at h
    exact hUnique hBackInc hgI (by rw [hgT]; rfl) hmG

/-! ## 7.  The trivalent branch, discharged -/

open DraismaVargas.Infrastructure.GluingDatum.LengthMatrixPresentation in
/-- **Part I's Figure 7 is impossible.**  At a trivalent target vertex adjacent
to a leaf, two distinct surviving-valency-two blocks each carrying a survivor
above the leaf edge make the two remaining columns of `A_φ` differ only in the
leaf row -- and the leaf column is `2 e_{h(v)}`, so a nonzero combination of
three columns vanishes. -/
theorem trivalentPassOnce (fd : FullDimensionalSourcePresentation data coordinate) :
    TrivalentPassOnce data := by
  classical
  intro leaf hLeaf X X' e e' hXX' hTargetXX' hTri hValX hValX' heS he'S
    hTargetE hTargetE' hIncE hIncE'
  -- the leaf edge is one of the three occurrences at `w = φ(X)`
  have ht₁ : leafEdge hLeaf ∈ GluingDatum.incidentEdges X.1.1 :=
    hTargetE ▸ ((incident_iff_target_mem_and_rel data e X).mp hIncE).1
  -- the leaf fibre is `{e, e'}`
  have hEeNe : e ≠ e' := by
    intro hEq
    exact hXX' (LollipopBridgeFibre.eq_of_incident_of_target_eq hTargetXX' hIncE
      (hEq ▸ hIncE'))
  have hSet : LeafFibre.leafSurvivors (data := data) hLeaf = {e, e'} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact (LeafFibre.mem_leafSurvivors hLeaf).mpr ⟨heS, hTargetE⟩
      · rw [Finset.mem_singleton] at hx
        subst hx
        exact (LeafFibre.mem_leafSurvivors hLeaf).mpr ⟨he'S, hTargetE'⟩
    · rw [LeafFibre.leafSurvivors_card fd hLeaf, Finset.card_pair hEeNe]
  -- every survivor at `X` or at `X'` lies on the leaf row
  obtain ⟨f, ⟨hfNe, hfS, hfI⟩, -⟩ :=
    exists_unique_other_of_nonDanglingValency_eq_two data hValX heS hIncE
  obtain ⟨f', ⟨hf'Ne, hf'S, hf'I⟩, -⟩ :=
    exists_unique_other_of_nonDanglingValency_eq_two data hValX' he'S hIncE'
  have hRowE : fd.labelling.row (NonDanglingEdge.stablePath
      (⟨e, heS⟩ : NonDanglingEdge data)) = LeafFibre.leafRow fd hLeaf :=
    LeafFibre.row_eq_leafRow fd hLeaf
      ((LeafFibre.mem_leafSurvivors hLeaf).mpr ⟨heS, hTargetE⟩) heS
  have hRowE' : fd.labelling.row (NonDanglingEdge.stablePath
      (⟨e', he'S⟩ : NonDanglingEdge data)) = LeafFibre.leafRow fd hLeaf :=
    LeafFibre.row_eq_leafRow fd hLeaf
      ((LeafFibre.mem_leafSurvivors hLeaf).mpr ⟨he'S, hTargetE'⟩) he'S
  have hRowF : fd.labelling.row (NonDanglingEdge.stablePath
      (⟨f, hfS⟩ : NonDanglingEdge data)) = LeafFibre.leafRow fd hLeaf := by
    rw [stablePath_eq_of_consecutive
      (⟨fun h ↦ hfNe (congrArg Subtype.val h), X, hfI, hIncE, hValX⟩ :
        Consecutive data ⟨f, hfS⟩ ⟨e, heS⟩)]
    exact hRowE
  have hRowF' : fd.labelling.row (NonDanglingEdge.stablePath
      (⟨f', hf'S⟩ : NonDanglingEdge data)) = LeafFibre.leafRow fd hLeaf := by
    rw [stablePath_eq_of_consecutive
      (⟨fun h ↦ hf'Ne (congrArg Subtype.val h), X', hf'I, hIncE', hValX'⟩ :
        Consecutive data ⟨f', hf'S⟩ ⟨e', he'S⟩)]
    exact hRowE'
  have hXrow : ∀ (x : data.SourceEdge) (hx : ¬ IsDangling data x), Incident data x X →
      fd.labelling.row (NonDanglingEdge.stablePath (⟨x, hx⟩ : NonDanglingEdge data)) =
        LeafFibre.leafRow fd hLeaf := by
    intro x hx hxI
    rcases IndexPattern.eq_or_eq_of_nonDanglingValency_two hValX heS hIncE hfS hfI
      (Ne.symm hfNe) hx hxI with rfl | rfl
    · exact hRowE
    · exact hRowF
  have hX'row : ∀ (x : data.SourceEdge) (hx : ¬ IsDangling data x), Incident data x X' →
      fd.labelling.row (NonDanglingEdge.stablePath (⟨x, hx⟩ : NonDanglingEdge data)) =
        LeafFibre.leafRow fd hLeaf := by
    intro x hx hxI
    rcases IndexPattern.eq_or_eq_of_nonDanglingValency_two hValX' he'S hIncE' hf'S hf'I
      (Ne.symm hf'Ne) hx hxI with rfl | rfl
    · exact hRowE'
    · exact hRowF'
  -- a survivor off the leaf row sits on a block with no survivor above the leaf edge
  have hIncidentBlock : ∀ (u : target.edges), u ∈ GluingDatum.incidentEdges X.1.1 →
      ∀ g : data.SourceEdge, (g.1.1 : target.edges) = u →
      Incident data g (data.sourceEndpoint X.1.1 g.1.2) := by
    intro u hu g hgT
    have h := incident_sourceEdge_sourceEndpoint data X.1.1 u hu g.1.2
    rwa [show data.sourceEdge u g.1.2 = g by rw [← hgT]; exact GluingDatum.sourceEdge_self data g]
      at h
  have hNoSurvAt : ∀ (u : target.edges), u ∈ GluingDatum.incidentEdges X.1.1 →
      ∀ (g : data.SourceEdge) (hgS : ¬ IsDangling data g), (g.1.1 : target.edges) = u →
      fd.labelling.row (NonDanglingEdge.stablePath (⟨g, hgS⟩ : NonDanglingEdge data)) ≠
        LeafFibre.leafRow fd hLeaf →
      ∀ x : data.SourceEdge, ¬ IsDangling data x →
        Incident data x (data.sourceEndpoint X.1.1 g.1.2) →
        (x.1.1 : target.edges) ≠ leafEdge hLeaf := by
    intro u hu g hgS hgT hgRow x hxS hxI hxT
    have hgIB : Incident data g (data.sourceEndpoint X.1.1 g.1.2) := hIncidentBlock u hu g hgT
    have hBT : ((data.sourceEndpoint X.1.1 g.1.2).1.1 : target.V) = X.1.1 := rfl
    have hxMem : x ∈ LeafFibre.leafSurvivors (data := data) hLeaf :=
      (LeafFibre.mem_leafSurvivors hLeaf).mpr ⟨hxS, hxT⟩
    rw [hSet] at hxMem
    rcases Finset.mem_insert.mp hxMem with rfl | hxMem
    · have hBX : data.sourceEndpoint X.1.1 g.1.2 = X :=
        LollipopBridgeFibre.eq_of_incident_of_target_eq hBT hxI hIncE
      exact hgRow (hXrow g hgS (hBX ▸ hgIB))
    · rw [Finset.mem_singleton] at hxMem
      subst hxMem
      have hBX' : data.sourceEndpoint X.1.1 g.1.2 = X' :=
        LollipopBridgeFibre.eq_of_incident_of_target_eq (hBT.trans hTargetXX') hxI hIncE'
      exact hgRow (hX'row g hgS (hBX' ▸ hgIB))
  -- the two occurrences at `w` other than the leaf edge
  obtain ⟨s, t, hst, hPair⟩ : ∃ s t : target.edges, s ≠ t ∧
      (GluingDatum.incidentEdges X.1.1).erase (leafEdge hLeaf) = {s, t} :=
    Finset.card_eq_two.mp (by rw [Finset.card_erase_of_mem ht₁, hTri])
  have hsErase : s ∈ (GluingDatum.incidentEdges X.1.1).erase (leafEdge hLeaf) := by
    rw [hPair]; simp
  have htErase : t ∈ (GluingDatum.incidentEdges X.1.1).erase (leafEdge hLeaf) := by
    rw [hPair]; simp
  have hs : s ∈ GluingDatum.incidentEdges X.1.1 := (Finset.mem_erase.mp hsErase).2
  have ht : t ∈ GluingDatum.incidentEdges X.1.1 := (Finset.mem_erase.mp htErase).2
  have hst₁ : s ≠ leafEdge hLeaf := (Finset.mem_erase.mp hsErase).1
  have htt₁ : t ≠ leafEdge hLeaf := (Finset.mem_erase.mp htErase).1
  -- the column identity off the leaf row
  have hColumn : ∀ (u v : target.edges), u ∈ GluingDatum.incidentEdges X.1.1 →
      v ∈ GluingDatum.incidentEdges X.1.1 → u ≠ leafEdge hLeaf → v ≠ leafEdge hLeaf →
      u ≠ v → ∀ sourceRow : coordinate, sourceRow ≠ LeafFibre.leafRow fd hLeaf →
      matrix fd.labelling.presentation sourceRow (fd.labelling.targetEdge.symm u) =
        matrix fd.labelling.presentation sourceRow (fd.labelling.targetEdge.symm v) := by
    intro u v hu hv hu₁ hv₁ huv sourceRow hRow
    rw [LeafFibre.matrix_eq_sum_fibre, LeafFibre.matrix_eq_sum_fibre]
    refine Finset.sum_nbij' (fun g ↦ data.sourceEdge v g.1.2) (fun g ↦ data.sourceEdge u g.1.2)
      ?_ ?_ ?_ ?_ ?_
    · intro g hg
      obtain ⟨⟨hgS, hgRow⟩, hgT⟩ := (LeafFibre.mem_rowFibre _ _ _ _).mp hg
      obtain ⟨hS, hPath, -, -⟩ := partner_of_block fd (B := data.sourceEndpoint X.1.1 g.1.2)
        hTri ht₁ hu hv hu₁ hv₁ huv
        (hNoSurvAt u hu g hgS hgT (by rw [hgRow]; exact hRow))
        hgS (hIncidentBlock u hu g hgT) hgT
      exact (LeafFibre.mem_rowFibre _ _ _ _).mpr ⟨⟨hS, by rw [hPath]; exact hgRow⟩, rfl⟩
    · intro g hg
      obtain ⟨⟨hgS, hgRow⟩, hgT⟩ := (LeafFibre.mem_rowFibre _ _ _ _).mp hg
      obtain ⟨hS, hPath, -, -⟩ := partner_of_block fd (B := data.sourceEndpoint X.1.1 g.1.2)
        hTri ht₁ hv hu hv₁ hu₁ (Ne.symm huv)
        (hNoSurvAt v hv g hgS hgT (by rw [hgRow]; exact hRow))
        hgS (hIncidentBlock v hv g hgT) hgT
      exact (LeafFibre.mem_rowFibre _ _ _ _).mpr ⟨⟨hS, by rw [hPath]; exact hgRow⟩, rfl⟩
    · intro g hg
      obtain ⟨⟨hgS, hgRow⟩, hgT⟩ := (LeafFibre.mem_rowFibre _ _ _ _).mp hg
      obtain ⟨-, -, -, hBack⟩ := partner_of_block fd (B := data.sourceEndpoint X.1.1 g.1.2)
        hTri ht₁ hu hv hu₁ hv₁ huv
        (hNoSurvAt u hu g hgS hgT (by rw [hgRow]; exact hRow))
        hgS (hIncidentBlock u hu g hgT) hgT
      exact hBack
    · intro g hg
      obtain ⟨⟨hgS, hgRow⟩, hgT⟩ := (LeafFibre.mem_rowFibre _ _ _ _).mp hg
      obtain ⟨-, -, -, hBack⟩ := partner_of_block fd (B := data.sourceEndpoint X.1.1 g.1.2)
        hTri ht₁ hv hu hv₁ hu₁ (Ne.symm huv)
        (hNoSurvAt v hv g hgS hgT (by rw [hgRow]; exact hRow))
        hgS (hIncidentBlock v hv g hgT) hgT
      exact hBack
    · intro g hg
      obtain ⟨⟨hgS, hgRow⟩, hgT⟩ := (LeafFibre.mem_rowFibre _ _ _ _).mp hg
      obtain ⟨-, -, hIndex, -⟩ := partner_of_block fd (B := data.sourceEndpoint X.1.1 g.1.2)
        hTri ht₁ hu hv hu₁ hv₁ huv
        (hNoSurvAt u hu g hgS hgT (by rw [hgRow]; exact hRow))
        hgS (hIncidentBlock u hu g hgT) hgT
      rw [hIndex]
  -- the determinant dies
  refine fd.det_ne_zero (IndexPattern.det_eq_zero_of_column_relation_and_leaf
    (matrix fd.labelling.presentation)
    (sourceRow := LeafFibre.leafRow fd hLeaf)
    (coefficient := matrix fd.labelling.presentation (LeafFibre.leafRow fd hLeaf)
        (fd.labelling.targetEdge.symm s) -
      matrix fd.labelling.presentation (LeafFibre.leafRow fd hLeaf)
        (fd.labelling.targetEdge.symm t))
    (leafColumn := fd.labelling.targetEdge.symm (leafEdge hLeaf))
    (fun hEq ↦ hst (fd.labelling.targetEdge.symm.injective hEq)) ?_
    (fun row ↦ LeafFibre.matrix_leafEdge_column fd hLeaf row))
  intro row
  by_cases hCase : row = LeafFibre.leafRow fd hLeaf
  · rw [ite_eq_left hCase, hCase]
  · rw [ite_eq_right hCase, hColumn s t hs ht hst₁ htt₁ hst row hCase, sub_self]

/-! ## 8.  Pass-once at the lollipop, unconditionally -/

open DraismaVargas.LocalCases.StablePathCount in
/-- **Pass-once at the lollipop.**  For a stable row with both ends at one
branch vertex `A`, the image `φ(A)` is adjacent to the leaf the row passes
above.

This is the statement that `Count/LollipopBridgeFibre.lean` and
`Count/RowSingleColumnWitness.lean` both reduce the caterpillar structure lemma to; through
`LollipopBridgeFibre.leafAdjacent_iff_exists_end_above_leafEdge` it is also the
length-two clause `h_l = ⟨A, e₁, C, e₂, A⟩` of Part II's `lm:bridge-and-loop`.
It is Part I's `lemma-pass-once` at the lollipop, and it carries **no hypothesis** beyond
full-dimensionality, a branch vertex of surviving valency other than two
carrying both ends of the row, and the identification of the row as the leaf
row of `leaf`. -/
theorem leafAdjacent_of_loopRow
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : nonDanglingValency data branch ≠ 2)
    (hTwo : incidenceCount data branch path = 2)
    {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    (hLeafRow : LeafFibre.leafRow fd hLeaf = fd.labelling.row path) :
    leafEdge hLeaf ∈ GluingDatum.incidentEdges branch.1.1 :=
  leafAdjacent_of_loopRow_of_trivalentPassOnce fd (trivalentPassOnce fd) hBranch hTwo
    hLeaf hLeafRow

open DraismaVargas.LocalCases.StablePathCount in
/-- **The length-two clause of `lm:bridge-and-loop`**, in the "every end of the
loop row lies above the leaf edge" form. -/
theorem onRow_target_eq_leafEdge_of_loopRow
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : 3 ≤ nonDanglingValency data branch)
    (hTwo : incidenceCount data branch path = 2)
    {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    (hLeafRow : LeafFibre.leafRow fd hLeaf = fd.labelling.row path)
    {edge : data.SourceEdge} (hRow : OnRow data path edge)
    (hInc : Incident data edge branch) :
    (edge.1.1 : target.edges) = leafEdge hLeaf :=
  LollipopBridgeFibre.onRow_target_eq_leafEdge fd hBranch hTwo hLeaf
    (leafAdjacent_of_loopRow fd (by omega) hTwo hLeaf hLeafRow) hRow hInc

open DraismaVargas.LocalCases.StablePathCount in
/-- **The same statement in the form the spine side reaches**
(`Count/RowSingleColumnWitness.lean`, `eq_two_iff_exists_end_above_leafEdge`):
some end of the loop row lies above the leaf edge. -/
theorem exists_end_above_leafEdge_of_loopRow
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : 3 ≤ nonDanglingValency data branch)
    (hTwo : incidenceCount data branch path = 2)
    {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    (hLeafRow : LeafFibre.leafRow fd hLeaf = fd.labelling.row path) :
    ∃ edge : data.SourceEdge, OnRow data path edge ∧ Incident data edge branch ∧
      (edge.1.1 : target.edges) = leafEdge hLeaf :=
  (LollipopBridgeFibre.leafAdjacent_iff_exists_end_above_leafEdge fd hBranch hTwo hLeaf).mp
    (leafAdjacent_of_loopRow fd (by omega) hTwo hLeaf hLeafRow)

end DraismaVargas.Count.PassOnceLollipop
