import DraismaVargasCount.RowSingleColumnProof
import DraismaVargasCount.LollipopDivalentWitness

/-!
# The lollipop half of the single-column property, localised at the branch vertex

**Source.**  Draisma--Vargas Part I (arXiv:1909.12924), `lemma-loop-bridge`
(`h_l = ⟨A, e₁, C, e₂, A⟩`), cited by Vargas, Part II (arXiv:2609.09109) as
`lm:bridge-and-loop`.  This is the single-column property
`SpineOffDiagonal.RowSingleColumn` on the loop rows.

`RowSingleColumnProof` shows that `SpineOffDiagonal.RowSingleColumn`
on a row passing above a leaf is exactly "the row displays two occurrences".
This module reduces *that* to a statement about a single vertex.

## The reduction

Let `h_l` be a stable row with both ends at one branch vertex `A`.  Known
facts: it is the leaf row `h(v)` of a leaf `v`
(`LollipopLeafRow.exists_leafRow_eq_of_loopRow`); the leaf core vertex `A_v` is
an interior walk vertex of it (`LollipopDivalentWitness.exists_split`), so the
**two** surviving occurrences above the leaf edge
(`LeafFibre.leafSurvivors_card`) are the two entries of the ordered row on
either side of `A_v`; and the two ends of `h_l` at `A` lie above **one** target
occurrence (`LollipopDivalentWitness.loopReturnsSameDirection`, the hairpin).

The hairpin does **not** say which target occurrence that is.  If it is the leaf
edge, then an end of the row is one of the two leaf survivors, so the split
index is `0`, so the row is exactly `⟨A, e₁, A_v, e₂, A⟩` and `RowSingleColumn`
holds.  If it is not, then the row's first, `k`-th and `(k+1)`-st occurrences
are three distinct surviving occurrences above the leaf edge, of which there are
only two.  Hence:

> **`RowSingleColumn` on a loop row ⟺ an end of that row lies above the leaf edge**
> ⟺ `φ(A)` is the neighbour of the leaf `v`.

That is `eq_two_iff_exists_end_above_leafEdge` below, and it is the whole of
the lollipop half of the single-column property.

## What is proved

* `three_le_card_of_mem_of_ne` --- a counting triviality, stated once.
* `card_rowEdges_eq_two_of_end_above_leafEdge` --- the substantive direction:
  one end above the leaf edge collapses the loop row to length two.
* `exists_end_above_leafEdge_of_card_rowEdges_eq_two` --- the converse.
* `eq_two_iff_exists_end_above_leafEdge`,
  `exists_rowSingleColumn_loopRow_iff` --- the reduction, and the same with
  `RowSingleColumn` in front.
* `exists_rowSingleColumn_loopRow_iff_adjacent` --- the same residue as a
  source adjacency: `A` and `A_v` are joined by a surviving occurrence.
* `exists_rowSingleColumn_core_loop_iff` --- the member-level form at a
  self-loop slot of an arbitrary core.

## What is NOT proved (every hypothesis, explicitly)

The first bullet below is about this file only: "an end of the loop row lies
above the leaf edge" is proved unconditionally as
`PassOnceLollipop.exists_end_above_leafEdge_of_loopRow`, and
`PassOnceLollipopWitness` uses it to prove `RowSingleColumn` on the loop rows
(`exists_rowSingleColumn_loopRow`, `exists_rowSingleColumn_core_loop`); both of
those modules import this one.

* **"An end of the loop row lies above the leaf edge" is not proved here**, for
  no row and in no generality.  It is Part I's use of the **pass-once** condition
  (`lemma-pass-once`).  The leaf-avoiding form of pass-once,
  `SharpRowDenominator.rowTargetInjective_of_not_passesAboveLeaf`, is
  inapplicable on a row that passes above a leaf.  Part I's proof of
  pass-once is a column-dependence argument (`a₂ = a₁ + a₃` against full rank)
  using case (r0-nd2) of `prop-local` and `lemma-change-zero`; it is not
  formalised here.
* Nothing here is about the spine rows, and nothing here is an exhaustion of
  the fibre: `GeometricFibre`, `openOddCount`, `BallotFamily`, `Open` and
  `HasOddMult` do not occur below.
* The member-level statement is about a **self-loop slot of an arbitrary core**;
  nothing below mentions `catCore`, the genus, the degree or the request.
-/

namespace DraismaVargas.Count.RowSingleColumnWitness

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.OrientedTraversal
open DraismaVargas.Count.LeafFibre
open DraismaVargas.Count.EdgeDenominator
open DraismaVargas.Count.RowWalk
open DraismaVargas.Count.SpineOffDiagonal
open DraismaVargas.Count.RowSingleColumnProof
open Utilities.Certificate.ExplicitPotential (Core)

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-! ## 0.  Three distinct members need three slots -/

theorem three_le_card_of_mem_of_ne {α : Type*} [DecidableEq α] {S : Finset α} {a b c : α}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    3 ≤ S.card := by
  have hsub : ({a, b, c} : Finset α) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hcard : ({a, b, c} : Finset α).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  exact hcard ▸ Finset.card_le_card hsub

/-! ## 1.  One end above the leaf edge collapses the loop row -/

open DraismaVargas.LocalCases.StablePathCount in
/-- **The substantive direction.**  If some occurrence of a loop row incident to
its branch vertex lies above the leaf edge, the row displays exactly two
occurrences --- Part I's `h_l = ⟨A, e₁, C, e₂, A⟩`.

The argument is a pigeonhole on `LeafFibre.leafSurvivors`, which has two
elements: the first occurrence of the ordered row and the two occurrences on
either side of the leaf core vertex all lie above the leaf edge, so the split
index must be `0`; then the last occurrence lies there too, by the hairpin, so
the row has length two. -/
theorem card_rowEdges_eq_two_of_end_above_leafEdge
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : nonDanglingValency data branch ≠ 2)
    (hTwo : incidenceCount data branch path = 2)
    {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    (hLeafRow : LeafFibre.leafRow fd hLeaf = fd.labelling.row path)
    {edge : data.SourceEdge} (hOnRow : OnRow data path edge)
    (hIncident : Incident data edge branch) (hTarget : edge.1.1 = leafEdge hLeaf) :
    (rowEdges fd.labelling (fd.labelling.row path)).card = 2 := by
  classical
  have hNodup : (orderedRow fd.pathEnds path).Nodup := orderedRow_nodup fd.pathEnds path
  have hSurvives : ∀ e ∈ orderedRow fd.pathEnds path, ¬ IsDangling data e := fun e he ↦
    ((mem_orderedRow_iff fd.pathEnds path e).mp he).survives
  have hStart : startVertex fd.pathEnds path = branch :=
    LollipopLeafRow.startVertex_eq_of_incidenceCount_eq_two
      (NonDanglingValency.nonDanglingValency_ne_one data fd.connected) fd.pathEnds hBranch hTwo
  obtain ⟨last, hlast, hlastPos, hlastLen, _, hlastIncident⟩ :=
    LollipopDivalentWitness.loopRow_ends fd hBranch hTwo
  obtain ⟨k, hk, hCore⟩ :=
    LollipopDivalentWitness.exists_split fd hBranch hTwo hLeaf hLeafRow
  have hLen0 : 0 < (orderedRow fd.pathEnds path).length := by omega
  -- the two occurrences flanking the leaf core vertex
  have hmemK : (orderedRow fd.pathEnds path)[k]'(by omega) ∈ leafSurvivors (data := data) hLeaf :=
    mem_leafSurvivors_of_incident_coreVertex fd hLeaf (hSurvives _ (List.getElem_mem (by omega)))
      (by rw [← hCore]; exact walkVertex_succ_incident (by omega))
  have hmemK1 : (orderedRow fd.pathEnds path)[k + 1]'hk ∈ leafSurvivors (data := data) hLeaf :=
    mem_leafSurvivors_of_incident_coreVertex fd hLeaf (hSurvives _ (List.getElem_mem hk))
      (by rw [← hCore]; exact RowPosition.rowVertex_incident fd path hk)
  -- the first occurrence, above the leaf edge by the hairpin
  have hZeroOnRow : OnRow data path ((orderedRow fd.pathEnds path)[0]'hLen0) :=
    (mem_orderedRow_iff fd.pathEnds path _).mp (List.getElem_mem hLen0)
  have hZeroIncident : Incident data ((orderedRow fd.pathEnds path)[0]'hLen0) branch :=
    hStart ▸ (RowPosition.orderedRow_start fd path hLen0).1
  have hZeroTarget : (((orderedRow fd.pathEnds path)[0]'hLen0).1.1 : target.edges)
      = leafEdge hLeaf := by
    rw [LollipopDivalentWitness.loopReturnsSameDirection fd hBranch hTwo _ edge
      hZeroOnRow hZeroIncident hOnRow hIncident]
    exact hTarget
  have hmem0 : (orderedRow fd.pathEnds path)[0]'hLen0 ∈ leafSurvivors (data := data) hLeaf :=
    (mem_leafSurvivors hLeaf).mpr ⟨hSurvives _ (List.getElem_mem hLen0), hZeroTarget⟩
  -- the last occurrence, likewise
  have hLastOnRow : OnRow data path ((orderedRow fd.pathEnds path)[last]'hlast) :=
    (mem_orderedRow_iff fd.pathEnds path _).mp (List.getElem_mem hlast)
  have hLastTarget : (((orderedRow fd.pathEnds path)[last]'hlast).1.1 : target.edges)
      = leafEdge hLeaf := by
    rw [LollipopDivalentWitness.loopReturnsSameDirection fd hBranch hTwo _ edge
      hLastOnRow hlastIncident hOnRow hIncident]
    exact hTarget
  have hmemLast : (orderedRow fd.pathEnds path)[last]'hlast ∈ leafSurvivors (data := data) hLeaf :=
    (mem_leafSurvivors hLeaf).mpr ⟨hSurvives _ (List.getElem_mem hlast), hLastTarget⟩
  have hCard : (leafSurvivors (data := data) hLeaf).card = 2 :=
    leafSurvivors_card (data := data) fd hLeaf
  have hInj : ∀ (i j : ℕ) (hi : i < (orderedRow fd.pathEnds path).length)
      (hj : j < (orderedRow fd.pathEnds path).length),
      (orderedRow fd.pathEnds path)[i]'hi = (orderedRow fd.pathEnds path)[j]'hj → i = j := by
    intro i j hi hj hEq
    exact (List.Nodup.getElem_inj_iff hNodup).mp hEq
  -- the split index is `0`
  have hk0 : k = 0 := by
    by_contra hne
    have hthree := three_le_card_of_mem_of_ne hmem0 hmemK hmemK1
      (fun hEq ↦ hne (hInj 0 k hLen0 (by omega) hEq).symm)
      (fun hEq ↦ by simpa using (hInj 0 (k + 1) hLen0 hk hEq))
      (fun hEq ↦ by simpa using (hInj k (k + 1) (by omega) hk hEq))
    omega
  have hmem1 : (orderedRow fd.pathEnds path)[1]'(by omega) ∈ leafSurvivors (data := data) hLeaf := by
    subst hk0
    exact hmemK1
  have hOne : (1 : ℕ) < (orderedRow fd.pathEnds path).length := by omega
  -- hence the last index is `1`
  have hlast1 : last = 1 := by
    by_contra hne
    have hthree := three_le_card_of_mem_of_ne hmem0 hmem1 hmemLast
      (fun hEq ↦ by simpa using (hInj 0 1 hLen0 hOne hEq))
      (fun hEq ↦ by have := hInj 0 last hLen0 hlast hEq; omega)
      (fun hEq ↦ hne (hInj 1 last hOne hlast hEq).symm)
    omega
  rw [card_rowEdges_eq_length_orderedRow fd path]
  omega

/-! ## 2.  The converse, and the reduction -/

open DraismaVargas.LocalCases.StablePathCount in
/-- **The converse.**  A loop row of length two has both of its occurrences
above the leaf edge, so in particular an end of it does. -/
theorem exists_end_above_leafEdge_of_card_rowEdges_eq_two
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : nonDanglingValency data branch ≠ 2)
    (hTwo : incidenceCount data branch path = 2)
    {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    (hLeafRow : LeafFibre.leafRow fd hLeaf = fd.labelling.row path)
    (hCard : (rowEdges fd.labelling (fd.labelling.row path)).card = 2) :
    ∃ edge : data.SourceEdge, OnRow data path edge ∧ Incident data edge branch ∧
      edge.1.1 = leafEdge hLeaf := by
  have hLen0 : 0 < (orderedRow fd.pathEnds path).length := by
    rw [← card_rowEdges_eq_length_orderedRow fd path]
    omega
  have hStart : startVertex fd.pathEnds path = branch :=
    LollipopLeafRow.startVertex_eq_of_incidenceCount_eq_two
      (NonDanglingValency.nonDanglingValency_ne_one data fd.connected) fd.pathEnds hBranch hTwo
  have hSingle : RowSingleColumn fd.labelling (LeafFibre.leafRow fd hLeaf)
      (fd.labelling.targetEdge.symm (leafEdge hLeaf)) := by
    refine (rowSingleColumn_leafRow_iff fd hLeaf).mpr ?_
    rw [hLeafRow]
    exact hCard
  refine ⟨(orderedRow fd.pathEnds path)[0]'hLen0,
    (mem_orderedRow_iff fd.pathEnds path _).mp (List.getElem_mem hLen0),
    hStart ▸ (RowPosition.orderedRow_start fd path hLen0).1, ?_⟩
  have hMem : (orderedRow fd.pathEnds path)[0]'hLen0
      ∈ rowEdges fd.labelling (LeafFibre.leafRow fd hLeaf) := by
    rw [hLeafRow, mem_rowEdges_iff_onRow, Equiv.symm_apply_apply]
    exact (mem_orderedRow_iff fd.pathEnds path _).mp (List.getElem_mem hLen0)
  rw [hSingle _ hMem, Equiv.apply_symm_apply]

open DraismaVargas.LocalCases.StablePathCount in
/-- **The lollipop half of the single-column property, localised.**  A loop row displays exactly two
occurrences exactly when one of its two ends lies above the leaf edge of the
leaf it passes above --- equivalently, when the branch vertex is a neighbour of
the leaf core vertex `A_v`. -/
theorem eq_two_iff_exists_end_above_leafEdge
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : nonDanglingValency data branch ≠ 2)
    (hTwo : incidenceCount data branch path = 2)
    {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    (hLeafRow : LeafFibre.leafRow fd hLeaf = fd.labelling.row path) :
    (rowEdges fd.labelling (fd.labelling.row path)).card = 2 ↔
      ∃ edge : data.SourceEdge, OnRow data path edge ∧ Incident data edge branch ∧
        edge.1.1 = leafEdge hLeaf := by
  refine ⟨exists_end_above_leafEdge_of_card_rowEdges_eq_two fd hBranch hTwo hLeaf hLeafRow, ?_⟩
  rintro ⟨edge, hOnRow, hIncident, hTarget⟩
  exact card_rowEdges_eq_two_of_end_above_leafEdge fd hBranch hTwo hLeaf hLeafRow
    hOnRow hIncident hTarget

open DraismaVargas.LocalCases.StablePathCount in
/-- **`RowSingleColumn` on a loop row is exactly that.** -/
theorem exists_rowSingleColumn_loopRow_iff
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : nonDanglingValency data branch ≠ 2)
    (hTwo : incidenceCount data branch path = 2)
    {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    (hLeafRow : LeafFibre.leafRow fd hLeaf = fd.labelling.row path) :
    (∃ column, RowSingleColumn fd.labelling (fd.labelling.row path) column) ↔
      ∃ edge : data.SourceEdge, OnRow data path edge ∧ Incident data edge branch ∧
        edge.1.1 = leafEdge hLeaf := by
  rw [← eq_two_iff_exists_end_above_leafEdge fd hBranch hTwo hLeaf hLeafRow]
  constructor
  · rintro ⟨column, hSingle⟩
    rw [← hLeafRow] at hSingle ⊢
    rw [← rowSingleColumn_leafRow_iff fd hLeaf,
      ← targetEdge_eq_leafEdge_of_rowSingleColumn_leafRow fd hLeaf hSingle]
    exact hSingle
  · intro hCard
    rw [← hLeafRow] at hCard ⊢
    exact ⟨_, (rowSingleColumn_leafRow_iff fd hLeaf).mpr hCard⟩

open DraismaVargas.LocalCases.StablePathCount in
/-- **The same, as an adjacency in the source.**  `RowSingleColumn` on a loop row
says exactly that the branch vertex `A` and the leaf core vertex `A_v` are
joined by a surviving occurrence --- i.e. that `φ(A)` is the neighbour of the
leaf. -/
theorem exists_rowSingleColumn_loopRow_iff_adjacent
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : nonDanglingValency data branch ≠ 2)
    (hTwo : incidenceCount data branch path = 2)
    {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    (hLeafRow : LeafFibre.leafRow fd hLeaf = fd.labelling.row path) :
    (∃ column, RowSingleColumn fd.labelling (fd.labelling.row path) column) ↔
      ∃ edge : data.SourceEdge, ¬ IsDangling data edge ∧ Incident data edge branch ∧
        Incident data edge (LeafFibre.coreVertex fd hLeaf) := by
  rw [exists_rowSingleColumn_loopRow_iff fd hBranch hTwo hLeaf hLeafRow]
  constructor
  · rintro ⟨edge, hOnRow, hIncident, hTarget⟩
    refine ⟨edge, hOnRow.survives, hIncident, ?_⟩
    exact incident_coreVertex_of_mem_leafSurvivors fd hLeaf
      ((mem_leafSurvivors hLeaf).mpr ⟨hOnRow.survives, hTarget⟩)
  · rintro ⟨edge, hSurvives, hIncident, hCore⟩
    have hMem : edge ∈ leafSurvivors (data := data) hLeaf :=
      mem_leafSurvivors_of_incident_coreVertex fd hLeaf hSurvives hCore
    refine ⟨edge, ⟨hSurvives, ?_⟩, hIncident, ((mem_leafSurvivors hLeaf).mp hMem).2⟩
    refine fd.labelling.row.injective ?_
    rw [row_eq_leafRow fd hLeaf hMem hSurvives, hLeafRow]

/-! ## 3.  At a self-loop slot of an arbitrary core -/

section Member

variable {n p : ℕ} {core : Core n p} {y : Fin p → ℚ} {degree : ℕ}
  (member : FibreMember core y degree)

/-- **The member-level form.**  For a self-loop slot of an arbitrary core,
`RowSingleColumn` on that row is "one of the two occurrences at the branch vertex lies
above the leaf edge".  Nothing about the caterpillar, the genus, the degree, the
request, openness or oddness enters. -/
theorem exists_rowSingleColumn_core_loop_iff {slot : Fin p}
    (hLoop : core.tail slot = core.head slot) :
    (∃ column, RowSingleColumn member.fullDim.labelling
        (member.fullDim.labelling.row (member.ident.row.symm slot)) column) ↔
      ∃ edge : member.data.SourceEdge,
        OnRow member.data (member.ident.row.symm slot) edge ∧
          Incident member.data edge (member.ident.vertex.symm (core.tail slot)).1 ∧
          edge.1.1 = leafEdge (LollipopLeafRow.loopLeaf_isLeafVertex member hLoop) := by
  refine exists_rowSingleColumn_loopRow_iff member.fullDim (branch :=
    (member.ident.vertex.symm (core.tail slot)).1) ?_
    (LollipopLeafRow.incidenceCount_eq_two_of_core_loop member hLoop)
    (LollipopLeafRow.loopLeaf_isLeafVertex member hLoop)
    (LollipopLeafRow.leafRow_loopLeaf member hLoop)
  have hThree := (member.ident.vertex.symm (core.tail slot)).2
  omega

end Member

end DraismaVargas.Count.RowSingleColumnWitness
