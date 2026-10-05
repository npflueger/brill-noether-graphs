module

public import DraismaVargasCount.LollipopDivalent

@[expose] public section

/-!
# The fibres above a lollipop's two target occurrences

**Source.**  Vargas, Part II (arXiv:2609.09109), `lm:bridge-and-loop`, whose last sentence
says that `e_b, A, e_1, e_2, C` are the only non-dangling elements in the fibres of
`φ(e_b)`, `φ(A)`, `φ(e_1)` and `φ(C)` (the *fibre clause*).  Part II cites
Draisma--Vargas Part I (arXiv:1909.12924), `lemma-loop-bridge`, which in turn reduces the
fibre clause to `lemma-loop-12` and `lemma-pass-once`.

Above `t_v` and above `φ(C)` the clause is in `Count/LeafFibre.lean`
(`leafSurvivors_card = 2`, `isDangling_of_other_block`).  This file is the other two
fibres.

## What is proved

### Unconditional

* `exists_survivor_above_leafEdge` -- **the engine.**  Above a **divalent**
  target vertex `u` one of whose two incident occurrences is the leaf edge
  `t_v` of a leaf `v`, every block with a surviving occurrence has a surviving
  occurrence **above `t_v`**.  This is the no-return step inside Part I's
  `lemma-loop-12`, derived here from the change budget
  (`IndexPattern.localRamification_le_targetChange`), the incidence-count
  formula and the balancing identity -- no case of `prop-local`, and no
  no-return hypothesis.
* `eq_of_incident_of_target_eq` -- two source vertices above one target vertex
  sharing an incident occurrence coincide.
* `eq_of_nonDangling`, `nonDanglingValency_eq_zero_of_ne` -- consequently, if
  every surviving occurrence above `t_v` meets one block `A`, then `A` is the
  **only** non-dangling block above `u`.
* `incident_of_survivor_above_leafEdge` -- two distinct survivors above `t_v`
  already exhaust the leaf fibre (`LeafFibre.leafSurvivors_card`), so they
  supply that hypothesis.
* `eq_of_surviving_above_bridge` -- and then the occurrence of `A` whose index
  is the whole local degree is the **only** surviving occurrence above its own
  target occurrence.
* `not_isDangling_of_incident_branch` -- every occurrence incident to a
  lollipop branch vertex survives (`card_incidentSourceEdge_eq_three` with
  `nd = 3`).
* `onRow_target_eq_leafEdge` -- **what remains is target-side.**  As soon as
  `φ(A)` is incident to `t_v`, both ends of the loop row lie above `t_v`, i.e.
  `h_l = ⟨A, e_1, C, e_2, A⟩`.  The converse is immediate, so the missing
  clause is exactly the sentence *"`φ(A)` is adjacent to the leaf its loop row
  passes above"*.
* `leafAdjacent_iff_exists_end_above_leafEdge` -- that sentence in the three
  interchangeable forms "`φ(A)` incident to `t_v`" / "some row end above `t_v`"
  / "every row end above `t_v`".  The middle one is the form reached from the spine
  side (`Count/RowSingleColumnWitness.lean`, `eq_two_iff_exists_end_above_leafEdge`),
  so the lollipop and the spine arguments need one and the same statement.

### Conditional on that sentence

* `nonDanglingValency_eq_zero_of_ne_loopBranch`,
  `nonDanglingValency_eq_zero_of_ne_of_leafAdjacent` -- **the fibre clause above
  `φ(A)`**: every source vertex above `φ(A)` other than `A` is completely dangling.
* `eq_bridge_of_surviving`, `eq_bridge_of_surviving_of_leafAdjacent` --
  **the fibre clause above `φ(e_b)`**: `e_b` is the only surviving occurrence there.

## What is not proved here

* **The length-two clause of `lm:bridge-and-loop` is not proved here**, in
  either of its equivalent forms: `hAdj : leafEdge hLeaf ∈ incidentEdges branch.1.1`
  ("`φ(A)` is adjacent to the leaf") and `hEnds` ("both row ends lie above the
  leaf edge").  It is proved in `Count/PassOnceLollipop.lean` (`leafAdjacent_of_loopRow`,
  exactly `hAdj`, unconditionally), and `Count/PassOnceLollipopWitness.lean` carries it to
  a member; this file, upstream of those, states its conclusions with `hAdj` as a
  hypothesis.  Part I gets the clause from **pass-once** (`lemma-pass-once`);
  `Count/RowWalk.lean` and `Count/SharpRowDenominator.lean` prove pass-once only for
  **leaf-avoiding** rows (`rowFibre_eq_singleton_of_not_passesAboveLeaf`), and a loop row
  always passes above a leaf (`LollipopLeafRow.not_rowAvoidsLeaves_of_loopRow`).
  Part II states the clause as part of `lm:bridge-and-loop` itself
  (`h_l = ⟨A, e_1, C, e_2, A⟩`); it is a separate statement from the fibre clause.
  Part I's own proof of pass-once is a column-dependence argument
  (`a_2 = a_1 + a_3` against full rank) through case (r0-nd2) of `prop-local`
  and `lemma-change-zero`, and neither ingredient is formalized here.
* **The two fibres are not independent.**  The fibre above `t_b` is a corollary of the
  fibre above `φ(A)` (`eq_of_surviving_above_bridge` calls `eq_of_nonDangling`).
* Nothing here is an exhaustion of the fibre: no statement mentions
  `GeometricFibre`, `openOddCount`, `BallotFamily` or `BallotClassification`.
* Nothing about the spine, the slope sequence or the diagonality of `A_φ`.
* No genericity, `Open`, `HasOddMult` or request hypothesis is used anywhere.
-/
namespace DraismaVargas.Count.LollipopBridgeFibre

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.RowWalk
open Utilities.Certificate.ExplicitPotential (Core)

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-! ## 1.  A surviving block above a leaf-adjacent divalent vertex meets the leaf edge -/

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- The surviving valency counts the surviving incident occurrences. -/
theorem card_survivors_eq_nonDanglingValency (vertex : data.SourceVertex) :
    ((Finset.univ : Finset data.SourceEdge).filter
        fun item ↦ ¬ IsDangling data item ∧ Incident data item vertex).card
      = nonDanglingValency data vertex := by
  classical
  rw [nonDanglingValency]
  congr 1
  ext item
  simp

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- One surviving incident occurrence makes the surviving valency positive. -/
theorem nonDanglingValency_pos_of_survivor {vertex : data.SourceVertex}
    {edge : data.SourceEdge} (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge vertex) :
    0 < nonDanglingValency data vertex := by
  classical
  rw [← card_survivors_eq_nonDanglingValency]
  exact Finset.card_pos.mpr ⟨edge, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    hSurvives, hIncident⟩⟩

/-- **Every surviving block above a divalent target vertex incident to a leaf
edge carries a surviving occurrence above that leaf edge.**

This is Part I's no-return step inside `lemma-loop-12`, derived here from
the change budget and the balancing identity rather than from `prop-local`. -/
theorem exists_survivor_above_leafEdge
    (fd : FullDimensionalSourcePresentation data coordinate)
    {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    {vertex : data.SourceVertex}
    (hDivalent : (GluingDatum.incidentEdges vertex.1.1).card = 2)
    (hLeafMem : leafEdge hLeaf ∈ GluingDatum.incidentEdges vertex.1.1)
    (hSurvives : 0 < nonDanglingValency data vertex) :
    ∃ edge : data.SourceEdge, ¬ IsDangling data edge ∧
      edge.1.1 = leafEdge hLeaf ∧ Incident data edge vertex := by
  classical
  by_contra hNo
  push Not at hNo
  -- two distinct surviving incident occurrences
  have hTwoLe : 2 ≤ nonDanglingValency data vertex := by
    rcases fd.nonDanglingValency_trichotomy vertex with h | h | h <;> omega
  have hFilter := card_survivors_eq_nonDanglingValency (data := data) vertex
  have hOneLt : 1 < ((Finset.univ : Finset data.SourceEdge).filter
      fun item ↦ ¬ IsDangling data item ∧ Incident data item vertex).card := by omega
  obtain ⟨f₁, hf₁, f₂, hf₂, hNe⟩ := Finset.one_lt_card.mp hOneLt
  obtain ⟨hf₁Surv, hf₁Inc⟩ := (Finset.mem_filter.mp hf₁).2
  obtain ⟨hf₂Surv, hf₂Inc⟩ := (Finset.mem_filter.mp hf₂).2
  have hf₁Mem : f₁.1.1 ∈ GluingDatum.incidentEdges vertex.1.1 :=
    ((incident_iff_target_mem_and_rel data f₁ vertex).mp hf₁Inc).1
  have hf₂Mem : f₂.1.1 ∈ GluingDatum.incidentEdges vertex.1.1 :=
    ((incident_iff_target_mem_and_rel data f₂ vertex).mp hf₂Inc).1
  have hRel₁ : (data.vertexPartition vertex.1.1).Rel vertex.1.2 f₁.1.2 :=
    ((incident_iff_target_mem_and_rel data f₁ vertex).mp hf₁Inc).2
  have hRel₂ : (data.vertexPartition vertex.1.1).Rel vertex.1.2 f₂.1.2 :=
    ((incident_iff_target_mem_and_rel data f₂ vertex).mp hf₂Inc).2
  have hf₁NeLeaf : f₁.1.1 ≠ leafEdge hLeaf := fun h ↦ hNo f₁ hf₁Surv h hf₁Inc
  have hf₂NeLeaf : f₂.1.1 ≠ leafEdge hLeaf := fun h ↦ hNo f₂ hf₂Surv h hf₂Inc
  -- both lie above the *other* incident target occurrence
  obtain ⟨other, hOtherSingle⟩ : ∃ other,
      (GluingDatum.incidentEdges vertex.1.1).erase (leafEdge hLeaf) = {other} :=
    Finset.card_eq_one.mp (by rw [Finset.card_erase_of_mem hLeafMem, hDivalent])
  have hMemErase : ∀ edge : target.edges, edge ∈ GluingDatum.incidentEdges vertex.1.1 →
      edge ≠ leafEdge hLeaf → edge = other := by
    intro edge hMem hNeLeaf
    have h : edge ∈ (GluingDatum.incidentEdges vertex.1.1).erase (leafEdge hLeaf) :=
      Finset.mem_erase.mpr ⟨hNeLeaf, hMem⟩
    rw [hOtherSingle, Finset.mem_singleton] at h
    exact h
  have hOtherMem : other ∈ GluingDatum.incidentEdges vertex.1.1 := by
    have h : other ∈ (GluingDatum.incidentEdges vertex.1.1).erase (leafEdge hLeaf) := by
      rw [hOtherSingle]; exact Finset.mem_singleton_self _
    exact (Finset.mem_erase.mp h).2
  have hOtherNeLeaf : other ≠ leafEdge hLeaf := by
    have h : other ∈ (GluingDatum.incidentEdges vertex.1.1).erase (leafEdge hLeaf) := by
      rw [hOtherSingle]; exact Finset.mem_singleton_self _
    exact (Finset.mem_erase.mp h).1
  have hf₁Other : f₁.1.1 = other := hMemErase _ hf₁Mem hf₁NeLeaf
  have hf₂Other : f₂.1.1 = other := hMemErase _ hf₂Mem hf₂NeLeaf
  have hSame : f₁.1.1 = f₂.1.1 := by rw [hf₁Other, hf₂Other]
  have hAdd := sourceEdgeIndex_add_le_blockCard data hf₁Inc hf₂Inc hNe hSame
  have hPos₁ := StableLocalProperties.sourceEdgeIndex_pos data f₁
  have hPos₂ := StableLocalProperties.sourceEdgeIndex_pos data f₂
  -- the canonical occurrence above the leaf edge, which is dangling
  have hqInc : Incident data (data.sourceEdge (leafEdge hLeaf) vertex.1.2) vertex := by
    have h := incident_sourceEdge_sourceEndpoint data vertex.1.1 (leafEdge hLeaf)
      hLeafMem vertex.1.2
    rwa [GluingDatum.sourceEndpoint_self] at h
  have hqDangling : IsDangling data (data.sourceEdge (leafEdge hLeaf) vertex.1.2) := by
    by_contra hS
    exact hNo _ hS rfl hqInc
  have hqIndex : data.sourceEdgeIndex (data.sourceEdge (leafEdge hLeaf) vertex.1.2) = 1 :=
    fd.danglingEdgeNoGlue _ hqDangling
  -- the change budget bounds the number of incident occurrences by three
  have hCardForm :=
    NonDanglingValency.card_incidentSourceEdge_eq_localRamification_form data vertex
  rw [hDivalent] at hCardForm
  norm_num at hCardForm
  have hRamLe := IndexPattern.localRamification_le_targetChange fd
    (wall := vertex.1.1) ⟨vertex.1.2, vertex.2⟩
  have hChange := IndexPattern.targetChange_eq_three_sub_valency fd vertex.1.1
  rw [hDivalent] at hChange
  rw [hChange] at hRamLe
  have hRamNonneg := data.localRamification_nonneg vertex.1.1 (fd.valid.2 vertex.1.1)
    (⟨vertex.1.2, vertex.2⟩ : (data.vertexPartition vertex.1.1).Blocks)
  -- split the incidence count over the two incident target occurrences
  have hSplit := IndexPattern.card_incidentSourceEdge_eq_pair vertex
    (Ne.symm hOtherNeLeaf) hLeafMem hOtherMem hDivalent
  have hPosLeaf := SheetPartition.blockCountWithin_pos (data.edgePartition (leafEdge hLeaf))
    (data.vertexPartition vertex.1.1) vertex.1.2
  have hPosOther := SheetPartition.blockCountWithin_pos (data.edgePartition other)
    (data.vertexPartition vertex.1.1) vertex.1.2
  -- the *other* occurrence carries two distinct source occurrences
  have hOtherCountNeOne : (data.edgePartition other).blockCountWithin
      (data.vertexPartition vertex.1.1) vertex.1.2 ≠ 1 := by
    intro hOne
    apply hNe
    have h₁ : data.sourceEdge other f₁.1.2 = data.sourceEdge other vertex.1.2 :=
      IndexPattern.sourceEdge_eq_anchor vertex hOtherMem hRel₁ hOne
    have h₂ : data.sourceEdge other f₂.1.2 = data.sourceEdge other vertex.1.2 :=
      IndexPattern.sourceEdge_eq_anchor vertex hOtherMem hRel₂ hOne
    have e₁ : data.sourceEdge other f₁.1.2 = f₁ := by
      rw [← hf₁Other]; exact GluingDatum.sourceEdge_self data f₁
    have e₂ : data.sourceEdge other f₂.1.2 = f₂ := by
      rw [← hf₂Other]; exact GluingDatum.sourceEdge_self data f₂
    rw [← e₁, ← e₂, h₁, h₂]
  -- hence the leaf occurrence carries exactly one, so the block is a single sheet
  have hLeafCountOne : (data.edgePartition (leafEdge hLeaf)).blockCountWithin
      (data.vertexPartition vertex.1.1) vertex.1.2 = 1 := by omega
  have hBlockCard : (data.edgePartition (leafEdge hLeaf)).blockCard vertex.1.2 =
      (data.vertexPartition vertex.1.1).blockCard vertex.1.2 :=
    SheetPartition.blockCard_eq_of_refines_of_blockCountWithin_eq_one
      (data.edgePartition (leafEdge hLeaf)) (data.vertexPartition vertex.1.1)
      (StableLocalProperties.refines_of_mem_incidentEdges data hLeafMem) vertex.1.2 hLeafCountOne
  have hAnchorCard : data.sourceEdgeIndex (data.sourceEdge (leafEdge hLeaf) vertex.1.2) =
      (data.edgePartition (leafEdge hLeaf)).blockCard vertex.1.2 :=
    GluingDatum.sourceEdgeIndex_sourceEdge data (leafEdge hLeaf) vertex.1.2
  omega

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- Two source vertices above one target vertex sharing an incident occurrence
coincide. -/
theorem eq_of_incident_of_target_eq {first second : data.SourceVertex}
    (hTarget : (first.1.1 : target.V) = second.1.1) {edge : data.SourceEdge}
    (hFirst : Incident data edge first) (hSecond : Incident data edge second) :
    first = second := by
  obtain ⟨⟨p₁, s₁⟩, h₁⟩ := first
  obtain ⟨⟨p₂, s₂⟩, h₂⟩ := second
  simp only at hTarget
  subst hTarget
  have hRel₁ := ((incident_iff_target_mem_and_rel data edge _).mp hFirst).2
  have hRel₂ := ((incident_iff_target_mem_and_rel data edge _).mp hSecond).2
  simp only [SheetPartition.rel_iff] at hRel₁ hRel₂
  have hSheet : s₁ = s₂ := by
    simp only at h₁ h₂ hRel₁ hRel₂
    rw [← h₁, ← h₂, hRel₁, hRel₂]
  exact Subtype.ext (by simp [hSheet])

/-- **The unique surviving block above a leaf-adjacent divalent target
vertex.**  If every surviving occurrence above the leaf edge meets `branch`,
then `branch` is the only source vertex above its own image with a surviving
occurrence. -/
theorem eq_of_nonDangling
    (fd : FullDimensionalSourcePresentation data coordinate)
    {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    {branch vertex : data.SourceVertex}
    (hDivalent : (GluingDatum.incidentEdges branch.1.1).card = 2)
    (hLeafMem : leafEdge hLeaf ∈ GluingDatum.incidentEdges branch.1.1)
    (hBranch : ∀ edge : data.SourceEdge, ¬ IsDangling data edge →
      edge.1.1 = leafEdge hLeaf → Incident data edge branch)
    (hTarget : (vertex.1.1 : target.V) = branch.1.1)
    (hSurvives : 0 < nonDanglingValency data vertex) :
    vertex = branch := by
  obtain ⟨edge, hSurv, hTargetEdge, hIncV⟩ :=
    exists_survivor_above_leafEdge fd hLeaf (vertex := vertex)
      (by rw [hTarget]; exact hDivalent) (by rw [hTarget]; exact hLeafMem) hSurvives
  exact eq_of_incident_of_target_eq hTarget hIncV (hBranch edge hSurv hTargetEdge)

/-- The contrapositive: every *other* source vertex above that target vertex is
completely dangling. -/
theorem nonDanglingValency_eq_zero_of_ne
    (fd : FullDimensionalSourcePresentation data coordinate)
    {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    {branch vertex : data.SourceVertex}
    (hDivalent : (GluingDatum.incidentEdges branch.1.1).card = 2)
    (hLeafMem : leafEdge hLeaf ∈ GluingDatum.incidentEdges branch.1.1)
    (hBranch : ∀ edge : data.SourceEdge, ¬ IsDangling data edge →
      edge.1.1 = leafEdge hLeaf → Incident data edge branch)
    (hTarget : (vertex.1.1 : target.V) = branch.1.1)
    (hNe : vertex ≠ branch) :
    nonDanglingValency data vertex = 0 := by
  by_contra hPos
  exact hNe (eq_of_nonDangling fd hLeaf hDivalent hLeafMem hBranch hTarget (by omega))

/-- Two distinct surviving occurrences above the leaf edge **are** the whole
leaf fibre, so every surviving occurrence there meets whatever they meet. -/
theorem incident_of_survivor_above_leafEdge
    (fd : FullDimensionalSourcePresentation data coordinate)
    {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    {branch : data.SourceVertex} {first second : data.SourceEdge} (hNe : first ≠ second)
    (hFirstSurv : ¬ IsDangling data first) (hFirstTarget : first.1.1 = leafEdge hLeaf)
    (hFirstInc : Incident data first branch)
    (hSecondSurv : ¬ IsDangling data second) (hSecondTarget : second.1.1 = leafEdge hLeaf)
    (hSecondInc : Incident data second branch)
    {edge : data.SourceEdge} (hSurv : ¬ IsDangling data edge)
    (hTarget : edge.1.1 = leafEdge hLeaf) :
    Incident data edge branch := by
  classical
  have hSet : LeafFibre.leafSurvivors (data := data) hLeaf = {first, second} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact (LeafFibre.mem_leafSurvivors hLeaf).mpr ⟨hFirstSurv, hFirstTarget⟩
      · rw [Finset.mem_singleton] at hx
        subst hx
        exact (LeafFibre.mem_leafSurvivors hLeaf).mpr ⟨hSecondSurv, hSecondTarget⟩
    · rw [LeafFibre.leafSurvivors_card fd hLeaf, Finset.card_pair hNe]
  have hMem : edge ∈ LeafFibre.leafSurvivors (data := data) hLeaf :=
    (LeafFibre.mem_leafSurvivors hLeaf).mpr ⟨hSurv, hTarget⟩
  rw [hSet] at hMem
  rcases Finset.mem_insert.mp hMem with rfl | hMem
  · exact hFirstInc
  · rw [Finset.mem_singleton] at hMem
    subst hMem
    exact hSecondInc

/-- **The fibre above the second incident occurrence is a single survivor.**
An occurrence of `branch` whose index is the full local degree is the only
surviving occurrence above its target occurrence. -/
theorem eq_of_surviving_above_bridge
    (fd : FullDimensionalSourcePresentation data coordinate)
    {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    {branch : data.SourceVertex}
    (hDivalent : (GluingDatum.incidentEdges branch.1.1).card = 2)
    (hLeafMem : leafEdge hLeaf ∈ GluingDatum.incidentEdges branch.1.1)
    (hBranch : ∀ edge : data.SourceEdge, ¬ IsDangling data edge →
      edge.1.1 = leafEdge hLeaf → Incident data edge branch)
    {bridge : data.SourceEdge} (hBridgeInc : Incident data bridge branch)
    (hBridgeIndex : data.sourceEdgeIndex bridge =
      (data.vertexPartition branch.1.1).blockCard branch.1.2)
    {edge : data.SourceEdge} (hSurv : ¬ IsDangling data edge)
    (hTarget : edge.1.1 = bridge.1.1) :
    edge = bridge := by
  by_contra hNe
  have hEdgeMem : edge.1.1 ∈ GluingDatum.incidentEdges branch.1.1 :=
    hTarget ▸ ((incident_iff_target_mem_and_rel data bridge branch).mp hBridgeInc).1
  have hIncW : Incident data edge (data.sourceEndpoint branch.1.1 edge.1.2) :=
    (incident_iff_target_mem_and_rel data edge _).mpr
      ⟨hEdgeMem, (data.vertexPartition branch.1.1).rel_repr_left edge.1.2⟩
  have hwEq : data.sourceEndpoint branch.1.1 edge.1.2 = branch :=
    eq_of_nonDangling fd hLeaf hDivalent hLeafMem hBranch rfl
      (nonDanglingValency_pos_of_survivor hSurv hIncW)
  have hIncB : Incident data edge branch := hwEq ▸ hIncW
  have hAdd := sourceEdgeIndex_add_le_blockCard data hIncB hBridgeInc hNe hTarget
  have hPos := StableLocalProperties.sourceEdgeIndex_pos data edge
  omega

/-! ## 2.  The lollipop, under the length-two clause -/

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- The two ends of a stable row at a branch vertex carrying both of them. -/
theorem exists_row_ends {path : StablePath data} {branch : data.SourceVertex}
    (hTwo : StablePathCount.incidenceCount data branch path = 2) :
    ∃ first second : data.SourceEdge, first ≠ second ∧
      ¬ IsDangling data first ∧ Incident data first branch ∧ OnRow data path first ∧
      ¬ IsDangling data second ∧ Incident data second branch ∧ OnRow data path second := by
  classical
  have hCard : ((StablePathCount.incidentEdges data branch).filter
      (fun edge ↦ edge.stablePath = path)).card = 2 := hTwo
  obtain ⟨first, hfirstMem, second, hsecondMem, hNe⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < ((StablePathCount.incidentEdges data branch).filter
      (fun edge ↦ edge.stablePath = path)).card)
  exact ⟨first.1, second.1, fun h ↦ hNe (Subtype.ext h), first.2,
    (StablePathCount.mem_incidentEdges data branch first).mp (Finset.mem_filter.mp hfirstMem).1,
    ⟨first.2, (Finset.mem_filter.mp hfirstMem).2⟩, second.2,
    (StablePathCount.mem_incidentEdges data branch second).mp (Finset.mem_filter.mp hsecondMem).1,
    ⟨second.2, (Finset.mem_filter.mp hsecondMem).2⟩⟩

/-- The three inputs the general theorems of §1 need, assembled at a lollipop
branch vertex from the **length-two clause** `hEnds`. -/
theorem loopBranch_leafEdge_data
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : 3 ≤ nonDanglingValency data branch)
    (hTwo : StablePathCount.incidenceCount data branch path = 2)
    {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    (hEnds : ∀ edge : data.SourceEdge, OnRow data path edge →
      Incident data edge branch → edge.1.1 = leafEdge hLeaf) :
    (GluingDatum.incidentEdges branch.1.1).card = 2 ∧
      leafEdge hLeaf ∈ GluingDatum.incidentEdges branch.1.1 ∧
      ∀ edge : data.SourceEdge, ¬ IsDangling data edge →
        edge.1.1 = leafEdge hLeaf → Incident data edge branch := by
  obtain ⟨first, second, hNe, hFirstSurv, hFirstInc, hFirstRow,
    hSecondSurv, hSecondInc, hSecondRow⟩ := exists_row_ends hTwo
  have hFirstTarget : first.1.1 = leafEdge hLeaf := hEnds first hFirstRow hFirstInc
  have hSecondTarget : second.1.1 = leafEdge hLeaf := hEnds second hSecondRow hSecondInc
  refine ⟨LollipopDivalent.card_incidentEdges_eq_two_of_incidenceCount_eq_two fd hBranch hTwo,
    ?_, fun edge hSurv hTarget ↦ incident_of_survivor_above_leafEdge fd hLeaf hNe
      hFirstSurv hFirstTarget hFirstInc hSecondSurv hSecondTarget hSecondInc hSurv hTarget⟩
  exact hFirstTarget ▸ ((incident_iff_target_mem_and_rel data first branch).mp hFirstInc).1

/-- **The fibre clause above `φ(A)`** -- under the length-two clause `hEnds`:
every source vertex above `φ(A)` other than `A` itself is completely
dangling. -/
theorem nonDanglingValency_eq_zero_of_ne_loopBranch
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : 3 ≤ nonDanglingValency data branch)
    (hTwo : StablePathCount.incidenceCount data branch path = 2)
    {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    (hEnds : ∀ edge : data.SourceEdge, OnRow data path edge →
      Incident data edge branch → edge.1.1 = leafEdge hLeaf)
    {vertex : data.SourceVertex} (hTarget : (vertex.1.1 : target.V) = branch.1.1)
    (hNe : vertex ≠ branch) :
    nonDanglingValency data vertex = 0 := by
  obtain ⟨hDivalent, hLeafMem, hAll⟩ :=
    loopBranch_leafEdge_data fd hBranch hTwo hLeaf hEnds
  exact nonDanglingValency_eq_zero_of_ne fd hLeaf hDivalent hLeafMem hAll hTarget hNe

/-- **The fibre clause above `φ(e_b)`** -- under the length-two clause `hEnds`:
the bridge occurrence is the only surviving occurrence above its own target
occurrence. -/
theorem eq_bridge_of_surviving
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : 3 ≤ nonDanglingValency data branch)
    (hTwo : StablePathCount.incidenceCount data branch path = 2)
    {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    (hEnds : ∀ edge : data.SourceEdge, OnRow data path edge →
      Incident data edge branch → edge.1.1 = leafEdge hLeaf)
    {bridge : data.SourceEdge} (hBridgeSurvives : ¬ IsDangling data bridge)
    (hBridgeIncident : Incident data bridge branch)
    (hBridgeNotOnRow : ¬ OnRow data path bridge)
    {edge : data.SourceEdge} (hSurv : ¬ IsDangling data edge)
    (hTarget : edge.1.1 = bridge.1.1) :
    edge = bridge := by
  obtain ⟨hDivalent, hLeafMem, hAll⟩ :=
    loopBranch_leafEdge_data fd hBranch hTwo hLeaf hEnds
  refine eq_of_surviving_above_bridge fd hLeaf hDivalent hLeafMem hAll hBridgeIncident ?_
    hSurv hTarget
  rw [LollipopDivalent.sourceEdgeIndex_eq_two_of_not_onRow fd hBranch hTwo hBridgeSurvives
      hBridgeIncident hBridgeNotOnRow,
    LollipopDivalent.blockCard_eq_two_of_incidenceCount_eq_two fd hBranch hTwo]

/-! ## 3.  The length-two clause is a purely target-side statement -/

/-- **Every incident occurrence at a lollipop branch vertex survives**, so the
three occurrences of `card_incidentSourceEdge_eq_three` are `e₁, e₂, e_b`. -/
theorem not_isDangling_of_incident_branch
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : 3 ≤ nonDanglingValency data branch)
    (hTwo : StablePathCount.incidenceCount data branch path = 2)
    {edge : data.SourceEdge} (hIncident : Incident data edge branch) :
    ¬ IsDangling data edge := by
  classical
  have hValency : nonDanglingValency data branch = 3 := by
    have := fd.trivalent branch
    omega
  have hFilter :=
    StableLocalProperties.card_filter_not_isDangling_eq_nonDanglingValency data branch
  rw [hValency] at hFilter
  have hEq : ((Finset.univ : Finset (IncidentSourceEdge data branch)).filter
      (fun item ↦ ¬ IsDangling data item.1)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by
      rw [hFilter, LollipopDivalent.card_incidentSourceEdge_eq_three fd hBranch hTwo])
  exact (Finset.mem_filter.mp
    (Finset.eq_univ_iff_forall.mp hEq ⟨edge, hIncident⟩)).2

/-- **The length-two clause of Part II's `lm:bridge-and-loop` is equivalent to
a statement about the target tree alone.**  As soon as `φ(A)` is incident to
the leaf edge, both ends of the loop row lie above it -- so `h_l` really is
`⟨A, e₁, C, e₂, A⟩`.

The converse is trivial (a row end is incident to `A`), so what remains of
the clause is the target-side sentence "`φ(A)` is adjacent to the leaf that its
loop row passes above", which is Part I's pass-once condition at the
lollipop. -/
theorem onRow_target_eq_leafEdge
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : 3 ≤ nonDanglingValency data branch)
    (hTwo : StablePathCount.incidenceCount data branch path = 2)
    {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    (hAdj : leafEdge hLeaf ∈ GluingDatum.incidentEdges branch.1.1)
    {edge : data.SourceEdge} (hRow : OnRow data path edge)
    (hInc : Incident data edge branch) :
    edge.1.1 = leafEdge hLeaf := by
  have hqInc : Incident data (data.sourceEdge (leafEdge hLeaf) branch.1.2) branch := by
    have h := incident_sourceEdge_sourceEndpoint data branch.1.1 (leafEdge hLeaf) hAdj branch.1.2
    rwa [GluingDatum.sourceEndpoint_self] at h
  have hqIndex : data.sourceEdgeIndex (data.sourceEdge (leafEdge hLeaf) branch.1.2) = 1 :=
    LeafFibre.sourceEdgeIndex_eq_one_above_leaf fd hLeaf rfl
  have hqSurv := not_isDangling_of_incident_branch fd hBranch hTwo hqInc
  have hqRow : OnRow data path (data.sourceEdge (leafEdge hLeaf) branch.1.2) := by
    by_contra hOff
    have h2 := LollipopDivalent.sourceEdgeIndex_eq_two_of_not_onRow fd hBranch hTwo
      hqSurv hqInc hOff
    omega
  exact LollipopDivalentWitness.loopReturnsSameDirection fd (by omega) hTwo
    edge (data.sourceEdge (leafEdge hLeaf) branch.1.2) hRow hInc hqRow hqInc

/-- **The fibre clause above `φ(A)`, with the length-two clause in its target-side
form.** -/
theorem nonDanglingValency_eq_zero_of_ne_of_leafAdjacent
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : 3 ≤ nonDanglingValency data branch)
    (hTwo : StablePathCount.incidenceCount data branch path = 2)
    {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    (hAdj : leafEdge hLeaf ∈ GluingDatum.incidentEdges branch.1.1)
    {vertex : data.SourceVertex} (hTarget : (vertex.1.1 : target.V) = branch.1.1)
    (hNe : vertex ≠ branch) :
    nonDanglingValency data vertex = 0 :=
  nonDanglingValency_eq_zero_of_ne_loopBranch fd hBranch hTwo hLeaf
    (fun _ hRow hInc ↦ onRow_target_eq_leafEdge fd hBranch hTwo hLeaf hAdj hRow hInc)
    hTarget hNe

/-- **The fibre clause above `φ(e_b)`, with the length-two clause in its target-side
form.** -/
theorem eq_bridge_of_surviving_of_leafAdjacent
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : 3 ≤ nonDanglingValency data branch)
    (hTwo : StablePathCount.incidenceCount data branch path = 2)
    {leaf : target.V} (hLeaf : IsLeafVertex target leaf)
    (hAdj : leafEdge hLeaf ∈ GluingDatum.incidentEdges branch.1.1)
    {bridge : data.SourceEdge} (hBridgeSurvives : ¬ IsDangling data bridge)
    (hBridgeIncident : Incident data bridge branch)
    (hBridgeNotOnRow : ¬ OnRow data path bridge)
    {edge : data.SourceEdge} (hSurv : ¬ IsDangling data edge)
    (hTarget : edge.1.1 = bridge.1.1) :
    edge = bridge :=
  eq_bridge_of_surviving fd hBranch hTwo hLeaf
    (fun _ hRow hInc ↦ onRow_target_eq_leafEdge fd hBranch hTwo hLeaf hAdj hRow hInc)
    hBridgeSurvives hBridgeIncident hBridgeNotOnRow hSurv hTarget


/-- **The length-two clause in its three interchangeable forms.**  "`φ(A)` is incident
to the leaf edge", "*some* end of the loop row lies above the leaf edge" and
"*every* end of the loop row lies above the leaf edge" are one statement.  The
middle form is the one reached from the spine side
(`Count/RowSingleColumnWitness.lean`, `eq_two_iff_exists_end_above_leafEdge`),
so the lollipop and the spine arguments need the **same** statement. -/
theorem leafAdjacent_iff_exists_end_above_leafEdge
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {branch : data.SourceVertex}
    (hBranch : 3 ≤ nonDanglingValency data branch)
    (hTwo : StablePathCount.incidenceCount data branch path = 2)
    {leaf : target.V} (hLeaf : IsLeafVertex target leaf) :
    leafEdge hLeaf ∈ GluingDatum.incidentEdges branch.1.1 ↔
      ∃ edge : data.SourceEdge, OnRow data path edge ∧ Incident data edge branch ∧
        edge.1.1 = leafEdge hLeaf := by
  constructor
  · intro hAdj
    obtain ⟨first, -, -, -, hFirstInc, hFirstRow, -, -, -⟩ := exists_row_ends hTwo
    exact ⟨first, hFirstRow, hFirstInc,
      onRow_target_eq_leafEdge fd hBranch hTwo hLeaf hAdj hFirstRow hFirstInc⟩
  · rintro ⟨edge, -, hInc, hTarget⟩
    have hMem := ((incident_iff_target_mem_and_rel data edge branch).mp hInc).1
    rw [hTarget] at hMem
    exact hMem

end DraismaVargas.Count.LollipopBridgeFibre
