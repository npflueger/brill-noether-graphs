module

public import DraismaVargas.LocalCases.PrunedRealizationSpec
public import DraismaVargas.LocalCases.DanglingSideStructure

@[expose] public section

/-!
# The two residues of the pruned realization spec, discharged

`DraismaVargas.LocalCases.PrunedRealizationSpec` leaves two facts about
dangling occurrences named rather than proved:

* `PendantSeparated` — a dangling positive slot has an endpoint class that
  pruning discards;
* the count `classCard + keptSlotCard = keptClassCard + slotCard`, equivalently
  #(discarded classes) = #(dangling positive slots), which
  `genus_prunedSpec_eq_genus_sourceGraph_iff` shows is the genus identity
  itself.

`DraismaVargas.LocalCases.DanglingSideStructure` proves the structure theorem
both rest on, stated about a bare `GluingDatum` and a `DanglingSide`.  This
module applies it on the pair `(data, realization)` alone;
`DraismaVargas.LocalCases.PrunedContractedSpecResidues` restates the results at
the cleared-face names, as thin wrappers over this module.

## What each residue costs

`pendantSeparated` needs **nothing beyond `SourceTopology`**: the chosen far
side of a dangling occurrence of positive cleared length contains the whole
contraction class of its inner endpoint
(`DanglingSideStructure.mem_side_of_reachIn`), and every vertex of that side
has non-dangling valency zero
(`DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side`), so that class
is discarded.

The count needs two further inputs:

* `hKept : (keptClasses topology).Nonempty` — genuinely necessary: if the
  quotient source is a tree then every occurrence dangles, `keptClasses` is
  empty, and the count reads `classCard = slotCard`, false by one for a tree.
* `hConnected : data.Connected` — also genuinely necessary; the counterexample
  (a triangle beside an isolated vertex) is recorded in the header of
  `PrunedContractedSpecResidues`.  It is what `GluingDatum.Valid` already
  asserts, and it also discharges `bnExists_prunedSpec`'s own connectivity
  hypothesis (`graph_connected_contractedSpec_of_connected`).

## What is NOT proved here

Nothing about a point map into a requested metric realization, nothing about
surjectivity, and nothing about the rank of a *chosen* divisor: the transported
statement is the existential `BNExists`.  `bnExists_prunedSpec'` still takes
`hKept` and `data.Connected`; neither is discharged here.

The refinement-driven corollary `bnExists_prunedSpec_of_refinement'` of
`PrunedContractedSpecResidues` has no counterpart here: it needs §5b of
`PrunedContractedSpec` (`RefinementPresentation` of a `PackedSpec`), which this
module does not import.
-/

namespace DraismaVargas.LocalCases.PrunedRealizationSpec

open Utilities
open Utilities.Certificate
open Utilities.Certificate.DegenerateSpec
open Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.ContractionForestCensusGeneral
open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.TerminalContraction
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.DanglingDescent
open DraismaVargas.LocalCases.DanglingSideStructure

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {realization : data.NonnegativeIntegralRealization}

/-! ## 1.  A contraction class is a chain of zero-length occurrences -/

/-- The representative map of `degSpec` is the union-find fold over the zero
occurrences (`TerminalContraction.sourceDegSpec_rep`, specialised). -/
theorem degSpec_rep_eq (topology : SourceTopology data realization)
    (v : Fin (Fintype.card data.sourceGraph.V)) :
    topology.degSpec.rep v =
      compFold (UnitSubdivisionPresentation.core data.sourceGraph)
        realization.sourceZeroSet v :=
  congrFun (sourceDegSpec_rep realization topology.forest topology.notLoopy) v

/-- **Two quotient-source vertices share a contraction class exactly when a
chain of zero-length occurrences joins them.** -/
theorem classOf_eq_iff (topology : SourceTopology data realization)
    (u v : data.SourceVertex) :
    classOf topology u = classOf topology v ↔
      ReachIn (UnitSubdivisionPresentation.core data.sourceGraph)
        realization.sourceZeroSet
        (vertexIndex data u) (vertexIndex data v) := by
  constructor
  · intro h
    have hval : topology.degSpec.rep (vertexIndex data u) =
        topology.degSpec.rep (vertexIndex data v) := congrArg Subtype.val h
    rw [degSpec_rep_eq, degSpec_rep_eq] at hval
    exact (compFold_iff _ _ _ _).mp hval
  · intro h
    have hval := (compFold_iff _ _ _ _).mpr h
    exact Subtype.ext (((degSpec_rep_eq topology _).trans hval).trans
      (degSpec_rep_eq topology _).symm)

/-- A zero-length occurrence joins the two classes of its endpoints. -/
theorem classOf_eq_of_sourceLength_zero (topology : SourceTopology data realization)
    {edge : data.SourceEdge}
    (hZero : realization.sourceLength edge = 0) :
    classOf topology (data.sourceEnds edge).1 =
      classOf topology (data.sourceEnds edge).2 := by
  obtain ⟨slot, hSlot⟩ : ∃ slot, realization.sourceEdgeAt slot = edge :=
    ⟨realization.sourceSlotEquiv.symm edge,
      realization.sourceSlotEquiv.apply_symm_apply edge⟩
  have hLen : topology.degSpec.length slot = 0 := by
    show realization.sourceLength (realization.sourceEdgeAt slot) = 0
    rw [hSlot]
    exact hZero
  have hRep := topology.degSpec.rep_zero slot hLen
  rw [← hSlot, classOf_sourceEnds_fst topology slot, classOf_sourceEnds_snd topology slot]
  exact Subtype.ext hRep

/-! ## 2.  The class of the inner endpoint never escapes the far side -/

/-- **The escape theorem.**  A quotient-source vertex in the contraction class
of the inner endpoint of a dangling cut whose cut occurrence has positive
cleared length lies on the cut's side. -/
theorem mem_side_of_classOf_eq (topology : SourceTopology data realization)
    {inner outer : data.SourceVertex}
    (cut : DanglingSide data.sourceGraph inner outer)
    {edge : data.SourceEdge}
    (hEnds : data.sourceEnds edge = (inner, outer) ∨
      data.sourceEnds edge = (outer, inner))
    (hPos : 0 < realization.sourceLength edge)
    {u : data.SourceVertex}
    (hu : classOf topology u = classOf topology inner) : u ∈ cut.side := by
  have hReach := (classOf_eq_iff topology inner u).mp hu.symm
  have hMem := mem_side_of_reachIn realization cut hEnds hPos
    (a := vertexIndex data inner) (b := vertexIndex data u)
    (by rw [Equiv.symm_apply_apply]; exact cut.left_mem) hReach
  rwa [Equiv.symm_apply_apply] at hMem

/-- **The far class is discarded.**  The contraction class of the inner
endpoint of a dangling occurrence of positive cleared length contains no
surviving vertex. -/
theorem not_keptClass_inner (topology : SourceTopology data realization)
    {edge : data.SourceEdge}
    (hPos : 0 < realization.sourceLength edge)
    (item : DanglingData data edge) :
    ¬ KeptClass topology (classOf topology item.inner) := by
  rintro ⟨u, hu, hValency⟩
  rw [nonDanglingValency_eq_zero_of_mem_side data item.cut
    (mem_side_of_classOf_eq topology item.cut item.ends hPos hu)] at hValency
  omega

/-! ## 3.  The first residue: `PendantSeparated` -/

/-- **`PendantSeparated`, proved.**  A dangling positive slot has an endpoint
class that pruning discards — namely the class of the inner endpoint of its far
side.  The only hypotheses are the two fields of `SourceContractionTopology`,
and they enter only through `classOf`. -/
theorem pendantSeparated (topology : SourceTopology data realization) :
    PendantSeparated topology := by
  intro e hDropped
  have hDangling : IsDangling data (realization.sourceEdgeAt e.val) :=
    not_not.mp hDropped
  have hPos : 0 < realization.sourceLength
      (realization.sourceEdgeAt e.val) := e.property
  have hNot : ¬ KeptClass topology
      (classOf topology (chosenDangling hDangling).inner) :=
    not_keptClass_inner topology hPos (chosenDangling hDangling)
  rcases (chosenDangling hDangling).ends with hEnds | hEnds
  · refine Or.inl ?_
    rw [← classOf_sourceEnds_fst topology e.val, hEnds]
    exact hNot
  · refine Or.inr ?_
    rw [← classOf_sourceEnds_snd topology e.val, hEnds]
    exact hNot

/-! ## 4.  The far class of a dropped slot -/

/-- A slot that pruning drops carries a dangling occurrence. -/
theorem isDangling_of_not_mem_keptSlots (topology : SourceTopology data realization)
    {e' : Fin topology.degSpec.slotCard} (he' : e' ∉ keptSlots topology) :
    IsDangling data (realization.sourceEdgeAt
      (topology.degSpec.slotIndex.symm e').val) := by
  rw [mem_keptSlots] at he'
  exact not_not.mp he'

/-- Its cleared length is positive: it is a slot of `degSpec`. -/
theorem sourceLength_pos_of_slot (topology : SourceTopology data realization)
    (e' : Fin topology.degSpec.slotCard) :
    0 < realization.sourceLength
      (realization.sourceEdgeAt (topology.degSpec.slotIndex.symm e').val) :=
  (topology.degSpec.slotIndex.symm e').property

/-- The chosen far side of a dropped slot. -/
noncomputable def droppedData (topology : SourceTopology data realization)
    {e' : Fin topology.degSpec.slotCard} (he' : e' ∉ keptSlots topology) :
    DanglingData data (realization.sourceEdgeAt
      (topology.degSpec.slotIndex.symm e').val) :=
  chosenDangling (isDangling_of_not_mem_keptSlots topology he')

/-- **The discarded class of a dropped slot**: the class of the inner endpoint
of its far side. -/
noncomputable def droppedClass (topology : SourceTopology data realization)
    {e' : Fin topology.degSpec.slotCard} (he' : e' ∉ keptSlots topology) :
    Fin topology.degSpec.classCard :=
  topology.degSpec.classIndex (classOf topology (droppedData topology he').inner)

theorem droppedClass_not_mem_keptClasses (topology : SourceTopology data realization)
    {e' : Fin topology.degSpec.slotCard} (he' : e' ∉ keptSlots topology) :
    droppedClass topology he' ∉ keptClasses topology := by
  rw [mem_keptClasses, droppedClass, Equiv.symm_apply_apply]
  exact not_keptClass_inner topology (sourceLength_pos_of_slot topology e') _

/-- A nonempty set of kept classes produces a surviving quotient-source
vertex. -/
theorem exists_survivor (topology : SourceTopology data realization)
    (hKept : (keptClasses topology).Nonempty) :
    ∃ v : data.SourceVertex, 0 < nonDanglingValency data v := by
  obtain ⟨c', hc'⟩ := hKept
  rw [mem_keptClasses] at hc'
  obtain ⟨v, _, hv⟩ := hc'
  exact ⟨v, hv⟩

/-- **Injectivity.**  Distinct dropped slots have distinct discarded classes. -/
theorem droppedClass_injective (topology : SourceTopology data realization)
    (hKept : (keptClasses topology).Nonempty)
    {e₁ e₂ : Fin topology.degSpec.slotCard}
    (h₁ : e₁ ∉ keptSlots topology) (h₂ : e₂ ∉ keptSlots topology)
    (hEq : droppedClass topology h₁ = droppedClass topology h₂) : e₁ = e₂ := by
  obtain ⟨survivor, hSurvivor⟩ := exists_survivor topology hKept
  by_contra hNe
  have hClass : classOf topology (droppedData topology h₁).inner =
      classOf topology (droppedData topology h₂).inner :=
    topology.degSpec.classIndex.injective hEq
  have hEdgeNe : realization.sourceEdgeAt (topology.degSpec.slotIndex.symm e₁).val ≠
      realization.sourceEdgeAt (topology.degSpec.slotIndex.symm e₂).val := by
    intro hEqual
    exact hNe (topology.degSpec.slotIndex.symm.injective (Subtype.ext
      (realization.sourceSlotEquiv.injective hEqual)))
  exact false_of_inner_mem_side data hSurvivor (droppedData topology h₁)
    (droppedData topology h₂) hEdgeNe
    (mem_side_of_classOf_eq topology (droppedData topology h₁).cut
      (droppedData topology h₁).ends (sourceLength_pos_of_slot topology e₁) hClass.symm)
    (mem_side_of_classOf_eq topology (droppedData topology h₂).cut
      (droppedData topology h₂).ends (sourceLength_pos_of_slot topology e₂) hClass)

/-! ## 5.  Surjectivity -/

/-- Any dangling occurrence of positive cleared length is a dropped slot, with
the same far class. -/
theorem exists_dropped_of_danglingData (topology : SourceTopology data realization)
    {survivor : data.SourceVertex}
    (hSurvivor : 0 < nonDanglingValency data survivor)
    {edge : data.SourceEdge}
    (hPos : 0 < realization.sourceLength edge)
    (item : DanglingData data edge) :
    ∃ (e' : Fin topology.degSpec.slotCard) (he' : e' ∉ keptSlots topology),
      classOf topology (droppedData topology he').inner =
        classOf topology item.inner := by
  obtain ⟨slot, hSlot⟩ : ∃ slot, realization.sourceEdgeAt slot = edge :=
    ⟨realization.sourceSlotEquiv.symm edge,
      realization.sourceSlotEquiv.apply_symm_apply edge⟩
  have hLen : 0 < topology.degSpec.length slot := by
    show 0 < realization.sourceLength (realization.sourceEdgeAt slot)
    rw [hSlot]
    exact hPos
  have hNotKept : topology.degSpec.slotIndex ⟨slot, hLen⟩ ∉ keptSlots topology := by
    rw [mem_keptSlots, Equiv.symm_apply_apply]
    refine not_not.mpr ?_
    show IsDangling data (realization.sourceEdgeAt slot)
    rw [hSlot]
    exact isDangling_of_danglingData item
  refine ⟨topology.degSpec.slotIndex ⟨slot, hLen⟩, hNotKept, congrArg (classOf topology) ?_⟩
  refine inner_eq_of_danglingData_of_eq data hSurvivor ?_ _ item
  rw [Equiv.symm_apply_apply]
  exact hSlot

/-- **Surjectivity.**  A discarded class is the far class of a dropped slot.
If it were not, then the class together with the far sides hanging off it
would be closed under adjacency and carry no surviving vertex, so — the
quotient source being connected — nothing would survive at all. -/
theorem exists_dropped_of_not_keptClass (topology : SourceTopology data realization)
    (hKept : (keptClasses topology).Nonempty)
    (hConnected : data.Connected)
    {c : topology.degSpec.Class} (hc : ¬ KeptClass topology c) :
    ∃ (e' : Fin topology.degSpec.slotCard) (he' : e' ∉ keptSlots topology),
      classOf topology (droppedData topology he').inner = c := by
  classical
  obtain ⟨survivor, hSurvivor⟩ := exists_survivor topology hKept
  by_cases hAny : ∃ (edge : data.SourceEdge)
      (_ : 0 < realization.sourceLength edge)
      (item : DanglingData data edge), classOf topology item.inner = c
  · obtain ⟨edge, hPos, item, hInner⟩ := hAny
    obtain ⟨e', he', hEq⟩ :=
      exists_dropped_of_danglingData topology hSurvivor hPos item
    exact ⟨e', he', hEq.trans hInner⟩
  · exfalso
    have hBase : classOf topology
        ((vertexIndex data).symm c.val) = c := by
      refine Subtype.ext ?_
      show topology.degSpec.rep
        (vertexIndex data ((vertexIndex data).symm c.val)) = c.val
      rw [Equiv.apply_symm_apply]
      exact c.property
    have hStep : ∀ a b : data.SourceVertex,
        0 < num_edges data.sourceGraph a b →
        (classOf topology a = c ∨ ∃ (x y : data.SourceVertex)
          (cut : DanglingSide data.sourceGraph x y),
          classOf topology y = c ∧ a ∈ cut.side) →
        (classOf topology b = c ∨ ∃ (x y : data.SourceVertex)
          (cut : DanglingSide data.sourceGraph x y),
          classOf topology y = c ∧ b ∈ cut.side) := by
      intro a b hEdge hPrev
      obtain ⟨edge, hEnds⟩ :=
        exists_sourceEnds_of_num_edges_pos data hEdge
      rcases hPrev with hClassA | ⟨x, y, cut, hy, hMem⟩
      · by_cases hLen : realization.sourceLength edge = 0
        · refine Or.inl ?_
          have hJoin := classOf_eq_of_sourceLength_zero topology hLen
          rcases hEnds with hE | hE <;> rw [hE] at hJoin
          · exact hJoin.symm.trans hClassA
          · exact hJoin.trans hClassA
        · have hPos : 0 < realization.sourceLength edge := Nat.pos_of_ne_zero hLen
          have hValency : nonDanglingValency data a = 0 := by
            by_contra hNeZero
            exact hc ⟨a, hClassA, Nat.pos_of_ne_zero hNeZero⟩
          have hDangling : IsDangling data edge :=
            (nonDanglingValency_eq_zero_iff data a).mp hValency edge
              (incident_of_sourceEnds data hEnds)
          have hOrient :
              ((chosenDangling hDangling).inner = a ∧
                  (chosenDangling hDangling).outer = b) ∨
                ((chosenDangling hDangling).inner = b ∧
                  (chosenDangling hDangling).outer = a) := by
            rcases (chosenDangling hDangling).ends with h1 | h1 <;>
              rcases hEnds with h2 | h2 <;> rw [h1] at h2
            · exact Or.inl ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩
            · exact Or.inr ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩
            · exact Or.inr ⟨congrArg Prod.snd h2, congrArg Prod.fst h2⟩
            · exact Or.inl ⟨congrArg Prod.snd h2, congrArg Prod.fst h2⟩
          rcases hOrient with ⟨hInner, _⟩ | ⟨hInner, hOuter⟩
          · exact absurd ⟨edge, hPos, chosenDangling hDangling,
              by rw [hInner]; exact hClassA⟩ hAny
          · refine Or.inr ⟨(chosenDangling hDangling).inner,
              (chosenDangling hDangling).outer, (chosenDangling hDangling).cut, ?_, ?_⟩
            · rw [hOuter]
              exact hClassA
            · rw [← hInner]
              exact (chosenDangling hDangling).cut.left_mem
      · by_cases hb : b ∈ cut.side
        · exact Or.inr ⟨x, y, cut, hy, hb⟩
        · refine Or.inl ?_
          have hCross := cut.cross_num_edges a b hMem hb
          have hPair : a = x ∧ b = y := by
            by_contra hno
            have hVanish : num_edges data.sourceGraph a b = 0 := by
              rw [hCross]
              exact ite_eq_right hno
            omega
          rw [hPair.2]
          exact hy
    have hAll := reach_propagate (H := data.sourceGraph)
      (motive := fun z ↦ classOf topology z = c ∨
        ∃ (x y : data.SourceVertex)
          (cut : DanglingSide data.sourceGraph x y),
          classOf topology y = c ∧ z ∈ cut.side)
      (Or.inl hBase) hStep
      (reach_of_graph_connected hConnected _ survivor)
    rcases hAll with hClass | ⟨x, y, cut, _, hMem⟩
    · exact hc ⟨survivor, hClass, hSurvivor⟩
    · rw [nonDanglingValency_eq_zero_of_mem_side data cut hMem] at hSurvivor
      omega

/-! ## 6.  The second residue: the count -/

/-- **The bijection.**  Discarded classes and dropped positive slots are
equinumerous. -/
theorem card_sdiff_keptSlots_eq_card_sdiff_keptClasses
    (topology : SourceTopology data realization)
    (hKept : (keptClasses topology).Nonempty)
    (hConnected : data.Connected) :
    (Finset.univ \ keptSlots topology).card =
      (Finset.univ \ keptClasses topology).card := by
  classical
  refine Finset.card_bij
    (fun e' he' ↦ droppedClass topology (Finset.mem_sdiff.mp he').2) ?_ ?_ ?_
  · intro e' he'
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      droppedClass_not_mem_keptClasses topology _⟩
  · intro e₁ h₁ e₂ h₂ hEq
    exact droppedClass_injective topology hKept _ _ hEq
  · intro c' hc'
    have hNot : ¬ KeptClass topology (topology.degSpec.classIndex.symm c') := by
      have hMem := (Finset.mem_sdiff.mp hc').2
      rwa [mem_keptClasses] at hMem
    obtain ⟨e', he', hEq⟩ :=
      exists_dropped_of_not_keptClass topology hKept hConnected hNot
    refine ⟨e', Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, he'⟩, ?_⟩
    show topology.degSpec.classIndex
      (classOf topology (droppedData topology he').inner) = c'
    rw [hEq, Equiv.apply_symm_apply]

/-- **The count, proved.**  `#(discarded classes) = #(dangling positive
slots)`, in the subtraction-free form
`genus_prunedSpec_eq_genus_sourceGraph_iff` asks for. -/
theorem classCard_add_keptSlots_card (topology : SourceTopology data realization)
    (hKept : (keptClasses topology).Nonempty)
    (hConnected : data.Connected) :
    topology.degSpec.classCard + (keptSlots topology).card =
      (keptClasses topology).card + topology.degSpec.slotCard := by
  classical
  have hCount := card_sdiff_keptSlots_eq_card_sdiff_keptClasses topology hKept hConnected
  have hSlots : (Finset.univ \ keptSlots topology).card + (keptSlots topology).card =
      topology.degSpec.slotCard := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_fin]
  have hClasses : (Finset.univ \ keptClasses topology).card + (keptClasses topology).card =
      topology.degSpec.classCard := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_fin]
  omega

/-! ## 7.  The corollaries, with both residues discharged -/

/-- Connectivity of the contracted spec is free from connectivity of the
quotient source: the canonical core is connected, the contraction carries that
to the contracted core, and a `Spec` with connected core has connected
graph. -/
theorem graph_connected_contractedSpec_of_connected
    (topology : SourceTopology data realization)
    (hConnected : data.Connected) :
    graph_connected topology.contractedSpec.graph :=
  SubdivisionGraph.Spec.graph_connected_of_coreConnected _
    (topology.degSpec.canonicalContraction.target_core_connected
      (unitPresentationCore_connected_of_graph_connected
        data.sourceGraph hConnected))

/-- **`prunedSpec_laplacianEquiv`, unconditional.** -/
noncomputable def prunedSpec_laplacianEquiv' (topology : SourceTopology data realization)
    (hKept : (keptClasses topology).Nonempty) :
    LaplacianEquiv (prunedSpec topology hKept).graph
      (inducedSubgraph topology.contractedSpec.graph (prunedVertices topology)
        (PendantDeletion.Spec.keptVertices_nonempty hKept)) :=
  prunedSpec_laplacianEquiv topology hKept (pendantSeparated topology)

/-- **The Euler transport, unconditional** given source connectivity. -/
theorem genus_prunedSpec_eq_genus_sourceGraph'
    (topology : SourceTopology data realization)
    (hKept : (keptClasses topology).Nonempty)
    (hConnected : data.Connected) :
    genus (prunedSpec topology hKept).graph = genus data.sourceGraph :=
  genus_prunedSpec_eq_genus_sourceGraph topology hKept
    (classCard_add_keptSlots_card topology hKept hConnected)

/-- **The pendant-deletion pushforward, unconditional** given source
connectivity: no `PendantSeparated`, no count, no connectivity of the
contracted spec and no genus identity are asked of the caller. -/
theorem bnExists_prunedSpec' (topology : SourceTopology data realization)
    (hKept : (keptClasses topology).Nonempty)
    (hConnected : data.Connected)
    {divisorDegree : ℤ}
    (hBN : BNExists topology.contractedSpec.graph 1 divisorDegree) :
    BNExists (prunedSpec topology hKept).graph 1 divisorDegree :=
  bnExists_prunedSpec topology hKept (pendantSeparated topology)
    (graph_connected_contractedSpec_of_connected topology hConnected)
    ((genus_prunedSpec_eq_genus_sourceGraph' topology hKept hConnected).trans
      (genus_contractedSpec_eq topology).symm) hBN

end DraismaVargas.LocalCases.PrunedRealizationSpec
