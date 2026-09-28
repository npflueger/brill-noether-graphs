import DraismaVargas.Infrastructure.ContractionFibre
import DraismaVargas.Infrastructure.IteratedContraction
import DraismaVargas.Infrastructure.IteratedContractionSource
import DraismaVargas.LocalCases.ZeroForestBridge

/-!
# The zero set stays a census forest under contraction

`DraismaVargas.LocalCases.ZeroForestBridge` turns the terminal face's
single receipt

```
IsForest (UnitSubdivisionPresentation.core data.sourceGraph) realization.sourceZeroSet
```

into `ContractionForestAt data e` at a zero-length target occurrence `e`.  That
discharges the Draisma--Vargas contraction receipt at the **starting** stage of
`IteratedContraction`.  This file supplies the induction: after
contracting one zero-length occurrence the remaining zero set is still a census
forest of the **new** quotient source, so the receipt is available at every
stage the iteration actually reaches.

## The count

Write `n`, `p` for the vertex and occurrence counts of the quotient source `S`,
`F` for its zero slot set, `C = |image (compFold core F)|` for the number of
components of `(S, F)`, and `n'`, `F'`, `C'` for the same data after contracting
a zero-length target occurrence `c`.  Let `k` be the number of source
occurrences above `c`; all of them have length zero, so they all lie in `F`.

`IsForest core F` is `C + F.card = n`, and `C + F.card ≥ n` holds for *every*
slot set (`card_le_card_image_compFold_add_card`).  So only the `≤` half has to
be proved downstairs, and it splits into three inequalities, each of which is
the easy direction of its own statement:

* `C' ≤ C` (`card_image_compFold_contractDatum_le`): the source vertex map
  is surjective and carries a zero occurrence either to a zero occurrence or to
  a collapsed pair, so components map onto components;
* `F'.card + k = F.card` (`card_sourceZeroSet_contractDatum`): the surviving
  source occurrences are exactly the source occurrences not above `c`, with
  unchanged lengths;
* `n ≤ n' + k` (`card_sourceVertex_contractDatum_ge`): the fibres of the source
  vertex map are the classes of the walk relation through the `k` occurrences
  above `c`, and contracting `k` slots cuts the class count by at most `k`.

Adding them to `C + F.card = n` gives `C' + F'.card ≤ n - k ≤ n'`, hence
equality, hence `IsForest core' F'`.

**The forest property is preserved only when the contracted occurrence has
length zero.**  Contracting a *positive* occurrence merges source vertices that
a zero walk may already join, and then the new zero set carries a cycle; see
the module note before `isForest_contractDatum`.  This is why the iteration
below runs along `ContractsFlaggedMany` for the zero-length flag rather than
along bare `ContractsMany`.

## What is proved

* `isForest_contractDatum` — deliverable (1), the one-step statement;
* `isForest_of_contractsFlaggedMany` — its iteration;
* `exists_terminal_positive_of_isForest`,
  `exists_terminal_integralRealization_of_isForest` — the terminal conclusion of
  `IteratedContraction` with the forest receipt demanded **only at the starting
  stage**, which is what the terminal face of Part I can actually supply;
* `targetLength_targetMap`, `exists_sourceCorrespondence_zero`,
  `exists_terminal_sourceCorrespondence` — the identification `hZero` that
  `TerminalContraction.faceSourceEquivOfTerminal` consumes, and the whole
  package it needs, assembled at the `Step` level.
-/

namespace DraismaVargas.LocalCases.ZeroForestPreservation

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.ZeroForestBridge
open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral

universe u

/-! ## Three generic counting lemmas -/

section Generic

variable {α β : Type*}

/-- If an idempotent `r` is separated by `ψ` — distinct `r`-classes have
distinct `ψ`-values — then `r` has at most `Fintype.card β` classes. -/
theorem card_image_le_card_of_separating [Fintype α] [DecidableEq α] [Fintype β]
    {r : α → α} {ψ : α → β} (hidem : ∀ x, r (r x) = r x)
    (hsep : ∀ x y, ψ x = ψ y → r x = r y) :
    (Finset.image r Finset.univ).card ≤ Fintype.card β := by
  classical
  rw [← Finset.card_univ (α := β)]
  refine Finset.card_le_card_of_injOn ψ (fun _ _ ↦ Finset.mem_univ _) ?_
  intro first hFirst second hSecond hValue
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hFirst)
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hSecond)
  have hStep := hsep _ _ hValue
  rwa [hidem, hidem] at hStep

/-- A map constant on the classes of `r` takes at most as many values as `r`
has classes. -/
theorem card_image_le_card_image_of_factors [Fintype α] [DecidableEq α]
    [DecidableEq β] {r : α → α} {g : α → β} (hFactor : ∀ x, g (r x) = g x) :
    (Finset.image g Finset.univ).card ≤ (Finset.image r Finset.univ).card := by
  have hRewrite : Finset.image g (Finset.univ : Finset α)
      = Finset.image g (Finset.image r Finset.univ) := by
    rw [Finset.image_image]
    exact Finset.image_congr fun x _ ↦ (hFactor x).symm
  rw [hRewrite]
  exact Finset.card_image_le

/-- Reflexive-transitive closure transported along an equivalence of the
underlying types. -/
theorem reflTransGen_of_equiv (equiv : α ≃ β) {R : α → α → Prop} {S : β → β → Prop}
    (hStep : ∀ x y : α, R x y ↔ S (equiv x) (equiv y)) (x y : α) :
    Relation.ReflTransGen R x y ↔ Relation.ReflTransGen S (equiv x) (equiv y) := by
  constructor
  · intro hReach
    induction hReach with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hLast ih => exact ih.tail ((hStep _ _).mp hLast)
  · intro hReach
    have hBack : ∀ u v : β, Relation.ReflTransGen S u v →
        Relation.ReflTransGen R (equiv.symm u) (equiv.symm v) := by
      intro u v hUV
      induction hUV with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hLast ih =>
        refine ih.tail ((hStep _ _).mpr ?_)
        rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have hResult := hBack _ _ hReach
    rwa [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at hResult

end Generic

/-! ## The dictionary between census slots and source occurrences

`ContractionForestCensusGeneral` works with slots `Fin p` and vertex labels
`Fin n`; the contraction fibre analysis of `ContractionFibre` works with
`data.SourceEdge` and `data.SourceVertex`.  The two are matched by
`sourceSlotEquiv` and `UnitSubdivisionPresentation.vertexEquiv`; this section
records the translation of the census walk relation. -/

section Dictionary

attribute [local instance 0] Classical.propDecidable

variable {target : CFGraph} {degree : ℕ}

/-- The canonical finite labelling of the quotient-source vertices, read as an
equivalence.  `ZeroForestBridge.sourceVertexOf` is the underlying function. -/
noncomputable def sourceVertexEquiv (data : GluingDatum target degree) :
    Fin (Fintype.card data.sourceGraph.V) ≃ data.SourceVertex :=
  (UnitSubdivisionPresentation.vertexEquiv data.sourceGraph).symm

theorem sourceVertexEquiv_apply (data : GluingDatum target degree)
    (label : Fin (Fintype.card data.sourceGraph.V)) :
    sourceVertexEquiv data label = sourceVertexOf data label := rfl

theorem sourceVertexOf_injective (data : GluingDatum target degree) :
    Function.Injective (sourceVertexOf data) :=
  (sourceVertexEquiv data).injective

/-- The slot carrying a given source occurrence. -/
noncomputable def slotOf (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization) (edge : data.SourceEdge) :
    Fin data.sourceGraph.edges.card :=
  realization.sourceSlotEquiv.symm edge

@[simp] theorem sourceEdgeAt_slotOf (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization) (edge : data.SourceEdge) :
    realization.sourceEdgeAt (slotOf data realization edge) = edge := by
  rw [← GluingDatum.NonnegativeIntegralRealization.sourceSlotEquiv_apply, slotOf,
    Equiv.apply_symm_apply]

@[simp] theorem slotOf_sourceEdgeAt (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (slot : Fin data.sourceGraph.edges.card) :
    slotOf data realization (realization.sourceEdgeAt slot) = slot := by
  rw [slotOf, ← GluingDatum.NonnegativeIntegralRealization.sourceSlotEquiv_apply,
    Equiv.symm_apply_apply]

/-- One step of a walk along the source occurrences carrying a slot of `F`. -/
def SlotStep (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (F : Finset (Fin data.sourceGraph.edges.card))
    (x y : data.SourceVertex) : Prop :=
  ∃ slot ∈ F,
    ((data.sourceEnds (realization.sourceEdgeAt slot)).1 = x ∧
        (data.sourceEnds (realization.sourceEdgeAt slot)).2 = y) ∨
      ((data.sourceEnds (realization.sourceEdgeAt slot)).2 = x ∧
        (data.sourceEnds (realization.sourceEdgeAt slot)).1 = y)

/-- A `SlotStep` named by the source occurrence rather than by its slot. -/
theorem slotStep_of_sourceEdge (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    {F : Finset (Fin data.sourceGraph.edges.card)} {edge : data.SourceEdge}
    (hMember : slotOf data realization edge ∈ F) :
    SlotStep data realization F (data.sourceEnds edge).1 (data.sourceEnds edge).2 := by
  refine ⟨slotOf data realization edge, hMember, Or.inl ⟨?_, ?_⟩⟩ <;>
    rw [sourceEdgeAt_slotOf]

/-- **The dictionary, one step.**  Census adjacency through the slots of `F` is
exactly a `SlotStep` between the corresponding source vertices. -/
theorem adjInList_iff_slotStep (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (F : Finset (Fin data.sourceGraph.edges.card))
    (x y : Fin (Fintype.card data.sourceGraph.V)) :
    AdjInList (UnitSubdivisionPresentation.core data.sourceGraph) (edgeList F) x y ↔
      SlotStep data realization F (sourceVertexOf data x) (sourceVertexOf data y) := by
  constructor
  · rintro ⟨slot, hSlot, hEnds⟩
    refine ⟨slot, (mem_edgeList F slot).mp hSlot, ?_⟩
    rcases hEnds with ⟨hTail, hHead⟩ | ⟨hHead, hTail⟩
    · exact Or.inl
        ⟨(vertexEquiv_symm_core_tail data realization slot).symm.trans
            (congrArg (sourceVertexOf data) hTail),
          (vertexEquiv_symm_core_head data realization slot).symm.trans
            (congrArg (sourceVertexOf data) hHead)⟩
    · exact Or.inr
        ⟨(vertexEquiv_symm_core_head data realization slot).symm.trans
            (congrArg (sourceVertexOf data) hHead),
          (vertexEquiv_symm_core_tail data realization slot).symm.trans
            (congrArg (sourceVertexOf data) hTail)⟩
  · rintro ⟨slot, hSlot, hEnds⟩
    refine ⟨slot, (mem_edgeList F slot).mpr hSlot, ?_⟩
    rcases hEnds with ⟨hTail, hHead⟩ | ⟨hHead, hTail⟩
    · refine Or.inl ⟨sourceVertexOf_injective data ?_, sourceVertexOf_injective data ?_⟩
      · rw [vertexEquiv_symm_core_tail]; exact hTail
      · rw [vertexEquiv_symm_core_head]; exact hHead
    · refine Or.inr ⟨sourceVertexOf_injective data ?_, sourceVertexOf_injective data ?_⟩
      · rw [vertexEquiv_symm_core_head]; exact hHead
      · rw [vertexEquiv_symm_core_tail]; exact hTail

/-- **The dictionary.**  Census reachability through the slots of `F` is exactly
a walk of `SlotStep`s. -/
theorem reachIn_iff_reflTransGen_slotStep (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (F : Finset (Fin data.sourceGraph.edges.card))
    (x y : Fin (Fintype.card data.sourceGraph.V)) :
    ReachIn (UnitSubdivisionPresentation.core data.sourceGraph) F x y ↔
      Relation.ReflTransGen (SlotStep data realization F)
        (sourceVertexOf data x) (sourceVertexOf data y) :=
  reflTransGen_of_equiv (sourceVertexEquiv data)
    (adjInList_iff_slotStep data realization F) x y

end Dictionary

/-! ## The vertex count: contracting merges at most `k` classes

The fibres of `GluingContraction.sourceVertexMap` are the classes of the walk
relation through the source occurrences above the contracted target occurrence
(`ContractionFibre.sourceVertexMap_eq_iff`), and the census bound
`card_le_card_image_compFold_add_card` says that contracting `k` slots cuts the
class count by at most `k`.  Together: the contracted quotient source has at
least `n - k` vertices. -/

section VertexCount

open GraphContraction GluingContraction ContractionFibre

attribute [local instance 0] Classical.propDecidable

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}

theorem SlotStep.symm (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    {F : Finset (Fin data.sourceGraph.edges.card)} {x y : data.SourceVertex}
    (h : SlotStep data realization F x y) : SlotStep data realization F y x := by
  obtain ⟨slot, hSlot, hEnds⟩ := h
  rcases hEnds with ⟨hFirst, hSecond⟩ | ⟨hSecond, hFirst⟩
  · exact ⟨slot, hSlot, Or.inr ⟨hSecond, hFirst⟩⟩
  · exact ⟨slot, hSlot, Or.inl ⟨hFirst, hSecond⟩⟩

theorem reflTransGen_slotStep_symm (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    {F : Finset (Fin data.sourceGraph.edges.card)} {x y : data.SourceVertex}
    (h : Relation.ReflTransGen (SlotStep data realization F) x y) :
    Relation.ReflTransGen (SlotStep data realization F) y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hLast ih =>
    exact (Relation.ReflTransGen.single (SlotStep.symm data realization hLast)).trans ih

/-- A walk through the occurrences above the contracted target occurrence is a
walk through the slots of `fibreSlots`. -/
theorem reflTransGen_slotStep_of_reachThroughContracted
    (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    {x y : data.SourceVertex} (h : ReachThroughContracted data contracted x y) :
    Relation.ReflTransGen
      (SlotStep data realization (fibreSlots data realization contracted)) x y := by
  induction h with
  | rel u v huv =>
    obtain ⟨edge, hAbove, hTail, hHead⟩ := huv
    have hMember : slotOf data realization edge
        ∈ fibreSlots data realization contracted := by
      rw [mem_fibreSlots, sourceEdgeAt_slotOf]
      exact hAbove
    rw [← hTail, ← hHead]
    exact Relation.ReflTransGen.single
      (slotStep_of_sourceEdge data realization hMember)
  | refl u => exact Relation.ReflTransGen.refl
  | symm u v _ ih => exact reflTransGen_slotStep_symm data realization ih
  | trans u v w _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- The union-find fold of the fibre slots has at most as many classes as the
contracted quotient source has vertices: its classes are separated by
`sourceVertexMap`. -/
theorem card_image_compFold_fibreSlots_le (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) :
    (Finset.image
        (compFold (UnitSubdivisionPresentation.core data.sourceGraph)
          (fibreSlots data realization contracted)) Finset.univ).card
      ≤ Fintype.card (contractDatum data hc hab hOne).sourceGraph.V := by
  refine card_image_le_card_of_separating
    (compFold_idem (UnitSubdivisionPresentation.core data.sourceGraph)
      (fibreSlots data realization contracted))
    (ψ := fun label ↦ sourceVertexMap data hc hab hOne (sourceVertexOf data label)) ?_
  intro x y hValue
  refine (compFold_iff (UnitSubdivisionPresentation.core data.sourceGraph)
    (fibreSlots data realization contracted) x y).mpr ?_
  refine (reachIn_iff_reflTransGen_slotStep data realization
    (fibreSlots data realization contracted) x y).mpr ?_
  exact reflTransGen_slotStep_of_reachThroughContracted data realization
    ((sourceVertexMap_eq_iff data hc hab hOne _ _).mp hValue)

/-- **The vertex half of the count.**  Contracting a target occurrence removes
at most as many quotient-source vertices as there are source occurrences above
it. -/
theorem card_sourceVertex_contractDatum_ge (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) :
    Fintype.card data.sourceGraph.V
      ≤ Fintype.card (contractDatum data hc hab hOne).sourceGraph.V
        + (fibreSlots data realization contracted).card := by
  have hBound := card_le_card_image_compFold_add_card
    (UnitSubdivisionPresentation.core data.sourceGraph)
    (fibreSlots data realization contracted)
  have hClasses := card_image_compFold_fibreSlots_le data realization hc hab hOne
  omega

end VertexCount

/-! ## The occurrence count: the zero set loses exactly the fibre

The surviving source occurrences are exactly the source occurrences not above
the contracted target occurrence (`GluingContraction.sourceEdgeMap`), and they
keep their lengths.  Since the contracted occurrence has length zero, every
source occurrence above it is a zero occurrence, so the zero set loses exactly
the fibre. -/

section OccurrenceCount

open GraphContraction GluingContraction IteratedContraction

attribute [local instance 0] Classical.propDecidable

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}

/-- The zero slots are the zero source occurrences. -/
theorem card_sourceZeroSet (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization) :
    realization.sourceZeroSet.card
      = (Finset.univ.filter fun edge : data.SourceEdge ↦
          realization.sourceLength edge = 0).card := by
  refine Finset.card_bij'
    (fun slot _ ↦ realization.sourceEdgeAt slot)
    (fun edge _ ↦ slotOf data realization edge)
    (fun slot hSlot ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (GluingDatum.NonnegativeIntegralRealization.mem_sourceZeroSet
        realization slot).mp hSlot⟩)
    (fun edge hEdge ↦ ?_)
    (fun slot _ ↦ slotOf_sourceEdgeAt data realization slot)
    (fun edge _ ↦ sourceEdgeAt_slotOf data realization edge)
  rw [GluingDatum.NonnegativeIntegralRealization.mem_sourceZeroSet,
    sourceEdgeAt_slotOf]
  exact (Finset.mem_filter.mp hEdge).2

/-- The slots above a target occurrence are the source occurrences above it. -/
theorem card_fibreSlots_eq_card_filter (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization) :
    (fibreSlots data realization contracted).card
      = (Finset.univ.filter fun edge : data.SourceEdge ↦
          edge.1.1 = contracted).card := by
  refine Finset.card_bij'
    (fun slot _ ↦ realization.sourceEdgeAt slot)
    (fun edge _ ↦ slotOf data realization edge)
    (fun slot hSlot ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (mem_fibreSlots data realization contracted slot).mp hSlot⟩)
    (fun edge hEdge ↦ ?_)
    (fun slot _ ↦ slotOf_sourceEdgeAt data realization slot)
    (fun edge _ ↦ sourceEdgeAt_slotOf data realization edge)
  rw [mem_fibreSlots, sourceEdgeAt_slotOf]
  exact (Finset.mem_filter.mp hEdge).2

/-- The surviving zero occurrences downstairs are the zero occurrences upstairs
away from the contracted target occurrence. -/
theorem card_filter_sourceLength_eq_zero_contractDatum
    (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) :
    (Finset.univ.filter fun edge : data.SourceEdge ↦
        realization.sourceLength edge = 0 ∧ edge.1.1 ≠ contracted).card
      = (Finset.univ.filter fun edge : (contractDatum data hc hab hOne).SourceEdge ↦
          (contractRealization data realization hc hab hOne).sourceLength edge = 0).card := by
  refine Finset.card_bij'
    (fun edge hEdge ↦
      sourceEdgeMap data hc hab hOne ⟨edge, (Finset.mem_filter.mp hEdge).2.2⟩)
    (fun edge _ ↦ unfoldSourceEdge data hc hab hOne edge)
    (fun edge hEdge ↦ ?_) (fun edge hEdge ↦ ?_)
    (fun edge hEdge ↦ unfoldSourceEdge_sourceEdgeMap data hc hab hOne
      ⟨edge, (Finset.mem_filter.mp hEdge).2.2⟩)
    (fun edge _ ↦ Subtype.ext (Prod.ext
      (foldEdge_unfoldEdge hc hab hOne edge.1.1
        (unfoldEdge_ne_contracted hc hab hOne edge.1.1)) rfl))
  · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [contractRealization_sourceLength_sourceEdgeMap]
    exact (Finset.mem_filter.mp hEdge).2.1
  · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · have hLength := (Finset.mem_filter.mp hEdge).2
      rwa [contractRealization_sourceLength] at hLength
    · exact unfoldEdge_ne_contracted hc hab hOne edge.1.1

/-- **The occurrence half of the count.**  Contracting a zero-length target
occurrence removes from the zero set exactly the source occurrences above it. -/
theorem card_sourceZeroSet_contractDatum (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hZero : realization.targetLength contracted = 0) :
    (contractRealization data realization hc hab hOne).sourceZeroSet.card
        + (fibreSlots data realization contracted).card
      = realization.sourceZeroSet.card := by
  classical
  have hAbove : ∀ edge : data.SourceEdge, edge.1.1 = contracted →
      realization.sourceLength edge = 0 :=
    fun edge hEdge ↦ sourceLength_eq_zero_of_targetLength_eq_zero data realization
      hZero edge hEdge
  have hDisjoint : Disjoint
      (Finset.univ.filter fun edge : data.SourceEdge ↦
        realization.sourceLength edge = 0 ∧ edge.1.1 = contracted)
      (Finset.univ.filter fun edge : data.SourceEdge ↦
        realization.sourceLength edge = 0 ∧ edge.1.1 ≠ contracted) := by
    refine Finset.disjoint_left.mpr ?_
    intro edge hLeft hRight
    exact (Finset.mem_filter.mp hRight).2.2 (Finset.mem_filter.mp hLeft).2.2
  have hUnion : (Finset.univ.filter fun edge : data.SourceEdge ↦
        realization.sourceLength edge = 0)
      = (Finset.univ.filter fun edge : data.SourceEdge ↦
          realization.sourceLength edge = 0 ∧ edge.1.1 = contracted)
        ∪ Finset.univ.filter fun edge : data.SourceEdge ↦
          realization.sourceLength edge = 0 ∧ edge.1.1 ≠ contracted := by
    ext edge
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hEdge : edge.1.1 = contracted <;> tauto
  have hSplit : (Finset.univ.filter fun edge : data.SourceEdge ↦
          realization.sourceLength edge = 0 ∧ edge.1.1 = contracted).card
        + (Finset.univ.filter fun edge : data.SourceEdge ↦
          realization.sourceLength edge = 0 ∧ edge.1.1 ≠ contracted).card
      = (Finset.univ.filter fun edge : data.SourceEdge ↦
          realization.sourceLength edge = 0).card := by
    rw [hUnion, Finset.card_union_of_disjoint hDisjoint]
  have hZeroFibre :
      (Finset.univ.filter fun edge : data.SourceEdge ↦
          realization.sourceLength edge = 0 ∧ edge.1.1 = contracted)
        = Finset.univ.filter fun edge : data.SourceEdge ↦ edge.1.1 = contracted := by
    apply Finset.filter_congr
    intro edge _
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hAbove edge h, h⟩⟩
  rw [hZeroFibre] at hSplit
  rw [card_sourceZeroSet data realization,
    card_sourceZeroSet (contractDatum data hc hab hOne)
      (contractRealization data realization hc hab hOne),
    card_fibreSlots_eq_card_filter data realization,
    ← card_filter_sourceLength_eq_zero_contractDatum data realization hc hab hOne]
  omega

end OccurrenceCount

/-! ## The component count: contracting does not create components

The source vertex map is surjective, and it carries a zero source occurrence
either to a zero source occurrence downstairs (when the occurrence survives) or
to a collapsed pair of vertices (when it lies above the contracted occurrence).
So every component of the new zero set is the image of a component of the old
one. -/

section ComponentCount

open GraphContraction GluingContraction ContractionFibre IteratedContraction

attribute [local instance 0] Classical.propDecidable

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}

/-- The canonical label of the image of a quotient-source vertex under the
contraction. -/
noncomputable def contractedVertexLabel (data : GluingDatum target degree)
    {contracted : target.edges} (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (label : Fin (Fintype.card data.sourceGraph.V)) :
    Fin (Fintype.card (contractDatum data hc hab hOne).sourceGraph.V) :=
  (sourceVertexEquiv (contractDatum data hc hab hOne)).symm
    (sourceVertexMap data hc hab hOne (sourceVertexOf data label))

theorem sourceVertexOf_contractedVertexLabel (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (label : Fin (Fintype.card data.sourceGraph.V)) :
    sourceVertexOf (contractDatum data hc hab hOne)
        (contractedVertexLabel data hc hab hOne label)
      = sourceVertexMap data hc hab hOne (sourceVertexOf data label) :=
  (sourceVertexEquiv (contractDatum data hc hab hOne)).apply_symm_apply _

theorem contractedVertexLabel_surjective (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) :
    Function.Surjective (contractedVertexLabel data hc hab hOne) :=
  ((sourceVertexEquiv (contractDatum data hc hab hOne)).symm.surjective).comp
    ((sourceVertexMap_surjective data hc hab hOne).comp
      (sourceVertexEquiv data).surjective)

/-- A zero source occurrence is carried to a walk of zero source occurrences
downstairs: to a single step if it survives, and to nothing at all if it lies
above the contracted occurrence, where the two ends already agree. -/
theorem reflTransGen_slotStep_contractDatum_of_sourceLength_eq_zero
    (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) {edge : data.SourceEdge}
    (hLength : realization.sourceLength edge = 0) :
    Relation.ReflTransGen
      (SlotStep (contractDatum data hc hab hOne)
        (contractRealization data realization hc hab hOne)
        (contractRealization data realization hc hab hOne).sourceZeroSet)
      (sourceVertexMap data hc hab hOne (data.sourceEnds edge).1)
      (sourceVertexMap data hc hab hOne (data.sourceEnds edge).2) := by
  by_cases hAbove : edge.1.1 = contracted
  · rw [sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hOne edge hAbove]
  · have hImage := sourceEnds_sourceEdgeMap data hc hab hOne ⟨edge, hAbove⟩
    have hMember : slotOf (contractDatum data hc hab hOne)
        (contractRealization data realization hc hab hOne)
        (sourceEdgeMap data hc hab hOne ⟨edge, hAbove⟩)
          ∈ (contractRealization data realization hc hab hOne).sourceZeroSet := by
      rw [GluingDatum.NonnegativeIntegralRealization.mem_sourceZeroSet,
        sourceEdgeAt_slotOf, contractRealization_sourceLength_sourceEdgeMap]
      exact hLength
    have hStep := slotStep_of_sourceEdge (contractDatum data hc hab hOne)
      (contractRealization data realization hc hab hOne) hMember
    rw [hImage] at hStep
    exact Relation.ReflTransGen.single hStep

/-- One step of the old zero walk becomes a walk of the new zero walk. -/
theorem reflTransGen_slotStep_contractDatum_of_slotStep
    (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) {x y : data.SourceVertex}
    (h : SlotStep data realization realization.sourceZeroSet x y) :
    Relation.ReflTransGen
      (SlotStep (contractDatum data hc hab hOne)
        (contractRealization data realization hc hab hOne)
        (contractRealization data realization hc hab hOne).sourceZeroSet)
      (sourceVertexMap data hc hab hOne x) (sourceVertexMap data hc hab hOne y) := by
  obtain ⟨slot, hSlot, hEnds⟩ := h
  have hLength : realization.sourceLength (realization.sourceEdgeAt slot) = 0 :=
    (GluingDatum.NonnegativeIntegralRealization.mem_sourceZeroSet
      realization slot).mp hSlot
  have hWalk := reflTransGen_slotStep_contractDatum_of_sourceLength_eq_zero
    data realization hc hab hOne hLength
  rcases hEnds with ⟨hFirst, hSecond⟩ | ⟨hSecond, hFirst⟩
  · rw [hFirst, hSecond] at hWalk
    exact hWalk
  · rw [hFirst, hSecond] at hWalk
    exact reflTransGen_slotStep_symm _ _ hWalk

/-- The whole old zero walk becomes a new zero walk. -/
theorem reflTransGen_slotStep_contractDatum (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) {x y : data.SourceVertex}
    (h : Relation.ReflTransGen (SlotStep data realization realization.sourceZeroSet) x y) :
    Relation.ReflTransGen
      (SlotStep (contractDatum data hc hab hOne)
        (contractRealization data realization hc hab hOne)
        (contractRealization data realization hc hab hOne).sourceZeroSet)
      (sourceVertexMap data hc hab hOne x) (sourceVertexMap data hc hab hOne y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hLast ih =>
    exact ih.trans (reflTransGen_slotStep_contractDatum_of_slotStep data realization
      hc hab hOne hLast)

/-- The new zero-component map factors through the old one. -/
theorem compFold_contractDatum_of_compFold_eq (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    {x y : Fin (Fintype.card data.sourceGraph.V)}
    (h : compFold (UnitSubdivisionPresentation.core data.sourceGraph)
      realization.sourceZeroSet x
        = compFold (UnitSubdivisionPresentation.core data.sourceGraph)
          realization.sourceZeroSet y) :
    compFold (UnitSubdivisionPresentation.core
          (contractDatum data hc hab hOne).sourceGraph)
        (contractRealization data realization hc hab hOne).sourceZeroSet
        (contractedVertexLabel data hc hab hOne x)
      = compFold (UnitSubdivisionPresentation.core
          (contractDatum data hc hab hOne).sourceGraph)
        (contractRealization data realization hc hab hOne).sourceZeroSet
        (contractedVertexLabel data hc hab hOne y) := by
  refine (compFold_iff _ _ _ _).mpr ?_
  refine (reachIn_iff_reflTransGen_slotStep (contractDatum data hc hab hOne)
    (contractRealization data realization hc hab hOne) _ _ _).mpr ?_
  rw [sourceVertexOf_contractedVertexLabel, sourceVertexOf_contractedVertexLabel]
  refine reflTransGen_slotStep_contractDatum data realization hc hab hOne ?_
  exact (reachIn_iff_reflTransGen_slotStep data realization
    realization.sourceZeroSet x y).mp ((compFold_iff _ _ x y).mp h)

/-- **The component half of the count.**  Contracting a target occurrence does
not increase the number of zero components. -/
theorem card_image_compFold_contractDatum_le (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) :
    (Finset.image
        (compFold (UnitSubdivisionPresentation.core
            (contractDatum data hc hab hOne).sourceGraph)
          (contractRealization data realization hc hab hOne).sourceZeroSet)
        Finset.univ).card
      ≤ (Finset.image
          (compFold (UnitSubdivisionPresentation.core data.sourceGraph)
            realization.sourceZeroSet) Finset.univ).card := by
  classical
  have hImage :
      Finset.image
          (compFold (UnitSubdivisionPresentation.core
              (contractDatum data hc hab hOne).sourceGraph)
            (contractRealization data realization hc hab hOne).sourceZeroSet)
          Finset.univ
        = Finset.image
          (fun label ↦ compFold (UnitSubdivisionPresentation.core
              (contractDatum data hc hab hOne).sourceGraph)
            (contractRealization data realization hc hab hOne).sourceZeroSet
            (contractedVertexLabel data hc hab hOne label)) Finset.univ := by
    rw [← Finset.image_univ_of_surjective
      (contractedVertexLabel_surjective data hc hab hOne), Finset.image_image]
    rfl
  rw [hImage]
  refine card_image_le_card_image_of_factors ?_
  intro label
  exact compFold_contractDatum_of_compFold_eq data realization hc hab hOne
    (compFold_idem (UnitSubdivisionPresentation.core data.sourceGraph)
      realization.sourceZeroSet label)

end ComponentCount

/-! ## Deliverable (1): one contraction preserves the census forest

The three halves are added to the starting receipt `C + F.card = n`.  Note that
`hZero` is genuinely needed: contracting a target occurrence of **positive**
length merges quotient-source vertices that a zero walk may already join, and
then the surviving zero set carries a cycle.  The smallest example is a target
path `u — c — v — g — w` of a degree-two datum whose source is a four-cycle
lying over it; with `g` of length zero and `c` of positive length the zero set
upstairs is a forest and its image downstairs is a pair of parallel zero
occurrences, which is not. -/

section OneStep

open GraphContraction GluingContraction ContractionFibre IteratedContraction

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}

/-- **Deliverable (1).**  If the zero set of a gluing datum's quotient source is
a census forest, then so is the zero set after contracting one **zero-length**
target occurrence. -/
theorem isForest_contractDatum (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hZero : realization.targetLength contracted = 0)
    (hForest : IsForest (UnitSubdivisionPresentation.core data.sourceGraph)
      realization.sourceZeroSet) :
    IsForest (UnitSubdivisionPresentation.core
        (contractDatum data hc hab hOne).sourceGraph)
      (contractRealization data realization hc hab hOne).sourceZeroSet := by
  have hLower := card_le_card_image_compFold_add_card
    (UnitSubdivisionPresentation.core (contractDatum data hc hab hOne).sourceGraph)
    (contractRealization data realization hc hab hOne).sourceZeroSet
  have hUpper := card_image_compFold_le
    (UnitSubdivisionPresentation.core (contractDatum data hc hab hOne).sourceGraph)
    (contractRealization data realization hc hab hOne).sourceZeroSet
  have hComponents := card_image_compFold_contractDatum_le data realization hc hab hOne
  have hOccurrences := card_sourceZeroSet_contractDatum data realization hc hab hOne hZero
  have hVertices := card_sourceVertex_contractDatum_ge data realization hc hab hOne
  have hOld := forest_image_add_card_eq
    (UnitSubdivisionPresentation.core data.sourceGraph) hForest
  unfold IsForest
  omega

/-- Deliverable (1) at a chosen target occurrence. -/
theorem isForest_contractDatumAt (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization) (edge : target.edges)
    (hOne : num_edges target (edge : target.V × target.V).1
      (edge : target.V × target.V).2 = 1)
    (hZero : realization.targetLength edge = 0)
    (hForest : IsForest (UnitSubdivisionPresentation.core data.sourceGraph)
      realization.sourceZeroSet) :
    IsForest (UnitSubdivisionPresentation.core
        (contractDatumAt data edge hOne).sourceGraph)
      (contractRealizationAt data realization edge hOne).sourceZeroSet :=
  isForest_contractDatum data realization rfl (fst_ne_snd edge) hOne hZero hForest

/-- Deliverable (1) for a stage of `IteratedContraction`. -/
theorem isForest_contractAt (s : Step.{u} degree) (edge : s.target.edges)
    (hOne : num_edges s.target (edge : s.target.V × s.target.V).1
      (edge : s.target.V × s.target.V).2 = 1)
    (hZero : s.realization.targetLength edge = 0)
    (hForest : IsForest (UnitSubdivisionPresentation.core s.data.sourceGraph)
      s.realization.sourceZeroSet) :
    IsForest (UnitSubdivisionPresentation.core (s.contractAt edge hOne).data.sourceGraph)
      (s.contractAt edge hOne).realization.sourceZeroSet :=
  isForest_contractDatumAt s.data s.realization edge hOne hZero hForest

end OneStep

/-! ## Deliverable (2): the iteration, and the terminal stage

The driver `IteratedContraction.exists_terminal_flagged` takes its "should be
contracted" flag as a **rule on stages**, not as a subset of the starting
target's occurrences.  That is what makes this section possible: the rule used
here is

```
zeroForestFlag r e :  r.realization.targetLength e = 0  ∧  IsForest (core …) …
```

so the driver's receipt hypothesis is handed the census forest of the stage it
is being applied at, and `ZeroForestBridge` discharges it outright.  The second
conjunct is then propagated along the resulting `ContractsFlaggedMany` by
deliverable (1), which is exactly the induction the bare `ContractsMany` form of
the hypothesis cannot support: preservation is **false** for a contraction of a
positive-length occurrence, and `ContractsMany` does not record that only
zero-length occurrences were contracted. -/

section Iteration

open GraphContraction GluingContraction ContractionRamification IteratedContraction

variable {degree : ℕ}

/-- Weakening the flag weakens the flagged iteration. -/
theorem contractsFlaggedMany_mono
    {flag flagWeak : ∀ r : Step.{u} degree, r.target.edges → Prop}
    (hMono : ∀ (r : Step.{u} degree) (e : r.target.edges), flag r e → flagWeak r e)
    {s t : Step.{u} degree} (h : ContractsFlaggedMany flag s t) :
    ContractsFlaggedMany flagWeak s t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hStep ih =>
    cases hStep with
    | contract edge hOne hReceipt hFlag =>
      exact ih.tail (ContractsFlagged.contract _ edge hOne hReceipt (hMono _ edge hFlag))

/-- The rule the driver is run with: contract an occurrence of length zero, at a
stage whose zero set is still a census forest. -/
def zeroForestFlag (r : Step.{u} degree) (e : r.target.edges) : Prop :=
  r.realization.targetLength e = 0 ∧
    IsForest (UnitSubdivisionPresentation.core r.data.sourceGraph)
      r.realization.sourceZeroSet

/-- **Deliverable (2), the induction.**  A census forest of the starting stage
stays a census forest along any sequence of zero-length contractions. -/
theorem isForest_of_contractsFlaggedMany {s t : Step.{u} degree}
    (h : ContractsFlaggedMany (fun r e ↦ r.realization.targetLength e = 0) s t)
    (hForest : IsForest (UnitSubdivisionPresentation.core s.data.sourceGraph)
      s.realization.sourceZeroSet) :
    IsForest (UnitSubdivisionPresentation.core t.data.sourceGraph)
      t.realization.sourceZeroSet := by
  induction h with
  | refl => exact hForest
  | tail _ hStep ih =>
    cases hStep with
    | contract edge hOne _ hFlag => exact isForest_contractAt _ edge hOne hFlag ih

/-- The same induction for the rule actually used by the driver below. -/
theorem isForest_of_contractsFlaggedMany_zeroForestFlag {s t : Step.{u} degree}
    (h : ContractsFlaggedMany zeroForestFlag s t)
    (hForest : IsForest (UnitSubdivisionPresentation.core s.data.sourceGraph)
      s.realization.sourceZeroSet) :
    IsForest (UnitSubdivisionPresentation.core t.data.sourceGraph)
      t.realization.sourceZeroSet := by
  induction h with
  | refl => exact hForest
  | tail _ hStep ih =>
    cases hStep with
    | contract edge hOne _ hFlag => exact isForest_contractAt _ edge hOne hFlag.1 ih

/-- The driver's receipt hypothesis for `zeroForestFlag`, discharged outright by
the census bridge: the flag carries the census forest of the very stage the
receipt is demanded at. -/
theorem contractionForestAt_of_zeroForestFlag (t : Step.{u} degree)
    (e : t.target.edges) (hFlag : zeroForestFlag t e) :
    ContractionForestAt t.data e :=
  contractionForest_of_isForest_of_targetLength_eq_zero
    t.data t.realization rfl hFlag.1 hFlag.2

/-- **Deliverable (2).**  The terminal conclusion of `IteratedContraction` with
the forest receipt demanded **only at the starting stage** — which is exactly
what the terminal face of Part I supplies.

`IteratedContraction.exists_terminal_positive` asks instead for
`ContractionForestAt t.data e` at every `ContractsMany`-reachable stage `t`;
that hypothesis is strictly stronger and is *not* a consequence of the starting
receipt (see the note before `isForest_contractDatum`).  Running the driver with
`zeroForestFlag` avoids it. -/
theorem exists_terminal_flagged_of_isForest (s : Step.{u} degree) (hValid : s.data.Valid)
    (hConnected : graph_connected s.target) (hGenus : genus s.target = 0)
    (hForest : IsForest (UnitSubdivisionPresentation.core s.data.sourceGraph)
      s.realization.sourceZeroSet) :
    ∃ final : Step.{u} degree,
      ContractsFlaggedMany (fun r e ↦ r.realization.targetLength e = 0) s final ∧
      (∀ e : final.target.edges, 0 < final.realization.targetLength e) ∧
      final.data.Valid ∧ graph_connected final.target ∧ genus final.target = 0 ∧
      IsForest (UnitSubdivisionPresentation.core final.data.sourceGraph)
        final.realization.sourceZeroSet := by
  obtain ⟨final, hReach, hNone, hValidFinal, hConnectedFinal, hGenusFinal⟩ :=
    exists_terminal_flagged zeroForestFlag s hValid hConnected hGenus
      (fun t _ _ _ _ e hFlag ↦ contractionForestAt_of_zeroForestFlag t e hFlag)
  have hForestFinal := isForest_of_contractsFlaggedMany_zeroForestFlag hReach hForest
  refine ⟨final, contractsFlaggedMany_mono (fun _ _ hFlag ↦ hFlag.1) hReach, ?_,
    hValidFinal, hConnectedFinal, hGenusFinal, hForestFinal⟩
  intro e
  exact Nat.pos_of_ne_zero fun hZeroLength ↦ hNone e ⟨hZeroLength, hForestFinal⟩

/-- **Deliverable (2), in the plain `ContractsMany` form.** -/
theorem exists_terminal_positive_of_isForest (s : Step.{u} degree) (hValid : s.data.Valid)
    (hConnected : graph_connected s.target) (hGenus : genus s.target = 0)
    (hForest : IsForest (UnitSubdivisionPresentation.core s.data.sourceGraph)
      s.realization.sourceZeroSet) :
    ∃ final : Step.{u} degree, ContractsMany s final ∧
      (∀ e : final.target.edges, 0 < final.realization.targetLength e) ∧
      final.data.Valid ∧ graph_connected final.target ∧ genus final.target = 0 ∧
      IsForest (UnitSubdivisionPresentation.core final.data.sourceGraph)
        final.realization.sourceZeroSet := by
  obtain ⟨final, hReach, hPositive, hValidFinal, hConnectedFinal, hGenusFinal,
    hForestFinal⟩ := exists_terminal_flagged_of_isForest s hValid hConnected hGenus hForest
  exact ⟨final, contractsMany_of_contractsFlaggedMany hReach, hPositive, hValidFinal,
    hConnectedFinal, hGenusFinal, hForestFinal⟩

/-- The terminal stage packaged with the positive `GluingDatum.IntegralRealization`
that `LocalCases.ClosedEndpoint.ContractedGluing` consumes, from the starting
census forest alone. -/
theorem exists_terminal_integralRealization_of_isForest (s : Step.{u} degree)
    (hValid : s.data.Valid) (hConnected : graph_connected s.target)
    (hGenus : genus s.target = 0)
    (hForest : IsForest (UnitSubdivisionPresentation.core s.data.sourceGraph)
      s.realization.sourceZeroSet) :
    ∃ final : Step.{u} degree, ∃ positive : final.data.IntegralRealization,
      ContractsMany s final ∧
      (∀ e : final.target.edges,
        positive.targetLength e = final.realization.targetLength e) ∧
      (∀ e : final.data.SourceEdge,
        positive.sourceLength e = final.realization.sourceLength e) ∧
      final.data.Valid ∧ graph_connected final.target ∧ genus final.target = 0 ∧
      IsForest (UnitSubdivisionPresentation.core final.data.sourceGraph)
        final.realization.sourceZeroSet := by
  obtain ⟨final, hReach, hPositive, hValidFinal, hConnectedFinal, hGenusFinal,
    hForestFinal⟩ := exists_terminal_positive_of_isForest s hValid hConnected hGenus hForest
  exact ⟨final, final.integralRealization hPositive, hReach, fun _ ↦ rfl, fun _ ↦ rfl,
    hValidFinal, hConnectedFinal, hGenusFinal, hForestFinal⟩

end Iteration


/-! ## Deliverable (3): the identification `hZero`

`TerminalContraction.faceSourceEquivOfTerminal` — the `sourceEquiv` field of
`Candidate.ClearedFace.ContractedGluing` — consumes, besides a
`SourceCorrespondence`, the identification

```
hZero : ∀ e : s.data.SourceEdge, s.realization.sourceLength e = 0 ↔ e.1.1 ∈ sc.contracted
```

"the source occurrences that vanish are exactly those above the occurrences that
were contracted".  One direction is conjunct (6) of `SourceCorrespondence` plus
positivity of the terminal stage.  The other needs to know that only zero-length
occurrences were contracted, which `SourceCorrespondence` does not record; it is
supplied here by re-running the `IteratedContractionSource` induction along
`ContractsFlaggedMany` and carrying that fact.

The one input the induction needs and `FullCorrespondence` does not carry is
that its **target** occurrence bijection preserves target lengths.  That is not
an extra hypothesis: it follows from conjuncts (4) and (6) and the dilation
equation, as soon as the sheet degree is positive. -/

section Identification

open GraphContraction GluingContraction IteratedContraction IteratedContractionSource

variable {degree : ℕ}

/-- **Target lengths are preserved by the composed target occurrence
bijection.**  Read a surviving target occurrence through any one sheet: the
source occurrence over it keeps its length (conjunct (6)) and its dilation index
(conjunct (4)), so the dilation equation gives the same target length on both
sides. -/
theorem targetLength_targetMap {s t : Step.{u} degree} (sc : FullCorrespondence s t)
    (sheet : Fin degree) (f : {f : s.target.edges // f ∉ sc.contracted}) :
    t.realization.targetLength (sc.targetMap f) = s.realization.targetLength f.1 := by
  have hMember : (s.data.sourceEdge f.1 sheet).1.1 ∉ sc.contracted := f.2
  have hFst : (sc.edgeMap ⟨s.data.sourceEdge f.1 sheet, hMember⟩).1.1 = sc.targetMap f := by
    rw [sc.edgeMap_fst ⟨s.data.sourceEdge f.1 sheet, hMember⟩]
    exact congrArg sc.targetMap (Subtype.ext rfl)
  have hSource :=
    s.realization.dilation_length (s.data.sourceEdge f.1 sheet)
  have hTarget :=
    t.realization.dilation_length (sc.edgeMap ⟨s.data.sourceEdge f.1 sheet, hMember⟩)
  rw [sc.sourceEdgeIndex_edgeMap ⟨s.data.sourceEdge f.1 sheet, hMember⟩,
    sc.sourceLength_edgeMap ⟨s.data.sourceEdge f.1 sheet, hMember⟩, hFst] at hTarget
  rw [← hTarget, hSource]
  rfl

/-- **The composed correspondence, with the contracted set pinned down.**  Along
a sequence of zero-length contractions the set of starting-target occurrences
recorded by the correspondence consists of zero-length occurrences only. -/
theorem exists_fullCorrespondence_contracted_zero {s t : Step.{u} degree}
    (sheet : Fin degree)
    (h : ContractsFlaggedMany (fun r e ↦ r.realization.targetLength e = 0) s t) :
    ∃ sc : FullCorrespondence s t,
      ∀ f ∈ sc.contracted, s.realization.targetLength f = 0 := by
  induction h with
  | refl => exact ⟨reflCorrespondence s, fun f hf ↦ absurd hf (Finset.notMem_empty f)⟩
  | tail _ hStep ih =>
    obtain ⟨sc, hContracted⟩ := ih
    cases hStep with
    | contract edge hOne _ hFlag =>
      refine ⟨stepCorrespondence sc edge hOne, ?_⟩
      intro f hf
      rcases (mem_nextContracted_iff sc edge f).mp hf with hNew | hOld
      · have hTarget := targetLength_targetMap sc sheet (sc.targetMap.symm edge)
        rw [Equiv.apply_symm_apply] at hTarget
        rw [hNew]
        exact hTarget.symm.trans hFlag
      · exact hContracted f hOld

/-- **The identification `hZero`.**  At a terminal stage of a sequence of
zero-length contractions there is a source correspondence whose contracted set
is exactly the set of target occurrences carrying the vanishing source
occurrences. -/
theorem exists_sourceCorrespondence_zero {s t : Step.{u} degree}
    (h : ContractsFlaggedMany (fun r e ↦ r.realization.targetLength e = 0) s t)
    (hPositive : ∀ e : t.target.edges, 0 < t.realization.targetLength e) :
    ∃ sc : SourceCorrespondence s t,
      ∀ e : s.data.SourceEdge,
        s.realization.sourceLength e = 0 ↔ e.1.1 ∈ sc.contracted := by
  rcases Nat.eq_zero_or_pos degree with hDegree | hDegree
  · obtain ⟨sc⟩ := nonempty_sourceCorrespondence (contractsMany_of_contractsFlaggedMany h)
    exact ⟨sc, fun e ↦ absurd e.1.2.isLt (by omega)⟩
  · obtain ⟨sc, hContracted⟩ :=
      exists_fullCorrespondence_contracted_zero ⟨0, hDegree⟩ h
    refine ⟨sc.toSourceCorrespondence, fun e ↦ ⟨?_, ?_⟩⟩
    · intro hLength
      by_contra hMember
      have hCarried := sc.sourceLength_edgeMap ⟨e, hMember⟩
      have hDilation := t.realization.dilation_length (sc.edgeMap ⟨e, hMember⟩)
      have hTargetPos := hPositive (sc.edgeMap ⟨e, hMember⟩).1.1
      rw [hCarried, hLength, Nat.mul_zero] at hDilation
      omega
    · intro hMember
      exact sourceLength_eq_zero_of_targetLength_eq_zero s.data s.realization
        (hContracted e.1.1 hMember) e rfl

/-- **Deliverable (3), at the `Step` level.**  Everything
`Candidate.ClearedFace.ContractedGluing` needs, from the terminal face's single
census-forest receipt: a terminal stage with positive lengths, still valid over
a connected genus-zero target, a source correspondence to it, and the
identification `hZero` that
`TerminalContraction.faceSourceEquivOfTerminal` consumes.

Assembling the structure itself is one `where` block in a file that may import
`DraismaVargas.LocalCases.ClosedEndpoint`; this file deliberately does not, so
that it sits below the terminal-face layer. -/
theorem exists_terminal_sourceCorrespondence (s : Step.{u} degree) (hValid : s.data.Valid)
    (hConnected : graph_connected s.target) (hGenus : genus s.target = 0)
    (hForest : IsForest (UnitSubdivisionPresentation.core s.data.sourceGraph)
      s.realization.sourceZeroSet) :
    ∃ (final : Step.{u} degree) (sc : SourceCorrespondence s final),
      ContractsMany s final ∧
      (∀ e : final.target.edges, 0 < final.realization.targetLength e) ∧
      (∀ e : s.data.SourceEdge,
        s.realization.sourceLength e = 0 ↔ e.1.1 ∈ sc.contracted) ∧
      final.data.Valid ∧ graph_connected final.target ∧ genus final.target = 0 ∧
      IsForest (UnitSubdivisionPresentation.core final.data.sourceGraph)
        final.realization.sourceZeroSet := by
  obtain ⟨final, hReach, hPositive, hValidFinal, hConnectedFinal, hGenusFinal,
    hForestFinal⟩ := exists_terminal_flagged_of_isForest s hValid hConnected hGenus hForest
  obtain ⟨sc, hZero⟩ := exists_sourceCorrespondence_zero hReach hPositive
  exact ⟨final, sc, contractsMany_of_contractsFlaggedMany hReach, hPositive, hZero,
    hValidFinal, hConnectedFinal, hGenusFinal, hForestFinal⟩

end Identification

end DraismaVargas.LocalCases.ZeroForestPreservation
