import DraismaVargas.LocalCases.PrunedContractedSpec
import DraismaVargas.LocalCases.PrunedRealizationResidues

/-!
# The two named facts of the pruned contracted spec, proved

`PrunedContractedSpec` leaves two facts about dangling
occurrences named rather than proved, because neither is a statement about its
own construction:

* `PendantSeparated` — a dangling positive slot has an endpoint class that
  pruning discards;
* the count `classCard + keptSlotCard = keptClassCard + slotCard`, equivalently
  #(discarded classes) = #(dangling positive slots), which
  `genus_prunedSpec_eq_genus_sourceGraph_iff` shows is the genus identity
  itself.

`DanglingSideStructure` proves the structure theorem both rest on.
`PrunedRealizationResidues` applies it, on the pair
`(candidate.datum, face.realization)` alone; this module is the **thin
wrapper** that states the result at the cleared-face names, through the
adapter `SourceContractionTopology.toSourceTopology` of `PrunedContractedSpec`.

## What each fact costs

`pendantSeparated` needs **nothing beyond `SourceContractionTopology`**: the
chosen far side of a dangling occurrence of positive cleared length contains
the whole contraction class of its inner endpoint
(`DanglingSideStructure.mem_side_of_reachIn`), and every vertex of that side
has non-dangling valency zero
(`DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side`), so that class
is discarded.  The `forest` and `notLoopy` fields enter only because
`topology.degSpec` — and hence `classOf` — is defined from them.

The count needs two further inputs, and **one of them is not carried by
`PrunedContractedSpec`**:

* `hKept : (keptClasses topology).Nonempty` — already carried by every
  statement about `prunedSpec`, and genuinely necessary: if the quotient
  source is a tree then every occurrence dangles, `keptClasses` is empty, and
  the count reads `classCard = slotCard`, which is false by one for a tree.
* `hConnected : candidate.datum.Connected` — **not** carried by
  `PrunedContractedSpec`, and genuinely necessary.  Without it the count is
  false: let the quotient source be a triangle together with an isolated
  vertex (a target vertex of degree zero gives one), at strictly positive
  cleared lengths.  Then `sourceZeroSet = ∅`, so `forest` and `notLoopy`
  hold, `classCard = 4`, `slotCard = 3`; no occurrence is dangling, by
  `DanglingSideStructure.not_isDangling_of_not_graph_connected` (a
  `DanglingSide` has connected side, connected complement and an occurrence
  between them, so it forces the ambient graph connected); hence
  `keptSlotCard = 3` and `keptClassCard = 3` — the isolated vertex's class has
  non-dangling valency zero — and `4 + 3 ≠ 3 + 3`.  Source connectivity is the
  cheapest repair, it is what `GluingDatum.Valid` already asserts, and it also
  discharges `bnExists_prunedSpec`'s own `hConnected` hypothesis
  (`graph_connected_contractedSpec_of_connected`), so the primed corollaries
  below take strictly less input than the unprimed ones.

## The bijection

`droppedClass` sends a dropped positive slot to the contraction class of the
inner endpoint of its chosen far side.  It lands among the discarded classes
(`droppedClass_not_mem_keptClasses`); it is injective because two distinct dangling
occurrences whose far sides share a class would have their two sides cover the
whole quotient source (`DanglingSideStructure.false_of_inner_mem_side`); and it
is surjective because a discarded class none of whose occurrences points
*into* it would, with the far sides hanging off it, be a union of
non-surviving vertices closed under adjacency, hence everything
(`exists_dropped_of_not_keptClass`).

`bnExists_prunedSpec_of_refinement'` is the one declaration here with no
counterpart in `PrunedRealizationResidues`: it consumes §5b of
`PrunedContractedSpec`, which has no analogue on the realization side.
-/

namespace DraismaVargas.LocalCases.BalancedGlobal.Candidate.ClearedFace.SourceContractionTopology

open Utilities
open Utilities.Certificate
open Utilities.Certificate.DegenerateSpec
open Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.ContractionForestCensusGeneral
open Utilities.Certificate.IteratedSplitRefinement
open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.TerminalContraction
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.DanglingDescent
open DraismaVargas.LocalCases.DanglingSideStructure

variable {target : CFGraph} {degree : ℕ}
  {data : GluingDatum target degree} {wall : target.V}
  {candidate : Candidate target degree data wall}
  {coordinate : Type*}
  {presentation : candidate.datum.LengthMatrixPresentation coordinate}
  {coordinates : coordinate → ℚ}
  {face : ClearedFace candidate presentation coordinates}

/-! ## 1.  A contraction class is a chain of zero-length occurrences -/

/-- The representative map of `degSpec` is the union-find fold over the zero
occurrences (`TerminalContraction.sourceDegSpec_rep`, specialised). -/
theorem degSpec_rep_eq (topology : SourceContractionTopology face)
    (v : Fin (Fintype.card candidate.datum.sourceGraph.V)) :
    topology.degSpec.rep v =
      compFold (UnitSubdivisionPresentation.core candidate.datum.sourceGraph)
        face.realization.sourceZeroSet v :=
  PrunedRealizationSpec.degSpec_rep_eq topology.toSourceTopology v

/-- **Two quotient-source vertices share a contraction class exactly when a
chain of zero-length occurrences joins them.** -/
theorem classOf_eq_iff (topology : SourceContractionTopology face)
    (u v : candidate.datum.SourceVertex) :
    classOf topology u = classOf topology v ↔
      ReachIn (UnitSubdivisionPresentation.core candidate.datum.sourceGraph)
        face.realization.sourceZeroSet
        (vertexIndex candidate.datum u) (vertexIndex candidate.datum v) :=
  PrunedRealizationSpec.classOf_eq_iff topology.toSourceTopology u v

/-- A zero-length occurrence joins the two classes of its endpoints. -/
theorem classOf_eq_of_sourceLength_zero (topology : SourceContractionTopology face)
    {edge : candidate.datum.SourceEdge}
    (hZero : face.realization.sourceLength edge = 0) :
    classOf topology (candidate.datum.sourceEnds edge).1 =
      classOf topology (candidate.datum.sourceEnds edge).2 :=
  PrunedRealizationSpec.classOf_eq_of_sourceLength_zero topology.toSourceTopology hZero

/-! ## 2.  The class of the inner endpoint never escapes the far side -/

/-- **The escape theorem.**  A quotient-source vertex in the contraction class
of the inner endpoint of a dangling cut whose cut occurrence has positive
cleared length lies on the cut's side. -/
theorem mem_side_of_classOf_eq (topology : SourceContractionTopology face)
    {inner outer : candidate.datum.SourceVertex}
    (cut : DanglingSide candidate.datum.sourceGraph inner outer)
    {edge : candidate.datum.SourceEdge}
    (hEnds : candidate.datum.sourceEnds edge = (inner, outer) ∨
      candidate.datum.sourceEnds edge = (outer, inner))
    (hPos : 0 < face.realization.sourceLength edge)
    {u : candidate.datum.SourceVertex}
    (hu : classOf topology u = classOf topology inner) : u ∈ cut.side :=
  PrunedRealizationSpec.mem_side_of_classOf_eq topology.toSourceTopology cut hEnds hPos hu

/-- **The far class is discarded.**  The contraction class of the inner
endpoint of a dangling occurrence of positive cleared length contains no
surviving vertex. -/
theorem not_keptClass_inner (topology : SourceContractionTopology face)
    {edge : candidate.datum.SourceEdge}
    (hPos : 0 < face.realization.sourceLength edge)
    (item : DanglingData candidate.datum edge) :
    ¬ KeptClass topology (classOf topology item.inner) :=
  PrunedRealizationSpec.not_keptClass_inner topology.toSourceTopology hPos item

/-! ## 3.  The first fact: `PendantSeparated` -/

/-- **`PendantSeparated`, proved.**  A dangling positive slot has an endpoint
class that pruning discards — namely the class of the inner endpoint of its far
side.  The only hypotheses are the two fields of `SourceContractionTopology`,
and they enter only through `classOf`. -/
theorem pendantSeparated (topology : SourceContractionTopology face) :
    PendantSeparated topology :=
  PrunedRealizationSpec.pendantSeparated topology.toSourceTopology

/-! ## 4.  The far class of a dropped slot -/

/-- A slot that pruning drops carries a dangling occurrence. -/
theorem isDangling_of_not_mem_keptSlots (topology : SourceContractionTopology face)
    {e' : Fin topology.degSpec.slotCard} (he' : e' ∉ keptSlots topology) :
    IsDangling candidate.datum (face.realization.sourceEdgeAt
      (topology.degSpec.slotIndex.symm e').val) :=
  PrunedRealizationSpec.isDangling_of_not_mem_keptSlots topology.toSourceTopology he'

/-- Its cleared length is positive: it is a slot of `degSpec`. -/
theorem sourceLength_pos_of_slot (topology : SourceContractionTopology face)
    (e' : Fin topology.degSpec.slotCard) :
    0 < face.realization.sourceLength
      (face.realization.sourceEdgeAt (topology.degSpec.slotIndex.symm e').val) :=
  (topology.degSpec.slotIndex.symm e').property

/-- The chosen far side of a dropped slot. -/
noncomputable def droppedData (topology : SourceContractionTopology face)
    {e' : Fin topology.degSpec.slotCard} (he' : e' ∉ keptSlots topology) :
    DanglingData candidate.datum (face.realization.sourceEdgeAt
      (topology.degSpec.slotIndex.symm e').val) :=
  PrunedRealizationSpec.droppedData topology.toSourceTopology he'

/-- **The discarded class of a dropped slot**: the class of the inner endpoint
of its far side. -/
noncomputable def droppedClass (topology : SourceContractionTopology face)
    {e' : Fin topology.degSpec.slotCard} (he' : e' ∉ keptSlots topology) :
    Fin topology.degSpec.classCard :=
  PrunedRealizationSpec.droppedClass topology.toSourceTopology he'

theorem droppedClass_not_mem_keptClasses (topology : SourceContractionTopology face)
    {e' : Fin topology.degSpec.slotCard} (he' : e' ∉ keptSlots topology) :
    droppedClass topology he' ∉ keptClasses topology :=
  PrunedRealizationSpec.droppedClass_not_mem_keptClasses topology.toSourceTopology he'

/-- A nonempty set of kept classes produces a surviving quotient-source
vertex. -/
theorem exists_survivor (topology : SourceContractionTopology face)
    (hKept : (keptClasses topology).Nonempty) :
    ∃ v : candidate.datum.SourceVertex, 0 < nonDanglingValency candidate.datum v :=
  PrunedRealizationSpec.exists_survivor topology.toSourceTopology hKept

/-- **Injectivity.**  Distinct dropped slots have distinct discarded classes. -/
theorem droppedClass_injective (topology : SourceContractionTopology face)
    (hKept : (keptClasses topology).Nonempty)
    {e₁ e₂ : Fin topology.degSpec.slotCard}
    (h₁ : e₁ ∉ keptSlots topology) (h₂ : e₂ ∉ keptSlots topology)
    (hEq : droppedClass topology h₁ = droppedClass topology h₂) : e₁ = e₂ :=
  PrunedRealizationSpec.droppedClass_injective topology.toSourceTopology hKept h₁ h₂ hEq

/-! ## 5.  Surjectivity -/

/-- Any dangling occurrence of positive cleared length is a dropped slot, with
the same far class. -/
theorem exists_dropped_of_danglingData (topology : SourceContractionTopology face)
    {survivor : candidate.datum.SourceVertex}
    (hSurvivor : 0 < nonDanglingValency candidate.datum survivor)
    {edge : candidate.datum.SourceEdge}
    (hPos : 0 < face.realization.sourceLength edge)
    (item : DanglingData candidate.datum edge) :
    ∃ (e' : Fin topology.degSpec.slotCard) (he' : e' ∉ keptSlots topology),
      classOf topology (droppedData topology he').inner =
        classOf topology item.inner :=
  PrunedRealizationSpec.exists_dropped_of_danglingData topology.toSourceTopology
    hSurvivor hPos item

/-- **Surjectivity.**  A discarded class is the far class of a dropped slot.
If it were not, then the class together with the far sides hanging off it
would be closed under adjacency and carry no surviving vertex, so — the
quotient source being connected — nothing would survive at all. -/
theorem exists_dropped_of_not_keptClass (topology : SourceContractionTopology face)
    (hKept : (keptClasses topology).Nonempty)
    (hConnected : candidate.datum.Connected)
    {c : topology.degSpec.Class} (hc : ¬ KeptClass topology c) :
    ∃ (e' : Fin topology.degSpec.slotCard) (he' : e' ∉ keptSlots topology),
      classOf topology (droppedData topology he').inner = c :=
  PrunedRealizationSpec.exists_dropped_of_not_keptClass topology.toSourceTopology
    hKept hConnected hc

/-! ## 6.  The second fact: the count -/

/-- **The bijection.**  Discarded classes and dropped positive slots are
equinumerous. -/
theorem card_sdiff_keptSlots_eq_card_sdiff_keptClasses
    (topology : SourceContractionTopology face)
    (hKept : (keptClasses topology).Nonempty)
    (hConnected : candidate.datum.Connected) :
    (Finset.univ \ keptSlots topology).card =
      (Finset.univ \ keptClasses topology).card :=
  PrunedRealizationSpec.card_sdiff_keptSlots_eq_card_sdiff_keptClasses
    topology.toSourceTopology hKept hConnected

/-- **The count, proved.**  `#(discarded classes) = #(dangling positive
slots)`, in the subtraction-free form
`genus_prunedSpec_eq_genus_sourceGraph_iff` asks for. -/
theorem classCard_add_keptSlots_card (topology : SourceContractionTopology face)
    (hKept : (keptClasses topology).Nonempty)
    (hConnected : candidate.datum.Connected) :
    topology.degSpec.classCard + (keptSlots topology).card =
      (keptClasses topology).card + topology.degSpec.slotCard :=
  PrunedRealizationSpec.classCard_add_keptSlots_card topology.toSourceTopology
    hKept hConnected

/-! ## 7.  The corollaries, with both facts discharged -/

/-- Connectivity of the contracted spec is free from connectivity of the
quotient source: the canonical core is connected, the contraction carries that
to the contracted core, and a `Spec` with connected core has connected
graph. -/
theorem graph_connected_contractedSpec_of_connected
    (topology : SourceContractionTopology face)
    (hConnected : candidate.datum.Connected) :
    graph_connected topology.contractedSpec.graph :=
  PrunedRealizationSpec.graph_connected_contractedSpec_of_connected
    topology.toSourceTopology hConnected

/-- **`prunedSpec_laplacianEquiv`, unconditional.** -/
noncomputable def prunedSpec_laplacianEquiv' (topology : SourceContractionTopology face)
    (hKept : (keptClasses topology).Nonempty) :
    LaplacianEquiv (prunedSpec topology hKept).graph
      (inducedSubgraph topology.contractedSpec.graph (prunedVertices topology)
        (PendantDeletion.Spec.keptVertices_nonempty hKept)) :=
  PrunedRealizationSpec.prunedSpec_laplacianEquiv' topology.toSourceTopology hKept

/-- **The Euler transport, unconditional** given source connectivity. -/
theorem genus_prunedSpec_eq_genus_sourceGraph'
    (topology : SourceContractionTopology face)
    (hKept : (keptClasses topology).Nonempty)
    (hConnected : candidate.datum.Connected) :
    genus (prunedSpec topology hKept).graph = genus candidate.datum.sourceGraph :=
  PrunedRealizationSpec.genus_prunedSpec_eq_genus_sourceGraph'
    topology.toSourceTopology hKept hConnected

/-- **The pendant-deletion pushforward, unconditional** given source
connectivity: no `PendantSeparated`, no count, no connectivity of the
contracted spec and no genus identity are asked of the caller. -/
theorem bnExists_prunedSpec' (topology : SourceContractionTopology face)
    (hKept : (keptClasses topology).Nonempty)
    (hConnected : candidate.datum.Connected)
    {divisorDegree : ℤ}
    (hBN : BNExists topology.contractedSpec.graph 1 divisorDegree) :
    BNExists (prunedSpec topology hKept).graph 1 divisorDegree :=
  PrunedRealizationSpec.bnExists_prunedSpec' topology.toSourceTopology hKept
    hConnected hBN

/-- and the refinement-driven form, which does not even need the count: the
genus identity comes from the presentation.  This is the one declaration of
this module with no counterpart in `PrunedRealizationResidues`: §5b of
`PrunedContractedSpec` has no analogue in `PrunedRealizationSpec`. -/
theorem bnExists_prunedSpec_of_refinement'
    (topology : SourceContractionTopology face)
    (hKept : (keptClasses topology).Nonempty)
    (hConnected : candidate.datum.Connected)
    {source : PackedSpec}
    (refinement : RefinementPresentation source (prunedSpec topology hKept).graph)
    (hSource : genus source.graph = genus candidate.datum.sourceGraph)
    {divisorDegree : ℤ}
    (hBN : BNExists topology.contractedSpec.graph 1 divisorDegree) :
    BNExists (prunedSpec topology hKept).graph 1 divisorDegree :=
  bnExists_prunedSpec_of_refinement topology hKept (pendantSeparated topology)
    (graph_connected_contractedSpec_of_connected topology hConnected)
    refinement hSource hBN

end DraismaVargas.LocalCases.BalancedGlobal.Candidate.ClearedFace.SourceContractionTopology
