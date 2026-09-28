import Utilities.Foundations.PendantDeletion
import DraismaVargas.LocalCases.TerminalContraction
import DraismaVargas.LocalCases.NonDanglingValency

/-!
# The pruned contracted spec of a nonnegative integral realization

`DraismaVargas.LocalCases.PrunedContractedSpec` builds the *pendant-pruned*
contracted quotient source of a `ClearedFace` of a global candidate: the
contracted source with the dangling occurrences and the classes they hang from
removed, identified with an induced subgraph of the contracted source so that
the pushforward of `Infrastructure.PendantDeletion` applies.

Everything it does depends on the cleared face only through the pair
`(data, realization)` — the gluing datum and the nonnegative integral
realization.  A caller may have such a pair with no `Candidate`, no `wall` and
therefore no `ClearedFace`; this module is the same construction stated on the
pair alone.

`SourceTopology data realization` is the two-field receipt that
`ClosedFaceRealization.SourceContractionTopology face` is: the zero occurrences
form a forest and are not loopy.  Every declaration below is the corresponding
declaration of `PrunedContractedSpec` with `candidate.datum` replaced by
`data` and `face.realization` by `realization`.

## What is proved here

* `KeptSlot`, `KeptClass`, `keptSlots`, `keptClasses` — the surviving positive
  slots (non-dangling occurrences) and the surviving contraction classes
  (those meeting a surviving occurrence).
* `keptClass_tail_of_keptSlot`, `keptClass_head_of_keptSlot` — the free half
  of the separation: a kept slot has two kept endpoint classes.
* `prunedSpec` — `contractedSpec` restricted to the kept classes and kept
  slots, via `Infrastructure.PendantDeletion.Spec.restrict`.
* `prunedSpec_laplacianEquiv` — its identification with the induced subgraph of
  `contractedSpec.graph` on the kept vertices, under `PendantSeparated`.
* `genus_prunedSpec`, `genus_prunedSpec_eq_genus_sourceGraph_iff` — the Euler
  transport, and the fact that the genus identity *is* the count "discarded
  classes = dangling positive slots".
* `bnExists_prunedSpec`, `bnExists_prunedSpec_of_count` — the pendant-deletion
  pushforward, specialised.

## What is NOT proved here

`PendantSeparated` and the count
`classCard + keptSlotCard = keptClassCard + slotCard` are **named hypotheses**,
exactly as in `PrunedContractedSpec`; they are discharged, for a
`SourceTopology`, in `DraismaVargas.LocalCases.PrunedRealizationResidues`.
`bnExists_prunedSpec` additionally takes connectivity of
`contractedSpec.graph` as a hypothesis.  Nothing here is about a point map, a
metric realization of a request, surjectivity, or the rank of a *chosen*
divisor: the pushforward transported is `BNExists`, which is existential.

## Relation to `PrunedContractedSpec`

`PrunedContractedSpec` imports this module. Its `SourceContractionTopology face`
yields `SourceTopology candidate.datum face.realization` by
`⟨topology.forest, topology.notLoopy⟩`, and its declarations are thin wrappers
over the ones here.
-/

namespace DraismaVargas.LocalCases.PrunedRealizationSpec

open Utilities
open Utilities.Certificate
open Utilities.Certificate.DegenerateSpec
open Utilities.Certificate.SubdivisionGraph
open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.TerminalContraction
open DraismaVargas.LocalCases.W4StableSource

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}

/-- The two-field receipt that the zero-length occurrences of a nonnegative
integral realization contract a genus-preserving forest: exactly the content of
`BalancedGlobal.Candidate.ClearedFace.SourceContractionTopology`, stated on the
realization alone. -/
structure SourceTopology (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization) : Prop where
  forest : Utilities.Certificate.ContractionForestCensusGeneral.IsForest
    (UnitSubdivisionPresentation.core data.sourceGraph) realization.sourceZeroSet
  notLoopy : ¬ Utilities.Certificate.ContractionForestCensusGeneral.IsLoopy
    (UnitSubdivisionPresentation.core data.sourceGraph) realization.sourceZeroSet

namespace SourceTopology

variable {realization : data.NonnegativeIntegralRealization}

/-- The canonical degenerate quotient-source subdivision. -/
noncomputable def degSpec (topology : SourceTopology data realization) :=
  realization.sourceDegSpec topology.forest topology.notLoopy

/-- Its canonical strictly positive contracted presentation. -/
noncomputable def contractedSpec (topology : SourceTopology data realization) :=
  topology.degSpec.contractedSpec

/-- The exact graph equivalence from the positive contracted presentation to
the degenerate quotient source. -/
noncomputable def laplacianEquiv (topology : SourceTopology data realization) :
    LaplacianEquiv topology.contractedSpec.graph topology.degSpec.graph :=
  topology.degSpec.canonicalContraction.laplacianEquiv

/-- Brill--Noether existence is identical on the two. -/
theorem bnExists_iff (topology : SourceTopology data realization)
    (rank divisorDegree : ℤ) :
    BNExists topology.contractedSpec.graph rank divisorDegree ↔
      BNExists topology.degSpec.graph rank divisorDegree :=
  topology.laplacianEquiv.bnExists_iff rank divisorDegree

end SourceTopology

variable {realization : data.NonnegativeIntegralRealization}

/-! ## 1.  Classes, kept slots and kept classes -/

/-- The contraction class of a core index of the quotient source. -/
noncomputable def classOfCore (topology : SourceTopology data realization)
    (v : Fin (Fintype.card data.sourceGraph.V)) : topology.degSpec.Class :=
  ⟨topology.degSpec.rep v, topology.degSpec.rep_idem v⟩

/-- The contraction class of a quotient-source vertex. -/
noncomputable def classOf (topology : SourceTopology data realization)
    (v : data.SourceVertex) : topology.degSpec.Class :=
  classOfCore topology (vertexIndex data v)

/-- **A positive slot that survives pruning**: its source occurrence is not
dangling. -/
def KeptSlot (topology : SourceTopology data realization)
    (e : topology.degSpec.PositiveSlot) : Prop :=
  ¬ IsDangling data (realization.sourceEdgeAt e.val)

/-- **A contraction class that survives pruning**: it contains a
quotient-source vertex meeting a surviving occurrence. -/
def KeptClass (topology : SourceTopology data realization)
    (c : topology.degSpec.Class) : Prop :=
  ∃ v : data.SourceVertex,
    classOf topology v = c ∧ 0 < nonDanglingValency data v

/-- The kept slots, as a subset of the slot indices of `contractedSpec`. -/
noncomputable def keptSlots (topology : SourceTopology data realization) :
    Finset (Fin topology.degSpec.slotCard) := by
  classical
  exact Finset.univ.filter fun e' ↦ KeptSlot topology (topology.degSpec.slotIndex.symm e')

/-- The kept classes, as a subset of the core indices of `contractedSpec`. -/
noncomputable def keptClasses (topology : SourceTopology data realization) :
    Finset (Fin topology.degSpec.classCard) := by
  classical
  exact Finset.univ.filter fun c' ↦ KeptClass topology (topology.degSpec.classIndex.symm c')

@[simp] theorem mem_keptSlots (topology : SourceTopology data realization)
    (e' : Fin topology.degSpec.slotCard) :
    e' ∈ keptSlots topology ↔ KeptSlot topology (topology.degSpec.slotIndex.symm e') := by
  classical
  simp only [keptSlots, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem mem_keptClasses (topology : SourceTopology data realization)
    (c' : Fin topology.degSpec.classCard) :
    c' ∈ keptClasses topology ↔
      KeptClass topology (topology.degSpec.classIndex.symm c') := by
  classical
  simp only [keptClasses, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_keptClasses_classIndex (topology : SourceTopology data realization)
    {c : topology.degSpec.Class} (hc : KeptClass topology c) :
    topology.degSpec.classIndex c ∈ keptClasses topology := by
  rw [mem_keptClasses, Equiv.symm_apply_apply]
  exact hc

/-! ## 2.  A non-dangling slot has two kept endpoint classes -/

/-- A source occurrence meeting a vertex, not dangling, forces positive
non-dangling valency there. -/
theorem nonDanglingValency_pos_of_incident
    {edge : data.SourceEdge} {v : data.SourceVertex}
    (hDangling : ¬ IsDangling data edge)
    (hIncident : Incident data edge v) :
    0 < nonDanglingValency data v := by
  classical
  refine Finset.card_pos.mpr ⟨edge, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hDangling, hIncident⟩

theorem classOf_sourceEnds_fst (topology : SourceTopology data realization)
    (slot : Fin data.sourceGraph.edges.card) :
    classOf topology (data.sourceEnds (realization.sourceEdgeAt slot)).1 =
      classOfCore topology (topology.degSpec.core.tail slot) := by
  have h : topology.degSpec.core.tail slot =
      vertexIndex data
        (data.sourceEnds (realization.sourceEdgeAt slot)).1 :=
    core_tail_eq realization slot
  rw [classOf, h]

theorem classOf_sourceEnds_snd (topology : SourceTopology data realization)
    (slot : Fin data.sourceGraph.edges.card) :
    classOf topology (data.sourceEnds (realization.sourceEdgeAt slot)).2 =
      classOfCore topology (topology.degSpec.core.head slot) := by
  have h : topology.degSpec.core.head slot =
      vertexIndex data
        (data.sourceEnds (realization.sourceEdgeAt slot)).2 :=
    core_head_eq realization slot
  rw [classOf, h]

/-- **Free half of the separation.**  The tail class of a kept slot is kept. -/
theorem keptClass_tail_of_keptSlot (topology : SourceTopology data realization)
    {e : topology.degSpec.PositiveSlot} (he : KeptSlot topology e) :
    KeptClass topology (classOfCore topology (topology.degSpec.core.tail e.val)) :=
  ⟨(data.sourceEnds (realization.sourceEdgeAt e.val)).1,
    classOf_sourceEnds_fst topology e.val,
    nonDanglingValency_pos_of_incident he (incident_left data _)⟩

/-- and so is the head class. -/
theorem keptClass_head_of_keptSlot (topology : SourceTopology data realization)
    {e : topology.degSpec.PositiveSlot} (he : KeptSlot topology e) :
    KeptClass topology (classOfCore topology (topology.degSpec.core.head e.val)) :=
  ⟨(data.sourceEnds (realization.sourceEdgeAt e.val)).2,
    classOf_sourceEnds_snd topology e.val,
    nonDanglingValency_pos_of_incident he (incident_right data _)⟩

/-! ## 3.  `contractedSpec` endpoints, read as classes -/

theorem contractedSpec_tail (topology : SourceTopology data realization)
    (e' : Fin topology.degSpec.slotCard) :
    topology.degSpec.classIndex.symm (topology.contractedSpec.core.tail e') =
      classOfCore topology
        (topology.degSpec.core.tail (topology.degSpec.slotIndex.symm e').val) := by
  show topology.degSpec.classIndex.symm (topology.degSpec.classIndex _) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem contractedSpec_head (topology : SourceTopology data realization)
    (e' : Fin topology.degSpec.slotCard) :
    topology.degSpec.classIndex.symm (topology.contractedSpec.core.head e') =
      classOfCore topology
        (topology.degSpec.core.head (topology.degSpec.slotIndex.symm e').val) := by
  show topology.degSpec.classIndex.symm (topology.degSpec.classIndex _) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem tail_mem_keptClasses (topology : SourceTopology data realization) :
    ∀ e' ∈ keptSlots topology,
      topology.contractedSpec.core.tail e' ∈ keptClasses topology := by
  intro e' he'
  rw [mem_keptSlots] at he'
  rw [mem_keptClasses, contractedSpec_tail]
  exact keptClass_tail_of_keptSlot topology he'

theorem head_mem_keptClasses (topology : SourceTopology data realization) :
    ∀ e' ∈ keptSlots topology,
      topology.contractedSpec.core.head e' ∈ keptClasses topology := by
  intro e' he'
  rw [mem_keptSlots] at he'
  rw [mem_keptClasses, contractedSpec_head]
  exact keptClass_head_of_keptSlot topology he'

/-! ## 4.  The pruned spec -/

/-- **The pruned contracted spec.**  `contractedSpec` with the dangling
occurrences and the classes they hang from removed. -/
noncomputable def prunedSpec (topology : SourceTopology data realization)
    (hKept : (keptClasses topology).Nonempty) :
    SubdivisionGraph.Spec (keptClasses topology).card (keptSlots topology).card :=
  PendantDeletion.Spec.restrict topology.contractedSpec (keptClasses topology)
    (keptSlots topology) hKept (tail_mem_keptClasses topology)
    (head_mem_keptClasses topology)

/-- **The pendant-separation receipt.**  A dangling positive slot has an
endpoint class that pruning discards.  Its converse is free
(`keptClass_tail_of_keptSlot`). -/
def PendantSeparated (topology : SourceTopology data realization) : Prop :=
  ∀ e : topology.degSpec.PositiveSlot, ¬ KeptSlot topology e →
    ¬ KeptClass topology (classOfCore topology (topology.degSpec.core.tail e.val)) ∨
      ¬ KeptClass topology (classOfCore topology (topology.degSpec.core.head e.val))

theorem dropped_of_pendantSeparated (topology : SourceTopology data realization)
    (hSep : PendantSeparated topology) :
    ∀ e' ∉ keptSlots topology, topology.contractedSpec.length e' = 1 →
      topology.contractedSpec.core.tail e' ∉ keptClasses topology ∨
        topology.contractedSpec.core.head e' ∉ keptClasses topology := by
  intro e' he' _
  rw [mem_keptSlots] at he'
  rcases hSep (topology.degSpec.slotIndex.symm e') he' with h | h
  · refine Or.inl ?_
    rw [mem_keptClasses, contractedSpec_tail]
    exact h
  · refine Or.inr ?_
    rw [mem_keptClasses, contractedSpec_head]
    exact h

/-- **`prunedSpec` is the induced subgraph.**  The kept vertices are the kept
classes together with the interiors of the kept slots. -/
noncomputable def prunedVertices (topology : SourceTopology data realization) :
    Finset topology.contractedSpec.Vertex :=
  PendantDeletion.Spec.keptVertices topology.contractedSpec (keptClasses topology)
    (keptSlots topology)

noncomputable def prunedSpec_laplacianEquiv (topology : SourceTopology data realization)
    (hKept : (keptClasses topology).Nonempty) (hSep : PendantSeparated topology) :
    LaplacianEquiv (prunedSpec topology hKept).graph
      (inducedSubgraph topology.contractedSpec.graph (prunedVertices topology)
        (PendantDeletion.Spec.keptVertices_nonempty hKept)) :=
  PendantDeletion.Spec.laplacianEquiv_restrict hKept (tail_mem_keptClasses topology)
    (head_mem_keptClasses topology) (dropped_of_pendantSeparated topology hSep)

/-! ## 5.  Genus, and the pushforward -/

/-- The genus of `contractedSpec`, proved directly from the two fields of
`SourceTopology`: this module sits below `ClosedEndpoint`. -/
theorem genus_contractedSpec_eq (topology : SourceTopology data realization) :
    genus topology.contractedSpec.graph = genus data.sourceGraph := by
  rw [← topology.laplacianEquiv.genus_eq]
  exact realization.genus_sourceDegSpec topology.forest topology.notLoopy

theorem genus_contractedSpec_card (topology : SourceTopology data realization) :
    genus topology.contractedSpec.graph =
      (topology.degSpec.slotCard : ℤ) - (topology.degSpec.classCard : ℤ) + 1 :=
  SubdivisionGraph.Spec.genus_graph _

theorem genus_prunedSpec (topology : SourceTopology data realization)
    (hKept : (keptClasses topology).Nonempty) :
    genus (prunedSpec topology hKept).graph =
      ((keptSlots topology).card : ℤ) - ((keptClasses topology).card : ℤ) + 1 :=
  PendantDeletion.Spec.genus_restrict hKept (tail_mem_keptClasses topology)
    (head_mem_keptClasses topology)

/-- **The Euler transport, as an equivalence.**  The genus identity the
pushforward needs is *exactly* the count "discarded classes = dangling positive
slots", in subtraction-free form. -/
theorem genus_prunedSpec_eq_genus_sourceGraph_iff
    (topology : SourceTopology data realization)
    (hKept : (keptClasses topology).Nonempty) :
    genus (prunedSpec topology hKept).graph = genus data.sourceGraph ↔
      topology.degSpec.classCard + (keptSlots topology).card =
        (keptClasses topology).card + topology.degSpec.slotCard := by
  rw [genus_prunedSpec, ← genus_contractedSpec_eq topology, genus_contractedSpec_card]
  omega

/-- **The Euler transport.** -/
theorem genus_prunedSpec_eq_genus_sourceGraph (topology : SourceTopology data realization)
    (hKept : (keptClasses topology).Nonempty)
    (hCount : topology.degSpec.classCard + (keptSlots topology).card =
      (keptClasses topology).card + topology.degSpec.slotCard) :
    genus (prunedSpec topology hKept).graph = genus data.sourceGraph :=
  (genus_prunedSpec_eq_genus_sourceGraph_iff topology hKept).mpr hCount

/-- **The pushforward, specialised.**  The pencil produced on the whole
contracted quotient source is carried to the pruned contracted spec. -/
theorem bnExists_prunedSpec (topology : SourceTopology data realization)
    (hKept : (keptClasses topology).Nonempty) (hSep : PendantSeparated topology)
    (hConnected : graph_connected topology.contractedSpec.graph)
    (hGenus : genus (prunedSpec topology hKept).graph =
      genus topology.contractedSpec.graph)
    {d : ℤ} (hBN : BNExists topology.contractedSpec.graph 1 d) :
    BNExists (prunedSpec topology hKept).graph 1 d := by
  have hEquiv := prunedSpec_laplacianEquiv topology hKept hSep
  have hInduced :
      genus (inducedSubgraph topology.contractedSpec.graph (prunedVertices topology)
        (PendantDeletion.Spec.keptVertices_nonempty hKept)) =
      genus topology.contractedSpec.graph := by
    rw [hEquiv.genus_eq]
    exact hGenus
  exact (hEquiv.bnExists_iff 1 d).mpr
    (PendantDeletion.bnExists_induce_of_genus_eq topology.contractedSpec.graph
      (prunedVertices topology) (PendantDeletion.Spec.keptVertices_nonempty hKept)
      hConnected hInduced hBN)

/-- The same with the genus hypothesis replaced by the count it is equivalent
to (`genus_prunedSpec_eq_genus_sourceGraph_iff`). -/
theorem bnExists_prunedSpec_of_count (topology : SourceTopology data realization)
    (hKept : (keptClasses topology).Nonempty) (hSep : PendantSeparated topology)
    (hConnected : graph_connected topology.contractedSpec.graph)
    (hCount : topology.degSpec.classCard + (keptSlots topology).card =
      (keptClasses topology).card + topology.degSpec.slotCard)
    {d : ℤ} (hBN : BNExists topology.contractedSpec.graph 1 d) :
    BNExists (prunedSpec topology hKept).graph 1 d :=
  bnExists_prunedSpec topology hKept hSep hConnected
    ((genus_prunedSpec_eq_genus_sourceGraph topology hKept hCount).trans
      (genus_contractedSpec_eq topology).symm) hBN


end DraismaVargas.LocalCases.PrunedRealizationSpec
