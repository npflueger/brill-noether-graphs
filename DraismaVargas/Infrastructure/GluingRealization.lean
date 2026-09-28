import DraismaVargas.Infrastructure.GluingDatum
import Utilities.Gonality.SubdivisionPencil
import Utilities.Subdivision.SubdivisionConnectivity
import Utilities.Subdivision.UnitSubdivisionPresentation

/-!
# Integral realizations of DV gluing data

A realized sheet gluing datum assigns a positive integral length to every
target-edge occurrence and every quotient-source edge block.  The target
length is the dilation index times the source length.  This file turns those
occurrence-labelled lengths into actual `SubdivisionGraph.Spec` objects.

The construction deliberately routes through the occurrence-safe unit
presentation of a `CFGraph` in `Utilities`.  A `Multiset.mapEquiv` remembers which
`GluingDatum.SourceEdge` produced each occurrence of the quotient graph, even
when several blocks have the same endpoint pair.
-/

namespace DraismaVargas.Infrastructure

open Finset
open Utilities
open Utilities.Certificate
open Utilities.Certificate.ExplicitPotential
open Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.UnitSubdivisionPresentation

/-- Connectedness of a finite graph implies connectedness of its canonical
occurrence-labelled ordered core. -/
theorem unitPresentationCore_connected_of_graph_connected (graph : CFGraph)
    (hConnected : graph_connected graph) :
    (Utilities.Certificate.UnitSubdivisionPresentation.core graph).Connected := by
  intro cut hSplit
  let originalCut : Finset graph.V :=
    Finset.univ.filter fun vertex ↦ vertexEquiv graph vertex ∈ cut
  obtain ⟨inside, outside, hInside, hOutside⟩ := hSplit
  have hOriginalSplit :
      ∃ first second : graph.V,
        first ∈ originalCut ∧ second ∉ originalCut := by
    exact ⟨(vertexEquiv graph).symm inside,
      (vertexEquiv graph).symm outside, by simpa [originalCut], by
        simpa [originalCut]⟩
  obtain ⟨first, hFirst, second, hSecond, hEdge⟩ :=
    hConnected originalCut hOriginalSplit
  have hFirstCut : vertexEquiv graph first ∈ cut := by
    simpa [originalCut] using hFirst
  have hSecondCut : vertexEquiv graph second ∉ cut := by
    simpa [originalCut] using hSecond
  unfold num_edges at hEdge
  obtain ⟨pair, hPair⟩ := Multiset.card_pos_iff_exists_mem.mp hEdge
  have hPairData := Multiset.mem_filter.mp hPair
  rcases hPairData.2 with hPairOrder | hPairOrder
  · let occurrence : graph.edges :=
      ⟨pair, ⟨0, Multiset.count_pos.mpr hPairData.1⟩⟩
    refine ⟨edgeEquiv graph occurrence, Or.inl ⟨?_, ?_⟩⟩
    · rw [core_tail_edgeEquiv graph occurrence]
      change vertexEquiv graph pair.1 ∈ cut
      rw [hPairOrder]
      exact hFirstCut
    · rw [core_head_edgeEquiv graph occurrence]
      change vertexEquiv graph pair.2 ∉ cut
      rw [hPairOrder]
      exact hSecondCut
  · let occurrence : graph.edges :=
      ⟨pair, ⟨0, Multiset.count_pos.mpr hPairData.1⟩⟩
    refine ⟨edgeEquiv graph occurrence, Or.inr ⟨?_, ?_⟩⟩
    · rw [core_head_edgeEquiv graph occurrence]
      change vertexEquiv graph pair.2 ∈ cut
      rw [hPairOrder]
      exact hFirstCut
    · rw [core_tail_edgeEquiv graph occurrence]
      change vertexEquiv graph pair.1 ∉ cut
      rw [hPairOrder]
      exact hSecondCut

namespace GluingDatum

variable {target : CFGraph} {degree : ℕ}

/-- The occurrence type before applying `sourceEnds`.  Coercion forgets only
the proof/index distinguishing its position in `univ`; it retains the actual
source edge block. -/
abbrev EnumeratedSourceEdge (data : GluingDatum target degree) :=
  Multiset.ToType (Finset.univ : Finset data.SourceEdge).val

/-- Enumerating the duplicate-free multiset underlying `Finset.univ` neither
loses nor duplicates source edge blocks. -/
noncomputable def sourceEnumerationEquiv (data : GluingDatum target degree) :
    data.EnumeratedSourceEdge ≃ data.SourceEdge where
  toFun item := item.1
  invFun edge :=
    ⟨edge, ⟨0, by
      rw [Multiset.count_eq_one_of_mem Finset.univ.nodup (by simp)]
      omega⟩⟩
  left_inv := by
    rintro ⟨edge, index⟩
    have hCount :
        Multiset.count edge (Finset.univ : Finset data.SourceEdge).val = 1 :=
      Multiset.count_eq_one_of_mem Finset.univ.nodup (by simp)
    have hSubsingleton : Subsingleton
        (Fin (Multiset.count edge (Finset.univ : Finset data.SourceEdge).val)) := by
      rw [hCount]
      infer_instance
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      exact hSubsingleton.elim _ _
  right_inv := by
    intro edge
    rfl

/-- Every emitted quotient-source edge occurrence remembers its unique
enumerated source edge.  This remains an equivalence when endpoint pairs are
parallel. -/
noncomputable def sourceOccurrenceEquiv (data : GluingDatum target degree) :
    data.EnumeratedSourceEdge ≃ data.sourceGraph.edges := by
  exact Multiset.mapEquiv
    (Finset.univ : Finset data.SourceEdge).val data.sourceEnds

/-- The exact quotient-source occurrence emitted by each source edge block. -/
noncomputable def sourceEdgeOccurrenceEquiv (data : GluingDatum target degree) :
    data.SourceEdge ≃ data.sourceGraph.edges :=
  data.sourceEnumerationEquiv.symm.trans data.sourceOccurrenceEquiv

@[simp] theorem sourceEdgeOccurrenceEquiv_apply
    (data : GluingDatum target degree) (edge : data.SourceEdge) :
    ((data.sourceEdgeOccurrenceEquiv edge : data.sourceGraph.edges) :
        data.sourceGraph.V × data.sourceGraph.V) = data.sourceEnds edge := by
  change ((data.sourceOccurrenceEquiv (data.sourceEnumerationEquiv.symm edge) :
      data.sourceGraph.edges) : data.sourceGraph.V × data.sourceGraph.V) = _
  unfold sourceOccurrenceEquiv
  change ((Multiset.mapEquiv
      (Finset.univ : Finset data.SourceEdge).val data.sourceEnds
      (data.sourceEnumerationEquiv.symm edge)).1 :
        data.SourceVertex × data.SourceVertex) = data.sourceEnds edge
  have hEmitter : (data.sourceEnumerationEquiv.symm edge).1 = edge :=
    data.sourceEnumerationEquiv.apply_symm_apply edge
  have hMap := Multiset.mapEquiv_apply
    (Finset.univ : Finset data.SourceEdge).val data.sourceEnds
    (data.sourceEnumerationEquiv.symm edge)
  simpa only [hEmitter] using hMap

/-- Recover the sheet-partition edge block that emitted an occurrence of the
quotient source graph. -/
noncomputable def sourceEdgeOfOccurrence (data : GluingDatum target degree)
    (occurrence : data.sourceGraph.edges) : data.SourceEdge :=
  data.sourceEdgeOccurrenceEquiv.symm occurrence

/-- Recovering an emitter preserves its unordered endpoint pair literally. -/
@[simp] theorem sourceEnds_sourceEdgeOfOccurrence
    (data : GluingDatum target degree)
    (occurrence : data.sourceGraph.edges) :
    data.sourceEnds (data.sourceEdgeOfOccurrence occurrence) =
      (occurrence : data.sourceGraph.V × data.sourceGraph.V) := by
  rw [← data.sourceEdgeOccurrenceEquiv_apply]
  exact congrArg (fun item : data.sourceGraph.edges ↦ item.1)
    (data.sourceEdgeOccurrenceEquiv.apply_symm_apply occurrence)

/-- Positive integral metric data compatible with all sheet-block dilation
indices.  The equation is the metric-harmonic identity
`target length = index * source length`. -/
structure IntegralRealization (data : GluingDatum target degree) where
  targetLength : target.edges → ℕ
  targetLength_pos : ∀ edge, 0 < targetLength edge
  sourceLength : data.SourceEdge → ℕ
  sourceLength_pos : ∀ edge, 0 < sourceLength edge
  dilation_length : ∀ edge,
    data.sourceEdgeIndex edge * sourceLength edge = targetLength edge.1.1

namespace IntegralRealization

variable {data : GluingDatum target degree}

/-- The exact sheet-block edge occupying a source specification slot. -/
noncomputable def sourceEdgeAt (_realization : data.IntegralRealization)
    (slot : Fin data.sourceGraph.edges.card) : data.SourceEdge :=
  data.sourceEdgeOfOccurrence
    (UnitSubdivisionPresentation.edgeOccurrence data.sourceGraph slot)

/-- Canonical source specification slots are equivalent to the exact
sheet-partition edge blocks that emitted them. -/
noncomputable def sourceSlotEquiv (_realization : data.IntegralRealization) :
    Fin data.sourceGraph.edges.card ≃ data.SourceEdge :=
  (UnitSubdivisionPresentation.edgeEquiv data.sourceGraph).symm.trans
    data.sourceEdgeOccurrenceEquiv.symm

@[simp] theorem sourceSlotEquiv_apply (realization : data.IntegralRealization)
    (slot : Fin data.sourceGraph.edges.card) :
    realization.sourceSlotEquiv slot = realization.sourceEdgeAt slot := rfl

/-- The quotient-source vertex carrying a canonical finite core label. -/
noncomputable def sourceVertexAt (_realization : data.IntegralRealization)
    (vertex : Fin (Fintype.card data.sourceGraph.V)) : data.SourceVertex :=
  (UnitSubdivisionPresentation.vertexEquiv data.sourceGraph).symm vertex

/-- Canonical source core labels are equivalent to quotient-source vertices. -/
noncomputable def sourceVertexEquiv (_realization : data.IntegralRealization) :
    Fin (Fintype.card data.sourceGraph.V) ≃ data.SourceVertex :=
  (UnitSubdivisionPresentation.vertexEquiv data.sourceGraph).symm

@[simp] theorem sourceVertexEquiv_apply (realization : data.IntegralRealization)
    (vertex : Fin (Fintype.card data.sourceGraph.V)) :
    realization.sourceVertexEquiv vertex = realization.sourceVertexAt vertex := rfl

theorem sourceVertexAt_injective (realization : data.IntegralRealization) :
    Function.Injective realization.sourceVertexAt :=
  (UnitSubdivisionPresentation.vertexEquiv data.sourceGraph).symm.injective

/-- The target tree with every occurrence subdivided to its realized integral
length. -/
noncomputable def targetSpec (realization : data.IntegralRealization) :
    Spec (Fintype.card target.V) target.edges.card where
  core := UnitSubdivisionPresentation.core target
  length slot := realization.targetLength
    (UnitSubdivisionPresentation.edgeOccurrence target slot)
  core_nonempty := Fintype.card_pos
  core_loopless := (UnitSubdivisionPresentation.spec target).core_loopless
  length_pos slot := realization.targetLength_pos
    (UnitSubdivisionPresentation.edgeOccurrence target slot)

/-- The quotient source core with the length attached to the exact source-edge
block that emitted each occurrence. -/
noncomputable def sourceSpec (realization : data.IntegralRealization) :
    Spec (Fintype.card data.sourceGraph.V) data.sourceGraph.edges.card where
  core := UnitSubdivisionPresentation.core data.sourceGraph
  length slot := realization.sourceLength
    (realization.sourceEdgeAt slot)
  core_nonempty := Fintype.card_pos
  core_loopless := (UnitSubdivisionPresentation.spec data.sourceGraph).core_loopless
  length_pos slot := realization.sourceLength_pos
    (realization.sourceEdgeAt slot)

/-- The tail core label decodes to the tail quotient vertex of the exact
source edge block occupying the slot. -/
theorem sourceVertexAt_core_tail (realization : data.IntegralRealization)
    (slot : Fin data.sourceGraph.edges.card) :
    realization.sourceVertexAt (realization.sourceSpec.core.tail slot) =
      (data.sourceEnds (realization.sourceEdgeAt slot)).1 := by
  change (UnitSubdivisionPresentation.vertexEquiv data.sourceGraph).symm
      ((UnitSubdivisionPresentation.core data.sourceGraph).tail slot) = _
  rw [UnitSubdivisionPresentation.core_tail]
  simp only [Equiv.symm_apply_apply]
  rw [sourceEdgeAt, data.sourceEnds_sourceEdgeOfOccurrence]
  rfl

/-- The head core label decodes to the head quotient vertex of the exact
source edge block occupying the slot. -/
theorem sourceVertexAt_core_head (realization : data.IntegralRealization)
    (slot : Fin data.sourceGraph.edges.card) :
    realization.sourceVertexAt (realization.sourceSpec.core.head slot) =
      (data.sourceEnds (realization.sourceEdgeAt slot)).2 := by
  change (UnitSubdivisionPresentation.vertexEquiv data.sourceGraph).symm
      ((UnitSubdivisionPresentation.core data.sourceGraph).head slot) = _
  rw [UnitSubdivisionPresentation.core_head]
  simp only [Equiv.symm_apply_apply]
  rw [sourceEdgeAt, data.sourceEnds_sourceEdgeOfOccurrence]
  rfl

/-- The source specification is connected whenever the gluing datum's literal
quotient source graph is connected. -/
theorem sourceSpec_connected (realization : data.IntegralRealization)
    (hConnected : data.Connected) :
    graph_connected realization.sourceSpec.graph := by
  apply realization.sourceSpec.graph_connected_of_coreConnected
  exact unitPresentationCore_connected_of_graph_connected
    data.sourceGraph hConnected

/-- The realized dilation equation, expressed on the source specification's
canonical edge slots without forgetting occurrence identity. -/
theorem sourceSpec_dilation_length (realization : data.IntegralRealization)
    (slot : Fin data.sourceGraph.edges.card) :
    data.sourceEdgeIndex
        (data.sourceEdgeOfOccurrence
          (UnitSubdivisionPresentation.edgeOccurrence data.sourceGraph slot)) *
      realization.sourceSpec.length slot =
    realization.targetLength
      ((data.sourceEdgeOfOccurrence
        (UnitSubdivisionPresentation.edgeOccurrence data.sourceGraph slot)).1.1) := by
  exact realization.dilation_length _

/-- Pull a target-vertex potential back to the quotient-source core labels. -/
noncomputable def sourcePotential (realization : data.IntegralRealization)
    (potential : target.V → ℤ) :
    Fin (Fintype.card data.sourceGraph.V) → ℤ :=
  fun vertex ↦ potential (realization.sourceVertexAt vertex).1.1

/-- The integral source slope induced by a target slope is multiplied by the
sheet-block dilation index. -/
noncomputable def sourceSlope (realization : data.IntegralRealization)
    (targetSlope : target.edges → ℤ) :
    Fin data.sourceGraph.edges.card → ℤ :=
  fun slot ↦
    (data.sourceEdgeIndex (realization.sourceEdgeAt slot) : ℤ) *
      targetSlope (realization.sourceEdgeAt slot).1.1

/-- On canonical source specification slots, the pulled-back signed incidence
is the source local degree times the signed target incidence.  This transports
the partition harmonicity theorem through both occurrence equivalences. -/
theorem sourceSpec_incidence_eq_localDegree_mul_targetEdgeIncidence
    (realization : data.IntegralRealization)
    (targetSlope : target.edges → ℤ)
    (vertex : Fin (Fintype.card data.sourceGraph.V)) :
    (∑ slot : Fin data.sourceGraph.edges.card,
      ((if realization.sourceSpec.core.tail slot = vertex then
          realization.sourceSlope targetSlope slot else 0) +
        (if realization.sourceSpec.core.head slot = vertex then
          -realization.sourceSlope targetSlope slot else 0))) =
      ((data.vertexPartition (realization.sourceVertexAt vertex).1.1).blockCard
          (realization.sourceVertexAt vertex).1.2 : ℤ) *
        targetEdgeIncidence targetSlope
          (realization.sourceVertexAt vertex).1.1 := by
  let sourceVertex := realization.sourceVertexAt vertex
  let sourceSummand : data.SourceEdge → ℤ := fun edge ↦
    ((if (data.sourceEnds edge).1 = sourceVertex then
        (data.sourceEdgeIndex edge : ℤ) * targetSlope edge.1.1
      else 0) +
      (if (data.sourceEnds edge).2 = sourceVertex then
        (data.sourceEdgeIndex edge : ℤ) * (-targetSlope edge.1.1)
      else 0))
  calc
    (∑ slot : Fin data.sourceGraph.edges.card,
      ((if realization.sourceSpec.core.tail slot = vertex then
          realization.sourceSlope targetSlope slot else 0) +
        (if realization.sourceSpec.core.head slot = vertex then
          -realization.sourceSlope targetSlope slot else 0))) =
        ∑ edge : data.SourceEdge, sourceSummand edge := by
      apply Fintype.sum_equiv realization.sourceSlotEquiv
      intro slot
      have hTail : realization.sourceSpec.core.tail slot = vertex ↔
          (data.sourceEnds (realization.sourceEdgeAt slot)).1 = sourceVertex := by
        constructor
        · intro h
          subst vertex
          exact (realization.sourceVertexAt_core_tail slot).symm
        · intro h
          apply realization.sourceVertexAt_injective
          rw [realization.sourceVertexAt_core_tail slot]
          exact h
      have hHead : realization.sourceSpec.core.head slot = vertex ↔
          (data.sourceEnds (realization.sourceEdgeAt slot)).2 = sourceVertex := by
        constructor
        · intro h
          subst vertex
          exact (realization.sourceVertexAt_core_head slot).symm
        · intro h
          apply realization.sourceVertexAt_injective
          rw [realization.sourceVertexAt_core_head slot]
          exact h
      simp only [sourceSummand, sourceSlope, sourceSlotEquiv_apply]
      rw [if_congr hTail.symm rfl rfl, if_congr hHead.symm rfl rfl]
      simp only [mul_neg]
    _ = data.sourceEdgeIncidence targetSlope sourceVertex := rfl
    _ = ((data.vertexPartition sourceVertex.1.1).blockCard sourceVertex.1.2 : ℤ) *
          targetEdgeIncidence targetSlope sourceVertex.1.1 :=
      data.sourceEdgeIncidence_eq_localDegree_mul_targetEdgeIncidence
        targetSlope sourceVertex

/-- The local degree attached to a canonical source core vertex. -/
noncomputable def sourceLocalDegree (realization : data.IntegralRealization)
    (vertex : Fin (Fintype.card data.sourceGraph.V)) : ℤ :=
  ((data.vertexPartition (realization.sourceVertexAt vertex).1.1).blockCard
    (realization.sourceVertexAt vertex).1.2 : ℤ)

/-- The core-supported pullback of a one-chip divisor at a target vertex. -/
noncomputable def fibreWeight (realization : data.IntegralRealization)
    (root : target.V) (vertex : Fin (Fintype.card data.sourceGraph.V)) : ℤ :=
  if (realization.sourceVertexAt vertex).1.1 = root then
    realization.sourceLocalDegree vertex
  else 0

/-- Reindex the canonical-core fibre sum by the literal quotient-source
vertices.  The right side is finite and computational for concrete data even
though the canonical `Fintype.equivFin` labeling is noncomputable. -/
theorem sum_fibreWeight_eq_sum_sourceVertices
    (realization : data.IntegralRealization) (root : target.V) :
    (∑ vertex : Fin (Fintype.card data.sourceGraph.V),
      realization.fibreWeight root vertex) =
    ∑ vertex : data.SourceVertex,
      if vertex.1.1 = root then
        ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ)
      else 0 := by
  rw [← realization.sourceVertexEquiv.sum_comp]
  rfl

/-- Every canonical fibre has total weight equal to the number of sheets. -/
theorem sum_fibreWeight_eq_degree
    (realization : data.IntegralRealization) (root : target.V) :
    (∑ vertex : Fin (Fintype.card data.sourceGraph.V),
      realization.fibreWeight root vertex) = degree := by
  rw [realization.sum_fibreWeight_eq_sum_sourceVertices]
  exact data.sum_sourceVertex_localDegree_over root

private theorem fibreResidual_nonneg {source targetVertex : Type*}
    [DecidableEq source] [DecidableEq targetVertex]
    (vertex anchor : source) (vertexMap : source → targetVertex)
    (root : targetVertex) (localDegree : ℤ) (hLocalDegree : 0 < localDegree) :
    0 ≤ (if vertexMap vertex = root then localDegree else 0) -
        (if vertex = anchor then 1 else 0) +
      localDegree *
        ((if vertexMap vertex = vertexMap anchor then 1 else 0) -
          (if vertexMap vertex = root then 1 else 0)) := by
  split_ifs <;> simp_all <;> omega

/-- The metric pullback identity on every actual quotient-source occurrence.
If the target potential has exact integral slope on each realized target
edge, its pullback has slope `index * targetSlope` on the corresponding
realized source edge. -/
theorem sourceCoreRise_eq_sourceSlope_mul_length
    (realization : data.IntegralRealization)
    (potential : target.V → ℤ) (targetSlope : target.edges → ℤ)
    (hTargetRise : ∀ edge : target.edges,
      potential (edge : target.V × target.V).2 -
          potential (edge : target.V × target.V).1 =
        targetSlope edge * (realization.targetLength edge : ℤ))
    (slot : Fin data.sourceGraph.edges.card) :
    realization.sourceSpec.coreRise
        (realization.sourcePotential potential) slot =
      realization.sourceSlope targetSlope slot *
        (realization.sourceSpec.length slot : ℤ) := by
  let sourceEdge := realization.sourceEdgeAt slot
  have hDilationNat := realization.dilation_length sourceEdge
  have hDilationInt :
      (data.sourceEdgeIndex sourceEdge : ℤ) *
          (realization.sourceLength sourceEdge : ℤ) =
        (realization.targetLength sourceEdge.1.1 : ℤ) := by
    exact_mod_cast hDilationNat
  change potential
      (realization.sourceVertexAt
        (realization.sourceSpec.core.head slot)).1.1 -
      potential
        (realization.sourceVertexAt
          (realization.sourceSpec.core.tail slot)).1.1 = _
  rw [realization.sourceVertexAt_core_head slot,
    realization.sourceVertexAt_core_tail slot]
  change potential (sourceEdge.1.1 : target.V × target.V).2 -
      potential (sourceEdge.1.1 : target.V × target.V).1 = _
  rw [hTargetRise sourceEdge.1.1]
  change targetSlope sourceEdge.1.1 *
      (realization.targetLength sourceEdge.1.1 : ℤ) =
    ((data.sourceEdgeIndex sourceEdge : ℤ) *
      targetSlope sourceEdge.1.1) *
        (realization.sourceLength sourceEdge : ℤ)
  rw [← hDilationInt]
  ring

/-- Semantic lowering for an integral DV realization.

It is enough to supply, on the occurrence-labelled target, exact integral
potentials moving a chip from `root` to every target vertex.  Partition
harmonicity pulls their slopes back with the dilation indices, and the fibre
over `root` becomes an effective rank-one divisor of the stated degree on the
realized quotient-source subdivision. -/
theorem rank_fibre_ge_one_of_targetPotentials
    (realization : data.IntegralRealization) (hConnected : data.Connected)
    (root : target.V)
    (targetPotential : target.V → target.V → ℤ)
    (targetSlope : target.V → target.edges → ℤ)
    (hTargetRise : ∀ (anchor : target.V) (edge : target.edges),
      targetPotential anchor (edge : target.V × target.V).2 -
          targetPotential anchor (edge : target.V × target.V).1 =
        targetSlope anchor edge * (realization.targetLength edge : ℤ))
    (hTargetIncidence : ∀ anchor vertex,
      targetEdgeIncidence (targetSlope anchor) vertex =
        (if vertex = anchor then 1 else 0) -
          (if vertex = root then 1 else 0)) :
    rank realization.sourceSpec.graph
      (Utilities.Subdivision.SubdivisionCoreSupport.coreDivisor
        realization.sourceSpec (realization.fibreWeight root)) ≥ 1 := by
  refine DraismaVargas.SubdivisionPencil.rank_coreDivisor_ge_one_of_exactCorePotentials
    realization.sourceSpec (realization.fibreWeight root)
    (realization.sourceSpec_connected hConnected)
    (fun anchor ↦ realization.sourcePotential
      (targetPotential (realization.sourceVertexAt anchor).1.1))
    (fun anchor ↦ realization.sourceSlope
      (targetSlope (realization.sourceVertexAt anchor).1.1)) ?_ ?_
  · intro anchor edge
    exact realization.sourceCoreRise_eq_sourceSlope_mul_length
      (targetPotential (realization.sourceVertexAt anchor).1.1)
      (targetSlope (realization.sourceVertexAt anchor).1.1)
      (hTargetRise (realization.sourceVertexAt anchor).1.1) edge
  · intro anchor vertex
    rw [realization.sourceSpec_incidence_eq_localDegree_mul_targetEdgeIncidence,
      hTargetIncidence]
    exact fibreResidual_nonneg vertex anchor
      (fun sourceVertex ↦ (realization.sourceVertexAt sourceVertex).1.1) root
      (realization.sourceLocalDegree vertex) (by
        unfold sourceLocalDegree
        exact_mod_cast (data.vertexPartition
          (realization.sourceVertexAt vertex).1.1).blockCard_pos
            (realization.sourceVertexAt vertex).1.2)

/-- Existence and effectivity, retaining the named-fibre rank proof above. -/
theorem bnExists_and_effective_of_targetPotentials
    (realization : data.IntegralRealization) (hConnected : data.Connected)
    (root : target.V) (divisorDegree : ℤ)
    (hDegree : (∑ vertex : Fin (Fintype.card data.sourceGraph.V),
      realization.fibreWeight root vertex) = divisorDegree)
    (targetPotential : target.V → target.V → ℤ)
    (targetSlope : target.V → target.edges → ℤ)
    (hTargetRise : ∀ (anchor : target.V) (edge : target.edges),
      targetPotential anchor (edge : target.V × target.V).2 -
          targetPotential anchor (edge : target.V × target.V).1 =
        targetSlope anchor edge * (realization.targetLength edge : ℤ))
    (hTargetIncidence : ∀ anchor vertex,
      targetEdgeIncidence (targetSlope anchor) vertex =
        (if vertex = anchor then 1 else 0) -
          (if vertex = root then 1 else 0)) :
    BNExists realization.sourceSpec.graph 1 divisorDegree ∧
      _root_.effective
        (Utilities.Subdivision.SubdivisionCoreSupport.coreDivisor
          realization.sourceSpec (realization.fibreWeight root)) := by
  refine ⟨⟨_, (Utilities.Subdivision.SubdivisionCoreSupport.deg_coreDivisor
    realization.sourceSpec (realization.fibreWeight root)).trans hDegree,
    realization.rank_fibre_ge_one_of_targetPotentials hConnected root
      targetPotential targetSlope hTargetRise hTargetIncidence⟩, ?_⟩
  apply Utilities.Subdivision.SubdivisionCoreSupport.coreDivisor_effective
  intro vertex
  unfold fibreWeight
  split
  · unfold sourceLocalDegree
    exact_mod_cast (data.vertexPartition
      (realization.sourceVertexAt vertex).1.1).blockCard_pos
        (realization.sourceVertexAt vertex).1.2 |>.le
  · exact le_rfl

end IntegralRealization

end GluingDatum

end DraismaVargas.Infrastructure
