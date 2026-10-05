module

public import DraismaVargas.LocalCases.PrunedContractionFibre
public import DraismaVargas.LocalCases.PrunedSource

@[expose] public section

/-!
# Actual occurrence accounting in a pruned contraction fibre

Source: Draisma–Vargas Part I, arXiv:1909.12924, `lemma-ndval-of-GqA0`.  This file proves the
first equality in its proof: the sum of
non-dangling valencies in an actual contraction fibre equals the boundary
valency plus twice the number of surviving internal occurrences.  Incoming
vertices of non-dangling valency zero contribute zero, so the same equality
holds after pruning the vertex set.

The only transfer hypothesis is `DanglingCompatible` on actual noncontracted
occurrences.  No Euler count or stable-path compatibility is assumed.  The
forest identity `|E| + 1 = |V|` for the pruned fibre is proved separately
(`PrunedFibreTree`), not assumed here.
-/

namespace DraismaVargas.LocalCases.PrunedFibreValency

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre
open W4StableSource WallDegeneration PrunedSource

variable {target : CFGraph} {degree : ℕ}

/-- The exact handshake over a set of actual source vertices.  Each surviving
occurrence contributes once at each endpoint contained in the set. -/
theorem sum_nonDanglingValency_set (data : GluingDatum target degree)
    (vertices : Finset data.SourceVertex) :
    ∑ vertex ∈ vertices, nonDanglingValency data vertex =
      ∑ edge ∈ nonDanglingEdges data,
        ((if (data.sourceEnds edge).1 ∈ vertices then 1 else 0) +
          (if (data.sourceEnds edge).2 ∈ vertices then 1 else 0)) := by
  classical
  have hAt (vertex : data.SourceVertex) :
      nonDanglingValency data vertex =
        ∑ edge ∈ nonDanglingEdges data,
          ((if (data.sourceEnds edge).1 = vertex then 1 else 0) +
            (if (data.sourceEnds edge).2 = vertex then 1 else 0)) := by
    have hFilter : nonDanglingValency data vertex =
        ((nonDanglingEdges data).filter fun edge ↦ Incident data edge vertex).card := by
      unfold nonDanglingValency nonDanglingEdges
      congr 1
      ext edge
      simp
    rw [hFilter]
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro edge _
    have hNe := data.sourceEnds_ne edge
    by_cases hFirst : (data.sourceEnds edge).1 = vertex
    · have hSecond : (data.sourceEnds edge).2 ≠ vertex := by
        intro hSecond
        exact hNe (hFirst.trans hSecond.symm)
      simp only [Incident, hFirst, hSecond, or_false, ite_true, ite_false, add_zero]
    · by_cases hSecond : (data.sourceEnds edge).2 = vertex
      · simp only [Incident, hFirst, hSecond, false_or, ite_true, ite_false, zero_add]
      · simp only [Incident, hFirst, hSecond, or_self, ite_false, add_zero]
  simp_rw [hAt]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro edge _
  rw [Finset.sum_add_distrib]
  simp

section Fibre

variable (data : GluingDatum target degree) {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

/-- The actual source-vertex preimage of a wall vertex. -/
noncomputable def fibreVertices
    (vertex : (contractDatum data hc hab hOne).SourceVertex) : Finset data.SourceVertex :=
  Finset.univ.filter fun first ↦ sourceVertexMap data hc hab hOne first = vertex

/-- Its pruned vertex set: vertices meeting at least one surviving occurrence. -/
noncomputable def activeFibreVertices
    (vertex : (contractDatum data hc hab hOne).SourceVertex) : Finset data.SourceVertex :=
  (fibreVertices data hc hab hOne vertex).filter fun first ↦
    nonDanglingValency data first ≠ 0

/-- Surviving contracted occurrences inside the given actual fibre. -/
noncomputable def internalEdges
    (vertex : (contractDatum data hc hab hOne).SourceVertex) : Finset data.SourceEdge :=
  (nonDanglingEdges data).filter fun edge ↦ edge.1.1 = contracted ∧
    sourceVertexMap data hc hab hOne (data.sourceEnds edge).1 = vertex

/-- Surviving noncontracted occurrences meeting the given actual fibre. -/
noncomputable def boundaryEdges
    (vertex : (contractDatum data hc hab hOne).SourceVertex) : Finset data.SourceEdge :=
  (nonDanglingEdges data).filter fun edge ↦ edge.1.1 ≠ contracted ∧
    (sourceVertexMap data hc hab hOne (data.sourceEnds edge).1 = vertex ∨
      sourceVertexMap data hc hab hOne (data.sourceEnds edge).2 = vertex)

@[simp] theorem mem_fibreVertices
    (vertex : (contractDatum data hc hab hOne).SourceVertex) (first : data.SourceVertex) :
    first ∈ fibreVertices data hc hab hOne vertex ↔
      sourceVertexMap data hc hab hOne first = vertex := by
  classical
  simp only [fibreVertices, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem mem_boundaryEdges
    (vertex : (contractDatum data hc hab hOne).SourceVertex) (edge : data.SourceEdge) :
    edge ∈ boundaryEdges data hc hab hOne vertex ↔
      ¬ IsDangling data edge ∧ edge.1.1 ≠ contracted ∧
      (sourceVertexMap data hc hab hOne (data.sourceEnds edge).1 = vertex ∨
        sourceVertexMap data hc hab hOne (data.sourceEnds edge).2 = vertex) := by
  classical
  simp only [boundaryEdges, nonDanglingEdges, Finset.mem_filter,
    Finset.mem_univ, true_and]

/-- A noncontracted occurrence cannot have both endpoints in one fibre: its
mapped source occurrence is loopless. -/
theorem sourceVertexMap_sourceEnds_ne
    (edge : {edge : data.SourceEdge // edge.1.1 ≠ contracted}) :
    sourceVertexMap data hc hab hOne (data.sourceEnds edge.1).1 ≠
      sourceVertexMap data hc hab hOne (data.sourceEnds edge.1).2 := by
  have hNe := (contractDatum data hc hab hOne).sourceEnds_ne
    (sourceEdgeMap data hc hab hOne edge)
  rw [sourceEnds_sourceEdgeMap] at hNe
  exact hNe

/-- Actual boundary occurrences are in bijection with the wall's incident
survivors, using the existing occurrencewise danglingness compatibility. -/
theorem card_boundaryEdges (hCompat : DanglingCompatible data hc hab hOne)
    (vertex : (contractDatum data hc hab hOne).SourceVertex) :
    (boundaryEdges data hc hab hOne vertex).card =
      nonDanglingValency (contractDatum data hc hab hOne) vertex := by
  classical
  rw [nonDanglingValency_eq_card_filter]
  refine Finset.card_bij
    (fun edge hEdge ↦ sourceEdgeMap data hc hab hOne
      ⟨edge, ((mem_boundaryEdges data hc hab hOne vertex edge).mp hEdge).2.1⟩) ?_ ?_ ?_
  · intro edge hEdge
    obtain ⟨hSurvive, hTarget, hEnds⟩ :=
      (mem_boundaryEdges data hc hab hOne vertex edge).mp hEdge
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · exact fun hBad ↦ hSurvive (hCompat.2 ⟨edge, hTarget⟩ hBad)
    · unfold Incident
      rw [sourceEnds_sourceEdgeMap]
      exact hEnds
  · intro first hFirst second hSecond hEq
    exact congrArg Subtype.val (sourceEdgeMap_injective data hc hab hOne hEq)
  · intro edge hEdge
    obtain ⟨hSurvive, hIncident⟩ := (Finset.mem_filter.mp hEdge).2
    let preimage := (sourceEdgeEquiv data hc hab hOne).symm edge
    have hMap : sourceEdgeMap data hc hab hOne preimage = edge :=
      (sourceEdgeEquiv data hc hab hOne).apply_symm_apply edge
    have hPreimage : preimage.1 ∈ boundaryEdges data hc hab hOne vertex := by
      rw [mem_boundaryEdges]
      refine ⟨fun hBad ↦ hSurvive (hMap ▸ hCompat.1 preimage hBad), preimage.2, ?_⟩
      rw [← hMap] at hIncident
      unfold Incident at hIncident
      rw [sourceEnds_sourceEdgeMap] at hIncident
      exact hIncident
    exact ⟨preimage.1, hPreimage, hMap⟩

/-- The source's first double-counting equality, before the tree Euler count:
internal surviving occurrences count twice, and boundary occurrences once. -/
theorem sum_nonDanglingValency_fibre_eq_boundary_add_twice_internal
    (vertex : (contractDatum data hc hab hOne).SourceVertex) :
    ∑ first ∈ fibreVertices data hc hab hOne vertex, nonDanglingValency data first =
      (boundaryEdges data hc hab hOne vertex).card +
        2 * (internalEdges data hc hab hOne vertex).card := by
  classical
  rw [sum_nonDanglingValency_set]
  simp only [mem_fibreVertices, boundaryEdges, internalEdges,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro edge _
  by_cases hTarget : edge.1.1 = contracted
  · have hMap := sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hOne edge hTarget
    by_cases hFirst : sourceVertexMap data hc hab hOne (data.sourceEnds edge).1 = vertex
    · have hSecond := hMap.symm.trans hFirst
      simp [Ne, hFirst, hSecond, hTarget]
    · have hSecond : sourceVertexMap data hc hab hOne (data.sourceEnds edge).2 ≠ vertex :=
        fun h ↦ hFirst (hMap.trans h)
      simp [hFirst, hSecond]
  · have hNe := sourceVertexMap_sourceEnds_ne data hc hab hOne ⟨edge, hTarget⟩
    by_cases hFirst : sourceVertexMap data hc hab hOne (data.sourceEnds edge).1 = vertex
    · have hSecond : sourceVertexMap data hc hab hOne (data.sourceEnds edge).2 ≠ vertex :=
        fun h ↦ hNe (hFirst.trans h.symm)
      simp [Ne, hFirst, hSecond, hTarget]
    · by_cases hSecond : sourceVertexMap data hc hab hOne (data.sourceEnds edge).2 = vertex
      · simp [Ne, hFirst, hSecond, hTarget]
      · simp [hFirst, hSecond]

/-- Pruning the fibre vertex set does not change the sum of non-dangling
valencies: precisely its zero summands are removed. -/
theorem sum_nonDanglingValency_activeFibre_eq
    (vertex : (contractDatum data hc hab hOne).SourceVertex) :
    ∑ first ∈ activeFibreVertices data hc hab hOne vertex, nonDanglingValency data first =
      ∑ first ∈ fibreVertices data hc hab hOne vertex, nonDanglingValency data first := by
  classical
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro first hMem hNot
  by_contra hNe
  exact hNot (Finset.mem_filter.mpr ⟨hMem, hNe⟩)

/-- **Actual pruned-fibre valency accounting.**  This is the first equality in
the proof of `lemma-ndval-of-GqA0`, in additive natural-number form.  It remains
valid independently of the contraction forest count. -/
theorem sum_nonDanglingValency_activeFibre
    (hCompat : DanglingCompatible data hc hab hOne)
    (vertex : (contractDatum data hc hab hOne).SourceVertex) :
    ∑ first ∈ activeFibreVertices data hc hab hOne vertex, nonDanglingValency data first =
      nonDanglingValency (contractDatum data hc hab hOne) vertex +
        2 * (internalEdges data hc hab hOne vertex).card := by
  rw [sum_nonDanglingValency_activeFibre_eq,
    sum_nonDanglingValency_fibre_eq_boundary_add_twice_internal,
    card_boundaryEdges data hc hab hOne hCompat]

end Fibre

end DraismaVargas.LocalCases.PrunedFibreValency
