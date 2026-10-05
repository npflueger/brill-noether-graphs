module

public import DraismaVargas.LocalCases.W4Bridge
public import DraismaVargas.LocalCases.DivalentSourceLocal

@[expose] public section

/-!
# The incoming four-valent source census

Source: Draisma–Vargas Part I, arXiv:1909.12924, Case {aux-r0} (`sub-r0`), its
opening paragraph.  The local no-return claim there is a consequence of
directional harmonicity, not an incoming matching hypothesis.  Equation (1) of
Part I (`eq-1`, the balancing equation of Case {w4}) is downstream of the
pruned-fibre classification; its presented-family proof does not identify an
arbitrary incoming datum with a member.

This module proves the source-local prerequisite on the actual incoming
datum. It does not supply a whole-fibre partition classification, incoming
family membership, or common stable-row matching.

Two distinct data are involved.  `IncomingSourceCases.Classification.w4`
retains an `AuxR0SourceInput` on the contracted datum, and
`AuxR0SourceInput.presentedFamily` builds its entire three-candidate family
from it, including the canonical occurrence receipts.  That family does not
identify the original incoming datum with a member; the statements here are
about the original incoming datum, and assume nothing beyond that input.

## How it fits

The identification of the incoming datum with a member is assembled on top of
this module:

1. `W4IncomingTargetNormalization` uses the forced endpoint valencies `3,3` to
   show that the actual `IncomingTargetExpansion.right` selects two of the four
   literal star occurrences, through the finite pairing exhaustion
   (`FourStar.exhausts_assignment_up_to_swap`) and the support/swap target
   isomorphisms, preserving `none` and every named `some edge` occurrence.
2. `W4IncomingPrunedFibre` combines the internal-incidence bound below with
   pruned-fibre connectedness to obtain one vertex, or one edge with two
   vertices.  For nd2, the side placement selects the alternative; for nd3 it
   gives an nd2 singleton-side vertex and an nd3 other-side vertex.
   `W4IncomingSheetClasses` then uses the exact block equality below and the
   class-union lemma to identify the coarse block and the singleton-branch
   refinement as literal sheet sets.
3. `W4IncomingGlobalMatching` matches these partitions with the constructed
   candidate (including dangling singleton blocks).

The outgoing source invariants and the certified exit (`W4OutgoingSurvival`,
`W4PositiveExit`) are separate statements; none is a consequence merely of
declaring the presented family.

**The `FourStar` enters only through a vanishing target change.**  It is used
at exactly one place -- `localRamification_eq_zero_at_endpoint` -- and only to
obtain `data.targetChange place = 0` at the two original endpoints, via
`W4Bridge.endpoints_trivalent_of_fourStar`.  The content therefore lives in the
`AnyWall` namespace, stated at a wall of any arity with that vanishing as a
hypothesis; `changeZero_of_fourStar` discharges it from a star in one line, and
each statement keeps its original name in its four-valent form.  A trivalent
wall reaches the `AnyWall` statements at any endpoint whose target change
vanishes -- which is what `W3Nd2IncomingSheetClasses` needs at its unramified
endpoint.
-/

namespace DraismaVargas.LocalCases.W4IncomingCensus

open DraismaVargas.Infrastructure
open W4StableSource StableLocalProperties W3R1SourceProfile FullDimensionalSource

variable {target : CFGraph} {degree : ℕ}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-- At an unramified nd3 source vertex, a repeated target direction would
carry two indices of total at most `m`; the remaining index is at most `m`,
contradicting the required total `2m+1`. -/
theorem sourceEdge_eq_of_same_target_of_nd3_r0
    (data : GluingDatum target degree) (hNoGlue : DanglingEdgeNoGlue data)
    (vertex : data.SourceVertex) (hNd : nonDanglingValency data vertex = 3)
    (hR : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 0)
    (first second : data.SourceEdge)
    (hFirst : ¬ IsDangling data first) (hSecond : ¬ IsDangling data second)
    (hFirstInc : Incident data first vertex) (hSecondInc : Incident data second vertex)
    (hTarget : first.1.1 = second.1.1) : first = second := by
  classical
  by_contra hNe
  let left : IncidentSourceEdge data vertex := ⟨first, hFirstInc⟩
  let right : IncidentSourceEdge data vertex := ⟨second, hSecondInc⟩
  have hDistinct : left ≠ right := fun h ↦ hNe (congrArg Subtype.val h)
  let surviving := Finset.univ.filter fun edge : IncidentSourceEdge data vertex ↦
    ¬ IsDangling data edge.1
  have hCard : surviving.card = 3 :=
    (card_filter_not_isDangling_eq_nonDanglingValency data vertex).trans hNd
  have hPair : {left, right} ⊆ surviving := by
    intro edge hEdge
    rcases Finset.mem_insert.mp hEdge with rfl | hEdge
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFirst⟩
    · rw [Finset.mem_singleton.mp hEdge]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSecond⟩
  have hRemainder : (surviving \ {left, right}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hPair, hCard, Finset.card_pair hDistinct]
  obtain ⟨third, hThird⟩ := Finset.card_eq_one.mp hRemainder
  have hPairBound := sum_index_le_of_same_target data vertex {left, right}
    first.1.1 ((incident_iff_target_mem_and_rel data first vertex).mp hFirstInc).1
    (by
      intro edge hEdge
      rcases Finset.mem_insert.mp hEdge with rfl | hEdge
      · rfl
      · exact (Finset.mem_singleton.mp hEdge) ▸ hTarget.symm)
  rw [Finset.sum_pair hDistinct] at hPairBound
  have hThirdBound := sourceEdgeIndex_le_blockCard data vertex third
  have hSum := Finset.sum_sdiff hPair
    (f := fun edge : IncidentSourceEdge data vertex ↦ (data.sourceEdgeIndex edge.1 : ℤ))
  rw [hThird, Finset.sum_singleton, Finset.sum_pair hDistinct] at hSum
  have hFormula := localRamification_eq_nonDangling_form data hNoGlue vertex
  rw [hR, hNd] at hFormula
  change 0 = (3 : ℤ) - 2 + 2 *
    ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) -
    ∑ edge ∈ surviving, (data.sourceEdgeIndex edge.1 : ℤ) at hFormula
  omega

/-- Each actual surviving edge at an unramified nd2 source vertex carries
the whole vertex block as a sheet set, not merely the same cardinality. -/
theorem block_eq_of_survives_nd2_r0
    (data : GluingDatum target degree) (hNoGlue : DanglingEdgeNoGlue data)
    (vertex : data.SourceVertex) (hNd : nonDanglingValency data vertex = 2)
    (hR : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 0)
    (edge : data.SourceEdge) (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge vertex) :
    (data.edgePartition edge.1.1).block edge.1.2 =
      (data.vertexPartition vertex.1.1).block vertex.1.2 := by
  classical
  obtain ⟨other, hNe, hPair⟩ := nonDanglingIncident_eq_pair data hNd hSurvives hIncident
  have hOtherMem : other ∈ nonDanglingIncident data vertex := by
    rw [hPair]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  obtain ⟨hOther, hOtherInc⟩ := (mem_nonDanglingIncident data vertex other).mp hOtherMem
  have hIndex := (DivalentSourceLocal.indices_eq_of_ramification_zero data hNoGlue
    vertex hNd hR ⟨edge, hIncident⟩ ⟨other, hOtherInc⟩
    (fun h ↦ hNe (congrArg Subtype.val h).symm) hSurvives hOther).1
  apply Finset.eq_of_subset_of_card_le
  · obtain ⟨hMember, hRel⟩ := (incident_iff_target_mem_and_rel data edge vertex).mp hIncident
    intro sheet hSheet
    exact ((data.vertexPartition vertex.1.1).mem_block_iff _ _).mpr
      (hRel.trans ((refines_of_mem_incidentEdges data hMember).rel
        (((data.edgePartition edge.1.1).mem_block_iff _ _).mp hSheet)))
  · exact hIndex.ge

section AnyWallIncoming

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {contracted : target.edges}

namespace AnyWall

include fd

/-- Vanishing target change at the original endpoint forces zero local
ramification above it. This is the only use of the four-valent wall below, so
every statement in this section is stated at an arbitrary wall and carries that
vanishing as a hypothesis. -/
theorem localRamification_eq_zero_at_endpoint (vertex : data.SourceVertex)
    (hChange : data.targetChange vertex.1.1 = 0) :
    data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 0 := by
  apply localRamification_eq_zero_of_targetChange_zero data fd.valid
  exact hChange

/-- The paper's local no-return assertion on literal incoming occurrences.
It is derived from full-dimensionality and the vanishing target change at the
endpoint, not assumed as a source-picture or family-membership receipt. -/
theorem sourceEdge_eq_of_same_target_at_endpoint (vertex : data.SourceVertex)
    (hChange : data.targetChange vertex.1.1 = 0)
    (first second : data.SourceEdge)
    (hFirst : ¬ IsDangling data first) (hSecond : ¬ IsDangling data second)
    (hFirstInc : Incident data first vertex) (hSecondInc : Incident data second vertex)
    (hTarget : first.1.1 = second.1.1) : first = second := by
  have hR := localRamification_eq_zero_at_endpoint data fd vertex hChange
  rcases fd.nonDanglingValency_trichotomy vertex with hZero | hTwo | hThree
  · have hMem := (mem_nonDanglingIncident data vertex first).mpr ⟨hFirst, hFirstInc⟩
    have hPos := Finset.card_pos.mpr ⟨first, hMem⟩
    rw [card_nonDanglingIncident, hZero] at hPos
    omega
  · exact DivalentSourceLocal.sourceEdge_eq_of_same_target data fd.danglingEdgeNoGlue
      vertex hTwo (by omega) first second hFirst hSecond hFirstInc hSecondInc hTarget
  · exact sourceEdge_eq_of_same_target_of_nd3_r0 data fd.danglingEdgeNoGlue vertex
      hThree hR first second hFirst hSecond hFirstInc hSecondInc hTarget

/-- In particular, the pruned preimage of the actual contracted occurrence
has at most one incidence at each incoming endpoint source vertex. This is
the local degree bound needed by the auxiliary r0 pruned-fibre census. -/
theorem contracted_incidence_card_le_one_at_endpoint (vertex : data.SourceVertex)
    (hChange : data.targetChange vertex.1.1 = 0) :
    ((nonDanglingIncident data vertex).filter
      fun edge : data.SourceEdge ↦ edge.1.1 = contracted).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro first hFirst second hSecond
  obtain ⟨hFirstInc, hFirstTarget⟩ := Finset.mem_filter.mp hFirst
  obtain ⟨hSecondInc, hSecondTarget⟩ := Finset.mem_filter.mp hSecond
  obtain ⟨hFirstSurvives, hFirstInc⟩ := (mem_nonDanglingIncident data vertex first).mp hFirstInc
  obtain ⟨hSecondSurvives, hSecondInc⟩ := (mem_nonDanglingIncident data vertex second).mp hSecondInc
  exact sourceEdge_eq_of_same_target_at_endpoint data fd vertex hChange
    first second hFirstSurvives hSecondSurvives hFirstInc hSecondInc
    (hFirstTarget.trans hSecondTarget.symm)

/-- The exact sheet-set part of the incoming auxiliary r0-nd2 census.
Applied to an internal edge and either exterior survivor, this yields the
paper's equalities `eα = Au = e′ = Av = eβ`, once the two-vertex fibre
alternative is established. -/
theorem block_eq_of_survives_nd2_at_endpoint (vertex : data.SourceVertex)
    (hChange : data.targetChange vertex.1.1 = 0)
    (hNd : nonDanglingValency data vertex = 2)
    (edge : data.SourceEdge) (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge vertex) :
    (data.edgePartition edge.1.1).block edge.1.2 =
      (data.vertexPartition vertex.1.1).block vertex.1.2 :=
  block_eq_of_survives_nd2_r0 data fd.danglingEdgeNoGlue vertex hNd
    (localRamification_eq_zero_at_endpoint data fd vertex hChange)
    edge hSurvives hIncident

end AnyWall

end AnyWallIncoming

section Incoming

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : W4TargetPairings.FourStar (GraphContraction.contract target hab hOne) ⟨a, hab⟩)

include fd hc hab hOne star

/-- The four-valent wall is exactly a contraction of an occurrence between two
change-free trivalent target vertices, so it supplies the hypothesis of every
`AnyWall` statement above. This is the only use of the `FourStar` in this
module. -/
theorem changeZero_of_fourStar (place : target.V) (hPlace : place = a ∨ place = b) :
    data.targetChange place = 0 := by
  obtain ⟨_, _, hA, hB⟩ := W4Bridge.endpoints_trivalent_of_fourStar data hc hab hOne
    fd.valid fd.changeMinimal star
  exact hPlace.elim (fun h ↦ h ▸ hA) (fun h ↦ h ▸ hB)

/-- The actual W4 target contraction forces zero local ramification above
both original endpoints, before choosing any candidate or source picture. -/
theorem localRamification_eq_zero_at_endpoint (vertex : data.SourceVertex)
    (hAbove : vertex.1.1 = a ∨ vertex.1.1 = b) :
    data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 0 :=
  AnyWall.localRamification_eq_zero_at_endpoint data fd vertex
    (changeZero_of_fourStar data fd hc hab hOne star _ hAbove)

/-- The four-valent form of `AnyWall.sourceEdge_eq_of_same_target_at_endpoint`. -/
theorem sourceEdge_eq_of_same_target_at_endpoint (vertex : data.SourceVertex)
    (hAbove : vertex.1.1 = a ∨ vertex.1.1 = b)
    (first second : data.SourceEdge)
    (hFirst : ¬ IsDangling data first) (hSecond : ¬ IsDangling data second)
    (hFirstInc : Incident data first vertex) (hSecondInc : Incident data second vertex)
    (hTarget : first.1.1 = second.1.1) : first = second :=
  AnyWall.sourceEdge_eq_of_same_target_at_endpoint data fd vertex
    (changeZero_of_fourStar data fd hc hab hOne star _ hAbove)
    first second hFirst hSecond hFirstInc hSecondInc hTarget

/-- The four-valent form of
`AnyWall.contracted_incidence_card_le_one_at_endpoint`. -/
theorem contracted_incidence_card_le_one_at_endpoint (vertex : data.SourceVertex)
    (hAbove : vertex.1.1 = a ∨ vertex.1.1 = b) :
    ((nonDanglingIncident data vertex).filter
      fun edge : data.SourceEdge ↦ edge.1.1 = contracted).card ≤ 1 :=
  AnyWall.contracted_incidence_card_le_one_at_endpoint data fd vertex
    (changeZero_of_fourStar data fd hc hab hOne star _ hAbove)

/-- The four-valent form of `AnyWall.block_eq_of_survives_nd2_at_endpoint`. -/
theorem block_eq_of_survives_nd2_at_endpoint (vertex : data.SourceVertex)
    (hAbove : vertex.1.1 = a ∨ vertex.1.1 = b)
    (hNd : nonDanglingValency data vertex = 2)
    (edge : data.SourceEdge) (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge vertex) :
    (data.edgePartition edge.1.1).block edge.1.2 =
      (data.vertexPartition vertex.1.1).block vertex.1.2 :=
  AnyWall.block_eq_of_survives_nd2_at_endpoint data fd vertex
    (changeZero_of_fourStar data fd hc hab hOne star _ hAbove) hNd edge hSurvives hIncident

end Incoming

end DraismaVargas.LocalCases.W4IncomingCensus
