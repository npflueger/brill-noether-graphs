import DraismaVargas.LocalCases.W4IncomingCensus
import DraismaVargas.LocalCases.PrunedFibreTree

/-!
# The literal one-vertex or one-edge incoming W4 pruned fibre

Source: Draisma--Vargas Part I (arXiv:1909.12924), Section 6, Case
`{aux-r0}`, using Lemmas `lemma-vertices-in-GqA0` and `lemma-edges-in-GqA0` on
the vertices and edges of the pruned fibre. The existing `PrunedDivalentFibre`
walk argument handles only nd2 wall fibres. Here the incoming W4 endpoint
uniqueness works for both nd2 and nd3 constituents, so no wall-nd2
hypothesis is needed. Connectivity comes from the existing actual
`sourceVertexMap_eq_iff_surviving_walk`, not a displayed fibre or matching
receipt. No source-partition identification or candidate matching is claimed.

**Wall arity.**  The walk argument needs zero local ramification at both
original endpoints, and nothing else about the wall.  The content is therefore
stated in the `AnyWall` namespace under
`hChangeZero : ∀ place, place = a ∨ place = b → data.targetChange place = 0`;
the original names are retained as their four-valent forms, which discharge
that hypothesis from the star through
`W4IncomingCensus.changeZero_of_fourStar`.  Note that a W3 r1 wall does *not*
satisfy `hChangeZero`: one of its endpoints carries the whole unit of target
change, which is why the r1 cases use `PrunedDivalentFibre` instead.
-/

namespace DraismaVargas.LocalCases.W4IncomingPrunedFibre

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4StableSource StableLocalProperties WallDegeneration ClassInjectivity
open PrunedContractionFibre PrunedFibreValency PrunedFibreTree FullContractionFibre
open FullDimensionalSource

variable {target : CFGraph} {degree : ℕ}

section AnyWallIncoming

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (hChangeZero : ∀ place : target.V, place = a ∨ place = b → data.targetChange place = 0)

/-- The two literal ends of an internal occurrence lie above the original
ordered target endpoints, and both map to the specified contracted source
vertex. In particular they are distinct. -/
theorem internalEdge_endpoints
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (edge : data.SourceEdge) (hEdge : edge ∈ internalEdges data hc hab hOne vertex) :
    (data.sourceEnds edge).1.1.1 = a ∧ (data.sourceEnds edge).2.1.1 = b ∧
      sourceVertexMap data hc hab hOne (data.sourceEnds edge).1 = vertex ∧
      sourceVertexMap data hc hab hOne (data.sourceEnds edge).2 = vertex ∧
      (data.sourceEnds edge).1 ≠ (data.sourceEnds edge).2 := by
  obtain ⟨_, hTarget, hMap⟩ := (mem_internalEdges data hc hab hOne vertex edge).mp hEdge
  have hLeft : (data.sourceEnds edge).1.1.1 = a := by
    change (edge.1.1 : target.V × target.V).1 = a
    rw [hTarget, hc]
  have hRight : (data.sourceEnds edge).2.1.1 = b := by
    change (edge.1.1 : target.V × target.V).2 = b
    rw [hTarget, hc]
  refine ⟨hLeft, hRight, hMap, ?_, ?_⟩
  · exact (sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hOne edge hTarget).symm.trans hMap
  · intro h
    exact hab (hLeft.symm.trans ((congrArg (fun point : data.SourceVertex ↦ point.1.1) h).trans hRight))

namespace AnyWall

include fd hc hab hOne hChangeZero

omit hab hOne in
/-- The endpoint location is forced by actual incidence with the contracted
occurrence; it need not be supplied in a fibre walk. -/
theorem contracted_sourceEdge_eq_of_incident
    (point : data.SourceVertex) (first second : data.SourceEdge)
    (hFirstTarget : first.1.1 = contracted) (hSecondTarget : second.1.1 = contracted)
    (hFirst : ¬ IsDangling data first) (hSecond : ¬ IsDangling data second)
    (hFirstInc : Incident data first point) (hSecondInc : Incident data second point) :
    first = second := by
  have hAt := ((incident_iff_target_mem_and_rel data first point).mp hFirstInc).1
  rw [hFirstTarget] at hAt
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hAt
  rw [hc] at hAt
  exact W4IncomingCensus.AnyWall.sourceEdge_eq_of_same_target_at_endpoint data fd
    point (hChangeZero _ (hAt.imp Eq.symm Eq.symm)) first second hFirst hSecond
    hFirstInc hSecondInc (hFirstTarget.trans hSecondTarget.symm)

omit hab hOne in
/-- Equality propagates along an actual pruned walk, using literal source
occurrences at every step, without an assumption about the wall valency. -/
theorem sourceEdge_eq_of_surviving_walk
    (first : data.SourceEdge) (hFirstTarget : first.1.1 = contracted)
    (hFirst : ¬ IsDangling data first)
    (left right : data.SourceVertex) (hFirstInc : Incident data first left)
    (hWalk : Relation.ReflTransGen (SurvivingFibreStep data contracted) left right)
    (second : data.SourceEdge) (hSecondTarget : second.1.1 = contracted)
    (hSecond : ¬ IsDangling data second) (hSecondInc : Incident data second right) :
    first = second := by
  induction hWalk generalizing second with
  | refl =>
    exact contracted_sourceEdge_eq_of_incident data fd hc hChangeZero left first second
      hFirstTarget hSecondTarget hFirst hSecond hFirstInc hSecondInc
  | @tail previous last hWalk hStep ih =>
    obtain ⟨edge, hTarget, hSurvives, hEnds⟩ := hStep
    exact (ih edge hTarget hSurvives (incident_of_sourceEnds data hEnds)).trans
      (contracted_sourceEdge_eq_of_incident data fd hc hChangeZero last edge second
        hTarget hSecondTarget hSurvives hSecond
        (incident_of_sourceEnds data hEnds.symm) hSecondInc)

/-- Each actual pruned contraction fibre has at most one surviving internal
occurrence. Its connectedness is derived by the existing walk-pruning theorem. -/
theorem internalEdges_subsingleton (vertex : (contractDatum data hc hab hOne).SourceVertex) :
    ∀ first ∈ internalEdges data hc hab hOne vertex,
      ∀ second ∈ internalEdges data hc hab hOne vertex, first = second := by
  intro first hFirst second hSecond
  obtain ⟨hFirstSurvives, hFirstTarget, hFirstMap⟩ :=
    (mem_internalEdges data hc hab hOne vertex first).mp hFirst
  obtain ⟨hSecondSurvives, hSecondTarget, hSecondMap⟩ :=
    (mem_internalEdges data hc hab hOne vertex second).mp hSecond
  have hWalk := (sourceVertexMap_eq_iff_surviving_walk data hc hab hOne
    (nonDanglingValency_ne_zero_of_incident data hFirstSurvives (Or.inl rfl))
    (nonDanglingValency_ne_zero_of_incident data hSecondSurvives (Or.inl rfl))).mp
      (hFirstMap.trans hSecondMap.symm)
  exact sourceEdge_eq_of_surviving_walk data fd hc hChangeZero first hFirstTarget
    hFirstSurvives (data.sourceEnds first).1 (data.sourceEnds second).1 (Or.inl rfl)
    hWalk second hSecondTarget hSecondSurvives (Or.inl rfl)

theorem internalEdges_card_le_one (vertex : (contractDatum data hc hab hOne).SourceVertex) :
    (internalEdges data hc hab hOne vertex).card ≤ 1 :=
  Finset.card_le_one.mpr (internalEdges_subsingleton data fd hc hab hOne hChangeZero vertex)

/-- Every active vertex meets the unique internal occurrence, when present. -/
theorem internalEdge_incident_of_mem_activeFibre
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (edge : data.SourceEdge) (hEdge : edge ∈ internalEdges data hc hab hOne vertex)
    (point : data.SourceVertex) (hPoint : point ∈ activeFibreVertices data hc hab hOne vertex) :
    Incident data edge point := by
  obtain ⟨hSurvives, hTarget, hEdgeMap⟩ := (mem_internalEdges data hc hab hOne vertex edge).mp hEdge
  obtain ⟨hPointMap, hActive⟩ := (mem_activeFibreVertices data hc hab hOne vertex point).mp hPoint
  have hWalk := (sourceVertexMap_eq_iff_surviving_walk data hc hab hOne
    (nonDanglingValency_ne_zero_of_incident data hSurvives (Or.inl rfl)) hActive).mp
      (hEdgeMap.trans hPointMap.symm)
  cases hWalk with
  | refl => exact Or.inl rfl
  | @tail previous last hWalk hStep =>
    obtain ⟨step, hStepTarget, hStepSurvives, hEnds⟩ := hStep
    have hLast := incident_of_sourceEnds data hEnds.symm
    have hEq := sourceEdge_eq_of_surviving_walk data fd hc hChangeZero edge hTarget
      hSurvives (data.sourceEnds edge).1 point (Or.inl rfl)
      (hWalk.tail ⟨step, hStepTarget, hStepSurvives, hEnds⟩)
      step hStepTarget hStepSurvives hLast
    exact hEq.symm ▸ hLast

/-- The nonempty-edge alternative records the exact two endpoint vertices,
not just the number two. -/
theorem activeFibreVertices_eq_endpoints
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (edge : data.SourceEdge) (hEdge : edge ∈ internalEdges data hc hab hOne vertex) :
    activeFibreVertices data hc hab hOne vertex =
      {(data.sourceEnds edge).1, (data.sourceEnds edge).2} := by
  classical
  have hEnds := (sourceEnds_mem_activeFibre_iff data hc hab hOne vertex edge).mpr hEdge
  ext point
  constructor
  · intro hPoint
    have hInc := internalEdge_incident_of_mem_activeFibre data fd hc hab hOne hChangeZero
      vertex edge hEdge point hPoint
    exact Finset.mem_insert.mpr (hInc.imp Eq.symm (fun h ↦ Finset.mem_singleton.mpr h.symm))
  · intro hPoint
    rcases Finset.mem_insert.mp hPoint with rfl | hPoint
    · exact hEnds.1
    · exact (Finset.mem_singleton.mp hPoint) ▸ hEnds.2

/-- The complete nonempty pruned-fibre alternative: one literal vertex with
no internal edge, or one literal surviving occurrence with its two distinct
endpoint vertices. No displayed graph or connectedness receipt is assumed. -/
theorem census (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNonempty : (activeFibreVertices data hc hab hOne vertex).Nonempty) :
    (∃ point : data.SourceVertex,
      activeFibreVertices data hc hab hOne vertex = {point} ∧
      internalEdges data hc hab hOne vertex = ∅) ∨
    (∃ edge : data.SourceEdge,
      internalEdges data hc hab hOne vertex = {edge} ∧
      activeFibreVertices data hc hab hOne vertex =
        {(data.sourceEnds edge).1, (data.sourceEnds edge).2} ∧
      (data.sourceEnds edge).1 ≠ (data.sourceEnds edge).2) := by
  classical
  by_cases hEmpty : internalEdges data hc hab hOne vertex = ∅
  · have hBound := activeFibreVertices_card_le_internalEdges_card_add_one
      data hc hab hOne vertex hNonempty
    rw [hEmpty, Finset.card_empty] at hBound
    have hPos := Finset.card_pos.mpr hNonempty
    obtain ⟨point, hPoint⟩ := Finset.card_eq_one.mp (show
      (activeFibreVertices data hc hab hOne vertex).card = 1 by omega)
    exact Or.inl ⟨point, hPoint, hEmpty⟩
  · obtain ⟨edge, hEdge⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
    have hSingleton : internalEdges data hc hab hOne vertex = {edge} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨hEdge, fun other hOther ↦
        internalEdges_subsingleton data fd hc hab hOne hChangeZero vertex other hOther edge hEdge⟩
    exact Or.inr ⟨edge, hSingleton,
      activeFibreVertices_eq_endpoints data fd hc hab hOne hChangeZero vertex edge hEdge,
      (internalEdge_endpoints data hc hab hOne vertex edge hEdge).2.2.2.2⟩

/-- The cardinality version follows from the exact occurrence census. -/
theorem activeFibreVertices_card_one_or_two
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNonempty : (activeFibreVertices data hc hab hOne vertex).Nonempty) :
    (activeFibreVertices data hc hab hOne vertex).card = 1 ∨
      (activeFibreVertices data hc hab hOne vertex).card = 2 := by
  classical
  rcases census data fd hc hab hOne hChangeZero vertex hNonempty with ⟨point, hPoint, _⟩ |
    ⟨edge, _, hEnds, hNe⟩
  · exact Or.inl (by rw [hPoint, Finset.card_singleton])
  · exact Or.inr (by rw [hEnds, Finset.card_pair hNe])

/-- A surviving wall block supplies the nonemptiness needed by the census
through the existing actual occurrence accounting. Compatibility is used
only here, not to assume pruned connectivity or the one-edge conclusion. -/
theorem census_of_nonzero
    (hCompat : DanglingCompatible data hc hab hOne)
    (block : (mergedPartition data a b).Blocks)
    (hNonzero : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) ≠ 0) :
    (∃ point : data.SourceVertex,
      activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block) = {point} ∧
      internalEdges data hc hab hOne (mergedVertex data hc hab hOne block) = ∅) ∨
    (∃ edge : data.SourceEdge,
      internalEdges data hc hab hOne (mergedVertex data hc hab hOne block) = {edge} ∧
      activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block) =
        {(data.sourceEnds edge).1, (data.sourceEnds edge).2} ∧
      (data.sourceEnds edge).1 ≠ (data.sourceEnds edge).2) :=
  census data fd hc hab hOne hChangeZero _
    (activeFibreVertices_nonempty_of_nonDanglingValency_ne_zero data hc hab hOne hCompat _ hNonzero)

end AnyWall

end AnyWallIncoming

section Incoming

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩)

include fd hc hab hOne star

/-- The four-valent form of `AnyWall.contracted_sourceEdge_eq_of_incident`. -/
theorem contracted_sourceEdge_eq_of_incident
    (point : data.SourceVertex) (first second : data.SourceEdge)
    (hFirstTarget : first.1.1 = contracted) (hSecondTarget : second.1.1 = contracted)
    (hFirst : ¬ IsDangling data first) (hSecond : ¬ IsDangling data second)
    (hFirstInc : Incident data first point) (hSecondInc : Incident data second point) :
    first = second :=
  AnyWall.contracted_sourceEdge_eq_of_incident data fd hc
    (W4IncomingCensus.changeZero_of_fourStar data fd hc hab hOne star)
    point first second hFirstTarget hSecondTarget hFirst hSecond hFirstInc hSecondInc

/-- The four-valent form of `AnyWall.sourceEdge_eq_of_surviving_walk`. -/
theorem sourceEdge_eq_of_surviving_walk
    (first : data.SourceEdge) (hFirstTarget : first.1.1 = contracted)
    (hFirst : ¬ IsDangling data first)
    (left right : data.SourceVertex) (hFirstInc : Incident data first left)
    (hWalk : Relation.ReflTransGen (SurvivingFibreStep data contracted) left right)
    (second : data.SourceEdge) (hSecondTarget : second.1.1 = contracted)
    (hSecond : ¬ IsDangling data second) (hSecondInc : Incident data second right) :
    first = second :=
  AnyWall.sourceEdge_eq_of_surviving_walk data fd hc
    (W4IncomingCensus.changeZero_of_fourStar data fd hc hab hOne star)
    first hFirstTarget hFirst left right hFirstInc hWalk second hSecondTarget hSecond hSecondInc

/-- The four-valent form of `AnyWall.internalEdges_subsingleton`. -/
theorem internalEdges_subsingleton (vertex : (contractDatum data hc hab hOne).SourceVertex) :
    ∀ first ∈ internalEdges data hc hab hOne vertex,
      ∀ second ∈ internalEdges data hc hab hOne vertex, first = second :=
  AnyWall.internalEdges_subsingleton data fd hc hab hOne
    (W4IncomingCensus.changeZero_of_fourStar data fd hc hab hOne star) vertex

/-- The four-valent form of `AnyWall.internalEdges_card_le_one`. -/
theorem internalEdges_card_le_one (vertex : (contractDatum data hc hab hOne).SourceVertex) :
    (internalEdges data hc hab hOne vertex).card ≤ 1 :=
  AnyWall.internalEdges_card_le_one data fd hc hab hOne
    (W4IncomingCensus.changeZero_of_fourStar data fd hc hab hOne star) vertex

/-- The four-valent form of `AnyWall.internalEdge_incident_of_mem_activeFibre`. -/
theorem internalEdge_incident_of_mem_activeFibre
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (edge : data.SourceEdge) (hEdge : edge ∈ internalEdges data hc hab hOne vertex)
    (point : data.SourceVertex) (hPoint : point ∈ activeFibreVertices data hc hab hOne vertex) :
    Incident data edge point :=
  AnyWall.internalEdge_incident_of_mem_activeFibre data fd hc hab hOne
    (W4IncomingCensus.changeZero_of_fourStar data fd hc hab hOne star) vertex edge hEdge point hPoint

/-- The four-valent form of `AnyWall.activeFibreVertices_eq_endpoints`. -/
theorem activeFibreVertices_eq_endpoints
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (edge : data.SourceEdge) (hEdge : edge ∈ internalEdges data hc hab hOne vertex) :
    activeFibreVertices data hc hab hOne vertex =
      {(data.sourceEnds edge).1, (data.sourceEnds edge).2} :=
  AnyWall.activeFibreVertices_eq_endpoints data fd hc hab hOne
    (W4IncomingCensus.changeZero_of_fourStar data fd hc hab hOne star) vertex edge hEdge

/-- The four-valent form of `AnyWall.census`. -/
theorem census (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNonempty : (activeFibreVertices data hc hab hOne vertex).Nonempty) :
    (∃ point : data.SourceVertex,
      activeFibreVertices data hc hab hOne vertex = {point} ∧
      internalEdges data hc hab hOne vertex = ∅) ∨
    (∃ edge : data.SourceEdge,
      internalEdges data hc hab hOne vertex = {edge} ∧
      activeFibreVertices data hc hab hOne vertex =
        {(data.sourceEnds edge).1, (data.sourceEnds edge).2} ∧
      (data.sourceEnds edge).1 ≠ (data.sourceEnds edge).2) :=
  AnyWall.census data fd hc hab hOne
    (W4IncomingCensus.changeZero_of_fourStar data fd hc hab hOne star) vertex hNonempty

/-- The four-valent form of `AnyWall.activeFibreVertices_card_one_or_two`. -/
theorem activeFibreVertices_card_one_or_two
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNonempty : (activeFibreVertices data hc hab hOne vertex).Nonempty) :
    (activeFibreVertices data hc hab hOne vertex).card = 1 ∨
      (activeFibreVertices data hc hab hOne vertex).card = 2 :=
  AnyWall.activeFibreVertices_card_one_or_two data fd hc hab hOne
    (W4IncomingCensus.changeZero_of_fourStar data fd hc hab hOne star) vertex hNonempty

/-- The four-valent form of `AnyWall.census_of_nonzero`. -/
theorem census_of_nonzero
    (hCompat : DanglingCompatible data hc hab hOne)
    (block : (mergedPartition data a b).Blocks)
    (hNonzero : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) ≠ 0) :
    (∃ point : data.SourceVertex,
      activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block) = {point} ∧
      internalEdges data hc hab hOne (mergedVertex data hc hab hOne block) = ∅) ∨
    (∃ edge : data.SourceEdge,
      internalEdges data hc hab hOne (mergedVertex data hc hab hOne block) = {edge} ∧
      activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block) =
        {(data.sourceEnds edge).1, (data.sourceEnds edge).2} ∧
      (data.sourceEnds edge).1 ≠ (data.sourceEnds edge).2) :=
  AnyWall.census_of_nonzero data fd hc hab hOne
    (W4IncomingCensus.changeZero_of_fourStar data fd hc hab hOne star) hCompat block hNonzero

end Incoming

end DraismaVargas.LocalCases.W4IncomingPrunedFibre
