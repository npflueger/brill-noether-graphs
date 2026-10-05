module

public import DraismaVargas.LocalCases.W4IncomingPrunedFibre

@[expose] public section

/-!
# Side-conditioned actual W4 pruned fibres

Source: Draisma--Vargas Part I, Case `{aux-r0}`. All flags below are literal
retained source occurrences. Their membership in `boundaryEdges` and their
incidences with incoming endpoints are geometric data, not a fibre-picture
or candidate-membership assumption. The exact one-vertex/one-edge census
and retained-occurrence accounting determine their endpoint configurations.

**Wall arity.**  Everything below rests on the pruned-fibre census, so it needs
zero target change at both original endpoints and nothing else about the wall.
The content is stated in the `AnyWall` namespace under
`hChangeZero : ∀ place, place = a ∨ place = b → data.targetChange place = 0`;
the original names are retained as their four-valent forms, discharging that
hypothesis from the star through `W4IncomingCensus.changeZero_of_fourStar`.
The retained-flag bookkeeping above the namespace never needed either.
-/

namespace DraismaVargas.LocalCases.W4IncomingSideCensus

open DraismaVargas.Infrastructure
open GluingContraction ContractionRamification ContractionFibre
open W4StableSource ClassInjectivity StableLocalProperties WallDegeneration
open PrunedFibreValency PrunedFibreTree FullContractionFibre FullDimensionalSource

variable {target : CFGraph} {degree : ℕ}

section AnyWallIncoming

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (hChangeZero : ∀ place : target.V, place = a ∨ place = b → data.targetChange place = 0)

/-- A retained occurrence cannot meet two distinct vertices of one fibre:
its contracted source occurrence remains loopless. -/
theorem boundary_endpoint_unique
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (edge : data.SourceEdge) (hEdge : edge ∈ boundaryEdges data hc hab hOne vertex)
    (first second : data.SourceVertex)
    (hFirstMap : sourceVertexMap data hc hab hOne first = vertex)
    (hSecondMap : sourceVertexMap data hc hab hOne second = vertex)
    (hFirst : Incident data edge first) (hSecond : Incident data edge second) : first = second := by
  have hNe := ((mem_boundaryEdges data hc hab hOne vertex edge).mp hEdge).2.1
  have hNoLoop := sourceVertexMap_sourceEnds_ne data hc hab hOne ⟨edge, hNe⟩
  rcases hFirst with hFirst | hFirst <;> rcases hSecond with hSecond | hSecond
  · exact hFirst.symm.trans hSecond
  · exact False.elim (hNoLoop (by rw [hFirst, hSecond, hFirstMap, hSecondMap]))
  · exact False.elim (hNoLoop (by rw [hFirst, hSecond, hFirstMap, hSecondMap]))
  · exact hFirst.symm.trans hSecond

/-- A literal surviving retained flag makes its incident fibre endpoint active. -/
theorem active_of_boundary_incident
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (edge : data.SourceEdge) (hEdge : edge ∈ boundaryEdges data hc hab hOne vertex)
    (point : data.SourceVertex) (hMap : sourceVertexMap data hc hab hOne point = vertex)
    (hIncident : Incident data edge point) :
    point ∈ activeFibreVertices data hc hab hOne vertex :=
  (mem_activeFibreVertices data hc hab hOne vertex point).mpr ⟨hMap,
    nonDanglingValency_ne_zero_of_incident data
      ((mem_boundaryEdges data hc hab hOne vertex edge).mp hEdge).1 hIncident⟩

/-- The retained occurrences incident to one actual fibre endpoint. -/
noncomputable def boundaryAt
    (vertex : (contractDatum data hc hab hOne).SourceVertex) (point : data.SourceVertex) :
    Finset data.SourceEdge := by
  classical
  exact (boundaryEdges data hc hab hOne vertex).filter fun edge ↦ Incident data edge point

/-- The two distinct retained flags of an nd2 wall block exhaust its
boundary, by actual contraction accounting. -/
theorem boundary_eq_pair (hCompat : DanglingCompatible data hc hab hOne)
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne) vertex = 2)
    (first second : data.SourceEdge) (hNe : first ≠ second)
    (hFirst : first ∈ boundaryEdges data hc hab hOne vertex)
    (hSecond : second ∈ boundaryEdges data hc hab hOne vertex) :
    boundaryEdges data hc hab hOne vertex = {first, second} := by
  classical
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro edge hEdge
    rcases Finset.mem_insert.mp hEdge with rfl | hEdge
    · exact hFirst
    · exact (Finset.mem_singleton.mp hEdge) ▸ hSecond
  · rw [card_boundaryEdges data hc hab hOne hCompat, hNd, Finset.card_pair hNe]

namespace AnyWall

include fd hc hab hOne hChangeZero

/-- On either target side a pruned fibre has at most one active vertex. -/
theorem eq_of_same_side (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (first second : data.SourceVertex)
    (hFirst : first ∈ activeFibreVertices data hc hab hOne vertex)
    (hSecond : second ∈ activeFibreVertices data hc hab hOne vertex)
    (hSide : first.1.1 = second.1.1) : first = second := by
  classical
  rcases W4IncomingPrunedFibre.AnyWall.census data fd hc hab hOne hChangeZero vertex
    ⟨first, hFirst⟩ with ⟨point, hPoint, _⟩ | ⟨edge, hEdge, hEnds, _⟩
  · rw [hPoint, Finset.mem_singleton] at hFirst hSecond
    exact hFirst.trans hSecond.symm
  · have hMember : edge ∈ internalEdges data hc hab hOne vertex := by rw [hEdge]; simp
    obtain ⟨hA, hB, _, _, _⟩ :=
      W4IncomingPrunedFibre.internalEdge_endpoints data hc hab hOne vertex edge hMember
    rw [hEnds, Finset.mem_insert, Finset.mem_singleton] at hFirst hSecond
    rcases hFirst with rfl | rfl <;> rcases hSecond with rfl | rfl
    · rfl
    · exact False.elim (hab (hA.symm.trans (hSide.trans hB)))
    · exact False.elim (hab (hA.symm.trans (hSide.symm.trans hB)))
    · rfl

/-- Opposite active sides force the unique internal occurrence and its
literal incidences with the two prescribed source vertices. -/
theorem internalEdge_of_opposite_sides
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (first second : data.SourceVertex)
    (hFirst : first ∈ activeFibreVertices data hc hab hOne vertex)
    (hSecond : second ∈ activeFibreVertices data hc hab hOne vertex)
    (hSide : first.1.1 ≠ second.1.1) :
    ∃ edge : data.SourceEdge, internalEdges data hc hab hOne vertex = {edge} ∧
      activeFibreVertices data hc hab hOne vertex = {first, second} ∧
      Incident data edge first ∧ Incident data edge second := by
  classical
  have hNe : first ≠ second := fun h ↦ hSide (congrArg (fun p : data.SourceVertex ↦ p.1.1) h)
  rcases W4IncomingPrunedFibre.AnyWall.census data fd hc hab hOne hChangeZero vertex
    ⟨first, hFirst⟩ with ⟨point, hPoint, _⟩ | ⟨edge, hEdge, hEnds, hEndsNe⟩
  · rw [hPoint, Finset.mem_singleton] at hFirst hSecond
    exact False.elim (hNe (hFirst.trans hSecond.symm))
  · have hMember : edge ∈ internalEdges data hc hab hOne vertex := by rw [hEdge]; simp
    refine ⟨edge, hEdge, ?_,
      W4IncomingPrunedFibre.AnyWall.internalEdge_incident_of_mem_activeFibre data fd hc hab hOne
        hChangeZero vertex edge hMember first hFirst,
      W4IncomingPrunedFibre.AnyWall.internalEdge_incident_of_mem_activeFibre data fd hc hab hOne
        hChangeZero vertex edge hMember second hSecond⟩
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro point hPoint
      rcases Finset.mem_insert.mp hPoint with rfl | hPoint
      · exact hFirst
      · exact (Finset.mem_singleton.mp hPoint) ▸ hSecond
    · rw [hEnds, Finset.card_pair hEndsNe, Finset.card_pair hNe]

/-- Each active vertex meets a retained boundary occurrence: it has at least
two surviving incidences, but at most one can be internal. -/
theorem exists_boundary_incident
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (point : data.SourceVertex) (hPoint : point ∈ activeFibreVertices data hc hab hOne vertex) :
    ∃ edge ∈ boundaryEdges data hc hab hOne vertex, Incident data edge point := by
  classical
  obtain ⟨hMap, hActive⟩ := (mem_activeFibreVertices data hc hab hOne vertex point).mp hPoint
  by_contra hNone
  have hTarget : ∀ edge ∈ nonDanglingIncident data point, edge.1.1 = contracted := by
    intro edge hEdge
    obtain ⟨hSurvives, hInc⟩ := (mem_nonDanglingIncident data point edge).mp hEdge
    by_contra hNe
    apply hNone
    refine ⟨edge, (mem_boundaryEdges data hc hab hOne vertex edge).mpr ⟨hSurvives, hNe, ?_⟩, hInc⟩
    exact hInc.imp (fun h ↦ (congrArg (sourceVertexMap data hc hab hOne) h).trans hMap)
      (fun h ↦ (congrArg (sourceVertexMap data hc hab hOne) h).trans hMap)
  have hBound : (nonDanglingIncident data point).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro first hFirst second hSecond
    have hFirstInfo := (mem_nonDanglingIncident data point first).mp hFirst
    have hSecondInfo := (mem_nonDanglingIncident data point second).mp hSecond
    exact W4IncomingPrunedFibre.AnyWall.contracted_sourceEdge_eq_of_incident data fd hc
      hChangeZero point first second (hTarget first hFirst) (hTarget second hSecond)
      hFirstInfo.1 hSecondInfo.1 hFirstInfo.2 hSecondInfo.2
  rw [card_nonDanglingIncident] at hBound
  have hCases := fd.nonDanglingValency_trichotomy point
  omega

/-- At an active endpoint, all surviving incidences are precisely its
retained boundary flags and the unique internal occurrence, when present. -/
theorem nonDanglingIncident_eq_insert_boundaryAt
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (internal : data.SourceEdge) (hInternal : internal ∈ internalEdges data hc hab hOne vertex)
    (point : data.SourceVertex) (hPoint : point ∈ activeFibreVertices data hc hab hOne vertex) :
    nonDanglingIncident data point = insert internal (boundaryAt data hc hab hOne vertex point) := by
  classical
  obtain ⟨hInternalSurvives, hInternalTarget, _⟩ :=
    (mem_internalEdges data hc hab hOne vertex internal).mp hInternal
  have hInternalInc := W4IncomingPrunedFibre.AnyWall.internalEdge_incident_of_mem_activeFibre
    data fd hc hab hOne hChangeZero vertex internal hInternal point hPoint
  have hMap := ((mem_activeFibreVertices data hc hab hOne vertex point).mp hPoint).1
  ext edge
  simp only [mem_nonDanglingIncident, Finset.mem_insert, boundaryAt, Finset.mem_filter]
  constructor
  · rintro ⟨hSurvives, hInc⟩
    by_cases hTarget : edge.1.1 = contracted
    · exact Or.inl (W4IncomingPrunedFibre.AnyWall.contracted_sourceEdge_eq_of_incident
        data fd hc hChangeZero point edge internal hTarget hInternalTarget
        hSurvives hInternalSurvives hInc hInternalInc)
    · exact Or.inr ⟨(mem_boundaryEdges data hc hab hOne vertex edge).mpr ⟨hSurvives, hTarget,
        hInc.imp (fun h ↦ (congrArg (sourceVertexMap data hc hab hOne) h).trans hMap)
          (fun h ↦ (congrArg (sourceVertexMap data hc hab hOne) h).trans hMap)⟩, hInc⟩
  · rintro (rfl | ⟨hBoundary, hInc⟩)
    · exact ⟨hInternalSurvives, hInternalInc⟩
    · exact ⟨((mem_boundaryEdges data hc hab hOne vertex edge).mp hBoundary).1, hInc⟩

/-- If the complete retained boundary meets just one active endpoint, the
pruned fibre is that singleton and has no internal surviving occurrence. -/
theorem singleton_of_boundary_incident
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (point : data.SourceVertex) (hPoint : point ∈ activeFibreVertices data hc hab hOne vertex)
    (hBoundary : ∀ edge ∈ boundaryEdges data hc hab hOne vertex, Incident data edge point) :
    activeFibreVertices data hc hab hOne vertex = {point} ∧
      internalEdges data hc hab hOne vertex = ∅ := by
  classical
  have hMap := ((mem_activeFibreVertices data hc hab hOne vertex point).mp hPoint).1
  have hSingleton : activeFibreVertices data hc hab hOne vertex = {point} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hPoint, ?_⟩
    intro other hOther
    obtain ⟨edge, hEdge, hInc⟩ :=
      exists_boundary_incident data fd hc hab hOne hChangeZero vertex other hOther
    exact boundary_endpoint_unique data hc hab hOne vertex edge hEdge other point
      ((mem_activeFibreVertices data hc hab hOne vertex other).mp hOther).1 hMap
      hInc (hBoundary edge hEdge)
  refine ⟨hSingleton, ?_⟩
  by_contra hNotEmpty
  obtain ⟨edge, hEdge⟩ := Finset.nonempty_iff_ne_empty.mpr hNotEmpty
  have hEnds := W4IncomingPrunedFibre.AnyWall.activeFibreVertices_eq_endpoints
    data fd hc hab hOne hChangeZero vertex edge hEdge
  have hNe := (W4IncomingPrunedFibre.internalEdge_endpoints data hc hab hOne vertex edge hEdge).2.2.2.2
  have hCard := congrArg Finset.card (hSingleton.symm.trans hEnds)
  rw [Finset.card_singleton, Finset.card_pair hNe] at hCard
  omega

/-- The source's nd2 same-side alternative: the two literal retained ends
coincide, and that common endpoint is the whole active fibre. -/
theorem nd2_same_side (hCompat : DanglingCompatible data hc hab hOne)
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne) vertex = 2)
    (first second : data.SourceEdge) (hNe : first ≠ second)
    (hFirst : first ∈ boundaryEdges data hc hab hOne vertex)
    (hSecond : second ∈ boundaryEdges data hc hab hOne vertex)
    (left right : data.SourceVertex)
    (hLeftMap : sourceVertexMap data hc hab hOne left = vertex)
    (hRightMap : sourceVertexMap data hc hab hOne right = vertex)
    (hLeftInc : Incident data first left) (hRightInc : Incident data second right)
    (hSide : left.1.1 = right.1.1) :
    left = right ∧ activeFibreVertices data hc hab hOne vertex = {left} ∧
      internalEdges data hc hab hOne vertex = ∅ ∧ nonDanglingValency data left = 2 := by
  classical
  have hLeft := active_of_boundary_incident data hc hab hOne vertex first hFirst left hLeftMap hLeftInc
  have hRight := active_of_boundary_incident data hc hab hOne vertex second hSecond right hRightMap hRightInc
  have hEqual := eq_of_same_side data fd hc hab hOne hChangeZero vertex left right hLeft hRight hSide
  have hBoundary := boundary_eq_pair data hc hab hOne hCompat vertex hNd first second hNe hFirst hSecond
  obtain ⟨hSingleton, hEmpty⟩ := singleton_of_boundary_incident data fd hc hab hOne hChangeZero
    vertex left hLeft (by
      intro edge hEdge
      rw [hBoundary, Finset.mem_insert, Finset.mem_singleton] at hEdge
      rcases hEdge with rfl | rfl
      · exact hLeftInc
      · exact hEqual.symm ▸ hRightInc)
  have hCount := sum_nonDanglingValency_activeFibre data hc hab hOne hCompat vertex
  rw [hSingleton, hEmpty, Finset.sum_singleton, Finset.card_empty, hNd] at hCount
  exact ⟨hEqual, hSingleton, hEmpty, by omega⟩

/-- The source's nd2 opposite-side alternative, including the actual
internal incidences and both incoming endpoint valencies. -/
theorem nd2_opposite_sides (hCompat : DanglingCompatible data hc hab hOne)
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne) vertex = 2)
    (first second : data.SourceEdge)
    (hFirst : first ∈ boundaryEdges data hc hab hOne vertex)
    (hSecond : second ∈ boundaryEdges data hc hab hOne vertex)
    (left right : data.SourceVertex)
    (hLeftMap : sourceVertexMap data hc hab hOne left = vertex)
    (hRightMap : sourceVertexMap data hc hab hOne right = vertex)
    (hLeftInc : Incident data first left) (hRightInc : Incident data second right)
    (hSide : left.1.1 ≠ right.1.1) :
    ∃ edge : data.SourceEdge, internalEdges data hc hab hOne vertex = {edge} ∧
      activeFibreVertices data hc hab hOne vertex = {left, right} ∧
      Incident data edge left ∧ Incident data edge right ∧
      nonDanglingValency data left = 2 ∧ nonDanglingValency data right = 2 := by
  classical
  have hLeft := active_of_boundary_incident data hc hab hOne vertex first hFirst left hLeftMap hLeftInc
  have hRight := active_of_boundary_incident data hc hab hOne vertex second hSecond right hRightMap hRightInc
  obtain ⟨edge, hEdge, hActive, hEdgeLeft, hEdgeRight⟩ :=
    internalEdge_of_opposite_sides data fd hc hab hOne hChangeZero vertex left right hLeft hRight hSide
  have hNe : left ≠ right := fun h ↦ hSide (congrArg (fun p : data.SourceVertex ↦ p.1.1) h)
  have hCount := sum_nonDanglingValency_activeFibre data hc hab hOne hCompat vertex
  rw [hActive, hEdge, Finset.sum_pair hNe, Finset.card_singleton, hNd] at hCount
  have hLeftNonzero := ((mem_activeFibreVertices data hc hab hOne vertex left).mp hLeft).2
  have hRightNonzero := ((mem_activeFibreVertices data hc hab hOne vertex right).mp hRight).2
  have hLeftCases := fd.nonDanglingValency_trichotomy left
  have hRightCases := fd.nonDanglingValency_trichotomy right
  exact ⟨edge, hEdge, hActive, hEdgeLeft, hEdgeRight, by omega, by omega⟩

/-- The source's nd3 singleton/pair-side alternative. The two retained
flags on one side meet the same actual vertex; the internal survivor meets
that nd3 vertex and the prescribed nd2 singleton-side vertex. -/
theorem nd3_singleton_side (hCompat : DanglingCompatible data hc hab hOne)
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne) vertex = 3)
    (first second third : data.SourceEdge) (hSecondThird : second ≠ third)
    (hFirst : first ∈ boundaryEdges data hc hab hOne vertex)
    (hSecond : second ∈ boundaryEdges data hc hab hOne vertex)
    (hThird : third ∈ boundaryEdges data hc hab hOne vertex)
    (single double other : data.SourceVertex)
    (hSingleMap : sourceVertexMap data hc hab hOne single = vertex)
    (hDoubleMap : sourceVertexMap data hc hab hOne double = vertex)
    (hOtherMap : sourceVertexMap data hc hab hOne other = vertex)
    (hFirstInc : Incident data first single) (hSecondInc : Incident data second double)
    (hThirdInc : Incident data third other)
    (hOpposite : single.1.1 ≠ double.1.1) (hSame : double.1.1 = other.1.1) :
    double = other ∧ ∃ edge : data.SourceEdge,
      internalEdges data hc hab hOne vertex = {edge} ∧
      activeFibreVertices data hc hab hOne vertex = {single, double} ∧
      Incident data edge single ∧ Incident data edge double ∧
      nonDanglingValency data single = 2 ∧ nonDanglingValency data double = 3 := by
  classical
  have hSingle := active_of_boundary_incident data hc hab hOne vertex first hFirst single hSingleMap hFirstInc
  have hDouble := active_of_boundary_incident data hc hab hOne vertex second hSecond double hDoubleMap hSecondInc
  have hOther := active_of_boundary_incident data hc hab hOne vertex third hThird other hOtherMap hThirdInc
  have hEqual := eq_of_same_side data fd hc hab hOne hChangeZero vertex double other hDouble hOther hSame
  obtain ⟨edge, hEdge, hActive, hEdgeSingle, hEdgeDouble⟩ :=
    internalEdge_of_opposite_sides data fd hc hab hOne hChangeZero vertex single double
      hSingle hDouble hOpposite
  have hEdgeMem : edge ∈ internalEdges data hc hab hOne vertex := by rw [hEdge]; simp
  obtain ⟨hEdgeSurvives, hEdgeTarget, _⟩ := (mem_internalEdges data hc hab hOne vertex edge).mp hEdgeMem
  have hSecondInfo := (mem_boundaryEdges data hc hab hOne vertex second).mp hSecond
  have hThirdInfo := (mem_boundaryEdges data hc hab hOne vertex third).mp hThird
  have hEdgeSecond : edge ≠ second := fun h ↦ hSecondInfo.2.1
    ((congrArg (fun e : data.SourceEdge ↦ e.1.1) h).symm.trans hEdgeTarget)
  have hEdgeThird : edge ≠ third := fun h ↦ hThirdInfo.2.1
    ((congrArg (fun e : data.SourceEdge ↦ e.1.1) h).symm.trans hEdgeTarget)
  have hSubset : {edge, second, third} ⊆ nonDanglingIncident data double := by
    intro item hItem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hItem
    rcases hItem with rfl | rfl | rfl
    · exact (mem_nonDanglingIncident data double _).mpr ⟨hEdgeSurvives, hEdgeDouble⟩
    · exact (mem_nonDanglingIncident data double _).mpr ⟨hSecondInfo.1, hSecondInc⟩
    · exact (mem_nonDanglingIncident data double _).mpr ⟨hThirdInfo.1, hEqual.symm ▸ hThirdInc⟩
  have hLower := Finset.card_le_card hSubset
  rw [card_nonDanglingIncident] at hLower
  have hTriple : ({edge, second, third} : Finset data.SourceEdge).card = 3 := by
    simp [hEdgeSecond, hEdgeThird, hSecondThird]
  rw [hTriple] at hLower
  have hUpper := fd.trivalent double
  have hDoubleNd : nonDanglingValency data double = 3 := by omega
  have hNe : single ≠ double := fun h ↦ hOpposite (congrArg (fun p : data.SourceVertex ↦ p.1.1) h)
  have hCount := sum_nonDanglingValency_activeFibre data hc hab hOne hCompat vertex
  rw [hActive, hEdge, Finset.sum_pair hNe, Finset.card_singleton, hNd, hDoubleNd] at hCount
  exact ⟨hEqual, edge, hEdge, hActive, hEdgeSingle, hEdgeDouble, by omega, hDoubleNd⟩

/-- At the derived nd2 endpoint, the internal occurrence and any retained
flag have exactly the same sheet block. This is the local sheet-set equality
in auxiliary r0, before the separate merged-class union argument. -/
theorem internal_block_eq_boundary_of_nd2
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (internal boundary : data.SourceEdge)
    (hInternal : internal ∈ internalEdges data hc hab hOne vertex)
    (hBoundary : boundary ∈ boundaryEdges data hc hab hOne vertex)
    (point : data.SourceVertex)
    (hMap : sourceVertexMap data hc hab hOne point = vertex)
    (hIncident : Incident data boundary point)
    (hNd : nonDanglingValency data point = 2) :
    (data.edgePartition internal.1.1).block internal.1.2 =
      (data.edgePartition boundary.1.1).block boundary.1.2 := by
  have hActive := active_of_boundary_incident data hc hab hOne vertex boundary hBoundary point hMap hIncident
  have hInternalInc := W4IncomingPrunedFibre.AnyWall.internalEdge_incident_of_mem_activeFibre
    data fd hc hab hOne hChangeZero vertex internal hInternal point hActive
  obtain ⟨hSurvives, hTarget, _⟩ := (mem_internalEdges data hc hab hOne vertex internal).mp hInternal
  have hAt := ((incident_iff_target_mem_and_rel data internal point).mp hInternalInc).1
  rw [hTarget] at hAt
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hAt
  rw [hc] at hAt
  have hChange := hChangeZero point.1.1 (hAt.imp Eq.symm Eq.symm)
  exact (W4IncomingCensus.AnyWall.block_eq_of_survives_nd2_at_endpoint data fd
    point hChange hNd internal hSurvives hInternalInc).trans
    (W4IncomingCensus.AnyWall.block_eq_of_survives_nd2_at_endpoint data fd
      point hChange hNd boundary ((mem_boundaryEdges data hc hab hOne vertex boundary).mp hBoundary).1
      hIncident).symm

end AnyWall

end AnyWallIncoming

section Incoming

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : W4TargetPairings.FourStar (GraphContraction.contract target hab hOne) ⟨a, hab⟩)

include fd hc hab hOne star

/-- The four-valent form of `AnyWall.eq_of_same_side`. -/
theorem eq_of_same_side (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (first second : data.SourceVertex)
    (hFirst : first ∈ activeFibreVertices data hc hab hOne vertex)
    (hSecond : second ∈ activeFibreVertices data hc hab hOne vertex)
    (hSide : first.1.1 = second.1.1) : first = second :=
  AnyWall.eq_of_same_side data fd hc hab hOne
    (W4IncomingCensus.changeZero_of_fourStar data fd hc hab hOne star)
    vertex first second hFirst hSecond hSide

/-- The four-valent form of `AnyWall.internalEdge_of_opposite_sides`. -/
theorem internalEdge_of_opposite_sides
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (first second : data.SourceVertex)
    (hFirst : first ∈ activeFibreVertices data hc hab hOne vertex)
    (hSecond : second ∈ activeFibreVertices data hc hab hOne vertex)
    (hSide : first.1.1 ≠ second.1.1) :
    ∃ edge : data.SourceEdge, internalEdges data hc hab hOne vertex = {edge} ∧
      activeFibreVertices data hc hab hOne vertex = {first, second} ∧
      Incident data edge first ∧ Incident data edge second :=
  AnyWall.internalEdge_of_opposite_sides data fd hc hab hOne
    (W4IncomingCensus.changeZero_of_fourStar data fd hc hab hOne star)
    vertex first second hFirst hSecond hSide

/-- The four-valent form of `AnyWall.exists_boundary_incident`. -/
theorem exists_boundary_incident
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (point : data.SourceVertex) (hPoint : point ∈ activeFibreVertices data hc hab hOne vertex) :
    ∃ edge ∈ boundaryEdges data hc hab hOne vertex, Incident data edge point :=
  AnyWall.exists_boundary_incident data fd hc hab hOne
    (W4IncomingCensus.changeZero_of_fourStar data fd hc hab hOne star) vertex point hPoint

/-- The four-valent form of `AnyWall.nonDanglingIncident_eq_insert_boundaryAt`. -/
theorem nonDanglingIncident_eq_insert_boundaryAt
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (internal : data.SourceEdge) (hInternal : internal ∈ internalEdges data hc hab hOne vertex)
    (point : data.SourceVertex) (hPoint : point ∈ activeFibreVertices data hc hab hOne vertex) :
    nonDanglingIncident data point = insert internal (boundaryAt data hc hab hOne vertex point) :=
  AnyWall.nonDanglingIncident_eq_insert_boundaryAt data fd hc hab hOne
    (W4IncomingCensus.changeZero_of_fourStar data fd hc hab hOne star)
    vertex internal hInternal point hPoint

/-- The four-valent form of `AnyWall.singleton_of_boundary_incident`. -/
theorem singleton_of_boundary_incident
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (point : data.SourceVertex) (hPoint : point ∈ activeFibreVertices data hc hab hOne vertex)
    (hBoundary : ∀ edge ∈ boundaryEdges data hc hab hOne vertex, Incident data edge point) :
    activeFibreVertices data hc hab hOne vertex = {point} ∧
      internalEdges data hc hab hOne vertex = ∅ :=
  AnyWall.singleton_of_boundary_incident data fd hc hab hOne
    (W4IncomingCensus.changeZero_of_fourStar data fd hc hab hOne star)
    vertex point hPoint hBoundary

/-- The four-valent form of `AnyWall.nd2_same_side`. -/
theorem nd2_same_side (hCompat : DanglingCompatible data hc hab hOne)
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne) vertex = 2)
    (first second : data.SourceEdge) (hNe : first ≠ second)
    (hFirst : first ∈ boundaryEdges data hc hab hOne vertex)
    (hSecond : second ∈ boundaryEdges data hc hab hOne vertex)
    (left right : data.SourceVertex)
    (hLeftMap : sourceVertexMap data hc hab hOne left = vertex)
    (hRightMap : sourceVertexMap data hc hab hOne right = vertex)
    (hLeftInc : Incident data first left) (hRightInc : Incident data second right)
    (hSide : left.1.1 = right.1.1) :
    left = right ∧ activeFibreVertices data hc hab hOne vertex = {left} ∧
      internalEdges data hc hab hOne vertex = ∅ ∧ nonDanglingValency data left = 2 :=
  AnyWall.nd2_same_side data fd hc hab hOne
    (W4IncomingCensus.changeZero_of_fourStar data fd hc hab hOne star)
    hCompat vertex hNd first second hNe hFirst hSecond left right hLeftMap hRightMap
    hLeftInc hRightInc hSide

/-- The four-valent form of `AnyWall.nd2_opposite_sides`. -/
theorem nd2_opposite_sides (hCompat : DanglingCompatible data hc hab hOne)
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne) vertex = 2)
    (first second : data.SourceEdge)
    (hFirst : first ∈ boundaryEdges data hc hab hOne vertex)
    (hSecond : second ∈ boundaryEdges data hc hab hOne vertex)
    (left right : data.SourceVertex)
    (hLeftMap : sourceVertexMap data hc hab hOne left = vertex)
    (hRightMap : sourceVertexMap data hc hab hOne right = vertex)
    (hLeftInc : Incident data first left) (hRightInc : Incident data second right)
    (hSide : left.1.1 ≠ right.1.1) :
    ∃ edge : data.SourceEdge, internalEdges data hc hab hOne vertex = {edge} ∧
      activeFibreVertices data hc hab hOne vertex = {left, right} ∧
      Incident data edge left ∧ Incident data edge right ∧
      nonDanglingValency data left = 2 ∧ nonDanglingValency data right = 2 :=
  AnyWall.nd2_opposite_sides data fd hc hab hOne
    (W4IncomingCensus.changeZero_of_fourStar data fd hc hab hOne star)
    hCompat vertex hNd first second hFirst hSecond left right hLeftMap hRightMap
    hLeftInc hRightInc hSide

/-- The four-valent form of `AnyWall.nd3_singleton_side`. -/
theorem nd3_singleton_side (hCompat : DanglingCompatible data hc hab hOne)
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne) vertex = 3)
    (first second third : data.SourceEdge) (hSecondThird : second ≠ third)
    (hFirst : first ∈ boundaryEdges data hc hab hOne vertex)
    (hSecond : second ∈ boundaryEdges data hc hab hOne vertex)
    (hThird : third ∈ boundaryEdges data hc hab hOne vertex)
    (single double other : data.SourceVertex)
    (hSingleMap : sourceVertexMap data hc hab hOne single = vertex)
    (hDoubleMap : sourceVertexMap data hc hab hOne double = vertex)
    (hOtherMap : sourceVertexMap data hc hab hOne other = vertex)
    (hFirstInc : Incident data first single) (hSecondInc : Incident data second double)
    (hThirdInc : Incident data third other)
    (hOpposite : single.1.1 ≠ double.1.1) (hSame : double.1.1 = other.1.1) :
    double = other ∧ ∃ edge : data.SourceEdge,
      internalEdges data hc hab hOne vertex = {edge} ∧
      activeFibreVertices data hc hab hOne vertex = {single, double} ∧
      Incident data edge single ∧ Incident data edge double ∧
      nonDanglingValency data single = 2 ∧ nonDanglingValency data double = 3 :=
  AnyWall.nd3_singleton_side data fd hc hab hOne
    (W4IncomingCensus.changeZero_of_fourStar data fd hc hab hOne star)
    hCompat vertex hNd first second third hSecondThird hFirst hSecond hThird
    single double other hSingleMap hDoubleMap hOtherMap hFirstInc hSecondInc hThirdInc
    hOpposite hSame

/-- The four-valent form of `AnyWall.internal_block_eq_boundary_of_nd2`. -/
theorem internal_block_eq_boundary_of_nd2
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (internal boundary : data.SourceEdge)
    (hInternal : internal ∈ internalEdges data hc hab hOne vertex)
    (hBoundary : boundary ∈ boundaryEdges data hc hab hOne vertex)
    (point : data.SourceVertex)
    (hMap : sourceVertexMap data hc hab hOne point = vertex)
    (hIncident : Incident data boundary point)
    (hNd : nonDanglingValency data point = 2) :
    (data.edgePartition internal.1.1).block internal.1.2 =
      (data.edgePartition boundary.1.1).block boundary.1.2 :=
  AnyWall.internal_block_eq_boundary_of_nd2 data fd hc hab hOne
    (W4IncomingCensus.changeZero_of_fourStar data fd hc hab hOne star)
    vertex internal boundary hInternal hBoundary point hMap hIncident hNd

end Incoming

end DraismaVargas.LocalCases.W4IncomingSideCensus
