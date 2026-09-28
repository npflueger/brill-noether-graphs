import DraismaVargas.LocalCases.DivalentSourceLocal
import DraismaVargas.LocalCases.PrunedFibreStablePath

/-!
# An nd2 fibre between nonleaf target endpoints has at most one survivor

Source: Draisma--Vargas Part I, `lemma-edges-in-GqA0`, and Base II of Case
{w2}. The pruned-tree formula makes every active constituent of an
nd2 wall fibre divalent. At a nonleaf change-minimal target endpoint its
ramification is at most one, so its two survivors have distinct directions.
In particular at most one of them lies over the contracted target edge.

The already-proved pruned connectivity then makes all surviving internal
occurrences equal. The proof propagates occurrence equality along an actual
pruned walk; it does not assume the fibre is a displayed one-edge diagram.
-/

namespace DraismaVargas.LocalCases.PrunedDivalentFibre

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4StableSource StableLocalProperties ClassInjectivity WallDegeneration
open PrunedContractionFibre PrunedFibreValency PrunedFibreTree PrunedFibreStablePath
open FullDimensionalSource DivalentSourceLocal

variable {target : CFGraph} {degree : ℕ}

section Fibre

variable (data : GluingDatum target degree) {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hCompat : DanglingCompatible data hc hab hOne)
  (hForest : ContractionForest data a b contracted)
  (hLeft : 2 ≤ (GluingDatum.incidentEdges a).card)
  (hRight : 2 ≤ (GluingDatum.incidentEdges b).card)
  (vertex : (contractDatum data hc hab hOne).SourceVertex)
  (hNd : nonDanglingValency (contractDatum data hc hab hOne) vertex = 2)

include fullDim hCompat hForest hLeft hRight hNd

/-- At any constituent of this fibre there is at most one surviving
occurrence in the contracted target direction. -/
theorem contracted_sourceEdge_eq_of_incident
    (point : data.SourceVertex) (hMap : sourceVertexMap data hc hab hOne point = vertex)
    (first second : data.SourceEdge)
    (hFirstTarget : first.1.1 = contracted) (hSecondTarget : second.1.1 = contracted)
    (hFirst : ¬ IsDangling data first) (hSecond : ¬ IsDangling data second)
    (hFirstInc : Incident data first point) (hSecondInc : Incident data second point) :
    first = second := by
  have hTarget := (incident_iff_target_mem_and_rel data first point).mp hFirstInc |>.1
  rw [hFirstTarget] at hTarget
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hTarget
  have hAt : point.1.1 = a ∨ point.1.1 = b := by
    rw [hc] at hTarget
    exact hTarget.imp Eq.symm Eq.symm
  have hNonleaf : 2 ≤ (GluingDatum.incidentEdges point.1.1).card := by
    rcases hAt with hAt | hAt
    · rw [hAt]; exact hLeft
    · rw [hAt]; exact hRight
  have hLocal := localRamification_le_one_of_nonleaf data fullDim.valid point
    (fullDim.changeMinimal point.1.1) hNonleaf
  have hTwo := nonDanglingValency_eq_two_of_sourceVertexMap_eq data hc hab hOne
    fullDim.valid.1 hCompat hForest vertex hNd point hMap
    (nonDanglingValency_ne_zero_of_incident data hFirst hFirstInc)
  exact sourceEdge_eq_of_same_target data fullDim.danglingEdgeNoGlue point hTwo hLocal
    first second hFirst hSecond hFirstInc hSecondInc (hFirstTarget.trans hSecondTarget.symm)

/-- Equality of internal occurrences propagates along the actual pruned
fibre walk. Every intermediate equality is justified by local no-return. -/
theorem sourceEdge_eq_of_surviving_walk
    (first : data.SourceEdge) (hFirstTarget : first.1.1 = contracted)
    (hFirst : ¬ IsDangling data first)
    (left right : data.SourceVertex) (hFirstInc : Incident data first left)
    (hLeftMap : sourceVertexMap data hc hab hOne left = vertex)
    (hWalk : Relation.ReflTransGen (SurvivingFibreStep data contracted) left right)
    (second : data.SourceEdge) (hSecondTarget : second.1.1 = contracted)
    (hSecond : ¬ IsDangling data second) (hSecondInc : Incident data second right) :
    first = second := by
  induction hWalk generalizing second with
  | refl =>
    exact contracted_sourceEdge_eq_of_incident data hc hab hOne fullDim hCompat hForest
      hLeft hRight vertex hNd left hLeftMap first second
      hFirstTarget hSecondTarget hFirst hSecond hFirstInc hSecondInc
  | @tail previous last hWalk hStep ih =>
    obtain ⟨edge, hTarget, hSurvives, hEnds⟩ := hStep
    have hPrevious : Incident data edge previous := incident_of_sourceEnds data hEnds
    have hLast : Incident data edge last := incident_of_sourceEnds data hEnds.symm
    have hLastMap : sourceVertexMap data hc hab hOne last = vertex :=
      (sourceVertexMap_eq_of_surviving_walk data hc hab hOne
        (hWalk.tail ⟨edge, hTarget, hSurvives, hEnds⟩)).symm.trans hLeftMap
    exact (ih edge hTarget hSurvives hPrevious).trans
      (contracted_sourceEdge_eq_of_incident data hc hab hOne fullDim hCompat hForest
        hLeft hRight vertex hNd last hLastMap edge second
        hTarget hSecondTarget hSurvives hSecond hLast hSecondInc)

/-- The literal surviving internal edge set has at most one member. -/
theorem internalEdges_subsingleton :
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
  exact sourceEdge_eq_of_surviving_walk data hc hab hOne fullDim hCompat hForest
    hLeft hRight vertex hNd first hFirstTarget hFirstSurvives
    (data.sourceEnds first).1 (data.sourceEnds second).1 (Or.inl rfl)
    hFirstMap hWalk second hSecondTarget hSecondSurvives (Or.inl rfl)

theorem internalEdges_card_le_one : (internalEdges data hc hab hOne vertex).card ≤ 1 :=
  Finset.card_le_one.mpr
    (internalEdges_subsingleton data hc hab hOne fullDim hCompat hForest hLeft hRight vertex hNd)

/-- Every active constituent meets the unique internal occurrence, whenever
one is present. This follows by propagating its equality along the pruned
walk to that constituent. -/
theorem internalEdge_incident_of_mem_activeFibre
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
    have hEq := sourceEdge_eq_of_surviving_walk data hc hab hOne fullDim hCompat hForest
      hLeft hRight vertex hNd edge hTarget hSurvives (data.sourceEnds edge).1 point (Or.inl rfl)
      hEdgeMap (hWalk.tail ⟨step, hStepTarget, hStepSurvives, hEnds⟩)
      step hStepTarget hStepSurvives hLast
    rw [hEq]
    exact hLast

/-- An exterior survivor and the unique internal survivor meeting the same
constituent have indices differing by at most one. -/
theorem internal_index_close_to_boundary
    (edge : data.SourceEdge) (hEdge : edge ∈ internalEdges data hc hab hOne vertex)
    (boundary : data.SourceEdge) (hBoundary : ¬ IsDangling data boundary)
    (hBoundaryTarget : boundary.1.1 ≠ contracted)
    (point : data.SourceVertex) (hMap : sourceVertexMap data hc hab hOne point = vertex)
    (hIncident : Incident data boundary point) :
    data.sourceEdgeIndex edge ≤ data.sourceEdgeIndex boundary + 1 ∧
      data.sourceEdgeIndex boundary ≤ data.sourceEdgeIndex edge + 1 := by
  have hActive := nonDanglingValency_ne_zero_of_incident data hBoundary hIncident
  have hInternalInc := internalEdge_incident_of_mem_activeFibre data hc hab hOne fullDim
    hCompat hForest hLeft hRight vertex hNd edge hEdge point
      ((mem_activeFibreVertices data hc hab hOne vertex point).mpr ⟨hMap, hActive⟩)
  obtain ⟨hSurvives, hTarget, _⟩ := (mem_internalEdges data hc hab hOne vertex edge).mp hEdge
  have hTargetInc := (incident_iff_target_mem_and_rel data edge point).mp hInternalInc |>.1
  rw [hTarget] at hTargetInc
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hTargetInc
  rw [hc] at hTargetInc
  have hNonleaf : 2 ≤ (GluingDatum.incidentEdges point.1.1).card := by
    rcases hTargetInc with hAt | hAt
    · rw [← hAt]; exact hLeft
    · rw [← hAt]; exact hRight
  have hLocal := localRamification_le_one_of_nonleaf data fullDim.valid point
    (fullDim.changeMinimal point.1.1) hNonleaf
  have hTwo := nonDanglingValency_eq_two_of_sourceVertexMap_eq data hc hab hOne
    fullDim.valid.1 hCompat hForest vertex hNd point hMap hActive
  apply indices_close_of_ramification_le_one data fullDim.danglingEdgeNoGlue point hTwo hLocal
    ⟨edge, hInternalInc⟩ ⟨boundary, hIncident⟩ _ hSurvives hBoundary
  intro hEq
  exact hBoundaryTarget ((congrArg (fun e : IncidentSourceEdge data point ↦ e.1.1.1) hEq).symm.trans hTarget)

end Fibre

/-- **Base II's actual one-edge census.** Between two divalent target
endpoints an nd2 wall fibre has exactly one surviving internal occurrence.
Existence follows from directional harmonicity at an actual active preimage;
uniqueness follows from the preceding pruned-walk theorem. -/
theorem exists_unique_internalEdge
    (data : GluingDatum target degree) {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hCompat : DanglingCompatible data hc hab hOne)
    (hForest : ContractionForest data a b contracted)
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2)
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hMerge : vertex.1.1 = ⟨a, hab⟩)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne) vertex = 2) :
    ∃ edge : data.SourceEdge, internalEdges data hc hab hOne vertex = {edge} := by
  classical
  obtain ⟨point, hPoint⟩ := activeFibreVertices_nonempty_of_nonDanglingValency_ne_zero
    data hc hab hOne hCompat vertex (by omega)
  obtain ⟨hMap, hActive⟩ := (mem_activeFibreVertices data hc hab hOne vertex point).mp hPoint
  have hProjection := congrArg (fun x : (contractDatum data hc hab hOne).SourceVertex ↦ x.1.1) hMap
  change fold target hab point.1.1 = vertex.1.1 at hProjection
  rw [hMerge] at hProjection
  have hAt : point.1.1 = a ∨ point.1.1 = b := by
    simpa only [fold_eq_iff, true_and] using hProjection
  have hDivalent : (GluingDatum.incidentEdges point.1.1).card = 2 :=
    hAt.elim (fun h ↦ h ▸ hLeft) (fun h ↦ h ▸ hRight)
  have hIncident : contracted ∈ GluingDatum.incidentEdges point.1.1 := by
    rcases hAt with hAt | hAt
    · rw [hAt]; exact contracted_mem_incidentEdges_left hc
    · rw [hAt]; exact contracted_mem_incidentEdges_right hc
  have hTwo := nonDanglingValency_eq_two_of_sourceVertexMap_eq data hc hab hOne
    fullDim.valid.1 hCompat hForest vertex hNd point hMap hActive
  have hLocal := localRamification_le_one_of_nonleaf data fullDim.valid point
    (fullDim.changeMinimal point.1.1) (by omega)
  obtain ⟨edge, hSurvives, hTarget, hInc⟩ := exists_surviving_incidence_over_target data
    fullDim.danglingEdgeNoGlue point hTwo hLocal hDivalent contracted hIncident
  have hEdgeMap : sourceVertexMap data hc hab hOne (data.sourceEnds edge).1 = vertex := by
    rcases hInc with hInc | hInc
    · exact (congrArg (sourceVertexMap data hc hab hOne) hInc).trans hMap
    · exact (sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hOne edge hTarget).trans
        ((congrArg (sourceVertexMap data hc hab hOne) hInc).trans hMap)
  have hMember := (mem_internalEdges data hc hab hOne vertex edge).mpr ⟨hSurvives, hTarget, hEdgeMap⟩
  refine ⟨edge, Finset.eq_singleton_iff_unique_mem.mpr ⟨hMember, ?_⟩⟩
  intro other hOther
  exact internalEdges_subsingleton data hc hab hOne fullDim hCompat hForest
    (by omega) (by omega) vertex hNd other hOther edge hMember

end DraismaVargas.LocalCases.PrunedDivalentFibre
