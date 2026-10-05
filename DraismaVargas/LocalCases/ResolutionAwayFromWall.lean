module

public import DraismaVargas.LocalCases.ResolutionPruning

@[expose] public section

/-!
# Stable-path incidences away from the resolved wall

The source partitions are unchanged off the wall. The literal retained-edge
map therefore identifies the incident occurrences there; the new target edge
cannot meet such a vertex. For a genus-preserving candidate the proved pruning
equivalence restricts this dictionary to surviving occurrences, so surviving
valency and consecutive pairs are preserved. This is the off-wall part of
the induced-labelling argument following the paper's non-dangling-union lemma.
-/

namespace DraismaVargas.LocalCases.ResolutionAwayFromWall

open DraismaVargas.Infrastructure TargetExpansion W4StableSource ResolutionM11

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}

/-- The canonical endpoint at the retained copy of an old target vertex. -/
noncomputable def retainedVertex
    (candidate : BalancedGlobal.Candidate target degree data wall)
    (vertex : data.SourceVertex) : candidate.datum.SourceVertex :=
  candidate.datum.sourceEndpoint (oldVertex target vertex.1.1) vertex.1.2

theorem vertexPartition_retained
    (candidate : BalancedGlobal.Candidate target degree data wall)
    (vertex : data.SourceVertex) (hAway : vertex.1.1 ≠ wall) :
    candidate.datum.vertexPartition (oldVertex target vertex.1.1) =
      data.vertexPartition vertex.1.1 :=
  GlobalResolution.expandedVertexPartition_old_of_ne data wall vertex.1.1
    (LocalResolution.paste _ candidate.resolution candidate.contracts) hAway

theorem retainedVertex_sheet
    (candidate : BalancedGlobal.Candidate target degree data wall)
    (vertex : data.SourceVertex) (hAway : vertex.1.1 ≠ wall) :
    (retainedVertex candidate vertex).1.2 = vertex.1.2 := by
  change (candidate.datum.vertexPartition (oldVertex target vertex.1.1)).repr vertex.1.2 = vertex.1.2
  rw [vertexPartition_retained candidate vertex hAway]
  exact vertex.2

/-- Every source vertex over an unchanged target vertex is literally the
retained copy of an old source vertex. -/
theorem exists_retainedVertex_of_target
    (candidate : BalancedGlobal.Candidate target degree data wall)
    (vertex : candidate.datum.SourceVertex) (place : target.V) (hAway : place ≠ wall)
    (hTarget : vertex.1.1 = oldVertex target place) :
    ∃ old : data.SourceVertex, old.1.1 = place ∧ retainedVertex candidate old = vertex := by
  have hPart : candidate.datum.vertexPartition (oldVertex target place) = data.vertexPartition place :=
    GlobalResolution.expandedVertexPartition_old_of_ne data wall place
      (LocalResolution.paste _ candidate.resolution candidate.contracts) hAway
  have hCanonical : (data.vertexPartition place).repr vertex.1.2 = vertex.1.2 := by
    rw [← hPart, ← hTarget]
    exact vertex.2
  let old : data.SourceVertex := ⟨(place, vertex.1.2), hCanonical⟩
  refine ⟨old, rfl, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact hTarget.symm
  · exact retainedVertex_sheet candidate old hAway

theorem incident_oldSourceEdge_iff
    (candidate : BalancedGlobal.Candidate target degree data wall)
    (vertex : data.SourceVertex) (hAway : vertex.1.1 ≠ wall) (edge : data.SourceEdge) :
    Incident candidate.datum (candidate.oldSourceEdge edge) (retainedVertex candidate vertex) ↔
      Incident data edge vertex := by
  rw [incident_iff_target_mem_and_rel, incident_iff_target_mem_and_rel,
    candidate.oldSourceEdge_target, candidate.oldSourceEdge_sheet,
    retainedVertex_sheet candidate vertex hAway]
  change (occurrenceEquiv target wall candidate.right (some edge.1.1) ∈
      GluingDatum.incidentEdges (oldVertex target vertex.1.1) ∧
      (candidate.datum.vertexPartition (oldVertex target vertex.1.1)).Rel vertex.1.2 edge.1.2) ↔ _
  rw [GlobalResolution.oldOccurrence_mem_incidentEdges_old_iff wall vertex.1.1 candidate.right hAway,
    vertexPartition_retained candidate vertex hAway]

theorem not_incident_newSourceEdge
    (candidate : BalancedGlobal.Candidate target degree data wall)
    (vertex : data.SourceVertex) (hAway : vertex.1.1 ≠ wall) (sheet : Fin degree) :
    ¬ Incident candidate.datum (candidate.newSourceEdge sheet) (retainedVertex candidate vertex) := by
  intro hIncident
  have hTarget := (incident_iff_target_mem_and_rel _ _ _).mp hIncident |>.1
  exact GlobalResolution.newOccurrence_not_mem_incidentEdges_old wall vertex.1.1 candidate.right hAway hTarget

/-- The complete surviving incidence set is the image of the old one.
No new occurrence can contribute away from the wall. -/
theorem nonDanglingIncident_retainedVertex
    (candidate : BalancedGlobal.Candidate target degree data wall) (hValid : data.Valid)
    (hGenus : genus candidate.datum.sourceGraph = genus data.sourceGraph)
    (vertex : data.SourceVertex) (hAway : vertex.1.1 ≠ wall) :
    nonDanglingIncident candidate.datum (retainedVertex candidate vertex) =
      (nonDanglingIncident data vertex).image candidate.oldSourceEdge := by
  classical
  ext edge
  constructor
  · intro hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases ResolutionPruning.sourceEdge_cases candidate edge with ⟨old, rfl⟩ | ⟨sheet, rfl⟩
    · refine Finset.mem_image.mpr ⟨old, (mem_nonDanglingIncident _ _ _).mpr ⟨?_, ?_⟩, rfl⟩
      · exact fun h ↦ hSurvives ((ResolutionPruning.isDangling_oldSourceEdge_iff candidate hValid hGenus old).mpr h)
      · exact (incident_oldSourceEdge_iff candidate vertex hAway old).mp hIncident
    · exact (not_incident_newSourceEdge candidate vertex hAway sheet hIncident).elim
  · rintro hMem
    obtain ⟨old, hOld, rfl⟩ := Finset.mem_image.mp hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hOld
    exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨ResolutionSurvival.not_isDangling_oldSourceEdge candidate hValid.1 old hSurvives,
        (incident_oldSourceEdge_iff candidate vertex hAway old).mpr hIncident⟩

theorem nonDanglingValency_retainedVertex
    (candidate : BalancedGlobal.Candidate target degree data wall) (hValid : data.Valid)
    (hGenus : genus candidate.datum.sourceGraph = genus data.sourceGraph)
    (vertex : data.SourceVertex) (hAway : vertex.1.1 ≠ wall) :
    nonDanglingValency candidate.datum (retainedVertex candidate vertex) =
      nonDanglingValency data vertex := by
  classical
  rw [← card_nonDanglingIncident, nonDanglingIncident_retainedVertex candidate hValid hGenus vertex hAway,
    Finset.card_image_of_injective _ (ResolutionCut.oldSourceEdge_injective candidate), card_nonDanglingIncident]

/-- Retaining an actual surviving occurrence, with its survival proof derived
from the source contraction rather than supplied as a compatibility receipt. -/
noncomputable def retainedEdge
    (candidate : BalancedGlobal.Candidate target degree data wall) (hConnected : data.Connected)
    (edge : NonDanglingEdge data) : NonDanglingEdge candidate.datum :=
  ⟨candidate.oldSourceEdge edge.1,
    ResolutionSurvival.not_isDangling_oldSourceEdge candidate hConnected edge.1 edge.2⟩

theorem retainedEdge_injective
    (candidate : BalancedGlobal.Candidate target degree data wall) (hConnected : data.Connected) :
    Function.Injective (retainedEdge candidate hConnected) := by
  intro first second hEqual
  exact Subtype.ext (ResolutionCut.oldSourceEdge_injective candidate (congrArg Subtype.val hEqual))

/-- Exhaust surviving occurrences, deriving the old survival assertion in
the retained branch from the genus-preserving pruning theorem. -/
theorem nonDanglingEdge_cases
    (candidate : BalancedGlobal.Candidate target degree data wall) (hValid : data.Valid)
    (hGenus : genus candidate.datum.sourceGraph = genus data.sourceGraph)
    (edge : NonDanglingEdge candidate.datum) :
    (∃ old : NonDanglingEdge data, edge = retainedEdge candidate hValid.1 old) ∨
      ∃ (sheet : Fin degree) (hSurvives : ¬ IsDangling candidate.datum (candidate.newSourceEdge sheet)),
        edge = ⟨candidate.newSourceEdge sheet, hSurvives⟩ := by
  rcases ResolutionPruning.sourceEdge_cases candidate edge.1 with ⟨old, hOld⟩ | ⟨sheet, hNew⟩
  · left
    have hSurvives : ¬ IsDangling data old := by
      intro h
      apply edge.2
      rw [hOld]
      exact (ResolutionPruning.isDangling_oldSourceEdge_iff candidate hValid hGenus old).mpr h
    exact ⟨⟨old, hSurvives⟩, Subtype.ext hOld⟩
  · right
    have hSurvives : ¬ IsDangling candidate.datum (candidate.newSourceEdge sheet) := by
      rw [← hNew]
      exact edge.2
    exact ⟨sheet, hSurvives, Subtype.ext hNew⟩

theorem consecutive_retained_of_away
    (candidate : BalancedGlobal.Candidate target degree data wall) (hValid : data.Valid)
    (hGenus : genus candidate.datum.sourceGraph = genus data.sourceGraph)
    (first second : NonDanglingEdge data) (hNe : first ≠ second)
    (vertex : data.SourceVertex) (hAway : vertex.1.1 ≠ wall)
    (hFirst : Incident data first.1 vertex) (hSecond : Incident data second.1 vertex)
    (hValency : nonDanglingValency data vertex = 2) :
    Consecutive candidate.datum (retainedEdge candidate hValid.1 first) (retainedEdge candidate hValid.1 second) := by
  refine ⟨fun h ↦ hNe (retainedEdge_injective candidate hValid.1 h), retainedVertex candidate vertex, ?_, ?_, ?_⟩
  · exact (incident_oldSourceEdge_iff candidate vertex hAway first.1).mpr hFirst
  · exact (incident_oldSourceEdge_iff candidate vertex hAway second.1).mpr hSecond
  · exact (nonDanglingValency_retainedVertex candidate hValid hGenus vertex hAway).trans hValency

end DraismaVargas.LocalCases.ResolutionAwayFromWall
