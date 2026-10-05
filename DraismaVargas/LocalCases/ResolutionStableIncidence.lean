module

public import DraismaVargas.LocalCases.ResolutionAwayFromWall
public import DraismaVargas.LocalCases.StableGraphIncidence

@[expose] public section

/-!
# Off-wall stable incidence transport for a resolution

The surviving incident star at an unchanged vertex is exactly the image under
`candidate.oldSourceEdge`. Filtering this proved census by an actual stable-row
equivalence gives the incidence equality needed by `StableGraphIncidence`.
No new source occurrence can enter this star.

The row equivalence and its action on retained occurrences are explicit inputs
to this reusable consumer, not conclusions or assumed incidence identities.
Case-specific modules construct that row map and the branch-vertex map at the
resolved wall. Nothing here constructs a global incidence certificate,
a requested `Spec`, or any metric/contraction dictionary. Distinct incident
occurrences are counted even if they belong to the same stable row.
-/

namespace DraismaVargas.LocalCases.ResolutionStableIncidence

open DraismaVargas.Infrastructure W4StableSource StablePathCount ResolutionAwayFromWall

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}

/-- Off the wall both the target location and the canonical sheet are
unchanged; thus retained vertices cannot merge there. -/
theorem retainedVertex_injective_away
    (candidate : BalancedGlobal.Candidate target degree data wall)
    (first second : data.SourceVertex) (hFirst : first.1.1 ≠ wall) (hSecond : second.1.1 ≠ wall)
    (hEqual : retainedVertex candidate first = retainedVertex candidate second) : first = second := by
  apply Subtype.ext
  apply Prod.ext
  · exact Sum.inl.inj (congrArg (fun vertex : candidate.datum.SourceVertex ↦ vertex.1.1) hEqual)
  · have hSheet := congrArg (fun vertex : candidate.datum.SourceVertex ↦ vertex.1.2) hEqual
    rwa [retainedVertex_sheet candidate first hFirst, retainedVertex_sheet candidate second hSecond] at hSheet

/-- Filter the exact off-wall surviving-star census by a row map which follows
each actual retained occurrence. This supplies the off-wall incidence field,
oriented from the original cover to the resolution. -/
theorem incidenceCount_retainedVertex
    (candidate : BalancedGlobal.Candidate target degree data wall) (hValid : data.Valid)
    (hGenus : genus candidate.datum.sourceGraph = genus data.sourceGraph)
    (row : StablePath data ≃ StablePath candidate.datum)
    (row_mk : ∀ edge : NonDanglingEdge data,
      row edge.stablePath = (retainedEdge candidate hValid.1 edge).stablePath)
    (vertex : data.SourceVertex) (hAway : vertex.1.1 ≠ wall) (path : StablePath data) :
    incidenceCount data vertex path =
      incidenceCount candidate.datum (retainedVertex candidate vertex) (row path) := by
  classical
  unfold incidenceCount
  apply Finset.card_bij (fun edge _ ↦ retainedEdge candidate hValid.1 edge)
  · intro edge hEdge
    simp only [Finset.mem_filter, mem_incidentEdges] at hEdge ⊢
    refine ⟨(incident_oldSourceEdge_iff candidate vertex hAway edge.1).mpr hEdge.1, ?_⟩
    rw [← row_mk, hEdge.2]
  · intro first _ second _ hEq
    exact retainedEdge_injective candidate hValid.1 hEq
  · intro edge hEdge
    simp only [Finset.mem_filter, mem_incidentEdges] at hEdge
    have hMem : edge.1 ∈ nonDanglingIncident candidate.datum (retainedVertex candidate vertex) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hEdge.1⟩
    rw [nonDanglingIncident_retainedVertex candidate hValid hGenus vertex hAway] at hMem
    obtain ⟨old, hOld, hEqual⟩ := Finset.mem_image.mp hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hOld
    let oldEdge : NonDanglingEdge data := ⟨old, hSurvives⟩
    have hRetained : retainedEdge candidate hValid.1 oldEdge = edge := Subtype.ext hEqual
    refine ⟨oldEdge, ?_, hRetained⟩
    simp only [Finset.mem_filter, mem_incidentEdges]
    refine ⟨hIncident, row.injective ?_⟩
    rw [row_mk, hRetained]
    exact hEdge.2

end DraismaVargas.LocalCases.ResolutionStableIncidence
