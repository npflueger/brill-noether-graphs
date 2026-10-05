module

public import DraismaVargas.LocalCases.StablePathCount
public import DraismaVargas.LocalCases.SheetRelabelStable

@[expose] public section

/-!
# A minimal stable-source incidence dictionary

`Equivalence` identifies actual branch vertices and maximal stable paths and
preserves the number of surviving occurrences of each path at each branch.
The vertex equivalence includes injectivity and exhaustion, rather than just
placing named row ends at possibly coincident vertices. Incidences are counted:
a stable loop can contribute twice at the same branch vertex. No distinctness
of row endpoints, or of rows represented by distinct occurrences, is required.

This is an incidence certificate, not a construction of a `Spec`, a length
dictionary, or a zero-contraction/refinement receipt. In particular it does not
claim the terminal conclusions, whose additional graph data are discussed in
`StrongRefinement`.

The sheet-relabel inhabitant uses the actual source vertex/edge maps and their
descended stable-path map. The generic consumer transports `HasPathEnds`:
connectedness of the source excludes surviving valency one, so every old path
end is a branch; positive incidence at its image produces a new path end.
-/

namespace DraismaVargas.LocalCases.StableGraphIncidence

open DraismaVargas.Infrastructure W4StableSource StablePathCount

variable {target₁ target₂ target₃ : CFGraph} {degree₁ degree₂ degree₃ : ℕ}

/-- The surviving branch vertices, without an arbitrary finite labelling. -/
def BranchVertex (data : GluingDatum target₁ degree₁) :=
  {vertex : data.SourceVertex // 3 ≤ nonDanglingValency data vertex}

/-- This subtype is exactly the stable-vertex finset already used by trivalence. -/
noncomputable def branchVertexEquivStableVertices (data : GluingDatum target₁ degree₁) :
    BranchVertex data ≃ ↥(Trivalence.stableVertices data) :=
  Equiv.subtypeEquivRight fun vertex ↦ (Trivalence.mem_stableVertices data vertex).symm

/-- Required incidence data. Declaring this structure proves no existence of
such data between an arbitrary pair of covers. The multiplicity equality is
oriented from the original cover to its image. -/
structure Equivalence (first : GluingDatum target₁ degree₁)
    (second : GluingDatum target₂ degree₂) where
  vertex : BranchVertex first ≃ BranchVertex second
  row : StablePath first ≃ StablePath second
  incidence : ∀ (v : BranchVertex first) (path : StablePath first),
    incidenceCount first v.1 path = incidenceCount second (vertex v).1 (row path)

namespace Equivalence

variable {first : GluingDatum target₁ degree₁} {second : GluingDatum target₂ degree₂}
    {third : GluingDatum target₃ degree₃}

/-- The identity incidence dictionary is inhabited for every datum. -/
def refl (data : GluingDatum target₁ degree₁) : Equivalence data data where
  vertex := Equiv.refl _
  row := Equiv.refl _
  incidence _ _ := rfl

/-- Reverse a proved incidence dictionary. -/
def symm (certificate : Equivalence first second) : Equivalence second first where
  vertex := certificate.vertex.symm
  row := certificate.row.symm
  incidence v path := by
    simpa using (certificate.incidence (certificate.vertex.symm v)
      (certificate.row.symm path)).symm

/-- Compose actual branch and row maps, retaining all incidence multiplicities. -/
def trans (left : Equivalence first second) (right : Equivalence second third) :
    Equivalence first third where
  vertex := left.vertex.trans right.vertex
  row := left.row.trans right.row
  incidence v path := (left.incidence v path).trans (right.incidence (left.vertex v) (left.row path))

/-- Path ends transport without assuming that the destination is connected.
Only the original connectedness is used to recognize its ends as branches. -/
theorem hasPathEnds (certificate : Equivalence first second)
    (hConnected : first.Connected) (hEnds : HasPathEnds first) : HasPathEnds second := by
  classical
  intro edge
  obtain ⟨v, hNeTwo, hPositive⟩ := exists_end_vertex first hEnds
    (certificate.row.symm edge.stablePath)
  obtain ⟨oldEdge, hIncident, _⟩ := (incidenceCount_pos_iff first v _).mp hPositive
  have hPositiveValency : 0 < nonDanglingValency first v := by
    rw [← card_incidentEdges, Finset.card_pos]
    exact ⟨oldEdge, (mem_incidentEdges first v oldEdge).mpr hIncident⟩
  have hNeOne := NonDanglingValency.nonDanglingValency_ne_one first hConnected v
  have hBranch : 3 ≤ nonDanglingValency first v := by omega
  let branch : BranchVertex first := ⟨v, hBranch⟩
  have hMapped : 0 < incidenceCount second (certificate.vertex branch).1 edge.stablePath := by
    change 0 < incidenceCount first branch.1 (certificate.row.symm edge.stablePath) at hPositive
    rw [certificate.incidence branch] at hPositive
    simpa using hPositive
  obtain ⟨newEdge, hNewIncident, hNewPath⟩ :=
    (incidenceCount_pos_iff second _ _).mp hMapped
  refine ⟨newEdge, (certificate.vertex branch).1, hNewPath, hNewIncident, ?_⟩
  have := (certificate.vertex branch).2
  omega

/-- With both sources connected, the path-end property is equivalent. -/
theorem hasPathEnds_iff (certificate : Equivalence first second)
    (hFirst : first.Connected) (hSecond : second.Connected) :
    HasPathEnds first ↔ HasPathEnds second :=
  ⟨certificate.hasPathEnds hFirst, certificate.symm.hasPathEnds hSecond⟩

end Equivalence

variable {data : GluingDatum target₁ degree₁}

/-- Restrict the literal source-vertex equivalence to surviving branches. -/
noncomputable def sheetRelabelVertex (relabeling : data.SheetRelabeling)
    (hConnected : data.Connected) : BranchVertex data ≃ BranchVertex relabeling.apply :=
  relabeling.sourceVertexEquiv.subtypeEquiv fun vertex ↦ by
    rw [SheetRelabelStable.nonDanglingValency_map relabeling hConnected]

/-- The actual surviving-edge bijection preserves each row-filtered star,
including when two different occurrences represent the same stable row. -/
theorem incidenceCount_sheetRelabel (relabeling : data.SheetRelabeling)
    (hConnected : data.Connected) (vertex : data.SourceVertex) (path : StablePath data) :
    incidenceCount data vertex path =
      incidenceCount relabeling.apply (relabeling.sourceVertexEquiv vertex)
        (SheetRelabelStable.stablePathEquiv relabeling hConnected path) := by
  classical
  unfold incidenceCount
  apply Finset.card_bij (fun edge _ ↦ SheetRelabelStable.nonDanglingEdgeEquiv relabeling hConnected edge)
  · intro edge hEdge
    simp only [Finset.mem_filter, mem_incidentEdges] at hEdge ⊢
    refine ⟨(SheetRelabelPruning.incident_sourceEdgeEquiv_iff relabeling edge.1 vertex).mpr hEdge.1, ?_⟩
    rw [← SheetRelabelStable.stablePathEquiv_mk, hEdge.2]
  · intro first _ second _ hEq
    exact (SheetRelabelStable.nonDanglingEdgeEquiv relabeling hConnected).injective hEq
  · intro edge hEdge
    obtain ⟨oldEdge, rfl⟩ :=
      (SheetRelabelStable.nonDanglingEdgeEquiv relabeling hConnected).surjective edge
    refine ⟨oldEdge, ?_, rfl⟩
    simp only [Finset.mem_filter, mem_incidentEdges] at hEdge ⊢
    refine ⟨(SheetRelabelPruning.incident_sourceEdgeEquiv_iff relabeling oldEdge.1 vertex).mp hEdge.1, ?_⟩
    apply (SheetRelabelStable.stablePathEquiv relabeling hConnected).injective
    rw [SheetRelabelStable.stablePathEquiv_mk]
    exact hEdge.2

/-- A checked geometric inhabitant: sheet relabelling supplies the three
fields via its actual source vertex, source edge, and stable-path maps. -/
noncomputable def sheetRelabel (relabeling : data.SheetRelabeling)
    (hConnected : data.Connected) : Equivalence data relabeling.apply where
  vertex := sheetRelabelVertex relabeling hConnected
  row := SheetRelabelStable.stablePathEquiv relabeling hConnected
  incidence v path := incidenceCount_sheetRelabel relabeling hConnected v.1 path

/-- The generic incidence consumer applies to the actual sheet-relabel map. -/
theorem hasPathEnds_sheetRelabel (relabeling : data.SheetRelabeling)
    (hConnected : data.Connected) (hEnds : HasPathEnds data) :
    HasPathEnds relabeling.apply :=
  (sheetRelabel relabeling hConnected).hasPathEnds hConnected hEnds

end DraismaVargas.LocalCases.StableGraphIncidence
