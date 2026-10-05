module

public import DraismaVargas.LocalCases.StableGraphIncidence
public import DraismaVargas.LocalCases.FullDimensionalSource

@[expose] public section

/-!
# Transporting full-dimensional source data through stable incidence

An actual stable-incidence equivalence preserves the surviving valency of
each branch vertex: split that valency into its incidences with all stable
rows and reindex the sum by the row equivalence.  Surjectivity on branch
vertices then transports the global upper valency bound.  Together with the
path-end transport, this supplies the combinatorial fields needed to
rebuild a full-dimensional presentation once the destination's geometric and
matrix data are provided.
-/

namespace DraismaVargas.LocalCases.StableGraphFullDimensional

open DraismaVargas.Infrastructure
open W4StableSource StablePathCount FullDimensionalSource
open StableGraphIncidence

variable {target₁ target₂ : CFGraph} {degree : ℕ}
  {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}

/-- Stable incidence preserves the exact surviving valency of every branch
vertex.  Incidence multiplicities, rather than a set of adjacent rows, are
summed so a loop at a branch remains counted twice. -/
theorem branchVertex_valency_eq
    (certificate : Equivalence first second) (vertex : BranchVertex first) :
    nonDanglingValency first vertex.1 =
      nonDanglingValency second (certificate.vertex vertex).1 := by
  rw [← sum_incidenceCount_vertex first vertex.1,
    ← sum_incidenceCount_vertex second (certificate.vertex vertex).1]
  calc
    (∑ path : StablePath first, incidenceCount first vertex.1 path) =
        ∑ path : StablePath first,
          incidenceCount second (certificate.vertex vertex).1 (certificate.row path) := by
      apply Finset.sum_congr rfl
      intro path _
      exact certificate.incidence vertex path
    _ = ∑ path : StablePath second,
          incidenceCount second (certificate.vertex vertex).1 path :=
      certificate.row.sum_comp
        (fun path ↦ incidenceCount second (certificate.vertex vertex).1 path)

/-- A stable-incidence equivalence transports the global trivalence upper
bound.  A destination nonbranch has valency below three by definition; a
destination branch has an old preimage with the same exact valency. -/
theorem trivalent_of_equivalence
    (certificate : Equivalence first second)
    (hTrivalent : ∀ vertex : first.SourceVertex,
      nonDanglingValency first vertex ≤ 3) :
    ∀ vertex : second.SourceVertex,
      nonDanglingValency second vertex ≤ 3 := by
  intro vertex
  by_cases hBranch : 3 ≤ nonDanglingValency second vertex
  · let newBranch : BranchVertex second := ⟨vertex, hBranch⟩
    obtain ⟨oldBranch, hImage⟩ := certificate.vertex.surjective newBranch
    have hValency := branchVertex_valency_eq certificate oldBranch
    rw [hImage] at hValency
    exact hValency ▸ hTrivalent oldBranch.1
  · omega

/-- Rebuild a destination full-dimensional presentation from an actual
stable-incidence dictionary and independently checked destination geometry
and length matrix.  The equalities of target-edge count and source genus are
the exact numerical receipts needed to transport saturation. -/
noncomputable def presentationOfEquivalence
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (source : FullDimensionalSourcePresentation first coordinate)
    (certificate : Equivalence first second)
    (destinationValid : second.Valid)
    (destinationTargetConnected : graph_connected target₂)
    (destinationTargetGenus : genus target₂ = 0)
    (targetEdgeCard : target₂.edges.card = target₁.edges.card)
    (sourceGenus : genus second.sourceGraph = genus first.sourceGraph)
    (destinationLabelling : StableLengthMatrixLabelling second coordinate)
    (destinationDet :
      (GluingDatum.LengthMatrixPresentation.matrix
        destinationLabelling.presentation).det ≠ 0) :
    FullDimensionalSourcePresentation second coordinate where
  valid := destinationValid
  targetConnected := destinationTargetConnected
  targetGenus := destinationTargetGenus
  saturated := by
    rw [targetEdgeCard, sourceGenus]
    exact source.saturated
  labelling := destinationLabelling
  det_ne_zero := destinationDet
  trivalent := trivalent_of_equivalence certificate source.trivalent
  pathEnds := certificate.hasPathEnds source.valid.1 source.pathEnds

/-- Concrete sanity consumer: the generic valency argument recovers
trivalence after any compatible sheet relabelling. -/
theorem trivalent_sheetRelabel
    {target : CFGraph} {data : GluingDatum target degree}
    (relabeling : data.SheetRelabeling) (hConnected : data.Connected)
    (hTrivalent : ∀ vertex : data.SourceVertex,
      nonDanglingValency data vertex ≤ 3) :
    ∀ vertex : relabeling.apply.SourceVertex,
      nonDanglingValency relabeling.apply vertex ≤ 3 :=
  trivalent_of_equivalence (StableGraphIncidence.sheetRelabel relabeling hConnected)
    hTrivalent

end DraismaVargas.LocalCases.StableGraphFullDimensional
