module

public import DraismaVargas.LocalCases.FullDimensionalSource
public import DraismaVargas.LocalCases.StablePathCount
public import DraismaVargas.LocalCases.StableGraphIncidence

@[expose] public section

/-!
# The marked stable graph and the marked labelling

A marked discrete tropical morphism declares some surviving valency-two source vertices to be
**marks**. The **marked stable graph** `H(φ; marks)` has as vertices the surviving vertices of
valency at least three together with the marks, and as edges the maximal paths of surviving
occurrences whose interior vertices have surviving valency two and are not marks. In Lean:

* `MarkedConsecutive data marks`: two distinct surviving occurrences meeting at a surviving
  valency-two vertex **that is not a mark** (the unmarked `W4StableSource.Consecutive` with one
  more clause);
* `MarkedStablePath data marks := Quot (MarkedConsecutive data marks)`, the rows of the marked
  matrix `A_{φ;u,v}`;
* `MarkedBranchVertex data marks`, the vertices of `H(φ; marks)`;
* `markedIncidenceCount`, the incidence multiplicity of a marked row at a vertex (a marked row
  through no mark that closes up counts twice, as `StablePathCount.incidenceCount` does);
* `HasMarkedPathEnds`, the analogue of `W4StableSource.HasPathEnds`: every marked row
  has an end, at a vertex of surviving valency `≠ 2` or at a mark;
* `MarkedLabelling data marks coordinate`, the generalization of
  `W4StableSource.StableLengthMatrixLabelling` with marked rows, and its literal presentation,
  whose matrix is the marked edge-length matrix `A_{φ;u,v}`.

## What is proved here

* `markedConsecutive_empty_iff`, `markedStablePathEmptyEquiv`,
  `markedBranchVertexEmptyEquiv`: with no marks, the marked notions **are** the unmarked ones.
  This is the check that the generalization is the right one.
* `MarkedStablePath.toStablePath`: every marked row lies in one unmarked stable path (marks only
  cut paths).
-/

namespace DraismaVargas.Count.MarkedCount

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource

variable {target : CFGraph} {degree : ℕ}

/-! ## 1.  Marked rows -/

/-- Two surviving occurrences are **consecutive along a marked row** when they are distinct and
meet at a surviving valency-two vertex that is not a mark. -/
def MarkedConsecutive (data : GluingDatum target degree) (marks : Finset data.SourceVertex)
    (first second : NonDanglingEdge data) : Prop :=
  first ≠ second ∧ ∃ vertex : data.SourceVertex,
    Incident data first.1 vertex ∧ Incident data second.1 vertex ∧
      nonDanglingValency data vertex = 2 ∧ vertex ∉ marks

/-- **The marked rows**: the rows of the marked edge-length matrix. -/
def MarkedStablePath (data : GluingDatum target degree) (marks : Finset data.SourceVertex) :=
  Quot (MarkedConsecutive data marks)

noncomputable instance (data : GluingDatum target degree) (marks : Finset data.SourceVertex) :
    Fintype (MarkedStablePath data marks) := by
  letI : Finite (MarkedStablePath data marks) := Quot.finite (MarkedConsecutive data marks)
  exact Fintype.ofFinite _

noncomputable instance (data : GluingDatum target degree) (marks : Finset data.SourceVertex) :
    DecidableEq (MarkedStablePath data marks) :=
  Classical.decEq _

/-- The marked row containing a surviving occurrence. -/
def markedRow {data : GluingDatum target degree}
    (marks : Finset data.SourceVertex) (edge : NonDanglingEdge data) :
    MarkedStablePath data marks :=
  Quot.mk _ edge

theorem markedRow_eq_of_markedConsecutive {data : GluingDatum target degree}
    {marks : Finset data.SourceVertex} {first second : NonDanglingEdge data}
    (h : MarkedConsecutive data marks first second) :
    markedRow marks first = markedRow marks second :=
  Quot.sound h

/-- Marked consecutiveness is unmarked consecutiveness away from the marks. -/
theorem MarkedConsecutive.consecutive {data : GluingDatum target degree}
    {marks : Finset data.SourceVertex} {first second : NonDanglingEdge data}
    (h : MarkedConsecutive data marks first second) : Consecutive data first second := by
  obtain ⟨hne, vertex, h1, h2, h3, -⟩ := h
  exact ⟨hne, vertex, h1, h2, h3⟩

/-- **Marks only cut rows**: every marked row lies in one unmarked stable path. -/
def MarkedStablePath.toStablePath {data : GluingDatum target degree}
    {marks : Finset data.SourceVertex} : MarkedStablePath data marks → StablePath data :=
  Quot.lift (fun edge ↦ NonDanglingEdge.stablePath edge) fun _ _ h ↦ Quot.sound h.consecutive

/-! ## 2.  Marked vertices and incidences -/

/-- **The vertices of the marked stable graph**: surviving valency at least three, or a mark. -/
def MarkedBranchVertex (data : GluingDatum target degree) (marks : Finset data.SourceVertex) :=
  {vertex : data.SourceVertex // 3 ≤ nonDanglingValency data vertex ∨ vertex ∈ marks}

/-- The number of surviving occurrences of the marked row `path` meeting `vertex`, the marked
twin of `StablePathCount.incidenceCount`. -/
noncomputable def markedIncidenceCount (data : GluingDatum target degree)
    (marks : Finset data.SourceVertex) (vertex : data.SourceVertex)
    (path : MarkedStablePath data marks) : ℕ :=
  ((StablePathCount.incidentEdges data vertex).filter fun edge ↦
    markedRow marks edge = path).card

/-- An end of a marked row: an incident vertex of surviving valency other than two, or a
mark. -/
def IsMarkedPathEnd (data : GluingDatum target degree) (marks : Finset data.SourceVertex)
    (edge : data.SourceEdge) (vertex : data.SourceVertex) : Prop :=
  Incident data edge vertex ∧ (nonDanglingValency data vertex ≠ 2 ∨ vertex ∈ marks)

/-- **No marked row is a cycle**: the marked twin of
`W4StableSource.HasPathEnds`. -/
def HasMarkedPathEnds (data : GluingDatum target degree) (marks : Finset data.SourceVertex) :
    Prop :=
  ∀ edge : NonDanglingEdge data, ∃ first : NonDanglingEdge data, ∃ vertex : data.SourceVertex,
    markedRow marks first = markedRow marks edge ∧ IsMarkedPathEnd data marks first.1 vertex

/-! ## 3.  The marked labelling -/

/-- **The marked labelling**: a square labelling of the marked rows and the
target edge occurrences, the generalization of `W4StableSource.StableLengthMatrixLabelling` in
which the rows are `MarkedStablePath data marks`. -/
structure MarkedLabelling (data : GluingDatum target degree) (marks : Finset data.SourceVertex)
    (coordinate : Type*) where
  targetEdge : coordinate ≃ target.edges
  row : MarkedStablePath data marks ≃ coordinate

namespace MarkedLabelling

variable {coordinate : Type*} {data : GluingDatum target degree}
  {marks : Finset data.SourceVertex}

/-- All surviving occurrences in one labelled marked row, as in
`StableLengthMatrixLabelling.path`. -/
noncomputable def path (labelling : MarkedLabelling data marks coordinate) (row : coordinate) :
    List data.SourceEdge := by
  classical
  exact (Finset.univ : Finset data.SourceEdge).toList.filter fun edge ↦
    ∃ hSurvives : ¬ IsDangling data edge,
      labelling.row
        (markedRow marks (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = row

/-- **The marked edge-length presentation**; its matrix is `A_{φ;u,v}`. -/
noncomputable def presentation (labelling : MarkedLabelling data marks coordinate) :
    data.LengthMatrixPresentation coordinate where
  targetEdge := labelling.targetEdge
  path := labelling.path

end MarkedLabelling

/-! ## 4.  No marks: the unmarked notions -/

section Empty

variable (data : GluingDatum target degree)

theorem markedConsecutive_empty_iff (first second : NonDanglingEdge data) :
    MarkedConsecutive data ∅ first second ↔ Consecutive data first second := by
  simp [MarkedConsecutive, Consecutive]

/-- **With no marks, the marked rows are the stable paths.** -/
def markedStablePathEmptyEquiv : MarkedStablePath data ∅ ≃ StablePath data :=
  Quot.congr (Equiv.refl _) fun first second ↦ markedConsecutive_empty_iff data first second

/-- **With no marks, the marked vertices are the branch vertices.** -/
def markedBranchVertexEmptyEquiv :
    MarkedBranchVertex data ∅ ≃ StableGraphIncidence.BranchVertex data :=
  Equiv.subtypeEquivRight fun vertex ↦ by simp

end Empty

end DraismaVargas.Count.MarkedCount
