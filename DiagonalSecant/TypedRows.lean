module

public import DraismaVargasMarkedCount.MarkedCountGeneral.TypedFrame
public import DraismaVargas.LocalCases.OrientedTraversal
public import DraismaVargasCount.RowRealizedPosition

@[expose] public section

/-!
# The ordered walk of a marked row, and its vertices

This is the marked twin of the row layer of the public placement chain:

| public (unmarked, on `FullDimensionalSourcePresentation`) | here (marked, on `TypedFullDim`) |
|---|---|
| `W4StableSource.traverse` | `markedTraverse` |
| `RowWalk.orderedRow`, `startEdge`, `startVertex`, `OnRow` | `orderedRow`, `startEdge`, `startVertex`, `OnRow` |
| `RowPosition.rowVertex`, `prefixPosition` | `rowVertex`, `prefixPosition` |
| `RowSlotOrientation.startBranch`, `finishBranch`, `branch_incident_eq_endpoint` | the same names, on `MarkedBranchVertex` |
| `SurvivingSlotMap.InteriorAddress`, `addressVertex`, `addressEquiv` | the same names |
| `RowVertexEnumeration.exists_interior_index`, `row_eq_of_interior_eq`, … | the same names |
| `RowRealizedPosition.integralPrefix`, `collisionCoefficient` | the same names |

The one new idea: a marked row (`MarkedStablePath data marks`,
`DraismaVargasMarkedCount.MarkedCount.MarkedPath`) is cut at the marks as well as at the branch
vertices, so the walk **stops at a mark**: `markedTraverse`
continues through a vertex exactly when it has surviving valency two **and is not a mark**. A
mark is therefore a row **end**, never an interior vertex, and the ends of a marked row are the
marked branch vertices (`MarkedBranchVertex`: surviving valency `≥ 3`, or a mark). Everything
else is the public development with `nonDanglingValency = 2` replaced by
`nonDanglingValency = 2 ∧ ∉ marks` and `IsPathEnd` by `IsMarkedPathEnd`.

The row layer is stated on `fd : TypedFullDim data marks coordinate excess` with `excess` **free**
(the typed dimension count is never used here), so it serves every typed frame of the two-point
ramified count and, through `Agreement`, every marked frame of the count at ramification one;
the walk itself (§1–§2) needs only `HasMarkedPathEnds`.
The public generic walk engine (`OrientedTraversal.walkVertex`, `walkVertex_succ`,
`eq_or_eq_otherEnd`) is reused; `OrientedTraversal.walk_invariant` is not, because its start must
be a path end of valency `≠ 2` and a marked row may start at a mark of valency two, so the
invariant is re-proved here (`markedWalk_invariant`) with the closure clause restricted to
non-marks.
-/

namespace DiagonalSecant.TypedRows

open DraismaVargas.Infrastructure DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.OrientedTraversal
open DraismaVargas.LocalCases.TraversalPresentation (MeetsAt otherEnd_ne)
open DraismaVargas.Count DraismaVargas.Count.MarkedCount DraismaVargas.Count.MarkedCountGeneral
open DraismaVargas.Count.PendantRetraction

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}

/-! ## 1.  The marked traversal -/

section Traverse

variable (data) (marks : Finset data.SourceVertex)

/-- **The marked walk**: `W4StableSource.traverse` stopping at the marks. `edge` is the current
surviving occurrence, `vertex` the end through which it was entered, `visited` the occurrences
already emitted. The walk continues through the far end exactly when that end has surviving
valency two **and is not a mark**. -/
noncomputable def markedTraverse (visited : Finset data.SourceEdge) (edge : data.SourceEdge)
    (vertex : data.SourceVertex) : List data.SourceEdge :=
  if _hVisited : edge ∈ visited then []
  else if hCont : nonDanglingValency data (otherEnd data edge vertex) = 2 ∧
      otherEnd data edge vertex ∉ marks then
    edge :: markedTraverse (insert edge visited) (stepEdge data hCont.1 edge)
      (otherEnd data edge vertex)
  else [edge]
termination_by ((Finset.univ : Finset data.SourceEdge) \ visited).card
decreasing_by exact card_sdiff_insert_lt data (by assumption)

theorem markedTraverse_of_mem {visited : Finset data.SourceEdge} {edge : data.SourceEdge}
    (vertex : data.SourceVertex) (hVisited : edge ∈ visited) :
    markedTraverse data marks visited edge vertex = [] := by
  rw [markedTraverse.eq_def, dite_eq_left hVisited]

theorem markedTraverse_of_stop {visited : Finset data.SourceEdge} {edge : data.SourceEdge}
    {vertex : data.SourceVertex} (hVisited : edge ∉ visited)
    (hStop : ¬ (nonDanglingValency data (otherEnd data edge vertex) = 2 ∧
      otherEnd data edge vertex ∉ marks)) :
    markedTraverse data marks visited edge vertex = [edge] := by
  rw [markedTraverse.eq_def, dite_eq_right hVisited, dite_eq_right hStop]

theorem markedTraverse_of_step {visited : Finset data.SourceEdge} {edge : data.SourceEdge}
    {vertex : data.SourceVertex} (hVisited : edge ∉ visited)
    (hCont : nonDanglingValency data (otherEnd data edge vertex) = 2 ∧
      otherEnd data edge vertex ∉ marks) :
    markedTraverse data marks visited edge vertex =
      edge :: markedTraverse data marks (insert edge visited) (stepEdge data hCont.1 edge)
        (otherEnd data edge vertex) := by
  rw [markedTraverse.eq_def, dite_eq_right hVisited, dite_eq_left hCont]

/-- The recursion principle matching `markedTraverse`. -/
theorem markedTraverse_rec
    {motive : Finset data.SourceEdge → data.SourceEdge → data.SourceVertex → Prop}
    (visitedCase : ∀ visited edge vertex, edge ∈ visited → motive visited edge vertex)
    (stopCase : ∀ visited edge vertex, edge ∉ visited →
      ¬ (nonDanglingValency data (otherEnd data edge vertex) = 2 ∧
        otherEnd data edge vertex ∉ marks) →
      motive visited edge vertex)
    (stepCase : ∀ visited edge vertex, edge ∉ visited →
      ∀ hCont : nonDanglingValency data (otherEnd data edge vertex) = 2 ∧
        otherEnd data edge vertex ∉ marks,
      motive (insert edge visited) (stepEdge data hCont.1 edge) (otherEnd data edge vertex) →
        motive visited edge vertex)
    (visited : Finset data.SourceEdge) (edge : data.SourceEdge) (vertex : data.SourceVertex) :
    motive visited edge vertex := by
  classical
  suffices hAll : ∀ bound (visited : Finset data.SourceEdge) (edge : data.SourceEdge)
      (vertex : data.SourceVertex),
      ((Finset.univ : Finset data.SourceEdge) \ visited).card ≤ bound →
      motive visited edge vertex from
    hAll _ visited edge vertex le_rfl
  intro bound
  induction bound with
  | zero =>
    intro visited edge vertex hBound
    by_cases hVisited : edge ∈ visited
    · exact visitedCase visited edge vertex hVisited
    · exfalso
      have hMem : edge ∈ (Finset.univ : Finset data.SourceEdge) \ visited :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hVisited⟩
      have hPos := Finset.card_pos.mpr ⟨edge, hMem⟩
      omega
  | succ bound ih =>
    intro visited edge vertex hBound
    by_cases hVisited : edge ∈ visited
    · exact visitedCase visited edge vertex hVisited
    · by_cases hCont : nonDanglingValency data (otherEnd data edge vertex) = 2 ∧
          otherEnd data edge vertex ∉ marks
      · refine stepCase visited edge vertex hVisited hCont (ih _ _ _ ?_)
        have hLt := card_sdiff_insert_lt data hVisited
        omega
      · exact stopCase visited edge vertex hVisited hCont

theorem mem_markedTraverse_self (visited : Finset data.SourceEdge) (edge : data.SourceEdge)
    (vertex : data.SourceVertex) (hVisited : edge ∉ visited) :
    edge ∈ markedTraverse data marks visited edge vertex := by
  by_cases hCont : nonDanglingValency data (otherEnd data edge vertex) = 2 ∧
      otherEnd data edge vertex ∉ marks
  · rw [markedTraverse_of_step data marks hVisited hCont]; simp
  · rw [markedTraverse_of_stop data marks hVisited hCont]; simp

theorem markedTraverse_head? (visited : Finset data.SourceEdge) (edge : data.SourceEdge)
    (vertex : data.SourceVertex) (hVisited : edge ∉ visited) :
    (markedTraverse data marks visited edge vertex).head? = some edge := by
  by_cases hCont : nonDanglingValency data (otherEnd data edge vertex) = 2 ∧
      otherEnd data edge vertex ∉ marks
  · rw [markedTraverse_of_step data marks hVisited hCont]; rfl
  · rw [markedTraverse_of_stop data marks hVisited hCont]; rfl

theorem markedTraverse_head?' (visited : Finset data.SourceEdge) (edge : data.SourceEdge)
    (vertex : data.SourceVertex) :
    ∀ first ∈ (markedTraverse data marks visited edge vertex).head?, first = edge := by
  by_cases hVisited : edge ∈ visited
  · rw [markedTraverse_of_mem data marks vertex hVisited]; simp
  · rw [markedTraverse_head? data marks visited edge vertex hVisited]; simp

/-- Consecutive entries meet at a surviving valency-two vertex that is not a mark: the chain
relation of a marked row (`MarkedConsecutive` without the inequality). -/
def MeetsAtNonMark (first second : data.SourceEdge) : Prop :=
  ∃ vertex : data.SourceVertex, Incident data first vertex ∧ Incident data second vertex ∧
    nonDanglingValency data vertex = 2 ∧ vertex ∉ marks

theorem MeetsAtNonMark.meetsAt {first second : data.SourceEdge}
    (h : MeetsAtNonMark data marks first second) : MeetsAt data first second := by
  obtain ⟨v, h1, h2, h3, -⟩ := h
  exact ⟨v, h1, h2, h3⟩

/-- The emitted occurrences are pairwise distinct and none was visited before. -/
theorem markedTraverse_nodup_notMem (visited : Finset data.SourceEdge) (edge : data.SourceEdge)
    (vertex : data.SourceVertex) :
    (markedTraverse data marks visited edge vertex).Nodup ∧
      ∀ e ∈ markedTraverse data marks visited edge vertex, e ∉ visited := by
  refine markedTraverse_rec data marks (motive := fun visited edge vertex ↦
    (markedTraverse data marks visited edge vertex).Nodup ∧
      ∀ e ∈ markedTraverse data marks visited edge vertex, e ∉ visited)
    ?_ ?_ ?_ visited edge vertex
  · intro visited edge vertex hVisited
    rw [markedTraverse_of_mem data marks vertex hVisited]
    exact ⟨List.nodup_nil, by simp⟩
  · intro visited edge vertex hVisited hStop
    rw [markedTraverse_of_stop data marks hVisited hStop]
    refine ⟨List.nodup_singleton _, ?_⟩
    intro emitted hEmitted
    rw [List.mem_singleton] at hEmitted
    subst hEmitted
    exact hVisited
  · intro visited edge vertex hVisited hCont ih
    obtain ⟨ihNodup, ihNotMem⟩ := ih
    rw [markedTraverse_of_step data marks hVisited hCont]
    refine ⟨List.nodup_cons.mpr ⟨fun hMem ↦ ?_, ihNodup⟩, ?_⟩
    · exact ihNotMem edge hMem (Finset.mem_insert_self _ _)
    · intro emitted hEmitted
      rcases List.mem_cons.mp hEmitted with hEq | hTail
      · subst hEq
        exact hVisited
      · exact fun hMem ↦ ihNotMem emitted hTail (Finset.mem_insert_of_mem hMem)

/-- Consecutive entries of the marked walk meet at a surviving valency-two non-mark vertex. -/
theorem markedTraverse_chain (visited : Finset data.SourceEdge) (edge : data.SourceEdge)
    (vertex : data.SourceVertex) :
    (markedTraverse data marks visited edge vertex).IsChain (MeetsAtNonMark data marks) := by
  refine markedTraverse_rec data marks (motive := fun visited edge vertex ↦
    (markedTraverse data marks visited edge vertex).IsChain (MeetsAtNonMark data marks))
    ?_ ?_ ?_ visited edge vertex
  · intro visited edge vertex hVisited
    rw [markedTraverse_of_mem data marks vertex hVisited]
    exact List.IsChain.nil
  · intro visited edge vertex hVisited hStop
    rw [markedTraverse_of_stop data marks hVisited hStop]
    exact List.IsChain.singleton _
  · intro visited edge vertex hVisited hCont ih
    rw [markedTraverse_of_step data marks hVisited hCont]
    refine ih.cons ?_
    intro second hSecond
    have hEq := markedTraverse_head?' data marks (insert edge visited)
      (stepEdge data hCont.1 edge) (otherEnd data edge vertex) second hSecond
    subst hEq
    exact ⟨otherEnd data edge vertex, incident_otherEnd data edge vertex,
      stepEdge_incident data hCont.1 edge, hCont.1, hCont.2⟩

/-- Every emitted occurrence survives and lies on the marked row of the start. -/
theorem markedTraverse_markedRow (visited : Finset data.SourceEdge) (edge : data.SourceEdge)
    (vertex : data.SourceVertex) (hSurvives : ¬ IsDangling data edge)
    (e : data.SourceEdge) (he : e ∈ markedTraverse data marks visited edge vertex) :
    ∃ hs : ¬ IsDangling data e,
      markedRow marks (⟨e, hs⟩ : NonDanglingEdge data) = markedRow marks ⟨edge, hSurvives⟩ := by
  refine markedTraverse_rec data marks (motive := fun visited edge vertex ↦
    ∀ hEdge : ¬ IsDangling data edge, ∀ emitted : data.SourceEdge,
      emitted ∈ markedTraverse data marks visited edge vertex →
      ∃ hs : ¬ IsDangling data emitted,
        markedRow marks (⟨emitted, hs⟩ : NonDanglingEdge data) = markedRow marks ⟨edge, hEdge⟩)
    ?_ ?_ ?_ visited edge vertex hSurvives e he
  · intro visited edge vertex hVisited _ emitted hEmitted
    rw [markedTraverse_of_mem data marks vertex hVisited] at hEmitted
    simp at hEmitted
  · intro visited edge vertex hVisited hStop hEdge emitted hEmitted
    rw [markedTraverse_of_stop data marks hVisited hStop, List.mem_singleton] at hEmitted
    subst hEmitted
    exact ⟨hEdge, rfl⟩
  · intro visited edge vertex hVisited hCont ih hEdge emitted hEmitted
    rw [markedTraverse_of_step data marks hVisited hCont] at hEmitted
    have hStepSurvives : ¬ IsDangling data (stepEdge data hCont.1 edge) :=
      stepEdge_not_dangling data hCont.1 edge
    have hConsecutive : MarkedConsecutive data marks ⟨edge, hEdge⟩
        ⟨stepEdge data hCont.1 edge, hStepSurvives⟩ := by
      refine ⟨fun hEq ↦ ?_, otherEnd data edge vertex, incident_otherEnd data edge vertex,
        stepEdge_incident data hCont.1 edge, hCont.1, hCont.2⟩
      exact stepEdge_ne data hCont.1 edge (congrArg Subtype.val hEq).symm
    rcases List.mem_cons.mp hEmitted with hEq | hTail
    · subst hEq
      exact ⟨hEdge, rfl⟩
    · obtain ⟨hs, hPath⟩ := ih hStepSurvives emitted hTail
      exact ⟨hs, hPath.trans (markedRow_eq_of_markedConsecutive hConsecutive).symm⟩

/-- The marked traversal is closed under passage through surviving valency-two non-mark
vertices, except possibly at the end through which it was started
(`W4StableSource.traverse_closed`). -/
theorem markedTraverse_closed (visited : Finset data.SourceEdge) (edge : data.SourceEdge)
    (vertex : data.SourceVertex) (hEdge : ¬ IsDangling data edge)
    (hIncident : Incident data edge vertex) {meeting : data.SourceVertex}
    (hValency : nonDanglingValency data meeting = 2) (hMark : meeting ∉ marks)
    (emitted neighbour : data.SourceEdge)
    (hEmitted : emitted ∈ markedTraverse data marks visited edge vertex)
    (hNeighbour : ¬ IsDangling data neighbour) (hNe : neighbour ≠ emitted)
    (hEmittedMeets : Incident data emitted meeting)
    (hNeighbourMeets : Incident data neighbour meeting) :
    neighbour ∈ markedTraverse data marks visited edge vertex ∨ neighbour ∈ visited ∨
      (Incident data neighbour vertex ∧ nonDanglingValency data vertex = 2 ∧ vertex ∉ marks) := by
  refine markedTraverse_rec data marks (motive := fun visited edge vertex ↦
    ¬ IsDangling data edge → Incident data edge vertex →
    ∀ emitted neighbour : data.SourceEdge,
      emitted ∈ markedTraverse data marks visited edge vertex →
      ¬ IsDangling data neighbour → neighbour ≠ emitted →
      Incident data emitted meeting → Incident data neighbour meeting →
      neighbour ∈ markedTraverse data marks visited edge vertex ∨ neighbour ∈ visited ∨
        (Incident data neighbour vertex ∧ nonDanglingValency data vertex = 2 ∧ vertex ∉ marks))
    ?_ ?_ ?_ visited edge vertex hEdge hIncident emitted neighbour hEmitted
    hNeighbour hNe hEmittedMeets hNeighbourMeets
  · intro visited edge vertex hVisited _ _ emitted _ hEmitted
    rw [markedTraverse_of_mem data marks vertex hVisited] at hEmitted
    simp at hEmitted
  · intro visited edge vertex hVisited hStop hEdge hIncident emitted neighbour
      hEmitted hNeighbour hNe hEmittedMeets hNeighbourMeets
    rw [markedTraverse_of_stop data marks hVisited hStop, List.mem_singleton] at hEmitted
    rw [hEmitted] at hEmittedMeets
    rcases eq_or_eq_otherEnd data hIncident hEmittedMeets with hMeeting | hMeeting
    · rw [hMeeting] at hNeighbourMeets hValency hMark
      exact Or.inr (Or.inr ⟨hNeighbourMeets, hValency, hMark⟩)
    · exfalso
      apply hStop
      rw [← hMeeting]
      exact ⟨hValency, hMark⟩
  · intro visited edge vertex hVisited hStep ih hEdge hIncident emitted neighbour
      hEmitted hNeighbour hNe hEmittedMeets hNeighbourMeets
    have hStepSurvives : ¬ IsDangling data (stepEdge data hStep.1 edge) :=
      stepEdge_not_dangling data hStep.1 edge
    have hStepIncident : Incident data (stepEdge data hStep.1 edge)
        (otherEnd data edge vertex) := stepEdge_incident data hStep.1 edge
    have hStepMem : stepEdge data hStep.1 edge ∈
        edge :: markedTraverse data marks (insert edge visited) (stepEdge data hStep.1 edge)
          (otherEnd data edge vertex) ∨ stepEdge data hStep.1 edge ∈ visited := by
      by_cases hMem : stepEdge data hStep.1 edge ∈ insert edge visited
      · rcases Finset.mem_insert.mp hMem with hEq | hMemVisited
        · exact absurd hEq (stepEdge_ne data hStep.1 edge)
        · exact Or.inr hMemVisited
      · exact Or.inl (List.mem_cons_of_mem _
          (mem_markedTraverse_self data marks _ _ (otherEnd data edge vertex) hMem))
    rw [markedTraverse_of_step data marks hVisited hStep] at hEmitted ⊢
    rcases List.mem_cons.mp hEmitted with hEq | hTail
    · rw [hEq] at hEmittedMeets hNe
      rcases eq_or_eq_otherEnd data hIncident hEmittedMeets with hMeeting | hMeeting
      · rw [hMeeting] at hNeighbourMeets hValency hMark
        exact Or.inr (Or.inr ⟨hNeighbourMeets, hValency, hMark⟩)
      · rw [hMeeting] at hNeighbourMeets
        rcases eq_or_eq_stepEdge data hStep.1 hEdge
          (incident_otherEnd data edge vertex) hNeighbour hNeighbourMeets with
          hCase | hCase
        · exact absurd hCase hNe
        · rw [hCase]
          rcases hStepMem with hMem | hMem
          · exact Or.inl hMem
          · exact Or.inr (Or.inl hMem)
    · rcases ih hStepSurvives hStepIncident emitted neighbour hTail hNeighbour hNe
        hEmittedMeets hNeighbourMeets with hCase | hCase | hCase
      · exact Or.inl (List.mem_cons_of_mem _ hCase)
      · rcases Finset.mem_insert.mp hCase with hMemEq | hMemVisited
        · rw [hMemEq]
          exact Or.inl (by simp)
        · exact Or.inr (Or.inl hMemVisited)
      · rcases eq_or_eq_stepEdge data hStep.1 hEdge
          (incident_otherEnd data edge vertex) hNeighbour hCase.1 with hEq | hEq
        · rw [hEq]
          exact Or.inl (by simp)
        · rw [hEq]
          rcases hStepMem with hMem | hMem
          · exact Or.inl hMem
          · exact Or.inr (Or.inl hMem)

theorem markedConsecutive_symm {first second : NonDanglingEdge data}
    (h : MarkedConsecutive data marks first second) : MarkedConsecutive data marks second first := by
  obtain ⟨hNe, meeting, hFirst, hSecond, hValency, hMark⟩ := h
  exact ⟨hNe.symm, meeting, hSecond, hFirst, hValency, hMark⟩

/-- A property closed under a symmetric relation is constant along its equivalence closure. -/
private theorem eqvGen_iff_of_closed {α : Type*} {r : α → α → Prop}
    (hSymm : ∀ a b, r a b → r b a) {property : α → Prop}
    (hClosed : ∀ a b, r a b → property a → property b) {a b : α}
    (hEqv : Relation.EqvGen r a b) : property a ↔ property b := by
  induction hEqv with
  | rel x y hxy => exact ⟨hClosed x y hxy, hClosed y x (hSymm x y hxy)⟩
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- **The traversal started at a marked path end emits every surviving occurrence of the marked
row.** -/
theorem mem_markedTraverse_of_markedRow_eq {first : NonDanglingEdge data}
    {vertex : data.SourceVertex} (hEnd : IsMarkedPathEnd data marks first.1 vertex)
    (edge : NonDanglingEdge data) (hRow : markedRow marks edge = markedRow marks first) :
    edge.1 ∈ markedTraverse data marks ∅ first.1 vertex := by
  have hClosed : ∀ a b : NonDanglingEdge data, MarkedConsecutive data marks a b →
      a.1 ∈ markedTraverse data marks ∅ first.1 vertex →
      b.1 ∈ markedTraverse data marks ∅ first.1 vertex := by
    intro a b hConsecutive hMem
    obtain ⟨hNe, meeting, hA, hB, hValency, hMark⟩ := hConsecutive
    rcases markedTraverse_closed data marks ∅ first.1 vertex first.2 hEnd.1 hValency hMark a.1 b.1
      hMem b.2 (fun hEq ↦ hNe (Subtype.ext hEq.symm)) hA hB with hCase | hCase | hCase
    · exact hCase
    · simp at hCase
    · rcases hEnd.2 with hTwo | hIn
      · exact absurd hCase.2.1 hTwo
      · exact absurd hIn hCase.2.2
  exact (eqvGen_iff_of_closed (fun _ _ h ↦ markedConsecutive_symm data marks h)
    (property := fun candidate ↦ candidate.1 ∈ markedTraverse data marks ∅ first.1 vertex)
    hClosed (Quot.eq.mp hRow)).mpr
    (mem_markedTraverse_self data marks ∅ first.1 vertex (by simp))

end Traverse

/-! ## 2.  The ordered marked row -/

section Ordered

variable {marks : Finset data.SourceVertex}

/-- `edge` is displayed on the marked row `path`: it survives and its marked row is `path`. -/
def OnRow (marks : Finset data.SourceVertex) (path : MarkedStablePath data marks)
    (edge : data.SourceEdge) : Prop :=
  ∃ hSurvives : ¬ IsDangling data edge,
    markedRow marks (⟨edge, hSurvives⟩ : NonDanglingEdge data) = path

theorem OnRow.survives {path : MarkedStablePath data marks} {edge : data.SourceEdge}
    (h : OnRow marks path edge) : ¬ IsDangling data edge := h.choose

/-- A chosen surviving representative of a marked row. -/
noncomputable def pathRepresentative (path : MarkedStablePath data marks) : NonDanglingEdge data :=
  (Quot.exists_rep path).choose

theorem pathRepresentative_markedRow (path : MarkedStablePath data marks) :
    markedRow marks (pathRepresentative path) = path :=
  (Quot.exists_rep path).choose_spec

variable (hEnds : HasMarkedPathEnds data marks)

/-- A chosen end occurrence of the marked row `path`. -/
noncomputable def startEdge (path : MarkedStablePath data marks) : NonDanglingEdge data :=
  (hEnds (pathRepresentative path)).choose

/-- The vertex through which the walk of `path` starts: a marked path end. -/
noncomputable def startVertex (path : MarkedStablePath data marks) : data.SourceVertex :=
  (hEnds (pathRepresentative path)).choose_spec.choose

theorem startEdge_markedRow (path : MarkedStablePath data marks) :
    markedRow marks (startEdge hEnds path) = path :=
  ((hEnds (pathRepresentative path)).choose_spec.choose_spec).1.trans
    (pathRepresentative_markedRow path)

theorem startEdge_isMarkedPathEnd (path : MarkedStablePath data marks) :
    IsMarkedPathEnd data marks (startEdge hEnds path).1 (startVertex hEnds path) :=
  ((hEnds (pathRepresentative path)).choose_spec.choose_spec).2

/-- **The ordered walk of a marked row**: `RowWalk.orderedRow` with the marked traversal. -/
noncomputable def orderedRow (path : MarkedStablePath data marks) : List data.SourceEdge :=
  markedTraverse data marks ∅ (startEdge hEnds path).1 (startVertex hEnds path)

theorem mem_orderedRow_iff (path : MarkedStablePath data marks) (edge : data.SourceEdge) :
    edge ∈ orderedRow hEnds path ↔ OnRow marks path edge := by
  constructor
  · intro hMem
    obtain ⟨hs, hRow⟩ := markedTraverse_markedRow data marks ∅ _ _ (startEdge hEnds path).2
      edge hMem
    exact ⟨hs, hRow.trans (startEdge_markedRow hEnds path)⟩
  · rintro ⟨hs, hRow⟩
    exact mem_markedTraverse_of_markedRow_eq data marks (startEdge_isMarkedPathEnd hEnds path)
      ⟨edge, hs⟩ (hRow.trans (startEdge_markedRow hEnds path).symm)

theorem orderedRow_nodup (path : MarkedStablePath data marks) : (orderedRow hEnds path).Nodup :=
  (markedTraverse_nodup_notMem data marks ∅ _ _).1

theorem orderedRow_chain (path : MarkedStablePath data marks) :
    (orderedRow hEnds path).IsChain (MeetsAtNonMark data marks) :=
  markedTraverse_chain data marks ∅ _ _

theorem orderedRow_head? (path : MarkedStablePath data marks) :
    (orderedRow hEnds path).head? = some (startEdge hEnds path).1 :=
  markedTraverse_head? data marks ∅ _ _ (by simp)

theorem startEdge_mem_orderedRow (path : MarkedStablePath data marks) :
    (startEdge hEnds path).1 ∈ orderedRow hEnds path :=
  (mem_orderedRow_iff hEnds path _).mpr ⟨(startEdge hEnds path).2, startEdge_markedRow hEnds path⟩

theorem orderedRow_length_pos (path : MarkedStablePath data marks) :
    0 < (orderedRow hEnds path).length :=
  List.length_pos_of_mem (startEdge_mem_orderedRow hEnds path)

theorem orderedRow_survives (path : MarkedStablePath data marks) :
    ∀ edge ∈ orderedRow hEnds path, ¬ IsDangling data edge :=
  fun _ h ↦ ((mem_orderedRow_iff hEnds path _).mp h).survives

theorem orderedRow_getElem_zero (path : MarkedStablePath data marks) :
    (orderedRow hEnds path)[0]'(orderedRow_length_pos hEnds path) = (startEdge hEnds path).1 := by
  have hHead := orderedRow_head? hEnds path
  rw [head?_eq_getElem _ (orderedRow_length_pos hEnds path), Option.some.injEq] at hHead
  exact hHead

/-- **The walk does not leave its row**: the partner of a row occurrence at a surviving
valency-two non-mark vertex lies on the same marked row (`RowWalk.onRow_of_incident`). -/
theorem onRow_of_incident {path : MarkedStablePath data marks} {vertex : data.SourceVertex}
    (hValency : nonDanglingValency data vertex = 2) (hMark : vertex ∉ marks)
    {edge partner : data.SourceEdge} (hEdge : OnRow marks path edge)
    (hIncident : Incident data edge vertex) (hPartnerSurvives : ¬ IsDangling data partner)
    (hPartnerIncident : Incident data partner vertex) : OnRow marks path partner := by
  obtain ⟨hSurvives, hPath⟩ := hEdge
  by_cases hEq : partner = edge
  · exact ⟨hPartnerSurvives, by
      rw [show (⟨partner, hPartnerSurvives⟩ : NonDanglingEdge data) =
        ⟨edge, hSurvives⟩ from Subtype.ext hEq]; exact hPath⟩
  · refine ⟨hPartnerSurvives, ?_⟩
    have hCons : MarkedConsecutive data marks (⟨edge, hSurvives⟩ : NonDanglingEdge data)
        ⟨partner, hPartnerSurvives⟩ :=
      ⟨fun hEq' ↦ hEq (congrArg Subtype.val hEq').symm, vertex, hIncident,
        hPartnerIncident, hValency, hMark⟩
    exact (markedRow_eq_of_markedConsecutive hCons).symm.trans hPath

/-! ### The walk vertices -/

/-- The source vertex reached after `j` occurrences of the ordered marked row
(`OrientedTraversal.walkVertex`, the public generic engine). -/
noncomputable def rowVertex (path : MarkedStablePath data marks) (j : ℕ) : data.SourceVertex :=
  walkVertex data (orderedRow hEnds path) (startVertex hEnds path) j

theorem rowVertex_zero (path : MarkedStablePath data marks) :
    rowVertex hEnds path 0 = startVertex hEnds path := rfl

theorem rowVertex_succ (path : MarkedStablePath data marks) {j : ℕ}
    (hj : j < (orderedRow hEnds path).length) :
    rowVertex hEnds path (j + 1) =
      otherEnd data (orderedRow hEnds path)[j] (rowVertex hEnds path j) :=
  walkVertex_succ _ _ hj

/-- The `j`-th occurrence is incident to the walk vertex after it. -/
theorem rowVertex_succ_incident (path : MarkedStablePath data marks) {j : ℕ}
    (hj : j < (orderedRow hEnds path).length) :
    Incident data (orderedRow hEnds path)[j] (rowVertex hEnds path (j + 1)) := by
  rw [rowVertex_succ hEnds path hj]
  exact incident_otherEnd data _ _

theorem rowVertex_ne_succ (path : MarkedStablePath data marks) {j : ℕ}
    (hj : j < (orderedRow hEnds path).length) :
    rowVertex hEnds path (j + 1) ≠ rowVertex hEnds path j := by
  rw [rowVertex_succ hEnds path hj]
  exact otherEnd_ne data _ _

/-- **The marked walk invariant**: the walk vertex at position `j` is an end of the `j`-th
occurrence at which every other surviving occurrence has already been passed, the closure clause
being asked only at a surviving valency-two **non-mark** vertex. This is
`OrientedTraversal.WalkInvariant` with the non-mark clause, which is what lets the start be a
mark of surviving valency two. -/
def MarkedWalkInvariant (path : MarkedStablePath data marks) (j : ℕ)
    (hj : j < (orderedRow hEnds path).length) : Prop :=
  Incident data (orderedRow hEnds path)[j] (rowVertex hEnds path j) ∧
    ∀ f, ¬ IsDangling data f → Incident data f (rowVertex hEnds path j) →
      f ≠ (orderedRow hEnds path)[j] →
        nonDanglingValency data (rowVertex hEnds path j) = 2 → rowVertex hEnds path j ∉ marks →
          Earlier (orderedRow hEnds path) j f

/-- **The meeting vertex is the far end**: under the invariant at `j`, a surviving valency-two
non-mark vertex shared by the `j`-th and `(j+1)`-st occurrences is the walk vertex `j + 1`
(`OrientedTraversal.meet_eq_walkVertex_succ`). -/
theorem meet_eq_rowVertex_succ (path : MarkedStablePath data marks) {j : ℕ}
    (hj : j + 1 < (orderedRow hEnds path).length)
    (hInv : MarkedWalkInvariant hEnds path j (Nat.lt_of_succ_lt hj))
    {meet : data.SourceVertex} (hFirst : Incident data (orderedRow hEnds path)[j] meet)
    (hSecond : Incident data (orderedRow hEnds path)[j + 1] meet)
    (hValency : nonDanglingValency data meet = 2) (hMark : meet ∉ marks) :
    meet = rowVertex hEnds path (j + 1) := by
  obtain ⟨hIncident, hClosed⟩ := hInv
  have hjlt : j < (orderedRow hEnds path).length := Nat.lt_of_succ_lt hj
  have hNeIndex : (orderedRow hEnds path)[j] ≠ (orderedRow hEnds path)[j + 1] := by
    intro hEq
    exact absurd ((orderedRow_nodup hEnds path).getElem_inj_iff.mp hEq) (by omega)
  rcases eq_or_eq_otherEnd data hIncident hFirst with hCase | hCase
  · exfalso
    rw [hCase] at hValency hSecond hMark
    obtain ⟨k, hk, hklt, hkEq⟩ := hClosed (orderedRow hEnds path)[j + 1]
      (orderedRow_survives hEnds path _ (List.getElem_mem hj)) hSecond (Ne.symm hNeIndex)
      hValency hMark
    have : k = j + 1 := (orderedRow_nodup hEnds path).getElem_inj_iff.mp hkEq
    omega
  · rw [rowVertex_succ hEnds path hjlt, hCase]

theorem markedWalk_invariant (path : MarkedStablePath data marks) :
    ∀ j, ∀ hj : j < (orderedRow hEnds path).length, MarkedWalkInvariant hEnds path j hj := by
  intro j
  induction j with
  | zero =>
    intro hj
    refine ⟨?_, fun _ _ _ _ hValency hMark ↦ ?_⟩
    · rw [orderedRow_getElem_zero hEnds path]
      exact (startEdge_isMarkedPathEnd hEnds path).1
    · rcases (startEdge_isMarkedPathEnd hEnds path).2 with hTwo | hIn
      · exact absurd hValency hTwo
      · exact absurd hIn hMark
  | succ j ih =>
    intro hj
    have hjlt : j < (orderedRow hEnds path).length := Nat.lt_of_succ_lt hj
    have hInv := ih hjlt
    obtain ⟨meet, hFirst, hSecond, hValency, hMark⟩ := (orderedRow_chain hEnds path).getElem j hj
    have hMeetEq := meet_eq_rowVertex_succ hEnds path hj hInv hFirst hSecond hValency hMark
    have hNeIndex : (orderedRow hEnds path)[j] ≠ (orderedRow hEnds path)[j + 1] := by
      intro hEq
      exact absurd ((orderedRow_nodup hEnds path).getElem_inj_iff.mp hEq) (by omega)
    refine ⟨hMeetEq ▸ hSecond, fun f hf hfIncident hfNe hfValency _ ↦ ?_⟩
    have hPrevIncident : Incident data (orderedRow hEnds path)[j] (rowVertex hEnds path (j + 1)) :=
      rowVertex_succ_incident hEnds path hjlt
    obtain ⟨other, -, hUnique⟩ :=
      exists_unique_other_of_nonDanglingValency_eq_two data hfValency
        (orderedRow_survives hEnds path _ (List.getElem_mem hj)) (hMeetEq ▸ hSecond)
    exact ⟨j, hjlt, by omega,
      (hUnique (orderedRow hEnds path)[j]
        ⟨hNeIndex, orderedRow_survives hEnds path _ (List.getElem_mem hjlt), hPrevIncident⟩).trans
        (hUnique f ⟨hfNe, hf, hfIncident⟩).symm⟩

theorem rowVertex_incident (path : MarkedStablePath data marks) {j : ℕ}
    (h : j < (orderedRow hEnds path).length) :
    Incident data (orderedRow hEnds path)[j] (rowVertex hEnds path j) :=
  (markedWalk_invariant hEnds path j h).1

/-- **Interior walk vertices have surviving valency two and are not marks.** -/
theorem rowVertex_interior (path : MarkedStablePath data marks) {j : ℕ}
    (h : j + 1 < (orderedRow hEnds path).length) :
    nonDanglingValency data (rowVertex hEnds path (j + 1)) = 2 ∧
      rowVertex hEnds path (j + 1) ∉ marks := by
  obtain ⟨meet, hFirst, hSecond, hValency, hMark⟩ := (orderedRow_chain hEnds path).getElem j h
  rw [← meet_eq_rowVertex_succ hEnds path h
    (markedWalk_invariant hEnds path j (Nat.lt_of_succ_lt h)) hFirst hSecond hValency hMark]
  exact ⟨hValency, hMark⟩

theorem rowVertex_valency (path : MarkedStablePath data marks) {j : ℕ}
    (h : j + 1 < (orderedRow hEnds path).length) :
    nonDanglingValency data (rowVertex hEnds path (j + 1)) = 2 :=
  (rowVertex_interior hEnds path h).1

theorem rowVertex_notMem (path : MarkedStablePath data marks) {j : ℕ}
    (h : j + 1 < (orderedRow hEnds path).length) : rowVertex hEnds path (j + 1) ∉ marks :=
  (rowVertex_interior hEnds path h).2

/-! ### The interior vertices, from the walk alone -/

/-- An occurrence meeting an interior vertex is one of its two adjacent occurrences
(`RowVertexEnumeration.incident_interior_iff`). -/
theorem incident_interior_iff (path : MarkedStablePath data marks) {i : ℕ}
    (hi : i + 1 < (orderedRow hEnds path).length) {edge : data.SourceEdge}
    (hEdge : ¬ IsDangling data edge) :
    Incident data edge (rowVertex hEnds path (i + 1)) ↔
      edge = (orderedRow hEnds path)[i] ∨ edge = (orderedRow hEnds path)[i + 1] := by
  have hi0 : i < (orderedRow hEnds path).length := by omega
  have hFirstInc := rowVertex_succ_incident hEnds path hi0
  have hSecondInc := rowVertex_incident hEnds path hi
  have hNe : (orderedRow hEnds path)[i] ≠ (orderedRow hEnds path)[i + 1] := by
    intro h
    have := (orderedRow_nodup hEnds path).getElem_inj_iff.mp h
    omega
  constructor
  · exact IndexPattern.eq_or_eq_of_nonDanglingValency_two (rowVertex_valency hEnds path hi)
      (orderedRow_survives hEnds path _ (List.getElem_mem hi0)) hFirstInc
      (orderedRow_survives hEnds path _ (List.getElem_mem hi)) hSecondInc hNe hEdge
  · rintro (rfl | rfl)
    · exact hFirstInc
    · exact hSecondInc

/-- Interior indices of one row are injective (`RowVertexEnumeration.interior_injective`). -/
theorem interior_injective' (path : MarkedStablePath data marks) {i j : ℕ}
    (hi : i + 1 < (orderedRow hEnds path).length) (hj : j + 1 < (orderedRow hEnds path).length)
    (hEq : rowVertex hEnds path (i + 1) = rowVertex hEnds path (j + 1)) : i = j := by
  have hj0 : j < (orderedRow hEnds path).length := by omega
  have hInc : Incident data (orderedRow hEnds path)[j] (rowVertex hEnds path (i + 1)) := by
    rw [hEq]
    exact rowVertex_succ_incident hEnds path hj0
  rcases (incident_interior_iff hEnds path hi
      (orderedRow_survives hEnds path _ (List.getElem_mem hj0))).mp hInc with h | h
  · exact ((orderedRow_nodup hEnds path).getElem_inj_iff.mp h).symm
  · have hji : j = i + 1 := (orderedRow_nodup hEnds path).getElem_inj_iff.mp h
    have hInc' : Incident data (orderedRow hEnds path)[j + 1] (rowVertex hEnds path (i + 1)) := by
      rw [hEq]
      exact rowVertex_incident hEnds path hj
    rcases (incident_interior_iff hEnds path hi
        (orderedRow_survives hEnds path _ (List.getElem_mem hj))).mp hInc' with h' | h' <;>
      have hIndex := (orderedRow_nodup hEnds path).getElem_inj_iff.mp h' <;> omega

/-- An interior vertex is not the finish vertex (`RowVertexEnumeration.interior_ne_finish`). -/
theorem interior_ne_finish (path : MarkedStablePath data marks) {i : ℕ}
    (hi : i + 1 < (orderedRow hEnds path).length) :
    rowVertex hEnds path (i + 1) ≠ rowVertex hEnds path (orderedRow hEnds path).length := by
  intro hEq
  let last := (orderedRow hEnds path).length - 1
  have hLast : last < (orderedRow hEnds path).length := by dsimp [last]; omega
  have hLen : last + 1 = (orderedRow hEnds path).length := by dsimp [last]; omega
  have hInc : Incident data (orderedRow hEnds path)[last] (rowVertex hEnds path (i + 1)) := by
    rw [hEq, ← hLen]
    exact rowVertex_succ_incident hEnds path hLast
  rcases (incident_interior_iff hEnds path hi
      (orderedRow_survives hEnds path _ (List.getElem_mem hLast))).mp hInc with h | h
  · have := (orderedRow_nodup hEnds path).getElem_inj_iff.mp h
    omega
  · have hIndex := (orderedRow_nodup hEnds path).getElem_inj_iff.mp h
    have hNot : rowVertex hEnds path (last + 1) ≠ rowVertex hEnds path last :=
      rowVertex_ne_succ hEnds path hLast
    rw [hLen, hIndex] at hNot
    exact hNot hEq.symm

/-- Two displayed occurrences incident at a valency-two non-mark vertex meet at the far end of
the earlier one (`RowVertexEnumeration.vertex_eq_next_of_incident`). -/
theorem vertex_eq_next_of_incident (path : MarkedStablePath data marks) {i j : ℕ}
    (hi : i < (orderedRow hEnds path).length) (hj : j < (orderedRow hEnds path).length)
    (hij : i < j) {vertex : data.SourceVertex} (hValency : nonDanglingValency data vertex = 2)
    (hMark : vertex ∉ marks) (hFirst : Incident data (orderedRow hEnds path)[i] vertex)
    (hSecond : Incident data (orderedRow hEnds path)[j] vertex) :
    vertex = rowVertex hEnds path (i + 1) := by
  have hInvariant := markedWalk_invariant hEnds path i hi
  rcases eq_or_eq_otherEnd data hInvariant.1 hFirst with hSame | hNext
  · have hSecond' : Incident data (orderedRow hEnds path)[j] (rowVertex hEnds path i) :=
      hSame ▸ hSecond
    have hValency' : nonDanglingValency data (rowVertex hEnds path i) = 2 := hSame ▸ hValency
    have hMark' : rowVertex hEnds path i ∉ marks := hSame ▸ hMark
    have hNe : (orderedRow hEnds path)[j] ≠ (orderedRow hEnds path)[i] := by
      intro h
      have := (orderedRow_nodup hEnds path).getElem_inj_iff.mp h
      omega
    obtain ⟨k, hk, hki, hEq⟩ := hInvariant.2 _
      (orderedRow_survives hEnds path _ (List.getElem_mem hj)) hSecond' hNe hValency' hMark'
    have := (orderedRow_nodup hEnds path).getElem_inj_iff.mp hEq
    omega
  · rw [rowVertex_succ hEnds path hi]
    exact hNext

/-- Every surviving valency-two non-mark vertex on a row is displayed at an interior index. -/
theorem exists_interior_index' (path : MarkedStablePath data marks) {vertex : data.SourceVertex}
    (hValency : nonDanglingValency data vertex = 2) (hMark : vertex ∉ marks)
    {edge : data.SourceEdge} (hEdge : OnRow marks path edge)
    (hIncident : Incident data edge vertex) :
    ∃ i : Fin ((orderedRow hEnds path).length - 1),
      rowVertex hEnds path (i.val + 1) = vertex := by
  obtain ⟨other, ⟨hNe, hSurvives, hOtherInc⟩, -⟩ :=
    exists_unique_other_of_nonDanglingValency_eq_two data hValency hEdge.survives hIncident
  have hOther := onRow_of_incident hValency hMark hEdge hIncident hSurvives hOtherInc
  obtain ⟨i, hi, hI⟩ := List.mem_iff_getElem.mp ((mem_orderedRow_iff hEnds path edge).mpr hEdge)
  obtain ⟨j, hj, hJ⟩ := List.mem_iff_getElem.mp ((mem_orderedRow_iff hEnds path other).mpr hOther)
  have hIJ : i ≠ j := by
    intro h
    subst h
    exact hNe (hJ.symm.trans hI)
  have hIInc : Incident data (orderedRow hEnds path)[i] vertex := hI ▸ hIncident
  have hJInc : Incident data (orderedRow hEnds path)[j] vertex := hJ ▸ hOtherInc
  rcases lt_or_gt_of_ne hIJ with hij | hji
  · exact ⟨⟨i, by omega⟩,
      (vertex_eq_next_of_incident hEnds path hi hj hij hValency hMark hIInc hJInc).symm⟩
  · exact ⟨⟨j, by omega⟩,
      (vertex_eq_next_of_incident hEnds path hj hi hji hValency hMark hJInc hIInc).symm⟩

/-- The last occurrence of the ordered marked row. -/
noncomputable def finishEdge (path : MarkedStablePath data marks) : data.SourceEdge :=
  (orderedRow hEnds path).getLast (List.ne_nil_of_length_pos (orderedRow_length_pos hEnds path))

theorem finishEdge_mem (path : MarkedStablePath data marks) :
    finishEdge hEnds path ∈ orderedRow hEnds path :=
  List.getLast_mem _

theorem finishEdge_eq_getElem (path : MarkedStablePath data marks) :
    finishEdge hEnds path =
      (orderedRow hEnds path)[(orderedRow hEnds path).length - 1]'(by
        have := orderedRow_length_pos hEnds path; omega) :=
  List.getLast_eq_getElem _

/-- The far end of the walk is a marked path end: the walk stopped there
(`RowSlotOrientation.finish_valency_ne_two`). -/
theorem finish_isMarkedPathEnd (path : MarkedStablePath data marks) :
    IsMarkedPathEnd data marks (finishEdge hEnds path)
      (rowVertex hEnds path (orderedRow hEnds path).length) := by
  have hPos := orderedRow_length_pos hEnds path
  have hLast : (orderedRow hEnds path).length - 1 < (orderedRow hEnds path).length := by omega
  have hLen : (orderedRow hEnds path).length - 1 + 1 = (orderedRow hEnds path).length := by omega
  have hIncident : Incident data (finishEdge hEnds path)
      (rowVertex hEnds path (orderedRow hEnds path).length) := by
    have hStep := rowVertex_succ_incident hEnds path hLast
    rw [hLen] at hStep
    rw [finishEdge_eq_getElem]
    exact hStep
  refine ⟨hIncident, ?_⟩
  by_contra hNot
  push Not at hNot
  obtain ⟨hValency, hMark⟩ := hNot
  have hOn := (mem_orderedRow_iff hEnds path _).mp (finishEdge_mem hEnds path)
  obtain ⟨i, hEq⟩ := exists_interior_index' hEnds path hValency hMark hOn hIncident
  exact interior_ne_finish hEnds path (by have := i.isLt; omega) hEq

end Ordered

/-! ## 3.  The ends of a marked row are marked branch vertices -/

section Ends

variable {marks : Finset data.SourceVertex} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate] {excess : ℤ} (fd : TypedFullDim data marks coordinate excess)

/-- A marked path end of a surviving occurrence is a marked branch vertex (valency `≥ 3`, or a
mark): valency zero is excluded by the incident survivor, valency one by connectedness
(`nonDanglingValency_ne_one`), and valency two by the end condition unless it is a mark. -/
theorem markedBranch_of_isMarkedPathEnd (hConn : data.Connected) {edge : data.SourceEdge}
    {vertex : data.SourceVertex} (hSurvives : ¬ IsDangling data edge)
    (hEnd : IsMarkedPathEnd data marks edge vertex) :
    3 ≤ nonDanglingValency data vertex ∨ vertex ∈ marks := by
  have hNotZero := ClassInjectivity.nonDanglingValency_ne_zero_of_incident data hSurvives hEnd.1
  have hNotOne := NonDanglingValency.nonDanglingValency_ne_one data hConn vertex
  rcases hEnd.2 with hTwo | hIn
  · exact Or.inl (by omega)
  · exact Or.inr hIn

/-- The start of a marked row, as a marked branch vertex. -/
noncomputable def startBranch (path : MarkedStablePath data marks) :
    MarkedBranchVertex data marks :=
  ⟨rowVertex fd.pathEnds path 0, markedBranch_of_isMarkedPathEnd fd.valid.1
    (startEdge fd.pathEnds path).2 (startEdge_isMarkedPathEnd fd.pathEnds path)⟩

/-- The finish of a marked row, as a marked branch vertex. -/
noncomputable def finishBranch (path : MarkedStablePath data marks) :
    MarkedBranchVertex data marks :=
  ⟨rowVertex fd.pathEnds path (orderedRow fd.pathEnds path).length,
    markedBranch_of_isMarkedPathEnd fd.valid.1
      (orderedRow_survives fd.pathEnds path _ (finishEdge_mem fd.pathEnds path))
      (finish_isMarkedPathEnd fd.pathEnds path)⟩

/-- **A marked branch vertex met by a row occurrence is one of the row's two ends**: no interior
walk vertex is a marked branch vertex (`rowVertex_interior`). -/
theorem branch_incident_eq_endpoint (path : MarkedStablePath data marks)
    (branch : MarkedBranchVertex data marks) {edge : data.SourceEdge}
    (hEdge : OnRow marks path edge) (hIncident : Incident data edge branch.1) :
    branch.1 = (startBranch fd path).1 ∨ branch.1 = (finishBranch fd path).1 := by
  obtain ⟨i, hi, hI⟩ :=
    List.mem_iff_getElem.mp ((mem_orderedRow_iff fd.pathEnds path edge).mpr hEdge)
  have hIncident' : Incident data (orderedRow fd.pathEnds path)[i] branch.1 := hI ▸ hIncident
  have hNotInterior : ∀ j, j + 1 < (orderedRow fd.pathEnds path).length →
      branch.1 ≠ rowVertex fd.pathEnds path (j + 1) := by
    intro j hj hEq
    obtain ⟨hValency, hMark⟩ := rowVertex_interior fd.pathEnds path hj
    rw [← hEq] at hValency hMark
    rcases branch.2 with hThree | hIn
    · omega
    · exact hMark hIn
  rcases eq_or_eq_otherEnd data (rowVertex_incident fd.pathEnds path hi) hIncident' with h | h
  · by_cases hi0 : i = 0
    · exact Or.inl (by subst hi0; exact h)
    · exfalso
      have hPred : i - 1 + 1 = i := by omega
      exact hNotInterior (i - 1) (by omega) (by rw [hPred]; exact h)
  · have hNext : branch.1 = rowVertex fd.pathEnds path (i + 1) :=
      h.trans (rowVertex_succ fd.pathEnds path hi).symm
    by_cases hLen : i + 1 = (orderedRow fd.pathEnds path).length
    · refine Or.inr ?_
      show branch.1 = rowVertex fd.pathEnds path (orderedRow fd.pathEnds path).length
      rw [← hLen]
      exact hNext
    · exact absurd hNext (hNotInterior i (by omega))

end Ends

/-! ## 4.  The interior vertices of the marked rows, enumerated -/

section Interior

variable {marks : Finset data.SourceVertex} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate] {excess : ℤ} (fd : TypedFullDim data marks coordinate excess)

/-- A literal occurrence of an interior vertex in a marked row. -/
def InteriorAddress :=
  Σ path : MarkedStablePath data marks, Fin ((orderedRow fd.pathEnds path).length - 1)

/-- The source vertex at an interior address. -/
noncomputable def addressVertex (address : InteriorAddress fd) : data.SourceVertex :=
  rowVertex fd.pathEnds address.1 (address.2.val + 1)

theorem addressVertex_valency (address : InteriorAddress fd) :
    nonDanglingValency data (addressVertex fd address) = 2 :=
  rowVertex_valency fd.pathEnds address.1 (by have := address.2.isLt; omega)

theorem addressVertex_notMem (address : InteriorAddress fd) : addressVertex fd address ∉ marks :=
  rowVertex_notMem fd.pathEnds address.1 (by have := address.2.isLt; omega)

/-- Every surviving valency-two non-mark vertex on a row is displayed at an interior index. -/
theorem exists_interior_index (path : MarkedStablePath data marks) {vertex : data.SourceVertex}
    (hValency : nonDanglingValency data vertex = 2) (hMark : vertex ∉ marks)
    {edge : data.SourceEdge} (hEdge : OnRow marks path edge)
    (hIncident : Incident data edge vertex) :
    ∃ i : Fin ((orderedRow fd.pathEnds path).length - 1),
      rowVertex fd.pathEnds path (i.val + 1) = vertex :=
  exists_interior_index' fd.pathEnds path hValency hMark hEdge hIncident

/-- Interior indices of one row are injective. -/
theorem interior_injective (path : MarkedStablePath data marks) {i j : ℕ}
    (hi : i + 1 < (orderedRow fd.pathEnds path).length)
    (hj : j + 1 < (orderedRow fd.pathEnds path).length)
    (hEq : rowVertex fd.pathEnds path (i + 1) = rowVertex fd.pathEnds path (j + 1)) : i = j :=
  interior_injective' fd.pathEnds path hi hj hEq

/-- Distinct marked rows have disjoint interiors
(`RowVertexEnumeration.row_eq_of_interior_eq`). -/
theorem row_eq_of_interior_eq (first second : MarkedStablePath data marks) {i j : ℕ}
    (hi : i + 1 < (orderedRow fd.pathEnds first).length)
    (hj : j + 1 < (orderedRow fd.pathEnds second).length)
    (hEq : rowVertex fd.pathEnds first (i + 1) = rowVertex fd.pathEnds second (j + 1)) :
    first = second := by
  have hFirst := (mem_orderedRow_iff fd.pathEnds first _).mp (List.getElem_mem hi)
  have hSecond := (mem_orderedRow_iff fd.pathEnds second _).mp (List.getElem_mem hj)
  have hIncident : Incident data (orderedRow fd.pathEnds second)[j + 1]
      (rowVertex fd.pathEnds first (i + 1)) := by
    rw [hEq]
    exact rowVertex_incident fd.pathEnds second hj
  obtain ⟨hValency, hMark⟩ := rowVertex_interior fd.pathEnds first hi
  have hBoth := onRow_of_incident hValency hMark hFirst
    (rowVertex_incident fd.pathEnds first hi) hSecond.survives hIncident
  obtain ⟨hSurvivesA, hA⟩ := hBoth
  obtain ⟨hSurvivesB, hB⟩ := hSecond
  exact hA.symm.trans hB

theorem addressVertex_injective : Function.Injective (addressVertex fd) := by
  rintro ⟨first, i⟩ ⟨second, j⟩ hEq
  change rowVertex fd.pathEnds first (i.val + 1) = rowVertex fd.pathEnds second (j.val + 1) at hEq
  have hPath := row_eq_of_interior_eq fd first second
    (by have := i.isLt; omega) (by have := j.isLt; omega) hEq
  subst hPath
  have hIndex : i = j := Fin.ext (interior_injective fd first (by have := i.isLt; omega)
    (by have := j.isLt; omega) hEq)
  subst hIndex
  rfl

theorem exists_address (vertex : data.SourceVertex)
    (hValency : nonDanglingValency data vertex = 2) (hMark : vertex ∉ marks) :
    ∃ address : InteriorAddress fd, addressVertex fd address = vertex := by
  obtain ⟨first, _, _, hSurvives, hIncident, _, _⟩ :=
    RowWalk.exists_pair_of_nonDanglingValency_two hValency
  obtain ⟨i, hI⟩ := exists_interior_index fd (markedRow marks ⟨first, hSurvives⟩) hValency hMark
    (show OnRow marks (markedRow marks ⟨first, hSurvives⟩) first from ⟨hSurvives, rfl⟩) hIncident
  exact ⟨⟨_, i⟩, hI⟩

/-- **The surviving valency-two non-mark vertices are exactly the interior addresses.** -/
noncomputable def addressEquiv :
    InteriorAddress fd ≃
      {vertex : data.SourceVertex // nonDanglingValency data vertex = 2 ∧ vertex ∉ marks} :=
  Equiv.ofBijective
    (fun address ↦ ⟨addressVertex fd address,
      addressVertex_valency fd address, addressVertex_notMem fd address⟩)
    ⟨fun _ _ h ↦ addressVertex_injective fd (congrArg Subtype.val h), by
      rintro ⟨vertex, hValency, hMark⟩
      obtain ⟨address, hAddress⟩ := exists_address fd vertex hValency hMark
      exact ⟨address, Subtype.ext hAddress⟩⟩

/-- Pendant retraction classes of distinct interior vertices of one row are distinct
(`RowVertexEnumeration.interior_retract_injective`): a retraction class holds at most one
surviving vertex (`PendantRetraction.surviving_vertex_unique`). -/
theorem interior_retract_injective (path : MarkedStablePath data marks) :
    Function.Injective (fun i : Fin ((orderedRow fd.pathEnds path).length - 1) ↦
      retractVertex (rowVertex fd.pathEnds path (i.val + 1))) := by
  intro i j hEq
  apply Fin.ext
  apply interior_injective fd path (by have := i.isLt; omega) (by have := j.isLt; omega)
  apply surviving_vertex_unique (second := rowVertex fd.pathEnds path (j.val + 1)) ?_ ?_ hEq
  · rw [rowVertex_valency fd.pathEnds path (by have := i.isLt; omega)]; omega
  · rw [rowVertex_valency fd.pathEnds path (by have := j.isLt; omega)]; omega

end Interior

/-! ## 5.  Positions along a marked row -/

section Position

variable {marks : Finset data.SourceVertex} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate] {excess : ℤ} (fd : TypedFullDim data marks coordinate excess)

/-- The rational position of the `j`-th walk vertex: the sum of the source lengths along the
prefix, each occurrence of index `m` over a target edge of length `z` having length `z / m`. -/
noncomputable def prefixPosition (z : coordinate → ℚ) (path : MarkedStablePath data marks)
    (j : ℕ) : ℚ :=
  (((orderedRow fd.pathEnds path).take j).map fun edge ↦
    z (fd.labelling.targetEdge.symm edge.1.1) / (data.sourceEdgeIndex edge : ℚ)).sum

/-- **The full prefix is the matrix row**: traversal order does not change the marked
edge-length row (`RowPosition.prefixPosition_full`). -/
theorem prefixPosition_full (z : coordinate → ℚ) (path : MarkedStablePath data marks) :
    prefixPosition fd z path (orderedRow fd.pathEnds path).length =
      (LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec z
        (fd.labelling.row path) := by
  have hPerm : (orderedRow fd.pathEnds path).Perm
      (fd.labelling.path (fd.labelling.row path)) := by
    have hNodup : (fd.labelling.path (fd.labelling.row path)).Nodup :=
      List.Nodup.filter _ Finset.univ.nodup_toList
    apply List.perm_ext_iff_of_nodup (orderedRow_nodup fd.pathEnds path) hNodup |>.mpr
    intro edge
    rw [mem_orderedRow_iff, fd.labelling.mem_path_iff]
    constructor
    · rintro ⟨hSurvives, hPath⟩
      exact ⟨hSurvives, congrArg fd.labelling.row hPath⟩
    · rintro ⟨hSurvives, hPath⟩
      exact ⟨hSurvives, fd.labelling.row.injective hPath⟩
  unfold prefixPosition
  rw [List.take_length, LengthMatrixPresentation.matrix_mulVec]
  exact (hPerm.map (fun edge ↦
    z (fd.labelling.targetEdge.symm edge.1.1) / (data.sourceEdgeIndex edge : ℚ))).sum_eq

/-- The integral position obtained by traversing a nonnegative integral realization. -/
noncomputable def integralPrefix (realization : data.NonnegativeIntegralRealization)
    (path : MarkedStablePath data marks) (j : ℕ) : ℕ :=
  ((orderedRow fd.pathEnds path).take j |>.map realization.sourceLength).sum

theorem integralPrefix_le_full (realization : data.NonnegativeIntegralRealization)
    (path : MarkedStablePath data marks) (j : ℕ) :
    integralPrefix fd realization path j ≤
      integralPrefix fd realization path (orderedRow fd.pathEnds path).length := by
  have hSplit : integralPrefix fd realization path j +
      ((orderedRow fd.pathEnds path).drop j |>.map realization.sourceLength).sum =
      integralPrefix fd realization path (orderedRow fd.pathEnds path).length := by
    simp only [integralPrefix, List.take_length]
    rw [← List.sum_append, ← List.map_append, List.take_append_drop]
  omega

theorem integralPrefix_succ (realization : data.NonnegativeIntegralRealization)
    (path : MarkedStablePath data marks) {j : ℕ} (hj : j < (orderedRow fd.pathEnds path).length) :
    integralPrefix fd realization path (j + 1) =
      integralPrefix fd realization path j +
        realization.sourceLength (orderedRow fd.pathEnds path)[j] := by
  simp only [integralPrefix, List.take_succ_eq_append_getElem hj, List.map_append,
    List.map_singleton, List.sum_append, List.sum_singleton]

/-- Denominator clearing commutes with prefixes (`RowRealizedPosition.integralPrefix_cast`). -/
theorem integralPrefix_cast (z : coordinate → ℚ) (hNonnegative : ∀ c, 0 ≤ z c)
    (path : MarkedStablePath data marks) (j : ℕ) :
    (integralPrefix fd
      (NonnegativeIntegralRealization.ofNonnegativeRational data
        (fun edge ↦ z (fd.labelling.targetEdge.symm edge)) (fun _ ↦ hNonnegative _)) path j : ℚ) =
      (data.rationalRealizationScale (fun edge ↦ z (fd.labelling.targetEdge.symm edge)) : ℚ) *
        prefixPosition fd z path j := by
  simp only [integralPrefix, Nat.cast_list_sum, List.map_map, Function.comp_def,
    NonnegativeIntegralRealization.ofNonnegativeRational_sourceLength_cast,
    sourceEdgeLength, prefixPosition, ← List.sum_map_mul_left]

/-- Literal row-interior chip mass at one integral position, aggregating every interior vertex
realized there (`RowRealizedPosition.collisionCoefficient`). -/
noncomputable def collisionCoefficient (realization : data.NonnegativeIntegralRealization)
    (root : target.V) (path : MarkedStablePath data marks) (offset : ℕ) : ℤ := by
  classical
  exact ∑ i : Fin ((orderedRow fd.pathEnds path).length - 1),
    if integralPrefix fd realization path (i.val + 1) = offset then
      retractedFibre root (retractVertex (rowVertex fd.pathEnds path (i.val + 1))) else 0

open scoped Classical in
/-- The collision coefficient is a literal pushforward of the pullback fibre, each source vertex
counted once (`RowVertexEnumeration.collisionCoefficient_eq_raw_fibre_sum`). -/
theorem collisionCoefficient_eq_raw_fibre_sum (realization : data.NonnegativeIntegralRealization)
    (root : target.V) (path : MarkedStablePath data marks) (offset : ℕ) :
    collisionCoefficient fd realization root path offset =
      ∑ vertex : data.SourceVertex,
        if vertex.1.1 = root ∧
          ∃ i : Fin ((orderedRow fd.pathEnds path).length - 1),
            retractVertex vertex = retractVertex (rowVertex fd.pathEnds path (i.val + 1)) ∧
              integralPrefix fd realization path (i.val + 1) = offset then
          ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) else 0 := by
  let index := Fin ((orderedRow fd.pathEnds path).length - 1)
  have hExpand : collisionCoefficient fd realization root path offset =
      ∑ i : index, ∑ vertex : data.SourceVertex,
        if integralPrefix fd realization path (i.val + 1) = offset ∧
          retractVertex vertex = retractVertex (rowVertex fd.pathEnds path (i.val + 1)) ∧
          vertex.1.1 = root then
          ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) else 0 := by
    unfold collisionCoefficient
    apply Finset.sum_congr rfl
    intro i _
    by_cases hOffset : integralPrefix fd realization path (i.val + 1) = offset
    · simp only [hOffset, ite_true, retractedFibre, true_and]
    · simp only [hOffset, ite_false, false_and, Finset.sum_const_zero]
  rw [hExpand, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro vertex _
  by_cases hRoot : vertex.1.1 = root
  · by_cases hExists : ∃ i : index,
        retractVertex vertex = retractVertex (rowVertex fd.pathEnds path (i.val + 1)) ∧
          integralPrefix fd realization path (i.val + 1) = offset
    · obtain ⟨i, hClass, hOffset⟩ := hExists
      rw [ite_eq_left ⟨hRoot, i, hClass, hOffset⟩]
      rw [Finset.sum_eq_single i]
      · simp only [hOffset, hClass, hRoot, and_self, ite_true]
      · intro j _ hNe
        have hClassNe : retractVertex vertex ≠
            retractVertex (rowVertex fd.pathEnds path (j.val + 1)) := by
          intro h
          exact hNe ((interior_retract_injective fd path) (h.symm.trans hClass))
        simp only [hClassNe, false_and, and_false, ite_false]
      · simp
    · rw [ite_eq_right (by simpa only [hRoot, true_and] using hExists)]
      apply Finset.sum_eq_zero
      intro i _
      split_ifs with h
      · exact False.elim (hExists ⟨i, h.2.1, h.1⟩)
      · rfl
  · simp only [hRoot, and_false, false_and, ite_false, Finset.sum_const_zero]

end Position

end DiagonalSecant.TypedRows
