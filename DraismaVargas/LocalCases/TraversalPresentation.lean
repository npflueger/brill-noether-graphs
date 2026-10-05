module

public import DraismaVargas.LocalCases.FullDimensionalSource
public import DraismaVargas.LocalCases.TerminalForestReceipt
public import DraismaVargas.LocalCases.InputRefinementData

@[expose] public section

/-!
# The honest traversal presentation

`GluingDatum.LengthMatrixPresentation` (`Infrastructure/LengthMatrix.lean`) has
two fields, `targetEdge : coordinate ≃ target.edges` and
`path : coordinate → List SourceEdge`, and constrains them not at all.  This
module states the row conditions a terminal-face argument needs as a separate
bundled structure, `StrongPresentation`, proves that the honest traversal
already satisfies every one of them, and isolates what is left.

`StrongPresentation` *contains* a `LengthMatrixPresentation` rather than adding
fields to it, so the construction sites and consumers of
`LengthMatrixPresentation` are untouched, and a consumer asks for the strong
form only when it needs strength.

## The row conditions, reconciled

**`PresentationDecomposition.Decomposes` and
`W4StableSource.StableLengthMatrixLabelling.orderedPath_chain` agree, exactly.**

* A **row** is, in both, the set of surviving source occurrences of one
  stable-path class.  `Decomposes` describes it as a set — duplicate-free,
  pairwise disjoint, covering the non-dangling occurrences, missing the dangling
  ones — and is deliberately silent about order.  `orderedPath_chain` describes
  the *same* set with its traversal order: `orderedPath_perm_path` says the
  ordered row is a permutation of the `Decomposes` row, and `orderedDecomposes`
  (§3 below, and `FullDimensionalSourcePresentation.orderedDecomposes`) says the
  ordered rows still decompose.  There is no disagreement to settle: the two are
  the same row seen as a set and as a list, and `MeetsAt` (§2) is the one chain
  predicate both use.
* Rows may also be indexed by the stable slots of a requested specification,
  through `InputInterface.slot : Fin p ≃ coordinate`.  `slot` is an
  equivalence, so "for every stable slot" and "for every matrix row" are the
  same quantifier (`forall_slot_iff`, §4).
* **Endpoints.**  Asking only that the first and last occurrences of a row be
  *incident* to two named vertices does not pin the row's ends.  An occurrence
  has two ends, and for a row of two or more occurrences such an incidence
  condition is also satisfied by the **interior** vertex at which the first two
  occurrences meet (`head_incident_interior`) — so the row need not be a
  maximal stable path, which is what an `OrderedPathSplit` of a slot
  (`Utilities.Certificate.IteratedSplitRefinement.OrderedPathSplit`) needs.  `Trivalence.lean` records the same weakness on the other side:
  "`Decomposes` alone allows two rows to meet at a valency-two vertex".

Accordingly `StrongPresentation` states the endpoint condition with
`W4StableSource.IsPathEnd` — incidence *at a vertex of surviving valency
different from two* — which is strictly stronger than bare incidence
(`StrongPresentation.head_incident` and `getLast_incident` recover the
incidence).  §3 shows the strengthened form costs nothing, because the honest
traversal satisfies it.

## What is proved

* §1 `exists_isPathEnd_getLast` — **the far end of a traversal is a path end.**
  `W4StableSource.traverse` stops either at a genuine path end or because the
  occurrence continuing ahead has already been emitted, and nothing there rules
  the second case out; `orderedPath_head?` consequently names only the end a row
  *starts* from.  `TraverseInvariant` rules it out, using looplessness of the
  quotient source (§0, via `GluingDatum.sourceEnds_ne`).  This is what makes a
  statement about the second end of a row available at all.
* §2 `StrongPresentation`, §3 `ofLabelling` and `ofFullDimensional` — the
  bundled structure, and the proof that
  `W4StableSource.StableLengthMatrixLabelling.orderedPresentation` under
  `HasPathEnds` *is* one, with the length matrix unchanged
  (`matrix_ofLabelling`), hence still nonsingular.
* §5 `CoreDictionary` — the one input that is not a source-side statement: the
  vertices of `spec.core` placed on the quotient source, matched with the row
  ends a strong presentation names.
* §6 `isForest_of_cyclesAreRows` — the forest receipt is the arithmetic half
  (proved here from `InputInterface.matrixMap` and `Spec.length_pos` alone, with
  no march state) together with one incidence condition, `CyclesAreRows`.
* §8 — joint satisfiability, including the one pair of fields that could have
  conflicted.

## What is left, precisely

Two inputs, and neither is a row condition.

* `CyclesAreRows` (§6): *a slot set carrying a cycle contains a complete
  displayed row.*  Every field of `StrongPresentation` constrains one row at a
  time; none of them says the rows exhaust the cycles of the quotient source, so
  this does not follow from them.  With it, the forest receipt is proved.
* `CoreDictionary` (§5): the statement "`spec.core` is the stable model of the
  quotient source".  It is not a consequence of the interface: `spec.core` does
  not appear in `InputInterface`, and the slot lengths alone do not determine
  the graph.

One further condition is deliberately **not** imposed: compatibility of the
target occurrences under a row with the coordinate labelling the row.  It would
be needed by a construction that matched a row against the split chain column
by column.
-/
namespace DraismaVargas.LocalCases.TraversalPresentation

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.PresentationDecomposition
open DraismaVargas.LocalCases.W4StableSource

variable {target : CFGraph} {degree : ℕ}

/-! ## 0.  The quotient source has no loops -/

/-- **Looplessness, in the form the traversal consumes.**  The far end of an
occurrence is never the end it was entered by. -/
theorem otherEnd_ne (data : GluingDatum target degree)
    (edge : data.SourceEdge) (vertex : data.SourceVertex) :
    otherEnd data edge vertex ≠ vertex := by
  unfold otherEnd
  split_ifs with hSplit
  · intro hEq
    exact data.sourceEnds_ne edge (hSplit.trans hEq.symm)
  · exact hSplit

/-! ## 1.  The far end of a traversal

`W4StableSource.traverse` stops for one of two reasons: the far end of the
current occurrence is not a surviving valency-two vertex — a genuine path end —
or the occurrence continuing there has already been emitted.  Nothing in
`W4StableSource` rules the second reason out, and it is exactly what stands
between `orderedPath_head?` and a statement about the *other* end of a row.

`TraverseInvariant` rules it out.  Its two substantive clauses say that the
already-emitted occurrences have exhausted every surviving valency-two vertex
they touch, apart from the vertex the walk is currently standing at, and that
the current entry vertex is exhausted too as soon as it is divalent.  Both hold
vacuously at the start of a traversal, both are preserved by one step, and
together with looplessness (`otherEnd_ne`) they force the continuing occurrence
to be new. -/

section Traversal

variable (data : GluingDatum target degree)

/-- The invariant a traversal started at a path end carries. -/
def TraverseInvariant (visited : Finset data.SourceEdge)
    (edge : data.SourceEdge) (vertex : data.SourceVertex) : Prop :=
  edge ∉ visited ∧ ¬ IsDangling data edge ∧ Incident data edge vertex ∧
    (nonDanglingValency data vertex = 2 → ∀ other : data.SourceEdge,
      ¬ IsDangling data other → Incident data other vertex → other ≠ edge →
        other ∈ visited) ∧
    (∀ emitted ∈ visited, ∀ met : data.SourceVertex,
      Incident data emitted met → met ≠ vertex →
        nonDanglingValency data met = 2 → ∀ other : data.SourceEdge,
          ¬ IsDangling data other → Incident data other met → other ∈ visited)

variable {data}

/-- A traversal of a surviving occurrence entered at a vertex of surviving
valency different from two starts with the invariant. -/
theorem traverseInvariant_empty {edge : data.SourceEdge}
    {vertex : data.SourceVertex} (hSurvives : ¬ IsDangling data edge)
    (hEnd : IsPathEnd data edge vertex) :
    TraverseInvariant data ∅ edge vertex :=
  ⟨Finset.notMem_empty _, hSurvives, hEnd.1, fun hValency ↦ absurd hValency hEnd.2,
    fun _ hEmitted ↦ absurd hEmitted (Finset.notMem_empty _)⟩

/-- **The walk never turns back.**  Under the invariant the occurrence
continuing at the far end has not been emitted, so the traversal does not stop
early. -/
theorem stepEdge_notMem_insert {visited : Finset data.SourceEdge}
    {edge : data.SourceEdge} {vertex : data.SourceVertex}
    (hInv : TraverseInvariant data visited edge vertex)
    (hValency : nonDanglingValency data (otherEnd data edge vertex) = 2) :
    stepEdge data hValency edge ∉ insert edge visited := by
  obtain ⟨hFresh, hSurvives, hIncident, -, hClosed⟩ := hInv
  intro hMem
  rcases Finset.mem_insert.mp hMem with hEq | hVisited
  · exact stepEdge_ne data hValency edge hEq
  · exact hFresh (hClosed _ hVisited (otherEnd data edge vertex)
      (stepEdge_incident data hValency edge) (otherEnd_ne data edge vertex)
      hValency edge hSurvives (incident_otherEnd data edge vertex))

/-- One step preserves the invariant. -/
theorem traverseInvariant_step {visited : Finset data.SourceEdge}
    {edge : data.SourceEdge} {vertex : data.SourceVertex}
    (hInv : TraverseInvariant data visited edge vertex)
    (hValency : nonDanglingValency data (otherEnd data edge vertex) = 2) :
    TraverseInvariant data (insert edge visited) (stepEdge data hValency edge)
      (otherEnd data edge vertex) := by
  have hStep := stepEdge_notMem_insert hInv hValency
  obtain ⟨-, hSurvives, hIncident, hHere, hClosed⟩ := hInv
  refine ⟨hStep,
    stepEdge_not_dangling data hValency edge,
    stepEdge_incident data hValency edge, ?_, ?_⟩
  · intro _ other hOther hOtherIncident hNe
    rcases eq_or_eq_stepEdge data hValency hSurvives
      (incident_otherEnd data edge vertex) hOther hOtherIncident with hCase | hCase
    · exact Finset.mem_insert.mpr (Or.inl hCase)
    · exact absurd hCase hNe
  · intro emitted hEmitted met hMet hNe hMetValency other hOther hOtherIncident
    rcases Finset.mem_insert.mp hEmitted with hEq | hVisited
    · subst hEq
      rcases eq_or_eq_otherEnd data hIncident hMet with hCase | hCase
      · subst hCase
        by_cases hSame : other = emitted
        · exact Finset.mem_insert.mpr (Or.inl hSame)
        · exact Finset.mem_insert.mpr
            (Or.inr (hHere hMetValency other hOther hOtherIncident hSame))
      · exact absurd hCase hNe
    · by_cases hSame : met = vertex
      · subst hSame
        by_cases hEdgeEq : other = edge
        · exact Finset.mem_insert.mpr (Or.inl hEdgeEq)
        · exact Finset.mem_insert.mpr
            (Or.inr (hHere hMetValency other hOther hOtherIncident hEdgeEq))
      · exact Finset.mem_insert.mpr (Or.inr (hClosed emitted hVisited met hMet
          hSame hMetValency other hOther hOtherIncident))

/-- **The far end of a traversal is a path end.**  Under the invariant the
walk stops only because the far end of its last occurrence is not a surviving
valency-two vertex. -/
theorem exists_isPathEnd_getLast {visited : Finset data.SourceEdge}
    {edge : data.SourceEdge} {vertex : data.SourceVertex}
    (hInv : TraverseInvariant data visited edge vertex) :
    ∃ finish : data.SourceVertex, ∀ last ∈ (traverse data visited edge vertex).getLast?,
      IsPathEnd data last finish := by
  revert hInv
  refine traverse_rec (motive := fun visited edge vertex ↦
    TraverseInvariant data visited edge vertex →
      ∃ finish : data.SourceVertex,
        ∀ last ∈ (traverse data visited edge vertex).getLast?,
          IsPathEnd data last finish) ?_ ?_ ?_ visited edge vertex
  · intro visited edge _ hVisited hInv
    exact absurd hVisited hInv.1
  · intro visited edge vertex hVisited hValency _
    refine ⟨otherEnd data edge vertex, ?_⟩
    rw [traverse_of_valency_ne data hVisited hValency]
    intro last hLast
    rw [List.getLast?_singleton, Option.mem_def, Option.some_inj] at hLast
    exact hLast ▸ ⟨incident_otherEnd data edge vertex, hValency⟩
  · intro visited edge vertex hVisited hValency ih hInv
    obtain ⟨finish, hFinish⟩ := ih (traverseInvariant_step hInv hValency)
    refine ⟨finish, ?_⟩
    rw [traverse_of_valency_eq data hVisited hValency]
    have hTail := traverse_head?_eq_some data (insert edge visited)
      (stepEdge data hValency edge) (otherEnd data edge vertex)
      (stepEdge_notMem_insert hInv hValency)
    obtain ⟨head, tail, hCons⟩ :
        ∃ head tail, traverse data (insert edge visited)
          (stepEdge data hValency edge) (otherEnd data edge vertex) = head :: tail := by
      cases hEq : traverse data (insert edge visited)
        (stepEdge data hValency edge) (otherEnd data edge vertex) with
      | nil => rw [hEq] at hTail; exact absurd hTail (by simp)
      | cons head tail => exact ⟨head, tail, rfl⟩
    rw [hCons, List.getLast?_cons_cons, ← hCons]
    exact hFinish

end Traversal

/-! ## 2.  The bundled strong presentation

The reconciled row conditions, in one object.  `toPresentation` is an ordinary
`GluingDatum.LengthMatrixPresentation`, so every consumer of the plain form
keeps working; the remaining fields are the row conditions reconciled in the
module docstring, with the endpoint statement strengthened from bare incidence
to
`W4StableSource.IsPathEnd`, i.e. incidence *at a vertex the stable path does
not continue through*.  That strengthening is what makes the row a **maximal**
stable path and not merely a walk with two named ends, and §3 shows it is free
for the honest traversal. -/

section Strong

variable {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- Consecutive occurrences of a row meet at a surviving valency-two source
vertex.  Written once, so that `PresentationDecomposition` and
`W4StableSource.StableLengthMatrixLabelling.orderedPath_chain` can be compared as
the same predicate. -/
def MeetsAt (data : GluingDatum target degree)
    (first second : data.SourceEdge) : Prop :=
  ∃ vertex : data.SourceVertex, Incident data first vertex ∧
    Incident data second vertex ∧ nonDanglingValency data vertex = 2

/-- **The strong form of a length-matrix presentation.**

A `GluingDatum.LengthMatrixPresentation` whose rows are the maximal stable
paths of the pruned source, listed in traversal order:

* `decomposes` — the rows partition the surviving occurrences
  (`PresentationDecomposition.Decomposes`);
* `chain` — consecutive entries of a row meet at a surviving valency-two
  vertex (`W4StableSource.StableLengthMatrixLabelling.orderedPath_chain`);
* `start`, `finish`, `head_isPathEnd`, `getLast_isPathEnd` — each row carries
  two named source vertices, and its first and last occurrences sit at them
  through ends the stable path does not continue through;
* `path_ne_nil` — no row is empty.

Nothing here mentions a face, a specification or a coordinate vector: this is
purely a statement about `data`, which is what makes it available at the same
time to the `InputRefinement` receipt and to the forest receipt. -/
structure StrongPresentation (data : GluingDatum target degree)
    (coordinate : Type*) [Fintype coordinate] [DecidableEq coordinate] where
  /-- The underlying length-matrix presentation. -/
  toPresentation : data.LengthMatrixPresentation coordinate
  /-- The rows partition the surviving source occurrences. -/
  decomposes : Decomposes toPresentation
  /-- Consecutive occurrences of a row meet at a surviving valency-two vertex. -/
  chain : ∀ row : coordinate, (toPresentation.path row).IsChain (MeetsAt data)
  /-- The source vertex a row starts at. -/
  start : coordinate → data.SourceVertex
  /-- The source vertex a row ends at. -/
  finish : coordinate → data.SourceVertex
  /-- The first occurrence of a row sits at its start vertex, through an end
  the stable path does not continue through. -/
  head_isPathEnd : ∀ row : coordinate, ∀ edge ∈ (toPresentation.path row).head?,
    IsPathEnd data edge (start row)
  /-- The last occurrence of a row sits at its finish vertex, through an end
  the stable path does not continue through. -/
  getLast_isPathEnd : ∀ row : coordinate, ∀ edge ∈ (toPresentation.path row).getLast?,
    IsPathEnd data edge (finish row)
  /-- No row is empty. -/
  path_ne_nil : ∀ row : coordinate, toPresentation.path row ≠ []

namespace StrongPresentation

variable (strong : StrongPresentation data coordinate)

/-- The first occurrence of a row is incident to the row's start vertex: the
bare incidence form of the endpoint condition. -/
theorem head_incident (row : coordinate) :
    ∀ edge ∈ (strong.toPresentation.path row).head?,
      Incident data edge (strong.start row) :=
  fun edge hEdge ↦ (strong.head_isPathEnd row edge hEdge).1

/-- The last occurrence of a row is incident to the row's finish vertex: the
bare incidence form of the endpoint condition. -/
theorem getLast_incident (row : coordinate) :
    ∀ edge ∈ (strong.toPresentation.path row).getLast?,
      Incident data edge (strong.finish row) :=
  fun edge hEdge ↦ (strong.getLast_isPathEnd row edge hEdge).1

/-- Rows are nonempty, so both ends are actually constrained. -/
theorem exists_head (row : coordinate) :
    ∃ edge, (strong.toPresentation.path row).head? = some edge := by
  obtain ⟨first, rest, hCons⟩ := List.exists_cons_of_ne_nil (strong.path_ne_nil row)
  exact ⟨first, by rw [hCons]; rfl⟩

/-- **The two ends are genuine ends.**  A row's start vertex has surviving
valency different from two — it is a junction of the stable graph, not an
interior point of a stable path. -/
theorem start_not_divalent (row : coordinate) :
    nonDanglingValency data (strong.start row) ≠ 2 := by
  obtain ⟨edge, hEdge⟩ := strong.exists_head row
  exact (strong.head_isPathEnd row edge (by rw [hEdge]; rfl)).2

/-- The same for a row's finish vertex. -/
theorem finish_not_divalent (row : coordinate) :
    nonDanglingValency data (strong.finish row) ≠ 2 := by
  obtain ⟨edge, hEdge⟩ :
      ∃ edge, (strong.toPresentation.path row).getLast? = some edge := by
    exact ⟨_, List.getLast?_eq_getLast_of_ne_nil (strong.path_ne_nil row)⟩
  exact (strong.getLast_isPathEnd row edge (by rw [hEdge]; rfl)).2

end StrongPresentation

end Strong

/-! ## 3.  The honest traversal is a strong presentation

`W4StableSource.StableLengthMatrixLabelling.orderedPresentation` is already
built from a genuine traversal of each stable-path class, started at an end
supplied by `HasPathEnds`.  Everything the strong form asks for is therefore
available: `orderedDecomposes`-style bookkeeping from `mem_orderedPath_iff`,
`orderedPath_chain` for the walk condition, `orderedPath_head?` together with
`startEdge_isPathEnd` for the first end, and §1 for the second. -/

section Producer

variable {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- The traversal of the class labelled `row` reaches a path end. -/
theorem exists_isPathEnd_getLast_orderedPath (hEnds : HasPathEnds data)
    (labelling : StableLengthMatrixLabelling data coordinate) (row : coordinate) :
    ∃ finish : data.SourceVertex,
      ∀ last ∈ (labelling.orderedPath hEnds row).getLast?,
        IsPathEnd data last finish :=
  exists_isPathEnd_getLast
    (traverseInvariant_empty (labelling.startEdge hEnds row).2
      (labelling.startEdge_isPathEnd hEnds row))

/-- The vertex at which the traversal of `row` ends. -/
noncomputable def finishVertex (hEnds : HasPathEnds data)
    (labelling : StableLengthMatrixLabelling data coordinate)
    (row : coordinate) : data.SourceVertex :=
  (exists_isPathEnd_getLast_orderedPath hEnds labelling row).choose

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem getLast_isPathEnd_finishVertex (hEnds : HasPathEnds data)
    (labelling : StableLengthMatrixLabelling data coordinate) (row : coordinate) :
    ∀ last ∈ (labelling.orderedPath hEnds row).getLast?,
      IsPathEnd data last (finishVertex hEnds labelling row) :=
  (exists_isPathEnd_getLast_orderedPath hEnds labelling row).choose_spec

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- A traversal-ordered row is never empty: it starts at the chosen path end. -/
theorem orderedPath_ne_nil (hEnds : HasPathEnds data)
    (labelling : StableLengthMatrixLabelling data coordinate) (row : coordinate) :
    labelling.orderedPath hEnds row ≠ [] := by
  intro hNil
  have hHead := labelling.orderedPath_head? hEnds row
  rw [hNil] at hHead
  simp at hHead

/-- The traversal-ordered rows partition the surviving occurrences.  Identical
to `FullDimensionalSource.FullDimensionalSourcePresentation.orderedDecomposes`,
restated for a bare labelling so that the strong form does not need the whole
full-dimensional package. -/
theorem orderedDecomposes (hEnds : HasPathEnds data)
    (labelling : StableLengthMatrixLabelling data coordinate) :
    Decomposes (labelling.orderedPresentation hEnds) := by
  refine ⟨fun row ↦ labelling.orderedPath_nodup hEnds row,
    fun row row' hNe edge hMem hMem' ↦ ?_, fun edge hSurvives ↦ ?_,
    fun edge hDangling row hMem ↦ ?_⟩
  · obtain ⟨_, hRow⟩ := (labelling.mem_orderedPath_iff hEnds row edge).mp hMem
    obtain ⟨_, hRow'⟩ := (labelling.mem_orderedPath_iff hEnds row' edge).mp hMem'
    exact hNe (hRow.symm.trans hRow')
  · exact ⟨labelling.row (NonDanglingEdge.stablePath ⟨edge, hSurvives⟩),
      (labelling.mem_orderedPath_iff hEnds _ edge).mpr ⟨hSurvives, rfl⟩⟩
  · exact ((labelling.mem_orderedPath_iff hEnds row edge).mp hMem).choose hDangling

/-- **The producer.**  An honest stable labelling whose stable paths are not
cycles gives a strong presentation, on the traversal-ordered rows of
`W4StableSource.StableLengthMatrixLabelling.orderedPresentation`. -/
noncomputable def ofLabelling (hEnds : HasPathEnds data)
    (labelling : StableLengthMatrixLabelling data coordinate) :
    StrongPresentation data coordinate where
  toPresentation := labelling.orderedPresentation hEnds
  decomposes := orderedDecomposes hEnds labelling
  chain row := labelling.orderedPath_chain hEnds row
  start row := labelling.startVertex hEnds row
  finish := finishVertex hEnds labelling
  head_isPathEnd row edge hEdge := by
    rw [StableLengthMatrixLabelling.orderedPresentation_path,
      labelling.orderedPath_head? hEnds row, Option.mem_def,
      Option.some_inj] at hEdge
    exact hEdge ▸ labelling.startEdge_isPathEnd hEnds row
  getLast_isPathEnd row := getLast_isPathEnd_finishVertex hEnds labelling row
  path_ne_nil row := orderedPath_ne_nil hEnds labelling row

@[simp] theorem ofLabelling_toPresentation (hEnds : HasPathEnds data)
    (labelling : StableLengthMatrixLabelling data coordinate) :
    (ofLabelling hEnds labelling).toPresentation =
      labelling.orderedPresentation hEnds := rfl

/-- Passing to the strong form leaves the length matrix untouched, so every
consequence already drawn from the honest presentation survives. -/
theorem matrix_ofLabelling (hEnds : HasPathEnds data)
    (labelling : StableLengthMatrixLabelling data coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix
        (ofLabelling hEnds labelling).toPresentation =
      GluingDatum.LengthMatrixPresentation.matrix labelling.presentation :=
  labelling.matrix_orderedPresentation hEnds

/-- **The producer from the full-dimensional package.**  Both hypotheses of
`ofLabelling` are fields of
`FullDimensionalSource.FullDimensionalSourcePresentation`, so a
full-dimensional source presentation *is* a strong presentation. -/
noncomputable def ofFullDimensional
    (fd : FullDimensionalSource.FullDimensionalSourcePresentation data coordinate) :
    StrongPresentation data coordinate :=
  ofLabelling fd.pathEnds fd.labelling

@[simp] theorem ofFullDimensional_toPresentation
    (fd : FullDimensionalSource.FullDimensionalSourcePresentation data coordinate) :
    (ofFullDimensional fd).toPresentation = fd.orderedPresentation := rfl

/-- The strong presentation of a full-dimensional source is still
nonsingular. -/
theorem det_ofFullDimensional_ne_zero
    (fd : FullDimensionalSource.FullDimensionalSourcePresentation data coordinate) :
    (GluingDatum.LengthMatrixPresentation.matrix
      (ofFullDimensional fd).toPresentation).det ≠ 0 :=
  fd.det_orderedPresentation_ne_zero

end Producer

/-! ## 4.  The reconciliation, in Lean

`PresentationDecomposition` and `W4StableSource` index rows by the
presentation's own `coordinate`; a requested specification indexes them by
`Fin p` through `InputRefinementData.InputInterface.slot`, and `slot` is an
equivalence, so the two quantifications are interchangeable.  `MeetsAt` is the
*same* chain predicate throughout. -/

section Reconciliation

open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancedGlobal.Candidate
open DraismaVargas.LocalCases.InputRefinementData
open Utilities.Certificate

variable {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- The chain predicate `MeetsAt`, unfolded: the two occurrences share a
surviving valency-two vertex.  This is the predicate of
`W4StableSource.StableLengthMatrixLabelling.orderedPath_chain`. -/
theorem meetsAt_iff (first second : data.SourceEdge) :
    MeetsAt data first second ↔
      ∃ vertex : data.SourceVertex, Incident data first vertex ∧
        Incident data second vertex ∧ nonDanglingValency data vertex = 2 :=
  Iff.rfl

/-- **Bare incidence does not pin the start, exhibited.**  In a row of two or
more occurrences let `meet` be a surviving valency-two vertex on the first
occurrence — by `StrongPresentation.chain` there is one, where the first two
occurrences meet.  Then bare *incidence* of the first occurrence holds at
`meet`, while the *path end* asked for by `StrongPresentation.head_isPathEnd`
does not.  So incidence alone does not say the row starts where it claims; it
is satisfied by an interior vertex of the row. -/
theorem head_incident_interior (strong : StrongPresentation data coordinate)
    {row : coordinate} {first second : data.SourceEdge}
    {rest : List data.SourceEdge}
    (hRow : strong.toPresentation.path row = first :: second :: rest)
    {meet : data.SourceVertex} (hFirst : Incident data first meet)
    (hMeet : nonDanglingValency data meet = 2) :
    (∀ edge ∈ (strong.toPresentation.path row).head?, Incident data edge meet) ∧
      ¬ ∀ edge ∈ (strong.toPresentation.path row).head?, IsPathEnd data edge meet := by
  have hHead : (strong.toPresentation.path row).head? = some first := by
    rw [hRow]; rfl
  constructor
  · intro edge hEdge
    rw [hHead, Option.mem_def, Option.some_inj] at hEdge
    exact hEdge ▸ hFirst
  · intro hAll
    exact (hAll first (by rw [hHead]; rfl)).2 hMeet

variable {wall : target.V} {candidate : Candidate target degree data wall}
  {coordinates : coordinate → ℚ} {n p : ℕ}
  {spec : SubdivisionGraph.Spec n p}
  {presentation : candidate.datum.LengthMatrixPresentation coordinate}

/-- **The row indexings agree.**  `InputInterface.slot` is an equivalence, so a
condition imposed on every stable slot `i : Fin p` is a condition imposed on
every matrix row, and conversely.  This is what lets a row condition stated
on slots and one stated on matrix rows (such as
`W4StableSource.StableLengthMatrixLabelling.orderedPath_chain`) be compared at all. -/
theorem forall_slot_iff (iface : InputInterface spec presentation coordinates)
    (property : coordinate → Prop) :
    (∀ i : Fin p, property (iface.slot i)) ↔ ∀ row : coordinate, property row :=
  ⟨fun hAll row ↦ by simpa using hAll (iface.slot.symm row), fun hAll i ↦ hAll _⟩

end Reconciliation

/-! ## 5.  The core dictionary

The row conditions of `StrongPresentation` (`decomposes`, `chain` and the two
endpoint conditions, read through `InputInterface.slot`) are source-side
statements.  What is *not* a source-side statement at all is the placement of
the requested core:

* `vertexAt`, together with the identification of the two ends of the row
  displaying slot `i` with `vertexAt (spec.core.tail i)` and
  `vertexAt (spec.core.head i)`.  This is not a consequence of the interface:
  `spec.core` does not appear in `InputInterface`, and the slot lengths alone
  do not determine the graph.

`CoreDictionary` is precisely that, and nothing else.  It mentions no face; the
relabeling it feeds is onto the *pruned* contracted source. -/

section Dictionary

open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancedGlobal.Candidate
open DraismaVargas.LocalCases.InputRefinementData
open Utilities.Certificate

variable {data : GluingDatum target degree} {wall : target.V}
  {candidate : Candidate target degree data wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {coordinates : coordinate → ℚ} {n p : ℕ}
  {spec : SubdivisionGraph.Spec n p}

/-- **What the source cannot know.**  The dictionary putting the stable core of
`spec` on the quotient source, matched with the ends a strong presentation
already names.  It is the one input about the requested core beyond
`StrongPresentation` and the interface; it mentions no face, so one term serves
every cleared face of the same `(strong, spec, iface)`. -/
structure CoreDictionary (spec : SubdivisionGraph.Spec n p)
    (strong : StrongPresentation candidate.datum coordinate)
    {F : Finset (Fin p)}
    (iface : InputInterface spec strong.toPresentation coordinates F) where
  /-- Which quotient-source vertex carries each stable core vertex. -/
  vertexAt : Fin n → candidate.datum.SourceVertex
  /-- The row displaying slot `i` starts where the stable tail of `i` sits. -/
  tail_eq : ∀ i : Fin p,
    vertexAt (spec.core.tail i) = strong.start (iface.slot i)
  /-- and ends where the stable head of `i` sits. -/
  head_eq : ∀ i : Fin p,
    vertexAt (spec.core.head i) = strong.finish (iface.slot i)

end Dictionary

/-! ## 6.  The forest receipt: the half the strong form pays for

`TerminalForestReceipt` isolates the honest Draisma--Vargas acyclicity argument
into two halves.  The arithmetic half — *no displayed row is entirely swallowed
by the zero set* — it derives from the march's `currentFinish_map`.  Read
through an `InputRefinementData.InputInterface` the same half is even cheaper:
`matrixMap` says the row value **is** `spec.length`, which `Spec.length_pos`
makes positive, so no march state is needed at all.

The other half is `CyclesAreRows`: a slot set carrying a cycle contains a
complete displayed row.  That is the incidence condition, and
`isForest_of_cyclesAreRows` shows the two halves together are exactly the
receipt.  `CyclesAreRows` is *not* proved here: it is a statement about how the
rows of a maximal-path presentation sit inside the quotient source, and the
`StrongPresentation` fields constrain each row separately without saying that
the rows exhaust the cycles.  See the module docstring. -/

section Forest

open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancedGlobal.Candidate
open DraismaVargas.LocalCases.InputRefinementData
open DraismaVargas.LocalCases.TerminalForestReceipt
open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral

variable {degree : ℕ} {target : CFGraph.{0}}
  {data : GluingDatum target degree} {wall : target.V}
  {candidate : Candidate target degree data wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {coordinates : coordinate → ℚ} {n p : ℕ}
  {spec : SubdivisionGraph.Spec n p}

/-- **The arithmetic half, from the interface alone.**  `matrixMap` identifies
the length-matrix value of a row with the requested stable slot length, which
is positive, so the row carries an occurrence of nonzero cleared length.  No
march state, and no field of `StrongPresentation`, is used. -/
theorem exists_sourceLength_ne_zero_of_interface
    {presentation : candidate.datum.LengthMatrixPresentation coordinate}
    (iface : InputInterface spec presentation coordinates)
    (face : ClearedFace candidate presentation coordinates) (row : coordinate) :
    ∃ edge ∈ presentation.path row,
      face.realization.sourceLength edge ≠ 0 := by
  refine exists_sourceLength_ne_zero_of_mulVec_ne_zero face ?_
  rw [iface.matrixMap]
  show ((spec.length (iface.slot.symm row) : ℕ) : ℚ) ≠ 0
  exact_mod_cast (spec.length_pos (iface.slot.symm row)).ne'

/-- The slot form: every row displays a canonical quotient-source slot outside
the zero set of the face. -/
theorem exists_notMem_sourceZeroSet_of_interface
    {presentation : candidate.datum.LengthMatrixPresentation coordinate}
    (iface : InputInterface spec presentation coordinates)
    (face : ClearedFace candidate presentation coordinates) (row : coordinate) :
    ∃ slot : Fin candidate.datum.sourceGraph.edges.card,
      slot ∉ face.realization.sourceZeroSet ∧
        face.realization.sourceEdgeAt slot ∈ presentation.path row := by
  refine exists_notMem_sourceZeroSet_of_mulVec_ne_zero face ?_
  rw [iface.matrixMap]
  show ((spec.length (iface.slot.symm row) : ℕ) : ℚ) ≠ 0
  exact_mod_cast (spec.length_pos (iface.slot.symm row)).ne'

/-- **The residual incidence condition.**  *Every cycle of the quotient source
is a union of complete displayed rows*, written so that it can be consumed: a
slot set that fails to be a census forest contains some displayed row entirely.

This is the second half of the honest argument.  It is a statement about how
the rows lie inside the quotient source — it says the maximal stable paths
exhaust every cycle — and no field of `StrongPresentation`, which constrains
one row at a time, implies it. -/
def CyclesAreRows
    (presentation : candidate.datum.LengthMatrixPresentation coordinate)
    (face : ClearedFace candidate presentation coordinates) : Prop :=
  ∀ slots : Finset (Fin candidate.datum.sourceGraph.edges.card),
    ¬ IsForest (UnitSubdivisionPresentation.core candidate.datum.sourceGraph) slots →
      ∃ row : coordinate, ∀ edge ∈ presentation.path row,
        face.realization.sourceSlotEquiv.symm edge ∈ slots

/-- **The two halves are the receipt.**  The arithmetic half of §6 and the
incidence condition together give the forest receipt -- the zero set of the
face is a census forest of the quotient source -- at the face they are stated
at. -/
theorem isForest_of_cyclesAreRows
    {presentation : candidate.datum.LengthMatrixPresentation coordinate}
    (iface : InputInterface spec presentation coordinates)
    (face : ClearedFace candidate presentation coordinates)
    (hCycles : CyclesAreRows presentation face) :
    IsForest (UnitSubdivisionPresentation.core candidate.datum.sourceGraph)
      face.realization.sourceZeroSet := by
  by_contra hForest
  obtain ⟨row, hRow⟩ := hCycles face.realization.sourceZeroSet hForest
  obtain ⟨slot, hSlot, hMem⟩ :=
    exists_notMem_sourceZeroSet_of_interface iface face row
  refine hSlot ?_
  have hSlotEq : face.realization.sourceSlotEquiv.symm
      (face.realization.sourceEdgeAt slot) = slot := by
    rw [← GluingDatum.NonnegativeIntegralRealization.sourceSlotEquiv_apply,
      Equiv.symm_apply_apply]
  exact hSlotEq ▸ hRow _ hMem

end Forest

/-! ## 8.  Joint satisfiability

The fields of `StrongPresentation` are not merely individually plausible: §3
constructs one from `W4StableSource.HasPathEnds` and an honest
`StableLengthMatrixLabelling`, so the whole list is realized simultaneously by a
single object, and `ofFullDimensional` realizes it from the package
`FullDimensionalSource.FullDimensionalSourcePresentation` that the local cases
already carry.  That is the strongest form of joint satisfiability available
without exhibiting a concrete gluing datum.

The one pair of fields that could conflict is `chain` against
`head_isPathEnd`/`getLast_isPathEnd`: the first demands a vertex of surviving
valency **two** on the first occurrence of a row, the second a vertex of
surviving valency **different from two** on the same occurrence.  They are
compatible precisely because the quotient source is loopless — an occurrence has
two distinct ends — and `start_ne_meet` below exhibits the two ends carrying the
two demands.  This rules out the failure mode in which two fields demand
incompatible things of one vertex. -/

section Satisfiability

variable {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The two demands sit on the two ends of one occurrence.**  In a row of two
or more occurrences the vertex where the first two meet is *not* the row's start
vertex, and the start vertex is its other end.  So `chain` and `head_isPathEnd`
constrain different ends of the same occurrence, and looplessness of the
quotient source (§0) is exactly what keeps those ends apart. -/
theorem start_ne_meet (strong : StrongPresentation data coordinate)
    {row : coordinate} {first second : data.SourceEdge}
    {rest : List data.SourceEdge}
    (hRow : strong.toPresentation.path row = first :: second :: rest)
    {meet : data.SourceVertex} (hFirst : Incident data first meet)
    (hMeet : nonDanglingValency data meet = 2) :
    meet ≠ strong.start row ∧
      strong.start row = otherEnd data first meet := by
  have hHead : IsPathEnd data first (strong.start row) := by
    refine strong.head_isPathEnd row first ?_
    rw [hRow]
    rfl
  have hNe : meet ≠ strong.start row := by
    intro hEq
    exact hHead.2 (hEq ▸ hMeet)
  refine ⟨hNe, ?_⟩
  rcases eq_or_eq_otherEnd data hFirst hHead.1 with hCase | hCase
  · exact absurd hCase.symm hNe
  · exact hCase

/-- A strong presentation exists whenever an honest labelling and
`HasPathEnds` do: the fields of §2 are jointly realized. -/
theorem nonempty_strongPresentation (hEnds : HasPathEnds data)
    (labelling : StableLengthMatrixLabelling data coordinate) :
    Nonempty (StrongPresentation data coordinate) :=
  ⟨ofLabelling hEnds labelling⟩

/-- and from the full-dimensional package the local cases already carry. -/
theorem nonempty_strongPresentation_of_fullDimensional
    (fd : FullDimensionalSource.FullDimensionalSourcePresentation data coordinate) :
    Nonempty (StrongPresentation data coordinate) :=
  ⟨ofFullDimensional fd⟩

end Satisfiability

end DraismaVargas.LocalCases.TraversalPresentation
