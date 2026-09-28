import DraismaVargas.LocalCases.CycleRows
import DraismaVargas.LocalCases.RefinementCore
import DraismaVargas.LocalCases.StrongRefinement

/-!
# Oriented rows, and the stable model they build

A `RefinementCore.SourceModel` at a cleared terminal face -- a stable model of
the pruned contracted quotient source -- is what the terminal face needs:
`SourceModel.laplacianEquiv` and `SourceModel.inputRefinement` turn it into the
input refinement.  Beyond a stable core dictionary
(`TraversalPresentation.CoreDictionary`), a certificate for it must supply two
things: that `vertexAt` together with the row breakpoints *enumerates* the
contraction classes, and that each row traverses its occurrences as an
**oriented walk**.  This file settles the second, constructs everything the
first does not touch, and reduces the whole obligation to one bijectivity
hypothesis on a canonically defined map.

## The orientation verdict (§1–2)

**Orientation is a theorem about `StrongPresentation` on every row of two or
more occurrences, and on a row of exactly one occurrence it is a strengthening
— one bit, which is itself free as soon as the stable core is modelled
injectively.**  In detail.

* `StrongPresentation.chain` is `MeetsAt`, existential in the meeting vertex.
  `meet_eq_walkVertex_succ` *names* it: under the walk invariant at position
  `j`, the meeting vertex of the `j`-th and `(j+1)`-st occurrences is the end
  of the `j`-th one the walk leaves by, and nothing else.  The proof is the
  uniqueness of the companion at a surviving valency-two vertex
  (`W4StableSource.exists_unique_other_of_nonDanglingValency_eq_two`) against
  `Decomposes.nodup`: three distinct surviving occurrences cannot meet at a
  divalent vertex.  `walk_invariant` propagates it along the row from the path
  end named by `head_isPathEnd`.
* `walkVertex_length` — the walk ends at `finish` — needs one extra bit, and
  only on a row of one occurrence: `2 ≤ row.length ∨ finish ≠ start`.
* That bit is **not** free from `StrongPresentation`: `reflectFinish` replaces
  `finish` by `start` on a single-occurrence row and is still a strong
  presentation with the same rows and the same starts
  (`not_oriented_reflectFinish`).  An occurrence has two ends and both can be
  path ends; `head_isPathEnd` and `getLast_isPathEnd` cannot tell them apart.
* But `orient_of_injective` recovers it for nothing in the situation that
  matters: `spec.core_loopless` plus an injective model of the stable core
  separate `start` from `finish` on *every* row.

So the honest traversal's orientation is not lost by passing to
`StrongPresentation` — it is recoverable, and `OrientedRow` is the bundled
form: a row together with the walk `vertex : ℕ → SourceVertex` whose interior
values are the meeting vertices (`vertex_succ_valency`) and whose two extreme
values are the row's ends.

## The model (§3–5)

`RowDictionary` is the certificate, and it **is**
`TraversalPresentation.CoreDictionary` — three fields, no face
(`coreDictionary` is the identity).  From it, and from the face:

* `positiveRow` — the refined slots of a row are its **positive sublist**: the
  occurrences the face does not contract, in traversal order
  (`segments_eq_positiveRow`).  Zero occurrences are contracted *within* the
  row by `degSpec.rep`; `position` names where in the row the `m`-th positive
  occurrence sits.
* `slotEquiv` — the refined slots **are** the kept slots of the contraction
  topology — the positive non-dangling occurrences, the slots of the pruned
  contracted spec `SourceContractionTopology.prunedSpec` — bijectively.  Derived,
  from `Decomposes` alone; no dictionary field is used.
* `vertexClass` — the canonical map from refined core vertices to contraction
  classes: a stable core vertex to the class of the vertex `vertexAt` puts it
  on, the `m`-th breakpoint of row `i` to the class of the vertex the walk
  reaches after the `m`-th positive occurrence.  Once `vertexAt` is fixed there
  is no choice left.  Along a run of contracted occurrences the walk stays in
  one class (`classOf_rowWalk_eq_of_zero_run`), which is what the endpoint
  equations of the model need.
* `sourceModel` — the three equations of `RefinementCore.SourceModel`, with the
  orientation flag `reversedAt` recording which of an occurrence's two named
  ends the walk enters by.  The **only** hypothesis is that `vertexClass` is a
  bijection onto the **kept** classes — `Set.BijOn (vertexClass dict topology)
  Set.univ {c | topology.KeptClass c}` — since a dangling positive occurrence
  hangs a discarded class off the quotient source that no refined vertex
  should reach.

That hypothesis is injectivity — a local condition — together with exhaustion
(every kept class is reached by a refined core vertex), which is a global
condition; `Spanning`, which puts every placement on a surviving vertex, makes
`vertexClass` land in the kept classes (`mapsTo_keptClass_of_spanning`, §5).
§5 also feeds the model to `SourceModel.laplacianEquiv` and
`SourceModel.inputRefinement`.

## What is assumed, precisely, and what is not

Beyond `StrongPresentation` and `InputInterface` the construction uses exactly
two things, the three fields of `RowDictionary` and `hBij`:

1. `vertexAt`, `tail_eq`, `head_eq` — `CoreDictionary`: where the stable core
   sits on the quotient source.  This is extra data, not read off
   `InputInterface`.
2. `hBij` — bijectivity of `vertexClass` onto the kept classes, of which
   exhaustion is the global part.

Nothing is assumed about the face.  In particular the dictionary does not ask
that the zero-length occurrences be exactly the dangling ones: zero fibres and
dangling occurrences both occur where Part I must run (boundary terminal
states, wall-crossing members), and they are handled where they belong — zeros
by the positive sublist, dangling occurrences by the pruned target and the
pendant pushforward in `ClosedEndpoint`.

No orientation is assumed anywhere: `reversedAt` is computed, and the
`oriented` bit is derived from `hBij` by `orient_of_injective`.
-/

namespace DraismaVargas.LocalCases.OrientedTraversal

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.TraversalPresentation

variable {target : CFGraph} {degree : ℕ}

/-! ## 1.  The oriented walk along a row -/

section Walk

variable {data : GluingDatum target degree}

/-- The vertex sequence of a walk along a list of occurrences entered at
`start`: every occurrence is left by the end it was not entered by. -/
noncomputable def walkVertex (data : GluingDatum target degree)
    (row : List data.SourceEdge) (start : data.SourceVertex) :
    ℕ → data.SourceVertex
  | 0 => start
  | j + 1 =>
      match row[j]? with
      | none => walkVertex data row start j
      | some edge => otherEnd data edge (walkVertex data row start j)

@[simp] theorem walkVertex_zero (row : List data.SourceEdge)
    (start : data.SourceVertex) : walkVertex data row start 0 = start := rfl

theorem walkVertex_succ (row : List data.SourceEdge) (start : data.SourceVertex)
    {j : ℕ} (hj : j < row.length) :
    walkVertex data row start (j + 1) =
      otherEnd data row[j] (walkVertex data row start j) := by
  show (match row[j]? with
    | none => walkVertex data row start j
    | some edge => otherEnd data edge (walkVertex data row start j)) = _
  rw [List.getElem?_eq_getElem hj]

/-- The occurrences of `row` strictly before position `j`. -/
def Earlier (row : List data.SourceEdge) (j : ℕ) (edge : data.SourceEdge) : Prop :=
  ∃ k, ∃ hk : k < row.length, k < j ∧ row[k] = edge

/-- The walk vertex at position `j` is an end of the `j`-th occurrence at which
every *other* surviving occurrence has already been passed.  This is the
invariant `walk_invariant` propagates. -/
def WalkInvariant (data : GluingDatum target degree)
    (row : List data.SourceEdge) (start : data.SourceVertex) (j : ℕ)
    (hj : j < row.length) : Prop :=
  Incident data row[j] (walkVertex data row start j) ∧
    ∀ f, ¬ IsDangling data f →
      Incident data f (walkVertex data row start j) → f ≠ row[j] →
        nonDanglingValency data (walkVertex data row start j) = 2 →
          Earlier row j f

/-- **The meeting vertex is the far end.**  Under the invariant at `j`, any
surviving valency-two vertex shared by the `j`-th and `(j+1)`-st occurrences is
the end of the `j`-th occurrence the walk leaves by.  This is the whole content
of orientation: `MeetsAt` is existential in the meeting vertex, and this names
it. -/
theorem meet_eq_walkVertex_succ {row : List data.SourceEdge}
    {start : data.SourceVertex} (hNodup : row.Nodup)
    (hSurvives : ∀ edge ∈ row, ¬ IsDangling data edge) {j : ℕ}
    (hj : j + 1 < row.length) (hInv : WalkInvariant data row start j
      (Nat.lt_of_succ_lt hj))
    {meet : data.SourceVertex} (hFirst : Incident data row[j] meet)
    (hSecond : Incident data row[j + 1] meet)
    (hValency : nonDanglingValency data meet = 2) :
    meet = walkVertex data row start (j + 1) := by
  obtain ⟨hIncident, hClosed⟩ := hInv
  have hjlt : j < row.length := Nat.lt_of_succ_lt hj
  have hNeIndex : row[j] ≠ row[j + 1] := by
    intro hEq
    exact absurd (hNodup.getElem_inj_iff.mp hEq) (by omega)
  rcases eq_or_eq_otherEnd data hIncident hFirst with hCase | hCase
  · exfalso
    rw [hCase] at hValency hSecond
    obtain ⟨k, hk, hklt, hkEq⟩ := hClosed row[j + 1]
      (hSurvives _ (List.getElem_mem hj)) hSecond (Ne.symm hNeIndex) hValency
    have : k = j + 1 := hNodup.getElem_inj_iff.mp hkEq
    omega
  · rw [walkVertex_succ row start hjlt, hCase]

/-- **The walk invariant, all along the row.** -/
theorem walk_invariant {row : List data.SourceEdge} {start : data.SourceVertex}
    (hNodup : row.Nodup) (hSurvives : ∀ edge ∈ row, ¬ IsDangling data edge)
    (hChain : row.IsChain (MeetsAt data))
    (hStart : ∀ h : 0 < row.length, IsPathEnd data row[0] start) :
    ∀ j, ∀ hj : j < row.length, WalkInvariant data row start j hj := by
  intro j
  induction j with
  | zero =>
      intro hj
      exact ⟨(hStart hj).1, fun _ _ _ _ hValency ↦ absurd hValency (hStart hj).2⟩
  | succ j ih =>
      intro hj
      have hjlt : j < row.length := Nat.lt_of_succ_lt hj
      have hInv := ih hjlt
      obtain ⟨meet, hFirst, hSecond, hValency⟩ := hChain.getElem j hj
      have hMeetEq :=
        meet_eq_walkVertex_succ hNodup hSurvives hj hInv hFirst hSecond hValency
      have hNeIndex : row[j] ≠ row[j + 1] := by
        intro hEq
        exact absurd (hNodup.getElem_inj_iff.mp hEq) (by omega)
      refine ⟨hMeetEq ▸ hSecond, fun f hf hfIncident hfNe hfValency ↦ ?_⟩
      have hPrevIncident : Incident data row[j] (walkVertex data row start (j + 1)) := by
        rw [walkVertex_succ row start hjlt]
        exact incident_otherEnd data _ _
      obtain ⟨other, -, hUnique⟩ :=
        exists_unique_other_of_nonDanglingValency_eq_two data hfValency
          (hSurvives _ (List.getElem_mem hj)) (hMeetEq ▸ hSecond)
      exact ⟨j, hjlt, by omega,
        (hUnique row[j] ⟨hNeIndex, hSurvives _ (List.getElem_mem hjlt),
          hPrevIncident⟩).trans
          (hUnique f ⟨hfNe, hf, hfIncident⟩).symm⟩

/-- Each occurrence of the row is incident to the walk vertex before it. -/
theorem walkVertex_incident {row : List data.SourceEdge} {start : data.SourceVertex}
    (hNodup : row.Nodup) (hSurvives : ∀ edge ∈ row, ¬ IsDangling data edge)
    (hChain : row.IsChain (MeetsAt data))
    (hStart : ∀ h : 0 < row.length, IsPathEnd data row[0] start)
    {j : ℕ} (hj : j < row.length) :
    Incident data row[j] (walkVertex data row start j) :=
  (walk_invariant hNodup hSurvives hChain hStart j hj).1

/-- and to the walk vertex after it. -/
theorem walkVertex_succ_incident {row : List data.SourceEdge}
    {start : data.SourceVertex} {j : ℕ} (hj : j < row.length) :
    Incident data row[j] (walkVertex data row start (j + 1)) := by
  rw [walkVertex_succ row start hj]
  exact incident_otherEnd data _ _

/-- **The interior walk vertices are the meeting vertices**: each has surviving
valency two, so it is an interior point of the stable path, not an end. -/
theorem walkVertex_succ_valency {row : List data.SourceEdge}
    {start : data.SourceVertex} (hNodup : row.Nodup)
    (hSurvives : ∀ edge ∈ row, ¬ IsDangling data edge)
    (hChain : row.IsChain (MeetsAt data))
    (hStart : ∀ h : 0 < row.length, IsPathEnd data row[0] start)
    {j : ℕ} (hj : j + 1 < row.length) :
    nonDanglingValency data (walkVertex data row start (j + 1)) = 2 := by
  obtain ⟨meet, hFirst, hSecond, hValency⟩ := hChain.getElem j hj
  rw [← meet_eq_walkVertex_succ hNodup hSurvives hj
    (walk_invariant hNodup hSurvives hChain hStart j (Nat.lt_of_succ_lt hj))
    hFirst hSecond hValency]
  exact hValency

/-- The walk never stands still: consecutive walk vertices differ, by
looplessness of the quotient source. -/
theorem walkVertex_ne_succ {row : List data.SourceEdge}
    {start : data.SourceVertex} {j : ℕ} (hj : j < row.length) :
    walkVertex data row start (j + 1) ≠ walkVertex data row start j := by
  rw [walkVertex_succ row start hj]
  exact otherEnd_ne data _ _


/-- **The walk ends where the row ends.**  The far end of the last occurrence
is the row's finish vertex.  The hypothesis `hOrient` is needed only for a row
of a single occurrence, where `finish` could otherwise be the same end as
`start`; §2 shows that case really is undetermined by a `StrongPresentation`,
and §4 that it is forced as soon as the stable core is modelled injectively. -/
theorem walkVertex_length {row : List data.SourceEdge}
    {start finish : data.SourceVertex} (hNodup : row.Nodup)
    (hSurvives : ∀ edge ∈ row, ¬ IsDangling data edge)
    (hChain : row.IsChain (MeetsAt data))
    (hStart : ∀ h : 0 < row.length, IsPathEnd data row[0] start)
    (hFinish : ∀ h : 0 < row.length,
      IsPathEnd data row[row.length - 1] finish)
    (hNeNil : row ≠ []) (hOrient : 2 ≤ row.length ∨ finish ≠ start) :
    walkVertex data row start row.length = finish := by
  have hpos : 0 < row.length := List.length_pos_of_ne_nil hNeNil
  set j := row.length - 1 with hjdef
  have hj : j < row.length := by omega
  have hlen : row.length = j + 1 := by omega
  have hEnd := hFinish hpos
  have hNe : finish ≠ walkVertex data row start j := by
    by_cases h2 : 2 ≤ row.length
    · have hi : j - 1 + 1 = j := by omega
      have hlt : (j - 1) + 1 < row.length := by omega
      have hVal := walkVertex_succ_valency hNodup hSurvives hChain hStart hlt
      rw [hi] at hVal
      intro hEq
      exact hEnd.2 (hEq ▸ hVal)
    · have h1 : row.length = 1 := by omega
      have hj0 : j = 0 := by omega
      rw [hj0, walkVertex_zero]
      rcases hOrient with hOrient | hOrient
      · omega
      · exact hOrient
  rcases eq_or_eq_otherEnd data
    (walkVertex_incident hNodup hSurvives hChain hStart hj) hEnd.1 with hCase | hCase
  · exact absurd hCase hNe
  · rw [hlen, walkVertex_succ row start hj, ← hCase]

/-! ### The oriented row, bundled -/

/-- **An oriented row.**  A nonempty duplicate-free chain of surviving
occurrences with two named ends, together with the one bit `oriented` that a
`StrongPresentation` leaves open: for a row of a single occurrence, which of
its two ends is the start.  Everything else is the strong presentation's own
row conditions, stated for one row. -/
structure OrientedRow (data : GluingDatum target degree) where
  /-- The occurrences of the row, in traversal order. -/
  row : List data.SourceEdge
  /-- The vertex the row starts at. -/
  start : data.SourceVertex
  /-- The vertex the row ends at. -/
  finish : data.SourceVertex
  /-- The row is nonempty. -/
  ne_nil : row ≠ []
  /-- It lists no occurrence twice. -/
  nodup : row.Nodup
  /-- Every occurrence it lists survives pruning. -/
  survives : ∀ edge ∈ row, ¬ IsDangling data edge
  /-- Consecutive occurrences meet at a surviving valency-two vertex. -/
  chain : row.IsChain (MeetsAt data)
  /-- The first occurrence sits at `start` through a path end. -/
  head_isPathEnd : ∀ h : 0 < row.length, IsPathEnd data row[0] start
  /-- The last occurrence sits at `finish` through a path end. -/
  getLast_isPathEnd : ∀ h : 0 < row.length,
    IsPathEnd data row[row.length - 1] finish
  /-- The orientation bit, vacuous except on a row of one occurrence. -/
  oriented : 2 ≤ row.length ∨ finish ≠ start

namespace OrientedRow

variable (orow : OrientedRow data)

/-- The walk vertex at position `j`. -/
noncomputable def vertex (j : ℕ) : data.SourceVertex :=
  walkVertex data orow.row orow.start j

@[simp] theorem vertex_zero : orow.vertex 0 = orow.start := rfl

theorem vertex_succ {j : ℕ} (hj : j < orow.row.length) :
    orow.vertex (j + 1) = otherEnd data orow.row[j] (orow.vertex j) :=
  walkVertex_succ orow.row orow.start hj

/-- **The row is an oriented walk.**  Occurrence `j` runs from `vertex j` to
`vertex (j+1)`, and these are its two distinct ends. -/
theorem incident_vertex {j : ℕ} (hj : j < orow.row.length) :
    Incident data orow.row[j] (orow.vertex j) :=
  walkVertex_incident orow.nodup orow.survives orow.chain orow.head_isPathEnd hj

theorem incident_vertex_succ {j : ℕ} (hj : j < orow.row.length) :
    Incident data orow.row[j] (orow.vertex (j + 1)) :=
  walkVertex_succ_incident hj

theorem vertex_succ_ne {j : ℕ} (hj : j < orow.row.length) :
    orow.vertex (j + 1) ≠ orow.vertex j :=
  walkVertex_ne_succ hj

/-- The interior walk vertices have surviving valency two. -/
theorem vertex_succ_valency {j : ℕ} (hj : j + 1 < orow.row.length) :
    nonDanglingValency data (orow.vertex (j + 1)) = 2 :=
  walkVertex_succ_valency orow.nodup orow.survives orow.chain
    orow.head_isPathEnd hj

/-- The walk ends at `finish`. -/
theorem vertex_length : orow.vertex orow.row.length = orow.finish :=
  walkVertex_length orow.nodup orow.survives orow.chain orow.head_isPathEnd
    orow.getLast_isPathEnd orow.ne_nil orow.oriented

/-- The two ends of the row are path ends: neither is an interior point of a
stable path. -/
theorem start_valency : nonDanglingValency data orow.start ≠ 2 :=
  (orow.head_isPathEnd (List.length_pos_of_ne_nil orow.ne_nil)).2

theorem finish_valency : nonDanglingValency data orow.finish ≠ 2 :=
  (orow.getLast_isPathEnd (List.length_pos_of_ne_nil orow.ne_nil)).2

/-- **Start and finish are never interior walk vertices.**  So the walk visits
`row.length + 1` positions of which only the two extreme ones can be junctions
of the stable graph. -/
theorem ne_start_of_interior {j : ℕ} (hj : j + 1 < orow.row.length) :
    orow.vertex (j + 1) ≠ orow.start := by
  intro hEq
  exact orow.start_valency (hEq ▸ orow.vertex_succ_valency hj)

theorem ne_finish_of_interior {j : ℕ} (hj : j + 1 < orow.row.length) :
    orow.vertex (j + 1) ≠ orow.finish := by
  intro hEq
  exact orow.finish_valency (hEq ▸ orow.vertex_succ_valency hj)

end OrientedRow

end Walk


/-! ## 2.  Where orientation comes from, and where it does not -/

section FromStrong

variable {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

theorem head?_eq_getElem {α : Type*} (l : List α) (h : 0 < l.length) :
    l.head? = some l[0] := by
  cases l with
  | nil => exact absurd h (by simp)
  | cons _ _ => rfl

theorem getLast?_eq_getElem {α : Type*} (l : List α) (h : 0 < l.length) :
    l.getLast? = some l[l.length - 1] := by
  have hne : l ≠ [] := List.ne_nil_of_length_pos h
  rw [List.getLast?_eq_getLast_of_ne_nil hne, List.getLast_eq_getElem]

/-- **The producer.**  Every row of a strong presentation is an oriented row,
given the one bit `hOrient`, which is vacuous unless the row has a single
occurrence.  Nothing else is assumed: the meeting vertices, which
`StrongPresentation.chain` leaves existential, are *named* by the walk. -/
noncomputable def orientedRow (strong : StrongPresentation data coordinate)
    (r : coordinate)
    (hOrient : 2 ≤ (strong.toPresentation.path r).length ∨
      strong.finish r ≠ strong.start r) :
    OrientedRow data where
  row := strong.toPresentation.path r
  start := strong.start r
  finish := strong.finish r
  ne_nil := strong.path_ne_nil r
  nodup := strong.decomposes.nodup r
  survives := fun _ hEdge ↦ strong.decomposes.not_isDangling_of_mem hEdge
  chain := strong.chain r
  head_isPathEnd := fun h ↦ strong.head_isPathEnd r _
    (by rw [Option.mem_def, head?_eq_getElem _ h])
  getLast_isPathEnd := fun h ↦ strong.getLast_isPathEnd r _
    (by rw [Option.mem_def, getLast?_eq_getElem _ h])
  oriented := hOrient

@[simp] theorem orientedRow_row (strong : StrongPresentation data coordinate)
    (r : coordinate) (hOrient : 2 ≤ (strong.toPresentation.path r).length ∨
      strong.finish r ≠ strong.start r) :
    (orientedRow strong r hOrient).row = strong.toPresentation.path r := rfl

@[simp] theorem orientedRow_start (strong : StrongPresentation data coordinate)
    (r : coordinate) (hOrient : 2 ≤ (strong.toPresentation.path r).length ∨
      strong.finish r ≠ strong.start r) :
    (orientedRow strong r hOrient).start = strong.start r := rfl

@[simp] theorem orientedRow_finish (strong : StrongPresentation data coordinate)
    (r : coordinate) (hOrient : 2 ≤ (strong.toPresentation.path r).length ∨
      strong.finish r ≠ strong.start r) :
    (orientedRow strong r hOrient).finish = strong.finish r := rfl

/-- **Orientation is free on a row of two or more occurrences.**  No hypothesis
beyond `StrongPresentation` is needed: `hOrient` is discharged by the length. -/
noncomputable def orientedRow_of_two_le (strong : StrongPresentation data coordinate)
    (r : coordinate) (hLen : 2 ≤ (strong.toPresentation.path r).length) :
    OrientedRow data :=
  orientedRow strong r (Or.inl hLen)

/-! ### The one bit that is not free

For a row of a single occurrence `StrongPresentation` constrains `start` and
`finish` only to be ends of that occurrence at which the stable path does not
continue — and an occurrence can have two such ends.  Replacing `finish` by
`start` on such a row therefore leaves a strong presentation with the *same*
rows, the same starts, and the opposite orientation. -/

/-- The strong presentation with the finish vertex of one single-occurrence row
replaced by its start vertex. -/
noncomputable def reflectFinish (strong : StrongPresentation data coordinate)
    (r : coordinate) (hLen : (strong.toPresentation.path r).length = 1) :
    StrongPresentation data coordinate where
  toPresentation := strong.toPresentation
  decomposes := strong.decomposes
  chain := strong.chain
  start := strong.start
  finish := fun row ↦ if row = r then strong.start row else strong.finish row
  head_isPathEnd := strong.head_isPathEnd
  getLast_isPathEnd := by
    intro row edge hEdge
    by_cases hrow : row = r
    · rw [if_pos hrow]
      refine strong.head_isPathEnd row edge ?_
      have hLen' : (strong.toPresentation.path row).length = 1 := by
        rw [hrow]; exact hLen
      have hidx : (strong.toPresentation.path row).length - 1 = 0 := by omega
      rw [Option.mem_def, getLast?_eq_getElem _ (by omega)] at hEdge
      rw [Option.mem_def, head?_eq_getElem _ (by omega), ← hEdge]
      simp [hidx]
    · simp only [if_neg hrow]
      exact strong.getLast_isPathEnd row edge hEdge
  path_ne_nil := strong.path_ne_nil

@[simp] theorem reflectFinish_toPresentation
    (strong : StrongPresentation data coordinate) (r : coordinate)
    (hLen : (strong.toPresentation.path r).length = 1) :
    (reflectFinish strong r hLen).toPresentation = strong.toPresentation := rfl

@[simp] theorem reflectFinish_start (strong : StrongPresentation data coordinate)
    (r : coordinate) (hLen : (strong.toPresentation.path r).length = 1) :
    (reflectFinish strong r hLen).start = strong.start := rfl

@[simp] theorem reflectFinish_finish_self
    (strong : StrongPresentation data coordinate) (r : coordinate)
    (hLen : (strong.toPresentation.path r).length = 1) :
    (reflectFinish strong r hLen).finish r = strong.start r := by
  show (if r = r then strong.start r else strong.finish r) = strong.start r
  rw [if_pos rfl]

/-- **Orientation is a strengthening of `StrongPresentation`, not a theorem
about it.**  A single-occurrence row admits a strong presentation with the same
underlying presentation, the same start vertices, and `finish = start` on that
row — so the walk cannot end where the row ends, and the `oriented` field of
`OrientedRow` fails.  Hence `hOrient` above cannot be removed. -/
theorem not_oriented_reflectFinish (strong : StrongPresentation data coordinate)
    (r : coordinate) (hLen : (strong.toPresentation.path r).length = 1) :
    ¬ (2 ≤ ((reflectFinish strong r hLen).toPresentation.path r).length ∨
        (reflectFinish strong r hLen).finish r ≠
          (reflectFinish strong r hLen).start r) := by
  rintro (hCase | hCase)
  · rw [reflectFinish_toPresentation, hLen] at hCase
    omega
  · exact hCase (reflectFinish_finish_self strong r hLen)

end FromStrong


/-! ## 3.  The source-side dictionary of a cleared face -/

section Model

open Utilities
open Utilities.Certificate
open Utilities.Certificate.DegenerateSpec
open Utilities.Certificate.IteratedSplitRefinement
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancedGlobal.Candidate
open DraismaVargas.LocalCases.InputRefinementData
open DraismaVargas.LocalCases.RefinementCore
open DraismaVargas.LocalCases.ZeroForestBridge
open DraismaVargas.LocalCases.ZeroForestPreservation

variable {gluing : GluingDatum target degree} {wall : target.V}
  {candidate : Candidate target degree gluing wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {coordinates : coordinate → ℚ}
  {n p : ℕ} {spec : SubdivisionGraph.Spec n p}
  {strong : TraversalPresentation.StrongPresentation candidate.datum coordinate}
  {face : ClearedFace candidate strong.toPresentation coordinates}
  {topology : ClearedFace.SourceContractionTopology face}

/-! ### Contraction classes, read on the quotient source -/

/-- The contraction class of a quotient-source vertex:
`PrunedContractedSpec`'s `SourceContractionTopology.classOf`, under a local
name. -/
noncomputable abbrev classOf (topology : ClearedFace.SourceContractionTopology face)
    (u : candidate.datum.SourceVertex) : topology.degSpec.Class :=
  ClearedFace.SourceContractionTopology.classOf topology u

/-- The `rep`-class of the tail of a surviving slot is the class of the first
end of the occurrence it carries. -/
theorem rep_core_tail (topology : ClearedFace.SourceContractionTopology face)
    (s : Fin candidate.datum.sourceGraph.edges.card) :
    topology.degSpec.rep (topology.degSpec.core.tail s) =
      (classOf topology
        (candidate.datum.sourceEnds (face.realization.sourceEdgeAt s)).1).val :=
  (congrArg Subtype.val
    (ClearedFace.SourceContractionTopology.classOf_sourceEnds_fst topology s)).symm

/-- and of the head, the class of the second end. -/
theorem rep_core_head (topology : ClearedFace.SourceContractionTopology face)
    (s : Fin candidate.datum.sourceGraph.edges.card) :
    topology.degSpec.rep (topology.degSpec.core.head s) =
      (classOf topology
        (candidate.datum.sourceEnds (face.realization.sourceEdgeAt s)).2).val :=
  (congrArg Subtype.val
    (ClearedFace.SourceContractionTopology.classOf_sourceEnds_snd topology s)).symm

/-- The degenerate slot length is the cleared source length of the occurrence
the slot carries. -/
theorem degSpec_length (topology : ClearedFace.SourceContractionTopology face)
    (s : Fin candidate.datum.sourceGraph.edges.card) :
    topology.degSpec.length s =
      face.realization.sourceLength (face.realization.sourceEdgeAt s) := rfl

/-- **A contracted occurrence joins the classes of its two ends**, read at
`otherEnd`. -/
theorem classOf_otherEnd_of_sourceLength_zero
    (topology : ClearedFace.SourceContractionTopology face)
    {edge : candidate.datum.SourceEdge} {v : candidate.datum.SourceVertex}
    (hIncident : Incident candidate.datum edge v)
    (hZero : face.realization.sourceLength edge = 0) :
    classOf topology v = classOf topology (otherEnd candidate.datum edge v) := by
  have h := ClearedFace.SourceContractionTopology.classOf_eq_of_sourceLength_zero
    topology hZero
  unfold otherEnd
  split_ifs with hFirst
  · rw [← hFirst]
    exact h
  · rcases hIncident with hIncident | hIncident
    · exact absurd hIncident hFirst
    · rw [← hIncident]
      exact h.symm

/-! ### The certificate -/

/-- **The stable core dictionary a local case must supply.**  It is
`TraversalPresentation.CoreDictionary` on the nose:

* `vertexAt`, `tail_eq`, `head_eq` — the stable core of `spec` sits on the
  quotient source, matched with the two ends a strong presentation already
  names.  This is extra data, not read off `InputInterface`.

Nothing here is a bijectivity claim: `vertexAt` is a bare function.  What §4
adds on top is one bijectivity hypothesis on a *canonically constructed* map —
and, given spanning, that hypothesis is injectivity together with exhaustion of
the kept classes (§5).  The dictionary mentions no face: the same term serves
every cleared face of the same `(strong, spec, iface)`. -/
abbrev RowDictionary
    (strong : TraversalPresentation.StrongPresentation candidate.datum coordinate)
    (spec : SubdivisionGraph.Spec n p)
    {F : Finset (Fin p)}
    (iface : InputInterface spec strong.toPresentation coordinates F) : Type _ :=
  TraversalPresentation.CoreDictionary spec strong iface

namespace RowDictionary

variable {iface : InputInterface spec strong.toPresentation coordinates}

/-- The row displaying stable slot `i`. -/
abbrev row (i : Fin p) : List candidate.datum.SourceEdge :=
  strong.toPresentation.path (iface.slot i)

/-! ### The row as an oriented walk, indexed by the stable slot -/

theorem row_nodup (i : Fin p) :
    (row (strong := strong) (iface := iface) i).Nodup :=
  strong.decomposes.nodup _

theorem row_survives (i : Fin p) :
    ∀ edge ∈ row (strong := strong) (iface := iface) i,
      ¬ IsDangling candidate.datum edge :=
  fun _ hEdge ↦ strong.decomposes.not_isDangling_of_mem hEdge

theorem row_chain (i : Fin p) :
    (row (strong := strong) (iface := iface) i).IsChain
      (TraversalPresentation.MeetsAt candidate.datum) :=
  strong.chain _

theorem row_head_isPathEnd (i : Fin p)
    (h : 0 < (row (strong := strong) (iface := iface) i).length) :
    IsPathEnd candidate.datum (row (strong := strong) (iface := iface) i)[0]
      (strong.start (iface.slot i)) :=
  strong.head_isPathEnd _ _ (by rw [Option.mem_def, head?_eq_getElem _ h])

theorem row_getLast_isPathEnd (i : Fin p)
    (h : 0 < (row (strong := strong) (iface := iface) i).length) :
    IsPathEnd candidate.datum
      (row (strong := strong) (iface := iface) i)[
        (row (strong := strong) (iface := iface) i).length - 1]
      (strong.finish (iface.slot i)) :=
  strong.getLast_isPathEnd _ _ (by rw [Option.mem_def, getLast?_eq_getElem _ h])

/-- The oriented walk along the row displaying stable slot `i`. -/
noncomputable def rowWalk
    (strong : TraversalPresentation.StrongPresentation candidate.datum coordinate)
    (iface : InputInterface spec strong.toPresentation coordinates)
    (i : Fin p) (k : ℕ) : candidate.datum.SourceVertex :=
  walkVertex candidate.datum (row (strong := strong) (iface := iface) i)
    (strong.start (iface.slot i)) k

@[simp] theorem rowWalk_zero (i : Fin p) :
    rowWalk strong iface i 0 = strong.start (iface.slot i) := rfl

theorem rowWalk_succ {i : Fin p} {k : ℕ}
    (hk : k < (row (strong := strong) (iface := iface) i).length) :
    rowWalk strong iface i (k + 1) =
      otherEnd candidate.datum (row (strong := strong) (iface := iface) i)[k]
        (rowWalk strong iface i k) :=
  walkVertex_succ _ _ hk

theorem rowWalk_incident {i : Fin p} {k : ℕ}
    (hk : k < (row (strong := strong) (iface := iface) i).length) :
    Incident candidate.datum (row (strong := strong) (iface := iface) i)[k]
      (rowWalk strong iface i k) :=
  walkVertex_incident (row_nodup i) (row_survives i) (row_chain i)
    (row_head_isPathEnd i) hk

/-- **The walk ends at the row's finish vertex**, given the orientation bit. -/
theorem rowWalk_length {i : Fin p}
    (hOrient : 2 ≤ (row (strong := strong) (iface := iface) i).length ∨
      strong.finish (iface.slot i) ≠ strong.start (iface.slot i)) :
    rowWalk strong iface i (row (strong := strong) (iface := iface) i).length =
      strong.finish (iface.slot i) :=
  walkVertex_length (row_nodup i) (row_survives i) (row_chain i)
    (row_head_isPathEnd i) (row_getLast_isPathEnd i) (strong.path_ne_nil _) hOrient

/-- **Along a run of contracted occurrences the walk stays in one class.**
This is what lets a breakpoint of the refinement — which sits between two
*positive* occurrences — be sent to the class of a whole contracted run. -/
theorem classOf_rowWalk_eq_of_zero_run (topology : ClearedFace.SourceContractionTopology face)
    {i : Fin p} {a b : ℕ} (hab : a ≤ b)
    (hb : b ≤ (row (strong := strong) (iface := iface) i).length)
    (hZero : ∀ k, ∀ hk : k < (row (strong := strong) (iface := iface) i).length,
      a ≤ k → k < b →
        face.realization.sourceLength (row (strong := strong) (iface := iface) i)[k] = 0) :
    classOf topology (rowWalk strong iface i a) =
      classOf topology (rowWalk strong iface i b) := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
      have hblt : b < (row (strong := strong) (iface := iface) i).length := by omega
      rw [ih (by omega) (fun k hk hak hkb ↦ hZero k hk hak (by omega)), rowWalk_succ hblt]
      exact classOf_otherEnd_of_sourceLength_zero topology
        (rowWalk_incident (strong := strong) (iface := iface) hblt)
        (hZero b hblt hab (Nat.lt_succ_self b))

/-! ### The positive sublist of a row -/

/-- The positive sublist of the row displaying stable slot `i`: the occurrences
the face does not contract, in traversal order.  These are the refined slots
of `i`. -/
def positiveRow (iface : InputInterface spec strong.toPresentation coordinates)
    (face : ClearedFace candidate strong.toPresentation coordinates) (i : Fin p) :
    List candidate.datum.SourceEdge :=
  (row (strong := strong) (iface := iface) i).filter
    fun edge ↦ decide (0 < face.realization.sourceLength edge)

theorem mem_positiveRow {i : Fin p} {edge : candidate.datum.SourceEdge} :
    edge ∈ positiveRow iface face i ↔
      edge ∈ row (strong := strong) (iface := iface) i ∧
        0 < face.realization.sourceLength edge := by
  simp [positiveRow, List.mem_filter]

theorem positiveRow_sublist (i : Fin p) :
    (positiveRow iface face i).Sublist (row (strong := strong) (iface := iface) i) :=
  List.filter_sublist

theorem positiveRow_nodup (i : Fin p) : (positiveRow iface face i).Nodup :=
  (row_nodup (strong := strong) (iface := iface) i).filter _

theorem sourceLength_pos_of_mem_positiveRow {i : Fin p}
    {edge : candidate.datum.SourceEdge} (hEdge : edge ∈ positiveRow iface face i) :
    0 < face.realization.sourceLength edge :=
  (mem_positiveRow.mp hEdge).2

theorem not_isDangling_of_mem_positiveRow {i : Fin p}
    {edge : candidate.datum.SourceEdge} (hEdge : edge ∈ positiveRow iface face i) :
    ¬ IsDangling candidate.datum edge :=
  row_survives (strong := strong) (iface := iface) i edge (mem_positiveRow.mp hEdge).1

/-- A short name for `sourceLength_pos_of_mem_positiveRow`: an occurrence of the
positive sublist has positive length. -/
theorem sourceLength_pos_of_mem {i : Fin p}
    {edge : candidate.datum.SourceEdge} (hEdge : edge ∈ positiveRow iface face i) :
    0 < face.realization.sourceLength edge :=
  sourceLength_pos_of_mem_positiveRow hEdge

/-- **The prescribed segment list of a slot is its positive sublist, measured.**
This is `InputRefinementData.segmentData_segments` together with
`List.filter_map`: the face's contraction discards exactly the zero entries. -/
theorem segments_eq_positiveRow (i : Fin p) :
    (segmentData iface face).segments i =
      (positiveRow iface face i).map face.realization.sourceLength := by
  rw [segmentData_segments, OrderedPathSplit.positiveSegments, rowSegments, List.filter_map]
  rfl

/-- A short name for `segments_eq_positiveRow`: the segment list is the
positive sublist measured, and no dictionary enters. -/
theorem segments_eq (i : Fin p) :
    (segmentData iface face).segments i =
      (positiveRow iface face i).map face.realization.sourceLength :=
  segments_eq_positiveRow i

/-- so the refined slots of `i` are exactly the positions of its positive
sublist. -/
theorem segments_length (i : Fin p) :
    ((segmentData iface face).segments i).length = (positiveRow iface face i).length := by
  rw [segments_eq_positiveRow, List.length_map]

/-- **No row is contracted entirely**: the interface makes every row total the
positive stable length (`InputRefinementData.rowSegments_sum`), and the
positive sublist carries all of it. -/
theorem positiveRow_ne_nil (i : Fin p) : positiveRow iface face i ≠ [] := by
  intro hNil
  have hSum := rowSegments_sum_of_not_mem iface face (by simp : i ∉ (∅ : Finset (Fin p)))
  have hPositive : ((segmentData iface face).segments i).sum = (rowSegments iface face i).sum :=
    OrderedPathSplit.sum_positiveSegments _
  rw [segments_eq_positiveRow, hNil, List.map_nil, List.sum_nil] at hPositive
  have := Nat.mul_pos face.scale_pos (spec.length_pos i)
  omega

/-! ### The refined slots are the kept slots -/

theorem getD_map_zero {α : Type*} (f : α → ℕ) (l : List α) {m : ℕ}
    (h : m < l.length) : (l.map f).getD m 0 = f l[m] := by
  rw [List.getD_eq_getElem (l.map f) 0 (by simpa using h), List.getElem_map]

/-- The index of a refined slot in the positive sublist of its row. -/
def positiveIndex (x : RefinedSlotIndex iface face) : Fin (positiveRow iface face x.1).length :=
  ⟨(x.2 : ℕ), by rw [← segments_length]; exact x.2.isLt⟩

@[simp] theorem positiveIndex_val (x : RefinedSlotIndex iface face) :
    ((positiveIndex x : Fin _) : ℕ) = (x.2 : ℕ) := rfl

/-- The positive source occurrence carrying refined slot `x`: the `x.2`-th
entry of the positive sublist of the row displaying stable slot `x.1`. -/
def occurrence (x : RefinedSlotIndex iface face) : candidate.datum.SourceEdge :=
  (positiveRow iface face x.1)[(positiveIndex x : ℕ)]

theorem occurrence_mem_positiveRow (x : RefinedSlotIndex iface face) :
    occurrence x ∈ positiveRow iface face x.1 :=
  List.getElem_mem _

theorem occurrence_mem (x : RefinedSlotIndex iface face) :
    occurrence x ∈ row (strong := strong) (iface := iface) x.1 :=
  (mem_positiveRow.mp (occurrence_mem_positiveRow x)).1

theorem sourceLength_occurrence_pos (x : RefinedSlotIndex iface face) :
    0 < face.realization.sourceLength (occurrence x) :=
  sourceLength_pos_of_mem_positiveRow (occurrence_mem_positiveRow x)

theorem not_isDangling_occurrence (x : RefinedSlotIndex iface face) :
    ¬ IsDangling candidate.datum (occurrence x) :=
  not_isDangling_of_mem_positiveRow (occurrence_mem_positiveRow x)

/-- The prescribed segment at a position of the positive sublist. -/
theorem segments_getD_of_lt (i : Fin p) {k : ℕ} (hk : k < (positiveRow iface face i).length) :
    ((segmentData iface face).segments i).getD k 0 =
      face.realization.sourceLength (positiveRow iface face i)[k] := by
  rw [segments_eq_positiveRow, getD_map_zero _ _ hk]

/-- **The refined slot carries the prescribed segment.** -/
theorem segments_getD (x : RefinedSlotIndex iface face) :
    ((segmentData iface face).segments x.1).getD (x.2 : ℕ) 0 =
      face.realization.sourceLength (occurrence x) :=
  segments_getD_of_lt x.1 (positiveIndex x).isLt

theorem occurrence_injective :
    Function.Injective (occurrence (iface := iface) (face := face)) := by
  rintro ⟨i, m⟩ ⟨i', m'⟩ hEq
  have hMem : occurrence (⟨i, m⟩ : RefinedSlotIndex iface face) ∈
      row (strong := strong) (iface := iface) i :=
    occurrence_mem ⟨i, m⟩
  have hMem' : occurrence (⟨i, m⟩ : RefinedSlotIndex iface face) ∈
      row (strong := strong) (iface := iface) i' := by
    rw [hEq]; exact occurrence_mem ⟨i', m'⟩
  have hRow : i = i' := by
    by_contra hNe
    exact strong.decomposes.disjoint (iface.slot i) (iface.slot i')
      (fun hSlot ↦ hNe (iface.slot.injective hSlot)) _ hMem hMem'
  subst hRow
  have hIdx : (m : ℕ) = (m' : ℕ) :=
    (positiveRow_nodup (iface := iface) (face := face) i).getElem_inj_iff.mp hEq
  exact congrArg (Sigma.mk i) (Fin.ext hIdx)

/-- Every positive non-dangling occurrence is a refined slot. -/
theorem occurrence_surjective {edge : candidate.datum.SourceEdge}
    (hPos : 0 < face.realization.sourceLength edge)
    (hSurvives : ¬ IsDangling candidate.datum edge) :
    ∃ x : RefinedSlotIndex iface face, occurrence x = edge := by
  obtain ⟨r, hr⟩ := strong.decomposes.surviving_mem edge hSurvives
  have hMem : edge ∈ positiveRow iface face (iface.slot.symm r) := by
    refine mem_positiveRow.mpr ⟨?_, hPos⟩
    show edge ∈ strong.toPresentation.path (iface.slot (iface.slot.symm r))
    rw [Equiv.apply_symm_apply]; exact hr
  obtain ⟨m, hm, hmEq⟩ := List.mem_iff_getElem.mp hMem
  exact ⟨⟨iface.slot.symm r, ⟨m, by rw [segments_length]; exact hm⟩⟩, hmEq⟩

/-- **`slotModel`, constructed.**  The refined slots of the canonical
refinement are exactly the kept slots of the contraction topology — the
positive non-dangling occurrences — a bijection, not a count.  Only
`Decomposes` is used; no dictionary enters. -/
noncomputable def slotEquiv (iface : InputInterface spec strong.toPresentation coordinates)
    (topology : ClearedFace.SourceContractionTopology face) :
    RefinedSlotIndex iface face ≃
      {e : topology.degSpec.PositiveSlot // topology.KeptSlot e} :=
  Equiv.ofBijective
    (fun x ↦ ⟨⟨slotOf candidate.datum face.realization (occurrence x), by
        rw [degSpec_length, sourceEdgeAt_slotOf]
        exact sourceLength_occurrence_pos x⟩, by
        show ¬ IsDangling candidate.datum
          (face.realization.sourceEdgeAt (slotOf candidate.datum face.realization (occurrence x)))
        rw [sourceEdgeAt_slotOf]
        exact not_isDangling_occurrence x⟩)
    ⟨fun x y hxy ↦ occurrence_injective (by
        have h := congrArg (fun s ↦ face.realization.sourceEdgeAt s.val.val) hxy
        simpa using h),
      fun s ↦ by
        obtain ⟨x, hx⟩ := occurrence_surjective
          (show 0 < face.realization.sourceLength
            (face.realization.sourceEdgeAt s.val.val) from s.val.property) s.property
        refine ⟨x, Subtype.ext (Subtype.ext ?_)⟩
        show slotOf candidate.datum face.realization (occurrence x) = s.val.val
        rw [hx, slotOf_sourceEdgeAt]⟩

@[simp] theorem slotEquiv_val (topology : ClearedFace.SourceContractionTopology face)
    (x : RefinedSlotIndex iface face) :
    (slotEquiv iface topology x).val.val =
      slotOf candidate.datum face.realization (occurrence x) := rfl

@[simp] theorem sourceEdgeAt_slotEquiv (topology : ClearedFace.SourceContractionTopology face)
    (x : RefinedSlotIndex iface face) :
    face.realization.sourceEdgeAt (slotEquiv iface topology x).val.val = occurrence x := by
  rw [slotEquiv_val, sourceEdgeAt_slotOf]

/-! ### Where the positive occurrences sit in the row

The positive sublist is a sublist, so its entries occupy an increasing
sequence of positions of the row (`List.sublist_iff_exists_fin_orderEmbedding_get_eq`).
`position i m` is the position of the `m`-th positive occurrence; every
position carrying a positive occurrence is one of them
(`exists_position_of_pos`), so the positions strictly between consecutive
ones, before the first and after the last carry only contracted
occurrences. -/

theorem exists_positionEmbedding (i : Fin p) :
    ∃ f : Fin (positiveRow iface face i).length ↪o
        Fin (row (strong := strong) (iface := iface) i).length,
      ∀ m : Fin (positiveRow iface face i).length,
        (positiveRow iface face i)[(m : ℕ)] =
          (row (strong := strong) (iface := iface) i)[((f m : Fin _) : ℕ)] := by
  obtain ⟨f, hf⟩ :=
    List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
      (positiveRow_sublist (iface := iface) (face := face) i)
  refine ⟨f, fun m ↦ ?_⟩
  have h := hf m
  simp only [List.get_eq_getElem] at h
  exact h

/-- The positions of the positive occurrences of row `i`, as an order
embedding into the positions of the row. -/
noncomputable def positionEmbedding (i : Fin p) :
    Fin (positiveRow iface face i).length ↪o
      Fin (row (strong := strong) (iface := iface) i).length :=
  Classical.choose (exists_positionEmbedding i)

/-- The position in its row of the `m`-th positive occurrence. -/
noncomputable def position (i : Fin p) (m : Fin (positiveRow iface face i).length) : ℕ :=
  ((positionEmbedding (iface := iface) (face := face) i m : Fin _) : ℕ)

theorem position_lt (i : Fin p) (m : Fin (positiveRow iface face i).length) :
    position i m < (row (strong := strong) (iface := iface) i).length :=
  (positionEmbedding (iface := iface) (face := face) i m).isLt

theorem getElem_position (i : Fin p) (m : Fin (positiveRow iface face i).length) :
    (row (strong := strong) (iface := iface) i)[position i m]'(position_lt i m) =
      (positiveRow iface face i)[(m : ℕ)] :=
  (Classical.choose_spec (exists_positionEmbedding (iface := iface) (face := face) i) m).symm

theorem position_lt_position_iff {i : Fin p}
    {m m' : Fin (positiveRow iface face i).length} :
    position i m < position i m' ↔ m < m' := by
  unfold position
  rw [← Fin.lt_def]
  exact (positionEmbedding i).lt_iff_lt

theorem position_le_position_iff {i : Fin p}
    {m m' : Fin (positiveRow iface face i).length} :
    position i m ≤ position i m' ↔ m ≤ m' := by
  unfold position
  rw [← Fin.le_def]
  exact (positionEmbedding i).le_iff_le

theorem position_injective (i : Fin p) :
    Function.Injective (position (iface := iface) (face := face) i) := by
  intro m m' h
  exact le_antisymm (position_le_position_iff.mp h.le) (position_le_position_iff.mp h.ge)

theorem position_strictMono (i : Fin p) :
    StrictMono (position (iface := iface) (face := face) i) :=
  fun _ _ h ↦ position_lt_position_iff.mpr h

/-- The occurrence at a positive position is positive. -/
theorem sourceLength_position_pos (i : Fin p) (m : Fin (positiveRow iface face i).length) :
    0 < face.realization.sourceLength
      ((row (strong := strong) (iface := iface) i)[position i m]'(position_lt i m)) := by
  rw [getElem_position]
  exact sourceLength_pos_of_mem_positiveRow (List.getElem_mem m.isLt)

/-- and every positive position is one of them. -/
theorem exists_position_of_pos {i : Fin p} {k : ℕ}
    (hk : k < (row (strong := strong) (iface := iface) i).length)
    (hPos : 0 < face.realization.sourceLength
      (row (strong := strong) (iface := iface) i)[k]) :
    ∃ m : Fin (positiveRow iface face i).length, position i m = k := by
  have hMem : (row (strong := strong) (iface := iface) i)[k] ∈ positiveRow iface face i :=
    mem_positiveRow.mpr ⟨List.getElem_mem hk, hPos⟩
  obtain ⟨m, hm, hmEq⟩ := List.mem_iff_getElem.mp hMem
  refine ⟨⟨m, hm⟩, ?_⟩
  refine (List.Nodup.getElem_inj_iff (row_nodup (strong := strong) (iface := iface) i)
    (hi := position_lt i ⟨m, hm⟩) (hj := hk)).mp ?_
  rw [getElem_position]
  exact hmEq

/-- A position that is no positive position carries a contracted
occurrence. -/
theorem sourceLength_eq_zero_of_forall_position_ne {i : Fin p} {k : ℕ}
    (hk : k < (row (strong := strong) (iface := iface) i).length)
    (hNe : ∀ m : Fin (positiveRow iface face i).length, position i m ≠ k) :
    face.realization.sourceLength (row (strong := strong) (iface := iface) i)[k] = 0 := by
  by_contra hPos
  obtain ⟨m, hm⟩ := exists_position_of_pos hk (Nat.pos_of_ne_zero hPos)
  exact hNe m hm

/-- Before the first positive occurrence everything is contracted. -/
theorem sourceLength_eq_zero_of_lt_position_zero {i : Fin p} {k : ℕ}
    (hk : k < (row (strong := strong) (iface := iface) i).length)
    (m₀ : Fin (positiveRow iface face i).length) (hlt : k < position i m₀)
    (hFirst : (m₀ : ℕ) = 0) :
    face.realization.sourceLength (row (strong := strong) (iface := iface) i)[k] = 0 := by
  refine sourceLength_eq_zero_of_forall_position_ne hk fun m hm ↦ ?_
  have h : position i m < position i m₀ := by omega
  have := position_lt_position_iff.mp h
  rw [Fin.lt_def, hFirst] at this
  omega

/-- After the last positive occurrence everything is contracted. -/
theorem sourceLength_eq_zero_of_position_last_lt {i : Fin p} {k : ℕ}
    (hk : k < (row (strong := strong) (iface := iface) i).length)
    (m₁ : Fin (positiveRow iface face i).length) (hlt : position i m₁ < k)
    (hLast : (m₁ : ℕ) + 1 = (positiveRow iface face i).length) :
    face.realization.sourceLength (row (strong := strong) (iface := iface) i)[k] = 0 := by
  refine sourceLength_eq_zero_of_forall_position_ne hk fun m hm ↦ ?_
  have h : position i m₁ < position i m := by omega
  have := position_lt_position_iff.mp h
  rw [Fin.lt_def] at this
  have := m.isLt
  omega

/-- Between two consecutive positive occurrences everything is contracted. -/
theorem sourceLength_eq_zero_of_position_lt_of_lt_position {i : Fin p} {k : ℕ}
    (hk : k < (row (strong := strong) (iface := iface) i).length)
    (m₀ m₁ : Fin (positiveRow iface face i).length)
    (hSucc : (m₀ : ℕ) + 1 = (m₁ : ℕ))
    (hlt₀ : position i m₀ < k) (hlt₁ : k < position i m₁) :
    face.realization.sourceLength (row (strong := strong) (iface := iface) i)[k] = 0 := by
  refine sourceLength_eq_zero_of_forall_position_ne hk fun m hm ↦ ?_
  have h₀ : position i m₀ < position i m := by omega
  have h₁ : position i m < position i m₁ := by omega
  have := position_lt_position_iff.mp h₀
  have := position_lt_position_iff.mp h₁
  rw [Fin.lt_def] at *
  omega

/-- The position of a refined slot in its row. -/
noncomputable def slotPosition (x : RefinedSlotIndex iface face) : ℕ :=
  position x.1 (positiveIndex x)

theorem slotPosition_lt (x : RefinedSlotIndex iface face) :
    slotPosition x < (row (strong := strong) (iface := iface) x.1).length :=
  position_lt x.1 (positiveIndex x)

theorem occurrence_eq_getElem (x : RefinedSlotIndex iface face) :
    occurrence x =
      (row (strong := strong) (iface := iface) x.1)[slotPosition x]'(slotPosition_lt x) :=
  (getElem_position x.1 (positiveIndex x)).symm

/-! ### The breakpoints, on the row -/

/-- A breakpoint of row `i` — the `m`-th internal core vertex the refinement
adds — as an index into the positive sublist: the positive occurrence it
follows. -/
def breakIndex (y : Σ i : Fin p, Fin (((segmentData iface face).segments i).length - 1)) :
    Fin (positiveRow iface face y.1).length :=
  ⟨(y.2 : ℕ), by
    have := y.2.isLt
    have hlen := segments_length (iface := iface) (face := face) y.1
    omega⟩

/-- and the positive occurrence it precedes. -/
def breakIndexSucc (y : Σ i : Fin p, Fin (((segmentData iface face).segments i).length - 1)) :
    Fin (positiveRow iface face y.1).length :=
  ⟨(y.2 : ℕ) + 1, by
    have := y.2.isLt
    have hlen := segments_length (iface := iface) (face := face) y.1
    omega⟩

@[simp] theorem breakIndex_val
    (y : Σ i : Fin p, Fin (((segmentData iface face).segments i).length - 1)) :
    ((breakIndex y : Fin _) : ℕ) = (y.2 : ℕ) := rfl

@[simp] theorem breakIndexSucc_val
    (y : Σ i : Fin p, Fin (((segmentData iface face).segments i).length - 1)) :
    ((breakIndexSucc y : Fin _) : ℕ) = (y.2 : ℕ) + 1 := rfl

/-- The position in its row of the positive occurrence a breakpoint follows. -/
noncomputable def breakPosition
    (y : Σ i : Fin p, Fin (((segmentData iface face).segments i).length - 1)) : ℕ :=
  position y.1 (breakIndex y)

/-- A breakpoint names an *interior* position of the walk: the positive
occurrence it precedes comes strictly later in the row. -/
theorem breakPosition_succ_lt
    (y : Σ i : Fin p, Fin (((segmentData iface face).segments i).length - 1)) :
    breakPosition y + 1 < (row (strong := strong) (iface := iface) y.1).length := by
  have h : position y.1 (breakIndex y) < position y.1 (breakIndexSucc y) :=
    position_lt_position_iff.mpr (by rw [Fin.lt_def]; simp)
  have := position_lt y.1 (breakIndexSucc y)
  unfold breakPosition
  omega

/-- The vertex the walk reaches after the positive occurrence a breakpoint
follows.  Its contraction class is the breakpoint's class. -/
noncomputable def breakVertex
    (y : Σ i : Fin p, Fin (((segmentData iface face).segments i).length - 1)) :
    candidate.datum.SourceVertex :=
  rowWalk strong iface y.1 (breakPosition y + 1)

/-! ### The canonical vertex map -/

/-- **The canonical map from refined core vertices to contraction classes.**
A stable core vertex goes to the class of the quotient-source vertex the
dictionary puts it on; the `m`-th breakpoint of row `i` goes to the class of
the vertex the oriented walk reaches after the `m`-th positive occurrence.
Nothing is chosen: once `vertexAt` is fixed, so is this map. -/
noncomputable def vertexClass (dict : RowDictionary strong spec iface)
    (topology : ClearedFace.SourceContractionTopology face) :
    RefinedVertex (segmentData iface face) → topology.degSpec.Class
  | Sum.inl v => classOf topology (dict.vertexAt v)
  | Sum.inr y => classOf topology (breakVertex y)

/-- **Only the contraction classes of `vertexAt` matter.**  Two dictionaries
agreeing on the class of every stable core vertex give the same canonical map,
so nothing in §4 uses the vertex-level equations `tail_eq` and `head_eq` beyond
their class-level shadow.  They are stated at vertex level only to match
`TraversalPresentation.CoreDictionary`. -/
theorem vertexClass_congr (dict dict' : RowDictionary strong spec iface)
    (topology : ClearedFace.SourceContractionTopology face)
    (hAgree : ∀ v : Fin n,
      classOf topology (dict.vertexAt v) = classOf topology (dict'.vertexAt v)) :
    vertexClass dict topology = vertexClass dict' topology := by
  funext v
  match v with
  | Sum.inl u => exact hAgree u
  | Sum.inr _ => rfl

/-- **Orientation is forced by injectivity.**  The stable core is loopless, so
an injective `vertexClass` separates the two ends of every row — which is
exactly the bit §2 shows a `StrongPresentation` leaves open. -/
theorem finish_ne_start_of_injective (dict : RowDictionary strong spec iface)
    {topology : ClearedFace.SourceContractionTopology face}
    (hInj : Function.Injective (vertexClass dict topology)) (i : Fin p) :
    strong.finish (iface.slot i) ≠ strong.start (iface.slot i) := by
  intro hEq
  refine spec.core_loopless i ?_
  have hHead : vertexClass dict topology
        (Sum.inl (spec.core.head i) : RefinedVertex (segmentData iface face)) =
      vertexClass dict topology (Sum.inl (spec.core.tail i)) := by
    show classOf topology (dict.vertexAt (spec.core.head i)) =
      classOf topology (dict.vertexAt (spec.core.tail i))
    rw [dict.head_eq i, dict.tail_eq i, hEq]
  exact (Sum.inl_injective (hInj hHead)).symm

/-- The orientation bit of every row, from injectivity. -/
theorem orient_of_injective (dict : RowDictionary strong spec iface)
    {topology : ClearedFace.SourceContractionTopology face}
    (hInj : Function.Injective (vertexClass dict topology)) (i : Fin p) :
    2 ≤ (row (strong := strong) (iface := iface) i).length ∨
      strong.finish (iface.slot i) ≠ strong.start (iface.slot i) :=
  Or.inr (finish_ne_start_of_injective dict hInj i)


/-! ### The two endpoints of a refined slot, named on the source -/

/-- The start of a refined slot is the walk vertex before its occurrence.  For
the first refined slot of a row the class of the stable tail is reached across
the contracted run at the start of the row; for a later one, across the
contracted run after the previous positive occurrence. -/
theorem vertexClass_segmentTailVertex (dict : RowDictionary strong spec iface)
    (topology : ClearedFace.SourceContractionTopology face)
    (x : RefinedSlotIndex iface face) :
    vertexClass dict topology (segmentTailVertex (segmentData iface face) x) =
      classOf topology (rowWalk strong iface x.1 (slotPosition x)) := by
  have hlen := segments_length (iface := iface) (face := face) x.1
  have hxlt := x.2.isLt
  unfold segmentTailVertex
  split_ifs with hzero
  · show classOf topology (dict.vertexAt (spec.core.tail x.1)) = _
    rw [dict.tail_eq x.1, ← rowWalk_zero (strong := strong) (iface := iface) x.1]
    refine classOf_rowWalk_eq_of_zero_run topology (Nat.zero_le _)
      (slotPosition_lt x).le fun k hk _ hkb ↦ ?_
    exact sourceLength_eq_zero_of_lt_position_zero hk (positiveIndex x) hkb hzero
  · have hm : (x.2 : ℕ) - 1 < ((segmentData iface face).segments x.1).length - 1 := by
      omega
    show classOf topology (breakVertex ⟨x.1, ⟨(x.2 : ℕ) - 1, hm⟩⟩) = _
    unfold breakVertex breakPosition
    dsimp only
    have hlt : position x.1 (breakIndex ⟨x.1, ⟨(x.2 : ℕ) - 1, hm⟩⟩) <
        position x.1 (positiveIndex x) := by
      refine position_lt_position_iff.mpr ?_
      rw [Fin.lt_def]
      show (x.2 : ℕ) - 1 < (x.2 : ℕ)
      omega
    refine classOf_rowWalk_eq_of_zero_run topology hlt (slotPosition_lt x).le
      fun k hk hak hkb ↦ ?_
    exact sourceLength_eq_zero_of_position_lt_of_lt_position hk
      (breakIndex ⟨x.1, ⟨(x.2 : ℕ) - 1, hm⟩⟩) (positiveIndex x)
      (show (x.2 : ℕ) - 1 + 1 = (x.2 : ℕ) by omega) (by omega) hkb

/-- and its end is the walk vertex after it.  For the last refined slot of a
row the class of the stable head is reached across the contracted run at the
end of the row. -/
theorem vertexClass_segmentHeadVertex (dict : RowDictionary strong spec iface)
    (topology : ClearedFace.SourceContractionTopology face)
    (hOrient : ∀ i : Fin p,
      2 ≤ (row (strong := strong) (iface := iface) i).length ∨
        strong.finish (iface.slot i) ≠ strong.start (iface.slot i))
    (x : RefinedSlotIndex iface face) :
    vertexClass dict topology (segmentHeadVertex (segmentData iface face) x) =
      classOf topology (rowWalk strong iface x.1 (slotPosition x + 1)) := by
  have hlen := segments_length (iface := iface) (face := face) x.1
  unfold segmentHeadVertex
  split_ifs with hlast
  · show classOf topology (dict.vertexAt (spec.core.head x.1)) = _
    rw [dict.head_eq x.1, ← rowWalk_length (hOrient x.1)]
    refine (classOf_rowWalk_eq_of_zero_run topology (slotPosition_lt x) le_rfl
      fun k hk hak _ ↦ ?_).symm
    refine sourceLength_eq_zero_of_position_last_lt hk (positiveIndex x) (by
      unfold slotPosition at hak; omega) ?_
    show (x.2 : ℕ) + 1 = _
    omega
  · rfl

/-! ### The orientation flag -/

/-- Whether the row traverses the occurrence carrying refined slot `x`
backwards, i.e. enters it at the second of its two named ends. -/
noncomputable def reversedAt (x : RefinedSlotIndex iface face) : Bool :=
  if (candidate.datum.sourceEnds (occurrence x)).1 =
      rowWalk strong iface x.1 (slotPosition x) then false else true

/-- **The first named end of the occurrence, located on the walk.** -/
theorem sourceEnds_occurrence_fst (x : RefinedSlotIndex iface face) :
    (candidate.datum.sourceEnds (occurrence x)).1 =
      rowWalk strong iface x.1
        (if reversedAt x then slotPosition x + 1 else slotPosition x) := by
  have hb := slotPosition_lt (strong := strong) (iface := iface) x
  by_cases hc : (candidate.datum.sourceEnds (occurrence x)).1 =
      rowWalk strong iface x.1 (slotPosition x)
  · rw [show reversedAt x = false from if_pos hc, if_neg (by simp)]
    exact hc
  · rw [show reversedAt x = true from if_neg hc, if_pos rfl,
      rowWalk_succ hb, ← occurrence_eq_getElem x]
    unfold otherEnd
    rw [if_neg hc]

/-- **and the second.** -/
theorem sourceEnds_occurrence_snd (x : RefinedSlotIndex iface face) :
    (candidate.datum.sourceEnds (occurrence x)).2 =
      rowWalk strong iface x.1
        (if reversedAt x then slotPosition x else slotPosition x + 1) := by
  have hb := slotPosition_lt (strong := strong) (iface := iface) x
  by_cases hc : (candidate.datum.sourceEnds (occurrence x)).1 =
      rowWalk strong iface x.1 (slotPosition x)
  · rw [show reversedAt x = false from if_pos hc, if_neg (by simp),
      rowWalk_succ hb, ← occurrence_eq_getElem x]
    unfold otherEnd
    rw [if_pos hc]
  · rw [show reversedAt x = true from if_neg hc, if_pos rfl]
    have hInc := rowWalk_incident (strong := strong) (iface := iface) hb
    rw [← occurrence_eq_getElem x] at hInc
    rcases hInc with hCase | hCase
    · exact absurd hCase hc
    · exact hCase


/-! ## 4.  The stable model -/

/-- Injectivity of the canonical map, read off a bijection onto the kept
classes. -/
theorem injective_of_bijOn (dict : RowDictionary strong spec iface)
    (topology : ClearedFace.SourceContractionTopology face)
    (hBij : Set.BijOn (vertexClass dict topology) Set.univ {c | topology.KeptClass c}) :
    Function.Injective (vertexClass dict topology) :=
  Set.injOn_univ.mp hBij.injOn

/-- **The stable model of the pruned contracted quotient source, constructed.**

`slotModel` and the three equations are *derived*: the positive sublists of
the rows enumerate the kept slots (`Decomposes`), and the oriented walk of §1
names the meeting vertex `StrongPresentation.chain` leaves existential, so
every endpoint equation holds on the nose with the orientation flag
`reversedAt`, the contracted runs being absorbed by
`classOf_rowWalk_eq_of_zero_run`.  The single hypothesis beyond the dictionary
is that the canonical `vertexClass` is a bijection onto the kept classes; §5
relates that to injectivity, exhaustion of the kept classes and `Spanning`. -/
noncomputable def sourceModel (dict : RowDictionary strong spec iface)
    (topology : ClearedFace.SourceContractionTopology face)
    (hBij : Set.BijOn (vertexClass dict topology) Set.univ {c | topology.KeptClass c}) :
    SourceModel iface topology where
  slotModel := slotEquiv iface topology
  vertexModel := Equiv.ofBijective
    (fun v ↦ ⟨vertexClass dict topology v, hBij.mapsTo (Set.mem_univ v)⟩)
    ⟨fun a b hab ↦ injective_of_bijOn dict topology hBij (congrArg Subtype.val hab),
      fun c ↦ by
        obtain ⟨v, -, hv⟩ := hBij.surjOn c.property
        exact ⟨v, Subtype.ext hv⟩⟩
  reversed := reversedAt
  length_eq := fun x ↦ by
    rw [degSpec_length, sourceEdgeAt_slotEquiv]
    exact (segments_getD x).symm
  tail_eq := fun x ↦ by
    rw [rep_core_tail, sourceEdgeAt_slotEquiv, sourceEnds_occurrence_fst x]
    show _ = (vertexClass dict topology _).val
    split_ifs with hr
    · rw [vertexClass_segmentHeadVertex dict topology
        (orient_of_injective dict (injective_of_bijOn dict topology hBij)) x]
    · rw [vertexClass_segmentTailVertex dict topology x]
  head_eq := fun x ↦ by
    rw [rep_core_head, sourceEdgeAt_slotEquiv, sourceEnds_occurrence_snd x]
    show _ = (vertexClass dict topology _).val
    split_ifs with hr
    · rw [vertexClass_segmentTailVertex dict topology x]
    · rw [vertexClass_segmentHeadVertex dict topology
        (orient_of_injective dict (injective_of_bijOn dict topology hBij)) x]

/-! ## 5.  What the bijectivity hypothesis is -/

/-- A row end meets the first (or last) occurrence of its row, which
survives: its non-dangling valency is positive. -/
theorem nonDanglingValency_start_pos (i : Fin p) :
    0 < nonDanglingValency candidate.datum (strong.start (iface.slot i)) := by
  have hpos : 0 < (row (strong := strong) (iface := iface) i).length :=
    List.length_pos_of_ne_nil (strong.path_ne_nil _)
  exact ClearedFace.SourceContractionTopology.nonDanglingValency_pos_of_incident
    (row_survives i _ (List.getElem_mem hpos))
    (row_head_isPathEnd (strong := strong) (iface := iface) i hpos).1

theorem nonDanglingValency_finish_pos (i : Fin p) :
    0 < nonDanglingValency candidate.datum (strong.finish (iface.slot i)) := by
  have hpos : 0 < (row (strong := strong) (iface := iface) i).length :=
    List.length_pos_of_ne_nil (strong.path_ne_nil _)
  exact ClearedFace.SourceContractionTopology.nonDanglingValency_pos_of_incident
    (row_survives i _ (List.getElem_mem (show
      (row (strong := strong) (iface := iface) i).length - 1 <
        (row (strong := strong) (iface := iface) i).length by omega)))
    (row_getLast_isPathEnd (strong := strong) (iface := iface) i hpos).1

/-- A breakpoint sits at an interior walk vertex, of surviving valency two. -/
theorem nonDanglingValency_breakVertex
    (y : Σ i : Fin p, Fin (((segmentData iface face).segments i).length - 1)) :
    nonDanglingValency candidate.datum (breakVertex y) = 2 :=
  walkVertex_succ_valency (row_nodup y.1) (row_survives y.1) (row_chain y.1)
    (row_head_isPathEnd y.1) (breakPosition_succ_lt y)

/-- **Every refined core vertex lands in a kept class**, once the placement is
spanning: a stable core vertex sits at a row end, a breakpoint at an interior
walk vertex, and both meet a surviving occurrence. -/
theorem mapsTo_keptClass_of_spanning (dict : RowDictionary strong spec iface)
    (topology : ClearedFace.SourceContractionTopology face)
    (hSpanning : StrongRefinement.Spanning dict) :
    Set.MapsTo (vertexClass dict topology) Set.univ {c | topology.KeptClass c} := by
  intro v _
  match v with
  | Sum.inl w =>
      refine ⟨dict.vertexAt w, rfl, ?_⟩
      rcases hSpanning w with ⟨i, hi⟩ | ⟨i, hi⟩
      · rw [show dict.vertexAt w = strong.start (iface.slot i) from hi]
        exact nonDanglingValency_start_pos i
      · rw [show dict.vertexAt w = strong.finish (iface.slot i) from hi]
        exact nonDanglingValency_finish_pos i
  | Sum.inr y =>
      refine ⟨breakVertex y, rfl, ?_⟩
      rw [nonDanglingValency_breakVertex y]
      omega

/-- The `LaplacianEquiv` that `InputRefinementData.inputRefinement` needs,
from a row dictionary: onto the pruned contracted spec. -/
noncomputable def laplacianEquiv (dict : RowDictionary strong spec iface)
    (topology : ClearedFace.SourceContractionTopology face)
    (hBij : Set.BijOn (vertexClass dict topology) Set.univ {c | topology.KeptClass c}) :
    LaplacianEquiv (refinedSpec iface face).graph
      (topology.prunedSpec (sourceModel dict topology hBij).kept).graph :=
  (sourceModel dict topology hBij).laplacianEquiv

/-- and the closed-face input refinement receipt. -/
noncomputable def inputRefinement (dict : RowDictionary strong spec iface)
    (topology : ClearedFace.SourceContractionTopology face)
    (hBij : Set.BijOn (vertexClass dict topology) Set.univ {c | topology.KeptClass c}) :
    ClearedFace.InputRefinement spec topology :=
  (sourceModel dict topology hBij).inputRefinement

/-! ## 6.  The fields of the dictionary, measured -/

/-- A row dictionary is a `TraversalPresentation.CoreDictionary`:
`RowDictionary` is an abbreviation of it, so this is the identity.  It is kept
as a named coercion for the callers that read `Faithful` and `Spanning`
through it. -/
abbrev coreDictionary {F : Finset (Fin p)}
    {iface : InputInterface spec strong.toPresentation coordinates F}
    (dict : RowDictionary strong spec iface) :
    TraversalPresentation.CoreDictionary spec strong iface :=
  dict

end RowDictionary


end Model


end DraismaVargas.LocalCases.OrientedTraversal
