module

public import DraismaVargas.LocalCases.W4StableSource

@[expose] public section

/-!
# Length-matrix presentations that decompose the pruned source

`GluingDatum.LengthMatrixPresentation`
(`DraismaVargas.Infrastructure.LengthMatrix`) stores a square labelling

```
targetEdge : coordinate ≃ target.edges
path       : coordinate → List data.SourceEdge
```

and **nothing else**.  In particular nothing there ties the path family to the
source graph: a presentation is free to list one source occurrence in two
different rows, to repeat it inside a single row, to omit it altogether, or to
carry an occurrence that pruning has already deleted.  That freedom is exactly
what blocks the `relabeling` receipt of
`Candidate.ClearedFace.InputRefinement`, which must identify the contracted
source with the requested metric subdivided at the block boundaries of the
cover; `DraismaVargas.LocalCases.ZeroFreeTerminalFace` therefore takes that
receipt as a hypothesis.

Rather than add a field to a structure that several constructors build and many
files consume, this module states the condition separately:

* `Decomposes presentation` says that the rows of the presentation **partition
  the surviving source occurrences** — each row is duplicate-free, distinct
  rows are disjoint, every non-dangling occurrence appears in some row, and no
  dangling occurrence appears anywhere.

* `stableLengthMatrixLabelling_decomposes` proves it for the honest stable
  presentation of `W4StableSource.StableLengthMatrixLabelling`, where it holds
  by construction: that presentation's row `r` is literally the list of all
  surviving occurrences whose stable-path class is labelled `r`.

* `card_nonDanglingEdges_eq_sum_length`, `card_surviving_eq_sum_length`,
  `exists_unique_row`, `biUnion_toFinset_eq_nonDanglingEdges` and
  `sum_path_eq_nonDanglingEdges_val` are the bookkeeping consequences a later
  refinement argument consumes: the total number of surviving occurrences is
  the sum of the row lengths, each surviving occurrence has exactly one row,
  and the rows assemble — as a finset and as a multiset — into the pruned
  occurrence set.

Everything here is occurrence-level bookkeeping.  `Decomposes` says the rows
partition the pruned source as a *set of edge occurrences*; it deliberately
says nothing about the order inside a row, and hence nothing about consecutive
occurrences sharing a source vertex.  See the note at the end of the file.
-/

namespace DraismaVargas.LocalCases.PresentationDecomposition

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.W4StableSource

variable {target : CFGraph} {degree : ℕ}

/-- The rows of `presentation` partition the surviving source occurrences.

This is the occurrence-level statement that the presentation's paths decompose
the pruned source: no row repeats an occurrence, two different rows share no
occurrence, every non-dangling occurrence is listed by some row, and every
dangling occurrence is listed by none. -/
structure Decomposes {data : GluingDatum target degree} {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate]
    (presentation : data.LengthMatrixPresentation coordinate) : Prop where
  /-- No row lists a source occurrence twice. -/
  nodup : ∀ row, (presentation.path row).Nodup
  /-- Two different rows never share a source occurrence. -/
  disjoint : ∀ row row', row ≠ row' →
    ∀ edge, edge ∈ presentation.path row → edge ∉ presentation.path row'
  /-- Every surviving source occurrence is listed by some row. -/
  surviving_mem : ∀ edge : data.SourceEdge, ¬ IsDangling data edge →
    ∃ row, edge ∈ presentation.path row
  /-- No row lists a deleted source occurrence. -/
  dangling_not_mem : ∀ edge : data.SourceEdge, IsDangling data edge →
    ∀ row, edge ∉ presentation.path row

namespace Decomposes

variable {data : GluingDatum target degree} {coordinate : Type*}
  [Fintype coordinate] [DecidableEq coordinate]
  {presentation : data.LengthMatrixPresentation coordinate}

/-- A listed occurrence survives pruning. -/
theorem not_isDangling_of_mem (h : Decomposes presentation) {row : coordinate}
    {edge : data.SourceEdge} (hEdge : edge ∈ presentation.path row) :
    ¬ IsDangling data edge := fun hDangling ↦
  h.dangling_not_mem edge hDangling row hEdge

/-- Each surviving source occurrence lies in exactly one row. -/
theorem exists_unique_row (h : Decomposes presentation)
    {edge : data.SourceEdge} (hEdge : ¬ IsDangling data edge) :
    ∃! row, edge ∈ presentation.path row := by
  obtain ⟨row, hRow⟩ := h.surviving_mem edge hEdge
  refine ⟨row, hRow, fun row' hRow' ↦ ?_⟩
  by_contra hNe
  exact h.disjoint row' row hNe edge hRow' hRow

/-- Discarding the order of a row loses nothing: its finset has as many
elements as the list has entries. -/
theorem card_toFinset (h : Decomposes presentation) (row : coordinate) :
    (presentation.path row).toFinset.card = (presentation.path row).length :=
  List.toFinset_card_of_nodup (h.nodup row)

/-- The row finsets are pairwise disjoint. -/
theorem pairwiseDisjoint_toFinset (h : Decomposes presentation) :
    ((Finset.univ : Finset coordinate) : Set coordinate).PairwiseDisjoint
      (fun row ↦ (presentation.path row).toFinset) := by
  intro row _ row' _ hNe
  refine Finset.disjoint_left.mpr fun edge hEdge hEdge' ↦ ?_
  exact h.disjoint row row' hNe edge (List.mem_toFinset.mp hEdge)
    (List.mem_toFinset.mp hEdge')

/-- The rows cover exactly the occurrence finset left after pruning. -/
theorem biUnion_toFinset_eq_nonDanglingEdges (h : Decomposes presentation) :
    (Finset.univ : Finset coordinate).biUnion
        (fun row ↦ (presentation.path row).toFinset)
      = nonDanglingEdges data := by
  ext edge
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, List.mem_toFinset,
    mem_nonDanglingEdges]
  exact ⟨fun hRow ↦ h.not_isDangling_of_mem hRow.choose_spec,
    h.surviving_mem edge⟩

/-- The pruned source has exactly as many edge occurrences as the rows have
entries in total. -/
theorem card_nonDanglingEdges_eq_sum_length (h : Decomposes presentation) :
    (nonDanglingEdges data).card
      = ∑ row : coordinate, (presentation.path row).length := by
  rw [← biUnion_toFinset_eq_nonDanglingEdges h,
    Finset.card_biUnion (pairwiseDisjoint_toFinset h)]
  exact Finset.sum_congr rfl fun row _ ↦ card_toFinset h row

open scoped Classical in
/-- The same count, written with the literal surviving-occurrence filter. -/
theorem card_surviving_eq_sum_length (h : Decomposes presentation) :
    (Finset.univ.filter fun edge : data.SourceEdge ↦
        ¬ IsDangling data edge).card
      = ∑ row : coordinate, (presentation.path row).length := by
  have hFilter :
      (Finset.univ.filter fun edge : data.SourceEdge ↦ ¬ IsDangling data edge)
        = nonDanglingEdges data := by
    ext edge
    simp
  rw [hFilter, card_nonDanglingEdges_eq_sum_length h]

/-- The multiset form: the disjoint union of the rows is the multiset of
surviving source occurrences. -/
theorem sum_path_eq_nonDanglingEdges_val (h : Decomposes presentation) :
    (∑ row : coordinate, (presentation.path row : Multiset data.SourceEdge))
      = (nonDanglingEdges data).val := by
  have hUnion : (Finset.univ : Finset coordinate).disjiUnion
      (fun row ↦ (presentation.path row).toFinset)
      (pairwiseDisjoint_toFinset h) = nonDanglingEdges data := by
    rw [Finset.disjiUnion_eq_biUnion]
    exact biUnion_toFinset_eq_nonDanglingEdges h
  calc (∑ row : coordinate, (presentation.path row : Multiset data.SourceEdge))
      = ∑ row : coordinate, ((presentation.path row).toFinset).val := by
        refine Finset.sum_congr rfl fun row _ ↦ ?_
        rw [List.toFinset_val, (h.nodup row).dedup]
    _ = ((Finset.univ : Finset coordinate).disjiUnion
          (fun row ↦ (presentation.path row).toFinset)
          (pairwiseDisjoint_toFinset h)).val := rfl
    _ = (nonDanglingEdges data).val := by rw [hUnion]

end Decomposes

/-! ## The honest stable presentation decomposes the pruned source -/

section Stable

variable {data : GluingDatum target degree} {coordinate : Type*}
  [Fintype coordinate] [DecidableEq coordinate]

omit [Fintype coordinate] in
/-- Membership in a row of the induced stable presentation is membership in the
labelled stable-path class. -/
theorem mem_presentation_path_iff
    (labelling : StableLengthMatrixLabelling data coordinate)
    (row : coordinate) (edge : data.SourceEdge) :
    edge ∈ labelling.presentation.path row ↔
      ∃ hSurvives : ¬ IsDangling data edge,
        labelling.row
          (NonDanglingEdge.stablePath
            (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = row :=
  labelling.mem_path_iff row edge

/-- The honest stable-source presentation decomposes the pruned source: its
rows enumerate each surviving occurrence exactly once, in the row labelling its
stable path, and list no deleted occurrence. -/
theorem stableLengthMatrixLabelling_decomposes
    (labelling : StableLengthMatrixLabelling data coordinate) :
    Decomposes labelling.presentation := by
  classical
  refine ⟨fun row ↦ ?_, fun row row' hNe edge hMem hMem' ↦ ?_,
    fun edge hSurvives ↦ ?_, fun edge hDangling row hMem ↦ ?_⟩
  · have hPath : labelling.presentation.path row = labelling.path row := rfl
    rw [hPath]
    unfold StableLengthMatrixLabelling.path
    exact List.Nodup.filter _ (Finset.nodup_toList _)
  · obtain ⟨hSurvives, hRow⟩ := (mem_presentation_path_iff labelling row edge).mp hMem
    obtain ⟨hSurvives', hRow'⟩ :=
      (mem_presentation_path_iff labelling row' edge).mp hMem'
    exact hNe (hRow.symm.trans hRow')
  · exact ⟨labelling.row (NonDanglingEdge.stablePath ⟨edge, hSurvives⟩),
      (mem_presentation_path_iff labelling _ edge).mpr ⟨hSurvives, rfl⟩⟩
  · exact ((mem_presentation_path_iff labelling row edge).mp hMem).choose hDangling

/-- Specialisation of the occurrence count to the honest stable presentation. -/
theorem card_nonDanglingEdges_eq_sum_stable_length
    (labelling : StableLengthMatrixLabelling data coordinate) :
    (nonDanglingEdges data).card
      = ∑ row : coordinate, (labelling.presentation.path row).length :=
  (stableLengthMatrixLabelling_decomposes labelling).card_nonDanglingEdges_eq_sum_length

end Stable

/-!
## What `Decomposes` does and does not give

`Decomposes` is an **occurrence-level partition** statement.  It supplies the
bookkeeping a refinement argument needs to know that nothing is double counted
or dropped, and in particular it makes `Decomposes.exists_unique_row` available
as the row-assignment function on surviving occurrences.

It is deliberately silent about three further things, none of which is needed
for counting but all of which a genuine path-splitting argument would use:

* **Connectivity and order.** Nothing says that consecutive entries of
  `presentation.path row` meet at a source vertex, nor that the list is ordered
  along the path at all.  For the honest stable presentation the row is
  produced by filtering `Finset.univ.toList`, so its order is the arbitrary
  enumeration order of `data.SourceEdge`, not a traversal order.
* **Endpoints.** Nothing says a row starts and ends at a vertex of
  non-dangling valency different from two, i.e. that the row is a *maximal*
  stable path rather than a sub-path.
* **Compatibility with `targetEdge`.** Nothing relates the target occurrences
  under the entries of a row to the coordinate labelling the row.

Consequently `Decomposes` alone is *not* enough to build the
`Candidate.ClearedFace.InputRefinement` receipt.  That field is a
`IteratedSplitRefinement.RefinementPresentation`, i.e. a `CanonicalSplitChain` of
`OrderedPathSplit`s followed by a `relabeling : LaplacianEquiv`, and an
`OrderedPathSplit` cuts one target slot into an **ordered list of segments**.
Matching a row against such a list needs the row itself to be ordered along the
source path.  The missing hypothesis is therefore an ordering field of the
shape

```
chain : ∀ row, (presentation.path row).Chain' fun first second ↦
  ∃ vertex : data.SourceVertex,
    Incident data first vertex ∧ Incident data second vertex ∧
      nonDanglingValency data vertex = 2
```

(together with an endpoint condition on the two ends of the list).  That is a
genuine strengthening, and it is *not* provable for
`StableLengthMatrixLabelling.path` as defined: that definition filters a
global enumeration of `data.SourceEdge` rather than traversing the path, so the
order of a row of three or more occurrences is whatever the enumeration happens
to produce.  Supplying the field therefore means replacing the honest
presentation's `path` by an actual traversal, which is not a consequence of
this file: `TraversalPresentation.StrongPresentation` adds such a `chain` field
together with endpoint conditions, and `TraversalPresentation.ofLabelling`
realizes it by traversing the stable paths.
-/

end DraismaVargas.LocalCases.PresentationDecomposition
