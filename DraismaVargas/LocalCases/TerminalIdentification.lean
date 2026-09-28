import DraismaVargas.LocalCases.OuterWalk
import DraismaVargas.LocalCases.CertifiedPencil
import DraismaVargas.LocalCases.RequestedExpandedEndpoints
import DraismaVargas.LocalCases.StrongRefinement

/-!
# The terminal identification from a tracked pencil at the requested core

**Source.**  Draisma–Vargas Part I, arXiv:1909.12924, the terminal step of the atlas march (the
stable source `H(M)`, and its occurrence-based row labels coming from
compatible edge labellings).

**What is proved.**  A tracked march state whose ambient row-labelled graph is
isomorphic to the requested cubic core carries a certified pencil:

* `carriesCertifiedPencil_of_tracked` -- from `InteriorGraphTracking.Tracks`
  under the state's own payload binder, an isomorphism `endpoint` of the
  ambient graph onto `CubicCoreDarts.ofCore spec.core`, a slot equivalence
  `slots` reading the row labels as core slots, and the endpoint vector read
  through `slots` (with the expansion forest `F` where it vanishes), it
  produces `CertifiedPencil.CarriesCertifiedPencil` -- the strong presentation,
  the source-genus certificate, the `InputRefinementData.InputInterface`, the
  three-field `OrientedTraversal.RowDictionary` and both of
  `StrongRefinement.Faithful` and `StrongRefinement.Spanning`.
* `carriesCertifiedPencil_of_tracked_expanded` -- the same, with the endpoint
  vector written as `RequestedExpandedEndpoints.expandedFinish`, the shape
  `RetainedIndexProducer.exists_subdivisionPencil_of_transport` takes; and
* `hT05_of_tracked` -- the same statement at the empty forest, at any terminal
  tracked state over the requested core, which is what the outer walk
  (`OuterWalk.exists_terminal_of_chain`) produces.

The composition with the outer walk -- the explicit subdivision pencil from the
walk's `interior` and `link` hypotheses alone -- is carried out in
`StatementFromLink`.

**The mathematical content, and why `TraversalPresentation.ofLabelling` is not
the producer used.**  A `RowDictionary` must send `spec.core.tail i` to the
vertex the displaying row *starts* at and `spec.core.head i` to the vertex it
*finishes* at, and `StrongRefinement.Faithful` then forces those two vertices
to be distinct whenever the core slot is not a loop.  The producer
`TraversalPresentation.ofLabelling` chooses its `finish` field by
`Exists.choose` on `exists_isPathEnd_getLast_orderedPath`, whose statement
constrains the chosen vertex only to be *a* path end of the last occurrence:
for a row of one occurrence with two branch ends nothing in that statement
prevents the choice from returning the row's own start, and no isomorphism of
dart graphs can repair an orientation that the presentation has already
collapsed.  Sections 1-3 replace the choice by the honest far end:

* §1 `exists_getLast_isPathEnd_ne` strengthens
  `TraversalPresentation.exists_isPathEnd_getLast` by recording that the
  terminal (occurrence, vertex) pair of a traversal differs from the pair it
  started at -- in the stopping case because the source is loopless
  (`otherEnd_ne`), in the stepping case because the traversal never repeats an
  occurrence (`traverse_nodup_notMem`).
* §2 `getLast_isPathEnd_opposite` identifies that far end: the traversal
  started at a dart of `StableSourceDarts.ofDatum` ends at the **opposite**
  dart of the same stable row, by the uniqueness in
  `StableSourceDarts.exists_unique_other`.
* §3 `orientedStrong` is the resulting producer: given any family
  `tailDart : coordinate → Dart data` of darts labelling the rows, it builds a
  `TraversalPresentation.StrongPresentation` whose row `c` is the traversal
  from `tailDart c`, whose `start` is that dart's source vertex and whose
  `finish` is the opposite dart's.  `matrix_orientedStrong` records that the
  length matrix is untouched (`orientedPresentation_perm`: the rows are
  reorderings), so the strong presentation still displays the chart matrix.

§4 then takes `tailDart c` to be the dart the core's *tail* end of slot
`slots c` names, through `tracking.iso.trans endpoint`; `tail_eq` and `head_eq`
become the two halves of `Iso.vert_map`, `Faithful` is injectivity of
`Iso.vtx.symm`, and `Spanning` is cubicity of the core (`card_fibre`).

**What is not proved here.**  Nothing about the march itself: the tracked
state, its terminal-ness, the graph isomorphism onto the core and the slot map
are hypotheses, supplied by `OuterWalk.exists_terminal_of_chain`.  The
non-cubic request is covered to the extent that
`carriesCertifiedPencil_of_tracked` is stated at a general expansion forest
`F`; the transport of that statement to an arbitrary connected request is
`StatementFromLink.nonempty_subdivisionPencil_of_certified_expansion`, whose
one further input, `StatementFromLink.RetainedRelabeling` at the forest, is
supplied by `RetainedRelabeling.retainedRelabeling_of_cutRelabeling`.

**Consumers.**  `StatementFromLink` and `RequestedExpandedEndpoints`, and
through them `DraismaVargas.Statement`.
-/

namespace DraismaVargas.LocalCases.TerminalIdentification

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.NonDanglingValency
open DraismaVargas.LocalCases.PresentationDecomposition
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.StablePathCount
open DraismaVargas.LocalCases.StableSourceDarts
open DraismaVargas.LocalCases.TraversalPresentation
open DraismaVargas.LocalCases.W4StableSource

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}

/-! ## 1.  The far end of a traversal, identified -/

/-- **The far end of a traversal is a genuinely new dart.** -/
theorem exists_getLast_isPathEnd_ne {visited : Finset data.SourceEdge}
    {edge : data.SourceEdge} {vertex : data.SourceVertex}
    (hInv : TraverseInvariant data visited edge vertex) :
    ∃ (finish : data.SourceVertex) (last : data.SourceEdge),
      (traverse data visited edge vertex).getLast? = some last ∧
        IsPathEnd data last finish ∧ (last ≠ edge ∨ finish ≠ vertex) := by
  revert hInv
  refine traverse_rec (motive := fun visited edge vertex ↦
    TraverseInvariant data visited edge vertex →
      ∃ (finish : data.SourceVertex) (last : data.SourceEdge),
        (traverse data visited edge vertex).getLast? = some last ∧
          IsPathEnd data last finish ∧ (last ≠ edge ∨ finish ≠ vertex)) ?_ ?_ ?_
    visited edge vertex
  · intro visited edge _ hVisited hInv
    exact absurd hVisited hInv.1
  · intro visited edge vertex hVisited hValency _
    refine ⟨otherEnd data edge vertex, edge, ?_, ?_, Or.inr (otherEnd_ne data edge vertex)⟩
    · rw [traverse_of_valency_ne data hVisited hValency]
      simp
    · exact ⟨incident_otherEnd data edge vertex, hValency⟩
  · intro visited edge vertex hVisited hValency ih hInv
    obtain ⟨finish, last, hLast, hEnd, -⟩ := ih (traverseInvariant_step hInv hValency)
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
    refine ⟨finish, last, ?_, hEnd, Or.inl ?_⟩
    · rw [traverse_of_valency_eq data hVisited hValency, hCons,
        List.getLast?_cons_cons, ← hCons]
      exact hLast
    · have hMem : last ∈ traverse data (insert edge visited)
          (stepEdge data hValency edge) (otherEnd data edge vertex) :=
        List.mem_of_getLast? hLast
      have hNot := (traverse_nodup_notMem data (insert edge visited)
        (stepEdge data hValency edge) (otherEnd data edge vertex)).2 last hMem
      intro hEq
      exact hNot (Finset.mem_insert.mpr (Or.inl hEq))

/-! ## 2.  The traversal from a dart ends at the opposite dart -/

/-- A dart is a path end of its own occurrence. -/
theorem isPathEnd_dart (d : Dart data) : IsPathEnd data d.2.1.1 d.1.1 :=
  ⟨d.2.2, by have h := d.1.2; omega⟩

/-- **The far end of the traversal started at a dart is the opposite dart's
vertex.** -/
theorem getLast_isPathEnd_opposite (hConnected : data.Connected)
    (hEnds : HasPathEnds data) (d : Dart data) :
    ∀ last ∈ (traverse data ∅ d.2.1.1 d.1.1).getLast?,
      IsPathEnd data last (StableSourceDarts.opposite data hConnected hEnds d).1.1 := by
  obtain ⟨finish, last, hLast, hEnd, hNe⟩ :=
    exists_getLast_isPathEnd_ne (traverseInvariant_empty d.2.1.2 (isPathEnd_dart d))
  have hMem : last ∈ traverse data ∅ d.2.1.1 d.1.1 := List.mem_of_getLast? hLast
  obtain ⟨hSurv, hPath⟩ := traverse_stablePath data ∅ d.2.1.1 d.1.1 d.2.1.2 last hMem
  have hPos : 0 < nonDanglingValency data finish := by
    rw [← card_incidentEdges data finish]
    exact Finset.card_pos.mpr ⟨⟨last, hSurv⟩,
      (mem_incidentEdges data finish ⟨last, hSurv⟩).mpr hEnd.1⟩
  have hBranch : 3 ≤ nonDanglingValency data finish := by
    have h1 := nonDanglingValency_ne_one data hConnected finish
    have h2 := hEnd.2
    omega
  have hRowF : row data (⟨⟨finish, hBranch⟩, ⟨⟨last, hSurv⟩, hEnd.1⟩⟩ : Dart data) =
      row data d := hPath
  have hNeF : (⟨⟨finish, hBranch⟩, ⟨⟨last, hSurv⟩, hEnd.1⟩⟩ : Dart data) ≠ d := by
    rcases hNe with hCase | hCase
    · exact fun hEq ↦ hCase (congrArg (fun x : Dart data ↦ x.2.1.1) hEq)
    · exact fun hEq ↦ hCase (congrArg (fun x : Dart data ↦ x.1.1) hEq)
  have hOpp : (⟨⟨finish, hBranch⟩, ⟨⟨last, hSurv⟩, hEnd.1⟩⟩ : Dart data) =
      StableSourceDarts.opposite data hConnected hEnds d :=
    opposite_eq_of_row_eq data hConnected hEnds hRowF hNeF
  intro last' hLast'
  rw [hLast, Option.mem_def, Option.some_inj] at hLast'
  subst hLast'
  rw [← hOpp]
  exact hEnd

/-! ## 3.  The strong presentation oriented by a family of darts -/

section Oriented

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- The length-matrix presentation whose row `c` is the traversal of the stable
path of `c` started at the prescribed dart `tailDart c`. -/
noncomputable def orientedPresentation
    (fd : FullDimensionalSourcePresentation data coordinate)
    (tailDart : coordinate → Dart data) : data.LengthMatrixPresentation coordinate where
  targetEdge := fd.labelling.targetEdge
  path := fun c ↦ traverse data ∅ (tailDart c).2.1.1 (tailDart c).1.1

@[simp] theorem orientedPresentation_path
    (fd : FullDimensionalSourcePresentation data coordinate)
    (tailDart : coordinate → Dart data) (c : coordinate) :
    (orientedPresentation fd tailDart).path c =
      traverse data ∅ (tailDart c).2.1.1 (tailDart c).1.1 := rfl

/-- The row `c` of the oriented presentation lists exactly the surviving
occurrences the labelling assigns to `c`. -/
theorem mem_orientedPresentation_path_iff
    (fd : FullDimensionalSourcePresentation data coordinate)
    (tailDart : coordinate → Dart data)
    (hTail : ∀ c, fd.labelling.row (row data (tailDart c)) = c)
    (c : coordinate) (edge : data.SourceEdge) :
    edge ∈ (orientedPresentation fd tailDart).path c ↔
      ∃ hSurvives : ¬ IsDangling data edge,
        fd.labelling.row (NonDanglingEdge.stablePath
          (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = c := by
  rw [orientedPresentation_path]
  constructor
  · intro hMem
    obtain ⟨hSurvives, hPath⟩ := traverse_stablePath data ∅ (tailDart c).2.1.1
      (tailDart c).1.1 (tailDart c).2.1.2 edge hMem
    exact ⟨hSurvives, hPath ▸ hTail c⟩
  · rintro ⟨hSurvives, hRow⟩
    refine mem_traverse_of_stablePath_eq data (isPathEnd_dart (tailDart c))
      ⟨edge, hSurvives⟩ ?_
    exact fd.labelling.row.injective (hRow.trans (hTail c).symm)

/-- Each row of the oriented presentation is a reordering of the honest row. -/
theorem orientedPresentation_perm
    (fd : FullDimensionalSourcePresentation data coordinate)
    (tailDart : coordinate → Dart data)
    (hTail : ∀ c, fd.labelling.row (row data (tailDart c)) = c) (c : coordinate) :
    ((orientedPresentation fd tailDart).path c).Perm (fd.labelling.path c) := by
  refine (List.perm_ext_iff_of_nodup
    ((traverse_nodup_notMem data ∅ (tailDart c).2.1.1 (tailDart c).1.1).1)
    (fd.labelling.path_nodup c)).mpr ?_
  intro edge
  exact (mem_orientedPresentation_path_iff fd tailDart hTail c edge).trans
    (StableLengthMatrixLabelling.mem_path_iff fd.labelling c edge).symm

/-- **Reorienting the rows leaves the length matrix untouched.** -/
theorem matrix_orientedPresentation
    (fd : FullDimensionalSourcePresentation data coordinate)
    (tailDart : coordinate → Dart data)
    (hTail : ∀ c, fd.labelling.row (row data (tailDart c)) = c) :
    GluingDatum.LengthMatrixPresentation.matrix (orientedPresentation fd tailDart) =
      GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation := by
  funext c column
  exact ((orientedPresentation_perm fd tailDart hTail c).map
    (fun edge ↦ GluingDatum.LengthMatrixPresentation.coefficient
      fd.labelling.presentation edge column)).sum_eq

/-- **The oriented strong presentation.**  Same matrix as the honest
full-dimensional labelling, but every row is traversed from a prescribed dart,
so its two named ends are the vertices of that dart and of its opposite. -/
noncomputable def orientedStrong
    (fd : FullDimensionalSourcePresentation data coordinate)
    (tailDart : coordinate → Dart data)
    (hTail : ∀ c, fd.labelling.row (row data (tailDart c)) = c) :
    StrongPresentation data coordinate where
  toPresentation := orientedPresentation fd tailDart
  decomposes :=
    { nodup := fun c ↦ (traverse_nodup_notMem data ∅ (tailDart c).2.1.1 (tailDart c).1.1).1
      disjoint := fun c c' hNe edge hMem hMem' ↦ by
        obtain ⟨_, hRow⟩ := (mem_orientedPresentation_path_iff fd tailDart hTail c edge).mp hMem
        obtain ⟨_, hRow'⟩ :=
          (mem_orientedPresentation_path_iff fd tailDart hTail c' edge).mp hMem'
        exact hNe (hRow.symm.trans hRow')
      surviving_mem := fun edge hSurvives ↦
        ⟨fd.labelling.row (NonDanglingEdge.stablePath ⟨edge, hSurvives⟩),
          (mem_orientedPresentation_path_iff fd tailDart hTail _ edge).mpr ⟨hSurvives, rfl⟩⟩
      dangling_not_mem := fun edge hDangling c hMem ↦
        ((mem_orientedPresentation_path_iff fd tailDart hTail c edge).mp hMem).choose
          hDangling }
  chain c := traverse_chain data ∅ (tailDart c).2.1.1 (tailDart c).1.1
  start c := (tailDart c).1.1
  finish c := (StableSourceDarts.opposite data fd.connected fd.pathEnds (tailDart c)).1.1
  head_isPathEnd c edge hEdge := by
    rw [orientedPresentation_path, traverse_head?_eq_some data ∅ (tailDart c).2.1.1
      (tailDart c).1.1 (by simp), Option.mem_def, Option.some_inj] at hEdge
    exact hEdge ▸ isPathEnd_dart (tailDart c)
  getLast_isPathEnd c :=
    getLast_isPathEnd_opposite fd.connected fd.pathEnds (tailDart c)
  path_ne_nil c := by
    intro hNil
    have hHead := traverse_head?_eq_some data ∅ (tailDart c).2.1.1 (tailDart c).1.1 (by simp)
    rw [orientedPresentation_path] at hNil
    rw [hNil] at hHead
    simp at hHead

@[simp] theorem orientedStrong_toPresentation
    (fd : FullDimensionalSourcePresentation data coordinate)
    (tailDart : coordinate → Dart data)
    (hTail : ∀ c, fd.labelling.row (row data (tailDart c)) = c) :
    (orientedStrong fd tailDart hTail).toPresentation =
      orientedPresentation fd tailDart := rfl

@[simp] theorem orientedStrong_start
    (fd : FullDimensionalSourcePresentation data coordinate)
    (tailDart : coordinate → Dart data)
    (hTail : ∀ c, fd.labelling.row (row data (tailDart c)) = c) (c : coordinate) :
    (orientedStrong fd tailDart hTail).start c = (tailDart c).1.1 := rfl

@[simp] theorem orientedStrong_finish
    (fd : FullDimensionalSourcePresentation data coordinate)
    (tailDart : coordinate → Dart data)
    (hTail : ∀ c, fd.labelling.row (row data (tailDart c)) = c) (c : coordinate) :
    (orientedStrong fd tailDart hTail).finish c =
      (StableSourceDarts.opposite data fd.connected fd.pathEnds (tailDart c)).1.1 := rfl

/-- The oriented strong presentation displays the honest chart matrix. -/
theorem matrix_orientedStrong
    (fd : FullDimensionalSourcePresentation data coordinate)
    (tailDart : coordinate → Dart data)
    (hTail : ∀ c, fd.labelling.row (row data (tailDart c)) = c) :
    GluingDatum.LengthMatrixPresentation.matrix
        (orientedStrong fd tailDart hTail).toPresentation =
      GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation :=
  matrix_orientedPresentation fd tailDart hTail

end Oriented

/-! ## 4.  The certified pencil at a tracked state over the requested core -/

section Terminal

open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.ExplicitPotential
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.InputRefinementData
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.TerminalExhausts

/-- **The terminal certificate at a tracked state whose graph is the requested
core.** -/
theorem carriesCertifiedPencil_of_tracked
    {n p degree : ℕ} {spec : Spec n p} {F : Finset (Fin p)}
    (hCubic : spec.core.Cubic) (hCoreConnected : spec.core.Connected)
    {coordinate chart D V : Type} [Fintype coordinate] [DecidableEq coordinate]
    [Fintype chart] [DecidableEq chart] [Fintype D] [DecidableEq D]
    [Fintype V] [DecidableEq V]
    {graph : CubicDartGraph D V} {label : D → coordinate}
    {matrix : chart → Matrix coordinate coordinate ℚ}
    {baseStart baseFinish : coordinate → ℚ}
    (endpoint : graph.Iso (CubicCoreDarts.ofCore spec.core hCubic hCoreConnected))
    (slots : coordinate ≃ Fin p)
    (hslots : ∀ d : D, slots (label d) = (endpoint.dart d).1)
    (hBase : baseFinish =
      fun row ↦ if slots row ∈ F then 0 else ((spec.length (slots row) : ℕ) : ℚ))
    (final : TrackedState degree graph label matrix baseStart baseFinish) :
    CertifiedPencil.CarriesCertifiedPencil spec degree
      (matrix final.toMatrixState.label)
      final.toMatrixState.currentStart final.toMatrixState.currentFinish F := by
  classical
  obtain ⟨tgt, gdata, wall, candidate, fd, hMatrix, hValid, hConnTgt, hGenusTgt,
    hPencil, ⟨tracking⟩, hGenusSrc⟩ := final.carriesTrackedPencil
  set J := tracking.iso.trans endpoint with hJ
  -- the dart prescribed by the tail end of the core slot a row displays
  set tailDart : coordinate → Dart candidate.datum :=
    fun c ↦ J.dart.symm (slots c, false) with hTailDart
  have hDartVert : ∀ x : Dart candidate.datum,
      (CubicCoreDarts.ofCore spec.core hCubic hCoreConnected).vert (J.dart x) =
        J.vtx x.1 := fun x ↦ J.vert_map x
  have hTail : ∀ c, fd.labelling.row (row candidate.datum (tailDart c)) = c := by
    intro c
    apply slots.injective
    rw [← tracking.row_map (tailDart c), hslots (tracking.iso.dart (tailDart c))]
    show (J.dart (tailDart c)).1 = slots c
    rw [hTailDart]
    simp
  set strong := orientedStrong fd tailDart hTail with hStrong
  have hStrongMatrix : GluingDatum.LengthMatrixPresentation.matrix strong.toPresentation =
      matrix final.toMatrixState.label := by
    rw [hStrong, matrix_orientedStrong fd tailDart hTail, hMatrix]
  -- the source genus receipt
  have hSource : SourceGenusMatches spec candidate.datum := by
    rw [sourceGenusMatches_iff, hGenusSrc,
      ← endpoint.genus_eq]
    have hEuler := (CubicCoreDarts.ofCore spec.core hCubic hCoreConnected).euler
    rw [CubicCoreDarts.edgeCard_ofCore, Fintype.card_fin] at hEuler
    omega
  refine ⟨tgt, gdata, wall, candidate, fd, strong, hMatrix, hStrongMatrix, hValid,
    hConnTgt, hGenusTgt, hPencil, hSource, fun _ ↦ ?_⟩
  -- the interface at the requested lengths: the march's own atlas equation
  have hMap : (GluingDatum.LengthMatrixPresentation.matrix strong.toPresentation).mulVec
      final.toMatrixState.currentFinish = baseFinish := by
    rw [hStrongMatrix]
    exact final.toMatrixState.currentFinish_map
  refine ⟨{ slot := slots.symm
            matrixMap := by rw [hMap, hBase]; funext r; simp }, ?_⟩
  -- the two ends of a row, read on the core
  have hStartVert : ∀ c : coordinate,
      J.vtx (tailDart c).1 = spec.core.tail (slots c) := by
    intro c
    have h := hDartVert (tailDart c)
    rw [hTailDart] at h
    simpa [CubicCoreDarts.ofCore, CubicCoreDarts.vertex] using h.symm
  have hFinishVert : ∀ c : coordinate,
      J.vtx (StableSourceDarts.opposite candidate.datum fd.connected fd.pathEnds
          (tailDart c)).1 = spec.core.head (slots c) := by
    intro c
    have hOp := J.op_map (tailDart c)
    have hDart : J.dart (StableSourceDarts.opposite candidate.datum fd.connected
        fd.pathEnds (tailDart c)) = (slots c, true) := by
      have hEq : J.dart ((StableSourceDarts.ofDatum candidate.datum fd.connected
          fd.trivalent fd.pathEnds).op (tailDart c)) = (slots c, true) := by
        rw [← hOp, hTailDart]
        simp [CubicCoreDarts.ofCore, CubicCoreDarts.opposite]
      exact hEq
    have h := hDartVert (StableSourceDarts.opposite candidate.datum fd.connected
      fd.pathEnds (tailDart c))
    rw [hDart] at h
    simpa [CubicCoreDarts.ofCore, CubicCoreDarts.vertex] using h.symm
  have htail_eq : ∀ i : Fin p,
      (J.vtx.symm (spec.core.tail i)).1 = strong.start (slots.symm i) := by
    intro i
    rw [hStrong, orientedStrong_start]
    congr 1
    apply J.vtx.injective
    rw [Equiv.apply_symm_apply, hStartVert (slots.symm i), Equiv.apply_symm_apply]
  have hhead_eq : ∀ i : Fin p,
      (J.vtx.symm (spec.core.head i)).1 = strong.finish (slots.symm i) := by
    intro i
    rw [hStrong, orientedStrong_finish]
    congr 1
    apply J.vtx.injective
    rw [Equiv.apply_symm_apply, hFinishVert (slots.symm i), Equiv.apply_symm_apply]
  refine ⟨{ vertexAt := fun v ↦ (J.vtx.symm v).1
            tail_eq := htail_eq
            head_eq := hhead_eq }, ?_, ?_⟩
  · exact fun a b hab ↦ J.vtx.symm.injective (Subtype.ext hab)
  · intro v
    have hCard := (CubicCoreDarts.ofCore spec.core hCubic hCoreConnected).card_fibre v
    obtain ⟨d, hd⟩ : ∃ d : Fin p × Bool,
        d ∈ Finset.univ.filter (fun d : Fin p × Bool ↦
          (CubicCoreDarts.ofCore spec.core hCubic hCoreConnected).vert d = v) :=
      Finset.card_pos.mp (by omega)
    have hvert : (CubicCoreDarts.ofCore spec.core hCubic hCoreConnected).vert d = v :=
      (Finset.mem_filter.mp hd).2
    obtain ⟨i, b⟩ := d
    cases b with
    | false =>
      refine Or.inl ⟨i, ?_⟩
      have : spec.core.tail i = v := by
        simpa [CubicCoreDarts.ofCore, CubicCoreDarts.vertex] using hvert
      rw [← this]
      exact htail_eq i
    | true =>
      refine Or.inr ⟨i, ?_⟩
      have : spec.core.head i = v := by
        simpa [CubicCoreDarts.ofCore, CubicCoreDarts.vertex] using hvert
      rw [← this]
      exact hhead_eq i

/-- **The same statement at the requested expansion vector**, in the literal shape
`RequestedExpandedEndpoints.expandedFinish` gives it, which is the `hBase`
`RetainedIndexProducer.exists_subdivisionPencil_of_transport` consumes. -/
theorem carriesCertifiedPencil_of_tracked_expanded
    {n p degree : ℕ} {spec : Spec n p} {F : Finset (Fin p)}
    (hCubic : spec.core.Cubic) (hCoreConnected : spec.core.Connected)
    {coordinate chart D V : Type} [Fintype coordinate] [DecidableEq coordinate]
    [Fintype chart] [DecidableEq chart] [Fintype D] [DecidableEq D]
    [Fintype V] [DecidableEq V]
    {graph : CubicDartGraph D V} {label : D → coordinate}
    {matrix : chart → Matrix coordinate coordinate ℚ}
    {baseStart baseFinish : coordinate → ℚ}
    (endpoint : graph.Iso (CubicCoreDarts.ofCore spec.core hCubic hCoreConnected))
    (slots : coordinate ≃ Fin p)
    (hslots : ∀ d : D, slots (label d) = (endpoint.dart d).1)
    (hBase : baseFinish = RequestedExpandedEndpoints.expandedFinish spec F slots.symm)
    (final : TrackedState degree graph label matrix baseStart baseFinish) :
    CertifiedPencil.CarriesCertifiedPencil spec degree
      (matrix final.toMatrixState.label)
      final.toMatrixState.currentStart final.toMatrixState.currentFinish F :=
  carriesCertifiedPencil_of_tracked hCubic hCoreConnected endpoint slots hslots
    (by
      rw [hBase]
      funext r
      simp [RequestedExpandedEndpoints.expandedFinish,
        RequestedExpandedEndpoints.expandedLength, apply_ite (fun k : ℕ ↦ (k : ℚ))])
    final

end Terminal

/-! ## 5.  The composite with the outer walk -/

section Walk

open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.OuterWalk

/-- **The terminal certificate for the outer walk**, at the empty forest: at any
terminal tracked state over the requested cubic core. -/
theorem hT05_of_tracked (m : ℕ) {n p : ℕ} (spec : Spec n p)
    (hCubic : spec.core.Cubic) (hCoreConnected : spec.core.Connected) :
    ∀ (last : CubicDartGraph (Dart (CaterpillarSeed.seed m).candidate.datum)
        (BranchVertex (CaterpillarSeed.seed m).candidate.datum))
      (endpoint : last.Iso (CubicCoreDarts.ofCore spec.core hCubic hCoreConnected))
      (slots : Fin (6 * m + 3) ≃ Fin p),
      (∀ d, slots (seedLabel m d) = (endpoint.dart d).1) →
      ∀ (baseStart : Fin (6 * m + 3) → ℚ)
        (final : TrackedState (m + 2) last (seedLabel m)
          (MatrixAtlas.atlasMatrix (coordinate := Fin (6 * m + 3)) (degree := m + 2))
          baseStart (fun row ↦ ((spec.length (slots row) : ℕ) : ℚ))),
        final.Terminal →
        CertifiedPencil.CarriesCertifiedPencil spec (m + 2)
          (MatrixAtlas.atlasMatrix final.toMatrixState.label)
          final.toMatrixState.currentStart final.toMatrixState.currentFinish :=
  fun _ endpoint slots hslots _ final _ ↦
    carriesCertifiedPencil_of_tracked (F := ∅) hCubic hCoreConnected endpoint slots hslots
      (by simp) final

end Walk

/-! ## 6.  Non-vacuity -/

section NonVacuity

/-- **The oriented producer is unconditionally inhabited.** -/
noncomputable def orientedStrongOfRowDart {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation data coordinate) :
    StrongPresentation data coordinate :=
  orientedStrong fd
    (fun c ↦ StableSourceDarts.rowDart data fd.connected fd.pathEnds
      (fd.labelling.row.symm c))
    (fun c ↦ by
      rw [StableSourceDarts.row_rowDart, Equiv.apply_symm_apply])

theorem matrix_orientedStrongOfRowDart {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation data coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix
        (orientedStrongOfRowDart fd).toPresentation =
      GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation :=
  matrix_orientedStrong fd _ _

/-- A concrete inhabitant at the literal caterpillar seed cover. -/
noncomputable def seedOrientedStrong (m : ℕ) :
    StrongPresentation (CaterpillarSeed.seed m).candidate.datum (Fin (6 * m + 3)) :=
  orientedStrongOfRowDart (CaterpillarSeed.seedFullDim m (CaterpillarRows.fullDim m))

theorem matrix_seedOrientedStrong (m : ℕ) :
    GluingDatum.LengthMatrixPresentation.matrix (seedOrientedStrong m).toPresentation =
      GluingDatum.LengthMatrixPresentation.matrix
        (CaterpillarSeed.seedFullDim m (CaterpillarRows.fullDim m)).labelling.presentation :=
  matrix_orientedStrongOfRowDart _

end NonVacuity

end DraismaVargas.LocalCases.TerminalIdentification
