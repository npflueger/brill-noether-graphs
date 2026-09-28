import DraismaVargas.Infrastructure.IteratedContraction
import DraismaVargas.Infrastructure.IteratedContractionSource
import DraismaVargas.LocalCases.ClosedFaceRealization

/-!
# The terminal-face contraction datum

`DraismaVargas/LocalCases/ClosedEndpoint.lean` asks a `ContractedGluing` for a
`LaplacianEquiv` between

* `topology.contractedSpec.graph` — the canonical *positive* presentation of the
  quotient source of the starting stage with its zero-length occurrences
  contracted, and
* `realization.sourceSpec.graph` — the quotient source of the *contracted*
  gluing datum, subdivided by its own (positive) lengths.

`Utilities.Certificate.DegenerateSpec.DegSpec.Contraction` is the `LaplacianEquiv`
constructor that drops slots, so the route goes through it.  This file builds
that `Contraction` from the source correspondence of
`IteratedContractionSource` for `IteratedContraction.ContractsMany`, and
assembles `sourceEquiv` from it.

## The orientation

`DegSpec.Contraction.tail_eq` and `head_eq` are *orientation-exact*, and
`Utilities.Subdivision.ClosedContraction` provides no composition of a
`Contraction` with a slot-reversing `Spec.Relabeling`.  **The orientation comes
out right**, and `orientation_tail` / `orientation_head` below are the
witnesses: every link of the chain sends a first ordered endpoint to a first
ordered endpoint.

* `UnitSubdivisionPresentation.core_tail`/`core_head` send slot `tail` to
  `(edgeAt G slot).1` and `head` to `.2`, on *both* sides, since both sides use
  the same `core` constructor.
* `GluingDatum.sourceEnds_sourceEdgeOfOccurrence` (in
  `DraismaVargas.Infrastructure.GluingRealization`) identifies `edgeAt G slot`
  with `sourceEnds (sourceEdgeAt slot)` as an **ordered** pair.
* `SourceCorrespondenceSpec.sourceEnds_edgeMap` is stated with the ordered pair
  `(vertexMap (sourceEnds e).1, vertexMap (sourceEnds e).2)`.

So no `Spec.Relabeling` composition is needed, and the rest is bookkeeping.

## What is taken as a hypothesis

`SourceCorrespondenceSpec` is `IteratedContractionSource.SourceCorrespondence`,
imported rather than restated, and
`IteratedContractionSource.nonempty_sourceCorrespondence` proves one exists
along any iterated contraction.  Nothing in this file proves that; it consumes
the correspondence and builds the contraction datum from it.

Two further inputs are explicit hypotheses, both of which the terminal face
supplies:

* `hZero` — a source occurrence has length zero exactly when it lies over a
  contracted target occurrence (at the face this is
  `ClearedFace.sourceLength_eq_zero_iff`);
* `hLength` — the contracted realization restricts the starting one along
  `edgeMap` (with the realization bundled into `Step` this is available by
  construction).  `sourceLength_edgeMap` derives it from target-length
  compatibility and field (4) of the correspondence.

## What is delivered

* `orientation_tail` / `orientation_head` — the orientation finding;
* `contraction` — the `DegSpec.Contraction`;
* `sourceEquiv`, `bnExists_iff_of_sourceEquiv` — the `LaplacianEquiv` and the
  transport of Brill--Noether existence across it;
* `faceSourceEquiv` — the same, in the exact shape
  `Candidate.ClearedFace.ContractedGluing.sourceEquiv` demands, checked against
  `faceStep_sourceDegSpec`.
-/

namespace DraismaVargas.LocalCases.TerminalContraction

open Utilities
open Utilities.Certificate
open Utilities.Certificate.DegenerateSpec
open Utilities.Certificate.ContractionForestCensusGeneral
open Utilities.Certificate.ClosedFaceCensus
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.IteratedContraction
open DraismaVargas.Infrastructure.IteratedContractionSource

universe u

/-! ## Endpoint decoding on the degenerate side

The positive side already has `GluingRealization.sourceVertexAt_core_tail` and
`_head`.  These are the same two statements for the canonical degenerate
subdivision of a nonnegative realization; they are the first half of the
orientation check. -/

section Decode

variable {target : CFGraph.{u}} {degree : ℕ} {data : GluingDatum target degree}
  (realization : data.NonnegativeIntegralRealization)

/-- The canonical degenerate subdivision uses the unit-subdivision core of the
quotient source, unchanged. -/
theorem sourceDegSpec_core
    (hForest : IsForest (UnitSubdivisionPresentation.core data.sourceGraph)
      realization.sourceZeroSet)
    (hNotLoopy : ¬ IsLoopy (UnitSubdivisionPresentation.core data.sourceGraph)
      realization.sourceZeroSet) :
    (realization.sourceDegSpec hForest hNotLoopy).core =
      UnitSubdivisionPresentation.core data.sourceGraph := rfl

/-- Its representative map is the canonical union-find fold over the zero
occurrences. -/
theorem sourceDegSpec_rep
    (hForest : IsForest (UnitSubdivisionPresentation.core data.sourceGraph)
      realization.sourceZeroSet)
    (hNotLoopy : ¬ IsLoopy (UnitSubdivisionPresentation.core data.sourceGraph)
      realization.sourceZeroSet) :
    (realization.sourceDegSpec hForest hNotLoopy).rep =
      compFold (UnitSubdivisionPresentation.core data.sourceGraph)
        realization.sourceZeroSet := rfl

/-- **Orientation, degenerate side, tail.**  The `tail` of a canonical core
slot is the `vertexEquiv`-label of the **first** ordered endpoint of the exact
source occurrence that emitted the slot. -/
theorem core_tail_eq (slot : Fin data.sourceGraph.edges.card) :
    (UnitSubdivisionPresentation.core data.sourceGraph).tail slot =
      UnitSubdivisionPresentation.vertexEquiv data.sourceGraph
        (data.sourceEnds (realization.sourceEdgeAt slot)).1 := by
  show UnitSubdivisionPresentation.vertexEquiv data.sourceGraph
      (UnitSubdivisionPresentation.edgeAt data.sourceGraph slot).1 = _
  rw [GluingDatum.NonnegativeIntegralRealization.sourceEdgeAt,
    data.sourceEnds_sourceEdgeOfOccurrence]
  rfl

/-- **Orientation, degenerate side, head.**  The `head` of a canonical core slot
is the label of the **second** ordered endpoint. -/
theorem core_head_eq (slot : Fin data.sourceGraph.edges.card) :
    (UnitSubdivisionPresentation.core data.sourceGraph).head slot =
      UnitSubdivisionPresentation.vertexEquiv data.sourceGraph
        (data.sourceEnds (realization.sourceEdgeAt slot)).2 := by
  show UnitSubdivisionPresentation.vertexEquiv data.sourceGraph
      (UnitSubdivisionPresentation.edgeAt data.sourceGraph slot).2 = _
  rw [GluingDatum.NonnegativeIntegralRealization.sourceEdgeAt,
    data.sourceEnds_sourceEdgeOfOccurrence]
  rfl

/-- The canonical `Fin`-label of a quotient-source vertex. -/
noncomputable def vertexIndex (datum : GluingDatum target degree) :
    datum.SourceVertex ≃ Fin (Fintype.card datum.sourceGraph.V) :=
  UnitSubdivisionPresentation.vertexEquiv datum.sourceGraph

/-- The canonical slot of a quotient-source edge occurrence: the inverse of
`sourceEdgeAt`. -/
noncomputable def slotIndex : data.SourceEdge ≃ Fin data.sourceGraph.edges.card :=
  realization.sourceSlotEquiv.symm

@[simp] theorem sourceEdgeAt_slotIndex (edge : data.SourceEdge) :
    realization.sourceEdgeAt (slotIndex realization edge) = edge :=
  realization.sourceSlotEquiv.apply_symm_apply edge

@[simp] theorem slotIndex_sourceEdgeAt (slot : Fin data.sourceGraph.edges.card) :
    slotIndex realization (realization.sourceEdgeAt slot) = slot :=
  realization.sourceSlotEquiv.symm_apply_apply slot

/-- The canonical slot of a quotient-source edge occurrence, positive side. -/
noncomputable def posSlotIndex (positive : data.IntegralRealization) :
    data.SourceEdge ≃ Fin data.sourceGraph.edges.card :=
  positive.sourceSlotEquiv.symm

@[simp] theorem sourceEdgeAt_posSlotIndex (positive : data.IntegralRealization)
    (edge : data.SourceEdge) :
    positive.sourceEdgeAt (posSlotIndex positive edge) = edge :=
  positive.sourceSlotEquiv.apply_symm_apply edge

@[simp] theorem posSlotIndex_sourceEdgeAt (positive : data.IntegralRealization)
    (slot : Fin data.sourceGraph.edges.card) :
    posSlotIndex positive (positive.sourceEdgeAt slot) = slot :=
  positive.sourceSlotEquiv.symm_apply_apply slot

end Decode


/-! ## The source correspondence

Imported from `DraismaVargas/Infrastructure/IteratedContractionSource.lean`,
which also proves
`∀ {s t}, ContractsMany s t → Nonempty (SourceCorrespondence s t)`. -/

section Interface

/-- The shared interface, imported from `IteratedContractionSource`.  It is
proved inhabited along any iterated contraction by
`IteratedContractionSource.nonempty_sourceCorrespondence`.  The local name keeps
the statements below short. -/
@[reducible] def SourceCorrespondenceSpec {degree : ℕ} (s t : Step.{u} degree) :=
  IteratedContractionSource.SourceCorrespondence s t

end Interface


/-! ## `ReachThroughSet` and the census reachability relation agree

`DegSpec.Contraction.vtx_inj` and `vtx_surj` are statements about
`compFold`-classes on `Fin n`, while the correspondence's fibre equation (5) is
a statement about `ReachThroughSet` on quotient-source vertices.  These two
lemmas translate between them along `vertexIndex`. -/

section Translate

variable {degree : ℕ} {s : Step.{u} degree} {F : Finset s.target.edges}

/-- The census zero set of the starting stage is the set of slots lying over
contracted target occurrences. -/
theorem mem_sourceZeroSet_iff_mem
    (hZero : ∀ e : s.data.SourceEdge, s.realization.sourceLength e = 0 ↔ e.1.1 ∈ F)
    (slot : Fin s.data.sourceGraph.edges.card) :
    slot ∈ s.realization.sourceZeroSet ↔ (s.realization.sourceEdgeAt slot).1.1 ∈ F := by
  rw [GluingDatum.NonnegativeIntegralRealization.mem_sourceZeroSet]
  exact hZero _

/-- One walk step over a contracted occurrence is one census adjacency. -/
theorem adjInList_of_stepThroughSet
    (hZero : ∀ e : s.data.SourceEdge, s.realization.sourceLength e = 0 ↔ e.1.1 ∈ F)
    {x y : s.data.SourceVertex} (h : StepThroughSet s F x y) :
    AdjInList (UnitSubdivisionPresentation.core s.data.sourceGraph)
      (edgeList s.realization.sourceZeroSet)
      (vertexIndex s.data x) (vertexIndex s.data y) := by
  obtain ⟨e, hmem, hfst, hsnd⟩ := h
  refine ⟨slotIndex s.realization e, ?_, Or.inl ⟨?_, ?_⟩⟩
  · rw [mem_edgeList, mem_sourceZeroSet_iff_mem hZero, sourceEdgeAt_slotIndex]
    exact hmem
  · rw [core_tail_eq s.realization, sourceEdgeAt_slotIndex, hfst]
    rfl
  · rw [core_head_eq s.realization, sourceEdgeAt_slotIndex, hsnd]
    rfl

/-- Forward translation: a walk over contracted occurrences is a census
reachability. -/
theorem reachIn_of_reachThroughSet
    (hZero : ∀ e : s.data.SourceEdge, s.realization.sourceLength e = 0 ↔ e.1.1 ∈ F)
    {x y : s.data.SourceVertex} (h : ReachThroughSet s F x y) :
    ReachIn (UnitSubdivisionPresentation.core s.data.sourceGraph)
      s.realization.sourceZeroSet (vertexIndex s.data x) (vertexIndex s.data y) := by
  induction h with
  | rel _ _ hxy => exact Relation.ReflTransGen.single (adjInList_of_stepThroughSet hZero hxy)
  | refl _ => exact Relation.ReflTransGen.refl
  | symm _ _ _ ih => exact (reachIn_equivalence _ _).symm ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact (reachIn_equivalence _ _).trans ih₁ ih₂

/-- Backward translation: a census reachability is a walk over contracted
occurrences. -/
theorem reachThroughSet_of_reachIn
    (hZero : ∀ e : s.data.SourceEdge, s.realization.sourceLength e = 0 ↔ e.1.1 ∈ F)
    {a b : Fin (Fintype.card s.data.sourceGraph.V)}
    (h : ReachIn (UnitSubdivisionPresentation.core s.data.sourceGraph)
      s.realization.sourceZeroSet a b) :
    ReachThroughSet s F ((vertexIndex s.data).symm a) ((vertexIndex s.data).symm b) := by
  have h' : Relation.ReflTransGen
      (AdjInList (UnitSubdivisionPresentation.core s.data.sourceGraph)
        (edgeList s.realization.sourceZeroSet)) a b := h
  clear h
  induction h' with
  | refl => exact ReachThroughSet.refl _ _ _
  | tail _ hbc ih =>
      refine ih.trans ?_
      obtain ⟨slot, hslot, hcase⟩ := hbc
      rw [mem_edgeList] at hslot
      have hmem : (s.realization.sourceEdgeAt slot).1.1 ∈ F :=
        (mem_sourceZeroSet_iff_mem hZero slot).mp hslot
      have htail := core_tail_eq s.realization slot
      have hhead := core_head_eq s.realization slot
      rcases hcase with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
      · refine StepThroughSet.reach ⟨s.realization.sourceEdgeAt slot, hmem, ?_, ?_⟩
        · rw [← hfst, htail]
          exact ((vertexIndex s.data).symm_apply_apply _).symm
        · rw [← hsnd, hhead]
          exact ((vertexIndex s.data).symm_apply_apply _).symm
      · refine ReachThroughSet.symm
          (StepThroughSet.reach ⟨s.realization.sourceEdgeAt slot, hmem, ?_, ?_⟩)
        · rw [← hsnd, htail]
          exact ((vertexIndex s.data).symm_apply_apply _).symm
        · rw [← hfst, hhead]
          exact ((vertexIndex s.data).symm_apply_apply _).symm

end Translate


/-! ## The contraction datum

The seven fields of `DegSpec.Contraction`, each an index computation through
the four `Fintype.equivFin` choices. -/

section Build

variable {degree : ℕ} {s t : Step.{u} degree}

/-- The composite slot map: a slot of the contracted stage, decoded back to
the slot of the starting stage it came from.  This is
`edgeEquiv ∘ sourceEdgeOccurrenceEquiv ∘ edgeMap⁻¹ ∘ sourceEdgeOccurrenceEquiv⁻¹ ∘ edgeEquiv⁻¹`,
packaged through `sourceEdgeAt`. -/
noncomputable def slotMap (sc : SourceCorrespondenceSpec s t)
    (positive : t.data.IntegralRealization)
    (e' : Fin t.data.sourceGraph.edges.card) : Fin s.data.sourceGraph.edges.card :=
  slotIndex s.realization (sc.edgeMap.symm (positive.sourceEdgeAt e')).1

@[simp] theorem sourceEdgeAt_slotMap (sc : SourceCorrespondenceSpec s t)
    (positive : t.data.IntegralRealization)
    (e' : Fin t.data.sourceGraph.edges.card) :
    s.realization.sourceEdgeAt (slotMap sc positive e') =
      (sc.edgeMap.symm (positive.sourceEdgeAt e')).1 :=
  sourceEdgeAt_slotIndex s.realization _

theorem slotMap_injective (sc : SourceCorrespondenceSpec s t)
    (positive : t.data.IntegralRealization) :
    Function.Injective (slotMap sc positive) := by
  intro a b hab
  have h : (sc.edgeMap.symm (positive.sourceEdgeAt a)).1 =
      (sc.edgeMap.symm (positive.sourceEdgeAt b)).1 := by
    rw [← sourceEdgeAt_slotMap sc positive a, ← sourceEdgeAt_slotMap sc positive b, hab]
  have h₂ : positive.sourceEdgeAt a = positive.sourceEdgeAt b :=
    sc.edgeMap.symm.injective (Subtype.ext h)
  simpa using congrArg (posSlotIndex positive) h₂

/-- A section of the composite source vertex map, landing on `compFold`
representatives.  Well defined by the fibre equation (5) of the
correspondence, which is what `vtxMap_eq` records. -/
noncomputable def vtxMap (sc : SourceCorrespondenceSpec s t)
    (positive : t.data.IntegralRealization)
    (v' : Fin (Fintype.card t.data.sourceGraph.V)) :
    Fin (Fintype.card s.data.sourceGraph.V) :=
  compFold (UnitSubdivisionPresentation.core s.data.sourceGraph)
    s.realization.sourceZeroSet
    (vertexIndex s.data
      (Classical.choose (sc.vertexMap_surjective (positive.sourceVertexAt v'))))

/-- **The well-definedness of `vtxMap`.**  Any preimage of the decoded target
vertex computes it.  This is the only place the fibre equation is used. -/
theorem vtxMap_eq (sc : SourceCorrespondenceSpec s t)
    (positive : t.data.IntegralRealization)
    (hZero : ∀ e : s.data.SourceEdge,
      s.realization.sourceLength e = 0 ↔ e.1.1 ∈ sc.contracted)
    (v' : Fin (Fintype.card t.data.sourceGraph.V)) (x : s.data.SourceVertex)
    (hx : sc.vertexMap x = positive.sourceVertexAt v') :
    vtxMap sc positive v' =
      compFold (UnitSubdivisionPresentation.core s.data.sourceGraph)
        s.realization.sourceZeroSet (vertexIndex s.data x) := by
  have hchoice : sc.vertexMap
      (Classical.choose (sc.vertexMap_surjective (positive.sourceVertexAt v'))) =
      positive.sourceVertexAt v' :=
    Classical.choose_spec (sc.vertexMap_surjective (positive.sourceVertexAt v'))
  refine (compFold_iff _ _ _ _).mpr (reachIn_of_reachThroughSet hZero ?_)
  exact (sc.vertexMap_eq_iff _ x).mp (hchoice.trans hx.symm)

/-- **Orientation, tail.**  The `tail` of a transported slot is the
`compFold`-class of the label of the **first** ordered endpoint of the source
occurrence that emitted it.  Together with `sourceVertexAt_core_tail` on the
positive side and `sourceEnds_edgeMap` in the middle, this is the orientation
check of the module docstring: `.1` throughout, no reversal. -/
theorem core_tail_slotMap (sc : SourceCorrespondenceSpec s t)
    (positive : t.data.IntegralRealization)
    (e' : Fin t.data.sourceGraph.edges.card) :
    (UnitSubdivisionPresentation.core s.data.sourceGraph).tail (slotMap sc positive e') =
      vertexIndex s.data
        (s.data.sourceEnds (sc.edgeMap.symm (positive.sourceEdgeAt e')).1).1 := by
  rw [core_tail_eq s.realization, sourceEdgeAt_slotMap]
  rfl

/-- **Orientation, head.**  The same for `.2`. -/
theorem core_head_slotMap (sc : SourceCorrespondenceSpec s t)
    (positive : t.data.IntegralRealization)
    (e' : Fin t.data.sourceGraph.edges.card) :
    (UnitSubdivisionPresentation.core s.data.sourceGraph).head (slotMap sc positive e') =
      vertexIndex s.data
        (s.data.sourceEnds (sc.edgeMap.symm (positive.sourceEdgeAt e')).1).2 := by
  rw [core_head_eq s.realization, sourceEdgeAt_slotMap]
  rfl

/-- **The orientation finding, stated end to end (tail).**  The decoded target
endpoint of a transported slot is the `vertexMap`-image of the decoded source
endpoint **of the same index**. -/
theorem orientation_tail (sc : SourceCorrespondenceSpec s t)
    (positive : t.data.IntegralRealization)
    (e' : Fin t.data.sourceGraph.edges.card) :
    positive.sourceVertexAt (positive.sourceSpec.core.tail e') =
      sc.vertexMap
        (s.data.sourceEnds (sc.edgeMap.symm (positive.sourceEdgeAt e')).1).1 := by
  rw [positive.sourceVertexAt_core_tail]
  conv_lhs => rw [← sc.edgeMap.apply_symm_apply (positive.sourceEdgeAt e')]
  rw [sc.sourceEnds_edgeMap]

/-- **The orientation finding, stated end to end (head).** -/
theorem orientation_head (sc : SourceCorrespondenceSpec s t)
    (positive : t.data.IntegralRealization)
    (e' : Fin t.data.sourceGraph.edges.card) :
    positive.sourceVertexAt (positive.sourceSpec.core.head e') =
      sc.vertexMap
        (s.data.sourceEnds (sc.edgeMap.symm (positive.sourceEdgeAt e')).1).2 := by
  rw [positive.sourceVertexAt_core_head]
  conv_lhs => rw [← sc.edgeMap.apply_symm_apply (positive.sourceEdgeAt e')]
  rw [sc.sourceEnds_edgeMap]

/-- **The contraction datum** identifying the canonical degenerate
quotient source of the starting stage with the honest positive quotient source
of the contracted stage.

The hypotheses beyond the correspondence are exactly two, and both are supplied
at a cleared terminal face:

* `hZero` — a source occurrence has length zero exactly when it lies over a
  contracted target occurrence;
* `hLength` — the contracted realization restricts the starting one along
  `edgeMap`.

`hForest` and `hNotLoopy` are the two fields of
`Candidate.ClearedFace.SourceContractionTopology`; with
`s = ⟨_, candidate.datum, face.realization⟩` the degenerate spec below is
`topology.degSpec` on the nose. -/
noncomputable def contraction (sc : SourceCorrespondenceSpec s t)
    (positive : t.data.IntegralRealization)
    (hForest : IsForest (UnitSubdivisionPresentation.core s.data.sourceGraph)
      s.realization.sourceZeroSet)
    (hNotLoopy : ¬ IsLoopy (UnitSubdivisionPresentation.core s.data.sourceGraph)
      s.realization.sourceZeroSet)
    (hZero : ∀ e : s.data.SourceEdge,
      s.realization.sourceLength e = 0 ↔ e.1.1 ∈ sc.contracted)
    (hLength : ∀ e : {e : s.data.SourceEdge // e.1.1 ∉ sc.contracted},
      positive.sourceLength (sc.edgeMap e) = s.realization.sourceLength e.1) :
    DegSpec.Contraction (s.realization.sourceDegSpec hForest hNotLoopy)
      positive.sourceSpec where
  vtx := vtxMap sc positive
  vtx_rep _ := compFold_idem _ _ _
  vtx_inj := by
    intro v₁ v₂ hv
    obtain ⟨x₁, hx₁⟩ := sc.vertexMap_surjective (positive.sourceVertexAt v₁)
    obtain ⟨x₂, hx₂⟩ := sc.vertexMap_surjective (positive.sourceVertexAt v₂)
    rw [vtxMap_eq sc positive hZero v₁ x₁ hx₁, vtxMap_eq sc positive hZero v₂ x₂ hx₂] at hv
    have hreach := reachThroughSet_of_reachIn (F := sc.contracted) hZero
      ((compFold_iff _ _ _ _).mp hv)
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at hreach
    have hmap : sc.vertexMap x₁ = sc.vertexMap x₂ := (sc.vertexMap_eq_iff x₁ x₂).mpr hreach
    rw [hx₁, hx₂] at hmap
    exact positive.sourceVertexAt_injective hmap
  vtx_surj := by
    intro v
    refine ⟨positive.sourceVertexEquiv.symm
      (sc.vertexMap ((vertexIndex s.data).symm v)), ?_⟩
    rw [vtxMap_eq sc positive hZero _ ((vertexIndex s.data).symm v)
      (positive.sourceVertexEquiv.apply_symm_apply _).symm, Equiv.apply_symm_apply]
    rfl
  slot := slotMap sc positive
  slot_inj := slotMap_injective sc positive
  slot_surj := by
    intro e hpos
    have hne : (s.realization.sourceEdgeAt e).1.1 ∉ sc.contracted := by
      intro hmem
      have hzero : s.realization.sourceLength (s.realization.sourceEdgeAt e) = 0 :=
        (hZero _).mpr hmem
      have : (s.realization.sourceDegSpec hForest hNotLoopy).length e = 0 := hzero
      omega
    refine ⟨posSlotIndex positive (sc.edgeMap ⟨s.realization.sourceEdgeAt e, hne⟩), ?_⟩
    show slotIndex s.realization
      (sc.edgeMap.symm (positive.sourceEdgeAt
        (posSlotIndex positive (sc.edgeMap ⟨s.realization.sourceEdgeAt e, hne⟩)))).1 = e
    rw [sourceEdgeAt_posSlotIndex, Equiv.symm_apply_apply]
    exact slotIndex_sourceEdgeAt s.realization e
  length_eq := by
    intro e'
    show positive.sourceLength (positive.sourceEdgeAt e') =
      s.realization.sourceLength (s.realization.sourceEdgeAt (slotMap sc positive e'))
    rw [sourceEdgeAt_slotMap]
    have h := hLength (sc.edgeMap.symm (positive.sourceEdgeAt e'))
    rwa [Equiv.apply_symm_apply] at h
  tail_eq := by
    intro e'
    show vtxMap sc positive (positive.sourceSpec.core.tail e') =
      compFold (UnitSubdivisionPresentation.core s.data.sourceGraph)
        s.realization.sourceZeroSet
        ((UnitSubdivisionPresentation.core s.data.sourceGraph).tail
          (slotMap sc positive e'))
    rw [core_tail_slotMap, vtxMap_eq sc positive hZero _ _
      (orientation_tail sc positive e').symm]
  head_eq := by
    intro e'
    show vtxMap sc positive (positive.sourceSpec.core.head e') =
      compFold (UnitSubdivisionPresentation.core s.data.sourceGraph)
        s.realization.sourceZeroSet
        ((UnitSubdivisionPresentation.core s.data.sourceGraph).head
          (slotMap sc positive e'))
    rw [core_head_slotMap, vtxMap_eq sc positive hZero _ _
      (orientation_head sc positive e').symm]

/-- `hLength` of `contraction`, derived from target-length compatibility and
field (4) of the correspondence.  This is how a terminal face supplies it: the
contracted realization restricts the starting one along the fold on target
occurrences, and the dilation index is unchanged, so the source lengths agree
after cancelling the (positive) index. -/
theorem sourceLength_edgeMap (sc : SourceCorrespondenceSpec s t)
    (positive : t.data.IntegralRealization)
    (hTarget : ∀ e : {e : s.data.SourceEdge // e.1.1 ∉ sc.contracted},
      positive.targetLength (sc.edgeMap e).1.1 = s.realization.targetLength e.1.1.1)
    (e : {e : s.data.SourceEdge // e.1.1 ∉ sc.contracted}) :
    positive.sourceLength (sc.edgeMap e) = s.realization.sourceLength e.1 := by
  have hindex : 0 < s.data.sourceEdgeIndex e.1 := s.data.sourceEdgeIndex_pos e.1
  have hposDil := positive.dilation_length (sc.edgeMap e)
  have hstartDil := s.realization.dilation_length e.1
  rw [sc.sourceEdgeIndex_edgeMap e, hTarget e] at hposDil
  exact Nat.eq_of_mul_eq_mul_left hindex (hposDil.trans hstartDil.symm)

end Build

/-! ## The `LaplacianEquiv` -/

section Assemble

/-- The composite, at the level of bare specifications: the canonical
positive contraction of a `DegSpec` is Laplacian-equivalent to any positive
`Spec` it contracts onto.  This is the shape of
`DegenerateRepRigidity.repEquiv` and of `ZeroFreeTerminalFace.sourceEquiv`. -/
noncomputable def sourceEquivOfContraction {n p n' p' : ℕ} {d : DegSpec n p}
    {positiveSpec : SubdivisionGraph.Spec n' p'} (c : DegSpec.Contraction d positiveSpec) :
    LaplacianEquiv d.contractedSpec.graph positiveSpec.graph :=
  d.canonicalContraction.laplacianEquiv.trans c.laplacianEquiv.symm

variable {degree : ℕ} {s t : Step.{u} degree}

/-- **The `sourceEquiv` of `ContractedGluing`.**  With
`s = ⟨_, candidate.datum, face.realization⟩` and
`hForest`, `hNotLoopy` the two fields of
`Candidate.ClearedFace.SourceContractionTopology`, the source of this
equivalence is `topology.contractedSpec.graph` definitionally, and the first
factor is `topology.laplacianEquiv`. -/
noncomputable def sourceEquiv (sc : SourceCorrespondenceSpec s t)
    (positive : t.data.IntegralRealization)
    (hForest : IsForest (UnitSubdivisionPresentation.core s.data.sourceGraph)
      s.realization.sourceZeroSet)
    (hNotLoopy : ¬ IsLoopy (UnitSubdivisionPresentation.core s.data.sourceGraph)
      s.realization.sourceZeroSet)
    (hZero : ∀ e : s.data.SourceEdge,
      s.realization.sourceLength e = 0 ↔ e.1.1 ∈ sc.contracted)
    (hLength : ∀ e : {e : s.data.SourceEdge // e.1.1 ∉ sc.contracted},
      positive.sourceLength (sc.edgeMap e) = s.realization.sourceLength e.1) :
    LaplacianEquiv (s.realization.sourceDegSpec hForest hNotLoopy).contractedSpec.graph
      positive.sourceSpec.graph :=
  sourceEquivOfContraction (contraction sc positive hForest hNotLoopy hZero hLength)

/-- Brill--Noether existence transports across `sourceEquiv`; this is the only
property `ClosedEndpoint.bnExists` consumes. -/
theorem bnExists_iff_of_sourceEquiv (sc : SourceCorrespondenceSpec s t)
    (positive : t.data.IntegralRealization)
    (hForest : IsForest (UnitSubdivisionPresentation.core s.data.sourceGraph)
      s.realization.sourceZeroSet)
    (hNotLoopy : ¬ IsLoopy (UnitSubdivisionPresentation.core s.data.sourceGraph)
      s.realization.sourceZeroSet)
    (hZero : ∀ e : s.data.SourceEdge,
      s.realization.sourceLength e = 0 ↔ e.1.1 ∈ sc.contracted)
    (hLength : ∀ e : {e : s.data.SourceEdge // e.1.1 ∉ sc.contracted},
      positive.sourceLength (sc.edgeMap e) = s.realization.sourceLength e.1)
    (rank divisorDegree : ℤ) :
    BNExists (s.realization.sourceDegSpec hForest hNotLoopy).contractedSpec.graph
        rank divisorDegree ↔
      BNExists positive.sourceSpec.graph rank divisorDegree :=
  (sourceEquiv sc positive hForest hNotLoopy hZero hLength).bnExists_iff rank divisorDegree

end Assemble


/-! ## The terminal face, wired up

These three declarations check that the general construction above has exactly
the type `Candidate.ClearedFace.ContractedGluing.sourceEquiv` asks for (in
`ClosedEndpoint`).  An actual inhabitant of `ContractedGluing` also needs the
`SourceCorrespondenceSpec` itself (`IteratedContractionSource.nonempty_sourceCorrespondence`)
and the identification `hZero` of the contracted target occurrences with the
zero-length ones; `TerminalGluing.contractedGluing_of_incoming` assembles it. -/

section TerminalFace

open DraismaVargas.LocalCases.BalancedGlobal

variable {tgt : CFGraph.{u}} {degree : ℕ} {datum : GluingDatum tgt degree} {wall : tgt.V}
  {candidate : Candidate tgt degree datum wall} {coordinate : Type*}
  {presentation : candidate.datum.LengthMatrixPresentation coordinate}
  {coordinates : coordinate → ℚ}

/-- The stage an iterated contraction starts from at a cleared terminal face:
the expanded target, the candidate's outgoing datum, and the face's own
nonnegative realization. -/
noncomputable def faceStep (face : Candidate.ClearedFace candidate presentation coordinates) :
    Step.{u} degree :=
  ⟨DraismaVargas.Infrastructure.TargetExpansion.graph tgt wall candidate.right,
    candidate.datum, face.realization⟩

/-- The degenerate spec of `faceStep` **is** `topology.degSpec`, on the nose. -/
theorem faceStep_sourceDegSpec
    (face : Candidate.ClearedFace candidate presentation coordinates)
    (topology : Candidate.ClearedFace.SourceContractionTopology face) :
    (faceStep face).realization.sourceDegSpec topology.forest topology.notLoopy =
      topology.degSpec := rfl

/-- **The `sourceEquiv` field of `ContractedGluing`**, in the exact shape
`ClosedEndpoint` demands. -/
noncomputable def faceSourceEquiv
    (face : Candidate.ClearedFace candidate presentation coordinates)
    (topology : Candidate.ClearedFace.SourceContractionTopology face)
    {t : Step.{u} degree} (sc : SourceCorrespondenceSpec (faceStep face) t)
    (positive : t.data.IntegralRealization)
    (hZero : ∀ e : (faceStep face).data.SourceEdge,
      (faceStep face).realization.sourceLength e = 0 ↔ e.1.1 ∈ sc.contracted)
    (hLength : ∀ e : {e : (faceStep face).data.SourceEdge // e.1.1 ∉ sc.contracted},
      positive.sourceLength (sc.edgeMap e) = (faceStep face).realization.sourceLength e.1) :
    LaplacianEquiv topology.contractedSpec.graph positive.sourceSpec.graph :=
  sourceEquiv sc positive topology.forest topology.notLoopy hZero hLength

/-- The same equivalence with `hLength` discharged rather than assumed.

At the terminal stage the positive realization is the stage's own realization
(`Step.integralRealization_sourceLength` is `rfl`), and the composed
correspondence preserves source lengths, so the hypothesis is exactly
`sc.sourceLength_edgeMap`.  It is *not* dischargeable for an arbitrary positive
realization on the terminal datum, which is why `faceSourceEquiv` above keeps it
as a hypothesis. -/
noncomputable def faceSourceEquivOfTerminal
    (face : Candidate.ClearedFace candidate presentation coordinates)
    (topology : Candidate.ClearedFace.SourceContractionTopology face)
    {t : Step.{u} degree} (sc : SourceCorrespondenceSpec (faceStep face) t)
    (hPositive : ∀ e : t.target.edges, 0 < t.realization.targetLength e)
    (hZero : ∀ e : (faceStep face).data.SourceEdge,
      (faceStep face).realization.sourceLength e = 0 ↔ e.1.1 ∈ sc.contracted) :
    LaplacianEquiv topology.contractedSpec.graph
      (t.integralRealization hPositive).sourceSpec.graph :=
  faceSourceEquiv face topology sc (t.integralRealization hPositive) hZero
    sc.sourceLength_edgeMap

end TerminalFace

end DraismaVargas.LocalCases.TerminalContraction
