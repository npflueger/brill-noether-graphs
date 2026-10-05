module

public import DraismaVargas.LocalCases.RetainedStraddle
public import DraismaVargas.LocalCases.RetainedStatement

@[expose] public section

/-!
# The vertex map of the retained core model, and its endpoint equations

**Source.**  The requested type is presented, as in the proof of the main result
of Draisma–Vargas Part I, arXiv:1909.12924 (subsection
`section-proof-main-result`), as a point of the closed cone of a trivalent one.
The marker cut itself is in neither Draisma–Vargas Part I nor Vargas, Part II
(arXiv:2609.09109), and the integral-scale transport has
no verbatim counterpart there, so, as in `DraismaVargas.LocalCases.RetainedCut`,
`RetainedRowPieces` and `RetainedStraddle`, nothing here is a transcription of
either paper.  The target of the core model is the pruned contracted spec cut at
the straddled markers (`RetainedCut.cutSpec`).  A requested core vertex that is
not a marker is the image of a whole fibre of model core vertices and is sent to
that fibre's contraction class, which is well defined because the fibre is
connected through contracted slots, each a zero row
(`RetainedFibre.coreClass_eq_of_fib_eq`); a marker has no model core vertex
above it and is treated separately (`RetainedFibre.isMarker_or_exists_fib`).

## What is proved

`RetainedExhausts.cutRelabeling_of_expansion_of_injective` reduces the cut
relabelling at every terminal face of the requested expansion model to one
datum: an orientation flag `rev`, a map `Ψ` from the refined core vertices of
the retained segment data to the core vertices of `RetainedCut.cutSpec`, its
injectivity, and `RetainedCoreModel.EndpointEquations`.  **This file builds `Ψ` and proves the
endpoint equations for it, with no hypothesis beyond what
`RetainedRelabeling.CutRelabeling` already keeps inside its binder.**  The
orientation is the traversal's own, `RetainedTraversal.reversedAt`.

* §1--§2 count the pieces the marker cut leaves of a kept slot -- two on a
  straddled slot, one otherwise -- and name the two contraction classes the
  oriented row passes through at that occurrence, `startClass` and `endClass`.
  Both are kept classes, because the occurrence is not dangling.

* §3 names the core vertices of the cut spec on the kept slots themselves
  (`cutSlot`, `cutClass`, `cutLeft`, `splitVertex`), which is what keeps the
  file off the expensive unfolding of `(packed (prunedSpec …)).p =
  (keptSlots …).card`, exactly as `RetainedCoreModel.cutSegs` does for the
  segment lists.  `cutTail x t` and `cutHead x t` are the core vertices of the
  cut spec immediately before and after the `t`-th piece of the kept slot `x`
  **in row order**: a new split vertex where a second piece follows or
  precedes, and a walk class at an occurrence boundary otherwise.

* §4--§6 turn the cut spec's own endpoint equations into that language.  The
  content is `RefinementCore.prunedSpec_core_tail`/`_head` composed with
  `RetainedTraversal.sourceEnds_occurrence_fst`/`_snd`: the pruned spec orients
  a kept slot by the source's `sourceEnds`, the cut lists its pieces in row
  order, and `RetainedCoreModel.pieceIndex` is the mirror index between the
  two.

* §7 is the one genuinely new combinatorial lemma,
  `cutHead_eq_cutTail_of_succ`: **the two readings of one interior point of a
  retained row agree.**  If one piece follows another immediately along the
  row, the vertex the cut puts after the first is the vertex it puts before the
  second -- either both are the new split vertex of a single straddled kept
  slot, or the two pieces end and start consecutive kept slots and the two walk
  classes agree because everything the row meets between them is contracted.

* §8--§13 locate a prescribed segment (`blockSlot`, `blockIndex`), identify the
  handover points -- the requested core vertices at which a retained row hands
  over from the first requested slot it carries to the second -- with
  `RetainedFibre.IsMarker` at the requested expansion model, and build the map:

  - a **breakpoint** inside a requested slot goes to the cut vertex after the
    piece it follows;
  - a **handover point** goes to the cut vertex before the first piece of the
    requested slot that begins there.  This is the whole marker case, and it
    needs no separate locating lemma: `cutTail` is the new split vertex exactly
    when the marker straddles a kept slot, and the walk class at the occurrence
    boundary exactly when it does not, which is the aligned case
    `RetainedStraddle` leaves open;
  - every other requested core vertex is the image of a whole fibre of model
    core vertices (`RetainedFibre.isMarker_or_exists_fib`) and goes to that
    fibre's common contraction class (`RetainedFibre.coreClass_eq_of_fib_eq`).

* §14--§15 prove the two endpoint equations.  Inside a requested slot they are
  §7; at the ends they are the handover case, or
  `RetainedFibre.requestedClass` reached across the contracted run at the start
  or the end of the row.  **`StrongRefinement.Faithful` is what orients the
  rows** (`finish_ne_start_of_faithful`, from the looplessness of the cubic
  model's core) and `Spanning` is what makes the fibre classes kept; both are
  already inside `CutRelabeling`'s binder, so nothing new is assumed.

* §16--§17 feed this back.  `cutRelabeling_of_expansion`: the cut relabelling at
  the requested expansion model follows from **the injectivity of `vertexModel`
  alone**, and `nonempty_evenSubdivisionPencil_of_link_of_injective_vertexModel`
  is the Statement's conclusion from the walk's `link` and that one hypothesis.

* §19--§21 discharge the **split half of that injectivity**.  A breakpoint of
  the retained refinement never lands on a new split vertex
  (`not_straddles_blockSlot_breakPair`, from
  `RetainedStraddle.retPos_ne_piecePos_zero`), only a straddling marker does,
  and the split vertex records the kept slot it was cut inside, which together
  with the carrier position determines the marker
  (`eq_of_cutVertex_inr`).  `injective_vertexModel_of_inl` therefore reduces
  `Function.Injective vertexModel` to **the contraction classes alone**: two
  refined core vertices sent to the same kept class are equal.

## The hypotheses that remain explicit

1. **`Function.Injective vertexModel`.**  This is all that remains of the cut
   relabelling after this file, and it is named as one hypothesis at every
   terminal face.  §19--§21 reduce it to the **class half**, the general-forest
   form of `DraismaVargas.LocalCases.ClassInjectivity`: two refined core
   vertices sent to the same kept class must be equal.  That half is **not
   proved here**; it is proved in
   `DraismaVargas.LocalCases.RetainedClassInjectivity`, which supplies `hcls`
   below.  Its three general-forest replacements for `ClassInjectivity`'s
   §3--§4 inputs are `RetainedCut.positiveRow_ne_nil_of_not_mem_forest` (every
   retained row carries a surviving occurrence),
   `RetainedTraversal.classOf_finish_eq_classOf_start_of_mem_forest` with
   `RetainedFibre.coreClass_eq_of_fib_eq` (a forest row is one class), and
   `RetainedFibre.not_exists_fib_eq_marker` (a marker is the class of no model
   core vertex); `ClassInjectivity`'s own zero-run confinement (`Near`,
   `near_step`, `eq_of_near`) is stated at `F = ∅` and is re-proved at a
   nonempty forest in `RetainedClassInjectivity` §1--§2.
2. **`link`** -- the type-changing exits at non-trivalent walls.  Untouched.
3. Everything `RetainedRelabeling.CutRelabeling` keeps inside its binder: the
   core dictionary, `Faithful`, `Spanning`, `Connected`, `SourceGenusMatches`,
   the topology and the kept class.  §15--§17 use `Faithful`, `Spanning` and
   `hCond`; the theorems below take them as explicit arguments.

## Consumers

The cut relabelling `RetainedRelabeling.CutRelabeling`, through
`RetainedExhausts.cutRelabeling_of_expansion_of_injective`; and through
`RetainedStatement.nonempty_evenSubdivisionPencil_of_link_of_injective` the
route to `DraismaVargas.Statement`.
-/

namespace DraismaVargas.LocalCases.RetainedVertexModel

noncomputable section

open Utilities
open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.IteratedSplitRefinement
open Utilities.Subdivision.CoreExpansion
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.BlockSplitCount
open DraismaVargas.Infrastructure.FlattenIndex
open DraismaVargas.Infrastructure.OccurrenceCut
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancedGlobal.Candidate
open DraismaVargas.LocalCases.InputRefinementData
open DraismaVargas.LocalCases.OrientedTraversal
open DraismaVargas.LocalCases.RefinementCore
open DraismaVargas.LocalCases.RequestedExpandedEndpoints
open DraismaVargas.LocalCases.RetainedCoreModel
open DraismaVargas.LocalCases.RetainedCut
open DraismaVargas.LocalCases.RetainedRelabeling
open DraismaVargas.LocalCases.RetainedRowPieces
open DraismaVargas.LocalCases.RetainedStraddle
open DraismaVargas.LocalCases.SlotRefinement
open DraismaVargas.LocalCases.StrongRefinement
open DraismaVargas.LocalCases.TraversalPresentation
open DraismaVargas.LocalCases.ZeroForestPreservation
open DraismaVargas.LocalCases.W4StableSource

variable {target : CFGraph} {degree : ℕ}
  {gluing : GluingDatum target degree} {wall : target.V}
  {candidate : Candidate target degree gluing wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {coordinates : coordinate → ℚ}
  {strong : StrongPresentation candidate.datum coordinate}
  {face : ClearedFace candidate strong.toPresentation coordinates}

section General

variable {n p : ℕ} {spec : SubdivisionGraph.Spec n p} {F : Finset (Fin p)}
  {n' p' : ℕ} {small : SubdivisionGraph.Spec n' p'}
  {iface : InputInterface spec strong.toPresentation coordinates F}

/-! ## 1.  The pieces of a kept slot, counted -/

/-- **The number of pieces the marker cut leaves of one kept slot**: two on a
straddled slot, one otherwise. -/
abbrev pieceCount (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small) (x : SlotIndex iface face) : ℕ :=
  (OrderedPathSplit.positiveSegments (pieces iface face idx x)).length

theorem pieceCount_of_straddles (idx : RetainedIndex spec F small)
    {x : SlotIndex iface face} (h : Straddles iface face idx x) :
    pieceCount iface face idx x = 2 :=
  length_positiveSegments_pieces_of_straddles idx h

theorem pieceCount_of_not_straddles (idx : RetainedIndex spec F small)
    {x : SlotIndex iface face} (h : ¬ Straddles iface face idx x) :
    pieceCount iface face idx x = 1 := by
  show (OrderedPathSplit.positiveSegments (pieces iface face idx x)).length = 1
  rw [positiveSegments_pieces idx x, ite_eq_right h]
  rfl

theorem pieceCount_pos (idx : RetainedIndex spec F small) (x : SlotIndex iface face) :
    0 < pieceCount iface face idx x := by
  by_cases h : Straddles iface face idx x
  · rw [pieceCount_of_straddles idx h]; omega
  · rw [pieceCount_of_not_straddles idx h]; omega

theorem pieceCount_le_two (idx : RetainedIndex spec F small) (x : SlotIndex iface face) :
    pieceCount iface face idx x ≤ 2 := by
  by_cases h : Straddles iface face idx x
  · rw [pieceCount_of_straddles idx h]
  · rw [pieceCount_of_not_straddles idx h]; omega

theorem straddles_of_one_lt_pieceCount (idx : RetainedIndex spec F small)
    {x : SlotIndex iface face} (h : 1 < pieceCount iface face idx x) :
    Straddles iface face idx x := by
  by_contra hs
  have := pieceCount_of_not_straddles idx hs
  omega

theorem piecePos_lt' (idx : RetainedIndex spec F small) (hTwo : CarriesAtMostTwo idx)
    (x : SlotIndex iface face) {t : ℕ} (ht : t < pieceCount iface face idx x) :
    piecePos iface face idx x t < (rowPieces iface face idx (slotRow x)).length :=
  piecePos_lt idx hTwo x ht

theorem piecePos_inj' (idx : RetainedIndex spec F small) {x x' : SlotIndex iface face}
    (hrow : x.1 = x'.1) {t t' : ℕ} (ht : t < pieceCount iface face idx x)
    (ht' : t' < pieceCount iface face idx x')
    (h : piecePos iface face idx x t = piecePos iface face idx x' t') : x = x' ∧ t = t' :=
  piecePos_inj idx hrow ht ht' h

theorem getD_rowPieces_piecePos' (idx : RetainedIndex spec F small)
    (hTwo : CarriesAtMostTwo idx) (x : SlotIndex iface face) {t : ℕ}
    (ht : t < pieceCount iface face idx x) :
    (rowPieces iface face idx (slotRow x)).getD (piecePos iface face idx x t) 0 =
      (OrderedPathSplit.positiveSegments (pieces iface face idx x)).getD t 0 :=
  getD_rowPieces_piecePos idx hTwo x ht

/-! ## 2.  The two walk classes of a kept slot -/

/-- The contraction class the row is in when it enters the occurrence carrying
the kept slot `x`. -/
def startClass (topology : ClearedFace.SourceContractionTopology face)
    (x : SlotIndex iface face) : topology.degSpec.Class :=
  classOf topology
    (RetainedTraversal.rowWalk strong iface x.1 (RetainedTraversal.slotPosition x))

/-- and the one it is in when it leaves it. -/
def endClass (topology : ClearedFace.SourceContractionTopology face)
    (x : SlotIndex iface face) : topology.degSpec.Class :=
  classOf topology
    (RetainedTraversal.rowWalk strong iface x.1 (RetainedTraversal.slotPosition x + 1))

theorem incident_startClass (x : SlotIndex iface face) :
    Incident candidate.datum (occurrence x)
      (RetainedTraversal.rowWalk strong iface x.1 (RetainedTraversal.slotPosition x)) := by
  have h := RetainedTraversal.rowWalk_incident (strong := strong) (iface := iface)
    (RetainedTraversal.slotPosition_lt (iface := iface) (face := face) x)
  rwa [← RetainedTraversal.occurrence_eq_getElem x] at h

theorem incident_endClass (x : SlotIndex iface face) :
    Incident candidate.datum (occurrence x)
      (RetainedTraversal.rowWalk strong iface x.1 (RetainedTraversal.slotPosition x + 1)) := by
  have h := RetainedTraversal.rowWalk_succ_incident (strong := strong) (iface := iface)
    (RetainedTraversal.slotPosition_lt (iface := iface) (face := face) x)
  rwa [← RetainedTraversal.occurrence_eq_getElem x] at h

theorem keptClass_startClass (topology : ClearedFace.SourceContractionTopology face)
    (x : SlotIndex iface face) :
    ClearedFace.SourceContractionTopology.KeptClass topology (startClass topology x) :=
  ⟨_, rfl,
    ClearedFace.SourceContractionTopology.nonDanglingValency_pos_of_incident
      (not_isDangling_occurrence x) (incident_startClass x)⟩

theorem keptClass_endClass (topology : ClearedFace.SourceContractionTopology face)
    (x : SlotIndex iface face) :
    ClearedFace.SourceContractionTopology.KeptClass topology (endClass topology x) :=
  ⟨_, rfl,
    ClearedFace.SourceContractionTopology.nonDanglingValency_pos_of_incident
      (not_isDangling_occurrence x) (incident_endClass x)⟩

/-! ## 3.  The core vertices of the cut spec, named on the kept slots -/

section CutVertices

variable (idx : RetainedIndex spec F small)
  (topology : ClearedFace.SourceContractionTopology face)
  (rev : SlotIndex iface face → Bool)
  (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)

/-- **A kept slot, read as a slot of the packed pruned contracted spec.**
Naming this coercion once is what keeps every statement below off the expensive
unfolding of `(packed (prunedSpec …)).p = (keptSlots …).card`, exactly as
`RetainedCoreModel.cutSegs` does for the segment lists. -/
def cutSlot (x : SlotIndex iface face) :
    Fin (packed (ClearedFace.SourceContractionTopology.prunedSpec topology hKept)).p :=
  slotIndexEquivKept iface face topology x

/-- **and a kept class, read as a core vertex of it.** -/
def cutClass (c : Fin (ClearedFace.SourceContractionTopology.keptClasses topology).card) :
    Fin (packed (ClearedFace.SourceContractionTopology.prunedSpec topology hKept)).n :=
  c

theorem length_cutSegs_eq (x : SlotIndex iface face) :
    (cutSegs iface face idx topology rev hKept x).length = pieceCount iface face idx x :=
  length_cutSegs iface face idx topology rev hKept x

theorem cutSlot_segments (x : SlotIndex iface face) :
    (cutData iface face idx topology rev hKept).segments (cutSlot topology hKept x) =
      cutSegs iface face idx topology rev hKept x := rfl

theorem length_cutData_segments (x : SlotIndex iface face) :
    ((cutData iface face idx topology rev hKept).segments
        (cutSlot topology hKept x)).length = pieceCount iface face idx x := by
  rw [cutSlot_segments idx topology rev hKept x, length_cutSegs]

/-- **A kept class, read as a core vertex of the cut spec.** -/
def cutLeft (c : Fin (ClearedFace.SourceContractionTopology.keptClasses topology).card) :
    RefinementCore.RefinedVertex (cutData iface face idx topology rev hKept) :=
  Sum.inl (cutClass topology hKept c)

/-- **The new split vertex the cut puts inside a straddled kept slot.**  It is
the only kind of core vertex of `RetainedCut.cutSpec` that is not a kept
class. -/
def splitVertex {x : SlotIndex iface face} (h : Straddles iface face idx x) :
    RefinementCore.RefinedVertex (cutData iface face idx topology rev hKept) :=
  Sum.inr ⟨cutSlot topology hKept x,
    ⟨0, by
      have h2 := length_cutData_segments idx topology rev hKept x
      have h3 := pieceCount_of_straddles idx h
      omega⟩⟩

/-- **The core vertex of the cut spec before the `t`-th piece of the kept slot
`x`**, in the order the retained row traverses them: the class the row is in
when it enters the occurrence if `t = 0`, and the new split vertex otherwise. -/
def cutTail (x : SlotIndex iface face) (t : ℕ) :
    RefinementCore.RefinedVertex (cutData iface face idx topology rev hKept) :=
  if h : Straddles iface face idx x ∧ t ≠ 0 then splitVertex idx topology rev hKept h.1
  else cutLeft idx topology rev hKept
    (RefinementCore.keptClassIndex topology
      ⟨startClass topology x, keptClass_startClass topology x⟩)

/-- **and the one after it**: the new split vertex if a second piece follows,
and otherwise the class the row is in when it leaves the occurrence. -/
def cutHead (x : SlotIndex iface face) (t : ℕ) :
    RefinementCore.RefinedVertex (cutData iface face idx topology rev hKept) :=
  if h : Straddles iface face idx x ∧ t = 0 then splitVertex idx topology rev hKept h.1
  else cutLeft idx topology rev hKept
    (RefinementCore.keptClassIndex topology
      ⟨endClass topology x, keptClass_endClass topology x⟩)

theorem cutTail_of_zero (x : SlotIndex iface face) :
    cutTail idx topology rev hKept x 0 =
      cutLeft idx topology rev hKept
        (RefinementCore.keptClassIndex topology
          ⟨startClass topology x, keptClass_startClass topology x⟩) :=
  dite_eq_right (fun h ↦ h.2 rfl)

theorem cutTail_of_ne_zero {x : SlotIndex iface face} {t : ℕ} (ht : t ≠ 0)
    (h : Straddles iface face idx x) :
    cutTail idx topology rev hKept x t = splitVertex idx topology rev hKept h :=
  dite_eq_left ⟨h, ht⟩

theorem cutTail_of_not_straddles {x : SlotIndex iface face}
    (h : ¬ Straddles iface face idx x) (t : ℕ) :
    cutTail idx topology rev hKept x t =
      cutLeft idx topology rev hKept
        (RefinementCore.keptClassIndex topology
          ⟨startClass topology x, keptClass_startClass topology x⟩) :=
  dite_eq_right (fun hc ↦ h hc.1)

theorem cutHead_of_zero_of_straddles {x : SlotIndex iface face}
    (h : Straddles iface face idx x) :
    cutHead idx topology rev hKept x 0 = splitVertex idx topology rev hKept h :=
  dite_eq_left ⟨h, rfl⟩

theorem cutHead_of_ne_zero {x : SlotIndex iface face} {t : ℕ} (ht : t ≠ 0) :
    cutHead idx topology rev hKept x t =
      cutLeft idx topology rev hKept
        (RefinementCore.keptClassIndex topology
          ⟨endClass topology x, keptClass_endClass topology x⟩) :=
  dite_eq_right (fun h ↦ ht h.2)

theorem cutHead_of_not_straddles {x : SlotIndex iface face}
    (h : ¬ Straddles iface face idx x) (t : ℕ) :
    cutHead idx topology rev hKept x t =
      cutLeft idx topology rev hKept
        (RefinementCore.keptClassIndex topology
          ⟨endClass topology x, keptClass_endClass topology x⟩) :=
  dite_eq_right (fun hc ↦ h hc.1)

/-- **The last piece of a kept slot ends where the row leaves the
occurrence.** -/
theorem cutHead_of_last {x : SlotIndex iface face} {t : ℕ}
    (ht : t + 1 = pieceCount iface face idx x) :
    cutHead idx topology rev hKept x t =
      cutLeft idx topology rev hKept
        (RefinementCore.keptClassIndex topology
          ⟨endClass topology x, keptClass_endClass topology x⟩) := by
  by_cases h : Straddles iface face idx x
  · have h2 := pieceCount_of_straddles idx h
    exact cutHead_of_ne_zero idx topology rev hKept (by omega)
  · exact cutHead_of_not_straddles idx topology rev hKept h t

end CutVertices

/-! ## 4.  The endpoints of a refined slot, unfolded -/

section Generic

variable {source : PackedSpec} {data : SegmentData source}

theorem segmentTailVertex_of_zero
    {y : Σ i : Fin source.p, Fin (data.segments i).length} (h : (y.2 : ℕ) = 0) :
    RefinementCore.segmentTailVertex data y = Sum.inl (source.spec.core.tail y.1) :=
  dite_eq_left h

theorem segmentTailVertex_of_ne_zero
    {y : Σ i : Fin source.p, Fin (data.segments i).length} (h : (y.2 : ℕ) ≠ 0)
    {k : Fin ((data.segments y.1).length - 1)} (hk : (k : ℕ) + 1 = (y.2 : ℕ)) :
    RefinementCore.segmentTailVertex data y = Sum.inr ⟨y.1, k⟩ := by
  refine (dite_eq_right h).trans (congrArg (fun m ↦ Sum.inr (Sigma.mk y.1 m)) (Fin.ext ?_))
  show (y.2 : ℕ) - 1 = (k : ℕ)
  omega

theorem segmentHeadVertex_of_last
    {y : Σ i : Fin source.p, Fin (data.segments i).length}
    (h : (y.2 : ℕ) + 1 = (data.segments y.1).length) :
    RefinementCore.segmentHeadVertex data y = Sum.inl (source.spec.core.head y.1) :=
  dite_eq_left h

theorem segmentHeadVertex_of_not_last
    {y : Σ i : Fin source.p, Fin (data.segments i).length}
    (h : (y.2 : ℕ) + 1 ≠ (data.segments y.1).length)
    {k : Fin ((data.segments y.1).length - 1)} (hk : (k : ℕ) = (y.2 : ℕ)) :
    RefinementCore.segmentHeadVertex data y = Sum.inr ⟨y.1, k⟩ := by
  refine (dite_eq_right h).trans (congrArg (fun m ↦ Sum.inr (Sigma.mk y.1 m)) (Fin.ext ?_))
  show (y.2 : ℕ) = (k : ℕ)
  omega

end Generic

/-! ## 5.  The two ends of a kept slot, located on the walk -/

section Ends

variable (idx : RetainedIndex spec F small)
  (topology : ClearedFace.SourceContractionTopology face)
  (rev : SlotIndex iface face → Bool)
  (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)

theorem cutSlot_tail (x : SlotIndex iface face) :
    (packed (ClearedFace.SourceContractionTopology.prunedSpec topology hKept)).spec.core.tail
        (cutSlot topology hKept x) =
      (ClearedFace.SourceContractionTopology.prunedSpec topology hKept).core.tail
        (RefinementCore.keptSlotIndex topology (keptSlotEquiv iface topology x)) := rfl

theorem cutSlot_head (x : SlotIndex iface face) :
    (packed (ClearedFace.SourceContractionTopology.prunedSpec topology hKept)).spec.core.head
        (cutSlot topology hKept x) =
      (ClearedFace.SourceContractionTopology.prunedSpec topology hKept).core.head
        (RefinementCore.keptSlotIndex topology (keptSlotEquiv iface topology x)) := rfl

theorem classOfCore_tail_keptSlotEquiv (x : SlotIndex iface face) :
    ClearedFace.SourceContractionTopology.classOfCore topology
        (topology.degSpec.core.tail (keptSlotEquiv iface topology x).val.val) =
      classOf topology (candidate.datum.sourceEnds (occurrence x)).1 := by
  rw [← ClearedFace.SourceContractionTopology.classOf_sourceEnds_fst,
    sourceEdgeAt_keptSlotEquiv]

theorem classOfCore_head_keptSlotEquiv (x : SlotIndex iface face) :
    ClearedFace.SourceContractionTopology.classOfCore topology
        (topology.degSpec.core.head (keptSlotEquiv iface topology x).val.val) =
      classOf topology (candidate.datum.sourceEnds (occurrence x)).2 := by
  rw [← ClearedFace.SourceContractionTopology.classOf_sourceEnds_snd,
    sourceEdgeAt_keptSlotEquiv]

/-- **The tail class of a kept slot of the pruned contracted spec** is the
class of the first named end of its occurrence. -/
theorem prunedSpec_tail_cutSlot (x : SlotIndex iface face)
    (c : {c : topology.degSpec.Class //
      ClearedFace.SourceContractionTopology.KeptClass topology c})
    (hc : (c : topology.degSpec.Class) =
      classOf topology (candidate.datum.sourceEnds (occurrence x)).1) :
    (packed (ClearedFace.SourceContractionTopology.prunedSpec topology hKept)).spec.core.tail
        (cutSlot topology hKept x) =
      RefinementCore.keptClassIndex topology c :=
  (cutSlot_tail topology hKept x).trans
    ((RefinementCore.prunedSpec_core_tail topology hKept (keptSlotEquiv iface topology x)).trans
      (congrArg (RefinementCore.keptClassIndex topology)
        (Subtype.ext ((classOfCore_tail_keptSlotEquiv topology x).trans hc.symm))))

/-- **and the head class is the class of the second.** -/
theorem prunedSpec_head_cutSlot (x : SlotIndex iface face)
    (c : {c : topology.degSpec.Class //
      ClearedFace.SourceContractionTopology.KeptClass topology c})
    (hc : (c : topology.degSpec.Class) =
      classOf topology (candidate.datum.sourceEnds (occurrence x)).2) :
    (packed (ClearedFace.SourceContractionTopology.prunedSpec topology hKept)).spec.core.head
        (cutSlot topology hKept x) =
      RefinementCore.keptClassIndex topology c :=
  (cutSlot_head topology hKept x).trans
    ((RefinementCore.prunedSpec_core_head topology hKept (keptSlotEquiv iface topology x)).trans
      (congrArg (RefinementCore.keptClassIndex topology)
        (Subtype.ext ((classOfCore_head_keptSlotEquiv topology x).trans hc.symm))))

theorem classOf_sourceEnds_fst_of_not_rev {x : SlotIndex iface face}
    (h : RetainedTraversal.reversedAt (strong := strong) x = false) :
    classOf topology (candidate.datum.sourceEnds (occurrence x)).1 = startClass topology x := by
  rw [RetainedTraversal.sourceEnds_occurrence_fst (strong := strong) x, h]
  rfl

theorem classOf_sourceEnds_fst_of_rev {x : SlotIndex iface face}
    (h : RetainedTraversal.reversedAt (strong := strong) x = true) :
    classOf topology (candidate.datum.sourceEnds (occurrence x)).1 = endClass topology x := by
  rw [RetainedTraversal.sourceEnds_occurrence_fst (strong := strong) x, h]
  rfl

theorem classOf_sourceEnds_snd_of_not_rev {x : SlotIndex iface face}
    (h : RetainedTraversal.reversedAt (strong := strong) x = false) :
    classOf topology (candidate.datum.sourceEnds (occurrence x)).2 = endClass topology x := by
  rw [RetainedTraversal.sourceEnds_occurrence_snd (strong := strong) x, h]
  rfl

theorem classOf_sourceEnds_snd_of_rev {x : SlotIndex iface face}
    (h : RetainedTraversal.reversedAt (strong := strong) x = true) :
    classOf topology (candidate.datum.sourceEnds (occurrence x)).2 = startClass topology x := by
  rw [RetainedTraversal.sourceEnds_occurrence_snd (strong := strong) x, h]
  rfl

end Ends

/-! ## 6.  The cut spec's own endpoint equations, in the two walk classes -/

section CutPair

variable (idx : RetainedIndex spec F small)
  (topology : ClearedFace.SourceContractionTopology face)
  (rev : SlotIndex iface face → Bool)
  (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)

/-- **A piece of a kept slot, read as a refined slot index of the cut.** -/
def cutPair (x : SlotIndex iface face)
    (q : Fin (cutSegs iface face idx topology rev hKept x).length) :
    Σ i : Fin (packed (ClearedFace.SourceContractionTopology.prunedSpec topology hKept)).p,
      Fin (((cutData iface face idx topology rev hKept).segments i).length) :=
  ⟨cutSlot topology hKept x, q⟩

theorem cutLeft_eq (c : Fin (ClearedFace.SourceContractionTopology.keptClasses topology).card) :
    cutLeft idx topology rev hKept c = Sum.inl (cutClass topology hKept c) := rfl

theorem length_cutPair (x : SlotIndex iface face)
    (q : Fin (cutSegs iface face idx topology rev hKept x).length) :
    ((cutData iface face idx topology rev hKept).segments
        (cutPair idx topology rev hKept x q).1).length = pieceCount iface face idx x :=
  length_cutData_segments idx topology rev hKept x

/-- **The tail of a piece, on a kept slot the row traverses forwards.** -/
theorem segmentTailVertex_cutPair_of_not_rev
    {x : SlotIndex iface face}
    (hr : RetainedTraversal.reversedAt (strong := strong) x = false)
    (q : Fin (cutSegs iface face idx topology rev hKept x).length) :
    RefinementCore.segmentTailVertex (cutData iface face idx topology rev hKept)
        (cutPair idx topology rev hKept x q) =
      cutTail idx topology rev hKept x (q : ℕ) := by
  have hlen := length_cutPair idx topology rev hKept x q
  have hq : (q : ℕ) < pieceCount iface face idx x := by
    have h1 := q.isLt
    have h2 := length_cutSegs_eq idx topology rev hKept x
    omega
  have hle := pieceCount_le_two idx x
  have hq2 : ((cutPair idx topology rev hKept x q).2 : ℕ) = (q : ℕ) := rfl
  by_cases h0 : (q : ℕ) = 0
  · refine (segmentTailVertex_of_zero (show ((cutPair idx topology rev hKept x q).2 : ℕ) = 0
      from h0)).trans ?_
    refine Eq.trans (congrArg Sum.inl (prunedSpec_tail_cutSlot topology hKept x
      ⟨startClass topology x, keptClass_startClass topology x⟩
      (classOf_sourceEnds_fst_of_not_rev topology hr).symm)) ?_
    rw [h0, cutTail_of_zero idx topology rev hKept x]
    rfl
  · have hstr : Straddles iface face idx x :=
      straddles_of_one_lt_pieceCount (x := x) idx (by omega)
    have hpf : 0 < ((cutData iface face idx topology rev hKept).segments
        (cutPair idx topology rev hKept x q).1).length - 1 := by
      have := pieceCount_of_straddles idx hstr
      omega
    refine (segmentTailVertex_of_ne_zero
      (show ((cutPair idx topology rev hKept x q).2 : ℕ) ≠ 0 from h0)
      (k := ⟨0, hpf⟩) (by
        have := pieceCount_of_straddles idx hstr
        show 0 + 1 = (q : ℕ)
        omega)).trans ?_
    exact (cutTail_of_ne_zero idx topology rev hKept h0 hstr).symm

/-- **The tail of a piece, on a kept slot the row traverses backwards.** -/
theorem segmentTailVertex_cutPair_of_rev
    {x : SlotIndex iface face}
    (hr : RetainedTraversal.reversedAt (strong := strong) x = true)
    (q : Fin (cutSegs iface face idx topology rev hKept x).length) :
    RefinementCore.segmentTailVertex (cutData iface face idx topology rev hKept)
        (cutPair idx topology rev hKept x q) =
      cutHead idx topology rev hKept x
        ((cutSegs iface face idx topology rev hKept x).length - 1 - (q : ℕ)) := by
  have hlen := length_cutPair idx topology rev hKept x q
  have hcs := length_cutSegs_eq idx topology rev hKept x
  have hq : (q : ℕ) < pieceCount iface face idx x := by
    have h1 := q.isLt
    omega
  have hle := pieceCount_le_two idx x
  have hq2 : ((cutPair idx topology rev hKept x q).2 : ℕ) = (q : ℕ) := rfl
  by_cases h0 : (q : ℕ) = 0
  · refine (segmentTailVertex_of_zero (show ((cutPair idx topology rev hKept x q).2 : ℕ) = 0
      from h0)).trans ?_
    refine Eq.trans (congrArg Sum.inl (prunedSpec_tail_cutSlot topology hKept x
      ⟨endClass topology x, keptClass_endClass topology x⟩
      (classOf_sourceEnds_fst_of_rev topology hr).symm)) ?_
    rw [cutHead_of_last idx topology rev hKept (x := x)
      (t := (cutSegs iface face idx topology rev hKept x).length - 1 - (q : ℕ)) (by omega)]
    rfl
  · have hstr : Straddles iface face idx x :=
      straddles_of_one_lt_pieceCount (x := x) idx (by omega)
    have h2 := pieceCount_of_straddles idx hstr
    have hpf : 0 < ((cutData iface face idx topology rev hKept).segments
        (cutPair idx topology rev hKept x q).1).length - 1 := by omega
    refine (segmentTailVertex_of_ne_zero
      (show ((cutPair idx topology rev hKept x q).2 : ℕ) ≠ 0 from h0)
      (k := ⟨0, hpf⟩) (by show 0 + 1 = (q : ℕ); omega)).trans ?_
    have hzero : (cutSegs iface face idx topology rev hKept x).length - 1 - (q : ℕ) = 0 := by
      omega
    rw [hzero]
    exact (cutHead_of_zero_of_straddles idx topology rev hKept hstr).symm

/-- **The head of a piece, on a kept slot the row traverses forwards.** -/
theorem segmentHeadVertex_cutPair_of_not_rev
    {x : SlotIndex iface face}
    (hr : RetainedTraversal.reversedAt (strong := strong) x = false)
    (q : Fin (cutSegs iface face idx topology rev hKept x).length) :
    RefinementCore.segmentHeadVertex (cutData iface face idx topology rev hKept)
        (cutPair idx topology rev hKept x q) =
      cutHead idx topology rev hKept x (q : ℕ) := by
  have hlen := length_cutPair idx topology rev hKept x q
  have hcs := length_cutSegs_eq idx topology rev hKept x
  have hq : (q : ℕ) < pieceCount iface face idx x := by
    have h1 := q.isLt
    omega
  have hle := pieceCount_le_two idx x
  have hq2 : ((cutPair idx topology rev hKept x q).2 : ℕ) = (q : ℕ) := rfl
  by_cases h0 : (q : ℕ) + 1 = pieceCount iface face idx x
  · refine (segmentHeadVertex_of_last (show ((cutPair idx topology rev hKept x q).2 : ℕ) + 1 =
      ((cutData iface face idx topology rev hKept).segments
        (cutPair idx topology rev hKept x q).1).length by omega)).trans ?_
    refine Eq.trans (congrArg Sum.inl (prunedSpec_head_cutSlot topology hKept x
      ⟨endClass topology x, keptClass_endClass topology x⟩
      (classOf_sourceEnds_snd_of_not_rev topology hr).symm)) ?_
    rw [cutHead_of_last idx topology rev hKept (x := x) (t := (q : ℕ)) h0]
    rfl
  · have hstr : Straddles iface face idx x :=
      straddles_of_one_lt_pieceCount (x := x) idx (by omega)
    have h2 := pieceCount_of_straddles idx hstr
    have hpf : 0 < ((cutData iface face idx topology rev hKept).segments
        (cutPair idx topology rev hKept x q).1).length - 1 := by omega
    refine (segmentHeadVertex_of_not_last
      (show ((cutPair idx topology rev hKept x q).2 : ℕ) + 1 ≠
        ((cutData iface face idx topology rev hKept).segments
          (cutPair idx topology rev hKept x q).1).length by omega)
      (k := ⟨0, hpf⟩) (by show (0 : ℕ) = (q : ℕ); omega)).trans ?_
    have hzero : (q : ℕ) = 0 := by omega
    rw [hzero]
    exact (cutHead_of_zero_of_straddles idx topology rev hKept hstr).symm

/-- **The head of a piece, on a kept slot the row traverses backwards.** -/
theorem segmentHeadVertex_cutPair_of_rev
    {x : SlotIndex iface face}
    (hr : RetainedTraversal.reversedAt (strong := strong) x = true)
    (q : Fin (cutSegs iface face idx topology rev hKept x).length) :
    RefinementCore.segmentHeadVertex (cutData iface face idx topology rev hKept)
        (cutPair idx topology rev hKept x q) =
      cutTail idx topology rev hKept x
        ((cutSegs iface face idx topology rev hKept x).length - 1 - (q : ℕ)) := by
  have hlen := length_cutPair idx topology rev hKept x q
  have hcs := length_cutSegs_eq idx topology rev hKept x
  have hq : (q : ℕ) < pieceCount iface face idx x := by
    have h1 := q.isLt
    omega
  have hle := pieceCount_le_two idx x
  have hq2 : ((cutPair idx topology rev hKept x q).2 : ℕ) = (q : ℕ) := rfl
  by_cases h0 : (q : ℕ) + 1 = pieceCount iface face idx x
  · refine (segmentHeadVertex_of_last (show ((cutPair idx topology rev hKept x q).2 : ℕ) + 1 =
      ((cutData iface face idx topology rev hKept).segments
        (cutPair idx topology rev hKept x q).1).length by omega)).trans ?_
    refine Eq.trans (congrArg Sum.inl (prunedSpec_head_cutSlot topology hKept x
      ⟨startClass topology x, keptClass_startClass topology x⟩
      (classOf_sourceEnds_snd_of_rev topology hr).symm)) ?_
    have hzero : (cutSegs iface face idx topology rev hKept x).length - 1 - (q : ℕ) = 0 := by
      omega
    rw [hzero, cutTail_of_zero idx topology rev hKept x]
    rfl
  · have hstr : Straddles iface face idx x :=
      straddles_of_one_lt_pieceCount (x := x) idx (by omega)
    have h2 := pieceCount_of_straddles idx hstr
    have hpf : 0 < ((cutData iface face idx topology rev hKept).segments
        (cutPair idx topology rev hKept x q).1).length - 1 := by omega
    refine (segmentHeadVertex_of_not_last
      (show ((cutPair idx topology rev hKept x q).2 : ℕ) + 1 ≠
        ((cutData iface face idx topology rev hKept).segments
          (cutPair idx topology rev hKept x q).1).length by omega)
      (k := ⟨0, hpf⟩) (by show (0 : ℕ) = (q : ℕ); omega)).trans ?_
    refine (cutTail_of_ne_zero idx topology rev hKept (t := (cutSegs iface face idx topology rev
      hKept x).length - 1 - (q : ℕ)) (by omega) hstr).symm

end CutPair

/-! ## 7.  Consecutive pieces along a retained row -/

section Adjacent

variable (idx : RetainedIndex spec F small)
  (topology : ClearedFace.SourceContractionTopology face)

/-- **Two kept slots in succession have the same end class.**  Everything the
row meets between them is contracted. -/
theorem endClass_eq_startClass_succ {x x' : SlotIndex iface face} (hrow : x.1 = x'.1)
    (hsucc : (x'.2 : ℕ) = (x.2 : ℕ) + 1) :
    endClass topology x = startClass topology x' := by
  obtain ⟨i, m⟩ := x
  obtain ⟨i', m'⟩ := x'
  simp only at hrow hsucc
  subst hrow
  show classOf topology (RetainedTraversal.rowWalk strong iface i
      (RetainedTraversal.position (iface := iface) (face := face) i m + 1)) =
    classOf topology (RetainedTraversal.rowWalk strong iface i
      (RetainedTraversal.position (iface := iface) (face := face) i m'))
  have hlt : RetainedTraversal.position (iface := iface) (face := face) i m <
      RetainedTraversal.position (iface := iface) (face := face) i m' :=
    RetainedTraversal.position_lt_position_iff.mpr (by rw [Fin.lt_def]; omega)
  refine RetainedTraversal.classOf_rowWalk_eq_of_zero_run topology (by omega)
    (RetainedTraversal.position_lt (iface := iface) (face := face) i m').le
    fun k hk hak hkb ↦ ?_
  exact RetainedTraversal.sourceLength_eq_zero_of_position_lt_of_lt_position hk m m'
    (by omega) (by omega) hkb

theorem length_cutBlocks (i : Fin p) :
    (cutBlocks iface face idx i).length = (positiveRow iface face i).length := by
  rw [cutBlocks, List.length_map, length_cutList_row]

theorem offset_cutBlocks_succ (x : SlotIndex iface face) :
    offset (cutBlocks iface face idx x.1) ((x.2 : ℕ) + 1) =
      offset (cutBlocks iface face idx x.1) (x.2 : ℕ) + pieceCount iface face idx x := by
  rw [offset_succ]
  exact congrArg (fun k ↦ offset (cutBlocks iface face idx x.1) (x.2 : ℕ) + k)
    (length_getD_map_cutList idx x)

theorem offset_cutBlocks_length (hTwo : CarriesAtMostTwo idx) (x : SlotIndex iface face) :
    offset (cutBlocks iface face idx x.1) (cutBlocks iface face idx x.1).length =
      (rowPieces iface face idx (slotRow x)).length := by
  rw [offset_length, ← rowPieces_slotRow_eq_flatten_cutBlocks idx hTwo x]

variable (rev : SlotIndex iface face → Bool)
  (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)

/-- **The two readings of one interior point of a retained row agree.**  If the
`t'`-th piece of the kept slot `x'` follows the `t`-th piece of the kept slot
`x` immediately along the row, then the core vertex the cut puts after the one
is the core vertex it puts before the other: either both are the new split
vertex of a single straddled kept slot, or the piece ends a kept slot and the
next one starts the next kept slot, and the two walk classes agree because
everything between them is contracted. -/
theorem cutHead_eq_cutTail_of_succ (hTwo : CarriesAtMostTwo idx)
    {x x' : SlotIndex iface face} (hrow : x.1 = x'.1)
    {t t' : ℕ} (ht : t < pieceCount iface face idx x)
    (ht' : t' < pieceCount iface face idx x')
    (hsucc : piecePos iface face idx x' t' = piecePos iface face idx x t + 1) :
    cutHead idx topology rev hKept x t = cutTail idx topology rev hKept x' t' := by
  by_cases hcase : Straddles iface face idx x ∧ t = 0
  · obtain ⟨hstr, rfl⟩ := hcase
    have h2 := pieceCount_of_straddles idx hstr
    have hone : piecePos iface face idx x 1 = piecePos iface face idx x' t' := by
      rw [hsucc, piecePos_eq, piecePos_eq]
    obtain ⟨rfl, hteq⟩ := piecePos_inj' idx hrow (t := 1) (t' := t') (by omega) ht' hone
    rw [cutHead_of_zero_of_straddles idx topology rev hKept hstr,
      cutTail_of_ne_zero idx topology rev hKept (by omega) hstr]
  · have hlast : t + 1 = pieceCount iface face idx x := by
      by_cases hstr : Straddles iface face idx x
      · have h2 := pieceCount_of_straddles idx hstr
        have : t ≠ 0 := fun h ↦ hcase ⟨hstr, h⟩
        omega
      · have h2 := pieceCount_of_not_straddles idx hstr
        omega
    have hoff : piecePos iface face idx x t + 1 =
        offset (cutBlocks iface face idx x.1) ((x.2 : ℕ) + 1) := by
      rw [offset_cutBlocks_succ idx x, piecePos_eq]
      omega
    have hbound : (x.2 : ℕ) + 1 < (positiveRow iface face x.1).length := by
      by_contra hcon
      have hx2 := x.2.isLt
      have heq : (x.2 : ℕ) + 1 = (cutBlocks iface face idx x.1).length := by
        rw [length_cutBlocks idx x.1]
        omega
      have htot : piecePos iface face idx x t + 1 =
          (rowPieces iface face idx (slotRow x)).length := by
        rw [hoff, heq, offset_cutBlocks_length idx hTwo x]
      have hlt' := piecePos_lt' idx hTwo x' ht'
      have hrw : (rowPieces iface face idx (slotRow x')).length =
          (rowPieces iface face idx (slotRow x)).length :=
        congrArg (fun e ↦ (rowPieces iface face idx e).length) (Subtype.ext hrow.symm)
      omega
    have hnext : piecePos iface face idx (⟨x.1, ⟨(x.2 : ℕ) + 1, hbound⟩⟩ : SlotIndex iface face) 0
        = piecePos iface face idx x' t' := by
      have h1 : piecePos iface face idx
          (⟨x.1, ⟨(x.2 : ℕ) + 1, hbound⟩⟩ : SlotIndex iface face) 0 =
          offset (cutBlocks iface face idx x.1) ((x.2 : ℕ) + 1) := rfl
      omega
    obtain ⟨hxx, htt⟩ := piecePos_inj' idx (x := (⟨x.1, ⟨(x.2 : ℕ) + 1, hbound⟩⟩ :
      SlotIndex iface face)) (x' := x') hrow (t := 0) (t' := t')
      (pieceCount_pos idx _) ht' hnext
    rw [cutHead_of_last idx topology rev hKept hlast, ← htt,
      cutTail_of_zero idx topology rev hKept x']
    refine congrArg (fun c ↦ cutLeft idx topology rev hKept
      (RefinementCore.keptClassIndex topology c)) (Subtype.ext ?_)
    exact endClass_eq_startClass_succ topology hrow
      (congrArg (fun z : SlotIndex iface face ↦ (z.2 : ℕ)) hxx.symm)

end Adjacent

/-! ## 8.  Which piece of which kept slot a prescribed segment is -/

section Block

variable (idx : RetainedIndex spec F small)
  (topology : ClearedFace.SourceContractionTopology face)
  (rev : SlotIndex iface face → Bool)
  (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
  (hTwo : CarriesAtMostTwo idx)

/-- **The kept slot carrying the `m`-th prescribed segment of the requested
slot `j`.** -/
def blockSlot (y : Σ j : Fin p', Fin ((Retained.segmentData iface face idx).segments j).length) :
    SlotIndex iface face :=
  (slotBlockEquiv iface face idx topology rev hKept hTwo y).1

/-- **and which of its pieces that is, in the order the row traverses them.** -/
def blockIndex (y : Σ j : Fin p', Fin ((Retained.segmentData iface face idx).segments j).length) :
    ℕ :=
  pieceIndex iface face idx topology rev hKept
    (slotBlockEquiv iface face idx topology rev hKept hTwo y).1
    ((slotBlockEquiv iface face idx topology rev hKept hTwo y).2 : ℕ)

theorem blockSlot_def
    (y : Σ j : Fin p', Fin ((Retained.segmentData iface face idx).segments j).length) :
    blockSlot idx topology rev hKept hTwo y =
      (slotBlockEquiv iface face idx topology rev hKept hTwo y).1 := rfl

theorem blockIndex_def
    (y : Σ j : Fin p', Fin ((Retained.segmentData iface face idx).segments j).length) :
    blockIndex idx topology rev hKept hTwo y =
      pieceIndex iface face idx topology rev hKept
        (slotBlockEquiv iface face idx topology rev hKept hTwo y).1
        ((slotBlockEquiv iface face idx topology rev hKept hTwo y).2 : ℕ) := rfl

theorem blockIndex_lt
    (y : Σ j : Fin p', Fin ((Retained.segmentData iface face idx).segments j).length) :
    blockIndex idx topology rev hKept hTwo y <
      pieceCount iface face idx (blockSlot idx topology rev hKept hTwo y) :=
  pieceIndex_lt iface face idx topology rev hKept _
    (slotBlockEquiv iface face idx topology rev hKept hTwo y).2.isLt

theorem cutRow_slotBlock
    (y : Σ j : Fin p', Fin ((Retained.segmentData iface face idx).segments j).length) :
    cutRowEquiv iface face idx topology rev hTwo hKept
        (slotBlockEquiv iface face idx topology rev hKept hTwo y) =
      retRowEquiv iface face idx y := by
  rw [slotBlockEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]

/-- **The kept slot lies on the row that carries the requested slot.** -/
theorem blockSlot_row
    (y : Σ j : Fin p', Fin ((Retained.segmentData iface face idx).segments j).length) :
    (blockSlot idx topology rev hKept hTwo y).1 = ↑(idx.owner y.1) :=
  congrArg (fun w : RowPos iface face idx ↦ (w.1 : Fin p))
    (cutRow_slotBlock idx topology rev hKept hTwo y)

/-- **and it sits at the prescribed place along it.** -/
theorem piecePos_blockIndex
    (y : Σ j : Fin p', Fin ((Retained.segmentData iface face idx).segments j).length) :
    piecePos iface face idx (blockSlot idx topology rev hKept hTwo y)
        (blockIndex idx topology rev hKept hTwo y) =
      retPos iface face idx y.1 (y.2 : ℕ) :=
  congrArg (fun w : RowPos iface face idx ↦ ((w.2 : Fin _) : ℕ))
    (cutRow_slotBlock idx topology rev hKept hTwo y)

end Block

/-! ## 9.  The handover points of the requested specification -/

/-- **A requested core vertex at which a retained row hands over** from the
first requested slot it carries to the second.  At the requested expansion model
these are exactly the markers (`RetainedFibre.IsMarker`); the predicate is phrased on the
`RetainedIndex` alone so that the vertex map can be defined by cases on it
without unfolding `ExpansionData`. -/
abbrev IsHandover (idx : RetainedIndex spec F small) (w : Fin n') : Prop :=
  ∃ j : Fin p', idx.pos j = 1 ∧ small.core.tail j = w

/-- **A breakpoint of a requested slot, read as one of its prescribed
segments**: the segment it follows. -/
def breakPair (idx : RetainedIndex spec F small)
    (y : Σ j : Fin p', Fin (((Retained.segmentData iface face idx).segments j).length - 1)) :
    Σ j : Fin p', Fin ((Retained.segmentData iface face idx).segments j).length :=
  ⟨y.1, ⟨(y.2 : ℕ), by have := y.2.isLt; omega⟩⟩

/-! ## 10.  The ends of a displayed row -/

theorem nonDanglingValency_start_pos
    (iface : InputInterface spec strong.toPresentation coordinates F) (i : Fin p) :
    0 < nonDanglingValency candidate.datum (strong.start (iface.slot i)) := by
  obtain ⟨edge, hedge⟩ := strong.exists_head (iface.slot i)
  have hmem : edge ∈ row iface i := List.mem_of_mem_head? (by rw [hedge]; rfl)
  exact ClearedFace.SourceContractionTopology.nonDanglingValency_pos_of_incident
    (strong.decomposes.not_isDangling_of_mem hmem)
    (strong.head_incident _ edge (by rw [hedge]; rfl))

theorem nonDanglingValency_finish_pos
    (iface : InputInterface spec strong.toPresentation coordinates F) (i : Fin p) :
    0 < nonDanglingValency candidate.datum (strong.finish (iface.slot i)) := by
  obtain ⟨edge, hedge⟩ : ∃ edge, (strong.toPresentation.path (iface.slot i)).getLast? = some edge :=
    ⟨_, List.getLast?_eq_getLast_of_ne_nil (strong.path_ne_nil _)⟩
  have hmem : edge ∈ row iface i := List.mem_of_mem_getLast? (by rw [hedge]; rfl)
  exact ClearedFace.SourceContractionTopology.nonDanglingValency_pos_of_incident
    (strong.decomposes.not_isDangling_of_mem hmem)
    (strong.getLast_incident _ edge (by rw [hedge]; rfl))

/-- **A faithful dictionary orients every displayed row.**  The stable core is
loopless, so a row whose two named ends coincide would place two distinct
stable core vertices at one quotient-source vertex.  This is the general-forest
form of `OrientedTraversal.RowDictionary.finish_ne_start_of_injective`, and it
costs `StrongRefinement.Faithful` instead of injectivity of a vertex map. -/
theorem finish_ne_start_of_faithful
    {iface : InputInterface spec strong.toPresentation coordinates F}
    (dict : CoreDictionary spec strong iface) (hF : Faithful dict) (i : Fin p) :
    strong.finish (iface.slot i) ≠ strong.start (iface.slot i) := by
  intro hEq
  refine spec.core_loopless i (hF ?_).symm
  rw [dict.head_eq i, dict.tail_eq i, hEq]

/-- **and therefore the walk along a row really ends at its finish vertex.** -/
theorem rowWalk_length_of_faithful
    {iface : InputInterface spec strong.toPresentation coordinates F}
    (dict : CoreDictionary spec strong iface) (hF : Faithful dict) (i : Fin p) :
    RetainedTraversal.rowWalk strong iface i (row iface i).length =
      strong.finish (iface.slot i) :=
  RetainedTraversal.rowWalk_length (Or.inr (finish_ne_start_of_faithful dict hF i))

theorem scaledPacked_core_tail
    (face : ClearedFace candidate strong.toPresentation coordinates) (j : Fin p') :
    (scaledPacked small face).spec.core.tail j = small.core.tail j := rfl

theorem scaledPacked_core_head
    (face : ClearedFace candidate strong.toPresentation coordinates) (j : Fin p') :
    (scaledPacked small face).spec.core.head j = small.core.head j := rfl

/-! ## 11.  The first and last kept slot of a row -/

section RowEnds

variable (idx : RetainedIndex spec F small)
  (topology : ClearedFace.SourceContractionTopology face)

/-- **The first piece of a row is the first piece of its first kept slot.** -/
theorem eq_zero_of_piecePos_eq_zero {x : SlotIndex iface face} {t : ℕ}
    (h : piecePos iface face idx x t = 0) : (x.2 : ℕ) = 0 ∧ t = 0 := by
  have h1 : piecePos iface face idx x t =
      offset (cutBlocks iface face idx x.1) (x.2 : ℕ) + t := rfl
  have hb : 0 < (positiveRow iface face x.1).length :=
    lt_of_le_of_lt (Nat.zero_le _) x.2.isLt
  have h2 : offset (cutBlocks iface face idx x.1) 1 =
      pieceCount iface face idx (⟨x.1, ⟨0, hb⟩⟩ : SlotIndex iface face) := by
    rw [offset_succ, offset_zero, Nat.zero_add]
    exact length_getD_map_cutList idx (⟨x.1, ⟨0, hb⟩⟩ : SlotIndex iface face)
  have h3 := pieceCount_pos idx (⟨x.1, ⟨0, hb⟩⟩ : SlotIndex iface face)
  refine ⟨?_, by omega⟩
  by_contra hne
  have hmono : offset (cutBlocks iface face idx x.1) 1 ≤
      offset (cutBlocks iface face idx x.1) (x.2 : ℕ) := offset_mono _ (by omega)
  omega

/-- **and the class the row is in before it is the class of the row's start
vertex**: everything earlier in the row is contracted. -/
theorem startClass_eq_start {x : SlotIndex iface face} (h0 : (x.2 : ℕ) = 0) :
    startClass topology x = classOf topology (strong.start (iface.slot x.1)) := by
  obtain ⟨i, m⟩ := x
  simp only at h0
  show classOf topology (RetainedTraversal.rowWalk strong iface i
    (RetainedTraversal.position (iface := iface) (face := face) i m)) = _
  rw [← RetainedTraversal.rowWalk_zero (strong := strong) (iface := iface) i]
  refine (RetainedTraversal.classOf_rowWalk_eq_of_zero_run topology (Nat.zero_le _)
    (RetainedTraversal.position_lt (iface := iface) (face := face) i m).le
    fun k hk _ hkb ↦ ?_).symm
  exact RetainedTraversal.sourceLength_eq_zero_of_lt_position_zero hk m hkb h0

/-- **The class the row is in after its last kept slot is the class of the
row's finish vertex.** -/
theorem endClass_eq_finish {iface : InputInterface spec strong.toPresentation coordinates F}
    (topology : ClearedFace.SourceContractionTopology face)
    (dict : CoreDictionary spec strong iface) (hF : Faithful dict)
    {x : SlotIndex iface face}
    (hlast : (x.2 : ℕ) + 1 = (positiveRow iface face x.1).length) :
    endClass topology x = classOf topology (strong.finish (iface.slot x.1)) := by
  obtain ⟨i, m⟩ := x
  simp only at hlast
  show classOf topology (RetainedTraversal.rowWalk strong iface i
    (RetainedTraversal.position (iface := iface) (face := face) i m + 1)) = _
  rw [← rowWalk_length_of_faithful dict hF i]
  refine RetainedTraversal.classOf_rowWalk_eq_of_zero_run topology
    (RetainedTraversal.position_lt (iface := iface) (face := face) i m) le_rfl
    fun k hk hak _ ↦ ?_
  exact RetainedTraversal.sourceLength_eq_zero_of_position_last_lt hk m (by omega) hlast

/-- **The retained blocks of a row exhaust it.** -/
theorem offset_rowBlocks_length (e : {i : Fin p // i ∉ F}) :
    offset (rowBlocks iface face idx e) (idx.carried e).length =
      (rowPieces iface face idx e).length := by
  have hlen : (rowBlocks iface face idx e).length = (idx.carried e).length := by
    rw [rowBlocks, List.length_map]
  rw [← hlen, offset_length, ← rowPieces_eq_flatten_rowBlocks]

/-- **and each of them moves the offset by its own prescribed length.** -/
theorem offset_rowBlocks_succ (j : Fin p') :
    offset (rowBlocks iface face idx (idx.owner j)) (idx.pos j + 1) =
      offset (rowBlocks iface face idx (idx.owner j)) (idx.pos j) +
        ((Retained.segmentData iface face idx).segments j).length := by
  rw [offset_succ]
  exact congrArg (fun k ↦ offset (rowBlocks iface face idx (idx.owner j)) (idx.pos j) + k)
    (length_getD_map_carried iface face idx j)

/-- **The last kept slot of a row, located from its last piece.** -/
theorem slot_last_of_piecePos_succ (hTwo : CarriesAtMostTwo idx) {x : SlotIndex iface face}
    {t : ℕ} (ht : t + 1 = pieceCount iface face idx x)
    (h : piecePos iface face idx x t + 1 = (rowPieces iface face idx (slotRow x)).length) :
    (x.2 : ℕ) + 1 = (positiveRow iface face x.1).length := by
  have hx2 := x.2.isLt
  by_contra hne
  have hbound : (x.2 : ℕ) + 1 < (positiveRow iface face x.1).length := by omega
  have h1 : piecePos iface face idx
      (⟨x.1, ⟨(x.2 : ℕ) + 1, hbound⟩⟩ : SlotIndex iface face) 0 =
      offset (cutBlocks iface face idx x.1) ((x.2 : ℕ) + 1) := rfl
  have h2 := offset_cutBlocks_succ idx x
  have h3 : piecePos iface face idx x t =
      offset (cutBlocks iface face idx x.1) (x.2 : ℕ) + t := rfl
  have h4 := piecePos_lt' idx hTwo (⟨x.1, ⟨(x.2 : ℕ) + 1, hbound⟩⟩ : SlotIndex iface face)
    (pieceCount_pos idx _)
  have h5 : (rowPieces iface face idx
      (slotRow (⟨x.1, ⟨(x.2 : ℕ) + 1, hbound⟩⟩ : SlotIndex iface face))).length =
      (rowPieces iface face idx (slotRow x)).length := rfl
  omega

end RowEnds

end General

/-! ## 12.  At the requested expansion model, markers are handovers -/

section Producer

variable {n₀ p₀ N Q : ℕ} {D : ExpansionData n₀ p₀ N Q} {spec₀ : SubdivisionGraph.Spec n₀ p₀}
  {hN : 0 < N} {hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e}
  {iface : InputInterface (D.bigSpec spec₀ hN hL) strong.toPresentation coordinates
    (expansionForest D)}

theorem retainedIndex_pos (hCond : D.Conditions spec₀.core) (j : Fin p₀) :
    (RetainedIndexProducer.retainedIndex hCond hN hL).pos j = if D.side j then 1 else 0 := rfl

theorem carried_owner (hCond : D.Conditions spec₀.core) (j : Fin p₀) :
    (RetainedIndexProducer.retainedIndex hCond hN hL).carried
        ((RetainedIndexProducer.retainedIndex hCond hN hL).owner j) =
      RetainedIndexProducer.kindCarried (D.kind (D.owner j)) := rfl

/-- **The three shapes of a carrier list at the requested expansion model**, with the position
the requested slot occupies in it. -/
theorem carrier_cases (hCond : D.Conditions spec₀.core) (j : Fin p₀) :
    (D.kind (D.owner j) = SlotKind.single j ∧
        (RetainedIndexProducer.retainedIndex hCond hN hL).pos j = 0) ∨
      (∃ j₂ : Fin p₀, D.kind (D.owner j) = SlotKind.double j j₂ ∧
        (RetainedIndexProducer.retainedIndex hCond hN hL).pos j = 0) ∨
      (∃ j₁ : Fin p₀, D.kind (D.owner j) = SlotKind.double j₁ j ∧
        (RetainedIndexProducer.retainedIndex hCond hN hL).pos j = 1) := by
  rcases ExpansionData.exists_carrier hCond j with ⟨hk, hs⟩ | ⟨j₂, hk, hs⟩ | ⟨j₁, hk, hs⟩
  · exact Or.inl ⟨hk, by rw [retainedIndex_pos, hs]; rfl⟩
  · exact Or.inr (Or.inl ⟨j₂, hk, by rw [retainedIndex_pos, hs]; rfl⟩)
  · exact Or.inr (Or.inr ⟨j₁, hk, by rw [retainedIndex_pos, hs]; rfl⟩)

/-- **A requested slot at carrier position one is the second half of a
double.** -/
theorem exists_double_of_pos_one (hCond : D.Conditions spec₀.core) {j : Fin p₀}
    (hpos : (RetainedIndexProducer.retainedIndex hCond hN hL).pos j = 1) :
    ∃ j₁ : Fin p₀, D.kind (D.owner j) = SlotKind.double j₁ j := by
  rcases carrier_cases (hN := hN) (hL := hL) hCond j with ⟨-, h0⟩ | ⟨-, -, h0⟩ | ⟨j₁, hk, -⟩
  · omega
  · omega
  · exact ⟨j₁, hk⟩

/-- **and a requested slot at carrier position zero is a single or the first
half of a double.** -/
theorem first_of_pos_zero (hCond : D.Conditions spec₀.core) {j : Fin p₀}
    (hpos : (RetainedIndexProducer.retainedIndex hCond hN hL).pos j = 0) :
    D.kind (D.owner j) = SlotKind.single j ∨
      ∃ j₂ : Fin p₀, D.kind (D.owner j) = SlotKind.double j j₂ := by
  rcases carrier_cases (hN := hN) (hL := hL) hCond j with ⟨hk, -⟩ | ⟨j₂, hk, -⟩ | ⟨-, -, h1⟩
  · exact Or.inl hk
  · exact Or.inr ⟨j₂, hk⟩
  · omega

/-- **No other requested slot begins at a marker.**  `MarkerIsolated` says no
other slot *ends* there; a slot beginning there would place the marker in the
image of `ExpansionData.fib` unless it is the second half of the same double,
which `SlotCompatible` forbids. -/
theorem eq_of_tail_eq_marker (hCond : D.Conditions spec₀.core)
    {e : Fin Q} {j₁ j₂ : Fin p₀} (hk : D.kind e = SlotKind.double j₁ j₂)
    {j : Fin p₀} (hj : spec₀.core.tail j = spec₀.core.head j₁) : j = j₂ := by
  rcases ExpansionData.exists_carrier hCond j with ⟨hk', -⟩ | ⟨j₂', hk', -⟩ | ⟨j₁', hk', -⟩
  · exact absurd
      (((ExpansionData.compatible_of_conditions hCond (D.owner j)).2.1 j hk').1.trans hj)
      (RetainedFibre.not_exists_fib_eq_marker hCond hk _)
  · exact absurd
      (((ExpansionData.compatible_of_conditions hCond (D.owner j)).2.2 j j₂' hk').1.trans hj)
      (RetainedFibre.not_exists_fib_eq_marker hCond hk _)
  · have hc := (ExpansionData.compatible_of_conditions hCond (D.owner j)).2.2 j₁' j hk'
    have hj1 : j₁' = j₁ :=
      RetainedFibre.eq_of_head_eq_marker hCond hk (hc.2.1.trans hj)
    have h1 := ExpansionData.owner_eq_of_double hCond hk'
    have h2 := ExpansionData.owner_eq_of_double hCond hk
    have hoe : D.owner j = e := by rw [← h1.1, hj1]; exact h2.1
    have heq : (SlotKind.double j₁' j : SlotKind p₀) = SlotKind.double j₁ j₂ := by
      rw [← hk', hoe]; exact hk
    simp only [SlotKind.double.injEq] at heq
    exact heq.2

/-- **A handover point is a marker.** -/
theorem isMarker_of_handover (hCond : D.Conditions spec₀.core) {w : Fin n₀}
    (h : IsHandover (RetainedIndexProducer.retainedIndex hCond hN hL) w) :
    RetainedFibre.IsMarker D spec₀.core w := by
  obtain ⟨j, hpos, hw⟩ := h
  obtain ⟨j₁, hk⟩ := exists_double_of_pos_one hCond hpos
  exact ⟨D.owner j, j₁, j, hk,
    (RetainedFibre.head_eq_tail_of_double hCond hk).trans hw⟩

/-- **and conversely.** -/
theorem handover_of_isMarker (hCond : D.Conditions spec₀.core) {w : Fin n₀}
    (h : RetainedFibre.IsMarker D spec₀.core w) :
    IsHandover (RetainedIndexProducer.retainedIndex hCond hN hL) w := by
  obtain ⟨e, j₁, j₂, hk, hw⟩ := h
  refine ⟨j₂, ?_, (RetainedFibre.head_eq_tail_of_double hCond hk).symm.trans hw⟩
  rw [retainedIndex_pos, (ExpansionData.owner_eq_of_double hCond hk).2.2.2]
  rfl

/-- **so a requested core vertex that is not a handover is the image of a model
core vertex.** -/
theorem exists_fib_of_not_handover (hCond : D.Conditions spec₀.core) {w : Fin n₀}
    (h : ¬ IsHandover (RetainedIndexProducer.retainedIndex hCond hN hL) w) :
    ∃ v : Fin N, D.fib v = w :=
  (RetainedFibre.isMarker_or_exists_fib hCond w).elim
    (fun hm ↦ absurd (handover_of_isMarker hCond hm) h) id

/-- **A handover point determines the requested slot that begins there.** -/
theorem handover_slot_unique (hCond : D.Conditions spec₀.core) {j j' : Fin p₀}
    (hpos' : (RetainedIndexProducer.retainedIndex hCond hN hL).pos j' = 1)
    (hw : spec₀.core.tail j = spec₀.core.tail j') : j = j' := by
  obtain ⟨j₁, hk⟩ := exists_double_of_pos_one hCond hpos'
  exact eq_of_tail_eq_marker hCond hk
    (hw.trans (RetainedFibre.head_eq_tail_of_double hCond hk).symm)

end Producer

/-! ## 13.  The vertex map -/

section VertexMap

variable {n₀ p₀ N Q : ℕ} {D : ExpansionData n₀ p₀ N Q} {spec₀ : SubdivisionGraph.Spec n₀ p₀}
  {hN : 0 < N} {hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e}
  {iface : InputInterface (D.bigSpec spec₀ hN hL) strong.toPresentation coordinates
    (expansionForest D)}

/-- **The class of a non-marker requested core vertex is kept.**  `Spanning`
puts every model core vertex at an end of a displayed row, and a row is
nonempty, so its end meets a surviving occurrence. -/
theorem keptClass_requestedClass
    (dict : CoreDictionary (D.bigSpec spec₀ hN hL) strong iface) (hSpan : Spanning dict)
    (topology : ClearedFace.SourceContractionTopology face) {w : Fin n₀}
    (hw : ∃ v : Fin N, D.fib v = w) :
    ClearedFace.SourceContractionTopology.KeptClass topology
      (RetainedFibre.requestedClass dict topology hw) := by
  refine ⟨dict.vertexAt hw.choose, rfl, ?_⟩
  rcases hSpan hw.choose with ⟨i, hi⟩ | ⟨i, hi⟩
  · rw [hi]
    exact nonDanglingValency_start_pos iface i
  · rw [hi]
    exact nonDanglingValency_finish_pos iface i

/-- The first prescribed segment of the requested slot that begins at a
handover point. -/
def handoverPair (hCond : D.Conditions spec₀.core)
    (face : ClearedFace candidate strong.toPresentation coordinates) {w : Fin n₀}
    (h : IsHandover (RetainedIndexProducer.retainedIndex hCond hN hL) w) :
    Σ j : Fin p₀, Fin ((Retained.segmentData iface face
      (RetainedIndexProducer.retainedIndex hCond hN hL)).segments j).length :=
  ⟨h.choose, ⟨0, RefinementCore.length_segments_pos _ _⟩⟩

variable (hCond : D.Conditions spec₀.core)
  (dict : CoreDictionary (D.bigSpec spec₀ hN hL) strong iface) (hSpan : Spanning dict)
  (topology : ClearedFace.SourceContractionTopology face)
  (rev : SlotIndex iface face → Bool)
  (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
  (hTwo : CarriesAtMostTwo (RetainedIndexProducer.retainedIndex hCond hN hL))

/-- **Where a requested core vertex goes.**  A handover point goes to the core
vertex of the cut spec that precedes the first piece of the requested slot that
begins there -- the new split vertex if the marker straddles a kept slot, and
the class the row is in at that occurrence boundary if it does not.  Every
other requested core vertex is the image of a whole fibre of model core
vertices (`RetainedFibre.isMarker_or_exists_fib`), and goes to that fibre's
common contraction class (`RetainedFibre.coreClass_eq_of_fib_eq`). -/
def coreVertex (w : Fin n₀) :
    RefinementCore.RefinedVertex (cutData iface face
      (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept) :=
  if h : IsHandover (RetainedIndexProducer.retainedIndex hCond hN hL) w then
    cutTail (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
      (blockSlot (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept hTwo
        (handoverPair hCond face h))
      (blockIndex (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept hTwo
        (handoverPair hCond face h))
  else
    cutLeft (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
      (RefinementCore.keptClassIndex topology
        ⟨RetainedFibre.requestedClass dict topology (exists_fib_of_not_handover hCond h),
          keptClass_requestedClass dict hSpan topology _⟩)

/-- **The vertex map of the retained core model.**  A breakpoint inside a
requested slot goes to the core vertex of the cut spec that follows the piece
it comes after; a requested core vertex goes where `coreVertex` sends it. -/
def cutVertex (v : RefinementCore.RefinedVertex (Retained.segmentData iface face
      (RetainedIndexProducer.retainedIndex hCond hN hL))) :
    RefinementCore.RefinedVertex (cutData iface face
      (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept) :=
  match v with
  | Sum.inl w => coreVertex hCond dict hSpan topology rev hKept hTwo w
  | Sum.inr y =>
      cutHead (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
        (blockSlot (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept hTwo
          (breakPair (RetainedIndexProducer.retainedIndex hCond hN hL) y))
        (blockIndex (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept hTwo
          (breakPair (RetainedIndexProducer.retainedIndex hCond hN hL) y))

theorem cutVertex_inl (w : Fin n₀) :
    cutVertex hCond dict hSpan topology rev hKept hTwo (Sum.inl w) =
      coreVertex hCond dict hSpan topology rev hKept hTwo w := rfl

theorem cutVertex_inr
    (y : Σ j : Fin p₀, Fin (((Retained.segmentData iface face
      (RetainedIndexProducer.retainedIndex hCond hN hL)).segments j).length - 1)) :
    cutVertex hCond dict hSpan topology rev hKept hTwo (Sum.inr y) =
      cutHead (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
        (blockSlot (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept hTwo
          (breakPair (RetainedIndexProducer.retainedIndex hCond hN hL) y))
        (blockIndex (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept hTwo
          (breakPair (RetainedIndexProducer.retainedIndex hCond hN hL) y)) := rfl

end VertexMap

/-! ## 14.  The vertex map matches the endpoints of every prescribed segment -/

section Endpoints

variable {n₀ p₀ N Q : ℕ} {D : ExpansionData n₀ p₀ N Q} {spec₀ : SubdivisionGraph.Spec n₀ p₀}
  {hN : 0 < N} {hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e}
  {iface : InputInterface (D.bigSpec spec₀ hN hL) strong.toPresentation coordinates
    (expansionForest D)}

theorem fib_tail_of_pos_zero (hCond : D.Conditions spec₀.core) {j : Fin p₀}
    (h0 : (RetainedIndexProducer.retainedIndex hCond hN hL).pos j = 0) :
    D.fib (D.bigCore.tail (D.owner j)) = spec₀.core.tail j := by
  rcases first_of_pos_zero hCond h0 with hk | ⟨j₂, hk⟩
  · exact ((ExpansionData.compatible_of_conditions hCond (D.owner j)).2.1 j hk).1
  · exact ((ExpansionData.compatible_of_conditions hCond (D.owner j)).2.2 j j₂ hk).1

theorem fib_head_of_last (hCond : D.Conditions spec₀.core) {j : Fin p₀}
    (hk : D.kind (D.owner j) = SlotKind.single j ∨
      ∃ j₁ : Fin p₀, D.kind (D.owner j) = SlotKind.double j₁ j) :
    D.fib (D.bigCore.head (D.owner j)) = spec₀.core.head j := by
  rcases hk with hk | ⟨j₁, hk⟩
  · exact ((ExpansionData.compatible_of_conditions hCond (D.owner j)).2.1 j hk).2
  · exact ((ExpansionData.compatible_of_conditions hCond (D.owner j)).2.2 j₁ j hk).2.2

theorem carried_length_eq (hCond : D.Conditions spec₀.core) (j : Fin p₀) :
    ((RetainedIndexProducer.retainedIndex hCond hN hL).carried
        ((RetainedIndexProducer.retainedIndex hCond hN hL).owner j)).length =
      (RetainedIndexProducer.kindCarried (D.kind (D.owner j))).length := rfl

/-- **A requested slot that no handover follows is the last on its row.** -/
theorem pos_succ_eq_carried_length (hCond : D.Conditions spec₀.core) {j : Fin p₀}
    (hk : D.kind (D.owner j) = SlotKind.single j ∨
      ∃ j₁ : Fin p₀, D.kind (D.owner j) = SlotKind.double j₁ j) :
    (RetainedIndexProducer.retainedIndex hCond hN hL).pos j + 1 =
      ((RetainedIndexProducer.retainedIndex hCond hN hL).carried
        ((RetainedIndexProducer.retainedIndex hCond hN hL).owner j)).length := by
  rcases hk with hk | ⟨j₁, hk⟩
  · rw [carried_length_eq hCond j, hk, retainedIndex_pos,
      (ExpansionData.owner_eq_of_single hCond hk).2]
    rfl
  · rw [carried_length_eq hCond j, hk, retainedIndex_pos,
      (ExpansionData.owner_eq_of_double hCond hk).2.2.2]
    rfl

theorem last_of_not_handover_head (hCond : D.Conditions spec₀.core) {j : Fin p₀}
    (h : ¬ IsHandover (RetainedIndexProducer.retainedIndex hCond hN hL) (spec₀.core.head j)) :
    D.kind (D.owner j) = SlotKind.single j ∨
      ∃ j₁ : Fin p₀, D.kind (D.owner j) = SlotKind.double j₁ j := by
  rcases carrier_cases (hN := hN) (hL := hL) hCond j with ⟨hk, -⟩ | ⟨j₂, hk, -⟩ | ⟨j₁, hk, -⟩
  · exact Or.inl hk
  · refine absurd ⟨j₂, ?_, (RetainedFibre.head_eq_tail_of_double hCond hk).symm⟩ h
    rw [retainedIndex_pos, (ExpansionData.owner_eq_of_double hCond hk).2.2.2]
    rfl
  · exact Or.inr ⟨j₁, hk⟩

theorem pos_zero_of_not_handover_tail (hCond : D.Conditions spec₀.core) {j : Fin p₀}
    (h : ¬ IsHandover (RetainedIndexProducer.retainedIndex hCond hN hL) (spec₀.core.tail j)) :
    (RetainedIndexProducer.retainedIndex hCond hN hL).pos j = 0 := by
  rcases carrier_cases (hN := hN) (hL := hL) hCond j with ⟨-, h0⟩ | ⟨-, -, h0⟩ | ⟨-, -, h1⟩
  · exact h0
  · exact h0
  · exact absurd ⟨j, h1, rfl⟩ h

variable (hCond : D.Conditions spec₀.core)
  (dict : CoreDictionary (D.bigSpec spec₀ hN hL) strong iface) (hSpan : Spanning dict)
  (topology : ClearedFace.SourceContractionTopology face)
  (rev : SlotIndex iface face → Bool)
  (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
  (hTwo : CarriesAtMostTwo (RetainedIndexProducer.retainedIndex hCond hN hL))

theorem coreVertex_of_handover {w : Fin n₀}
    (h : IsHandover (RetainedIndexProducer.retainedIndex hCond hN hL) w) :
    coreVertex hCond dict hSpan topology rev hKept hTwo w =
      cutTail (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
        (blockSlot (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept hTwo
          (handoverPair hCond face h))
        (blockIndex (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept hTwo
          (handoverPair hCond face h)) :=
  dite_eq_left h

theorem coreVertex_of_not_handover {w : Fin n₀}
    (h : ¬ IsHandover (RetainedIndexProducer.retainedIndex hCond hN hL) w) :
    coreVertex hCond dict hSpan topology rev hKept hTwo w =
      cutLeft (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
        (RefinementCore.keptClassIndex topology
          ⟨RetainedFibre.requestedClass dict topology (exists_fib_of_not_handover hCond h),
            keptClass_requestedClass dict hSpan topology _⟩) :=
  dite_eq_right h

/-- **The fibre class of the tail of a first requested slot is the class the
row is in before its first kept slot.** -/
theorem requestedClass_eq_startClass
    {y : Σ j : Fin p₀, Fin ((Retained.segmentData iface face
      (RetainedIndexProducer.retainedIndex hCond hN hL)).segments j).length}
    (h0' : (RetainedIndexProducer.retainedIndex hCond hN hL).pos y.1 = 0)
    (hx0 : ((blockSlot (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
      hTwo y).2 : ℕ) = 0)
    (hw : ∃ v : Fin N, D.fib v = spec₀.core.tail y.1) :
    RetainedFibre.requestedClass dict topology hw =
      startClass topology
        (blockSlot (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
          hTwo y) := by
  refine Eq.trans (RetainedFibre.requestedClass_eq hCond dict topology hw
    (fib_tail_of_pos_zero hCond h0')) ?_
  refine Eq.trans ?_ (startClass_eq_start topology hx0).symm
  show classOf topology
    (dict.vertexAt ((D.bigSpec spec₀ hN hL).core.tail (D.owner y.1))) = _
  rw [dict.tail_eq (D.owner y.1), blockSlot_row]
  rfl

/-- **The vertex map sends the start of a prescribed segment where the cut
spec puts it.**  Inside a requested slot this is the adjacency lemma
`cutHead_eq_cutTail_of_succ`; at the start of a requested slot it is the
handover case of `coreVertex` when a marker sits there, and otherwise
`RetainedFibre`'s fibre class, reached across the contracted run at the
beginning of the row. -/
theorem cutVertex_segmentTailVertex
    (y : Σ j : Fin p₀, Fin ((Retained.segmentData iface face
      (RetainedIndexProducer.retainedIndex hCond hN hL)).segments j).length) :
    cutVertex hCond dict hSpan topology rev hKept hTwo
        (RefinementCore.segmentTailVertex (Retained.segmentData iface face
          (RetainedIndexProducer.retainedIndex hCond hN hL)) y) =
      cutTail (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
        (blockSlot (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept hTwo y)
        (blockIndex (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept hTwo
          y) := by
  have hy := y.2.isLt
  by_cases h0 : (y.2 : ℕ) = 0
  · rw [segmentTailVertex_of_zero h0, scaledPacked_core_tail, cutVertex_inl]
    by_cases h : IsHandover (RetainedIndexProducer.retainedIndex hCond hN hL)
        (spec₀.core.tail y.1)
    · rw [coreVertex_of_handover hCond dict hSpan topology rev hKept hTwo h]
      have hpair : handoverPair hCond face h = y := by
        refine sigma_fin_ext ?_ ?_
        · exact (handover_slot_unique hCond h.choose_spec.1 h.choose_spec.2.symm).symm
        · show (0 : ℕ) = (y.2 : ℕ)
          omega
      rw [hpair]
    · rw [coreVertex_of_not_handover hCond dict hSpan topology rev hKept hTwo h]
      have h0' : (RetainedIndexProducer.retainedIndex hCond hN hL).pos y.1 = 0 :=
        pos_zero_of_not_handover_tail hCond h
      have hp : piecePos iface face (RetainedIndexProducer.retainedIndex hCond hN hL)
          (blockSlot (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
            hTwo y)
          (blockIndex (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
            hTwo y) = 0 := by
        rw [piecePos_blockIndex, retPos_eq, h0', h0, offset_zero]
      obtain ⟨hx0, ht0⟩ :=
        eq_zero_of_piecePos_eq_zero (RetainedIndexProducer.retainedIndex hCond hN hL) hp
      rw [ht0, cutTail_of_zero]
      exact congrArg (fun c ↦ cutLeft (RetainedIndexProducer.retainedIndex hCond hN hL)
        topology rev hKept (RefinementCore.keptClassIndex topology c))
        (Subtype.ext (requestedClass_eq_startClass hCond dict topology rev hKept hTwo
          h0' hx0 _))
  · have hpf : (y.2 : ℕ) - 1 < ((Retained.segmentData iface face
        (RetainedIndexProducer.retainedIndex hCond hN hL)).segments y.1).length - 1 := by omega
    rw [segmentTailVertex_of_ne_zero h0 (k := ⟨(y.2 : ℕ) - 1, hpf⟩)
        (show ((y.2 : ℕ) - 1) + 1 = (y.2 : ℕ) by omega),
      cutVertex_inr]
    refine cutHead_eq_cutTail_of_succ (RetainedIndexProducer.retainedIndex hCond hN hL)
      topology rev hKept hTwo
      ((blockSlot_row (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept hTwo
          (breakPair (RetainedIndexProducer.retainedIndex hCond hN hL)
            ⟨y.1, ⟨(y.2 : ℕ) - 1, hpf⟩⟩)).trans
        (blockSlot_row (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
          hTwo y).symm)
      (blockIndex_lt (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept hTwo
        (breakPair (RetainedIndexProducer.retainedIndex hCond hN hL)
          ⟨y.1, ⟨(y.2 : ℕ) - 1, hpf⟩⟩))
      (blockIndex_lt (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
        hTwo y) ?_
    rw [piecePos_blockIndex, piecePos_blockIndex, retPos_eq, retPos_eq]
    show offset (rowBlocks iface face (RetainedIndexProducer.retainedIndex hCond hN hL)
        ((RetainedIndexProducer.retainedIndex hCond hN hL).owner y.1))
        ((RetainedIndexProducer.retainedIndex hCond hN hL).pos y.1) + (y.2 : ℕ) =
      offset (rowBlocks iface face (RetainedIndexProducer.retainedIndex hCond hN hL)
        ((RetainedIndexProducer.retainedIndex hCond hN hL).owner y.1))
        ((RetainedIndexProducer.retainedIndex hCond hN hL).pos y.1) + ((y.2 : ℕ) - 1) + 1
    omega

/-- **The handover point at the far end of a requested slot lies on the same
retained row**, one place further along. -/
theorem handover_owner_eq (hCond : D.Conditions spec₀.core) {j j₀ : Fin p₀}
    (hpos : (RetainedIndexProducer.retainedIndex hCond hN hL).pos j₀ = 1)
    (hw : spec₀.core.tail j₀ = spec₀.core.head j) :
    (RetainedIndexProducer.retainedIndex hCond hN hL).owner j =
        (RetainedIndexProducer.retainedIndex hCond hN hL).owner j₀ ∧
      (RetainedIndexProducer.retainedIndex hCond hN hL).pos j = 0 := by
  obtain ⟨j₁, hk⟩ := exists_double_of_pos_one hCond hpos
  have hj1 : j = j₁ :=
    RetainedFibre.eq_of_head_eq_marker hCond hk
      (hw.symm.trans (RetainedFibre.head_eq_tail_of_double hCond hk).symm)
  obtain ⟨ho, hs, -, -⟩ := ExpansionData.owner_eq_of_double hCond hk
  refine ⟨Subtype.ext ?_, ?_⟩
  · show D.owner j = D.owner j₀
    rw [hj1, ho]
  · rw [retainedIndex_pos, hj1, hs]
    rfl

variable (hF : Faithful dict)

include hF in
/-- **The fibre class of the head of a last requested slot is the class the row
is in after its last kept slot.** -/
theorem requestedClass_eq_endClass
    {y : Σ j : Fin p₀, Fin ((Retained.segmentData iface face
      (RetainedIndexProducer.retainedIndex hCond hN hL)).segments j).length}
    (hk : D.kind (D.owner y.1) = SlotKind.single y.1 ∨
      ∃ j₁ : Fin p₀, D.kind (D.owner y.1) = SlotKind.double j₁ y.1)
    (hxlast : ((blockSlot (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
        hTwo y).2 : ℕ) + 1 =
      (positiveRow iface face (blockSlot (RetainedIndexProducer.retainedIndex hCond hN hL)
        topology rev hKept hTwo y).1).length)
    (hw : ∃ v : Fin N, D.fib v = spec₀.core.head y.1) :
    RetainedFibre.requestedClass dict topology hw =
      endClass topology
        (blockSlot (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
          hTwo y) := by
  refine Eq.trans (RetainedFibre.requestedClass_eq hCond dict topology hw
    (fib_head_of_last hCond hk)) ?_
  refine Eq.trans ?_ (endClass_eq_finish topology dict hF hxlast).symm
  show classOf topology
    (dict.vertexAt ((D.bigSpec spec₀ hN hL).core.head (D.owner y.1))) = _
  rw [dict.head_eq (D.owner y.1), blockSlot_row]
  rfl

include hF in
/-- **The vertex map sends the end of a prescribed segment where the cut spec
puts it.**  Inside a requested slot it is the breakpoint case of `cutVertex`,
true by definition; at the end of a requested slot it is the handover case
through the adjacency lemma when a marker follows, and otherwise
`RetainedFibre`'s fibre class, reached across the contracted run at the end of
the row. -/
theorem cutVertex_segmentHeadVertex
    (y : Σ j : Fin p₀, Fin ((Retained.segmentData iface face
      (RetainedIndexProducer.retainedIndex hCond hN hL)).segments j).length) :
    cutVertex hCond dict hSpan topology rev hKept hTwo
        (RefinementCore.segmentHeadVertex (Retained.segmentData iface face
          (RetainedIndexProducer.retainedIndex hCond hN hL)) y) =
      cutHead (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
        (blockSlot (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept hTwo y)
        (blockIndex (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept hTwo
          y) := by
  have hy := y.2.isLt
  by_cases hlast : (y.2 : ℕ) + 1 = ((Retained.segmentData iface face
      (RetainedIndexProducer.retainedIndex hCond hN hL)).segments y.1).length
  · rw [segmentHeadVertex_of_last hlast, scaledPacked_core_head, cutVertex_inl]
    by_cases h : IsHandover (RetainedIndexProducer.retainedIndex hCond hN hL)
        (spec₀.core.head y.1)
    · rw [coreVertex_of_handover hCond dict hSpan topology rev hKept hTwo h]
      obtain ⟨howner, hpos0⟩ := handover_owner_eq hCond h.choose_spec.1 h.choose_spec.2
      refine (cutHead_eq_cutTail_of_succ (RetainedIndexProducer.retainedIndex hCond hN hL)
        topology rev hKept hTwo
        ((blockSlot_row (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
            hTwo y).trans ?_)
        (blockIndex_lt (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
          hTwo y)
        (blockIndex_lt (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
          hTwo (handoverPair hCond face h)) ?_).symm
      · exact (congrArg Subtype.val howner).trans
          (blockSlot_row (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
            hTwo (handoverPair hCond face h)).symm
      · rw [piecePos_blockIndex, piecePos_blockIndex, retPos_eq, retPos_eq]
        have hone := offset_rowBlocks_one (iface := iface) (face := face)
          (RetainedIndexProducer.retainedIndex hCond hN hL) hpos0
        have hpos1 : (RetainedIndexProducer.retainedIndex hCond hN hL).pos
            (handoverPair (iface := iface) hCond face h).1 = 1 := h.choose_spec.1
        have hrb : offset (rowBlocks iface face
            (RetainedIndexProducer.retainedIndex hCond hN hL)
            ((RetainedIndexProducer.retainedIndex hCond hN hL).owner
              (handoverPair (iface := iface) hCond face h).1)) 1 =
            offset (rowBlocks iface face
              (RetainedIndexProducer.retainedIndex hCond hN hL)
              ((RetainedIndexProducer.retainedIndex hCond hN hL).owner y.1)) 1 :=
          congrArg (fun e ↦ offset (rowBlocks iface face
            (RetainedIndexProducer.retainedIndex hCond hN hL) e) 1) howner.symm
        have hzero : ((handoverPair (iface := iface) hCond face h).2 : ℕ) = 0 := rfl
        rw [hpos1, hzero, hpos0, hrb, hone, offset_zero]
        omega
    · rw [coreVertex_of_not_handover hCond dict hSpan topology rev hKept hTwo h]
      have hk := last_of_not_handover_head hCond h
      have hretlast : retPos iface face (RetainedIndexProducer.retainedIndex hCond hN hL)
          y.1 (y.2 : ℕ) + 1 =
          (rowPieces iface face (RetainedIndexProducer.retainedIndex hCond hN hL)
            ((RetainedIndexProducer.retainedIndex hCond hN hL).owner y.1)).length := by
        have h1 := offset_rowBlocks_succ (iface := iface) (face := face)
          (RetainedIndexProducer.retainedIndex hCond hN hL) y.1
        have h2 := offset_rowBlocks_length (iface := iface) (face := face)
          (RetainedIndexProducer.retainedIndex hCond hN hL)
          ((RetainedIndexProducer.retainedIndex hCond hN hL).owner y.1)
        have h3 := pos_succ_eq_carried_length (hN := hN) (hL := hL) hCond hk
        have h4 : retPos iface face (RetainedIndexProducer.retainedIndex hCond hN hL)
            y.1 (y.2 : ℕ) = offset (rowBlocks iface face
              (RetainedIndexProducer.retainedIndex hCond hN hL)
              ((RetainedIndexProducer.retainedIndex hCond hN hL).owner y.1))
              ((RetainedIndexProducer.retainedIndex hCond hN hL).pos y.1) + (y.2 : ℕ) := rfl
        rw [← h3] at h2
        omega
      have hrow : slotRow (blockSlot (RetainedIndexProducer.retainedIndex hCond hN hL)
          topology rev hKept hTwo y) =
          (RetainedIndexProducer.retainedIndex hCond hN hL).owner y.1 :=
        Subtype.ext (blockSlot_row (RetainedIndexProducer.retainedIndex hCond hN hL) topology
          rev hKept hTwo y)
      have hpp : piecePos iface face (RetainedIndexProducer.retainedIndex hCond hN hL)
          (blockSlot (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
            hTwo y)
          (blockIndex (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
            hTwo y) + 1 =
          (rowPieces iface face (RetainedIndexProducer.retainedIndex hCond hN hL)
            (slotRow (blockSlot (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev
              hKept hTwo y))).length := by
        rw [piecePos_blockIndex, hrow]
        exact hretlast
      have hbi : blockIndex (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev
          hKept hTwo y + 1 =
          pieceCount iface face (RetainedIndexProducer.retainedIndex hCond hN hL)
            (blockSlot (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
              hTwo y) := by
        have hlt := blockIndex_lt (RetainedIndexProducer.retainedIndex hCond hN hL) topology
          rev hKept hTwo y
        by_contra hne
        have hnext := piecePos_lt' (RetainedIndexProducer.retainedIndex hCond hN hL) hTwo
          (blockSlot (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
            hTwo y)
          (t := blockIndex (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev
            hKept hTwo y + 1) (by omega)
        have hstep : piecePos iface face (RetainedIndexProducer.retainedIndex hCond hN hL)
            (blockSlot (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
              hTwo y)
            (blockIndex (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
              hTwo y + 1) =
            piecePos iface face (RetainedIndexProducer.retainedIndex hCond hN hL)
              (blockSlot (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
                hTwo y)
              (blockIndex (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
                hTwo y) + 1 := by
          rw [piecePos_eq, piecePos_eq]
          omega
        omega
      rw [cutHead_of_last (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
        hbi]
      exact congrArg (fun c ↦ cutLeft (RetainedIndexProducer.retainedIndex hCond hN hL)
        topology rev hKept (RefinementCore.keptClassIndex topology c))
        (Subtype.ext (requestedClass_eq_endClass hCond dict topology rev hKept hTwo hF hk
          (slot_last_of_piecePos_succ (RetainedIndexProducer.retainedIndex hCond hN hL) hTwo
            hbi hpp) _))
  · rw [segmentHeadVertex_of_not_last hlast (k := ⟨(y.2 : ℕ), by omega⟩) rfl, cutVertex_inr]
    rfl

end Endpoints

/-! ## 15.  The endpoint equations -/

section Equations

variable {n₀ p₀ N Q : ℕ} {D : ExpansionData n₀ p₀ N Q} {spec₀ : SubdivisionGraph.Spec n₀ p₀}
  {hN : 0 < N} {hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e}
  {iface : InputInterface (D.bigSpec spec₀ hN hL) strong.toPresentation coordinates
    (expansionForest D)}

variable (hCond : D.Conditions spec₀.core)
  (dict : CoreDictionary (D.bigSpec spec₀ hN hL) strong iface) (hSpan : Spanning dict)
  (topology : ClearedFace.SourceContractionTopology face)
  (rev : SlotIndex iface face → Bool)
  (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
  (hTwo : CarriesAtMostTwo (RetainedIndexProducer.retainedIndex hCond hN hL))

theorem cutSpec_tail_slotModel
    (x : Σ j : Fin p₀, Fin ((Retained.segmentData iface face
      (RetainedIndexProducer.retainedIndex hCond hN hL)).segments j).length) :
    (cutSpec iface face (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev
          hKept).spec.core.tail
        (slotModel iface face (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev
          hKept hTwo x) =
      RefinementCore.vertexIndexEquiv
        (cutData iface face (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept)
        (RefinementCore.segmentTailVertex
          (cutData iface face (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev
            hKept)
          (cutPair (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
            (slotBlockEquiv iface face (RetainedIndexProducer.retainedIndex hCond hN hL)
              topology rev hKept hTwo x).1
            (slotBlockEquiv iface face (RetainedIndexProducer.retainedIndex hCond hN hL)
              topology rev hKept hTwo x).2)) :=
  RefinementCore.refineAllSlots_tail_at _ _

theorem cutSpec_head_slotModel
    (x : Σ j : Fin p₀, Fin ((Retained.segmentData iface face
      (RetainedIndexProducer.retainedIndex hCond hN hL)).segments j).length) :
    (cutSpec iface face (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev
          hKept).spec.core.head
        (slotModel iface face (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev
          hKept hTwo x) =
      RefinementCore.vertexIndexEquiv
        (cutData iface face (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept)
        (RefinementCore.segmentHeadVertex
          (cutData iface face (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev
            hKept)
          (cutPair (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
            (slotBlockEquiv iface face (RetainedIndexProducer.retainedIndex hCond hN hL)
              topology rev hKept hTwo x).1
            (slotBlockEquiv iface face (RetainedIndexProducer.retainedIndex hCond hN hL)
              topology rev hKept hTwo x).2)) :=
  RefinementCore.refineAllSlots_head_at _ _

variable (hF : Faithful dict)

include hF in
/-- **The tail equation, on the cut side.** -/
theorem cut_tail_eq
    (hrev : ∀ z : SlotIndex iface face,
      rev z = RetainedTraversal.reversedAt (strong := strong) z)
    (x : Σ j : Fin p₀, Fin ((Retained.segmentData iface face
      (RetainedIndexProducer.retainedIndex hCond hN hL)).segments j).length) :
    RefinementCore.segmentTailVertex
        (cutData iface face (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept)
        (cutPair (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
          (slotBlockEquiv iface face (RetainedIndexProducer.retainedIndex hCond hN hL)
            topology rev hKept hTwo x).1
          (slotBlockEquiv iface face (RetainedIndexProducer.retainedIndex hCond hN hL)
            topology rev hKept hTwo x).2) =
      cutVertex hCond dict hSpan topology rev hKept hTwo
        (if reversedSlot iface face (RetainedIndexProducer.retainedIndex hCond hN hL) topology
            rev hKept hTwo x then
          RefinementCore.segmentHeadVertex (Retained.segmentData iface face
            (RetainedIndexProducer.retainedIndex hCond hN hL)) x
        else RefinementCore.segmentTailVertex (Retained.segmentData iface face
            (RetainedIndexProducer.retainedIndex hCond hN hL)) x) := by
  refine (Bool.eq_false_or_eq_true
    (rev (slotBlockEquiv iface face (RetainedIndexProducer.retainedIndex hCond hN hL) topology
      rev hKept hTwo x).1)).symm.elim (fun hb => ?_) (fun hb => ?_)
  · rw [show reversedSlot iface face (RetainedIndexProducer.retainedIndex hCond hN hL) topology
        rev hKept hTwo x = false from hb, ite_eq_right Bool.false_ne_true,
      cutVertex_segmentTailVertex hCond dict hSpan topology rev hKept hTwo x,
      blockSlot_def, blockIndex_def,
      segmentTailVertex_cutPair_of_not_rev (RetainedIndexProducer.retainedIndex hCond hN hL)
        topology rev hKept (by rw [← hrev]; exact hb) _,
      pieceIndex_of_not_rev iface face (RetainedIndexProducer.retainedIndex hCond hN hL)
        topology rev hKept _ _ hb]
  · rw [show reversedSlot iface face (RetainedIndexProducer.retainedIndex hCond hN hL) topology
        rev hKept hTwo x = true from hb, ite_eq_left rfl,
      cutVertex_segmentHeadVertex hCond dict hSpan topology rev hKept hTwo hF x,
      blockSlot_def, blockIndex_def,
      segmentTailVertex_cutPair_of_rev (RetainedIndexProducer.retainedIndex hCond hN hL)
        topology rev hKept (by rw [← hrev]; exact hb) _,
      pieceIndex_of_rev iface face (RetainedIndexProducer.retainedIndex hCond hN hL)
        topology rev hKept _ _ hb]

include hF in
/-- **The head equation, on the cut side.** -/
theorem cut_head_eq
    (hrev : ∀ z : SlotIndex iface face,
      rev z = RetainedTraversal.reversedAt (strong := strong) z)
    (x : Σ j : Fin p₀, Fin ((Retained.segmentData iface face
      (RetainedIndexProducer.retainedIndex hCond hN hL)).segments j).length) :
    RefinementCore.segmentHeadVertex
        (cutData iface face (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept)
        (cutPair (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
          (slotBlockEquiv iface face (RetainedIndexProducer.retainedIndex hCond hN hL)
            topology rev hKept hTwo x).1
          (slotBlockEquiv iface face (RetainedIndexProducer.retainedIndex hCond hN hL)
            topology rev hKept hTwo x).2) =
      cutVertex hCond dict hSpan topology rev hKept hTwo
        (if reversedSlot iface face (RetainedIndexProducer.retainedIndex hCond hN hL) topology
            rev hKept hTwo x then
          RefinementCore.segmentTailVertex (Retained.segmentData iface face
            (RetainedIndexProducer.retainedIndex hCond hN hL)) x
        else RefinementCore.segmentHeadVertex (Retained.segmentData iface face
            (RetainedIndexProducer.retainedIndex hCond hN hL)) x) := by
  refine (Bool.eq_false_or_eq_true
    (rev (slotBlockEquiv iface face (RetainedIndexProducer.retainedIndex hCond hN hL) topology
      rev hKept hTwo x).1)).symm.elim (fun hb => ?_) (fun hb => ?_)
  · rw [show reversedSlot iface face (RetainedIndexProducer.retainedIndex hCond hN hL) topology
        rev hKept hTwo x = false from hb, ite_eq_right Bool.false_ne_true,
      cutVertex_segmentHeadVertex hCond dict hSpan topology rev hKept hTwo hF x,
      blockSlot_def, blockIndex_def,
      segmentHeadVertex_cutPair_of_not_rev (RetainedIndexProducer.retainedIndex hCond hN hL)
        topology rev hKept (by rw [← hrev]; exact hb) _,
      pieceIndex_of_not_rev iface face (RetainedIndexProducer.retainedIndex hCond hN hL)
        topology rev hKept _ _ hb]
  · rw [show reversedSlot iface face (RetainedIndexProducer.retainedIndex hCond hN hL) topology
        rev hKept hTwo x = true from hb, ite_eq_left rfl,
      cutVertex_segmentTailVertex hCond dict hSpan topology rev hKept hTwo x,
      blockSlot_def, blockIndex_def,
      segmentHeadVertex_cutPair_of_rev (RetainedIndexProducer.retainedIndex hCond hN hL)
        topology rev hKept (by rw [← hrev]; exact hb) _,
      pieceIndex_of_rev iface face (RetainedIndexProducer.retainedIndex hCond hN hL)
        topology rev hKept _ _ hb]

end Equations

/-! ## 16.  The vertex datum, and the cut relabelling it gives -/

section Headline

open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases.OuterWalk
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.StableSourceDarts
open DraismaVargas.LocalCases.TerminalExhausts

variable {n₀ p₀ N Q : ℕ} {D : ExpansionData n₀ p₀ N Q} {spec₀ : SubdivisionGraph.Spec n₀ p₀}
  {hN : 0 < N} {hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e}
  {iface : InputInterface (D.bigSpec spec₀ hN hL) strong.toPresentation coordinates
    (expansionForest D)}

/-- **The vertex map of the retained core model**, at the traversal's own orientation
`RetainedTraversal.reversedAt`: the composite of the case split `cutVertex` with
the naming `RefinementCore.vertexIndexEquiv` of the cut spec's core vertices. -/
def vertexModel (hCond : D.Conditions spec₀.core)
    (dict : CoreDictionary (D.bigSpec spec₀ hN hL) strong iface) (hSpan : Spanning dict)
    (topology : ClearedFace.SourceContractionTopology face)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty) :
    RefinementCore.RefinedVertex (Retained.segmentData iface face
        (RetainedIndexProducer.retainedIndex hCond hN hL)) →
      Fin (cutSpec iface face (RetainedIndexProducer.retainedIndex hCond hN hL) topology
        (RetainedTraversal.reversedAt (strong := strong) (iface := iface) (face := face))
        hKept).n :=
  fun v ↦ RefinementCore.vertexIndexEquiv
    (cutData iface face (RetainedIndexProducer.retainedIndex hCond hN hL) topology
      (RetainedTraversal.reversedAt (strong := strong) (iface := iface) (face := face)) hKept)
    (cutVertex hCond dict hSpan topology
      (RetainedTraversal.reversedAt (strong := strong) (iface := iface) (face := face)) hKept
      (RetainedCut.carried_length_le_two hCond hN hL) v)

/-- **The two endpoint equations of the retained core model hold for it.**  No
hypothesis beyond what `RetainedRelabeling.CutRelabeling` already keeps inside
its binder: `Faithful` orients every displayed row, `Spanning` makes the fibre
classes kept, and `hCond` is an output of the requested expansion model. -/
theorem endpointEquations (hCond : D.Conditions spec₀.core)
    (dict : CoreDictionary (D.bigSpec spec₀ hN hL) strong iface) (hSpan : Spanning dict)
    (hF : Faithful dict)
    (topology : ClearedFace.SourceContractionTopology face)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty) :
    RetainedCoreModel.EndpointEquations iface face
      (RetainedIndexProducer.retainedIndex hCond hN hL) topology
      (RetainedTraversal.reversedAt (strong := strong) (iface := iface) (face := face)) hKept
      (RetainedCut.carried_length_le_two hCond hN hL)
      (vertexModel hCond dict hSpan topology hKept) := by
  constructor
  · intro x
    exact (cutSpec_tail_slotModel hCond topology _ hKept
        (RetainedCut.carried_length_le_two hCond hN hL) x).trans
      (congrArg (RefinementCore.vertexIndexEquiv _)
        (cut_tail_eq hCond dict hSpan topology _ hKept
          (RetainedCut.carried_length_le_two hCond hN hL) hF (fun _ ↦ rfl) x))
  · intro x
    exact (cutSpec_head_slotModel hCond topology _ hKept
        (RetainedCut.carried_length_le_two hCond hN hL) x).trans
      (congrArg (RefinementCore.vertexIndexEquiv _)
        (cut_head_eq hCond dict hSpan topology _ hKept
          (RetainedCut.carried_length_le_two hCond hN hL) hF (fun _ ↦ rfl) x))

end Headline

section Receipt

open DraismaVargas.LocalCases.TerminalExhausts

variable {n₀ p₀ : ℕ} {D : ExpansionData n₀ p₀ (2 * (p₀ - n₀)) (3 * (p₀ - n₀))}
  {spec₀ : SubdivisionGraph.Spec n₀ p₀} {hN : 0 < 2 * (p₀ - n₀)}
  {hL : ∀ e : Fin (3 * (p₀ - n₀)), D.bigCore.tail e ≠ D.bigCore.head e}

/-- **The cut relabelling, conditional only on the injectivity of the vertex
map.**

`RetainedExhausts.cutRelabeling_of_expansion_of_injective` reduces
`RetainedRelabeling.CutRelabeling` at the requested expansion model to an injective map on the
refined core vertices satisfying the two endpoint equations.  §13 proves the
equations for `vertexModel` outright, so what is left is exactly the named
hypothesis `hInj`. -/
theorem cutRelabeling_of_expansion (hCond : D.Conditions spec₀.core)
    (hInj : ∀ (degree : ℕ) (coordinate : Type) [Fintype coordinate] [DecidableEq coordinate]
      (tgt : CFGraph.{0}) (gdata : GluingDatum tgt degree) (wall : tgt.V)
      (cand : Candidate tgt degree gdata wall)
      (strong : StrongPresentation cand.datum coordinate)
      (coordinates : coordinate → ℚ)
      (iface : InputInterface (D.bigSpec spec₀ hN hL) strong.toPresentation coordinates
        (expansionForest D))
      (dict : CoreDictionary (D.bigSpec spec₀ hN hL) strong iface),
      Faithful dict → ∀ hSpan : Spanning dict, cand.datum.Connected →
        SourceGenusMatches (D.bigSpec spec₀ hN hL) cand.datum →
        ∀ (face : ClearedFace cand strong.toPresentation coordinates)
          (topology : ClearedFace.SourceContractionTopology face)
          (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty),
          Function.Injective (vertexModel hCond dict hSpan topology hKept)) :
    RetainedRelabeling.CutRelabeling (D.bigSpec spec₀ hN hL) (expansionForest D) spec₀
      (RetainedIndexProducer.retainedIndex hCond hN hL) := by
  refine RetainedExhausts.cutRelabeling_of_expansion_of_injective hCond ?_
  intro degree coordinate _ _ tgt gdata wall cand strong coordinates iface dict
    hFaithful hSpanning hConnected hSource face topology hKept
  exact ⟨_, vertexModel hCond dict hSpanning topology hKept,
    hInj degree coordinate tgt gdata wall cand strong coordinates iface dict hFaithful
      hSpanning hConnected hSource face topology hKept,
    endpointEquations hCond dict hSpanning hFaithful topology hKept⟩

end Receipt

/-! ## 17.  The Statement's conclusion, on the link and the injectivity of the
vertex map -/

section Statement

open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases.OuterWalk
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.StableSourceDarts
open DraismaVargas.LocalCases.TerminalExhausts

/-- **The Statement's conclusion from the walk's link and the injectivity of the
vertex map.**  The binders `spec`, `hconn`, `hGenus`, `hEven`, the conclusion
and `link` are
`RetainedStatement.nonempty_evenSubdivisionPencil_of_link_of_injective`'s
verbatim; `inj` replaces its whole `vertex` datum by the single statement that
the map this file constructs is injective. -/
theorem nonempty_evenSubdivisionPencil_of_link_of_injective_vertexModel {n p : ℕ}
    (spec : SubdivisionGraph.Spec n p)
    (hconn : graph_connected spec.graph) (hGenus : 6 ≤ p + 1 - n)
    (hEven : Even (p + 1 - n))
    (link : ∀ m : ℕ, p + 1 - n = 2 * m + 2 →
      ∀ K : CubicDartGraph (Dart (CaterpillarSeed.seed m).candidate.datum)
        (BranchVertex (CaterpillarSeed.seed m).candidate.datum),
      CubicDartGraph.Reaches (seedGraph m) K →
      ∀ (mv : K.MoveData)
        (arrival : OuterWalk.FacetArrival (m + 2) K (seedLabel m) (seedLabel m mv.base))
        (wd : OuterWalk.WallData arrival), OuterWalk.TypeChangeLink mv wd)
    (inj : ∀ {n₀ p₀ : ℕ} (spec₀ : SubdivisionGraph.Spec n₀ p₀)
      (D : ExpansionData n₀ p₀ (2 * (p₀ - n₀)) (3 * (p₀ - n₀)))
      (hN : 0 < 2 * (p₀ - n₀))
      (hL : ∀ e : Fin (3 * (p₀ - n₀)), D.bigCore.tail e ≠ D.bigCore.head e)
      (hCond : D.Conditions spec₀.core)
      (degree : ℕ) (coordinate : Type) [Fintype coordinate] [DecidableEq coordinate]
      (tgt : CFGraph.{0}) (gdata : GluingDatum tgt degree) (wall : tgt.V)
      (cand : Candidate tgt degree gdata wall)
      (strong : StrongPresentation cand.datum coordinate)
      (coordinates : coordinate → ℚ)
      (iface : InputInterface (D.bigSpec spec₀ hN hL) strong.toPresentation coordinates
        (expansionForest D))
      (dict : CoreDictionary (D.bigSpec spec₀ hN hL) strong iface),
      Faithful dict → ∀ hSpan : Spanning dict, cand.datum.Connected →
        SourceGenusMatches (D.bigSpec spec₀ hN hL) cand.datum →
        ∀ (face : ClearedFace cand strong.toPresentation coordinates)
          (topology : ClearedFace.SourceContractionTopology face)
          (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty),
          Function.Injective (vertexModel hCond dict hSpan topology hKept)) :
    Nonempty (DraismaVargas.SubdivisionPencil spec ((p + 2 - n) / 2 + 1)) :=
  RetainedStatement.nonempty_evenSubdivisionPencil_of_link_of_injective spec hconn hGenus hEven
    link
    (fun spec₀ D hN hL hCond degree coordinate _ _ tgt gdata wall cand strong coordinates iface
      dict hFaithful hSpanning hConnected hSource face topology hKept ↦
      ⟨_, vertexModel hCond dict hSpanning topology hKept,
        inj spec₀ D hN hL hCond degree coordinate tgt gdata wall cand strong coordinates iface
          dict hFaithful hSpanning hConnected hSource face topology hKept,
        endpointEquations hCond dict hSpanning hFaithful topology hKept⟩)

end Statement

/-! ## 18.  Non-vacuity, and the arithmetic concretely

No structure is introduced in this file: `cutTail`, `cutHead`, `splitVertex`
and `cutVertex` inhabit `RefinementCore.RefinedVertex` of
`RetainedCut.cutData`, `vertexModel` is a function into `Fin (cutSpec …).n`,
and `IsHandover` is an existential over the slots of the requested
specification.  What is new is the case split, and both of its branches are
inhabited: `§18` exhibits a genuine handover point at the marker-aware
expansion of the wedge of two loops, and the straddle arithmetic the split
branch is about is evaluated on the three-piece row of
`RetainedCut` §7. -/

section Witness

/-- The requested specification underlying the marker witness of the expansion
model: the wedge of
two loops, displayed looplessly on four unit slots. -/
def wedgeSpec : SubdivisionGraph.Spec 3 4 :=
  SubdivisionGraph.Spec.ofCore StableModelReduction.wedgeCore (by norm_num)
    StableModelReduction.wedge_loopless (fun _ ↦ 1) (fun _ ↦ Nat.one_pos)

/-- **`IsHandover` is inhabited.**  The marker-aware expansion of the wedge
carries two requested slots in series along one cubic slot, and their joint is
a handover point of the retained index the producer builds. -/
theorem exists_isHandover :
    ∃ (D : ExpansionData 3 4 2 3) (hCond : D.Conditions wedgeSpec.core) (w : Fin 3),
      IsHandover (RetainedIndexProducer.retainedIndex hCond
        (show (0 : ℕ) < 2 by norm_num)
        (fun e ↦ ExpansionData.loopless_of_conditions hCond e)) w := by
  obtain ⟨D, hCond, e, j₁, j₂, hk⟩ := RetainedFibre.exists_conditions_with_marker
  exact ⟨D, hCond, StableModelReduction.wedgeCore.head j₁,
    handover_of_isMarker hCond ⟨e, j₁, j₂, hk, rfl⟩⟩

/-- **and so is its negation**: the tail of a requested slot at carrier position
zero is not a handover point of a marker-free expansion. -/
theorem isHandover_of_pos_eq_one {n p : ℕ} {spec : SubdivisionGraph.Spec n p}
    {F : Finset (Fin p)} {n' p' : ℕ} {small : SubdivisionGraph.Spec n' p'}
    {idx : RetainedIndex spec F small} {j : Fin p'} (h : idx.pos j = 1) :
    IsHandover idx (small.core.tail j) :=
  ⟨j, h, rfl⟩

/-- The straddle the split branch is about: one cleared occurrence of length
three, cut at metric position one, leaves two pieces. -/
example : OrderedPathSplit.positiveSegments ((cutList [3] 1).getD 0 []) = [1, 2] := rfl

/-- Its second piece is the first piece of the second requested slot: the two
groupings of that row have the same flattening, so the marker is the place at
which the row hands over. -/
example : ([[1, 2]] : List (List ℕ)).flatten = ([[1], [2]] : List (List ℕ)).flatten := rfl

/-- On that row the marker's kept slot has two pieces, so `cutTail` at piece
one is the new split vertex and `cutHead` at piece zero is the same vertex,
while `cutHead` at piece one is the class the row leaves the occurrence in. -/
example : offset ([[1, 2]] : List (List ℕ)) 0 + 1 = offset ([[1], [2]] : List (List ℕ)) 1 :=
  rfl

/-- An aligned marker instead: the cut leaves a zero-length piece, which the
refinement discards, so the marker's kept slot has one piece and `cutTail` at
piece zero is an honest contraction class. -/
example : OrderedPathSplit.positiveSegments ((cutList [2, 3] 2).getD 1 []) = [3] := rfl

end Witness

/-! ## 19.  The split half of injectivity -/

section SplitInjectivity

variable {n p : ℕ} {spec : SubdivisionGraph.Spec n p} {F : Finset (Fin p)}
  {n' p' : ℕ} {small : SubdivisionGraph.Spec n' p'}
  {iface : InputInterface spec strong.toPresentation coordinates F}
  (idx : RetainedIndex spec F small)
  (topology : ClearedFace.SourceContractionTopology face)
  (rev : SlotIndex iface face → Bool)
  (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)

/-- **A retained slot and a position along it determine the requested
slot.** -/
theorem owner_pos_determines {j j' : Fin p'} (ho : idx.owner j = idx.owner j')
    (hp : idx.pos j = idx.pos j') : j = j' := by
  have h1 := idx.carried_getElem j
  have h2 := idx.carried_getElem j'
  rw [ho, hp] at h1
  exact Option.some_inj.mp (h1.symm.trans h2)

theorem cutSlot_injective :
    Function.Injective (cutSlot (iface := iface) topology hKept) := by
  intro x x' h
  exact (slotIndexEquivKept iface face topology).injective h

/-- **A new split vertex records the kept slot it was cut inside.** -/
theorem straddles_of_cutTail_inr {x : SlotIndex iface face} {t : ℕ}
    {z : Σ s : Fin (packed (ClearedFace.SourceContractionTopology.prunedSpec topology hKept)).p,
      Fin (((cutData iface face idx topology rev hKept).segments s).length - 1)}
    (h : cutTail idx topology rev hKept x t = Sum.inr z) :
    Straddles iface face idx x ∧ t ≠ 0 ∧ z.1 = cutSlot topology hKept x := by
  by_cases hc : Straddles iface face idx x ∧ t ≠ 0
  · refine ⟨hc.1, hc.2, ?_⟩
    have hs : cutTail idx topology rev hKept x t =
        splitVertex idx topology rev hKept hc.1 := dite_eq_left hc
    have hz := Sum.inr.inj (hs.symm.trans h)
    exact (congrArg Sigma.fst hz).symm
  · exact absurd ((dite_eq_right hc).symm.trans h) (by simp [cutLeft])

/-- and the same on the far side of the piece. -/
theorem straddles_of_cutHead_inr {x : SlotIndex iface face} {t : ℕ}
    {z : Σ s : Fin (packed (ClearedFace.SourceContractionTopology.prunedSpec topology hKept)).p,
      Fin (((cutData iface face idx topology rev hKept).segments s).length - 1)}
    (h : cutHead idx topology rev hKept x t = Sum.inr z) :
    Straddles iface face idx x ∧ t = 0 ∧ z.1 = cutSlot topology hKept x := by
  by_cases hc : Straddles iface face idx x ∧ t = 0
  · refine ⟨hc.1, hc.2, ?_⟩
    have hs : cutHead idx topology rev hKept x t =
        splitVertex idx topology rev hKept hc.1 := dite_eq_left hc
    have hz := Sum.inr.inj (hs.symm.trans h)
    exact (congrArg Sigma.fst hz).symm
  · exact absurd ((dite_eq_right hc).symm.trans h) (by simp [cutLeft])

end SplitInjectivity

/-! ## 20.  Injectivity, reduced to the contraction classes -/

section Reduce

variable {n₀ p₀ N Q : ℕ} {D : ExpansionData n₀ p₀ N Q} {spec₀ : SubdivisionGraph.Spec n₀ p₀}
  {hN : 0 < N} {hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e}
  {iface : InputInterface (D.bigSpec spec₀ hN hL) strong.toPresentation coordinates
    (expansionForest D)}

variable (hCond : D.Conditions spec₀.core)
  (dict : CoreDictionary (D.bigSpec spec₀ hN hL) strong iface) (hSpan : Spanning dict)
  (topology : ClearedFace.SourceContractionTopology face)
  (rev : SlotIndex iface face → Bool)
  (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
  (hTwo : CarriesAtMostTwo (RetainedIndexProducer.retainedIndex hCond hN hL))

/-- **No breakpoint of the retained refinement lands on a new split vertex.**
This is `RetainedStraddle.retPos_ne_piecePos_zero`: a breakpoint separates two
consecutive pieces of one requested slot, while the straddle point is the
boundary between the two requested slots the row carries. -/
theorem not_straddles_blockSlot_breakPair
    (y : Σ j : Fin p₀, Fin (((Retained.segmentData iface face
      (RetainedIndexProducer.retainedIndex hCond hN hL)).segments j).length - 1)) :
    ¬ (Straddles iface face (RetainedIndexProducer.retainedIndex hCond hN hL)
        (blockSlot (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept hTwo
          (breakPair (RetainedIndexProducer.retainedIndex hCond hN hL) y)) ∧
      blockIndex (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept hTwo
        (breakPair (RetainedIndexProducer.retainedIndex hCond hN hL) y) = 0) := by
  rintro ⟨hstr, h0⟩
  have hy := y.2.isLt
  refine retPos_ne_piecePos_zero (RetainedIndexProducer.retainedIndex hCond hN hL) hTwo hstr
    (j := (breakPair (RetainedIndexProducer.retainedIndex hCond hN hL) y).1)
    (Subtype.ext (blockSlot_row (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev
      hKept hTwo (breakPair (RetainedIndexProducer.retainedIndex hCond hN hL) y)).symm)
    (m := ((breakPair (RetainedIndexProducer.retainedIndex hCond hN hL) y).2 : ℕ))
    (by
      show (y.2 : ℕ) + 1 < ((Retained.segmentData iface face
        (RetainedIndexProducer.retainedIndex hCond hN hL)).segments y.1).length
      omega) ?_
  rw [← piecePos_blockIndex (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
    hTwo (breakPair (RetainedIndexProducer.retainedIndex hCond hN hL) y), h0]

/-- **so a breakpoint always goes to a kept class.** -/
theorem cutVertex_inr_eq_cutLeft
    (y : Σ j : Fin p₀, Fin (((Retained.segmentData iface face
      (RetainedIndexProducer.retainedIndex hCond hN hL)).segments j).length - 1)) :
    cutVertex hCond dict hSpan topology rev hKept hTwo (Sum.inr y) =
      cutLeft (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
        (RefinementCore.keptClassIndex topology
          ⟨endClass topology (blockSlot (RetainedIndexProducer.retainedIndex hCond hN hL)
              topology rev hKept hTwo
              (breakPair (RetainedIndexProducer.retainedIndex hCond hN hL) y)),
            keptClass_endClass topology _⟩) :=
  (cutVertex_inr hCond dict hSpan topology rev hKept hTwo y).trans
    (dite_eq_right (not_straddles_blockSlot_breakPair hCond topology rev hKept hTwo y))

/-- **The new split vertices are hit at most once.**  Only a straddling marker
lands on one, the split vertex records the kept slot the marker cut, and the
kept slot together with the carrier position determines the requested slot that
begins at the marker. -/
theorem eq_of_cutVertex_inr
    {v v' : RefinementCore.RefinedVertex (Retained.segmentData iface face
      (RetainedIndexProducer.retainedIndex hCond hN hL))}
    {z z' : Σ s : Fin (packed (ClearedFace.SourceContractionTopology.prunedSpec topology
        hKept)).p,
      Fin (((cutData iface face (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev
        hKept).segments s).length - 1)}
    (hv : cutVertex hCond dict hSpan topology rev hKept hTwo v = Sum.inr z)
    (hv' : cutVertex hCond dict hSpan topology rev hKept hTwo v' = Sum.inr z')
    (hzz : z.1 = z'.1) : v = v' := by
  obtain ⟨w, rfl⟩ : ∃ w : Fin n₀, v = Sum.inl w := by
    cases v with
    | inl w => exact ⟨w, rfl⟩
    | inr y =>
        exact absurd ((cutVertex_inr_eq_cutLeft hCond dict hSpan topology rev hKept hTwo
          y).symm.trans hv) (by simp [cutLeft])
  obtain ⟨w', rfl⟩ : ∃ w' : Fin n₀, v' = Sum.inl w' := by
    cases v' with
    | inl w' => exact ⟨w', rfl⟩
    | inr y =>
        exact absurd ((cutVertex_inr_eq_cutLeft hCond dict hSpan topology rev hKept hTwo
          y).symm.trans hv') (by simp [cutLeft])
  by_cases hw : IsHandover (RetainedIndexProducer.retainedIndex hCond hN hL) w
  · by_cases hw' : IsHandover (RetainedIndexProducer.retainedIndex hCond hN hL) w'
    · obtain ⟨-, -, hz1⟩ := straddles_of_cutTail_inr
        (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
        ((coreVertex_of_handover hCond dict hSpan topology rev hKept hTwo hw).symm.trans
          ((cutVertex_inl hCond dict hSpan topology rev hKept hTwo w).symm.trans hv))
      obtain ⟨-, -, hz1'⟩ := straddles_of_cutTail_inr
        (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
        ((coreVertex_of_handover hCond dict hSpan topology rev hKept hTwo hw').symm.trans
          ((cutVertex_inl hCond dict hSpan topology rev hKept hTwo w').symm.trans hv'))
      have hx : blockSlot (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
            hTwo (handoverPair hCond face hw) =
          blockSlot (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept hTwo
            (handoverPair hCond face hw') :=
        cutSlot_injective topology hKept (hz1.symm.trans (hzz.trans hz1'))
      have hown : (RetainedIndexProducer.retainedIndex hCond hN hL).owner
            (handoverPair hCond face hw).1 =
          (RetainedIndexProducer.retainedIndex hCond hN hL).owner
            (handoverPair hCond face hw').1 :=
        Subtype.ext ((blockSlot_row (RetainedIndexProducer.retainedIndex hCond hN hL) topology
          rev hKept hTwo (handoverPair hCond face hw)).symm.trans
          ((congrArg Sigma.fst hx).trans
            (blockSlot_row (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
              hTwo (handoverPair hCond face hw'))))
      have hj : (handoverPair hCond face hw).1 = (handoverPair hCond face hw').1 :=
        owner_pos_determines (RetainedIndexProducer.retainedIndex hCond hN hL) hown
          (hw.choose_spec.1.trans hw'.choose_spec.1.symm)
      exact congrArg Sum.inl (hw.choose_spec.2.symm.trans
        ((congrArg spec₀.core.tail hj).trans hw'.choose_spec.2))
    · exact absurd ((coreVertex_of_not_handover hCond dict hSpan topology rev hKept hTwo
        hw').symm.trans ((cutVertex_inl hCond dict hSpan topology rev hKept hTwo w').symm.trans
          hv')) (by simp [cutLeft])
  · exact absurd ((coreVertex_of_not_handover hCond dict hSpan topology rev hKept hTwo
      hw).symm.trans ((cutVertex_inl hCond dict hSpan topology rev hKept hTwo w).symm.trans hv))
      (by simp [cutLeft])

end Reduce

/-! ## 21.  What injectivity costs -/

section ReduceHeadline

variable {n₀ p₀ N Q : ℕ} {D : ExpansionData n₀ p₀ N Q} {spec₀ : SubdivisionGraph.Spec n₀ p₀}
  {hN : 0 < N} {hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e}
  {iface : InputInterface (D.bigSpec spec₀ hN hL) strong.toPresentation coordinates
    (expansionForest D)}

/-- **Injectivity of the vertex map, reduced to the contraction classes.**

The new split vertices are handled outright: only a straddling marker lands on
one (`not_straddles_blockSlot_breakPair`), and the split vertex records the
kept slot it was cut inside (`eq_of_cutVertex_inr`).  What is left is the
general-forest form of `DraismaVargas.LocalCases.ClassInjectivity`: **two
refined core vertices sent to the same kept contraction class are equal**.

That statement is what `RetainedClassInjectivity` supplies (as `hcls`, §1--§8
there).  Its three general-forest replacements for `ClassInjectivity`'s §3--§4
inputs are:
`RetainedCut.positiveRow_ne_nil_of_not_mem_forest` (a zero run can never
traverse a whole retained row, since every retained row carries a surviving
occurrence), `RetainedTraversal.classOf_finish_eq_classOf_start_of_mem_forest`
together with `RetainedFibre.coreClass_eq_of_fib_eq` (a forest row is one
class, so the fibre classes are well defined and two model core vertices of one
fibre may not be separated), and `RetainedFibre.not_exists_fib_eq_marker`
(a marker is the class of no model core vertex, so an aligned marker cannot
collide with a fibre class unless the walk class at its occurrence boundary
does).  `ClassInjectivity` §4's zero-run confinement itself (`Near`,
`near_step` and `eq_of_near`) is stated for `OrientedTraversal.RowDictionary`,
i.e. at `F = ∅`; its nonempty-forest form is proved in
`RetainedClassInjectivity`. -/
theorem injective_vertexModel_of_inl (hCond : D.Conditions spec₀.core)
    (dict : CoreDictionary (D.bigSpec spec₀ hN hL) strong iface) (hSpan : Spanning dict)
    (topology : ClearedFace.SourceContractionTopology face)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (hcls : ∀ (v v' : RefinementCore.RefinedVertex (Retained.segmentData iface face
        (RetainedIndexProducer.retainedIndex hCond hN hL)))
      (c : Fin (packed (ClearedFace.SourceContractionTopology.prunedSpec topology hKept)).n),
      cutVertex hCond dict hSpan topology
          (RetainedTraversal.reversedAt (strong := strong) (iface := iface) (face := face))
          hKept (RetainedCut.carried_length_le_two hCond hN hL) v = Sum.inl c →
        cutVertex hCond dict hSpan topology
          (RetainedTraversal.reversedAt (strong := strong) (iface := iface) (face := face))
          hKept (RetainedCut.carried_length_le_two hCond hN hL) v' = Sum.inl c → v = v') :
    Function.Injective (vertexModel hCond dict hSpan topology hKept) := by
  intro v v' h
  have hcv := (RefinementCore.vertexIndexEquiv _).injective h
  rcases hc : cutVertex hCond dict hSpan topology
      (RetainedTraversal.reversedAt (strong := strong) (iface := iface) (face := face)) hKept
      (RetainedCut.carried_length_le_two hCond hN hL) v with c | z
  · exact hcls v v' c hc (hcv.symm.trans hc)
  · exact eq_of_cutVertex_inr hCond dict hSpan topology _ hKept
      (RetainedCut.carried_length_le_two hCond hN hL) hc (hcv.symm.trans hc) rfl

end ReduceHeadline

end

end DraismaVargas.LocalCases.RetainedVertexModel
