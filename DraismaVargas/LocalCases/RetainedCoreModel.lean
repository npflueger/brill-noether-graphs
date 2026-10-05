module

public import DraismaVargas.LocalCases.RetainedRowPieces
public import DraismaVargas.LocalCases.RetainedFibre

@[expose] public section

/-!
# The slot bijection of the retained core model on the cut spec

**Source.**  As in `DraismaVargas.LocalCases.RetainedRowPieces`, the marker cut
appears in neither Draisma–Vargas Part I (arXiv:1909.12924) nor Vargas, Part II
(arXiv:2609.09109), so nothing here is a transcription of either.  The target
of the core model is the pruned contracted spec cut at the straddled markers
(`RetainedCut.cutSpec`), whose slots are the kept slots together with one extra
slot per straddled marker.

## What is proved

`RetainedCut.cutRelabeling_of_cutCoreModel` reduces the cut relabelling
`RetainedRelabeling.CutRelabeling` -- the last input of the transport to the
requested graph -- to a `RefinementCore.CoreModel` of the retained segment data
on `RetainedCut.cutSpec`.  That model needs two bijections and three equations.
**This file builds the slot bijection and proves the length equation.**

* §6 puts the cut spec's own prescribed lists on the kept slots themselves
  (`cutSegs`), rather than on their numbers in the pruned contracted spec.
  Naming that once is what keeps every statement below off the expensive
  unfolding of `(packed (prunedSpec …)).p = (keptSlots …).card`.

* §7 reads those lists in row order: `pieceIndex` is the identity on a kept
  slot the row traverses forwards and the mirror index `len - 1 - q` on one it
  traverses backwards, which is exactly the `rev` bit of
  `RetainedCut.cutSegments`; `getD_cutSegs` says the two readings agree.

* §8 assembles the cut side: `pieceEquiv` orients one kept slot's pieces,
  `pieceRowEquiv` places them along the retained rows -- its cardinality is
  `RetainedCut.cutSpec_p` -- and `cutRowEquiv` is their composite.

* §9 is the deliverable.  `slotModel` is the bijection from the prescribed
  segments of the requested slots to the slots of `RetainedCut.cutSpec`, and
  `length_eq_slotModel` the core model's length equation: the named slot
  carries the prescribed segment.  Both sides are read at the same place of the
  same retained row, so the equation is `FlattenIndex.getD_flatten` twice.
  `coreModel_of_vertexModel` states the residue in one place: with `slotModel`,
  the orientation flag `reversedSlot` and `length_eq` discharged, a core model
  on the cut spec is **exactly** a bijection of the refined core vertices
  satisfying the two endpoint equations.

* §11 feeds that back through `RetainedCut.cutRelabeling_of_cutCoreModel`:
  `cutRelabeling_of_vertexModel` says the cut relabelling
  `RetainedRelabeling.CutRelabeling` follows from the vertex datum alone.  At
  the requested expansion model (`RequestedExpandedEndpoints.exists_expansionModel`)
  its `hTwo` is `RetainedCut.carried_length_le_two hCond hN hL`, so
  `cutRelabeling_of_vertexModel (RetainedCut.carried_length_le_two hCond hN hL)`
  is exactly the `cut` binder of
  `RetainedRelabeling.nonempty_evenSubdivisionPencil_of_link'`, with the vertex
  datum in place of the whole relabelling.

## The hypotheses that remain explicit

1. **`hTwo : RetainedCut.CarriesAtMostTwo idx`**, discharged at the requested
   expansion model by `RetainedCut.carried_length_le_two`.

2. **The vertex half.**  Nothing here produces
   `RefinementCore.CoreModel (Retained.segmentData iface face idx)
   (RetainedCut.cutSpec …).spec`: `coreModel_of_vertexModel` and
   `cutRelabeling_of_vertexModel` ask for the `vertexModel` bijection and the two
   endpoint equations -- the two theorems are reductions, not constructions.
   The datum is built elsewhere: `RetainedVertexModel.vertexModel` builds the map
   with its endpoint equations unconditional, and `RetainedClassInjectivity`
   supplies the class-half injectivity.  Building it needs `RetainedTraversal`'s
   walk and its zero-run confinement, `RetainedStraddle`'s location of the
   marker, `RetainedFibre`'s marker/fibre dichotomy, the general-forest
   injectivity of the class map, and `RetainedCut.RetainedExhausts` (the
   general-forest genus count, which `card_refinedVertex_eq_cutSpec_n` turns into
   the cardinality the bijection needs).

3. **The orientation is a parameter.**  `rev` is an arbitrary
   `SlotIndex iface face → Bool` here; the vertex half instantiates it with
   `RetainedTraversal.reversedAt`, which is computed, not assumed.

4. Everything `RetainedRelabeling.CutRelabeling` keeps inside its binder: the
   core dictionary, `Faithful`, `Spanning`, `Connected`, `SourceGenusMatches`,
   the topology and the kept class.

## Consumers

The vertex half (`RetainedVertexModel`), and through
`RetainedCut.cutRelabeling_of_cutCoreModel` the cut relabelling
`RetainedRelabeling.CutRelabeling` on `StatementFromLink`'s route to
`DraismaVargas.Statement`.
-/

namespace DraismaVargas.LocalCases.RetainedCoreModel

noncomputable section

open Utilities
open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.IteratedSplitRefinement
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.BlockSplitCount
open DraismaVargas.Infrastructure.FlattenIndex
open DraismaVargas.Infrastructure.OccurrenceCut
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancedGlobal.Candidate
open DraismaVargas.LocalCases.InputRefinementData
open DraismaVargas.LocalCases.RefinementCore
open DraismaVargas.LocalCases.RetainedCut
open DraismaVargas.LocalCases.RetainedRowPieces
open DraismaVargas.LocalCases.RetainedRelabeling
open DraismaVargas.LocalCases.SlotRefinement
open DraismaVargas.LocalCases.TraversalPresentation

section Slots

variable {target : CFGraph} {degree : ℕ}
  {gluing : GluingDatum target degree} {wall : target.V}
  {candidate : Candidate target degree gluing wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {coordinates : coordinate → ℚ}
  {n p : ℕ} {spec : SubdivisionGraph.Spec n p} {F : Finset (Fin p)}
  {strong : StrongPresentation candidate.datum coordinate}
  {face : ClearedFace candidate strong.toPresentation coordinates}
  {n' p' : ℕ} {small : SubdivisionGraph.Spec n' p'}

/-! ## 6.  The cut spec's segment lists, indexed by the kept slots -/

theorem cond_of_true {α : Type*} {b : Bool} (h : b = true) (x y : α) :
    cond b x y = x := by
  subst h
  rfl

theorem cond_of_false {α : Type*} {b : Bool} (h : b = false) (x y : α) :
    cond b x y = y := by
  subst h
  rfl


/-- **The segment list the cut prescribes for a kept slot.**  It is `cutData`'s
own list, indexed by the kept slot itself rather than by its number in the
pruned contracted spec.  Naming it once is what keeps the statements below off
the expensive unfolding of `(packed (prunedSpec …)).p = (keptSlots …).card`. -/
def cutSegs (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (x : SlotIndex iface face) : List ℕ :=
  (cutData iface face idx topology rev hKept).segments
    (slotIndexEquivKept iface face topology x)

/-- **On a kept slot the row traverses backwards** the prescribed list is the
reversed piece list. -/
theorem cutSegs_of_rev (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (x : SlotIndex iface face) (hrev : rev x = true) :
    cutSegs iface face idx topology rev hKept x =
      (OrderedPathSplit.positiveSegments (pieces iface face idx x)).reverse := by
  unfold cutSegs
  rw [cutData_segments, cutSegments, Equiv.symm_apply_apply, ite_eq_left hrev]
  exact positiveSegments_reverse _

/-- **and on one it traverses forwards** it is the piece list itself. -/
theorem cutSegs_of_not_rev (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (x : SlotIndex iface face) (hrev : rev x = false) :
    cutSegs iface face idx topology rev hKept x =
      OrderedPathSplit.positiveSegments (pieces iface face idx x) := by
  unfold cutSegs
  rw [cutData_segments, cutSegments, Equiv.symm_apply_apply,
    ite_eq_right (show ¬ (rev x = true) by rw [hrev]; exact Bool.false_ne_true)]

theorem length_cutSegs (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (x : SlotIndex iface face) :
    (cutSegs iface face idx topology rev hKept x).length =
      (OrderedPathSplit.positiveSegments (pieces iface face idx x)).length := by
  refine (Bool.eq_false_or_eq_true (rev x)).elim (fun hrev => ?_) (fun hrev => ?_)
  · rw [cutSegs_of_rev iface face idx topology rev hKept x hrev, List.length_reverse]
  · rw [cutSegs_of_not_rev iface face idx topology rev hKept x hrev]

/-! ## 7.  The place along the row of a piece of the cut spec's source -/

/-- **The index along the row of the piece a slot of the cut spec's source
carries at index `q`.**  It is `q` itself on a kept slot the row traverses
forwards, and the mirror index on one it traverses backwards. -/
def pieceIndex (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (x : SlotIndex iface face) (q : ℕ) : ℕ :=
  cond (rev x) ((cutSegs iface face idx topology rev hKept x).length - 1 - q) q

theorem pieceIndex_of_rev (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (x : SlotIndex iface face) (q : ℕ) (hrev : rev x = true) :
    pieceIndex iface face idx topology rev hKept x q =
      (cutSegs iface face idx topology rev hKept x).length - 1 - q :=
  cond_of_true hrev _ _

theorem pieceIndex_of_not_rev (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (x : SlotIndex iface face) (q : ℕ) (hrev : rev x = false) :
    pieceIndex iface face idx topology rev hKept x q = q :=
  cond_of_false hrev _ _

theorem pieceIndex_lt (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (x : SlotIndex iface face) {q : ℕ}
    (hq : q < (cutSegs iface face idx topology rev hKept x).length) :
    pieceIndex iface face idx topology rev hKept x q <
      (OrderedPathSplit.positiveSegments (pieces iface face idx x)).length := by
  have hlen := length_cutSegs iface face idx topology rev hKept x
  refine (Bool.eq_false_or_eq_true (rev x)).elim (fun hrev => ?_) (fun hrev => ?_)
  · rw [pieceIndex_of_rev iface face idx topology rev hKept x q hrev]
    omega
  · rw [pieceIndex_of_not_rev iface face idx topology rev hKept x q hrev]
    omega

theorem pieceIndex_inj (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (x : SlotIndex iface face) {q q' : ℕ}
    (hq : q < (cutSegs iface face idx topology rev hKept x).length)
    (hq' : q' < (cutSegs iface face idx topology rev hKept x).length)
    (h : pieceIndex iface face idx topology rev hKept x q =
      pieceIndex iface face idx topology rev hKept x q') : q = q' := by
  refine (Bool.eq_false_or_eq_true (rev x)).elim (fun hrev => ?_) (fun hrev => ?_)
  · have e1 := pieceIndex_of_rev iface face idx topology rev hKept x q hrev
    have e2 := pieceIndex_of_rev iface face idx topology rev hKept x q' hrev
    omega
  · have e1 := pieceIndex_of_not_rev iface face idx topology rev hKept x q hrev
    have e2 := pieceIndex_of_not_rev iface face idx topology rev hKept x q' hrev
    omega

/-- **and the piece it names is the prescribed one.** -/
theorem getD_cutSegs (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (x : SlotIndex iface face) {q : ℕ}
    (hq : q < (cutSegs iface face idx topology rev hKept x).length) :
    (OrderedPathSplit.positiveSegments (pieces iface face idx x)).getD
        (pieceIndex iface face idx topology rev hKept x q) 0 =
      (cutSegs iface face idx topology rev hKept x).getD q 0 := by
  have hlen := length_cutSegs iface face idx topology rev hKept x
  refine (Bool.eq_false_or_eq_true (rev x)).elim (fun hrev => ?_) (fun hrev => ?_)
  · have hseg := cutSegs_of_rev iface face idx topology rev hKept x hrev
    have hidx := pieceIndex_of_rev iface face idx topology rev hKept x q hrev
    have hq' : q < (OrderedPathSplit.positiveSegments (pieces iface face idx x)).length := by
      omega
    rw [hidx, hlen, hseg, getD_reverse _ 0 hq']
  · have hseg := cutSegs_of_not_rev iface face idx topology rev hKept x hrev
    have hidx := pieceIndex_of_not_rev iface face idx topology rev hKept x q hrev
    rw [hidx, hseg]

/-! ## 8.  The pieces of the cut spec's source, as places along the rows -/

/-- **The pieces of one kept slot, in row order.**  The reversal is exactly
`rev`'s. -/
def pieceEquiv (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (x : SlotIndex iface face) :
    Fin (cutSegs iface face idx topology rev hKept x).length ≃
      Fin (OrderedPathSplit.positiveSegments (pieces iface face idx x)).length :=
  Equiv.ofBijective
    (fun q ↦ ⟨pieceIndex iface face idx topology rev hKept x (q : ℕ),
      pieceIndex_lt iface face idx topology rev hKept x q.isLt⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun q q' hqq' ↦ Fin.ext (pieceIndex_inj iface face idx topology rev hKept x
          q.isLt q'.isLt (congrArg Fin.val hqq')),
        by rw [Fintype.card_fin, Fintype.card_fin,
          length_cutSegs iface face idx topology rev hKept x]⟩)

@[simp] theorem pieceEquiv_val (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (x : SlotIndex iface face) (q : Fin (cutSegs iface face idx topology rev hKept x).length) :
    ((pieceEquiv iface face idx topology rev hKept x q : Fin _) : ℕ) =
      pieceIndex iface face idx topology rev hKept x (q : ℕ) := rfl

/-- **The total piece count of the cut equals the retained refinement's slot
count.**  This is `RetainedCut.cutSpec_p`, read on the kept slots. -/
theorem sum_length_positiveSegments_pieces
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool) (hTwo : CarriesAtMostTwo idx)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty) :
    ∑ x : SlotIndex iface face,
        (OrderedPathSplit.positiveSegments (pieces iface face idx x)).length =
      ∑ j : Fin p', ((Retained.segmentData iface face idx).segments j).length := by
  have h1 : ∑ x : SlotIndex iface face,
      (cutSegs iface face idx topology rev hKept x).length =
      ∑ s : Fin (ClearedFace.SourceContractionTopology.keptSlots topology).card,
        ((cutData iface face idx topology rev hKept).segments s).length :=
    Fintype.sum_equiv (slotIndexEquivKept iface face topology) _ _ (fun _ ↦ rfl)
  have h2 := cutSpec_p iface face idx topology rev hTwo hKept
  rw [cutSpec, refineAllSlots_p] at h2
  rw [← h2, ← h1]
  exact Finset.sum_congr rfl fun x _ ↦
    (length_cutSegs iface face idx topology rev hKept x).symm

/-- **The pieces of the kept slots are the places along the retained rows.** -/
def pieceRowEquiv (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool) (hTwo : CarriesAtMostTwo idx)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty) :
    (Σ x : SlotIndex iface face,
        Fin (OrderedPathSplit.positiveSegments (pieces iface face idx x)).length) ≃
      RowPos iface face idx :=
  Equiv.ofBijective
    (fun y ↦ ⟨slotRow y.1, ⟨piecePos iface face idx y.1 (y.2 : ℕ),
      piecePos_lt idx hTwo y.1 y.2.isLt⟩⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨by
        rintro ⟨x, t⟩ ⟨x', t'⟩ hEq
        have h1 : slotRow x = slotRow x' := congrArg Sigma.fst hEq
        have hrow : (x : SlotIndex iface face).1 = (x' : SlotIndex iface face).1 :=
          congrArg Subtype.val h1
        have h2 := congrArg (fun z : RowPos iface face idx ↦ ((z.2 : Fin _) : ℕ)) hEq
        obtain ⟨hx, ht⟩ := piecePos_inj idx hrow t.isLt t'.isLt h2
        exact sigma_fin_ext hx ht,
        by
          rw [card_rowPos, Fintype.card_sigma]
          simp only [Fintype.card_fin]
          exact sum_length_positiveSegments_pieces iface face idx topology rev hTwo hKept⟩)

@[simp] theorem pieceRowEquiv_fst (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool) (hTwo : CarriesAtMostTwo idx)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (y : Σ x : SlotIndex iface face,
        Fin (OrderedPathSplit.positiveSegments (pieces iface face idx x)).length) :
    (pieceRowEquiv iface face idx topology rev hTwo hKept y).1 = slotRow y.1 := rfl

@[simp] theorem pieceRowEquiv_snd (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool) (hTwo : CarriesAtMostTwo idx)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (y : Σ x : SlotIndex iface face,
        Fin (OrderedPathSplit.positiveSegments (pieces iface face idx x)).length) :
    ((pieceRowEquiv iface face idx topology rev hTwo hKept y).2 : ℕ) =
      piecePos iface face idx y.1 (y.2 : ℕ) := rfl

/-- **The slots of the cut spec's source are the places along the retained
rows.** -/
def cutRowEquiv (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool) (hTwo : CarriesAtMostTwo idx)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty) :
    (Σ x : SlotIndex iface face, Fin (cutSegs iface face idx topology rev hKept x).length) ≃
      RowPos iface face idx :=
  (Equiv.sigmaCongrRight (pieceEquiv iface face idx topology rev hKept)).trans
    (pieceRowEquiv iface face idx topology rev hTwo hKept)

theorem cutRowEquiv_fst (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool) (hTwo : CarriesAtMostTwo idx)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (z : Σ x : SlotIndex iface face, Fin (cutSegs iface face idx topology rev hKept x).length) :
    (cutRowEquiv iface face idx topology rev hTwo hKept z).1 = slotRow z.1 := rfl

theorem cutRowEquiv_snd (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool) (hTwo : CarriesAtMostTwo idx)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (z : Σ x : SlotIndex iface face, Fin (cutSegs iface face idx topology rev hKept x).length) :
    ((cutRowEquiv iface face idx topology rev hTwo hKept z).2 : ℕ) =
      piecePos iface face idx z.1
        (pieceIndex iface face idx topology rev hKept z.1 (z.2 : ℕ)) := rfl

/-! ## 9.  The slot bijection of the retained core model -/

/-- **The slots of the cut spec, named on the kept slots.** -/
def cutSlotModel (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty) :
    (Σ x : SlotIndex iface face, Fin (cutSegs iface face idx topology rev hKept x).length) ≃
      Fin (cutSpec iface face idx topology rev hKept).p :=
  (Equiv.sigmaCongrLeft
      (β := fun s : Fin (ClearedFace.SourceContractionTopology.keptSlots topology).card ↦
        Fin ((cutData iface face idx topology rev hKept).segments s).length)
      (slotIndexEquivKept iface face topology)).trans
    (RefinementCore.slotIndexEquiv (cutData iface face idx topology rev hKept))

/-- **and it carries the prescribed piece.** -/
theorem length_cutSlotModel (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (z : Σ x : SlotIndex iface face,
      Fin (cutSegs iface face idx topology rev hKept x).length) :
    (cutSpec iface face idx topology rev hKept).spec.length
        (cutSlotModel iface face idx topology rev hKept z) =
      (cutSegs iface face idx topology rev hKept z.1).getD (z.2 : ℕ) 0 :=
  RefinementCore.refineAllSlots_length_at (cutData iface face idx topology rev hKept)
    ⟨slotIndexEquivKept iface face topology z.1, z.2⟩

/-- **The prescribed segments of the requested slots are the pieces of the kept
slots.**  The `m`-th prescribed segment of the requested slot `j` and the `q`-th
piece of a kept slot are two readings of one and the same positive piece along
one and the same retained row. -/
def slotBlockEquiv (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (hTwo : CarriesAtMostTwo idx) :
    (Σ j : Fin p', Fin ((Retained.segmentData iface face idx).segments j).length) ≃
      (Σ x : SlotIndex iface face,
        Fin (cutSegs iface face idx topology rev hKept x).length) :=
  (retRowEquiv iface face idx).trans
    (cutRowEquiv iface face idx topology rev hTwo hKept).symm

/-- **`slotModel`**: which slot of the chain's target carries the `m`-th
prescribed segment of the requested slot `j`. -/
def slotModel (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (hTwo : CarriesAtMostTwo idx) :
    (Σ j : Fin p', Fin ((Retained.segmentData iface face idx).segments j).length) ≃
      Fin (cutSpec iface face idx topology rev hKept).p :=
  (slotBlockEquiv iface face idx topology rev hKept hTwo).trans
    (cutSlotModel iface face idx topology rev hKept)

theorem slotModel_apply (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (hTwo : CarriesAtMostTwo idx)
    (x : Σ j : Fin p', Fin ((Retained.segmentData iface face idx).segments j).length) :
    slotModel iface face idx topology rev hKept hTwo x =
      cutSlotModel iface face idx topology rev hKept
        (slotBlockEquiv iface face idx topology rev hKept hTwo x) := rfl

/-- **The first equation of the core model: the named slot carries the
prescribed segment.** -/
theorem length_eq_slotModel
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (hTwo : CarriesAtMostTwo idx)
    (x : Σ j : Fin p', Fin ((Retained.segmentData iface face idx).segments j).length) :
    (cutSpec iface face idx topology rev hKept).spec.length
        (slotModel iface face idx topology rev hKept hTwo x) =
      ((Retained.segmentData iface face idx).segments x.1).getD (x.2 : ℕ) 0 := by
  rw [slotModel_apply]
  set z := slotBlockEquiv iface face idx topology rev hKept hTwo x with hz
  have hbeta : cutRowEquiv iface face idx topology rev hTwo hKept z =
      retRowEquiv iface face idx x := by
    rw [hz, slotBlockEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  have hval := congrArg (fun w : RowPos iface face idx ↦
    (rowPieces iface face idx w.1).getD ((w.2 : Fin _) : ℕ) 0) hbeta
  rw [length_cutSlotModel iface face idx topology rev hKept z]
  calc (cutSegs iface face idx topology rev hKept z.1).getD ((z.2 : Fin _) : ℕ) 0
      = (OrderedPathSplit.positiveSegments (pieces iface face idx z.1)).getD
          (pieceIndex iface face idx topology rev hKept z.1 ((z.2 : Fin _) : ℕ)) 0 :=
        (getD_cutSegs iface face idx topology rev hKept z.1 z.2.isLt).symm
    _ = (rowPieces iface face idx (slotRow z.1)).getD
          (piecePos iface face idx z.1
            (pieceIndex iface face idx topology rev hKept z.1 ((z.2 : Fin _) : ℕ))) 0 :=
        (getD_rowPieces_piecePos idx hTwo z.1
          (pieceIndex_lt iface face idx topology rev hKept z.1 z.2.isLt)).symm
    _ = (rowPieces iface face idx (idx.owner x.1)).getD
          (retPos iface face idx x.1 (x.2 : ℕ)) 0 := hval
    _ = ((Retained.segmentData iface face idx).segments x.1).getD (x.2 : ℕ) 0 :=
        getD_rowPieces_retPos iface face idx x.1 x.2.isLt

/-- **The orientation flag of the retained core model.**  The prescribed
segment `x` is carried by a piece of the kept slot
`(slotBlockEquiv … x).1`, and `rev` records whether the retained row traverses
that kept slot against the orientation the source's own `sourceEnds` gives
it. -/
def reversedSlot (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (hTwo : CarriesAtMostTwo idx)
    (x : Σ j : Fin p', Fin ((Retained.segmentData iface face idx).segments j).length) :
    Bool :=
  rev (slotBlockEquiv iface face idx topology rev hKept hTwo x).1

/-- **The two endpoint equations of the retained core model**, against the slot
bijection `slotModel` and the orientation flag `reversedSlot` this file has
already built.  Nothing in this file produces an instance of this predicate: it
is what the vertex half (`RetainedVertexModel`) has to supply. -/
def EndpointEquations (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (hTwo : CarriesAtMostTwo idx)
    (vertexModel : RefinementCore.RefinedVertex (Retained.segmentData iface face idx) →
      Fin (cutSpec iface face idx topology rev hKept).n) : Prop :=
  (∀ x : Σ j : Fin p', Fin ((Retained.segmentData iface face idx).segments j).length,
      (cutSpec iface face idx topology rev hKept).spec.core.tail
          (slotModel iface face idx topology rev hKept hTwo x) =
        vertexModel (if reversedSlot iface face idx topology rev hKept hTwo x then
          RefinementCore.segmentHeadVertex (Retained.segmentData iface face idx) x
          else RefinementCore.segmentTailVertex (Retained.segmentData iface face idx) x)) ∧
  (∀ x : Σ j : Fin p', Fin ((Retained.segmentData iface face idx).segments j).length,
      (cutSpec iface face idx topology rev hKept).spec.core.head
          (slotModel iface face idx topology rev hKept hTwo x) =
        vertexModel (if reversedSlot iface face idx topology rev hKept hTwo x then
          RefinementCore.segmentTailVertex (Retained.segmentData iface face idx) x
          else RefinementCore.segmentHeadVertex (Retained.segmentData iface face idx) x))

/-- **What remains of the core model, in one statement.**  With the slot
bijection and the length equation discharged, a `RefinementCore.CoreModel` of
the retained segment data on the cut spec is exactly a bijection of the refined
core vertices satisfying the two endpoint equations.  Producing that bijection
is the vertex half; it needs `RetainedTraversal`'s walk, `RetainedFibre`'s
marker/fibre dichotomy, the general-forest injectivity of the class map, and
`RetainedCut.RetainedExhausts`. -/
def coreModel_of_vertexModel
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (hTwo : CarriesAtMostTwo idx)
    (vertexModel : RefinementCore.RefinedVertex (Retained.segmentData iface face idx) ≃
      Fin (cutSpec iface face idx topology rev hKept).n)
    (hEq : EndpointEquations iface face idx topology rev hKept hTwo vertexModel) :
    RefinementCore.CoreModel (Retained.segmentData iface face idx)
      (cutSpec iface face idx topology rev hKept).spec where
  slotModel := slotModel iface face idx topology rev hKept hTwo
  vertexModel := vertexModel
  reversed := reversedSlot iface face idx topology rev hKept hTwo
  length_eq := length_eq_slotModel iface face idx topology rev hKept hTwo
  tail_eq := hEq.1
  head_eq := hEq.2

/-- **The vertex bijection from an injection.**  `RetainedCut.RetainedExhausts`
is the general-forest genus count, and
`RetainedCut.card_refinedVertex_eq_cutSpec_n` turns it into the statement that
the two vertex sets have the same size; so on it an injection is a bijection. -/
def vertexEquivOfInjective (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (hTwo : CarriesAtMostTwo idx) (hExh : RetainedExhausts topology n' p')
    (vertexModel : RefinementCore.RefinedVertex (Retained.segmentData iface face idx) →
      Fin (cutSpec iface face idx topology rev hKept).n)
    (hInj : Function.Injective vertexModel) :
    RefinementCore.RefinedVertex (Retained.segmentData iface face idx) ≃
      Fin (cutSpec iface face idx topology rev hKept).n :=
  Equiv.ofBijective vertexModel
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨hInj, by
        rw [Fintype.card_fin]
        exact card_refinedVertex_eq_cutSpec_n iface face idx topology rev hTwo hKept hExh⟩)

/-- **The core model from an injection and the genus count.**  This is the
shape the vertex half supplies: no bijection has to be exhibited, only an injective vertex
map satisfying the two endpoint equations, because
`RetainedCut.RetainedExhausts` supplies the missing cardinality. -/
def coreModel_of_injective_of_exhausts
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (hTwo : CarriesAtMostTwo idx) (hExh : RetainedExhausts topology n' p')
    (vertexModel : RefinementCore.RefinedVertex (Retained.segmentData iface face idx) →
      Fin (cutSpec iface face idx topology rev hKept).n)
    (hInj : Function.Injective vertexModel)
    (hEq : EndpointEquations iface face idx topology rev hKept hTwo vertexModel) :
    RefinementCore.CoreModel (Retained.segmentData iface face idx)
      (cutSpec iface face idx topology rev hKept).spec :=
  coreModel_of_vertexModel iface face idx topology rev hKept hTwo
    (vertexEquivOfInjective iface face idx topology rev hKept hTwo hExh vertexModel hInj) hEq

/-! ## 10.  The arithmetic, concretely

No structure is introduced: `slotModel` is an `Equiv` between two `Fintype`s
whose inhabitants are the pairs themselves, and `coreModel_of_vertexModel`
inhabits `RefinementCore.CoreModel`, whose other producers are
`RefinementCore.coreModelOfRelabeling` and, at the empty forest,
`OrientedTraversal.RowDictionary.sourceModel`.  What is new is the mirror index
`pieceIndex` puts on a kept slot the row traverses backwards, and it is
evaluated here on the straddle `RetainedCut` §7 exhibits: one occurrence of
length three cut at metric position one, so a kept slot with two pieces. -/

example : OrderedPathSplit.positiveSegments ((cutList [3] 1).getD 0 []) = [1, 2] := rfl

/-- On a kept slot with two pieces the row traverses backwards, the two indices
are exchanged. -/
example : cond true (2 - 1 - 0) 0 = 1 := rfl

example : cond true (2 - 1 - 1) 1 = 0 := rfl

/-- and on one it traverses forwards they are fixed. -/
example : cond false (2 - 1 - 0) 0 = 0 := rfl

/-- The reversed prescribed list really is the reversed piece list. -/
example : ([1, 2] : List ℕ).reverse = [2, 1] := rfl

example : ([1, 2] : List ℕ).reverse.getD 0 0 = ([1, 2] : List ℕ).getD (2 - 1 - 0) 0 := rfl

end Slots

/-! ## 11.  The cut relabelling, reduced to the vertex half -/

section Reduction

open Utilities.Subdivision.CoreExpansion
open DraismaVargas.LocalCases.RequestedExpandedEndpoints
open DraismaVargas.LocalCases.StrongRefinement
open DraismaVargas.LocalCases.TerminalExhausts

/-- **`RetainedRelabeling.CutRelabeling`, reduced to the vertex half.**

`RetainedCut.cutRelabeling_of_cutCoreModel` reduces it to a
`RefinementCore.CoreModel` of the retained segment data on the canonical cut.
§9 supplies that model's slot bijection and its length equation outright, so
what is left is exactly what this binder asks for: a bijection
of the refined core vertices, and the two endpoint equations against the slot
bijection already built.

The binder is `RetainedRelabeling.CutRelabeling`'s own, verbatim, with the
`Nonempty (CoreModel …)` of `cutRelabeling_of_cutCoreModel` replaced by that
vertex datum.  `hTwo` is the one extra hypothesis, and
`RetainedCut.carried_length_le_two` discharges it at the requested expansion
model. -/
theorem cutRelabeling_of_vertexModel {N Q m q : ℕ} {model : SubdivisionGraph.Spec N Q}
    {G : Finset (Fin Q)} {req : SubdivisionGraph.Spec m q}
    {idx : RetainedIndex model G req} (hTwo : CarriesAtMostTwo idx)
    (H : ∀ (degree : ℕ) (coordinate : Type) [Fintype coordinate] [DecidableEq coordinate]
      (tgt : CFGraph.{0}) (gdata : GluingDatum tgt degree) (wall : tgt.V)
      (candidate : Candidate tgt degree gdata wall)
      (strong : StrongPresentation candidate.datum coordinate)
      (coordinates : coordinate → ℚ)
      (iface : InputInterface model strong.toPresentation coordinates G)
      (dict : CoreDictionary model strong iface),
      Faithful dict → Spanning dict → candidate.datum.Connected →
      SourceGenusMatches model candidate.datum →
      ∀ (face : ClearedFace candidate strong.toPresentation coordinates)
        (topology : ClearedFace.SourceContractionTopology face)
        (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty),
        ∃ (rev : SlotIndex iface face → Bool)
          (vertexModel :
            RefinementCore.RefinedVertex (Retained.segmentData iface face idx) ≃
              Fin (cutSpec iface face idx topology rev hKept).n),
          EndpointEquations iface face idx topology rev hKept hTwo vertexModel) :
    RetainedRelabeling.CutRelabeling model G req idx := by
  refine RetainedCut.cutRelabeling_of_cutCoreModel ?_
  intro degree coordinate _ _ tgt gdata wall candidate strong coordinates iface dict
    hFaithful hSpanning hConnected hSource face topology hKept
  obtain ⟨rev, vertexModel, hEq⟩ := H degree coordinate tgt gdata wall candidate
    strong coordinates iface dict hFaithful hSpanning hConnected hSource face topology hKept
  exact ⟨rev, ⟨coreModel_of_vertexModel iface face idx topology rev hKept hTwo
    vertexModel hEq⟩⟩

end Reduction

end

end DraismaVargas.LocalCases.RetainedCoreModel
