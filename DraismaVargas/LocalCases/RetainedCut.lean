import DraismaVargas.Infrastructure.OccurrenceCut
import DraismaVargas.LocalCases.RetainedRelabeling

/-!
# The canonical cut of the pruned contracted source

**Source.**  Draisma--Vargas Part I, the proof of the main theorem (§5.4): a
requested metric graph is realized as a point of the closed cone of a
trivalent combinatorial type, with zero length on exactly the collapsed edges.
At a terminal face the model's target is the pruned contracted spec, and the
collapsed edges are the zero rows of the trivalent model.  The marker cut
itself is in neither paper -- see the source paragraphs of
`DraismaVargas.LocalCases.RetainedRelabeling` and of
`DraismaVargas.Infrastructure.OccurrenceCut`: neither paper spells out the
transport at an integral scale, and the ordered block split
(`DraismaVargas.Infrastructure.OrderedBlockSplit`) is bookkeeping the papers do
not need.

## What is proved

`RetainedRelabeling.CutRelabeling` asks, at each terminal face, for a
`CanonicalSplitChain` out of the face's pruned contracted spec together with a
`RefinementCore.CoreModel` of the retained segment data on its far end.
`RetainedRelabeling` also proves that the chain's length is forced -- the
retained refinement has `(keptSlots topology).card + ∑ cutCount` slots
(`RetainedRelabeling.sum_segments_eq_card_keptSlots_add`), one more than the
pruned source for every occurrence a marker straddles.  This file builds that
chain.

* §1 measures the kept slots on the rows: `positiveLengths` is the positive
  sublist of a row, measured, and it is `OrderedPathSplit.positiveSegments` of
  the row's cleared occurrence lengths (`positiveLengths_eq_positiveSegments`).
  Because a cut does not see the contracted occurrences
  (`OccurrenceCut.positiveSegments_splitSum`), the pieces can be indexed by the
  *positive* occurrences -- i.e. by the kept slots, through
  `RetainedRelabeling.keptSlotEquiv` -- with no reference to a position in the
  uncut row.  `positiveRow_ne_nil_of_not_mem_forest` is the general-forest
  replacement of `OrientedTraversal.RowDictionary.positiveRow_ne_nil`, which is
  stated at `F = ∅` and is false on a forest row: off the forest a row still
  carries its positive scaled stable length.

* §2 is the cut.  `cutOffsetAt` is the metric position of the marker along a
  retained row -- the first prescribed block total -- and `pieces` is the list
  of pieces it leaves of one kept slot: `[len]` when the marker misses that
  occurrence and `[a - S, S + len - a]` when it straddles it
  (`positiveSegments_pieces`).  Each piece list sums to the occurrence
  (`sum_pieces`), which is the length the pruned spec gives that slot
  (`prunedSpec_length_slotIndexEquivKept`).

* §3 assembles them: `cutData` is the
  `SlotRefinement.SegmentData (packed (prunedSpec topology hKept))` whose
  segment list is the (possibly reversed) piece list of each kept slot, and
  `cutChain : CanonicalSplitChain (packed (prunedSpec topology hKept)) cutSpec`
  is the chain it generates -- at most one step per marker.  The orientation
  flag `rev` is a parameter: the pieces are listed along the row, while the
  pruned spec orients each slot by the source's own `sourceEnds`; the retained
  core model instantiates `rev` with the traversal's
  `RetainedTraversal.reversedAt`.

* §4 matches the two readings of the cut and counts them.
  `flatten_map_carried_segments` is the crux: concatenating the segment lists
  the **retained** refinement prescribes along one retained row -- one per
  requested slot the row carries -- gives exactly the list obtained by cutting
  each **kept slot** of that row at the marker. The two sides therefore index
  one and the same ordered list of positive pieces, which is what the slot
  bijection of the retained core model is built from. Taking lengths,
  `cutSpec_p` says the chain's target has the same number of slots as the
  retained refinement,
  `∑ j, ((Retained.segmentData iface face idx).segments j).length`, hence (with
  the count of `RetainedRelabeling`) `(keptSlots topology).card + ∑ cutCount`
  (`cutSpec_p_eq_card_keptSlots_add`).

  §4 ends with the matching vertex count: `RetainedExhausts` is the
  general-forest analogue of the exhaustion count at the empty forest
  (`keptClasses.card + p' = n' + keptSlots.card`), and on it
  `card_refinedVertex_eq_cutSpec_n` says the refined core vertices of the
  retained refinement are as many as the core vertices of `cutSpec`.  With
  `cutSpec_p` that settles **both** cardinalities the core model's two
  bijections need, so the core model has only to produce two *injections* and
  the three endpoint equations.

* §5 reduces `RetainedRelabeling.CutRelabeling` to this file's chain:
  `cutRelabeling_of_cutCoreModel` says
  `RetainedRelabeling.CutRelabeling model F small idx` follows from a
  `RefinementCore.CoreModel` of the retained segment data on `cutSpec` alone,
  for some orientation flag.  The chain half of the relabeling is discharged.

* §6 discharges the file's one hypothesis for the expansion model of the
  stable-model reduction: every carrier list of
  `RetainedIndexProducer.retainedIndex` has length at most two
  (`carried_length_le_two`), because a `CoreExpansion.SlotKind` is `single` or
  `double`.

## What is not proved here -- the explicit hypotheses

1. **`hTwo`**: every retained slot carries at most two requested slots, i.e.
   at most one marker per row.  This is what lets `OccurrenceCut.cutList`
   describe the pieces with a single cut total; §6 proves it for the expansion
   model of the stable-model reduction, so it restricts only the generality of
   the statements.  A retained slot carrying three requested slots would need
   the general transpose of `OrderedBlockSplit.blocks` (see `OccurrenceCut`'s
   "What is NOT proved").
2. **The core model itself.**  This file produces the chain, proves its target
   has the right slot count, and proves the list identity the slot bijection is
   read off; it does **not** produce
   `RefinementCore.CoreModel (Retained.segmentData iface face idx) cutSpec.spec`.
   The slot half of that model turns `flatten_map_carried_segments` into an
   `Equiv` by the flatten-index gadget (`Infrastructure.FlattenIndex`) and the
   regroupings `Fin p' ≃ Σ e, Fin (idx.carried e).length` and
   `RetainedRelabeling.SlotIndex ≃ Σ e, Fin (positiveRow ↑e).length`; the
   vertex half re-indexes `OrientedTraversal` §3's `breakVertex` and
   `vertexClass` through the `RetainedIndex` (see
   `DraismaVargas.LocalCases.RetainedTraversal` and
   `DraismaVargas.LocalCases.RetainedFibre`), with the markers landing on the
   **new** split vertices of `cutSpec` rather than on contraction classes.  The
   general-forest genus count is `RetainedExhausts.retainedExhausts_of_expansion`,
   the vertex model with its endpoint equations is
   `RetainedVertexModel.vertexModel`, and `RetainedClassInjectivity` supplies
   the injectivity of the class half.
3. Everything `CutRelabeling` already keeps inside its binder: the core
   dictionary, `Faithful`, `Spanning`, `Connected`, `SourceGenusMatches`, the
   topology and the kept class.

## Consumers

The retained core model (`RetainedCoreModel`, `RetainedVertexModel`) behind
`RetainedRelabeling.CutRelabeling`, and through it `StatementFromLink`'s route
to `DraismaVargas.Statement`.
-/

namespace DraismaVargas.LocalCases.RetainedCut

noncomputable section

open Utilities
open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.IteratedSplitRefinement
open Utilities.Subdivision.CoreExpansion
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.BlockSplitCount
open DraismaVargas.Infrastructure.OccurrenceCut
open DraismaVargas.Infrastructure.OrderedBlockSplit
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancedGlobal.Candidate
open DraismaVargas.LocalCases.InputRefinementData
open DraismaVargas.LocalCases.RetainedRelabeling
open DraismaVargas.LocalCases.SlotRefinement
open DraismaVargas.LocalCases.StrongRefinement
open DraismaVargas.LocalCases.TraversalPresentation
open DraismaVargas.LocalCases.ZeroForestPreservation

section Cut

variable {target : CFGraph} {degree : ℕ}
  {gluing : GluingDatum target degree} {wall : target.V}
  {candidate : Candidate target degree gluing wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {coordinates : coordinate → ℚ}
  {n p : ℕ} {spec : SubdivisionGraph.Spec n p} {F : Finset (Fin p)}
  {strong : StrongPresentation candidate.datum coordinate}
  {face : ClearedFace candidate strong.toPresentation coordinates}
  {n' p' : ℕ} {small : SubdivisionGraph.Spec n' p'}

/-! ## 1.  The kept slots of a row, measured -/

/-- The cleared lengths of the surviving occurrences of a row, in traversal
order: one entry per kept slot the row displays. -/
def positiveLengths (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates) (i : Fin p) : List ℕ :=
  (positiveRow iface face i).map face.realization.sourceLength

variable {iface : InputInterface spec strong.toPresentation coordinates F}

/-- **and it is the positive sublist of the measured row.**  The general-forest
form of `OrientedTraversal.RowDictionary.segments_eq_positiveRow`. -/
theorem positiveLengths_eq_positiveSegments (i : Fin p) :
    positiveLengths iface face i =
      OrderedPathSplit.positiveSegments (rowSegments iface face i) := by
  rw [OrderedPathSplit.positiveSegments, rowSegments, List.filter_map]
  rfl

@[simp] theorem length_positiveLengths (i : Fin p) :
    (positiveLengths iface face i).length = (positiveRow iface face i).length :=
  List.length_map _

theorem getD_positiveLengths {i : Fin p} {m : ℕ} (hm : m < (positiveRow iface face i).length) :
    (positiveLengths iface face i).getD m 0 =
      face.realization.sourceLength (positiveRow iface face i)[m] := by
  rw [positiveLengths, List.getD_eq_getElem _ _ (by simpa using hm), List.getElem_map]

theorem getD_positiveLengths_pos {i : Fin p} {m : ℕ}
    (hm : m < (positiveRow iface face i).length) :
    0 < (positiveLengths iface face i).getD m 0 := by
  rw [getD_positiveLengths hm]
  exact (mem_positiveRow.mp (List.getElem_mem hm)).2

/-- A forest row displays no kept slot. -/
theorem positiveLengths_eq_nil_of_mem_forest {i : Fin p} (hi : i ∈ F) :
    positiveLengths iface face i = [] := by
  rw [positiveLengths, positiveRow_eq_nil_of_mem_forest hi, List.map_nil]

theorem sum_positiveLengths (i : Fin p) :
    (positiveLengths iface face i).sum = (rowSegments iface face i).sum := by
  rw [positiveLengths_eq_positiveSegments, OrderedPathSplit.sum_positiveSegments]

/-- **No retained row is contracted entirely.**  The general-forest form of
`OrientedTraversal.RowDictionary.positiveRow_ne_nil`, which is stated at
`F = ∅` and is *false* on a forest row: off the forest the interface still
makes the row total the positive scaled stable length
(`InputRefinementData.rowSegments_sum_of_not_mem`), and the surviving
occurrences carry all of it.  This is the replacement the general-forest
confinement argument of `ClassInjectivity` §4 needs. -/
theorem positiveRow_ne_nil_of_not_mem_forest {i : Fin p} (hi : i ∉ F) :
    positiveRow iface face i ≠ [] := by
  intro hNil
  have hsum : (rowSegments iface face i).sum = face.scale * spec.length i :=
    rowSegments_sum_of_not_mem iface face hi
  have hzero : (rowSegments iface face i).sum = 0 := by
    rw [← sum_positiveLengths (iface := iface) (face := face) i, positiveLengths, hNil]
    rfl
  have hpos := Nat.mul_pos face.scale_pos (spec.length_pos i)
  omega

/-- and therefore some occurrence of a retained row survives the
contraction. -/
theorem exists_sourceLength_pos_of_not_mem_forest {i : Fin p} (hi : i ∉ F) :
    ∃ edge ∈ row iface i, 0 < face.realization.sourceLength edge := by
  obtain ⟨edge, hedge⟩ :=
    List.exists_mem_of_ne_nil _ (positiveRow_ne_nil_of_not_mem_forest (iface := iface) hi)
  exact ⟨edge, (mem_positiveRow.mp hedge).1, (mem_positiveRow.mp hedge).2⟩

/-! ## 2.  The marker's metric position, and the pieces it leaves -/

/-- **The metric position of the marker along a row.**  The first prescribed
block total: the point at which the retained slot hands over from the first
requested slot it carries to the second.  On a row carrying a single requested
slot it is the row total, so no occurrence is cut; on a forest row it is
irrelevant and set to zero. -/
def cutOffsetAt (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small) (i : Fin p) : ℕ :=
  if h : i ∈ F then 0 else (Retained.blockTotals face idx ⟨i, h⟩).headD 0

theorem cutOffsetAt_coe (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small) (e : {i : Fin p // i ∉ F}) :
    cutOffsetAt face idx ↑e = (Retained.blockTotals face idx e).headD 0 := by
  rw [cutOffsetAt, dif_neg e.2]

/-- **The pieces of one kept slot.**  The occurrence carrying the refined slot
`x`, cut at the marker if the marker falls strictly inside it. -/
def pieces (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small) (x : SlotIndex iface face) : List ℕ :=
  (cutList (positiveLengths iface face x.1) (cutOffsetAt face idx x.1)).getD (x.2 : ℕ) []

/-- **Each piece list recovers its occurrence.** -/
theorem sum_pieces (idx : RetainedIndex spec F small) (x : SlotIndex iface face) :
    (pieces iface face idx x).sum = face.realization.sourceLength (occurrence x) := by
  rw [pieces, sum_getD_cutList, getD_positiveLengths x.2.isLt]
  rfl

/-- **The canonical cut, kept slot by kept slot.**  The occurrence is left
whole unless the marker falls strictly inside it, in which case it is cut in
two at the marker; `S` is the total of the earlier kept slots of the same
row. -/
theorem positiveSegments_pieces (idx : RetainedIndex spec F small)
    (x : SlotIndex iface face) :
    OrderedPathSplit.positiveSegments (pieces iface face idx x) =
      (if ((positiveLengths iface face x.1).take (x.2 : ℕ)).sum < cutOffsetAt face idx x.1 ∧
          cutOffsetAt face idx x.1 <
            ((positiveLengths iface face x.1).take (x.2 : ℕ)).sum +
              face.realization.sourceLength (occurrence x) then
        [cutOffsetAt face idx x.1 - ((positiveLengths iface face x.1).take (x.2 : ℕ)).sum,
          ((positiveLengths iface face x.1).take (x.2 : ℕ)).sum +
            face.realization.sourceLength (occurrence x) - cutOffsetAt face idx x.1]
      else [face.realization.sourceLength (occurrence x)]) := by
  have hgetD : (positiveLengths iface face x.1).getD (x.2 : ℕ) 0 =
      face.realization.sourceLength (occurrence x) := getD_positiveLengths x.2.isLt
  have hpos : 0 < (positiveLengths iface face x.1).getD (x.2 : ℕ) 0 :=
    getD_positiveLengths_pos x.2.isLt
  rw [pieces, positiveSegments_getD_cutList _ _ _ hpos, hgetD]

/-! ## 3.  The segment data on the pruned contracted spec, and its chain -/

@[simp] theorem keptSlotEquiv_val
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (topology : ClearedFace.SourceContractionTopology face) (x : SlotIndex iface face) :
    (keptSlotEquiv iface topology x).val.val =
      slotOf candidate.datum face.realization (occurrence x) := rfl

theorem sourceEdgeAt_keptSlotEquiv
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (topology : ClearedFace.SourceContractionTopology face) (x : SlotIndex iface face) :
    face.realization.sourceEdgeAt (keptSlotEquiv iface topology x).val.val = occurrence x := by
  rw [keptSlotEquiv_val, sourceEdgeAt_slotOf]

/-- The kept slots, indexed as the slots of the pruned contracted spec. -/
def slotIndexEquivKept (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (topology : ClearedFace.SourceContractionTopology face) :
    SlotIndex iface face ≃
      Fin (ClearedFace.SourceContractionTopology.keptSlots topology).card :=
  (keptSlotEquiv iface topology).trans (RefinementCore.keptSlotIndex topology)

/-- **The pruned spec gives a kept slot the length of its occurrence.** -/
theorem prunedSpec_length_slotIndexEquivKept
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (topology : ClearedFace.SourceContractionTopology face)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (x : SlotIndex iface face) :
    (ClearedFace.SourceContractionTopology.prunedSpec topology hKept).length
        (slotIndexEquivKept iface face topology x) =
      face.realization.sourceLength (occurrence x) := by
  show (ClearedFace.SourceContractionTopology.prunedSpec topology hKept).length
      (RefinementCore.keptSlotIndex topology (keptSlotEquiv iface topology x)) = _
  rw [RefinementCore.prunedSpec_length]
  show face.realization.sourceLength
      (face.realization.sourceEdgeAt (keptSlotEquiv iface topology x).val.val) = _
  rw [sourceEdgeAt_keptSlotEquiv]

/-- The prescribed list of pieces of a slot of the pruned contracted spec,
oriented by `rev`: the pieces are listed in the order the row traverses them,
and `rev` records which slots the row traverses against the orientation the
source's own `sourceEnds` gives them. -/
def cutSegments (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (s : Fin (ClearedFace.SourceContractionTopology.keptSlots topology).card) : List ℕ :=
  if rev ((slotIndexEquivKept iface face topology).symm s) then
    (pieces iface face idx ((slotIndexEquivKept iface face topology).symm s)).reverse
  else pieces iface face idx ((slotIndexEquivKept iface face topology).symm s)

theorem sum_cutSegments (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (s : Fin (ClearedFace.SourceContractionTopology.keptSlots topology).card) :
    (cutSegments iface face idx topology rev s).sum =
      (ClearedFace.SourceContractionTopology.prunedSpec topology hKept).length s := by
  have hx := prunedSpec_length_slotIndexEquivKept iface face topology hKept
    ((slotIndexEquivKept iface face topology).symm s)
  rw [Equiv.apply_symm_apply] at hx
  rw [cutSegments]
  split_ifs
  · rw [List.sum_reverse, sum_pieces, hx]
  · rw [sum_pieces, hx]

theorem countPos_cutSegments (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (s : Fin (ClearedFace.SourceContractionTopology.keptSlots topology).card) :
    countPos (cutSegments iface face idx topology rev s) =
      countPos (pieces iface face idx ((slotIndexEquivKept iface face topology).symm s)) := by
  rw [cutSegments]
  split_ifs
  · exact countPos_reverse _
  · rfl

/-- **The canonical cut of the pruned contracted spec.**  One segment list per
kept slot: the slot itself where no marker falls inside it, and its two pieces
where one does. -/
def cutData (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty) :
    SegmentData (packed (ClearedFace.SourceContractionTopology.prunedSpec topology hKept)) :=
  SegmentData.ofListsWithZeros _ (cutSegments iface face idx topology rev)
    (fun s ↦ sum_cutSegments iface face idx topology rev hKept s)

@[simp] theorem cutData_segments
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (s : Fin (ClearedFace.SourceContractionTopology.keptSlots topology).card) :
    (cutData iface face idx topology rev hKept).segments s =
      OrderedPathSplit.positiveSegments (cutSegments iface face idx topology rev s) :=
  rfl

/-- **The far end of the chain**: the pruned contracted spec with each
straddled kept slot cut in two. -/
def cutSpec (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty) :
    PackedSpec :=
  refineAllSlots (cutData iface face idx topology rev hKept)

/-- **The chain `RetainedRelabeling.CutRelabeling` asks for.**  A canonical
chain of positive bivalent splits out of the face's pruned contracted spec, one
step per straddled kept slot -- and `Spec.graph` is the unit subdivision, so by
`CanonicalSplitChain.laplacianEquiv` it does not change the graph. -/
def cutChain (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty) :
    CanonicalSplitChain
      (packed (ClearedFace.SourceContractionTopology.prunedSpec topology hKept))
      (cutSpec iface face idx topology rev hKept) :=
  refineAllSlotsChain (cutData iface face idx topology rev hKept)

/-! ## 4.  The count: the chain's target has the retained refinement's slots -/

/-- At most one marker per retained row: every retained slot carries at most
two requested slots.  §6 proves it for the expansion model of the stable-model
reduction. -/
def CarriesAtMostTwo (idx : RetainedIndex spec F small) : Prop :=
  ∀ e : {i : Fin p // i ∉ F}, (idx.carried e).length ≤ 2

/-- The block of a retained slot carrying a single requested slot is the whole
row. -/
theorem blockSegments_of_carried_singleton
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small) {e : {i : Fin p // i ∉ F}} {j : Fin p'}
    (hcar : idx.carried e = [j]) :
    Retained.blockSegments iface face idx j = rowSegments iface face ↑e := by
  have hmem : j ∈ idx.carried e := by rw [hcar]; simp
  have howner : idx.owner j = e := idx.owner_eq_of_mem e j hmem
  have hlt : (0 : ℕ) < (idx.carried e).length := by rw [hcar]; simp
  have hget : (idx.carried e)[(0 : ℕ)]'hlt = j := by
    simp only [hcar]
    rfl
  have hpos : idx.pos j = 0 := by
    have h := pos_getElem idx e hlt
    rwa [hget] at h
  have htot : Retained.blockTotals face idx e = [face.scale * small.length j] := by
    rw [Retained.blockTotals, hcar]
    rfl
  rw [Retained.blockSegments, howner, hpos, htot, blocks_singleton]
  rfl

/-- and a retained slot carrying two requested slots splits its row at the
marker. -/
theorem blockSegments_of_carried_pair
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small) {e : {i : Fin p // i ∉ F}} {j₁ j₂ : Fin p'}
    (hcar : idx.carried e = [j₁, j₂]) :
    Retained.blockSegments iface face idx j₁ =
        (splitSum (rowSegments iface face ↑e) (face.scale * small.length j₁)).1 ∧
      Retained.blockSegments iface face idx j₂ =
        (splitSum (rowSegments iface face ↑e) (face.scale * small.length j₁)).2 := by
  have hmem₁ : j₁ ∈ idx.carried e := by rw [hcar]; simp
  have hmem₂ : j₂ ∈ idx.carried e := by rw [hcar]; simp
  have howner₁ : idx.owner j₁ = e := idx.owner_eq_of_mem e j₁ hmem₁
  have howner₂ : idx.owner j₂ = e := idx.owner_eq_of_mem e j₂ hmem₂
  have hlt₀ : (0 : ℕ) < (idx.carried e).length := by rw [hcar]; simp
  have hlt₁ : (1 : ℕ) < (idx.carried e).length := by rw [hcar]; simp
  have hget₀ : (idx.carried e)[(0 : ℕ)]'hlt₀ = j₁ := by
    simp only [hcar]
    rfl
  have hget₁ : (idx.carried e)[(1 : ℕ)]'hlt₁ = j₂ := by
    simp only [hcar]
    rfl
  have hpos₁ : idx.pos j₁ = 0 := by
    have h := pos_getElem idx e hlt₀
    rwa [hget₀] at h
  have hpos₂ : idx.pos j₂ = 1 := by
    have h := pos_getElem idx e hlt₁
    rwa [hget₁] at h
  have htot : Retained.blockTotals face idx e =
      [face.scale * small.length j₁, face.scale * small.length j₂] := by
    rw [Retained.blockTotals, hcar]
    rfl
  constructor
  · rw [Retained.blockSegments, howner₁, hpos₁, htot, blocks_pair]
    rfl
  · rw [Retained.blockSegments, howner₂, hpos₂, htot, blocks_pair]
    rfl

/-- **The two readings of the cut agree, piece by piece.**  Concatenating the
segment lists the retained refinement prescribes along one retained row -- one
per requested slot the row carries -- gives exactly the list obtained by
cutting each kept slot of the row at the marker.  This is
`OccurrenceCut.flatten_map_positiveSegments_cutList` transported to the face,
and it is what the slot bijection of the retained core model is built from: the
two sides index the *same ordered list* of positive pieces. -/
theorem flatten_map_carried_segments
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (hTwo : CarriesAtMostTwo idx) (e : {i : Fin p // i ∉ F}) :
    ((idx.carried e).map fun j ↦ (Retained.segmentData iface face idx).segments j).flatten =
      ((cutList (positiveLengths iface face ↑e) (cutOffsetAt face idx ↑e)).map
        OrderedPathSplit.positiveSegments).flatten := by
  have hL : positiveLengths iface face ↑e =
      OrderedPathSplit.positiveSegments (rowSegments iface face ↑e) :=
    positiveLengths_eq_positiveSegments (iface := iface) (face := face) ↑e
  have hsum := sum_blockTotals_eq_sum_rowSegments (iface := iface) (face := face) idx e
  have hcut := cutOffsetAt_coe face idx e
  rw [flatten_map_positiveSegments_cutList]
  rcases hcar : idx.carried e with _ | ⟨j₁, tail⟩
  · exact absurd hcar (idx.carried_ne_nil e)
  · have htot : Retained.blockTotals face idx e =
        (j₁ :: tail).map fun k ↦ face.scale * small.length k := by
      rw [Retained.blockTotals, hcar]
    rcases tail with _ | ⟨j₂, tail'⟩
    · -- one requested slot: the cut is at the row total, so nothing is cut
      rw [htot] at hsum hcut
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.headD_cons] at hsum hcut
      have ha : cutOffsetAt face idx ↑e = (positiveLengths iface face ↑e).sum := by
        rw [hcut, sum_positiveLengths]
        omega
      rw [ha, splitSum_of_sum_le (le_refl _)]
      simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil, positiveSegments_nil]
      rw [Retained.segmentData_segments,
        blockSegments_of_carried_singleton iface face idx hcar, hL,
        positiveSegments_idem]
    · rcases tail' with _ | ⟨j₃, tail''⟩
      · -- two requested slots: one marker, one cut
        rw [htot] at hcut
        simp only [List.map_cons, List.map_nil, List.headD_cons] at hcut
        obtain ⟨hb₁, hb₂⟩ := blockSegments_of_carried_pair iface face idx hcar
        simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
          List.append_nil]
        rw [Retained.segmentData_segments, Retained.segmentData_segments, hb₁, hb₂,
          ← hcut, hL, positiveSegments_splitSum_fst, positiveSegments_splitSum_snd]
      · exact absurd (hTwo e) (by rw [hcar]; simp)

/-- The cut described on the measured row, block by block, under `hTwo`. -/
theorem sum_map_countPos_blocks_eq
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (hTwo : CarriesAtMostTwo idx) (e : {i : Fin p // i ∉ F}) :
    ((blocks (rowSegments iface face ↑e) (Retained.blockTotals face idx e)).map countPos).sum =
      countPos (splitSum (positiveLengths iface face ↑e) (cutOffsetAt face idx ↑e)).1 +
        countPos (splitSum (positiveLengths iface face ↑e) (cutOffsetAt face idx ↑e)).2 := by
  have hL : positiveLengths iface face ↑e =
      OrderedPathSplit.positiveSegments (rowSegments iface face ↑e) :=
    positiveLengths_eq_positiveSegments (iface := iface) (face := face) ↑e
  have hfst : countPos (splitSum (rowSegments iface face ↑e) (cutOffsetAt face idx ↑e)).1 =
      countPos (splitSum (positiveLengths iface face ↑e) (cutOffsetAt face idx ↑e)).1 := by
    rw [hL]
    exact congrArg List.length
      (positiveSegments_splitSum_fst (rowSegments iface face ↑e) (cutOffsetAt face idx ↑e))
  have hsnd : countPos (splitSum (rowSegments iface face ↑e) (cutOffsetAt face idx ↑e)).2 =
      countPos (splitSum (positiveLengths iface face ↑e) (cutOffsetAt face idx ↑e)).2 := by
    rw [hL]
    exact congrArg List.length
      (positiveSegments_splitSum_snd (rowSegments iface face ↑e) (cutOffsetAt face idx ↑e))
  have hsum := sum_blockTotals_eq_sum_rowSegments (iface := iface) (face := face) idx e
  have hcut := cutOffsetAt_coe face idx e
  rcases hcar : idx.carried e with _ | ⟨j₁, tail⟩
  · exact absurd hcar (idx.carried_ne_nil e)
  · have htot : Retained.blockTotals face idx e =
        (j₁ :: tail).map fun k ↦ face.scale * small.length k := by
      rw [Retained.blockTotals, hcar]
    rcases tail with _ | ⟨j₂, tail'⟩
    · -- one requested slot: the row is one block, and the cut is at the row total
      rw [htot] at hsum hcut
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.headD_cons] at hsum hcut
      rw [htot]
      simp only [List.map_cons, List.map_nil]
      rw [blocks_singleton]
      have ha : cutOffsetAt face idx ↑e = (positiveLengths iface face ↑e).sum := by
        rw [hcut, sum_positiveLengths]
        omega
      rw [ha, splitSum_of_sum_le (le_refl _)]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, countPos_nil]
      rw [hL, countPos_positiveSegments]
    · rcases tail' with _ | ⟨j₃, tail''⟩
      · -- two requested slots: one marker, one cut
        rw [htot] at hcut
        simp only [List.map_cons, List.map_nil, List.headD_cons] at hcut
        rw [htot]
        simp only [List.map_cons, List.map_nil]
        rw [blocks_pair, ← hcut]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        rw [hfst, hsnd]
        omega
      · exact absurd (hTwo e) (by rw [hcar]; simp)

/-- **The pieces of a whole row, counted.** -/
theorem sum_countPos_pieces_row
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small) (i : Fin p) :
    ∑ m : Fin (positiveRow iface face i).length,
        countPos (pieces iface face idx ⟨i, m⟩) =
      countPos (splitSum (positiveLengths iface face i) (cutOffsetAt face idx i)).1 +
        countPos (splitSum (positiveLengths iface face i) (cutOffsetAt face idx i)).2 := by
  have hlen : (positiveRow iface face i).length =
      (cutList (positiveLengths iface face i) (cutOffsetAt face idx i)).length := by
    rw [length_cutList, length_positiveLengths]
  have h1 : ∑ m : Fin (positiveRow iface face i).length,
        countPos (pieces iface face idx ⟨i, m⟩) =
      ∑ k ∈ Finset.range (positiveRow iface face i).length,
        countPos ((cutList (positiveLengths iface face i)
          (cutOffsetAt face idx i)).getD k []) :=
    Fin.sum_univ_eq_sum_range
      (fun k ↦ countPos ((cutList (positiveLengths iface face i)
        (cutOffsetAt face idx i)).getD k [])) _
  rw [h1, hlen, ← sum_map_eq_sum_range, sum_map_countPos_cutList']

/-- The forest rows contribute nothing to the cut count. -/
theorem sum_cut_eq_sum_retained
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small) :
    ∑ i : Fin p,
        (countPos (splitSum (positiveLengths iface face i) (cutOffsetAt face idx i)).1 +
          countPos (splitSum (positiveLengths iface face i) (cutOffsetAt face idx i)).2) =
      ∑ e : {i : Fin p // i ∉ F},
        (countPos (splitSum (positiveLengths iface face ↑e) (cutOffsetAt face idx ↑e)).1 +
          countPos (splitSum (positiveLengths iface face ↑e) (cutOffsetAt face idx ↑e)).2) := by
  classical
  have h1 : ∑ i ∈ Fᶜ,
      (countPos (splitSum (positiveLengths iface face i) (cutOffsetAt face idx i)).1 +
        countPos (splitSum (positiveLengths iface face i) (cutOffsetAt face idx i)).2) =
      ∑ i : Fin p,
      (countPos (splitSum (positiveLengths iface face i) (cutOffsetAt face idx i)).1 +
        countPos (splitSum (positiveLengths iface face i) (cutOffsetAt face idx i)).2) := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro i _ hi
    rw [Finset.mem_compl, not_not] at hi
    rw [positiveLengths_eq_nil_of_mem_forest hi]
    simp
  rw [← h1]
  exact Finset.sum_subtype _ (fun x ↦ Finset.mem_compl) _

/-- **The chain's target has exactly the retained refinement's slots.**  This
is the count `RetainedRelabeling.sum_segments_eq_card_keptSlots_add` forces,
and it is what makes the slot bijection of the retained core model possible at
all. -/
theorem cutSpec_p (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool) (hTwo : CarriesAtMostTwo idx)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty) :
    (cutSpec iface face idx topology rev hKept).p =
      ∑ j : Fin p', ((Retained.segmentData iface face idx).segments j).length := by
  classical
  rw [cutSpec, refineAllSlots_p]
  have hleft : ∑ s : Fin (ClearedFace.SourceContractionTopology.keptSlots topology).card,
      ((cutData iface face idx topology rev hKept).segments s).length =
      ∑ x : SlotIndex iface face, countPos (pieces iface face idx x) := by
    rw [← Equiv.sum_comp (slotIndexEquivKept iface face topology)
      (fun s ↦ ((cutData iface face idx topology rev hKept).segments s).length)]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    show countPos (cutSegments iface face idx topology rev
      (slotIndexEquivKept iface face topology x)) = _
    rw [countPos_cutSegments, Equiv.symm_apply_apply]
  have hsig : ∑ x : SlotIndex iface face, countPos (pieces iface face idx x) =
      ∑ i : Fin p, ∑ m : Fin (positiveRow iface face i).length,
        countPos (pieces iface face idx ⟨i, m⟩) := by
    rw [← Finset.univ_sigma_univ]
    exact Finset.sum_sigma _ _ _
  rw [hleft, hsig,
    Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) ↦
      sum_countPos_pieces_row iface face idx i),
    sum_cut_eq_sum_retained iface face idx,
    sum_over_carried idx (fun j ↦ ((Retained.segmentData iface face idx).segments j).length)]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [map_carried_segments_length iface idx e,
    sum_map_countPos_blocks_eq iface face idx hTwo e]

/-- **and therefore the count `RetainedRelabeling.sum_segments_eq_card_keptSlots_add`
predicts**: one slot per kept slot of the face, plus one per straddled
marker. -/
theorem cutSpec_p_eq_card_keptSlots_add
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool) (hTwo : CarriesAtMostTwo idx)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty) :
    (cutSpec iface face idx topology rev hKept).p =
      (ClearedFace.SourceContractionTopology.keptSlots topology).card +
        ∑ e : {i : Fin p // i ∉ F},
          cutCount (rowSegments iface face ↑e) (Retained.blockTotals face idx e) := by
  rw [cutSpec_p iface face idx topology rev hTwo hKept,
    sum_segments_eq_card_keptSlots_add iface idx topology]


/-- **The general-forest analogue of the exhaustion count.**  At the empty
forest exhaustion says the kept classes are exactly the core vertices of the
refinement; at a general forest the retained refinement is a refinement of
`small`, so the Euler count reads
`keptClasses.card + p' = n' + keptSlots.card`.  It is a genus identity, and as
at the empty forest it is not derivable from a slot labelling alone; it is
stated here as the shape a producer must supply.  As a genus identity it does
hold where it is used: `RetainedExhausts.retainedExhausts_of_expansion` proves
it for the expansion model of the stable-model reduction from `hKept`,
connectedness and `SourceGenusMatches` alone. -/
def RetainedExhausts (topology : ClearedFace.SourceContractionTopology face)
    (n' p' : ℕ) : Prop :=
  (ClearedFace.SourceContractionTopology.keptClasses topology).card + p' =
    n' + (ClearedFace.SourceContractionTopology.keptSlots topology).card

/-- **and it is exactly the count the vertex half of the core model needs**: the
refined core vertices of the retained refinement -- the core vertices of `small`
together with the breakpoints inside each requested slot -- are as many as the
core vertices of the chain's target, which are the kept classes together with
one new split vertex per straddled marker. -/
theorem card_refinedVertex_eq_cutSpec_n
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    (rev : SlotIndex iface face → Bool) (hTwo : CarriesAtMostTwo idx)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (hExh : RetainedExhausts topology n' p') :
    Fintype.card (RefinementCore.RefinedVertex (Retained.segmentData iface face idx)) =
      (cutSpec iface face idx topology rev hKept).n := by
  have h1 : (cutSpec iface face idx topology rev hKept).n +
      (ClearedFace.SourceContractionTopology.keptSlots topology).card =
      (ClearedFace.SourceContractionTopology.keptClasses topology).card +
        ∑ s : Fin (ClearedFace.SourceContractionTopology.keptSlots topology).card,
          ((cutData iface face idx topology rev hKept).segments s).length :=
    refineAllSlots_n (cutData iface face idx topology rev hKept)
  have h2 : Fintype.card
      (RefinementCore.RefinedVertex (Retained.segmentData iface face idx)) + p' =
      n' + ∑ j : Fin p', ((Retained.segmentData iface face idx).segments j).length := by
    rw [RefinementCore.card_refinedVertex]
    exact refineAllSlots_n (Retained.segmentData iface face idx)
  have h3 : ∑ s : Fin (ClearedFace.SourceContractionTopology.keptSlots topology).card,
      ((cutData iface face idx topology rev hKept).segments s).length =
      ∑ j : Fin p', ((Retained.segmentData iface face idx).segments j).length := by
    have := cutSpec_p iface face idx topology rev hTwo hKept
    rwa [cutSpec, refineAllSlots_p] at this
  rw [h3] at h1
  unfold RetainedExhausts at hExh
  omega

end Cut

/-! ## 5.  The reduction of `CutRelabeling` to a core model on `cutSpec` -/

section Reduction

open DraismaVargas.LocalCases.OuterWalk
open DraismaVargas.LocalCases.RefinementCore
open DraismaVargas.LocalCases.StableSourceDarts
open DraismaVargas.LocalCases.TerminalExhausts
open DraismaVargas.LocalCases.W4StableSource

/-- **`RetainedRelabeling.CutRelabeling`, reduced to the canonical cut.**

`RetainedRelabeling.CutRelabeling` asks for *some* canonical split chain out of
the pruned contracted spec together with a core model of the retained segment
data on its far end. This file has built the chain, so the receipt is exactly: a
core model of the retained segment data on `cutSpec`, for some orientation flag.
Everything else -- the chain, and the fact that it does not change the graph --
is discharged.

The binder is `RetainedRelabeling.CutRelabeling`'s own, verbatim. -/
theorem cutRelabeling_of_cutCoreModel {N Q n p : ℕ} {model : SubdivisionGraph.Spec N Q}
    {F : Finset (Fin Q)} {small : SubdivisionGraph.Spec n p}
    {idx : RetainedIndex model F small}
    (H : ∀ (degree : ℕ) (coordinate : Type) [Fintype coordinate] [DecidableEq coordinate]
      (tgt : CFGraph.{0}) (gdata : GluingDatum tgt degree) (wall : tgt.V)
      (candidate : Candidate tgt degree gdata wall)
      (strong : StrongPresentation candidate.datum coordinate)
      (coordinates : coordinate → ℚ)
      (iface : InputInterface model strong.toPresentation coordinates F)
      (dict : CoreDictionary model strong iface),
      Faithful dict → Spanning dict → candidate.datum.Connected →
      SourceGenusMatches model candidate.datum →
      ∀ (face : ClearedFace candidate strong.toPresentation coordinates)
        (topology : ClearedFace.SourceContractionTopology face)
        (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty),
        ∃ rev : SlotIndex iface face → Bool,
          Nonempty (RefinementCore.CoreModel (Retained.segmentData iface face idx)
            (cutSpec iface face idx topology rev hKept).spec)) :
    RetainedRelabeling.CutRelabeling model F small idx := by
  intro degree coordinate _ _ tgt gdata wall candidate strong coordinates iface dict
    hFaithful hSpanning hConnected hSource face topology hKept
  obtain ⟨rev, ⟨cm⟩⟩ := H degree coordinate tgt gdata wall candidate strong coordinates
    iface dict hFaithful hSpanning hConnected hSource face topology hKept
  exact ⟨cutSpec iface face idx topology rev hKept,
    cutChain iface face idx topology rev hKept, ⟨cm⟩⟩

end Reduction

/-! ## 6.  The stable-model reduction carries at most two requested slots per row -/

section Producer

variable {n₀ p₀ N Q : ℕ} {D : ExpansionData n₀ p₀ N Q} {spec₀ : Spec n₀ p₀}

/-- **Every carrier list of the expansion model has length at most two**,
because a `CoreExpansion.SlotKind` is `contracted`, `single j` or
`double j₁ j₂`: a retained cubic slot carries one requested slot, or two in
series through a single marker.  So `CarriesAtMostTwo` is not a restriction
where the retained relabeling is used. -/
theorem carried_length_le_two (hCond : D.Conditions spec₀.core) (hN : 0 < N)
    (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e) :
    CarriesAtMostTwo (RetainedIndexProducer.retainedIndex hCond hN hL) := by
  intro e
  rw [RetainedIndexProducer.retainedIndex_carried]
  cases D.kind ↑e with
  | contracted => simp [RetainedIndexProducer.kindCarried]
  | single j => simp [RetainedIndexProducer.kindCarried]
  | double j₁ j₂ => simp [RetainedIndexProducer.kindCarried]

end Producer

/-! ## 7.  The cut, concretely

No new structure is introduced here: `cutData` inhabits
`SlotRefinement.SegmentData` and `cutChain` a `CanonicalSplitChain`, whose own
producers are `SegmentData.ofListsWithZeros` and `refineAllSlotsChain`.  What
is new is the arithmetic of the cut, and it is evaluated here on the straddle
exhibited in `RetainedRelabeling` §6: one occurrence of length three, a marker
at metric position one. -/

/-- The single occurrence is cut in two. -/
example : cutList [3] 1 = [[1, 2]] := rfl

/-- An aligned marker leaves a zero-length piece, which the refinement
discards: no occurrence is really cut. -/
example : cutList [2, 3] 2 = [[2], [0, 3]] := rfl

example : OrderedPathSplit.positiveSegments ((cutList [2, 3] 2).getD 1 []) = [3] := rfl

/-- and a marker at the far end of the row cuts nothing either. -/
example : cutList [2, 3] 5 = [[2], [3]] := rfl

/-- The pieces of a straddled occurrence really are two positive slots where
the pruned source has one. -/
example : countPos ((cutList [3] 1).getD 0 []) = 2 := rfl

/-- and the cut is counted exactly as `RetainedRelabeling.cutCount_three_one_two`
counts it. -/
theorem sum_map_countPos_cutList_three_one :
    ((cutList [3] 1).map countPos).sum = countPos [3] + cutCount [3] [1, 2] := by
  rw [RetainedRelabeling.cutCount_three_one_two]
  rfl

end

end DraismaVargas.LocalCases.RetainedCut
