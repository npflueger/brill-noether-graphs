import DraismaVargas.Infrastructure.OrderedBlockSplit
import DraismaVargas.LocalCases.ClosedEndpoint
import Utilities.Subdivision.SlotRefinement

/-!
# The interface data a closed-face input refinement needs

`Candidate.ClearedFace.InputRefinement` asks for a `RefinementPresentation`
from the *scaled* stable specification `spec.scale face.scale` to the
contracted source of a terminal face.  Its statement mentions a
`Spec n p` and a face whose coordinate type `coordinate` indexes the target
occurrences, with nothing whatever tying `Fin p` to `coordinate`.  This file
supplies the missing dictionary and everything it buys.

`InputInterface` is that dictionary, and it has exactly two fields, both
forced by the consumers:

* `slot : Fin p ≃ coordinate` -- `spec.length` is indexed by `Fin p` while
  `LengthMatrixPresentation.path` and the rational coordinate vector are
  indexed by `coordinate`; `SlotRefinement.SegmentData` needs one segment list
  per `Fin p`, obtained from the path of the matching row.
* `matrixMap` -- the face's rational metric, evaluated by the length matrix,
  *is* the requested stable metric.  This is the hypothesis of
  `ClearedFace.sourcePathLength_eq_scale_mul_of_matrixMap`, the only route
  from face data to the natural number `face.scale * spec.length i`, which is
  precisely the length of slot `i` of the scaled specification.

From those two fields the file builds the `SegmentData` prescribing, for every
slot of the scaled specification, the ordered list of cleared source-occurrence
lengths along the corresponding stable path -- zero entries and all, which
`SegmentData.ofListsWithZeros` discards exactly as the face's contraction does
-- and hence the canonical positive refinement
`SlotRefinement.refineAllSlots`, its split chain, and the
`RefinementPresentation` onto its own graph.

## The expansion forest

`InputInterface` carries a fourth parameter, a slot set
`F : Finset (Fin p)` **defaulting to `∅`**, and `matrixMap` reads
`mulVec coordinates = fun row ↦ if slot.symm row ∈ F then 0 else
spec.length (slot.symm row)`.  `F` is the expansion forest of
`RequestedExpandedEndpoints`: the reduction to a cubic model presents a
non-trivalent request as a point of the closed cone of a trivalent one, with
zero length exactly on the slots the contraction collapses, so the terminal
face contracts those rows whole (`rowSegments_sum_of_mem`,
`sourceLength_eq_zero_of_mem_forest`).  A zero row prescribes no segments, so
at a nonempty forest the refinement is a refinement of the **contracted**
request, and the segment data is indexed by the retained slots: that is the
`Retained` section at the end of the file, whose `RetainedIndex` is the
interface to the zero-contraction certificate of the reduction.

Because `F` defaults to `∅`, an occurrence of
`InputInterface spec presentation coordinates` with no forest argument is the
empty forest: `InputInterface.matrixMap_empty` is the positive field
statement, `rowSegments_sum_of_not_mem` generalizes `rowSegments_sum`, and
`segmentData`, `refinedSpec`, `refinementChain`, `refinementPresentation` and
`inputRefinement` below are equal to their `Retained` counterparts at
`RetainedIndex.self` by `rfl`.

What is deliberately **not** here is the last step, a
`LaplacianEquiv (refinedSpec ..).graph (prunedSpec topology hKept).graph`
identifying that canonical refinement with the face's contracted source with
its pendant trees deleted (`PrunedContractedSpec`; see `ClosedEndpoint`).  That
is Draisma--Vargas content: it needs the row ordering of the source paths and
the trivalence of the source.  `inputRefinement` takes it as a hypothesis and
discharges everything else, so it is the only hypothesis left.
-/

namespace DraismaVargas.LocalCases.InputRefinementData

open Utilities
open Utilities.Certificate
open Utilities.Certificate.IteratedSplitRefinement
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.OrderedBlockSplit
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancedGlobal.Candidate
open DraismaVargas.LocalCases.SlotRefinement

variable {target : CFGraph} {degree : ℕ}
  {data : GluingDatum target degree} {wall : target.V}
  {candidate : Candidate target degree data wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {presentation : candidate.datum.LengthMatrixPresentation coordinate}
  {coordinates : coordinate → ℚ}
  {n p : ℕ} {spec : SubdivisionGraph.Spec n p}
  {F : Finset (Fin p)}
  {face : ClearedFace candidate presentation coordinates}

/-! ## The packed scaled input -/

/-- The packed subdivision specification that `InputRefinement` refines: the
requested stable specification with every slot length multiplied by the face's
common denominator-clearing scale.  Reducible, so that it unifies with the
anonymous packed specification written out in `InputRefinement`. -/
abbrev scaledPacked (spec : SubdivisionGraph.Spec n p)
    (face : ClearedFace candidate presentation coordinates) : PackedSpec where
  n := n
  p := p
  spec := spec.scale face.scale face.scale_pos

/-! ## The interface -/

/-- The dictionary between the abstract stable specification `spec` and the
coordinate presentation of a cleared face: a labelling of the stable slots by
matrix rows under which the face's rational metric is the stable metric,
**outside a distinguished slot set `F`**, and zero on `F`.

`F` is the *expansion forest*: the requested type is presented as a point
of the closed cone of a trivalent type, with zero length on exactly the slots
that the contraction collapses (`RequestedExpandedEndpoints`).  The forest
defaults to `∅`, which is the positive interface: an occurrence of
`InputInterface spec presentation coordinates` with no forest argument means
`F = ∅`, and `matrixMap_empty` gives the positive field statement. -/
structure InputInterface (spec : SubdivisionGraph.Spec n p)
    (presentation : candidate.datum.LengthMatrixPresentation coordinate)
    (coordinates : coordinate → ℚ)
    (F : Finset (Fin p) := ∅) where
  /-- Which matrix row displays the stable path of a given slot. -/
  slot : Fin p ≃ coordinate
  /-- The rational metric the face realizes is the requested stable metric on
  the retained slots and zero on the forest `F`. -/
  matrixMap :
    (GluingDatum.LengthMatrixPresentation.matrix presentation).mulVec coordinates =
      fun row ↦ if slot.symm row ∈ F then 0
        else ((spec.length (slot.symm row) : ℕ) : ℚ)

namespace InputInterface

/-- **The positive field statement, at `F = ∅`.**  Every consumer of the
positive interface reads `matrixMap` through this lemma. -/
theorem matrixMap_empty (iface : InputInterface spec presentation coordinates) :
    (GluingDatum.LengthMatrixPresentation.matrix presentation).mulVec coordinates =
      fun row ↦ ((spec.length (iface.slot.symm row) : ℕ) : ℚ) := by
  rw [iface.matrixMap]
  funext row
  simp

/-- Build the interface from a stable length function on rows, the shape in
which a certificate actually presents it: the requested length on the retained
slots, zero on the forest.  At `F = ∅` the second hypothesis is vacuous and the
first is the positive one. -/
def ofStableLength (slot : Fin p ≃ coordinate) (stableLength : coordinate → ℕ)
    (hMap : ∀ row,
      (GluingDatum.LengthMatrixPresentation.matrix presentation).mulVec
        coordinates row = (stableLength row : ℚ))
    (length_eq : ∀ i : Fin p, i ∉ F → stableLength (slot i) = spec.length i)
    (zero_eq : ∀ i : Fin p, i ∈ F → stableLength (slot i) = 0) :
    InputInterface spec presentation coordinates F where
  slot := slot
  matrixMap := by
    funext row
    by_cases hmem : slot.symm row ∈ F
    · have h := zero_eq _ hmem
      rw [slot.apply_symm_apply] at h
      rw [hMap row, h, if_pos hmem, Nat.cast_zero]
    · have h := length_eq _ hmem
      rw [slot.apply_symm_apply] at h
      rw [hMap row, h, if_neg hmem]

@[simp] theorem ofStableLength_slot (slot : Fin p ≃ coordinate)
    (stableLength : coordinate → ℕ)
    (hMap : ∀ row,
      (GluingDatum.LengthMatrixPresentation.matrix presentation).mulVec
        coordinates row = (stableLength row : ℚ))
    (length_eq : ∀ i : Fin p, i ∉ F → stableLength (slot i) = spec.length i)
    (zero_eq : ∀ i : Fin p, i ∈ F → stableLength (slot i) = 0) :
    (ofStableLength (spec := spec) (F := F) slot stableLength hMap length_eq
      zero_eq).slot = slot :=
  rfl

end InputInterface

/-! ## The segment data prescribed by a cleared face -/

/-- The ordered list of cleared source-occurrence lengths along the stable path
displaying slot `i`.  Entries may be zero: those are exactly the occurrences
the face contracts. -/
def rowSegments (iface : InputInterface spec presentation coordinates F)
    (face : ClearedFace candidate presentation coordinates) (i : Fin p) : List ℕ :=
  (presentation.path (iface.slot i)).map face.realization.sourceLength

/-- The source occurrences along the stable path of slot `i` sum to the scaled
length of slot `i` on a retained slot, and to zero on a forest slot.  This is
the one arithmetic fact the interface exists to provide. -/
theorem rowSegments_sum (iface : InputInterface spec presentation coordinates F)
    (face : ClearedFace candidate presentation coordinates) (i : Fin p) :
    (rowSegments iface face i).sum =
      if i ∈ F then 0 else face.scale * spec.length i := by
  have hMap :
      (GluingDatum.LengthMatrixPresentation.matrix presentation).mulVec coordinates =
        fun row ↦ (((if iface.slot.symm row ∈ F then 0
          else spec.length (iface.slot.symm row)) : ℕ) : ℚ) := by
    rw [iface.matrixMap]
    funext row
    by_cases hmem : iface.slot.symm row ∈ F <;> simp [hmem]
  have h := face.sourcePathLength_eq_scale_mul_of_matrixMap
    (fun row ↦ if iface.slot.symm row ∈ F then 0
      else spec.length (iface.slot.symm row)) hMap (iface.slot i)
  simp only [rowSegments, Equiv.symm_apply_apply] at h ⊢
  rw [h, mul_ite, Nat.mul_zero]

/-- On a retained slot the row realizes the scaled requested length on the
nose.  At `F = ∅` this is `rowSegments_sum`. -/
theorem rowSegments_sum_of_not_mem
    (iface : InputInterface spec presentation coordinates F)
    (face : ClearedFace candidate presentation coordinates) {i : Fin p}
    (hi : i ∉ F) :
    (rowSegments iface face i).sum = face.scale * spec.length i := by
  rw [rowSegments_sum iface face i, if_neg hi]

/-- On a forest slot the whole row is contracted: its total is zero. -/
theorem rowSegments_sum_of_mem
    (iface : InputInterface spec presentation coordinates F)
    (face : ClearedFace candidate presentation coordinates) {i : Fin p}
    (hi : i ∈ F) : (rowSegments iface face i).sum = 0 := by
  rw [rowSegments_sum iface face i, if_pos hi]

/-- and then every occurrence displayed by a forest row has cleared length
zero: the face contracts the whole row, occurrence by occurrence. -/
theorem sourceLength_eq_zero_of_mem_forest
    (iface : InputInterface spec presentation coordinates F)
    (face : ClearedFace candidate presentation coordinates) {i : Fin p}
    (hi : i ∈ F) :
    ∀ edge ∈ presentation.path (iface.slot i),
      face.realization.sourceLength edge = 0 := by
  intro edge hedge
  have hsum := rowSegments_sum_of_mem iface face hi
  have hmem : face.realization.sourceLength edge ∈ rowSegments iface face i :=
    List.mem_map_of_mem hedge
  have hle : face.realization.sourceLength edge ≤ (rowSegments iface face i).sum :=
    List.le_sum_of_mem hmem
  rw [hsum] at hle
  omega

/-- The segment data prescribing, for every slot of the scaled specification,
the cleared source occurrences along its stable path. -/
noncomputable def segmentData (iface : InputInterface spec presentation coordinates)
    (face : ClearedFace candidate presentation coordinates) :
    SegmentData (scaledPacked spec face) :=
  SegmentData.ofListsWithZeros _ (rowSegments iface face)
    (fun i ↦ rowSegments_sum_of_not_mem iface face (by simp))

@[simp] theorem segmentData_segments
    (iface : InputInterface spec presentation coordinates)
    (face : ClearedFace candidate presentation coordinates) (i : Fin p) :
    (segmentData iface face).segments i =
      OrderedPathSplit.positiveSegments (rowSegments iface face i) :=
  rfl

/-! ## The refinement it produces -/

/-- The canonical positive refinement of the scaled input prescribed by a
cleared face. -/
noncomputable def refinedSpec (iface : InputInterface spec presentation coordinates)
    (face : ClearedFace candidate presentation coordinates) : PackedSpec :=
  refineAllSlots (segmentData iface face)

/-- Its chain of positive canonical bivalent splits from the scaled input. -/
noncomputable def refinementChain (iface : InputInterface spec presentation coordinates)
    (face : ClearedFace candidate presentation coordinates) :
    CanonicalSplitChain (scaledPacked spec face) (refinedSpec iface face) :=
  refineAllSlotsChain _

/-- **The payoff.**  The interface data alone yields a refinement presentation
of the scaled input specification, presented on the canonical refinement's own
graph.  Only a relabeling onto the face's contracted source is left. -/
noncomputable def refinementPresentation
    (iface : InputInterface spec presentation coordinates)
    (face : ClearedFace candidate presentation coordinates) :
    RefinementPresentation (scaledPacked spec face) (refinedSpec iface face).graph :=
  refineAllSlotsPresentation _

/-- The refinement has one slot per *positive* cleared source occurrence. -/
theorem refinedSpec_p (iface : InputInterface spec presentation coordinates)
    (face : ClearedFace candidate presentation coordinates) :
    (refinedSpec iface face).p =
      ∑ i : Fin p,
        (OrderedPathSplit.positiveSegments (rowSegments iface face i)).length :=
  refineAllSlots_p _

/-- Each of those slots carries one new bivalent core vertex. -/
theorem refinedSpec_n (iface : InputInterface spec presentation coordinates)
    (face : ClearedFace candidate presentation coordinates) :
    (refinedSpec iface face).n + p =
      n + ∑ i : Fin p,
        (OrderedPathSplit.positiveSegments (rowSegments iface face i)).length :=
  refineAllSlots_n _

/-- The refinement is metric: its total edge length is the face's scale times
the total stable length. -/
theorem refinedSpec_total_length (iface : InputInterface spec presentation coordinates)
    (face : ClearedFace candidate presentation coordinates) :
    ∑ j : Fin (refinedSpec iface face).p, (refinedSpec iface face).spec.length j =
      face.scale * ∑ i : Fin p, spec.length i :=
  (refineAllSlots_total_length _).trans (Finset.mul_sum _ _ _).symm

/-- Counting the positive entries of a mapped list. -/
theorem length_positiveSegments_map {α : Type*} (f : α → ℕ) (l : List α) :
    (OrderedPathSplit.positiveSegments (l.map f)).length =
      l.countP fun a ↦ decide (0 < f a) := by
  unfold OrderedPathSplit.positiveSegments
  rw [List.countP_eq_length_filter]
  induction l with
  | nil => rfl
  | cons a rest ih => by_cases h : 0 < f a <;> simp [h, ih]

/-- The slot count of the refinement, read off the face: the number of source
occurrences along the displayed stable paths that the face does *not*
contract. -/
theorem refinedSpec_p_eq_countP (iface : InputInterface spec presentation coordinates)
    (face : ClearedFace candidate presentation coordinates) :
    (refinedSpec iface face).p =
      ∑ i : Fin p, (presentation.path (iface.slot i)).countP
        fun edge ↦ decide (0 < face.realization.sourceLength edge) := by
  rw [refinedSpec_p]
  exact Finset.sum_congr rfl fun i _ ↦
    length_positiveSegments_map face.realization.sourceLength
      (presentation.path (iface.slot i))

/-- The same count, read off the face's *rational* data: a source occurrence
survives the contraction exactly when the target coordinate above it is
nonzero, so the refined slot count is determined by `coordinates` alone. -/
theorem refinedSpec_p_eq_countP_coordinates
    (iface : InputInterface spec presentation coordinates)
    (face : ClearedFace candidate presentation coordinates) :
    (refinedSpec iface face).p =
      ∑ i : Fin p, (presentation.path (iface.slot i)).countP
        fun edge ↦ decide (coordinates (presentation.targetEdge.symm edge.1.1) ≠ 0) := by
  rw [refinedSpec_p_eq_countP]
  refine Finset.sum_congr rfl fun i _ ↦ List.countP_congr fun edge _ ↦ ?_
  have hzero := face.sourceLength_eq_zero_iff edge
  have hpos : 0 < face.realization.sourceLength edge ↔
      face.realization.sourceLength edge ≠ 0 := by omega
  simp only [decide_eq_true_eq, hpos, ne_eq, hzero]

/-! ## The input refinement, up to the final identification -/

/-- The closed-face input refinement, assuming only the final
identification of the canonical positive refinement with the face's pruned
contracted source.  Everything else -- the segment data, its positivity, the
sums, the whole split chain -- is supplied by the interface. -/
noncomputable def inputRefinement
    (iface : InputInterface spec presentation coordinates)
    {topology : ClearedFace.SourceContractionTopology face}
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (relabeling : LaplacianEquiv (refinedSpec iface face).graph
      (ClearedFace.SourceContractionTopology.prunedSpec topology hKept).graph) :
    ClearedFace.InputRefinement spec topology where
  kept := hKept
  refinement := refineAllSlotsPresentationOf (segmentData iface face) relabeling


/-! ## The general forest: the refinement lives on the retained slots

When the forest `F` is nonempty its rows are contracted
whole (`sourceLength_eq_zero_of_mem_forest`), so they prescribe no segments at all and
the refinement is a refinement of the **contracted** request, not of `spec`:
`spec` has positive length on every slot (`Spec.length_pos`), so `spec.scale`
is not what such a face realizes.  Which subdivision specification the retained
slots assemble into is given by the zero-contraction certificate of the
reduction to a cubic model, and is deliberately **not** built here.
`RetainedIndex` is the interface to it: a specification `small` whose slots are
distributed, in series and in order, over the retained slots of `spec`, with
the lengths adding up.

At `F = ∅` the specification indexes its own retained slots one for one
(`RetainedIndex.self`) and every declaration below agrees on the nose with its
positive counterpart (`blockSegments_self`, `segmentData_self`,
`refinedSpec_self`).

**Why an ordered carrier list.**  An equivalence
`Fin p' ≃ {i : Fin p // i ∉ F}`, one retained slot per requested slot, is
available exactly when the expansion datum has no
`CoreExpansion.SlotKind.double` slot, i.e. when the requested core has no
marker; a `double` carries **two** requested slots in series through the marker
by which a loop of the metric graph is displayed looplessly, so `owner` is then
two-to-one and the counting fails
(`RetainedIndexProducer.markerFree_of_equiv`).  `RetainedIndex` therefore
records the ordered carrier list `carried`, and the produced refinement cuts
each retained row at the prescribed metric positions
(`Infrastructure.OrderedBlockSplit`).  Cutting one occurrence in two is
invisible: `Spec.graph` is the unit subdivision, so an extra core vertex at an
interior integer point does not change the graph, and the `LaplacianEquiv`
hypothesis of `inputRefinement` has the same form as at the empty forest. -/

section Retained

/-- A presentation of the retained slots of `spec` — those outside the forest
`F` — by a subdivision specification `small` in its own right: every retained
slot of `spec` carries an **ordered list** of slots of `small`, in series, and
those lists partition the slots of `small`.

This is the slot half of
`Utilities.Certificate.DegenerateSpec.DegSpec.Contraction`, widened to allow a
retained slot to carry more than one requested slot: `owner` is that structure's
`slot` read backwards, `owner_eq_of_mem` together with `carried_getElem` is its
`slot_inj`/`slot_surj` pair, and `length_eq` is its `length_eq` summed along a
block.  Building one from the certificate of the reduction to a cubic model is
`DraismaVargas.LocalCases.RetainedIndexProducer.retainedIndex`.

`owner` and `pos` are fields rather than functions recovered from `carried`
precisely so that `RetainedIndex.self` below makes the whole `Retained` API
reduce to the positive one by `rfl`. -/
structure RetainedIndex (spec : SubdivisionGraph.Spec n p) (F : Finset (Fin p))
    {n' p' : ℕ} (small : SubdivisionGraph.Spec n' p') where
  /-- The slots of `small` that a retained slot of `spec` carries, in series
  order along it. -/
  carried : {i : Fin p // i ∉ F} → List (Fin p')
  /-- Which retained slot carries a given slot of `small`. -/
  owner : Fin p' → {i : Fin p // i ∉ F}
  /-- Where along its owner it sits. -/
  pos : Fin p' → ℕ
  /-- `owner` and `pos` really locate it. -/
  carried_getElem : ∀ j : Fin p', (carried (owner j))[pos j]? = some j
  /-- No other retained slot carries it: the lists partition the slots of
  `small`. -/
  owner_eq_of_mem : ∀ (e : {i : Fin p // i ∉ F}) (j : Fin p'),
    j ∈ carried e → owner j = e
  /-- and no list repeats one. -/
  nodup : ∀ e : {i : Fin p // i ∉ F}, (carried e).Nodup
  /-- No retained slot is idle. -/
  carried_ne_nil : ∀ e : {i : Fin p // i ∉ F}, carried e ≠ []
  /-- The lengths add up in series along each retained slot. -/
  length_eq : ∀ e : {i : Fin p // i ∉ F},
    spec.length ↑e = ((carried e).map small.length).sum

namespace RetainedIndex

variable {n' p' : ℕ} {small : SubdivisionGraph.Spec n' p'}

theorem mem_carried_owner (idx : RetainedIndex spec F small) (j : Fin p') :
    j ∈ idx.carried (idx.owner j) :=
  List.mem_of_getElem? (idx.carried_getElem j)

theorem pos_lt (idx : RetainedIndex spec F small) (j : Fin p') :
    idx.pos j < (idx.carried (idx.owner j)).length := by
  by_contra h
  have hget := idx.carried_getElem j
  rw [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hget
  exact absurd hget (by simp)

end RetainedIndex

/-- At an empty forest a specification indexes its own retained slots, each
retained slot carrying exactly itself. -/
def RetainedIndex.self (spec : SubdivisionGraph.Spec n p) :
    RetainedIndex spec ∅ spec where
  carried := fun e ↦ [(e : Fin p)]
  owner := fun j ↦ ⟨j, by simp⟩
  pos := fun _ ↦ 0
  carried_getElem := fun _ ↦ rfl
  owner_eq_of_mem := by
    rintro ⟨i, hi⟩ j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    exact Subtype.ext hj
  nodup := fun _ ↦ List.nodup_singleton _
  carried_ne_nil := fun _ ↦ List.cons_ne_nil _ _
  length_eq := fun _ ↦ by simp

namespace Retained

variable {n' p' : ℕ} {small : SubdivisionGraph.Spec n' p'}

/-- The prescribed totals along a retained row: the scaled lengths of the slots
it carries, in series order. -/
def blockTotals (face : ClearedFace candidate presentation coordinates)
    (idx : RetainedIndex spec F small) (e : {i : Fin p // i ∉ F}) : List ℕ :=
  (idx.carried e).map fun k ↦ face.scale * small.length k

theorem sum_map_mul_left {α : Type*} (c : ℕ) (f : α → ℕ) (l : List α) :
    (l.map fun a ↦ c * f a).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a rest ih => simp [ih, Nat.mul_add]

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem sum_blockTotals (face : ClearedFace candidate presentation coordinates)
    (idx : RetainedIndex spec F small) (e : {i : Fin p // i ∉ F}) :
    (blockTotals face idx e).sum = face.scale * spec.length ↑e := by
  rw [blockTotals, sum_map_mul_left, ← idx.length_eq e]

omit [Fintype coordinate] [DecidableEq coordinate] in
@[simp] theorem length_blockTotals
    (face : ClearedFace candidate presentation coordinates)
    (idx : RetainedIndex spec F small) (e : {i : Fin p // i ∉ F}) :
    (blockTotals face idx e).length = (idx.carried e).length := by
  rw [blockTotals, List.length_map]

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem getD_blockTotals (face : ClearedFace candidate presentation coordinates)
    (idx : RetainedIndex spec F small) (j : Fin p') :
    (blockTotals face idx (idx.owner j)).getD (idx.pos j) 0 =
      face.scale * small.length j := by
  rw [blockTotals, List.getD_eq_getElem?_getD, List.getElem?_map,
    idx.carried_getElem j]
  rfl

/-- The cleared source occurrences allotted to the slot `j` of `small`: the
`pos j`-th block of its owner's displayed row, cut at the prescribed metric
positions.  At most one occurrence per marker is cut in two, which the unit
subdivision does not see. -/
def blockSegments (iface : InputInterface spec presentation coordinates F)
    (face : ClearedFace candidate presentation coordinates)
    (idx : RetainedIndex spec F small) (j : Fin p') : List ℕ :=
  (OrderedBlockSplit.blocks (rowSegments iface face ↑(idx.owner j))
    (blockTotals face idx (idx.owner j))).getD (idx.pos j) []

/-- **The one arithmetic fact the retained interface exists to provide.**  Each
block realizes the scaled length of the slot it is allotted to. -/
theorem sum_blockSegments (iface : InputInterface spec presentation coordinates F)
    (face : ClearedFace candidate presentation coordinates)
    (idx : RetainedIndex spec F small) (j : Fin p') :
    (blockSegments iface face idx j).sum = face.scale * small.length j := by
  have hsum : (blockTotals face idx (idx.owner j)).sum
      = (rowSegments iface face ↑(idx.owner j)).sum := by
    rw [sum_blockTotals face idx (idx.owner j),
      rowSegments_sum_of_not_mem iface face (idx.owner j).2]
  have hk : idx.pos j < (blockTotals face idx (idx.owner j)).length := by
    rw [length_blockTotals]
    exact idx.pos_lt j
  rw [blockSegments,
    OrderedBlockSplit.sum_getD_blocks _ _ hsum (idx.pos j) hk,
    getD_blockTotals]

/-- At the empty forest a slot's block is its own whole row. -/
theorem blockSegments_self
    (iface : InputInterface spec presentation coordinates)
    (face : ClearedFace candidate presentation coordinates) (j : Fin p) :
    blockSegments iface face (RetainedIndex.self spec) j = rowSegments iface face j :=
  rfl

/-- The segment data prescribing, for every slot of `small`, the cleared
source occurrences allotted to it.  The forest rows contribute nothing. -/
noncomputable def segmentData
    (iface : InputInterface spec presentation coordinates F)
    (face : ClearedFace candidate presentation coordinates)
    (idx : RetainedIndex spec F small) :
    SegmentData (scaledPacked small face) :=
  SegmentData.ofListsWithZeros _ (blockSegments iface face idx)
    (fun j ↦ sum_blockSegments iface face idx j)

@[simp] theorem segmentData_segments
    (iface : InputInterface spec presentation coordinates F)
    (face : ClearedFace candidate presentation coordinates)
    (idx : RetainedIndex spec F small) (j : Fin p') :
    (segmentData iface face idx).segments j =
      OrderedPathSplit.positiveSegments (blockSegments iface face idx j) :=
  rfl

/-- The canonical positive refinement of the scaled retained input. -/
noncomputable def refinedSpec
    (iface : InputInterface spec presentation coordinates F)
    (face : ClearedFace candidate presentation coordinates)
    (idx : RetainedIndex spec F small) : PackedSpec :=
  refineAllSlots (segmentData iface face idx)

/-- Its chain of positive canonical bivalent splits from the scaled retained
input. -/
noncomputable def refinementChain
    (iface : InputInterface spec presentation coordinates F)
    (face : ClearedFace candidate presentation coordinates)
    (idx : RetainedIndex spec F small) :
    CanonicalSplitChain (scaledPacked small face) (refinedSpec iface face idx) :=
  refineAllSlotsChain _

/-- **The payoff at a general forest.**  The interface data and the retained
indexing yield a refinement presentation of the scaled *contracted* input. -/
noncomputable def refinementPresentation
    (iface : InputInterface spec presentation coordinates F)
    (face : ClearedFace candidate presentation coordinates)
    (idx : RetainedIndex spec F small) :
    RefinementPresentation (scaledPacked small face) (refinedSpec iface face idx).graph :=
  refineAllSlotsPresentation _

/-- The refinement has one slot per positive cleared source occurrence allotted
to a slot of `small`. -/
theorem refinedSpec_p
    (iface : InputInterface spec presentation coordinates F)
    (face : ClearedFace candidate presentation coordinates)
    (idx : RetainedIndex spec F small) :
    (refinedSpec iface face idx).p =
      ∑ j : Fin p',
        (OrderedPathSplit.positiveSegments
          (blockSegments iface face idx j)).length :=
  refineAllSlots_p _

/-- Each of those slots carries one new bivalent core vertex. -/
theorem refinedSpec_n
    (iface : InputInterface spec presentation coordinates F)
    (face : ClearedFace candidate presentation coordinates)
    (idx : RetainedIndex spec F small) :
    (refinedSpec iface face idx).n + p' =
      n' + ∑ j : Fin p',
        (OrderedPathSplit.positiveSegments
          (blockSegments iface face idx j)).length :=
  refineAllSlots_n _

/-- The refinement is metric for the contracted request: its total edge length
is the face's scale times the retained total length. -/
theorem refinedSpec_total_length
    (iface : InputInterface spec presentation coordinates F)
    (face : ClearedFace candidate presentation coordinates)
    (idx : RetainedIndex spec F small) :
    ∑ k : Fin (refinedSpec iface face idx).p,
        (refinedSpec iface face idx).spec.length k =
      face.scale * ∑ j : Fin p', small.length j :=
  (refineAllSlots_total_length _).trans (Finset.mul_sum _ _ _).symm

/-- The closed-face input refinement **for the contracted request**,
assuming only the final identification of the canonical positive refinement
with the face's pruned contracted source. -/
noncomputable def inputRefinement
    (iface : InputInterface spec presentation coordinates F)
    (idx : RetainedIndex spec F small)
    {topology : ClearedFace.SourceContractionTopology face}
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (relabeling : LaplacianEquiv (refinedSpec iface face idx).graph
      (ClearedFace.SourceContractionTopology.prunedSpec topology hKept).graph) :
    ClearedFace.InputRefinement small topology where
  kept := hKept
  refinement :=
    refineAllSlotsPresentationOf (segmentData iface face idx) relabeling

end Retained

/-! ### `F = ∅` recovers the positive declarations on the nose -/

theorem segmentData_self
    (iface : InputInterface spec presentation coordinates)
    (face : ClearedFace candidate presentation coordinates) :
    Retained.segmentData iface face (RetainedIndex.self spec) =
      segmentData iface face :=
  rfl

theorem refinedSpec_self
    (iface : InputInterface spec presentation coordinates)
    (face : ClearedFace candidate presentation coordinates) :
    Retained.refinedSpec iface face (RetainedIndex.self spec) =
      refinedSpec iface face :=
  rfl

theorem inputRefinement_self
    (iface : InputInterface spec presentation coordinates)
    {topology : ClearedFace.SourceContractionTopology face}
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (relabeling : LaplacianEquiv (refinedSpec iface face).graph
      (ClearedFace.SourceContractionTopology.prunedSpec topology hKept).graph) :
    Retained.inputRefinement iface (RetainedIndex.self spec) hKept relabeling =
      inputRefinement iface hKept relabeling :=
  rfl

end Retained

end DraismaVargas.LocalCases.InputRefinementData
