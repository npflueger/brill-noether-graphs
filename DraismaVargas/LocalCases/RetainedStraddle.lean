module

public import DraismaVargas.LocalCases.RetainedRowPieces

@[expose] public section

/-!
# Where the marker sits along a retained row

**Source.**  None: the marker cut appears in neither Draisma--Vargas Part I nor
Vargas, Part II.  It is needed because a retained row can carry two requested
slots in series through a marker, and this file is the arithmetic of that
situation.

## What is proved

`DraismaVargas.LocalCases.RetainedRowPieces` indexes one and the same ordered
list of positive pieces along a retained row from two sides: from the requested
slots the row carries (`retPos`) and from the kept slots it displays
(`piecePos`).  Nothing there says how the two groupings *interleave*.  This
file settles the one interleaving fact the vertex half of the retained
relabeling needs.

* §1 names the two groupings as lists of blocks, `rowBlocks` and `cutBlocks`,
  with `retPos` and `piecePos` read off `FlattenIndex.offset` of each.

* §2 computes each block's total: the retained blocks sum to
  `Retained.blockTotals` (so the first block total is the marker's metric
  position `RetainedCut.cutOffsetAt`), and the cut blocks sum to the cleared
  occurrence lengths `RetainedCut.positiveLengths`.

* §3 turns those into prefix sums along the row, through
  `FlattenIndex.sum_take_flatten`, and notes that every piece along a retained
  row is positive.

* §4 is the theorem.  `Straddles` is the `if` of
  `RetainedCut.positiveSegments_pieces` -- the marker falls strictly inside the
  occurrence carrying a kept slot -- and `piecePos_succ_eq_offset_one` says
  **the straddle point is the first block boundary of the retained
  refinement**: both are the place at which the running total of the pieces
  first reaches `cutOffsetAt`, and the running totals are strictly increasing
  because every piece is positive (`FlattenIndex.take_sum_inj`).
  `eq_of_straddles`: at most one kept slot of a row is straddled.

* §5 is what the vertex half consumes.  `retPos_ne_piecePos_zero`: **no
  breakpoint of the retained refinement falls strictly inside a straddled kept
  slot**, so every such breakpoint is an occurrence boundary and therefore a
  contraction class; and `piecePos_one_eq_retPos_zero`: the second piece of the
  straddled kept slot is the first piece of the second requested slot, so the
  **marker** is the one refined core vertex that lands on a new split vertex of
  `RetainedCut.cutSpec`.  That is exactly the case split the vertex map needs
  at a marker.

## The hypotheses that remain explicit

1. **`hTwo : RetainedCut.CarriesAtMostTwo idx`** -- at most one marker per
   retained row.  §4 and §5 both use it: `rowPieces_eq_cut` needs it, and §5's
   case split is `pos j ∈ {0, 1}`.  `RetainedCut.carried_length_le_two`
   discharges it at the expansion model.
2. **No vertex map.**  Nothing here mentions contraction classes, the oriented
   walk, or `RetainedFibre`'s markers: this is the combinatorics of the row
   alone.  Which class a breakpoint lands in is
   `RetainedTraversal.classOf_rowWalk_eq_of_zero_run`, and which requested core
   vertex is a marker is `RetainedFibre.isMarker_or_exists_fib`.
3. **Nothing about an aligned marker.**  When `Straddles` fails at every kept
   slot of the row the marker sits at an occurrence boundary and no kept slot
   is cut; §4 and §5 say nothing about that case, which the vertex half must
   treat separately (see `RetainedFibre`).

## Used by

The vertex half of the retained relabeling, above
`DraismaVargas.LocalCases.RetainedCoreModel`.
-/

namespace DraismaVargas.LocalCases.RetainedStraddle

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
open DraismaVargas.LocalCases.RetainedRelabeling
open DraismaVargas.LocalCases.RetainedRowPieces
open DraismaVargas.LocalCases.SlotRefinement
open DraismaVargas.LocalCases.TraversalPresentation

variable {target : CFGraph} {degree : ℕ}
  {gluing : GluingDatum target degree} {wall : target.V}
  {candidate : Candidate target degree gluing wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {coordinates : coordinate → ℚ}
  {n p : ℕ} {spec : SubdivisionGraph.Spec n p} {F : Finset (Fin p)}
  {strong : StrongPresentation candidate.datum coordinate}
  {face : ClearedFace candidate strong.toPresentation coordinates}
  {n' p' : ℕ} {small : SubdivisionGraph.Spec n' p'}
  {iface : InputInterface spec strong.toPresentation coordinates F}

/-! ## 1.  The two groupings of a retained row, as blocks -/

/-- The retained refinement's grouping of a retained row: one block per
requested slot the row carries. -/
def rowBlocks (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small) (e : {i : Fin p // i ∉ F}) : List (List ℕ) :=
  (idx.carried e).map fun j ↦ (Retained.segmentData iface face idx).segments j

/-- The marker cut's grouping of the same row: one block per kept slot. -/
def cutBlocks (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small) (i : Fin p) : List (List ℕ) :=
  (cutList (positiveLengths iface face i) (cutOffsetAt face idx i)).map
    OrderedPathSplit.positiveSegments

theorem rowPieces_eq_flatten_rowBlocks (idx : RetainedIndex spec F small)
    (e : {i : Fin p // i ∉ F}) :
    rowPieces iface face idx e = (rowBlocks iface face idx e).flatten := rfl

theorem rowPieces_eq_flatten_cutBlocks (idx : RetainedIndex spec F small)
    (hTwo : CarriesAtMostTwo idx) (e : {i : Fin p // i ∉ F}) :
    rowPieces iface face idx e = (cutBlocks iface face idx ↑e).flatten :=
  rowPieces_eq_cut iface face idx hTwo e

/-- the same, at the row displaying a kept slot. -/
theorem rowPieces_slotRow_eq_flatten_cutBlocks (idx : RetainedIndex spec F small)
    (hTwo : CarriesAtMostTwo idx) (x : SlotIndex iface face) :
    rowPieces iface face idx (slotRow x) = (cutBlocks iface face idx x.1).flatten :=
  rowPieces_eq_cut iface face idx hTwo (slotRow x)

theorem retPos_eq (idx : RetainedIndex spec F small) (j : Fin p') (m : ℕ) :
    retPos iface face idx j m =
      offset (rowBlocks iface face idx (idx.owner j)) (idx.pos j) + m := rfl

theorem piecePos_eq (idx : RetainedIndex spec F small) (x : SlotIndex iface face) (t : ℕ) :
    piecePos iface face idx x t = offset (cutBlocks iface face idx x.1) (x.2 : ℕ) + t := rfl

/-! ## 2.  Each block sums to what it should -/

/-- **The retained blocks sum to the prescribed block totals.** -/
theorem map_sum_rowBlocks (idx : RetainedIndex spec F small) (e : {i : Fin p // i ∉ F}) :
    (rowBlocks iface face idx e).map List.sum = Retained.blockTotals face idx e := by
  rw [rowBlocks, List.map_map, Retained.blockTotals]
  refine List.map_congr_left fun j _ ↦ ?_
  show (OrderedPathSplit.positiveSegments (Retained.blockSegments iface face idx j)).sum = _
  rw [OrderedPathSplit.sum_positiveSegments, Retained.sum_blockSegments]

/-- **Each entry of a cut recovers its occurrence.** -/
theorem map_sum_cutList (l : List ℕ) (a : ℕ) : (cutList l a).map List.sum = l := by
  refine List.ext_getElem (by rw [List.length_map, length_cutList]) fun k h1 h2 ↦ ?_
  have h := sum_getD_cutList l a k
  rw [List.getD_eq_getElem _ _ (by simpa using h1), List.getD_eq_getElem _ _ h2] at h
  rw [List.getElem_map]
  exact h

/-- **The cut blocks sum to the cleared occurrence lengths.** -/
theorem map_sum_cutBlocks (idx : RetainedIndex spec F small) (i : Fin p) :
    (cutBlocks iface face idx i).map List.sum = positiveLengths iface face i := by
  rw [cutBlocks, List.map_map,
    show (List.sum ∘ OrderedPathSplit.positiveSegments) = List.sum from
      funext fun l ↦ OrderedPathSplit.sum_positiveSegments l]
  exact map_sum_cutList _ _

/-! ## 3.  Prefix sums along a retained row -/

theorem sum_take_one (l : List ℕ) : (l.take 1).sum = l.headD 0 := by
  cases l with
  | nil => rfl
  | cons a rest => simp

/-- **Every piece along a retained row is positive.** -/
theorem pos_of_mem_rowPieces (idx : RetainedIndex spec F small) {e : {i : Fin p // i ∉ F}}
    {v : ℕ} (hv : v ∈ rowPieces iface face idx e) : 0 < v := by
  rw [rowPieces_eq_flatten_rowBlocks] at hv
  obtain ⟨B, hB, hvB⟩ := List.mem_flatten.mp hv
  rw [rowBlocks, List.mem_map] at hB
  obtain ⟨j, -, rfl⟩ := hB
  exact OrderedPathSplit.positiveSegments_all_pos _ v hvB

/-- **A prefix sum at a boundary of the retained grouping.** -/
theorem sum_take_rowPieces_offset (idx : RetainedIndex spec F small)
    (e : {i : Fin p // i ∉ F}) (k : ℕ) :
    ((rowPieces iface face idx e).take (offset (rowBlocks iface face idx e) k)).sum =
      ((Retained.blockTotals face idx e).take k).sum := by
  rw [rowPieces_eq_flatten_rowBlocks, sum_take_flatten_offset, List.map_take,
    map_sum_rowBlocks]

/-- **and one inside a block of the marker cut.** -/
theorem sum_take_rowPieces_piecePos (idx : RetainedIndex spec F small)
    (hTwo : CarriesAtMostTwo idx) (x : SlotIndex iface face) {q : ℕ}
    (hq : q ≤ (OrderedPathSplit.positiveSegments (pieces iface face idx x)).length) :
    ((rowPieces iface face idx (slotRow x)).take (piecePos iface face idx x q)).sum =
      ((positiveLengths iface face x.1).take (x.2 : ℕ)).sum +
        ((OrderedPathSplit.positiveSegments (pieces iface face idx x)).take q).sum := by
  have hblock : (cutBlocks iface face idx x.1).getD (x.2 : ℕ) [] =
      OrderedPathSplit.positiveSegments (pieces iface face idx x) := by
    rw [cutBlocks, getD_map_of_lt _ _ (slotIndex_lt_cutList idx x), getElem_cutList]
  rw [piecePos_eq, rowPieces_slotRow_eq_flatten_cutBlocks idx hTwo x,
    sum_take_flatten _ _ _ (by rw [hblock]; exact hq), List.map_take, map_sum_cutBlocks,
    hblock]

/-! ## 4.  The marker's straddle point is a block boundary -/

/-- **The marker falls strictly inside the occurrence carrying the kept slot
`x`.**  This is the `if` of `RetainedCut.positiveSegments_pieces`. -/
abbrev Straddles (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small) (x : SlotIndex iface face) : Prop :=
  ((positiveLengths iface face x.1).take (x.2 : ℕ)).sum < cutOffsetAt face idx x.1 ∧
    cutOffsetAt face idx x.1 <
      ((positiveLengths iface face x.1).take (x.2 : ℕ)).sum +
        face.realization.sourceLength (occurrence x)

theorem positiveSegments_pieces_of_straddles (idx : RetainedIndex spec F small)
    {x : SlotIndex iface face} (h : Straddles iface face idx x) :
    OrderedPathSplit.positiveSegments (pieces iface face idx x) =
      [cutOffsetAt face idx x.1 - ((positiveLengths iface face x.1).take (x.2 : ℕ)).sum,
        ((positiveLengths iface face x.1).take (x.2 : ℕ)).sum +
          face.realization.sourceLength (occurrence x) - cutOffsetAt face idx x.1] := by
  rw [positiveSegments_pieces idx x, ite_eq_left h]

/-- A straddled kept slot has exactly two pieces. -/
theorem length_positiveSegments_pieces_of_straddles (idx : RetainedIndex spec F small)
    {x : SlotIndex iface face} (h : Straddles iface face idx x) :
    (OrderedPathSplit.positiveSegments (pieces iface face idx x)).length = 2 := by
  rw [positiveSegments_pieces_of_straddles idx h]
  rfl

/-- and the first of them runs up to the marker. -/
theorem sum_take_one_positiveSegments_pieces (idx : RetainedIndex spec F small)
    {x : SlotIndex iface face} (h : Straddles iface face idx x) :
    ((OrderedPathSplit.positiveSegments (pieces iface face idx x)).take 1).sum =
      cutOffsetAt face idx x.1 - ((positiveLengths iface face x.1).take (x.2 : ℕ)).sum := by
  rw [positiveSegments_pieces_of_straddles idx h]
  simp

/-- **The row reaches the marker just after the first piece of the straddled
kept slot.** -/
theorem sum_take_rowPieces_straddle (idx : RetainedIndex spec F small)
    (hTwo : CarriesAtMostTwo idx) {x : SlotIndex iface face}
    (h : Straddles iface face idx x) :
    ((rowPieces iface face idx (slotRow x)).take
        (piecePos iface face idx x 0 + 1)).sum = cutOffsetAt face idx x.1 := by
  have hlen := length_positiveSegments_pieces_of_straddles idx h
  have hpiece : piecePos iface face idx x 0 + 1 = piecePos iface face idx x 1 := by
    rw [piecePos_eq, piecePos_eq]
  rw [hpiece, sum_take_rowPieces_piecePos idx hTwo x (by omega),
    sum_take_one_positiveSegments_pieces idx h]
  have := h.1
  omega

/-- **and it reaches the marker exactly at the first block boundary.** -/
theorem sum_take_rowPieces_offset_one (idx : RetainedIndex spec F small)
    (e : {i : Fin p // i ∉ F}) :
    ((rowPieces iface face idx e).take (offset (rowBlocks iface face idx e) 1)).sum =
      cutOffsetAt face idx ↑e := by
  rw [sum_take_rowPieces_offset idx e 1, sum_take_one, cutOffsetAt_coe]

/-- **The straddle point of the marker cut is the first block boundary of the
retained refinement.**

Both are the place along the row at which the running total of the pieces first
reaches the marker's metric position `cutOffsetAt`: for the cut because the
first piece of a straddled kept slot ends there, for the retained refinement
because the first block is the first requested slot the row carries, whose
prescribed total is exactly `cutOffsetAt`.  Every piece along a retained row is
positive, so the running totals are strictly increasing and the two places
coincide. -/
theorem piecePos_succ_eq_offset_one (idx : RetainedIndex spec F small)
    (hTwo : CarriesAtMostTwo idx) {x : SlotIndex iface face}
    (h : Straddles iface face idx x) :
    piecePos iface face idx x 0 + 1 = offset (rowBlocks iface face idx (slotRow x)) 1 := by
  have hlen := length_positiveSegments_pieces_of_straddles idx h
  have hpiece : piecePos iface face idx x 1 = piecePos iface face idx x 0 + 1 := by
    rw [piecePos_eq, piecePos_eq]
  have hb1 : piecePos iface face idx x 0 + 1 ≤
      (rowPieces iface face idx (slotRow x)).length := by
    have hlt := piecePos_lt idx hTwo x (t := 1) (by omega)
    omega
  have hb2 : offset (rowBlocks iface face idx (slotRow x)) 1 ≤
      (rowPieces iface face idx (slotRow x)).length := by
    have hlen1 : 1 ≤ (rowBlocks iface face idx (slotRow x)).length := by
      rw [rowBlocks, List.length_map]
      exact List.length_pos_of_ne_nil (idx.carried_ne_nil _)
    have hmono := offset_mono (rowBlocks iface face idx (slotRow x)) hlen1
    rw [offset_length] at hmono
    rw [rowPieces_eq_flatten_rowBlocks]
    exact hmono
  refine take_sum_inj (fun v hv ↦ pos_of_mem_rowPieces idx hv) hb1 hb2 ?_
  rw [sum_take_rowPieces_straddle idx hTwo h, sum_take_rowPieces_offset_one idx (slotRow x)]
  rfl

/-- **At most one kept slot of a row is straddled.** -/
theorem eq_of_straddles (idx : RetainedIndex spec F small) (hTwo : CarriesAtMostTwo idx)
    {x x' : SlotIndex iface face} (h : Straddles iface face idx x)
    (h' : Straddles iface face idx x') (hrow : x.1 = x'.1) : x = x' := by
  have hlen := length_positiveSegments_pieces_of_straddles idx h
  have hlen' := length_positiveSegments_pieces_of_straddles idx h'
  have hk := piecePos_succ_eq_offset_one idx hTwo h
  have hk' := piecePos_succ_eq_offset_one idx hTwo h'
  have hslot : slotRow x = slotRow x' := Subtype.ext hrow
  rw [hslot] at hk
  exact (piecePos_inj idx hrow (t := 0) (t' := 0) (by omega) (by omega) (by omega)).1

/-! ## 5.  A breakpoint of the retained refinement is a kept-slot boundary -/

theorem offset_rowBlocks_one (idx : RetainedIndex spec F small) {j : Fin p'}
    (h0 : idx.pos j = 0) :
    offset (rowBlocks iface face idx (idx.owner j)) 1 =
      ((Retained.segmentData iface face idx).segments j).length := by
  have hget : (idx.carried (idx.owner j))[0]? = some j := by
    rw [← h0]
    exact idx.carried_getElem j
  have hblock : (rowBlocks iface face idx (idx.owner j)).getD 0 [] =
      (Retained.segmentData iface face idx).segments j := by
    rw [rowBlocks, List.getD_eq_getElem?_getD, List.getElem?_map, hget]
    rfl
  rw [offset_succ, offset_zero, hblock, Nat.zero_add]

/-- **No breakpoint of the retained refinement falls strictly inside a
straddled kept slot.**

A breakpoint of the requested slot `j` separates two consecutive pieces of the
block of `j`; the straddle point is the boundary *between* the two blocks
(`piecePos_succ_eq_offset_one`), and `CarriesAtMostTwo` leaves only the two
cases `pos j = 0` and `pos j = 1`, each of which contradicts that.  This is
what makes every breakpoint of the retained refinement an occurrence boundary,
hence a contraction class, and the marker the only refined vertex that can land
on a new split vertex of `RetainedCut.cutSpec`. -/
theorem retPos_ne_piecePos_zero (idx : RetainedIndex spec F small)
    (hTwo : CarriesAtMostTwo idx) {x : SlotIndex iface face}
    (h : Straddles iface face idx x) {j : Fin p'} (hj : idx.owner j = slotRow x) {m : ℕ}
    (hm : m + 1 < ((Retained.segmentData iface face idx).segments j).length) :
    retPos iface face idx j m ≠ piecePos iface face idx x 0 := by
  intro hEq
  have hkey := piecePos_succ_eq_offset_one idx hTwo h
  have hpos2 : idx.pos j < 2 := lt_of_lt_of_le (idx.pos_lt j) (hTwo (idx.owner j))
  rw [retPos_eq, hj] at hEq
  rcases (show idx.pos j = 0 ∨ idx.pos j = 1 by omega) with h0 | h1
  · have hone := offset_rowBlocks_one (iface := iface) (face := face) idx h0
    rw [hj] at hone
    rw [h0, offset_zero, Nat.zero_add] at hEq
    omega
  · rw [h1] at hEq
    omega

/-- **The second piece of a straddled kept slot is the first piece of the
second requested slot the row carries.**  This is the other half of
`piecePos_succ_eq_offset_one`: the marker is where the row hands over. -/
theorem piecePos_one_eq_retPos_zero (idx : RetainedIndex spec F small)
    (hTwo : CarriesAtMostTwo idx) {x : SlotIndex iface face}
    (h : Straddles iface face idx x) {j : Fin p'} (hj : idx.owner j = slotRow x)
    (hpos : idx.pos j = 1) :
    piecePos iface face idx x 1 = retPos iface face idx j 0 := by
  have hkey := piecePos_succ_eq_offset_one idx hTwo h
  have h1 : piecePos iface face idx x 1 = piecePos iface face idx x 0 + 1 := by
    rw [piecePos_eq, piecePos_eq]
  have h2 : retPos iface face idx j 0 = offset (rowBlocks iface face idx (slotRow x)) 1 := by
    rw [retPos_eq, hj, hpos, Nat.add_zero]
  omega

/-- **and the first piece of the first requested slot is the first piece of the
row.** -/
theorem retPos_zero_eq_zero (idx : RetainedIndex spec F small) {j : Fin p'}
    (h0 : idx.pos j = 0) : retPos iface face idx j 0 = 0 := by
  rw [retPos_eq, h0, offset_zero]

/-! ## 6.  The straddle, concretely

No structure is introduced: `Straddles` is a conjunction of two inequalities on
naturals and `rowBlocks`/`cutBlocks` are lists.  The arithmetic is evaluated
here on the straddle `RetainedRelabeling` §6 and `RetainedCut` §7 exhibit: a
row with one cleared occurrence of length three, carrying two requested slots
of scaled lengths one and two, so the marker sits at metric position one. -/

/-- The cut leaves that occurrence in two pieces. -/
example : OrderedPathSplit.positiveSegments ((cutList [3] 1).getD 0 []) = [1, 2] := rfl

/-- The straddle condition holds there: the pieces before the kept slot total
`0`, the marker is at `1`, and the occurrence has length `3`. -/
example : (0 : ℕ) < 1 ∧ (1 : ℕ) < 0 + 3 := by omega

/-- The two groupings of that row: one block per kept slot on the cut side
(a single block, of two pieces), one block per requested slot on the retained
side (two blocks, of one piece each). -/
example : ([[1, 2]] : List (List ℕ)).flatten = ([[1], [2]] : List (List ℕ)).flatten := rfl

/-- and `piecePos_succ_eq_offset_one` on it: the straddled kept slot's two
pieces are at row places `0` and `1`, and the first block boundary of the
retained refinement is also at `1`. -/
example : offset ([[1, 2]] : List (List ℕ)) 0 + 1 = offset ([[1], [2]] : List (List ℕ)) 1 :=
  rfl

end

end DraismaVargas.LocalCases.RetainedStraddle
