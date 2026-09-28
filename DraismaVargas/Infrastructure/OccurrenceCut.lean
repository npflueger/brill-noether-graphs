import DraismaVargas.Infrastructure.BlockSplitCount

/-!
# One marker cut, read occurrence by occurrence

**Source.**  None.  This is the list arithmetic companion of
`DraismaVargas.Infrastructure.OrderedBlockSplit` and
`DraismaVargas.Infrastructure.BlockSplitCount`.  All three supply bookkeeping
for the markers that the reduction to a cubic model places on retained slots.
Draisma--Vargas Part I does not spell this bookkeeping out: it gives no
detailed integral-scale transport to the requested graph, and does not discuss
the marker cut.

## The problem

`OrderedBlockSplit.blocks l ws` cuts a row's cleared occurrence lengths `l`
into blocks of prescribed totals `ws`: it is indexed by the **blocks**, i.e.
by the requested slots a retained cubic slot carries.  The terminal face's
pruned contracted source is indexed the other way round, by the **occurrences**
-- one slot per positive entry of `l` -- so the split chain that reconciles the
two counts (`DraismaVargas.LocalCases.RetainedRelabeling` §3--§4) has to know, for
each occurrence, into how many pieces the markers cut it and how long they
are.  That is the transpose of `blocks`, and this file supplies it for a
**single** cut, which is the only case the reduction to a cubic model
produces: a `CoreExpansion.SlotKind`
is `single` or `double`, so `RetainedIndexProducer.kindCarried` is a list of
length one or two and a retained row carries at most one marker.

## What is proved

`cutList l a` is that transpose: a list of `l.length` blocks, the `k`-th being
the pieces of the `k`-th occurrence under the cut at total `a`.  It is `[x]` on
an occurrence the cut misses and `[a - S, S + x - a]` on the one it straddles
(`positiveSegments_getD_cutList`, with `S` the total of the earlier
occurrences); its `k`-th entry always sums to `l.getD k 0`
(`sum_getD_cutList`); and it is the same refinement as the cut itself:

```
((cutList l a).map positiveSegments).flatten =
  positiveSegments (splitSum l a).1 ++ positiveSegments (splitSum l a).2
```

(`flatten_map_positiveSegments_cutList`), whence the count
`((cutList l a).map countPos).sum = countPos l + (if alignedB l a then 0 else 1)`
(`sum_map_countPos_cutList`) matching `BlockSplitCount.countPos_splitSum`.

`positiveSegments_splitSum_fst`/`_snd` let the cut be taken on the measured
row or on its positive sublist indifferently, which is what lets the consumer
index the pieces by the *positive* occurrences -- the kept slots -- without
ever naming a position in the uncut row.

## What is NOT proved

Nothing about more than one cut in a row: `cutList` takes a single total `a`.
A retained slot carrying three or more requested slots would need the general
transpose `blocks ws l` and a concatenation lemma for `blocks`, which is not
here; `RetainedCut` therefore carries the hypothesis that every carrier list
has length at most two, and discharges it for the expansion that the reduction
to a cubic model produces.

## Consumers

`DraismaVargas.LocalCases.RetainedCut`, and through it
`RetainedRelabeling.CutRelabeling`: at a terminal face, a core model of the
retained segment data on a canonical split of the pruned contracted source.
-/

namespace DraismaVargas.Infrastructure.OccurrenceCut

open Utilities
open Utilities.Certificate
open Utilities.Certificate.IteratedSplitRefinement
open DraismaVargas.Infrastructure.OrderedBlockSplit
open DraismaVargas.Infrastructure.BlockSplitCount

/-! ## 0.  The positive sublist, as a list operation -/

theorem positiveSegments_nil : OrderedPathSplit.positiveSegments [] = [] := rfl

theorem positiveSegments_cons (x : ℕ) (l : List ℕ) :
    OrderedPathSplit.positiveSegments (x :: l) =
      if 0 < x then x :: OrderedPathSplit.positiveSegments l
      else OrderedPathSplit.positiveSegments l := by
  unfold OrderedPathSplit.positiveSegments
  rw [List.filter_cons]
  by_cases h : 0 < x <;> simp [h]

theorem positiveSegments_append (l l' : List ℕ) :
    OrderedPathSplit.positiveSegments (l ++ l') =
      OrderedPathSplit.positiveSegments l ++ OrderedPathSplit.positiveSegments l' := by
  unfold OrderedPathSplit.positiveSegments
  exact List.filter_append _ _

theorem positiveSegments_idem (l : List ℕ) :
    OrderedPathSplit.positiveSegments (OrderedPathSplit.positiveSegments l) =
      OrderedPathSplit.positiveSegments l := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
      rw [positiveSegments_cons]
      by_cases h : 0 < x
      · rw [if_pos h, positiveSegments_cons, if_pos h, ih]
      · rw [if_neg h, ih]

theorem positiveSegments_reverse (l : List ℕ) :
    OrderedPathSplit.positiveSegments l.reverse =
      (OrderedPathSplit.positiveSegments l).reverse := by
  unfold OrderedPathSplit.positiveSegments
  exact List.filter_reverse

theorem countPos_reverse (l : List ℕ) : countPos l.reverse = countPos l := by
  unfold countPos
  rw [positiveSegments_reverse, List.length_reverse]

theorem countPos_positiveSegments (l : List ℕ) :
    countPos (OrderedPathSplit.positiveSegments l) = countPos l := by
  unfold countPos
  rw [positiveSegments_idem]

theorem countPos_eq_length_of_all_pos {l : List ℕ} (h : ∀ x ∈ l, 0 < x) :
    countPos l = l.length := by
  unfold countPos OrderedPathSplit.positiveSegments
  rw [List.filter_eq_self.mpr (fun x hx ↦ by simpa using h x hx)]

/-! ## 1.  A cut, taken on the measured row or on its positive sublist -/

/-- **The cut does not see the contracted occurrences.**  Both halves of a cut
have the same positive sublist whether the cut is taken on the row or on its
positive sublist, so the pieces may be indexed by the *positive* occurrences.
(The two halves themselves differ: a cut at total `0` produces the block `[0]`
on the row and the block `[]` on its positive sublist.) -/
theorem positiveSegments_splitSum (l : List ℕ) (a : ℕ) :
    OrderedPathSplit.positiveSegments (splitSum l a).1 =
        OrderedPathSplit.positiveSegments
          (splitSum (OrderedPathSplit.positiveSegments l) a).1 ∧
      OrderedPathSplit.positiveSegments (splitSum l a).2 =
        OrderedPathSplit.positiveSegments
          (splitSum (OrderedPathSplit.positiveSegments l) a).2 := by
  induction l generalizing a with
  | nil => exact ⟨rfl, rfl⟩
  | cons x rest ih =>
      by_cases hx : 0 < x
      · rw [positiveSegments_cons x rest, if_pos hx]
        by_cases h : x ≤ a
        · rw [splitSum_cons_of_le rest h,
            splitSum_cons_of_le (OrderedPathSplit.positiveSegments rest) h]
          refine ⟨?_, (ih (a - x)).2⟩
          show OrderedPathSplit.positiveSegments (x :: (splitSum rest (a - x)).1) =
            OrderedPathSplit.positiveSegments
              (x :: (splitSum (OrderedPathSplit.positiveSegments rest) (a - x)).1)
          rw [positiveSegments_cons x (splitSum rest (a - x)).1, if_pos hx,
            positiveSegments_cons x
              (splitSum (OrderedPathSplit.positiveSegments rest) (a - x)).1, if_pos hx,
            (ih (a - x)).1]
        · rw [splitSum_cons_of_gt rest h,
            splitSum_cons_of_gt (OrderedPathSplit.positiveSegments rest) h]
          refine ⟨rfl, ?_⟩
          have hxa : 0 < x - a := by omega
          show OrderedPathSplit.positiveSegments ((x - a) :: rest) =
            OrderedPathSplit.positiveSegments
              ((x - a) :: OrderedPathSplit.positiveSegments rest)
          rw [positiveSegments_cons (x - a) rest, if_pos hxa,
            positiveSegments_cons (x - a) (OrderedPathSplit.positiveSegments rest),
            if_pos hxa, positiveSegments_idem]
      · have hx0 : x = 0 := by omega
        subst hx0
        rw [positiveSegments_cons 0 rest, if_neg (lt_irrefl 0),
          splitSum_cons_of_le rest (Nat.zero_le a), Nat.sub_zero]
        refine ⟨?_, (ih a).2⟩
        show OrderedPathSplit.positiveSegments (0 :: (splitSum rest a).1) =
          OrderedPathSplit.positiveSegments (splitSum (OrderedPathSplit.positiveSegments rest) a).1
        rw [positiveSegments_cons 0 (splitSum rest a).1, if_neg (lt_irrefl 0)]
        exact (ih a).1

theorem positiveSegments_splitSum_fst (l : List ℕ) (a : ℕ) :
    OrderedPathSplit.positiveSegments (splitSum l a).1 =
      OrderedPathSplit.positiveSegments
        (splitSum (OrderedPathSplit.positiveSegments l) a).1 :=
  (positiveSegments_splitSum l a).1

theorem positiveSegments_splitSum_snd (l : List ℕ) (a : ℕ) :
    OrderedPathSplit.positiveSegments (splitSum l a).2 =
      OrderedPathSplit.positiveSegments
        (splitSum (OrderedPathSplit.positiveSegments l) a).2 :=
  (positiveSegments_splitSum l a).2

/-- **A cut beyond the total takes everything.** -/
theorem splitSum_of_sum_le {l : List ℕ} {a : ℕ} (h : l.sum ≤ a) :
    splitSum l a = (l, []) := by
  induction l generalizing a with
  | nil => rfl
  | cons x rest ih =>
      simp only [List.sum_cons] at h
      rw [splitSum_cons_of_le rest (by omega), ih (show rest.sum ≤ a - x by omega)]

/-- Two prescribed block totals cut a row once. -/
theorem blocks_pair (l : List ℕ) (w w' : ℕ) :
    blocks l [w, w'] = [(splitSum l w).1, (splitSum l w).2] := by
  rw [blocks_cons_cons, blocks_singleton]

/-! ## 2.  The transpose of one cut -/

/-- **The pieces of each occurrence, under the cut at total `a`.**  The `k`-th
entry lists the pieces the cut leaves of the `k`-th occurrence of `l`: the
occurrence itself when the cut misses it, and its two parts when the cut
straddles it. -/
def cutList : List ℕ → ℕ → List (List ℕ)
  | [], _ => []
  | x :: rest, a =>
      if x ≤ a then [x] :: cutList rest (a - x)
      else [a, x - a] :: rest.map fun y ↦ [y]

@[simp] theorem cutList_nil (a : ℕ) : cutList [] a = [] := rfl

theorem cutList_cons_of_le {x a : ℕ} (rest : List ℕ) (h : x ≤ a) :
    cutList (x :: rest) a = [x] :: cutList rest (a - x) := by
  simp only [cutList, if_pos h]

theorem cutList_cons_of_gt {x a : ℕ} (rest : List ℕ) (h : ¬ x ≤ a) :
    cutList (x :: rest) a = [a, x - a] :: rest.map fun y ↦ [y] := by
  simp only [cutList, if_neg h]

/-- One entry per occurrence. -/
@[simp] theorem length_cutList (l : List ℕ) (a : ℕ) : (cutList l a).length = l.length := by
  induction l generalizing a with
  | nil => rfl
  | cons x rest ih =>
      by_cases h : x ≤ a
      · rw [cutList_cons_of_le rest h]
        simp only [List.length_cons]
        exact congrArg (· + 1) (ih (a - x))
      · rw [cutList_cons_of_gt rest h]
        simp

/-- **Each entry recovers its occurrence.** -/
theorem sum_getD_cutList (l : List ℕ) (a k : ℕ) :
    ((cutList l a).getD k []).sum = l.getD k 0 := by
  induction l generalizing a k with
  | nil => simp [List.getD_eq_getElem?_getD]
  | cons x rest ih =>
      by_cases h : x ≤ a
      · rw [cutList_cons_of_le rest h]
        cases k with
        | zero => simp
        | succ k' =>
            rw [List.getD_cons_succ, List.getD_cons_succ]
            exact ih (a - x) k'
      · rw [cutList_cons_of_gt rest h]
        cases k with
        | zero =>
            simp only [List.getD_cons_zero, List.sum_cons, List.sum_nil]
            omega
        | succ k' =>
            rw [List.getD_cons_succ, List.getD_cons_succ]
            by_cases hk : k' < rest.length
            · rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
                List.getD_eq_getElem rest 0 hk]
              simp
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hk),
                List.getD_eq_default _ _ (Nat.le_of_not_lt hk)]
              rfl

/-- Flattening the singleton blocks past the cut. -/
theorem flatten_map_positiveSegments_singletons (l : List ℕ) :
    ((l.map fun y ↦ [y]).map OrderedPathSplit.positiveSegments).flatten =
      OrderedPathSplit.positiveSegments l := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
      simp only [List.map_cons, List.flatten_cons]
      rw [ih, ← positiveSegments_append]
      rfl

/-- **The transpose is the same refinement.**  Reading the cut occurrence by
occurrence and reading it block by block give the same ordered list of positive
pieces. -/
theorem flatten_map_positiveSegments_cutList (l : List ℕ) (a : ℕ) :
    ((cutList l a).map OrderedPathSplit.positiveSegments).flatten =
      OrderedPathSplit.positiveSegments (splitSum l a).1 ++
        OrderedPathSplit.positiveSegments (splitSum l a).2 := by
  induction l generalizing a with
  | nil => rfl
  | cons x rest ih =>
      by_cases h : x ≤ a
      · rw [cutList_cons_of_le rest h, splitSum_cons_of_le rest h]
        simp only [List.map_cons, List.flatten_cons]
        rw [ih (a - x),
          show (x :: (splitSum rest (a - x)).1) = [x] ++ (splitSum rest (a - x)).1 from rfl,
          positiveSegments_append, List.append_assoc]
      · rw [cutList_cons_of_gt rest h, splitSum_cons_of_gt rest h]
        simp only [List.map_cons, List.flatten_cons]
        rw [flatten_map_positiveSegments_singletons,
          show ([a, x - a] : List ℕ) = [a] ++ [x - a] from rfl,
          show ((x - a) :: rest) = [x - a] ++ rest from rfl,
          positiveSegments_append, positiveSegments_append, List.append_assoc]

/-! ## 3.  The count -/

theorem sum_map_eq_sum_range {α : Type*} (l : List α) (d : α) (g : α → ℕ) :
    (l.map g).sum = ∑ k ∈ Finset.range l.length, g (l.getD k d) := by
  induction l with
  | nil => simp
  | cons x rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [Finset.sum_range_succ', ih]
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      omega

/-- **The transpose has the same positive count as the cut.** -/
theorem sum_map_countPos_cutList' (l : List ℕ) (a : ℕ) :
    ((cutList l a).map countPos).sum =
      countPos (splitSum l a).1 + countPos (splitSum l a).2 := by
  have hflat := congrArg List.length (flatten_map_positiveSegments_cutList l a)
  rw [List.length_flatten, List.length_append, List.map_map] at hflat
  exact hflat

/-- **The cut adds exactly one piece, and only at a misaligned cut.**  The
occurrence-by-occurrence count of `BlockSplitCount.countPos_splitSum`. -/
theorem sum_map_countPos_cutList {l : List ℕ} {a : ℕ} (hle : a ≤ l.sum) :
    ((cutList l a).map countPos).sum = countPos l + (if alignedB l a then 0 else 1) := by
  rw [sum_map_countPos_cutList' l a]
  exact countPos_splitSum hle

/-! ## 4.  Which occurrence the cut straddles -/

/-- **The canonical cut, occurrence by occurrence.**  The `k`-th positive
occurrence is left whole unless the cut falls strictly inside it, in which case
it is cut in two at the prescribed metric position. -/
theorem positiveSegments_getD_cutList (l : List ℕ) (a k : ℕ) (hpos : 0 < l.getD k 0) :
    OrderedPathSplit.positiveSegments ((cutList l a).getD k []) =
      if (l.take k).sum < a ∧ a < (l.take k).sum + l.getD k 0 then
        [a - (l.take k).sum, (l.take k).sum + l.getD k 0 - a]
      else [l.getD k 0] := by
  induction l generalizing a k with
  | nil => simp at hpos
  | cons x rest ih =>
      by_cases h : x ≤ a
      · rw [cutList_cons_of_le rest h]
        cases k with
        | zero =>
            simp only [List.getD_cons_zero, List.take_zero, List.sum_nil] at hpos ⊢
            rw [if_neg (by omega), positiveSegments_cons, if_pos hpos]
            rfl
        | succ k' =>
            simp only [List.getD_cons_succ, List.take_succ_cons, List.sum_cons] at hpos ⊢
            rw [ih (a - x) k' hpos]
            by_cases hc : (rest.take k').sum < a - x ∧ a - x < (rest.take k').sum + rest.getD k' 0
            · rw [if_pos hc, if_pos (by omega)]
              congr 1
              · omega
              · congr 1
                omega
            · rw [if_neg hc, if_neg (by omega)]
      · rw [cutList_cons_of_gt rest h]
        cases k with
        | zero =>
            simp only [List.getD_cons_zero, List.take_zero, List.sum_nil] at hpos ⊢
            by_cases ha : 0 < a
            · rw [if_pos ⟨ha, by omega⟩, positiveSegments_cons, if_pos ha,
                positiveSegments_cons, if_pos (by omega), positiveSegments_nil]
              simp
            · rw [if_neg (by omega), positiveSegments_cons, if_neg (by omega),
                positiveSegments_cons, if_pos (by omega), positiveSegments_nil]
              congr 1
              omega
        | succ k' =>
            simp only [List.getD_cons_succ, List.take_succ_cons, List.sum_cons] at hpos ⊢
            rw [if_neg (by omega)]
            by_cases hk : k' < rest.length
            · rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
                List.getD_eq_getElem _ _ hk, positiveSegments_cons, if_pos (by
                  rwa [List.getD_eq_getElem _ _ hk] at hpos)]
              rfl
            · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hk)] at hpos
              simp at hpos

end DraismaVargas.Infrastructure.OccurrenceCut
