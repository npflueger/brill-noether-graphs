import DraismaVargas.Infrastructure.OccurrenceCut

/-!
# Indexing a flattened list of blocks

**Source.**  None.  This is list bookkeeping, the companion of
`DraismaVargas.Infrastructure.OccurrenceCut`.  Neither Draisma--Vargas Part I
nor Vargas, Part II writes the marker cut down (neither paper spells out the
transport at an integral scale), so a fortiori neither writes down the two
readings of it that this file identifies.

## The problem

`DraismaVargas.LocalCases.RetainedCut.flatten_map_carried_segments` says that
two lists of lists have the *same flattening*: the segment lists the retained
refinement prescribes along one retained row, one per requested slot the row
carries, and the piece lists the marker cut leaves of the kept slots of that
row.  A `RefinementCore.CoreModel` needs that identity as an **equivalence** of
the two index types

```
Σ k : Fin LL.length, Fin (LL.getD k []).length      (block `k`, entry `q`)
```

and it needs to know which entry of the flattening a pair `(k, q)` names, so
that the prescribed segment lengths can be compared.  This file supplies both,
for an arbitrary list of blocks.

## What is proved

`offset LL k` is the number of entries of `LL.flatten` before block `k`
(`offset_succ`, `offset_mono`, `offset_length`).  The map
`(k, q) ↦ offset LL k + q` lands in `Fin LL.flatten.length`
(`add_lt_length_flatten`), is injective (`flatPos_injective`) and is therefore
an equivalence `sigmaEquiv` by a cardinality count; and it reads the entry it
names, `getD_flatten`:

```
LL.flatten.getD (offset LL k + q) d = (LL.getD k []).getD q d
```

§6--§7 add the metric reading of the same index.  `sum_take_flatten` computes a
prefix sum of `LL.flatten` block by block, and `take_sum_inj` says that on an
all-positive list a prefix sum determines its own prefix.  Together they turn a
*metric* coincidence of two groupings into an *index* coincidence, which is how
the vertex half of the retained relabeling locates the marker: the straddle
point of the marker cut and the block boundary of the retained refinement have
the same prefix sum along a retained row, hence are the same place.

`sigmaEquivOfFlattenEq` is the transport an equality of flattenings gives: if
`LL.flatten = MM.flatten` then the two block indexings are equivalent, and
`getD_sigmaEquivOfFlattenEq` says corresponding entries agree.  That is the
form the slot bijection of the retained core model
(`DraismaVargas.LocalCases.RetainedCoreModel`) is built from.

## What is NOT proved

Nothing about the *structure* of the two groupings -- which block of `MM` a
block of `LL` meets, or how many.  The consumer reads that off its own
arithmetic (`OccurrenceCut.positiveSegments_getD_cutList`); this file only
identifies the two index sets over one and the same flattened list.

## Consumers

`DraismaVargas.LocalCases.RetainedRowPieces`,
`DraismaVargas.LocalCases.RetainedCoreModel` and
`DraismaVargas.LocalCases.RetainedStraddle`, and through them
`RetainedRelabeling.CutRelabeling`, the relabeling that transports a pencil on
the terminal face back to the requested core.
-/

namespace DraismaVargas.Infrastructure.FlattenIndex

open DraismaVargas.Infrastructure.OccurrenceCut

universe u

variable {α : Type u}

/-! ## 1.  The offset of a block -/

/-- **The number of entries of `LL.flatten` before block `k`.** -/
def offset (LL : List (List α)) (k : ℕ) : ℕ := ((LL.take k).map List.length).sum

@[simp] theorem offset_zero (LL : List (List α)) : offset LL 0 = 0 := rfl

/-- **Each block moves the offset by its own length.** -/
theorem offset_succ (LL : List (List α)) (k : ℕ) :
    offset LL (k + 1) = offset LL k + (LL.getD k []).length := by
  unfold offset
  rw [List.take_add_one, List.map_append, List.sum_append]
  refine congrArg (fun total ↦ ((LL.take k).map List.length).sum + total) ?_
  rw [List.getD_eq_getElem?_getD]
  rcases h : LL[k]? with _ | B
  · simp
  · simp

theorem offset_le_succ (LL : List (List α)) (k : ℕ) : offset LL k ≤ offset LL (k + 1) := by
  rw [offset_succ]
  omega

theorem offset_mono (LL : List (List α)) {k l : ℕ} (h : k ≤ l) :
    offset LL k ≤ offset LL l := by
  induction l, h using Nat.le_induction with
  | base => exact le_rfl
  | succ l _ ih => exact ih.trans (offset_le_succ LL l)

/-- **All the blocks together are the flattening.** -/
theorem offset_length (LL : List (List α)) : offset LL LL.length = LL.flatten.length := by
  rw [offset, List.take_length, List.length_flatten]

theorem lt_length_of_getD_pos {LL : List (List α)} {k : ℕ}
    (h : 0 < (LL.getD k []).length) : k < LL.length := by
  by_contra hk
  rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hk)] at h
  simp at h

/-- **An entry of a block is an entry of the flattening.** -/
theorem add_lt_length_flatten (LL : List (List α)) {k q : ℕ}
    (hq : q < (LL.getD k []).length) : offset LL k + q < LL.flatten.length := by
  have hk : k < LL.length := lt_length_of_getD_pos (by omega)
  have h1 : offset LL (k + 1) = offset LL k + (LL.getD k []).length := offset_succ LL k
  have h2 : offset LL (k + 1) ≤ offset LL LL.length := offset_mono LL hk
  rw [offset_length] at h2
  omega

/-! ## 2.  The entry a pair names -/

theorem offset_cons_succ (B : List α) (rest : List (List α)) (k : ℕ) :
    offset (B :: rest) (k + 1) = B.length + offset rest k := by
  unfold offset
  rw [List.take_succ_cons, List.map_cons, List.sum_cons]

theorem getD_append_left (B C : List α) (d : α) {i : ℕ} (hi : i < B.length) :
    (B ++ C).getD i d = B.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_append_right (B C : List α) (d : α) (i : ℕ) :
    (B ++ C).getD (B.length + i) d = C.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega)]
  congr 2
  omega

/-- **The flattening, read block by block.** -/
theorem getD_flatten (LL : List (List α)) (d : α) {k q : ℕ}
    (hq : q < (LL.getD k []).length) :
    LL.flatten.getD (offset LL k + q) d = (LL.getD k []).getD q d := by
  induction LL generalizing k with
  | nil =>
      rw [List.getD_eq_default _ _ (by simp)] at hq
      simp at hq
  | cons B rest ih =>
      cases k with
      | zero =>
          rw [List.getD_cons_zero] at hq ⊢
          rw [offset_zero, Nat.zero_add, List.flatten_cons, getD_append_left _ _ _ hq]
      | succ k =>
          rw [List.getD_cons_succ] at hq ⊢
          rw [offset_cons_succ, List.flatten_cons,
            show B.length + offset rest k + q = B.length + (offset rest k + q) by omega,
            getD_append_right]
          exact ih hq

/-- **The place in the flattening determines the block and the entry.**  This
is the injectivity of the flattening index, in non-dependent form. -/
theorem offset_add_inj (LL : List (List α)) {k q k' q' : ℕ}
    (hq : q < (LL.getD k []).length) (hq' : q' < (LL.getD k' []).length)
    (h : offset LL k + q = offset LL k' + q') : k = k' ∧ q = q' := by
  have hk : k = k' := by
    rcases Nat.lt_trichotomy k k' with hlt | hlt | hlt
    · have h1 := offset_succ LL k
      have h2 := offset_mono LL (show k + 1 ≤ k' by omega)
      omega
    · exact hlt
    · have h1 := offset_succ LL k'
      have h2 := offset_mono LL (show k' + 1 ≤ k by omega)
      omega
  refine ⟨hk, ?_⟩
  subst hk
  omega

/-! ## 3.  The index equivalence -/

/-- A pair (block, entry within it). -/
abbrev BlockIndex (LL : List (List α)) : Type :=
  Σ k : Fin LL.length, Fin ((LL.getD (k : ℕ) []).length)

/-- Its place in the flattening. -/
def flatPos (LL : List (List α)) (x : BlockIndex LL) : ℕ :=
  offset LL (x.1 : ℕ) + (x.2 : ℕ)

theorem flatPos_lt (LL : List (List α)) (x : BlockIndex LL) :
    flatPos LL x < LL.flatten.length :=
  add_lt_length_flatten LL x.2.isLt

theorem flatPos_injective (LL : List (List α)) :
    Function.Injective (flatPos LL) := by
  rintro ⟨k, q⟩ ⟨k', q'⟩ hEq
  obtain ⟨hk, hq⟩ := offset_add_inj LL q.isLt q'.isLt hEq
  obtain rfl : k = k' := Fin.ext hk
  exact congrArg (Sigma.mk k) (Fin.ext hq)

theorem card_blockIndex (LL : List (List α)) :
    Fintype.card (BlockIndex LL) = LL.flatten.length := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ (LL.getD k []).length) LL.length,
    List.length_flatten, sum_map_eq_sum_range LL [] List.length]

/-- **The entries of a flattened list are the pairs (block, entry).** -/
noncomputable def sigmaEquiv (LL : List (List α)) :
    BlockIndex LL ≃ Fin LL.flatten.length :=
  Equiv.ofBijective (fun x ↦ ⟨flatPos LL x, flatPos_lt LL x⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun x y hxy ↦ flatPos_injective LL (congrArg Fin.val hxy),
        by rw [card_blockIndex, Fintype.card_fin]⟩)

@[simp] theorem sigmaEquiv_val (LL : List (List α)) (x : BlockIndex LL) :
    ((sigmaEquiv LL x : Fin LL.flatten.length) : ℕ) = flatPos LL x := rfl

/-- **and the pair names its own entry.** -/
theorem getD_sigmaEquiv (LL : List (List α)) (d : α) (x : BlockIndex LL) :
    LL.flatten.getD ((sigmaEquiv LL x : Fin LL.flatten.length) : ℕ) d =
      (LL.getD (x.1 : ℕ) []).getD (x.2 : ℕ) d :=
  getD_flatten LL d x.2.isLt

/-! ## 4.  Two groupings of one flattened list -/

/-- **Two block lists with the same flattening index it the same way.**  This
is the equivalence underlying the slot bijection of the retained relabeling:
the retained refinement's segment lists along a row and the marker cut's piece
lists of its kept slots are two groupings of one ordered list of positive
pieces. -/
noncomputable def sigmaEquivOfFlattenEq {LL MM : List (List α)}
    (h : LL.flatten = MM.flatten) : BlockIndex LL ≃ BlockIndex MM :=
  (sigmaEquiv LL).trans ((finCongr (congrArg List.length h)).trans (sigmaEquiv MM).symm)

/-- **The place in the flattening is the same on both sides.** -/
theorem flatPos_sigmaEquivOfFlattenEq {LL MM : List (List α)}
    (h : LL.flatten = MM.flatten) (x : BlockIndex LL) :
    flatPos MM (sigmaEquivOfFlattenEq h x) = flatPos LL x := by
  show ((sigmaEquiv MM (sigmaEquivOfFlattenEq h x) : Fin MM.flatten.length) : ℕ) = _
  rw [sigmaEquivOfFlattenEq, Equiv.trans_apply, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  rfl

/-- **and corresponding entries agree.** -/
theorem getD_sigmaEquivOfFlattenEq {LL MM : List (List α)} (h : LL.flatten = MM.flatten)
    (d : α) (x : BlockIndex LL) :
    (MM.getD ((sigmaEquivOfFlattenEq h x).1 : ℕ) []).getD
        ((sigmaEquivOfFlattenEq h x).2 : ℕ) d =
      (LL.getD (x.1 : ℕ) []).getD (x.2 : ℕ) d := by
  have h1 := getD_flatten MM d (sigmaEquivOfFlattenEq h x).2.isLt
  have h2 := getD_flatten LL d x.2.isLt
  have h3 := flatPos_sigmaEquivOfFlattenEq h x
  unfold flatPos at h3
  rw [← h1, ← h2, h3, h]

/-! ## 5.  Blocks given by a map -/

section Map

variable {β : Type*}

theorem getD_map_of_lt (l : List β) (f : β → List α) {k : ℕ} (hk : k < l.length) :
    (l.map f).getD k [] = f l[k] := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map]

theorem sum_map_eq_sum_fin (l : List β) (g : β → ℕ) :
    (l.map g).sum = ∑ k : Fin l.length, g l[(k : ℕ)] := by
  induction l with
  | nil => simp
  | cons x rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [Fin.sum_univ_succ, ih]
      rfl

/-- **The place in `(l.map f).flatten` of entry `q` of block `k`.** -/
def mapPos (l : List β) (f : β → List α) (k q : ℕ) : ℕ := offset (l.map f) k + q

theorem mapPos_lt (l : List β) (f : β → List α) {k q : ℕ} (hk : k < l.length)
    (hq : q < (f l[k]).length) : mapPos l f k q < (l.map f).flatten.length := by
  refine add_lt_length_flatten _ ?_
  rwa [getD_map_of_lt l f hk]

theorem mapPos_inj (l : List β) (f : β → List α) {k q k' q' : ℕ}
    (hk : k < l.length) (hk' : k' < l.length)
    (hq : q < (f l[k]).length) (hq' : q' < (f l[k']).length)
    (h : mapPos l f k q = mapPos l f k' q') : k = k' ∧ q = q' := by
  refine offset_add_inj (l.map f) ?_ ?_ h
  · rwa [getD_map_of_lt l f hk]
  · rwa [getD_map_of_lt l f hk']

theorem getD_flatten_mapPos (l : List β) (f : β → List α) (d : α) {k q : ℕ}
    (hk : k < l.length) (hq : q < (f l[k]).length) :
    (l.map f).flatten.getD (mapPos l f k q) d = (f l[k]).getD q d := by
  have h := getD_flatten (l.map f) d (k := k) (q := q) (by rwa [getD_map_of_lt l f hk])
  rwa [getD_map_of_lt l f hk] at h

theorem length_flatten_map (l : List β) (f : β → List α) :
    (l.map f).flatten.length = ∑ k : Fin l.length, (f l[(k : ℕ)]).length := by
  rw [List.length_flatten, List.map_map]
  exact sum_map_eq_sum_fin l (fun b ↦ (f b).length)

end Map

/-! ## 6.  Prefix sums along the flattening -/

/-- **The first `k` blocks are the first `offset LL k` entries.** -/
theorem flatten_take (LL : List (List α)) (k : ℕ) :
    (LL.take k).flatten = LL.flatten.take (offset LL k) := by
  have hlen : offset LL k = (LL.take k).flatten.length := by
    rw [List.length_flatten, offset]
  have hsplit : LL.flatten = (LL.take k).flatten ++ (LL.drop k).flatten := by
    conv_lhs => rw [← List.take_append_drop k LL]
    rw [List.flatten_append]
  rw [hlen, hsplit, List.take_append]
  simp

/-- **and the entries after them start with block `k`.** -/
theorem take_drop_flatten (LL : List (List α)) {k q : ℕ}
    (hq : q ≤ (LL.getD k []).length) :
    ((LL.drop k).flatten).take q = (LL.getD k []).take q := by
  rcases Nat.lt_or_ge k LL.length with hk | hk
  · rw [List.getD_eq_getElem _ _ hk] at hq ⊢
    rw [List.drop_eq_getElem_cons hk, List.flatten_cons, List.take_append,
      show q - LL[k].length = 0 by omega]
    simp
  · rw [List.getD_eq_default _ _ hk] at hq ⊢
    simp only [List.length_nil, Nat.le_zero] at hq
    subst hq
    simp

/-- **A prefix sum of the flattening, block by block.** -/
theorem sum_take_flatten (LL : List (List ℕ)) (k q : ℕ)
    (hq : q ≤ (LL.getD k []).length) :
    (LL.flatten.take (offset LL k + q)).sum =
      ((LL.take k).map List.sum).sum + ((LL.getD k []).take q).sum := by
  have hlen : (LL.take k).flatten.length = offset LL k := by
    rw [List.length_flatten, offset]
  have hsplit : LL.flatten = (LL.take k).flatten ++ (LL.drop k).flatten := by
    conv_lhs => rw [← List.take_append_drop k LL]
    rw [List.flatten_append]
  rw [hsplit, ← hlen, List.take_append, List.sum_append,
    List.take_of_length_le (by omega), List.sum_flatten,
    show (LL.take k).flatten.length + q - (LL.take k).flatten.length = q by omega,
    take_drop_flatten LL hq]

/-- **A prefix sum at a block boundary.** -/
theorem sum_take_flatten_offset (LL : List (List ℕ)) (k : ℕ) :
    (LL.flatten.take (offset LL k)).sum = ((LL.take k).map List.sum).sum := by
  have h := sum_take_flatten LL k 0 (Nat.zero_le _)
  simpa using h

/-! ## 7.  Prefix sums of an all-positive list -/

theorem sum_take_succ (l : List ℕ) {t : ℕ} (ht : t < l.length) :
    (l.take (t + 1)).sum = (l.take t).sum + l[t] := by
  rw [List.take_add_one, List.getElem?_eq_getElem ht, List.sum_append]
  simp

/-- **The prefix sums of an all-positive list are strictly increasing.** -/
theorem sum_take_lt_sum_take {l : List ℕ} (hpos : ∀ x ∈ l, 0 < x) {t t' : ℕ}
    (htt : t < t') (ht' : t' ≤ l.length) : (l.take t).sum < (l.take t').sum := by
  induction t', htt using Nat.le_induction with
  | base =>
      have ht : t < l.length := by omega
      rw [sum_take_succ l ht]
      have := hpos l[t] (List.getElem_mem ht)
      omega
  | succ u hu ih =>
      have hu' : u < l.length := by omega
      rw [sum_take_succ l hu']
      have := hpos l[u] (List.getElem_mem hu')
      have := ih (by omega)
      omega

/-- **so a prefix sum determines the prefix.** -/
theorem take_sum_inj {l : List ℕ} (hpos : ∀ x ∈ l, 0 < x) {t t' : ℕ}
    (ht : t ≤ l.length) (ht' : t' ≤ l.length)
    (h : (l.take t).sum = (l.take t').sum) : t = t' := by
  rcases Nat.lt_trichotomy t t' with hlt | hlt | hlt
  · exact absurd h (Nat.ne_of_lt (sum_take_lt_sum_take hpos hlt ht'))
  · exact hlt
  · exact absurd h.symm (Nat.ne_of_lt (sum_take_lt_sum_take hpos hlt ht))

/-! ## 8.  The gadget, concretely

No structure is introduced: `offset` and `flatPos` are total arithmetic
functions and `sigmaEquiv` an `Equiv` between two `Fintype`s, whose inhabitants
are the pairs themselves.  The arithmetic is evaluated here on the straddle
`DraismaVargas.LocalCases.RetainedCut` §7 exhibits -- one occurrence of length
three cut at metric position one -- read as blocks. -/

example : offset ([[1, 2], [3]] : List (List ℕ)) 0 = 0 := rfl

example : offset ([[1, 2], [3]] : List (List ℕ)) 1 = 2 := rfl

example : offset ([[1, 2], [3]] : List (List ℕ)) 2 = 3 := rfl

example : ([[1, 2], [3]] : List (List ℕ)).flatten = [1, 2, 3] := rfl

/-- The two groupings of one straddled row: one requested slot per block, and
one kept slot per block. -/
example : ([[1], [2]] : List (List ℕ)).flatten = ([[1, 2]] : List (List ℕ)).flatten := rfl

example : flatPos ([[1], [2]] : List (List ℕ)) ⟨⟨1, by norm_num⟩, ⟨0, by norm_num⟩⟩ = 1 := rfl

end DraismaVargas.Infrastructure.FlattenIndex
