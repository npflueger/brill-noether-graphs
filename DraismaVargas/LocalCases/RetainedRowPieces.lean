import DraismaVargas.Infrastructure.FlattenIndex
import DraismaVargas.LocalCases.RetainedCut

/-!
# The two readings of a retained row: prescribed segments and marker pieces

**Source.**  This is the slot half of the terminal core model.  At a nonempty
expansion forest the model's target is the pruned contracted spec **cut at the
straddled markers** (`DraismaVargas.LocalCases.RetainedCut`).  The marker cut
is in neither Draisma--Vargas Part I nor Vargas, Part II -- neither spells out
the transport at an integral scale -- so, as in
`DraismaVargas.LocalCases.RetainedCut` and
`DraismaVargas.Infrastructure.OccurrenceCut`, nothing here is a transcription
of either paper.  The list bookkeeping is
`DraismaVargas.Infrastructure.FlattenIndex`.

## What is proved

`RetainedCut.flatten_map_carried_segments` says that the segment lists the
retained refinement prescribes along one retained row -- one per requested slot
the row carries -- and the piece lists the marker cut leaves of the kept slots
of that row have the **same flattening**.  This file turns that identity into
an indexing of one ordered list of positive pieces, `rowPieces`, from each
side.

* §1 regroups the requested slots over the retained rows: `carriedEquiv`, built
  from `RetainedIndex`'s `owner`/`pos`/`carried_getElem`/`nodup`.

* §2 regroups the kept slots the same way: a row displaying a kept slot is
  retained (`not_mem_forest_of_slotIndex`, from
  `RetainedRelabeling.positiveRow_eq_nil_of_mem_forest`), and `rowSlotEquiv`
  identifies `RetainedRelabeling.SlotIndex` with the surviving occurrences of
  the retained rows.

* §3 is `rowPieces`, the ordered list of positive pieces along one retained
  row, together with its count (`card_rowPos`) and the identity
  `rowPieces_eq_cut` that reads it as the marker cut instead.

* §4 indexes it from the requested side: `retPos` places the `m`-th prescribed
  segment of the requested slot `j`, `retRowEquiv` is the resulting bijection,
  and `getD_rowPieces_retPos` says the place names the prescribed segment.

* §5 indexes it from the kept side: `piecePos` places the `t`-th piece of the
  kept slot `x`, `piecePos_inj` says two pieces at one place of one row are the
  same piece of the same kept slot, and `getD_rowPieces_piecePos` reads it off.

## What is not proved here -- the explicit hypotheses

1. **`hTwo : RetainedCut.CarriesAtMostTwo idx`** -- at most one marker per
   retained row -- is carried by every statement that uses `rowPieces_eq_cut`.
   `RetainedCut.carried_length_le_two` discharges it for the expansion model of
   the stable-model reduction.
2. Nothing about the cut spec itself: no bijection onto
   `RetainedCut.cutSpec`'s slots, no orientation, no vertex map.  That is
   `DraismaVargas.LocalCases.RetainedCoreModel`.

## Consumers

`DraismaVargas.LocalCases.RetainedCoreModel`, and through it
`RetainedRelabeling.CutRelabeling`, the relabeling that transports a pencil on
the terminal face back to the requested core.
-/

namespace DraismaVargas.LocalCases.RetainedRowPieces

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

/-! ## 1.  The requested slots, regrouped over the retained rows -/

theorem sum_map_one {α : Type*} (l : List α) : (l.map fun _ ↦ (1 : ℕ)).sum = l.length := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      omega

/-- The requested slot sitting at position `y.2` of the carrier list of the
retained row `y.1`. -/
def carriedAt (idx : RetainedIndex spec F small)
    (y : Σ e : {i : Fin p // i ∉ F}, Fin (idx.carried e).length) : Fin p' :=
  (idx.carried y.1)[(y.2 : ℕ)]

/-- **`owner` and `pos` locate a requested slot in its carrier list.** -/
theorem carriedAt_owner (idx : RetainedIndex spec F small) (j : Fin p') :
    carriedAt idx ⟨idx.owner j, ⟨idx.pos j, idx.pos_lt j⟩⟩ = j := by
  have h := idx.carried_getElem j
  rw [List.getElem?_eq_getElem (idx.pos_lt j), Option.some_inj] at h
  exact h

theorem card_sigma_carried (idx : RetainedIndex spec F small) :
    Fintype.card (Σ e : {i : Fin p // i ∉ F}, Fin (idx.carried e).length) = p' := by
  have h := sum_over_carried idx (fun _ ↦ (1 : ℕ))
  simp only [sum_map_one] at h
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [← h]
  simp

/-- **The requested slots are the carrier positions of the retained rows.** -/
def carriedEquiv (idx : RetainedIndex spec F small) :
    Fin p' ≃ Σ e : {i : Fin p // i ∉ F}, Fin (idx.carried e).length :=
  Equiv.ofBijective (fun j ↦ ⟨idx.owner j, ⟨idx.pos j, idx.pos_lt j⟩⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨Function.LeftInverse.injective (carriedAt_owner idx), by
        rw [Fintype.card_fin, card_sigma_carried]⟩)

@[simp] theorem carriedEquiv_fst (idx : RetainedIndex spec F small) (j : Fin p') :
    (carriedEquiv idx j).1 = idx.owner j := rfl

@[simp] theorem carriedEquiv_snd (idx : RetainedIndex spec F small) (j : Fin p') :
    ((carriedEquiv idx j).2 : ℕ) = idx.pos j := rfl

theorem carriedAt_carriedEquiv (idx : RetainedIndex spec F small) (j : Fin p') :
    carriedAt idx (carriedEquiv idx j) = j :=
  carriedAt_owner idx j

/-! ## 2.  The kept slots, regrouped over the retained rows -/

variable {iface : InputInterface spec strong.toPresentation coordinates F}

/-- **A row displaying a kept slot is retained**: a forest row is contracted
whole (`RetainedRelabeling.positiveRow_eq_nil_of_mem_forest`). -/
theorem not_mem_forest_of_slotIndex (x : SlotIndex iface face) : x.1 ∉ F := by
  intro hx
  have hnil := positiveRow_eq_nil_of_mem_forest (iface := iface) (face := face) hx
  have h : 0 < (positiveRow iface face x.1).length :=
    lt_of_le_of_lt (Nat.zero_le _) x.2.isLt
  rw [hnil] at h
  simp at h

/-- The retained row displaying a kept slot. -/
def slotRow (x : SlotIndex iface face) : {i : Fin p // i ∉ F} :=
  ⟨x.1, not_mem_forest_of_slotIndex x⟩

theorem card_sigma_positiveRow
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates) :
    Fintype.card (Σ e : {i : Fin p // i ∉ F}, Fin (positiveRow iface face ↑e).length) =
      Fintype.card (SlotIndex iface face) := by
  rw [Fintype.card_sigma, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact (sum_positiveRow_eq (face := face) iface).symm

/-- **The kept slots are the surviving occurrences of the retained rows.** -/
def rowSlotEquiv (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates) :
    (Σ e : {i : Fin p // i ∉ F}, Fin (positiveRow iface face ↑e).length) ≃
      SlotIndex iface face :=
  Equiv.ofBijective (fun y ↦ ⟨(y.1 : Fin p), y.2⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨by
        rintro ⟨⟨i, hi⟩, m⟩ ⟨⟨i', hi'⟩, m'⟩ hEq
        simp only [Sigma.mk.injEq] at hEq
        obtain ⟨h1, h2⟩ := hEq
        subst h1
        obtain rfl : m = m' := eq_of_heq h2
        rfl,
        card_sigma_positiveRow iface face⟩)

@[simp] theorem rowSlotEquiv_apply
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (y : Σ e : {i : Fin p // i ∉ F}, Fin (positiveRow iface face ↑e).length) :
    rowSlotEquiv iface face y = ⟨(y.1 : Fin p), y.2⟩ := rfl

theorem rowSlotEquiv_symm_apply (x : SlotIndex iface face) :
    (rowSlotEquiv iface face).symm x = ⟨slotRow x, x.2⟩ :=
  ((rowSlotEquiv iface face).symm_apply_eq).mpr rfl

/-! ## 3.  The positive pieces along a retained row -/

/-- A sigma over `Fin`-fibres is determined by its two components, read as
naturals.  (Stated to avoid `HEq` in the injectivity proofs below.) -/
theorem sigma_fin_ext {ι : Type*} {g : ι → ℕ} {x y : Σ i : ι, Fin (g i)}
    (h1 : x.1 = y.1) (h2 : (x.2 : ℕ) = (y.2 : ℕ)) : x = y := by
  obtain ⟨i, m⟩ := x
  obtain ⟨i', m'⟩ := y
  simp only at h1 h2
  subst h1
  exact congrArg _ (Fin.ext h2)

theorem getD_reverse {α : Type*} (l : List α) (d : α) {q : ℕ} (hq : q < l.length) :
    l.reverse.getD q d = l.getD (l.length - 1 - q) d := by
  have h1 : q < l.reverse.length := by
    rw [List.length_reverse]
    exact hq
  rw [List.getD_eq_getElem _ _ h1, List.getElem_reverse h1,
    List.getD_eq_getElem _ _ (by omega)]

/-- **The ordered list of positive pieces along a retained row**, read by the
retained refinement: the segment lists of the requested slots the row carries,
concatenated in series order. -/
def rowPieces (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small) (e : {i : Fin p // i ∉ F}) : List ℕ :=
  ((idx.carried e).map fun j ↦ (Retained.segmentData iface face idx).segments j).flatten

/-- **A place along a retained row.** -/
abbrev RowPos (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small) : Type :=
  Σ e : {i : Fin p // i ∉ F}, Fin (rowPieces iface face idx e).length

theorem length_rowPieces (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small) (e : {i : Fin p // i ∉ F}) :
    (rowPieces iface face idx e).length =
      ((idx.carried e).map fun j ↦
        ((Retained.segmentData iface face idx).segments j).length).sum := by
  rw [rowPieces, List.length_flatten, List.map_map]
  rfl

theorem card_rowPos (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small) :
    Fintype.card (RowPos iface face idx) =
      ∑ j : Fin p', ((Retained.segmentData iface face idx).segments j).length := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [sum_over_carried idx
    (fun j ↦ ((Retained.segmentData iface face idx).segments j).length)]
  exact Finset.sum_congr rfl fun e _ ↦ length_rowPieces iface face idx e

/-- **The retained row's pieces, read by the marker cut instead.**  This is
`RetainedCut.flatten_map_carried_segments`: the two readings of the cut are one
and the same ordered list. -/
theorem rowPieces_eq_cut (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small) (hTwo : CarriesAtMostTwo idx)
    (e : {i : Fin p // i ∉ F}) :
    rowPieces iface face idx e =
      ((cutList (positiveLengths iface face ↑e) (cutOffsetAt face idx ↑e)).map
        OrderedPathSplit.positiveSegments).flatten :=
  flatten_map_carried_segments iface face idx hTwo e

/-! ## 4.  The requested side: one place per prescribed segment -/

theorem getElem_carried_pos (idx : RetainedIndex spec F small) (j : Fin p') :
    (idx.carried (idx.owner j))[idx.pos j]'(idx.pos_lt j) = j :=
  carriedAt_owner idx j

/-- The place along its row of the `m`-th prescribed segment of the requested
slot `j`. -/
def retPos (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small) (j : Fin p') (m : ℕ) : ℕ :=
  mapPos (idx.carried (idx.owner j))
    (fun k ↦ (Retained.segmentData iface face idx).segments k) (idx.pos j) m

theorem retPos_lt (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small) (j : Fin p') {m : ℕ}
    (hm : m < ((Retained.segmentData iface face idx).segments j).length) :
    retPos iface face idx j m < (rowPieces iface face idx (idx.owner j)).length := by
  refine mapPos_lt _ _ (idx.pos_lt j) ?_
  rw [getElem_carried_pos]
  exact hm

/-- and the piece it names is the prescribed one. -/
theorem getD_rowPieces_retPos
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small) (j : Fin p') {m : ℕ}
    (hm : m < ((Retained.segmentData iface face idx).segments j).length) :
    (rowPieces iface face idx (idx.owner j)).getD (retPos iface face idx j m) 0 =
      ((Retained.segmentData iface face idx).segments j).getD m 0 := by
  have h := getD_flatten_mapPos (idx.carried (idx.owner j))
    (fun k ↦ (Retained.segmentData iface face idx).segments k) 0 (idx.pos_lt j)
    (q := m) (by rw [getElem_carried_pos]; exact hm)
  rw [getElem_carried_pos] at h
  exact h

theorem length_getD_map_carried
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small) (j : Fin p') :
    ((((idx.carried (idx.owner j)).map fun k ↦
        (Retained.segmentData iface face idx).segments k)).getD (idx.pos j) []).length =
      ((Retained.segmentData iface face idx).segments j).length := by
  rw [getD_map_of_lt _ _ (idx.pos_lt j), getElem_carried_pos]

/-- **The prescribed segments of the requested slots are the places along the
retained rows.** -/
def retRowEquiv (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small) :
    (Σ j : Fin p', Fin ((Retained.segmentData iface face idx).segments j).length) ≃
      RowPos iface face idx :=
  Equiv.ofBijective
    (fun x ↦ ⟨idx.owner x.1, ⟨retPos iface face idx x.1 (x.2 : ℕ),
      retPos_lt iface face idx x.1 x.2.isLt⟩⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨by
        rintro ⟨j, m⟩ ⟨j', m'⟩ hEq
        have h1 : idx.owner j = idx.owner j' := congrArg Sigma.fst hEq
        have h2 : retPos iface face idx j (m : ℕ) = retPos iface face idx j' (m' : ℕ) :=
          congrArg (fun z : RowPos iface face idx ↦ ((z.2 : Fin _) : ℕ)) hEq
        rw [retPos, retPos, h1] at h2
        simp only [mapPos] at h2
        have hbj := length_getD_map_carried iface face idx j
        rw [h1] at hbj
        have hbj' := length_getD_map_carried iface face idx j'
        obtain ⟨hpos, hm⟩ := offset_add_inj
          ((idx.carried (idx.owner j')).map fun k ↦
            (Retained.segmentData iface face idx).segments k)
          (by rw [hbj]; exact m.isLt) (by rw [hbj']; exact m'.isLt) h2
        exact sigma_fin_ext ((carriedEquiv idx).injective (sigma_fin_ext h1 hpos)) hm,
        by
          rw [card_rowPos, Fintype.card_sigma]
          simp only [Fintype.card_fin]⟩)

@[simp] theorem retRowEquiv_fst (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (x : Σ j : Fin p', Fin ((Retained.segmentData iface face idx).segments j).length) :
    (retRowEquiv iface face idx x).1 = idx.owner x.1 := rfl

@[simp] theorem retRowEquiv_snd (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small)
    (x : Σ j : Fin p', Fin ((Retained.segmentData iface face idx).segments j).length) :
    ((retRowEquiv iface face idx x).2 : ℕ) = retPos iface face idx x.1 (x.2 : ℕ) := rfl

/-! ## 5.  The cut side: one place per piece of a kept slot -/

theorem length_cutList_row (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small) (i : Fin p) :
    (cutList (positiveLengths iface face i) (cutOffsetAt face idx i)).length =
      (positiveRow iface face i).length := by
  rw [length_cutList, length_positiveLengths]

theorem slotIndex_lt_cutList (idx : RetainedIndex spec F small)
    (x : SlotIndex iface face) :
    (x.2 : ℕ) <
      (cutList (positiveLengths iface face x.1) (cutOffsetAt face idx x.1)).length := by
  rw [length_cutList_row]
  exact x.2.isLt

theorem getElem_cutList (idx : RetainedIndex spec F small) (x : SlotIndex iface face) :
    (cutList (positiveLengths iface face x.1)
        (cutOffsetAt face idx x.1))[(x.2 : ℕ)]'(slotIndex_lt_cutList idx x) =
      pieces iface face idx x :=
  (List.getD_eq_getElem _ _ _).symm

/-- The place along its row of the `t`-th positive piece of the kept slot
`x`. -/
def piecePos (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small) (x : SlotIndex iface face) (t : ℕ) : ℕ :=
  mapPos (cutList (positiveLengths iface face x.1) (cutOffsetAt face idx x.1))
    OrderedPathSplit.positiveSegments (x.2 : ℕ) t

theorem piecePos_lt (idx : RetainedIndex spec F small) (hTwo : CarriesAtMostTwo idx)
    (x : SlotIndex iface face) {t : ℕ}
    (ht : t < (OrderedPathSplit.positiveSegments (pieces iface face idx x)).length) :
    piecePos iface face idx x t < (rowPieces iface face idx (slotRow x)).length := by
  have hbound := mapPos_lt (cutList (positiveLengths iface face x.1)
      (cutOffsetAt face idx x.1)) OrderedPathSplit.positiveSegments
    (slotIndex_lt_cutList idx x) (q := t) (by rw [getElem_cutList]; exact ht)
  rw [rowPieces_eq_cut iface face idx hTwo (slotRow x)]
  exact hbound

theorem getD_rowPieces_piecePos (idx : RetainedIndex spec F small)
    (hTwo : CarriesAtMostTwo idx) (x : SlotIndex iface face) {t : ℕ}
    (ht : t < (OrderedPathSplit.positiveSegments (pieces iface face idx x)).length) :
    (rowPieces iface face idx (slotRow x)).getD (piecePos iface face idx x t) 0 =
      (OrderedPathSplit.positiveSegments (pieces iface face idx x)).getD t 0 := by
  have h := getD_flatten_mapPos (cutList (positiveLengths iface face x.1)
      (cutOffsetAt face idx x.1)) OrderedPathSplit.positiveSegments 0
    (slotIndex_lt_cutList idx x) (q := t) (by rw [getElem_cutList]; exact ht)
  rw [getElem_cutList] at h
  rw [rowPieces_eq_cut iface face idx hTwo (slotRow x)]
  exact h

theorem length_getD_map_cutList (idx : RetainedIndex spec F small)
    (x : SlotIndex iface face) :
    ((((cutList (positiveLengths iface face x.1) (cutOffsetAt face idx x.1)).map
        OrderedPathSplit.positiveSegments)).getD (x.2 : ℕ) []).length =
      (OrderedPathSplit.positiveSegments (pieces iface face idx x)).length := by
  rw [getD_map_of_lt _ _ (slotIndex_lt_cutList idx x), getElem_cutList]

/-- **Two pieces at the same place of the same row are the same piece of the
same kept slot.** -/
theorem piecePos_inj (idx : RetainedIndex spec F small) {x x' : SlotIndex iface face}
    (hrow : x.1 = x'.1) {t t' : ℕ}
    (ht : t < (OrderedPathSplit.positiveSegments (pieces iface face idx x)).length)
    (ht' : t' < (OrderedPathSplit.positiveSegments (pieces iface face idx x')).length)
    (h : piecePos iface face idx x t = piecePos iface face idx x' t') :
    x = x' ∧ t = t' := by
  obtain ⟨i, m⟩ := x
  obtain ⟨i', m'⟩ := x'
  simp only at hrow
  subst hrow
  simp only [piecePos, mapPos] at h
  have hb := length_getD_map_cutList idx (⟨i, m⟩ : SlotIndex iface face)
  have hb' := length_getD_map_cutList idx (⟨i, m'⟩ : SlotIndex iface face)
  obtain ⟨hm, htt⟩ := offset_add_inj
    ((cutList (positiveLengths iface face i) (cutOffsetAt face idx i)).map
      OrderedPathSplit.positiveSegments)
    (by rw [hb]; exact ht) (by rw [hb']; exact ht') h
  exact ⟨sigma_fin_ext rfl hm, htt⟩

end

end DraismaVargas.LocalCases.RetainedRowPieces
