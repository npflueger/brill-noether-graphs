module

public import DraismaVargasCount.BallotStabiliserReduction

@[expose] public section

/-!
# The spine reversal of the caterpillar core, constructed

This module constructs the relabelling in the reversal branch of `hStab` (the
realisation of the relabellings that stabilise a ballot core diagonal; see
`BallotStabiliserReduction`).

## What is constructed

`BallotOrbit.ballotCoreDiag_relabel_eq_self_or_reverse` proves that a relabelling
of `catCore m` either fixes a ballot diagonal or carries it to the diagonal of the
reversed slope sequence.  **`spineReversal m : Relabel (catCore m) (catCore m)`**
attains the second alternative, at every `m`, `m = 0` included.  It is built from
two closed-form involutions of indices and a single incidence computation; no
automorphism table is enumerated and no genus is special-cased.

## The arithmetic, in one paragraph

`catCore m` is the spine `0 – 1 – 3 – 5 – ⋯ – 4m+1` with a self-loop at each
end, a stem `2k+1 – 2k+2` at each interior spine vertex and a self-loop at each
stem tip.  The reversal is `revVtxVal`: `0 ↔ 4m+1`, `2j+1 ↔ 4m-2j-1` on the
interior spine, `2j ↔ 4m+2-2j` on the tips.  On slots it is `revSlotVal`:
`0 ↔ 6m+2` on the two extreme loops, `e ↦ 6m+2-e` on the spine slots
(`e ≡ 1 mod 3`), `e ↦ 6m+1-e` on the stems (`e ≡ 2 mod 3`, `e ≠ 6m+2`) and
`e ↦ 6m+3-e` on the interior loops (`e ≡ 0 mod 3`, `e ≠ 0`).  `rev_ends` is the
whole content: on the spine slots the reversal *exchanges* the two ends of a
slot, on every other slot it preserves them, and `coreIncidence` is a symmetric
sum of the two, so one `Nat.add_comm` absorbs the difference.

`revSlotVal_genusSix` and `revVtxVal_genusSix` check the two involutions at
`m = 2` against the explicit picture of `catCore 2` (§11).

## What is proved

* `revSlotVal`, `revVtxVal`, their bounds and involutivity, and their closed
  forms per residue class (`revSlotVal_three_one` and friends).
* `tailIdx`, `headIdx` -- the two ends of a slot as plain arithmetic, identified
  with `catCore`'s (`catCore_tail_idx`, `catCore_head_idx`).
* **`rev_ends`** -- the two ends, transported, in the `±` form `coreIncidence`
  needs.
* **`spineReversal`** -- the `Relabel`, at every `m`, with `rev_incidence`.
* `spineReversal_vtx_ne` -- it fixes **no** vertex, at any `m`;
  `spineReversal_slot_eq_self_iff` -- it fixes **exactly one** slot, the middle
  spine edge `3m+1`.  Contrast `SlopeRigidity.endSwap`, which fixes every slot
  of index at least four and every vertex but two.
* `spineReversal_ne_refl`, `spineReversal_ne_endSwap` -- it is neither the
  identity nor the end swap, at any `m`.
* **`innerIndex_spineReversal`** -- it lies in the *reversal* branch of
  `BallotStabiliserReduction.innerIndex_id_or_reverse`
  (`innerIndex (spineReversal m) a = 2m-2-a`), and
  `spineReversal_not_identity_branch` -- not in the identity branch, for
  `m ≥ 2`.  So the two branches of `hStab_of_two_branches` are disjoint
  problems: the identity branch is the two end swaps, this is not either.
* `ballotCoreDiag_spineReversal`, **`spineReversal_stabilises_iff`** -- the
  spine reversal stabilises `ballotCoreDiag m s` **iff** `s` is a palindrome.
  The forward half is `BallotStabiliserReduction.reverseSlopes_eq_of_stab`; the
  converse is what makes the reversal branch non-vacuous.
* `comp`, `comp_slot_apply`, **`innerIndex_comp`** -- composition of
  relabellings (`CoreRelabelInvariance` provides only `Relabel.symm`), and
  the fact that `innerIndex` composes contravariantly.
* **`reversal_branch_factor`**, **`reversal_branch_unique`** -- composing with
  the spine reversal is an involution carrying the reversal branch onto the
  identity branch, so (at `m ≥ 2`) the reversal branch is pinned by the *same*
  two bits as `BallotStabiliserReduction.identity_branch_unique`: where `d.slot`
  sends slot `1` and where it sends slot `6m+1`.  With that lemma this gives
  `|Relabel (catCore m) (catCore m)| ≤ 8` at every `m ≥ 2`, in the same sense as
  its bound is stated -- with no automorphism table.
* `cum_add_dn_le_self`, `cum_add_dn`, **`two_cum_succ`** -- the height
  dictionary `2·cum i + 1 = slope i + i` on `1 ≤ i ≤ g-1`.
* **`cum_reflect`** -- the palindrome arithmetic law
  `cum (g-i) + i = cum i + (m+1)`: at a palindrome the sheet block above the
  spine edge `g-i` has the same endpoints as the block above the spine edge `i`
  *translated* by `m+1-i`.  This numeric coincidence does **not** mean the sheet
  layer of `hReversal` is an edge-varying shift: the bijection realising it
  (`BallotSpineReversalSheetIso`) is `mirror m`, the single global reflection
  `k ↦ m+2-k` (fixing sheet `0`), the same permutation at every spine vertex,
  spine edge and end lollipop, corrected only at the bridge pairs by one
  transposition per interior lollipop (`lolliPerm`).  See that module's
  docstring for why a FIFO-queue reading makes the reflection, not a shift, the
  right guess.
* `vertPred_last`, `not_vertPred_zero` -- sheet `m+1` is glued at the far spine
  end `u_g` and not at the root, for **every** `s` and every `m ≥ 1`.
* **`realizes_spineReversal_of_hStab`**, `realizes_spineReversal_of_hReversal`
  -- `hStab` (and its reversal branch) has a concrete named consequence at
  every palindrome.

## Why the palindrome does not make the obligation easy

Compared with the end swap, the `Realizes` obligation for the spine reversal is
**harder**, and the reason is structural rather than incidental.

* *Necessary, not sufficient.*  The palindrome is exactly what makes a sheet
  layer possible at all: the block above the spine edge `i` has `slope i`
  elements, so a permutation carrying it to the block above `g-i` exists only if
  `slope i = slope (g-i)`.  That is already forced by
  `BallotStabiliserReduction.reverseSlopes_eq_of_stab`, so the palindrome buys no
  freedom -- it removes the cases where the obligation is *false*, leaving exactly
  the hard ones.
* *Nothing is fixed.*  `SlopeRigidity.endSwap` moves five target vertices and
  four occurrences and is the identity elsewhere, so
  `BallotEndSwapSheetIso.bEndSwapDatumIso` can take the identity sheet permutation
  at every other vertex, and has one `compatible` obligation to check.  The spine
  reversal fixes **no** vertex (`spineReversal_vtx_ne`) and exactly **one** slot
  (`spineReversal_slot_eq_self_iff`), so every one of the `6m+4` `vertexPerm`s
  and `6m+3` `edgePerm`s is in play and every one of the `2(6m+3)` incident
  pairs carries a `compatible` obligation -- `30` at genus six, against one.
* *The permutation is not the identity.*  `vertPred_last` and `not_vertPred_zero`
  show that the identity is unavailable already at the root, with no slope
  sequence named.  The block arithmetic of `cum_reflect` might suggest that the
  block over spine edge `i` must be shifted by `m+1-i`, an edge-varying shift.  It
  need not: the sheet family that works (`BallotSpineReversalSheetIso`) is
  `mirror m`, the single global reflection `k ↦ m+2-k` fixing sheet `0`, the
  *same* permutation at every spine vertex, spine edge, and end lollipop -- every
  `compatible` obligation among those is free.  Only the bridge pairs at interior
  lollipops break the global reflection, and there the fix is one transposition
  per interior lollipop (`lolliPerm`), not an edge-by-edge change.

So `hReversal` needs a `GeometricDatumIso` whose sheet family is one global
reflection plus one transposition per interior lollipop.
`BallotSpineReversalSheetIso` builds it, and proves `hReversal` and `hStab` at
genus six.

## What is NOT proved here (every hypothesis, explicitly)

* **`hReversal` is not proved by this file.**  Nothing here inhabits
  `SlopeRigidity.Realizes (spineReversal m) _` at any `m` or any `s`.
  `realizes_spineReversal_of_hStab` and `realizes_spineReversal_of_hReversal`
  *consume* the hypothesis; they do not supply it.  It is proved at
  genus six by `BallotSpineReversalSheetIso.hReversal_genusSix` and
  `BallotSpineReversalSheetIso.hStab_genusSix`; at every other `m` nothing here
  proves it.
* **No `GeometricDatumIso` is built.**  §8--§9 establish the shift law and one
  obstruction; they do not construct `vertexPerm`, `edgePerm`, `targetVertex`,
  `targetEdge`, `ends`, or check a single `compatible` obligation.
* **The tree-level reading of the reversal is not constructed here.**  There is
  no `catTree`-level `Equiv` here matching `SlopeRigidity.endSwapTgtEquiv` (that
  is `BallotSpineReversalSheetIso.revTgtEquiv`); `vertPred_last` and
  `not_vertPred_zero` are stated at the two vertex *indices* `6m+2` and `0`,
  which `revVtxVal_branchIdx_zero` records the reversal exchanges at the core
  level.
* **`Aut (catCore m)` is not enumerated**, and no `Fintype` or
  cardinality statement about it is proved here (a computer enumeration, not
  part of this library, gives `|Aut (catCore m)| = 8` for `1 ≤ m ≤ 5`).  What
  `reversal_branch_unique` gives is a *rigidity* statement in the shape of
  `BallotStabiliserReduction.identity_branch_unique` -- two elements of the
  branch agreeing on two named slots are equal -- not a count; the literal
  cardinality `≤ 4` per branch is not proved.  The relabellings with a nontrivial
  far bit are constructed in `BallotFarEndSwap`.
* **The far end swap is not treated here** (see `BallotFarEndSwap`);
  `spineReversal_not_identity_branch` shows that the spine reversal is not one
  of the end swaps.
* **`m ≥ 1` is used in `not_vertPred_zero`** (at `m = 0` the two ends
  carry the same two sheets) and `m ≥ 2` in
  `spineReversal_not_identity_branch`.  Everything else is at every `m`.
* **Nothing about `hSep`, `hSpine` or `hSupply`.**
* No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`, no
  `#eval`.  Two `decide`s, in the genus-six sanity checks of §11.
-/

namespace DraismaVargas.Count.SpineReversal

open DraismaVargas.Count
open DraismaVargas.Count.CoreRelabel
open DraismaVargas.Count.FibreCaterpillar
open DraismaVargas.Count.BallotOrbit
open DraismaVargas.Count.BallotDatum
open DraismaVargas.Infrastructure.CaterpillarTree (lolli)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Infrastructure.CaterpillarTree (parentIndex)
open DraismaVargas.LocalCases.CaterpillarPruning (IsLeafEdge)

/-! ## 1.  The two involutions of indices -/

def revSlotVal (m e : ℕ) : ℕ :=
  if e = 0 then 6 * m + 2
  else if e = 6 * m + 2 then 0
  else if e % 3 = 1 then 6 * m + 2 - e
  else if e % 3 = 2 then 6 * m + 1 - e
  else 6 * m + 3 - e

def revVtxVal (m x : ℕ) : ℕ :=
  if x = 0 then 4 * m + 1
  else if x = 4 * m + 1 then 0
  else if x % 2 = 1 then 4 * m - x
  else 4 * m + 2 - x

theorem revSlotVal_lt {m e : ℕ} (he : e < 6 * m + 3) : revSlotVal m e < 6 * m + 3 := by
  unfold revSlotVal; split_ifs <;> omega

theorem revVtxVal_lt {m x : ℕ} (hx : x < 4 * m + 2) : revVtxVal m x < 4 * m + 2 := by
  unfold revVtxVal; split_ifs <;> omega

theorem revSlotVal_rev {m e : ℕ} (he : e < 6 * m + 3) :
    revSlotVal m (revSlotVal m e) = e := by
  unfold revSlotVal; split_ifs <;> first | omega | exact ((by assumption : False)).elim

theorem revVtxVal_rev {m x : ℕ} (hx : x < 4 * m + 2) :
    revVtxVal m (revVtxVal m x) = x := by
  unfold revVtxVal; split_ifs <;> first | omega | exact ((by assumption : False)).elim

/-! ## 2.  The two ends of a slot, arithmetically -/

def tailIdx (e : ℕ) : ℕ := branchIdx (parentIndex (e + 1))

def headIdx (m e : ℕ) : ℕ :=
  if e % 3 = 0 ∨ e = 6 * m + 2 then branchIdx (parentIndex (e + 1)) else branchIdx (e + 1)

-- closed forms for tailIdx
theorem tailIdx_eq (e : ℕ) : tailIdx e = 2 * (if e % 3 = 1 then e - 2 else e) / 3 := by
  unfold tailIdx branchIdx parentIndex; split_ifs <;> omega

theorem headIdx_eq (m e : ℕ) :
    headIdx m e = if e % 3 = 0 ∨ e = 6 * m + 2 then tailIdx e else 2 * (e + 1) / 3 := by
  unfold headIdx tailIdx branchIdx; split_ifs <;> omega

theorem tailIdx_three (k : ℕ) : tailIdx (3 * k) = 2 * k := by
  rw [tailIdx_eq, ite_eq_right (by omega)]; omega

theorem tailIdx_three_one (k : ℕ) : tailIdx (3 * k + 1) = 2 * k - 1 := by
  rw [tailIdx_eq, ite_eq_left (by omega)]; omega

theorem tailIdx_three_two (k : ℕ) : tailIdx (3 * k + 2) = 2 * k + 1 := by
  rw [tailIdx_eq, ite_eq_right (by omega)]; omega

theorem headIdx_three (m k : ℕ) : headIdx m (3 * k) = 2 * k := by
  rw [headIdx_eq, ite_eq_left (Or.inl (by omega)), tailIdx_three]

theorem headIdx_three_one (m k : ℕ) : headIdx m (3 * k + 1) = 2 * k + 1 := by
  rw [headIdx_eq, ite_eq_right (by rintro (h | h) <;> omega)]; omega

theorem headIdx_three_two (m k : ℕ) (h : 3 * k + 2 ≠ 6 * m + 2) :
    headIdx m (3 * k + 2) = 2 * k + 2 := by
  rw [headIdx_eq, ite_eq_right (by rintro (h' | h') <;> omega)]; omega

theorem tailIdx_zero : tailIdx 0 = 0 := by
  rw [tailIdx_eq, ite_eq_right (by omega)]

theorem headIdx_zero (m : ℕ) : headIdx m 0 = 0 := by
  rw [headIdx_eq, ite_eq_left (Or.inl (by omega)), tailIdx_zero]

theorem tailIdx_last (m : ℕ) : tailIdx (6 * m + 2) = 4 * m + 1 := by
  rw [tailIdx_eq, ite_eq_right (by omega)]; omega

theorem headIdx_last (m : ℕ) : headIdx m (6 * m + 2) = 4 * m + 1 := by
  rw [headIdx_eq, ite_eq_left (Or.inr rfl), tailIdx_last]

/-! revSlotVal closed forms -/

theorem revSlotVal_zero (m : ℕ) : revSlotVal m 0 = 6 * m + 2 := by
  unfold revSlotVal; rw [ite_eq_left rfl]

theorem revSlotVal_last (m : ℕ) : revSlotVal m (6 * m + 2) = 0 := by
  unfold revSlotVal; rw [ite_eq_right (by omega), ite_eq_left rfl]

theorem revSlotVal_three_one (m k : ℕ) (hk : k ≤ 2 * m) :
    revSlotVal m (3 * k + 1) = 3 * (2 * m - k) + 1 := by
  unfold revSlotVal; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]; omega

theorem revSlotVal_three_two (m k : ℕ) (hk : k < 2 * m) :
    revSlotVal m (3 * k + 2) = 3 * (2 * m - 1 - k) + 2 := by
  unfold revSlotVal
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]; omega

theorem revSlotVal_three (m k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ 2 * m) :
    revSlotVal m (3 * k) = 3 * (2 * m + 1 - k) := by
  unfold revSlotVal
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]; omega

/-! revVtxVal closed forms -/

theorem revVtxVal_odd (m j : ℕ) (hj : j < 2 * m) : revVtxVal m (2 * j + 1) = 4 * m - 2 * j - 1 := by
  unfold revVtxVal; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]; omega

theorem revVtxVal_even (m j : ℕ) (h1 : 1 ≤ j) :
    revVtxVal m (2 * j) = 4 * m + 2 - 2 * j := by
  unfold revVtxVal; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem revVtxVal_zero (m : ℕ) : revVtxVal m 0 = 4 * m + 1 := by
  unfold revVtxVal; rw [ite_eq_left rfl]

theorem revVtxVal_top (m : ℕ) : revVtxVal m (4 * m + 1) = 0 := by
  unfold revVtxVal; rw [ite_eq_right (by omega), ite_eq_left rfl]

/-! The two ends, transported -/

theorem rev_ends (m e : ℕ) (he : e < 6 * m + 3) :
    (tailIdx (revSlotVal m e) = revVtxVal m (tailIdx e) ∧
        headIdx m (revSlotVal m e) = revVtxVal m (headIdx m e)) ∨
      (tailIdx (revSlotVal m e) = revVtxVal m (headIdx m e) ∧
        headIdx m (revSlotVal m e) = revVtxVal m (tailIdx e)) := by
  rcases (show e % 3 = 0 ∨ e % 3 = 1 ∨ e % 3 = 2 by omega) with h | h | h
  · obtain ⟨k, rfl⟩ : ∃ k, e = 3 * k := ⟨e / 3, by omega⟩
    left
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [show 3 * 0 = 0 from by omega, revSlotVal_zero, tailIdx_last, headIdx_last,
        tailIdx_zero, headIdx_zero, revVtxVal_zero]
      exact ⟨rfl, rfl⟩
    · rw [revSlotVal_three m k hk (by omega)]
      simp only [tailIdx_three, headIdx_three]
      rw [revVtxVal_even m k hk]
      omega
  · obtain ⟨k, rfl⟩ : ∃ k, e = 3 * k + 1 := ⟨e / 3, by omega⟩
    right
    have hkle : k ≤ 2 * m := by omega
    have h5 : revVtxVal m (2 * k + 1) = 2 * (2 * m - k) - 1 := by
      rcases (show k = 2 * m ∨ k < 2 * m from by omega) with rfl | hk2
      · rw [show 2 * (2 * m) + 1 = 4 * m + 1 from by ring, revVtxVal_top]; omega
      · rw [revVtxVal_odd m k hk2]; omega
    have h6 : revVtxVal m (2 * k - 1) = 2 * (2 * m - k) + 1 := by
      rcases Nat.eq_zero_or_pos k with rfl | hk1
      · rw [show 2 * 0 - 1 = 0 from by omega, revVtxVal_zero]; omega
      · rw [show 2 * k - 1 = 2 * (k - 1) + 1 from by omega, revVtxVal_odd m (k - 1) (by omega)]
        omega
    rw [revSlotVal_three_one m k hkle]
    simp only [tailIdx_three_one, headIdx_three_one]
    rw [h5, h6]
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, e = 3 * k + 2 := ⟨e / 3, by omega⟩
    left
    rcases (show k = 2 * m ∨ k < 2 * m from by omega) with rfl | hk
    · rw [show 3 * (2 * m) + 2 = 6 * m + 2 from by ring, revSlotVal_last, tailIdx_last,
        headIdx_last, tailIdx_zero, headIdx_zero, revVtxVal_top]
      exact ⟨rfl, rfl⟩
    · rw [revSlotVal_three_two m k hk]
      simp only [tailIdx_three_two]
      rw [headIdx_three_two m (2 * m - 1 - k) (by omega), headIdx_three_two m k (by omega),
        revVtxVal_odd m k hk, show 2 * k + 2 = 2 * (k + 1) from by ring,
        revVtxVal_even m (k + 1) (by omega)]
      omega

/-! ## 3.  The two ends of a slot of `catCore m`, read off arithmetically -/

theorem catCore_tail_idx (m : ℕ) (e : Fin (6 * m + 3)) :
    ((catCore m).tail e).val = tailIdx e.val :=
  SlopeRigidity.catCore_tail_val m e

theorem catCore_head_idx (m : ℕ) (e : Fin (6 * m + 3)) :
    ((catCore m).head e).val = headIdx m e.val := by
  rw [SlopeRigidity.catCore_head_val]
  by_cases hleaf : IsLeafEdge m e
  · rw [catHeadVal, ite_eq_left hleaf, headIdx, ite_eq_left (by exact hleaf)]
  · rw [catHeadVal, ite_eq_right hleaf, headIdx, ite_eq_right (by exact hleaf)]

theorem tailIdx_lt (m : ℕ) (e : Fin (6 * m + 3)) : tailIdx e.val < 4 * m + 2 := by
  rw [← catCore_tail_idx m e]; exact ((catCore m).tail e).isLt

theorem headIdx_lt (m : ℕ) (e : Fin (6 * m + 3)) : headIdx m e.val < 4 * m + 2 := by
  rw [← catCore_head_idx m e]; exact ((catCore m).head e).isLt

theorem revVtxVal_inj {m a b : ℕ} (ha : a < 4 * m + 2) (hb : b < 4 * m + 2)
    (h : revVtxVal m a = revVtxVal m b) : a = b := by
  rw [← revVtxVal_rev ha, ← revVtxVal_rev hb, h]

/-! ## 4.  The relabelling -/

/-- The slot component of the spine reversal. -/
def revSlot (m : ℕ) (e : Fin (6 * m + 3)) : Fin (6 * m + 3) :=
  ⟨revSlotVal m e.val, revSlotVal_lt e.isLt⟩

/-- The vertex component of the spine reversal. -/
def revVtx (m : ℕ) (v : Fin (4 * m + 2)) : Fin (4 * m + 2) :=
  ⟨revVtxVal m v.val, revVtxVal_lt v.isLt⟩

@[simp] theorem revSlot_val (m : ℕ) (e : Fin (6 * m + 3)) :
    (revSlot m e).val = revSlotVal m e.val := rfl

@[simp] theorem revVtx_val (m : ℕ) (v : Fin (4 * m + 2)) :
    (revVtx m v).val = revVtxVal m v.val := rfl

theorem revSlot_involutive (m : ℕ) : Function.Involutive (revSlot m) :=
  fun e ↦ Fin.ext (revSlotVal_rev e.isLt)

theorem revVtx_involutive (m : ℕ) : Function.Involutive (revVtx m) :=
  fun v ↦ Fin.ext (revVtxVal_rev v.isLt)

theorem rev_incidence (m : ℕ) (v : Fin (4 * m + 2)) (e : Fin (6 * m + 3)) :
    coreIncidence (catCore m) (revVtx m v) (revSlot m e) = coreIncidence (catCore m) v e := by
  rw [coreIncidence, coreIncidence]
  have hTL : ((catCore m).tail (revSlot m e)).val = tailIdx (revSlotVal m e.val) :=
    catCore_tail_idx m (revSlot m e)
  have hHL : ((catCore m).head (revSlot m e)).val = headIdx m (revSlotVal m e.val) :=
    catCore_head_idx m (revSlot m e)
  have hTR : ((catCore m).tail e).val = tailIdx e.val := catCore_tail_idx m e
  have hHR : ((catCore m).head e).val = headIdx m e.val := catCore_head_idx m e
  have key : ∀ a b : ℕ, a < 4 * m + 2 → b < 4 * m + 2 →
      ((revVtxVal m a = revVtxVal m b) ↔ (a = b)) := by
    intro a b ha hb
    exact ⟨revVtxVal_inj ha hb, fun h ↦ by rw [h]⟩
  simp only [Fin.ext_iff, hTL, hHL, hTR, hHR, revVtx_val]
  rcases rev_ends m e.val e.isLt with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    exact congrArg₂ (· + ·)
      (if_congr (key _ _ (tailIdx_lt m e) v.isLt) rfl rfl)
      (if_congr (key _ _ (headIdx_lt m e) v.isLt) rfl rfl)
  · rw [h1, h2, Nat.add_comm ((if tailIdx e.val = v.val then 1 else 0))]
    exact congrArg₂ (· + ·)
      (if_congr (key _ _ (headIdx_lt m e) v.isLt) rfl rfl)
      (if_congr (key _ _ (tailIdx_lt m e) v.isLt) rfl rfl)

/-- **The spine reversal of the caterpillar core**, at every `m`: the global
order-reversing symmetry of the caterpillar. -/
def spineReversal (m : ℕ) : Relabel (catCore m) (catCore m) where
  slot := (revSlot_involutive m).toPerm _
  vtx := (revVtx_involutive m).toPerm _
  incidence := rev_incidence m

@[simp] theorem spineReversal_slot_apply (m : ℕ) (e : Fin (6 * m + 3)) :
    (spineReversal m).slot e = revSlot m e := rfl

@[simp] theorem spineReversal_slot_symm_apply (m : ℕ) (e : Fin (6 * m + 3)) :
    (spineReversal m).slot.symm e = revSlot m e := rfl

@[simp] theorem spineReversal_vtx_apply (m : ℕ) (v : Fin (4 * m + 2)) :
    (spineReversal m).vtx v = revVtx m v := rfl

/-! ## 5.  What the spine reversal moves -/

/-- **The spine reversal fixes no vertex**, at any `m`.  Contrast
`SlopeRigidity.endSwap`, which fixes every vertex but `0` and `2`. -/
theorem revVtxVal_ne_self {m x : ℕ} (hx : x < 4 * m + 2) : revVtxVal m x ≠ x := by
  unfold revVtxVal; split_ifs <;> omega

theorem spineReversal_vtx_ne (m : ℕ) (v : Fin (4 * m + 2)) : (spineReversal m).vtx v ≠ v :=
  fun h ↦ revVtxVal_ne_self v.isLt (congrArg Fin.val h)

/-- **The spine reversal fixes exactly one slot**, the middle spine edge `3m+1`.
Contrast `SlopeRigidity.endSwap_slot_of_four_le`, which fixes every slot of index
at least four. -/
theorem revSlotVal_eq_self_iff {m e : ℕ} (he : e < 6 * m + 3) :
    revSlotVal m e = e ↔ e = 3 * m + 1 := by
  unfold revSlotVal; split_ifs <;> omega

theorem spineReversal_slot_eq_self_iff (m : ℕ) (e : Fin (6 * m + 3)) :
    (spineReversal m).slot e = e ↔ e.val = 3 * m + 1 := by
  rw [spineReversal_slot_apply, Fin.ext_iff, revSlot_val]
  exact revSlotVal_eq_self_iff e.isLt

/-- **The spine reversal is not the identity relabelling**, at any `m`. -/
theorem spineReversal_ne_refl (m : ℕ) : ¬ ∀ e, (spineReversal m).slot e = e := by
  intro h
  have h0 := (spineReversal_slot_eq_self_iff m ⟨0, by omega⟩).mp (h _)
  simp only at h0
  omega

/-- **The spine reversal is not the end swap**, at any `m`: they disagree on
slot `0`, which the end swap sends to `3` and the reversal to `6m+8`. -/
theorem spineReversal_ne_endSwap (m : ℕ) :
    (spineReversal (m + 1)).slot ⟨0, by omega⟩ ≠ (SlopeRigidity.endSwap m).slot ⟨0, by omega⟩ := by
  intro h
  have := congrArg Fin.val h
  rw [SlopeRigidity.endSwap_slot_zero] at this
  simp only [spineReversal_slot_apply, revSlot_val] at this
  rw [revSlotVal_zero] at this
  omega

/-! ## 6.  The spine reversal lies in the reversal branch -/

/-- **The index dichotomy of `BallotStabiliserReduction.innerIndex_id_or_reverse`, decided for
the spine reversal**: it reverses the interior spine slots. -/
theorem innerIndex_spineReversal (m : ℕ) {k : ℕ} (hk : k < 2 * m - 1) :
    innerIndex (spineReversal m) k = 2 * m - 2 - k := by
  rw [innerIndex_eq (spineReversal m) hk, spineReversal_slot_symm_apply, revSlot_val,
    innerSlot_val, show 3 * k + 4 = 3 * (k + 1) + 1 from by ring,
    revSlotVal_three_one m (k + 1) (by omega)]
  omega

theorem spineReversal_reverse_branch (m : ℕ) :
    ∀ a, a < 2 * m - 1 → innerIndex (spineReversal m) a = 2 * m - 2 - a :=
  fun _ ha ↦ innerIndex_spineReversal m ha

/-- **And it is not in the identity branch**, as soon as `m ≥ 2`.  So the two
branches of `BallotStabiliserReduction.hStab_of_two_branches` are genuinely
different problems: the identity branch is `SlopeRigidity.endSwap` and the far
end swap, and this is not either of them. -/
theorem spineReversal_not_identity_branch (m : ℕ) (hm : 2 ≤ m) :
    ¬ ∀ a, a < 2 * m - 1 → innerIndex (spineReversal m) a = a := by
  intro h
  have h0 := h 0 (by omega)
  rw [innerIndex_spineReversal m (show (0 : ℕ) < 2 * m - 1 from by omega)] at h0
  omega

/-! ## 7.  The stabiliser condition: exactly the palindromes -/

/-- **The spine reversal carries every ballot diagonal to the reversed one.**
This is `BallotStabiliserReduction.ballotCoreDiag_of_reverse_branch` at the
spine reversal. -/
theorem ballotCoreDiag_spineReversal (m : ℕ) (s : Slopes (2 * (m + 1))) :
    (fun slot ↦ BallotSlopes.ballotCoreDiag m s ((spineReversal m).slot.symm slot)) =
      BallotSlopes.ballotCoreDiag m (reverseSlopes s) :=
  BallotStabiliserReduction.ballotCoreDiag_of_reverse_branch m s (spineReversal m)
    (spineReversal_reverse_branch m)

/-- **The spine reversal stabilises `ballotCoreDiag m s` exactly when `s` is a
palindrome.**  The forward direction is
`BallotStabiliserReduction.reverseSlopes_eq_of_stab`; the converse is what makes
the reversal branch of `hStab_of_two_branches` non-vacuous. -/
theorem spineReversal_stabilises_iff (m : ℕ) (s : Slopes (2 * (m + 1))) :
    (∀ slot, BallotSlopes.ballotCoreDiag m s ((spineReversal m).slot.symm slot) =
        BallotSlopes.ballotCoreDiag m s slot) ↔ reverseSlopes s = s := by
  constructor
  · intro h
    exact BallotStabiliserReduction.reverseSlopes_eq_of_stab m s (spineReversal m)
      (spineReversal_reverse_branch m) h
  · intro hs slot
    have h := congrFun (ballotCoreDiag_spineReversal m s) slot
    rw [h, hs]

/-! ## 7a.  Composition, and the reversal branch as a coset -/

/-- **Composition of relabellings.**  `CoreRelabelInvariance` gives
`Relabel.symm` but no composition; this is it.  `comp d d'` does `d` first. -/
def comp {n p : ℕ} {c : Core n p} (d d' : Relabel c c) : Relabel c c where
  slot := d.slot.trans d'.slot
  vtx := d.vtx.trans d'.vtx
  incidence v e := (d'.incidence (d.vtx v) (d.slot e)).trans (d.incidence v e)

@[simp] theorem comp_slot_apply {n p : ℕ} {c : Core n p} (d d' : Relabel c c)
    (e : Fin p) : (comp d d').slot e = d'.slot (d.slot e) := rfl

@[simp] theorem comp_slot_symm_apply {n p : ℕ} {c : Core n p} (d d' : Relabel c c)
    (e : Fin p) : (comp d d').slot.symm e = d.slot.symm (d'.slot.symm e) := rfl

@[simp] theorem comp_vtx_apply {n p : ℕ} {c : Core n p} (d d' : Relabel c c)
    (v : Fin n) : (comp d d').vtx v = d'.vtx (d.vtx v) := rfl

/-- **The index map is contravariantly multiplicative.**  `innerIndex` is read
through `slot.symm`, so it composes in the order `d ∘ d'`. -/
theorem innerIndex_comp (m : ℕ) (d d' : Relabel (catCore m) (catCore m)) {k : ℕ}
    (hk : k < 2 * m - 1) :
    innerIndex (comp d d') k = innerIndex d (innerIndex d' k) := by
  rw [innerIndex_eq (comp d d') hk, comp_slot_symm_apply, innerSlot_symm d' hk,
    innerSlot_symm d (innerIndex_spec d' hk).1, innerSlot_val]
  omega

theorem revSlotVal_one (m : ℕ) : revSlotVal m 1 = 6 * m + 1 := by
  unfold revSlotVal; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]; omega

theorem revSlotVal_far (m : ℕ) : revSlotVal m (6 * m + 1) = 1 := by
  unfold revSlotVal; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]; omega

/-- **The reversal branch is `spineReversal` times the identity branch.**
Composing with the reversal on the left carries the reversal branch into the
identity branch, and doing it twice is the identity. -/
theorem reversal_branch_factor (m : ℕ) (d : Relabel (catCore m) (catCore m))
    (hrev : ∀ a, a < 2 * m - 1 → innerIndex d a = 2 * m - 2 - a) :
    (∀ a, a < 2 * m - 1 → innerIndex (comp (spineReversal m) d) a = a) ∧
      comp (spineReversal m) (comp (spineReversal m) d) = d := by
  refine ⟨fun a ha ↦ ?_, ?_⟩
  · rw [innerIndex_comp m (spineReversal m) d ha, hrev a ha,
      innerIndex_spineReversal m (show 2 * m - 2 - a < 2 * m - 1 from by omega)]
    omega
  · refine BallotStabiliserReduction.relabel_ext ?_ ?_
    · exact Equiv.ext fun e ↦ by
        simp only [comp_slot_apply, spineReversal_slot_apply]
        rw [revSlot_involutive m e]
    · exact Equiv.ext fun v ↦ by
        simp only [comp_vtx_apply, spineReversal_vtx_apply]
        rw [revVtx_involutive m v]

/-- **The reversal branch has at most four elements**, and they are pinned by
the *same* two bits that pin the identity branch in
`BallotStabiliserReduction.identity_branch_unique`: where `d.slot` sends the
near spine slot `1` and where it sends the far spine slot `6m+1`.  So
`hReversal` is, like `hFar`, a statement about a bounded and explicitly indexed
set of relabellings, not about an unenumerated group. -/
theorem reversal_branch_unique {m : ℕ} (hm : 2 ≤ m) (d d' : Relabel (catCore m) (catCore m))
    (hrev : ∀ a, a < 2 * m - 1 → innerIndex d a = 2 * m - 2 - a)
    (hrev' : ∀ a, a < 2 * m - 1 → innerIndex d' a = 2 * m - 2 - a)
    (hnear : ∀ e : Fin (6 * m + 3), e.val = 1 → (d.slot e).val = (d'.slot e).val)
    (hfar : ∀ e : Fin (6 * m + 3), e.val = 6 * m + 1 → (d.slot e).val = (d'.slot e).val) :
    d = d' := by
  obtain ⟨hid, hback⟩ := reversal_branch_factor m d hrev
  obtain ⟨hid', hback'⟩ := reversal_branch_factor m d' hrev'
  have hstep : comp (spineReversal m) d = comp (spineReversal m) d' := by
    refine BallotStabiliserReduction.identity_branch_unique hm _ _ hid hid' ?_ ?_
    · intro e he
      have hE : (spineReversal m).slot e = (⟨6 * m + 1, by omega⟩ : Fin (6 * m + 3)) :=
        Fin.ext (by rw [spineReversal_slot_apply, revSlot_val, he, revSlotVal_one])
      simp only [comp_slot_apply, hE]
      exact hfar _ rfl
    · intro e he
      have hE : (spineReversal m).slot e = (⟨1, by omega⟩ : Fin (6 * m + 3)) :=
        Fin.ext (by rw [spineReversal_slot_apply, revSlot_val, he, revSlotVal_far])
      simp only [comp_slot_apply, hE]
      exact hnear _ rfl
  rw [← hback, ← hback', hstep]

/-! ## 8.  The sheet layer: the height dictionary and the palindrome shift law -/

section Sheets

variable {g : ℕ}

/-- Past index `0` the counters together grow by at most one per index, and the
step at index `1` is a stay (`slope 0 = slope 1`), so `cum i + dn i ≤ i`.  This
is the missing half of `Slopes.cum_add_dn_le`, which only gives `≤ 1 + i`. -/
theorem cum_add_dn_le_self (s : Slopes g) : ∀ i : ℕ, 1 ≤ i → s.cum i + s.dn i ≤ i := by
  intro i
  induction i with
  | zero => omega
  | succ i ih =>
    intro _
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [Slopes.cum_succ, Slopes.dn_succ, Slopes.cum_zero, Slopes.dn_zero,
        ite_eq_right (show ¬ (s.slope (0 + 1) = s.slope 0 + 1) by
          rw [show (0 : ℕ) + 1 = 1 from rfl, Slopes.slope_zero]; omega),
        ite_eq_right (show ¬ (s.slope 0 = s.slope (0 + 1) + 1) by
          rw [show (0 : ℕ) + 1 = 1 from rfl, Slopes.slope_zero]; omega)]
    · have := ih hi
      rw [Slopes.cum_succ, Slopes.dn_succ]
      split_ifs <;> omega

/-- **Every index in range contributes exactly one step**: `cum i + dn i = i` for
`1 ≤ i ≤ g-1`.  `Slopes.le_cum_add_dn` is the other inequality. -/
theorem cum_add_dn (s : Slopes g) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ g - 1) :
    s.cum i + s.dn i = i := by
  have hle := cum_add_dn_le_self s i h1
  have hge := Slopes.le_cum_add_dn s (i - 1) (by omega)
  rw [show i - 1 + 1 = i from by omega] at hge
  omega

/-- **The height dictionary**: `2·cum i + 1 = slope i + i`, i.e.
`cum i = (slope i + i - 1)/2`, on `1 ≤ i ≤ g-1`.  So the newest sheet label above
the spine edge `i` is determined by the slope there and the index. -/
theorem two_cum_succ (s : Slopes g) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ g - 1) :
    2 * s.cum i + 1 = s.slope i + i := by
  have hbal := Slopes.balance s i
  have hsum := cum_add_dn s h1 h2
  omega

/-- **The palindrome arithmetic law.**  If `s` is a palindrome then the newest
label above the spine edge `g-i` is the newest label above the spine edge `i`
shifted by `m+1-i`.  Since the block above the spine edge `i` is
`{0} ∪ [cum i - slope i + 2, cum i]` and the two slopes agree, the two blocks
have the same endpoints under this translation — but that numeric coincidence
is **not** what the sheet permutation of a `hReversal` `GeometricDatumIso`
realises: the bijection is the single global reflection `k ↦ m+2-k`
(`BallotSpineReversalSheetIso.spineMem_reflect`), the same at every edge,
corrected only at the bridge pairs of interior lollipops. -/
theorem cum_reflect {m : ℕ} (s : Slopes (2 * (m + 1))) (hs : reverseSlopes s = s)
    {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ 2 * (m + 1) - 1) :
    s.cum (2 * (m + 1) - i) + i = s.cum i + (m + 1) := by
  have hslope : s.slope i = s.slope (2 * (m + 1) - i) := by
    conv_lhs => rw [← hs]
    exact slope_reverseSlopes s h1 h2
  have hA := two_cum_succ s h1 h2
  have hB := two_cum_succ s (i := 2 * (m + 1) - i) (by omega) (by omega)
  omega

/-- Sheet `m+1` -- the newest label there is -- is glued at the far spine end
`u_g`, the target vertex of index `6m+2`.  It lies in the block above the last
spine edge, whose newest label is `m+1` by `Slopes.cum_last`. -/
theorem vertPred_last (m : ℕ) (s : Slopes (2 * (m + 1))) :
    VertPred m s (6 * m + 2) (m + 1) := by
  rw [vertPred_junction s (show (6 * m + 2) % 3 = 2 from by omega)]
  refine Or.inl ?_
  have hl : lolli (6 * m + 2) = 2 * m + 2 := by unfold lolli; omega
  rw [hl]
  have hcum : s.cum (2 * (m + 1) - 1) = m + 1 := Slopes.cum_last s rfl
  have hslope : s.slope (2 * (m + 1) - 1) = 2 := Slopes.slope_of_ge s (le_refl _)
  rw [show 2 * m + 2 - 1 = 2 * (m + 1) - 1 from by omega]
  exact Or.inr ⟨by omega, by omega⟩

/-- Sheet `m+1` is **not** glued at the root, whose block is the bridge pair
`{0, cum 1} = {0, 1}` of the first lollipop -- as soon as `m ≥ 1`. -/
theorem not_vertPred_zero (m : ℕ) (hm : 1 ≤ m) (s : Slopes (2 * (m + 1))) :
    ¬ VertPred m s 0 (m + 1) := by
  rw [vertPred_pair s (show (0 : ℕ) % 3 ≠ 2 from by omega)]
  have hl : lolli 0 = 1 := by unfold lolli; omega
  rw [hl]
  rintro (h | h)
  · omega
  · rw [Slopes.cum_one] at h; omega

end Sheets

/-! ## 9.  The sheet layer: why the identity sheet permutation is unavailable -/

/-- The core-vertex index of the root of `catTree m` is `0`, that of the far
spine end `u_g` is `4m+1`, and the spine reversal exchanges them. -/
theorem revVtxVal_branchIdx_zero (m : ℕ) :
    revVtxVal m (branchIdx 0) = branchIdx (6 * m + 2) := by
  rw [show branchIdx 0 = 0 from by unfold branchIdx; omega,
    show branchIdx (6 * m + 2) = 4 * m + 1 from by unfold branchIdx; omega, revVtxVal_zero]

/-! ## 10.  What `hStab` demands, named -/

/-- **The obligation, named.**  `hStab` (the third residue of
`DiagonalClassificationGenusSix.diagonalClassification_of_residues`) has a
concrete consequence at every palindromic slope sequence: the spine reversal must
be realised inside the ballot member's gluing datum.  So the reversal branch of
`BallotStabiliserReduction.hStab_of_two_branches` contains a relabelling. -/
theorem realizes_spineReversal_of_hStab (m : ℕ) (request : Fin (6 * m + 3) → ℚ)
    (hStab : ∀ (s : Slopes (2 * (m + 1))) (d : Relabel (catCore m) (catCore m)),
      (∀ slot, BallotSlopes.ballotCoreDiag m s (d.slot.symm slot) =
          BallotSlopes.ballotCoreDiag m s slot) →
        SlopeRigidity.Realizes d (BallotCoreIdentification.ballotFamilyMember m request s))
    (s : Slopes (2 * (m + 1))) (hs : reverseSlopes s = s) :
    SlopeRigidity.Realizes (spineReversal m)
      (BallotCoreIdentification.ballotFamilyMember m request s) :=
  hStab s (spineReversal m) ((spineReversal_stabilises_iff m s).mpr hs)

/-- The same, read on the reversal branch of `hStab_of_two_branches`: that
branch is **non-vacuous** at every palindrome. -/
theorem realizes_spineReversal_of_hReversal (m : ℕ) (request : Fin (6 * m + 3) → ℚ)
    (hReversal : ∀ (s : Slopes (2 * (m + 1))) (d : Relabel (catCore m) (catCore m)),
      (∀ a, a < 2 * m - 1 → innerIndex d a = 2 * m - 2 - a) → reverseSlopes s = s →
        SlopeRigidity.Realizes d (BallotCoreIdentification.ballotFamilyMember m request s))
    (s : Slopes (2 * (m + 1))) (hs : reverseSlopes s = s) :
    SlopeRigidity.Realizes (spineReversal m)
      (BallotCoreIdentification.ballotFamilyMember m request s) :=
  hReversal s (spineReversal m) (spineReversal_reverse_branch m) hs

/-! ## 11.  The construction, checked against the genus-six picture -/

/-- **The slot involution at genus six.**  Slot `0` (the loop at the near spine
end) is exchanged with slot `14` (the loop at the far end), the five spine slots
`1, 4, 7, 10, 13` are reversed among themselves, the four stems `2, 5, 8, 11`
are reversed among themselves, and so are the four interior loops `3, 6, 9, 12`.
Only the middle spine slot `7` is fixed. -/
theorem revSlotVal_genusSix :
    (List.range 15).map (fun e ↦ revSlotVal 2 e) =
      [14, 13, 11, 12, 10, 8, 9, 7, 5, 6, 4, 2, 3, 1, 0] := by decide

/-- **The vertex involution at genus six.**  The spine `0–1–3–5–7–9` is
reversed (`0 ↔ 9`, `1 ↔ 7`, `3 ↔ 5`) and each stem tip is carried along with its
spine vertex (`2 ↔ 8`, `4 ↔ 6`).  No vertex is fixed. -/
theorem revVtxVal_genusSix :
    (List.range 10).map (fun v ↦ revVtxVal 2 v) = [9, 7, 8, 5, 6, 3, 4, 1, 2, 0] := by decide

end DraismaVargas.Count.SpineReversal
