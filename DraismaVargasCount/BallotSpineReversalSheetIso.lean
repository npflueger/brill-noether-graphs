module

public import DraismaVargasCount.SpineReversal
public import DraismaVargasCount.BallotEndSwapSheetIso
public import DraismaVargasCount.BallotFarEndSwap

@[expose] public section

/-!
# The spine reversal is a self-isomorphism of every palindromic ballot datum

This module proves the `hReversal` hypothesis of
`BallotFarEndSwap.diagonalClassification_genusSix_of_reversal`, the reversal branch of
`hStab`.  `hStab` asks that every relabelling of `catCore m` stabilising a ballot core
diagonal be realised by the ballot member: residue (B) of
`SlopeRigidity.coreDiagRigid_iff`, restricted to the ballot members, which is the
realisation half of the uniqueness in `prop-caterpillar-ballot`(2) of Vargas, Part II
(arXiv:2609.09109).

## What this module supplies

After `BallotFarEndSwap`, `hStab` at genus six rests on one hypothesis,
`hReversal`: every relabelling of `catCore 2` in the *reversal* branch of
`BallotStabiliserReduction.innerIndex_id_or_reverse` must be realised by the ballot
member of every palindromic slope sequence.  `SpineReversal` builds the spine
reversal as a `Relabel` at every `m`, without a sheet layer; this module supplies the
sheet layer.

* **`bRevDatumIso s hs : GeometricDatumIso (ballotDatum m s) (ballotDatum m s)`**
  -- the sheet-carrying self-isomorphism lying over `SpineReversal.spineReversal m`,
  at **every** `m` and every palindromic `s`.
* **`ballotRealizes_spineReversal s hs request`** -- so
  `Realizes (spineReversal m) (ballotFamilyMember m request s)`, at every `m`,
  every palindrome, and every request whatsoever.
* **`hReversal_of_identity`**, **`hStab_of_identity`** -- at every `m` the
  reversal branch, hence all of `hStab`, follows from the identity branch.
* **`hReversal_genusSix`** -- `hReversal` discharged, in the exact binder shape of
  `BallotFarEndSwap.diagonalClassification_genusSix_of_reversal`.
* **`hStab_genusSix`** -- the whole of `hStab` at genus six, discharged: the third
  residue of `DiagonalClassificationGenusSix.diagonalClassification_of_residues`.
* **`diagonalClassification_genusSix_of_three_residues`** --
  `BallotSlopes.DiagonalClassification 2 request` from `hSep`, `hSpine`, `hSupply`
  alone.

## The finding: one reflection on the spine, one transposition per lollipop

One might expect, following `SpineReversal.cum_reflect`, a sheet
family that *shifts* the block over the spine edge `h_i` by `m+1-i` -- a shift
that changes from edge to edge -- with the `compatible` slack absorbing the
discrepancy at every spine vertex.  That is not what happens, and the actual
mechanism is simpler.

* **The spine takes a single global permutation.**  By the height dictionary
  (`two_cum_succ`) the block over `h_i` is `{0} ∪ [i+1-cum i, cum i]`: the labels
  form a first-in-first-out queue, pushed at the top and popped at the bottom.
  At a palindrome, `cum_reflect` turns the block over `h_{g-i}` into
  `{0} ∪ [m+2-cum i, m+1+cum i-i]`, which is the image of the block over `h_i`
  under the **reflection** `k ↦ m+2-k` (fixing sheet `0`) -- for every `i` at
  once (`spineMem_reflect`).  Reading a FIFO queue backwards reverses the order
  of its labels; that is the whole reason.  So `mirror m` is the sheet
  permutation at every spine vertex, every spine edge, and both end lollipops,
  and every `compatible` obligation among them is free (the two permutations
  coincide).
* **Only the bridge pairs break it.**  The stem at `p_k` carries `cum k`, the
  newest label over the spine edge `h_k` on its right.  The mirror sends it to
  `m+2-cum k`, the *oldest* label over `h_{g-k}` -- the edge on the *left* of
  `p_{g+1-k}` -- whereas the stem at `p_{g+1-k}` carries `cum (g+1-k)`, the
  newest label over the edge on its right.  "Newest label on the right" does not
  survive reading the spine backwards.  So at each interior lollipop `k`
  (`2 ≤ k ≤ g-1`: the stem, `u_k`, the loop, `v_k`) the mirror is corrected by
  the transposition `(cum k, m+2-cum (g+1-k))` (`lolliPerm`), which exchanges
  the stem label with the mirror preimage of the image stem label.  Both lie in
  the block over `p_k` (`vertMem_partner`), and that is the **only** `compatible`
  obligation that is not free (`lolliSwap_rel`).

At `[2,3,2,3,2]` this can be seen by hand: the middle spine edge
forces a global permutation to fix sheet `2`, and the bridge pairs force
`2 ↦ 3`.
`edgePerm_ne_of_rev_hump` records the obstruction in Lean: over the reversal's
target layer, *every* isomorphism uses different sheet permutations over the
middle spine edge and over the first stem.  At `[2,1,2,1,2]` the correction is
trivial and the mirror is global (`sheetAt_zigzag_eq_mirror`); at `[2,3,2,3,2]`
and `[2,3,4,3,2]` it is not (`lolliPerm_hump_ne_mirror`, `lolliPerm_six_ne_mirror`).

The branch reduction is also simple: no enumeration of the reversal branch and no
use of `SpineReversal.reversal_branch_unique` is needed.  `reversal_branch_factor`
writes every `d` in the reversal branch as `comp (spineReversal m) d'` with `d'`
in the identity branch, which is realised at genus six in full
(`BallotFarEndSwap.identity_branch_realized_genusSix`), and `Realizes` is closed
under composition (`BallotFarEndSwap.realizes_comp`; `SpineReversal.comp d d'`
*is* `relabelComp d' d`, by `rfl`).

## What is proved

* `revTgtVal`, its closed forms, `revTgtVal_rev`, `revEnds_aux`; `revTgtEquiv`,
  `revEdgeEquiv`, **`rev_tree_ends`** -- the target layer at every `m`: `u_1 ↔ u_g`,
  `v_1 ↔ v_g`, and `u_k ↔ u_{g+1-k}`, `v_k ↔ v_{g+1-k}`, `p_k ↔ p_{g+1-k}`; the
  spine edges reverse their storage orientation, every other occurrence keeps it.
* `mirrorVal`, `slope_pal`, **`spineMem_reflect`**, **`vertMem_reflect`**,
  `pairMem_one_iff`, `cum_top`, `pairMem_top_iff`, `vertMem_top_iff` -- the
  palindrome block arithmetic, at every `m`.
* `mirror`, `cumSheet`, `partner`, `lolliSwap`, **`lolliPerm`**,
  `pairMem_lolliPerm`, `IsLolli`, **`sheetAt`** -- the sheet family.
* `vertPred_mirror`, `vertPred_lolliPerm`, `edgePred_mirror`, `edgePred_lolliPerm`
  -- the membership dictionary, transported, at every target vertex and
  occurrence.
* `vertexPartition_rev`, `edgePartition_rev`, `sheetAt_parent`,
  **`lolliSwap_rel`**, `compatible_rev` -- the three obligations.
* **`bRevDatumIso`**, `bRevDatumIso_targetVertex`, `bRevDatumIso_targetEdge`,
  `revVtx_branchIdx`, `bRevDatumIso_rowIndex`,
  `bRevDatumIso_overCore_row`, `bRevDatumIso_overCore_vertex`,
  **`ballotRealizes_spineReversal`** -- the realisation, at every `m`.
* **`hReversal_of_identity`**, **`hStab_of_identity`** (every `m`),
  **`hReversal_genusSix`**, **`hStab_genusSix`**,
  **`diagonalClassification_genusSix_of_three_residues`** (genus six).
* `zigzag`, `hump`, `slopes_ext`, `palindrome_zigzag`, `palindrome_hump`,
  `palindrome_six`, `ballotRealizes_spineReversal_hump`,
  `sheetAt_zigzag_eq_mirror`, `lolliPerm_hump_ne_mirror`,
  `lolliPerm_six_ne_mirror`, `edgePart_hump_seven_eq_two`,
  `edgePart_hump_seven_ne_eleven`, **`edgePerm_ne_of_rev_hump`** -- the three
  genus-six palindromes, the palindrome hypothesis inhabited at each, and the
  obstruction to a constant sheet layer.

## What is NOT proved (every hypothesis, explicitly)

* **`BallotSlopes.DiagonalClassification 2 request` is not proved here.**  Here it
  rests on `hSep`, `hSpine` and `hSupply` -- the three residues of
  `diagonalClassification_genusSix_of_three_residues` -- none of which this
  module touches or inhabits.  (It is proved at every request in
  `CaterpillarAllMembers`.)
* **`hStab` is proved at genus six only.**  At every `m`, `hStab_of_identity`
  reduces it to the identity branch.  That branch is closed only at `m = 2`,
  because the near-end sheet isomorphism
  (`BallotEndSwapSheetIso.ballotRealizes_endSwap`) and
  `BallotStabiliserReduction.left_end_determined`/`right_end_determined`/`identity_branch_unique`
  are stated at genus six.  The far end swap and everything in this module are at
  every `m`.
* **The choice of target layer is not proved forced.**  `revTgtEquiv` and
  `revEdgeEquiv` are the tree-level reading of `spineReversal m`; that `ends`
  forces them is a paper argument, not a Lean one.  Likewise the sheet family is
  exhibited, not proved unique.  `edgePerm_ne_of_rev_hump` only shows that it
  cannot be constant.
* **`Aut (catCore m)` is not enumerated.**  Nothing here counts
  relabellings; the reduction goes through `reversal_branch_factor`, not through
  a cardinality.
* **Requests.**  The headline and `hReversal_genusSix` hold for every request,
  with no positivity or genericity used; the corollary takes the implicit
  `request` of the theorem it composes with.  No supply predicate is
  introduced.  `IsLolli` is an index class (`v % 3 ≠ 2 ∧ 3 ≤ v ≤ 6m+1`, the
  vertices `u_k`, `v_k` with `2 ≤ k ≤ g-1`), decided by `if` inside `sheetAt`,
  and is not a hypothesis anything outside this module must supply.
* No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`, no
  `#eval`.  `decide` appears only in the genus-six checks of §9.
-/

namespace DraismaVargas.Count.BallotSpineReversalSheetIso

open DraismaVargas.Count
open DraismaVargas.Count.BallotDatum
open DraismaVargas.Count.CoreRelabel
open DraismaVargas.Count.FibreCaterpillar
open DraismaVargas.Count.SlopeRigidity
open DraismaVargas.Count.BallotCoreIdentification
open DraismaVargas.Count.BallotValency
open DraismaVargas.Count.SpineReversal
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CaterpillarDatum
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open DraismaVargas.LocalCases.W4StableSource

/-! ## 1.  The reversal of the target tree, on indices

`catTree m` numbers `u_i = 3i-3`, `v_i = 3i-2`, `p_i = 3i-4` for `i ≤ g-1`, and
`u_g = 6m+2`, `v_g = 6m+3`.  The reversal sends lollipop `i` to lollipop
`g+1-i`, which in indices is `u ↦ 6m+3-u`, `v ↦ 6m+5-v`, `p ↦ 6m+1-p`, with the
two end lollipops exchanged separately. -/

/-- The spine reversal on target vertex indices. -/
def revTgtVal (m v : ℕ) : ℕ :=
  if v = 0 then 6 * m + 2
  else if v = 6 * m + 2 then 0
  else if v = 1 then 6 * m + 3
  else if v = 6 * m + 3 then 1
  else if v % 3 = 0 then 6 * m + 3 - v
  else if v % 3 = 1 then 6 * m + 5 - v
  else 6 * m + 1 - v

theorem revTgtVal_zero (m : ℕ) : revTgtVal m 0 = 6 * m + 2 := by
  unfold revTgtVal; rw [ite_eq_left rfl]

theorem revTgtVal_top (m : ℕ) : revTgtVal m (6 * m + 2) = 0 := by
  unfold revTgtVal; rw [ite_eq_right (by omega), ite_eq_left rfl]

theorem revTgtVal_one (m : ℕ) : revTgtVal m 1 = 6 * m + 3 := by
  unfold revTgtVal; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]

theorem revTgtVal_topLeaf (m : ℕ) : revTgtVal m (6 * m + 3) = 1 := by
  unfold revTgtVal; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]

/-- The interior stem tips `u_k`. -/
theorem revTgtVal_three {m v : ℕ} (h : v % 3 = 0) (h0 : v ≠ 0) (h1 : v ≠ 6 * m + 3) :
    revTgtVal m v = 6 * m + 3 - v := by
  unfold revTgtVal
  rw [ite_eq_right h0, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h1, ite_eq_left h]

/-- The interior folded tips `v_k`. -/
theorem revTgtVal_three_one {m v : ℕ} (h : v % 3 = 1) (h1 : v ≠ 1) :
    revTgtVal m v = 6 * m + 5 - v := by
  unfold revTgtVal
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h1, ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_left h]

/-- The interior spine vertices `p_k`. -/
theorem revTgtVal_three_two {m v : ℕ} (h : v % 3 = 2) (h1 : v ≠ 6 * m + 2) :
    revTgtVal m v = 6 * m + 1 - v := by
  unfold revTgtVal
  rw [ite_eq_right (by omega), ite_eq_right h1, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega)]

theorem revTgtVal_lt {m v : ℕ} (hv : v < 6 * m + 4) : revTgtVal m v < 6 * m + 4 := by
  unfold revTgtVal; split_ifs <;> omega

theorem revTgtVal_rev {m v : ℕ} (hv : v < 6 * m + 4) : revTgtVal m (revTgtVal m v) = v := by
  rcases (show v = 0 ∨ v = 6 * m + 2 ∨ v = 1 ∨ v = 6 * m + 3 ∨
      (v % 3 = 0 ∧ v ≠ 0 ∧ v ≠ 6 * m + 3) ∨ (v % 3 = 1 ∧ v ≠ 1) ∨
      (v % 3 = 2 ∧ v ≠ 6 * m + 2) by omega) with h | h | h | h | h | h | h
  · rw [h, revTgtVal_zero, revTgtVal_top]
  · rw [h, revTgtVal_top, revTgtVal_zero]
  · rw [h, revTgtVal_one, revTgtVal_topLeaf]
  · rw [h, revTgtVal_topLeaf, revTgtVal_one]
  · rw [revTgtVal_three h.1 h.2.1 h.2.2, revTgtVal_three (by omega) (by omega) (by omega)]
    omega
  · rw [revTgtVal_three_one h.1 h.2, revTgtVal_three_one (by omega) (by omega)]
    omega
  · rw [revTgtVal_three_two h.1 h.2, revTgtVal_three_two (by omega) (by omega)]
    omega

/-- **The two ends of an occurrence, transported.**  The occurrence `i` joins
`parentIndex (i+1)` to `i+1`; its image `revSlotVal m i` joins the images of
those two vertices -- in the same order off the spine, in the opposite order on
the spine edges (`i % 3 = 1`). -/
theorem revEnds_aux (m i : ℕ) (hi : i < 6 * m + 3) :
    (parentIndex (revSlotVal m i + 1) = revTgtVal m (parentIndex (i + 1)) ∧
        revSlotVal m i + 1 = revTgtVal m (i + 1)) ∨
      (parentIndex (revSlotVal m i + 1) = revTgtVal m (i + 1) ∧
        revSlotVal m i + 1 = revTgtVal m (parentIndex (i + 1))) := by
  rcases (show i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 by omega) with h | h | h
  · obtain ⟨k, rfl⟩ : ∃ k, i = 3 * k := ⟨i / 3, by omega⟩
    left
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have hp : parentIndex (6 * m + 2 + 1) = 6 * m + 2 := by
        unfold parentIndex; split_ifs <;> omega
      rw [show 3 * 0 = 0 from rfl, revSlotVal_zero, hp, show parentIndex (0 + 1) = 0 from rfl,
        revTgtVal_zero, show (0 : ℕ) + 1 = 1 from rfl, revTgtVal_one]
      exact ⟨rfl, rfl⟩
    · have hr : revSlotVal m (3 * k) = 6 * m + 3 - 3 * k := by
        rw [revSlotVal_three m k hk (by omega)]; omega
      have hp1 : parentIndex (3 * k + 1) = 3 * k := by unfold parentIndex; split_ifs <;> omega
      have hp2 : parentIndex (6 * m + 3 - 3 * k + 1) = 6 * m + 3 - 3 * k := by
        unfold parentIndex; split_ifs <;> omega
      rw [hr, hp1, hp2, revTgtVal_three (by omega) (by omega) (by omega),
        revTgtVal_three_one (by omega) (by omega)]
      exact ⟨rfl, by omega⟩
  · obtain ⟨k, rfl⟩ : ∃ k, i = 3 * k + 1 := ⟨i / 3, by omega⟩
    right
    have hr : revSlotVal m (3 * k + 1) = 6 * m + 1 - 3 * k := by
      rw [revSlotVal_three_one m k (by omega)]; omega
    have hp1 : parentIndex (3 * k + 1 + 1) = 3 * k - 1 := by
      unfold parentIndex; split_ifs <;> omega
    have hp2 : parentIndex (6 * m + 1 - 3 * k + 1) = 6 * m - 1 - 3 * k := by
      unfold parentIndex; split_ifs <;> omega
    rw [hr, hp1, hp2]
    rcases (show k = 2 * m ∨ k < 2 * m by omega) with hk | hk
    · subst hk
      rw [show 3 * (2 * m) + 1 + 1 = 6 * m + 2 from by ring, revTgtVal_top]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [show 3 * (2 * 0) - 1 = 0 from rfl, revTgtVal_zero]; exact ⟨rfl, rfl⟩
      · rw [revTgtVal_three_two (by omega) (by omega)]; exact ⟨by omega, by omega⟩
    · rw [revTgtVal_three_two (m := m) (v := 3 * k + 1 + 1) (by omega) (by omega)]
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [show 3 * 0 - 1 = 0 from rfl, revTgtVal_zero]; exact ⟨by omega, by omega⟩
      · rw [revTgtVal_three_two (by omega) (by omega)]; exact ⟨by omega, by omega⟩
  · obtain ⟨k, rfl⟩ : ∃ k, i = 3 * k + 2 := ⟨i / 3, by omega⟩
    left
    rcases (show k = 2 * m ∨ k < 2 * m by omega) with hk | hk
    · subst hk
      have hp : parentIndex (0 + 1) = 0 := rfl
      have hp2 : parentIndex (6 * m + 2 + 1) = 6 * m + 2 := by
        unfold parentIndex; split_ifs <;> omega
      rw [show 3 * (2 * m) + 2 = 6 * m + 2 from by ring, revSlotVal_last, hp, hp2, revTgtVal_top,
        show 6 * m + 2 + 1 = 6 * m + 3 from rfl, revTgtVal_topLeaf]
      exact ⟨rfl, rfl⟩
    · have hr : revSlotVal m (3 * k + 2) = 6 * m - 1 - 3 * k := by
        rw [revSlotVal_three_two m k hk]; omega
      have hp1 : parentIndex (3 * k + 2 + 1) = 3 * k + 2 := by
        unfold parentIndex; split_ifs <;> omega
      have hp2 : parentIndex (6 * m - 1 - 3 * k + 1) = 6 * m - 1 - 3 * k := by
        unfold parentIndex; split_ifs <;> omega
      rw [hr, hp1, hp2, revTgtVal_three_two (by omega) (by omega),
        revTgtVal_three (by omega) (by omega) (by omega)]
      exact ⟨by omega, by omega⟩

/-! ## 2.  The target layer -/

/-- The reversal of the target tree `catTree m`. -/
def revTgt (m : ℕ) (v : (catTree m).V) : (catTree m).V :=
  ⟨revTgtVal m v.val, revTgtVal_lt v.isLt⟩

theorem revTgt_involutive (m : ℕ) : Function.Involutive (revTgt m) :=
  fun v ↦ Fin.ext (revTgtVal_rev v.isLt)

/-- The reversal of the target tree, as a permutation of its vertices. -/
def revTgtEquiv (m : ℕ) : (catTree m).V ≃ (catTree m).V :=
  (revTgt_involutive m).toPerm _

@[simp] theorem revTgtEquiv_val (m : ℕ) (v : (catTree m).V) :
    (revTgtEquiv m v).val = revTgtVal m v.val := rfl

/-- The spine reversal on target occurrences: `spineReversal m`'s slot
permutation, read through the occurrence dictionary. -/
noncomputable def revEdgeEquiv (m : ℕ) : (catTree m).edges ≃ (catTree m).edges :=
  (catEdgeEquiv m).symm.trans ((spineReversal m).slot.trans (catEdgeEquiv m))

theorem revEdgeEquiv_occ (m : ℕ) (i : Fin (6 * m + 3)) :
    revEdgeEquiv m (occ m i) = occ m ((spineReversal m).slot i) := by
  show catEdgeEquiv m ((spineReversal m).slot ((catEdgeEquiv m).symm (catEdgeEquiv m i))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem revEdgeEquiv_symm_apply (m : ℕ) (e : (catTree m).edges) :
    (catEdgeEquiv m).symm (revEdgeEquiv m e) =
      (spineReversal m).slot ((catEdgeEquiv m).symm e) := by
  show (catEdgeEquiv m).symm
    (catEdgeEquiv m ((spineReversal m).slot ((catEdgeEquiv m).symm e))) = _
  rw [Equiv.symm_apply_apply]

/-- **The spine reversal preserves unordered endpoints**, at every `m`. -/
theorem rev_tree_ends (m : ℕ) (edge : (catTree m).edges) :
    UnorderedEnds (revTgtEquiv m) (edge : (catTree m).V × (catTree m).V)
      (revEdgeEquiv m edge : (catTree m).V × (catTree m).V) := by
  obtain ⟨i, rfl⟩ := occ_surj m edge
  rw [revEdgeEquiv_occ]
  rcases revEnds_aux m i.val i.isLt with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (Prod.ext (Fin.ext h1) (Fin.ext h2))
  · exact Or.inr (Prod.ext (Fin.ext h1) (Fin.ext h2))

/-! ## 3.  The palindrome block arithmetic -/

/-- The reflection of the sheet labels: `0` is the spine sheet and stays, and a
label `k ≥ 1` goes to `m+2-k`. -/
def mirrorVal (m k : ℕ) : ℕ := if k = 0 then 0 else m + 2 - k

theorem mirrorVal_lt {m k : ℕ} (hk : k < m + 2) : mirrorVal m k < m + 2 := by
  unfold mirrorVal; split_ifs <;> omega

theorem mirrorVal_mirrorVal {m k : ℕ} (hk : k < m + 2) : mirrorVal m (mirrorVal m k) = k := by
  unfold mirrorVal; split_ifs <;> omega

section Blocks

variable {m : ℕ} (s : Slopes (2 * (m + 1)))

/-- The palindrome condition, read on the slope function. -/
theorem slope_pal (hs : BallotOrbit.reverseSlopes s = s) {i : ℕ} (h1 : 1 ≤ i)
    (h2 : i ≤ 2 * (m + 1) - 1) : s.slope i = s.slope (2 * (m + 1) - i) := by
  conv_lhs => rw [← hs]
  exact BallotOrbit.slope_reverseSlopes s h1 h2

/-- **The reflection carries the block over `h_i` onto the block over `h_{g-i}`**,
for every spine edge at once.  The block over `h_i` is the interval
`[i+1-cum i, cum i]` of labels together with the spine sheet (`two_cum_succ`), and
at a palindrome `cum_reflect` makes the block over `h_{g-i}` its reflection.
One might have expected an `i`-dependent shift here instead. -/
theorem spineMem_reflect (hs : BallotOrbit.reverseSlopes s = s) {i : ℕ} (h1 : 1 ≤ i)
    (h2 : i ≤ 2 * (m + 1) - 1) {k : ℕ} (hk : k < m + 2) :
    s.SpineMem i k ↔ s.SpineMem (2 * (m + 1) - i) (mirrorVal m k) := by
  have hA := two_cum_succ s h1 h2
  have hB := two_cum_succ s (i := 2 * (m + 1) - i) (by omega) (by omega)
  have hC := cum_reflect s hs h1 h2
  have hD := slope_pal s hs h1 h2
  unfold Slopes.SpineMem mirrorVal
  split_ifs with h0 <;> omega

/-- The same for the block over an interior spine vertex `p_i`, which the
reversal sends to `p_{g+1-i}`. -/
theorem vertMem_reflect (hs : BallotOrbit.reverseSlopes s = s) {i : ℕ} (h1 : 2 ≤ i)
    (h2 : i ≤ 2 * (m + 1) - 1) {k : ℕ} (hk : k < m + 2) :
    s.VertMem i k ↔ s.VertMem (2 * (m + 1) + 1 - i) (mirrorVal m k) := by
  unfold Slopes.VertMem
  rw [spineMem_reflect s hs (i := i - 1) (by omega) (by omega) hk,
    spineMem_reflect s hs (i := i) (by omega) h2 hk,
    show 2 * (m + 1) - (i - 1) = 2 * (m + 1) + 1 - i from by omega,
    show 2 * (m + 1) + 1 - i - 1 = 2 * (m + 1) - i from by omega]
  exact or_comm

theorem pairMem_one_iff (k : ℕ) : s.PairMem 1 k ↔ (k = 0 ∨ k = 1) := by
  unfold Slopes.PairMem; rw [Slopes.cum_one]

theorem cum_top : s.cum (2 * m + 2) = m + 1 := by
  have h := Slopes.cum_of_ge s (i := 2 * (m + 1) - 1) le_rfl
  rw [show 2 * (m + 1) - 1 + 1 = 2 * m + 2 from by omega, Slopes.cum_last s rfl] at h
  exact h

theorem pairMem_top_iff (k : ℕ) : s.PairMem (2 * m + 2) k ↔ (k = 0 ∨ k = m + 1) := by
  unfold Slopes.PairMem; rw [cum_top]

theorem vertMem_top_iff (k : ℕ) : s.VertMem (2 * m + 2) k ↔ (k = 0 ∨ k = m + 1) := by
  have hc1 : s.cum (2 * m + 1) = m + 1 := by
    have := Slopes.cum_last s (m := m) rfl
    rwa [show 2 * (m + 1) - 1 = 2 * m + 1 from by omega] at this
  have hs1 : s.slope (2 * m + 1) = 2 := Slopes.slope_of_ge s (by omega)
  have hs2 : s.slope (2 * m + 2) = 2 := Slopes.slope_of_ge s (by omega)
  have hc2 := cum_top s
  unfold Slopes.VertMem Slopes.SpineMem
  rw [show 2 * m + 2 - 1 = 2 * m + 1 from by omega, hc1, hc2, hs1, hs2]
  omega

end Blocks

/-! ## 4.  The sheet family -/

def mirrorFun (m : ℕ) (k : Fin (m + 2)) : Fin (m + 2) :=
  ⟨mirrorVal m k.val, mirrorVal_lt k.isLt⟩

theorem mirrorFun_involutive (m : ℕ) : Function.Involutive (mirrorFun m) :=
  fun k ↦ Fin.ext (mirrorVal_mirrorVal k.isLt)

/-- **The mirror**: the sheet permutation over the whole spine and both end
lollipops. -/
def mirror (m : ℕ) : Equiv.Perm (Fin (m + 2)) := (mirrorFun_involutive m).toPerm _

@[simp] theorem mirror_val (m : ℕ) (k : Fin (m + 2)) : (mirror m k).val = mirrorVal m k.val := rfl

theorem mirror_mirror (m : ℕ) (k : Fin (m + 2)) : mirror m (mirror m k) = k :=
  mirrorFun_involutive m k

theorem mirror_symm_apply (m : ℕ) (k : Fin (m + 2)) : (mirror m).symm k = mirror m k := rfl

theorem mirror_zero (m : ℕ) : mirror m 0 = 0 := Fin.ext (by simp [mirrorVal])

section Sheets

variable {m : ℕ} (s : Slopes (2 * (m + 1)))

/-- The label `cum s i`, as a sheet. -/
def cumSheet (i : ℕ) : Fin (m + 2) :=
  ⟨s.cum i, by have := Slopes.cum_le s (m := m) rfl i; omega⟩

@[simp] theorem cumSheet_val (i : ℕ) : (cumSheet s i).val = s.cum i := rfl

theorem cumSheet_ne_zero (i : ℕ) : cumSheet s i ≠ 0 := by
  intro h
  have h1 := congrArg Fin.val h
  have h2 := Slopes.one_le_cum s i
  rw [cumSheet_val] at h1
  exact absurd h1 (by simp; omega)

/-- The sheet the mirror sends to the bridge label `cum (g+1-k)` of the image
lollipop. -/
def partner (k : ℕ) : Fin (m + 2) := mirror m (cumSheet s (2 * (m + 1) + 1 - k))

theorem partner_ne_zero (k : ℕ) : partner s k ≠ 0 := by
  intro h
  have h1 := congrArg (mirror m) h
  rw [partner, mirror_mirror, mirror_zero] at h1
  exact cumSheet_ne_zero s _ h1

/-- The correction at lollipop `k`: the transposition of the bridge label
`cum k` with its partner. -/
def lolliSwap (k : ℕ) : Equiv.Perm (Fin (m + 2)) := Equiv.swap (cumSheet s k) (partner s k)

/-- **The sheet permutation at an interior lollipop `k`**: the correction,
then the mirror. -/
def lolliPerm (k : ℕ) : Equiv.Perm (Fin (m + 2)) := (lolliSwap s k).trans (mirror m)

theorem lolliPerm_apply (k : ℕ) (x : Fin (m + 2)) :
    lolliPerm s k x = mirror m (lolliSwap s k x) := rfl

theorem lolliSwap_zero (k : ℕ) : lolliSwap s k 0 = 0 :=
  Equiv.swap_apply_of_ne_of_ne (Ne.symm (cumSheet_ne_zero s k)) (Ne.symm (partner_ne_zero s k))

theorem lolliPerm_zero (k : ℕ) : lolliPerm s k 0 = 0 := by
  rw [lolliPerm_apply, lolliSwap_zero, mirror_zero]

theorem lolliPerm_eq_cum_iff (k : ℕ) (x : Fin (m + 2)) :
    lolliPerm s k x = cumSheet s (2 * (m + 1) + 1 - k) ↔ x = cumSheet s k := by
  rw [lolliPerm_apply]
  constructor
  · intro h
    have h1 := congrArg (mirror m) h
    rw [mirror_mirror] at h1
    rw [lolliSwap, Equiv.swap_apply_eq_iff,
      show mirror m (cumSheet s (2 * (m + 1) + 1 - k)) = partner s k from rfl,
      Equiv.swap_apply_right] at h1
    exact h1
  · rintro rfl
    rw [lolliSwap, Equiv.swap_apply_left, partner, mirror_mirror]

/-- **The lollipop permutation carries the bridge pair `{0, cum k}` onto the
bridge pair `{0, cum (g+1-k)}`.** -/
theorem pairMem_lolliPerm (k : ℕ) (x : Fin (m + 2)) :
    s.PairMem k x.val ↔ s.PairMem (2 * (m + 1) + 1 - k) (lolliPerm s k x).val := by
  unfold Slopes.PairMem
  constructor
  · rintro (h | h)
    · left
      rw [show x = 0 from Fin.ext h, lolliPerm_zero]
      rfl
    · right
      rw [show x = cumSheet s k from Fin.ext h, (lolliPerm_eq_cum_iff s k _).mpr rfl]
      rfl
  · rintro (h | h)
    · left
      have hx : lolliPerm s k x = lolliPerm s k 0 := by
        rw [lolliPerm_zero]; exact Fin.ext h
      rw [(lolliPerm s k).injective hx]
      rfl
    · right
      have hx := (lolliPerm_eq_cum_iff s k x).mp (Fin.ext h)
      rw [hx]
      rfl

theorem zero_lolliPerm_iff (k : ℕ) (x : Fin (m + 2)) :
    x.val = 0 ↔ (lolliPerm s k x).val = 0 := by
  constructor
  · intro h
    rw [show x = 0 from Fin.ext h, lolliPerm_zero]
    rfl
  · intro h
    have hx : lolliPerm s k x = lolliPerm s k 0 := by rw [lolliPerm_zero]; exact Fin.ext h
    rw [(lolliPerm s k).injective hx]
    rfl

/-- A target vertex of an *interior* lollipop: `u_k = 3k-3` or `v_k = 3k-2` with
`2 ≤ k ≤ g-1`.  An index class, decided by `if` in `sheetAt`; not a hypothesis.
Interface: equivalent, by definition, to `v % 3 ≠ 2 ∧ 3 ≤ v ∧ v ≤ 6m+1`. -/
def IsLolli (m v : ℕ) : Prop := v % 3 ≠ 2 ∧ 3 ≤ v ∧ v ≤ 6 * m + 1

instance (m v : ℕ) : Decidable (IsLolli m v) := by unfold IsLolli; infer_instance

/-- **The sheet family**, indexed by a target vertex; an occurrence takes the
permutation of its child endpoint.  The lollipop permutation at the vertices of
an interior lollipop, the mirror everywhere else. -/
def sheetAt (v : ℕ) : Equiv.Perm (Fin (m + 2)) :=
  if IsLolli m v then lolliPerm s (lolli v) else mirror m

theorem sheetAt_lolli {v : ℕ} (h : IsLolli m v) : sheetAt s v = lolliPerm s (lolli v) := ite_eq_left h

theorem sheetAt_mirror {v : ℕ} (h : ¬ IsLolli m v) : sheetAt s v = mirror m := ite_eq_right h

theorem sheetAt_zero (v : ℕ) : sheetAt s v 0 = 0 := by
  unfold sheetAt; split_ifs
  · exact lolliPerm_zero s _
  · exact mirror_zero m

end Sheets

/-! ## 5.  The membership dictionary, transported -/

section Dictionary

variable {m : ℕ} (s : Slopes (2 * (m + 1)))

theorem lolli_zero : lolli 0 = 1 := by unfold lolli; omega
theorem lolli_one : lolli 1 = 1 := by unfold lolli; omega
theorem lolli_top (m : ℕ) : lolli (6 * m + 2) = 2 * m + 2 := by unfold lolli; omega
theorem lolli_topLeaf (m : ℕ) : lolli (6 * m + 3) = 2 * m + 2 := by unfold lolli; omega

theorem mirror_ends_iff {k : ℕ} (hk : k < m + 2) :
    (k = 0 ∨ k = 1) ↔ (mirrorVal m k = 0 ∨ mirrorVal m k = m + 1) := by
  unfold mirrorVal; split_ifs <;> omega

theorem mirror_ends_iff' {k : ℕ} (hk : k < m + 2) :
    (k = 0 ∨ k = m + 1) ↔ (mirrorVal m k = 0 ∨ mirrorVal m k = 1) := by
  unfold mirrorVal; split_ifs <;> omega

theorem mirror_zero_iff {k : ℕ} (hk : k < m + 2) : k = 0 ↔ mirrorVal m k = 0 := by
  unfold mirrorVal; split_ifs <;> omega

theorem vertPred_zero_iff (k : ℕ) : VertPred m s 0 k ↔ (k = 0 ∨ k = 1) := by
  rw [vertPred_pair s (by omega), lolli_zero, pairMem_one_iff]

theorem vertPred_one_iff (k : ℕ) : VertPred m s 1 k ↔ (k = 0 ∨ k = 1) := by
  rw [vertPred_pair s (by omega), lolli_one, pairMem_one_iff]

theorem vertPred_top_iff (k : ℕ) : VertPred m s (6 * m + 2) k ↔ (k = 0 ∨ k = m + 1) := by
  rw [vertPred_junction s (by omega), lolli_top, vertMem_top_iff]

theorem vertPred_topLeaf_iff (k : ℕ) : VertPred m s (6 * m + 3) k ↔ (k = 0 ∨ k = m + 1) := by
  rw [vertPred_pair s (by omega), lolli_topLeaf, pairMem_top_iff]

/-- At every target vertex off the interior lollipops -- the spine vertices and
the two end lollipops -- the mirror carries the block onto the block at the
reversed vertex. -/
theorem vertPred_mirror (hs : BallotOrbit.reverseSlopes s = s) {a : ℕ} (ha : a < 6 * m + 4)
    (hna : ¬ IsLolli m a) {k : ℕ} (hk : k < m + 2) :
    VertPred m s a k ↔ VertPred m s (revTgtVal m a) (mirrorVal m k) := by
  unfold IsLolli at hna
  rcases (show a = 0 ∨ a = 1 ∨ a = 6 * m + 2 ∨ a = 6 * m + 3 ∨
      (a % 3 = 2 ∧ a ≠ 6 * m + 2) by omega) with h | h | h | h | h
  · rw [h, revTgtVal_zero, vertPred_zero_iff, vertPred_top_iff]
    exact mirror_ends_iff hk
  · rw [h, revTgtVal_one, vertPred_one_iff, vertPred_topLeaf_iff]
    exact mirror_ends_iff hk
  · rw [h, revTgtVal_top, vertPred_top_iff, vertPred_zero_iff]
    exact mirror_ends_iff' hk
  · rw [h, revTgtVal_topLeaf, vertPred_topLeaf_iff, vertPred_one_iff]
    exact mirror_ends_iff' hk
  · rw [revTgtVal_three_two h.1 h.2, vertPred_junction s h.1,
      vertPred_junction s (show (6 * m + 1 - a) % 3 = 2 by omega),
      show lolli (6 * m + 1 - a) = 2 * (m + 1) + 1 - lolli a by unfold lolli; omega]
    exact vertMem_reflect s hs (by unfold lolli; omega) (by unfold lolli; omega) hk

/-- At the two vertices `u_k`, `v_k` of an interior lollipop the lollipop
permutation carries the bridge pair onto the bridge pair at the reversed
vertex.  No palindrome hypothesis is needed here. -/
theorem vertPred_lolliPerm {a : ℕ} (ha : IsLolli m a) (x : Fin (m + 2)) :
    VertPred m s a x.val ↔ VertPred m s (revTgtVal m a) (lolliPerm s (lolli a) x).val := by
  unfold IsLolli at ha
  have hrev : revTgtVal m a = if a % 3 = 0 then 6 * m + 3 - a else 6 * m + 5 - a := by
    split_ifs with h
    · exact revTgtVal_three h (by omega) (by omega)
    · exact revTgtVal_three_one (by omega) (by omega)
  have hl : lolli (revTgtVal m a) = 2 * (m + 1) + 1 - lolli a := by
    rw [hrev]; unfold lolli; split_ifs <;> omega
  rw [vertPred_pair s ha.1, vertPred_pair s (by rw [hrev]; split_ifs <;> omega), hl]
  exact pairMem_lolliPerm s _ x

/-- Along the spine edges and the two end loops the mirror carries the block
onto the block over the reversed occurrence. -/
theorem edgePred_mirror (hs : BallotOrbit.reverseSlopes s = s) {i : ℕ} (hi : i < 6 * m + 3)
    (hna : ¬ IsLolli m (i + 1)) {k : ℕ} (hk : k < m + 2) :
    EdgePred m s i k ↔ EdgePred m s (revSlotVal m i) (mirrorVal m k) := by
  unfold IsLolli at hna
  rcases (show i % 3 = 1 ∨ i = 0 ∨ i = 6 * m + 2 by omega) with h | h | h
  · obtain ⟨j, rfl⟩ : ∃ j, i = 3 * j + 1 := ⟨i / 3, by omega⟩
    rw [revSlotVal_three_one m j (by omega), edgePred_spine s (by omega),
      edgePred_spine s (by omega),
      show (3 * (2 * m - j) + 1 + 2) / 3 = 2 * (m + 1) - (3 * j + 1 + 2) / 3 by omega]
    exact spineMem_reflect s hs (by omega) (by omega) hk
  · rw [h, revSlotVal_zero, edgePred_leaf s (Or.inl (by omega)),
      edgePred_leaf s (Or.inr rfl)]
    exact mirror_zero_iff hk
  · rw [h, revSlotVal_last, edgePred_leaf s (Or.inr rfl),
      edgePred_leaf s (Or.inl (by omega))]
    exact mirror_zero_iff hk

/-- Along the stem and the loop of an interior lollipop the lollipop
permutation carries the block onto the block over the reversed occurrence. -/
theorem edgePred_lolliPerm {i : ℕ} (hi : i < 6 * m + 3) (h : IsLolli m (i + 1))
    (x : Fin (m + 2)) :
    EdgePred m s i x.val ↔ EdgePred m s (revSlotVal m i) (lolliPerm s (lolli (i + 1)) x).val := by
  unfold IsLolli at h
  rcases (show i % 3 = 2 ∨ i % 3 = 0 by omega) with h3 | h3
  · obtain ⟨j, rfl⟩ : ∃ j, i = 3 * j + 2 := ⟨i / 3, by omega⟩
    rw [revSlotVal_three_two m j (by omega), edgePred_stem s (by omega) (by omega),
      edgePred_stem s (by omega) (by omega),
      show (3 * (2 * m - 1 - j) + 2 + 4) / 3 = 2 * (m + 1) + 1 - lolli (3 * j + 2 + 1) by
        unfold lolli; omega,
      show (3 * j + 2 + 4) / 3 = lolli (3 * j + 2 + 1) by unfold lolli; omega]
    exact pairMem_lolliPerm s _ x
  · obtain ⟨j, rfl⟩ : ∃ j, i = 3 * j := ⟨i / 3, by omega⟩
    rw [revSlotVal_three m j (by omega) (by omega), edgePred_leaf s (Or.inl (by omega)),
      edgePred_leaf s (Or.inl (by omega))]
    exact zero_lolliPerm_iff s _ x

end Dictionary

/-! ## 6.  The three obligations of `GeometricDatumIso` -/

section Obligations

variable {m : ℕ} (s : Slopes (2 * (m + 1)))

/-- **The vertex partitions**, at every target vertex. -/
theorem vertexPartition_rev (hs : BallotOrbit.reverseSlopes s = s) (v : (catTree m).V) :
    ballotVertexPart m s (revTgtEquiv m v) =
      (ballotVertexPart m s v).relabel (sheetAt s v.val) := by
  show catStar m (VertPred m s (revTgtVal m v.val)) =
    (catStar m (VertPred m s v.val)).relabel (sheetAt s v.val)
  symm
  by_cases h : IsLolli m v.val
  · rw [sheetAt_lolli s h]
    exact BallotEndSwapSheetIso.catStar_relabel_eq _ _ _ (lolliPerm_zero s _)
      (fun x ↦ vertPred_lolliPerm s h x)
  · rw [sheetAt_mirror s h]
    exact BallotEndSwapSheetIso.catStar_relabel_eq _ _ _ (mirror_zero m)
      (fun x ↦ vertPred_mirror s hs v.isLt h x.isLt)

/-- **The occurrence partitions**, at every target occurrence. -/
theorem edgePartition_rev (hs : BallotOrbit.reverseSlopes s = s) (e : (catTree m).edges) :
    ballotEdgePart m s (revEdgeEquiv m e) =
      (ballotEdgePart m s e).relabel (sheetAt s (edgeIndex m e + 1)) := by
  obtain ⟨i, rfl⟩ := occ_surj m e
  rw [revEdgeEquiv_occ]
  show catStar m (EdgePred m s (revSlotVal m i.val)) =
    (catStar m (EdgePred m s i.val)).relabel (sheetAt s (i.val + 1))
  symm
  by_cases h : IsLolli m (i.val + 1)
  · rw [sheetAt_lolli s h]
    exact BallotEndSwapSheetIso.catStar_relabel_eq _ _ _ (lolliPerm_zero s _)
      (fun x ↦ edgePred_lolliPerm s i.isLt h x)
  · rw [sheetAt_mirror s h]
    exact BallotEndSwapSheetIso.catStar_relabel_eq _ _ _ (mirror_zero m)
      (fun x ↦ edgePred_mirror s hs i.isLt h x.isLt)

/-- Off the stems, an occurrence and its parent endpoint carry the same sheet
permutation, so `compatible` is free there. -/
theorem sheetAt_parent {i : ℕ} (hi : i < 6 * m + 3) (hstem : ¬ (i % 3 = 2 ∧ i ≠ 6 * m + 2)) :
    sheetAt s (parentIndex (i + 1)) = sheetAt s (i + 1) := by
  rcases (show i % 3 = 1 ∨ i = 0 ∨ (i % 3 = 0 ∧ i ≠ 0) ∨ i = 6 * m + 2 by omega) with
    h | h | h | h
  · rw [sheetAt_mirror s (show ¬ IsLolli m (parentIndex (i + 1)) by
        unfold IsLolli parentIndex; split_ifs <;> omega),
      sheetAt_mirror s (show ¬ IsLolli m (i + 1) by unfold IsLolli; omega)]
  · subst h
    rw [sheetAt_mirror s (show ¬ IsLolli m (parentIndex (0 + 1)) by
        unfold IsLolli parentIndex; split_ifs <;> omega),
      sheetAt_mirror s (show ¬ IsLolli m (0 + 1) by unfold IsLolli; omega)]
  · have hp : parentIndex (i + 1) = i := by unfold parentIndex; split_ifs <;> omega
    rw [hp, sheetAt_lolli s (show IsLolli m i by unfold IsLolli; omega),
      sheetAt_lolli s (show IsLolli m (i + 1) by unfold IsLolli; omega),
      show lolli i = lolli (i + 1) by unfold lolli; omega]
  · rw [sheetAt_mirror s (show ¬ IsLolli m (parentIndex (i + 1)) by
        unfold IsLolli parentIndex; split_ifs <;> omega),
      sheetAt_mirror s (show ¬ IsLolli m (i + 1) by unfold IsLolli; omega)]

theorem vertMem_cumSheet (k : ℕ) : s.VertMem k (cumSheet s k).val :=
  Slopes.vertMem_of_pairMem s (Or.inr rfl)

/-- The partner of the bridge label lies in the block over `p_k` too: it is the
mirror image of the bridge label of `p_{g+1-k}`. -/
theorem vertMem_partner (hs : BallotOrbit.reverseSlopes s = s) {k : ℕ} (h1 : 2 ≤ k)
    (h2 : k ≤ 2 * (m + 1) - 1) : s.VertMem k (partner s k).val := by
  rw [vertMem_reflect s hs h1 h2 (partner s k).isLt, partner, mirror_val,
    mirrorVal_mirrorVal (cumSheet s _).isLt]
  exact vertMem_cumSheet s _

/-- **The one non-trivial `compatible` obligation**: at the spine vertex `p_k`,
which carries the mirror, the stem's permutation differs from it by the
correction `lolliSwap`, and the correction moves every sheet inside its own
block over `p_k`. -/
theorem lolliSwap_rel (hs : BallotOrbit.reverseSlopes s = s) {a : ℕ} (ha : a % 3 = 2)
    (h2 : a ≤ 6 * m - 1) (x : Fin (m + 2)) :
    (catStar m (VertPred m s a)).Rel (lolliSwap s (lolli (a + 1)) x) x := by
  rw [catStar_rel_iff _ (vertPred_zero s _)]
  have hl : lolli a = lolli (a + 1) := by unfold lolli; omega
  have hk1 : 2 ≤ lolli (a + 1) := by unfold lolli; omega
  have hk2 : lolli (a + 1) ≤ 2 * (m + 1) - 1 := by unfold lolli; omega
  have hC : VertPred m s a (cumSheet s (lolli (a + 1))).val := by
    rw [vertPred_junction s ha, hl]; exact vertMem_cumSheet s _
  have hP : VertPred m s a (partner s (lolli (a + 1))).val := by
    rw [vertPred_junction s ha, hl]; exact vertMem_partner s hs hk1 hk2
  by_cases hx1 : x = cumSheet s (lolli (a + 1))
  · subst hx1
    left
    rw [lolliSwap, Equiv.swap_apply_left]
    exact ⟨hP, hC⟩
  · by_cases hx2 : x = partner s (lolli (a + 1))
    · subst hx2
      left
      rw [lolliSwap, Equiv.swap_apply_right]
      exact ⟨hC, hP⟩
    · right
      exact Equiv.swap_apply_of_ne_of_ne hx1 hx2

/-- **The `compatible` field.**  At the child end of every occurrence, and at
the parent end of every occurrence except a stem, the two permutations are
equal; at the parent end `p_k` of a stem it is `lolliSwap_rel`. -/
theorem compatible_rev (hs : BallotOrbit.reverseSlopes s = s) (edge : (catTree m).edges)
    (vertex : (catTree m).V)
    (hv : (edge : (catTree m).V × (catTree m).V).1 = vertex ∨
      (edge : (catTree m).V × (catTree m).V).2 = vertex) (sheet : Fin (m + 2)) :
    (ballotVertexPart m s vertex).Rel
      ((sheetAt s vertex.val).symm (sheetAt s (edgeIndex m edge + 1) sheet)) sheet := by
  obtain ⟨i, rfl⟩ := occ_surj m edge
  have hlt := i.isLt
  rcases hv with h | h
  · have hval : vertex.val = parentIndex (i.val + 1) := by rw [← h]; rfl
    by_cases hstem : i.val % 3 = 2 ∧ i.val ≠ 6 * m + 2
    · have hp : parentIndex (i.val + 1) = i.val := by
        unfold parentIndex; split_ifs <;> omega
      rw [hp] at hval
      rw [hval, show edgeIndex m (occ m i) + 1 = i.val + 1 from rfl,
        sheetAt_mirror s (show ¬ IsLolli m i.val by unfold IsLolli; omega),
        sheetAt_lolli s (show IsLolli m (i.val + 1) by unfold IsLolli; omega),
        mirror_symm_apply, lolliPerm_apply, mirror_mirror]
      show (catStar m (VertPred m s vertex.val)).Rel _ sheet
      rw [hval]
      exact lolliSwap_rel s hs hstem.1 (by omega) sheet
    · rw [hval, show edgeIndex m (occ m i) + 1 = i.val + 1 from rfl,
        sheetAt_parent s hlt hstem, Equiv.symm_apply_apply]
      exact rfl
  · have hval : vertex.val = i.val + 1 := by rw [← h]; rfl
    rw [hval, show edgeIndex m (occ m i) + 1 = i.val + 1 from rfl, Equiv.symm_apply_apply]
    exact rfl

end Obligations

/-! ## 7.  The self-isomorphism, and `Realizes` -/

section Iso

variable {m : ℕ} (s : Slopes (2 * (m + 1)))

/-- **The spine reversal is a self-isomorphism of the ballot gluing datum, at
every `m` and every palindromic slope sequence.**  Its target layer is the
reversal of `catTree m`; its sheet layer is the mirror over the spine and the
two end lollipops and the corrected mirror `lolliPerm` over each interior
lollipop. -/
noncomputable def bRevDatumIso (hs : BallotOrbit.reverseSlopes s = s) :
    GeometricDatumIso (ballotDatum m s) (ballotDatum m s) where
  targetVertex := revTgtEquiv m
  targetEdge := revEdgeEquiv m
  ends := rev_tree_ends m
  vertexPerm v := sheetAt s v.val
  edgePerm e := sheetAt s (edgeIndex m e + 1)
  vertexPartition v := vertexPartition_rev s hs v
  edgePartition e := edgePartition_rev s hs e
  compatible edge vertex hv sheet := compatible_rev s hs edge vertex hv sheet

@[simp] theorem bRevDatumIso_targetVertex (hs : BallotOrbit.reverseSlopes s = s) :
    (bRevDatumIso s hs).targetVertex = revTgtEquiv m := rfl

@[simp] theorem bRevDatumIso_targetEdge (hs : BallotOrbit.reverseSlopes s = s) :
    (bRevDatumIso s hs).targetEdge = revEdgeEquiv m := rfl

/-- The core involution `revVtxVal` intertwines `branchIdx` with the tree
reversal at every **branch** target index (the folded tips `v_i` are not core
vertices). -/
theorem revVtx_branchIdx {v : ℕ} (hv : v < 6 * m + 4) (h1 : v % 3 ≠ 1) (h2 : v ≠ 6 * m + 3) :
    revVtxVal m (branchIdx (revTgtVal m v)) = branchIdx v := by
  rcases (show v = 0 ∨ v = 6 * m + 2 ∨ (v % 3 = 0 ∧ v ≠ 0) ∨
      (v % 3 = 2 ∧ v ≠ 6 * m + 2) by omega) with h | h | h | h
  · rw [h, revTgtVal_zero]; unfold revVtxVal branchIdx; split_ifs <;> omega
  · rw [h, revTgtVal_top]; unfold revVtxVal branchIdx; split_ifs <;> omega
  · rw [revTgtVal_three h.1 h.2 h2]; unfold revVtxVal branchIdx; split_ifs <;> omega
  · rw [revTgtVal_three_two h.1 h.2]; unfold revVtxVal branchIdx; split_ifs <;> omega

/-- The row dictionary moves by the slot part of the spine reversal. -/
theorem bRevDatumIso_rowIndex (hs : BallotOrbit.reverseSlopes s = s)
    (hconn : (ballotDatum m s).Connected) (edge : NonDanglingEdge (ballotDatum m s)) :
    (ballotLabelling m s).row ((bRevDatumIso s hs).stablePathEquiv hconn edge.stablePath) =
      (spineReversal m).slot ((ballotLabelling m s).row edge.stablePath) := by
  rw [GeometricDatumIso.stablePathEquiv_mk]
  show (catEdgeEquiv m).symm (revEdgeEquiv m edge.1.1.1) =
    (spineReversal m).slot ((catEdgeEquiv m).symm edge.1.1.1)
  exact revEdgeEquiv_symm_apply m _

/-- **The row half of `Realizes`**, the spine reversal being an involution on
slots. -/
theorem bRevDatumIso_overCore_row (hs : BallotOrbit.reverseSlopes s = s)
    (hconn : (ballotDatum m s).Connected) (path : StablePath (ballotDatum m s)) :
    (spineReversal m).slot
        ((ballotIdent m s).row ((bRevDatumIso s hs).stablePathEquiv hconn path)) =
      (ballotIdent m s).row path := by
  induction path using Quot.inductionOn with
  | h edge =>
    show (spineReversal m).slot ((ballotLabelling m s).row
        ((bRevDatumIso s hs).stablePathEquiv hconn edge.stablePath)) =
      (ballotLabelling m s).row edge.stablePath
    rw [bRevDatumIso_rowIndex s hs hconn edge]
    exact revSlot_involutive m _

/-- **The vertex half of `Realizes`.** -/
theorem bRevDatumIso_overCore_vertex (hs : BallotOrbit.reverseSlopes s = s)
    (hconn : (ballotDatum m s).Connected) (b : BranchVertex (ballotDatum m s)) :
    (spineReversal m).vtx
        ((ballotIdent m s).vertex ((bRevDatumIso s hs).branchVertexEquiv hconn b)) =
      (ballotIdent m s).vertex b := by
  have hbr := (bEq_bCore_of_branch s b.2).2
  apply Fin.ext
  show revVtxVal m ((ballotIdent m s).vertex ((bRevDatumIso s hs).branchVertexEquiv hconn b)).val =
    branchIdx b.1.1.1.val
  rw [show ((ballotIdent m s).vertex ((bRevDatumIso s hs).branchVertexEquiv hconn b)).val =
      branchIdx (revTgtVal m b.1.1.1.val) from rfl]
  exact revVtx_branchIdx b.1.1.1.isLt hbr.1 hbr.2

/-- **The spine reversal is realised by the ballot member of every palindromic
slope sequence**, at every `m`, over every request whatsoever: no positivity, no
genericity. -/
theorem ballotRealizes_spineReversal (hs : BallotOrbit.reverseSlopes s = s)
    (request : Fin (6 * m + 3) → ℚ) :
    Realizes (spineReversal m) (ballotFamilyMember m request s) :=
  ⟨bRevDatumIso s hs, bRevDatumIso_overCore_vertex s hs _, bRevDatumIso_overCore_row s hs _⟩

end Iso

/-! ## 8.  The reversal branch, and `hStab` -/

/-- **At every `m`, the reversal branch follows from the identity branch.**
`reversal_branch_factor` writes `d = comp (spineReversal m) d'` with `d'` in the
identity branch, `comp d d'` is `BallotFarEndSwap.relabelComp d' d` on the nose,
and `Realizes` is closed under composition. -/
theorem hReversal_of_identity (m : ℕ) (request : Fin (6 * m + 3) → ℚ)
    (hIdentity : ∀ (s : Slopes (2 * (m + 1))) (d : Relabel (catCore m) (catCore m)),
      (∀ a, a < 2 * m - 1 → BallotOrbit.innerIndex d a = a) →
        Realizes d (ballotFamilyMember m request s)) :
    ∀ (s : Slopes (2 * (m + 1))) (d : Relabel (catCore m) (catCore m)),
      (∀ a, a < 2 * m - 1 → BallotOrbit.innerIndex d a = 2 * m - 2 - a) →
        BallotOrbit.reverseSlopes s = s → Realizes d (ballotFamilyMember m request s) := by
  intro s d hrev hs
  obtain ⟨hid, hback⟩ := reversal_branch_factor m d hrev
  rw [← hback]
  exact BallotFarEndSwap.realizes_comp (hIdentity s _ hid)
    (ballotRealizes_spineReversal s hs request)

/-- **At every `m`, `hStab` follows from the identity branch alone.** -/
theorem hStab_of_identity (m : ℕ) (request : Fin (6 * m + 3) → ℚ)
    (hIdentity : ∀ (s : Slopes (2 * (m + 1))) (d : Relabel (catCore m) (catCore m)),
      (∀ a, a < 2 * m - 1 → BallotOrbit.innerIndex d a = a) →
        Realizes d (ballotFamilyMember m request s)) :
    ∀ (s : Slopes (2 * (m + 1))) (d : Relabel (catCore m) (catCore m)),
      (∀ slot, BallotSlopes.ballotCoreDiag m s (d.slot.symm slot) =
          BallotSlopes.ballotCoreDiag m s slot) →
        Realizes d (ballotFamilyMember m request s) :=
  BallotStabiliserReduction.hStab_of_two_branches m request hIdentity
    (hReversal_of_identity m request hIdentity)

/-- **`hReversal` at genus six, discharged**, in the exact binder shape of
`BallotFarEndSwap.diagonalClassification_genusSix_of_reversal`. -/
theorem hReversal_genusSix (request : Fin (6 * 2 + 3) → ℚ) :
    ∀ (s : Slopes (2 * (2 + 1))) (d : Relabel (catCore 2) (catCore 2)),
      (∀ a < 2 * 2 - 1, BallotOrbit.innerIndex d a = 2 * 2 - 2 - a) →
      BallotOrbit.reverseSlopes s = s →
      Realizes d (ballotFamilyMember 2 request s) :=
  hReversal_of_identity 2 request
    (fun s d hid ↦ BallotFarEndSwap.identity_branch_realized_genusSix s request d hid)

/-- **`hStab` at genus six, discharged**: every relabelling of `catCore 2`
stabilising a ballot core diagonal is realised by that ballot member, over every
request.  This is the third residue of
`DiagonalClassificationGenusSix.diagonalClassification_of_residues`. -/
theorem hStab_genusSix (request : Fin (6 * 2 + 3) → ℚ) :
    ∀ (s : Slopes (2 * (2 + 1))) (d : Relabel (catCore 2) (catCore 2)),
      (∀ slot, BallotSlopes.ballotCoreDiag 2 s (d.slot.symm slot) =
          BallotSlopes.ballotCoreDiag 2 s slot) →
        Realizes d (ballotFamilyMember 2 request s) :=
  BallotFarEndSwap.hStab_genusSix_of_reversal request (hReversal_genusSix request)

/-- **The genus-six package on three residues.**  `hSep`, `hSpine` and `hSupply`
are the hypotheses of `BallotFarEndSwap.diagonalClassification_genusSix_of_reversal`,
untouched; `hReversal` is supplied. -/
theorem diagonalClassification_genusSix_of_three_residues {request : Fin (6 * 2 + 3) → ℚ}
    (hSep : ∀ mem : FibreMember (catCore 2) request (2 + 2), mem.Open → mem.HasOddMult →
      SpineSingleColumn.LeafAvoidingSeparated 2 mem)
    (hSpine : ∀ mem : FibreMember (catCore 2) request (2 + 2),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        ∃ s : Slopes (2 * (2 + 1)), ∀ slot : Fin (6 * 2 + 3),
          ¬ CaterpillarPruning.IsLeafEdge 2 slot →
            mem.coreDiag slot = BallotSlopes.ballotCoreDiag 2 s slot)
    (hSupply : ∀ (s : Slopes (2 * (2 + 1))) (mem : FibreMember (catCore 2) request (2 + 2)),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        mem.coreDiag = BallotSlopes.ballotCoreDiag 2 s →
          Nonempty (GeometricDatumIso (ballotFamilyMember 2 request s).data mem.data)) :
    BallotSlopes.DiagonalClassification 2 request :=
  BallotFarEndSwap.diagonalClassification_genusSix_of_reversal hSep hSpine
    (hReversal_genusSix request) hSupply

/-! ## 9.  The three genus-six palindromes, and the obstruction to a constant
sheet layer -/

/-- The palindrome `[2,1,2,1,2]` (the zig-zag). -/
def zigzag : Slopes (2 * (2 + 1)) where
  slopes := [2, 1, 2, 1, 2]
  length_eq := rfl
  head_eq := by decide
  getLast_eq := by decide
  one_le := by decide
  step := by decide

/-- The palindrome `[2,3,2,3,2]`, the example that can be checked by hand. -/
def hump : Slopes (2 * (2 + 1)) where
  slopes := [2, 3, 2, 3, 2]
  length_eq := rfl
  head_eq := by decide
  getLast_eq := by decide
  one_le := by decide
  step := by decide

theorem slopes_ext {g : ℕ} {s t : Slopes g} (h : s.slopes = t.slopes) : s = t := by
  cases s; cases t; cases h; rfl

/-- The palindrome hypothesis is inhabited at each of the three genus-six
palindromes. -/
theorem palindrome_zigzag : BallotOrbit.reverseSlopes zigzag = zigzag := slopes_ext rfl

theorem palindrome_hump : BallotOrbit.reverseSlopes hump = hump := slopes_ext rfl

theorem palindrome_six : BallotOrbit.reverseSlopes Slopes.six = Slopes.six := slopes_ext rfl

theorem ballotRealizes_spineReversal_hump (request : Fin (6 * 2 + 3) → ℚ) :
    Realizes (spineReversal 2) (ballotFamilyMember 2 request hump) :=
  ballotRealizes_spineReversal hump palindrome_hump request

/-- At the zig-zag every correction is trivial and the mirror is a global sheet
permutation. -/
theorem sheetAt_zigzag_eq_mirror :
    ∀ v < 16, ∀ x : Fin (2 + 2), sheetAt zigzag v x = mirror 2 x := by
  decide

/-- At `[2,3,2,3,2]` the correction at lollipop `2` is genuine: the lollipop
permutation is the `3`-cycle `1 ↦ 2 ↦ 3 ↦ 1`, not the mirror `(1 3)`. -/
theorem lolliPerm_hump_ne_mirror :
    ((lolliPerm hump 2 1).val = 2 ∧ (lolliPerm hump 2 2).val = 3 ∧
        (lolliPerm hump 2 3).val = 1) ∧ lolliPerm hump 2 ≠ mirror 2 := by
  refine ⟨by decide, fun h ↦ ?_⟩
  have h1 := congrArg (fun σ : Equiv.Perm (Fin (2 + 2)) ↦ (σ 1).val) h
  revert h1
  decide

/-- At `[2,3,4,3,2]` the correction at lollipop `2` is the same `3`-cycle. -/
theorem lolliPerm_six_ne_mirror :
    ((lolliPerm (m := 2) Slopes.six 2 1).val = 2 ∧ (lolliPerm (m := 2) Slopes.six 2 2).val = 3 ∧
        (lolliPerm (m := 2) Slopes.six 2 3).val = 1) ∧
      lolliPerm (m := 2) Slopes.six 2 ≠ mirror 2 := by
  refine ⟨by decide, fun h ↦ ?_⟩
  have h1 := congrArg (fun σ : Equiv.Perm (Fin (2 + 2)) ↦ (σ 1).val) h
  revert h1
  decide

/-- At `[2,3,2,3,2]` the middle spine edge `h₃` (occurrence `7`) and the first
stem (occurrence `2`) carry the same partition, `{0, 2}` and singletons... -/
theorem edgePart_hump_seven_eq_two :
    ballotEdgePart 2 hump (occ 2 ⟨7, by omega⟩) =
      ballotEdgePart 2 hump (occ 2 ⟨2, by omega⟩) := by
  apply SheetPartition.ext_repr
  funext k
  revert k
  decide

/-- ... but their images under the reversal, `h₃` itself and the last stem
(occurrence `11`, bridge pair `{0, 3}`), do not. -/
theorem edgePart_hump_seven_ne_eleven :
    ballotEdgePart 2 hump (occ 2 ⟨7, by omega⟩) ≠
      ballotEdgePart 2 hump (occ 2 ⟨11, by omega⟩) := by
  intro h
  have h2 := congrArg (fun P : SheetPartition (2 + 2) ↦ P.repr 2) h
  revert h2
  decide

/-- **No constant sheet layer over the spine reversal at `[2,3,2,3,2]`.**  Every
self-isomorphism of the ballot datum over the reversal's target occurrences uses
*different* sheet permutations over the middle spine edge and over the first
stem.  This is the hand obstruction ("the spine forces `σ(2) = 2`, the bridge
pairs force `σ(2) = 3`"), with no assumption on the vertex layer or on sheet
`0`. -/
theorem edgePerm_ne_of_rev_hump (a : GeometricDatumIso (ballotDatum 2 hump) (ballotDatum 2 hump))
    (ha : a.targetEdge = revEdgeEquiv 2) :
    a.edgePerm (occ 2 ⟨7, by omega⟩) ≠ a.edgePerm (occ 2 ⟨2, by omega⟩) := by
  intro h
  have h7 := a.edgePartition (occ 2 ⟨7, by omega⟩)
  have h2 := a.edgePartition (occ 2 ⟨2, by omega⟩)
  rw [ha, revEdgeEquiv_occ] at h7 h2
  have e7 : (spineReversal 2).slot ⟨7, by omega⟩ = ⟨7, by omega⟩ := Fin.ext (by decide)
  have e2 : (spineReversal 2).slot ⟨2, by omega⟩ = ⟨11, by omega⟩ := Fin.ext (by decide)
  rw [e7] at h7
  rw [e2] at h2
  apply edgePart_hump_seven_ne_eleven
  calc ballotEdgePart 2 hump (occ 2 ⟨7, by omega⟩)
      = (ballotEdgePart 2 hump (occ 2 ⟨7, by omega⟩)).relabel
          (a.edgePerm (occ 2 ⟨7, by omega⟩)) := h7
    _ = (ballotEdgePart 2 hump (occ 2 ⟨2, by omega⟩)).relabel
          (a.edgePerm (occ 2 ⟨2, by omega⟩)) := by rw [edgePart_hump_seven_eq_two, h]
    _ = ballotEdgePart 2 hump (occ 2 ⟨11, by omega⟩) := h2.symm

end DraismaVargas.Count.BallotSpineReversalSheetIso
