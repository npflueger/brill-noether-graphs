import DraismaVargasCount.BallotStabiliserReduction

/-!
# The far end swap, constructed and realised: `hStab`'s identity branch closes

The `hStab` hypothesis of `DiagonalClassificationGenusSix` asks that every
relabelling of `catCore m` stabilising a ballot core diagonal be realised by the
ballot member: residue (B) of `SlopeRigidity.coreDiagRigid_iff`, restricted to the
ballot members, which is the realisation half of the uniqueness in
`prop-caterpillar-ballot`(2) of Vargas, Part II (arXiv:2609.09109).

## What this module supplies

`BallotStabiliserReduction` reduces `hStab` at genus six to two hypotheses,
`hFar` and `hReversal`; `hFar` concerns the relabellings with a non-trivial
far-end bit.  This module builds them and proves `hFar`.

* `farSwap m : Relabel (catCore (m+1)) (catCore (m+1))` -- the exchange of the
  two loops at the *far* end of the spine, the mirror of
  `SlopeRigidity.endSwap`: slots `(6M-1  6M+1)(6M  6M+2)`, vertices
  `(4M  4M+1)`, writing `M = m+1`.
* `bFarSwapDatumIso s` -- a self-isomorphism of `ballotDatum (m+1) s` lying over
  it, for **every** slope sequence and at **every** even genus at least four.
* `ballotRealizes_farSwap` -- so `SlopeRigidity.Realizes (farSwap m)` holds at
  every ballot member, over every request whatsoever.
* `relabelComp`, `realizes_comp`, `nearFarSwap`, `ballotRealizes_nearFarSwap` --
  the same for the product of the two end swaps, the fourth element of the
  Klein four-group.
* `hFar_genusSix` -- the `hFar` hypothesis of
  `BallotStabiliserReduction.hStab_genusSix_of_far_and_reversal`, discharged.
* `identity_branch_realized_genusSix` -- **the whole identity branch of `hStab`
  at genus six is closed**: every relabelling acting as the identity on the
  interior spine slots is realised, with no hypothesis on the request.
* `hStab_genusSix_of_reversal`,
  `diagonalClassification_genusSix_of_reversal` -- the genus-six package with
  one residue fewer: `hSep`, `hSpine`, `hReversal`, `hSupply`.

## The finding: the far end is *easier* than the near end, not harder

At the near end the identity sheet layer does not work -- the end swap preserves
neither `ballotVertexPart` nor `ballotEdgePart` there -- and `BallotEndSwapSheetIso`
carries the genuine transposition `(cum s 1, cum s 2)`
(`BallotEndSwapSheetIso.bSwap_six_ne_refl`).  One might expect the far end to need
the same adjustment, with the same two complications (the loops must be among the
moved occurrences; the transposition degenerates when `cum` does).

**Neither happens.**  At the far end *both* partitions are preserved on the
nose, so the sheet layer is the identity at every target vertex and every
occurrence (`bFarSwapDatumIso_vertexPerm`, `bFarSwapDatumIso_edgePerm`), and the
`compatible` field is `rfl`.

The structural reason is §3.  The near-end swap exchanges lollipops `1` and `2`,
whose bridge pairs are `{0, cum s 1}` and `{0, cum s 2}` -- different blocks
whenever `s₂ = 3`.  The far-end swap exchanges lollipops `g-1` and `g`, which
both sit at or past the last spine edge `h_{g-1}`, where `cum` has already
saturated at `m+2` (`cum_far`).  So both bridge pairs, the last spine block and
the last spine-vertex block are the *same* two-element block `{0, m+2}`
(`vertPred_far`, `edgePred_farPair`), and the two loops both carry the discrete
partition (`edgePred_farLeaf`).  Nothing has to be moved.

One genuinely new wrinkle does appear, in the opposite place: the *vertex* half
of `Realizes`.  The near-end identity
`SlopeRigidity.endSwapVtx_branchIdx` holds at every target index with no branch
hypothesis; the far-end one (`farSwapVtx_branchIdx`) does **not**, because the
last folded tip `v_g = 6M+3` is exceptional -- `branchIdx (6M+3) = 4M+2` is not
a core vertex at all -- so the arithmetic fails at the index `6M+1` that is sent
there.  `IsBranchIndex`, which excludes exactly the folded tips, is what makes
it hold.

## What is proved

* `coreIncidence_farStem`, `coreIncidence_farLoop`, `coreIncidence_farSpine`,
  `coreIncidence_farLast`, `coreIncidence_farVtx_zero` -- the far end of
  `catCore (m+1)`, read off in raw indices.
* `farSwapSlotFun`, `farSwapVtxFun`, their involutivity, `farSwap_incidence`,
  **`farSwap`**, `farSwap_slot_val`, `farSwap_ne_refl`, `farSwap_slot_of_le`,
  `innerIndex_farSwap`, `farSwap_slot_far` -- the relabelling.
* `cum_far`, `spineMem_far`, `pairMem_far`, `vertMem_far`, **`vertPred_far`**,
  **`edgePred_farPair`**, `edgePred_farLeaf`, `ballotVertexPart_far`,
  `ballotEdgePart_farPair`, `ballotEdgePart_farLeaf` -- the far-end membership
  dictionary, at every `m`.
* `farTgtFun`, `farTgtEquiv`, `farEdgeEquiv`, `farEnds_fst_aux`,
  `farEnds_snd_aux`, **`farSwap_ends`** -- the target layer.
* **`bFarSwapDatumIso`**, `bFarSwapDatumIso_rowIndex`,
  `bFarSwapDatumIso_overCore_row`, `farSwapVtx_branchIdx`,
  `bFarSwapDatumIso_overCore_vertex`, **`ballotRealizes_farSwap`** -- its
  realisation.
* `relabelComp`, **`realizes_comp`**, `innerIndex_of_slot_fix`, `nearFarSwap`,
  `nearFarSwap_slot_one`, `nearFarSwap_slot_far`, `innerIndex_nearFarSwap`,
  **`ballotRealizes_nearFarSwap`** -- the composite.
* **`hFar_genusSix`**, **`identity_branch_realized_genusSix`**,
  **`hStab_genusSix_of_reversal`**,
  **`diagonalClassification_genusSix_of_reversal`** -- the genus-six assembly.

## What is NOT proved (every hypothesis, explicitly)

* **`hStab` is not proved by this file.**  `hStab_genusSix_of_reversal`
  takes `hReversal`, the reversal branch of
  `BallotStabiliserReduction.hStab_of_two_branches`.  What closes here is the
  *identity* branch only.  `hReversal` is proved at genus six by
  `BallotSpineReversalSheetIso.hReversal_genusSix`, so
  `hStab_genusSix_of_reversal` composed with it gives
  `BallotSpineReversalSheetIso.hStab_genusSix`, and
  `BallotSpineReversalSheetIso.diagonalClassification_genusSix_of_three_residues`
  does not take `hStab` at all.
* **The spine reversal is not constructed by this file, at any `m ≥ 1`.**
  `SpineReversal` constructs it as a `Relabel` at every `m`, and
  `BallotSpineReversalSheetIso` builds the sheet-carrying isomorphism over it and
  realises the reversal branch at genus six.
  `BallotStabiliserReduction.reverseSlopes_eq_of_stab` is all that is proved about
  it at other `m`.
* **`Aut (catCore m)` is not enumerated**, at any `m ≥ 1`.  The identity
  branch is fully realised, but that is a statement about one branch of the
  dichotomy `BallotStabiliserReduction.innerIndex_id_or_reverse`, not about the
  group.
* **Nothing about `hSep`/`hTrivalent`, `hSpine`/`hThree` or `hSupply`**, the
  other three residues of
  `DiagonalClassificationGenusSix.diagonalClassification_genusSix_of_residues`.
* **The genus-six statements are genus six only.**  `farSwap`,
  `bFarSwapDatumIso` and `ballotRealizes_farSwap` are proved at every `m`, but
  `hFar_genusSix`, `identity_branch_realized_genusSix` and the two assembly
  theorems are stated at `m = 2` because
  `BallotStabiliserReduction.left_end_determined` /
  `right_end_determined` / `identity_branch_unique` and
  `BallotEndSwapSheetIso.ballotRealizes_endSwap` are.  The near-end input is the
  binding one: it is genus six only.
* **The choice of target layer is not proved forced.**  `farTgtEquiv` and
  `farEdgeEquiv` are the tree-level reading that mirrors
  `EndSwapRealized`; that the `ends` field forces them is a paper
  argument, not a Lean one.  Likewise the identity sheet layer is exhibited, not
  proved unique.
* **`m ≥ 1` is implicit in the shape `catCore (m+1)`**; at `m = 0` (genus two)
  the two ends of the spine coincide and nothing here applies.
* No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`, no
  `#eval`.
-/

namespace DraismaVargas.Count.BallotFarEndSwap

open DraismaVargas.Count
open DraismaVargas.Count.BallotDatum
open DraismaVargas.Count.CoreRelabel
open DraismaVargas.Count.FibreCaterpillar
open DraismaVargas.Count.SlopeRigidity
open DraismaVargas.Count.BallotCoreIdentification
open DraismaVargas.Count.BallotValency
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CaterpillarDatum
open DraismaVargas.LocalCases.CaterpillarPruning (IsLeafEdge)
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open DraismaVargas.LocalCases.W4StableSource
open Utilities.Certificate.ExplicitPotential (Core)

/-! ## 1.  The four slots and three vertices at the far end

At `catCore (m+1)`, writing `M = m+1` and `g = 2M+2`, the last four slots are
`6M-1 = 6m+5` (the last stem `p_{g-1} u_{g-1}`), `6M = 6m+6` (the loop at
`u_{g-1}`), `6M+1 = 6m+7` (the last spine edge `p_{g-1} u_g`) and
`6M+2 = 6m+8` (the loop at `u_g`); the core vertices they meet are
`p_{g-1} = 4M-1 = 4m+3`, `u_{g-1} = 4M = 4m+4` and `u_g = 4M+1 = 4m+5`.
-/

/-- The last stem `p_{g-1} u_{g-1}`. -/
theorem coreIncidence_farStem (m : ℕ) (v : Fin (4 * (m + 1) + 2)) (e : Fin (6 * (m + 1) + 3))
    (he : e.val = 6 * m + 5) :
    coreIncidence (catCore (m + 1)) v e =
      (if v.val = 4 * m + 3 then 1 else 0) + (if v.val = 4 * m + 4 then 1 else 0) := by
  rw [coreIncidence_catCore_val]
  unfold catTailVal catHeadVal branchIdx parentIndex IsLeafEdge
  split_ifs <;> omega

/-- The loop at `u_{g-1}`. -/
theorem coreIncidence_farLoop (m : ℕ) (v : Fin (4 * (m + 1) + 2)) (e : Fin (6 * (m + 1) + 3))
    (he : e.val = 6 * m + 6) :
    coreIncidence (catCore (m + 1)) v e = if v.val = 4 * m + 4 then 2 else 0 := by
  rw [coreIncidence_catCore_val]
  unfold catTailVal catHeadVal branchIdx parentIndex IsLeafEdge
  split_ifs <;> omega

/-- The last spine edge `p_{g-1} u_g`. -/
theorem coreIncidence_farSpine (m : ℕ) (v : Fin (4 * (m + 1) + 2)) (e : Fin (6 * (m + 1) + 3))
    (he : e.val = 6 * m + 7) :
    coreIncidence (catCore (m + 1)) v e =
      (if v.val = 4 * m + 3 then 1 else 0) + (if v.val = 4 * m + 5 then 1 else 0) := by
  rw [coreIncidence_catCore_val]
  unfold catTailVal catHeadVal branchIdx parentIndex IsLeafEdge
  split_ifs <;> omega

/-- The loop at `u_g`, the exceptional leaf slot `6M+2`. -/
theorem coreIncidence_farLast (m : ℕ) (v : Fin (4 * (m + 1) + 2)) (e : Fin (6 * (m + 1) + 3))
    (he : e.val = 6 * m + 8) :
    coreIncidence (catCore (m + 1)) v e = if v.val = 4 * m + 5 then 2 else 0 := by
  rw [coreIncidence_catCore_val]
  unfold catTailVal catHeadVal branchIdx parentIndex IsLeafEdge
  split_ifs <;> omega

/-- **The two swapped vertices meet no other slot.**  Away from the last four
slots, neither `u_{g-1}` nor `u_g` is incident. -/
theorem coreIncidence_farVtx_zero (m : ℕ) (v : Fin (4 * (m + 1) + 2))
    (e : Fin (6 * (m + 1) + 3)) (he : e.val ≤ 6 * m + 4)
    (hv : v.val = 4 * m + 4 ∨ v.val = 4 * m + 5) :
    coreIncidence (catCore (m + 1)) v e = 0 := by
  rw [coreIncidence_catCore_val]
  unfold catTailVal catHeadVal branchIdx parentIndex IsLeafEdge
  have hlt := e.isLt
  split_ifs <;> omega

/-! ## 2.  The far end swap -/

/-- The slot component of the far end swap: `(6M-1  6M+1)(6M  6M+2)`. -/
def farSwapSlotFun (m : ℕ) (e : Fin (6 * (m + 1) + 3)) : Fin (6 * (m + 1) + 3) :=
  if e.val = 6 * m + 5 then ⟨6 * m + 7, by omega⟩
  else if e.val = 6 * m + 6 then ⟨6 * m + 8, by omega⟩
  else if e.val = 6 * m + 7 then ⟨6 * m + 5, by omega⟩
  else if e.val = 6 * m + 8 then ⟨6 * m + 6, by omega⟩
  else e

theorem farSwapSlotFun_val (m : ℕ) (e : Fin (6 * (m + 1) + 3)) :
    (farSwapSlotFun m e).val =
      if e.val = 6 * m + 5 then 6 * m + 7 else if e.val = 6 * m + 6 then 6 * m + 8
        else if e.val = 6 * m + 7 then 6 * m + 5 else if e.val = 6 * m + 8 then 6 * m + 6
          else e.val := by
  unfold farSwapSlotFun
  split_ifs <;> rfl

theorem farSwapSlotFun_involutive (m : ℕ) : Function.Involutive (farSwapSlotFun m) := by
  intro e
  apply Fin.ext
  rw [farSwapSlotFun_val, farSwapSlotFun_val]
  split_ifs <;> first | contradiction | omega

/-- The vertex component of the far end swap: `(4M  4M+1)`. -/
def farSwapVtxFun (m : ℕ) (v : Fin (4 * (m + 1) + 2)) : Fin (4 * (m + 1) + 2) :=
  if v.val = 4 * m + 4 then ⟨4 * m + 5, by omega⟩
  else if v.val = 4 * m + 5 then ⟨4 * m + 4, by omega⟩ else v

theorem farSwapVtxFun_val (m : ℕ) (v : Fin (4 * (m + 1) + 2)) :
    (farSwapVtxFun m v).val =
      if v.val = 4 * m + 4 then 4 * m + 5 else if v.val = 4 * m + 5 then 4 * m + 4 else v.val := by
  unfold farSwapVtxFun
  split_ifs <;> rfl

theorem farSwapVtxFun_involutive (m : ℕ) : Function.Involutive (farSwapVtxFun m) := by
  intro v
  apply Fin.ext
  rw [farSwapVtxFun_val, farSwapVtxFun_val]
  split_ifs <;> first | contradiction | omega

theorem farSwap_incidence (m : ℕ) (v : Fin (4 * (m + 1) + 2)) (e : Fin (6 * (m + 1) + 3)) :
    coreIncidence (catCore (m + 1)) (farSwapVtxFun m v) (farSwapSlotFun m e) =
      coreIncidence (catCore (m + 1)) v e := by
  have hlt := e.isLt
  rcases (show e.val ≤ 6 * m + 4 ∨ e.val = 6 * m + 5 ∨ e.val = 6 * m + 6 ∨
      e.val = 6 * m + 7 ∨ e.val = 6 * m + 8 by omega) with h | h | h | h | h
  · have hfix : farSwapSlotFun m e = e := by
      apply Fin.ext
      rw [farSwapSlotFun_val]
      split_ifs <;> omega
    rw [hfix]
    rcases (show v.val = 4 * m + 4 ∨ v.val = 4 * m + 5 ∨
        (v.val ≠ 4 * m + 4 ∧ v.val ≠ 4 * m + 5) by omega) with hx | hx | hx
    · rw [coreIncidence_farVtx_zero _ _ _ h (Or.inl hx),
        coreIncidence_farVtx_zero _ _ _ h
          (by rw [farSwapVtxFun_val, if_pos hx]; exact Or.inr rfl)]
    · rw [coreIncidence_farVtx_zero _ _ _ h (Or.inr hx),
        coreIncidence_farVtx_zero _ _ _ h
          (by rw [farSwapVtxFun_val, if_neg (by omega), if_pos hx]; exact Or.inl rfl)]
    · have hvf : farSwapVtxFun m v = v := by
        apply Fin.ext
        rw [farSwapVtxFun_val, if_neg hx.1, if_neg hx.2]
      rw [hvf]
  · rw [coreIncidence_farSpine _ _ _ (by rw [farSwapSlotFun_val, if_pos h]),
      coreIncidence_farStem _ _ _ h, farSwapVtxFun_val]
    split_ifs <;> omega
  · rw [coreIncidence_farLast _ _ _ (by rw [farSwapSlotFun_val, if_neg (by omega), if_pos h]),
      coreIncidence_farLoop _ _ _ h, farSwapVtxFun_val]
    split_ifs <;> omega
  · rw [coreIncidence_farStem _ _ _
        (by rw [farSwapSlotFun_val, if_neg (by omega), if_neg (by omega), if_pos h]),
      coreIncidence_farSpine _ _ _ h, farSwapVtxFun_val]
    split_ifs <;> omega
  · rw [coreIncidence_farLoop _ _ _
        (by rw [farSwapSlotFun_val, if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_pos h]),
      coreIncidence_farLast _ _ _ h, farSwapVtxFun_val]
    split_ifs <;> omega

/-- **The far end swap of the caterpillar core**, for every even genus at least
four: the exchange of the two loops hanging at the *far* end of the spine,
together with their two edges to the last spine vertex `p_{g-1}`.  This is the
mirror of `SlopeRigidity.endSwap`, and the relabelling
`BallotStabiliserReduction.right_end_determined` names in its second
alternative. -/
def farSwap (m : ℕ) : Relabel (catCore (m + 1)) (catCore (m + 1)) where
  slot := (farSwapSlotFun_involutive m).toPerm _
  vtx := (farSwapVtxFun_involutive m).toPerm _
  incidence := farSwap_incidence m

@[simp] theorem farSwap_slot_apply (m : ℕ) (e : Fin (6 * (m + 1) + 3)) :
    (farSwap m).slot e = farSwapSlotFun m e := rfl

@[simp] theorem farSwap_slot_symm_apply (m : ℕ) (e : Fin (6 * (m + 1) + 3)) :
    (farSwap m).slot.symm e = farSwapSlotFun m e := rfl

@[simp] theorem farSwap_vtx_apply (m : ℕ) (v : Fin (4 * (m + 1) + 2)) :
    (farSwap m).vtx v = farSwapVtxFun m v := rfl

theorem farSwap_slot_val (m : ℕ) (e : Fin (6 * (m + 1) + 3)) :
    ((farSwap m).slot e).val =
      if e.val = 6 * m + 5 then 6 * m + 7 else if e.val = 6 * m + 6 then 6 * m + 8
        else if e.val = 6 * m + 7 then 6 * m + 5 else if e.val = 6 * m + 8 then 6 * m + 6
          else e.val := by
  rw [farSwap_slot_apply, farSwapSlotFun_val]

/-- **The far end swap is not the identity relabelling.** -/
theorem farSwap_ne_refl (m : ℕ) : ¬ ∀ e, (farSwap m).slot e = e := by
  intro h
  have h0 : ((farSwap m).slot ⟨6 * m + 5, by omega⟩).val = 6 * m + 7 := by
    rw [farSwap_slot_val]; exact if_pos rfl
  rw [h ⟨6 * m + 5, by omega⟩] at h0
  exact absurd (show (6 * m + 5 : ℕ) = 6 * m + 7 from h0) (by omega)

/-- **The far end swap is supported at the far end of the spine**: it fixes
every slot of index at most `6M-2`. -/
theorem farSwap_slot_of_le (m : ℕ) (e : Fin (6 * (m + 1) + 3)) (he : e.val ≤ 6 * m + 4) :
    (farSwap m).slot e = e := by
  apply Fin.ext
  rw [farSwap_slot_val]
  split_ifs <;> omega

/-- **The far end swap lies in the identity branch**: it fixes every interior
spine slot, since those are the slots `3k+4` with `k < 2M-1`, all of index at
most `6M-2 = 6m+4`. -/
theorem innerIndex_farSwap (m k : ℕ) (hk : k < 2 * (m + 1) - 1) :
    BallotOrbit.innerIndex (farSwap m) k = k := by
  rw [BallotOrbit.innerIndex_eq _ hk]
  have h : (farSwap m).slot.symm (BallotOrbit.innerSlot (m + 1) k hk) =
      BallotOrbit.innerSlot (m + 1) k hk := by
    rw [farSwap_slot_symm_apply]
    apply Fin.ext
    rw [farSwapSlotFun_val, BallotOrbit.innerSlot_val]
    split_ifs <;> omega
  rw [h, BallotOrbit.innerSlot_val]
  omega

/-- The far end swap makes the second alternative of
`BallotStabiliserReduction.right_end_determined` non-vacuous: it sends the last
spine slot `6M+1` to the last stem `6M-1`. -/
theorem farSwap_slot_far (m : ℕ) (e : Fin (6 * (m + 1) + 3)) (he : e.val = 6 * m + 7) :
    ((farSwap m).slot e).val = 6 * m + 5 := by
  rw [farSwap_slot_val, if_neg (by omega), if_neg (by omega), if_pos he]


/-! ## 3.  The far end of the ballot datum: both partitions are preserved on the nose

This is where the far end differs from the near end.  At the *near* end the
identity sheet layer does not work, and `BallotEndSwapSheetIso` carries the
transposition `(cum s 1, cum s 2)`.  At the far end no such adjustment is needed: all four
moved target vertices and all four moved occurrences sit past the last spine
edge, where `cum` has already reached its maximum `m+2`, so every moved block
is the same bridge pair `{0, m+2}` or the same singleton `{0}`.
-/

section FarPartitions

variable {m : ℕ} (s : Slopes (2 * (m + 1 + 1)))

/-- Past the last spine edge the up-step counter is constant at its maximum. -/
theorem cum_far : ∀ i : ℕ, 2 * m + 3 ≤ i → s.cum i = m + 2 := by
  intro i
  induction i with
  | zero => intro h; omega
  | succ j ih =>
    intro h
    rcases Nat.lt_or_ge j (2 * m + 3) with hlt | hge
    · have h0 := Slopes.cum_last s (m := m + 1) rfl
      rw [show 2 * (m + 1 + 1) - 1 = j + 1 by omega] at h0
      exact h0
    · rw [Slopes.cum_of_ge s (show 2 * (m + 1 + 1) - 1 ≤ j by omega)]
      exact ih (by omega)

/-- **Every spine block past the last spine edge is the bridge pair
`{0, m+2}`.** -/
theorem spineMem_far {i : ℕ} (hi : 2 * m + 3 ≤ i) (k : ℕ) :
    s.SpineMem i k ↔ (k = 0 ∨ k = m + 2) := by
  have hslope : s.slope i = 2 := Slopes.slope_of_ge s (by omega)
  have hcum := cum_far s i hi
  unfold Slopes.SpineMem
  rw [hslope, hcum]
  omega

/-- The same for the bridge pairs themselves. -/
theorem pairMem_far {i : ℕ} (hi : 2 * m + 3 ≤ i) (k : ℕ) :
    s.PairMem i k ↔ (k = 0 ∨ k = m + 2) := by
  unfold Slopes.PairMem
  rw [cum_far s i hi]

/-- And for the last spine vertex block. -/
theorem vertMem_far {i : ℕ} (hi : 2 * m + 4 ≤ i) (k : ℕ) :
    s.VertMem i k ↔ (k = 0 ∨ k = m + 2) := by
  unfold Slopes.VertMem
  rw [spineMem_far s (show 2 * m + 3 ≤ i - 1 by omega) k, spineMem_far s (by omega) k]
  tauto

/-- **The four moved target vertices all carry the bridge pair `{0, m+2}`** --
`u_{g-1} = 6M`, `v_{g-1} = 6M+1`, `u_g = 6M+2` and `v_g = 6M+3`.  Note that
`u_g` is a *junction* (its index is `2 mod 3`), so its block is a `VertMem`
rather than a `PairMem`; past the last spine edge the two agree. -/
theorem vertPred_far (a : ℕ) (ha : 6 * m + 6 ≤ a) (ha' : a ≤ 6 * m + 9) (k : ℕ) :
    VertPred (m + 1) s a k ↔ (k = 0 ∨ k = m + 2) := by
  by_cases h : a % 3 = 2
  · rw [vertPred_junction s h k]
    exact vertMem_far s (show 2 * m + 4 ≤ lolli a by unfold lolli; omega) k
  · rw [vertPred_pair s h k]
    exact pairMem_far s (show 2 * m + 3 ≤ lolli a by unfold lolli; omega) k

/-- **The last stem and the last spine edge carry the same bridge pair.** -/
theorem edgePred_farPair (e : ℕ) (he : e = 6 * m + 5 ∨ e = 6 * m + 7) (k : ℕ) :
    EdgePred (m + 1) s e k ↔ (k = 0 ∨ k = m + 2) := by
  rcases he with h | h
  · rw [edgePred_stem s (show e % 3 = 2 by omega) (show e ≠ 6 * (m + 1) + 2 by omega) k]
    exact pairMem_far s (show 2 * m + 3 ≤ (e + 4) / 3 by omega) k
  · rw [edgePred_spine s (show e % 3 = 1 by omega) k]
    exact spineMem_far s (show 2 * m + 3 ≤ (e + 2) / 3 by omega) k

/-- **The two loops at the far end carry the discrete partition**, as every leaf
edge does. -/
theorem edgePred_farLeaf (e : ℕ) (he : e = 6 * m + 6 ∨ e = 6 * m + 8) (k : ℕ) :
    EdgePred (m + 1) s e k ↔ k = 0 := by
  rcases he with h | h
  · exact edgePred_leaf s (Or.inl (by omega)) k
  · exact edgePred_leaf s (Or.inr (by omega)) k

theorem ballotVertexPart_far (v : (catTree (m + 1)).V) (hv : 6 * m + 6 ≤ v.val) :
    ballotVertexPart (m + 1) s v = pairPart (m + 1) (m + 2) :=
  catStar_eq_pairPart _ _ (vertPred_far s v.val hv (by have := v.isLt; omega))

theorem ballotEdgePart_farPair (i : Fin (6 * (m + 1) + 3))
    (hi : i.val = 6 * m + 5 ∨ i.val = 6 * m + 7) :
    ballotEdgePart (m + 1) s (occ (m + 1) i) = pairPart (m + 1) (m + 2) := by
  show catStar (m + 1) (EdgePred (m + 1) s (edgeIndex (m + 1) (occ (m + 1) i))) = _
  rw [edgeIndex_occ]
  exact catStar_eq_pairPart _ _ (edgePred_farPair s i.val hi)

theorem ballotEdgePart_farLeaf (i : Fin (6 * (m + 1) + 3))
    (hi : i.val = 6 * m + 6 ∨ i.val = 6 * m + 8) :
    ballotEdgePart (m + 1) s (occ (m + 1) i) = SheetPartition.discrete (m + 1 + 2) := by
  show catStar (m + 1) (EdgePred (m + 1) s (edgeIndex (m + 1) (occ (m + 1) i))) = _
  rw [edgeIndex_occ]
  exact catStar_eq_discrete _ (edgePred_farLeaf s i.val hi)

end FarPartitions


/-! ## 4.  The target automorphism lifting the far end swap -/

/-- The involution of `catTree (m+1)` underlying the far end swap:
`u_{g-1} ↔ u_g` and `v_{g-1} ↔ v_g`, i.e. `6M ↔ 6M+2` and `6M+1 ↔ 6M+3`, with
every other target vertex fixed. -/
def farTgtFun (m : ℕ) (v : (catTree (m + 1)).V) : (catTree (m + 1)).V :=
  ⟨(if v.val = 6 * m + 6 then 6 * m + 8 else if v.val = 6 * m + 7 then 6 * m + 9
      else if v.val = 6 * m + 8 then 6 * m + 6 else if v.val = 6 * m + 9 then 6 * m + 7
      else v.val), by have := v.isLt; split_ifs <;> omega⟩

theorem farTgtFun_val (m : ℕ) (v : (catTree (m + 1)).V) :
    (farTgtFun m v).val =
      if v.val = 6 * m + 6 then 6 * m + 8 else if v.val = 6 * m + 7 then 6 * m + 9
        else if v.val = 6 * m + 8 then 6 * m + 6 else if v.val = 6 * m + 9 then 6 * m + 7
          else v.val := rfl

/-- Away from the four moved vertices the involution is the identity. -/
theorem farTgtFun_fix (m : ℕ) (v : (catTree (m + 1)).V) (h : v.val ≤ 6 * m + 5) :
    farTgtFun m v = v := by
  apply Fin.ext
  rw [farTgtFun_val, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem farTgtFun_involutive (m : ℕ) : Function.Involutive (farTgtFun m) := by
  intro v
  apply Fin.ext
  rw [farTgtFun_val, farTgtFun_val]
  split_ifs <;> first | contradiction | omega

/-- The involution, as a permutation of the target vertices. -/
def farTgtEquiv (m : ℕ) : (catTree (m + 1)).V ≃ (catTree (m + 1)).V :=
  (farTgtFun_involutive m).toPerm _

@[simp] theorem farTgtEquiv_apply (m : ℕ) (v : (catTree (m + 1)).V) :
    farTgtEquiv m v = farTgtFun m v := rfl

/-- The far end swap on target occurrences: `farSwap m`'s slot permutation, read
through the occurrence dictionary. -/
noncomputable def farEdgeEquiv (m : ℕ) :
    (catTree (m + 1)).edges ≃ (catTree (m + 1)).edges :=
  (catEdgeEquiv (m + 1)).symm.trans ((farSwap m).slot.trans (catEdgeEquiv (m + 1)))

theorem farEdgeEquiv_occ (m : ℕ) (i : Fin (6 * (m + 1) + 3)) :
    farEdgeEquiv m (occ (m + 1) i) = occ (m + 1) ((farSwap m).slot i) := by
  show catEdgeEquiv (m + 1)
    ((farSwap m).slot ((catEdgeEquiv (m + 1)).symm (catEdgeEquiv (m + 1) i))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem farEdgeEquiv_symm_apply (m : ℕ) (e : (catTree (m + 1)).edges) :
    (catEdgeEquiv (m + 1)).symm (farEdgeEquiv m e) =
      (farSwap m).slot ((catEdgeEquiv (m + 1)).symm e) := by
  show (catEdgeEquiv (m + 1)).symm
    (catEdgeEquiv (m + 1) ((farSwap m).slot ((catEdgeEquiv (m + 1)).symm e))) = _
  rw [Equiv.symm_apply_apply]

/-- The arithmetic behind the tail half of `farSwap_ends`. -/
theorem farEnds_fst_aux (m j : ℕ) (hj : j ≤ 6 * m + 8) :
    parentIndex ((if j = 6 * m + 5 then 6 * m + 7 else if j = 6 * m + 6 then 6 * m + 8
        else if j = 6 * m + 7 then 6 * m + 5 else if j = 6 * m + 8 then 6 * m + 6 else j) + 1) =
      (if parentIndex (j + 1) = 6 * m + 6 then 6 * m + 8
        else if parentIndex (j + 1) = 6 * m + 7 then 6 * m + 9
        else if parentIndex (j + 1) = 6 * m + 8 then 6 * m + 6
        else if parentIndex (j + 1) = 6 * m + 9 then 6 * m + 7 else parentIndex (j + 1)) := by
  unfold parentIndex
  split_ifs <;> omega

/-- The arithmetic behind the head half of `farSwap_ends`. -/
theorem farEnds_snd_aux (m j : ℕ) :
    (if j = 6 * m + 5 then 6 * m + 7 else if j = 6 * m + 6 then 6 * m + 8
        else if j = 6 * m + 7 then 6 * m + 5 else if j = 6 * m + 8 then 6 * m + 6 else j) + 1 =
      (if j + 1 = 6 * m + 6 then 6 * m + 8 else if j + 1 = 6 * m + 7 then 6 * m + 9
        else if j + 1 = 6 * m + 8 then 6 * m + 6 else if j + 1 = 6 * m + 9 then 6 * m + 7
          else j + 1) := by
  split_ifs <;> omega

/-- **The far end swap preserves unordered endpoints.**  Four moved occurrences
-- the last stem `p_{g-1} u_{g-1}`, the loop `u_{g-1} v_{g-1}`, the last spine
edge `p_{g-1} u_g` and the loop `u_g v_g` -- and everything of index at most
`6M-2` is fixed on the nose.  Unlike the near end, all four moved occurrences
keep their storage orientation, so every case is the `Or.inl` branch. -/
theorem farSwap_ends (m : ℕ) (edge : (catTree (m + 1)).edges) :
    UnorderedEnds (farTgtEquiv m) (edge : (catTree (m + 1)).V × (catTree (m + 1)).V)
      (farEdgeEquiv m edge : (catTree (m + 1)).V × (catTree (m + 1)).V) := by
  obtain ⟨i, rfl⟩ := occ_surj (m + 1) edge
  rw [farEdgeEquiv_occ]
  have hlt := i.isLt
  refine Or.inl (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
  · simp only [farTgtEquiv_apply, farTgtFun_val, occ_fst_val, farSwap_slot_val]
    exact farEnds_fst_aux m i.val (by omega)
  · simp only [farTgtEquiv_apply, farTgtFun_val, occ_snd_val, farSwap_slot_val]
    exact farEnds_snd_aux m i.val


/-! ## 5.  The self-isomorphism of the ballot gluing datum

The near end needs a genuine sheet transposition
(`BallotEndSwapSheetIso.bSwap`, non-trivial by `bSwap_six_ne_refl`); §3 shows the
far end does not.  So the far-end isomorphism is built by the same
partition-preservation route `SlopeRigidity.endSwapSheetIso` uses for
the caterpillar datum, with the identity sheet permutation throughout.
-/

section FarIso

variable {m : ℕ} (s : Slopes (2 * (m + 1 + 1)))

/-- **The far end swap is a self-isomorphism of the ballot gluing datum**, at
every even genus at least four and for **every** slope sequence, with the
identity sheet permutation at every target vertex and every occurrence. -/
noncomputable def bFarSwapDatumIso :
    GeometricDatumIso (ballotDatum (m + 1) s) (ballotDatum (m + 1) s) where
  targetVertex := farTgtEquiv m
  targetEdge := farEdgeEquiv m
  ends := farSwap_ends m
  vertexPerm _ := Equiv.refl _
  edgePerm _ := Equiv.refl _
  vertexPartition v := by
    show ballotVertexPart (m + 1) s (farTgtEquiv m v) =
      (ballotVertexPart (m + 1) s v).relabel (Equiv.refl _)
    rw [Transport.DatumIso.relabel_refl]
    rcases (show v.val ≤ 6 * m + 5 ∨ 6 * m + 6 ≤ v.val by omega) with h | h
    · rw [show farTgtEquiv m v = v from farTgtFun_fix m v h]
    · rw [ballotVertexPart_far s _
          (show 6 * m + 6 ≤ (farTgtEquiv m v).val by
            rw [farTgtEquiv_apply, farTgtFun_val]; split_ifs <;> omega),
        ballotVertexPart_far s v h]
  edgePartition e := by
    obtain ⟨i, rfl⟩ := occ_surj (m + 1) e
    show ballotEdgePart (m + 1) s (farEdgeEquiv m (occ (m + 1) i)) =
      (ballotEdgePart (m + 1) s (occ (m + 1) i)).relabel (Equiv.refl _)
    rw [Transport.DatumIso.relabel_refl, farEdgeEquiv_occ]
    have hlt := i.isLt
    rcases (show i.val ≤ 6 * m + 4 ∨ i.val = 6 * m + 5 ∨ i.val = 6 * m + 6 ∨
        i.val = 6 * m + 7 ∨ i.val = 6 * m + 8 by omega) with h | h | h | h | h
    · rw [farSwap_slot_of_le m i h]
    · rw [ballotEdgePart_farPair s _
          (Or.inr (by rw [farSwap_slot_val, if_pos h])),
        ballotEdgePart_farPair s i (Or.inl h)]
    · rw [ballotEdgePart_farLeaf s _
          (Or.inr (by rw [farSwap_slot_val, if_neg (by omega), if_pos h])),
        ballotEdgePart_farLeaf s i (Or.inl h)]
    · rw [ballotEdgePart_farPair s _
          (Or.inl (by rw [farSwap_slot_val, if_neg (by omega), if_neg (by omega), if_pos h])),
        ballotEdgePart_farPair s i (Or.inr h)]
    · rw [ballotEdgePart_farLeaf s _
          (Or.inl (by
            rw [farSwap_slot_val, if_neg (by omega), if_neg (by omega), if_neg (by omega),
              if_pos h])),
        ballotEdgePart_farLeaf s i (Or.inr h)]
  compatible _ _ _ _ := rfl

@[simp] theorem bFarSwapDatumIso_targetVertex :
    (bFarSwapDatumIso s).targetVertex = farTgtEquiv m := rfl

@[simp] theorem bFarSwapDatumIso_targetEdge :
    (bFarSwapDatumIso s).targetEdge = farEdgeEquiv m := rfl

/-- **The sheet layer of the far-end isomorphism is trivial.**  This is the
contrast with the near end, where the identity sheet layer does not work and
`BallotEndSwapSheetIso.bSwap_six_ne_refl` records that the sheet permutation used
there is a genuine transposition. -/
@[simp] theorem bFarSwapDatumIso_vertexPerm (v : (catTree (m + 1)).V) :
    (bFarSwapDatumIso s).vertexPerm v = Equiv.refl _ := rfl

@[simp] theorem bFarSwapDatumIso_edgePerm (e : (catTree (m + 1)).edges) :
    (bFarSwapDatumIso s).edgePerm e = Equiv.refl _ := rfl

end FarIso

/-! ### The two `overCore` equations of `SlopeRigidity.Realizes` -/

/-- The core involution `(4M  4M+1)` intertwines `branchIdx` with the target
involution, at every **branch** target index.  Unlike the near-end analogue
`SlopeRigidity.endSwapVtx_branchIdx`, a branch hypothesis really is needed: the
last folded tip `v_g = 6M+3` has `branchIdx (6M+3) = 4M+2`, which is not a core
vertex at all, so the identity fails at the one index `6M+1` that is sent
there. -/
theorem farSwapVtx_branchIdx (m v : ℕ) (h1 : v % 3 ≠ 1) (h2 : v ≠ 6 * m + 9)
    (h3 : v ≤ 6 * m + 9) :
    (if branchIdx (if v = 6 * m + 6 then 6 * m + 8 else if v = 6 * m + 7 then 6 * m + 9
        else if v = 6 * m + 8 then 6 * m + 6 else if v = 6 * m + 9 then 6 * m + 7 else v)
          = 4 * m + 4 then 4 * m + 5
      else if branchIdx (if v = 6 * m + 6 then 6 * m + 8 else if v = 6 * m + 7 then 6 * m + 9
        else if v = 6 * m + 8 then 6 * m + 6 else if v = 6 * m + 9 then 6 * m + 7 else v)
          = 4 * m + 5 then 4 * m + 4
      else branchIdx (if v = 6 * m + 6 then 6 * m + 8 else if v = 6 * m + 7 then 6 * m + 9
        else if v = 6 * m + 8 then 6 * m + 6 else if v = 6 * m + 9 then 6 * m + 7 else v))
      = branchIdx v := by
  unfold branchIdx
  split_ifs <;> first | contradiction | omega

section FarRealizes

variable {m : ℕ} (s : Slopes (2 * (m + 1 + 1)))

/-- **The row dictionary moves by the slot part of the far end swap.** -/
theorem bFarSwapDatumIso_rowIndex (hconn : (ballotDatum (m + 1) s).Connected)
    (edge : NonDanglingEdge (ballotDatum (m + 1) s)) :
    (ballotLabelling (m + 1) s).row ((bFarSwapDatumIso s).stablePathEquiv hconn edge.stablePath) =
      (farSwap m).slot ((ballotLabelling (m + 1) s).row edge.stablePath) := by
  rw [GeometricDatumIso.stablePathEquiv_mk]
  show (catEdgeEquiv (m + 1)).symm (farEdgeEquiv m edge.1.1.1) =
    (farSwap m).slot ((catEdgeEquiv (m + 1)).symm edge.1.1.1)
  exact farEdgeEquiv_symm_apply m _

/-- **The row half of `Realizes`**, the far end swap being an involution on
slots. -/
theorem bFarSwapDatumIso_overCore_row (hconn : (ballotDatum (m + 1) s).Connected)
    (path : StablePath (ballotDatum (m + 1) s)) :
    (farSwap m).slot
        ((ballotIdent (m + 1) s).row ((bFarSwapDatumIso s).stablePathEquiv hconn path)) =
      (ballotIdent (m + 1) s).row path := by
  induction path using Quot.inductionOn with
  | h edge =>
    show (farSwap m).slot ((ballotLabelling (m + 1) s).row
        ((bFarSwapDatumIso s).stablePathEquiv hconn edge.stablePath)) =
      (ballotLabelling (m + 1) s).row edge.stablePath
    rw [bFarSwapDatumIso_rowIndex s hconn edge]
    exact farSwapSlotFun_involutive m _

/-- **The vertex half of `Realizes`.** -/
theorem bFarSwapDatumIso_overCore_vertex (hconn : (ballotDatum (m + 1) s).Connected)
    (b : BranchVertex (ballotDatum (m + 1) s)) :
    (farSwap m).vtx
        ((ballotIdent (m + 1) s).vertex ((bFarSwapDatumIso s).branchVertexEquiv hconn b)) =
      (ballotIdent (m + 1) s).vertex b := by
  have hbr := (bEq_bCore_of_branch s b.2).2
  apply Fin.ext
  show (farSwapVtxFun m ((ballotIdent (m + 1) s).vertex
      ((bFarSwapDatumIso s).branchVertexEquiv hconn b))).val = branchIdx b.1.1.1.val
  rw [farSwapVtxFun_val,
    show ((ballotIdent (m + 1) s).vertex ((bFarSwapDatumIso s).branchVertexEquiv hconn b)).val =
      branchIdx (farTgtFun m b.1.1.1).val from rfl,
    farTgtFun_val]
  exact farSwapVtx_branchIdx m b.1.1.1.val hbr.1 (by have := hbr.2; omega)
    (by have := b.1.1.1.isLt; omega)

/-- **The far end swap is realised by every member of the ballot family**, at
every even genus at least four, over every slope sequence and every request
whatsoever: no positivity, no genericity.  This is
the mirror of `BallotEndSwapSheetIso.ballotRealizes_endSwap`. -/
theorem ballotRealizes_farSwap (request : Fin (6 * (m + 1) + 3) → ℚ) :
    Realizes (farSwap m) (ballotFamilyMember (m + 1) request s) :=
  ⟨bFarSwapDatumIso s, bFarSwapDatumIso_overCore_vertex s _, bFarSwapDatumIso_overCore_row s _⟩

end FarRealizes



/-! ## 6.  Composing the two end swaps

`BallotStabiliserReduction.right_end_determined` leaves the far branch with
**two** members, not one: the far end swap itself and its product with the near
end swap.  `Realizes` is closed under composition, so the near-end theorem
`BallotEndSwapSheetIso.ballotRealizes_endSwap` and §5 together cover both.
-/

section Compose

variable {n p degree : ℕ} {c : Core n p} {y : Fin p → ℚ}

/-- The composite of two core relabellings. -/
def relabelComp (d₁ d₂ : Relabel c c) : Relabel c c where
  slot := d₂.slot.trans d₁.slot
  vtx := d₂.vtx.trans d₁.vtx
  incidence v e := by
    show coreIncidence c (d₁.vtx (d₂.vtx v)) (d₁.slot (d₂.slot e)) = coreIncidence c v e
    rw [d₁.incidence, d₂.incidence]

@[simp] theorem relabelComp_slot (d₁ d₂ : Relabel c c) (e : Fin p) :
    (relabelComp d₁ d₂).slot e = d₁.slot (d₂.slot e) := rfl

@[simp] theorem relabelComp_vtx (d₁ d₂ : Relabel c c) (v : Fin n) :
    (relabelComp d₁ d₂).vtx v = d₁.vtx (d₂.vtx v) := rfl

/-- **`Realizes` is closed under composition**, through
`GeometricDatumIso.trans`. -/
theorem realizes_comp {d₁ d₂ : Relabel c c} {mem : FibreMember c y degree}
    (h₁ : Realizes d₁ mem) (h₂ : Realizes d₂ mem) : Realizes (relabelComp d₁ d₂) mem := by
  obtain ⟨a₁, hv₁, hs₁⟩ := h₁
  obtain ⟨a₂, hv₂, hs₂⟩ := h₂
  refine ⟨a₁.trans a₂, fun b ↦ ?_, fun path ↦ ?_⟩
  · rw [GeometricDatumIso.branchVertexEquiv_trans a₁ a₂ mem.fullDim.valid.1 mem.fullDim.valid.1,
      Equiv.trans_apply, relabelComp_vtx, hv₂, hv₁]
  · rw [GeometricDatumIso.stablePathEquiv_trans a₁ a₂ mem.fullDim.valid.1 mem.fullDim.valid.1,
      Equiv.trans_apply, relabelComp_slot, hs₂, hs₁]

end Compose

/-- A relabelling fixing every interior spine slot lies in the identity
branch. -/
theorem innerIndex_of_slot_fix {M : ℕ} (d : Relabel (catCore M) (catCore M))
    (h : ∀ (j : ℕ) (hj : j < 2 * M - 1),
      d.slot (BallotOrbit.innerSlot M j hj) = BallotOrbit.innerSlot M j hj)
    (k : ℕ) (hk : k < 2 * M - 1) : BallotOrbit.innerIndex d k = k := by
  rw [BallotOrbit.innerIndex_eq d hk,
    show d.slot.symm (BallotOrbit.innerSlot M k hk) = BallotOrbit.innerSlot M k hk from
      d.slot.symm_apply_eq.mpr (h k hk).symm,
    BallotOrbit.innerSlot_val]
  omega

/-- **The product of the two end swaps**: the fourth element of the Klein
four-group `BallotStabiliserReduction.identity_branch_unique` pins down. -/
def nearFarSwap (m : ℕ) : Relabel (catCore (m + 1)) (catCore (m + 1)) :=
  relabelComp (SlopeRigidity.endSwap m) (farSwap m)

theorem nearFarSwap_slot_one (m : ℕ) (e : Fin (6 * (m + 1) + 3)) (he : e.val = 1) :
    ((nearFarSwap m).slot e).val = 2 := by
  show ((SlopeRigidity.endSwap m).slot ((farSwap m).slot e)).val = 2
  have h : ((farSwap m).slot e).val = 1 := by rw [farSwap_slot_val]; split_ifs <;> omega
  rw [SlopeRigidity.endSwap_slot_val, h]
  split_ifs <;> first | contradiction | omega

theorem nearFarSwap_slot_far (m : ℕ) (e : Fin (6 * (m + 1) + 3)) (he : e.val = 6 * m + 7) :
    ((nearFarSwap m).slot e).val = 6 * m + 5 := by
  show ((SlopeRigidity.endSwap m).slot ((farSwap m).slot e)).val = 6 * m + 5
  have h : ((farSwap m).slot e).val = 6 * m + 5 := by
    rw [farSwap_slot_val]; split_ifs <;> omega
  rw [SlopeRigidity.endSwap_slot_val, h]
  split_ifs <;> first | contradiction | omega

theorem innerIndex_nearFarSwap (m k : ℕ) (hk : k < 2 * (m + 1) - 1) :
    BallotOrbit.innerIndex (nearFarSwap m) k = k := by
  refine innerIndex_of_slot_fix _ (fun j hj ↦ ?_) k hk
  show (SlopeRigidity.endSwap m).slot ((farSwap m).slot (BallotOrbit.innerSlot (m + 1) j hj)) = _
  rw [farSwap_slot_of_le m (BallotOrbit.innerSlot (m + 1) j hj)
      (by rw [BallotOrbit.innerSlot_val]; omega),
    SlopeRigidity.endSwap_slot_of_four_le m (BallotOrbit.innerSlot (m + 1) j hj)
      (by rw [BallotOrbit.innerSlot_val]; omega)]

/-- **The product of the two end swaps is realised by every ballot member**, at
every even genus at least four. -/
theorem ballotRealizes_nearFarSwap (s : Slopes (2 * (2 + 1))) (request : Fin (6 * 2 + 3) → ℚ) :
    Realizes (nearFarSwap 1) (ballotFamilyMember 2 request s) :=
  realizes_comp (BallotEndSwapSheetIso.ballotRealizes_endSwap s request)
    (ballotRealizes_farSwap s request)


/-! ## 7.  `hFar` discharged, and the identity branch of `hStab` closed -/

section GenusSix

variable (s : Slopes (2 * (2 + 1))) (request : Fin (6 * 2 + 3) → ℚ)

/-- **`hFar` at genus six, discharged.**  This is exactly the `hFar` hypothesis
of `BallotStabiliserReduction.hStab_genusSix_of_far_and_reversal`: every
relabelling in the identity branch whose far-end bit is non-trivial is realised
by the ballot member, over every slope sequence and every request.

`identity_branch_unique` says there are at most two such relabellings, and
`left_end_determined` separates them by their near-end bit: the far end swap
`farSwap 1` and its product `nearFarSwap 1` with the near end swap.  Both are
constructed here and both are realised. -/
theorem hFar_genusSix (d : Relabel (catCore 2) (catCore 2))
    (hid : ∀ a, a < 2 * 2 - 1 → BallotOrbit.innerIndex d a = a)
    (hR : ∀ e : Fin (6 * 2 + 3), e.val = 6 * 2 + 1 → (d.slot e).val = 6 * 2 - 1) :
    Realizes d (ballotFamilyMember 2 request s) := by
  rcases BallotStabiliserReduction.left_end_determined (m := 2) (by omega) d hid with hL | hL
  · have hd : d = farSwap 1 :=
      BallotStabiliserReduction.identity_branch_unique (m := 2) (by omega) d (farSwap 1) hid
        (fun a ha ↦ innerIndex_farSwap 1 a ha)
        (fun e he ↦ by
          rw [hL.2.1 e he, farSwap_slot_val]
          split_ifs <;> first | contradiction | omega)
        (fun e he ↦ by
          rw [hR e he, farSwap_slot_val]
          split_ifs <;> first | contradiction | omega)
    rw [hd]
    exact ballotRealizes_farSwap s request
  · have hd : d = nearFarSwap 1 :=
      BallotStabiliserReduction.identity_branch_unique (m := 2) (by omega) d (nearFarSwap 1) hid
        (fun a ha ↦ innerIndex_nearFarSwap 1 a ha)
        (fun e he ↦ by rw [hL.2.1 e he, nearFarSwap_slot_one 1 e he])
        (fun e he ↦ by rw [hR e he, nearFarSwap_slot_far 1 e (by omega)])
    rw [hd]
    exact ballotRealizes_nearFarSwap s request

/-- **The identity branch of `hStab` at genus six is closed entirely.**  Every
relabelling acting as the identity on the interior spine slots -- the Klein
four-group `{1, endSwap 1, farSwap 1, nearFarSwap 1}` of
`BallotStabiliserReduction.identity_branch_unique` -- is realised by every
member of the ballot family, over every slope sequence and every request.  Only
the reversal branch of `BallotStabiliserReduction.hStab_of_two_branches`
survives. -/
theorem identity_branch_realized_genusSix (d : Relabel (catCore 2) (catCore 2))
    (hid : ∀ a, a < 2 * 2 - 1 → BallotOrbit.innerIndex d a = a) :
    Realizes d (ballotFamilyMember 2 request s) := by
  rcases BallotStabiliserReduction.right_end_determined (m := 2) (by omega) d hid with hR | hR
  · rcases BallotStabiliserReduction.left_end_determined (m := 2) (by omega) d hid with hL | hL
    · have htriv := BallotStabiliserReduction.identity_branch_trivial_of_ends_fixed
        (m := 2) (by omega) d hid (fun e he ↦ hL.2.1 e he) (fun e he ↦ hR.2.2.1 e he)
      exact realizes_of_trivial htriv.1 htriv.2 _
    · have hde : d = SlopeRigidity.endSwap 1 :=
        BallotStabiliserReduction.identity_branch_unique (m := 2) (by omega) d
          (SlopeRigidity.endSwap 1) hid
          (fun a ha ↦ BallotStabiliserReduction.innerIndex_endSwap 1 a ha)
          (fun e he ↦ by
            rw [hL.2.1 e he, SlopeRigidity.endSwap_slot_apply,
              SlopeRigidity.endSwapSlotFun_val]
            split_ifs <;> omega)
          (fun e he ↦ by
            rw [hR.2.2.1 e he, SlopeRigidity.endSwap_slot_apply,
              SlopeRigidity.endSwapSlotFun_val]
            split_ifs <;> omega)
      rw [hde]
      exact BallotEndSwapSheetIso.ballotRealizes_endSwap s request
  · exact hFar_genusSix s request d hid (fun e he ↦ hR.2.2.1 e he)

end GenusSix

/-- **`hStab` at genus six, reduced to the reversal branch alone.**  This is
`BallotStabiliserReduction.hStab_genusSix_of_far_and_reversal` with its `hFar`
hypothesis supplied. -/
theorem hStab_genusSix_of_reversal (request : Fin (6 * 2 + 3) → ℚ)
    (hReversal : ∀ (s : Slopes (2 * (2 + 1))) (d : Relabel (catCore 2) (catCore 2)),
      (∀ a, a < 2 * 2 - 1 → BallotOrbit.innerIndex d a = 2 * 2 - 2 - a) →
        BallotOrbit.reverseSlopes s = s →
          Realizes d (ballotFamilyMember 2 request s)) :
    ∀ (s : Slopes (2 * (2 + 1))) (d : Relabel (catCore 2) (catCore 2)),
      (∀ slot, BallotSlopes.ballotCoreDiag 2 s (d.slot.symm slot) =
          BallotSlopes.ballotCoreDiag 2 s slot) →
        Realizes d (ballotFamilyMember 2 request s) :=
  BallotStabiliserReduction.hStab_genusSix_of_far_and_reversal request
    (fun s d hid hR ↦ hFar_genusSix s request d hid hR) hReversal

/-- **The genus-six package, with `hFar` supplied.**
`BallotStabiliserReduction.diagonalClassification_genusSix_of_far_and_reversal`
with `hFar` proved: what is left is `hSep`, `hSpine`, `hReversal` (empty off
the palindromic slope sequences) and `hSupply`.  `hReversal` itself is in turn
proved at genus six by
`BallotSpineReversalSheetIso.hReversal_genusSix`, so a caller who does not
need this theorem's exact binder shape should prefer
`BallotSpineReversalSheetIso.diagonalClassification_genusSix_of_three_residues`,
which takes only `hSep`, `hSpine` and `hSupply`. -/
theorem diagonalClassification_genusSix_of_reversal {request : Fin (6 * 2 + 3) → ℚ}
    (hSep : ∀ mem : FibreMember (catCore 2) request (2 + 2), mem.Open → mem.HasOddMult →
      SpineSingleColumn.LeafAvoidingSeparated 2 mem)
    (hSpine : ∀ mem : FibreMember (catCore 2) request (2 + 2),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        ∃ s : Slopes (2 * (2 + 1)), ∀ slot : Fin (6 * 2 + 3), ¬ IsLeafEdge 2 slot →
          mem.coreDiag slot = BallotSlopes.ballotCoreDiag 2 s slot)
    (hReversal : ∀ (s : Slopes (2 * (2 + 1))) (d : Relabel (catCore 2) (catCore 2)),
      (∀ a, a < 2 * 2 - 1 → BallotOrbit.innerIndex d a = 2 * 2 - 2 - a) →
        BallotOrbit.reverseSlopes s = s →
          Realizes d (ballotFamilyMember 2 request s))
    (hSupply : ∀ (s : Slopes (2 * (2 + 1))) (mem : FibreMember (catCore 2) request (2 + 2)),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        mem.coreDiag = BallotSlopes.ballotCoreDiag 2 s →
          Nonempty (GeometricDatumIso
            (ballotFamilyMember 2 request s).data mem.data)) :
    BallotSlopes.DiagonalClassification 2 request :=
  BallotStabiliserReduction.diagonalClassification_genusSix_of_far_and_reversal hSep hSpine
    (fun s d hid hR ↦ hFar_genusSix s request d hid hR) hReversal hSupply

end DraismaVargas.Count.BallotFarEndSwap
