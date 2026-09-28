import DraismaVargasCount.BallotOrbitStability
import DraismaVargasCount.BallotEndSwapSheetIso
import DraismaVargasCount.DiagonalClassificationGenusSix

/-!
# What the orbit dichotomy really pins: the `hStab` stabiliser, reduced

## The question this module answers

The genus-six exhaustion package `BallotSlopes.DiagonalClassification 2` is assembled
in `DiagonalClassificationGenusSix` from residues, one of which is `hStab`: *every*
`d : CoreRelabel.Relabel (catCore m) (catCore m)` stabilising a ballot core
diagonal is realised inside the corresponding ballot member's gluing datum.  This is
residue (B) of `SlopeRigidity.coreDiagRigid_iff` -- the realisation half of the
uniqueness in `prop-caterpillar-ballot`(2) of Vargas, Part II (arXiv:2609.09109) --
restricted to the ballot members.  `BallotEndSwapSheetIso` proves it at the single
relabelling `SlopeRigidity.endSwap 1`; the group `Aut (catCore m)` is not enumerated,
so the quantifier cannot be turned into a finite check directly.

**It can be reduced without enumerating that group.**
`BallotOrbit.ballotCoreDiag_relabel_eq_self_or_reverse` proves a dichotomy about
what a relabelling does to a ballot *diagonal*; its proof first proves a
dichotomy about what the relabelling does to the interior spine *slots*.
Extracted (`innerIndex_id_or_reverse`) and pushed through, that stronger statement
reduces `hStab` at genus six to **two** hypotheses, one of them about at most two
relabellings and the other empty off the palindromic slope sequences.

## The identity branch is not trivial

The natural hope -- that a relabelling acting as the identity on the interior
spine slots is the identity relabelling, so that the identity branch is free --
is **false**, and `SlopeRigidity.endSwap` is the counterexample at every even
genus at least four (`exists_nontrivial_in_identity_branch`).  The loops and
stems at the two ends of the spine are not pinned by the interior.

What *is* true is sharper than a bound on that freedom: the identity branch is
exactly the Klein four-group of the two end swaps.  A relabelling in it fixes
every slot but the eight at the two ends and every vertex but the four at the
two ends (`identity_branch_rigidity`); at each end it makes one binary choice,
and that choice determines all four slots and both vertices there
(`left_end_determined`, `right_end_determined`); and two members of the branch
agreeing on the two choices are equal (`identity_branch_unique`).  So the branch
has at most four elements.  Of those, the identity is free
(`identity_branch_trivial_of_ends_fixed`), `SlopeRigidity.endSwap 1` is realised by
`BallotEndSwapSheetIso.ballotRealizes_endSwap`, and the two with a nontrivial
far-end bit are what is left.

## How the identity branch is pinned: three local steps, no automorphism table

1.  Each interior spine slot is fixed, so `d.vtx` fixes or swaps its two ends.
    At `m ≥ 2` there are at least three of them and a swap at one contradicts
    either neighbour, so every spine vertex `1, 3, …, 4m-1` is fixed
    (`inner_vtx_straight`, `vtx_fix_odd`).
2.  An interior stem meets a fixed spine vertex, only three slots do
    (`endpoint_odd_iff`), and the other two are interior spine slots, which are
    not loop-adjacent while the stem is.  So every interior stem is fixed
    (`slot_fix_stem`), and with it its far end (`vtx_fix_even`).
3.  A relabelling preserves the self-loops and distinct loops sit at distinct
    vertices (`leaf_tail_injective`), so every interior loop is fixed
    (`slot_fix_loop`).

The same three steps run at the two ends, where the interior spine slot
adjacent to the end vertex is fixed and the remaining two slots there can only
be exchanged.

## What is proved

* `innerIndex_injOn`, `innerIndex_adjacent`, **`innerIndex_id_or_reverse`** --
  the index dichotomy, extracted from `BallotOrbit`'s proof and stated on its
  own.  Every relabelling acts on the `2m-1` interior spine slots as the
  identity or as the reversal, at every genus.
* `slot_symm_innerSlot`, `slot_innerSlot` -- the identity branch read on
  `d.slot` and `d.slot.symm`.
* `innerIndex_endSwap`, **`exists_nontrivial_in_identity_branch`** -- the end swap
  lies in the identity branch without being the identity.
* `endpoint_odd_iff`, `stem_tail_val`, `stem_head_val`, `loop_tail_val`,
  `leaf_tail_eq_iff`, `leaf_tail_injective`, `slot_one_ends`, `last_spine_ends`,
  `last_leaf_tail_val`, `loop_image_tail_val` -- the caterpillar core's local
  arithmetic.
* `vtx_of_slot_fixed`, `slot_image_endpoint`, `VtxTo`, `SlotTo`,
  `inner_vtx_dichotomy`, `inner_vtx_straight`, `vtx_fix_odd`, `slot_fix_stem`,
  `vtx_fix_even`, `slot_fix_loop` -- the three steps.
* **`identity_branch_rigidity`** -- every slot but eight and every vertex but
  four is fixed.
* `slot_at_near_vertex`, `slot_at_far_vertex`, **`left_end_determined`**,
  **`right_end_determined`** -- one binary choice at each end, and it determines
  that end completely.
* `relabel_ext`, **`identity_branch_unique`** -- the identity branch has at most
  four elements.
* `identity_branch_trivial_of_ends_fixed` -- the element with both bits trivial
  is the identity relabelling, hence free.
* `ballotCoreDiag_of_reverse_branch`, **`reverseSlopes_eq_of_stab`** -- in the
  reversal branch the stabiliser premise forces `reverseSlopes s = s`.
* **`hStab_of_two_branches`**, `hStab_genusSix_of_two_branches`,
  **`hStab_genusSix_of_far_and_reversal`** -- the reduction, at every `m` and in
  its sharpest genus-six form.
* `identity_branch_endSwap_discharged` -- `BallotEndSwapSheetIso.ballotRealizes_endSwap`,
  placed in the identity branch.
* **`diagonalClassification_genusSix_of_far_and_reversal`** -- the reduction
  plugged into `DiagonalClassificationGenusSix`'s assembly, so the genus-six
  package rests on `hSep`, `hSpine`, `hFar`, `hReversal` and `hSupply`.

## What is NOT proved here (every hypothesis, explicitly)

* **`hStab` is not proved by this file.**  What is proved here is a
  reduction: `hStab_genusSix_of_far_and_reversal` takes two hypotheses and
  neither is inhabited here.  Both are inhabited elsewhere at genus six (see
  below), which gives `BallotSpineReversalSheetIso.hStab_genusSix`.  At every other
  `m` nothing here proves `hStab`.
* **The far end swap is constructed elsewhere, not here.**  `hFar` quantifies
  over relabellings with `(d.slot ⟨13⟩).val = 11` at genus six;
  `identity_branch_unique` says there are at most two.  This file builds no
  `Relabel` with that far-end bit; `BallotFarEndSwap`
  builds `farSwap m` at every `m`, proves `Realizes` for it with identity
  sheet permutations, and proves `hFar` (`hFar_genusSix`), so the identity
  branch is closed there (`identity_branch_realized_genusSix`).  The reversal
  `Relabel` is `SpineReversal.spineReversal m`; its sheet layer
  (`hReversal`) is realised at genus six by
  `BallotSpineReversalSheetIso.hReversal_genusSix`.
* **The spine reversal is not constructed by this file either.**
  `SpineReversal` constructs it as a `Relabel` at every `m`, and
  `BallotSpineReversalSheetIso` builds the sheet isomorphism over it
  and realises the reversal branch at genus six, so that branch of
  `hStab_of_two_branches` is non-vacuous there.  At other `m`, what
  is proved about it here is only that its premise forces
  `reverseSlopes s = s`.
* **`Aut (catCore m)` is not enumerated**, and nothing here does so.  The
  statements above bound the *stabiliser branch by branch*; they say nothing
  about how many relabellings there are in the reversal branch.
* **`m ≥ 2` is used throughout §3 and §4.**  At `m = 1` there is a single
  interior spine slot, the chain argument has no second slot to run against, and
  the identity and reversal branches coincide; nothing here covers that case.
  At `m = 0` there is no interior spine slot at all.
* **Nothing about `hSep`/`hTrivalent`, `hThree`/`hSpine` or `hSupply`**, the
  other three residues of
  `DiagonalClassificationGenusSix.diagonalClassification_genusSix_of_sharp_residues`.
* No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`, no
  `decide`, no `#eval`.
-/

namespace DraismaVargas.Count.BallotStabiliserReduction

open DraismaVargas.Count
open DraismaVargas.Count.CoreRelabel
open DraismaVargas.Count.FibreCaterpillar
open DraismaVargas.Count.BallotOrbit
open DraismaVargas.LocalCases.CaterpillarPruning (IsLeafEdge)
open DraismaVargas.Count.SlopeRigidity (catCore_tail_val catCore_head_val)
open DraismaVargas.Infrastructure.CaterpillarTree (parentIndex)

variable {m : ℕ}

/-! ## 1.  The index dichotomy, extracted from the orbit proof

`BallotOrbit.ballotCoreDiag_relabel_eq_self_or_reverse` establishes a dichotomy
on the *diagonal*, but its proof first establishes a dichotomy on `innerIndex d`
-- how `d.slot.symm` moves the interior spine slots -- and then reads the
diagonal off it.  That intermediate statement is the one a stabiliser analysis
needs; here it is, on its own. -/

/-- `innerIndex d` is injective on `[0, 2m-1)`.  (The first half of the
`walk_rigid` input, extracted verbatim from
`ballotCoreDiag_relabel_eq_self_or_reverse`.) -/
theorem innerIndex_injOn (d : Relabel (catCore m) (catCore m)) :
    ∀ a b, a < 2 * m - 1 → b < 2 * m - 1 → innerIndex d a = innerIndex d b → a = b := by
  intro a b ha hb hab
  have h1 := (innerIndex_spec d ha).2
  have h2 := (innerIndex_spec d hb).2
  have heq : d.slot.symm (innerSlot m a ha) = d.slot.symm (innerSlot m b hb) :=
    Fin.ext (by omega)
  have h3 := congrArg Fin.val (d.slot.symm.injective heq)
  rw [innerSlot_val, innerSlot_val] at h3
  omega

/-- `innerIndex d` moves consecutive indices to indices at distance at most one:
the interior spine slots form a path and a relabelling preserves sharing a
vertex.  (The second half of the `walk_rigid` input.) -/
theorem innerIndex_adjacent (d : Relabel (catCore m) (catCore m)) :
    ∀ a, a + 1 < 2 * m - 1 →
      innerIndex d (a + 1) ≤ innerIndex d a + 1 ∧ innerIndex d a ≤ innerIndex d (a + 1) + 1 := by
  intro a ha
  have ha' : a < 2 * m - 1 := by omega
  have hmeet : Meet (catCore m) (innerSlot m a ha') (innerSlot m (a + 1) ha) :=
    (meet_innerSlot ha' ha).mpr ⟨by omega, by omega⟩
  have hm := (meet_relabel_symm d (innerSlot m a ha') (innerSlot m (a + 1) ha)).mpr hmeet
  rw [innerSlot_symm d ha', innerSlot_symm d ha, meet_innerSlot] at hm
  exact ⟨hm.2, hm.1⟩

/-- **The sharp dichotomy, on the index map rather than on the diagonal.**
Every `Relabel (catCore m) (catCore m)` acts on the `2m-1` interior spine slots
either as the identity or as the reversal -- at every genus, with no
automorphism table.  This is the statement
`BallotOrbit.ballotCoreDiag_relabel_eq_self_or_reverse` proves on the way to its
own conclusion; it is strictly stronger, because it is about `d.slot` and not
about what `d.slot` does to one rational-valued function. -/
theorem innerIndex_id_or_reverse (m : ℕ) (d : Relabel (catCore m) (catCore m)) :
    (∀ a, a < 2 * m - 1 → innerIndex d a = a) ∨
      (∀ a, a < 2 * m - 1 → innerIndex d a = 2 * m - 2 - a) := by
  rcases walk_rigid (innerIndex d) (innerIndex_injOn d)
    (fun a ha ↦ (innerIndex_spec d ha).1) (innerIndex_adjacent d) with h | h
  · exact Or.inl h
  · exact Or.inr fun a ha ↦ by rw [h a ha]; omega

/-- The identity branch, read on `d.slot.symm` itself. -/
theorem slot_symm_innerSlot (d : Relabel (catCore m) (catCore m))
    (hid : ∀ a, a < 2 * m - 1 → innerIndex d a = a) {k : ℕ} (hk : k < 2 * m - 1) :
    d.slot.symm (innerSlot m k hk) = innerSlot m k hk :=
  Fin.ext (by rw [(innerIndex_spec d hk).2, hid k hk, innerSlot_val])

/-- The identity branch, read on `d.slot`. -/
theorem slot_innerSlot (d : Relabel (catCore m) (catCore m))
    (hid : ∀ a, a < 2 * m - 1 → innerIndex d a = a) {k : ℕ} (hk : k < 2 * m - 1) :
    d.slot (innerSlot m k hk) = innerSlot m k hk := by
  conv_lhs => rw [← slot_symm_innerSlot d hid hk]
  exact d.slot.apply_symm_apply _

/-! ## 2.  The identity branch does **not** pin `d`

One might hope that a
relabelling acting as the identity on the interior spine slots is the identity
relabelling, so that `hStab`'s identity branch would be the trivial obligation.
It is not: `SlopeRigidity.endSwap m` -- the exchange of the two loops at the
near end of the spine -- fixes every slot of index at least four
(`SlopeRigidity.endSwap_slot_of_four_le`), hence every interior spine slot,
while moving slot `0` to slot `3`. -/

/-- **The end swap lies in the identity branch.** -/
theorem innerIndex_endSwap (m k : ℕ) (hk : k < 2 * (m + 1) - 1) :
    innerIndex (SlopeRigidity.endSwap m) k = k := by
  rw [innerIndex_eq _ hk]
  have h : (SlopeRigidity.endSwap m).slot.symm (innerSlot (m + 1) k hk) =
      innerSlot (m + 1) k hk := by
    rw [SlopeRigidity.endSwap_slot_symm_apply]
    apply Fin.ext
    rw [SlopeRigidity.endSwapSlotFun_val, innerSlot_val]
    split_ifs <;> first | contradiction | omega
  rw [h, innerSlot_val]
  omega

/-- **So the identity branch does not collapse.**  At every even genus at least
four there is a relabelling acting as the identity on every interior spine slot
which is not the identity on slots. -/
theorem exists_nontrivial_in_identity_branch (m : ℕ) :
    ∃ d : Relabel (catCore (m + 1)) (catCore (m + 1)),
      (∀ a, a < 2 * (m + 1) - 1 → innerIndex d a = a) ∧ ¬ ∀ e, d.slot e = e :=
  ⟨SlopeRigidity.endSwap m, fun a ha ↦ innerIndex_endSwap m a ha,
    SlopeRigidity.endSwap_ne_refl m⟩

/-! ## 3.  What the identity branch *does* pin

Everything except the two ends.  The argument is three steps, all of them local
and none of them an automorphism enumeration.

1.  Each interior spine slot is fixed, so its two ends are fixed or swapped.  At
    `m ≥ 2` there are at least three of them and a swap at one slot contradicts
    either neighbour, so **every spine vertex `1, 3, …, 4m-1` is fixed**.
2.  A stem `3j+2` with `1 ≤ j ≤ 2m-2` is loop-adjacent and meets the fixed
    spine vertex `2j+1`; the only slots at that vertex are `3j+1`, `3j+2`,
    `3j+4`, and the other two are interior spine slots, which are not
    loop-adjacent.  So **every interior stem is fixed**, and with it its far end
    `2j+2`.
3.  A relabelling preserves the self-loops, and the loop at `2j+2` is the unique
    leaf slot there, so **every interior loop is fixed**. -/

/-- **The slots at a spine vertex.**  The vertex of index `2j+1` is met by
exactly the slots `3j+1`, `3j+2` and `3j+4` -- the spine slot below it, its
stem, and the spine slot above it. -/
theorem endpoint_odd_iff (m j : ℕ) (e : Fin (6 * m + 3)) :
    (((catCore m).tail e).val = 2 * j + 1 ∨ ((catCore m).head e).val = 2 * j + 1) ↔
      (e.val = 3 * j + 1 ∨ e.val = 3 * j + 2 ∨ e.val = 3 * j + 4) := by
  have hlt := e.isLt
  rw [catCore_tail_val, catCore_head_val]
  unfold catTailVal catHeadVal branchIdx parentIndex IsLeafEdge
  split_ifs <;> omega

/-- The near end of the slot `3j+2` is the spine vertex `2j+1`. -/
theorem stem_tail_val (m j : ℕ) (e : Fin (6 * m + 3)) (hj : e.val = 3 * j + 2) :
    ((catCore m).tail e).val = 2 * j + 1 := by
  have hlt := e.isLt
  rw [catCore_tail_val]
  unfold catTailVal branchIdx parentIndex
  split_ifs <;> omega

/-- The far end of a stem `3j+2` is the loop vertex `2j+2`. -/
theorem stem_head_val (m j : ℕ) (e : Fin (6 * m + 3)) (hj : e.val = 3 * j + 2)
    (hne : e.val ≠ 6 * m + 2) :
    ((catCore m).head e).val = 2 * j + 2 := by
  have hlt := e.isLt
  have hleaf : ¬ IsLeafEdge m e := by unfold IsLeafEdge; omega
  rw [catCore_head_val]
  unfold catHeadVal
  rw [if_neg hleaf]
  unfold branchIdx
  omega

/-- The loop `3j` sits at the vertex `2j`. -/
theorem loop_tail_val (m j : ℕ) (e : Fin (6 * m + 3)) (hj : e.val = 3 * j) :
    ((catCore m).tail e).val = 2 * j := by
  have hlt := e.isLt
  rw [catCore_tail_val]
  unfold catTailVal branchIdx parentIndex
  split_ifs <;> omega

/-- **A leaf slot is determined by the vertex it sits at.** -/
theorem leaf_tail_eq_iff (m i : ℕ) (e : Fin (6 * m + 3)) (he : IsLeafEdge m e) :
    ((catCore m).tail e).val = 2 * i ↔ e.val = 3 * i := by
  have hlt := e.isLt
  rw [catCore_tail_val]
  unfold catTailVal branchIdx parentIndex
  unfold IsLeafEdge at he
  split_ifs <;> omega

/-- **Distinct leaf slots sit at distinct vertices.** -/
theorem leaf_tail_injective (m : ℕ) (e f : Fin (6 * m + 3)) (he : IsLeafEdge m e)
    (hf : IsLeafEdge m f) (h : ((catCore m).tail e).val = ((catCore m).tail f).val) :
    e.val = f.val := by
  have hlt := e.isLt
  have hlt' := f.isLt
  rw [catCore_tail_val, catCore_tail_val] at h
  unfold catTailVal branchIdx parentIndex at h
  unfold IsLeafEdge at he hf
  split_ifs at h <;> omega

/-- The near spine slot `1` runs from the near loop vertex `0` to the near spine
vertex `1`. -/
theorem slot_one_ends (m : ℕ) (e : Fin (6 * m + 3)) (h : e.val = 1) :
    ((catCore m).tail e).val = 0 ∧ ((catCore m).head e).val = 1 := by
  have hlt := e.isLt
  have hleaf : ¬ IsLeafEdge m e := by unfold IsLeafEdge; omega
  refine ⟨?_, ?_⟩
  · rw [catCore_tail_val]; unfold catTailVal branchIdx parentIndex; split_ifs <;> omega
  · rw [catCore_head_val]; unfold catHeadVal; rw [if_neg hleaf]; unfold branchIdx; omega

/-- The far spine slot `6m+1` runs from the far spine vertex `4m-1` to the last
loop vertex `4m+1`. -/
theorem last_spine_ends (m : ℕ) (hm : 1 ≤ m) (e : Fin (6 * m + 3)) (h : e.val = 6 * m + 1) :
    ((catCore m).tail e).val = 4 * m - 1 ∧ ((catCore m).head e).val = 4 * m + 1 := by
  have hlt := e.isLt
  have hleaf : ¬ IsLeafEdge m e := by unfold IsLeafEdge; omega
  refine ⟨?_, ?_⟩
  · rw [catCore_tail_val]; unfold catTailVal branchIdx parentIndex; split_ifs <;> omega
  · rw [catCore_head_val]; unfold catHeadVal; rw [if_neg hleaf]; unfold branchIdx; omega

/-- The exceptional leaf slot `6m+2` is the loop at the last vertex `4m+1`. -/
theorem last_leaf_tail_val (m : ℕ) (e : Fin (6 * m + 3)) (h : e.val = 6 * m + 2) :
    ((catCore m).tail e).val = 4 * m + 1 := by
  have hlt := e.isLt
  rw [catCore_tail_val]
  unfold catTailVal branchIdx parentIndex
  split_ifs <;> omega

/-- The image of a loop sits at the image of its vertex. -/
theorem loop_image_tail_val (d : Relabel (catCore m) (catCore m)) (e : Fin (6 * m + 3))
    (he : IsLeafEdge m e) :
    ((catCore m).tail (d.slot e)).val = (d.vtx ((catCore m).tail e)).val := by
  have hte : (catCore m).head e = (catCore m).tail e :=
    ((SlopeRigidity.catCore_tail_eq_head_iff m e).mpr he).symm
  rcases relabel_orientation d e with ⟨ha, _⟩ | ⟨_, hb⟩
  · rw [ha]
  · rw [hb, hte]

/-- A slot fixed by `d.slot` has its two ends fixed, or swapped, by `d.vtx`. -/
theorem vtx_of_slot_fixed (d : Relabel (catCore m) (catCore m)) {e : Fin (6 * m + 3)}
    (he : d.slot e = e) :
    (d.vtx ((catCore m).tail e) = (catCore m).tail e ∧
        d.vtx ((catCore m).head e) = (catCore m).head e) ∨
      (d.vtx ((catCore m).tail e) = (catCore m).head e ∧
        d.vtx ((catCore m).head e) = (catCore m).tail e) := by
  rcases relabel_orientation d e with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [he] at h1 h2
  · exact Or.inl ⟨h1.symm, h2.symm⟩
  · exact Or.inr ⟨h1.symm, h2.symm⟩

/-- If `d.vtx` fixes the vertex of index `a`, then `d.slot` carries slots at
that vertex to slots at that vertex. -/
theorem slot_image_endpoint (d : Relabel (catCore m) (catCore m)) {a : ℕ}
    (hfix : ∀ v : Fin (4 * m + 2), v.val = a → d.vtx v = v) (e : Fin (6 * m + 3))
    (he : ((catCore m).tail e).val = a ∨ ((catCore m).head e).val = a) :
    ((catCore m).tail (d.slot e)).val = a ∨ ((catCore m).head (d.slot e)).val = a := by
  rcases relabel_orientation d e with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases he with h | h
  · exact Or.inl (by rw [h1, hfix _ h]; exact h)
  · exact Or.inr (by rw [h2, hfix _ h]; exact h)
  · exact Or.inr (by rw [h1, hfix _ h]; exact h)
  · exact Or.inl (by rw [h2, hfix _ h]; exact h)

/-- `d.vtx` carries the vertex of index `a` to the vertex of index `b`. -/
def VtxTo (d : Relabel (catCore m) (catCore m)) (a b : ℕ) : Prop :=
  ∀ v : Fin (4 * m + 2), v.val = a → (d.vtx v).val = b

theorem VtxTo.unique {d : Relabel (catCore m) (catCore m)} {a b b' : ℕ} (ha : a < 4 * m + 2)
    (h : VtxTo d a b) (h' : VtxTo d a b') : b = b' := by
  have h1 := h ⟨a, ha⟩ rfl
  have h2 := h' ⟨a, ha⟩ rfl
  omega

/-- **Step 1a.**  Each interior spine slot has its two ends fixed or swapped. -/
theorem inner_vtx_dichotomy (d : Relabel (catCore m) (catCore m))
    (hid : ∀ a, a < 2 * m - 1 → innerIndex d a = a) {k : ℕ} (hk : k < 2 * m - 1) :
    (VtxTo d (2 * k + 1) (2 * k + 1) ∧ VtxTo d (2 * k + 3) (2 * k + 3)) ∨
      (VtxTo d (2 * k + 1) (2 * k + 3) ∧ VtxTo d (2 * k + 3) (2 * k + 1)) := by
  have htv := innerSlot_tail_val hk
  have hhv := innerSlot_head_val hk
  rcases vtx_of_slot_fixed d (slot_innerSlot d hid hk) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inl ⟨fun v hv ↦ ?_, fun v hv ↦ ?_⟩
    · rw [show v = (catCore m).tail (innerSlot m k hk) from Fin.ext (by omega), h1]; omega
    · rw [show v = (catCore m).head (innerSlot m k hk) from Fin.ext (by omega), h2]; omega
  · refine Or.inr ⟨fun v hv ↦ ?_, fun v hv ↦ ?_⟩
    · rw [show v = (catCore m).tail (innerSlot m k hk) from Fin.ext (by omega), h1]; omega
    · rw [show v = (catCore m).head (innerSlot m k hk) from Fin.ext (by omega), h2]; omega

/-- **Step 1b, the chain argument.**  At `m ≥ 2` there are at least three
interior spine slots, and a swap at one of them is inconsistent with either
neighbour, so no interior spine slot is swapped. -/
theorem inner_vtx_straight (hm : 2 ≤ m) (d : Relabel (catCore m) (catCore m))
    (hid : ∀ a, a < 2 * m - 1 → innerIndex d a = a) :
    ∀ k, k < 2 * m - 1 → VtxTo d (2 * k + 1) (2 * k + 1) ∧ VtxTo d (2 * k + 3) (2 * k + 3) := by
  have hbase : VtxTo d 1 1 ∧ VtxTo d 3 3 := by
    rcases inner_vtx_dichotomy d hid (show 0 < 2 * m - 1 by omega) with h | h
    · exact ⟨by simpa using h.1, by simpa using h.2⟩
    · exfalso
      have h3 : VtxTo d 3 1 := by simpa using h.2
      rcases inner_vtx_dichotomy d hid (show 1 < 2 * m - 1 by omega) with h' | h'
      · have := VtxTo.unique (d := d) (a := 3) (by omega) h3 (by simpa using h'.1)
        omega
      · have := VtxTo.unique (d := d) (a := 3) (by omega) h3 (by simpa using h'.1)
        omega
  intro k
  induction k with
  | zero => intro _; exact hbase
  | succ j ih =>
    intro hj
    have ihj := ih (by omega)
    rcases inner_vtx_dichotomy d hid hj with h | h
    · exact h
    · exfalso
      have hA : VtxTo d (2 * j + 3) (2 * j + 3) := ihj.2
      have hB : VtxTo d (2 * j + 3) (2 * (j + 1) + 3) := by
        have hx := h.1
        rw [show 2 * (j + 1) + 1 = 2 * j + 3 by omega] at hx
        exact hx
      have := VtxTo.unique (d := d) (a := 2 * j + 3) (by omega) hA hB
      omega

/-- **Step 1, the conclusion: every spine vertex is fixed.**  These are the odd
indices `1, 3, …, 4m-1`. -/
theorem vtx_fix_odd (hm : 2 ≤ m) (d : Relabel (catCore m) (catCore m))
    (hid : ∀ a, a < 2 * m - 1 → innerIndex d a = a) (v : Fin (4 * m + 2))
    (hodd : v.val % 2 = 1) (hv : v.val < 4 * m) : d.vtx v = v := by
  have hstr := inner_vtx_straight hm d hid
  apply Fin.ext
  rcases (show v.val / 2 < 2 * m - 1 ∨ v.val / 2 = 2 * m - 1 by omega) with hk | hk
  · have h := (hstr (v.val / 2) hk).1 v (by omega)
    omega
  · have h := (hstr (2 * m - 2) (by omega)).2 v (by omega)
    omega

/-- **Step 2: every interior stem is fixed.**  The stems `3j+2` with
`1 ≤ j ≤ 2m-2`, i.e. the slots `5, 8, …, 6m-4`. -/
theorem slot_fix_stem (hm : 2 ≤ m) (d : Relabel (catCore m) (catCore m))
    (hid : ∀ a, a < 2 * m - 1 → innerIndex d a = a) (e : Fin (6 * m + 3))
    (hmod : e.val % 3 = 2) (h1 : 4 ≤ e.val) (h2 : e.val ≤ 6 * m - 2) : d.slot e = e := by
  obtain ⟨j, hjeq⟩ : ∃ j, e.val = 3 * j + 2 := ⟨e.val / 3, by omega⟩
  have hjlo : 1 ≤ j := by omega
  have hjhi : j ≤ 2 * m - 2 := by omega
  have hfix : ∀ v : Fin (4 * m + 2), v.val = 2 * j + 1 → d.vtx v = v := fun v hv ↦
    vtx_fix_odd hm d hid v (by omega) (by omega)
  have hend : ((catCore m).tail e).val = 2 * j + 1 ∨ ((catCore m).head e).val = 2 * j + 1 :=
    Or.inl (stem_tail_val m j e hjeq)
  have hmem := (endpoint_odd_iff m j (d.slot e)).mp (slot_image_endpoint d hfix e hend)
  have hla : LoopAdjacent (catCore m) (d.slot e) :=
    (loopAdjacent_relabel d e).mpr ((loopAdjacent_catCore m e).mpr (by omega))
  have hla' := (loopAdjacent_catCore m (d.slot e)).mp hla
  exact Fin.ext (by omega)

/-- **Step 2b: the far end of an interior stem is fixed** -- the even vertices
`4, 6, …, 4m-2`. -/
theorem vtx_fix_even (hm : 2 ≤ m) (d : Relabel (catCore m) (catCore m))
    (hid : ∀ a, a < 2 * m - 1 → innerIndex d a = a) (v : Fin (4 * m + 2))
    (heven : v.val % 2 = 0) (h1 : 4 ≤ v.val) (h2 : v.val ≤ 4 * m - 2) : d.vtx v = v := by
  obtain ⟨j, hjeq⟩ : ∃ j, v.val = 2 * j + 2 := ⟨v.val / 2 - 1, by omega⟩
  have hjlo : 1 ≤ j := by omega
  have hjhi : j ≤ 2 * m - 2 := by omega
  have hslt : 3 * j + 2 < 6 * m + 3 := by omega
  set e : Fin (6 * m + 3) := ⟨3 * j + 2, hslt⟩ with hedef
  have hev : e.val = 3 * j + 2 := rfl
  have hfe : d.slot e = e := slot_fix_stem hm d hid e (by omega) (by omega) (by omega)
  have htv : ((catCore m).tail e).val = 2 * j + 1 := stem_tail_val m j e hev
  have hhv : ((catCore m).head e).val = 2 * j + 2 := stem_head_val m j e hev (by omega)
  rcases vtx_of_slot_fixed d hfe with ⟨_, hb⟩ | ⟨ha, _⟩
  · rw [show v = (catCore m).head e from Fin.ext (by omega), hb]
  · exfalso
    have hfx := vtx_fix_odd hm d hid ((catCore m).tail e) (by omega) (by omega)
    have := congrArg Fin.val (hfx.symm.trans ha)
    omega

/-- **Step 3: every interior loop is fixed** -- the leaf slots `6, 9, …, 6m-3`. -/
theorem slot_fix_loop (hm : 2 ≤ m) (d : Relabel (catCore m) (catCore m))
    (hid : ∀ a, a < 2 * m - 1 → innerIndex d a = a) (e : Fin (6 * m + 3))
    (hmod : e.val % 3 = 0) (h1 : 4 ≤ e.val) (h2 : e.val ≤ 6 * m - 2) : d.slot e = e := by
  obtain ⟨j, hjeq⟩ : ∃ j, e.val = 3 * j := ⟨e.val / 3, by omega⟩
  have hjlo : 2 ≤ j := by omega
  have hleaf : IsLeafEdge m e := Or.inl (by omega)
  have hleaf' : IsLeafEdge m (d.slot e) := (SlopeRigidity.relabel_isLeafEdge_iff d e).mpr hleaf
  have htv : ((catCore m).tail e).val = 2 * j := loop_tail_val m j e hjeq
  have hfx : d.vtx ((catCore m).tail e) = (catCore m).tail e :=
    vtx_fix_even hm d hid _ (by omega) (by omega) (by omega)
  have himg : ((catCore m).tail (d.slot e)).val = 2 * j := by
    rcases relabel_orientation d e with ⟨hh, _⟩ | ⟨_, hh⟩
    · rw [hh, hfx]; exact htv
    · rw [hh, show (catCore m).head e = (catCore m).tail e from
        Fin.ext (((SlopeRigidity.catCore_tail_eq_head_iff m e).mpr hleaf) ▸ rfl), hfx]
      exact htv
  exact Fin.ext (by rw [(leaf_tail_eq_iff m j (d.slot e) hleaf').mp himg]; omega)

/-- **The identity branch, in full: every slot but the eight at the two ends is
fixed, and every vertex but the four at the two ends.**

At `m = 2` (genus six) this says: `d.slot` fixes the slots `4, 5, 6, 7, 8, 9,
10`, and may only permute `{0, 1, 2, 3}` and `{11, 12, 13, 14}`; `d.vtx` fixes
`1, 3, 4, 5, 6, 7`, and may only permute `{0, 2}` and `{8, 9}`. -/
theorem identity_branch_rigidity (hm : 2 ≤ m) (d : Relabel (catCore m) (catCore m))
    (hid : ∀ a, a < 2 * m - 1 → innerIndex d a = a) :
    (∀ e : Fin (6 * m + 3), 4 ≤ e.val → e.val ≤ 6 * m - 2 → d.slot e = e) ∧
      (∀ v : Fin (4 * m + 2), v.val ≠ 0 → v.val ≠ 2 → v.val < 4 * m → d.vtx v = v) := by
  constructor
  · intro e h1 h2
    rcases (show e.val % 3 = 0 ∨ e.val % 3 = 1 ∨ e.val % 3 = 2 by omega) with h | h | h
    · exact slot_fix_loop hm d hid e h h1 h2
    · have hk : (e.val - 4) / 3 < 2 * m - 1 := by omega
      have he : e = innerSlot m ((e.val - 4) / 3) hk := Fin.ext (by rw [innerSlot_val]; omega)
      rw [he]
      exact slot_innerSlot d hid hk
    · exact slot_fix_stem hm d hid e h h1 h2
  · intro v h0 h2 hlt
    rcases (show v.val % 2 = 0 ∨ v.val % 2 = 1 by omega) with h | h
    · exact vtx_fix_even hm d hid v h (by omega) (by omega)
    · exact vtx_fix_odd hm d hid v h hlt


/-! ## 4.  The freedom that survives at the two ends is one binary choice each

`identity_branch_rigidity` leaves `d.slot` free on the eight slots
`{0, 1, 2, 3}` and `{6m-1, 6m, 6m+1, 6m+2}`.  It is not free there either.  The
spine vertices `1` and `4m-1` are fixed, each meets exactly three slots, and one
of the three is an interior spine slot, which is fixed; so at each end `d.slot`
can only exchange the remaining two.  That single binary choice then propagates:
it determines which vertex the near loop vertex goes to, and hence where both
loops at that end go.

The upshot is that the identity branch is **exactly** the Klein four-group
`{1, τ_near, τ_far, τ_near τ_far}` of the two end swaps.  `τ_near` is
`SlopeRigidity.endSwap`; `τ_far` is `BallotFarEndSwap.farSwap`. -/

/-- `d.slot` carries the slot of index `a` to the slot of index `b`. -/
def SlotTo (d : Relabel (catCore m) (catCore m)) (a b : ℕ) : Prop :=
  ∀ e : Fin (6 * m + 3), e.val = a → (d.slot e).val = b

/-- **Only the two slots `1` and `2` meet the near spine vertex** (apart from
the interior spine slot `4`, which is fixed), so `d.slot` permutes them. -/
theorem slot_at_near_vertex (hm : 2 ≤ m) (d : Relabel (catCore m) (catCore m))
    (hid : ∀ a, a < 2 * m - 1 → innerIndex d a = a) (e : Fin (6 * m + 3))
    (he : e.val = 1 ∨ e.val = 2) : (d.slot e).val = 1 ∨ (d.slot e).val = 2 := by
  have hfix : ∀ v : Fin (4 * m + 2), v.val = 2 * 0 + 1 → d.vtx v = v := fun v hv ↦
    vtx_fix_odd hm d hid v (by omega) (by omega)
  have hend : ((catCore m).tail e).val = 2 * 0 + 1 ∨ ((catCore m).head e).val = 2 * 0 + 1 :=
    (endpoint_odd_iff m 0 e).mpr (by omega)
  have hmem := (endpoint_odd_iff m 0 (d.slot e)).mp (slot_image_endpoint d hfix e hend)
  have h0 : (0 : ℕ) < 2 * m - 1 := by omega
  have hne4 : (d.slot e).val ≠ 4 := by
    intro h
    have hfi := slot_innerSlot d hid h0
    have hinj := d.slot.injective (show d.slot e = d.slot (innerSlot m 0 h0) from
      Fin.ext (by rw [h, hfi, innerSlot_val]))
    have := congrArg Fin.val hinj
    rw [innerSlot_val] at this
    omega
  omega

/-- **Only the two slots `6m-1` and `6m+1` meet the far spine vertex** (apart
from the interior spine slot `6m-2`, which is fixed). -/
theorem slot_at_far_vertex (hm : 2 ≤ m) (d : Relabel (catCore m) (catCore m))
    (hid : ∀ a, a < 2 * m - 1 → innerIndex d a = a) (e : Fin (6 * m + 3))
    (he : e.val = 6 * m - 1 ∨ e.val = 6 * m + 1) :
    (d.slot e).val = 6 * m - 1 ∨ (d.slot e).val = 6 * m + 1 := by
  have hfix : ∀ v : Fin (4 * m + 2), v.val = 2 * (2 * m - 1) + 1 → d.vtx v = v := fun v hv ↦
    vtx_fix_odd hm d hid v (by omega) (by omega)
  have hend : ((catCore m).tail e).val = 2 * (2 * m - 1) + 1 ∨
      ((catCore m).head e).val = 2 * (2 * m - 1) + 1 :=
    (endpoint_odd_iff m (2 * m - 1) e).mpr (by omega)
  have hmem := (endpoint_odd_iff m (2 * m - 1) (d.slot e)).mp
    (slot_image_endpoint d hfix e hend)
  have h0 : 2 * m - 2 < 2 * m - 1 := by omega
  have hne : (d.slot e).val ≠ 6 * m - 2 := by
    intro h
    have hfi := slot_innerSlot d hid h0
    have hinj := d.slot.injective (show d.slot e = d.slot (innerSlot m (2 * m - 2) h0) from
      Fin.ext (by rw [h, hfi, innerSlot_val]; omega))
    have := congrArg Fin.val hinj
    rw [innerSlot_val] at this
    omega
  omega

/-- **The near end is determined by its binary choice.**  Either `d.slot` fixes
all four near slots, or it is the near end swap `(0 3)(1 2)` there -- which is
exactly the slot component of `SlopeRigidity.endSwap`. -/
theorem left_end_determined (hm : 2 ≤ m) (d : Relabel (catCore m) (catCore m))
    (hid : ∀ a, a < 2 * m - 1 → innerIndex d a = a) :
    (SlotTo d 0 0 ∧ SlotTo d 1 1 ∧ SlotTo d 2 2 ∧ SlotTo d 3 3 ∧
        VtxTo d 0 0 ∧ VtxTo d 2 2) ∨
      (SlotTo d 0 3 ∧ SlotTo d 1 2 ∧ SlotTo d 2 1 ∧ SlotTo d 3 0 ∧
        VtxTo d 0 2 ∧ VtxTo d 2 0) := by
  set s0 : Fin (6 * m + 3) := ⟨0, by omega⟩ with hs0def
  set s1 : Fin (6 * m + 3) := ⟨1, by omega⟩ with hs1def
  set s2 : Fin (6 * m + 3) := ⟨2, by omega⟩ with hs2def
  set s3 : Fin (6 * m + 3) := ⟨3, by omega⟩ with hs3def
  have hn0 : s0.val = 0 := rfl
  have hn1 : s1.val = 1 := rfl
  have hn2 : s2.val = 2 := rfl
  have hn3 : s3.val = 3 := rfl
  have hleaf0 : IsLeafEdge m s0 := Or.inl (by omega)
  have hleaf3 : IsLeafEdge m s3 := Or.inl (by omega)
  have hleaf0' : IsLeafEdge m (d.slot s0) := (SlopeRigidity.relabel_isLeafEdge_iff d s0).mpr hleaf0
  have hleaf3' : IsLeafEdge m (d.slot s3) := (SlopeRigidity.relabel_isLeafEdge_iff d s3).mpr hleaf3
  have ht1 := (slot_one_ends m s1 hn1).1
  have hh1 := (slot_one_ends m s1 hn1).2
  have ht2 : ((catCore m).tail s2).val = 2 * 0 + 1 := stem_tail_val m 0 s2 (by omega)
  have hh2 : ((catCore m).head s2).val = 2 * 0 + 2 := stem_head_val m 0 s2 (by omega) (by omega)
  have ht0 : ((catCore m).tail s0).val = 2 * 0 := loop_tail_val m 0 s0 (by omega)
  have ht3 : ((catCore m).tail s3).val = 2 * 1 := loop_tail_val m 1 s3 (by omega)
  have hfixv1 : d.vtx ((catCore m).head s1) = (catCore m).head s1 :=
    vtx_fix_odd hm d hid _ (by omega) (by omega)
  rcases slot_at_near_vertex hm d hid s1 (Or.inl hn1) with h1 | h1
  · have hd1 : d.slot s1 = s1 := Fin.ext (by omega)
    have hvv0 : d.vtx ((catCore m).tail s1) = (catCore m).tail s1 := by
      rcases relabel_orientation d s1 with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [hd1] at ha hb
      · exact ha.symm
      · exfalso
        rw [hfixv1] at hb
        have := congrArg Fin.val hb
        omega
    have hd0 : (d.slot s0).val = 0 := by
      have himg := loop_image_tail_val d s0 hleaf0
      rw [show (catCore m).tail s0 = (catCore m).tail s1 from Fin.ext (by omega), hvv0] at himg
      have := leaf_tail_injective m (d.slot s0) s0 hleaf0' hleaf0 (by omega)
      omega
    have hd2 : (d.slot s2).val = 2 := by
      rcases slot_at_near_vertex hm d hid s2 (Or.inr hn2) with h | h
      · exfalso
        have hx := congrArg Fin.val
          (d.slot.injective (show d.slot s2 = d.slot s1 from Fin.ext (by omega)))
        omega
      · exact h
    have hvv2 : d.vtx ((catCore m).head s2) = (catCore m).head s2 := by
      rcases vtx_of_slot_fixed d (show d.slot s2 = s2 from Fin.ext (by omega)) with
        ⟨_, hb⟩ | ⟨ha, _⟩
      · exact hb
      · exfalso
        have hfx : d.vtx ((catCore m).tail s2) = (catCore m).tail s2 :=
          vtx_fix_odd hm d hid _ (by omega) (by omega)
        have := congrArg Fin.val (hfx.symm.trans ha)
        omega
    have hd3 : (d.slot s3).val = 3 := by
      have himg := loop_image_tail_val d s3 hleaf3
      rw [show (catCore m).tail s3 = (catCore m).head s2 from Fin.ext (by omega), hvv2] at himg
      have := leaf_tail_injective m (d.slot s3) s3 hleaf3' hleaf3 (by omega)
      omega
    exact Or.inl ⟨fun e he ↦ by rw [show e = s0 from Fin.ext (by omega)]; exact hd0,
      fun e he ↦ by rw [show e = s1 from Fin.ext (by omega)]; exact h1,
      fun e he ↦ by rw [show e = s2 from Fin.ext (by omega)]; exact hd2,
      fun e he ↦ by rw [show e = s3 from Fin.ext (by omega)]; exact hd3,
      fun v hv ↦ by
        rw [show v = (catCore m).tail s1 from Fin.ext (by omega), hvv0]; omega,
      fun v hv ↦ by
        rw [show v = (catCore m).head s2 from Fin.ext (by omega), hvv2]; omega⟩
  · have hd1 : d.slot s1 = s2 := Fin.ext (by omega)
    have hvv0 : (d.vtx ((catCore m).tail s1)).val = 2 := by
      rcases relabel_orientation d s1 with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [hd1] at ha hb
      · exfalso
        rw [hfixv1] at hb
        have := congrArg Fin.val hb
        omega
      · rw [← ha]; omega
    have hd0 : (d.slot s0).val = 3 := by
      have himg := loop_image_tail_val d s0 hleaf0
      rw [show (catCore m).tail s0 = (catCore m).tail s1 from Fin.ext (by omega)] at himg
      have := leaf_tail_injective m (d.slot s0) s3 hleaf0' hleaf3 (by omega)
      omega
    have hd2 : (d.slot s2).val = 1 := by
      rcases slot_at_near_vertex hm d hid s2 (Or.inr hn2) with h | h
      · exact h
      · exfalso
        have hx := congrArg Fin.val
          (d.slot.injective (show d.slot s2 = d.slot s1 from Fin.ext (by omega)))
        omega
    have hvv2 : (d.vtx ((catCore m).head s2)).val = 0 := by
      rcases relabel_orientation d s2 with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
        rw [show d.slot s2 = s1 from Fin.ext (by omega)] at ha hb
      · exfalso
        have hfx : d.vtx ((catCore m).tail s2) = (catCore m).tail s2 :=
          vtx_fix_odd hm d hid _ (by omega) (by omega)
        rw [hfx] at ha
        have := congrArg Fin.val ha
        omega
      · rw [← hb]; omega
    have hd3 : (d.slot s3).val = 0 := by
      have himg := loop_image_tail_val d s3 hleaf3
      rw [show (catCore m).tail s3 = (catCore m).head s2 from Fin.ext (by omega)] at himg
      have := leaf_tail_injective m (d.slot s3) s0 hleaf3' hleaf0 (by omega)
      omega
    exact Or.inr ⟨fun e he ↦ by rw [show e = s0 from Fin.ext (by omega)]; exact hd0,
      fun e he ↦ by rw [show e = s1 from Fin.ext (by omega)]; exact h1,
      fun e he ↦ by rw [show e = s2 from Fin.ext (by omega)]; exact hd2,
      fun e he ↦ by rw [show e = s3 from Fin.ext (by omega)]; exact hd3,
      fun v hv ↦ by rw [show v = (catCore m).tail s1 from Fin.ext (by omega)]; exact hvv0,
      fun v hv ↦ by rw [show v = (catCore m).head s2 from Fin.ext (by omega)]; exact hvv2⟩


/-- **The far end is determined by its binary choice.**  Either `d.slot` fixes
all four far slots, or it is the far end swap `(6m-1 6m+1)(6m 6m+2)` there.  The
second alternative is realised by the relabelling `BallotFarEndSwap.farSwap`. -/
theorem right_end_determined (hm : 2 ≤ m) (d : Relabel (catCore m) (catCore m))
    (hid : ∀ a, a < 2 * m - 1 → innerIndex d a = a) :
    (SlotTo d (6 * m - 1) (6 * m - 1) ∧ SlotTo d (6 * m) (6 * m) ∧
        SlotTo d (6 * m + 1) (6 * m + 1) ∧ SlotTo d (6 * m + 2) (6 * m + 2) ∧
        VtxTo d (4 * m) (4 * m) ∧ VtxTo d (4 * m + 1) (4 * m + 1)) ∨
      (SlotTo d (6 * m - 1) (6 * m + 1) ∧ SlotTo d (6 * m) (6 * m + 2) ∧
        SlotTo d (6 * m + 1) (6 * m - 1) ∧ SlotTo d (6 * m + 2) (6 * m) ∧
        VtxTo d (4 * m) (4 * m + 1) ∧ VtxTo d (4 * m + 1) (4 * m)) := by
  set sA : Fin (6 * m + 3) := ⟨6 * m - 1, by omega⟩ with hsAdef
  set sC : Fin (6 * m + 3) := ⟨6 * m, by omega⟩ with hsCdef
  set sB : Fin (6 * m + 3) := ⟨6 * m + 1, by omega⟩ with hsBdef
  set sD : Fin (6 * m + 3) := ⟨6 * m + 2, by omega⟩ with hsDdef
  have hnA : sA.val = 6 * m - 1 := rfl
  have hnC : sC.val = 6 * m := rfl
  have hnB : sB.val = 6 * m + 1 := rfl
  have hnD : sD.val = 6 * m + 2 := rfl
  have hleafC : IsLeafEdge m sC := Or.inl (by omega)
  have hleafD : IsLeafEdge m sD := Or.inr (by omega)
  have hleafC' : IsLeafEdge m (d.slot sC) := (SlopeRigidity.relabel_isLeafEdge_iff d sC).mpr hleafC
  have hleafD' : IsLeafEdge m (d.slot sD) := (SlopeRigidity.relabel_isLeafEdge_iff d sD).mpr hleafD
  have htA : ((catCore m).tail sA).val = 2 * (2 * m - 1) + 1 := stem_tail_val m (2 * m - 1) sA
    (by omega)
  have hhA : ((catCore m).head sA).val = 2 * (2 * m - 1) + 2 :=
    stem_head_val m (2 * m - 1) sA (by omega) (by omega)
  have htB := (last_spine_ends m (by omega) sB hnB).1
  have hhB := (last_spine_ends m (by omega) sB hnB).2
  have htC : ((catCore m).tail sC).val = 2 * (2 * m) := loop_tail_val m (2 * m) sC (by omega)
  have htD : ((catCore m).tail sD).val = 4 * m + 1 := last_leaf_tail_val m sD hnD
  have hfixA : d.vtx ((catCore m).tail sA) = (catCore m).tail sA :=
    vtx_fix_odd hm d hid _ (by omega) (by omega)
  have hfixB : d.vtx ((catCore m).tail sB) = (catCore m).tail sB :=
    vtx_fix_odd hm d hid _ (by omega) (by omega)
  rcases slot_at_far_vertex hm d hid sB (Or.inr hnB) with h1 | h1
  · -- the far end swap
    have hdB : d.slot sB = sA := Fin.ext (by omega)
    have hvvB : (d.vtx ((catCore m).head sB)).val = 2 * (2 * m - 1) + 2 := by
      rcases relabel_orientation d sB with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [hdB] at ha hb
      · rw [← hb]; omega
      · exfalso
        rw [hfixB] at ha
        have := congrArg Fin.val ha
        omega
    have hdD : (d.slot sD).val = 6 * m := by
      have himg := loop_image_tail_val d sD hleafD
      rw [show (catCore m).tail sD = (catCore m).head sB from Fin.ext (by omega)] at himg
      have := leaf_tail_injective m (d.slot sD) sC hleafD' hleafC (by omega)
      omega
    have hdA : (d.slot sA).val = 6 * m + 1 := by
      rcases slot_at_far_vertex hm d hid sA (Or.inl hnA) with h | h
      · exfalso
        have hx := congrArg Fin.val
          (d.slot.injective (show d.slot sA = d.slot sB from Fin.ext (by omega)))
        omega
      · exact h
    have hvvA : (d.vtx ((catCore m).head sA)).val = 4 * m + 1 := by
      rcases relabel_orientation d sA with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
        rw [show d.slot sA = sB from Fin.ext (by omega)] at ha hb
      · rw [← hb]; omega
      · exfalso
        rw [hfixA] at ha
        have := congrArg Fin.val ha
        omega
    have hdC : (d.slot sC).val = 6 * m + 2 := by
      have himg := loop_image_tail_val d sC hleafC
      rw [show (catCore m).tail sC = (catCore m).head sA from Fin.ext (by omega)] at himg
      have := leaf_tail_injective m (d.slot sC) sD hleafC' hleafD (by omega)
      omega
    exact Or.inr ⟨fun e he ↦ by rw [show e = sA from Fin.ext (by omega)]; exact hdA,
      fun e he ↦ by rw [show e = sC from Fin.ext (by omega)]; exact hdC,
      fun e he ↦ by rw [show e = sB from Fin.ext (by omega)]; exact h1,
      fun e he ↦ by rw [show e = sD from Fin.ext (by omega)]; exact hdD,
      fun v hv ↦ by
        rw [show v = (catCore m).head sA from Fin.ext (by omega)]; exact hvvA,
      fun v hv ↦ by
        rw [show v = (catCore m).head sB from Fin.ext (by omega), hvvB]; omega⟩
  · -- the far end is fixed
    have hdB : d.slot sB = sB := Fin.ext (by omega)
    have hvvB : d.vtx ((catCore m).head sB) = (catCore m).head sB := by
      rcases relabel_orientation d sB with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [hdB] at ha hb
      · exact hb.symm
      · exfalso
        rw [hfixB] at ha
        have := congrArg Fin.val ha
        omega
    have hdD : (d.slot sD).val = 6 * m + 2 := by
      have himg := loop_image_tail_val d sD hleafD
      rw [show (catCore m).tail sD = (catCore m).head sB from Fin.ext (by omega), hvvB] at himg
      have := leaf_tail_injective m (d.slot sD) sD hleafD' hleafD (by omega)
      omega
    have hdA : (d.slot sA).val = 6 * m - 1 := by
      rcases slot_at_far_vertex hm d hid sA (Or.inl hnA) with h | h
      · exact h
      · exfalso
        have hx := congrArg Fin.val
          (d.slot.injective (show d.slot sA = d.slot sB from Fin.ext (by omega)))
        omega
    have hvvA : d.vtx ((catCore m).head sA) = (catCore m).head sA := by
      rcases vtx_of_slot_fixed d (show d.slot sA = sA from Fin.ext (by omega)) with
        ⟨_, hb⟩ | ⟨ha, _⟩
      · exact hb
      · exfalso
        have := congrArg Fin.val (hfixA.symm.trans ha)
        omega
    have hdC : (d.slot sC).val = 6 * m := by
      have himg := loop_image_tail_val d sC hleafC
      rw [show (catCore m).tail sC = (catCore m).head sA from Fin.ext (by omega), hvvA] at himg
      have := leaf_tail_injective m (d.slot sC) sC hleafC' hleafC (by omega)
      omega
    exact Or.inl ⟨fun e he ↦ by rw [show e = sA from Fin.ext (by omega)]; exact hdA,
      fun e he ↦ by rw [show e = sC from Fin.ext (by omega)]; exact hdC,
      fun e he ↦ by rw [show e = sB from Fin.ext (by omega)]; exact h1,
      fun e he ↦ by rw [show e = sD from Fin.ext (by omega)]; exact hdD,
      fun v hv ↦ by
        rw [show v = (catCore m).head sA from Fin.ext (by omega), hvvA]; omega,
      fun v hv ↦ by
        rw [show v = (catCore m).head sB from Fin.ext (by omega), hvvB]; omega⟩


/-- Two relabellings with the same slot and vertex permutations are equal: the
third field of `Relabel` is a `Prop`. -/
theorem relabel_ext {d d' : Relabel (catCore m) (catCore m)} (hs : d.slot = d'.slot)
    (hv : d.vtx = d'.vtx) : d = d' := by
  obtain ⟨s₁, v₁, i₁⟩ := d
  obtain ⟨s₂, v₂, i₂⟩ := d'
  subst hs
  subst hv
  rfl

/-- **The identity branch has at most four elements.**  A relabelling acting as
the identity on the interior spine slots is determined by two bits: where it
sends the near spine slot `1` and where it sends the far spine slot `6m+1`.

So the identity branch of `hStab` is a group of order at most four -- and
`exists_nontrivial_in_identity_branch` shows it is not trivial, while
`SlopeRigidity.endSwap` inhabits the near-swap bit.  Together with
`identity_branch_rigidity` this is the exact residual freedom: the Klein
four-group of the two end swaps, no more. -/
theorem identity_branch_unique (hm : 2 ≤ m) (d d' : Relabel (catCore m) (catCore m))
    (hid : ∀ a, a < 2 * m - 1 → innerIndex d a = a)
    (hid' : ∀ a, a < 2 * m - 1 → innerIndex d' a = a)
    (hnear : ∀ e : Fin (6 * m + 3), e.val = 1 → (d.slot e).val = (d'.slot e).val)
    (hfar : ∀ e : Fin (6 * m + 3), e.val = 6 * m + 1 → (d.slot e).val = (d'.slot e).val) :
    d = d' := by
  have h1lt : (1 : ℕ) < 6 * m + 3 := by omega
  have hBlt : 6 * m + 1 < 6 * m + 3 := by omega
  have hn := hnear ⟨1, h1lt⟩ rfl
  have hf := hfar ⟨6 * m + 1, hBlt⟩ rfl
  have hmid := (identity_branch_rigidity hm d hid).1
  have hmid' := (identity_branch_rigidity hm d' hid').1
  have hvmid := (identity_branch_rigidity hm d hid).2
  have hvmid' := (identity_branch_rigidity hm d' hid').2
  have hleft : ∀ e : Fin (6 * m + 3), e.val ≤ 3 → (d.slot e).val = (d'.slot e).val := by
    intro e he
    rcases left_end_determined hm d hid with hL | hL <;>
      rcases left_end_determined hm d' hid' with hL' | hL' <;>
      rcases (show e.val = 0 ∨ e.val = 1 ∨ e.val = 2 ∨ e.val = 3 by omega) with h | h | h | h <;>
      first
        | (exfalso
           have ha := hL.2.1 ⟨1, h1lt⟩ rfl
           have hb := hL'.2.1 ⟨1, h1lt⟩ rfl
           omega)
        | rw [hL.1 e h, hL'.1 e h]
        | rw [hL.2.1 e h, hL'.2.1 e h]
        | rw [hL.2.2.1 e h, hL'.2.2.1 e h]
        | rw [hL.2.2.2.1 e h, hL'.2.2.2.1 e h]
  have hright : ∀ e : Fin (6 * m + 3), 6 * m - 1 ≤ e.val →
      (d.slot e).val = (d'.slot e).val := by
    intro e he
    have hlt := e.isLt
    rcases right_end_determined hm d hid with hR | hR <;>
      rcases right_end_determined hm d' hid' with hR' | hR' <;>
      rcases (show e.val = 6 * m - 1 ∨ e.val = 6 * m ∨ e.val = 6 * m + 1 ∨ e.val = 6 * m + 2 by
        omega) with h | h | h | h <;>
      first
        | (exfalso
           have ha := hR.2.2.1 ⟨6 * m + 1, hBlt⟩ rfl
           have hb := hR'.2.2.1 ⟨6 * m + 1, hBlt⟩ rfl
           omega)
        | rw [hR.1 e h, hR'.1 e h]
        | rw [hR.2.1 e h, hR'.2.1 e h]
        | rw [hR.2.2.1 e h, hR'.2.2.1 e h]
        | rw [hR.2.2.2.1 e h, hR'.2.2.2.1 e h]
  have hvleft : ∀ v : Fin (4 * m + 2), v.val = 0 ∨ v.val = 2 →
      (d.vtx v).val = (d'.vtx v).val := by
    intro v hv
    rcases left_end_determined hm d hid with hL | hL <;>
      rcases left_end_determined hm d' hid' with hL' | hL' <;>
      rcases hv with h | h <;>
      first
        | (exfalso
           have ha := hL.2.1 ⟨1, h1lt⟩ rfl
           have hb := hL'.2.1 ⟨1, h1lt⟩ rfl
           omega)
        | rw [hL.2.2.2.2.1 v h, hL'.2.2.2.2.1 v h]
        | rw [hL.2.2.2.2.2 v h, hL'.2.2.2.2.2 v h]
  have hvright : ∀ v : Fin (4 * m + 2), v.val = 4 * m ∨ v.val = 4 * m + 1 →
      (d.vtx v).val = (d'.vtx v).val := by
    intro v hv
    rcases right_end_determined hm d hid with hR | hR <;>
      rcases right_end_determined hm d' hid' with hR' | hR' <;>
      rcases hv with h | h <;>
      first
        | (exfalso
           have ha := hR.2.2.1 ⟨6 * m + 1, hBlt⟩ rfl
           have hb := hR'.2.2.1 ⟨6 * m + 1, hBlt⟩ rfl
           omega)
        | rw [hR.2.2.2.2.1 v h, hR'.2.2.2.2.1 v h]
        | rw [hR.2.2.2.2.2 v h, hR'.2.2.2.2.2 v h]
  refine relabel_ext (Equiv.ext fun e ↦ Fin.ext ?_) (Equiv.ext fun v ↦ Fin.ext ?_)
  · have hlt := e.isLt
    rcases (show e.val ≤ 3 ∨ (4 ≤ e.val ∧ e.val ≤ 6 * m - 2) ∨ 6 * m - 1 ≤ e.val by omega) with
      h | h | h
    · exact hleft e h
    · rw [hmid e h.1 h.2, hmid' e h.1 h.2]
    · exact hright e h
  · have hlt := v.isLt
    rcases (show v.val = 0 ∨ v.val = 2 ∨ (v.val ≠ 0 ∧ v.val ≠ 2 ∧ v.val < 4 * m) ∨
        v.val = 4 * m ∨ v.val = 4 * m + 1 by omega) with h | h | h | h | h
    · exact hvleft v (Or.inl h)
    · exact hvleft v (Or.inr h)
    · rw [hvmid v h.1 h.2.1 h.2.2, hvmid' v h.1 h.2.1 h.2.2]
    · exact hvright v (Or.inl h)
    · exact hvright v (Or.inr h)


/-- **If both binary choices are trivial, the relabelling is the identity.**
This is the one element of the identity branch that costs nothing. -/
theorem identity_branch_trivial_of_ends_fixed (hm : 2 ≤ m)
    (d : Relabel (catCore m) (catCore m)) (hid : ∀ a, a < 2 * m - 1 → innerIndex d a = a)
    (hnear : ∀ e : Fin (6 * m + 3), e.val = 1 → (d.slot e).val = 1)
    (hfar : ∀ e : Fin (6 * m + 3), e.val = 6 * m + 1 → (d.slot e).val = 6 * m + 1) :
    (∀ e, d.slot e = e) ∧ (∀ v, d.vtx v = v) := by
  have h1lt : (1 : ℕ) < 6 * m + 3 := by omega
  have hBlt : 6 * m + 1 < 6 * m + 3 := by omega
  have hn := hnear ⟨1, h1lt⟩ rfl
  have hf := hfar ⟨6 * m + 1, hBlt⟩ rfl
  have hmid := (identity_branch_rigidity hm d hid).1
  have hvmid := (identity_branch_rigidity hm d hid).2
  refine ⟨fun e ↦ Fin.ext ?_, fun v ↦ Fin.ext ?_⟩
  · have hlt := e.isLt
    rcases (show e.val ≤ 3 ∨ (4 ≤ e.val ∧ e.val ≤ 6 * m - 2) ∨ 6 * m - 1 ≤ e.val by omega) with
      h | h | h
    · rcases left_end_determined hm d hid with hL | hL <;>
        rcases (show e.val = 0 ∨ e.val = 1 ∨ e.val = 2 ∨ e.val = 3 by omega) with
          h' | h' | h' | h' <;>
        first
          | (exfalso; have ha := hL.2.1 ⟨1, h1lt⟩ rfl; omega)
          | (rw [hL.1 e h']; omega)
          | (rw [hL.2.1 e h']; omega)
          | (rw [hL.2.2.1 e h']; omega)
          | (rw [hL.2.2.2.1 e h']; omega)
    · rw [hmid e h.1 h.2]
    · rcases right_end_determined hm d hid with hR | hR <;>
        rcases (show e.val = 6 * m - 1 ∨ e.val = 6 * m ∨ e.val = 6 * m + 1 ∨ e.val = 6 * m + 2 by
          omega) with h' | h' | h' | h' <;>
        first
          | (exfalso; have ha := hR.2.2.1 ⟨6 * m + 1, hBlt⟩ rfl; omega)
          | (rw [hR.1 e h']; omega)
          | (rw [hR.2.1 e h']; omega)
          | (rw [hR.2.2.1 e h']; omega)
          | (rw [hR.2.2.2.1 e h']; omega)
  · have hlt := v.isLt
    rcases (show v.val = 0 ∨ v.val = 2 ∨ (v.val ≠ 0 ∧ v.val ≠ 2 ∧ v.val < 4 * m) ∨
        v.val = 4 * m ∨ v.val = 4 * m + 1 by omega) with h | h | h | h | h
    · rcases left_end_determined hm d hid with hL | hL
      · rw [hL.2.2.2.2.1 v h]; omega
      · exfalso; have ha := hL.2.1 ⟨1, h1lt⟩ rfl; omega
    · rcases left_end_determined hm d hid with hL | hL
      · rw [hL.2.2.2.2.2 v h]; omega
      · exfalso; have ha := hL.2.1 ⟨1, h1lt⟩ rfl; omega
    · rw [hvmid v h.1 h.2.1 h.2.2]
    · rcases right_end_determined hm d hid with hR | hR
      · rw [hR.2.2.2.2.1 v h]; omega
      · exfalso; have ha := hR.2.2.1 ⟨6 * m + 1, hBlt⟩ rfl; omega
    · rcases right_end_determined hm d hid with hR | hR
      · rw [hR.2.2.2.2.2 v h]; omega
      · exfalso; have ha := hR.2.2.1 ⟨6 * m + 1, hBlt⟩ rfl; omega

/-! ## 5.  The reversal branch forces a palindrome -/

/-- **The reversal branch carries the diagonal to the reversed one.**  This is
the second half of `BallotOrbit.ballotCoreDiag_relabel_eq_self_or_reverse`'s
proof, made conditional on the index branch rather than left as a disjunct. -/
theorem ballotCoreDiag_of_reverse_branch (m : ℕ) (s : Slopes (2 * (m + 1)))
    (d : Relabel (catCore m) (catCore m))
    (hrev : ∀ a, a < 2 * m - 1 → innerIndex d a = 2 * m - 2 - a) :
    (fun slot ↦ BallotSlopes.ballotCoreDiag m s (d.slot.symm slot)) =
      BallotSlopes.ballotCoreDiag m (reverseSlopes s) := by
  refine ballotCoreDiag_relabel_eq_of_not_loopAdjacent s (reverseSlopes s) d fun slot hna ↦ ?_
  obtain ⟨k, hk, rfl⟩ := exists_innerSlot hna
  rw [innerSlot_symm d hk,
    BallotSlopes.ballotCoreDiag_spine s
      (show (innerSlot m (innerIndex d k) (innerIndex_spec d hk).1).val % 3 = 1 by
        rw [innerSlot_val]; omega),
    BallotSlopes.ballotCoreDiag_spine (reverseSlopes s)
      (show (innerSlot m k hk).val % 3 = 1 by rw [innerSlot_val]; omega)]
  simp only [innerSlot_val]
  rw [show (3 * innerIndex d k + 4 + 2) / 3 = 2 * m - k by rw [hrev k hk]; omega,
    show (3 * k + 4 + 2) / 3 = k + 2 by omega,
    slope_reverseSlopes s (by omega) (by omega),
    show 2 * (m + 1) - (k + 2) = 2 * m - k by omega]

/-- **In the reversal branch the stabiliser premise forces the slope sequence to
be a palindrome.**  So the reversal branch of `hStab` is not a statement about
all five genus-six slope sequences: it is empty unless `reverseSlopes s = s`. -/
theorem reverseSlopes_eq_of_stab (m : ℕ) (s : Slopes (2 * (m + 1)))
    (d : Relabel (catCore m) (catCore m))
    (hrev : ∀ a, a < 2 * m - 1 → innerIndex d a = 2 * m - 2 - a)
    (hstab : ∀ slot, BallotSlopes.ballotCoreDiag m s (d.slot.symm slot) =
      BallotSlopes.ballotCoreDiag m s slot) :
    reverseSlopes s = s := by
  apply BallotSlopes.ballotCoreDiag_injective m
  rw [← ballotCoreDiag_of_reverse_branch m s d hrev]
  funext slot
  exact hstab slot

/-! ## 6.  `hStab`, reduced to the two branches -/

/-- **The reduction.**  The `hStab` hypothesis of
`DiagonalClassificationGenusSix` -- a statement about *every*
relabelling of `catCore m` stabilising a ballot diagonal, over a group that is
not enumerated -- follows from two statements indexed by
the index branch of `innerIndex_id_or_reverse`, and the second of them is
vacuous unless the slope sequence is a palindrome.

No positivity, no genericity, and no enumeration of `Aut (catCore m)`. -/
theorem hStab_of_two_branches (m : ℕ) (request : Fin (6 * m + 3) → ℚ)
    (hIdentity : ∀ (s : Slopes (2 * (m + 1))) (d : Relabel (catCore m) (catCore m)),
      (∀ a, a < 2 * m - 1 → innerIndex d a = a) →
        SlopeRigidity.Realizes d (BallotCoreIdentification.ballotFamilyMember m request s))
    (hReversal : ∀ (s : Slopes (2 * (m + 1))) (d : Relabel (catCore m) (catCore m)),
      (∀ a, a < 2 * m - 1 → innerIndex d a = 2 * m - 2 - a) → reverseSlopes s = s →
        SlopeRigidity.Realizes d (BallotCoreIdentification.ballotFamilyMember m request s)) :
    ∀ (s : Slopes (2 * (m + 1))) (d : Relabel (catCore m) (catCore m)),
      (∀ slot, BallotSlopes.ballotCoreDiag m s (d.slot.symm slot) =
          BallotSlopes.ballotCoreDiag m s slot) →
        SlopeRigidity.Realizes d (BallotCoreIdentification.ballotFamilyMember m request s) := by
  intro s d hstab
  rcases innerIndex_id_or_reverse m d with h | h
  · exact hIdentity s d h
  · exact hReversal s d h (reverseSlopes_eq_of_stab m s d h hstab)

/-- **Genus six.**  The same, at `m = 2`, in the exact shape
`DiagonalClassificationGenusSix.diagonalClassification_genusSix_of_sharp_residues`
asks for.  In the identity branch `identity_branch_rigidity` says `d.slot` fixes
the seven middle slots `4, …, 10` and `d.vtx` fixes the six middle vertices
`1, 3, 4, 5, 6, 7`; `left_end_determined` and `right_end_determined` say the two
ends carry one binary choice each.  In the reversal branch `s` is a
palindrome. -/
theorem hStab_genusSix_of_two_branches (request : Fin (6 * 2 + 3) → ℚ)
    (hIdentity : ∀ (s : Slopes (2 * (2 + 1))) (d : Relabel (catCore 2) (catCore 2)),
      (∀ a, a < 2 * 2 - 1 → innerIndex d a = a) →
        SlopeRigidity.Realizes d (BallotCoreIdentification.ballotFamilyMember 2 request s))
    (hReversal : ∀ (s : Slopes (2 * (2 + 1))) (d : Relabel (catCore 2) (catCore 2)),
      (∀ a, a < 2 * 2 - 1 → innerIndex d a = 2 * 2 - 2 - a) → reverseSlopes s = s →
        SlopeRigidity.Realizes d (BallotCoreIdentification.ballotFamilyMember 2 request s)) :
    ∀ (s : Slopes (2 * (2 + 1))) (d : Relabel (catCore 2) (catCore 2)),
      (∀ slot, BallotSlopes.ballotCoreDiag 2 s (d.slot.symm slot) =
          BallotSlopes.ballotCoreDiag 2 s slot) →
        SlopeRigidity.Realizes d (BallotCoreIdentification.ballotFamilyMember 2 request s) :=
  hStab_of_two_branches 2 request hIdentity hReversal


/-- **Genus six, sharpened: `hStab` needs only the far end swap and the
palindromes.**  Of the four relabellings in the identity branch, the identity is
free (`identity_branch_trivial_of_ends_fixed` plus
`SlopeRigidity.realizes_of_trivial`) and `SlopeRigidity.endSwap 1` is
realised (`BallotEndSwapSheetIso.ballotRealizes_endSwap`); what remains are
the two whose far-end bit is nontrivial.  So the whole of `hStab` at genus six
is the two hypotheses below.

`hFar` is a statement about at most **two** relabellings (`BallotFarEndSwap.farSwap`
and `BallotFarEndSwap.nearFarSwap`, both realised in `BallotFarEndSwap`);
`hReversal` is empty unless `reverseSlopes s = s`. -/
theorem hStab_genusSix_of_far_and_reversal (request : Fin (6 * 2 + 3) → ℚ)
    (hFar : ∀ (s : Slopes (2 * (2 + 1))) (d : Relabel (catCore 2) (catCore 2)),
      (∀ a, a < 2 * 2 - 1 → innerIndex d a = a) →
        (∀ e : Fin (6 * 2 + 3), e.val = 6 * 2 + 1 → (d.slot e).val = 6 * 2 - 1) →
          SlopeRigidity.Realizes d (BallotCoreIdentification.ballotFamilyMember 2 request s))
    (hReversal : ∀ (s : Slopes (2 * (2 + 1))) (d : Relabel (catCore 2) (catCore 2)),
      (∀ a, a < 2 * 2 - 1 → innerIndex d a = 2 * 2 - 2 - a) → reverseSlopes s = s →
        SlopeRigidity.Realizes d (BallotCoreIdentification.ballotFamilyMember 2 request s)) :
    ∀ (s : Slopes (2 * (2 + 1))) (d : Relabel (catCore 2) (catCore 2)),
      (∀ slot, BallotSlopes.ballotCoreDiag 2 s (d.slot.symm slot) =
          BallotSlopes.ballotCoreDiag 2 s slot) →
        SlopeRigidity.Realizes d (BallotCoreIdentification.ballotFamilyMember 2 request s) := by
  refine hStab_of_two_branches 2 request (fun s d hid ↦ ?_) hReversal
  rcases right_end_determined (m := 2) (by omega) d hid with hR | hR
  · rcases left_end_determined (m := 2) (by omega) d hid with hL | hL
    · have htriv := identity_branch_trivial_of_ends_fixed (m := 2) (by omega) d hid
        (fun e he ↦ hL.2.1 e he) (fun e he ↦ hR.2.2.1 e he)
      exact SlopeRigidity.realizes_of_trivial htriv.1 htriv.2 _
    · have hde : d = SlopeRigidity.endSwap 1 :=
        identity_branch_unique (m := 2) (by omega) d (SlopeRigidity.endSwap 1) hid
          (fun a ha ↦ innerIndex_endSwap 1 a ha)
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
  · exact hFar s d hid (fun e he ↦ hR.2.2.1 e he)

/-- **The identity branch is not empty at genus six, and `SlopeRigidity.endSwap 1`
is realised in it.**  `BallotEndSwapSheetIso.ballotRealizes_endSwap`
proves the `Realizes` conclusion for that one relabelling, over every request
and every `s : Slopes 6`; `innerIndex_endSwap` places it in the identity
branch. -/
theorem identity_branch_endSwap_discharged (request : Fin (6 * 2 + 3) → ℚ)
    (s : Slopes (2 * (2 + 1))) :
    (∀ a, a < 2 * 2 - 1 → innerIndex (SlopeRigidity.endSwap 1) a = a) ∧
      SlopeRigidity.Realizes (SlopeRigidity.endSwap 1)
        (BallotCoreIdentification.ballotFamilyMember 2 request s) :=
  ⟨fun a ha ↦ innerIndex_endSwap 1 a ha, BallotEndSwapSheetIso.ballotRealizes_endSwap s request⟩


/-! ## 7.  The reduction, plugged into the genus-six assembly -/

/-- **The genus-six package from the same four residues, with `hStab` replaced
by the two branches.**  This is
`DiagonalClassificationGenusSix.diagonalClassification_genusSix_of_residues`
with its third hypothesis -- a quantifier over an unenumerated group -- traded
for `hFar` (at most two relabellings) and
`hReversal` (empty off the palindromic slope sequences).

The other three residues are untouched and none of them is inhabited here. -/
theorem diagonalClassification_genusSix_of_far_and_reversal {request : Fin (6 * 2 + 3) → ℚ}
    (hSep : ∀ mem : FibreMember (catCore 2) request (2 + 2), mem.Open → mem.HasOddMult →
      SpineSingleColumn.LeafAvoidingSeparated 2 mem)
    (hSpine : ∀ mem : FibreMember (catCore 2) request (2 + 2),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        ∃ s : Slopes (2 * (2 + 1)), ∀ slot : Fin (6 * 2 + 3), ¬ IsLeafEdge 2 slot →
          mem.coreDiag slot = BallotSlopes.ballotCoreDiag 2 s slot)
    (hFar : ∀ (s : Slopes (2 * (2 + 1))) (d : Relabel (catCore 2) (catCore 2)),
      (∀ a, a < 2 * 2 - 1 → innerIndex d a = a) →
        (∀ e : Fin (6 * 2 + 3), e.val = 6 * 2 + 1 → (d.slot e).val = 6 * 2 - 1) →
          SlopeRigidity.Realizes d (BallotCoreIdentification.ballotFamilyMember 2 request s))
    (hReversal : ∀ (s : Slopes (2 * (2 + 1))) (d : Relabel (catCore 2) (catCore 2)),
      (∀ a, a < 2 * 2 - 1 → innerIndex d a = 2 * 2 - 2 - a) → reverseSlopes s = s →
        SlopeRigidity.Realizes d (BallotCoreIdentification.ballotFamilyMember 2 request s))
    (hSupply : ∀ (s : Slopes (2 * (2 + 1))) (mem : FibreMember (catCore 2) request (2 + 2)),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        mem.coreDiag = BallotSlopes.ballotCoreDiag 2 s →
          Nonempty (GeometricDatumIso
            (BallotCoreIdentification.ballotFamilyMember 2 request s).data mem.data)) :
    BallotSlopes.DiagonalClassification 2 request :=
  DiagonalClassificationGenusSix.diagonalClassification_genusSix_of_residues hSep hSpine
    (hStab_genusSix_of_far_and_reversal request hFar hReversal) hSupply

end DraismaVargas.Count.BallotStabiliserReduction
