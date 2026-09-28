import Utilities.Subdivision.SlotRefinement
import Utilities.Subdivision.SubdivisionIso
import DraismaVargas.LocalCases.InputRefinementData

/-!
# A core API for `refineAllSlots`, and what the relabeling needs

`SlotRefinement` exposes the all-slot refinement through three *counts* —
`refineAllSlots_p`, `refineAllSlots_n` and `refineAllSlots_total_length`.  No
lemma there says **which** refined slot carries **which** prescribed segment,
still less what its two endpoints in the refined core are, and that description
is exactly what an identification of the refined specification with the
contracted source of a terminal face
(`LaplacianEquiv (refinedSpec iface face).graph topology.contractedSpec.graph`)
needs.  This file supplies the description and then uses it.

## 1–3.  The description

The bookkeeping of `refineAllSlots` is left-to-right: slots are refined in
index order, the first prescribed segment of a slot keeps that slot's own
index, and the remaining segments are appended at the end, one contiguous block
per stable slot.  `refinedSlot`, `refinedTail` and `refinedHead` name the slot
and its two endpoints; `refineAllSlots_core` proves the naming correct, by an
induction on `OrderedPathSplitValid` (`valid_core_transport`) followed by an
induction along `refineUpTo` (`described_refineUpTo`).  Nothing in
`SlotRefinement.lean` is modified: `stepSplit` and `step_target` recover the
ordered path split each step performs, both by `rfl`.

`slotIndexEquiv` and `vertexIndexEquiv` upgrade the naming to bijections —
refined slots are exactly the pairs (stable slot, segment index), refined core
vertices are exactly the stable core vertices together with the internal
breakpoints of the segment lists — by injectivity plus the counts
`refineAllSlots_p` and `refineAllSlots_n`.  `refineAllSlots_length_at`,
`refineAllSlots_tail_at` and `refineAllSlots_head_at` are the API in the form a
relabeling consumes.

## 4.  What a relabeling *is*

`CoreModel` reads a `SubdivisionGraph.Spec.Relabeling` of the refinement on the
source side: two bijections and three equations, no reference to the internal
indexing.  `CoreModel.relabeling` and `coreModelOfRelabeling` go both ways, so
this is a reading of the relabeling, not a strengthening or a weakening of it;
`coreModelSelf` is the joint-satisfiability check on the six fields.

## 5–6.  The last mile

`SourceModel` is `CoreModel` at a cleared face: a bijection from (stable slot,
segment position) pairs to the **kept slots** — the positive non-dangling
source occurrences — preserving length, and a bijection from (stable core
vertices ⊔ row breakpoints) to the **kept contraction classes** — those
meeting a surviving occurrence — matching endpoints, with an orientation flag
per occurrence.  Kept slots and kept classes are the slots and vertices of
`PrunedContractedSpec.prunedSpec`, the contracted quotient source with its
pendant trees deleted, which is the target of the refinement presentation at a
terminal face.  `SourceModel.laplacianEquiv` is the missing identification, and
`SourceModel.inputRefinement` packages it as the closed-face input refinement.

## What a stable model has to supply

A stable model is a pair of *bijections*, not counts:
`refinedSpec_p_eq_slotCard_of_sourceModel` shows that `slotModel` is the
bijective form of the count of kept slots, and `vertexModel` is likewise the
bijective form of the count of kept classes.  What a construction must supply
is that the stable core vertices together with the row breakpoints
**enumerate** the kept contraction classes, and that each row traverses its
occurrences as an oriented walk.  Existence of a `SourceModel` is not claimed
here; `OrientedTraversal` builds one from an oriented row dictionary, in the
same spirit as `W4StableSource.HasPathEnds` is supplied separately.
-/

namespace DraismaVargas.LocalCases.RefinementCore

open Utilities
open Utilities.Certificate
open Utilities.Certificate.OneEdgeSplitRefinement
open Utilities.Certificate.IteratedSplitRefinement
open DraismaVargas.LocalCases.SlotRefinement

/-! ## 1.  One canonical split, described on the nose -/

section OneSplit

variable (src : PackedSpec) (sl : Fin src.p) (first second : ℕ)
  (hFirst : 0 < first) (hSecond : 0 < second)

theorem splitPacked_length_old (i : Fin src.p) :
    (splitPacked src sl first second hFirst hSecond).spec.length i.castSucc =
      if i = sl then first else src.spec.length i := by
  show splitLength src.spec sl first second (oldSlot src.spec i) = _
  simp

theorem splitPacked_length_last :
    (splitPacked src sl first second hFirst hSecond).spec.length
      (secondSlot src.spec) = second := by
  show splitLength src.spec sl first second (secondSlot src.spec) = _
  simp

theorem splitPacked_tail_old (i : Fin src.p) :
    (((splitPacked src sl first second hFirst hSecond).spec.core.tail
      i.castSucc : Fin (src.n + 1)) : ℕ) = (src.spec.core.tail i : ℕ) := by
  show (((splitCore src.spec sl).tail (oldSlot src.spec i) : Fin (src.n + 1)) : ℕ) = _
  rw [splitCore_tail_old]
  simp [oldVertex]

theorem splitPacked_head_old (i : Fin src.p) (hi : i ≠ sl) :
    (((splitPacked src sl first second hFirst hSecond).spec.core.head
      i.castSucc : Fin (src.n + 1)) : ℕ) = (src.spec.core.head i : ℕ) := by
  show (((splitCore src.spec sl).head (oldSlot src.spec i) : Fin (src.n + 1)) : ℕ) = _
  rw [splitCore_head_old]
  simp [hi, oldVertex]

theorem splitPacked_head_split :
    (((splitPacked src sl first second hFirst hSecond).spec.core.head
      sl.castSucc : Fin (src.n + 1)) : ℕ) = src.n := by
  show (((splitCore src.spec sl).head (oldSlot src.spec sl) : Fin (src.n + 1)) : ℕ) = _
  rw [splitCore_head_old]
  simp [splitVertex]

theorem splitPacked_tail_last :
    (((splitPacked src sl first second hFirst hSecond).spec.core.tail
      (secondSlot src.spec) : Fin (src.n + 1)) : ℕ) = src.n := by
  show (((splitCore src.spec sl).tail (secondSlot src.spec) : Fin (src.n + 1)) : ℕ) = _
  rw [splitCore_tail_second]
  simp [splitVertex]

theorem splitPacked_head_last :
    (((splitPacked src sl first second hFirst hSecond).spec.core.head
      (secondSlot src.spec) : Fin (src.n + 1)) : ℕ) = (src.spec.core.head sl : ℕ) := by
  show (((splitCore src.spec sl).head (secondSlot src.spec) : Fin (src.n + 1)) : ℕ) = _
  rw [splitCore_head_second]
  simp [oldVertex]

end OneSplit

/-! ## 2.  One ordered path split, described -/

section OnePathSplit

variable {source target : PackedSpec} {slot : Fin source.p} {segments : List ℕ}

/-- The slot of the target of an ordered path split carrying the `k`-th
prescribed segment: the first segment stays in the split slot, and the rest
are appended in order at the end. -/
def segmentSlot (source : PackedSpec) (slot : Fin source.p) (k : ℕ) : ℕ :=
  if k = 0 then (slot : ℕ) else source.p + k - 1

/-- Its tail: the tail of the split slot for the first segment, and otherwise
the fresh bivalent vertex cut before it. -/
def segmentTail (source : PackedSpec) (slot : Fin source.p) (k : ℕ) : ℕ :=
  if k = 0 then (source.spec.core.tail slot : ℕ) else source.n + k - 1

/-- Its head: the head of the split slot for the last segment, and otherwise
the fresh bivalent vertex cut after it. -/
def segmentHead (source : PackedSpec) (slot : Fin source.p) (m k : ℕ) : ℕ :=
  if k + 1 = m then (source.spec.core.head slot : ℕ) else source.n + k

/-- **The core description of one ordered path split.**  Every slot other than
the split one keeps its length and both its endpoints at the same numeric
index; the split slot is replaced by the prescribed segments, in order, at the
slots named by `segmentSlot`, running between the vertices named by
`segmentTail` and `segmentHead`. -/
theorem valid_core_transport {chain : CanonicalSplitChain source target}
    (valid : OrderedPathSplitValid source slot segments target chain) :
    (∀ (i : Fin source.p) (j : Fin target.p), i ≠ slot → (i : ℕ) = (j : ℕ) →
        target.spec.length j = source.spec.length i ∧
          (target.spec.core.tail j : ℕ) = (source.spec.core.tail i : ℕ) ∧
            (target.spec.core.head j : ℕ) = (source.spec.core.head i : ℕ)) ∧
      ∀ (k : ℕ) (j : Fin target.p), k < segments.length →
        (j : ℕ) = segmentSlot source slot k →
          target.spec.length j = segments.getD k 0 ∧
            (target.spec.core.tail j : ℕ) = segmentTail source slot k ∧
              (target.spec.core.head j : ℕ) =
                segmentHead source slot segments.length k := by
  induction valid with
  | singleton src sl =>
      refine ⟨fun i j _ hval ↦ ?_, fun k j hk hval ↦ ?_⟩
      · obtain rfl : j = i := Fin.ext hval.symm
        exact ⟨rfl, rfl, rfl⟩
      · obtain rfl : k = 0 := by simpa using Nat.lt_one_iff.mp (by simpa using hk)
        simp only [segmentSlot] at hval
        obtain rfl : j = sl := Fin.ext hval
        refine ⟨by simp, by simp [segmentTail], by simp [segmentHead]⟩
  | cons src sl first rest first_pos rest_sum_pos length_sum tailValid ih =>
      obtain ⟨ihOld, ihSeg⟩ := ih
      have hrest : rest ≠ [] := by
        intro hEq
        rw [hEq] at rest_sum_pos
        simp at rest_sum_pos
      have hrestlen : 0 < rest.length := List.length_pos_of_ne_nil hrest
      have hne : ∀ i : Fin src.p, (i.castSucc : Fin (src.p + 1)) ≠ secondSlot src.spec :=
        fun i ↦ Fin.castSucc_ne_last i
      refine ⟨fun i j hi hval ↦ ?_, fun k j hk hval ↦ ?_⟩
      · obtain ⟨hLength, hTail, hHead⟩ :=
          ihOld i.castSucc j (hne i) (by simpa using hval)
        refine ⟨?_, ?_, ?_⟩
        · rw [hLength, splitPacked_length_old, if_neg hi]
        · rw [hTail, splitPacked_tail_old]
        · rw [hHead, splitPacked_head_old _ _ _ _ _ _ i hi]
      · rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · -- the first segment stays where it was
          simp only [segmentSlot] at hval
          obtain ⟨hLength, hTail, hHead⟩ :=
            ihOld sl.castSucc j (hne sl) (by simpa using hval.symm)
          refine ⟨?_, ?_, ?_⟩
          · rw [hLength, splitPacked_length_old, if_pos rfl]
            simp
          · rw [hTail, splitPacked_tail_old]
            simp [segmentTail]
          · rw [hHead, splitPacked_head_split]
            have hne0 : ¬ (0 + 1 = (first :: rest).length) := by
              simp only [List.length_cons]
              omega
            unfold segmentHead
            rw [if_neg hne0]
            omega
        · -- the remaining segments were appended by the tail split
          obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          have hk' : k < rest.length := by
            simp only [List.length_cons] at hk
            omega
          have hidx : (j : ℕ) =
              segmentSlot
                (splitPacked src sl first rest.sum first_pos rest_sum_pos)
                (secondSlot src.spec) k := by
            rw [hval]
            unfold segmentSlot
            by_cases hzero : k = 0
            · subst hzero
              simp only [if_neg (by omega : ¬ (0 + 1 = 0))]
              show src.p + (0 + 1) - 1 = ((Fin.last src.p : Fin (src.p + 1)) : ℕ)
              simp
            · rw [if_neg hzero, if_neg (by omega : ¬ (k + 1 = 0))]
              show src.p + (k + 1) - 1 = src.p + 1 + k - 1
              omega
          obtain ⟨hLength, hTail, hHead⟩ := ihSeg k j hk' hidx
          refine ⟨?_, ?_, ?_⟩
          · rw [hLength, List.getD_cons_succ]
          · rw [hTail]
            unfold segmentTail
            by_cases hzero : k = 0
            · subst hzero
              rw [if_pos rfl, if_neg (by omega : ¬ (0 + 1 = 0))]
              rw [splitPacked_tail_last]
              omega
            · rw [if_neg hzero, if_neg (by omega : ¬ (k + 1 = 0))]
              show src.n + 1 + k - 1 = src.n + (k + 1) - 1
              omega
          · rw [hHead]
            unfold segmentHead
            by_cases hlast : k + 1 = rest.length
            · rw [if_pos hlast, if_pos (by simp only [List.length_cons]; omega)]
              rw [splitPacked_head_last]
            · rw [if_neg hlast, if_neg (by simp only [List.length_cons]; omega)]
              show src.n + 1 + k = src.n + (k + 1)
              omega

end OnePathSplit

/-! ## 3.  Refining every slot, described -/

section AllSlots

variable {source : PackedSpec}

/-- The number of slots present after the first `k` stable slots have been
refined.  This is `PartialRefinement.p_eq`, named. -/
def slotCount (data : SegmentData source) (k : ℕ) : ℕ :=
  ∑ i : Fin source.p, if (i : ℕ) < k then (data.segments i).length else 1

/-- The number of fresh bivalent core vertices cut by refining the first `k`
stable slots. -/
def addedCore (data : SegmentData source) (k : ℕ) : ℕ :=
  ∑ i : Fin source.p, if (i : ℕ) < k then (data.segments i).length - 1 else 0

theorem length_segments_pos (data : SegmentData source) (i : Fin source.p) :
    0 < (data.segments i).length :=
  List.length_pos_of_ne_nil (data.ne_nil i)

theorem slotCount_eq_add (data : SegmentData source) (k : ℕ) :
    slotCount data k = source.p + addedCore data k := by
  have hterm : ∀ i : Fin source.p,
      (if (i : ℕ) < k then (data.segments i).length else 1) =
        1 + (if (i : ℕ) < k then (data.segments i).length - 1 else 0) := by
    intro i
    have hpos := length_segments_pos data i
    by_cases hlt : (i : ℕ) < k
    · rw [if_pos hlt, if_pos hlt]
      omega
    · rw [if_neg hlt, if_neg hlt]
  unfold slotCount addedCore
  rw [Finset.sum_congr rfl fun i _ ↦ hterm i, Finset.sum_add_distrib]
  simp

theorem p_le_slotCount (data : SegmentData source) (k : ℕ) :
    source.p ≤ slotCount data k := by
  rw [slotCount_eq_add]
  omega

theorem slotCount_mono (data : SegmentData source) {k l : ℕ} (hkl : k ≤ l) :
    slotCount data k ≤ slotCount data l := by
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have hpos := length_segments_pos data i
  by_cases hk : (i : ℕ) < k
  · rw [if_pos hk, if_pos (lt_of_lt_of_le hk hkl)]
  · rw [if_neg hk]
    by_cases hl : (i : ℕ) < l
    · rw [if_pos hl]
      omega
    · rw [if_neg hl]

theorem slotCount_succ (data : SegmentData source) {k : ℕ} (hk : k < source.p) :
    slotCount data (k + 1) + 1 =
      slotCount data k + (data.segments ⟨k, hk⟩).length := by
  classical
  have hmem : (⟨k, hk⟩ : Fin source.p) ∈ (Finset.univ : Finset (Fin source.p)) :=
    Finset.mem_univ _
  have hcongr :
      (∑ x ∈ (Finset.univ : Finset (Fin source.p)).erase ⟨k, hk⟩,
        if (x : ℕ) < k + 1 then (data.segments x).length else 1) =
      ∑ x ∈ (Finset.univ : Finset (Fin source.p)).erase ⟨k, hk⟩,
        if (x : ℕ) < k then (data.segments x).length else 1 := by
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    have hxk : (x : ℕ) ≠ k := fun hEq ↦ (Finset.mem_erase.mp hx).1 (Fin.ext hEq)
    by_cases hlt : (x : ℕ) < k
    · rw [if_pos hlt, if_pos (Nat.lt_succ_of_lt hlt)]
    · rw [if_neg hlt, if_neg (by omega : ¬ (x : ℕ) < k + 1)]
  unfold slotCount
  rw [← Finset.sum_erase_add _ _ hmem, ← Finset.sum_erase_add _ _ hmem, hcongr]
  rw [if_pos (Nat.lt_succ_self k), if_neg (Nat.lt_irrefl k)]
  omega

/-! ### The names -/

/-- **Which refined slot carries the `m`-th segment of stable slot `i`.**  The
first segment keeps the stable slot's own index; the remaining ones occupy the
block appended while slot `i` was being refined. -/
def refinedSlot (data : SegmentData source) (i : Fin source.p) (m : ℕ) : ℕ :=
  if m = 0 then (i : ℕ) else slotCount data (i : ℕ) + m - 1

/-- **Where that refined slot starts.** -/
def refinedTail (data : SegmentData source) (i : Fin source.p) (m : ℕ) : ℕ :=
  if m = 0 then (source.spec.core.tail i : ℕ)
  else source.n + addedCore data (i : ℕ) + m - 1

/-- **and where it ends.** -/
def refinedHead (data : SegmentData source) (i : Fin source.p) (m : ℕ) : ℕ :=
  if m + 1 = (data.segments i).length then (source.spec.core.head i : ℕ)
  else source.n + addedCore data (i : ℕ) + m

/-! ### The induction -/

/-- The invariant: unrefined stable slots keep their length and both
endpoints at the same numeric index, and every already-refined segment sits at
the slot `refinedSlot` names, between the vertices `refinedTail` and
`refinedHead` name. -/
def Described (data : SegmentData source) (k : ℕ)
    (prev : PartialRefinement data k) : Prop :=
  (∀ (i : Fin source.p) (j : Fin prev.target.p), k ≤ (i : ℕ) → (i : ℕ) = (j : ℕ) →
      prev.target.spec.length j = source.spec.length i ∧
        (prev.target.spec.core.tail j : ℕ) = (source.spec.core.tail i : ℕ) ∧
          (prev.target.spec.core.head j : ℕ) = (source.spec.core.head i : ℕ)) ∧
    ∀ (i : Fin source.p) (m : ℕ) (j : Fin prev.target.p), (i : ℕ) < k →
      m < (data.segments i).length → (j : ℕ) = refinedSlot data i m →
        prev.target.spec.length j = (data.segments i).getD m 0 ∧
          (prev.target.spec.core.tail j : ℕ) = refinedTail data i m ∧
            (prev.target.spec.core.head j : ℕ) = refinedHead data i m

theorem described_initial (data : SegmentData source) :
    Described data 0 (PartialRefinement.initial data) := by
  refine ⟨fun i j _ hval ↦ ?_, fun i m j hik _ _ ↦ absurd hik (Nat.not_lt_zero _)⟩
  obtain rfl : j = i := Fin.ext hval.symm
  exact ⟨rfl, rfl, rfl⟩

/-- The ordered path split performed by one step of the slot-by-slot
refinement, named so that `valid_core_transport` can be applied to it. -/
noncomputable def stepSplit {data : SegmentData source} {k : ℕ}
    (slot : Fin source.p) (hslot : (slot : ℕ) = k)
    (prev : PartialRefinement data k) :
    Σ target, OrderedPathSplit prev.target
      ⟨(slot : ℕ), lt_of_lt_of_le slot.isLt prev.le⟩ (data.segments slot) target :=
  OrderedPathSplit.ofList prev.target
    ⟨(slot : ℕ), lt_of_lt_of_le slot.isLt prev.le⟩ (data.segments slot)
    (data.ne_nil slot) (data.pos slot)
    ((data.sum_eq slot).trans
      (prev.length_eq slot ⟨(slot : ℕ), lt_of_lt_of_le slot.isLt prev.le⟩
        (le_of_eq hslot.symm) rfl).symm)

theorem step_target {data : SegmentData source} {k : ℕ}
    (slot : Fin source.p) (hslot : (slot : ℕ) = k)
    (prev : PartialRefinement data k) :
    (PartialRefinement.step slot hslot prev).target =
      (stepSplit slot hslot prev).1 := rfl

/-- **The induction step.**  One further slot-by-slot refinement preserves the
description: the slots it does not touch keep everything, and the block it
appends is exactly the prescribed segment list of the slot just refined. -/
theorem described_step {data : SegmentData source} {k : ℕ}
    (slot : Fin source.p) (hslot : (slot : ℕ) = k)
    (prev : PartialRefinement data k) (hprev : Described data k prev) :
    Described data (k + 1) (PartialRefinement.step slot hslot prev) := by
  classical
  obtain ⟨hOld, hSeg⟩ := hprev
  have hkp : k < source.p := hslot ▸ slot.isLt
  have hp : prev.target.p = slotCount data k := prev.p_eq
  have hn : prev.target.n = source.n + addedCore data k := by
    have hne := prev.n_eq
    rw [hp, slotCount_eq_add] at hne
    omega
  obtain ⟨tOld, tSeg⟩ := valid_core_transport (stepSplit slot hslot prev).2.valid
  refine ⟨fun i j hik hval ↦ ?_, fun i m j hik hm hval ↦ ?_⟩
  · have hbound : (i : ℕ) < prev.target.p := lt_of_lt_of_le i.isLt prev.le
    have hne : (⟨(i : ℕ), hbound⟩ : Fin prev.target.p) ≠
        ⟨(slot : ℕ), lt_of_lt_of_le slot.isLt prev.le⟩ := by
      intro hEq
      simp only [Fin.mk.injEq] at hEq
      omega
    obtain ⟨l1, t1, h1⟩ := tOld ⟨(i : ℕ), hbound⟩ j hne hval
    obtain ⟨l2, t2, h2⟩ := hOld i ⟨(i : ℕ), hbound⟩ (by omega) rfl
    exact ⟨l1.trans l2, t1.trans t2, h1.trans h2⟩
  · by_cases hEq : (i : ℕ) = k
    · have hi : i = slot := Fin.ext (hEq.trans hslot.symm)
      rw [hi] at hm hval ⊢
      have hidx : (j : ℕ) = segmentSlot prev.target
          ⟨(slot : ℕ), lt_of_lt_of_le slot.isLt prev.le⟩ m := by
        rw [hval]
        unfold refinedSlot segmentSlot
        by_cases hm0 : m = 0
        · rw [if_pos hm0, if_pos hm0]
        · rw [if_neg hm0, if_neg hm0, hp, hslot]
      obtain ⟨l1, t1, h1⟩ := tSeg m j hm hidx
      obtain ⟨_, t2, h2⟩ := hOld slot ⟨(slot : ℕ), lt_of_lt_of_le slot.isLt prev.le⟩
        (le_of_eq hslot.symm) rfl
      refine ⟨l1, t1.trans ?_, h1.trans ?_⟩
      · unfold segmentTail refinedTail
        by_cases hm0 : m = 0
        · rw [if_pos hm0, if_pos hm0]
          exact t2
        · rw [if_neg hm0, if_neg hm0, hn, hslot]
      · unfold segmentHead refinedHead
        by_cases hlast : m + 1 = (data.segments slot).length
        · rw [if_pos hlast, if_pos hlast]
          exact h2
        · rw [if_neg hlast, if_neg hlast, hn, hslot]
    · have hlt : (i : ℕ) < k := by omega
      have hsucc : slotCount data ((i : ℕ) + 1) + 1 =
          slotCount data (i : ℕ) + (data.segments i).length :=
        slotCount_succ data i.isLt
      have hbound : refinedSlot data i m < prev.target.p := by
        rw [hp]
        unfold refinedSlot
        by_cases hm0 : m = 0
        · rw [if_pos hm0]
          exact lt_of_lt_of_le i.isLt (p_le_slotCount data k)
        · rw [if_neg hm0]
          have hmono := slotCount_mono data (show (i : ℕ) + 1 ≤ k by omega)
          omega
      have hne : (⟨refinedSlot data i m, hbound⟩ : Fin prev.target.p) ≠
          ⟨(slot : ℕ), lt_of_lt_of_le slot.isLt prev.le⟩ := by
        intro hEqq
        simp only [Fin.mk.injEq] at hEqq
        have hvals : refinedSlot data i m = (slot : ℕ) := hEqq
        unfold refinedSlot at hvals
        by_cases hm0 : m = 0
        · rw [if_pos hm0] at hvals
          omega
        · rw [if_neg hm0] at hvals
          have hple := p_le_slotCount data (i : ℕ)
          omega
      obtain ⟨l1, t1, h1⟩ := tOld ⟨refinedSlot data i m, hbound⟩ j hne hval.symm
      obtain ⟨l2, t2, h2⟩ := hSeg i m ⟨refinedSlot data i m, hbound⟩ hlt hm rfl
      exact ⟨l1.trans l2, t1.trans t2, h1.trans h2⟩

/-- The description holds all the way along the slot-by-slot recursion. -/
theorem described_refineUpTo (data : SegmentData source) :
    ∀ (k : ℕ) (hk : k ≤ source.p), Described data k (refineUpTo data k hk) := by
  intro k
  induction k with
  | zero => intro _; exact described_initial data
  | succ k ih =>
      intro hk
      exact described_step ⟨k, by omega⟩ rfl (refineUpTo data k (by omega))
        (ih (by omega))

/-- **The core API.**  For every stable slot `i` and every prescribed segment
index `m`, the refined slot at index `refinedSlot data i m` carries exactly the
`m`-th segment of slot `i`, and runs from `refinedTail data i m` to
`refinedHead data i m`. -/
theorem refineAllSlots_core (data : SegmentData source) (i : Fin source.p) (m : ℕ)
    (j : Fin (refineAllSlots data).p) (hm : m < (data.segments i).length)
    (hval : (j : ℕ) = refinedSlot data i m) :
    (refineAllSlots data).spec.length j = (data.segments i).getD m 0 ∧
      ((refineAllSlots data).spec.core.tail j : ℕ) = refinedTail data i m ∧
        ((refineAllSlots data).spec.core.head j : ℕ) = refinedHead data i m :=
  (described_refineUpTo data source.p le_rfl).2 i m j i.isLt hm hval

/-! ### The slot index is a bijection -/

theorem refineAllSlots_p_eq_slotCount (data : SegmentData source) :
    (refineAllSlots data).p = slotCount data source.p := by
  rw [refineAllSlots_p]
  exact (Finset.sum_congr rfl fun i _ ↦ by rw [if_pos i.isLt]).symm

theorem addedCore_mono (data : SegmentData source) {k l : ℕ} (hkl : k ≤ l) :
    addedCore data k ≤ addedCore data l := by
  refine Finset.sum_le_sum fun i _ ↦ ?_
  by_cases hk : (i : ℕ) < k
  · rw [if_pos hk, if_pos (lt_of_lt_of_le hk hkl)]
  · rw [if_neg hk]
    by_cases hl : (i : ℕ) < l
    · rw [if_pos hl]
      omega
    · rw [if_neg hl]

theorem addedCore_succ (data : SegmentData source) {k : ℕ} (hk : k < source.p) :
    addedCore data (k + 1) =
      addedCore data k + ((data.segments ⟨k, hk⟩).length - 1) := by
  have h1 := slotCount_succ data hk
  have h2 := slotCount_eq_add data (k + 1)
  have h3 := slotCount_eq_add data k
  have h4 : 0 < (data.segments ⟨k, hk⟩).length :=
    length_segments_pos data ⟨k, hk⟩
  omega

theorem refineAllSlots_n_eq (data : SegmentData source) :
    (refineAllSlots data).n = source.n + addedCore data source.p := by
  have hn := refineAllSlots_n data
  have hp := refineAllSlots_p data
  have heq := slotCount_eq_add data source.p
  rw [← refineAllSlots_p_eq_slotCount] at heq
  omega

/-- The block a refined slot belongs to: the first segment of a stable slot
stays at that slot's own index, and the later ones fill the half-open interval
of indices appended while that slot was refined. -/
theorem refinedSlot_block (data : SegmentData source) (i : Fin source.p) (m : ℕ)
    (hm : m < (data.segments i).length) :
    (m = 0 ∧ refinedSlot data i m = (i : ℕ)) ∨
      (m ≠ 0 ∧ slotCount data (i : ℕ) ≤ refinedSlot data i m ∧
        refinedSlot data i m < slotCount data ((i : ℕ) + 1)) := by
  by_cases hm0 : m = 0
  · exact Or.inl ⟨hm0, by unfold refinedSlot; rw [if_pos hm0]⟩
  · refine Or.inr ⟨hm0, ?_, ?_⟩
    · unfold refinedSlot
      rw [if_neg hm0]
      omega
    · unfold refinedSlot
      rw [if_neg hm0]
      have hsucc : slotCount data ((i : ℕ) + 1) + 1 =
          slotCount data (i : ℕ) + (data.segments i).length :=
        slotCount_succ data i.isLt
      omega

theorem refinedSlot_lt (data : SegmentData source) (i : Fin source.p) (m : ℕ)
    (hm : m < (data.segments i).length) :
    refinedSlot data i m < (refineAllSlots data).p := by
  rw [refineAllSlots_p_eq_slotCount]
  rcases refinedSlot_block data i m hm with ⟨_, hEq⟩ | ⟨_, _, hlt⟩
  · rw [hEq]
    exact lt_of_lt_of_le i.isLt (p_le_slotCount data source.p)
  · exact lt_of_lt_of_le hlt (slotCount_mono data i.isLt)

theorem refinedSlot_injective (data : SegmentData source) :
    Function.Injective fun x : Σ i : Fin source.p, Fin (data.segments i).length ↦
      refinedSlot data x.1 x.2 := by
  rintro ⟨i, m⟩ ⟨i', m'⟩ hEq
  simp only at hEq
  have hbi := refinedSlot_block data i (m : ℕ) m.isLt
  have hbi' := refinedSlot_block data i' (m' : ℕ) m'.isLt
  have hple := p_le_slotCount data (i : ℕ)
  have hple' := p_le_slotCount data (i' : ℕ)
  have hival := i.isLt
  have hival' := i'.isLt
  have hi : (i : ℕ) = (i' : ℕ) := by
    rcases Nat.lt_trichotomy (i : ℕ) (i' : ℕ) with hlt | hlt | hlt
    · have hmono := slotCount_mono data (show (i : ℕ) + 1 ≤ (i' : ℕ) by omega)
      omega
    · exact hlt
    · have hmono := slotCount_mono data (show (i' : ℕ) + 1 ≤ (i : ℕ) by omega)
      omega
  obtain rfl : i = i' := Fin.ext hi
  refine congrArg (Sigma.mk i) (Fin.ext ?_)
  unfold refinedSlot at hEq
  by_cases hm0 : (m : ℕ) = 0
  · by_cases hm0' : (m' : ℕ) = 0
    · omega
    · rw [if_pos hm0, if_neg hm0'] at hEq
      omega
  · by_cases hm0' : (m' : ℕ) = 0
    · rw [if_neg hm0, if_pos hm0'] at hEq
      omega
    · rw [if_neg hm0, if_neg hm0'] at hEq
      omega

/-- **The refined slots are named.**  Stable slot `i` and segment index `m`
together name one refined slot, every refined slot is named exactly once, and
`refineAllSlots_core` says what that slot carries. -/
noncomputable def slotIndexEquiv (data : SegmentData source) :
    (Σ i : Fin source.p, Fin (data.segments i).length) ≃
      Fin (refineAllSlots data).p :=
  Equiv.ofBijective
    (fun x ↦ ⟨refinedSlot data x.1 x.2, refinedSlot_lt data x.1 x.2 x.2.isLt⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun x y hxy ↦ refinedSlot_injective data (congrArg Fin.val hxy), by
        rw [Fintype.card_sigma, Fintype.card_fin, refineAllSlots_p]
        exact Finset.sum_congr rfl fun i _ ↦ Fintype.card_fin _⟩)

@[simp] theorem slotIndexEquiv_val (data : SegmentData source)
    (x : Σ i : Fin source.p, Fin (data.segments i).length) :
    ((slotIndexEquiv data x : Fin (refineAllSlots data).p) : ℕ) =
      refinedSlot data x.1 x.2 := rfl

/-! ### The core vertices are named too -/

/-- The core vertices of the refined specification, named on the source side:
the stable core vertices, together with one fresh bivalent vertex for each
internal breakpoint of a prescribed segment list. -/
abbrev RefinedVertex (data : SegmentData source) : Type :=
  Fin source.n ⊕ (Σ i : Fin source.p, Fin ((data.segments i).length - 1))

/-- Its numeric index in the refined core. -/
def refinedVertex (data : SegmentData source) : RefinedVertex data → ℕ
  | Sum.inl vertex => (vertex : ℕ)
  | Sum.inr breakpoint =>
      source.n + addedCore data (breakpoint.1 : ℕ) + (breakpoint.2 : ℕ)

theorem refinedVertex_lt (data : SegmentData source) (vertex : RefinedVertex data) :
    refinedVertex data vertex < (refineAllSlots data).n := by
  rw [refineAllSlots_n_eq]
  match vertex with
  | Sum.inl v =>
      have := v.isLt
      have := Nat.zero_le (addedCore data source.p)
      simp only [refinedVertex]
      omega
  | Sum.inr ⟨i, m⟩ =>
      have hsucc : addedCore data ((i : ℕ) + 1) =
          addedCore data (i : ℕ) + ((data.segments i).length - 1) :=
        addedCore_succ data i.isLt
      have hmono := addedCore_mono data (show (i : ℕ) + 1 ≤ source.p from i.isLt)
      have := m.isLt
      simp only [refinedVertex]
      omega

theorem refinedVertex_injective (data : SegmentData source) :
    Function.Injective (refinedVertex data) := by
  intro first second hEq
  match first, second with
  | Sum.inl u, Sum.inl v =>
      exact congrArg Sum.inl (Fin.ext hEq)
  | Sum.inl u, Sum.inr ⟨i, m⟩ =>
      exact absurd hEq (by have := u.isLt; simp only [refinedVertex]; omega)
  | Sum.inr ⟨i, m⟩, Sum.inl v =>
      exact absurd hEq (by have := v.isLt; simp only [refinedVertex]; omega)
  | Sum.inr ⟨i, m⟩, Sum.inr ⟨i', m'⟩ =>
      simp only [refinedVertex] at hEq
      have hsucc : addedCore data ((i : ℕ) + 1) =
          addedCore data (i : ℕ) + ((data.segments i).length - 1) :=
        addedCore_succ data i.isLt
      have hsucc' : addedCore data ((i' : ℕ) + 1) =
          addedCore data (i' : ℕ) + ((data.segments i').length - 1) :=
        addedCore_succ data i'.isLt
      have hm := m.isLt
      have hm' := m'.isLt
      have hi : (i : ℕ) = (i' : ℕ) := by
        rcases Nat.lt_trichotomy (i : ℕ) (i' : ℕ) with hlt | hlt | hlt
        · have hmono := addedCore_mono data (show (i : ℕ) + 1 ≤ (i' : ℕ) by omega)
          omega
        · exact hlt
        · have hmono := addedCore_mono data (show (i' : ℕ) + 1 ≤ (i : ℕ) by omega)
          omega
      obtain rfl : i = i' := Fin.ext hi
      exact congrArg (fun t ↦ Sum.inr (Sigma.mk i t)) (Fin.ext (by omega))

theorem card_refinedVertex (data : SegmentData source) :
    Fintype.card (RefinedVertex data) = (refineAllSlots data).n := by
  rw [refineAllSlots_n_eq, Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma]
  refine congrArg (fun total ↦ source.n + total) ?_
  unfold addedCore
  exact Finset.sum_congr rfl fun i _ ↦ by rw [if_pos i.isLt, Fintype.card_fin]

/-- **The refined core vertices are named.** -/
noncomputable def vertexIndexEquiv (data : SegmentData source) :
    RefinedVertex data ≃ Fin (refineAllSlots data).n :=
  Equiv.ofBijective (fun v ↦ ⟨refinedVertex data v, refinedVertex_lt data v⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun x y hxy ↦ refinedVertex_injective data (congrArg Fin.val hxy), by
        rw [card_refinedVertex, Fintype.card_fin]⟩)

@[simp] theorem vertexIndexEquiv_val (data : SegmentData source)
    (vertex : RefinedVertex data) :
    ((vertexIndexEquiv data vertex : Fin (refineAllSlots data).n) : ℕ) =
      refinedVertex data vertex := rfl

/-! ### The endpoints of a refined slot, named -/

/-- The vertex a refined slot starts at. -/
def segmentTailVertex (data : SegmentData source)
    (x : Σ i : Fin source.p, Fin (data.segments i).length) : RefinedVertex data :=
  if h : (x.2 : ℕ) = 0 then Sum.inl (source.spec.core.tail x.1)
  else Sum.inr ⟨x.1, ⟨(x.2 : ℕ) - 1, by have := x.2.isLt; omega⟩⟩

/-- The vertex a refined slot ends at. -/
def segmentHeadVertex (data : SegmentData source)
    (x : Σ i : Fin source.p, Fin (data.segments i).length) : RefinedVertex data :=
  if h : (x.2 : ℕ) + 1 = (data.segments x.1).length then
    Sum.inl (source.spec.core.head x.1)
  else Sum.inr ⟨x.1, ⟨(x.2 : ℕ), by have := x.2.isLt; omega⟩⟩

theorem refinedVertex_segmentTailVertex (data : SegmentData source)
    (x : Σ i : Fin source.p, Fin (data.segments i).length) :
    refinedVertex data (segmentTailVertex data x) = refinedTail data x.1 (x.2 : ℕ) := by
  unfold segmentTailVertex refinedTail
  by_cases h : (x.2 : ℕ) = 0
  · rw [dif_pos h, if_pos h]
    rfl
  · rw [dif_neg h, if_neg h]
    simp only [refinedVertex]
    omega

theorem refinedVertex_segmentHeadVertex (data : SegmentData source)
    (x : Σ i : Fin source.p, Fin (data.segments i).length) :
    refinedVertex data (segmentHeadVertex data x) = refinedHead data x.1 (x.2 : ℕ) := by
  unfold segmentHeadVertex refinedHead
  by_cases h : (x.2 : ℕ) + 1 = (data.segments x.1).length
  · rw [dif_pos h, if_pos h]
    rfl
  · rw [dif_neg h, if_neg h]
    rfl

/-! ### The core API, assembled -/

/-- **Which segment a refined slot carries.** -/
theorem refineAllSlots_length_at (data : SegmentData source)
    (x : Σ i : Fin source.p, Fin (data.segments i).length) :
    (refineAllSlots data).spec.length (slotIndexEquiv data x) =
      (data.segments x.1).getD (x.2 : ℕ) 0 :=
  (refineAllSlots_core data x.1 (x.2 : ℕ) (slotIndexEquiv data x) x.2.isLt rfl).1

/-- **Where it starts.** -/
theorem refineAllSlots_tail_at (data : SegmentData source)
    (x : Σ i : Fin source.p, Fin (data.segments i).length) :
    (refineAllSlots data).spec.core.tail (slotIndexEquiv data x) =
      vertexIndexEquiv data (segmentTailVertex data x) :=
  Fin.ext <|
    ((refineAllSlots_core data x.1 (x.2 : ℕ) (slotIndexEquiv data x)
      x.2.isLt rfl).2.1).trans
      (refinedVertex_segmentTailVertex data x).symm

/-- **and where it ends.** -/
theorem refineAllSlots_head_at (data : SegmentData source)
    (x : Σ i : Fin source.p, Fin (data.segments i).length) :
    (refineAllSlots data).spec.core.head (slotIndexEquiv data x) =
      vertexIndexEquiv data (segmentHeadVertex data x) :=
  Fin.ext <|
    ((refineAllSlots_core data x.1 (x.2 : ℕ) (slotIndexEquiv data x)
      x.2.isLt rfl).2.2).trans
      (refinedVertex_segmentHeadVertex data x).symm

/-! ### What a relabeling of the refinement *is* -/

/-- **A core model of a specification by an all-slot refinement.**  The two
bijections name, on the source side, the slots and core vertices of the
refinement; the three equations say the named slot carries the prescribed
segment and runs between the named endpoints.  `reversed` allows each slot to
be read in either direction, exactly as `SubdivisionGraph.Spec.Relabeling`
does. -/
structure CoreModel {n' p' : ℕ} (data : SegmentData source)
    (target : SubdivisionGraph.Spec n' p') where
  /-- Which slot of `target` carries the `m`-th segment of stable slot `i`. -/
  slotModel : (Σ i : Fin source.p, Fin (data.segments i).length) ≃ Fin p'
  /-- Which core vertex of `target` carries a stable core vertex or a
  breakpoint. -/
  vertexModel : RefinedVertex data ≃ Fin n'
  /-- Whether that slot is read backwards. -/
  reversed : (Σ i : Fin source.p, Fin (data.segments i).length) → Bool
  /-- It carries the prescribed segment. -/
  length_eq : ∀ x, target.length (slotModel x) = (data.segments x.1).getD (x.2 : ℕ) 0
  /-- It starts where the segment starts. -/
  tail_eq : ∀ x, target.core.tail (slotModel x) =
    vertexModel (if reversed x then segmentHeadVertex data x
      else segmentTailVertex data x)
  /-- and ends where the segment ends. -/
  head_eq : ∀ x, target.core.head (slotModel x) =
    vertexModel (if reversed x then segmentTailVertex data x
      else segmentHeadVertex data x)

namespace CoreModel

variable {n' p' : ℕ} {data : SegmentData source}
  {target : SubdivisionGraph.Spec n' p'}

/-- **A core model is a relabeling.** -/
noncomputable def relabeling (model : CoreModel data target) :
    (refineAllSlots data).spec.Relabeling target where
  coreEquiv := (vertexIndexEquiv data).symm.trans model.vertexModel
  slotEquiv := (slotIndexEquiv data).symm.trans model.slotModel
  reversed := fun edge ↦ model.reversed ((slotIndexEquiv data).symm edge)
  length_eq := by
    intro edge
    have hx := refineAllSlots_length_at data ((slotIndexEquiv data).symm edge)
    rw [Equiv.apply_symm_apply] at hx
    rw [hx]
    exact (model.length_eq _).symm
  tail_eq := by
    intro edge
    have hTail := refineAllSlots_tail_at data ((slotIndexEquiv data).symm edge)
    have hHead := refineAllSlots_head_at data ((slotIndexEquiv data).symm edge)
    rw [Equiv.apply_symm_apply] at hTail hHead
    show target.core.tail (model.slotModel ((slotIndexEquiv data).symm edge)) = _
    rw [model.tail_eq, hTail, hHead]
    by_cases hrev : model.reversed ((slotIndexEquiv data).symm edge) = true
    · simp only [hrev, if_true]
      show _ = ((vertexIndexEquiv data).symm.trans model.vertexModel)
        (vertexIndexEquiv data (segmentHeadVertex data _))
      rw [Equiv.trans_apply, Equiv.symm_apply_apply]
    · simp only [Bool.not_eq_true] at hrev
      simp only [hrev]
      show _ = ((vertexIndexEquiv data).symm.trans model.vertexModel)
        (vertexIndexEquiv data (segmentTailVertex data _))
      rw [Equiv.trans_apply, Equiv.symm_apply_apply]
      simp
  head_eq := by
    intro edge
    have hTail := refineAllSlots_tail_at data ((slotIndexEquiv data).symm edge)
    have hHead := refineAllSlots_head_at data ((slotIndexEquiv data).symm edge)
    rw [Equiv.apply_symm_apply] at hTail hHead
    show target.core.head (model.slotModel ((slotIndexEquiv data).symm edge)) = _
    rw [model.head_eq, hTail, hHead]
    by_cases hrev : model.reversed ((slotIndexEquiv data).symm edge) = true
    · simp only [hrev, if_true]
      show _ = ((vertexIndexEquiv data).symm.trans model.vertexModel)
        (vertexIndexEquiv data (segmentTailVertex data _))
      rw [Equiv.trans_apply, Equiv.symm_apply_apply]
    · simp only [Bool.not_eq_true] at hrev
      simp only [hrev]
      show _ = ((vertexIndexEquiv data).symm.trans model.vertexModel)
        (vertexIndexEquiv data (segmentHeadVertex data _))
      rw [Equiv.trans_apply, Equiv.symm_apply_apply]
      simp

/-- and therefore a Laplacian equivalence. -/
noncomputable def laplacianEquiv (model : CoreModel data target) :
    LaplacianEquiv (refineAllSlots data).graph target.graph :=
  SubdivisionGraph.Spec.laplacianEquiv _ _ model.relabeling

end CoreModel

/-- **and conversely**: a relabeling of the all-slot refinement onto a
specification *is* a core model of it.  So the core model is neither weaker
nor stronger than the relabeling; it is a source-side reading of it. -/
noncomputable def coreModelOfRelabeling {n' p' : ℕ} {data : SegmentData source}
    {target : SubdivisionGraph.Spec n' p'}
    (relabeling : (refineAllSlots data).spec.Relabeling target) :
    CoreModel data target where
  slotModel := (slotIndexEquiv data).trans relabeling.slotEquiv
  vertexModel := (vertexIndexEquiv data).trans relabeling.coreEquiv
  reversed := fun x ↦ relabeling.reversed (slotIndexEquiv data x)
  length_eq := by
    intro x
    rw [show ((slotIndexEquiv data).trans relabeling.slotEquiv) x =
      relabeling.slotEquiv (slotIndexEquiv data x) from rfl,
      ← relabeling.length_eq]
    exact refineAllSlots_length_at data x
  tail_eq := by
    intro x
    rw [show ((slotIndexEquiv data).trans relabeling.slotEquiv) x =
      relabeling.slotEquiv (slotIndexEquiv data x) from rfl,
      relabeling.tail_eq, refineAllSlots_tail_at, refineAllSlots_head_at]
    by_cases hrev : relabeling.reversed (slotIndexEquiv data x) = true <;>
      simp [hrev]
  head_eq := by
    intro x
    rw [show ((slotIndexEquiv data).trans relabeling.slotEquiv) x =
      relabeling.slotEquiv (slotIndexEquiv data x) from rfl,
      relabeling.head_eq, refineAllSlots_tail_at, refineAllSlots_head_at]
    by_cases hrev : relabeling.reversed (slotIndexEquiv data x) = true <;>
      simp [hrev]

/-- The tautological core model: the all-slot refinement models itself.  This
is the joint-satisfiability check on the six fields above — they are not a
bundle no object can satisfy. -/
noncomputable def coreModelSelf (data : SegmentData source) :
    CoreModel data (refineAllSlots data).spec where
  slotModel := slotIndexEquiv data
  vertexModel := vertexIndexEquiv data
  reversed := fun _ ↦ false
  length_eq := fun x ↦ refineAllSlots_length_at data x
  tail_eq := fun x ↦ by simpa using refineAllSlots_tail_at data x
  head_eq := fun x ↦ by simpa using refineAllSlots_head_at data x

end AllSlots

/-! ## 5.  The last mile, read on the source -/

section LastMile

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancedGlobal.Candidate
open DraismaVargas.LocalCases.InputRefinementData
open DraismaVargas.LocalCases.W4StableSource
open Utilities.Certificate.DegenerateSpec

/-! ### The canonical contraction target, unfolded -/

variable {n' p' : ℕ}

theorem contractedSpec_length (deg : DegSpec n' p') (slot : deg.PositiveSlot) :
    deg.contractedSpec.length (deg.slotIndex slot) = deg.length slot.val := by
  show deg.length (deg.slotIndex.symm (deg.slotIndex slot)).val = _
  rw [Equiv.symm_apply_apply]

theorem contractedSpec_core_tail (deg : DegSpec n' p') (slot : deg.PositiveSlot) :
    deg.contractedSpec.core.tail (deg.slotIndex slot) =
      deg.classIndex ⟨deg.rep (deg.core.tail slot.val),
        deg.rep_idem (deg.core.tail slot.val)⟩ := by
  show deg.classIndex ⟨deg.rep (deg.core.tail
      (deg.slotIndex.symm (deg.slotIndex slot)).val),
    deg.rep_idem (deg.core.tail (deg.slotIndex.symm (deg.slotIndex slot)).val)⟩ = _
  rw [Equiv.symm_apply_apply]

theorem contractedSpec_core_head (deg : DegSpec n' p') (slot : deg.PositiveSlot) :
    deg.contractedSpec.core.head (deg.slotIndex slot) =
      deg.classIndex ⟨deg.rep (deg.core.head slot.val),
        deg.rep_idem (deg.core.head slot.val)⟩ := by
  show deg.classIndex ⟨deg.rep (deg.core.head
      (deg.slotIndex.symm (deg.slotIndex slot)).val),
    deg.rep_idem (deg.core.head (deg.slotIndex.symm (deg.slotIndex slot)).val)⟩ = _
  rw [Equiv.symm_apply_apply]

/-! ### The pruned contraction target, unfolded -/

variable {target : CFGraph} {degree : ℕ}
  {gluing : GluingDatum target degree} {wall : target.V}
  {candidate : Candidate target degree gluing wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {presentation : candidate.datum.LengthMatrixPresentation coordinate}
  {coordinates : coordinate → ℚ}
  {n p : ℕ} {spec : SubdivisionGraph.Spec n p}
  {face : ClearedFace candidate presentation coordinates}

open DraismaVargas.LocalCases.BalancedGlobal.Candidate.ClearedFace.SourceContractionTopology in
/-- The kept slots of a contraction topology, indexed as the slots of its
pruned contracted spec: `slotIndex` followed by the reindexing
`Finset.equivFin` that `PendantDeletion.Spec.restrict` uses. -/
noncomputable def keptSlotIndex (topology : ClearedFace.SourceContractionTopology face) :
    {e : topology.degSpec.PositiveSlot // topology.KeptSlot e} ≃
      Fin (topology.keptSlots).card :=
  (Equiv.subtypeEquiv topology.degSpec.slotIndex fun e ↦ by
    rw [mem_keptSlots, Equiv.symm_apply_apply]).trans (topology.keptSlots).equivFin

open DraismaVargas.LocalCases.BalancedGlobal.Candidate.ClearedFace.SourceContractionTopology in
/-- The kept classes, indexed as the core vertices of the pruned contracted
spec. -/
noncomputable def keptClassIndex (topology : ClearedFace.SourceContractionTopology face) :
    {c : topology.degSpec.Class // topology.KeptClass c} ≃
      Fin (topology.keptClasses).card :=
  (Equiv.subtypeEquiv topology.degSpec.classIndex fun c ↦ by
    rw [mem_keptClasses, Equiv.symm_apply_apply]).trans (topology.keptClasses).equivFin

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem keptSlotAt_keptSlotIndex (topology : ClearedFace.SourceContractionTopology face)
    (e : {e : topology.degSpec.PositiveSlot // topology.KeptSlot e}) :
    PendantDeletion.Spec.keptSlotAt (topology.keptSlots) (keptSlotIndex topology e) =
      topology.degSpec.slotIndex e.val :=
  PendantDeletion.Spec.keptSlotAt_equivFin (topology.keptSlots) _

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem keptVertexAt_keptClassIndex (topology : ClearedFace.SourceContractionTopology face)
    (c : {c : topology.degSpec.Class // topology.KeptClass c}) :
    PendantDeletion.Spec.keptVertexAt (topology.keptClasses) (keptClassIndex topology c) =
      topology.degSpec.classIndex c.val :=
  PendantDeletion.Spec.keptVertexAt_equivFin (topology.keptClasses) _

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem prunedSpec_length (topology : ClearedFace.SourceContractionTopology face)
    (hKept : (topology.keptClasses).Nonempty)
    (e : {e : topology.degSpec.PositiveSlot // topology.KeptSlot e}) :
    (topology.prunedSpec hKept).length (keptSlotIndex topology e) =
      topology.degSpec.length e.val.val := by
  show topology.degSpec.length
    (topology.degSpec.slotIndex.symm
      (PendantDeletion.Spec.keptSlotAt (topology.keptSlots) (keptSlotIndex topology e))).val = _
  rw [keptSlotAt_keptSlotIndex, Equiv.symm_apply_apply]

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem prunedSpec_core_tail (topology : ClearedFace.SourceContractionTopology face)
    (hKept : (topology.keptClasses).Nonempty)
    (e : {e : topology.degSpec.PositiveSlot // topology.KeptSlot e}) :
    (topology.prunedSpec hKept).core.tail (keptSlotIndex topology e) =
      keptClassIndex topology
        ⟨ClearedFace.SourceContractionTopology.classOfCore topology
            (topology.degSpec.core.tail e.val.val),
          ClearedFace.SourceContractionTopology.keptClass_tail_of_keptSlot topology e.property⟩ := by
  refine PendantDeletion.Spec.keptVertexAt_injective (topology.keptClasses) ?_
  rw [keptVertexAt_keptClassIndex, ClearedFace.SourceContractionTopology.prunedSpec,
    PendantDeletion.Spec.restrict_core_tail, keptSlotAt_keptSlotIndex]
  show topology.degSpec.contractedSpec.core.tail (topology.degSpec.slotIndex e.val) = _
  rw [contractedSpec_core_tail]
  rfl

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem prunedSpec_core_head (topology : ClearedFace.SourceContractionTopology face)
    (hKept : (topology.keptClasses).Nonempty)
    (e : {e : topology.degSpec.PositiveSlot // topology.KeptSlot e}) :
    (topology.prunedSpec hKept).core.head (keptSlotIndex topology e) =
      keptClassIndex topology
        ⟨ClearedFace.SourceContractionTopology.classOfCore topology
            (topology.degSpec.core.head e.val.val),
          ClearedFace.SourceContractionTopology.keptClass_head_of_keptSlot topology e.property⟩ := by
  refine PendantDeletion.Spec.keptVertexAt_injective (topology.keptClasses) ?_
  rw [keptVertexAt_keptClassIndex, ClearedFace.SourceContractionTopology.prunedSpec,
    PendantDeletion.Spec.restrict_core_head, keptSlotAt_keptSlotIndex]
  show topology.degSpec.contractedSpec.core.head (topology.degSpec.slotIndex e.val) = _
  rw [contractedSpec_core_head]
  rfl

/-! ### A stable model of the pruned contracted quotient source -/

/-- A refined slot of the canonical refinement, named on the source: a stable
slot together with the position of a surviving source occurrence in the row
displaying it. -/
abbrev RefinedSlotIndex (iface : InputInterface spec presentation coordinates)
    (face : ClearedFace candidate presentation coordinates) : Type :=
  Σ i : Fin p, Fin ((segmentData iface face).segments i).length

/-- **The stable model of the pruned contracted quotient source.**

This is the datum an identification of the canonical refinement with the
pruned contracted source needs, written out; the core API of `refineAllSlots`
makes it statable.  The two bijections are the content:

* `slotModel` — the **kept** slots of the contraction topology (the positive
  non-dangling source occurrences, `KeptSlot`) are exactly the positive
  positions of the displayed rows, one refined slot each, with matching
  length.  Its existence contains `PresentationDecomposition.Decomposes` (the
  rows partition the surviving occurrences), and is strictly more: it is a
  bijection, not a count.
* `vertexModel` — the **kept** contraction classes of the quotient source
  (those meeting a surviving occurrence, `KeptClass`) are exactly the stable
  core vertices together with the internal breakpoints of the rows.  A bare
  function from the stable core vertices to source vertices, neither injective
  nor surjective, together with unoriented meeting vertices along the rows,
  would not suffice.

The three equations are stated in `topology.degSpec.rep`, `core` and `length`;
their codomains are the kept slots and the kept classes.  `reversed` is the
orientation with which a row traverses each occurrence; the endpoint equations
are stated with it, so no orientation is silently assumed. -/
structure SourceModel (iface : InputInterface spec presentation coordinates)
    {face : ClearedFace candidate presentation coordinates}
    (topology : ClearedFace.SourceContractionTopology face) where
  /-- Each refined slot is a kept slot, bijectively. -/
  slotModel : RefinedSlotIndex iface face ≃
    {e : topology.degSpec.PositiveSlot // topology.KeptSlot e}
  /-- Each refined core vertex is a kept contraction class, bijectively. -/
  vertexModel :
    RefinedVertex (segmentData iface face) ≃
      {c : topology.degSpec.Class // topology.KeptClass c}
  /-- The orientation with which the row traverses the occurrence. -/
  reversed : RefinedSlotIndex iface face → Bool
  /-- The occurrence carries the prescribed segment length. -/
  length_eq : ∀ x, topology.degSpec.length (slotModel x).val.val =
    ((segmentData iface face).segments x.1).getD (x.2 : ℕ) 0
  /-- It starts at the class the segment starts at. -/
  tail_eq : ∀ x, topology.degSpec.rep
      (topology.degSpec.core.tail (slotModel x).val.val) =
    (vertexModel (if reversed x then segmentHeadVertex (segmentData iface face) x
      else segmentTailVertex (segmentData iface face) x)).val.val
  /-- and ends at the class the segment ends at. -/
  head_eq : ∀ x, topology.degSpec.rep
      (topology.degSpec.core.head (slotModel x).val.val) =
    (vertexModel (if reversed x then segmentTailVertex (segmentData iface face) x
      else segmentHeadVertex (segmentData iface face) x)).val.val

namespace SourceModel

variable {iface : InputInterface spec presentation coordinates}
  {topology : ClearedFace.SourceContractionTopology face}

/-- A model keeps a class: the one carrying any stable core vertex. -/
theorem kept (model : SourceModel iface topology) :
    (topology.keptClasses).Nonempty :=
  ⟨topology.degSpec.classIndex (model.vertexModel (Sum.inl ⟨0, spec.core_nonempty⟩)).val,
    ClearedFace.SourceContractionTopology.mem_keptClasses_classIndex topology
      (model.vertexModel (Sum.inl ⟨0, spec.core_nonempty⟩)).property⟩

/-- The generic core model underlying a stable model, on the pruned contracted
spec. -/
noncomputable def coreModel (model : SourceModel iface topology) :
    CoreModel (segmentData iface face) (topology.prunedSpec model.kept) where
  slotModel := model.slotModel.trans (keptSlotIndex topology)
  vertexModel := model.vertexModel.trans (keptClassIndex topology)
  reversed := model.reversed
  length_eq := fun x ↦ by
    show (topology.prunedSpec model.kept).length
      (keptSlotIndex topology (model.slotModel x)) = _
    rw [prunedSpec_length]
    exact model.length_eq x
  tail_eq := fun x ↦ by
    show (topology.prunedSpec model.kept).core.tail
      (keptSlotIndex topology (model.slotModel x)) = _
    rw [prunedSpec_core_tail]
    exact congrArg (keptClassIndex topology) (Subtype.ext (Subtype.ext (model.tail_eq x)))
  head_eq := fun x ↦ by
    show (topology.prunedSpec model.kept).core.head
      (keptSlotIndex topology (model.slotModel x)) = _
    rw [prunedSpec_core_head]
    exact congrArg (keptClassIndex topology) (Subtype.ext (Subtype.ext (model.head_eq x)))

/-- **The identification, from the model.**  This is the single remaining
input of `InputRefinementData.inputRefinement`. -/
noncomputable def laplacianEquiv (model : SourceModel iface topology) :
    LaplacianEquiv (refinedSpec iface face).graph
      (topology.prunedSpec model.kept).graph :=
  model.coreModel.laplacianEquiv

/-- and therefore the closed-face input refinement. -/
noncomputable def inputRefinement (model : SourceModel iface topology) :
    ClearedFace.InputRefinement spec topology :=
  InputRefinementData.inputRefinement iface model.kept model.laplacianEquiv

end SourceModel

/-! ### The model implies every compatibility already known to be necessary -/

/-- The refined slots are exactly the pairs (stable slot, segment index). -/
theorem card_refinedSlotIndex (iface : InputInterface spec presentation coordinates)
    (face : ClearedFace candidate presentation coordinates) :
    Fintype.card (RefinedSlotIndex iface face) = (refinedSpec iface face).p := by
  rw [Fintype.card_sigma, show (refinedSpec iface face).p =
    (refineAllSlots (segmentData iface face)).p from rfl, refineAllSlots_p]
  exact Finset.sum_congr rfl fun i _ ↦ Fintype.card_fin _

/-- **`slotModel` is the bijective form of the slot count.**  The count of
refined slots, which also follows from `Decomposes`, is given by the model
outright: one refined slot per kept slot. -/
theorem refinedSpec_p_eq_slotCard_of_sourceModel
    {iface : InputInterface spec presentation coordinates}
    {topology : ClearedFace.SourceContractionTopology face}
    (model : SourceModel iface topology) :
    (refinedSpec iface face).p = (topology.keptSlots).card := by
  rw [← card_refinedSlotIndex iface face,
    Fintype.card_congr (model.slotModel.trans (keptSlotIndex topology)), Fintype.card_fin]

/-- The surviving slots of the contracted source are the surviving source
occurrences: `slotModel` really is a bijection onto them. -/
noncomputable def positiveSlotEquiv
    {topology : ClearedFace.SourceContractionTopology face} :
    topology.degSpec.PositiveSlot ≃
      {edge : candidate.datum.SourceEdge // 0 < face.realization.sourceLength edge} :=
  Equiv.subtypeEquiv face.realization.sourceSlotEquiv fun _ ↦ Iff.rfl

end LastMile

end DraismaVargas.LocalCases.RefinementCore
