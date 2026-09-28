import Utilities.Subdivision.PathSplitRefinement

/-!
# Refining every subdivision slot, not just one

`Utilities.Certificate.IteratedSplitRefinement.OrderedPathSplit` replaces a
**single** positive subdivision slot by an ordered list of positive segment
lengths, and `OrderedPathSplit.ofList` builds it.  A point of a closed cone
face in the Draisma--Vargas construction (Draisma--Vargas Part I,
arXiv:1909.12924), however, prescribes a segment list for *every* slot at
once.  This file iterates the one-slot construction over all slots and
packages the result as a `CanonicalSplitChain`, hence as a
`RefinementPresentation`.

The bookkeeping, not the mathematics, is the content.  `splitPacked` keeps the
old slots at `Fin.castSucc` and appends the fresh slot at `Fin.last`, so after
refining slots `0, …, k-1` an original slot `i` still sits at *numerically the
same index* in the current target, while the target has grown.  That is the
invariant carried by `PartialRefinement`:

* `le`        : the slot count never decreases;
* `length_eq` : an unrefined slot keeps its length at the same numeric index;
* `p_eq`      : the exact slot count, `∑ i, if i < k then (segments i).length else 1`;
* `n_eq`      : each split adds one core vertex and one slot;
* `total_eq`  : the total metric length is unchanged.

The headline consequences are `refineAllSlots_p` (the refined presentation has
exactly `∑ i, (segments i).length` slots), `refineAllSlots_total_length`, and
`refineAllSlotsPresentationOf`, which is the `RefinementPresentation` such a
closed cone face needs.

Stating `length_eq` through raw `Fin.val` equalities rather than through
`Fin.castLE` is what keeps the induction free of cast transport: the two sides
live in different `Fin` types by construction, and only their numeric values
are ever compared.  A `Fin.castLE` corollary is supplied for downstream use.
-/

namespace DraismaVargas.LocalCases.SlotRefinement

open Utilities
open Utilities.Certificate
open Utilities.Certificate.OneEdgeSplitRefinement
open Utilities.Certificate.IteratedSplitRefinement

/-! ## Slot transport along one ordered path split -/

section OnePathSplit

variable {source target : PackedSpec} {slot : Fin source.p} {segments : List ℕ}

/-- The three facts about an ordered path split that a slot-by-slot refinement
needs, proved by a single induction on the retained chain shape: the exact new
slot count, the exact new core vertex count, and invariance of the length of
every *other* slot at the same numeric index. -/
theorem valid_transport {chain : CanonicalSplitChain source target}
    (valid : OrderedPathSplitValid source slot segments target chain) :
    target.p + 1 = source.p + segments.length ∧
      target.n + 1 = source.n + segments.length ∧
      ∀ (i : Fin source.p) (j : Fin target.p), i ≠ slot → (i : ℕ) = (j : ℕ) →
        target.spec.length j = source.spec.length i := by
  induction valid with
  | singleton source slot =>
      refine ⟨by simp, by simp, ?_⟩
      intro i j _ hval
      exact congrArg source.spec.length (Fin.ext hval.symm)
  | cons src sl first rest first_pos rest_sum_pos length_sum tail ih =>
      obtain ⟨ihp, ihn, ihlength⟩ := ih
      rw [show (splitPacked src sl first rest.sum first_pos rest_sum_pos).p
        = src.p + 1 from rfl] at ihp
      rw [show (splitPacked src sl first rest.sum first_pos rest_sum_pos).n
        = src.n + 1 from rfl] at ihn
      refine ⟨by simp only [List.length_cons]; omega,
        by simp only [List.length_cons]; omega, ?_⟩
      intro i j hi hval
      have hne : (i.castSucc : Fin (src.p + 1)) ≠ secondSlot src.spec :=
        Fin.castSucc_ne_last i
      have := ihlength i.castSucc j hne (by simpa using hval)
      rw [this]
      show splitLength src.spec sl first rest.sum (oldSlot src.spec i) =
        src.spec.length i
      simp [hi]

/-- One ordered path split preserves the total metric length: it only cuts
existing slots. -/
theorem valid_total_length {chain : CanonicalSplitChain source target}
    (valid : OrderedPathSplitValid source slot segments target chain) :
    ∑ j : Fin target.p, target.spec.length j =
      ∑ i : Fin source.p, source.spec.length i := by
  induction valid with
  | singleton source slot => rfl
  | cons src sl first rest first_pos rest_sum_pos length_sum tail ih =>
      refine ih.trans ?_
      show ∑ j : Fin (src.p + 1), splitLength src.spec sl first rest.sum j =
        ∑ i : Fin src.p, src.spec.length i
      rw [Fin.sum_univ_castSucc]
      have hold : ∀ i : Fin src.p,
          splitLength src.spec sl first rest.sum i.castSucc =
            if i = sl then first else src.spec.length i :=
        fun i => splitLength_old src.spec sl first rest.sum i
      have hlast : splitLength src.spec sl first rest.sum (Fin.last src.p) =
          rest.sum := splitLength_second src.spec sl first rest.sum
      rw [Finset.sum_congr rfl fun i _ => hold i, hlast,
        ← Finset.sum_erase_add _ _ (Finset.mem_univ sl),
        ← Finset.sum_erase_add _ _ (Finset.mem_univ sl)]
      have hc : (∑ x ∈ (Finset.univ : Finset (Fin src.p)).erase sl,
            if x = sl then first else src.spec.length x) =
          ∑ x ∈ (Finset.univ : Finset (Fin src.p)).erase sl, src.spec.length x :=
        Finset.sum_congr rfl fun x hx => by simp [(Finset.mem_erase.mp hx).1]
      rw [hc, if_pos rfl]
      omega

end OnePathSplit

section OnePathSplitCorollaries

variable {source target : PackedSpec} {slot : Fin source.p} {segments : List ℕ}

/-- One ordered path split of a slot into `segments` adds exactly
`segments.length - 1` slots. -/
theorem pathSplit_p_succ_eq (split : OrderedPathSplit source slot segments target) :
    target.p + 1 = source.p + segments.length :=
  (valid_transport split.valid).1

/-- It adds exactly `segments.length - 1` core vertices as well. -/
theorem pathSplit_n_succ_eq (split : OrderedPathSplit source slot segments target) :
    target.n + 1 = source.n + segments.length :=
  (valid_transport split.valid).2.1

/-- Every slot other than the split one keeps its length at the same numeric
index.  This is the form the slot-by-slot induction uses: the two indices live
in different `Fin` types and only their values are compared. -/
theorem pathSplit_length_eq_of_val
    (split : OrderedPathSplit source slot segments target)
    (i : Fin source.p) (j : Fin target.p) (hi : i ≠ slot)
    (hval : (i : ℕ) = (j : ℕ)) :
    target.spec.length j = source.spec.length i :=
  (valid_transport split.valid).2.2 i j hi hval

/-- A refined slot always receives at least one segment. -/
theorem pathSplit_segments_ne_nil
    (split : OrderedPathSplit source slot segments target) : segments ≠ [] := by
  intro hnil
  have hsum := OrderedPathSplit.sum_eq split
  have hpos := source.spec.length_pos slot
  rw [hnil] at hsum
  simp only [List.sum_nil] at hsum
  omega

/-- Consequently the slot count never decreases. -/
theorem pathSplit_p_le (split : OrderedPathSplit source slot segments target) :
    source.p ≤ target.p := by
  have hlen : 0 < segments.length :=
    List.length_pos_of_ne_nil (pathSplit_segments_ne_nil split)
  have := pathSplit_p_succ_eq split
  omega

/-- One ordered path split preserves the total metric length. -/
theorem pathSplit_total_length
    (split : OrderedPathSplit source slot segments target) :
    ∑ j : Fin target.p, target.spec.length j =
      ∑ i : Fin source.p, source.spec.length i :=
  valid_total_length split.valid

/-- The `Fin.castLE` form of `pathSplit_length_eq_of_val`. -/
theorem pathSplit_length_castLE
    (split : OrderedPathSplit source slot segments target)
    (h : source.p ≤ target.p) (i : Fin source.p) (hi : i ≠ slot) :
    target.spec.length (Fin.castLE h i) = source.spec.length i :=
  pathSplit_length_eq_of_val split i (Fin.castLE h i) hi rfl

end OnePathSplitCorollaries

/-! ## Prescribing a refinement of every slot -/

/-- An ordered list of positive segment lengths for **every** slot of a packed
subdivision specification, each summing to that slot's length. -/
structure SegmentData (source : PackedSpec) where
  /-- The ordered segment lengths replacing each slot. -/
  segments : Fin source.p → List ℕ
  /-- Every prescribed segment is positive. -/
  pos : ∀ slot : Fin source.p, ∀ length ∈ segments slot, 0 < length
  /-- Each slot's segments recover its length. -/
  sum_eq : ∀ slot : Fin source.p, (segments slot).sum = source.spec.length slot

namespace SegmentData

variable {source : PackedSpec}

/-- No slot is prescribed the empty list: its length is positive. -/
theorem ne_nil (data : SegmentData source) (slot : Fin source.p) :
    data.segments slot ≠ [] := by
  intro hnil
  have hsum := data.sum_eq slot
  have hpos := source.spec.length_pos slot
  rw [hnil] at hsum
  simp only [List.sum_nil] at hsum
  omega

/-- Segment data from lists which may contain zero entries, as emitted by a
closed cone face where some source occurrences are contracted.  The zero
entries are discarded by `OrderedPathSplit.positiveSegments`. -/
def ofListsWithZeros (source : PackedSpec)
    (segments : Fin source.p → List ℕ)
    (sum_eq : ∀ slot : Fin source.p,
      (segments slot).sum = source.spec.length slot) :
    SegmentData source where
  segments slot := OrderedPathSplit.positiveSegments (segments slot)
  pos slot := OrderedPathSplit.positiveSegments_all_pos (segments slot)
  sum_eq slot := by
    rw [OrderedPathSplit.sum_positiveSegments]
    exact sum_eq slot

@[simp] theorem ofListsWithZeros_segments (source : PackedSpec)
    (segments : Fin source.p → List ℕ)
    (sum_eq : ∀ slot : Fin source.p,
      (segments slot).sum = source.spec.length slot) (slot : Fin source.p) :
    (ofListsWithZeros source segments sum_eq).segments slot =
      OrderedPathSplit.positiveSegments (segments slot) :=
  rfl

end SegmentData

/-! ## The slot-by-slot refinement -/

/-- The explicit induction invariant: a canonical split chain refining exactly
the slots with index `< k`, together with everything the next step needs.

`length_eq` is the load-bearing clause.  It says an *unrefined* slot `i` of
`source` is still present in `target` at the same numeric index, with the same
length — which is exactly what `splitPacked`'s "old slots at `Fin.castSucc`,
fresh slot at `Fin.last`" convention guarantees, and what lets the next step
locate slot `k` without transporting any earlier cast. -/
structure PartialRefinement {source : PackedSpec} (data : SegmentData source)
    (k : ℕ) where
  /-- The presentation reached after refining the first `k` slots. -/
  target : PackedSpec
  /-- The canonical chain of positive bivalent splits reaching it. -/
  chain : CanonicalSplitChain source target
  /-- Slots are only ever added. -/
  le : source.p ≤ target.p
  /-- An unrefined slot keeps its index and its length. -/
  length_eq : ∀ (i : Fin source.p) (j : Fin target.p), k ≤ (i : ℕ) →
    (i : ℕ) = (j : ℕ) → target.spec.length j = source.spec.length i
  /-- The exact slot count so far. -/
  p_eq : target.p =
    ∑ i : Fin source.p, if (i : ℕ) < k then (data.segments i).length else 1
  /-- Each split adds one core vertex and one slot. -/
  n_eq : target.n + source.p = source.n + target.p
  /-- Splitting only cuts slots, so the total metric length is unchanged. -/
  total_eq : ∑ j : Fin target.p, target.spec.length j =
    ∑ i : Fin source.p, source.spec.length i

namespace PartialRefinement

variable {source : PackedSpec} {data : SegmentData source}

/-- Refining no slot at all: the empty chain. -/
def initial (data : SegmentData source) : PartialRefinement data 0 where
  target := source
  chain := .refl
  le := le_rfl
  length_eq i j _ hval := congrArg source.spec.length (Fin.ext hval.symm)
  p_eq := by simp
  n_eq := rfl
  total_eq := rfl

/-- Refine one further slot.  `slot` is the `source` slot whose index is `k`;
`pos` is its position in the current target, which by the invariant is the
numerically identical index. -/
noncomputable def step {k : ℕ} (slot : Fin source.p) (hslot : (slot : ℕ) = k)
    (prev : PartialRefinement data k) : PartialRefinement data (k + 1) :=
  let pos : Fin prev.target.p := ⟨(slot : ℕ), lt_of_lt_of_le slot.isLt prev.le⟩
  let split := OrderedPathSplit.ofList prev.target pos (data.segments slot)
    (data.ne_nil slot) (data.pos slot)
    ((data.sum_eq slot).trans
      (prev.length_eq slot pos (le_of_eq hslot.symm) rfl).symm)
  { target := split.1
    chain := prev.chain.append split.2.chain
    le := prev.le.trans (pathSplit_p_le split.2)
    length_eq := by
      intro i j hi hval
      have hlt : (i : ℕ) < prev.target.p := lt_of_lt_of_le i.isLt prev.le
      have hne : (⟨(i : ℕ), hlt⟩ : Fin prev.target.p) ≠ pos := by
        intro hEq
        have hval' := congrArg Fin.val hEq
        simp only [pos] at hval'
        omega
      refine (pathSplit_length_eq_of_val split.2 ⟨(i : ℕ), hlt⟩ j hne hval).trans ?_
      exact prev.length_eq i ⟨(i : ℕ), hlt⟩ (by omega) rfl
    p_eq := by
      have hp := pathSplit_p_succ_eq split.2
      have hprev := prev.p_eq
      have hmem : slot ∈ (Finset.univ : Finset (Fin source.p)) := Finset.mem_univ _
      have hsucc :
          (∑ i : Fin source.p,
              if (i : ℕ) < k + 1 then (data.segments i).length else 1) + 1 =
            (∑ i : Fin source.p,
              if (i : ℕ) < k then (data.segments i).length else 1) +
                (data.segments slot).length := by
        have hcongr :
            (∑ x ∈ (Finset.univ : Finset (Fin source.p)).erase slot,
              if (x : ℕ) < k + 1 then (data.segments x).length else 1) =
            ∑ x ∈ (Finset.univ : Finset (Fin source.p)).erase slot,
              if (x : ℕ) < k then (data.segments x).length else 1 := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          have hxk : (x : ℕ) ≠ k := by
            intro hEq
            exact (Finset.mem_erase.mp hx).1 (Fin.ext (hEq.trans hslot.symm))
          by_cases hlt : (x : ℕ) < k
          · simp [hlt, Nat.lt_succ_of_lt hlt]
          · have hlt' : ¬ (x : ℕ) < k + 1 := by omega
            simp [hlt, hlt']
        have hnew : (if (slot : ℕ) < k + 1 then (data.segments slot).length
            else 1) = (data.segments slot).length := by simp [hslot]
        have hold : (if (slot : ℕ) < k then (data.segments slot).length
            else 1) = 1 := by simp [hslot]
        rw [← Finset.sum_erase_add _ _ hmem, ← Finset.sum_erase_add _ _ hmem,
          hcongr, hnew, hold]
        omega
      omega
    n_eq := by
      have hp := pathSplit_p_succ_eq split.2
      have hn := pathSplit_n_succ_eq split.2
      have hprev := prev.n_eq
      omega
    total_eq := (pathSplit_total_length split.2).trans prev.total_eq }

end PartialRefinement

/-- Refine the slots with index `< k`, by structural recursion on `k`. -/
noncomputable def refineUpTo {source : PackedSpec} (data : SegmentData source) :
    ∀ k : ℕ, k ≤ source.p → PartialRefinement data k
  | 0, _ => PartialRefinement.initial data
  | k + 1, hk =>
      PartialRefinement.step ⟨k, by omega⟩ rfl
        (refineUpTo data k (by omega))

/-! ## Refining every slot -/

section AllSlots

variable {source : PackedSpec}

/-- The packed specification obtained by refining **every** slot of `source`
according to `data`, one slot at a time from left to right. -/
noncomputable def refineAllSlots (data : SegmentData source) : PackedSpec :=
  (refineUpTo data source.p le_rfl).target

/-- The canonical chain of positive bivalent splits realizing it. -/
noncomputable def refineAllSlotsChain (data : SegmentData source) :
    CanonicalSplitChain source (refineAllSlots data) :=
  (refineUpTo data source.p le_rfl).chain

/-- The refined specification has exactly one slot per prescribed segment. -/
theorem refineAllSlots_p (data : SegmentData source) :
    (refineAllSlots data).p = ∑ i : Fin source.p, (data.segments i).length := by
  have h : (refineAllSlots data).p =
      ∑ i : Fin source.p,
        if (i : ℕ) < source.p then (data.segments i).length else 1 :=
    (refineUpTo data source.p le_rfl).p_eq
  rw [h]
  exact Finset.sum_congr rfl fun i _ => by simp [i.isLt]

/-- Every new slot comes with exactly one new bivalent core vertex. -/
theorem refineAllSlots_n (data : SegmentData source) :
    (refineAllSlots data).n + source.p =
      source.n + ∑ i : Fin source.p, (data.segments i).length := by
  have hn : (refineAllSlots data).n + source.p =
      source.n + (refineAllSlots data).p :=
    (refineUpTo data source.p le_rfl).n_eq
  rwa [refineAllSlots_p] at hn

/-- The refinement is metric: the total edge length is unchanged. -/
theorem refineAllSlots_total_length (data : SegmentData source) :
    ∑ j : Fin (refineAllSlots data).p, (refineAllSlots data).spec.length j =
      ∑ i : Fin source.p, source.spec.length i :=
  (refineUpTo data source.p le_rfl).total_eq

/-- The all-slot refinement, presented as itself: no relabeling is needed when
the canonical append-at-the-end model is the presentation used. -/
noncomputable def refineAllSlotsPresentation (data : SegmentData source) :
    RefinementPresentation source (refineAllSlots data).graph :=
  RefinementPresentation.ofChain (refineAllSlotsChain data)
    (identityLaplacianEquiv (refineAllSlots data).spec)

/-- The all-slot refinement followed by a checked relabeling onto the
presentation an external certificate actually emits.  This is the form needed
when the refined graph is presented by such a certificate. -/
noncomputable def refineAllSlotsPresentationOf {presented : CFGraph}
    (data : SegmentData source)
    (relabeling : LaplacianEquiv (refineAllSlots data).graph presented) :
    RefinementPresentation source presented :=
  RefinementPresentation.ofChain (refineAllSlotsChain data) relabeling

/-- Refining every slot preserves Brill--Noether existence, in both
directions and for every rank and degree. -/
theorem refineAllSlots_bnExists_iff (data : SegmentData source) (r d : ℤ) :
    BNExists source.graph r d ↔ BNExists (refineAllSlots data).graph r d :=
  (refineAllSlotsChain data).bnExists_iff r d

end AllSlots

/-! ## The contracted variant

A closed cone face prescribes segment lists in which some entries have been
cleared to zero.  `OrderedPathSplit.positiveSegments` discards those before any
split occurs, which is exactly the contraction the face performs. -/

section WithZeros

variable (source : PackedSpec) (segments : Fin source.p → List ℕ)
  (sum_eq : ∀ slot : Fin source.p, (segments slot).sum = source.spec.length slot)

/-- The all-slot refinement prescribed by segment lists that may contain zero
entries. -/
noncomputable def refineAllSlotsWithZeros : PackedSpec :=
  refineAllSlots (SegmentData.ofListsWithZeros source segments sum_eq)

/-- Its canonical split chain. -/
noncomputable def refineAllSlotsWithZerosChain :
    CanonicalSplitChain source (refineAllSlotsWithZeros source segments sum_eq) :=
  refineAllSlotsChain _

/-- Its slot count counts only the positive prescribed segments. -/
theorem refineAllSlotsWithZeros_p :
    (refineAllSlotsWithZeros source segments sum_eq).p =
      ∑ i : Fin source.p,
        (OrderedPathSplit.positiveSegments (segments i)).length :=
  refineAllSlots_p _

/-- It is metric. -/
theorem refineAllSlotsWithZeros_total_length :
    ∑ j : Fin (refineAllSlotsWithZeros source segments sum_eq).p,
        (refineAllSlotsWithZeros source segments sum_eq).spec.length j =
      ∑ i : Fin source.p, source.spec.length i :=
  refineAllSlots_total_length _

/-- Its presentation obligation. -/
noncomputable def refineAllSlotsWithZerosPresentation :
    RefinementPresentation source
      (refineAllSlotsWithZeros source segments sum_eq).graph :=
  refineAllSlotsPresentation _

/-- Brill--Noether existence is preserved. -/
theorem refineAllSlotsWithZeros_bnExists_iff (r d : ℤ) :
    BNExists source.graph r d ↔
      BNExists (refineAllSlotsWithZeros source segments sum_eq).graph r d :=
  refineAllSlots_bnExists_iff _ r d

end WithZeros

end DraismaVargas.LocalCases.SlotRefinement
