module

public import DraismaVargas.Infrastructure.OrderedBlockSplit

@[expose] public section

/-!
# Counting the refined slots an ordered block split prescribes

**Source.**  None: this is list arithmetic, the counting companion of
`DraismaVargas.Infrastructure.OrderedBlockSplit`, which records bookkeeping
that Draisma--Vargas Part I does not write down: when a pencil built on a
trivalent model is transported back to the requested graph, one retained slot
of that model may carry several requested slots.

## The problem

A retained slot of the cubic model produced by the stable-model reduction
(`DraismaVargas.LocalCases.StableModelReduction`) can carry two requested slots
in series through a marker, so the cleared source occurrences displayed by one
row are shared out between them with prescribed totals
(`OrderedBlockSplit.blocks`). The refinement a block prescribes has one slot per
**positive** entry, so the question the consumer must answer is how many
positive entries the blocks have between them, compared with the row itself.

## What is proved

`countPos l` is the number of positive entries of `l`, i.e. the number of
refined slots `l` prescribes (`OrderedPathSplit.positiveSegments`).  `Aligned l
a` says the cut at total `a` lands on an entry boundary, `alignedB` is its
decidable form, and `cutCount l ws` counts the interior boundaries of the block
totals `ws` that are **not** aligned.  Then:

* `countPos_splitSum` -- one cut adds exactly one positive entry when it is
  misaligned (the straddled entry is split into two positive pieces) and
  exactly none when it is aligned;
* `sum_countPos_blocks` -- along a whole row,
  `((blocks l ws).map countPos).sum = countPos l + cutCount l ws`, as soon as
  the prescribed totals add up to the row total;
* `cutCount_lt_length` -- a chain of `k` blocks straddles at most `k - 1`
  entries, so the excess is bounded by the number of markers.

## What is NOT proved

Nothing is claimed about *which* cuts are aligned: alignment is a property of
the terminal face's realization, which this file never mentions.  Whether the
excess is positive at a given face is settled downstream, in
`DraismaVargas.LocalCases.RetainedRelabeling` §3.

## Consumers

`DraismaVargas.LocalCases.RetainedRelabeling`, and through it the retained
relabeling (the transport from the terminal face back to the requested core)
that `DraismaVargas.LocalCases.StatementFromLink` consumes.
-/

namespace DraismaVargas.Infrastructure.BlockSplitCount

open Utilities
open Utilities.Certificate
open Utilities.Certificate.IteratedSplitRefinement
open DraismaVargas.Infrastructure.OrderedBlockSplit


/-- The number of positive entries of a list of cleared occurrence lengths:
the number of refined slots that list prescribes. -/
def countPos (l : List ℕ) : ℕ := (OrderedPathSplit.positiveSegments l).length

@[simp] theorem countPos_nil : countPos [] = 0 := rfl

theorem countPos_cons (x : ℕ) (l : List ℕ) :
    countPos (x :: l) = (if 0 < x then 1 else 0) + countPos l := by
  unfold countPos OrderedPathSplit.positiveSegments
  by_cases h : 0 < x <;> simp [h, Nat.add_comm]

theorem countPos_eq_zero_of_sum_eq_zero {l : List ℕ} (h : l.sum = 0) : countPos l = 0 := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
      simp only [List.sum_cons] at h
      have hx : ¬ 0 < x := by omega
      rw [countPos_cons, ih (by omega), ite_eq_right hx]

/-- **The cut at total `a` lands on an occurrence boundary.**  This is the
condition under which the marker of a `CoreExpansion.SlotKind.double` slot
does not have to cut a source occurrence in two. -/
def Aligned (l : List ℕ) (a : ℕ) : Prop := ∃ k : ℕ, (l.take k).sum = a

theorem aligned_zero (l : List ℕ) : Aligned l 0 := ⟨0, by simp⟩

/-- The partial sums of a list, the totals at which a cut is aligned. -/
def partialSums (l : List ℕ) : List ℕ :=
  (List.range (l.length + 1)).map fun k ↦ (l.take k).sum

/-- A decidable test for alignment: the cut totals that land on an occurrence
boundary are the partial sums, and there are only finitely many. -/
def alignedB (l : List ℕ) (a : ℕ) : Bool := decide (a ∈ partialSums l)

theorem alignedB_iff (l : List ℕ) (a : ℕ) : alignedB l a = true ↔ Aligned l a := by
  simp only [alignedB, decide_eq_true_eq, partialSums, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, -, hk⟩
    exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    by_cases hkle : k < l.length + 1
    · exact ⟨k, hkle, hk⟩
    · refine ⟨l.length, Nat.lt_succ_self _, ?_⟩
      rw [List.take_of_length_le (le_refl l.length)]
      rw [List.take_of_length_le (by omega : l.length ≤ k)] at hk
      exact hk

/-- Cutting never loses a positive entry. -/
theorem countPos_le_splitSum (l : List ℕ) (a : ℕ) :
    countPos l ≤ countPos (splitSum l a).1 + countPos (splitSum l a).2 := by
  induction l generalizing a with
  | nil => simp
  | cons x rest ih =>
      by_cases h : x ≤ a
      · rw [splitSum_cons_of_le rest h]
        have hih := ih (a - x)
        simp only [countPos_cons]
        omega
      · rw [splitSum_cons_of_gt rest h]
        have hx : 0 < x := by omega
        have hxa : 0 < x - a := by omega
        simp only [countPos_cons, countPos_nil, ite_eq_left hx, ite_eq_left hxa]
        split_ifs <;> omega

/-- **and a misaligned cut gains exactly one**: the straddled occurrence is
split into two positive pieces. -/
theorem countPos_splitSum_of_not_aligned {l : List ℕ} {a : ℕ} (hle : a ≤ l.sum)
    (hAl : ¬ Aligned l a) :
    countPos (splitSum l a).1 + countPos (splitSum l a).2 = countPos l + 1 := by
  induction l generalizing a with
  | nil =>
      simp only [List.sum_nil, Nat.le_zero] at hle
      exact absurd (hle ▸ aligned_zero ([] : List ℕ)) hAl
  | cons x rest ih =>
      by_cases h : x ≤ a
      · have hrest : a - x ≤ rest.sum := by
          simp only [List.sum_cons] at hle
          omega
        have hAl' : ¬ Aligned rest (a - x) := by
          rintro ⟨k, hk⟩
          refine hAl ⟨k + 1, ?_⟩
          rw [List.take_succ_cons, List.sum_cons, hk]
          omega
        rw [splitSum_cons_of_le rest h]
        have hih := ih hrest hAl'
        simp only [countPos_cons]
        omega
      · have ha : a ≠ 0 := by
          rintro rfl
          exact hAl (aligned_zero _)
        have hx : 0 < x := by omega
        have hxa : 0 < x - a := by omega
        rw [splitSum_cons_of_gt rest h]
        simp only [countPos_cons, countPos_nil, ite_eq_left hx, ite_eq_left hxa,
          ite_eq_left (Nat.pos_of_ne_zero ha)]
        omega

/-- **and an aligned cut gains nothing**: no occurrence is straddled. -/
theorem countPos_splitSum_of_aligned {l : List ℕ} {a : ℕ} (hAl : Aligned l a) :
    countPos (splitSum l a).1 + countPos (splitSum l a).2 = countPos l := by
  induction l generalizing a with
  | nil => simp
  | cons x rest ih =>
      obtain ⟨k, hk⟩ := hAl
      by_cases h : x ≤ a
      · have hAl' : Aligned rest (a - x) := by
          cases k with
          | zero =>
              simp only [List.take_zero, List.sum_nil] at hk
              exact ⟨0, by simp; omega⟩
          | succ k' =>
              refine ⟨k', ?_⟩
              rw [List.take_succ_cons, List.sum_cons] at hk
              omega
        rw [splitSum_cons_of_le rest h]
        simp only [countPos_cons]
        rw [Nat.add_assoc, ih hAl']
      · have ha : a = 0 := by
          cases k with
          | zero => simpa using hk.symm
          | succ k' =>
              rw [List.take_succ_cons, List.sum_cons] at hk
              omega
        subst ha
        rw [splitSum_cons_of_gt rest h]
        have hx : 0 < x := by omega
        simp only [countPos_cons, countPos_nil, Nat.sub_zero, ite_eq_left hx,
          ite_eq_right (lt_irrefl 0)]
        omega

/-- **The exact effect of one cut.** -/
theorem countPos_splitSum {l : List ℕ} {a : ℕ} (hle : a ≤ l.sum) :
    countPos (splitSum l a).1 + countPos (splitSum l a).2 =
      countPos l + (if alignedB l a then 0 else 1) := by
  by_cases hAl : Aligned l a
  · rw [ite_eq_left ((alignedB_iff l a).mpr hAl), countPos_splitSum_of_aligned hAl, Nat.add_zero]
  · rw [ite_eq_right (by simpa only [alignedB_iff] using hAl),
      countPos_splitSum_of_not_aligned hle hAl]

/-- **How many occurrences a whole row's cuts straddle.**  One per interior
block boundary that is not a partial sum of the cleared occurrence lengths
still to come. -/
def cutCount : List ℕ → List ℕ → ℕ
  | _, [] => 0
  | _, [_] => 0
  | l, w :: w' :: ws => (if alignedB l w then 0 else 1) + cutCount (splitSum l w).2 (w' :: ws)

@[simp] theorem cutCount_nil (l : List ℕ) : cutCount l [] = 0 := rfl

@[simp] theorem cutCount_singleton (l : List ℕ) (w : ℕ) : cutCount l [w] = 0 := rfl

theorem cutCount_cons_cons (l : List ℕ) (w w' : ℕ) (ws : List ℕ) :
    cutCount l (w :: w' :: ws) =
      (if alignedB l w then 0 else 1) + cutCount (splitSum l w).2 (w' :: ws) := rfl

/-- **A cut chain straddles fewer occurrences than it has blocks.** -/
theorem cutCount_lt_length : ∀ (l ws : List ℕ), ws ≠ [] → cutCount l ws < ws.length := by
  intro l ws
  induction ws generalizing l with
  | nil => intro h; exact absurd rfl h
  | cons w ws ih =>
      cases ws with
      | nil => intro _; simp
      | cons w' ws' =>
          intro _
          rw [cutCount_cons_cons]
          have hih := ih (splitSum l w).2 (by simp)
          simp only [List.length_cons] at hih ⊢
          split_ifs <;> omega

/-- **The refined slots a cut row prescribes, exactly.**  Cutting a row into
blocks of prescribed totals adds one refined slot for each straddled
occurrence and nothing else. -/
theorem sum_countPos_blocks : ∀ (l ws : List ℕ), ws.sum = l.sum →
    ((blocks l ws).map countPos).sum = countPos l + cutCount l ws := by
  intro l ws
  induction ws generalizing l with
  | nil =>
      intro hsum
      simp only [List.sum_nil] at hsum
      simp only [blocks_nil, List.map_nil, List.sum_nil, cutCount_nil, Nat.add_zero]
      exact (countPos_eq_zero_of_sum_eq_zero hsum.symm).symm
  | cons w ws ih =>
      cases ws with
      | nil => intro _; simp
      | cons w' ws' =>
          intro hsum
          have hle : w ≤ l.sum := by
            simp only [List.sum_cons] at hsum
            omega
          have hrest : (w' :: ws').sum = (splitSum l w).2.sum := by
            rw [sum_splitSum_snd hle]
            simp only [List.sum_cons] at hsum ⊢
            omega
          have hsplit := countPos_splitSum hle
          rw [blocks_cons_cons, cutCount_cons_cons]
          simp only [List.map_cons, List.sum_cons]
          rw [ih (splitSum l w).2 hrest]
          omega

end DraismaVargas.Infrastructure.BlockSplitCount
