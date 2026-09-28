import Utilities.Subdivision.PathSplitRefinement

/-!
# Cutting an ordered list of occurrence lengths into blocks of prescribed sums

**Source.**  None: this is list surgery, needed when a pencil built on a
trivalent model is transported back to the requested graph, where a `double`
row's occurrence list has to be split at its marker.  Draisma--Vargas Part I
does not write this step down.

## The problem

The reduction to a trivalent model presents a requested combinatorial type as a
point of the closed cone of a trivalent one.
A retained slot of the cubic model can carry **two** requested slots in series
through a marker (`CoreExpansion.SlotKind.double`), so the cleared source
occurrences displayed by that one row have to be shared out between the two
requested slots, in order, with prescribed totals.  The marker sits at a
prescribed metric position along the row and the terminal source need not have
an occurrence boundary there, so one occurrence may have to be cut in two.

## What is proved

`splitSum L a` cuts `L` after total `a`, splitting at most one entry
(`length_splitSum_le`), with `(splitSum L a).1.sum = a` and
`(splitSum L a).2.sum = L.sum - a` once `a ≤ L.sum`
(`sum_splitSum_fst`, `sum_splitSum_snd`); the two parts always recombine
(`sum_splitSum_add`).  `blocks L ws` iterates it, cutting `L` into
`ws.length` blocks whose sums are `ws` entry by entry
(`length_blocks`, `sum_getD_blocks`), the last block taking whatever is left.

Cutting an entry in two is invisible to the consumer:
`Utilities.Certificate.SubdivisionGraph.Spec.graph` is the *unit* subdivision, so
placing an extra core vertex at an interior integer point of a slot does not
change the graph.  That is why this file has no geometric content and why the
refinement receipt built from it is no weaker than the uncut one.

## Consumers

`DraismaVargas.LocalCases.InputRefinementData.Retained.blockSegments` and
everything downstream of it (`Retained.segmentData`, `Retained.refinedSpec`,
`Retained.inputRefinement`), and through them the transport of a pencil from
the trivalent model back to the requested graph.
-/

namespace DraismaVargas.Infrastructure.OrderedBlockSplit

/-! ## 1.  One cut -/

/-- Cut `l` after total `a`: the first component accumulates whole entries while
they fit and then takes the part of the straddling entry that still fits, and
the second component keeps the remainder.  At most one entry of `l` is split. -/
def splitSum : List ℕ → ℕ → List ℕ × List ℕ
  | [], _ => ([], [])
  | x :: rest, a =>
      if x ≤ a then (x :: (splitSum rest (a - x)).1, (splitSum rest (a - x)).2)
      else ([a], (x - a) :: rest)

@[simp] theorem splitSum_nil (a : ℕ) : splitSum [] a = ([], []) := rfl

theorem splitSum_cons_of_le {x a : ℕ} (rest : List ℕ) (h : x ≤ a) :
    splitSum (x :: rest) a =
      (x :: (splitSum rest (a - x)).1, (splitSum rest (a - x)).2) := by
  simp only [splitSum, if_pos h]

theorem splitSum_cons_of_gt {x a : ℕ} (rest : List ℕ) (h : ¬ x ≤ a) :
    splitSum (x :: rest) a = ([a], (x - a) :: rest) := by
  simp only [splitSum, if_neg h]

/-- **The two parts always recombine.** -/
theorem sum_splitSum_add (l : List ℕ) (a : ℕ) :
    (splitSum l a).1.sum + (splitSum l a).2.sum = l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x rest ih =>
      by_cases h : x ≤ a
      · rw [splitSum_cons_of_le rest h]
        simp only [List.sum_cons]
        rw [Nat.add_assoc, ih (a - x)]
      · rw [splitSum_cons_of_gt rest h]
        simp only [List.sum_cons, List.sum_nil]
        omega

/-- **The first part has the prescribed total**, as soon as there is enough. -/
theorem sum_splitSum_fst {l : List ℕ} {a : ℕ} (h : a ≤ l.sum) :
    (splitSum l a).1.sum = a := by
  induction l generalizing a with
  | nil =>
      simp only [List.sum_nil] at h
      simp [Nat.le_zero.mp h]
  | cons x rest ih =>
      simp only [List.sum_cons] at h
      by_cases hx : x ≤ a
      · rw [splitSum_cons_of_le rest hx]
        have hrest : a - x ≤ rest.sum := by omega
        simp only [List.sum_cons]
        rw [ih hrest]
        omega
      · rw [splitSum_cons_of_gt rest hx]
        simp

/-- **and the second part has the rest.** -/
theorem sum_splitSum_snd {l : List ℕ} {a : ℕ} (h : a ≤ l.sum) :
    (splitSum l a).2.sum = l.sum - a := by
  have hadd := sum_splitSum_add l a
  rw [sum_splitSum_fst h] at hadd
  omega

/-- **At most one entry is split.** -/
theorem length_splitSum_le (l : List ℕ) (a : ℕ) :
    (splitSum l a).1.length + (splitSum l a).2.length ≤ l.length + 1 := by
  induction l generalizing a with
  | nil => simp
  | cons x rest ih =>
      by_cases h : x ≤ a
      · rw [splitSum_cons_of_le rest h]
        simp only [List.length_cons]
        have := ih (a - x)
        omega
      · rw [splitSum_cons_of_gt rest h]
        simp only [List.length_cons, List.length_nil]
        omega

/-! ## 2.  All the cuts -/

/-- Cut `l` into blocks of prescribed totals `ws`, in order; the last block
takes whatever is left, so `blocks l [w] = [l]` definitionally. -/
def blocks : List ℕ → List ℕ → List (List ℕ)
  | _, [] => []
  | l, [_] => [l]
  | l, w :: (w' :: ws) => (splitSum l w).1 :: blocks (splitSum l w).2 (w' :: ws)

@[simp] theorem blocks_nil (l : List ℕ) : blocks l [] = [] := rfl

/-- **The degenerate cut is the identity**, and definitionally so: this is what
keeps the empty-forest instance of the refinement equal to the uncut refinement
by `rfl`. -/
@[simp] theorem blocks_singleton (l : List ℕ) (w : ℕ) : blocks l [w] = [l] := rfl

theorem blocks_cons_cons (l : List ℕ) (w w' : ℕ) (ws : List ℕ) :
    blocks l (w :: w' :: ws) =
      (splitSum l w).1 :: blocks (splitSum l w).2 (w' :: ws) := rfl

/-- One block per prescribed total. -/
@[simp] theorem length_blocks (l ws : List ℕ) : (blocks l ws).length = ws.length := by
  induction ws generalizing l with
  | nil => rfl
  | cons w ws ih =>
      cases ws with
      | nil => rfl
      | cons w' ws' =>
          rw [blocks_cons_cons]
          simp only [List.length_cons]
          exact congrArg (· + 1) (ih (splitSum l w).2)

/-- **The blocks have the prescribed totals.**  This is the whole point of the
file. -/
theorem sum_getD_blocks : ∀ (l ws : List ℕ), ws.sum = l.sum →
    ∀ k, k < ws.length → ((blocks l ws).getD k []).sum = ws.getD k 0 := by
  intro l ws
  induction ws generalizing l with
  | nil => intro _ k hk; simp at hk
  | cons w ws ih =>
      cases ws with
      | nil =>
          intro hsum k hk
          simp only [List.length_cons, List.length_nil] at hk
          interval_cases k
          simp only [blocks_singleton, List.getD_cons_zero]
          simpa using hsum.symm
      | cons w' ws' =>
          intro hsum k hk
          have hle : w ≤ l.sum := by
            simp only [List.sum_cons] at hsum
            omega
          have hfst : (splitSum l w).1.sum = w := sum_splitSum_fst hle
          have hsnd : (splitSum l w).2.sum = l.sum - w := sum_splitSum_snd hle
          rw [blocks_cons_cons]
          cases k with
          | zero => simpa using hfst
          | succ m =>
              simp only [List.getD_cons_succ]
              refine ih (splitSum l w).2 ?_ m ?_
              · simp only [List.sum_cons] at hsum ⊢
                omega
              · simp only [List.length_cons] at hk ⊢
                omega

end DraismaVargas.Infrastructure.OrderedBlockSplit
