import Utilities.Combinatorics.Ballot

/-!
# Slope sequences of a caterpillar of loops, and their bijection with ballot sequences

**Source.**  Vargas, *Catalan-many tropical morphisms to trees; Part II: A
space and a count* (arXiv:2609.09109), subsection "Caterpillars of loops": the
reduction of a full-dimensional tropical morphism over a metric caterpillar of
loops to a choice of slopes on the path edges (the paragraph before
`prop-caterpillar-ballot`); the proposition `prop-caterpillar-ballot`, whose
part (1) is the slope condition and whose part (2) says the slope sequence
determines the morphism; its proof, which derives the step condition; the
paragraph after that proof, which passes from a slope sequence to a ballot
sequence; and the lemma `lm:catalan-many`, the Catalan count, citing Stanley,
*Enumerative Combinatorics I*, Theorem 1.5.1.

## The indexing convention, fixed against the source

Part (1) of `prop-caterpillar-ballot` reads, verbatim: *"the slopes `s_i` on
the path edges satisfy `s_1 = s_{g-1} = 2`, `s_i ≥ 1`, and `s_i - s_{i-1} = ±1`
for all `i = 2, …, g-1`"*, and part (2) names the object `(s_i)_{i=1}^{g-1}`.
So the paper's sequence runs over `i = 1, …, g-1`: it has **`g - 1` terms**,
with prescribed value `2` at *both* ends, and the step condition is imposed
for `i = 2, …, g-1`, i.e. **`g - 2` times** -- exactly once for each of the
`g - 2` consecutive pairs of a list of length `g - 1`.  That arithmetic is the
whole off-by-one check, and it is why `step` below is a `List.IsChain` over
the whole list rather than a condition with an explicit index range.

`Slopes g` therefore stores `slopes : List ℕ` with `slopes.length = g - 1`, and
the dictionary is

* `slopes[0]` is the paper's `s_1`, …, `slopes[g-2]` is the paper's `s_{g-1}`;
  in general **the paper's `s_i` is `slopes[i-1]`** (list indices are 0-based,
  the paper's are 1-based);
* the paper's `s_1 = 2` is `head_eq`, and its `s_{g-1} = 2` is `getLast_eq`;
* the paper's `s_i ≥ 1` (all `i`) is `one_le`;
* the paper's `s_i - s_{i-1} = ±1` for `i = 2, …, g-1` is `step`.

Both boundary conditions are stated on `head?`/`getLast?`, so they are vacuous
on the empty list.  This is deliberate and is the second half of the
off-by-one check: at `g = 0` the paper's index range `1 ≤ i ≤ g-1` is empty,
the sequence is empty, and `Slopes 0` must be a one-point type to match
`Ballot 0` and `catalan 0 = 1`.  Stating them as `head? = some 2` instead would
empty `Slopes 0` and break `card_eq_catalan` at `n = 0`.  The price is that
`Slopes 1` is also a one-point type while `Ballot 1` is empty (there is no
ballot sequence of odd length), so `equivBallot` below carries the hypothesis
`g ≠ 1`.  That is not a gap in the source: the proposition
`prop-divisors-on-chain`, where Part II uses the count, assumes `g` even
throughout, and the count below is stated at `g = 2 * n`.

The ballot side is `Ballot g` from `Utilities.Combinatorics.Ballot` (a
length-`g` list of `±1` votes over Mathlib's `DyckStep`, `U ↦ +1`, `D ↦ -1`),
with `b.votes[0]` the paper's `b_1`, …, `b.votes[g-1]` the paper's `b_g`.  The
paper sets `b_1 = 1`, `b_g = -1` and `b_i = s_i - s_{i-1}` for
`i = 2, …, g-1`: one leading `+1`, then the `g - 2` consecutive differences of
the slope list, then one trailing `-1`, for a total of `1 + (g-2) + 1 = g`
votes.  That is literally `votesOfSlopes`: `U :: (interiorVotes slopes ++ [D])`,
with `interiorVotes` the list of `g - 2` consecutive-difference signs.  The
counts agree, which is the same off-by-one check read on the other side.

## What is proved

* `Slopes g` -- the slope sequence of `prop-caterpillar-ballot`(1), with
  `Slopes.six` a concrete inhabitant at `g = 6` (`[2, 3, 4, 3, 2]`).
* `Slopes.equivBallot (hg : g ≠ 1) : Slopes g ≃ Ballot g` -- the paper's
  passage `(s_i) ↦ (b_i)` is a **bijection**.  Both directions are explicit
  (`toBallot`, `ofBallot`) and both round trips are proved.
* `Slopes.one_le_scanl_two_iff` -- the bridge itself, in the form that carries
  the content of the paper's *"all partial sums `∑_{j=1}^i b_j = s_i - 1` are
  non-negative"*: positivity of every slope is **equivalent** to
  non-negativity of every partial vote sum, which is exactly `Ballot`'s
  `prefix_le` field.  `Slopes.getElem_slopes_add_count` states the identity
  itself, `s_i + #{j ≤ i : b_j = -1} = 1 + #{j ≤ i : b_j = +1}`, in a form with
  no truncated subtraction.
* `Slopes.card_eq_catalan (n) : Fintype.card (Slopes (2 * n)) = catalan n` and
  `Slopes.card_six_eq_five : Fintype.card (Slopes 6) = 5` -- the count of
  `lm:catalan-many` transported to the slope side, which is the form used by
  `prop-divisors-on-chain` and by the proof of the main theorem of Part II.

Together with `Utilities.Combinatorics.Ballot` these give the **combinatorial
half** of the classification of tropical morphisms over a caterpillar of
loops: slope sequences are ballot sequences, and there are Catalan many of
them.

## What is NOT proved

Everything geometric.  In particular:

* **No tropical morphism appears here.**  That the slopes of a
  full-dimensional tropical morphism over a metric caterpillar of loops satisfy
  the conditions of `Slopes` is `prop-caterpillar-ballot`(1), and is not
  proved (nor stated) in this module; that every slope sequence arises from
  one, uniquely, is `prop-caterpillar-ballot`(2), and likewise is not.
* Consequently **no statement about the fibre** of Part II's projection, of
  any kind: this module does not mention fibres, cores, or any gluing datum,
  and it imports only `Utilities.Combinatorics.Ballot` and Mathlib, so that it
  can be used anywhere.
* `equivBallot`, `instFintypeTwoMul` and `card_eq_catalan` are the only places
  a hypothesis remains, and it is only `g ≠ 1` (respectively `g = 2 * n`, which
  gives `g ≠ 1`).  No other declaration below carries a hypothesis beyond the
  fields of `Slopes`/`Ballot` themselves.
* Nothing here asserts that the genus `g` arising in an application is even;
  as in `Utilities.Combinatorics.Ballot`, evenness is supplied at the use
  site, exactly as `prop-divisors-on-chain` supplies it as a standing
  hypothesis.

## Consumers

The Draisma--Vargas count, which builds the gluing datum of a tropical morphism
over a caterpillar of loops from a *slope* sequence rather than from a vote
sequence (so `Slopes (2 * (m + 1))` is its index type), and composes
`equivBallot` with `Ballot.card_eq_catalan` to count them.
-/

namespace DraismaVargas.Count

/-- The step relation of `prop-caterpillar-ballot`(1): `s_i - s_{i-1} = ±1`,
written without truncated subtraction.  `SlopeStepRel a b` says the slope moves
from `a` to `b` by exactly one unit, up or down. -/
abbrev SlopeStepRel (a b : ℕ) : Prop := b = a + 1 ∨ a = b + 1

/-- A **slope sequence** of a metric caterpillar of loops of genus `g`
(Vargas, Part II, `prop-caterpillar-ballot`(1)): the slopes `(s_i)_{i=1}^{g-1}`
on the `g - 1` path edges of the spine, subject to `s_1 = s_{g-1} = 2`,
`s_i ≥ 1`, and `s_i - s_{i-1} = ±1` for `i = 2, …, g-1`.

The paper's `s_i` is `slopes[i-1]`; see the module docstring for the full
indexing dictionary and for why the two boundary conditions are stated on
`head?` and `getLast?`.  `Slopes.six` is a concrete inhabitant at `g = 6`. -/
structure Slopes (g : ℕ) where
  /-- The `g - 1` slopes, `slopes[i-1]` being the paper's `s_i`. -/
  slopes : List ℕ
  /-- There are `g - 1` slopes -- the paper's index range `i = 1, …, g-1`. -/
  length_eq : slopes.length = g - 1
  /-- The paper's `s_1 = 2`. -/
  head_eq : ∀ s ∈ slopes.head?, s = 2
  /-- The paper's `s_{g-1} = 2`. -/
  getLast_eq : ∀ s ∈ slopes.getLast?, s = 2
  /-- The paper's `s_i ≥ 1`. -/
  one_le : ∀ s ∈ slopes, 1 ≤ s
  /-- The paper's `s_i - s_{i-1} = ±1` for `i = 2, …, g-1`: one condition for
  each of the `g - 2` consecutive pairs of the list. -/
  step : List.IsChain SlopeStepRel slopes

namespace Slopes

/-! ## 1.  The two raw list maps of the passage to ballot sequences -/

/-- The action of one vote on the running slope: a `+1` vote raises it,
a `-1` vote lowers it.  Truncated subtraction is harmless here -- every slope
sequence in sight is positive, and every lemma below that could see a step down
from `0` carries the positivity hypothesis that rules it out. -/
def slopeStep : ℕ → DyckStep → ℕ
  | s, .U => s + 1
  | s, .D => s - 1

/-- The vote that the paper reads off a consecutive pair of slopes:
`b_i = s_i - s_{i-1}` is `+1` when the slope rises and `-1` otherwise. -/
def slopeVote (a b : ℕ) : DyckStep := if a < b then .U else .D

/-- The interior votes `(b_i)_{i=2}^{g-1}` of the passage to ballot sequences,
read off the slope list as its consecutive-difference signs.  A list of `g - 1`
slopes has `g - 2` consecutive pairs, which is exactly the number of interior
votes. -/
def interiorVotes : List ℕ → List DyckStep
  | [] => []
  | [_] => []
  | a :: b :: t => slopeVote a b :: interiorVotes (b :: t)

@[simp] theorem interiorVotes_nil : interiorVotes [] = [] := rfl

@[simp] theorem interiorVotes_singleton (a : ℕ) : interiorVotes [a] = [] := rfl

@[simp] theorem interiorVotes_cons_cons (a b : ℕ) (t : List ℕ) :
    interiorVotes (a :: b :: t) = slopeVote a b :: interiorVotes (b :: t) := rfl

/-- The paper's map `(s_i)_{i=1}^{g-1} ↦ (b_i)_{i=1}^{g}`: a leading `b_1 = +1`,
then the `g - 2` interior votes, then a trailing `b_g = -1`.  The empty slope
list is sent to the empty vote list, which is the `g = 0` case. -/
def votesOfSlopes : List ℕ → List DyckStep
  | [] => []
  | a :: t => DyckStep.U :: (interiorVotes (a :: t) ++ [DyckStep.D])

@[simp] theorem votesOfSlopes_nil : votesOfSlopes [] = [] := rfl

@[simp] theorem votesOfSlopes_cons (a : ℕ) (t : List ℕ) :
    votesOfSlopes (a :: t) = DyckStep.U :: (interiorVotes (a :: t) ++ [DyckStep.D]) := rfl

/-- The inverse map, `s_i = 1 + ∑_{j=1}^{i} b_j`: drop the leading and trailing
votes and accumulate, starting from `s_1 = 2`.  (`List.scanl` emits the initial
value, so `g - 2` interior votes produce `g - 1` slopes.) -/
def slopesOfVotes : List DyckStep → List ℕ
  | [] => []
  | _ :: v => List.scanl slopeStep 2 v.dropLast

@[simp] theorem slopesOfVotes_nil : slopesOfVotes [] = [] := rfl

@[simp] theorem slopesOfVotes_cons (x : DyckStep) (v : List DyckStep) :
    slopesOfVotes (x :: v) = List.scanl slopeStep 2 v.dropLast := rfl

/-! ## 2.  Accumulation and difference are inverse, and what the conditions say -/

/-- The initial value of a `scanl` is one of its entries. -/
theorem mem_scanl_self (a : ℕ) (m : List DyckStep) : a ∈ List.scanl slopeStep a m := by
  cases m <;> simp

/-- A `scanl` always begins with its initial value. -/
theorem scanl_eq_cons (a : ℕ) (m : List DyckStep) :
    ∃ t, List.scanl slopeStep a m = a :: t := by
  cases m with
  | nil => exact ⟨[], rfl⟩
  | cons x m => exact ⟨_, List.scanl_cons⟩

/-- **Round trip, votes first**: accumulating a vote list and then reading off
the consecutive-difference signs returns the vote list.  No positivity is
needed: in `ℕ`, `a < a - 1` is false, so a step down is always read back as
a `-1` vote. -/
theorem interiorVotes_scanl : ∀ (a : ℕ) (m : List DyckStep),
    interiorVotes (List.scanl slopeStep a m) = m := by
  intro a m
  induction m generalizing a with
  | nil => simp
  | cons x m ih =>
    obtain ⟨t, ht⟩ := scanl_eq_cons (slopeStep a x) m
    have hvote : slopeVote a (slopeStep a x) = x := by
      cases x
      · have h : a < slopeStep a DyckStep.U := by show a < a + 1; omega
        simp [slopeVote, h]
      · have h : ¬ a < slopeStep a DyckStep.D := by show ¬ a < a - 1; omega
        simp [slopeVote, h]
    rw [List.scanl_cons, ht, interiorVotes_cons_cons, ← ht, ih, hvote]

/-- **Round trip, slopes first**: reading off the consecutive-difference signs
of a `±1`-step chain and then accumulating them from its first entry returns the
chain.  The chain hypothesis is what makes the truncated subtraction exact. -/
theorem scanl_interiorVotes : ∀ (a : ℕ) (t : List ℕ),
    List.IsChain SlopeStepRel (a :: t) →
    List.scanl slopeStep a (interiorVotes (a :: t)) = a :: t := by
  intro a t
  induction t generalizing a with
  | nil => intro _; simp
  | cons b t ih =>
    intro hchain
    rw [List.isChain_cons_cons] at hchain
    obtain ⟨hr, hc⟩ := hchain
    have hstep : slopeStep a (slopeVote a b) = b := by
      rcases hr with h | h
      · subst h; simp [slopeVote, slopeStep]
      · subst h; simp [slopeVote, slopeStep]
    rw [interiorVotes_cons_cons, List.scanl_cons, hstep, ih b hc]

/-- **The bridge of the passage to ballot sequences.**  In the paper's words,
*"all partial sums `∑_{j=1}^i b_j = s_i - 1` are non-negative"*: positivity of
every slope is equivalent to non-negativity of every partial vote sum, which is
verbatim `Ballot`'s `prefix_le` field.  Stated at initial slope `b + 1` and
threshold `b` so that no truncated subtraction occurs; `b = 1` is the case
used. -/
theorem one_le_scanl_iff : ∀ (b : ℕ) (m : List DyckStep),
    (∀ x ∈ List.scanl slopeStep (b + 1) m, 1 ≤ x) ↔
      ∀ i, (m.take i).count DyckStep.D ≤ b + (m.take i).count DyckStep.U := by
  intro b m
  induction m generalizing b with
  | nil => simp
  | cons x m ih =>
    cases x with
    | U =>
      have hs : slopeStep (b + 1) DyckStep.U = (b + 1) + 1 := rfl
      simp only [List.scanl_cons, hs, List.forall_mem_cons, ih (b + 1)]
      constructor
      · rintro ⟨-, h⟩ i
        cases i with
        | zero => simp
        | succ j =>
          have := h j
          simp only [List.take_succ_cons, List.count_cons] at this ⊢
          simp at this ⊢
          omega
      · intro h
        refine ⟨by omega, fun i => ?_⟩
        have := h (i + 1)
        simp only [List.take_succ_cons, List.count_cons] at this ⊢
        simp at this ⊢
        omega
    | D =>
      have hs : slopeStep (b + 1) DyckStep.D = b := rfl
      simp only [List.scanl_cons, hs, List.forall_mem_cons]
      constructor
      · rintro ⟨-, h⟩ i
        have hb : 1 ≤ b := h b (mem_scanl_self b m)
        obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
        have h' := (ih c).1 h
        cases i with
        | zero => simp
        | succ j =>
          have := h' j
          simp only [List.take_succ_cons, List.count_cons] at this ⊢
          simp at this ⊢
          omega
      · intro h
        have hb : 1 ≤ b := by
          have := h 1
          simp at this
          omega
        obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
        refine ⟨by omega, (ih c).2 fun i => ?_⟩
        have := h (i + 1)
        simp only [List.take_succ_cons, List.count_cons] at this ⊢
        simp at this ⊢
        omega

/-- The case of `one_le_scanl_iff` used throughout: initial slope `s_1 = 2`. -/
theorem one_le_scanl_two_iff (m : List DyckStep) :
    (∀ x ∈ List.scanl slopeStep 2 m, 1 ≤ x) ↔
      ∀ i, (m.take i).count DyckStep.D ≤ 1 + (m.take i).count DyckStep.U :=
  one_le_scanl_iff 1 m

/-- The final slope equals the initial slope plus the total vote, in the form
`final + #(-1 votes) = initial + #(+1 votes)` that avoids truncated
subtraction.  With `initial = final = 2` this is the paper's
*"`∑_{j=1}^g b_j = 0` since `s_1 = s_{g-1} = 2`"*. -/
theorem foldl_slopeStep_add_count : ∀ (a : ℕ) (m : List DyckStep),
    (∀ x ∈ List.scanl slopeStep a m, 1 ≤ x) →
    List.foldl slopeStep a m + m.count DyckStep.D = a + m.count DyckStep.U := by
  intro a m
  induction m generalizing a with
  | nil => simp
  | cons x m ih =>
    intro h
    have htail : ∀ y ∈ List.scanl slopeStep (slopeStep a x) m, 1 ≤ y := by
      intro y hy
      exact h y (by rw [List.scanl_cons]; exact List.mem_cons_of_mem _ hy)
    have hrec := ih (slopeStep a x) htail
    cases x with
    | U =>
      have hs : slopeStep a DyckStep.U = a + 1 := rfl
      rw [hs] at hrec
      simp only [List.foldl_cons, hs, List.count_cons] at hrec ⊢
      simp at hrec ⊢
      omega
    | D =>
      have hs : slopeStep a DyckStep.D = a - 1 := rfl
      have ha : 1 ≤ a - 1 := by
        have := htail (slopeStep a DyckStep.D) (mem_scanl_self _ m)
        omega
      rw [hs] at hrec
      simp only [List.foldl_cons, hs, List.count_cons] at hrec ⊢
      simp at hrec ⊢
      omega

/-- Accumulating votes produces a `±1`-step chain, provided no slope drops to
zero (which is where truncated subtraction would break the step). -/
theorem isChain_scanl : ∀ (a : ℕ) (m : List DyckStep),
    (∀ x ∈ List.scanl slopeStep a m, 1 ≤ x) →
    List.IsChain SlopeStepRel (List.scanl slopeStep a m) := by
  intro a m
  induction m generalizing a with
  | nil => intro _; simp
  | cons x m ih =>
    intro h
    obtain ⟨t, ht⟩ := scanl_eq_cons (slopeStep a x) m
    have htail : ∀ y ∈ List.scanl slopeStep (slopeStep a x) m, 1 ≤ y := by
      intro y hy
      exact h y (by rw [List.scanl_cons]; exact List.mem_cons_of_mem _ hy)
    rw [List.scanl_cons, ht, List.isChain_cons_cons]
    refine ⟨?_, ?_⟩
    · cases x with
      | U => exact Or.inl rfl
      | D =>
        have ha : 1 ≤ a := h a (mem_scanl_self a (DyckStep.D :: m))
        show a - 1 = a + 1 ∨ a = a - 1 + 1
        omega
    · rw [← ht]; exact ih (slopeStep a x) htail

/-! ## 3.  From a slope sequence to a ballot sequence -/

variable {g : ℕ}

/-- For a nonempty slope sequence, accumulating its interior votes from `2`
returns the sequence itself.  This is where `head_eq` (the paper's `s_1 = 2`)
and `step` (the paper's `s_i - s_{i-1} = ±1`) are consumed. -/
theorem scanl_interior (s : Slopes g) (h : s.slopes ≠ []) :
    List.scanl slopeStep 2 (interiorVotes s.slopes) = s.slopes := by
  obtain ⟨a, t, ht⟩ := List.exists_cons_of_ne_nil h
  have ha : a = 2 := s.head_eq a (by rw [ht]; simp)
  subst ha
  rw [ht]
  exact scanl_interiorVotes 2 t (by rw [← ht]; exact s.step)

/-- `one_le` transported along `scanl_interior`. -/
theorem one_le_interior_scanl (s : Slopes g) (h : s.slopes ≠ []) :
    ∀ x ∈ List.scanl slopeStep 2 (interiorVotes s.slopes), 1 ≤ x := by
  rw [scanl_interior s h]; exact s.one_le

/-- A slope sequence of length `g - 1` has `g - 2` interior votes. -/
theorem length_interior (s : Slopes g) (h : s.slopes ≠ []) :
    (interiorVotes s.slopes).length + 1 = s.slopes.length := by
  have := congrArg List.length (scanl_interior s h)
  rw [List.length_scanl] at this
  omega

/-- `getLast_eq` (the paper's `s_{g-1} = 2`) read as a statement about the
total vote. -/
theorem foldl_interior (s : Slopes g) (h : s.slopes ≠ []) :
    List.foldl slopeStep 2 (interiorVotes s.slopes) = 2 := by
  have hlast : s.slopes.getLast?
      = some (List.foldl slopeStep 2 (interiorVotes s.slopes)) := by
    conv_lhs => rw [← scanl_interior s h]
    exact List.getLast?_scanl
  exact s.getLast_eq _ (by rw [hlast]; simp)

/-- The paper's *"`∑_{j=1}^g b_j = 0`"*: the interior votes are tied, so the
whole vote list is too once the leading `+1` and trailing `-1` are added. -/
theorem count_interior (s : Slopes g) (h : s.slopes ≠ []) :
    (interiorVotes s.slopes).count DyckStep.D
      = (interiorVotes s.slopes).count DyckStep.U := by
  have := foldl_slopeStep_add_count 2 (interiorVotes s.slopes) (one_le_interior_scanl s h)
  rw [foldl_interior s h] at this
  omega

/-- The paper's *"all partial sums are non-negative"*, on the interior votes. -/
theorem take_count_interior (s : Slopes g) (h : s.slopes ≠ []) (i : ℕ) :
    ((interiorVotes s.slopes).take i).count DyckStep.D
      ≤ 1 + ((interiorVotes s.slopes).take i).count DyckStep.U :=
  (one_le_scanl_two_iff _).1 (one_le_interior_scanl s h) i

/-- The vote list of a nonempty slope sequence, unfolded. -/
theorem votesOfSlopes_eq (s : Slopes g) (h : s.slopes ≠ []) :
    votesOfSlopes s.slopes
      = DyckStep.U :: (interiorVotes s.slopes ++ [DyckStep.D]) := by
  obtain ⟨a, t, ht⟩ := List.exists_cons_of_ne_nil h
  rw [ht]
  exact votesOfSlopes_cons a t

/-- `1 + (g - 2) + 1 = g`: the vote list has length `g`.  The hypothesis
`g ≠ 1` is what excludes the degenerate index range; see the module docstring. -/
theorem length_votesOfSlopes (s : Slopes g) (hg : g ≠ 1) :
    (votesOfSlopes s.slopes).length = g := by
  by_cases hne : s.slopes = []
  · have hl := s.length_eq
    rw [hne] at hl
    simp only [List.length_nil] at hl
    rw [hne]
    simp only [votesOfSlopes_nil, List.length_nil]
    omega
  · have hlen := length_interior s hne
    have hl := s.length_eq
    have hpos : 0 < s.slopes.length := List.length_pos_of_ne_nil hne
    rw [votesOfSlopes_eq s hne]
    simp only [List.length_cons, List.length_append, List.length_nil]
    omega

/-- The vote list is tied -- `Ballot`'s `count_eq`. -/
theorem count_votesOfSlopes (s : Slopes g) :
    (votesOfSlopes s.slopes).count DyckStep.U
      = (votesOfSlopes s.slopes).count DyckStep.D := by
  by_cases hne : s.slopes = []
  · rw [hne]; simp
  · have hc := count_interior s hne
    rw [votesOfSlopes_eq s hne]
    simp only [List.count_cons, List.count_append, List.count_nil]
    simp
    omega

/-- Every prefix of the vote list has at least as many `+1`s as `-1`s --
`Ballot`'s `prefix_le`. -/
theorem prefix_le_votesOfSlopes (s : Slopes g) (i : ℕ) :
    ((votesOfSlopes s.slopes).take i).count DyckStep.D
      ≤ ((votesOfSlopes s.slopes).take i).count DyckStep.U := by
  by_cases hne : s.slopes = []
  · rw [hne]; simp
  · rw [votesOfSlopes_eq s hne]
    cases i with
    | zero => simp
    | succ j =>
      rw [List.take_succ_cons]
      simp only [List.count_cons]
      simp only [beq_iff_eq, reduceCtorEq, if_false, if_true, Nat.add_zero]
      by_cases hj : j ≤ (interiorVotes s.slopes).length
      · rw [List.take_append_of_le_length hj]
        have := take_count_interior s hne j
        omega
      · rw [List.take_of_length_le (by simp; omega)]
        have := count_interior s hne
        simp only [List.count_append, List.count_cons, List.count_nil]
        simp
        omega

/-- The ballot sequence of a slope sequence. -/
def toBallot (hg : g ≠ 1) (s : Slopes g) : Ballot g where
  votes := votesOfSlopes s.slopes
  length_eq := length_votesOfSlopes s hg
  count_eq := count_votesOfSlopes s
  prefix_le := prefix_le_votesOfSlopes s

/-! ## 4.  From a ballot sequence to a slope sequence -/

/-- The paper's `b_1 = 1` is not an extra condition on a ballot sequence but a
consequence: the first prefix must already be non-negative. -/
theorem head_votes_eq_U (b : Ballot g) {x : DyckStep} {v : List DyckStep}
    (hv : b.votes = x :: v) : x = DyckStep.U := by
  have h := b.prefix_le 1
  rw [hv] at h
  cases x with
  | U => rfl
  | D => simp at h

/-- The paper's `b_g = -1` is likewise a consequence: a last vote of `+1` would
make the total positive while the second-to-last prefix is non-negative. -/
theorem votes_concat (b : Ballot g) (h : b.votes ≠ []) :
    b.votes.dropLast ++ [DyckStep.D] = b.votes := by
  have hsplit := List.dropLast_append_getLast h
  have hw : b.votes.getLast h = DyckStep.D := by
    cases hx : b.votes.getLast h with
    | D => rfl
    | U =>
      exfalso
      rw [hx] at hsplit
      have hpre := b.prefix_le (b.votes.length - 1)
      rw [← List.dropLast_eq_take] at hpre
      have hU : b.votes.count DyckStep.U = b.votes.dropLast.count DyckStep.U + 1 := by
        conv_lhs => rw [← hsplit]
        simp
      have hD : b.votes.count DyckStep.D = b.votes.dropLast.count DyckStep.D := by
        conv_lhs => rw [← hsplit]
        simp
      have hc := b.count_eq
      omega
  rw [← hw]; exact hsplit

/-- The decomposition of a ballot sequence matching the paper's passage to
ballot sequences: a leading `+1`, an interior block, and a trailing `-1`. -/
theorem votes_eq (b : Ballot g) (hg : g ≠ 1) (h : b.votes ≠ []) :
    b.votes = DyckStep.U :: (b.votes.tail.dropLast ++ [DyckStep.D]) := by
  have hcat := votes_concat b h
  have hdne : b.votes.dropLast ≠ [] := by
    intro h0
    have hl := congrArg List.length hcat
    rw [h0, b.length_eq] at hl
    simp at hl
    omega
  obtain ⟨x, w, hw⟩ := List.exists_cons_of_ne_nil hdne
  rw [hw] at hcat
  have hv : b.votes = x :: (w ++ [DyckStep.D]) := by rw [← hcat]; rfl
  have hx : x = DyckStep.U := head_votes_eq_U b hv
  rw [hv, List.tail_cons, List.dropLast_concat, hx]

/-- The slope list of a nonempty ballot sequence, unfolded. -/
theorem slopesOfVotes_eq (b : Ballot g) (h : b.votes ≠ []) :
    slopesOfVotes b.votes = List.scanl slopeStep 2 b.votes.tail.dropLast := by
  obtain ⟨x, v, hv⟩ := List.exists_cons_of_ne_nil h
  rw [hv, List.tail_cons]
  exact slopesOfVotes_cons x v

/-- The interior of a ballot sequence is tied. -/
theorem count_ballot_interior (b : Ballot g) (hg : g ≠ 1) (h : b.votes ≠ []) :
    b.votes.tail.dropLast.count DyckStep.D = b.votes.tail.dropLast.count DyckStep.U := by
  have hc := b.count_eq
  rw [votes_eq b hg h] at hc
  simp at hc
  omega

/-- Every prefix of the interior of a ballot sequence satisfies the threshold
that `one_le_scanl_two_iff` turns into positivity of the slopes. -/
theorem take_count_ballot_interior (b : Ballot g) (hg : g ≠ 1) (h : b.votes ≠ []) (i : ℕ) :
    (b.votes.tail.dropLast.take i).count DyckStep.D
      ≤ 1 + (b.votes.tail.dropLast.take i).count DyckStep.U := by
  have key : ∀ j, j ≤ b.votes.tail.dropLast.length →
      (b.votes.tail.dropLast.take j).count DyckStep.D
        ≤ 1 + (b.votes.tail.dropLast.take j).count DyckStep.U := by
    intro j hj
    have hp := b.prefix_le (j + 1)
    rw [votes_eq b hg h] at hp
    rw [List.take_succ_cons, List.take_append_of_le_length hj] at hp
    simp only [List.count_cons] at hp
    simp at hp
    omega
  by_cases hi : i ≤ b.votes.tail.dropLast.length
  · exact key i hi
  · rw [List.take_of_length_le (by omega)]
    have := key _ le_rfl
    rwa [List.take_of_length_le le_rfl] at this

/-- The slope list of a length-`g` ballot sequence has length `g - 1`. -/
theorem length_slopesOfVotes (b : Ballot g) (hg : g ≠ 1) :
    (slopesOfVotes b.votes).length = g - 1 := by
  by_cases h : b.votes = []
  · have hl := b.length_eq
    rw [h] at hl
    simp only [List.length_nil] at hl
    rw [h]
    simp only [slopesOfVotes_nil, List.length_nil]
    omega
  · rw [slopesOfVotes_eq b h, List.length_scanl]
    have hl := b.length_eq
    rw [votes_eq b hg h] at hl
    simp only [List.length_cons, List.length_append, List.length_nil] at hl
    omega

/-- The paper's `s_1 = 2`. -/
theorem head_slopesOfVotes (b : Ballot g) : ∀ x ∈ (slopesOfVotes b.votes).head?, x = 2 := by
  by_cases h : b.votes = []
  · rw [h]; simp
  · rw [slopesOfVotes_eq b h]
    intro x hx
    rw [List.head?_scanl] at hx
    simp only [Option.mem_def, Option.some.injEq] at hx
    omega

/-- The paper's `s_i ≥ 1`. -/
theorem one_le_slopesOfVotes (b : Ballot g) (hg : g ≠ 1) :
    ∀ x ∈ slopesOfVotes b.votes, 1 ≤ x := by
  by_cases h : b.votes = []
  · rw [h]; simp
  · rw [slopesOfVotes_eq b h]
    exact (one_le_scanl_two_iff _).2 (take_count_ballot_interior b hg h)

/-- The paper's `s_{g-1} = 2`. -/
theorem getLast_slopesOfVotes (b : Ballot g) (hg : g ≠ 1) :
    ∀ x ∈ (slopesOfVotes b.votes).getLast?, x = 2 := by
  by_cases h : b.votes = []
  · rw [h]; simp
  · rw [slopesOfVotes_eq b h]
    intro x hx
    rw [List.getLast?_scanl] at hx
    have hpos := (one_le_scanl_two_iff _).2 (take_count_ballot_interior b hg h)
    have hfold := foldl_slopeStep_add_count 2 _ hpos
    have hc := count_ballot_interior b hg h
    simp only [Option.mem_def, Option.some.injEq] at hx
    omega

/-- The paper's `s_i - s_{i-1} = ±1`. -/
theorem isChain_slopesOfVotes (b : Ballot g) (hg : g ≠ 1) :
    List.IsChain SlopeStepRel (slopesOfVotes b.votes) := by
  by_cases h : b.votes = []
  · rw [h]; simp
  · rw [slopesOfVotes_eq b h]
    exact isChain_scanl 2 _ ((one_le_scanl_two_iff _).2 (take_count_ballot_interior b hg h))

/-- The slope sequence of a ballot sequence. -/
def ofBallot (hg : g ≠ 1) (b : Ballot g) : Slopes g where
  slopes := slopesOfVotes b.votes
  length_eq := length_slopesOfVotes b hg
  head_eq := head_slopesOfVotes b
  getLast_eq := getLast_slopesOfVotes b hg
  one_le := one_le_slopesOfVotes b hg
  step := isChain_slopesOfVotes b hg

/-! ## 5.  The bijection, the count, and a witness -/

/-- Round trip on the slope side. -/
theorem slopesOfVotes_votesOfSlopes (s : Slopes g) :
    slopesOfVotes (votesOfSlopes s.slopes) = s.slopes := by
  by_cases hne : s.slopes = []
  · rw [hne]; simp
  · rw [votesOfSlopes_eq s hne, slopesOfVotes_cons, List.dropLast_concat]
    exact scanl_interior s hne

/-- Round trip on the ballot side. -/
theorem votesOfSlopes_slopesOfVotes (b : Ballot g) (hg : g ≠ 1) :
    votesOfSlopes (slopesOfVotes b.votes) = b.votes := by
  by_cases h : b.votes = []
  · rw [h]; simp
  · rw [slopesOfVotes_eq b h]
    obtain ⟨u, hu⟩ := scanl_eq_cons 2 b.votes.tail.dropLast
    rw [hu, votesOfSlopes_cons, ← hu, interiorVotes_scanl]
    exact (votes_eq b hg h).symm

/-- A slope sequence is determined by its list of slopes. -/
theorem eq_of_slopes_eq {s₁ s₂ : Slopes g} (h : s₁.slopes = s₂.slopes) : s₁ = s₂ := by
  obtain ⟨l₁, p₁, p₂, p₃, p₄, p₅⟩ := s₁
  obtain ⟨l₂, q₁, q₂, q₃, q₄, q₅⟩ := s₂
  have h' : l₁ = l₂ := h
  subst h'
  rfl

/-- A ballot sequence is determined by its list of votes. -/
theorem ballot_eq_of_votes_eq {b₁ b₂ : Ballot g} (h : b₁.votes = b₂.votes) : b₁ = b₂ := by
  obtain ⟨v₁, p₁, p₂, p₃⟩ := b₁
  obtain ⟨v₂, q₁, q₂, q₃⟩ := b₂
  have h' : v₁ = v₂ := h
  subst h'
  rfl

/-- **The bijection of the passage to ballot sequences**: slope sequences of
length `g - 1` correspond to ballot sequences of length `g`. -/
def equivBallot (hg : g ≠ 1) : Slopes g ≃ Ballot g where
  toFun := toBallot hg
  invFun := ofBallot hg
  left_inv s := eq_of_slopes_eq (slopesOfVotes_votesOfSlopes s)
  right_inv b := ballot_eq_of_votes_eq (votesOfSlopes_slopesOfVotes b hg)

/-- An entry of a `scanl` is the fold of the corresponding prefix. -/
private theorem getElem_of_scanl (m : List DyckStep) (L : List ℕ)
    (hscan : List.scanl slopeStep 2 m = L) (i : ℕ) (hi : i < L.length) :
    L[i] = List.foldl slopeStep 2 (m.take i) := by
  have hilen : i ≤ m.length := by
    have := congrArg List.length hscan
    rw [List.length_scanl] at this
    omega
  have hopt : L[i]? = some (List.foldl slopeStep 2 (m.take i)) := by
    rw [← hscan, List.getElem?_scanl, if_pos hilen]
  rw [List.getElem?_eq_getElem hi] at hopt
  exact Option.some.inj hopt

/-- The paper's `s_i = 1 + ∑_{j=1}^{i} b_j`, read as a fold: the list entry
`slopes[i]` (the paper's `s_{i+1}`) is the accumulation of the first `i`
interior votes from `2`. -/
theorem getElem_slopes (s : Slopes g) (i : ℕ) (hi : i < s.slopes.length) :
    s.slopes[i] = List.foldl slopeStep 2 ((interiorVotes s.slopes).take i) := by
  have hne : s.slopes ≠ [] := by intro h0; rw [h0] at hi; simp at hi
  exact getElem_of_scanl _ _ (scanl_interior s hne) i hi

/-- **The paper's partial-sum identity**, in a form with no truncated
subtraction. -/
theorem getElem_slopes_add_count (hg : g ≠ 1) (s : Slopes g) (i : ℕ)
    (hi : i < s.slopes.length) :
    s.slopes[i] + ((toBallot hg s).votes.take (i + 1)).count DyckStep.D
      = 1 + ((toBallot hg s).votes.take (i + 1)).count DyckStep.U := by
  have hne : s.slopes ≠ [] := by intro h0; rw [h0] at hi; simp at hi
  have hlen := length_interior s hne
  have hilen : i ≤ (interiorVotes s.slopes).length := by omega
  have hvotes : (toBallot hg s).votes
      = DyckStep.U :: (interiorVotes s.slopes ++ [DyckStep.D]) := votesOfSlopes_eq s hne
  have hpos : ∀ x ∈ List.scanl slopeStep 2 ((interiorVotes s.slopes).take i), 1 ≤ x := by
    refine (one_le_scanl_two_iff _).2 fun j => ?_
    rw [List.take_take]
    exact take_count_interior s hne _
  have hfold := foldl_slopeStep_add_count 2 _ hpos
  rw [hvotes, List.take_succ_cons, List.take_append_of_le_length hilen,
    getElem_slopes s i hi]
  simp only [List.count_cons]
  simp
  omega

/-- At even length the slope sequences form a finite type, through
`equivBallot`. -/
instance instFintypeTwoMul (n : ℕ) : Fintype (Slopes (2 * n)) :=
  Fintype.ofEquiv _ (equivBallot (g := 2 * n) (by omega)).symm

/-- **The count**: there are `catalan n` slope sequences at `g = 2 * n`. -/
theorem card_eq_catalan (n : ℕ) : Fintype.card (Slopes (2 * n)) = catalan n := by
  rw [Fintype.card_congr (equivBallot (g := 2 * n) (by omega)), Ballot.card_eq_catalan]

/-- The genus-six instance of `instFintypeTwoMul`. -/
instance : Fintype (Slopes 6) := instFintypeTwoMul 3

/-- **The genus-six instance of the count**. -/
theorem card_six_eq_five : Fintype.card (Slopes 6) = 5 := by
  show Fintype.card (Slopes (2 * 3)) = 5
  rw [card_eq_catalan, catalan_three]

/-- A concrete slope sequence at `g = 6`. -/
def six : Slopes 6 where
  slopes := [2, 3, 4, 3, 2]
  length_eq := rfl
  head_eq := by
    intro x hx
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx
    omega
  getLast_eq := by
    intro x hx
    simp at hx
    omega
  one_le := by decide
  step := by decide

/-- The witness's ballot sequence is `Ballot.six`, i.e. `+1 +1 +1 -1 -1 -1`:
the slopes `2, 3, 4, 3, 2` rise then fall. -/
theorem votes_toBallot_six (h : (6 : ℕ) ≠ 1) :
    (toBallot h six).votes = Ballot.six.votes := rfl

end Slopes

end DraismaVargas.Count
