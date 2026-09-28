import Mathlib.Combinatorics.Enumerative.DyckWord

/-!
# Ballot sequences and the Catalan count

**Source.**  Vargas, *Catalan-many tropical morphisms to trees; Part II: A
space and a count* (arXiv:2609.09109), subsection "Caterpillars of loops": the
proposition `prop-caterpillar-ballot`, the paragraph after its proof that
passes from slope sequences to ballot sequences, and the lemma
`lm:catalan-many`, which cites Stanley, *Enumerative Combinatorics I*,
Theorem 1.5.1.

**Indexing, fixed against the source.**  Part (1) of `prop-caterpillar-ballot`
gives the slopes on the path edges of a caterpillar of loops as a sequence
`(s_i)_{i=1}^{g-1}` with `s_1 = s_{g-1} = 2`, `s_i ≥ 1`, and
`s_i - s_{i-1} = ±1` for `2 ≤ i ≤ g-1`.  The paragraph after the proof then
defines, from *any* such slope sequence, a length-`g` sequence `(b_i)_{i=1}^g`
by `b_1 = 1`, `b_g = -1`, and `b_i = s_i - s_{i-1}` for `2 ≤ i ≤ g-1`, and
observes: every `b_i ∈ {1,-1}`; every partial sum `∑_{j=1}^i b_j = s_i - 1` is
non-negative (`1 ≤ i ≤ g-1`; the case `i = g` is the total, see below); and
`∑_{j=1}^g b_j = 0` because `s_1 = s_{g-1} = 2`.  The closing sentence of that
paragraph names this `(b_i)_{i=1}^g` object, and *only* this object, "ballot
sequences of length `g`" — the slope sequence `(s_i)` is a different, richer
piece of data (it remembers *where* the votes came from; `(b_i)` only
remembers the votes) that the paper does not itself call a "ballot sequence."
The lemma `lm:catalan-many` counts the `(b_i)` object: the number of
length-`g` ballot sequences is the Catalan number `C_{g/2}`.

**What this module formalizes** is exactly `(b_i)_{i=1}^g`: a length-`g`
sequence of `±1` votes, every prefix sum non-negative, total sum zero — the
standard ballot-sequence / Dyck-path object (the introduction of Part II calls
the same bijection class "length-`g` Dyck paths (or ballot sequences)"),
independent of any slope sequence, tropical morphism, or gluing datum.
**Not** formalized here: the map `(s_i) ↦ (b_i)` itself, or that it is a
bijection onto ballot sequences (that is `Utilities.Combinatorics.Slopes`, which
imports this module), nor the classification of tropical morphisms over a
caterpillar of loops by their slope sequences (`prop-caterpillar-ballot`
itself).

**Even length.**  A ballot sequence's length is always even (`length_even`
below: it equals `count U + count D` with the two counts equal, since `U`/`D`
are the only two `DyckStep`s).  The proposition `prop-divisors-on-chain` of
Part II separately *assumes* "let `g` be even" whenever it uses the Catalan
count — it is not claimed there either that every `g` gives a non-trivial
count.  Consistently, the headline theorem below is stated for `g = 2 * n`,
and `card_eq_catalan` gives `catalan n` unconditionally; nothing about the
parity of the genus of a source graph is asserted here — that is a fact about
the graph, not about this combinatorial count.

## Implementation

A ballot sequence is represented over Mathlib's `DyckStep` alphabet (`U`/`D`)
rather than literal integers `1`/`-1`: `U ↦ +1`, `D ↦ -1` (`voteValue`), which
is proved faithful to the paper's `∑ b_i = 0` / `∀ i, 0 ≤ ∑_{j≤i} b_j`
description by `sum_votes_eq_zero` / `sum_take_votes_nonneg` below, rather
than assumed.  Using `DyckStep` makes `Ballot g`'s two defining conditions
literally Mathlib's `DyckWord` conditions, so the bijection between ballot
sequences and Dyck words of semilength `g/2` is immediate: `Ballot g` and
`{p : DyckWord // p.toList.length = g}` share the same underlying data.

## Main declarations

* `Ballot g` — a ballot sequence of length `g`, with `Ballot.six` a concrete
  witness (the genus-six case, where `catalan 3 = 5`).
* `Ballot.equivDyckWordLength`, `Ballot.equivDyckWordSemilength` — the
  bijections with `DyckWord`.
* `Ballot.card_eq_catalan : Fintype.card (Ballot (2 * n)) = catalan n` — the
  headline count.
* `Ballot.card_six_eq_five : Fintype.card (Ballot 6) = 5` — the count
  `catalan 3 = 5`, specialized to genus six.

## What is NOT proved

* No connection to slope sequences, tropical morphisms, fibres, or any
  gluing datum: this module depends on Mathlib alone.  A bijection between the
  fibre of Part II's projection over a caterpillar of loops and ballot
  sequences, composed with `card_eq_catalan` here, gives the count `C_{g/2}`
  of `prop-divisors-on-chain`; that composition is not performed here.
* No `Fintype (Ballot g)` instance for general (possibly odd) `g`: only
  `Ballot (2 * n)` is given one, which is all `card_eq_catalan` needs. For odd
  `g`, `Ballot g` is uninhabited (`length_even`), so `Fintype.card` would be
  `0`, not `catalan (g / 2)` — consistent with `card_eq_catalan` only ever
  being stated at even lengths.
* No claim that every genus `g` arising in an application is even; that is
  supplied at the use site, exactly as Part II supplies it as a standing
  hypothesis of `prop-divisors-on-chain`, not as a consequence of the ballot
  count.
-/

namespace DraismaVargas.Count

/-- A **ballot sequence** of length `g` (Vargas, Part II, the paragraph after
the proof of `prop-caterpillar-ballot`; counted by `lm:catalan-many`, citing
Stanley, *Enumerative Combinatorics I*, Thm 1.5.1): a list of `g`
`±1` votes (`DyckStep.U` for `+1`, `DyckStep.D` for `-1`) with every prefix at
least as many `+1`s as `-1`s and the whole list tied. The two `Prop` fields
are, verbatim, `DyckWord`'s two conditions; only the fixed length `g` is
extra. -/
structure Ballot (g : ℕ) where
  /-- The list of `g` votes. -/
  votes : List DyckStep
  /-- There are exactly `g` votes. -/
  length_eq : votes.length = g
  /-- The vote is tied: as many `U`s (`+1`) as `D`s (`-1`). -/
  count_eq : votes.count DyckStep.U = votes.count DyckStep.D
  /-- Every prefix has at least as many `U`s (`+1`) as `D`s (`-1`). -/
  prefix_le : ∀ i, (votes.take i).count DyckStep.D ≤ (votes.take i).count DyckStep.U

namespace Ballot

variable {g n : ℕ}

/-! ## The `±1` reading of a vote, and faithfulness to the source -/

/-- The integer value of a vote: `U ↦ 1`, `D ↦ -1`, matching the source's
`b_i ∈ {1, -1}`. -/
def voteValue : DyckStep → ℤ
  | .U => 1
  | .D => -1

private lemma sum_map_voteValue_eq (l : List DyckStep) :
    (l.map voteValue).sum = (l.count DyckStep.U : ℤ) - l.count DyckStep.D := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rcases a with _ | _ <;> simp [voteValue, ih] <;> ring

/-- Faithfulness, part 1: read as `±1`s, a ballot sequence's votes sum to
zero — the source's `∑_{j=1}^g b_j = 0`. -/
theorem sum_votes_eq_zero (b : Ballot g) : (b.votes.map voteValue).sum = 0 := by
  rw [sum_map_voteValue_eq, b.count_eq]; ring

/-- Faithfulness, part 2: read as `±1`s, every prefix of a ballot sequence's
votes has non-negative sum — the source's `∑_{j=1}^i b_j = s_i - 1 ≥ 0`. -/
theorem sum_take_votes_nonneg (b : Ballot g) (i : ℕ) :
    0 ≤ ((b.votes.take i).map voteValue).sum := by
  rw [sum_map_voteValue_eq]
  have h := b.prefix_le i
  omega

/-! ## Length is always even -/

/-- The votes list of a ballot sequence, repackaged as a `DyckWord` (forgetting
only the fixed length `g`, which becomes `DyckWord.toList.length`). -/
def toDyckWord (b : Ballot g) : DyckWord := ⟨b.votes, b.count_eq, b.prefix_le⟩

@[simp] theorem toDyckWord_toList (b : Ballot g) : b.toDyckWord.toList = b.votes := rfl

theorem toDyckWord_length (b : Ballot g) : b.toDyckWord.toList.length = g :=
  b.length_eq

/-- A ballot sequence's length is always even: it is twice its `DyckWord`
semilength. In particular `Ballot g` is uninhabited for odd `g`. -/
theorem length_even (b : Ballot g) : Even g := by
  refine ⟨b.toDyckWord.semilength, ?_⟩
  have h := b.toDyckWord.two_mul_semilength_eq_length
  rw [b.toDyckWord_length] at h
  omega

/-! ## The bijection with `DyckWord` -/

/-- Any `DyckWord` whose underlying list has length `g` is a ballot sequence
of length `g`: the converse repackaging to `toDyckWord`. -/
def ofDyckWord (p : DyckWord) (h : p.toList.length = g) : Ballot g where
  votes := p.toList
  length_eq := h
  count_eq := p.count_U_eq_count_D
  prefix_le := p.count_D_le_count_U

@[simp] theorem ofDyckWord_toDyckWord (p : DyckWord) (h : p.toList.length = g) :
    (ofDyckWord p h).toDyckWord = p := by
  cases p; rfl

@[simp] theorem toDyckWord_ofDyckWord (b : Ballot g) :
    ofDyckWord b.toDyckWord b.toDyckWord_length = b := by
  cases b; rfl

/-- Ballot sequences of length `g` are equivalent to `DyckWord`s whose
underlying list has length `g`. -/
def equivDyckWordLength (g : ℕ) : Ballot g ≃ {p : DyckWord // p.toList.length = g} where
  toFun b := ⟨b.toDyckWord, b.toDyckWord_length⟩
  invFun p := ofDyckWord p.1 p.2
  left_inv b := toDyckWord_ofDyckWord b
  right_inv p := Subtype.ext (ofDyckWord_toDyckWord p.1 p.2)

/-- Ballot sequences of length `2 * n` are equivalent to `DyckWord`s of
semilength `n` — the bijection "ballot sequences ≃ Dyck words of semilength
`g/2`", specialized to `g = 2 * n` (`length_even`). -/
def equivDyckWordSemilength (n : ℕ) :
    Ballot (2 * n) ≃ {p : DyckWord // p.semilength = n} :=
  (equivDyckWordLength (2 * n)).trans <|
    Equiv.subtypeEquivRight fun p => by
      have h := p.two_mul_semilength_eq_length
      omega

instance instFintypeTwoMul (n : ℕ) : Fintype (Ballot (2 * n)) :=
  Fintype.ofEquiv _ (equivDyckWordSemilength n).symm

/-! ## The Catalan count -/

/-- **The Catalan count**: the number of length-`2 * n` ballot sequences is the
`n`th Catalan number (Part II, `lm:catalan-many`, via Mathlib's
`DyckWord.card_dyckWord_semilength_eq_catalan`). -/
theorem card_eq_catalan (n : ℕ) : Fintype.card (Ballot (2 * n)) = catalan n := by
  rw [Fintype.card_congr (equivDyckWordSemilength n), DyckWord.card_dyckWord_semilength_eq_catalan]

/-- A concrete witness: `[U, U, U, D, D, D]` is a ballot sequence of length
six (partial vote counts `1, 2, 3, 2, 1, 0` for `U` minus `D`), so `Ballot 6`
is non-vacuous. -/
def six : Ballot 6 where
  votes := [.U, .U, .U, .D, .D, .D]
  length_eq := rfl
  count_eq := rfl
  prefix_le := by
    have h7 : ∀ i < 7, (([DyckStep.U, .U, .U, .D, .D, .D] : List DyckStep).take i).count
        DyckStep.D ≤ (([DyckStep.U, .U, .U, .D, .D, .D] : List DyckStep).take i).count
        DyckStep.U := by decide
    intro i
    rcases lt_or_ge i 7 with hi | hi
    · exact h7 i hi
    · rw [List.take_of_length_le (by simp; omega)]
      exact h7 6 (by omega)

instance : Fintype (Ballot 6) := instFintypeTwoMul 3

/-- The genus-six instance of the count: `catalan 3 = 5` specialized to ballot
sequences. -/
theorem card_six_eq_five : Fintype.card (Ballot 6) = 5 := by
  show Fintype.card (Ballot (2 * 3)) = 5
  rw [card_eq_catalan, catalan_three]

end Ballot

end DraismaVargas.Count
