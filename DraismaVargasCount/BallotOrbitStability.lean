module

public import DraismaVargasCount.DiagonalRigidityObligation
public import DraismaVargasCount.DiagonalExtract

@[expose] public section

/-!
# The ballot diagonals are stable under the relabellings of the caterpillar core

`BallotSlopes.BallotDiagonalRelabelStable m` asks that the set of ballot core diagonals be stable
under the slot action of the incidence-preserving relabellings of the caterpillar core
`catCore m`.  This module proves it at every `m` (`ballotDiagonalRelabelStable`), in a sharp
form (`ballotCoreDiag_relabel_eq_self_or_reverse`): the orbit of a ballot diagonal under
`Relabel (catCore m) (catCore m)` is contained in
`{ballotCoreDiag m s, ballotCoreDiag m (reverseSlopes s)}` -- at most two elements.

Consequently the hypothesis of the refutation criterion
`SlopeRigidity.not_diagonalClassification_of_orbit_escape` never holds (`no_orbit_escape`), and
neither does the negation of `BallotDiagonalRelabelStable` (`not_not_ballotDiagonalRelabelStable`).
The dichotomy itself, and the slope reversal `reverseSlopes`, are used in the analysis of the
ballot members over the caterpillar (`BallotStabiliserReduction`, `LoopAdjacentDiagonal`,
`SpineReversal`, ...).

## The mechanism

**The proof does not enumerate `Aut (catCore m)`.**  Two invariants that every relabelling
respects, plus one injectivity argument, decide the question with no automorphism table at any
genus.

1. **Loop-adjacency.**  Call a slot *loop-adjacent* when one of its two endpoints carries a
   self-loop (`LoopAdjacent`).  A `Relabel` preserves it (`loopAdjacent_relabel`), because it
   preserves incidence multiplicities and hence self-loops.  This is strictly finer than
   `SlopeRigidity.relabel_loop_iff`: it pins the *neighbours* of a loop too.
2. **Every ballot diagonal is constant on the loop-adjacent slots**
   (`ballotCoreDiag_of_loopAdjacent`): `2` on the `2m+2` self-loops, `1/2` on the `2m` stems
   *and* on the two extreme spine slots `e = 1` and `e = 6m+1`, the latter because
   `Slopes.head_eq` and `Slopes.getLast_eq` force `s₁ = s_{2m+1} = 2`.  That is `4m+4` of the
   `6m+3` slots disposed of, where `SlopeRigidity.ballotCoreDiag_relabel_eq_of_nonleaf` disposes
   of `2m+2`.
3. **What is left is a path.**  The `2m-1` surviving slots are the interior spine edges `3k+4`,
   `k < 2m-1`, with endpoints `2k+1` and `2k+3` (`innerSlot_tail_val`, `innerSlot_head_val`), so
   two of them share a vertex exactly when their indices differ by at most one
   (`meet_innerSlot`).  A relabelling preserves sharing a vertex (`meet_relabel`), so it induces
   an injective, range-preserving, unit-step map of `[0, 2m-1)` -- and `walk_rigid` forces such a
   map to be the identity or the reversal.  In the first case the ballot diagonal is fixed
   pointwise; in the second it is carried to the diagonal of the reversed slope sequence.

`walk_rigid` is the whole combinatorial content and it needs no path machinery: a rise followed
by a fall returns to a value already taken, so injectivity alone makes the direction constant.

For example, the two slope sequences `[2,3,2,1,2]` and `[2,1,2,3,2]` of
`BallotSlopes.coordsMultiset_collision` form a reversal orbit of this kind.

## Main results

* `LoopVertex`, `LoopAdjacent`, `loopVertex_relabel`, `loopAdjacent_relabel` -- the invariant,
  over an arbitrary `Core n p`.
* `loopVertex_catCore`, `loopAdjacent_catCore`, `not_loopAdjacent_catCore` -- the invariant
  computed at the caterpillar core, in closed arithmetic form.
* `ballotCoreDiag_of_loopAdjacent`, **`ballotCoreDiag_relabel_eq_of_not_loopAdjacent`** -- the
  reduction of the question from `6m+3` slots to `2m-1`.
* `ballotDiagonalRelabelStable_zero`, `ballotDiagonalRelabelStable_one` -- genus two and genus
  four from the reduction alone (there is nothing left to test); both are subsumed by
  `ballotDiagonalRelabelStable` below and kept because they isolate the mechanism.  The
  genus-two case is also proved independently, as
  `BaseCountParity.ballotDiagonalRelabelStable_genusTwo`.
* **`walk_rigid`** -- an injective unit-step map of `[0, K)` into itself is the identity or the
  reversal.
* `innerSlot`, `exists_innerSlot`, `Meet`, `meet_relabel`, `meet_innerSlot` -- the interior
  spine slots and their path structure.
* `reverseSlopes`, `slope_reverseSlopes` -- a slope sequence read backwards is a slope
  sequence, and its `slope` function is `i ↦ s.slope (g - i)`.
* **`ballotCoreDiag_relabel_eq_self_or_reverse`** -- the sharp dichotomy.
* **`ballotDiagonalRelabelStable`** -- stability, at every `m`.
* `no_orbit_escape`, `not_not_ballotDiagonalRelabelStable` -- the two refutation hypotheses
  never hold.
* `relabel_nontrivial` -- the relabelling group of `catCore (m + 1)` is not trivial
  (`SlopeRigidity.endSwap`), so the statements above are not about a one-element group.  The
  spine reversal is not constructed as a `Relabel` here, so the second alternative of the
  dichotomy is not shown to occur.
-/

namespace DraismaVargas.Count.BallotOrbit

open DraismaVargas.Count
open DraismaVargas.Count.CoreRelabel
open DraismaVargas.Count.FibreCaterpillar
open DraismaVargas.LocalCases.CaterpillarPruning (IsLeafEdge)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p : ℕ} {c c' : Core n p}

/-! ## 1.  Loop vertices and loop-adjacent slots, over an arbitrary core -/

/-- **`v` carries a self-loop.** -/
def LoopVertex (c : Core n p) (v : Fin n) : Prop := ∃ e : Fin p, c.tail e = v ∧ c.head e = v

/-- **The slot `e` has an endpoint that carries a self-loop.**  Every self-loop
is loop-adjacent, so this is a *weakening* of `e` being a loop. -/
def LoopAdjacent (c : Core n p) (e : Fin p) : Prop :=
  LoopVertex c (c.tail e) ∨ LoopVertex c (c.head e)

theorem loopAdjacent_of_loop {e : Fin p} (h : c.tail e = c.head e) : LoopAdjacent c e :=
  Or.inl ⟨e, rfl, h.symm⟩

/-- A relabelling carries each slot to its image with or without exchanging the
two ends; this is `CoreIso.orientation` read through `Relabel.toCoreIso`. -/
theorem relabel_orientation (d : Relabel c c') (e : Fin p) :
    (c'.tail (d.slot e) = d.vtx (c.tail e) ∧ c'.head (d.slot e) = d.vtx (c.head e)) ∨
      (c'.head (d.slot e) = d.vtx (c.tail e) ∧ c'.tail (d.slot e) = d.vtx (c.head e)) :=
  d.toCoreIso.orientation e

/-- **A relabelling carries loop vertices to loop vertices.** -/
theorem loopVertex_relabel (d : Relabel c c') (v : Fin n) :
    LoopVertex c' (d.vtx v) ↔ LoopVertex c v := by
  constructor
  · rintro ⟨e', ht, hh⟩
    refine ⟨d.slot.symm e', ?_, ?_⟩
    · rcases relabel_orientation d (d.slot.symm e') with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rw [Equiv.apply_symm_apply] at h1 h2
      · exact d.vtx.injective (h1.symm.trans ht)
      · exact d.vtx.injective (h1.symm.trans hh)
    · rcases relabel_orientation d (d.slot.symm e') with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rw [Equiv.apply_symm_apply] at h1 h2
      · exact d.vtx.injective (h2.symm.trans hh)
      · exact d.vtx.injective (h2.symm.trans ht)
  · rintro ⟨e, ht, hh⟩
    refine ⟨d.slot e, ?_, ?_⟩
    · rcases relabel_orientation d e with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, ht]
      · rw [h2, hh]
    · rcases relabel_orientation d e with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2, hh]
      · rw [h1, ht]

/-- **A relabelling preserves loop-adjacency.**  This is the invariant the whole
module runs on: it is strictly finer than `SlopeRigidity.relabel_loop_iff`
(loops are preserved), because it also pins the *neighbours* of a loop. -/
theorem loopAdjacent_relabel (d : Relabel c c') (e : Fin p) :
    LoopAdjacent c' (d.slot e) ↔ LoopAdjacent c e := by
  rcases relabel_orientation d e with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [LoopAdjacent, LoopAdjacent, h1, h2, loopVertex_relabel, loopVertex_relabel]
  · rw [LoopAdjacent, LoopAdjacent, h1, h2, loopVertex_relabel, loopVertex_relabel]
    exact or_comm

theorem loopAdjacent_relabel_symm (d : Relabel c c) (e : Fin p) :
    LoopAdjacent c (d.slot.symm e) ↔ LoopAdjacent c e := by
  have h := loopAdjacent_relabel d.symm e
  exact h

/-! ## 2.  The caterpillar core: which slots are loop-adjacent -/

open DraismaVargas.Count.SlopeRigidity (catCore_tail_val catCore_head_val
  catCore_tail_eq_head_iff relabel_isLeafEdge_symm_iff)
open DraismaVargas.Infrastructure.CaterpillarTree (parentIndex)

/-- The tail of a self-loop is a loop vertex. -/
theorem loopVertex_tail_of_leaf (m : ℕ) (e : Fin (6 * m + 3)) (hleaf : IsLeafEdge m e) :
    LoopVertex (catCore m) ((catCore m).tail e) :=
  ⟨e, rfl, ((catCore_tail_eq_head_iff m e).mpr hleaf).symm⟩

/-- **The loop vertices of `catCore m`.**  The `2m+2` self-loops sit at the
even-numbered vertices `0, 2, …, 4m` and at the last vertex `4m+1`; the
remaining `2m` vertices -- the odd ones below `4m+1` -- carry none.  These are
the spine's interior branch vertices. -/
theorem loopVertex_catCore (m : ℕ) (v : Fin (4 * m + 2)) :
    LoopVertex (catCore m) v ↔ (v.val % 2 = 0 ∨ v.val = 4 * m + 1) := by
  have hvlt := v.isLt
  constructor
  · rintro ⟨e, ht, hh⟩
    have hleaf : IsLeafEdge m e := (catCore_tail_eq_head_iff m e).mp (ht.trans hh.symm)
    have hval : branchIdx (catTailVal m e) = v.val := by rw [← catCore_tail_val, ht]
    have hlt := e.isLt
    unfold catTailVal branchIdx parentIndex at hval
    unfold IsLeafEdge at hleaf
    split_ifs at hval <;> omega
  · intro hv
    rcases hv with hv | hv
    · have hlt : 3 * (v.val / 2) < 6 * m + 3 := by omega
      have hleaf : IsLeafEdge m (⟨3 * (v.val / 2), hlt⟩ : Fin (6 * m + 3)) :=
        Or.inl (show 3 * (v.val / 2) % 3 = 0 by omega)
      have hv' : (catCore m).tail (⟨3 * (v.val / 2), hlt⟩ : Fin (6 * m + 3)) = v := by
        refine Fin.ext ?_
        rw [catCore_tail_val]
        show branchIdx (parentIndex (3 * (v.val / 2) + 1)) = v.val
        unfold branchIdx parentIndex
        split_ifs <;> omega
      exact hv' ▸ loopVertex_tail_of_leaf m _ hleaf
    · have hlt : 6 * m + 2 < 6 * m + 3 := by omega
      have hleaf : IsLeafEdge m (⟨6 * m + 2, hlt⟩ : Fin (6 * m + 3)) := Or.inr rfl
      have hv' : (catCore m).tail (⟨6 * m + 2, hlt⟩ : Fin (6 * m + 3)) = v := by
        refine Fin.ext ?_
        rw [catCore_tail_val]
        show branchIdx (parentIndex (6 * m + 2 + 1)) = v.val
        unfold branchIdx parentIndex
        split_ifs <;> omega
      exact hv' ▸ loopVertex_tail_of_leaf m _ hleaf

/-- **The loop-adjacent slots of `catCore m`, in closed form.**  A slot fails to
be loop-adjacent exactly when it is a spine edge (`e ≡ 1 mod 3`) *other* than
the two extreme ones, `e = 1` and `e = 6m+1`.  There are `2m-1` such slots. -/
theorem loopAdjacent_catCore (m : ℕ) (e : Fin (6 * m + 3)) :
    LoopAdjacent (catCore m) e ↔ ¬ (e.val % 3 = 1 ∧ e.val ≠ 1 ∧ e.val ≠ 6 * m + 1) := by
  have hlt := e.isLt
  rw [LoopAdjacent, loopVertex_catCore, loopVertex_catCore, catCore_tail_val, catCore_head_val]
  unfold catTailVal catHeadVal branchIdx parentIndex IsLeafEdge
  split_ifs <;> omega

/-- The same, stated positively on the slots that survive. -/
theorem not_loopAdjacent_catCore (m : ℕ) (e : Fin (6 * m + 3)) :
    ¬ LoopAdjacent (catCore m) e ↔ (e.val % 3 = 1 ∧ e.val ≠ 1 ∧ e.val ≠ 6 * m + 1) := by
  rw [loopAdjacent_catCore, not_not]

/-! ## 3.  `ballotCoreDiag` is constant on the loop-adjacent slots -/

/-- **The value of a ballot diagonal on a loop-adjacent slot does not depend on
the slope sequence.**  It is `2` on a self-loop and `1/2` on everything else
that touches one: on a stem by definition, and on the two extreme spine slots
`e = 1` and `e = 6m+1` because `Slopes.head_eq` and `Slopes.getLast_eq` force
`s₁ = s_{2m+1} = 2`.  This is the whole mechanism behind the orbit test. -/
theorem ballotCoreDiag_of_loopAdjacent (m : ℕ) (s : Slopes (2 * (m + 1)))
    {e : Fin (6 * m + 3)} (h : LoopAdjacent (catCore m) e) :
    BallotSlopes.ballotCoreDiag m s e = if IsLeafEdge m e then 2 else 1 / 2 := by
  by_cases hleaf : IsLeafEdge m e
  · rw [ite_eq_left hleaf, BallotSlopes.ballotCoreDiag_leaf s hleaf]
  · rw [ite_eq_right hleaf, loopAdjacent_catCore] at *
    have hlt := e.isLt
    have hleaf' : e.val % 3 ≠ 0 ∧ e.val ≠ 6 * m + 2 := by
      unfold IsLeafEdge at hleaf; push Not at hleaf; exact hleaf
    by_cases hspine : e.val % 3 = 1
    · rw [BallotSlopes.ballotCoreDiag_spine s hspine]
      have hend : e.val = 1 ∨ e.val = 6 * m + 1 := by
        by_contra hc
        push Not at hc
        exact h ⟨hspine, hc.1, hc.2⟩
      rcases hend with h1 | h1
      · rw [h1, show (1 + 2) / 3 = 1 from rfl, Slopes.slope_one]
        norm_num
      · rw [h1, show (6 * m + 1 + 2) / 3 = 2 * m + 1 by omega,
          Slopes.slope_of_ge s (by omega)]
        norm_num
    · exact BallotSlopes.ballotCoreDiag_stem s (by omega) hleaf'.2

/-! ## 4.  The reduction: only the non-loop-adjacent slots can move the value -/

/-- **The orbit test reduces to the `2m-1` interior spine slots.**  This is a
strict sharpening of `SlopeRigidity.ballotCoreDiag_relabel_eq_of_nonleaf`, which
removed only the `2m+2` leaf slots: the `2m` stems and the two extreme spine
slots go too, because a relabelling preserves loop-adjacency
(`loopAdjacent_relabel`) and `ballotCoreDiag` is constant there
(`ballotCoreDiag_of_loopAdjacent`). -/
theorem ballotCoreDiag_relabel_eq_of_not_loopAdjacent {m : ℕ} (s t : Slopes (2 * (m + 1)))
    (d : Relabel (catCore m) (catCore m))
    (h : ∀ slot, ¬ LoopAdjacent (catCore m) slot →
      BallotSlopes.ballotCoreDiag m s (d.slot.symm slot) =
        BallotSlopes.ballotCoreDiag m t slot) :
    (fun slot ↦ BallotSlopes.ballotCoreDiag m s (d.slot.symm slot)) =
      BallotSlopes.ballotCoreDiag m t := by
  funext slot
  by_cases hla : LoopAdjacent (catCore m) slot
  · have hla' : LoopAdjacent (catCore m) (d.slot.symm slot) :=
      (loopAdjacent_relabel_symm d slot).mpr hla
    rw [ballotCoreDiag_of_loopAdjacent m s hla', ballotCoreDiag_of_loopAdjacent m t hla]
    by_cases hleaf : IsLeafEdge m slot
    · rw [ite_eq_left hleaf, ite_eq_left ((relabel_isLeafEdge_symm_iff d slot).mpr hleaf)]
    · rw [ite_eq_right hleaf, ite_eq_right fun hx ↦ hleaf ((relabel_isLeafEdge_symm_iff d slot).mp hx)]
  · exact h slot hla

/-! ## 5.  Genus two and genus four: the test has nothing left to test

Both are subsumed by `ballotDiagonalRelabelStable` in §10.  They are kept
because at these two genera the reduction of §4 already finishes -- `catCore 0`
has no interior spine slot and `catCore 1` has exactly one -- so they isolate
the mechanism with no walk argument at all. -/

/-- **Genus two.**  `catCore 0` has no interior spine slot at all, so every
relabelling fixes every ballot diagonal on the nose. -/
theorem ballotDiagonalRelabelStable_zero : BallotSlopes.BallotDiagonalRelabelStable 0 := by
  intro s d
  refine ⟨s, ballotCoreDiag_relabel_eq_of_not_loopAdjacent s s d fun slot hslot ↦ ?_⟩
  exfalso
  obtain ⟨h1, h2, h3⟩ := (not_loopAdjacent_catCore 0 slot).mp hslot
  have := slot.isLt
  omega

/-- **Genus four.**  `catCore 1` has exactly one interior spine slot, `e = 4`, so
a relabelling must fix it, and again every ballot diagonal is fixed on the
nose. -/
theorem ballotDiagonalRelabelStable_one : BallotSlopes.BallotDiagonalRelabelStable 1 := by
  intro s d
  refine ⟨s, ballotCoreDiag_relabel_eq_of_not_loopAdjacent s s d fun slot hslot ↦ ?_⟩
  have hslot' : ¬ LoopAdjacent (catCore 1) (d.slot.symm slot) :=
    fun hx ↦ hslot ((loopAdjacent_relabel_symm d slot).mp hx)
  obtain ⟨h1, h2, h3⟩ := (not_loopAdjacent_catCore 1 slot).mp hslot
  obtain ⟨g1, g2, g3⟩ := (not_loopAdjacent_catCore 1 (d.slot.symm slot)).mp hslot'
  have hlt := slot.isLt
  have hlt' := (d.slot.symm slot).isLt
  rw [show d.slot.symm slot = slot from Fin.ext (by omega)]

/-! ## 6.  An injective unit-step walk that stays in range is monotone

The only combinatorial input the general case needs.  `φ` is the index map a
relabelling induces on the interior spine slots; the hypotheses say it is
injective, stays inside `[0, K)`, and moves consecutive indices to indices at
distance at most one.  There is no "path automorphism" machinery: injectivity
alone forbids a change of direction, because a rise followed by a fall returns
to a value already taken. -/

theorem walk_rigid {K : ℕ} (φ : ℕ → ℕ)
    (hinj : ∀ a b, a < K → b < K → φ a = φ b → a = b)
    (hlt : ∀ a, a < K → φ a < K)
    (hadj : ∀ a, a + 1 < K → φ (a + 1) ≤ φ a + 1 ∧ φ a ≤ φ (a + 1) + 1) :
    (∀ a, a < K → φ a = a) ∨ (∀ a, a < K → φ a = K - 1 - a) := by
  have hstep : ∀ a, a + 1 < K → φ (a + 1) = φ a + 1 ∨ φ a = φ (a + 1) + 1 := by
    intro a ha
    have hne : φ (a + 1) ≠ φ a := fun h ↦ by
      have := hinj (a + 1) a (by omega) (by omega) h; omega
    have := hadj a ha
    omega
  have hup : ∀ a, a + 1 + 1 < K → φ (a + 1) = φ a + 1 →
      φ (a + 1 + 1) = φ (a + 1) + 1 := by
    intro a ha h
    rcases hstep (a + 1) ha with h' | h'
    · exact h'
    · exact absurd (hinj (a + 1 + 1) a (by omega) (by omega) (by omega)) (by omega)
  have hdown : ∀ a, a + 1 + 1 < K → φ a = φ (a + 1) + 1 →
      φ (a + 1) = φ (a + 1 + 1) + 1 := by
    intro a ha h
    rcases hstep (a + 1) ha with h' | h'
    · exact absurd (hinj (a + 1 + 1) a (by omega) (by omega) (by omega)) (by omega)
    · exact h'
  have hmono : (∀ a, a + 1 < K → φ (a + 1) = φ a + 1) ∨
      (∀ a, a + 1 < K → φ a = φ (a + 1) + 1) := by
    by_cases hK : 1 < K
    · rcases hstep 0 hK with h0 | h0
      · refine Or.inl fun a ↦ ?_
        induction a with
        | zero => intro _; exact h0
        | succ b ih => intro hb; exact hup b hb (ih (by omega))
      · refine Or.inr fun a ↦ ?_
        induction a with
        | zero => intro _; exact h0
        | succ b ih => intro hb; exact hdown b hb (ih (by omega))
    · exact Or.inl fun a ha ↦ by omega
  rcases hmono with hA | hA
  · refine Or.inl fun a ha ↦ ?_
    have hlin : ∀ a, a < K → φ a = φ 0 + a := by
      intro a
      induction a with
      | zero => intro _; omega
      | succ b ih =>
        intro hb
        have h1 := hA b hb
        have h2 := ih (by omega)
        omega
    have h0 : φ 0 = 0 := by
      have h1 := hlin (K - 1) (by omega)
      have h2 := hlt (K - 1) (by omega)
      omega
    have := hlin a ha
    omega
  · refine Or.inr fun a ha ↦ ?_
    have hlin : ∀ a, a < K → φ a + a = φ 0 := by
      intro a
      induction a with
      | zero => intro _; omega
      | succ b ih =>
        intro hb
        have h1 := hA b hb
        have h2 := ih (by omega)
        omega
    have h1 := hlin (K - 1) (by omega)
    have h2 := hlt (K - 1) (by omega)
    have h3 := hlin a ha
    have h4 := hlt 0 (by omega)
    omega

/-! ## 7.  The interior spine slots, indexed -/

theorem innerVal_lt {m k : ℕ} (hk : k < 2 * m - 1) : 3 * k + 4 < 6 * m + 3 := by omega

/-- **The `k`-th interior spine slot of `catCore m`**: the slot `3k+4`, for
`k < 2m-1`.  These are exactly the slots `loopAdjacent_catCore` leaves over. -/
def innerSlot (m k : ℕ) (hk : k < 2 * m - 1) : Fin (6 * m + 3) := ⟨3 * k + 4, innerVal_lt hk⟩

theorem innerSlot_val {m k : ℕ} (hk : k < 2 * m - 1) :
    (innerSlot m k hk).val = 3 * k + 4 := rfl

theorem not_isLeafEdge_innerSlot {m k : ℕ} (hk : k < 2 * m - 1) :
    ¬ IsLeafEdge m (innerSlot m k hk) := by
  rintro (h | h)
  · exact absurd (show (3 * k + 4) % 3 = 0 from h) (by omega)
  · exact absurd (show 3 * k + 4 = 6 * m + 2 from h) (by omega)

theorem not_loopAdjacent_innerSlot {m k : ℕ} (hk : k < 2 * m - 1) :
    ¬ LoopAdjacent (catCore m) (innerSlot m k hk) := by
  rw [not_loopAdjacent_catCore, innerSlot_val]
  exact ⟨by omega, by omega, by omega⟩

/-- **And there are no others.** -/
theorem exists_innerSlot {m : ℕ} {e : Fin (6 * m + 3)} (h : ¬ LoopAdjacent (catCore m) e) :
    ∃ k, ∃ hk : k < 2 * m - 1, e = innerSlot m k hk := by
  rw [not_loopAdjacent_catCore] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hlt := e.isLt
  exact ⟨(e.val - 4) / 3, by omega, Fin.ext (by rw [innerSlot_val]; omega)⟩

theorem innerSlot_tail_val {m k : ℕ} (hk : k < 2 * m - 1) :
    ((catCore m).tail (innerSlot m k hk)).val = 2 * k + 1 := by
  rw [catCore_tail_val]
  show branchIdx (parentIndex (3 * k + 4 + 1)) = 2 * k + 1
  unfold branchIdx parentIndex
  split_ifs <;> omega

theorem innerSlot_head_val {m k : ℕ} (hk : k < 2 * m - 1) :
    ((catCore m).head (innerSlot m k hk)).val = 2 * k + 3 := by
  rw [catCore_head_val]
  unfold catHeadVal
  rw [ite_eq_right (not_isLeafEdge_innerSlot hk)]
  show branchIdx (3 * k + 4 + 1) = 2 * k + 3
  unfold branchIdx
  omega

/-! ## 8.  Slots that share a vertex -/

/-- Two slots meet when they have an endpoint in common. -/
def Meet (c : Core n p) (e f : Fin p) : Prop :=
  c.tail e = c.tail f ∨ c.tail e = c.head f ∨ c.head e = c.tail f ∨ c.head e = c.head f

/-- **A relabelling preserves meeting.** -/
theorem meet_relabel (d : Relabel c c') (e f : Fin p) :
    Meet c' (d.slot e) (d.slot f) ↔ Meet c e f := by
  rcases relabel_orientation d e with ⟨he1, he2⟩ | ⟨he1, he2⟩ <;>
    rcases relabel_orientation d f with ⟨hf1, hf2⟩ | ⟨hf1, hf2⟩ <;>
      rw [Meet, Meet, he1, he2, hf1, hf2] <;>
        simp only [Equiv.apply_eq_iff_eq] <;> tauto

theorem meet_relabel_symm (d : Relabel c c) (e f : Fin p) :
    Meet c (d.slot.symm e) (d.slot.symm f) ↔ Meet c e f := meet_relabel d.symm e f

/-- **The interior spine slots form a path**: `innerSlot k` has endpoints
`2k+1` and `2k+3`, so two of them meet exactly when their indices differ by at
most one. -/
theorem meet_innerSlot {m k l : ℕ} (hk : k < 2 * m - 1) (hl : l < 2 * m - 1) :
    Meet (catCore m) (innerSlot m k hk) (innerSlot m l hl) ↔ (k ≤ l + 1 ∧ l ≤ k + 1) := by
  rw [Meet]
  simp only [Fin.ext_iff, innerSlot_tail_val, innerSlot_head_val]
  omega

/-! ## 9.  The reversal of a slope sequence -/

/-- **A slope sequence read backwards is a slope sequence.**  Every field of
`Slopes` is reversal-symmetric: the two boundary conditions swap, `one_le` is a
membership condition, and `SlopeStepRel` is a symmetric relation. -/
def reverseSlopes {g : ℕ} (s : Slopes g) : Slopes g where
  slopes := s.slopes.reverse
  length_eq := by rw [List.length_reverse]; exact s.length_eq
  head_eq := fun x hx ↦ s.getLast_eq x (by rwa [List.head?_reverse] at hx)
  getLast_eq := fun x hx ↦ s.head_eq x (by rwa [List.getLast?_reverse] at hx)
  one_le := fun x hx ↦ s.one_le x (List.mem_reverse.mp hx)
  step := by
    rw [List.isChain_reverse]
    exact (List.IsChain.iff fun a b ↦ or_comm).mp s.step

theorem slope_reverseSlopes {g : ℕ} (s : Slopes g) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ g - 1) :
    (reverseSlopes s).slope i = s.slope (g - i) := by
  have hlen : s.slopes.length = g - 1 := s.length_eq
  have h3 : i - 1 < s.slopes.reverse.length := by rw [List.length_reverse]; omega
  have h4 : g - i - 1 < s.slopes.length := by omega
  show s.slopes.reverse.getD (i - 1) 2 = s.slopes.getD (g - i - 1) 2
  rw [← List.getElem_eq_getD (h := h3) 2, ← List.getElem_eq_getD (h := h4) 2,
    List.getElem_reverse]
  congr 1
  omega


/-! ## 10.  The ballot diagonals are relabelling-stable at every `m` -/

/-- **The index map a relabelling induces on the interior spine slots.** -/
def innerIndex {m : ℕ} (d : Relabel (catCore m) (catCore m)) (k : ℕ) : ℕ :=
  if hk : k < 2 * m - 1 then ((d.slot.symm (innerSlot m k hk)).val - 4) / 3 else 0

theorem innerIndex_eq {m : ℕ} (d : Relabel (catCore m) (catCore m)) {k : ℕ}
    (hk : k < 2 * m - 1) :
    innerIndex d k = ((d.slot.symm (innerSlot m k hk)).val - 4) / 3 := by
  unfold innerIndex; exact dite_eq_left hk

theorem innerIndex_spec {m : ℕ} (d : Relabel (catCore m) (catCore m)) {k : ℕ}
    (hk : k < 2 * m - 1) :
    innerIndex d k < 2 * m - 1 ∧
      (d.slot.symm (innerSlot m k hk)).val = 3 * innerIndex d k + 4 := by
  have hna : ¬ LoopAdjacent (catCore m) (d.slot.symm (innerSlot m k hk)) :=
    fun hx ↦ not_loopAdjacent_innerSlot hk ((loopAdjacent_relabel_symm d _).mp hx)
  obtain ⟨h1, h2, h3⟩ := (not_loopAdjacent_catCore m _).mp hna
  have hlt := (d.slot.symm (innerSlot m k hk)).isLt
  have hk' := innerIndex_eq d hk
  exact ⟨by omega, by omega⟩

theorem innerSlot_symm {m : ℕ} (d : Relabel (catCore m) (catCore m)) {k : ℕ}
    (hk : k < 2 * m - 1) :
    d.slot.symm (innerSlot m k hk) = innerSlot m (innerIndex d k) (innerIndex_spec d hk).1 :=
  Fin.ext (by rw [innerSlot_val]; exact (innerIndex_spec d hk).2)

/-- **The headline, in its sharp form: the orbit of a ballot diagonal under
`Relabel (catCore m) (catCore m)` has at most two elements.**  A relabelling
either fixes every interior spine slot, and then fixes `ballotCoreDiag m s`
pointwise, or reverses them all, and then carries it to
`ballotCoreDiag m (reverseSlopes s)`.

The mechanism, in one line: a relabelling preserves loop-adjacency, every
ballot diagonal is constant (`2`, then `1/2`) on the loop-adjacent slots, and
what is left is an injective unit-step walk on the `2m-1` interior spine slots,
which `walk_rigid` forces to be the identity or the reversal. -/
theorem ballotCoreDiag_relabel_eq_self_or_reverse (m : ℕ) (s : Slopes (2 * (m + 1)))
    (d : Relabel (catCore m) (catCore m)) :
    (fun slot ↦ BallotSlopes.ballotCoreDiag m s (d.slot.symm slot)) =
        BallotSlopes.ballotCoreDiag m s ∨
      (fun slot ↦ BallotSlopes.ballotCoreDiag m s (d.slot.symm slot)) =
        BallotSlopes.ballotCoreDiag m (reverseSlopes s) := by
  have hinj : ∀ a b, a < 2 * m - 1 → b < 2 * m - 1 → innerIndex d a = innerIndex d b → a = b := by
    intro a b ha hb hab
    have h1 := (innerIndex_spec d ha).2
    have h2 := (innerIndex_spec d hb).2
    have heq : d.slot.symm (innerSlot m a ha) = d.slot.symm (innerSlot m b hb) :=
      Fin.ext (by omega)
    have h3 := congrArg Fin.val (d.slot.symm.injective heq)
    rw [innerSlot_val, innerSlot_val] at h3
    omega
  have hadj : ∀ a, a + 1 < 2 * m - 1 →
      innerIndex d (a + 1) ≤ innerIndex d a + 1 ∧ innerIndex d a ≤ innerIndex d (a + 1) + 1 := by
    intro a ha
    have ha' : a < 2 * m - 1 := by omega
    have hmeet : Meet (catCore m) (innerSlot m a ha') (innerSlot m (a + 1) ha) :=
      (meet_innerSlot ha' ha).mpr ⟨by omega, by omega⟩
    have hm := (meet_relabel_symm d (innerSlot m a ha') (innerSlot m (a + 1) ha)).mpr hmeet
    rw [innerSlot_symm d ha', innerSlot_symm d ha, meet_innerSlot] at hm
    exact ⟨hm.2, hm.1⟩
  rcases walk_rigid (innerIndex d) hinj (fun a ha ↦ (innerIndex_spec d ha).1) hadj with hA | hB
  · refine Or.inl (ballotCoreDiag_relabel_eq_of_not_loopAdjacent s s d fun slot hna ↦ ?_)
    obtain ⟨k, hk, rfl⟩ := exists_innerSlot hna
    rw [innerSlot_symm d hk]
    congr 1
    exact Fin.ext (by rw [innerSlot_val, innerSlot_val, hA k hk])
  · refine Or.inr (ballotCoreDiag_relabel_eq_of_not_loopAdjacent s (reverseSlopes s) d
      fun slot hna ↦ ?_)
    obtain ⟨k, hk, rfl⟩ := exists_innerSlot hna
    rw [innerSlot_symm d hk,
      BallotSlopes.ballotCoreDiag_spine s
        (show (innerSlot m (innerIndex d k) (innerIndex_spec d hk).1).val % 3 = 1 by
          rw [innerSlot_val]; omega),
      BallotSlopes.ballotCoreDiag_spine (reverseSlopes s)
        (show (innerSlot m k hk).val % 3 = 1 by rw [innerSlot_val]; omega)]
    simp only [innerSlot_val]
    rw [show (3 * innerIndex d k + 4 + 2) / 3 = 2 * m - k by rw [hB k hk]; omega,
      show (3 * k + 4 + 2) / 3 = k + 2 by omega,
      slope_reverseSlopes s (by omega) (by omega),
      show 2 * (m + 1) - (k + 2) = 2 * m - k by omega]

/-- **`BallotSlopes.BallotDiagonalRelabelStable m` holds, at every `m`.**

`SlopeRigidity.not_diagonalClassification_of_orbit_escape` refutes
`BallotSlopes.DiagonalClassification` from a *failure* of this condition; by
this theorem that hypothesis never holds, at any genus. -/
theorem ballotDiagonalRelabelStable (m : ℕ) : BallotSlopes.BallotDiagonalRelabelStable m := by
  intro s d
  rcases ballotCoreDiag_relabel_eq_self_or_reverse m s d with h | h
  · exact ⟨s, h⟩
  · exact ⟨reverseSlopes s, h⟩

/-- **No orbit escapes**: no core symmetry carries any ballot diagonal off the
set of ballot diagonals.  This is the exact negation of the
hypothesis `hescape` of
`SlopeRigidity.not_diagonalClassification_of_orbit_escape`. -/
theorem no_orbit_escape (m : ℕ) (s : Slopes (2 * (m + 1)))
    (d : Relabel (catCore m) (catCore m)) :
    ¬ ∀ t : Slopes (2 * (m + 1)),
      (fun slot ↦ BallotSlopes.ballotCoreDiag m s (d.slot.symm slot)) ≠
        BallotSlopes.ballotCoreDiag m t := by
  intro h
  obtain ⟨t, ht⟩ := ballotDiagonalRelabelStable m s d
  exact h t ht

/-- **The negation of `BallotDiagonalRelabelStable m` is false**, at every `m`. -/
theorem not_not_ballotDiagonalRelabelStable (m : ℕ) :
    ¬ ¬ BallotSlopes.BallotDiagonalRelabelStable m :=
  fun h ↦ h (ballotDiagonalRelabelStable m)

/-- **The quantifier is not vacuous.**  For every even genus at least four the
relabelling group of `catCore m` has a non-identity element, so
`ballotDiagonalRelabelStable` is not a statement about a one-element group.
This is `SlopeRigidity.endSwap`, recorded here so the theorems above can be read
without chasing it. -/
theorem relabel_nontrivial (m : ℕ) :
    ∃ d : Relabel (catCore (m + 1)) (catCore (m + 1)), ¬ ∀ e, d.slot e = e :=
  ⟨SlopeRigidity.endSwap m, SlopeRigidity.endSwap_ne_refl m⟩

end DraismaVargas.Count.BallotOrbit
