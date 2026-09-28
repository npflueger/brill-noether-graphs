import Utilities.Combinatorics.Slopes

/-!
# The stack of a slope sequence: which sheets are glued along which spine edge

**Source.**  Vargas, Part II (arXiv:2609.09109), `prop-caterpillar-ballot`,
read through the sheet-gluing encoding of `Infrastructure.GluingDatum`.  This
module is the arithmetic half of the ballot-parametrised caterpillar datum: it
fixes, for a slope sequence `s`, *which* `s_i`-element subset of the
`d = m + 2` sheets is glued along the spine edge `h_i`, and proves the facts
the gluing datum of `Count.BallotDatum` needs about those subsets.  Through
`Count.BallotDatum` it feeds the ballot members of the base count over the
caterpillar of loops (step 1 of `DraismaVargasCount/Assembly.lean`).  Nothing
here mentions a graph, a partition or a gluing datum.

## Why a choice has to be made, and which choice this is

In the quotient-source encoding a full-dimensional morphism over the
caterpillar of loops is a partition of the sheet set above every target vertex
and every target occurrence.  Part II's `prop-caterpillar-ballot`(2) determines
the *sizes*: the block above the spine edge `h_i` has `s_i` sheets, the block
above the spine vertex `p_i` has `m(B_i) = max (s_{i-1}, s_i)`, and the block
above a stem (the bridge) has two.  Refinement at `p_i` forces the two spine
blocks `S_{i-1}` and `S_i` to be **nested**, since their union has
`max (s_{i-1}, s_i)` elements; so the family `(S_i)` is a chain that grows by
one sheet at an up-step and shrinks by one at a down-step.  The source is
connected exactly when the `m` up-steps introduce `m` *distinct* new sheets, so
the choice that works is the one that never reuses a discarded label:

```
S_i = {0} ∪ {cum i - s_i + 2, …, cum i},    cum i = 1 + #{up-steps up to i}.
```

`cum` is the counter of new labels, `cum 0 = cum 1 = 1` and
`cum (g-1) = m + 1` (`cum_last`), and each `S_i` is an interval of labels
hanging off the spine sheet `0`.  Up-steps extend the interval on the right by
the brand-new label `cum i`; down-steps drop its left end.  At the
distinguished ballot sequence `(2,1,2,1,…,2)` this returns `{0, j}` at the
`j`-th pair of lollipops, which is the caterpillar datum of
`LocalCases.CaterpillarDatum` (that comparison is made in `Count.BallotDatum`).

## The indexing convention

`Slopes.slope s i` is Part II's `s_i` for `1 ≤ i ≤ g - 1`, extended by the constant
`2` outside that range -- deliberately, so that `slope s 0 = slope s 1 = 2` and
`slope s i = 2` for `i ≥ g - 1`, which makes the two end lollipops of the
caterpillar obey the same formulas as the interior ones.  The price is that the
step relation is *not* available at `i = 0` or `i ≥ g - 1`; `slope_trichotomy`
is the replacement, and it is the only step fact used below.

## What is proved

* `slope_one`, `slope_of_ge`, `one_le_slope`, `slope_rel`, `slope_trichotomy`
  -- the extended slope function and its step behaviour.
* `cum`, `dn` -- the up-step and down-step counters, with `balance`
  (`s_i + #down = 1 + #up`, Part II's partial-sum identity
  `b_1 + ⋯ + b_i = s_i - 1` for the ballot sequence of a slope sequence, in the
  form with no truncated subtraction), `cum_mono`, `cum_le_last`, and
  `cum_last : cum s (g-1) = m + 1` at `g = 2 * (m+1)`.
* `SpineMem`, `VertMem`, `PairMem` -- the three sheet-membership predicates:
  the block above a spine edge, above a spine vertex, above a stem.
* `card_spineMem`, `card_vertMem`, `card_pairMem` -- their cardinalities
  `s_i`, `max (s_{i-1}, s_i)` and `2`.
* `vertMem_of_spineMem_left/right`, `vertMem_iff`, `spineMem_mono_up/down` --
  the nesting, in the form the refinement receipts of the gluing datum consume.
* `cum_one`, `spineMem_one_iff_pairMem_one`, `vertMem_of_pairMem` -- the two
  boundary receipts: at the first lollipop the spine block and the bridge pair
  coincide (the root `u_1` carries no stem), and at every lollipop the bridge
  pair lies inside the spine-vertex block.
* `exists_cum_eq` -- every label `1 ≤ c ≤ cum s n` is `cum s i` at some `i ≤ n`
  whose slope is at least two, i.e. every sheet really occurs in some `S_i`.
  This is the combinatorial content of connectedness of the source.

## Scope

* Nothing geometric: no graph, no partition, no gluing datum, no morphism.
  The statement that these subsets *are* the blocks of a valid gluing datum is
  `Count.BallotDatum`, and this module is not aware of it.
* `cum_last`, `cum_le` and `card_*` carry the genus hypothesis
  `g = 2 * (m + 1)` explicitly, as a hypothesis, never as a standing
  assumption; `Slopes g` itself is defined for every `g`.
* Nothing here asserts that a slope sequence exists, that there are Catalan
  many of them, or anything at all about the number of sheets beyond
  `cum s i ≤ m + 1`.  The count is `Count.Slopes.card_eq_catalan`.
-/

namespace DraismaVargas.Count

namespace Slopes

variable {g : ℕ}

/-! ## 1.  The extended slope function -/

/-- Part II's `s_i`, extended to every natural index by the constant `2`.  For
`1 ≤ i ≤ g - 1` this is `slopes[i-1]`; at `i = 0` it repeats `s_1`, and beyond
`g - 1` it repeats the value `2` that `s_{g-1}` already has. -/
def slope (s : Slopes g) (i : ℕ) : ℕ := s.slopes.getD (i - 1) 2

/-- The extension at `0` repeats `s_1`: both read index `0` of the list. -/
theorem slope_zero (s : Slopes g) : s.slope 0 = s.slope 1 := rfl

theorem slope_eq_getElem (s : Slopes g) {i : ℕ} (hi : i - 1 < s.slopes.length) :
    s.slope i = s.slopes[i - 1] := (List.getElem_eq_getD 2).symm

/-- Part II's `s_1 = 2`. -/
theorem slope_one (s : Slopes g) : s.slope 1 = 2 := by
  have hhead := s.head_eq
  unfold slope
  rw [Nat.sub_self, List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?]
  cases hcase : s.slopes.head? with
  | none => simp
  | some a => rw [hhead a (by rw [hcase]; exact rfl)]; rfl

/-- Every slope is positive: Part II's `s_i ≥ 1`, on the extension. -/
theorem one_le_slope (s : Slopes g) (i : ℕ) : 1 ≤ s.slope i := by
  unfold slope
  rw [List.getD_eq_getElem?_getD]
  cases hcase : s.slopes[i - 1]? with
  | none => simp
  | some a => exact s.one_le a (List.mem_of_getElem? hcase)

/-- Beyond the last spine edge the extension is constantly `2`; at `i = g - 1`
this is Part II's `s_{g-1} = 2`. -/
theorem slope_of_ge (s : Slopes g) {i : ℕ} (hi : g - 1 ≤ i) : s.slope i = 2 := by
  have hlen := s.length_eq
  have hlast := s.getLast_eq
  rcases Nat.lt_or_ge (i - 1) s.slopes.length with hlt | hge
  · -- inside the list: then `i - 1` is the last index, and `getLast? = some _`
    have hi1 : i - 1 = s.slopes.length - 1 := by omega
    have hget : s.slopes.getLast? = s.slopes[i - 1]? := by
      rw [List.getLast?_eq_getElem?, hi1]
    have hsome : s.slopes[i - 1]? = some s.slopes[i - 1] := by
      rw [List.getElem?_eq_getElem hlt]
    unfold slope
    rw [List.getD_eq_getElem?_getD, hsome]
    exact hlast _ (by rw [hget, hsome]; exact rfl)
  · unfold slope
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
    rfl

/-- Part II's step condition `s_i - s_{i-1} = ±1`, read on the extension at an
index where the chain really applies. -/
theorem slope_rel (s : Slopes g) {i : ℕ} (h1 : 1 ≤ i) (h2 : i + 1 ≤ g - 1) :
    SlopeStepRel (s.slope i) (s.slope (i + 1)) := by
  have hlen := s.length_eq
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hlt : j + 1 < s.slopes.length := by omega
  have hchain := s.step.getElem j hlt
  have hA : s.slope (j + 1) = s.slopes[j] := (List.getElem_eq_getD 2).symm
  have hB : s.slope (j + 1 + 1) = s.slopes[j + 1] := (List.getElem_eq_getD 2).symm
  rw [hA, hB]
  exact hchain

/-- **The only step fact used downstream.**  On the extended slope function
every consecutive pair either rises by one, falls by one, or repeats; the third
alternative occurs exactly at the two artificial ends `i = 0` and
`i ≥ g - 1`. -/
theorem slope_trichotomy (s : Slopes g) (i : ℕ) :
    s.slope (i + 1) = s.slope i + 1 ∨ s.slope i = s.slope (i + 1) + 1 ∨
      s.slope (i + 1) = s.slope i := by
  rcases Nat.eq_zero_or_pos i with rfl | h1
  · exact Or.inr (Or.inr (slope_zero s).symm)
  · rcases Nat.lt_or_ge (g - 1) (i + 1) with h2 | h2
    · refine Or.inr (Or.inr ?_)
      rw [slope_of_ge s (by omega), slope_of_ge s (by omega)]
    · rcases slope_rel s h1 h2 with h | h
      exacts [Or.inl h, Or.inr (Or.inl h)]

/-- At every index at least one of the two neighbouring slopes is at least two:
either the index is one of the artificial ends, where the slope is `2`, or the
step relation forces a value at least `2` on the higher side. -/
theorem two_le_max_slope (s : Slopes g) (i : ℕ) :
    2 ≤ max (s.slope (i - 1)) (s.slope i) := by
  have key : 2 ≤ s.slope (i - 1) ∨ 2 ≤ s.slope i := by
    rcases Nat.lt_or_ge i (g - 1) with hlt | hge
    · rcases Nat.lt_or_ge i 2 with hsmall | hbig
      · have h1 : s.slope 1 = 2 := slope_one s
        have h0 : s.slope 0 = 2 := by rw [slope_zero]; exact h1
        rcases Nat.lt_or_ge i 1 with hzero | hone
        · obtain rfl : i = 0 := by omega
          exact Or.inl (by rw [h0])
        · obtain rfl : i = 1 := by omega
          exact Or.inr (by rw [h1])
      · have hstep := slope_rel s (i := i - 1) (by omega) (by omega)
        rw [show (i - 1) + 1 = i by omega] at hstep
        have hpos := one_le_slope s (i - 1)
        have hpos' := one_le_slope s i
        rcases hstep with h | h
        · exact Or.inr (by omega)
        · exact Or.inl (by omega)
    · exact Or.inr (by rw [slope_of_ge s hge])
  rcases key with h | h
  · exact le_trans h (le_max_left _ _)
  · exact le_trans h (le_max_right _ _)

/-! ## 2.  The two step counters -/

/-- `cum s i - 1` is the number of up-steps of the slope sequence at indices
`≤ i`; `cum s i` itself is the newest sheet label in use at the spine edge
`h_i`.  The offset by one is because sheet `0` is the spine sheet and label `1`
is already in use at `i = 0`. -/
def cum (s : Slopes g) : ℕ → ℕ
  | 0 => 1
  | (i + 1) => cum s i + (if s.slope (i + 1) = s.slope i + 1 then 1 else 0)

/-- The number of down-steps at indices `≤ i`. -/
def dn (s : Slopes g) : ℕ → ℕ
  | 0 => 0
  | (i + 1) => dn s i + (if s.slope i = s.slope (i + 1) + 1 then 1 else 0)

@[simp] theorem cum_zero (s : Slopes g) : s.cum 0 = 1 := rfl

@[simp] theorem dn_zero (s : Slopes g) : s.dn 0 = 0 := rfl

theorem cum_succ (s : Slopes g) (i : ℕ) :
    s.cum (i + 1) = s.cum i + (if s.slope (i + 1) = s.slope i + 1 then 1 else 0) := rfl

theorem dn_succ (s : Slopes g) (i : ℕ) :
    s.dn (i + 1) = s.dn i + (if s.slope i = s.slope (i + 1) + 1 then 1 else 0) := rfl

theorem one_le_cum (s : Slopes g) (i : ℕ) : 1 ≤ s.cum i := by
  induction i with
  | zero => exact le_refl _
  | succ i ih => rw [cum_succ]; omega

theorem cum_le_succ (s : Slopes g) (i : ℕ) : s.cum i ≤ s.cum (i + 1) := by
  rw [cum_succ]; omega

theorem cum_mono (s : Slopes g) {i j : ℕ} (h : i ≤ j) : s.cum i ≤ s.cum j := by
  revert h
  induction j with
  | zero =>
    intro h
    obtain rfl : i = 0 := by omega
    exact le_refl _
  | succ j ih =>
    intro h
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · exact le_trans (ih (by omega)) (cum_le_succ s j)
    · obtain rfl : i = j + 1 := by omega
      exact le_refl _

/-- **Part II's partial-sum identity for the ballot sequence of a slope
sequence**, with no truncated subtraction:
`s_i + #down-steps = 1 + #up-steps + 1`.  Equivalently `s_i - 1` is the height
of the ballot path. -/
theorem balance (s : Slopes g) (i : ℕ) : s.slope i + s.dn i = 1 + s.cum i := by
  induction i with
  | zero =>
    have h : s.slope 0 = 2 := by rw [slope_zero]; exact slope_one s
    rw [h]; rfl
  | succ i ih =>
    rw [cum_succ, dn_succ]
    rcases slope_trichotomy s i with h | h | h
    · rw [if_pos h,
        if_neg (show ¬ (s.slope i = s.slope (i + 1) + 1) by omega)]
      omega
    · rw [if_neg (show ¬ (s.slope (i + 1) = s.slope i + 1) by omega),
        if_pos h]
      omega
    · rw [if_neg (show ¬ (s.slope (i + 1) = s.slope i + 1) by omega),
        if_neg (show ¬ (s.slope i = s.slope (i + 1) + 1) by omega)]
      omega

/-- Every slope is at most one more than the newest label. -/
theorem slope_le_cum_succ (s : Slopes g) (i : ℕ) : s.slope i ≤ s.cum i + 1 := by
  have := balance s i; omega

/-- Each index contributes at most one step. -/
theorem cum_add_dn_le (s : Slopes g) (i : ℕ) : s.cum i + s.dn i ≤ 1 + i := by
  induction i with
  | zero => exact le_refl _
  | succ i ih =>
    rw [cum_succ, dn_succ]
    rcases slope_trichotomy s i with h | h | h
    · rw [if_pos h,
        if_neg (show ¬ (s.slope i = s.slope (i + 1) + 1) by omega)]
      omega
    · rw [if_neg (show ¬ (s.slope (i + 1) = s.slope i + 1) by omega),
        if_pos h]
      omega
    · rw [if_neg (show ¬ (s.slope (i + 1) = s.slope i + 1) by omega),
        if_neg (show ¬ (s.slope i = s.slope (i + 1) + 1) by omega)]
      omega

/-- In the range where the chain condition applies, each index contributes
exactly one step. -/
theorem le_cum_add_dn (s : Slopes g) : ∀ i : ℕ, i + 1 ≤ g - 1 →
    i + 1 ≤ s.cum (i + 1) + s.dn (i + 1) := by
  intro i
  induction i with
  | zero => intro _; have := one_le_cum s (0 + 1); omega
  | succ i ih =>
    intro hle
    have hprev := ih (by omega)
    have hstep := slope_rel s (i := i + 1) (by omega) (by omega)
    rw [cum_succ, dn_succ]
    rcases hstep with h | h
    · rw [if_pos h,
        if_neg (show ¬ (s.slope (i + 1) = s.slope (i + 1 + 1) + 1) by omega)]
      omega
    · rw [if_neg (show ¬ (s.slope (i + 1 + 1) = s.slope (i + 1) + 1) by omega),
        if_pos h]
      omega

/-- Past the last spine edge the up-step counter is constant. -/
theorem cum_of_ge (s : Slopes g) {i : ℕ} (hi : g - 1 ≤ i) :
    s.cum (i + 1) = s.cum i := by
  rw [cum_succ,
    if_neg (show ¬ (s.slope (i + 1) = s.slope i + 1) by
      rw [slope_of_ge s hi, slope_of_ge s (show g - 1 ≤ i + 1 by omega)]; omega),
    Nat.add_zero]

/-- The up-step counter is maximal at the last spine edge. -/
theorem cum_le_last (s : Slopes g) (i : ℕ) : s.cum i ≤ s.cum (g - 1) := by
  rcases Nat.lt_or_ge i (g - 1) with hlt | hge
  · exact cum_mono s (by omega)
  · obtain ⟨k, rfl⟩ : ∃ k, i = (g - 1) + k := ⟨i - (g - 1), by omega⟩
    clear hge
    induction k with
    | zero => exact le_refl _
    | succ k ih =>
      rw [show (g - 1) + (k + 1) = ((g - 1) + k) + 1 by ring,
        cum_of_ge s (show g - 1 ≤ (g - 1) + k by omega)]
      exact ih

/-- **The newest label at the last spine edge is `m + 1`**, so the `m + 2`
sheets `0, 1, …, m + 1` are exactly the labels that occur. -/
theorem cum_last (s : Slopes g) {m : ℕ} (hg : g = 2 * (m + 1)) :
    s.cum (g - 1) = m + 1 := by
  have hslope : s.slope (g - 1) = 2 := slope_of_ge s (le_refl _)
  have hbal := balance s (g - 1)
  have hle := cum_add_dn_le s (g - 1)
  have hge := le_cum_add_dn s (g - 2) (by omega)
  rw [show (g - 2) + 1 = g - 1 by omega] at hge
  omega

theorem cum_le (s : Slopes g) {m : ℕ} (hg : g = 2 * (m + 1)) (i : ℕ) :
    s.cum i ≤ m + 1 := by
  have := cum_le_last s i
  rw [cum_last s hg] at this
  exact this

/-- **Every label is reached at an index whose slope is at least two.**  This is
the combinatorial content of connectedness of the source: the sheet with label
`c` really lies in the block above some spine edge. -/
theorem exists_cum_eq (s : Slopes g) : ∀ (n c : ℕ), 1 ≤ c → c ≤ s.cum n →
    ∃ i, i ≤ n ∧ s.cum i = c ∧ 2 ≤ s.slope i := by
  intro n
  induction n with
  | zero =>
    intro c h1 h2
    rw [cum_zero] at h2
    refine ⟨0, le_refl _, ?_, ?_⟩
    · rw [cum_zero]; omega
    · rw [slope_zero, slope_one]
  | succ n ih =>
    intro c h1 h2
    rcases Nat.lt_or_ge (s.cum n) c with hlt | hge
    · have hup : s.slope (n + 1) = s.slope n + 1 := by
        by_contra hno
        rw [cum_succ, if_neg hno] at h2
        omega
      have hcs : s.cum (n + 1) = s.cum n + 1 := by rw [cum_succ, if_pos hup]
      refine ⟨n + 1, le_refl _, by omega, ?_⟩
      have := one_le_slope s n
      omega
    · obtain ⟨i, hi, hci, hsi⟩ := ih c h1 hge
      exact ⟨i, by omega, hci, hsi⟩


/-! ## 3.  The three sheet-membership predicates

`SpineMem s i` is the block above the spine edge `h_i`: the spine sheet `0`
together with the interval of labels `[cum i - s_i + 2, cum i]`, written
without truncated subtraction.  `VertMem s i` is the block above the spine
vertex `p_i`, the union of the blocks of the two spine edges meeting there.
`PairMem s i` is the bridge pair above the stem `p_i u_i`: the spine sheet and
the newest label.  All three contain sheet `0`. -/

/-- The sheets glued along the spine edge `h_i`. -/
def SpineMem (s : Slopes g) (i k : ℕ) : Prop :=
  k = 0 ∨ (s.cum i + 2 ≤ k + s.slope i ∧ k ≤ s.cum i)

instance (s : Slopes g) (i k : ℕ) : Decidable (s.SpineMem i k) := by
  unfold SpineMem; infer_instance

/-- The sheets glued at the spine vertex `p_i`. -/
def VertMem (s : Slopes g) (i k : ℕ) : Prop :=
  s.SpineMem (i - 1) k ∨ s.SpineMem i k

instance (s : Slopes g) (i k : ℕ) : Decidable (s.VertMem i k) := by
  unfold VertMem; infer_instance

/-- The bridge pair above the stem of the `i`-th lollipop. -/
def PairMem (s : Slopes g) (i k : ℕ) : Prop := k = 0 ∨ k = s.cum i

instance (s : Slopes g) (i k : ℕ) : Decidable (s.PairMem i k) := by
  unfold PairMem; infer_instance

@[simp] theorem spineMem_zero (s : Slopes g) (i : ℕ) : s.SpineMem i 0 := Or.inl rfl

@[simp] theorem vertMem_zero (s : Slopes g) (i : ℕ) : s.VertMem i 0 :=
  Or.inl (spineMem_zero s _)

@[simp] theorem pairMem_zero (s : Slopes g) (i : ℕ) : s.PairMem i 0 := Or.inl rfl

theorem spineMem_le (s : Slopes g) {i k : ℕ} (h : s.SpineMem i k) : k ≤ s.cum i := by
  rcases h with rfl | ⟨-, h⟩
  · exact Nat.zero_le _
  · exact h

/-- The two inclusions that make `VertMem` the union: they are the refinement
receipts of the gluing datum at a spine vertex. -/
theorem vertMem_of_spineMem_left (s : Slopes g) {i k : ℕ}
    (h : s.SpineMem (i - 1) k) : s.VertMem i k := Or.inl h

theorem vertMem_of_spineMem_right (s : Slopes g) {i k : ℕ}
    (h : s.SpineMem i k) : s.VertMem i k := Or.inr h

/-! ### Nesting

An up-step enlarges the block by the brand-new label `cum (i+1)`; a down-step
shrinks it at the other end; a repeat leaves it alone.  Consequently the block
above a spine vertex is literally the larger of its two neighbours. -/

theorem spineMem_mono_up (s : Slopes g) {i k : ℕ}
    (hup : s.slope (i + 1) = s.slope i + 1) (h : s.SpineMem i k) :
    s.SpineMem (i + 1) k := by
  have hc : s.cum (i + 1) = s.cum i + 1 := by rw [cum_succ, if_pos hup]
  rcases h with rfl | ⟨h1, h2⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨by omega, by omega⟩

theorem spineMem_mono_down (s : Slopes g) {i k : ℕ}
    (hdown : s.slope i = s.slope (i + 1) + 1) (h : s.SpineMem (i + 1) k) :
    s.SpineMem i k := by
  have hc : s.cum (i + 1) = s.cum i := by
    rw [cum_succ, if_neg (show ¬ (s.slope (i + 1) = s.slope i + 1) by omega),
      Nat.add_zero]
  rcases h with rfl | ⟨h1, h2⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨by omega, by omega⟩

theorem spineMem_congr_flat (s : Slopes g) {i : ℕ}
    (hflat : s.slope (i + 1) = s.slope i) (k : ℕ) :
    s.SpineMem (i + 1) k ↔ s.SpineMem i k := by
  have hc : s.cum (i + 1) = s.cum i := by
    rw [cum_succ, if_neg (show ¬ (s.slope (i + 1) = s.slope i + 1) by omega),
      Nat.add_zero]
  unfold SpineMem
  rw [hc, hflat]

/-- **The block above a spine vertex is the block above one of its two spine
edges.**  Which one is decided by the sign of `s_i - s_{i-1}`: the `+1` branch
is the up-step, where the forward edge already carries the bigger block. -/
theorem vertMem_iff (s : Slopes g) (i : ℕ) :
    (∀ k, s.VertMem i k ↔ s.SpineMem i k) ∨
      (∀ k, s.VertMem i k ↔ s.SpineMem (i - 1) k) := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · exact Or.inl (fun k => by unfold VertMem; simp)
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hj : (j + 1) - 1 = j := by omega
    rcases slope_trichotomy s j with h | h | h
    · refine Or.inl (fun k => ?_)
      constructor
      · rintro (hk | hk)
        · rw [hj] at hk; exact spineMem_mono_up s h hk
        · exact hk
      · exact fun hk => Or.inr hk
    · refine Or.inr (fun k => ?_)
      constructor
      · rintro (hk | hk)
        · exact hk
        · rw [hj]; exact spineMem_mono_down s h hk
      · intro hk; exact Or.inl hk
    · refine Or.inl (fun k => ?_)
      constructor
      · rintro (hk | hk)
        · rw [hj] at hk; exact (spineMem_congr_flat s h k).mpr hk
        · exact hk
      · exact fun hk => Or.inr hk


/-! ### The two boundary facts the refinement receipts need -/

/-- The counter has not moved at the first spine edge: `slope 0 = slope 1`. -/
theorem cum_one (s : Slopes g) : s.cum 1 = 1 := by
  have h : ¬ (s.slope (0 + 1) = s.slope 0 + 1) := by
    show ¬ (s.slope 1 = s.slope 0 + 1)
    rw [slope_zero]
    omega
  rw [cum_succ, if_neg h, cum_zero, Nat.add_zero]

/-- At the first lollipop the spine block and the bridge pair coincide: both
are `{0, 1}`, because `s_1 = 2` and no label has yet been introduced.  This is
what lets the root `u_1`, which carries no stem, receive the spine edge `h_1`. -/
theorem spineMem_one_iff_pairMem_one (s : Slopes g) (k : ℕ) :
    s.SpineMem 1 k ↔ s.PairMem 1 k := by
  have hc := cum_one s
  have hs := slope_one s
  unfold SpineMem PairMem
  rw [hc, hs]
  omega

/-- **The newest label lies in the block above the spine vertex.**  This is the
receipt over a stem: the bridge pair `{0, cum i}` is contained in the block
`VertMem i` of Part II's `m(B_i)` sheets. -/
theorem vertMem_of_pairMem (s : Slopes g) {i k : ℕ} (h : s.PairMem i k) :
    s.VertMem i k := by
  rcases h with rfl | rfl
  · exact vertMem_zero s i
  · rcases Nat.lt_or_ge 1 (s.slope i) with hbig | hsmall
    · exact Or.inr (Or.inr ⟨by omega, le_refl _⟩)
    · -- the forward slope is one, so the step into `i` was not an up-step
      have hpos := one_le_slope s i
      have hone : s.slope i = 1 := by omega
      have hmax := two_le_max_slope s i
      have hback : 2 ≤ s.slope (i - 1) := by
        rcases Nat.le_total (s.slope (i - 1)) (s.slope i) with hle | hle
        · rw [max_eq_right hle, hone] at hmax; omega
        · rw [max_eq_left hle] at hmax; exact hmax
      have hcum : s.cum (i - 1) = s.cum i := by
        rcases Nat.eq_zero_or_pos i with rfl | hipos
        · rfl
        · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
          have hj : (j + 1) - 1 = j := by omega
          rw [hj, cum_succ,
            if_neg (show ¬ (s.slope (j + 1) = s.slope j + 1) by
              have := one_le_slope s j; omega), Nat.add_zero]
      exact Or.inl (Or.inr ⟨by omega, by omega⟩)

/-! ## 4.  Cardinalities

Every one of the three predicates cuts out `{0}` together with an interval of
labels, so its cardinality inside `Fin (m+2)` is read off by one generic
count. -/

/-- The generic count: `{0} ∪ [a, b]` inside `range (m+2)`. -/
theorem card_range_filter_interval (m a b : ℕ) (ha : 1 ≤ a) (hb : b ≤ m + 1) :
    ((Finset.range (m + 2)).filter (fun k => k = 0 ∨ (a ≤ k ∧ k ≤ b))).card
      = 1 + (b + 1 - a) := by
  classical
  have hset : (Finset.range (m + 2)).filter (fun k => k = 0 ∨ (a ≤ k ∧ k ≤ b))
      = insert 0 (Finset.Ico a (b + 1)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
      Finset.mem_Ico]
    omega
  rw [hset, Finset.card_insert_of_notMem (by simp only [Finset.mem_Ico]; omega),
    Nat.card_Ico]
  omega

/-- The count in the shape the three predicates present it. -/
theorem card_range_filter_of_iff (m a b : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (ha : 1 ≤ a) (hb : b ≤ m + 1)
    (hP : ∀ k, P k ↔ (k = 0 ∨ (a ≤ k ∧ k ≤ b))) :
    ((Finset.range (m + 2)).filter P).card = 1 + (b + 1 - a) := by
  classical
  have hcongr : (Finset.range (m + 2)).filter P
      = (Finset.range (m + 2)).filter (fun k => k = 0 ∨ (a ≤ k ∧ k ≤ b)) := by
    ext k
    simp only [Finset.mem_filter, hP]
  rw [hcongr]
  exact card_range_filter_interval m a b ha hb

/-- **The block above the spine edge `h_i` has `s_i` sheets.** -/
theorem card_spineMem (s : Slopes g) {m : ℕ} (hg : g = 2 * (m + 1)) (i : ℕ) :
    ((Finset.range (m + 2)).filter (s.SpineMem i)).card = s.slope i := by
  have hcum := cum_le s hg i
  have hslope := slope_le_cum_succ s i
  have hpos := one_le_slope s i
  rw [card_range_filter_of_iff m (s.cum i + 2 - s.slope i) (s.cum i) _
    (by omega) (by omega) (fun k => by unfold SpineMem; constructor <;>
      (rintro (rfl | ⟨h1, h2⟩)) <;> first
        | exact Or.inl rfl
        | exact Or.inr ⟨by omega, by omega⟩)]
  omega

/-- **The bridge pair has two sheets.** -/
theorem card_pairMem (s : Slopes g) {m : ℕ} (hg : g = 2 * (m + 1)) (i : ℕ) :
    ((Finset.range (m + 2)).filter (s.PairMem i)).card = 2 := by
  have hcum := cum_le s hg i
  have hpos := one_le_cum s i
  rw [card_range_filter_of_iff m (s.cum i) (s.cum i) _ (by omega) (by omega)
    (fun k => by unfold PairMem; omega)]
  omega

/-- **The block above the spine vertex `p_i` has `max (s_{i-1}, s_i)` sheets**,
which is Part II's `m(B_i)`. -/
theorem card_vertMem (s : Slopes g) {m : ℕ} (hg : g = 2 * (m + 1)) (i : ℕ) :
    ((Finset.range (m + 2)).filter (s.VertMem i)).card
      = max (s.slope (i - 1)) (s.slope i) := by
  classical
  have hcongr : ∀ (j : ℕ), (∀ k, s.VertMem i k ↔ s.SpineMem j k) →
      ((Finset.range (m + 2)).filter (s.VertMem i)).card = s.slope j := by
    intro j hj
    have : (Finset.range (m + 2)).filter (s.VertMem i)
        = (Finset.range (m + 2)).filter (s.SpineMem j) := by
      ext k; simp only [Finset.mem_filter, hj]
    rw [this, card_spineMem s hg j]
  rcases vertMem_iff s i with h | h
  · rw [hcongr i h]
    -- the forward edge carries the bigger block
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [Nat.zero_sub, slope_zero]; omega
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hj : (j + 1) - 1 = j := by omega
      rw [hj]
      -- `h` says the union is the forward block, so the backward slope is smaller
      have hback : s.slope j ≤ s.slope (j + 1) := by
        by_contra hgt
        push Not at hgt
        rcases slope_trichotomy s j with hup | hdown | hflat
        · omega
        · -- a down-step: then the union is the backward block, of strictly larger size
          have hcard := hcongr (j + 1) h
          have hb : (Finset.range (m + 2)).filter (s.VertMem (j + 1))
              = (Finset.range (m + 2)).filter (s.SpineMem j) := by
            ext k
            simp only [Finset.mem_filter, h]
            constructor
            · intro hk; exact ⟨hk.1, spineMem_mono_down s hdown hk.2⟩
            · intro hk
              refine ⟨hk.1, ?_⟩
              rw [← h]
              exact Or.inl (by rw [hj]; exact hk.2)
          rw [hb, card_spineMem s hg j] at hcard
          omega
        · omega
      omega
  · rw [hcongr (i - 1) h]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [Nat.zero_sub]; omega
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hj : (j + 1) - 1 = j := by omega
      rw [hj]
      have hfwd : s.slope (j + 1) ≤ s.slope j := by
        by_contra hgt
        push Not at hgt
        rcases slope_trichotomy s j with hup | hdown | hflat
        · have hcard := hcongr j (by rw [hj] at h; exact h)
          have hb : (Finset.range (m + 2)).filter (s.VertMem (j + 1))
              = (Finset.range (m + 2)).filter (s.SpineMem (j + 1)) := by
            ext k
            simp only [Finset.mem_filter, hj] at h ⊢
            constructor
            · intro hk; exact ⟨hk.1, spineMem_mono_up s hup ((h k).mp hk.2)⟩
            · intro hk
              refine ⟨hk.1, ?_⟩
              exact Or.inr hk.2
          rw [hb, card_spineMem s hg (j + 1)] at hcard
          omega
        · omega
        · omega
      omega

end Slopes

end DraismaVargas.Count
