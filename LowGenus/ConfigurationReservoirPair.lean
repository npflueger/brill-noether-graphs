import LowGenus.ConfigurationMarkedThree

/-!
# A banana pair on two reservoir-backed hubs

This is the second of the two local pictures of Atanasov--Ranganathan's
*second* genus-five family (atlas row `02`); the first is
`ConfigurationReservoirChain`.  Neither is among the eleven pictures of their
Proposition 5.1: the only one of the eleven with two adjacent chips is the
*First*, a single edge, whereas the whole point here is that a paying chip has a
second chip one slot behind it.  The module is therefore named for its geometry,
following the `ConfigurationThreeChain` / `ConfigurationBananaTail` /
`ConfigurationBananaDoubleChip` / `ConfigurationChippedTriangle` precedent.

```
   A1 --alpha-- A --l-- B --beta-- B1        chips at A1, A, B, B1
                |               |
                p               q            X, Y are chip free
                |               |
               (X) ==(m1,m2)== (Y)           and are the two targets
```

**The reservoir.**  A chip vertex `A` whose neighbour `A1` also carries a chip,
at distance `alpha`, can pay **two** units: `A` rises to exactly `alpha`, gains
one unit across the full ramp `A1 - A`, and `A1` pays the single unit its own
chip covers.  Here `A` really does spend both units on one arm, so its arm `p`
runs at **slope two** -- this is `ConfigurationBananaDoubleChip`'s mechanism
with the double chip replaced by a chip plus a reservoir, and the three
slope-two one-edge facts that file proves at a zero endpoint are generalized
below to an arbitrary one.

Write `par = min m1 m2`.  The profile at the target `Y` is the four nested
minima

```
 hB = min alpha beta
 hA = min alpha (min (hB + l) (hB + q))
 hX = min (hB + q) (hA + 2 * p)
 hY = min (hB + q) (hX + par)
```

and the target `X` is read off the mirror (`A <-> B`, `X <-> Y`,
`alpha <-> beta`, `p <-> q`), which on row `02` is literally the core
automorphism `sigma`.  The cap `min (hB + q)` inside `hA` is what makes the
whole picture work: it says `A` may only climb into slope two while the other
hub still has somewhere to climb from, and it is the reason the `A` ledger below
can always find the two units it spends.

**Every height is a nested minimum of slot lengths**, so the profile is
automatically constant across a collapsed slot and one script covers the open
cell and every nonloopy forest face at once.  A collapsed *banana* slot is not
assumed away: `par = 0` merges `X` with `Y`, and that case is absorbed below.

**Chips move inside a contracted class.**  Three allocations are needed, and all
are class-internal, hence invisible to the divisor.  The reservoir chips are
charged to their working chips exactly when the reservoir arms collapse
(`zeroChip alpha`, `zeroChip beta`).  When the slot `A - B` collapses while `B`
sits strictly below `A`'s own arm, `A` and `B` are the same class and `B` lends
`A` its chip (`lendFlat`).  And when the arm `A - X` collapses while `Y` still
sits strictly above `X`, the hub `X` has to pay *both* banana slots with no ramp
of its own; `A` and `X` are then the same class, so `A` hands `X` **two** units
-- the chip it sits on and the one unit its own ledger can spare (`lendHub`,
used with coefficient two).  This is the one place in the row where a class's
chips are not split `0/1` between its vertices.

-/

namespace AtanasovRanganathan.ConfigurationReservoirPair

open Utilities

open Certificate
open Certificate.ExplicitPotential
open ConfigurationFive
open ConfigurationMarkedThree

/-! ## One-edge arithmetic at slope two

`ConfigurationFive`'s ledger bounds every endpoint slope by one in absolute
value, which is right for a divisor with one chip per arm end; the reservoir
allows -- and needs -- slope two.  `ConfigurationBananaDoubleChip` proves these
three facts with the low end pinned at height zero, which is where its double
chip sits; the reservoir's working chip sits at a positive height, so they are
restated here for an arbitrary pair of end heights.  The proofs are the same
two `SubdivisionArithmetic` bridges. -/

/-- An ascending ramp never charges its head, whatever its slope.  Unlike
`ConfigurationFive.headContribution_nonneg` this needs no upper bound on the
rise at all. -/
theorem headContribution_nonneg_of_le {L hu hv : ℕ} (h : hu ≤ hv) :
    0 ≤ headContribution L hu hv := by
  rcases Nat.eq_zero_or_pos L with hL | hL
  · simp [headContribution, hL]
  · simp only [headContribution, if_neg hL.ne']
    have hstep := SubdivisionArithmetic.step_le_upper_of_le_mul
      (L := L) (i := L - 1) ((hu : ℤ) - (hv : ℤ)) 0 hL (by omega)
      (by omega)
    omega

/-- **Slope two.**  An arm whose rise is twice its length delivers two chips at
its head.  This is what the reservoir buys. -/
theorem headContribution_ge_two {L hu hv : ℕ} (hL : 0 < L)
    (h : hu + 2 * L ≤ hv) : 2 ≤ headContribution L hu hv := by
  simp only [headContribution, if_neg hL.ne']
  have hstep := SubdivisionArithmetic.step_le_upper_of_le_mul
    (L := L) (i := L - 1) ((hu : ℤ) - (hv : ℤ)) (-2) hL (by omega)
    (by omega)
  omega

/-- The matching cost: an arm of rise at most twice its length takes at most two
chips from its tail. -/
theorem tailContribution_ge_neg_two {L hu hv : ℕ} (h : hv ≤ hu + 2 * L) :
    -2 ≤ tailContribution L hu hv := by
  rcases Nat.eq_zero_or_pos L with hL | hL
  · simp [tailContribution, hL]
  · simp only [tailContribution, if_neg hL.ne']
    exact SubdivisionArithmetic.lower_le_step_of_mul_le (L := L) (i := 0)
      ((hu : ℤ) - (hv : ℤ)) (-2) hL (by omega)

/-! ## The four nested minima -/

/-- The height at the chip `B`, the one whose arm is read at slope one. -/
def restHeight (alpha beta : ℕ) : ℕ := min alpha beta

/-- The height at the chip `A`, the one that pays two into its arm. -/
def workHeight (alpha beta l q : ℕ) : ℕ :=
  min alpha (min (restHeight alpha beta + l) (restHeight alpha beta + q))

/-- The height at the hub `X`, the end of `A`'s arm. -/
def hubHeight (alpha beta l p q : ℕ) : ℕ :=
  min (restHeight alpha beta + q) (workHeight alpha beta l q + 2 * p)

/-- The height at the target `Y`, the end of `B`'s arm. -/
def targetHeight (alpha beta l p q par : ℕ) : ℕ :=
  min (restHeight alpha beta + q) (hubHeight alpha beta l p q + par)

/-- The chip `B` lends its neighbour `A` when the slot between them has
collapsed and `B` sits strictly below `A`'s own arm. -/
def lendFlat (l alpha hB : ℕ) : ℤ := if l = 0 ∧ hB < alpha then 1 else 0

/-- The chip `A` lends the hub `X` when the arm between them has collapsed and
the hub still has to pay across the banana.  It is used with coefficient
**two**. -/
def lendHub (p hX hY : ℕ) : ℤ := if p = 0 ∧ hX < hY then 1 else 0

theorem lendFlat_nonneg (l alpha hB : ℕ) : 0 ≤ lendFlat l alpha hB := by
  unfold lendFlat; split_ifs <;> norm_num

theorem lendFlat_cases (l alpha hB : ℕ) :
    lendFlat l alpha hB = 0 ∨ lendFlat l alpha hB = 1 := by
  unfold lendFlat; split_ifs <;> simp

theorem eq_of_lendFlat_eq_one {l alpha hB : ℕ} (h : lendFlat l alpha hB = 1) :
    l = 0 ∧ hB < alpha := by
  by_cases hcond : l = 0 ∧ hB < alpha
  · exact hcond
  · rw [lendFlat, if_neg hcond] at h
    exact absurd h (by norm_num)

theorem lendFlat_eq_one {l alpha hB : ℕ} (hl : l = 0) (hlt : hB < alpha) :
    lendFlat l alpha hB = 1 := by
  unfold lendFlat; rw [if_pos ⟨hl, hlt⟩]

theorem lendHub_nonneg (p hX hY : ℕ) : 0 ≤ lendHub p hX hY := by
  unfold lendHub; split_ifs <;> norm_num

theorem lendHub_cases (p hX hY : ℕ) :
    lendHub p hX hY = 0 ∨ lendHub p hX hY = 1 := by
  unfold lendHub; split_ifs <;> simp

theorem eq_of_lendHub_eq_one {p hX hY : ℕ} (h : lendHub p hX hY = 1) :
    p = 0 ∧ hX < hY := by
  by_cases hcond : p = 0 ∧ hX < hY
  · exact hcond
  · rw [lendHub, if_neg hcond] at h
    exact absurd h (by norm_num)

theorem lendHub_eq_one {p hX hY : ℕ} (hp : p = 0) (hlt : hX < hY) :
    lendHub p hX hY = 1 := by
  unfold lendHub; rw [if_pos ⟨hp, hlt⟩]

theorem lendHub_eq_zero_of_eq {p hX hY : ℕ} (h : hX = hY) :
    lendHub p hX hY = 0 := by
  unfold lendHub; rw [if_neg (by omega)]

/-! ## The arithmetic of the four minima

Everything the residual statements need about the profile is this one bundle of
inequalities and "which argument is attained" disjunctions; each consumer then
works with plain naturals and `omega`. -/

theorem bounds {alpha beta l p q par hB hA hX hY : ℕ}
    (hhB : hB = restHeight alpha beta)
    (hhA : hA = workHeight alpha beta l q)
    (hhX : hX = hubHeight alpha beta l p q)
    (hhY : hY = targetHeight alpha beta l p q par) :
    (hB ≤ alpha ∧ hB ≤ beta) ∧ (hB = alpha ∨ hB = beta)
      ∧ (hA ≤ alpha ∧ hA ≤ hB + l ∧ hA ≤ hB + q ∧ hB ≤ hA)
      ∧ (hA = alpha ∨ hA = hB + l ∨ hA = hB + q)
      ∧ (hX ≤ hB + q ∧ hX ≤ hA + 2 * p ∧ hA ≤ hX)
      ∧ (hX = hB + q ∨ hX = hA + 2 * p)
      ∧ (hY ≤ hB + q ∧ hY ≤ hX + par ∧ hX ≤ hY)
      ∧ (hY = hB + q ∨ hY = hX + par) := by
  subst hhB hhA hhX hhY
  simp only [targetHeight, hubHeight, workHeight, restHeight]
  omega

/-! ## Who owns the delivered chip -/

/-- The target delivers its own chip: its own arm goes full, or the banana
does. -/
def Delivers (q par hB hX hY : ℕ) : Prop :=
  (0 < q ∧ hY = hB + q) ∨ (0 < par ∧ hY = hX + par)

instance (q par hB hX hY : ℕ) : Decidable (Delivers q par hB hX hY) := by
  unfold Delivers; infer_instance

/-- When the target does not deliver, either its arm has collapsed -- putting
the chip `B` in its class -- or the banana has, and the hub is then sitting at
the top of a slope-two ramp. -/
theorem cases_of_not_delivers {alpha beta l p q par hB hA hX hY : ℕ}
    (hhB : hB = restHeight alpha beta)
    (hhA : hA = workHeight alpha beta l q)
    (hhX : hX = hubHeight alpha beta l p q)
    (hhY : hY = targetHeight alpha beta l p q par)
    (h : ¬ Delivers q par hB hX hY) :
    q = 0 ∨ (par = 0 ∧ hX = hY ∧ hX = hA + 2 * p) := by
  have hb := bounds hhB hhA hhX hhY
  unfold Delivers at h
  omega

/-! ## The five residual statements

The reservoir arms, the slot `A - B` and the two banana slots may each be read
from either end, so they are read through a `PairLedger`, exactly as in
`ConfigurationChippedTriangle`; `S.tail L x y` is the contribution at the end
carrying height `x`.  The two hub arms `p` and `q` need no ledger: on row `02`
both readings traverse them in the same direction, and the slope-two facts above
are stated for `tailContribution` / `headContribution` directly. -/

/-- **The two units `A` can always find.**  Whenever the working chip is not
already capped by the other hub's arm, its own arm, the slot to `B`, or the
lending of `B`'s chip supplies one unit on top of its own. -/
theorem work_supply (SAl SL : PairLedger)
    {alpha beta l p q par hB hA hX hY : ℕ}
    (hhB : hB = restHeight alpha beta)
    (hhA : hA = workHeight alpha beta l q)
    (hhX : hX = hubHeight alpha beta l p q)
    (hhY : hY = targetHeight alpha beta l p q par)
    (hlt : hA < hB + q) :
    1 ≤ zeroChip alpha + lendFlat l alpha hB +
      (SAl.tail alpha hA 0 + SL.tail l hA hB) := by
  have hb := bounds hhB hhA hhX hhY
  have ht1 : 0 ≤ SAl.tail alpha hA 0 := SAl.tail_nonneg (Nat.zero_le _) (by omega)
  have ht2 : 0 ≤ SL.tail l hA hB := SL.tail_nonneg (by omega) (by omega)
  have hZ : (0 : ℤ) ≤ zeroChip alpha := zeroChip_nonneg alpha
  have hF : (0 : ℤ) ≤ lendFlat l alpha hB := lendFlat_nonneg l alpha hB
  by_cases hAal : hA = alpha
  · have hs : 1 ≤ zeroChip alpha + SAl.tail alpha hA 0 := by
      rw [hAal]; exact SAl.zeroChip_add_tail_full alpha
    omega
  · by_cases hlpos : 0 < l
    · have hone : SL.tail l hA hB = 1 :=
        SL.tail_eq_one_of_full hlpos (by omega)
      omega
    · have hone : lendFlat l alpha hB = 1 :=
        lendFlat_eq_one (by omega) (by omega)
      omega

/-- **The working chip.**  It balances because its own arm runs at slope two
exactly when the reservoir behind it has fired. -/
theorem pairWork_nonneg (SAl SL : PairLedger)
    {alpha beta l p q par hB hA hX hY : ℕ}
    (hhB : hB = restHeight alpha beta)
    (hhA : hA = workHeight alpha beta l q)
    (hhX : hX = hubHeight alpha beta l p q)
    (hhY : hY = targetHeight alpha beta l p q par) :
    0 ≤ 1 + zeroChip alpha + lendFlat l alpha hB - 2 * lendHub p hX hY +
      (SAl.tail alpha hA 0 + SL.tail l hA hB + tailContribution p hA hX) := by
  have hb := bounds hhB hhA hhX hhY
  have ht1 : 0 ≤ SAl.tail alpha hA 0 := SAl.tail_nonneg (Nat.zero_le _) (by omega)
  have ht2 : 0 ≤ SL.tail l hA hB := SL.tail_nonneg (by omega) (by omega)
  have hZ : (0 : ℤ) ≤ zeroChip alpha := zeroChip_nonneg alpha
  have hF : (0 : ℤ) ≤ lendFlat l alpha hB := lendFlat_nonneg l alpha hB
  rcases lendHub_cases p hX hY with hHub | hHub
  · rw [hHub]
    by_cases hnear : hX ≤ hA + p
    · have ht3 : -1 ≤ tailContribution p hA hX :=
        tailContribution_ge_neg_one (by omega) (by omega)
      omega
    · have ht3 : -2 ≤ tailContribution p hA hX :=
        tailContribution_ge_neg_two (by omega)
      have hsup := work_supply SAl SL hhB hhA hhX hhY (by omega)
      omega
  · obtain ⟨hp0, hlt⟩ := eq_of_lendHub_eq_one hHub
    have hXA : hX = hA := by omega
    have ht3 : tailContribution p hA hX = 0 := by
      rw [hXA]; exact tailContribution_same p hA
    have hsup := work_supply SAl SL hhB hhA hhX hhY (by omega)
    rw [hHub, ht3]
    omega

/-- The same vertex, when the fallback owner lives here: the arm to the hub has
collapsed and the banana carries no rise, so the working chip is in the target's
class and its own arm costs it nothing. -/
theorem pairWork_ge_one (SAl SL : PairLedger)
    {alpha beta l p q par hB hA hX hY : ℕ}
    (hhB : hB = restHeight alpha beta)
    (hhA : hA = workHeight alpha beta l q)
    (hhX : hX = hubHeight alpha beta l p q)
    (hhY : hY = targetHeight alpha beta l p q par)
    (hp : p = 0) (hXY : hX = hY) :
    1 ≤ 1 + zeroChip alpha + lendFlat l alpha hB - 2 * lendHub p hX hY +
      (SAl.tail alpha hA 0 + SL.tail l hA hB + tailContribution p hA hX) := by
  have hb := bounds hhB hhA hhX hhY
  have ht1 : 0 ≤ SAl.tail alpha hA 0 := SAl.tail_nonneg (Nat.zero_le _) (by omega)
  have ht2 : 0 ≤ SL.tail l hA hB := SL.tail_nonneg (by omega) (by omega)
  have hZ : (0 : ℤ) ≤ zeroChip alpha := zeroChip_nonneg alpha
  have hF : (0 : ℤ) ≤ lendFlat l alpha hB := lendFlat_nonneg l alpha hB
  have hXA : hX = hA := by omega
  have ht3 : tailContribution p hA hX = 0 := by
    rw [hXA]; exact tailContribution_same p hA
  have hHub : lendHub p hX hY = 0 := lendHub_eq_zero_of_eq hXY
  rw [hHub, ht3]
  omega

/-- **The resting chip.**  It pays across the slot to `A` and into its own arm
only when it is sitting on a full reservoir ramp. -/
theorem pairRest_nonneg (SL SBe : PairLedger)
    {alpha beta l p q par hB hA hX hY : ℕ}
    (hhB : hB = restHeight alpha beta)
    (hhA : hA = workHeight alpha beta l q)
    (hhX : hX = hubHeight alpha beta l p q)
    (hhY : hY = targetHeight alpha beta l p q par) :
    0 ≤ 1 + zeroChip beta - lendFlat l alpha hB +
      (SL.tail l hB hA + SBe.tail beta hB 0 + tailContribution q hB hY) := by
  have hb := bounds hhB hhA hhX hhY
  have hu1 : -1 ≤ SL.tail l hB hA := SL.tail_ge_neg_one (by omega) (by omega)
  have hu2 : 0 ≤ SBe.tail beta hB 0 := SBe.tail_nonneg (Nat.zero_le _) (by omega)
  have hu3 : -1 ≤ tailContribution q hB hY :=
    tailContribution_ge_neg_one (by omega) (by omega)
  have hZ : (0 : ℤ) ≤ zeroChip beta := zeroChip_nonneg beta
  by_cases hEq : hA = hB
  · have h0 : SL.tail l hB hA = 0 := by rw [hEq]; exact SL.tail_same l hB
    rcases lendFlat_cases l alpha hB with hFl | hFl
    · rw [hFl, h0]; omega
    · obtain ⟨hl0, hBlt⟩ := eq_of_lendFlat_eq_one hFl
      have hs : 1 ≤ zeroChip beta + SBe.tail beta hB 0 := by
        rw [show hB = beta by omega]; exact SBe.zeroChip_add_tail_full beta
      rw [hFl, h0]; omega
  · have hFl : lendFlat l alpha hB = 0 := by
      rcases lendFlat_cases l alpha hB with h | h
      · exact h
      · obtain ⟨hl0, -⟩ := eq_of_lendFlat_eq_one h
        omega
    have hs : 1 ≤ zeroChip beta + SBe.tail beta hB 0 := by
      rw [show hB = beta by omega]; exact SBe.zeroChip_add_tail_full beta
    rw [hFl]; omega

/-- The same vertex, when the fallback owner lives here: the target's arm has
collapsed, so this chip is in the target's class and nothing in the picture
rises at all. -/
theorem pairRest_ge_one (SL SBe : PairLedger)
    {alpha beta l p q par hB hA hX hY : ℕ}
    (hhB : hB = restHeight alpha beta)
    (hhA : hA = workHeight alpha beta l q)
    (hhX : hX = hubHeight alpha beta l p q)
    (hhY : hY = targetHeight alpha beta l p q par)
    (hq : q = 0) :
    1 ≤ 1 + zeroChip beta - lendFlat l alpha hB +
      (SL.tail l hB hA + SBe.tail beta hB 0 + tailContribution q hB hY) := by
  have hb := bounds hhB hhA hhX hhY
  have hu2 : 0 ≤ SBe.tail beta hB 0 := SBe.tail_nonneg (Nat.zero_le _) (by omega)
  have hZ : (0 : ℤ) ≤ zeroChip beta := zeroChip_nonneg beta
  have hEq : hA = hB := by omega
  have hYB : hY = hB := by omega
  have h0 : SL.tail l hB hA = 0 := by rw [hEq]; exact SL.tail_same l hB
  have h1 : tailContribution q hB hY = 0 := by
    rw [hYB]; exact tailContribution_same q hB
  rcases lendFlat_cases l alpha hB with hFl | hFl
  · rw [hFl, h0, h1]; omega
  · obtain ⟨hl0, hBlt⟩ := eq_of_lendFlat_eq_one hFl
    have hs : 1 ≤ zeroChip beta + SBe.tail beta hB 0 := by
      rw [show hB = beta by omega]; exact SBe.zeroChip_add_tail_full beta
    rw [hFl, h0, h1]; omega

/-- **The hub.**  It pays both banana slots at once, and it can, because
whenever the banana rises the hub is at the top of a full slope-two ramp -- or
that ramp has collapsed and `A` hands it two units directly. -/
theorem pairHub_nonneg (SM : PairLedger)
    {alpha beta l p q par m1 m2 hB hA hX hY : ℕ}
    (hpar : par = min m1 m2)
    (hhB : hB = restHeight alpha beta)
    (hhA : hA = workHeight alpha beta l q)
    (hhX : hX = hubHeight alpha beta l p q)
    (hhY : hY = targetHeight alpha beta l p q par) :
    0 ≤ 2 * lendHub p hX hY +
      (headContribution p hA hX + SM.tail m1 hX hY + SM.tail m2 hX hY) := by
  have hb := bounds hhB hhA hhX hhY
  have hw0 : 0 ≤ headContribution p hA hX := headContribution_nonneg_of_le (by omega)
  have hw1 : -1 ≤ SM.tail m1 hX hY := SM.tail_ge_neg_one (by omega) (by omega)
  have hw2 : -1 ≤ SM.tail m2 hX hY := SM.tail_ge_neg_one (by omega) (by omega)
  have hH : (0 : ℤ) ≤ lendHub p hX hY := lendHub_nonneg p hX hY
  by_cases hEq : hX = hY
  · have h1 : SM.tail m1 hX hY = 0 := by rw [hEq]; exact SM.tail_same m1 hY
    have h2 : SM.tail m2 hX hY = 0 := by rw [hEq]; exact SM.tail_same m2 hY
    omega
  · have hlt : hX < hY := by omega
    by_cases hp : 0 < p
    · have htwo : 2 ≤ headContribution p hA hX :=
        headContribution_ge_two hp (by omega)
      omega
    · have hone : lendHub p hX hY = 1 := lendHub_eq_one (by omega) hlt
      rw [hone]; omega

/-- The same vertex, when the fallback owner lives here: the banana carries no
rise, so the hub is in the target's class, and its slope-two ramp is full. -/
theorem pairHub_ge_one (SM : PairLedger)
    {alpha beta l p q par m1 m2 hB hA hX hY : ℕ}
    (_hpar : par = min m1 m2)
    (hhB : hB = restHeight alpha beta)
    (hhA : hA = workHeight alpha beta l q)
    (hhX : hX = hubHeight alpha beta l p q)
    (hhY : hY = targetHeight alpha beta l p q par)
    (hp : 0 < p) (hfull : hX = hA + 2 * p) (hXY : hX = hY) :
    1 ≤ 2 * lendHub p hX hY +
      (headContribution p hA hX + SM.tail m1 hX hY + SM.tail m2 hX hY) := by
  have hb := bounds hhB hhA hhX hhY
  have htwo : 2 ≤ headContribution p hA hX := headContribution_ge_two hp (by omega)
  have hH : (0 : ℤ) ≤ lendHub p hX hY := lendHub_nonneg p hX hY
  have h1 : SM.tail m1 hX hY = 0 := by rw [hXY]; exact SM.tail_same m1 hY
  have h2 : SM.tail m2 hX hY = 0 := by rw [hXY]; exact SM.tail_same m2 hY
  omega

/-- **The target.**  Every slot at it rises towards it, so it never goes
negative. -/
theorem pairTarget_nonneg (SM : PairLedger)
    {alpha beta l p q par m1 m2 hB hA hX hY : ℕ}
    (hpar : par = min m1 m2)
    (hhB : hB = restHeight alpha beta)
    (hhA : hA = workHeight alpha beta l q)
    (hhX : hX = hubHeight alpha beta l p q)
    (hhY : hY = targetHeight alpha beta l p q par) :
    0 ≤ headContribution q hB hY + SM.tail m1 hY hX + SM.tail m2 hY hX := by
  have hb := bounds hhB hhA hhX hhY
  have hw0 : 0 ≤ headContribution q hB hY := headContribution_nonneg_of_le (by omega)
  have hw1 : 0 ≤ SM.tail m1 hY hX := SM.tail_nonneg (by omega) (by omega)
  have hw2 : 0 ≤ SM.tail m2 hY hX := SM.tail_nonneg (by omega) (by omega)
  omega

/-- **The target delivers.**  One of the two arguments of `hY` is attained at a
positive slot, and that slot is full. -/
theorem pairTarget_ge_one (SM : PairLedger)
    {alpha beta l p q par m1 m2 hB hA hX hY : ℕ}
    (hpar : par = min m1 m2)
    (hhB : hB = restHeight alpha beta)
    (hhA : hA = workHeight alpha beta l q)
    (hhX : hX = hubHeight alpha beta l p q)
    (hhY : hY = targetHeight alpha beta l p q par)
    (hDel : Delivers q par hB hX hY) :
    1 ≤ headContribution q hB hY + SM.tail m1 hY hX + SM.tail m2 hY hX := by
  have hb := bounds hhB hhA hhX hhY
  have hw0 : 0 ≤ headContribution q hB hY := headContribution_nonneg_of_le (by omega)
  have hw1 : 0 ≤ SM.tail m1 hY hX := SM.tail_nonneg (by omega) (by omega)
  have hw2 : 0 ≤ SM.tail m2 hY hX := SM.tail_nonneg (by omega) (by omega)
  rcases hDel with ⟨hpos, hYeq⟩ | ⟨hpos, hYeq⟩
  · have h0 : headContribution q hB hY = 1 :=
      headContribution_eq_one_of_full hpos (by omega)
    omega
  · rcases Nat.le_total m1 m2 with h12 | h12
    · have h1 : SM.tail m1 hY hX = 1 :=
        SM.tail_eq_one_of_full (by omega) (by omega)
      omega
    · have h2 : SM.tail m2 hY hX = 1 :=
        SM.tail_eq_one_of_full (by omega) (by omega)
      omega

end AtanasovRanganathan.ConfigurationReservoirPair
