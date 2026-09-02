import LowGenus.ConfigurationMarkedThree

/-!
# Two bananas in series, both backed by a reservoir

This is one of the two local pictures of Atanasov--Ranganathan's *second*
genus-five family (atlas row `02`).  It is **not** one of the eleven pictures of
their Proposition 5.1: the only one of the eleven with two adjacent chips is the
*First*, a single edge, whereas the whole point here is that a paying chip has a
second chip one slot behind it.  The module is therefore named for its geometry,
following the `ConfigurationThreeChain` / `ConfigurationBananaTail` /
`ConfigurationBananaDoubleChip` / `ConfigurationChippedTriangle` precedent.

```
   A1 --alpha-- A ==(n1,n2)== P --s-- Q ==(m1,m2)== B --beta-- B1

   chips at A1, A, B, B1;  P and Q are chip free and are the two targets
```

**The reservoir.**  A chip vertex `A` whose neighbour `A1` also carries a chip,
at distance `alpha`, can pay **two** units: `A` rises to exactly `alpha`, gains
one unit across the full ramp `A1 - A`, and `A1` pays the single unit its own
chip covers.  Here `A` needs that only to cover both slots of the banana
`A == P` at once, so its own arm never runs at slope two -- unlike
`ConfigurationBananaDoubleChip`, this picture needs no new one-edge arithmetic.

Write `par3 = min n1 n2` and `par2 = min m1 m2`.  The profile at the target `Q`
is the four nested minima

```
 hQ = min (beta + par2) (alpha + par3 + s)
 hP = min (alpha + par3) hQ
 hA = min alpha hP
 hB = min beta hQ
```

and the target `P` is read off the mirror (`A <-> B`, `P <-> Q`,
`alpha <-> beta`, `(n1,n2) <-> (m1,m2)`), which on row `02` is literally the
core automorphism `sigma`.  The two ways `Q` gets its chip are the two
arguments of `hQ`: the near banana goes full and `B` refills along `beta`, or
the middle slot `s` goes full and `P` refills across its own banana.

**Every height is a nested minimum of slot lengths**, so the profile is
automatically constant across a collapsed slot and one script covers the open
cell and every nonloopy forest face at once.  A collapsed *banana* slot is not
assumed away: `par3 = 0` merges `A` with `P` and `par2 = 0` merges `B` with `Q`,
and both are absorbed below.

**Chips move inside a contracted class.**  Two allocations are needed, and both
are class-internal, hence invisible to the divisor.  The reservoir chip is
charged to the working chip exactly when the reservoir arm collapses (`zeroChip
alpha`, `zeroChip beta`).  And when the near banana collapses (`par3 = 0`) while
`Q` still sits strictly above `P`, the partner `P` has to pay one unit across
`s` that neither banana slot can supply; `A` and `P` are then the same
contracted class, so `A` lends `P` the chip it is sitting on.  That transfer is
`lend`.

-/

namespace AtanasovRanganathan.ConfigurationReservoirChain

open Utilities

open Certificate
open Certificate.ExplicitPotential
open ConfigurationFive
open ConfigurationMarkedThree

/-! ## The four nested minima -/

/-- The height at the target `Q`. -/
def targetHeight (alpha beta s par2 par3 : ℕ) : ℕ :=
  min (beta + par2) (alpha + par3 + s)

/-- The height at the partner `P`. -/
def partnerHeight (alpha beta s par2 par3 : ℕ) : ℕ :=
  min (alpha + par3) (targetHeight alpha beta s par2 par3)

/-- The height at the chip `A`, which sits on the partner's banana. -/
def nearHeight (alpha beta s par2 par3 : ℕ) : ℕ :=
  min alpha (partnerHeight alpha beta s par2 par3)

/-- The height at the chip `B`, which sits on the target's banana. -/
def farHeight (alpha beta s par2 par3 : ℕ) : ℕ :=
  min beta (targetHeight alpha beta s par2 par3)

/-- The chip `A` lends its partner `P` when the banana between them has
collapsed and `P` still has to pay across the middle slot. -/
def lend (par3 hP hQ : ℕ) : ℤ := if par3 = 0 ∧ hP < hQ then 1 else 0

theorem lend_nonneg (par3 hP hQ : ℕ) : 0 ≤ lend par3 hP hQ := by
  unfold lend; split_ifs <;> norm_num

theorem lend_cases (par3 hP hQ : ℕ) :
    lend par3 hP hQ = 0 ∨ lend par3 hP hQ = 1 := by
  unfold lend; split_ifs <;> simp

theorem eq_of_lend_eq_one {par3 hP hQ : ℕ} (h : lend par3 hP hQ = 1) :
    par3 = 0 ∧ hP < hQ := by
  by_cases hcond : par3 = 0 ∧ hP < hQ
  · exact hcond
  · rw [lend, if_neg hcond] at h
    exact absurd h (by norm_num)

theorem lend_eq_one {par3 hP hQ : ℕ} (hz : par3 = 0) (hlt : hP < hQ) :
    lend par3 hP hQ = 1 := by
  unfold lend; rw [if_pos ⟨hz, hlt⟩]

theorem lend_eq_zero_of_eq {par3 hP hQ : ℕ} (h : hP = hQ) :
    lend par3 hP hQ = 0 := by
  unfold lend; rw [if_neg (by omega)]

/-! ## The arithmetic of the four minima

Everything the residual statements need about the profile is this one bundle of
inequalities and "which argument is attained" disjunctions; each consumer then
works with plain naturals and `omega`. -/

theorem bounds {alpha beta s par2 par3 hQ hP hA hB : ℕ}
    (hhQ : hQ = targetHeight alpha beta s par2 par3)
    (hhP : hP = partnerHeight alpha beta s par2 par3)
    (hhA : hA = nearHeight alpha beta s par2 par3)
    (hhB : hB = farHeight alpha beta s par2 par3) :
    (hQ ≤ beta + par2 ∧ hQ ≤ alpha + par3 + s)
      ∧ (hQ = beta + par2 ∨ hQ = alpha + par3 + s)
      ∧ (hP ≤ alpha + par3 ∧ hP ≤ hQ) ∧ (hP = alpha + par3 ∨ hP = hQ)
      ∧ (hA ≤ alpha ∧ hA ≤ hP) ∧ (hA = alpha ∨ hA = hP)
      ∧ (hB ≤ beta ∧ hB ≤ hQ) ∧ (hB = beta ∨ hB = hQ)
      ∧ (hA ≤ hP ∧ hP ≤ hQ ∧ hB ≤ hQ
          ∧ hP ≤ hA + par3 ∧ hQ ≤ hB + par2 ∧ hQ ≤ hP + s) := by
  subst hhQ hhP hhA hhB
  simp only [farHeight, nearHeight, partnerHeight, targetHeight]
  omega

/-! ## Who owns the delivered chip -/

/-- The target delivers its own chip: its own banana goes full, or the middle
slot does. -/
def Delivers (alpha beta s par2 par3 hQ : ℕ) : Prop :=
  (0 < par2 ∧ hQ = beta + par2) ∨ (0 < s ∧ hQ = alpha + par3 + s)

instance (alpha beta s par2 par3 hQ : ℕ) :
    Decidable (Delivers alpha beta s par2 par3 hQ) := by
  unfold Delivers; infer_instance

/-- When the target does not deliver, one of the two slot groups at it has
collapsed -- which is what puts the fallback owner in the target's class. -/
theorem cases_of_not_delivers {alpha beta s par2 par3 hQ hP hA hB : ℕ}
    (hhQ : hQ = targetHeight alpha beta s par2 par3)
    (hhP : hP = partnerHeight alpha beta s par2 par3)
    (hhA : hA = nearHeight alpha beta s par2 par3)
    (hhB : hB = farHeight alpha beta s par2 par3)
    (h : ¬ Delivers alpha beta s par2 par3 hQ) :
    (par2 = 0 ∧ hQ = beta) ∨ (s = 0 ∧ hQ = alpha + par3) := by
  have hb := bounds hhQ hhP hhA hhB
  unfold Delivers at h
  omega

/-! ## The five residual statements

Each of the seven slots may be read from either end, so all of them are read
through a `PairLedger`, exactly as in `ConfigurationChippedTriangle`.
`S.tail L x y` is the contribution at the end carrying height `x`. -/

/-- **The chip on the partner's banana.**  Its reservoir fires exactly when the
banana charges it twice. -/
theorem chainNear_nonneg (SA SN : PairLedger)
    {alpha beta s n1 n2 par2 par3 hQ hP hA hB : ℕ}
    (hpar3 : par3 = min n1 n2)
    (hhQ : hQ = targetHeight alpha beta s par2 par3)
    (hhP : hP = partnerHeight alpha beta s par2 par3)
    (hhA : hA = nearHeight alpha beta s par2 par3)
    (hhB : hB = farHeight alpha beta s par2 par3) :
    0 ≤ 1 + zeroChip alpha - lend par3 hP hQ +
      (SA.tail alpha hA 0 + SN.tail n1 hA hP + SN.tail n2 hA hP) := by
  have hb := bounds hhQ hhP hhA hhB
  have hA0 : 0 ≤ SA.tail alpha hA 0 := SA.tail_nonneg (Nat.zero_le _) (by omega)
  have hN1 : -1 ≤ SN.tail n1 hA hP := SN.tail_ge_neg_one (by omega) (by omega)
  have hN2 : -1 ≤ SN.tail n2 hA hP := SN.tail_ge_neg_one (by omega) (by omega)
  have hZ : (0 : ℤ) ≤ zeroChip alpha := zeroChip_nonneg alpha
  have hL : (0 : ℤ) ≤ lend par3 hP hQ := lend_nonneg par3 hP hQ
  by_cases hEq : hA = hP
  · have h1 : SN.tail n1 hA hP = 0 := by rw [hEq]; exact SN.tail_same n1 hP
    have h2 : SN.tail n2 hA hP = 0 := by rw [hEq]; exact SN.tail_same n2 hP
    rcases lend_cases par3 hP hQ with hcase | hcase <;> rw [hcase] <;> omega
  · have hLzero : lend par3 hP hQ = 0 := by
      rcases lend_cases par3 hP hQ with hz | ho
      · exact hz
      · obtain ⟨hp0, -⟩ := eq_of_lend_eq_one ho
        omega
    have hFull : hA = alpha := by omega
    have hsupply : 1 ≤ zeroChip alpha + SA.tail alpha hA 0 := by
      rw [hFull]; exact SA.zeroChip_add_tail_full alpha
    rw [hLzero]
    omega

/-- The same vertex, when the fallback owner lives here: both the banana to the
partner and the middle slot have collapsed, so this chip is in the target's
class. -/
theorem chainNear_ge_one (SA SN : PairLedger)
    {alpha beta s n1 n2 par2 par3 hQ hP hA hB : ℕ}
    (hpar3 : par3 = min n1 n2)
    (hhQ : hQ = targetHeight alpha beta s par2 par3)
    (hhP : hP = partnerHeight alpha beta s par2 par3)
    (hhA : hA = nearHeight alpha beta s par2 par3)
    (hhB : hB = farHeight alpha beta s par2 par3)
    (hzero : par3 = 0) (hs : s = 0) :
    1 ≤ 1 + zeroChip alpha - lend par3 hP hQ +
      (SA.tail alpha hA 0 + SN.tail n1 hA hP + SN.tail n2 hA hP) := by
  have hb := bounds hhQ hhP hhA hhB
  have hA0 : 0 ≤ SA.tail alpha hA 0 := SA.tail_nonneg (Nat.zero_le _) (by omega)
  have hZ : (0 : ℤ) ≤ zeroChip alpha := zeroChip_nonneg alpha
  have hEq : hA = hP := by omega
  have h1 : SN.tail n1 hA hP = 0 := by rw [hEq]; exact SN.tail_same n1 hP
  have h2 : SN.tail n2 hA hP = 0 := by rw [hEq]; exact SN.tail_same n2 hP
  have hLzero : lend par3 hP hQ = 0 := lend_eq_zero_of_eq (by omega)
  rw [h1, h2, hLzero]
  omega

/-- **The partner.**  It pays across the middle slot only when its own banana is
full, or when `A` lends it the chip it sits on. -/
theorem chainPartner_nonneg (SN SS : PairLedger)
    {alpha beta s n1 n2 par2 par3 hQ hP hA hB : ℕ}
    (hpar3 : par3 = min n1 n2)
    (hhQ : hQ = targetHeight alpha beta s par2 par3)
    (hhP : hP = partnerHeight alpha beta s par2 par3)
    (hhA : hA = nearHeight alpha beta s par2 par3)
    (hhB : hB = farHeight alpha beta s par2 par3) :
    0 ≤ lend par3 hP hQ +
      (SN.tail n1 hP hA + SN.tail n2 hP hA + SS.tail s hP hQ) := by
  have hb := bounds hhQ hhP hhA hhB
  have hN1 : 0 ≤ SN.tail n1 hP hA := SN.tail_nonneg (by omega) (by omega)
  have hN2 : 0 ≤ SN.tail n2 hP hA := SN.tail_nonneg (by omega) (by omega)
  have hS : -1 ≤ SS.tail s hP hQ := SS.tail_ge_neg_one (by omega) (by omega)
  have hL : (0 : ℤ) ≤ lend par3 hP hQ := lend_nonneg par3 hP hQ
  by_cases hEq : hP = hQ
  · have h0 : SS.tail s hP hQ = 0 := by rw [hEq]; exact SS.tail_same s hQ
    omega
  · have hlt : hP < hQ := by omega
    by_cases hpos : 0 < par3
    · rcases Nat.le_total n1 n2 with h12 | h12
      · have h1 : SN.tail n1 hP hA = 1 :=
          SN.tail_eq_one_of_full (by omega) (by omega)
        omega
      · have h2 : SN.tail n2 hP hA = 1 :=
          SN.tail_eq_one_of_full (by omega) (by omega)
        omega
    · have hone : lend par3 hP hQ = 1 := lend_eq_one (by omega) hlt
      omega

/-- The same vertex, when the fallback owner lives here: the middle slot has
collapsed, so the partner is in the target's class, and its own banana is what
delivers. -/
theorem chainPartner_ge_one (SN SS : PairLedger)
    {alpha beta s n1 n2 par2 par3 hQ hP hA hB : ℕ}
    (hpar3 : par3 = min n1 n2)
    (hhQ : hQ = targetHeight alpha beta s par2 par3)
    (hhP : hP = partnerHeight alpha beta s par2 par3)
    (hhA : hA = nearHeight alpha beta s par2 par3)
    (hhB : hB = farHeight alpha beta s par2 par3)
    (hs : s = 0) (hQeq : hQ = alpha + par3) (hpos : 0 < par3) :
    1 ≤ lend par3 hP hQ +
      (SN.tail n1 hP hA + SN.tail n2 hP hA + SS.tail s hP hQ) := by
  have hb := bounds hhQ hhP hhA hhB
  have hN1 : 0 ≤ SN.tail n1 hP hA := SN.tail_nonneg (by omega) (by omega)
  have hN2 : 0 ≤ SN.tail n2 hP hA := SN.tail_nonneg (by omega) (by omega)
  have hL : (0 : ℤ) ≤ lend par3 hP hQ := lend_nonneg par3 hP hQ
  have hEq : hP = hQ := by omega
  have h0 : SS.tail s hP hQ = 0 := by rw [hEq]; exact SS.tail_same s hQ
  rcases Nat.le_total n1 n2 with h12 | h12
  · have h1 : SN.tail n1 hP hA = 1 :=
      SN.tail_eq_one_of_full (by omega) (by omega)
    omega
  · have h2 : SN.tail n2 hP hA = 1 :=
      SN.tail_eq_one_of_full (by omega) (by omega)
    omega

/-- **The chip on the target's banana.**  The same reservoir argument as
`chainNear_nonneg`, with no lending: the target never needs this chip's
rescue. -/
theorem chainFar_nonneg (SB SM : PairLedger)
    {alpha beta s m1 m2 par2 par3 hQ hP hA hB : ℕ}
    (hpar2 : par2 = min m1 m2)
    (hhQ : hQ = targetHeight alpha beta s par2 par3)
    (hhP : hP = partnerHeight alpha beta s par2 par3)
    (hhA : hA = nearHeight alpha beta s par2 par3)
    (hhB : hB = farHeight alpha beta s par2 par3) :
    0 ≤ 1 + zeroChip beta +
      (SB.tail beta hB 0 + SM.tail m1 hB hQ + SM.tail m2 hB hQ) := by
  have hb := bounds hhQ hhP hhA hhB
  have hB0 : 0 ≤ SB.tail beta hB 0 := SB.tail_nonneg (Nat.zero_le _) (by omega)
  have hM1 : -1 ≤ SM.tail m1 hB hQ := SM.tail_ge_neg_one (by omega) (by omega)
  have hM2 : -1 ≤ SM.tail m2 hB hQ := SM.tail_ge_neg_one (by omega) (by omega)
  have hZ : (0 : ℤ) ≤ zeroChip beta := zeroChip_nonneg beta
  by_cases hEq : hB = hQ
  · have h1 : SM.tail m1 hB hQ = 0 := by rw [hEq]; exact SM.tail_same m1 hQ
    have h2 : SM.tail m2 hB hQ = 0 := by rw [hEq]; exact SM.tail_same m2 hQ
    omega
  · have hFull : hB = beta := by omega
    have hsupply : 1 ≤ zeroChip beta + SB.tail beta hB 0 := by
      rw [hFull]; exact SB.zeroChip_add_tail_full beta
    omega

/-- The same vertex, when the fallback owner lives here: the target's banana has
collapsed, so this chip is in the target's class. -/
theorem chainFar_ge_one (SB SM : PairLedger)
    {alpha beta s m1 m2 par2 par3 hQ hP hA hB : ℕ}
    (hpar2 : par2 = min m1 m2)
    (hhQ : hQ = targetHeight alpha beta s par2 par3)
    (hhP : hP = partnerHeight alpha beta s par2 par3)
    (hhA : hA = nearHeight alpha beta s par2 par3)
    (hhB : hB = farHeight alpha beta s par2 par3)
    (hzero : par2 = 0) :
    1 ≤ 1 + zeroChip beta +
      (SB.tail beta hB 0 + SM.tail m1 hB hQ + SM.tail m2 hB hQ) := by
  have hb := bounds hhQ hhP hhA hhB
  have hB0 : 0 ≤ SB.tail beta hB 0 := SB.tail_nonneg (Nat.zero_le _) (by omega)
  have hZ : (0 : ℤ) ≤ zeroChip beta := zeroChip_nonneg beta
  have hEq : hB = hQ := by omega
  have h1 : SM.tail m1 hB hQ = 0 := by rw [hEq]; exact SM.tail_same m1 hQ
  have h2 : SM.tail m2 hB hQ = 0 := by rw [hEq]; exact SM.tail_same m2 hQ
  omega

/-- **The target.**  Every slot at it rises towards it, so it never goes
negative. -/
theorem chainTarget_nonneg (SM SS : PairLedger)
    {alpha beta s m1 m2 par2 par3 hQ hP hA hB : ℕ}
    (hpar2 : par2 = min m1 m2)
    (hhQ : hQ = targetHeight alpha beta s par2 par3)
    (hhP : hP = partnerHeight alpha beta s par2 par3)
    (hhA : hA = nearHeight alpha beta s par2 par3)
    (hhB : hB = farHeight alpha beta s par2 par3) :
    0 ≤ SM.tail m1 hQ hB + SM.tail m2 hQ hB + SS.tail s hQ hP := by
  have hb := bounds hhQ hhP hhA hhB
  have hM1 : 0 ≤ SM.tail m1 hQ hB := SM.tail_nonneg (by omega) (by omega)
  have hM2 : 0 ≤ SM.tail m2 hQ hB := SM.tail_nonneg (by omega) (by omega)
  have hS : 0 ≤ SS.tail s hQ hP := SS.tail_nonneg (by omega) (by omega)
  omega

/-- **The target delivers.**  One of the two arguments of `hQ` is attained at a
positive slot group, and that slot is full. -/
theorem chainTarget_ge_one (SM SS : PairLedger)
    {alpha beta s m1 m2 par2 par3 hQ hP hA hB : ℕ}
    (hpar2 : par2 = min m1 m2)
    (hhQ : hQ = targetHeight alpha beta s par2 par3)
    (hhP : hP = partnerHeight alpha beta s par2 par3)
    (hhA : hA = nearHeight alpha beta s par2 par3)
    (hhB : hB = farHeight alpha beta s par2 par3)
    (hDel : Delivers alpha beta s par2 par3 hQ) :
    1 ≤ SM.tail m1 hQ hB + SM.tail m2 hQ hB + SS.tail s hQ hP := by
  have hb := bounds hhQ hhP hhA hhB
  have hM1 : 0 ≤ SM.tail m1 hQ hB := SM.tail_nonneg (by omega) (by omega)
  have hM2 : 0 ≤ SM.tail m2 hQ hB := SM.tail_nonneg (by omega) (by omega)
  have hS : 0 ≤ SS.tail s hQ hP := SS.tail_nonneg (by omega) (by omega)
  rcases hDel with ⟨hpos, hQeq⟩ | ⟨hpos, hQeq⟩
  · rcases Nat.le_total m1 m2 with h12 | h12
    · have h1 : SM.tail m1 hQ hB = 1 :=
        SM.tail_eq_one_of_full (by omega) (by omega)
      omega
    · have h2 : SM.tail m2 hQ hB = 1 :=
        SM.tail_eq_one_of_full (by omega) (by omega)
      omega
  · have h0 : SS.tail s hQ hP = 1 :=
      SS.tail_eq_one_of_full (by omega) (by omega)
    omega

end AtanasovRanganathan.ConfigurationReservoirChain
