module

public import Utilities.Subdivision.InteriorFiring
public import Utilities.IntegralGeometry.Denominator

@[expose] public section

/-!
# Consecutive-index row divisibility and the slot-moment arithmetic

The *consecutive-index row lemma* (`consecutive_row_divisibility`): a row
identity `k (k + 1) y = (k + 1) L + k r` forces `k ∣ L` and `k + 1 ∣ r`. Its
cleared form produces explicit divisibility witnesses in every commutative
ring, with no characteristic or domain hypothesis. The quotient form, and the
membership of the terms of a row before, at and after a transition, work
uniformly in any subring of `ℚ`, in particular in the subring of rationals
with odd reduced denominator defined here.

`slotMoment_dvd_two_pow_of_terms` converts odd-denominator weighted positions
into the integer offset divisibility required by the interior-firing lemma of
`Utilities.Subdivision.InteriorFiring`, separately for each `Spec` slot and
counting chip multiplicity. It does not produce the geometric hypotheses: the
positions and coefficients of an actual fibre divisor, and the identification
of the rows of an edge-length system with slots, must be supplied by the
caller. No positivity of target lengths is used by the arithmetic.
-/

namespace DraismaVargas.Count.SlotMoment

open DraismaVargas.Infrastructure
open Utilities.Certificate.SubdivisionGraph

/-- The consecutive-index row lemma uses only the identity
`1 = (k + 1) - k`, hence works in every commutative ring. -/
theorem consecutive_row_divisibility {R : Type*} [CommRing R] (k y L r : R)
    (h : k * (k + 1) * y = (k + 1) * L + k * r) :
    k ∣ L ∧ k + 1 ∣ r := by
  constructor
  · refine ⟨(k + 1) * y - r - L, ?_⟩
    linear_combination -h
  · refine ⟨r - k * y + L, ?_⟩
    linear_combination h

/-- The quotient conclusion of the consecutive-index row lemma, inside any
coefficient subring of `ℚ`.
No integrality or positivity of the request is needed. -/
theorem consecutive_row_quotients_mem (S : Subring ℚ) (k y L r : ℚ)
    (hk : k ≠ 0) (hk1 : k + 1 ≠ 0) (hkmem : k ∈ S)
    (hy : y ∈ S) (hL : L ∈ S) (hr : r ∈ S)
    (h : k * (k + 1) * y = (k + 1) * L + k * r) :
    L / k ∈ S ∧ r / (k + 1) ∈ S := by
  have hLeft : L / k = (k + 1) * y - r - L := by
    apply (div_eq_iff hk).mpr
    linear_combination -h
  have hRight : r / (k + 1) = r - k * y + L := by
    apply (div_eq_iff hk1).mpr
    linear_combination h
  rw [hLeft, hRight]
  exact ⟨S.sub_mem (S.sub_mem (S.mul_mem (S.add_mem hkmem S.one_mem) hy) hr) hL,
    S.add_mem (S.sub_mem hr (S.mul_mem hkmem hy)) hL⟩

/-- The coefficient ring used in the odd-multiplicity argument, represented
concretely by reduced rational denominators. -/
def oddDenominatorSubring : Subring ℚ where
  carrier := {q | Odd q.den}
  one_mem' := by norm_num
  zero_mem' := by norm_num
  add_mem' := fun ha hb ↦ (ha.mul hb).of_dvd_nat (Rat.add_den_dvd _ _)
  mul_mem' := fun ha hb ↦ (ha.mul hb).of_dvd_nat (Rat.mul_den_dvd _ _)
  neg_mem' := fun ha ↦ by simpa using ha

@[simp] theorem mem_oddDenominatorSubring (q : ℚ) :
    q ∈ oddDenominatorSubring ↔ Odd q.den := Iff.rfl

/-- Before a transition, a chip coefficient is zero or the constant edge
index, so its product with the position belongs to the coefficient ring. -/
theorem before_transition_term_mem (S : Subring ℚ) (k subtotal c : ℚ)
    (hk : k ≠ 0) (hPartial : subtotal ∈ S) (hc : c = 0 ∨ c = k) :
    c * (subtotal / k) ∈ S := by
  rcases hc with hc | hc
  · simp [hc]
  · rw [hc]
    have hCancel : k * (subtotal / k) = subtotal := by field_simp
    rwa [hCancel]

/-- At the transition, the consecutive-index row lemma makes the position
itself belong to the ring, so every integral chip coefficient is allowed,
including coefficient one. -/
theorem transition_term_mem (S : Subring ℚ) (k y L r : ℚ) (c : ℤ)
    (hk : k ≠ 0) (hk1 : k + 1 ≠ 0) (hkmem : k ∈ S)
    (hy : y ∈ S) (hL : L ∈ S) (hr : r ∈ S)
    (h : k * (k + 1) * y = (k + 1) * L + k * r) :
    (c : ℚ) * (L / k) ∈ S :=
  S.mul_mem (intCast_mem S c)
    (consecutive_row_quotients_mem S k y L r hk hk1 hkmem hy hL hr h).1

/-- After a transition, the coefficient cancels the second index while the
first partial quotient is already in the ring by the consecutive-index row
lemma. -/
theorem after_transition_term_mem (S : Subring ℚ) (k y L r subtotal c : ℚ)
    (hk : k ≠ 0) (hk1 : k + 1 ≠ 0) (hkmem : k ∈ S)
    (hy : y ∈ S) (hL : L ∈ S) (hr : r ∈ S) (hPartial : subtotal ∈ S)
    (h : k * (k + 1) * y = (k + 1) * L + k * r)
    (hc : c = 0 ∨ c = k + 1) :
    c * (L / k + subtotal / (k + 1)) ∈ S := by
  rcases hc with rfl | rfl
  · simp
  · have hQuot := (consecutive_row_quotients_mem S k y L r
      hk hk1 hkmem hy hL hr h).1
    have hProduct : (k + 1) * (L / k + subtotal / (k + 1)) =
        (k + 1) * (L / k) + subtotal := by field_simp
    rw [hProduct]
    exact S.add_mem (S.mul_mem (S.add_mem hkmem S.one_mem) hQuot) hPartial

/-- Before the hairpin the position is a sum of non-leaf lengths; after it
the leaf length occurs twice. This is the only arithmetic needed in that row. -/
theorem hairpin_term_mem (S : Subring ℚ) (subtotal leaf : ℚ) (c : ℤ)
    (hPartial : subtotal ∈ S) (hLeaf : 2 * leaf ∈ S) :
    (c : ℚ) * subtotal ∈ S ∧ (c : ℚ) * (subtotal + 2 * leaf) ∈ S :=
  ⟨S.mul_mem (intCast_mem S c) hPartial,
    S.mul_mem (intCast_mem S c) (S.add_mem hPartial hLeaf)⟩

/-- If multiplying a rational of odd denominator by `N` gives an integer,
the integer contains every power of two dividing `N`. -/
theorem two_pow_dvd_of_scaled_odd_denominator (N a : ℕ) (q : ℚ) (moment : ℤ)
    (hN : 2 ^ a ∣ N) (hOdd : Odd q.den)
    (hScaled : (N : ℚ) * q = moment) : ((2 ^ a : ℕ) : ℤ) ∣ moment := by
  have hRational : (q.den : ℚ) * moment = (N : ℚ) * q.num := by
    rw [← hScaled]
    calc
      (q.den : ℚ) * (N * q) = N * ((q.den : ℚ) * q) := by ring
      _ = N * q.num := by rw [Rat.den_mul_eq_num]
  have hInteger : (q.den : ℤ) * moment = (N : ℤ) * q.num := by
    exact_mod_cast hRational
  have hDvd : ((2 ^ a : ℕ) : ℤ) ∣ (q.den : ℤ) * moment := by
    rw [hInteger]
    exact dvd_mul_of_dvd_left (by exact_mod_cast hN) _
  rw [Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_natCast] at hDvd
  exact Int.natCast_dvd.mpr
    (((Nat.coprime_two_left.mpr hOdd).pow_left a).dvd_of_dvd_mul_left hDvd)

/-- The integer slot offset moment is `N` times its rational position moment. -/
theorem slotMoment_scaled {n p : ℕ} (T : Spec n p) (D : CFDiv T.graph)
    (N : ℕ) (hN : 0 < N) (e : Fin p) :
    (N : ℚ) * (∑ o : Fin (T.length e - 1),
      (D (T.interiorVertex e o) : ℚ) * (((o.val + 1 : ℕ) : ℚ) / N)) =
      (InteriorFiring.slotMoment T D e : ℚ) := by
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simp only [InteriorFiring.slotMoment, Int.cast_sum, Int.cast_mul, Int.cast_natCast,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o _
  field_simp

/-- The arithmetic adapter to the per-slot hypothesis of the interior-firing
lemma. The caller must establish membership of each weighted rational position
in the odd-denominator subring. The moment is taken slot by slot, never over a
union of slots. -/
theorem slotMoment_dvd_two_pow_of_terms {n p : ℕ} (T : Spec n p)
    (D : CFDiv T.graph) (N a : ℕ) (hN : 0 < N) (hScale : 2 ^ a ∣ N)
    (e : Fin p)
    (hTerms : ∀ o : Fin (T.length e - 1),
      (D (T.interiorVertex e o) : ℚ) * (((o.val + 1 : ℕ) : ℚ) / N)
        ∈ oddDenominatorSubring) :
    ((2 ^ a : ℕ) : ℤ) ∣ InteriorFiring.slotMoment T D e := by
  apply two_pow_dvd_of_scaled_odd_denominator N a
    (∑ o : Fin (T.length e - 1),
      (D (T.interiorVertex e o) : ℚ) * (((o.val + 1 : ℕ) : ℚ) / N)) _ hScale
  · exact oddDenominatorSubring.sum_mem (fun o _ ↦ hTerms o)
  · exact slotMoment_scaled T D N hN e

/-- The consecutive-index row lemma genuinely permits nonintegral positions in
its 2-local form: indices three and four with row length one give partial
positions one third and two thirds. -/
theorem odd_thirds_example :
    (1 / 3 : ℚ) ∈ oddDenominatorSubring ∧ (2 / 3 : ℚ) ∈ oddDenominatorSubring := by
  convert consecutive_row_quotients_mem oddDenominatorSubring
    3 1 1 (8 / 3) (by norm_num) (by norm_num)
    (by change Odd (3 : ℚ).den; decide)
    (by change Odd (1 : ℚ).den; decide)
    (by change Odd (1 : ℚ).den; decide)
    (by norm_num [mem_oddDenominatorSubring]) (by norm_num) using 1
  norm_num

end DraismaVargas.Count.SlotMoment
