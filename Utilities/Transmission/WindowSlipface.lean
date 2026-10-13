module

public import Utilities.Transmission.WindowPerm
public import Utilities.Transmission.TransmissionCorner
public import Utilities.Transmission.TransmissionExistence

@[expose] public section

/-!
# The slipface of a window permutation, computably

A finite window permutation `windowPerm σ o` (`Utilities.Transmission.WindowPerm`) made as cheap
to use as a Young diagram: its slipface, length, inverse and essential set are computable and
evaluated by `decide`, and corner domination (`Utilities.CornersDominate`) reduces to a finite box
check, also by `decide`.

## API

`import Utilities.Transmission.WindowSlipface` (it imports `Utilities.Transmission.WindowPerm`,
`Utilities.Transmission.TransmissionCorner` and `Utilities.Transmission.TransmissionExistence`).

**Defining `σ`.** Give the one-line values and the inverse, both as vectors; the two inverse laws
default to `by decide`:

```
def σ : Equiv.Perm (Fin 6) := Window.mkPerm ![1, 4, 0, 2, 5, 3] ![2, 0, 3, 5, 1, 4]
def τ : AspPerm := Window.windowPerm σ 0
```

The one-line permutation `140253` is `windowPerm σ 0` with this `σ` (values `0`-indexed); a translate
`[o, o + n)` is `windowPerm σ o`. Because the inverse is explicit, `σ⁻¹` evaluates under `decide`
as fast as `σ`.

**Facts about `τ = windowPerm σ o`.**

* `windowPerm_inv : (windowPerm σ o)⁻¹ = windowPerm σ⁻¹ o`, `windowPerm_inv_apply`;
* `windowPerm_chi : (windowPerm σ o).χ = 0`;
* `windowPerm_inv_set_ncard : (inv_set (windowPerm σ o)).ncard = finInv σ` (`finInv` computable),
  `finiteTransmissionPerm_windowPerm`, `inv_set_windowPerm` (the inversion set itself);
* `windowPerm_s : (windowPerm σ o).s A b = windowS σ o A b` (`windowS` computable; the
  transmission row `(a, b)` uses `A = a + 1`), and `windowPerm_s_eq_max_of_not_box`: outside the
  box `o < A < o + n`, `o < b < o + n` the slipface is `max 0 (A − b)`;
* `mem_ess_windowPerm_iff : (a, b) ∈ (windowPerm σ o).ess ↔ (a, b) ∈ windowEss σ o`
  (`windowEss` computable; the transmission row of `(a, b)` is `(a − 1, b)`);
* translation: `windowFun_translate`, `windowPerm_s_translate`
  (`(windowPerm σ (o + t)).s A b = (windowPerm σ o).s (A − t) (b − t)`).

**Corner domination by `decide`.** `BoxDominates σ o C` (decidable; it is `boxCheck σ o C = true`)
checks the rows `o ≤ a ≤ o + n − 2`, `o + 1 ≤ b ≤ o + n − 1`, and
`cornersDominate_of_boxDominates : BoxDominates σ o C → CornersDominate (windowPerm σ o) C`. Outside
that box every row is trivial or on the Riemann line. Typical use:

```
example : CornersDominate (windowPerm σ⁻¹ 0) [(1, 4, 0), (1, 1, 1), (4, 4, 1)] :=
  Window.cornersDominate_of_boxDominates _ _ _ (by decide)
example : (windowPerm σ⁻¹ 0).s 2 4 = 1 := by rw [Window.windowPerm_s]; decide
```

`transmissionExists_of_boxDominates` packages `satisfiesTransmission_of_corners`: a divisor of
degree `g` meeting the corner bounds witnesses `TransmissionExists G u v (windowPerm σ o)`.

**Timings** (`decide`, elaboration plus kernel check, measured 2026-10-12): the `140253` box with
three corners about 30 ms; `24153` (`windowPerm σ (-2)`, three corners) about 20 ms; an `n = 10` window with eight
corners about 80 ms. `decide +kernel` also works and is no faster.

All counts are recursions on `ℕ` with `ℤ` offsets (`countFrom`, `sumNat`), and `σ` is read on `ℕ`
through `σN`; no `Finset` over `ℤ` is reduced.
-/

namespace Utilities.Window

open Utilities

/-! ## Counting by recursion -/

/-- `countFrom p b k` is the number of `i < k` with `p (b + i)`, by recursion on `k`. -/
def countFrom (p : ℤ → Bool) : ℤ → ℕ → ℕ
  | _, 0 => 0
  | b, k + 1 => (bif p b then 1 else 0) + countFrom p (b + 1) k

/-- `sumNat f k = f 0 + ⋯ + f (k - 1)`, by recursion on `k`. -/
def sumNat (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => sumNat f k + f k

theorem sumNat_eq_sum (f : ℕ → ℕ) (k : ℕ) : sumNat f k = ∑ i ∈ Finset.range k, f i := by
  induction k with
  | zero => rfl
  | succ k ih => rw [sumNat, ih, Finset.sum_range_succ]

theorem countFrom_shift (p : ℤ → Bool) (t : ℤ) (b : ℤ) (k : ℕ) :
    countFrom p b k = countFrom (fun m ↦ p (m + t)) (b - t) k := by
  induction k generalizing b with
  | zero => rfl
  | succ k ih =>
      rw [countFrom, countFrom, ih (b + 1), sub_add_cancel, show b - t + 1 = b + 1 - t by ring]

/-! ## The function on `ℕ` and the window value -/

/-- `σ` read as a function on `ℕ`, the identity from `n` on. -/
def σN {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) : ℕ :=
  if h : k < n then ((σ ⟨k, h⟩ : Fin n) : ℕ) else k

theorem σN_of_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) {k : ℕ} (h : k < n) :
    σN σ k = ((σ ⟨k, h⟩ : Fin n) : ℕ) := by
  rw [σN, dite_eq_left h]

theorem σN_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) {k : ℕ} (h : k < n) : σN σ k < n := by
  rw [σN_of_lt σ h]
  exact (σ _).isLt

theorem windowFun_add_nat {n : ℕ} (σ : Equiv.Perm (Fin n)) (o : ℤ) {k : ℕ} (h : k < n) :
    windowFun σ o (o + k) = o + σN σ k := by
  rw [σN_of_lt σ h]
  exact windowFun_index σ o ⟨k, h⟩

/-- The window function is the identity below `o`. -/
theorem windowFun_of_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) {o x : ℤ} (h : x < o) :
    windowFun σ o x = x :=
  windowFun_of_not_mem σ o (by omega)

/-- The window function is the identity from `o + n` on. -/
theorem windowFun_of_ge {n : ℕ} (σ : Equiv.Perm (Fin n)) {o x : ℤ} (h : o + n ≤ x) :
    windowFun σ o x = x :=
  windowFun_of_not_mem σ o (by omega)

/-! ## Inverse -/

/-- **The inverse of a window permutation** is the window permutation of the inverse. -/
theorem windowPerm_inv {n : ℕ} (σ : Equiv.Perm (Fin n)) (o : ℤ) :
    (windowPerm σ o)⁻¹ = windowPerm σ⁻¹ o := by
  apply AspPerm.ext.2
  funext x
  have h := windowFun_leftInverse σ⁻¹ o x
  rw [inv_inv] at h
  change (windowPerm σ o)⁻¹ x = windowFun σ⁻¹ o x
  conv_lhs => rw [← h]
  exact (windowPerm σ o).inv_mul_cancel_eval _

@[simp] theorem windowPerm_inv_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (o x : ℤ) :
    (windowPerm σ o)⁻¹ x = windowFun σ⁻¹ o x := by
  rw [windowPerm_inv]
  rfl

/-! ## The slipface as a count -/

/-- The slipface of any ASP permutation as a count over `[b, M)`, once `M` bounds the inputs
with value below `a`. -/
theorem s_eq_countFrom (τ : AspPerm) (A M : ℤ) (hM : ∀ m, M ≤ m → A ≤ τ m) (b : ℤ) :
    τ.s A b = countFrom (fun m ↦ decide (τ m < A)) b (M - b).toNat := by
  generalize hk : (M - b).toNat = k
  induction k generalizing b with
  | zero =>
      rw [countFrom, AspPerm.s_eq_ncard]
      have : southeast_set τ A b = ∅ := by
        ext m
        simp only [southeast_set, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and,
          not_lt]
        intro hm
        exact hM m (by omega)
      rw [this, Set.ncard_empty]
  | succ k ih =>
      have hstep := τ.b_step A b
      rw [ih (b + 1) (by omega)] at hstep
      rw [countFrom]
      push_cast
      by_cases h : τ b < A
      · simp only [h, decide_true, Bool.cond_true, ite_true] at hstep ⊢
        push_cast
        omega
      · simp only [h, decide_false, Bool.cond_false, ite_false] at hstep ⊢
        push_cast
        omega

/-- **The computable slipface** of `windowPerm σ o`: the number of `m ∈ [b, max A (o + n))`
with `windowFun σ o m < A`. -/
def windowS {n : ℕ} (σ : Equiv.Perm (Fin n)) (o A b : ℤ) : ℤ :=
  (countFrom (fun m ↦ decide (windowFun σ o m < A)) b (max A (o + n) - b).toNat : ℕ)

/-- **The slipface of a window permutation is `windowS`.** -/
theorem windowPerm_s {n : ℕ} (σ : Equiv.Perm (Fin n)) (o A b : ℤ) :
    (windowPerm σ o).s A b = windowS σ o A b := by
  rw [s_eq_countFrom (windowPerm σ o) A (max A (o + n)) ?_ b]
  · rfl
  · intro m hm
    rw [windowPerm_apply, windowFun_of_ge σ (le_of_max_le_right hm)]
    exact le_of_max_le_left hm

/-! ## Shift zero -/

theorem windowPerm_s_self {n : ℕ} (σ : Equiv.Perm (Fin n)) (o : ℤ) :
    (windowPerm σ o).s o o = 0 := by
  rw [AspPerm.s_eq_ncard]
  have : southeast_set (windowPerm σ o) o o = ∅ := by
    ext m
    simp only [southeast_set, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and,
      not_lt, windowPerm_apply]
    intro hm
    by_cases hw : o ≤ m ∧ m < o + n
    · exact (windowFun_mem σ o hw).1
    · rw [windowFun_of_not_mem σ o hw]
      exact hm
  rw [this, Set.ncard_empty]
  rfl

/-- **A window permutation has shift zero.** -/
@[simp] theorem windowPerm_chi {n : ℕ} (σ : Equiv.Perm (Fin n)) (o : ℤ) :
    (windowPerm σ o).χ = 0 := by
  have h1 := (windowPerm σ o).s_ge o o
  have h2 := (windowPerm σ⁻¹ o).s_ge o o
  rw [windowPerm_s_self] at h1 h2
  rw [← windowPerm_inv, AspPerm.chi_dual] at h2
  omega

/-! ## Outside the box the slipface is the identity's -/

/-- The southeast set equals `[b, A)` when `A ≤ o`, `o + n ≤ A` or `o + n ≤ b`. -/
theorem windowPerm_southeast_eq_Ico {n : ℕ} (σ : Equiv.Perm (Fin n)) (o A b : ℤ)
    (h : A ≤ o ∨ o + n ≤ A ∨ o + n ≤ b) :
    southeast_set (windowPerm σ o) A b = Set.Ico b A := by
  ext m
  simp only [southeast_set, Set.mem_ofPred_eq, Set.mem_Ico, windowPerm_apply]
  by_cases hw : o ≤ m ∧ m < o + n
  · have := windowFun_mem σ o hw
    constructor
    · rintro ⟨hb, hA⟩
      exact ⟨hb, by omega⟩
    · rintro ⟨hb, hA⟩
      exact ⟨hb, by omega⟩
  · rw [windowFun_of_not_mem σ o hw]

theorem windowPerm_s_eq_max_of_not_box_aux {n : ℕ} (σ : Equiv.Perm (Fin n)) (o A b : ℤ)
    (h : A ≤ o ∨ o + n ≤ A ∨ o + n ≤ b) :
    (windowPerm σ o).s A b = max 0 (A - b) := by
  rw [AspPerm.s_eq_ncard, windowPerm_southeast_eq_Ico σ o A b h, ← Finset.coe_Ico,
    Set.ncard_coe_finset, Int.card_Ico, Int.toNat_eq_max, max_comm]

/-- **Outside the box** `o < A < o + n`, `o < b < o + n`, the slipface of `windowPerm σ o` is
the identity's, `max 0 (A − b)`. -/
theorem windowPerm_s_eq_max_of_not_box {n : ℕ} (σ : Equiv.Perm (Fin n)) (o A b : ℤ)
    (h : A ≤ o ∨ o + n ≤ A ∨ b ≤ o ∨ o + n ≤ b) :
    (windowPerm σ o).s A b = max 0 (A - b) := by
  rcases h with h | h | h | h
  · exact windowPerm_s_eq_max_of_not_box_aux σ o A b (Or.inl h)
  · exact windowPerm_s_eq_max_of_not_box_aux σ o A b (Or.inr (Or.inl h))
  · have hd := (windowPerm σ o).s_eq A b
    rw [windowPerm_inv, windowPerm_chi,
      windowPerm_s_eq_max_of_not_box_aux σ⁻¹ o b A (Or.inl h)] at hd
    rw [hd]
    omega
  · exact windowPerm_s_eq_max_of_not_box_aux σ o A b (Or.inr (Or.inr h))

/-! ## The box check -/

/-- The corner test at one row `(a, b)`, given the slipface value `s = s(a + 1, b)`: trivial,
Riemann (shift zero), or transport from a corner of `C`. -/
def rowCovered (C : List Corner) (a b s : ℤ) : Bool :=
  decide (s - 1 < 0) || decide (s - 1 ≤ a - b) || C.any fun c ↦ decide (s - 1 ≤ cornerBound c a b)

/-- **The box check**: every row `(a, b)` with `o ≤ a ≤ o + n − 2` and `o + 1 ≤ b ≤ o + n − 1`
is covered. -/
def boxCheck {n : ℕ} (σ : Equiv.Perm (Fin n)) (o : ℤ) (C : List Corner) : Bool :=
  (List.range (n - 1)).all fun i : ℕ ↦ (List.range (n - 1)).all fun j : ℕ ↦
    rowCovered C (o + i) (o + 1 + j) (windowS σ o (o + i + 1) (o + 1 + j))

/-- The corner list `C` dominates `windowPerm σ o` on the box; a decidable finite check. -/
def BoxDominates {n : ℕ} (σ : Equiv.Perm (Fin n)) (o : ℤ) (C : List Corner) : Prop :=
  boxCheck σ o C = true

instance {n : ℕ} (σ : Equiv.Perm (Fin n)) (o : ℤ) (C : List Corner) :
    Decidable (BoxDominates σ o C) :=
  inferInstanceAs (Decidable (boxCheck σ o C = true))

/-- **The box lemma.** A box check proves `CornersDominate` on the whole lattice. -/
theorem cornersDominate_of_boxDominates {n : ℕ} (σ : Equiv.Perm (Fin n)) (o : ℤ)
    (C : List Corner) (h : BoxDominates σ o C) :
    CornersDominate (windowPerm σ o) C := by
  intro a b
  rw [windowPerm_chi, zero_add]
  by_cases hbox : o ≤ a ∧ a + 1 < o + n ∧ o < b ∧ b < o + n
  · obtain ⟨ha1, ha2, hb1, hb2⟩ := hbox
    have hi : (a - o).toNat < n - 1 := by omega
    have hj : (b - o - 1).toNat < n - 1 := by omega
    have hrow := List.all_eq_true.mp (List.all_eq_true.mp h _ (List.mem_range.mpr hi)) _
      (List.mem_range.mpr hj)
    have hai : o + (((a - o).toNat : ℕ) : ℤ) = a := by omega
    have hbj : o + 1 + (((b - o - 1).toNat : ℕ) : ℤ) = b := by omega
    rw [hai, hbj, ← windowPerm_s] at hrow
    simp only [rowCovered, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hrow
    rcases hrow with (h1 | h2) | ⟨c, hc, h3⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨c, hc, h3⟩)
  · rw [windowPerm_s_eq_max_of_not_box σ o (a + 1) b (by omega)]
    by_cases hab : a + 1 - b ≤ 0
    · left
      rw [max_eq_left hab]
      omega
    · right; left
      rw [max_eq_right (by omega)]
      omega

/-! ## Writing a concrete permutation -/

/-- A permutation of `Fin n` from a function and an explicit inverse, both usually written as
vectors `![…]`; the two inverse laws default to `by decide`. Because the inverse is explicit,
`decide` evaluates `σ⁻¹` as fast as `σ`. -/
def mkPerm {n : ℕ} (f g : Fin n → Fin n) (hgf : ∀ i, g (f i) = i := by decide)
    (hfg : ∀ i, f (g i) = i := by decide) : Equiv.Perm (Fin n) :=
  ⟨f, g, hgf, hfg⟩

/-! ## Translation -/

/-- On the window, `windowFun` reads `σ` through `σN`. -/
theorem windowFun_eq_σN {n : ℕ} (σ : Equiv.Perm (Fin n)) (o : ℤ) {x : ℤ}
    (h : o ≤ x ∧ x < o + n) : windowFun σ o x = o + σN σ (x - o).toNat := by
  have hx : x = o + (((x - o).toNat : ℕ) : ℤ) := by omega
  conv_lhs => rw [hx]
  exact windowFun_add_nat σ o (by omega)

/-- **Translating the window** conjugates by the shift: `windowFun σ (o + t) x =
windowFun σ o (x − t) + t`. -/
theorem windowFun_translate {n : ℕ} (σ : Equiv.Perm (Fin n)) (o t x : ℤ) :
    windowFun σ (o + t) x = windowFun σ o (x - t) + t := by
  by_cases hw : o + t ≤ x ∧ x < o + t + n
  · rw [windowFun_eq_σN σ (o + t) hw, windowFun_eq_σN σ o (by omega),
      show x - t - o = x - (o + t) by ring]
    ring
  · rw [windowFun_of_not_mem σ (o + t) hw, windowFun_of_not_mem σ o (by omega)]
    ring

/-- The slipface of a translated window is the translated slipface. -/
theorem windowPerm_s_translate {n : ℕ} (σ : Equiv.Perm (Fin n)) (o t A b : ℤ) :
    (windowPerm σ (o + t)).s A b = (windowPerm σ o).s (A - t) (b - t) := by
  rw [windowPerm_s, windowPerm_s, windowS, windowS, countFrom_shift _ t b]
  have hlen : max A (o + t + n) - b = max (A - t) (o + n) - (b - t) := by
    rw [max_def, max_def]
    split_ifs <;> omega
  rw [hlen]
  congr 2
  funext m
  rw [windowFun_translate, add_sub_cancel_right, decide_eq_decide]
  omega

/-! ## Inversions -/

/-- The inversion count of `σ`: pairs `i < j < n` with `σ j < σ i`, by recursion. -/
def finInv {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  sumNat (fun i ↦ sumNat (fun j ↦ if i < j ∧ σN σ j < σN σ i then 1 else 0) n) n

/-- The inversions of `σ` as a finset of pairs of naturals. -/
def invFinset {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset (ℕ × ℕ) :=
  (Finset.range n ×ˢ Finset.range n).filter fun p ↦ p.1 < p.2 ∧ σN σ p.2 < σN σ p.1

theorem finInv_eq_card {n : ℕ} (σ : Equiv.Perm (Fin n)) : finInv σ = (invFinset σ).card := by
  rw [invFinset, Finset.card_filter, Finset.sum_product, finInv, sumNat_eq_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [sumNat_eq_sum]

/-- Every inversion of `windowPerm σ o` lies in the window. -/
theorem mem_window_of_inv {n : ℕ} (σ : Equiv.Perm (Fin n)) (o : ℤ) {x y : ℤ}
    (h : (x, y) ∈ inv_set (windowPerm σ o)) :
    (o ≤ x ∧ x < o + n) ∧ (o ≤ y ∧ y < o + n) := by
  obtain ⟨hxy, hval⟩ := h
  simp only [windowPerm_apply] at hval
  by_cases hx : o ≤ x ∧ x < o + n
  · by_cases hy : o ≤ y ∧ y < o + n
    · exact ⟨hx, hy⟩
    · rw [windowFun_of_not_mem σ o hy] at hval
      have := windowFun_mem σ o hx
      omega
  · rw [windowFun_of_not_mem σ o hx] at hval
    by_cases hy : o ≤ y ∧ y < o + n
    · have := windowFun_mem σ o hy
      omega
    · rw [windowFun_of_not_mem σ o hy] at hval
      omega

/-- The inversion set of `windowPerm σ o` is the translate of the inversions of `σ`. -/
theorem inv_set_windowPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) (o : ℤ) :
    inv_set (windowPerm σ o) =
      (fun p : ℕ × ℕ ↦ (o + (p.1 : ℤ), o + (p.2 : ℤ))) '' (invFinset σ : Set (ℕ × ℕ)) := by
  ext ⟨x, y⟩
  constructor
  · intro h
    obtain ⟨hx, hy⟩ := mem_window_of_inv σ o h
    obtain ⟨hxy, hval⟩ := h
    simp only [windowPerm_apply, windowFun_eq_σN σ o hx, windowFun_eq_σN σ o hy] at hval
    refine ⟨((x - o).toNat, (y - o).toNat), ?_, ?_⟩
    · simp only [invFinset, Finset.coe_filter, Finset.mem_product, Finset.mem_range,
        Set.mem_ofPred_eq]
      omega
    · simp only [Prod.mk.injEq]
      omega
  · rintro ⟨⟨i, j⟩, hp, hpq⟩
    simp only [invFinset, Finset.coe_filter, Finset.mem_product, Finset.mem_range,
      Set.mem_ofPred_eq] at hp
    simp only [Prod.mk.injEq] at hpq
    obtain ⟨rfl, rfl⟩ := hpq
    refine ⟨by omega, ?_⟩
    simp only [windowPerm_apply, windowFun_add_nat σ o hp.1.1, windowFun_add_nat σ o hp.1.2]
    omega

/-- **The length of a window permutation** is the inversion count of `σ`. -/
theorem windowPerm_inv_set_ncard {n : ℕ} (σ : Equiv.Perm (Fin n)) (o : ℤ) :
    (inv_set (windowPerm σ o)).ncard = finInv σ := by
  rw [inv_set_windowPerm, Set.ncard_image_of_injective, Set.ncard_coe_finset, finInv_eq_card]
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  simp only [Prod.mk.injEq] at h
  simp only [Prod.mk.injEq]
  omega

/-- A window permutation has finite length. -/
theorem finiteTransmissionPerm_windowPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) (o : ℤ) :
    FiniteTransmissionPerm (windowPerm σ o) := by
  unfold FiniteTransmissionPerm
  rw [inv_set_windowPerm]
  exact (invFinset σ).finite_toSet.image _

/-! ## The essential set -/

/-- The essential-set condition at `(a, b)`, read off `σ` and `σ⁻¹`. -/
def essCheck {n : ℕ} (σ : Equiv.Perm (Fin n)) (o a b : ℤ) : Bool :=
  decide (windowFun σ o b < a ∧ a ≤ windowFun σ o (b - 1) ∧
    windowFun σ⁻¹ o a < b ∧ b ≤ windowFun σ⁻¹ o (a - 1))

/-- The points of the box `[o + 1, o + n − 1]²`, row by row. -/
def boxPoints (n : ℕ) (o : ℤ) : List (ℤ × ℤ) :=
  (List.range (n - 1)).flatMap fun i : ℕ ↦ (List.range (n - 1)).map fun j : ℕ ↦
    (o + 1 + (i : ℤ), o + 1 + (j : ℤ))

/-- **The computable essential set** of `windowPerm σ o`. -/
def windowEss {n : ℕ} (σ : Equiv.Perm (Fin n)) (o : ℤ) : List (ℤ × ℤ) :=
  (boxPoints n o).filter fun p ↦ essCheck σ o p.1 p.2

theorem mem_boxPoints {n : ℕ} {o a b : ℤ} :
    (a, b) ∈ boxPoints n o ↔ (o < a ∧ a < o + n) ∧ (o < b ∧ b < o + n) := by
  simp only [boxPoints, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨i, hi, j, hj, rfl, rfl⟩
    omega
  · rintro ⟨⟨ha1, ha2⟩, hb1, hb2⟩
    exact ⟨(a - o - 1).toNat, by omega, (b - o - 1).toNat, by omega, by omega, by omega⟩

/-- The essential condition forces `o < b < o + n`. -/
theorem lt_window_of_ess {n : ℕ} (σ : Equiv.Perm (Fin n)) (o a b : ℤ)
    (h1 : windowFun σ o b < a) (h2 : a ≤ windowFun σ o (b - 1)) : o < b ∧ b < o + n := by
  by_cases hb : o ≤ b ∧ b < o + n
  · have hb1 := windowFun_mem σ o hb
    by_cases hb' : o ≤ b - 1 ∧ b - 1 < o + n
    · omega
    · rw [windowFun_of_not_mem σ o hb'] at h2
      omega
  · rw [windowFun_of_not_mem σ o hb] at h1
    by_cases hb' : o ≤ b - 1 ∧ b - 1 < o + n
    · have := windowFun_mem σ o hb'
      omega
    · rw [windowFun_of_not_mem σ o hb'] at h2
      omega

/-- **The essential set of a window permutation is `windowEss`.** -/
theorem mem_ess_windowPerm_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) (o a b : ℤ) :
    (a, b) ∈ (windowPerm σ o).ess ↔ (a, b) ∈ windowEss σ o := by
  simp only [AspPerm.ess, Set.mem_ofPred_eq, windowPerm_apply, windowPerm_inv_apply, windowEss,
    List.mem_filter, essCheck, decide_eq_true_eq, mem_boxPoints]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨?_, lt_window_of_ess σ o a b h1 h2⟩, h1, h2, h3, h4⟩
    exact lt_window_of_ess σ⁻¹ o b a h3 h4
  · rintro ⟨-, h⟩
    exact h

/-! ## Transmission from a box check -/

/-- **Transmission for a window permutation from corners.** A divisor of degree `g` meeting the
rank bounds of a corner list that passes the box check witnesses `windowPerm σ o`. -/
theorem transmissionExists_of_boxDominates {G : CFGraph} (hG : graph_connected G) (u v : G.V)
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (o : ℤ) (C : List Corner) (hbox : BoxDominates σ o C)
    (D : CFDiv G) (hdeg : deg D = (genus G : ℤ))
    (hC : ∀ c ∈ C, rank G (D + c.1 • one_chip u - c.2.1 • one_chip v) ≥ c.2.2) :
    TransmissionExists G u v (windowPerm σ o) :=
  ⟨D, satisfiesTransmission_of_corners hG u v _ D C (by rw [windowPerm_chi, add_zero]; exact hdeg)
    (cornersDominate_of_boxDominates σ o C hbox) hC⟩

end Utilities.Window
