module

public import DraismaVargasMarkedCount.MarkedCountGeneral.Correspondence
public import DraismaVargasMarkedCount.MarkedCountGeneral.Drop
public import DraismaVargasCount.IntegerCount.EvenGenusCount

@[expose] public section

/-!
# The marked Draisma--Vargas count for every `(a, b)`

Over a general twice-marked metric graph `(Γ, u, v)` of genus `g`, with `a, b ≥ 0`,
`g + a + b + 2 = 2d` and `L = g - d + 1 ≥ 1`, the marked members of type `(a, b)` in degree `d`
(condition (D4′) of module `TypedFrame` at both marks), counted with the typed multiplicity
`D det A / 2^{l*}` (`typedAbsMult`), number

  `N(g; a, b) = C(g, L + a) - C(g, L - 1)`        (`markedFormula g d a`),

**in the range `g ≥ 5`, or `g = 4` with `a` and `b` both odd** (every level `g + a' + b'` of
the induction is then at least `6`, where the integer count holds).

* `typedCount_onceMarked`: the once-marked form `(a, 0)` with `v` absent, `g ≥ 5`
  (`typedCount_onceMarked_chain` under weaker genericity);
* `typedCount_twiceMarked`: `(a, b)` on the twice-marked core, `v` and `u` kept even when of
  type `0`.

**The proof** is strong induction on `a + b` over all lower types at once.
At `(a, b)` with `a, b ≥ 1`, attach caterpillar tails at both marks (`Tailed.canonical`); the
integer count (`IntegerCount.openMultCount_eq_catalan`) gives `C_{(g+a+b)/2}` on the tailed core,
the decomposition (`Correspondence.openMultCount_tailed`) expands it as
`Σ_{j,k} M_j(a) M_k(b) N_{a-2j, b-2k}`, the induction hypothesis gives every term but `(0, 0)`, and
the binomial identity `chainTail_identity` solves for it. A type-`0` mark is dropped
(`Drop.typedCount_dropFirst`, `typedCount_dropSecond`, `typedCount_dropOnce`), which reaches the
once-marked count and the integer count on `Γ`. **With `a` and `b` both odd no drop occurs.**

**Genericity** is a conjunction over the lower types (`OnceGeneral`,
`TwiceGeneral`): no typed frame of any type `≤ (a, b)` has a zero coordinate at `y`, and the same
for the once-marked cores and `Γ` at the merged requests, where a type-`0` mark is dropped. Every
clause excludes a finite union of hyperplanes in `y`. The once-marked count holds under the
weaker `OnceChainGeneral` and `OnceDropGeneral` (`typedCount_onceMarked_chain`), which name only
the typed frames of the types `a − 2m` in the degrees `d − m` and the frames of `Γ` in the degree
`d − a/2`, the ones the induction reads.

The four headlines depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open Finset
open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.SegmentWalls (Frame)
open GenusSixExistence.Tripod.Gadget (subdivide subdivide_connected)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p : ℕ}

/-! ## 1.  The formula and genericity -/

/-- **`N(g; a, b)` at degree `d`**: `C(g, L + a) - C(g, L - 1)` with `L = g + 1 - d`
(`b` enters through `d`). -/
def markedFormula (g d a : ℕ) : ℤ := (g.choose (g + 1 - d + a) : ℤ) - (g.choose (g - d) : ℤ)

/-- `N(g; a, b) = N(g; b, a)`: `C(g, L + a) = C(g, L + b)` as `g = 2L + a + b`. -/
theorem markedFormula_symm {g d a b : ℕ} (hd : g + a + b + 2 = 2 * d) (hL : d ≤ g) :
    markedFormula g d a = markedFormula g d b := by
  unfold markedFormula
  rw [← Nat.choose_symm (by omega : g + 1 - d + a ≤ g)]
  congr 3
  omega

/-- **Genericity of a once-marked core** `(Γ, u)` for type `a`, typed part: no typed
frame of type `≤ a` has a zero coordinate at `y`. The degree is free and so is the parity: typed
frames of type `a'` exist only in degree `(g + a' + 2)/2` (`MarkedFullDim.saturated`), so the extra
quantifiers are vacuous. -/
def OnceTypedGeneral (core : Core n p) (s : Fin p) (a : ℕ) (y : Fin (p + 1) → ℚ) : Prop :=
  ∀ types : Fin 1 → ℕ, types 0 ≤ a → ∀ (d : ℕ)
    (κ : TypedFrame (subdivide core s) (onceMark n) types d) (col : Fin (p + 1)),
    κ.coordsAt y col ≠ 0

/-- **Genericity of a once-marked core** for type `a`: the typed part, and the clause for the
drop of `u` (no frame of `Γ` has a zero coordinate at the merged request; used when `a` is
even). -/
def OnceGeneral (core : Core n p) (s : Fin p) (a : ℕ) (y : Fin (p + 1) → ℚ) : Prop :=
  OnceTypedGeneral core s a y ∧
    ∀ (d : ℕ) (f : Frame core d) (col : Fin p), f.coordsAt (mergeRequest s y) col ≠ 0

theorem OnceTypedGeneral.mono {core : Core n p} {s : Fin p} {a a' : ℕ} {y : Fin (p + 1) → ℚ}
    (h : OnceTypedGeneral core s a y) (ha : a' ≤ a) : OnceTypedGeneral core s a' y :=
  fun t ht ↦ h t (ht.trans ha)

theorem OnceGeneral.mono {core : Core n p} {s : Fin p} {a a' : ℕ} {y : Fin (p + 1) → ℚ}
    (h : OnceGeneral core s a y) (ha : a' ≤ a) : OnceGeneral core s a' y :=
  ⟨h.1.mono ha, h.2⟩

/-- **Genericity of a once-marked core along the chain** of type `a` in degree `d`: no typed
frame of type `a − 2m` in degree `d − m`, `2m ≤ a`, has a zero coordinate at `y`. These are the
only typed frames the proof of the once-marked count reads (`catalan_eq_once` at every level of
the induction). The type vector and the degree are quantified with equations, so that a typed
frame of a lower type `lowerType c J` in degree `d − shed J` is covered without a cast. -/
def OnceChainGeneral (core : Core n p) (s : Fin p) (a d : ℕ) (y : Fin (p + 1) → ℚ) : Prop :=
  ∀ m d', 2 * m ≤ a → d' = d - m → ∀ types : Fin 1 → ℕ, types 0 = a - 2 * m →
    ∀ (κ : TypedFrame (subdivide core s) (onceMark n) types d') (col : Fin (p + 1)),
      κ.coordsAt y col ≠ 0

/-- Chain genericity passes to a lower level of the induction. -/
theorem OnceChainGeneral.lower {core : Core n p} {s : Fin p} {a d : ℕ} {y : Fin (p + 1) → ℚ}
    (h : OnceChainGeneral core s a d y) {j : ℕ} (hj : 2 * j ≤ a) :
    OnceChainGeneral core s (a - 2 * j) (d - j) y :=
  fun m d' hm hd' types ht ↦ h (j + m) d' (by omega) (by omega) types (by omega)

/-- Typed genericity gives chain genericity in every degree. -/
theorem OnceTypedGeneral.chain {core : Core n p} {s : Fin p} {a : ℕ} {y : Fin (p + 1) → ℚ}
    (h : OnceTypedGeneral core s a y) (d : ℕ) : OnceChainGeneral core s a d y :=
  fun _ d' _ _ types ht ↦ h types (by omega) d'

/-- **The drop clause at one degree**: no frame of `Γ` in degree `d₀` has a zero coordinate at
the merged request. The once-marked count of type `a` in degree `d` uses it only at
`d₀ = d − a/2`, the degree of its type-`0` level. -/
def OnceDropGeneral (core : Core n p) (s : Fin p) (d₀ : ℕ) (y : Fin (p + 1) → ℚ) : Prop :=
  ∀ (f : Frame core d₀) (col : Fin p), f.coordsAt (mergeRequest s y) col ≠ 0

/-- **Genericity of a twice-marked core** `(Γ, u, v)` for type `(a, b)`, typed part:
no typed frame of type `≤ (a, b)` has a zero coordinate at `y`. -/
def TwiceTypedGeneral (core : Core n p) (s₁ : Fin p) (s₂ : Fin (p + 1)) (a b : ℕ)
    (y : Fin (p + 1 + 1) → ℚ) : Prop :=
  ∀ types : Fin 2 → ℕ, types 0 ≤ a → types 1 ≤ b → ∀ (d : ℕ)
    (κ : TypedFrame (twiceMarked core s₁ s₂) (twiceMark n) types d) (col : Fin (p + 1 + 1)),
    κ.coordsAt y col ≠ 0

/-- **Genericity of a twice-marked core** for type `(a, b)`: the typed part, and the clauses for the
drops of `v` and of `u` (the once-marked cores at the merged requests, used when `b`, resp. `a`,
is even). -/
def TwiceGeneral (core : Core n p) (s₁ : Fin p) (s₂ : Fin (p + 1)) (a b : ℕ)
    (y : Fin (p + 1 + 1) → ℚ) : Prop :=
  TwiceTypedGeneral core s₁ s₂ a b y ∧
    OnceGeneral core s₁ a (mergeRequest s₂ y) ∧
    OnceGeneral core (dropFirstSlot s₁ s₂) b (dropFirstRequest s₁ s₂ y)

theorem TwiceTypedGeneral.mono {core : Core n p} {s₁ : Fin p} {s₂ : Fin (p + 1)}
    {a b a' b' : ℕ} {y : Fin (p + 1 + 1) → ℚ} (h : TwiceTypedGeneral core s₁ s₂ a b y)
    (ha : a' ≤ a) (hb : b' ≤ b) : TwiceTypedGeneral core s₁ s₂ a' b' y :=
  fun t h0 h1 ↦ h t (h0.trans ha) (h1.trans hb)

theorem TwiceGeneral.mono {core : Core n p} {s₁ : Fin p} {s₂ : Fin (p + 1)} {a b a' b' : ℕ}
    {y : Fin (p + 1 + 1) → ℚ} (h : TwiceGeneral core s₁ s₂ a b y) (ha : a' ≤ a) (hb : b' ≤ b) :
    TwiceGeneral core s₁ s₂ a' b' y :=
  ⟨h.1.mono ha hb, h.2.1.mono ha, h.2.2.mono hb⟩

/-! ## 2.  The engines: the integer count on the tailed core, expanded -/

/-- **The once-marked tail count**: for `a ≥ 1`, the integer count on `(Γ, u)` with a caterpillar of
genus `a` at `u`, expanded by the decomposition:
`C_{d-1} = Σ_{j ≤ a/2} M_j(a) · N_{a - 2j}(d - j)`. -/
theorem catalan_eq_once {core : Core n p} (hCubic : core.Cubic) (hConnected : core.Connected)
    {g : ℕ} (hg : p + 1 - n = g) (hg4 : 4 ≤ g) (s : Fin p) {a d : ℕ} (ha : 1 ≤ a)
    (hd : g + a + 2 = 2 * d) (h6 : 6 ≤ g + a) {y : Fin (p + 1) → ℚ} (hy : ∀ i, 0 < y i)
    (hGen : OnceChainGeneral core s a d y) :
    (catalan (d - 1) : ℚ) = ∑ j ∈ range (a / 2 + 1), (ballot a j : ℚ) *
      typedCount (subdivide core s) (onceMark n) ![a - 2 * j] y (d - j) := by
  set c₀ := a - 1 with hc₀
  set cc : Fin 1 → ℕ := fun _ ↦ c₀ with hcc
  set T := Tailed.canonical (subdivide core s) (onceMark n) cc
  have hc := isMarkedCubic_onceMarked hCubic s
  have hd' : IsTailDegree (n + 1) (p + 1) cc d := by
    unfold IsTailDegree
    simp only [hcc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, one_mul]
    omega
  have hEng := openMultCount_tailed T hc hd' (y := y) (yH := T.request y)
    (fun i ↦ T.request_coreSlot y i) (fun j s ↦ by rw [T.request_tailSlot]; exact one_pos)
  obtain ⟨K, rfl⟩ : ∃ K, d = K + 2 := ⟨d - 2, by omega⟩
  have hGenus : T.P + 1 - T.N = 2 * K + 2 := by
    rw [T.genus_eq (by omega)]
    simp only [hcc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, one_mul]
    omega
  have hG1 := IntegerCount.openMultCount_eq_catalan (k := K) (by omega) T.H (T.cubic hc)
    (T.connected (subdivide_connected _ _ hConnected)) hGenus (T.request y) (T.request_pos hy)
    (general_tailed_of_general T hc (fun i ↦ T.request_coreSlot y i)
      (fun j s ↦ by rw [T.request_tailSlot]; exact one_ne_zero)
      fun J κ col ↦ hGen (J 0) _ (by have := (J 0).isLt; simp only [hcc] at this; omega)
        (by simp [shed]) _ (by simp only [lowerType, hcc]; omega) κ col)
  rw [hG1] at hEng
  rw [show K + 2 - 1 = K + 1 by omega, hEng]
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin ((c₀ + 1) / 2 + 1)) : LowerIndex cc ≃ _) _
    (fun j : Fin ((c₀ + 1) / 2 + 1) ↦ (ballot a j : ℚ) *
      typedCount (subdivide core s) (onceMark n) ![a - 2 * (j : ℕ)] y (K + 2 - j))]
  · rw [Fin.sum_univ_eq_sum_range (fun j ↦ (ballot a j : ℚ) *
      typedCount (subdivide core s) (onceMark n) ![a - 2 * j] y (K + 2 - j)),
      show (c₀ + 1) / 2 + 1 = a / 2 + 1 by omega]
  · intro J
    have hCard : (Fintype.card (SlopeData cc J) : ℚ) = (ballot a (J 0) : ℚ) := by
      have h := card_slopeData J
      rw [Fin.prod_univ_one] at h
      rw [show a = c₀ + 1 by omega]
      exact_mod_cast h
    have hType : lowerType cc J = ![a - 2 * (J 0 : ℕ)] := by
      funext i
      fin_cases i
      simp only [lowerType, hcc]
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_fin_one]
      omega
    have hShed : shed J = J 0 := by simp [shed]
    rw [hCard, hType, hShed]
    rfl

/-- **The twice-marked tail count**: for `a, b ≥ 1`, the integer count on `(Γ, u, v)` with
caterpillars of genus `a` at `u` and `b` at `v`, expanded by the decomposition:
`C_{d-1} = Σ_{j ≤ a/2} Σ_{k ≤ b/2} M_j(a) M_k(b) · N_{a-2j, b-2k}(d - j - k)`. -/
theorem catalan_eq_twice {core : Core n p} (hCubic : core.Cubic) (hConnected : core.Connected)
    {g : ℕ} (hg : p + 1 - n = g) (hg4 : 4 ≤ g) (s₁ : Fin p) (s₂ : Fin (p + 1)) {a b d : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : g + a + b + 2 = 2 * d) (h6 : 6 ≤ g + a + b)
    {y : Fin (p + 1 + 1) → ℚ} (hy : ∀ i, 0 < y i) (hGen : TwiceTypedGeneral core s₁ s₂ a b y) :
    (catalan (d - 1) : ℚ) = ∑ j ∈ range (a / 2 + 1), ∑ k ∈ range (b / 2 + 1),
      (ballot a j : ℚ) * (ballot b k : ℚ) *
        typedCount (twiceMarked core s₁ s₂) (twiceMark n) ![a - 2 * j, b - 2 * k] y
          (d - j - k) := by
  set cc : Fin 2 → ℕ := ![a - 1, b - 1] with hcc
  set T := Tailed.canonical (twiceMarked core s₁ s₂) (twiceMark n) cc
  have hc := isMarkedCubic_twiceMarked hCubic s₁ s₂
  have hd' : IsTailDegree (n + 1 + 1) (p + 1 + 1) cc d := by
    unfold IsTailDegree
    rw [Fin.sum_univ_two]
    simp only [hcc, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have hEng := openMultCount_tailed T hc hd' (y := y) (yH := T.request y)
    (fun i ↦ T.request_coreSlot y i) (fun j s ↦ by rw [T.request_tailSlot]; exact one_pos)
  obtain ⟨K, rfl⟩ : ∃ K, d = K + 2 := ⟨d - 2, by omega⟩
  have hGenus : T.P + 1 - T.N = 2 * K + 2 := by
    rw [T.genus_eq (by omega), Fin.sum_univ_two]
    simp only [hcc, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have hG1 := IntegerCount.openMultCount_eq_catalan (k := K) (by omega) T.H (T.cubic hc)
    (T.connected (twiceMarked_connected hConnected s₁ s₂)) hGenus (T.request y)
    (T.request_pos hy)
    (general_tailed_of_general T hc (fun i ↦ T.request_coreSlot y i)
      (fun j s ↦ by rw [T.request_tailSlot]; exact one_ne_zero)
      fun J κ col ↦ hGen _
        (by show cc 0 + 1 - 2 * (J 0 : ℕ) ≤ a; simp only [hcc, Matrix.cons_val_zero]; omega)
        (by show cc 1 + 1 - 2 * (J 1 : ℕ) ≤ b; simp [hcc]; omega) _ κ col)
  rw [hG1] at hEng
  rw [show K + 2 - 1 = K + 1 by omega, hEng]
  rw [Fintype.sum_equiv (piFinTwoEquiv fun i ↦ Fin ((cc i + 1) / 2 + 1)) _
    (fun q : Fin ((a - 1 + 1) / 2 + 1) × Fin ((b - 1 + 1) / 2 + 1) ↦
      (ballot a q.1 : ℚ) * (ballot b q.2 : ℚ) *
        typedCount (twiceMarked core s₁ s₂) (twiceMark n) ![a - 2 * (q.1 : ℕ), b - 2 * (q.2 : ℕ)]
          y (K + 2 - q.1 - q.2))]
  · rw [Fintype.sum_prod_type]
    dsimp only
    change ∑ x : Fin ((a - 1 + 1) / 2 + 1), ∑ y_1 : Fin ((b - 1 + 1) / 2 + 1),
      (ballot a x : ℚ) * (ballot b y_1 : ℚ) *
        typedCount (twiceMarked core s₁ s₂) (twiceMark n) ![a - 2 * (x : ℕ), b - 2 * (y_1 : ℕ)]
          y (K + 2 - x - y_1) = _
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ ∑ k : Fin ((b - 1 + 1) / 2 + 1),
      (ballot a j : ℚ) * (ballot b k : ℚ) *
        typedCount (twiceMarked core s₁ s₂) (twiceMark n) ![a - 2 * j, b - 2 * (k : ℕ)]
          y (K + 2 - j - k))]
    rw [show (a - 1 + 1) / 2 + 1 = a / 2 + 1 by omega]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Fin.sum_univ_eq_sum_range (fun k ↦ (ballot a j : ℚ) * (ballot b k : ℚ) *
        typedCount (twiceMarked core s₁ s₂) (twiceMark n) ![a - 2 * j, b - 2 * k]
          y (K + 2 - j - k)),
      show (b - 1 + 1) / 2 + 1 = b / 2 + 1 by omega]
  · intro J
    have hCard : (Fintype.card (SlopeData cc J) : ℚ) =
        (ballot a (J 0) : ℚ) * (ballot b (J 1) : ℚ) := by
      have h := card_slopeData J
      rw [Fin.prod_univ_two] at h
      simp only [hcc, Matrix.cons_val_zero, Matrix.cons_val_one] at h
      rw [show a = a - 1 + 1 by omega, show b = b - 1 + 1 by omega]
      exact_mod_cast h
    have hType : lowerType cc J = ![a - 2 * (J 0 : ℕ), b - 2 * (J 1 : ℕ)] := by
      funext i
      fin_cases i
      · simp only [lowerType, hcc, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        omega
      · simp only [lowerType, hcc, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
          Matrix.cons_val_zero]
        omega
    have hShed : shed J = J 0 + J 1 := by simp [shed, Fin.sum_univ_two]
    rw [hCard, hType, hShed, Nat.sub_sub]
    rfl

/-! ## 3.  The once-marked count -/

/-- `markedFormula` at a lower type is the summand of the identity `chainTail_identity`. -/
theorem markedFormula_lower {g d a j k : ℕ} (hj : 2 * j ≤ a) (hjk : j + k ≤ d) (hL : d ≤ g) :
    markedFormula g (d - j - k) (a - 2 * j) =
      (g.choose (g + 1 - d + a + k - j) : ℤ) - (g.choose (g + 1 - d + j + k - 1) : ℤ) := by
  unfold markedFormula
  congr 3 <;> omega

/-- **The inductive step, once-marked** (at `(a, 0)`, `a ≥ 1`): the tail count, the
induction hypothesis at every `a - 2j`, `j ≥ 1`, and the identity `chainTail_identity` give
`N(g; a)`. -/
theorem onceMarked_step {core : Core n p} (hCubic : core.Cubic) (hConnected : core.Connected)
    {g : ℕ} (hg : p + 1 - n = g) (hg4 : 4 ≤ g) (s : Fin p) {a d : ℕ} (ha : 1 ≤ a)
    (hd : g + a + 2 = 2 * d) (hL : d ≤ g) (h6 : 6 ≤ g + a) {y : Fin (p + 1) → ℚ}
    (hy : ∀ i, 0 < y i) (hGen : OnceChainGeneral core s a d y)
    (hIH : ∀ j ∈ range (a / 2 + 1), j ≠ 0 →
      typedCount (subdivide core s) (onceMark n) ![a - 2 * j] y (d - j) =
        (markedFormula g (d - j) (a - 2 * j) : ℚ)) :
    typedCount (subdivide core s) (onceMark n) ![a] y d = (markedFormula g d a : ℚ) := by
  have hEng := catalan_eq_once hCubic hConnected hg hg4 s ha hd h6 hy hGen
  have hId := chainTail_identity_once (g := g) (a := a) (L := g + 1 - d) (by omega) (by omega)
  rw [show catalan (g + 1 - d + a) = catalan (d - 1) by congr 1; omega] at hId
  set X : ℕ → ℚ := fun j ↦
    typedCount (subdivide core s) (onceMark n) ![a - 2 * j] y (d - j) with hX
  set B : ℕ → ℚ := fun j ↦
    (((g.choose (g + 1 - d + a - j) : ℤ) - (g.choose (g + 1 - d + j - 1) : ℤ) : ℤ) : ℚ) with hB
  have hLow : ∀ j ∈ range (a / 2 + 1), j ≠ 0 → X j = B j := by
    intro j hj hj0
    have hj' := Finset.mem_range.mp hj
    simp only [hX, hB]
    rw [hIH j hj hj0]
    have h := markedFormula_lower (g := g) (d := d) (a := a) (j := j) (k := 0)
      (by omega) (by omega) hL
    simp only [Nat.sub_zero, add_zero] at h
    rw [h]
  have hSum : ∑ j ∈ range (a / 2 + 1), (ballot a j : ℚ) * (X j - B j) = 0 := by
    have hId' := congrArg (fun z : ℤ ↦ (z : ℚ)) hId
    push_cast at hId'
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← hEng]
    simp only [hB]
    push_cast
    linarith
  have hSingle : ∑ j ∈ range (a / 2 + 1), (ballot a j : ℚ) * (X j - B j) = X 0 - B 0 := by
    rw [Finset.sum_eq_single_of_mem 0 (by simp) fun j hj hj0 ↦ by
      rw [hLow j hj hj0, sub_self, mul_zero]]
    simp
  have h00 : X 0 = B 0 := by linarith
  simp only [hX, hB, Nat.mul_zero, Nat.sub_zero, add_zero] at h00
  rw [h00]
  unfold markedFormula
  push_cast
  congr 3
  omega

/-- **The once-marked count `(a, 0)` under chain genericity** (over `(Γ, u)`, `v` absent),
`g ≥ 5`: the genericity it reads is `OnceChainGeneral` and the drop clause in the one degree
`d − a/2`. -/
theorem typedCount_onceMarked_chain {core : Core n p} (hCubic : core.Cubic)
    (hConnected : core.Connected) {g : ℕ} (hg : p + 1 - n = g) (hg5 : 5 ≤ g) (s : Fin p)
    (a d : ℕ) (hd : g + a + 2 = 2 * d) (hL : d ≤ g) (y : Fin (p + 1) → ℚ) (hy : ∀ i, 0 < y i)
    (hGen : OnceChainGeneral core s a d y) (hDrop : OnceDropGeneral core s (d - a / 2) y) :
    typedCount (subdivide core s) (onceMark n) ![a] y d = (markedFormula g d a : ℚ) := by
  induction a using Nat.strong_induction_on generalizing d with
  | _ a ih =>
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · -- type 0: drop `u`, then the integer count on `Γ`
    obtain ⟨K, rfl⟩ : ∃ K, d = K + 2 := ⟨d - 2, by omega⟩
    rw [typedCount_dropOnce hCubic s hy (hGen 0 _ (by omega) (by omega) ![0] (by simp)),
      IntegerCount.openMultCount_eq_catalan (k := K) (by omega) core hCubic hConnected
        (by omega) _ (mergeRequest_pos hy) (by simpa [OnceDropGeneral] using hDrop)]
    have hC := catalan_eq_choose_sub (m := K + 1) (by omega)
    unfold markedFormula
    rw [show g + 1 - (K + 2) + 0 = K + 1 by omega, show g - (K + 2) = K + 1 - 1 by omega,
      show g = 2 * (K + 1) by omega]
    exact_mod_cast hC
  · refine onceMarked_step hCubic hConnected hg (by omega) s ha hd hL (by omega) hy hGen
      fun j hj hj0 ↦ ?_
    have hj' := Finset.mem_range.mp hj
    refine ih (a - 2 * j) (by omega) (d - j) (by omega) (by omega) (hGen.lower (by omega)) ?_
    rwa [show d - j - (a - 2 * j) / 2 = d - a / 2 by omega]

/-- **The once-marked count `(a, 0)`** (over `(Γ, u)`, `v` absent), `g ≥ 5`. -/
theorem typedCount_onceMarked {core : Core n p} (hCubic : core.Cubic)
    (hConnected : core.Connected) {g : ℕ} (hg : p + 1 - n = g) (hg5 : 5 ≤ g) (s : Fin p) :
    ∀ (a d : ℕ), g + a + 2 = 2 * d → d ≤ g → ∀ y : Fin (p + 1) → ℚ, (∀ i, 0 < y i) →
      OnceGeneral core s a y →
        typedCount (subdivide core s) (onceMark n) ![a] y d = (markedFormula g d a : ℚ) :=
  fun a d hd hL y hy hGen ↦ typedCount_onceMarked_chain hCubic hConnected hg hg5 s a d hd hL y hy
    (hGen.1.chain d) (hGen.2 _)

/-- **The once-marked count for odd `a`**, with no drop: every lower type `a - 2j` is odd,
so the proof uses neither the drop lemma nor the `k = 0` comparison with the integer count
(module `Drop`, `Agreement.typedCount_nil_eq_openMultCount`), and the genericity is
`OnceTypedGeneral` alone. -/
theorem typedCount_onceMarked_odd {core : Core n p} (hCubic : core.Cubic)
    (hConnected : core.Connected) {g : ℕ} (hg : p + 1 - n = g) (hg5 : 5 ≤ g) (s : Fin p) :
    ∀ (a d : ℕ), Odd a → g + a + 2 = 2 * d → d ≤ g → ∀ y : Fin (p + 1) → ℚ, (∀ i, 0 < y i) →
      OnceTypedGeneral core s a y →
        typedCount (subdivide core s) (onceMark n) ![a] y d = (markedFormula g d a : ℚ) := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro d hOdd hd hL y hy hGen
  have ha : 1 ≤ a := hOdd.pos
  refine onceMarked_step hCubic hConnected hg (by omega) s ha hd hL (by omega) hy (hGen.chain d)
    fun j hj hj0 ↦ ?_
  have hj' := Finset.mem_range.mp hj
  exact ih (a - 2 * j) (by omega) (d - j) (Nat.Odd.sub_even (by omega) hOdd (even_two_mul j))
    (by omega) (by omega) y hy (hGen.mono (by omega))

/-! ## 4.  The twice-marked count -/

/-- **The inductive step, twice-marked** (at `(a, b)`, `a, b ≥ 1`): the tail count, the
induction hypothesis at every `(a - 2j, b - 2k) ≠ (a, b)`, and the identity
`chainTail_identity`. -/
theorem twiceMarked_step {core : Core n p} (hCubic : core.Cubic) (hConnected : core.Connected)
    {g : ℕ} (hg : p + 1 - n = g) (hg4 : 4 ≤ g) (s₁ : Fin p) (s₂ : Fin (p + 1)) {a b d : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : g + a + b + 2 = 2 * d) (hL : d ≤ g)
    {y : Fin (p + 1 + 1) → ℚ} (hy : ∀ i, 0 < y i) (hGen : TwiceTypedGeneral core s₁ s₂ a b y)
    (hIH : ∀ j ∈ range (a / 2 + 1), ∀ k ∈ range (b / 2 + 1), (j, k) ≠ (0, 0) →
      typedCount (twiceMarked core s₁ s₂) (twiceMark n) ![a - 2 * j, b - 2 * k] y (d - j - k) =
        (markedFormula g (d - j - k) (a - 2 * j) : ℚ)) :
    typedCount (twiceMarked core s₁ s₂) (twiceMark n) ![a, b] y d = (markedFormula g d a : ℚ) := by
  have hEng := catalan_eq_twice hCubic hConnected hg hg4 s₁ s₂ ha hb hd (by omega) hy hGen
  have hId := chainTail_identity (g := g) (a := a) (b := b) (L := g + 1 - d) (by omega)
    (by omega)
  rw [show g + 1 - d + a + b = d - 1 by omega] at hId
  set X : ℕ → ℕ → ℚ := fun j k ↦
    typedCount (twiceMarked core s₁ s₂) (twiceMark n) ![a - 2 * j, b - 2 * k] y (d - j - k)
    with hX
  set B : ℕ → ℕ → ℚ := fun j k ↦
    (((g.choose (g + 1 - d + a + k - j) : ℤ) - (g.choose (g + 1 - d + j + k - 1) : ℤ) : ℤ) : ℚ)
    with hB
  have hLow : ∀ j ∈ range (a / 2 + 1), ∀ k ∈ range (b / 2 + 1), (j, k) ≠ (0, 0) →
      X j k = B j k := by
    intro j hj k hk hjk
    have hj' := Finset.mem_range.mp hj
    have hk' := Finset.mem_range.mp hk
    simp only [hX, hB]
    rw [hIH j hj k hk hjk, markedFormula_lower (by omega) (by omega) hL]
  have hSum : ∑ j ∈ range (a / 2 + 1), ∑ k ∈ range (b / 2 + 1),
      (ballot a j : ℚ) * (ballot b k : ℚ) * (X j k - B j k) = 0 := by
    have hId' := congrArg (fun z : ℤ ↦ (z : ℚ)) hId
    push_cast at hId'
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← hEng]
    simp only [hB]
    push_cast
    linarith
  have hSingle : ∑ j ∈ range (a / 2 + 1), ∑ k ∈ range (b / 2 + 1),
      (ballot a j : ℚ) * (ballot b k : ℚ) * (X j k - B j k) = X 0 0 - B 0 0 := by
    rw [Finset.sum_eq_single_of_mem 0 (by simp) fun j hj hj0 ↦ Finset.sum_eq_zero fun k hk ↦ by
      rw [hLow j hj k hk (by simp [hj0]), sub_self, mul_zero]]
    rw [Finset.sum_eq_single_of_mem 0 (by simp) fun k hk hk0 ↦ by
      rw [hLow 0 (by simp) k hk (by simp [hk0]), sub_self, mul_zero]]
    simp
  have h00 : X 0 0 = B 0 0 := by linarith
  simp only [hX, hB, Nat.mul_zero, Nat.sub_zero, add_zero] at h00
  rw [h00]
  unfold markedFormula
  push_cast
  congr 3
  omega

/-- A lower index `(j, k) ≠ (0, 0)` lowers `a + b`. -/
theorem lower_lt {a b j k : ℕ} (hj : j < a / 2 + 1) (hk : k < b / 2 + 1) (hjk : (j, k) ≠ (0, 0)) :
    a - 2 * j + (b - 2 * k) < a + b := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · have : k ≠ 0 := fun h ↦ hjk (by rw [h])
    omega
  · omega

/-- **The marked Draisma--Vargas count for every `(a, b)`**: over a general
twice-marked core of genus `g`, the typed count of type `(a, b)` in degree
`d = (g + a + b + 2)/2`, `L = g + 1 - d ≥ 1`, is `C(g, L + a) - C(g, L - 1)`, for `g ≥ 5`, or
`g = 4` with `a`, `b` both odd. The marks may share an edge, lie on a bridge or a loop; a mark of
type `0` is kept in the core. -/
theorem typedCount_twiceMarked {core : Core n p} (hCubic : core.Cubic)
    (hConnected : core.Connected) {g : ℕ} (hg : p + 1 - n = g) (s₁ : Fin p) (s₂ : Fin (p + 1)) :
    ∀ (a b d : ℕ), (5 ≤ g ∨ (g = 4 ∧ Odd a ∧ Odd b)) → g + a + b + 2 = 2 * d → d ≤ g →
      ∀ y : Fin (p + 1 + 1) → ℚ, (∀ i, 0 < y i) → TwiceGeneral core s₁ s₂ a b y →
        typedCount (twiceMarked core s₁ s₂) (twiceMark n) ![a, b] y d =
          (markedFormula g d a : ℚ) := by
  suffices H : ∀ m a b d, a + b = m → (5 ≤ g ∨ (g = 4 ∧ Odd a ∧ Odd b)) →
      g + a + b + 2 = 2 * d → d ≤ g → ∀ y : Fin (p + 1 + 1) → ℚ, (∀ i, 0 < y i) →
        TwiceGeneral core s₁ s₂ a b y →
          typedCount (twiceMarked core s₁ s₂) (twiceMark n) ![a, b] y d =
            (markedFormula g d a : ℚ) from
    fun a b d ↦ H (a + b) a b d rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro a b d hm hRange hd hL y hy hGen
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · -- `u` of type 0: drop it
    have hg5 : 5 ≤ g := by
      rcases hRange with h | ⟨-, h, -⟩
      · exact h
      · exact absurd h (by decide)
    rw [typedCount_dropFirst hCubic s₁ s₂ b hy (hGen.1 ![0, b] (by simp) (by simp) d),
      typedCount_onceMarked hCubic hConnected hg hg5 (dropFirstSlot s₁ s₂) b d (by omega) hL _
        (dropFirstRequest_pos hy) hGen.2.2, markedFormula_symm (a := b) (b := 0) (by omega) hL]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · -- `v` of type 0: drop it
    have hg5 : 5 ≤ g := by
      rcases hRange with h | ⟨-, -, h⟩
      · exact h
      · exact absurd h (by decide)
    rw [typedCount_dropSecond hCubic s₁ s₂ a hy (hGen.1 ![a, 0] (by simp) (by simp) d),
      typedCount_onceMarked hCubic hConnected hg hg5 s₁ a d (by omega) hL _
        (mergeRequest_pos hy) hGen.2.1]
  -- both ramified
  have h4 : 4 ≤ g := by rcases hRange with h | ⟨h, -⟩ <;> omega
  refine twiceMarked_step hCubic hConnected hg h4 s₁ s₂ ha hb hd hL hy hGen.1
    fun j hj k hk hjk ↦ ?_
  have hj' := Finset.mem_range.mp hj
  have hk' := Finset.mem_range.mp hk
  have hRange' : 5 ≤ g ∨ (g = 4 ∧ Odd (a - 2 * j) ∧ Odd (b - 2 * k)) := by
    rcases hRange with h | ⟨h, hoa, hob⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, Nat.Odd.sub_even (by omega) hoa (even_two_mul j),
        Nat.Odd.sub_even (by omega) hob (even_two_mul k)⟩
  exact ih _ (hm ▸ lower_lt hj' hk' hjk) (a - 2 * j) (b - 2 * k) (d - j - k) rfl hRange'
    (by omega) (by omega) y hy (hGen.mono (by omega) (by omega))

/-- **The twice-marked count for `a`, `b` both odd**, `g ≥ 4`, with no drop: every lower type is
odd, so the proof uses neither the drop lemma nor the `k = 0` comparison with the integer count, and
the genericity is `TwiceTypedGeneral` alone. -/
theorem typedCount_twiceMarked_odd {core : Core n p} (hCubic : core.Cubic)
    (hConnected : core.Connected) {g : ℕ} (hg : p + 1 - n = g) (hg4 : 4 ≤ g) (s₁ : Fin p)
    (s₂ : Fin (p + 1)) :
    ∀ (a b d : ℕ), Odd a → Odd b → g + a + b + 2 = 2 * d → d ≤ g →
      ∀ y : Fin (p + 1 + 1) → ℚ, (∀ i, 0 < y i) → TwiceTypedGeneral core s₁ s₂ a b y →
        typedCount (twiceMarked core s₁ s₂) (twiceMark n) ![a, b] y d =
          (markedFormula g d a : ℚ) := by
  suffices H : ∀ m a b d, a + b = m → Odd a → Odd b → g + a + b + 2 = 2 * d → d ≤ g →
      ∀ y : Fin (p + 1 + 1) → ℚ, (∀ i, 0 < y i) → TwiceTypedGeneral core s₁ s₂ a b y →
        typedCount (twiceMarked core s₁ s₂) (twiceMark n) ![a, b] y d =
          (markedFormula g d a : ℚ) from
    fun a b d ↦ H (a + b) a b d rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro a b d hm hoa hob hd hL y hy hGen
  refine twiceMarked_step hCubic hConnected hg hg4 s₁ s₂ hoa.pos hob.pos hd hL hy hGen
    fun j hj k hk hjk ↦ ?_
  have hj' := Finset.mem_range.mp hj
  have hk' := Finset.mem_range.mp hk
  exact ih _ (hm ▸ lower_lt hj' hk' hjk) (a - 2 * j) (b - 2 * k) (d - j - k) rfl
    (Nat.Odd.sub_even (by omega) hoa (even_two_mul j))
    (Nat.Odd.sub_even (by omega) hob (even_two_mul k)) (by omega) (by omega) y hy
    (hGen.mono (by omega) (by omega))

end DraismaVargas.Count.MarkedCountGeneral
