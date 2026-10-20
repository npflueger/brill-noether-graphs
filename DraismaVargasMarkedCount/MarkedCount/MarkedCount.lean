module

public import DraismaVargasMarkedCount.MarkedCount.Correspondence
public import DraismaVargasCount.IntegerCount.EvenGenusCount

@[expose] public section

/-!
# The marked Draisma--Vargas count for `a, b ≤ 1`

Over a general marked metric graph `(Γ, marks)` of genus `g`, with `k` ramified marks and
`g + k = 2K + 2` even, the marked members of degree `K + 2 = (g + k + 2)/2` ramified at every
mark, counted with the multiplicity `Mult = (∏ r_φ(mark)) · D det A / 2^{l(T)}`
(`MarkedFrame.markedSignedMult`), number `C_{K+1} = C_{(g+k)/2}`.

* **Engine** (`markedCount_eq_catalan`): any marked cubic core with `k` marks, all ramified. The
  proof is the lollipop lemma (`Correspondence.markedCount_eq_openMultCount`) followed by the
  integer count `IntegerCount.openMultCount_eq_catalan` on the lollipop core, whose hypotheses come
  from `attachLollipops_cubic`, `attachLollipops_connected`, `attachLollipops_genus`,
  `lollipopRequest_pos` and the transfer of genericity (`general_lollipop_of_general`), with tails
  `β = λ = 1` (any positive tails would do).
* **`(a, b) = (1, 0)`, once-marked** (`markedCount_eq_catalan_onceMarked`): `(Γ, u)`, `g` odd. This
  is the once-marked statement (the lollipop lemma for `Γ` marked at `u` alone): the unramified
  mark `v` is not in the core and plays no role. `(0, 1)` is the same statement.
* **`(a, b) = (1, 1)`** (`markedCount_eq_catalan_twiceMarked`): `(Γ, u, v)`, `g` even; the marks
  may share an edge (`s₂` a piece of `s₁`), lie on a bridge or a loop.
* `(0, 0)` is the integer count `IntegerCount.openMultCount_eq_catalan` itself.

**Genus range.** `2 ≤ K`, i.e. `g + k ≥ 6`, exactly the range of the integer count: the lollipop
core has genus `g + k`. The cases `g + k = 4` (`g = 3` with `(1, 0)`, `g = 2` with `(1, 1)`) are not
treated here: they would need the integer count in genus four, below the range `2 ≤ k` (genus
at least six) of `IntegerCount.openMultCount_eq_catalan`.

**Genericity** has two parts: the core is (marked) cubic, the marks are interior to edges and
distinct (every piece length positive: `hPositive`), and no marked frame has a zero coordinate at
`y` (`hGeneral`, quantified over **all** marked frames, as the `hGeneral` of the integer count is
over all frames).
-/

namespace DraismaVargas.Count.MarkedCount

open Utilities.Certificate.ExplicitPotential (Core)
open GenusSixExistence.Tripod.Gadget (subdivide subdivide_connected)

/-- **The marked Draisma--Vargas count, engine form** (every mark of type `a = 1`). For `K ≥ 2`, a
connected marked cubic core with `k` marks whose genus plus `k` is `2K + 2`, a positive request at
which no marked frame has a zero coordinate, the marked count in degree `K + 2` is
`catalan (K + 1)`. The genus of the marked core is `p + 1 - n` (the marks are divalent); `hGenus` is
written without truncated subtraction trouble. -/
theorem markedCount_eq_catalan {K : ℕ} (hK : 2 ≤ K) {n p k : ℕ} (core : Core n p)
    (mark : Fin k → Fin n) (hMarked : IsMarkedCubic core mark) (hConnected : core.Connected)
    (hGenus : p + k + 1 - n = 2 * K + 2) (y : Fin p → ℚ) (hPositive : ∀ i, 0 < y i)
    (hGeneral : ∀ (κ : MarkedFrame core mark (K + 2)) (col : Fin p), κ.coordsAt y col ≠ 0) :
    markedCount core mark y (K + 2) = catalan (K + 1) := by
  have hOne : ∀ _ : Fin k, (0 : ℚ) < 1 := fun _ ↦ one_pos
  rw [markedCount_eq_openMultCount (bridge := fun _ ↦ 1) (loop := fun _ ↦ 1) hMarked hOne hOne,
    IntegerCount.openMultCount_eq_catalan hK (attachLollipops core mark)
      (attachLollipops_cubic hMarked) (attachLollipops_connected core mark hConnected)
      (by rw [attachLollipops_genus]; exact hGenus) _ (lollipopRequest_pos hPositive hOne hOne)
      (general_lollipop_of_general hMarked hGeneral (fun _ ↦ one_ne_zero) fun _ ↦ one_ne_zero)]

/-- **The once-marked count, `(a, b) = (1, 0)`** (the engine form with the single mark `u`).
`core` is a connected cubic core of odd genus `g = p + 1 - n = 2K + 1 ≥ 5`, the
mark `u` sits on slot `s`, and `y` gives the lengths of `Γ` with that slot split at `u`. The marked
members of degree `K + 2 = (g + 3)/2` with `r_φ(u) ≥ 1` number `C_{K+1} = C_{(g+1)/2}`. -/
theorem markedCount_eq_catalan_onceMarked {K : ℕ} (hK : 2 ≤ K) {n p : ℕ} (core : Core n p)
    (hCubic : core.Cubic) (hConnected : core.Connected) (hGenus : p + 1 - n + 1 = 2 * K + 2)
    (s : Fin p) (y : Fin (p + 1) → ℚ) (hPositive : ∀ i, 0 < y i)
    (hGeneral : ∀ (κ : MarkedFrame (subdivide core s) (onceMark n) (K + 2)) (col : Fin (p + 1)),
      κ.coordsAt y col ≠ 0) :
    markedCount (subdivide core s) (onceMark n) y (K + 2) = catalan (K + 1) :=
  markedCount_eq_catalan hK _ _ (isMarkedCubic_onceMarked hCubic s)
    (subdivide_connected _ _ hConnected) (by omega) y hPositive hGeneral

/-- **The twice-marked count, `(a, b) = (1, 1)`**. `core` is a connected cubic
core of even genus `g = p + 1 - n = 2K ≥ 4`; `u` sits on slot `s₁`, `v` on slot `s₂` of the
once-subdivided core (possibly a piece of `s₁`); `y` gives the lengths of `Γ` split at both marks.
The marked members of degree `K + 2 = (g + 4)/2` with `r_φ(u), r_φ(v) ≥ 1` number
`C_{K+1} = C_{(g+2)/2}`. -/
theorem markedCount_eq_catalan_twiceMarked {K : ℕ} (hK : 2 ≤ K) {n p : ℕ} (core : Core n p)
    (hCubic : core.Cubic) (hConnected : core.Connected) (hGenus : p + 1 - n + 2 = 2 * K + 2)
    (s₁ : Fin p) (s₂ : Fin (p + 1)) (y : Fin (p + 1 + 1) → ℚ) (hPositive : ∀ i, 0 < y i)
    (hGeneral : ∀ (κ : MarkedFrame (twiceMarked core s₁ s₂) (twiceMark n) (K + 2))
      (col : Fin (p + 1 + 1)), κ.coordsAt y col ≠ 0) :
    markedCount (twiceMarked core s₁ s₂) (twiceMark n) y (K + 2) = catalan (K + 1) :=
  markedCount_eq_catalan hK _ _ (isMarkedCubic_twiceMarked hCubic s₁ s₂)
    (twiceMarked_connected hConnected s₁ s₂) (by omega) y hPositive hGeneral

end DraismaVargas.Count.MarkedCount
