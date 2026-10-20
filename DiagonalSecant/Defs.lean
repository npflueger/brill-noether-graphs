module

public import DraismaVargasMarkedCount.MarkedCountGeneral.MarkedCount
public import DraismaVargasCount.DegenerateBigDivisor
public import GenusSixExistence.BrillNoetherRank.Reduction

@[expose] public section

/-!
# The diagonal secant theorem: definitions

The theorem (`Main.lean`): on every connected graph `G` of genus `g ≥ 5` with
`g ≡ 1, 2 (mod 4)` and every vertex `u`, some effective `F` of degree two has
`r_G((g − 3)u + F) ≥ 1`; hence `BNExists G 1 (g − 1)`.

This module holds the shared vocabulary, almost all of it definitions:

* `tailType`, `tailed`: the once-marked core `subdivide core s` with the caterpillar tail of
  genus `a` at the mark, as in the two-point ramified count (`Tailed.canonical`), the core `H` on
  which the closure is run;
* `IsFullType`: a frame of `H` whose restriction (`restrictTailed`) sheds no sheet, i.e. whose
  lower index is `J = 0`. These are the frames that restrict to typed frames of the full type
  `a`; the predicate reads the frame only (`restrictTailed` takes a `Frame`), as the tripod's
  `MemberIsClaw` does;
* `DiagonalOddWitness G m u`: the restriction of the public
  `GenusSixExistence.BrillNoetherRank.OddCompletionWitness G 1 (m − 1)` to the single divisor
  `E = m • u`, in the same unit presentation and the same shape (an odd scale, two chips);
* `OnceMarkedModel g G u`: the once-marked, leg-free analogue of the public
  `GenusSixExistence.Tripod.Closure.TripodModel`
  (`GenusSixExistence/BrillNoetherRank/Tripod/TripodModelDefs.lean`): a cubic
  connected loopless core of genus `g`, one slot split at the mark, an expansion of the marked
  core onto a small specification of `G` whose contracted slots are the forest and the zero mark
  piece, and a Laplacian equivalence at every scale carrying the mark to `u`.
-/

namespace DiagonalSecant

open DraismaVargas.Count DraismaVargas.Count.MarkedCount DraismaVargas.Count.MarkedCountGeneral
open DraismaVargas.Count.SegmentWalls (Frame)
open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.ExplicitPotential (Core)
open Utilities.Subdivision.CoreExpansion (ExpansionData)
open DraismaVargas.Count.DegenerateBigDivisor (degenerateLength)
open GenusSixExistence.Tripod.Gadget (subdivide)

variable {n p : ℕ}

/-! ## 1.  The tailed core -/

/-- The caterpillar type `c = a − 1` at the one mark: `Tailed` attaches a tail of genus `c + 1 = a`
(the tailed cores of the two-point ramified count, `DraismaVargas.Count.MarkedCountGeneral`). -/
def tailType (a : ℕ) : Fin 1 → ℕ := fun _ ↦ a - 1

/-- **The tailed core `H = Γ ∪ CT_a`** of the once-marked core `(Γ, u) = subdivide core s`: the
canonical tailed core of the two-point ramified count (`Tailed.canonical`). Cubic and connected
when `core` is (`Tailed.cubic`, `Tailed.connected`); it has loops (the bulbs), so it is **not**
a `Spec` core. -/
noncomputable def tailed (core : Core n p) (s : Fin p) (a : ℕ) :
    Tailed (subdivide core s) (onceMark n) (tailType a) :=
  Tailed.canonical _ _ _

/-- The once-marked core is marked-cubic. -/
theorem tailed_markedCubic {core : Core n p} (hCubic : core.Cubic) (s : Fin p) :
    IsMarkedCubic (subdivide core s) (onceMark n) :=
  isMarkedCubic_onceMarked hCubic s

/-- `H` has the headline degree `2d = g + a + 2` (`IsTailDegree`) when `(Γ, u)` has genus
`g = p + 1 − n` and `a ≥ 1`. -/
theorem tailed_isTailDegree {g a d : ℕ} (hg : p + 1 - n = g) (ha : 1 ≤ a)
    (hd : g + a + 2 = 2 * d) : IsTailDegree (n + 1) (p + 1) (tailType a) d := by
  unfold IsTailDegree
  simp only [tailType, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, one_mul]
  omega

/-! ## 1b.  Casting a typed frame along equalities of its type and degree -/

/-- Transport a typed frame along equalities of the type vector and the degree. -/
def TypedFrame.cast {k : ℕ} {core : Core n p} {mark : Fin k → Fin n} {types types' : Fin k → ℕ}
    {d d' : ℕ} (ht : types = types') (hd : d = d')
    (κ : TypedFrame core mark types d) : TypedFrame core mark types' d' :=
  ht ▸ hd ▸ κ

theorem TypedFrame.coordsAt_cast {k : ℕ} {core : Core n p} {mark : Fin k → Fin n}
    {types types' : Fin k → ℕ} {d d' : ℕ} (ht : types = types') (hd : d = d')
    (κ : TypedFrame core mark types d) (y : Fin p → ℚ) :
    (TypedFrame.cast ht hd κ).coordsAt y = κ.coordsAt y := by
  subst ht hd
  rfl

theorem TypedFrame.typedAbsMult_cast {k : ℕ} {core : Core n p} {mark : Fin k → Fin n}
    {types types' : Fin k → ℕ} {d d' : ℕ} (ht : types = types') (hd : d = d')
    (κ : TypedFrame core mark types d) :
    (TypedFrame.cast ht hd κ).typedAbsMult = κ.typedAbsMult := by
  subst ht hd
  rfl

/-- The lower type of the zero index is the full type `a` (for `a ≥ 1`): the type of the casts
`TypedFrame.cast` makes from the restriction of a full-type frame. -/
theorem lowerType_tailType_zero {a : ℕ} (ha : 1 ≤ a) :
    lowerType (tailType a) (fun _ ↦ 0) = ![a] := by
  funext j
  fin_cases j
  show a - 1 + 1 - 2 * ((0 : Fin ((a - 1 + 1) / 2 + 1)) : ℕ) = a
  rw [Fin.val_zero]
  omega

/-! ## 2.  Full-type frames of `H` -/

/-- **A full-type frame of `H`**: its restriction to `(Γ, u)` (`restrictTailed`) sheds no
sheet, `J = 0`, so it restricts to a typed frame of the full type `a = c + 1` in the full degree.
A frame predicate: `restrictTailed` reads the frame, not a request. -/
def IsFullType {k : ℕ} {core : Core n p} {mark : Fin k → Fin n} {c : Fin k → ℕ}
    (T : Tailed core mark c) (hc : IsMarkedCubic core mark) {d : ℕ} (f : Frame T.H d) : Prop :=
  ∀ j, ((restrictTailed T hc f).1 j : ℕ) = 0

/-- The lower index of a full-type frame is `0`. -/
theorem IsFullType.lowerIndex_eq {k : ℕ} {core : Core n p} {mark : Fin k → Fin n}
    {c : Fin k → ℕ} {T : Tailed core mark c} {hc : IsMarkedCubic core mark} {d : ℕ}
    {f : Frame T.H d} (h : IsFullType T hc f) : (restrictTailed T hc f).1 = fun _ ↦ 0 := by
  funext j
  exact Fin.ext (h j)

/-! ## 3.  The diagonal odd witness -/

/-- **The diagonal odd witness at `u`**: `OddCompletionWitness G 1 (m − 1)` of
`GenusSixExistence/BrillNoetherRank/Reduction.lean` restricted to the one divisor `E = m • u`
on the unit presentation of `G`: an odd scale `N` and an effective `F` of degree two on the
`N`-fold subdivision with `rank (embed (m • u) + F) ≥ 1`. For the theorem, `m = g − 3`. -/
def DiagonalOddWitness (G : CFGraph.{0}) (m : ℕ)
    (u : (UnitSubdivisionPresentation.spec G).graph.V) : Prop :=
  ∃ (N : ℕ) (hN : 0 < N), Odd N ∧
    ∃ F : CFDiv ((UnitSubdivisionPresentation.spec G).scale N hN).graph,
      effective F ∧ deg F = 2 ∧
        rank ((UnitSubdivisionPresentation.spec G).scale N hN).graph
          ((UnitSubdivisionPresentation.spec G).embed N hN (m • one_chip u) + F) ≥ 1

/-! ## 4.  The once-marked model -/

/-- **A once-marked model** of a graph `G` with a vertex `u`, in genus `g`: the leg-free,
one-mark form of the public `TripodModel`
(`GenusSixExistence/BrillNoetherRank/Tripod/TripodModelDefs.lean`, §6.2 of
`Research/genus-six-brill-noether-rank.md`).

* `core`: a cubic connected loopless core `G̃` of genus `g`, with `N = 2(g − 1)` vertices and
  `Q = 3(g − 1)` slots when it comes from the public reduction (not recorded);
* `slot`: the slot of `G̃` split at the mark; the marked core is `subdivide core slot`, whose mark
  is `Fin.last N = onceMark N 0`;
* `small`, `expansion`: the reduced specification of `G` and the expansion of the marked core
  onto it, whose contracted slots are the forest of `G̃` and the zero mark piece
  (`conditions`), sending the mark to the small core vertex `smallMark` (`fib_mark`);
* `transport`: at every scale the small specification is `G`'s subdivision, with the mark going
  to `u`. -/
structure OnceMarkedModel (g : ℕ) (G : CFGraph.{0})
    (u : (UnitSubdivisionPresentation.spec G).graph.V) where
  /-- The number of vertices of `G̃`. -/
  N : ℕ
  /-- The number of slots of `G̃`. -/
  Q : ℕ
  /-- The cubic core `G̃`. -/
  core : Core N Q
  cubic : core.Cubic
  connected : core.Connected
  loopless : ∀ i, core.tail i ≠ core.head i
  /-- `G̃` has genus `g`. -/
  genus_eq : Q + 1 - N = g
  /-- The slot of `G̃` carrying the mark. -/
  slot : Fin Q
  /-- The small specification: the reduced specification of `G`, split at the mark if the mark is
  a bivalent vertex. -/
  smallVertices : ℕ
  smallSlots : ℕ
  small : Spec smallVertices smallSlots
  smallConnected : small.core.Connected
  /-- The small core vertex carrying the mark. -/
  smallMark : Fin smallVertices
  /-- The expansion from the marked core onto the small specification. -/
  expansion : ExpansionData smallVertices smallSlots (N + 1) (Q + 1)
  bigCore_eq : expansion.bigCore = subdivide core slot
  conditions : expansion.Conditions small.core
  fib_mark : expansion.fib (Fin.last N) = smallMark
  /-- At every scale the small specification is `G`'s subdivision, with the mark going to `u`. -/
  transport : ∀ (k : ℕ) (hk : 0 < k), ∃ eqv : LaplacianEquiv (small.scale k hk).graph
      ((UnitSubdivisionPresentation.spec G).scale k hk).graph,
    eqv.mapDiv (small.embed k hk (one_chip (small.coreVertex smallMark))) =
      (UnitSubdivisionPresentation.spec G).embed k hk (one_chip u)

namespace OnceMarkedModel

variable {g : ℕ} {G : CFGraph.{0}} {u : (UnitSubdivisionPresentation.spec G).graph.V}

/-- **The actual request** on the marked core: the degenerate lengths of the expansion, zero on
the forest and on the zero mark piece, the small slot lengths on the retained slots. -/
noncomputable def request (M : OnceMarkedModel g G u) : Fin (M.Q + 1) → ℚ :=
  fun e ↦ (degenerateLength M.expansion M.small e : ℚ)

theorem request_nonneg (M : OnceMarkedModel g G u) : ∀ e, 0 ≤ M.request e :=
  fun _ ↦ Nat.cast_nonneg _

/-- The marked core of the model, as the typed count sees it. -/
abbrev markedCore (M : OnceMarkedModel g G u) : Core (M.N + 1) (M.Q + 1) :=
  subdivide M.core M.slot

/-- The marked core has genus `g`. -/
theorem markedCore_genus (M : OnceMarkedModel g G u) : M.Q + 1 + 1 - (M.N + 1) = g := by
  have := M.genus_eq
  omega

/-- The mark chips `m • ū` on the small specification. -/
noncomputable def markChips (M : OnceMarkedModel g G u) (m : ℕ) : CFDiv M.small.graph :=
  m • one_chip (M.small.coreVertex M.smallMark)

end OnceMarkedModel

end DiagonalSecant
