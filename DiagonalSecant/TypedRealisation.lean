module

public import DiagonalSecant.Defs
public import DiagonalSecant.TypedReach
public import DiagonalSecant.TypedMoments
public import DiagonalSecant.CMHairpin
public import GenusSixExistence.BrillNoetherRank.Tripod.RealisationProof

@[expose] public section

/-!
# Realisation of a closed typed member at an odd scale

This is the realisation of `Research/genus-six-brill-noether-rank.md` §7 in typed form, for one
mark and no legs.

## Why the public realisation is not re-instantiated

The public realisation (`GenusSixExistence/BrillNoetherRank/Tripod/RealisationProof.lean`)
cannot simply be re-instantiated at `(g − 1, n, p)`, for a reason of **type**, not of
mathematics:

* every public placement lemma (`DegeneratePlacement`, `DegenerateBigDivisor`,
  `DegenerateRealizationImage`, `PencilTransportProducer`, `CorePencilCoverProducer`,
  `RowHairpinPosition`, `ExpansionSeriesMoment`) takes a `FibreMember` of a core: a
  `FullDimensionalSourcePresentation` (square labelling of the **unmarked** stable paths) and a
  `CoreIdentification` (branch vertices of surviving valency `≥ 3` to core vertices). A typed
  frame `κ` of the two-point ramified count is neither: its mark `u_G` has surviving valency
  two, its rows are the marked rows (`MarkedStablePath`, cut at the mark), and its target has
  `p + 1` edges against the `p` unmarked rows. The tripod never met this: its legs make the
  marks trivalent.
* the alternative "regrow, then place" (`Regrowth.regrowTailed` makes `κ` an unmarked frame `f`
  of the tailed core `H`, with the same coordinates on the core columns and `|Mult f| =
  |Mult κ|`) is closed by **loops**: `H` carries the caterpillar's loops at the bulbs, and a
  `Spec` core is loopless (`Spec.ofCore` demands it; `D.bigSpec` too). A cubic loopless gadget
  attached at one point does not exist in genus one, so no loopless tailed core can replace `H`.

So the realisation of a typed member needs a **typed placement**: the marked twins of the
identification-dependent part of the public chain (row enumeration and orientation, the
placement of row vertices on the slots of a `Spec`, the pushed fibre, the descended tree
potential and the reach of the pencil, the hairpin positions and the slot moments), over
`MarkedStablePath` and `MarkedCoreIdentification`. The row-local public lemmas (`RowWalk`,
`RowChipCoefficient`, `EdgeDenominator`, `OddDenominator`) take a
`FullDimensionalSourcePresentation` too, but only to reach its labelling and path ends; stated
on a weaker "stable presentation", they would make most of the typed placement a
re-instantiation. The odd-denominator input is obtained through the regrowth, which is sound
for the **matrix** even though the placement is not: `OddDenominator.odd_adjusted_denominator`
on the regrown frame, read on the core columns by `coordsAt_restrictTailed`
(`CMDictionary.lean`).

## What is stated here

* `exists_placedFibre`: the typed analogue of `DegenerateBigDivisor.bigDivisor` at the root
  `x_u` pushed to the small specification, with its four receipts (effective; degree `g − 1`;
  at least `g − 3` chips at `ū`, because the mark `u_G` has local degree `≥ a + 1 = g − 3` by
  (D4′) and is placed at `ū`; rank at least one, by the typed pencil transport and the typed
  reach) and the slot-moment receipt (every slot moment divisible by every `2^e` dividing the
  scale, by the typed hairpin positions and `ExpansionSeriesMoment`), all at the member's own
  scale `k`.
* `witness_of_closed_typed`: the realisation, from `exists_placedFibre` by the public
  `RealisationProof.round_completion` (interior firing on `F = W − (g − 3)ū` alone and
  zero-budget rounding with the mark chips fixed) at the odd part of `k`.
-/

namespace DiagonalSecant

open DraismaVargas.Count DraismaVargas.Count.MarkedCount DraismaVargas.Count.MarkedCountGeneral
open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.ExplicitPotential (Core)
open GenusSixExistence.Tripod.Gadget (subdivide)
open GenusSixExistence.Tripod.RealisationProof (coreChips round_completion)
open DraismaVargas.Count.DegenerateBigDivisor (degenerateLength)
open Utilities.Subdivision.CoreExpansion (ExpansionData)
open DiagonalSecant.TypedPlacement DiagonalSecant.TypedImage DiagonalSecant.TypedReach
open DiagonalSecant.TypedMoments

variable {g : ℕ} {G : CFGraph.{0}} {u : (UnitSubdivisionPresentation.spec G).graph.V}

/-- **The placed fibre, generically**: for a typed frame over the big core of an expansion
datum, closed at the degenerate request, with the hairpin receipt at the image of the mark `j`
(`TypedMoments.HairpinReceipt`), the pushed fibre over that image is effective of
the frame's degree, carries the local degree of the mark at `coreVertex (D.fib (mark j))`, has
rank at least one, and has every slot moment divisible by every power of two dividing the scale.
The assembly of the six typed modules; `exists_placedFibre` is its instance at the model. -/
theorem exists_placedFibre_of_bigCore {n p N Q : ℕ} (D : ExpansionData n p N Q) (small : Spec n p)
    (hN : 0 < N) (hCond : D.Conditions small.core) (hConn : small.core.Connected)
    {m degree : ℕ} {mark : Fin m → Fin N} {types : Fin m → ℕ}
    (κ : TypedFrame D.bigCore mark types degree)
    (hClosed : Closed (degenerateLength D small) κ) (j : Fin m)
    (hReceipt : HairpinReceipt κ.fullDim (coords (degenerateLength D small) κ)
      (κ.markSource j).1.1) :
    ∃ (k : ℕ) (hk : 0 < k) (W : CFDiv (small.scale k hk).graph),
      effective W ∧ deg W = (degree : ℤ) ∧
        (markIndex κ.data (κ.markSource j) : ℤ) ≤ W ((small.scale k hk).coreVertex (D.fib (mark j))) ∧
        rank (small.scale k hk).graph W ≥ 1 ∧
        ∀ e : ℕ, 2 ^ e ∣ k → ∀ i, ((2 ^ e : ℕ) : ℤ) ∣
          DraismaVargas.Count.InteriorFiring.slotMoment (small.scale k hk) W i := by
  have hL := ExpansionData.loopless_of_conditions hCond
  refine ⟨scale (degenerateLength D small) κ, scale_pos _ _,
    pushed D small hN hL _ (scale_pos _ _) κ hClosed rfl (κ.markSource j).1.1,
    pushed_effective D small hN hL _ _ κ hClosed rfl _, deg_pushed D small hN hL _ _ κ hClosed rfl _,
    markIndex_le_pushed D small hN hL _ _ κ hClosed rfl j,
    rank_pushed_ge_one D small hN hL _ _ κ hClosed rfl hCond hConn _, fun e he i ↦
    dvd_slotMoment_pushed D small hN hL _ _ κ hClosed rfl hCond hReceipt e he i⟩

/-- **The placed fibre over the mark image** (the typed form of Proposition 7.4 and §7.4 of
`Research/genus-six-brill-noether-rank.md`). For a closed typed member `κ` of type `g − 4` in
degree `g − 1` at the actual request of a once-marked model, of odd typed multiplicity, there is
a scale `k` and an effective divisor `W` of degree `g − 1` on `small.scale k` — the fibre of `κ`
over `x_u`, placed and pushed along the expansion — with at least `g − 3` chips at `ū`, of rank
at least one, and with every slot moment divisible by every power of two dividing `k`. -/
theorem exists_placedFibre (M : OnceMarkedModel g G u) (hg5 : 5 ≤ g)
    (κ : TypedFrame M.markedCore (onceMark M.N) ![g - 4] (g - 1))
    (hClosed : ∀ col, 0 ≤ κ.coordsAt M.request col)
    (hOdd : ∃ m : ℕ, Odd m ∧ κ.typedAbsMult = m) :
    ∃ (k : ℕ) (hk : 0 < k) (W : CFDiv (M.small.scale k hk).graph),
      effective W ∧ deg W = ((g - 1 : ℕ) : ℤ) ∧
        ((g - 3 : ℕ) : ℤ) ≤ W ((M.small.scale k hk).coreVertex M.smallMark) ∧
        rank (M.small.scale k hk).graph W ≥ 1 ∧
        ∀ e : ℕ, 2 ^ e ∣ k → ∀ j, ((2 ^ e : ℕ) : ℤ) ∣
          DraismaVargas.Count.InteriorFiring.slotMoment (M.small.scale k hk) W j := by
  -- The model-specific input, the hairpin receipt at `x_u`, proved on `κ` over the marked core
  -- `subdivide core slot` through the regrowth (`CMHairpin.lean`).
  have hReceipt : HairpinReceipt κ.fullDim (κ.coordsAt M.request) (κ.markSource 0).1.1 :=
    fun path i hi ↦ CM.weighted_prefix_mem_of_model M hg5 κ hOdd path 0 hi
  have hmark : g - 4 + 1 ≤ markIndex κ.data (κ.markSource 0) := (κ.typed 0).2
  -- The generic assembly, over the big core of the expansion, reached by `bigCore_eq`.
  have key : ∀ (core : Core (M.N + 1) (M.Q + 1)) (hcore : M.expansion.bigCore = core)
      (κ : TypedFrame core (onceMark M.N) ![g - 4] (g - 1)),
      (∀ col, 0 ≤ κ.coordsAt M.request col) →
      HairpinReceipt κ.fullDim (κ.coordsAt M.request) (κ.markSource 0).1.1 →
      g - 4 + 1 ≤ markIndex κ.data (κ.markSource 0) →
      ∃ (k : ℕ) (hk : 0 < k) (W : CFDiv (M.small.scale k hk).graph),
        effective W ∧ deg W = ((g - 1 : ℕ) : ℤ) ∧
          ((g - 3 : ℕ) : ℤ) ≤ W ((M.small.scale k hk).coreVertex M.smallMark) ∧
          rank (M.small.scale k hk).graph W ≥ 1 ∧
          ∀ e : ℕ, 2 ^ e ∣ k → ∀ j, ((2 ^ e : ℕ) : ℤ) ∣
            DraismaVargas.Count.InteriorFiring.slotMoment (M.small.scale k hk) W j := by
    intro core hcore κ hClosed hReceipt hmark
    subst hcore
    obtain ⟨k, hk, W, hW, hdeg, hmark', hrank, hmom⟩ :=
      exists_placedFibre_of_bigCore M.expansion M.small (Nat.succ_pos _) M.conditions
        M.smallConnected κ hClosed 0 hReceipt
    refine ⟨k, hk, W, hW, hdeg, ?_, hrank, hmom⟩
    have hfib : M.expansion.fib (onceMark M.N 0) = M.smallMark := M.fib_mark
    rw [hfib] at hmark'
    refine le_trans ?_ hmark'
    exact_mod_cast (by omega : g - 3 ≤ markIndex κ.data (κ.markSource 0))
  exact key M.markedCore M.bigCore_eq κ hClosed hReceipt hmark

/-- **The realisation** (Theorem 7.5 of `Research/genus-six-brill-noether-rank.md`, typed
form). A closed typed
member of odd typed multiplicity at the actual request of a once-marked model of `(G, u)`
completes `(g − 3)ū` by two chips to a divisor of rank at least one on an odd regular
subdivision of the small specification. -/
theorem witness_of_closed_typed (M : OnceMarkedModel g G u) (hg5 : 5 ≤ g)
    (κ : TypedFrame M.markedCore (onceMark M.N) ![g - 4] (g - 1))
    (hClosed : ∀ col, 0 ≤ κ.coordsAt M.request col)
    (hOdd : ∃ m : ℕ, Odd m ∧ κ.typedAbsMult = m) :
    ∃ (N : ℕ) (hN : 0 < N), Odd N ∧
      ∃ F : CFDiv (M.small.scale N hN).graph, effective F ∧ deg F = 2 ∧
        rank (M.small.scale N hN).graph
          (M.small.embed N hN (M.markChips (g - 3)) + F) ≥ 1 := by
  classical
  obtain ⟨k, hk, W, hW, hdeg, hmark, hrank, hmom⟩ := exists_placedFibre M hg5 κ hClosed hOdd
  -- the odd part of the scale
  obtain ⟨a, u, hOddU, hEq⟩ := Nat.exists_eq_two_pow_mul_odd hk.ne'
  have hu : 0 < u := hOddU.pos
  subst hEq
  -- the mark chips as `coreChips`, so that no concrete vertex type is unfolded
  have hmc : coreChips M.small (fun _ : Fin (g - 3) ↦ M.smallMark) = M.markChips (g - 3) := by
    unfold coreChips OnceMarkedModel.markChips
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hcc : M.small.embed (2 ^ a * u) hk (coreChips M.small (fun _ : Fin (g - 3) ↦ M.smallMark)) =
      (g - 3) • one_chip ((M.small.scale (2 ^ a * u) hk).coreVertex M.smallMark) := by
    rw [GenusSixExistence.Tripod.RealisationProof.embed_coreChips]
    unfold coreChips
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  -- the two chips
  set F : CFDiv (M.small.scale (2 ^ a * u) hk).graph :=
    W - M.small.embed (2 ^ a * u) hk (coreChips M.small (fun _ : Fin (g - 3) ↦ M.smallMark)) with hF
  have hFapply : ∀ y, F y = W y - (g - 3) • one_chip
      ((M.small.scale (2 ^ a * u) hk).coreVertex M.smallMark) y := by
    intro y
    rw [hF, hcc]
    rfl
  have hFeff : effective F := by
    intro y
    rw [hFapply]
    by_cases hy : y = (M.small.scale (2 ^ a * u) hk).coreVertex M.smallMark
    · rw [hy, one_chip_apply_v, nsmul_eq_mul, mul_one]
      have := hmark
      omega
    · rw [one_chip_apply_other' _ _ hy, smul_zero, sub_zero]
      exact hW y
  have hFdeg : deg F = 2 := by
    rw [hF, map_sub, hdeg, hcc, map_nsmul, deg_one_chip, nsmul_eq_mul, mul_one]
    have h3 : ((g - 3 : ℕ) : ℤ) = (g : ℤ) - 3 := by omega
    have h1 : ((g - 1 : ℕ) : ℤ) = (g : ℤ) - 1 := by omega
    rw [h3, h1]
    ring
  have hFmom : ∀ j, ((2 ^ a : ℕ) : ℤ) ∣
      DraismaVargas.Count.InteriorFiring.slotMoment (M.small.scale (2 ^ a * u) hk) F j := by
    intro j
    have hsame : DraismaVargas.Count.InteriorFiring.slotMoment (M.small.scale (2 ^ a * u) hk) F j =
        DraismaVargas.Count.InteriorFiring.slotMoment (M.small.scale (2 ^ a * u) hk) W j := by
      unfold DraismaVargas.Count.InteriorFiring.slotMoment
      refine Finset.sum_congr rfl fun o _ ↦ ?_
      rw [hFapply, one_chip_apply_other' _ _ (by exact Sum.inr_ne_inl), smul_zero, sub_zero]
    rw [hsame]
    exact hmom a (Dvd.intro u rfl) j
  have hFrank : rank (M.small.scale (2 ^ a * u) hk).graph
      (M.small.embed (2 ^ a * u) hk (coreChips M.small (fun _ : Fin (g - 3) ↦ M.smallMark)) + F) ≥
        1 := by
    rw [hF, add_sub_cancel]
    exact hrank
  -- interior firing and zero-budget rounding at the odd part
  obtain ⟨F', hF', hdeg', hrank'⟩ :=
    round_completion M.small (fun _ : Fin (g - 3) ↦ M.smallMark) u a hu hk F hFeff hFdeg hFmom hFrank
  rw [hmc] at hrank'
  exact ⟨u, hu, hOddU, F', hF', hdeg', hrank'⟩

end DiagonalSecant
