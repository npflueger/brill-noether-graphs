module

public import DraismaVargasCount.SwitchingParity

@[expose] public section

/-!
# From a signed multiplicity balance to the star-parity clause

**Source.**  Vargas, Part II (arXiv:2609.09109), the balancing condition
`prop-signed-mult`.

## What this file is for

`Count/WallSwitchingBridge.lean`'s `countLink_source_target_of_even_stars`
carries one hypothesis about stars, and it is this:

    hstar : ∀ (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (w : Regrowth core (S.request t) degree),
      Even (Nat.card {c : GeometricFibre core (S.request t) degree //
        GeometricStar.IsStarClass (nondegenerate_segment hsrc htgt ht0 ht1) w c ∧ c.IsOdd})

The balancing identities of the wall families come in a *different* shape:
`Σ_q Mult φ_q = 0` over a **prescribed finite index** of outgoing members at one wall
(`W4UnitBalance.sum_signedMult_canonical_eq_zero`, indexed by `pairing : Fin 3`).
This file is the reindexing that turns the second into the first, and nothing
else.  It proves no balance and builds no star.

## What is proved

* `card_starClass_odd_eq` -- the subtype the bridge counts is the subtype of
  *odd classes of the star*: `GeometricStar.Star.equivSubtype` read on the
  `IsOdd` predicate.  No hypothesis.
* `even_card_starClass_odd_of_even_sum` -- if the total `multNat` over the star
  is even, the bridge's clause holds.  Only the parity of the sum is used.
* `even_card_starClass_odd_of_equiv` -- the same through **any** finite
  indexing `ι ≃ GeometricStar.Star hy wall` of the star.  This is the
  reindexing lemma: a balance stated over a prescribed index set is usable
  exactly when that index set is put in bijection with the star.
* `even_sum_num_natAbs_of_sum_eq_zero` -- the mod-two step, over an arbitrary
  finite index: a vanishing sum of **integral** rationals has an even sum of
  numerator absolute values.  Integrality is a hypothesis here and is *not*
  free: without it the numerators do not add.
* `even_card_starClass_odd_w4` -- **the assembled statement at a discrete
  four-valent wall**: given the candidate package of `W4WallExhaustion`
  (`W4WallExhaustion.Candidate` at each of the three pairings) and a vanishing
  signed-multiplicity sum over *those three candidates' own presentations*, the
  bridge's `hstar` clause holds at that wall.  Integrality is discharged by
  `Count.isIntegralMultiplicity`, which is unconditional on a
  `FullDimensionalSourcePresentation`.

## What is not proved here

* **No balance is proved.**  `hbal` is a hypothesis of
  `even_card_starClass_odd_w4`, and it is stated on
  `(cand q).fullDim.labelling.presentation`, i.e. on the presentations carried
  by the *star's* candidate package.  `Count.W4UnitBalance` and
  `Count.W4FullDimensionalBalance` prove a vanishing sum on
  `(W4CommonBalance.labelling input initial q).presentation`, i.e. on the
  presentations of the outgoing family that an
  `LocalCases.W4StableSource.AuxR0SourceInput` builds.  Nothing here identifies those
  two `Fin 3`-indexed families at an arbitrary wall; that identification is the work of
  the star censuses (`StarCensusEngine`, `W4StarParity`).
* **No star is exhausted here.**  `even_card_starClass_odd_w4` takes `hFour`,
  `hDiscrete`, the `FourStar` and the three candidates and hands them straight
  to `W4WallExhaustion.starEquiv`; every caveat of that exhaustion applies
  unchanged, and the other nine families are untouched -- the `Fin 3` is the
  three `2+2` pairings of four occurrences and has no counterpart at another
  arity.
* **Nothing here connects the star to the classes whose openness changes.**
  `GeometricStar.Star hy wall` is a set of classes at one nondegenerate request, while
  `CountTransportLink.switchingCount` is about a *pair* of requests.  So nothing here
  produces `Even (switchingCount …)`.  What is produced is exactly the `hstar` clause of
  `WallSwitchingBridge.countLink_source_target_of_even_stars`, which turns it into the
  parity of the count across the wall.
* **No schedule, no wall of a schedule.**  Nothing says the walls of a
  `Count.CountSchedule.Schedule` are four-valent or discrete.
* `multNat` is `Count.GeometricFibre.multNat`, the unsigned multiplicity; the
  signed multiplicity enters only through `signedMult`'s numerator, and
  `Count.ConeSide`'s sign law is not used.

## Consumers

The star censuses of the wall families (`StarCensusEngine`, `W4StarParity`,
`M11StarParityFree`, `W2R1StarCensusProof`, `W3Nd2StarCensusProof`), which feed the
trivalent walls (step 2 of the genus-six assembly).
-/

namespace DraismaVargas.Count.StarParityFromBalance

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.WallStar (Regrowth Nondegenerate)
open DraismaVargas.LocalCases.W4TargetPairings (FourStar)
open DraismaVargas.Count.W4WallExhaustion (mergeVertex Candidate)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  {hy : Nondegenerate y} {wall : Regrowth core y degree}

/-! ## 1.  The bridge's subtype is the odd part of the star -/

/-- **What `WallSwitchingBridge`'s `hstar` actually counts.**  The classes of
the geometric fibre that are star classes of `wall` and carry odd multiplicity
are, as a finite type, the odd elements of `GeometricStar.Star hy wall`.  This
is `GeometricStar.Star.equivSubtype` read through the `IsOdd` predicate; no
hypothesis enters. -/
theorem card_starClass_odd_eq :
    Nat.card {c : GeometricFibre core y degree //
        GeometricStar.IsStarClass hy wall c ∧ c.IsOdd} =
      Nat.card {s : GeometricStar.Star hy wall // (GeometricStar.Star.toFibre s).IsOdd} := by
  refine (Nat.card_congr ?_).symm
  exact (Equiv.subtypeEquiv (GeometricStar.Star.equivSubtype hy wall)
    (fun _ ↦ Iff.rfl)).trans (Equiv.subtypeSubtypeEquivSubtypeInter _ _)

/-- **The parity clause from a parity of multiplicities over the star.**  Only
the parity of `Σ Mult` is used; no member is weighted and no class is named. -/
theorem even_card_starClass_odd_of_even_sum
    (hsum : Even (∑ s : GeometricStar.Star hy wall, (GeometricStar.Star.toFibre s).multNat)) :
    Even (Nat.card {c : GeometricFibre core y degree //
      GeometricStar.IsStarClass hy wall c ∧ c.IsOdd}) := by
  classical
  rw [card_starClass_odd_eq, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.even_sum_iff_even_card_odd] at hsum
  convert hsum using 2
  exact Finset.filter_congr fun _ _ ↦ Iff.rfl

/-- **The reindexing lemma.**  A multiplicity balance stated over a prescribed
finite index `ι` delivers the bridge's parity clause exactly when `ι` has been
put in bijection with the star.  Supplying that bijection is the work of the star
exhaustion and census: the balance alone does not know what its index set is. -/
theorem even_card_starClass_odd_of_equiv {ι : Type*} [Fintype ι]
    (e : ι ≃ GeometricStar.Star hy wall)
    (hsum : Even (∑ i, (GeometricStar.Star.toFibre (e i)).multNat)) :
    Even (Nat.card {c : GeometricFibre core y degree //
      GeometricStar.IsStarClass hy wall c ∧ c.IsOdd}) := by
  refine even_card_starClass_odd_of_even_sum ?_
  rwa [← Equiv.sum_comp e fun s ↦ (GeometricStar.Star.toFibre s).multNat]

/-! ## 2.  The mod-two step, with integrality displayed -/

/-- **`Σ m = 0` with every `m` integral forces `Σ |num m|` even.**  This is
`SwitchingParity.even_sum_natAbs_of_sum_eq_zero` at the level the balancing
identities state, where the summands are rationals known to be integers.  The
integrality hypothesis is doing real work: the numerator map is not additive on
general rationals. -/
theorem even_sum_num_natAbs_of_sum_eq_zero {ι : Type*} [Fintype ι] (m : ι → ℚ)
    (hint : ∀ i, ∃ value : ℤ, m i = (value : ℚ)) (hsum : ∑ i, m i = 0) :
    Even (∑ i, (m i).num.natAbs) := by
  classical
  choose value hvalue using hint
  have hnum : ∀ i, (m i).num = value i := fun i ↦ by rw [hvalue i, Rat.num_intCast]
  have hzero : ∑ i, value i = 0 := by
    have hcast : ((∑ i, value i : ℤ) : ℚ) = 0 := by
      push_cast
      simpa only [hvalue] using hsum
    exact_mod_cast hcast
  simpa only [hnum] using SwitchingParity.even_sum_natAbs_of_sum_eq_zero value hzero

/-! ## 3.  The discrete four-valent wall -/

/-- **The star multiplicity at a pairing is the candidate's own multiplicity.**
`W4WallExhaustion.starEquiv` sends `q` to the class of `(cand q).starMember`,
whose frame carries `(cand q).fullDim`; `GeometricFibre.multNat` of that class
is `fdAbsMultNat` of that presentation, which is
`(signedMult …).num.natAbs` by definition. -/
theorem multNat_starEquiv
    (hFour : (GluingDatum.incidentEdges (mergeVertex wall)).card = 4)
    (hDiscrete : wall.limit.vertexPartition (mergeVertex wall) = SheetPartition.discrete degree)
    (star : FourStar (wall.frame.limitTarget wall.column) (mergeVertex wall))
    (cand : ∀ q : Fin 3, Candidate hy wall hDiscrete star q) (q : Fin 3) :
    (GeometricStar.Star.toFibre
        (W4WallExhaustion.starEquiv hFour hDiscrete star cand q)).multNat =
      (signedMult (cand q).fullDim.labelling.presentation).num.natAbs := rfl

/-- **The bridge's star clause at a discrete four-valent wall, from a vanishing
signed sum over the three candidates.**  Every hypothesis is displayed:
`hFour`, `hDiscrete`, `FourStar` and the candidate package of `W4WallExhaustion`, and a
vanishing signed multiplicity sum stated on *those candidates' own*
presentations.  Integrality is not assumed -- it is
`Count.isIntegralMultiplicity`, unconditional on a full-dimensional
presentation. -/
theorem even_card_starClass_odd_w4
    (hFour : (GluingDatum.incidentEdges (mergeVertex wall)).card = 4)
    (hDiscrete : wall.limit.vertexPartition (mergeVertex wall) = SheetPartition.discrete degree)
    (star : FourStar (wall.frame.limitTarget wall.column) (mergeVertex wall))
    (cand : ∀ q : Fin 3, Candidate hy wall hDiscrete star q)
    (hbal : ∑ q : Fin 3, signedMult (cand q).fullDim.labelling.presentation = 0) :
    Even (Nat.card {c : GeometricFibre core y degree //
      GeometricStar.IsStarClass hy wall c ∧ c.IsOdd}) := by
  refine even_card_starClass_odd_of_equiv
    (W4WallExhaustion.starEquiv hFour hDiscrete star cand) ?_
  have h := even_sum_num_natAbs_of_sum_eq_zero
    (fun q : Fin 3 ↦ signedMult (cand q).fullDim.labelling.presentation)
    (fun q ↦ isIntegralMultiplicity (cand q).fullDim) hbal
  simpa only [multNat_starEquiv hFour hDiscrete star cand] using h

end DraismaVargas.Count.StarParityFromBalance
