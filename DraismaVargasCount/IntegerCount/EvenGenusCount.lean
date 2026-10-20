module

public import DraismaVargasCount.IntegerCount.WallCrossing
public import DraismaVargasCount.IntegerCount.StarBalanceW4
public import DraismaVargasCount.IntegerCount.StarBalanceW3
public import DraismaVargasCount.IntegerCount.StarBalanceW2
public import DraismaVargasCount.IntegerCount.TypeChange
public import DraismaVargasCount.EvenGenusParity

@[expose] public section

/-!
# The Draisma--Vargas count in every even genus at least six

Over a general metric graph of even genus `g`, the tropical morphisms of degree `g/2 + 1` to
metric trees, counted with multiplicity, number the Catalan number `C_{g/2}` (A. Vargas,
*Catalan-many tropical morphisms to trees; Part II: A space and a count*, arXiv:2609.09109, the
main theorem, in its fibre form `fiber-count`).

**Theorem** (`openMultCount_eq_catalan`).  For every `k ≥ 2`, over every connected cubic core
of genus `2k + 2` and every positive general request `y`, in the sense of
`CountSchedule.C34`, the open classes in degree `k + 2` satisfy

  `Σ_{c open} |Mult c| = openMultCount core y (k + 2) = catalan (k + 1)`.

It is the integer twin of `EvenGenusParity.openOddCount_mod_two`, with exactly its hypotheses,
and it implies it (`openOddCount_mod_two_of_integer`).

## The proof

`EvenGenusParity`, steps 1 to 5, with every parity input replaced by a sum:

1. **Base count** (`openMultCount_caterpillar`): over `catCore k` there are `catalan (k + 1)`
   open classes, each of multiplicity one (`EvenGenusParity.baseCount`). Already integer.
2. **The caterpillar is a base core**: `EvenGenusParity.catCubicCore`, reused.
3. **Trivalent walls** (`trivalentWalls`): `InConeSupplySum`, from the balance by sides of every
   star (`familyStarBalance`, from the four-, three- and two-valent walls of `StarBalanceW4`,
   `StarBalanceW3` and `StarBalanceW2`) through the integer crossing
   (`inConeSupplySum_of_familyStarBalance`).
4. **Type changes** (`IntegerCount.typeChanges`): `TypeChangeSupplySum`, from the same census
   supply as the parity proof.
5. **Transport** (`eq_of_positiveGeneral`): the weighted count is the same at every positive
   general site of cubic cores with the same indices.  It is an equality, so no contraposition.

## Corollaries

* `openOddCount_mod_two_of_integer`: the public mod-2 theorem, recovered.
* `exists_open_class`: at every positive general request there is an open class (in the open
  orthant), including where `catalan (k + 1)` is even.
-/

namespace DraismaVargas.Count.IntegerCount

open DraismaVargas.Count
open DraismaVargas.Count.FibreCaterpillar (catCore)
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore)
open DraismaVargas.LocalCases.ClassifiedContinuation (SourceCase)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)

/-! ## 1.  The base count -/

/-- **The base count, integer form.**  Over the caterpillar of loops `catCore k`, at every
positive request, the weighted count in degree `k + 2` is `catalan (k + 1)`: there are that many
open classes (`BallotEndSwapGeneral.card_open`) and every member has multiplicity one
(`BallotEndSwapGeneral.absMult_eq_one`), both through `EvenGenusParity.baseCount`. -/
theorem openMultCount_caterpillar {k : ℕ} (hk : 2 ≤ k) {request : Fin (6 * k + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot) :
    openMultCount (catCore k) request (k + 2) = catalan (k + 1) := by
  obtain ⟨hCard, hMult⟩ := EvenGenusParity.baseCount hk hRequest
  rw [← hCard]
  refine openMultCount_eq_card_of_multNat_eq_one fun c _ ↦ ?_
  obtain ⟨mem, rfl⟩ := GeometricFibre.cls_surjective c
  have h := GeometricFibre.absMult_eq_multNat (GeometricFibre.cls mem)
  rw [GeometricFibre.absMult_cls, hMult mem] at h
  exact_mod_cast h.symm

/-! ## 2.  The trivalent walls -/

/-- **All ten wall families are balanced by sides, at every degree, core size and request.**
The integer twin of `EvenGenusParity.familyStarParity`. -/
theorem familyStarBalance (degree n p : ℕ) (tag : SourceCase) :
    FamilyStarBalance degree n p tag := by
  cases tag with
  | w4 => exact familyStarBalance_w4 degree n p
  | w3Four => exact familyStarBalance_w3Four degree n p
  | w3Shift => exact familyStarBalance_w3Shift degree n p
  | w3Nd3CoarseFine => exact familyStarBalance_w3Nd3 degree n p
  | w3Nd2CoarseFine => exact familyStarBalance_w3Nd2 degree n p
  | w2M11 => exact familyStarBalance_w2M11 degree n p
  | w2M1k => exact familyStarBalance_w2M1k degree n p
  | w2Mkk => exact familyStarBalance_w2Mkk degree n p
  | w2P => exact familyStarBalance_w2P degree n p
  | w2R1 => exact familyStarBalance_w2R1 degree n p

/-- **The trivalent walls, integer form, at every degree and size.**  The integer twin of
`EvenGenusParity.trivalentWalls`. -/
theorem trivalentWalls (degree n p : ℕ) : InConeSupplySum degree n p :=
  inConeSupplySum_of_familyStarBalance (familyStarBalance degree n p)

/-! ## 3.  The theorem -/

/-- **The Draisma--Vargas count in every even genus at least six.**  For every `k ≥ 2`, over
every connected cubic core of genus `2k + 2` and every positive general request, the open
classes in degree `k + 2` carry total multiplicity `catalan (k + 1)`.  "General" is the form
`CountSchedule.C34` uses: no frame loses a coordinate at the request.  The hypotheses are
exactly those of `EvenGenusParity.openOddCount_mod_two`. -/
theorem openMultCount_eq_catalan {k : ℕ} (hk : 2 ≤ k) {n p : ℕ} (core : Core n p)
    (hCubic : core.Cubic) (hConnected : core.Connected) (hGenus : p + 1 - n = 2 * k + 2)
    (y : Fin p → ℚ) (hPositive : ∀ i, 0 < y i)
    (hGeneral : ∀ (f : Frame core (k + 2)) (col : Fin p), f.coordsAt y col ≠ 0) :
    openMultCount core y (k + 2) = catalan (k + 1) := by
  obtain ⟨rfl, rfl⟩ := EvenGenusParity.index_of_genus hCubic hGenus
  obtain ⟨request, hRequest⟩ := SimpleWallSupply.exists_positiveGeneral (catCore k) (k + 2)
  rw [← openMultCount_caterpillar hk hRequest.1]
  exact eq_of_positiveGeneral (trivalentWalls _ _ _) (typeChanges (by omega) (by omega))
    (by omega) (EvenGenusParity.catCubicCore k) ⟨core, hCubic, hConnected⟩ request y hRequest
    ⟨hPositive, hGeneral⟩

/-! ## 4.  Corollaries -/

/-- **The integer count implies the public mod-2 count** (`EvenGenusParity.openOddCount_mod_two`),
through `openMultCount_mod_two`.  A consistency check of the definitions. -/
theorem openOddCount_mod_two_of_integer {k : ℕ} (hk : 2 ≤ k) {n p : ℕ} (core : Core n p)
    (hCubic : core.Cubic) (hConnected : core.Connected) (hGenus : p + 1 - n = 2 * k + 2)
    (y : Fin p → ℚ) (hPositive : ∀ i, 0 < y i)
    (hGeneral : ∀ (f : Frame core (k + 2)) (col : Fin p), f.coordsAt y col ≠ 0) :
    GeometricFibre.openOddCount core y (k + 2) % 2 = catalan (k + 1) % 2 := by
  rw [← openMultCount_mod_two,
    openMultCount_eq_catalan hk core hCubic hConnected hGenus y hPositive hGeneral]

/-- **An open class exists at every positive general request**, in every even genus at least
six, including those where `catalan (k + 1)` is even (genus eight: `C₄ = 14`), where the mod-2
count gives nothing. -/
theorem exists_open_class {k : ℕ} (hk : 2 ≤ k) {n p : ℕ} (core : Core n p)
    (hCubic : core.Cubic) (hConnected : core.Connected) (hGenus : p + 1 - n = 2 * k + 2)
    (y : Fin p → ℚ) (hPositive : ∀ i, 0 < y i)
    (hGeneral : ∀ (f : Frame core (k + 2)) (col : Fin p), f.coordsAt y col ≠ 0) :
    ∃ c : GeometricFibre core y (k + 2), c.Open := by
  by_contra hNone
  have hEmpty : IsEmpty {c : GeometricFibre core y (k + 2) // c.Open} :=
    ⟨fun c ↦ hNone ⟨c.1, c.2⟩⟩
  have hZero : openMultCount core y (k + 2) = 0 := by
    unfold openMultCount
    exact finsum_of_isEmpty _
  rw [openMultCount_eq_catalan hk core hCubic hConnected hGenus y hPositive hGeneral] at hZero
  have hcb := succ_mul_catalan_eq_centralBinom (k + 1)
  rw [hZero, mul_zero] at hcb
  exact Nat.centralBinom_ne_zero (k + 1) hcb.symm

end DraismaVargas.Count.IntegerCount
