import DraismaVargasCount.M11StarExhaustionProof
import DraismaVargasCount.W2R1StarExhaustionProof
import DraismaVargasCount.W2PStarExhaustionProof
import DraismaVargasCount.W3Nd2StarExhaustionProof
import DraismaVargasCount.W3Nd3StarExhaustionProof
import DraismaVargasCount.W4NonDiscreteStarExhaustionProof
import DraismaVargasCount.W3FourStarExhaustionProof
import DraismaVargasCount.W2M1kStarExhaustionProof
import DraismaVargasCount.W2MkkStarExhaustionProof
import DraismaVargasCount.W3ShiftStarExhaustionProof

/-!
# The trivalent walls at genus six: the in-cone supply from the ten family clauses

Inside the cone of one cubic core, the parity of the open odd count survives a codimension-one
wall when every star of the wall has an even number of classes of odd multiplicity
(`RegrowthWallInput.inConeSupplySimple_of_familyStarParity`). The stars are split by the ten wall
types of Draisma--Vargas Part I (`ClassifiedContinuation.SourceCase`), and the star parity of each
family is proved in its own module (`W4NonDiscreteStarExhaustionProof`,
`W3FourStarExhaustionProof`, ..., `W3ShiftStarExhaustionProof`). This file collects the ten
clauses.

* `familyStarParity_of_proved`, `familyStarParity_of_ne_w3Shift`, `familyStarParity_all`: the
  clause for every tag, at genus six in degree four.
* `inConeSupplySimple_genusSix`: `SimpleWallSupply.InConeSupplySimple` at genus six in degree
  four, with no hypothesis. This is step 2 of the genus-six assembly
  (`Assembly.trivalentWalls_genusSix`).
-/

namespace DraismaVargas.Count.StarSupplyAssembly

open DraismaVargas.LocalCases.ClassifiedContinuation (SourceCase)
open DraismaVargas.Count.RegrowthWallInput (FamilyStarParity)

/-- **Seven family clauses, collected.**  Every tag except `w3Shift`, `w2M1k` and `w2Mkk`
has its genus-six star parity as a theorem with no hypothesis. -/
theorem familyStarParity_of_proved (tag : SourceCase)
    (h3 : tag ≠ .w3Shift) (h1k : tag ≠ .w2M1k) (hkk : tag ≠ .w2Mkk) :
    FamilyStarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3) tag := by
  cases tag with
  | w4 => exact W4NonDiscreteStarExhaustionProof.familyStarParity_w4
  | w3Four => exact W3FourStarExhaustionProof.familyStarParity_w3Four
  | w3Shift => exact absurd rfl h3
  | w3Nd3CoarseFine => exact W3Nd3StarExhaustionProof.familyStarParity_w3Nd3
  | w3Nd2CoarseFine => exact W3Nd2StarExhaustionProof.familyStarParity_w3Nd2
  | w2M11 => exact M11StarExhaustionProof.familyStarParity_w2M11
  | w2M1k => exact absurd rfl h1k
  | w2Mkk => exact absurd rfl hkk
  | w2P => exact W2PStarExhaustionProof.familyStarParity_w2P
  | w2R1 => exact W2R1StarExhaustionProof.familyStarParity_w2R1

/-- **Nine family clauses, collected.**  Every tag except `w3Shift` has its genus-six star
parity as a theorem with no hypothesis. -/
theorem familyStarParity_of_ne_w3Shift (tag : SourceCase) (h3 : tag ≠ .w3Shift) :
    FamilyStarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3) tag := by
  by_cases e1 : tag = .w2M1k
  · exact e1 ▸ W2M1kStarExhaustionProof.familyStarParity_w2M1k
  by_cases ek : tag = .w2Mkk
  · exact ek ▸ W2MkkStarExhaustionProof.familyStarParity_w2Mkk
  exact familyStarParity_of_proved tag h3 e1 ek

/-- **All ten family clauses.**  Every source-case tag has its genus-six star parity as a
theorem with no hypothesis. -/
theorem familyStarParity_all (tag : SourceCase) :
    FamilyStarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3) tag := by
  by_cases e : tag = .w3Shift
  · exact e ▸ W3ShiftStarExhaustionProof.familyStarParity_w3Shift
  exact familyStarParity_of_ne_w3Shift tag e

/-- **The in-cone supply at genus six, with no hypothesis**: the trivalent walls of
`Assembly.trivalentWalls_genusSix`. -/
theorem inConeSupplySimple_genusSix :
    SimpleWallSupply.InConeSupplySimple (2 + 2) (4 * 2 + 2) (6 * 2 + 3) :=
  RegrowthWallInput.inConeSupplySimple_of_familyStarParity familyStarParity_all

end DraismaVargas.Count.StarSupplyAssembly
