import LowGenus.ConfigurationThree

/-!
# The Atanasov--Ranganathan construction on row 13

Row 13 consists of two `K₄`-minus-edge blocks joined along the two missing
edges.  Put one chip on each of `2,3,6,7`.  The chip-free core vertices form
the two edges `0--4` and `1--5`; together with their four incident chip
vertices, each is configuration 3 of Atanasov--Ranganathan, Proposition 5.1.

The calculation itself is core generic and lives in
`LowGenus/ConfigurationThree.lean`.  All this file does
is name the row's lookup tables and check the incidence facts that file asks
for.
-/

namespace AtanasovRanganathan.GenusFiveRow13

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Configurations
open GenusFiveCoreAtlas
open ConfigurationThree

/-! ## The row-13 lookup tables -/

/-- The other chip-free centre in the same configuration-3 component. -/
def partner : Fin 8 → Fin 8
  | 0 => 4
  | 4 => 0
  | 1 => 5
  | 5 => 1
  | v => v

/-- The first arm from each chip-free centre to a chip vertex. -/
def firstArm : Fin 8 → Fin 12
  | 0 => 0
  | 4 => 5
  | 1 => 1
  | 5 => 6
  | _ => 0

/-- The second arm from each chip-free centre to a chip vertex. -/
def secondArm : Fin 8 → Fin 12
  | 0 => 2
  | 4 => 7
  | 1 => 3
  | 5 => 8
  | _ => 0

/-- The chip at the far end of the first arm. -/
def firstChip : Fin 8 → Fin 8
  | 0 => 2
  | 4 => 6
  | 1 => 2
  | 5 => 6
  | _ => 0

/-- The chip at the far end of the second arm. -/
def secondChip : Fin 8 → Fin 8
  | 0 => 3
  | 4 => 7
  | 1 => 3
  | 5 => 7
  | _ => 0

/-- The edge joining the two chip-free centres. -/
def middleEdge : Fin 8 → Fin 12
  | 0 | 4 => 10
  | 1 | 5 => 11
  | _ => 10

/-- The chip-free core vertices, as a decidable table. -/
def isCenter : Fin 8 → Bool
  | 0 | 1 | 4 | 5 => true
  | _ => false

/-- Row 13 read as a pair of AR configuration-3 pictures. -/
def row13Config : ConfigThree 8 12 where
  core := row13Core
  chipOne := 2
  chipTwo := 3
  chipThree := 6
  chipFour := 7
  isCenter := isCenter
  partner := partner
  firstArm := firstArm
  secondArm := secondArm
  middleSlot := middleEdge
  firstChip := firstChip
  secondChip := secondChip
  center_not_chip := by decide
  partner_isCenter := by decide
  partner_ne := by decide
  partner_partner := by decide
  middleSlot_partner := by decide
  firstChip_isChip := by decide
  secondChip_isChip := by decide
  firstArm_ends := by decide
  secondArm_ends := by decide
  middleSlot_ends := by decide
  firstArm_ne_secondArm := by decide
  incident_slots := by decide
  chipSum := by
    intro v hv f
    fin_cases v <;>
      simp only [isCenter, Fin.zero_eta, Fin.isValue, firstChip, secondChip, partner, Fin.mk_one,
        Fin.reduceFinMk, Bool.false_eq_true] at hv ⊢<;> ring

/-- AR configuration 3 on row 13, valid simultaneously on the open cell and
every nonloopy forest face. -/
theorem row13_closedConstruction :
    ClosedSubdivisionDharConstruction row13Core (by norm_num) :=
  row13Config.closedConstruction (by norm_num) row13_connected (by decide)

end AtanasovRanganathan.GenusFiveRow13
