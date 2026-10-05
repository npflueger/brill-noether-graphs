import GenusSixExistence.BrillNoetherRank.Tripod.Classification
import GenusSixExistence.BrillNoetherRank.Tripod.TripodModelDefs
import GenusSixExistence.BrillNoetherRank.Tripod.TripodModelProof
import GenusSixExistence.BrillNoetherRank.Tripod.ClosureFrame
import GenusSixExistence.BrillNoetherRank.Tripod.BridgeLift
import GenusSixExistence.BrillNoetherRank.Reduction
import DraismaVargasCount.DegenerateBigDivisor
import Utilities.Subdivision.CoreCutsAndFlats

/-!
# From the generic long-leg locus to the actual point

Prose proof: `Research/genus-six-brill-noether-rank.md`, §6 (Closure to the actual point):
§6.1 (Contracting bridges), §6.2 (The tripod model), §6.3 (Admissible requests, and the parity
of the claw classes) and §6.4 (The segment); section and statement numbers in this file refer
to that note.

## The closure (Theorem 6.3)

`exists_closed_oddClaw_of_package`: given the generic-point package (P5)
(`Classification.ParityPackage`), at **every** non-negative request with long legs some member
over the gadget is closed, of odd multiplicity, and a claw member. This is
`ClosedBoundaryMember.exists_closed_hasOddMult_of_nonneg` with a larger wall set; the proof is
`ClosureFrame.exists_closed_oddClaw_of_package`. `exists_closed_oddClaw` composes it with
`Classification.parityPackage`.

## The tripod model (§6.2)

The retained slots of the cubic model do not carry the unit lengths of `G` directly:
`exists_expansionModel` returns a *reduced* specification `spec₀` (bridges contracted, bivalent
vertices suppressed except loop markers), whose slots are chains of unit edges of `G`; a
retained cubic slot is `single` or `double` over **those**. So `TripodModel G E` is stated over a
small specification `small` that is `spec₀` with every slot carrying a bivalent mark split at the
mark, and records:

* the cubic core `G̃ : Core 10 15` and the mark slots `slots`;
* an `ExpansionData` from the **marked** core `markedCore G̃ slots` onto `small`, whose
  contracted slots are the expansion forest of `G̃` and the zero mark pieces (`conditions`), and
  which sends mark `k` to the small core vertex `smallMark k` (`fib_mark`);
* at every scale `u`, a `LaplacianEquiv` from `small.scale u` to the `u`-fold subdivision of `G`
  carrying the marks to `E` (`transport`; this is where `E` enters, and it is used for the
  transport to `G` at the end of §7.5);
* integral legs, longer than four times the total length of `G` (`long`).

The actual request `TripodModel.request` is `degenerateLength` on the G-slots and the legs on
the leg slots. The model is **built** from `G̃`, not requested from `exists_expansionModel` for
the gadget: when two marks coincide, a cubic model of the gadget may join two legs inside the
expansion forest, and then the attached part is not a tripod (§6.2).

## The bridge lift (Lemma 6.1 and Corollary 6.2)

`oddCompletionWitness_of_bridgeless` reduces `OddCompletionWitness` to bridgeless graphs. It is
proved in `BridgeLift.lean` by contracting every bridge at once, onto the fossil
`Utilities.fossil G` (`Utilities.Subdivision.BridgeLift`).

The tripod model is `TripodModelProof.exists_tripodModel`, and the closure is
`ClosureFrame.exists_closed_oddClaw_of_package`.
-/

namespace GenusSixExistence.Tripod.Closure

open DraismaVargas.Count
open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.ExplicitPotential (Core)
open Utilities.Subdivision.CoreExpansion (ExpansionData)
open DraismaVargas.Count.DegenerateBigDivisor (degenerateLength)
open Gadget Classification

/-! ## 1.  The closure -/

/-- **The closure** (Theorem 6.3). From the generic-point package, at every non-negative
request on the gadget with long legs there is a member that is closed (`z ≥ 0`), has odd
multiplicity, and is a claw member. -/
theorem exists_closed_oddClaw_of_package {n p : ℕ} (core : Core n p) (s : MarkSlots p)
    (hP : ParityPackage core s) (y : Fin (p + 1 + 1 + 1 + 3) → ℚ) (hy : ∀ i, 0 ≤ y i)
    (hlong : LongLegs s y) :
    ∃ mem : FibreMember (tripodCore core s) y (3 + 2),
      mem.Closed ∧ mem.HasOddMult ∧ MemberIsClaw mem :=
  ClosureFrame.exists_closed_oddClaw_of_package core s hP y hy hlong

/-- **The closure, unconditionally**: over a cubic connected loopless core of genus six, at every
non-negative request with long legs, a closed claw member of odd multiplicity. -/
theorem exists_closed_oddClaw {n p : ℕ} (core : Core n p) (hcubic : core.Cubic)
    (hconn : core.Connected) (hloop : ∀ i, core.tail i ≠ core.head i) (hgenus : p + 1 - n = 6)
    (s : MarkSlots p)
    (y : Fin (p + 1 + 1 + 1 + 3) → ℚ) (hy : ∀ i, 0 ≤ y i) (hlong : LongLegs s y) :
    ∃ mem : FibreMember (tripodCore core s) y (3 + 2),
      mem.Closed ∧ mem.HasOddMult ∧ MemberIsClaw mem :=
  exists_closed_oddClaw_of_package core s (parityPackage hcubic hconn hloop hgenus s) y hy hlong

/-! ## 2.  The tripod model

`TripodModel` and its request are in `TripodModelDefs.lean`. -/


/-- **Tripod models exist** (§6.2). Every connected
bridgeless graph of genus six, with every effective divisor of degree three on its vertices, has
a tripod model. -/
theorem exists_tripodModel (G : CFGraph.{0}) (hG : graph_connected G) (hg : genus G = 6)
    (hb : (UnitSubdivisionPresentation.spec G).core.Bridgeless)
    (E : CFDiv (UnitSubdivisionPresentation.spec G).graph) (hE : effective E) (hdeg : deg E = 3) :
    Nonempty (TripodModel G E) :=
  TripodModelProof.exists_tripodModel G hG hg hb E hE hdeg

/-! ## 3.  The bridge lift -/

/-- **The bridge lift** (Lemma 6.1 and Corollary 6.2). It suffices to prove the triple
witness for bridgeless graphs. -/
theorem oddCompletionWitness_of_bridgeless
    (h : ∀ H : CFGraph.{0}, graph_connected H → genus H = 6 →
      (UnitSubdivisionPresentation.spec H).core.Bridgeless →
        BrillNoetherRank.OddCompletionWitness H 1 2)
    (G : CFGraph.{0}) (hG : graph_connected G) (hg : genus G = 6) :
    BrillNoetherRank.OddCompletionWitness G 1 2 :=
  BridgeLift.oddCompletionWitness_of_bridgeless h G hG hg

end GenusSixExistence.Tripod.Closure
