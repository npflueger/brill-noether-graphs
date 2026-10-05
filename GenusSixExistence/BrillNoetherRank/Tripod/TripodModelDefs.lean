import GenusSixExistence.BrillNoetherRank.Tripod.Gadget
import GenusSixExistence.BrillNoetherRank.Reduction
import DraismaVargasCount.DegenerateBigDivisor
import Utilities.Subdivision.CoreCutsAndFlats

/-!
# The tripod model of a graph with three marks

The definitions behind `Closure.exists_tripodModel`, kept apart so that its proof can live in a
module of its own (`TripodModelProof.lean`). `TripodModel G E` is the structure of §6.2 (The
tripod model) of `Research/genus-six-brill-noether-rank.md`; see the docstring of
`Closure.lean` for its fields.
-/

namespace GenusSixExistence.Tripod.Closure

open DraismaVargas.Count
open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.ExplicitPotential (Core)
open Utilities.Subdivision.CoreExpansion (ExpansionData)
open DraismaVargas.Count.DegenerateBigDivisor (degenerateLength)
open Gadget

/-! ## The tripod model -/

/-- **A tripod model** of a graph `G` with a degree-three divisor `E` on its vertices
(§6.2). See the docstring of `Closure.lean` for the fields. -/
structure TripodModel (G : CFGraph.{0}) (E : CFDiv (UnitSubdivisionPresentation.spec G).graph)
    where
  /-- The cubic core `G̃` of genus six. -/
  core : Core 10 15
  cubic : core.Cubic
  connected : core.Connected
  /-- `G̃` has no loop (the big core of an expansion is loopless). -/
  loopless : ∀ i, core.tail i ≠ core.head i
  /-- Where the marks sit on `G̃`. -/
  slots : MarkSlots 15
  /-- The small specification: the reduced specification of `G`, split at its bivalent marks. -/
  smallVertices : ℕ
  smallSlots : ℕ
  small : Spec smallVertices smallSlots
  /-- The small core vertex carrying mark `k`. -/
  smallMark : Fin 3 → Fin smallVertices
  /-- The expansion from the marked core onto the small specification. -/
  expansion : ExpansionData smallVertices smallSlots (10 + 1 + 1 + 1) (15 + 1 + 1 + 1)
  bigCore_eq : expansion.bigCore = markedCore core slots
  conditions : expansion.Conditions small.core
  fib_mark : ∀ k, expansion.fib (markVertex 10 k) = smallMark k
  /-- At every scale the small specification is `G`'s subdivision, with the marks going to `E`. -/
  transport : ∀ (u : ℕ) (hu : 0 < u), ∃ eqv : LaplacianEquiv (small.scale u hu).graph
      ((UnitSubdivisionPresentation.spec G).scale u hu).graph,
    eqv.mapDiv (small.embed u hu (∑ k : Fin 3, one_chip (small.coreVertex (smallMark k)))) =
      (UnitSubdivisionPresentation.spec G).embed u hu E
  /-- The leg lengths. -/
  legs : Fin 3 → ℕ
  /-- Long legs: longer than four times the total length of `G`. -/
  long : ∀ k, 4 * (∑ i, degenerateLength expansion small i) < legs k

namespace TripodModel

variable {G : CFGraph.{0}} {E : CFDiv (UnitSubdivisionPresentation.spec G).graph}

/-- **The actual request** on the gadget: the degenerate lengths of the expansion on the G-slots
(zero on the forest and on the zero mark pieces), and the legs. -/
noncomputable def request (M : TripodModel G E) : Fin (15 + 1 + 1 + 1 + 3) → ℚ :=
  Fin.addCases (fun i ↦ (degenerateLength M.expansion M.small i : ℚ)) fun k ↦ (M.legs k : ℚ)

theorem request_nonneg (M : TripodModel G E) : ∀ i, 0 ≤ M.request i := by
  intro i
  refine Fin.addCases (fun i ↦ ?_) (fun k ↦ ?_) i
  · simp [request]
  · simp [request]

theorem longLegs (M : TripodModel G E) : LongLegs M.slots M.request := by
  intro k
  rw [sum_baseRequest]
  have hg : ∀ i, gPart M.request i = (degenerateLength M.expansion M.small i : ℚ) := by
    intro i
    simp [gPart, request]
  have hl : legLength M.request k = (M.legs k : ℚ) := by
    simp [legLength, legSlot, request]
  rw [Finset.sum_congr rfl fun i _ ↦ hg i, hl]
  exact_mod_cast M.long k

end TripodModel

end GenusSixExistence.Tripod.Closure
