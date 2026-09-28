import DraismaVargas.LowGenus
import DraismaVargas.OddGenusTwoCycle
import DraismaVargas.LocalCases.RetainedClassInjectivity

/-!
# The Draisma--Vargas existence theorem

This file states the main theorems of the Draisma--Vargas construction.  A
rational metric graph is represented by a loopless finite core
and a positive integral length vector.  The conclusion uses
`Spec.regularSubdivisionGonality`: some common integral refinement of that
length vector carries a rank-one divisor of the asserted degree.

The name deliberately does not claim that metric graphs or piecewise-linear
functions have been formalized.  Identifying this invariant with metric
divisorial gonality is a separate theorem from the literature.

The explicit-scale subdivision-pencil construction in even genus at least six
follows the route of Vargas, Part II (arXiv:2609.09109)
(`LocalCases.RetainedClassInjectivity.nonempty_evenSubdivisionPencil`:
the caterpillar seed, the Whitehead-move walk through the non-trivalent walls with
a prescribed type-changing exit at every wall, and the integral-scale transport
back to the requested core).  The imported low-genus bounds, including genus
four, hold at scale one; both the even inequality and the all-genus theorem are
proved from the explicit construction and the formal odd-to-even two-cycle
reduction.  Nothing in this file is admitted.
-/

namespace DraismaVargas

open Utilities
open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open Utilities.Gonality

/-- The explicit-scale irreducible core of Draisma--Vargas Part I.  The
construction must return a positive regular scale together with an
effective degree-`⌈g/2⌉+1` rank-one divisor there; it may not hide the scale
inside the gonality infimum. -/
theorem nonempty_evenSubdivisionPencil_ceil_half_genus_add_one
    {n p : ℕ} (spec : Spec n p) (hconn : graph_connected spec.graph)
    (hGenus : 6 ≤ p + 1 - n) (hEven : Even (p + 1 - n)) :
    Nonempty (SubdivisionPencil spec ((p + 2 - n) / 2 + 1)) :=
  DraismaVargas.LocalCases.RetainedClassInjectivity.nonempty_evenSubdivisionPencil
    spec hconn hGenus hEven

/-- The irreducible even-genus bound follows from the explicit subdivision
pencil construction.  Low genus is proved independently, and
`OddGenusTwoCycle` formally reduces every odd genus to this case. -/
theorem even_regularSubdivisionGonality_le_ceil_half_genus_add_one
    {n p : ℕ} (spec : Spec n p) (hconn : graph_connected spec.graph)
    (hGenus : 6 ≤ p + 1 - n) (hEven : Even (p + 1 - n)) :
    spec.regularSubdivisionGonality ≤ (p + 2 - n) / 2 + 1 := by
  exact (Classical.choice
    (nonempty_evenSubdivisionPencil_ceil_half_genus_add_one
      spec hconn hGenus hEven)).gonality_le

/-- **Draisma--Vargas Part I, main theorem (`theorem-gonality`), in this
library's vocabulary.**
Every rational metric graph presented as a connected loopless core with a
positive integral length vector admits, on some regular refinement, a
rank-one divisor of degree `⌈g/2⌉ + 1`.

Here `genus spec.graph = (p : ℤ) - (n : ℤ) + 1`.  Connectedness gives
`n ≤ p + 1`, and `ceil_half_genus_normal_form` identifies the right side
with the usual ceiling expression.  A loop in a metric model must first be
presented with a bivalent vertex, since `Spec` intentionally requires its core
slots to be loopless. -/
theorem regularSubdivisionGonality_le_ceil_half_genus_add_one
    {n p : ℕ} (spec : Spec n p) (hconn : graph_connected spec.graph) :
    spec.regularSubdivisionGonality ≤ (p + 2 - n) / 2 + 1 := by
  by_cases hg : p + 1 - n ≤ 5
  · exact throughFive_regularSubdivisionGonality_le_ceil_half_genus_add_one spec hconn hg
  · have hGenus : 6 ≤ p + 1 - n := by omega
    obtain hEven | hOdd := Nat.even_or_odd (p + 1 - n)
    · exact even_regularSubdivisionGonality_le_ceil_half_genus_add_one
        spec hconn hGenus hEven
    · let root : Fin n := ⟨0, spec.core_nonempty⟩
      let extended := OddGenusTwoCycle.extension spec root
      have hCoreConnected : spec.core.Connected :=
        Utilities.Certificate.PseudocorePresentation.core_connected_of_graph_connected
          spec hconn
      have hExtendedConnected : graph_connected extended.graph :=
        extended.graph_connected_of_coreConnected
          (OddGenusTwoCycle.core_connected spec root hCoreConnected)
      have hIncrement :
          (p + 2) + 1 - (n + 1) = (p + 1 - n) + 1 :=
        OddGenusTwoCycle.genusIndex_extension spec
          (core_vertices_le_edges_add_one spec hconn)
      have hExtendedGenus : 6 ≤ (p + 2) + 1 - (n + 1) := by
        rw [hIncrement]
        omega
      have hExtendedEven : Even ((p + 2) + 1 - (n + 1)) := by
        rw [hIncrement]
        exact hOdd.add_one
      have hEvenBound : extended.regularSubdivisionGonality ≤
          ((p + 2) + 2 - (n + 1)) / 2 + 1 :=
        even_regularSubdivisionGonality_le_ceil_half_genus_add_one
          extended hExtendedConnected hExtendedGenus hExtendedEven
      exact OddGenusTwoCycle.odd_regularSubdivisionGonality_le_of_twoCycle
        spec root hconn hOdd hEvenBound

/-- All-ones specialization for an arbitrary connected finite loopless
multigraph, through its occurrence-safe unit subdivision presentation. -/
theorem graph_regularSubdivisionGonality_le_ceil_half_genus_add_one
    (G : CFGraph.{u}) (hconn : graph_connected G) :
    Utilities.Gonality.regularSubdivisionGonality G ≤
      (G.edges.card + 2 - Fintype.card G.V) / 2 + 1 := by
  apply regularSubdivisionGonality_le_ceil_half_genus_add_one
    (Utilities.Certificate.UnitSubdivisionPresentation.spec G)
  exact
    (Utilities.Certificate.UnitSubdivisionPresentation.laplacianEquiv G).graphConnected hconn

end DraismaVargas
