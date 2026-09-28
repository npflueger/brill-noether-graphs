import DraismaVargas.Statement

/-!
# Highlights: Draisma--Vargas Part I

The headline statements of the library, restated as `example`s so that they are checked against
the proved declarations.
-/

namespace DraismaVargas.Highlights

open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph Utilities.Gonality

universe u

/-- Every connected finite loopless multigraph `G` has a regular subdivision carrying a divisor of
degree `⌈g/2⌉ + 1` and rank at least one, where `g = |E| - |V| + 1` is its genus; the right-hand
side is `⌈g/2⌉ + 1` written with natural-number division. -/
example (G : CFGraph.{u}) (hconn : graph_connected G) :
    regularSubdivisionGonality G ≤ (G.edges.card + 2 - Fintype.card G.V) / 2 + 1 :=
  DraismaVargas.graph_regularSubdivisionGonality_le_ceil_half_genus_add_one G hconn

/-- The same bound for a connected core with `n` vertices, `p` edge slots and positive integer
edge lengths: some common integral refinement of the lengths carries such a divisor. -/
example {n p : ℕ} (spec : Spec n p) (hconn : graph_connected spec.graph) :
    spec.regularSubdivisionGonality ≤ (p + 2 - n) / 2 + 1 :=
  DraismaVargas.regularSubdivisionGonality_le_ceil_half_genus_add_one spec hconn

/-- In even genus at least six the construction exhibits the regular scale and the divisor. -/
example {n p : ℕ} (spec : Spec n p) (hconn : graph_connected spec.graph)
    (hGenus : 6 ≤ p + 1 - n) (hEven : Even (p + 1 - n)) :
    Nonempty (SubdivisionPencil spec ((p + 2 - n) / 2 + 1)) :=
  DraismaVargas.nonempty_evenSubdivisionPencil_ceil_half_genus_add_one spec hconn hGenus hEven

end DraismaVargas.Highlights
