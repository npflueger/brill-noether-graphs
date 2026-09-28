import Utilities.Foundations.ElementaryExistence
import Utilities.Gonality.GonalityTransport
import Utilities.Iso.GraphContractionFibreTree
import Mathlib.Tactic

/-!
# Elementary subdivision-gonality bounds

Foundations independent of the all-genus statement in
`DraismaVargas/Statement.lean`. Construction and composition modules import
this file, so the final theorem can consume them without a dependency cycle.
-/

namespace DraismaVargas

open Utilities
open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open Utilities.Gonality

/-- A connected `Spec` has no more core vertices than core edge slots plus
one.  This is the natural-number side condition needed when rewriting its
cyclomatic genus. -/
theorem core_vertices_le_edges_add_one
    {n p : ℕ} (spec : Spec n p) (hconn : graph_connected spec.graph) :
    n ≤ p + 1 := by
  have hnonneg := genus_nonneg_of_graph_connected spec.graph hconn
  rw [spec.genus_graph] at hnonneg
  omega

/-- Normal form for `⌈g/2⌉ + 1`, where the natural cyclomatic genus of a
connected `n`-vertex, `p`-edge core is `p + 1 - n`.

The order of subtraction matters: `p - n + 2` is one too large for trees
because subtraction in `ℕ` truncates. -/
theorem ceil_half_genus_normal_form {n p : ℕ} (h : n ≤ p + 1) :
    (p + 1 - n + 1) / 2 + 1 = (p + 2 - n) / 2 + 1 := by
  omega

/-- The genus-two instance is already in the elementary Brill--Noether range:
every connected genus-two graph has a degree-two rank-one divisor, so no
nontrivial refinement is needed. -/
theorem genusTwo_regularSubdivisionGonality_le_two
    {n p : ℕ} (spec : Spec n p) (hgenus : p = n + 1)
    (hconn : graph_connected spec.graph) :
    spec.regularSubdivisionGonality ≤ 2 := by
  have hBN : BNExists spec.graph 1 2 := by
    apply BNExists_elementary hconn
    · norm_num
    · simp [bnNumber, rectangleWidth, hgenus]
    · right
      simp [rectangleWidth, hgenus]
  have hDgon : divisorialGonality spec.graph ≤ 2 := by
    exact_mod_cast divisorialGonality_le_of_BNExists hBN
  exact spec.regularSubdivisionGonality_le_divisorialGonality.trans hDgon

end DraismaVargas
