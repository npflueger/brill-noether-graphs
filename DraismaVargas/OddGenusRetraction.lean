import DraismaVargas.Interface
import Utilities.Gluing.VertexCutWedge
import Utilities.Gluing.VertexWedgeRankFormula

/-!
# Rank retraction from a pendant vertex-wedge factor

The odd-genus step in Draisma--Vargas attaches a positive-genus pendant
factor, applies the even-genus theorem, and then returns to the original
graph.  No morphism theorem is needed for the return: assign the entire chip
mass on the pendant factor to the gluing vertex of the original factor.

The vertex-wedge rank formula of `Utilities` makes the proof especially short.  At
the phase one below minus the pendant divisor's degree, the pendant summand
has degree `-1` and hence rank `-1`; the formula forces the collapsed divisor
on the original factor to retain the full nonnegative rank threshold.
-/

namespace DraismaVargas

open Utilities
open Utilities.Certificate
open Utilities.Gonality

universe u v

/-- Collapse a divisor on a vertex wedge to the left factor, assigning the
entire degree on the right factor to the left gluing vertex. -/
def retractLeftWedgeDivisor
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (Q : CFDiv (vertexWedge G H x y)) : CFDiv G :=
  wedgeRestrictLeftDivisor G H x y Q +
    deg (wedgeRestrictRightDivisor G H x y Q) • one_chip x

/-- Pendant-factor retraction preserves the total divisor degree. -/
theorem deg_retractLeftWedgeDivisor
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (Q : CFDiv (vertexWedge G H x y)) :
    deg (retractLeftWedgeDivisor G H x y Q) = deg Q := by
  rw [retractLeftWedgeDivisor, deg.map_add]
  have hPendant :
      deg (deg (wedgeRestrictRightDivisor G H x y Q) • one_chip x) =
        deg (wedgeRestrictRightDivisor G H x y Q) := by
    rw [map_zsmul, deg_one_chip]
    simp
  rw [hPendant]
  exact deg_wedgeRestrictions G H x y Q

/-- Retraction from a pendant wedge preserves every nonnegative rank lower
bound.  This is the divisor-side content needed by the odd-genus reduction. -/
theorem rank_retractLeftWedgeDivisor_ge
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (Q : CFDiv (vertexWedge G H x y)) (k : ℤ) (hk : 0 ≤ k)
    (hRank : rank (vertexWedge G H x y) Q ≥ k) :
    rank G (retractLeftWedgeDivisor G H x y Q) ≥ k := by
  let D := wedgeRestrictLeftDivisor G H x y Q
  let E := wedgeRestrictRightDivisor G H x y Q
  have hWedgeRank :
      rank (vertexWedge G H x y) (wedgeAddDivisor G H x y D E) ≥ k := by
    rw [wedgeAddDivisor_restrict G H x y Q]
    exact hRank
  have hProfile := vertexWedge_rank_profile_inequality
    G H x y D E k hk hWedgeRank (-deg E - 1)
  have hRight :
      rank H (E + (-deg E - 1) • one_chip y) = -1 := by
    apply rank_add_zsmul_one_chip_eq_neg_one_of_degree_neg
    omega
  have hLeft :
      D - ((-deg E - 1) + 1) • one_chip x =
        retractLeftWedgeDivisor G H x y Q := by
    funext z
    simp only [retractLeftWedgeDivisor, D, E, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  rw [hRight, hLeft] at hProfile
  omega

/-- Every nonnegative-rank Brill--Noether witness on a vertex wedge retracts
to the left factor in the same degree. -/
theorem bnExists_left_of_vertexWedge
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (r d : ℤ) (hr : 0 ≤ r)
    (hExists : BNExists (vertexWedge G H x y) r d) :
    BNExists G r d := by
  obtain ⟨Q, hDegree, hRank⟩ := hExists
  exact ⟨retractLeftWedgeDivisor G H x y Q,
    (deg_retractLeftWedgeDivisor G H x y Q).trans hDegree,
    rank_retractLeftWedgeDivisor_ge G H x y Q r hr hRank⟩

/-- The same rank retraction for an arbitrary ambient graph equipped with an
explicit one-vertex cut. -/
theorem bnExists_leftGraph_of_oneVertexCut
    {K : CFGraph.{u}} (cut : OneVertexCut K)
    (r d : ℤ) (hr : 0 ≤ r) (hExists : BNExists K r d) :
    BNExists cut.leftGraph r d := by
  apply bnExists_left_of_vertexWedge cut.leftGraph cut.rightGraph
    cut.leftGlue cut.rightGlue r d hr
  exact (cut.BNExists_iff r d).mp hExists

/-- A rank-one witness on a pendant extension of one regular subdivision
already bounds the regular-subdivision gonality of the original metric.  This
is the fixed-scale component consumed by the concrete two-cycle extension. -/
theorem regularSubdivisionGonality_le_of_vertexWedge_scale
    {n p k d : ℕ}
    (spec : Utilities.Certificate.SubdivisionGraph.Spec n p)
    (hk : 0 < k) (H : CFGraph.{v})
    (x : (spec.scale k hk).graph.V) (y : H.V)
    (hExists : BNExists
      (vertexWedge (spec.scale k hk).graph H x y) 1 (d : ℤ)) :
    spec.regularSubdivisionGonality ≤ d := by
  exact regularSubdivisionGonality_le_of_BNExists_scale spec hk
    (bnExists_left_of_vertexWedge
      (spec.scale k hk).graph H x y 1 (d : ℤ) (by omega) hExists)

/-- Scale-aware pendant retraction stated on an arbitrary ambient graph with
a one-vertex cut.  A Laplacian equivalence identifies the retained factor with
the selected regular subdivision of the requested metric. -/
theorem regularSubdivisionGonality_le_of_oneVertexCut_scale
    {n p k d : ℕ}
    (spec : Utilities.Certificate.SubdivisionGraph.Spec n p)
    (hk : 0 < k) {K : CFGraph.{u}} (cut : OneVertexCut K)
    (leftEquiv : LaplacianEquiv (spec.scale k hk).graph cut.leftGraph)
    (hExists : BNExists K 1 (d : ℤ)) :
    spec.regularSubdivisionGonality ≤ d := by
  apply regularSubdivisionGonality_le_of_BNExists_scale spec hk
  exact (leftEquiv.bnExists_iff 1 (d : ℤ)).mpr
    (bnExists_leftGraph_of_oneVertexCut cut 1 (d : ℤ) (by omega) hExists)

/-- A scale-compatible pendant extension of one subdivision presentation.
The retained factor at every regular scale is identified with the same scale
of `source`; the other factor may vary with the scale. -/
structure RegularPendantExtension
    {n p n' p' : ℕ}
    (source : Utilities.Certificate.SubdivisionGraph.Spec n p)
    (extended : Utilities.Certificate.SubdivisionGraph.Spec n' p') where
  connected : ∀ (k : ℕ) (hk : 0 < k),
    graph_connected (extended.scale k hk).graph
  cut : ∀ (k : ℕ) (hk : 0 < k),
    OneVertexCut (extended.scale k hk).graph
  leftEquiv : ∀ (k : ℕ) (hk : 0 < k),
    LaplacianEquiv (source.scale k hk).graph (cut k hk).leftGraph

/-- Regular-subdivision gonality cannot decrease when a scale-compatible
pendant factor is attached.  This consumes the enlarged metric's bound in its
actual `sInf` form: choose a minimizing scale, retract its gonality divisor,
and compare with the assumed bound. -/
theorem regularSubdivisionGonality_le_of_regularPendantExtension
    {n p n' p' d : ℕ}
    {source : Utilities.Certificate.SubdivisionGraph.Spec n p}
    {extended : Utilities.Certificate.SubdivisionGraph.Spec n' p'}
    (extension : RegularPendantExtension source extended)
    (hBound : extended.regularSubdivisionGonality ≤ d) :
    source.regularSubdivisionGonality ≤ d := by
  obtain ⟨k, hk, hMinimum⟩ :=
    Nat.sInf_mem extended.regularSubdivisionGonalitySet_nonempty
  change divisorialGonality (extended.scale k hk).graph =
    extended.regularSubdivisionGonality at hMinimum
  have hExists : BNExists (extended.scale k hk).graph 1
      (divisorialGonality (extended.scale k hk).graph : ℤ) :=
    BNExists_one_divisorialGonality (extension.connected k hk)
  have hSource := regularSubdivisionGonality_le_of_oneVertexCut_scale
    source hk (extension.cut k hk) (extension.leftEquiv k hk) hExists
  rw [hMinimum] at hSource
  exact hSource.trans hBound

/-- Raising an odd natural genus by one does not change the degree
`ceil(genus / 2) + 1`, in the subtraction normal form used by `Spec`. -/
theorem ceilHalfDegree_eq_of_odd_genus_increment
    {n p n' p' : ℕ} (hVertices : n ≤ p + 1)
    (hOdd : Odd (p + 1 - n))
    (hIncrement : p' + 1 - n' = (p + 1 - n) + 1) :
    (p' + 2 - n') / 2 + 1 = (p + 2 - n) / 2 + 1 := by
  obtain ⟨half, hHalf⟩ := hOdd
  omega

/-- **Odd-genus reduction.**  If attaching a scale-compatible pendant factor
raises the core genus by one, the even-genus bound on the enlarged metric
returns with exactly the required odd-genus degree. -/
theorem odd_regularSubdivisionGonality_le_of_regularPendantExtension
    {n p n' p' : ℕ}
    {source : Utilities.Certificate.SubdivisionGraph.Spec n p}
    {extended : Utilities.Certificate.SubdivisionGraph.Spec n' p'}
    (hConnected : graph_connected source.graph)
    (hOdd : Odd (p + 1 - n))
    (hIncrement : p' + 1 - n' = (p + 1 - n) + 1)
    (extension : RegularPendantExtension source extended)
    (hEven : extended.regularSubdivisionGonality ≤
      (p' + 2 - n') / 2 + 1) :
    source.regularSubdivisionGonality ≤ (p + 2 - n) / 2 + 1 := by
  have hDegree := ceilHalfDegree_eq_of_odd_genus_increment
    (core_vertices_le_edges_add_one source hConnected) hOdd hIncrement
  rw [← hDegree]
  exact regularSubdivisionGonality_le_of_regularPendantExtension extension hEven

end DraismaVargas
