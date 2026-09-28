import DraismaVargasCount.GeometricStar

/-!
# Lifting a limit isomorphism to a frame isomorphism over the core

Source: Vargas, Part II (arXiv:2609.09109), the star of a codimension-one
wall.

## What is proved

`Count.GeometricStar.LimitIso.ofFrameIso` already turns a
`GeometricSegmentWalls.FrameIso` into a `GeometricStar.LimitIso`.  This module
proves the **converse criterion** that an exhaustion argument needs.

Let `first` and `second` be regrowths of the same core at the same positive
request, both carrying a labelled limit isomorphism to a fixed `wall`
regrowth.  Suppose a geometric isomorphism `map` of their *frame* data is
given, and suppose the dictionaries it induces on the quotient source commute
with the two literal limit contractions -- on vertices (`hVertex`) and on
retained occurrences (`hEdge`).  Then `map` is a frame isomorphism over the
core (`ofLimitSquare`): both inherited dictionaries are preserved.

The point is that neither `first.frame.ident` nor `second.frame.ident` is
touched directly.  `InheritedLimitBranches.branchLabel` and
`InheritedLimitRows.rowLabel` express each frame identification through the
corresponding limit identification (`ident_vertex`, `ident_row`), so the two
`overCore_*` obligations of `FrameIso` become the two `overCore_*` fields of
the given limit isomorphisms, plus exactly the two commuting squares assumed.

## What is NOT proved

The two squares are **hypotheses**: this module does not prove that any
particular `map` satisfies them, and it does not construct a `map` from
`first`, `second` and their limit isomorphisms.  Nothing here is an
exhaustion, a cardinality or a parity statement, and nothing is specific to
degree four, to W4 walls or to any particular wall.  No hypothesis is added to
`Count.CoreIdentification` or to `GeometricSegmentWalls.FrameIso`; both are
used exactly as they stand.

## Use

`W4WallExhaustion` glues its exhaustion of the labelled geometric star at a
discrete four-valent wall with `ofLimitSquare`.
-/

namespace DraismaVargas.Count.StarFrameIso

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open W4StableSource StableGraphIncidence
open WallStar (Regrowth Nondegenerate)
open GeometricSegmentWalls (FrameIso)
open InheritedLimitRows (limit_connected rowEquiv rowEquiv_mk edgeEmbedding)
open InheritedLimitBranches (branchEquiv branchLabel vertexMap)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- A frame's own branch label, read through the inherited limit dictionary. -/
theorem ident_vertex (w : Regrowth core y degree) (hy : Nondegenerate y)
    (branch : BranchVertex w.frame.data) :
    (InheritedLimitIncidence.coreIdentification w hy).vertex (branchEquiv w hy branch) =
      w.frame.ident.vertex branch := by
  rw [InheritedLimitIncidence.coreIdentification_vertex, branchLabel, Equiv.trans_apply,
    Equiv.symm_apply_apply]

/-- A frame's own row label, read through the inherited limit dictionary. -/
theorem ident_row (w : Regrowth core y degree) (hy : Nondegenerate y)
    (path : StablePath w.frame.data) :
    (InheritedLimitIncidence.coreIdentification w hy).row ((rowEquiv w hy).symm path) =
      w.frame.ident.row path := by
  rw [InheritedLimitIncidence.coreIdentification_row, InheritedLimitRows.rowLabel,
    Equiv.trans_apply, Equiv.apply_symm_apply]

variable {hy : Nondegenerate y} {first second wall : Regrowth core y degree}
  (left : GeometricStar.LimitIso hy first wall) (right : GeometricStar.LimitIso hy second wall)

/-- The occurrence of `second.limit` matching an occurrence of `first.limit`
under the two limit isomorphisms to the common wall. -/
noncomputable def transfer (edge : first.limit.SourceEdge) : second.limit.SourceEdge :=
  right.datum.sourceEdgeEquiv.symm (left.datum.sourceEdgeEquiv edge)

theorem datum_sourceEdgeEquiv_transfer (edge : first.limit.SourceEdge) :
    right.datum.sourceEdgeEquiv (transfer left right edge) = left.datum.sourceEdgeEquiv edge :=
  right.datum.sourceEdgeEquiv.apply_symm_apply _

/-- The same transfer on surviving occurrences. -/
noncomputable def transferSurviving (edge : NonDanglingEdge first.limit) :
    NonDanglingEdge second.limit :=
  (right.datum.nonDanglingEdgeEquiv (limit_connected second)).symm
    (left.datum.nonDanglingEdgeEquiv (limit_connected first) edge)

theorem transferSurviving_val (edge : NonDanglingEdge first.limit) :
    (transferSurviving left right edge).1 = transfer left right edge.1 := rfl

theorem stablePathEquiv_transferSurviving (edge : NonDanglingEdge first.limit) :
    right.datum.stablePathEquiv (limit_connected second)
        (transferSurviving left right edge).stablePath =
      left.datum.stablePathEquiv (limit_connected first) edge.stablePath := by
  rw [right.datum.stablePathEquiv_mk, left.datum.stablePathEquiv_mk, transferSurviving,
    Equiv.apply_symm_apply]

variable (map : GeometricDatumIso first.frame.data second.frame.data)

/-- The row half of the square, transported to the frames. -/
theorem row_square
    (hEdge : ∀ edge : first.limit.SourceEdge,
      map.sourceEdgeEquiv (edgeEmbedding first edge) =
        edgeEmbedding second (transfer left right edge))
    (edge : NonDanglingEdge first.limit) :
    (rowEquiv second hy).symm
        (map.stablePathEquiv first.frame.fullDim.valid.1
          (rowEquiv first hy edge.stablePath)) =
      (transferSurviving left right edge).stablePath := by
  apply (rowEquiv second hy).injective
  rw [Equiv.apply_symm_apply, rowEquiv_mk first hy edge,
    rowEquiv_mk second hy (transferSurviving left right edge)]
  refine (map.stablePathEquiv_mk _ _).trans ?_
  exact congrArg NonDanglingEdge.stablePath (Subtype.ext (hEdge edge.1))

/-- **The upward criterion.**  A geometric isomorphism of frame data whose
quotient-source dictionaries commute with the two literal limit contractions
is an isomorphism over the core. -/
noncomputable def ofLimitSquare
    (hVertex : ∀ vertex : first.frame.data.SourceVertex,
      right.datum.sourceVertexEquiv (vertexMap second (map.sourceVertexEquiv vertex)) =
        left.datum.sourceVertexEquiv (vertexMap first vertex))
    (hEdge : ∀ edge : first.limit.SourceEdge,
      map.sourceEdgeEquiv (edgeEmbedding first edge) =
        edgeEmbedding second (transfer left right edge)) :
    FrameIso first.frame second.frame where
  datum := map
  overCore_vertex branch := by
    rw [← ident_vertex second hy, ← ident_vertex first hy branch,
      ← right.overCore_vertex, ← left.overCore_vertex]
    exact congrArg (InheritedLimitIncidence.coreIdentification wall hy).vertex
      (Subtype.ext (hVertex branch.1))
  overCore_row path := by
    rw [← ident_row second hy, ← ident_row first hy path,
      ← right.overCore_row, ← left.overCore_row]
    refine congrArg (InheritedLimitIncidence.coreIdentification wall hy).row ?_
    obtain ⟨row, rfl⟩ := (rowEquiv first hy).surjective path
    rw [Equiv.symm_apply_apply]
    refine Quot.inductionOn row ?_
    intro edge
    exact (congrArg (right.datum.stablePathEquiv (limit_connected second))
      (row_square left right map hEdge edge)).trans
      (stablePathEquiv_transferSurviving left right edge)

end DraismaVargas.Count.StarFrameIso
