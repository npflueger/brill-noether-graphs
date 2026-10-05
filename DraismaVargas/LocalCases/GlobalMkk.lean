module

public import DraismaVargas.Infrastructure.TargetSeparation
public import DraismaVargas.LocalCases.GlobalM11Arbitrary
public import DraismaVargas.LocalCases.ResolutionMkk

@[expose] public section

/-!
# Global arbitrary-degree continuation in case M-kk

The three Figure 34 candidates are divalent at both new endpoints.  This makes
their selected-block Riemann--Hurwitz checks uniform; the substantive local
data are the two endpoint blocks of sizes `k₁,k₂`, their detachments, and the
exterior refinements.  The guarded-background adapter installs those choices
among arbitrary other wall blocks, and Equation (8) supplies the positive
wall crossing.

## Two points about the detaching members

*Each detaching member detaches on both sides.*  `Geometry.firstLocal` and
`Geometry.secondLocal` are built on `ResolutionMkk.bothDetachedResolution`,
which detaches the sheet on the new edge **and** on the retained `t₃`
endpoint.  Detaching on the new edge only (`ResolutionMkk.detachedResolution`,
which keeps `right := wall`) gives an Euler count one too large
(`ResolutionMkk.detachedResolution_card_blocks`), so an Equation (8) exit
assembled from it would raise the source genus by exactly one: it creates two
parallel edges over `t₁`, a cycle over `t₁` of the kind Draisma--Vargas Part I
excludes (Position II.b of case `{w3-r1-nd3-t2}`).  Figure 34 forces the
second detachment: Base II.2 gives `k₃ = |A⁽ᵠ⁾| = |e'| + |e''|` and
Cardinality M gives `k₃ + 1 = |A₀|`, so the `t₃` endpoint block is `A₀` minus
the sheet carrying the dangling `e₄`.  The genus is **proved** preserved
(`firstLocal_card_blocks`, `firstLocal_sourceGenus_eq` and their `second`
companions).  Candidate 3 (`thirdResolution`) has block-count defect zero and
detaches nothing.

*The two detaching members live over different data.*  They cannot share one
gluing datum (`W2MkkSourceCandidates.no_common_geometry`, stated against the
two-sided shape).  The `t₃` exterior refinement of a two-sided detachment pins
the detached sheet to the unique sheet that the dangling occurrence `e₄`
isolates, and that sheet lies in exactly one of the two endpoint blocks.  This
is a matter of **gauge**: a branch swap across the `t₂` branch fixes the wall
partition and fixes the `t₃` occurrence partition -- hence fixes *which* sheet
is pinned -- while exchanging the two endpoint blocks at it
(`W2MkkSourceCandidates.branchSwap_moves_pinSheet`).  So the second member is
taken over the branch-swapped datum, exactly as `GlobalM11Arbitrary` does for
Figure 32 and `GlobalM1k` for Figure 33.  That is the section
*The branch-swapped second member* below.

The two points are linked.  For a one-sided detachment the `t₃` exterior
condition degenerates to `(edgePartition e).Refines (vertexPartition wall)`, a
field of every `GluingDatum`
(`W2MkkSourceCandidates.detachedResolution_exterior_vacuous`), so over
one-sided detachments the unswapped three-pattern bundle is vacuously
satisfiable, at the price of the genus; over two-sided ones it is empty.

## Which bundle is inhabited

`candidates` / `exists_valid_positive_exit` keep the literal reading of
Figure 34 -- all three members over one `data` and one `Geometry` -- because
that is the shape `BalancingValencyTwo.balance_M_kk` is stated against.  They
have **no instance at an actual `w2Mkk` profile**, as
`W2MkkSourceCandidates.no_common_geometry` proves.

The **swapped** bundle is the one an actual profile can use, and the section
*The bundle is inhabited* proves it is nonempty: from a single `PinnedProfile`
-- the wall's two occurrences, the `t₂` endpoint refinement and the pinned
sheet, all conditions on `data` alone -- `PinnedProfile.nonempty_swapped`
builds all three members, the second one over the branch-swapped datum.  The
separation input that the swap needs is **not carried**: it is discharged from
`graph_connected target` and `genus target = 0` through
`Infrastructure.TargetSeparation.edgeMoved_eq_false`, which is why this file
imports `TargetSeparation`.
-/

namespace DraismaVargas.LocalCases.GlobalMkk

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionM1k
open DraismaVargas.LocalCases.ResolutionMkk
open DraismaVargas.LocalCases.BalancingValencyTwo
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.GlobalM11Arbitrary

variable {target : CFGraph} {degree : ℕ}
  {data : GluingDatum target degree} {wall : target.V}

/-- The two nontrivial endpoint blocks of source case M-kk. -/
structure Geometry (data : GluingDatum target degree) (wall : target.V) where
  endpoint : SheetPartition degree
  first : Fin degree
  firstRemainder : Fin degree
  second : Fin degree
  secondRemainder : Fin degree
  endpoint_refines : endpoint.Refines (data.vertexPartition wall)
  wall_together : (data.vertexPartition wall).Rel first second
  separate : ¬endpoint.Rel first second
  first_together : endpoint.Rel first firstRemainder
  second_together : endpoint.Rel second secondRemainder
  first_ne : first ≠ firstRemainder
  second_ne : second ≠ secondRemainder
  k₁ : ℕ
  k₂ : ℕ
  one_lt_k₁ : 1 < k₁
  one_lt_k₂ : 1 < k₂
  firstCard : endpoint.blockCard first = k₁
  secondCard : endpoint.blockCard second = k₂
  wallCard : (data.vertexPartition wall).blockCard first = k₁ + k₂

namespace Geometry

/-- Figure 34, candidate 1: detach the first endpoint block's sheet on the new
edge **and** on the retained `t₃` endpoint.  Detaching on the new edge only
(`ResolutionMkk.detachedResolution`) would raise the source genus by one. -/
abbrev firstLocal (geometry : Geometry data wall) : LocalResolution degree :=
  bothDetachedResolution (data.vertexPartition wall) geometry.endpoint
    geometry.first geometry.firstRemainder geometry.first_ne
    (geometry.endpoint_refines.rel geometry.first_together)
    geometry.first_together geometry.endpoint_refines

/-- Figure 34, candidate 2: the same, on the second endpoint block. -/
abbrev secondLocal (geometry : Geometry data wall) : LocalResolution degree :=
  bothDetachedResolution (data.vertexPartition wall) geometry.endpoint
    geometry.second geometry.secondRemainder geometry.second_ne
    (geometry.endpoint_refines.rel geometry.second_together)
    geometry.second_together geometry.endpoint_refines

/-- Figure 34, candidate 3: retain the complete joined wall block. -/
abbrev thirdLocal (_geometry : Geometry data wall) : LocalResolution degree :=
  thirdResolution (data.vertexPartition wall)

end Geometry

/-- Common one-old-edge-per-side occurrence input for every Figure 34
candidate. -/
structure DivalentPattern (distinguished : Fin degree)
    (selected : LocalResolution degree) where
  background : Background data wall distinguished
  leftExternal : target.edges
  rightExternal : target.edges
  leftEdges : background.leftEdges = [leftExternal]
  rightEdges : background.rightEdges = [rightExternal]
  exterior : ∀ edge : target.edges,
    ((edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) →
    (data.edgePartition edge).Refines
      (if background.right edge then selected.right else selected.left)

namespace DivalentPattern

/-- Assemble one divalent selected-block resolution with all background wall
blocks. -/
noncomputable def candidate {distinguished : Fin degree}
    {selected : LocalResolution degree}
    (pattern : DivalentPattern (data := data) (wall := wall)
      distinguished selected)
    (hContracts : selected.ContractsTo (data.vertexPartition wall)) :
    Candidate target degree data wall := by
  apply pattern.background.install selected hContracts pattern.exterior
  · intro anchor _ _
    rw [pattern.leftEdges]
    simpa using riemannHurwitzAtBlock_divalent
      (data.vertexPartition wall) selected.left selected.newEdge
      (data.edgePartition pattern.leftExternal) anchor
  · intro anchor _ _
    rw [pattern.rightEdges]
    simpa using riemannHurwitzAtBlock_divalent
      (data.vertexPartition wall) selected.right selected.newEdge
      (data.edgePartition pattern.rightExternal) anchor

/-- A divalent pattern as a heterogeneous global candidate. -/
noncomputable def certified {distinguished : Fin degree}
    {selected : LocalResolution degree}
    (pattern : DivalentPattern (data := data) (wall := wall)
      distinguished selected)
    (hContracts : selected.ContractsTo (data.vertexPartition wall)) :
    CertifiedCandidate data := (pattern.candidate hContracts).certified

end DivalentPattern

/-- Contraction proof for candidate 1. -/
theorem firstLocal_contracts (geometry : Geometry data wall) :
    geometry.firstLocal.ContractsTo (data.vertexPartition wall) :=
  bothDetachedResolution_contracts (data.vertexPartition wall) geometry.endpoint
    geometry.first geometry.firstRemainder geometry.first_ne
    (geometry.endpoint_refines.rel geometry.first_together)
    geometry.first_together geometry.endpoint_refines

/-- Contraction proof for candidate 2. -/
theorem secondLocal_contracts (geometry : Geometry data wall) :
    geometry.secondLocal.ContractsTo (data.vertexPartition wall) :=
  bothDetachedResolution_contracts (data.vertexPartition wall) geometry.endpoint
    geometry.second geometry.secondRemainder geometry.second_ne
    (geometry.endpoint_refines.rel geometry.second_together)
    geometry.second_together geometry.endpoint_refines

/-- Contraction proof for candidate 3. -/
theorem thirdLocal_contracts (geometry : Geometry data wall) :
    geometry.thirdLocal.ContractsTo (data.vertexPartition wall) :=
  thirdResolution_contracts (data.vertexPartition wall)

/-! ## The two-sided members preserve the source genus

The Riemann--Hurwitz receipts are those of the one-sided detachment -- both
new endpoints stay divalent -- but the displayed indices and the Euler count
differ.  `right` is `A₀ ∖ {x}` rather than `A₀`, which is exactly Figure 34's
`A⁽ᵠ⁾`, and the blockwise Euler identity of
`GlobalResolution.sourceGraph_genus_eq_iff_block_card` closes. -/

/-- Candidate 1's new edge isolates the detached sheet: `|e₄| = 1`. -/
theorem firstLocal_newEdge_blockCard_single (geometry : Geometry data wall) :
    geometry.firstLocal.newEdge.blockCard geometry.first = 1 :=
  bothDetachedResolution_newEdge_blockCard_single (data.vertexPartition wall)
    geometry.endpoint geometry.first geometry.firstRemainder geometry.first_ne
    (geometry.endpoint_refines.rel geometry.first_together)
    geometry.first_together geometry.endpoint_refines

/-- Figure 34's `M⁽¹⁾` index `|e'| = k₁ - 1`. -/
theorem firstLocal_newEdge_blockCard_remainder (geometry : Geometry data wall) :
    geometry.firstLocal.newEdge.blockCard geometry.firstRemainder =
      geometry.k₁ - 1 :=
  bothDetachedResolution_newEdge_blockCard_remainder (data.vertexPartition wall)
    geometry.endpoint geometry.first geometry.firstRemainder geometry.first_ne
    (geometry.endpoint_refines.rel geometry.first_together)
    geometry.first_together geometry.endpoint_refines geometry.k₁
    geometry.firstCard

/-- Figure 34's `M⁽¹⁾` index `|e''| = k₂`: the untouched endpoint block keeps
its cardinality on the new edge. -/
theorem firstLocal_newEdge_blockCard_second (geometry : Geometry data wall) :
    geometry.firstLocal.newEdge.blockCard geometry.second = geometry.k₂ := by
  rw [bothDetachedResolution_newEdge_blockCard_other (data.vertexPartition wall)
    geometry.endpoint geometry.first geometry.firstRemainder geometry.second
    geometry.first_ne (geometry.endpoint_refines.rel geometry.first_together)
    geometry.first_together geometry.endpoint_refines geometry.separate]
  exact geometry.secondCard

/-- **The retained `t₃` endpoint really does shrink.**  Its class is
Figure 34's `A⁽¹⁾ = e₃`, of `|A₀| - 1 = k₁ + k₂ - 1` sheets -- this is the
whole difference from the one-sided detachment. -/
theorem firstLocal_right_blockCard_remainder (geometry : Geometry data wall) :
    geometry.firstLocal.right.blockCard geometry.firstRemainder =
      geometry.k₁ + geometry.k₂ - 1 :=
  bothDetachedResolution_right_blockCard_remainder (data.vertexPartition wall)
    geometry.endpoint geometry.first geometry.firstRemainder geometry.first_ne
    (geometry.endpoint_refines.rel geometry.first_together)
    geometry.first_together geometry.endpoint_refines
    (geometry.k₁ + geometry.k₂) geometry.wallCard

/-- Candidate 2's new edge isolates its detached sheet. -/
theorem secondLocal_newEdge_blockCard_single (geometry : Geometry data wall) :
    geometry.secondLocal.newEdge.blockCard geometry.second = 1 :=
  bothDetachedResolution_newEdge_blockCard_single (data.vertexPartition wall)
    geometry.endpoint geometry.second geometry.secondRemainder
    geometry.second_ne
    (geometry.endpoint_refines.rel geometry.second_together)
    geometry.second_together geometry.endpoint_refines

/-- Figure 34's `M⁽²⁾` index `|e''| = k₂ - 1`. -/
theorem secondLocal_newEdge_blockCard_remainder (geometry : Geometry data wall) :
    geometry.secondLocal.newEdge.blockCard geometry.secondRemainder =
      geometry.k₂ - 1 :=
  bothDetachedResolution_newEdge_blockCard_remainder (data.vertexPartition wall)
    geometry.endpoint geometry.second geometry.secondRemainder
    geometry.second_ne
    (geometry.endpoint_refines.rel geometry.second_together)
    geometry.second_together geometry.endpoint_refines geometry.k₂
    geometry.secondCard

/-- Figure 34's `M⁽²⁾` index `|e'| = k₁`. -/
theorem secondLocal_newEdge_blockCard_first (geometry : Geometry data wall) :
    geometry.secondLocal.newEdge.blockCard geometry.first = geometry.k₁ := by
  rw [bothDetachedResolution_newEdge_blockCard_other (data.vertexPartition wall)
    geometry.endpoint geometry.second geometry.secondRemainder geometry.first
    geometry.second_ne (geometry.endpoint_refines.rel geometry.second_together)
    geometry.second_together geometry.endpoint_refines
    (fun hRel ↦ geometry.separate hRel.symm)]
  exact geometry.firstCard

/-- Candidate 2's retained `t₃` class is `A⁽²⁾`, again `|A₀| - 1` sheets. -/
theorem secondLocal_right_blockCard_remainder (geometry : Geometry data wall) :
    geometry.secondLocal.right.blockCard geometry.secondRemainder =
      geometry.k₁ + geometry.k₂ - 1 := by
  refine bothDetachedResolution_right_blockCard_remainder
    (data.vertexPartition wall) geometry.endpoint geometry.second
    geometry.secondRemainder geometry.second_ne
    (geometry.endpoint_refines.rel geometry.second_together)
    geometry.second_together geometry.endpoint_refines
    (geometry.k₁ + geometry.k₂) ?_
  have hBlock : (data.vertexPartition wall).block geometry.first =
      (data.vertexPartition wall).block geometry.second :=
    SheetPartition.block_eq_of_rel _ geometry.wall_together
  simpa only [SheetPartition.blockCard, ← hBlock] using geometry.wallCard

/-- Both new endpoints are divalent, so candidate 1's left receipt is the
uniform two-occurrence count. -/
theorem firstLocal_left_riemannHurwitzAtBlock (geometry : Geometry data wall)
    (external : SheetPartition degree) (anchor : Fin degree) :
    LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
      geometry.firstLocal.left
      [geometry.firstLocal.newEdge, external] anchor :=
  bothDetachedResolution_left_riemannHurwitzAtBlock _ _ _ _ _ _ _ _ _ _

/-- The same on the retained side. -/
theorem firstLocal_right_riemannHurwitzAtBlock (geometry : Geometry data wall)
    (external : SheetPartition degree) (anchor : Fin degree) :
    LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
      geometry.firstLocal.right
      [geometry.firstLocal.newEdge, external] anchor :=
  bothDetachedResolution_right_riemannHurwitzAtBlock _ _ _ _ _ _ _ _ _ _

theorem secondLocal_left_riemannHurwitzAtBlock (geometry : Geometry data wall)
    (external : SheetPartition degree) (anchor : Fin degree) :
    LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
      geometry.secondLocal.left
      [geometry.secondLocal.newEdge, external] anchor :=
  bothDetachedResolution_left_riemannHurwitzAtBlock _ _ _ _ _ _ _ _ _ _

theorem secondLocal_right_riemannHurwitzAtBlock (geometry : Geometry data wall)
    (external : SheetPartition degree) (anchor : Fin degree) :
    LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
      geometry.secondLocal.right
      [geometry.secondLocal.newEdge, external] anchor :=
  bothDetachedResolution_right_riemannHurwitzAtBlock _ _ _ _ _ _ _ _ _ _

/-- **The Euler count of candidate 1 closes**, whereas the one-sided shape's is
one too large (`ResolutionMkk.detachedResolution_card_blocks`). -/
theorem firstLocal_card_blocks (geometry : Geometry data wall) :
    Fintype.card geometry.firstLocal.newEdge.Blocks +
        Fintype.card (data.vertexPartition wall).Blocks =
      Fintype.card geometry.firstLocal.left.Blocks +
        Fintype.card geometry.firstLocal.right.Blocks :=
  bothDetachedResolution_card_blocks (data.vertexPartition wall)
    geometry.endpoint geometry.first geometry.firstRemainder geometry.first_ne
    (geometry.endpoint_refines.rel geometry.first_together)
    geometry.first_together geometry.endpoint_refines

/-- The same for candidate 2. -/
theorem secondLocal_card_blocks (geometry : Geometry data wall) :
    Fintype.card geometry.secondLocal.newEdge.Blocks +
        Fintype.card (data.vertexPartition wall).Blocks =
      Fintype.card geometry.secondLocal.left.Blocks +
        Fintype.card geometry.secondLocal.right.Blocks :=
  bothDetachedResolution_card_blocks (data.vertexPartition wall)
    geometry.endpoint geometry.second geometry.secondRemainder
    geometry.second_ne
    (geometry.endpoint_refines.rel geometry.second_together)
    geometry.second_together geometry.endpoint_refines

/-- **The genus statement.**  Resolving the wall by Figure 34's `M⁽¹⁾`
preserves the quotient-source genus, whereas the one-sided shape raises it by
exactly one (`W3ShiftShrinkExistence.detachedResolution_sourceGenus_eq_succ`). -/
theorem firstLocal_sourceGenus_eq (geometry : Geometry data wall)
    (right : target.edges → Bool)
    (hCompatible :
      GlobalResolution.OldCompatible data wall right geometry.firstLocal) :
    genus (GlobalResolution.datum data wall right geometry.firstLocal
        hCompatible).sourceGraph =
      genus data.sourceGraph :=
  (GlobalResolution.sourceGraph_genus_eq_iff_block_card data wall right
    geometry.firstLocal hCompatible).mpr (firstLocal_card_blocks geometry)

/-- `M⁽²⁾` preserves the quotient-source genus too. -/
theorem secondLocal_sourceGenus_eq (geometry : Geometry data wall)
    (right : target.edges → Bool)
    (hCompatible :
      GlobalResolution.OldCompatible data wall right geometry.secondLocal) :
    genus (GlobalResolution.datum data wall right geometry.secondLocal
        hCompatible).sourceGraph =
      genus data.sourceGraph :=
  (GlobalResolution.sourceGraph_genus_eq_iff_block_card data wall right
    geometry.secondLocal hCompatible).mpr (secondLocal_card_blocks geometry)

/-- The three actual arbitrary-degree Figure 34 candidates.

This is the literal reading of Figure 34, all three members over one datum.
It is what `balance_M_kk` is stated against, and it is **not instantiable at
an actual `w2Mkk` source profile**: see
`W2MkkSourceCandidates.no_common_geometry`.  The instantiable form is
`swappedCandidates` below. -/
noncomputable def candidates (geometry : Geometry data wall)
    (first : DivalentPattern (data := data) (wall := wall)
      geometry.first geometry.firstLocal)
    (second : DivalentPattern (data := data) (wall := wall)
      geometry.first geometry.secondLocal)
    (third : DivalentPattern (data := data) (wall := wall)
      geometry.first geometry.thirdLocal) :
    Fin 3 → CertifiedCandidate data :=
  ![first.certified (firstLocal_contracts geometry),
    second.certified (secondLocal_contracts geometry),
    third.certified (thirdLocal_contracts geometry)]

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- Equation (8) packaged with the three globally assembled candidates. -/
noncomputable def balancedFamily (geometry : Geometry data wall)
    (first : DivalentPattern (data := data) (wall := wall)
      geometry.first geometry.firstLocal)
    (second : DivalentPattern (data := data) (wall := wall)
      geometry.first geometry.secondLocal)
    (third : DivalentPattern (data := data) (wall := wall)
      geometry.first geometry.thirdLocal)
    (matrix : Fin 3 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate) (c₁ c₂ c₃ s : ℚ)
    (hdet : ∀ i, (matrix i).det =
      ![c₁ / ((geometry.k₁ : ℚ) - 1) + c₂ / (geometry.k₂ : ℚ) + s,
        c₁ / (geometry.k₁ : ℚ) + c₂ / ((geometry.k₂ : ℚ) - 1) + s,
        c₃ / ((geometry.k₁ : ℚ) + geometry.k₂) + s] i)
    (hleft : c₁ / (geometry.k₁ : ℚ) +
      c₂ / (geometry.k₂ : ℚ) + s = 0)
    (hright : c₃ / ((geometry.k₁ : ℚ) + geometry.k₂ - 1) + s = 0)
    (hAgree : ∀ i j,
      AgreeOffColumn (matrix i) (matrix j) wallColumn) :
    Family (coordinate := coordinate) 3 data where
  candidate := candidates geometry first second third
  matrix := matrix
  wallColumn := wallColumn
  weight := ![(geometry.k₁ : ℚ) - 1, (geometry.k₂ : ℚ) - 1,
    (geometry.k₁ : ℚ) + geometry.k₂]
  positiveBalance := by
    have hk₁ : (1 : ℚ) < (geometry.k₁ : ℚ) := by
      exact_mod_cast geometry.one_lt_k₁
    have hk₂ : (1 : ℚ) < (geometry.k₂ : ℚ) := by
      exact_mod_cast geometry.one_lt_k₂
    simpa only [hdet] using balance_M_kk hk₁ hk₂ hleft hright
  agreeOffWall := hAgree

/-- Full arbitrary-degree continuation for source case M-kk. -/
theorem exists_valid_positive_exit (geometry : Geometry data wall)
    (first : DivalentPattern (data := data) (wall := wall)
      geometry.first geometry.firstLocal)
    (second : DivalentPattern (data := data) (wall := wall)
      geometry.first geometry.secondLocal)
    (third : DivalentPattern (data := data) (wall := wall)
      geometry.first geometry.thirdLocal)
    (matrix : Fin 3 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate) (c₁ c₂ c₃ s : ℚ)
    (hdet : ∀ i, (matrix i).det =
      ![c₁ / ((geometry.k₁ : ℚ) - 1) + c₂ / (geometry.k₂ : ℚ) + s,
        c₁ / (geometry.k₁ : ℚ) + c₂ / ((geometry.k₂ : ℚ) - 1) + s,
        c₃ / ((geometry.k₁ : ℚ) + geometry.k₂) + s] i)
    (hleft : c₁ / (geometry.k₁ : ℚ) +
      c₂ / (geometry.k₂ : ℚ) + s = 0)
    (hright : c₃ / ((geometry.k₁ : ℚ) + geometry.k₂ - 1) + s = 0)
    (hAgree : ∀ i j,
      AgreeOffColumn (matrix i) (matrix j) wallColumn)
    (hValid : data.Valid) (incoming : Fin 3)
    (hincoming : (matrix incoming).det ≠ 0)
    (z incomingVelocity : coordinate → ℚ)
    (outgoingVelocity : Fin 3 → coordinate → ℚ)
    (hz : z wallColumn = 0)
    (hzpos : ∀ i, i ≠ wallColumn → 0 < z i)
    (hSystems : ∀ outgoing,
      (matrix incoming).mulVec incomingVelocity =
        (matrix outgoing).mulVec (outgoingVelocity outgoing))
    (hIncomingDirection : incomingVelocity wallColumn < 0) :
    ∃ outgoing,
      (candidates geometry first second third outgoing).datum.Valid ∧
      (matrix incoming).det * (matrix outgoing).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        (matrix outgoing).mulVec
            (z + t • outgoingVelocity outgoing) =
          (matrix incoming).mulVec z +
            t • (matrix incoming).mulVec incomingVelocity := by
  exact (balancedFamily geometry first second third matrix wallColumn
    c₁ c₂ c₃ s hdet hleft hright hAgree).exists_valid_positive_exit
      hValid incoming hincoming z incomingVelocity outgoingVelocity hz hzpos
      (fun outgoing _ ↦ hSystems outgoing) hIncomingDirection

/-! ## The branch-swapped second member

Figure 34's two detaching members cannot share one gluing datum (see the
module docstring).  What follows is the M-kk mirror of
`GlobalM11Arbitrary.SwappedDatum` / `remoteCertified` and of `GlobalM1k`'s
`section Swapped`: the second member is taken over the datum branch-swapped
across the `t₂` branch, transposing the sheet `M⁽¹⁾` detaches with a sheet of
the **other** endpoint block, and is still certified *against the original
datum* because the branch swap preserves validity.
-/

section Swapped

/-- The branch swap fixes the wall partition as a term: the wall vertex is
outside the moved branch.  This is `W3FourDisjointness`'s
`branchSwapOfPerm_vertexPartition_wall` at a transposition, and a local copy
of `GlobalM1k.swappedDatum_vertexPartition_wall`, proved here so that
`GlobalMkk` acquires no dependency on either file. -/
theorem swappedDatum_vertexPartition_wall (root : target.V) (hRoot : root ≠ wall)
    (p q : Fin degree) (hTogether : (data.vertexPartition wall).Rel p q) :
    (SwappedDatum data wall root hRoot p q hTogether).vertexPartition wall =
      data.vertexPartition wall := by
  change (data.vertexPartition wall).relabel
    (GluingDatum.SheetRelabeling.togglePermutation
      (TargetBranchRegion.vertexMoved wall root hRoot wall) (Equiv.swap p q)) = _
  rw [TargetBranchRegion.vertexMoved_wall]
  cases hPartition : data.vertexPartition wall
  rfl

/-- An occurrence outside the moved branch keeps its partition.  Local copy of
`W2MkkSourceCandidates.branchSwapped_edgePartition_of_fixed`, which lives in a
file that imports this one. -/
theorem swappedDatum_edgePartition_of_fixed (root : target.V) (hRoot : root ≠ wall)
    (p q : Fin degree) (hTogether : (data.vertexPartition wall).Rel p q)
    (edge : target.edges)
    (hFixed : TargetBranchRegion.edgeMoved wall root hRoot edge = false) :
    (SwappedDatum data wall root hRoot p q hTogether).edgePartition edge =
      data.edgePartition edge := by
  change (data.edgePartition edge).relabel
    (GluingDatum.SheetRelabeling.togglePermutation
      (TargetBranchRegion.edgeMoved wall root hRoot edge) (Equiv.swap p q)) = _
  rw [hFixed]
  apply SheetPartition.ext_repr
  rfl

/-- An occurrence inside the moved branch is relabelled by the transposition.
Local copy of `W2MkkSourceCandidates.branchSwapped_edgePartition_of_moved`. -/
theorem swappedDatum_edgePartition_of_moved (root : target.V) (hRoot : root ≠ wall)
    (p q : Fin degree) (hTogether : (data.vertexPartition wall).Rel p q)
    (edge : target.edges)
    (hMoved : TargetBranchRegion.edgeMoved wall root hRoot edge = true) :
    (SwappedDatum data wall root hRoot p q hTogether).edgePartition edge =
      (data.edgePartition edge).relabel (Equiv.swap p q) := by
  change (data.edgePartition edge).relabel
    (GluingDatum.SheetRelabeling.togglePermutation
      (TargetBranchRegion.edgeMoved wall root hRoot edge) (Equiv.swap p q)) = _
  rw [hMoved]
  rfl

/-- A transposition of two sheets of one wall block carries any refinement of
the wall partition to another one. -/
theorem relabel_refines_wall (partition : SheetPartition degree)
    (hRefines : partition.Refines (data.vertexPartition wall))
    (p q : Fin degree) (hTogether : (data.vertexPartition wall).Rel p q) :
    (partition.relabel (Equiv.swap p q)).Refines (data.vertexPartition wall) := by
  intro i j hij
  have hSwap := (data.vertexPartition wall).swap_apply_rel_self_of_rel hTogether
  have hMoved : partition.Rel (Equiv.swap p q i) (Equiv.swap p q j) := by
    refine (partition.relabel_rel_iff (Equiv.swap p q) (Equiv.swap p q i)
      (Equiv.swap p q j)).mp ?_
    simpa only [Equiv.swap_apply_self] using hij
  exact ((hSwap i).symm.trans (hRefines.rel hMoved)).trans (hSwap j)

namespace Geometry

/-- The M-kk gauge move: transpose the sheet `M⁽¹⁾` detaches with a sheet of
the other endpoint block, across the branch through `root`. -/
abbrev swappedDatum (geometry : Geometry data wall) (root : target.V)
    (hRoot : root ≠ wall) : GluingDatum target degree :=
  SwappedDatum data wall root hRoot geometry.first geometry.second
    geometry.wall_together

@[simp] theorem swappedDatum_vertexPartition (geometry : Geometry data wall)
    (root : target.V) (hRoot : root ≠ wall) :
    (geometry.swappedDatum root hRoot).vertexPartition wall =
      data.vertexPartition wall :=
  _root_.DraismaVargas.LocalCases.GlobalMkk.swappedDatum_vertexPartition_wall
    root hRoot _ _ _

theorem swappedDatum_edgePartition_fixed (geometry : Geometry data wall)
    (root : target.V) (hRoot : root ≠ wall) (edge : target.edges)
    (hFixed : TargetBranchRegion.edgeMoved wall root hRoot edge = false) :
    (geometry.swappedDatum root hRoot).edgePartition edge =
      data.edgePartition edge :=
  _root_.DraismaVargas.LocalCases.GlobalMkk.swappedDatum_edgePartition_of_fixed
    root hRoot _ _ _ edge hFixed

theorem swappedDatum_edgePartition_moved (geometry : Geometry data wall)
    (root : target.V) (hRoot : root ≠ wall) (edge : target.edges)
    (hMoved : TargetBranchRegion.edgeMoved wall root hRoot edge = true) :
    (geometry.swappedDatum root hRoot).edgePartition edge =
      (data.edgePartition edge).relabel
        (Equiv.swap geometry.first geometry.second) :=
  _root_.DraismaVargas.LocalCases.GlobalMkk.swappedDatum_edgePartition_of_moved
    root hRoot _ _ _ edge hMoved

/-- **The selected M-kk geometry over the branch-swapped datum.**  The wall
partition is fixed, so every field that speaks about it transports verbatim;
the `t₂` endpoint partition is relabelled by the transposition, which
exchanges the roles of the two endpoint blocks.  The two block sizes are
therefore *preserved*, and `swapped.secondLocal` detaches the same sheet that
`geometry.firstLocal` does -- now out of the block of size `k₂`.  That is
exactly Figure 34's `M⁽²⁾`, and it is the `M⁽¹⁾`/`M⁽²⁾` exchange recorded by
`W2MkkSourceCandidates.branchSwap_moves_pinSheet`. -/
def swapped (geometry : Geometry data wall) (root : target.V)
    (hRoot : root ≠ wall) : Geometry (geometry.swappedDatum root hRoot) wall where
  endpoint := geometry.endpoint.relabel (Equiv.swap geometry.first geometry.second)
  first := geometry.second
  firstRemainder :=
    Equiv.swap geometry.first geometry.second geometry.firstRemainder
  second := geometry.first
  secondRemainder :=
    Equiv.swap geometry.first geometry.second geometry.secondRemainder
  endpoint_refines := by
    rw [geometry.swappedDatum_vertexPartition root hRoot]
    exact relabel_refines_wall geometry.endpoint geometry.endpoint_refines
      geometry.first geometry.second geometry.wall_together
  wall_together := by
    rw [geometry.swappedDatum_vertexPartition root hRoot]
    exact geometry.wall_together.symm
  separate := by
    intro hRel
    refine geometry.separate ?_
    refine (geometry.endpoint.relabel_rel_iff
      (Equiv.swap geometry.first geometry.second) geometry.first
      geometry.second).mp ?_
    rwa [Equiv.swap_apply_left, Equiv.swap_apply_right]
  first_together := by
    have hRel := (geometry.endpoint.relabel_rel_iff
      (Equiv.swap geometry.first geometry.second) geometry.first
      geometry.firstRemainder).mpr geometry.first_together
    rwa [Equiv.swap_apply_left] at hRel
  second_together := by
    have hRel := (geometry.endpoint.relabel_rel_iff
      (Equiv.swap geometry.first geometry.second) geometry.second
      geometry.secondRemainder).mpr geometry.second_together
    rwa [Equiv.swap_apply_right] at hRel
  first_ne := by
    intro hEq
    refine geometry.first_ne ?_
    have hImage := congrArg (Equiv.swap geometry.first geometry.second) hEq
    rwa [Equiv.swap_apply_right, Equiv.swap_apply_self] at hImage
  second_ne := by
    intro hEq
    refine geometry.second_ne ?_
    have hImage := congrArg (Equiv.swap geometry.first geometry.second) hEq
    rwa [Equiv.swap_apply_left, Equiv.swap_apply_self] at hImage
  k₁ := geometry.k₁
  k₂ := geometry.k₂
  one_lt_k₁ := geometry.one_lt_k₁
  one_lt_k₂ := geometry.one_lt_k₂
  firstCard := by
    have hCard := geometry.endpoint.relabel_blockCard
      (Equiv.swap geometry.first geometry.second) geometry.first
    rw [Equiv.swap_apply_left] at hCard
    rw [hCard]
    exact geometry.firstCard
  secondCard := by
    have hCard := geometry.endpoint.relabel_blockCard
      (Equiv.swap geometry.first geometry.second) geometry.second
    rw [Equiv.swap_apply_right] at hCard
    rw [hCard]
    exact geometry.secondCard
  wallCard := by
    rw [geometry.swappedDatum_vertexPartition root hRoot]
    have hBlock : (data.vertexPartition wall).block geometry.first =
        (data.vertexPartition wall).block geometry.second :=
      SheetPartition.block_eq_of_rel _ geometry.wall_together
    simpa only [SheetPartition.blockCard, ← hBlock] using geometry.wallCard

theorem swapped_k₁ (geometry : Geometry data wall) (root : target.V)
    (hRoot : root ≠ wall) : (geometry.swapped root hRoot).k₁ = geometry.k₁ := rfl

theorem swapped_k₂ (geometry : Geometry data wall) (root : target.V)
    (hRoot : root ≠ wall) : (geometry.swapped root hRoot).k₂ = geometry.k₂ := rfl

theorem swapped_second (geometry : Geometry data wall) (root : target.V)
    (hRoot : root ≠ wall) :
    (geometry.swapped root hRoot).second = geometry.first := rfl

end Geometry

/-- **The branch-swapped member is certified against the original datum.**
A divalent pattern over the branch-swapped datum is still a globally valid
candidate *for the original datum*: the branch swap preserves validity
(`ResolutionM11.wallBranchSwap_preserves_valid`), and blockwise assembly then
preserves it again.  This is `GlobalM11Arbitrary.remoteCertified` for
Figure 34. -/
noncomputable def DivalentPattern.remoteCertified (geometry : Geometry data wall)
    (root : target.V) (hRoot : root ≠ wall) {distinguished : Fin degree}
    {selected : LocalResolution degree}
    (pattern : DivalentPattern (data := geometry.swappedDatum root hRoot)
      (wall := wall) distinguished selected)
    (hContracts : selected.ContractsTo
      ((geometry.swappedDatum root hRoot).vertexPartition wall)) :
    CertifiedCandidate data where
  outgoingTarget := TargetExpansion.graph target wall pattern.background.right
  datum := (pattern.candidate hContracts).datum
  valid_of_old := by
    intro hValid
    exact (pattern.candidate hContracts).datum_valid
      (wallBranchSwap_preserves_valid data hValid wall root hRoot geometry.first
        geometry.second geometry.wall_together)

/-- The three actual arbitrary-degree Figure 34 candidates, with the second
member over the branch-swapped datum.  Members one and three keep the original
datum, exactly as in `GlobalM11Arbitrary.candidates`. -/
noncomputable def swappedCandidates (geometry : Geometry data wall)
    (root : target.V) (hRoot : root ≠ wall)
    (first : DivalentPattern (data := data) (wall := wall)
      geometry.first geometry.firstLocal)
    (second : DivalentPattern (data := geometry.swappedDatum root hRoot)
      (wall := wall) (geometry.swapped root hRoot).first
      (geometry.swapped root hRoot).secondLocal)
    (third : DivalentPattern (data := data) (wall := wall)
      geometry.first geometry.thirdLocal) :
    Fin 3 → CertifiedCandidate data :=
  ![first.certified (firstLocal_contracts geometry),
    DivalentPattern.remoteCertified geometry root hRoot second
      (secondLocal_contracts (geometry.swapped root hRoot)),
    third.certified (thirdLocal_contracts geometry)]

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- Equation (8) packaged with the three globally assembled candidates, the
second one remote.  The balance identity is the same `balance_M_kk`, with the
same `k₁` and `k₂`: the branch swap preserves both block sizes
(`Geometry.swapped_k₁`, `Geometry.swapped_k₂`), and which datum a member lives
over does not enter the identity. -/
noncomputable def swappedBalancedFamily (geometry : Geometry data wall)
    (root : target.V) (hRoot : root ≠ wall)
    (first : DivalentPattern (data := data) (wall := wall)
      geometry.first geometry.firstLocal)
    (second : DivalentPattern (data := geometry.swappedDatum root hRoot)
      (wall := wall) (geometry.swapped root hRoot).first
      (geometry.swapped root hRoot).secondLocal)
    (third : DivalentPattern (data := data) (wall := wall)
      geometry.first geometry.thirdLocal)
    (matrix : Fin 3 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate) (c₁ c₂ c₃ s : ℚ)
    (hdet : ∀ i, (matrix i).det =
      ![c₁ / ((geometry.k₁ : ℚ) - 1) + c₂ / (geometry.k₂ : ℚ) + s,
        c₁ / (geometry.k₁ : ℚ) + c₂ / ((geometry.k₂ : ℚ) - 1) + s,
        c₃ / ((geometry.k₁ : ℚ) + geometry.k₂) + s] i)
    (hleft : c₁ / (geometry.k₁ : ℚ) +
      c₂ / (geometry.k₂ : ℚ) + s = 0)
    (hright : c₃ / ((geometry.k₁ : ℚ) + geometry.k₂ - 1) + s = 0)
    (hAgree : ∀ i j,
      AgreeOffColumn (matrix i) (matrix j) wallColumn) :
    Family (coordinate := coordinate) 3 data where
  candidate := swappedCandidates geometry root hRoot first second third
  matrix := matrix
  wallColumn := wallColumn
  weight := ![(geometry.k₁ : ℚ) - 1, (geometry.k₂ : ℚ) - 1,
    (geometry.k₁ : ℚ) + geometry.k₂]
  positiveBalance := by
    have hk₁ : (1 : ℚ) < (geometry.k₁ : ℚ) := by
      exact_mod_cast geometry.one_lt_k₁
    have hk₂ : (1 : ℚ) < (geometry.k₂ : ℚ) := by
      exact_mod_cast geometry.one_lt_k₂
    simpa only [hdet] using balance_M_kk hk₁ hk₂ hleft hright
  agreeOffWall := hAgree

/-- **Full arbitrary-degree continuation for source case M-kk, with the second
member over the branch-swapped datum.**  This is the form an actual `w2Mkk`
profile can instantiate; `exists_valid_positive_exit` above cannot be, because
its three `DivalentPattern`s over one `Geometry` are jointly contradictory for
two-sided detachments (`W2MkkSourceCandidates.no_common_geometry`).

*Why this hypothesis bundle is jointly satisfiable.*  The obstruction is
entirely in the `exterior` fields.  Over one datum both detaching members'
`t₃` conditions pin the detached sheet to the unique sheet that the dangling
occurrence isolates, and one sheet cannot lie in both endpoint blocks.  Here
`first` reads `data.edgePartition` and `second` reads
`(geometry.swappedDatum …).edgePartition`, which differ exactly on the branch
swapped across; the swap fixes the `t₃` occurrence while relabelling the `t₂`
one, so the *same* sheet stays pinned while its endpoint block acquires the
other block's cardinality.  The section *The bundle is inhabited* below turns
this paragraph into a theorem: `PinnedProfile.nonempty_swapped` builds all
three patterns from one consistent set of inputs. -/
theorem exists_valid_positive_exit_swapped (geometry : Geometry data wall)
    (root : target.V) (hRoot : root ≠ wall)
    (first : DivalentPattern (data := data) (wall := wall)
      geometry.first geometry.firstLocal)
    (second : DivalentPattern (data := geometry.swappedDatum root hRoot)
      (wall := wall) (geometry.swapped root hRoot).first
      (geometry.swapped root hRoot).secondLocal)
    (third : DivalentPattern (data := data) (wall := wall)
      geometry.first geometry.thirdLocal)
    (matrix : Fin 3 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate) (c₁ c₂ c₃ s : ℚ)
    (hdet : ∀ i, (matrix i).det =
      ![c₁ / ((geometry.k₁ : ℚ) - 1) + c₂ / (geometry.k₂ : ℚ) + s,
        c₁ / (geometry.k₁ : ℚ) + c₂ / ((geometry.k₂ : ℚ) - 1) + s,
        c₃ / ((geometry.k₁ : ℚ) + geometry.k₂) + s] i)
    (hleft : c₁ / (geometry.k₁ : ℚ) +
      c₂ / (geometry.k₂ : ℚ) + s = 0)
    (hright : c₃ / ((geometry.k₁ : ℚ) + geometry.k₂ - 1) + s = 0)
    (hAgree : ∀ i j,
      AgreeOffColumn (matrix i) (matrix j) wallColumn)
    (hValid : data.Valid) (incoming : Fin 3)
    (hincoming : (matrix incoming).det ≠ 0)
    (z incomingVelocity : coordinate → ℚ)
    (outgoingVelocity : Fin 3 → coordinate → ℚ)
    (hz : z wallColumn = 0)
    (hzpos : ∀ i, i ≠ wallColumn → 0 < z i)
    (hSystems : ∀ outgoing,
      (matrix incoming).mulVec incomingVelocity =
        (matrix outgoing).mulVec (outgoingVelocity outgoing))
    (hIncomingDirection : incomingVelocity wallColumn < 0) :
    ∃ outgoing,
      (swappedCandidates geometry root hRoot first second third
        outgoing).datum.Valid ∧
      (matrix incoming).det * (matrix outgoing).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        (matrix outgoing).mulVec
            (z + t • outgoingVelocity outgoing) =
          (matrix incoming).mulVec z +
            t • (matrix incoming).mulVec incomingVelocity := by
  exact (swappedBalancedFamily geometry root hRoot first second third matrix
    wallColumn c₁ c₂ c₃ s hdet hleft hright
      hAgree).exists_valid_positive_exit hValid incoming hincoming z
      incomingVelocity outgoingVelocity hz hzpos
      (fun outgoing _ ↦ hSystems outgoing) hIncomingDirection

end Swapped

/-! ## The bundle is inhabited

`W2MkkSourceCandidates.no_common_geometry` says the *unswapped* three-pattern
bundle is empty at a real profile for two-sided detachments.  This section proves
the swapped one is **not**: all three patterns are constructed from a single
`PinnedProfile`, whose fields are conditions on `data` and the geometry alone
and contain no second exterior condition to clash with the first.

The separating input the branch swap needs -- that the swap across the `t₂`
branch leaves the `t₃` occurrence alone -- is discharged here from
`graph_connected target` and `genus target = 0` through
`Infrastructure.TargetSeparation`.  No separation hypothesis is carried. -/

section Inhabited

/-- A wall-incident occurrence refines the wall partition: this is a field of
every `GluingDatum`. -/
theorem incident_edgePartition_refines_wall (edge : target.edges)
    (hIncident : ((edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall)) :
    (data.edgePartition edge).Refines (data.vertexPartition wall) := by
  rcases hIncident with hEnd | hEnd
  · exact hEnd ▸ data.refines_left edge
  · exact hEnd ▸ data.refines_right edge

/-- The wall data an actual M-kk profile supplies: a divalent wall with one
occurrence on each side, the `t₂` occurrence partition refining the chosen
endpoint partition, and the `t₃` occurrence isolating the detached sheet.

Every field is a condition on `data`, `wall` and `geometry` separately; there
is no second exterior condition, which is precisely why the bundle this
generates is nonempty where `candidates`' is not. -/
structure PinnedProfile (geometry : Geometry data wall) where
  /-- Which side of the split each old wall occurrence goes to. -/
  right : target.edges → Bool
  /-- The `t₂` occurrence: the only wall occurrence on the retained side. -/
  leftExternal : target.edges
  /-- The `t₃` occurrence: the only wall occurrence on the fresh side. -/
  rightExternal : target.edges
  leftEdges : (([leftExternal] : List target.edges) : Multiset target.edges) =
    (TargetExpansion.wallEdgesAssigned target wall right false).val
  rightEdges : (([rightExternal] : List target.edges) : Multiset target.edges) =
    (TargetExpansion.wallEdgesAssigned target wall right true).val
  /-- Base II.2: the `t₂` direction's occurrence partition is the endpoint
  partition, or finer. -/
  endpointRefines : (data.edgePartition leftExternal).Refines geometry.endpoint
  /-- The dangling occurrence above `t₃` isolates the detached sheet. -/
  pinned :
    (data.edgePartition rightExternal).block geometry.first = {geometry.first}

namespace PinnedProfile

variable {geometry : Geometry data wall}

theorem leftExternal_mem (profile : PinnedProfile geometry) :
    profile.leftExternal ∈
      TargetExpansion.wallEdgesAssigned target wall profile.right false := by
  have hMem : profile.leftExternal ∈
      (([profile.leftExternal] : List target.edges) :
        Multiset target.edges) := by simp
  rw [profile.leftEdges] at hMem
  exact hMem

theorem rightExternal_mem (profile : PinnedProfile geometry) :
    profile.rightExternal ∈
      TargetExpansion.wallEdgesAssigned target wall profile.right true := by
  have hMem : profile.rightExternal ∈
      (([profile.rightExternal] : List target.edges) :
        Multiset target.edges) := by simp
  rw [profile.rightEdges] at hMem
  exact hMem

theorem leftExternal_incident (profile : PinnedProfile geometry) :
    ((profile.leftExternal : target.V × target.V).1 = wall ∨
      (profile.leftExternal : target.V × target.V).2 = wall) :=
  ((TargetExpansion.mem_wallEdgesAssigned target wall profile.right false
    profile.leftExternal).mp profile.leftExternal_mem).1

theorem rightExternal_incident (profile : PinnedProfile geometry) :
    ((profile.rightExternal : target.V × target.V).1 = wall ∨
      (profile.rightExternal : target.V × target.V).2 = wall) :=
  ((TargetExpansion.mem_wallEdgesAssigned target wall profile.right true
    profile.rightExternal).mp profile.rightExternal_mem).1

theorem right_leftExternal (profile : PinnedProfile geometry) :
    profile.right profile.leftExternal = false :=
  ((TargetExpansion.mem_wallEdgesAssigned target wall profile.right false
    profile.leftExternal).mp profile.leftExternal_mem).2

theorem right_rightExternal (profile : PinnedProfile geometry) :
    profile.right profile.rightExternal = true :=
  ((TargetExpansion.mem_wallEdgesAssigned target wall profile.right true
    profile.rightExternal).mp profile.rightExternal_mem).2

/-- The two wall occurrences are distinct: they sit on opposite sides of the
split. -/
theorem external_ne (profile : PinnedProfile geometry) :
    profile.leftExternal ≠ profile.rightExternal := by
  intro hEq
  have hFalse := profile.right_leftExternal
  rw [hEq, profile.right_rightExternal] at hFalse
  exact Bool.noConfusion hFalse

theorem eq_leftExternal (profile : PinnedProfile geometry) (edge : target.edges)
    (hIncident : ((edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall))
    (hSide : profile.right edge = false) : edge = profile.leftExternal := by
  have hMem : edge ∈
      TargetExpansion.wallEdgesAssigned target wall profile.right false :=
    (TargetExpansion.mem_wallEdgesAssigned target wall profile.right false
      edge).mpr ⟨hIncident, hSide⟩
  have hVal : edge ∈ (([profile.leftExternal] : List target.edges) :
      Multiset target.edges) := by
    rw [profile.leftEdges]
    exact hMem
  simpa using hVal

theorem eq_rightExternal (profile : PinnedProfile geometry) (edge : target.edges)
    (hIncident : ((edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall))
    (hSide : profile.right edge = true) : edge = profile.rightExternal := by
  have hMem : edge ∈
      TargetExpansion.wallEdgesAssigned target wall profile.right true :=
    (TargetExpansion.mem_wallEdgesAssigned target wall profile.right true
      edge).mpr ⟨hIncident, hSide⟩
  have hVal : edge ∈ (([profile.rightExternal] : List target.edges) :
      Multiset target.edges) := by
    rw [profile.rightEdges]
    exact hMem
  simpa using hVal

/-- The background in which every *other* wall block keeps the whole wall
partition.  It is the shape `M11SourceCandidates.joinedBackground` has, stated
over an arbitrary datum so that the branch-swapped one can use it too. -/
noncomputable def background (datum : GluingDatum target degree)
    (profile : PinnedProfile geometry) (distinguished : Fin degree) :
    Background datum wall distinguished where
  right := profile.right
  resolution := fun _ ↦ thirdResolution (datum.vertexPartition wall)
  contracts := fun _ _ ↦ thirdResolution_contracts _
  exterior := by
    intro edge hIncident _ _
    simpa only [thirdResolution, joinedResolutionAt, ite_self] using
      incident_edgePartition_refines_wall (data := datum) edge hIncident
  leftEdges := [profile.leftExternal]
  rightEdges := [profile.rightExternal]
  leftEdges_eq := profile.leftEdges
  rightEdges_eq := profile.rightEdges
  left_riemannHurwitz := fun anchor _ _ ↦ by
    simpa only [List.map_cons, List.map_nil] using
      thirdResolution_left_riemannHurwitzAtBlock (datum.vertexPartition wall)
        (datum.edgePartition profile.leftExternal) anchor
  right_riemannHurwitz := fun anchor _ _ ↦ by
    simpa only [List.map_cons, List.map_nil] using
      thirdResolution_right_riemannHurwitzAtBlock (datum.vertexPartition wall)
        (datum.edgePartition profile.rightExternal) anchor

@[simp] theorem background_right (datum : GluingDatum target degree)
    (profile : PinnedProfile geometry) (distinguished : Fin degree) :
    (profile.background datum distinguished).right = profile.right := rfl

/-- **Member 1**, Figure 34's `M⁽¹⁾`, over the original datum. -/
noncomputable def firstPattern (profile : PinnedProfile geometry) :
    DivalentPattern (data := data) (wall := wall)
      geometry.first geometry.firstLocal where
  background := profile.background data geometry.first
  leftExternal := profile.leftExternal
  rightExternal := profile.rightExternal
  leftEdges := rfl
  rightEdges := rfl
  exterior := by
    intro edge hIncident
    by_cases hSide : profile.right edge = false
    · have hEdge : edge = profile.leftExternal :=
        profile.eq_leftExternal edge hIncident hSide
      subst hEdge
      rw [background_right, profile.right_leftExternal]
      exact profile.endpointRefines
    · have hTrue : profile.right edge = true := by
        simpa using hSide
      have hEdge : edge = profile.rightExternal :=
        profile.eq_rightExternal edge hIncident hTrue
      subst hEdge
      rw [background_right, profile.right_rightExternal]
      exact SheetPartition.refines_detachSheet_of_block_singleton _
        (data.vertexPartition wall) geometry.first geometry.firstRemainder
        geometry.first_ne
        (geometry.endpoint_refines.rel geometry.first_together)
        (incident_edgePartition_refines_wall _ hIncident) profile.pinned

/-- **Member 3**, Figure 34's `M⁽³⁾`, over the original datum.  It imposes no
occurrence condition at all. -/
noncomputable def thirdPattern (profile : PinnedProfile geometry) :
    DivalentPattern (data := data) (wall := wall)
      geometry.first geometry.thirdLocal where
  background := profile.background data geometry.first
  leftExternal := profile.leftExternal
  rightExternal := profile.rightExternal
  leftEdges := rfl
  rightEdges := rfl
  exterior := by
    intro edge hIncident
    simpa only [thirdResolution, joinedResolutionAt, ite_self] using
      incident_edgePartition_refines_wall (data := data) edge hIncident

/-- The root of the branch the gauge move is taken across: the far endpoint of
the `t₂` occurrence. -/
def root (profile : PinnedProfile geometry) : target.V :=
  TargetSeparation.farEndpoint wall profile.leftExternal

theorem root_ne (profile : PinnedProfile geometry) : profile.root ≠ wall :=
  TargetSeparation.farEndpoint_ne profile.leftExternal_incident

/-- The gauge move moves the `t₂` occurrence.  No genus hypothesis is needed. -/
theorem leftExternal_moved (profile : PinnedProfile geometry) :
    TargetBranchRegion.edgeMoved wall profile.root profile.root_ne
        profile.leftExternal = true :=
  TargetSeparation.edgeMoved_self_eq_true profile.leftExternal_incident

/-- **The separation, discharged.**  On a connected genus-zero target the
branch through the `t₂` occurrence does not move the `t₃` occurrence.  This is
`TargetSeparation.edgeMoved_eq_false`, so the separation need not be carried as
a hypothesis (as it is in `W2M1kSourceCandidates`). -/
theorem rightExternal_fixed (profile : PinnedProfile geometry)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    TargetBranchRegion.edgeMoved wall profile.root profile.root_ne
        profile.rightExternal = false :=
  TargetSeparation.edgeMoved_eq_false hConnected hGenus
    profile.leftExternal_incident profile.rightExternal_incident
    profile.external_ne

/-- **Member 2**, Figure 34's `M⁽²⁾`, over the branch-swapped datum.

The `t₃` occurrence is untouched by the swap, so it still isolates the *same*
sheet, and that sheet is what `(geometry.swapped …).secondLocal` detaches; the
`t₂` occurrence is relabelled by the transposition, exactly as the endpoint
partition of `Geometry.swapped` is, so the left condition transports.  No new
hypothesis appears: both conditions come from the one `PinnedProfile` that
already produced member 1. -/
noncomputable def swappedSecondPattern (profile : PinnedProfile geometry)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    DivalentPattern (data := geometry.swappedDatum profile.root profile.root_ne)
      (wall := wall) (geometry.swapped profile.root profile.root_ne).first
      (geometry.swapped profile.root profile.root_ne).secondLocal where
  background := profile.background
    (geometry.swappedDatum profile.root profile.root_ne)
    (geometry.swapped profile.root profile.root_ne).first
  leftExternal := profile.leftExternal
  rightExternal := profile.rightExternal
  leftEdges := rfl
  rightEdges := rfl
  exterior := by
    intro edge hIncident
    by_cases hSide : profile.right edge = false
    · have hEdge : edge = profile.leftExternal :=
        profile.eq_leftExternal edge hIncident hSide
      subst hEdge
      rw [background_right, profile.right_leftExternal,
        geometry.swappedDatum_edgePartition_moved profile.root profile.root_ne
          profile.leftExternal profile.leftExternal_moved]
      exact SheetPartition.relabel_refines profile.endpointRefines _
    · have hTrue : profile.right edge = true := by
        simpa using hSide
      have hEdge : edge = profile.rightExternal :=
        profile.eq_rightExternal edge hIncident hTrue
      subst hEdge
      rw [background_right, profile.right_rightExternal]
      refine SheetPartition.refines_detachSheet_of_block_singleton _
        ((geometry.swappedDatum profile.root profile.root_ne).vertexPartition
          wall)
        (geometry.swapped profile.root profile.root_ne).second
        (geometry.swapped profile.root profile.root_ne).secondRemainder
        (geometry.swapped profile.root profile.root_ne).second_ne
        ((geometry.swapped profile.root profile.root_ne).endpoint_refines.rel
          (geometry.swapped profile.root profile.root_ne).second_together)
        (incident_edgePartition_refines_wall _ hIncident) ?_
      rw [geometry.swappedDatum_edgePartition_fixed profile.root profile.root_ne
        profile.rightExternal (profile.rightExternal_fixed hConnected hGenus)]
      exact profile.pinned

/-- **The swapped bundle is inhabited.**  All three members of Figure 34 exist
over one `PinnedProfile`, the second one over the branch-swapped datum.
Compare `W2MkkSourceCandidates.no_common_geometry`, which says the *unswapped*
three patterns over one datum cannot all exist at a real profile. -/
theorem nonempty_swapped (profile : PinnedProfile geometry)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    Nonempty (DivalentPattern (data := data) (wall := wall)
        geometry.first geometry.firstLocal) ∧
      Nonempty (DivalentPattern
        (data := geometry.swappedDatum profile.root profile.root_ne)
        (wall := wall) (geometry.swapped profile.root profile.root_ne).first
        (geometry.swapped profile.root profile.root_ne).secondLocal) ∧
      Nonempty (DivalentPattern (data := data) (wall := wall)
        geometry.first geometry.thirdLocal) :=
  ⟨⟨profile.firstPattern⟩, ⟨profile.swappedSecondPattern hConnected hGenus⟩,
    ⟨profile.thirdPattern⟩⟩

/-- The three globally assembled Figure 34 candidates over one
`PinnedProfile`: no pattern is assumed, all three are built. -/
noncomputable def candidates (profile : PinnedProfile geometry)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    Fin 3 → CertifiedCandidate data :=
  swappedCandidates geometry profile.root profile.root_ne profile.firstPattern
    (profile.swappedSecondPattern hConnected hGenus) profile.thirdPattern

end PinnedProfile

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **Equation (8)'s positive exit for case M-kk with no assumed patterns.**
The three Figure 34 members are constructed from one `PinnedProfile`, the
second over the branch-swapped datum; only the length-matrix hypotheses
remain.  This is the form a wall input at an actual `w2Mkk` profile needs,
and it is the proof that the bundle `exists_valid_positive_exit_swapped` asks
for is not empty. -/
theorem exists_valid_positive_exit_pinned {geometry : Geometry data wall}
    (profile : PinnedProfile geometry)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (matrix : Fin 3 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate) (c₁ c₂ c₃ s : ℚ)
    (hdet : ∀ i, (matrix i).det =
      ![c₁ / ((geometry.k₁ : ℚ) - 1) + c₂ / (geometry.k₂ : ℚ) + s,
        c₁ / (geometry.k₁ : ℚ) + c₂ / ((geometry.k₂ : ℚ) - 1) + s,
        c₃ / ((geometry.k₁ : ℚ) + geometry.k₂) + s] i)
    (hleft : c₁ / (geometry.k₁ : ℚ) +
      c₂ / (geometry.k₂ : ℚ) + s = 0)
    (hright : c₃ / ((geometry.k₁ : ℚ) + geometry.k₂ - 1) + s = 0)
    (hAgree : ∀ i j,
      AgreeOffColumn (matrix i) (matrix j) wallColumn)
    (hValid : data.Valid) (incoming : Fin 3)
    (hincoming : (matrix incoming).det ≠ 0)
    (z incomingVelocity : coordinate → ℚ)
    (outgoingVelocity : Fin 3 → coordinate → ℚ)
    (hz : z wallColumn = 0)
    (hzpos : ∀ i, i ≠ wallColumn → 0 < z i)
    (hSystems : ∀ outgoing,
      (matrix incoming).mulVec incomingVelocity =
        (matrix outgoing).mulVec (outgoingVelocity outgoing))
    (hIncomingDirection : incomingVelocity wallColumn < 0) :
    ∃ outgoing,
      (profile.candidates hConnected hGenus outgoing).datum.Valid ∧
      (matrix incoming).det * (matrix outgoing).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        (matrix outgoing).mulVec
            (z + t • outgoingVelocity outgoing) =
          (matrix incoming).mulVec z +
            t • (matrix incoming).mulVec incomingVelocity :=
  exists_valid_positive_exit_swapped geometry profile.root profile.root_ne
    profile.firstPattern (profile.swappedSecondPattern hConnected hGenus)
    profile.thirdPattern matrix wallColumn c₁ c₂ c₃ s hdet hleft hright hAgree
    hValid incoming hincoming z incomingVelocity outgoingVelocity hz hzpos
    hSystems hIncomingDirection

end Inhabited

end DraismaVargas.LocalCases.GlobalMkk
