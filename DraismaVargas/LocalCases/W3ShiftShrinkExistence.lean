import DraismaVargas.LocalCases.GlobalResolution
import DraismaVargas.LocalCases.ResolutionMkk
import DraismaVargas.LocalCases.W3FourDisjointness
import DraismaVargas.Infrastructure.TargetSeparation

/-!
# The Position II.b shrink member: a genus count and a gauge

Source: Draisma--Vargas Part I: Position II and its two sub-cases at a
trivalent wall (case `{w3}`), case `{w3-r1-nd3-t2-(a>k₄)}`, Figure 29 and
Equation (3), together with the subsection on isomorphism classes of gluing
datums: the **tree-swap** (one global permutation), the **branch-swap** (one
permutation above one branch only) and the gluing-datum isomorphism
`definition-gd-iso` (*one permutation `πₓ` per target element*).

This file proves two facts about Figure 29's Position II.b member.

## `ResolutionMkk.detachedResolution` raises the source genus

`GlobalResolution.sourceGraph_genus_eq_iff_block_card` preserves the source
genus exactly when

`#newEdge.Blocks + #wall.Blocks = #left.Blocks + #right.Blocks`.

`detachedResolution` sets `right := wall` while detaching one sheet on the new
edge, so its left-hand side is one too large and
`detachedResolution_sourceGenus_eq_succ` below turns that into a sharp
negative theorem: **any** candidate assembled from that shape has source genus
exactly one greater than the datum's.  Geometrically the detached singleton
and the residual class over `t₁` join the same pair of ends, which is the
parallel pair the source excludes by its no-cycle argument in Position II.b.

`ResolutionMkk.bothDetachedResolution` is the shape the source actually
produces -- Position II.b's `A⁽ᵠ⁾ = A₀ ∖ {x}`, and equally Figure 34's
`M⁽¹⁾`, whose retained class `A⁽¹⁾ = e₃` has `|A₀| - 1 = k₁ + k₂ - 1` sheets --
and `bothDetachedResolution_card_blocks` closes the Euler count exactly.
`detachedResolution` and its companion lemmas are kept, since other modules
use them.

## Position II.b's sheet condition is a gauge, not an obstruction

Position II.b needs a sheet `x` of `eₐ` lying in neither `e_b` nor `e_c`:
Part I's Position II gives `A'` incident to `e_α⁽ᵠ⁾`, Position II.b's
`|A'| = |e_α⁽ᵠ⁾|` then forces `A' = eₐ`, the cycle argument in the same
sentence forces
`A⁽ᵠ⁾ = A₀ ∖ {x}` with `x ∈ A'`, and the clause "the ends of `e_β⁽ᵠ⁾` and
`e_γ⁽ᵠ⁾` are above `v`" forces `e_b ∪ e_c ⊆ A⁽ᵠ⁾`, hence `x ∉ e_b ∪ e_c`.  So
`W3ShiftSourceCandidates.HasShrinkSheet` is exactly the source's requirement
and not a formalization artefact.

At a **fixed** gluing-datum value the case's arithmetic does not supply it,
and `no_private_sheet_forces_double_cover` below says precisely when it fails:
a shrink-sheet-free configuration is exactly one in which every sheet of `A₀`
lies in exactly **two** of `e₂, e₃, e₄` -- the "theta" configuration, of which
`|A₀| = 3`, `k = (2,2,2)` is the smallest instance.

**This does not obstruct Part I's argument.**  The configuration is moved by
DV's own branch-swap, which permutes sheets above **one branch** of
`T ∖ {w₀}` only, while the gluing-datum isomorphism allows one permutation per
target element, so at a trivalent `w₀` the three classes `e₂, e₃, e₄` may be
permuted inside `A₀` *independently*; only their cardinalities are invariant.
`exists_branchGauge_shrinkSheet` produces, from any datum of the case, a
branch-swapped copy carrying Position II.b's sheet on the prescribed
direction, with `A₀` and `eₐ` literally unchanged and both other class indices
preserved; `exists_shrinkSheet_of_genus_zero` discharges its branch flags from
`graph_connected target` and `genus target = 0` alone, through
`Infrastructure.TargetSeparation`.  `theta_configuration_moved_by_one_branchSwap`
exhibits the same move on the smallest theta configuration.

The consequence is the same as for Figure 28 (see `W3FourSourceCandidates`):
Equation (3)'s `(k-1, k+1)` pair lives over branch-swapped wall data, so the
exit is assembled as a gauge family (one base per member plus the gauge
implication), not as six members over one `GluingDatum` value.

## What is not proved here

That `GluingDatum.SheetRelabeling` *is* Part I's `definition-gd-iso`, and that
`ℙ𝒞*(M₀)`'s members may therefore use different representatives of `M₀`, are
readings of the source, exactly as flagged in `W3FourDisjointness`.  The Lean
content is the construction of the swaps and the list of what they do not
move.
-/

namespace DraismaVargas.LocalCases.W3ShiftShrinkExistence

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionMkk

variable {target : CFGraph} {degree : ℕ}

/-! ## The Euler defect of a one-sided detachment -/

/-- **The Euler defect of a local resolution, as a genus shift.**  The
quantitative form of `GlobalResolution.sourceGraph_genus_eq_iff_block_card`:
whatever the resolution's block counts fail the Euler identity by, the source
genus rises by. -/
theorem sourceGenus_datum_eq_add
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : GlobalResolution.OldCompatible data wall right resolution)
    (defect : ℕ)
    (hCard : Fintype.card resolution.newEdge.Blocks +
          Fintype.card (data.vertexPartition wall).Blocks =
        Fintype.card resolution.left.Blocks +
          Fintype.card resolution.right.Blocks + defect) :
    genus (GlobalResolution.datum data wall right resolution hCompatible).sourceGraph =
      genus data.sourceGraph + (defect : ℤ) := by
  have hEdges := GlobalResolution.card_sourceEdge_datum data wall right resolution
    hCompatible
  have hVertices := GlobalResolution.card_sourceVertex_datum_add_wall data wall right
    resolution hCompatible
  simp only [genus, GluingDatum.sourceGraph_edges_card]
  change
    ((Fintype.card
        (GlobalResolution.datum data wall right resolution hCompatible).SourceEdge : ℤ) -
      (Fintype.card
        (GlobalResolution.datum data wall right resolution hCompatible).SourceVertex : ℤ) +
        1 =
      ((Fintype.card data.SourceEdge : ℤ) - (Fintype.card data.SourceVertex : ℤ) + 1) +
        (defect : ℤ))
  omega

/-- **The genus defect of `detachedResolution`, sharp.**  A candidate assembled
from `detachedResolution` on the wall block has source genus **exactly one
greater** than the incoming datum's.  The shape detaches on the new edge only
and keeps the whole wall partition at the retained endpoint, so over `t₁` the
detached singleton and the residual class have the same pair of ends: the
parallel pair excluded in Position II.b, where both detachments are forced.

No user of `detachedResolution` states a genus claim; but any Equation (3)
exit assembled out of this resolution would produce a genus-raising candidate.
The shape to use is `ResolutionMkk.bothDetachedResolution`, whose Euler count
closes (`bothDetachedResolution_card_blocks`). -/
theorem detachedResolution_sourceGenus_eq_succ
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (endpoint : SheetPartition degree)
    (single remainder : Fin degree) (hne : single ≠ remainder)
    (hTogether : endpoint.Rel single remainder)
    (hEndpointRefines : endpoint.Refines (data.vertexPartition wall))
    (hCompatible : GlobalResolution.OldCompatible data wall right
      (detachedResolution (data.vertexPartition wall) endpoint single remainder hne
        hTogether hEndpointRefines)) :
    genus (GlobalResolution.datum data wall right
        (detachedResolution (data.vertexPartition wall) endpoint single remainder hne
          hTogether hEndpointRefines) hCompatible).sourceGraph =
      genus data.sourceGraph + 1 := by
  have hCard : Fintype.card (detachedResolution (data.vertexPartition wall) endpoint
          single remainder hne hTogether hEndpointRefines).newEdge.Blocks +
        Fintype.card (data.vertexPartition wall).Blocks =
      Fintype.card (detachedResolution (data.vertexPartition wall) endpoint single
          remainder hne hTogether hEndpointRefines).left.Blocks +
        Fintype.card (detachedResolution (data.vertexPartition wall) endpoint single
          remainder hne hTogether hEndpointRefines).right.Blocks + 1 := by
    exact detachedResolution_card_blocks (data.vertexPartition wall) endpoint single
      remainder hne hTogether hEndpointRefines
  have := sourceGenus_datum_eq_add data wall right _ hCompatible 1 hCard
  simpa using this

/-- The companion positive statement, on the same footing: a candidate
assembled from the both-sided detachment preserves the source genus.  Stated
here rather than in `ResolutionMkk` because the genus lives in
`GlobalResolution`; the block count it consumes is
`ResolutionMkk.bothDetachedResolution_card_blocks`. -/
theorem bothDetached_sourceGenus_eq
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (endpoint : SheetPartition degree)
    (single remainder : Fin degree) (hne : single ≠ remainder)
    (hWallTogether : (data.vertexPartition wall).Rel single remainder)
    (hTogether : endpoint.Rel single remainder)
    (hEndpointRefines : endpoint.Refines (data.vertexPartition wall))
    (hCompatible : GlobalResolution.OldCompatible data wall right
      (bothDetachedResolution (data.vertexPartition wall) endpoint single remainder hne
        hWallTogether hTogether hEndpointRefines)) :
    genus (GlobalResolution.datum data wall right
        (bothDetachedResolution (data.vertexPartition wall) endpoint single remainder hne
          hWallTogether hTogether hEndpointRefines) hCompatible).sourceGraph =
      genus data.sourceGraph := by
  have hCard : Fintype.card (bothDetachedResolution (data.vertexPartition wall) endpoint
          single remainder hne hWallTogether hTogether hEndpointRefines).newEdge.Blocks +
        Fintype.card (data.vertexPartition wall).Blocks =
      Fintype.card (bothDetachedResolution (data.vertexPartition wall) endpoint single
          remainder hne hWallTogether hTogether hEndpointRefines).left.Blocks +
        Fintype.card (bothDetachedResolution (data.vertexPartition wall) endpoint single
          remainder hne hWallTogether hTogether hEndpointRefines).right.Blocks + 0 := by
    rw [Nat.add_zero]
    exact bothDetachedResolution_card_blocks (data.vertexPartition wall) endpoint single
      remainder hne hWallTogether hTogether hEndpointRefines
  have := sourceGenus_datum_eq_add data wall right _ hCompatible 0 hCard
  simpa using this


/-! ## At a fixed datum: exactly when Position II.b's sheet is missing -/

section FixedDatum

variable {sheetType : Type*} [DecidableEq sheetType]

/-- How many of the three surviving classes a sheet lies in.  Position II.b's
sheet for direction `α` is a sheet of `e_α` of multiplicity one. -/
def multiplicity (classes : Fin 3 → Finset sheetType) (sheet : sheetType) : ℕ :=
  ((Finset.univ : Finset (Fin 3)).filter fun index ↦ sheet ∈ classes index).card

/-- The three class sizes add up to the total multiplicity carried by the wall
block.  This is the double count behind the case's own index identity
`k₂ + k₃ + k₄ = 2|A₀|`. -/
theorem sum_card_eq_sum_multiplicity (whole : Finset sheetType)
    (classes : Fin 3 → Finset sheetType) (hSub : ∀ index, classes index ⊆ whole) :
    (∑ index, (classes index).card) = ∑ sheet ∈ whole, multiplicity classes sheet := by
  classical
  have hCard : ∀ index : Fin 3, (classes index).card =
      ∑ sheet ∈ whole, if sheet ∈ classes index then 1 else 0 := by
    intro index
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr (hSub index)]
  simp only [hCard, multiplicity, Finset.card_filter]
  exact Finset.sum_comm

/-- **The sharpest true statement at a fixed gluing-datum value.**  Suppose no
direction has a Position II.b sheet -- every sheet of every surviving class
lies in a second one -- and every sheet of the wall block lies in some class.
Then the case's index identity `k₂ + k₃ + k₄ = 2|A₀|` forces every sheet of
`A₀` to lie in **exactly two** of the three classes.

So the shrink-sheet-free data are precisely the "theta" configurations: split
`A₀` into three nonempty parts `P₂, P₃, P₄` and take `e_α = A₀ ∖ P_α`.  The
smallest is `|A₀| = 3` with `k = (2,2,2)`, which is
`W3ShiftSourceCandidates.shift_arithmetic_does_not_force_shrinkSheet`'s witness.
The refutation of "some direction always has a shrink sheet" is therefore not
an accident of one example: an infinite family of fixed data has none.

What this does *not* establish is that any of it is an invariant of the wall
datum; see `exists_branchGauge_shrinkSheet` below, where it is dissolved. -/
theorem no_private_sheet_forces_double_cover (whole : Finset sheetType)
    (classes : Fin 3 → Finset sheetType) (hSub : ∀ index, classes index ⊆ whole)
    (hSum : (∑ index, (classes index).card) = 2 * whole.card)
    (hCover : ∀ sheet ∈ whole, ∃ index, sheet ∈ classes index)
    (hNoPrivate : ∀ index, ∀ sheet ∈ classes index,
      ∃ other, other ≠ index ∧ sheet ∈ classes other) :
    ∀ sheet ∈ whole, multiplicity classes sheet = 2 := by
  classical
  have hTwo : ∀ sheet ∈ whole, 2 ≤ multiplicity classes sheet := by
    intro sheet hSheet
    obtain ⟨index, hIndex⟩ := hCover sheet hSheet
    obtain ⟨other, hNe, hOther⟩ := hNoPrivate index sheet hIndex
    have hSubset : ({index, other} : Finset (Fin 3)) ⊆
        (Finset.univ : Finset (Fin 3)).filter fun i ↦ sheet ∈ classes i := by
      intro i hi
      rcases Finset.mem_insert.mp hi with hEq | hEq
      · subst hEq
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hIndex⟩
      · rw [Finset.mem_singleton] at hEq
        subst hEq
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hOther⟩
    have hPair : ({index, other} : Finset (Fin 3)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa using fun h ↦ hNe h.symm),
        Finset.card_singleton]
    calc 2 = ({index, other} : Finset (Fin 3)).card := hPair.symm
      _ ≤ multiplicity classes sheet := Finset.card_le_card hSubset
  have hSumEq : ∑ _sheet ∈ whole, 2 = ∑ sheet ∈ whole, multiplicity classes sheet := by
    rw [← sum_card_eq_sum_multiplicity whole classes hSub, hSum, Finset.sum_const,
      smul_eq_mul]
    omega
  intro sheet hSheet
  exact ((Finset.sum_eq_sum_iff_of_le hTwo).mp hSumEq sheet hSheet).symm

end FixedDatum

/-! ## The sheet is a branch-swap gauge

DV's **tree-swap** applies one permutation of `[d]` to every relation at once
and would indeed leave `e_α ⊆ e_β ∪ e_γ` intact.  The **branch-swap** does
not: it applies the permutation above one connected component of `T ∖ {w₀}`
only, and the gluing-datum isomorphism (`definition-gd-iso`) allows one
permutation `πₓ` per target element.  At a trivalent `w₀` the three classes
therefore move independently inside `A₀`, and only their cardinalities -- the
data the case analysis actually uses -- are invariant.

This is the same reading as for Figure 28 (`W3FourSourceCandidates`,
`W3FourDisjointness`).  What the two situations have in common is that the
invisible datum is an intersection of blocks of *different* edge partitions
whose only common target vertex is `w₀`.
-/

/-- One legal branch-swap transposition inside a wall block: if a subset of the
block is not the whole block, transposing a chosen sheet with a sheet outside
the subset carries the subset off the chosen sheet.  The caller supplies the
chosen sheet's own membership in the block, which is what makes both
transposed sheets lie in one block of `∼_{w₀}` and the transposition a legal DV
branch-swap. -/
theorem exists_swap_avoiding (whole small : Finset (Fin degree))
    (hSmall : small ⊆ whole) (hCard : small.card < whole.card)
    (chosen : Fin degree) :
    ∃ free : Fin degree, free ∈ whole ∧
      chosen ∉ small.image (Equiv.swap chosen free) := by
  classical
  have hStrict : small ⊂ whole :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hSmall, fun hEq ↦ by
      rw [hEq] at hCard
      exact lt_irrefl _ hCard⟩
  obtain ⟨free, hFreeWhole, hFreeNot⟩ := Finset.exists_of_ssubset hStrict
  refine ⟨free, hFreeWhole, fun hMem ↦ ?_⟩
  obtain ⟨preimage, hPre, hEq⟩ := Finset.mem_image.mp hMem
  have hFree : preimage = free := (Equiv.swap chosen free).injective
    (hEq.trans (Equiv.swap_apply_right chosen free).symm)
  exact hFreeNot (hFree ▸ hPre)

/-- **One branch-swap clears a chosen sheet out of one class.**  Relabel the
branch through `movedTarget` by a transposition inside the wall block.  The
wall partition, `targetExcess wall`, validity and every class on another branch
are untouched; the moved class keeps its index and no longer contains the
chosen sheet.  The only arithmetic used is that the moved class is smaller than
the wall block, which case `{w3-r1-nd3-t2-(a>k₄)}` gives for all three
directions (`|A₀| > k₄ ≥ k_i`). -/
theorem exists_branchSwap_clearing (data : GluingDatum target degree)
    (wall root : target.V) (hRoot : root ≠ wall) (movedTarget : target.edges)
    (anchor movedAnchor chosen : Fin degree)
    (hChosen : (data.vertexPartition wall).Rel anchor chosen)
    (hMovedRel : (data.vertexPartition wall).Rel anchor movedAnchor)
    (hRefines : (data.edgePartition movedTarget).Refines (data.vertexPartition wall))
    (hLt : (data.edgePartition movedTarget).blockCard movedAnchor <
      (data.vertexPartition wall).blockCard anchor)
    (hMoved : TargetBranchRegion.edgeMoved wall root hRoot movedTarget = true) :
    ∃ (swapped : GluingDatum target degree) (newAnchor : Fin degree),
      swapped.vertexPartition wall = data.vertexPartition wall ∧
      (∀ edge, TargetBranchRegion.edgeMoved wall root hRoot edge = false →
        swapped.edgePartition edge = data.edgePartition edge) ∧
      swapped.targetExcess wall = data.targetExcess wall ∧
      (data.Valid → swapped.Valid) ∧
      (data.vertexPartition wall).Rel anchor newAnchor ∧
      (swapped.edgePartition movedTarget).blockCard newAnchor =
        (data.edgePartition movedTarget).blockCard movedAnchor ∧
      ¬(swapped.edgePartition movedTarget).Rel newAnchor chosen := by
  classical
  obtain ⟨free, hFreeMem, hAvoid⟩ := exists_swap_avoiding
    ((data.vertexPartition wall).block anchor)
    ((data.edgePartition movedTarget).block movedAnchor)
    (W3FourDisjointness.block_subset_wallBlock data wall movedTarget anchor movedAnchor
      hRefines hMovedRel) hLt chosen
  have hFreeRel : (data.vertexPartition wall).Rel anchor free :=
    ((data.vertexPartition wall).mem_block_iff anchor free).mp hFreeMem
  have hFix := (data.vertexPartition wall).swap_apply_rel_self_of_rel
    (hChosen.symm.trans hFreeRel)
  have hGauge := W3FourDisjointness.branchSwapOfPerm_branchGauge data wall root hRoot
    (Equiv.swap chosen free) hFix
  have hMovedEdge :
      (W3FourDisjointness.branchSwapOfPerm data wall root hRoot
            (Equiv.swap chosen free) hFix).apply.edgePartition movedTarget =
        (data.edgePartition movedTarget).relabel (Equiv.swap chosen free) :=
    W3FourDisjointness.branchSwapOfPerm_edgePartition_of_moved data wall root hRoot _
      hFix movedTarget hMoved
  refine ⟨(W3FourDisjointness.branchSwapOfPerm data wall root hRoot
      (Equiv.swap chosen free) hFix).apply,
    (Equiv.swap chosen free) movedAnchor, hGauge.wallPartition, hGauge.fixedEdges,
    hGauge.targetExcess, hGauge.valid, hMovedRel.trans (hFix movedAnchor).symm, ?_, ?_⟩
  · rw [hMovedEdge]
    exact (data.edgePartition movedTarget).relabel_blockCard (Equiv.swap chosen free)
      movedAnchor
  · rw [hMovedEdge]
    intro hRel
    have hMem : chosen ∈
        ((data.edgePartition movedTarget).relabel (Equiv.swap chosen free)).block
          ((Equiv.swap chosen free) movedAnchor) :=
      (((data.edgePartition movedTarget).relabel
        (Equiv.swap chosen free)).mem_block_iff _ _).mpr hRel
    rw [(data.edgePartition movedTarget).relabel_block (Equiv.swap chosen free)
      movedAnchor] at hMem
    exact hAvoid hMem

/-- **Position II.b's sheet is available on any prescribed direction, on a
branch-swapped copy of the same wall datum.**

Two DV branch-swaps -- one on the branch through `t_β`, one on the branch
through `t_γ` -- move those two classes off the moving direction's own anchor
sheet.  Neither swap touches `A₀`, `e_α`, `targetExcess wall`, validity, or the
other swapped branch, and each moved class keeps its index.  In the resulting
datum the moving anchor is a sheet of `e_α` lying in neither `e_β` nor `e_γ`:
exactly `W3ShiftSourceCandidates.HasShrinkSheet`, hence exactly what
`exists_shrinkData` needs to build Figure 29's `k - 1` member on the prescribed
direction.

The only arithmetic consumed is `k_β, k_γ < |A₀|`, which is the case
hypothesis `|A₀| > k₄` of `{w3-r1-nd3-t2-(a>k₄)}`.  The branch flags
are the same species as in `W3FourDisjointness`: on a target tree they hold
with `firstRoot`, `secondRoot` the far endpoints of `t_β`, `t_γ`, because the
components of `T ∖ {w₀}` through `t_α`, `t_β`, `t_γ` are then distinct.
`exists_shrinkSheet_of_genus_zero` below discharges all six of them.

**Consequence.**  The configuration without a Position II.b sheet is a
sheet-labelling gauge, of the same kind as for Figure 28, and Part I's
justification in case `{w3-r1-nd3-t2-(a>k₄)}` applies once its members are
read on isomorphism classes, as Part I's definition of `ℙ𝒞*(M₀)` as a set of
isomorphism classes provides.  The formalization cost is the same as for
Figure 28: Equation (3)'s `(k-1, k+1)` pair does not live over one
`GluingDatum` **value**, so the exit is assembled as a gauge family. -/
theorem exists_branchGauge_shrinkSheet (data : GluingDatum target degree)
    (wall firstRoot secondRoot : target.V)
    (hFirstRoot : firstRoot ≠ wall) (hSecondRoot : secondRoot ≠ wall)
    (movingTarget firstTarget secondTarget : target.edges)
    (anchor movingAnchor firstAnchor secondAnchor : Fin degree)
    (hMovingRel : (data.vertexPartition wall).Rel anchor movingAnchor)
    (hFirstRel : (data.vertexPartition wall).Rel anchor firstAnchor)
    (hSecondRel : (data.vertexPartition wall).Rel anchor secondAnchor)
    (hFirstRefines :
      (data.edgePartition firstTarget).Refines (data.vertexPartition wall))
    (hSecondRefines :
      (data.edgePartition secondTarget).Refines (data.vertexPartition wall))
    (hFirstLt : (data.edgePartition firstTarget).blockCard firstAnchor <
      (data.vertexPartition wall).blockCard anchor)
    (hSecondLt : (data.edgePartition secondTarget).blockCard secondAnchor <
      (data.vertexPartition wall).blockCard anchor)
    (hMovingFixedFirst :
      TargetBranchRegion.edgeMoved wall firstRoot hFirstRoot movingTarget = false)
    (hSecondFixedFirst :
      TargetBranchRegion.edgeMoved wall firstRoot hFirstRoot secondTarget = false)
    (hFirstMovedFirst :
      TargetBranchRegion.edgeMoved wall firstRoot hFirstRoot firstTarget = true)
    (hMovingFixedSecond :
      TargetBranchRegion.edgeMoved wall secondRoot hSecondRoot movingTarget = false)
    (hFirstFixedSecond :
      TargetBranchRegion.edgeMoved wall secondRoot hSecondRoot firstTarget = false)
    (hSecondMovedSecond :
      TargetBranchRegion.edgeMoved wall secondRoot hSecondRoot secondTarget = true) :
    ∃ (swapped : GluingDatum target degree)
      (newFirstAnchor newSecondAnchor : Fin degree),
      swapped.vertexPartition wall = data.vertexPartition wall ∧
      swapped.edgePartition movingTarget = data.edgePartition movingTarget ∧
      swapped.targetExcess wall = data.targetExcess wall ∧
      (data.Valid → swapped.Valid) ∧
      (data.vertexPartition wall).Rel anchor newFirstAnchor ∧
      (data.vertexPartition wall).Rel anchor newSecondAnchor ∧
      (swapped.edgePartition firstTarget).blockCard newFirstAnchor =
        (data.edgePartition firstTarget).blockCard firstAnchor ∧
      (swapped.edgePartition secondTarget).blockCard newSecondAnchor =
        (data.edgePartition secondTarget).blockCard secondAnchor ∧
      (swapped.edgePartition movingTarget).Rel movingAnchor movingAnchor ∧
      ¬(swapped.edgePartition firstTarget).Rel newFirstAnchor movingAnchor ∧
      ¬(swapped.edgePartition secondTarget).Rel newSecondAnchor movingAnchor := by
  classical
  obtain ⟨first, newFirstAnchor, hWallFirst, hFixedFirst, hExcessFirst, hValidFirst,
    hRelFirst, hCardFirst, hClearFirst⟩ :=
    exists_branchSwap_clearing data wall firstRoot hFirstRoot firstTarget anchor
      firstAnchor movingAnchor hMovingRel hFirstRel hFirstRefines hFirstLt
      hFirstMovedFirst
  have hMovingEdgeFirst : first.edgePartition movingTarget =
      data.edgePartition movingTarget := hFixedFirst movingTarget hMovingFixedFirst
  have hSecondEdgeFirst : first.edgePartition secondTarget =
      data.edgePartition secondTarget := hFixedFirst secondTarget hSecondFixedFirst
  obtain ⟨second, newSecondAnchor, hWallSecond, hFixedSecond, hExcessSecond,
    hValidSecond, hRelSecond, hCardSecond, hClearSecond⟩ :=
    exists_branchSwap_clearing first wall secondRoot hSecondRoot secondTarget anchor
      secondAnchor movingAnchor (by rw [hWallFirst]; exact hMovingRel)
      (by rw [hWallFirst]; exact hSecondRel)
      (by rw [hWallFirst, hSecondEdgeFirst]; exact hSecondRefines)
      (by rw [hWallFirst, hSecondEdgeFirst]; exact hSecondLt) hSecondMovedSecond
  have hFirstEdgeSecond : second.edgePartition firstTarget =
      first.edgePartition firstTarget := hFixedSecond firstTarget hFirstFixedSecond
  refine ⟨second, newFirstAnchor, newSecondAnchor, hWallSecond.trans hWallFirst,
    (hFixedSecond movingTarget hMovingFixedSecond).trans hMovingEdgeFirst,
    hExcessSecond.trans hExcessFirst, fun hValid ↦ hValidSecond (hValidFirst hValid),
    hRelFirst, by rw [← hWallFirst]; exact hRelSecond, ?_, ?_, rfl, ?_, hClearSecond⟩
  · rw [hFirstEdgeSecond]
    exact hCardFirst
  · rw [hCardSecond, hSecondEdgeFirst]
  · rw [hFirstEdgeSecond]
    exact hClearFirst

/-- **The branch flags discharged on an actual Part I target.**  Every target
of Part I is a connected tree, so `graph_connected target` and
`genus target = 0` hold, and `Infrastructure.TargetSeparation` turns the six
branch flags of
`exists_branchGauge_shrinkSheet` into theorems: take the two swap roots to be
the far endpoints of `t_β` and `t_γ`, and each occurrence at `w₀` selects a
branch that moves itself and fixes the other two.

So on an actual `{w3-r1-nd3-t2-(a>k₄)}` wall nothing at all is carried beyond
the case's own data: Position II.b's sheet is available on whichever direction
Equation (3)'s pair is wanted for. -/
theorem exists_shrinkSheet_of_genus_zero (data : GluingDatum target degree)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (wall : target.V) (movingTarget firstTarget secondTarget : target.edges)
    (hMovingAt : (movingTarget : target.V × target.V).1 = wall ∨
      (movingTarget : target.V × target.V).2 = wall)
    (hFirstAt : (firstTarget : target.V × target.V).1 = wall ∨
      (firstTarget : target.V × target.V).2 = wall)
    (hSecondAt : (secondTarget : target.V × target.V).1 = wall ∨
      (secondTarget : target.V × target.V).2 = wall)
    (hFirstNeMoving : firstTarget ≠ movingTarget)
    (hFirstNeSecond : firstTarget ≠ secondTarget)
    (hSecondNeMoving : secondTarget ≠ movingTarget)
    (anchor movingAnchor firstAnchor secondAnchor : Fin degree)
    (hMovingRel : (data.vertexPartition wall).Rel anchor movingAnchor)
    (hFirstRel : (data.vertexPartition wall).Rel anchor firstAnchor)
    (hSecondRel : (data.vertexPartition wall).Rel anchor secondAnchor)
    (hFirstRefines :
      (data.edgePartition firstTarget).Refines (data.vertexPartition wall))
    (hSecondRefines :
      (data.edgePartition secondTarget).Refines (data.vertexPartition wall))
    (hFirstLt : (data.edgePartition firstTarget).blockCard firstAnchor <
      (data.vertexPartition wall).blockCard anchor)
    (hSecondLt : (data.edgePartition secondTarget).blockCard secondAnchor <
      (data.vertexPartition wall).blockCard anchor) :
    ∃ (swapped : GluingDatum target degree)
      (newFirstAnchor newSecondAnchor : Fin degree),
      swapped.vertexPartition wall = data.vertexPartition wall ∧
      swapped.edgePartition movingTarget = data.edgePartition movingTarget ∧
      swapped.targetExcess wall = data.targetExcess wall ∧
      (data.Valid → swapped.Valid) ∧
      (data.vertexPartition wall).Rel anchor newFirstAnchor ∧
      (data.vertexPartition wall).Rel anchor newSecondAnchor ∧
      (swapped.edgePartition firstTarget).blockCard newFirstAnchor =
        (data.edgePartition firstTarget).blockCard firstAnchor ∧
      (swapped.edgePartition secondTarget).blockCard newSecondAnchor =
        (data.edgePartition secondTarget).blockCard secondAnchor ∧
      (swapped.edgePartition movingTarget).Rel movingAnchor movingAnchor ∧
      ¬(swapped.edgePartition firstTarget).Rel newFirstAnchor movingAnchor ∧
      ¬(swapped.edgePartition secondTarget).Rel newSecondAnchor movingAnchor :=
  exists_branchGauge_shrinkSheet data wall
    (TargetSeparation.farEndpoint wall firstTarget)
    (TargetSeparation.farEndpoint wall secondTarget)
    (TargetSeparation.farEndpoint_ne hFirstAt)
    (TargetSeparation.farEndpoint_ne hSecondAt)
    movingTarget firstTarget secondTarget anchor movingAnchor firstAnchor
    secondAnchor hMovingRel hFirstRel hSecondRel hFirstRefines hSecondRefines
    hFirstLt hSecondLt
    (TargetSeparation.edgeMoved_eq_false hConnected hGenus hFirstAt hMovingAt
      hFirstNeMoving)
    (TargetSeparation.edgeMoved_eq_false hConnected hGenus hFirstAt hSecondAt
      hFirstNeSecond)
    (TargetSeparation.edgeMoved_self_eq_true hFirstAt)
    (TargetSeparation.edgeMoved_eq_false hConnected hGenus hSecondAt hMovingAt
      hSecondNeMoving)
    (TargetSeparation.edgeMoved_eq_false hConnected hGenus hSecondAt hFirstAt
      (Ne.symm hFirstNeSecond))
    (TargetSeparation.edgeMoved_self_eq_true hSecondAt)

/-- **The smallest theta configuration, and the single branch-swap that
dissolves it.**  The
three classes `{0,1}`, `{1,2}`, `{0,2}` in a wall block of three sheets meet
every numerical constraint of case `{w3-r1-nd3-t2-(a>k₄)}` -- the index sum is
`2|A₀|`, each index is at least two and strictly below `|A₀|` -- and no
direction has a Position II.b sheet: this is exactly
`no_private_sheet_forces_double_cover`'s doubly covered configuration.

Relabelling the **first** class alone by the transposition `(0 2)` -- one DV
branch-swap above the branch through `t₂`, which leaves `A₀` and the other two
classes literally unchanged -- keeps its cardinality and makes sheet `0`
private to the third class. -/
theorem theta_configuration_moved_by_one_branchSwap :
    ∃ classes : Fin 3 → Finset (Fin 3),
      (∑ index, (classes index).card) = 2 * (Finset.univ : Finset (Fin 3)).card ∧
      (∀ index, 2 ≤ (classes index).card) ∧
      (∀ index, (classes index).card < (Finset.univ : Finset (Fin 3)).card) ∧
      (∀ index sheet, sheet ∈ classes index →
        ∃ other, other ≠ index ∧ sheet ∈ classes other) ∧
      ((classes 0).image (Equiv.swap (0 : Fin 3) 2)).card = (classes 0).card ∧
      ∃ sheet, sheet ∈ classes 2 ∧
        sheet ∉ (classes 0).image (Equiv.swap (0 : Fin 3) 2) ∧
        sheet ∉ classes 1 := by
  refine ⟨![{0, 1}, {1, 2}, {0, 2}], ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end DraismaVargas.LocalCases.W3ShiftShrinkExistence
