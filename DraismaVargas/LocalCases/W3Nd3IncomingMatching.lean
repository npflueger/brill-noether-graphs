import DraismaVargas.LocalCases.W3Nd3IncomingCensus
import DraismaVargas.LocalCases.W3Nd3LimitMatrix
import DraismaVargas.LocalCases.W3Nd2IncomingMemberMatching

/-!
# Normalizing an incoming W3 nd3 datum and matching it to a named Figure 30 member

Source: Draisma–Vargas Part I, arXiv:1909.12924, case `{w3-r1-nd3-t3}`, Figure 30 and
Equation (4).  The prose of the case attaches the two members to `α = 3` and
`α = 4` the other way round from Figure 30; this file follows the figure,
exactly as `W3Nd3SourceCandidates` and `W3Nd3IncomingCensus` do.

This is the nd3 analogue of `W3Nd2IncomingNormalization` together with
`W3Nd2IncomingMemberMatching`, for an **arbitrary** incoming W3 nd3 datum: the
hypothesis bundle is the nd2 incoming bundle with `Nd2Profile` replaced by
`Nd3Profile` plus the doubled direction `hSame`, exactly as
`W3Nd3IncomingCensus` takes them.  No hypothesis is added.

## What is *not* rebuilt here

* **The `r = 0` background census is profile-free.**  `W3Nd2IncomingBackground`
  and `W3Nd2IncomingNormalization.background_whole_block_census` never mention a
  profile: a background block is characterised only by being distinct from the
  distinguished block, and the divalent dichotomy comes from full-dimensionality
  and the contraction forest.  `background_whole_block_census` below is that
  application in the nd3 context, recorded so that the applicability is
  machine-checked rather than asserted; it is *not* a second proof.  The same
  holds for the four literal block forms
  `W3Nd2IncomingMemberMatching.background_edge_block_eq_of_left_divalent` and
  companions, which are consumed verbatim.
* **The stored-representative normalization is profile-free.**
  `W3Nd2IncomingNormalization.exists_normalized_presentation` is stated for an
  arbitrary target isomorphism and comparison datum, so
  `W3Nd2IncomingMemberMatching.NormalizedAgainst` is reused as the receipt.
* **The candidate/vertex exhaustion is profile-free.**
  `W3Nd2IncomingMemberMatching.sameBlocks_of_wall_blocks` reduces a whole-cover
  `SameBlocks` family to three wall comparisons for *any* assembled candidate
  over the contracted wall, and
  `W3Nd2IncomingMemberMatching.transported_endpoints_of_left_divalent` and its
  mirror decide the normalization swap from the side census alone.

## The three nd3/nd2 divergences, and where each bites here

1. **There is no residual sheet.**  `k₂ + k₃ = |A₀|`, so the doubled direction
   cuts `A₀` into *exactly two* blocks that already exhaust it
   (`W3Nd3StableGraph.fine_blocks_cover_wall`).  In nd2 the fine class missed
   exactly one sheet and the comparison was
   `W3Nd2IncomingMemberMatching.block_eq_of_block_eq_of_card_succ_local`, a
   "block plus one singleton" argument.  Here the replacement is
   `block_eq_of_cover_pair_local`: a partition agreeing with the doubled
   direction at *two* sheets whose fine blocks cover the wall class agrees with
   it on the whole class.  Both the trivalent endpoint and the contracted
   occurrence of `M⁽²⁾` are pinned this way, from the *two* surviving internal
   occurrences rather than one survivor and one dangler.
2. **The divalent endpoint is a branch vertex in both members.**  This is
   already absorbed by `W3Nd3IncomingCensus`: its `selected_sheet_classes_of_*`
   deliver the census without
   `PrunedDivalentFibre.internalEdges_card_le_one` or
   `PrunedFibreTree.nonDanglingValency_eq_two_of_mem_activeFibre`.  Downstream
   of that census the divergence is invisible: what this file consumes is the
   branch vertex's literal sheet class, which is `A₀` in both members.
3. **`old_wall_branch_background` is false here.**  Nothing in this file uses
   it: the background half is entirely the profile-free
   `W3Nd2IncomingNormalization` census plus `W3Nd3LimitMatrix`'s background
   block dictionary, neither of which mentions a branch background.

## What is proved

* `block_eq_of_cover_pair_local` -- the two-block covering comparison.
* `background_whole_block_census` -- the profile-free `r = 0` whole-block
  census, applied in the nd3 context.
* `largest_flag_block_eq_local` -- `k₄ = |A₀|` read as an equality of literal
  sheet sets: the largest survivor's retained flag class is the entire
  distinguished wall class.  This is the nd3 counterpart of
  `W3Nd2IncomingMemberMatching.large_flag_block_eq_local`, and it is what makes
  `M⁽¹⁾` the whole-wall member.
* `selected_endpoint_joined` -- on the distinguished block at least one of the
  two original endpoint partitions is `JoinedOnBlock`; which one is the
  `M⁽¹⁾`/`M⁽²⁾` dichotomy and is left as a disjunction, complementing the
  background census exactly as in nd2.
* `shared_selected_endpoints_joined`, `shared_selected_contracted_joined`,
  `largest_selected_blocks` -- the selected block in each orientation, as
  literal block identities.
* `coarse_placement_of_eq_shared`, `fine_placement_of_eq_largest`,
  `coarseTargetIso`, `fineTargetIso` and their occurrence dictionaries.
* `coarse_wall_blocks`, `fine_wall_blocks` -- the three wall comparisons.
* `coarse_sameBlocks`, `fine_sameBlocks` and their split forms -- the pointwise
  `SameBlocks` families against the named Figure 30 member.
* `exists_member_normalization` -- the exit: an arbitrary incoming W3 nd3 datum
  *is* one of the two named Figure 30 members, with the literal Option column
  dictionary and the normalization receipt `NormalizedAgainst`, whose recorded
  clauses (original target-edge labelling, unchanged length matrix,
  occurrence-for-occurrence source map, preserved stable-row matrix entries)
  forbid a hidden incoming classification or count-based row bijection.

## What is *not* proved

The original-coordinate arbitrary-incoming exit, combining this identification
with `W3Nd3CommonBalance`'s identified-member exit, is **not** proved here; see
`W3Nd3ArbitraryExit` and `W3Nd3GraphTracking`.

Every identity below is an identity of literal **occurrence** sets or of sheet
blocks; no row label is identified anywhere, and no stable-row bijection is
chosen from a cardinality.
-/

namespace DraismaVargas.LocalCases.W3Nd3IncomingMatching

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4Assembly W4StableSource StableLocalProperties NonDanglingValency
open ThirdEquation W3R1SourceProfile FullDimensionalSource WallDegeneration
open TargetExpansion
open M11IncomingPartitions
open PrunedFibreValency PrunedFibreTree
open W4IncomingRetainedFlags (endpoint)
open W3Nd2SourceCandidates (rightOf)
open W3Nd2IncomingTargetPlacement (divalentOccurrence divalentOccurrence_spec
  divalentOccurrence_placement endpoint_valencies)
open W3Nd2IncomingDirection (Placement)
open W3Nd2IncomingSelectedCensus (selectedVertex selectedBlock)

/-! ## A generic two-block covering comparison

This is what replaces nd2's residual-sheet comparison.  In nd2 the fine class
on `A₀` missed exactly one sheet, and
`W3Nd2IncomingMemberMatching.block_eq_of_block_eq_of_card_succ_local` compared
two refinements through that singleton.  Here `k₂ + k₃ = |A₀|`, so the doubled
direction cuts `A₀` into two blocks that already exhaust it, and the comparison
runs through the covering pair instead. -/

section Partitions

variable {d : ℕ}

/-- **Two-block covering comparison.**  If every sheet of a coarse block is
`fine`-related to one of two chosen sheets, and a third partition has the same
`fine` block at each of those two, then it has the same `fine` block at every
sheet of the coarse block.  No cardinality and no refinement of `partition` is
used. -/
theorem block_eq_of_cover_pair_local (coarse fine partition : SheetPartition d)
    (root first second : Fin d)
    (hCover : ∀ sheet, coarse.Rel root sheet →
      fine.Rel first sheet ∨ fine.Rel second sheet)
    (hFirst : partition.block first = fine.block first)
    (hSecond : partition.block second = fine.block second)
    (sheet : Fin d) (hSheet : coarse.Rel root sheet) :
    partition.block sheet = fine.block sheet := by
  classical
  have hStep : ∀ anchor : Fin d, partition.block anchor = fine.block anchor →
      fine.Rel anchor sheet → partition.block sheet = fine.block sheet := by
    intro anchor hAnchor hRel
    have hMem : sheet ∈ partition.block anchor := by
      rw [hAnchor]
      exact (fine.mem_block_iff anchor sheet).mpr hRel
    have hRelP : partition.Rel anchor sheet :=
      (partition.mem_block_iff anchor sheet).mp hMem
    rw [← partition.block_eq_of_rel hRelP, ← fine.block_eq_of_rel hRel]
    exact hAnchor
  rcases hCover sheet hSheet with hRel | hRel
  · exact hStep first hFirst hRel
  · exact hStep second hSecond hRel

end Partitions


/-! ## The largest survivor's flag class is the whole distinguished class

`Nd3Profile.doubled_direction` records `k₄ = |A₀|` alongside `k₂ + k₃ = |A₀|`.
Read as sets, the first of these says the largest survivor's retained wall flag
fills its entire wall class -- the nd3 counterpart of
`W3Nd2IncomingMemberMatching.large_flag_block_eq_local`. -/

section FlagClass

variable {wallTarget : CFGraph} {wallDegree : ℕ} {wall : wallTarget.V}
  {wallData : GluingDatum wallTarget wallDegree} {star : ThreeStar wallTarget wall}

/-- **The largest flag class is the entire distinguished wall class.**  Its
index is `k₄ = |A₀|`, and it is contained in `A₀` by refinement, so the two
finite sets coincide. -/
theorem largest_flag_block_eq_local (input : W3SourceInput wallData star)
    (profile : Nd3Profile wallData input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (wallData.edgePartition profile.largest.1.1.1).block profile.largest.1.1.2 =
      (wallData.vertexPartition wall).block input.distinguishedBlock.1 := by
  classical
  have hRel := W3Nd3SourceCandidates.incident_wall_rel input profile.largest
  have hRefines : (wallData.edgePartition profile.largest.1.1.1).Refines
      (wallData.vertexPartition wall) :=
    refines_of_mem_incidentEdges wallData
      (W3Nd3SourceCandidates.largestTarget_mem input profile)
  have hSub : (wallData.edgePartition profile.largest.1.1.1).block
      profile.largest.1.1.2 ⊆
        (wallData.vertexPartition wall).block input.distinguishedBlock.1 := by
    intro sheet hSheet
    exact ((wallData.vertexPartition wall).mem_block_iff _ sheet).mpr
      (hRel.trans (hRefines.rel
        (((wallData.edgePartition profile.largest.1.1.1).mem_block_iff _ sheet).mp hSheet)))
  have hCard : ((wallData.vertexPartition wall).block input.distinguishedBlock.1).card ≤
      ((wallData.edgePartition profile.largest.1.1.1).block
        profile.largest.1.1.2).card := by
    have hIndex : (wallData.edgePartition profile.largest.1.1.1).blockCard
        profile.largest.1.1.2 =
          (wallData.vertexPartition wall).blockCard input.distinguishedBlock.1 :=
      (profile.doubled_direction hSame).2
    unfold SheetPartition.blockCard at hIndex
    omega
  exact Finset.eq_of_subset_of_card_le hSub hCard

end FlagClass


/-! ## The `r = 0` background, consumed -/

section Background

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  {star : ThreeStar (contract target hab hOne) ⟨a, hab⟩}
  (input : W3SourceInput (contractDatum data hc hab hOne) star)

include fullDim hForest input

/-- **The `r = 0` whole-block census at a `(2,3)` incoming W3 wall, in the nd3
context.**  `W3Nd2IncomingNormalization.background_whole_block_census` is
profile-free -- a background block is characterised only by
`background ≠ input.distinguishedBlock`, its vanishing wall ramification comes
from `ThirdEquation.W3SourceInput.localRamification_eq_zero_of_ne`, and the
divalent dichotomy comes from full-dimensionality and the contraction forest --
so it applies verbatim to an incoming **nd3** datum.  This theorem is that
application, recorded here so that the applicability is machine-checked rather
than asserted, and so that the nd3 matching below has an nd3-named entry point.
It is *not* a second proof, and no nd3-specific background statement is needed
or claimed. -/
theorem background_whole_block_census
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hBackground : background ≠ input.distinguishedBlock) :
    ((GluingDatum.incidentEdges a).card = 2 ∧ (GluingDatum.incidentEdges b).card = 3 ∧
        (∀ edge ∈ GluingDatum.incidentEdges a, ∀ first second : Fin degree,
            (mergedPartition data a b).Rel background.1 first →
            ((data.edgePartition edge).Rel first second ↔
              (data.vertexPartition a).Rel first second)) ∧
        JoinedOnBlock (data.vertexPartition b) (mergedPartition data a b) background.1 ∧
        (data.vertexPartition b).blockCountWithin
          (mergedPartition data a b) background.1 = 1) ∨
      ((GluingDatum.incidentEdges a).card = 3 ∧ (GluingDatum.incidentEdges b).card = 2 ∧
        (∀ edge ∈ GluingDatum.incidentEdges b, ∀ first second : Fin degree,
            (mergedPartition data a b).Rel background.1 first →
            ((data.edgePartition edge).Rel first second ↔
              (data.vertexPartition b).Rel first second)) ∧
        JoinedOnBlock (data.vertexPartition a) (mergedPartition data a b) background.1 ∧
        (data.vertexPartition a).blockCountWithin
          (mergedPartition data a b) background.1 = 1) :=
  W3Nd2IncomingNormalization.background_whole_block_census data hc hab hOne fullDim
    hForest input hBackground

end Background


/-! ## Merged-versus-wall bookkeeping -/

section Merged

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

theorem merged_eq_wall :
    mergedPartition data a b =
      (contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩ :=
  (contractDatum_vertexPartition_merge data hc hab hOne).symm

theorem merged_block_eq_wall_block (sheet : Fin degree) :
    (mergedPartition data a b).block sheet =
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block sheet :=
  congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
    (merged_eq_wall data hc hab hOne)

theorem merged_rel_eq_wall_rel (root sheet : Fin degree) :
    ((mergedPartition data a b).Rel root sheet) =
      (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel root sheet) :=
  congrArg (fun partition : SheetPartition degree ↦ partition.Rel root sheet)
    (merged_eq_wall data hc hab hOne)

end Merged


/-! ## Which original endpoint each canonical endpoint restores -/

section Endpoints

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

/-- Every canonical endpoint sits over one of the two original endpoints. -/
theorem endpoint_target_left_or_right
    (edge : (contractDatum data hc hab hOne).SourceEdge) :
    (endpoint data hc hab hOne edge).1.1 = a ∨
      (endpoint data hc hab hOne edge).1.1 = b := by
  cases hValue : IncomingTargetExpansion.right hc hab hOne edge.1.1
  · exact Or.inl
      (W3Nd2IncomingSheetClasses.endpoint_target_of_false data hc hab hOne edge hValue)
  · exact Or.inr
      (W3Nd2IncomingSheetClasses.endpoint_target_of_true data hc hab hOne edge hValue)

end Endpoints


/-! ## The selected block, complementing the background census -/

section Selected

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (hCompat : DanglingCompatible data hc hab hOne)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (profile : Nd3Profile (contractDatum data hc hab hOne) input.distinguishedBlock)

include fullDim hForest hCompat

/-- **The selected block mirrors a background block.**  In both Figure 30
members the branch vertex of the selected fibre carries the entire merged wall
class `A₀`, so one of the two original endpoint partitions is `JoinedOnBlock`
on the *distinguished* block.  Together with `background_whole_block_census`
this gives the whole-block picture at a `(2,3)` incoming nd3 wall: on every
wall block at least one endpoint partition is joined, and on a background block
it is the trivalent one.  Which endpoint carries the branch vertex here is the
`M⁽¹⁾`/`M⁽²⁾` dichotomy, so it is reported as a disjunction rather than
fixed. -/
theorem selected_endpoint_joined
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    JoinedOnBlock (data.vertexPartition a) (mergedPartition data a b)
        (selectedBlock data hc hab hOne star input).1 ∨
      JoinedOnBlock (data.vertexPartition b) (mergedPartition data a b)
        (selectedBlock data hc hab hOne star input).1 := by
  classical
  have hBranch : ∃ branch : (contractDatum data hc hab hOne).SourceEdge,
      (data.vertexPartition (endpoint data hc hab hOne branch).1.1).block
          (endpoint data hc hab hOne branch).1.2 =
        (mergedPartition data a b).block
          (selectedBlock data hc hab hOne star input).1 := by
    rcases W3Nd3IncomingCensus.selected_sheet_classes data hc hab hOne fullDim hForest
        hCompat star input profile hSame with
      ⟨_, _, _, _, _, _, _, _, hBranchClass, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hBranchClass, _, _, _⟩
    · exact ⟨profile.first.1, hBranchClass⟩
    · exact ⟨profile.largest.1, hBranchClass⟩
  obtain ⟨branch, hBranchClass⟩ := hBranch
  rcases endpoint_target_left_or_right data hc hab hOne branch with hEq | hEq
  · refine Or.inl (W3Nd2IncomingNormalization.joinedOnBlock_of_block_eq_local _ _ _
      (endpoint data hc hab hOne branch).1.2 ?_)
    exact (congrArg (fun place : target.V ↦
      (data.vertexPartition place).block
        (endpoint data hc hab hOne branch).1.2) hEq).symm.trans hBranchClass
  · refine Or.inr (W3Nd2IncomingNormalization.joinedOnBlock_of_block_eq_local _ _ _
      (endpoint data hc hab hOne branch).1.2 ?_)
    exact (congrArg (fun place : target.V ↦
      (data.vertexPartition place).block
        (endpoint data hc hab hOne branch).1.2) hEq).symm.trans hBranchClass

end Selected


/-! ## The selected block of `M⁽¹⁾` (the doubled direction at the divalent end) -/

section SelectedShared

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (hCompat : DanglingCompatible data hc hab hOne)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (profile : Nd3Profile (contractDatum data hc hab hOne) input.distinguishedBlock)

include hForest hCompat

/-- **Both endpoint partitions are joined on the selected block, in the `M⁽¹⁾`
orientation.**  The branch vertex -- the common canonical endpoint of the two
smaller survivors, sitting above the divalent original endpoint -- carries the
whole merged class `A₀`; the unramified endpoint carries the *largest*
survivor's retained flag, whose class is also all of `A₀` because `k₄ = |A₀|`.
This is exactly `thirdResolution`'s selected picture, and it is why the coarse
Figure 30 member is the right one here. -/
theorem shared_selected_endpoints_joined
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (hShared : divalentOccurrence data hc hab hOne fullDim star = profile.first.1.1.1) :
    JoinedOnBlock (data.vertexPartition a) (mergedPartition data a b)
        (input.distinguishedBlock.1 : Fin degree) ∧
      JoinedOnBlock (data.vertexPartition b) (mergedPartition data a b)
        (input.distinguishedBlock.1 : Fin degree) := by
  classical
  obtain ⟨_, _, _, _, _, _, _, hFlag, hBranchClass, _, _⟩ :=
    W3Nd3IncomingCensus.selected_sheet_classes_of_shared data hc hab hOne fullDim hForest
      hCompat star input profile hSame hShared
  have hBranchJoined : JoinedOnBlock
      (data.vertexPartition
        (W3Nd3IncomingCensus.firstEndpoint data hc hab hOne star input profile).1.1)
      (mergedPartition data a b) (input.distinguishedBlock.1 : Fin degree) :=
    W3Nd2IncomingNormalization.joinedOnBlock_of_block_eq_local _ _ _ _ hBranchClass
  have hLargestClass : (data.vertexPartition
        (W3Nd3IncomingCensus.largestEndpoint data hc hab hOne star input profile).1.1).block
        (W3Nd3IncomingCensus.largestEndpoint data hc hab hOne star input profile).1.2 =
      (mergedPartition data a b).block (input.distinguishedBlock.1 : Fin degree) :=
    hFlag.trans ((largest_flag_block_eq_local input profile hSame).trans
      (merged_block_eq_wall_block data hc hab hOne
        (input.distinguishedBlock.1 : Fin degree)).symm)
  have hLargestJoined : JoinedOnBlock
      (data.vertexPartition
        (W3Nd3IncomingCensus.largestEndpoint data hc hab hOne star input profile).1.1)
      (mergedPartition data a b) (input.distinguishedBlock.1 : Fin degree) :=
    W3Nd2IncomingNormalization.joinedOnBlock_of_block_eq_local _ _ _ _ hLargestClass
  have hSideNe : IncomingTargetExpansion.right hc hab hOne profile.largest.1.1.1 ≠
      IncomingTargetExpansion.right hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star) :=
    W3Nd3IncomingCensus.side_ne_of_ne_divalentOccurrence data hc hab hOne fullDim star _
      (W3Nd3SourceCandidates.incident_target_mem input profile.largest)
      (by rw [hShared]; exact Ne.symm profile.first_target_ne)
  rw [hShared] at hSideNe
  cases hSide : IncomingTargetExpansion.right hc hab hOne profile.first.1.1.1 with
  | false =>
    have hLargestSide : IncomingTargetExpansion.right hc hab hOne
        profile.largest.1.1.1 = true := by
      cases hValue : IncomingTargetExpansion.right hc hab hOne profile.largest.1.1.1
      · exact absurd (hValue.trans hSide.symm) hSideNe
      · rfl
    have hBranchAt := W3Nd2IncomingSheetClasses.endpoint_target_of_false data hc hab hOne
      profile.first.1 hSide
    have hLargestAt := W3Nd2IncomingSheetClasses.endpoint_target_of_true data hc hab hOne
      profile.largest.1 hLargestSide
    rw [congrArg data.vertexPartition hBranchAt] at hBranchJoined
    rw [congrArg data.vertexPartition hLargestAt] at hLargestJoined
    exact ⟨hBranchJoined, hLargestJoined⟩
  | true =>
    have hLargestSide : IncomingTargetExpansion.right hc hab hOne
        profile.largest.1.1.1 = false := by
      cases hValue : IncomingTargetExpansion.right hc hab hOne profile.largest.1.1.1
      · rfl
      · exact absurd (hValue.trans hSide.symm) hSideNe
    have hBranchAt := W3Nd2IncomingSheetClasses.endpoint_target_of_true data hc hab hOne
      profile.first.1 hSide
    have hLargestAt := W3Nd2IncomingSheetClasses.endpoint_target_of_false data hc hab hOne
      profile.largest.1 hLargestSide
    rw [congrArg data.vertexPartition hBranchAt] at hBranchJoined
    rw [congrArg data.vertexPartition hLargestAt] at hLargestJoined
    exact ⟨hLargestJoined, hBranchJoined⟩

/-- Hence the contracted occurrence is joined there too: the forest identity
turns two unit endpoint counts into a unit occurrence count.  This is the only
place the contraction forest is used on the *selected* block. -/
theorem shared_selected_contracted_joined
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (hShared : divalentOccurrence data hc hab hOne fullDim star = profile.first.1.1.1) :
    JoinedOnBlock (data.edgePartition contracted) (mergedPartition data a b)
      (input.distinguishedBlock.1 : Fin degree) := by
  obtain ⟨hLeft, hRight⟩ := shared_selected_endpoints_joined data hc hab hOne fullDim
    hForest hCompat star input profile hSame hShared
  have hTree := contractionForest_count data hc hForest
    (selectedMergedBlock data hc hab hOne input.distinguishedBlock)
  have hCountLeft := blockCountWithin_eq_one_of_joinedOnBlock _ _ _ hLeft
  have hCountRight := blockCountWithin_eq_one_of_joinedOnBlock _ _ _ hRight
  have hTree' : ((data.edgePartition contracted).blockCountWithin
        (mergedPartition data a b) (input.distinguishedBlock.1 : Fin degree) : ℤ) + 1 =
      ((data.vertexPartition a).blockCountWithin
          (mergedPartition data a b) (input.distinguishedBlock.1 : Fin degree) : ℤ) +
        ((data.vertexPartition b).blockCountWithin
          (mergedPartition data a b) (input.distinguishedBlock.1 : Fin degree) : ℤ) := hTree
  rw [hCountLeft, hCountRight] at hTree'
  have hCount : (data.edgePartition contracted).blockCountWithin
      (mergedPartition data a b) (input.distinguishedBlock.1 : Fin degree) = 1 := by
    have : ((data.edgePartition contracted).blockCountWithin
        (mergedPartition data a b) (input.distinguishedBlock.1 : Fin degree) : ℤ) = 1 := by
      omega
    exact_mod_cast this
  exact joinedOnBlock_of_blockCountWithin_eq_one _ _ _
    (edgePartition_refines_mergedPartition data hc) hCount

end SelectedShared


/-! ## The selected block of `M⁽²⁾` (the largest direction at the divalent end) -/

section SelectedLargest

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (hCompat : DanglingCompatible data hc hab hOne)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (profile : Nd3Profile (contractDatum data hc hab hOne) input.distinguishedBlock)

include hForest hCompat

/-- **The selected block in the `M⁽²⁾` orientation.**  The branch vertex is now
the largest survivor's canonical endpoint, above the divalent original endpoint
`u`, and it carries the whole merged class `A₀`.  The unramified endpoint `v`
carries *both* smaller survivors' canonical endpoints, and the contracted
occurrence carries *both* internal occurrences -- there being no residual sheet,
`k₂ + k₃ = |A₀|` -- so each of them agrees with the doubled direction on all of
`A₀` by the two-block covering comparison.  That is literally the reversed
`fineResolution` of `W3Nd3SourceCandidates.selectedResolution`. -/
theorem largest_selected_blocks
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (hLargest : divalentOccurrence data hc hab hOne fullDim star = profile.largest.1.1.1)
    (u v : target.V)
    (hU : (W3Nd3IncomingCensus.largestEndpoint data hc hab hOne star input profile).1.1 = u)
    (hV : (W3Nd3IncomingCensus.firstEndpoint data hc hab hOne star input profile).1.1 = v)
    (hV' : (W3Nd3IncomingCensus.secondEndpoint data hc hab hOne star input profile).1.1 = v) :
    JoinedOnBlock (data.vertexPartition u) (mergedPartition data a b)
        (input.distinguishedBlock.1 : Fin degree) ∧
      (∀ sheet, (mergedPartition data a b).Rel
          (input.distinguishedBlock.1 : Fin degree) sheet →
        (data.vertexPartition v).block sheet =
          (W3Nd3SourceCandidates.finePartition input profile).block sheet) ∧
      (∀ sheet, (mergedPartition data a b).Rel
          (input.distinguishedBlock.1 : Fin degree) sheet →
        (data.edgePartition contracted).block sheet =
          (W3Nd3SourceCandidates.finePartition input profile).block sheet) := by
  classical
  obtain ⟨firstInternal, secondInternal, _, hInternal, _, _,
    _, _, _, _, hFirstClass, hSecondClass, hFirstFlag, hSecondFlag, hBranchClass,
    _, _, _⟩ :=
    W3Nd3IncomingCensus.selected_sheet_classes_of_largest data hc hab hOne fullDim hForest
      hCompat star input profile hSame hLargest
  -- the doubled direction, as a partition of the sheets
  have hSecondPartition :
      (contractDatum data hc hab hOne).edgePartition profile.second.1.1.1 =
        W3Nd3SourceCandidates.finePartition input profile :=
    congrArg (contractDatum data hc hab hOne).edgePartition hSame.symm
  -- the branch vertex carries the whole merged class
  have hUJoined : JoinedOnBlock (data.vertexPartition u) (mergedPartition data a b)
      (input.distinguishedBlock.1 : Fin degree) := by
    refine W3Nd2IncomingNormalization.joinedOnBlock_of_block_eq_local _ _ _
      (W3Nd3IncomingCensus.largestEndpoint data hc hab hOne star input profile).1.2 ?_
    rw [← hU]
    exact hBranchClass
  -- the two flag anchors at the unramified endpoint
  have hFlagV : (data.vertexPartition v).block
      (W3Nd3IncomingCensus.firstEndpoint data hc hab hOne star input profile).1.2 =
      (W3Nd3SourceCandidates.finePartition input profile).block profile.first.1.1.2 := by
    rw [← hV]
    exact hFirstFlag
  have hFlagV' : (data.vertexPartition v).block
      (W3Nd3IncomingCensus.secondEndpoint data hc hab hOne star input profile).1.2 =
      (W3Nd3SourceCandidates.finePartition input profile).block profile.second.1.1.2 := by
    rw [← hV']
    refine hSecondFlag.trans ?_
    exact congrArg (fun partition : SheetPartition degree ↦
      partition.block profile.second.1.1.2) hSecondPartition
  -- the two internal occurrences lie over the contracted target occurrence
  have hFirstMem : firstInternal ∈ internalEdges data hc hab hOne
      (selectedVertex data hc hab hOne star input) := by
    rw [hInternal]
    exact Finset.mem_insert_self _ _
  have hSecondMem : secondInternal ∈ internalEdges data hc hab hOne
      (selectedVertex data hc hab hOne star input) := by
    rw [hInternal]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hFirstTarget : firstInternal.1.1 = contracted :=
    ((mem_internalEdges data hc hab hOne _ firstInternal).mp hFirstMem).2.1
  have hSecondTarget : secondInternal.1.1 = contracted :=
    ((mem_internalEdges data hc hab hOne _ secondInternal).mp hSecondMem).2.1
  have hFlagNew : (data.edgePartition contracted).block firstInternal.1.2 =
      (W3Nd3SourceCandidates.finePartition input profile).block profile.first.1.1.2 := by
    have hStep : (data.edgePartition contracted).block firstInternal.1.2 =
        (data.edgePartition firstInternal.1.1).block firstInternal.1.2 :=
      congrArg (fun partition : SheetPartition degree ↦ partition.block firstInternal.1.2)
        (congrArg data.edgePartition hFirstTarget).symm
    exact hStep.trans (hFirstClass.trans hFirstFlag)
  have hFlagNew' : (data.edgePartition contracted).block secondInternal.1.2 =
      (W3Nd3SourceCandidates.finePartition input profile).block profile.second.1.1.2 := by
    have hStep : (data.edgePartition contracted).block secondInternal.1.2 =
        (data.edgePartition secondInternal.1.1).block secondInternal.1.2 :=
      congrArg (fun partition : SheetPartition degree ↦ partition.block secondInternal.1.2)
        (congrArg data.edgePartition hSecondTarget).symm
    refine hStep.trans (hSecondClass.trans (hSecondFlag.trans ?_))
    exact congrArg (fun partition : SheetPartition degree ↦
      partition.block profile.second.1.1.2) hSecondPartition
  -- turn each flag identity into a same-sheet identity
  have hAnchor : ∀ (partition : SheetPartition degree) (anchor sheet : Fin degree),
      partition.block sheet =
        (W3Nd3SourceCandidates.finePartition input profile).block anchor →
      (W3Nd3SourceCandidates.finePartition input profile).Rel anchor sheet ∧
        partition.block sheet =
          (W3Nd3SourceCandidates.finePartition input profile).block sheet := by
    intro partition anchor sheet hBlock
    have hMem : sheet ∈
        (W3Nd3SourceCandidates.finePartition input profile).block anchor := by
      rw [← hBlock]
      exact partition.self_mem_block sheet
    have hRel : (W3Nd3SourceCandidates.finePartition input profile).Rel anchor sheet :=
      ((W3Nd3SourceCandidates.finePartition input profile).mem_block_iff _ _).mp hMem
    exact ⟨hRel, hBlock.trans
      ((W3Nd3SourceCandidates.finePartition input profile).block_eq_of_rel hRel)⟩
  obtain ⟨hRelV, hBlockV⟩ := hAnchor _ _ _ hFlagV
  obtain ⟨hRelV', hBlockV'⟩ := hAnchor _ _ _ hFlagV'
  obtain ⟨hRelNew, hBlockNew⟩ := hAnchor _ _ _ hFlagNew
  obtain ⟨hRelNew', hBlockNew'⟩ := hAnchor _ _ _ hFlagNew'
  -- the two doubled-direction blocks already cover the whole merged class
  have hCover : ∀ sheet, (mergedPartition data a b).Rel
      (input.distinguishedBlock.1 : Fin degree) sheet →
      (W3Nd3SourceCandidates.finePartition input profile).Rel profile.first.1.1.2 sheet ∨
        (W3Nd3SourceCandidates.finePartition input profile).Rel
          profile.second.1.1.2 sheet := by
    intro sheet hSheet
    exact W3Nd3StableGraph.fine_rel_first_or_second input profile hSame sheet
      (cast (merged_rel_eq_wall_rel data hc hab hOne
        (input.distinguishedBlock.1 : Fin degree) sheet) hSheet)
  refine ⟨hUJoined, ?_, ?_⟩
  · intro sheet hSheet
    refine block_eq_of_cover_pair_local (mergedPartition data a b)
      (W3Nd3SourceCandidates.finePartition input profile) (data.vertexPartition v)
      (input.distinguishedBlock.1 : Fin degree)
      (W3Nd3IncomingCensus.firstEndpoint data hc hab hOne star input profile).1.2
      (W3Nd3IncomingCensus.secondEndpoint data hc hab hOne star input profile).1.2
      ?_ hBlockV hBlockV' sheet hSheet
    intro other hOther
    rcases hCover other hOther with hRel | hRel
    · exact Or.inl (hRelV.symm.trans hRel)
    · exact Or.inr (hRelV'.symm.trans hRel)
  · intro sheet hSheet
    refine block_eq_of_cover_pair_local (mergedPartition data a b)
      (W3Nd3SourceCandidates.finePartition input profile) (data.edgePartition contracted)
      (input.distinguishedBlock.1 : Fin degree)
      firstInternal.1.2 secondInternal.1.2
      ?_ hBlockNew hBlockNew' sheet hSheet
    intro other hOther
    rcases hCover other hOther with hRel | hRel
    · exact Or.inl (hRelNew.symm.trans hRel)
    · exact Or.inr (hRelNew'.symm.trans hRel)

end SelectedLargest


/-! ## The side predicate carried by each Figure 30 member -/

section CandidateSide

variable {wallTarget : CFGraph} {wallDegree : ℕ} {wall : wallTarget.V}
  {wallData : GluingDatum wallTarget wallDegree} {star : ThreeStar wallTarget wall}

/-- `M⁽¹⁾` carries the doubled direction's side predicate.  Stated as an
explicitly instantiable term equality: at the contracted wall `⟨a, hab⟩` the
surrounding expression is not type-correct at `implicit` transparency, so
`rw`/`simp only` on this wrapper cannot fire and the equation must be consumed
by `Eq.trans`. -/
theorem coarseCandidate_right (input : W3SourceInput wallData star)
    (profile : Nd3Profile wallData input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (edge : wallTarget.edges) :
    (W3Nd3SourceCandidates.coarseCandidate input profile hSame).right edge =
      rightOf profile.first.1.1.1 edge := rfl

/-- `M⁽²⁾` carries the largest direction's side predicate.  Consume it by
`Eq.trans`, as above. -/
theorem fineCandidate_right (input : W3SourceInput wallData star)
    (profile : Nd3Profile wallData input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (edge : wallTarget.edges) :
    (W3Nd3SourceCandidates.fineCandidate input profile hSame).right edge =
      rightOf profile.largest.1.1.1 edge := rfl

end CandidateSide


/-! ## The actual target placement and the literal target isomorphisms -/

section Placement

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (profile : Nd3Profile (contractDatum data hc hab hOne) input.distinguishedBlock)

/-- If the isolated direction is the DOUBLED one, the actual incoming target
placement is the target of the source-derived `M⁽¹⁾`. -/
theorem coarse_placement_of_eq_shared
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (hShared : divalentOccurrence data hc hab hOne fullDim star = profile.first.1.1.1) :
    Placement hc hab hOne
      (W3Nd3SourceCandidates.coarseCandidate input profile hSame).right := by
  change Placement hc hab hOne (rightOf profile.first.1.1.1)
  have hPlacement := divalentOccurrence_placement data hc hab hOne fullDim star
  simpa only [Placement, hShared] using hPlacement

/-- If the isolated direction is the LARGEST one, the actual incoming target
placement is the target of the source-derived `M⁽²⁾`. -/
theorem fine_placement_of_eq_largest
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (hLargest : divalentOccurrence data hc hab hOne fullDim star = profile.largest.1.1.1) :
    Placement hc hab hOne
      (W3Nd3SourceCandidates.fineCandidate input profile hSame).right := by
  change Placement hc hab hOne (rightOf profile.largest.1.1.1)
  have hPlacement := divalentOccurrence_placement data hc hab hOne fullDim star
  simpa only [Placement, hLargest] using hPlacement

/-- The literal target isomorphism to the actual `M⁽¹⁾`. -/
noncomputable def coarseTargetIso
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (hShared : divalentOccurrence data hc hab hOne fullDim star = profile.first.1.1.1) :
    Utilities.CFGraphIso target
      (graph (contract target hab hOne) ⟨a, hab⟩
        (W3Nd3SourceCandidates.coarseCandidate input profile hSame).right) :=
  M11IncomingTargetNormalization.incomingIso hc hab hOne
    (W3Nd3SourceCandidates.coarseCandidate input profile hSame).right
    (coarse_placement_of_eq_shared data hc hab hOne fullDim star input profile hSame hShared)

/-- Every literal incoming Option occurrence, including the contracted
occurrence `none`, is carried to the corresponding `M⁽¹⁾` column. -/
theorem coarseTargetIso_occurrence
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (hShared : divalentOccurrence data hc hab hOne fullDim star = profile.first.1.1.1)
    (column : Option (contract target hab hOne).edges) :
    GluingTransport.edgeEquiv
        (coarseTargetIso data hc hab hOne fullDim star input profile hSame hShared)
        (M11IncomingCoordinates.incomingColumnEquiv hc hab hOne column) =
      occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
        (W3Nd3SourceCandidates.coarseCandidate input profile hSame).right column :=
  M11IncomingTargetNormalization.incomingIso_occurrence hc hab hOne
    (W3Nd3SourceCandidates.coarseCandidate input profile hSame).right
    (coarse_placement_of_eq_shared data hc hab hOne fullDim star input profile hSame hShared)
    fullDim.targetConnected fullDim.targetGenus column

/-- The literal target isomorphism to the actual `M⁽²⁾`. -/
noncomputable def fineTargetIso
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (hLargest : divalentOccurrence data hc hab hOne fullDim star = profile.largest.1.1.1) :
    Utilities.CFGraphIso target
      (graph (contract target hab hOne) ⟨a, hab⟩
        (W3Nd3SourceCandidates.fineCandidate input profile hSame).right) :=
  M11IncomingTargetNormalization.incomingIso hc hab hOne
    (W3Nd3SourceCandidates.fineCandidate input profile hSame).right
    (fine_placement_of_eq_largest data hc hab hOne fullDim star input profile hSame hLargest)

/-- Every literal incoming Option occurrence is carried to the corresponding
`M⁽²⁾` column. -/
theorem fineTargetIso_occurrence
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (hLargest : divalentOccurrence data hc hab hOne fullDim star = profile.largest.1.1.1)
    (column : Option (contract target hab hOne).edges) :
    GluingTransport.edgeEquiv
        (fineTargetIso data hc hab hOne fullDim star input profile hSame hLargest)
        (M11IncomingCoordinates.incomingColumnEquiv hc hab hOne column) =
      occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
        (W3Nd3SourceCandidates.fineCandidate input profile hSame).right column :=
  M11IncomingTargetNormalization.incomingIso_occurrence hc hab hOne
    (W3Nd3SourceCandidates.fineCandidate input profile hSame).right
    (fine_placement_of_eq_largest data hc hab hOne fullDim star input profile hSame hLargest)
    fullDim.targetConnected fullDim.targetGenus column

end Placement


/-! ## The three wall comparisons, member by member -/

section WallBlocks

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (profile : Nd3Profile (contractDatum data hc hab hOne) input.distinguishedBlock)

/-- **`M⁽¹⁾`'s three wall partitions.**  `u` is the divalent original endpoint
and `v` the trivalent one. -/
theorem coarse_wall_blocks
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (hShared : divalentOccurrence data hc hab hOne fullDim star = profile.first.1.1.1)
    (u v : target.V)
    (hBgEdge : ∀ edge ∈ GluingDatum.incidentEdges u, ∀ sheet : Fin degree,
      ¬ (mergedPartition data a b).Rel (input.distinguishedBlock.1 : Fin degree) sheet →
      (data.edgePartition edge).block sheet = (data.vertexPartition u).block sheet)
    (hBgTri : ∀ sheet : Fin degree,
      ¬ (mergedPartition data a b).Rel (input.distinguishedBlock.1 : Fin degree) sheet →
      (data.vertexPartition v).block sheet = (mergedPartition data a b).block sheet)
    (hFlagAt : unfoldEdge hc hab hOne (divalentOccurrence data hc hab hOne fullDim star) ∈
      GluingDatum.incidentEdges u)
    (hContractedAt : contracted ∈ GluingDatum.incidentEdges u)
    (hURefines : (data.vertexPartition u).Refines (mergedPartition data a b))
    (hVRefines : (data.vertexPartition v).Refines (mergedPartition data a b))
    (hUJoined : JoinedOnBlock (data.vertexPartition u) (mergedPartition data a b)
      (input.distinguishedBlock.1 : Fin degree))
    (hVJoined : JoinedOnBlock (data.vertexPartition v) (mergedPartition data a b)
      (input.distinguishedBlock.1 : Fin degree))
    (hNewJoined : JoinedOnBlock (data.edgePartition contracted) (mergedPartition data a b)
      (input.distinguishedBlock.1 : Fin degree)) :
    (∀ sheet, (data.vertexPartition u).block sheet =
        (W3Nd2IncomingMemberMatching.pasted
          (W3Nd3SourceCandidates.coarseCandidate input profile hSame)).left.block sheet) ∧
      (∀ sheet, (data.vertexPartition v).block sheet =
        (W3Nd2IncomingMemberMatching.pasted
          (W3Nd3SourceCandidates.coarseCandidate input profile hSame)).right.block sheet) ∧
      (∀ sheet, (data.edgePartition contracted).block sheet =
        (W3Nd2IncomingMemberMatching.pasted
          (W3Nd3SourceCandidates.coarseCandidate input profile hSame)).newEdge.block sheet) := by
  classical
  have hFlagEq : (data.edgePartition (unfoldEdge hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star))).block =
      (W3Nd3SourceCandidates.finePartition input profile).block := by
    rw [hShared]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro sheet
    by_cases hSel : (mergedPartition data a b).Rel
        (input.distinguishedBlock.1 : Fin degree) sheet
    · exact (W3Nd2IncomingMemberMatching.block_eq_of_joinedOnBlock_local _ _ _
        hURefines hUJoined sheet hSel).trans
        ((merged_block_eq_wall_block data hc hab hOne sheet).trans
          (W3Nd3StableGraph.coarse_pasted_left_block_selected input profile hSame sheet
            (cast (merged_rel_eq_wall_rel data hc hab hOne _ sheet) hSel)).symm)
    · have hOffWall : ¬ ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
          (input.distinguishedBlock.1 : Fin degree) sheet :=
        fun h ↦ hSel (cast (merged_rel_eq_wall_rel data hc hab hOne _ sheet).symm h)
      exact ((hBgEdge _ hFlagAt sheet hSel).symm.trans (congrFun hFlagEq sheet)).trans
        (W3Nd3LimitMatrix.coarse_background_left_block input profile hSame sheet hOffWall).symm
  · intro sheet
    by_cases hSel : (mergedPartition data a b).Rel
        (input.distinguishedBlock.1 : Fin degree) sheet
    · exact (W3Nd2IncomingMemberMatching.block_eq_of_joinedOnBlock_local _ _ _
        hVRefines hVJoined sheet hSel).trans
        ((merged_block_eq_wall_block data hc hab hOne sheet).trans
          (W3Nd3StableGraph.coarse_pasted_right_block_selected input profile hSame sheet
            (cast (merged_rel_eq_wall_rel data hc hab hOne _ sheet) hSel)).symm)
    · have hOffWall : ¬ ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
          (input.distinguishedBlock.1 : Fin degree) sheet :=
        fun h ↦ hSel (cast (merged_rel_eq_wall_rel data hc hab hOne _ sheet).symm h)
      exact (hBgTri sheet hSel).trans
        ((merged_block_eq_wall_block data hc hab hOne sheet).trans
          (W3Nd3LimitMatrix.coarse_background_right_block input profile hSame sheet
            hOffWall).symm)
  · intro sheet
    by_cases hSel : (mergedPartition data a b).Rel
        (input.distinguishedBlock.1 : Fin degree) sheet
    · exact (W3Nd2IncomingMemberMatching.block_eq_of_joinedOnBlock_local _ _ _
        (edgePartition_refines_mergedPartition data hc) hNewJoined sheet hSel).trans
        ((merged_block_eq_wall_block data hc hab hOne sheet).trans
          (W3Nd3SourceCandidates.coarse_pasted_newEdge_block_selected input profile hSame sheet
            (cast (merged_rel_eq_wall_rel data hc hab hOne _ sheet) hSel)).symm)
    · have hOffWall : ¬ ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
          (input.distinguishedBlock.1 : Fin degree) sheet :=
        fun h ↦ hSel (cast (merged_rel_eq_wall_rel data hc hab hOne _ sheet).symm h)
      exact ((hBgEdge _ hContractedAt sheet hSel).trans
        ((hBgEdge _ hFlagAt sheet hSel).symm.trans (congrFun hFlagEq sheet))).trans
        (W3Nd3LimitMatrix.coarse_background_newEdge_block input profile hSame sheet
          hOffWall).symm

/-- **`M⁽²⁾`'s three wall partitions.**  Here the trivalent endpoint and the
contracted occurrence carry the doubled direction's two-block partition of
`A₀`, and the background uses the largest direction. -/
theorem fine_wall_blocks
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (hLargest : divalentOccurrence data hc hab hOne fullDim star = profile.largest.1.1.1)
    (u v : target.V)
    (hBgEdge : ∀ edge ∈ GluingDatum.incidentEdges u, ∀ sheet : Fin degree,
      ¬ (mergedPartition data a b).Rel (input.distinguishedBlock.1 : Fin degree) sheet →
      (data.edgePartition edge).block sheet = (data.vertexPartition u).block sheet)
    (hBgTri : ∀ sheet : Fin degree,
      ¬ (mergedPartition data a b).Rel (input.distinguishedBlock.1 : Fin degree) sheet →
      (data.vertexPartition v).block sheet = (mergedPartition data a b).block sheet)
    (hFlagAt : unfoldEdge hc hab hOne (divalentOccurrence data hc hab hOne fullDim star) ∈
      GluingDatum.incidentEdges u)
    (hContractedAt : contracted ∈ GluingDatum.incidentEdges u)
    (hURefines : (data.vertexPartition u).Refines (mergedPartition data a b))
    (hUJoined : JoinedOnBlock (data.vertexPartition u) (mergedPartition data a b)
      (input.distinguishedBlock.1 : Fin degree))
    (hVSelected : ∀ sheet, (mergedPartition data a b).Rel
        (input.distinguishedBlock.1 : Fin degree) sheet →
      (data.vertexPartition v).block sheet =
        (W3Nd3SourceCandidates.finePartition input profile).block sheet)
    (hNewSelected : ∀ sheet, (mergedPartition data a b).Rel
        (input.distinguishedBlock.1 : Fin degree) sheet →
      (data.edgePartition contracted).block sheet =
        (W3Nd3SourceCandidates.finePartition input profile).block sheet) :
    (∀ sheet, (data.vertexPartition u).block sheet =
        (W3Nd2IncomingMemberMatching.pasted
          (W3Nd3SourceCandidates.fineCandidate input profile hSame)).left.block sheet) ∧
      (∀ sheet, (data.vertexPartition v).block sheet =
        (W3Nd2IncomingMemberMatching.pasted
          (W3Nd3SourceCandidates.fineCandidate input profile hSame)).right.block sheet) ∧
      (∀ sheet, (data.edgePartition contracted).block sheet =
        (W3Nd2IncomingMemberMatching.pasted
          (W3Nd3SourceCandidates.fineCandidate input profile hSame)).newEdge.block sheet) := by
  classical
  have hFlagEq : (data.edgePartition (unfoldEdge hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star))).block =
      (W3Nd3SourceCandidates.largestPartition input profile).block := by
    rw [hLargest]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro sheet
    by_cases hSel : (mergedPartition data a b).Rel
        (input.distinguishedBlock.1 : Fin degree) sheet
    · exact (W3Nd2IncomingMemberMatching.block_eq_of_joinedOnBlock_local _ _ _
        hURefines hUJoined sheet hSel).trans
        ((merged_block_eq_wall_block data hc hab hOne sheet).trans
          (W3Nd3StableGraph.fine_pasted_left_block_selected input profile hSame sheet
            (cast (merged_rel_eq_wall_rel data hc hab hOne _ sheet) hSel)).symm)
    · have hOffWall : ¬ ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
          (input.distinguishedBlock.1 : Fin degree) sheet :=
        fun h ↦ hSel (cast (merged_rel_eq_wall_rel data hc hab hOne _ sheet).symm h)
      exact ((hBgEdge _ hFlagAt sheet hSel).symm.trans (congrFun hFlagEq sheet)).trans
        (W3Nd3LimitMatrix.fine_background_left_block input profile hSame sheet hOffWall).symm
  · intro sheet
    by_cases hSel : (mergedPartition data a b).Rel
        (input.distinguishedBlock.1 : Fin degree) sheet
    · exact (hVSelected sheet hSel).trans
        (W3Nd3StableGraph.fine_pasted_right_block_selected input profile hSame sheet
          (cast (merged_rel_eq_wall_rel data hc hab hOne _ sheet) hSel)).symm
    · have hOffWall : ¬ ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
          (input.distinguishedBlock.1 : Fin degree) sheet :=
        fun h ↦ hSel (cast (merged_rel_eq_wall_rel data hc hab hOne _ sheet).symm h)
      exact (hBgTri sheet hSel).trans
        ((merged_block_eq_wall_block data hc hab hOne sheet).trans
          (W3Nd3LimitMatrix.fine_background_right_block input profile hSame sheet
            hOffWall).symm)
  · intro sheet
    by_cases hSel : (mergedPartition data a b).Rel
        (input.distinguishedBlock.1 : Fin degree) sheet
    · exact (hNewSelected sheet hSel).trans
        (W3Nd3SourceCandidates.fine_pasted_newEdge_block_selected input profile hSame sheet
          (cast (merged_rel_eq_wall_rel data hc hab hOne _ sheet) hSel)).symm
    · have hOffWall : ¬ ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
          (input.distinguishedBlock.1 : Fin degree) sheet :=
        fun h ↦ hSel (cast (merged_rel_eq_wall_rel data hc hab hOne _ sheet).symm h)
      exact ((hBgEdge _ hContractedAt sheet hSel).trans
        ((hBgEdge _ hFlagAt sheet hSel).symm.trans (congrFun hFlagEq sheet))).trans
        (W3Nd3LimitMatrix.fine_background_newEdge_block input profile hSame sheet
          hOffWall).symm

end WallBlocks


/-! ## Pointwise matching against the named Figure 30 member -/

section Matching

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (hCompat : DanglingCompatible data hc hab hOne)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (profile : Nd3Profile (contractDatum data hc hab hOne) input.distinguishedBlock)

include hForest hCompat

/-- **`M⁽¹⁾` matches the coarse Figure 30 member, pointwise.** -/
theorem coarse_sameBlocks
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (hShared : divalentOccurrence data hc hab hOne fullDim star = profile.first.1.1.1) :
    (∀ vertex, ((GluingTransport.transport
          (coarseTargetIso data hc hab hOne fullDim star input profile hSame hShared)
          data).vertexPartition vertex).SameBlocks
        ((W3Nd3SourceCandidates.coarseCandidate input profile hSame).datum.vertexPartition
          vertex)) ∧
      (∀ edge, ((GluingTransport.transport
          (coarseTargetIso data hc hab hOne fullDim star input profile hSame hShared)
          data).edgePartition edge).SameBlocks
        ((W3Nd3SourceCandidates.coarseCandidate input profile hSame).datum.edgePartition
          edge)) := by
  classical
  have hSide : ∀ edge,
      (W3Nd3SourceCandidates.coarseCandidate input profile hSame).right edge =
        rightOf (divalentOccurrence data hc hab hOne fullDim star) edge := fun edge ↦
    (coarseCandidate_right input profile hSame edge).trans
      (congrArg (fun place ↦ rightOf place edge) hShared).symm
  obtain ⟨hJoinedA, hJoinedB⟩ := shared_selected_endpoints_joined data hc hab hOne fullDim
    hForest hCompat star input profile hSame hShared
  have hNewJoined := shared_selected_contracted_joined data hc hab hOne fullDim hForest
    hCompat star input profile hSame hShared
  rcases endpoint_valencies data hc hab hOne fullDim star with
    ⟨hLeftDiv, _, _, _⟩ | ⟨_, hRightDiv, _, _⟩
  · have hFlagAt : unfoldEdge hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star) ∈ GluingDatum.incidentEdges a :=
      (IncomingW2TargetPlacement.right_eq_false_iff_of_incident hc hab hOne _
        (divalentOccurrence_spec data hc hab hOne fullDim star).1).mp
        (W3Nd2IncomingMemberMatching.divalentOccurrence_right_eq_false data hc hab hOne
          fullDim star hLeftDiv)
    obtain ⟨hBlockLeft, hBlockRight, hBlockNew⟩ := coarse_wall_blocks data hc hab hOne fullDim
      star input profile hSame hShared a b
      (fun edge hEdge sheet hOff ↦
        W3Nd2IncomingMemberMatching.background_edge_block_eq_of_left_divalent data hc hab hOne
          fullDim hForest input hLeftDiv edge hEdge sheet hOff)
      (fun sheet hOff ↦
        W3Nd2IncomingMemberMatching.background_trivalent_block_eq_of_left_divalent data hc hab
          hOne fullDim hForest input hLeftDiv sheet hOff)
      hFlagAt (contracted_mem_incidentEdges_left hc)
      (vertexPartition_refines_mergedPartition data a b)
      (vertexPartition_refines_mergedPartition_right data a b)
      hJoinedA hJoinedB hNewJoined
    obtain ⟨hTransLeft, hTransRight⟩ :=
      W3Nd2IncomingMemberMatching.transported_endpoints_of_left_divalent data hc hab hOne
        fullDim star (W3Nd3SourceCandidates.coarseCandidate input profile hSame).right
        (coarse_placement_of_eq_shared data hc hab hOne fullDim star input profile hSame hShared)
        hSide hLeftDiv
    exact W3Nd2IncomingMemberMatching.sameBlocks_of_wall_blocks data hc hab hOne
      fullDim.targetConnected fullDim.targetGenus
      (W3Nd3SourceCandidates.coarseCandidate input profile hSame)
      (coarse_placement_of_eq_shared data hc hab hOne fullDim star input profile hSame hShared)
      (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
        hTransLeft).trans (hBlockLeft sheet))
      (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
        hTransRight).trans (hBlockRight sheet))
      hBlockNew
  · have hFlagAt : unfoldEdge hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star) ∈ GluingDatum.incidentEdges b :=
      (IncomingW2TargetPlacement.right_eq_true_iff hc hab hOne _).mp
        (W3Nd2IncomingMemberMatching.divalentOccurrence_right_eq_true data hc hab hOne
          fullDim star hRightDiv)
    obtain ⟨hBlockLeft, hBlockRight, hBlockNew⟩ := coarse_wall_blocks data hc hab hOne fullDim
      star input profile hSame hShared b a
      (fun edge hEdge sheet hOff ↦
        W3Nd2IncomingMemberMatching.background_edge_block_eq_of_right_divalent data hc hab hOne
          fullDim hForest input hRightDiv edge hEdge sheet hOff)
      (fun sheet hOff ↦
        W3Nd2IncomingMemberMatching.background_trivalent_block_eq_of_right_divalent data hc hab
          hOne fullDim hForest input hRightDiv sheet hOff)
      hFlagAt (contracted_mem_incidentEdges_right hc)
      (vertexPartition_refines_mergedPartition_right data a b)
      (vertexPartition_refines_mergedPartition data a b)
      hJoinedB hJoinedA hNewJoined
    obtain ⟨hTransLeft, hTransRight⟩ :=
      W3Nd2IncomingMemberMatching.transported_endpoints_of_right_divalent data hc hab hOne
        fullDim star (W3Nd3SourceCandidates.coarseCandidate input profile hSame).right
        (coarse_placement_of_eq_shared data hc hab hOne fullDim star input profile hSame hShared)
        hSide hRightDiv
    exact W3Nd2IncomingMemberMatching.sameBlocks_of_wall_blocks data hc hab hOne
      fullDim.targetConnected fullDim.targetGenus
      (W3Nd3SourceCandidates.coarseCandidate input profile hSame)
      (coarse_placement_of_eq_shared data hc hab hOne fullDim star input profile hSame hShared)
      (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
        hTransLeft).trans (hBlockLeft sheet))
      (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
        hTransRight).trans (hBlockRight sheet))
      hBlockNew

/-- **`M⁽²⁾` matches the oppositely oriented fine Figure 30 member,
pointwise.** -/
theorem fine_sameBlocks
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (hLargest : divalentOccurrence data hc hab hOne fullDim star = profile.largest.1.1.1) :
    (∀ vertex, ((GluingTransport.transport
          (fineTargetIso data hc hab hOne fullDim star input profile hSame hLargest)
          data).vertexPartition vertex).SameBlocks
        ((W3Nd3SourceCandidates.fineCandidate input profile hSame).datum.vertexPartition
          vertex)) ∧
      (∀ edge, ((GluingTransport.transport
          (fineTargetIso data hc hab hOne fullDim star input profile hSame hLargest)
          data).edgePartition edge).SameBlocks
        ((W3Nd3SourceCandidates.fineCandidate input profile hSame).datum.edgePartition
          edge)) := by
  classical
  have hSide : ∀ edge,
      (W3Nd3SourceCandidates.fineCandidate input profile hSame).right edge =
        rightOf (divalentOccurrence data hc hab hOne fullDim star) edge := fun edge ↦
    (fineCandidate_right input profile hSame edge).trans
      (congrArg (fun place ↦ rightOf place edge) hLargest).symm
  have hFirstNe : IncomingTargetExpansion.right hc hab hOne profile.first.1.1.1 ≠
      IncomingTargetExpansion.right hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star) :=
    W3Nd3IncomingCensus.side_ne_of_ne_divalentOccurrence data hc hab hOne fullDim star _
      (W3Nd3SourceCandidates.incident_target_mem input profile.first)
      (by rw [hLargest]; exact profile.first_target_ne)
  have hSecondNe : IncomingTargetExpansion.right hc hab hOne profile.second.1.1.1 ≠
      IncomingTargetExpansion.right hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star) :=
    W3Nd3IncomingCensus.side_ne_of_ne_divalentOccurrence data hc hab hOne fullDim star _
      (W3Nd3SourceCandidates.incident_target_mem input profile.second)
      (by rw [hLargest]; exact profile.second_target_ne)
  rcases endpoint_valencies data hc hab hOne fullDim star with
    ⟨hLeftDiv, _, _, _⟩ | ⟨_, hRightDiv, _, _⟩
  · have hDiv := W3Nd2IncomingMemberMatching.divalentOccurrence_right_eq_false data hc hab hOne
      fullDim star hLeftDiv
    have hLargestSide : IncomingTargetExpansion.right hc hab hOne
        profile.largest.1.1.1 = false :=
      (congrArg (IncomingTargetExpansion.right hc hab hOne) hLargest).symm.trans hDiv
    have hFirstSide : IncomingTargetExpansion.right hc hab hOne
        profile.first.1.1.1 = true := by
      cases hValue : IncomingTargetExpansion.right hc hab hOne profile.first.1.1.1
      · exact absurd (hValue.trans hDiv.symm) hFirstNe
      · rfl
    have hSecondSide : IncomingTargetExpansion.right hc hab hOne
        profile.second.1.1.1 = true := by
      cases hValue : IncomingTargetExpansion.right hc hab hOne profile.second.1.1.1
      · exact absurd (hValue.trans hDiv.symm) hSecondNe
      · rfl
    have hFlagAt : unfoldEdge hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star) ∈ GluingDatum.incidentEdges a :=
      (IncomingW2TargetPlacement.right_eq_false_iff_of_incident hc hab hOne _
        (divalentOccurrence_spec data hc hab hOne fullDim star).1).mp hDiv
    obtain ⟨hUJoined, hVSelected, hNewSelected⟩ := largest_selected_blocks data hc hab hOne
      fullDim hForest hCompat star input profile hSame hLargest a b
      (W3Nd2IncomingSheetClasses.endpoint_target_of_false data hc hab hOne profile.largest.1
        hLargestSide)
      (W3Nd2IncomingSheetClasses.endpoint_target_of_true data hc hab hOne profile.first.1
        hFirstSide)
      (W3Nd2IncomingSheetClasses.endpoint_target_of_true data hc hab hOne profile.second.1
        hSecondSide)
    obtain ⟨hBlockLeft, hBlockRight, hBlockNew⟩ := fine_wall_blocks data hc hab hOne fullDim
      star input profile hSame hLargest a b
      (fun edge hEdge sheet hOff ↦
        W3Nd2IncomingMemberMatching.background_edge_block_eq_of_left_divalent data hc hab hOne
          fullDim hForest input hLeftDiv edge hEdge sheet hOff)
      (fun sheet hOff ↦
        W3Nd2IncomingMemberMatching.background_trivalent_block_eq_of_left_divalent data hc hab
          hOne fullDim hForest input hLeftDiv sheet hOff)
      hFlagAt (contracted_mem_incidentEdges_left hc)
      (vertexPartition_refines_mergedPartition data a b)
      hUJoined hVSelected hNewSelected
    obtain ⟨hTransLeft, hTransRight⟩ :=
      W3Nd2IncomingMemberMatching.transported_endpoints_of_left_divalent data hc hab hOne
        fullDim star (W3Nd3SourceCandidates.fineCandidate input profile hSame).right
        (fine_placement_of_eq_largest data hc hab hOne fullDim star input profile hSame hLargest)
        hSide hLeftDiv
    exact W3Nd2IncomingMemberMatching.sameBlocks_of_wall_blocks data hc hab hOne
      fullDim.targetConnected fullDim.targetGenus
      (W3Nd3SourceCandidates.fineCandidate input profile hSame)
      (fine_placement_of_eq_largest data hc hab hOne fullDim star input profile hSame hLargest)
      (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
        hTransLeft).trans (hBlockLeft sheet))
      (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
        hTransRight).trans (hBlockRight sheet))
      hBlockNew
  · have hDiv := W3Nd2IncomingMemberMatching.divalentOccurrence_right_eq_true data hc hab hOne
      fullDim star hRightDiv
    have hLargestSide : IncomingTargetExpansion.right hc hab hOne
        profile.largest.1.1.1 = true :=
      (congrArg (IncomingTargetExpansion.right hc hab hOne) hLargest).symm.trans hDiv
    have hFirstSide : IncomingTargetExpansion.right hc hab hOne
        profile.first.1.1.1 = false := by
      cases hValue : IncomingTargetExpansion.right hc hab hOne profile.first.1.1.1
      · rfl
      · exact absurd (hValue.trans hDiv.symm) hFirstNe
    have hSecondSide : IncomingTargetExpansion.right hc hab hOne
        profile.second.1.1.1 = false := by
      cases hValue : IncomingTargetExpansion.right hc hab hOne profile.second.1.1.1
      · rfl
      · exact absurd (hValue.trans hDiv.symm) hSecondNe
    have hFlagAt : unfoldEdge hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star) ∈ GluingDatum.incidentEdges b :=
      (IncomingW2TargetPlacement.right_eq_true_iff hc hab hOne _).mp hDiv
    obtain ⟨hUJoined, hVSelected, hNewSelected⟩ := largest_selected_blocks data hc hab hOne
      fullDim hForest hCompat star input profile hSame hLargest b a
      (W3Nd2IncomingSheetClasses.endpoint_target_of_true data hc hab hOne profile.largest.1
        hLargestSide)
      (W3Nd2IncomingSheetClasses.endpoint_target_of_false data hc hab hOne profile.first.1
        hFirstSide)
      (W3Nd2IncomingSheetClasses.endpoint_target_of_false data hc hab hOne profile.second.1
        hSecondSide)
    obtain ⟨hBlockLeft, hBlockRight, hBlockNew⟩ := fine_wall_blocks data hc hab hOne fullDim
      star input profile hSame hLargest b a
      (fun edge hEdge sheet hOff ↦
        W3Nd2IncomingMemberMatching.background_edge_block_eq_of_right_divalent data hc hab hOne
          fullDim hForest input hRightDiv edge hEdge sheet hOff)
      (fun sheet hOff ↦
        W3Nd2IncomingMemberMatching.background_trivalent_block_eq_of_right_divalent data hc hab
          hOne fullDim hForest input hRightDiv sheet hOff)
      hFlagAt (contracted_mem_incidentEdges_right hc)
      (vertexPartition_refines_mergedPartition_right data a b)
      hUJoined hVSelected hNewSelected
    obtain ⟨hTransLeft, hTransRight⟩ :=
      W3Nd2IncomingMemberMatching.transported_endpoints_of_right_divalent data hc hab hOne
        fullDim star (W3Nd3SourceCandidates.fineCandidate input profile hSame).right
        (fine_placement_of_eq_largest data hc hab hOne fullDim star input profile hSame hLargest)
        hSide hRightDiv
    exact W3Nd2IncomingMemberMatching.sameBlocks_of_wall_blocks data hc hab hOne
      fullDim.targetConnected fullDim.targetGenus
      (W3Nd3SourceCandidates.fineCandidate input profile hSame)
      (fine_placement_of_eq_largest data hc hab hOne fullDim star input profile hSame hLargest)
      (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
        hTransLeft).trans (hBlockLeft sheet))
      (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
        hTransRight).trans (hBlockRight sheet))
      hBlockNew

/-- The vertex half of `coarse_sameBlocks`, named for the exit statement. -/
theorem coarse_vertexPartitions_sameBlocks
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (hShared : divalentOccurrence data hc hab hOne fullDim star = profile.first.1.1.1) :
    ∀ vertex, ((GluingTransport.transport
        (coarseTargetIso data hc hab hOne fullDim star input profile hSame hShared)
        data).vertexPartition vertex).SameBlocks
      ((W3Nd3SourceCandidates.coarseCandidate input profile hSame).datum.vertexPartition
        vertex) :=
  (coarse_sameBlocks data hc hab hOne fullDim hForest hCompat star input profile
    hSame hShared).1

/-- The occurrence half of `coarse_sameBlocks`. -/
theorem coarse_edgePartitions_sameBlocks
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (hShared : divalentOccurrence data hc hab hOne fullDim star = profile.first.1.1.1) :
    ∀ edge, ((GluingTransport.transport
        (coarseTargetIso data hc hab hOne fullDim star input profile hSame hShared)
        data).edgePartition edge).SameBlocks
      ((W3Nd3SourceCandidates.coarseCandidate input profile hSame).datum.edgePartition edge) :=
  (coarse_sameBlocks data hc hab hOne fullDim hForest hCompat star input profile
    hSame hShared).2

/-- The vertex half of `fine_sameBlocks`. -/
theorem fine_vertexPartitions_sameBlocks
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (hLargest : divalentOccurrence data hc hab hOne fullDim star = profile.largest.1.1.1) :
    ∀ vertex, ((GluingTransport.transport
        (fineTargetIso data hc hab hOne fullDim star input profile hSame hLargest)
        data).vertexPartition vertex).SameBlocks
      ((W3Nd3SourceCandidates.fineCandidate input profile hSame).datum.vertexPartition
        vertex) :=
  (fine_sameBlocks data hc hab hOne fullDim hForest hCompat star input profile
    hSame hLargest).1

/-- The occurrence half of `fine_sameBlocks`. -/
theorem fine_edgePartitions_sameBlocks
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (hLargest : divalentOccurrence data hc hab hOne fullDim star = profile.largest.1.1.1) :
    ∀ edge, ((GluingTransport.transport
        (fineTargetIso data hc hab hOne fullDim star input profile hSame hLargest)
        data).edgePartition edge).SameBlocks
      ((W3Nd3SourceCandidates.fineCandidate input profile hSame).datum.edgePartition edge) :=
  (fine_sameBlocks data hc hab hOne fullDim hForest hCompat star input profile
    hSame hLargest).2

end Matching


/-! ## The certified exit: the incoming datum IS a named Figure 30 member -/

section Identification

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (hCompat : DanglingCompatible data hc hab hOne)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (profile : Nd3Profile (contractDatum data hc hab hOne) input.distinguishedBlock)

include hForest hCompat

/-- **The identification step.**  An arbitrary incoming W3 nd3 datum whose
contraction of the single edge between `a` and `b` is a forest with dangling
compatibility, over a genuine trivalent contracted wall with a Figure 30 nd3
profile and the doubled direction `hSame`, *is* one of the two named Figure 30
members: the orientation dichotomy
`W3Nd3IncomingCensus.divalentOccurrence_eq_shared_or_largest` decides which, the
literal Option column dictionary is the actual one, and the stored
representative tables agree after the within-block transpositions of
`Infrastructure.PartitionNormalization`.

The two branches are `M⁽¹⁾` (`α = 3`) and `M⁽²⁾` (`α = 4`) and both genuinely
occur; the hypothesis bundle is exactly the one already shown jointly
satisfiable by `W3Nd3IncomingCensus.selected_fibre_census_of_shared` and
`_of_largest`.  Nothing is added to it.

The original-coordinate restatement that feeds `W3Nd3CommonBalance`'s
identified-member exit is not proved here; see `W3Nd3ArbitraryExit` and
`W3Nd3GraphTracking`. -/
theorem exists_member_normalization
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (∃ hShared : divalentOccurrence data hc hab hOne fullDim star = profile.first.1.1.1,
      (∀ column : Option (contract target hab hOne).edges,
          GluingTransport.edgeEquiv
              (coarseTargetIso data hc hab hOne fullDim star input profile hSame hShared)
              (M11IncomingCoordinates.incomingColumnEquiv hc hab hOne column) =
            occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
              (W3Nd3SourceCandidates.coarseCandidate input profile hSame).right column) ∧
        W3Nd2IncomingMemberMatching.NormalizedAgainst data fullDim
          (coarseTargetIso data hc hab hOne fullDim star input profile hSame hShared)
          (W3Nd3SourceCandidates.coarseCandidate input profile hSame).datum
          (coarse_vertexPartitions_sameBlocks data hc hab hOne fullDim hForest hCompat star
            input profile hSame hShared)
          (coarse_edgePartitions_sameBlocks data hc hab hOne fullDim hForest hCompat star
            input profile hSame hShared)) ∨
      (∃ hLargest : divalentOccurrence data hc hab hOne fullDim star = profile.largest.1.1.1,
        (∀ column : Option (contract target hab hOne).edges,
            GluingTransport.edgeEquiv
                (fineTargetIso data hc hab hOne fullDim star input profile hSame hLargest)
                (M11IncomingCoordinates.incomingColumnEquiv hc hab hOne column) =
              occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
                (W3Nd3SourceCandidates.fineCandidate input profile hSame).right column) ∧
          W3Nd2IncomingMemberMatching.NormalizedAgainst data fullDim
            (fineTargetIso data hc hab hOne fullDim star input profile hSame hLargest)
            (W3Nd3SourceCandidates.fineCandidate input profile hSame).datum
            (fine_vertexPartitions_sameBlocks data hc hab hOne fullDim hForest hCompat star
              input profile hSame hLargest)
            (fine_edgePartitions_sameBlocks data hc hab hOne fullDim hForest hCompat star
              input profile hSame hLargest)) := by
  rcases W3Nd3IncomingCensus.divalentOccurrence_eq_shared_or_largest data hc hab hOne fullDim
      hForest hCompat star input profile hSame with hShared | hLargest
  · exact Or.inl ⟨hShared,
      coarseTargetIso_occurrence data hc hab hOne fullDim star input profile hSame hShared,
      W3Nd2IncomingMemberMatching.normalizedAgainst data fullDim _ _ _ _⟩
  · exact Or.inr ⟨hLargest,
      fineTargetIso_occurrence data hc hab hOne fullDim star input profile hSame hLargest,
      W3Nd2IncomingMemberMatching.normalizedAgainst data fullDim _ _ _ _⟩

end Identification

end DraismaVargas.LocalCases.W3Nd3IncomingMatching
