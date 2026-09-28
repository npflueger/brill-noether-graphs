import DraismaVargas.LocalCases.W3Nd3StableGraph
import DraismaVargas.LocalCases.W3Nd2Background
import DraismaVargas.LocalCases.ResolutionAwayFromWall
import DraismaVargas.LocalCases.DivalentSourceLocal
import DraismaVargas.LocalCases.StableSourceMatrix
import DraismaVargas.LocalCases.ResolutionStableIncidence
import DraismaVargas.LocalCases.StableGraphIncidence
import DraismaVargas.LocalCases.W3FourRowDescent

/-!
# Retained and new columns of the two Figure 30 members

Source: Draisma–Vargas Part I, arXiv:1909.12924, case `{w3-r1-nd3-t3}`, Figure 30 and
Equation (4).  `W3Nd3SourceCandidates` builds both members `M⁽¹⁾` (`α = 3`) and
`M⁽²⁾` (`α = 4`); `W3Nd3StableGraph` supplies the endpoint half — covering
layer, the exact `nonDanglingIncident` sets with their valencies, survival and
stable-row identities for the new occurrences, and Equation (4)'s three
denominators `k₄ = k₂ + k₃`, `k₂`, `k₃` on the surviving new rows.  This module
is the column half.

## What this module proves

For an actual `W3SourceInput`, an actual `Nd3Profile` and the doubled direction
`hSame`:

* **Background rows.**  `coarse_background_left_card_two`,
  `fine_background_left_card_two`,
  `coarse_background_new_survives_iff_doubled` and
  `fine_background_new_survives_iff_largest`: away from the distinguished block
  each member's divalent endpoint carries exactly the retained old occurrence
  and the corresponding new one.  That the pair has one stable row is *not*
  proved here -- `coarseBackgroundShape` / `fineBackgroundShape` exhibit both
  members as `W3FourSurvival.BackgroundShape`s and
  `W3FourRowDescent.Background.background_retained_eq_of_consecutive` supplies
  the identity at arbitrary old valency.
* **Stable-row transport.**  `coarseStablePathLift` / `fineStablePathLift` with
  `coarseStablePathLift_surjective` / `fineStablePathLift_surjective`, the
  reverse assignments `coarseRowOfEdge` / `fineRowOfEdge` with their quotient
  descents, and hence the equivalences `coarseStablePathEquiv` and
  `fineStablePathEquiv`.  Both are `Equiv.ofBijective` from an explicit left
  inverse and an explicit surjection; no cardinality argument is used.
* **Stable incidence graphs.**  `coarseBranchVertexEquiv`,
  `fineBranchVertexEquiv` and the incidence identities
  `coarse_incidenceCount_selected`, `coarse_incidenceCount_background`,
  `fine_incidenceCount_selected`, `fine_incidenceCount_background`, assembled
  into `coarseStableGraphEquivalence` and `fineStableGraphEquivalence`
  (`StableGraphIncidence.Equivalence`), with `coarse_hasPathEnds` and
  `fine_hasPathEnds`.
* **Limit matrices.**  `coarse_matrix_retained` and `fine_matrix_retained`
  (every retained column is literally the source's), and Equation (4)'s new
  columns: `coarse_matrix_new` / `coarse_matrix_new_on_old_row` give
  `c⁽¹⁾`'s selected coefficient `1/(k₂+k₃)` on the row of the retained largest
  direction `e₄` plus the exact old `t₃` background sum, and `fine_matrix_new`
  / `fine_matrix_new_on_old_row` give `c⁽²⁾`'s **two** selected coefficients
  `1/k₂` and `1/k₃` on the rows of `e₂` and `e₃` plus the exact old `t₄`
  background sum.

Every flag statement is about **occurrences**, and the two selected terms of
the fine new column are kept as two separate indicator terms rather than a sum
over a set of row labels: nothing here asserts that the rows of `e₂` and `e₃`
are distinct, so a stable loop through the branch vertex is not excluded and
the formulas stay correct if those rows coincide.

## Where the nd2 chain transfers, and where it does not

Transferring essentially verbatim, with `smallTarget ↦ t₃` in `M⁽¹⁾` and
`largeTarget ↦ t₄` in `M⁽²⁾`: all of `W3Nd2Background`; the background half of
`W3Nd2StableLift`; the background replacement of `W3Nd2RowDescent` /
`W3Nd2FineRowDescent`, which is a bijection of surviving incidence sets for
**arbitrary** old valency; and both limit-matrix modules apart from the new
column of the fine member.

Not transferring:

* **The selected vertex is a branch vertex, and that makes the transport
  *easier*, not harder.**  `Consecutive` requires surviving valency two at the
  joining vertex, and the distinguished source vertex has valency three
  (`W3Nd3StableGraph.source_nonDanglingValency_eq_three`), as does the divalent
  endpoint of each member (`coarse_left_nonDanglingValency_eq_three`,
  `fine_left_nonDanglingValency_eq_three`).  So the selected case of both
  well-definedness arguments is **vacuous** here
  (`selected_nonDanglingValency_ne_two`, `coarse_left_selected_valency_eq_three`,
  `fine_left_selected_valency_eq_three`), and nd2's
  `W3Nd2StableLift.coarse_retained_selected_eq_anchor` /
  `fine_retained_selected_eq_anchor` — the claim that both retained selected
  survivors acquire the new occurrence's row — has no nd3 analogue and needs
  none.
* **`W3Nd2Coarse/FineStableGraph.old_wall_branch_background` is false here.**
  In nd2 the distinguished source vertex is divalent, so every old branch above
  the wall is a background block and moves to the *fresh* endpoint.  In nd3 the
  distinguished source vertex is a branch vertex and moves to the *divalent*
  endpoint, which is where both members keep their three flags.  The branch map
  therefore has three cases, not two (`coarseBranchVertexMap`,
  `fineBranchVertexMap`), and the selected incidence identity is a genuine new
  flag bijection: `e₄ ↦ e'` and the identity on `e₂, e₃` for `M⁽¹⁾`
  (`coarseSelectedFlag`), and `e₂ ↦ e'`, `e₃ ↦ e''`, `e₄ ↦ e₄` for `M⁽²⁾`
  (`fineSelectedFlag`).
* **There is no residual sheet**, so `M⁽²⁾` has two surviving selected new
  occurrences where nd2's fine member has one survivor and one dangler.  The
  fine reverse row assignment is correspondingly two-valued on selected sheets
  (`fineNewOldSourceEdge`), and the fine new column carries two selected terms
  (`fine_matrix_new`).  Survival of the new occurrences is not reproved here:
  it is `W3Nd3StableGraph.coarse_anchor_new_survives` and `fine_new_survives`,
  argued at the opposite endpoint.

## Why the hypotheses can hold at once

The hypotheses are exactly those of `W3Nd3StableGraph`: an actual `W3SourceInput`, an
actual `Nd3Profile` on its distinguished block, and `hSame`, the first of the
three mutually exclusive alternatives of `W3R1SourceProfile.Nd3Profile.cases`.
Nothing numerical is assumed; `k₂ + k₃ = |A₀|` and `k₄ = |A₀|` are derived
through `Nd3Profile.doubled_direction`.  The two facts the argument leans on — that the
distinguished source vertex is trivalent, and that each member's divalent
endpoint is trivalent — are proved, not assumed.  The vacuous selected cases
above are therefore vacuous because `Consecutive` demands surviving valency two
at a vertex that has valency three, not because no such configuration exists:
under the very same hypotheses `W3Nd3StableGraph` exhibits three distinct
surviving occurrences at the source vertex (`profile.surviving` with
`first_ne_second`, `first_ne_largest`, `second_ne_largest`) and two distinct
surviving new occurrences in `M⁽²⁾` (`fine_new_first_ne_second`).

## What is not here

The pairing of the two members into a balanced family is `W3Nd3CommonBalance`'s.
`GlobalCoarseFine.nd3BalancedFamily` itself is not used: it does not accept a
reversed fine pattern, and `fineCandidate` is the `LocalResolution.reverse` of
`Nd3Geometry.fineLocal`, exactly as `W3Nd3SourceCandidates` records.
-/
namespace DraismaVargas.LocalCases.W3Nd3LimitMatrix

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open W3R1SourceProfile ResolutionCoarseFine GlobalCoarseFine
open ResolutionM11 ResolutionM1k ResolutionPruning ResolutionSurvival
open ResolutionAwayFromWall M11SplitRows M11SourceCandidates
open DivalentSourceLocal StableSourceMatrix
open ResolutionStableIncidence StableGraphIncidence StablePathCount
open W3Nd3SourceCandidates W3Nd3StableGraph
open W3Nd2SourceCandidates (rightOf)
open W3Nd2Background (survives_iff_of_card_two
  nonDanglingValency_eq_two_of_card_two_of_survives)
open W3Nd2Survival (oldSourceEdge_incident_old)
open M11SplitSurvival (oldSourceEdge_incident_fresh)
open W3FourSurvival (BackgroundShape)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (datum : GluingDatum target degree)
    (vertex : datum.SourceVertex) : DecidableEq (IncidentSourceEdge datum vertex) :=
  Classical.decEq _

/-! ## The background resolutions of the two members -/

/-- Away from the distinguished block, `M⁽¹⁾` uses the doubled direction `t₃`
at the divalent endpoint and on the new edge. -/
theorem coarse_resolution_background (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (coarseCandidate input profile hSame).resolution sheet =
      fineResolution (data.vertexPartition wall) (finePartition input profile)
        (fine_refines_wall input profile) := by
  change LocalResolution.onBlock (data.vertexPartition wall)
      profile.first.1.1.2 (thirdResolution (data.vertexPartition wall))
      (background input profile).resolution sheet = _
  rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ (by
    intro hAnchor
    exact hSheet ((incident_wall_rel input profile.first).trans hAnchor))]
  rfl

/-- Away from the distinguished block, `M⁽²⁾` uses the largest direction `t₄`
at the divalent endpoint and on the new edge. -/
theorem fine_resolution_background (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (fineCandidate input profile hSame).resolution sheet =
      fineResolution (data.vertexPartition wall) (largestPartition input profile)
        (largest_refines_wall input profile) := by
  change LocalResolution.onBlock (data.vertexPartition wall)
      profile.first.1.1.2 (selectedResolution input profile)
      (fineBackground input profile).resolution sheet = _
  rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ (by
    intro hAnchor
    exact hSheet ((incident_wall_rel input profile.first).trans hAnchor))]
  rfl

theorem coarse_background_left_block (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (coarsePastedResolution input profile hSame).left.block sheet =
      (finePartition input profile).block sheet := by
  change (LocalResolution.pasteLeft (data.vertexPartition wall)
    (coarseCandidate input profile hSame).resolution
    (coarseCandidate input profile hSame).contracts).block sheet = _
  unfold LocalResolution.pasteLeft
  rw [(data.vertexPartition wall).paste_block]
  rw [coarse_resolution_background input profile hSame
    ((data.vertexPartition wall).repr sheet) (by
      intro hDist
      exact hSheet (hDist.trans ((data.vertexPartition wall).rel_repr_left sheet)))]
  rfl

theorem coarse_background_newEdge_block (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (coarsePastedResolution input profile hSame).newEdge.block sheet =
      (finePartition input profile).block sheet := by
  change (LocalResolution.pasteNewEdge (data.vertexPartition wall)
    (coarseCandidate input profile hSame).resolution
    (coarseCandidate input profile hSame).contracts).block sheet = _
  unfold LocalResolution.pasteNewEdge
  rw [(data.vertexPartition wall).paste_block]
  rw [coarse_resolution_background input profile hSame
    ((data.vertexPartition wall).repr sheet) (by
      intro hDist
      exact hSheet (hDist.trans ((data.vertexPartition wall).rel_repr_left sheet)))]
  rfl

theorem coarse_background_right_block (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (coarsePastedResolution input profile hSame).right.block sheet =
      (data.vertexPartition wall).block sheet := by
  change (LocalResolution.pasteRight (data.vertexPartition wall)
    (coarseCandidate input profile hSame).resolution
    (coarseCandidate input profile hSame).contracts).block sheet = _
  unfold LocalResolution.pasteRight
  rw [(data.vertexPartition wall).paste_block]
  rw [coarse_resolution_background input profile hSame
    ((data.vertexPartition wall).repr sheet) (by
      intro hDist
      exact hSheet (hDist.trans ((data.vertexPartition wall).rel_repr_left sheet)))]
  rfl

theorem fine_background_left_block (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (finePastedResolution input profile hSame).left.block sheet =
      (largestPartition input profile).block sheet := by
  change (LocalResolution.pasteLeft (data.vertexPartition wall)
    (fineCandidate input profile hSame).resolution
    (fineCandidate input profile hSame).contracts).block sheet = _
  unfold LocalResolution.pasteLeft
  rw [(data.vertexPartition wall).paste_block]
  rw [fine_resolution_background input profile hSame
    ((data.vertexPartition wall).repr sheet) (by
      intro hDist
      exact hSheet (hDist.trans ((data.vertexPartition wall).rel_repr_left sheet)))]
  rfl

theorem fine_background_newEdge_block (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (finePastedResolution input profile hSame).newEdge.block sheet =
      (largestPartition input profile).block sheet := by
  change (LocalResolution.pasteNewEdge (data.vertexPartition wall)
    (fineCandidate input profile hSame).resolution
    (fineCandidate input profile hSame).contracts).block sheet = _
  unfold LocalResolution.pasteNewEdge
  rw [(data.vertexPartition wall).paste_block]
  rw [fine_resolution_background input profile hSame
    ((data.vertexPartition wall).repr sheet) (by
      intro hDist
      exact hSheet (hDist.trans ((data.vertexPartition wall).rel_repr_left sheet)))]
  rfl

theorem fine_background_right_block (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (finePastedResolution input profile hSame).right.block sheet =
      (data.vertexPartition wall).block sheet := by
  change (LocalResolution.pasteRight (data.vertexPartition wall)
    (fineCandidate input profile hSame).resolution
    (fineCandidate input profile hSame).contracts).block sheet = _
  unfold LocalResolution.pasteRight
  rw [(data.vertexPartition wall).paste_block]
  rw [fine_resolution_background input profile hSame
    ((data.vertexPartition wall).repr sheet) (by
      intro hDist
      exact hSheet (hDist.trans ((data.vertexPartition wall).rel_repr_left sheet)))]
  rfl

/-! ## The two target occurrences at a divalent endpoint -/

theorem coarse_left_target_incident_pair (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    GluingDatum.incidentEdges
        (target := graph target wall (coarseCandidate input profile hSame).right)
        (oldVertex target wall) =
      {occurrenceEquiv target wall (coarseCandidate input profile hSame).right none,
        occurrenceEquiv target wall (coarseCandidate input profile hSame).right
          (some profile.first.1.1.1)} := by
  classical
  let candidate := coarseCandidate input profile hSame
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro edge hEdge
    rcases Finset.mem_insert.mp hEdge with rfl | hEdge
    · simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and, occurrenceEquiv_none]
      exact Or.inl rfl
    · rw [Finset.mem_singleton] at hEdge
      subst edge
      simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and, occurrenceEquiv_some]
      apply (oldEnds_incident_oldVertex_iff target wall candidate.right
        profile.first.1.1.1).mpr
      refine ⟨?_, coarse_right_doubled input profile hSame⟩
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter,
        Finset.mem_univ, true_and] using incident_target_mem input profile.first
  · have hNe : occurrenceEquiv target wall candidate.right none ≠
        occurrenceEquiv target wall candidate.right (some profile.first.1.1.1) :=
      (occurrenceEquiv target wall candidate.right).injective.ne (by simp)
    rw [Finset.card_pair hNe]
    exact le_of_eq (candidate_target_valencies candidate).1

theorem fine_left_target_incident_pair (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    GluingDatum.incidentEdges
        (target := graph target wall (fineCandidate input profile hSame).right)
        (oldVertex target wall) =
      {occurrenceEquiv target wall (fineCandidate input profile hSame).right none,
        occurrenceEquiv target wall (fineCandidate input profile hSame).right
          (some (largestTarget input profile))} := by
  classical
  let candidate := fineCandidate input profile hSame
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro edge hEdge
    rcases Finset.mem_insert.mp hEdge with rfl | hEdge
    · simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and, occurrenceEquiv_none]
      exact Or.inl rfl
    · rw [Finset.mem_singleton] at hEdge
      subst edge
      simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and, occurrenceEquiv_some]
      apply (oldEnds_incident_oldVertex_iff target wall candidate.right
        (largestTarget input profile)).mpr
      refine ⟨?_, fine_right_largest input profile hSame⟩
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter,
        Finset.mem_univ, true_and] using largestTarget_mem input profile
  · have hNe : occurrenceEquiv target wall candidate.right none ≠
        occurrenceEquiv target wall candidate.right
          (some (largestTarget input profile)) :=
      (occurrenceEquiv target wall candidate.right).injective.ne (by simp)
    rw [Finset.card_pair hNe]
    exact le_of_eq (candidate_target_valencies candidate).1

/-! ## Each background divalent endpoint carries exactly two occurrences -/

theorem coarse_background_left_card_two (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    Fintype.card (IncidentSourceEdge (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) sheet)) = 2 := by
  classical
  let candidate := coarseCandidate input profile hSame
  rw [card_incidentSourceEdge_eq_sum_blockCountWithin]
  change (∑ edge ∈ GluingDatum.incidentEdges (oldVertex target wall),
    (candidate.datum.edgePartition edge).blockCountWithin
      (candidate.datum.vertexPartition (oldVertex target wall))
      ((candidate.datum.vertexPartition (oldVertex target wall)).repr sheet)) = 2
  rw [coarse_left_target_incident_pair input profile hSame]
  have hNe : occurrenceEquiv target wall candidate.right none ≠
      occurrenceEquiv target wall candidate.right (some profile.first.1.1.1) :=
    (occurrenceEquiv target wall candidate.right).injective.ne (by simp)
  rw [Finset.sum_pair hNe]
  have hVertex : candidate.datum.vertexPartition (oldVertex target wall) =
      (coarsePastedResolution input profile hSame).left :=
    GlobalResolution.expandedVertexPartition_old_wall data wall _
  have hNew : candidate.datum.edgePartition
      (occurrenceEquiv target wall candidate.right none) =
      (coarsePastedResolution input profile hSame).newEdge :=
    GlobalResolution.expandedEdgePartition_new data wall _ _
  have hOld : candidate.datum.edgePartition
      (occurrenceEquiv target wall candidate.right (some profile.first.1.1.1)) =
      finePartition input profile :=
    GlobalResolution.expandedEdgePartition_old data wall _ _ _
  rw [hVertex, hNew, hOld]
  rw [SheetPartition.blockCountWithin_congr _ _
      ((coarsePastedResolution input profile hSame).left.rel_repr_left sheet),
    SheetPartition.blockCountWithin_congr _ _
      ((coarsePastedResolution input profile hSame).left.rel_repr_left sheet)]
  have hRepr : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1
      ((data.vertexPartition wall).repr sheet) := by
    intro hDist
    exact hSheet (hDist.trans ((data.vertexPartition wall).rel_repr_left sheet))
  have hNewCount : (coarsePastedResolution input profile hSame).newEdge.blockCountWithin
      (coarsePastedResolution input profile hSame).left sheet = 1 := by
    rw [LocalResolution.paste_newEdge_blockCountWithin_left,
      coarse_resolution_background input profile hSame _ hRepr]
    exact SheetPartition.blockCountWithin_self _ _
  have hOldCount : (finePartition input profile).blockCountWithin
      (coarsePastedResolution input profile hSame).left sheet = 1 := by
    unfold SheetPartition.blockCountWithin
    rw [coarse_background_left_block input profile hSame sheet hSheet]
    exact SheetPartition.blockCountWithin_self _ _
  rw [hNewCount, hOldCount]

theorem fine_background_left_card_two (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    Fintype.card (IncidentSourceEdge (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) sheet)) = 2 := by
  classical
  let candidate := fineCandidate input profile hSame
  rw [card_incidentSourceEdge_eq_sum_blockCountWithin]
  change (∑ edge ∈ GluingDatum.incidentEdges (oldVertex target wall),
    (candidate.datum.edgePartition edge).blockCountWithin
      (candidate.datum.vertexPartition (oldVertex target wall))
      ((candidate.datum.vertexPartition (oldVertex target wall)).repr sheet)) = 2
  rw [fine_left_target_incident_pair input profile hSame]
  have hNe : occurrenceEquiv target wall candidate.right none ≠
      occurrenceEquiv target wall candidate.right
        (some (largestTarget input profile)) :=
    (occurrenceEquiv target wall candidate.right).injective.ne (by simp)
  rw [Finset.sum_pair hNe]
  have hVertex : candidate.datum.vertexPartition (oldVertex target wall) =
      (finePastedResolution input profile hSame).left :=
    GlobalResolution.expandedVertexPartition_old_wall data wall _
  have hNew : candidate.datum.edgePartition
      (occurrenceEquiv target wall candidate.right none) =
      (finePastedResolution input profile hSame).newEdge :=
    GlobalResolution.expandedEdgePartition_new data wall _ _
  have hOld : candidate.datum.edgePartition
      (occurrenceEquiv target wall candidate.right
        (some (largestTarget input profile))) =
      largestPartition input profile :=
    GlobalResolution.expandedEdgePartition_old data wall _ _ _
  rw [hVertex, hNew, hOld]
  rw [SheetPartition.blockCountWithin_congr _ _
      ((finePastedResolution input profile hSame).left.rel_repr_left sheet),
    SheetPartition.blockCountWithin_congr _ _
      ((finePastedResolution input profile hSame).left.rel_repr_left sheet)]
  have hRepr : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1
      ((data.vertexPartition wall).repr sheet) := by
    intro hDist
    exact hSheet (hDist.trans ((data.vertexPartition wall).rel_repr_left sheet))
  have hNewCount : (finePastedResolution input profile hSame).newEdge.blockCountWithin
      (finePastedResolution input profile hSame).left sheet = 1 := by
    rw [LocalResolution.paste_newEdge_blockCountWithin_left,
      fine_resolution_background input profile hSame _ hRepr]
    exact SheetPartition.blockCountWithin_self _ _
  have hOldCount : (largestPartition input profile).blockCountWithin
      (finePastedResolution input profile hSame).left sheet = 1 := by
    unfold SheetPartition.blockCountWithin
    rw [fine_background_left_block input profile hSame sheet hSheet]
    exact SheetPartition.blockCountWithin_self _ _
  rw [hNewCount, hOldCount]

/-! ## Background new occurrences and their stable rows -/

theorem coarse_background_new_incident_left (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree) :
    Incident (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).newSourceEdge sheet)
      ((coarseCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) sheet) :=
  Or.inl (congrArg Prod.fst (GlobalResolution.sourceEnds_newSourceEdge data wall
    (coarseCandidate input profile hSame).right
    (coarsePastedResolution input profile hSame)
    (GlobalAssembly.blockwiseCompatible _ _ _ _ _
      (coarseCandidate input profile hSame).exterior) sheet))

theorem coarse_background_doubled_incident_left (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree) :
    Incident (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).oldSourceEdge
        (data.sourceEdge profile.first.1.1.1 sheet))
      ((coarseCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) sheet) :=
  oldSourceEdge_incident_old (coarseCandidate input profile hSame)
    profile.first.1.1.1 (incident_target_mem input profile.first)
    (coarse_right_doubled input profile hSame) sheet

theorem fine_background_new_incident_left (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree) :
    Incident (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).newSourceEdge sheet)
      ((fineCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) sheet) :=
  fine_new_incident_left input profile hSame sheet

theorem fine_background_largest_incident_left (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree) :
    Incident (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).oldSourceEdge
        (data.sourceEdge (largestTarget input profile) sheet))
      ((fineCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) sheet) :=
  oldSourceEdge_incident_old (fineCandidate input profile hSame)
    (largestTarget input profile) (largestTarget_mem input profile)
    (fine_right_largest input profile hSame) sheet

/-- At a background block the new occurrence of `M⁽¹⁾` survives exactly when
the doubled direction's occurrence through the same sheet survives. -/
theorem coarse_background_new_survives_iff_doubled
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (¬ IsDangling (coarseCandidate input profile hSame).datum
        ((coarseCandidate input profile hSame).newSourceEdge sheet)) ↔
      ¬ IsDangling data (data.sourceEdge profile.first.1.1.1 sheet) := by
  let candidate := coarseCandidate input profile hSame
  have hPair := survives_iff_of_card_two candidate.datum
    (coarseCandidate_valid input profile hSame).1
    (candidate.datum.sourceEndpoint (oldVertex target wall) sheet)
    (candidate.newSourceEdge sheet)
    (candidate.oldSourceEdge (data.sourceEdge profile.first.1.1.1 sheet))
    (coarse_background_new_incident_left input profile hSame sheet)
    (coarse_background_doubled_incident_left input profile hSame sheet)
    (coarse_background_left_card_two input profile hSame sheet hSheet)
  exact hPair.trans (not_congr (coarse_old_isDangling_iff input profile hSame _))

/-- At a background block the new occurrence of `M⁽²⁾` survives exactly when
the largest direction's occurrence through the same sheet survives. -/
theorem fine_background_new_survives_iff_largest
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (¬ IsDangling (fineCandidate input profile hSame).datum
        ((fineCandidate input profile hSame).newSourceEdge sheet)) ↔
      ¬ IsDangling data (data.sourceEdge (largestTarget input profile) sheet) := by
  let candidate := fineCandidate input profile hSame
  have hPair := survives_iff_of_card_two candidate.datum
    (fineCandidate_valid input profile hSame).1
    (candidate.datum.sourceEndpoint (oldVertex target wall) sheet)
    (candidate.newSourceEdge sheet)
    (candidate.oldSourceEdge (data.sourceEdge (largestTarget input profile) sheet))
    (fine_background_new_incident_left input profile hSame sheet)
    (fine_background_largest_incident_left input profile hSame sheet)
    (fine_background_left_card_two input profile hSame sheet hSheet)
  exact hPair.trans (not_congr (fine_old_isDangling_iff input profile hSame _))

theorem coarse_background_new_consecutive_doubled
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hOld : ¬ IsDangling data (data.sourceEdge profile.first.1.1.1 sheet)) :
    Consecutive (coarseCandidate input profile hSame).datum
      ⟨(coarseCandidate input profile hSame).newSourceEdge sheet,
        (coarse_background_new_survives_iff_doubled input profile hSame sheet
          hSheet).2 hOld⟩
      ⟨(coarseCandidate input profile hSame).oldSourceEdge
          (data.sourceEdge profile.first.1.1.1 sheet),
        ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ hOld⟩ := by
  let candidate := coarseCandidate input profile hSame
  let vertex := candidate.datum.sourceEndpoint (oldVertex target wall) sheet
  refine ⟨?_, vertex, coarse_background_new_incident_left input profile hSame sheet,
    coarse_background_doubled_incident_left input profile hSame sheet, ?_⟩
  · intro hEqual
    have hTargets := congrArg
      (fun edge : NonDanglingEdge candidate.datum ↦ edge.1.1.1) hEqual
    have hLabels := (occurrenceEquiv target wall candidate.right).injective hTargets
    cases hLabels
  · exact nonDanglingValency_eq_two_of_card_two_of_survives candidate.datum
      (coarseCandidate_valid input profile hSame).1 vertex
      (candidate.newSourceEdge sheet)
      (coarse_background_new_incident_left input profile hSame sheet)
      ((coarse_background_new_survives_iff_doubled input profile hSame sheet
        hSheet).2 hOld)
      (coarse_background_left_card_two input profile hSame sheet hSheet)

theorem fine_background_new_consecutive_largest
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hOld : ¬ IsDangling data (data.sourceEdge (largestTarget input profile) sheet)) :
    Consecutive (fineCandidate input profile hSame).datum
      ⟨(fineCandidate input profile hSame).newSourceEdge sheet,
        (fine_background_new_survives_iff_largest input profile hSame sheet
          hSheet).2 hOld⟩
      ⟨(fineCandidate input profile hSame).oldSourceEdge
          (data.sourceEdge (largestTarget input profile) sheet),
        ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ hOld⟩ := by
  let candidate := fineCandidate input profile hSame
  let vertex := candidate.datum.sourceEndpoint (oldVertex target wall) sheet
  refine ⟨?_, vertex, fine_background_new_incident_left input profile hSame sheet,
    fine_background_largest_incident_left input profile hSame sheet, ?_⟩
  · intro hEqual
    have hTargets := congrArg
      (fun edge : NonDanglingEdge candidate.datum ↦ edge.1.1.1) hEqual
    have hLabels := (occurrenceEquiv target wall candidate.right).injective hTargets
    cases hLabels
  · exact nonDanglingValency_eq_two_of_card_two_of_survives candidate.datum
      (fineCandidate_valid input profile hSame).1 vertex
      (candidate.newSourceEdge sheet)
      (fine_background_new_incident_left input profile hSame sheet)
      ((fine_background_new_survives_iff_largest input profile hSame sheet
        hSheet).2 hOld)
      (fine_background_left_card_two input profile hSame sheet hSheet)

theorem coarse_background_new_stablePath_eq_doubled
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hOld : ¬ IsDangling data (data.sourceEdge profile.first.1.1.1 sheet)) :
    NonDanglingEdge.stablePath
        ⟨(coarseCandidate input profile hSame).newSourceEdge sheet,
          (coarse_background_new_survives_iff_doubled input profile hSame sheet
            hSheet).2 hOld⟩ =
      NonDanglingEdge.stablePath
        ⟨(coarseCandidate input profile hSame).oldSourceEdge
            (data.sourceEdge profile.first.1.1.1 sheet),
          ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ hOld⟩ :=
  stablePath_eq_of_consecutive
    (coarse_background_new_consecutive_doubled input profile hSame sheet hSheet hOld)

theorem fine_background_new_stablePath_eq_largest
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hOld : ¬ IsDangling data (data.sourceEdge (largestTarget input profile) sheet)) :
    NonDanglingEdge.stablePath
        ⟨(fineCandidate input profile hSame).newSourceEdge sheet,
          (fine_background_new_survives_iff_largest input profile hSame sheet
            hSheet).2 hOld⟩ =
      NonDanglingEdge.stablePath
        ⟨(fineCandidate input profile hSame).oldSourceEdge
            (data.sourceEdge (largestTarget input profile) sheet),
          ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ hOld⟩ :=
  stablePath_eq_of_consecutive
    (fine_background_new_consecutive_largest input profile hSame sheet hSheet hOld)

/-- Every surviving background new occurrence of `M⁽¹⁾` has the retained
doubled-direction occurrence as a stable-row representative. -/
theorem coarse_background_new_has_doubled_row
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hNew : ¬ IsDangling (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).newSourceEdge sheet)) :
    ∃ hOld : ¬ IsDangling data (data.sourceEdge profile.first.1.1.1 sheet),
      NonDanglingEdge.stablePath
          ⟨(coarseCandidate input profile hSame).newSourceEdge sheet, hNew⟩ =
        NonDanglingEdge.stablePath
          ⟨(coarseCandidate input profile hSame).oldSourceEdge
              (data.sourceEdge profile.first.1.1.1 sheet),
            ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ hOld⟩ := by
  let hOld := (coarse_background_new_survives_iff_doubled
    input profile hSame sheet hSheet).1 hNew
  refine ⟨hOld, ?_⟩
  simpa only using coarse_background_new_stablePath_eq_doubled
    input profile hSame sheet hSheet hOld

/-- Every surviving background new occurrence of `M⁽²⁾` has the retained
largest-direction occurrence as a stable-row representative. -/
theorem fine_background_new_has_largest_row
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hNew : ¬ IsDangling (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).newSourceEdge sheet)) :
    ∃ hOld : ¬ IsDangling data (data.sourceEdge (largestTarget input profile) sheet),
      NonDanglingEdge.stablePath
          ⟨(fineCandidate input profile hSame).newSourceEdge sheet, hNew⟩ =
        NonDanglingEdge.stablePath
          ⟨(fineCandidate input profile hSame).oldSourceEdge
              (data.sourceEdge (largestTarget input profile) sheet),
            ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ hOld⟩ := by
  let hOld := (fine_background_new_survives_iff_largest
    input profile hSame sheet hSheet).1 hNew
  refine ⟨hOld, ?_⟩
  simpa only using fine_background_new_stablePath_eq_largest
    input profile hSame sheet hSheet hOld

/-! ## Background trivalent endpoints -/

theorem coarse_background_old_incident_right_iff
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (old : data.SourceEdge) :
    Incident (coarseCandidate input profile hSame).datum
        ((coarseCandidate input profile hSame).oldSourceEdge old)
        ((coarseCandidate input profile hSame).datum.sourceEndpoint
          (freshVertex target) sheet) ↔
      Incident data old (data.sourceEndpoint wall sheet) ∧
        old.1.1 ≠ profile.first.1.1.1 := by
  let candidate := coarseCandidate input profile hSame
  let targetEdge : target.edges := old.val.fst
  have hTarget : occurrenceEquiv target wall candidate.right (some targetEdge) ∈
      GluingDatum.incidentEdges (target := graph target wall candidate.right)
        (freshVertex target) ↔
      targetEdge ∈ GluingDatum.incidentEdges wall ∧
        targetEdge ≠ profile.first.1.1.1 := by
    simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rw [occurrenceEquiv_some]
    refine (oldEnds_incident_freshVertex_iff target wall candidate.right
      targetEdge).trans ?_
    change (_ ∧ rightOf profile.first.1.1.1 targetEdge = true) ↔ _
    simp [rightOf]
  rw [incident_iff_target_mem_and_rel, incident_iff_target_mem_and_rel]
  change (_ ∧ (coarsePastedResolution input profile hSame).right.Rel
      ((coarsePastedResolution input profile hSame).right.repr sheet) old.1.2) ↔
    (_ ∧ (data.vertexPartition wall).Rel
      ((data.vertexPartition wall).repr sheet) old.1.2) ∧ _
  simp only [SheetPartition.Rel, SheetPartition.repr_idem]
  change (_ ∧ (coarsePastedResolution input profile hSame).right.Rel sheet old.1.2) ↔
    (_ ∧ (data.vertexPartition wall).Rel sheet old.1.2) ∧ _
  have hRel : (coarsePastedResolution input profile hSame).right.Rel sheet old.1.2 ↔
      (data.vertexPartition wall).Rel sheet old.1.2 := by
    rw [← (coarsePastedResolution input profile hSame).right.mem_block_iff,
      ← (data.vertexPartition wall).mem_block_iff,
      coarse_background_right_block input profile hSame sheet hSheet]
  rw [hRel]
  tauto

theorem fine_background_old_incident_right_iff
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (old : data.SourceEdge) :
    Incident (fineCandidate input profile hSame).datum
        ((fineCandidate input profile hSame).oldSourceEdge old)
        ((fineCandidate input profile hSame).datum.sourceEndpoint
          (freshVertex target) sheet) ↔
      Incident data old (data.sourceEndpoint wall sheet) ∧
        old.1.1 ≠ largestTarget input profile := by
  let candidate := fineCandidate input profile hSame
  let targetEdge : target.edges := old.val.fst
  have hTarget : occurrenceEquiv target wall candidate.right (some targetEdge) ∈
      GluingDatum.incidentEdges (target := graph target wall candidate.right)
        (freshVertex target) ↔
      targetEdge ∈ GluingDatum.incidentEdges wall ∧
        targetEdge ≠ largestTarget input profile := by
    simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rw [occurrenceEquiv_some]
    refine (oldEnds_incident_freshVertex_iff target wall candidate.right
      targetEdge).trans ?_
    change (_ ∧ rightOf (largestTarget input profile) targetEdge = true) ↔ _
    simp [rightOf]
  rw [incident_iff_target_mem_and_rel, incident_iff_target_mem_and_rel]
  change (_ ∧ (finePastedResolution input profile hSame).right.Rel
      ((finePastedResolution input profile hSame).right.repr sheet) old.1.2) ↔
    (_ ∧ (data.vertexPartition wall).Rel
      ((data.vertexPartition wall).repr sheet) old.1.2) ∧ _
  simp only [SheetPartition.Rel, SheetPartition.repr_idem]
  change (_ ∧ (finePastedResolution input profile hSame).right.Rel sheet old.1.2) ↔
    (_ ∧ (data.vertexPartition wall).Rel sheet old.1.2) ∧ _
  have hRel : (finePastedResolution input profile hSame).right.Rel sheet old.1.2 ↔
      (data.vertexPartition wall).Rel sheet old.1.2 := by
    rw [← (finePastedResolution input profile hSame).right.mem_block_iff,
      ← (data.vertexPartition wall).mem_block_iff,
      fine_background_right_block input profile hSame sheet hSheet]
  rw [hRel]
  tauto

theorem coarse_background_new_incident_right
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet other : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hRel : (data.vertexPartition wall).Rel sheet other) :
    Incident (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).newSourceEdge other)
      ((coarseCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) sheet) := by
  let candidate := coarseCandidate input profile hSame
  have hBase : Incident candidate.datum (candidate.newSourceEdge other)
      (candidate.datum.sourceEndpoint (freshVertex target) other) :=
    Or.inr (congrArg Prod.snd (GlobalResolution.sourceEnds_newSourceEdge data wall
      candidate.right (coarsePastedResolution input profile hSame)
      (GlobalAssembly.blockwiseCompatible _ _ _ _ _ candidate.exterior) other))
  have hEndpoint : candidate.datum.sourceEndpoint (freshVertex target) sheet =
      candidate.datum.sourceEndpoint (freshVertex target) other := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (coarsePastedResolution input profile hSame).right.repr sheet =
          (coarsePastedResolution input profile hSame).right.repr other
      apply (coarsePastedResolution input profile hSame).right.mem_block_iff _ _ |>.mp
      rw [coarse_background_right_block input profile hSame sheet hSheet]
      exact (data.vertexPartition wall).mem_block_iff _ _ |>.mpr hRel
  exact hEndpoint.symm ▸ hBase

theorem fine_background_new_incident_right
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet other : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hRel : (data.vertexPartition wall).Rel sheet other) :
    Incident (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).newSourceEdge other)
      ((fineCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) sheet) := by
  let candidate := fineCandidate input profile hSame
  have hBase : Incident candidate.datum (candidate.newSourceEdge other)
      (candidate.datum.sourceEndpoint (freshVertex target) other) :=
    fine_new_incident_right input profile hSame other
  have hEndpoint : candidate.datum.sourceEndpoint (freshVertex target) sheet =
      candidate.datum.sourceEndpoint (freshVertex target) other := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (finePastedResolution input profile hSame).right.repr sheet =
          (finePastedResolution input profile hSame).right.repr other
      apply (finePastedResolution input profile hSame).right.mem_block_iff _ _ |>.mp
      rw [fine_background_right_block input profile hSame sheet hSheet]
      exact (data.vertexPartition wall).mem_block_iff _ _ |>.mpr hRel
  exact hEndpoint.symm ▸ hBase

theorem coarse_background_new_incident_right_rel
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet other : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hIncident : Incident (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).newSourceEdge other)
      ((coarseCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) sheet)) :
    (data.vertexPartition wall).Rel sheet other := by
  have hData := (incident_iff_target_mem_and_rel
    (coarseCandidate input profile hSame).datum _ _).mp hIncident |>.2
  change (coarsePastedResolution input profile hSame).right.Rel
      ((coarsePastedResolution input profile hSame).right.repr sheet)
      ((coarsePastedResolution input profile hSame).newEdge.repr other) at hData
  have hRight : (coarsePastedResolution input profile hSame).right.Rel sheet
      ((coarsePastedResolution input profile hSame).newEdge.repr other) :=
    (coarsePastedResolution input profile hSame).right.rel_repr_right sheet |>.trans hData
  have hWallRepr : (data.vertexPartition wall).Rel sheet
      ((coarsePastedResolution input profile hSame).newEdge.repr other) := by
    rw [← (data.vertexPartition wall).mem_block_iff,
      ← coarse_background_right_block input profile hSame sheet hSheet,
      (coarsePastedResolution input profile hSame).right.mem_block_iff]
    exact hRight
  have hRefines : (coarsePastedResolution input profile hSame).newEdge.Refines
      (data.vertexPartition wall) :=
    (coarsePastedResolution input profile hSame).edge_refines_right.trans
      (LocalResolution.pasteRight_refines (data.vertexPartition wall)
        (coarseCandidate input profile hSame).resolution
        (coarseCandidate input profile hSame).contracts)
  exact hWallRepr.trans (hRefines.rel
    ((coarsePastedResolution input profile hSame).newEdge.rel_repr_left other))

theorem fine_background_new_incident_right_rel
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet other : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hIncident : Incident (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).newSourceEdge other)
      ((fineCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) sheet)) :
    (data.vertexPartition wall).Rel sheet other := by
  have hData := (incident_iff_target_mem_and_rel
    (fineCandidate input profile hSame).datum _ _).mp hIncident |>.2
  change (finePastedResolution input profile hSame).right.Rel
      ((finePastedResolution input profile hSame).right.repr sheet)
      ((finePastedResolution input profile hSame).newEdge.repr other) at hData
  have hRight : (finePastedResolution input profile hSame).right.Rel sheet
      ((finePastedResolution input profile hSame).newEdge.repr other) :=
    (finePastedResolution input profile hSame).right.rel_repr_right sheet |>.trans hData
  have hWallRepr : (data.vertexPartition wall).Rel sheet
      ((finePastedResolution input profile hSame).newEdge.repr other) := by
    rw [← (data.vertexPartition wall).mem_block_iff,
      ← fine_background_right_block input profile hSame sheet hSheet,
      (finePastedResolution input profile hSame).right.mem_block_iff]
    exact hRight
  have hRefines : (finePastedResolution input profile hSame).newEdge.Refines
      (data.vertexPartition wall) :=
    (finePastedResolution input profile hSame).edge_refines_right.trans
      (LocalResolution.pasteRight_refines (data.vertexPartition wall)
        (fineCandidate input profile hSame).resolution
        (fineCandidate input profile hSame).contracts)
  exact hWallRepr.trans (hRefines.rel
    ((finePastedResolution input profile hSame).newEdge.rel_repr_left other))

theorem coarse_background_new_eq_of_doubled_source_eq
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet other : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hEqual : data.sourceEdge profile.first.1.1.1 other =
      data.sourceEdge profile.first.1.1.1 sheet) :
    (coarseCandidate input profile hSame).newSourceEdge other =
      (coarseCandidate input profile hSame).newSourceEdge sheet := by
  have hRepr := congrArg (fun edge : data.SourceEdge ↦ edge.1.2) hEqual
  have hFine : (finePartition input profile).Rel sheet other := hRepr.symm
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (coarsePastedResolution input profile hSame).newEdge.repr other =
        (coarsePastedResolution input profile hSame).newEdge.repr sheet
    symm
    apply (coarsePastedResolution input profile hSame).newEdge.mem_block_iff _ _ |>.mp
    rw [coarse_background_newEdge_block input profile hSame sheet hSheet]
    exact (finePartition input profile).mem_block_iff _ _ |>.mpr hFine

theorem fine_background_new_eq_of_largest_source_eq
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet other : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hEqual : data.sourceEdge (largestTarget input profile) other =
      data.sourceEdge (largestTarget input profile) sheet) :
    (fineCandidate input profile hSame).newSourceEdge other =
      (fineCandidate input profile hSame).newSourceEdge sheet := by
  have hRepr := congrArg (fun edge : data.SourceEdge ↦ edge.1.2) hEqual
  have hLargest : (largestPartition input profile).Rel sheet other := hRepr.symm
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (finePastedResolution input profile hSame).newEdge.repr other =
        (finePastedResolution input profile hSame).newEdge.repr sheet
    symm
    apply (finePastedResolution input profile hSame).newEdge.mem_block_iff _ _ |>.mp
    rw [fine_background_newEdge_block input profile hSame sheet hSheet]
    exact (largestPartition input profile).mem_block_iff _ _ |>.mpr hLargest

/-! ## Retained rows at a background trivalent endpoint

Both Figure 30 members are `W3FourSurvival.BackgroundShape`s.  Away from the
distinguished block each installs its own background direction's fine star
(`coarse_resolution_background`, `fine_resolution_background`, whose
`finePartition` / `largestPartition` *are* `data.edgePartition t₃` /
`data.edgePartition t₄`), and `W3Nd2SourceCandidates.rightOf t` leaves `t`
alone on the retained side (`coarse_right_doubled` /
`coarse_right_eq_false_iff`, `fine_right_largest` / `fine_right_eq_false_iff`).

So the background half of the lift's well-definedness is
`W3FourRowDescent.Background.background_retained_eq_of_consecutive` applied to
the two adapters below: a literal bijection of surviving incidence sets at
every unramified wall block, **for arbitrary old valency**, needing neither
`dangling_no_glue` nor an unramifiedness receipt.  No case split on which
incident target direction the consecutive pair uses is required. -/

/-- An occurrence incident to a wall source vertex has its sheet in the same
wall block. -/
theorem wall_rel_of_incident (sheet : Fin degree) (edge : data.SourceEdge)
    (hIncident : Incident data edge (data.sourceEndpoint wall sheet)) :
    (data.vertexPartition wall).Rel sheet edge.1.2 := by
  have hRel := (incident_iff_target_mem_and_rel data edge _).mp hIncident |>.2
  change (data.vertexPartition wall).Rel
    ((data.vertexPartition wall).repr sheet) edge.1.2 at hRel
  exact (data.vertexPartition wall).rel_repr_right sheet |>.trans hRel

/-- `M⁽¹⁾` away from the distinguished block: the doubled direction `t₃`'s own
fine star. -/
noncomputable def coarseBackgroundShape (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    BackgroundShape data wall where
  candidate := coarseCandidate input profile hSame
  backgroundTarget := profile.first.1.1.1
  target_mem := incident_target_mem input profile.first
  left := coarse_right_doubled input profile hSame
  unique := fun edge hRight ↦
    (coarse_right_eq_false_iff input profile hSame edge).mp hRight
  selected := input.distinguishedBlock.1
  resolution_eq := coarse_resolution_background input profile hSame
  genus_eq := coarseCandidate_sourceGenus input profile hSame

/-- `M⁽²⁾` away from the distinguished block: the largest direction `t₄`'s own
fine star. -/
noncomputable def fineBackgroundShape (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    BackgroundShape data wall where
  candidate := fineCandidate input profile hSame
  backgroundTarget := largestTarget input profile
  target_mem := largestTarget_mem input profile
  left := fine_right_largest input profile hSame
  unique := fun edge hRight ↦
    (fine_right_eq_false_iff input profile hSame edge).mp hRight
  selected := input.distinguishedBlock.1
  resolution_eq := fine_resolution_background input profile hSame
  genus_eq := fineCandidate_sourceGenus input profile hSame

/-! ## The distinguished source vertex is a branch vertex

This is the first place where the nd2 template genuinely changes shape, and it
changes it in the *easy* direction.  `W3Nd2StableLift` has to prove that both
retained selected survivors acquire the selected new occurrence's row, because
in nd2 the distinguished source vertex has surviving valency two and therefore
carries consecutive pairs.  Here the same vertex has surviving valency three
(`W3Nd3StableGraph.source_nonDanglingValency_eq_three`), so **no** consecutive
pair of the source quotient meets it and the selected case of the transport
argument is vacuous. -/

theorem selected_sourceEndpoint_eq (input : W3SourceInput data star)
    (sheet : Fin degree)
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    data.sourceEndpoint wall sheet =
      WallBlock.sourceVertex data wall input.distinguishedBlock :=
  (data.sourceEndpoint_eq_iff wall sheet
    (WallBlock.sourceVertex data wall input.distinguishedBlock)).mpr
    ⟨rfl, hSelected.symm.trans
      ((data.vertexPartition wall).rel_repr_right input.distinguishedBlock.1)⟩

/-- No consecutive pair of the source stable-path quotient meets the
distinguished block's source vertex. -/
theorem selected_nonDanglingValency_ne_two (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    nonDanglingValency data (data.sourceEndpoint wall sheet) ≠ 2 := by
  rw [selected_sourceEndpoint_eq input sheet hSelected,
    source_nonDanglingValency_eq_three input profile]
  omega

/-! ## Stable-row lifts for the two Figure 30 members -/

theorem coarse_stablePath_retained_eq_of_consecutive
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (first second : NonDanglingEdge data)
    (hConsecutive : Consecutive data first second) :
    (retainedEdge (coarseCandidate input profile hSame) input.valid.1 first).stablePath =
      (retainedEdge (coarseCandidate input profile hSame) input.valid.1 second).stablePath := by
  classical
  obtain ⟨hNe, vertex, hFirst, hSecond, hNd⟩ := hConsecutive
  by_cases hAt : vertex.1.1 = wall
  · have hVertex : data.sourceEndpoint wall vertex.1.2 = vertex :=
      (data.sourceEndpoint_eq_iff wall vertex.1.2 vertex).mpr ⟨hAt.symm, rfl⟩
    have hNd' : nonDanglingValency data (data.sourceEndpoint wall vertex.1.2) = 2 := by
      rw [hVertex]; exact hNd
    by_cases hSelected : (data.vertexPartition wall).Rel
        input.distinguishedBlock.1 vertex.1.2
    · exact absurd hNd'
        (selected_nonDanglingValency_ne_two input profile vertex.1.2 hSelected)
    · have hFirst' : Incident data first.1 (data.sourceEndpoint wall vertex.1.2) := by
        rw [hVertex]; exact hFirst
      have hSecond' : Incident data second.1 (data.sourceEndpoint wall vertex.1.2) := by
        rw [hVertex]; exact hSecond
      exact W3FourRowDescent.Background.background_retained_eq_of_consecutive
        (coarseBackgroundShape input profile hSame) input.valid hSelected
        first second hNe hFirst' hSecond' hNd'
  · exact stablePath_eq_of_consecutive (consecutive_retained_of_away
      (coarseCandidate input profile hSame) input.valid
      (coarseCandidate_sourceGenus input profile hSame) first second hNe vertex hAt
      hFirst hSecond hNd)

theorem fine_stablePath_retained_eq_of_consecutive
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (first second : NonDanglingEdge data)
    (hConsecutive : Consecutive data first second) :
    (retainedEdge (fineCandidate input profile hSame) input.valid.1 first).stablePath =
      (retainedEdge (fineCandidate input profile hSame) input.valid.1 second).stablePath := by
  classical
  obtain ⟨hNe, vertex, hFirst, hSecond, hNd⟩ := hConsecutive
  by_cases hAt : vertex.1.1 = wall
  · have hVertex : data.sourceEndpoint wall vertex.1.2 = vertex :=
      (data.sourceEndpoint_eq_iff wall vertex.1.2 vertex).mpr ⟨hAt.symm, rfl⟩
    have hNd' : nonDanglingValency data (data.sourceEndpoint wall vertex.1.2) = 2 := by
      rw [hVertex]; exact hNd
    by_cases hSelected : (data.vertexPartition wall).Rel
        input.distinguishedBlock.1 vertex.1.2
    · exact absurd hNd'
        (selected_nonDanglingValency_ne_two input profile vertex.1.2 hSelected)
    · have hFirst' : Incident data first.1 (data.sourceEndpoint wall vertex.1.2) := by
        rw [hVertex]; exact hFirst
      have hSecond' : Incident data second.1 (data.sourceEndpoint wall vertex.1.2) := by
        rw [hVertex]; exact hSecond
      exact W3FourRowDescent.Background.background_retained_eq_of_consecutive
        (fineBackgroundShape input profile hSame) input.valid hSelected
        first second hNe hFirst' hSecond' hNd'
  · exact stablePath_eq_of_consecutive (consecutive_retained_of_away
      (fineCandidate input profile hSame) input.valid
      (fineCandidate_sourceGenus input profile hSame) first second hNe vertex hAt
      hFirst hSecond hNd)

/-- Transport of source stable rows into `M⁽¹⁾` by retaining an occurrence. -/
noncomputable def coarseStablePathLift
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    StablePath data → StablePath (coarseCandidate input profile hSame).datum :=
  Quot.lift
    (fun edge ↦ (retainedEdge (coarseCandidate input profile hSame)
      input.valid.1 edge).stablePath)
    (coarse_stablePath_retained_eq_of_consecutive input profile hSame)

@[simp] theorem coarseStablePathLift_mk
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge data) :
    coarseStablePathLift input profile hSame edge.stablePath =
      (retainedEdge (coarseCandidate input profile hSame)
        input.valid.1 edge).stablePath := rfl

/-- Transport of source stable rows into `M⁽²⁾` by retaining an occurrence. -/
noncomputable def fineStablePathLift
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    StablePath data → StablePath (fineCandidate input profile hSame).datum :=
  Quot.lift
    (fun edge ↦ (retainedEdge (fineCandidate input profile hSame)
      input.valid.1 edge).stablePath)
    (fine_stablePath_retained_eq_of_consecutive input profile hSame)

@[simp] theorem fineStablePathLift_mk
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge data) :
    fineStablePathLift input profile hSame edge.stablePath =
      (retainedEdge (fineCandidate input profile hSame)
        input.valid.1 edge).stablePath := rfl

/-! ## Selected new occurrences are the two Figure 30 arms -/

/-- `M⁽¹⁾` has one selected new occurrence: its new edge carries the whole
distinguished block. -/
theorem coarse_newSourceEdge_eq_of_selected (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (coarseCandidate input profile hSame).newSourceEdge sheet =
      (coarseCandidate input profile hSame).newSourceEdge profile.first.1.1.2 := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (coarsePastedResolution input profile hSame).newEdge.repr sheet =
      (coarsePastedResolution input profile hSame).newEdge.repr profile.first.1.1.2
    apply (coarsePastedResolution input profile hSame).newEdge.mem_block_iff _ _ |>.mp
    rw [coarse_pasted_newEdge_block_selected input profile hSame sheet hSheet]
    exact (data.vertexPartition wall).mem_block_iff _ _ |>.mpr
      (hSheet.symm.trans (incident_wall_rel input profile.first))

/-- `M⁽²⁾` has exactly two selected new occurrences, one over each block of
the doubled direction. -/
theorem fine_newSourceEdge_eq_of_selected (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (fineCandidate input profile hSame).newSourceEdge sheet =
        (fineCandidate input profile hSame).newSourceEdge profile.first.1.1.2 ∨
      (fineCandidate input profile hSame).newSourceEdge sheet =
        (fineCandidate input profile hSame).newSourceEdge profile.second.1.1.2 := by
  rcases fine_rel_first_or_second input profile hSame sheet hSheet with hFirst | hSecond
  · exact Or.inl (fine_newSourceEdge_eq_of_fine_rel input profile hSame
      profile.first.1.1.2 sheet (incident_wall_rel input profile.first) hFirst)
  · exact Or.inr (fine_newSourceEdge_eq_of_fine_rel input profile hSame
      profile.second.1.1.2 sheet (incident_wall_rel input profile.second) hSecond)

/-! ## Surjectivity of the two lifts -/

theorem coarse_exists_retained_row
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge (coarseCandidate input profile hSame).datum) :
    ∃ old : NonDanglingEdge data,
      (retainedEdge (coarseCandidate input profile hSame)
        input.valid.1 old).stablePath = edge.stablePath := by
  let candidate := coarseCandidate input profile hSame
  rcases nonDanglingEdge_cases candidate input.valid
      (coarseCandidate_sourceGenus input profile hSame) edge with
    ⟨old, rfl⟩ | ⟨sheet, hSurvives, rfl⟩
  · exact ⟨old, rfl⟩
  · by_cases hSelected : (data.vertexPartition wall).Rel
        input.distinguishedBlock.1 sheet
    · refine ⟨⟨profile.largest.1, largest_survives input profile⟩, ?_⟩
      have hEdge : (⟨candidate.newSourceEdge sheet, hSurvives⟩ :
          NonDanglingEdge candidate.datum) = coarseAnchorNew input profile hSame :=
        Subtype.ext (coarse_newSourceEdge_eq_of_selected input profile hSame
          sheet hSelected)
      rw [hEdge]
      exact (coarse_anchor_new_stablePath_eq_largest input profile hSame).symm
    · obtain ⟨hOld, hPath⟩ := coarse_background_new_has_doubled_row
        input profile hSame sheet hSelected hSurvives
      exact ⟨⟨data.sourceEdge profile.first.1.1.1 sheet, hOld⟩, hPath.symm⟩

theorem coarseStablePathLift_surjective
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    Function.Surjective (coarseStablePathLift input profile hSame) := by
  intro path
  induction path using Quot.inductionOn with
  | h edge =>
      obtain ⟨old, hPath⟩ := coarse_exists_retained_row input profile hSame edge
      exact ⟨old.stablePath, hPath⟩

theorem fine_exists_retained_row
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge (fineCandidate input profile hSame).datum) :
    ∃ old : NonDanglingEdge data,
      (retainedEdge (fineCandidate input profile hSame)
        input.valid.1 old).stablePath = edge.stablePath := by
  let candidate := fineCandidate input profile hSame
  rcases nonDanglingEdge_cases candidate input.valid
      (fineCandidate_sourceGenus input profile hSame) edge with
    ⟨old, rfl⟩ | ⟨sheet, hSurvives, rfl⟩
  · exact ⟨old, rfl⟩
  · by_cases hSelected : (data.vertexPartition wall).Rel
        input.distinguishedBlock.1 sheet
    · rcases fine_newSourceEdge_eq_of_selected input profile hSame sheet hSelected with
        hFirst | hSecond
      · refine ⟨⟨profile.first.1, first_survives input profile⟩, ?_⟩
        have hEdge : (⟨candidate.newSourceEdge sheet, hSurvives⟩ :
            NonDanglingEdge candidate.datum) =
              fineNew input profile hSame profile.first.1.1.2
                (incident_wall_rel input profile.first) := Subtype.ext hFirst
        have hRetained : retainedEdge candidate input.valid.1
            ⟨profile.first.1, first_survives input profile⟩ =
              fineRetainedDoubled input profile hSame profile.first.1.1.2
                (incident_wall_rel input profile.first) :=
          Subtype.ext (fineRetainedDoubled_first input profile hSame).symm
        rw [hEdge, hRetained]
        exact (fine_new_stablePath_eq_doubled input profile hSame
          profile.first.1.1.2 (incident_wall_rel input profile.first)).symm
      · refine ⟨⟨profile.second.1, second_survives input profile⟩, ?_⟩
        have hEdge : (⟨candidate.newSourceEdge sheet, hSurvives⟩ :
            NonDanglingEdge candidate.datum) =
              fineNew input profile hSame profile.second.1.1.2
                (incident_wall_rel input profile.second) := Subtype.ext hSecond
        have hRetained : retainedEdge candidate input.valid.1
            ⟨profile.second.1, second_survives input profile⟩ =
              fineRetainedDoubled input profile hSame profile.second.1.1.2
                (incident_wall_rel input profile.second) :=
          Subtype.ext (fineRetainedDoubled_second input profile hSame).symm
        rw [hEdge, hRetained]
        exact (fine_new_stablePath_eq_doubled input profile hSame
          profile.second.1.1.2 (incident_wall_rel input profile.second)).symm
    · obtain ⟨hOld, hPath⟩ := fine_background_new_has_largest_row
        input profile hSame sheet hSelected hSurvives
      exact ⟨⟨data.sourceEdge (largestTarget input profile) sheet, hOld⟩, hPath.symm⟩

theorem fineStablePathLift_surjective
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    Function.Surjective (fineStablePathLift input profile hSame) := by
  intro path
  induction path using Quot.inductionOn with
  | h edge =>
      obtain ⟨old, hPath⟩ := fine_exists_retained_row input profile hSame edge
      exact ⟨old.stablePath, hPath⟩

/-! ## Reverse row transport for `M⁽¹⁾`

The coarse background replaces each old doubled-direction occurrence by the
corresponding new occurrence and retains every other old occurrence.  This is
a literal bijection of surviving incidence sets at every unramified wall
block, for arbitrary old valency. -/

noncomputable def coarseBackgroundReplace
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (old : data.SourceEdge) : (coarseCandidate input profile hSame).datum.SourceEdge :=
  if old.1.1 = profile.first.1.1.1 then
    (coarseCandidate input profile hSame).newSourceEdge old.1.2
  else (coarseCandidate input profile hSame).oldSourceEdge old

theorem coarseBackgroundReplace_of_doubled
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (old : data.SourceEdge) (hTarget : old.1.1 = profile.first.1.1.1) :
    coarseBackgroundReplace input profile hSame old =
      (coarseCandidate input profile hSame).newSourceEdge old.1.2 := by
  rw [coarseBackgroundReplace, if_pos hTarget]

theorem coarseBackgroundReplace_of_ne_doubled
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (old : data.SourceEdge) (hTarget : old.1.1 ≠ profile.first.1.1.1) :
    coarseBackgroundReplace input profile hSame old =
      (coarseCandidate input profile hSame).oldSourceEdge old := by
  rw [coarseBackgroundReplace, if_neg hTarget]

theorem coarseBackgroundReplace_mem_iff
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (old : data.SourceEdge) :
    coarseBackgroundReplace input profile hSame old ∈
        nonDanglingIncident (coarseCandidate input profile hSame).datum
          ((coarseCandidate input profile hSame).datum.sourceEndpoint
            (freshVertex target) sheet) ↔
      old ∈ nonDanglingIncident data (data.sourceEndpoint wall sheet) := by
  classical
  by_cases hTarget : old.1.1 = profile.first.1.1.1
  · rw [coarseBackgroundReplace_of_doubled input profile hSame old hTarget]
    constructor
    · intro hMem
      obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
      have hWall := coarse_background_new_incident_right_rel
        input profile hSame sheet old.1.2 hSheet hIncident
      have hOldSheet : ¬(data.vertexPartition wall).Rel
          input.distinguishedBlock.1 old.1.2 := by
        intro hDist
        exact hSheet (hDist.trans hWall.symm)
      have hOldSurvives : ¬ IsDangling data old := by
        have hCanonical : data.sourceEdge profile.first.1.1.1 old.1.2 = old := by
          rw [← hTarget]
          exact GluingDatum.sourceEdge_self data old
        have := (coarse_background_new_survives_iff_doubled
          input profile hSame old.1.2 hOldSheet).mp hSurvives
        simpa [hCanonical] using this
      have hOldIncident : Incident data old (data.sourceEndpoint wall sheet) := by
        apply (incident_iff_target_mem_and_rel data old _).mpr
        refine ⟨hTarget ▸ incident_target_mem input profile.first, ?_⟩
        change (data.vertexPartition wall).Rel
          ((data.vertexPartition wall).repr sheet) old.1.2
        exact (data.vertexPartition wall).rel_repr_left sheet |>.trans hWall
      exact (mem_nonDanglingIncident _ _ _).mpr ⟨hOldSurvives, hOldIncident⟩
    · intro hMem
      obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
      have hWall : (data.vertexPartition wall).Rel sheet old.1.2 :=
        wall_rel_of_incident sheet old hIncident
      have hOldSheet : ¬(data.vertexPartition wall).Rel
          input.distinguishedBlock.1 old.1.2 := by
        intro hDist
        exact hSheet (hDist.trans hWall.symm)
      have hCanonical : data.sourceEdge profile.first.1.1.1 old.1.2 = old := by
        rw [← hTarget]
        exact GluingDatum.sourceEdge_self data old
      apply (mem_nonDanglingIncident _ _ _).mpr
      refine ⟨(coarse_background_new_survives_iff_doubled input profile hSame
        old.1.2 hOldSheet).mpr (by simpa [hCanonical] using hSurvives), ?_⟩
      exact coarse_background_new_incident_right input profile hSame sheet old.1.2
        hSheet hWall
  · rw [coarseBackgroundReplace_of_ne_doubled input profile hSame old hTarget]
    rw [mem_nonDanglingIncident, mem_nonDanglingIncident]
    rw [coarse_old_isDangling_iff input profile hSame old,
      coarse_background_old_incident_right_iff input profile hSame sheet hSheet old]
    tauto

theorem coarseBackgroundReplace_surjective_on_incidence
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (edge : (coarseCandidate input profile hSame).datum.SourceEdge)
    (hEdge : edge ∈ nonDanglingIncident (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) sheet)) :
    ∃ old : data.SourceEdge,
      old ∈ nonDanglingIncident data (data.sourceEndpoint wall sheet) ∧
        coarseBackgroundReplace input profile hSame old = edge := by
  classical
  let candidate := coarseCandidate input profile hSame
  obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hEdge
  rcases sourceEdge_cases candidate edge with ⟨old, rfl⟩ | ⟨other, rfl⟩
  · have hOldTarget :=
      (coarse_background_old_incident_right_iff input profile hSame sheet hSheet
        old).mp hIncident |>.2
    have hReplace := coarseBackgroundReplace_of_ne_doubled input profile hSame old
      hOldTarget
    refine ⟨old, (coarseBackgroundReplace_mem_iff input profile hSame sheet hSheet
      old).mp ?_, hReplace⟩
    rw [hReplace]
    exact hEdge
  · have hWall := coarse_background_new_incident_right_rel
      input profile hSame sheet other hSheet hIncident
    let old := data.sourceEdge profile.first.1.1.1 other
    have hOldSheet : ¬(data.vertexPartition wall).Rel
        input.distinguishedBlock.1 old.1.2 := by
      intro hDist
      apply hSheet
      have hFineWall := (fine_refines_wall input profile).rel
        ((finePartition input profile).rel_repr_left other)
      exact hDist.trans (hFineWall.trans hWall.symm)
    have hOldTarget : old.1.1 = profile.first.1.1.1 := rfl
    refine ⟨old, (coarseBackgroundReplace_mem_iff input profile hSame sheet hSheet
      old).mp ?_, ?_⟩
    · rw [coarseBackgroundReplace_of_doubled input profile hSame old hOldTarget]
      have hEq : candidate.newSourceEdge old.1.2 = candidate.newSourceEdge other := by
        apply coarse_background_new_eq_of_doubled_source_eq input profile hSame
          other old.1.2
        · intro hDist
          exact hSheet (hDist.trans hWall.symm)
        · exact GluingDatum.sourceEdge_self data old
      rw [hEq]
      exact hEdge
    · rw [coarseBackgroundReplace_of_doubled input profile hSame old hOldTarget]
      apply coarse_background_new_eq_of_doubled_source_eq input profile hSame
        other old.1.2
      · intro hDist
        exact hSheet (hDist.trans hWall.symm)
      · exact GluingDatum.sourceEdge_self data old

theorem coarseBackgroundReplace_injective_on_incidence
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (first second : data.SourceEdge)
    (hFirst : first ∈ nonDanglingIncident data (data.sourceEndpoint wall sheet))
    (_hSecond : second ∈ nonDanglingIncident data (data.sourceEndpoint wall sheet))
    (hEqual : coarseBackgroundReplace input profile hSame first =
      coarseBackgroundReplace input profile hSame second) : first = second := by
  classical
  let candidate := coarseCandidate input profile hSame
  by_cases hFirstTarget : first.1.1 = profile.first.1.1.1
  · by_cases hSecondTarget : second.1.1 = profile.first.1.1.1
    · rw [coarseBackgroundReplace_of_doubled input profile hSame first hFirstTarget,
        coarseBackgroundReplace_of_doubled input profile hSame second hSecondTarget]
        at hEqual
      have hNewRepr := congrArg
        (fun edge : candidate.datum.SourceEdge ↦ edge.1.2) hEqual
      have hFirstIncident := (mem_nonDanglingIncident _ _ _).mp hFirst |>.2
      have hFirstWall : (data.vertexPartition wall).Rel sheet first.1.2 :=
        wall_rel_of_incident sheet first hFirstIncident
      have hFirstSheet : ¬(data.vertexPartition wall).Rel
          input.distinguishedBlock.1 first.1.2 := by
        intro hDist
        exact hSheet (hDist.trans hFirstWall.symm)
      have hNewRel : (coarsePastedResolution input profile hSame).newEdge.Rel
          first.1.2 second.1.2 := hNewRepr
      have hFineRel : (finePartition input profile).Rel first.1.2 second.1.2 := by
        apply (finePartition input profile).mem_block_iff _ _ |>.mp
        rw [← coarse_background_newEdge_block input profile hSame first.1.2 hFirstSheet,
          (coarsePastedResolution input profile hSame).newEdge.mem_block_iff]
        exact hNewRel
      apply Subtype.ext
      apply Prod.ext
      · exact hFirstTarget.trans hSecondTarget.symm
      · have hFirstRepr : (finePartition input profile).repr first.1.2 = first.1.2 := by
          change (data.edgePartition profile.first.1.1.1).repr first.1.2 = first.1.2
          rw [← hFirstTarget]
          exact first.2
        have hSecondRepr : (finePartition input profile).repr second.1.2 =
            second.1.2 := by
          change (data.edgePartition profile.first.1.1.1).repr second.1.2 = second.1.2
          rw [← hSecondTarget]
          exact second.2
        exact hFirstRepr.symm.trans (hFineRel.trans hSecondRepr)
    · rw [coarseBackgroundReplace_of_doubled input profile hSame first hFirstTarget,
        coarseBackgroundReplace_of_ne_doubled input profile hSame second hSecondTarget]
        at hEqual
      have hLabels := (occurrenceEquiv target wall candidate.right).injective
        (congrArg (fun edge : candidate.datum.SourceEdge ↦ edge.1.1) hEqual)
      cases hLabels
  · by_cases hSecondTarget : second.1.1 = profile.first.1.1.1
    · rw [coarseBackgroundReplace_of_ne_doubled input profile hSame first hFirstTarget,
        coarseBackgroundReplace_of_doubled input profile hSame second hSecondTarget]
        at hEqual
      have hLabels := (occurrenceEquiv target wall candidate.right).injective
        (congrArg (fun edge : candidate.datum.SourceEdge ↦ edge.1.1) hEqual)
      cases hLabels
    · rw [coarseBackgroundReplace_of_ne_doubled input profile hSame first hFirstTarget,
        coarseBackgroundReplace_of_ne_doubled input profile hSame second hSecondTarget]
        at hEqual
      exact ResolutionCut.oldSourceEdge_injective candidate hEqual

theorem coarse_nonDanglingIncident_background_image
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    nonDanglingIncident (coarseCandidate input profile hSame).datum
        ((coarseCandidate input profile hSame).datum.sourceEndpoint
          (freshVertex target) sheet) =
      (nonDanglingIncident data (data.sourceEndpoint wall sheet)).image
        (coarseBackgroundReplace input profile hSame) := by
  classical
  ext edge
  constructor
  · intro hEdge
    obtain ⟨old, hOld, hReplace⟩ :=
      coarseBackgroundReplace_surjective_on_incidence input profile hSame sheet hSheet
        edge hEdge
    exact Finset.mem_image.mpr ⟨old, hOld, hReplace⟩
  · intro hEdge
    obtain ⟨old, hOld, rfl⟩ := Finset.mem_image.mp hEdge
    exact (coarseBackgroundReplace_mem_iff input profile hSame sheet hSheet old).mpr hOld

/-- Surviving valency is preserved at every coarse background fresh vertex,
whatever the old valency there. -/
theorem coarse_nonDanglingValency_background
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    nonDanglingValency (coarseCandidate input profile hSame).datum
        ((coarseCandidate input profile hSame).datum.sourceEndpoint
          (freshVertex target) sheet) =
      nonDanglingValency data (data.sourceEndpoint wall sheet) := by
  classical
  rw [← card_nonDanglingIncident,
    coarse_nonDanglingIncident_background_image input profile hSame sheet hSheet,
    Finset.card_image_iff.mpr]
  · rw [card_nonDanglingIncident]
  · intro first hFirst second hSecond hEqual
    exact coarseBackgroundReplace_injective_on_incidence input profile hSame sheet
      hSheet first second hFirst hSecond hEqual

/-! ## Reverse row transport for `M⁽²⁾`

The fine background replaces each old largest-direction occurrence by the
corresponding new occurrence and retains every other old occurrence.  This is
a literal bijection of surviving incidence sets at every unramified wall
block, for arbitrary old valency. -/

noncomputable def fineBackgroundReplace
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (old : data.SourceEdge) : (fineCandidate input profile hSame).datum.SourceEdge :=
  if old.1.1 = (largestTarget input profile) then
    (fineCandidate input profile hSame).newSourceEdge old.1.2
  else (fineCandidate input profile hSame).oldSourceEdge old

theorem fineBackgroundReplace_of_largest
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (old : data.SourceEdge) (hTarget : old.1.1 = (largestTarget input profile)) :
    fineBackgroundReplace input profile hSame old =
      (fineCandidate input profile hSame).newSourceEdge old.1.2 := by
  rw [fineBackgroundReplace, if_pos hTarget]

theorem fineBackgroundReplace_of_ne_largest
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (old : data.SourceEdge) (hTarget : old.1.1 ≠ (largestTarget input profile)) :
    fineBackgroundReplace input profile hSame old =
      (fineCandidate input profile hSame).oldSourceEdge old := by
  rw [fineBackgroundReplace, if_neg hTarget]

theorem fineBackgroundReplace_mem_iff
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (old : data.SourceEdge) :
    fineBackgroundReplace input profile hSame old ∈
        nonDanglingIncident (fineCandidate input profile hSame).datum
          ((fineCandidate input profile hSame).datum.sourceEndpoint
            (freshVertex target) sheet) ↔
      old ∈ nonDanglingIncident data (data.sourceEndpoint wall sheet) := by
  classical
  by_cases hTarget : old.1.1 = (largestTarget input profile)
  · rw [fineBackgroundReplace_of_largest input profile hSame old hTarget]
    constructor
    · intro hMem
      obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
      have hWall := fine_background_new_incident_right_rel
        input profile hSame sheet old.1.2 hSheet hIncident
      have hOldSheet : ¬(data.vertexPartition wall).Rel
          input.distinguishedBlock.1 old.1.2 := by
        intro hDist
        exact hSheet (hDist.trans hWall.symm)
      have hOldSurvives : ¬ IsDangling data old := by
        have hCanonical : data.sourceEdge (largestTarget input profile) old.1.2 = old := by
          rw [← hTarget]
          exact GluingDatum.sourceEdge_self data old
        have := (fine_background_new_survives_iff_largest
          input profile hSame old.1.2 hOldSheet).mp hSurvives
        simpa [hCanonical] using this
      have hOldIncident : Incident data old (data.sourceEndpoint wall sheet) := by
        apply (incident_iff_target_mem_and_rel data old _).mpr
        refine ⟨hTarget ▸ (largestTarget_mem input profile), ?_⟩
        change (data.vertexPartition wall).Rel
          ((data.vertexPartition wall).repr sheet) old.1.2
        exact (data.vertexPartition wall).rel_repr_left sheet |>.trans hWall
      exact (mem_nonDanglingIncident _ _ _).mpr ⟨hOldSurvives, hOldIncident⟩
    · intro hMem
      obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
      have hWall : (data.vertexPartition wall).Rel sheet old.1.2 :=
        wall_rel_of_incident sheet old hIncident
      have hOldSheet : ¬(data.vertexPartition wall).Rel
          input.distinguishedBlock.1 old.1.2 := by
        intro hDist
        exact hSheet (hDist.trans hWall.symm)
      have hCanonical : data.sourceEdge (largestTarget input profile) old.1.2 = old := by
        rw [← hTarget]
        exact GluingDatum.sourceEdge_self data old
      apply (mem_nonDanglingIncident _ _ _).mpr
      refine ⟨(fine_background_new_survives_iff_largest input profile hSame
        old.1.2 hOldSheet).mpr (by simpa [hCanonical] using hSurvives), ?_⟩
      exact fine_background_new_incident_right input profile hSame sheet old.1.2
        hSheet hWall
  · rw [fineBackgroundReplace_of_ne_largest input profile hSame old hTarget]
    rw [mem_nonDanglingIncident, mem_nonDanglingIncident]
    rw [fine_old_isDangling_iff input profile hSame old,
      fine_background_old_incident_right_iff input profile hSame sheet hSheet old]
    tauto

theorem fineBackgroundReplace_surjective_on_incidence
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (edge : (fineCandidate input profile hSame).datum.SourceEdge)
    (hEdge : edge ∈ nonDanglingIncident (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) sheet)) :
    ∃ old : data.SourceEdge,
      old ∈ nonDanglingIncident data (data.sourceEndpoint wall sheet) ∧
        fineBackgroundReplace input profile hSame old = edge := by
  classical
  let candidate := fineCandidate input profile hSame
  obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hEdge
  rcases sourceEdge_cases candidate edge with ⟨old, rfl⟩ | ⟨other, rfl⟩
  · have hOldTarget :=
      (fine_background_old_incident_right_iff input profile hSame sheet hSheet
        old).mp hIncident |>.2
    have hReplace := fineBackgroundReplace_of_ne_largest input profile hSame old
      hOldTarget
    refine ⟨old, (fineBackgroundReplace_mem_iff input profile hSame sheet hSheet
      old).mp ?_, hReplace⟩
    rw [hReplace]
    exact hEdge
  · have hWall := fine_background_new_incident_right_rel
      input profile hSame sheet other hSheet hIncident
    let old := data.sourceEdge (largestTarget input profile) other
    have hOldSheet : ¬(data.vertexPartition wall).Rel
        input.distinguishedBlock.1 old.1.2 := by
      intro hDist
      apply hSheet
      have hFineWall := (largest_refines_wall input profile).rel
        ((largestPartition input profile).rel_repr_left other)
      exact hDist.trans (hFineWall.trans hWall.symm)
    have hOldTarget : old.1.1 = (largestTarget input profile) := rfl
    refine ⟨old, (fineBackgroundReplace_mem_iff input profile hSame sheet hSheet
      old).mp ?_, ?_⟩
    · rw [fineBackgroundReplace_of_largest input profile hSame old hOldTarget]
      have hEq : candidate.newSourceEdge old.1.2 = candidate.newSourceEdge other := by
        apply fine_background_new_eq_of_largest_source_eq input profile hSame
          other old.1.2
        · intro hDist
          exact hSheet (hDist.trans hWall.symm)
        · exact GluingDatum.sourceEdge_self data old
      rw [hEq]
      exact hEdge
    · rw [fineBackgroundReplace_of_largest input profile hSame old hOldTarget]
      apply fine_background_new_eq_of_largest_source_eq input profile hSame
        other old.1.2
      · intro hDist
        exact hSheet (hDist.trans hWall.symm)
      · exact GluingDatum.sourceEdge_self data old

theorem fineBackgroundReplace_injective_on_incidence
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (first second : data.SourceEdge)
    (hFirst : first ∈ nonDanglingIncident data (data.sourceEndpoint wall sheet))
    (_hSecond : second ∈ nonDanglingIncident data (data.sourceEndpoint wall sheet))
    (hEqual : fineBackgroundReplace input profile hSame first =
      fineBackgroundReplace input profile hSame second) : first = second := by
  classical
  let candidate := fineCandidate input profile hSame
  by_cases hFirstTarget : first.1.1 = (largestTarget input profile)
  · by_cases hSecondTarget : second.1.1 = (largestTarget input profile)
    · rw [fineBackgroundReplace_of_largest input profile hSame first hFirstTarget,
        fineBackgroundReplace_of_largest input profile hSame second hSecondTarget]
        at hEqual
      have hNewRepr := congrArg
        (fun edge : candidate.datum.SourceEdge ↦ edge.1.2) hEqual
      have hFirstIncident := (mem_nonDanglingIncident _ _ _).mp hFirst |>.2
      have hFirstWall : (data.vertexPartition wall).Rel sheet first.1.2 :=
        wall_rel_of_incident sheet first hFirstIncident
      have hFirstSheet : ¬(data.vertexPartition wall).Rel
          input.distinguishedBlock.1 first.1.2 := by
        intro hDist
        exact hSheet (hDist.trans hFirstWall.symm)
      have hNewRel : (finePastedResolution input profile hSame).newEdge.Rel
          first.1.2 second.1.2 := hNewRepr
      have hFineRel : (largestPartition input profile).Rel first.1.2 second.1.2 := by
        apply (largestPartition input profile).mem_block_iff _ _ |>.mp
        rw [← fine_background_newEdge_block input profile hSame first.1.2 hFirstSheet,
          (finePastedResolution input profile hSame).newEdge.mem_block_iff]
        exact hNewRel
      apply Subtype.ext
      apply Prod.ext
      · exact hFirstTarget.trans hSecondTarget.symm
      · have hFirstRepr : (largestPartition input profile).repr first.1.2 = first.1.2 := by
          change (data.edgePartition (largestTarget input profile)).repr first.1.2 = first.1.2
          rw [← hFirstTarget]
          exact first.2
        have hSecondRepr : (largestPartition input profile).repr second.1.2 =
            second.1.2 := by
          change (data.edgePartition (largestTarget input profile)).repr second.1.2 = second.1.2
          rw [← hSecondTarget]
          exact second.2
        exact hFirstRepr.symm.trans (hFineRel.trans hSecondRepr)
    · rw [fineBackgroundReplace_of_largest input profile hSame first hFirstTarget,
        fineBackgroundReplace_of_ne_largest input profile hSame second hSecondTarget]
        at hEqual
      have hLabels := (occurrenceEquiv target wall candidate.right).injective
        (congrArg (fun edge : candidate.datum.SourceEdge ↦ edge.1.1) hEqual)
      cases hLabels
  · by_cases hSecondTarget : second.1.1 = (largestTarget input profile)
    · rw [fineBackgroundReplace_of_ne_largest input profile hSame first hFirstTarget,
        fineBackgroundReplace_of_largest input profile hSame second hSecondTarget]
        at hEqual
      have hLabels := (occurrenceEquiv target wall candidate.right).injective
        (congrArg (fun edge : candidate.datum.SourceEdge ↦ edge.1.1) hEqual)
      cases hLabels
    · rw [fineBackgroundReplace_of_ne_largest input profile hSame first hFirstTarget,
        fineBackgroundReplace_of_ne_largest input profile hSame second hSecondTarget]
        at hEqual
      exact ResolutionCut.oldSourceEdge_injective candidate hEqual

theorem fine_nonDanglingIncident_background_image
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    nonDanglingIncident (fineCandidate input profile hSame).datum
        ((fineCandidate input profile hSame).datum.sourceEndpoint
          (freshVertex target) sheet) =
      (nonDanglingIncident data (data.sourceEndpoint wall sheet)).image
        (fineBackgroundReplace input profile hSame) := by
  classical
  ext edge
  constructor
  · intro hEdge
    obtain ⟨old, hOld, hReplace⟩ :=
      fineBackgroundReplace_surjective_on_incidence input profile hSame sheet hSheet
        edge hEdge
    exact Finset.mem_image.mpr ⟨old, hOld, hReplace⟩
  · intro hEdge
    obtain ⟨old, hOld, rfl⟩ := Finset.mem_image.mp hEdge
    exact (fineBackgroundReplace_mem_iff input profile hSame sheet hSheet old).mpr hOld

/-- Surviving valency is preserved at every fine background fresh vertex,
whatever the old valency there. -/
theorem fine_nonDanglingValency_background
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    nonDanglingValency (fineCandidate input profile hSame).datum
        ((fineCandidate input profile hSame).datum.sourceEndpoint
          (freshVertex target) sheet) =
      nonDanglingValency data (data.sourceEndpoint wall sheet) := by
  classical
  rw [← card_nonDanglingIncident,
    fine_nonDanglingIncident_background_image input profile hSame sheet hSheet,
    Finset.card_image_iff.mpr]
  · rw [card_nonDanglingIncident]
  · intro first hFirst second hSecond hEqual
    exact fineBackgroundReplace_injective_on_incidence input profile hSame sheet
      hSheet first second hFirst hSecond hEqual

/-! ### The reverse row assignment of `M⁽¹⁾`

A retained occurrence returns to its literal preimage.  A new occurrence over
a background sheet returns to the doubled-direction occurrence through that
sheet; over a selected sheet it returns to the retained largest direction `e₄`,
which is the row `coarse_anchor_new_stablePath_eq_largest` gives it. -/

noncomputable def coarseNewOldSourceEdge
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (sheet : Fin degree) : data.SourceEdge :=
  if (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet then
    profile.largest.1
  else data.sourceEdge profile.first.1.1.1 sheet

theorem coarseNewOldSourceEdge_survives
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).newSourceEdge sheet)) :
    ¬ IsDangling data (coarseNewOldSourceEdge input profile sheet) := by
  classical
  by_cases hSelected : (data.vertexPartition wall).Rel
      input.distinguishedBlock.1 sheet
  · rw [coarseNewOldSourceEdge, if_pos hSelected]
    exact largest_survives input profile
  · rw [coarseNewOldSourceEdge, if_neg hSelected]
    exact (coarse_background_new_survives_iff_doubled input profile hSame sheet
      hSelected).mp hSurvives

noncomputable def coarseNewOldEdge
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).newSourceEdge sheet)) :
    NonDanglingEdge data :=
  ⟨coarseNewOldSourceEdge input profile sheet,
    coarseNewOldSourceEdge_survives input profile hSame sheet hSurvives⟩

theorem coarse_new_representation
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge (coarseCandidate input profile hSame).datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge (coarseCandidate input profile hSame) input.valid.1 old = edge) :
    ∃ sheet : Fin degree, ∃ hSurvives : ¬ IsDangling
        (coarseCandidate input profile hSame).datum
        ((coarseCandidate input profile hSame).newSourceEdge sheet),
      edge = ⟨(coarseCandidate input profile hSame).newSourceEdge sheet,
        hSurvives⟩ := by
  rcases nonDanglingEdge_cases (coarseCandidate input profile hSame) input.valid
      (coarseCandidate_sourceGenus input profile hSame) edge with
    ⟨old, hOld⟩ | ⟨sheet, hSurvives, hNew⟩
  · exact (hNotOld ⟨old, hOld.symm⟩).elim
  · exact ⟨sheet, hSurvives, hNew⟩

noncomputable def coarseNewSheet
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge (coarseCandidate input profile hSame).datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge (coarseCandidate input profile hSame) input.valid.1 old = edge) :
    Fin degree :=
  (coarse_new_representation input profile hSame edge hNotOld).choose

theorem coarseNewSheet_survives
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge (coarseCandidate input profile hSame).datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge (coarseCandidate input profile hSame) input.valid.1 old = edge) :
    ¬ IsDangling (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).newSourceEdge
        (coarseNewSheet input profile hSame edge hNotOld)) :=
  (coarse_new_representation input profile hSame edge hNotOld).choose_spec.choose

theorem coarseNewSheet_spec
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge (coarseCandidate input profile hSame).datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge (coarseCandidate input profile hSame) input.valid.1 old = edge) :
    edge = ⟨(coarseCandidate input profile hSame).newSourceEdge
        (coarseNewSheet input profile hSame edge hNotOld),
      coarseNewSheet_survives input profile hSame edge hNotOld⟩ :=
  (coarse_new_representation input profile hSame edge hNotOld).choose_spec.choose_spec

noncomputable def coarseRowOfEdge
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge (coarseCandidate input profile hSame).datum) :
    StablePath data := by
  classical
  exact if hOld : ∃ old : NonDanglingEdge data,
      retainedEdge (coarseCandidate input profile hSame) input.valid.1 old = edge then
    (Classical.choose hOld).stablePath
  else
    (coarseNewOldEdge input profile hSame
      (coarseNewSheet input profile hSame edge hOld)
      (coarseNewSheet_survives input profile hSame edge hOld)).stablePath

@[simp] theorem coarseRowOfEdge_retained
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (old : NonDanglingEdge data) :
    coarseRowOfEdge input profile hSame
      (retainedEdge (coarseCandidate input profile hSame) input.valid.1 old) =
        old.stablePath := by
  classical
  have hOld : ∃ other : NonDanglingEdge data,
      retainedEdge (coarseCandidate input profile hSame) input.valid.1 other =
        retainedEdge (coarseCandidate input profile hSame) input.valid.1 old :=
    ⟨old, rfl⟩
  rw [coarseRowOfEdge, dif_pos hOld]
  exact congrArg NonDanglingEdge.stablePath
    (retainedEdge_injective _ input.valid.1 (Classical.choose_spec hOld))

theorem coarseRowOfEdge_not_retained
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge (coarseCandidate input profile hSame).datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge (coarseCandidate input profile hSame) input.valid.1 old = edge) :
    coarseRowOfEdge input profile hSame edge =
      (coarseNewOldEdge input profile hSame
        (coarseNewSheet input profile hSame edge hNotOld)
        (coarseNewSheet_survives input profile hSame edge hNotOld)).stablePath := by
  classical
  exact dif_neg hNotOld

theorem coarseNewOldEdge_of_selected
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).newSourceEdge sheet))
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    coarseNewOldEdge input profile hSame sheet hSurvives =
      ⟨profile.largest.1, largest_survives input profile⟩ := by
  apply Subtype.ext
  change coarseNewOldSourceEdge input profile sheet = profile.largest.1
  rw [coarseNewOldSourceEdge, if_pos hSelected]

theorem coarseNewOldEdge_of_background
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).newSourceEdge sheet))
    (hBackground : ¬(data.vertexPartition wall).Rel
      input.distinguishedBlock.1 sheet) :
    (coarseNewOldEdge input profile hSame sheet hSurvives).1 =
      data.sourceEdge profile.first.1.1.1 sheet := by
  change coarseNewOldSourceEdge input profile sheet =
    data.sourceEdge profile.first.1.1.1 sheet
  rw [coarseNewOldSourceEdge, if_neg hBackground]

theorem coarseRowOfEdge_incident_background
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (edge : NonDanglingEdge (coarseCandidate input profile hSame).datum)
    (hIncident : Incident (coarseCandidate input profile hSame).datum edge.1
      ((coarseCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) sheet)) :
    ∃ old : NonDanglingEdge data,
      Incident data old.1 (data.sourceEndpoint wall sheet) ∧
        coarseBackgroundReplace input profile hSame old.1 = edge.1 ∧
          coarseRowOfEdge input profile hSame edge = old.stablePath := by
  classical
  let candidate := coarseCandidate input profile hSame
  by_cases hOld : ∃ old : NonDanglingEdge data,
      retainedEdge candidate input.valid.1 old = edge
  · let old := Classical.choose hOld
    have hEq := Classical.choose_spec hOld
    have hCandidateIncident : Incident candidate.datum (candidate.oldSourceEdge old.1)
        (candidate.datum.sourceEndpoint (freshVertex target) sheet) := by
      rw [show candidate.oldSourceEdge old.1 = edge.1 from congrArg Subtype.val hEq]
      exact hIncident
    obtain ⟨hOldIncident, hTarget⟩ :=
      (coarse_background_old_incident_right_iff input profile hSame sheet hBackground
        old.1).mp hCandidateIncident
    refine ⟨old, hOldIncident, ?_, ?_⟩
    · rw [coarseBackgroundReplace_of_ne_doubled input profile hSame old.1 hTarget]
      exact congrArg Subtype.val hEq
    · rw [coarseRowOfEdge, dif_pos hOld]
  · let newSheet := coarseNewSheet input profile hSame edge hOld
    let hNewSurvives := coarseNewSheet_survives input profile hSame edge hOld
    have hEdge := coarseNewSheet_spec input profile hSame edge hOld
    have hNewIncident : Incident candidate.datum (candidate.newSourceEdge newSheet)
        (candidate.datum.sourceEndpoint (freshVertex target) sheet) := by
      rw [← show edge.1 = candidate.newSourceEdge newSheet from
        congrArg Subtype.val hEdge]
      exact hIncident
    have hWall := coarse_background_new_incident_right_rel input profile hSame
      sheet newSheet hBackground hNewIncident
    have hNewBackground : ¬(data.vertexPartition wall).Rel
        input.distinguishedBlock.1 newSheet := by
      intro hSelected
      exact hBackground (hSelected.trans hWall.symm)
    let old := coarseNewOldEdge input profile hSame newSheet hNewSurvives
    have hOldValue : old.1 = data.sourceEdge profile.first.1.1.1 newSheet :=
      coarseNewOldEdge_of_background input profile hSame newSheet hNewSurvives
        hNewBackground
    have hOldIncident : Incident data old.1 (data.sourceEndpoint wall sheet) := by
      rw [hOldValue]
      have hBase := incident_sourceEdge_sourceEndpoint data wall
        profile.first.1.1.1 (incident_target_mem input profile.first) newSheet
      have hEndpoint : data.sourceEndpoint wall sheet =
          data.sourceEndpoint wall newSheet := by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact hWall
      rw [hEndpoint]
      exact hBase
    refine ⟨old, hOldIncident, ?_, ?_⟩
    · rw [coarseBackgroundReplace_of_doubled input profile hSame old.1 (by
        rw [hOldValue]
        rfl)]
      rw [hOldValue]
      have hReplace : candidate.newSourceEdge
          (data.sourceEdge profile.first.1.1.1 newSheet).1.2 =
          candidate.newSourceEdge newSheet := by
        apply coarse_background_new_eq_of_doubled_source_eq input profile hSame
          newSheet (data.sourceEdge profile.first.1.1.1 newSheet).1.2
        · exact hNewBackground
        · exact GluingDatum.sourceEdge_self data
            (data.sourceEdge profile.first.1.1.1 newSheet)
      exact hReplace.trans (congrArg Subtype.val hEdge).symm
    · exact (coarseRowOfEdge_not_retained input profile hSame edge hOld).trans
        (congrArg NonDanglingEdge.stablePath rfl)

theorem coarseRowOfEdge_eq_background
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (first second : NonDanglingEdge (coarseCandidate input profile hSame).datum)
    (hNe : first ≠ second)
    (hFirst : Incident (coarseCandidate input profile hSame).datum first.1
      ((coarseCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) sheet))
    (hSecond : Incident (coarseCandidate input profile hSame).datum second.1
      ((coarseCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) sheet))
    (hValency : nonDanglingValency (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) sheet) = 2) :
    coarseRowOfEdge input profile hSame first =
      coarseRowOfEdge input profile hSame second := by
  obtain ⟨oldFirst, hOldFirst, hReplaceFirst, hFirstRow⟩ :=
    coarseRowOfEdge_incident_background input profile hSame sheet hBackground first hFirst
  obtain ⟨oldSecond, hOldSecond, hReplaceSecond, hSecondRow⟩ :=
    coarseRowOfEdge_incident_background input profile hSame sheet hBackground second hSecond
  have hOldValency : nonDanglingValency data (data.sourceEndpoint wall sheet) = 2 :=
    (coarse_nonDanglingValency_background input profile hSame sheet
      hBackground).symm.trans hValency
  have hOldNe : oldFirst ≠ oldSecond := by
    intro hEqual
    apply hNe
    apply Subtype.ext
    rw [← hReplaceFirst, ← hReplaceSecond, hEqual]
  exact hFirstRow.trans ((stablePath_eq_of_consecutive
    ⟨hOldNe, data.sourceEndpoint wall sheet, hOldFirst, hOldSecond,
      hOldValency⟩).trans hSecondRow.symm)

theorem coarseRowOfEdge_new_selected
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hSurvives : ¬ IsDangling (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).newSourceEdge sheet)) :
    coarseRowOfEdge input profile hSame
        ⟨(coarseCandidate input profile hSame).newSourceEdge sheet, hSurvives⟩ =
      NonDanglingEdge.stablePath ⟨profile.largest.1, largest_survives input profile⟩ := by
  classical
  let candidate := coarseCandidate input profile hSame
  let edge : NonDanglingEdge candidate.datum :=
    ⟨candidate.newSourceEdge sheet, hSurvives⟩
  have hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge candidate input.valid.1 old = edge := by
    rintro ⟨old, hEqual⟩
    have hLabels := (occurrenceEquiv target wall candidate.right).injective
      (congrArg (fun occurrence : NonDanglingEdge candidate.datum ↦ occurrence.1.1.1)
        hEqual)
    cases hLabels
  let chosen := coarseNewSheet input profile hSame edge hNotOld
  let hChosenSurvives := coarseNewSheet_survives input profile hSame edge hNotOld
  have hSpec := coarseNewSheet_spec input profile hSame edge hNotOld
  have hNewEqual : candidate.newSourceEdge sheet = candidate.newSourceEdge chosen :=
    congrArg Subtype.val hSpec
  have hNewRel : (coarsePastedResolution input profile hSame).newEdge.Rel sheet chosen :=
    congrArg (fun item : candidate.datum.SourceEdge ↦ item.1.2) hNewEqual
  have hWallRel : (data.vertexPartition wall).Rel sheet chosen :=
    (coarsePastedResolution input profile hSame).edge_refines_left.trans
      (LocalResolution.pasteLeft_refines (data.vertexPartition wall)
        candidate.resolution candidate.contracts) |>.rel hNewRel
  have hChosenSelected : (data.vertexPartition wall).Rel
      input.distinguishedBlock.1 chosen := hSelected.trans hWallRel
  calc
    coarseRowOfEdge input profile hSame edge =
        (coarseNewOldEdge input profile hSame chosen hChosenSurvives).stablePath :=
      coarseRowOfEdge_not_retained input profile hSame edge hNotOld
    _ = NonDanglingEdge.stablePath ⟨profile.largest.1, largest_survives input profile⟩ :=
      congrArg NonDanglingEdge.stablePath
        (coarseNewOldEdge_of_selected input profile hSame chosen hChosenSurvives
          hChosenSelected)

theorem coarseRowOfEdge_new_background
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hSurvives : ¬ IsDangling (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).newSourceEdge sheet)) :
    coarseRowOfEdge input profile hSame
        ⟨(coarseCandidate input profile hSame).newSourceEdge sheet, hSurvives⟩ =
      NonDanglingEdge.stablePath
        ⟨data.sourceEdge profile.first.1.1.1 sheet,
          (coarse_background_new_survives_iff_doubled input profile hSame sheet
            hBackground).mp hSurvives⟩ := by
  classical
  let candidate := coarseCandidate input profile hSame
  let edge : NonDanglingEdge candidate.datum :=
    ⟨candidate.newSourceEdge sheet, hSurvives⟩
  have hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge candidate input.valid.1 old = edge := by
    rintro ⟨old, hEqual⟩
    have hLabels := (occurrenceEquiv target wall candidate.right).injective
      (congrArg (fun occurrence : NonDanglingEdge candidate.datum ↦ occurrence.1.1.1)
        hEqual)
    cases hLabels
  let chosen := coarseNewSheet input profile hSame edge hNotOld
  let hChosenSurvives := coarseNewSheet_survives input profile hSame edge hNotOld
  have hSpec := coarseNewSheet_spec input profile hSame edge hNotOld
  have hNewEqual : candidate.newSourceEdge sheet = candidate.newSourceEdge chosen :=
    congrArg Subtype.val hSpec
  have hNewRel : (coarsePastedResolution input profile hSame).newEdge.Rel sheet chosen :=
    congrArg (fun item : candidate.datum.SourceEdge ↦ item.1.2) hNewEqual
  have hWallRel : (data.vertexPartition wall).Rel sheet chosen :=
    (coarsePastedResolution input profile hSame).edge_refines_left.trans
      (LocalResolution.pasteLeft_refines (data.vertexPartition wall)
        candidate.resolution candidate.contracts) |>.rel hNewRel
  have hChosenBackground : ¬(data.vertexPartition wall).Rel
      input.distinguishedBlock.1 chosen := by
    intro hSelected
    exact hBackground (hSelected.trans hWallRel.symm)
  have hOldEqual : data.sourceEdge profile.first.1.1.1 chosen =
      data.sourceEdge profile.first.1.1.1 sheet := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hFineRel : (finePartition input profile).Rel sheet chosen := by
          apply (finePartition input profile).mem_block_iff _ _ |>.mp
          rw [← coarse_background_newEdge_block input profile hSame sheet hBackground,
            (coarsePastedResolution input profile hSame).newEdge.mem_block_iff]
          exact hNewRel
      calc
        (data.sourceEdge profile.first.1.1.1 chosen).1.2 =
            (finePartition input profile).repr chosen := rfl
        _ = (finePartition input profile).repr sheet := hFineRel.symm
        _ = (data.sourceEdge profile.first.1.1.1 sheet).1.2 := rfl
  have hChosenOld := coarseNewOldEdge_of_background input profile hSame chosen
    hChosenSurvives hChosenBackground
  calc
    coarseRowOfEdge input profile hSame edge =
        (coarseNewOldEdge input profile hSame chosen hChosenSurvives).stablePath :=
      coarseRowOfEdge_not_retained input profile hSame edge hNotOld
    _ = NonDanglingEdge.stablePath
        ⟨data.sourceEdge profile.first.1.1.1 sheet,
          (coarse_background_new_survives_iff_doubled input profile hSame sheet
            hBackground).mp hSurvives⟩ := by
      apply congrArg NonDanglingEdge.stablePath
      apply Subtype.ext
      exact hChosenOld.trans hOldEqual

/-- Every row assigned at the trivalent selected endpoint of `M⁽¹⁾` is the
retained largest direction's old row. -/
theorem coarseRowOfEdge_incident_fresh_selected
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (edge : NonDanglingEdge (coarseCandidate input profile hSame).datum)
    (hIncident : Incident (coarseCandidate input profile hSame).datum edge.1
      ((coarseCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) sheet)) :
    coarseRowOfEdge input profile hSame edge =
      NonDanglingEdge.stablePath ⟨profile.largest.1, largest_survives input profile⟩ := by
  classical
  let candidate := coarseCandidate input profile hSame
  have hEndpoint : candidate.datum.sourceEndpoint (freshVertex target) sheet =
      candidate.datum.sourceEndpoint (freshVertex target) profile.first.1.1.2 := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (coarsePastedResolution input profile hSame).right.repr sheet =
          (coarsePastedResolution input profile hSame).right.repr profile.first.1.1.2
      apply (coarsePastedResolution input profile hSame).right.mem_block_iff _ _ |>.mp
      rw [coarse_pasted_right_block_selected input profile hSame sheet hSelected]
      exact (data.vertexPartition wall).mem_block_iff _ _ |>.mpr
        (hSelected.symm.trans (incident_wall_rel input profile.first))
  have hAtAnchor : edge.1 ∈ nonDanglingIncident candidate.datum
      (candidate.datum.sourceEndpoint (freshVertex target) profile.first.1.1.2) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hEndpoint.symm ▸ hIncident⟩
  rw [coarse_nonDanglingIncident_right input profile hSame] at hAtAnchor
  rcases Finset.mem_insert.mp hAtAnchor with hNew | hLargest
  · have hEdge : edge = coarseAnchorNew input profile hSame := Subtype.ext hNew
    rw [hEdge]
    exact coarseRowOfEdge_new_selected input profile hSame profile.first.1.1.2
      (incident_wall_rel input profile.first)
      (coarse_anchor_new_survives input profile hSame)
  · have hOld := Finset.mem_singleton.mp hLargest
    let retainedLargest : NonDanglingEdge candidate.datum :=
      retainedEdge candidate input.valid.1 ⟨profile.largest.1, largest_survives input profile⟩
    have hEdge : edge = retainedLargest := Subtype.ext hOld
    rw [hEdge]
    simpa only [candidate, retainedLargest] using
      (coarseRowOfEdge_retained input profile hSame
        (⟨profile.largest.1, largest_survives input profile⟩ : NonDanglingEdge data))

/-- The divalent selected endpoint of `M⁽¹⁾` is a branch vertex, so no
consecutive pair of the resolved quotient meets it. -/
theorem coarse_left_selected_valency_eq_three
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    nonDanglingValency (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) sheet) = 3 := by
  rw [← coarse_left_endpoint_eq_of_wall_rel input profile hSame profile.first.1.1.2
    sheet (incident_wall_rel input profile.first)
    ((incident_wall_rel input profile.first).symm.trans hSelected)]
  exact coarse_left_nonDanglingValency_eq_three input profile hSame

theorem coarseRowOfEdge_incident_left_background
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (edge : NonDanglingEdge (coarseCandidate input profile hSame).datum)
    (hIncident : Incident (coarseCandidate input profile hSame).datum edge.1
      ((coarseCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) sheet)) :
    ∃ hOld : ¬ IsDangling data (data.sourceEdge profile.first.1.1.1 sheet),
      coarseRowOfEdge input profile hSame edge = NonDanglingEdge.stablePath
        ⟨data.sourceEdge profile.first.1.1.1 sheet, hOld⟩ := by
  classical
  let candidate := coarseCandidate input profile hSame
  rcases nonDanglingEdge_cases candidate input.valid
      (coarseCandidate_sourceGenus input profile hSame) edge with
    ⟨old, rfl⟩ | ⟨other, hSurvives, rfl⟩
  · have hData := (incident_iff_target_mem_and_rel candidate.datum
      (candidate.oldSourceEdge old.1)
      (candidate.datum.sourceEndpoint (oldVertex target wall) sheet)).mp hIncident
    simp only [GluingDatum.sourceEndpoint, candidate.oldSourceEdge_target,
      candidate.oldSourceEdge_sheet] at hData
    have hVertex : candidate.datum.vertexPartition (oldVertex target wall) =
        (coarsePastedResolution input profile hSame).left :=
      GlobalResolution.expandedVertexPartition_old_wall data wall _
    rw [hVertex] at hData
    have hTarget := hData.1
    rw [coarse_left_target_incident_pair input profile hSame] at hTarget
    rcases Finset.mem_insert.mp hTarget with hNew | hDoubled
    · have hLabels := (occurrenceEquiv target wall candidate.right).injective hNew
      cases hLabels
    · have hOldTarget : old.1.1.1 = profile.first.1.1.1 :=
        Option.some.inj ((occurrenceEquiv target wall candidate.right).injective
          (Finset.mem_singleton.mp hDoubled))
      have hRel := hData.2
      have hLeftRel : (coarsePastedResolution input profile hSame).left.Rel
          sheet old.1.1.2 := by
        change (coarsePastedResolution input profile hSame).left.Rel
          ((coarsePastedResolution input profile hSame).left.repr sheet)
          old.1.1.2 at hRel
        exact (coarsePastedResolution input profile hSame).left.rel_repr_right sheet
          |>.trans hRel
      have hFineRel : (finePartition input profile).Rel sheet old.1.1.2 := by
        apply (finePartition input profile).mem_block_iff _ _ |>.mp
        rw [← coarse_background_left_block input profile hSame sheet hBackground,
          (coarsePastedResolution input profile hSame).left.mem_block_iff]
        exact hLeftRel
      have hOldEq : old.1 = data.sourceEdge profile.first.1.1.1 sheet := by
        apply Subtype.ext
        apply Prod.ext
        · exact hOldTarget
        · calc
            old.1.1.2 = (finePartition input profile).repr old.1.1.2 := by
              have hCanonical := old.1.2
              change (data.edgePartition old.1.1.1).repr old.1.1.2 =
                old.1.1.2 at hCanonical
              rw [hOldTarget] at hCanonical
              exact hCanonical.symm
            _ = (finePartition input profile).repr sheet := hFineRel.symm
            _ = (data.sourceEdge profile.first.1.1.1 sheet).1.2 := rfl
      refine ⟨hOldEq ▸ old.2, ?_⟩
      rw [coarseRowOfEdge_retained]
      exact congrArg NonDanglingEdge.stablePath (Subtype.ext hOldEq)
  · have hData := (incident_iff_target_mem_and_rel candidate.datum
      (candidate.newSourceEdge other)
      (candidate.datum.sourceEndpoint (oldVertex target wall) sheet)).mp hIncident
    simp only [GluingDatum.sourceEndpoint, candidate.newSourceEdge_target,
      candidate.newSourceEdge_sheet] at hData
    have hVertex : candidate.datum.vertexPartition (oldVertex target wall) =
        (coarsePastedResolution input profile hSame).left :=
      GlobalResolution.expandedVertexPartition_old_wall data wall _
    rw [hVertex] at hData
    have hRel := hData.2
    have hLeftRel : (coarsePastedResolution input profile hSame).left.Rel sheet
        ((coarsePastedResolution input profile hSame).newEdge.repr other) := by
      change (coarsePastedResolution input profile hSame).left.Rel
        ((coarsePastedResolution input profile hSame).left.repr sheet)
        ((coarsePastedResolution input profile hSame).newEdge.repr other) at hRel
      exact (coarsePastedResolution input profile hSame).left.rel_repr_right sheet
        |>.trans hRel
    have hLeftRelOther : (coarsePastedResolution input profile hSame).left.Rel
        sheet other :=
      hLeftRel.trans ((coarsePastedResolution input profile hSame).edge_refines_left.rel
        ((coarsePastedResolution input profile hSame).newEdge.rel_repr_left other))
    have hWallOther : (data.vertexPartition wall).Rel sheet other :=
      (LocalResolution.pasteLeft_refines (data.vertexPartition wall)
        candidate.resolution candidate.contracts).rel hLeftRelOther
    have hOtherBackground : ¬(data.vertexPartition wall).Rel
        input.distinguishedBlock.1 other := by
      intro hSelected
      exact hBackground (hSelected.trans hWallOther.symm)
    have hNewRel : (coarsePastedResolution input profile hSame).newEdge.Rel
        sheet other := by
      apply (coarsePastedResolution input profile hSame).newEdge.mem_block_iff _ _ |>.mp
      rw [coarse_background_newEdge_block input profile hSame sheet hBackground]
      apply (finePartition input profile).mem_block_iff _ _ |>.mpr
      apply (finePartition input profile).mem_block_iff _ _ |>.mp
      rw [← coarse_background_left_block input profile hSame sheet hBackground,
        (coarsePastedResolution input profile hSame).left.mem_block_iff]
      exact hLeftRelOther
    have hFineRel : (finePartition input profile).Rel sheet other := by
      apply (finePartition input profile).mem_block_iff _ _ |>.mp
      rw [← coarse_background_newEdge_block input profile hSame sheet hBackground,
        (coarsePastedResolution input profile hSame).newEdge.mem_block_iff]
      exact hNewRel
    have hOldEq : data.sourceEdge profile.first.1.1.1 other =
        data.sourceEdge profile.first.1.1.1 sheet := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact hFineRel.symm
    have hOldOther := (coarse_background_new_survives_iff_doubled input profile hSame
      other hOtherBackground).mp hSurvives
    have hOldSheet : ¬ IsDangling data
        (data.sourceEdge profile.first.1.1.1 sheet) := hOldEq.symm ▸ hOldOther
    refine ⟨hOldSheet, ?_⟩
    exact (coarseRowOfEdge_new_background input profile hSame other hOtherBackground
      hSurvives).trans (congrArg NonDanglingEdge.stablePath (Subtype.ext hOldEq))

theorem coarseRowOfEdge_eq_away
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (vertex : data.SourceVertex) (hAway : vertex.1.1 ≠ wall)
    (first second : NonDanglingEdge (coarseCandidate input profile hSame).datum)
    (hFirst : Incident (coarseCandidate input profile hSame).datum first.1
      (retainedVertex (coarseCandidate input profile hSame) vertex))
    (hSecond : Incident (coarseCandidate input profile hSame).datum second.1
      (retainedVertex (coarseCandidate input profile hSame) vertex))
    (hValency : nonDanglingValency (coarseCandidate input profile hSame).datum
      (retainedVertex (coarseCandidate input profile hSame) vertex) = 2) :
    coarseRowOfEdge input profile hSame first =
      coarseRowOfEdge input profile hSame second := by
  classical
  let candidate := coarseCandidate input profile hSame
  have hGenus := coarseCandidate_sourceGenus input profile hSame
  rcases nonDanglingEdge_cases candidate input.valid hGenus first with
      ⟨oldFirst, rfl⟩ | ⟨sheet, hSurvives, rfl⟩
  · rcases nonDanglingEdge_cases candidate input.valid hGenus second with
        ⟨oldSecond, rfl⟩ | ⟨sheet, hSurvives, rfl⟩
    · rw [coarseRowOfEdge_retained, coarseRowOfEdge_retained]
      by_cases hEqual : oldFirst = oldSecond
      · exact congrArg NonDanglingEdge.stablePath hEqual
      · exact stablePath_eq_of_consecutive ⟨hEqual, vertex,
          (incident_oldSourceEdge_iff candidate vertex hAway oldFirst.1).mp hFirst,
          (incident_oldSourceEdge_iff candidate vertex hAway oldSecond.1).mp hSecond,
          (nonDanglingValency_retainedVertex candidate input.valid hGenus vertex
            hAway).symm.trans hValency⟩
    · exact (not_incident_newSourceEdge candidate vertex hAway sheet hSecond).elim
  · exact (not_incident_newSourceEdge candidate vertex hAway sheet hFirst).elim

/-- The coarse reverse assignment is constant on every consecutive pair.  Its
selected divalent case is *vacuous*, because that endpoint is a branch vertex
in `M⁽¹⁾`. -/
theorem coarseRowOfEdge_eq_of_consecutive
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (first second : NonDanglingEdge (coarseCandidate input profile hSame).datum)
    (hConsecutive : Consecutive (coarseCandidate input profile hSame).datum first second) :
    coarseRowOfEdge input profile hSame first =
      coarseRowOfEdge input profile hSame second := by
  classical
  let candidate := coarseCandidate input profile hSame
  obtain ⟨hNe, vertex, hFirst, hSecond, hValency⟩ := hConsecutive
  have hSelf : candidate.datum.sourceEndpoint vertex.1.1 vertex.1.2 = vertex :=
    (candidate.datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨rfl, rfl⟩
  cases hTarget : vertex.1.1 with
  | inl place =>
      by_cases hAt : place = wall
      · subst place
        have hEndpoint : candidate.datum.sourceEndpoint (oldVertex target wall)
            vertex.1.2 = vertex :=
          (congrArg (fun place ↦ candidate.datum.sourceEndpoint place vertex.1.2)
            hTarget.symm).trans hSelf
        rw [← hEndpoint] at hFirst hSecond hValency
        by_cases hSelected : (data.vertexPartition wall).Rel
            input.distinguishedBlock.1 vertex.1.2
        · rw [coarse_left_selected_valency_eq_three input profile hSame vertex.1.2
            hSelected] at hValency
          exact absurd hValency (by omega)
        · obtain ⟨hOldFirst, hFirstRow⟩ :=
            coarseRowOfEdge_incident_left_background input profile hSame _ hSelected
              first hFirst
          obtain ⟨hOldSecond, hSecondRow⟩ :=
            coarseRowOfEdge_incident_left_background input profile hSame _ hSelected
              second hSecond
          exact hFirstRow.trans hSecondRow.symm
      · obtain ⟨old, hOld, hVertex⟩ :=
          exists_retainedVertex_of_target candidate vertex place hAt hTarget
        rw [← hVertex] at hFirst hSecond hValency
        exact coarseRowOfEdge_eq_away input profile hSame old (hOld ▸ hAt) first second
          hFirst hSecond hValency
  | inr point =>
      cases point
      have hEndpoint : candidate.datum.sourceEndpoint (freshVertex target)
          vertex.1.2 = vertex :=
        (congrArg (fun place ↦ candidate.datum.sourceEndpoint place vertex.1.2)
          hTarget.symm).trans hSelf
      rw [← hEndpoint] at hFirst hSecond hValency
      by_cases hSelected : (data.vertexPartition wall).Rel
          input.distinguishedBlock.1 vertex.1.2
      · exact (coarseRowOfEdge_incident_fresh_selected input profile hSame _ hSelected
          first hFirst).trans (coarseRowOfEdge_incident_fresh_selected input profile
            hSame _ hSelected second hSecond).symm
      · exact coarseRowOfEdge_eq_background input profile hSame _ hSelected first second
          hNe hFirst hSecond hValency

/-- The explicit reverse row assignment of `M⁽¹⁾` descends through the
stable-path quotient. -/
noncomputable def coarseStablePathDescend
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    StablePath (coarseCandidate input profile hSame).datum → StablePath data :=
  Quot.lift (coarseRowOfEdge input profile hSame)
    (coarseRowOfEdge_eq_of_consecutive input profile hSame)

@[simp] theorem coarseStablePathDescend_mk
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge (coarseCandidate input profile hSame).datum) :
    coarseStablePathDescend input profile hSame edge.stablePath =
      coarseRowOfEdge input profile hSame edge := rfl

theorem coarseStablePathDescend_lift
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath data) :
    coarseStablePathDescend input profile hSame
      (coarseStablePathLift input profile hSame path) = path := by
  induction path using Quot.inductionOn with
  | h edge => exact coarseRowOfEdge_retained input profile hSame edge

theorem coarseStablePathLift_injective
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    Function.Injective (coarseStablePathLift input profile hSame) :=
  Function.LeftInverse.injective (coarseStablePathDescend_lift input profile hSame)

/-- **The stable rows of `M⁽¹⁾` are the source's, via retention.** -/
noncomputable def coarseStablePathEquiv
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    StablePath data ≃ StablePath (coarseCandidate input profile hSame).datum :=
  Equiv.ofBijective (coarseStablePathLift input profile hSame)
    ⟨coarseStablePathLift_injective input profile hSame,
      coarseStablePathLift_surjective input profile hSame⟩

@[simp] theorem coarseStablePathEquiv_mk
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge data) :
    coarseStablePathEquiv input profile hSame edge.stablePath =
      (retainedEdge (coarseCandidate input profile hSame)
        input.valid.1 edge).stablePath := rfl

/-! ### The reverse row assignment of `M⁽²⁾`

A retained occurrence returns to its literal preimage.  A new occurrence over
a background sheet returns to the largest-direction occurrence through that
sheet; over a selected sheet it returns to the doubled-direction occurrence
through that sheet, which is the literal `e₂` or `e₃` according to which block
of `A₀` the sheet lies in — exactly the row `fine_new_stablePath_eq_doubled`
gives it.  This is the one place where `M⁽²⁾` needs a genuinely two-valued
selected assignment where `M⁽¹⁾` needs a constant one. -/

noncomputable def fineNewOldSourceEdge
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (sheet : Fin degree) : data.SourceEdge :=
  if (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet then
    data.sourceEdge profile.first.1.1.1 sheet
  else data.sourceEdge (largestTarget input profile) sheet

theorem fineNewOldSourceEdge_survives
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).newSourceEdge sheet)) :
    ¬ IsDangling data (fineNewOldSourceEdge input profile sheet) := by
  classical
  by_cases hSelected : (data.vertexPartition wall).Rel
      input.distinguishedBlock.1 sheet
  · rw [fineNewOldSourceEdge, if_pos hSelected]
    exact doubled_sourceEdge_survives input profile hSame sheet hSelected
  · rw [fineNewOldSourceEdge, if_neg hSelected]
    exact (fine_background_new_survives_iff_largest input profile hSame sheet
      hSelected).mp hSurvives

noncomputable def fineNewOldEdge
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).newSourceEdge sheet)) :
    NonDanglingEdge data :=
  ⟨fineNewOldSourceEdge input profile sheet,
    fineNewOldSourceEdge_survives input profile hSame sheet hSurvives⟩

theorem fine_new_representation
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge (fineCandidate input profile hSame).datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge (fineCandidate input profile hSame) input.valid.1 old = edge) :
    ∃ sheet : Fin degree, ∃ hSurvives : ¬ IsDangling
        (fineCandidate input profile hSame).datum
        ((fineCandidate input profile hSame).newSourceEdge sheet),
      edge = ⟨(fineCandidate input profile hSame).newSourceEdge sheet,
        hSurvives⟩ := by
  rcases nonDanglingEdge_cases (fineCandidate input profile hSame) input.valid
      (fineCandidate_sourceGenus input profile hSame) edge with
    ⟨old, hOld⟩ | ⟨sheet, hSurvives, hNew⟩
  · exact (hNotOld ⟨old, hOld.symm⟩).elim
  · exact ⟨sheet, hSurvives, hNew⟩

noncomputable def fineNewSheet
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge (fineCandidate input profile hSame).datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge (fineCandidate input profile hSame) input.valid.1 old = edge) :
    Fin degree :=
  (fine_new_representation input profile hSame edge hNotOld).choose

theorem fineNewSheet_survives
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge (fineCandidate input profile hSame).datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge (fineCandidate input profile hSame) input.valid.1 old = edge) :
    ¬ IsDangling (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).newSourceEdge
        (fineNewSheet input profile hSame edge hNotOld)) :=
  (fine_new_representation input profile hSame edge hNotOld).choose_spec.choose

theorem fineNewSheet_spec
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge (fineCandidate input profile hSame).datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge (fineCandidate input profile hSame) input.valid.1 old = edge) :
    edge = ⟨(fineCandidate input profile hSame).newSourceEdge
        (fineNewSheet input profile hSame edge hNotOld),
      fineNewSheet_survives input profile hSame edge hNotOld⟩ :=
  (fine_new_representation input profile hSame edge hNotOld).choose_spec.choose_spec

noncomputable def fineRowOfEdge
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge (fineCandidate input profile hSame).datum) :
    StablePath data := by
  classical
  exact if hOld : ∃ old : NonDanglingEdge data,
      retainedEdge (fineCandidate input profile hSame) input.valid.1 old = edge then
    (Classical.choose hOld).stablePath
  else
    (fineNewOldEdge input profile hSame
      (fineNewSheet input profile hSame edge hOld)
      (fineNewSheet_survives input profile hSame edge hOld)).stablePath

@[simp] theorem fineRowOfEdge_retained
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (old : NonDanglingEdge data) :
    fineRowOfEdge input profile hSame
      (retainedEdge (fineCandidate input profile hSame) input.valid.1 old) =
        old.stablePath := by
  classical
  have hOld : ∃ other : NonDanglingEdge data,
      retainedEdge (fineCandidate input profile hSame) input.valid.1 other =
        retainedEdge (fineCandidate input profile hSame) input.valid.1 old :=
    ⟨old, rfl⟩
  rw [fineRowOfEdge, dif_pos hOld]
  exact congrArg NonDanglingEdge.stablePath
    (retainedEdge_injective _ input.valid.1 (Classical.choose_spec hOld))

theorem fineRowOfEdge_not_retained
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge (fineCandidate input profile hSame).datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge (fineCandidate input profile hSame) input.valid.1 old = edge) :
    fineRowOfEdge input profile hSame edge =
      (fineNewOldEdge input profile hSame
        (fineNewSheet input profile hSame edge hNotOld)
        (fineNewSheet_survives input profile hSame edge hNotOld)).stablePath := by
  classical
  exact dif_neg hNotOld

theorem fineNewOldEdge_of_selected
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).newSourceEdge sheet))
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (fineNewOldEdge input profile hSame sheet hSurvives).1 =
      data.sourceEdge profile.first.1.1.1 sheet := by
  change fineNewOldSourceEdge input profile sheet =
    data.sourceEdge profile.first.1.1.1 sheet
  rw [fineNewOldSourceEdge, if_pos hSelected]

theorem fineNewOldEdge_of_background
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).newSourceEdge sheet))
    (hBackground : ¬(data.vertexPartition wall).Rel
      input.distinguishedBlock.1 sheet) :
    (fineNewOldEdge input profile hSame sheet hSurvives).1 =
      data.sourceEdge (largestTarget input profile) sheet := by
  change fineNewOldSourceEdge input profile sheet =
    data.sourceEdge (largestTarget input profile) sheet
  rw [fineNewOldSourceEdge, if_neg hBackground]

theorem fineRowOfEdge_incident_background
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (edge : NonDanglingEdge (fineCandidate input profile hSame).datum)
    (hIncident : Incident (fineCandidate input profile hSame).datum edge.1
      ((fineCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) sheet)) :
    ∃ old : NonDanglingEdge data,
      Incident data old.1 (data.sourceEndpoint wall sheet) ∧
        fineBackgroundReplace input profile hSame old.1 = edge.1 ∧
          fineRowOfEdge input profile hSame edge = old.stablePath := by
  classical
  let candidate := fineCandidate input profile hSame
  by_cases hOld : ∃ old : NonDanglingEdge data,
      retainedEdge candidate input.valid.1 old = edge
  · let old := Classical.choose hOld
    have hEq := Classical.choose_spec hOld
    have hCandidateIncident : Incident candidate.datum (candidate.oldSourceEdge old.1)
        (candidate.datum.sourceEndpoint (freshVertex target) sheet) := by
      rw [show candidate.oldSourceEdge old.1 = edge.1 from congrArg Subtype.val hEq]
      exact hIncident
    obtain ⟨hOldIncident, hTarget⟩ :=
      (fine_background_old_incident_right_iff input profile hSame sheet hBackground
        old.1).mp hCandidateIncident
    refine ⟨old, hOldIncident, ?_, ?_⟩
    · rw [fineBackgroundReplace_of_ne_largest input profile hSame old.1 hTarget]
      exact congrArg Subtype.val hEq
    · rw [fineRowOfEdge, dif_pos hOld]
  · let newSheet := fineNewSheet input profile hSame edge hOld
    let hNewSurvives := fineNewSheet_survives input profile hSame edge hOld
    have hEdge := fineNewSheet_spec input profile hSame edge hOld
    have hNewIncident : Incident candidate.datum (candidate.newSourceEdge newSheet)
        (candidate.datum.sourceEndpoint (freshVertex target) sheet) := by
      rw [← show edge.1 = candidate.newSourceEdge newSheet from
        congrArg Subtype.val hEdge]
      exact hIncident
    have hWall := fine_background_new_incident_right_rel input profile hSame
      sheet newSheet hBackground hNewIncident
    have hNewBackground : ¬(data.vertexPartition wall).Rel
        input.distinguishedBlock.1 newSheet := by
      intro hSelected
      exact hBackground (hSelected.trans hWall.symm)
    let old := fineNewOldEdge input profile hSame newSheet hNewSurvives
    have hOldValue : old.1 = data.sourceEdge (largestTarget input profile) newSheet :=
      fineNewOldEdge_of_background input profile hSame newSheet hNewSurvives
        hNewBackground
    have hOldIncident : Incident data old.1 (data.sourceEndpoint wall sheet) := by
      rw [hOldValue]
      have hBase := incident_sourceEdge_sourceEndpoint data wall
        (largestTarget input profile) (largestTarget_mem input profile) newSheet
      have hEndpoint : data.sourceEndpoint wall sheet =
          data.sourceEndpoint wall newSheet := by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact hWall
      rw [hEndpoint]
      exact hBase
    refine ⟨old, hOldIncident, ?_, ?_⟩
    · rw [fineBackgroundReplace_of_largest input profile hSame old.1 (by
        rw [hOldValue]
        rfl)]
      rw [hOldValue]
      have hReplace : candidate.newSourceEdge
          (data.sourceEdge (largestTarget input profile) newSheet).1.2 =
          candidate.newSourceEdge newSheet := by
        apply fine_background_new_eq_of_largest_source_eq input profile hSame
          newSheet (data.sourceEdge (largestTarget input profile) newSheet).1.2
        · exact hNewBackground
        · exact GluingDatum.sourceEdge_self data
            (data.sourceEdge (largestTarget input profile) newSheet)
      exact hReplace.trans (congrArg Subtype.val hEdge).symm
    · exact (fineRowOfEdge_not_retained input profile hSame edge hOld).trans
        (congrArg NonDanglingEdge.stablePath rfl)

theorem fineRowOfEdge_eq_background
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (first second : NonDanglingEdge (fineCandidate input profile hSame).datum)
    (hNe : first ≠ second)
    (hFirst : Incident (fineCandidate input profile hSame).datum first.1
      ((fineCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) sheet))
    (hSecond : Incident (fineCandidate input profile hSame).datum second.1
      ((fineCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) sheet))
    (hValency : nonDanglingValency (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) sheet) = 2) :
    fineRowOfEdge input profile hSame first =
      fineRowOfEdge input profile hSame second := by
  obtain ⟨oldFirst, hOldFirst, hReplaceFirst, hFirstRow⟩ :=
    fineRowOfEdge_incident_background input profile hSame sheet hBackground first hFirst
  obtain ⟨oldSecond, hOldSecond, hReplaceSecond, hSecondRow⟩ :=
    fineRowOfEdge_incident_background input profile hSame sheet hBackground second hSecond
  have hOldValency : nonDanglingValency data (data.sourceEndpoint wall sheet) = 2 :=
    (fine_nonDanglingValency_background input profile hSame sheet
      hBackground).symm.trans hValency
  have hOldNe : oldFirst ≠ oldSecond := by
    intro hEqual
    apply hNe
    apply Subtype.ext
    rw [← hReplaceFirst, ← hReplaceSecond, hEqual]
  exact hFirstRow.trans ((stablePath_eq_of_consecutive
    ⟨hOldNe, data.sourceEndpoint wall sheet, hOldFirst, hOldSecond,
      hOldValency⟩).trans hSecondRow.symm)

theorem fineRowOfEdge_new_selected
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hSurvives : ¬ IsDangling (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).newSourceEdge sheet)) :
    fineRowOfEdge input profile hSame
        ⟨(fineCandidate input profile hSame).newSourceEdge sheet, hSurvives⟩ =
      NonDanglingEdge.stablePath
        ⟨data.sourceEdge profile.first.1.1.1 sheet,
          doubled_sourceEdge_survives input profile hSame sheet hSelected⟩ := by
  classical
  let candidate := fineCandidate input profile hSame
  let edge : NonDanglingEdge candidate.datum :=
    ⟨candidate.newSourceEdge sheet, hSurvives⟩
  have hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge candidate input.valid.1 old = edge := by
    rintro ⟨old, hEqual⟩
    have hLabels := (occurrenceEquiv target wall candidate.right).injective
      (congrArg (fun occurrence : NonDanglingEdge candidate.datum ↦ occurrence.1.1.1)
        hEqual)
    cases hLabels
  let chosen := fineNewSheet input profile hSame edge hNotOld
  let hChosenSurvives := fineNewSheet_survives input profile hSame edge hNotOld
  have hSpec := fineNewSheet_spec input profile hSame edge hNotOld
  have hNewEqual : candidate.newSourceEdge sheet = candidate.newSourceEdge chosen :=
    congrArg Subtype.val hSpec
  have hNewRel : (finePastedResolution input profile hSame).newEdge.Rel sheet chosen :=
    congrArg (fun item : candidate.datum.SourceEdge ↦ item.1.2) hNewEqual
  have hWallRel : (data.vertexPartition wall).Rel sheet chosen :=
    (finePastedResolution input profile hSame).edge_refines_left.trans
      (LocalResolution.pasteLeft_refines (data.vertexPartition wall)
        candidate.resolution candidate.contracts) |>.rel hNewRel
  have hChosenSelected : (data.vertexPartition wall).Rel
      input.distinguishedBlock.1 chosen := hSelected.trans hWallRel
  have hFineRel : (finePartition input profile).Rel sheet chosen := by
    apply (finePartition input profile).mem_block_iff _ _ |>.mp
    rw [← fine_pasted_newEdge_block_selected input profile hSame sheet hSelected,
      (finePastedResolution input profile hSame).newEdge.mem_block_iff]
    exact hNewRel
  have hOldEqual : data.sourceEdge profile.first.1.1.1 chosen =
      data.sourceEdge profile.first.1.1.1 sheet := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact hFineRel.symm
  calc
    fineRowOfEdge input profile hSame edge =
        (fineNewOldEdge input profile hSame chosen hChosenSurvives).stablePath :=
      fineRowOfEdge_not_retained input profile hSame edge hNotOld
    _ = NonDanglingEdge.stablePath
        ⟨data.sourceEdge profile.first.1.1.1 sheet,
          doubled_sourceEdge_survives input profile hSame sheet hSelected⟩ := by
      apply congrArg NonDanglingEdge.stablePath
      apply Subtype.ext
      exact (fineNewOldEdge_of_selected input profile hSame chosen hChosenSurvives
        hChosenSelected).trans hOldEqual

theorem fineRowOfEdge_new_background
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hSurvives : ¬ IsDangling (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).newSourceEdge sheet)) :
    fineRowOfEdge input profile hSame
        ⟨(fineCandidate input profile hSame).newSourceEdge sheet, hSurvives⟩ =
      NonDanglingEdge.stablePath
        ⟨data.sourceEdge (largestTarget input profile) sheet,
          (fine_background_new_survives_iff_largest input profile hSame sheet
            hBackground).mp hSurvives⟩ := by
  classical
  let candidate := fineCandidate input profile hSame
  let edge : NonDanglingEdge candidate.datum :=
    ⟨candidate.newSourceEdge sheet, hSurvives⟩
  have hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge candidate input.valid.1 old = edge := by
    rintro ⟨old, hEqual⟩
    have hLabels := (occurrenceEquiv target wall candidate.right).injective
      (congrArg (fun occurrence : NonDanglingEdge candidate.datum ↦ occurrence.1.1.1)
        hEqual)
    cases hLabels
  let chosen := fineNewSheet input profile hSame edge hNotOld
  let hChosenSurvives := fineNewSheet_survives input profile hSame edge hNotOld
  have hSpec := fineNewSheet_spec input profile hSame edge hNotOld
  have hNewEqual : candidate.newSourceEdge sheet = candidate.newSourceEdge chosen :=
    congrArg Subtype.val hSpec
  have hNewRel : (finePastedResolution input profile hSame).newEdge.Rel sheet chosen :=
    congrArg (fun item : candidate.datum.SourceEdge ↦ item.1.2) hNewEqual
  have hWallRel : (data.vertexPartition wall).Rel sheet chosen :=
    (finePastedResolution input profile hSame).edge_refines_left.trans
      (LocalResolution.pasteLeft_refines (data.vertexPartition wall)
        candidate.resolution candidate.contracts) |>.rel hNewRel
  have hChosenBackground : ¬(data.vertexPartition wall).Rel
      input.distinguishedBlock.1 chosen := by
    intro hSelected
    exact hBackground (hSelected.trans hWallRel.symm)
  have hOldEqual : data.sourceEdge (largestTarget input profile) chosen =
      data.sourceEdge (largestTarget input profile) sheet := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hFineRel : (largestPartition input profile).Rel sheet chosen := by
          apply (largestPartition input profile).mem_block_iff _ _ |>.mp
          rw [← fine_background_newEdge_block input profile hSame sheet hBackground,
            (finePastedResolution input profile hSame).newEdge.mem_block_iff]
          exact hNewRel
      calc
        (data.sourceEdge (largestTarget input profile) chosen).1.2 =
            (largestPartition input profile).repr chosen := rfl
        _ = (largestPartition input profile).repr sheet := hFineRel.symm
        _ = (data.sourceEdge (largestTarget input profile) sheet).1.2 := rfl
  have hChosenOld := fineNewOldEdge_of_background input profile hSame chosen
    hChosenSurvives hChosenBackground
  calc
    fineRowOfEdge input profile hSame edge =
        (fineNewOldEdge input profile hSame chosen hChosenSurvives).stablePath :=
      fineRowOfEdge_not_retained input profile hSame edge hNotOld
    _ = NonDanglingEdge.stablePath
        ⟨data.sourceEdge (largestTarget input profile) sheet,
          (fine_background_new_survives_iff_largest input profile hSame sheet
            hBackground).mp hSurvives⟩ := by
      apply congrArg NonDanglingEdge.stablePath
      apply Subtype.ext
      exact hChosenOld.trans hOldEqual

/-- Every row assigned at a trivalent selected endpoint of `M⁽²⁾` is the old
row of the doubled-direction survivor through that sheet: `e₂`'s row above the
first block of `A₀`, `e₃`'s above the second. -/
theorem fineRowOfEdge_incident_fresh_selected
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (edge : NonDanglingEdge (fineCandidate input profile hSame).datum)
    (hIncident : Incident (fineCandidate input profile hSame).datum edge.1
      ((fineCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) sheet)) :
    fineRowOfEdge input profile hSame edge =
      NonDanglingEdge.stablePath
        ⟨data.sourceEdge profile.first.1.1.1 sheet,
          doubled_sourceEdge_survives input profile hSame sheet hSelected⟩ := by
  classical
  let candidate := fineCandidate input profile hSame
  have hMem : edge.1 ∈ nonDanglingIncident candidate.datum
      (candidate.datum.sourceEndpoint (freshVertex target) sheet) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hIncident⟩
  rw [fine_nonDanglingIncident_right input profile hSame sheet hSelected] at hMem
  rcases Finset.mem_insert.mp hMem with hNew | hDoubled
  · have hEdge : edge = ⟨candidate.newSourceEdge sheet,
        fine_new_survives input profile hSame sheet hSelected⟩ := Subtype.ext hNew
    rw [hEdge]
    exact fineRowOfEdge_new_selected input profile hSame sheet hSelected
      (fine_new_survives input profile hSame sheet hSelected)
  · have hOld := Finset.mem_singleton.mp hDoubled
    let retainedDoubled : NonDanglingEdge candidate.datum :=
      retainedEdge candidate input.valid.1
        ⟨data.sourceEdge profile.first.1.1.1 sheet,
          doubled_sourceEdge_survives input profile hSame sheet hSelected⟩
    have hEdge : edge = retainedDoubled := Subtype.ext hOld
    rw [hEdge]
    simpa only [candidate, retainedDoubled] using
      (fineRowOfEdge_retained input profile hSame
        (⟨data.sourceEdge profile.first.1.1.1 sheet,
          doubled_sourceEdge_survives input profile hSame sheet hSelected⟩ :
            NonDanglingEdge data))

/-- The divalent selected endpoint of `M⁽²⁾` is a branch vertex, so no
consecutive pair of the resolved quotient meets it. -/
theorem fine_left_selected_valency_eq_three
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    nonDanglingValency (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) sheet) = 3 := by
  rw [← fine_left_endpoint_eq_of_wall_rel input profile hSame profile.first.1.1.2
    sheet (incident_wall_rel input profile.first)
    ((incident_wall_rel input profile.first).symm.trans hSelected)]
  exact fine_left_nonDanglingValency_eq_three input profile hSame

theorem fineRowOfEdge_incident_left_background
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (edge : NonDanglingEdge (fineCandidate input profile hSame).datum)
    (hIncident : Incident (fineCandidate input profile hSame).datum edge.1
      ((fineCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) sheet)) :
    ∃ hOld : ¬ IsDangling data (data.sourceEdge (largestTarget input profile) sheet),
      fineRowOfEdge input profile hSame edge = NonDanglingEdge.stablePath
        ⟨data.sourceEdge (largestTarget input profile) sheet, hOld⟩ := by
  classical
  let candidate := fineCandidate input profile hSame
  rcases nonDanglingEdge_cases candidate input.valid
      (fineCandidate_sourceGenus input profile hSame) edge with
    ⟨old, rfl⟩ | ⟨other, hSurvives, rfl⟩
  · have hData := (incident_iff_target_mem_and_rel candidate.datum
      (candidate.oldSourceEdge old.1)
      (candidate.datum.sourceEndpoint (oldVertex target wall) sheet)).mp hIncident
    simp only [GluingDatum.sourceEndpoint, candidate.oldSourceEdge_target,
      candidate.oldSourceEdge_sheet] at hData
    have hVertex : candidate.datum.vertexPartition (oldVertex target wall) =
        (finePastedResolution input profile hSame).left :=
      GlobalResolution.expandedVertexPartition_old_wall data wall _
    rw [hVertex] at hData
    have hTarget := hData.1
    rw [fine_left_target_incident_pair input profile hSame] at hTarget
    rcases Finset.mem_insert.mp hTarget with hNew | hDoubled
    · have hLabels := (occurrenceEquiv target wall candidate.right).injective hNew
      cases hLabels
    · have hOldTarget : old.1.1.1 = (largestTarget input profile) :=
        Option.some.inj ((occurrenceEquiv target wall candidate.right).injective
          (Finset.mem_singleton.mp hDoubled))
      have hRel := hData.2
      have hLeftRel : (finePastedResolution input profile hSame).left.Rel
          sheet old.1.1.2 := by
        change (finePastedResolution input profile hSame).left.Rel
          ((finePastedResolution input profile hSame).left.repr sheet)
          old.1.1.2 at hRel
        exact (finePastedResolution input profile hSame).left.rel_repr_right sheet
          |>.trans hRel
      have hFineRel : (largestPartition input profile).Rel sheet old.1.1.2 := by
        apply (largestPartition input profile).mem_block_iff _ _ |>.mp
        rw [← fine_background_left_block input profile hSame sheet hBackground,
          (finePastedResolution input profile hSame).left.mem_block_iff]
        exact hLeftRel
      have hOldEq : old.1 = data.sourceEdge (largestTarget input profile) sheet := by
        apply Subtype.ext
        apply Prod.ext
        · exact hOldTarget
        · calc
            old.1.1.2 = (largestPartition input profile).repr old.1.1.2 := by
              have hCanonical := old.1.2
              change (data.edgePartition old.1.1.1).repr old.1.1.2 =
                old.1.1.2 at hCanonical
              rw [hOldTarget] at hCanonical
              exact hCanonical.symm
            _ = (largestPartition input profile).repr sheet := hFineRel.symm
            _ = (data.sourceEdge (largestTarget input profile) sheet).1.2 := rfl
      refine ⟨hOldEq ▸ old.2, ?_⟩
      rw [fineRowOfEdge_retained]
      exact congrArg NonDanglingEdge.stablePath (Subtype.ext hOldEq)
  · have hData := (incident_iff_target_mem_and_rel candidate.datum
      (candidate.newSourceEdge other)
      (candidate.datum.sourceEndpoint (oldVertex target wall) sheet)).mp hIncident
    simp only [GluingDatum.sourceEndpoint, candidate.newSourceEdge_target,
      candidate.newSourceEdge_sheet] at hData
    have hVertex : candidate.datum.vertexPartition (oldVertex target wall) =
        (finePastedResolution input profile hSame).left :=
      GlobalResolution.expandedVertexPartition_old_wall data wall _
    rw [hVertex] at hData
    have hRel := hData.2
    have hLeftRel : (finePastedResolution input profile hSame).left.Rel sheet
        ((finePastedResolution input profile hSame).newEdge.repr other) := by
      change (finePastedResolution input profile hSame).left.Rel
        ((finePastedResolution input profile hSame).left.repr sheet)
        ((finePastedResolution input profile hSame).newEdge.repr other) at hRel
      exact (finePastedResolution input profile hSame).left.rel_repr_right sheet
        |>.trans hRel
    have hLeftRelOther : (finePastedResolution input profile hSame).left.Rel
        sheet other :=
      hLeftRel.trans ((finePastedResolution input profile hSame).edge_refines_left.rel
        ((finePastedResolution input profile hSame).newEdge.rel_repr_left other))
    have hWallOther : (data.vertexPartition wall).Rel sheet other :=
      (LocalResolution.pasteLeft_refines (data.vertexPartition wall)
        candidate.resolution candidate.contracts).rel hLeftRelOther
    have hOtherBackground : ¬(data.vertexPartition wall).Rel
        input.distinguishedBlock.1 other := by
      intro hSelected
      exact hBackground (hSelected.trans hWallOther.symm)
    have hNewRel : (finePastedResolution input profile hSame).newEdge.Rel
        sheet other := by
      apply (finePastedResolution input profile hSame).newEdge.mem_block_iff _ _ |>.mp
      rw [fine_background_newEdge_block input profile hSame sheet hBackground]
      apply (largestPartition input profile).mem_block_iff _ _ |>.mpr
      apply (largestPartition input profile).mem_block_iff _ _ |>.mp
      rw [← fine_background_left_block input profile hSame sheet hBackground,
        (finePastedResolution input profile hSame).left.mem_block_iff]
      exact hLeftRelOther
    have hFineRel : (largestPartition input profile).Rel sheet other := by
      apply (largestPartition input profile).mem_block_iff _ _ |>.mp
      rw [← fine_background_newEdge_block input profile hSame sheet hBackground,
        (finePastedResolution input profile hSame).newEdge.mem_block_iff]
      exact hNewRel
    have hOldEq : data.sourceEdge (largestTarget input profile) other =
        data.sourceEdge (largestTarget input profile) sheet := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact hFineRel.symm
    have hOldOther := (fine_background_new_survives_iff_largest input profile hSame
      other hOtherBackground).mp hSurvives
    have hOldSheet : ¬ IsDangling data
        (data.sourceEdge (largestTarget input profile) sheet) := hOldEq.symm ▸ hOldOther
    refine ⟨hOldSheet, ?_⟩
    exact (fineRowOfEdge_new_background input profile hSame other hOtherBackground
      hSurvives).trans (congrArg NonDanglingEdge.stablePath (Subtype.ext hOldEq))

theorem fineRowOfEdge_eq_away
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (vertex : data.SourceVertex) (hAway : vertex.1.1 ≠ wall)
    (first second : NonDanglingEdge (fineCandidate input profile hSame).datum)
    (hFirst : Incident (fineCandidate input profile hSame).datum first.1
      (retainedVertex (fineCandidate input profile hSame) vertex))
    (hSecond : Incident (fineCandidate input profile hSame).datum second.1
      (retainedVertex (fineCandidate input profile hSame) vertex))
    (hValency : nonDanglingValency (fineCandidate input profile hSame).datum
      (retainedVertex (fineCandidate input profile hSame) vertex) = 2) :
    fineRowOfEdge input profile hSame first =
      fineRowOfEdge input profile hSame second := by
  classical
  let candidate := fineCandidate input profile hSame
  have hGenus := fineCandidate_sourceGenus input profile hSame
  rcases nonDanglingEdge_cases candidate input.valid hGenus first with
      ⟨oldFirst, rfl⟩ | ⟨sheet, hSurvives, rfl⟩
  · rcases nonDanglingEdge_cases candidate input.valid hGenus second with
        ⟨oldSecond, rfl⟩ | ⟨sheet, hSurvives, rfl⟩
    · rw [fineRowOfEdge_retained, fineRowOfEdge_retained]
      by_cases hEqual : oldFirst = oldSecond
      · exact congrArg NonDanglingEdge.stablePath hEqual
      · exact stablePath_eq_of_consecutive ⟨hEqual, vertex,
          (incident_oldSourceEdge_iff candidate vertex hAway oldFirst.1).mp hFirst,
          (incident_oldSourceEdge_iff candidate vertex hAway oldSecond.1).mp hSecond,
          (nonDanglingValency_retainedVertex candidate input.valid hGenus vertex
            hAway).symm.trans hValency⟩
    · exact (not_incident_newSourceEdge candidate vertex hAway sheet hSecond).elim
  · exact (not_incident_newSourceEdge candidate vertex hAway sheet hFirst).elim

/-- The coarse reverse assignment is constant on every consecutive pair.  Its
selected divalent case is *vacuous*, because that endpoint is a branch vertex
in `M⁽²⁾`. -/
theorem fineRowOfEdge_eq_of_consecutive
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (first second : NonDanglingEdge (fineCandidate input profile hSame).datum)
    (hConsecutive : Consecutive (fineCandidate input profile hSame).datum first second) :
    fineRowOfEdge input profile hSame first =
      fineRowOfEdge input profile hSame second := by
  classical
  let candidate := fineCandidate input profile hSame
  obtain ⟨hNe, vertex, hFirst, hSecond, hValency⟩ := hConsecutive
  have hSelf : candidate.datum.sourceEndpoint vertex.1.1 vertex.1.2 = vertex :=
    (candidate.datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨rfl, rfl⟩
  cases hTarget : vertex.1.1 with
  | inl place =>
      by_cases hAt : place = wall
      · subst place
        have hEndpoint : candidate.datum.sourceEndpoint (oldVertex target wall)
            vertex.1.2 = vertex :=
          (congrArg (fun place ↦ candidate.datum.sourceEndpoint place vertex.1.2)
            hTarget.symm).trans hSelf
        rw [← hEndpoint] at hFirst hSecond hValency
        by_cases hSelected : (data.vertexPartition wall).Rel
            input.distinguishedBlock.1 vertex.1.2
        · rw [fine_left_selected_valency_eq_three input profile hSame vertex.1.2
            hSelected] at hValency
          exact absurd hValency (by omega)
        · obtain ⟨hOldFirst, hFirstRow⟩ :=
            fineRowOfEdge_incident_left_background input profile hSame _ hSelected
              first hFirst
          obtain ⟨hOldSecond, hSecondRow⟩ :=
            fineRowOfEdge_incident_left_background input profile hSame _ hSelected
              second hSecond
          exact hFirstRow.trans hSecondRow.symm
      · obtain ⟨old, hOld, hVertex⟩ :=
          exists_retainedVertex_of_target candidate vertex place hAt hTarget
        rw [← hVertex] at hFirst hSecond hValency
        exact fineRowOfEdge_eq_away input profile hSame old (hOld ▸ hAt) first second
          hFirst hSecond hValency
  | inr point =>
      cases point
      have hEndpoint : candidate.datum.sourceEndpoint (freshVertex target)
          vertex.1.2 = vertex :=
        (congrArg (fun place ↦ candidate.datum.sourceEndpoint place vertex.1.2)
          hTarget.symm).trans hSelf
      rw [← hEndpoint] at hFirst hSecond hValency
      by_cases hSelected : (data.vertexPartition wall).Rel
          input.distinguishedBlock.1 vertex.1.2
      · exact (fineRowOfEdge_incident_fresh_selected input profile hSame _ hSelected
          first hFirst).trans (fineRowOfEdge_incident_fresh_selected input profile
            hSame _ hSelected second hSecond).symm
      · exact fineRowOfEdge_eq_background input profile hSame _ hSelected first second
          hNe hFirst hSecond hValency

/-- The explicit reverse row assignment of `M⁽²⁾` descends through the
stable-path quotient. -/
noncomputable def fineStablePathDescend
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    StablePath (fineCandidate input profile hSame).datum → StablePath data :=
  Quot.lift (fineRowOfEdge input profile hSame)
    (fineRowOfEdge_eq_of_consecutive input profile hSame)

@[simp] theorem fineStablePathDescend_mk
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge (fineCandidate input profile hSame).datum) :
    fineStablePathDescend input profile hSame edge.stablePath =
      fineRowOfEdge input profile hSame edge := rfl

theorem fineStablePathDescend_lift
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath data) :
    fineStablePathDescend input profile hSame
      (fineStablePathLift input profile hSame path) = path := by
  induction path using Quot.inductionOn with
  | h edge => exact fineRowOfEdge_retained input profile hSame edge

theorem fineStablePathLift_injective
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    Function.Injective (fineStablePathLift input profile hSame) :=
  Function.LeftInverse.injective (fineStablePathDescend_lift input profile hSame)

/-- **The stable rows of `M⁽²⁾` are the source's, via retention.** -/
noncomputable def fineStablePathEquiv
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    StablePath data ≃ StablePath (fineCandidate input profile hSame).datum :=
  Equiv.ofBijective (fineStablePathLift input profile hSame)
    ⟨fineStablePathLift_injective input profile hSame,
      fineStablePathLift_surjective input profile hSame⟩

@[simp] theorem fineStablePathEquiv_mk
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge data) :
    fineStablePathEquiv input profile hSame edge.stablePath =
      (retainedEdge (fineCandidate input profile hSame)
        input.valid.1 edge).stablePath := rfl

/-! ## The limit matrix of `M⁽¹⁾`

Retained target occurrences reproduce the original source matrix under the
geometric coarse row equivalence.  On the new target occurrence the single
selected source occurrence is separated from every background occurrence, each
carrying its genuine dilation index. -/

theorem coarse_occurrences_retained (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath data) (place : target.edges) :
    occurrences (coarseCandidate input profile hSame).datum
        (coarseStablePathEquiv input profile hSame path)
        (occurrenceEquiv target wall (coarseCandidate input profile hSame).right
          (some place)) =
      (occurrences data path place).image
        (coarseCandidate input profile hSame).oldSourceEdge := by
  classical
  let candidate := coarseCandidate input profile hSame
  ext edge
  constructor
  · intro hMem
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hMem
    rcases sourceEdge_cases candidate edge with ⟨old, rfl⟩ | ⟨sheet, rfl⟩
    · have hOld : ¬ IsDangling data old := fun h ↦ hSurvives
        ((isDangling_oldSourceEdge_iff candidate input.valid
          (coarseCandidate_sourceGenus input profile hSame) old).mpr h)
      refine Finset.mem_image.mpr
        ⟨old, (mem_occurrences _ _ _).mpr ⟨⟨hOld, ?_⟩, ?_⟩, rfl⟩
      · apply (coarseStablePathEquiv input profile hSame).injective
        exact (coarseStablePathEquiv_mk input profile hSame ⟨old, hOld⟩).trans hRow
      · exact Option.some.inj
          ((occurrenceEquiv target wall candidate.right).injective hTarget)
    · have hLabels := (occurrenceEquiv target wall candidate.right).injective hTarget
      cases hLabels
  · intro hMem
    obtain ⟨old, hOld, rfl⟩ := Finset.mem_image.mp hMem
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hOld
    refine (mem_occurrences _ _ _).mpr
      ⟨⟨not_isDangling_oldSourceEdge candidate input.valid.1 old hSurvives, ?_⟩, ?_⟩
    · exact (coarseStablePathEquiv_mk input profile hSame ⟨old, hSurvives⟩).symm.trans
        (congrArg (coarseStablePathEquiv input profile hSame) hRow)
    · exact congrArg
        (fun label ↦ occurrenceEquiv target wall candidate.right (some label)) hTarget

/-- Every retained entry of `M⁽¹⁾`'s matrix is literally its original wall
entry. -/
theorem coarse_matrix_retained (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath data) (place : target.edges) :
    matrix (coarseCandidate input profile hSame).datum
        (coarseStablePathEquiv input profile hSame path)
        (occurrenceEquiv target wall (coarseCandidate input profile hSame).right
          (some place)) =
      matrix data path place := by
  classical
  unfold matrix
  rw [coarse_occurrences_retained, Finset.sum_image]
  · exact Finset.sum_congr rfl fun edge _ ↦ by
      rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge]
  · intro first _ second _ hEqual
    exact ResolutionCut.oldSourceEdge_injective _ hEqual

/-- A new occurrence over a selected sheet has a selected sheet label, and
conversely. -/
theorem coarse_new_sheet_rel (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree) :
    (data.vertexPartition wall).Rel sheet
      ((coarseCandidate input profile hSame).newSourceEdge sheet).1.2 := by
  let pasted := coarsePastedResolution input profile hSame
  have hRefines : pasted.newEdge.Refines (data.vertexPartition wall) :=
    pasted.edge_refines_left.trans
      (SheetPartition.IsJoin.left_refines (LocalResolution.paste_contracts
        (data.vertexPartition wall) (coarseCandidate input profile hSame).resolution
        (coarseCandidate input profile hSame).contracts))
  change (data.vertexPartition wall).Rel sheet (pasted.newEdge.repr sheet)
  exact hRefines.rel (pasted.newEdge.rel_repr_right sheet)

/-- The row-filtered new fibre of `M⁽¹⁾` away from the distinguished block. -/
noncomputable def coarseBackgroundOccurrences (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath (coarseCandidate input profile hSame).datum) :
    Finset (coarseCandidate input profile hSame).datum.SourceEdge := by
  classical
  exact (occurrences (coarseCandidate input profile hSame).datum path
    (occurrenceEquiv target wall (coarseCandidate input profile hSame).right none)).erase
      ((coarseCandidate input profile hSame).newSourceEdge profile.first.1.1.2)

theorem mem_coarseBackgroundOccurrences (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath (coarseCandidate input profile hSame).datum)
    (edge : (coarseCandidate input profile hSame).datum.SourceEdge) :
    edge ∈ coarseBackgroundOccurrences input profile hSame path ↔
      edge ∈ occurrences (coarseCandidate input profile hSame).datum path
          (occurrenceEquiv target wall (coarseCandidate input profile hSame).right
            none) ∧
        ¬ (data.vertexPartition wall).Rel input.distinguishedBlock.1 edge.1.2 := by
  classical
  let candidate := coarseCandidate input profile hSame
  rw [coarseBackgroundOccurrences, Finset.mem_erase]
  constructor
  · rintro ⟨hNe, hMem⟩
    refine ⟨hMem, ?_⟩
    intro hSelected
    have hNew := eq_newSourceEdge_of_target candidate edge
      ((mem_occurrences _ _ _).mp hMem).2
    exact hNe (hNew.trans
      (coarse_newSourceEdge_eq_of_selected input profile hSame edge.1.2 hSelected))
  · rintro ⟨hMem, hBackground⟩
    refine ⟨?_, hMem⟩
    intro hEqual
    apply hBackground
    rw [hEqual]
    exact (incident_wall_rel input profile.first).trans
      (coarse_new_sheet_rel input profile hSame profile.first.1.1.2)

/-- The selected new occurrence of `M⁽¹⁾` lies in exactly its geometric row. -/
theorem coarse_selected_mem_occurrences_iff (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath (coarseCandidate input profile hSame).datum) :
    (coarseCandidate input profile hSame).newSourceEdge profile.first.1.1.2 ∈
        occurrences (coarseCandidate input profile hSame).datum path
          (occurrenceEquiv target wall (coarseCandidate input profile hSame).right
            none) ↔
      path = (coarseAnchorNew input profile hSame).stablePath := by
  rw [mem_occurrences]
  constructor
  · rintro ⟨⟨_, hRow⟩, _⟩
    exact hRow.symm
  · intro hRow
    exact ⟨⟨coarse_anchor_new_survives input profile hSame, hRow.symm⟩, rfl⟩

/-- Every new-fibre contribution of `M⁽¹⁾` away from the distinguished wall
block, with its actual quotient-source index. -/
noncomputable def coarseBackgroundColumn (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath (coarseCandidate input profile hSame).datum) : ℚ :=
  ∑ edge ∈ coarseBackgroundOccurrences input profile hSame path,
    (1 : ℚ) / (coarseCandidate input profile hSame).datum.sourceEdgeIndex edge

/-- **Equation (4)'s coarse new column.**  One selected occurrence with the
literal index `k₂ + k₃`, plus the exact background sum. -/
theorem coarse_matrix_new (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath (coarseCandidate input profile hSame).datum) :
    matrix (coarseCandidate input profile hSame).datum path
        (occurrenceEquiv target wall (coarseCandidate input profile hSame).right none) =
      (if path = (coarseAnchorNew input profile hSame).stablePath then
          (1 : ℚ) / (data.sourceEdgeIndex profile.first.1 +
            data.sourceEdgeIndex profile.second.1)
        else 0) + coarseBackgroundColumn input profile hSame path := by
  classical
  let candidate := coarseCandidate input profile hSame
  let selected := candidate.newSourceEdge profile.first.1.1.2
  let fibre := occurrences candidate.datum path
    (occurrenceEquiv target wall candidate.right none)
  have hIndex : ((candidate.datum.sourceEdgeIndex selected : ℚ)) =
      ((data.sourceEdgeIndex profile.first.1 +
        data.sourceEdgeIndex profile.second.1 : ℕ) : ℚ) :=
    congrArg (fun n : ℕ ↦ (n : ℚ)) (coarse_anchor_new_index input profile hSame)
  by_cases hRow : path = (coarseAnchorNew input profile hSame).stablePath
  · have hMem : selected ∈ fibre :=
      (coarse_selected_mem_occurrences_iff input profile hSame path).mpr hRow
    have hSum := Finset.sum_erase_add fibre
      (fun edge ↦ (1 : ℚ) / candidate.datum.sourceEdgeIndex edge) hMem
    change coarseBackgroundColumn input profile hSame path +
      (1 : ℚ) / candidate.datum.sourceEdgeIndex selected =
        matrix candidate.datum path
          (occurrenceEquiv target wall candidate.right none) at hSum
    rw [if_pos hRow]
    rw [← hSum, add_comm]
    congr 1
    rw [hIndex]
    push_cast
    ring
  · have hNot : selected ∉ fibre :=
      fun h ↦ hRow ((coarse_selected_mem_occurrences_iff input profile hSame path).mp h)
    have hErase := Finset.erase_eq_of_notMem hNot
    rw [if_neg hRow, zero_add]
    change (∑ edge ∈ fibre, (1 : ℚ) / candidate.datum.sourceEdgeIndex edge) =
      ∑ edge ∈ fibre.erase selected,
        (1 : ℚ) / candidate.datum.sourceEdgeIndex edge
    rw [hErase]

/-- Original doubled-direction occurrences in a fixed old row and outside the
distinguished wall block. -/
noncomputable def coarseOldBackgroundOccurrences (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (path : StablePath data) : Finset data.SourceEdge := by
  classical
  exact (occurrences data path profile.first.1.1.1).filter
    (fun edge ↦ ¬ (data.vertexPartition wall).Rel
      input.distinguishedBlock.1 edge.1.2)

theorem mem_coarseOldBackgroundOccurrences (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (path : StablePath data) (edge : data.SourceEdge) :
    edge ∈ coarseOldBackgroundOccurrences input profile path ↔
      edge ∈ occurrences data path profile.first.1.1.1 ∧
        ¬ (data.vertexPartition wall).Rel input.distinguishedBlock.1 edge.1.2 := by
  classical
  exact Finset.mem_filter

theorem coarse_new_mem_of_old_mem (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath data) (edge : data.SourceEdge)
    (hMem : edge ∈ coarseOldBackgroundOccurrences input profile path) :
    (coarseCandidate input profile hSame).newSourceEdge edge.1.2 ∈
      coarseBackgroundOccurrences input profile hSame
        (coarseStablePathEquiv input profile hSame path) := by
  have hOld := (mem_coarseOldBackgroundOccurrences input profile path edge).mp hMem
  obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hOld.1
  have hCanonical : data.sourceEdge profile.first.1.1.1 edge.1.2 = edge := by
    rw [← hTarget]
    exact GluingDatum.sourceEdge_self data edge
  have hCanonicalSurvives :
      ¬ IsDangling data (data.sourceEdge profile.first.1.1.1 edge.1.2) := by
    rw [hCanonical]
    exact hSurvives
  have hNew := (coarse_background_new_survives_iff_doubled input profile hSame
    edge.1.2 hOld.2).mpr hCanonicalSurvives
  refine (mem_coarseBackgroundOccurrences input profile hSame _ _).mpr
    ⟨(mem_occurrences _ _ _).mpr ⟨⟨hNew, ?_⟩, rfl⟩, ?_⟩
  · exact (coarse_background_new_stablePath_eq_doubled input profile hSame
      edge.1.2 hOld.2 hCanonicalSurvives).trans
      ((coarseStablePathEquiv_mk input profile hSame
        ⟨data.sourceEdge profile.first.1.1.1 edge.1.2,
          hCanonicalSurvives⟩).symm.trans
        (congrArg (coarseStablePathEquiv input profile hSame)
          ((congrArg NonDanglingEdge.stablePath
            (show (⟨data.sourceEdge profile.first.1.1.1 edge.1.2,
              hCanonicalSurvives⟩ : NonDanglingEdge data) = ⟨edge, hSurvives⟩ from
                Subtype.ext hCanonical)).trans hRow)))
  · intro hSelected
    exact hOld.2 (hSelected.trans
      (coarse_new_sheet_rel input profile hSame edge.1.2).symm)

theorem coarse_old_mem_of_new_mem (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath data)
    (edge : (coarseCandidate input profile hSame).datum.SourceEdge)
    (hMem : edge ∈ coarseBackgroundOccurrences input profile hSame
      (coarseStablePathEquiv input profile hSame path)) :
    data.sourceEdge profile.first.1.1.1 edge.1.2 ∈
      coarseOldBackgroundOccurrences input profile path := by
  let candidate := coarseCandidate input profile hSame
  have hData := (mem_coarseBackgroundOccurrences input profile hSame _ _).mp hMem
  obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hData.1
  have hEdge := eq_newSourceEdge_of_target candidate edge hTarget
  have hNew : ¬ IsDangling candidate.datum (candidate.newSourceEdge edge.1.2) := by
    rw [← hEdge]
    exact hSurvives
  have hOld : ¬ IsDangling data
      (data.sourceEdge profile.first.1.1.1 edge.1.2) :=
    (coarse_background_new_survives_iff_doubled input profile hSame edge.1.2
      hData.2).mp hNew
  have hNewRow : NonDanglingEdge.stablePath
      ⟨candidate.newSourceEdge edge.1.2, hNew⟩ =
        coarseStablePathEquiv input profile hSame path :=
    (congrArg NonDanglingEdge.stablePath
      (show (⟨candidate.newSourceEdge edge.1.2, hNew⟩ :
        NonDanglingEdge candidate.datum) = ⟨edge, hSurvives⟩ from
          Subtype.ext hEdge.symm)).trans hRow
  refine (mem_coarseOldBackgroundOccurrences input profile path _).mpr
    ⟨(mem_occurrences _ _ _).mpr ⟨⟨hOld, ?_⟩, rfl⟩, ?_⟩
  · apply (coarseStablePathEquiv input profile hSame).injective
    exact (coarseStablePathEquiv_mk input profile hSame
      ⟨data.sourceEdge profile.first.1.1.1 edge.1.2, hOld⟩).trans
      ((coarse_background_new_stablePath_eq_doubled input profile hSame
        edge.1.2 hData.2 hOld).symm.trans hNewRow)
  · intro hSelected
    apply hData.2
    exact hSelected.trans
      ((StableLocalProperties.refines_of_mem_incidentEdges data
        (incident_target_mem input profile.first)).rel
          ((data.edgePartition profile.first.1.1.1).rel_repr_left edge.1.2))

theorem coarse_new_old_roundtrip (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath data)
    (edge : (coarseCandidate input profile hSame).datum.SourceEdge)
    (hMem : edge ∈ coarseBackgroundOccurrences input profile hSame
      (coarseStablePathEquiv input profile hSame path)) :
    (coarseCandidate input profile hSame).newSourceEdge
        (data.sourceEdge profile.first.1.1.1 edge.1.2).1.2 = edge := by
  let candidate := coarseCandidate input profile hSame
  have hData := (mem_coarseBackgroundOccurrences input profile hSame _ _).mp hMem
  have hTarget := ((mem_occurrences _ _ _).mp hData.1).2
  have hEdge := eq_newSourceEdge_of_target candidate edge hTarget
  exact (coarse_background_new_eq_of_doubled_source_eq input profile hSame edge.1.2
    (data.sourceEdge profile.first.1.1.1 edge.1.2).1.2 hData.2
      (GluingDatum.sourceEdge_self data
        (data.sourceEdge profile.first.1.1.1 edge.1.2))).trans hEdge.symm

theorem coarse_new_of_old_injective (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath data) (first second : data.SourceEdge)
    (hFirst : first ∈ coarseOldBackgroundOccurrences input profile path)
    (hSecond : second ∈ coarseOldBackgroundOccurrences input profile path)
    (hEqual : (coarseCandidate input profile hSame).newSourceEdge first.1.2 =
      (coarseCandidate input profile hSame).newSourceEdge second.1.2) :
    first = second := by
  have hFirstData := (mem_coarseOldBackgroundOccurrences input profile path first).mp
    hFirst
  have hSecondData := (mem_coarseOldBackgroundOccurrences input profile path second).mp
    hSecond
  have hFirstTarget := ((mem_occurrences _ _ _).mp hFirstData.1).2
  have hSecondTarget := ((mem_occurrences _ _ _).mp hSecondData.1).2
  have hNewRepr := congrArg
    (fun edge : (coarseCandidate input profile hSame).datum.SourceEdge ↦ edge.1.2)
    hEqual
  have hNewRel : (coarsePastedResolution input profile hSame).newEdge.Rel
      first.1.2 second.1.2 := hNewRepr
  have hFineRel : (finePartition input profile).Rel first.1.2 second.1.2 := by
    apply (finePartition input profile).mem_block_iff _ _ |>.mp
    rw [← coarse_background_newEdge_block input profile hSame first.1.2 hFirstData.2,
      (coarsePastedResolution input profile hSame).newEdge.mem_block_iff]
    exact hNewRel
  apply Subtype.ext
  apply Prod.ext
  · exact hFirstTarget.trans hSecondTarget.symm
  · have hFirstRepr : (finePartition input profile).repr first.1.2 = first.1.2 := by
      change (data.edgePartition profile.first.1.1.1).repr first.1.2 = first.1.2
      rw [← hFirstTarget]
      exact first.2
    have hSecondRepr : (finePartition input profile).repr second.1.2 = second.1.2 := by
      change (data.edgePartition profile.first.1.1.1).repr second.1.2 = second.1.2
      rw [← hSecondTarget]
      exact second.2
    exact hFirstRepr.symm.trans (hFineRel.trans hSecondRepr)

theorem coarse_background_index_eq (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath data) (edge : data.SourceEdge)
    (hMem : edge ∈ coarseOldBackgroundOccurrences input profile path) :
    (coarseCandidate input profile hSame).datum.sourceEdgeIndex
        ((coarseCandidate input profile hSame).newSourceEdge edge.1.2) =
      data.sourceEdgeIndex edge := by
  have hData := (mem_coarseOldBackgroundOccurrences input profile path edge).mp hMem
  have hTarget := ((mem_occurrences _ _ _).mp hData.1).2
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge]
  change (coarsePastedResolution input profile hSame).newEdge.blockCard edge.1.2 =
    (data.edgePartition edge.1.1).blockCard edge.1.2
  unfold SheetPartition.blockCard
  rw [coarse_background_newEdge_block input profile hSame edge.1.2 hData.2]
  change ((data.edgePartition profile.first.1.1.1).block edge.1.2).card =
    ((data.edgePartition edge.1.1).block edge.1.2).card
  rw [hTarget]

/-- The background part of `M⁽¹⁾`'s new column is a term-by-term reindexing of
the original doubled-direction background fibre. -/
theorem coarse_backgroundColumn_eq_sum_old (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath data) :
    coarseBackgroundColumn input profile hSame
        (coarseStablePathEquiv input profile hSame path) =
      ∑ edge ∈ coarseOldBackgroundOccurrences input profile path,
        (1 : ℚ) / data.sourceEdgeIndex edge := by
  classical
  symm
  unfold coarseBackgroundColumn
  refine Finset.sum_bij
    (fun edge _ ↦ (coarseCandidate input profile hSame).newSourceEdge edge.1.2)
    ?_ ?_ ?_ ?_
  · exact fun edge hEdge ↦ coarse_new_mem_of_old_mem input profile hSame path edge hEdge
  · exact fun first hFirst second hSecond hEqual ↦
      coarse_new_of_old_injective input profile hSame path first second hFirst hSecond
        hEqual
  · intro edge hEdge
    exact ⟨_, coarse_old_mem_of_new_mem input profile hSame path edge hEdge,
      coarse_new_old_roundtrip input profile hSame path edge hEdge⟩
  · intro edge hEdge
    rw [coarse_background_index_eq input profile hSame path edge hEdge]

/-- **Figure 30's `c⁽¹⁾` column on the source's own stable rows.**  The
selected coefficient is `1/(k₂+k₃)` on the row of the retained largest
direction `e₄`, and the residual term is the exact old doubled-direction
background sum. -/
theorem coarse_matrix_new_on_old_row (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath data) :
    matrix (coarseCandidate input profile hSame).datum
        (coarseStablePathEquiv input profile hSame path)
        (occurrenceEquiv target wall (coarseCandidate input profile hSame).right none) =
      (if path = NonDanglingEdge.stablePath
          ⟨profile.largest.1, largest_survives input profile⟩ then
        (1 : ℚ) / (data.sourceEdgeIndex profile.first.1 +
          data.sourceEdgeIndex profile.second.1)
       else 0) +
        ∑ edge ∈ coarseOldBackgroundOccurrences input profile path,
          (1 : ℚ) / data.sourceEdgeIndex edge := by
  classical
  rw [coarse_matrix_new input profile hSame,
    coarse_backgroundColumn_eq_sum_old input profile hSame]
  have hSelected : coarseStablePathEquiv input profile hSame
      (NonDanglingEdge.stablePath
        ⟨profile.largest.1, largest_survives input profile⟩) =
        (coarseAnchorNew input profile hSame).stablePath :=
    (coarseStablePathEquiv_mk input profile hSame
      ⟨profile.largest.1, largest_survives input profile⟩).trans
        (coarse_anchor_new_stablePath_eq_largest input profile hSame).symm
  have hIff : coarseStablePathEquiv input profile hSame path =
      (coarseAnchorNew input profile hSame).stablePath ↔
        path = NonDanglingEdge.stablePath
          ⟨profile.largest.1, largest_survives input profile⟩ := by
    rw [← hSelected, Equiv.apply_eq_iff_eq]
  simp only [hIff]

/-! ## The limit matrix of `M⁽²⁾`

The retained columns are again literally the source's.  The new column is the
place where Figure 30's `M⁽²⁾` differs from every nd2 member and from `M⁽¹⁾`:
`k₂ + k₃ = |A₀|` leaves no residual sheet, so the distinguished block
contributes **two** surviving new occurrences, with the two separate indices
`k₂` and `k₃`.  The two indicator terms below are kept separate rather than
summed over a set of row labels, because the rows of `e₂` and `e₃` are not
asserted to be distinct — a stable loop through the branch vertex would make
them equal, and the formula stays correct. -/

theorem fine_occurrences_retained (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath data) (place : target.edges) :
    occurrences (fineCandidate input profile hSame).datum
        (fineStablePathEquiv input profile hSame path)
        (occurrenceEquiv target wall (fineCandidate input profile hSame).right
          (some place)) =
      (occurrences data path place).image
        (fineCandidate input profile hSame).oldSourceEdge := by
  classical
  let candidate := fineCandidate input profile hSame
  ext edge
  constructor
  · intro hMem
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hMem
    rcases sourceEdge_cases candidate edge with ⟨old, rfl⟩ | ⟨sheet, rfl⟩
    · have hOld : ¬ IsDangling data old := fun h ↦ hSurvives
        ((isDangling_oldSourceEdge_iff candidate input.valid
          (fineCandidate_sourceGenus input profile hSame) old).mpr h)
      refine Finset.mem_image.mpr
        ⟨old, (mem_occurrences _ _ _).mpr ⟨⟨hOld, ?_⟩, ?_⟩, rfl⟩
      · apply (fineStablePathEquiv input profile hSame).injective
        exact (fineStablePathEquiv_mk input profile hSame ⟨old, hOld⟩).trans hRow
      · exact Option.some.inj
          ((occurrenceEquiv target wall candidate.right).injective hTarget)
    · have hLabels := (occurrenceEquiv target wall candidate.right).injective hTarget
      cases hLabels
  · intro hMem
    obtain ⟨old, hOld, rfl⟩ := Finset.mem_image.mp hMem
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hOld
    refine (mem_occurrences _ _ _).mpr
      ⟨⟨not_isDangling_oldSourceEdge candidate input.valid.1 old hSurvives, ?_⟩, ?_⟩
    · exact (fineStablePathEquiv_mk input profile hSame ⟨old, hSurvives⟩).symm.trans
        (congrArg (fineStablePathEquiv input profile hSame) hRow)
    · exact congrArg
        (fun label ↦ occurrenceEquiv target wall candidate.right (some label)) hTarget

theorem fine_matrix_retained (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath data) (place : target.edges) :
    matrix (fineCandidate input profile hSame).datum
        (fineStablePathEquiv input profile hSame path)
        (occurrenceEquiv target wall (fineCandidate input profile hSame).right
          (some place)) =
      matrix data path place := by
  classical
  unfold matrix
  rw [fine_occurrences_retained, Finset.sum_image]
  · exact Finset.sum_congr rfl fun edge _ ↦ by
      rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge]
  · intro first _ second _ hEqual
    exact ResolutionCut.oldSourceEdge_injective _ hEqual

theorem fine_new_sheet_rel (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree) :
    (data.vertexPartition wall).Rel sheet
      ((fineCandidate input profile hSame).newSourceEdge sheet).1.2 := by
  let pasted := finePastedResolution input profile hSame
  have hRefines : pasted.newEdge.Refines (data.vertexPartition wall) :=
    pasted.edge_refines_left.trans
      (SheetPartition.IsJoin.left_refines (LocalResolution.paste_contracts
        (data.vertexPartition wall) (fineCandidate input profile hSame).resolution
        (fineCandidate input profile hSame).contracts))
  change (data.vertexPartition wall).Rel sheet (pasted.newEdge.repr sheet)
  exact hRefines.rel (pasted.newEdge.rel_repr_right sheet)

/-- The new fibre of `M⁽²⁾` with **both** selected occurrences removed. -/
noncomputable def fineBackgroundOccurrences (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath (fineCandidate input profile hSame).datum) :
    Finset (fineCandidate input profile hSame).datum.SourceEdge := by
  classical
  exact ((occurrences (fineCandidate input profile hSame).datum path
      (occurrenceEquiv target wall (fineCandidate input profile hSame).right none)).erase
      ((fineCandidate input profile hSame).newSourceEdge profile.first.1.1.2)).erase
      ((fineCandidate input profile hSame).newSourceEdge profile.second.1.1.2)

theorem mem_fineBackgroundOccurrences (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath (fineCandidate input profile hSame).datum)
    (edge : (fineCandidate input profile hSame).datum.SourceEdge) :
    edge ∈ fineBackgroundOccurrences input profile hSame path ↔
      edge ∈ occurrences (fineCandidate input profile hSame).datum path
          (occurrenceEquiv target wall (fineCandidate input profile hSame).right
            none) ∧
        ¬ (data.vertexPartition wall).Rel input.distinguishedBlock.1 edge.1.2 := by
  classical
  let candidate := fineCandidate input profile hSame
  rw [fineBackgroundOccurrences, Finset.mem_erase, Finset.mem_erase]
  constructor
  · rintro ⟨hNeSecond, hNeFirst, hMem⟩
    refine ⟨hMem, ?_⟩
    intro hSelected
    have hNew := eq_newSourceEdge_of_target candidate edge
      ((mem_occurrences _ _ _).mp hMem).2
    rcases fine_newSourceEdge_eq_of_selected input profile hSame edge.1.2 hSelected with
      hFirst | hSecond
    · exact hNeFirst (hNew.trans hFirst)
    · exact hNeSecond (hNew.trans hSecond)
  · rintro ⟨hMem, hBackground⟩
    refine ⟨?_, ?_, hMem⟩
    · intro hEqual
      apply hBackground
      rw [hEqual]
      exact (incident_wall_rel input profile.second).trans
        (fine_new_sheet_rel input profile hSame profile.second.1.1.2)
    · intro hEqual
      apply hBackground
      rw [hEqual]
      exact (incident_wall_rel input profile.first).trans
        (fine_new_sheet_rel input profile hSame profile.first.1.1.2)

theorem fine_selected_first_mem_occurrences_iff (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath (fineCandidate input profile hSame).datum) :
    (fineCandidate input profile hSame).newSourceEdge profile.first.1.1.2 ∈
        occurrences (fineCandidate input profile hSame).datum path
          (occurrenceEquiv target wall (fineCandidate input profile hSame).right
            none) ↔
      path = (fineNew input profile hSame profile.first.1.1.2
        (incident_wall_rel input profile.first)).stablePath := by
  rw [mem_occurrences]
  constructor
  · rintro ⟨⟨_, hRow⟩, _⟩
    exact hRow.symm
  · intro hRow
    exact ⟨⟨fine_new_survives input profile hSame profile.first.1.1.2
      (incident_wall_rel input profile.first), hRow.symm⟩, rfl⟩

theorem fine_selected_second_mem_occurrences_iff (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath (fineCandidate input profile hSame).datum) :
    (fineCandidate input profile hSame).newSourceEdge profile.second.1.1.2 ∈
        occurrences (fineCandidate input profile hSame).datum path
          (occurrenceEquiv target wall (fineCandidate input profile hSame).right
            none) ↔
      path = (fineNew input profile hSame profile.second.1.1.2
        (incident_wall_rel input profile.second)).stablePath := by
  rw [mem_occurrences]
  constructor
  · rintro ⟨⟨_, hRow⟩, _⟩
    exact hRow.symm
  · intro hRow
    exact ⟨⟨fine_new_survives input profile hSame profile.second.1.1.2
      (incident_wall_rel input profile.second), hRow.symm⟩, rfl⟩

noncomputable def fineBackgroundColumn (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath (fineCandidate input profile hSame).datum) : ℚ :=
  ∑ edge ∈ fineBackgroundOccurrences input profile hSame path,
    (1 : ℚ) / (fineCandidate input profile hSame).datum.sourceEdgeIndex edge

/-- **Equation (4)'s fine new column.**  Two selected occurrences with the
literal indices `k₂` and `k₃`, plus the exact background sum. -/
theorem fine_matrix_new (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath (fineCandidate input profile hSame).datum) :
    matrix (fineCandidate input profile hSame).datum path
        (occurrenceEquiv target wall (fineCandidate input profile hSame).right none) =
      (if path = (fineNew input profile hSame profile.first.1.1.2
            (incident_wall_rel input profile.first)).stablePath then
          (1 : ℚ) / data.sourceEdgeIndex profile.first.1 else 0) +
        (if path = (fineNew input profile hSame profile.second.1.1.2
            (incident_wall_rel input profile.second)).stablePath then
          (1 : ℚ) / data.sourceEdgeIndex profile.second.1 else 0) +
        fineBackgroundColumn input profile hSame path := by
  classical
  let candidate := fineCandidate input profile hSame
  let first := candidate.newSourceEdge profile.first.1.1.2
  let second := candidate.newSourceEdge profile.second.1.1.2
  let fibre := occurrences candidate.datum path
    (occurrenceEquiv target wall candidate.right none)
  let weight : candidate.datum.SourceEdge → ℚ :=
    fun edge ↦ (1 : ℚ) / candidate.datum.sourceEdgeIndex edge
  have hNe : first ≠ second := fine_new_first_ne_second input profile hSame
  have hFirstIndex : weight first = (1 : ℚ) / data.sourceEdgeIndex profile.first.1 := by
    change (1 : ℚ) / (candidate.datum.sourceEdgeIndex first : ℚ) = _
    rw [show candidate.datum.sourceEdgeIndex first =
      data.sourceEdgeIndex profile.first.1 from
        fine_new_first_index input profile hSame]
  have hSecondIndex : weight second =
      (1 : ℚ) / data.sourceEdgeIndex profile.second.1 := by
    change (1 : ℚ) / (candidate.datum.sourceEdgeIndex second : ℚ) = _
    rw [show candidate.datum.sourceEdgeIndex second =
      data.sourceEdgeIndex profile.second.1 from
        fine_new_second_index input profile hSame]
  have hSplit : (∑ edge ∈ fibre, weight edge) =
      (if first ∈ fibre then weight first else 0) +
        (if second ∈ fibre then weight second else 0) +
        ∑ edge ∈ (fibre.erase first).erase second, weight edge := by
    by_cases hA : first ∈ fibre
    · by_cases hB : second ∈ fibre
      · have hSecondErase : second ∈ fibre.erase first :=
          Finset.mem_erase.mpr ⟨fun h ↦ hNe h.symm, hB⟩
        have hOne := Finset.sum_erase_add fibre weight hA
        have hTwo := Finset.sum_erase_add (fibre.erase first) weight hSecondErase
        rw [if_pos hA, if_pos hB, ← hOne, ← hTwo]
        ring
      · have hNotErase : second ∉ fibre.erase first :=
          fun h ↦ hB (Finset.mem_of_mem_erase h)
        have hOne := Finset.sum_erase_add fibre weight hA
        rw [if_pos hA, if_neg hB, Finset.erase_eq_of_notMem hNotErase, ← hOne]
        ring
    · by_cases hB : second ∈ fibre
      · have hEraseFirst : fibre.erase first = fibre :=
          Finset.erase_eq_of_notMem hA
        have hThree := Finset.sum_erase_add fibre weight hB
        rw [if_neg hA, if_pos hB, hEraseFirst, ← hThree]
        ring
      · have hEraseFirst : fibre.erase first = fibre :=
          Finset.erase_eq_of_notMem hA
        have hNotErase : second ∉ fibre.erase first := by
          rw [hEraseFirst]; exact hB
        rw [if_neg hA, if_neg hB, Finset.erase_eq_of_notMem hNotErase, hEraseFirst]
        ring
  have hGoal : matrix candidate.datum path
      (occurrenceEquiv target wall candidate.right none) =
        ∑ edge ∈ fibre, weight edge := rfl
  rw [hGoal, hSplit]
  rw [show (if first ∈ fibre then weight first else 0) =
      (if path = (fineNew input profile hSame profile.first.1.1.2
        (incident_wall_rel input profile.first)).stablePath then
        (1 : ℚ) / data.sourceEdgeIndex profile.first.1 else 0) by
    by_cases hRow : path = (fineNew input profile hSame profile.first.1.1.2
        (incident_wall_rel input profile.first)).stablePath
    · rw [if_pos hRow, if_pos
        ((fine_selected_first_mem_occurrences_iff input profile hSame path).mpr hRow),
        hFirstIndex]
    · rw [if_neg hRow, if_neg (fun h ↦ hRow
        ((fine_selected_first_mem_occurrences_iff input profile hSame path).mp h))]]
  rw [show (if second ∈ fibre then weight second else 0) =
      (if path = (fineNew input profile hSame profile.second.1.1.2
        (incident_wall_rel input profile.second)).stablePath then
        (1 : ℚ) / data.sourceEdgeIndex profile.second.1 else 0) by
    by_cases hRow : path = (fineNew input profile hSame profile.second.1.1.2
        (incident_wall_rel input profile.second)).stablePath
    · rw [if_pos hRow, if_pos
        ((fine_selected_second_mem_occurrences_iff input profile hSame path).mpr hRow),
        hSecondIndex]
    · rw [if_neg hRow, if_neg (fun h ↦ hRow
        ((fine_selected_second_mem_occurrences_iff input profile hSame path).mp h))]]
  rfl

/-- Original largest-direction occurrences in a fixed old row and outside the
distinguished wall block. -/
noncomputable def fineOldBackgroundOccurrences (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (path : StablePath data) : Finset data.SourceEdge := by
  classical
  exact (occurrences data path (largestTarget input profile)).filter
    (fun edge ↦ ¬ (data.vertexPartition wall).Rel
      input.distinguishedBlock.1 edge.1.2)

theorem mem_fineOldBackgroundOccurrences (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (path : StablePath data) (edge : data.SourceEdge) :
    edge ∈ fineOldBackgroundOccurrences input profile path ↔
      edge ∈ occurrences data path (largestTarget input profile) ∧
        ¬ (data.vertexPartition wall).Rel input.distinguishedBlock.1 edge.1.2 := by
  classical
  exact Finset.mem_filter

theorem fine_new_mem_of_old_mem (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath data) (edge : data.SourceEdge)
    (hMem : edge ∈ fineOldBackgroundOccurrences input profile path) :
    (fineCandidate input profile hSame).newSourceEdge edge.1.2 ∈
      fineBackgroundOccurrences input profile hSame
        (fineStablePathEquiv input profile hSame path) := by
  have hOld := (mem_fineOldBackgroundOccurrences input profile path edge).mp hMem
  obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hOld.1
  have hCanonical : data.sourceEdge (largestTarget input profile) edge.1.2 = edge := by
    rw [← hTarget]
    exact GluingDatum.sourceEdge_self data edge
  have hCanonicalSurvives :
      ¬ IsDangling data (data.sourceEdge (largestTarget input profile) edge.1.2) := by
    rw [hCanonical]
    exact hSurvives
  have hNew := (fine_background_new_survives_iff_largest input profile hSame
    edge.1.2 hOld.2).mpr hCanonicalSurvives
  refine (mem_fineBackgroundOccurrences input profile hSame _ _).mpr
    ⟨(mem_occurrences _ _ _).mpr ⟨⟨hNew, ?_⟩, rfl⟩, ?_⟩
  · exact (fine_background_new_stablePath_eq_largest input profile hSame
      edge.1.2 hOld.2 hCanonicalSurvives).trans
      ((fineStablePathEquiv_mk input profile hSame
        ⟨data.sourceEdge (largestTarget input profile) edge.1.2,
          hCanonicalSurvives⟩).symm.trans
        (congrArg (fineStablePathEquiv input profile hSame)
          ((congrArg NonDanglingEdge.stablePath
            (show (⟨data.sourceEdge (largestTarget input profile) edge.1.2,
              hCanonicalSurvives⟩ : NonDanglingEdge data) = ⟨edge, hSurvives⟩ from
                Subtype.ext hCanonical)).trans hRow)))
  · intro hSelected
    exact hOld.2 (hSelected.trans
      (fine_new_sheet_rel input profile hSame edge.1.2).symm)

theorem fine_old_mem_of_new_mem (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath data)
    (edge : (fineCandidate input profile hSame).datum.SourceEdge)
    (hMem : edge ∈ fineBackgroundOccurrences input profile hSame
      (fineStablePathEquiv input profile hSame path)) :
    data.sourceEdge (largestTarget input profile) edge.1.2 ∈
      fineOldBackgroundOccurrences input profile path := by
  let candidate := fineCandidate input profile hSame
  have hData := (mem_fineBackgroundOccurrences input profile hSame _ _).mp hMem
  obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hData.1
  have hEdge := eq_newSourceEdge_of_target candidate edge hTarget
  have hNew : ¬ IsDangling candidate.datum (candidate.newSourceEdge edge.1.2) := by
    rw [← hEdge]
    exact hSurvives
  have hOld : ¬ IsDangling data
      (data.sourceEdge (largestTarget input profile) edge.1.2) :=
    (fine_background_new_survives_iff_largest input profile hSame edge.1.2
      hData.2).mp hNew
  have hNewRow : NonDanglingEdge.stablePath
      ⟨candidate.newSourceEdge edge.1.2, hNew⟩ =
        fineStablePathEquiv input profile hSame path :=
    (congrArg NonDanglingEdge.stablePath
      (show (⟨candidate.newSourceEdge edge.1.2, hNew⟩ :
        NonDanglingEdge candidate.datum) = ⟨edge, hSurvives⟩ from
          Subtype.ext hEdge.symm)).trans hRow
  refine (mem_fineOldBackgroundOccurrences input profile path _).mpr
    ⟨(mem_occurrences _ _ _).mpr ⟨⟨hOld, ?_⟩, rfl⟩, ?_⟩
  · apply (fineStablePathEquiv input profile hSame).injective
    exact (fineStablePathEquiv_mk input profile hSame
      ⟨data.sourceEdge (largestTarget input profile) edge.1.2, hOld⟩).trans
      ((fine_background_new_stablePath_eq_largest input profile hSame
        edge.1.2 hData.2 hOld).symm.trans hNewRow)
  · intro hSelected
    apply hData.2
    exact hSelected.trans
      ((StableLocalProperties.refines_of_mem_incidentEdges data
        (largestTarget_mem input profile)).rel
          ((data.edgePartition (largestTarget input profile)).rel_repr_left edge.1.2))

theorem fine_new_old_roundtrip (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath data)
    (edge : (fineCandidate input profile hSame).datum.SourceEdge)
    (hMem : edge ∈ fineBackgroundOccurrences input profile hSame
      (fineStablePathEquiv input profile hSame path)) :
    (fineCandidate input profile hSame).newSourceEdge
        (data.sourceEdge (largestTarget input profile) edge.1.2).1.2 = edge := by
  let candidate := fineCandidate input profile hSame
  have hData := (mem_fineBackgroundOccurrences input profile hSame _ _).mp hMem
  have hTarget := ((mem_occurrences _ _ _).mp hData.1).2
  have hEdge := eq_newSourceEdge_of_target candidate edge hTarget
  exact (fine_background_new_eq_of_largest_source_eq input profile hSame edge.1.2
    (data.sourceEdge (largestTarget input profile) edge.1.2).1.2 hData.2
      (GluingDatum.sourceEdge_self data
        (data.sourceEdge (largestTarget input profile) edge.1.2))).trans hEdge.symm

theorem fine_new_of_old_injective (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath data) (first second : data.SourceEdge)
    (hFirst : first ∈ fineOldBackgroundOccurrences input profile path)
    (hSecond : second ∈ fineOldBackgroundOccurrences input profile path)
    (hEqual : (fineCandidate input profile hSame).newSourceEdge first.1.2 =
      (fineCandidate input profile hSame).newSourceEdge second.1.2) :
    first = second := by
  have hFirstData := (mem_fineOldBackgroundOccurrences input profile path first).mp
    hFirst
  have hSecondData := (mem_fineOldBackgroundOccurrences input profile path second).mp
    hSecond
  have hFirstTarget := ((mem_occurrences _ _ _).mp hFirstData.1).2
  have hSecondTarget := ((mem_occurrences _ _ _).mp hSecondData.1).2
  have hNewRepr := congrArg
    (fun edge : (fineCandidate input profile hSame).datum.SourceEdge ↦ edge.1.2)
    hEqual
  have hNewRel : (finePastedResolution input profile hSame).newEdge.Rel
      first.1.2 second.1.2 := hNewRepr
  have hFineRel : (largestPartition input profile).Rel first.1.2 second.1.2 := by
    apply (largestPartition input profile).mem_block_iff _ _ |>.mp
    rw [← fine_background_newEdge_block input profile hSame first.1.2 hFirstData.2,
      (finePastedResolution input profile hSame).newEdge.mem_block_iff]
    exact hNewRel
  apply Subtype.ext
  apply Prod.ext
  · exact hFirstTarget.trans hSecondTarget.symm
  · have hFirstRepr : (largestPartition input profile).repr first.1.2 = first.1.2 := by
      change (data.edgePartition (largestTarget input profile)).repr first.1.2 = first.1.2
      rw [← hFirstTarget]
      exact first.2
    have hSecondRepr : (largestPartition input profile).repr second.1.2 = second.1.2 := by
      change (data.edgePartition (largestTarget input profile)).repr second.1.2 = second.1.2
      rw [← hSecondTarget]
      exact second.2
    exact hFirstRepr.symm.trans (hFineRel.trans hSecondRepr)

theorem fine_background_index_eq (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath data) (edge : data.SourceEdge)
    (hMem : edge ∈ fineOldBackgroundOccurrences input profile path) :
    (fineCandidate input profile hSame).datum.sourceEdgeIndex
        ((fineCandidate input profile hSame).newSourceEdge edge.1.2) =
      data.sourceEdgeIndex edge := by
  have hData := (mem_fineOldBackgroundOccurrences input profile path edge).mp hMem
  have hTarget := ((mem_occurrences _ _ _).mp hData.1).2
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge]
  change (finePastedResolution input profile hSame).newEdge.blockCard edge.1.2 =
    (data.edgePartition edge.1.1).blockCard edge.1.2
  unfold SheetPartition.blockCard
  rw [fine_background_newEdge_block input profile hSame edge.1.2 hData.2]
  change ((data.edgePartition (largestTarget input profile)).block edge.1.2).card =
    ((data.edgePartition edge.1.1).block edge.1.2).card
  rw [hTarget]

/-- The background part of `M⁽²⁾`'s new column is a term-by-term reindexing of
the original largest-direction background fibre. -/
theorem fine_backgroundColumn_eq_sum_old (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath data) :
    fineBackgroundColumn input profile hSame
        (fineStablePathEquiv input profile hSame path) =
      ∑ edge ∈ fineOldBackgroundOccurrences input profile path,
        (1 : ℚ) / data.sourceEdgeIndex edge := by
  classical
  symm
  unfold fineBackgroundColumn
  refine Finset.sum_bij
    (fun edge _ ↦ (fineCandidate input profile hSame).newSourceEdge edge.1.2)
    ?_ ?_ ?_ ?_
  · exact fun edge hEdge ↦ fine_new_mem_of_old_mem input profile hSame path edge hEdge
  · exact fun first hFirst second hSecond hEqual ↦
      fine_new_of_old_injective input profile hSame path first second hFirst hSecond
        hEqual
  · intro edge hEdge
    exact ⟨_, fine_old_mem_of_new_mem input profile hSame path edge hEdge,
      fine_new_old_roundtrip input profile hSame path edge hEdge⟩
  · intro edge hEdge
    rw [fine_background_index_eq input profile hSame path edge hEdge]

/-- **Figure 30's `c⁽²⁾` column on the source's own stable rows.**  The two
selected coefficients are `1/k₂` on `e₂`'s row and `1/k₃` on `e₃`'s row — kept
as two separate indicator terms, since nothing here asserts that those two rows
are distinct — and the residual term is the exact old largest-direction
background sum. -/
theorem fine_matrix_new_on_old_row (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (path : StablePath data) :
    matrix (fineCandidate input profile hSame).datum
        (fineStablePathEquiv input profile hSame path)
        (occurrenceEquiv target wall (fineCandidate input profile hSame).right none) =
      (if path = NonDanglingEdge.stablePath
          ⟨profile.first.1, first_survives input profile⟩ then
        (1 : ℚ) / data.sourceEdgeIndex profile.first.1 else 0) +
      (if path = NonDanglingEdge.stablePath
          ⟨profile.second.1, second_survives input profile⟩ then
        (1 : ℚ) / data.sourceEdgeIndex profile.second.1 else 0) +
        ∑ edge ∈ fineOldBackgroundOccurrences input profile path,
          (1 : ℚ) / data.sourceEdgeIndex edge := by
  classical
  rw [fine_matrix_new input profile hSame,
    fine_backgroundColumn_eq_sum_old input profile hSame]
  have hRetFirst : retainedEdge (fineCandidate input profile hSame) input.valid.1
      ⟨profile.first.1, first_survives input profile⟩ =
        fineRetainedDoubled input profile hSame profile.first.1.1.2
          (incident_wall_rel input profile.first) :=
    Subtype.ext (fineRetainedDoubled_first input profile hSame).symm
  have hRetSecond : retainedEdge (fineCandidate input profile hSame) input.valid.1
      ⟨profile.second.1, second_survives input profile⟩ =
        fineRetainedDoubled input profile hSame profile.second.1.1.2
          (incident_wall_rel input profile.second) :=
    Subtype.ext (fineRetainedDoubled_second input profile hSame).symm
  have hFirstRow : fineStablePathEquiv input profile hSame
      (NonDanglingEdge.stablePath ⟨profile.first.1, first_survives input profile⟩) =
        (fineNew input profile hSame profile.first.1.1.2
          (incident_wall_rel input profile.first)).stablePath :=
    (fineStablePathEquiv_mk input profile hSame
      ⟨profile.first.1, first_survives input profile⟩).trans
      ((congrArg NonDanglingEdge.stablePath hRetFirst).trans
        (fine_new_stablePath_eq_doubled input profile hSame profile.first.1.1.2
          (incident_wall_rel input profile.first)).symm)
  have hSecondRow : fineStablePathEquiv input profile hSame
      (NonDanglingEdge.stablePath ⟨profile.second.1, second_survives input profile⟩) =
        (fineNew input profile hSame profile.second.1.1.2
          (incident_wall_rel input profile.second)).stablePath :=
    (fineStablePathEquiv_mk input profile hSame
      ⟨profile.second.1, second_survives input profile⟩).trans
      ((congrArg NonDanglingEdge.stablePath hRetSecond).trans
        (fine_new_stablePath_eq_doubled input profile hSame profile.second.1.1.2
          (incident_wall_rel input profile.second)).symm)
  have hIffFirst : fineStablePathEquiv input profile hSame path =
      (fineNew input profile hSame profile.first.1.1.2
        (incident_wall_rel input profile.first)).stablePath ↔
        path = NonDanglingEdge.stablePath
          ⟨profile.first.1, first_survives input profile⟩ := by
    constructor
    · intro hPath
      exact (fineStablePathEquiv input profile hSame).injective
        (hPath.trans hFirstRow.symm)
    · intro hPath
      exact (congrArg (fineStablePathEquiv input profile hSame) hPath).trans hFirstRow
  have hIffSecond : fineStablePathEquiv input profile hSame path =
      (fineNew input profile hSame profile.second.1.1.2
        (incident_wall_rel input profile.second)).stablePath ↔
        path = NonDanglingEdge.stablePath
          ⟨profile.second.1, second_survives input profile⟩ := by
    constructor
    · intro hPath
      exact (fineStablePathEquiv input profile hSame).injective
        (hPath.trans hSecondRow.symm)
    · intro hPath
      exact (congrArg (fineStablePathEquiv input profile hSame) hPath).trans hSecondRow
  simp only [hIffFirst, hIffSecond]


/-! ## The stable incidence graph of `M⁽¹⁾`

Here the nd2 template changes shape for the last time.  In nd2 the
distinguished source vertex is divalent, so *every* old branch above the wall
is a background block and moves to the fresh endpoint.  In nd3 the
distinguished source vertex **is** a branch vertex, and it moves to the
divalent endpoint of the resolution, which is where both members keep their
three flags. -/

/-- The surviving star of the distinguished source vertex is exactly `e₂`,
`e₃`, `e₄`. -/
theorem selected_survivor_cases (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (edge : NonDanglingEdge data)
    (hIncident : Incident data edge.1
      (WallBlock.sourceVertex data wall input.distinguishedBlock)) :
    edge.1 = profile.first.1 ∨ edge.1 = profile.second.1 ∨
      edge.1 = profile.largest.1 := by
  classical
  let incident : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall input.distinguishedBlock) :=
    ⟨edge.1, hIncident⟩
  have hMem := (mem_survivors data input.distinguishedBlock incident).mpr edge.2
  rw [profile.surviving] at hMem
  rcases Finset.mem_insert.mp hMem with hFirst | hRest
  · exact Or.inl (congrArg Subtype.val hFirst)
  · rcases Finset.mem_insert.mp hRest with hSecond | hLargest
    · exact Or.inr (Or.inl (congrArg Subtype.val hSecond))
    · exact Or.inr (Or.inr (congrArg Subtype.val (Finset.mem_singleton.mp hLargest)))

theorem source_first_ne_largest (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    profile.first.1 ≠ profile.largest.1 :=
  fun hEqual ↦ profile.first_ne_largest (Subtype.ext hEqual)

theorem source_second_ne_largest (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    profile.second.1 ≠ profile.largest.1 :=
  fun hEqual ↦ profile.second_ne_largest (Subtype.ext hEqual)

theorem source_first_ne_second (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    profile.first.1 ≠ profile.second.1 :=
  fun hEqual ↦ profile.first_ne_second (Subtype.ext hEqual)

/-- A branch vertex of the source above the wall with a selected sheet is the
distinguished block's source vertex. -/
theorem selected_wall_vertex_eq (input : W3SourceInput data star)
    (vertex : data.SourceVertex) (hAt : vertex.1.1 = wall)
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 vertex.1.2) :
    vertex = WallBlock.sourceVertex data wall input.distinguishedBlock := by
  have hSelf := data.sourceEndpoint_self vertex
  rw [hAt] at hSelf
  exact hSelf.symm.trans (selected_sourceEndpoint_eq input vertex.1.2 hSelected)

/-! ### Branch vertices of `M⁽¹⁾` -/

theorem coarse_left_background_valency_le_two (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    nonDanglingValency (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) sheet) ≤ 2 := by
  have hUpper := NonDanglingValency.nonDanglingValency_le_card_incidentSourceEdge
    (coarseCandidate input profile hSame).datum
    ((coarseCandidate input profile hSame).datum.sourceEndpoint
      (oldVertex target wall) sheet)
  rw [coarse_background_left_card_two input profile hSame sheet hBackground] at hUpper
  exact hUpper

theorem coarse_fresh_selected_valency_two (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    nonDanglingValency (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) sheet) = 2 := by
  have hEndpoint : (coarseCandidate input profile hSame).datum.sourceEndpoint
      (freshVertex target) sheet =
        (coarseCandidate input profile hSame).datum.sourceEndpoint
          (freshVertex target) profile.first.1.1.2 := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (coarsePastedResolution input profile hSame).right.repr sheet =
        (coarsePastedResolution input profile hSame).right.repr profile.first.1.1.2
      apply (coarsePastedResolution input profile hSame).right.mem_block_iff _ _ |>.mp
      rw [coarse_pasted_right_block_selected input profile hSame sheet hSelected]
      exact (data.vertexPartition wall).mem_block_iff _ _ |>.mpr
        (hSelected.symm.trans (incident_wall_rel input profile.first))
  rw [hEndpoint, coarse_right_nonDanglingValency_eq_two input profile hSame]

/-- The distinguished source branch vertex moves to the **divalent** endpoint
of `M⁽¹⁾`. -/
noncomputable def coarseSelectedBranch (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (vertex : BranchVertex data) (_hAt : vertex.1.1.1 = wall)
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1
      vertex.1.1.2) :
    BranchVertex (coarseCandidate input profile hSame).datum :=
  ⟨(coarseCandidate input profile hSame).datum.sourceEndpoint
      (oldVertex target wall) vertex.1.1.2, by
    rw [coarse_left_selected_valency_eq_three input profile hSame vertex.1.1.2
      hSelected]⟩

/-- A background branch above the old wall moves to the corresponding fresh
endpoint. -/
noncomputable def coarseBackgroundFreshBranch (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (vertex : BranchVertex data) (hAt : vertex.1.1.1 = wall)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1
      vertex.1.1.2) :
    BranchVertex (coarseCandidate input profile hSame).datum :=
  ⟨(coarseCandidate input profile hSame).datum.sourceEndpoint
      (freshVertex target) vertex.1.1.2, by
    rw [coarse_nonDanglingValency_background input profile hSame vertex.1.1.2
      hBackground]
    have hSelf := data.sourceEndpoint_self vertex.1
    rw [hAt] at hSelf
    rw [hSelf]
    exact vertex.2⟩

/-- An old branch away from the wall is retained literally. -/
noncomputable def coarseRetainedBranch (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (vertex : BranchVertex data) (hAway : vertex.1.1.1 ≠ wall) :
    BranchVertex (coarseCandidate input profile hSame).datum :=
  ⟨retainedVertex (coarseCandidate input profile hSame) vertex.1, by
    rw [nonDanglingValency_retainedVertex _ input.valid
      (coarseCandidate_sourceGenus input profile hSame) vertex.1 hAway]
    exact vertex.2⟩

noncomputable def coarseBranchVertexMap (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    BranchVertex data → BranchVertex (coarseCandidate input profile hSame).datum := by
  classical
  exact fun vertex ↦ if hAt : vertex.1.1.1 = wall then
      (if hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1
          vertex.1.1.2 then
        coarseSelectedBranch input profile hSame vertex hAt hSelected
      else coarseBackgroundFreshBranch input profile hSame vertex hAt hSelected)
    else coarseRetainedBranch input profile hSame vertex hAt

theorem coarseBranchVertexMap_of_selected (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (vertex : BranchVertex data) (hAt : vertex.1.1.1 = wall)
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1
      vertex.1.1.2) :
    (coarseBranchVertexMap input profile hSame vertex).1 =
      (coarseCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) vertex.1.1.2 := by
  classical
  unfold coarseBranchVertexMap
  rw [dif_pos hAt, dif_pos hSelected]
  rfl

theorem coarseBranchVertexMap_of_background (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (vertex : BranchVertex data) (hAt : vertex.1.1.1 = wall)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1
      vertex.1.1.2) :
    (coarseBranchVertexMap input profile hSame vertex).1 =
      (coarseCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) vertex.1.1.2 := by
  classical
  unfold coarseBranchVertexMap
  rw [dif_pos hAt, dif_neg hBackground]
  rfl

theorem coarseBranchVertexMap_of_away (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (vertex : BranchVertex data) (hAway : vertex.1.1.1 ≠ wall) :
    (coarseBranchVertexMap input profile hSame vertex).1 =
      retainedVertex (coarseCandidate input profile hSame) vertex.1 := by
  classical
  unfold coarseBranchVertexMap
  rw [dif_neg hAway]
  rfl

theorem coarse_fresh_endpoint_reflects_background (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (first second : Fin degree)
    (hFirst : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 first)
    (hEqual : (coarseCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) first =
      (coarseCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) second) :
    data.sourceEndpoint wall first = data.sourceEndpoint wall second := by
  have hRight : (coarsePastedResolution input profile hSame).right.Rel first second := by
    change (coarsePastedResolution input profile hSame).right.repr first =
      (coarsePastedResolution input profile hSame).right.repr second
    exact congrArg
      (fun vertex : (coarseCandidate input profile hSame).datum.SourceVertex ↦
        vertex.1.2) hEqual
  have hWall : (data.vertexPartition wall).Rel first second := by
    apply (data.vertexPartition wall).mem_block_iff _ _ |>.mp
    rw [← coarse_background_right_block input profile hSame first hFirst,
      (coarsePastedResolution input profile hSame).right.mem_block_iff]
    exact hRight
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact hWall

theorem coarse_fresh_endpoint_wall_repr (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (coarseCandidate input profile hSame).datum.sourceEndpoint (freshVertex target)
        ((data.vertexPartition wall).repr sheet) =
      (coarseCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) sheet := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (coarsePastedResolution input profile hSame).right.repr
      ((data.vertexPartition wall).repr sheet) =
        (coarsePastedResolution input profile hSame).right.repr sheet
    symm
    apply (coarsePastedResolution input profile hSame).right.mem_block_iff _ _ |>.mp
    rw [coarse_background_right_block input profile hSame sheet hBackground]
    exact (data.vertexPartition wall).mem_block_iff _ _ |>.mpr
      ((data.vertexPartition wall).rel_repr_right sheet)

theorem coarseBranchVertexMap_injective (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    Function.Injective (coarseBranchVertexMap input profile hSame) := by
  classical
  intro first second hEqual
  let candidate := coarseCandidate input profile hSame
  by_cases hFirst : first.1.1.1 = wall
  · by_cases hSecond : second.1.1.1 = wall
    · by_cases hFirstSelected : (data.vertexPartition wall).Rel
          input.distinguishedBlock.1 first.1.1.2
      · by_cases hSecondSelected : (data.vertexPartition wall).Rel
            input.distinguishedBlock.1 second.1.1.2
        · apply Subtype.ext
          exact (selected_wall_vertex_eq input first.1 hFirst hFirstSelected).trans
            (selected_wall_vertex_eq input second.1 hSecond hSecondSelected).symm
        · have hValues := (coarseBranchVertexMap_of_selected input profile hSame
            first hFirst hFirstSelected).symm.trans
            ((congrArg Subtype.val hEqual).trans
              (coarseBranchVertexMap_of_background input profile hSame second hSecond
                hSecondSelected))
          have hTargets := congrArg
            (fun vertex : candidate.datum.SourceVertex ↦ vertex.1.1) hValues
          cases hTargets
      · by_cases hSecondSelected : (data.vertexPartition wall).Rel
            input.distinguishedBlock.1 second.1.1.2
        · have hValues := (coarseBranchVertexMap_of_background input profile hSame
            first hFirst hFirstSelected).symm.trans
            ((congrArg Subtype.val hEqual).trans
              (coarseBranchVertexMap_of_selected input profile hSame second hSecond
                hSecondSelected))
          have hTargets := congrArg
            (fun vertex : candidate.datum.SourceVertex ↦ vertex.1.1) hValues
          cases hTargets
        · apply Subtype.ext
          have hFresh := (coarseBranchVertexMap_of_background input profile hSame
            first hFirst hFirstSelected).symm.trans
            ((congrArg Subtype.val hEqual).trans
              (coarseBranchVertexMap_of_background input profile hSame second hSecond
                hSecondSelected))
          have hOld := coarse_fresh_endpoint_reflects_background input profile hSame
            first.1.1.2 second.1.1.2 hFirstSelected hFresh
          have hFirstSelf := data.sourceEndpoint_self first.1
          have hSecondSelf := data.sourceEndpoint_self second.1
          rw [hFirst] at hFirstSelf
          rw [hSecond] at hSecondSelf
          exact hFirstSelf.symm.trans (hOld.trans hSecondSelf)
    · have hAway := (coarseBranchVertexMap_of_away input profile hSame second hSecond)
      by_cases hFirstSelected : (data.vertexPartition wall).Rel
          input.distinguishedBlock.1 first.1.1.2
      · have hValues := (coarseBranchVertexMap_of_selected input profile hSame
          first hFirst hFirstSelected).symm.trans
          ((congrArg Subtype.val hEqual).trans hAway)
        have hTargets := Sum.inl.inj (congrArg
          (fun vertex : candidate.datum.SourceVertex ↦ vertex.1.1) hValues)
        exact (hSecond hTargets.symm).elim
      · have hValues := (coarseBranchVertexMap_of_background input profile hSame
          first hFirst hFirstSelected).symm.trans
          ((congrArg Subtype.val hEqual).trans hAway)
        have hTargets := congrArg
          (fun vertex : candidate.datum.SourceVertex ↦ vertex.1.1) hValues
        cases hTargets
  · by_cases hSecond : second.1.1.1 = wall
    · have hAway := (coarseBranchVertexMap_of_away input profile hSame first hFirst)
      by_cases hSecondSelected : (data.vertexPartition wall).Rel
          input.distinguishedBlock.1 second.1.1.2
      · have hValues := hAway.symm.trans ((congrArg Subtype.val hEqual).trans
          (coarseBranchVertexMap_of_selected input profile hSame second hSecond
            hSecondSelected))
        have hTargets := Sum.inl.inj (congrArg
          (fun vertex : candidate.datum.SourceVertex ↦ vertex.1.1) hValues)
        exact (hFirst hTargets).elim
      · have hValues := hAway.symm.trans ((congrArg Subtype.val hEqual).trans
          (coarseBranchVertexMap_of_background input profile hSame second hSecond
            hSecondSelected))
        have hTargets := congrArg
          (fun vertex : candidate.datum.SourceVertex ↦ vertex.1.1) hValues
        cases hTargets
    · apply Subtype.ext
      apply retainedVertex_injective_away candidate first.1 second.1 hFirst hSecond
      exact (coarseBranchVertexMap_of_away input profile hSame first hFirst).symm.trans
        ((congrArg Subtype.val hEqual).trans
          (coarseBranchVertexMap_of_away input profile hSame second hSecond))

theorem coarseBranchVertexMap_surjective (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    Function.Surjective (coarseBranchVertexMap input profile hSame) := by
  classical
  intro vertex
  let candidate := coarseCandidate input profile hSame
  cases hPlace : vertex.1.1.1 with
  | inl place =>
      by_cases hAt : place = wall
      · subst place
        have hSelf := candidate.datum.sourceEndpoint_self vertex.1
        rw [hPlace] at hSelf
        change (coarseCandidate input profile hSame).datum.sourceEndpoint
          (oldVertex target wall) vertex.1.1.2 = vertex.1 at hSelf
        by_cases hSelected : (data.vertexPartition wall).Rel
            input.distinguishedBlock.1 vertex.1.1.2
        · have hThree : 3 ≤ nonDanglingValency data
              (WallBlock.sourceVertex data wall input.distinguishedBlock) := by
            rw [source_nonDanglingValency_eq_three input profile]
          let selectedBranch : BranchVertex data :=
            ⟨WallBlock.sourceVertex data wall input.distinguishedBlock, hThree⟩
          have hAt' : selectedBranch.1.1.1 = wall := rfl
          have hSel : (data.vertexPartition wall).Rel input.distinguishedBlock.1
              selectedBranch.1.1.2 :=
            (data.vertexPartition wall).rel_repr_right input.distinguishedBlock.1
          refine ⟨selectedBranch, ?_⟩
          apply Subtype.ext
          rw [coarseBranchVertexMap_of_selected input profile hSame selectedBranch
            hAt' hSel]
          exact (coarse_left_endpoint_eq_of_wall_rel input profile hSame _ _ hSel
            (hSel.symm.trans hSelected)).trans hSelf
        · have hLe := coarse_left_background_valency_le_two input profile hSame
            vertex.1.1.2 hSelected
          rw [hSelf] at hLe
          have hGe := vertex.2
          change 3 ≤ nonDanglingValency (coarseCandidate input profile hSame).datum
            vertex.1 at hGe
          omega
      · obtain ⟨old, hOldTarget, hRetained⟩ :=
          exists_retainedVertex_of_target candidate vertex.1 place hAt hPlace
        have hOldAway : old.1.1 ≠ wall := by
          intro hOldWall
          exact hAt (hOldTarget.symm.trans hOldWall)
        have hValency := nonDanglingValency_retainedVertex candidate input.valid
          (coarseCandidate_sourceGenus input profile hSame) old hOldAway
        rw [hRetained] at hValency
        have hOldBranch : 3 ≤ nonDanglingValency data old := by
          rw [← hValency]
          exact vertex.2
        let oldBranch : BranchVertex data := ⟨old, hOldBranch⟩
        refine ⟨oldBranch, ?_⟩
        apply Subtype.ext
        exact (coarseBranchVertexMap_of_away input profile hSame oldBranch
          hOldAway).trans hRetained
  | inr point =>
      cases point
      have hSelf := candidate.datum.sourceEndpoint_self vertex.1
      rw [hPlace] at hSelf
      change (coarseCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) vertex.1.1.2 = vertex.1 at hSelf
      by_cases hSelected : (data.vertexPartition wall).Rel
          input.distinguishedBlock.1 vertex.1.1.2
      · have hTwo := coarse_fresh_selected_valency_two input profile hSame
          vertex.1.1.2 hSelected
        rw [hSelf] at hTwo
        have hGe := vertex.2
        change 3 ≤ nonDanglingValency (coarseCandidate input profile hSame).datum
          vertex.1 at hGe
        omega
      · have hOldBranch : 3 ≤ nonDanglingValency data
            (data.sourceEndpoint wall vertex.1.1.2) := by
          have hValency := coarse_nonDanglingValency_background input profile hSame
            vertex.1.1.2 hSelected
          rw [← hValency]
          exact hSelf.symm ▸ vertex.2
        let oldBranch : BranchVertex data :=
          ⟨data.sourceEndpoint wall vertex.1.1.2, hOldBranch⟩
        have hAt : oldBranch.1.1.1 = wall := rfl
        have hBack : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1
            oldBranch.1.1.2 := by
          intro hRel
          exact hSelected (hRel.trans
            ((data.vertexPartition wall).rel_repr_left vertex.1.1.2))
        refine ⟨oldBranch, ?_⟩
        apply Subtype.ext
        rw [coarseBranchVertexMap_of_background input profile hSame oldBranch hAt hBack]
        exact (coarse_fresh_endpoint_wall_repr input profile hSame vertex.1.1.2
          hSelected).trans hSelf

/-- The branch-vertex equivalence for `M⁽¹⁾`. -/
noncomputable def coarseBranchVertexEquiv (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    BranchVertex data ≃ BranchVertex (coarseCandidate input profile hSame).datum :=
  Equiv.ofBijective (coarseBranchVertexMap input profile hSame)
    ⟨coarseBranchVertexMap_injective input profile hSame,
      coarseBranchVertexMap_surjective input profile hSame⟩

@[simp] theorem coarseBranchVertexEquiv_apply (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (vertex : BranchVertex data) :
    coarseBranchVertexEquiv input profile hSame vertex =
      coarseBranchVertexMap input profile hSame vertex := rfl

/-! ### Incidence multiplicities of `M⁽¹⁾` -/

noncomputable def coarseBackgroundReplaceEdge (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (old : NonDanglingEdge data)
    (hIncident : Incident data old.1 (data.sourceEndpoint wall sheet)) :
    NonDanglingEdge (coarseCandidate input profile hSame).datum :=
  ⟨coarseBackgroundReplace input profile hSame old.1, by
    have hOldMem : old.1 ∈ nonDanglingIncident data (data.sourceEndpoint wall sheet) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨old.2, hIncident⟩
    have hNewMem := (coarseBackgroundReplace_mem_iff input profile hSame sheet
      hBackground old.1).mpr hOldMem
    exact (mem_nonDanglingIncident _ _ _).mp hNewMem |>.1⟩

theorem coarseBackgroundReplaceEdge_incident (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (old : NonDanglingEdge data)
    (hIncident : Incident data old.1 (data.sourceEndpoint wall sheet)) :
    Incident (coarseCandidate input profile hSame).datum
      (coarseBackgroundReplaceEdge input profile hSame sheet hBackground old
        hIncident).1
      ((coarseCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) sheet) := by
  have hOldMem : old.1 ∈ nonDanglingIncident data (data.sourceEndpoint wall sheet) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨old.2, hIncident⟩
  have hNewMem := (coarseBackgroundReplace_mem_iff input profile hSame sheet
    hBackground old.1).mpr hOldMem
  exact (mem_nonDanglingIncident _ _ _).mp hNewMem |>.2

theorem coarseStablePathEquiv_backgroundReplace (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (old : NonDanglingEdge data)
    (hIncident : Incident data old.1 (data.sourceEndpoint wall sheet)) :
    coarseStablePathEquiv input profile hSame old.stablePath =
      (coarseBackgroundReplaceEdge input profile hSame sheet hBackground old
        hIncident).stablePath := by
  by_cases hTarget : old.1.1.1 = profile.first.1.1.1
  · have hWall : (data.vertexPartition wall).Rel sheet old.1.1.2 :=
      wall_rel_of_incident sheet old.1 hIncident
    have hOldBackground : ¬(data.vertexPartition wall).Rel
        input.distinguishedBlock.1 old.1.1.2 := by
      intro hSelected
      exact hBackground (hSelected.trans hWall.symm)
    have hCanonical : data.sourceEdge profile.first.1.1.1 old.1.1.2 = old.1 := by
      rw [← hTarget]
      exact GluingDatum.sourceEdge_self data old.1
    have hCanonicalSurvives : ¬ IsDangling data
        (data.sourceEdge profile.first.1.1.1 old.1.1.2) := by
      rw [hCanonical]
      exact old.2
    refine (coarseStablePathEquiv_mk input profile hSame old).trans ?_
    calc
      (retainedEdge (coarseCandidate input profile hSame) input.valid.1 old).stablePath =
          NonDanglingEdge.stablePath
            ⟨(coarseCandidate input profile hSame).oldSourceEdge
                (data.sourceEdge profile.first.1.1.1 old.1.1.2),
              not_isDangling_oldSourceEdge _ input.valid.1 _ hCanonicalSurvives⟩ := by
        apply congrArg NonDanglingEdge.stablePath
        apply Subtype.ext
        exact congrArg (coarseCandidate input profile hSame).oldSourceEdge
          hCanonical.symm
      _ = NonDanglingEdge.stablePath
            ⟨(coarseCandidate input profile hSame).newSourceEdge old.1.1.2,
              (coarse_background_new_survives_iff_doubled input profile hSame
                old.1.1.2 hOldBackground).mpr hCanonicalSurvives⟩ :=
        (coarse_background_new_stablePath_eq_doubled input profile hSame old.1.1.2
          hOldBackground hCanonicalSurvives).symm
      _ = (coarseBackgroundReplaceEdge input profile hSame sheet hBackground old
            hIncident).stablePath := by
        apply congrArg NonDanglingEdge.stablePath
        apply Subtype.ext
        exact (coarseBackgroundReplace_of_doubled input profile hSame old.1
          hTarget).symm
  · refine (coarseStablePathEquiv_mk input profile hSame old).trans ?_
    apply congrArg NonDanglingEdge.stablePath
    apply Subtype.ext
    exact (coarseBackgroundReplace_of_ne_doubled input profile hSame old.1
      hTarget).symm

/-- The background wall branch and its fresh image have identical incidence
multiplicity in every stable row.  The bijection is on **flags**, so the two
flags of a stable loop are counted separately. -/
theorem coarse_incidenceCount_background (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (path : StablePath data) :
    incidenceCount data (data.sourceEndpoint wall sheet) path =
      incidenceCount (coarseCandidate input profile hSame).datum
        ((coarseCandidate input profile hSame).datum.sourceEndpoint
          (freshVertex target) sheet)
        (coarseStablePathEquiv input profile hSame path) := by
  classical
  unfold incidenceCount
  apply Finset.card_bij
    (fun edge hEdge ↦ coarseBackgroundReplaceEdge input profile hSame sheet
      hBackground edge
      ((mem_incidentEdges data (data.sourceEndpoint wall sheet) edge).mp
        (Finset.mem_filter.mp hEdge).1))
  · intro edge hEdge
    obtain ⟨hIncident, hRow⟩ := Finset.mem_filter.mp hEdge
    apply Finset.mem_filter.mpr
    refine ⟨(mem_incidentEdges _ _ _).mpr
      (coarseBackgroundReplaceEdge_incident input profile hSame sheet hBackground edge
        ((mem_incidentEdges _ _ _).mp hIncident)), ?_⟩
    rw [← coarseStablePathEquiv_backgroundReplace input profile hSame sheet
      hBackground edge ((mem_incidentEdges _ _ _).mp hIncident), hRow]
  · intro first hFirst second hSecond hEqual
    apply Subtype.ext
    apply coarseBackgroundReplace_injective_on_incidence input profile hSame sheet
      hBackground
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨first.2, (mem_incidentEdges _ _ _).mp (Finset.mem_filter.mp hFirst).1⟩
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨second.2, (mem_incidentEdges _ _ _).mp (Finset.mem_filter.mp hSecond).1⟩
    · exact congrArg Subtype.val hEqual
  · intro edge hEdge
    obtain ⟨hIncident, hRow⟩ := Finset.mem_filter.mp hEdge
    obtain ⟨old, hOldIncident, hReplace, hOldRow⟩ :=
      coarseRowOfEdge_incident_background input profile hSame sheet hBackground edge
        ((mem_incidentEdges _ _ _).mp hIncident)
    have hMapped : coarseBackgroundReplaceEdge input profile hSame sheet hBackground
        old hOldIncident = edge := Subtype.ext hReplace
    have hOldPath : old.stablePath = path := by
      apply (coarseStablePathEquiv input profile hSame).injective
      rw [coarseStablePathEquiv_backgroundReplace input profile hSame sheet
        hBackground old hOldIncident, hMapped, hRow]
    exact ⟨old, Finset.mem_filter.mpr
      ⟨(mem_incidentEdges _ _ _).mpr hOldIncident, hOldPath⟩, hMapped⟩

/-! ### The branch flag dictionary above the distinguished block

The source branch vertex carries `e₂`, `e₃`, `e₄`.  The divalent endpoint of
`M⁽¹⁾` carries `e'`, `e₂`, `e₃`, and `e'` has `e₄`'s row.  The flag bijection
below is therefore `e₄ ↦ e'` and the identity on the other two, and it is a
bijection of **flags**, not of row labels. -/

noncomputable def coarseSelectedFlag (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge data) :
    NonDanglingEdge (coarseCandidate input profile hSame).datum := by
  classical
  exact if edge.1 = profile.largest.1 then coarseAnchorNew input profile hSame
    else retainedEdge (coarseCandidate input profile hSame) input.valid.1 edge

theorem coarseSelectedFlag_of_largest (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge data) (hLargest : edge.1 = profile.largest.1) :
    coarseSelectedFlag input profile hSame edge =
      coarseAnchorNew input profile hSame := by
  classical
  rw [coarseSelectedFlag, if_pos hLargest]

theorem coarseSelectedFlag_of_ne (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge data) (hLargest : edge.1 ≠ profile.largest.1) :
    coarseSelectedFlag input profile hSame edge =
      retainedEdge (coarseCandidate input profile hSame) input.valid.1 edge := by
  classical
  rw [coarseSelectedFlag, if_neg hLargest]

theorem coarseSelectedFlag_incident (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge data)
    (hIncident : Incident data edge.1
      (WallBlock.sourceVertex data wall input.distinguishedBlock)) :
    Incident (coarseCandidate input profile hSame).datum
      (coarseSelectedFlag input profile hSame edge).1
      ((coarseCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) profile.first.1.1.2) := by
  classical
  by_cases hLargest : edge.1 = profile.largest.1
  · rw [coarseSelectedFlag_of_largest input profile hSame edge hLargest]
    exact coarse_anchor_new_incident_left input profile hSame
  · rw [coarseSelectedFlag_of_ne input profile hSame edge hLargest]
    rcases selected_survivor_cases input profile edge hIncident with
      hFirst | hSecond | hL
    · change Incident (coarseCandidate input profile hSame).datum
        ((coarseCandidate input profile hSame).oldSourceEdge edge.1) _
      rw [hFirst]
      exact coarse_first_incident_left input profile hSame
    · change Incident (coarseCandidate input profile hSame).datum
        ((coarseCandidate input profile hSame).oldSourceEdge edge.1) _
      rw [hSecond]
      exact coarse_second_incident_left input profile hSame
    · exact (hLargest hL).elim

theorem coarseSelectedFlag_stablePath (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge data) :
    coarseStablePathEquiv input profile hSame edge.stablePath =
      (coarseSelectedFlag input profile hSame edge).stablePath := by
  classical
  by_cases hLargest : edge.1 = profile.largest.1
  · have hRet : retainedEdge (coarseCandidate input profile hSame) input.valid.1 edge =
        coarseRetainedLargest input profile hSame :=
      Subtype.ext (congrArg (coarseCandidate input profile hSame).oldSourceEdge
        hLargest)
    exact (coarseStablePathEquiv_mk input profile hSame edge).trans
      ((congrArg NonDanglingEdge.stablePath hRet).trans
        ((coarse_anchor_new_stablePath_eq_largest input profile hSame).symm.trans
          (congrArg NonDanglingEdge.stablePath
            (coarseSelectedFlag_of_largest input profile hSame edge hLargest).symm)))
  · exact (coarseStablePathEquiv_mk input profile hSame edge).trans
      (congrArg NonDanglingEdge.stablePath
        (coarseSelectedFlag_of_ne input profile hSame edge hLargest).symm)

/-- The distinguished source branch vertex and the divalent endpoint of `M⁽¹⁾`
have identical incidence multiplicity in every stable row. -/
theorem coarse_incidenceCount_selected (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (path : StablePath data) :
    incidenceCount data
        (WallBlock.sourceVertex data wall input.distinguishedBlock) path =
      incidenceCount (coarseCandidate input profile hSame).datum
        ((coarseCandidate input profile hSame).datum.sourceEndpoint
          (oldVertex target wall) profile.first.1.1.2)
        (coarseStablePathEquiv input profile hSame path) := by
  classical
  unfold incidenceCount
  apply Finset.card_bij (fun edge _ ↦ coarseSelectedFlag input profile hSame edge)
  · intro edge hEdge
    obtain ⟨hIncident, hRow⟩ := Finset.mem_filter.mp hEdge
    apply Finset.mem_filter.mpr
    refine ⟨(mem_incidentEdges _ _ _).mpr
      (coarseSelectedFlag_incident input profile hSame edge
        ((mem_incidentEdges _ _ _).mp hIncident)), ?_⟩
    rw [← coarseSelectedFlag_stablePath input profile hSame edge, hRow]
  · intro first hFirst second hSecond hEqual
    by_cases hFirstLargest : first.1 = profile.largest.1
    · by_cases hSecondLargest : second.1 = profile.largest.1
      · exact Subtype.ext (hFirstLargest.trans hSecondLargest.symm)
      · exfalso
        rw [coarseSelectedFlag_of_largest input profile hSame first hFirstLargest,
          coarseSelectedFlag_of_ne input profile hSame second hSecondLargest] at hEqual
        exact coarse_new_ne_old input profile hSame profile.first.1.1.2 second.1
          (congrArg Subtype.val hEqual)
    · by_cases hSecondLargest : second.1 = profile.largest.1
      · exfalso
        rw [coarseSelectedFlag_of_ne input profile hSame first hFirstLargest,
          coarseSelectedFlag_of_largest input profile hSame second hSecondLargest]
          at hEqual
        exact coarse_new_ne_old input profile hSame profile.first.1.1.2 first.1
          (congrArg Subtype.val hEqual).symm
      · rw [coarseSelectedFlag_of_ne input profile hSame first hFirstLargest,
          coarseSelectedFlag_of_ne input profile hSame second hSecondLargest] at hEqual
        exact retainedEdge_injective _ input.valid.1 hEqual
  · intro edge hEdge
    obtain ⟨hIncident, hRow⟩ := Finset.mem_filter.mp hEdge
    have hStar : edge.1 ∈ nonDanglingIncident (coarseCandidate input profile hSame).datum
        ((coarseCandidate input profile hSame).datum.sourceEndpoint
          (oldVertex target wall) profile.first.1.1.2) :=
      (mem_nonDanglingIncident _ _ _).mpr
        ⟨edge.2, (mem_incidentEdges _ _ _).mp hIncident⟩
    rw [coarse_nonDanglingIncident_left input profile hSame] at hStar
    have hRowOf : ∀ old : NonDanglingEdge data,
        coarseSelectedFlag input profile hSame old = edge → old.stablePath = path := by
      intro old hFlag
      apply (coarseStablePathEquiv input profile hSame).injective
      rw [coarseSelectedFlag_stablePath input profile hSame old, hFlag, hRow]
    rcases Finset.mem_insert.mp hStar with hNew | hRest
    · let old : NonDanglingEdge data := ⟨profile.largest.1, largest_survives input profile⟩
      have hFlag : coarseSelectedFlag input profile hSame old = edge :=
        (coarseSelectedFlag_of_largest input profile hSame old rfl).trans
          (Subtype.ext hNew.symm)
      exact ⟨old, Finset.mem_filter.mpr
        ⟨(mem_incidentEdges _ _ _).mpr profile.largest.2, hRowOf old hFlag⟩, hFlag⟩
    · rcases Finset.mem_insert.mp hRest with hFirst | hSecond
      · let old : NonDanglingEdge data := ⟨profile.first.1, first_survives input profile⟩
        have hFlag : coarseSelectedFlag input profile hSame old = edge :=
          (coarseSelectedFlag_of_ne input profile hSame old
            (source_first_ne_largest input profile)).trans (Subtype.ext hFirst.symm)
        exact ⟨old, Finset.mem_filter.mpr
          ⟨(mem_incidentEdges _ _ _).mpr profile.first.2, hRowOf old hFlag⟩, hFlag⟩
      · let old : NonDanglingEdge data :=
          ⟨profile.second.1, second_survives input profile⟩
        have hFlag : coarseSelectedFlag input profile hSame old = edge :=
          (coarseSelectedFlag_of_ne input profile hSame old
            (source_second_ne_largest input profile)).trans
            (Subtype.ext (Finset.mem_singleton.mp hSecond).symm)
        exact ⟨old, Finset.mem_filter.mpr
          ⟨(mem_incidentEdges _ _ _).mpr profile.second.2, hRowOf old hFlag⟩, hFlag⟩

/-- **`M⁽¹⁾` has the same stable incidence graph as the source.**  Both maps
are the explicit geometric maps proved above. -/
noncomputable def coarseStableGraphEquivalence (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    StableGraphIncidence.Equivalence data
      (coarseCandidate input profile hSame).datum where
  vertex := coarseBranchVertexEquiv input profile hSame
  row := coarseStablePathEquiv input profile hSame
  incidence vertex path := by
    classical
    change incidenceCount data vertex.1 path =
      incidenceCount (coarseCandidate input profile hSame).datum
        (coarseBranchVertexMap input profile hSame vertex).1
        (coarseStablePathEquiv input profile hSame path)
    by_cases hAt : vertex.1.1.1 = wall
    · by_cases hSelected : (data.vertexPartition wall).Rel
          input.distinguishedBlock.1 vertex.1.1.2
      · have hEndpoint : (coarseCandidate input profile hSame).datum.sourceEndpoint
            (oldVertex target wall) vertex.1.1.2 =
            (coarseCandidate input profile hSame).datum.sourceEndpoint
              (oldVertex target wall) profile.first.1.1.2 :=
          (coarse_left_endpoint_eq_of_wall_rel input profile hSame
            profile.first.1.1.2 vertex.1.1.2 (incident_wall_rel input profile.first)
            ((incident_wall_rel input profile.first).symm.trans hSelected)).symm
        rw [coarseBranchVertexMap_of_selected input profile hSame vertex hAt hSelected,
          hEndpoint, selected_wall_vertex_eq input vertex.1 hAt hSelected]
        exact coarse_incidenceCount_selected input profile hSame path
      · rw [coarseBranchVertexMap_of_background input profile hSame vertex hAt
          hSelected]
        have hSelf := data.sourceEndpoint_self vertex.1
        rw [hAt] at hSelf
        exact (congrArg (fun sourceVertex ↦ incidenceCount data sourceVertex path)
          hSelf).symm.trans (coarse_incidenceCount_background input profile hSame
            vertex.1.1.2 hSelected path)
    · rw [coarseBranchVertexMap_of_away input profile hSame vertex hAt]
      exact ResolutionStableIncidence.incidenceCount_retainedVertex
        (coarseCandidate input profile hSame) input.valid
        (coarseCandidate_sourceGenus input profile hSame)
        (coarseStablePathEquiv input profile hSame)
        (coarseStablePathEquiv_mk input profile hSame) vertex.1 hAt path

theorem coarseStableGraphEquivalence_row (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (coarseStableGraphEquivalence input profile hSame).row =
      coarseStablePathEquiv input profile hSame := rfl

theorem coarseStableGraphEquivalence_vertex_apply (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (vertex : BranchVertex data) :
    (coarseStableGraphEquivalence input profile hSame).vertex vertex =
      coarseBranchVertexMap input profile hSame vertex := rfl

theorem coarse_hasPathEnds (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (hEnds : HasPathEnds data) :
    HasPathEnds (coarseCandidate input profile hSame).datum :=
  (coarseStableGraphEquivalence input profile hSame).hasPathEnds input.valid.1 hEnds

/-! ### Branch vertices of `M⁽²⁾` -/

theorem fine_left_background_valency_le_two (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    nonDanglingValency (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) sheet) ≤ 2 := by
  have hUpper := NonDanglingValency.nonDanglingValency_le_card_incidentSourceEdge
    (fineCandidate input profile hSame).datum
    ((fineCandidate input profile hSame).datum.sourceEndpoint
      (oldVertex target wall) sheet)
  rw [fine_background_left_card_two input profile hSame sheet hBackground] at hUpper
  exact hUpper

theorem fine_fresh_selected_valency_two (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    nonDanglingValency (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) sheet) = 2 :=
  fine_right_nonDanglingValency_eq_two input profile hSame sheet hSelected

/-- The distinguished source branch vertex moves to the **divalent** endpoint
of `M⁽²⁾`. -/
noncomputable def fineSelectedBranch (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (vertex : BranchVertex data) (_hAt : vertex.1.1.1 = wall)
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1
      vertex.1.1.2) :
    BranchVertex (fineCandidate input profile hSame).datum :=
  ⟨(fineCandidate input profile hSame).datum.sourceEndpoint
      (oldVertex target wall) vertex.1.1.2, by
    rw [fine_left_selected_valency_eq_three input profile hSame vertex.1.1.2
      hSelected]⟩

/-- A background branch above the old wall moves to the corresponding fresh
endpoint. -/
noncomputable def fineBackgroundFreshBranch (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (vertex : BranchVertex data) (hAt : vertex.1.1.1 = wall)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1
      vertex.1.1.2) :
    BranchVertex (fineCandidate input profile hSame).datum :=
  ⟨(fineCandidate input profile hSame).datum.sourceEndpoint
      (freshVertex target) vertex.1.1.2, by
    rw [fine_nonDanglingValency_background input profile hSame vertex.1.1.2
      hBackground]
    have hSelf := data.sourceEndpoint_self vertex.1
    rw [hAt] at hSelf
    rw [hSelf]
    exact vertex.2⟩

/-- An old branch away from the wall is retained literally. -/
noncomputable def fineRetainedBranch (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (vertex : BranchVertex data) (hAway : vertex.1.1.1 ≠ wall) :
    BranchVertex (fineCandidate input profile hSame).datum :=
  ⟨retainedVertex (fineCandidate input profile hSame) vertex.1, by
    rw [nonDanglingValency_retainedVertex _ input.valid
      (fineCandidate_sourceGenus input profile hSame) vertex.1 hAway]
    exact vertex.2⟩

noncomputable def fineBranchVertexMap (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    BranchVertex data → BranchVertex (fineCandidate input profile hSame).datum := by
  classical
  exact fun vertex ↦ if hAt : vertex.1.1.1 = wall then
      (if hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1
          vertex.1.1.2 then
        fineSelectedBranch input profile hSame vertex hAt hSelected
      else fineBackgroundFreshBranch input profile hSame vertex hAt hSelected)
    else fineRetainedBranch input profile hSame vertex hAt

theorem fineBranchVertexMap_of_selected (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (vertex : BranchVertex data) (hAt : vertex.1.1.1 = wall)
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1
      vertex.1.1.2) :
    (fineBranchVertexMap input profile hSame vertex).1 =
      (fineCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) vertex.1.1.2 := by
  classical
  unfold fineBranchVertexMap
  rw [dif_pos hAt, dif_pos hSelected]
  rfl

theorem fineBranchVertexMap_of_background (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (vertex : BranchVertex data) (hAt : vertex.1.1.1 = wall)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1
      vertex.1.1.2) :
    (fineBranchVertexMap input profile hSame vertex).1 =
      (fineCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) vertex.1.1.2 := by
  classical
  unfold fineBranchVertexMap
  rw [dif_pos hAt, dif_neg hBackground]
  rfl

theorem fineBranchVertexMap_of_away (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (vertex : BranchVertex data) (hAway : vertex.1.1.1 ≠ wall) :
    (fineBranchVertexMap input profile hSame vertex).1 =
      retainedVertex (fineCandidate input profile hSame) vertex.1 := by
  classical
  unfold fineBranchVertexMap
  rw [dif_neg hAway]
  rfl

theorem fine_fresh_endpoint_reflects_background (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (first second : Fin degree)
    (hFirst : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 first)
    (hEqual : (fineCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) first =
      (fineCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) second) :
    data.sourceEndpoint wall first = data.sourceEndpoint wall second := by
  have hRight : (finePastedResolution input profile hSame).right.Rel first second := by
    change (finePastedResolution input profile hSame).right.repr first =
      (finePastedResolution input profile hSame).right.repr second
    exact congrArg
      (fun vertex : (fineCandidate input profile hSame).datum.SourceVertex ↦
        vertex.1.2) hEqual
  have hWall : (data.vertexPartition wall).Rel first second := by
    apply (data.vertexPartition wall).mem_block_iff _ _ |>.mp
    rw [← fine_background_right_block input profile hSame first hFirst,
      (finePastedResolution input profile hSame).right.mem_block_iff]
    exact hRight
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact hWall

theorem fine_fresh_endpoint_wall_repr (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (fineCandidate input profile hSame).datum.sourceEndpoint (freshVertex target)
        ((data.vertexPartition wall).repr sheet) =
      (fineCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) sheet := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (finePastedResolution input profile hSame).right.repr
      ((data.vertexPartition wall).repr sheet) =
        (finePastedResolution input profile hSame).right.repr sheet
    symm
    apply (finePastedResolution input profile hSame).right.mem_block_iff _ _ |>.mp
    rw [fine_background_right_block input profile hSame sheet hBackground]
    exact (data.vertexPartition wall).mem_block_iff _ _ |>.mpr
      ((data.vertexPartition wall).rel_repr_right sheet)

theorem fineBranchVertexMap_injective (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    Function.Injective (fineBranchVertexMap input profile hSame) := by
  classical
  intro first second hEqual
  let candidate := fineCandidate input profile hSame
  by_cases hFirst : first.1.1.1 = wall
  · by_cases hSecond : second.1.1.1 = wall
    · by_cases hFirstSelected : (data.vertexPartition wall).Rel
          input.distinguishedBlock.1 first.1.1.2
      · by_cases hSecondSelected : (data.vertexPartition wall).Rel
            input.distinguishedBlock.1 second.1.1.2
        · apply Subtype.ext
          exact (selected_wall_vertex_eq input first.1 hFirst hFirstSelected).trans
            (selected_wall_vertex_eq input second.1 hSecond hSecondSelected).symm
        · have hValues := (fineBranchVertexMap_of_selected input profile hSame
            first hFirst hFirstSelected).symm.trans
            ((congrArg Subtype.val hEqual).trans
              (fineBranchVertexMap_of_background input profile hSame second hSecond
                hSecondSelected))
          have hTargets := congrArg
            (fun vertex : candidate.datum.SourceVertex ↦ vertex.1.1) hValues
          cases hTargets
      · by_cases hSecondSelected : (data.vertexPartition wall).Rel
            input.distinguishedBlock.1 second.1.1.2
        · have hValues := (fineBranchVertexMap_of_background input profile hSame
            first hFirst hFirstSelected).symm.trans
            ((congrArg Subtype.val hEqual).trans
              (fineBranchVertexMap_of_selected input profile hSame second hSecond
                hSecondSelected))
          have hTargets := congrArg
            (fun vertex : candidate.datum.SourceVertex ↦ vertex.1.1) hValues
          cases hTargets
        · apply Subtype.ext
          have hFresh := (fineBranchVertexMap_of_background input profile hSame
            first hFirst hFirstSelected).symm.trans
            ((congrArg Subtype.val hEqual).trans
              (fineBranchVertexMap_of_background input profile hSame second hSecond
                hSecondSelected))
          have hOld := fine_fresh_endpoint_reflects_background input profile hSame
            first.1.1.2 second.1.1.2 hFirstSelected hFresh
          have hFirstSelf := data.sourceEndpoint_self first.1
          have hSecondSelf := data.sourceEndpoint_self second.1
          rw [hFirst] at hFirstSelf
          rw [hSecond] at hSecondSelf
          exact hFirstSelf.symm.trans (hOld.trans hSecondSelf)
    · have hAway := (fineBranchVertexMap_of_away input profile hSame second hSecond)
      by_cases hFirstSelected : (data.vertexPartition wall).Rel
          input.distinguishedBlock.1 first.1.1.2
      · have hValues := (fineBranchVertexMap_of_selected input profile hSame
          first hFirst hFirstSelected).symm.trans
          ((congrArg Subtype.val hEqual).trans hAway)
        have hTargets := Sum.inl.inj (congrArg
          (fun vertex : candidate.datum.SourceVertex ↦ vertex.1.1) hValues)
        exact (hSecond hTargets.symm).elim
      · have hValues := (fineBranchVertexMap_of_background input profile hSame
          first hFirst hFirstSelected).symm.trans
          ((congrArg Subtype.val hEqual).trans hAway)
        have hTargets := congrArg
          (fun vertex : candidate.datum.SourceVertex ↦ vertex.1.1) hValues
        cases hTargets
  · by_cases hSecond : second.1.1.1 = wall
    · have hAway := (fineBranchVertexMap_of_away input profile hSame first hFirst)
      by_cases hSecondSelected : (data.vertexPartition wall).Rel
          input.distinguishedBlock.1 second.1.1.2
      · have hValues := hAway.symm.trans ((congrArg Subtype.val hEqual).trans
          (fineBranchVertexMap_of_selected input profile hSame second hSecond
            hSecondSelected))
        have hTargets := Sum.inl.inj (congrArg
          (fun vertex : candidate.datum.SourceVertex ↦ vertex.1.1) hValues)
        exact (hFirst hTargets).elim
      · have hValues := hAway.symm.trans ((congrArg Subtype.val hEqual).trans
          (fineBranchVertexMap_of_background input profile hSame second hSecond
            hSecondSelected))
        have hTargets := congrArg
          (fun vertex : candidate.datum.SourceVertex ↦ vertex.1.1) hValues
        cases hTargets
    · apply Subtype.ext
      apply retainedVertex_injective_away candidate first.1 second.1 hFirst hSecond
      exact (fineBranchVertexMap_of_away input profile hSame first hFirst).symm.trans
        ((congrArg Subtype.val hEqual).trans
          (fineBranchVertexMap_of_away input profile hSame second hSecond))

theorem fineBranchVertexMap_surjective (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    Function.Surjective (fineBranchVertexMap input profile hSame) := by
  classical
  intro vertex
  let candidate := fineCandidate input profile hSame
  cases hPlace : vertex.1.1.1 with
  | inl place =>
      by_cases hAt : place = wall
      · subst place
        have hSelf := candidate.datum.sourceEndpoint_self vertex.1
        rw [hPlace] at hSelf
        change (fineCandidate input profile hSame).datum.sourceEndpoint
          (oldVertex target wall) vertex.1.1.2 = vertex.1 at hSelf
        by_cases hSelected : (data.vertexPartition wall).Rel
            input.distinguishedBlock.1 vertex.1.1.2
        · have hThree : 3 ≤ nonDanglingValency data
              (WallBlock.sourceVertex data wall input.distinguishedBlock) := by
            rw [source_nonDanglingValency_eq_three input profile]
          let selectedBranch : BranchVertex data :=
            ⟨WallBlock.sourceVertex data wall input.distinguishedBlock, hThree⟩
          have hAt' : selectedBranch.1.1.1 = wall := rfl
          have hSel : (data.vertexPartition wall).Rel input.distinguishedBlock.1
              selectedBranch.1.1.2 :=
            (data.vertexPartition wall).rel_repr_right input.distinguishedBlock.1
          refine ⟨selectedBranch, ?_⟩
          apply Subtype.ext
          rw [fineBranchVertexMap_of_selected input profile hSame selectedBranch
            hAt' hSel]
          exact (fine_left_endpoint_eq_of_wall_rel input profile hSame _ _ hSel
            (hSel.symm.trans hSelected)).trans hSelf
        · have hLe := fine_left_background_valency_le_two input profile hSame
            vertex.1.1.2 hSelected
          rw [hSelf] at hLe
          have hGe := vertex.2
          change 3 ≤ nonDanglingValency (fineCandidate input profile hSame).datum
            vertex.1 at hGe
          omega
      · obtain ⟨old, hOldTarget, hRetained⟩ :=
          exists_retainedVertex_of_target candidate vertex.1 place hAt hPlace
        have hOldAway : old.1.1 ≠ wall := by
          intro hOldWall
          exact hAt (hOldTarget.symm.trans hOldWall)
        have hValency := nonDanglingValency_retainedVertex candidate input.valid
          (fineCandidate_sourceGenus input profile hSame) old hOldAway
        rw [hRetained] at hValency
        have hOldBranch : 3 ≤ nonDanglingValency data old := by
          rw [← hValency]
          exact vertex.2
        let oldBranch : BranchVertex data := ⟨old, hOldBranch⟩
        refine ⟨oldBranch, ?_⟩
        apply Subtype.ext
        exact (fineBranchVertexMap_of_away input profile hSame oldBranch
          hOldAway).trans hRetained
  | inr point =>
      cases point
      have hSelf := candidate.datum.sourceEndpoint_self vertex.1
      rw [hPlace] at hSelf
      change (fineCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) vertex.1.1.2 = vertex.1 at hSelf
      by_cases hSelected : (data.vertexPartition wall).Rel
          input.distinguishedBlock.1 vertex.1.1.2
      · have hTwo := fine_fresh_selected_valency_two input profile hSame
          vertex.1.1.2 hSelected
        rw [hSelf] at hTwo
        have hGe := vertex.2
        change 3 ≤ nonDanglingValency (fineCandidate input profile hSame).datum
          vertex.1 at hGe
        omega
      · have hOldBranch : 3 ≤ nonDanglingValency data
            (data.sourceEndpoint wall vertex.1.1.2) := by
          have hValency := fine_nonDanglingValency_background input profile hSame
            vertex.1.1.2 hSelected
          rw [← hValency]
          exact hSelf.symm ▸ vertex.2
        let oldBranch : BranchVertex data :=
          ⟨data.sourceEndpoint wall vertex.1.1.2, hOldBranch⟩
        have hAt : oldBranch.1.1.1 = wall := rfl
        have hBack : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1
            oldBranch.1.1.2 := by
          intro hRel
          exact hSelected (hRel.trans
            ((data.vertexPartition wall).rel_repr_left vertex.1.1.2))
        refine ⟨oldBranch, ?_⟩
        apply Subtype.ext
        rw [fineBranchVertexMap_of_background input profile hSame oldBranch hAt hBack]
        exact (fine_fresh_endpoint_wall_repr input profile hSame vertex.1.1.2
          hSelected).trans hSelf

/-- The branch-vertex equivalence for `M⁽²⁾`. -/
noncomputable def fineBranchVertexEquiv (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    BranchVertex data ≃ BranchVertex (fineCandidate input profile hSame).datum :=
  Equiv.ofBijective (fineBranchVertexMap input profile hSame)
    ⟨fineBranchVertexMap_injective input profile hSame,
      fineBranchVertexMap_surjective input profile hSame⟩

@[simp] theorem fineBranchVertexEquiv_apply (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (vertex : BranchVertex data) :
    fineBranchVertexEquiv input profile hSame vertex =
      fineBranchVertexMap input profile hSame vertex := rfl

/-! ### Incidence multiplicities of `M⁽²⁾` -/

noncomputable def fineBackgroundReplaceEdge (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (old : NonDanglingEdge data)
    (hIncident : Incident data old.1 (data.sourceEndpoint wall sheet)) :
    NonDanglingEdge (fineCandidate input profile hSame).datum :=
  ⟨fineBackgroundReplace input profile hSame old.1, by
    have hOldMem : old.1 ∈ nonDanglingIncident data (data.sourceEndpoint wall sheet) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨old.2, hIncident⟩
    have hNewMem := (fineBackgroundReplace_mem_iff input profile hSame sheet
      hBackground old.1).mpr hOldMem
    exact (mem_nonDanglingIncident _ _ _).mp hNewMem |>.1⟩

theorem fineBackgroundReplaceEdge_incident (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (old : NonDanglingEdge data)
    (hIncident : Incident data old.1 (data.sourceEndpoint wall sheet)) :
    Incident (fineCandidate input profile hSame).datum
      (fineBackgroundReplaceEdge input profile hSame sheet hBackground old
        hIncident).1
      ((fineCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) sheet) := by
  have hOldMem : old.1 ∈ nonDanglingIncident data (data.sourceEndpoint wall sheet) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨old.2, hIncident⟩
  have hNewMem := (fineBackgroundReplace_mem_iff input profile hSame sheet
    hBackground old.1).mpr hOldMem
  exact (mem_nonDanglingIncident _ _ _).mp hNewMem |>.2

theorem fineStablePathEquiv_backgroundReplace (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (old : NonDanglingEdge data)
    (hIncident : Incident data old.1 (data.sourceEndpoint wall sheet)) :
    fineStablePathEquiv input profile hSame old.stablePath =
      (fineBackgroundReplaceEdge input profile hSame sheet hBackground old
        hIncident).stablePath := by
  by_cases hTarget : old.1.1.1 = (largestTarget input profile)
  · have hWall : (data.vertexPartition wall).Rel sheet old.1.1.2 :=
      wall_rel_of_incident sheet old.1 hIncident
    have hOldBackground : ¬(data.vertexPartition wall).Rel
        input.distinguishedBlock.1 old.1.1.2 := by
      intro hSelected
      exact hBackground (hSelected.trans hWall.symm)
    have hCanonical : data.sourceEdge (largestTarget input profile) old.1.1.2 = old.1 := by
      rw [← hTarget]
      exact GluingDatum.sourceEdge_self data old.1
    have hCanonicalSurvives : ¬ IsDangling data
        (data.sourceEdge (largestTarget input profile) old.1.1.2) := by
      rw [hCanonical]
      exact old.2
    refine (fineStablePathEquiv_mk input profile hSame old).trans ?_
    calc
      (retainedEdge (fineCandidate input profile hSame) input.valid.1 old).stablePath =
          NonDanglingEdge.stablePath
            ⟨(fineCandidate input profile hSame).oldSourceEdge
                (data.sourceEdge (largestTarget input profile) old.1.1.2),
              not_isDangling_oldSourceEdge _ input.valid.1 _ hCanonicalSurvives⟩ := by
        apply congrArg NonDanglingEdge.stablePath
        apply Subtype.ext
        exact congrArg (fineCandidate input profile hSame).oldSourceEdge
          hCanonical.symm
      _ = NonDanglingEdge.stablePath
            ⟨(fineCandidate input profile hSame).newSourceEdge old.1.1.2,
              (fine_background_new_survives_iff_largest input profile hSame
                old.1.1.2 hOldBackground).mpr hCanonicalSurvives⟩ :=
        (fine_background_new_stablePath_eq_largest input profile hSame old.1.1.2
          hOldBackground hCanonicalSurvives).symm
      _ = (fineBackgroundReplaceEdge input profile hSame sheet hBackground old
            hIncident).stablePath := by
        apply congrArg NonDanglingEdge.stablePath
        apply Subtype.ext
        exact (fineBackgroundReplace_of_largest input profile hSame old.1
          hTarget).symm
  · refine (fineStablePathEquiv_mk input profile hSame old).trans ?_
    apply congrArg NonDanglingEdge.stablePath
    apply Subtype.ext
    exact (fineBackgroundReplace_of_ne_largest input profile hSame old.1
      hTarget).symm

/-- The background wall branch and its fresh image have identical incidence
multiplicity in every stable row.  The bijection is on **flags**, so the two
flags of a stable loop are counted separately. -/
theorem fine_incidenceCount_background (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (path : StablePath data) :
    incidenceCount data (data.sourceEndpoint wall sheet) path =
      incidenceCount (fineCandidate input profile hSame).datum
        ((fineCandidate input profile hSame).datum.sourceEndpoint
          (freshVertex target) sheet)
        (fineStablePathEquiv input profile hSame path) := by
  classical
  unfold incidenceCount
  apply Finset.card_bij
    (fun edge hEdge ↦ fineBackgroundReplaceEdge input profile hSame sheet
      hBackground edge
      ((mem_incidentEdges data (data.sourceEndpoint wall sheet) edge).mp
        (Finset.mem_filter.mp hEdge).1))
  · intro edge hEdge
    obtain ⟨hIncident, hRow⟩ := Finset.mem_filter.mp hEdge
    apply Finset.mem_filter.mpr
    refine ⟨(mem_incidentEdges _ _ _).mpr
      (fineBackgroundReplaceEdge_incident input profile hSame sheet hBackground edge
        ((mem_incidentEdges _ _ _).mp hIncident)), ?_⟩
    rw [← fineStablePathEquiv_backgroundReplace input profile hSame sheet
      hBackground edge ((mem_incidentEdges _ _ _).mp hIncident), hRow]
  · intro first hFirst second hSecond hEqual
    apply Subtype.ext
    apply fineBackgroundReplace_injective_on_incidence input profile hSame sheet
      hBackground
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨first.2, (mem_incidentEdges _ _ _).mp (Finset.mem_filter.mp hFirst).1⟩
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨second.2, (mem_incidentEdges _ _ _).mp (Finset.mem_filter.mp hSecond).1⟩
    · exact congrArg Subtype.val hEqual
  · intro edge hEdge
    obtain ⟨hIncident, hRow⟩ := Finset.mem_filter.mp hEdge
    obtain ⟨old, hOldIncident, hReplace, hOldRow⟩ :=
      fineRowOfEdge_incident_background input profile hSame sheet hBackground edge
        ((mem_incidentEdges _ _ _).mp hIncident)
    have hMapped : fineBackgroundReplaceEdge input profile hSame sheet hBackground
        old hOldIncident = edge := Subtype.ext hReplace
    have hOldPath : old.stablePath = path := by
      apply (fineStablePathEquiv input profile hSame).injective
      rw [fineStablePathEquiv_backgroundReplace input profile hSame sheet
        hBackground old hOldIncident, hMapped, hRow]
    exact ⟨old, Finset.mem_filter.mpr
      ⟨(mem_incidentEdges _ _ _).mpr hOldIncident, hOldPath⟩, hMapped⟩

/-! ### The branch flag dictionary above the distinguished block

The source branch vertex carries `e₂`, `e₃`, `e₄`.  The divalent endpoint of
`M⁽²⁾` carries `e'`, `e''`, `e₄`, and the two new arms carry `e₂`'s and `e₃`'s
rows.  The flag bijection is therefore `e₂ ↦ e'`, `e₃ ↦ e''`, `e₄ ↦ e₄`, and it
is a bijection of **flags**, not of row labels: nothing here asserts that the
rows of `e₂` and `e₃` are distinct. -/

noncomputable def fineSelectedFlag (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge data) :
    NonDanglingEdge (fineCandidate input profile hSame).datum := by
  classical
  exact if edge.1 = profile.first.1 then
      fineNew input profile hSame profile.first.1.1.2
        (incident_wall_rel input profile.first)
    else if edge.1 = profile.second.1 then
      fineNew input profile hSame profile.second.1.1.2
        (incident_wall_rel input profile.second)
    else retainedEdge (fineCandidate input profile hSame) input.valid.1 edge

theorem fineSelectedFlag_of_first (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge data) (hFirst : edge.1 = profile.first.1) :
    fineSelectedFlag input profile hSame edge =
      fineNew input profile hSame profile.first.1.1.2
        (incident_wall_rel input profile.first) := by
  classical
  rw [fineSelectedFlag, if_pos hFirst]

theorem fineSelectedFlag_of_second (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge data) (hFirst : edge.1 ≠ profile.first.1)
    (hSecond : edge.1 = profile.second.1) :
    fineSelectedFlag input profile hSame edge =
      fineNew input profile hSame profile.second.1.1.2
        (incident_wall_rel input profile.second) := by
  classical
  rw [fineSelectedFlag, if_neg hFirst, if_pos hSecond]

theorem fineSelectedFlag_of_ne (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge data) (hFirst : edge.1 ≠ profile.first.1)
    (hSecond : edge.1 ≠ profile.second.1) :
    fineSelectedFlag input profile hSame edge =
      retainedEdge (fineCandidate input profile hSame) input.valid.1 edge := by
  classical
  rw [fineSelectedFlag, if_neg hFirst, if_neg hSecond]

theorem fineSelectedFlag_incident (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge data)
    (hIncident : Incident data edge.1
      (WallBlock.sourceVertex data wall input.distinguishedBlock)) :
    Incident (fineCandidate input profile hSame).datum
      (fineSelectedFlag input profile hSame edge).1
      ((fineCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) profile.first.1.1.2) := by
  classical
  by_cases hFirst : edge.1 = profile.first.1
  · rw [fineSelectedFlag_of_first input profile hSame edge hFirst]
    exact fine_new_incident_left input profile hSame profile.first.1.1.2
  · by_cases hSecond : edge.1 = profile.second.1
    · rw [fineSelectedFlag_of_second input profile hSame edge hFirst hSecond]
      exact fine_second_new_incident_left input profile hSame
    · rw [fineSelectedFlag_of_ne input profile hSame edge hFirst hSecond]
      rcases selected_survivor_cases input profile edge hIncident with
        hF | hS | hLargest
      · exact (hFirst hF).elim
      · exact (hSecond hS).elim
      · change Incident (fineCandidate input profile hSame).datum
          ((fineCandidate input profile hSame).oldSourceEdge edge.1) _
        rw [hLargest]
        exact fine_largest_incident_left input profile hSame

theorem fineSelectedFlag_stablePath (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (edge : NonDanglingEdge data) :
    fineStablePathEquiv input profile hSame edge.stablePath =
      (fineSelectedFlag input profile hSame edge).stablePath := by
  classical
  by_cases hFirst : edge.1 = profile.first.1
  · have hRet : retainedEdge (fineCandidate input profile hSame) input.valid.1 edge =
        fineRetainedDoubled input profile hSame profile.first.1.1.2
          (incident_wall_rel input profile.first) :=
      Subtype.ext ((congrArg (fineCandidate input profile hSame).oldSourceEdge
        hFirst).trans (fineRetainedDoubled_first input profile hSame).symm)
    exact (fineStablePathEquiv_mk input profile hSame edge).trans
      ((congrArg NonDanglingEdge.stablePath hRet).trans
        ((fine_new_stablePath_eq_doubled input profile hSame profile.first.1.1.2
            (incident_wall_rel input profile.first)).symm.trans
          (congrArg NonDanglingEdge.stablePath
            (fineSelectedFlag_of_first input profile hSame edge hFirst).symm)))
  · by_cases hSecond : edge.1 = profile.second.1
    · have hRet : retainedEdge (fineCandidate input profile hSame) input.valid.1 edge =
          fineRetainedDoubled input profile hSame profile.second.1.1.2
            (incident_wall_rel input profile.second) :=
        Subtype.ext ((congrArg (fineCandidate input profile hSame).oldSourceEdge
          hSecond).trans (fineRetainedDoubled_second input profile hSame).symm)
      exact (fineStablePathEquiv_mk input profile hSame edge).trans
        ((congrArg NonDanglingEdge.stablePath hRet).trans
          ((fine_new_stablePath_eq_doubled input profile hSame profile.second.1.1.2
              (incident_wall_rel input profile.second)).symm.trans
            (congrArg NonDanglingEdge.stablePath
              (fineSelectedFlag_of_second input profile hSame edge hFirst
                hSecond).symm)))
    · exact (fineStablePathEquiv_mk input profile hSame edge).trans
        (congrArg NonDanglingEdge.stablePath
          (fineSelectedFlag_of_ne input profile hSame edge hFirst hSecond).symm)

/-- The distinguished source branch vertex and the divalent endpoint of `M⁽²⁾`
have identical incidence multiplicity in every stable row. -/
theorem fine_incidenceCount_selected (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (path : StablePath data) :
    incidenceCount data
        (WallBlock.sourceVertex data wall input.distinguishedBlock) path =
      incidenceCount (fineCandidate input profile hSame).datum
        ((fineCandidate input profile hSame).datum.sourceEndpoint
          (oldVertex target wall) profile.first.1.1.2)
        (fineStablePathEquiv input profile hSame path) := by
  classical
  unfold incidenceCount
  apply Finset.card_bij (fun edge _ ↦ fineSelectedFlag input profile hSame edge)
  · intro edge hEdge
    obtain ⟨hIncident, hRow⟩ := Finset.mem_filter.mp hEdge
    apply Finset.mem_filter.mpr
    refine ⟨(mem_incidentEdges _ _ _).mpr
      (fineSelectedFlag_incident input profile hSame edge
        ((mem_incidentEdges _ _ _).mp hIncident)), ?_⟩
    rw [← fineSelectedFlag_stablePath input profile hSame edge, hRow]
  · intro first hFirst second hSecond hEqual
    by_cases h1f : first.1 = profile.first.1
    · by_cases h2f : second.1 = profile.first.1
      · exact Subtype.ext (h1f.trans h2f.symm)
      · exfalso
        rw [fineSelectedFlag_of_first input profile hSame first h1f] at hEqual
        by_cases h2s : second.1 = profile.second.1
        · rw [fineSelectedFlag_of_second input profile hSame second h2f h2s] at hEqual
          exact fine_new_first_ne_second input profile hSame (congrArg Subtype.val hEqual)
        · rw [fineSelectedFlag_of_ne input profile hSame second h2f h2s] at hEqual
          exact fine_new_ne_old input profile hSame profile.first.1.1.2 second.1
            (congrArg Subtype.val hEqual)
    · by_cases h1s : first.1 = profile.second.1
      · rw [fineSelectedFlag_of_second input profile hSame first h1f h1s] at hEqual
        by_cases h2f : second.1 = profile.first.1
        · exfalso
          rw [fineSelectedFlag_of_first input profile hSame second h2f] at hEqual
          exact fine_new_first_ne_second input profile hSame
            (congrArg Subtype.val hEqual).symm
        · by_cases h2s : second.1 = profile.second.1
          · exact Subtype.ext (h1s.trans h2s.symm)
          · exfalso
            rw [fineSelectedFlag_of_ne input profile hSame second h2f h2s] at hEqual
            exact fine_new_ne_old input profile hSame profile.second.1.1.2 second.1
              (congrArg Subtype.val hEqual)
      · rw [fineSelectedFlag_of_ne input profile hSame first h1f h1s] at hEqual
        by_cases h2f : second.1 = profile.first.1
        · exfalso
          rw [fineSelectedFlag_of_first input profile hSame second h2f] at hEqual
          exact fine_new_ne_old input profile hSame profile.first.1.1.2 first.1
            (congrArg Subtype.val hEqual).symm
        · by_cases h2s : second.1 = profile.second.1
          · exfalso
            rw [fineSelectedFlag_of_second input profile hSame second h2f h2s] at hEqual
            exact fine_new_ne_old input profile hSame profile.second.1.1.2 first.1
              (congrArg Subtype.val hEqual).symm
          · rw [fineSelectedFlag_of_ne input profile hSame second h2f h2s] at hEqual
            exact retainedEdge_injective _ input.valid.1 hEqual
  · intro edge hEdge
    obtain ⟨hIncident, hRow⟩ := Finset.mem_filter.mp hEdge
    have hStar : edge.1 ∈ nonDanglingIncident (fineCandidate input profile hSame).datum
        ((fineCandidate input profile hSame).datum.sourceEndpoint
          (oldVertex target wall) profile.first.1.1.2) :=
      (mem_nonDanglingIncident _ _ _).mpr
        ⟨edge.2, (mem_incidentEdges _ _ _).mp hIncident⟩
    rw [fine_nonDanglingIncident_left input profile hSame] at hStar
    have hRowOf : ∀ old : NonDanglingEdge data,
        fineSelectedFlag input profile hSame old = edge → old.stablePath = path := by
      intro old hFlag
      apply (fineStablePathEquiv input profile hSame).injective
      rw [fineSelectedFlag_stablePath input profile hSame old, hFlag, hRow]
    rcases Finset.mem_insert.mp hStar with hNewFirst | hRest
    · let old : NonDanglingEdge data := ⟨profile.first.1, first_survives input profile⟩
      have hFlag : fineSelectedFlag input profile hSame old = edge :=
        (fineSelectedFlag_of_first input profile hSame old rfl).trans
          (Subtype.ext hNewFirst.symm)
      exact ⟨old, Finset.mem_filter.mpr
        ⟨(mem_incidentEdges _ _ _).mpr profile.first.2, hRowOf old hFlag⟩, hFlag⟩
    · rcases Finset.mem_insert.mp hRest with hNewSecond | hLargest
      · let old : NonDanglingEdge data :=
          ⟨profile.second.1, second_survives input profile⟩
        have hFlag : fineSelectedFlag input profile hSame old = edge :=
          (fineSelectedFlag_of_second input profile hSame old
            (source_first_ne_second input profile).symm rfl).trans
            (Subtype.ext hNewSecond.symm)
        exact ⟨old, Finset.mem_filter.mpr
          ⟨(mem_incidentEdges _ _ _).mpr profile.second.2, hRowOf old hFlag⟩, hFlag⟩
      · let old : NonDanglingEdge data :=
          ⟨profile.largest.1, largest_survives input profile⟩
        have hFlag : fineSelectedFlag input profile hSame old = edge :=
          (fineSelectedFlag_of_ne input profile hSame old
            (source_first_ne_largest input profile).symm
            (source_second_ne_largest input profile).symm).trans
            (Subtype.ext (Finset.mem_singleton.mp hLargest).symm)
        exact ⟨old, Finset.mem_filter.mpr
          ⟨(mem_incidentEdges _ _ _).mpr profile.largest.2, hRowOf old hFlag⟩, hFlag⟩

/-- **`M⁽²⁾` has the same stable incidence graph as the source.**  Both maps
are the explicit geometric maps proved above. -/
noncomputable def fineStableGraphEquivalence (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    StableGraphIncidence.Equivalence data
      (fineCandidate input profile hSame).datum where
  vertex := fineBranchVertexEquiv input profile hSame
  row := fineStablePathEquiv input profile hSame
  incidence vertex path := by
    classical
    change incidenceCount data vertex.1 path =
      incidenceCount (fineCandidate input profile hSame).datum
        (fineBranchVertexMap input profile hSame vertex).1
        (fineStablePathEquiv input profile hSame path)
    by_cases hAt : vertex.1.1.1 = wall
    · by_cases hSelected : (data.vertexPartition wall).Rel
          input.distinguishedBlock.1 vertex.1.1.2
      · have hEndpoint : (fineCandidate input profile hSame).datum.sourceEndpoint
            (oldVertex target wall) vertex.1.1.2 =
            (fineCandidate input profile hSame).datum.sourceEndpoint
              (oldVertex target wall) profile.first.1.1.2 :=
          (fine_left_endpoint_eq_of_wall_rel input profile hSame
            profile.first.1.1.2 vertex.1.1.2 (incident_wall_rel input profile.first)
            ((incident_wall_rel input profile.first).symm.trans hSelected)).symm
        rw [fineBranchVertexMap_of_selected input profile hSame vertex hAt hSelected,
          hEndpoint, selected_wall_vertex_eq input vertex.1 hAt hSelected]
        exact fine_incidenceCount_selected input profile hSame path
      · rw [fineBranchVertexMap_of_background input profile hSame vertex hAt
          hSelected]
        have hSelf := data.sourceEndpoint_self vertex.1
        rw [hAt] at hSelf
        exact (congrArg (fun sourceVertex ↦ incidenceCount data sourceVertex path)
          hSelf).symm.trans (fine_incidenceCount_background input profile hSame
            vertex.1.1.2 hSelected path)
    · rw [fineBranchVertexMap_of_away input profile hSame vertex hAt]
      exact ResolutionStableIncidence.incidenceCount_retainedVertex
        (fineCandidate input profile hSame) input.valid
        (fineCandidate_sourceGenus input profile hSame)
        (fineStablePathEquiv input profile hSame)
        (fineStablePathEquiv_mk input profile hSame) vertex.1 hAt path

theorem fineStableGraphEquivalence_row (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (fineStableGraphEquivalence input profile hSame).row =
      fineStablePathEquiv input profile hSame := rfl

theorem fineStableGraphEquivalence_vertex_apply (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (vertex : BranchVertex data) :
    (fineStableGraphEquivalence input profile hSame).vertex vertex =
      fineBranchVertexMap input profile hSame vertex := rfl

theorem fine_hasPathEnds (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (hEnds : HasPathEnds data) :
    HasPathEnds (fineCandidate input profile hSame).datum :=
  (fineStableGraphEquivalence input profile hSame).hasPathEnds input.valid.1 hEnds

end DraismaVargas.LocalCases.W3Nd3LimitMatrix
