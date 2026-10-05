module

public import DraismaVargas.LocalCases.W3Nd3SourceCandidates
public import DraismaVargas.LocalCases.W3Nd2EndRows

@[expose] public section

/-!
# Surviving occurrences, stable rows and endpoints of the two Figure 30 members

Source: Draisma--Vargas Part I, case `{w3-r1-nd3-t3}`, Figure 30 and
Equation (4).  `W3Nd3SourceCandidates` builds both members `M⁽¹⁾` (`α = 3`) and
`M⁽²⁾` (`α = 4`), proves them valid and genus-preserving, and reads off
Equation (4)'s three denominators as literal block cardinalities.  This module
determines which occurrences survive the resolution, what the complete
surviving star at each endpoint above the distinguished block is, and which
stable rows the new occurrences join.

## What this module proves

For an actual `W3SourceInput`, an actual `Nd3Profile` and the doubled direction
`hSame`:

* `fine_blocks_cover_wall`, `doubled_sourceEdge_eq`, `doubled_sourceEdge_survives`
  — the doubled direction's two blocks exactly exhaust `A₀`, so *every*
  occurrence of `t₃` above `A₀` is one of the two literal survivors `e₂`, `e₃`.
* `M⁽¹⁾`: `coarse_nonDanglingIncident_right` (the trivalent endpoint's
  surviving pair), `coarse_right_nonDanglingValency_eq_two`,
  `coarse_anchor_new_survives`, `coarse_anchor_new_stablePath_eq_largest`, and
  `coarse_nonDanglingIncident_left` / `coarse_left_nonDanglingValency_eq_three`
  (the divalent endpoint's surviving triple).
* `M⁽²⁾`: `fine_nonDanglingIncident_right` and
  `fine_right_nonDanglingValency_eq_two` at *every* trivalent endpoint above
  `A₀`, `fine_new_survives` for both selected new occurrences,
  `fine_new_stablePath_eq_doubled`, and `fine_nonDanglingIncident_left` /
  `fine_left_nonDanglingValency_eq_three`.
* `source_nonDanglingValency_eq_three`, `coarse_anchor_new_index`,
  `fine_new_first_index`, `fine_new_second_index` — the incoming branch valency
  and Equation (4)'s denominators `k₄ = k₂ + k₃`, `k₂`, `k₃` carried on the
  surviving new rows.

Every endpoint statement is an identity of **occurrence** sets
(`nonDanglingIncident`), i.e. of stable-graph flags, not of sets of stable-row
labels; nothing below asserts that the rows of `e₂` and `e₃` are distinct, so a
stable loop through the branch vertex is not excluded.

## Where the nd2 route transfers, and where it does not

Transferring: the pasted endpoint dictionary, `ResolutionPruning.sourceEdge_cases`,
`LimitChainCore.old_incident_fresh_selected_info` (which is stated for an arbitrary
candidate and block), the `nonDanglingIncident` computation and
`stablePath_eq_of_consecutive`.

Not transferring, and this is the mathematical content of the nd3 case:

* **There is no residual sheet.**  `k₂ + k₃ = |A₀|` makes the doubled direction
  cover `A₀` exactly (`fine_blocks_cover_wall`), where nd2 has `k + 1 = |A₀|`
  and a single leftover sheet.  So `W3Nd2Survival.exists_residualSheet` has no
  nd3 analogue — it is false here — and neither member has a dangling selected
  new occurrence.  `M⁽²⁾` accordingly has **two** surviving new occurrences.
* **Survival of a new occurrence is therefore proved at the opposite endpoint.**
  nd2 uses `M11SplitSurvival.survives_of_trivalent_of_deleted` with the dangling
  residual companion.  Here the subset computation at the trivalent endpoint
  plus `nonDanglingValency_ne_one` does the work
  (`coarse_nonDanglingIncident_right_subset`, `fine_nonDanglingIncident_right_subset`).
* **The divalent endpoint is a branch vertex in both members.**  The incoming
  datum already has non-dangling valency three above `A₀`, and each member keeps
  that vertex trivalent: `M⁽¹⁾` carries `e'`, `e₂`, `e₃` there and `M⁽²⁾`
  carries `e'`, `e''`, `e₄`.  In nd2 the corresponding vertex has valency two,
  which is why the nd2 coarse new edge inherits *both* retained survivors' row;
  here only `coarse_anchor_new_stablePath_eq_largest` holds.

## Two points of comparison with nd2

* nd2's fine member and nd3's fine member have the **same** local shape: both
  are `(fineResolution wall selectedFine).reverse`, so both have `left` equal to the
  wall partition on the selected block — compare
  `W3Nd2FineCandidates.selectedResolution` and its
  `pasted_left_block_selected` with `W3Nd3SourceCandidates.selectedResolution`
  and `fine_pasted_left_block_selected` below.  The real difference is the
  *sizes* of the two induced blocks at the trivalent end, `k`/`1` against
  `k₂`/`k₃`, and hence whether the smaller new occurrence dangles.
* `fine_blockCountWithin_eq_two` is an equality in both cases: nd2 proves the
  same equality (`W3Nd2Survival.fine_blockCountWithin_eq_two`), only one module
  later, because the nd2 coarse Riemann--Hurwitz count at candidate-assembly
  time goes through with `W3Nd2SourceCandidates.fine_blockCountWithin_le_two`.

## Why the hypotheses can hold at once

The hypotheses are exactly those of `W3Nd3SourceCandidates`: an actual
`W3SourceInput`, an actual `Nd3Profile` on its distinguished block, and `hSame`,
the first of the three mutually exclusive alternatives of `Nd3Profile.cases`.
Nothing numerical is assumed: `k₂ + k₃ = |A₀|` and `k₄ = |A₀|` are *derived*
through `Nd3Profile.doubled_direction`. `source_nonDanglingValency_eq_three` is
a consequence of `profile.surviving`, not an added hypothesis.

## What is not here

The retained and new **columns** under these row dictionaries, the background
(nonselected) blocks, the stable lift and row descent, the branch-vertex
equivalences and the limit matrices — the nd3 analogues of `W3Nd2Background`,
`W3Nd2StableLift`, `W3Nd2RowDescent`, `W3Nd2FineRowDescent`,
`W3Nd2CoarseStableGraph`, `W3Nd2FineStableGraph` and the two limit-matrix
modules — are built on top of this file (`W3Nd3LimitMatrix`).  Pairing the two
members into `GlobalCoarseFine.nd3BalancedFamily` would need that family to
accept a reversed fine pattern, as `W3Nd3SourceCandidates` records; nothing
here claims it.
-/
namespace DraismaVargas.LocalCases.W3Nd3StableGraph

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open W3R1SourceProfile ResolutionCoarseFine GlobalCoarseFine
open ResolutionM11 ResolutionPruning ResolutionSurvival
open W3Nd3SourceCandidates
open W3Nd2Survival (oldSourceEdge_incident_old)
open W3Nd2EndRows (old_incident_fresh_selected_info)
open M11SplitSurvival (oldSourceEdge_incident_fresh)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (datum : GluingDatum target degree)
    (vertex : datum.SourceVertex) : DecidableEq (IncidentSourceEdge datum vertex) :=
  Classical.decEq _

/-! ## The doubled direction exactly covers the distinguished block -/

/-- The two surviving occurrences of the doubled direction lie over one wall
block. -/
theorem wall_together (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    (data.vertexPartition wall).Rel profile.first.1.1.2 profile.second.1.1.2 :=
  (incident_wall_rel input profile.first).symm.trans
    (incident_wall_rel input profile.second)

theorem wall_blockCard_first (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (data.vertexPartition wall).blockCard profile.first.1.1.2 =
      data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 := by
  rw [← SheetPartition.blockCard_congr (data.vertexPartition wall)
    (incident_wall_rel input profile.first)]
  exact (profile.doubled_direction hSame).1.symm

/-- **The nd3 analogue of the nd2 residual sheet, and its exact opposite.**
The two blocks that the doubled direction cuts out of the distinguished wall
block already exhaust it: `k₂ + k₃ = |A₀|`.  There is no residual sheet, so no
selected new occurrence dangles in either Figure 30 member. -/
theorem fine_blocks_cover_wall (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (finePartition input profile).block profile.first.1.1.2 ∪
        (finePartition input profile).block profile.second.1.1.2 =
      (data.vertexPartition wall).block profile.first.1.1.2 := by
  classical
  let fine := finePartition input profile
  let coarse := data.vertexPartition wall
  have hFirstSubset : fine.block profile.first.1.1.2 ⊆
      coarse.block profile.first.1.1.2 := by
    intro sheet hSheet
    exact (coarse.mem_block_iff _ _).mpr
      ((fine_refines_wall input profile).rel ((fine.mem_block_iff _ _).mp hSheet))
  have hSecondSubset : fine.block profile.second.1.1.2 ⊆
      coarse.block profile.first.1.1.2 := by
    intro sheet hSheet
    exact (coarse.mem_block_iff _ _).mpr
      ((wall_together input profile).trans
        ((fine_refines_wall input profile).rel ((fine.mem_block_iff _ _).mp hSheet)))
  have hDisjoint : Disjoint (fine.block profile.first.1.1.2)
      (fine.block profile.second.1.1.2) := by
    apply Finset.disjoint_left.mpr
    intro sheet hFirst hSecond
    exact fine_separate input profile hSame
      (((fine.mem_block_iff _ _).mp hFirst).trans
        ((fine.mem_block_iff _ _).mp hSecond).symm)
  apply Finset.eq_of_subset_of_card_le (Finset.union_subset hFirstSubset hSecondSubset)
  rw [Finset.card_union_of_disjoint hDisjoint]
  change coarse.blockCard profile.first.1.1.2 ≤
    fine.blockCard profile.first.1.1.2 + fine.blockCard profile.second.1.1.2
  rw [wall_blockCard_first input profile hSame,
    show fine.blockCard profile.first.1.1.2 = data.sourceEdgeIndex profile.first.1 from
      fine_blockCard_first input profile,
    show fine.blockCard profile.second.1.1.2 = data.sourceEdgeIndex profile.second.1 from
      fine_blockCard_second input profile hSame]

/-- Every sheet of the distinguished block is doubled-direction related to one
of the two survivors. -/
theorem fine_rel_first_or_second (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (finePartition input profile).Rel profile.first.1.1.2 sheet ∨
      (finePartition input profile).Rel profile.second.1.1.2 sheet := by
  have hMem : sheet ∈ (data.vertexPartition wall).block profile.first.1.1.2 :=
    ((data.vertexPartition wall).mem_block_iff _ _).mpr
      ((incident_wall_rel input profile.first).symm.trans hSheet)
  rw [← fine_blocks_cover_wall input profile hSame] at hMem
  rcases Finset.mem_union.mp hMem with hFirst | hSecond
  · exact Or.inl (((finePartition input profile).mem_block_iff _ _).mp hFirst)
  · exact Or.inr (((finePartition input profile).mem_block_iff _ _).mp hSecond)

/-- The canonical doubled-direction occurrence through any sheet of the
distinguished block is one of the two literal survivors. -/
theorem doubled_sourceEdge_eq (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    data.sourceEdge profile.first.1.1.1 sheet = profile.first.1 ∨
      data.sourceEdge profile.first.1.1.1 sheet = profile.second.1 := by
  rcases fine_rel_first_or_second input profile hSame sheet hSheet with hFirst | hSecond
  · left
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (data.edgePartition profile.first.1.1.1).repr sheet = profile.first.1.1.2
      exact hFirst.symm.trans profile.first.1.2
  · right
    apply Subtype.ext
    apply Prod.ext
    · exact hSame
    · change (data.edgePartition profile.first.1.1.1).repr sheet = profile.second.1.1.2
      exact hSecond.symm.trans (second_repr input profile hSame)

/-- Hence every doubled-direction occurrence above the distinguished block
survives. -/
theorem doubled_sourceEdge_survives (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    ¬ IsDangling data (data.sourceEdge profile.first.1.1.1 sheet) := by
  have hSurvives : ∀ edge ∈ survivors data input.distinguishedBlock,
      ¬ IsDangling data (edge : IncidentSourceEdge data
        (WallBlock.sourceVertex data wall input.distinguishedBlock)).1 := by
    intro edge hEdge
    exact (mem_survivors data input.distinguishedBlock edge).mp hEdge
  rcases doubled_sourceEdge_eq input profile hSame sheet hSheet with hFirst | hSecond
  · rw [hFirst]
    exact hSurvives profile.first (by rw [profile.surviving]; simp)
  · rw [hSecond]
    exact hSurvives profile.second (by rw [profile.surviving]; simp)

/-! ## The pasted endpoint dictionary of the two Figure 30 members -/

theorem coarse_pasted_left_block_selected (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (coarsePastedResolution input profile hSame).left.block sheet =
      (data.vertexPartition wall).block sheet := by
  change (LocalResolution.pasteLeft (data.vertexPartition wall)
    (coarseCandidate input profile hSame).resolution
    (coarseCandidate input profile hSame).contracts).block sheet = _
  unfold LocalResolution.pasteLeft
  rw [(data.vertexPartition wall).paste_block]
  rw [coarseCandidate_resolution_selected input profile hSame
    ((data.vertexPartition wall).repr sheet)
    (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  rfl

theorem coarse_pasted_right_block_selected (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (coarsePastedResolution input profile hSame).right.block sheet =
      (data.vertexPartition wall).block sheet := by
  change (LocalResolution.pasteRight (data.vertexPartition wall)
    (coarseCandidate input profile hSame).resolution
    (coarseCandidate input profile hSame).contracts).block sheet = _
  unfold LocalResolution.pasteRight
  rw [(data.vertexPartition wall).paste_block]
  rw [coarseCandidate_resolution_selected input profile hSame
    ((data.vertexPartition wall).repr sheet)
    (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  rfl

/-- `M⁽²⁾` retains the whole distinguished block at its divalent endpoint. -/
theorem fine_pasted_left_block_selected (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (finePastedResolution input profile hSame).left.block sheet =
      (data.vertexPartition wall).block sheet := by
  change (LocalResolution.pasteLeft (data.vertexPartition wall)
    (fineCandidate input profile hSame).resolution
    (fineCandidate input profile hSame).contracts).block sheet = _
  unfold LocalResolution.pasteLeft
  rw [(data.vertexPartition wall).paste_block]
  rw [fineCandidate_resolution_selected input profile hSame
    ((data.vertexPartition wall).repr sheet)
    (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  rfl

/-- `M⁽²⁾` carries the doubled direction's two blocks at its trivalent
endpoint. -/
theorem fine_pasted_right_block_selected (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (finePastedResolution input profile hSame).right.block sheet =
      (finePartition input profile).block sheet := by
  change (LocalResolution.pasteRight (data.vertexPartition wall)
    (fineCandidate input profile hSame).resolution
    (fineCandidate input profile hSame).contracts).block sheet = _
  unfold LocalResolution.pasteRight
  rw [(data.vertexPartition wall).paste_block]
  rw [fineCandidate_resolution_selected input profile hSame
    ((data.vertexPartition wall).repr sheet)
    (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  exact selectedFine_block_eq_fine input profile sheet hSheet

/-! ## The divalent-endpoint counterpart of `old_incident_fresh_selected_info`

`LimitChainCore.old_incident_fresh_selected_info` classifies an old occurrence
incident to a **fresh** selected endpoint.  Both Figure 30 members also need
the same statement at the retained **old** endpoint, which is where the nd3
branch vertex sits.  It is `LimitChainCore.old_incident_old_selected_info`,
kept under its `_local` name because `W3FourSurvival` consumes it. -/

alias old_incident_old_selected_info_local := DraismaVargas.LocalCases.LimitChainCore.old_incident_old_selected_info

/-! ## Old survivors of the distinguished block -/

theorem first_survives (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    ¬ IsDangling data profile.first.1 :=
  (mem_survivors data input.distinguishedBlock profile.first).mp
    (by rw [profile.surviving]; simp)

theorem second_survives (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    ¬ IsDangling data profile.second.1 :=
  (mem_survivors data input.distinguishedBlock profile.second).mp
    (by rw [profile.surviving]; simp)

theorem largest_survives (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    ¬ IsDangling data profile.largest.1 :=
  (mem_survivors data input.distinguishedBlock profile.largest).mp
    (by rw [profile.surviving]; simp)

theorem coarse_old_isDangling_iff (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (edge : data.SourceEdge) :
    IsDangling (coarseCandidate input profile hSame).datum
        ((coarseCandidate input profile hSame).oldSourceEdge edge) ↔
      IsDangling data edge :=
  isDangling_oldSourceEdge_iff _ input.valid
    (coarseCandidate_sourceGenus input profile hSame) edge

theorem fine_old_isDangling_iff (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (edge : data.SourceEdge) :
    IsDangling (fineCandidate input profile hSame).datum
        ((fineCandidate input profile hSame).oldSourceEdge edge) ↔
      IsDangling data edge :=
  isDangling_oldSourceEdge_iff _ input.valid
    (fineCandidate_sourceGenus input profile hSame) edge

/-! ## Side assignment of the three actual target directions -/

theorem coarse_right_doubled (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (coarseCandidate input profile hSame).right profile.first.1.1.1 = false := by
  change W3Nd2SourceCandidates.rightOf profile.first.1.1.1 profile.first.1.1.1 = false
  simp [W3Nd2SourceCandidates.rightOf]

theorem coarse_right_largest (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (coarseCandidate input profile hSame).right
      (largestTarget input profile) = true := by
  change W3Nd2SourceCandidates.rightOf profile.first.1.1.1
    (largestTarget input profile) = true
  simp only [W3Nd2SourceCandidates.rightOf, ne_eq, decide_eq_true_eq]
  exact fun hEq ↦ profile.first_target_ne hEq.symm

theorem coarse_right_third (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (coarseCandidate input profile hSame).right
      (thirdTarget input profile) = true := by
  change W3Nd2SourceCandidates.rightOf profile.first.1.1.1
    (thirdTarget input profile) = true
  simp [W3Nd2SourceCandidates.rightOf, thirdTarget_ne_shared input profile]

/-! ## The coarse member `M⁽¹⁾` -/

theorem coarse_new_ne_old (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (sheet : Fin degree) (edge : data.SourceEdge) :
    (coarseCandidate input profile hSame).newSourceEdge sheet ≠
      (coarseCandidate input profile hSame).oldSourceEdge edge := by
  intro hEqual
  have hTargets := congrArg
    (fun item : (coarseCandidate input profile hSame).datum.SourceEdge ↦ item.1.1)
    hEqual
  have hLabels := (occurrenceEquiv target wall
    (coarseCandidate input profile hSame).right).injective hTargets
  cases hLabels

theorem coarse_left_endpoint_eq_of_wall_rel (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (first second : Fin degree)
    (hFirst : (data.vertexPartition wall).Rel input.distinguishedBlock.1 first)
    (hRel : (data.vertexPartition wall).Rel first second) :
    (coarseCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) first =
      (coarseCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) second := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change ((coarseCandidate input profile hSame).datum.vertexPartition
        (oldVertex target wall)).repr first =
      ((coarseCandidate input profile hSame).datum.vertexPartition
        (oldVertex target wall)).repr second
    rw [show (coarseCandidate input profile hSame).datum.vertexPartition
        (oldVertex target wall) =
          (coarsePastedResolution input profile hSame).left from
      GlobalResolution.expandedVertexPartition_old_wall data wall _]
    have hMem : second ∈ (data.vertexPartition wall).block first :=
      ((data.vertexPartition wall).mem_block_iff first second).mpr hRel
    rw [← coarse_pasted_left_block_selected input profile hSame first hFirst] at hMem
    exact ((coarsePastedResolution input profile hSame).left.mem_block_iff
      first second).mp hMem

theorem coarse_right_endpoint_eq_of_wall_rel (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (first second : Fin degree)
    (hFirst : (data.vertexPartition wall).Rel input.distinguishedBlock.1 first)
    (hRel : (data.vertexPartition wall).Rel first second) :
    (coarseCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) first =
      (coarseCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) second := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (coarsePastedResolution input profile hSame).right.repr first =
      (coarsePastedResolution input profile hSame).right.repr second
    have hMem : second ∈ (data.vertexPartition wall).block first :=
      ((data.vertexPartition wall).mem_block_iff first second).mpr hRel
    rw [← coarse_pasted_right_block_selected input profile hSame first hFirst] at hMem
    exact ((coarsePastedResolution input profile hSame).right.mem_block_iff
      first second).mp hMem

theorem coarse_anchor_new_incident_left (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    Incident (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).newSourceEdge profile.first.1.1.2)
      ((coarseCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) profile.first.1.1.2) :=
  Or.inl (congrArg Prod.fst (GlobalResolution.sourceEnds_newSourceEdge data wall
    (coarseCandidate input profile hSame).right
    (coarsePastedResolution input profile hSame)
    (GlobalAssembly.blockwiseCompatible _ _ _ _ _
      (coarseCandidate input profile hSame).exterior) profile.first.1.1.2))

theorem coarse_anchor_new_incident_right (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    Incident (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).newSourceEdge profile.first.1.1.2)
      ((coarseCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) profile.first.1.1.2) :=
  Or.inr (congrArg Prod.snd (GlobalResolution.sourceEnds_newSourceEdge data wall
    (coarseCandidate input profile hSame).right
    (coarsePastedResolution input profile hSame)
    (GlobalAssembly.blockwiseCompatible _ _ _ _ _
      (coarseCandidate input profile hSame).exterior) profile.first.1.1.2))

theorem coarse_largest_incident_right (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    Incident (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).oldSourceEdge profile.largest.1)
      ((coarseCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) profile.first.1.1.2) := by
  have hIncident := oldSourceEdge_incident_fresh
    (coarseCandidate input profile hSame) (largestTarget input profile)
    (largestTarget_mem input profile) (coarse_right_largest input profile hSame)
    profile.largest.1.1.2
  rw [coarse_right_endpoint_eq_of_wall_rel input profile hSame
    profile.first.1.1.2 profile.largest.1.1.2 (incident_wall_rel input profile.first)
    ((incident_wall_rel input profile.first).symm.trans
      (incident_wall_rel input profile.largest))]
  simpa only [GluingDatum.sourceEdge_self] using hIncident

theorem coarse_largest_survives (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    ¬ IsDangling (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).oldSourceEdge profile.largest.1) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
    (largest_survives input profile)

theorem coarse_new_eq_anchor_of_incident_right (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hIncident : Incident (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).newSourceEdge sheet)
      ((coarseCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) profile.first.1.1.2)) :
    (coarseCandidate input profile hSame).newSourceEdge sheet =
      (coarseCandidate input profile hSame).newSourceEdge profile.first.1.1.2 := by
  let candidate := coarseCandidate input profile hSame
  let pasted := coarsePastedResolution input profile hSame
  have hOutgoing := (incident_iff_target_mem_and_rel candidate.datum
    (candidate.newSourceEdge sheet)
    (candidate.datum.sourceEndpoint (freshVertex target)
      profile.first.1.1.2)).mp hIncident
  change occurrenceEquiv target wall candidate.right none ∈
      GluingDatum.incidentEdges (freshVertex target) ∧
    pasted.right.Rel (pasted.right.repr profile.first.1.1.2)
      (pasted.newEdge.repr sheet) at hOutgoing
  have hRightRel : pasted.right.Rel profile.first.1.1.2
      (pasted.newEdge.repr sheet) :=
    (pasted.right.rel_repr_right profile.first.1.1.2).trans hOutgoing.2
  have hMem : pasted.newEdge.repr sheet ∈
      pasted.right.block profile.first.1.1.2 :=
    (pasted.right.mem_block_iff _ _).mpr hRightRel
  rw [coarse_pasted_right_block_selected input profile hSame profile.first.1.1.2
      (incident_wall_rel input profile.first),
    ← coarse_pasted_newEdge_block_selected input profile hSame profile.first.1.1.2
      (incident_wall_rel input profile.first)] at hMem
  have hNewRel := (pasted.newEdge.mem_block_iff
    profile.first.1.1.2 (pasted.newEdge.repr sheet)).mp hMem
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change pasted.newEdge.repr sheet = pasted.newEdge.repr profile.first.1.1.2
    exact (pasted.newEdge.repr_idem sheet).symm.trans hNewRel.symm

/-- At the trivalent endpoint of `M⁽¹⁾` only the retained largest direction
and the single selected new occurrence can survive. -/
theorem coarse_nonDanglingIncident_right_subset (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    nonDanglingIncident (coarseCandidate input profile hSame).datum
        ((coarseCandidate input profile hSame).datum.sourceEndpoint
          (freshVertex target) profile.first.1.1.2) ⊆
      {(coarseCandidate input profile hSame).newSourceEdge profile.first.1.1.2,
        (coarseCandidate input profile hSame).oldSourceEdge profile.largest.1} := by
  classical
  intro edge hMem
  obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
  rcases sourceEdge_cases (coarseCandidate input profile hSame) edge with
    ⟨old, hOld⟩ | ⟨sheet, hNew⟩
  · subst edge
    have hInfo := old_incident_fresh_selected_info
      (coarseCandidate input profile hSame) input.distinguishedBlock
      profile.first.1.1.2 (incident_wall_rel input profile.first) old hIncident
    have hOldSurvives : ¬ IsDangling data old := fun hDangling ↦
      hSurvives ((coarse_old_isDangling_iff input profile hSame old).mpr hDangling)
    have hProfile := (mem_survivors data input.distinguishedBlock
      ⟨old, hInfo.1⟩).mpr hOldSurvives
    rw [profile.surviving] at hProfile
    have hDoubled : ∀ hTarget : old.1.1 = profile.first.1.1.1, False := by
      intro hTarget
      have hRight := hInfo.2
      rw [hTarget] at hRight
      exact Bool.noConfusion
        (hRight.symm.trans (coarse_right_doubled input profile hSame))
    rcases Finset.mem_insert.mp hProfile with hFirst | hRest
    · exact (hDoubled (congrArg (fun item : IncidentSourceEdge data
        (WallBlock.sourceVertex data wall input.distinguishedBlock) ↦
          item.1.1.1) hFirst)).elim
    · rcases Finset.mem_insert.mp hRest with hSecond | hLargest
      · refine (hDoubled ?_).elim
        exact (congrArg (fun item : IncidentSourceEdge data
          (WallBlock.sourceVertex data wall input.distinguishedBlock) ↦
            item.1.1.1) hSecond).trans hSame.symm
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_singleton.mpr
        exact congrArg (fun item : IncidentSourceEdge data
          (WallBlock.sourceVertex data wall input.distinguishedBlock) ↦
            (coarseCandidate input profile hSame).oldSourceEdge item.1)
          (Finset.mem_singleton.mp hLargest)
  · subst edge
    exact Finset.mem_insert.mpr
      (Or.inl (coarse_new_eq_anchor_of_incident_right input profile hSame sheet
        hIncident))

private theorem coarse_right_pair_card (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    ({(coarseCandidate input profile hSame).newSourceEdge profile.first.1.1.2,
        (coarseCandidate input profile hSame).oldSourceEdge profile.largest.1} :
      Finset (coarseCandidate input profile hSame).datum.SourceEdge).card = 2 :=
  Finset.card_pair (coarse_new_ne_old input profile hSame _ _)

theorem coarse_right_nonDanglingValency_eq_two (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    nonDanglingValency (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) profile.first.1.1.2) = 2 := by
  classical
  have hLe := (Finset.card_le_card
    (coarse_nonDanglingIncident_right_subset input profile hSame)).trans
    (le_of_eq (coarse_right_pair_card input profile hSame))
  have hPos : 0 < (nonDanglingIncident (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) profile.first.1.1.2)).card :=
    Finset.card_pos.mpr ⟨_, (mem_nonDanglingIncident _ _ _).mpr
      ⟨coarse_largest_survives input profile hSame,
        coarse_largest_incident_right input profile hSame⟩⟩
  rw [card_nonDanglingIncident] at hLe hPos
  have hNotOne := NonDanglingValency.nonDanglingValency_ne_one
    (coarseCandidate input profile hSame).datum
    (coarseCandidate_valid input profile hSame).1
    ((coarseCandidate input profile hSame).datum.sourceEndpoint
      (freshVertex target) profile.first.1.1.2)
  omega

/-- The surviving star at the trivalent endpoint of `M⁽¹⁾`. -/
theorem coarse_nonDanglingIncident_right (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    nonDanglingIncident (coarseCandidate input profile hSame).datum
        ((coarseCandidate input profile hSame).datum.sourceEndpoint
          (freshVertex target) profile.first.1.1.2) =
      {(coarseCandidate input profile hSame).newSourceEdge profile.first.1.1.2,
        (coarseCandidate input profile hSame).oldSourceEdge profile.largest.1} := by
  classical
  apply Finset.eq_of_subset_of_card_le
    (coarse_nonDanglingIncident_right_subset input profile hSame)
  rw [card_nonDanglingIncident,
    coarse_right_nonDanglingValency_eq_two input profile hSame]
  exact le_of_eq (coarse_right_pair_card input profile hSame)

/-- **The single selected new occurrence of `M⁽¹⁾` survives.**  The nd2 route
deduces this at the divalent endpoint from a dangling residual companion;
there is no such companion here, and the argument runs at the opposite
endpoint instead: the third direction is entirely dangling there, so a
dangling new occurrence would leave the retained largest direction as the only
survivor. -/
theorem coarse_anchor_new_survives (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    ¬ IsDangling (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).newSourceEdge profile.first.1.1.2) := by
  have hMem : (coarseCandidate input profile hSame).newSourceEdge
      profile.first.1.1.2 ∈
      nonDanglingIncident (coarseCandidate input profile hSame).datum
        ((coarseCandidate input profile hSame).datum.sourceEndpoint
          (freshVertex target) profile.first.1.1.2) := by
    rw [coarse_nonDanglingIncident_right input profile hSame]
    exact Finset.mem_insert_self _ _
  exact ((mem_nonDanglingIncident _ _ _).mp hMem).1

/-! ### The stable rows of `M⁽¹⁾` -/

theorem coarse_first_survives (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    ¬ IsDangling (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).oldSourceEdge profile.first.1) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
    (first_survives input profile)

theorem coarse_second_survives (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    ¬ IsDangling (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).oldSourceEdge profile.second.1) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
    (second_survives input profile)

/-- Figure 30's new edge `e'` of `M⁽¹⁾`. -/
noncomputable def coarseAnchorNew (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    NonDanglingEdge (coarseCandidate input profile hSame).datum :=
  ⟨(coarseCandidate input profile hSame).newSourceEdge profile.first.1.1.2,
    coarse_anchor_new_survives input profile hSame⟩

/-- The retained largest direction `e₄` in `M⁽¹⁾`. -/
noncomputable def coarseRetainedLargest (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    NonDanglingEdge (coarseCandidate input profile hSame).datum :=
  ⟨(coarseCandidate input profile hSame).oldSourceEdge profile.largest.1,
    coarse_largest_survives input profile hSame⟩

/-- The retained doubled-direction survivor `e₂` in `M⁽¹⁾`. -/
noncomputable def coarseRetainedFirst (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    NonDanglingEdge (coarseCandidate input profile hSame).datum :=
  ⟨(coarseCandidate input profile hSame).oldSourceEdge profile.first.1,
    coarse_first_survives input profile hSame⟩

/-- The retained doubled-direction survivor `e₃` in `M⁽¹⁾`. -/
noncomputable def coarseRetainedSecond (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    NonDanglingEdge (coarseCandidate input profile hSame).datum :=
  ⟨(coarseCandidate input profile hSame).oldSourceEdge profile.second.1,
    coarse_second_survives input profile hSame⟩

theorem coarse_anchor_new_consecutive_largest (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    Consecutive (coarseCandidate input profile hSame).datum
      (coarseAnchorNew input profile hSame)
      (coarseRetainedLargest input profile hSame) := by
  refine ⟨?_, _, coarse_anchor_new_incident_right input profile hSame,
    coarse_largest_incident_right input profile hSame,
    coarse_right_nonDanglingValency_eq_two input profile hSame⟩
  intro hEqual
  exact coarse_new_ne_old input profile hSame profile.first.1.1.2 profile.largest.1
    (congrArg (fun item : NonDanglingEdge (coarseCandidate input profile hSame).datum ↦
      item.1) hEqual)

/-- **The new edge of `M⁽¹⁾` carries the row of the retained largest
direction.**  In nd2 the coarse new edge lay in the *small* survivor's row at
the divalent end and in the large survivor's row at the trivalent end, so both
retained survivors shared one row; here the divalent end is a branch vertex and
only this identity holds. -/
theorem coarse_anchor_new_stablePath_eq_largest (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (coarseAnchorNew input profile hSame).stablePath =
      (coarseRetainedLargest input profile hSame).stablePath :=
  stablePath_eq_of_consecutive (coarse_anchor_new_consecutive_largest input profile hSame)

/-! ### The divalent endpoint of `M⁽¹⁾` is the nd3 branch vertex

In nd2 the divalent endpoint of the coarse new edge is an interior valency-two
vertex, because one of the two occurrences the divalent direction contributes
there is the dangling residual one.  In nd3 the doubled direction contributes
**two surviving** occurrences, so the same vertex is a branch vertex of the
stable graph and carries three separate flags. -/

/-- Distinct old occurrences stay distinct after retention
(`ResolutionCut.oldSourceEdge_injective`, in the local form `W3FourSurvival`
consumes). -/
theorem oldSourceEdge_injective_local
    (candidate : BalancedGlobal.Candidate target degree data wall)
    {first second : data.SourceEdge}
    (hEq : candidate.oldSourceEdge first = candidate.oldSourceEdge second) :
    first = second :=
  ResolutionCut.oldSourceEdge_injective candidate hEq

theorem coarse_right_eq_false_iff (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (edge : target.edges) :
    (coarseCandidate input profile hSame).right edge = false ↔
      edge = profile.first.1.1.1 := by
  constructor
  · intro hRight
    change W3Nd2SourceCandidates.rightOf profile.first.1.1.1 edge = false at hRight
    simp only [W3Nd2SourceCandidates.rightOf, ne_eq, decide_eq_false_iff_not,
      not_not] at hRight
    exact hRight
  · rintro rfl
    exact coarse_right_doubled input profile hSame

theorem coarse_new_eq_anchor_of_incident_left (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hIncident : Incident (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).newSourceEdge sheet)
      ((coarseCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) profile.first.1.1.2)) :
    (coarseCandidate input profile hSame).newSourceEdge sheet =
      (coarseCandidate input profile hSame).newSourceEdge profile.first.1.1.2 := by
  let candidate := coarseCandidate input profile hSame
  let pasted := coarsePastedResolution input profile hSame
  have hOutgoing := (incident_iff_target_mem_and_rel candidate.datum
    (candidate.newSourceEdge sheet)
    (candidate.datum.sourceEndpoint (oldVertex target wall)
      profile.first.1.1.2)).mp hIncident
  simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
    GluingDatum.sourceEndpoint,
    GlobalResolution.datum_vertexPartition_old_wall] at hOutgoing
  change occurrenceEquiv target wall candidate.right none ∈
      GluingDatum.incidentEdges (oldVertex target wall) ∧
    pasted.left.Rel (pasted.left.repr profile.first.1.1.2)
      (pasted.newEdge.repr sheet) at hOutgoing
  have hLeftRel : pasted.left.Rel profile.first.1.1.2
      (pasted.newEdge.repr sheet) :=
    (pasted.left.rel_repr_right profile.first.1.1.2).trans hOutgoing.2
  have hMem : pasted.newEdge.repr sheet ∈ pasted.left.block profile.first.1.1.2 :=
    (pasted.left.mem_block_iff _ _).mpr hLeftRel
  rw [coarse_pasted_left_block_selected input profile hSame profile.first.1.1.2
      (incident_wall_rel input profile.first),
    ← coarse_pasted_newEdge_block_selected input profile hSame profile.first.1.1.2
      (incident_wall_rel input profile.first)] at hMem
  have hNewRel := (pasted.newEdge.mem_block_iff
    profile.first.1.1.2 (pasted.newEdge.repr sheet)).mp hMem
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change pasted.newEdge.repr sheet = pasted.newEdge.repr profile.first.1.1.2
    exact (pasted.newEdge.repr_idem sheet).symm.trans hNewRel.symm

theorem coarse_first_incident_left (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    Incident (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).oldSourceEdge profile.first.1)
      ((coarseCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) profile.first.1.1.2) := by
  have hIncident := oldSourceEdge_incident_old (coarseCandidate input profile hSame)
    profile.first.1.1.1 (incident_target_mem input profile.first)
    (coarse_right_doubled input profile hSame) profile.first.1.1.2
  simpa only [GluingDatum.sourceEdge_self] using hIncident

theorem coarse_second_incident_left (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    Incident (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).oldSourceEdge profile.second.1)
      ((coarseCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) profile.first.1.1.2) := by
  have hIncident := oldSourceEdge_incident_old (coarseCandidate input profile hSame)
    profile.first.1.1.1 (incident_target_mem input profile.first)
    (coarse_right_doubled input profile hSame) profile.second.1.1.2
  have hEdge : data.sourceEdge profile.first.1.1.1 profile.second.1.1.2 =
      profile.second.1 := by
    rw [hSame]
    exact GluingDatum.sourceEdge_self data profile.second.1
  rw [hEdge] at hIncident
  rw [coarse_left_endpoint_eq_of_wall_rel input profile hSame profile.first.1.1.2
    profile.second.1.1.2 (incident_wall_rel input profile.first)
    (wall_together input profile)]
  exact hIncident

/-- The complete surviving star at the divalent endpoint of `M⁽¹⁾`. -/
theorem coarse_nonDanglingIncident_left (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    nonDanglingIncident (coarseCandidate input profile hSame).datum
        ((coarseCandidate input profile hSame).datum.sourceEndpoint
          (oldVertex target wall) profile.first.1.1.2) =
      {(coarseCandidate input profile hSame).newSourceEdge profile.first.1.1.2,
        (coarseCandidate input profile hSame).oldSourceEdge profile.first.1,
        (coarseCandidate input profile hSame).oldSourceEdge profile.second.1} := by
  classical
  ext edge
  constructor
  · intro hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases sourceEdge_cases (coarseCandidate input profile hSame) edge with
      ⟨old, hOld⟩ | ⟨sheet, hNew⟩
    · subst edge
      have hInfo := old_incident_old_selected_info_local
        (coarseCandidate input profile hSame) input.distinguishedBlock
        profile.first.1.1.2 (incident_wall_rel input profile.first) old hIncident
      have hTarget : old.1.1 = profile.first.1.1.1 :=
        (coarse_right_eq_false_iff input profile hSame old.1.1).mp hInfo.2
      have hOldSurvives : ¬ IsDangling data old := fun hDangling ↦
        hSurvives ((coarse_old_isDangling_iff input profile hSame old).mpr hDangling)
      have hProfile := (mem_survivors data input.distinguishedBlock
        ⟨old, hInfo.1⟩).mpr hOldSurvives
      rw [profile.surviving] at hProfile
      rcases Finset.mem_insert.mp hProfile with hFirst | hRest
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_insert.mpr
        refine Or.inl (congrArg (fun item : IncidentSourceEdge data
          (WallBlock.sourceVertex data wall input.distinguishedBlock) ↦
            (coarseCandidate input profile hSame).oldSourceEdge item.1) hFirst)
      · rcases Finset.mem_insert.mp hRest with hSecond | hLargest
        · apply Finset.mem_insert_of_mem
          apply Finset.mem_insert_of_mem
          apply Finset.mem_singleton.mpr
          exact congrArg (fun item : IncidentSourceEdge data
            (WallBlock.sourceVertex data wall input.distinguishedBlock) ↦
              (coarseCandidate input profile hSame).oldSourceEdge item.1) hSecond
        · exact absurd (hTarget.symm.trans (congrArg
            (fun item : IncidentSourceEdge data
              (WallBlock.sourceVertex data wall input.distinguishedBlock) ↦
                item.1.1.1) (Finset.mem_singleton.mp hLargest)))
            profile.first_target_ne
    · subst edge
      exact Finset.mem_insert.mpr
        (Or.inl (coarse_new_eq_anchor_of_incident_left input profile hSame sheet
          hIncident))
  · intro hMem
    rcases Finset.mem_insert.mp hMem with hNew | hRest
    · rw [hNew]
      exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨coarse_anchor_new_survives input profile hSame,
          coarse_anchor_new_incident_left input profile hSame⟩
    · rcases Finset.mem_insert.mp hRest with hFirst | hSecond
      · rw [hFirst]
        exact (mem_nonDanglingIncident _ _ _).mpr
          ⟨coarse_first_survives input profile hSame,
            coarse_first_incident_left input profile hSame⟩
      · rw [Finset.mem_singleton.mp hSecond]
        exact (mem_nonDanglingIncident _ _ _).mpr
          ⟨coarse_second_survives input profile hSame,
            coarse_second_incident_left input profile hSame⟩

theorem coarse_old_first_ne_second (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (coarseCandidate input profile hSame).oldSourceEdge profile.first.1 ≠
      (coarseCandidate input profile hSame).oldSourceEdge profile.second.1 := by
  intro hEqual
  exact profile.first_ne_second (Subtype.ext
    (oldSourceEdge_injective_local (coarseCandidate input profile hSame) hEqual))

/-- **The divalent endpoint of `M⁽¹⁾` is a trivalent stable vertex.**  This is
where the nd2 template genuinely fails: there the same vertex has valency two,
because the divalent direction's second occurrence dangles. -/
theorem coarse_left_nonDanglingValency_eq_three (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    nonDanglingValency (coarseCandidate input profile hSame).datum
      ((coarseCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) profile.first.1.1.2) = 3 := by
  classical
  rw [← card_nonDanglingIncident, coarse_nonDanglingIncident_left input profile hSame,
    Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (hFirst | hSecond)
      · exact coarse_new_ne_old input profile hSame _ _ hFirst
      · exact coarse_new_ne_old input profile hSame _ _ hSecond),
    Finset.card_pair (coarse_old_first_ne_second input profile hSame)]

/-! ## The fine member `M⁽²⁾`

`M⁽²⁾` keeps the whole distinguished block at its divalent endpoint, where the
largest direction `t₄` is retained, and cuts it into the doubled direction's
two blocks at the trivalent endpoint, beside `t₃` and the dangling `t₂`.  It
therefore has **two** selected new occurrences, and — unlike the nd2 fine
member, whose residual singleton new occurrence dangles — both of them
survive. -/

theorem fine_right_largest (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (fineCandidate input profile hSame).right
      (largestTarget input profile) = false := by
  change W3Nd2SourceCandidates.rightOf (largestTarget input profile)
    (largestTarget input profile) = false
  simp [W3Nd2SourceCandidates.rightOf]

theorem fine_right_eq_false_iff (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (edge : target.edges) :
    (fineCandidate input profile hSame).right edge = false ↔
      edge = largestTarget input profile := by
  constructor
  · intro hRight
    change W3Nd2SourceCandidates.rightOf (largestTarget input profile) edge =
      false at hRight
    simp only [W3Nd2SourceCandidates.rightOf, ne_eq, decide_eq_false_iff_not,
      not_not] at hRight
    exact hRight
  · rintro rfl
    exact fine_right_largest input profile hSame

theorem fine_right_doubled (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (fineCandidate input profile hSame).right profile.first.1.1.1 = true := by
  change W3Nd2SourceCandidates.rightOf (largestTarget input profile)
    profile.first.1.1.1 = true
  simp only [W3Nd2SourceCandidates.rightOf, ne_eq, decide_eq_true_eq]
  exact profile.first_target_ne

theorem fine_new_ne_old (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (sheet : Fin degree) (edge : data.SourceEdge) :
    (fineCandidate input profile hSame).newSourceEdge sheet ≠
      (fineCandidate input profile hSame).oldSourceEdge edge := by
  intro hEqual
  have hTargets := congrArg
    (fun item : (fineCandidate input profile hSame).datum.SourceEdge ↦ item.1.1)
    hEqual
  have hLabels := (occurrenceEquiv target wall
    (fineCandidate input profile hSame).right).injective hTargets
  cases hLabels

/-! ### Reading a sheet relation off an incidence

Stated for an arbitrary candidate in `LimitChainCore`; the `_local` names are
kept because `W3FourSurvival` consumes them. -/

alias old_incident_fresh_sheet_rel_local := DraismaVargas.LocalCases.LimitChainCore.old_incident_fresh_sheet_rel

alias new_incident_old_sheet_rel_local := DraismaVargas.LocalCases.LimitChainCore.new_incident_old_sheet_rel

alias newSourceEdge_repr_local := DraismaVargas.LocalCases.LimitChainCore.newSourceEdge_repr
/-! ### The endpoint dictionary of `M⁽²⁾` -/

theorem fine_left_endpoint_eq_of_wall_rel (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (first second : Fin degree)
    (hFirst : (data.vertexPartition wall).Rel input.distinguishedBlock.1 first)
    (hRel : (data.vertexPartition wall).Rel first second) :
    (fineCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) first =
      (fineCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) second := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change ((fineCandidate input profile hSame).datum.vertexPartition
        (oldVertex target wall)).repr first =
      ((fineCandidate input profile hSame).datum.vertexPartition
        (oldVertex target wall)).repr second
    rw [show (fineCandidate input profile hSame).datum.vertexPartition
        (oldVertex target wall) =
          (finePastedResolution input profile hSame).left from
      GlobalResolution.expandedVertexPartition_old_wall data wall _]
    have hMem : second ∈ (data.vertexPartition wall).block first :=
      ((data.vertexPartition wall).mem_block_iff first second).mpr hRel
    rw [← fine_pasted_left_block_selected input profile hSame first hFirst] at hMem
    exact ((finePastedResolution input profile hSame).left.mem_block_iff
      first second).mp hMem

theorem fine_right_endpoint_eq_of_fine_rel (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (first second : Fin degree)
    (hFirst : (data.vertexPartition wall).Rel input.distinguishedBlock.1 first)
    (hRel : (finePartition input profile).Rel first second) :
    (fineCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) first =
      (fineCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) second := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (finePastedResolution input profile hSame).right.repr first =
      (finePastedResolution input profile hSame).right.repr second
    have hMem : second ∈ (finePartition input profile).block first :=
      ((finePartition input profile).mem_block_iff first second).mpr hRel
    rw [← fine_pasted_right_block_selected input profile hSame first hFirst] at hMem
    exact ((finePastedResolution input profile hSame).right.mem_block_iff
      first second).mp hMem

theorem fine_newSourceEdge_eq_of_fine_rel (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (first second : Fin degree)
    (hFirst : (data.vertexPartition wall).Rel input.distinguishedBlock.1 first)
    (hRel : (finePartition input profile).Rel first second) :
    (fineCandidate input profile hSame).newSourceEdge second =
      (fineCandidate input profile hSame).newSourceEdge first := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (finePastedResolution input profile hSame).newEdge.repr second =
      (finePastedResolution input profile hSame).newEdge.repr first
    have hMem : second ∈ (finePartition input profile).block first :=
      ((finePartition input profile).mem_block_iff first second).mpr hRel
    rw [← fine_pasted_newEdge_block_selected input profile hSame first hFirst] at hMem
    exact (((finePastedResolution input profile hSame).newEdge.mem_block_iff
      first second).mp hMem).symm

theorem fine_new_incident_left (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree) :
    Incident (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).newSourceEdge sheet)
      ((fineCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) sheet) :=
  Or.inl (congrArg Prod.fst (GlobalResolution.sourceEnds_newSourceEdge data wall
    (fineCandidate input profile hSame).right
    (finePastedResolution input profile hSame)
    (GlobalAssembly.blockwiseCompatible _ _ _ _ _
      (fineCandidate input profile hSame).exterior) sheet))

theorem fine_new_incident_right (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree) :
    Incident (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).newSourceEdge sheet)
      ((fineCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) sheet) :=
  Or.inr (congrArg Prod.snd (GlobalResolution.sourceEnds_newSourceEdge data wall
    (fineCandidate input profile hSame).right
    (finePastedResolution input profile hSame)
    (GlobalAssembly.blockwiseCompatible _ _ _ _ _
      (fineCandidate input profile hSame).exterior) sheet))

theorem fine_doubled_incident_right (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree) :
    Incident (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).oldSourceEdge
        (data.sourceEdge profile.first.1.1.1 sheet))
      ((fineCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) sheet) :=
  oldSourceEdge_incident_fresh (fineCandidate input profile hSame)
    profile.first.1.1.1 (incident_target_mem input profile.first)
    (fine_right_doubled input profile hSame) sheet

theorem fine_largest_incident_left (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    Incident (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).oldSourceEdge profile.largest.1)
      ((fineCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) profile.first.1.1.2) := by
  have hIncident := oldSourceEdge_incident_old (fineCandidate input profile hSame)
    (largestTarget input profile) (largestTarget_mem input profile)
    (fine_right_largest input profile hSame) profile.largest.1.1.2
  rw [fine_left_endpoint_eq_of_wall_rel input profile hSame profile.first.1.1.2
    profile.largest.1.1.2 (incident_wall_rel input profile.first)
    ((incident_wall_rel input profile.first).symm.trans
      (incident_wall_rel input profile.largest))]
  simpa only [GluingDatum.sourceEdge_self] using hIncident

theorem fine_largest_survives (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    ¬ IsDangling (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).oldSourceEdge profile.largest.1) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
    (largest_survives input profile)

theorem fine_doubled_survives (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    ¬ IsDangling (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).oldSourceEdge
        (data.sourceEdge profile.first.1.1.1 sheet)) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
    (doubled_sourceEdge_survives input profile hSame sheet hSheet)

theorem fine_new_eq_of_incident_right (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (anchor sheet : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel input.distinguishedBlock.1 anchor)
    (hIncident : Incident (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).newSourceEdge sheet)
      ((fineCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) anchor)) :
    (fineCandidate input profile hSame).newSourceEdge sheet =
      (fineCandidate input profile hSame).newSourceEdge anchor := by
  let candidate := fineCandidate input profile hSame
  let pasted := finePastedResolution input profile hSame
  have hOutgoing := (incident_iff_target_mem_and_rel candidate.datum
    (candidate.newSourceEdge sheet)
    (candidate.datum.sourceEndpoint (freshVertex target) anchor)).mp hIncident
  change occurrenceEquiv target wall candidate.right none ∈
      GluingDatum.incidentEdges (freshVertex target) ∧
    pasted.right.Rel (pasted.right.repr anchor)
      (pasted.newEdge.repr sheet) at hOutgoing
  have hRightRel : pasted.right.Rel anchor (pasted.newEdge.repr sheet) :=
    (pasted.right.rel_repr_right anchor).trans hOutgoing.2
  have hMem : pasted.newEdge.repr sheet ∈ pasted.right.block anchor :=
    (pasted.right.mem_block_iff _ _).mpr hRightRel
  rw [fine_pasted_right_block_selected input profile hSame anchor hAnchor,
    ← fine_pasted_newEdge_block_selected input profile hSame anchor hAnchor] at hMem
  have hNewRel := (pasted.newEdge.mem_block_iff anchor
    (pasted.newEdge.repr sheet)).mp hMem
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change pasted.newEdge.repr sheet = pasted.newEdge.repr anchor
    exact (pasted.newEdge.repr_idem sheet).symm.trans hNewRel.symm

/-- At every trivalent endpoint of `M⁽²⁾` only the canonical doubled-direction
survivor through that sheet and the selected new occurrence can survive. -/
theorem fine_nonDanglingIncident_right_subset (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    nonDanglingIncident (fineCandidate input profile hSame).datum
        ((fineCandidate input profile hSame).datum.sourceEndpoint
          (freshVertex target) sheet) ⊆
      {(fineCandidate input profile hSame).newSourceEdge sheet,
        (fineCandidate input profile hSame).oldSourceEdge
          (data.sourceEdge profile.first.1.1.1 sheet)} := by
  classical
  intro edge hMem
  obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
  rcases sourceEdge_cases (fineCandidate input profile hSame) edge with
    ⟨old, hOld⟩ | ⟨other, hNew⟩
  · subst edge
    have hInfo := old_incident_fresh_selected_info
      (fineCandidate input profile hSame) input.distinguishedBlock sheet hSheet
      old hIncident
    have hOldSurvives : ¬ IsDangling data old := fun hDangling ↦
      hSurvives ((fine_old_isDangling_iff input profile hSame old).mpr hDangling)
    have hProfile := (mem_survivors data input.distinguishedBlock
      ⟨old, hInfo.1⟩).mpr hOldSurvives
    rw [profile.surviving] at hProfile
    have hTarget : old.1.1 = profile.first.1.1.1 := by
      rcases Finset.mem_insert.mp hProfile with hFirst | hRest
      · exact congrArg (fun item : IncidentSourceEdge data
          (WallBlock.sourceVertex data wall input.distinguishedBlock) ↦
            item.1.1.1) hFirst
      · rcases Finset.mem_insert.mp hRest with hSecond | hLargest
        · exact (congrArg (fun item : IncidentSourceEdge data
            (WallBlock.sourceVertex data wall input.distinguishedBlock) ↦
              item.1.1.1) hSecond).trans hSame.symm
        · exfalso
          have hLargestTarget := congrArg (fun item : IncidentSourceEdge data
            (WallBlock.sourceVertex data wall input.distinguishedBlock) ↦
              item.1.1.1) (Finset.mem_singleton.mp hLargest)
          have hRight := hInfo.2
          rw [hLargestTarget] at hRight
          exact Bool.noConfusion
            ((fine_right_largest input profile hSame).symm.trans hRight)
    have hRightRel := old_incident_fresh_sheet_rel_local
      (fineCandidate input profile hSame) sheet old hIncident
    have hBlockMem : old.1.2 ∈
        (finePastedResolution input profile hSame).right.block sheet :=
      ((finePastedResolution input profile hSame).right.mem_block_iff _ _).mpr
        hRightRel
    rw [fine_pasted_right_block_selected input profile hSame sheet hSheet]
      at hBlockMem
    have hFineRel := ((finePartition input profile).mem_block_iff _ _).mp hBlockMem
    have hRepr : (data.edgePartition profile.first.1.1.1).repr old.1.2 = old.1.2 := by
      rw [← hTarget]
      exact old.2
    have hEdge : data.sourceEdge profile.first.1.1.1 sheet = old := by
      apply Subtype.ext
      apply Prod.ext
      · exact hTarget.symm
      · change (data.edgePartition profile.first.1.1.1).repr sheet = old.1.2
        exact hFineRel.trans hRepr
    apply Finset.mem_insert_of_mem
    apply Finset.mem_singleton.mpr
    exact congrArg (fineCandidate input profile hSame).oldSourceEdge hEdge.symm
  · subst edge
    exact Finset.mem_insert.mpr
      (Or.inl (fine_new_eq_of_incident_right input profile hSame sheet other
        hSheet hIncident))

private theorem fine_right_pair_card (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree) :
    ({(fineCandidate input profile hSame).newSourceEdge sheet,
        (fineCandidate input profile hSame).oldSourceEdge
          (data.sourceEdge profile.first.1.1.1 sheet)} :
      Finset (fineCandidate input profile hSame).datum.SourceEdge).card = 2 :=
  Finset.card_pair (fine_new_ne_old input profile hSame _ _)

theorem fine_right_nonDanglingValency_eq_two (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    nonDanglingValency (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) sheet) = 2 := by
  classical
  have hLe := (Finset.card_le_card
    (fine_nonDanglingIncident_right_subset input profile hSame sheet hSheet)).trans
    (le_of_eq (fine_right_pair_card input profile hSame sheet))
  have hPos : 0 < (nonDanglingIncident (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).datum.sourceEndpoint
        (freshVertex target) sheet)).card :=
    Finset.card_pos.mpr ⟨_, (mem_nonDanglingIncident _ _ _).mpr
      ⟨fine_doubled_survives input profile hSame sheet hSheet,
        fine_doubled_incident_right input profile hSame sheet⟩⟩
  rw [card_nonDanglingIncident] at hLe hPos
  have hNotOne := NonDanglingValency.nonDanglingValency_ne_one
    (fineCandidate input profile hSame).datum
    (fineCandidate_valid input profile hSame).1
    ((fineCandidate input profile hSame).datum.sourceEndpoint
      (freshVertex target) sheet)
  omega

/-- The surviving star at every trivalent endpoint of `M⁽²⁾`. -/
theorem fine_nonDanglingIncident_right (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    nonDanglingIncident (fineCandidate input profile hSame).datum
        ((fineCandidate input profile hSame).datum.sourceEndpoint
          (freshVertex target) sheet) =
      {(fineCandidate input profile hSame).newSourceEdge sheet,
        (fineCandidate input profile hSame).oldSourceEdge
          (data.sourceEdge profile.first.1.1.1 sheet)} := by
  classical
  apply Finset.eq_of_subset_of_card_le
    (fine_nonDanglingIncident_right_subset input profile hSame sheet hSheet)
  rw [card_nonDanglingIncident,
    fine_right_nonDanglingValency_eq_two input profile hSame sheet hSheet]
  exact le_of_eq (fine_right_pair_card input profile hSame sheet)

/-- **Both selected new occurrences of `M⁽²⁾` survive.**  The nd2 fine member
has a residual singleton new occurrence that dangles; here `k₂ + k₃ = |A₀|`
leaves no residue, and each of the two new occurrences is forced to survive at
its own trivalent endpoint. -/
theorem fine_new_survives (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    ¬ IsDangling (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).newSourceEdge sheet) := by
  have hMem : (fineCandidate input profile hSame).newSourceEdge sheet ∈
      nonDanglingIncident (fineCandidate input profile hSame).datum
        ((fineCandidate input profile hSame).datum.sourceEndpoint
          (freshVertex target) sheet) := by
    rw [fine_nonDanglingIncident_right input profile hSame sheet hSheet]
    exact Finset.mem_insert_self _ _
  exact ((mem_nonDanglingIncident _ _ _).mp hMem).1

/-! ### The stable rows of `M⁽²⁾` -/

/-- A selected new occurrence of `M⁽²⁾` through a sheet of the distinguished
block. -/
noncomputable def fineNew (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    NonDanglingEdge (fineCandidate input profile hSame).datum :=
  ⟨(fineCandidate input profile hSame).newSourceEdge sheet,
    fine_new_survives input profile hSame sheet hSheet⟩

/-- The retained doubled-direction survivor through that same sheet. -/
noncomputable def fineRetainedDoubled (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    NonDanglingEdge (fineCandidate input profile hSame).datum :=
  ⟨(fineCandidate input profile hSame).oldSourceEdge
      (data.sourceEdge profile.first.1.1.1 sheet),
    fine_doubled_survives input profile hSame sheet hSheet⟩

/-- The retained largest direction `e₄` in `M⁽²⁾`. -/
noncomputable def fineRetainedLargest (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    NonDanglingEdge (fineCandidate input profile hSame).datum :=
  ⟨(fineCandidate input profile hSame).oldSourceEdge profile.largest.1,
    fine_largest_survives input profile hSame⟩

theorem fine_new_consecutive_doubled (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    Consecutive (fineCandidate input profile hSame).datum
      (fineNew input profile hSame sheet hSheet)
      (fineRetainedDoubled input profile hSame sheet hSheet) := by
  refine ⟨?_, _, fine_new_incident_right input profile hSame sheet,
    fine_doubled_incident_right input profile hSame sheet,
    fine_right_nonDanglingValency_eq_two input profile hSame sheet hSheet⟩
  intro hEqual
  exact fine_new_ne_old input profile hSame sheet
    (data.sourceEdge profile.first.1.1.1 sheet)
    (congrArg (fun item : NonDanglingEdge (fineCandidate input profile hSame).datum ↦
      item.1) hEqual)

/-- **Each new occurrence of `M⁽²⁾` carries the row of the doubled-direction
survivor it meets.**  For `sheet = profile.first` this is `e₂`'s row and the
new edge has `|e'| = k₂`; for `sheet = profile.second` it is `e₃`'s row and
`|e''| = k₃`. -/
theorem fine_new_stablePath_eq_doubled (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (fineNew input profile hSame sheet hSheet).stablePath =
      (fineRetainedDoubled input profile hSame sheet hSheet).stablePath :=
  stablePath_eq_of_consecutive
    (fine_new_consecutive_doubled input profile hSame sheet hSheet)

theorem fineRetainedDoubled_first (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (fineRetainedDoubled input profile hSame profile.first.1.1.2
        (incident_wall_rel input profile.first)).1 =
      (fineCandidate input profile hSame).oldSourceEdge profile.first.1 := by
  change (fineCandidate input profile hSame).oldSourceEdge
    (data.sourceEdge profile.first.1.1.1 profile.first.1.1.2) = _
  exact congrArg (fineCandidate input profile hSame).oldSourceEdge
    (GluingDatum.sourceEdge_self data profile.first.1)

theorem fineRetainedDoubled_second (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (fineRetainedDoubled input profile hSame profile.second.1.1.2
        (incident_wall_rel input profile.second)).1 =
      (fineCandidate input profile hSame).oldSourceEdge profile.second.1 := by
  change (fineCandidate input profile hSame).oldSourceEdge
    (data.sourceEdge profile.first.1.1.1 profile.second.1.1.2) = _
  refine congrArg (fineCandidate input profile hSame).oldSourceEdge ?_
  rw [hSame]
  exact GluingDatum.sourceEdge_self data profile.second.1

/-! ### The divalent endpoint of `M⁽²⁾` is the nd3 branch vertex -/

theorem fine_new_first_ne_second (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (fineCandidate input profile hSame).newSourceEdge profile.first.1.1.2 ≠
      (fineCandidate input profile hSame).newSourceEdge profile.second.1.1.2 := by
  intro hEqual
  apply fine_separate input profile hSame
  have hSheets := congrArg
    (fun item : (fineCandidate input profile hSame).datum.SourceEdge ↦ item.1.2)
    hEqual
  have hRel : (finePastedResolution input profile hSame).newEdge.Rel
      profile.first.1.1.2 profile.second.1.1.2 := hSheets
  have hMem := ((finePastedResolution input profile hSame).newEdge.mem_block_iff
    profile.first.1.1.2 profile.second.1.1.2).mpr hRel
  rw [fine_pasted_newEdge_block_selected input profile hSame profile.first.1.1.2
    (incident_wall_rel input profile.first)] at hMem
  exact ((finePartition input profile).mem_block_iff _ _).mp hMem

theorem fine_new_eq_first_or_second_of_incident_left (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hIncident : Incident (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).newSourceEdge sheet)
      ((fineCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) profile.first.1.1.2)) :
    (fineCandidate input profile hSame).newSourceEdge sheet =
        (fineCandidate input profile hSame).newSourceEdge profile.first.1.1.2 ∨
      (fineCandidate input profile hSame).newSourceEdge sheet =
        (fineCandidate input profile hSame).newSourceEdge profile.second.1.1.2 := by
  have hRel := new_incident_old_sheet_rel_local (fineCandidate input profile hSame)
    profile.first.1.1.2 sheet hIncident
  have hMem := ((finePastedResolution input profile hSame).left.mem_block_iff
    profile.first.1.1.2
    ((finePastedResolution input profile hSame).newEdge.repr sheet)).mpr hRel
  rw [fine_pasted_left_block_selected input profile hSame profile.first.1.1.2
    (incident_wall_rel input profile.first)] at hMem
  have hDist : (data.vertexPartition wall).Rel input.distinguishedBlock.1
      ((finePastedResolution input profile hSame).newEdge.repr sheet) :=
    (incident_wall_rel input profile.first).trans
      (((data.vertexPartition wall).mem_block_iff _ _).mp hMem)
  rcases fine_rel_first_or_second input profile hSame
    ((finePastedResolution input profile hSame).newEdge.repr sheet) hDist with
    hFirst | hSecond
  · exact Or.inl
      ((newSourceEdge_repr_local (fineCandidate input profile hSame) sheet).symm.trans
        (fine_newSourceEdge_eq_of_fine_rel input profile hSame profile.first.1.1.2
          _ (incident_wall_rel input profile.first) hFirst))
  · exact Or.inr
      ((newSourceEdge_repr_local (fineCandidate input profile hSame) sheet).symm.trans
        (fine_newSourceEdge_eq_of_fine_rel input profile hSame profile.second.1.1.2
          _ (incident_wall_rel input profile.second) hSecond))

theorem fine_second_new_incident_left (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    Incident (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).newSourceEdge profile.second.1.1.2)
      ((fineCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) profile.first.1.1.2) := by
  rw [fine_left_endpoint_eq_of_wall_rel input profile hSame profile.first.1.1.2
    profile.second.1.1.2 (incident_wall_rel input profile.first)
    (wall_together input profile)]
  exact fine_new_incident_left input profile hSame profile.second.1.1.2

/-- The complete surviving star at the divalent endpoint of `M⁽²⁾`: the two
selected new occurrences and the retained largest direction. -/
theorem fine_nonDanglingIncident_left (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    nonDanglingIncident (fineCandidate input profile hSame).datum
        ((fineCandidate input profile hSame).datum.sourceEndpoint
          (oldVertex target wall) profile.first.1.1.2) =
      {(fineCandidate input profile hSame).newSourceEdge profile.first.1.1.2,
        (fineCandidate input profile hSame).newSourceEdge profile.second.1.1.2,
        (fineCandidate input profile hSame).oldSourceEdge profile.largest.1} := by
  classical
  ext edge
  constructor
  · intro hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases sourceEdge_cases (fineCandidate input profile hSame) edge with
      ⟨old, hOld⟩ | ⟨sheet, hNew⟩
    · subst edge
      have hInfo := old_incident_old_selected_info_local
        (fineCandidate input profile hSame) input.distinguishedBlock
        profile.first.1.1.2 (incident_wall_rel input profile.first) old hIncident
      have hTarget : old.1.1 = largestTarget input profile :=
        (fine_right_eq_false_iff input profile hSame old.1.1).mp hInfo.2
      have hOldSurvives : ¬ IsDangling data old := fun hDangling ↦
        hSurvives ((fine_old_isDangling_iff input profile hSame old).mpr hDangling)
      have hProfile := (mem_survivors data input.distinguishedBlock
        ⟨old, hInfo.1⟩).mpr hOldSurvives
      rw [profile.surviving] at hProfile
      rcases Finset.mem_insert.mp hProfile with hFirst | hRest
      · exact absurd ((congrArg (fun item : IncidentSourceEdge data
          (WallBlock.sourceVertex data wall input.distinguishedBlock) ↦
            item.1.1.1) hFirst).symm.trans hTarget) profile.first_target_ne
      · rcases Finset.mem_insert.mp hRest with hSecond | hLargest
        · refine absurd ?_ profile.second_target_ne
          exact (congrArg (fun item : IncidentSourceEdge data
            (WallBlock.sourceVertex data wall input.distinguishedBlock) ↦
              item.1.1.1) hSecond).symm.trans hTarget
        · apply Finset.mem_insert_of_mem
          apply Finset.mem_insert_of_mem
          apply Finset.mem_singleton.mpr
          exact congrArg (fun item : IncidentSourceEdge data
            (WallBlock.sourceVertex data wall input.distinguishedBlock) ↦
              (fineCandidate input profile hSame).oldSourceEdge item.1)
            (Finset.mem_singleton.mp hLargest)
    · subst edge
      rcases fine_new_eq_first_or_second_of_incident_left input profile hSame sheet
        hIncident with hFirst | hSecond
      · exact Finset.mem_insert.mpr (Or.inl hFirst)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl hSecond))
  · intro hMem
    rcases Finset.mem_insert.mp hMem with hFirst | hRest
    · rw [hFirst]
      exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨fine_new_survives input profile hSame profile.first.1.1.2
            (incident_wall_rel input profile.first),
          fine_new_incident_left input profile hSame profile.first.1.1.2⟩
    · rcases Finset.mem_insert.mp hRest with hSecond | hLargest
      · rw [hSecond]
        exact (mem_nonDanglingIncident _ _ _).mpr
          ⟨fine_new_survives input profile hSame profile.second.1.1.2
              (incident_wall_rel input profile.second),
            fine_second_new_incident_left input profile hSame⟩
      · rw [Finset.mem_singleton.mp hLargest]
        exact (mem_nonDanglingIncident _ _ _).mpr
          ⟨fine_largest_survives input profile hSame,
            fine_largest_incident_left input profile hSame⟩

/-- **The divalent endpoint of `M⁽²⁾` is a trivalent stable vertex**, carrying
the two new flags and the retained `e₄` flag. -/
theorem fine_left_nonDanglingValency_eq_three (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    nonDanglingValency (fineCandidate input profile hSame).datum
      ((fineCandidate input profile hSame).datum.sourceEndpoint
        (oldVertex target wall) profile.first.1.1.2) = 3 := by
  classical
  rw [← card_nonDanglingIncident, fine_nonDanglingIncident_left input profile hSame,
    Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (hSecond | hLargest)
      · exact fine_new_first_ne_second input profile hSame hSecond
      · exact fine_new_ne_old input profile hSame _ _ hLargest),
    Finset.card_pair (fine_new_ne_old input profile hSame _ _)]

/-! ## Branch valency is preserved, and Equation (4)'s denominators sit on the
surviving new rows -/

/-- The distinguished source vertex of the incoming datum is already a branch
vertex: the nd3 case is exactly non-dangling valency three. -/
theorem source_nonDanglingValency_eq_three (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    nonDanglingValency data
      (WallBlock.sourceVertex data wall input.distinguishedBlock) = 3 := by
  classical
  rw [← card_survivors, profile.surviving,
    Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (hSecond | hLargest)
      · exact profile.first_ne_second hSecond
      · exact profile.first_ne_largest hLargest),
    Finset.card_pair profile.second_ne_largest]

/-- Figure 30's `|e'| = k₄ = k₂ + k₃` on the surviving new row of `M⁽¹⁾`. -/
theorem coarse_anchor_new_index (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (coarseCandidate input profile hSame).datum.sourceEdgeIndex
        (coarseAnchorNew input profile hSame).1 =
      data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 := by
  change (coarseCandidate input profile hSame).datum.sourceEdgeIndex
    ((coarseCandidate input profile hSame).newSourceEdge profile.first.1.1.2) = _
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge]
  exact coarse_pasted_newEdge_blockCard_selected input profile hSame _
    (incident_wall_rel input profile.first)

/-- Figure 30's `|e'| = k₂` on the first surviving new row of `M⁽²⁾`. -/
theorem fine_new_first_index (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (fineCandidate input profile hSame).datum.sourceEdgeIndex
        (fineNew input profile hSame profile.first.1.1.2
          (incident_wall_rel input profile.first)).1 =
      data.sourceEdgeIndex profile.first.1 := by
  change (fineCandidate input profile hSame).datum.sourceEdgeIndex
    ((fineCandidate input profile hSame).newSourceEdge profile.first.1.1.2) = _
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge]
  exact fine_pasted_newEdge_blockCard_first input profile hSame

/-- Figure 30's `|e''| = k₃` on the second surviving new row of `M⁽²⁾`. -/
theorem fine_new_second_index (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (fineCandidate input profile hSame).datum.sourceEdgeIndex
        (fineNew input profile hSame profile.second.1.1.2
          (incident_wall_rel input profile.second)).1 =
      data.sourceEdgeIndex profile.second.1 := by
  change (fineCandidate input profile hSame).datum.sourceEdgeIndex
    ((fineCandidate input profile hSame).newSourceEdge profile.second.1.1.2) = _
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge]
  exact fine_pasted_newEdge_blockCard_second input profile hSame

end DraismaVargas.LocalCases.W3Nd3StableGraph
