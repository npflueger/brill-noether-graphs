module

public import DraismaVargas.LocalCases.W2MkkSourceCandidates
public import DraismaVargas.LocalCases.M11JoinedSurvival
public import DraismaVargas.LocalCases.LimitChainCore

@[expose] public section

/-!
# Survival and the endpoint census for Figure 34's three members

Source: Draisma--Vargas Part I, case `{w2-r2-nd3-M-kk}`, Figure 34 and
Equation (8).  The Base I/II vocabulary is fixed in Case `{w2-r2}`, and
`{w2-r2-nd3}` right after it.

`W2MkkSourceCandidates` builds the three members and proves them valid,
genus preserving, divalent at both new endpoints, with Figure 34's displayed
new-edge indices.  This module is the first step from that geometry towards
Equation (8): **which occurrences of each member survive pruning, what the
complete surviving star at each new endpoint is, and which stable row each
surviving new occurrence joins.**  The lift, the row descent, the limit
matrices and Equation (8) itself are later modules (`W2MkkStableLift`,
`W2MkkRowDescent`, `W2MkkLimitMatrix`, `W2MkkCommonBalance`).

The template is the M11 chain (`M11JoinedSurvival`, `M11JoinedStableGraph`),
not the W3 chain: M-kk sits at the same divalent `w2` wall, and the arguments
below are the same trivalent-with-a-deleted-occurrence and divalent
both-or-neither arguments.  What is new is that the detaching member detaches
on **both** sides, which produces one genuinely new phenomenon -- a *second*
dangling occurrence, the new occurrence through the pinned sheet.

## Does the census transport across the branch swap?

Member 2 of Figure 34 lives over `GlobalMkk.Geometry.swapped`, i.e. over
`GlobalM11Arbitrary.SwappedDatum data wall root hRoot _ _ _`.  The answer has
three parts and only the third one matters in practice.

* **Not along `W3FourStableGraph.WallTransport`.**  A `WallTransport` preserves
  exactly two things: the target occurrence an occurrence lies above, and its
  dilation index.  That is all a *length matrix* reads.  `IsDangling`,
  `nonDanglingIncident`, `nonDanglingValency` and `Consecutive` are none of
  them functions of (target occurrence, index) -- a `WallTransport` need not
  even be injective or preserve incidence -- so
  `WallTransport.ofSheetRelabeling` does **not** carry the census, and nothing
  below is routed through it.
* **Along the actual gauge, yes.**  The M-kk swap is
  `ResolutionM11.wallBranchSwap …`, a genuine `GluingDatum.SheetRelabeling`, and
  along one of those the whole census already transports:
  `SheetRelabelPruning.isDangling_sourceEdgeEquiv_iff`,
  `SheetRelabelStable.nonDanglingIncident_map`, `nonDanglingValency_map`,
  `consecutive_map_iff` and `stablePathEquiv`, at the cost of `data.Connected`
  and nothing else.
* **But there is nothing to transport.**  `W2MkkSourceCandidates`
  (`no_common_geometry`, `not_firstMember_and_secondMember`) shows that a given datum
  carries `M⁽¹⁾` or `M⁽²⁾` and never both, so there is no member-2 candidate
  *over the original datum* whose census could be pushed forward.  This is
  exactly the situation `W3FourSurvival` records for Figure 28's Position I and
  Position II.b members.

Consequently the census here is **not transported at all**: every statement is
proved once, uniformly in `data`, `star`, `block`, `profile`, `shape` and
`detach`, and member 2 obtains it by instantiating the *same* theorems at the
branch-swapped datum with a transported profile.  Per swapped copy that costs
nothing: the transported `W2R2SourceProfile.SourceProfile` is
`W2SourceTransport.sourceProfile_relabel`, which is stated for an arbitrary
`GluingDatum.SheetRelabeling`; the `Shape` half is `W2MkkTransport.shapeRelabel`
and the `DetachData` half is `exists_detachData` over the copy, and
`W2MkkLimitColumns.remoteMember` builds the remote member over every datum of
the case.  No hypothesis is added anywhere below.

## What the census is

Write `A₀` for the distinguished wall block, `t₂` for `profile.doubleLabel`'s
direction (two survivors `e₁`, `e₂` of indices `k₁`, `k₂`), `t₃` for
`profile.singleLabel`'s (the survivor `e₃` of index `k₃ = k₁ + k₂ - 1` and the
dangling `e₄` of index one), and `x := pinSheet profile` for `e₄`'s sheet.
`A_p` is the `t₂` endpoint block containing `x` and `A_q` the other one.

For the detachment member `M⁽¹⁾`/`M⁽²⁾` (`DetachData.candidate`):

| new source vertex | incidences | surviving | `nd` |
|---|---|---|---|
| `t₂` endpoint over `A_p` | old `t₂`-in-`A_p`, new(`x`), new(rest of `A_p`) | 2 | 2 |
| `t₂` endpoint over `A_q` | old `t₂`-in-`A_q`, new(`A_q`) | 2 | 2 |
| `t₃` endpoint over `{x}` | old `e₄`, new(`x`) | 0 | 0 |
| `t₃` endpoint over `A₀ ∖ {x}` | old `e₃`, new(rest of `A_p`), new(`A_q`) | 3 | 3 |

For the joined member `M⁽³⁾` (`joinedCandidate`):

| new source vertex | incidences | surviving | `nd` |
|---|---|---|---|
| `t₂` endpoint over `A₀` | old `e₁`, old `e₂`, new(`A₀`) | 3 | 3 |
| `t₃` endpoint over `A₀` | old `e₃`, old `e₄`, new(`A₀`) | 2 | 2 |

The one substantive new item is row three of the first table: **the new
occurrence through the pinned sheet dies with `e₄`.**  That is what the second
detachment buys, and it is why the `t₃` endpoint of a detaching member is
divalent over `{x}` rather than carrying a surviving parallel pair.  Without
the second detachment this vertex does not exist, and the two occurrences above
`t₁` between the same pair of ends form a parallel pair -- a cycle over `t₁` of
the kind Draisma--Vargas Part I excludes (Position II.b of case
`{w3-r1-nd3-t2}`); see `GlobalMkk`.

Every statement is an identity of **occurrence** sets, never of row labels,
and no `Nodup` or pairwise-distinctness hypothesis on rows appears: a stable
loop may put two of the three survivors at a trivalent endpoint into one row
and nothing here excludes it.

## What is *not* done here

This module proves the census the M11 chain's `M11JoinedSurvival` proves, not
what `M11JoinedStableGraph` proves: no branch-vertex classification and no row
bijection appears below.  The stable lift, the row descent and the limit
matrices are `W2MkkStableLift`, `W2MkkRowDescent` and `W2MkkLimitMatrix`, as
instances of `LimitChainCore`; Equation (8) is `W2MkkCommonBalance`; and the
`StableGraphIncidence.Equivalence` -- the core's `GraphData`,
`selectedSide := true` for a detaching member and `false` for `M⁽³⁾` -- is
`W2MkkGraphData`.

## What is general, and where it lives

The endpoint geometry of a candidate retaining one wall direction — the pasted
resolution `pasted`, the two-endpoint incidence dictionary
`target_incident_pair_old/fresh`, the counts `card_incident_oldEndpoint` /
`card_incident_freshEndpoint`, `newSourceEdge_incident_old/fresh`,
`oldSourceEdge_ne_newSourceEdge`, `newSourceEdge_eq_iff_rel` — and the six
readers of a surviving star off a complete incidence list
(`forall_eq_of_card_two/three`, the four `nonDanglingIncident_*_of_card_*`)
are `LimitChainCore`'s, opened below.  So are `oldSourceEdge_incident_old`,
`survives_iff_of_card_two` and
`nonDanglingValency_eq_two_of_card_two_of_survives`.  Two short lemmas are
copied with a `_local` suffix from `M11JoinedBackground`, which this module
does not import: `background_ramification_zero_local` and
`background_blockCount_local`; neither statement mentions M11.

`detachSheet_blockCountWithin_of_not_rel` is general, a companion of
`SheetPartition.detachSheet_blockCard_of_not_rel`.
-/

namespace DraismaVargas.LocalCases.W2MkkStableGraph

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open ResolutionM11 ResolutionM1k GlobalM11Arbitrary
open W2MkkSourceCandidates
open LimitChainCore (pasted target_incident_pair_old target_incident_pair_fresh
  card_incident_oldEndpoint card_incident_freshEndpoint sourceEndpoint_old_eq_of_rel
  sourceEndpoint_fresh_eq_of_rel newSourceEdge_incident_old newSourceEdge_incident_fresh
  oldSourceEdge_ne_newSourceEdge newSourceEdge_eq_iff_rel forall_eq_of_card_two
  forall_eq_of_card_three nonDanglingIncident_pair_of_card_two
  nonDanglingIncident_empty_of_card_two nonDanglingIncident_pair_of_card_three
  nonDanglingIncident_triple_of_card_three oldSourceEdge_incident_old
  survives_iff_of_card_two nonDanglingValency_eq_two_of_card_two_of_survives)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
/-! ## One general partition lemma -/

/-- Detaching a sheet leaves every *other* block of its own partition alone:
one induced block, as before. -/
theorem detachSheet_blockCountWithin_of_not_rel (partition : SheetPartition degree)
    (single remainder sheet : Fin degree) (hne : single ≠ remainder)
    (hTogether : partition.Rel single remainder)
    (hNotRel : ¬ partition.Rel single sheet) :
    (partition.detachSheet single remainder hne hTogether).blockCountWithin
      partition sheet = 1 := by
  classical
  have hImage : (partition.block sheet).image
      (partition.detachSheet single remainder hne hTogether).repr =
        {partition.repr sheet} := by
    ext value
    simp only [Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨source, hSource, rfl⟩
      have hRel : partition.Rel sheet source :=
        (partition.mem_block_iff sheet source).mp hSource
      have hNot : ¬ partition.Rel single source := fun h ↦ hNotRel (h.trans hRel.symm)
      rw [partition.detachSheet_repr_of_not_rel single remainder source hne
        hTogether hNot]
      exact hRel.symm
    · rintro rfl
      refine ⟨sheet, (partition.mem_block_iff sheet sheet).mpr rfl, ?_⟩
      rw [partition.detachSheet_repr_of_not_rel single remainder sheet hne
        hTogether hNotRel]
  unfold SheetPartition.blockCountWithin
  rw [hImage, Finset.card_singleton]



/-! ## The `t₃` direction's induced block count on `A₀`

`W2MkkSourceCandidates.endpointPartition_blockCountWithin` is the `t₂` half:
`e₁` and `e₂` tile `A₀`.  The `t₃` half is the mirror statement, `e₃` and `e₄`,
and it is what both members' fresh endpoints need.
-/

section Single

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- The `t₃` direction's own occurrence partition. -/
abbrev singlePartition (profile : W2R2SourceProfile.SourceProfile data star block) :
    SheetPartition degree :=
  data.edgePartition (star.edge profile.singleLabel)

/-- The canonical sheet of `e₃`. -/
def thirdSheet (profile : W2R2SourceProfile.SourceProfile data star block) :
    Fin degree := profile.third.1.1.2

theorem thirdSheet_rel (profile : W2R2SourceProfile.SourceProfile data star block) :
    (data.vertexPartition wall).Rel block.1 (thirdSheet profile) :=
  sheet_rel_of_incident profile.third

theorem singlePartition_repr_third
    (profile : W2R2SourceProfile.SourceProfile data star block) :
    (singlePartition profile).repr (thirdSheet profile) = thirdSheet profile := by
  have h := profile.third.1.2
  rw [profile.third_target] at h
  exact h

theorem singlePartition_repr_pin (shape : Shape profile) :
    (singlePartition profile).repr (pinSheet profile) = pinSheet profile := by
  have h := profile.deleted.edge.1.2
  rw [shape.deleted_single] at h
  exact h

/-- `|e₃| = k₃`. -/
theorem singlePartition_blockCard_third
    (profile : W2R2SourceProfile.SourceProfile data star block) :
    (singlePartition profile).blockCard (thirdSheet profile) =
      data.sourceEdgeIndex profile.third.1 := by
  show (data.edgePartition (star.edge profile.singleLabel)).blockCard profile.third.1.1.2 =
    (data.edgePartition profile.third.1.1.1).blockCard profile.third.1.1.2
  rw [profile.third_target]

/-- `e₃` and `e₄` are distinct blocks of the `t₃` occurrence partition: their
indices are `k₃ ≥ 3` and `1`. -/
theorem singlePartition_separate (shape : Shape profile) :
    ¬(singlePartition profile).Rel (thirdSheet profile) (pinSheet profile) := by
  intro hRel
  have hCard := SheetPartition.blockCard_congr (singlePartition profile) hRel
  rw [singlePartition_blockCard_third, pinSheet_blockCard shape] at hCard
  have := shape.three_le_third
  omega

theorem thirdSheet_ne_pinSheet (shape : Shape profile) :
    thirdSheet profile ≠ pinSheet profile := by
  intro hEq
  exact singlePartition_separate shape (((singlePartition profile).rel_iff _ _).mpr (by rw [hEq]))

/-- **`e₃` and `e₄` tile `A₀`.**  Cardinality M puts both `t₃` occurrences of
the block in the `t₃` fibre, and the profile's exhaustion has no other. -/
theorem singlePartition_covers (shape : Shape profile) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    (singlePartition profile).Rel (thirdSheet profile) sheet ∨
      (singlePartition profile).Rel (pinSheet profile) sheet := by
  have hIncident : Incident data (data.sourceEdge (star.edge profile.singleLabel) sheet)
      (WallBlock.sourceVertex data wall block) := by
    apply (incident_wallBlock_sourceVertex_iff data block _).mpr
    refine ⟨star.edge_mem_incidentEdges profile.singleLabel, ?_⟩
    apply (WallBlock.ofSheet_eq_iff_rel data wall block _).mpr
    exact hSheet.trans ((star.edgePartition_refines_wall data profile.singleLabel).rel
      ((data.edgePartition (star.edge profile.singleLabel)).rel_repr_right sheet))
  have hNeLabel : star.edge profile.doubleLabel ≠ star.edge profile.singleLabel :=
    star.edge_injective.ne profile.labels_ne
  rcases profile.exhaustive ⟨_, hIncident⟩ with hEq | hEq | hEq | hEq
  · exact absurd ((congrArg (fun edge ↦ edge.1.1.1) hEq).trans profile.first_target)
      hNeLabel.symm
  · exact absurd ((congrArg (fun edge ↦ edge.1.1.1) hEq).trans profile.second_target)
      hNeLabel.symm
  · left
    have hSheet := congrArg (fun edge ↦ edge.1.1.2) hEq
    change (singlePartition profile).repr sheet = thirdSheet profile at hSheet
    rw [SheetPartition.rel_iff, singlePartition_repr_third, hSheet]
  · right
    have hSheet := congrArg (fun edge ↦ edge.1.1.2) hEq
    change (singlePartition profile).repr sheet = pinSheet profile at hSheet
    rw [SheetPartition.rel_iff, singlePartition_repr_pin shape, hSheet]

/-- **The exact induced-block count of the `t₃` direction on `A₀`: two.** -/
theorem singlePartition_blockCountWithin (shape : Shape profile) (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    (singlePartition profile).blockCountWithin (data.vertexPartition wall) anchor = 2 := by
  classical
  have hThirdMem : thirdSheet profile ∈ (data.vertexPartition wall).block anchor :=
    ((data.vertexPartition wall).mem_block_iff anchor _).mpr
      (hAnchor.symm.trans (thirdSheet_rel profile))
  have hPinMem : pinSheet profile ∈ (data.vertexPartition wall).block anchor :=
    ((data.vertexPartition wall).mem_block_iff anchor _).mpr
      (hAnchor.symm.trans (pinSheet_rel profile))
  have hImage : ((data.vertexPartition wall).block anchor).image
      (singlePartition profile).repr = {thirdSheet profile, pinSheet profile} := by
    ext value
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton,
      SheetPartition.mem_block_iff]
    constructor
    · rintro ⟨source, hSource, rfl⟩
      rcases singlePartition_covers shape source (hAnchor.trans hSource) with h | h
      · exact Or.inl (by rw [← singlePartition_repr_third profile, h])
      · exact Or.inr (by rw [← singlePartition_repr_pin shape, h])
    · rintro (rfl | rfl)
      · exact ⟨thirdSheet profile, (((data.vertexPartition wall).mem_block_iff anchor _).mp
          hThirdMem), singlePartition_repr_third profile⟩
      · exact ⟨pinSheet profile, (((data.vertexPartition wall).mem_block_iff anchor _).mp
          hPinMem), singlePartition_repr_pin shape⟩
  unfold SheetPartition.blockCountWithin
  rw [hImage, Finset.card_insert_of_notMem (by
    simpa using thirdSheet_ne_pinSheet shape), Finset.card_singleton]

end Single

/-! ## The detachment member's endpoint census

`M⁽¹⁾`/`M⁽²⁾` is `DetachData.candidate`: the `t₂` endpoint keeps `e₁ ⊔ e₂`, the
new edge additionally detaches the pinned sheet `x` from its own endpoint
block, and the `t₃` endpoint detaches `x` from the whole of `A₀`.
-/

section Detach

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- The member's side assignment is the oriented two-star's own. -/
theorem detach_right (shape : Shape profile) (detach : DetachData profile)
    (edge : target.edges) :
    (detach.candidate shape).right edge = (orientedStar profile).right edge := rfl

/-- On the distinguished block the member is literally `DetachData.selected`. -/
theorem detach_resolution (shape : Shape profile) (detach : DetachData profile)
    (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel (pinSheet profile) anchor) :
    (detach.candidate shape).resolution anchor = detach.selected := by
  change LocalResolution.onBlock (data.vertexPartition wall) (pinSheet profile)
    detach.selected (fun _ ↦ joinedResolutionAt (data.vertexPartition wall)) anchor = _
  rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hAnchor]

theorem detach_blockCountWithin_left (shape : Shape profile) (detach : DetachData profile)
    (fine : SheetPartition degree) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel (pinSheet profile) sheet) :
    fine.blockCountWithin (pasted (detach.candidate shape)).left sheet =
      fine.blockCountWithin (endpointPartition profile) sheet := by
  rw [LocalResolution.blockCountWithin_paste_left, detach_resolution shape detach _
    (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  rfl

theorem detach_blockCountWithin_right (shape : Shape profile) (detach : DetachData profile)
    (fine : SheetPartition degree) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel (pinSheet profile) sheet) :
    fine.blockCountWithin (pasted (detach.candidate shape)).right sheet =
      fine.blockCountWithin ((data.vertexPartition wall).detachSheet (pinSheet profile)
        detach.remainder detach.ne_remainder detach.wallTogether) sheet := by
  rw [LocalResolution.blockCountWithin_paste_right, detach_resolution shape detach _
    (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  rfl

theorem detach_newEdge_within_left (shape : Shape profile) (detach : DetachData profile)
    (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel (pinSheet profile) sheet) :
    (pasted (detach.candidate shape)).newEdge.blockCountWithin
        (pasted (detach.candidate shape)).left sheet =
      ((endpointPartition profile).detachSheet (pinSheet profile) detach.remainder
        detach.ne_remainder detach.together).blockCountWithin
          (endpointPartition profile) sheet := by
  rw [LocalResolution.paste_newEdge_blockCountWithin_left, detach_resolution shape detach _
    (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  rfl

theorem detach_newEdge_within_right (shape : Shape profile) (detach : DetachData profile)
    (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel (pinSheet profile) sheet) :
    (pasted (detach.candidate shape)).newEdge.blockCountWithin
        (pasted (detach.candidate shape)).right sheet =
      ((endpointPartition profile).detachSheet (pinSheet profile) detach.remainder
        detach.ne_remainder detach.together).blockCountWithin
          ((data.vertexPartition wall).detachSheet (pinSheet profile) detach.remainder
            detach.ne_remainder detach.wallTogether) sheet := by
  rw [LocalResolution.paste_newEdge_blockCountWithin_right, detach_resolution shape detach _
    (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  rfl

/-- **Three incidences at the `t₂` endpoint over the pinned block `A_p`**: the
retained `t₂` occurrence, the new occurrence through `x`, and the new
occurrence through the rest of `A_p`. -/
theorem detach_card_incident_old_pin (shape : Shape profile) (detach : DetachData profile)
    (sheet : Fin degree)
    (hSheet : (endpointPartition profile).Rel (pinSheet profile) sheet) :
    Fintype.card (IncidentSourceEdge (detach.candidate shape).datum
      ((detach.candidate shape).datum.sourceEndpoint (oldVertex target wall) sheet)) = 3 := by
  have hWall : (data.vertexPartition wall).Rel (pinSheet profile) sheet :=
    (endpointPartition_refines profile).rel hSheet
  rw [card_incident_oldEndpoint (twoStar := orientedStar profile)
      (detach_right shape detach),
    detach_newEdge_within_left shape detach sheet hWall,
    orientedStar_edge_zero, detach_blockCountWithin_left shape detach _ sheet hWall,
    W3ShiftSourceCandidates.detachSheet_blockCountWithin_self (endpointPartition profile)
      (pinSheet profile) detach.remainder sheet detach.ne_remainder detach.together hSheet]
  show 2 + (endpointPartition profile).blockCountWithin (endpointPartition profile) sheet = 3
  rw [SheetPartition.blockCountWithin_self]

/-- **Two incidences at the `t₂` endpoint over the other block `A_q`**: the
retained `t₂` occurrence and the new occurrence through `A_q`. -/
theorem detach_card_incident_old_other (shape : Shape profile) (detach : DetachData profile)
    (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile) sheet)
    (hNot : ¬(endpointPartition profile).Rel (pinSheet profile) sheet) :
    Fintype.card (IncidentSourceEdge (detach.candidate shape).datum
      ((detach.candidate shape).datum.sourceEndpoint (oldVertex target wall) sheet)) = 2 := by
  rw [card_incident_oldEndpoint (twoStar := orientedStar profile)
      (detach_right shape detach),
    detach_newEdge_within_left shape detach sheet hWall,
    orientedStar_edge_zero, detach_blockCountWithin_left shape detach _ sheet hWall,
    detachSheet_blockCountWithin_of_not_rel (endpointPartition profile)
      (pinSheet profile) detach.remainder sheet detach.ne_remainder detach.together hNot]
  show 1 + (endpointPartition profile).blockCountWithin (endpointPartition profile) sheet = 2
  rw [SheetPartition.blockCountWithin_self]

/-- **Two incidences at the `t₃` endpoint over the singleton `{x}`**: the
retained dangling `e₄` and the new occurrence through `x`.  This vertex is the
whole content of the second detachment. -/
theorem detach_card_incident_fresh_pin (shape : Shape profile) (detach : DetachData profile) :
    Fintype.card (IncidentSourceEdge (detach.candidate shape).datum
      ((detach.candidate shape).datum.sourceEndpoint (freshVertex target)
        (pinSheet profile))) = 2 := by
  have hSingleton : ((data.vertexPartition wall).detachSheet (pinSheet profile)
      detach.remainder detach.ne_remainder detach.wallTogether).block (pinSheet profile) =
      {pinSheet profile} :=
    (data.vertexPartition wall).detachSheet_block_single (pinSheet profile)
      detach.remainder detach.ne_remainder detach.wallTogether
  rw [card_incident_freshEndpoint (twoStar := orientedStar profile)
      (detach_right shape detach),
    detach_newEdge_within_right shape detach _
      (show (data.vertexPartition wall).Rel (pinSheet profile) (pinSheet profile) from rfl),
    orientedStar_edge_one,
    detach_blockCountWithin_right shape detach _ _
      (show (data.vertexPartition wall).Rel (pinSheet profile) (pinSheet profile) from rfl),
    SheetPartition.blockCountWithin_eq_one_of_block_eq_singleton _ _ _ hSingleton,
    SheetPartition.blockCountWithin_eq_one_of_block_eq_singleton _ _ _ hSingleton]

/-- **Three incidences at the `t₃` endpoint over `A⁽ᵠ⁾ = A₀ ∖ {x}`**: the
retained `e₃`, the new occurrence through the rest of `A_p`, and the new
occurrence through `A_q`. -/
theorem detach_card_incident_fresh_other (shape : Shape profile)
    (detach : DetachData profile) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile) sheet)
    (hNe : sheet ≠ pinSheet profile) :
    Fintype.card (IncidentSourceEdge (detach.candidate shape).datum
      ((detach.candidate shape).datum.sourceEndpoint (freshVertex target) sheet)) = 3 := by
  have hNewSingle : ((endpointPartition profile).detachSheet (pinSheet profile)
      detach.remainder detach.ne_remainder detach.together).block (pinSheet profile) =
      {pinSheet profile} :=
    (endpointPartition profile).detachSheet_block_single (pinSheet profile)
      detach.remainder detach.ne_remainder detach.together
  have hNew := W3ShiftSourceCandidates.blockCountWithin_detachSheet_of_singleton
    ((endpointPartition profile).detachSheet (pinSheet profile) detach.remainder
      detach.ne_remainder detach.together)
    (data.vertexPartition wall) (pinSheet profile) detach.remainder sheet
    detach.ne_remainder detach.wallTogether hNewSingle hWall hNe
  have hOld := W3ShiftSourceCandidates.blockCountWithin_detachSheet_of_singleton
    (singlePartition profile) (data.vertexPartition wall) (pinSheet profile)
    detach.remainder sheet detach.ne_remainder detach.wallTogether
    (pinSheet_block shape) hWall hNe
  have hNewTotal := (detach_blockCountWithin shape detach sheet
    ((pinSheet_rel profile).trans hWall)).2.1
  have hOldTotal := singlePartition_blockCountWithin shape sheet
    ((pinSheet_rel profile).trans hWall)
  rw [DetachData.selected_newEdge] at hNewTotal
  rw [card_incident_freshEndpoint (twoStar := orientedStar profile)
      (detach_right shape detach),
    detach_newEdge_within_right shape detach sheet hWall, orientedStar_edge_one,
    detach_blockCountWithin_right shape detach _ sheet hWall]
  have hOldStep : (data.edgePartition (star.edge profile.singleLabel)).blockCountWithin
      ((data.vertexPartition wall).detachSheet (pinSheet profile) detach.remainder
        detach.ne_remainder detach.wallTogether) sheet + 1 =
      (data.edgePartition (star.edge profile.singleLabel)).blockCountWithin
        (data.vertexPartition wall) sheet := hOld
  have hOldValue : (data.edgePartition (star.edge profile.singleLabel)).blockCountWithin
      (data.vertexPartition wall) sheet = 2 := hOldTotal
  omega

/-- Sheets of one `t₂` endpoint block over `A₀` share a retained new endpoint. -/
theorem detach_pasted_left_rel (shape : Shape profile) (detach : DetachData profile)
    (first second : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile) first)
    (hRel : (endpointPartition profile).Rel first second) :
    (pasted (detach.candidate shape)).left.Rel first second := by
  show (LocalResolution.pasteLeft (data.vertexPartition wall)
    (detach.candidate shape).resolution (detach.candidate shape).contracts).Rel first second
  unfold LocalResolution.pasteLeft
  rw [SheetPartition.paste_rel_iff, detach_resolution shape detach _
    (hWall.trans ((data.vertexPartition wall).rel_repr_right first))]
  exact hRel

/-- Over `A₀` the pasted new edge is the member's own detached `t₂`
endpoint. -/
theorem detach_pasted_newEdge_rel_iff (shape : Shape profile) (detach : DetachData profile)
    (first second : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile) first) :
    (pasted (detach.candidate shape)).newEdge.Rel first second ↔
      ((endpointPartition profile).detachSheet (pinSheet profile) detach.remainder
        detach.ne_remainder detach.together).Rel first second := by
  show (LocalResolution.pasteNewEdge (data.vertexPartition wall)
    (detach.candidate shape).resolution (detach.candidate shape).contracts).Rel first second ↔ _
  unfold LocalResolution.pasteNewEdge
  rw [SheetPartition.paste_rel_iff, detach_resolution shape detach _
    (hWall.trans ((data.vertexPartition wall).rel_repr_right first)),
    DetachData.selected_newEdge]

/-! ### Which occurrences of the detachment member survive -/

theorem detach_right_double (shape : Shape profile) (detach : DetachData profile) :
    (detach.candidate shape).right (star.edge profile.doubleLabel) = false := by
  rw [detach_right, ← orientedStar_edge_zero profile]
  exact TwoStar.right_edge_zero _

theorem detach_right_single (shape : Shape profile) (detach : DetachData profile) :
    (detach.candidate shape).right (star.edge profile.singleLabel) = true := by
  rw [detach_right, ← orientedStar_edge_one profile]
  exact TwoStar.right_edge_one _

/-- Both `t₂` survivors of `A₀` survive: the block's only dangling occurrence
is `e₄`, which Cardinality M puts above `t₃`.  Same argument as
`M11SplitSurvival.double_sourceEdge_survives`, with `Shape.deleted_single` in
place of the two-sheet hypothesis. -/
theorem double_sourceEdge_survives_shape (shape : Shape profile) (sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    ¬ IsDangling data (data.sourceEdge (star.edge profile.doubleLabel) sheet) := by
  have hAt := star.edge_mem_incidentEdges profile.doubleLabel
  have hRefines := refines_of_mem_incidentEdges data hAt
  have hRepresentative := hRefines.rel
    ((data.edgePartition (star.edge profile.doubleLabel)).rel_repr_right sheet)
  have hIncident : Incident data (data.sourceEdge (star.edge profile.doubleLabel) sheet)
      (WallBlock.sourceVertex data wall block) := by
    apply (incident_wallBlock_sourceVertex_iff data block _).mpr
    exact ⟨hAt, Subtype.ext (hRepresentative.symm.trans (hRel.symm.trans block.2))⟩
  intro hDangling
  have hDeleted := (profile.deleted.unique
    ⟨data.sourceEdge (star.edge profile.doubleLabel) sheet, hIncident⟩).mp hDangling
  have hTarget : star.edge profile.doubleLabel = profile.deleted.edge.1.1.1 :=
    congrArg (fun item : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall block) ↦ item.1.1.1) hDeleted
  exact profile.labels_ne (star.edge_injective (hTarget.trans shape.deleted_single))

/-- The retained `t₂` occurrence through a sheet meets the retained endpoint
over that sheet. -/
theorem detach_double_incident (shape : Shape profile) (detach : DetachData profile)
    (sheet : Fin degree) :
    Incident (detach.candidate shape).datum
      ((detach.candidate shape).oldSourceEdge
        (data.sourceEdge (star.edge profile.doubleLabel) sheet))
      ((detach.candidate shape).datum.sourceEndpoint (oldVertex target wall) sheet) :=
  oldSourceEdge_incident_old _ _ (star.edge_mem_incidentEdges profile.doubleLabel)
    (detach_right_double shape detach) sheet

/-- The retained dangling `e₄` meets the fresh endpoint over the pinned
sheet. -/
theorem detach_deleted_incident (shape : Shape profile) (detach : DetachData profile) :
    Incident (detach.candidate shape).datum
      ((detach.candidate shape).oldSourceEdge profile.deleted.edge.1)
      ((detach.candidate shape).datum.sourceEndpoint (freshVertex target)
        (pinSheet profile)) := by
  have hAt : profile.deleted.edge.1.1.1 ∈ GluingDatum.incidentEdges wall := by
    rw [shape.deleted_single]
    exact star.edge_mem_incidentEdges profile.singleLabel
  have hRight : (detach.candidate shape).right profile.deleted.edge.1.1.1 = true := by
    rw [shape.deleted_single]
    exact detach_right_single shape detach
  have h := M11SplitSurvival.oldSourceEdge_incident_fresh (detach.candidate shape)
    profile.deleted.edge.1.1.1 hAt hRight (pinSheet profile)
  rwa [show data.sourceEdge profile.deleted.edge.1.1.1 (pinSheet profile) =
    profile.deleted.edge.1 from GluingDatum.sourceEdge_self data profile.deleted.edge.1] at h

/-- The retained `e₃` meets the fresh endpoint over its own sheet. -/
theorem detach_third_incident (shape : Shape profile) (detach : DetachData profile) :
    Incident (detach.candidate shape).datum
      ((detach.candidate shape).oldSourceEdge profile.third.1)
      ((detach.candidate shape).datum.sourceEndpoint (freshVertex target)
        (thirdSheet profile)) := by
  have hAt : profile.third.1.1.1 ∈ GluingDatum.incidentEdges wall := by
    rw [profile.third_target]
    exact star.edge_mem_incidentEdges profile.singleLabel
  have hRight : (detach.candidate shape).right profile.third.1.1.1 = true := by
    rw [profile.third_target]
    exact detach_right_single shape detach
  have h := M11SplitSurvival.oldSourceEdge_incident_fresh (detach.candidate shape)
    profile.third.1.1.1 hAt hRight (thirdSheet profile)
  rwa [show data.sourceEdge profile.third.1.1.1 (thirdSheet profile) = profile.third.1 from
    GluingDatum.sourceEdge_self data profile.third.1] at h

/-- Genus-preserving pruning keeps `e₄` dangling. -/
theorem detach_deleted_dangling (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) :
    IsDangling (detach.candidate shape).datum
      ((detach.candidate shape).oldSourceEdge profile.deleted.edge.1) :=
  (ResolutionPruning.isDangling_oldSourceEdge_iff _ input.valid
    (detach_sourceGenus shape detach) _).mpr profile.deleted.dangling

/-- **The new occurrence through the pinned sheet dies with `e₄`.**  Its fresh
endpoint is the divalent source vertex `{x}`, whose only other incidence is the
retained dangling `e₄`; surviving valency one is impossible, so the pair
dangles together.  This is what the *second* detachment buys: without it
there is no such vertex, and the two occurrences above `t₁` between the same
pair of ends form a parallel pair, which Draisma--Vargas Part I excludes. -/
theorem detach_new_pin_dangling (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) :
    IsDangling (detach.candidate shape).datum
      ((detach.candidate shape).newSourceEdge (pinSheet profile)) := by
  by_contra hSurvives
  exact ((survives_iff_of_card_two (detach.candidate shape).datum
    (detach_valid input shape detach).1
    ((detach.candidate shape).datum.sourceEndpoint (freshVertex target) (pinSheet profile))
    ((detach.candidate shape).newSourceEdge (pinSheet profile))
    ((detach.candidate shape).oldSourceEdge profile.deleted.edge.1)
    (newSourceEdge_incident_fresh _) (detach_deleted_incident shape detach)
    (detach_card_incident_fresh_pin shape detach)).mp hSurvives)
    (detach_deleted_dangling input shape detach)

/-- Every other new occurrence over `A₀` survives.  Over `A_q` the retained
endpoint is divalent and its retained `t₂` occurrence survives; over
`A_p ∖ {x}` it is trivalent with the pinned arm already deleted. -/
theorem detach_new_survives (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile) sheet)
    (hNe : sheet ≠ pinSheet profile) :
    ¬ IsDangling (detach.candidate shape).datum
      ((detach.candidate shape).newSourceEdge sheet) := by
  have hBlock : (data.vertexPartition wall).Rel block.1 sheet :=
    (pinSheet_rel profile).trans hWall
  have hOldSurvives := ResolutionSurvival.not_isDangling_oldSourceEdge
    (detach.candidate shape) input.valid.1 _
    (double_sourceEdge_survives_shape shape sheet hBlock)
  by_cases hSame : (endpointPartition profile).Rel (pinSheet profile) sheet
  · -- the pinned `t₂` endpoint block: trivalent, with the pinned arm deleted
    have hVertexEq : (detach.candidate shape).datum.sourceEndpoint (oldVertex target wall)
        (pinSheet profile) =
        (detach.candidate shape).datum.sourceEndpoint (oldVertex target wall) sheet :=
      sourceEndpoint_old_eq_of_rel _ _
        (detach_pasted_left_rel shape detach _ _ rfl hSame)
    have hPinIncident : Incident (detach.candidate shape).datum
        ((detach.candidate shape).newSourceEdge (pinSheet profile))
        ((detach.candidate shape).datum.sourceEndpoint (oldVertex target wall) sheet) :=
      hVertexEq ▸ newSourceEdge_incident_old _
    refine M11SplitSurvival.survives_of_trivalent_of_deleted (detach.candidate shape).datum
      (detach_valid input shape detach).1 _
      ⟨_, detach_double_incident shape detach sheet⟩
      ⟨_, hPinIncident⟩ ⟨_, newSourceEdge_incident_old _⟩ hOldSurvives
      (detach_new_pin_dangling input shape detach) ?_
      (detach_card_incident_old_pin shape detach sheet hSame)
    intro hEqual
    have hEdges := congrArg (fun item : IncidentSourceEdge (detach.candidate shape).datum
      ((detach.candidate shape).datum.sourceEndpoint (oldVertex target wall) sheet) ↦
        item.1) hEqual
    have hRel := (detach_pasted_newEdge_rel_iff shape detach _ _ rfl).mp
      ((newSourceEdge_eq_iff_rel _ _).mp hEdges)
    refine hNe ?_
    have hSingle : ((endpointPartition profile).detachSheet (pinSheet profile)
        detach.remainder detach.ne_remainder detach.together).block (pinSheet profile) =
        {pinSheet profile} :=
      (endpointPartition profile).detachSheet_block_single (pinSheet profile)
        detach.remainder detach.ne_remainder detach.together
    have hMem : sheet ∈ ((endpointPartition profile).detachSheet (pinSheet profile)
        detach.remainder detach.ne_remainder detach.together).block (pinSheet profile) :=
      (((endpointPartition profile).detachSheet (pinSheet profile) detach.remainder
        detach.ne_remainder detach.together).mem_block_iff _ _).mpr hRel
    rw [hSingle] at hMem
    simpa using hMem
  · -- the other `t₂` endpoint block: divalent
    refine (survives_iff_of_card_two (detach.candidate shape).datum
      (detach_valid input shape detach).1 _ _
      ((detach.candidate shape).newSourceEdge sheet)
      (detach_double_incident shape detach sheet) (newSourceEdge_incident_old _)
      (detach_card_incident_old_other shape detach sheet hWall hSame)).mp hOldSurvives

/-! ### The surviving stars of the detachment member -/

/-- A sheet of the `t₂` endpoint block that does **not** contain the pinned
sheet.  It exists because `e₁`, `e₂` are distinct blocks tiling `A₀` and the
pinned sheet lies in exactly one of them. -/
noncomputable def otherSheet (profile : W2R2SourceProfile.SourceProfile data star block) :
    Fin degree := by
  classical
  exact if (endpointPartition profile).Rel (firstSheet profile) (pinSheet profile) then
    secondSheet profile else firstSheet profile

theorem otherSheet_not_rel (profile : W2R2SourceProfile.SourceProfile data star block) :
    ¬(endpointPartition profile).Rel (pinSheet profile) (otherSheet profile) := by
  classical
  by_cases hFirst : (endpointPartition profile).Rel (firstSheet profile) (pinSheet profile)
  · simp only [otherSheet, hFirst, ↓reduceIte]
    intro hRel
    exact endpointPartition_separate profile (hFirst.trans hRel)
  · simp only [otherSheet, hFirst, ↓reduceIte]
    exact fun hRel ↦ hFirst hRel.symm

theorem otherSheet_wall_rel (profile : W2R2SourceProfile.SourceProfile data star block) :
    (data.vertexPartition wall).Rel (pinSheet profile) (otherSheet profile) := by
  classical
  by_cases hFirst : (endpointPartition profile).Rel (firstSheet profile) (pinSheet profile)
  · simp only [otherSheet, hFirst, ↓reduceIte]
    exact (pinSheet_rel profile).symm.trans (secondSheet_rel profile)
  · simp only [otherSheet, hFirst, ↓reduceIte]
    exact (pinSheet_rel profile).symm.trans (firstSheet_rel profile)

theorem otherSheet_ne_pinSheet (profile : W2R2SourceProfile.SourceProfile data star block) :
    otherSheet profile ≠ pinSheet profile := by
  intro hEq
  exact otherSheet_not_rel profile
    (((endpointPartition profile).rel_iff _ _).mpr (by rw [hEq]))

/-- Sheets of `A₀ ∖ {x}` share the member's fresh new endpoint. -/
theorem detach_pasted_right_rel (shape : Shape profile) (detach : DetachData profile)
    (first second : Fin degree)
    (hFirstWall : (data.vertexPartition wall).Rel (pinSheet profile) first)
    (hFirstNe : first ≠ pinSheet profile)
    (hSecondWall : (data.vertexPartition wall).Rel (pinSheet profile) second)
    (hSecondNe : second ≠ pinSheet profile) :
    (pasted (detach.candidate shape)).right.Rel first second := by
  have hFirstRem := W3ShiftSourceCandidates.detachSheet_rel_remainder
    (data.vertexPartition wall) (pinSheet profile) detach.remainder first
    detach.ne_remainder detach.wallTogether hFirstWall hFirstNe
  have hSecondRem := W3ShiftSourceCandidates.detachSheet_rel_remainder
    (data.vertexPartition wall) (pinSheet profile) detach.remainder second
    detach.ne_remainder detach.wallTogether hSecondWall hSecondNe
  show (LocalResolution.pasteRight (data.vertexPartition wall)
    (detach.candidate shape).resolution (detach.candidate shape).contracts).Rel first second
  unfold LocalResolution.pasteRight
  rw [SheetPartition.paste_rel_iff, detach_resolution shape detach _
    (hFirstWall.trans ((data.vertexPartition wall).rel_repr_right first))]
  exact hFirstRem.trans hSecondRem.symm

theorem detach_fresh_vertex_eq (shape : Shape profile) (detach : DetachData profile)
    (first second : Fin degree)
    (hFirstWall : (data.vertexPartition wall).Rel (pinSheet profile) first)
    (hFirstNe : first ≠ pinSheet profile)
    (hSecondWall : (data.vertexPartition wall).Rel (pinSheet profile) second)
    (hSecondNe : second ≠ pinSheet profile) :
    (detach.candidate shape).datum.sourceEndpoint (freshVertex target) first =
      (detach.candidate shape).datum.sourceEndpoint (freshVertex target) second :=
  sourceEndpoint_fresh_eq_of_rel _ _
    (detach_pasted_right_rel shape detach first second hFirstWall hFirstNe hSecondWall hSecondNe)

/-- The pinned new occurrence is not any other new occurrence over `A₀`. -/
theorem detach_newSourceEdge_pin_ne (shape : Shape profile) (detach : DetachData profile)
    (sheet : Fin degree) (hNe : sheet ≠ pinSheet profile) :
    (detach.candidate shape).newSourceEdge (pinSheet profile) ≠
      (detach.candidate shape).newSourceEdge sheet := by
  intro hEqual
  refine hNe ?_
  have hRel := (detach_pasted_newEdge_rel_iff shape detach _ _ rfl).mp
    ((newSourceEdge_eq_iff_rel _ _).mp hEqual)
  have hSingle : ((endpointPartition profile).detachSheet (pinSheet profile)
      detach.remainder detach.ne_remainder detach.together).block (pinSheet profile) =
      {pinSheet profile} :=
    (endpointPartition profile).detachSheet_block_single (pinSheet profile)
      detach.remainder detach.ne_remainder detach.together
  have hMem : sheet ∈ ((endpointPartition profile).detachSheet (pinSheet profile)
      detach.remainder detach.ne_remainder detach.together).block (pinSheet profile) :=
    (((endpointPartition profile).detachSheet (pinSheet profile) detach.remainder
      detach.ne_remainder detach.together).mem_block_iff _ _).mpr hRel
  rw [hSingle] at hMem
  simpa using hMem

/-- The two surviving new occurrences of the member are distinct: one lies
over `A_p ∖ {x}`, the other over `A_q`. -/
theorem detach_newSourceEdge_ne (shape : Shape profile) (detach : DetachData profile)
    (first second : Fin degree)
    (hFirstWall : (data.vertexPartition wall).Rel (pinSheet profile) first)
    (hFirstEp : (endpointPartition profile).Rel (pinSheet profile) first)
    (hSecondEp : ¬(endpointPartition profile).Rel (pinSheet profile) second) :
    (detach.candidate shape).newSourceEdge first ≠
      (detach.candidate shape).newSourceEdge second := by
  intro hEqual
  have hRel := (detach_pasted_newEdge_rel_iff shape detach _ _ hFirstWall).mp
    ((newSourceEdge_eq_iff_rel _ _).mp hEqual)
  exact hSecondEp (hFirstEp.trans
    ((endpointPartition profile).detachSheet_refines (pinSheet profile) detach.remainder
      detach.ne_remainder detach.together |>.rel hRel))

/-- **The surviving star at a `t₂` endpoint of the detachment member.**  Over
either endpoint block the surviving pair is the retained `t₂` occurrence
through the sheet and the new occurrence through the sheet; over the pinned
block the third incidence, the new occurrence through `x`, has been pruned. -/
theorem detach_nonDanglingIncident_old (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile) sheet)
    (hNe : sheet ≠ pinSheet profile) :
    nonDanglingIncident (detach.candidate shape).datum
        ((detach.candidate shape).datum.sourceEndpoint (oldVertex target wall) sheet) =
      {(detach.candidate shape).oldSourceEdge
          (data.sourceEdge (star.edge profile.doubleLabel) sheet),
        (detach.candidate shape).newSourceEdge sheet} := by
  have hBlock : (data.vertexPartition wall).Rel block.1 sheet :=
    (pinSheet_rel profile).trans hWall
  have hOldSurvives := ResolutionSurvival.not_isDangling_oldSourceEdge
    (detach.candidate shape) input.valid.1 _
    (double_sourceEdge_survives_shape shape sheet hBlock)
  have hNewSurvives := detach_new_survives input shape detach sheet hWall hNe
  by_cases hSame : (endpointPartition profile).Rel (pinSheet profile) sheet
  · have hVertexEq : (detach.candidate shape).datum.sourceEndpoint (oldVertex target wall)
        (pinSheet profile) =
        (detach.candidate shape).datum.sourceEndpoint (oldVertex target wall) sheet :=
      sourceEndpoint_old_eq_of_rel _ _
        (detach_pasted_left_rel shape detach _ _ rfl hSame)
    refine nonDanglingIncident_pair_of_card_three _
      (detach_double_incident shape detach sheet) (newSourceEdge_incident_old _)
      (hVertexEq ▸ newSourceEdge_incident_old _)
      (oldSourceEdge_ne_newSourceEdge _ _) (oldSourceEdge_ne_newSourceEdge _ _)
      (Ne.symm (detach_newSourceEdge_pin_ne shape detach sheet hNe))
      hOldSurvives hNewSurvives (detach_new_pin_dangling input shape detach)
      (detach_card_incident_old_pin shape detach sheet hSame)
  · exact nonDanglingIncident_pair_of_card_two _
      (detach_double_incident shape detach sheet) (newSourceEdge_incident_old _)
      (oldSourceEdge_ne_newSourceEdge _ _) hOldSurvives hNewSurvives
      (detach_card_incident_old_other shape detach sheet hWall hSame)

theorem detach_nonDanglingValency_old (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile) sheet)
    (hNe : sheet ≠ pinSheet profile) :
    nonDanglingValency (detach.candidate shape).datum
      ((detach.candidate shape).datum.sourceEndpoint (oldVertex target wall) sheet) = 2 := by
  rw [← card_nonDanglingIncident,
    detach_nonDanglingIncident_old input shape detach sheet hWall hNe,
    Finset.card_pair (oldSourceEdge_ne_newSourceEdge _ _)]

/-- **Nothing survives at the `t₃` endpoint over `{x}`.**  Its two incidences
are the retained dangling `e₄` and the new occurrence through `x`. -/
theorem detach_nonDanglingIncident_fresh_pin (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile) :
    nonDanglingIncident (detach.candidate shape).datum
      ((detach.candidate shape).datum.sourceEndpoint (freshVertex target)
        (pinSheet profile)) = ∅ :=
  nonDanglingIncident_empty_of_card_two _ (detach_deleted_incident shape detach)
    (newSourceEdge_incident_fresh _) (oldSourceEdge_ne_newSourceEdge _ _)
    (detach_deleted_dangling input shape detach)
    (detach_new_pin_dangling input shape detach)
    (detach_card_incident_fresh_pin shape detach)

theorem detach_nonDanglingValency_fresh_pin (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile) :
    nonDanglingValency (detach.candidate shape).datum
      ((detach.candidate shape).datum.sourceEndpoint (freshVertex target)
        (pinSheet profile)) = 0 := by
  rw [← card_nonDanglingIncident,
    detach_nonDanglingIncident_fresh_pin input shape detach, Finset.card_empty]

/-- **The `t₃` endpoint over `A⁽ᵠ⁾ = A₀ ∖ {x}` is a branch vertex.**  All three
of its incidences survive: the retained `e₃`, the new occurrence over
`A_p ∖ {x}` and the new occurrence over `A_q`. -/
theorem detach_nonDanglingIncident_fresh (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile) sheet)
    (hNe : sheet ≠ pinSheet profile) :
    nonDanglingIncident (detach.candidate shape).datum
        ((detach.candidate shape).datum.sourceEndpoint (freshVertex target) sheet) =
      {(detach.candidate shape).oldSourceEdge profile.third.1,
        (detach.candidate shape).newSourceEdge detach.remainder,
        (detach.candidate shape).newSourceEdge (otherSheet profile)} := by
  have hThirdWall : (data.vertexPartition wall).Rel (pinSheet profile) (thirdSheet profile) :=
    (pinSheet_rel profile).symm.trans (thirdSheet_rel profile)
  have hRemNe : detach.remainder ≠ pinSheet profile := Ne.symm detach.ne_remainder
  have hOtherNe : otherSheet profile ≠ pinSheet profile := otherSheet_ne_pinSheet profile
  refine nonDanglingIncident_triple_of_card_three _
    (detach_fresh_vertex_eq shape detach (thirdSheet profile) sheet hThirdWall
      (thirdSheet_ne_pinSheet shape) hWall hNe ▸ detach_third_incident shape detach)
    (detach_fresh_vertex_eq shape detach detach.remainder sheet detach.wallTogether
      hRemNe hWall hNe ▸ newSourceEdge_incident_fresh _)
    (detach_fresh_vertex_eq shape detach (otherSheet profile) sheet
      (otherSheet_wall_rel profile) hOtherNe hWall hNe ▸ newSourceEdge_incident_fresh _)
    (oldSourceEdge_ne_newSourceEdge _ _) (oldSourceEdge_ne_newSourceEdge _ _)
    (detach_newSourceEdge_ne shape detach detach.remainder (otherSheet profile)
      detach.wallTogether detach.together (otherSheet_not_rel profile))
    (ResolutionSurvival.not_isDangling_oldSourceEdge (detach.candidate shape)
      input.valid.1 _ profile.third_survives)
    (detach_new_survives input shape detach detach.remainder detach.wallTogether hRemNe)
    (detach_new_survives input shape detach (otherSheet profile)
      (otherSheet_wall_rel profile) hOtherNe)
    (detach_card_incident_fresh_other shape detach sheet hWall hNe)

theorem detach_nonDanglingValency_fresh (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile) sheet)
    (hNe : sheet ≠ pinSheet profile) :
    nonDanglingValency (detach.candidate shape).datum
      ((detach.candidate shape).datum.sourceEndpoint (freshVertex target) sheet) = 3 := by
  classical
  rw [← card_nonDanglingIncident,
    detach_nonDanglingIncident_fresh input shape detach sheet hWall hNe,
    Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (hEq | hEq)
      · exact oldSourceEdge_ne_newSourceEdge _ _ hEq
      · exact oldSourceEdge_ne_newSourceEdge _ _ hEq),
    Finset.card_pair (detach_newSourceEdge_ne shape detach detach.remainder
      (otherSheet profile) detach.wallTogether detach.together (otherSheet_not_rel profile))]

/-! ### The surviving new occurrences' stable rows

At every `t₂` endpoint of the detachment member the surviving valency is two,
so the surviving new occurrence there is consecutive with the retained `t₂`
occurrence through the same sheet and they name one stable row.  Nothing here
asserts that the two rows so obtained (one per endpoint block) are distinct;
a stable loop through the `t₃` branch vertex may identify them, and every
statement below is an identity of occurrences, not of row labels.
-/

/-- **Figure 34's row identity for a detaching member**: the new occurrence
through a sheet of `A₀ ∖ {x}` shares the stable row of the retained `t₂`
occurrence through that sheet. -/
theorem detach_new_stablePath_eq (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile) sheet)
    (hNe : sheet ≠ pinSheet profile) :
    NonDanglingEdge.stablePath
        ⟨(detach.candidate shape).newSourceEdge sheet,
          detach_new_survives input shape detach sheet hWall hNe⟩ =
      NonDanglingEdge.stablePath
        ⟨(detach.candidate shape).oldSourceEdge
            (data.sourceEdge (star.edge profile.doubleLabel) sheet),
          ResolutionSurvival.not_isDangling_oldSourceEdge (detach.candidate shape)
            input.valid.1 _ (double_sourceEdge_survives_shape shape sheet
              ((pinSheet_rel profile).trans hWall))⟩ := by
  refine stablePath_eq_of_consecutive ⟨?_, _, newSourceEdge_incident_old _,
    detach_double_incident shape detach sheet,
    detach_nonDanglingValency_old input shape detach sheet hWall hNe⟩
  intro hEqual
  exact oldSourceEdge_ne_newSourceEdge _ _
    (congrArg (fun edge : NonDanglingEdge (detach.candidate shape).datum ↦ edge.1) hEqual).symm

end Detach

/-! ## The joined member's endpoint census

`M⁽³⁾` is `joinedCandidate`, Base II.1.M: both endpoints and the new edge keep
the whole wall partition.  Each new endpoint over `A₀` therefore carries one
new occurrence and the two old occurrences of its own direction, and the
argument is literally M11's (`M11JoinedSurvival`), with `e₄` at the `t₃`
endpoint doing the work.
-/

section Joined

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

theorem joined_right (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished : Fin degree) (edge : target.edges) :
    (joinedCandidate profile distinguished).right edge =
      (orientedStar profile).right edge := rfl

theorem joined_right_double (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished : Fin degree) :
    (joinedCandidate profile distinguished).right (star.edge profile.doubleLabel) = false := by
  rw [joined_right, ← orientedStar_edge_zero profile]
  exact TwoStar.right_edge_zero _

theorem joined_right_single (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished : Fin degree) :
    (joinedCandidate profile distinguished).right (star.edge profile.singleLabel) = true := by
  rw [joined_right, ← orientedStar_edge_one profile]
  exact TwoStar.right_edge_one _

theorem joined_resolution (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished anchor : Fin degree) :
    (joinedCandidate profile distinguished).resolution anchor =
      thirdResolution (data.vertexPartition wall) := by
  change LocalResolution.onBlock (data.vertexPartition wall) distinguished
    (thirdResolution (data.vertexPartition wall))
    (fun _ ↦ joinedResolutionAt (data.vertexPartition wall)) anchor = _
  simp only [LocalResolution.onBlock, ite_self]

theorem joined_pasted_left (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished : Fin degree) :
    (pasted (joinedCandidate profile distinguished)).left = data.vertexPartition wall := by
  apply SheetPartition.ext_repr
  funext sheet
  change ((joinedCandidate profile distinguished).resolution
    ((data.vertexPartition wall).repr sheet)).left.repr sheet = _
  rw [joined_resolution]
  rfl

theorem joined_pasted_right (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished : Fin degree) :
    (pasted (joinedCandidate profile distinguished)).right = data.vertexPartition wall := by
  apply SheetPartition.ext_repr
  funext sheet
  change ((joinedCandidate profile distinguished).resolution
    ((data.vertexPartition wall).repr sheet)).right.repr sheet = _
  rw [joined_resolution]
  rfl

theorem joined_pasted_newEdge (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished : Fin degree) :
    (pasted (joinedCandidate profile distinguished)).newEdge = data.vertexPartition wall := by
  apply SheetPartition.ext_repr
  funext sheet
  change ((joinedCandidate profile distinguished).resolution
    ((data.vertexPartition wall).repr sheet)).newEdge.repr sheet = _
  rw [joined_resolution]
  rfl

/-- **Three incidences at the `t₂` endpoint over `A₀`**: `e₁`, `e₂` and the
one new occurrence. -/
theorem joined_card_incident_old (shape : Shape profile) (distinguished sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    Fintype.card (IncidentSourceEdge (joinedCandidate profile distinguished).datum
      ((joinedCandidate profile distinguished).datum.sourceEndpoint
        (oldVertex target wall) sheet)) = 3 := by
  rw [card_incident_oldEndpoint (twoStar := orientedStar profile)
      (joined_right profile distinguished),
    joined_pasted_left, joined_pasted_newEdge, orientedStar_edge_zero,
    SheetPartition.blockCountWithin_self,
    endpointPartition_blockCountWithin shape sheet hSheet]

/-- **Three incidences at the `t₃` endpoint over `A₀`**: `e₃`, the dangling
`e₄` and the one new occurrence. -/
theorem joined_card_incident_fresh (shape : Shape profile) (distinguished sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    Fintype.card (IncidentSourceEdge (joinedCandidate profile distinguished).datum
      ((joinedCandidate profile distinguished).datum.sourceEndpoint
        (freshVertex target) sheet)) = 3 := by
  rw [card_incident_freshEndpoint (twoStar := orientedStar profile)
      (joined_right profile distinguished),
    joined_pasted_right, joined_pasted_newEdge, orientedStar_edge_one,
    SheetPartition.blockCountWithin_self,
    singlePartition_blockCountWithin shape sheet hSheet]

/-- Old occurrences of the `t₂` direction reach the joined member's retained
endpoint over their own sheet. -/
theorem joined_double_incident (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished : Fin degree) (edge : data.SourceEdge)
    (hTarget : edge.1.1 = star.edge profile.doubleLabel) :
    Incident (joinedCandidate profile distinguished).datum
      ((joinedCandidate profile distinguished).oldSourceEdge edge)
      ((joinedCandidate profile distinguished).datum.sourceEndpoint
        (oldVertex target wall) edge.1.2) := by
  have hAt : edge.1.1 ∈ GluingDatum.incidentEdges wall := by
    rw [hTarget]
    exact star.edge_mem_incidentEdges profile.doubleLabel
  have hRight : (joinedCandidate profile distinguished).right edge.1.1 = false := by
    rw [hTarget]
    exact joined_right_double profile distinguished
  have h := oldSourceEdge_incident_old (joinedCandidate profile distinguished)
    edge.1.1 hAt hRight edge.1.2
  rwa [GluingDatum.sourceEdge_self data edge] at h

/-- The same-sheet canonical `t₂` occurrence reaches the joined member's
retained endpoint over that sheet. -/
theorem joined_double_sheet_incident
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished sheet : Fin degree) :
    Incident (joinedCandidate profile distinguished).datum
      ((joinedCandidate profile distinguished).oldSourceEdge
        (data.sourceEdge (star.edge profile.doubleLabel) sheet))
      ((joinedCandidate profile distinguished).datum.sourceEndpoint
        (oldVertex target wall) sheet) :=
  oldSourceEdge_incident_old _ _ (star.edge_mem_incidentEdges profile.doubleLabel)
    (joined_right_double profile distinguished) sheet

/-- Old occurrences of the `t₃` direction reach the joined member's fresh
endpoint over their own sheet. -/
theorem joined_single_incident (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished : Fin degree) (edge : data.SourceEdge)
    (hTarget : edge.1.1 = star.edge profile.singleLabel) :
    Incident (joinedCandidate profile distinguished).datum
      ((joinedCandidate profile distinguished).oldSourceEdge edge)
      ((joinedCandidate profile distinguished).datum.sourceEndpoint
        (freshVertex target) edge.1.2) := by
  have hAt : edge.1.1 ∈ GluingDatum.incidentEdges wall := by
    rw [hTarget]
    exact star.edge_mem_incidentEdges profile.singleLabel
  have hRight : (joinedCandidate profile distinguished).right edge.1.1 = true := by
    rw [hTarget]
    exact joined_right_single profile distinguished
  have h := M11SplitSurvival.oldSourceEdge_incident_fresh
    (joinedCandidate profile distinguished) edge.1.1 hAt hRight edge.1.2
  rwa [GluingDatum.sourceEdge_self data edge] at h

theorem joined_old_vertex_eq (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished first second : Fin degree)
    (hRel : (data.vertexPartition wall).Rel first second) :
    (joinedCandidate profile distinguished).datum.sourceEndpoint (oldVertex target wall) first =
      (joinedCandidate profile distinguished).datum.sourceEndpoint
        (oldVertex target wall) second :=
  sourceEndpoint_old_eq_of_rel _ _ (by rw [joined_pasted_left]; exact hRel)

theorem joined_fresh_vertex_eq (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished first second : Fin degree)
    (hRel : (data.vertexPartition wall).Rel first second) :
    (joinedCandidate profile distinguished).datum.sourceEndpoint (freshVertex target) first =
      (joinedCandidate profile distinguished).datum.sourceEndpoint
        (freshVertex target) second :=
  sourceEndpoint_fresh_eq_of_rel _ _ (by rw [joined_pasted_right]; exact hRel)

theorem joined_deleted_dangling (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block) (distinguished : Fin degree) :
    IsDangling (joinedCandidate profile distinguished).datum
      ((joinedCandidate profile distinguished).oldSourceEdge profile.deleted.edge.1) :=
  (ResolutionPruning.isDangling_oldSourceEdge_iff _ input.valid
    (joined_sourceGenus profile distinguished) _).mpr profile.deleted.dangling

/-- **The joined new occurrence survives**, by the trivalent argument at the
`t₃` endpoint: `e₃` survives there and `e₄` is deleted. -/
theorem joined_new_survives (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    ¬ IsDangling (joinedCandidate profile distinguished).datum
      ((joinedCandidate profile distinguished).newSourceEdge sheet) := by
  have hThirdRel : (data.vertexPartition wall).Rel (thirdSheet profile) sheet :=
    (thirdSheet_rel profile).symm.trans hSheet
  have hPinRel : (data.vertexPartition wall).Rel (pinSheet profile) sheet :=
    (pinSheet_rel profile).symm.trans hSheet
  refine M11SplitSurvival.survives_of_trivalent_of_deleted _
    (joined_valid input profile distinguished).1 _
    ⟨_, joined_fresh_vertex_eq profile distinguished (thirdSheet profile) sheet hThirdRel ▸
      joined_single_incident profile distinguished profile.third.1 profile.third_target⟩
    ⟨_, joined_fresh_vertex_eq profile distinguished (pinSheet profile) sheet hPinRel ▸
      joined_single_incident profile distinguished profile.deleted.edge.1 shape.deleted_single⟩
    ⟨_, newSourceEdge_incident_fresh _⟩
    (ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ profile.third_survives)
    (joined_deleted_dangling input profile distinguished) ?_
    (joined_card_incident_fresh shape distinguished sheet hSheet)
  intro hEqual
  exact oldSourceEdge_ne_newSourceEdge _ _
    (congrArg (fun item : IncidentSourceEdge (joinedCandidate profile distinguished).datum
      ((joinedCandidate profile distinguished).datum.sourceEndpoint
        (freshVertex target) sheet) ↦ item.1) hEqual)

/-- **The surviving star at the joined `t₃` endpoint**: the retained `e₃` and
the new occurrence.  `e₄` is pruned. -/
theorem joined_nonDanglingIncident_fresh (input : W2SourceInput data star)
    (shape : Shape profile) (distinguished sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    nonDanglingIncident (joinedCandidate profile distinguished).datum
        ((joinedCandidate profile distinguished).datum.sourceEndpoint
          (freshVertex target) sheet) =
      {(joinedCandidate profile distinguished).oldSourceEdge profile.third.1,
        (joinedCandidate profile distinguished).newSourceEdge sheet} := by
  have hThirdRel : (data.vertexPartition wall).Rel (thirdSheet profile) sheet :=
    (thirdSheet_rel profile).symm.trans hSheet
  have hPinRel : (data.vertexPartition wall).Rel (pinSheet profile) sheet :=
    (pinSheet_rel profile).symm.trans hSheet
  refine nonDanglingIncident_pair_of_card_three _
    (joined_fresh_vertex_eq profile distinguished (thirdSheet profile) sheet hThirdRel ▸
      joined_single_incident profile distinguished profile.third.1 profile.third_target)
    (newSourceEdge_incident_fresh _)
    (joined_fresh_vertex_eq profile distinguished (pinSheet profile) sheet hPinRel ▸
      joined_single_incident profile distinguished profile.deleted.edge.1 shape.deleted_single)
    (oldSourceEdge_ne_newSourceEdge _ _)
    (fun hEqual ↦ singlePartition_separate shape ?_)
    (Ne.symm (oldSourceEdge_ne_newSourceEdge _ _))
    (ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ profile.third_survives)
    (joined_new_survives input shape distinguished sheet hSheet)
    (joined_deleted_dangling input profile distinguished)
    (joined_card_incident_fresh shape distinguished sheet hSheet)
  have hEdges := ResolutionCut.oldSourceEdge_injective _ hEqual
  have hSheets := congrArg (fun edge : data.SourceEdge ↦ edge.1.2) hEdges
  change thirdSheet profile = pinSheet profile at hSheets
  rw [SheetPartition.rel_iff, singlePartition_repr_third, singlePartition_repr_pin shape, hSheets]

theorem joined_nonDanglingValency_fresh (input : W2SourceInput data star)
    (shape : Shape profile) (distinguished sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    nonDanglingValency (joinedCandidate profile distinguished).datum
      ((joinedCandidate profile distinguished).datum.sourceEndpoint
        (freshVertex target) sheet) = 2 := by
  rw [← card_nonDanglingIncident,
    joined_nonDanglingIncident_fresh input shape distinguished sheet hSheet,
    Finset.card_pair (oldSourceEdge_ne_newSourceEdge _ _)]

/-- **The joined `t₂` endpoint over `A₀` is a branch vertex**: `e₁`, `e₂` and
the new occurrence all survive. -/
theorem joined_nonDanglingIncident_old (input : W2SourceInput data star)
    (shape : Shape profile) (distinguished sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    nonDanglingIncident (joinedCandidate profile distinguished).datum
        ((joinedCandidate profile distinguished).datum.sourceEndpoint
          (oldVertex target wall) sheet) =
      {(joinedCandidate profile distinguished).oldSourceEdge profile.first.1,
        (joinedCandidate profile distinguished).oldSourceEdge profile.second.1,
        (joinedCandidate profile distinguished).newSourceEdge sheet} := by
  have hFirstRel : (data.vertexPartition wall).Rel (firstSheet profile) sheet :=
    (firstSheet_rel profile).symm.trans hSheet
  have hSecondRel : (data.vertexPartition wall).Rel (secondSheet profile) sheet :=
    (secondSheet_rel profile).symm.trans hSheet
  refine nonDanglingIncident_triple_of_card_three _
    (joined_old_vertex_eq profile distinguished (firstSheet profile) sheet hFirstRel ▸
      joined_double_incident profile distinguished profile.first.1 profile.first_target)
    (joined_old_vertex_eq profile distinguished (secondSheet profile) sheet hSecondRel ▸
      joined_double_incident profile distinguished profile.second.1 profile.second_target)
    (newSourceEdge_incident_old _)
    (fun hEqual ↦ profile.first_ne_second (Subtype.ext (ResolutionCut.oldSourceEdge_injective _ hEqual)))
    (oldSourceEdge_ne_newSourceEdge _ _) (oldSourceEdge_ne_newSourceEdge _ _)
    (ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ profile.first_survives)
    (ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ profile.second_survives)
    (joined_new_survives input shape distinguished sheet hSheet)
    (joined_card_incident_old shape distinguished sheet hSheet)

theorem joined_nonDanglingValency_old (input : W2SourceInput data star)
    (shape : Shape profile) (distinguished sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    nonDanglingValency (joinedCandidate profile distinguished).datum
      ((joinedCandidate profile distinguished).datum.sourceEndpoint
        (oldVertex target wall) sheet) = 3 := by
  classical
  rw [← card_nonDanglingIncident,
    joined_nonDanglingIncident_old input shape distinguished sheet hSheet,
    Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (hEq | hEq)
      · exact profile.first_ne_second (Subtype.ext (ResolutionCut.oldSourceEdge_injective _ hEq))
      · exact oldSourceEdge_ne_newSourceEdge _ _ hEq),
    Finset.card_pair (oldSourceEdge_ne_newSourceEdge _ _)]

/-- **Figure 34's row identity for `M⁽³⁾`**: the single new occurrence shares
the stable row of the retained `e₃`, exactly as in Figure 32. -/
theorem joined_new_stablePath_eq_third (input : W2SourceInput data star)
    (shape : Shape profile) (distinguished sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    NonDanglingEdge.stablePath
        ⟨(joinedCandidate profile distinguished).newSourceEdge sheet,
          joined_new_survives input shape distinguished sheet hSheet⟩ =
      NonDanglingEdge.stablePath
        ⟨(joinedCandidate profile distinguished).oldSourceEdge profile.third.1,
          ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
            profile.third_survives⟩ := by
  have hThirdRel : (data.vertexPartition wall).Rel (thirdSheet profile) sheet :=
    (thirdSheet_rel profile).symm.trans hSheet
  refine stablePath_eq_of_consecutive ⟨?_, _, newSourceEdge_incident_fresh _,
    joined_fresh_vertex_eq profile distinguished (thirdSheet profile) sheet hThirdRel ▸
      joined_single_incident profile distinguished profile.third.1 profile.third_target,
    joined_nonDanglingValency_fresh input shape distinguished sheet hSheet⟩
  intro hEqual
  exact oldSourceEdge_ne_newSourceEdge _ _
    (congrArg (fun edge : NonDanglingEdge (joinedCandidate profile distinguished).datum ↦
      edge.1) hEqual).symm

end Joined

/-! ## The background census

Away from `A₀` both members install `M11SourceCandidates.joinedBackground`'s
own star, `ResolutionM11.joinedResolutionAt`, which retains the whole wall
block at both endpoints and along the new edge.  Every other wall block has
local ramification zero (`W2RankObstructions.other_localRamification_eq_zero`
applied to `profile.ramification`), so each direction contributes exactly one
occurrence there and each background new endpoint is divalent: the new
occurrence is a *subdivision* of the old block, dangling exactly when the old
occurrence in that direction dangles, and sharing its stable row when it
survives.  These background occurrences are **not** the detaching member's
deleted arm; that one lives over `A₀`.
-/

section Background

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- Every wall block other than `A₀` has vanishing local ramification.  Local
copy of `M11JoinedBackground.background_ramification_zero`. -/
theorem background_ramification_zero_local (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel block.1 sheet) :
    data.localRamification wall ((data.vertexPartition wall).toBlock sheet) = 0 := by
  apply W2RankObstructions.other_localRamification_eq_zero input block profile.ramification
  intro hEqual
  exact hBackground (block.2.trans (congrArg Subtype.val hEqual).symm)

/-- Hence exactly one occurrence per direction there.  Local copy of
`M11JoinedBackground.background_blockCount`. -/
theorem background_blockCount_local (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block) (label : Fin 2)
    (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel block.1 sheet) :
    (data.edgePartition (star.edge label)).blockCountWithin
      (data.vertexPartition wall) sheet = 1 :=
  blockCountWithin_eq_one_of_divalent_localRamification_zero data wall
    star.card_incidentEdges sheet
    (background_ramification_zero_local input profile sheet hBackground) _
    (star.edge_mem_incidentEdges label)

/-! ### The detachment member off `A₀` -/

theorem detach_background_resolution (shape : Shape profile) (detach : DetachData profile)
    (anchor : Fin degree)
    (hAnchor : ¬(data.vertexPartition wall).Rel (pinSheet profile) anchor) :
    (detach.candidate shape).resolution anchor =
      joinedResolutionAt (data.vertexPartition wall) := by
  change LocalResolution.onBlock (data.vertexPartition wall) (pinSheet profile)
    detach.selected (fun _ ↦ joinedResolutionAt (data.vertexPartition wall)) anchor = _
  rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hAnchor]

theorem detach_background_repr (profile : W2R2SourceProfile.SourceProfile data star block)
    (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel block.1 sheet) :
    ¬(data.vertexPartition wall).Rel (pinSheet profile)
      ((data.vertexPartition wall).repr sheet) := by
  intro hRel
  exact hBackground
    (((pinSheet_rel profile).trans hRel).trans
      ((data.vertexPartition wall).rel_repr_left sheet))

/-- **Both background new endpoints of the detachment member are divalent.** -/
theorem detach_card_incident_background (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel block.1 sheet) :
    Fintype.card (IncidentSourceEdge (detach.candidate shape).datum
        ((detach.candidate shape).datum.sourceEndpoint (oldVertex target wall) sheet)) = 2 ∧
      Fintype.card (IncidentSourceEdge (detach.candidate shape).datum
        ((detach.candidate shape).datum.sourceEndpoint (freshVertex target) sheet)) = 2 := by
  have hRes := detach_background_resolution shape detach _
    (detach_background_repr profile sheet hBackground)
  constructor
  · rw [card_incident_oldEndpoint (twoStar := orientedStar profile)
        (detach_right shape detach),
      LocalResolution.paste_newEdge_blockCountWithin_left, hRes,
      LocalResolution.blockCountWithin_paste_left, hRes, orientedStar_edge_zero]
    simp only [joinedResolutionAt, SheetPartition.blockCountWithin_self,
      background_blockCount_local input profile profile.doubleLabel sheet hBackground]
  · rw [card_incident_freshEndpoint (twoStar := orientedStar profile)
        (detach_right shape detach),
      LocalResolution.paste_newEdge_blockCountWithin_right, hRes,
      LocalResolution.blockCountWithin_paste_right, hRes, orientedStar_edge_one]
    simp only [joinedResolutionAt, SheetPartition.blockCountWithin_self,
      background_blockCount_local input profile profile.singleLabel sheet hBackground]

/-- **A background new occurrence of the detachment member is a subdivision**:
it dangles exactly when the same-sheet old `t₂` occurrence does. -/
theorem detach_background_survives_iff (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel block.1 sheet) :
    (¬ IsDangling (detach.candidate shape).datum
        ((detach.candidate shape).newSourceEdge sheet)) ↔
      ¬ IsDangling data (data.sourceEdge (star.edge profile.doubleLabel) sheet) :=
  (survives_iff_of_card_two (detach.candidate shape).datum
    (detach_valid input shape detach).1 _
    ((detach.candidate shape).newSourceEdge sheet) _
    (newSourceEdge_incident_old _) (detach_double_incident shape detach sheet)
    (detach_card_incident_background input shape detach sheet hBackground).1).trans
    (not_congr (ResolutionPruning.isDangling_oldSourceEdge_iff _ input.valid
      (detach_sourceGenus shape detach) _))

/-- A surviving background new occurrence of the detachment member shares the
stable row of the same-sheet old `t₂` occurrence. -/
theorem detach_background_stablePath_eq (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel block.1 sheet)
    (hOld : ¬ IsDangling data (data.sourceEdge (star.edge profile.doubleLabel) sheet)) :
    NonDanglingEdge.stablePath
        ⟨(detach.candidate shape).newSourceEdge sheet,
          (detach_background_survives_iff input shape detach sheet hBackground).mpr hOld⟩ =
      NonDanglingEdge.stablePath
        ⟨(detach.candidate shape).oldSourceEdge
            (data.sourceEdge (star.edge profile.doubleLabel) sheet),
          ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ hOld⟩ := by
  refine stablePath_eq_of_consecutive ⟨?_, _, newSourceEdge_incident_old _,
    detach_double_incident shape detach sheet, ?_⟩
  · intro hEqual
    exact oldSourceEdge_ne_newSourceEdge _ _
      (congrArg (fun edge : NonDanglingEdge (detach.candidate shape).datum ↦ edge.1)
        hEqual).symm
  · exact nonDanglingValency_eq_two_of_card_two_of_survives _
      (detach_valid input shape detach).1 _ _ (newSourceEdge_incident_old _)
      ((detach_background_survives_iff input shape detach sheet hBackground).mpr hOld)
      (detach_card_incident_background input shape detach sheet hBackground).1

/-! ### The joined member off `A₀` -/

/-- **Both background new endpoints of `M⁽³⁾` are divalent.** -/
theorem joined_card_incident_background (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel block.1 sheet) :
    Fintype.card (IncidentSourceEdge (joinedCandidate profile distinguished).datum
        ((joinedCandidate profile distinguished).datum.sourceEndpoint
          (oldVertex target wall) sheet)) = 2 ∧
      Fintype.card (IncidentSourceEdge (joinedCandidate profile distinguished).datum
        ((joinedCandidate profile distinguished).datum.sourceEndpoint
          (freshVertex target) sheet)) = 2 := by
  constructor
  · rw [card_incident_oldEndpoint (twoStar := orientedStar profile)
        (joined_right profile distinguished),
      joined_pasted_left, joined_pasted_newEdge, orientedStar_edge_zero,
      SheetPartition.blockCountWithin_self,
      background_blockCount_local input profile profile.doubleLabel sheet hBackground]
  · rw [card_incident_freshEndpoint (twoStar := orientedStar profile)
        (joined_right profile distinguished),
      joined_pasted_right, joined_pasted_newEdge, orientedStar_edge_one,
      SheetPartition.blockCountWithin_self,
      background_blockCount_local input profile profile.singleLabel sheet hBackground]

/-- **A background new occurrence of `M⁽³⁾` is a subdivision.** -/
theorem joined_background_survives_iff (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel block.1 sheet) :
    (¬ IsDangling (joinedCandidate profile distinguished).datum
        ((joinedCandidate profile distinguished).newSourceEdge sheet)) ↔
      ¬ IsDangling data (data.sourceEdge (star.edge profile.doubleLabel) sheet) :=
  (survives_iff_of_card_two (joinedCandidate profile distinguished).datum
    (joined_valid input profile distinguished).1 _
    ((joinedCandidate profile distinguished).newSourceEdge sheet) _
    (newSourceEdge_incident_old _)
    (joined_double_sheet_incident profile distinguished sheet)
    (joined_card_incident_background input profile distinguished sheet hBackground).1).trans
    (not_congr (ResolutionPruning.isDangling_oldSourceEdge_iff _ input.valid
      (joined_sourceGenus profile distinguished) _))

/-- A surviving background new occurrence of `M⁽³⁾` shares the stable row of
the same-sheet old `t₂` occurrence. -/
theorem joined_background_stablePath_eq (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel block.1 sheet)
    (hOld : ¬ IsDangling data (data.sourceEdge (star.edge profile.doubleLabel) sheet)) :
    NonDanglingEdge.stablePath
        ⟨(joinedCandidate profile distinguished).newSourceEdge sheet,
          (joined_background_survives_iff input profile distinguished sheet
            hBackground).mpr hOld⟩ =
      NonDanglingEdge.stablePath
        ⟨(joinedCandidate profile distinguished).oldSourceEdge
            (data.sourceEdge (star.edge profile.doubleLabel) sheet),
          ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ hOld⟩ := by
  refine stablePath_eq_of_consecutive ⟨?_, _, newSourceEdge_incident_old _,
    joined_double_sheet_incident profile distinguished sheet, ?_⟩
  · intro hEqual
    exact oldSourceEdge_ne_newSourceEdge _ _
      (congrArg (fun edge : NonDanglingEdge (joinedCandidate profile distinguished).datum ↦
        edge.1) hEqual).symm
  · exact nonDanglingValency_eq_two_of_card_two_of_survives _
      (joined_valid input profile distinguished).1 _ _ (newSourceEdge_incident_old _)
      ((joined_background_survives_iff input profile distinguished sheet hBackground).mpr hOld)
      (joined_card_incident_background input profile distinguished sheet hBackground).1

end Background

end DraismaVargas.LocalCases.W2MkkStableGraph