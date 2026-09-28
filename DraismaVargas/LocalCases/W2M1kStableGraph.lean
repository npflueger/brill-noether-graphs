import DraismaVargas.LocalCases.W2M1kLeaves
import DraismaVargas.LocalCases.LimitChainCore

/-!
# Survival and the endpoint census for Figure 33's three members

Source: Draisma--Vargas Part I, case `{w2-r2-nd3-M-1k}`, Figure 33 and
Equation (7).  The Base I/II vocabulary is fixed once in case `{w2-r2}`, and
Cardinality M in `{w2-r2-nd3}`.

`W2M1kSourceCandidates` builds the three members and proves them valid, genus
preserving, with Figure 33's target valencies -- `(1, 3)` for `M⁽¹⁾` and
`(2, 2)` for the other two.  This module is the first step from that geometry
towards Equation (7): **which occurrences of each member survive pruning, what
the complete surviving star at each new endpoint is, and which stable row each
surviving new occurrence joins.**  The lift, the row descent, the limit
matrices and Equation (7) itself are in later modules (`W2M1kStableLift`,
`W2M1kRowDescent`, `W2M1kLimitMatrix`, `W2M1kCommonBalance`).

The template is `W2MkkStableGraph` (Figure 34), which is the M11 chain's
(`M11JoinedSurvival`, `M11SplitSurvival`) rather than the W3 chain's: M-1k sits
at the same divalent `w2` wall.  Two things are new here and have no analogue
in Figure 34.

* **A target leaf.**  `M⁽¹⁾` is Base I.a, so its retained endpoint carries no
  wall direction at all and a monovalent source vertex over it prunes its one
  arm outright.  `W2M1kLeaves` is that layer, the M-1k `M11SplitLeaves`;
  `§8`--`§9` below are the survival and the stars on top of it.  The effect is
  that `k - 1` of the member's `k + 1` new occurrences over `A₀` are pruned,
  and **all** of its background ones are.
* **An endpoint of unbounded valency.**  `M⁽¹⁾`'s trivalent endpoint over
  `A₀ ∖ {x}` carries `k + 2` occurrences -- `e₂`, `e₃` and `k` new ones -- so
  its surviving star is read by an explicit classification of incidences
  (`ResolutionPruning.sourceEdge_cases` plus the profile's `exhaustive`), not
  by one of `LimitChainCore` §1's four `(card, surviving)` readers.  Its
  surviving valency is nevertheless three: it is `M⁽¹⁾`'s branch vertex.

## Which side is which

M-kk's members are built over `W2MkkSourceCandidates.orientedStar`, whose
label `0` is the profile's `doubleLabel` by construction.  M-1k's are built
over the raw `star`, so **nothing in `W2M1kSourceCandidates`' bundle says
whether `star.edge 0` is `t₂` or `t₃`**.  Rather than prove each divalent
statement twice, `§2` indexes the two new endpoints by a `side : Bool` -- the
`LimitChainCore.wallSide` convention, `false` retained and `true` fresh -- and
gives the direction it carries the name `star.edge (sideLabel side)`.  Every
count and every incidence is then proved once, and the census names its two
endpoints by the profile's own labels, `sideOf profile.doubleLabel` and
`sideOf profile.singleLabel`.  `§1` is what makes that possible: on an M-1k
block **each** wall direction carries exactly two incident occurrences, a
`pinnedOccurrence` of index one whose block is a singleton and a
`bulkOccurrence` of index `k` covering the rest, and which of `e₁, e₂, e₃, e₄`
plays which role is the only thing the label decides.

## Does the census transport across the branch swap?

`M⁽²⁾` of `W2M1kSwapped.SwappedBundle.candidates` lives over
`W2M1kSwapped.swappedData`, i.e. over
`GlobalM11Arbitrary.SwappedDatum data wall (M11RemoteCandidates.branchRoot star 1) _
geometry.first geometry.second _`.  `W2MkkStableGraph`'s three-part answer
applies verbatim, and the third part is again the operative one.

* **Not along `W3FourStableGraph.WallTransport`.**  A `WallTransport` preserves
  exactly the target occurrence an occurrence lies above and its dilation
  index, which is all a *length matrix* reads.  `IsDangling`,
  `nonDanglingIncident`, `nonDanglingValency` and `Consecutive` are none of
  them functions of that pair, so `WallTransport.ofSheetRelabeling` does not
  carry the census and nothing below is routed through it.
* **Along the actual gauge, yes.**  `ResolutionM11.wallBranchSwap` is a genuine
  `GluingDatum.SheetRelabeling`, and along one of those the whole census
  transports -- `SheetRelabelPruning.isDangling_sourceEdgeEquiv_iff`,
  `SheetRelabelStable.nonDanglingIncident_map`, `nonDanglingValency_map`,
  `consecutive_map_iff`, `stablePathEquiv` -- at the cost of `data.Connected`
  and nothing else.
* **But there is nothing to transport.**  `W2M1kSourceCandidates`' obstruction
  (`no_common_geometry`, `not_leafPair_and_dividedData`) and
  `W2M1kSwapped.no_common_patterns` say a given datum carries `M⁽¹⁾` or
  `M⁽²⁾` and never both -- `M⁽¹⁾` forces `p₀ = p₁` and `M⁽²⁾` forces
  `p₀ ≠ p₁` -- so there is no member-2 candidate *over the original datum*
  whose census could be pushed forward.

Consequently the census here is **not transported at all**: `§3`--`§6` are
proved once, uniformly in `data`, `star`, `block`, `profile`, `shape` and
`divided : DividedData profile`, and the swapped member 2 obtains them by
instantiating the *same* theorems at `W2M1kSwapped.swappedData` with a
transported `W2SourceInput`, `SourceProfile`, `Shape` and `DividedData`.  The
first three transports are general -- `W2SourceTransport`'s
`input_relabel`, `sourceProfile_relabel` and `shape_relabel` are stated for an
arbitrary `GluingDatum.SheetRelabeling`, and the last already lands in the
M-1k `Shape` -- and the fourth is free: `W2M1kSwapped.AlignedProfile.swapped_pins_ne`
gives the two block-singleton facts over the swapped datum, which
`W2M1kSourceCandidates.eq_pinSheet_of_block_singleton` turns into
`pinSheet 0 = geometry.first` and `pinSheet 1 = geometry.second` for the
transported profile, so `DividedData.pins_ne` is `geometry.first_ne_second`
-- derived rather than assumed.  Per swapped copy the census costs nothing.
No hypothesis is added anywhere below.

## What the census is

Write `t₂` for `profile.doubleLabel`'s direction (survivors `e₁` of index `1`
and `e₂` of index `k`), `t₃` for `profile.singleLabel`'s (the survivor `e₃` of
index `k` and the dangling `e₄` of index one), `p := pinSheet profile
profile.doubleLabel` for `e₁`'s sheet and `q := pinSheet profile
profile.singleLabel` for `e₄`'s.  `|A₀| = k + 1` and `k ≥ 2`.

For `M⁽¹⁾` (`LeafPair.candidate`, Base I.a; here `p = q =: x` and `pair.second`
is the partner at the new leaf):

| new source vertex | incidences | surviving | `nd` |
|---|---|---|---|
| leaf over `{x, pair.second}` | new(`x`), new(`pair.second`) | 2 | 2 |
| leaf over `{s}`, `s ∈ A₀ ∖ {x, pair.second}` | new(`s`) | 0 | 0 |
| leaf over a background sheet | new(that sheet) | 0 | 0 |
| `v` over `{x}` | `e₁`, `e₄`, new(`x`) | 2 | 2 |
| `v` over `A₀ ∖ {x}` | `e₂`, `e₃`, `k` new | 3 | 3 |

For `M⁽²⁾` (`DividedData.candidate`, Base II.2.2.M; `p ≠ q`, and `divided.third`
names the residual `k - 1` class):

| new source vertex | incidences | surviving | `nd` |
|---|---|---|---|
| `t₂` side over `{p}` | `e₁`, new(`p`) | 2 | 2 |
| `t₂` side over `A₀ ∖ {p}` | `e₂`, new(`q`), new(residual) | 2 | 2 |
| `t₃` side over `{q}` | `e₄`, new(`q`) | 0 | 0 |
| `t₃` side over `A₀ ∖ {q}` | `e₃`, new(`p`), new(residual) | 3 | 3 |

For `M⁽³⁾` (`joinedCandidate`, Base II.1.M):

| new source vertex | incidences | surviving | `nd` |
|---|---|---|---|
| `t₂` side over `A₀` | `e₁`, `e₂`, new | 3 | 3 |
| `t₃` side over `A₀` | `e₃`, `e₄`, new | 2 | 2 |

The **branch vertex** is therefore: for `M⁽¹⁾` the fresh endpoint over
`A₀ ∖ {x}`; for `M⁽²⁾` the `t₃`-side endpoint over `A₀ ∖ {q}`; for `M⁽³⁾` the
`t₂`-side endpoint over `A₀`.

Two substantive new items, beyond the target leaf:

* `divided_new_deleted_dangling` -- **the new occurrence through `e₄`'s sheet
  dies with `e₄`**, because its `t₃`-side endpoint is the divalent source
  vertex `{q}` whose only other incidence is the pruned `e₄`.  This is the M-1k
  form of `W2MkkStableGraph.detach_new_pin_dangling`, and it is what makes the
  `t₃`-side endpoint over `A₀ ∖ {q}` a branch vertex rather than the carrier of
  a surviving parallel pair.
* `nonDanglingIncident_empty_of_card_one` -- the `(1, 0)` endpoint shape, which
  `LimitChainCore` §1 does not carry: no other divalent-wall member produces
  it.

Every statement is an identity of **occurrence** sets, never of row labels, and
no `Nodup` or pairwise-distinctness hypothesis on rows appears: a stable loop
may put two of the three survivors at a branch vertex into one row and nothing
here excludes it.

## The census against Figure 33's boxes

* `M⁽¹⁾`: `σ¹(J₀,1) = σ¹(J₁,1) = 0` and `c⁽¹⁾ = 2c(e₁)`.  The two surviving new
  occurrences are the singletons `{x}` and `{pair.second}` -- index one, so both
  `σ`'s vanish -- and `leaf_new_pin_stablePath_eq` /
  `leaf_new_second_stablePath_eq` put **both** in `e₁`'s stable row, which is
  the factor two.
* `M⁽²⁾`: `|e'| = 1`, `|e''| = k - 1`, `σ²(J₀,1) = s`,
  `c⁽²⁾ = c(e₁) + c(e₂)/(k-1) + s`.  The two surviving new occurrences are
  `{p}` of index one and the residual class of index `k - 1`
  (`ResolutionM1k.secondNewEdge_blockCard_first` / `_third`), and
  `divided_new_unit_stablePath_eq` / `divided_new_third_stablePath_eq` put them
  in `e₁`'s and `e₂`'s rows respectively.  The third new-edge block `{q}` does
  not appear in the box because it is pruned.
* `M⁽³⁾`: `|e'| = k + 1`, `σ³(J₀,1) = s`, `c⁽³⁾ = c(e₃)/(k+1) + s`.  The one new
  occurrence has index `|A₀| = k + 1`
  (`ResolutionM1k.thirdResolution_newEdge_blockCard`) and
  `joined_new_stablePath_eq_third` puts it in `e₃`'s row.

The source's own Base I.a / II.2.2.M / II.1.M bookkeeping is reproduced too:
`M⁽¹⁾`'s `A_u` of size two with `|e'| = |e''| = 1` and `k₂ = |A'| = k₃`,
`k₁ = |A''| = k₄`; `M⁽²⁾`'s `|A'| = k₁ = 1` in Case (r0-nd2), `|A''| = k₂ = k`
in Case (r1-nd2) with `|e''| = |A''| - 1`, and `B = A^q` of non-dangling
valency three with `k₃ = |e'| + |e''| = 1 + (k-1)`.

## What is *not* done here

This module proves the census `M11JoinedSurvival` / `M11SplitSurvival` prove,
not what `M11JoinedStableGraph` / `M11SplitStableGraph` prove.  No
branch-vertex classification, no flag dictionary and no row bijection appears
below.  Those are in later modules: the stable lift, the row descent and the
limit matrices as instances of `LimitChainCore` (`LiftData`, `SelectedData`),
then the `StableGraphIncidence.Equivalence` via `LimitChainCore.GraphData`,
then the descent, and Equation (7) itself via `BalancingValencyTwo.balance_M_1k`.

What the branch-vertex table above fixes for those modules is the pair
(`selected`, `selectedSide`) of `LimitChainCore.BackgroundShape` /
`GraphData`, since `selectedFlag_star` is stated at
`sourceEndpoint (wallSide target wall selectedSide) selected` and must land on
the member's branch vertex.  Any sheet of `A₀` serves as `selected` for the
background half, so the choice is forced only by which endpoint over that sheet
is the branch vertex:

* `M⁽¹⁾`: `selected` a sheet of `A₀ ∖ {x}` -- `pair.second` is the canonical
  one -- and `selectedSide := true`.  It may **not** be `x`: the fresh endpoint
  over `{x}` is divalent (`leaf_nonDanglingValency_fresh_pin`), and the
  retained endpoint is a target leaf at every sheet.
* `M⁽²⁾`: `selected` a sheet of `A₀ ∖ {q}` -- `divided.third` or
  `pinSheet profile profile.doubleLabel` -- and
  `selectedSide := sideOf profile.singleLabel`.
* `M⁽³⁾`: any sheet of `A₀`, and `selectedSide := sideOf profile.doubleLabel`.

`GraphData.selected_not_branch` is then immediate from the tables: every other
endpoint above `A₀` has surviving valency `0` or `2` in all three members.

## What is general, and where it lives

The endpoint geometry of a candidate retaining one wall direction and the six
readers of a surviving star off a complete incidence list are
`LimitChainCore`'s, opened below.  `nonDanglingIncident_empty_of_card_one` is
general and would sit naturally in `LimitChainCore` §1, beside the other four
readers.  `new_incident_fresh_sheet_rel` is the mirror of
`LimitChainCore.old_incident_fresh_sheet_rel` and belongs beside it in
`LimitChainCore` §0.  `card_incident_side`, `newSourceEdge_incident_side`,
`oldSourceEdge_incident_side` and `sourceEndpoint_side_eq_of_rel` are the
`Bool`-indexed forms of four `LimitChainCore` lemmas and belong in its §2.
Two short lemmas are local copies, with a `_local` suffix, of lemmas of
`M11JoinedBackground`, which this module does not import:
`background_ramification_zero_local` and `background_blockCount_local`; since
neither statement mentions M11, they belong naturally in `W2RankObstructions`,
beside `other_localRamification_eq_zero`.
-/

namespace DraismaVargas.LocalCases.W2M1kStableGraph

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open ResolutionM11 ResolutionM1k GlobalM11Arbitrary
open W2M1kSourceCandidates W2M1kLeaves
open LimitChainCore (pasted wallSide card_incident_oldEndpoint card_incident_freshEndpoint
  sourceEndpoint_old_eq_of_rel sourceEndpoint_fresh_eq_of_rel newSourceEdge_incident_old
  newSourceEdge_incident_fresh oldSourceEdge_ne_newSourceEdge newSourceEdge_eq_iff_rel
  forall_eq_of_card_two forall_eq_of_card_three nonDanglingIncident_pair_of_card_two
  nonDanglingIncident_empty_of_card_two nonDanglingIncident_pair_of_card_three
  nonDanglingIncident_triple_of_card_three oldSourceEdge_incident_old
  survives_iff_of_card_two nonDanglingValency_eq_two_of_card_two_of_survives
  old_incident_fresh_selected_info old_incident_fresh_sheet_rel card_incident_fresh)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## §1  The two wall directions, read uniformly

On an M-1k block each of the two wall directions carries exactly two incident
occurrences: the **pinned** one, of index one, whose occurrence block is the
singleton `{pinSheet profile label}`, and the **bulk** one, of index `k`,
covering the rest of `A₀`.  Which of the four profile occurrences plays which
role depends on the label, and nothing below needs to know: every statement in
this section is proved once for an arbitrary `label : Fin 2`.
-/

section Directions

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- The index-`k` occurrence of one wall direction: `e₂` above `t₂` and `e₃`
above `t₃`.  Together with `pinnedOccurrence` it exhausts the direction. -/
noncomputable def bulkOccurrence (profile : W2R2SourceProfile.SourceProfile data star block)
    (label : Fin 2) : IncidentSourceEdge data (WallBlock.sourceVertex data wall block) :=
  if label = profile.doubleLabel then profile.second else profile.third

theorem bulkOccurrence_double :
    bulkOccurrence profile profile.doubleLabel = profile.second := by
  unfold bulkOccurrence
  exact if_pos rfl

theorem bulkOccurrence_single :
    bulkOccurrence profile profile.singleLabel = profile.third := by
  unfold bulkOccurrence
  exact if_neg profile.labels_ne.symm

theorem bulkOccurrence_target (label : Fin 2) :
    (bulkOccurrence profile label).1.1.1 = star.edge label := by
  rcases Shape.label_cases profile label with rfl | rfl
  · rw [bulkOccurrence_double]; exact profile.second_target
  · rw [bulkOccurrence_single]; exact profile.third_target

theorem bulkOccurrence_survives (label : Fin 2) :
    ¬ IsDangling data (bulkOccurrence profile label).1 := by
  rcases Shape.label_cases profile label with rfl | rfl
  · rw [bulkOccurrence_double]; exact profile.second_survives
  · rw [bulkOccurrence_single]; exact profile.third_survives

theorem bulkOccurrence_index (shape : Shape profile) (label : Fin 2) :
    data.sourceEdgeIndex (bulkOccurrence profile label).1 = shape.k := by
  rcases Shape.label_cases profile label with rfl | rfl
  · rw [bulkOccurrence_double]; exact shape.second_index
  · rw [bulkOccurrence_single]; exact shape.third_index

/-- The sheet of a direction's bulk occurrence. -/
noncomputable def bulkSheet (profile : W2R2SourceProfile.SourceProfile data star block)
    (label : Fin 2) : Fin degree := (bulkOccurrence profile label).1.1.2

theorem bulkSheet_rel (label : Fin 2) :
    (data.vertexPartition wall).Rel block.1 (bulkSheet profile label) :=
  M11SplitSurvival.sheet_rel_of_incident_block (bulkOccurrence profile label)

theorem edgePartition_repr_bulk (label : Fin 2) :
    (data.edgePartition (star.edge label)).repr (bulkSheet profile label) =
      bulkSheet profile label := by
  have h := (bulkOccurrence profile label).1.2
  rw [bulkOccurrence_target label] at h
  exact h

theorem edgePartition_repr_pin (shape : Shape profile) (label : Fin 2) :
    (data.edgePartition (star.edge label)).repr (pinSheet profile label) =
      pinSheet profile label := by
  have h := (pinnedOccurrence profile label).1.2
  rw [pinnedOccurrence_target shape label] at h
  exact h

/-- The bulk occurrence of a direction has index `k ≥ 2`, the pinned one index
one, so they are different blocks. -/
theorem bulkSheet_ne_pinSheet (shape : Shape profile) (label : Fin 2) :
    bulkSheet profile label ≠ pinSheet profile label := by
  intro hEq
  have hCard : (data.edgePartition (star.edge label)).blockCard (bulkSheet profile label) =
      (data.edgePartition (star.edge label)).blockCard (pinSheet profile label) := by
    rw [hEq]
  rw [pinSheet_blockCard shape label] at hCard
  have hIndex : data.sourceEdgeIndex (bulkOccurrence profile label).1 =
      (data.edgePartition (star.edge label)).blockCard (bulkSheet profile label) := by
    show (data.edgePartition (bulkOccurrence profile label).1.1.1).blockCard
      (bulkSheet profile label) = _
    rw [bulkOccurrence_target label]
  rw [bulkOccurrence_index shape label] at hIndex
  have := shape.one_lt_k
  omega

theorem edgePartition_separate (shape : Shape profile) (label : Fin 2) :
    ¬(data.edgePartition (star.edge label)).Rel (bulkSheet profile label)
      (pinSheet profile label) := by
  intro hRel
  refine bulkSheet_ne_pinSheet shape label ?_
  have hMem : bulkSheet profile label ∈
      (data.edgePartition (star.edge label)).block (pinSheet profile label) :=
    ((data.edgePartition (star.edge label)).mem_block_iff _ _).mpr hRel.symm
  rw [pinSheet_block shape label] at hMem
  simpa using hMem

/-- **The pinned and bulk occurrences of one direction tile `A₀`.**  Every
sheet of the distinguished block lies in one of the two. -/
theorem edgePartition_covers (shape : Shape profile) (label : Fin 2) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    (data.edgePartition (star.edge label)).Rel (bulkSheet profile label) sheet ∨
      (data.edgePartition (star.edge label)).Rel (pinSheet profile label) sheet := by
  have hIncident : Incident data (data.sourceEdge (star.edge label) sheet)
      (WallBlock.sourceVertex data wall block) := by
    apply (incident_wallBlock_sourceVertex_iff data block _).mpr
    refine ⟨star.edge_mem_incidentEdges label, ?_⟩
    apply (WallBlock.ofSheet_eq_iff_rel data wall block _).mpr
    exact hSheet.trans ((star.edgePartition_refines_wall data label).rel
      ((data.edgePartition (star.edge label)).rel_repr_right sheet))
  rcases profile.exhaustive ⟨_, hIncident⟩ with hEq | hEq | hEq | hEq
  · have hLabel : label = profile.doubleLabel := star.edge_injective
      ((congrArg (fun edge : IncidentSourceEdge data
        (WallBlock.sourceVertex data wall block) ↦ edge.1.1.1) hEq).trans profile.first_target)
    subst hLabel
    right
    have hRepr := congrArg (fun edge : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall block) ↦ edge.1.1.2) hEq
    change (data.edgePartition (star.edge profile.doubleLabel)).repr sheet =
      profile.first.1.1.2 at hRepr
    have hPin : pinSheet profile profile.doubleLabel = profile.first.1.1.2 :=
      congrArg (fun edge : IncidentSourceEdge data
        (WallBlock.sourceVertex data wall block) ↦ edge.1.1.2) pinnedOccurrence_double
    rw [SheetPartition.rel_iff, edgePartition_repr_pin shape, hRepr, hPin]
  · have hLabel : label = profile.doubleLabel := star.edge_injective
      ((congrArg (fun edge : IncidentSourceEdge data
        (WallBlock.sourceVertex data wall block) ↦ edge.1.1.1) hEq).trans profile.second_target)
    subst hLabel
    left
    have hRepr := congrArg (fun edge : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall block) ↦ edge.1.1.2) hEq
    change (data.edgePartition (star.edge profile.doubleLabel)).repr sheet =
      profile.second.1.1.2 at hRepr
    have hBulk : bulkSheet profile profile.doubleLabel = profile.second.1.1.2 :=
      congrArg (fun edge : IncidentSourceEdge data
        (WallBlock.sourceVertex data wall block) ↦ edge.1.1.2) bulkOccurrence_double
    rw [SheetPartition.rel_iff, edgePartition_repr_bulk, hRepr, hBulk]
  · have hLabel : label = profile.singleLabel := star.edge_injective
      ((congrArg (fun edge : IncidentSourceEdge data
        (WallBlock.sourceVertex data wall block) ↦ edge.1.1.1) hEq).trans profile.third_target)
    subst hLabel
    left
    have hRepr := congrArg (fun edge : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall block) ↦ edge.1.1.2) hEq
    change (data.edgePartition (star.edge profile.singleLabel)).repr sheet =
      profile.third.1.1.2 at hRepr
    have hBulk : bulkSheet profile profile.singleLabel = profile.third.1.1.2 :=
      congrArg (fun edge : IncidentSourceEdge data
        (WallBlock.sourceVertex data wall block) ↦ edge.1.1.2) bulkOccurrence_single
    rw [SheetPartition.rel_iff, edgePartition_repr_bulk, hRepr, hBulk]
  · have hLabel : label = profile.singleLabel := star.edge_injective
      ((congrArg (fun edge : IncidentSourceEdge data
        (WallBlock.sourceVertex data wall block) ↦ edge.1.1.1) hEq).trans shape.deleted_single)
    subst hLabel
    right
    have hRepr := congrArg (fun edge : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall block) ↦ edge.1.1.2) hEq
    change (data.edgePartition (star.edge profile.singleLabel)).repr sheet =
      profile.deleted.edge.1.1.2 at hRepr
    have hPin : pinSheet profile profile.singleLabel = profile.deleted.edge.1.1.2 :=
      congrArg (fun edge : IncidentSourceEdge data
        (WallBlock.sourceVertex data wall block) ↦ edge.1.1.2) pinnedOccurrence_single
    rw [SheetPartition.rel_iff, edgePartition_repr_pin shape, hRepr, hPin]

/-- Off the pinned sheet, every sheet of `A₀` is in the bulk occurrence's
block. -/
theorem edgePartition_rel_bulk (shape : Shape profile) (label : Fin 2) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet)
    (hNe : sheet ≠ pinSheet profile label) :
    (data.edgePartition (star.edge label)).Rel (bulkSheet profile label) sheet := by
  rcases edgePartition_covers shape label sheet hSheet with hRel | hRel
  · exact hRel
  · refine absurd ?_ hNe
    have hMem : sheet ∈ (data.edgePartition (star.edge label)).block (pinSheet profile label) :=
      ((data.edgePartition (star.edge label)).mem_block_iff _ _).mpr hRel
    rw [pinSheet_block shape label] at hMem
    simpa using hMem

/-- **The exact induced-block count of one wall direction on `A₀`: two.** -/
theorem edgePartition_blockCountWithin (shape : Shape profile) (label : Fin 2)
    (anchor : Fin degree) (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    (data.edgePartition (star.edge label)).blockCountWithin
      (data.vertexPartition wall) anchor = 2 := by
  classical
  have hBulkMem : bulkSheet profile label ∈ (data.vertexPartition wall).block anchor :=
    ((data.vertexPartition wall).mem_block_iff anchor _).mpr
      (hAnchor.symm.trans (bulkSheet_rel label))
  have hPinMem : pinSheet profile label ∈ (data.vertexPartition wall).block anchor :=
    ((data.vertexPartition wall).mem_block_iff anchor _).mpr
      (hAnchor.symm.trans (pinSheet_rel label))
  have hImage : ((data.vertexPartition wall).block anchor).image
      (data.edgePartition (star.edge label)).repr =
      {bulkSheet profile label, pinSheet profile label} := by
    ext value
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton,
      SheetPartition.mem_block_iff]
    constructor
    · rintro ⟨source, hSource, rfl⟩
      rcases edgePartition_covers shape label source (hAnchor.trans hSource) with h | h
      · exact Or.inl (by rw [← edgePartition_repr_bulk (profile := profile) label, h])
      · exact Or.inr (by rw [← edgePartition_repr_pin shape label, h])
    · rintro (rfl | rfl)
      · exact ⟨bulkSheet profile label,
          (((data.vertexPartition wall).mem_block_iff anchor _).mp hBulkMem),
          edgePartition_repr_bulk label⟩
      · exact ⟨pinSheet profile label,
          (((data.vertexPartition wall).mem_block_iff anchor _).mp hPinMem),
          edgePartition_repr_pin shape label⟩
  unfold SheetPartition.blockCountWithin
  rw [hImage, Finset.card_insert_of_notMem (by
    simpa using bulkSheet_ne_pinSheet shape label), Finset.card_singleton]

end Directions

/-! ## §2  The two new endpoints of a divalent member, read uniformly

Both `M⁽²⁾` and `M⁽³⁾` are two-star members: they retain `star.edge 0` at the
old endpoint and send `star.edge 1` to the fresh one.  Which of the two is the
profile's `doubleLabel` is **not** fixed by anything in
`W2M1kSourceCandidates`' bundle, so every endpoint statement below is indexed
by a `side : Bool` -- `false` the retained copy of the wall, `true` the fresh
one, as in `LimitChainCore.wallSide` -- and the direction it carries is
`star.edge (sideLabel side)`.  The census then names the two sides by the
profile's own labels (`sideOf profile.doubleLabel`, `sideOf profile.singleLabel`)
and nothing is proved twice.
-/

section Sides

/-- The wall direction a two-star member sends to one side of its new edge. -/
def sideLabel : Bool → Fin 2
  | false => 0
  | true => 1

/-- The side of the new edge a wall direction is sent to: the inverse of
`sideLabel`. -/
def sideOf (label : Fin 2) : Bool := decide (label = 1)

@[simp] theorem sideLabel_sideOf (label : Fin 2) : sideLabel (sideOf label) = label := by
  fin_cases label <;> rfl

theorem sideOf_inj {first second : Fin 2} (hEq : sideOf first = sideOf second) :
    first = second := by
  rw [← sideLabel_sideOf first, ← sideLabel_sideOf second, hEq]

theorem sideOf_ne {first second : Fin 2} (hNe : first ≠ second) :
    sideOf first ≠ sideOf second := fun hEq ↦ hNe (sideOf_inj hEq)

theorem sideLabel_not (side : Bool) : sideLabel (!side) ≠ sideLabel side := by
  cases side <;> decide

/-- The endpoint partition of a pasted candidate on one side of its new
edge. -/
noncomputable def pastedSide (candidate : BalancedGlobal.Candidate target degree data wall) :
    Bool → SheetPartition degree
  | false => (pasted candidate).left
  | true => (pasted candidate).right

variable {candidate : BalancedGlobal.Candidate target degree data wall}
  {twoStar : TwoStar target wall}

/-- **The complete source incidence count at either new endpoint of a two-star
member.**  `LimitChainCore.card_incident_oldEndpoint` and
`card_incident_freshEndpoint`, in one statement. -/
theorem card_incident_side (hRight : ∀ edge, candidate.right edge = twoStar.right edge)
    (side : Bool) (sheet : Fin degree) :
    Fintype.card (IncidentSourceEdge candidate.datum
        (candidate.datum.sourceEndpoint (wallSide target wall side) sheet)) =
      (pasted candidate).newEdge.blockCountWithin (pastedSide candidate side) sheet +
        (data.edgePartition (twoStar.edge (sideLabel side))).blockCountWithin
          (pastedSide candidate side) sheet := by
  cases side
  · exact card_incident_oldEndpoint hRight sheet
  · exact card_incident_freshEndpoint hRight sheet

/-- The new occurrence through a sheet meets its new endpoint on either
side. -/
theorem newSourceEdge_incident_side (candidate : BalancedGlobal.Candidate target degree data wall)
    (side : Bool) (sheet : Fin degree) :
    Incident candidate.datum (candidate.newSourceEdge sheet)
      (candidate.datum.sourceEndpoint (wallSide target wall side) sheet) := by
  cases side
  · exact newSourceEdge_incident_old _
  · exact newSourceEdge_incident_fresh _

/-- A retained wall occurrence meets the new endpoint on the side it is
assigned to, over its own sheet. -/
theorem oldSourceEdge_incident_side
    (candidate : BalancedGlobal.Candidate target degree data wall) (edge : target.edges)
    (hAt : edge ∈ GluingDatum.incidentEdges wall) (side : Bool)
    (hRight : candidate.right edge = side) (sheet : Fin degree) :
    Incident candidate.datum (candidate.oldSourceEdge (data.sourceEdge edge sheet))
      (candidate.datum.sourceEndpoint (wallSide target wall side) sheet) := by
  cases side
  · exact oldSourceEdge_incident_old candidate edge hAt hRight sheet
  · exact M11SplitSurvival.oldSourceEdge_incident_fresh candidate edge hAt hRight sheet

/-- Two sheets in one block of an endpoint partition name one source
vertex. -/
theorem sourceEndpoint_side_eq_of_rel (side : Bool) {first second : Fin degree}
    (hRel : (pastedSide candidate side).Rel first second) :
    candidate.datum.sourceEndpoint (wallSide target wall side) first =
      candidate.datum.sourceEndpoint (wallSide target wall side) second := by
  cases side
  · exact sourceEndpoint_old_eq_of_rel _ _ hRel
  · exact sourceEndpoint_fresh_eq_of_rel _ _ hRel

/-- An old occurrence incident to a fresh new endpoint has its sheet in that
endpoint's class.  The mirror of
`LimitChainCore.old_incident_fresh_sheet_rel` for the new occurrences. -/
theorem new_incident_fresh_sheet_rel
    (candidate : BalancedGlobal.Candidate target degree data wall)
    (anchor sheet : Fin degree)
    (hIncident : Incident candidate.datum (candidate.newSourceEdge sheet)
      (candidate.datum.sourceEndpoint (freshVertex target) anchor)) :
    (pasted candidate).right.Rel anchor sheet := by
  have hOutgoing := (incident_iff_target_mem_and_rel candidate.datum
    (candidate.newSourceEdge sheet)
    (candidate.datum.sourceEndpoint (freshVertex target) anchor)).mp hIncident
  change occurrenceEquiv target wall candidate.right none ∈
      GluingDatum.incidentEdges (freshVertex target) ∧
    (pasted candidate).right.Rel ((pasted candidate).right.repr anchor)
      ((pasted candidate).newEdge.repr sheet) at hOutgoing
  refine (((pasted candidate).right.rel_repr_right anchor).trans hOutgoing.2).trans ?_
  exact (pasted candidate).edge_refines_right.rel
    ((pasted candidate).newEdge.rel_repr_left sheet)

end Sides

/-! ## §3  The divided member's endpoint counts

`M⁽²⁾` is `DividedData.candidate`: each of the two divalent endpoints detaches
the pinned sheet of *its own* wall direction, and the new edge carries the two
detached singletons together with the residual `k - 1` class.
-/

section Divided

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- Any two pinned sheets lie in the distinguished wall block. -/
theorem pin_rel_pin (profile : W2R2SourceProfile.SourceProfile data star block)
    (first second : Fin 2) :
    (data.vertexPartition wall).Rel (pinSheet profile first) (pinSheet profile second) :=
  (pinSheet_rel first).symm.trans (pinSheet_rel second)

/-- `M⁽²⁾`'s new-edge partition on `A₀`: `{p₀}`, `{p₁}` and the residual
`k - 1` class. -/
noncomputable def dividedNewEdge (divided : DividedData profile) : SheetPartition degree :=
  secondNewEdge (data.vertexPartition wall) (pinSheet profile 0) (pinSheet profile 1)
    divided.third (pin_rel_pin profile 0 1) divided.rel_third divided.pins_ne
    divided.ne_first divided.ne_second

/-- `M⁽²⁾`'s endpoint partition on `A₀`, on either side of the new edge: the
side carrying `star.edge (sideLabel side)` detaches that direction's pinned
sheet. -/
noncomputable def dividedEndpoint (divided : DividedData profile) :
    Bool → SheetPartition degree
  | false => (data.vertexPartition wall).detachSheet (pinSheet profile 0)
      (pinSheet profile 1) divided.pins_ne (pin_rel_pin profile 0 1)
  | true => (data.vertexPartition wall).detachSheet (pinSheet profile 1)
      (pinSheet profile 0) divided.pins_ne.symm (pin_rel_pin profile 1 0)

/-- The member's side assignment is the two-star's own. -/
theorem divided_right (shape : Shape profile) (divided : DividedData profile)
    (edge : target.edges) :
    (DividedData.candidate shape divided).right edge = star.right edge := rfl

/-- On the distinguished block the member is literally Figure 33's
`secondResolution`. -/
theorem divided_resolution (shape : Shape profile) (divided : DividedData profile)
    (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel (pinSheet profile 0) anchor) :
    (DividedData.candidate shape divided).resolution anchor =
      secondResolution (data.vertexPartition wall) (pinSheet profile 0)
        (pinSheet profile 1) divided.third (pin_rel_pin profile 0 1) divided.rel_third
        divided.pins_ne divided.ne_first divided.ne_second := by
  change LocalResolution.onBlock (data.vertexPartition wall) (pinSheet profile 0) _
    (fun _ ↦ joinedResolutionAt (data.vertexPartition wall)) anchor = _
  rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hAnchor]
  rfl

theorem divided_blockCountWithin_side (shape : Shape profile) (divided : DividedData profile)
    (fine : SheetPartition degree) (side : Bool) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet) :
    fine.blockCountWithin (pastedSide (DividedData.candidate shape divided) side) sheet =
      fine.blockCountWithin (dividedEndpoint divided side) sheet := by
  cases side
  · show fine.blockCountWithin (pasted (DividedData.candidate shape divided)).left sheet = _
    rw [LocalResolution.blockCountWithin_paste_left, divided_resolution shape divided _
      (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]
    rfl
  · show fine.blockCountWithin (pasted (DividedData.candidate shape divided)).right sheet = _
    rw [LocalResolution.blockCountWithin_paste_right, divided_resolution shape divided _
      (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]
    rfl

theorem divided_newEdge_within_side (shape : Shape profile) (divided : DividedData profile)
    (side : Bool) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet) :
    (pasted (DividedData.candidate shape divided)).newEdge.blockCountWithin
        (pastedSide (DividedData.candidate shape divided) side) sheet =
      (dividedNewEdge divided).blockCountWithin (dividedEndpoint divided side) sheet := by
  cases side
  · show (pasted (DividedData.candidate shape divided)).newEdge.blockCountWithin
      (pasted (DividedData.candidate shape divided)).left sheet = _
    rw [LocalResolution.paste_newEdge_blockCountWithin_left, divided_resolution shape divided _
      (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]
    rfl
  · show (pasted (DividedData.candidate shape divided)).newEdge.blockCountWithin
      (pasted (DividedData.candidate shape divided)).right sheet = _
    rw [LocalResolution.paste_newEdge_blockCountWithin_right, divided_resolution shape divided _
      (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]
    rfl

/-- Each endpoint of `M⁽²⁾` isolates its own direction's pinned sheet. -/
theorem dividedEndpoint_block_pin (divided : DividedData profile) (side : Bool) :
    (dividedEndpoint divided side).block (pinSheet profile (sideLabel side)) =
      {pinSheet profile (sideLabel side)} := by
  cases side
  · exact (data.vertexPartition wall).detachSheet_block_single (pinSheet profile 0)
      (pinSheet profile 1) divided.pins_ne (pin_rel_pin profile 0 1)
  · exact (data.vertexPartition wall).detachSheet_block_single (pinSheet profile 1)
      (pinSheet profile 0) divided.pins_ne.symm (pin_rel_pin profile 1 0)

/-- The new edge isolates both pinned sheets. -/
theorem dividedNewEdge_block_pin (divided : DividedData profile) (side : Bool) :
    (dividedNewEdge divided).block (pinSheet profile (sideLabel side)) =
      {pinSheet profile (sideLabel side)} := by
  cases side
  · exact secondNewEdge_block_first (data.vertexPartition wall) (pinSheet profile 0)
      (pinSheet profile 1) divided.third (pin_rel_pin profile 0 1) divided.rel_third
      divided.pins_ne divided.ne_first divided.ne_second
  · have hSplit : dividedNewEdge divided =
        ((data.vertexPartition wall).detachSheet (pinSheet profile 0) (pinSheet profile 1)
          divided.pins_ne (pin_rel_pin profile 0 1)).detachSheet (pinSheet profile 1)
          divided.third divided.ne_second
          (detachFirst_rel_second_third (data.vertexPartition wall) (pinSheet profile 0)
            (pinSheet profile 1) divided.third (pin_rel_pin profile 0 1) divided.rel_third
            divided.pins_ne divided.ne_first) := rfl
    rw [hSplit]
    exact ((data.vertexPartition wall).detachSheet (pinSheet profile 0) (pinSheet profile 1)
      divided.pins_ne (pin_rel_pin profile 0 1)).detachSheet_block_single
      (pinSheet profile 1) divided.third divided.ne_second
      (detachFirst_rel_second_third (data.vertexPartition wall) (pinSheet profile 0)
        (pinSheet profile 1) divided.third (pin_rel_pin profile 0 1) divided.rel_third
        divided.pins_ne divided.ne_first)

/-- `M⁽²⁾`'s new edge induces three blocks on `A₀`. -/
theorem dividedNewEdge_blockCountWithin (divided : DividedData profile) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet) :
    (dividedNewEdge divided).blockCountWithin (data.vertexPartition wall) sheet = 3 :=
  secondNewEdge_blockCountWithin (data.vertexPartition wall) (pinSheet profile 0)
    (pinSheet profile 1) divided.third sheet (pin_rel_pin profile 0 1) divided.rel_third
    divided.pins_ne divided.ne_first divided.ne_second hSheet

/-- **Two incidences at the endpoint over a pinned singleton**: that
direction's own pinned occurrence and the new occurrence through the sheet. -/
theorem divided_card_incident_pin (shape : Shape profile) (divided : DividedData profile)
    (side : Bool) :
    Fintype.card (IncidentSourceEdge (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall side) (pinSheet profile (sideLabel side)))) = 2 := by
  rw [card_incident_side (twoStar := star) (divided_right shape divided) side _,
    divided_newEdge_within_side shape divided side _ (pin_rel_pin profile 0 (sideLabel side)),
    divided_blockCountWithin_side shape divided
      (data.edgePartition (star.edge (sideLabel side))) side _
      (pin_rel_pin profile 0 (sideLabel side)),
    SheetPartition.blockCountWithin_eq_one_of_block_eq_singleton _ _ _
      (dividedEndpoint_block_pin divided side),
    SheetPartition.blockCountWithin_eq_one_of_block_eq_singleton _ _ _
      (dividedEndpoint_block_pin divided side)]

/-- **Three incidences at the endpoint over the residual `k`-class**: that
direction's bulk occurrence, the other side's pinned new occurrence, and the
residual new occurrence. -/
theorem divided_card_incident_other (shape : Shape profile) (divided : DividedData profile)
    (side : Bool) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (hNe : sheet ≠ pinSheet profile (sideLabel side)) :
    Fintype.card (IncidentSourceEdge (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall side) sheet)) = 3 := by
  have hPinWall : (data.vertexPartition wall).Rel (pinSheet profile (sideLabel side)) sheet :=
    (pin_rel_pin profile (sideLabel side) 0).trans hWall
  have hNew : (dividedNewEdge divided).blockCountWithin
      (dividedEndpoint divided side) sheet + 1 =
      (dividedNewEdge divided).blockCountWithin (data.vertexPartition wall) sheet := by
    cases side
    · exact W3ShiftSourceCandidates.blockCountWithin_detachSheet_of_singleton
        (dividedNewEdge divided) (data.vertexPartition wall) (pinSheet profile 0)
        (pinSheet profile 1) sheet divided.pins_ne (pin_rel_pin profile 0 1)
        (dividedNewEdge_block_pin divided false) hPinWall hNe
    · exact W3ShiftSourceCandidates.blockCountWithin_detachSheet_of_singleton
        (dividedNewEdge divided) (data.vertexPartition wall) (pinSheet profile 1)
        (pinSheet profile 0) sheet divided.pins_ne.symm (pin_rel_pin profile 1 0)
        (dividedNewEdge_block_pin divided true) hPinWall hNe
  have hOld : (data.edgePartition (star.edge (sideLabel side))).blockCountWithin
      (dividedEndpoint divided side) sheet + 1 =
      (data.edgePartition (star.edge (sideLabel side))).blockCountWithin
        (data.vertexPartition wall) sheet := by
    cases side
    · exact W3ShiftSourceCandidates.blockCountWithin_detachSheet_of_singleton
        (data.edgePartition (star.edge (sideLabel false))) (data.vertexPartition wall)
        (pinSheet profile 0) (pinSheet profile 1) sheet divided.pins_ne
        (pin_rel_pin profile 0 1) (pinSheet_block shape 0) hPinWall hNe
    · exact W3ShiftSourceCandidates.blockCountWithin_detachSheet_of_singleton
        (data.edgePartition (star.edge (sideLabel true))) (data.vertexPartition wall)
        (pinSheet profile 1) (pinSheet profile 0) sheet divided.pins_ne.symm
        (pin_rel_pin profile 1 0) (pinSheet_block shape 1) hPinWall hNe
  have hNewTotal := dividedNewEdge_blockCountWithin divided sheet hWall
  have hOldTotal := edgePartition_blockCountWithin shape (sideLabel side) sheet
    ((pinSheet_rel 0).trans hWall)
  rw [card_incident_side (twoStar := star) (divided_right shape divided) side _,
    divided_newEdge_within_side shape divided side _ hWall,
    divided_blockCountWithin_side shape divided
      (data.edgePartition (star.edge (sideLabel side))) side _ hWall]
  omega

end Divided

/-! ## §4  The divided member's incidence dictionary -/

section DividedIncidence

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- Label `0` is retained and label `1` is sent to the fresh endpoint. -/
theorem divided_right_side (shape : Shape profile) (divided : DividedData profile)
    (side : Bool) :
    (DividedData.candidate shape divided).right (star.edge (sideLabel side)) = side := by
  cases side
  · exact star.right_edge_zero
  · exact star.right_edge_one

/-- Distinct labels pin distinct sheets, for `M⁽²⁾`. -/
theorem divided_pin_ne {first second : Fin 2} (divided : DividedData profile)
    (hNe : first ≠ second) : pinSheet profile first ≠ pinSheet profile second := by
  have hFirst : first = 0 ∨ first = 1 := by omega
  have hSecond : second = 0 ∨ second = 1 := by omega
  rcases hFirst with rfl | rfl <;> rcases hSecond with rfl | rfl
  · exact absurd rfl hNe
  · exact divided.pins_ne
  · exact divided.pins_ne.symm
  · exact absurd rfl hNe

/-- The residual sheet is neither pinned sheet. -/
theorem divided_third_ne_pin (divided : DividedData profile) (label : Fin 2) :
    divided.third ≠ pinSheet profile label := by
  have hLabel : label = 0 ∨ label = 1 := by omega
  rcases hLabel with rfl | rfl
  · exact divided.ne_first.symm
  · exact divided.ne_second.symm

theorem divided_third_wall (divided : DividedData profile) :
    (data.vertexPartition wall).Rel (pinSheet profile 0) divided.third := divided.rel_third

/-- Sheets of `A₀` off one side's pinned sheet share that side's endpoint
block. -/
theorem divided_endpoint_rel (divided : DividedData profile) (side : Bool)
    (first second : Fin degree)
    (hFirstWall : (data.vertexPartition wall).Rel (pinSheet profile 0) first)
    (hFirstNe : first ≠ pinSheet profile (sideLabel side))
    (hSecondWall : (data.vertexPartition wall).Rel (pinSheet profile 0) second)
    (hSecondNe : second ≠ pinSheet profile (sideLabel side)) :
    (dividedEndpoint divided side).Rel first second := by
  cases side
  · exact (W3ShiftSourceCandidates.detachSheet_rel_remainder (data.vertexPartition wall)
      (pinSheet profile 0) (pinSheet profile 1) first divided.pins_ne
      (pin_rel_pin profile 0 1) hFirstWall hFirstNe).trans
      (W3ShiftSourceCandidates.detachSheet_rel_remainder (data.vertexPartition wall)
        (pinSheet profile 0) (pinSheet profile 1) second divided.pins_ne
        (pin_rel_pin profile 0 1) hSecondWall hSecondNe).symm
  · exact (W3ShiftSourceCandidates.detachSheet_rel_remainder (data.vertexPartition wall)
      (pinSheet profile 1) (pinSheet profile 0) first divided.pins_ne.symm
      (pin_rel_pin profile 1 0) ((pin_rel_pin profile 1 0).trans hFirstWall) hFirstNe).trans
      (W3ShiftSourceCandidates.detachSheet_rel_remainder (data.vertexPartition wall)
        (pinSheet profile 1) (pinSheet profile 0) second divided.pins_ne.symm
        (pin_rel_pin profile 1 0) ((pin_rel_pin profile 1 0).trans hSecondWall)
        hSecondNe).symm

/-- Over `A₀` the member's pasted endpoint is its own `secondResolution`
endpoint. -/
theorem divided_pastedSide_rel (shape : Shape profile) (divided : DividedData profile)
    (side : Bool) (first second : Fin degree)
    (hFirstWall : (data.vertexPartition wall).Rel (pinSheet profile 0) first)
    (hRel : (dividedEndpoint divided side).Rel first second) :
    (pastedSide (DividedData.candidate shape divided) side).Rel first second := by
  cases side
  · show (LocalResolution.pasteLeft (data.vertexPartition wall)
      (DividedData.candidate shape divided).resolution
      (DividedData.candidate shape divided).contracts).Rel first second
    unfold LocalResolution.pasteLeft
    rw [SheetPartition.paste_rel_iff, divided_resolution shape divided _
      (hFirstWall.trans ((data.vertexPartition wall).rel_repr_right first))]
    exact hRel
  · show (LocalResolution.pasteRight (data.vertexPartition wall)
      (DividedData.candidate shape divided).resolution
      (DividedData.candidate shape divided).contracts).Rel first second
    unfold LocalResolution.pasteRight
    rw [SheetPartition.paste_rel_iff, divided_resolution shape divided _
      (hFirstWall.trans ((data.vertexPartition wall).rel_repr_right first))]
    exact hRel

/-- Over `A₀` the member's pasted new edge is its own `secondNewEdge`. -/
theorem divided_pasted_newEdge_rel_iff (shape : Shape profile) (divided : DividedData profile)
    (first second : Fin degree)
    (hFirstWall : (data.vertexPartition wall).Rel (pinSheet profile 0) first) :
    (pasted (DividedData.candidate shape divided)).newEdge.Rel first second ↔
      (dividedNewEdge divided).Rel first second := by
  show (LocalResolution.pasteNewEdge (data.vertexPartition wall)
    (DividedData.candidate shape divided).resolution
    (DividedData.candidate shape divided).contracts).Rel first second ↔ _
  unfold LocalResolution.pasteNewEdge
  rw [SheetPartition.paste_rel_iff, divided_resolution shape divided _
    (hFirstWall.trans ((data.vertexPartition wall).rel_repr_right first))]
  exact Iff.rfl

/-- Sheets of `A₀` off both pinned sheets carry the residual new
occurrence. -/
theorem divided_newEdge_rel_third (divided : DividedData profile) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (hZero : sheet ≠ pinSheet profile 0) (hOne : sheet ≠ pinSheet profile 1) :
    (dividedNewEdge divided).Rel sheet divided.third := by
  have hInner : (data.vertexPartition wall).Rel (pinSheet profile 0) divided.third :=
    divided.rel_third
  have hFirst := W3ShiftSourceCandidates.detachSheet_rel_remainder
    (data.vertexPartition wall) (pinSheet profile 0) (pinSheet profile 1) sheet
    divided.pins_ne (pin_rel_pin profile 0 1) hWall hZero
  have hOuter : ((data.vertexPartition wall).detachSheet (pinSheet profile 0)
      (pinSheet profile 1) divided.pins_ne (pin_rel_pin profile 0 1)).Rel
      (pinSheet profile 1) divided.third :=
    detachFirst_rel_second_third (data.vertexPartition wall) (pinSheet profile 0)
      (pinSheet profile 1) divided.third (pin_rel_pin profile 0 1) hInner
      divided.pins_ne divided.ne_first
  have hSplit : dividedNewEdge divided =
      ((data.vertexPartition wall).detachSheet (pinSheet profile 0) (pinSheet profile 1)
        divided.pins_ne (pin_rel_pin profile 0 1)).detachSheet (pinSheet profile 1)
        divided.third divided.ne_second hOuter := rfl
  rw [hSplit]
  exact W3ShiftSourceCandidates.detachSheet_rel_remainder
    ((data.vertexPartition wall).detachSheet (pinSheet profile 0) (pinSheet profile 1)
      divided.pins_ne (pin_rel_pin profile 0 1)) (pinSheet profile 1) divided.third
    sheet divided.ne_second hOuter hFirst.symm hOne

/-- **The member has exactly three new occurrences over `A₀`**: the two pinned
singletons and the residual `k - 1` class. -/
theorem divided_newSourceEdge_eq_third (shape : Shape profile) (divided : DividedData profile)
    (sheet : Fin degree) (hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (hZero : sheet ≠ pinSheet profile 0) (hOne : sheet ≠ pinSheet profile 1) :
    (DividedData.candidate shape divided).newSourceEdge sheet =
      (DividedData.candidate shape divided).newSourceEdge divided.third :=
  (newSourceEdge_eq_iff_rel _ _).mpr
    ((divided_pasted_newEdge_rel_iff shape divided sheet divided.third hWall).mpr
      (divided_newEdge_rel_third divided sheet hWall hZero hOne))

/-- The two pinned new occurrences and the residual one are pairwise
distinct. -/
theorem divided_newSourceEdge_pin_ne (shape : Shape profile) (divided : DividedData profile)
    (label : Fin 2) (sheet : Fin degree) (hNe : sheet ≠ pinSheet profile label) :
    (DividedData.candidate shape divided).newSourceEdge (pinSheet profile label) ≠
      (DividedData.candidate shape divided).newSourceEdge sheet := by
  intro hEqual
  refine hNe ?_
  have hRel := (divided_pasted_newEdge_rel_iff shape divided _ _
    (pin_rel_pin profile 0 label)).mp ((newSourceEdge_eq_iff_rel _ _).mp hEqual)
  have hMem : sheet ∈ (dividedNewEdge divided).block (pinSheet profile label) :=
    ((dividedNewEdge divided).mem_block_iff _ _).mpr hRel
  rw [show (dividedNewEdge divided).block (pinSheet profile label) =
    {pinSheet profile label} from by
      have := dividedNewEdge_block_pin divided (sideOf label)
      rwa [sideLabel_sideOf] at this] at hMem
  simpa using hMem

/-- The pinned occurrence of one direction meets that direction's own
endpoint over the pinned sheet. -/
theorem divided_pinned_incident (shape : Shape profile) (divided : DividedData profile)
    (side : Bool) :
    Incident (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).oldSourceEdge
        (pinnedOccurrence profile (sideLabel side)).1)
      ((DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall side) (pinSheet profile (sideLabel side))) := by
  have hAt : (pinnedOccurrence profile (sideLabel side)).1.1.1 ∈
      GluingDatum.incidentEdges wall := by
    rw [pinnedOccurrence_target shape]
    exact star.edge_mem_incidentEdges _
  have hRight : (DividedData.candidate shape divided).right
      (pinnedOccurrence profile (sideLabel side)).1.1.1 = side := by
    rw [pinnedOccurrence_target shape]
    exact divided_right_side shape divided side
  have h := oldSourceEdge_incident_side (DividedData.candidate shape divided)
    (pinnedOccurrence profile (sideLabel side)).1.1.1 hAt side hRight
    (pinSheet profile (sideLabel side))
  rwa [show data.sourceEdge (pinnedOccurrence profile (sideLabel side)).1.1.1
    (pinSheet profile (sideLabel side)) = (pinnedOccurrence profile (sideLabel side)).1 from
      GluingDatum.sourceEdge_self data _] at h

/-- The bulk occurrence of one direction meets that direction's own endpoint
over every sheet of the residual class. -/
theorem divided_bulk_incident (shape : Shape profile) (divided : DividedData profile)
    (side : Bool) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (hNe : sheet ≠ pinSheet profile (sideLabel side)) :
    Incident (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).oldSourceEdge
        (bulkOccurrence profile (sideLabel side)).1)
      ((DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall side) sheet) := by
  have hAt : (bulkOccurrence profile (sideLabel side)).1.1.1 ∈
      GluingDatum.incidentEdges wall := by
    rw [bulkOccurrence_target]
    exact star.edge_mem_incidentEdges _
  have hRight : (DividedData.candidate shape divided).right
      (bulkOccurrence profile (sideLabel side)).1.1.1 = side := by
    rw [bulkOccurrence_target]
    exact divided_right_side shape divided side
  have h := oldSourceEdge_incident_side (DividedData.candidate shape divided)
    (bulkOccurrence profile (sideLabel side)).1.1.1 hAt side hRight
    (bulkSheet profile (sideLabel side))
  rw [show data.sourceEdge (bulkOccurrence profile (sideLabel side)).1.1.1
    (bulkSheet profile (sideLabel side)) = (bulkOccurrence profile (sideLabel side)).1 from
      GluingDatum.sourceEdge_self data _] at h
  have hVertex : (DividedData.candidate shape divided).datum.sourceEndpoint
      (wallSide target wall side) (bulkSheet profile (sideLabel side)) =
      (DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall side) sheet :=
    sourceEndpoint_side_eq_of_rel side (divided_pastedSide_rel shape divided side _ _
      ((pinSheet_rel 0).symm.trans (bulkSheet_rel (sideLabel side)))
      (divided_endpoint_rel divided side _ _
        ((pinSheet_rel 0).symm.trans (bulkSheet_rel (sideLabel side)))
        (bulkSheet_ne_pinSheet shape (sideLabel side)) hWall hNe))
  exact hVertex ▸ h

/-- Sheets of one side's residual class share that side's new endpoint. -/
theorem divided_endpoint_eq (shape : Shape profile) (divided : DividedData profile)
    (side : Bool) (first second : Fin degree)
    (hFirstWall : (data.vertexPartition wall).Rel (pinSheet profile 0) first)
    (hFirstNe : first ≠ pinSheet profile (sideLabel side))
    (hSecondWall : (data.vertexPartition wall).Rel (pinSheet profile 0) second)
    (hSecondNe : second ≠ pinSheet profile (sideLabel side)) :
    (DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall side) first =
      (DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall side) second :=
  sourceEndpoint_side_eq_of_rel side (divided_pastedSide_rel shape divided side _ _
    hFirstWall (divided_endpoint_rel divided side first second hFirstWall hFirstNe
      hSecondWall hSecondNe))

end DividedIncidence

/-! ## §5  Which occurrences of the divided member survive

`e₁`, `e₂`, `e₃` survive and `e₄` is pruned, as in every member.  Of the three
new occurrences over `A₀` exactly one dies: **the new occurrence through `e₄`'s
sheet**, whose endpoint on the `t₃` side is the divalent source vertex
`{pinSheet profile singleLabel}` carrying nothing but `e₄`.  That is the M-1k
form of `W2MkkStableGraph.detach_new_pin_dangling`, and it is again what makes
the `t₃` endpoint over `A₀ ∖ {e₄'s sheet}` a branch vertex rather than a
carrier of a surviving parallel pair.
-/

section DividedSurvival

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- Each of `0`, `1` is the double or the single label. -/
theorem pinSheet_cases (profile : W2R2SourceProfile.SourceProfile data star block)
    (label : Fin 2) :
    pinSheet profile label = pinSheet profile profile.doubleLabel ∨
      pinSheet profile label = pinSheet profile profile.singleLabel := by
  rcases Shape.label_cases profile label with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Genus-preserving pruning keeps `e₄` dangling. -/
theorem divided_deleted_dangling (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) :
    IsDangling (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).oldSourceEdge profile.deleted.edge.1) :=
  (ResolutionPruning.isDangling_oldSourceEdge_iff _ input.valid
    (divided_sourceGenus shape divided) _).mpr profile.deleted.dangling

/-- **A pinned new occurrence lives exactly as long as its own direction's
pinned old occurrence.**  Their common endpoint is the divalent source vertex
over the pinned singleton. -/
theorem divided_new_pin_survives_iff (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (label : Fin 2) :
    (¬ IsDangling (DividedData.candidate shape divided).datum
        ((DividedData.candidate shape divided).newSourceEdge (pinSheet profile label))) ↔
      ¬ IsDangling (DividedData.candidate shape divided).datum
        ((DividedData.candidate shape divided).oldSourceEdge
          (pinnedOccurrence profile label).1) := by
  have hCard : Fintype.card (IncidentSourceEdge (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall (sideOf label)) (pinSheet profile label))) = 2 := by
    simpa only [sideLabel_sideOf] using divided_card_incident_pin shape divided (sideOf label)
  have hPinned : Incident (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).oldSourceEdge
        (pinnedOccurrence profile label).1)
      ((DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall (sideOf label)) (pinSheet profile label)) := by
    simpa only [sideLabel_sideOf] using divided_pinned_incident shape divided (sideOf label)
  exact survives_iff_of_card_two (DividedData.candidate shape divided).datum
    (divided_valid input shape divided).1 _ _ _
    (newSourceEdge_incident_side _ (sideOf label) _) hPinned hCard

/-- **The new occurrence through `e₄`'s sheet dies with `e₄`.**  The genuinely
new phenomenon of the divided member, and the M-1k analogue of
`W2MkkStableGraph.detach_new_pin_dangling`. -/
theorem divided_new_deleted_dangling (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) :
    IsDangling (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).newSourceEdge
        (pinSheet profile profile.singleLabel)) := by
  by_contra hSurvives
  refine ((divided_new_pin_survives_iff input shape divided profile.singleLabel).mp
    hSurvives) ?_
  rw [pinnedOccurrence_single]
  exact divided_deleted_dangling input shape divided

/-- The new occurrence through `e₁`'s sheet survives: `e₁` does. -/
theorem divided_new_unit_survives (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) :
    ¬ IsDangling (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).newSourceEdge
        (pinSheet profile profile.doubleLabel)) := by
  refine (divided_new_pin_survives_iff input shape divided profile.doubleLabel).mpr ?_
  rw [pinnedOccurrence_double]
  exact ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ profile.first_survives

/-- The residual new occurrence survives: at the `t₂` endpoint over the
residual class it is the third arm of a trivalent vertex whose other two are
the surviving `e₂` and the pruned new occurrence through `e₄`'s sheet. -/
theorem divided_new_third_survives (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) :
    ¬ IsDangling (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).newSourceEdge divided.third) := by
  have hThirdNe : divided.third ≠ pinSheet profile (sideLabel (sideOf profile.doubleLabel)) := by
    rw [sideLabel_sideOf]
    exact divided_third_ne_pin divided _
  have hSingleNe : pinSheet profile profile.singleLabel ≠
      pinSheet profile (sideLabel (sideOf profile.doubleLabel)) := by
    rw [sideLabel_sideOf]
    exact divided_pin_ne divided profile.labels_ne.symm
  have hVertex := divided_endpoint_eq shape divided (sideOf profile.doubleLabel)
    (pinSheet profile profile.singleLabel) divided.third
    (pin_rel_pin profile 0 profile.singleLabel) hSingleNe divided.rel_third hThirdNe
  have hBulk : Incident (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).oldSourceEdge
        (bulkOccurrence profile profile.doubleLabel).1)
      ((DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall (sideOf profile.doubleLabel)) divided.third) := by
    simpa only [sideLabel_sideOf] using divided_bulk_incident shape divided
      (sideOf profile.doubleLabel) divided.third divided.rel_third hThirdNe
  refine M11SplitSurvival.survives_of_trivalent_of_deleted
    (DividedData.candidate shape divided).datum (divided_valid input shape divided).1 _
    ⟨_, hBulk⟩ ⟨_, hVertex ▸ newSourceEdge_incident_side _ (sideOf profile.doubleLabel)
      (pinSheet profile profile.singleLabel)⟩
    ⟨_, newSourceEdge_incident_side _ (sideOf profile.doubleLabel) divided.third⟩
    (ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
      (bulkOccurrence_survives profile.doubleLabel))
    (divided_new_deleted_dangling input shape divided) ?_
    (divided_card_incident_other shape divided (sideOf profile.doubleLabel) divided.third
      divided.rel_third hThirdNe)
  · intro hEqual
    exact divided_newSourceEdge_pin_ne shape divided profile.singleLabel divided.third
      (divided_third_ne_pin divided _)
      (congrArg (fun item : IncidentSourceEdge (DividedData.candidate shape divided).datum
        ((DividedData.candidate shape divided).datum.sourceEndpoint
          (wallSide target wall (sideOf profile.doubleLabel)) divided.third) ↦ item.1) hEqual)

/-- **The complete new-occurrence census over `A₀`**: everything but the new
occurrence through `e₄`'s sheet survives. -/
theorem divided_new_survives (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (hNe : sheet ≠ pinSheet profile profile.singleLabel) :
    ¬ IsDangling (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).newSourceEdge sheet) := by
  by_cases hDouble : sheet = pinSheet profile profile.doubleLabel
  · rw [hDouble]
    exact divided_new_unit_survives input shape divided
  · have hZero : sheet ≠ pinSheet profile 0 := by
      rcases pinSheet_cases profile 0 with hEq | hEq <;> rw [hEq]
      · exact hDouble
      · exact hNe
    have hOne : sheet ≠ pinSheet profile 1 := by
      rcases pinSheet_cases profile 1 with hEq | hEq <;> rw [hEq]
      · exact hDouble
      · exact hNe
    rw [divided_newSourceEdge_eq_third shape divided sheet hWall hZero hOne]
    exact divided_new_third_survives input shape divided

end DividedSurvival

/-! ## §6  The divided member's surviving stars and rows

The four endpoints of `M⁽²⁾` above `A₀`, named by the profile's own labels
rather than by `old`/`fresh`, which the bundle does not fix:

| endpoint | incidences | surviving | `nd` |
|---|---|---|---|
| `t₂` side over `{e₁'s sheet}` | `e₁`, new(`e₁`'s sheet) | 2 | 2 |
| `t₂` side over `A₀ ∖ {e₁'s sheet}` | `e₂`, new(`e₄`'s sheet), new(residual) | 2 | 2 |
| `t₃` side over `{e₄'s sheet}` | `e₄`, new(`e₄`'s sheet) | 0 | 0 |
| `t₃` side over `A₀ ∖ {e₄'s sheet}` | `e₃`, new(`e₁`'s sheet), new(residual) | 3 | 3 |

The last row is the member's **branch vertex**, and it sits on the `t₃` side.
-/

section DividedStars

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

theorem divided_unit_incident (shape : Shape profile) (divided : DividedData profile) :
    Incident (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).oldSourceEdge profile.first.1)
      ((DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall (sideOf profile.doubleLabel))
        (pinSheet profile profile.doubleLabel)) := by
  simpa only [sideLabel_sideOf, pinnedOccurrence_double] using
    divided_pinned_incident shape divided (sideOf profile.doubleLabel)

theorem divided_deleted_incident (shape : Shape profile) (divided : DividedData profile) :
    Incident (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).oldSourceEdge profile.deleted.edge.1)
      ((DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall (sideOf profile.singleLabel))
        (pinSheet profile profile.singleLabel)) := by
  simpa only [sideLabel_sideOf, pinnedOccurrence_single] using
    divided_pinned_incident shape divided (sideOf profile.singleLabel)

theorem divided_pair_incident (shape : Shape profile) (divided : DividedData profile)
    (sheet : Fin degree) (hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (hNe : sheet ≠ pinSheet profile profile.doubleLabel) :
    Incident (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).oldSourceEdge profile.second.1)
      ((DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall (sideOf profile.doubleLabel)) sheet) := by
  have hNe' : sheet ≠ pinSheet profile (sideLabel (sideOf profile.doubleLabel)) := by
    rwa [sideLabel_sideOf]
  simpa only [sideLabel_sideOf, bulkOccurrence_double] using
    divided_bulk_incident shape divided (sideOf profile.doubleLabel) sheet hWall hNe'

theorem divided_single_incident (shape : Shape profile) (divided : DividedData profile)
    (sheet : Fin degree) (hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (hNe : sheet ≠ pinSheet profile profile.singleLabel) :
    Incident (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).oldSourceEdge profile.third.1)
      ((DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall (sideOf profile.singleLabel)) sheet) := by
  have hNe' : sheet ≠ pinSheet profile (sideLabel (sideOf profile.singleLabel)) := by
    rwa [sideLabel_sideOf]
  simpa only [sideLabel_sideOf, bulkOccurrence_single] using
    divided_bulk_incident shape divided (sideOf profile.singleLabel) sheet hWall hNe'

theorem divided_card_unit (shape : Shape profile) (divided : DividedData profile) :
    Fintype.card (IncidentSourceEdge (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall (sideOf profile.doubleLabel))
        (pinSheet profile profile.doubleLabel))) = 2 := by
  simpa only [sideLabel_sideOf] using
    divided_card_incident_pin shape divided (sideOf profile.doubleLabel)

theorem divided_card_deleted (shape : Shape profile) (divided : DividedData profile) :
    Fintype.card (IncidentSourceEdge (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall (sideOf profile.singleLabel))
        (pinSheet profile profile.singleLabel))) = 2 := by
  simpa only [sideLabel_sideOf] using
    divided_card_incident_pin shape divided (sideOf profile.singleLabel)

theorem divided_card_pair (shape : Shape profile) (divided : DividedData profile)
    (sheet : Fin degree) (hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (hNe : sheet ≠ pinSheet profile profile.doubleLabel) :
    Fintype.card (IncidentSourceEdge (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall (sideOf profile.doubleLabel)) sheet)) = 3 := by
  refine divided_card_incident_other shape divided (sideOf profile.doubleLabel) sheet hWall ?_
  rwa [sideLabel_sideOf]

theorem divided_card_single (shape : Shape profile) (divided : DividedData profile)
    (sheet : Fin degree) (hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (hNe : sheet ≠ pinSheet profile profile.singleLabel) :
    Fintype.card (IncidentSourceEdge (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall (sideOf profile.singleLabel)) sheet)) = 3 := by
  refine divided_card_incident_other shape divided (sideOf profile.singleLabel) sheet hWall ?_
  rwa [sideLabel_sideOf]

theorem divided_double_endpoint_eq (shape : Shape profile) (divided : DividedData profile)
    (first second : Fin degree)
    (hFirstWall : (data.vertexPartition wall).Rel (pinSheet profile 0) first)
    (hFirstNe : first ≠ pinSheet profile profile.doubleLabel)
    (hSecondWall : (data.vertexPartition wall).Rel (pinSheet profile 0) second)
    (hSecondNe : second ≠ pinSheet profile profile.doubleLabel) :
    (DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall (sideOf profile.doubleLabel)) first =
      (DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall (sideOf profile.doubleLabel)) second := by
  refine divided_endpoint_eq shape divided (sideOf profile.doubleLabel) first second
    hFirstWall ?_ hSecondWall ?_ <;> rwa [sideLabel_sideOf]

theorem divided_single_endpoint_eq (shape : Shape profile) (divided : DividedData profile)
    (first second : Fin degree)
    (hFirstWall : (data.vertexPartition wall).Rel (pinSheet profile 0) first)
    (hFirstNe : first ≠ pinSheet profile profile.singleLabel)
    (hSecondWall : (data.vertexPartition wall).Rel (pinSheet profile 0) second)
    (hSecondNe : second ≠ pinSheet profile profile.singleLabel) :
    (DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall (sideOf profile.singleLabel)) first =
      (DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall (sideOf profile.singleLabel)) second := by
  refine divided_endpoint_eq shape divided (sideOf profile.singleLabel) first second
    hFirstWall ?_ hSecondWall ?_ <;> rwa [sideLabel_sideOf]

/-- **The surviving star at the `t₂` endpoint over `{e₁'s sheet}`**: the
retained `e₁` and the new occurrence through its sheet.  This is the source's
`A'` of Base II.2.2.M, `|A'| = k₁ = 1`. -/
theorem divided_nonDanglingIncident_unit (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) :
    nonDanglingIncident (DividedData.candidate shape divided).datum
        ((DividedData.candidate shape divided).datum.sourceEndpoint
          (wallSide target wall (sideOf profile.doubleLabel))
          (pinSheet profile profile.doubleLabel)) =
      {(DividedData.candidate shape divided).oldSourceEdge profile.first.1,
        (DividedData.candidate shape divided).newSourceEdge
          (pinSheet profile profile.doubleLabel)} :=
  nonDanglingIncident_pair_of_card_two _ (divided_unit_incident shape divided)
    (newSourceEdge_incident_side _ _ _) (oldSourceEdge_ne_newSourceEdge _ _)
    (ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ profile.first_survives)
    (divided_new_unit_survives input shape divided) (divided_card_unit shape divided)

theorem divided_nonDanglingValency_unit (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) :
    nonDanglingValency (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall (sideOf profile.doubleLabel))
        (pinSheet profile profile.doubleLabel)) = 2 := by
  rw [← card_nonDanglingIncident, divided_nonDanglingIncident_unit input shape divided,
    Finset.card_pair (oldSourceEdge_ne_newSourceEdge _ _)]

/-- **Nothing survives at the `t₃` endpoint over `{e₄'s sheet}`.**  Its two
incidences are the pruned `e₄` and the new occurrence through its sheet. -/
theorem divided_nonDanglingIncident_deleted (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) :
    nonDanglingIncident (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall (sideOf profile.singleLabel))
        (pinSheet profile profile.singleLabel)) = ∅ :=
  nonDanglingIncident_empty_of_card_two _ (divided_deleted_incident shape divided)
    (newSourceEdge_incident_side _ _ _) (oldSourceEdge_ne_newSourceEdge _ _)
    (divided_deleted_dangling input shape divided)
    (divided_new_deleted_dangling input shape divided) (divided_card_deleted shape divided)

theorem divided_nonDanglingValency_deleted (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) :
    nonDanglingValency (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall (sideOf profile.singleLabel))
        (pinSheet profile profile.singleLabel)) = 0 := by
  rw [← card_nonDanglingIncident, divided_nonDanglingIncident_deleted input shape divided,
    Finset.card_empty]

/-- **The surviving star at the `t₂` endpoint over `A₀ ∖ {e₁'s sheet}`**: the
retained `e₂` and the residual new occurrence.  The third incidence, the new
occurrence through `e₄`'s sheet, has been pruned.  This is the source's `A''`,
`|A''| = k₂ = k`, with `|e''| = k - 1`. -/
theorem divided_nonDanglingIncident_pair (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (hNe : sheet ≠ pinSheet profile profile.doubleLabel) :
    nonDanglingIncident (DividedData.candidate shape divided).datum
        ((DividedData.candidate shape divided).datum.sourceEndpoint
          (wallSide target wall (sideOf profile.doubleLabel)) sheet) =
      {(DividedData.candidate shape divided).oldSourceEdge profile.second.1,
        (DividedData.candidate shape divided).newSourceEdge divided.third} := by
  have hSingleNe : pinSheet profile profile.singleLabel ≠
      pinSheet profile profile.doubleLabel := divided_pin_ne divided profile.labels_ne.symm
  have hThirdNe : divided.third ≠ pinSheet profile profile.doubleLabel :=
    divided_third_ne_pin divided _
  refine nonDanglingIncident_pair_of_card_three _
    (divided_pair_incident shape divided sheet hWall hNe)
    (divided_double_endpoint_eq shape divided divided.third sheet divided.rel_third hThirdNe
      hWall hNe ▸ newSourceEdge_incident_side _ (sideOf profile.doubleLabel) divided.third)
    (divided_double_endpoint_eq shape divided (pinSheet profile profile.singleLabel) sheet
      (pin_rel_pin profile 0 profile.singleLabel) hSingleNe hWall hNe ▸
      newSourceEdge_incident_side _ (sideOf profile.doubleLabel)
        (pinSheet profile profile.singleLabel))
    (oldSourceEdge_ne_newSourceEdge _ _) (oldSourceEdge_ne_newSourceEdge _ _)
    (Ne.symm (divided_newSourceEdge_pin_ne shape divided profile.singleLabel divided.third
      (divided_third_ne_pin divided _)))
    (ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ profile.second_survives)
    (divided_new_third_survives input shape divided)
    (divided_new_deleted_dangling input shape divided)
    (divided_card_pair shape divided sheet hWall hNe)

theorem divided_nonDanglingValency_pair (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (hNe : sheet ≠ pinSheet profile profile.doubleLabel) :
    nonDanglingValency (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall (sideOf profile.doubleLabel)) sheet) = 2 := by
  rw [← card_nonDanglingIncident,
    divided_nonDanglingIncident_pair input shape divided sheet hWall hNe,
    Finset.card_pair (oldSourceEdge_ne_newSourceEdge _ _)]

/-- **The `t₃` endpoint over `A₀ ∖ {e₄'s sheet}` is `M⁽²⁾`'s branch vertex.**
All three of its incidences survive: the retained `e₃`, the new occurrence
through `e₁`'s sheet and the residual new occurrence.  This is the source's
`B = A^q`, `|B| = k₃ = k` and `k₃ = |e'| + |e''| = 1 + (k-1)`. -/
theorem divided_nonDanglingIncident_branch (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (hNe : sheet ≠ pinSheet profile profile.singleLabel) :
    nonDanglingIncident (DividedData.candidate shape divided).datum
        ((DividedData.candidate shape divided).datum.sourceEndpoint
          (wallSide target wall (sideOf profile.singleLabel)) sheet) =
      {(DividedData.candidate shape divided).oldSourceEdge profile.third.1,
        (DividedData.candidate shape divided).newSourceEdge
          (pinSheet profile profile.doubleLabel),
        (DividedData.candidate shape divided).newSourceEdge divided.third} := by
  have hDoubleNe : pinSheet profile profile.doubleLabel ≠
      pinSheet profile profile.singleLabel := divided_pin_ne divided profile.labels_ne
  have hThirdNe : divided.third ≠ pinSheet profile profile.singleLabel :=
    divided_third_ne_pin divided _
  refine nonDanglingIncident_triple_of_card_three _
    (divided_single_incident shape divided sheet hWall hNe)
    (divided_single_endpoint_eq shape divided (pinSheet profile profile.doubleLabel) sheet
      (pin_rel_pin profile 0 profile.doubleLabel) hDoubleNe hWall hNe ▸
      newSourceEdge_incident_side _ (sideOf profile.singleLabel)
        (pinSheet profile profile.doubleLabel))
    (divided_single_endpoint_eq shape divided divided.third sheet divided.rel_third hThirdNe
      hWall hNe ▸ newSourceEdge_incident_side _ (sideOf profile.singleLabel) divided.third)
    (oldSourceEdge_ne_newSourceEdge _ _) (oldSourceEdge_ne_newSourceEdge _ _)
    (divided_newSourceEdge_pin_ne shape divided profile.doubleLabel divided.third
      (divided_third_ne_pin divided _))
    (ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ profile.third_survives)
    (divided_new_unit_survives input shape divided)
    (divided_new_third_survives input shape divided)
    (divided_card_single shape divided sheet hWall hNe)

theorem divided_nonDanglingValency_branch (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (hNe : sheet ≠ pinSheet profile profile.singleLabel) :
    nonDanglingValency (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall (sideOf profile.singleLabel)) sheet) = 3 := by
  classical
  rw [← card_nonDanglingIncident,
    divided_nonDanglingIncident_branch input shape divided sheet hWall hNe,
    Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (hEq | hEq)
      · exact oldSourceEdge_ne_newSourceEdge _ _ hEq
      · exact oldSourceEdge_ne_newSourceEdge _ _ hEq),
    Finset.card_pair (divided_newSourceEdge_pin_ne shape divided profile.doubleLabel
      divided.third (divided_third_ne_pin divided _))]

/-! ### The surviving new occurrences' stable rows

Figure 33's `M⁽²⁾` box reads `c⁽²⁾ = c(e₁) + c(e₂)/(k-1) + s`.  The two
surviving new occurrences are the singleton `e'` through `e₁`'s sheet and the
residual `e''` of index `k - 1`; the two identities below say that the first
joins `e₁`'s stable row and the second joins `e₂`'s, which is exactly the
displayed sum.  As everywhere, these are identities of occurrences, not of row
labels: nothing here asserts `e₁`'s and `e₂`'s rows are distinct. -/

/-- The new occurrence through `e₁`'s sheet shares `e₁`'s stable row. -/
theorem divided_new_unit_stablePath_eq (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) :
    NonDanglingEdge.stablePath
        ⟨(DividedData.candidate shape divided).newSourceEdge
            (pinSheet profile profile.doubleLabel),
          divided_new_unit_survives input shape divided⟩ =
      NonDanglingEdge.stablePath
        ⟨(DividedData.candidate shape divided).oldSourceEdge profile.first.1,
          ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
            profile.first_survives⟩ := by
  refine stablePath_eq_of_consecutive ⟨?_, _,
    newSourceEdge_incident_side _ (sideOf profile.doubleLabel) _,
    divided_unit_incident shape divided,
    divided_nonDanglingValency_unit input shape divided⟩
  intro hEqual
  exact oldSourceEdge_ne_newSourceEdge _ _
    (congrArg (fun edge : NonDanglingEdge (DividedData.candidate shape divided).datum ↦
      edge.1) hEqual).symm

/-- The residual new occurrence shares `e₂`'s stable row. -/
theorem divided_new_third_stablePath_eq (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) :
    NonDanglingEdge.stablePath
        ⟨(DividedData.candidate shape divided).newSourceEdge divided.third,
          divided_new_third_survives input shape divided⟩ =
      NonDanglingEdge.stablePath
        ⟨(DividedData.candidate shape divided).oldSourceEdge profile.second.1,
          ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
            profile.second_survives⟩ := by
  have hThirdNe : divided.third ≠ pinSheet profile profile.doubleLabel :=
    divided_third_ne_pin divided _
  refine stablePath_eq_of_consecutive ⟨?_, _,
    newSourceEdge_incident_side _ (sideOf profile.doubleLabel) divided.third,
    divided_pair_incident shape divided divided.third divided.rel_third hThirdNe,
    divided_nonDanglingValency_pair input shape divided divided.third divided.rel_third
      hThirdNe⟩
  intro hEqual
  exact oldSourceEdge_ne_newSourceEdge _ _
    (congrArg (fun edge : NonDanglingEdge (DividedData.candidate shape divided).datum ↦
      edge.1) hEqual).symm

end DividedStars

/-! ## §7  The joined member's endpoint census

`M⁽³⁾` is `joinedCandidate`, Base II.1.M: both endpoints and the new edge keep
the whole wall partition, so each new endpoint over `A₀` carries one new
occurrence and both old occurrences of its own direction.  The argument is
literally M11's (`M11JoinedSurvival`), with `e₄` at the `t₃` endpoint doing the
work.

| endpoint | incidences | surviving | `nd` |
|---|---|---|---|
| `t₂` side over `A₀` | `e₁`, `e₂`, new | 3 | 3 |
| `t₃` side over `A₀` | `e₃`, `e₄`, new | 2 | 2 |

The **branch vertex** of `M⁽³⁾` is therefore on the `t₂` side -- the opposite
side from `M⁽²⁾`'s.
-/

section Joined

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

theorem joined_right (geometry : GlobalM1k.Geometry data wall) (edge : target.edges) :
    (joinedCandidate star geometry).right edge = star.right edge := rfl

theorem joined_right_side (geometry : GlobalM1k.Geometry data wall) (side : Bool) :
    (joinedCandidate star geometry).right (star.edge (sideLabel side)) = side := by
  cases side
  · exact star.right_edge_zero
  · exact star.right_edge_one

theorem joined_resolution (geometry : GlobalM1k.Geometry data wall) (anchor : Fin degree) :
    (joinedCandidate star geometry).resolution anchor =
      thirdResolution (data.vertexPartition wall) := by
  change LocalResolution.onBlock (data.vertexPartition wall) geometry.first
    (thirdResolution (data.vertexPartition wall))
    (fun _ ↦ joinedResolutionAt (data.vertexPartition wall)) anchor = _
  simp only [LocalResolution.onBlock, ite_self]

theorem joined_pastedSide (geometry : GlobalM1k.Geometry data wall) (side : Bool) :
    pastedSide (joinedCandidate star geometry) side = data.vertexPartition wall := by
  cases side
  · apply SheetPartition.ext_repr
    funext sheet
    change ((joinedCandidate star geometry).resolution
      ((data.vertexPartition wall).repr sheet)).left.repr sheet = _
    rw [joined_resolution]
    rfl
  · apply SheetPartition.ext_repr
    funext sheet
    change ((joinedCandidate star geometry).resolution
      ((data.vertexPartition wall).repr sheet)).right.repr sheet = _
    rw [joined_resolution]
    rfl

theorem joined_pasted_newEdge (geometry : GlobalM1k.Geometry data wall) :
    (pasted (joinedCandidate star geometry)).newEdge = data.vertexPartition wall := by
  apply SheetPartition.ext_repr
  funext sheet
  change ((joinedCandidate star geometry).resolution
    ((data.vertexPartition wall).repr sheet)).newEdge.repr sheet = _
  rw [joined_resolution]
  rfl

/-- **Three incidences at either new endpoint over `A₀`**: that direction's
two old occurrences and the one new occurrence. -/
theorem joined_card_incident_side (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) (side : Bool) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    Fintype.card (IncidentSourceEdge (joinedCandidate star geometry).datum
      ((joinedCandidate star geometry).datum.sourceEndpoint
        (wallSide target wall side) sheet)) = 3 := by
  rw [card_incident_side (twoStar := star) (joined_right geometry) side sheet,
    joined_pastedSide, joined_pasted_newEdge, SheetPartition.blockCountWithin_self,
    edgePartition_blockCountWithin shape (sideLabel side) sheet hSheet]

/-- Sheets of `A₀` share both of the joined member's new endpoints. -/
theorem joined_endpoint_eq (geometry : GlobalM1k.Geometry data wall) (side : Bool)
    {first second : Fin degree} (hRel : (data.vertexPartition wall).Rel first second) :
    (joinedCandidate star geometry).datum.sourceEndpoint
        (wallSide target wall side) first =
      (joinedCandidate star geometry).datum.sourceEndpoint
        (wallSide target wall side) second :=
  sourceEndpoint_side_eq_of_rel side (by rw [joined_pastedSide]; exact hRel)

/-- Every old wall occurrence of one direction meets that direction's new
endpoint, over every sheet of `A₀`. -/
theorem joined_old_incident (geometry : GlobalM1k.Geometry data wall) (side : Bool)
    (occurrence : IncidentSourceEdge data (WallBlock.sourceVertex data wall block))
    (hTarget : occurrence.1.1.1 = star.edge (sideLabel side)) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    Incident (joinedCandidate star geometry).datum
      ((joinedCandidate star geometry).oldSourceEdge occurrence.1)
      ((joinedCandidate star geometry).datum.sourceEndpoint
        (wallSide target wall side) sheet) := by
  have hAt : occurrence.1.1.1 ∈ GluingDatum.incidentEdges wall := by
    rw [hTarget]
    exact star.edge_mem_incidentEdges _
  have hRight : (joinedCandidate star geometry).right occurrence.1.1.1 = side := by
    rw [hTarget]
    exact joined_right_side geometry side
  have h := oldSourceEdge_incident_side (joinedCandidate star geometry) occurrence.1.1.1
    hAt side hRight occurrence.1.1.2
  rw [show data.sourceEdge occurrence.1.1.1 occurrence.1.1.2 = occurrence.1 from
    GluingDatum.sourceEdge_self data occurrence.1] at h
  exact joined_endpoint_eq geometry side
    ((M11SplitSurvival.sheet_rel_of_incident_block occurrence).symm.trans hSheet) ▸ h

/-- Genus-preserving pruning keeps `e₄` dangling. -/
theorem joined_deleted_dangling (input : W2SourceInput data star)
    (geometry : GlobalM1k.Geometry data wall) :
    IsDangling (joinedCandidate star geometry).datum
      ((joinedCandidate star geometry).oldSourceEdge profile.deleted.edge.1) :=
  (ResolutionPruning.isDangling_oldSourceEdge_iff _ input.valid
    (joined_sourceGenus geometry) _).mpr profile.deleted.dangling

/-- **The joined new occurrence survives**, by the trivalent argument at the
`t₃` endpoint: `e₃` survives there and `e₄` is pruned. -/
theorem joined_new_survives (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    ¬ IsDangling (joinedCandidate star geometry).datum
      ((joinedCandidate star geometry).newSourceEdge sheet) := by
  have hThirdTarget : profile.third.1.1.1 = star.edge (sideLabel (sideOf profile.singleLabel)) := by
    rw [sideLabel_sideOf]
    exact profile.third_target
  have hDeletedTarget : profile.deleted.edge.1.1.1 =
      star.edge (sideLabel (sideOf profile.singleLabel)) := by
    rw [sideLabel_sideOf]
    exact shape.deleted_single
  refine M11SplitSurvival.survives_of_trivalent_of_deleted _
    (joined_valid input geometry).1 _
    ⟨_, joined_old_incident geometry (sideOf profile.singleLabel) profile.third hThirdTarget
      sheet hSheet⟩
    ⟨_, joined_old_incident geometry (sideOf profile.singleLabel) profile.deleted.edge
      hDeletedTarget sheet hSheet⟩
    ⟨_, newSourceEdge_incident_side _ (sideOf profile.singleLabel) sheet⟩
    (ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ profile.third_survives)
    (joined_deleted_dangling input geometry) ?_
    (joined_card_incident_side shape geometry (sideOf profile.singleLabel) sheet hSheet)
  intro hEqual
  exact oldSourceEdge_ne_newSourceEdge _ _
    (congrArg (fun item : IncidentSourceEdge (joinedCandidate star geometry).datum
      ((joinedCandidate star geometry).datum.sourceEndpoint
        (wallSide target wall (sideOf profile.singleLabel)) sheet) ↦ item.1) hEqual)

/-- **The surviving star at the joined `t₃` endpoint**: the retained `e₃` and
the new occurrence.  `e₄` is pruned. -/
theorem joined_nonDanglingIncident_single (input : W2SourceInput data star)
    (shape : Shape profile) (geometry : GlobalM1k.Geometry data wall) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    nonDanglingIncident (joinedCandidate star geometry).datum
        ((joinedCandidate star geometry).datum.sourceEndpoint
          (wallSide target wall (sideOf profile.singleLabel)) sheet) =
      {(joinedCandidate star geometry).oldSourceEdge profile.third.1,
        (joinedCandidate star geometry).newSourceEdge sheet} := by
  have hThirdTarget : profile.third.1.1.1 = star.edge (sideLabel (sideOf profile.singleLabel)) := by
    rw [sideLabel_sideOf]
    exact profile.third_target
  have hDeletedTarget : profile.deleted.edge.1.1.1 =
      star.edge (sideLabel (sideOf profile.singleLabel)) := by
    rw [sideLabel_sideOf]
    exact shape.deleted_single
  refine nonDanglingIncident_pair_of_card_three _
    (joined_old_incident geometry (sideOf profile.singleLabel) profile.third hThirdTarget
      sheet hSheet)
    (newSourceEdge_incident_side _ (sideOf profile.singleLabel) sheet)
    (joined_old_incident geometry (sideOf profile.singleLabel) profile.deleted.edge
      hDeletedTarget sheet hSheet)
    (oldSourceEdge_ne_newSourceEdge _ _) (fun hEqual ↦ ?_)
    (Ne.symm (oldSourceEdge_ne_newSourceEdge _ _))
    (ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ profile.third_survives)
    (joined_new_survives input shape geometry sheet hSheet)
    (joined_deleted_dangling input geometry)
    (joined_card_incident_side shape geometry (sideOf profile.singleLabel) sheet hSheet)
  have hEdges := ResolutionCut.oldSourceEdge_injective _ hEqual
  have hSurvives : ¬ IsDangling data profile.deleted.edge.1 := hEdges ▸ profile.third_survives
  exact hSurvives profile.deleted.dangling

theorem joined_nonDanglingValency_single (input : W2SourceInput data star)
    (shape : Shape profile) (geometry : GlobalM1k.Geometry data wall) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    nonDanglingValency (joinedCandidate star geometry).datum
      ((joinedCandidate star geometry).datum.sourceEndpoint
        (wallSide target wall (sideOf profile.singleLabel)) sheet) = 2 := by
  rw [← card_nonDanglingIncident,
    joined_nonDanglingIncident_single input shape geometry sheet hSheet,
    Finset.card_pair (oldSourceEdge_ne_newSourceEdge _ _)]

/-- **The joined `t₂` endpoint over `A₀` is `M⁽³⁾`'s branch vertex**: `e₁`,
`e₂` and the new occurrence all survive. -/
theorem joined_nonDanglingIncident_double (input : W2SourceInput data star)
    (shape : Shape profile) (geometry : GlobalM1k.Geometry data wall) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    nonDanglingIncident (joinedCandidate star geometry).datum
        ((joinedCandidate star geometry).datum.sourceEndpoint
          (wallSide target wall (sideOf profile.doubleLabel)) sheet) =
      {(joinedCandidate star geometry).oldSourceEdge profile.first.1,
        (joinedCandidate star geometry).oldSourceEdge profile.second.1,
        (joinedCandidate star geometry).newSourceEdge sheet} := by
  have hFirstTarget : profile.first.1.1.1 = star.edge (sideLabel (sideOf profile.doubleLabel)) := by
    rw [sideLabel_sideOf]
    exact profile.first_target
  have hSecondTarget : profile.second.1.1.1 =
      star.edge (sideLabel (sideOf profile.doubleLabel)) := by
    rw [sideLabel_sideOf]
    exact profile.second_target
  refine nonDanglingIncident_triple_of_card_three _
    (joined_old_incident geometry (sideOf profile.doubleLabel) profile.first hFirstTarget
      sheet hSheet)
    (joined_old_incident geometry (sideOf profile.doubleLabel) profile.second hSecondTarget
      sheet hSheet)
    (newSourceEdge_incident_side _ (sideOf profile.doubleLabel) sheet)
    (fun hEqual ↦ profile.first_ne_second
      (Subtype.ext (ResolutionCut.oldSourceEdge_injective _ hEqual)))
    (oldSourceEdge_ne_newSourceEdge _ _) (oldSourceEdge_ne_newSourceEdge _ _)
    (ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ profile.first_survives)
    (ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ profile.second_survives)
    (joined_new_survives input shape geometry sheet hSheet)
    (joined_card_incident_side shape geometry (sideOf profile.doubleLabel) sheet hSheet)

theorem joined_nonDanglingValency_double (input : W2SourceInput data star)
    (shape : Shape profile) (geometry : GlobalM1k.Geometry data wall) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    nonDanglingValency (joinedCandidate star geometry).datum
      ((joinedCandidate star geometry).datum.sourceEndpoint
        (wallSide target wall (sideOf profile.doubleLabel)) sheet) = 3 := by
  classical
  rw [← card_nonDanglingIncident,
    joined_nonDanglingIncident_double input shape geometry sheet hSheet,
    Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (hEq | hEq)
      · exact profile.first_ne_second (Subtype.ext (ResolutionCut.oldSourceEdge_injective _ hEq))
      · exact oldSourceEdge_ne_newSourceEdge _ _ hEq),
    Finset.card_pair (oldSourceEdge_ne_newSourceEdge _ _)]

/-- **Figure 33's row identity for `M⁽³⁾`**: the single new occurrence, of
index `|A₀| = k + 1`, shares the stable row of the retained `e₃`.  That is the
box `c⁽³⁾ = c(e₃)/(k+1) + s`. -/
theorem joined_new_stablePath_eq_third (input : W2SourceInput data star)
    (shape : Shape profile) (geometry : GlobalM1k.Geometry data wall) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    NonDanglingEdge.stablePath
        ⟨(joinedCandidate star geometry).newSourceEdge sheet,
          joined_new_survives input shape geometry sheet hSheet⟩ =
      NonDanglingEdge.stablePath
        ⟨(joinedCandidate star geometry).oldSourceEdge profile.third.1,
          ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
            profile.third_survives⟩ := by
  have hThirdTarget : profile.third.1.1.1 = star.edge (sideLabel (sideOf profile.singleLabel)) := by
    rw [sideLabel_sideOf]
    exact profile.third_target
  refine stablePath_eq_of_consecutive ⟨?_, _,
    newSourceEdge_incident_side _ (sideOf profile.singleLabel) sheet,
    joined_old_incident geometry (sideOf profile.singleLabel) profile.third hThirdTarget
      sheet hSheet,
    joined_nonDanglingValency_single input shape geometry sheet hSheet⟩
  intro hEqual
  exact oldSourceEdge_ne_newSourceEdge _ _
    (congrArg (fun edge : NonDanglingEdge (joinedCandidate star geometry).datum ↦
      edge.1) hEqual).symm

end Joined

/-! ## §8  The leaf member's trivalent endpoint, and which of its arms survive

The fresh endpoint of `M⁽¹⁾` carries **both** wall directions, so its two
source vertices above `A₀` are read through `LimitChainCore.card_incident_fresh`
with the full wall star, not through the two-star dictionary.  Over the
detached singleton `{x}` it is trivalent (`e₁`, `e₄`, new); over `A₀ ∖ {x}` it
carries `e₂`, `e₃` and all `k` new occurrences, of which only the one through
`pair.second` survives.
-/

section LeafFresh

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

theorem leaf_wallEdgesAssigned (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    wallEdgesAssigned target wall (LeafPair.candidate input shape pair).right true =
      {star.edge 0, star.edge 1} := by
  classical
  have hSet : wallEdgesAssigned target wall (LeafPair.candidate input shape pair).right true =
      GluingDatum.incidentEdges wall := by
    ext edge
    simp only [mem_wallEdgesAssigned, GluingDatum.incidentEdges, Finset.mem_filter,
      Finset.mem_univ, true_and, and_iff_left_iff_imp]
    exact fun _ ↦ rfl
  rw [hSet, incidentEdges_pair star]

theorem leaf_blockCountWithin_right (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (fine : SheetPartition degree) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet) :
    fine.blockCountWithin (pasted (LeafPair.candidate input shape pair)).right sheet =
      fine.blockCountWithin ((data.vertexPartition wall).detachSheet (pinSheet profile 0)
        pair.second pair.ne_second pair.rel_second) sheet := by
  rw [LocalResolution.blockCountWithin_paste_right, leaf_resolution_selected input shape pair _
    (hWall.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  rfl

theorem leaf_newEdge_within_right (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet) :
    (pasted (LeafPair.candidate input shape pair)).newEdge.blockCountWithin
        (pasted (LeafPair.candidate input shape pair)).right sheet =
      ((data.vertexPartition wall).splitBlock (pinSheet profile 0)).blockCountWithin
        ((data.vertexPartition wall).detachSheet (pinSheet profile 0) pair.second
          pair.ne_second pair.rel_second) sheet := by
  rw [LocalResolution.paste_newEdge_blockCountWithin_right,
    leaf_resolution_selected input shape pair _
      (hWall.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  rfl

theorem leaf_pasted_right_rel_iff (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (first second : Fin degree)
    (hFirstWall : (data.vertexPartition wall).Rel (pinSheet profile 0) first) :
    (pasted (LeafPair.candidate input shape pair)).right.Rel first second ↔
      ((data.vertexPartition wall).detachSheet (pinSheet profile 0) pair.second
        pair.ne_second pair.rel_second).Rel first second := by
  show (LocalResolution.pasteRight (data.vertexPartition wall)
    (LeafPair.candidate input shape pair).resolution
    (LeafPair.candidate input shape pair).contracts).Rel first second ↔ _
  unfold LocalResolution.pasteRight
  rw [SheetPartition.paste_rel_iff, leaf_resolution_selected input shape pair _
    (hFirstWall.trans ((data.vertexPartition wall).rel_repr_right first))]
  exact Iff.rfl

theorem leaf_pasted_left_rel (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (first second : Fin degree)
    (hFirstWall : (data.vertexPartition wall).Rel (pinSheet profile 0) first)
    (hRel : ((data.vertexPartition wall).pairBlock (pinSheet profile 0) pair.second
      pair.ne_second).Rel first second) :
    (pasted (LeafPair.candidate input shape pair)).left.Rel first second := by
  show (LocalResolution.pasteLeft (data.vertexPartition wall)
    (LeafPair.candidate input shape pair).resolution
    (LeafPair.candidate input shape pair).contracts).Rel first second
  unfold LocalResolution.pasteLeft
  rw [SheetPartition.paste_rel_iff, leaf_resolution_selected input shape pair _
    (hFirstWall.trans ((data.vertexPartition wall).rel_repr_right first))]
  exact hRel

theorem leaf_pasted_newEdge_rel_iff (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (first second : Fin degree)
    (hFirstWall : (data.vertexPartition wall).Rel (pinSheet profile 0) first) :
    (pasted (LeafPair.candidate input shape pair)).newEdge.Rel first second ↔
      ((data.vertexPartition wall).splitBlock (pinSheet profile 0)).Rel first second := by
  show (LocalResolution.pasteNewEdge (data.vertexPartition wall)
    (LeafPair.candidate input shape pair).resolution
    (LeafPair.candidate input shape pair).contracts).Rel first second ↔ _
  unfold LocalResolution.pasteNewEdge
  rw [SheetPartition.paste_rel_iff, leaf_resolution_selected input shape pair _
    (hFirstWall.trans ((data.vertexPartition wall).rel_repr_right first))]
  exact Iff.rfl

/-- **Three incidences at the trivalent endpoint over the detached singleton
`{x}`**: `e₁`, the dangling `e₄` and the new occurrence through `x`. -/
theorem leaf_card_incident_fresh_pin (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    Fintype.card (IncidentSourceEdge (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).datum.sourceEndpoint
        (freshVertex target) (pinSheet profile 0))) = 3 := by
  classical
  have hSingleton : ((data.vertexPartition wall).detachSheet (pinSheet profile 0)
      pair.second pair.ne_second pair.rel_second).block (pinSheet profile 0) =
      {pinSheet profile 0} :=
    (data.vertexPartition wall).detachSheet_block_single (pinSheet profile 0) pair.second
      pair.ne_second pair.rel_second
  rw [card_incident_fresh (LeafPair.candidate input shape pair) (pinSheet profile 0),
    leaf_wallEdgesAssigned input shape pair,
    Finset.sum_pair (star_edge_zero_ne_one star),
    leaf_newEdge_within_right input shape pair _ rfl,
    leaf_blockCountWithin_right input shape pair (data.edgePartition (star.edge 0)) _ rfl,
    leaf_blockCountWithin_right input shape pair (data.edgePartition (star.edge 1)) _ rfl,
    SheetPartition.blockCountWithin_eq_one_of_block_eq_singleton _ _ _ hSingleton,
    SheetPartition.blockCountWithin_eq_one_of_block_eq_singleton _ _ _ hSingleton,
    SheetPartition.blockCountWithin_eq_one_of_block_eq_singleton _ _ _ hSingleton]
  omega

/-- `e₁` sits above the common pinned sheet. -/
theorem leaf_first_sheet (pair : LeafPair profile) :
    profile.first.1.1.2 = pinSheet profile 0 := by
  have hPin : pinSheet profile profile.doubleLabel = profile.first.1.1.2 :=
    congrArg (fun edge : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall block) ↦ edge.1.1.2) pinnedOccurrence_double
  rw [← hPin, leaf_pinSheet_eq pair]

/-- and so does the dangling `e₄`: that is Base I.a's `k₁ = |A''| = k₄`. -/
theorem leaf_deleted_sheet (pair : LeafPair profile) :
    profile.deleted.edge.1.1.2 = pinSheet profile 0 := by
  have hPin : pinSheet profile profile.singleLabel = profile.deleted.edge.1.1.2 :=
    congrArg (fun edge : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall block) ↦ edge.1.1.2) pinnedOccurrence_single
  rw [← hPin, leaf_pinSheet_eq pair]

/-- Every old wall occurrence of the block reaches the member's trivalent
endpoint over its own sheet. -/
theorem leaf_old_incident_fresh (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile)
    (occurrence : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)) :
    Incident (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).oldSourceEdge occurrence.1)
      ((LeafPair.candidate input shape pair).datum.sourceEndpoint
        (freshVertex target) occurrence.1.1.2) := by
  have hAt : occurrence.1.1.1 ∈ GluingDatum.incidentEdges wall :=
    ((incident_wallBlock_sourceVertex_iff data block occurrence.1).mp occurrence.2).1
  have h := M11SplitSurvival.oldSourceEdge_incident_fresh
    (LeafPair.candidate input shape pair) occurrence.1.1.1 hAt rfl occurrence.1.1.2
  rwa [show data.sourceEdge occurrence.1.1.1 occurrence.1.1.2 = occurrence.1 from
    GluingDatum.sourceEdge_self data occurrence.1] at h

theorem leaf_unit_incident (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    Incident (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).oldSourceEdge profile.first.1)
      ((LeafPair.candidate input shape pair).datum.sourceEndpoint
        (freshVertex target) (pinSheet profile 0)) :=
  leaf_first_sheet pair ▸ leaf_old_incident_fresh input shape pair profile.first

theorem leaf_deleted_incident (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    Incident (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).oldSourceEdge profile.deleted.edge.1)
      ((LeafPair.candidate input shape pair).datum.sourceEndpoint
        (freshVertex target) (pinSheet profile 0)) :=
  leaf_deleted_sheet pair ▸ leaf_old_incident_fresh input shape pair profile.deleted.edge

/-- Genus-preserving pruning keeps `e₄` dangling. -/
theorem leaf_deleted_dangling (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    IsDangling (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).oldSourceEdge profile.deleted.edge.1) :=
  (ResolutionPruning.isDangling_oldSourceEdge_iff _ input.valid
    (leaf_sourceGenus input shape pair) _).mpr profile.deleted.dangling

/-- **The new occurrence through `x` survives**: at the trivalent endpoint over
`{x}` the retained `e₁` survives and `e₄` is pruned. -/
theorem leaf_new_pin_survives (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    ¬ IsDangling (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).newSourceEdge (pinSheet profile 0)) := by
  refine M11SplitSurvival.survives_of_trivalent_of_deleted _
    (leaf_valid input shape pair).1 _
    ⟨_, leaf_unit_incident input shape pair⟩ ⟨_, leaf_deleted_incident input shape pair⟩
    ⟨_, newSourceEdge_incident_fresh _⟩
    (ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ profile.first_survives)
    (leaf_deleted_dangling input shape pair) ?_
    (leaf_card_incident_fresh_pin input shape pair)
  intro hEqual
  exact oldSourceEdge_ne_newSourceEdge _ _
    (congrArg (fun item : IncidentSourceEdge (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).datum.sourceEndpoint
        (freshVertex target) (pinSheet profile 0)) ↦ item.1) hEqual)

/-- The leaf source vertex of the retained pair is shared by both its
sheets. -/
theorem leaf_left_vertex_eq (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    (LeafPair.candidate input shape pair).datum.sourceEndpoint
        (oldVertex target wall) (pinSheet profile 0) =
      (LeafPair.candidate input shape pair).datum.sourceEndpoint
        (oldVertex target wall) pair.second :=
  sourceEndpoint_old_eq_of_rel _ _ (leaf_pasted_left_rel input shape pair _ _ rfl
    (((data.vertexPartition wall).pairBlock_rel_first_iff (pinSheet profile 0) pair.second
      pair.second pair.ne_second pair.rel_second).mpr (Or.inr rfl)))

/-- **The new occurrence through `pair.second` survives**, by propagation
through the divalent leaf source vertex of the retained pair. -/
theorem leaf_new_second_survives (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    ¬ IsDangling (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).newSourceEdge pair.second) :=
  (survives_iff_of_card_two (LeafPair.candidate input shape pair).datum
    (leaf_valid input shape pair).1 _ _ _ (newSourceEdge_incident_old _)
    (leaf_left_vertex_eq input shape pair ▸ newSourceEdge_incident_old _)
    (leaf_card_left_pair input shape pair (pinSheet profile 0) rfl)).mp
    (leaf_new_pin_survives input shape pair)

/-- The two surviving new occurrences are distinct: the member's new edge is
discrete on `A₀`. -/
theorem leaf_newSourceEdge_ne (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    (LeafPair.candidate input shape pair).newSourceEdge (pinSheet profile 0) ≠
      (LeafPair.candidate input shape pair).newSourceEdge pair.second := by
  intro hEqual
  refine pair.ne_second ?_
  have hRel := (leaf_pasted_newEdge_rel_iff input shape pair _ _ rfl).mp
    ((newSourceEdge_eq_iff_rel _ _).mp hEqual)
  exact ((data.vertexPartition wall).splitBlock_rel_anchor_iff (pinSheet profile 0)
    pair.second).mp hRel

end LeafFresh

/-! ## §9  The leaf member's surviving stars and rows

| endpoint | incidences | surviving | `nd` |
|---|---|---|---|
| leaf over `{x, pair.second}` | new(`x`), new(`pair.second`) | 2 | 2 |
| leaf over `{s}`, `s ∈ A₀ ∖ {x, pair.second}` | new(`s`) | 0 | 0 |
| leaf over a background sheet | new(that sheet) | 0 | 0 |
| `v` over `{x}` | `e₁`, `e₄`, new(`x`) | 2 | 2 |
| `v` over `A₀ ∖ {x}` | `e₂`, `e₃`, `k` new occurrences | 3 | 3 |

The last row is the member's **branch vertex**, on the fresh side, and it is
the only endpoint in this file whose incidence count is not `1`, `2` or `3`:
it carries `k + 2` occurrences of which `k - 1` are pruned, so its surviving
star is read by an explicit classification of incidences rather than by one of
`LimitChainCore`'s four readers.
-/

section LeafStars

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- A monovalent source vertex whose one occurrence is pruned has an empty
surviving star.  The `(1, 0)` shape, which `LimitChainCore` §1 does not carry:
no other divalent-wall member produces it. -/
theorem nonDanglingIncident_empty_of_card_one (datum : GluingDatum target degree)
    {vertex : datum.SourceVertex} {edge : datum.SourceEdge}
    (hIncident : Incident datum edge vertex) (hDangles : IsDangling datum edge)
    (hCard : Fintype.card (IncidentSourceEdge datum vertex) = 1) :
    nonDanglingIncident datum vertex = ∅ := by
  classical
  obtain ⟨witness, hUnique⟩ := Fintype.card_eq_one_iff.mp hCard
  ext other
  simp only [mem_nonDanglingIncident, Finset.notMem_empty, iff_false, not_and]
  intro hSurvives hOtherIncident
  have hVal : other = edge := congrArg Subtype.val
    ((hUnique ⟨other, hOtherIncident⟩).trans (hUnique ⟨edge, hIncident⟩).symm)
  exact hSurvives (by rw [hVal]; exact hDangles)

theorem leaf_detach_ne_pin (pair : LeafPair profile) (sheet other : Fin degree)
    (hNe : sheet ≠ pinSheet profile 0)
    (hRel : ((data.vertexPartition wall).detachSheet (pinSheet profile 0) pair.second
      pair.ne_second pair.rel_second).Rel sheet other) : other ≠ pinSheet profile 0 := by
  intro hEq
  refine hNe ?_
  have hMem : sheet ∈ ((data.vertexPartition wall).detachSheet (pinSheet profile 0)
      pair.second pair.ne_second pair.rel_second).block (pinSheet profile 0) :=
    (((data.vertexPartition wall).detachSheet (pinSheet profile 0) pair.second
      pair.ne_second pair.rel_second).mem_block_iff _ _).mpr (hEq ▸ hRel).symm
  rw [(data.vertexPartition wall).detachSheet_block_single (pinSheet profile 0) pair.second
    pair.ne_second pair.rel_second] at hMem
  simpa using hMem

theorem leaf_detach_wall (pair : LeafPair profile) (sheet other : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (hRel : ((data.vertexPartition wall).detachSheet (pinSheet profile 0) pair.second
      pair.ne_second pair.rel_second).Rel sheet other) :
    (data.vertexPartition wall).Rel (pinSheet profile 0) other :=
  hWall.trans (((data.vertexPartition wall).detachSheet_refines (pinSheet profile 0)
    pair.second pair.ne_second pair.rel_second).rel hRel)

/-- Sheets of `A₀ ∖ {x}` share the member's trivalent endpoint. -/
theorem leaf_fresh_vertex_eq (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (first second : Fin degree)
    (hFirstWall : (data.vertexPartition wall).Rel (pinSheet profile 0) first)
    (hFirstNe : first ≠ pinSheet profile 0)
    (hSecondWall : (data.vertexPartition wall).Rel (pinSheet profile 0) second)
    (hSecondNe : second ≠ pinSheet profile 0) :
    (LeafPair.candidate input shape pair).datum.sourceEndpoint (freshVertex target) first =
      (LeafPair.candidate input shape pair).datum.sourceEndpoint (freshVertex target) second :=
  sourceEndpoint_fresh_eq_of_rel _ _
    ((leaf_pasted_right_rel_iff input shape pair first second hFirstWall).mpr
      ((W3ShiftSourceCandidates.detachSheet_rel_remainder (data.vertexPartition wall)
        (pinSheet profile 0) pair.second first pair.ne_second pair.rel_second hFirstWall
        hFirstNe).trans
        (W3ShiftSourceCandidates.detachSheet_rel_remainder (data.vertexPartition wall)
          (pinSheet profile 0) pair.second second pair.ne_second pair.rel_second
          hSecondWall hSecondNe).symm))

/-- `e₂`'s sheet is not the pinned one. -/
theorem leaf_second_sheet_ne (shape : Shape profile) (pair : LeafPair profile) :
    profile.second.1.1.2 ≠ pinSheet profile 0 := by
  have hBulk : bulkSheet profile profile.doubleLabel = profile.second.1.1.2 :=
    congrArg (fun edge : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall block) ↦ edge.1.1.2) bulkOccurrence_double
  have h := bulkSheet_ne_pinSheet shape profile.doubleLabel
  rw [leaf_pinSheet_eq pair, hBulk] at h
  exact h

/-- and neither is `e₃`'s. -/
theorem leaf_third_sheet_ne (shape : Shape profile) (pair : LeafPair profile) :
    profile.third.1.1.2 ≠ pinSheet profile 0 := by
  have hBulk : bulkSheet profile profile.singleLabel = profile.third.1.1.2 :=
    congrArg (fun edge : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall block) ↦ edge.1.1.2) bulkOccurrence_single
  have h := bulkSheet_ne_pinSheet shape profile.singleLabel
  rw [leaf_pinSheet_eq pair, hBulk] at h
  exact h

theorem leaf_second_incident (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (hNe : sheet ≠ pinSheet profile 0) :
    Incident (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).oldSourceEdge profile.second.1)
      ((LeafPair.candidate input shape pair).datum.sourceEndpoint
        (freshVertex target) sheet) :=
  leaf_fresh_vertex_eq input shape pair profile.second.1.1.2 sheet
    ((pinSheet_rel 0).symm.trans (M11SplitSurvival.sheet_rel_of_incident_block profile.second))
    (leaf_second_sheet_ne shape pair) hWall hNe ▸
    leaf_old_incident_fresh input shape pair profile.second

theorem leaf_third_incident (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (hNe : sheet ≠ pinSheet profile 0) :
    Incident (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).oldSourceEdge profile.third.1)
      ((LeafPair.candidate input shape pair).datum.sourceEndpoint
        (freshVertex target) sheet) :=
  leaf_fresh_vertex_eq input shape pair profile.third.1.1.2 sheet
    ((pinSheet_rel 0).symm.trans (M11SplitSurvival.sheet_rel_of_incident_block profile.third))
    (leaf_third_sheet_ne shape pair) hWall hNe ▸
    leaf_old_incident_fresh input shape pair profile.third

theorem leaf_new_second_incident (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (hNe : sheet ≠ pinSheet profile 0) :
    Incident (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).newSourceEdge pair.second)
      ((LeafPair.candidate input shape pair).datum.sourceEndpoint
        (freshVertex target) sheet) :=
  leaf_fresh_vertex_eq input shape pair pair.second sheet pair.rel_second
    (Ne.symm pair.ne_second) hWall hNe ▸ newSourceEdge_incident_fresh _

/-- `e₁` and `e₄` are different occurrences: one survives and the other does
not. -/
theorem leaf_unit_ne_deleted (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    (LeafPair.candidate input shape pair).oldSourceEdge profile.first.1 ≠
      (LeafPair.candidate input shape pair).oldSourceEdge profile.deleted.edge.1 := by
  intro hEqual
  exact profile.first_survives
    (ResolutionCut.oldSourceEdge_injective _ hEqual ▸ profile.deleted.dangling)

theorem leaf_second_ne_third (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    (LeafPair.candidate input shape pair).oldSourceEdge profile.second.1 ≠
      (LeafPair.candidate input shape pair).oldSourceEdge profile.third.1 := by
  intro hEqual
  have hTargets := congrArg (fun edge : data.SourceEdge ↦ edge.1.1)
    (ResolutionCut.oldSourceEdge_injective _ hEqual)
  rw [profile.second_target, profile.third_target] at hTargets
  exact profile.labels_ne (star.edge_injective hTargets)

/-- **The surviving star at the leaf source vertex of the retained pair**: both
new occurrences, each of index one.  Base I.a's `A_u` with `e'`, `e''`. -/
theorem leaf_nonDanglingIncident_left_pair (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile) :
    nonDanglingIncident (LeafPair.candidate input shape pair).datum
        ((LeafPair.candidate input shape pair).datum.sourceEndpoint
          (oldVertex target wall) (pinSheet profile 0)) =
      {(LeafPair.candidate input shape pair).newSourceEdge (pinSheet profile 0),
        (LeafPair.candidate input shape pair).newSourceEdge pair.second} :=
  nonDanglingIncident_pair_of_card_two _ (newSourceEdge_incident_old _)
    (leaf_left_vertex_eq input shape pair ▸ newSourceEdge_incident_old _)
    (leaf_newSourceEdge_ne input shape pair) (leaf_new_pin_survives input shape pair)
    (leaf_new_second_survives input shape pair)
    (leaf_card_left_pair input shape pair (pinSheet profile 0) rfl)

theorem leaf_nonDanglingValency_left_pair (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile) :
    nonDanglingValency (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).datum.sourceEndpoint
        (oldVertex target wall) (pinSheet profile 0)) = 2 := by
  rw [← card_nonDanglingIncident, leaf_nonDanglingIncident_left_pair input shape pair,
    Finset.card_pair (leaf_newSourceEdge_ne input shape pair)]

/-- **The other leaf source vertices over `A₀` are entirely pruned.** -/
theorem leaf_nonDanglingIncident_left_singleton (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (hNeFirst : sheet ≠ pinSheet profile 0) (hNeSecond : sheet ≠ pair.second) :
    nonDanglingIncident (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).datum.sourceEndpoint
        (oldVertex target wall) sheet) = ∅ :=
  nonDanglingIncident_empty_of_card_one _ (newSourceEdge_incident_old _)
    (leaf_new_singleton_dangling input shape pair sheet hWall hNeFirst hNeSecond)
    (leaf_card_left_singleton input shape pair sheet hWall hNeFirst hNeSecond)

/-- **And so is every background leaf source vertex.** -/
theorem leaf_nonDanglingIncident_left_background (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel (pinSheet profile 0) sheet) :
    nonDanglingIncident (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).datum.sourceEndpoint
        (oldVertex target wall) sheet) = ∅ :=
  nonDanglingIncident_empty_of_card_one _ (newSourceEdge_incident_old _)
    (leaf_new_background_dangling input shape pair sheet hBackground)
    (leaf_card_left_background input shape pair sheet hBackground)

/-- **The surviving star at the trivalent endpoint over `{x}`**: the retained
`e₁` and the new occurrence through `x`.  `e₄` is pruned.  This is Base I.a's
`A''`, `|A''| = k₁ = k₄ = 1`. -/
theorem leaf_nonDanglingIncident_fresh_pin (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile) :
    nonDanglingIncident (LeafPair.candidate input shape pair).datum
        ((LeafPair.candidate input shape pair).datum.sourceEndpoint
          (freshVertex target) (pinSheet profile 0)) =
      {(LeafPair.candidate input shape pair).oldSourceEdge profile.first.1,
        (LeafPair.candidate input shape pair).newSourceEdge (pinSheet profile 0)} :=
  nonDanglingIncident_pair_of_card_three _ (leaf_unit_incident input shape pair)
    (newSourceEdge_incident_fresh _) (leaf_deleted_incident input shape pair)
    (oldSourceEdge_ne_newSourceEdge _ _) (leaf_unit_ne_deleted input shape pair)
    (Ne.symm (oldSourceEdge_ne_newSourceEdge _ _))
    (ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ profile.first_survives)
    (leaf_new_pin_survives input shape pair) (leaf_deleted_dangling input shape pair)
    (leaf_card_incident_fresh_pin input shape pair)

theorem leaf_nonDanglingValency_fresh_pin (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile) :
    nonDanglingValency (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).datum.sourceEndpoint
        (freshVertex target) (pinSheet profile 0)) = 2 := by
  rw [← card_nonDanglingIncident, leaf_nonDanglingIncident_fresh_pin input shape pair,
    Finset.card_pair (oldSourceEdge_ne_newSourceEdge _ _)]

/-- **The trivalent endpoint over `A₀ ∖ {x}` is `M⁽¹⁾`'s branch vertex.**  Of
its `k + 2` incidences -- `e₂`, `e₃` and the `k` new occurrences through the
sheets of `A₀ ∖ {x}` -- exactly three survive: `e₂`, `e₃` and the new
occurrence through `pair.second`.  The other `k - 1` new arms were pruned at
the target leaf.  This is Base I.a's `A'`, `k₂ = |A'| = k₃ = k`. -/
theorem leaf_nonDanglingIncident_fresh_branch (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (hNe : sheet ≠ pinSheet profile 0) :
    nonDanglingIncident (LeafPair.candidate input shape pair).datum
        ((LeafPair.candidate input shape pair).datum.sourceEndpoint
          (freshVertex target) sheet) =
      {(LeafPair.candidate input shape pair).oldSourceEdge profile.second.1,
        (LeafPair.candidate input shape pair).oldSourceEdge profile.third.1,
        (LeafPair.candidate input shape pair).newSourceEdge pair.second} := by
  classical
  have hBlockRel : (data.vertexPartition wall).Rel block.1 sheet := (pinSheet_rel 0).trans hWall
  ext edge
  simp only [mem_nonDanglingIncident, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hSurvives, hIncident⟩
    rcases ResolutionPruning.sourceEdge_cases (LeafPair.candidate input shape pair) edge with
      ⟨old, rfl⟩ | ⟨other, rfl⟩
    · have hInfo := old_incident_fresh_selected_info (LeafPair.candidate input shape pair)
        block sheet hBlockRel old hIncident
      have hOldSurvives : ¬ IsDangling data old := fun hDangling ↦ hSurvives
        ((ResolutionPruning.isDangling_oldSourceEdge_iff _ input.valid
          (leaf_sourceGenus input shape pair) old).mpr hDangling)
      have hOldSheetNe : old.1.2 ≠ pinSheet profile 0 :=
        leaf_detach_ne_pin pair sheet old.1.2 hNe
          ((leaf_pasted_right_rel_iff input shape pair sheet old.1.2 hWall).mp
            (old_incident_fresh_sheet_rel (LeafPair.candidate input shape pair) sheet old
              hIncident))
      rcases profile.exhaustive ⟨old, hInfo.1⟩ with hEq | hEq | hEq | hEq
      · exact absurd ((congrArg (fun item : IncidentSourceEdge data
          (WallBlock.sourceVertex data wall block) ↦ item.1.1.2) hEq).trans
          (leaf_first_sheet pair)) hOldSheetNe
      · exact Or.inl (congrArg (fun item : IncidentSourceEdge data
          (WallBlock.sourceVertex data wall block) ↦
            (LeafPair.candidate input shape pair).oldSourceEdge item.1) hEq)
      · exact Or.inr (Or.inl (congrArg (fun item : IncidentSourceEdge data
          (WallBlock.sourceVertex data wall block) ↦
            (LeafPair.candidate input shape pair).oldSourceEdge item.1) hEq))
      · exact absurd ((congrArg (fun item : IncidentSourceEdge data
          (WallBlock.sourceVertex data wall block) ↦ item.1.1.2) hEq).trans
          (leaf_deleted_sheet pair)) hOldSheetNe
    · have hDetach := (leaf_pasted_right_rel_iff input shape pair sheet other hWall).mp
        (new_incident_fresh_sheet_rel (LeafPair.candidate input shape pair) sheet other
          hIncident)
      have hOtherNe : other ≠ pinSheet profile 0 :=
        leaf_detach_ne_pin pair sheet other hNe hDetach
      have hOtherWall : (data.vertexPartition wall).Rel (pinSheet profile 0) other :=
        leaf_detach_wall pair sheet other hWall hDetach
      by_cases hSecond : other = pair.second
      · exact Or.inr (Or.inr (by rw [hSecond]))
      · exact absurd (leaf_new_singleton_dangling input shape pair other hOtherWall
          hOtherNe hSecond) hSurvives
  · rintro (rfl | rfl | rfl)
    · exact ⟨ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
        profile.second_survives, leaf_second_incident input shape pair sheet hWall hNe⟩
    · exact ⟨ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
        profile.third_survives, leaf_third_incident input shape pair sheet hWall hNe⟩
    · exact ⟨leaf_new_second_survives input shape pair,
        leaf_new_second_incident input shape pair sheet hWall hNe⟩

theorem leaf_nonDanglingValency_fresh_branch (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (hNe : sheet ≠ pinSheet profile 0) :
    nonDanglingValency (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).datum.sourceEndpoint
        (freshVertex target) sheet) = 3 := by
  classical
  rw [← card_nonDanglingIncident,
    leaf_nonDanglingIncident_fresh_branch input shape pair sheet hWall hNe,
    Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (hEq | hEq)
      · exact leaf_second_ne_third input shape pair hEq
      · exact oldSourceEdge_ne_newSourceEdge _ _ hEq),
    Finset.card_pair (oldSourceEdge_ne_newSourceEdge _ _)]

/-! ### The surviving new occurrences' stable rows

Figure 33's `M⁽¹⁾` box reads `σ¹(J₀,1) = σ¹(J₁,1) = 0` and `c⁽¹⁾ = 2c(e₁)`.
Both surviving new occurrences have index one -- that is the vanishing of the
two `σ`'s -- and both join `e₁`'s stable row, which is the factor two. -/

/-- The new occurrence through `x` shares `e₁`'s stable row. -/
theorem leaf_new_pin_stablePath_eq (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    NonDanglingEdge.stablePath
        ⟨(LeafPair.candidate input shape pair).newSourceEdge (pinSheet profile 0),
          leaf_new_pin_survives input shape pair⟩ =
      NonDanglingEdge.stablePath
        ⟨(LeafPair.candidate input shape pair).oldSourceEdge profile.first.1,
          ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
            profile.first_survives⟩ := by
  refine stablePath_eq_of_consecutive ⟨?_, _, newSourceEdge_incident_fresh _,
    leaf_unit_incident input shape pair,
    leaf_nonDanglingValency_fresh_pin input shape pair⟩
  intro hEqual
  exact oldSourceEdge_ne_newSourceEdge _ _
    (congrArg (fun edge : NonDanglingEdge (LeafPair.candidate input shape pair).datum ↦
      edge.1) hEqual).symm

/-- **So does the new occurrence through `pair.second`**: the two meet at the
divalent leaf source vertex of the retained pair.  Hence `c⁽¹⁾ = 2c(e₁)`. -/
theorem leaf_new_second_stablePath_eq (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    NonDanglingEdge.stablePath
        ⟨(LeafPair.candidate input shape pair).newSourceEdge pair.second,
          leaf_new_second_survives input shape pair⟩ =
      NonDanglingEdge.stablePath
        ⟨(LeafPair.candidate input shape pair).oldSourceEdge profile.first.1,
          ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
            profile.first_survives⟩ :=
  (M11SplitRows.stablePath_eq_of_incident_card_two _ (leaf_valid input shape pair).1
    ⟨_, leaf_new_second_survives input shape pair⟩
    ⟨_, leaf_new_pin_survives input shape pair⟩
    ((LeafPair.candidate input shape pair).datum.sourceEndpoint
      (oldVertex target wall) (pinSheet profile 0))
    (leaf_left_vertex_eq input shape pair ▸ newSourceEdge_incident_old _)
    (newSourceEdge_incident_old _)
    (leaf_card_left_pair input shape pair (pinSheet profile 0) rfl)).trans
    (leaf_new_pin_stablePath_eq input shape pair)

end LeafStars

/-! ## §10  The background census

Away from `A₀` both divalent members install `M11SourceCandidates.joinedBackground`'s
own star, `ResolutionM11.joinedResolutionAt`, which retains the whole wall
block at both endpoints and along the new edge.  Every other wall block has
local ramification zero (`W2RankObstructions.other_localRamification_eq_zero`
applied to `profile.ramification`), so each direction contributes exactly one
occurrence there and each background new endpoint is divalent: the new
occurrence is a *subdivision* of the old block, dangling exactly when the old
occurrence in that direction dangles, and sharing its stable row when it
survives.

The leaf member is different, and that difference is `W2M1kLeaves`: its
background
endpoints on the retained side are **source leaves**, so all of its background
new occurrences are pruned (`leaf_new_background_dangling`).
-/

section Background

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- Every wall block other than `A₀` has vanishing local ramification.  Local
copy of `M11JoinedBackground.background_ramification_zero`; it belongs
naturally in `W2RankObstructions`, beside `other_localRamification_eq_zero`. -/
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

theorem background_repr (profile : W2R2SourceProfile.SourceProfile data star block)
    (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel block.1 sheet) :
    ¬(data.vertexPartition wall).Rel (pinSheet profile 0)
      ((data.vertexPartition wall).repr sheet) := by
  intro hRel
  exact hBackground
    (((pinSheet_rel 0).trans hRel).trans ((data.vertexPartition wall).rel_repr_left sheet))

/-- The same-sheet occurrence of the direction assigned to one side meets that
side's new endpoint. -/
theorem sameSheet_incident_side (candidate : BalancedGlobal.Candidate target degree data wall)
    (side : Bool) (hRight : candidate.right (star.edge (sideLabel side)) = side)
    (sheet : Fin degree) :
    Incident candidate.datum
      (candidate.oldSourceEdge (data.sourceEdge (star.edge (sideLabel side)) sheet))
      (candidate.datum.sourceEndpoint (wallSide target wall side) sheet) :=
  oldSourceEdge_incident_side candidate _ (star.edge_mem_incidentEdges _) side hRight sheet

/-! ### The divided member off `A₀` -/

theorem divided_background_resolution (shape : Shape profile) (divided : DividedData profile)
    (anchor : Fin degree)
    (hAnchor : ¬(data.vertexPartition wall).Rel (pinSheet profile 0) anchor) :
    (DividedData.candidate shape divided).resolution anchor =
      joinedResolutionAt (data.vertexPartition wall) := by
  change LocalResolution.onBlock (data.vertexPartition wall) (pinSheet profile 0) _
    (fun _ ↦ joinedResolutionAt (data.vertexPartition wall)) anchor = _
  rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hAnchor]

/-- **Both background new endpoints of `M⁽²⁾` are divalent.** -/
theorem divided_card_incident_background (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) (side : Bool) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel block.1 sheet) :
    Fintype.card (IncidentSourceEdge (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall side) sheet)) = 2 := by
  have hRes := divided_background_resolution shape divided _ (background_repr profile sheet
    hBackground)
  rw [card_incident_side (twoStar := star) (divided_right shape divided) side sheet]
  cases side
  · show (pasted (DividedData.candidate shape divided)).newEdge.blockCountWithin
        (pasted (DividedData.candidate shape divided)).left sheet +
      (data.edgePartition (star.edge 0)).blockCountWithin
        (pasted (DividedData.candidate shape divided)).left sheet = 2
    rw [LocalResolution.paste_newEdge_blockCountWithin_left, hRes,
      LocalResolution.blockCountWithin_paste_left, hRes]
    simp only [joinedResolutionAt, SheetPartition.blockCountWithin_self,
      background_blockCount_local input profile 0 sheet hBackground]
  · show (pasted (DividedData.candidate shape divided)).newEdge.blockCountWithin
        (pasted (DividedData.candidate shape divided)).right sheet +
      (data.edgePartition (star.edge 1)).blockCountWithin
        (pasted (DividedData.candidate shape divided)).right sheet = 2
    rw [LocalResolution.paste_newEdge_blockCountWithin_right, hRes,
      LocalResolution.blockCountWithin_paste_right, hRes]
    simp only [joinedResolutionAt, SheetPartition.blockCountWithin_self,
      background_blockCount_local input profile 1 sheet hBackground]

/-- Old occurrences of `M⁽²⁾` dangle exactly when they did downstairs. -/
theorem divided_old_isDangling_iff (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (edge : data.SourceEdge) :
    IsDangling (DividedData.candidate shape divided).datum
        ((DividedData.candidate shape divided).oldSourceEdge edge) ↔ IsDangling data edge :=
  ResolutionPruning.isDangling_oldSourceEdge_iff _ input.valid
    (divided_sourceGenus shape divided) _

/-- **A background new occurrence of `M⁽²⁾` is a subdivision**: it dangles
exactly when the same-sheet old occurrence of either direction does. -/
theorem divided_background_survives_iff (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) (side : Bool) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel block.1 sheet) :
    (¬ IsDangling (DividedData.candidate shape divided).datum
        ((DividedData.candidate shape divided).newSourceEdge sheet)) ↔
      ¬ IsDangling data (data.sourceEdge (star.edge (sideLabel side)) sheet) :=
  (survives_iff_of_card_two (DividedData.candidate shape divided).datum
    (divided_valid input shape divided).1 _ _ _
    (newSourceEdge_incident_side _ side sheet)
    (sameSheet_incident_side _ side (divided_right_side shape divided side) sheet)
    (divided_card_incident_background input shape divided side sheet hBackground)).trans
    (not_congr (divided_old_isDangling_iff input shape divided _))

/-- A surviving background new occurrence of `M⁽²⁾` shares the stable row of
the same-sheet old occurrence. -/
theorem divided_background_stablePath_eq (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) (side : Bool) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel block.1 sheet)
    (hOld : ¬ IsDangling data (data.sourceEdge (star.edge (sideLabel side)) sheet)) :
    NonDanglingEdge.stablePath
        ⟨(DividedData.candidate shape divided).newSourceEdge sheet,
          (divided_background_survives_iff input shape divided side sheet
            hBackground).mpr hOld⟩ =
      NonDanglingEdge.stablePath
        ⟨(DividedData.candidate shape divided).oldSourceEdge
            (data.sourceEdge (star.edge (sideLabel side)) sheet),
          ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ hOld⟩ := by
  refine stablePath_eq_of_consecutive ⟨?_, _, newSourceEdge_incident_side _ side sheet,
    sameSheet_incident_side _ side (divided_right_side shape divided side) sheet, ?_⟩
  · intro hEqual
    exact oldSourceEdge_ne_newSourceEdge _ _
      (congrArg (fun edge : NonDanglingEdge (DividedData.candidate shape divided).datum ↦
        edge.1) hEqual).symm
  · exact nonDanglingValency_eq_two_of_card_two_of_survives _
      (divided_valid input shape divided).1 _ _ (newSourceEdge_incident_side _ side sheet)
      ((divided_background_survives_iff input shape divided side sheet hBackground).mpr hOld)
      (divided_card_incident_background input shape divided side sheet hBackground)

/-! ### The joined member off `A₀` -/

/-- **Both background new endpoints of `M⁽³⁾` are divalent.** -/
theorem joined_card_incident_background (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (geometry : GlobalM1k.Geometry data wall) (side : Bool) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel block.1 sheet) :
    Fintype.card (IncidentSourceEdge (joinedCandidate star geometry).datum
      ((joinedCandidate star geometry).datum.sourceEndpoint
        (wallSide target wall side) sheet)) = 2 := by
  rw [card_incident_side (twoStar := star) (joined_right geometry) side sheet,
    joined_pastedSide, joined_pasted_newEdge, SheetPartition.blockCountWithin_self,
    background_blockCount_local input profile (sideLabel side) sheet hBackground]

/-- Old occurrences of `M⁽³⁾` dangle exactly when they did downstairs. -/
theorem joined_old_isDangling_iff (input : W2SourceInput data star)
    (geometry : GlobalM1k.Geometry data wall) (edge : data.SourceEdge) :
    IsDangling (joinedCandidate star geometry).datum
        ((joinedCandidate star geometry).oldSourceEdge edge) ↔ IsDangling data edge :=
  ResolutionPruning.isDangling_oldSourceEdge_iff _ input.valid (joined_sourceGenus geometry) _

/-- **A background new occurrence of `M⁽³⁾` is a subdivision.** -/
theorem joined_background_survives_iff (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (geometry : GlobalM1k.Geometry data wall) (side : Bool) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel block.1 sheet) :
    (¬ IsDangling (joinedCandidate star geometry).datum
        ((joinedCandidate star geometry).newSourceEdge sheet)) ↔
      ¬ IsDangling data (data.sourceEdge (star.edge (sideLabel side)) sheet) :=
  (survives_iff_of_card_two (joinedCandidate star geometry).datum
    (joined_valid input geometry).1 _ _ _ (newSourceEdge_incident_side _ side sheet)
    (sameSheet_incident_side _ side (joined_right_side geometry side) sheet)
    (joined_card_incident_background input profile geometry side sheet hBackground)).trans
    (not_congr (joined_old_isDangling_iff input geometry _))

/-- A surviving background new occurrence of `M⁽³⁾` shares the stable row of
the same-sheet old occurrence. -/
theorem joined_background_stablePath_eq (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (geometry : GlobalM1k.Geometry data wall) (side : Bool) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel block.1 sheet)
    (hOld : ¬ IsDangling data (data.sourceEdge (star.edge (sideLabel side)) sheet)) :
    NonDanglingEdge.stablePath
        ⟨(joinedCandidate star geometry).newSourceEdge sheet,
          (joined_background_survives_iff input profile geometry side sheet
            hBackground).mpr hOld⟩ =
      NonDanglingEdge.stablePath
        ⟨(joinedCandidate star geometry).oldSourceEdge
            (data.sourceEdge (star.edge (sideLabel side)) sheet),
          ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ hOld⟩ := by
  refine stablePath_eq_of_consecutive ⟨?_, _, newSourceEdge_incident_side _ side sheet,
    sameSheet_incident_side _ side (joined_right_side geometry side) sheet, ?_⟩
  · intro hEqual
    exact oldSourceEdge_ne_newSourceEdge _ _
      (congrArg (fun edge : NonDanglingEdge (joinedCandidate star geometry).datum ↦
        edge.1) hEqual).symm
  · exact nonDanglingValency_eq_two_of_card_two_of_survives _
      (joined_valid input geometry).1 _ _ (newSourceEdge_incident_side _ side sheet)
      ((joined_background_survives_iff input profile geometry side sheet hBackground).mpr hOld)
      (joined_card_incident_background input profile geometry side sheet hBackground)

/-! ### The leaf member off `A₀` -/

/-- Old occurrences of `M⁽¹⁾` dangle exactly when they did downstairs.  With
`leaf_new_background_dangling` and `leaf_nonDanglingIncident_left_background`
this completes the member's background census: every background new occurrence
is pruned, and every background *old* occurrence keeps the verdict it had on
the incoming datum. -/
theorem leaf_old_isDangling_iff (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (edge : data.SourceEdge) :
    IsDangling (LeafPair.candidate input shape pair).datum
        ((LeafPair.candidate input shape pair).oldSourceEdge edge) ↔ IsDangling data edge :=
  ResolutionPruning.isDangling_oldSourceEdge_iff _ input.valid
    (leaf_sourceGenus input shape pair) _

end Background

end DraismaVargas.LocalCases.W2M1kStableGraph
