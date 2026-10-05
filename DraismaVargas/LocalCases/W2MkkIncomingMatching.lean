module

public import DraismaVargas.LocalCases.W2MkkIncomingCensus

@[expose] public section

/-!
# Identifying the incoming `w2Mkk` datum with a named Figure 34 member

Source: Draisma--Vargas Part I, case `{w2-r2-nd3-M-kk}` and Figure 34.

`W2MkkIncomingCensus` handles the target side: Base I is precluded, the
placement exists, the retained end of every member restores `doubleEnd` and its
fresh end `singleEnd`, and the `r = 0` background census is symmetric at a `T_2`
W2 wall.  This module does the wall comparison and the whole-cover assembly, and
exits with the normalization receipt the arbitrary-incoming exit consumes.

## The one thing `IncomingMatchingCore` does not cover, and why

`IncomingMatchingCore.wall_blocks_of_dictionary` takes

```
hURefines : (data.vertexPartition u).Refines (mergedPartition data a b)
hUJoined  : JoinedOnBlock (data.vertexPartition u) (mergedPartition data a b) root
```

and concludes, on the distinguished class, that `u` carries the *whole* block --
which the member must then carry too (`hLeftSelected` compares the member's
retained end with `mergedPartition`).  That is **Base II.1** (Part I, Case
`{w2-r2}`): the ends of `e₁`, `e₂` above `u` are the same vertex of `ndG(A₀)`,
so `M⁽³⁾`'s `u` is joined on `A₀`.

**Base II.2 is not of that shape.**  There `ndG(A₀)` has three vertices: the
ends `A'`, `A''` of `e₁`, `e₂` above `u` and the end `B` of `e₃` above `v`.
So `M⁽¹⁾` and `M⁽²⁾` split `A₀` at `u` into `e₁` and `e₂`
(`W2MkkSourceCandidates.DetachData.selected_left` is literally
`endpointPartition profile`), and split it at `v` and along the new edge as well
(`selected_right`, `selected_newEdge` are `detachSheet`s).  No restored endpoint
of a detaching member carries the whole distinguished block, so
`wall_blocks_of_dictionary` does not apply to two of Figure 34's three members.

`wall_blocks_of_split_dictionary` below is the symmetric statement: all three
selected-class comparisons are against *named* partitions, none of them forced
to be `mergedPartition`.  It has one hypothesis fewer than the core's (no
`hURefines`) and a shorter proof, and the core's H is its special case
`selectedLeft := mergedPartition` together with `hURefines`/`hUJoined`.
`IncomingMatchingCore.block_eq_of_anchored_dictionary` generalizes both.

## What is proved, and what is assumed

Proved outright: the six block-dictionary facts of each of the two Figure 34
members that live over the incoming datum (§2), from `W2MkkStableGraph`'s
`detach_resolution` / `joined_resolution` and `W2MkkStableLift`'s background
shapes; the three wall comparisons (§4); the whole-cover `SameBlocks`
exhaustion (§5), by `W3Nd2IncomingMemberMatching.sameBlocks_of_wall_blocks`;
the normalization receipts and the indexed member exit (§6), by
`IncomingMatchingCore.exists_member_normalization_of_family` at `n = 2`.

Assumed here, and named rather than hidden: `SelectedCensus`, the
**selected-class** half of the source census -- what the incoming cover's two
restored endpoints and contracted occurrence look like on `A₀`.  That is the
Base II.1 / Base II.2 analysis of Part I, Case `{w2-r2}`, and it is the
irreducibly per-case part of every incoming instance (compare
`W3Nd3IncomingCensus.selected_fibre_census_of_shared` and
`M11IncomingSelectedCases`).  It is *not* re-derivable from anything in this
chain: `W2MkkStableGraph` is the outgoing survival census, and says what each
member's own source graph looks like, never what an arbitrary incoming cover's
does.  `W2MkkSelectedCensus` proves it.

`SelectedCensus` is stated once, parametrically in the three selected-class
partitions, so that `joinedSelected` (Base II.1) and `detachSelected`
(Base II.2) are two instantiations of one statement rather than two censuses.
`exists_member_normalization` takes the dichotomy `Base II.1 ∨ Base II.2` as its
hypothesis, which is exactly what Part I asserts in Case `{w2-r2}`: `ndG(A₀)`
has either one edge `e'` or two edges `e'`, `e''`.

## The third member is remote and does not appear here

`W2MkkSourceCandidates.no_common_geometry` forbids putting Figure 34's two
detaching members over one datum, so of the three Figure 34 positions only two
live over the incoming datum: the detaching member the datum carries (`M⁽¹⁾`
or `M⁽²⁾`, whichever `W2MkkSourceCandidates.pinSheet_mem` selects) and `M⁽³⁾`.
`IncomingMatchingCore.exists_member_normalization_of_family` asks for
`C : Fin n → BalancedGlobal.Candidate (contract …) degree (contractDatum …)
⟨a, hab⟩`, a single-datum family, so the remote slot cannot enter it: the remote
member is a `Candidate` over `W2MkkTransport.swapRelabeling …|>.apply`, a
different gluing datum of the same target.  `n = 2` here is therefore not a
weakening of Figure 34 -- it is the largest single-datum family the case has.
What the remote slot would need is recorded in `W2MkkArbitraryExit`, where the
three members are assembled as a `BalancedGlobal.GaugeFamily` instead.
-/

namespace DraismaVargas.LocalCases.W2MkkIncomingMatching

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionRamification
open TargetExpansion ResolutionM11 FullDimensionalSource WallDegeneration
open W4Assembly W4StableSource W2R1Target SecondEquation
open M11IncomingPartitions
open W2MkkSourceCandidates
open IncomingMatchingCore
open W3Nd2IncomingMemberMatching (pasted NormalizedAgainst normalizedAgainst
  sameBlocks_of_wall_blocks)
open W2MkkIncomingCensus

/-! ## §1  The symmetric three-position wall comparison

`IncomingMatchingCore.block_eq_of_anchored_dictionary` is the general form. -/

section Split

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}

/-- **The three wall comparisons of one member, with no endpoint assumed
joined.**  `IncomingMatchingCore.wall_blocks_of_dictionary`'s
`hURefines`/`hUJoined` pair is replaced by a named selected-class partition at
`u`, exactly as the other two positions already have one.  Taking
`selectedLeft := mergedPartition data a b` and supplying `hUSelected` from
`hURefines`/`hUJoined` recovers the core's statement. -/
theorem wall_blocks_of_split_dictionary
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (C : BalancedGlobal.Candidate (contract target hab hOne) degree
      (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (root : Fin degree) (u v : target.V) (flag : target.edges)
    (flagPartition selectedLeft selectedRight selectedNew : SheetPartition degree)
    (hFlagEq : ∀ sheet, (data.edgePartition flag).block sheet = flagPartition.block sheet)
    (hFlagAt : flag ∈ GluingDatum.incidentEdges u)
    (hContractedAt : contracted ∈ GluingDatum.incidentEdges u)
    (hBgEdge : ∀ edge ∈ GluingDatum.incidentEdges u, ∀ sheet : Fin degree,
      ¬ (mergedPartition data a b).Rel root sheet →
      (data.edgePartition edge).block sheet = (data.vertexPartition u).block sheet)
    (hBgTri : ∀ sheet : Fin degree,
      ¬ (mergedPartition data a b).Rel root sheet →
      (data.vertexPartition v).block sheet = (mergedPartition data a b).block sheet)
    (hUSelected : ∀ sheet, (mergedPartition data a b).Rel root sheet →
      (data.vertexPartition u).block sheet = selectedLeft.block sheet)
    (hVSelected : ∀ sheet, (mergedPartition data a b).Rel root sheet →
      (data.vertexPartition v).block sheet = selectedRight.block sheet)
    (hNewSelected : ∀ sheet, (mergedPartition data a b).Rel root sheet →
      (data.edgePartition contracted).block sheet = selectedNew.block sheet)
    (hLeftSelected : ∀ sheet, (mergedPartition data a b).Rel root sheet →
      (pasted C).left.block sheet = selectedLeft.block sheet)
    (hRightSelected : ∀ sheet, (mergedPartition data a b).Rel root sheet →
      (pasted C).right.block sheet = selectedRight.block sheet)
    (hNewMember : ∀ sheet, (mergedPartition data a b).Rel root sheet →
      (pasted C).newEdge.block sheet = selectedNew.block sheet)
    (hLeftBackground : ∀ sheet, ¬ (mergedPartition data a b).Rel root sheet →
      (pasted C).left.block sheet = flagPartition.block sheet)
    (hRightBackground : ∀ sheet, ¬ (mergedPartition data a b).Rel root sheet →
      (pasted C).right.block sheet = (mergedPartition data a b).block sheet)
    (hNewBackground : ∀ sheet, ¬ (mergedPartition data a b).Rel root sheet →
      (pasted C).newEdge.block sheet = flagPartition.block sheet) :
    (∀ sheet, (data.vertexPartition u).block sheet = (pasted C).left.block sheet) ∧
      (∀ sheet, (data.vertexPartition v).block sheet = (pasted C).right.block sheet) ∧
      (∀ sheet, (data.edgePartition contracted).block sheet =
        (pasted C).newEdge.block sheet) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro sheet
    by_cases hSel : (mergedPartition data a b).Rel root sheet
    · exact (hUSelected sheet hSel).trans (hLeftSelected sheet hSel).symm
    · exact ((hBgEdge _ hFlagAt sheet hSel).symm.trans (hFlagEq sheet)).trans
        (hLeftBackground sheet hSel).symm
  · intro sheet
    by_cases hSel : (mergedPartition data a b).Rel root sheet
    · exact (hVSelected sheet hSel).trans (hRightSelected sheet hSel).symm
    · exact (hBgTri sheet hSel).trans (hRightBackground sheet hSel).symm
  · intro sheet
    by_cases hSel : (mergedPartition data a b).Rel root sheet
    · exact (hNewSelected sheet hSel).trans (hNewMember sheet hSel).symm
    · exact ((hBgEdge _ hContractedAt sheet hSel).trans
        ((hBgEdge _ hFlagAt sheet hSel).symm.trans (hFlagEq sheet))).trans
        (hNewBackground sheet hSel).symm

end Split


/-! ## §2  The six block-dictionary facts of each member over the incoming datum

Three on the distinguished class `A₀` and three off it, per member.  The
off-`A₀` three are `W2MkkStableLift`'s background shapes read through
`LimitChainCore.BackgroundShape`; the on-`A₀` three are read off
`W2MkkStableGraph.detach_resolution` / `joined_resolution`, which say which
local resolution the member installs at an anchor of `A₀`. -/

section MemberDictionary

variable {wallTarget : CFGraph} {degree : ℕ} {wall : wallTarget.V}
  {wallData : GluingDatum wallTarget degree} {wallStar : TwoStar wallTarget wall}
  {wallBlock : WallBlock wallData wall}
  {wallProfile : W2R2SourceProfile.SourceProfile wallData wallStar wallBlock}

/-- An anchor of the distinguished block lies in the pinned sheet's wall
class: `A₀` is `pinSheet`'s own block. -/
theorem repr_rel_pinSheet {sheet : Fin degree}
    (hSel : (wallData.vertexPartition wall).Rel wallBlock.1 sheet) :
    (wallData.vertexPartition wall).Rel (pinSheet wallProfile)
      ((wallData.vertexPartition wall).repr sheet) :=
  ((pinSheet_rel wallProfile).symm.trans hSel).trans
    ((wallData.vertexPartition wall).rel_repr_right sheet)

/-! ### `M⁽¹⁾` / `M⁽²⁾`: Base II.2 splits `A₀` at every one of the three
positions -/

/-- On `A₀` the detaching member's retained end is `t₂`'s own occurrence
partition: `e₁` and `e₂` are separate vertices `A'`, `A''` of `ndG(A₀)`. -/
theorem detach_pasted_left_selected (shape : Shape wallProfile)
    (detach : DetachData wallProfile) {sheet : Fin degree}
    (hSel : (wallData.vertexPartition wall).Rel wallBlock.1 sheet) :
    (pasted (detach.candidate shape)).left.block sheet =
      (endpointPartition wallProfile).block sheet := by
  show (LocalResolution.pasteLeft (wallData.vertexPartition wall)
    (detach.candidate shape).resolution (detach.candidate shape).contracts).block sheet = _
  unfold LocalResolution.pasteLeft
  rw [SheetPartition.paste_block, W2MkkStableGraph.detach_resolution shape detach _
    (repr_rel_pinSheet hSel)]
  rfl

/-- On `A₀` its fresh end detaches the pinned sheet from the whole wall block:
`A⁽ᵠ⁾ = A₀ ∖ {x}` together with the entirely pruned `{x}`. -/
theorem detach_pasted_right_selected (shape : Shape wallProfile)
    (detach : DetachData wallProfile) {sheet : Fin degree}
    (hSel : (wallData.vertexPartition wall).Rel wallBlock.1 sheet) :
    (pasted (detach.candidate shape)).right.block sheet =
      ((wallData.vertexPartition wall).detachSheet (pinSheet wallProfile) detach.remainder
        detach.ne_remainder detach.wallTogether).block sheet := by
  show (LocalResolution.pasteRight (wallData.vertexPartition wall)
    (detach.candidate shape).resolution (detach.candidate shape).contracts).block sheet = _
  unfold LocalResolution.pasteRight
  rw [SheetPartition.paste_block, W2MkkStableGraph.detach_resolution shape detach _
    (repr_rel_pinSheet hSel)]
  rfl

/-- On `A₀` its new edge detaches the pinned sheet from `t₂`'s occurrence
partition: `|e'| = k₁ - 1`, `|e''| = k₂` (or the mirror). -/
theorem detach_pasted_newEdge_selected (shape : Shape wallProfile)
    (detach : DetachData wallProfile) {sheet : Fin degree}
    (hSel : (wallData.vertexPartition wall).Rel wallBlock.1 sheet) :
    (pasted (detach.candidate shape)).newEdge.block sheet =
      ((endpointPartition wallProfile).detachSheet (pinSheet wallProfile) detach.remainder
        detach.ne_remainder detach.together).block sheet := by
  show (LocalResolution.pasteNewEdge (wallData.vertexPartition wall)
    (detach.candidate shape).resolution (detach.candidate shape).contracts).block sheet = _
  unfold LocalResolution.pasteNewEdge
  rw [SheetPartition.paste_block, W2MkkStableGraph.detach_resolution shape detach _
    (repr_rel_pinSheet hSel)]
  rfl

/-- Off `A₀` the detaching member's retained end carries `t₂`'s class. -/
theorem detach_pasted_left_background (input : W2SourceInput wallData wallStar)
    (shape : Shape wallProfile) (detach : DetachData wallProfile) {sheet : Fin degree}
    (hOff : ¬ (wallData.vertexPartition wall).Rel wallBlock.1 sheet) :
    (pasted (detach.candidate shape)).left.block sheet =
      (wallData.edgePartition (wallStar.edge wallProfile.doubleLabel)).block sheet :=
  (W2MkkStableLift.detachBackgroundShape input shape detach).pasted_left_block hOff

/-- Off `A₀` its fresh end carries the whole wall block. -/
theorem detach_pasted_right_background (input : W2SourceInput wallData wallStar)
    (shape : Shape wallProfile) (detach : DetachData wallProfile) {sheet : Fin degree}
    (hOff : ¬ (wallData.vertexPartition wall).Rel wallBlock.1 sheet) :
    (pasted (detach.candidate shape)).right.block sheet =
      (wallData.vertexPartition wall).block sheet :=
  (W2MkkStableLift.detachBackgroundShape input shape detach).pasted_right_block hOff

/-- Off `A₀` its new edge carries `t₂`'s class. -/
theorem detach_pasted_newEdge_background (input : W2SourceInput wallData wallStar)
    (shape : Shape wallProfile) (detach : DetachData wallProfile) {sheet : Fin degree}
    (hOff : ¬ (wallData.vertexPartition wall).Rel wallBlock.1 sheet) :
    (pasted (detach.candidate shape)).newEdge.block sheet =
      (wallData.edgePartition (wallStar.edge wallProfile.doubleLabel)).block sheet :=
  (W2MkkStableLift.detachBackgroundShape input shape detach).pasted_newEdge_block hOff

/-! ### `M⁽³⁾`: Base II.1 keeps the whole wall partition everywhere -/

theorem joined_pasted_left_block (distinguished sheet : Fin degree) :
    (pasted (joinedCandidate wallProfile distinguished)).left.block sheet =
      (wallData.vertexPartition wall).block sheet :=
  congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
    (W2MkkStableGraph.joined_pasted_left wallProfile distinguished)

theorem joined_pasted_right_block (distinguished sheet : Fin degree) :
    (pasted (joinedCandidate wallProfile distinguished)).right.block sheet =
      (wallData.vertexPartition wall).block sheet :=
  congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
    (W2MkkStableGraph.joined_pasted_right wallProfile distinguished)

theorem joined_pasted_newEdge_block (distinguished sheet : Fin degree) :
    (pasted (joinedCandidate wallProfile distinguished)).newEdge.block sheet =
      (wallData.vertexPartition wall).block sheet :=
  congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
    (W2MkkStableGraph.joined_pasted_newEdge wallProfile distinguished)

end MemberDictionary


/-! ## §3  The selected-class census, named

This is the one thing this chain does not prove (`W2MkkSelectedCensus` proves
it). `SelectedCensus` says what the incoming cover's three wall positions look
like **on the distinguished block** `A₀`; off `A₀` the `r = 0` census of
`W2MkkIncomingCensus` §5 already settles them, and the member side is §2. The
two instantiations are Base II.1 (everything joined on `A₀`) and Base II.2
(everything split), and the dichotomy between them is Part I's dichotomy in Case
`{w2-r2}`: `ndG(A₀)` has either one edge `e'` or two edges `e'`, `e''`. -/

section Incoming

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
  (input : W2SourceInput (contractDatum data hc hab hOne) star)
  {block : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
  (profile : W2R2SourceProfile.SourceProfile (contractDatum data hc hab hOne) star block)

/-- The wall datum's partition at the merged vertex is the merged partition,
read at one sheet. -/
theorem merged_block_eq (sheet : Fin degree) :
    ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block sheet =
      (mergedPartition data a b).block sheet :=
  congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
    (contractDatum_vertexPartition_merge data hc hab hOne)

/-- **The selected-class half of the incoming census.**  The three named
partitions are the Figure 34 member's own; a cover satisfying this at a member's
triple *is* that member at the wall, once the background census is added. -/
structure SelectedCensus (selectedLeft selectedRight selectedNew : SheetPartition degree) :
    Prop where
  /-- What the `t₂` endpoint carries on `A₀`. -/
  left : ∀ sheet, (mergedPartition data a b).Rel block.1 sheet →
    (data.vertexPartition (doubleEnd data hc hab hOne profile)).block sheet =
      selectedLeft.block sheet
  /-- What the `t₃` endpoint carries on `A₀`. -/
  right : ∀ sheet, (mergedPartition data a b).Rel block.1 sheet →
    (data.vertexPartition (singleEnd data hc hab hOne profile)).block sheet =
      selectedRight.block sheet
  /-- What the contracted occurrence carries on `A₀`. -/
  new : ∀ sheet, (mergedPartition data a b).Rel block.1 sheet →
    (data.edgePartition contracted).block sheet = selectedNew.block sheet

/-- **Base II.1** (Part I, Case `{w2-r2}`): the ends of `e₁`, `e₂` above `u` are one vertex of
`ndG(A₀)`, so all three wall positions carry the whole distinguished block.
This is `M⁽³⁾`'s picture. -/
abbrev JoinedCensus : Prop :=
  SelectedCensus data hc hab hOne profile (mergedPartition data a b)
    (mergedPartition data a b) (mergedPartition data a b)

/-- **Base II.2** (Part I, Case `{w2-r2}`): `ndG(A₀)` has three vertices, so the `t₂` endpoint
splits `A₀` into `e₁` and `e₂`, the `t₃` endpoint detaches the pinned sheet from
`A₀`, and the contracted occurrence detaches it from `t₂`'s partition.  This is
`M⁽¹⁾`'s and `M⁽²⁾`'s picture; which of the two, the datum decides through
`W2MkkSourceCandidates.pinSheet_mem`. -/
abbrev DetachCensus (detach : DetachData profile) : Prop :=
  SelectedCensus data hc hab hOne profile (endpointPartition profile)
    (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).detachSheet
      (pinSheet profile) detach.remainder detach.ne_remainder detach.wallTogether)
    ((endpointPartition profile).detachSheet (pinSheet profile) detach.remainder
      detach.ne_remainder detach.together)

end Incoming


/-! ## §4  The three wall comparisons, one member at a time -/

section WallBlocks

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
  (input : W2SourceInput (contractDatum data hc hab hOne) star)
  {block : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
  (profile : W2R2SourceProfile.SourceProfile (contractDatum data hc hab hOne) star block)

/-- A sheet off the distinguished class, read in the wall datum's own
partition. -/
theorem off_wall_of_off_merged {sheet : Fin degree}
    (hOff : ¬ (mergedPartition data a b).Rel block.1 sheet) :
    ¬ ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel block.1 sheet :=
  fun h ↦ hOff (cast (merged_rel_eq data hc hab hOne block.1 sheet) h)

/-- A sheet on the distinguished class, read in the wall datum's own
partition. -/
theorem on_wall_of_on_merged {sheet : Fin degree}
    (hSel : (mergedPartition data a b).Rel block.1 sheet) :
    ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel block.1 sheet :=
  cast (merged_rel_eq data hc hab hOne block.1 sheet).symm hSel

include fullDim hForest input

/-- **`M⁽³⁾`'s three wall comparisons.**  Base II.1's selected-class census plus
the `T_2` background census identify the incoming cover's wall data with
`W2MkkSourceCandidates.joinedCandidate`'s pasted local resolution. -/
theorem joined_wall_blocks
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ block → (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
    (hRightCard : (GluingDatum.incidentEdges b).card = 2)
    (distinguished : Fin degree)
    (census : JoinedCensus data hc hab hOne profile) :
    (∀ sheet, (data.vertexPartition (doubleEnd data hc hab hOne profile)).block sheet =
        (pasted (joinedCandidate profile distinguished)).left.block sheet) ∧
      (∀ sheet, (data.vertexPartition (singleEnd data hc hab hOne profile)).block sheet =
        (pasted (joinedCandidate profile distinguished)).right.block sheet) ∧
      (∀ sheet, (data.edgePartition contracted).block sheet =
        (pasted (joinedCandidate profile distinguished)).newEdge.block sheet) :=
  wall_blocks_of_split_dictionary data hc hab hOne (joinedCandidate profile distinguished)
    block.1 (doubleEnd data hc hab hOne profile) (singleEnd data hc hab hOne profile)
    (flagEdge data hc hab hOne profile)
    ((contractDatum data hc hab hOne).edgePartition (star.edge profile.doubleLabel))
    (mergedPartition data a b) (mergedPartition data a b) (mergedPartition data a b)
    (flag_block data hc hab hOne profile)
    (flagEdge_mem_doubleEnd data hc hab hOne profile)
    (contracted_mem_doubleEnd data hc hab hOne profile)
    (background_edge_block_doubleEnd data hc hab hOne fullDim profile hForest hBackground
      hLeftCard hRightCard)
    (background_joined_block_singleEnd data hc hab hOne fullDim profile hForest hBackground
      hLeftCard hRightCard)
    census.left census.right census.new
    (fun sheet _ ↦ (joined_pasted_left_block distinguished sheet).trans
      (merged_block_eq data hc hab hOne sheet))
    (fun sheet _ ↦ (joined_pasted_right_block distinguished sheet).trans
      (merged_block_eq data hc hab hOne sheet))
    (fun sheet _ ↦ (joined_pasted_newEdge_block distinguished sheet).trans
      (merged_block_eq data hc hab hOne sheet))
    (fun sheet hOff ↦ (joined_pasted_left_block distinguished sheet).trans
      (W2MkkStableLift.wall_block_eq_double_block input profile
        (off_wall_of_off_merged data hc hab hOne hOff)))
    (fun sheet _ ↦ (joined_pasted_right_block distinguished sheet).trans
      (merged_block_eq data hc hab hOne sheet))
    (fun sheet hOff ↦ (joined_pasted_newEdge_block distinguished sheet).trans
      (W2MkkStableLift.wall_block_eq_double_block input profile
        (off_wall_of_off_merged data hc hab hOne hOff)))

/-- **A detaching member's three wall comparisons.**  Base II.2's selected-class
census plus the same background census.  This is the application the core's
`wall_blocks_of_dictionary` cannot make: no restored endpoint is joined on
`A₀`. -/
theorem detach_wall_blocks
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ block → (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
    (hRightCard : (GluingDatum.incidentEdges b).card = 2)
    (shape : Shape profile) (detach : DetachData profile)
    (census : DetachCensus data hc hab hOne profile detach) :
    (∀ sheet, (data.vertexPartition (doubleEnd data hc hab hOne profile)).block sheet =
        (pasted (detach.candidate shape)).left.block sheet) ∧
      (∀ sheet, (data.vertexPartition (singleEnd data hc hab hOne profile)).block sheet =
        (pasted (detach.candidate shape)).right.block sheet) ∧
      (∀ sheet, (data.edgePartition contracted).block sheet =
        (pasted (detach.candidate shape)).newEdge.block sheet) :=
  wall_blocks_of_split_dictionary data hc hab hOne (detach.candidate shape)
    block.1 (doubleEnd data hc hab hOne profile) (singleEnd data hc hab hOne profile)
    (flagEdge data hc hab hOne profile)
    ((contractDatum data hc hab hOne).edgePartition (star.edge profile.doubleLabel))
    (endpointPartition profile)
    (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).detachSheet
      (pinSheet profile) detach.remainder detach.ne_remainder detach.wallTogether)
    ((endpointPartition profile).detachSheet (pinSheet profile) detach.remainder
      detach.ne_remainder detach.together)
    (flag_block data hc hab hOne profile)
    (flagEdge_mem_doubleEnd data hc hab hOne profile)
    (contracted_mem_doubleEnd data hc hab hOne profile)
    (background_edge_block_doubleEnd data hc hab hOne fullDim profile hForest hBackground
      hLeftCard hRightCard)
    (background_joined_block_singleEnd data hc hab hOne fullDim profile hForest hBackground
      hLeftCard hRightCard)
    census.left census.right census.new
    (fun _sheet hSel ↦ detach_pasted_left_selected shape detach
      (on_wall_of_on_merged data hc hab hOne hSel))
    (fun _sheet hSel ↦ detach_pasted_right_selected shape detach
      (on_wall_of_on_merged data hc hab hOne hSel))
    (fun _sheet hSel ↦ detach_pasted_newEdge_selected shape detach
      (on_wall_of_on_merged data hc hab hOne hSel))
    (fun _sheet hOff ↦ detach_pasted_left_background input shape detach
      (off_wall_of_off_merged data hc hab hOne hOff))
    (fun sheet hOff ↦ (detach_pasted_right_background input shape detach
      (off_wall_of_off_merged data hc hab hOne hOff)).trans
      (merged_block_eq data hc hab hOne sheet))
    (fun _sheet hOff ↦ detach_pasted_newEdge_background input shape detach
      (off_wall_of_off_merged data hc hab hOne hOff))

end WallBlocks


/-! ## §5  The whole-cover exhaustion

`W3Nd2IncomingMemberMatching.sameBlocks_of_wall_blocks` does the vertex and
occurrence exhaustion once: away from the contracted wall every transported
partition is literally the wall datum's own and so is the member's, and at the
wall there are exactly the three comparisons of §4.  Nothing about Figure 34
enters it, so it is consumed verbatim. -/

section SameBlocks

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
  (input : W2SourceInput (contractDatum data hc hab hOne) star)
  {block : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
  (profile : W2R2SourceProfile.SourceProfile (contractDatum data hc hab hOne) star block)
  (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
    other ≠ block → (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
  (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
  (hRightCard : (GluingDatum.incidentEdges b).card = 2)

include fullDim hForest input hBackground hLeftCard hRightCard

/-- **`M⁽³⁾` is the incoming cover, partition by partition.** -/
theorem joined_sameBlocks (distinguished : Fin degree)
    (census : JoinedCensus data hc hab hOne profile) :
    (∀ vertex, ((GluingTransport.transport (memberTargetIso data hc hab hOne
          (joinedCandidate profile distinguished)
          (member_placement data hc hab hOne profile hLeftCard hRightCard))
        data).vertexPartition vertex).SameBlocks
      ((joinedCandidate profile distinguished).datum.vertexPartition vertex)) ∧
    (∀ edge, ((GluingTransport.transport (memberTargetIso data hc hab hOne
          (joinedCandidate profile distinguished)
          (member_placement data hc hab hOne profile hLeftCard hRightCard))
        data).edgePartition edge).SameBlocks
      ((joinedCandidate profile distinguished).datum.edgePartition edge)) := by
  obtain ⟨hLeftWall, hRightWall, hNewWall⟩ := joined_wall_blocks data hc hab hOne fullDim
    hForest input profile hBackground hLeftCard hRightCard distinguished census
  obtain ⟨hOld, hFresh⟩ := transported_endpoints data hc hab hOne profile hLeftCard hRightCard
    (member_placement data hc hab hOne profile hLeftCard hRightCard)
  exact sameBlocks_of_wall_blocks data hc hab hOne fullDim.targetConnected fullDim.targetGenus
    (joinedCandidate profile distinguished)
    (member_placement data hc hab hOne profile hLeftCard hRightCard)
    (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
      hOld).trans (hLeftWall sheet))
    (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
      hFresh).trans (hRightWall sheet))
    hNewWall

/-- **The detaching member the datum carries is the incoming cover, partition by
partition.** -/
theorem detach_sameBlocks (shape : Shape profile) (detach : DetachData profile)
    (census : DetachCensus data hc hab hOne profile detach) :
    (∀ vertex, ((GluingTransport.transport (memberTargetIso data hc hab hOne
          (detach.candidate shape)
          (member_placement data hc hab hOne profile hLeftCard hRightCard))
        data).vertexPartition vertex).SameBlocks
      ((detach.candidate shape).datum.vertexPartition vertex)) ∧
    (∀ edge, ((GluingTransport.transport (memberTargetIso data hc hab hOne
          (detach.candidate shape)
          (member_placement data hc hab hOne profile hLeftCard hRightCard))
        data).edgePartition edge).SameBlocks
      ((detach.candidate shape).datum.edgePartition edge)) := by
  obtain ⟨hLeftWall, hRightWall, hNewWall⟩ := detach_wall_blocks data hc hab hOne fullDim
    hForest input profile hBackground hLeftCard hRightCard shape detach census
  obtain ⟨hOld, hFresh⟩ := transported_endpoints data hc hab hOne profile hLeftCard hRightCard
    (member_placement data hc hab hOne profile hLeftCard hRightCard)
  exact sameBlocks_of_wall_blocks data hc hab hOne fullDim.targetConnected fullDim.targetGenus
    (detach.candidate shape)
    (member_placement data hc hab hOne profile hLeftCard hRightCard)
    (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
      hOld).trans (hLeftWall sheet))
    (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
      hFresh).trans (hRightWall sheet))
    hNewWall

end SameBlocks


/-! ## §6  The normalization receipts and the indexed member exit

The exit is `IncomingMatchingCore.exists_member_normalization_of_family` at
`n = 2`.  Its `selector`/`value` pair is, for M-kk, the Figure 34 **position**
itself with `value := id`.  That is not a weakening dressed up: nd2's and nd3's
dichotomies are equations between *target occurrences*
(`divalentOccurrence = smallTarget`), so their selector is a target datum, while
Base II.1 / Base II.2 is a statement about *sheet partitions on `A₀`* -- Part
I's "either one edge `e'` or two edges `e'`, `e''`" -- which is not an equation
in any ambient type.  The position carrying the case's census is the
honest selector for it.  What the combinator does here is what it does
everywhere: it produces the member's literal `Option` column dictionary, `none`
included, and packages the receipt. -/

section Identification

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
  (input : W2SourceInput (contractDatum data hc hab hOne) star)
  {block : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
  (profile : W2R2SourceProfile.SourceProfile (contractDatum data hc hab hOne) star block)
  (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
    other ≠ block → (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
  (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
  (hRightCard : (GluingDatum.incidentEdges b).card = 2)
  (shape : Shape profile) (detach : DetachData profile) (distinguished : Fin degree)

/-- **The two Figure 34 members over the incoming datum.**  Position `0` is the
detaching member the datum carries -- `M⁽¹⁾` or `M⁽²⁾`, decided by
`W2MkkSourceCandidates.pinSheet_mem` -- and position `1` is `M⁽³⁾`.  The third
Figure 34 slot is remote (`W2MkkLimitColumns.remoteMember`) and is not of this
type. -/
noncomputable def members : Fin 2 →
    BalancedGlobal.Candidate (contract target hab hOne) degree
      (contractDatum data hc hab hOne) ⟨a, hab⟩ :=
  ![detach.candidate shape, joinedCandidate profile distinguished]

/-- The selected-class census belonging to each position: Base II.2 at `0`,
Base II.1 at `1`. -/
def Census : Fin 2 → Prop :=
  ![DetachCensus data hc hab hOne profile detach, JoinedCensus data hc hab hOne profile]

/-- Every member's wall-side assignment is the oriented star's, so one
placement serves both positions. -/
theorem members_placement (index : Fin 2)
    (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
    (hRightCard : (GluingDatum.incidentEdges b).card = 2) :
    Placement hc hab hOne (members data hc hab hOne profile shape detach distinguished
      index).right := by
  match index with
  | 0 => exact member_placement data hc hab hOne profile hLeftCard hRightCard
  | 1 => exact member_placement data hc hab hOne profile hLeftCard hRightCard

include fullDim hForest input hBackground hLeftCard hRightCard

theorem members_vertexSameBlocks (index : Fin 2)
    (census : Census data hc hab hOne profile detach index) (vertex : _) :
    ((GluingTransport.transport (memberTargetIso data hc hab hOne
        (members data hc hab hOne profile shape detach distinguished index)
        (members_placement data hc hab hOne profile shape detach distinguished index
          hLeftCard hRightCard))
      data).vertexPartition vertex).SameBlocks
      ((members data hc hab hOne profile shape detach distinguished index).datum.vertexPartition
        vertex) := by
  match index with
  | 0 => exact (detach_sameBlocks data hc hab hOne fullDim hForest input profile hBackground
            hLeftCard hRightCard shape detach census).1 vertex
  | 1 => exact (joined_sameBlocks data hc hab hOne fullDim hForest input profile hBackground
            hLeftCard hRightCard distinguished census).1 vertex

theorem members_edgeSameBlocks (index : Fin 2)
    (census : Census data hc hab hOne profile detach index) (edge : _) :
    ((GluingTransport.transport (memberTargetIso data hc hab hOne
        (members data hc hab hOne profile shape detach distinguished index)
        (members_placement data hc hab hOne profile shape detach distinguished index
          hLeftCard hRightCard))
      data).edgePartition edge).SameBlocks
      ((members data hc hab hOne profile shape detach distinguished index).datum.edgePartition
        edge) := by
  match index with
  | 0 => exact (detach_sameBlocks data hc hab hOne fullDim hForest input profile hBackground
            hLeftCard hRightCard shape detach census).2 edge
  | 1 => exact (joined_sameBlocks data hc hab hOne fullDim hForest input profile hBackground
            hLeftCard hRightCard distinguished census).2 edge

/-- **The incoming `w2Mkk` cover is a named Figure 34 member.**  Given the
selected-class census at one of the two positions over the incoming datum, that
position's member carries the incoming cover's literal `Option` column
dictionary -- the restored contracted occurrence at `none` included -- together
with `W3Nd2IncomingMemberMatching.NormalizedAgainst`, the receipt saying that the
transported member carries an honest presentation whose length matrix is the
incoming one entry by entry. -/
theorem exists_member_normalization (position : Fin 2)
    (census : Census data hc hab hOne profile detach position) :
    ∃ index : Fin 2, ∃ h : position = index,
      (∀ column : Option (contract target hab hOne).edges,
          GluingTransport.edgeEquiv (memberTargetIso data hc hab hOne
              (members data hc hab hOne profile shape detach distinguished index)
              (members_placement data hc hab hOne profile shape detach distinguished index
                hLeftCard hRightCard))
              (M11IncomingCoordinates.incomingColumnEquiv hc hab hOne column) =
            occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
              (members data hc hab hOne profile shape detach distinguished index).right column) ∧
        NormalizedAgainst data fullDim
          (memberTargetIso data hc hab hOne
            (members data hc hab hOne profile shape detach distinguished index)
            (members_placement data hc hab hOne profile shape detach distinguished index
              hLeftCard hRightCard))
          (members data hc hab hOne profile shape detach distinguished index).datum
          (members_vertexSameBlocks data hc hab hOne fullDim hForest input profile hBackground
            hLeftCard hRightCard shape detach distinguished index ((show position = index from h) ▸ census))
          (members_edgeSameBlocks data hc hab hOne fullDim hForest input profile hBackground
            hLeftCard hRightCard shape detach distinguished index ((show position = index from h) ▸ census)) :=
  exists_member_normalization_of_family data hc hab hOne fullDim.targetConnected
    fullDim.targetGenus (members data hc hab hOne profile shape detach distinguished)
    position id ⟨position, rfl⟩
    (fun index _ ↦ members_placement data hc hab hOne profile shape detach distinguished index
      hLeftCard hRightCard)
    (fun index h ↦ NormalizedAgainst data fullDim
      (memberTargetIso data hc hab hOne
        (members data hc hab hOne profile shape detach distinguished index)
        (members_placement data hc hab hOne profile shape detach distinguished index
          hLeftCard hRightCard))
      (members data hc hab hOne profile shape detach distinguished index).datum
      (members_vertexSameBlocks data hc hab hOne fullDim hForest input profile hBackground
        hLeftCard hRightCard shape detach distinguished index ((show position = index from h) ▸ census))
      (members_edgeSameBlocks data hc hab hOne fullDim hForest input profile hBackground
        hLeftCard hRightCard shape detach distinguished index ((show position = index from h) ▸ census)))
    (fun _ _ ↦ normalizedAgainst data fullDim _ _ _ _)

/-- The dichotomy form: Base II.1 or Base II.2 -- Part I's "`ndG(A₀)` has
either one edge `e'` or two edges `e'`, `e''`" -- selects the position, and the
two `SameBlocks` witnesses are existentially quantified, which is the shape the
normalization receipts are consumed in. -/
theorem exists_member_normalization_of_dichotomy
    (hCensus : DetachCensus data hc hab hOne profile detach ∨
      JoinedCensus data hc hab hOne profile) :
    ∃ index : Fin 2,
      (∀ column : Option (contract target hab hOne).edges,
          GluingTransport.edgeEquiv (memberTargetIso data hc hab hOne
              (members data hc hab hOne profile shape detach distinguished index)
              (members_placement data hc hab hOne profile shape detach distinguished index
                hLeftCard hRightCard))
              (M11IncomingCoordinates.incomingColumnEquiv hc hab hOne column) =
            occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
              (members data hc hab hOne profile shape detach distinguished index).right column) ∧
      ∃ hVertices : ∀ vertex, ((GluingTransport.transport (memberTargetIso data hc hab hOne
            (members data hc hab hOne profile shape detach distinguished index)
            (members_placement data hc hab hOne profile shape detach distinguished index
              hLeftCard hRightCard))
          data).vertexPartition vertex).SameBlocks
          ((members data hc hab hOne profile shape detach distinguished
            index).datum.vertexPartition vertex),
      ∃ hEdges : ∀ edge, ((GluingTransport.transport (memberTargetIso data hc hab hOne
            (members data hc hab hOne profile shape detach distinguished index)
            (members_placement data hc hab hOne profile shape detach distinguished index
              hLeftCard hRightCard))
          data).edgePartition edge).SameBlocks
          ((members data hc hab hOne profile shape detach distinguished
            index).datum.edgePartition edge),
        NormalizedAgainst data fullDim
          (memberTargetIso data hc hab hOne
            (members data hc hab hOne profile shape detach distinguished index)
            (members_placement data hc hab hOne profile shape detach distinguished index
              hLeftCard hRightCard))
          (members data hc hab hOne profile shape detach distinguished index).datum
          hVertices hEdges := by
  rcases hCensus with hDetach | hJoined
  · obtain ⟨index, _, hColumns, hReceipt⟩ := exists_member_normalization data hc hab hOne
      fullDim hForest input profile hBackground hLeftCard hRightCard shape detach
      distinguished 0 hDetach
    exact ⟨index, hColumns, _, _, hReceipt⟩
  · obtain ⟨index, _, hColumns, hReceipt⟩ := exists_member_normalization data hc hab hOne
      fullDim hForest input profile hBackground hLeftCard hRightCard shape detach
      distinguished 1 hJoined
    exact ⟨index, hColumns, _, _, hReceipt⟩

end Identification

end DraismaVargas.LocalCases.W2MkkIncomingMatching
