module

public import DraismaVargas.LocalCases.W2M1kIncomingCensus
public import DraismaVargas.LocalCases.W2M1kStableLift

@[expose] public section

/-!
# Identifying the incoming `w2M1k` datum with a named Figure 33 member

Source: Draisma--Vargas Part I, case `{w2-r2-nd3-M-1k}` and Figure 33.

`W2M1kIncomingCensus` handles the target side: the **trichotomy** (Base I.a is
a genuine member here, so no member is precluded outright), the placements,
which restored endpoint each member's retained end restores, and the `r = 0`
background census at a `T_2` wall.  This module does the wall comparison and
the whole-cover assembly for each of Figure 33's three members; the M-1k
closure (`W2M1kClosureUnconditional`) consumes the result.

## The three members, and what each needs

| member | target | retained end | fresh end | new edge on `A₀` |
| --- | --- | --- | --- | --- |
| `M⁽¹⁾` (Base I.a) | `T_∅` | `pairBlock p₀ q` | `detachSheet p₀ q` | `splitBlock p₀` |
| `M⁽²⁾` (Base II.2.2.M) | `T_2` | `detachSheet p₀ p₁` | `detachSheet p₁ p₀` | `secondNewEdge` |
| `M⁽³⁾` (Base II.1.M) | `T_2` | `A₀` | `A₀` | `A₀` |

`M⁽²⁾` and `M⁽³⁾` compare against `zeroEnd` and `oneEnd`; `M⁽¹⁾` compares against
`leafEnd` and `branchEnd` (`W2M1kIncomingCensus` §4, §5).

## What is proved, and what is assumed

Proved outright: the six block-dictionary facts of each of the three members
(§1), from `W2M1kStableGraph.divided_resolution` / `joined_resolution` and
`W2M1kLeaves.leaf_resolution_selected` / `leaf_resolution_background` together
with `W2M1kStableLift`'s background blocks; the three wall comparisons per
member (§3); and the whole-cover `SameBlocks` exhaustion (§4), by
`W3Nd2IncomingMemberMatching.sameBlocks_of_wall_blocks`.

Assumed here as named hypotheses, and proved in later modules:

* `SelectedCensus` -- the **selected-class** half of the source census on `A₀`,
  the Base I / Base II analysis of case `{w2-r2-nd3}` in Part I.  This is the
  irreducibly per-case half of every incoming instance (compare
  `W3Nd3IncomingCensus.selected_fibre_census_of_shared`,
  `M11IncomingSelectedCases` and `W2MkkSelectedCensus`).  It is *not*
  re-derivable from anything in this chain: `W2M1kStableGraph` is the outgoing
  survival census.  `W2M1kSelectedCensus` proves it.
* `LeafBackgroundCensus` -- the `r = 0` background census **at a `(1,3)` wall**.
  For the two `T_2` members the background half is a theorem
  (`W2M1kIncomingCensus.background_edge_block_zeroEnd`,
  `background_joined_block_oneEnd`), through the `AnyBlock` lemmas of
  `W3Nd2IncomingBackground` / `W3Nd2IncomingNormalization` for a divalent
  restored endpoint; at Base I.a neither endpoint is divalent -- the valencies
  are `(1, 3)`.  There the census follows from Part I's remark on
  change-minimal leaves (`rem-leaves-min-change`): at a change-minimal leaf `v`
  every non-dangling class `A` above it has `r(A) = 2`, `val A = 2`,
  `|A| = 2`, there is exactly one such class, and `~_t` is trivial on it.  On a
  background block `r = 0`, so no class above the leaf is non-dangling there,
  every dangling class above a leaf is a singleton, and both
  `vertexPartition (leafEnd …)` and `edgePartition contracted` come out
  discrete -- the clauses `left` and `new` below.  The third clause `right` is
  then a *consequence*: with `p = |A₀'|` and `e = |A₀'|` both maximal on a
  background block `A₀'`, the contraction-forest identity `e + 1 = p + q` of
  `W3Nd2IncomingBackground.AnyBlock.background_dichotomy` forces `q = 1`.
  `W2M1kLeafBackground` proves it, through the leaf-endpoint lemmas of
  `W3Nd2IncomingNormalization.AnyBlock`.

## Why there is no `Fin n` family here

`IncomingMatchingCore.exists_member_normalization_of_family` asks for
`C : Fin n → BalancedGlobal.Candidate …` **together with one placement per
selected index**.  At M-kk and P that is free, because all members share a
wall-side assignment; at M-1k `M⁽¹⁾`'s is the constant `true` and the other
two's is `star.right`, and the two placements are *jointly unsatisfiable*
(`W2M1kIncomingCensus.no_true_placement_of_divalent`,
`no_star_placement_of_leaf`).  A `Fin 3` family would therefore be vacuous, and a
`Fin 2` family cannot even be *formed* over a datum carrying only one of
`LeafPair`, `DividedData` (`W2M1kSourceCandidates.not_leafPair_and_dividedData`).
So the three members are matched one at a time, each with its own placement,
and the trichotomy that selects among them is
`W2M1kIncomingCensus.member_trichotomy` on the target side and `SelectedCensus`
on the source side.  This is the honest shape for a case whose members do not
share a target type, and it costs nothing: the combinator's only other output,
the literal `Option` column dictionary, is
`IncomingMatchingCore.memberTargetIso_occurrence` itself.
-/

namespace DraismaVargas.LocalCases.W2M1kIncomingMatching

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionRamification
open TargetExpansion ResolutionM11 ResolutionM1k FullDimensionalSource WallDegeneration
open W4Assembly W4StableSource W2R1Target SecondEquation
open M11IncomingPartitions
open W2M1kSourceCandidates
open IncomingMatchingCore
open W3Nd2IncomingMemberMatching (pasted NormalizedAgainst normalizedAgainst
  sameBlocks_of_wall_blocks)
open W2M1kIncomingCensus

/-! ## §0  The three-position comparison, with no endpoint assumed joined

`IncomingMatchingCore.wall_blocks_of_dictionary` (item H) assumes the retained
endpoint is joined on the distinguished class -- Base II.1 -- and Figure 33
splits it at two of its three members.  The general shape is one comparison at a
time against a *named* selected partition and a *named* background partition,
with nothing forced to be `mergedPartition`; item H is the special case
`selectedPart := mergedPartition`, `backgroundPart := flagPartition` together
with `hURefines` / `hUJoined`.

This is `W2PIncomingMatching.block_eq_of_split_dictionary` character for
character, restated here.  `IncomingMatchingCore.block_eq_of_anchored_dictionary`
generalizes it, `W2MkkIncomingMatching.wall_blocks_of_split_dictionary` and
item H alike. -/

section Split

variable {degree : ℕ}

theorem block_eq_of_split_dictionary (wallPartition : SheetPartition degree) (root : Fin degree)
    (selectedPart backgroundPart first second : SheetPartition degree)
    (hFirstSelected : ∀ sheet, wallPartition.Rel root sheet →
      first.block sheet = selectedPart.block sheet)
    (hSecondSelected : ∀ sheet, wallPartition.Rel root sheet →
      second.block sheet = selectedPart.block sheet)
    (hFirstBackground : ∀ sheet, ¬ wallPartition.Rel root sheet →
      first.block sheet = backgroundPart.block sheet)
    (hSecondBackground : ∀ sheet, ¬ wallPartition.Rel root sheet →
      second.block sheet = backgroundPart.block sheet)
    (sheet : Fin degree) : first.block sheet = second.block sheet := by
  by_cases hSheet : wallPartition.Rel root sheet
  · exact (hFirstSelected sheet hSheet).trans (hSecondSelected sheet hSheet).symm
  · exact (hFirstBackground sheet hSheet).trans (hSecondBackground sheet hSheet).symm

/-- The same with the background comparison already carried out pointwise -- the
shape `M⁽¹⁾` needs, whose background blocks are the singletons `{sheet}` rather
than the blocks of a named partition. -/
theorem block_eq_of_split_singleton (wallPartition : SheetPartition degree) (root : Fin degree)
    (selectedPart first second : SheetPartition degree)
    (hFirstSelected : ∀ sheet, wallPartition.Rel root sheet →
      first.block sheet = selectedPart.block sheet)
    (hSecondSelected : ∀ sheet, wallPartition.Rel root sheet →
      second.block sheet = selectedPart.block sheet)
    (hFirstBackground : ∀ sheet, ¬ wallPartition.Rel root sheet →
      first.block sheet = {sheet})
    (hSecondBackground : ∀ sheet, ¬ wallPartition.Rel root sheet →
      second.block sheet = {sheet})
    (sheet : Fin degree) : first.block sheet = second.block sheet := by
  by_cases hSheet : wallPartition.Rel root sheet
  · exact (hFirstSelected sheet hSheet).trans (hSecondSelected sheet hSheet).symm
  · exact (hFirstBackground sheet hSheet).trans (hSecondBackground sheet hSheet).symm

end Split


/-! ## §1  The six block-dictionary facts of each Figure 33 member

Three on the distinguished class `A₀` and three off it, per member.  Everything
here is about the *outgoing* member over the wall datum; nothing about an
incoming cover enters. -/

section MemberDictionary

variable {wallTarget : CFGraph} {degree : ℕ} {wall : wallTarget.V}
  {wallData : GluingDatum wallTarget degree} {wallStar : TwoStar wallTarget wall}
  {wallBlock : WallBlock wallData wall}
  {wallProfile : W2R2SourceProfile.SourceProfile wallData wallStar wallBlock}

/-- An anchor of the distinguished block lies in the first pinned sheet's wall
class: `A₀` is `pinSheet wallProfile 0`'s own block. -/
theorem repr_rel_pinSheet {sheet : Fin degree}
    (hSel : (wallData.vertexPartition wall).Rel wallBlock.1 sheet) :
    (wallData.vertexPartition wall).Rel (pinSheet wallProfile 0)
      ((wallData.vertexPartition wall).repr sheet) :=
  (((pinSheet_rel 0).symm.trans hSel).trans
    ((wallData.vertexPartition wall).rel_repr_right sheet))

/-- The mirror: off `A₀` the representative is off the pinned sheet's class. -/
theorem repr_not_rel_pinSheet {sheet : Fin degree}
    (hOff : ¬ (wallData.vertexPartition wall).Rel wallBlock.1 sheet) :
    ¬ (wallData.vertexPartition wall).Rel (pinSheet wallProfile 0)
      ((wallData.vertexPartition wall).repr sheet) := fun hRel ↦
  hOff (((pinSheet_rel 0).trans hRel).trans ((wallData.vertexPartition wall).rel_repr_left sheet))

/-! ### `M⁽¹⁾`: Base I.a retains one pair at the target leaf -/

/-- Figure 33's `M⁽¹⁾` local resolution on `A₀`. -/
noncomputable def leafSelected (pair : LeafPair wallProfile) : LocalResolution degree :=
  firstResolution (wallData.vertexPartition wall) (pinSheet wallProfile 0) pair.second
    pair.ne_second pair.rel_second

theorem leaf_pasted_left_selected (input : W2SourceInput wallData wallStar)
    (shape : Shape wallProfile) (pair : LeafPair wallProfile) {sheet : Fin degree}
    (hSel : (wallData.vertexPartition wall).Rel wallBlock.1 sheet) :
    (pasted (LeafPair.candidate input shape pair)).left.block sheet =
      (leafSelected pair).left.block sheet := by
  show (LocalResolution.pasteLeft (wallData.vertexPartition wall)
    (LeafPair.candidate input shape pair).resolution
    (LeafPair.candidate input shape pair).contracts).block sheet = _
  unfold LocalResolution.pasteLeft
  rw [SheetPartition.paste_block, W2M1kLeaves.leaf_resolution_selected input shape pair _
    (repr_rel_pinSheet hSel)]
  rfl

theorem leaf_pasted_right_selected (input : W2SourceInput wallData wallStar)
    (shape : Shape wallProfile) (pair : LeafPair wallProfile) {sheet : Fin degree}
    (hSel : (wallData.vertexPartition wall).Rel wallBlock.1 sheet) :
    (pasted (LeafPair.candidate input shape pair)).right.block sheet =
      (leafSelected pair).right.block sheet := by
  show (LocalResolution.pasteRight (wallData.vertexPartition wall)
    (LeafPair.candidate input shape pair).resolution
    (LeafPair.candidate input shape pair).contracts).block sheet = _
  unfold LocalResolution.pasteRight
  rw [SheetPartition.paste_block, W2M1kLeaves.leaf_resolution_selected input shape pair _
    (repr_rel_pinSheet hSel)]
  rfl

theorem leaf_pasted_newEdge_selected (input : W2SourceInput wallData wallStar)
    (shape : Shape wallProfile) (pair : LeafPair wallProfile) {sheet : Fin degree}
    (hSel : (wallData.vertexPartition wall).Rel wallBlock.1 sheet) :
    (pasted (LeafPair.candidate input shape pair)).newEdge.block sheet =
      (leafSelected pair).newEdge.block sheet := by
  show (LocalResolution.pasteNewEdge (wallData.vertexPartition wall)
    (LeafPair.candidate input shape pair).resolution
    (LeafPair.candidate input shape pair).contracts).block sheet = _
  unfold LocalResolution.pasteNewEdge
  rw [SheetPartition.paste_block, W2M1kLeaves.leaf_resolution_selected input shape pair _
    (repr_rel_pinSheet hSel)]
  rfl

/-- Off `A₀` the target leaf is discrete: the background resolution's left
endpoint is `splitBlock`. -/
theorem leaf_pasted_left_background (input : W2SourceInput wallData wallStar)
    (shape : Shape wallProfile) (pair : LeafPair wallProfile) {sheet : Fin degree}
    (hOff : ¬ (wallData.vertexPartition wall).Rel wallBlock.1 sheet) :
    (pasted (LeafPair.candidate input shape pair)).left.block sheet = {sheet} := by
  show (LocalResolution.pasteLeft (wallData.vertexPartition wall)
    (LeafPair.candidate input shape pair).resolution
    (LeafPair.candidate input shape pair).contracts).block sheet = _
  unfold LocalResolution.pasteLeft
  rw [SheetPartition.paste_block, W2M1kLeaves.leaf_resolution_background input shape pair _
    (repr_not_rel_pinSheet hOff)]
  show ((wallData.vertexPartition wall).splitBlock
    ((wallData.vertexPartition wall).repr sheet)).block sheet = _
  exact (wallData.vertexPartition wall).splitBlock_block_of_rel _ sheet
    ((wallData.vertexPartition wall).rel_repr_left sheet)

/-- Off `A₀` the trivalent endpoint keeps the whole wall block. -/
theorem leaf_pasted_right_background (input : W2SourceInput wallData wallStar)
    (shape : Shape wallProfile) (pair : LeafPair wallProfile) {sheet : Fin degree}
    (hOff : ¬ (wallData.vertexPartition wall).Rel wallBlock.1 sheet) :
    (pasted (LeafPair.candidate input shape pair)).right.block sheet =
      (wallData.vertexPartition wall).block sheet := by
  show (LocalResolution.pasteRight (wallData.vertexPartition wall)
    (LeafPair.candidate input shape pair).resolution
    (LeafPair.candidate input shape pair).contracts).block sheet = _
  unfold LocalResolution.pasteRight
  rw [SheetPartition.paste_block, W2M1kLeaves.leaf_resolution_background input shape pair _
    (repr_not_rel_pinSheet hOff)]
  rfl

/-- Off `A₀` every background new occurrence is a singleton: this is why they
are all pruned (`W2M1kLeaves.leaf_new_background_dangling`). -/
theorem leaf_pasted_newEdge_background (input : W2SourceInput wallData wallStar)
    (shape : Shape wallProfile) (pair : LeafPair wallProfile) {sheet : Fin degree}
    (hOff : ¬ (wallData.vertexPartition wall).Rel wallBlock.1 sheet) :
    (pasted (LeafPair.candidate input shape pair)).newEdge.block sheet = {sheet} := by
  show (LocalResolution.pasteNewEdge (wallData.vertexPartition wall)
    (LeafPair.candidate input shape pair).resolution
    (LeafPair.candidate input shape pair).contracts).block sheet = _
  unfold LocalResolution.pasteNewEdge
  rw [SheetPartition.paste_block, W2M1kLeaves.leaf_resolution_background input shape pair _
    (repr_not_rel_pinSheet hOff)]
  show ((wallData.vertexPartition wall).splitBlock
    ((wallData.vertexPartition wall).repr sheet)).block sheet = _
  exact (wallData.vertexPartition wall).splitBlock_block_of_rel _ sheet
    ((wallData.vertexPartition wall).rel_repr_left sheet)

/-! ### `M⁽²⁾`: Base II.2.2.M detaches one pinned sheet at each endpoint -/

/-- Figure 33's `M⁽²⁾` local resolution on `A₀`. -/
noncomputable def dividedSelected (divided : DividedData wallProfile) : LocalResolution degree :=
  secondResolution (wallData.vertexPartition wall) (pinSheet wallProfile 0)
    (pinSheet wallProfile 1) divided.third (W2M1kStableGraph.pin_rel_pin wallProfile 0 1)
    divided.rel_third divided.pins_ne divided.ne_first divided.ne_second

theorem divided_pasted_left_selected (shape : Shape wallProfile)
    (divided : DividedData wallProfile) {sheet : Fin degree}
    (hSel : (wallData.vertexPartition wall).Rel wallBlock.1 sheet) :
    (pasted (DividedData.candidate shape divided)).left.block sheet =
      (dividedSelected divided).left.block sheet := by
  show (LocalResolution.pasteLeft (wallData.vertexPartition wall)
    (DividedData.candidate shape divided).resolution
    (DividedData.candidate shape divided).contracts).block sheet = _
  unfold LocalResolution.pasteLeft
  rw [SheetPartition.paste_block, W2M1kStableGraph.divided_resolution shape divided _
    (repr_rel_pinSheet hSel)]
  rfl

theorem divided_pasted_right_selected (shape : Shape wallProfile)
    (divided : DividedData wallProfile) {sheet : Fin degree}
    (hSel : (wallData.vertexPartition wall).Rel wallBlock.1 sheet) :
    (pasted (DividedData.candidate shape divided)).right.block sheet =
      (dividedSelected divided).right.block sheet := by
  show (LocalResolution.pasteRight (wallData.vertexPartition wall)
    (DividedData.candidate shape divided).resolution
    (DividedData.candidate shape divided).contracts).block sheet = _
  unfold LocalResolution.pasteRight
  rw [SheetPartition.paste_block, W2M1kStableGraph.divided_resolution shape divided _
    (repr_rel_pinSheet hSel)]
  rfl

theorem divided_pasted_newEdge_selected (shape : Shape wallProfile)
    (divided : DividedData wallProfile) {sheet : Fin degree}
    (hSel : (wallData.vertexPartition wall).Rel wallBlock.1 sheet) :
    (pasted (DividedData.candidate shape divided)).newEdge.block sheet =
      (dividedSelected divided).newEdge.block sheet := by
  show (LocalResolution.pasteNewEdge (wallData.vertexPartition wall)
    (DividedData.candidate shape divided).resolution
    (DividedData.candidate shape divided).contracts).block sheet = _
  unfold LocalResolution.pasteNewEdge
  rw [SheetPartition.paste_block, W2M1kStableGraph.divided_resolution shape divided _
    (repr_rel_pinSheet hSel)]
  rfl

/-- Off `A₀` `M⁽²⁾` keeps the whole wall block at both endpoints and on the new
edge; `W2M1kStableLift` proved all three. -/
theorem divided_pasted_left_background (shape : Shape wallProfile)
    (divided : DividedData wallProfile) {sheet : Fin degree}
    (hOff : ¬ (wallData.vertexPartition wall).Rel wallBlock.1 sheet) :
    (pasted (DividedData.candidate shape divided)).left.block sheet =
      (wallData.vertexPartition wall).block sheet :=
  W2M1kStableLift.divided_pasted_left_block shape divided hOff

theorem divided_pasted_right_background (shape : Shape wallProfile)
    (divided : DividedData wallProfile) {sheet : Fin degree}
    (hOff : ¬ (wallData.vertexPartition wall).Rel wallBlock.1 sheet) :
    (pasted (DividedData.candidate shape divided)).right.block sheet =
      (wallData.vertexPartition wall).block sheet :=
  W2M1kStableLift.divided_pasted_right_block shape divided hOff

theorem divided_pasted_newEdge_background (shape : Shape wallProfile)
    (divided : DividedData wallProfile) {sheet : Fin degree}
    (hOff : ¬ (wallData.vertexPartition wall).Rel wallBlock.1 sheet) :
    (pasted (DividedData.candidate shape divided)).newEdge.block sheet =
      (wallData.vertexPartition wall).block sheet :=
  W2M1kStableLift.divided_pasted_newEdge_block shape divided hOff

/-! ### `M⁽³⁾`: Base II.1.M keeps the whole wall partition everywhere -/

theorem joined_pasted_left_block (geometry : GlobalM1k.Geometry wallData wall)
    (sheet : Fin degree) :
    (pasted (joinedCandidate wallStar geometry)).left.block sheet =
      (wallData.vertexPartition wall).block sheet :=
  congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
    (W2M1kStableGraph.joined_pastedSide geometry false)

theorem joined_pasted_right_block (geometry : GlobalM1k.Geometry wallData wall)
    (sheet : Fin degree) :
    (pasted (joinedCandidate wallStar geometry)).right.block sheet =
      (wallData.vertexPartition wall).block sheet :=
  congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
    (W2M1kStableGraph.joined_pastedSide geometry true)

theorem joined_pasted_newEdge_block (geometry : GlobalM1k.Geometry wallData wall)
    (sheet : Fin degree) :
    (pasted (joinedCandidate wallStar geometry)).newEdge.block sheet =
      (wallData.vertexPartition wall).block sheet :=
  congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
    (W2M1kStableGraph.joined_pasted_newEdge geometry)

end MemberDictionary


/-! ## §2  The two named censuses

`SelectedCensus` says what the incoming cover's three wall positions look like
**on the distinguished block** `A₀`, at a named pair of restored endpoints.
`LeafBackgroundCensus` says what they look like off `A₀` at a `(1,3)` wall; off
`A₀` at a `(2,2)` wall the `r = 0` census of `W2M1kIncomingCensus` §6 already
settles them. -/

section Censuses

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
  {block : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}

/-- The wall datum's partition at the merged vertex is the merged partition,
read at one sheet. -/
theorem merged_block_eq (sheet : Fin degree) :
    ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block sheet =
      (mergedPartition data a b).block sheet :=
  congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
    (contractDatum_vertexPartition_merge data hc hab hOne)

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

/-- **The selected-class half of the incoming census**, at a named pair of
restored endpoints.  A cover satisfying this at a Figure 33 member's triple *is*
that member at the wall, once the background census is added. -/
structure SelectedCensus (block : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (u v : target.V)
    (selectedLeft selectedRight selectedNew : SheetPartition degree) : Prop where
  /-- What the retained endpoint carries on `A₀`. -/
  left : ∀ sheet, (mergedPartition data a b).Rel block.1 sheet →
    (data.vertexPartition u).block sheet = selectedLeft.block sheet
  /-- What the fresh endpoint carries on `A₀`. -/
  right : ∀ sheet, (mergedPartition data a b).Rel block.1 sheet →
    (data.vertexPartition v).block sheet = selectedRight.block sheet
  /-- What the contracted occurrence carries on `A₀`. -/
  new : ∀ sheet, (mergedPartition data a b).Rel block.1 sheet →
    (data.edgePartition contracted).block sheet = selectedNew.block sheet

/-- **The `r = 0` background census at a `(1,3)` wall.**  The two `T_2` members
get this from the divalent-endpoint `AnyBlock` lemmas; at Base I.a it comes
from the leaf-endpoint ones (`W2M1kLeafBackground.leafBackgroundCensus`).  See
this module's docstring for the argument. -/
structure LeafBackgroundCensus (block : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (u v : target.V) : Prop where
  /-- The target leaf is discrete off `A₀`. -/
  left : ∀ sheet, ¬ (mergedPartition data a b).Rel block.1 sheet →
    (data.vertexPartition u).block sheet = {sheet}
  /-- The trivalent endpoint carries the whole wall block off `A₀`. -/
  right : ∀ sheet, ¬ (mergedPartition data a b).Rel block.1 sheet →
    (data.vertexPartition v).block sheet = (mergedPartition data a b).block sheet
  /-- The contracted occurrence is discrete off `A₀`. -/
  new : ∀ sheet, ¬ (mergedPartition data a b).Rel block.1 sheet →
    (data.edgePartition contracted).block sheet = {sheet}

end Censuses


/-! ## §3  The three wall comparisons, one member at a time -/

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

/-- **`M⁽¹⁾`'s three wall comparisons.**  Base I.a's selected-class census and
the `(1,3)` background census identify the incoming cover's wall data with
`W2M1kSourceCandidates.LeafPair.candidate`'s pasted local resolution. -/
theorem leaf_wall_blocks (shape : Shape profile) (pair : LeafPair profile)
    (selected : SelectedCensus data hc hab hOne block (leafEnd hc hab hOne star)
      (branchEnd hc hab hOne star) (leafSelected pair).left (leafSelected pair).right
      (leafSelected pair).newEdge)
    (background : LeafBackgroundCensus data hc hab hOne block (leafEnd hc hab hOne star)
      (branchEnd hc hab hOne star)) :
    (∀ sheet, (data.vertexPartition (leafEnd hc hab hOne star)).block sheet =
        (pasted (LeafPair.candidate input shape pair)).left.block sheet) ∧
      (∀ sheet, (data.vertexPartition (branchEnd hc hab hOne star)).block sheet =
        (pasted (LeafPair.candidate input shape pair)).right.block sheet) ∧
      (∀ sheet, (data.edgePartition contracted).block sheet =
        (pasted (LeafPair.candidate input shape pair)).newEdge.block sheet) := by
  refine ⟨?_, ?_, ?_⟩
  · exact block_eq_of_split_singleton (mergedPartition data a b) block.1
      (leafSelected pair).left _ _ selected.left
      (fun _sheet hSel ↦ leaf_pasted_left_selected input shape pair
        (on_wall_of_on_merged data hc hab hOne hSel))
      background.left
      (fun _sheet hOff ↦ leaf_pasted_left_background input shape pair
        (off_wall_of_off_merged data hc hab hOne hOff))
  · exact block_eq_of_split_dictionary (mergedPartition data a b) block.1
      (leafSelected pair).right (mergedPartition data a b) _ _ selected.right
      (fun _sheet hSel ↦ leaf_pasted_right_selected input shape pair
        (on_wall_of_on_merged data hc hab hOne hSel))
      background.right
      (fun sheet hOff ↦ (leaf_pasted_right_background input shape pair
        (off_wall_of_off_merged data hc hab hOne hOff)).trans
        (merged_block_eq data hc hab hOne sheet))
  · exact block_eq_of_split_singleton (mergedPartition data a b) block.1
      (leafSelected pair).newEdge _ _ selected.new
      (fun _sheet hSel ↦ leaf_pasted_newEdge_selected input shape pair
        (on_wall_of_on_merged data hc hab hOne hSel))
      background.new
      (fun _sheet hOff ↦ leaf_pasted_newEdge_background input shape pair
        (off_wall_of_off_merged data hc hab hOne hOff))

include fullDim hForest input profile

/-- **`M⁽²⁾`'s three wall comparisons.**  Base II.2.2.M's selected-class census
plus the `T_2` background census. -/
theorem divided_wall_blocks
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ block → (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
    (hRightCard : (GluingDatum.incidentEdges b).card = 2)
    (shape : Shape profile) (divided : DividedData profile)
    (selected : SelectedCensus data hc hab hOne block (zeroEnd hc hab hOne star)
      (oneEnd hc hab hOne star) (dividedSelected divided).left (dividedSelected divided).right
      (dividedSelected divided).newEdge) :
    (∀ sheet, (data.vertexPartition (zeroEnd hc hab hOne star)).block sheet =
        (pasted (DividedData.candidate shape divided)).left.block sheet) ∧
      (∀ sheet, (data.vertexPartition (oneEnd hc hab hOne star)).block sheet =
        (pasted (DividedData.candidate shape divided)).right.block sheet) ∧
      (∀ sheet, (data.edgePartition contracted).block sheet =
        (pasted (DividedData.candidate shape divided)).newEdge.block sheet) := by
  refine ⟨?_, ?_, ?_⟩
  · exact block_eq_of_split_dictionary (mergedPartition data a b) block.1
      (dividedSelected divided).left
      ((contractDatum data hc hab hOne).edgePartition (star.edge 0)) _ _ selected.left
      (fun _sheet hSel ↦ divided_pasted_left_selected shape divided
        (on_wall_of_on_merged data hc hab hOne hSel))
      (fun sheet hOff ↦ (background_edge_block_zeroEnd data hc hab hOne fullDim hForest
          hBackground hLeftCard hRightCard (flagEdge hc hab hOne star)
          (flagEdge_mem_zeroEnd hc hab hOne star) sheet hOff).symm.trans
        (flag_block data hc hab hOne star sheet))
      (fun sheet hOff ↦ (divided_pasted_left_background shape divided
          (off_wall_of_off_merged data hc hab hOne hOff)).trans
        (W2M1kStableLift.wall_block_eq_zero_block input profile
          (off_wall_of_off_merged data hc hab hOne hOff)))
  · exact block_eq_of_split_dictionary (mergedPartition data a b) block.1
      (dividedSelected divided).right (mergedPartition data a b) _ _ selected.right
      (fun _sheet hSel ↦ divided_pasted_right_selected shape divided
        (on_wall_of_on_merged data hc hab hOne hSel))
      (fun sheet hOff ↦ background_joined_block_oneEnd data hc hab hOne fullDim hForest
        hBackground hLeftCard hRightCard sheet hOff)
      (fun sheet hOff ↦ (divided_pasted_right_background shape divided
          (off_wall_of_off_merged data hc hab hOne hOff)).trans
        (merged_block_eq data hc hab hOne sheet))
  · exact block_eq_of_split_dictionary (mergedPartition data a b) block.1
      (dividedSelected divided).newEdge
      ((contractDatum data hc hab hOne).edgePartition (star.edge 0)) _ _ selected.new
      (fun _sheet hSel ↦ divided_pasted_newEdge_selected shape divided
        (on_wall_of_on_merged data hc hab hOne hSel))
      (fun sheet hOff ↦ ((background_edge_block_zeroEnd data hc hab hOne fullDim hForest
          hBackground hLeftCard hRightCard contracted
          (contracted_mem_zeroEnd hc hab hOne star) sheet hOff).trans
        ((background_edge_block_zeroEnd data hc hab hOne fullDim hForest hBackground
          hLeftCard hRightCard (flagEdge hc hab hOne star)
          (flagEdge_mem_zeroEnd hc hab hOne star) sheet hOff).symm)).trans
        (flag_block data hc hab hOne star sheet))
      (fun sheet hOff ↦ (divided_pasted_newEdge_background shape divided
          (off_wall_of_off_merged data hc hab hOne hOff)).trans
        (W2M1kStableLift.wall_block_eq_zero_block input profile
          (off_wall_of_off_merged data hc hab hOne hOff)))

/-- **`M⁽³⁾`'s three wall comparisons.**  Base II.1.M's selected-class census
plus the same `T_2` background census. -/
theorem joined_wall_blocks
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ block → (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
    (hRightCard : (GluingDatum.incidentEdges b).card = 2)
    (geometry : GlobalM1k.Geometry (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (selected : SelectedCensus data hc hab hOne block (zeroEnd hc hab hOne star)
      (oneEnd hc hab hOne star) (mergedPartition data a b) (mergedPartition data a b)
      (mergedPartition data a b)) :
    (∀ sheet, (data.vertexPartition (zeroEnd hc hab hOne star)).block sheet =
        (pasted (joinedCandidate star geometry)).left.block sheet) ∧
      (∀ sheet, (data.vertexPartition (oneEnd hc hab hOne star)).block sheet =
        (pasted (joinedCandidate star geometry)).right.block sheet) ∧
      (∀ sheet, (data.edgePartition contracted).block sheet =
        (pasted (joinedCandidate star geometry)).newEdge.block sheet) := by
  refine ⟨?_, ?_, ?_⟩
  · exact block_eq_of_split_dictionary (mergedPartition data a b) block.1
      (mergedPartition data a b)
      ((contractDatum data hc hab hOne).edgePartition (star.edge 0)) _ _ selected.left
      (fun sheet _hSel ↦ (joined_pasted_left_block geometry sheet).trans
        (merged_block_eq data hc hab hOne sheet))
      (fun sheet hOff ↦ (background_edge_block_zeroEnd data hc hab hOne fullDim hForest
          hBackground hLeftCard hRightCard (flagEdge hc hab hOne star)
          (flagEdge_mem_zeroEnd hc hab hOne star) sheet hOff).symm.trans
        (flag_block data hc hab hOne star sheet))
      (fun sheet hOff ↦ (joined_pasted_left_block geometry sheet).trans
        (W2M1kStableLift.wall_block_eq_zero_block input profile
          (off_wall_of_off_merged data hc hab hOne hOff)))
  · exact block_eq_of_split_dictionary (mergedPartition data a b) block.1
      (mergedPartition data a b) (mergedPartition data a b) _ _ selected.right
      (fun sheet _hSel ↦ (joined_pasted_right_block geometry sheet).trans
        (merged_block_eq data hc hab hOne sheet))
      (fun sheet hOff ↦ background_joined_block_oneEnd data hc hab hOne fullDim hForest
        hBackground hLeftCard hRightCard sheet hOff)
      (fun sheet _hOff ↦ (joined_pasted_right_block geometry sheet).trans
        (merged_block_eq data hc hab hOne sheet))
  · exact block_eq_of_split_dictionary (mergedPartition data a b) block.1
      (mergedPartition data a b)
      ((contractDatum data hc hab hOne).edgePartition (star.edge 0)) _ _ selected.new
      (fun sheet _hSel ↦ (joined_pasted_newEdge_block geometry sheet).trans
        (merged_block_eq data hc hab hOne sheet))
      (fun sheet hOff ↦ ((background_edge_block_zeroEnd data hc hab hOne fullDim hForest
          hBackground hLeftCard hRightCard contracted
          (contracted_mem_zeroEnd hc hab hOne star) sheet hOff).trans
        ((background_edge_block_zeroEnd data hc hab hOne fullDim hForest hBackground
          hLeftCard hRightCard (flagEdge hc hab hOne star)
          (flagEdge_mem_zeroEnd hc hab hOne star) sheet hOff).symm)).trans
        (flag_block data hc hab hOne star sheet))
      (fun sheet hOff ↦ (joined_pasted_newEdge_block geometry sheet).trans
        (W2M1kStableLift.wall_block_eq_zero_block input profile
          (off_wall_of_off_merged data hc hab hOne hOff)))

end WallBlocks


/-! ## §4  The whole-cover exhaustion

`W3Nd2IncomingMemberMatching.sameBlocks_of_wall_blocks` does the vertex and
occurrence exhaustion once: away from the contracted wall every transported
partition is literally the wall datum's own and so is the member's, and at the
wall there are exactly the three comparisons of §3.  Nothing about Figure 33
enters it, so it is consumed verbatim -- once per member, with that member's own
placement. -/

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

/-- `M⁽¹⁾`'s target placement, at a `T_∅` incoming wall. -/
theorem leafPlacement (shape : Shape profile) (pair : LeafPair profile)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
      (GluingDatum.incidentEdges b).card = 1) :
    Placement hc hab hOne (LeafPair.candidate input shape pair).right :=
  true_placement hc hab hOne star hLeaf

/-- `M⁽²⁾`'s target placement, at a `T_2` incoming wall. -/
theorem dividedPlacement (shape : Shape profile) (divided : DividedData profile)
    (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
    (hRightCard : (GluingDatum.incidentEdges b).card = 2) :
    Placement hc hab hOne (DividedData.candidate shape divided).right :=
  star_placement hc hab hOne star hLeftCard hRightCard

/-- `M⁽³⁾`'s target placement, at a `T_2` incoming wall. -/
theorem joinedPlacement (geometry : GlobalM1k.Geometry (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
    (hRightCard : (GluingDatum.incidentEdges b).card = 2) :
    Placement hc hab hOne (joinedCandidate star geometry).right :=
  star_placement hc hab hOne star hLeftCard hRightCard

include fullDim input

/-- **`M⁽¹⁾` is the incoming cover, partition by partition.** -/
theorem leaf_sameBlocks (shape : Shape profile) (pair : LeafPair profile)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
      (GluingDatum.incidentEdges b).card = 1)
    (selected : SelectedCensus data hc hab hOne block (leafEnd hc hab hOne star)
      (branchEnd hc hab hOne star) (leafSelected pair).left (leafSelected pair).right
      (leafSelected pair).newEdge)
    (background : LeafBackgroundCensus data hc hab hOne block (leafEnd hc hab hOne star)
      (branchEnd hc hab hOne star)) :
    (∀ vertex, ((GluingTransport.transport (memberTargetIso data hc hab hOne
          (LeafPair.candidate input shape pair)
          (leafPlacement data hc hab hOne input profile shape pair hLeaf))
        data).vertexPartition vertex).SameBlocks
      ((LeafPair.candidate input shape pair).datum.vertexPartition vertex)) ∧
    (∀ edge, ((GluingTransport.transport (memberTargetIso data hc hab hOne
          (LeafPair.candidate input shape pair)
          (leafPlacement data hc hab hOne input profile shape pair hLeaf))
        data).edgePartition edge).SameBlocks
      ((LeafPair.candidate input shape pair).datum.edgePartition edge)) := by
  obtain ⟨hLeftWall, hRightWall, hNewWall⟩ := leaf_wall_blocks data hc hab hOne input profile
    shape pair selected background
  obtain ⟨hOld, hFresh⟩ := leaf_transported_endpoints data hc hab hOne star hLeaf
    (leafPlacement data hc hab hOne input profile shape pair hLeaf)
  exact sameBlocks_of_wall_blocks data hc hab hOne fullDim.targetConnected fullDim.targetGenus
    (LeafPair.candidate input shape pair)
    (leafPlacement data hc hab hOne input profile shape pair hLeaf)
    (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
      hOld).trans (hLeftWall sheet))
    (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
      hFresh).trans (hRightWall sheet))
    hNewWall

include hForest profile

/-- **`M⁽²⁾` is the incoming cover, partition by partition.** -/
theorem divided_sameBlocks
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ block → (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
    (hRightCard : (GluingDatum.incidentEdges b).card = 2)
    (shape : Shape profile) (divided : DividedData profile)
    (selected : SelectedCensus data hc hab hOne block (zeroEnd hc hab hOne star)
      (oneEnd hc hab hOne star) (dividedSelected divided).left (dividedSelected divided).right
      (dividedSelected divided).newEdge) :
    (∀ vertex, ((GluingTransport.transport (memberTargetIso data hc hab hOne
          (DividedData.candidate shape divided)
          (dividedPlacement data hc hab hOne profile shape divided hLeftCard hRightCard))
        data).vertexPartition vertex).SameBlocks
      ((DividedData.candidate shape divided).datum.vertexPartition vertex)) ∧
    (∀ edge, ((GluingTransport.transport (memberTargetIso data hc hab hOne
          (DividedData.candidate shape divided)
          (dividedPlacement data hc hab hOne profile shape divided hLeftCard hRightCard))
        data).edgePartition edge).SameBlocks
      ((DividedData.candidate shape divided).datum.edgePartition edge)) := by
  obtain ⟨hLeftWall, hRightWall, hNewWall⟩ := divided_wall_blocks data hc hab hOne fullDim
    hForest input profile hBackground hLeftCard hRightCard shape divided selected
  obtain ⟨hOld, hFresh⟩ := transported_endpoints data hc hab hOne star hLeftCard hRightCard
    (dividedPlacement data hc hab hOne profile shape divided hLeftCard hRightCard)
  exact sameBlocks_of_wall_blocks data hc hab hOne fullDim.targetConnected fullDim.targetGenus
    (DividedData.candidate shape divided)
    (dividedPlacement data hc hab hOne profile shape divided hLeftCard hRightCard)
    (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
      hOld).trans (hLeftWall sheet))
    (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
      hFresh).trans (hRightWall sheet))
    hNewWall

/-- **`M⁽³⁾` is the incoming cover, partition by partition.** -/
theorem joined_sameBlocks
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ block → (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
    (hRightCard : (GluingDatum.incidentEdges b).card = 2)
    (geometry : GlobalM1k.Geometry (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (selected : SelectedCensus data hc hab hOne block (zeroEnd hc hab hOne star)
      (oneEnd hc hab hOne star) (mergedPartition data a b) (mergedPartition data a b)
      (mergedPartition data a b)) :
    (∀ vertex, ((GluingTransport.transport (memberTargetIso data hc hab hOne
          (joinedCandidate star geometry)
          (joinedPlacement data hc hab hOne geometry hLeftCard hRightCard))
        data).vertexPartition vertex).SameBlocks
      ((joinedCandidate star geometry).datum.vertexPartition vertex)) ∧
    (∀ edge, ((GluingTransport.transport (memberTargetIso data hc hab hOne
          (joinedCandidate star geometry)
          (joinedPlacement data hc hab hOne geometry hLeftCard hRightCard))
        data).edgePartition edge).SameBlocks
      ((joinedCandidate star geometry).datum.edgePartition edge)) := by
  obtain ⟨hLeftWall, hRightWall, hNewWall⟩ := joined_wall_blocks data hc hab hOne fullDim
    hForest input profile hBackground hLeftCard hRightCard geometry selected
  obtain ⟨hOld, hFresh⟩ := transported_endpoints data hc hab hOne star hLeftCard hRightCard
    (joinedPlacement data hc hab hOne geometry hLeftCard hRightCard)
  exact sameBlocks_of_wall_blocks data hc hab hOne fullDim.targetConnected fullDim.targetGenus
    (joinedCandidate star geometry)
    (joinedPlacement data hc hab hOne geometry hLeftCard hRightCard)
    (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
      hOld).trans (hLeftWall sheet))
    (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
      hFresh).trans (hRightWall sheet))
    hNewWall

end SameBlocks


end DraismaVargas.LocalCases.W2M1kIncomingMatching
