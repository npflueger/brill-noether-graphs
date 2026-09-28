import DraismaVargas.LocalCases.W2R1SourceCandidates
import DraismaVargas.LocalCases.LimitChainCore

/-!
# Survival and the endpoint census for the two `w2-r1` members, at **both**
ramification-one blocks

Source: Draisma–Vargas Part I, arXiv:1909.12924, case `{w2-r1}`, sub-cases `{w2-r1-nd3}`
(Figure 37) and `{w2-r1-nd2}` (Figure 38), and the proof of Equation (*) for
the case, whose display is Equation (10).  Ambient hypotheses are those of
`{w2}`: `val(w₀) = 2`, `ch(w₀) = 2`, the constant `s`.

`W2R1SourceCandidates` builds Equation (10)'s two coupled members
(`Pair.candidate 0`, `Pair.candidate 1`) over one gluing datum and **two**
ramification-one blocks, with validity, source genus, both new endpoint
valencies and every Figure 37/38 displayed index.  This module is the first
step from that geometry towards Equation (10) -- the analogue of
`W2MkkStableGraph` for `{w2-r2-nd3-M-kk}`: **which occurrences of each member
survive pruning, what the complete surviving star at each new endpoint is, and
which stable row each surviving new occurrence joins** -- at `A₀`, at `B₀` and
over the background.  The lift, the row descent, the limit matrices and
Equation (10) itself are in the `W2R1*` modules that build on this one.

## What makes this case two-block

Part I opens the proof of Equation (*) for this case with *"There is another vertex `B₀`
above `w₀` with `r₀(B₀) = 1`.  The previous analysis holds for `B₀`, with
notation entirely analogous"*, and Equation (10) sums **two** blocks'
contributions,
`c⁽ⁱ⁾ = σ⁽ⁱ⁾(J_{A₀},1) + σ⁽ⁱ⁾(J_{B₀},1) + s`, `c⁽¹⁾ + c⁽²⁾ = σ₀(2) + σ₀(3) = 0`.
So the census here is **the same analysis run at each of two blocks**, and the
whole of §4--§7 is stated once for an arbitrary `BlockMember` and instantiated
twice per member (`firstMember`, `secondMember` in §9).  Two things do not
factor through one block, and they are the content of this module:

* **the background** is `≠ A₀` **and** `≠ B₀` (§8), where every earlier
  census in this repository reads `≠ input.distinguishedBlock`; and
* **a member has two branch vertices, on opposite sides of the new edge**
  (§9, `branch_positions_ne`).  That is `ch u = ch v = 1` in the proof of
  Equation (*) for this case, and it is this case's genuinely new phenomenon.

## Why the single-block core does not apply, with a machine-checked proof

**`LimitChainCore` §0--§2 scope; §3--§4 do not, and cannot be made to.**

*What scopes.*  A `{w2-r1}` member retains exactly one wall direction at the
retained endpoint, so `wallCandidate` (§10) exhibits it as a
`LimitChainCore.WallCandidate` with `retainedTarget = star.edge 0`, and the
core's occurrence identities (§0), surviving-star readers (§1) and two-star
incidence counts (§2) are what every proof below runs on.

*What does not.*  `BackgroundShape` is **not** "the member away from one
block".  Its three block clauses pin the background's *shape*: `right_block`
gives the fresh endpoint the whole wall block, `left_block` and
`newEdge_block` give the retained endpoint and the new edge the retained
direction's classes -- so the background's branch vertex is the **fresh** one,
and every theorem of `LimitChainCore.Background` reads the fresh endpoint.
`backgroundClausesAt_iff` (§10) proves, at an arbitrary ramification-one
block, that those three clauses hold **exactly when the member's local
position there is `1`**, i.e. exactly when the branch vertex above that block
is the fresh endpoint -- uniformly in which direction the block is doubled
over, the two configurations failing in different clauses (`left_block` and
`newEdge_block` when `double = 0`, `right_block` when `double = 1`) and
agreeing on the answer.

Since `A₀` sits at `position` and `B₀` at `other position`, and those are
opposite, the consequences at the pair (§11) are:

* `backgroundClauses_first_iff`: the clauses hold at `A₀` iff the member is `1`;
* `backgroundClauses_second_iff`: at `B₀` iff the member is `0`;
* `backgroundClauses_first_or_second`: **exactly one** of the two blocks is
  background-shaped, for every member;
* `not_backgroundClauses_both`: and **never both** -- so no
  `LimitChainCore.BackgroundShape` over a `{w2-r1}` member has both `A₀` and
  `B₀` outside its distinguished block;
* `backgroundClauses_not_uniform`: and the block that can be background is a
  *different* one for the two members, so no family-wide choice exists either.

So the core cannot serve a two-block member, and the census below is
standalone.  The two-block variant of the core is `LimitChainTwoBlock`, and it
differs from the core as follows:

1. `BackgroundShape.selected : Fin degree` is replaced by a *finite set* of
   distinguished anchors (here two), with the three block clauses quantified
   over sheets related to none of them.  Every proof in
   `LimitChainCore.Background` goes through verbatim: each one uses
   `hSheet : ¬ Rel selected sheet` only through `pasted_right_block` and its
   two companions.
2. `GraphData.selectedSide : Bool` and `selectedFlag` are replaced by one per
   distinguished anchor, and `branchImage` is built as a bijection onto the
   *union* of the branch stars.  `branchImage_injective` and
   `exists_branchImage` are where the work is: in the core they case on
   "selected or background", which becomes "which of the distinguished blocks,
   or background".
3. `selected_valency_ne_two` does *not* become per-anchor -- it fails in nd2, as
   `nd2_selected_valency_eq_two` below shows -- and is replaced by
   `selected_consecutive`; `selectedRep` becomes per-anchor, and the two
   `selected_*_pair` fields ask only that the old partner lie in the
   representative's incoming row, since a retained nd2 member's two divalent
   endpoints above one block share one regrown occurrence with different old
   partners.

## The census

Write `A₀` for a ramification-one wall block, `t₂` for the direction carrying
two of its occurrences (`e₁` of index `k₁`, `e₂` of index `k₂`) and `t₃` for
the one carrying `e₃` of index `k₃`, with `k₁ + k₂ = |A₀| = k₃` (case `{w2-r1}`).
`position` is `δ⁽ᵠ⁾(Ã)` read as a wall direction: `card_incident_side` says the
expanded endpoint named by a direction `label` carries **three** incidences
exactly when `label = position` and two otherwise, uniformly in `t₂`'s label.

**Retained member at the block** (`position = t₂`, Figure 37/38 gluing I,
`|e'| = k₃`; §6).  One endpoint per side above the block, one new occurrence.

| endpoint | incidences | nd3 | nd2 |
|---|---|---|---|
| side `t₂` (`= δ⁽ᵠ⁾(Ã)`) | old `e₁`, old `e₂`, new `e'` | 3 -- **branch** | 2 (`e₁` dies) |
| side `t₃` | old `e₃`, new `e'` | 2 | 2 |

**Resolved member at the block** (`position = t₃`, gluing II, `|e'| = k₁`,
`|e''| = k₂`; §7).  The `t₂` side splits into the `e₁` and `e₂` classes.

| endpoint | incidences | nd3 | nd2 |
|---|---|---|---|
| side `t₂` over `e₁` | old `e₁`, new `e'` | 2 | **0 -- both die** |
| side `t₂` over `e₂` | old `e₂`, new `e''` | 2 | 2 |
| side `t₃` (`= δ⁽ᵠ⁾(Ã)`) | old `e₃`, new `e'`, new `e''` | 3 -- **branch** | 2 (`e'` dies) |

**Background** (every wall block that is neither `A₀` nor `B₀`; §8).  Both
those blocks are unramified (`Pair.background`), so each direction contributes
one occurrence, both new endpoints are divalent, and the new occurrence is a
subdivision: it dangles exactly when the same-sheet old occurrence over either
direction does, and shares its row when it survives.

**Rows.**  `e'` of the retained member joins `e₃`'s row; `e''` of the resolved
member joins `e₂`'s row; in nd3 `e'` of the resolved member joins `e₁`'s row.
In nd2 (§12) the endpoint that was trivalent becomes divalent and buys one
identity more in each member, both saying that every surviving new occurrence
above the block lies in the single row carrying `e₂` and `e₃` -- consistent
with `W2R1SourceProfile.SourceProfile.nd2_stablePath_eq` downstairs.

**Both members, both blocks** (§9).  Member `q` is `firstMember` at `A₀` with
position `q` and `secondMember` at `B₀` with position `other q`; every row
above applies at each.  Which of the two tables a given block gets is decided
by `position = doubleLabel` there, so in the *aligned* configuration each
member retains one block and resolves the other, and in the *opposite* one a
member retains or resolves both -- `W2R1SourceCandidates.Pair.aligned_counts`,
`opposite_counts`.  The census is stated so that neither configuration is
assumed.

## The genuinely new phenomena

1. **Two branch vertices per member, on opposite sides** (`branch_positions_ne`,
   `branch_side_ne`).  No earlier member in this repository has more than one.
   It is also exactly what defeats `LimitChainCore.BackgroundShape`.
2. **In `{w2-r1-nd2}` neither member has a branch vertex above the block.**
   `retained_nonDanglingValency_double_nd2` and
   `resolved_nonDanglingValency_single_nd2` are both `2`: the block
   contributes a chain, not a trivalent vertex.  In the resolved member the
   whole `e₁` endpoint is pruned away
   (`resolved_nonDanglingIncident_first_nd2 = ∅`, with `k₁ = 1` from the
   profile's own indices), which is why Figure 38 draws one new occurrence
   of index `k₂` where Figure 37 draws two.
3. Nothing else is new: no second dangling occurrence appears (contrast
   `W2MkkStableGraph`'s pinned sheet), no detachment, and the resolution
   preserves the source genus (`W2R1SourceCandidates.Pair.resolution_euler`).

## The indices of Figure 38

Figure 38's limit box displays `σ₀(J_{A₀},2) = c_h/k₁`,
`σ₀(J_{A₀},3) = c_h/(k₁+1)`.  Here the indices are `k₂` and `k₂+1`, which is
what makes the display below the box balance; this differs from the box as
displayed in Part I.  Nothing here transcribes the box: the nd2 indices come
from the profile's own fields through
`W2R1SourceCandidates.nd2_displayed_indices` (`k₁ = 1`, `k₃ = k₂ + 1`), and
`BlockMember.nd_cases` re-exposes them.

## What is **not** done here

The stable lift (`LimitChainCore.LiftData`'s analogue), the row descent, the
regrown column, the limit matrices, Equation (10) itself, the incoming member,
the certified positive exit, and the stable incidence graph
(`StableGraphIncidence.Equivalence`) -- which needs the two-block `GraphData`
described above.  Also not done: an honest presented family for this case
(that is `W2R1GraphData.family`); the census here is its input, not the
family itself.  No numerical receipt, no
distinctness of stable rows and no `Nodup` hypothesis appears below: a stable
loop may put two survivors at a branch vertex into one row and nothing here
excludes it.

## What is general, and where it lives

* §1 (`pasted_left_block` ... `pasted_newEdge_rel_iff`) reads a pasted
  resolution off one wall block for an arbitrary candidate with a named local
  shape there.  With `memberLocal data star double position` replaced by an
  arbitrary `LocalResolution degree` this is case-free; it belongs beside
  `pasted` in `LimitChainCore` §2.
* §3's `side`, `old_incident` and `new_incident` collapse the core's
  old-endpoint/fresh-endpoint pair into one statement indexed by the wall
  direction, which is what a case whose distinguished direction is *per block*
  needs.  They belong beside `card_incident_oldEndpoint` and
  `card_incident_freshEndpoint` in `LimitChainCore` §2.
* `single_block_eq_wall_block` (§10) is the block-equality form of
  `W2R1SourceCandidates.singlePartition_blockCountWithin`, and belongs in that
  module's §1.
* `BackgroundClausesAt` and `backgroundClausesAt_iff` characterise
  `LimitChainCore.BackgroundShape`'s three block clauses, and belong in
  `LimitChainCore` §3.
-/

namespace DraismaVargas.LocalCases.W2R1StableGraph

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open ResolutionM11 ResolutionCoarseFine
open W2R1SourceCandidates
open LimitChainCore (pasted card_incident_oldEndpoint card_incident_freshEndpoint
  sourceEndpoint_old_eq_of_rel sourceEndpoint_fresh_eq_of_rel
  newSourceEdge_incident_old newSourceEdge_incident_fresh
  oldSourceEdge_ne_newSourceEdge newSourceEdge_eq_iff_rel
  forall_eq_of_card_two forall_eq_of_card_three
  nonDanglingIncident_pair_of_card_two nonDanglingIncident_empty_of_card_two
  nonDanglingIncident_pair_of_card_three nonDanglingIncident_triple_of_card_three
  oldSourceEdge_incident_old survives_iff_of_card_two
  nonDanglingValency_eq_two_of_card_two_of_survives)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## §1  Reading a member off one wall block

Everything below is stated for an arbitrary candidate `C` whose side
assignment is the two-star's own and whose local shape on one named wall
block is `W2R1SourceCandidates.memberLocal double position`.  Both members of
`Pair` satisfy this at **both** ramification-one blocks -- at `A₀` with
`position` and at `B₀` with `other position` -- which is how one block-level
census serves the two blocks. -/

section Local

variable {block : WallBlock data wall} {C : BalancedGlobal.Candidate target degree data wall}

/-- The local shape read at the canonical anchor of the sheet's wall block. -/
theorem resolution_at_repr {double position : Fin 2}
    (hLocal : ∀ anchor, (data.vertexPartition wall).Rel block.1 anchor →
      C.resolution anchor = memberLocal data star double position)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    C.resolution ((data.vertexPartition wall).repr sheet) =
      memberLocal data star double position :=
  hLocal _ (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))

theorem pasted_left_block {double position : Fin 2}
    (hLocal : ∀ anchor, (data.vertexPartition wall).Rel block.1 anchor →
      C.resolution anchor = memberLocal data star double position)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    (pasted C).left.block sheet =
      (memberLocal data star double position).left.block sheet := by
  rw [LocalResolution.pasteLeft_block, resolution_at_repr hLocal hSheet]

theorem pasted_right_block {double position : Fin 2}
    (hLocal : ∀ anchor, (data.vertexPartition wall).Rel block.1 anchor →
      C.resolution anchor = memberLocal data star double position)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    (pasted C).right.block sheet =
      (memberLocal data star double position).right.block sheet := by
  rw [LocalResolution.pasteRight_block, resolution_at_repr hLocal hSheet]

theorem pasted_newEdge_block {double position : Fin 2}
    (hLocal : ∀ anchor, (data.vertexPartition wall).Rel block.1 anchor →
      C.resolution anchor = memberLocal data star double position)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    (pasted C).newEdge.block sheet =
      (memberLocal data star double position).newEdge.block sheet := by
  rw [LocalResolution.pasteNewEdge_block, resolution_at_repr hLocal hSheet]

theorem pasted_newEdge_within_left {double position : Fin 2}
    (hLocal : ∀ anchor, (data.vertexPartition wall).Rel block.1 anchor →
      C.resolution anchor = memberLocal data star double position)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    (pasted C).newEdge.blockCountWithin (pasted C).left sheet =
      (memberLocal data star double position).newEdge.blockCountWithin
        (memberLocal data star double position).left sheet := by
  rw [LocalResolution.paste_newEdge_blockCountWithin_left, resolution_at_repr hLocal hSheet]

theorem pasted_newEdge_within_right {double position : Fin 2}
    (hLocal : ∀ anchor, (data.vertexPartition wall).Rel block.1 anchor →
      C.resolution anchor = memberLocal data star double position)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    (pasted C).newEdge.blockCountWithin (pasted C).right sheet =
      (memberLocal data star double position).newEdge.blockCountWithin
        (memberLocal data star double position).right sheet := by
  rw [LocalResolution.paste_newEdge_blockCountWithin_right, resolution_at_repr hLocal hSheet]

theorem pasted_blockCountWithin_left {double position : Fin 2}
    (hLocal : ∀ anchor, (data.vertexPartition wall).Rel block.1 anchor →
      C.resolution anchor = memberLocal data star double position)
    (fine : SheetPartition degree)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    fine.blockCountWithin (pasted C).left sheet =
      fine.blockCountWithin (memberLocal data star double position).left sheet := by
  rw [LocalResolution.blockCountWithin_paste_left, resolution_at_repr hLocal hSheet]

theorem pasted_blockCountWithin_right {double position : Fin 2}
    (hLocal : ∀ anchor, (data.vertexPartition wall).Rel block.1 anchor →
      C.resolution anchor = memberLocal data star double position)
    (fine : SheetPartition degree)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    fine.blockCountWithin (pasted C).right sheet =
      fine.blockCountWithin (memberLocal data star double position).right sheet := by
  rw [LocalResolution.blockCountWithin_paste_right, resolution_at_repr hLocal hSheet]

theorem pasted_left_rel_iff {double position : Fin 2}
    (hLocal : ∀ anchor, (data.vertexPartition wall).Rel block.1 anchor →
      C.resolution anchor = memberLocal data star double position)
    {first : Fin degree} (hFirst : (data.vertexPartition wall).Rel block.1 first)
    (second : Fin degree) :
    (pasted C).left.Rel first second ↔
      (memberLocal data star double position).left.Rel first second := by
  show (LocalResolution.pasteLeft (data.vertexPartition wall) C.resolution C.contracts).Rel
    first second ↔ _
  unfold LocalResolution.pasteLeft
  rw [SheetPartition.paste_rel_iff, resolution_at_repr hLocal hFirst]

theorem pasted_right_rel_iff {double position : Fin 2}
    (hLocal : ∀ anchor, (data.vertexPartition wall).Rel block.1 anchor →
      C.resolution anchor = memberLocal data star double position)
    {first : Fin degree} (hFirst : (data.vertexPartition wall).Rel block.1 first)
    (second : Fin degree) :
    (pasted C).right.Rel first second ↔
      (memberLocal data star double position).right.Rel first second := by
  show (LocalResolution.pasteRight (data.vertexPartition wall) C.resolution C.contracts).Rel
    first second ↔ _
  unfold LocalResolution.pasteRight
  rw [SheetPartition.paste_rel_iff, resolution_at_repr hLocal hFirst]

theorem pasted_newEdge_rel_iff {double position : Fin 2}
    (hLocal : ∀ anchor, (data.vertexPartition wall).Rel block.1 anchor →
      C.resolution anchor = memberLocal data star double position)
    {first : Fin degree} (hFirst : (data.vertexPartition wall).Rel block.1 first)
    (second : Fin degree) :
    (pasted C).newEdge.Rel first second ↔
      (memberLocal data star double position).newEdge.Rel first second := by
  show (LocalResolution.pasteNewEdge (data.vertexPartition wall) C.resolution C.contracts).Rel
    first second ↔ _
  unfold LocalResolution.pasteNewEdge
  rw [SheetPartition.paste_rel_iff, resolution_at_repr hLocal hFirst]

end Local

/-! ## §2  The two endpoint valencies above a ramification-one block

Figure 37 reads: whichever endpoint carries the block's **doubled** direction
when the block is retained, and the block's **single** direction when the
block is resolved, is trivalent; the other is divalent.  In the labelling of
`memberLocal` those two descriptions collapse into one: *the trivalent
endpoint above the block is the one on side `position`*, and it is `δ⁽ᵠ⁾(Ã)`.
Neither statement below mentions `double` at all. -/

section Cards

variable {block : WallBlock data wall} {C : BalancedGlobal.Candidate target degree data wall}

/-- **Three incidences at the retained endpoint exactly when `δ⁽ᵠ⁾(Ã)` is the
retained one.**  Above a ramification-one block, for every sheet of it. -/
theorem card_incident_old (profile : W2R1SourceProfile.OccurrenceProfile data star block)
    (hRight : ∀ edge, C.right edge = star.right edge) {position : Fin 2}
    (hLocal : ∀ anchor, (data.vertexPartition wall).Rel block.1 anchor →
      C.resolution anchor = memberLocal data star profile.doubleLabel position)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    Fintype.card (IncidentSourceEdge C.datum
        (C.datum.sourceEndpoint (oldVertex target wall) sheet)) =
      if position = 0 then 3 else 2 := by
  rw [card_incident_oldEndpoint (twoStar := star) hRight sheet,
    pasted_newEdge_within_left hLocal hSheet,
    pasted_blockCountWithin_left hLocal _ hSheet]
  by_cases hPosition : position = profile.doubleLabel
  · rw [memberLocal_of_eq data star hPosition]
    simp only [joinedResolutionAt, SheetPartition.blockCountWithin_self]
    by_cases hDouble : profile.doubleLabel = 0
    · rw [if_pos (hPosition.trans hDouble), ← hDouble]
      rw [doublePartition_blockCountWithin profile sheet hSheet]
    · rw [if_neg (fun hZero ↦ hDouble (hPosition.symm.trans hZero)),
        blockCountWithin_eq_one_of_ne_doubleLabel profile (Ne.symm hDouble) sheet hSheet]
  · rw [memberLocal_of_ne data star hPosition, sideFine_newEdge]
    by_cases hDouble : profile.doubleLabel = 0
    · rw [sideFine_left_of_zero data star hDouble,
        if_neg (fun hZero ↦ hPosition (hZero.trans hDouble.symm)), hDouble]
      rw [SheetPartition.blockCountWithin_self]
    · have hZero : position = 0 := by
        have hOne : profile.doubleLabel = 1 := by omega
        rw [hOne] at hPosition
        omega
      rw [sideFine_left_of_ne_zero data star hDouble, if_pos hZero,
        doublePartition_blockCountWithin profile sheet hSheet,
        blockCountWithin_eq_one_of_ne_doubleLabel profile (Ne.symm hDouble) sheet hSheet]

/-- **Three incidences at the fresh endpoint exactly when `δ⁽ᵠ⁾(Ã)` is the
fresh one.** -/
theorem card_incident_fresh (profile : W2R1SourceProfile.OccurrenceProfile data star block)
    (hRight : ∀ edge, C.right edge = star.right edge) {position : Fin 2}
    (hLocal : ∀ anchor, (data.vertexPartition wall).Rel block.1 anchor →
      C.resolution anchor = memberLocal data star profile.doubleLabel position)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    Fintype.card (IncidentSourceEdge C.datum
        (C.datum.sourceEndpoint (freshVertex target) sheet)) =
      if position = 1 then 3 else 2 := by
  rw [card_incident_freshEndpoint (twoStar := star) hRight sheet,
    pasted_newEdge_within_right hLocal hSheet,
    pasted_blockCountWithin_right hLocal _ hSheet]
  by_cases hPosition : position = profile.doubleLabel
  · rw [memberLocal_of_eq data star hPosition]
    simp only [joinedResolutionAt, SheetPartition.blockCountWithin_self]
    by_cases hDouble : profile.doubleLabel = 1
    · rw [if_pos (hPosition.trans hDouble), ← hDouble]
      rw [doublePartition_blockCountWithin profile sheet hSheet]
    · rw [if_neg (fun hOne ↦ hDouble (hPosition.symm.trans hOne)),
        blockCountWithin_eq_one_of_ne_doubleLabel profile (Ne.symm hDouble) sheet hSheet]
  · rw [memberLocal_of_ne data star hPosition, sideFine_newEdge]
    by_cases hDouble : profile.doubleLabel = 0
    · have hOne : position = 1 := by
        rw [hDouble] at hPosition
        omega
      rw [sideFine_right_of_zero data star hDouble, if_pos hOne,
        doublePartition_blockCountWithin profile sheet hSheet]
      have hNe : (1 : Fin 2) ≠ profile.doubleLabel := by rw [hDouble]; decide
      rw [blockCountWithin_eq_one_of_ne_doubleLabel profile hNe sheet hSheet]
    · have hOne : profile.doubleLabel = 1 := by omega
      rw [sideFine_right_of_ne_zero data star hDouble,
        if_neg (fun hEq ↦ hPosition (hEq.trans hOne.symm)), hOne]
      rw [SheetPartition.blockCountWithin_self]

end Cards

/-! ## §3  The two expanded endpoints, named by a wall direction

`TwoStar` sends label `0` to the retained endpoint and label `1` to the fresh
one, so a wall direction names an expanded endpoint.  Since the block's
doubled direction is a per-block datum, every statement below is indexed by
the direction rather than by the side: `side profile.doubleLabel` is the
endpoint Figure 37 draws with `e₁`, `e₂` on it and `side profile.singleLabel`
the one with `e₃`. -/

section Sides

/-- The expanded endpoint carrying the wall direction `label`. -/
def side (label : Fin 2) : Bool := if label = 0 then false else true

@[simp] theorem side_zero : side 0 = false := rfl

@[simp] theorem side_one : side 1 = true := rfl

theorem right_edge (label : Fin 2) : star.right (star.edge label) = side label := by
  by_cases hLabel : label = 0
  · subst hLabel; rw [star.right_edge_zero, side_zero]
  · have hOne : label = 1 := by omega
    subst hOne; rw [star.right_edge_one, side_one]

variable {C : BalancedGlobal.Candidate target degree data wall}

/-- A retained wall occurrence meets the expanded endpoint its direction
names, through its own sheet. -/
theorem old_incident (hRight : ∀ edge, C.right edge = star.right edge)
    (label : Fin 2) (sheet : Fin degree) :
    Incident C.datum (C.oldSourceEdge (data.sourceEdge (star.edge label) sheet))
      (C.datum.sourceEndpoint (LimitChainCore.wallSide target wall (side label)) sheet) := by
  by_cases hLabel : label = 0
  · subst hLabel
    exact oldSourceEdge_incident_old C (star.edge 0) (star.edge_mem_incidentEdges 0)
      ((hRight _).trans star.right_edge_zero) sheet
  · have hOne : label = 1 := by omega
    subst hOne
    exact M11SplitSurvival.oldSourceEdge_incident_fresh C (star.edge 1)
      (star.edge_mem_incidentEdges 1) ((hRight _).trans star.right_edge_one) sheet

/-- The new occurrence through a sheet meets both expanded endpoints above
it. -/
theorem new_incident (label : Fin 2) (sheet : Fin degree) :
    Incident C.datum (C.newSourceEdge sheet)
      (C.datum.sourceEndpoint (LimitChainCore.wallSide target wall (side label)) sheet) := by
  by_cases hLabel : label = 0
  · subst hLabel; exact newSourceEdge_incident_old sheet
  · have hOne : label = 1 := by omega
    subst hOne; exact newSourceEdge_incident_fresh sheet

/-- A wall occurrence's canonical sheet names it back. -/
theorem sourceEdge_first {block : WallBlock data wall}
    (profile : W2R1SourceProfile.OccurrenceProfile data star block) :
    data.sourceEdge (star.edge profile.doubleLabel) (firstSheet profile) = profile.first.1 := by
  rw [← profile.first_target]
  exact GluingDatum.sourceEdge_self data _

theorem sourceEdge_second {block : WallBlock data wall}
    (profile : W2R1SourceProfile.OccurrenceProfile data star block) :
    data.sourceEdge (star.edge profile.doubleLabel) (secondSheet profile) = profile.second.1 := by
  rw [← profile.second_target]
  exact GluingDatum.sourceEdge_self data _

theorem sourceEdge_third {block : WallBlock data wall}
    (profile : W2R1SourceProfile.OccurrenceProfile data star block) :
    data.sourceEdge (star.edge profile.singleLabel) (thirdSheet profile) = profile.third.1 := by
  rw [← profile.third_target]
  exact GluingDatum.sourceEdge_self data _

/-- Every sheet of the block carries `e₃` over the single direction. -/
theorem sourceEdge_single_eq_third {block : WallBlock data wall}
    (profile : W2R1SourceProfile.OccurrenceProfile data star block) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    data.sourceEdge (star.edge profile.singleLabel) sheet = profile.third.1 := by
  refine Eq.trans ?_ (sourceEdge_third profile)
  refine Subtype.ext (Prod.ext rfl ?_)
  have hRel := singlePartition_covers profile sheet hSheet
  rw [SheetPartition.rel_iff, singlePartition_repr_third] at hRel
  show (singlePartition profile).repr sheet =
    (singlePartition profile).repr (thirdSheet profile)
  rw [singlePartition_repr_third]
  exact hRel.symm

/-- The three occurrences are pairwise distinct as source occurrences. -/
theorem first_ne_second_val {block : WallBlock data wall}
    (profile : W2R1SourceProfile.OccurrenceProfile data star block) :
    profile.first.1 ≠ profile.second.1 :=
  fun hEq ↦ profile.first_ne_second (Subtype.ext hEq)

theorem first_ne_third_val {block : WallBlock data wall}
    (profile : W2R1SourceProfile.OccurrenceProfile data star block) :
    profile.first.1 ≠ profile.third.1 :=
  fun hEq ↦ profile.first_ne_third (Subtype.ext hEq)

theorem second_ne_third_val {block : WallBlock data wall}
    (profile : W2R1SourceProfile.OccurrenceProfile data star block) :
    profile.second.1 ≠ profile.third.1 :=
  fun hEq ↦ profile.second_ne_third (Subtype.ext hEq)

end Sides

/-! ## §4  `δ⁽ᵠ⁾(Ã)`, the endpoint identifications and the new occurrences

The one-line form of Figure 37: **the trivalent expanded endpoint above a
ramification-one block is the one named by `position`**, whichever direction
the block happens to be doubled over.  That endpoint is `Ã`, and the source's
`δ⁽ᵠ⁾(Ã)` is exactly the side `position` names. -/

section Endpoints

variable {block : WallBlock data wall} {C : BalancedGlobal.Candidate target degree data wall}

/-- **`δ⁽ᵠ⁾(Ã)` is the endpoint on side `position`.**  Above a
ramification-one block the endpoint named by a wall direction `label` carries
three incidences exactly when `label = position`, and two otherwise --
uniformly in the block's own doubled direction. -/
theorem card_incident_side (profile : W2R1SourceProfile.OccurrenceProfile data star block)
    (hRight : ∀ edge, C.right edge = star.right edge) {position : Fin 2}
    (hLocal : ∀ anchor, (data.vertexPartition wall).Rel block.1 anchor →
      C.resolution anchor = memberLocal data star profile.doubleLabel position)
    (label : Fin 2) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    Fintype.card (IncidentSourceEdge C.datum
        (C.datum.sourceEndpoint (LimitChainCore.wallSide target wall (side label)) sheet)) =
      if position = label then 3 else 2 := by
  by_cases hLabel : label = 0
  · subst hLabel
    exact card_incident_old profile hRight hLocal hSheet
  · have hOne : label = 1 := by omega
    subst hOne
    exact card_incident_fresh profile hRight hLocal hSheet

/-! ### The retained member: one endpoint on each side, one new occurrence -/

/-- With `δ⁽ᵠ⁾(Ã)` at the doubled direction the whole block stays whole: every
sheet of it names the same endpoint on each side. -/
theorem retained_vertex_eq {double position : Fin 2}
    (hLocal : ∀ anchor, (data.vertexPartition wall).Rel block.1 anchor →
      C.resolution anchor = memberLocal data star double position)
    (hPosition : position = double) (label : Fin 2) {first second : Fin degree}
    (hFirst : (data.vertexPartition wall).Rel block.1 first)
    (hSecond : (data.vertexPartition wall).Rel block.1 second) :
    C.datum.sourceEndpoint (LimitChainCore.wallSide target wall (side label)) first =
      C.datum.sourceEndpoint (LimitChainCore.wallSide target wall (side label)) second := by
  have hWall : (data.vertexPartition wall).Rel first second := hFirst.symm.trans hSecond
  by_cases hLabel : label = 0
  · subst hLabel
    refine sourceEndpoint_old_eq_of_rel first second ?_
    rw [pasted_left_rel_iff hLocal hFirst, memberLocal_of_eq data star hPosition]
    exact hWall
  · have hOne : label = 1 := by omega
    subst hOne
    refine sourceEndpoint_fresh_eq_of_rel first second ?_
    rw [pasted_right_rel_iff hLocal hFirst, memberLocal_of_eq data star hPosition]
    exact hWall

/-- and one new occurrence, of index `k₃ = |A₀|`. -/
theorem retained_newSourceEdge_eq {double position : Fin 2}
    (hLocal : ∀ anchor, (data.vertexPartition wall).Rel block.1 anchor →
      C.resolution anchor = memberLocal data star double position)
    (hPosition : position = double) {first second : Fin degree}
    (hFirst : (data.vertexPartition wall).Rel block.1 first)
    (hSecond : (data.vertexPartition wall).Rel block.1 second) :
    C.newSourceEdge first = C.newSourceEdge second := by
  refine (newSourceEdge_eq_iff_rel first second).mpr ?_
  rw [pasted_newEdge_rel_iff hLocal hFirst, memberLocal_of_eq data star hPosition]
  exact hFirst.symm.trans hSecond

/-! ### The resolved member: the doubled side splits, the single side does not -/

/-- With `δ⁽ᵠ⁾(Ã)` at the single direction the endpoint on any **other**
direction's side is still one vertex above the block. -/
theorem resolved_vertex_eq {double position : Fin 2}
    (hLocal : ∀ anchor, (data.vertexPartition wall).Rel block.1 anchor →
      C.resolution anchor = memberLocal data star double position)
    (hPosition : position ≠ double) {label : Fin 2} (hLabel : label ≠ double)
    {first second : Fin degree}
    (hFirst : (data.vertexPartition wall).Rel block.1 first)
    (hSecond : (data.vertexPartition wall).Rel block.1 second) :
    C.datum.sourceEndpoint (LimitChainCore.wallSide target wall (side label)) first =
      C.datum.sourceEndpoint (LimitChainCore.wallSide target wall (side label)) second := by
  have hWall : (data.vertexPartition wall).Rel first second := hFirst.symm.trans hSecond
  by_cases hDouble : double = 0
  · have hOne : label = 1 := by rw [hDouble] at hLabel; omega
    subst hOne
    refine sourceEndpoint_fresh_eq_of_rel first second ?_
    rw [pasted_right_rel_iff hLocal hFirst, memberLocal_of_ne data star hPosition,
      sideFine_right_of_zero data star hDouble]
    exact hWall
  · have hZero : label = 0 := by
      have : double = 1 := by omega
      rw [this] at hLabel; omega
    subst hZero
    refine sourceEndpoint_old_eq_of_rel first second ?_
    rw [pasted_left_rel_iff hLocal hFirst, memberLocal_of_ne data star hPosition,
      sideFine_left_of_ne_zero data star hDouble]
    exact hWall

/-- On the doubled direction's own side the endpoint splits exactly along that
direction's classes. -/
theorem resolved_double_vertex_eq {double position : Fin 2}
    (hLocal : ∀ anchor, (data.vertexPartition wall).Rel block.1 anchor →
      C.resolution anchor = memberLocal data star double position)
    (hPosition : position ≠ double) {first second : Fin degree}
    (hFirst : (data.vertexPartition wall).Rel block.1 first)
    (hRel : (data.edgePartition (star.edge double)).Rel first second) :
    C.datum.sourceEndpoint (LimitChainCore.wallSide target wall (side double)) first =
      C.datum.sourceEndpoint (LimitChainCore.wallSide target wall (side double)) second := by
  by_cases hDouble : double = 0
  · rw [show side double = false by rw [hDouble]; rfl]
    refine sourceEndpoint_old_eq_of_rel first second ?_
    rw [pasted_left_rel_iff hLocal hFirst, memberLocal_of_ne data star hPosition,
      sideFine_left_of_zero data star hDouble]
    exact hRel
  · rw [show side double = true by
      have hOne : double = 1 := by omega
      rw [hOne]; rfl]
    refine sourceEndpoint_fresh_eq_of_rel first second ?_
    rw [pasted_right_rel_iff hLocal hFirst, memberLocal_of_ne data star hPosition,
      sideFine_right_of_ne_zero data star hDouble]
    exact hRel

/-- **The resolved member's two new occurrences are the doubled direction's own
two classes**: `|e'| = k₁` and `|e''| = k₂`. -/
theorem resolved_newSourceEdge_eq_iff {double position : Fin 2}
    (hLocal : ∀ anchor, (data.vertexPartition wall).Rel block.1 anchor →
      C.resolution anchor = memberLocal data star double position)
    (hPosition : position ≠ double) {first : Fin degree}
    (hFirst : (data.vertexPartition wall).Rel block.1 first) (second : Fin degree) :
    C.newSourceEdge first = C.newSourceEdge second ↔
      (data.edgePartition (star.edge double)).Rel first second := by
  rw [newSourceEdge_eq_iff_rel, pasted_newEdge_rel_iff hLocal hFirst,
    memberLocal_of_ne data star hPosition, sideFine_newEdge]

end Endpoints

/-! ## §5  A member read at one ramification-one block

`BlockMember` bundles the hypotheses of §1--§4.  It is the two-block case's
analogue of `LimitChainCore.SelectedData`, and it is deliberately *per block*:
a `{w2-r1}` member is two of these over one candidate, at `A₀` with `position`
and at `B₀` with `other position`.  See §8 for why the core's single
`selected` anchor cannot hold both. -/

/-- A candidate read at one ramification-one wall block: the block's literal
occurrence profile, the member's position there, and the two receipts every
survival argument needs. -/
structure BlockMember (data : GluingDatum target degree) (star : TwoStar target wall)
    (block : WallBlock data wall) where
  /-- The member. -/
  candidate : BalancedGlobal.Candidate target degree data wall
  /-- The block's own `e₁, e₂, e₃`. -/
  profile : W2R1SourceProfile.SourceProfile data star block
  /-- `δ⁽ᵠ⁾(Ã)`, as a wall direction. -/
  position : Fin 2
  /-- The member keeps the two-star's own side assignment. -/
  right_eq : ∀ edge, candidate.right edge = star.right edge
  /-- and on this block it is Figure 37's member. -/
  local_eq : ∀ anchor, (data.vertexPartition wall).Rel block.1 anchor →
    candidate.resolution anchor = memberLocal data star profile.doubleLabel position
  valid : data.Valid
  genus_eq : genus candidate.datum.sourceGraph = genus data.sourceGraph

namespace BlockMember

variable {block : WallBlock data wall} (member : BlockMember data star block)

/-- The direction carrying `e₁` and `e₂`. -/
abbrev double : Fin 2 := member.profile.doubleLabel

/-- The direction carrying `e₃`. -/
abbrev single : Fin 2 := member.profile.singleLabel

/-- The member's expanded endpoint on the side named by a wall direction. -/
noncomputable def vertex (label : Fin 2) (sheet : Fin degree) :
    member.candidate.datum.SourceVertex :=
  member.candidate.datum.sourceEndpoint
    (LimitChainCore.wallSide target wall (side label)) sheet

theorem double_ne_single : member.double ≠ member.single := member.profile.labels_ne

theorem connected : member.candidate.datum.Connected :=
  (member.candidate.datum_valid member.valid).1

/-- **`δ⁽ᵠ⁾(Ã)` is the side `position` names.**  Three incidences there and two
on the other side, whichever direction the block is doubled over. -/
theorem card_vertex (label : Fin 2) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    Fintype.card (IncidentSourceEdge member.candidate.datum (member.vertex label sheet)) =
      if member.position = label then 3 else 2 :=
  card_incident_side member.profile.toOccurrenceProfile member.right_eq member.local_eq
    label hSheet

/-! ### The incidences, before pruning -/

theorem new_incident_vertex (label : Fin 2) (sheet : Fin degree) :
    Incident member.candidate.datum (member.candidate.newSourceEdge sheet)
      (member.vertex label sheet) :=
  new_incident label sheet

/-- `e₃` meets the single direction's endpoint above every sheet of the
block. -/
theorem third_incident_vertex {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    Incident member.candidate.datum
      (member.candidate.oldSourceEdge member.profile.third.1)
      (member.vertex member.single sheet) := by
  rw [← sourceEdge_single_eq_third member.profile.toOccurrenceProfile hSheet]
  exact old_incident member.right_eq _ sheet

/-- `e₁` meets the doubled direction's endpoint above its own sheet. -/
theorem first_incident_vertex :
    Incident member.candidate.datum
      (member.candidate.oldSourceEdge member.profile.first.1)
      (member.vertex member.double (firstSheet member.profile.toOccurrenceProfile)) := by
  rw [← sourceEdge_first member.profile.toOccurrenceProfile]
  exact old_incident member.right_eq _ _

/-- and `e₂` above its own. -/
theorem second_incident_vertex :
    Incident member.candidate.datum
      (member.candidate.oldSourceEdge member.profile.second.1)
      (member.vertex member.double (secondSheet member.profile.toOccurrenceProfile)) := by
  rw [← sourceEdge_second member.profile.toOccurrenceProfile]
  exact old_incident member.right_eq _ _

/-! ### Retained and dangling occurrences of the member -/

theorem old_survives {edge : data.SourceEdge} (hSurvives : ¬ IsDangling data edge) :
    ¬ IsDangling member.candidate.datum (member.candidate.oldSourceEdge edge) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge member.candidate member.valid.1 edge hSurvives

theorem old_isDangling_iff (edge : data.SourceEdge) :
    IsDangling member.candidate.datum (member.candidate.oldSourceEdge edge) ↔
      IsDangling data edge :=
  ResolutionPruning.isDangling_oldSourceEdge_iff member.candidate member.valid
    member.genus_eq edge

theorem second_survives :
    ¬ IsDangling member.candidate.datum
      (member.candidate.oldSourceEdge member.profile.second.1) :=
  member.old_survives member.profile.second_survives

theorem third_survives :
    ¬ IsDangling member.candidate.datum
      (member.candidate.oldSourceEdge member.profile.third.1) :=
  member.old_survives member.profile.third_survives

theorem old_ne_new (edge : data.SourceEdge) (sheet : Fin degree) :
    member.candidate.oldSourceEdge edge ≠ member.candidate.newSourceEdge sheet :=
  oldSourceEdge_ne_newSourceEdge edge sheet

theorem old_first_ne_second :
    member.candidate.oldSourceEdge member.profile.first.1 ≠
      member.candidate.oldSourceEdge member.profile.second.1 :=
  fun hEq ↦ first_ne_second_val member.profile.toOccurrenceProfile
    (ResolutionCut.oldSourceEdge_injective member.candidate hEq)

theorem old_first_ne_third :
    member.candidate.oldSourceEdge member.profile.first.1 ≠
      member.candidate.oldSourceEdge member.profile.third.1 :=
  fun hEq ↦ first_ne_third_val member.profile.toOccurrenceProfile
    (ResolutionCut.oldSourceEdge_injective member.candidate hEq)

theorem old_second_ne_third :
    member.candidate.oldSourceEdge member.profile.second.1 ≠
      member.candidate.oldSourceEdge member.profile.third.1 :=
  fun hEq ↦ second_ne_third_val member.profile.toOccurrenceProfile
    (ResolutionCut.oldSourceEdge_injective member.candidate hEq)

end BlockMember

/-! ## §6  The census of the retained member at the block (Figure 37, gluing I)

`δ⁽ᵠ⁾(Ã)` at the doubled direction: the block stays whole, so each side
carries one endpoint above it and there is one new occurrence `e'` of index
`k₃ = |A₀|`.

| endpoint | incidences | nd3 surviving | nd2 surviving |
|---|---|---|---|
| side `t₂` (`= δ⁽ᵠ⁾(Ã)`) | old `e₁`, old `e₂`, new `e'` | 3 (**branch**) | 2 (`e₁` dies) |
| side `t₃` | old `e₃`, new `e'` | 2 | 2 |
-/

section Retained

variable {block : WallBlock data wall} (member : BlockMember data star block)

namespace BlockMember

/-- With the block retained, all of its sheets name one endpoint on each
side. -/
theorem retained_vertex_eq' (hPosition : member.position = member.double)
    (label : Fin 2) {first second : Fin degree}
    (hFirst : (data.vertexPartition wall).Rel block.1 first)
    (hSecond : (data.vertexPartition wall).Rel block.1 second) :
    member.vertex label first = member.vertex label second :=
  retained_vertex_eq member.local_eq hPosition label hFirst hSecond

/-- `|e'| = k₃`: one new occurrence above the whole block. -/
theorem retained_new_eq (hPosition : member.position = member.double)
    {first second : Fin degree}
    (hFirst : (data.vertexPartition wall).Rel block.1 first)
    (hSecond : (data.vertexPartition wall).Rel block.1 second) :
    member.candidate.newSourceEdge first = member.candidate.newSourceEdge second :=
  retained_newSourceEdge_eq member.local_eq hPosition hFirst hSecond

theorem retained_card_single (hPosition : member.position = member.double)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    Fintype.card (IncidentSourceEdge member.candidate.datum
      (member.vertex member.single sheet)) = 2 := by
  rw [member.card_vertex member.single hSheet,
    if_neg (by rw [hPosition]; exact member.double_ne_single)]

theorem retained_card_double (hPosition : member.position = member.double)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    Fintype.card (IncidentSourceEdge member.candidate.datum
      (member.vertex member.double sheet)) = 3 := by
  rw [member.card_vertex member.double hSheet, if_pos hPosition]

/-- **The retained member's new occurrence survives**, always: it is paired
with `e₃` at a divalent endpoint and `e₃` never dangles. -/
theorem retained_new_survives (hPosition : member.position = member.double)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    ¬ IsDangling member.candidate.datum (member.candidate.newSourceEdge sheet) :=
  (survives_iff_of_card_two member.candidate.datum member.connected _
    (member.candidate.oldSourceEdge member.profile.third.1)
    (member.candidate.newSourceEdge sheet)
    (member.third_incident_vertex hSheet)
    (member.new_incident_vertex member.single sheet)
    (member.retained_card_single hPosition hSheet)).mp member.third_survives

/-- **The complete surviving star at the single direction's endpoint**: `e₃`
and `e'`, in both sub-cases. -/
theorem retained_nonDanglingIncident_single (hPosition : member.position = member.double)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    nonDanglingIncident member.candidate.datum (member.vertex member.single sheet) =
      {member.candidate.newSourceEdge sheet,
        member.candidate.oldSourceEdge member.profile.third.1} :=
  nonDanglingIncident_pair_of_card_two member.candidate.datum
    (member.new_incident_vertex member.single sheet)
    (member.third_incident_vertex hSheet)
    (Ne.symm (member.old_ne_new _ _))
    (member.retained_new_survives hPosition hSheet) member.third_survives
    (member.retained_card_single hPosition hSheet)

theorem retained_nonDanglingValency_single (hPosition : member.position = member.double)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    nonDanglingValency member.candidate.datum (member.vertex member.single sheet) = 2 :=
  nonDanglingValency_eq_two_of_card_two_of_survives member.candidate.datum
    member.connected _ (member.candidate.newSourceEdge sheet)
    (member.new_incident_vertex member.single sheet)
    (member.retained_new_survives hPosition hSheet)
    (member.retained_card_single hPosition hSheet)

/-- **`e'` joins `e₃`'s stable row.** -/
theorem retained_new_stablePath_eq (hPosition : member.position = member.double)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    NonDanglingEdge.stablePath (⟨member.candidate.newSourceEdge sheet,
        member.retained_new_survives hPosition hSheet⟩ :
      NonDanglingEdge member.candidate.datum) =
      NonDanglingEdge.stablePath (⟨member.candidate.oldSourceEdge member.profile.third.1,
        member.third_survives⟩ : NonDanglingEdge member.candidate.datum) := by
  refine stablePath_eq_of_consecutive ⟨?_, member.vertex member.single sheet,
    member.new_incident_vertex member.single sheet, member.third_incident_vertex hSheet,
    member.retained_nonDanglingValency_single hPosition hSheet⟩
  intro hEqual
  exact member.old_ne_new member.profile.third.1 sheet
    (congrArg (fun edge : NonDanglingEdge member.candidate.datum ↦ edge.1) hEqual).symm

/-- The `e₁` incidence, transported to an arbitrary sheet of the block. -/
theorem retained_first_incident (hPosition : member.position = member.double)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    Incident member.candidate.datum
      (member.candidate.oldSourceEdge member.profile.first.1)
      (member.vertex member.double sheet) := by
  rw [← member.retained_vertex_eq' hPosition member.double
    (firstSheet_rel member.profile.toOccurrenceProfile) hSheet]
  exact member.first_incident_vertex

theorem retained_second_incident (hPosition : member.position = member.double)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    Incident member.candidate.datum
      (member.candidate.oldSourceEdge member.profile.second.1)
      (member.vertex member.double sheet) := by
  rw [← member.retained_vertex_eq' hPosition member.double
    (secondSheet_rel member.profile.toOccurrenceProfile) hSheet]
  exact member.second_incident_vertex

/-- **nd3: the doubled direction's endpoint is a branch vertex** with the
complete surviving star `e₁`, `e₂`, `e'`. -/
theorem retained_nonDanglingIncident_double_nd3 (hPosition : member.position = member.double)
    (hNd3 : ¬ IsDangling data member.profile.first.1)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    nonDanglingIncident member.candidate.datum (member.vertex member.double sheet) =
      {member.candidate.oldSourceEdge member.profile.first.1,
        member.candidate.oldSourceEdge member.profile.second.1,
        member.candidate.newSourceEdge sheet} :=
  nonDanglingIncident_triple_of_card_three member.candidate.datum
    (member.retained_first_incident hPosition hSheet)
    (member.retained_second_incident hPosition hSheet)
    (member.new_incident_vertex member.double sheet)
    member.old_first_ne_second (member.old_ne_new _ _) (member.old_ne_new _ _)
    (member.old_survives hNd3) member.second_survives
    (member.retained_new_survives hPosition hSheet)
    (member.retained_card_double hPosition hSheet)

theorem retained_nonDanglingValency_double_nd3 (hPosition : member.position = member.double)
    (hNd3 : ¬ IsDangling data member.profile.first.1)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    nonDanglingValency member.candidate.datum (member.vertex member.double sheet) = 3 := by
  rw [← card_nonDanglingIncident,
    member.retained_nonDanglingIncident_double_nd3 hPosition hNd3 hSheet,
    Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (hEq | hEq)
      · exact member.old_first_ne_second hEq
      · exact member.old_ne_new _ _ hEq),
    Finset.card_pair (member.old_ne_new _ _)]

/-- **nd2: `e₁` dies and the doubled direction's endpoint is only divalent.**
So in Figure 38's retained member the block contributes no branch vertex. -/
theorem retained_nonDanglingIncident_double_nd2 (hPosition : member.position = member.double)
    (hNd2 : IsDangling data member.profile.first.1)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    nonDanglingIncident member.candidate.datum (member.vertex member.double sheet) =
      {member.candidate.oldSourceEdge member.profile.second.1,
        member.candidate.newSourceEdge sheet} :=
  nonDanglingIncident_pair_of_card_three member.candidate.datum
    (member.retained_second_incident hPosition hSheet)
    (member.new_incident_vertex member.double sheet)
    (member.retained_first_incident hPosition hSheet)
    (member.old_ne_new _ _) (Ne.symm member.old_first_ne_second)
    (Ne.symm (member.old_ne_new _ _))
    member.second_survives (member.retained_new_survives hPosition hSheet)
    ((member.old_isDangling_iff _).mpr hNd2)
    (member.retained_card_double hPosition hSheet)

theorem retained_nonDanglingValency_double_nd2 (hPosition : member.position = member.double)
    (hNd2 : IsDangling data member.profile.first.1)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    nonDanglingValency member.candidate.datum (member.vertex member.double sheet) = 2 := by
  rw [← card_nonDanglingIncident,
    member.retained_nonDanglingIncident_double_nd2 hPosition hNd2 hSheet,
    Finset.card_pair (member.old_ne_new _ _)]

end BlockMember

end Retained

/-! ## §7  The census of the resolved member at the block (Figure 37, gluing II)

`δ⁽ᵠ⁾(Ã)` at the single direction: the doubled direction's side splits into
the `e₁` class and the `e₂` class, and there are two new occurrences,
`|e'| = k₁` and `|e''| = k₂`.

| endpoint | incidences | nd3 surviving | nd2 surviving |
|---|---|---|---|
| side `t₂` over `e₁` | old `e₁`, new `e'` | 2 | 0 (**both die**) |
| side `t₂` over `e₂` | old `e₂`, new `e''` | 2 | 2 |
| side `t₃` (`= δ⁽ᵠ⁾(Ã)`) | old `e₃`, new `e'`, new `e''` | 3 (**branch**) | 2 (`e'` dies) |

Figure 38's `|e'| = k₂` is the third row's surviving new occurrence: with
`k₁ = 1` the `e₁` class is a single sheet and its whole endpoint is pruned
away, which is why the figure draws only one new occurrence there. -/

section Resolved

variable {block : WallBlock data wall} (member : BlockMember data star block)

namespace BlockMember

/-- With the block resolved, `δ⁽ᵠ⁾(Ã)` is the single direction's endpoint. -/
theorem position_eq_single (hPosition : member.position ≠ member.double) :
    member.position = member.single :=
  eq_singleLabel_of_ne_doubleLabel member.profile.toOccurrenceProfile hPosition

/-- The single direction's endpoint is still one vertex above the block. -/
theorem resolved_vertex_eq' (hPosition : member.position ≠ member.double)
    {first second : Fin degree}
    (hFirst : (data.vertexPartition wall).Rel block.1 first)
    (hSecond : (data.vertexPartition wall).Rel block.1 second) :
    member.vertex member.single first = member.vertex member.single second :=
  resolved_vertex_eq member.local_eq hPosition (Ne.symm member.double_ne_single) hFirst hSecond

/-- The doubled direction's endpoint splits exactly into the `e₁` and `e₂`
classes. -/
theorem resolved_double_vertex_eq' (hPosition : member.position ≠ member.double)
    {first second : Fin degree}
    (hFirst : (data.vertexPartition wall).Rel block.1 first)
    (hRel : (doublePartition member.profile.toOccurrenceProfile).Rel first second) :
    member.vertex member.double first = member.vertex member.double second :=
  resolved_double_vertex_eq member.local_eq hPosition hFirst hRel

/-- **`|e'| = k₁`, `|e''| = k₂`**: the two new occurrences are the doubled
direction's own two classes. -/
theorem resolved_new_eq_iff (hPosition : member.position ≠ member.double)
    {first : Fin degree} (hFirst : (data.vertexPartition wall).Rel block.1 first)
    (second : Fin degree) :
    member.candidate.newSourceEdge first = member.candidate.newSourceEdge second ↔
      (doublePartition member.profile.toOccurrenceProfile).Rel first second :=
  resolved_newSourceEdge_eq_iff member.local_eq hPosition hFirst second

theorem resolved_new_first_ne_second (hPosition : member.position ≠ member.double) :
    member.candidate.newSourceEdge (firstSheet member.profile.toOccurrenceProfile) ≠
      member.candidate.newSourceEdge (secondSheet member.profile.toOccurrenceProfile) := by
  intro hEqual
  exact doublePartition_separate member.profile.toOccurrenceProfile
    ((member.resolved_new_eq_iff hPosition
      (firstSheet_rel member.profile.toOccurrenceProfile) _).mp hEqual)

theorem resolved_card_double (hPosition : member.position ≠ member.double)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    Fintype.card (IncidentSourceEdge member.candidate.datum
      (member.vertex member.double sheet)) = 2 := by
  rw [member.card_vertex member.double hSheet, if_neg hPosition]

theorem resolved_card_single (hPosition : member.position ≠ member.double)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    Fintype.card (IncidentSourceEdge member.candidate.datum
      (member.vertex member.single sheet)) = 3 := by
  rw [member.card_vertex member.single hSheet,
    if_pos (member.position_eq_single hPosition)]

/-! ### The two divalent endpoints over the doubled direction -/

/-- **The `e₂` endpoint's star**: `e₂` and `e''`, in both sub-cases. -/
theorem resolved_new_second_survives (hPosition : member.position ≠ member.double) :
    ¬ IsDangling member.candidate.datum
      (member.candidate.newSourceEdge (secondSheet member.profile.toOccurrenceProfile)) :=
  (survives_iff_of_card_two member.candidate.datum member.connected _
    (member.candidate.oldSourceEdge member.profile.second.1)
    (member.candidate.newSourceEdge (secondSheet member.profile.toOccurrenceProfile))
    member.second_incident_vertex
    (member.new_incident_vertex member.double
      (secondSheet member.profile.toOccurrenceProfile))
    (member.resolved_card_double hPosition
      (secondSheet_rel member.profile.toOccurrenceProfile))).mp member.second_survives

theorem resolved_nonDanglingIncident_second (hPosition : member.position ≠ member.double) :
    nonDanglingIncident member.candidate.datum
        (member.vertex member.double (secondSheet member.profile.toOccurrenceProfile)) =
      {member.candidate.newSourceEdge (secondSheet member.profile.toOccurrenceProfile),
        member.candidate.oldSourceEdge member.profile.second.1} :=
  nonDanglingIncident_pair_of_card_two member.candidate.datum
    (member.new_incident_vertex member.double
      (secondSheet member.profile.toOccurrenceProfile))
    member.second_incident_vertex (Ne.symm (member.old_ne_new _ _))
    (member.resolved_new_second_survives hPosition) member.second_survives
    (member.resolved_card_double hPosition
      (secondSheet_rel member.profile.toOccurrenceProfile))

theorem resolved_nonDanglingValency_second (hPosition : member.position ≠ member.double) :
    nonDanglingValency member.candidate.datum
      (member.vertex member.double (secondSheet member.profile.toOccurrenceProfile)) = 2 :=
  nonDanglingValency_eq_two_of_card_two_of_survives member.candidate.datum member.connected _
    (member.candidate.newSourceEdge (secondSheet member.profile.toOccurrenceProfile))
    (member.new_incident_vertex member.double
      (secondSheet member.profile.toOccurrenceProfile))
    (member.resolved_new_second_survives hPosition)
    (member.resolved_card_double hPosition
      (secondSheet_rel member.profile.toOccurrenceProfile))

/-- **`e''` joins `e₂`'s stable row.** -/
theorem resolved_new_second_stablePath_eq (hPosition : member.position ≠ member.double) :
    NonDanglingEdge.stablePath
        (⟨member.candidate.newSourceEdge (secondSheet member.profile.toOccurrenceProfile),
          member.resolved_new_second_survives hPosition⟩ :
          NonDanglingEdge member.candidate.datum) =
      NonDanglingEdge.stablePath (⟨member.candidate.oldSourceEdge member.profile.second.1,
        member.second_survives⟩ : NonDanglingEdge member.candidate.datum) := by
  refine stablePath_eq_of_consecutive ⟨?_,
    member.vertex member.double (secondSheet member.profile.toOccurrenceProfile),
    member.new_incident_vertex member.double
      (secondSheet member.profile.toOccurrenceProfile),
    member.second_incident_vertex, member.resolved_nonDanglingValency_second hPosition⟩
  intro hEqual
  exact member.old_ne_new member.profile.second.1 _
    (congrArg (fun edge : NonDanglingEdge member.candidate.datum ↦ edge.1) hEqual).symm

/-- **The `e₁` endpoint is a both-or-neither pair**: `e'` survives exactly
when `e₁` does. -/
theorem resolved_new_first_survives_iff (hPosition : member.position ≠ member.double) :
    (¬ IsDangling member.candidate.datum
        (member.candidate.newSourceEdge (firstSheet member.profile.toOccurrenceProfile))) ↔
      ¬ IsDangling data member.profile.first.1 :=
  ((survives_iff_of_card_two member.candidate.datum member.connected _
    (member.candidate.oldSourceEdge member.profile.first.1)
    (member.candidate.newSourceEdge (firstSheet member.profile.toOccurrenceProfile))
    member.first_incident_vertex
    (member.new_incident_vertex member.double
      (firstSheet member.profile.toOccurrenceProfile))
    (member.resolved_card_double hPosition
      (firstSheet_rel member.profile.toOccurrenceProfile))).symm).trans
    (not_congr (member.old_isDangling_iff _))

/-- nd3: the `e₁` endpoint keeps both. -/
theorem resolved_nonDanglingIncident_first_nd3 (hPosition : member.position ≠ member.double)
    (hNd3 : ¬ IsDangling data member.profile.first.1) :
    nonDanglingIncident member.candidate.datum
        (member.vertex member.double (firstSheet member.profile.toOccurrenceProfile)) =
      {member.candidate.newSourceEdge (firstSheet member.profile.toOccurrenceProfile),
        member.candidate.oldSourceEdge member.profile.first.1} :=
  nonDanglingIncident_pair_of_card_two member.candidate.datum
    (member.new_incident_vertex member.double
      (firstSheet member.profile.toOccurrenceProfile))
    member.first_incident_vertex (Ne.symm (member.old_ne_new _ _))
    ((member.resolved_new_first_survives_iff hPosition).mpr hNd3)
    (member.old_survives hNd3)
    (member.resolved_card_double hPosition
      (firstSheet_rel member.profile.toOccurrenceProfile))

/-- **nd2: the whole `e₁` endpoint is pruned away.**  Both its occurrences
dangle, so Figure 38's resolved member has *no* vertex there -- which is why
the figure draws a single new occurrence of index `k₂`. -/
theorem resolved_nonDanglingIncident_first_nd2 (hPosition : member.position ≠ member.double)
    (hNd2 : IsDangling data member.profile.first.1) :
    nonDanglingIncident member.candidate.datum
      (member.vertex member.double (firstSheet member.profile.toOccurrenceProfile)) = ∅ :=
  nonDanglingIncident_empty_of_card_two member.candidate.datum
    (member.new_incident_vertex member.double
      (firstSheet member.profile.toOccurrenceProfile))
    member.first_incident_vertex (member.old_ne_new _ _).symm
    (by
      by_contra hSurvives
      exact ((member.resolved_new_first_survives_iff hPosition).mp hSurvives) hNd2)
    ((member.old_isDangling_iff _).mpr hNd2)
    (member.resolved_card_double hPosition
      (firstSheet_rel member.profile.toOccurrenceProfile))

/-- nd3: `e'` joins `e₁`'s stable row. -/
theorem resolved_new_first_stablePath_eq (hPosition : member.position ≠ member.double)
    (hNd3 : ¬ IsDangling data member.profile.first.1) :
    NonDanglingEdge.stablePath
        (⟨member.candidate.newSourceEdge (firstSheet member.profile.toOccurrenceProfile),
          (member.resolved_new_first_survives_iff hPosition).mpr hNd3⟩ :
          NonDanglingEdge member.candidate.datum) =
      NonDanglingEdge.stablePath (⟨member.candidate.oldSourceEdge member.profile.first.1,
        member.old_survives hNd3⟩ : NonDanglingEdge member.candidate.datum) := by
  refine stablePath_eq_of_consecutive ⟨?_,
    member.vertex member.double (firstSheet member.profile.toOccurrenceProfile),
    member.new_incident_vertex member.double
      (firstSheet member.profile.toOccurrenceProfile),
    member.first_incident_vertex, ?_⟩
  · intro hEqual
    exact member.old_ne_new member.profile.first.1 _
      (congrArg (fun edge : NonDanglingEdge member.candidate.datum ↦ edge.1) hEqual).symm
  · exact nonDanglingValency_eq_two_of_card_two_of_survives member.candidate.datum
      member.connected _ (member.candidate.oldSourceEdge member.profile.first.1)
      member.first_incident_vertex (member.old_survives hNd3)
      (member.resolved_card_double hPosition
        (firstSheet_rel member.profile.toOccurrenceProfile))

end BlockMember

end Resolved

/-! ### The trivalent endpoint over the single direction -/

section ResolvedSingle

variable {block : WallBlock data wall} (member : BlockMember data star block)

namespace BlockMember

theorem resolved_new_first_incident_single (hPosition : member.position ≠ member.double)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    Incident member.candidate.datum
      (member.candidate.newSourceEdge (firstSheet member.profile.toOccurrenceProfile))
      (member.vertex member.single sheet) := by
  rw [← member.resolved_vertex_eq' hPosition
    (firstSheet_rel member.profile.toOccurrenceProfile) hSheet]
  exact member.new_incident_vertex member.single _

theorem resolved_new_second_incident_single (hPosition : member.position ≠ member.double)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    Incident member.candidate.datum
      (member.candidate.newSourceEdge (secondSheet member.profile.toOccurrenceProfile))
      (member.vertex member.single sheet) := by
  rw [← member.resolved_vertex_eq' hPosition
    (secondSheet_rel member.profile.toOccurrenceProfile) hSheet]
  exact member.new_incident_vertex member.single _

/-- **nd3: the single direction's endpoint is the member's branch vertex above
the block**, with the complete surviving star `e₃`, `e'`, `e''`. -/
theorem resolved_nonDanglingIncident_single_nd3 (hPosition : member.position ≠ member.double)
    (hNd3 : ¬ IsDangling data member.profile.first.1)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    nonDanglingIncident member.candidate.datum (member.vertex member.single sheet) =
      {member.candidate.oldSourceEdge member.profile.third.1,
        member.candidate.newSourceEdge (firstSheet member.profile.toOccurrenceProfile),
        member.candidate.newSourceEdge (secondSheet member.profile.toOccurrenceProfile)} :=
  nonDanglingIncident_triple_of_card_three member.candidate.datum
    (member.third_incident_vertex hSheet)
    (member.resolved_new_first_incident_single hPosition hSheet)
    (member.resolved_new_second_incident_single hPosition hSheet)
    (member.old_ne_new _ _) (member.old_ne_new _ _)
    (member.resolved_new_first_ne_second hPosition)
    member.third_survives
    ((member.resolved_new_first_survives_iff hPosition).mpr hNd3)
    (member.resolved_new_second_survives hPosition)
    (member.resolved_card_single hPosition hSheet)

theorem resolved_nonDanglingValency_single_nd3 (hPosition : member.position ≠ member.double)
    (hNd3 : ¬ IsDangling data member.profile.first.1)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    nonDanglingValency member.candidate.datum (member.vertex member.single sheet) = 3 := by
  rw [← card_nonDanglingIncident,
    member.resolved_nonDanglingIncident_single_nd3 hPosition hNd3 hSheet,
    Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (hEq | hEq)
      · exact member.old_ne_new _ _ hEq
      · exact member.old_ne_new _ _ hEq),
    Finset.card_pair (member.resolved_new_first_ne_second hPosition)]

/-- **nd2: `e'` dies with `e₁` and the endpoint is only divalent.** -/
theorem resolved_nonDanglingIncident_single_nd2 (hPosition : member.position ≠ member.double)
    (hNd2 : IsDangling data member.profile.first.1)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    nonDanglingIncident member.candidate.datum (member.vertex member.single sheet) =
      {member.candidate.oldSourceEdge member.profile.third.1,
        member.candidate.newSourceEdge (secondSheet member.profile.toOccurrenceProfile)} :=
  nonDanglingIncident_pair_of_card_three member.candidate.datum
    (member.third_incident_vertex hSheet)
    (member.resolved_new_second_incident_single hPosition hSheet)
    (member.resolved_new_first_incident_single hPosition hSheet)
    (member.old_ne_new _ _) (member.old_ne_new _ _)
    (Ne.symm (member.resolved_new_first_ne_second hPosition))
    member.third_survives (member.resolved_new_second_survives hPosition)
    (by
      by_contra hSurvives
      exact ((member.resolved_new_first_survives_iff hPosition).mp hSurvives) hNd2)
    (member.resolved_card_single hPosition hSheet)

theorem resolved_nonDanglingValency_single_nd2 (hPosition : member.position ≠ member.double)
    (hNd2 : IsDangling data member.profile.first.1)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    nonDanglingValency member.candidate.datum (member.vertex member.single sheet) = 2 := by
  rw [← card_nonDanglingIncident,
    member.resolved_nonDanglingIncident_single_nd2 hPosition hNd2 hSheet,
    Finset.card_pair (member.old_ne_new _ _)]

end BlockMember

end ResolvedSingle

/-! ## §8  The background census, over every wall block that is **neither**
`A₀` **nor** `B₀`

`Pair.background` says every other wall block above the divalent wall is
unramified, so each direction contributes exactly one occurrence there, both
new endpoints are divalent and the new occurrence is a *subdivision*: it
dangles exactly when the same-sheet old occurrence does, and shares its stable
row when it survives.  The hypothesis is `¬ Rel first ∧ ¬ Rel second` --
**both** ramification-one blocks are excluded, which is the one place where
the two-block structure changes the shape of a census statement. -/

section Background

variable (pair : Pair data star)

theorem background_ramification_zero {sheet : Fin degree}
    (hFirst : ¬(data.vertexPartition wall).Rel pair.first.1 sheet)
    (hSecond : ¬(data.vertexPartition wall).Rel pair.second.1 sheet) :
    data.localRamification wall ((data.vertexPartition wall).toBlock sheet) = 0 :=
  pair.background (WallBlock.ofSheet data wall sheet)
    (fun hEq ↦ hFirst ((WallBlock.ofSheet_eq_iff_rel data wall pair.first sheet).mp hEq))
    (fun hEq ↦ hSecond ((WallBlock.ofSheet_eq_iff_rel data wall pair.second sheet).mp hEq))

/-- One occurrence per direction above a background block. -/
theorem background_blockCount (label : Fin 2) {sheet : Fin degree}
    (hFirst : ¬(data.vertexPartition wall).Rel pair.first.1 sheet)
    (hSecond : ¬(data.vertexPartition wall).Rel pair.second.1 sheet) :
    (data.edgePartition (star.edge label)).blockCountWithin
      (data.vertexPartition wall) sheet = 1 :=
  blockCountWithin_eq_one_of_divalent_localRamification_zero data wall
    star.card_incidentEdges sheet (background_ramification_zero pair hFirst hSecond) _
    (star.edge_mem_incidentEdges label)

theorem background_resolution_at_repr (position : Fin 2) {sheet : Fin degree}
    (hFirst : ¬(data.vertexPartition wall).Rel pair.first.1 sheet)
    (hSecond : ¬(data.vertexPartition wall).Rel pair.second.1 sheet) :
    (pair.candidate position).resolution ((data.vertexPartition wall).repr sheet) =
      joinedResolutionAt (data.vertexPartition wall) :=
  pair.resolution_of_background position
    (fun hRel ↦ hFirst (hRel.trans ((data.vertexPartition wall).rel_repr_left sheet)))
    (fun hRel ↦ hSecond (hRel.trans ((data.vertexPartition wall).rel_repr_left sheet)))

/-- **Both background new endpoints are divalent**, for both members. -/
theorem background_card_incident (position : Fin 2) {sheet : Fin degree}
    (hFirst : ¬(data.vertexPartition wall).Rel pair.first.1 sheet)
    (hSecond : ¬(data.vertexPartition wall).Rel pair.second.1 sheet) :
    Fintype.card (IncidentSourceEdge (pair.candidate position).datum
        ((pair.candidate position).datum.sourceEndpoint (oldVertex target wall) sheet)) = 2 ∧
      Fintype.card (IncidentSourceEdge (pair.candidate position).datum
        ((pair.candidate position).datum.sourceEndpoint (freshVertex target) sheet)) = 2 := by
  have hRes := background_resolution_at_repr pair position hFirst hSecond
  constructor
  · rw [card_incident_oldEndpoint (twoStar := star) (fun _ ↦ rfl) sheet,
      LocalResolution.paste_newEdge_blockCountWithin_left, hRes,
      LocalResolution.blockCountWithin_paste_left, hRes]
    simp only [joinedResolutionAt, SheetPartition.blockCountWithin_self,
      background_blockCount pair 0 hFirst hSecond]
  · rw [card_incident_freshEndpoint (twoStar := star) (fun _ ↦ rfl) sheet,
      LocalResolution.paste_newEdge_blockCountWithin_right, hRes,
      LocalResolution.blockCountWithin_paste_right, hRes]
    simp only [joinedResolutionAt, SheetPartition.blockCountWithin_self,
      background_blockCount pair 1 hFirst hSecond]

/-- The same-sheet old occurrence over a direction meets the endpoint that
direction names. -/
theorem background_old_incident (position label : Fin 2) (sheet : Fin degree) :
    Incident (pair.candidate position).datum
      ((pair.candidate position).oldSourceEdge (data.sourceEdge (star.edge label) sheet))
      ((pair.candidate position).datum.sourceEndpoint
        (LimitChainCore.wallSide target wall (side label)) sheet) :=
  old_incident (fun _ ↦ rfl) label sheet

/-- **A background new occurrence is a subdivision.**  It dangles exactly when
the same-sheet old occurrence over the direction naming its endpoint does --
so the two old occurrences and the new one all live or all die together. -/
theorem background_survives_iff (hValid : data.Valid) (position label : Fin 2)
    {sheet : Fin degree}
    (hFirst : ¬(data.vertexPartition wall).Rel pair.first.1 sheet)
    (hSecond : ¬(data.vertexPartition wall).Rel pair.second.1 sheet) :
    (¬ IsDangling (pair.candidate position).datum
        ((pair.candidate position).newSourceEdge sheet)) ↔
      ¬ IsDangling data (data.sourceEdge (star.edge label) sheet) := by
  have hCard : Fintype.card (IncidentSourceEdge (pair.candidate position).datum
      ((pair.candidate position).datum.sourceEndpoint
        (LimitChainCore.wallSide target wall (side label)) sheet)) = 2 := by
    by_cases hLabel : label = 0
    · subst hLabel
      exact (background_card_incident pair position hFirst hSecond).1
    · have hOne : label = 1 := by omega
      subst hOne
      exact (background_card_incident pair position hFirst hSecond).2
  refine (survives_iff_of_card_two (pair.candidate position).datum
    ((pair.candidate position).datum_valid hValid).1 _
    ((pair.candidate position).newSourceEdge sheet)
    ((pair.candidate position).oldSourceEdge (data.sourceEdge (star.edge label) sheet))
    (new_incident label sheet) (background_old_incident pair position label sheet)
    hCard).trans ?_
  exact not_congr (ResolutionPruning.isDangling_oldSourceEdge_iff _ hValid
    (pair.candidate_sourceGenus position) _)

/-- **The complete surviving star at a surviving background endpoint**: the
new occurrence and that side's old occurrence. -/
theorem background_nonDanglingIncident (hValid : data.Valid) (position label : Fin 2)
    {sheet : Fin degree}
    (hFirst : ¬(data.vertexPartition wall).Rel pair.first.1 sheet)
    (hSecond : ¬(data.vertexPartition wall).Rel pair.second.1 sheet)
    (hOld : ¬ IsDangling data (data.sourceEdge (star.edge label) sheet)) :
    nonDanglingIncident (pair.candidate position).datum
        ((pair.candidate position).datum.sourceEndpoint
          (LimitChainCore.wallSide target wall (side label)) sheet) =
      {(pair.candidate position).newSourceEdge sheet,
        (pair.candidate position).oldSourceEdge
          (data.sourceEdge (star.edge label) sheet)} := by
  have hCard : Fintype.card (IncidentSourceEdge (pair.candidate position).datum
      ((pair.candidate position).datum.sourceEndpoint
        (LimitChainCore.wallSide target wall (side label)) sheet)) = 2 := by
    by_cases hLabel : label = 0
    · subst hLabel
      exact (background_card_incident pair position hFirst hSecond).1
    · have hOne : label = 1 := by omega
      subst hOne
      exact (background_card_incident pair position hFirst hSecond).2
  exact nonDanglingIncident_pair_of_card_two (pair.candidate position).datum
    (new_incident label sheet) (background_old_incident pair position label sheet)
    (Ne.symm (oldSourceEdge_ne_newSourceEdge _ _))
    ((background_survives_iff pair hValid position label hFirst hSecond).mpr hOld)
    (ResolutionSurvival.not_isDangling_oldSourceEdge _ hValid.1 _ hOld) hCard

/-- **A surviving background new occurrence keeps the old occurrence's stable
row.** -/
theorem background_stablePath_eq (hValid : data.Valid) (position label : Fin 2)
    {sheet : Fin degree}
    (hFirst : ¬(data.vertexPartition wall).Rel pair.first.1 sheet)
    (hSecond : ¬(data.vertexPartition wall).Rel pair.second.1 sheet)
    (hOld : ¬ IsDangling data (data.sourceEdge (star.edge label) sheet)) :
    NonDanglingEdge.stablePath
        (⟨(pair.candidate position).newSourceEdge sheet,
          (background_survives_iff pair hValid position label hFirst hSecond).mpr hOld⟩ :
          NonDanglingEdge (pair.candidate position).datum) =
      NonDanglingEdge.stablePath
        (⟨(pair.candidate position).oldSourceEdge
            (data.sourceEdge (star.edge label) sheet),
          ResolutionSurvival.not_isDangling_oldSourceEdge _ hValid.1 _ hOld⟩ :
          NonDanglingEdge (pair.candidate position).datum) := by
  have hCard : Fintype.card (IncidentSourceEdge (pair.candidate position).datum
      ((pair.candidate position).datum.sourceEndpoint
        (LimitChainCore.wallSide target wall (side label)) sheet)) = 2 := by
    by_cases hLabel : label = 0
    · subst hLabel
      exact (background_card_incident pair position hFirst hSecond).1
    · have hOne : label = 1 := by omega
      subst hOne
      exact (background_card_incident pair position hFirst hSecond).2
  refine stablePath_eq_of_consecutive ⟨?_, _, new_incident label sheet,
    background_old_incident pair position label sheet, ?_⟩
  · intro hEqual
    exact oldSourceEdge_ne_newSourceEdge _ _
      (congrArg (fun edge : NonDanglingEdge (pair.candidate position).datum ↦ edge.1)
        hEqual).symm
  · exact nonDanglingValency_eq_two_of_card_two_of_survives _
      ((pair.candidate position).datum_valid hValid).1 _ _ (new_incident label sheet)
      ((background_survives_iff pair hValid position label hFirst hSecond).mpr hOld) hCard

end Background

/-! ## §9  The two members at the two blocks

Each member of `Pair` is **two** `BlockMember`s over one candidate: at `A₀`
with `position` and at `B₀` with `other position`.  Nothing else changes, and
the whole of §4--§7 applies verbatim at each. -/

section Members

variable (pair : Pair data star) (hValid : data.Valid)

/-- Member `q`, read at `A₀`. -/
noncomputable def firstMember (position : Fin 2) : BlockMember data star pair.first where
  candidate := pair.candidate position
  profile := pair.firstProfile
  position := position
  right_eq := fun _ ↦ rfl
  local_eq := fun _ hAnchor ↦ pair.resolution_of_first position hAnchor
  valid := hValid
  genus_eq := pair.candidate_sourceGenus position

/-- Member `q`, read at `B₀` -- at the **opposite** position, which is the
`δ⁽ᵠ⁾(Ã) ≠ δ⁽ᵠ⁾(B̃)` of Part I's proof of Equation (*) for this case. -/
noncomputable def secondMember (position : Fin 2) : BlockMember data star pair.second where
  candidate := pair.candidate position
  profile := pair.secondProfile
  position := other position
  right_eq := fun _ ↦ rfl
  local_eq := fun _ hAnchor ↦ pair.resolution_of_second position hAnchor
  valid := hValid
  genus_eq := pair.candidate_sourceGenus position

@[simp] theorem firstMember_candidate (position : Fin 2) :
    (firstMember pair hValid position).candidate = pair.candidate position := rfl

@[simp] theorem firstMember_position (position : Fin 2) :
    (firstMember pair hValid position).position = position := rfl

@[simp] theorem firstMember_profile (position : Fin 2) :
    (firstMember pair hValid position).profile = pair.firstProfile := rfl

@[simp] theorem secondMember_candidate (position : Fin 2) :
    (secondMember pair hValid position).candidate = pair.candidate position := rfl

@[simp] theorem secondMember_position (position : Fin 2) :
    (secondMember pair hValid position).position = other position := rfl

@[simp] theorem secondMember_profile (position : Fin 2) :
    (secondMember pair hValid position).profile = pair.secondProfile := rfl

/-- **Both blocks of one member are read by the same census**: the two
`BlockMember`s share the candidate and differ only in the block, the profile
and the position. -/
theorem members_share_candidate (position : Fin 2) :
    (firstMember pair hValid position).candidate =
      (secondMember pair hValid position).candidate := rfl

/-- **The member's two branch vertices sit on opposite sides of the new
edge.**  This is the `ch u = ch v = 1` of Part I's proof of Equation (*) for
this case, and it is the case's one
genuinely new phenomenon: a member has *two* trivalent expanded endpoints
above the wall, one over `A₀` and one over `B₀`, and they are never on the
same side. -/
theorem branch_positions_ne (position : Fin 2) :
    (secondMember pair hValid position).position ≠
      (firstMember pair hValid position).position :=
  other_ne position

theorem branch_side_ne (position : Fin 2) :
    side (other position) = !(side position) := by
  revert position
  decide

/-- The valency dictionary at `A₀`: three incidences on side `position`. -/
theorem first_card_vertex (position label : Fin 2) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel pair.first.1 sheet) :
    Fintype.card (IncidentSourceEdge (pair.candidate position).datum
        ((pair.candidate position).datum.sourceEndpoint
          (LimitChainCore.wallSide target wall (side label)) sheet)) =
      if position = label then 3 else 2 :=
  card_incident_side pair.firstProfile.toOccurrenceProfile (fun _ ↦ rfl)
    (fun _ hAnchor ↦ pair.resolution_of_first position hAnchor) label hSheet

/-- and at `B₀`: three incidences on side `other position`. -/
theorem second_card_vertex (position label : Fin 2) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel pair.second.1 sheet) :
    Fintype.card (IncidentSourceEdge (pair.candidate position).datum
        ((pair.candidate position).datum.sourceEndpoint
          (LimitChainCore.wallSide target wall (side label)) sheet)) =
      if other position = label then 3 else 2 :=
  card_incident_side pair.secondProfile.toOccurrenceProfile (fun _ ↦ rfl)
    (fun _ hAnchor ↦ pair.resolution_of_second position hAnchor) label hSheet

end Members

/-! ## §10  Scoping against `LimitChainCore`: what fits and what does not

**§2 of the core fits.**  A `{w2-r1}` member retains exactly one wall
direction at the retained endpoint, so it is a `LimitChainCore.WallCandidate`
with `retainedTarget = star.edge 0`, and §0--§2 of the core -- the occurrence
identities, the star readers and the two-star incidence counts -- are used
verbatim throughout §1--§8 above.

**§3--§4 of the core do not.**  `BackgroundShape` is not "the member off the
distinguished block": its three block clauses pin the background's *shape*,
and what they pin is that **the background's branch vertex is the fresh
endpoint** -- `right_block` gives the fresh endpoint the whole wall block,
`left_block` and `newEdge_block` give the retained endpoint and the new edge
the retained direction's classes, and every theorem of `Background` reads the
fresh endpoint.  A `{w2-r1}` member has **two** branch vertices, above `A₀` on
side `position` and above `B₀` on side `other position`, opposite by Part I's
proof of Equation (*) for this case.
So exactly one of them is fresh, and the block carrying the other one cannot
satisfy the clauses.  That is `backgroundClausesAt_iff` below, and its
consequence `not_backgroundClauses_both`: for **neither** member is there a
`BackgroundShape` whose background excludes both `A₀` and `B₀`.

The census above is therefore standalone, and `§11` records what a two-block
core variant would need. -/

section Scoping

/-- **A `{w2-r1}` member is a `LimitChainCore.WallCandidate`.**  §0--§2 of the
core scope unchanged. -/
noncomputable def wallCandidate (pair : Pair data star) (position : Fin 2) :
    LimitChainCore.WallCandidate data wall :=
  LimitChainCore.WallCandidate.ofTwoStar (pair.candidate position) star (fun _ ↦ rfl)

@[simp] theorem wallCandidate_candidate (pair : Pair data star) (position : Fin 2) :
    (wallCandidate pair position).candidate = pair.candidate position := rfl

@[simp] theorem wallCandidate_retainedTarget (pair : Pair data star) (position : Fin 2) :
    (wallCandidate pair position).retainedTarget = star.edge 0 := rfl

/-- **The single direction sees the block whole**, as a block equality and not
only as a count. -/
theorem single_block_eq_wall_block {block : WallBlock data wall}
    (profile : W2R1SourceProfile.OccurrenceProfile data star block) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    (singlePartition profile).block sheet = (data.vertexPartition wall).block sheet := by
  ext other
  simp only [SheetPartition.mem_block_iff]
  constructor
  · intro hRel
    exact (star.edgePartition_refines_wall data profile.singleLabel).rel hRel
  · intro hRel
    exact (singlePartition_covers profile sheet hSheet).symm.trans
      (singlePartition_covers profile other (hSheet.trans hRel))

/-- The three block clauses of `LimitChainCore.BackgroundShape`, read at one
wall block: this is exactly what that structure demands of a member at every
sheet outside its distinguished block. -/
def BackgroundClausesAt (C : BalancedGlobal.Candidate target degree data wall)
    (retainedTarget : target.edges) (block : WallBlock data wall) : Prop :=
  ∀ sheet : Fin degree, (data.vertexPartition wall).Rel block.1 sheet →
    (pasted C).left.block sheet = (data.edgePartition retainedTarget).block sheet ∧
      (pasted C).right.block sheet = (data.vertexPartition wall).block sheet ∧
        (pasted C).newEdge.block sheet = (data.edgePartition retainedTarget).block sheet

/-- **The background clauses hold at a ramification-one block exactly when the
member's branch vertex there is the fresh endpoint**, i.e. exactly when the
member's local position at that block is `1`.  Uniform in the block's own
doubled direction: the two configurations `double = 0` and `double = 1` fail
in *different* clauses (`left_block`/`newEdge_block` and `right_block`
respectively) and agree on the answer. -/
theorem backgroundClausesAt_iff {block : WallBlock data wall}
    {C : BalancedGlobal.Candidate target degree data wall}
    (profile : W2R1SourceProfile.OccurrenceProfile data star block) {position : Fin 2}
    (hLocal : ∀ anchor, (data.vertexPartition wall).Rel block.1 anchor →
      C.resolution anchor = memberLocal data star profile.doubleLabel position) :
    BackgroundClausesAt C (star.edge 0) block ↔ position = 1 := by
  constructor
  · intro hClauses
    by_contra hPosition
    have hZero : position = 0 := by omega
    have hRelSheets : (data.vertexPartition wall).Rel
        (firstSheet profile) (secondSheet profile) :=
      (firstSheet_rel profile).symm.trans (secondSheet_rel profile)
    have hMem : secondSheet profile ∈
        (data.vertexPartition wall).block (firstSheet profile) :=
      ((data.vertexPartition wall).mem_block_iff _ _).mpr hRelSheets
    obtain ⟨hLeft, hRight, _⟩ := hClauses (firstSheet profile) (firstSheet_rel profile)
    rw [pasted_left_block hLocal (firstSheet_rel profile)] at hLeft
    rw [pasted_right_block hLocal (firstSheet_rel profile)] at hRight
    by_cases hDouble : profile.doubleLabel = 0
    · rw [memberLocal_of_eq data star (hZero.trans hDouble.symm)] at hLeft
      change (data.vertexPartition wall).block (firstSheet profile) = _ at hLeft
      rw [hLeft, ← hDouble] at hMem
      exact doublePartition_separate profile
        ((SheetPartition.mem_block_iff _ _ _).mp hMem)
    · have hOne : profile.doubleLabel = 1 := by omega
      have hNe : position ≠ profile.doubleLabel := by rw [hZero, hOne]; decide
      rw [memberLocal_of_ne data star hNe,
        sideFine_right_of_ne_zero data star hDouble] at hRight
      rw [← hRight] at hMem
      exact doublePartition_separate profile
        ((SheetPartition.mem_block_iff _ _ _).mp hMem)
  · intro hPosition sheet hSheet
    by_cases hDouble : profile.doubleLabel = 0
    · have hNe : position ≠ profile.doubleLabel := by rw [hPosition, hDouble]; decide
      rw [pasted_left_block hLocal hSheet, pasted_right_block hLocal hSheet,
        pasted_newEdge_block hLocal hSheet, memberLocal_of_ne data star hNe,
        sideFine_left_of_zero data star hDouble, sideFine_right_of_zero data star hDouble,
        sideFine_newEdge, hDouble]
      exact ⟨rfl, rfl, rfl⟩
    · have hOne : profile.doubleLabel = 1 := by omega
      have hEq : position = profile.doubleLabel := by rw [hPosition, hOne]
      have hSingle : profile.singleLabel = 0 := by
        have hLabels := profile.labels_ne
        omega
      have hBlock : (data.edgePartition (star.edge 0)).block sheet =
          (data.vertexPartition wall).block sheet := by
        rw [← hSingle]
        exact single_block_eq_wall_block profile hSheet
      rw [pasted_left_block hLocal hSheet, pasted_right_block hLocal hSheet,
        pasted_newEdge_block hLocal hSheet, memberLocal_of_eq data star hEq]
      exact ⟨hBlock.symm, rfl, hBlock.symm⟩

end Scoping

/-! ## §11  The scoping decision, at the pair

`backgroundClausesAt_iff` at the two blocks of `Pair`: for member `q` the
clauses hold at `A₀` exactly when `q = 1` and at `B₀` exactly when `q = 0`.
So **exactly one** of the two ramification-one blocks can be background, and
it is a different one for each member -- there is no choice of `selected`
serving both members, and none at all serving the deliverable's requirement
that both `A₀` and `B₀` be outside the background. -/

section ScopingPair

variable (pair : Pair data star)

/-- At `A₀`: the background clauses hold exactly for member `1`. -/
theorem backgroundClauses_first_iff (position : Fin 2) :
    BackgroundClausesAt (pair.candidate position) (star.edge 0) pair.first ↔ position = 1 :=
  backgroundClausesAt_iff pair.firstProfile.toOccurrenceProfile
    (fun _ hAnchor ↦ pair.resolution_of_first position hAnchor)

/-- At `B₀`: exactly for member `0`, because `B₀` sits at the opposite
position. -/
theorem backgroundClauses_second_iff (position : Fin 2) :
    BackgroundClausesAt (pair.candidate position) (star.edge 0) pair.second ↔
      position = 0 := by
  refine (backgroundClausesAt_iff pair.secondProfile.toOccurrenceProfile
    (fun _ hAnchor ↦ pair.resolution_of_second position hAnchor)).trans ?_
  revert position
  decide

/-- **Exactly one of the two ramification-one blocks satisfies the background
clauses** -- so a `LimitChainCore.BackgroundShape` for a `{w2-r1}` member
always absorbs the *other* ramification-one block into its background. -/
theorem backgroundClauses_first_or_second (position : Fin 2) :
    BackgroundClausesAt (pair.candidate position) (star.edge 0) pair.first ∨
      BackgroundClausesAt (pair.candidate position) (star.edge 0) pair.second := by
  by_cases hPosition : position = 1
  · exact Or.inl ((backgroundClauses_first_iff pair position).mpr hPosition)
  · exact Or.inr ((backgroundClauses_second_iff pair position).mpr (by omega))

/-- **and never both.**  This is the machine-checked form of the scoping
decision: no `LimitChainCore.BackgroundShape` over a `{w2-r1}` member has both
`A₀` and `B₀` outside its distinguished block, for either member. -/
theorem not_backgroundClauses_both (position : Fin 2) :
    ¬(BackgroundClausesAt (pair.candidate position) (star.edge 0) pair.first ∧
      BackgroundClausesAt (pair.candidate position) (star.edge 0) pair.second) := by
  rintro ⟨hFirst, hSecond⟩
  have hOne := (backgroundClauses_first_iff pair position).mp hFirst
  have hZero := (backgroundClauses_second_iff pair position).mp hSecond
  rw [hOne] at hZero
  exact absurd hZero (by decide)

/-- **and no single block serves both members**: the block that can be
background for member `0` is `B₀` and for member `1` is `A₀`. -/
theorem backgroundClauses_not_uniform :
    ¬(BackgroundClausesAt (pair.candidate 0) (star.edge 0) pair.first ∧
      BackgroundClausesAt (pair.candidate 1) (star.edge 0) pair.first) := by
  rintro ⟨hZero, _⟩
  exact absurd ((backgroundClauses_first_iff pair 0).mp hZero) (by decide)

end ScopingPair


/-! ## §12  The two extra row identities of the nd2 sub-case

In `{w2-r1-nd2}` the endpoint that is trivalent in `{w2-r1-nd3}` loses one
occurrence and becomes divalent, which buys one further row identity in each
member.  Downstairs `e₂` and `e₃` already share a row
(`W2R1SourceProfile.SourceProfile.nd2_stablePath_eq`), so both identities say
the same thing upstairs: **in `nd2` every surviving new occurrence above the
block lies in the single row carrying `e₂` and `e₃`.** -/

section Nd2Rows

variable {block : WallBlock data wall} (member : BlockMember data star block)

namespace BlockMember

/-- The profile's own trichotomy, so that §6 and §7 together are exhaustive. -/
theorem nd_cases :
    (nonDanglingValency data (WallBlock.sourceVertex data wall block) = 3 ∧
        ¬ IsDangling data member.profile.first.1) ∨
      (nonDanglingValency data (WallBlock.sourceVertex data wall block) = 2 ∧
        IsDangling data member.profile.first.1 ∧
          data.sourceEdgeIndex member.profile.first.1 = 1 ∧
            data.sourceEdgeIndex member.profile.third.1 =
              data.sourceEdgeIndex member.profile.second.1 + 1) :=
  member.profile.cases

/-- nd2, retained member: `e'` also joins `e₂`'s row. -/
theorem retained_new_stablePath_eq_second_nd2 (hPosition : member.position = member.double)
    (hNd2 : IsDangling data member.profile.first.1)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    NonDanglingEdge.stablePath (⟨member.candidate.newSourceEdge sheet,
        member.retained_new_survives hPosition hSheet⟩ :
        NonDanglingEdge member.candidate.datum) =
      NonDanglingEdge.stablePath (⟨member.candidate.oldSourceEdge member.profile.second.1,
        member.second_survives⟩ : NonDanglingEdge member.candidate.datum) := by
  refine stablePath_eq_of_consecutive ⟨?_, member.vertex member.double sheet,
    member.new_incident_vertex member.double sheet,
    member.retained_second_incident hPosition hSheet,
    member.retained_nonDanglingValency_double_nd2 hPosition hNd2 hSheet⟩
  intro hEqual
  exact member.old_ne_new member.profile.second.1 sheet
    (congrArg (fun edge : NonDanglingEdge member.candidate.datum ↦ edge.1) hEqual).symm

/-- nd2, resolved member: `e''` also joins `e₃`'s row. -/
theorem resolved_new_second_stablePath_eq_third_nd2
    (hPosition : member.position ≠ member.double)
    (hNd2 : IsDangling data member.profile.first.1)
    {sheet : Fin degree} (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    NonDanglingEdge.stablePath
        (⟨member.candidate.newSourceEdge (secondSheet member.profile.toOccurrenceProfile),
          member.resolved_new_second_survives hPosition⟩ :
          NonDanglingEdge member.candidate.datum) =
      NonDanglingEdge.stablePath (⟨member.candidate.oldSourceEdge member.profile.third.1,
        member.third_survives⟩ : NonDanglingEdge member.candidate.datum) := by
  refine stablePath_eq_of_consecutive ⟨?_, member.vertex member.single sheet,
    member.resolved_new_second_incident_single hPosition hSheet,
    member.third_incident_vertex hSheet,
    member.resolved_nonDanglingValency_single_nd2 hPosition hNd2 hSheet⟩
  intro hEqual
  exact member.old_ne_new member.profile.third.1 _
    (congrArg (fun edge : NonDanglingEdge member.candidate.datum ↦ edge.1) hEqual).symm

/-- **A second scoping obstruction, independent of §10.**  In
`{w2-r1-nd2}` the distinguished source vertex is itself **divalent** (`k₁ = 1`,
`e₁` dangling), so `LimitChainCore.LiftData`'s field `selected_valency_ne_two`
fails at a ramification-one block in that sub-case: even a one-block `LiftData`
cannot be instantiated there.  A two-block core variant must drop or weaken that
field as well (as `LimitChainTwoBlock` does) -- its role is only to make the
selected case of the stable lift vacuous, and here the lift must instead use the
two row identities of §12. -/
theorem nd2_selected_valency_eq_two :
    ∀ {block : WallBlock data wall}
      (profile : W2R1SourceProfile.SourceProfile data star block),
      IsDangling data profile.first.1 →
      ∀ {sheet : Fin degree}, (data.vertexPartition wall).Rel block.1 sheet →
        nonDanglingValency data (data.sourceEndpoint wall sheet) = 2 := by
  intro block profile hNd2 sheet hSheet
  rw [LimitChainCore.sourceEndpoint_eq_of_rel data wall hSheet.symm]
  exact (nd2_displayed_indices profile hNd2).1

end BlockMember

end Nd2Rows

end DraismaVargas.LocalCases.W2R1StableGraph
