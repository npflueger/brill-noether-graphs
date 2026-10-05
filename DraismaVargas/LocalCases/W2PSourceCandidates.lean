module

public import DraismaVargas.LocalCases.GlobalP
public import DraismaVargas.LocalCases.M11SourceGenus
public import DraismaVargas.LocalCases.W3ShiftSourceCandidates
public import DraismaVargas.LocalCases.W3ShiftShrinkExistence

@[expose] public section

/-!
# Source-derived case-P geometry (Figure 35)

Source: Draisma–Vargas Part I, arXiv:1909.12924, case `{w2-r2-nd3-P}`, Figure 35 and
Equation (9).  The ambient hypotheses are `{w2-r2}` (where Base I/II is fixed
once for the whole `{w2}` section) and `{w2-r2-nd3}` (where Cardinality M and P
are separated, and the Base II.1/II.2 sub-cases used below are stated).

Cardinality P puts the dangling occurrence `e₄` above `t₂`, so
`k₁ + k₂ + 1 = |A₀| = k₃`, and Figure 35's three members are Base II.2.1.P
(`M⁽¹⁾`), Base II.2.2.P (`M⁽²⁾`) and Base II.1.P (`M⁽³⁾`).

This is the **nd3** P case.  The nd2 P case (Part I, case `{w2-r2-nd2-P}`,
Figure 36) is a different, excluded case -- one member, non-full-dimensional --
and the `W2R2Nd2P*` modules belong to it, not here.

Everything is derived from an actual `W2R2SourceProfile.SourceProfile`: the
`t₂` endpoint partition is not a parameter but the direction's own occurrence
partition, the dangling sheet is the profile's own `deleted` occurrence, and
the `k` identities come from the profile's `cases` field rather than from the
figure.

## The third member's shape: a **one-sided** detachment

`ResolutionP.residualResolution` sets `left := wall`, `right := wall` and
`newEdge := wall.detachSheet …`, so its Euler count is one too large
(`residualResolution_card_blocks`) and **every** candidate assembled from it
has source genus exactly one greater than the datum's
(`residualResolution_sourceGenus_eq_succ`, the exact analogue of
`W3ShiftShrinkExistence.detachedResolution_sourceGenus_eq_succ`).  Over `t₁`
the detached singleton and the residual class join the same pair of ends: a
parallel pair.

Checked against Figure 35, the shape it is meant to build is `M⁽³⁾`, Base
II.1.P.  There the vertex of `G⁽ᵠ⁾_{A₀}` above `u` is
`A⁽ᵠ⁾ = e₁ ∪ e₂` with `|A⁽ᵠ⁾| = |e'| = k₁ + k₂`, while the vertex above `v` is
`A'` with `|A'| = k₃ = k₁ + k₂ + 1 = |A₀|`: Case (r1-nd2) of Part I's local
properties reads `|e₃⁽ᵠ⁾| = |A'|` and `|e'| = |A'| - 1`.  So the figure calls
for **exactly one** detachment, and it is on the `t₂` side, which is the side
`residualResolution` leaves undetached.  `bothDetachedResolution` is therefore
*not* the right shape here: it would shrink the `t₃` endpoint to `|A₀| - 1`,
contradicting Base II.1.P's `|A'| = k₃`.  The genus-preserving shape is
`leftSplitResolution` below, whose Euler defect is zero
(`leftSplitResolution_sourceGenus_eq`), and it keeps `residualResolution`'s
new edge **unchanged** (`thirdLocal_newEdge_eq`): only the left endpoint moves.

The same reading makes all three Figure 35 members one shape: the `t₂`
endpoint and the new edge carry one common coarsening of the `t₂` occurrence
partition, and the `t₃` endpoint carries the whole wall block.  For `M⁽¹⁾` and
`M⁽²⁾` that shape is already `ResolutionP.attachedResolution`
(`attachedResolution_eq_leftSplit`), which is why their Euler defect is zero.

## The three members share one gluing datum

`exists_geometry` builds a `GlobalP.Geometry` at an actual case-P profile, and
`members_share_datum` builds all three `GlobalMkk.DivalentPattern`s over that
one `data` and that one `Geometry`.  Neither neighbouring obstruction occurs:

* not the opposition of two free choices of the M-1k case, because no member
  constrains a sheet that another member constrains oppositely -- every
  exterior condition here is a refinement in the easy direction;
* not the pinning of the M-kk case, because **nothing is detached from the `t₂`
  occurrence partition at all**.  All three members *merge* blocks of it
  (`e₁ ∪ e₄`, `e₂ ∪ e₄`, `e₁ ∪ e₂`), and a merge is always refined by what it
  merges (`SheetPartition.refines_mergeBlocks`), so the `t₂` exterior
  condition is automatic; the `t₃` exterior condition is
  `(edgePartition e).Refines (vertexPartition wall)`, a field of every
  `GluingDatum`.

The genus defect of `residualResolution` is not a matter of gauge: the `+1` of
`residualResolution_sourceGenus_eq_succ` is quantified over **all** arguments,
including all relabellings of the datum, so no branch swap removes it.
Conversely the shared datum is a positive statement, and a positive statement
is not weakened by gauge.

### No coupling between the genus and the shared datum

In the M-kk case the one-sided bundle of `GlobalMkk` is jointly satisfiable
*only because* its `t₃` exterior condition, with `right := wall`, degenerates
to a field of every `GluingDatum`; the genus-preserving shape empties it, which
is why `GlobalMkk` takes one member over a swapped datum
(`W2MkkSourceCandidates`).  **`GlobalP` does not have that coupling.**  Putting
`thirdLocal` on the genus-preserving shape turns its *left* exterior condition
from the vacuous `Refines wall` into `(edgePartition t₂).Refines (wall.detachSheet extra …)`,
and that is discharged by `SheetPartition.refines_detachSheet_of_block_singleton`
from `Geometry.extraSingleton` -- **a field `GlobalP.Geometry` already has**,
and one an actual profile satisfies because `e₄` is the dangling index-one
occurrence.  Both `members_share_datum` (the literal bundle) and
`repaired_members_share_datum` (the bundle with `M⁽³⁾` on the genus-preserving
shape) are proved inhabited at the same actual profile, so no swapped datum is
needed, and the only defect of `GlobalP.candidates` is the genus of its third
member.

## Base II.2.1.P, read through Case (r1-nd2)

Part I states Base II.2.1.P as "`|e'| = |A'| + 1 = k₁ + 1`", while Case (r1-nd2)
of its local properties offers a vertex only the two edge sizes `|A'|` and
`|A'| - 1`, an edge class being a subset of its endpoint class.  This file uses
the labelling `|e₁⁽ᵠ⁾| = |A'| - 1 = k₁`, so that the refinement above `t₂`,
`|e₁⁽ᵠ⁾| + |e₄⁽ᵠ⁾| = |A'|`, gives `|A'| = k₁ + 1 = |e'|`.  This differs from
Part I's statement only in the identification of `|A'|`: the index
`|e'| = k₁ + 1` and the Cardinality equation `(k₁+1) + k₂ = k₃` are the same,
and Figure 35's box prints only the index.  In the Cardinality M branch the
dangling occurrence is above `t₃` and `A'` is not enlarged, so there the two
readings agree.  Both sides are cardinalities of one vertex's own local data,
so relabelling does not affect this.  The identity used is
`firstLocal_newEdge_blockCard_eq_left` and its `second` mirror.

## What is constructed

`firstMember`, `secondMember`, `thirdMember` -- Figure 35's `M⁽¹⁾`, `M⁽²⁾`,
`M⁽³⁾` as actual arbitrary-degree outgoing gluing data over one profile --
with validity (`firstMember_valid`, ...), source genus
(`firstMember_sourceGenus`, ...), the target valencies of both new endpoints
(`firstMember_target_valencies`, ..., both `2`), the displayed new-edge block
cardinalities (`firstMember_indices`, `secondMember_indices`,
`thirdMember_indices`), the retained `t₃` endpoint cardinality `|A'| = k₃`
(`right_blockCard`, common to all three) and the induced block counts on `A₀`
(`firstMember_blockCountWithin`, ...: `2 + 1 = 2 + 1`).

The genus route is `M11SourceGenus.candidate_sourceGenus_of_stars`, not
`candidate_sourceGenus_of_blockwise_euler`: once the third member is on the
shape Figure 35 calls for, all three members *are* stars in that lemma's sense
-- `right = wall` and `newEdge = left` -- which is the same observation as the
first section seen from the Euler side.  `literalThirdMember_sourceGenus_eq_succ`
needs the blockwise route and its quantitative form, `paste_card_blocks_add`
and `candidate_sourceGenus_add`, which are general (they belong beside
`paste_block_euler_of_counts` in `M11SourceGenus`).  `blockCountWithin_eq_two`
is likewise general (it belongs beside
`SheetPartition.card_blocks_eq_sum_blockCountWithin` in `Infrastructure.Change`).
All three are kept here.

`leftSplitResolution` would sit naturally in `ResolutionP` beside
`attachedResolution` and `residualResolution`; it is stated here, with its two
genus theorems.  `orientStar`/`orientedStar`/`exists_label`/`joinedBackground_right`
are local copies of the identically named helpers in `W2MkkSourceCandidates`,
which is deliberately not imported.

Equation (9) on actual matrices, honest stable presentations, the incoming
member and the certified exit are `W2PCommonBalance`, `W2PLimitMatrix`,
`W2PIncomingMatching` and `W2PArbitraryIncomingExit`.
-/

namespace DraismaVargas.LocalCases.W2PSourceCandidates

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open ResolutionM11 ResolutionM1k GlobalM11Arbitrary

variable {d : ℕ} {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## The Figure 35 shape

All three members of Figure 35 have the same shape: the `t₂` endpoint and the
new edge carry one common partition `fine` refining the wall, and the `t₃`
endpoint carries the whole wall block.  Base II.2's `h(e₁⁽ᵠ⁾) = h(e')`,
`h(e₂⁽ᵠ⁾) = h(e'')` and Base II.1's `A⁽ᵠ⁾ = e'` (Part I, case `{w2-r2-nd3}`) are
exactly `left = newEdge`; Case (r1-nd3) at `A⁽ᵠ⁾` gives `|A'| = |e₃| = k₃`,
which with `k₃ = |A₀|` is `right = wall`. -/

/-- The Figure 35 local resolution shape: one common partition on the `t₂`
endpoint and the new edge, the whole wall block on the `t₃` endpoint. -/
def leftSplitResolution (wallPartition fine : SheetPartition d)
    (hRefines : fine.Refines wallPartition) : LocalResolution d where
  left := fine
  right := wallPartition
  newEdge := fine
  edge_refines_left := SheetPartition.Refines.refl _
  edge_refines_right := hRefines

@[simp] theorem leftSplitResolution_left (wallPartition fine : SheetPartition d)
    (hRefines : fine.Refines wallPartition) :
    (leftSplitResolution wallPartition fine hRefines).left = fine := rfl

@[simp] theorem leftSplitResolution_right (wallPartition fine : SheetPartition d)
    (hRefines : fine.Refines wallPartition) :
    (leftSplitResolution wallPartition fine hRefines).right = wallPartition := rfl

@[simp] theorem leftSplitResolution_newEdge (wallPartition fine : SheetPartition d)
    (hRefines : fine.Refines wallPartition) :
    (leftSplitResolution wallPartition fine hRefines).newEdge = fine := rfl

theorem leftSplitResolution_contracts (wallPartition fine : SheetPartition d)
    (hRefines : fine.Refines wallPartition) :
    (leftSplitResolution wallPartition fine hRefines).ContractsTo wallPartition :=
  SheetPartition.isJoin_right_of_refines hRefines

/-- `M⁽¹⁾` and `M⁽²⁾` are already of this shape: `ResolutionP.attachedResolution`
is the case `fine = endpoint.mergeBlocks first extra`. -/
theorem attachedResolution_eq_leftSplit (wallPartition endpoint : SheetPartition d)
    (first extra : Fin d) (hSeparate : ¬endpoint.Rel first extra)
    (hEndpointRefines : endpoint.Refines wallPartition)
    (hWallTogether : wallPartition.Rel first extra) :
    ResolutionP.attachedResolution wallPartition endpoint first extra hSeparate
        hEndpointRefines hWallTogether =
      leftSplitResolution wallPartition
        (endpoint.mergeBlocks first extra hSeparate)
        (endpoint.mergeBlocks_refines_coarse wallPartition first extra hSeparate
          hEndpointRefines hWallTogether) := rfl

/-! ## The Euler defects

`GlobalResolution.sourceGraph_genus_eq_iff_block_card` preserves the source
genus exactly when `#newEdge + #wall = #left + #right`. -/

/-- **`residualResolution` has block-count defect `+1`.**  Its two endpoints
are both the whole wall partition while its new edge has one block more. -/
theorem residualResolution_card_blocks (wallPartition : SheetPartition d)
    (extra remainder : Fin d) (hne : extra ≠ remainder)
    (hTogether : wallPartition.Rel extra remainder) :
    Fintype.card (ResolutionP.residualResolution wallPartition extra remainder hne
          hTogether).newEdge.Blocks +
        Fintype.card wallPartition.Blocks =
      Fintype.card (ResolutionP.residualResolution wallPartition extra remainder hne
          hTogether).left.Blocks +
        Fintype.card (ResolutionP.residualResolution wallPartition extra remainder hne
          hTogether).right.Blocks + 1 := by
  show Fintype.card (wallPartition.detachSheet extra remainder hne hTogether).Blocks +
      Fintype.card wallPartition.Blocks =
    Fintype.card wallPartition.Blocks + Fintype.card wallPartition.Blocks + 1
  rw [ResolutionMkk.card_blocks_detachSheet wallPartition extra remainder hne hTogether]
  omega

/-- **`ResolutionP.residualResolution` raises the genus, sharply.**  Any candidate
assembled from this shape on the wall block has source genus **exactly one
greater** than the incoming datum's -- for every `right` assignment, every
`extra`, every `remainder` and every compatibility proof, hence in particular
under every relabelling of the datum.  Geometrically the detached singleton and
the residual class over `t₁` join the same pair of ends, the parallel pair
Part I excludes by its no-cycle argument (in the discussion of Position II.b).

This is the exact analogue of
`W3ShiftShrinkExistence.detachedResolution_sourceGenus_eq_succ`. -/
theorem residualResolution_sourceGenus_eq_succ
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (extra remainder : Fin degree)
    (hne : extra ≠ remainder)
    (hTogether : (data.vertexPartition wall).Rel extra remainder)
    (hCompatible : GlobalResolution.OldCompatible data wall right
      (ResolutionP.residualResolution (data.vertexPartition wall) extra remainder hne
        hTogether)) :
    genus (GlobalResolution.datum data wall right
        (ResolutionP.residualResolution (data.vertexPartition wall) extra remainder hne
          hTogether) hCompatible).sourceGraph =
      genus data.sourceGraph + 1 := by
  have := W3ShiftShrinkExistence.sourceGenus_datum_eq_add data wall right _ hCompatible 1
    (residualResolution_card_blocks (data.vertexPartition wall) extra remainder hne
      hTogether)
  simpa using this

/-- **The genus-preserving shape has defect zero**, for any `fine`: the `t₂` endpoint
and the new edge are the same partition, so the identity is an identity. -/
theorem leftSplitResolution_card_blocks (wallPartition fine : SheetPartition d)
    (hRefines : fine.Refines wallPartition) :
    Fintype.card (leftSplitResolution wallPartition fine hRefines).newEdge.Blocks +
        Fintype.card wallPartition.Blocks =
      Fintype.card (leftSplitResolution wallPartition fine hRefines).left.Blocks +
        Fintype.card (leftSplitResolution wallPartition fine hRefines).right.Blocks :=
  rfl

/-- The companion positive statement: a candidate assembled from the Figure 35
shape preserves the source genus. -/
theorem leftSplitResolution_sourceGenus_eq
    (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (fine : SheetPartition degree)
    (hRefines : fine.Refines (data.vertexPartition wall))
    (hCompatible : GlobalResolution.OldCompatible data wall right
      (leftSplitResolution (data.vertexPartition wall) fine hRefines)) :
    genus (GlobalResolution.datum data wall right
        (leftSplitResolution (data.vertexPartition wall) fine hRefines)
        hCompatible).sourceGraph =
      genus data.sourceGraph := by
  have hCard := leftSplitResolution_card_blocks (data.vertexPartition wall) fine hRefines
  have := W3ShiftShrinkExistence.sourceGenus_datum_eq_add data wall right _ hCompatible 0
    (by simpa using hCard)
  simpa using this

/-! ## The literal `w2P` source shape -/

/-- The actual case-P refinement of a `w2-r2-nd3` source profile: the dangling
occurrence `e₄` lies above `t₂`, the direction that already carries two
survivors (case `{w2-r2-nd3-P}`).  **That single field is the whole case hypothesis.**
Unlike Cardinality M, no index is bounded below: Base II.2.1.P and II.2.2.P ask
nothing of `k₁`, `k₂`, which is why Figure 35 has no `k = 1` sub-case. -/
structure Shape {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block) where
  /-- Cardinality P: the dangling occurrence `e₄` lies above `t₂`. -/
  deleted_double : profile.deleted.edge.1.1.1 = star.edge profile.doubleLabel

namespace Shape

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- Cardinality P, read off the profile's own case disjunction:
`k₁ + k₂ + 1 = |A₀|` and `k₃ = |A₀|` (case `{w2-r2-nd3}`). -/
theorem cardinality (shape : Shape profile) :
    data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 + 1 =
        (data.vertexPartition wall).blockCard block.1 ∧
      data.sourceEdgeIndex profile.third.1 =
        (data.vertexPartition wall).blockCard block.1 := by
  rcases profile.cases with ⟨hSingle, _, _⟩ | ⟨_, hPair, hThird⟩
  · exact absurd (star.edge_injective (shape.deleted_double.symm.trans hSingle))
      profile.labels_ne
  · exact ⟨hPair, hThird⟩

/-- `|A₀| = k₁ + k₂ + 1`. -/
theorem blockCard (shape : Shape profile) :
    (data.vertexPartition wall).blockCard block.1 =
      data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 + 1 :=
  shape.cardinality.1.symm

/-- **`k₃ = k₁ + k₂ + 1`.**  This is the identity the limit box
`c(e₃)/(k₁+k₂+1) + s = 0` of Figure 35 displays, derived from the profile rather
than read off the figure. -/
theorem third_index (shape : Shape profile) :
    data.sourceEdgeIndex profile.third.1 =
      data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 + 1 := by
  have := shape.cardinality
  omega

/-- `k₁ + k₂ + k₃ + 1 = 2|A₀|`, the index sum of case `{w2-r2-nd3}`
with `k₄ = 1`. -/
theorem index_sum (shape : Shape profile) :
    data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 +
        data.sourceEdgeIndex profile.third.1 + 1 =
      2 * (data.vertexPartition wall).blockCard block.1 := by
  have := shape.cardinality
  omega

/-- `3 ≤ k₃`. -/
theorem three_le_third (shape : Shape profile) :
    3 ≤ data.sourceEdgeIndex profile.third.1 := by
  have hIndex := shape.third_index
  have h₁ := sourceEdgeIndex_pos data profile.first.1
  have h₂ := sourceEdgeIndex_pos data profile.second.1
  omega

/-- **The direction split is three-and-one.**  `e₁`, `e₂` and the dangling `e₄`
lie above `t₂`, and only `e₃` above `t₃`.  Base I requires two occurrences above
each direction ("here the two edges of `N(A₀)` are above `t₂`, and the other two
above `t₃`", Part I, case `{w2-r2}`), so this is why **Base I is precluded** in
case `{w2-r2-nd3-P}`. -/
theorem directions (shape : Shape profile) :
    profile.first.1.1.1 = star.edge profile.doubleLabel ∧
      profile.second.1.1.1 = star.edge profile.doubleLabel ∧
        profile.deleted.edge.1.1.1 = star.edge profile.doubleLabel ∧
          profile.third.1.1.1 = star.edge profile.singleLabel :=
  ⟨profile.first_target, profile.second_target, shape.deleted_double, profile.third_target⟩

/-- **Base I is precluded, in the source's own index equations** (case `{w2-r2}`).
Base I.a needs `k₂ = k₃`; Base I.b needs `k₃ = k₁` or `k₃ = k₄`.  All three fail
because `k₃ = k₁ + k₂ + 1` and `k₄ = 1`. -/
theorem base_one_precluded (shape : Shape profile) :
    data.sourceEdgeIndex profile.second.1 ≠ data.sourceEdgeIndex profile.third.1 ∧
      data.sourceEdgeIndex profile.third.1 ≠ data.sourceEdgeIndex profile.first.1 ∧
        data.sourceEdgeIndex profile.third.1 ≠
          data.sourceEdgeIndex profile.deleted.edge.1 := by
  have hIndex := shape.third_index
  have h₁ := sourceEdgeIndex_pos data profile.first.1
  have h₂ := sourceEdgeIndex_pos data profile.second.1
  rw [profile.deleted.index_one]
  omega

end Shape

/-! ## The three occurrences above `t₂` and their sheets -/

section Sheets

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- **Figure 35's `t₂` endpoint partition is not a choice.**  It is the `t₂`
direction's own occurrence partition, whose three blocks inside `A₀` are `e₁`,
`e₂` and the dangling singleton `e₄`. -/
abbrev endpointPartition (profile : W2R2SourceProfile.SourceProfile data star block) :
    SheetPartition degree :=
  data.edgePartition (star.edge profile.doubleLabel)

theorem endpointPartition_refines
    (profile : W2R2SourceProfile.SourceProfile data star block) :
    (endpointPartition profile).Refines (data.vertexPartition wall) :=
  star.edgePartition_refines_wall data profile.doubleLabel

/-- The canonical sheet of `e₁`. -/
def firstSheet (profile : W2R2SourceProfile.SourceProfile data star block) :
    Fin degree := profile.first.1.1.2

/-- The canonical sheet of `e₂`. -/
def secondSheet (profile : W2R2SourceProfile.SourceProfile data star block) :
    Fin degree := profile.second.1.1.2

/-- **The dangling sheet**: the unique sheet of the dangling occurrence `e₄`.
In Cardinality P it lies above `t₂`, alongside `e₁` and `e₂`. -/
def extraSheet (profile : W2R2SourceProfile.SourceProfile data star block) :
    Fin degree := profile.deleted.edge.1.1.2

theorem sheet_rel_of_incident
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)) :
    (data.vertexPartition wall).Rel block.1 edge.1.1.2 := by
  have hIncident := (incident_wallBlock_sourceVertex_iff data block edge.1).mp edge.2
  exact (WallBlock.ofSheet_eq_iff_rel data wall block edge.1.1.2).mp hIncident.2

theorem firstSheet_rel (profile : W2R2SourceProfile.SourceProfile data star block) :
    (data.vertexPartition wall).Rel block.1 (firstSheet profile) :=
  sheet_rel_of_incident profile.first

theorem secondSheet_rel (profile : W2R2SourceProfile.SourceProfile data star block) :
    (data.vertexPartition wall).Rel block.1 (secondSheet profile) :=
  sheet_rel_of_incident profile.second

theorem extraSheet_rel (profile : W2R2SourceProfile.SourceProfile data star block) :
    (data.vertexPartition wall).Rel block.1 (extraSheet profile) :=
  sheet_rel_of_incident profile.deleted.edge

/-- **Distinct occurrences above `t₂` sit in distinct blocks of the `t₂`
occurrence partition.**  The one separation lemma all three of Figure 35's
members consume. -/
theorem separate_of_ne
    (edge other : IncidentSourceEdge data (WallBlock.sourceVertex data wall block))
    (hEdge : edge.1.1.1 = star.edge profile.doubleLabel)
    (hOther : other.1.1.1 = star.edge profile.doubleLabel) (hNe : edge ≠ other) :
    ¬(endpointPartition profile).Rel edge.1.1.2 other.1.1.2 := by
  intro hRel
  apply hNe
  have hEdgeRepr : (endpointPartition profile).repr edge.1.1.2 = edge.1.1.2 := by
    have h := edge.1.2
    rw [hEdge] at h
    exact h
  have hOtherRepr : (endpointPartition profile).repr other.1.1.2 = other.1.1.2 := by
    have h := other.1.2
    rw [hOther] at h
    exact h
  have hSheet : edge.1.1.2 = other.1.1.2 := by
    have h := hRel
    rw [SheetPartition.rel_iff, hEdgeRepr, hOtherRepr] at h
    exact h
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (hEdge.trans hOther.symm) hSheet

theorem first_ne_deleted (profile : W2R2SourceProfile.SourceProfile data star block) :
    profile.first ≠ profile.deleted.edge := by
  intro h
  exact profile.first_survives (by rw [h]; exact profile.deleted.dangling)

theorem second_ne_deleted (profile : W2R2SourceProfile.SourceProfile data star block) :
    profile.second ≠ profile.deleted.edge := by
  intro h
  exact profile.second_survives (by rw [h]; exact profile.deleted.dangling)

theorem first_second_separate
    (profile : W2R2SourceProfile.SourceProfile data star block) :
    ¬(endpointPartition profile).Rel (firstSheet profile) (secondSheet profile) :=
  separate_of_ne profile.first profile.second profile.first_target profile.second_target
    profile.first_ne_second

theorem first_extra_separate (shape : Shape profile) :
    ¬(endpointPartition profile).Rel (firstSheet profile) (extraSheet profile) :=
  separate_of_ne profile.first profile.deleted.edge profile.first_target
    shape.deleted_double (first_ne_deleted profile)

theorem second_extra_separate (shape : Shape profile) :
    ¬(endpointPartition profile).Rel (secondSheet profile) (extraSheet profile) :=
  separate_of_ne profile.second profile.deleted.edge profile.second_target
    shape.deleted_double (second_ne_deleted profile)

/-- `|e₁| = k₁`. -/
theorem endpointPartition_blockCard_first
    (profile : W2R2SourceProfile.SourceProfile data star block) :
    (endpointPartition profile).blockCard (firstSheet profile) =
      data.sourceEdgeIndex profile.first.1 := by
  show (data.edgePartition (star.edge profile.doubleLabel)).blockCard profile.first.1.1.2 =
    (data.edgePartition profile.first.1.1.1).blockCard profile.first.1.1.2
  rw [profile.first_target]

/-- `|e₂| = k₂`. -/
theorem endpointPartition_blockCard_second
    (profile : W2R2SourceProfile.SourceProfile data star block) :
    (endpointPartition profile).blockCard (secondSheet profile) =
      data.sourceEdgeIndex profile.second.1 := by
  show (data.edgePartition (star.edge profile.doubleLabel)).blockCard profile.second.1.1.2 =
    (data.edgePartition profile.second.1.1.1).blockCard profile.second.1.1.2
  rw [profile.second_target]

/-- `|e₄| = 1`. -/
theorem extraSheet_blockCard (shape : Shape profile) :
    (endpointPartition profile).blockCard (extraSheet profile) = 1 := by
  have hIndex : data.sourceEdgeIndex profile.deleted.edge.1 =
      (data.edgePartition profile.deleted.edge.1.1.1).blockCard (extraSheet profile) := rfl
  rw [shape.deleted_double, profile.deleted.index_one] at hIndex
  exact hIndex.symm

/-- **The dangling sheet is isolated by the `t₂` occurrence partition.**  This
is `GlobalP.Geometry.extraSingleton`, and it is what makes the genus-preserving
third member's exterior condition satisfiable. -/
theorem extraSheet_block (shape : Shape profile) :
    (endpointPartition profile).block (extraSheet profile) = {extraSheet profile} :=
  SheetPartition.block_eq_singleton_of_blockCard_eq_one _ _ (extraSheet_blockCard shape)

/-- **`e₁`, `e₂` and `e₄` tile `A₀`.**  Cardinality P puts the dangling
occurrence above `t₂`, so the three of them are the whole `t₂` fibre of the
block. -/
theorem endpointPartition_covers (shape : Shape profile) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    (endpointPartition profile).Rel (firstSheet profile) sheet ∨
      (endpointPartition profile).Rel (secondSheet profile) sheet ∨
        (endpointPartition profile).Rel (extraSheet profile) sheet := by
  have hIncident : Incident data (data.sourceEdge (star.edge profile.doubleLabel) sheet)
      (WallBlock.sourceVertex data wall block) := by
    apply (incident_wallBlock_sourceVertex_iff data block _).mpr
    refine ⟨star.edge_mem_incidentEdges profile.doubleLabel, ?_⟩
    apply (WallBlock.ofSheet_eq_iff_rel data wall block _).mpr
    exact hSheet.trans ((star.edgePartition_refines_wall data profile.doubleLabel).rel
      ((data.edgePartition (star.edge profile.doubleLabel)).rel_repr_right sheet))
  have hReprFirst : (endpointPartition profile).repr (firstSheet profile) =
      firstSheet profile := by
    have h := profile.first.1.2
    rw [profile.first_target] at h
    exact h
  have hReprSecond : (endpointPartition profile).repr (secondSheet profile) =
      secondSheet profile := by
    have h := profile.second.1.2
    rw [profile.second_target] at h
    exact h
  have hReprExtra : (endpointPartition profile).repr (extraSheet profile) =
      extraSheet profile := by
    have h := profile.deleted.edge.1.2
    rw [shape.deleted_double] at h
    exact h
  rcases profile.exhaustive ⟨_, hIncident⟩ with hEq | hEq | hEq | hEq
  · left
    have hRepr := congrArg (fun edge ↦ edge.1.1.2) hEq
    change (endpointPartition profile).repr sheet = firstSheet profile at hRepr
    rw [SheetPartition.rel_iff, hReprFirst, hRepr]
  · right; left
    have hRepr := congrArg (fun edge ↦ edge.1.1.2) hEq
    change (endpointPartition profile).repr sheet = secondSheet profile at hRepr
    rw [SheetPartition.rel_iff, hReprSecond, hRepr]
  · exact absurd ((congrArg (fun edge ↦ edge.1.1.1) hEq).trans profile.third_target)
      (star.edge_injective.ne profile.labels_ne)
  · right; right
    have hRepr := congrArg (fun edge ↦ edge.1.1.2) hEq
    change (endpointPartition profile).repr sheet = extraSheet profile at hRepr
    rw [SheetPartition.rel_iff, hReprExtra, hRepr]

/-- The dangling sheet is not the canonical sheet of `e₁`. -/
theorem extra_ne_first (shape : Shape profile) :
    extraSheet profile ≠ firstSheet profile := by
  intro h
  exact first_extra_separate shape (by rw [h]; rfl)

/-- The dangling sheet is not the canonical sheet of `e₂`. -/
theorem extra_ne_second (shape : Shape profile) :
    extraSheet profile ≠ secondSheet profile := by
  intro h
  exact second_extra_separate shape (by rw [h]; rfl)

theorem wall_extra_first (profile : W2R2SourceProfile.SourceProfile data star block) :
    (data.vertexPartition wall).Rel (extraSheet profile) (firstSheet profile) :=
  (extraSheet_rel profile).symm.trans (firstSheet_rel profile)

/-- **A two-block induced count.**  A partition whose blocks inside one wall
block are exactly the blocks of two named sheets contributes exactly two induced
blocks there. -/
theorem blockCountWithin_eq_two (fine wallPartition : SheetPartition d)
    (a b anchor : Fin d) (hA : wallPartition.Rel anchor a) (hB : wallPartition.Rel anchor b)
    (hCovers : ∀ sheet, wallPartition.Rel anchor sheet → fine.Rel a sheet ∨ fine.Rel b sheet)
    (hSeparate : ¬fine.Rel a b) :
    fine.blockCountWithin wallPartition anchor = 2 := by
  classical
  have hImage : (wallPartition.block anchor).image fine.repr = {fine.repr a, fine.repr b} := by
    ext value
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton,
      SheetPartition.mem_block_iff]
    constructor
    · rintro ⟨source, hSource, rfl⟩
      rcases hCovers source hSource with hRel | hRel
      · exact Or.inl (by rw [SheetPartition.rel_iff] at hRel; exact hRel.symm)
      · exact Or.inr (by rw [SheetPartition.rel_iff] at hRel; exact hRel.symm)
    · rintro (rfl | rfl)
      · exact ⟨a, hA, rfl⟩
      · exact ⟨b, hB, rfl⟩
  unfold SheetPartition.blockCountWithin
  rw [hImage, Finset.card_insert_of_notMem (by simpa using hSeparate),
    Finset.card_singleton]

end Sheets

/-! ## The common gluing geometry

**One gluing datum for all three members.**  One `GlobalP.Geometry` carries all
three Figure 35 members, and every field of it is read off the profile: the
endpoint partition is the `t₂`
occurrence partition, the three sheets are the canonical sheets of `e₁`, `e₂`
and the dangling `e₄`, and `k₁`, `k₂`, `|A₀| = k₁+k₂+1` are the profile's own
indices. -/

section Geometry

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- The actual `GlobalP.Geometry` of a case-P source profile. -/
def geometry (shape : Shape profile) : GlobalP.Geometry data wall where
  endpoint := endpointPartition profile
  first := firstSheet profile
  second := secondSheet profile
  extra := extraSheet profile
  endpoint_refines := endpointPartition_refines profile
  first_second := first_second_separate profile
  first_extra := first_extra_separate shape
  second_extra := second_extra_separate shape
  wall_first_second := (firstSheet_rel profile).symm.trans (secondSheet_rel profile)
  wall_first_extra := (firstSheet_rel profile).symm.trans (extraSheet_rel profile)
  extraSingleton := extraSheet_block shape
  k₁ := data.sourceEdgeIndex profile.first.1
  k₂ := data.sourceEdgeIndex profile.second.1
  k₁_pos := sourceEdgeIndex_pos data profile.first.1
  k₂_pos := sourceEdgeIndex_pos data profile.second.1
  firstCard := endpointPartition_blockCard_first profile
  secondCard := endpointPartition_blockCard_second profile
  wallCard := by
    rw [SheetPartition.blockCard_congr (data.vertexPartition wall)
      (firstSheet_rel profile).symm]
    exact shape.blockCard

@[simp] theorem geometry_endpoint (shape : Shape profile) :
    (geometry shape).endpoint = endpointPartition profile := rfl

@[simp] theorem geometry_first (shape : Shape profile) :
    (geometry shape).first = firstSheet profile := rfl

@[simp] theorem geometry_second (shape : Shape profile) :
    (geometry shape).second = secondSheet profile := rfl

@[simp] theorem geometry_extra (shape : Shape profile) :
    (geometry shape).extra = extraSheet profile := rfl

@[simp] theorem geometry_k₁ (shape : Shape profile) :
    (geometry shape).k₁ = data.sourceEdgeIndex profile.first.1 := rfl

@[simp] theorem geometry_k₂ (shape : Shape profile) :
    (geometry shape).k₂ = data.sourceEdgeIndex profile.second.1 := rfl

/-- `GlobalP.Geometry` is inhabited at an actual case-P source profile. -/
theorem exists_geometry (shape : Shape profile) : Nonempty (GlobalP.Geometry data wall) :=
  ⟨geometry shape⟩

/-! ### `M⁽³⁾`, on the genus-preserving shape

The Base II.1.P partition above `u`: `A⁽ᵠ⁾ = e₁ ∪ e₂` of `k₁ + k₂` sheets,
together with the dangling singleton `{x}`. -/

/-- The `t₂`-side partition of Figure 35's `M⁽³⁾`: the wall block with the
dangling sheet detached. -/
abbrev thirdFine (shape : Shape profile) : SheetPartition degree :=
  (data.vertexPartition wall).detachSheet (extraSheet profile) (firstSheet profile)
    (extra_ne_first shape) (wall_extra_first profile)

theorem thirdFine_refines (shape : Shape profile) :
    (thirdFine shape).Refines (data.vertexPartition wall) :=
  (data.vertexPartition wall).detachSheet_refines _ _ _ _

/-- **Figure 35's `M⁽³⁾` (Base II.1.P), on the shape the figure calls for.**
The `t₂` endpoint splits off the dangling sheet, the `t₃` endpoint keeps the
whole block `A' = A₀`, and the new edge agrees with the `t₂` endpoint. -/
def thirdLocal (shape : Shape profile) : LocalResolution degree :=
  leftSplitResolution (data.vertexPartition wall) (thirdFine shape) (thirdFine_refines shape)

theorem thirdLocal_contracts (shape : Shape profile) :
    (thirdLocal shape).ContractsTo (data.vertexPartition wall) :=
  leftSplitResolution_contracts _ _ _

/-- **The change is one field wide.**  The new edge of the genus-preserving `M⁽³⁾` is
literally `GlobalP`'s: only the `t₂` endpoint moves, from `A₀` to `A₀ ∖ {x}`. -/
theorem thirdLocal_newEdge_eq (shape : Shape profile) :
    (thirdLocal shape).newEdge = ((geometry shape).thirdLocal).newEdge := rfl

theorem thirdLocal_right_eq (shape : Shape profile) :
    (thirdLocal shape).right = ((geometry shape).thirdLocal).right := rfl

/-- ... and the left endpoint is exactly what changes. -/
theorem thirdLocal_left (shape : Shape profile) :
    (thirdLocal shape).left = thirdFine shape ∧
      ((geometry shape).thirdLocal).left = data.vertexPartition wall :=
  ⟨rfl, rfl⟩

end Geometry

/-! ## The three members as actual gluing data -/

section Members

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- Relabel a two-star so that label `0` names a chosen direction.  A local copy
of `W2MkkSourceCandidates.orientStar`; that file is not imported here. -/
def orientStar (star : TwoStar target wall) (label : Fin 2) : TwoStar target wall :=
  ⟨(Equiv.swap 0 label).trans star.label⟩

theorem orientStar_edge (star : TwoStar target wall) (label other : Fin 2) :
    (orientStar star label).edge other = star.edge (Equiv.swap 0 label other) := rfl

/-- The two-star with `t₂` on label `0` (the retained side) and `t₃` on label
`1` (the fresh side). -/
def orientedStar (profile : W2R2SourceProfile.SourceProfile data star block) :
    TwoStar target wall := orientStar star profile.doubleLabel

theorem orientedStar_edge_zero
    (profile : W2R2SourceProfile.SourceProfile data star block) :
    (orientedStar profile).edge 0 = star.edge profile.doubleLabel := by
  rw [orientedStar, orientStar_edge, Equiv.swap_apply_left]

theorem orientedStar_edge_one
    (profile : W2R2SourceProfile.SourceProfile data star block) :
    (orientedStar profile).edge 1 = star.edge profile.singleLabel := by
  have hSwap : ∀ a b : Fin 2, a ≠ b → Equiv.swap (0 : Fin 2) a 1 = b := by decide
  rw [orientedStar, orientStar_edge, hSwap _ _ profile.labels_ne]

theorem exists_label (twoStar : TwoStar target wall) (edge : target.edges)
    (hAt : edge ∈ GluingDatum.incidentEdges wall) : ∃ label, twoStar.edge label = edge :=
  ⟨twoStar.label.symm ⟨edge, hAt⟩,
    congrArg Subtype.val (twoStar.label.apply_symm_apply ⟨edge, hAt⟩)⟩

theorem joinedBackground_right (twoStar : TwoStar target wall)
    (distinguished : Fin degree) (edge : target.edges) :
    (M11SourceCandidates.joinedBackground data twoStar distinguished).right edge =
      twoStar.right edge := rfl

/-- **One occurrence pattern for all three Figure 35 members.**  The only input
that varies is the `t₂` refinement `hLeft`; the `t₃` condition is the same for
every member because every member keeps the whole wall block there.  This is
the shared datum in constructive form: nothing here pins a sheet and nothing
opposes anything, so the three members live over one `data`. -/
noncomputable def pattern (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished : Fin degree) (fine : SheetPartition degree)
    (hRefines : fine.Refines (data.vertexPartition wall))
    (hLeft : (endpointPartition profile).Refines fine) :
    GlobalMkk.DivalentPattern (data := data) (wall := wall) distinguished
      (leftSplitResolution (data.vertexPartition wall) fine hRefines) where
  background := M11SourceCandidates.joinedBackground data (orientedStar profile) distinguished
  leftExternal := (orientedStar profile).edge 0
  rightExternal := (orientedStar profile).edge 1
  leftEdges := rfl
  rightEdges := rfl
  exterior := by
    intro edge hAt
    obtain ⟨label, rfl⟩ := exists_label (orientedStar profile) edge (by
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] using hAt)
    have hLabel : label = 0 ∨ label = 1 := by omega
    rcases hLabel with rfl | rfl
    · have hFalse : (M11SourceCandidates.joinedBackground data (orientedStar profile)
          distinguished).right ((orientedStar profile).edge 0) = false := by
        rw [joinedBackground_right]
        exact TwoStar.right_edge_zero _
      rw [ite_eq_right (by rw [hFalse]; simp)]
      show (data.edgePartition ((orientedStar profile).edge 0)).Refines fine
      rw [orientedStar_edge_zero]
      exact hLeft
    · have hTrue : (M11SourceCandidates.joinedBackground data (orientedStar profile)
          distinguished).right ((orientedStar profile).edge 1) = true := by
        rw [joinedBackground_right]
        exact TwoStar.right_edge_one _
      rw [ite_eq_left hTrue]
      show (data.edgePartition ((orientedStar profile).edge 1)).Refines
        (data.vertexPartition wall)
      rw [orientedStar_edge_one]
      exact star.edgePartition_refines_wall data profile.singleLabel

/-- Figure 35's `M⁽¹⁾`, Base II.2.1.P: the dangling sheet joins `e₁`. -/
noncomputable def firstPattern (shape : Shape profile) :
    GlobalMkk.DivalentPattern (data := data) (wall := wall)
      (geometry shape).first (geometry shape).firstLocal :=
  pattern profile (firstSheet profile)
    ((endpointPartition profile).mergeBlocks (firstSheet profile) (extraSheet profile)
      (first_extra_separate shape))
    ((endpointPartition profile).mergeBlocks_refines_coarse (data.vertexPartition wall)
      (firstSheet profile) (extraSheet profile) (first_extra_separate shape)
      (endpointPartition_refines profile)
      ((firstSheet_rel profile).symm.trans (extraSheet_rel profile)))
    (SheetPartition.refines_mergeBlocks _ _ _ _)

/-- Figure 35's `M⁽²⁾`, Base II.2.2.P: the dangling sheet joins `e₂`. -/
noncomputable def secondPattern (shape : Shape profile) :
    GlobalMkk.DivalentPattern (data := data) (wall := wall)
      (geometry shape).first (geometry shape).secondLocal :=
  pattern profile (firstSheet profile)
    ((endpointPartition profile).mergeBlocks (secondSheet profile) (extraSheet profile)
      (second_extra_separate shape))
    ((endpointPartition profile).mergeBlocks_refines_coarse (data.vertexPartition wall)
      (secondSheet profile) (extraSheet profile) (second_extra_separate shape)
      (endpointPartition_refines profile)
      ((secondSheet_rel profile).symm.trans (extraSheet_rel profile)))
    (SheetPartition.refines_mergeBlocks _ _ _ _)

/-- Figure 35's `M⁽³⁾` on the genus-preserving shape: the dangling sheet detaches from
the `t₂` endpoint and from the new edge, `|e'| = |A⁽³⁾| = k₁ + k₂`. -/
noncomputable def thirdPattern (shape : Shape profile) :
    GlobalMkk.DivalentPattern (data := data) (wall := wall)
      (geometry shape).first (thirdLocal shape) :=
  pattern profile (firstSheet profile) (thirdFine shape) (thirdFine_refines shape)
    (SheetPartition.refines_detachSheet_of_block_singleton _ (data.vertexPartition wall)
      (extraSheet profile) (firstSheet profile) (extra_ne_first shape)
      (wall_extra_first profile) (endpointPartition_refines profile)
      (extraSheet_block shape))

/-- Figure 35's `M⁽³⁾` on `GlobalP`'s literal, genus-raising shape.  Its
exterior condition is vacuous on **both** sides, since both endpoints are the
whole wall partition. -/
noncomputable def literalThirdPattern (shape : Shape profile) :
    GlobalMkk.DivalentPattern (data := data) (wall := wall)
      (geometry shape).first (geometry shape).thirdLocal where
  background := M11SourceCandidates.joinedBackground data (orientedStar profile)
    (firstSheet profile)
  leftExternal := (orientedStar profile).edge 0
  rightExternal := (orientedStar profile).edge 1
  leftEdges := rfl
  rightEdges := rfl
  exterior := by
    intro edge hAt
    have hRefines := refines_of_mem_incidentEdges data (by
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] using hAt)
    by_cases hSide : (M11SourceCandidates.joinedBackground data (orientedStar profile)
        (firstSheet profile)).right edge
    · rw [ite_eq_left hSide]
      exact hRefines
    · rw [ite_eq_right hSide]
      exact hRefines

/-! ### The local partitions of the three members, named -/

theorem firstLocal_left (shape : Shape profile) :
    (geometry shape).firstLocal.left =
      (endpointPartition profile).mergeBlocks (firstSheet profile) (extraSheet profile)
        (first_extra_separate shape) := rfl

theorem firstLocal_newEdge (shape : Shape profile) :
    (geometry shape).firstLocal.newEdge =
      (endpointPartition profile).mergeBlocks (firstSheet profile) (extraSheet profile)
        (first_extra_separate shape) := rfl

theorem firstLocal_right (shape : Shape profile) :
    (geometry shape).firstLocal.right = data.vertexPartition wall := rfl

theorem secondLocal_left (shape : Shape profile) :
    (geometry shape).secondLocal.left =
      (endpointPartition profile).mergeBlocks (secondSheet profile) (extraSheet profile)
        (second_extra_separate shape) := rfl

theorem secondLocal_newEdge (shape : Shape profile) :
    (geometry shape).secondLocal.newEdge =
      (endpointPartition profile).mergeBlocks (secondSheet profile) (extraSheet profile)
        (second_extra_separate shape) := rfl

theorem secondLocal_right (shape : Shape profile) :
    (geometry shape).secondLocal.right = data.vertexPartition wall := rfl

/-! ### The shared datum, stated -/

/-- **The three Figure 35 members share one gluing datum.**  Unlike the M-1k and
M-kk cases, `GlobalP.candidates`' three `DivalentPattern`s all exist over one actual case-P
profile, one `data` and one `Geometry`.  Contrast
`W2M1kSourceCandidates.no_common_geometry` and
`W2MkkSourceCandidates.no_common_geometry`. -/
theorem members_share_datum (shape : Shape profile) :
    ∃ geometry : GlobalP.Geometry data wall,
      Nonempty (GlobalMkk.DivalentPattern (data := data) (wall := wall)
        geometry.first geometry.firstLocal) ∧
      Nonempty (GlobalMkk.DivalentPattern (data := data) (wall := wall)
        geometry.first geometry.secondLocal) ∧
      Nonempty (GlobalMkk.DivalentPattern (data := data) (wall := wall)
        geometry.first geometry.thirdLocal) :=
  ⟨geometry shape, ⟨firstPattern shape⟩, ⟨secondPattern shape⟩, ⟨literalThirdPattern shape⟩⟩

/-- **The genus-preserving shape does not empty the bundle.**  The same profile
carries the first two members and the genus-preserving third member.  In the
M-kk case the one-sided bundle was jointly satisfiable only because of its
genus defect, so the genus-preserving shape there needed a swapped datum; here
the condition the genus-preserving shape introduces is already a field of
`GlobalP.Geometry`. -/
theorem repaired_members_share_datum (shape : Shape profile) :
    ∃ geometry : GlobalP.Geometry data wall,
      Nonempty (GlobalMkk.DivalentPattern (data := data) (wall := wall)
        geometry.first geometry.firstLocal) ∧
      Nonempty (GlobalMkk.DivalentPattern (data := data) (wall := wall)
        geometry.first geometry.secondLocal) ∧
      Nonempty (GlobalMkk.DivalentPattern (data := data) (wall := wall)
        geometry.first (thirdLocal shape)) :=
  ⟨geometry shape, ⟨firstPattern shape⟩, ⟨secondPattern shape⟩, ⟨thirdPattern shape⟩⟩

/-- **Why the change is free**, stated against `GlobalP.Geometry`'s own fields
and nothing else: the `t₂` exterior condition of the genus-preserving third member is
`extraSingleton`, which the structure already carries.  Compare
`W2MkkSourceCandidates.detachedResolution_exterior_vacuous`, where the
corresponding condition had to be *added*. -/
theorem repaired_left_exterior (geometry : GlobalP.Geometry data wall) :
    geometry.endpoint.Refines
      ((data.vertexPartition wall).detachSheet geometry.extra geometry.first
        geometry.extra_ne_first geometry.wall_first_extra.symm) :=
  SheetPartition.refines_detachSheet_of_block_singleton geometry.endpoint
    (data.vertexPartition wall) geometry.extra geometry.first geometry.extra_ne_first
    geometry.wall_first_extra.symm geometry.endpoint_refines geometry.extraSingleton

/-- The literal third member's exterior condition is vacuous on **both** sides:
`residualResolution` keeps the whole wall partition at each endpoint. -/
theorem residualResolution_exterior_vacuous (geometry : GlobalP.Geometry data wall)
    (edge : target.edges) (hAt : edge ∈ GluingDatum.incidentEdges wall) :
    (data.edgePartition edge).Refines geometry.thirdLocal.left ∧
      (data.edgePartition edge).Refines geometry.thirdLocal.right :=
  ⟨refines_of_mem_incidentEdges data hAt, refines_of_mem_incidentEdges data hAt⟩

/-! ### The three members as actual outgoing gluing data -/

/-- Figure 35's `M⁽¹⁾` as an actual arbitrary-degree outgoing gluing datum. -/
noncomputable def firstMember (shape : Shape profile) :
    BalancedGlobal.Candidate target degree data wall :=
  (firstPattern shape).candidate (GlobalP.firstLocal_contracts (geometry shape))

/-- Figure 35's `M⁽²⁾`. -/
noncomputable def secondMember (shape : Shape profile) :
    BalancedGlobal.Candidate target degree data wall :=
  (secondPattern shape).candidate (GlobalP.secondLocal_contracts (geometry shape))

/-- Figure 35's `M⁽³⁾`, on the genus-preserving shape. -/
noncomputable def thirdMember (shape : Shape profile) :
    BalancedGlobal.Candidate target degree data wall :=
  (thirdPattern shape).candidate (thirdLocal_contracts shape)

/-- Figure 35's `M⁽³⁾` as `GlobalP` builds it today, on the genus-raising
shape.  Kept so that the defect can be stated about an actual candidate. -/
noncomputable def literalThirdMember (shape : Shape profile) :
    BalancedGlobal.Candidate target degree data wall :=
  (literalThirdPattern shape).candidate (GlobalP.thirdLocal_contracts (geometry shape))

/-! ### Validity -/

theorem firstMember_valid (input : W2SourceInput data star) (shape : Shape profile) :
    (firstMember shape).datum.Valid :=
  (firstMember shape).datum_valid input.valid

theorem secondMember_valid (input : W2SourceInput data star) (shape : Shape profile) :
    (secondMember shape).datum.Valid :=
  (secondMember shape).datum_valid input.valid

theorem thirdMember_valid (input : W2SourceInput data star) (shape : Shape profile) :
    (thirdMember shape).datum.Valid :=
  (thirdMember shape).datum_valid input.valid

/-! ### Source genus -/

/-- `M⁽¹⁾` preserves the complete quotient-source genus: on the distinguished
block the `t₃` endpoint is the whole wall partition and the new edge agrees with
the `t₂` endpoint, and the background is the joined star. -/
theorem firstMember_sourceGenus (shape : Shape profile) :
    genus (firstMember shape).datum.sourceGraph = genus data.sourceGraph := by
  apply M11SourceGenus.candidate_sourceGenus_of_stars
  intro anchor
  have hResolution : (firstMember shape).resolution anchor =
      LocalResolution.onBlock (data.vertexPartition wall) (firstSheet profile)
        ((geometry shape).firstLocal)
        (fun _ ↦ joinedResolutionAt (data.vertexPartition wall)) anchor := rfl
  rw [hResolution]
  by_cases hRel : (data.vertexPartition wall).Rel (firstSheet profile) anchor
  · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hRel]
    exact Or.inr ⟨rfl, rfl⟩
  · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hRel]
    exact Or.inl ⟨rfl, rfl⟩

/-- `M⁽²⁾` preserves the source genus, for the same reason. -/
theorem secondMember_sourceGenus (shape : Shape profile) :
    genus (secondMember shape).datum.sourceGraph = genus data.sourceGraph := by
  apply M11SourceGenus.candidate_sourceGenus_of_stars
  intro anchor
  have hResolution : (secondMember shape).resolution anchor =
      LocalResolution.onBlock (data.vertexPartition wall) (firstSheet profile)
        ((geometry shape).secondLocal)
        (fun _ ↦ joinedResolutionAt (data.vertexPartition wall)) anchor := rfl
  rw [hResolution]
  by_cases hRel : (data.vertexPartition wall).Rel (firstSheet profile) anchor
  · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hRel]
    exact Or.inr ⟨rfl, rfl⟩
  · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hRel]
    exact Or.inl ⟨rfl, rfl⟩

/-- **The genus-preserving `M⁽³⁾` preserves the source genus** -- which the
shape of `GlobalP.Geometry.thirdLocal` does not. -/
theorem thirdMember_sourceGenus (shape : Shape profile) :
    genus (thirdMember shape).datum.sourceGraph = genus data.sourceGraph := by
  apply M11SourceGenus.candidate_sourceGenus_of_stars
  intro anchor
  have hResolution : (thirdMember shape).resolution anchor =
      LocalResolution.onBlock (data.vertexPartition wall) (firstSheet profile)
        (thirdLocal shape)
        (fun _ ↦ joinedResolutionAt (data.vertexPartition wall)) anchor := rfl
  rw [hResolution]
  by_cases hRel : (data.vertexPartition wall).Rel (firstSheet profile) anchor
  · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hRel]
    exact Or.inr ⟨rfl, rfl⟩
  · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hRel]
    exact Or.inl ⟨rfl, rfl⟩

/-! ### Target valencies: both new endpoints are divalent -/

theorem firstMember_target_valencies (shape : Shape profile) :
    (GluingDatum.incidentEdges
      (target := graph target wall (firstMember shape).right)
      (oldVertex target wall)).card = 2 ∧
    (GluingDatum.incidentEdges
      (target := graph target wall (firstMember shape).right)
      (freshVertex target)).card = 2 :=
  M11SourceCandidates.candidate_target_valencies (firstMember shape)

theorem secondMember_target_valencies (shape : Shape profile) :
    (GluingDatum.incidentEdges
      (target := graph target wall (secondMember shape).right)
      (oldVertex target wall)).card = 2 ∧
    (GluingDatum.incidentEdges
      (target := graph target wall (secondMember shape).right)
      (freshVertex target)).card = 2 :=
  M11SourceCandidates.candidate_target_valencies (secondMember shape)

theorem thirdMember_target_valencies (shape : Shape profile) :
    (GluingDatum.incidentEdges
      (target := graph target wall (thirdMember shape).right)
      (oldVertex target wall)).card = 2 ∧
    (GluingDatum.incidentEdges
      (target := graph target wall (thirdMember shape).right)
      (freshVertex target)).card = 2 :=
  M11SourceCandidates.candidate_target_valencies (thirdMember shape)

/-! ### The displayed Figure 35 indices -/

/-- `|A₀| = k₁ + k₂ + 1`, read at any sheet of the block. -/
theorem wall_blockCard_of_rel (shape : Shape profile) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    (data.vertexPartition wall).blockCard sheet =
      data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 + 1 := by
  rw [← SheetPartition.blockCard_congr (data.vertexPartition wall) hSheet]
  exact shape.blockCard

/-- **Figure 35's `t₃` endpoint**, common to all three members: the whole wall
block, `|A'| = |A₀| = k₃`.  Base II.1.P's `|e₃⁽ᵠ⁾| = |A'|` and Base II.2's
`|A⁽ᵠ⁾| = k₃`. -/
theorem right_blockCard (shape : Shape profile) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    (geometry shape).firstLocal.right.blockCard sheet =
        data.sourceEdgeIndex profile.third.1 ∧
      (geometry shape).secondLocal.right.blockCard sheet =
        data.sourceEdgeIndex profile.third.1 ∧
      (thirdLocal shape).right.blockCard sheet = data.sourceEdgeIndex profile.third.1 := by
  have hCard : (data.vertexPartition wall).blockCard sheet =
      data.sourceEdgeIndex profile.third.1 := by
    rw [← SheetPartition.blockCard_congr (data.vertexPartition wall) hSheet]
    exact shape.cardinality.2.symm
  exact ⟨hCard, hCard, hCard⟩

/-- **Figure 35's `M⁽¹⁾` box**: `|e'| = k₁ + 1`, `|e''| = k₂`. -/
theorem firstMember_indices (shape : Shape profile) :
    (geometry shape).firstLocal.newEdge.blockCard (firstSheet profile) =
        data.sourceEdgeIndex profile.first.1 + 1 ∧
      (geometry shape).firstLocal.newEdge.blockCard (secondSheet profile) =
        data.sourceEdgeIndex profile.second.1 := by
  rw [firstLocal_newEdge]
  constructor
  · rw [SheetPartition.mergeBlocks_blockCard_first_of_singleton (endpointPartition profile)
      (firstSheet profile) (extraSheet profile) (first_extra_separate shape)
      (extraSheet_block shape)]
    exact congrArg (· + 1) (endpointPartition_blockCard_first profile)
  · rw [SheetPartition.mergeBlocks_blockCard_of_separate (endpointPartition profile)
      (firstSheet profile) (extraSheet profile) (secondSheet profile)
      (first_extra_separate shape) (fun h ↦ first_second_separate profile h.symm)
      (second_extra_separate shape)]
    exact endpointPartition_blockCard_second profile

/-- **Figure 35's `M⁽²⁾` box**: `|e'| = k₁`, `|e''| = k₂ + 1`. -/
theorem secondMember_indices (shape : Shape profile) :
    (geometry shape).secondLocal.newEdge.blockCard (secondSheet profile) =
        data.sourceEdgeIndex profile.second.1 + 1 ∧
      (geometry shape).secondLocal.newEdge.blockCard (firstSheet profile) =
        data.sourceEdgeIndex profile.first.1 := by
  rw [secondLocal_newEdge]
  constructor
  · rw [SheetPartition.mergeBlocks_blockCard_first_of_singleton (endpointPartition profile)
      (secondSheet profile) (extraSheet profile) (second_extra_separate shape)
      (extraSheet_block shape)]
    exact congrArg (· + 1) (endpointPartition_blockCard_second profile)
  · rw [SheetPartition.mergeBlocks_blockCard_of_separate (endpointPartition profile)
      (secondSheet profile) (extraSheet profile) (firstSheet profile)
      (second_extra_separate shape) (first_second_separate profile)
      (first_extra_separate shape)]
    exact endpointPartition_blockCard_first profile

/-- **Base II.2.1.P: `|e'| = |A'| = k₁ + 1`.**  Part I states Base II.2.1.P as
`|e'| = |A'| + 1`; this statement differs from it as follows.  Case (r1-nd2) of
Part I's local properties offers a vertex only the two edge sizes `|A'|` and
`|A'| - 1`, and an edge class is a subset of its endpoint class, so here the
labelling is `|e₁⁽ᵠ⁾| = |A'| - 1 = k₁` and `|e'| = |A'|`, which with the
refinement `|e₁⁽ᵠ⁾| + |e₄⁽ᵠ⁾| = |A'|` above `t₂` gives `|A'| = k₁ + 1 = |e'|`.
(In the Cardinality M branch of the same statement the dangling occurrence is
above `t₃` and `A'` is not enlarged, so there the two agree.)  The index Part I
derives, `|e'| = k₁ + 1` with `(k₁+1) + k₂ = k₃`, is the same, and it is what
Figure 35 displays.

Nothing gauge-sensitive is at stake: both sides are cardinalities of a single
vertex's own local data, and every relabelling of a gluing datum preserves block
cardinalities.

The identity: the new edge and the `t₂` endpoint carry the same block, of
`k₁ + 1` sheets. -/
theorem firstLocal_newEdge_blockCard_eq_left (shape : Shape profile) :
    (geometry shape).firstLocal.newEdge.blockCard (firstSheet profile) =
        (geometry shape).firstLocal.left.blockCard (firstSheet profile) ∧
      (geometry shape).firstLocal.left.blockCard (firstSheet profile) =
        data.sourceEdgeIndex profile.first.1 + 1 :=
  ⟨rfl, (firstMember_indices shape).1⟩

/-- The mirror statement for Base II.2.2.P: `|e''| = |A''| = k₂ + 1`. -/
theorem secondLocal_newEdge_blockCard_eq_left (shape : Shape profile) :
    (geometry shape).secondLocal.newEdge.blockCard (secondSheet profile) =
        (geometry shape).secondLocal.left.blockCard (secondSheet profile) ∧
      (geometry shape).secondLocal.left.blockCard (secondSheet profile) =
        data.sourceEdgeIndex profile.second.1 + 1 :=
  ⟨rfl, (secondMember_indices shape).1⟩

/-- **Figure 35's `M⁽³⁾` box**: `|e'| = k₁ + k₂`, read at either
surviving sheet, with the unlisted dangling singleton isolated. -/
theorem thirdMember_indices (shape : Shape profile) :
    (thirdLocal shape).newEdge.blockCard (firstSheet profile) =
        data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 ∧
      (thirdLocal shape).newEdge.blockCard (secondSheet profile) =
        data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 ∧
      (thirdLocal shape).newEdge.blockCard (extraSheet profile) = 1 := by
  have hExtraCard : (data.vertexPartition wall).blockCard (extraSheet profile) =
      data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 + 1 :=
    wall_blockCard_of_rel shape (extraSheet profile) (extraSheet_rel profile)
  have hFirst : (thirdLocal shape).newEdge.blockCard (firstSheet profile) =
      data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 := by
    show (thirdFine shape).blockCard (firstSheet profile) = _
    rw [(data.vertexPartition wall).detachSheet_blockCard_remainder (extraSheet profile)
      (firstSheet profile) (extra_ne_first shape) (wall_extra_first profile), hExtraCard]
    omega
  refine ⟨hFirst, ?_, ?_⟩
  · have hRel := W3ShiftSourceCandidates.detachSheet_rel_remainder
      (data.vertexPartition wall) (extraSheet profile) (firstSheet profile)
      (secondSheet profile) (extra_ne_first shape) (wall_extra_first profile)
      ((extraSheet_rel profile).symm.trans (secondSheet_rel profile))
      (Ne.symm (extra_ne_second shape))
    show (thirdFine shape).blockCard (secondSheet profile) = _
    rw [SheetPartition.blockCard_congr (thirdFine shape) hRel]
    exact hFirst
  · show (thirdFine shape).blockCard (extraSheet profile) = 1
    exact (data.vertexPartition wall).detachSheet_blockCard_single _ _ _ _

/-! ### The induced block counts on `A₀` -/

/-- **`M⁽¹⁾`'s induced counts: two, two, one.**  Two blocks at the `t₂`
endpoint (`e₁ ∪ e₄` and `e₂`), the same two along the new edge, one at the `t₃`
endpoint.  The blockwise Euler identity `2 + 1 = 2 + 1` is what
`firstMember_sourceGenus` consumes. -/
theorem firstMember_blockCountWithin (shape : Shape profile) (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    (geometry shape).firstLocal.left.blockCountWithin (data.vertexPartition wall) anchor = 2 ∧
      (geometry shape).firstLocal.newEdge.blockCountWithin
        (data.vertexPartition wall) anchor = 2 ∧
      (geometry shape).firstLocal.right.blockCountWithin
        (data.vertexPartition wall) anchor = 1 := by
  have hCount : ((endpointPartition profile).mergeBlocks (firstSheet profile)
      (extraSheet profile) (first_extra_separate shape)).blockCountWithin
        (data.vertexPartition wall) anchor = 2 := by
    refine blockCountWithin_eq_two _ _ (firstSheet profile) (secondSheet profile) anchor
      (hAnchor.symm.trans (firstSheet_rel profile))
      (hAnchor.symm.trans (secondSheet_rel profile)) ?_ ?_
    · intro sheet hSheet
      rcases endpointPartition_covers shape sheet (hAnchor.trans hSheet) with h | h | h
      · exact Or.inl (((endpointPartition profile).mergeBlocks_rel_first_iff
          (firstSheet profile) (extraSheet profile) sheet
          (first_extra_separate shape)).mpr (Or.inl h))
      · exact Or.inr ((SheetPartition.refines_mergeBlocks (endpointPartition profile)
          (firstSheet profile) (extraSheet profile) (first_extra_separate shape)).rel h)
      · exact Or.inl (((endpointPartition profile).mergeBlocks_rel_first_iff
          (firstSheet profile) (extraSheet profile) sheet
          (first_extra_separate shape)).mpr (Or.inr h))
    · intro hRel
      rcases ((endpointPartition profile).mergeBlocks_rel_first_iff (firstSheet profile)
        (extraSheet profile) (secondSheet profile) (first_extra_separate shape)).mp hRel with
        h | h
      · exact first_second_separate profile h
      · exact second_extra_separate shape h.symm
  rw [firstLocal_left, firstLocal_newEdge, firstLocal_right]
  exact ⟨hCount, hCount, SheetPartition.blockCountWithin_self _ _⟩

/-- **`M⁽²⁾`'s induced counts**, the mirror statement. -/
theorem secondMember_blockCountWithin (shape : Shape profile) (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    (geometry shape).secondLocal.left.blockCountWithin
        (data.vertexPartition wall) anchor = 2 ∧
      (geometry shape).secondLocal.newEdge.blockCountWithin
        (data.vertexPartition wall) anchor = 2 ∧
      (geometry shape).secondLocal.right.blockCountWithin
        (data.vertexPartition wall) anchor = 1 := by
  have hCount : ((endpointPartition profile).mergeBlocks (secondSheet profile)
      (extraSheet profile) (second_extra_separate shape)).blockCountWithin
        (data.vertexPartition wall) anchor = 2 := by
    refine blockCountWithin_eq_two _ _ (secondSheet profile) (firstSheet profile) anchor
      (hAnchor.symm.trans (secondSheet_rel profile))
      (hAnchor.symm.trans (firstSheet_rel profile)) ?_ ?_
    · intro sheet hSheet
      rcases endpointPartition_covers shape sheet (hAnchor.trans hSheet) with h | h | h
      · exact Or.inr ((SheetPartition.refines_mergeBlocks (endpointPartition profile)
          (secondSheet profile) (extraSheet profile) (second_extra_separate shape)).rel h)
      · exact Or.inl (((endpointPartition profile).mergeBlocks_rel_first_iff
          (secondSheet profile) (extraSheet profile) sheet
          (second_extra_separate shape)).mpr (Or.inl h))
      · exact Or.inl (((endpointPartition profile).mergeBlocks_rel_first_iff
          (secondSheet profile) (extraSheet profile) sheet
          (second_extra_separate shape)).mpr (Or.inr h))
    · intro hRel
      rcases ((endpointPartition profile).mergeBlocks_rel_first_iff (secondSheet profile)
        (extraSheet profile) (firstSheet profile) (second_extra_separate shape)).mp hRel with
        h | h
      · exact first_second_separate profile h.symm
      · exact first_extra_separate shape h.symm
  rw [secondLocal_left, secondLocal_newEdge, secondLocal_right]
  exact ⟨hCount, hCount, SheetPartition.blockCountWithin_self _ _⟩

/-- **The genus-preserving `M⁽³⁾`'s induced counts: two, two, one.**  Two blocks at the
`t₂` endpoint -- `A⁽³⁾ = e₁ ∪ e₂` and the dangling singleton -- the same two
along the new edge, one at the `t₃` endpoint.  Euler closes: `2 + 1 = 2 + 1`. -/
theorem thirdMember_blockCountWithin (shape : Shape profile) (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    (thirdLocal shape).left.blockCountWithin (data.vertexPartition wall) anchor = 2 ∧
      (thirdLocal shape).newEdge.blockCountWithin (data.vertexPartition wall) anchor = 2 ∧
      (thirdLocal shape).right.blockCountWithin (data.vertexPartition wall) anchor = 1 := by
  have hCount : (thirdFine shape).blockCountWithin (data.vertexPartition wall) anchor = 2 :=
    W3ShiftSourceCandidates.detachSheet_blockCountWithin_self (data.vertexPartition wall)
      (extraSheet profile) (firstSheet profile) anchor (extra_ne_first shape)
      (wall_extra_first profile) ((extraSheet_rel profile).symm.trans hAnchor)
  exact ⟨hCount, hCount, SheetPartition.blockCountWithin_self _ _⟩

/-- **The literal `M⁽³⁾`'s induced counts: one, two, one** -- so its blockwise
Euler identity reads `2 + 1 = 1 + 1` and fails by exactly one on `A₀`.  This is
the genus defect localized: the `t₂` endpoint has one block where Base II.1.P
gives two. -/
theorem literalThirdLocal_blockCountWithin (shape : Shape profile) (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    (geometry shape).thirdLocal.left.blockCountWithin
        (data.vertexPartition wall) anchor = 1 ∧
      (geometry shape).thirdLocal.newEdge.blockCountWithin
        (data.vertexPartition wall) anchor = 2 ∧
      (geometry shape).thirdLocal.right.blockCountWithin
        (data.vertexPartition wall) anchor = 1 := by
  have hCount : (thirdFine shape).blockCountWithin (data.vertexPartition wall) anchor = 2 :=
    W3ShiftSourceCandidates.detachSheet_blockCountWithin_self (data.vertexPartition wall)
      (extraSheet profile) (firstSheet profile) anchor (extra_ne_first shape)
      (wall_extra_first profile) ((extraSheet_rel profile).symm.trans hAnchor)
  exact ⟨SheetPartition.blockCountWithin_self _ _, hCount,
    SheetPartition.blockCountWithin_self _ _⟩

/-! ### The genus defect at the level of an actual candidate

The universal `residualResolution_sourceGenus_eq_succ` above is stated for one
`LocalResolution` on the whole sheet set.  The members built here paste that
shape on `A₀` against a joined background, so the defect has to be summed over
wall blocks before it becomes a genus statement about `literalThirdMember`. -/

/-- **The quantitative form of `M11SourceGenus.paste_block_euler_of_counts`.**
Blockwise Euler defects add up to the pasted one. -/
theorem paste_card_blocks_add (wallPartition : SheetPartition degree)
    (resolution : Fin degree → LocalResolution degree)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wallPartition)
    (defect : Fin degree → ℕ)
    (hEuler : ∀ anchor, wallPartition.repr anchor = anchor →
      (resolution anchor).newEdge.blockCountWithin wallPartition anchor + 1 =
        (resolution anchor).left.blockCountWithin wallPartition anchor +
          (resolution anchor).right.blockCountWithin wallPartition anchor +
          defect anchor) :
    Fintype.card
          (LocalResolution.paste wallPartition resolution hContracts).newEdge.Blocks +
        Fintype.card wallPartition.Blocks =
      Fintype.card
          (LocalResolution.paste wallPartition resolution hContracts).left.Blocks +
        Fintype.card
          (LocalResolution.paste wallPartition resolution hContracts).right.Blocks +
        ∑ block : wallPartition.Blocks, defect block.1 := by
  classical
  have hNewRefines :
      (LocalResolution.paste wallPartition resolution hContracts).newEdge.Refines
        wallPartition :=
    (LocalResolution.pasteNewEdge_refines_left wallPartition resolution hContracts).trans
      (LocalResolution.pasteLeft_refines wallPartition resolution hContracts)
  have hLeftRefines :
      (LocalResolution.paste wallPartition resolution hContracts).left.Refines
        wallPartition :=
    LocalResolution.pasteLeft_refines wallPartition resolution hContracts
  have hRightRefines :
      (LocalResolution.paste wallPartition resolution hContracts).right.Refines
        wallPartition :=
    LocalResolution.pasteRight_refines wallPartition resolution hContracts
  rw [SheetPartition.card_blocks_eq_sum_blockCountWithin _ wallPartition hNewRefines,
    SheetPartition.card_blocks_eq_sum_blockCountWithin _ wallPartition hLeftRefines,
    SheetPartition.card_blocks_eq_sum_blockCountWithin _ wallPartition hRightRefines]
  have hCard : Fintype.card wallPartition.Blocks = ∑ _block : wallPartition.Blocks, 1 := by
    simp
  rw [hCard, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro block _
  rw [LocalResolution.pasteNewEdge_blockCountWithin,
    LocalResolution.pasteLeft_blockCountWithin,
    LocalResolution.pasteRight_blockCountWithin, block.2]
  exact hEuler block.1 block.2

/-- A candidate's source genus exceeds the datum's by exactly its total
blockwise Euler defect. -/
theorem candidate_sourceGenus_add
    (candidate : BalancedGlobal.Candidate target degree data wall)
    (defect : Fin degree → ℕ)
    (hEuler : ∀ anchor, (data.vertexPartition wall).repr anchor = anchor →
      (candidate.resolution anchor).newEdge.blockCountWithin
            (data.vertexPartition wall) anchor + 1 =
        (candidate.resolution anchor).left.blockCountWithin
            (data.vertexPartition wall) anchor +
          (candidate.resolution anchor).right.blockCountWithin
            (data.vertexPartition wall) anchor + defect anchor) :
    genus candidate.datum.sourceGraph = genus data.sourceGraph +
      ((∑ block : (data.vertexPartition wall).Blocks, defect block.1 : ℕ) : ℤ) :=
  W3ShiftShrinkExistence.sourceGenus_datum_eq_add data wall candidate.right
    (LocalResolution.paste (data.vertexPartition wall) candidate.resolution
      candidate.contracts)
    (GlobalAssembly.blockwiseCompatible data wall candidate.right candidate.resolution
      candidate.contracts candidate.exterior) _
    (paste_card_blocks_add (data.vertexPartition wall) candidate.resolution
      candidate.contracts defect hEuler)

/-- A defect supported on the distinguished wall block sums to one. -/
theorem sum_defect_eq_one (wallPartition : SheetPartition degree)
    (distinguished : Fin degree) :
    (∑ block : wallPartition.Blocks,
      (if block.1 = wallPartition.repr distinguished then 1 else 0)) = 1 := by
  have hSum : (∑ block : wallPartition.Blocks,
      (if block.1 = wallPartition.repr distinguished then 1 else 0)) =
        (if (wallPartition.toBlock distinguished).1 = wallPartition.repr distinguished
          then 1 else 0) := by
    refine Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) ?_
    intro other _ hNe
    exact ite_eq_right fun hEq ↦ hNe (Subtype.ext hEq)
  rw [hSum, SheetPartition.toBlock_val]
  exact ite_eq_left rfl

/-- **The genus defect at an actual case-P profile.**  `GlobalP`'s third Figure 35
member, assembled over a real source profile, has source genus **exactly one
greater** than the incoming datum's.  The genus-preserving `thirdMember` has the
same new edge and the same `t₃` endpoint, and preserves the genus. -/
theorem literalThirdMember_sourceGenus_eq_succ (shape : Shape profile) :
    genus (literalThirdMember shape).datum.sourceGraph = genus data.sourceGraph + 1 := by
  have hEuler : ∀ anchor, (data.vertexPartition wall).repr anchor = anchor →
      ((literalThirdMember shape).resolution anchor).newEdge.blockCountWithin
            (data.vertexPartition wall) anchor + 1 =
        ((literalThirdMember shape).resolution anchor).left.blockCountWithin
            (data.vertexPartition wall) anchor +
          ((literalThirdMember shape).resolution anchor).right.blockCountWithin
            (data.vertexPartition wall) anchor +
          (if anchor = (data.vertexPartition wall).repr (firstSheet profile) then 1 else 0) := by
    intro anchor hAnchorFixed
    have hResolution : (literalThirdMember shape).resolution anchor =
        LocalResolution.onBlock (data.vertexPartition wall) (firstSheet profile)
          ((geometry shape).thirdLocal)
          (fun _ ↦ joinedResolutionAt (data.vertexPartition wall)) anchor := rfl
    by_cases hAnchor : anchor = (data.vertexPartition wall).repr (firstSheet profile)
    · have hRel : (data.vertexPartition wall).Rel (firstSheet profile) anchor := by
        rw [SheetPartition.rel_iff, hAnchor, (data.vertexPartition wall).repr_idem]
      have hBlock : (data.vertexPartition wall).Rel block.1 anchor :=
        (firstSheet_rel profile).trans hRel
      obtain ⟨hLeft, hNew, hRight⟩ := literalThirdLocal_blockCountWithin shape anchor hBlock
      rw [hResolution, LocalResolution.onBlock_of_rel _ _ _ _ _ hRel, ite_eq_left hAnchor,
        hLeft, hNew, hRight]
    · have hRel : ¬(data.vertexPartition wall).Rel (firstSheet profile) anchor := by
        intro hRel
        apply hAnchor
        rw [SheetPartition.rel_iff] at hRel
        rw [← hAnchorFixed, ← hRel]
      rw [hResolution, LocalResolution.onBlock_of_not_rel _ _ _ _ _ hRel, ite_eq_right hAnchor]
      show (data.vertexPartition wall).blockCountWithin (data.vertexPartition wall) anchor + 1 =
        (data.vertexPartition wall).blockCountWithin (data.vertexPartition wall) anchor +
          (data.vertexPartition wall).blockCountWithin (data.vertexPartition wall) anchor + 0
      rw [SheetPartition.blockCountWithin_self]
  have hGenus := candidate_sourceGenus_add (literalThirdMember shape) _ hEuler
  rw [sum_defect_eq_one (data.vertexPartition wall) (firstSheet profile)] at hGenus
  simpa using hGenus

end Members

end DraismaVargas.LocalCases.W2PSourceCandidates
