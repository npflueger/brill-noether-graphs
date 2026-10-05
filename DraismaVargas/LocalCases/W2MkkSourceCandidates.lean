module

public import DraismaVargas.LocalCases.GlobalMkk
public import DraismaVargas.LocalCases.M11SourceGenus
public import DraismaVargas.LocalCases.W3ShiftSourceCandidates
public import DraismaVargas.Infrastructure.TargetSeparation

@[expose] public section

/-!
# Source-derived M-kk geometry (Figure 34)

Source: Draisma–Vargas Part I, arXiv:1909.12924, case `{w2-r2-nd3-M-kk}`, Figure 34 and
Equation (8).  The ambient hypotheses are `{w2-r2}` (where the Base I/II
vocabulary is fixed once for the whole `{w2}` section) and `{w2-r2-nd3}` (where
Cardinality M and P are separated).  The case is `k₁ ≥ 2`, `k₂ ≥ 2`; the neighbouring `k₁ = 1`
case is `W2M1kSourceCandidates` and `k₁ = k₂ = 1` is the `M11*` files.

Everything here is derived from an actual `W2R2SourceProfile.SourceProfile`
plus the `Shape` refinement below.  No numerical diagram, no caller-supplied
refinement and no caller-supplied induced count is accepted; in particular the
left endpoint partition is **not** a parameter, it is the `t₂` direction's own
occurrence partition (`endpointPartition`), which is what Base II.2's
`h(e₁⁽ᵠ⁾) = h(e')`, `h(e₂⁽ᵠ⁾) = h(e'')` says, and the detached sheet is not a
parameter either (`transfer_eq_pinSheet`).

## Why the detaching members detach on both sides

Proved elsewhere, and **not** re-derived here: `ResolutionMkk.detachedResolution` raises
the source genus by exactly one, for any arguments
(`W3ShiftShrinkExistence.detachedResolution_sourceGenus_eq_succ`, on
`ResolutionMkk.detachedResolution_card_blocks`), and `GlobalMkk.Geometry`'s
`firstLocal` and `secondLocal` are literally that shape.  The two new
endpoints of Figure 34 being divalent does **not** make the two detachments
cancel: divalence is a statement about the *target* valency of the expanded
wall and says nothing about block counts.  What the source forces is a second
detachment on the other side -- Base II.2 gives `k₃ = |A⁽ᵠ⁾| = |e'| + |e''|`
and Cardinality M gives `k₃ + 1 = |A₀|`, so the `t₃` endpoint block `A⁽ᵠ⁾` is
`A₀` minus one sheet, the missing sheet being the one carrying the dangling
`e₄`.  The members below are therefore built on
`ResolutionMkk.bothDetachedResolution`, whose Euler count closes.

One consequence of the one-sided shape is proved here because it is the hinge
of the next section: with `right := wall` the `t₃` exterior condition reads
`(data.edgePartition e).Refines (data.vertexPartition wall)`, which is a
*field of every gluing datum* (`detachedResolution_exterior_vacuous`), so over
the one-sided `GlobalMkk.Geometry` the three `DivalentPattern`s are jointly
satisfiable -- but only because the resolution they certify raises the genus.
With the genus-preserving two-sided detachment the joint satisfiability fails.

## The three members cannot share one gluing datum

`no_common_geometry`, exactly as in M-1k.  The detached sheet is
not free: the `t₃` exterior refinement forces it to be the unique sheet of the
dangling occurrence `e₄` (`transfer_eq_pinSheet`, from
`eq_pinSheet_of_block_singleton`, which in turn rests on `e₄` being the only
index-one occurrence above `t₃` -- `|e₃| = k₃ = k₁ + k₂ - 1 ≥ 3`).  That sheet
lies in exactly one of the two endpoint blocks `e₁`, `e₂`, so a given datum
carries Base II.2.1.M (`M⁽¹⁾`, `|e'| = k₁ - 1`, `|e''| = k₂`) or Base II.2.2.M
(`M⁽²⁾`, `|e'| = k₁`, `|e''| = k₂ - 1`) but never both.  `M⁽³⁾` (Base II.1.M)
is unconditional.

This is a matter of choosing representatives -- Part I compares gluing data up
to isomorphism, and a branch swap relates the two choices -- and the gauge move
is proved here: `branchSwap_moves_pinSheet` swaps the pinned
sheet with a sheet of the other endpoint block across the `t₂` branch, which
fixes the wall partition and fixes the `t₃` occurrence partition -- hence
fixes *which* sheet is pinned -- while exchanging the two endpoint blocks'
cardinalities at it, so `k₁` and `k₂` trade places and the other member
appears.  The separation input is not a carried hypothesis: it is
`Infrastructure.TargetSeparation.edgeMoved_eq_false`, from
`graph_connected target` and `genus target = 0`.  Consequently `GlobalMkk`
takes the second member over the branch-swapped datum
(`GlobalMkk.swappedCandidates`), as `GlobalM1k` does in its `section Swapped`.

## The shape's fields are jointly satisfiable

`deleted_single` is one of the two disjuncts of `W2R2SourceProfile.SourceProfile.cases`, and
`one_lt_first`/`one_lt_second` are the case hypothesis `k₁, k₂ ≥ 2` verbatim.
They are compatible: together they force `|A₀| = k₁ + k₂ ≥ 4` and
`k₃ = k₁ + k₂ - 1 ≥ 3`, which is consistent with every other field of the
profile, and `exists_detachData` then produces the partner sheet from the block
size alone.

## What is constructed

* `DetachData.candidate` -- the detachment member the datum itself selects,
  `M⁽¹⁾` (`FirstMember`) or `M⁽²⁾` (`SecondMember`), as an actual
  arbitrary-degree outgoing gluing datum;
* `joinedCandidate` -- `M⁽³⁾`, Base II.1.M, the whole block retained at both
  endpoints and along the new edge, `|e'| = k₁ + k₂`;

with validity (`detach_valid`, `joined_valid`), source genus
(`detach_sourceGenus`, `joined_sourceGenus`), target valencies (`2, 2` for
both, `detach_target_valencies`, `joined_target_valencies`), the Figure 34
new-edge indices (`detach_indices_first`, `detach_indices_second`,
`joined_newEdge_blockCard`) and the exact induced block counts on `A₀`
(`detach_blockCountWithin`: `3 + 1 = 2 + 2`).  The genus proofs use
`M11SourceGenus.candidate_sourceGenus_of_blockwise_euler`, because the
detachment member is not a star on the
distinguished block, and because these candidates are pasted blockwise rather
than being one global `LocalResolution`.  `W3ShiftSourceCandidates` is imported
only for two general `SheetPartition` counting facts it happens to own,
`detachSheet_blockCountWithin_self` and `detachSheet_rel_remainder`; nothing of
the W3 shift case is used.

`exists_firstMember_or_secondMember` and `not_firstMember_and_secondMember`
are the previous section in the form a consumer wants: a datum carries exactly
one of the two detachment members.

## What is constructed elsewhere

The *other* detachment member over the branch-swapped datum.  The gauge move
itself is here (`branchSwap_moves_pinSheet`, with its separation discharged),
but rebuilding the member on the swapped datum needs the `Shape`/`DetachData`
transported to it: the `W2R2SourceProfile.SourceProfile` is transported by
`W2SourceTransport.sourceProfile_relabel` for an arbitrary relabelling, the
`Shape` half by `W2MkkTransport.shapeRelabel`, and `W2MkkLimitColumns.remoteMember`
builds the member over the swapped datum on every datum of the case.

Equation (8) on actual matrices, honest stable presentations, the incoming
member and the certified exit are `W2MkkCommonBalance`, `W2MkkLimitColumns`,
`W2MkkIncomingMatching` and `W2MkkArbitraryExit`.
-/

namespace DraismaVargas.LocalCases.W2MkkSourceCandidates

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open ResolutionM11 ResolutionM1k GlobalM11Arbitrary

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## A blockwise counting lemma

The one general fact the two-sided detachment's blockwise Euler check needs:
detaching a sheet from the **fine** partition adds exactly one induced block
inside the coarse block containing it.  It belongs beside
`SheetPartition.card_blocks_eq_sum_blockCountWithin` in `Infrastructure.Change`,
and is kept local here.  (`ResolutionMkk.card_blocks_detachSheet` is the
*global* companion, and is used rather than repeated.) -/

theorem blockCountWithin_detachSheet_fine {d : ℕ} (fine coarse : SheetPartition d)
    (single remainder sheet : Fin d) (hne : single ≠ remainder)
    (hTogether : fine.Rel single remainder) (hRefines : fine.Refines coarse)
    (hSheet : coarse.Rel single sheet) :
    (fine.detachSheet single remainder hne hTogether).blockCountWithin coarse sheet =
      fine.blockCountWithin coarse sheet + 1 := by
  classical
  have hSingleMem : single ∈ coarse.block sheet :=
    (coarse.mem_block_iff sheet single).mpr hSheet.symm
  have hRemMem : remainder ∈ coarse.block sheet :=
    (coarse.mem_block_iff sheet remainder).mpr
      (hSheet.symm.trans (hRefines.rel hTogether))
  have hReprSingleMem : fine.repr single ∈ (coarse.block sheet).image fine.repr :=
    Finset.mem_image.mpr ⟨single, hSingleMem, rfl⟩
  have hImage : (coarse.block sheet).image
        (fine.detachSheet single remainder hne hTogether).repr =
      insert single (insert remainder
        (((coarse.block sheet).image fine.repr).erase (fine.repr single))) := by
    ext value
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨source, hSource, rfl⟩
      by_cases hSingle : source = single
      · subst hSingle
        exact Or.inl (fine.detachSheet_repr_single source remainder hne hTogether)
      · by_cases hBlock : fine.Rel single source
        · exact Or.inr (Or.inl (fine.detachSheet_repr_of_rel_of_ne single remainder
            source hne hTogether hSingle hBlock))
        · rw [fine.detachSheet_repr_of_not_rel single remainder source hne hTogether
            hBlock]
          exact Or.inr (Or.inr ⟨fun hEq ↦ hBlock hEq.symm, source, hSource, rfl⟩)
    · intro hValue
      rcases hValue with hEq | hEq | ⟨hNeRepr, source, hSource, hRepr⟩
      · refine ⟨single, hSingleMem, ?_⟩
        rw [hEq]
        exact fine.detachSheet_repr_single single remainder hne hTogether
      · refine ⟨remainder, hRemMem, ?_⟩
        rw [hEq]
        exact fine.detachSheet_repr_of_rel_of_ne single remainder remainder hne
          hTogether hne.symm hTogether
      · refine ⟨source, hSource, ?_⟩
        have hNotRel : ¬fine.Rel single source := by
          intro hRel
          exact hNeRepr (by rw [← hRepr]; exact hRel.symm)
        rw [fine.detachSheet_repr_of_not_rel single remainder source hne hTogether
          hNotRel]
        exact hRepr
  have hRemNotMem : remainder ∉
      ((coarse.block sheet).image fine.repr).erase (fine.repr single) := by
    intro hMem
    obtain ⟨hNeRepr, hMemImage⟩ := Finset.mem_erase.mp hMem
    obtain ⟨source, _, hSource⟩ := Finset.mem_image.mp hMemImage
    apply hNeRepr
    have hIdem : fine.repr remainder = remainder := by rw [← hSource, fine.repr_idem]
    rw [← hIdem]
    exact hTogether.symm
  have hSingleNotMem : single ∉ insert remainder
      (((coarse.block sheet).image fine.repr).erase (fine.repr single)) := by
    intro hMem
    rcases Finset.mem_insert.mp hMem with hEq | hErase
    · exact hne hEq
    · obtain ⟨hNeRepr, hMemImage⟩ := Finset.mem_erase.mp hErase
      obtain ⟨source, _, hSource⟩ := Finset.mem_image.mp hMemImage
      apply hNeRepr
      have hIdem : fine.repr single = single := by rw [← hSource, fine.repr_idem]
      exact hIdem.symm
  have hPos : 0 < ((coarse.block sheet).image fine.repr).card :=
    Finset.card_pos.mpr ⟨_, hReprSingleMem⟩
  unfold SheetPartition.blockCountWithin
  rw [hImage, Finset.card_insert_of_notMem hSingleNotMem,
    Finset.card_insert_of_notMem hRemNotMem,
    Finset.card_erase_of_mem hReprSingleMem]
  omega

/-- **Why the genus and the shared datum are the same story at Figure 34.**  The one-sided
detachment's second endpoint imposes nothing at all on the old occurrences:
`(edgePartition e).Refines (vertexPartition wall)` is a field of
`GluingDatum`.  So over `GlobalMkk.Geometry` as it stands the three
`DivalentPattern`s of Figure 34 *are* jointly satisfiable -- precisely because
the resolution they certify does not preserve the source genus.  Once the
second detachment is restored the same condition becomes
`refines_detachSheet_of_block_singleton`, which pins the detached sheet, and
`no_common_geometry` below applies. -/
theorem detachedResolution_exterior_vacuous
    (endpoint : SheetPartition degree) (single remainder : Fin degree)
    (hne : single ≠ remainder) (hTogether : endpoint.Rel single remainder)
    (hRefines : endpoint.Refines (data.vertexPartition wall))
    (edge : target.edges) (hAt : edge ∈ GluingDatum.incidentEdges wall) :
    (data.edgePartition edge).Refines
      (ResolutionMkk.detachedResolution (data.vertexPartition wall) endpoint single
        remainder hne hTogether hRefines).right :=
  refines_of_mem_incidentEdges data hAt

/-! ## The literal `w2Mkk` source shape -/

/-- The actual M-kk refinement of a `w2-r2-nd3` source profile: Cardinality M,
and both survivors above `t₂` of index at least two. -/
structure Shape {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block) where
  /-- Cardinality M: the dangling occurrence `e₄` lies above `t₃`. -/
  deleted_single : profile.deleted.edge.1.1.1 = star.edge profile.singleLabel
  /-- `k₁ ≥ 2`, which is what Base II.2.1.M asks for. -/
  one_lt_first : 1 < data.sourceEdgeIndex profile.first.1
  /-- `k₂ ≥ 2`, which is what Base II.2.2.M asks for. -/
  one_lt_second : 1 < data.sourceEdgeIndex profile.second.1

namespace Shape

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- The two target directions are the profile's own labels. -/
theorem label_cases (profile : W2R2SourceProfile.SourceProfile data star block)
    (label : Fin 2) : label = profile.doubleLabel ∨ label = profile.singleLabel := by
  have := profile.labels_ne
  omega

/-- Cardinality M, read off the profile's own case disjunction:
`k₁ + k₂ = |A₀|` and `k₃ + 1 = |A₀|`. -/
theorem cardinality (shape : Shape profile) :
    data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 =
        (data.vertexPartition wall).blockCard block.1 ∧
      data.sourceEdgeIndex profile.third.1 + 1 =
        (data.vertexPartition wall).blockCard block.1 := by
  rcases profile.cases with ⟨_, hPair, hSingle⟩ | ⟨hDouble, _, _⟩
  · exact ⟨hPair, hSingle⟩
  · exact absurd
      (star.edge_injective (shape.deleted_single.symm.trans hDouble)).symm
      profile.labels_ne

/-- `|A₀| = k₁ + k₂`. -/
theorem blockCard (shape : Shape profile) :
    (data.vertexPartition wall).blockCard block.1 =
      data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 :=
  shape.cardinality.1.symm

/-- `k₃ + 1 = k₁ + k₂`, so `k₃ = k₁ + k₂ - 1`.  This is the identity the limit
box `c(e₃)/(k₁+k₂-1) + s = 0` of Figure 34 displays. -/
theorem third_index (shape : Shape profile) :
    data.sourceEdgeIndex profile.third.1 + 1 =
      data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 := by
  have := shape.cardinality
  omega

/-- `2|A₀| - 1 = k₁ + k₂ + k₃`, the index sum of case `{w2-r2-nd3}`,
with `k₄ = 1`. -/
theorem index_sum (shape : Shape profile) :
    data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 +
        data.sourceEdgeIndex profile.third.1 + 1 =
      2 * (data.vertexPartition wall).blockCard block.1 := by
  have := shape.cardinality
  omega

/-- `k₃ > k₁`: the first half of "Base I is precluded" in case
`{w2-r2-nd3-M-kk}`. -/
theorem first_lt_third (shape : Shape profile) :
    data.sourceEdgeIndex profile.first.1 < data.sourceEdgeIndex profile.third.1 := by
  have := shape.third_index
  have := shape.one_lt_second
  omega

/-- `k₃ > k₂`: the second half. -/
theorem second_lt_third (shape : Shape profile) :
    data.sourceEdgeIndex profile.second.1 < data.sourceEdgeIndex profile.third.1 := by
  have := shape.third_index
  have := shape.one_lt_first
  omega

/-- **Base I is precluded** (case `{w2-r2-nd3-M-kk}`), in the source's own words: `|e₂| ≠ |e₃|`
and `|e₂| ≠ |e₄| = 1`. -/
theorem base_one_precluded (shape : Shape profile) :
    data.sourceEdgeIndex profile.second.1 ≠ data.sourceEdgeIndex profile.third.1 ∧
      data.sourceEdgeIndex profile.second.1 ≠ data.sourceEdgeIndex profile.deleted.edge.1 := by
  have hLt := shape.second_lt_third
  have hOne := shape.one_lt_second
  rw [profile.deleted.index_one]
  omega

/-- `3 ≤ k₃`, which is what makes the dangling `e₄` the *unique* index-one
occurrence above `t₃`. -/
theorem three_le_third (shape : Shape profile) :
    3 ≤ data.sourceEdgeIndex profile.third.1 := by
  have := shape.third_index
  have := shape.one_lt_first
  have := shape.one_lt_second
  omega

end Shape

/-! ## The two endpoint blocks and the pinned sheet -/

section Sheets

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- **Figure 34's left endpoint partition is not a choice.**  It is the `t₂`
direction's own occurrence partition, whose two blocks inside `A₀` are `e₁`
and `e₂`: Base II.2's `h(e₁⁽ᵠ⁾) = h(e')`, `h(e₂⁽ᵠ⁾) = h(e'')` with
`|A'| = k₁`, `|A''| = k₂`. -/
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

/-- **The pinned sheet**: the unique sheet of the dangling occurrence `e₄`.
Everything about which Figure 34 member a given datum admits is a corollary of
where this sheet sits. -/
def pinSheet (profile : W2R2SourceProfile.SourceProfile data star block) :
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

theorem pinSheet_rel (profile : W2R2SourceProfile.SourceProfile data star block) :
    (data.vertexPartition wall).Rel block.1 (pinSheet profile) :=
  sheet_rel_of_incident profile.deleted.edge

theorem endpointPartition_repr_first
    (profile : W2R2SourceProfile.SourceProfile data star block) :
    (endpointPartition profile).repr (firstSheet profile) = firstSheet profile := by
  have h := profile.first.1.2
  rw [profile.first_target] at h
  exact h

theorem endpointPartition_repr_second
    (profile : W2R2SourceProfile.SourceProfile data star block) :
    (endpointPartition profile).repr (secondSheet profile) = secondSheet profile := by
  have h := profile.second.1.2
  rw [profile.second_target] at h
  exact h

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

/-- `e₁` and `e₂` are distinct blocks of the `t₂` occurrence partition. -/
theorem endpointPartition_separate
    (profile : W2R2SourceProfile.SourceProfile data star block) :
    ¬(endpointPartition profile).Rel (firstSheet profile) (secondSheet profile) := by
  intro hRel
  apply profile.first_ne_second
  have hSheet : firstSheet profile = secondSheet profile := by
    have h := hRel
    rw [SheetPartition.rel_iff, endpointPartition_repr_first,
      endpointPartition_repr_second] at h
    exact h
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (profile.first_target.trans profile.second_target.symm) hSheet

theorem firstSheet_ne_secondSheet
    (profile : W2R2SourceProfile.SourceProfile data star block) :
    firstSheet profile ≠ secondSheet profile := by
  intro hEq
  apply endpointPartition_separate profile
  rw [hEq]
  exact ((endpointPartition profile).rel_iff _ _).mpr rfl

/-- **`e₁` and `e₂` tile `A₀`.**  Cardinality M puts the dangling occurrence
above `t₃`, so the two survivors are the whole `t₂` fibre of the block. -/
theorem endpointPartition_covers (shape : Shape profile) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    (endpointPartition profile).Rel (firstSheet profile) sheet ∨
      (endpointPartition profile).Rel (secondSheet profile) sheet := by
  have hIncident : Incident data (data.sourceEdge (star.edge profile.doubleLabel) sheet)
      (WallBlock.sourceVertex data wall block) := by
    apply (incident_wallBlock_sourceVertex_iff data block _).mpr
    refine ⟨star.edge_mem_incidentEdges profile.doubleLabel, ?_⟩
    apply (WallBlock.ofSheet_eq_iff_rel data wall block _).mpr
    exact hSheet.trans ((star.edgePartition_refines_wall data profile.doubleLabel).rel
      ((data.edgePartition (star.edge profile.doubleLabel)).rel_repr_right sheet))
  have hNeLabel : star.edge profile.singleLabel ≠ star.edge profile.doubleLabel :=
    star.edge_injective.ne (Ne.symm profile.labels_ne)
  rcases profile.exhaustive ⟨_, hIncident⟩ with hEq | hEq | hEq | hEq
  · left
    have hSheet := congrArg (fun edge ↦ edge.1.1.2) hEq
    change (endpointPartition profile).repr sheet = firstSheet profile at hSheet
    rw [SheetPartition.rel_iff, endpointPartition_repr_first, hSheet]
  · right
    have hSheet := congrArg (fun edge ↦ edge.1.1.2) hEq
    change (endpointPartition profile).repr sheet = secondSheet profile at hSheet
    rw [SheetPartition.rel_iff, endpointPartition_repr_second, hSheet]
  · exact absurd ((congrArg (fun edge ↦ edge.1.1.1) hEq).trans profile.third_target)
      (star.edge_injective.ne profile.labels_ne)
  · exact absurd ((congrArg (fun edge ↦ edge.1.1.1) hEq).trans shape.deleted_single)
      (star.edge_injective.ne profile.labels_ne)

/-- **The exact induced-block count of the left endpoint on `A₀`: two.** -/
theorem endpointPartition_blockCountWithin (shape : Shape profile) (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    (endpointPartition profile).blockCountWithin (data.vertexPartition wall) anchor = 2 := by
  classical
  have hFirstMem : firstSheet profile ∈ (data.vertexPartition wall).block anchor :=
    ((data.vertexPartition wall).mem_block_iff anchor _).mpr
      (hAnchor.symm.trans (firstSheet_rel profile))
  have hSecondMem : secondSheet profile ∈ (data.vertexPartition wall).block anchor :=
    ((data.vertexPartition wall).mem_block_iff anchor _).mpr
      (hAnchor.symm.trans (secondSheet_rel profile))
  have hImage : ((data.vertexPartition wall).block anchor).image
      (endpointPartition profile).repr = {firstSheet profile, secondSheet profile} := by
    ext value
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton,
      SheetPartition.mem_block_iff]
    constructor
    · rintro ⟨source, hSource, rfl⟩
      rcases endpointPartition_covers shape source (hAnchor.trans hSource) with h | h
      · exact Or.inl (by rw [← endpointPartition_repr_first profile, h])
      · exact Or.inr (by rw [← endpointPartition_repr_second profile, h])
    · rintro (rfl | rfl)
      · exact ⟨firstSheet profile, (((data.vertexPartition wall).mem_block_iff anchor _).mp
          hFirstMem), endpointPartition_repr_first profile⟩
      · exact ⟨secondSheet profile, (((data.vertexPartition wall).mem_block_iff anchor _).mp
          hSecondMem), endpointPartition_repr_second profile⟩
  unfold SheetPartition.blockCountWithin
  rw [hImage, Finset.card_insert_of_notMem (by
    simpa using firstSheet_ne_secondSheet profile), Finset.card_singleton]

/-- `|e₄| = 1`: the pinned sheet is a singleton of the `t₃` occurrence
partition. -/
theorem pinSheet_blockCard (shape : Shape profile) :
    (data.edgePartition (star.edge profile.singleLabel)).blockCard (pinSheet profile) = 1 := by
  have hIndex : data.sourceEdgeIndex profile.deleted.edge.1 =
      (data.edgePartition profile.deleted.edge.1.1.1).blockCard (pinSheet profile) := rfl
  rw [shape.deleted_single, profile.deleted.index_one] at hIndex
  exact hIndex.symm

theorem pinSheet_block (shape : Shape profile) :
    (data.edgePartition (star.edge profile.singleLabel)).block (pinSheet profile) =
      {pinSheet profile} :=
  SheetPartition.block_eq_singleton_of_blockCard_eq_one _ _ (pinSheet_blockCard shape)

/-- **`e₄` is the only index-one occurrence above `t₃`**, because
`|e₃| = k₃ = k₁ + k₂ - 1 ≥ 3`. -/
theorem eq_deleted_of_single_index_one (shape : Shape profile)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block))
    (hTarget : edge.1.1.1 = star.edge profile.singleLabel)
    (hIndex : data.sourceEdgeIndex edge.1 = 1) : edge = profile.deleted.edge := by
  have hNeLabel : star.edge profile.doubleLabel ≠ star.edge profile.singleLabel :=
    star.edge_injective.ne profile.labels_ne
  rcases profile.exhaustive edge with rfl | rfl | rfl | rfl
  · exact absurd (profile.first_target.symm.trans hTarget) hNeLabel
  · exact absurd (profile.second_target.symm.trans hTarget) hNeLabel
  · have := shape.three_le_third
    omega
  · rfl

/-- **The pinned sheet is the only sheet of `A₀` that the `t₃` direction
isolates.**  This is the whole content of Finding 2. -/
theorem eq_pinSheet_of_block_singleton (shape : Shape profile) (sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel block.1 sheet)
    (hSingleton : (data.edgePartition (star.edge profile.singleLabel)).block sheet =
      {sheet}) : sheet = pinSheet profile := by
  have hRepr : (data.edgePartition (star.edge profile.singleLabel)).repr sheet = sheet := by
    have hMem : (data.edgePartition (star.edge profile.singleLabel)).repr sheet ∈
        (data.edgePartition (star.edge profile.singleLabel)).block sheet :=
      ((data.edgePartition (star.edge profile.singleLabel)).mem_block_iff sheet _).mpr
        ((data.edgePartition (star.edge profile.singleLabel)).rel_repr_right sheet)
    rw [hSingleton] at hMem
    simpa using hMem
  have hIncident : Incident data
      (data.sourceEdge (star.edge profile.singleLabel) sheet)
      (WallBlock.sourceVertex data wall block) := by
    apply (incident_wallBlock_sourceVertex_iff data block _).mpr
    refine ⟨star.edge_mem_incidentEdges profile.singleLabel, ?_⟩
    apply (WallBlock.ofSheet_eq_iff_rel data wall block _).mpr
    exact hRel.trans ((star.edgePartition_refines_wall data profile.singleLabel).rel
      ((data.edgePartition (star.edge profile.singleLabel)).rel_repr_right sheet))
  have hIndex : data.sourceEdgeIndex
      (data.sourceEdge (star.edge profile.singleLabel) sheet) = 1 := by
    rw [GluingDatum.sourceEdgeIndex_sourceEdge]
    simp [SheetPartition.blockCard, hSingleton]
  have hEq := eq_deleted_of_single_index_one shape ⟨_, hIncident⟩ rfl hIndex
  have hSheet := congrArg (fun edge ↦ edge.1.1.2) hEq
  change (data.edgePartition (star.edge profile.singleLabel)).repr sheet =
    pinSheet profile at hSheet
  rw [hRepr] at hSheet
  exact hSheet

/-- The pinned sheet lies in `e₁` or in `e₂`, and in exactly one of them. -/
theorem pinSheet_mem (shape : Shape profile) :
    (endpointPartition profile).Rel (firstSheet profile) (pinSheet profile) ∨
      (endpointPartition profile).Rel (secondSheet profile) (pinSheet profile) :=
  endpointPartition_covers shape _ (pinSheet_rel profile)

theorem one_lt_pinSheet_endpoint_blockCard (shape : Shape profile) :
    1 < (endpointPartition profile).blockCard (pinSheet profile) := by
  rcases pinSheet_mem shape with hRel | hRel
  · rw [← SheetPartition.blockCard_congr _ hRel, endpointPartition_blockCard_first]
    exact shape.one_lt_first
  · rw [← SheetPartition.blockCard_congr _ hRel, endpointPartition_blockCard_second]
    exact shape.one_lt_second

end Sheets

/-! ## Orienting the two-star

`M11SourceCandidates.joinedBackground` sends label `0` to the retained endpoint
and label `1` to the fresh one.  The profile's `doubleLabel` need not be `0`, so
the two-star is relabelled.  A `TwoStar` is nothing but a labelling of the two
occurrences at a divalent wall, so this is a derived object, not an input. -/

section Orientation

/-- Relabel a two-star so that label `0` names a chosen direction. -/
def orientStar (star : TwoStar target wall) (label : Fin 2) : TwoStar target wall :=
  ⟨(Equiv.swap 0 label).trans star.label⟩

theorem orientStar_edge (star : TwoStar target wall) (label other : Fin 2) :
    (orientStar star label).edge other = star.edge (Equiv.swap 0 label other) := rfl

variable {block : WallBlock data wall}

/-- The two-star with the `t₂` direction on label `0` and `t₃` on label `1`. -/
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

end Orientation

/-! ## The three Figure 34 members -/

section Members

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

theorem exists_label (twoStar : TwoStar target wall) (edge : target.edges)
    (hAt : edge ∈ GluingDatum.incidentEdges wall) : ∃ label, twoStar.edge label = edge :=
  ⟨twoStar.label.symm ⟨edge, hAt⟩,
    congrArg Subtype.val (twoStar.label.apply_symm_apply ⟨edge, hAt⟩)⟩

theorem joinedBackground_right (twoStar : TwoStar target wall)
    (distinguished : Fin degree) (edge : target.edges) :
    (M11SourceCandidates.joinedBackground data twoStar distinguished).right edge =
      twoStar.right edge := rfl

/-- Figure 34's detachment datum: a partner for the pinned sheet inside *its
own* endpoint block.  Which of `e₁`, `e₂` that block is decides whether the
member is Base II.2.1.M (`M⁽¹⁾`) or Base II.2.2.M (`M⁽²⁾`); the datum decides
it, not the reader. -/
structure DetachData (profile : W2R2SourceProfile.SourceProfile data star block) where
  remainder : Fin degree
  ne_remainder : pinSheet profile ≠ remainder
  together : (endpointPartition profile).Rel (pinSheet profile) remainder

namespace DetachData

theorem wallTogether (detach : DetachData profile) :
    (data.vertexPartition wall).Rel (pinSheet profile) detach.remainder :=
  (endpointPartition_refines profile).rel detach.together

/-- Figure 34's `M⁽¹⁾`/`M⁽²⁾` local resolution: the `t₂` endpoint keeps its own
occurrence partition, the new edge detaches the pinned sheet from it, and the
`t₃` endpoint detaches the *same* sheet from the whole wall block, giving
`A⁽ᵠ⁾ = A₀ ∖ {x}` of `k₃` sheets. -/
noncomputable def selected (detach : DetachData profile) : LocalResolution degree :=
  ResolutionMkk.bothDetachedResolution (data.vertexPartition wall)
    (endpointPartition profile) (pinSheet profile) detach.remainder
    detach.ne_remainder detach.wallTogether detach.together
    (endpointPartition_refines profile)

theorem selected_left (detach : DetachData profile) :
    detach.selected.left = endpointPartition profile := rfl

theorem selected_right (detach : DetachData profile) :
    detach.selected.right = (data.vertexPartition wall).detachSheet (pinSheet profile)
      detach.remainder detach.ne_remainder detach.wallTogether := rfl

theorem selected_newEdge (detach : DetachData profile) :
    detach.selected.newEdge = (endpointPartition profile).detachSheet (pinSheet profile)
      detach.remainder detach.ne_remainder detach.together := rfl

theorem selected_contracts (detach : DetachData profile) :
    detach.selected.ContractsTo (data.vertexPartition wall) :=
  ResolutionMkk.bothDetachedResolution_contracts _ _ _ _ _ _ _ _

/-- The occurrence pattern of the detachment member, with both exterior
refinements derived from the actual occurrence indices. -/
noncomputable def pattern (shape : Shape profile) (detach : DetachData profile) :
    GlobalMkk.DivalentPattern (data := data) (wall := wall)
      (pinSheet profile) detach.selected where
  background := M11SourceCandidates.joinedBackground data (orientedStar profile)
    (pinSheet profile)
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
          (pinSheet profile)).right ((orientedStar profile).edge 0) = false := by
        rw [joinedBackground_right]
        exact TwoStar.right_edge_zero _
      rw [ite_eq_right (by rw [hFalse]; simp)]
      show (data.edgePartition ((orientedStar profile).edge 0)).Refines
        (endpointPartition profile)
      rw [orientedStar_edge_zero]
      exact SheetPartition.Refines.refl _
    · have hTrue : (M11SourceCandidates.joinedBackground data (orientedStar profile)
          (pinSheet profile)).right ((orientedStar profile).edge 1) = true := by
        rw [joinedBackground_right]
        exact TwoStar.right_edge_one _
      rw [ite_eq_left hTrue]
      show (data.edgePartition ((orientedStar profile).edge 1)).Refines
        ((data.vertexPartition wall).detachSheet (pinSheet profile) detach.remainder
          detach.ne_remainder detach.wallTogether)
      rw [orientedStar_edge_one]
      exact SheetPartition.refines_detachSheet_of_block_singleton _
        (data.vertexPartition wall) (pinSheet profile) detach.remainder
        detach.ne_remainder detach.wallTogether
        (star.edgePartition_refines_wall data profile.singleLabel)
        (pinSheet_block shape)

/-- Figure 34's detachment member as an actual arbitrary-degree outgoing
gluing datum. -/
noncomputable def candidate (shape : Shape profile) (detach : DetachData profile) :
    BalancedGlobal.Candidate target degree data wall :=
  (detach.pattern shape).candidate detach.selected_contracts

end DetachData

/-- A block of size `k₁ + k₂ ≥ 4` always supplies the partner sheet: the pinned
sheet's own endpoint block has `k₁ ≥ 2` or `k₂ ≥ 2` sheets. -/
theorem exists_detachData (shape : Shape profile) : Nonempty (DetachData profile) := by
  obtain ⟨partner, hPartner, hNe⟩ :=
    (endpointPartition profile).exists_other_of_one_lt_blockCard (pinSheet profile)
      (one_lt_pinSheet_endpoint_blockCard shape)
  exact ⟨⟨partner, hNe, hPartner⟩⟩

/-- Figure 34's `M⁽³⁾`, Base II.1.M: both endpoints and the new edge keep the
whole wall partition, `|e'| = |A⁽³⁾| = |A'| = k₁ + k₂`.  No occurrence
hypothesis at all is used, so this member always exists. -/
noncomputable def joinedPattern
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished : Fin degree) :
    GlobalMkk.DivalentPattern (data := data) (wall := wall) distinguished
      (thirdResolution (data.vertexPartition wall)) where
  background := M11SourceCandidates.joinedBackground data (orientedStar profile)
    distinguished
  leftExternal := (orientedStar profile).edge 0
  rightExternal := (orientedStar profile).edge 1
  leftEdges := rfl
  rightEdges := rfl
  exterior := by
    intro edge hAt
    have hRefines := refines_of_mem_incidentEdges data (by
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] using hAt)
    simpa only [thirdResolution, joinedResolutionAt, ite_self] using hRefines

noncomputable def joinedCandidate
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished : Fin degree) :
    BalancedGlobal.Candidate target degree data wall :=
  (joinedPattern profile distinguished).candidate (thirdResolution_contracts _)


/-! ### Validity, source genus and target valencies -/

theorem detach_valid (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) : (detach.candidate shape).datum.Valid :=
  (detach.candidate shape).datum_valid input.valid

theorem joined_valid (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished : Fin degree) :
    (joinedCandidate profile distinguished).datum.Valid :=
  (joinedCandidate profile distinguished).datum_valid input.valid

/-- **The detachment member preserves the complete quotient-source genus.**  Its
selected block is not a star -- the new edge is strictly finer than the `t₂`
endpoint -- so this goes through the blockwise Euler identity.  The two
detachments cancel: the new edge gains one induced block over the `t₂`
endpoint, and the `t₃` endpoint gains one over the wall. -/
theorem detach_sourceGenus (shape : Shape profile) (detach : DetachData profile) :
    genus (detach.candidate shape).datum.sourceGraph = genus data.sourceGraph := by
  apply M11SourceGenus.candidate_sourceGenus_of_blockwise_euler
  intro anchor _
  have hResolution : (detach.candidate shape).resolution anchor =
      LocalResolution.onBlock (data.vertexPartition wall) (pinSheet profile)
        detach.selected
        (fun _ ↦ joinedResolutionAt (data.vertexPartition wall)) anchor := rfl
  rw [hResolution]
  by_cases hSelected : (data.vertexPartition wall).Rel (pinSheet profile) anchor
  · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hSelected]
    have hNew := blockCountWithin_detachSheet_fine (endpointPartition profile)
      (data.vertexPartition wall) (pinSheet profile) detach.remainder anchor
      detach.ne_remainder detach.together (endpointPartition_refines profile) hSelected
    have hRight := W3ShiftSourceCandidates.detachSheet_blockCountWithin_self
      (data.vertexPartition wall) (pinSheet profile) detach.remainder anchor
      detach.ne_remainder detach.wallTogether hSelected
    rw [DetachData.selected_newEdge, DetachData.selected_left, DetachData.selected_right]
    omega
  · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hSelected]
    simp only [joinedResolutionAt, SheetPartition.blockCountWithin_self]

/-- `M⁽³⁾` keeps the whole wall partition everywhere, so it is a star on every
block. -/
theorem joined_sourceGenus (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished : Fin degree) :
    genus (joinedCandidate profile distinguished).datum.sourceGraph =
      genus data.sourceGraph := by
  apply M11SourceGenus.candidate_sourceGenus_of_stars
  intro anchor
  have hResolution : (joinedCandidate profile distinguished).resolution anchor =
      LocalResolution.onBlock (data.vertexPartition wall) distinguished
        (thirdResolution (data.vertexPartition wall))
        (fun _ ↦ joinedResolutionAt (data.vertexPartition wall)) anchor := rfl
  rw [hResolution]
  simp only [LocalResolution.onBlock, ite_self]
  exact Or.inl ⟨rfl, rfl⟩

/-- Both members expand the divalent wall into `T₂`: two divalent endpoints. -/
theorem detach_target_valencies (shape : Shape profile) (detach : DetachData profile) :
    (GluingDatum.incidentEdges
      (target := graph target wall (detach.candidate shape).right)
      (oldVertex target wall)).card = 2 ∧
    (GluingDatum.incidentEdges
      (target := graph target wall (detach.candidate shape).right)
      (freshVertex target)).card = 2 :=
  M11SourceCandidates.candidate_target_valencies (detach.candidate shape)

theorem joined_target_valencies
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished : Fin degree) :
    (GluingDatum.incidentEdges
      (target := graph target wall (joinedCandidate profile distinguished).right)
      (oldVertex target wall)).card = 2 ∧
    (GluingDatum.incidentEdges
      (target := graph target wall (joinedCandidate profile distinguished).right)
      (freshVertex target)).card = 2 :=
  M11SourceCandidates.candidate_target_valencies (joinedCandidate profile distinguished)

/-! ### The displayed Figure 34 indices and induced block counts -/

/-- **The exact induced-block counts on `A₀`.**  Two blocks at the `t₂`
endpoint (`e₁`, `e₂`), three along the new edge (`e'`, `e''` and the detached
singleton) and two at the `t₃` endpoint (`A⁽ᵠ⁾` and the same singleton).  The
blockwise Euler identity `3 + 1 = 2 + 2` is what `detach_sourceGenus` consumes. -/
theorem detach_blockCountWithin (shape : Shape profile) (detach : DetachData profile)
    (anchor : Fin degree) (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    detach.selected.left.blockCountWithin (data.vertexPartition wall) anchor = 2 ∧
      detach.selected.newEdge.blockCountWithin (data.vertexPartition wall) anchor = 3 ∧
      detach.selected.right.blockCountWithin (data.vertexPartition wall) anchor = 2 := by
  have hPin : (data.vertexPartition wall).Rel (pinSheet profile) anchor :=
    (pinSheet_rel profile).symm.trans hAnchor
  have hLeft := endpointPartition_blockCountWithin shape anchor hAnchor
  have hNew := blockCountWithin_detachSheet_fine (endpointPartition profile)
    (data.vertexPartition wall) (pinSheet profile) detach.remainder anchor
    detach.ne_remainder detach.together (endpointPartition_refines profile) hPin
  have hRight := W3ShiftSourceCandidates.detachSheet_blockCountWithin_self
    (data.vertexPartition wall) (pinSheet profile) detach.remainder anchor
    detach.ne_remainder detach.wallTogether hPin
  refine ⟨hLeft, ?_, hRight⟩
  rw [DetachData.selected_newEdge, hNew, hLeft]

/-- `|A₀| = k₁ + k₂` read at any sheet of the block. -/
theorem blockCard_of_rel (shape : Shape profile) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    (data.vertexPartition wall).blockCard sheet =
      data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 := by
  rw [← SheetPartition.blockCard_congr (data.vertexPartition wall) hSheet]
  exact shape.blockCard

/-- **Figure 34's `M⁽¹⁾`, Base II.2.1.M**: when the datum puts the
pinned sheet in `e₁`, the new edge displays `|e'| = k₁ - 1` and `|e''| = k₂`,
the detached singleton is unlisted because it is dangling, and the `t₃`
endpoint block is `A⁽¹⁾ = A₀ ∖ {x}` with `|A⁽¹⁾| = k₃`. -/
theorem detach_indices_first (shape : Shape profile) (detach : DetachData profile)
    (hFirst : (endpointPartition profile).Rel (firstSheet profile) (pinSheet profile)) :
    detach.selected.newEdge.blockCard (pinSheet profile) = 1 ∧
      detach.selected.newEdge.blockCard detach.remainder + 1 =
        data.sourceEdgeIndex profile.first.1 ∧
      detach.selected.newEdge.blockCard (secondSheet profile) =
        data.sourceEdgeIndex profile.second.1 ∧
      detach.selected.right.blockCard (secondSheet profile) =
        data.sourceEdgeIndex profile.third.1 := by
  have hPinCard : (endpointPartition profile).blockCard (pinSheet profile) =
      data.sourceEdgeIndex profile.first.1 := by
    rw [← SheetPartition.blockCard_congr _ hFirst, endpointPartition_blockCard_first]
  have hNotSecond : ¬(endpointPartition profile).Rel (pinSheet profile)
      (secondSheet profile) := fun h ↦ endpointPartition_separate profile (hFirst.trans h)
  have hNeSecond : secondSheet profile ≠ pinSheet profile := by
    intro hEq
    exact hNotSecond (((endpointPartition profile).rel_iff _ _).mpr (by rw [hEq]))
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ((endpointPartition profile).detachSheet (pinSheet profile) detach.remainder
        detach.ne_remainder detach.together).blockCard (pinSheet profile) = 1
    exact (endpointPartition profile).detachSheet_blockCard_single _ _ _ _
  · show ((endpointPartition profile).detachSheet (pinSheet profile) detach.remainder
        detach.ne_remainder detach.together).blockCard detach.remainder + 1 =
      data.sourceEdgeIndex profile.first.1
    rw [(endpointPartition profile).detachSheet_blockCard_remainder (pinSheet profile)
      detach.remainder detach.ne_remainder detach.together, hPinCard]
    have := shape.one_lt_first
    omega
  · show ((endpointPartition profile).detachSheet (pinSheet profile) detach.remainder
        detach.ne_remainder detach.together).blockCard (secondSheet profile) =
      data.sourceEdgeIndex profile.second.1
    rw [(endpointPartition profile).detachSheet_blockCard_of_not_rel (pinSheet profile)
      detach.remainder (secondSheet profile) detach.ne_remainder detach.together
      hNotSecond, endpointPartition_blockCard_second]
  · show ((data.vertexPartition wall).detachSheet (pinSheet profile) detach.remainder
        detach.ne_remainder detach.wallTogether).blockCard (secondSheet profile) =
      data.sourceEdgeIndex profile.third.1
    have hRel := W3ShiftSourceCandidates.detachSheet_rel_remainder
      (data.vertexPartition wall) (pinSheet profile) detach.remainder
      (secondSheet profile) detach.ne_remainder detach.wallTogether
      ((pinSheet_rel profile).symm.trans (secondSheet_rel profile)) hNeSecond
    rw [SheetPartition.blockCard_congr _ hRel,
      (data.vertexPartition wall).detachSheet_blockCard_remainder (pinSheet profile)
        detach.remainder detach.ne_remainder detach.wallTogether,
      blockCard_of_rel shape (pinSheet profile) (pinSheet_rel profile)]
    have := shape.third_index
    omega

/-- **Figure 34's `M⁽²⁾`, Base II.2.2.M**: the mirror statement, when the datum
puts the pinned sheet in `e₂`.  `|e'| = k₁`, `|e''| = k₂ - 1`, and the `t₃`
endpoint block again has `k₃` sheets. -/
theorem detach_indices_second (shape : Shape profile) (detach : DetachData profile)
    (hSecond : (endpointPartition profile).Rel (secondSheet profile) (pinSheet profile)) :
    detach.selected.newEdge.blockCard (pinSheet profile) = 1 ∧
      detach.selected.newEdge.blockCard detach.remainder + 1 =
        data.sourceEdgeIndex profile.second.1 ∧
      detach.selected.newEdge.blockCard (firstSheet profile) =
        data.sourceEdgeIndex profile.first.1 ∧
      detach.selected.right.blockCard (firstSheet profile) =
        data.sourceEdgeIndex profile.third.1 := by
  have hPinCard : (endpointPartition profile).blockCard (pinSheet profile) =
      data.sourceEdgeIndex profile.second.1 := by
    rw [← SheetPartition.blockCard_congr _ hSecond, endpointPartition_blockCard_second]
  have hNotFirst : ¬(endpointPartition profile).Rel (pinSheet profile)
      (firstSheet profile) := fun h ↦
    endpointPartition_separate profile (h.symm.trans hSecond.symm)
  have hNeFirst : firstSheet profile ≠ pinSheet profile := by
    intro hEq
    exact hNotFirst (((endpointPartition profile).rel_iff _ _).mpr (by rw [hEq]))
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ((endpointPartition profile).detachSheet (pinSheet profile) detach.remainder
        detach.ne_remainder detach.together).blockCard (pinSheet profile) = 1
    exact (endpointPartition profile).detachSheet_blockCard_single _ _ _ _
  · show ((endpointPartition profile).detachSheet (pinSheet profile) detach.remainder
        detach.ne_remainder detach.together).blockCard detach.remainder + 1 =
      data.sourceEdgeIndex profile.second.1
    rw [(endpointPartition profile).detachSheet_blockCard_remainder (pinSheet profile)
      detach.remainder detach.ne_remainder detach.together, hPinCard]
    have := shape.one_lt_second
    omega
  · show ((endpointPartition profile).detachSheet (pinSheet profile) detach.remainder
        detach.ne_remainder detach.together).blockCard (firstSheet profile) =
      data.sourceEdgeIndex profile.first.1
    rw [(endpointPartition profile).detachSheet_blockCard_of_not_rel (pinSheet profile)
      detach.remainder (firstSheet profile) detach.ne_remainder detach.together
      hNotFirst, endpointPartition_blockCard_first]
  · show ((data.vertexPartition wall).detachSheet (pinSheet profile) detach.remainder
        detach.ne_remainder detach.wallTogether).blockCard (firstSheet profile) =
      data.sourceEdgeIndex profile.third.1
    have hRel := W3ShiftSourceCandidates.detachSheet_rel_remainder
      (data.vertexPartition wall) (pinSheet profile) detach.remainder
      (firstSheet profile) detach.ne_remainder detach.wallTogether
      ((pinSheet_rel profile).symm.trans (firstSheet_rel profile)) hNeFirst
    rw [SheetPartition.blockCard_congr _ hRel,
      (data.vertexPartition wall).detachSheet_blockCard_remainder (pinSheet profile)
        detach.remainder detach.ne_remainder detach.wallTogether,
      blockCard_of_rel shape (pinSheet profile) (pinSheet_rel profile)]
    have := shape.third_index
    omega

/-- **Figure 34's `M⁽³⁾`, Base II.1.M**: the new edge retains the whole wall
block, `|e'| = |A⁽³⁾| = |A'| = k₃ + 1 = k₁ + k₂`. -/
theorem joined_newEdge_blockCard (shape : Shape profile) (distinguished : Fin degree)
    (anchor sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    ((joinedCandidate profile distinguished).resolution anchor).newEdge.blockCard sheet =
      data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 := by
  have hResolution : (joinedCandidate profile distinguished).resolution anchor =
      LocalResolution.onBlock (data.vertexPartition wall) distinguished
        (thirdResolution (data.vertexPartition wall))
        (fun _ ↦ joinedResolutionAt (data.vertexPartition wall)) anchor := rfl
  have hNewEdge : ((joinedCandidate profile distinguished).resolution anchor).newEdge =
      data.vertexPartition wall := by
    rw [hResolution]
    by_cases hRel : (data.vertexPartition wall).Rel distinguished anchor
    · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hRel]
      rfl
    · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hRel]
      rfl
  rw [hNewEdge]
  exact blockCard_of_rel shape sheet hSheet

/-- `M⁽³⁾` keeps one induced block everywhere: it is a star on every wall
block, and its blockwise Euler identity is `1 + 1 = 1 + 1`. -/
theorem joined_blockCountWithin
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished anchor sheet : Fin degree) :
    ((joinedCandidate profile distinguished).resolution anchor).left.blockCountWithin
        (data.vertexPartition wall) sheet = 1 ∧
      ((joinedCandidate profile distinguished).resolution anchor).newEdge.blockCountWithin
        (data.vertexPartition wall) sheet = 1 ∧
      ((joinedCandidate profile distinguished).resolution anchor).right.blockCountWithin
        (data.vertexPartition wall) sheet = 1 := by
  have hResolution : (joinedCandidate profile distinguished).resolution anchor =
      LocalResolution.onBlock (data.vertexPartition wall) distinguished
        (thirdResolution (data.vertexPartition wall))
        (fun _ ↦ joinedResolutionAt (data.vertexPartition wall)) anchor := rfl
  rw [hResolution]
  by_cases hRel : (data.vertexPartition wall).Rel distinguished anchor
  · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hRel]
    exact ⟨SheetPartition.blockCountWithin_self _ _, SheetPartition.blockCountWithin_self _ _,
      SheetPartition.blockCountWithin_self _ _⟩
  · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hRel]
    exact ⟨SheetPartition.blockCountWithin_self _ _, SheetPartition.blockCountWithin_self _ _,
      SheetPartition.blockCountWithin_self _ _⟩

/-! ### The two detachment members, named -/

/-- A datum's pinned sheet lies in `e₁` or in `e₂`, and never in both, so the
two detachment members of Figure 34 exclude each other. -/
theorem not_first_and_second
    (hFirst : (endpointPartition profile).Rel (firstSheet profile) (pinSheet profile))
    (hSecond : (endpointPartition profile).Rel (secondSheet profile) (pinSheet profile)) :
    False :=
  endpointPartition_separate profile (hFirst.trans hSecond.symm)

/-- Figure 34's `M⁽¹⁾`, Base II.2.1.M: the datum's pinned sheet lies in `e₁`,
so the detachment shrinks the `k₁` block. -/
structure FirstMember (profile : W2R2SourceProfile.SourceProfile data star block)
    extends DetachData profile where
  pin_first : (endpointPartition profile).Rel (firstSheet profile) (pinSheet profile)

/-- Figure 34's `M⁽²⁾`, Base II.2.2.M: the datum's pinned sheet lies in `e₂`,
so the detachment shrinks the `k₂` block. -/
structure SecondMember (profile : W2R2SourceProfile.SourceProfile data star block)
    extends DetachData profile where
  pin_second : (endpointPartition profile).Rel (secondSheet profile) (pinSheet profile)

/-- **Exactly one of the two detachment members is available over a given
datum.**  Which one is decided by the datum, through the endpoint block that
holds the dangling sheet. -/
theorem exists_firstMember_or_secondMember (shape : Shape profile) :
    Nonempty (FirstMember profile) ∨ Nonempty (SecondMember profile) := by
  obtain ⟨detach⟩ := exists_detachData shape
  rcases pinSheet_mem shape with hFirst | hSecond
  · exact Or.inl ⟨⟨detach, hFirst⟩⟩
  · exact Or.inr ⟨⟨detach, hSecond⟩⟩

/-- ... and never both. -/
theorem not_firstMember_and_secondMember (first : FirstMember profile)
    (second : SecondMember profile) : False :=
  not_first_and_second first.pin_first second.pin_second

/-! ## `M⁽¹⁾` and `M⁽²⁾` never resolve the same datum -/

/-- **The detached sheet is not a parameter.**  The `t₃` exterior refinement of
a two-sided detachment forces it to be the pinned sheet: the retained endpoint
must isolate it, and `e₄` is the only occurrence above `t₃` that isolates a
sheet of `A₀`. -/
theorem transfer_eq_pinSheet (shape : Shape profile) (transfer remainder : Fin degree)
    (hne : transfer ≠ remainder)
    (hWallTogether : (data.vertexPartition wall).Rel transfer remainder)
    (hTransfer : (data.vertexPartition wall).Rel block.1 transfer)
    (hRefines : (data.edgePartition (star.edge profile.singleLabel)).Refines
      ((data.vertexPartition wall).detachSheet transfer remainder hne hWallTogether)) :
    transfer = pinSheet profile :=
  eq_pinSheet_of_block_singleton shape transfer hTransfer
    (SheetPartition.block_eq_singleton_of_refines hRefines transfer
      ((data.vertexPartition wall).detachSheet_block_single transfer remainder hne
        hWallTogether))

/-- **No `w2Mkk` gluing datum carries both detachment members of Figure 34.**
Stated against `GlobalMkk.Geometry`'s own fields, with both members on the
genus-preserving two-sided shape: each member's `t₃` exterior refinement pins
its own detached sheet, so `geometry.first = pinSheet = geometry.second`,
which `geometry.separate` forbids.  Consequently `GlobalMkk.candidates` has no
instance at an actual `w2Mkk` source profile with the genus-preserving shape,
and `GlobalMkk` takes one member over the branch-swapped datum instead, as
`GlobalM1k` does. -/
theorem no_common_geometry (shape : Shape profile)
    (geometry : GlobalMkk.Geometry data wall)
    (hBlock : (data.vertexPartition wall).Rel block.1 geometry.first)
    (hFirst : (data.edgePartition (star.edge profile.singleLabel)).Refines
      (ResolutionMkk.bothDetachedResolution (data.vertexPartition wall) geometry.endpoint
        geometry.first geometry.firstRemainder geometry.first_ne
        (geometry.endpoint_refines.rel geometry.first_together) geometry.first_together
        geometry.endpoint_refines).right)
    (hSecond : (data.edgePartition (star.edge profile.singleLabel)).Refines
      (ResolutionMkk.bothDetachedResolution (data.vertexPartition wall) geometry.endpoint
        geometry.second geometry.secondRemainder geometry.second_ne
        (geometry.endpoint_refines.rel geometry.second_together) geometry.second_together
        geometry.endpoint_refines).right) : False := by
  have hFirstPin := transfer_eq_pinSheet shape geometry.first geometry.firstRemainder
    geometry.first_ne (geometry.endpoint_refines.rel geometry.first_together) hBlock hFirst
  have hSecondPin := transfer_eq_pinSheet shape geometry.second geometry.secondRemainder
    geometry.second_ne (geometry.endpoint_refines.rel geometry.second_together)
    (hBlock.trans geometry.wall_together) hSecond
  apply geometry.separate
  rw [hFirstPin, hSecondPin]
  exact (geometry.endpoint.rel_iff _ _).mpr rfl

end Members

/-! ## The obstruction is a gauge

A branch swap along the `t₂` branch fixes the wall partition and fixes the `t₃`
occurrence partition -- hence fixes *which* sheet is pinned -- and relabels the
`t₂` occurrence partition by the transposition.  So which of the two endpoint
blocks contains the pinned sheet, and therefore which of `M⁽¹⁾`, `M⁽²⁾` the
datum admits, is not an invariant: it is exactly what the swap moves.  Unlike
`W2M1kSourceCandidates`, the separation is not carried as a hypothesis here; it
is discharged from the two standing target hypotheses. -/

section Gauge

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

theorem edge_incident (twoStar : TwoStar target wall) (label : Fin 2) :
    ((twoStar.edge label : target.V × target.V).1 = wall ∨
      (twoStar.edge label : target.V × target.V).2 = wall) := by
  simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
    true_and] using twoStar.edge_mem_incidentEdges label

/-- **The separation is a theorem, not a hypothesis.**  On the connected
genus-zero targets of the programme the `t₂` branch does not move the `t₃`
occurrence. -/
theorem singleLabel_fixed (hConnected : graph_connected target) (hGenus : genus target = 0)
    (profile : W2R2SourceProfile.SourceProfile data star block) :
    TargetBranchRegion.edgeMoved wall
        (M11RemoteCandidates.branchRoot star profile.doubleLabel)
        (M11RemoteCandidates.branchRoot_ne star profile.doubleLabel)
        (star.edge profile.singleLabel) = false :=
  TargetSeparation.edgeMoved_eq_false hConnected hGenus
    (edge_incident star profile.doubleLabel) (edge_incident star profile.singleLabel)
    (star.edge_injective.ne profile.labels_ne)

/-- A branch swap is a gauge move: the swapped datum is valid whenever the
original is. -/
theorem branchSwapped_valid (input : W2SourceInput data star) (root : target.V)
    (hRoot : root ≠ wall) (p q : Fin degree)
    (hTogether : (data.vertexPartition wall).Rel p q) :
    (GlobalM11Arbitrary.SwappedDatum data wall root hRoot p q hTogether).Valid :=
  wallBranchSwap_preserves_valid data input.valid wall root hRoot p q hTogether

theorem branchSwapped_edgePartition_of_fixed (root : target.V) (hRoot : root ≠ wall)
    (p q : Fin degree) (hTogether : (data.vertexPartition wall).Rel p q)
    (edge : target.edges)
    (hFixed : TargetBranchRegion.edgeMoved wall root hRoot edge = false) :
    (GlobalM11Arbitrary.SwappedDatum data wall root hRoot p q hTogether).edgePartition
        edge = data.edgePartition edge := by
  change (data.edgePartition edge).relabel
    (GluingDatum.SheetRelabeling.togglePermutation
      (TargetBranchRegion.edgeMoved wall root hRoot edge) (Equiv.swap p q)) = _
  rw [hFixed]
  apply SheetPartition.ext_repr
  rfl

theorem branchSwapped_edgePartition_of_moved (root : target.V) (hRoot : root ≠ wall)
    (p q : Fin degree) (hTogether : (data.vertexPartition wall).Rel p q)
    (edge : target.edges)
    (hMoved : TargetBranchRegion.edgeMoved wall root hRoot edge = true) :
    (GlobalM11Arbitrary.SwappedDatum data wall root hRoot p q hTogether).edgePartition
        edge = (data.edgePartition edge).relabel (Equiv.swap p q) := by
  change (data.edgePartition edge).relabel
    (GluingDatum.SheetRelabeling.togglePermutation
      (TargetBranchRegion.edgeMoved wall root hRoot edge) (Equiv.swap p q)) = _
  rw [hMoved]
  rfl

/-- The branch swap always moves the occurrence it is taken across. -/
theorem doubleLabel_moved (profile : W2R2SourceProfile.SourceProfile data star block) :
    TargetBranchRegion.edgeMoved wall
        (M11RemoteCandidates.branchRoot star profile.doubleLabel)
        (M11RemoteCandidates.branchRoot_ne star profile.doubleLabel)
        (star.edge profile.doubleLabel) = true :=
  TargetSeparation.edgeMoved_self_eq_true (edge_incident star profile.doubleLabel)

/-- **The gauge check, run.**  Swapping the pinned sheet with any other sheet
of `A₀` across the `t₂` branch leaves the `t₃` occurrence partition untouched
-- so the pinned sheet is still the unique isolated one, and the case is still
M-kk -- while the pinned sheet's `t₂` endpoint block acquires the *other*
sheet's cardinality.  Choosing the other sheet inside the other endpoint block
therefore exchanges `k₁` and `k₂` at the pin, which is exactly the exchange of
Figure 34's `M⁽¹⁾` and `M⁽²⁾`.  The obstruction of `no_common_geometry` is
consequently a matter of gauge: `GlobalMkk` takes one member over a swapped
datum rather than changing the construction. -/
theorem branchSwap_moves_pinSheet (hConnected : graph_connected target)
    (hGenus : genus target = 0)
    (profile : W2R2SourceProfile.SourceProfile data star block) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    ((GlobalM11Arbitrary.SwappedDatum data wall
          (M11RemoteCandidates.branchRoot star profile.doubleLabel)
          (M11RemoteCandidates.branchRoot_ne star profile.doubleLabel)
          (pinSheet profile) other hOther).edgePartition
        (star.edge profile.singleLabel) =
      data.edgePartition (star.edge profile.singleLabel)) ∧
    ((GlobalM11Arbitrary.SwappedDatum data wall
          (M11RemoteCandidates.branchRoot star profile.doubleLabel)
          (M11RemoteCandidates.branchRoot_ne star profile.doubleLabel)
          (pinSheet profile) other hOther).edgePartition
        (star.edge profile.doubleLabel)).blockCard (pinSheet profile) =
      (endpointPartition profile).blockCard other := by
  refine ⟨branchSwapped_edgePartition_of_fixed _ _ _ _ _ _
    (singleLabel_fixed hConnected hGenus profile), ?_⟩
  rw [branchSwapped_edgePartition_of_moved _ _ _ _ _ _ (doubleLabel_moved profile)]
  have hCard := SheetPartition.relabel_blockCard
    (data.edgePartition (star.edge profile.doubleLabel))
    (Equiv.swap (pinSheet profile) other) other
  rw [Equiv.swap_apply_right] at hCard
  exact hCard

end Gauge

end DraismaVargas.LocalCases.W2MkkSourceCandidates
