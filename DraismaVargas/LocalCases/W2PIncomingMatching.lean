import DraismaVargas.LocalCases.W2PIncomingCensus
import DraismaVargas.LocalCases.W3Nd2IncomingMemberMatching

/-!
# Identifying the incoming `w2P` datum with a named Figure 35 member

Source: Draisma--Vargas Part I (arXiv:1909.12924), Section 6, Case
`{w2-r2-nd3-P}`, its Figure 35 and Equation (9).

`W2PIncomingCensus` settles the target side and the source census:

* the incoming wall is `(2,2)` -- the two leaf orientations are *impossible*
  at a `w2P` wall, so no hypothesis is added for them;
* every Figure 35 member has a `Placement`, and the retained end of each
  restores `doubleEnd` while its fresh end restores `singleEnd`;
* off `A₀` all three incoming partitions in sight are the whole wall block;
* above `A₀` the `t₃` endpoint carries the whole block, the contracted
  occurrence and the `t₂` endpoint induce the *same* two-class partition, and
  that partition is one of Figure 35's three fine partitions.

This module turns that into the three wall comparisons, the whole-cover
`SameBlocks` exhaustion, the normalization receipt, and the indexed member
exit.

## The orientation `IncomingMatchingCore` does not cover

`IncomingMatchingCore.wall_blocks_of_dictionary` takes

```
hURefines : (data.vertexPartition u).Refines (mergedPartition data a b)
hUJoined  : JoinedOnBlock (data.vertexPartition u) (mergedPartition data a b) root
```

and therefore compares the member's *retained* endpoint with the whole
distinguished class (`hLeftSelected` is stated against `mergedPartition`).
Figure 35 is the opposite way round: Base II.2 in Part I (Case `{w2-r2}`) puts
the two ends `A'`, `A''` of `e₁`, `e₂` above `u` and the single end `B` of `e₃`
above `v`, so **every**
Figure 35 member splits `A₀` in two at the retained end and keeps it whole at
the fresh end (`W2PSurvival.MemberShape.pasted_left_rel_iff_of_rel` is
`member.fine`, `pasted_right_eq` is the wall partition).  Neither shape in
`IncomingMatchingCore` applies.

`block_eq_of_split_dictionary` below supplies that shape, in the form all
three positions actually need: each comparison is against a *named* selected
partition and a *named* background partition, with nothing forced to be
`mergedPartition`.  The core's item H is the special case
`selectedLeft := mergedPartition`, `backgroundLeft := flagPartition`, and the
lemma would fit in `IncomingMatchingCore` beside it.

## What is proved, and what is assumed

Everything below is proved outright on the `w2P` bundle -- an honest incoming
full-dimensional presentation, the forest contraction of the single edge
between `a` and `b`, the two-star at the contracted wall, its W2 source input's
`w2P` profile with `W2PSourceCandidates.Shape`, and the classifier's
`background` field.  **Nothing is assumed**: in particular the selected-class
census is *derived* in `W2PIncomingCensus.exists_member_selected_blocks` rather
than hypothesised, because Cardinality P's `k₃ = |A₀|` pins the `t₃` endpoint
to a single class above `A₀` and the forest identity then turns the wall's
one unit of change at the `t₂` endpoint into `p = 2`.

The three members live over **one** datum (`W2PSourceCandidates.members_share_datum`),
so the family the exit hands to `IncomingMatchingCore.exists_member_normalization_of_family`
is a genuine `Fin 3` family of `BalancedGlobal.Candidate`s over
`contractDatum data hc hab hOne`, with no remote slot.
-/

namespace DraismaVargas.LocalCases.W2PIncomingMatching

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionRamification
open TargetExpansion ResolutionM11 FullDimensionalSource WallDegeneration
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open M11IncomingPartitions
open W2PSourceCandidates W2PSurvival
open IncomingMatchingCore
open W3Nd2IncomingMemberMatching (pasted NormalizedAgainst normalizedAgainst
  sameBlocks_of_wall_blocks)
open W2PIncomingCensus

/-! ## §1  The split wall comparison

This would fit in `IncomingMatchingCore`, beside `wall_blocks_of_dictionary`. -/

section Split

variable {degree : ℕ}

/-- **One wall position compared, with both halves named.**  Two partitions
that agree with one named partition on a distinguished class and with another
named partition off it are equal.  This is the whole content of
`IncomingMatchingCore.wall_blocks_of_dictionary` at one position, with neither
half forced to be the wall partition. -/
theorem block_eq_of_split_dictionary (wall : SheetPartition degree) (root : Fin degree)
    (selectedPart backgroundPart first second : SheetPartition degree)
    (hFirstSelected : ∀ sheet, wall.Rel root sheet →
      first.block sheet = selectedPart.block sheet)
    (hSecondSelected : ∀ sheet, wall.Rel root sheet →
      second.block sheet = selectedPart.block sheet)
    (hFirstBackground : ∀ sheet, ¬ wall.Rel root sheet →
      first.block sheet = backgroundPart.block sheet)
    (hSecondBackground : ∀ sheet, ¬ wall.Rel root sheet →
      second.block sheet = backgroundPart.block sheet)
    (sheet : Fin degree) : first.block sheet = second.block sheet := by
  by_cases hSheet : wall.Rel root sheet
  · exact (hFirstSelected sheet hSheet).trans (hSecondSelected sheet hSheet).symm
  · exact (hFirstBackground sheet hSheet).trans (hSecondBackground sheet hSheet).symm

/-- Membership in a block, read as a relation. -/
theorem mem_block_of_rel {Q : SheetPartition degree} {x y : Fin degree} (h : Q.Rel x y) :
    x ∈ Q.block y := (Q.mem_block_iff y x).mpr h.symm

theorem rel_of_mem_block {Q : SheetPartition degree} {x y : Fin degree} (h : x ∈ Q.block y) :
    Q.Rel x y := ((Q.mem_block_iff y x).mp h).symm

end Split


/-! ## §2  The member side of the three wall positions -/

section Member

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
  {selected : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
  (profile : W2R2SourceProfile.SourceProfile (contractDatum data hc hab hOne) star selected)
  (shape : Shape profile)

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest shape in
private theorem wall_rel {first second : Fin degree}
    (h : (mergedPartition data a b).Rel first second) :
    ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel first second := by
  rw [contractDatum_vertexPartition_merge data hc hab hOne]
  exact h

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest shape in
private theorem merged_rel {first second : Fin degree}
    (h : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel first second) :
    (mergedPartition data a b).Rel first second := by
  rw [← contractDatum_vertexPartition_merge data hc hab hOne]
  exact h

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest shape in
private theorem merged_block_eq (sheet : Fin degree) :
    ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block sheet =
      (mergedPartition data a b).block sheet :=
  congrFun (congrArg SheetPartition.block
    (contractDatum_vertexPartition_merge data hc hab hOne)) sheet

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest in
/-- Above `A₀` the member's retained end carries its own fine partition. -/
theorem member_left_selected (position : Fin 3) (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel selected.1 sheet) :
    (pasted (W2PCommonBalance.members profile shape position)).left.block sheet =
      (memberShape data hc hab hOne star profile shape position).fine.block sheet := by
  rw [← memberShape_candidate data hc hab hOne star profile shape position]
  ext other
  rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
  exact (memberShape data hc hab hOne star profile shape position).pasted_left_rel_iff_of_rel
    sheet other (wall_rel data hc hab hOne hSheet)

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest in
/-- Off `A₀` the member's retained end carries the whole wall block. -/
theorem member_left_background (position : Fin 3) (sheet : Fin degree)
    (hSheet : ¬ (mergedPartition data a b).Rel selected.1 sheet) :
    (pasted (W2PCommonBalance.members profile shape position)).left.block sheet =
      (mergedPartition data a b).block sheet := by
  rw [← memberShape_candidate data hc hab hOne star profile shape position,
    ← merged_block_eq data hc hab hOne]
  ext other
  rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
  exact (memberShape data hc hab hOne star profile shape position).pasted_left_rel_iff_of_not_rel
    sheet other (fun h ↦ hSheet (merged_rel data hc hab hOne h))

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest in
/-- The member's fresh end carries the whole wall block everywhere. -/
theorem member_right_block (position : Fin 3) (sheet : Fin degree) :
    (pasted (W2PCommonBalance.members profile shape position)).right.block sheet =
      (mergedPartition data a b).block sheet := by
  rw [← memberShape_candidate data hc hab hOne star profile shape position,
    ← merged_block_eq data hc hab hOne]
  exact congrFun (congrArg SheetPartition.block
    (memberShape data hc hab hOne star profile shape position).pasted_right_eq) sheet

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest in
/-- Above `A₀` the member's regrown occurrence carries its own fine partition. -/
theorem member_newEdge_selected (position : Fin 3) (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel selected.1 sheet) :
    (pasted (W2PCommonBalance.members profile shape position)).newEdge.block sheet =
      (memberShape data hc hab hOne star profile shape position).fine.block sheet := by
  rw [← memberShape_candidate data hc hab hOne star profile shape position]
  ext other
  rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
  exact (memberShape data hc hab hOne star profile shape position).pasted_newEdge_rel_iff_of_rel
    sheet other (wall_rel data hc hab hOne hSheet)

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest in
/-- Off `A₀` the member's regrown occurrence carries the whole wall block. -/
theorem member_newEdge_background (position : Fin 3) (sheet : Fin degree)
    (hSheet : ¬ (mergedPartition data a b).Rel selected.1 sheet) :
    (pasted (W2PCommonBalance.members profile shape position)).newEdge.block sheet =
      (mergedPartition data a b).block sheet := by
  rw [← memberShape_candidate data hc hab hOne star profile shape position,
    ← merged_block_eq data hc hab hOne]
  ext other
  rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
  exact (memberShape data hc hab hOne star profile shape
    position).pasted_newEdge_rel_iff_of_not_rel sheet other
    (fun h ↦ hSheet (merged_rel data hc hab hOne h))

end Member


/-! ## §3  The three wall comparisons and the whole-cover exhaustion -/

section Matching

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
  {selected : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
  (profile : W2R2SourceProfile.SourceProfile (contractDatum data hc hab hOne) star selected)
  (shape : Shape profile)
  (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
    other ≠ selected →
      (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)

include fullDim hForest shape hBackground

/-- Every Figure 35 member has a placement, in the form `sameBlocks_of_wall_blocks`
consumes it. -/
theorem members_placement (position : Fin 3) :
    Placement hc hab hOne (W2PCommonBalance.members profile shape position).right := by
  rw [members_right data hc hab hOne star profile shape position]
  exact member_placement data hc hab hOne fullDim hForest star profile shape hBackground

/-- **The retained end of every Figure 35 member restores `doubleEnd`, and its
fresh end restores `singleEnd`** -- in both orientations at once. -/
theorem transported_endpoints (side : (contract target hab hOne).edges → Bool)
    (hSide : side = (orientedStar profile).right)
    (hPlacement : Placement hc hab hOne side) :
    (GluingTransport.transport (M11IncomingTargetNormalization.incomingIso hc hab hOne
          side hPlacement) data).vertexPartition
        (oldVertex (contract target hab hOne) ⟨a, hab⟩) =
      data.vertexPartition (doubleEnd data hc hab hOne star profile) ∧
    (GluingTransport.transport (M11IncomingTargetNormalization.incomingIso hc hab hOne
          side hPlacement) data).vertexPartition
        (freshVertex (contract target hab hOne)) =
      data.vertexPartition (singleEnd data hc hab hOne star profile) := by
  classical
  subst hSide
  have hPair := M11IncomingOuterPartitions.transported_endpointPartitions data hc hab hOne
    (orientedStar profile).right hPlacement
  by_cases hSupport : ∀ edge ∈ GluingDatum.incidentEdges
      (target := contract target hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne edge = (orientedStar profile).right edge
  · have hFalse := (support_iff data hc hab hOne fullDim hForest star profile shape
      hBackground).mp hSupport
    rw [if_pos hSupport] at hPair
    rw [doubleEnd_of_false data hc hab hOne star profile hFalse,
      singleEnd_of_false data hc hab hOne star profile hFalse]
    exact ⟨congrArg Prod.fst hPair, congrArg Prod.snd hPair⟩
  · have hTrue : IncomingTargetExpansion.right hc hab hOne
        (star.edge profile.doubleLabel) = true := by
      by_contra hContra
      have hFalse : IncomingTargetExpansion.right hc hab hOne
          (star.edge profile.doubleLabel) = false := by simpa using hContra
      exact hSupport ((support_iff data hc hab hOne fullDim hForest star profile shape
        hBackground).mpr hFalse)
    rw [if_neg hSupport] at hPair
    rw [doubleEnd_of_true data hc hab hOne star profile hTrue,
      singleEnd_of_true data hc hab hOne star profile hTrue]
    exact ⟨congrArg Prod.fst hPair, congrArg Prod.snd hPair⟩

/-- **The three wall comparisons of one Figure 35 member**, given the
selected-class census at that member.  Off `A₀` all six partitions are the
whole wall block; above it the `t₂` endpoint and the contracted occurrence
carry the member's fine partition and the `t₃` endpoint carries the whole
block. -/
theorem wall_blocks (position : Fin 3)
    (hCensus : ∀ sheet : Fin degree, (mergedPartition data a b).Rel selected.1 sheet →
      (data.vertexPartition (doubleEnd data hc hab hOne star profile)).block sheet =
        (memberShape data hc hab hOne star profile shape position).fine.block sheet) :
    (∀ sheet, ((GluingTransport.transport (M11IncomingTargetNormalization.incomingIso hc hab hOne
          (W2PCommonBalance.members profile shape position).right
          (members_placement data hc hab hOne fullDim hForest star profile shape hBackground
            position)) data).vertexPartition
        (oldVertex (contract target hab hOne) ⟨a, hab⟩)).block sheet =
      (pasted (W2PCommonBalance.members profile shape position)).left.block sheet) ∧
    (∀ sheet, ((GluingTransport.transport (M11IncomingTargetNormalization.incomingIso hc hab hOne
          (W2PCommonBalance.members profile shape position).right
          (members_placement data hc hab hOne fullDim hForest star profile shape hBackground
            position)) data).vertexPartition
        (freshVertex (contract target hab hOne))).block sheet =
      (pasted (W2PCommonBalance.members profile shape position)).right.block sheet) ∧
    (∀ sheet, (data.edgePartition contracted).block sheet =
      (pasted (W2PCommonBalance.members profile shape position)).newEdge.block sheet) := by
  have hEnds := transported_endpoints data hc hab hOne fullDim hForest star profile shape
    hBackground (W2PCommonBalance.members profile shape position).right
    (members_right data hc hab hOne star profile shape position)
    (members_placement data hc hab hOne fullDim hForest star profile shape hBackground position)
  refine ⟨fun sheet ↦ ?_, fun sheet ↦ ?_, fun sheet ↦ ?_⟩
  · rw [hEnds.1]
    exact block_eq_of_split_dictionary (mergedPartition data a b) selected.1
      (memberShape data hc hab hOne star profile shape position).fine
      (mergedPartition data a b) _ _ hCensus
      (member_left_selected data hc hab hOne star profile shape position)
      (background_block_doubleEnd data hc hab hOne fullDim hForest star profile shape
        hBackground)
      (member_left_background data hc hab hOne star profile shape position) sheet
  · rw [hEnds.2]
    exact block_eq_of_split_dictionary (mergedPartition data a b) selected.1
      (mergedPartition data a b) (mergedPartition data a b)
      (data.vertexPartition (singleEnd data hc hab hOne star profile))
      (pasted (W2PCommonBalance.members profile shape position)).right
      (singleEnd_block data hc hab hOne fullDim hForest star profile shape hBackground)
      (fun sheet _ ↦ member_right_block data hc hab hOne star profile shape position sheet)
      (background_block_singleEnd data hc hab hOne fullDim hForest star profile shape
        hBackground)
      (fun sheet _ ↦ member_right_block data hc hab hOne star profile shape position sheet) sheet
  · exact block_eq_of_split_dictionary (mergedPartition data a b) selected.1
      (memberShape data hc hab hOne star profile shape position).fine
      (mergedPartition data a b) _ _
      (fun sheet hSheet ↦ (contracted_block_eq_doubleEnd_block data hc hab hOne fullDim hForest
        star profile shape hBackground sheet hSheet).trans (hCensus sheet hSheet))
      (member_newEdge_selected data hc hab hOne star profile shape position)
      (background_block_contracted data hc hab hOne fullDim hForest star profile shape
        hBackground)
      (member_newEdge_background data hc hab hOne star profile shape position) sheet


/-! ## §4  The whole-cover exhaustion, the receipt, and the indexed exit -/

/-- **The incoming cover is the member's, partition by partition.**  The three
wall comparisons feed `W3Nd2IncomingMemberMatching.sameBlocks_of_wall_blocks`,
which performs the vertex/occurrence exhaustion once. -/
theorem sameBlocks (position : Fin 3)
    (hCensus : ∀ sheet : Fin degree, (mergedPartition data a b).Rel selected.1 sheet →
      (data.vertexPartition (doubleEnd data hc hab hOne star profile)).block sheet =
        (memberShape data hc hab hOne star profile shape position).fine.block sheet) :
    (∀ vertex, ((GluingTransport.transport (memberTargetIso data hc hab hOne
          (W2PCommonBalance.members profile shape position)
          (members_placement data hc hab hOne fullDim hForest star profile shape hBackground
            position)) data).vertexPartition vertex).SameBlocks
        ((W2PCommonBalance.members profile shape position).datum.vertexPartition vertex)) ∧
    (∀ edge, ((GluingTransport.transport (memberTargetIso data hc hab hOne
          (W2PCommonBalance.members profile shape position)
          (members_placement data hc hab hOne fullDim hForest star profile shape hBackground
            position)) data).edgePartition edge).SameBlocks
        ((W2PCommonBalance.members profile shape position).datum.edgePartition edge)) := by
  have hWall := wall_blocks data hc hab hOne fullDim hForest star profile shape hBackground
    position hCensus
  exact sameBlocks_of_wall_blocks data hc hab hOne fullDim.targetConnected fullDim.targetGenus
    (W2PCommonBalance.members profile shape position)
    (members_placement data hc hab hOne fullDim hForest star profile shape hBackground position)
    hWall.1 hWall.2.1 hWall.2.2

theorem vertexPartitions_sameBlocks (position : Fin 3)
    (hCensus : ∀ sheet : Fin degree, (mergedPartition data a b).Rel selected.1 sheet →
      (data.vertexPartition (doubleEnd data hc hab hOne star profile)).block sheet =
        (memberShape data hc hab hOne star profile shape position).fine.block sheet) :
    ∀ vertex, ((GluingTransport.transport (memberTargetIso data hc hab hOne
        (W2PCommonBalance.members profile shape position)
        (members_placement data hc hab hOne fullDim hForest star profile shape hBackground
          position)) data).vertexPartition vertex).SameBlocks
      ((W2PCommonBalance.members profile shape position).datum.vertexPartition vertex) :=
  (sameBlocks data hc hab hOne fullDim hForest star profile shape hBackground position
    hCensus).1

theorem edgePartitions_sameBlocks (position : Fin 3)
    (hCensus : ∀ sheet : Fin degree, (mergedPartition data a b).Rel selected.1 sheet →
      (data.vertexPartition (doubleEnd data hc hab hOne star profile)).block sheet =
        (memberShape data hc hab hOne star profile shape position).fine.block sheet) :
    ∀ edge, ((GluingTransport.transport (memberTargetIso data hc hab hOne
        (W2PCommonBalance.members profile shape position)
        (members_placement data hc hab hOne fullDim hForest star profile shape hBackground
          position)) data).edgePartition edge).SameBlocks
      ((W2PCommonBalance.members profile shape position).datum.edgePartition edge) :=
  (sameBlocks data hc hab hOne fullDim hForest star profile shape hBackground position
    hCensus).2

/-! ### The selector: the class of the dangling sheet at the `t₂` endpoint

Figure 35's three members differ exactly in what the dangling sheet `e₄` does
at `u`: `M⁽¹⁾` joins it to `e₁`, `M⁽²⁾` to `e₂`, and `M⁽³⁾` leaves it
alone.  That class is therefore a faithful selector for the family,
and the census produces its value. -/

/-- The class of the dangling sheet at the incoming `t₂` endpoint. -/
noncomputable def danglingClass : Finset (Fin degree) :=
  (data.vertexPartition (doubleEnd data hc hab hOne star profile)).block (extraSheet profile)

/-- The same class in each Figure 35 member. -/
noncomputable def memberDanglingClass (position : Fin 3) : Finset (Fin degree) :=
  (memberShape data hc hab hOne star profile shape position).fine.block (extraSheet profile)

omit fullDim hForest hBackground in
/-- **The three members are told apart by the dangling sheet's class.** -/
theorem memberDanglingClass_injective :
    Function.Injective
      (memberDanglingClass data hc hab hOne star profile shape) := by
  have hFirst : (firstShape shape).fine.Rel (firstSheet profile) (extraSheet profile) :=
    mergeShape_fine_rel_extra profile.first (first_extra_separate shape)
  have hFirstNotSecond : ¬ (firstShape shape).fine.Rel (secondSheet profile)
      (extraSheet profile) := fun h ↦ mergeShape_fine_not_rel profile.first profile.second
    (first_extra_separate shape) (second_extra_separate shape) (first_second_separate profile)
    (hFirst.trans h.symm)
  have hSecond : (secondShape shape).fine.Rel (secondSheet profile) (extraSheet profile) :=
    mergeShape_fine_rel_extra profile.second (second_extra_separate shape)
  have hSecondNotFirst : ¬ (secondShape shape).fine.Rel (firstSheet profile)
      (extraSheet profile) := fun h ↦ mergeShape_fine_not_rel profile.second profile.first
    (second_extra_separate shape) (first_extra_separate shape)
    (fun h' ↦ first_second_separate profile h'.symm) (hSecond.trans h.symm)
  have hThirdFirst : ¬ (thirdShape shape).fine.Rel (firstSheet profile)
      (extraSheet profile) := thirdShape_fine_not_rel shape
  have hThirdSecond : ¬ (thirdShape shape).fine.Rel (secondSheet profile)
      (extraSheet profile) := by
    intro h
    refine hThirdFirst (((thirdFine_rel_iff shape (secondSheet profile)).mpr ⟨?_, ?_⟩).trans h)
    · exact secondSheet_rel profile
    · exact fun hEq ↦ extra_ne_second shape hEq.symm
  have hIndex : ∀ index : Fin 3, index = 0 ∨ index = 1 ∨ index = 2 := by decide
  intro first second hEq
  simp only [memberDanglingClass] at hEq
  rcases hIndex first with rfl | rfl | rfl <;> rcases hIndex second with rfl | rfl | rfl <;>
    simp only [memberShape_zero, memberShape_one, memberShape_two] at hEq ⊢
  · exact absurd (rel_of_mem_block (hEq ▸ mem_block_of_rel hFirst)) hSecondNotFirst
  · exact absurd (rel_of_mem_block (hEq ▸ mem_block_of_rel hFirst)) hThirdFirst
  · exact absurd (rel_of_mem_block (hEq ▸ mem_block_of_rel hSecond)) hFirstNotSecond
  · exact absurd (rel_of_mem_block (hEq ▸ mem_block_of_rel hSecond)) hThirdSecond
  · exact absurd (rel_of_mem_block (hEq.symm ▸ mem_block_of_rel hFirst)) hThirdFirst
  · exact absurd (rel_of_mem_block (hEq.symm ▸ mem_block_of_rel hSecond)) hThirdSecond

/-- **The census produces the selector's value.** -/
theorem exists_selector :
    ∃ position : Fin 3, danglingClass data hc hab hOne star profile =
      memberDanglingClass data hc hab hOne star profile shape position := by
  obtain ⟨position, hPosition⟩ := exists_member_selected_blocks data hc hab hOne fullDim
    hForest star profile shape hBackground
  exact ⟨position, hPosition (extraSheet profile)
    (merged_rel data hc hab hOne (extraSheet_rel profile))⟩

/-- **The selector decides the whole selected-class census.**  The dangling
sheet's class tells the three members apart, so knowing it at one sheet gives
the comparison at every sheet of `A₀`. -/
theorem census_of_selector (position : Fin 3)
    (hSelector : danglingClass data hc hab hOne star profile =
      memberDanglingClass data hc hab hOne star profile shape position) :
    ∀ sheet : Fin degree, (mergedPartition data a b).Rel selected.1 sheet →
      (data.vertexPartition (doubleEnd data hc hab hOne star profile)).block sheet =
        (memberShape data hc hab hOne star profile shape position).fine.block sheet := by
  obtain ⟨index, hIndex⟩ := exists_member_selected_blocks data hc hab hOne fullDim hForest
    star profile shape hBackground
  have hValue : memberDanglingClass data hc hab hOne star profile shape position =
      memberDanglingClass data hc hab hOne star profile shape index := by
    rw [← hSelector]
    exact hIndex (extraSheet profile) (merged_rel data hc hab hOne (extraSheet_rel profile))
  rw [memberDanglingClass_injective data hc hab hOne star profile shape hValue]
  exact hIndex

/-- **The incoming-member identification.**  An arbitrary incoming `w2P`
datum -- an honest full-dimensional presentation whose contraction of the
single edge between `a` and `b` is a forest, over a two-star at the contracted
wall with a Cardinality P source profile and the classifier's `background`
field -- *is* one of Figure 35's three members, with the literal `Option`
column dictionary and a normalization receipt.

The selector is the class of the dangling occurrence `e₄` at the incoming `t₂`
endpoint, which is exactly what Figure 35's three boxes differ in; all three
branches genuinely occur, and no leaf orientation has to be excluded by
hypothesis because `W2PIncomingCensus.divalent_endpoints` rules it out. -/
theorem exists_member_normalization :
    ∃ position : Fin 3,
      ∃ hSelector : danglingClass data hc hab hOne star profile =
          memberDanglingClass data hc hab hOne star profile shape position,
        (∀ column : Option (contract target hab hOne).edges,
            GluingTransport.edgeEquiv (memberTargetIso data hc hab hOne
                (W2PCommonBalance.members profile shape position)
                (members_placement data hc hab hOne fullDim hForest star profile shape
                  hBackground position))
              (M11IncomingCoordinates.incomingColumnEquiv hc hab hOne column) =
            occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
              (W2PCommonBalance.members profile shape position).right column) ∧
          NormalizedAgainst data fullDim
            (memberTargetIso data hc hab hOne
              (W2PCommonBalance.members profile shape position)
              (members_placement data hc hab hOne fullDim hForest star profile shape
                hBackground position))
            (W2PCommonBalance.members profile shape position).datum
            (vertexPartitions_sameBlocks data hc hab hOne fullDim hForest star profile shape
              hBackground position
              (census_of_selector data hc hab hOne fullDim hForest star profile shape
                hBackground position hSelector))
            (edgePartitions_sameBlocks data hc hab hOne fullDim hForest star profile shape
              hBackground position
              (census_of_selector data hc hab hOne fullDim hForest star profile shape
                hBackground position hSelector)) :=
  exists_member_normalization_of_family data hc hab hOne fullDim.targetConnected
    fullDim.targetGenus (W2PCommonBalance.members profile shape)
    (danglingClass data hc hab hOne star profile)
    (memberDanglingClass data hc hab hOne star profile shape)
    (exists_selector data hc hab hOne fullDim hForest star profile shape hBackground)
    (fun position _ ↦ members_placement data hc hab hOne fullDim hForest star profile shape
      hBackground position)
    (fun position hSelector ↦ NormalizedAgainst data fullDim
      (memberTargetIso data hc hab hOne (W2PCommonBalance.members profile shape position)
        (members_placement data hc hab hOne fullDim hForest star profile shape hBackground
          position))
      (W2PCommonBalance.members profile shape position).datum
      (vertexPartitions_sameBlocks data hc hab hOne fullDim hForest star profile shape
        hBackground position
        (census_of_selector data hc hab hOne fullDim hForest star profile shape hBackground
          position hSelector))
      (edgePartitions_sameBlocks data hc hab hOne fullDim hForest star profile shape
        hBackground position
        (census_of_selector data hc hab hOne fullDim hForest star profile shape hBackground
          position hSelector)))
    (fun _ _ ↦ normalizedAgainst data fullDim _ _ _ _)

end Matching

end DraismaVargas.LocalCases.W2PIncomingMatching
