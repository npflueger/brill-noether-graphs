import DraismaVargas.LocalCases.W2R1IncomingCensus

/-!
# Identifying the incoming `{w2-r1}` datum with a named Figure 37/38 member

Source: Draisma--Vargas Part I, case `{w2-r1}`, Figures 37 and 38 and
**Equation (10)**.

`W2R1IncomingCensus` settles the target side and the source census:

* the incoming wall is `(2,2)` with `ch u = ch v = 1` -- the two leaf
  orientations are *impossible* at a `{w2-r1}` wall, so no hypothesis is added
  for them;
* both members have a `Placement`, and they share the star's own side
  predicate, so the old wall end restores the direction-`0` endpoint and the
  fresh end the direction-`1` endpoint;
* off **both** `A₀` and `B₀` all partitions in sight are the whole wall block;
* above each block the census is the single number `p ∈ {1, 2}`, and
  `exists_member_selected_counts` couples the two blocks' numbers into one
  member index `q : Fin 2` -- Part I's `δ⁽ᵠ⁾(Ã) ≠ δ⁽ᵠ⁾(B̃)` in the proof of
  Equation (*) for case `{w2-r1}`.

This module turns that into the two wall comparisons, the whole-cover
`SameBlocks` exhaustion, the normalization receipt, and the indexed member
exit.

## A two-block wall comparison

`IncomingMatchingCore.wall_blocks_of_dictionary` and its `_of_joined` variant
compare **one** distinguished class against the member's pasted resolution
and put everything else in a single background bucket.
`W2PIncomingMatching.block_eq_of_split_dictionary` -- one position, two
*named* partitions, no `Refines`/`JoinedOnBlock` -- is the general
**one**-anchor shape, and `W2MkkIncomingMatching.wall_blocks_of_split_dictionary`
and `W3ShiftIncomingMatching.wall_blocks_of_free_dictionary` are variants of
the same thing.

None of the three fits here: a `{w2-r1}` member is **not** constant off one
distinguished class.  Its pasted resolution takes *three* different values --
one above `A₀`, a different one above `B₀`, and the whole wall block
elsewhere.  `block_eq_of_two_block_dictionary` below is the shape needed, and
it is the general one: `n` anchors, one named partition per anchor plus one
named background partition, and neither forced to be `mergedPartition`.  All
four one-anchor shapes above are its `n = 1` case; it would sit naturally in
`IncomingMatchingCore`, beside `wall_blocks_of_dictionary`.

## What is proved, and what is assumed

Everything below is proved outright on the `{w2-r1}` bundle -- an honest
incoming full-dimensional presentation, the forest contraction of the single
edge between `a` and `b`, the two-star at the contracted wall, and a
`W2R1SourceCandidates.Pair` for it, which is exactly the payload of
`IncomingSourceCases.W2.Classification.r1` (two distinct ramification-one
blocks with their literal profiles, plus the `background ∉ {A₀, B₀}` field).
**Nothing is assumed**: the `(2,2)` wall is `W2R1IncomingCensus.divalent_endpoints`
and the two-block selected census is
`W2R1IncomingCensus.exists_member_selected_counts`, both derived.

The two members live over **one** datum (`Pair.candidate`), so the family
`IncomingMatchingCore.exists_member_normalization_of_family` consumes is a
genuine `Fin 2` family of `BalancedGlobal.Candidate`s over
`contractDatum data hc hab hOne`, with no remote slot.
-/

namespace DraismaVargas.LocalCases.W2R1IncomingMatching

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionRamification
open W4Assembly W4StableSource StableLocalProperties
open W2R1Target SecondEquation FullDimensionalSource WallDegeneration
open TargetExpansion ResolutionM11
open W2R1SourceCandidates
open IncomingMatchingCore
open W3Nd2IncomingMemberMatching (pasted NormalizedAgainst normalizedAgainst
  sameBlocks_of_wall_blocks)
open W2R1IncomingCensus

/-! ## §1  The two-block wall comparison

These lemmas would sit naturally in `IncomingMatchingCore`, beside
`wall_blocks_of_dictionary`. -/

section Anchors

variable {degree : ℕ}

/-- **One wall position compared over a finite anchor set, with every half
named.**  Two partitions that agree with one named partition on each anchor's
class and with a common named partition off all of them are equal.  The
one-anchor shapes -- `IncomingMatchingCore.wall_blocks_of_dictionary`,
`W2PIncomingMatching.block_eq_of_split_dictionary`,
`W2MkkIncomingMatching.wall_blocks_of_split_dictionary` and
`W3ShiftIncomingMatching.wall_blocks_of_free_dictionary` -- are the case of a
one-element anchor set. -/
theorem block_eq_of_anchored_dictionary {ι : Type*} (wall : SheetPartition degree)
    (root : ι → Fin degree) (anchored : ι → Prop) [DecidablePred anchored]
    (selected : ι → SheetPartition degree) (backgroundPart first second : SheetPartition degree)
    (hFirstSelected : ∀ i, anchored i → ∀ sheet, wall.Rel (root i) sheet →
      first.block sheet = (selected i).block sheet)
    (hSecondSelected : ∀ i, anchored i → ∀ sheet, wall.Rel (root i) sheet →
      second.block sheet = (selected i).block sheet)
    (hFirstBackground : ∀ sheet, (∀ i, anchored i → ¬ wall.Rel (root i) sheet) →
      first.block sheet = backgroundPart.block sheet)
    (hSecondBackground : ∀ sheet, (∀ i, anchored i → ¬ wall.Rel (root i) sheet) →
      second.block sheet = backgroundPart.block sheet)
    (sheet : Fin degree) : first.block sheet = second.block sheet := by
  classical
  by_cases hSheet : ∃ i, anchored i ∧ wall.Rel (root i) sheet
  · obtain ⟨i, hi, hRel⟩ := hSheet
    exact (hFirstSelected i hi sheet hRel).trans (hSecondSelected i hi sheet hRel).symm
  · have hOff : ∀ i, anchored i → ¬ wall.Rel (root i) sheet :=
      fun i hi hRel ↦ hSheet ⟨i, hi, hRel⟩
    exact (hFirstBackground sheet hOff).trans (hSecondBackground sheet hOff).symm

/-- **The two-anchor instance**, in the shape `{w2-r1}`'s two ramification-one
blocks need it: one named partition above `A₀`, another above `B₀`, and one
named background partition off both. -/
theorem block_eq_of_two_block_dictionary (wall : SheetPartition degree)
    (rootFirst rootSecond : Fin degree)
    (selectedFirst selectedSecond backgroundPart first second : SheetPartition degree)
    (hFirstA : ∀ sheet, wall.Rel rootFirst sheet →
      first.block sheet = selectedFirst.block sheet)
    (hSecondA : ∀ sheet, wall.Rel rootFirst sheet →
      second.block sheet = selectedFirst.block sheet)
    (hFirstB : ∀ sheet, wall.Rel rootSecond sheet →
      first.block sheet = selectedSecond.block sheet)
    (hSecondB : ∀ sheet, wall.Rel rootSecond sheet →
      second.block sheet = selectedSecond.block sheet)
    (hFirstBackground : ∀ sheet, ¬ wall.Rel rootFirst sheet → ¬ wall.Rel rootSecond sheet →
      first.block sheet = backgroundPart.block sheet)
    (hSecondBackground : ∀ sheet, ¬ wall.Rel rootFirst sheet → ¬ wall.Rel rootSecond sheet →
      second.block sheet = backgroundPart.block sheet)
    (sheet : Fin degree) : first.block sheet = second.block sheet := by
  by_cases hFirstRel : wall.Rel rootFirst sheet
  · exact (hFirstA sheet hFirstRel).trans (hSecondA sheet hFirstRel).symm
  · by_cases hSecondRel : wall.Rel rootSecond sheet
    · exact (hFirstB sheet hSecondRel).trans (hSecondB sheet hSecondRel).symm
    · exact (hFirstBackground sheet hFirstRel hSecondRel).trans
        (hSecondBackground sheet hFirstRel hSecondRel).symm

end Anchors


/-! ## §2  The member's pasted wall partitions, in three regions

`Pair.resolution` is `joinedResolutionAt` off both blocks, `memberLocal δ(A₀) q`
above `A₀` and `memberLocal δ(B₀) (other q)` above `B₀`, and
`SheetPartition.paste_block` reads each off at its own sheet.  `localSide` and
`localNew` name the three partitions Figures 37 and 38 print. -/

section Member

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)

/-- The endpoint partition of a local resolution named by the wall direction it
carries: direction `0` is the retained (old) wall end, direction `1` the fresh
one. -/
noncomputable def resolutionSide (resolution : LocalResolution degree) (label : Fin 2) :
    SheetPartition degree :=
  if label = 0 then resolution.left else resolution.right

@[simp] theorem resolutionSide_zero (resolution : LocalResolution degree) :
    resolutionSide resolution 0 = resolution.left := if_pos rfl

@[simp] theorem resolutionSide_one (resolution : LocalResolution degree) :
    resolutionSide resolution 1 = resolution.right := by
  rw [resolutionSide, if_neg (by decide)]

/-- **What a member puts on side `label` above a block.**  `double` is the
block's doubled direction and `position` the member's own index: the block
stays whole in gluing I (`position = double`), and in gluing II the doubled
direction's endpoint carries that direction's own occurrence partition. -/
noncomputable def localSide (double position label : Fin 2) : SheetPartition degree :=
  if position = double then mergedPartition data a b
  else if label = double then data.edgePartition (wallOcc hc hab hOne star double)
  else mergedPartition data a b

/-- **What a member puts on the regrown occurrence above a block**: the whole
block in gluing I (`|e'| = k₃`), the doubled direction's partition in gluing II
(`|e'| = k₁`, `|e''| = k₂`). -/
noncomputable def localNew (double position : Fin 2) : SheetPartition degree :=
  if position = double then mergedPartition data a b
  else data.edgePartition (wallOcc hc hab hOne star double)

/-- **`memberLocal`'s endpoint partitions are `localSide`.** -/
theorem resolutionSide_memberLocal (double position label : Fin 2) :
    resolutionSide
        (memberLocal (contractDatum data hc hab hOne) star double position) label =
      localSide data hc hab hOne star double position label := by
  unfold localSide
  by_cases hPosition : position = double
  · rw [memberLocal_of_eq _ star hPosition, if_pos hPosition, resolutionSide]
    split <;> exact wallPartition_eq data hc hab hOne
  · rw [memberLocal_of_ne _ star hPosition, if_neg hPosition]
    by_cases hLabel : label = double
    · rw [if_pos hLabel, resolutionSide]
      by_cases hZero : label = 0
      · rw [if_pos hZero]
        exact (sideFine_left_of_zero (contractDatum data hc hab hOne) star
          (hLabel ▸ hZero)).trans (wallOcc_edgePartition data hc hab hOne star double).symm
      · rw [if_neg hZero]
        exact (sideFine_right_of_ne_zero (contractDatum data hc hab hOne) star
          (hLabel ▸ hZero)).trans (wallOcc_edgePartition data hc hab hOne star double).symm
    · rw [if_neg hLabel, resolutionSide]
      by_cases hZero : label = 0
      · have hDouble : double ≠ 0 := fun h ↦ hLabel (hZero.trans h.symm)
        rw [if_pos hZero, sideFine_left_of_ne_zero _ star hDouble]
        exact wallPartition_eq data hc hab hOne
      · have hDouble : double = 0 := by
          by_contra hContra
          exact hLabel (by omega)
        rw [if_neg hZero, sideFine_right_of_zero _ star hDouble]
        exact wallPartition_eq data hc hab hOne

/-- **`memberLocal`'s regrown partition is `localNew`.** -/
theorem memberLocal_newEdge_eq (double position : Fin 2) :
    (memberLocal (contractDatum data hc hab hOne) star double position).newEdge =
      localNew data hc hab hOne star double position := by
  unfold localNew
  by_cases hPosition : position = double
  · rw [memberLocal_of_eq _ star hPosition, if_pos hPosition]
    exact wallPartition_eq data hc hab hOne
  · rw [memberLocal_of_ne _ star hPosition, if_neg hPosition]
    exact sideFine_newEdge (contractDatum data hc hab hOne) star double

/-- The joined background shape's endpoint partitions. -/
theorem resolutionSide_joined (label : Fin 2) :
    resolutionSide
        (joinedResolutionAt ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩))
        label = mergedPartition data a b := by
  rw [resolutionSide]
  split <;> exact wallPartition_eq data hc hab hOne

end Member


/-! ## §3  The incoming side above one block, read against `localSide`

Four census facts, assembled into the two statements the wall comparison
consumes.  The parameter is the member index `q` and the receipt is the
block's own count from `W2R1IncomingCensus.exists_member_selected_counts`. -/

section IncomingSide

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
  (pair : Pair (contractDatum data hc hab hOne) star)
  {blk : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
  (profile : W2R1SourceProfile.OccurrenceProfile (contractDatum data hc hab hOne) star blk)

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest pair in
/-- **Both restored endpoints above one block, in one statement.** -/
theorem incoming_side_of_count (position : Fin 2)
    (hCount : doubleCount data hc hab hOne star profile =
      (if position = profile.doubleLabel then 1 else 2))
    (label : Fin 2) (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel blk.1 sheet) :
    (data.vertexPartition (endOf hc hab hOne star label)).block sheet =
      (localSide data hc hab hOne star profile.doubleLabel position label).block sheet := by
  unfold localSide
  by_cases hPosition : position = profile.doubleLabel
  · have hOneCount : doubleCount data hc hab hOne star profile = 1 := by
      rw [hCount, if_pos hPosition]
    rw [if_pos hPosition]
    by_cases hLabel : label = profile.doubleLabel
    · rw [hLabel]
      exact double_end_block_of_one data hc hab hOne star profile hOneCount sheet hSheet
    · rw [other_of_ne hLabel]
      exact single_end_block data hc hab hOne star profile sheet hSheet
  · have hTwoCount : doubleCount data hc hab hOne star profile = 2 := by
      rw [hCount, if_neg hPosition]
    rw [if_neg hPosition]
    by_cases hLabel : label = profile.doubleLabel
    · rw [if_pos hLabel, hLabel]
      exact double_end_block_of_two data hc hab hOne star profile hTwoCount sheet hSheet
    · rw [if_neg hLabel, other_of_ne hLabel]
      exact single_end_block data hc hab hOne star profile sheet hSheet

include fullDim hForest pair in
/-- **The contracted occurrence above one block, against `localNew`.** -/
theorem incoming_new_of_count (position : Fin 2)
    (hCount : doubleCount data hc hab hOne star profile =
      (if position = profile.doubleLabel then 1 else 2))
    (sheet : Fin degree) (hSheet : (mergedPartition data a b).Rel blk.1 sheet) :
    (data.edgePartition contracted).block sheet =
      (localNew data hc hab hOne star profile.doubleLabel position).block sheet := by
  have hContracted := contracted_block_eq data hc hab hOne fullDim hForest star pair profile
    sheet hSheet
  unfold localNew
  by_cases hPosition : position = profile.doubleLabel
  · have hOneCount : doubleCount data hc hab hOne star profile = 1 := by
      rw [hCount, if_pos hPosition]
    rw [if_pos hPosition]
    exact hContracted.trans
      (double_end_block_of_one data hc hab hOne star profile hOneCount sheet hSheet)
  · have hTwoCount : doubleCount data hc hab hOne star profile = 2 := by
      rw [hCount, if_neg hPosition]
    rw [if_neg hPosition]
    exact hContracted.trans
      (double_end_block_of_two data hc hab hOne star profile hTwoCount sheet hSheet)

end IncomingSide


/-! ## §4  The member side, in the three regions -/

section Pasted

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)

/-- The pasted endpoint partitions are read blockwise. -/
theorem pasted_side_block
    (C : BalancedGlobal.Candidate (contract target hab hOne) degree
      (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (label : Fin 2) (sheet : Fin degree) :
    (resolutionSide (pasted C) label).block sheet =
      (resolutionSide (C.resolution
        (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr sheet)) label).block
        sheet := by
  rw [resolutionSide, resolutionSide]
  split
  · exact SheetPartition.paste_block
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
      (fun anchor ↦ (C.resolution anchor).left)
      (fun anchor ↦ (C.contracts anchor).left_refines) sheet
  · exact SheetPartition.paste_block
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
      (fun anchor ↦ (C.resolution anchor).right)
      (fun anchor ↦ (C.contracts anchor).right_refines) sheet

/-- The pasted regrown partition is read blockwise. -/
theorem pasted_new_block
    (C : BalancedGlobal.Candidate (contract target hab hOne) degree
      (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (sheet : Fin degree) :
    (pasted C).newEdge.block sheet =
      (C.resolution
        (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr sheet)).newEdge.block
        sheet :=
  SheetPartition.paste_block ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
    (fun anchor ↦ (C.resolution anchor).newEdge)
    (fun anchor ↦ (C.resolution anchor).edge_refines_left.trans
      (C.contracts anchor).left_refines) sheet

variable (pair : Pair (contractDatum data hc hab hOne) star)

/-- Above `A₀` the member's endpoint partitions are `localSide` at `A₀`'s
doubled direction and the member's own position. -/
theorem pasted_side_first (position label : Fin 2) (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel pair.first.1 sheet) :
    (resolutionSide (pasted (pair.candidate position)) label).block sheet =
      (localSide data hc hab hOne star pair.firstProfile.doubleLabel position label).block
        sheet := by
  rw [pasted_side_block data hc hab hOne]
  have hRel : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel pair.first.1
      (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr sheet) :=
    (wall_rel_of_merged_rel data hc hab hOne hSheet).trans
      (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).rel_repr_right sheet)
  rw [show (pair.candidate position).resolution
      (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr sheet) =
      pair.resolution position
        (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr sheet) from rfl,
    pair.resolution_of_first position hRel, resolutionSide_memberLocal data hc hab hOne star]

/-- Above `B₀` the member's endpoint partitions are `localSide` at `B₀`'s
doubled direction and the **opposite** position. -/
theorem pasted_side_second (position label : Fin 2) (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel pair.second.1 sheet) :
    (resolutionSide (pasted (pair.candidate position)) label).block sheet =
      (localSide data hc hab hOne star pair.secondProfile.doubleLabel (other position) label).block
        sheet := by
  rw [pasted_side_block data hc hab hOne]
  have hRel : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel pair.second.1
      (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr sheet) :=
    (wall_rel_of_merged_rel data hc hab hOne hSheet).trans
      (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).rel_repr_right sheet)
  rw [show (pair.candidate position).resolution
      (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr sheet) =
      pair.resolution position
        (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr sheet) from rfl,
    pair.resolution_of_second position hRel, resolutionSide_memberLocal data hc hab hOne star]

/-- Off both blocks the member's endpoint partitions are the whole wall
block. -/
theorem pasted_side_background (position label : Fin 2) (sheet : Fin degree)
    (hOffFirst : ¬ (mergedPartition data a b).Rel pair.first.1 sheet)
    (hOffSecond : ¬ (mergedPartition data a b).Rel pair.second.1 sheet) :
    (resolutionSide (pasted (pair.candidate position)) label).block sheet =
      (mergedPartition data a b).block sheet := by
  rw [pasted_side_block data hc hab hOne]
  have hFirst : ¬ ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel pair.first.1
      (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr sheet) := by
    intro hRel
    exact hOffFirst (merged_rel_of_wall_rel data hc hab hOne
      (hRel.trans (((contractDatum data hc hab hOne).vertexPartition
        ⟨a, hab⟩).rel_repr_left sheet)))
  have hSecond : ¬ ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel pair.second.1
      (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr sheet) := by
    intro hRel
    exact hOffSecond (merged_rel_of_wall_rel data hc hab hOne
      (hRel.trans (((contractDatum data hc hab hOne).vertexPartition
        ⟨a, hab⟩).rel_repr_left sheet)))
  rw [show (pair.candidate position).resolution
      (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr sheet) =
      pair.resolution position
        (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr sheet) from rfl,
    pair.resolution_of_background position hFirst hSecond,
    resolutionSide_joined data hc hab hOne]

/-- Above `A₀` the member's regrown partition is `localNew` at `A₀`. -/
theorem pasted_new_first (position : Fin 2) (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel pair.first.1 sheet) :
    (pasted (pair.candidate position)).newEdge.block sheet =
      (localNew data hc hab hOne star pair.firstProfile.doubleLabel position).block sheet := by
  rw [pasted_new_block data hc hab hOne]
  have hRel : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel pair.first.1
      (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr sheet) :=
    (wall_rel_of_merged_rel data hc hab hOne hSheet).trans
      (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).rel_repr_right sheet)
  rw [show (pair.candidate position).resolution
      (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr sheet) =
      pair.resolution position
        (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr sheet) from rfl,
    pair.resolution_of_first position hRel, memberLocal_newEdge_eq data hc hab hOne star]

/-- Above `B₀` the member's regrown partition is `localNew` at `B₀`, with the
opposite position. -/
theorem pasted_new_second (position : Fin 2) (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel pair.second.1 sheet) :
    (pasted (pair.candidate position)).newEdge.block sheet =
      (localNew data hc hab hOne star pair.secondProfile.doubleLabel (other position)).block
        sheet := by
  rw [pasted_new_block data hc hab hOne]
  have hRel : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel pair.second.1
      (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr sheet) :=
    (wall_rel_of_merged_rel data hc hab hOne hSheet).trans
      (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).rel_repr_right sheet)
  rw [show (pair.candidate position).resolution
      (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr sheet) =
      pair.resolution position
        (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr sheet) from rfl,
    pair.resolution_of_second position hRel, memberLocal_newEdge_eq data hc hab hOne star]

/-- Off both blocks the member's regrown partition is the whole wall block. -/
theorem pasted_new_background (position : Fin 2) (sheet : Fin degree)
    (hOffFirst : ¬ (mergedPartition data a b).Rel pair.first.1 sheet)
    (hOffSecond : ¬ (mergedPartition data a b).Rel pair.second.1 sheet) :
    (pasted (pair.candidate position)).newEdge.block sheet =
      (mergedPartition data a b).block sheet := by
  rw [pasted_new_block data hc hab hOne]
  have hFirst : ¬ ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel pair.first.1
      (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr sheet) := by
    intro hRel
    exact hOffFirst (merged_rel_of_wall_rel data hc hab hOne
      (hRel.trans (((contractDatum data hc hab hOne).vertexPartition
        ⟨a, hab⟩).rel_repr_left sheet)))
  have hSecond : ¬ ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel pair.second.1
      (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr sheet) := by
    intro hRel
    exact hOffSecond (merged_rel_of_wall_rel data hc hab hOne
      (hRel.trans (((contractDatum data hc hab hOne).vertexPartition
        ⟨a, hab⟩).rel_repr_left sheet)))
  rw [show (pair.candidate position).resolution
      (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr sheet) =
      pair.resolution position
        (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr sheet) from rfl,
    pair.resolution_of_background position hFirst hSecond]
  exact congrFun (congrArg SheetPartition.block (wallPartition_eq data hc hab hOne)) sheet

end Pasted


/-! ## §5  The three wall comparisons and the whole-cover exhaustion -/

section Matching

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
  (pair : Pair (contractDatum data hc hab hOne) star)

include fullDim hForest in
/-- **One restored endpoint compared, over the two-block dictionary.** -/
theorem wall_blocks_side (position : Fin 2)
    (hFirstCount : doubleCount data hc hab hOne star pair.firstProfile.toOccurrenceProfile =
      (if position = pair.firstProfile.doubleLabel then 1 else 2))
    (hSecondCount : doubleCount data hc hab hOne star pair.secondProfile.toOccurrenceProfile =
      (if other position = pair.secondProfile.doubleLabel then 1 else 2))
    (label : Fin 2) (sheet : Fin degree) :
    (data.vertexPartition (endOf hc hab hOne star label)).block sheet =
      (resolutionSide (pasted (pair.candidate position)) label).block sheet :=
  block_eq_of_two_block_dictionary (mergedPartition data a b) pair.first.1 pair.second.1
    (localSide data hc hab hOne star pair.firstProfile.doubleLabel position label)
    (localSide data hc hab hOne star pair.secondProfile.doubleLabel (other position) label)
    (mergedPartition data a b) _ _
    (fun sheet hRel ↦ incoming_side_of_count data hc hab hOne star
      pair.firstProfile.toOccurrenceProfile position hFirstCount label sheet hRel)
    (fun sheet hRel ↦ pasted_side_first data hc hab hOne star pair position label sheet hRel)
    (fun sheet hRel ↦ incoming_side_of_count data hc hab hOne star
      pair.secondProfile.toOccurrenceProfile (other position) hSecondCount label sheet hRel)
    (fun sheet hRel ↦ pasted_side_second data hc hab hOne star pair position label sheet hRel)
    (fun _sheet hOffFirst hOffSecond ↦ background_block_endOf data hc hab hOne fullDim hForest
      star pair label hOffFirst hOffSecond)
    (fun sheet hOffFirst hOffSecond ↦ pasted_side_background data hc hab hOne star pair
      position label sheet hOffFirst hOffSecond)
    sheet

include fullDim hForest in
/-- **The contracted occurrence compared, over the two-block dictionary.** -/
theorem wall_blocks_new (position : Fin 2)
    (hFirstCount : doubleCount data hc hab hOne star pair.firstProfile.toOccurrenceProfile =
      (if position = pair.firstProfile.doubleLabel then 1 else 2))
    (hSecondCount : doubleCount data hc hab hOne star pair.secondProfile.toOccurrenceProfile =
      (if other position = pair.secondProfile.doubleLabel then 1 else 2))
    (sheet : Fin degree) :
    (data.edgePartition contracted).block sheet =
      (pasted (pair.candidate position)).newEdge.block sheet :=
  block_eq_of_two_block_dictionary (mergedPartition data a b) pair.first.1 pair.second.1
    (localNew data hc hab hOne star pair.firstProfile.doubleLabel position)
    (localNew data hc hab hOne star pair.secondProfile.doubleLabel (other position))
    (mergedPartition data a b) _ _
    (fun sheet hRel ↦ incoming_new_of_count data hc hab hOne fullDim hForest star pair
      pair.firstProfile.toOccurrenceProfile position hFirstCount sheet hRel)
    (fun sheet hRel ↦ pasted_new_first data hc hab hOne star pair position sheet hRel)
    (fun sheet hRel ↦ incoming_new_of_count data hc hab hOne fullDim hForest star pair
      pair.secondProfile.toOccurrenceProfile (other position) hSecondCount sheet hRel)
    (fun sheet hRel ↦ pasted_new_second data hc hab hOne star pair position sheet hRel)
    (fun _sheet hOffFirst hOffSecond ↦ background_block_contracted data hc hab hOne fullDim
      hForest star pair hOffFirst hOffSecond)
    (fun sheet hOffFirst hOffSecond ↦ pasted_new_background data hc hab hOne star pair
      position sheet hOffFirst hOffSecond)
    sheet

include fullDim hForest in
/-- **The three wall comparisons of one Equation (10) member**, given the
two-block selected census at that member. -/
theorem wall_blocks (position : Fin 2)
    (hFirstCount : doubleCount data hc hab hOne star pair.firstProfile.toOccurrenceProfile =
      (if position = pair.firstProfile.doubleLabel then 1 else 2))
    (hSecondCount : doubleCount data hc hab hOne star pair.secondProfile.toOccurrenceProfile =
      (if other position = pair.secondProfile.doubleLabel then 1 else 2)) :
    (∀ sheet, ((GluingTransport.transport (M11IncomingTargetNormalization.incomingIso hc hab hOne
          (pair.candidate position).right
          (members_placement data hc hab hOne fullDim star pair position)) data).vertexPartition
        (oldVertex (contract target hab hOne) ⟨a, hab⟩)).block sheet =
      (pasted (pair.candidate position)).left.block sheet) ∧
    (∀ sheet, ((GluingTransport.transport (M11IncomingTargetNormalization.incomingIso hc hab hOne
          (pair.candidate position).right
          (members_placement data hc hab hOne fullDim star pair position)) data).vertexPartition
        (freshVertex (contract target hab hOne))).block sheet =
      (pasted (pair.candidate position)).right.block sheet) ∧
    (∀ sheet, (data.edgePartition contracted).block sheet =
      (pasted (pair.candidate position)).newEdge.block sheet) := by
  have hEnds := transported_endpoints data hc hab hOne fullDim star pair
    (pair.candidate position).right (members_right data hc hab hOne star pair position)
    (members_placement data hc hab hOne fullDim star pair position)
  refine ⟨fun sheet ↦ ?_, fun sheet ↦ ?_, fun sheet ↦ ?_⟩
  · rw [hEnds.1, ← resolutionSide_zero (pasted (pair.candidate position))]
    exact wall_blocks_side data hc hab hOne fullDim hForest star pair position hFirstCount
      hSecondCount 0 sheet
  · rw [hEnds.2, ← resolutionSide_one (pasted (pair.candidate position))]
    exact wall_blocks_side data hc hab hOne fullDim hForest star pair position hFirstCount
      hSecondCount 1 sheet
  · exact wall_blocks_new data hc hab hOne fullDim hForest star pair position hFirstCount
      hSecondCount sheet

include fullDim hForest in
/-- **The incoming cover is the member's, partition by partition.**  The three
wall comparisons feed `W3Nd2IncomingMemberMatching.sameBlocks_of_wall_blocks`,
which performs the vertex/occurrence exhaustion once. -/
theorem sameBlocks (position : Fin 2)
    (hFirstCount : doubleCount data hc hab hOne star pair.firstProfile.toOccurrenceProfile =
      (if position = pair.firstProfile.doubleLabel then 1 else 2))
    (hSecondCount : doubleCount data hc hab hOne star pair.secondProfile.toOccurrenceProfile =
      (if other position = pair.secondProfile.doubleLabel then 1 else 2)) :
    (∀ vertex, ((GluingTransport.transport (memberTargetIso data hc hab hOne
          (pair.candidate position)
          (members_placement data hc hab hOne fullDim star pair position)) data).vertexPartition
        vertex).SameBlocks ((pair.candidate position).datum.vertexPartition vertex)) ∧
    (∀ edge, ((GluingTransport.transport (memberTargetIso data hc hab hOne
          (pair.candidate position)
          (members_placement data hc hab hOne fullDim star pair position)) data).edgePartition
        edge).SameBlocks ((pair.candidate position).datum.edgePartition edge)) := by
  have hWall := wall_blocks data hc hab hOne fullDim hForest star pair position hFirstCount
    hSecondCount
  exact sameBlocks_of_wall_blocks data hc hab hOne fullDim.targetConnected fullDim.targetGenus
    (pair.candidate position)
    (members_placement data hc hab hOne fullDim star pair position)
    hWall.1 hWall.2.1 hWall.2.2

include fullDim hForest in
theorem vertexPartitions_sameBlocks (position : Fin 2)
    (hFirstCount : doubleCount data hc hab hOne star pair.firstProfile.toOccurrenceProfile =
      (if position = pair.firstProfile.doubleLabel then 1 else 2))
    (hSecondCount : doubleCount data hc hab hOne star pair.secondProfile.toOccurrenceProfile =
      (if other position = pair.secondProfile.doubleLabel then 1 else 2)) :
    ∀ vertex, ((GluingTransport.transport (memberTargetIso data hc hab hOne
        (pair.candidate position)
        (members_placement data hc hab hOne fullDim star pair position)) data).vertexPartition
      vertex).SameBlocks ((pair.candidate position).datum.vertexPartition vertex) :=
  (sameBlocks data hc hab hOne fullDim hForest star pair position hFirstCount hSecondCount).1

include fullDim hForest in
theorem edgePartitions_sameBlocks (position : Fin 2)
    (hFirstCount : doubleCount data hc hab hOne star pair.firstProfile.toOccurrenceProfile =
      (if position = pair.firstProfile.doubleLabel then 1 else 2))
    (hSecondCount : doubleCount data hc hab hOne star pair.secondProfile.toOccurrenceProfile =
      (if other position = pair.secondProfile.doubleLabel then 1 else 2)) :
    ∀ edge, ((GluingTransport.transport (memberTargetIso data hc hab hOne
        (pair.candidate position)
        (members_placement data hc hab hOne fullDim star pair position)) data).edgePartition
      edge).SameBlocks ((pair.candidate position).datum.edgePartition edge) :=
  (sameBlocks data hc hab hOne fullDim hForest star pair position hFirstCount hSecondCount).2

end Matching


/-! ## §6  The selector, and the indexed member exit

Figures 37 and 38's two members differ in exactly one thing: which side of the
new edge `Ã` sits on.  The incoming datum's own answer is the number of classes
`A₀`'s doubled direction's endpoint induces above `A₀` -- `1` for gluing I and
`2` for gluing II -- so that number is a faithful selector, and Part I's
`δ⁽ᵠ⁾(Ã) ≠ δ⁽ᵠ⁾(B̃)` makes it decide `B₀` as well. -/

section Selector

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
  (pair : Pair (contractDatum data hc hab hOne) star)

/-- **`δ⁽ᵠ⁾(Ã)`, read off the incoming datum**: how many classes `A₀`'s doubled
direction's restored endpoint induces above `A₀`. -/
noncomputable def selector : ℕ := firstCount data hc hab hOne star pair

/-- The same number in each of Equation (10)'s two members. -/
noncomputable def memberSelector (position : Fin 2) : ℕ :=
  if position = pair.firstProfile.doubleLabel then 1 else 2

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest in
theorem selector_eq :
    selector data hc hab hOne star pair =
      doubleCount data hc hab hOne star pair.firstProfile.toOccurrenceProfile := rfl

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest in
theorem memberSelector_eq (position : Fin 2) :
    memberSelector data hc hab hOne star pair position =
      (if position = pair.firstProfile.doubleLabel then 1 else 2) := rfl

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest in
/-- **The two members are told apart by `δ⁽ᵠ⁾(Ã)`.** -/
theorem memberSelector_injective :
    Function.Injective (memberSelector data hc hab hOne star pair) := by
  intro x y hEq
  rw [memberSelector_eq, memberSelector_eq] at hEq
  by_cases hx : x = pair.firstProfile.doubleLabel
  · by_cases hy : y = pair.firstProfile.doubleLabel
    · rw [hx, hy]
    · rw [if_pos hx, if_neg hy] at hEq
      exact absurd hEq (by decide)
  · by_cases hy : y = pair.firstProfile.doubleLabel
    · rw [if_neg hx, if_pos hy] at hEq
      exact absurd hEq (by decide)
    · rw [other_of_ne hx, other_of_ne hy]

include fullDim hForest in
/-- **The census produces the selector's value.** -/
theorem exists_selector :
    ∃ position : Fin 2, selector data hc hab hOne star pair =
      memberSelector data hc hab hOne star pair position := by
  obtain ⟨position, hFirst, _⟩ :=
    exists_member_selected_counts data hc hab hOne fullDim hForest star pair
  exact ⟨position, hFirst⟩

include fullDim hForest in
/-- **The selector decides the census at *both* blocks.** -/
theorem census_of_selector (position : Fin 2)
    (hSelector : selector data hc hab hOne star pair =
      memberSelector data hc hab hOne star pair position) :
    doubleCount data hc hab hOne star pair.firstProfile.toOccurrenceProfile =
        (if position = pair.firstProfile.doubleLabel then 1 else 2) ∧
      doubleCount data hc hab hOne star pair.secondProfile.toOccurrenceProfile =
        (if other position = pair.secondProfile.doubleLabel then 1 else 2) := by
  obtain ⟨index, hFirst, hSecond⟩ :=
    exists_member_selected_counts data hc hab hOne fullDim hForest star pair
  rw [firstCount_eq] at hFirst
  rw [secondCount_eq] at hSecond
  have hValue : memberSelector data hc hab hOne star pair position =
      memberSelector data hc hab hOne star pair index := by
    rw [← hSelector, selector_eq, memberSelector_eq]
    exact hFirst
  rw [memberSelector_injective data hc hab hOne star pair hValue]
  exact ⟨hFirst, hSecond⟩

include fullDim hForest in
/-- **The incoming-member identification for `{w2-r1}`.**  An arbitrary incoming
`{w2-r1}` datum -- an honest full-dimensional presentation whose contraction of
the single edge between `a` and `b` is a forest, over a two-star at the
contracted wall with **two** ramification-one blocks carrying their own source
profiles and unramified background -- *is* one of Equation (10)'s two members,
with the literal `Option` column dictionary and a normalization receipt.

The selector is `δ⁽ᵠ⁾(Ã)`, the side of the new edge on which `A₀`'s branch
vertex sits; Part I's `ch u = ch v = 1` makes it determine `δ⁽ᵠ⁾(B̃)` too, so
the single index `position : Fin 2` names the datum at both blocks at once.
Both branches genuinely occur, and no leaf orientation has to be excluded by
hypothesis because `W2R1IncomingCensus.divalent_endpoints` rules it out. -/
theorem exists_member_normalization :
    ∃ position : Fin 2,
      ∃ hSelector : selector data hc hab hOne star pair =
          memberSelector data hc hab hOne star pair position,
        (∀ column : Option (contract target hab hOne).edges,
            GluingTransport.edgeEquiv (memberTargetIso data hc hab hOne
                (pair.candidate position)
                (members_placement data hc hab hOne fullDim star pair position))
              (M11IncomingCoordinates.incomingColumnEquiv hc hab hOne column) =
            occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
              (pair.candidate position).right column) ∧
          NormalizedAgainst data fullDim
            (memberTargetIso data hc hab hOne (pair.candidate position)
              (members_placement data hc hab hOne fullDim star pair position))
            (pair.candidate position).datum
            (vertexPartitions_sameBlocks data hc hab hOne fullDim hForest star pair position
              (census_of_selector data hc hab hOne fullDim hForest star pair position
                hSelector).1
              (census_of_selector data hc hab hOne fullDim hForest star pair position
                hSelector).2)
            (edgePartitions_sameBlocks data hc hab hOne fullDim hForest star pair position
              (census_of_selector data hc hab hOne fullDim hForest star pair position
                hSelector).1
              (census_of_selector data hc hab hOne fullDim hForest star pair position
                hSelector).2) :=
  exists_member_normalization_of_family data hc hab hOne fullDim.targetConnected
    fullDim.targetGenus (fun position ↦ pair.candidate position)
    (selector data hc hab hOne star pair)
    (memberSelector data hc hab hOne star pair)
    (exists_selector data hc hab hOne fullDim hForest star pair)
    (fun position _ ↦ members_placement data hc hab hOne fullDim star pair position)
    (fun position hSelector ↦ NormalizedAgainst data fullDim
      (memberTargetIso data hc hab hOne (pair.candidate position)
        (members_placement data hc hab hOne fullDim star pair position))
      (pair.candidate position).datum
      (vertexPartitions_sameBlocks data hc hab hOne fullDim hForest star pair position
        (census_of_selector data hc hab hOne fullDim hForest star pair position hSelector).1
        (census_of_selector data hc hab hOne fullDim hForest star pair position hSelector).2)
      (edgePartitions_sameBlocks data hc hab hOne fullDim hForest star pair position
        (census_of_selector data hc hab hOne fullDim hForest star pair position hSelector).1
        (census_of_selector data hc hab hOne fullDim hForest star pair position hSelector).2))
    (fun _ _ ↦ normalizedAgainst data fullDim _ _ _ _)

end Selector

end DraismaVargas.LocalCases.W2R1IncomingMatching
