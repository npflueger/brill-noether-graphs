module

public import DraismaVargas.LocalCases.W3ShiftSelectedCensus

@[expose] public section

/-!
# The `w3Shift` identification with the census discharged

Source: Draisma--Vargas Part I (arXiv:1909.12924), Section 6, Case
`{w3-r1-nd3-t2-(a>k₄)}`, its Figure 29 and Equation (3).

`W3ShiftIncomingMatching.exists_member_normalization` takes two named
hypotheses: the selected-block census `SelectedCensus` and the dichotomy
`∃ index, (selectedLeft, selectedRight, selectedNew) = shiftClasses shrink index`.
`W3ShiftSelectedCensus.exists_selectedCensus` proves the census on the
classifier's payload alone.  This file performs the join.

## What is unconditional, and what is not

* **Position II.b is completely unconditional.**  When the incoming cover is
  Figure 29's `k_α − 1` member on its own direction, the census *produces* the
  `W3ShiftSourceCandidates.ShrinkData` -- `HasShrinkSheet` is a theorem there,
  not a hypothesis -- and its transferred sheet is the cover's own.  The
  dichotomy is then `⟨0, rfl⟩`, and
  `exists_member_normalization_of_shrinkPosition` carries no census hypothesis
  at all.

* **Position II.a needs one displayed equation that the classifier does not
  carry**, and it concerns the *family*, not the census.
  `W3ShiftSourceCandidates.ShiftProfile.growPartition` is
  `mergeBlocks (e_α) movingAnchor (extraSheet)`, and an incoming Position II.a
  cover carries its own transferred sheet `y ∈ A₀ ∖ e_α`
  (`W3ShiftSelectedCensus.exists_selectedCensus`'s second alternative), so the
  dichotomy at index `1` holds **iff** `shift.extraSheet = y`.  The hypothesis is
  displayed as `hExtra` below and is discharged whenever `|A₀| = k_α + 1`
  (`extraSheet_eq_of_blockCard_eq_succ`).  In general it is removed by carrying
  the transferred sheet as data: `ShiftProfile.extraSheet` is the **field**
  `ShiftProfile.extra`, exactly as `ShrinkData.transfer` is, and
  `ShiftProfile.withExtra` installs the incoming cover's own `y`, after which
  `hExtra` is `rfl`.  `W3ShiftClosureFinal.exists_shiftProfile_census` is this
  file's `exists_shiftProfile_selectedCensus` with the sheet installed and
  `hExtra` gone.  Nothing in the census is missing: `selected_sheet_classes`
  determines `e_α ∪ {y}` on the nose.
-/

namespace DraismaVargas.LocalCases.W3ShiftClosureUnconditional

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4Assembly W4StableSource StableLocalProperties
open ThirdEquation W3R1SourceProfile FullDimensionalSource WallDegeneration
open TargetExpansion
open W3Nd2IncomingTargetPlacement (divalentOccurrence)
open W3ShiftSourceCandidates
open W3ShiftIncomingMatching (SelectedCensus shiftClasses)
open W3ShiftLimitRows (shiftMembers limitRows wallContribution)

noncomputable local instance {target : CFGraph} : DecidableEq target.edges :=
  Classical.decEq _

variable {target : CFGraph} {degree : ℕ} {a b : target.V}
  {contracted : target.edges}

/-! ## The two class triples, read off `shiftClasses` -/

section Triples

variable {wall : target.V} {data : GluingDatum target degree} {star : ThreeStar target wall}
  {input : W3SourceInput data star} {shift : ShiftProfile input}

/-- Position II.b's triple. -/
theorem shiftClasses_zero (shrink : ShrinkData shift) :
    shiftClasses shrink 0 =
      (data.edgePartition shift.movingTarget,
        (data.vertexPartition wall).detachSheet shrink.transfer shrink.remainder
          shrink.transfer_ne_remainder shrink.remainder_wall_rel,
        (data.edgePartition shift.movingTarget).detachSheet shrink.transfer
          shrink.remainder shrink.transfer_ne_remainder shrink.remainder_moving) := rfl

/-- Position II.a's triple. -/
theorem shiftClasses_one (shrink : ShrinkData shift) :
    shiftClasses shrink 1 =
      (shift.growPartition, data.vertexPartition wall, shift.growPartition) := rfl

/-- The dichotomy at index `0`, for free. -/
theorem dichotomy_zero (shrink : ShrinkData shift) :
    ∃ index : Fin 2, ((shiftClasses shrink 0).1, (shiftClasses shrink 0).2.1,
      (shiftClasses shrink 0).2.2) = shiftClasses shrink index :=
  ⟨0, rfl⟩

/-- **The grow member is pinned to one transferred sheet.**  With the incoming
cover's own sheet named, `growPartition` is its merge exactly when
`extraSheet` is that sheet. -/
theorem growPartition_eq_mergeBlocks (extra : Fin degree)
    (hSep : ¬(data.edgePartition shift.movingTarget).Rel shift.movingAnchor extra)
    (hExtra : shift.extraSheet = extra) :
    shift.growPartition =
      (data.edgePartition shift.movingTarget).mergeBlocks shift.movingAnchor extra hSep := by
  subst hExtra
  rfl

/-- The dichotomy at index `1`, on that one equation. -/
theorem dichotomy_one (shrink : ShrinkData shift) (extra : Fin degree)
    (hSep : ¬(data.edgePartition shift.movingTarget).Rel shift.movingAnchor extra)
    (hExtra : shift.extraSheet = extra) :
    ∃ index : Fin 2,
      (((data.edgePartition shift.movingTarget).mergeBlocks shift.movingAnchor extra hSep),
        data.vertexPartition wall,
        ((data.edgePartition shift.movingTarget).mergeBlocks shift.movingAnchor extra
          hSep)) = shiftClasses shrink index := by
  refine ⟨1, ?_⟩
  rw [shiftClasses_one shrink, growPartition_eq_mergeBlocks extra hSep hExtra]

/-- **When the case's own arithmetic settles `hExtra`.**  If the moving class
misses exactly one sheet of the distinguished wall block, the transferred sheet
of Position II.a is unique and `shift.extraSheet` is it. -/
theorem extraSheet_eq_of_blockCard_eq_succ (extra : Fin degree)
    (hExtraWall : (data.vertexPartition wall).Rel input.distinguishedBlock.1 extra)
    (hSep : ¬(data.edgePartition shift.movingTarget).Rel shift.movingAnchor extra)
    (hCard : (data.vertexPartition wall).blockCard input.distinguishedBlock.1 =
      data.sourceEdgeIndex shift.moving.1 + 1) :
    shift.extraSheet = extra := by
  classical
  have hSub : (data.edgePartition shift.movingTarget).block shift.movingAnchor ⊆
      (data.vertexPartition wall).block input.distinguishedBlock.1 := by
    intro sheet hSheet
    exact ((data.vertexPartition wall).mem_block_iff _ _).mpr
      (shift.movingAnchor_wall_rel.trans (shift.movingTarget_refines.rel
        (((data.edgePartition shift.movingTarget).mem_block_iff _ _).mp hSheet)))
  have hCardSdiff : (((data.vertexPartition wall).block input.distinguishedBlock.1) \
      ((data.edgePartition shift.movingTarget).block shift.movingAnchor)).card = 1 := by
    rw [Finset.card_sdiff_of_subset hSub]
    have hBlock : ((data.vertexPartition wall).block input.distinguishedBlock.1).card =
        ((data.edgePartition shift.movingTarget).block shift.movingAnchor).card + 1 := hCard
    omega
  obtain ⟨witness, hWitness⟩ := Finset.card_eq_one.mp hCardSdiff
  have hMemExtra : extra ∈ ((data.vertexPartition wall).block input.distinguishedBlock.1) \
      ((data.edgePartition shift.movingTarget).block shift.movingAnchor) :=
    Finset.mem_sdiff.mpr ⟨((data.vertexPartition wall).mem_block_iff _ _).mpr hExtraWall,
      fun h ↦ hSep (((data.edgePartition shift.movingTarget).mem_block_iff _ _).mp h)⟩
  have hMemChosen : shift.extraSheet ∈
      ((data.vertexPartition wall).block input.distinguishedBlock.1) \
      ((data.edgePartition shift.movingTarget).block shift.movingAnchor) :=
    Finset.mem_sdiff.mpr
      ⟨((data.vertexPartition wall).mem_block_iff _ _).mpr shift.extraSheet_wall_rel,
        fun h ↦ shift.extraSheet_separate
          (((data.edgePartition shift.movingTarget).mem_block_iff _ _).mp h)⟩
  rw [hWitness, Finset.mem_singleton] at hMemExtra hMemChosen
  rw [hMemChosen, hMemExtra]

end Triples

/-! ## The census on the classifier's payload -/

section Payload

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (hCompat : DanglingCompatible data hc hab hOne)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)

include fullDim hForest hCompat

/-- **The census on the classifier's payload.**  From
`W3IncomingClassification.Classification.shift`'s own payload -- an `Nd3Profile`
of the distinguished block with three distinct target directions and the
largest index below `|A₀|` -- an incoming `w3Shift` cover has a Figure 29
orientation whose moving direction is its own isolated one, satisfies
`W3ShiftClosure.RetainedBelow`, and displays a full selected-block census: it is
in Position II.b, where its own `ShrinkData` exists and the triple is
`shiftClasses _ 0`, or in Position II.a with its own transferred sheet. -/
theorem exists_shiftProfile_selectedCensus
    (profile : Nd3Profile (contractDatum data hc hab hOne) input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_lt : (contractDatum data hc hab hOne).sourceEdgeIndex profile.largest.1 <
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
        input.distinguishedBlock.1) :
    ∃ shift : ShiftProfile input,
      shift.movingTarget = divalentOccurrence data hc hab hOne fullDim star ∧
      W3ShiftClosure.RetainedBelow shift ∧
      ((∃ shrink : ShrinkData shift,
          SelectedCensus data hc hab hOne star input (shiftClasses shrink 0).1
            (shiftClasses shrink 0).2.1 (shiftClasses shrink 0).2.2) ∨
        (∃ extra : Fin degree, ∃ hSep : ¬((contractDatum data hc hab hOne).edgePartition
            shift.movingTarget).Rel shift.movingAnchor extra,
          ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
              input.distinguishedBlock.1 extra ∧
          SelectedCensus data hc hab hOne star input
            (((contractDatum data hc hab hOne).edgePartition
              shift.movingTarget).mergeBlocks shift.movingAnchor extra hSep)
            ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
            (((contractDatum data hc hab hOne).edgePartition
              shift.movingTarget).mergeBlocks shift.movingAnchor extra hSep))) := by
  obtain ⟨shift, hMoving, hRetained⟩ :=
    W3ShiftIncomingCensus.exists_shiftProfile_movingTarget_eq_divalent data hc hab hOne
      fullDim hForest hCompat star input profile directions largest_lt
  exact ⟨shift, hMoving, hRetained,
    W3ShiftSelectedCensus.exists_selectedCensus data hc hab hOne fullDim hForest hCompat
      star input shift hMoving⟩

end Payload

/-! ## The join: identification with `hCensus` discharged -/

section Join

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (shift : ShiftProfile input)
  (hMoving : shift.movingTarget = divalentOccurrence data hc hab hOne fullDim star)
  (shrink : ShrinkData shift)

include hForest hMoving

/-- **The identification for a Position II.b incoming cover, unconditional.**
Neither `hCensus` nor `hDichotomy` remains: the census is the classifier's, and
the index is `0` by `rfl`. -/
theorem exists_member_normalization_of_shrinkPosition
    (hCensus : SelectedCensus data hc hab hOne star input (shiftClasses shrink 0).1
      (shiftClasses shrink 0).2.1 (shiftClasses shrink 0).2.2) :
    ∃ index : Fin 2,
      ∃ hIndex : ((shiftClasses shrink 0).1, (shiftClasses shrink 0).2.1,
          (shiftClasses shrink 0).2.2) = shiftClasses shrink index,
        (∀ column : Option (contract target hab hOne).edges,
            GluingTransport.edgeEquiv
                (IncomingMatchingCore.memberTargetIso data hc hab hOne
                  (shiftMembers shrink index)
                  (W3ShiftIncomingMatching.shiftMembers_placement data hc hab hOne fullDim
                    star input shift hMoving shrink index))
                (M11IncomingCoordinates.incomingColumnEquiv hc hab hOne column) =
              TargetExpansion.occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
                (shiftMembers shrink index).right column) ∧
          W3Nd2IncomingMemberMatching.NormalizedAgainst data fullDim
            (IncomingMatchingCore.memberTargetIso data hc hab hOne
              (shiftMembers shrink index)
              (W3ShiftIncomingMatching.shiftMembers_placement data hc hab hOne fullDim
                star input shift hMoving shrink index))
            (shiftMembers shrink index).datum
            (W3ShiftIncomingMatching.shiftMembers_sameBlocks data hc hab hOne fullDim
              hForest star input shift hMoving shrink _ _ _ hCensus index hIndex).1
            (W3ShiftIncomingMatching.shiftMembers_sameBlocks data hc hab hOne fullDim
              hForest star input shift hMoving shrink _ _ _ hCensus index hIndex).2 :=
  W3ShiftIncomingMatching.exists_member_normalization data hc hab hOne fullDim hForest
    star input shift hMoving shrink _ _ _ hCensus (dichotomy_zero shrink)

/-- **The identification for a Position II.a incoming cover.**  The census is
the classifier's; the one displayed hypothesis `hExtra` is the grow member's
transferred sheet, discussed in this module's header. -/
theorem exists_member_normalization_of_growPosition
    (extra : Fin degree)
    (hSep : ¬((contractDatum data hc hab hOne).edgePartition shift.movingTarget).Rel
      shift.movingAnchor extra)
    (hCensus : SelectedCensus data hc hab hOne star input
      (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).mergeBlocks
        shift.movingAnchor extra hSep)
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
      (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).mergeBlocks
        shift.movingAnchor extra hSep))
    (hExtra : shift.extraSheet = extra) :
    ∃ index : Fin 2,
      ∃ hIndex : ((((contractDatum data hc hab hOne).edgePartition
            shift.movingTarget).mergeBlocks shift.movingAnchor extra hSep),
          ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩),
          (((contractDatum data hc hab hOne).edgePartition
            shift.movingTarget).mergeBlocks shift.movingAnchor extra hSep)) =
          shiftClasses shrink index,
        (∀ column : Option (contract target hab hOne).edges,
            GluingTransport.edgeEquiv
                (IncomingMatchingCore.memberTargetIso data hc hab hOne
                  (shiftMembers shrink index)
                  (W3ShiftIncomingMatching.shiftMembers_placement data hc hab hOne fullDim
                    star input shift hMoving shrink index))
                (M11IncomingCoordinates.incomingColumnEquiv hc hab hOne column) =
              TargetExpansion.occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
                (shiftMembers shrink index).right column) ∧
          W3Nd2IncomingMemberMatching.NormalizedAgainst data fullDim
            (IncomingMatchingCore.memberTargetIso data hc hab hOne
              (shiftMembers shrink index)
              (W3ShiftIncomingMatching.shiftMembers_placement data hc hab hOne fullDim
                star input shift hMoving shrink index))
            (shiftMembers shrink index).datum
            (W3ShiftIncomingMatching.shiftMembers_sameBlocks data hc hab hOne fullDim
              hForest star input shift hMoving shrink _ _ _ hCensus index hIndex).1
            (W3ShiftIncomingMatching.shiftMembers_sameBlocks data hc hab hOne fullDim
              hForest star input shift hMoving shrink _ _ _ hCensus index hIndex).2 :=
  W3ShiftIncomingMatching.exists_member_normalization data hc hab hOne fullDim hForest
    star input shift hMoving shrink _ _ _ hCensus
    (dichotomy_one shrink extra hSep hExtra)

end Join

end DraismaVargas.LocalCases.W3ShiftClosureUnconditional
