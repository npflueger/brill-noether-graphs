import DraismaVargas.LocalCases.NonTrivalentValencyTwoGauge
import DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitCandidate

/-!
# Part II, valency two, Configuration A: the **inclusion** alignment gauge of the split family

Source: Vargas, Part II (arXiv:2609.09109), §5.4, Configuration A of case
`{v2-nd4}` (case `{v2-nd4-t3}`), subcases `{v2-nd4-t3-k2=k3}` and
`{v2-nd4-t3-k2<k3}`: the Base II members in which one `t_thick`-class "splits
above `u` because `k_alpha > k_delta`", read against the diagrams of those
subcases.  Draisma--Vargas Part I, Case `{w2}`, fixes the base tree `T_2` (the
tree contracting to `T_0` with `val u = val v = 2`).

`NonTrivalentValencyTwoSplitCandidate` builds the split resolution and installs
it into the subdivision background of `NonTrivalentValencyTwoCandidate`, but
only from the receipt `SplitSetup`, whose clause

```text
sub : (data.edgePartition (thinEdge ...)).block delta ⊆
        (data.edgePartition (thickEdge ...)).block alpha
```

("the `t_thin`-class `e_delta` sits *inside* the `t_thick`-class `e_alpha` as a
set of sheets") is a statement about a *fixed* datum.  The paper's pictures
simply relabel the sheets so that it holds -- the diagrams of subcase
`{v2-nd4-t3-k2<k3}` re-order the sheets from one member to the next so that
`e_2 ⊆ e_4` -- and over a fixed datum that relabelling is a gauge: a
block-preserving branch swap on the `t_thin` side.  This module supplies that
gauge, in the **inclusion** form.
`NonTrivalentValencyTwoGauge.exists_alignment_perm` is the equal-size version
(it carries the two `t_thin`-classes *onto* the two `t_thick`-classes, which is
Base I); here only the small class has to land inside the large one, and the
hypothesis is the paper's strict inequality `k_delta < k_alpha`.

## What is proved

* `exists_perm_image_subset`, `exists_splitAlignment_perm`: the finite gauge
  move.  A subset of one wall block is carried inside a prescribed larger
  subset by a permutation fixing the block's complement pointwise and
  stabilizing the block.  The partition form lands `e_delta` inside
  `e_alpha ∖ {alpha}`, which is what makes the paper's bridge `e_alpha ∖ e_delta`
  nonempty, i.e. the receipt's `not_thin`.
* `IsSplitGauge`, `splitGaugePerm`, `splitRelabeling`, `splitGaugedData`,
  `splitGaugedAnchor`: the gauge applied on the `t_thin` branch through
  `BlockPreservingBranchSwap.branchSwapOfPerm` at the far endpoint of
  `star.edge 1`, exactly as in `NonTrivalentValencyTwoGauge`. `splitGaugePerm`
  is total: it is block-preserving for every datum and aligning as soon as an
  aligning permutation exists, so `splitGaugedData` needs no hypothesis. The
  wall partition and the `t_thick` partition are untouched
  (`splitGaugedData_vertexPartition_wall`, `splitGaugedData_edgePartition_zero`,
  the latter through `TargetSeparation.edgeMoved_eq_false`, which is where
  `graph_connected target` and `genus target = 0` enter); the `t_thin` partition
  is relabelled (`splitGaugedData_edgePartition_one`).
* `splitSurvivorEquiv`, `survivors_splitGauged`,
  `directionSurvivors_splitGauged`, `activeTargets_splitGauged`,
  `splitGaugedSource`: the transport of `TwoBranchAnchor`, of the survivor
  census and of Configuration A across the gauge
  (`NonTrivalentValencyTwoGauge.gaugedSource`, for the present permutation).
* `thickDirection_eq_zero`, `thickEdge_eq_zero`, `thinEdge_eq_one`:
  Configuration A pins the thick/thin dispatch of
  `NonTrivalentValencyTwoCandidate` to `star.edge 0` / `star.edge 1`.
* `splitSetup_gauged`: **the producer.**  From the four named survivors of
  Configuration A and the single numerical hypothesis
  `k_delta < k_alpha` (`NonTrivalentValencyTwoCandidate.sourceEdgeIndex_eq_blockCard`
  turns the block cardinalities into the paper's indices) the gauged datum
  carries `NonTrivalentValencyTwoSplitCandidate.SplitSetup`, so the split
  candidate and everything downstream of it live over the gauged wall datum --
  the `base` of the type-change link is the gauged datum, as at valency four
  and at Base I.
* `splitCandidate_newEdge_blockCard_piece`, `..._bridge`, `..._pass`: the three
  exact new-edge class sizes in the paper's indices -- piece `k_delta`, bridge
  `k_alpha - k_delta`, pass-through `k_beta` -- over any datum carrying a
  `SplitSetup`, hence in particular over the gauged one.
* `exists_splitCandidate_of_indices`: the packaged form, returning the
  candidate, the validity of its outgoing datum, its resolution at the anchor
  and the three partition identities relating the gauged datum to the incoming
  one.
* `splitModel_not_sub`, `splitModel_gauge_exists`, `splitModel_cards`,
  `splitModel_index_witness`: a literal five-sheet model in which the strict
  index inequality holds, the sub-alignment **fails**, and the gauge exists --
  so `IsSplitGauge` is inhabited and the gauge is not cosmetic.

## What is not proved -- the explicit hypotheses

1. `nonDanglingValency A = 4` at the wall block, Configuration A (the `2 + 2`
   survivor split, here the explicit `hSplit`) and the classifier
   `TwoBranchAnchor` are hypotheses about the *incoming* datum, exactly as in
   the other valency-two candidate modules; they are transported, not
   produced.
2. `graph_connected target`, `genus target = 0` and `data.Connected` are
   explicit: the first two separate the two star branches, the third is what
   makes pruning transport along a sheet relabelling.
3. The orientation: `NonTrivalentValencyTwoCandidate.rightAssignment` puts the
   thick direction at the divalent endpoint `u`, so this module realizes the
   splits of a class over `star.edge 0`.  The mirror members (a class over
   `star.edge 1` splitting) need the reversed subdivision background and are
   not built here.
4. No stable type, row census, dictionary, matrix, exit or tracking: those are
   the modules `NonTrivalentValencyTwoSplitRows`, `...SplitRowEquiv`,
   `...SplitRowDictionary`, `...SplitExit` and `...SplitTracks`.  In particular
   `k_delta < k_alpha` is used here only to produce the receipt; the
   *wall-metric* statement that this is the case that occurs is proved
   downstream.

## Consumers

`NonTrivalentValencyTwoSplitRows` and the rest of the split family, and the
valency-two type-change link (`NonTrivalentValencyTwoBaseOneLink`).
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitGauge

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BlockPreservingBranchSwap
open DraismaVargas.LocalCases.GlobalM11Arbitrary
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate.Prescribed
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoGauge (star_edge_incident
  exists_perm_matching_pair directionSurvivors_eq_pair pair_cover)
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.W3R1SourceProfile (survivors mem_survivors)
open DraismaVargas.LocalCases.NonTrivalentValencyThreeAnchor (activeTargets)
open DraismaVargas.LocalCases.W4Assembly DraismaVargas.LocalCases.W4StableSource

/-! ## 0.  The finite inclusion move -/

section Finite

variable {d : ℕ}

/-- **The inclusion gauge move.**  A subset of a finite `whole` is carried
inside any prescribed subset of `whole` of at least its size by a permutation
fixing the complement of `whole` pointwise and stabilizing `whole`. -/
theorem exists_perm_image_subset (whole small large : Finset (Fin d))
    (hSmall : small ⊆ whole) (hLarge : large ⊆ whole)
    (hCard : small.card ≤ large.card) :
    ∃ gauge : Equiv.Perm (Fin d),
      (∀ sheet, sheet ∉ whole → gauge sheet = sheet) ∧
        (∀ sheet ∈ whole, gauge sheet ∈ whole) ∧
          small.image gauge ⊆ large := by
  classical
  obtain ⟨image, hImageSub, hImageCard⟩ := Finset.exists_subset_card_eq hCard
  have hImageWhole : image ⊆ whole := hImageSub.trans hLarge
  have hUnionSmall : small ∪ (whole \ small) = whole := by
    rw [Finset.union_comm]
    exact Finset.sdiff_union_of_subset hSmall
  have hUnionImage : image ∪ (whole \ image) = whole := by
    rw [Finset.union_comm]
    exact Finset.sdiff_union_of_subset hImageWhole
  have hCardSmall : (whole \ small).card = (whole \ image).card := by
    rw [Finset.card_sdiff, Finset.card_sdiff, Finset.inter_eq_left.mpr hSmall,
      Finset.inter_eq_left.mpr hImageWhole, hImageCard]
  obtain ⟨gauge, hOutside, hInside, hFirst, _hSecond⟩ :=
    exists_perm_matching_pair whole small (whole \ small) image (whole \ image)
      hUnionSmall Finset.disjoint_sdiff hUnionImage Finset.disjoint_sdiff
      hImageCard.symm hCardSmall
  exact ⟨gauge, hOutside, hInside, hFirst ▸ hImageSub⟩

/-- **The inclusion alignment gauge, partition form.**  When the `thin` class of
`thinSheet` is strictly smaller than the `thick` class of `thickSheet`, a
block-preserving permutation carries the former inside the latter *and misses*
`thickSheet` itself -- so after relabelling the paper's bridge
`e_alpha ∖ e_delta` is nonempty, which is the receipt's `not_thin`. -/
theorem exists_splitAlignment_perm (thin thick wall : SheetPartition d)
    (anchor : Fin d) (hThin : thin.Refines wall) (hThick : thick.Refines wall)
    (thinSheet thickSheet : Fin d)
    (hThinWall : wall.Rel anchor thinSheet) (hThickWall : wall.Rel anchor thickSheet)
    (hCard : thin.blockCard thinSheet < thick.blockCard thickSheet) :
    ∃ gauge : Equiv.Perm (Fin d),
      (∀ sheet, sheet ∉ wall.block anchor → gauge sheet = sheet) ∧
        (∀ sheet ∈ wall.block anchor, gauge sheet ∈ wall.block anchor) ∧
          (thin.block thinSheet).image gauge ⊆
            (thick.block thickSheet).erase thickSheet := by
  classical
  have hThinSub : thin.block thinSheet ⊆ wall.block anchor := by
    intro sheet hSheet
    rw [SheetPartition.mem_block_iff] at hSheet ⊢
    exact hThinWall.trans (hThin.rel hSheet)
  have hThickSub : thick.block thickSheet ⊆ wall.block anchor := by
    intro sheet hSheet
    rw [SheetPartition.mem_block_iff] at hSheet ⊢
    exact hThickWall.trans (hThick.rel hSheet)
  have hSelf : thickSheet ∈ thick.block thickSheet := thick.self_mem_block thickSheet
  have hEraseCard : ((thick.block thickSheet).erase thickSheet).card =
      thick.blockCard thickSheet - 1 := by
    rw [Finset.card_erase_of_mem hSelf]
    rfl
  refine exists_perm_image_subset (wall.block anchor) (thin.block thinSheet)
    ((thick.block thickSheet).erase thickSheet) hThinSub
    ((Finset.erase_subset _ _).trans hThickSub) ?_
  rw [hEraseCard]
  have hPos : 1 ≤ thick.blockCard thickSheet :=
    Finset.card_pos.mpr ⟨thickSheet, hSelf⟩
  show thin.blockCard thinSheet ≤ thick.blockCard thickSheet - 1
  omega

end Finite

/-! ## 1.  The gauge at an actual divalent wall -/

section Wall

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (data : GluingDatum target degree)
    (vertex : data.SourceVertex) : DecidableEq (IncidentSourceEdge data vertex) :=
  Classical.decEq _

/-- **The defining property of the inclusion alignment gauge.**  It fixes the
anchor block's complement pointwise, stabilizes the anchor block, and carries
the `t_thin`-class of `thinSheet` into the `t_thick`-class of `thickSheet` with
`thickSheet` itself left over. -/
def IsSplitGauge (data : GluingDatum target degree) (star : TwoStar target wall)
    (anchor : WallBlock data wall) (thickSheet thinSheet : Fin degree)
    (gauge : Equiv.Perm (Fin degree)) : Prop :=
  (∀ sheet, sheet ∉ (data.vertexPartition wall).block anchor.1 → gauge sheet = sheet) ∧
    (∀ sheet ∈ (data.vertexPartition wall).block anchor.1,
        gauge sheet ∈ (data.vertexPartition wall).block anchor.1) ∧
      ((data.edgePartition (star.edge 1)).block thinSheet).image gauge ⊆
        ((data.edgePartition (star.edge 0)).block thickSheet).erase thickSheet

private theorem exists_conditional_splitGauge (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) :
    ∃ gauge : Equiv.Perm (Fin degree),
      (∀ sheet, sheet ∉ (data.vertexPartition wall).block anchor.1 →
          gauge sheet = sheet) ∧
        (∀ sheet ∈ (data.vertexPartition wall).block anchor.1,
            gauge sheet ∈ (data.vertexPartition wall).block anchor.1) ∧
          ((∃ other, IsSplitGauge data star anchor thickSheet thinSheet other) →
            IsSplitGauge data star anchor thickSheet thinSheet gauge) := by
  by_cases hExists : ∃ other, IsSplitGauge data star anchor thickSheet thinSheet other
  · obtain ⟨other, hOutside, hInside, hImage⟩ := hExists
    exact ⟨other, hOutside, hInside, fun _ ↦ ⟨hOutside, hInside, hImage⟩⟩
  · exact ⟨Equiv.refl _, fun _ _ ↦ rfl, fun _ hSheet ↦ hSheet,
      fun hOther ↦ absurd hOther hExists⟩

/-- **The gauge permutation.**  Unconditionally block-preserving; aligning as
soon as the paper's strict inequality `k_delta < k_alpha` holds. -/
noncomputable def splitGaugePerm (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) : Equiv.Perm (Fin degree) :=
  Classical.choose (exists_conditional_splitGauge data star anchor thickSheet thinSheet)

theorem splitGaugePerm_outside (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) (sheet : Fin degree)
    (hSheet : sheet ∉ (data.vertexPartition wall).block anchor.1) :
    splitGaugePerm data star anchor thickSheet thinSheet sheet = sheet :=
  (Classical.choose_spec
    (exists_conditional_splitGauge data star anchor thickSheet thinSheet)).1 sheet hSheet

theorem splitGaugePerm_inside (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) (sheet : Fin degree)
    (hSheet : sheet ∈ (data.vertexPartition wall).block anchor.1) :
    splitGaugePerm data star anchor thickSheet thinSheet sheet ∈
      (data.vertexPartition wall).block anchor.1 :=
  (Classical.choose_spec
    (exists_conditional_splitGauge data star anchor thickSheet thinSheet)).2.1 sheet hSheet

theorem splitGaugePerm_isSplitGauge (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree)
    (hExists : ∃ other, IsSplitGauge data star anchor thickSheet thinSheet other) :
    IsSplitGauge data star anchor thickSheet thinSheet
      (splitGaugePerm data star anchor thickSheet thinSheet) :=
  (Classical.choose_spec
    (exists_conditional_splitGauge data star anchor thickSheet thinSheet)).2.2 hExists

/-- **The sub-alignment the receipt asks for**, at the level of sheet sets. -/
theorem splitGaugePerm_image (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree)
    (hExists : ∃ other, IsSplitGauge data star anchor thickSheet thinSheet other) :
    ((data.edgePartition (star.edge 1)).block thinSheet).image
        (splitGaugePerm data star anchor thickSheet thinSheet) ⊆
      ((data.edgePartition (star.edge 0)).block thickSheet).erase thickSheet :=
  (splitGaugePerm_isSplitGauge data star anchor thickSheet thinSheet hExists).2.2

theorem splitGaugePerm_rel (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) (sheet : Fin degree) :
    (data.vertexPartition wall).Rel
      (splitGaugePerm data star anchor thickSheet thinSheet sheet) sheet :=
  rel_of_stabilizes_block (data.vertexPartition wall) anchor.1
    (splitGaugePerm data star anchor thickSheet thinSheet)
    (splitGaugePerm_inside data star anchor thickSheet thinSheet)
    (splitGaugePerm_outside data star anchor thickSheet thinSheet) sheet

/-- The gauge stabilizes the anchor block in both directions. -/
theorem splitGaugePerm_symm_inside (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) (sheet : Fin degree)
    (hSheet : sheet ∈ (data.vertexPartition wall).block anchor.1) :
    (splitGaugePerm data star anchor thickSheet thinSheet).symm sheet ∈
      (data.vertexPartition wall).block anchor.1 := by
  by_contra hNot
  have hFixed := splitGaugePerm_outside data star anchor thickSheet thinSheet _ hNot
  rw [Equiv.apply_symm_apply] at hFixed
  exact hNot (hFixed ▸ hSheet)

/-! ## 2.  The gauged datum -/

/-- The canonical branch relabelling: only the component behind the `t_thin`
occurrence receives the alignment permutation. -/
noncomputable def splitRelabeling (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) : data.SheetRelabeling :=
  branchSwapOfPerm data wall
    (TargetSeparation.farEndpoint wall (star.edge 1))
    (TargetSeparation.farEndpoint_ne (star_edge_incident star 1))
    (splitGaugePerm data star anchor thickSheet thinSheet)
    (splitGaugePerm_rel data star anchor thickSheet thinSheet)

/-- The datum after moving the `t_thin` branch so that `e_delta` sits inside
`e_alpha`. -/
noncomputable def splitGaugedData (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) : GluingDatum target degree :=
  (splitRelabeling data star anchor thickSheet thinSheet).apply

theorem splitGaugedData_vertexPartition_wall (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) :
    (splitGaugedData data star anchor thickSheet thinSheet).vertexPartition wall =
      data.vertexPartition wall := by
  unfold splitGaugedData splitRelabeling
  apply branchSwapOfPerm_vertexPartition_wall

theorem splitGaugedData_edgePartition_one (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) :
    (splitGaugedData data star anchor thickSheet thinSheet).edgePartition (star.edge 1) =
      (data.edgePartition (star.edge 1)).relabel
        (splitGaugePerm data star anchor thickSheet thinSheet) := by
  apply branchSwapOfPerm_edgePartition_of_moved
  exact TargetSeparation.edgeMoved_self_eq_true (star_edge_incident star 1)

theorem splitGaugedData_edgePartition_zero (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    (splitGaugedData data star anchor thickSheet thinSheet).edgePartition (star.edge 0) =
      data.edgePartition (star.edge 0) := by
  apply branchSwapOfPerm_edgePartition_of_fixed
  apply TargetSeparation.edgeMoved_eq_false hConnected hGenus
    (star_edge_incident star 1) (star_edge_incident star 0)
  exact star.edge_injective.ne (by decide)

/-- The anchor block, read in the gauged datum. -/
noncomputable def splitGaugedAnchor (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) :
    WallBlock (splitGaugedData data star anchor thickSheet thinSheet) wall :=
  ⟨anchor.1, by
    rw [splitGaugedData_vertexPartition_wall data star anchor thickSheet thinSheet]
    exact anchor.2⟩

@[simp] theorem splitGaugedAnchor_val (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) :
    (splitGaugedAnchor data star anchor thickSheet thinSheet).1 = anchor.1 := rfl

theorem splitGaugedData_valid (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) (hValid : data.Valid) :
    (splitGaugedData data star anchor thickSheet thinSheet).Valid :=
  (splitRelabeling data star anchor thickSheet thinSheet).valid hValid

/-! ## 3.  Transporting the survivor census across the gauge -/

theorem splitGauge_vertexPermutation_wall (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) :
    (splitRelabeling data star anchor thickSheet thinSheet).vertexPermutation wall =
      Equiv.refl (Fin degree) := by
  show GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.vertexMoved wall _ _ wall)
    (splitGaugePerm data star anchor thickSheet thinSheet) = _
  rw [TargetBranchRegion.vertexMoved_wall]
  rfl

theorem splitGauged_sourceVertex_eq (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) :
    (splitRelabeling data star anchor thickSheet thinSheet).sourceVertexEquiv
        (WallBlock.sourceVertex data wall anchor) =
      WallBlock.sourceVertex (splitGaugedData data star anchor thickSheet thinSheet) wall
        (splitGaugedAnchor data star anchor thickSheet thinSheet) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · show (splitRelabeling data star anchor thickSheet thinSheet).vertexPermutation wall
        ((data.vertexPartition wall).repr anchor.1) =
      ((splitGaugedData data star anchor thickSheet thinSheet).vertexPartition wall).repr
        anchor.1
    rw [splitGauge_vertexPermutation_wall data star anchor thickSheet thinSheet,
      splitGaugedData_vertexPartition_wall data star anchor thickSheet thinSheet]
    rfl

/-- **The gauge's census map.**  Incident source occurrences at the anchor are
carried by the literal source-edge equivalence of the relabelling. -/
noncomputable def splitSurvivorEquiv (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) :
    IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor) ≃
      IncidentSourceEdge (splitGaugedData data star anchor thickSheet thinSheet)
        (WallBlock.sourceVertex (splitGaugedData data star anchor thickSheet thinSheet)
          wall (splitGaugedAnchor data star anchor thickSheet thinSheet)) :=
  (splitRelabeling data star anchor thickSheet thinSheet).sourceEdgeEquiv.subtypeEquiv
    fun edge ↦ by
      rw [← splitGauged_sourceVertex_eq data star anchor thickSheet thinSheet]
      exact (SheetRelabelPruning.incident_sourceEdgeEquiv_iff
        (splitRelabeling data star anchor thickSheet thinSheet) edge
        (WallBlock.sourceVertex data wall anchor)).symm

@[simp] theorem splitSurvivorEquiv_val (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)) :
    (splitSurvivorEquiv data star anchor thickSheet thinSheet edge).1 =
      (splitRelabeling data star anchor thickSheet thinSheet).sourceEdgeEquiv edge.1 := rfl

@[simp] theorem splitSurvivorEquiv_target (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)) :
    (splitSurvivorEquiv data star anchor thickSheet thinSheet edge).1.1.1 = edge.1.1.1 := rfl

theorem splitSurvivorEquiv_index (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)) :
    (splitGaugedData data star anchor thickSheet thinSheet).sourceEdgeIndex
        (splitSurvivorEquiv data star anchor thickSheet thinSheet edge).1 =
      data.sourceEdgeIndex edge.1 :=
  SheetRelabelStable.sourceEdgeIndex_map
    (splitRelabeling data star anchor thickSheet thinSheet) edge.1

theorem splitGauged_isDangling_iff (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) (hConnected : data.Connected)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)) :
    IsDangling (splitGaugedData data star anchor thickSheet thinSheet)
        (splitSurvivorEquiv data star anchor thickSheet thinSheet edge).1 ↔
      IsDangling data edge.1 :=
  SheetRelabelPruning.isDangling_sourceEdgeEquiv_iff
    (splitRelabeling data star anchor thickSheet thinSheet) hConnected edge.1

theorem mem_survivors_splitGauged (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) (hConnected : data.Connected)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)) :
    splitSurvivorEquiv data star anchor thickSheet thinSheet edge ∈
        survivors (splitGaugedData data star anchor thickSheet thinSheet)
          (splitGaugedAnchor data star anchor thickSheet thinSheet) ↔
      edge ∈ survivors data anchor := by
  rw [mem_survivors, mem_survivors]
  exact not_congr
    (splitGauged_isDangling_iff data star anchor thickSheet thinSheet hConnected edge)

theorem survivors_splitGauged (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) (hConnected : data.Connected) :
    survivors (splitGaugedData data star anchor thickSheet thinSheet)
        (splitGaugedAnchor data star anchor thickSheet thinSheet) =
      (survivors data anchor).image
        (splitSurvivorEquiv data star anchor thickSheet thinSheet) := by
  classical
  ext edge
  obtain ⟨edge, rfl⟩ :=
    (splitSurvivorEquiv data star anchor thickSheet thinSheet).surjective edge
  rw [mem_survivors_splitGauged data star anchor thickSheet thinSheet hConnected]
  constructor
  · intro hSurvives
    exact Finset.mem_image.mpr ⟨edge, hSurvives, rfl⟩
  · intro hImage
    obtain ⟨other, hOther, hEq⟩ := Finset.mem_image.mp hImage
    exact (splitSurvivorEquiv data star anchor thickSheet thinSheet).injective hEq ▸ hOther

theorem directionSurvivors_splitGauged (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) (hConnected : data.Connected) (label : Fin 2) :
    directionSurvivors (splitGaugedData data star anchor thickSheet thinSheet) star
        (splitGaugedAnchor data star anchor thickSheet thinSheet) label =
      (directionSurvivors data star anchor label).image
        (splitSurvivorEquiv data star anchor thickSheet thinSheet) := by
  classical
  ext edge
  obtain ⟨edge, rfl⟩ :=
    (splitSurvivorEquiv data star anchor thickSheet thinSheet).surjective edge
  rw [mem_directionSurvivors, splitSurvivorEquiv_target,
    mem_survivors_splitGauged data star anchor thickSheet thinSheet hConnected]
  constructor
  · rintro ⟨hSurvives, hTarget⟩
    exact Finset.mem_image.mpr ⟨edge,
      (mem_directionSurvivors data star anchor label edge).mpr ⟨hSurvives, hTarget⟩, rfl⟩
  · intro hImage
    obtain ⟨other, hOther, hEq⟩ := Finset.mem_image.mp hImage
    have hSame : other = edge :=
      (splitSurvivorEquiv data star anchor thickSheet thinSheet).injective hEq
    subst hSame
    exact (mem_directionSurvivors data star anchor label other).mp hOther

theorem card_directionSurvivors_splitGauged (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) (hConnected : data.Connected) (label : Fin 2) :
    (directionSurvivors (splitGaugedData data star anchor thickSheet thinSheet) star
        (splitGaugedAnchor data star anchor thickSheet thinSheet) label).card =
      (directionSurvivors data star anchor label).card := by
  classical
  rw [directionSurvivors_splitGauged data star anchor thickSheet thinSheet hConnected label,
    Finset.card_image_of_injective _
      (splitSurvivorEquiv data star anchor thickSheet thinSheet).injective]

theorem mem_directionSurvivors_splitGauged (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) (hConnected : data.Connected) (label : Fin 2)
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor label) :
    splitSurvivorEquiv data star anchor thickSheet thinSheet edge ∈
      directionSurvivors (splitGaugedData data star anchor thickSheet thinSheet) star
        (splitGaugedAnchor data star anchor thickSheet thinSheet) label := by
  classical
  rw [directionSurvivors_splitGauged data star anchor thickSheet thinSheet hConnected label]
  exact Finset.mem_image.mpr ⟨edge, hEdge, rfl⟩

theorem activeTargets_splitGauged (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) (hConnected : data.Connected) :
    activeTargets (splitGaugedData data star anchor thickSheet thinSheet)
        (splitGaugedAnchor data star anchor thickSheet thinSheet) =
      activeTargets data anchor := by
  classical
  unfold activeTargets
  rw [survivors_splitGauged data star anchor thickSheet thinSheet hConnected,
    Finset.image_image]
  rfl

theorem splitGauged_blockCard (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) :
    ((splitGaugedData data star anchor thickSheet thinSheet).vertexPartition wall).blockCard
        anchor.1 =
      (data.vertexPartition wall).blockCard anchor.1 := by
  rw [splitGaugedData_vertexPartition_wall data star anchor thickSheet thinSheet]

/-- **Configuration A survives the gauge.** -/
theorem split_splitGauged (data : GluingDatum target degree) (star : TwoStar target wall)
    (anchor : WallBlock data wall) (thickSheet thinSheet : Fin degree)
    (hConnected : data.Connected)
    (hSplit : ∀ label : Fin 2, (directionSurvivors data star anchor label).card = 2)
    (label : Fin 2) :
    (directionSurvivors (splitGaugedData data star anchor thickSheet thinSheet) star
      (splitGaugedAnchor data star anchor thickSheet thinSheet) label).card = 2 := by
  rw [card_directionSurvivors_splitGauged data star anchor thickSheet thinSheet
    hConnected label]
  exact hSplit label

/-- **The valency-two classifier survives the inclusion branch gauge.**  Every
field of `TwoBranchAnchor` is a count or an index sum over the survivor census,
and the census is carried by `splitSurvivorEquiv`. -/
theorem splitGaugedSource (data : GluingDatum target degree) (star : TwoStar target wall)
    (anchor : WallBlock data wall) (thickSheet thinSheet : Fin degree)
    (hConnected : data.Connected) (source : TwoBranchAnchor data star anchor) :
    TwoBranchAnchor (splitGaugedData data star anchor thickSheet thinSheet) star
      (splitGaugedAnchor data star anchor thickSheet thinSheet) where
  active_all := by
    rw [activeTargets_splitGauged data star anchor thickSheet thinSheet hConnected]
    exact source.active_all
  distribution := by
    rcases source.distribution with hEven | ⟨tripled, hTripled, hSingle⟩
    · refine Or.inl fun label ↦ ?_
      rw [card_directionSurvivors_splitGauged data star anchor thickSheet thinSheet
        hConnected label]
      exact hEven label
    · refine Or.inr ⟨tripled, ?_, fun label hNe ↦ ?_⟩
      · rw [card_directionSurvivors_splitGauged data star anchor thickSheet thinSheet
          hConnected tripled]
        exact hTripled
      · rw [card_directionSurvivors_splitGauged data star anchor thickSheet thinSheet
          hConnected label]
        exact hSingle label hNe
  direction_index_sum := by
    intro label
    classical
    rw [directionSurvivors_splitGauged data star anchor thickSheet thinSheet hConnected label,
      Finset.sum_image (fun _ _ _ _ hEq ↦
        (splitSurvivorEquiv data star anchor thickSheet thinSheet).injective hEq)]
    rw [show ((splitGaugedAnchor data star anchor thickSheet thinSheet).1) = anchor.1 from rfl,
      splitGauged_blockCard data star anchor thickSheet thinSheet]
    rw [← source.direction_index_sum label]
    exact Finset.sum_congr rfl fun edge _ ↦ by
      rw [splitSurvivorEquiv_index data star anchor thickSheet thinSheet edge]
  survivor_index_sum := by
    classical
    rw [survivors_splitGauged data star anchor thickSheet thinSheet hConnected,
      Finset.sum_image (fun _ _ _ _ hEq ↦
        (splitSurvivorEquiv data star anchor thickSheet thinSheet).injective hEq)]
    rw [show ((splitGaugedAnchor data star anchor thickSheet thinSheet).1) = anchor.1 from rfl,
      splitGauged_blockCard data star anchor thickSheet thinSheet]
    rw [← source.survivor_index_sum]
    exact Finset.sum_congr rfl fun edge _ ↦ by
      rw [splitSurvivorEquiv_index data star anchor thickSheet thinSheet edge]

/-! ## 4.  Sheet bookkeeping across the gauge -/

theorem splitGauge_edgePermutation_one (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree) :
    (splitRelabeling data star anchor thickSheet thinSheet).edgePermutation (star.edge 1) =
      splitGaugePerm data star anchor thickSheet thinSheet := by
  show GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.edgeMoved wall _ _ (star.edge 1))
    (splitGaugePerm data star anchor thickSheet thinSheet) = _
  rw [TargetSeparation.edgeMoved_self_eq_true (star_edge_incident star 1)]
  rfl

theorem splitGauge_edgePermutation_zero (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    (splitRelabeling data star anchor thickSheet thinSheet).edgePermutation (star.edge 0) =
      Equiv.refl (Fin degree) := by
  show GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.edgeMoved wall _ _ (star.edge 0))
    (splitGaugePerm data star anchor thickSheet thinSheet) = _
  rw [TargetSeparation.edgeMoved_eq_false hConnected hGenus (star_edge_incident star 1)
    (star_edge_incident star 0) (star.edge_injective.ne (by decide))]
  rfl

theorem occurrenceSheet_splitSurvivorEquiv (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)) :
    occurrenceSheet (splitSurvivorEquiv data star anchor thickSheet thinSheet edge) =
      (splitRelabeling data star anchor thickSheet thinSheet).edgePermutation edge.1.1.1
        (occurrenceSheet edge) := rfl

/-- The `t_thick` side is untouched: a survivor above `star.edge 0` keeps its
sheet. -/
theorem occurrenceSheet_splitSurvivorEquiv_zero (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor 0) :
    occurrenceSheet (splitSurvivorEquiv data star anchor thickSheet thinSheet edge) =
      occurrenceSheet edge := by
  rw [occurrenceSheet_splitSurvivorEquiv, survivor_target hEdge,
    splitGauge_edgePermutation_zero data star anchor thickSheet thinSheet hConnected hGenus]
  rfl

/-- The `t_thin` side moves by the gauge permutation. -/
theorem occurrenceSheet_splitSurvivorEquiv_one (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (thickSheet thinSheet : Fin degree)
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor 1) :
    occurrenceSheet (splitSurvivorEquiv data star anchor thickSheet thinSheet edge) =
      splitGaugePerm data star anchor thickSheet thinSheet (occurrenceSheet edge) := by
  rw [occurrenceSheet_splitSurvivorEquiv, survivor_target hEdge,
    splitGauge_edgePermutation_one data star anchor thickSheet thinSheet]

/-! ## 5.  Configuration A pins the thick/thin dispatch -/

variable {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall}

/-- In Configuration A both directions carry two survivors, so
`NonTrivalentValencyTwoCandidate.thickDirection` is `0`. -/
theorem thickDirection_eq_zero
    (hSplit : (directionSurvivors data star anchor 0).card = 2) :
    thickDirection data star anchor = 0 := by
  unfold thickDirection
  rw [if_pos (by rw [hSplit])]

theorem thinDirection_eq_one
    (hSplit : (directionSurvivors data star anchor 0).card = 2) :
    thinDirection data star anchor = 1 := by
  unfold thinDirection
  rw [thickDirection_eq_zero hSplit]
  rfl

theorem thickEdge_eq_zero
    (hSplit : (directionSurvivors data star anchor 0).card = 2) :
    thickEdge data star anchor = star.edge 0 := by
  rw [thickEdge_eq, thickDirection_eq_zero hSplit]

theorem thinEdge_eq_one
    (hSplit : (directionSurvivors data star anchor 0).card = 2) :
    thinEdge data star anchor = star.edge 1 := by
  rw [thinEdge_eq, thinDirection_eq_one hSplit]

/-! ## 6.  The receipt, produced from the paper's strict index inequality -/

section Producer

variable (source : TwoBranchAnchor data star anchor)
  (hSplit : ∀ label : Fin 2, (directionSurvivors data star anchor label).card = 2)
  {alphaEdge betaEdge deltaEdge epsilonEdge :
    IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}

/-- **The gauge exists as soon as `k_delta < k_alpha`.**  This is Part II's
"because `k_alpha > k_delta`" (subcases `{v2-nd4-t3-k2=k3}` and
`{v2-nd4-t3-k2<k3}`) in its geometric form. -/
theorem exists_isSplitGauge
    (hAlpha : alphaEdge ∈ directionSurvivors data star anchor 0)
    (hDelta : deltaEdge ∈ directionSurvivors data star anchor 1)
    (hIndex : data.sourceEdgeIndex deltaEdge.1 < data.sourceEdgeIndex alphaEdge.1) :
    ∃ gauge : Equiv.Perm (Fin degree),
      IsSplitGauge data star anchor (occurrenceSheet alphaEdge)
        (occurrenceSheet deltaEdge) gauge := by
  refine exists_splitAlignment_perm (data.edgePartition (star.edge 1))
    (data.edgePartition (star.edge 0)) (data.vertexPartition wall) anchor.1
    (star.edgePartition_refines_wall data 1) (star.edgePartition_refines_wall data 0)
    (occurrenceSheet deltaEdge) (occurrenceSheet alphaEdge)
    (occurrenceSheet_wall_rel deltaEdge) (occurrenceSheet_wall_rel alphaEdge) ?_
  rw [← sourceEdgeIndex_eq_blockCard hDelta, ← sourceEdgeIndex_eq_blockCard hAlpha]
  exact hIndex

include source hSplit in
/-- **The split receipt at the gauged datum.**  Configuration A with four named
survivors and the single numerical hypothesis `k_delta < k_alpha` produce
`NonTrivalentValencyTwoSplitCandidate.SplitSetup` over the gauged wall datum:
the splitting class is `e_alpha` (above `star.edge 0`, the direction
`NonTrivalentValencyTwoCandidate.rightAssignment` puts at the divalent endpoint
`u`) and the piece is `e_delta` (above `star.edge 1`, at `v`). -/
theorem splitSetup_gauged
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hSourceConnected : data.Connected)
    (hAlpha : alphaEdge ∈ directionSurvivors data star anchor 0)
    (hDelta : deltaEdge ∈ directionSurvivors data star anchor 1)
    (hEpsilon : epsilonEdge ∈ directionSurvivors data star anchor 1)
    (hDeltaNe : deltaEdge ≠ epsilonEdge)
    (hIndex : data.sourceEdgeIndex deltaEdge.1 < data.sourceEdgeIndex alphaEdge.1) :
    SplitSetup
      (splitGaugedData data star anchor (occurrenceSheet alphaEdge)
        (occurrenceSheet deltaEdge)) star
      (splitGaugedAnchor data star anchor (occurrenceSheet alphaEdge)
        (occurrenceSheet deltaEdge))
      (occurrenceSheet alphaEdge)
      (splitGaugePerm data star anchor (occurrenceSheet alphaEdge)
        (occurrenceSheet deltaEdge) (occurrenceSheet deltaEdge)) := by
  classical
  have hExists := exists_isSplitGauge hAlpha hDelta hIndex
  have hImage := splitGaugePerm_image data star anchor (occurrenceSheet alphaEdge)
    (occurrenceSheet deltaEdge) hExists
  have hSplitG : ∀ label : Fin 2,
      (directionSurvivors (splitGaugedData data star anchor (occurrenceSheet alphaEdge)
        (occurrenceSheet deltaEdge)) star
        (splitGaugedAnchor data star anchor (occurrenceSheet alphaEdge)
          (occurrenceSheet deltaEdge)) label).card = 2 :=
    fun label ↦ split_splitGauged data star anchor _ _ hSourceConnected hSplit label
  have hThickG := thickEdge_eq_zero (star := star) (hSplitG 0)
  have hThinG := thinEdge_eq_one (star := star) (hSplitG 0)
  have hVP := splitGaugedData_vertexPartition_wall data star anchor
    (occurrenceSheet alphaEdge) (occurrenceSheet deltaEdge)
  have hE0 := splitGaugedData_edgePartition_zero data star anchor
    (occurrenceSheet alphaEdge) (occurrenceSheet deltaEdge) hConnected hGenus
  have hE1 := splitGaugedData_edgePartition_one data star anchor
    (occurrenceSheet alphaEdge) (occurrenceSheet deltaEdge)
  have hPiece : (splitGaugePerm data star anchor (occurrenceSheet alphaEdge)
        (occurrenceSheet deltaEdge) (occurrenceSheet deltaEdge)) ∈
      ((data.edgePartition (star.edge 0)).block (occurrenceSheet alphaEdge)).erase
        (occurrenceSheet alphaEdge) :=
    hImage (Finset.mem_image.mpr ⟨occurrenceSheet deltaEdge,
      (data.edgePartition (star.edge 1)).self_mem_block _, rfl⟩)
  have hRelabelBlock : ((data.edgePartition (star.edge 1)).relabel
        (splitGaugePerm data star anchor (occurrenceSheet alphaEdge)
          (occurrenceSheet deltaEdge))).block
        (splitGaugePerm data star anchor (occurrenceSheet alphaEdge)
          (occurrenceSheet deltaEdge) (occurrenceSheet deltaEdge)) =
      ((data.edgePartition (star.edge 1)).block (occurrenceSheet deltaEdge)).image
        (splitGaugePerm data star anchor (occurrenceSheet alphaEdge)
          (occurrenceSheet deltaEdge)) :=
    (data.edgePartition (star.edge 1)).relabel_block _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show ((splitGaugedData data star anchor (occurrenceSheet alphaEdge)
      (occurrenceSheet deltaEdge)).vertexPartition wall).Rel anchor.1 _
    rw [hVP]
    exact occurrenceSheet_wall_rel alphaEdge
  · rw [hThickG, hE0]
    exact ((data.edgePartition (star.edge 0)).mem_block_iff _ _).mp
      (Finset.mem_of_mem_erase hPiece)
  · rw [hThickG, hThinG, hE0, hE1, hRelabelBlock]
    exact fun sheet hSheet ↦ Finset.mem_of_mem_erase (hImage hSheet)
  · rw [hThinG, hE1]
    intro hRel
    have hMem : occurrenceSheet alphaEdge ∈ ((data.edgePartition (star.edge 1)).relabel
        (splitGaugePerm data star anchor (occurrenceSheet alphaEdge)
          (occurrenceSheet deltaEdge))).block
        (splitGaugePerm data star anchor (occurrenceSheet alphaEdge)
          (occurrenceSheet deltaEdge) (occurrenceSheet deltaEdge)) :=
      (SheetPartition.mem_block_iff _ _ _).mpr hRel.symm
    rw [hRelabelBlock] at hMem
    exact (Finset.mem_erase.mp (hImage hMem)).1 rfl
  · intro sheet hSheet
    have hSheetRel : (data.vertexPartition wall).Rel anchor.1 sheet := by
      have hRaw : ((splitGaugedData data star anchor (occurrenceSheet alphaEdge)
          (occurrenceSheet deltaEdge)).vertexPartition wall).Rel anchor.1 sheet := hSheet
      rw [hVP] at hRaw
      exact hRaw
    rw [hThinG, hE1]
    have hSheetMem : sheet ∈ (data.vertexPartition wall).block anchor.1 :=
      ((data.vertexPartition wall).mem_block_iff _ _).mpr hSheetRel
    have hOriginMem := splitGaugePerm_symm_inside data star anchor
      (occurrenceSheet alphaEdge) (occurrenceSheet deltaEdge) sheet hSheetMem
    have hOrigin : (data.vertexPartition wall).Rel anchor.1
        ((splitGaugePerm data star anchor (occurrenceSheet alphaEdge)
          (occurrenceSheet deltaEdge)).symm sheet) :=
      ((data.vertexPartition wall).mem_block_iff _ _).mp hOriginMem
    have hRestore : (splitGaugePerm data star anchor (occurrenceSheet alphaEdge)
        (occurrenceSheet deltaEdge))
        ((splitGaugePerm data star anchor (occurrenceSheet alphaEdge)
          (occurrenceSheet deltaEdge)).symm sheet) = sheet :=
      Equiv.apply_symm_apply _ _
    rcases pair_cover source (hSplit 1) hDelta hEpsilon hDeltaNe hOrigin with hCase | hCase
    · left
      have hRel := ((data.edgePartition (star.edge 1)).relabel_rel_iff
        (splitGaugePerm data star anchor (occurrenceSheet alphaEdge)
          (occurrenceSheet deltaEdge)) (occurrenceSheet deltaEdge) _).mpr hCase
      rwa [hRestore] at hRel
    · right
      have hAlphaMem : occurrenceSheet alphaEdge ∈
          (data.vertexPartition wall).block anchor.1 :=
        ((data.vertexPartition wall).mem_block_iff _ _).mpr
          (occurrenceSheet_wall_rel alphaEdge)
      have hAlphaOriginMem := splitGaugePerm_symm_inside data star anchor
        (occurrenceSheet alphaEdge) (occurrenceSheet deltaEdge) _ hAlphaMem
      have hAlphaOrigin : (data.vertexPartition wall).Rel anchor.1
          ((splitGaugePerm data star anchor (occurrenceSheet alphaEdge)
            (occurrenceSheet deltaEdge)).symm (occurrenceSheet alphaEdge)) :=
        ((data.vertexPartition wall).mem_block_iff _ _).mp hAlphaOriginMem
      have hAlphaRestore : (splitGaugePerm data star anchor (occurrenceSheet alphaEdge)
          (occurrenceSheet deltaEdge))
          ((splitGaugePerm data star anchor (occurrenceSheet alphaEdge)
            (occurrenceSheet deltaEdge)).symm (occurrenceSheet alphaEdge)) =
          occurrenceSheet alphaEdge :=
        Equiv.apply_symm_apply _ _
      rcases pair_cover source (hSplit 1) hDelta hEpsilon hDeltaNe hAlphaOrigin with
        hAlphaCase | hAlphaCase
      · exfalso
        have hMem : occurrenceSheet alphaEdge ∈
            ((data.edgePartition (star.edge 1)).block (occurrenceSheet deltaEdge)).image
              (splitGaugePerm data star anchor (occurrenceSheet alphaEdge)
                (occurrenceSheet deltaEdge)) :=
          Finset.mem_image.mpr ⟨_,
            ((data.edgePartition (star.edge 1)).mem_block_iff _ _).mpr hAlphaCase,
            hAlphaRestore⟩
        exact (Finset.mem_erase.mp (hImage hMem)).1 rfl
      · have hFirst := ((data.edgePartition (star.edge 1)).relabel_rel_iff
          (splitGaugePerm data star anchor (occurrenceSheet alphaEdge)
            (occurrenceSheet deltaEdge)) (occurrenceSheet epsilonEdge) _).mpr hAlphaCase
        have hSecond := ((data.edgePartition (star.edge 1)).relabel_rel_iff
          (splitGaugePerm data star anchor (occurrenceSheet alphaEdge)
            (occurrenceSheet deltaEdge)) (occurrenceSheet epsilonEdge) _).mpr hCase
        rw [hAlphaRestore] at hFirst
        rw [hRestore] at hSecond
        exact hFirst.symm.trans hSecond

end Producer

/-! ## 7.  The three new-edge class sizes in the paper's indices

`NonTrivalentValencyTwoSplitCandidate` proves the sizes against the block
cardinalities of the two direction partitions; under Configuration A those are
the dilation indices of the four named survivors, by
`NonTrivalentValencyTwoCandidate.sourceEdgeIndex_eq_blockCard`. These statements
are over an arbitrary datum carrying a `SplitSetup`, so they apply verbatim at
the gauged datum. -/

section Sizes

variable {alpha delta : Fin degree} (setup : SplitSetup data star anchor alpha delta)

/-- **The piece** `e_delta` continues through the new edge with index `k_delta`. -/
theorem splitCandidate_newEdge_blockCard_piece
    (hSplitZero : (directionSurvivors data star anchor 0).card = 2)
    {deltaEdge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hDelta : deltaEdge ∈ directionSurvivors data star anchor 1)
    (hSheet : occurrenceSheet deltaEdge = delta) :
    ((validCandidate setup).resolution anchor.1).newEdge.blockCard delta =
      data.sourceEdgeIndex deltaEdge.1 := by
  rw [validCandidate_newEdge_blockCard_piece setup, sourceEdgeIndex_eq_blockCard hDelta,
    hSheet, thinEdge_eq_one hSplitZero]

/-- **The bridge** `e_1 = e_alpha ∖ e_delta` has index `k_alpha - k_delta`; it is
nonempty exactly by the receipt's `not_thin`, i.e. by `k_delta < k_alpha`. -/
theorem splitCandidate_newEdge_blockCard_bridge
    (hSplitZero : (directionSurvivors data star anchor 0).card = 2)
    {alphaEdge deltaEdge : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall anchor)}
    (hAlpha : alphaEdge ∈ directionSurvivors data star anchor 0)
    (hDelta : deltaEdge ∈ directionSurvivors data star anchor 1)
    (hAlphaSheet : occurrenceSheet alphaEdge = alpha)
    (hDeltaSheet : occurrenceSheet deltaEdge = delta) :
    ((validCandidate setup).resolution anchor.1).newEdge.blockCard alpha =
      data.sourceEdgeIndex alphaEdge.1 - data.sourceEdgeIndex deltaEdge.1 := by
  rw [validCandidate_newEdge_blockCard_bridge setup, sourceEdgeIndex_eq_blockCard hAlpha,
    sourceEdgeIndex_eq_blockCard hDelta, hAlphaSheet, hDeltaSheet,
    thinEdge_eq_one hSplitZero, thickEdge_eq_zero hSplitZero]

/-- **The pass-through** `e_beta` crosses the new edge whole, with index
`k_beta`. -/
theorem splitCandidate_newEdge_blockCard_pass
    (hSplitZero : (directionSurvivors data star anchor 0).card = 2)
    {alphaEdge betaEdge : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall anchor)}
    (hAlpha : alphaEdge ∈ directionSurvivors data star anchor 0)
    (hBeta : betaEdge ∈ directionSurvivors data star anchor 0)
    (hNe : alphaEdge ≠ betaEdge) (hAlphaSheet : occurrenceSheet alphaEdge = alpha) :
    ((validCandidate setup).resolution anchor.1).newEdge.blockCard
        (occurrenceSheet betaEdge) = data.sourceEdgeIndex betaEdge.1 := by
  have hNotRel : ¬(data.edgePartition (thickEdge data star anchor)).Rel alpha
      (occurrenceSheet betaEdge) := by
    rw [thickEdge_eq_zero hSplitZero, ← hAlphaSheet]
    exact not_rel_occurrenceSheet hAlpha hBeta hNe
  rw [validCandidate_newEdge_blockCard_pass setup (occurrenceSheet_wall_rel betaEdge) hNotRel,
    sourceEdgeIndex_eq_blockCard hBeta, thickEdge_eq_zero hSplitZero]

end Sizes

/-! ## 8.  The packaged producer -/

section Packaged

variable (source : TwoBranchAnchor data star anchor)
  (hSplit : ∀ label : Fin 2, (directionSurvivors data star anchor label).card = 2)
  {alphaEdge deltaEdge epsilonEdge :
    IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}

include source hSplit in
/-- **Part II's split members of Types I and II (subcases `{v2-nd4-t3-k2=k3}`
and `{v2-nd4-t3-k2<k3}`), with the numerical hypothesis.** Given Configuration
A, the prescribed splitting class `e_alpha` above `star.edge 0`, the prescribed
piece `e_delta` above `star.edge 1` and *only* the paper's strict inequality
`k_delta < k_alpha`, the `t_thin`-branch gauge produces a datum carrying
`SplitSetup`, and over it the split candidate exists with a valid outgoing
datum. The gauge is returned with the candidate: the wall partition and the
`t_thick` partition are literally unchanged, and the `t_thin` partition is
relabelled by `splitGaugePerm`. -/
theorem exists_splitCandidate_of_indices
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hValid : data.Valid)
    (hAlpha : alphaEdge ∈ directionSurvivors data star anchor 0)
    (hDelta : deltaEdge ∈ directionSurvivors data star anchor 1)
    (hEpsilon : epsilonEdge ∈ directionSurvivors data star anchor 1)
    (hDeltaNe : deltaEdge ≠ epsilonEdge)
    (hIndex : data.sourceEdgeIndex deltaEdge.1 < data.sourceEdgeIndex alphaEdge.1) :
    ∃ setup : SplitSetup
        (splitGaugedData data star anchor (occurrenceSheet alphaEdge)
          (occurrenceSheet deltaEdge)) star
        (splitGaugedAnchor data star anchor (occurrenceSheet alphaEdge)
          (occurrenceSheet deltaEdge)) (occurrenceSheet alphaEdge)
        (splitGaugePerm data star anchor (occurrenceSheet alphaEdge)
          (occurrenceSheet deltaEdge) (occurrenceSheet deltaEdge)),
      (validCandidate setup).datum.Valid ∧
        (validCandidate setup).resolution anchor.1 =
            selectedResolution (splitGaugedData data star anchor (occurrenceSheet alphaEdge)
              (occurrenceSheet deltaEdge)) star
              (splitGaugedAnchor data star anchor (occurrenceSheet alphaEdge)
                (occurrenceSheet deltaEdge)) ∧
          (splitGaugedData data star anchor (occurrenceSheet alphaEdge)
              (occurrenceSheet deltaEdge)).vertexPartition wall =
              data.vertexPartition wall ∧
            (splitGaugedData data star anchor (occurrenceSheet alphaEdge)
                (occurrenceSheet deltaEdge)).edgePartition (star.edge 0) =
                data.edgePartition (star.edge 0) ∧
              (splitGaugedData data star anchor (occurrenceSheet alphaEdge)
                  (occurrenceSheet deltaEdge)).edgePartition (star.edge 1) =
                (data.edgePartition (star.edge 1)).relabel
                  (splitGaugePerm data star anchor (occurrenceSheet alphaEdge)
                    (occurrenceSheet deltaEdge)) := by
  have hSetup := splitSetup_gauged source hSplit hConnected hGenus hValid.1 hAlpha hDelta
    hEpsilon hDeltaNe hIndex
  refine ⟨hSetup, ?_, ?_, ?_, ?_, ?_⟩
  · exact validCandidate_datum_valid hSetup
      (splitGaugedData_valid data star anchor (occurrenceSheet alphaEdge)
        (occurrenceSheet deltaEdge) hValid)
  · exact validCandidate_resolution_anchor hSetup
  · exact splitGaugedData_vertexPartition_wall data star anchor (occurrenceSheet alphaEdge)
      (occurrenceSheet deltaEdge)
  · exact splitGaugedData_edgePartition_zero data star anchor (occurrenceSheet alphaEdge)
      (occurrenceSheet deltaEdge) hConnected hGenus
  · exact splitGaugedData_edgePartition_one data star anchor (occurrenceSheet alphaEdge)
      (occurrenceSheet deltaEdge)

end Packaged

end Wall

/-! ## 9.  Non-vacuity of the gauge on a literal model

Five sheets, one wall block; `t_thick`-classes `{0,1,2} | {3,4}`
(`k_alpha = 3`, `k_beta = 2`), `t_thin`-classes `{0,3} | {1,2,4}`
(`k_delta = 2`, `k_epsilon = 3`).  The paper's strict inequality
`k_delta = 2 < 3 = k_alpha` holds, yet over this fixed datum `e_delta` is
**not** contained in `e_alpha`, so the sub-alignment really needs a branch
move; and the move exists. -/

section NonVacuity

/-- The literal wall partition of the misaligned model: one block on five
sheets. -/
def splitModelWall : SheetPartition 5 := ⟨fun _ ↦ 0, by decide⟩

/-- The literal `t_thick` partition inside the anchor: `{0,1,2} | {3,4}`. -/
def splitModelThick : SheetPartition 5 := ⟨fun i ↦ if i.val < 3 then 0 else 3, by decide⟩

/-- The literal `t_thin` partition inside the anchor: `{0,3} | {1,2,4}`. -/
def splitModelThin : SheetPartition 5 :=
  ⟨fun i ↦ if i.val = 0 ∨ i.val = 3 then 0 else 1, by decide⟩

theorem splitModelThick_refines : splitModelThick.Refines splitModelWall := by decide

theorem splitModelThin_refines : splitModelThin.Refines splitModelWall := by decide

/-- The paper's strict index inequality holds on the model: `k_delta = 2`,
`k_alpha = 3`. -/
theorem splitModel_cards :
    splitModelThin.blockCard 0 = 2 ∧ splitModelThick.blockCard 0 = 3 := by decide

/-- **Why a gauge is needed at all.**  Over this fixed datum the strict index
inequality holds but the receipt's sub-alignment `e_delta ⊆ e_alpha` fails. -/
theorem splitModel_not_sub : ¬ splitModelThin.block 0 ⊆ splitModelThick.block 0 := by decide

/-- **A literal inhabitant of the inclusion gauge's defining property.**  These
are exactly the three clauses of `IsSplitGauge`, for the model's two direction
partitions with `thickSheet = thinSheet = 0`. -/
theorem splitModel_gauge_exists :
    ∃ gauge : Equiv.Perm (Fin 5),
      (∀ sheet, sheet ∉ splitModelWall.block 0 → gauge sheet = sheet) ∧
        (∀ sheet ∈ splitModelWall.block 0, gauge sheet ∈ splitModelWall.block 0) ∧
          (splitModelThin.block 0).image gauge ⊆ (splitModelThick.block 0).erase 0 :=
  exists_splitAlignment_perm splitModelThin splitModelThick splitModelWall 0
    splitModelThin_refines splitModelThick_refines 0 0 (by decide) (by decide) (by decide)

/-- Configuration A, subcase `{v2-nd4-t3-k2<k3}`: `|A| = 5`,
`k = (3, 2 | 2, 3)`.  Both direction sums are `|A|`, the piece has index `2`,
the bridge `3 - 2 = 1` and the pass-through `2`. -/
theorem splitModel_index_witness :
    (3 + 2 : ℕ) = 5 ∧ (2 + 3 : ℕ) = 5 ∧ (2 : ℕ) < 3 ∧ (3 : ℕ) - 2 = 1 := by
  norm_num

end NonVacuity

end DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitGauge
