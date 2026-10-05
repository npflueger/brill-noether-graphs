module

public import DraismaVargas.LocalCases.W2MkkIncomingMatching

@[expose] public section

/-!
# The selected-class census at a `w2Mkk` wall

Source: Draisma--Vargas Part I (arXiv:1909.12924), Section 6, Case
`{w2-r2-nd3-M-kk}` and its Figure 34; the Base I/II vocabulary is fixed once for
the whole valency-two case in Case `{w2-r2}` there, and every statement below is
in those words.

This module determines what an **arbitrary** incoming `w2Mkk` cover's two
restored endpoints and contracted occurrence carry on the distinguished block
`A₀`.  `W2MkkIncomingMatching.SelectedCensus` names the three facts and
`DetachCensus`/`JoinedCensus` are its two instantiations; Part I's discussion of
Base II asserts the dichotomy between them ("`ndG(A₀)` has either one edge `e'`;
or two edges `e'`, `e''`") and this module proves it.

## The argument, in counts

Write `p`, `q`, `c` for the numbers of induced blocks above `A₀` of the `t₂`
endpoint, the `t₃` endpoint and the contracted occurrence.  Cardinality M puts
**two** occurrences above each of `t₂` (`e₁`, `e₂`, of indices `k₁, k₂ ≥ 2`) and
`t₃` (`e₃` of index `k₃ = k₁+k₂-1`, and the dangling `e₄` of index one), so both
directions induce exactly two blocks above `A₀`
(`W2MkkSourceCandidates.endpointPartition_blockCountWithin` and
`singlePartition_blockCountWithin` below).  Since an occurrence partition
refines its endpoint's vertex partition, that already gives `p ≤ 2` and
`q ≤ 2` -- the bound that makes the case finite.

The rest is three equations.  At a `T_2` wall change-minimality puts one unit of
change at each restored endpoint and the `r = 0` background census puts all of
it above `A₀`, so summing `localRamification` over the blocks above `A₀` gives
`c + 2 - 2p = 1` at the `t₂` endpoint and `c + 2 - 2q = 1` at the `t₃` endpoint;
the contraction forest gives `c + 1 = p + q`.  Hence `p = q` and `c = 2p - 1`,
and with `p ≤ 2` exactly two solutions survive:

* `p = q = c = 1` -- **Base II.1** of Part I: all three wall positions carry the
  whole of `A₀`.  That is `JoinedCensus`.
* `p = q = 2`, `c = 3` -- **Base II.2** of Part I.  Then each partition has as
  many induced blocks above `A₀` as the occurrence partition refining it, so
  they agree there: the `t₂` endpoint splits `A₀` as `e₁ ⊔ e₂`
  (`endpointPartition`), the `t₃` endpoint as `e₃ ⊔ e₄ = (A₀ ∖ {x}) ⊔ {x}` with
  `x` the pinned sheet, and the contracted occurrence is their common
  refinement, `endpointPartition` with `{x}` detached.  That is `DetachCensus`.

## Base I is precluded on the incoming side too

`W2MkkIncomingCensus.divalent_of_member_placement` precludes `T_∅` for a cover
that is *already known* to match a Figure 34 member.  Here nothing is known, so
the leaf orientations of `SecondEquation.valencySplit_of_twoStar` are excluded
directly, and the M-kk indices do it in three lines of counting:
`MonovalentWall.exists_leafFibre` says a change-minimal leaf makes the
contracted occurrence partition **discrete**, the non-leaf endpoint is trivalent
with vanishing change, so every one of its blocks `B` above `A₀` has

`0 = r(B) = |B| + #t₂(B) + #t₃(B) - 2 - |B|`,

i.e. exactly one `t₂` block and one `t₃` block inside it.  Both partitions
therefore agree with the endpoint's above `A₀`; at the pinned sheet the `t₃`
block is the singleton `{x}` while the `t₂` block is `e₁` or `e₂`, of cardinality
`k₁, k₂ ≥ 2`.  `Shape.one_lt_first`/`one_lt_second` is exactly what fails, which
is the source's own reason (Part I's discussion of Base I: it forces `k₂ = k₄`
or `k₁ = k₄`, and `k₄ = 1`).

## Main results

* `singlePartition_blockCountWithin` -- the `t₃` direction induces two blocks
  above `A₀`, the companion of `endpointPartition_blockCountWithin`;
* `divalent_endpoints` -- Base I precluded, so the incoming wall is `T_2`;
* `selected_counts` -- `p = q` and `c = 2p - 1` with `p ≤ 2`;
* `selectedCensus_dichotomy` -- `DetachCensus ∨ JoinedCensus`;
* `exists_member_normalization` -- `W2MkkIncomingMatching`'s exit with the
  dichotomy discharged.
-/

namespace DraismaVargas.LocalCases.W2MkkSelectedCensus

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionRamification
open TargetExpansion ResolutionM11 FullDimensionalSource WallDegeneration
open W4Assembly W4StableSource W2R1Target SecondEquation StableLocalProperties
open NonDanglingValency
open M11IncomingPartitions
open W2MkkSourceCandidates
open W2MkkIncomingCensus

/-! ## §0  Generic counting facts about induced blocks

Three statements about a chain `fine ⊑ mid ⊑ coarse` of sheet partitions.  None
mentions a gluing datum; they would fit in `Infrastructure/Change.lean`, beside
`SheetPartition.card_blocks_eq_sum_blockCountWithin`. -/

section Counting

variable {degree : ℕ}

/-- Natural summands bounded below by one that add up to the number of
summands are all equal to one. -/
theorem eq_one_of_sum_eq_card {α : Type*} {s : Finset α} {f : α → ℕ}
    (hOne : ∀ x ∈ s, 1 ≤ f x) (hSum : ∑ x ∈ s, f x = s.card)
    {x : α} (hx : x ∈ s) : f x = 1 := by
  by_contra hNe
  have hAtLeast := hOne x hx
  have hTwo : 1 < f x := by omega
  have hLt : ∑ _y ∈ s, 1 < ∑ y ∈ s, f y :=
    Finset.sum_lt_sum (fun y hy ↦ hOne y hy) ⟨x, hx, hTwo⟩
  rw [hSum, Finset.sum_const, smul_eq_mul, mul_one] at hLt
  exact lt_irrefl _ hLt

/-- **A coarsening never has more induced blocks.**  Each of the `mid` blocks
inside the coarse block contains at least one `fine` block. -/
theorem blockCountWithin_mono (fine mid coarse : SheetPartition degree)
    (hFineMid : fine.Refines mid) (hMidCoarse : mid.Refines coarse)
    (coarseBlock : coarse.Blocks) :
    mid.blockCountWithin coarse coarseBlock.1 ≤
      fine.blockCountWithin coarse coarseBlock.1 := by
  classical
  have hSum := sum_blockCountWithin_trans fine mid coarse hFineMid hMidCoarse coarseBlock
  have hCards := SheetPartition.card_blocksWithin_eq_blockCountWithin mid coarse
    hMidCoarse coarseBlock
  have hLower : (SheetPartition.blocksWithin mid coarse coarseBlock).card * 1 ≤
      ∑ midBlock ∈ SheetPartition.blocksWithin mid coarse coarseBlock,
        fine.blockCountWithin mid midBlock.1 := by
    rw [← smul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ 1
      (fun midBlock _ ↦ SheetPartition.blockCountWithin_pos fine mid midBlock.1)
  rw [mul_one, hCards] at hLower
  have hCast : ((∑ midBlock ∈ SheetPartition.blocksWithin mid coarse coarseBlock,
      fine.blockCountWithin mid midBlock.1 : ℕ) : ℤ) =
      (fine.blockCountWithin coarse coarseBlock.1 : ℤ) := by
    rw [Nat.cast_sum]; exact hSum
  have hNat : ∑ midBlock ∈ SheetPartition.blocksWithin mid coarse coarseBlock,
      fine.blockCountWithin mid midBlock.1 =
      fine.blockCountWithin coarse coarseBlock.1 := by exact_mod_cast hCast
  omega

/-- **A refinement with the same induced count agrees throughout the block.** -/
theorem block_eq_of_blockCountWithin_eq (fine mid coarse : SheetPartition degree)
    (hFineMid : fine.Refines mid) (hMidCoarse : mid.Refines coarse)
    (coarseBlock : coarse.Blocks)
    (hEq : fine.blockCountWithin coarse coarseBlock.1 =
      mid.blockCountWithin coarse coarseBlock.1)
    (sheet : Fin degree) (hSheet : coarse.Rel coarseBlock.1 sheet) :
    fine.block sheet = mid.block sheet := by
  classical
  have hSum := sum_blockCountWithin_trans fine mid coarse hFineMid hMidCoarse coarseBlock
  have hCards := SheetPartition.card_blocksWithin_eq_blockCountWithin mid coarse
    hMidCoarse coarseBlock
  have hSumNat : ∑ midBlock ∈ SheetPartition.blocksWithin mid coarse coarseBlock,
      fine.blockCountWithin mid midBlock.1 =
      (SheetPartition.blocksWithin mid coarse coarseBlock).card := by
    have hCast : ((∑ midBlock ∈ SheetPartition.blocksWithin mid coarse coarseBlock,
        fine.blockCountWithin mid midBlock.1 : ℕ) : ℤ) =
        ((SheetPartition.blocksWithin mid coarse coarseBlock).card : ℤ) := by
      rw [Nat.cast_sum, hSum, hCards, hEq]
    exact_mod_cast hCast
  have hMem : mid.toBlock sheet ∈ SheetPartition.blocksWithin mid coarse coarseBlock := by
    rw [SheetPartition.mem_blocksWithin]
    refine (SheetPartition.fineBlockToCoarseBlock_eq_iff_rel mid coarse _ coarseBlock).mpr ?_
    exact hSheet.trans (hMidCoarse.rel (mid.rel_repr_right sheet))
  have hOne := eq_one_of_sum_eq_card
    (f := fun midBlock : mid.Blocks ↦ fine.blockCountWithin mid midBlock.1)
    (fun midBlock _ ↦ SheetPartition.blockCountWithin_pos _ _ _) hSumNat hMem
  have hCount : fine.blockCountWithin mid sheet = 1 := by
    rw [← hOne]
    exact blockCountWithin_congr _ mid (mid.rel_repr_right sheet)
  exact SheetPartition.block_eq_of_refines_of_blockCountWithin_eq_one fine mid hFineMid
    sheet hCount

/-- A partition whose classes inside one coarse block are the classes of two
named sheets contributes exactly two induced blocks there. -/
theorem blockCountWithin_eq_two (fine coarse : SheetPartition degree)
    (first second anchor : Fin degree)
    (hFirst : coarse.Rel anchor first) (hSecond : coarse.Rel anchor second)
    (hCovers : ∀ sheet, coarse.Rel anchor sheet →
      fine.Rel first sheet ∨ fine.Rel second sheet)
    (hSeparate : ¬ fine.Rel first second) :
    fine.blockCountWithin coarse anchor = 2 := by
  classical
  have hImage : (coarse.block anchor).image fine.repr =
      {fine.repr first, fine.repr second} := by
    ext value
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton,
      SheetPartition.mem_block_iff]
    constructor
    · rintro ⟨source, hSource, rfl⟩
      rcases hCovers source hSource with hRel | hRel
      · exact Or.inl (by rw [SheetPartition.rel_iff] at hRel; exact hRel.symm)
      · exact Or.inr (by rw [SheetPartition.rel_iff] at hRel; exact hRel.symm)
    · rintro (rfl | rfl)
      · exact ⟨first, hFirst, rfl⟩
      · exact ⟨second, hSecond, rfl⟩
  unfold SheetPartition.blockCountWithin
  rw [hImage, Finset.card_insert_of_notMem (by
      simp only [Finset.mem_singleton]
      intro h
      exact hSeparate (by rw [SheetPartition.rel_iff]; exact h)),
    Finset.card_singleton]

end Counting


/-! ## §1  The `t₃` direction induces two blocks above `A₀`

`W2MkkSourceCandidates.endpointPartition_blockCountWithin` says the `t₂`
direction does; Cardinality M puts the dangling `e₄` above `t₃`, so the `t₃`
direction does too, its two blocks being `e₃` and the pinned singleton `{x}`.
This is the fact that bounds the `t₃` endpoint's own count. -/

section Single

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- The `t₃` direction's own occurrence partition, the companion of
`W2MkkSourceCandidates.endpointPartition`. -/
abbrev singlePartition (profile : W2R2SourceProfile.SourceProfile data star block) :
    SheetPartition degree :=
  data.edgePartition (star.edge profile.singleLabel)

theorem singlePartition_refines
    (profile : W2R2SourceProfile.SourceProfile data star block) :
    (singlePartition profile).Refines (data.vertexPartition wall) :=
  star.edgePartition_refines_wall data profile.singleLabel

/-- The canonical sheet of `e₃`. -/
def thirdSheet (profile : W2R2SourceProfile.SourceProfile data star block) :
    Fin degree := profile.third.1.1.2

theorem thirdSheet_rel (profile : W2R2SourceProfile.SourceProfile data star block) :
    (data.vertexPartition wall).Rel block.1 (thirdSheet profile) :=
  sheet_rel_of_incident profile.third

theorem singlePartition_repr_third
    (profile : W2R2SourceProfile.SourceProfile data star block) :
    (singlePartition profile).repr (thirdSheet profile) = thirdSheet profile := by
  have h := profile.third.1.2
  rw [profile.third_target] at h
  exact h

theorem singlePartition_repr_pin (shape : Shape profile) :
    (singlePartition profile).repr (pinSheet profile) = pinSheet profile := by
  have h := profile.deleted.edge.1.2
  rw [shape.deleted_single] at h
  exact h

/-- `|e₃| = k₃`. -/
theorem singlePartition_blockCard_third
    (profile : W2R2SourceProfile.SourceProfile data star block) :
    (singlePartition profile).blockCard (thirdSheet profile) =
      data.sourceEdgeIndex profile.third.1 := by
  show (data.edgePartition (star.edge profile.singleLabel)).blockCard profile.third.1.1.2 =
    (data.edgePartition profile.third.1.1.1).blockCard profile.third.1.1.2
  rw [profile.third_target]

/-- `e₃` and `e₄` are distinct blocks of the `t₃` occurrence partition:
`|e₃| = k₃ ≥ 3` while `|e₄| = 1`. -/
theorem singlePartition_separate (shape : Shape profile) :
    ¬ (singlePartition profile).Rel (thirdSheet profile) (pinSheet profile) := by
  intro hRel
  have hCard := SheetPartition.blockCard_congr (singlePartition profile) hRel
  rw [singlePartition_blockCard_third profile, pinSheet_blockCard shape] at hCard
  have := shape.three_le_third
  omega

theorem thirdSheet_ne_pinSheet (shape : Shape profile) :
    thirdSheet profile ≠ pinSheet profile := by
  intro hEq
  apply singlePartition_separate shape
  rw [hEq]
  exact ((singlePartition profile).rel_iff _ _).mpr rfl

/-- **`e₃` and `e₄` tile `A₀`.**  Cardinality M puts the dangling occurrence
above `t₃`, so the `t₃` fibre of the block is `{e₃, e₄}`. -/
theorem singlePartition_covers (shape : Shape profile) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    (singlePartition profile).Rel (thirdSheet profile) sheet ∨
      (singlePartition profile).Rel (pinSheet profile) sheet := by
  have hIncident : Incident data (data.sourceEdge (star.edge profile.singleLabel) sheet)
      (WallBlock.sourceVertex data wall block) := by
    apply (incident_wallBlock_sourceVertex_iff data block _).mpr
    refine ⟨star.edge_mem_incidentEdges profile.singleLabel, ?_⟩
    apply (WallBlock.ofSheet_eq_iff_rel data wall block _).mpr
    exact hSheet.trans ((star.edgePartition_refines_wall data profile.singleLabel).rel
      ((data.edgePartition (star.edge profile.singleLabel)).rel_repr_right sheet))
  rcases profile.exhaustive ⟨_, hIncident⟩ with hEq | hEq | hEq | hEq
  · exact absurd ((congrArg (fun edge ↦ edge.1.1.1) hEq).trans profile.first_target)
      (star.edge_injective.ne (Ne.symm profile.labels_ne))
  · exact absurd ((congrArg (fun edge ↦ edge.1.1.1) hEq).trans profile.second_target)
      (star.edge_injective.ne (Ne.symm profile.labels_ne))
  · left
    have hSheet := congrArg (fun edge ↦ edge.1.1.2) hEq
    change (singlePartition profile).repr sheet = thirdSheet profile at hSheet
    rw [SheetPartition.rel_iff, singlePartition_repr_third, hSheet]
  · right
    have hSheet := congrArg (fun edge ↦ edge.1.1.2) hEq
    change (singlePartition profile).repr sheet = pinSheet profile at hSheet
    rw [SheetPartition.rel_iff, singlePartition_repr_pin shape, hSheet]

/-- **The exact induced-block count of the `t₃` direction on `A₀`: two.** -/
theorem singlePartition_blockCountWithin (shape : Shape profile) (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    (singlePartition profile).blockCountWithin (data.vertexPartition wall) anchor = 2 :=
  blockCountWithin_eq_two _ _ (thirdSheet profile) (pinSheet profile) anchor
    (hAnchor.symm.trans (thirdSheet_rel profile))
    (hAnchor.symm.trans (pinSheet_rel profile))
    (fun sheet hSheet ↦ singlePartition_covers shape sheet (hAnchor.trans hSheet))
    (singlePartition_separate shape)

end Single

/-! ## §2  Base I is precluded on the incoming side

`SecondEquation.valencySplit_of_twoStar` leaves three target shapes at a W2
wall: `T_2` and the two leaf orientations `T_∅`.  For M-kk the leaf orientations
are impossible, and the reason is the source's own (Part I's discussion of
Base I): Base I forces one of `k₁`, `k₂` to equal `k₄ = 1`, and
`Shape.one_lt_first`/`one_lt_second` says neither does.

Read on the incoming cover, the argument is three counts.  A change-minimal leaf
makes the contracted occurrence partition **discrete**
(`MonovalentWall.LeafFibre.edgePartition_repr`), and the other endpoint is
trivalent with vanishing change, so each of its blocks `B` above the wall
satisfies `0 = r(B) = |B| + #t₂(B) + #t₃(B) - 2 - |B|`.  Hence exactly one `t₃`
block sits inside `B`, and at the pinned sheet that block is the singleton
`{x}` -- so `B = {x}`, and the `t₂` block inside it, which is `e₁` or `e₂`,
would have cardinality one. -/

section LeafExclusion

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
  {block : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
  (profile : W2R2SourceProfile.SourceProfile (contractDatum data hc hab hOne) star block)

/-- The unfolded `t₃` occurrence of the incoming target, the companion of
`W2MkkIncomingCensus.flagEdge`. -/
noncomputable def coflagEdge : target.edges :=
  unfoldEdge hc hab hOne (star.edge profile.singleLabel)

theorem flagEdge_ne_coflagEdge :
    flagEdge data hc hab hOne profile ≠ coflagEdge data hc hab hOne profile := by
  intro h
  have hSub : (foldEdgeEquiv hc hab hOne).symm (star.edge profile.doubleLabel) =
      (foldEdgeEquiv hc hab hOne).symm (star.edge profile.singleLabel) := Subtype.ext h
  exact profile.labels_ne
    (star.edge_injective ((foldEdgeEquiv hc hab hOne).symm.injective hSub))

/-- The incoming `t₂` occurrence partition is the wall datum's, on the nose. -/
theorem flagEdge_edgePartition :
    data.edgePartition (flagEdge data hc hab hOne profile) = endpointPartition profile := rfl

/-- The incoming `t₃` occurrence partition is the wall datum's, on the nose. -/
theorem coflagEdge_edgePartition :
    data.edgePartition (coflagEdge data hc hab hOne profile) = singlePartition profile := rfl

/-- A discrete partition induces as many blocks inside a coarse block as the
coarse block has sheets. -/
theorem blockCountWithin_of_discrete {fine coarse : SheetPartition degree}
    (hDiscrete : ∀ sheet, fine.repr sheet = sheet) (sheet : Fin degree) :
    fine.blockCountWithin coarse sheet = coarse.blockCard sheet := by
  classical
  unfold SheetPartition.blockCountWithin SheetPartition.blockCard
  congr 1
  ext value
  simp only [Finset.mem_image]
  exact ⟨by rintro ⟨x, hx, rfl⟩; rwa [hDiscrete x],
    fun hValue ↦ ⟨value, hValue, hDiscrete value⟩⟩

include fullDim in
/-- **The trivalent endpoint of a leaf orientation cannot exist at an M-kk
wall.**  The hypotheses are exactly the leaf branch of
`SecondEquation.valencySplit_of_twoStar` together with the M-kk shape. -/
theorem false_of_leaf_orientation (shape : Shape profile) (other : target.V)
    (hOtherCard : (GluingDatum.incidentEdges other).card = 3)
    (hChange : data.targetChange other = 0)
    (hContractedAt : contracted ∈ GluingDatum.incidentEdges other)
    (hFlagAt : flagEdge data hc hab hOne profile ∈ GluingDatum.incidentEdges other)
    (hCoflagAt : coflagEdge data hc hab hOne profile ∈ GluingDatum.incidentEdges other)
    (hDiscrete : ∀ sheet, (data.edgePartition contracted).repr sheet = sheet) :
    False := by
  classical
  have hFlagNe := flagEdge_ne_coflagEdge data hc hab hOne profile
  have hContractedFlag : contracted ≠ flagEdge data hc hab hOne profile :=
    fun h ↦ unfoldEdge_ne_contracted hc hab hOne _ h.symm
  have hContractedCoflag : contracted ≠ coflagEdge data hc hab hOne profile :=
    fun h ↦ unfoldEdge_ne_contracted hc hab hOne _ h.symm
  have hNotMemFirst : contracted ∉
      ({flagEdge data hc hab hOne profile, coflagEdge data hc hab hOne profile} :
        Finset target.edges) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact hContractedFlag h
    · exact hContractedCoflag h
  have hNotMemSecond : flagEdge data hc hab hOne profile ∉
      ({coflagEdge data hc hab hOne profile} : Finset target.edges) := by
    simp only [Finset.mem_singleton]
    exact hFlagNe
  have hEdges : GluingDatum.incidentEdges other =
      {contracted, flagEdge data hc hab hOne profile,
        coflagEdge data hc hab hOne profile} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro edge hEdge
      rcases Finset.mem_insert.mp hEdge with rfl | hEdge
      · exact hContractedAt
      · rcases Finset.mem_insert.mp hEdge with rfl | hEdge
        · exact hFlagAt
        · rw [Finset.mem_singleton.mp hEdge]; exact hCoflagAt
    · rw [hOtherCard, Finset.card_insert_of_notMem hNotMemFirst,
        Finset.card_insert_of_notMem hNotMemSecond, Finset.card_singleton]
  have hRam := localRamification_eq_zero_of_targetChange_eq_zero data fullDim.valid other
    hChange ((data.vertexPartition other).toBlock (pinSheet profile))
  unfold GluingDatum.localRamification at hRam
  rw [hEdges, Finset.sum_insert hNotMemFirst, Finset.sum_insert hNotMemSecond,
    Finset.sum_singleton, Finset.card_insert_of_notMem hNotMemFirst,
    Finset.card_insert_of_notMem hNotMemSecond, Finset.card_singleton,
    SheetPartition.toBlock_val] at hRam
  have hReprRel : (data.vertexPartition other).Rel
      ((data.vertexPartition other).repr (pinSheet profile)) (pinSheet profile) :=
    (data.vertexPartition other).rel_repr_left (pinSheet profile)
  rw [blockCountWithin_congr (data.edgePartition contracted) (data.vertexPartition other)
      hReprRel,
    blockCountWithin_congr (data.edgePartition (flagEdge data hc hab hOne profile))
      (data.vertexPartition other) hReprRel,
    blockCountWithin_congr (data.edgePartition (coflagEdge data hc hab hOne profile))
      (data.vertexPartition other) hReprRel,
    SheetPartition.blockCard_congr (data.vertexPartition other) hReprRel,
    blockCountWithin_of_discrete hDiscrete] at hRam
  have hFlagPos := SheetPartition.blockCountWithin_pos
    (data.edgePartition (flagEdge data hc hab hOne profile)) (data.vertexPartition other)
    (pinSheet profile)
  have hCoflagPos := SheetPartition.blockCountWithin_pos
    (data.edgePartition (coflagEdge data hc hab hOne profile)) (data.vertexPartition other)
    (pinSheet profile)
  have hCoflagOne : (data.edgePartition (coflagEdge data hc hab hOne profile)).blockCountWithin
      (data.vertexPartition other) (pinSheet profile) = 1 := by
    push_cast at hRam
    omega
  have hBlockEq := SheetPartition.block_eq_of_refines_of_blockCountWithin_eq_one
    (data.edgePartition (coflagEdge data hc hab hOne profile)) (data.vertexPartition other)
    (refines_of_mem_incidentEdges data hCoflagAt) (pinSheet profile) hCoflagOne
  rw [coflagEdge_edgePartition data hc hab hOne profile, pinSheet_block shape] at hBlockEq
  have hSubset : (endpointPartition profile).block (pinSheet profile) ⊆
      (data.vertexPartition other).block (pinSheet profile) := by
    intro sheet hSheet
    refine ((data.vertexPartition other).mem_block_iff (pinSheet profile) sheet).mpr ?_
    exact (refines_of_mem_incidentEdges data hFlagAt).rel
      (((endpointPartition profile).mem_block_iff (pinSheet profile) sheet).mp hSheet)
  have hCard := Finset.card_le_card hSubset
  rw [← hBlockEq, Finset.card_singleton] at hCard
  have hTwo := one_lt_pinSheet_endpoint_blockCard shape
  unfold SheetPartition.blockCard at hTwo
  omega

/-- The leaf's star, as a literal singleton. -/
theorem incidentEdges_eq_singleton (vertex : target.V)
    (hMem : contracted ∈ GluingDatum.incidentEdges vertex)
    (hCard : (GluingDatum.incidentEdges vertex).card = 1) :
    GluingDatum.incidentEdges vertex = {contracted} := by
  classical
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro edge hEdge
    rw [Finset.mem_singleton.mp hEdge]
    exact hMem
  · rw [hCard, Finset.card_singleton]

include fullDim in
/-- A change-minimal leaf makes the contracted occurrence partition discrete:
`rem-leaves-min-change`, through `MonovalentWall.exists_leafFibre`. -/
theorem discrete_of_leaf (vertex : target.V)
    (hMem : contracted ∈ GluingDatum.incidentEdges vertex)
    (hCard : (GluingDatum.incidentEdges vertex).card = 1) (sheet : Fin degree) :
    (data.edgePartition contracted).repr sheet = sheet := by
  obtain ⟨fibre⟩ := MonovalentWall.exists_leafFibre data fullDim vertex contracted
    (incidentEdges_eq_singleton vertex hMem hCard)
  exact fibre.edgePartition_repr sheet

include fullDim in
/-- **Base I is precluded, incoming side.**  An arbitrary full-dimensional cover
whose contracted wall carries a `w2Mkk` profile has two divalent restored
endpoints and one unit of change at each: the tree `T_2` of Case `{w2}` in
Part I. -/
theorem divalent_endpoints (shape : Shape profile) :
    (GluingDatum.incidentEdges a).card = 2 ∧ (GluingDatum.incidentEdges b).card = 2 ∧
      data.targetChange a = 1 ∧ data.targetChange b = 1 := by
  rcases valencySplit_of_twoStar data hc hab hOne fullDim.valid fullDim.changeMinimal star with
    ⟨hLeft, hRight, hChangeLeft, hChangeRight⟩ |
    ⟨hLeft, hRight, _, hChangeRight⟩ | ⟨hLeft, hRight, hChangeLeft, _⟩
  · exact ⟨hLeft, hRight, hChangeLeft, hChangeRight⟩
  · exact absurd (false_of_leaf_orientation data hc hab hOne fullDim profile shape b hRight
      hChangeRight (contracted_mem_incidentEdges_right hc)
      ((IncomingW2TargetPlacement.right_eq_true_iff hc hab hOne _).mp
        (IncomingW2TargetPlacement.right_star_of_leaf_left hc hab hOne star hLeft
          profile.doubleLabel))
      ((IncomingW2TargetPlacement.right_eq_true_iff hc hab hOne _).mp
        (IncomingW2TargetPlacement.right_star_of_leaf_left hc hab hOne star hLeft
          profile.singleLabel))
      (discrete_of_leaf data fullDim a (contracted_mem_incidentEdges_left hc) hLeft))
      not_false
  · exact absurd (false_of_leaf_orientation data hc hab hOne fullDim profile shape a hLeft
      hChangeLeft (contracted_mem_incidentEdges_left hc)
      ((IncomingW2TargetPlacement.right_eq_false_iff_of_incident hc hab hOne _
        (star.edge_mem_incidentEdges profile.doubleLabel)).mp
        (IncomingW2TargetPlacement.right_star_of_leaf_right hc hab hOne star hRight
          profile.doubleLabel))
      ((IncomingW2TargetPlacement.right_eq_false_iff_of_incident hc hab hOne _
        (star.edge_mem_incidentEdges profile.singleLabel)).mp
        (IncomingW2TargetPlacement.right_star_of_leaf_right hc hab hOne star hRight
          profile.singleLabel))
      (discrete_of_leaf data fullDim b (contracted_mem_incidentEdges_right hc) hRight))
      not_false

end LeafExclusion

/-! ## §3  The three induced counts above `A₀`

Write `p`, `q`, `c` for the induced counts of the `t₂` endpoint, the `t₃`
endpoint and the contracted occurrence.  Three facts pin them down: the
contraction forest gives `c + 1 = p + q`; the change at each restored endpoint is
one and local ramification is nonnegative, so the ramification sum above `A₀` at
each endpoint lies in `{0, 1}`; and those two sums are `c + 2 - 2p` and
`c + 2 - 2q`, whose total is exactly `2`.  Hence both are `1`, `p = q`, and
`c = 2p - 1`.  The `t₂` and `t₃` occurrence partitions then bound `p, q ≤ 2`. -/

section Counts

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
  {block : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
  (profile : W2R2SourceProfile.SourceProfile (contractDatum data hc hab hOne) star block)

include fullDim in
/-- The ramification carried above one merged block never exceeds the whole
change at that target vertex, and is never negative. -/
theorem sum_localRamification_le_targetChange (endpoint : target.V)
    (mergedBlock : (mergedPartition data a b).Blocks) :
    0 ≤ (∑ sourceBlock ∈ SheetPartition.blocksWithin (data.vertexPartition endpoint)
          (mergedPartition data a b) mergedBlock,
        data.localRamification endpoint sourceBlock) ∧
      (∑ sourceBlock ∈ SheetPartition.blocksWithin (data.vertexPartition endpoint)
          (mergedPartition data a b) mergedBlock,
        data.localRamification endpoint sourceBlock) ≤ data.targetChange endpoint := by
  classical
  have hNonneg : ∀ sourceBlock : (data.vertexPartition endpoint).Blocks,
      0 ≤ data.localRamification endpoint sourceBlock :=
    fun sourceBlock ↦ data.localRamification_nonneg endpoint (fullDim.valid.2 endpoint) sourceBlock
  refine ⟨Finset.sum_nonneg (fun sourceBlock _ ↦ hNonneg sourceBlock), ?_⟩
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun sourceBlock _ _ ↦ hNonneg sourceBlock)

/-- **The ramification sum above `A₀` at a divalent restored endpoint.**  Its
star is the contracted occurrence and one other, so the sum is `c + #ext - 2p`:
the `|A₀|(val - 2)` term of Riemann--Hurwitz vanishes at valency two. -/
theorem sum_localRamification_of_divalent (endpoint : target.V) (ext : target.edges)
    (hNe : contracted ≠ ext)
    (hCard : (GluingDatum.incidentEdges endpoint).card = 2)
    (hContractedAt : contracted ∈ GluingDatum.incidentEdges endpoint)
    (hExtAt : ext ∈ GluingDatum.incidentEdges endpoint)
    (hRefines : (data.vertexPartition endpoint).Refines (mergedPartition data a b))
    (mergedBlock : (mergedPartition data a b).Blocks) :
    (∑ sourceBlock ∈ SheetPartition.blocksWithin (data.vertexPartition endpoint)
        (mergedPartition data a b) mergedBlock,
      data.localRamification endpoint sourceBlock) =
      ((data.edgePartition contracted).blockCountWithin (mergedPartition data a b)
          mergedBlock.1 : ℤ)
        + ((data.edgePartition ext).blockCountWithin (mergedPartition data a b)
          mergedBlock.1 : ℤ)
        - 2 * ((data.vertexPartition endpoint).blockCountWithin (mergedPartition data a b)
          mergedBlock.1 : ℤ) := by
  classical
  have hNotMem : contracted ∉ ({ext} : Finset target.edges) := by
    simp only [Finset.mem_singleton]; exact hNe
  have hEdges : GluingDatum.incidentEdges endpoint = {contracted, ext} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro edge hEdge
      rcases Finset.mem_insert.mp hEdge with rfl | hEdge
      · exact hContractedAt
      · rw [Finset.mem_singleton.mp hEdge]; exact hExtAt
    · rw [hCard, Finset.card_insert_of_notMem hNotMem, Finset.card_singleton]
  rw [sum_localRamification_blocksWithin data endpoint (mergedPartition data a b) hRefines
      mergedBlock, hEdges, Finset.sum_insert hNotMem, Finset.sum_singleton,
    Finset.card_insert_of_notMem hNotMem, Finset.card_singleton,
    SheetPartition.card_blocksWithin_eq_blockCountWithin (data.vertexPartition endpoint)
      (mergedPartition data a b) hRefines mergedBlock]
  ring

/-- The distinguished wall block, read in the merged partition. -/
theorem merged_rel_self :
    (mergedPartition data a b).Rel block.1 block.1 :=
  ((mergedPartition data a b).rel_iff _ _).mpr rfl

/-- **The `t₂` occurrence induces two blocks above `A₀`**, in the incoming
datum's own words. -/
theorem flag_count (shape : Shape profile) :
    (data.edgePartition (flagEdge data hc hab hOne profile)).blockCountWithin
      (mergedPartition data a b) block.1 = 2 := by
  rw [flagEdge_edgePartition data hc hab hOne profile,
    ← contractDatum_vertexPartition_merge data hc hab hOne]
  exact endpointPartition_blockCountWithin shape block.1
    (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).rel_iff _ _ |>.mpr rfl)

/-- **The `t₃` occurrence induces two blocks above `A₀`.** -/
theorem coflag_count (shape : Shape profile) :
    (data.edgePartition (coflagEdge data hc hab hOne profile)).blockCountWithin
      (mergedPartition data a b) block.1 = 2 := by
  rw [coflagEdge_edgePartition data hc hab hOne profile,
    ← contractDatum_vertexPartition_merge data hc hab hOne]
  exact singlePartition_blockCountWithin shape block.1
    (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).rel_iff _ _ |>.mpr rfl)

/-- The `t₃` occurrence of the incoming target meets `singleEnd`, the mirror of
`W2MkkIncomingCensus.flag_mem_doubleEnd`. -/
theorem coflagEdge_mem_singleEnd
    (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
    (hRightCard : (GluingDatum.incidentEdges b).card = 2) :
    coflagEdge data hc hab hOne profile ∈
      GluingDatum.incidentEdges (singleEnd data hc hab hOne profile) := by
  have hNe := star_values_ne data hc hab hOne profile hLeftCard hRightCard
  rcases Bool.eq_false_or_eq_true (IncomingTargetExpansion.right hc hab hOne
    (star.edge profile.doubleLabel)) with hTrue | hFalse
  · rw [singleEnd_of_true data hc hab hOne profile hTrue]
    have hSingleFalse : IncomingTargetExpansion.right hc hab hOne
        (star.edge profile.singleLabel) = false := by
      rcases Bool.eq_false_or_eq_true (IncomingTargetExpansion.right hc hab hOne
        (star.edge profile.singleLabel)) with h | h
      · exact absurd (hTrue.trans h.symm) hNe
      · exact h
    exact (IncomingW2TargetPlacement.right_eq_false_iff_of_incident hc hab hOne _
      (star.edge_mem_incidentEdges profile.singleLabel)).mp hSingleFalse
  · rw [singleEnd_of_false data hc hab hOne profile hFalse]
    have hSingleTrue : IncomingTargetExpansion.right hc hab hOne
        (star.edge profile.singleLabel) = true := by
      rcases Bool.eq_false_or_eq_true (IncomingTargetExpansion.right hc hab hOne
        (star.edge profile.singleLabel)) with h | h
      · exact h
      · exact absurd (hFalse.trans h.symm) hNe
    exact (IncomingW2TargetPlacement.right_eq_true_iff hc hab hOne _).mp hSingleTrue

/-- Either restored endpoint's partition is coarsened by the merged one. -/
theorem restoredEnd_refines (endpoint : target.V) (hEnd : endpoint = a ∨ endpoint = b) :
    (data.vertexPartition endpoint).Refines (mergedPartition data a b) := by
  rcases hEnd with hEq | hEq
  · rw [hEq]; exact vertexPartition_refines_mergedPartition data a b
  · rw [hEq]; exact vertexPartition_refines_mergedPartition_right data a b

include fullDim hForest in
/-- **The three induced counts above `A₀`, exhaustively.**  Base II.1 is the
first alternative and Base II.2 the second; nothing else solves the system. -/
theorem selected_counts (shape : Shape profile)
    (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
    (hRightCard : (GluingDatum.incidentEdges b).card = 2)
    (hChangeLeft : data.targetChange a = 1) (hChangeRight : data.targetChange b = 1) :
    ((data.vertexPartition (doubleEnd data hc hab hOne profile)).blockCountWithin
          (mergedPartition data a b) block.1 = 1 ∧
        (data.vertexPartition (singleEnd data hc hab hOne profile)).blockCountWithin
          (mergedPartition data a b) block.1 = 1 ∧
        (data.edgePartition contracted).blockCountWithin
          (mergedPartition data a b) block.1 = 1) ∨
      ((data.vertexPartition (doubleEnd data hc hab hOne profile)).blockCountWithin
          (mergedPartition data a b) block.1 = 2 ∧
        (data.vertexPartition (singleEnd data hc hab hOne profile)).blockCountWithin
          (mergedPartition data a b) block.1 = 2 ∧
        (data.edgePartition contracted).blockCountWithin
          (mergedPartition data a b) block.1 = 3) := by
  classical
  have hDoubleEnd : doubleEnd data hc hab hOne profile = a ∨
      doubleEnd data hc hab hOne profile = b := by
    rcases ends_cases data hc hab hOne profile with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  have hSingleEnd : singleEnd data hc hab hOne profile = a ∨
      singleEnd data hc hab hOne profile = b := by
    rcases ends_cases data hc hab hOne profile with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inr h
    · exact Or.inl h
  have hRefinesDouble := restoredEnd_refines data _ hDoubleEnd
  have hRefinesSingle := restoredEnd_refines data _ hSingleEnd
  have hForestCount : ((data.edgePartition contracted).blockCountWithin
        (mergedPartition data a b) block.1 : ℤ) + 1 =
      ((data.vertexPartition a).blockCountWithin (mergedPartition data a b) block.1 : ℤ) +
        ((data.vertexPartition b).blockCountWithin (mergedPartition data a b) block.1 : ℤ) :=
    contractionForest_count data hc hForest
      (M11IncomingPartitions.selectedMergedBlock data hc hab hOne block)
  have hPair : ((data.edgePartition contracted).blockCountWithin
        (mergedPartition data a b) block.1 : ℤ) + 1 =
      ((data.vertexPartition (doubleEnd data hc hab hOne profile)).blockCountWithin
          (mergedPartition data a b) block.1 : ℤ) +
        ((data.vertexPartition (singleEnd data hc hab hOne profile)).blockCountWithin
          (mergedPartition data a b) block.1 : ℤ) := by
    rcases ends_cases data hc hab hOne profile with ⟨hDouble, hSingle⟩ | ⟨hDouble, hSingle⟩
    · rw [hDouble, hSingle]; exact hForestCount
    · rw [hDouble, hSingle]; linarith [hForestCount]
  have hChangeDouble : data.targetChange (doubleEnd data hc hab hOne profile) = 1 := by
    rcases hDoubleEnd with h | h
    · rw [h]; exact hChangeLeft
    · rw [h]; exact hChangeRight
  have hChangeSingle : data.targetChange (singleEnd data hc hab hOne profile) = 1 := by
    rcases hSingleEnd with h | h
    · rw [h]; exact hChangeLeft
    · rw [h]; exact hChangeRight
  have hDoubleSum : (∑ sourceBlock ∈ SheetPartition.blocksWithin
        (data.vertexPartition (doubleEnd data hc hab hOne profile))
        (mergedPartition data a b)
        (M11IncomingPartitions.selectedMergedBlock data hc hab hOne block),
      data.localRamification (doubleEnd data hc hab hOne profile) sourceBlock) =
      ((data.edgePartition contracted).blockCountWithin
          (mergedPartition data a b) block.1 : ℤ)
        + ((data.edgePartition (flagEdge data hc hab hOne profile)).blockCountWithin
            (mergedPartition data a b) block.1 : ℤ)
        - 2 * ((data.vertexPartition (doubleEnd data hc hab hOne profile)).blockCountWithin
            (mergedPartition data a b) block.1 : ℤ) :=
    sum_localRamification_of_divalent data (doubleEnd data hc hab hOne profile)
      (flagEdge data hc hab hOne profile)
      (fun h ↦ unfoldEdge_ne_contracted hc hab hOne _ h.symm)
      (doubleEnd_divalent data hc hab hOne profile hLeftCard hRightCard)
      (contracted_mem_doubleEnd data hc hab hOne profile)
      (flagEdge_mem_doubleEnd data hc hab hOne profile) hRefinesDouble
      (M11IncomingPartitions.selectedMergedBlock data hc hab hOne block)
  have hSingleSum : (∑ sourceBlock ∈ SheetPartition.blocksWithin
        (data.vertexPartition (singleEnd data hc hab hOne profile))
        (mergedPartition data a b)
        (M11IncomingPartitions.selectedMergedBlock data hc hab hOne block),
      data.localRamification (singleEnd data hc hab hOne profile) sourceBlock) =
      ((data.edgePartition contracted).blockCountWithin
          (mergedPartition data a b) block.1 : ℤ)
        + ((data.edgePartition (coflagEdge data hc hab hOne profile)).blockCountWithin
            (mergedPartition data a b) block.1 : ℤ)
        - 2 * ((data.vertexPartition (singleEnd data hc hab hOne profile)).blockCountWithin
            (mergedPartition data a b) block.1 : ℤ) :=
    sum_localRamification_of_divalent data (singleEnd data hc hab hOne profile)
      (coflagEdge data hc hab hOne profile)
      (fun h ↦ unfoldEdge_ne_contracted hc hab hOne _ h.symm)
      (singleEnd_divalent data hc hab hOne profile hLeftCard hRightCard)
      (contracted_mem_singleEnd data hc hab hOne profile)
      (coflagEdge_mem_singleEnd data hc hab hOne profile hLeftCard hRightCard)
      hRefinesSingle (M11IncomingPartitions.selectedMergedBlock data hc hab hOne block)
  rw [flag_count data hc hab hOne profile shape] at hDoubleSum
  rw [coflag_count data hc hab hOne profile shape] at hSingleSum
  have hDoubleBounds := sum_localRamification_le_targetChange data fullDim
    (doubleEnd data hc hab hOne profile)
    (M11IncomingPartitions.selectedMergedBlock data hc hab hOne block)
  have hSingleBounds := sum_localRamification_le_targetChange data fullDim
    (singleEnd data hc hab hOne profile)
    (M11IncomingPartitions.selectedMergedBlock data hc hab hOne block)
  rw [hDoubleSum, hChangeDouble] at hDoubleBounds
  rw [hSingleSum, hChangeSingle] at hSingleBounds
  have hDoubleLe : (data.vertexPartition (doubleEnd data hc hab hOne profile)).blockCountWithin
      (mergedPartition data a b) block.1 ≤ 2 := by
    have hMono : (data.vertexPartition (doubleEnd data hc hab hOne profile)).blockCountWithin
          (mergedPartition data a b) block.1 ≤
        (data.edgePartition (flagEdge data hc hab hOne profile)).blockCountWithin
          (mergedPartition data a b) block.1 :=
      blockCountWithin_mono (data.edgePartition (flagEdge data hc hab hOne profile))
        (data.vertexPartition (doubleEnd data hc hab hOne profile)) (mergedPartition data a b)
        (refines_of_mem_incidentEdges data (flagEdge_mem_doubleEnd data hc hab hOne profile))
        hRefinesDouble (M11IncomingPartitions.selectedMergedBlock data hc hab hOne block)
    rw [flag_count data hc hab hOne profile shape] at hMono
    exact hMono
  have hDoublePos := SheetPartition.blockCountWithin_pos
    (data.vertexPartition (doubleEnd data hc hab hOne profile)) (mergedPartition data a b)
    block.1
  have hSinglePos := SheetPartition.blockCountWithin_pos
    (data.vertexPartition (singleEnd data hc hab hOne profile)) (mergedPartition data a b)
    block.1
  have hContractedPos := SheetPartition.blockCountWithin_pos
    (data.edgePartition contracted) (mergedPartition data a b) block.1
  obtain ⟨hDoubleNonneg, hDoubleLeOne⟩ := hDoubleBounds
  obtain ⟨hSingleNonneg, hSingleLeOne⟩ := hSingleBounds
  rcases Nat.lt_or_ge ((data.vertexPartition (doubleEnd data hc hab hOne profile)).blockCountWithin
      (mergedPartition data a b) block.1) 2 with hLt | hGe
  · left
    refine ⟨by omega, by omega, by omega⟩
  · right
    refine ⟨by omega, by omega, by omega⟩

end Counts

/-! ## §4  From the counts to the partitions

Each of the three counts then forces a literal identity of blocks above `A₀`,
because in each case a partition that refines it has the same induced count:
`1 = 1` against the merged partition itself (Base II.1), and `2 = 2`, `2 = 2`,
`3 = 3` against the `t₂` occurrence partition, the `t₃` occurrence partition and
the detached `t₂` partition (Base II.2). -/

section Census

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
  {block : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
  (profile : W2R2SourceProfile.SourceProfile (contractDatum data hc hab hOne) star block)

/-- A partition induces exactly one block inside each of its own blocks. -/
theorem blockCountWithin_self (partition : SheetPartition degree) (sheet : Fin degree) :
    partition.blockCountWithin partition sheet = 1 := by
  classical
  have hImage : (partition.block sheet).image partition.repr = {partition.repr sheet} := by
    ext value
    simp only [Finset.mem_image, Finset.mem_singleton, SheetPartition.mem_block_iff]
    exact ⟨by rintro ⟨x, hx, rfl⟩; exact ((partition.rel_iff sheet x).mp hx).symm,
      fun hValue ↦ ⟨sheet, (partition.rel_iff sheet sheet).mpr rfl, hValue.symm⟩⟩
  unfold SheetPartition.blockCountWithin
  rw [hImage, Finset.card_singleton]

/-- The wall datum's partition at the merged vertex is the merged partition. -/
theorem wall_eq_merged :
    (contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩ = mergedPartition data a b :=
  contractDatum_vertexPartition_merge data hc hab hOne

/-- **Base II.1.**  All three wall positions carry the whole distinguished
block. -/
theorem joinedCensus_of_counts
    (hDouble : (data.vertexPartition (doubleEnd data hc hab hOne profile)).blockCountWithin
      (mergedPartition data a b) block.1 = 1)
    (hSingle : (data.vertexPartition (singleEnd data hc hab hOne profile)).blockCountWithin
      (mergedPartition data a b) block.1 = 1)
    (hNew : (data.edgePartition contracted).blockCountWithin
      (mergedPartition data a b) block.1 = 1) :
    W2MkkIncomingMatching.JoinedCensus data hc hab hOne profile := by
  have hDoubleEnd : doubleEnd data hc hab hOne profile = a ∨
      doubleEnd data hc hab hOne profile = b := by
    rcases ends_cases data hc hab hOne profile with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  have hSingleEnd : singleEnd data hc hab hOne profile = a ∨
      singleEnd data hc hab hOne profile = b := by
    rcases ends_cases data hc hab hOne profile with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inr h
    · exact Or.inl h
  refine ⟨?_, ?_, ?_⟩
  · intro sheet hSheet
    refine SheetPartition.block_eq_of_refines_of_blockCountWithin_eq_one _ _
      (restoredEnd_refines data _ hDoubleEnd) sheet ?_
    rw [← blockCountWithin_congr _ (mergedPartition data a b) hSheet]
    exact hDouble
  · intro sheet hSheet
    refine SheetPartition.block_eq_of_refines_of_blockCountWithin_eq_one _ _
      (restoredEnd_refines data _ hSingleEnd) sheet ?_
    rw [← blockCountWithin_congr _ (mergedPartition data a b) hSheet]
    exact hSingle
  · intro sheet hSheet
    refine SheetPartition.block_eq_of_refines_of_blockCountWithin_eq_one _ _
      (edgePartition_refines_mergedPartition data hc) sheet ?_
    rw [← blockCountWithin_congr _ (mergedPartition data a b) hSheet]
    exact hNew

/-- **Base II.2, the `t₂` endpoint.**  It carries the `t₂` occurrence partition
on `A₀`: `A' = e₁`, `A'' = e₂` as subsets of `[d]`. -/
theorem doubleEnd_block_eq (shape : Shape profile)
    (hDouble : (data.vertexPartition (doubleEnd data hc hab hOne profile)).blockCountWithin
      (mergedPartition data a b) block.1 = 2)
    (sheet : Fin degree) (hSheet : (mergedPartition data a b).Rel block.1 sheet) :
    (data.vertexPartition (doubleEnd data hc hab hOne profile)).block sheet =
      (endpointPartition profile).block sheet := by
  have hDoubleEnd : doubleEnd data hc hab hOne profile = a ∨
      doubleEnd data hc hab hOne profile = b := by
    rcases ends_cases data hc hab hOne profile with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  refine (block_eq_of_blockCountWithin_eq
    (data.edgePartition (flagEdge data hc hab hOne profile))
    (data.vertexPartition (doubleEnd data hc hab hOne profile)) (mergedPartition data a b)
    (refines_of_mem_incidentEdges data (flagEdge_mem_doubleEnd data hc hab hOne profile))
    (restoredEnd_refines data _ hDoubleEnd)
    (M11IncomingPartitions.selectedMergedBlock data hc hab hOne block) ?_ sheet hSheet).symm
  show (data.edgePartition (flagEdge data hc hab hOne profile)).blockCountWithin
      (mergedPartition data a b) block.1 =
    (data.vertexPartition (doubleEnd data hc hab hOne profile)).blockCountWithin
      (mergedPartition data a b) block.1
  rw [flag_count data hc hab hOne profile shape, hDouble]

/-- **Base II.2, the `t₃` endpoint, first half.**  It carries the `t₃`
occurrence partition on `A₀`. -/
theorem singleEnd_block_eq (shape : Shape profile)
    (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
    (hRightCard : (GluingDatum.incidentEdges b).card = 2)
    (hSingle : (data.vertexPartition (singleEnd data hc hab hOne profile)).blockCountWithin
      (mergedPartition data a b) block.1 = 2)
    (sheet : Fin degree) (hSheet : (mergedPartition data a b).Rel block.1 sheet) :
    (data.vertexPartition (singleEnd data hc hab hOne profile)).block sheet =
      (singlePartition profile).block sheet := by
  have hSingleEnd : singleEnd data hc hab hOne profile = a ∨
      singleEnd data hc hab hOne profile = b := by
    rcases ends_cases data hc hab hOne profile with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inr h
    · exact Or.inl h
  refine (block_eq_of_blockCountWithin_eq
    (data.edgePartition (coflagEdge data hc hab hOne profile))
    (data.vertexPartition (singleEnd data hc hab hOne profile)) (mergedPartition data a b)
    (refines_of_mem_incidentEdges data
      (coflagEdge_mem_singleEnd data hc hab hOne profile hLeftCard hRightCard))
    (restoredEnd_refines data _ hSingleEnd)
    (M11IncomingPartitions.selectedMergedBlock data hc hab hOne block) ?_ sheet hSheet).symm
  show (data.edgePartition (coflagEdge data hc hab hOne profile)).blockCountWithin
      (mergedPartition data a b) block.1 =
    (data.vertexPartition (singleEnd data hc hab hOne profile)).blockCountWithin
      (mergedPartition data a b) block.1
  rw [coflag_count data hc hab hOne profile shape, hSingle]

/-- **Base II.2, the `t₃` endpoint, second half.**  `e₃ ⊔ e₄` is `A₀` with the
pinned sheet detached. -/
theorem singlePartition_block_eq_detach (shape : Shape profile) (detach : DetachData profile)
    (sheet : Fin degree) (hSheet : (mergedPartition data a b).Rel block.1 sheet) :
    (singlePartition profile).block sheet =
      (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).detachSheet
        (pinSheet profile) detach.remainder detach.ne_remainder detach.wallTogether).block
        sheet := by
  have hSheetWall : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
      block.1 sheet :=
    cast (merged_rel_eq data hc hab hOne block.1 sheet).symm hSheet
  refine block_eq_of_blockCountWithin_eq (singlePartition profile)
    (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).detachSheet
      (pinSheet profile) detach.remainder detach.ne_remainder detach.wallTogether)
    ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
    (SheetPartition.refines_detachSheet_of_block_singleton (singlePartition profile)
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩) (pinSheet profile)
      detach.remainder detach.ne_remainder detach.wallTogether
      (singlePartition_refines profile) (pinSheet_block shape))
    (SheetPartition.detachSheet_refines _ _ _ _ _) block ?_ sheet hSheetWall
  rw [singlePartition_blockCountWithin shape block.1
      ((((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)).rel_iff _ _ |>.mpr rfl),
    W2MkkSourceCandidates.blockCountWithin_detachSheet_fine
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩) (pinSheet profile)
      detach.remainder block.1 detach.ne_remainder detach.wallTogether (fun _ _ h ↦ h)
      (pinSheet_rel profile).symm,
    blockCountWithin_self ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩) block.1]

include fullDim hForest in
/-- **The contracted occurrence partition refines the `t₂` occurrence
partition.**  Inside `A₀` both are read off the `t₂` endpoint (§4); outside it
the `r = 0` background census makes every occurrence at that endpoint carry the
endpoint's own class, so the two agree there outright. -/
theorem contracted_refines_endpointPartition (shape : Shape profile)
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ block → (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
    (hRightCard : (GluingDatum.incidentEdges b).card = 2)
    (hDouble : (data.vertexPartition (doubleEnd data hc hab hOne profile)).blockCountWithin
      (mergedPartition data a b) block.1 = 2) :
    (data.edgePartition contracted).Refines (endpointPartition profile) := by
  intro i j hij
  have hMem : j ∈ (data.edgePartition contracted).block i :=
    ((data.edgePartition contracted).mem_block_iff i j).mpr hij
  by_cases hOn : (mergedPartition data a b).Rel block.1 i
  · have hRel : (data.vertexPartition (doubleEnd data hc hab hOne profile)).Rel i j :=
      (refines_of_mem_incidentEdges data
        (contracted_mem_doubleEnd data hc hab hOne profile)).rel hij
    have hBlock := doubleEnd_block_eq data hc hab hOne profile shape hDouble i hOn
    have hMemEnd : j ∈ (data.vertexPartition (doubleEnd data hc hab hOne profile)).block i :=
      (((data.vertexPartition (doubleEnd data hc hab hOne profile))).mem_block_iff i j).mpr hRel
    rw [hBlock] at hMemEnd
    exact ((endpointPartition profile).mem_block_iff i j).mp hMemEnd
  · have hContr := background_edge_block_doubleEnd data hc hab hOne fullDim profile hForest
      hBackground hLeftCard hRightCard contracted
      (contracted_mem_doubleEnd data hc hab hOne profile) i hOn
    have hFlag := background_edge_block_doubleEnd data hc hab hOne fullDim profile hForest
      hBackground hLeftCard hRightCard (flagEdge data hc hab hOne profile)
      (flagEdge_mem_doubleEnd data hc hab hOne profile) i hOn
    rw [hContr, ← hFlag] at hMem
    exact ((endpointPartition profile).mem_block_iff i j).mp hMem

include fullDim hForest in
/-- **Base II.2, the contracted occurrence.**  It is the `t₂` occurrence
partition with the pinned sheet detached: three classes above `A₀`, namely
`e₁ ∖ {x}`, `{x}` and `e₂` (or the mirror). -/
theorem contracted_block_eq_detach (shape : Shape profile) (detach : DetachData profile)
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ block → (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
    (hRightCard : (GluingDatum.incidentEdges b).card = 2)
    (hDouble : (data.vertexPartition (doubleEnd data hc hab hOne profile)).blockCountWithin
      (mergedPartition data a b) block.1 = 2)
    (hSingle : (data.vertexPartition (singleEnd data hc hab hOne profile)).blockCountWithin
      (mergedPartition data a b) block.1 = 2)
    (hNew : (data.edgePartition contracted).blockCountWithin
      (mergedPartition data a b) block.1 = 3)
    (sheet : Fin degree) (hSheet : (mergedPartition data a b).Rel block.1 sheet) :
    (data.edgePartition contracted).block sheet =
      ((endpointPartition profile).detachSheet (pinSheet profile) detach.remainder
        detach.ne_remainder detach.together).block sheet := by
  classical
  have hPinMerged : (mergedPartition data a b).Rel block.1 (pinSheet profile) :=
    cast (merged_rel_eq data hc hab hOne block.1 (pinSheet profile)) (pinSheet_rel profile)
  -- the contracted occurrence isolates the pinned sheet
  have hSingleEndPin : (data.vertexPartition (singleEnd data hc hab hOne profile)).block
      (pinSheet profile) = {pinSheet profile} := by
    rw [singleEnd_block_eq data hc hab hOne profile shape hLeftCard hRightCard hSingle
      (pinSheet profile) hPinMerged]
    exact pinSheet_block shape
  have hSingleton : (data.edgePartition contracted).block (pinSheet profile) =
      {pinSheet profile} := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro value hValue
      have hRel : (data.vertexPartition (singleEnd data hc hab hOne profile)).Rel
          (pinSheet profile) value :=
        (refines_of_mem_incidentEdges data
          (contracted_mem_singleEnd data hc hab hOne profile)).rel
          (((data.edgePartition contracted).mem_block_iff _ _).mp hValue)
      have := (((data.vertexPartition (singleEnd data hc hab hOne profile))).mem_block_iff
        (pinSheet profile) value).mpr hRel
      rwa [hSingleEndPin] at this
    · intro value hValue
      rw [Finset.mem_singleton.mp hValue]
      exact (data.edgePartition contracted).self_mem_block _
  have hSheetWall : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
      block.1 sheet :=
    cast (merged_rel_eq data hc hab hOne block.1 sheet).symm hSheet
  refine block_eq_of_blockCountWithin_eq (data.edgePartition contracted)
    ((endpointPartition profile).detachSheet (pinSheet profile) detach.remainder
      detach.ne_remainder detach.together)
    ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
    (SheetPartition.refines_detachSheet_of_block_singleton (data.edgePartition contracted)
      (endpointPartition profile) (pinSheet profile) detach.remainder detach.ne_remainder
      detach.together
      (contracted_refines_endpointPartition data hc hab hOne fullDim hForest profile shape
        hBackground hLeftCard hRightCard hDouble) hSingleton)
    ((SheetPartition.detachSheet_refines _ _ _ _ _).trans (endpointPartition_refines profile))
    block ?_ sheet hSheetWall
  rw [W2MkkSourceCandidates.blockCountWithin_detachSheet_fine (endpointPartition profile)
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩) (pinSheet profile)
      detach.remainder block.1 detach.ne_remainder detach.together
      (endpointPartition_refines profile) (pinSheet_rel profile).symm,
    endpointPartition_blockCountWithin shape block.1
      ((((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)).rel_iff _ _ |>.mpr rfl)]
  have hConv : (data.edgePartition contracted).blockCountWithin
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩) block.1 =
      (data.edgePartition contracted).blockCountWithin (mergedPartition data a b) block.1 :=
    congrArg (fun partition : SheetPartition degree ↦
      (data.edgePartition contracted).blockCountWithin partition block.1)
      (wall_eq_merged data hc hab hOne)
  rw [hConv, hNew]

include fullDim hForest in
/-- **Base II.2, assembled.**  The `t₂` endpoint splits `A₀` as
`e₁ ⊔ e₂`, the `t₃` endpoint detaches the pinned sheet from the whole block, and
the contracted occurrence detaches it from the `t₂` partition. -/
theorem detachCensus_of_counts (shape : Shape profile) (detach : DetachData profile)
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ block → (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
    (hRightCard : (GluingDatum.incidentEdges b).card = 2)
    (hDouble : (data.vertexPartition (doubleEnd data hc hab hOne profile)).blockCountWithin
      (mergedPartition data a b) block.1 = 2)
    (hSingle : (data.vertexPartition (singleEnd data hc hab hOne profile)).blockCountWithin
      (mergedPartition data a b) block.1 = 2)
    (hNew : (data.edgePartition contracted).blockCountWithin
      (mergedPartition data a b) block.1 = 3) :
    W2MkkIncomingMatching.DetachCensus data hc hab hOne profile detach :=
  ⟨fun sheet hSheet ↦ doubleEnd_block_eq data hc hab hOne profile shape hDouble sheet hSheet,
    fun sheet hSheet ↦
      (singleEnd_block_eq data hc hab hOne profile shape hLeftCard hRightCard hSingle sheet
        hSheet).trans
        (singlePartition_block_eq_detach data hc hab hOne profile shape detach sheet hSheet),
    fun sheet hSheet ↦ contracted_block_eq_detach data hc hab hOne fullDim hForest profile
      shape detach hBackground hLeftCard hRightCard hDouble hSingle hNew sheet hSheet⟩

include fullDim hForest in
/-- **The Base II dichotomy of Part I, proved.**  An arbitrary
full-dimensional incoming cover whose contracted wall carries a `w2Mkk` profile
satisfies Base II.2 or Base II.1 on the distinguished block -- `ndG(A₀)` has two
edges `e'`, `e''` or one edge `e'`.  Nothing beyond the classifier's own payload
enters: the profile, the M-kk shape, and the `background` field. -/
theorem selectedCensus_dichotomy (shape : Shape profile) (detach : DetachData profile)
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ block → (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0) :
    W2MkkIncomingMatching.DetachCensus data hc hab hOne profile detach ∨
      W2MkkIncomingMatching.JoinedCensus data hc hab hOne profile := by
  obtain ⟨hLeftCard, hRightCard, hChangeLeft, hChangeRight⟩ :=
    divalent_endpoints data hc hab hOne fullDim profile shape
  rcases selected_counts data hc hab hOne fullDim hForest profile shape hLeftCard hRightCard
    hChangeLeft hChangeRight with ⟨hDouble, hSingle, hNew⟩ | ⟨hDouble, hSingle, hNew⟩
  · exact Or.inr (joinedCensus_of_counts data hc hab hOne profile hDouble hSingle hNew)
  · exact Or.inl (detachCensus_of_counts data hc hab hOne fullDim hForest profile shape detach
      hBackground hLeftCard hRightCard hDouble hSingle hNew)

end Census


/-! ## §5  The incoming member identification, unconditional

`W2MkkIncomingMatching.exists_member_normalization_of_dichotomy` takes the
dichotomy, the two target valencies and the background field as hypotheses.
The first two are theorems of this module, so only the classifier's own
`background` field remains. -/

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
  (shape : Shape profile) (detach : DetachData profile) (distinguished : Fin degree)

include fullDim hForest input hBackground in
/-- **An arbitrary incoming `w2Mkk` cover is a named Figure 34 member,
unconditionally.**  `W2MkkIncomingMatching.exists_member_normalization_of_dichotomy`
with the census and both target valencies discharged. -/
theorem exists_member_normalization :
    ∃ index : Fin 2,
      (∀ column : Option (contract target hab hOne).edges,
          GluingTransport.edgeEquiv (IncomingMatchingCore.memberTargetIso data hc hab hOne
              (W2MkkIncomingMatching.members data hc hab hOne profile shape detach
                distinguished index)
              (W2MkkIncomingMatching.members_placement data hc hab hOne profile shape detach
                distinguished index
                (divalent_endpoints data hc hab hOne fullDim profile shape).1
                (divalent_endpoints data hc hab hOne fullDim profile shape).2.1))
              (M11IncomingCoordinates.incomingColumnEquiv hc hab hOne column) =
            occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
              (W2MkkIncomingMatching.members data hc hab hOne profile shape detach
                distinguished index).right column) ∧
      ∃ hVertices : ∀ vertex, ((GluingTransport.transport
            (IncomingMatchingCore.memberTargetIso data hc hab hOne
              (W2MkkIncomingMatching.members data hc hab hOne profile shape detach
                distinguished index)
              (W2MkkIncomingMatching.members_placement data hc hab hOne profile shape detach
                distinguished index
                (divalent_endpoints data hc hab hOne fullDim profile shape).1
                (divalent_endpoints data hc hab hOne fullDim profile shape).2.1))
          data).vertexPartition vertex).SameBlocks
          ((W2MkkIncomingMatching.members data hc hab hOne profile shape detach
            distinguished index).datum.vertexPartition vertex),
      ∃ hEdges : ∀ edge, ((GluingTransport.transport
            (IncomingMatchingCore.memberTargetIso data hc hab hOne
              (W2MkkIncomingMatching.members data hc hab hOne profile shape detach
                distinguished index)
              (W2MkkIncomingMatching.members_placement data hc hab hOne profile shape detach
                distinguished index
                (divalent_endpoints data hc hab hOne fullDim profile shape).1
                (divalent_endpoints data hc hab hOne fullDim profile shape).2.1))
          data).edgePartition edge).SameBlocks
          ((W2MkkIncomingMatching.members data hc hab hOne profile shape detach
            distinguished index).datum.edgePartition edge),
        W3Nd2IncomingMemberMatching.NormalizedAgainst data fullDim
          (IncomingMatchingCore.memberTargetIso data hc hab hOne
            (W2MkkIncomingMatching.members data hc hab hOne profile shape detach
              distinguished index)
            (W2MkkIncomingMatching.members_placement data hc hab hOne profile shape detach
              distinguished index
              (divalent_endpoints data hc hab hOne fullDim profile shape).1
              (divalent_endpoints data hc hab hOne fullDim profile shape).2.1))
          (W2MkkIncomingMatching.members data hc hab hOne profile shape detach
            distinguished index).datum hVertices hEdges :=
  W2MkkIncomingMatching.exists_member_normalization_of_dichotomy data hc hab hOne fullDim
    hForest input profile hBackground
    (divalent_endpoints data hc hab hOne fullDim profile shape).1
    (divalent_endpoints data hc hab hOne fullDim profile shape).2.1
    shape detach distinguished
    (selectedCensus_dichotomy data hc hab hOne fullDim hForest profile shape detach hBackground)

end Identification

end DraismaVargas.LocalCases.W2MkkSelectedCensus
